/-
Copyright (c) 2024 Siddhartha Gadgil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil
-/
import Lean.Elab.Tactic.Meta
import Lean.Meta.Tactic.TryThis
import LeanSearchClient.Basic

/-!
# LeanSearchClient

In this file, we provide syntax for search using the [leansearch API](https://leansearch.net/)
and the [Moogle API](https://www.moogle.ai/api/search).
from within Lean. It allows you to search for Lean tactics and theorems using natural language.

We provide syntax to make a query and generate `TryThis` options to click or
use a code action to use the results.

The queries are of three forms. For leansearch these are:

* `Command` syntax: `#leansearch "search query"` as a command.
* `Term` syntax: `#leansearch "search query"` as a term.
* `Tactic` syntax: `#leansearch "search query"` as a tactic.

The corresponding syntax for Moogle is:

* `Command` syntax: `#moogle "search query"` as a command.
* `Term` syntax: `#moogle "search query"` as a term.
* `Tactic` syntax: `#moogle "search query"` as a tactic.

In all cases results are displayed in the Lean Infoview and clicking these replaces the query text.
In the cases of a query for tactics only valid tactics are displayed.
-/

namespace LeanSearchClient

open Lean Meta Elab Tactic Parser Term

def useragent : CoreM String :=
  return leansearchclient.useragent.get (← getOptions)

def getLeanSearchQueryJson (s : String) (num_results : Nat := 6) : CoreM <| Array Json := do
  let apiUrl := "https://leansearch.net/api/search"
  let s' := System.Uri.escapeUri s
  let q := apiUrl ++ s!"?query={s'}&num_results={num_results}"
  let s ← IO.Process.output {cmd := "curl", args := #["-X", "GET", "--user-agent", ← useragent, q]}
  let js ← match Json.parse s.stdout |>.toOption with
    | some js => pure js
    | none => IO.throwServerError s!"Could not contact LeanSearch server"
  return js.getArr? |>.toOption |>.getD #[]

def getMoogleQueryJson (s : String) (num_results : Nat := 6) : CoreM <| Array Json := do
  let apiUrl := "https://www.moogle.ai/api/search"
  let data := Json.arr
    #[Json.mkObj [("isFind", false), ("contents", s)]]
  let s ← IO.Process.output {cmd := "curl", args := #[apiUrl, "-H", "content-type: application/json",  "--user-agent", ← useragent, "--data", data.pretty]}
  match Json.parse s.stdout with
  | Except.error _ =>
    throwError m!"Could not contact Moogle server"
  | Except.ok js =>
  let result? := js.getObjValAs?  Json "data"
  match result? with
    | Except.ok result =>
        match result.getArr? with
        | Except.ok arr => return arr[0:num_results]
        | Except.error e => IO.throwServerError s!"Could not obtain array from {js}; error: {e}"
    | _ => IO.throwServerError s!"Could not obtain data from {js}"


structure SearchResult where
  name : String
  type? : Option String
  docString? : Option String
  doc_url? : Option String
  kind? : Option String
  deriving Repr

namespace SearchResult

def ofLeanSearchJson? (js : Json) : Option SearchResult :=
  match js.getObjValAs? String "formal_name" with
  | Except.ok name =>
      let type? := js.getObjValAs? String "formal_type" |>.toOption
      let doc? := js.getObjValAs? String "docstring" |>.toOption
      let doc? := doc?.filter fun s => s != ""
      let docurl? := js.getObjValAs? String "doc_url" |>.toOption
      let kind? := js.getObjValAs? String "kind" |>.toOption
      some {name := name, type? := type?, docString? := doc?, doc_url? := docurl?, kind? := kind?}
  | _ => none

def ofMoogleJson? (js : Json) : MetaM <| Option SearchResult :=
  match js.getObjValAs? String "declarationName" with
  | Except.ok name => do
      let type? ←
        try
          let info ←  getConstInfo name.toName
          let fmt ← PrettyPrinter.ppExpr info.type
          pure <| some fmt.pretty
        catch _ =>
          pure none
      let doc? := js.getObjValAs? String "declarationDocString" |>.toOption
      let doc? := doc?.filter fun s => s != ""
      let kind? := js.getObjValAs? String "declarationType" |>.toOption
      return some {name := name, type? := type?, docString? := doc?, doc_url? := none, kind? := kind?}
  | _ => return none

def ofLoogleJson? (js : Json) : Option SearchResult :=
  match js.getObjValAs? String "name" with
  | Except.ok name =>
      let type? := js.getObjValAs? String "type" |>.toOption
      let doc? := js.getObjValAs? String "doc" |>.toOption
      let doc? := doc?.filter fun s => s != ""
      some {name := name, type? := type?, docString? := doc?, doc_url? := none, kind? := none}
  | _ => none

def toCommandSuggestion (sr : SearchResult) : TryThis.Suggestion :=
  let data := match sr.docString? with
    | some doc => s!"{doc}\n"
    | none => ""
  {suggestion := s!"#check {sr.name}", postInfo? := sr.type?.map fun s => s!" -- {s}" ++ s!"\n{data}"}

def toTermSuggestion (sr : SearchResult) : TryThis.Suggestion :=
  match sr.type? with
  | some type => {suggestion := sr.name, postInfo? := some s!" (type: {type})"}
  | none => {suggestion := sr.name}

def toTacticSuggestions (sr : SearchResult) : Array TryThis.Suggestion :=
  match sr.type? with
  | some type => #[{suggestion := s!"apply {sr.name}"},
        {suggestion := s!"have : {type} := {sr.name}"},
        {suggestion := s!"rw [{sr.name}]"},
        {suggestion := s!"rw [← {sr.name}]" }]
  | none => #[]

end SearchResult


def queryLeanSearch (s : String) (num_results : Nat) :
    MetaM <| Array SearchResult := do
  let jsArr ← getLeanSearchQueryJson s num_results
  return jsArr.filterMap SearchResult.ofLeanSearchJson?

def queryMoogle (s : String) (num_results : Nat) :
    MetaM <| Array SearchResult := do
  let jsArr ← getMoogleQueryJson s num_results
  jsArr.filterMapM SearchResult.ofMoogleJson?

def defaultTerm (expectedType? : Option Expr) : MetaM Expr := do
  match expectedType? with
  | some type =>
    if !type.hasExprMVar then
      mkAppM ``sorryAx #[type, mkConst ``false]
    else
      return mkConst ``True.intro
  | none => return mkConst ``True.intro

def checkTactic (target : Expr) (tac : Syntax) :
    TermElabM (Option Nat) :=
  withoutModifyingState do
  try
    let goal ← mkFreshExprMVar target
    let (goals, _) ←
      withoutErrToSorry do
      Elab.runTactic goal.mvarId! tac
        (← read) (← get)
    return some goals.length
  catch _ =>
    return none

structure SearchServer where
  name : String
  url : String
  cmd: String
  query : String → Nat → MetaM  (Array SearchResult)
  queryNum : CoreM Nat

def leanSearchServer : SearchServer :=
  {name := "LeanSearch", cmd := "#leansearch", url := "https://leansearch.net/",
   query := queryLeanSearch, queryNum := return leansearch.queries.get (← getOptions)}

def moogleServer : SearchServer :=
  {name := "Moogle", cmd := "#moogle", url := "https://www.moogle.ai/api/search",
   query := queryMoogle, queryNum := return moogle.queries.get (← getOptions)}

instance : Inhabited SearchServer := ⟨leanSearchServer⟩

namespace SearchServer

def getCommandSuggestions (ss : SearchServer) (s : String) (num_results : Nat) :
    MetaM (Array TryThis.Suggestion) := do
  let suggestions ← ss.query s num_results
  return suggestions.map SearchResult.toCommandSuggestion

def getTermSuggestions (ss : SearchServer) (s : String) (num_results : Nat) :
    MetaM (Array TryThis.Suggestion) := do
  let suggestions ← ss.query s num_results
  return suggestions.map SearchResult.toTermSuggestion

def getTacticSuggestionGroups (ss : SearchServer) (s : String) (num_results : Nat) :
    MetaM (Array (String ×  Array TryThis.Suggestion)) := do
  let suggestions ← ss.query s num_results
  return suggestions.map fun sr =>
    let fullName := match sr.type? with
      | some type => s!"{sr.name} (type: {type})"
      | none => sr.name
    (fullName, sr.toTacticSuggestions)

def incompleteSearchQuery (ss : SearchServer) : String :=
  s!"{ss.cmd} query should be a string that ends with a `.` or `?`.\n\
   Note this command sends your query to an external service at {ss.url}."

open Command
def searchCommandSuggestions (ss: SearchServer) (stx: Syntax) (s: TSyntax `str) : CommandElabM Unit := Command.liftTermElabM do
    let s := s.getString
    if s.endsWith "." || s.endsWith "?" then
      let suggestions ← ss.getCommandSuggestions s (← ss.queryNum)
      TryThis.addSuggestions stx suggestions (header := s!"{ss.name} Search Results")
    else
      logWarning <| ss.incompleteSearchQuery

def searchTermSuggestions (ss: SearchServer) (stx: Syntax)
    (s: TSyntax `str)  : TermElabM Unit := do
    let s := s.getString
    if s.endsWith "." || s.endsWith "?" then
      let suggestions ← ss.getTermSuggestions s (← ss.queryNum)
      TryThis.addSuggestions stx suggestions (header := s!"{ss.name} Search Results")
    else
      logWarning <| ss.incompleteSearchQuery

def searchTacticSuggestions (ss: SearchServer) (stx: Syntax) (s: TSyntax `str) : TacticM Unit := do
    let s := s.getString
    if s.endsWith "." || s.endsWith "?" then
      let target ← getMainTarget
      let suggestionGroups ←
          ss.getTacticSuggestionGroups s (← ss.queryNum)
      for (name, sg) in suggestionGroups do
        let sg ←  sg.filterM fun s =>
          let sugTxt := s.suggestion
          match sugTxt with
          | .string s => do
            let stx? := runParserCategory (← getEnv) `tactic s
            match stx? with
            | Except.ok stx =>
              let n? ← checkTactic target stx
              return n?.isSome
            | Except.error _ =>
              pure false
          | _ => pure false
        unless sg.isEmpty do
          TryThis.addSuggestions stx sg (header := s!"From: {name}")
    else
      logWarning <| ss.incompleteSearchQuery

end SearchServer

open Command
/-- Search [LeanSearch](https://leansearch.net/) from within Lean.
Queries should be a string that ends with a `.` or `?`. This works as a command, as a term
and as a tactic as in the following examples. In tactic mode, only valid tactics are displayed.

```lean
#leansearch "If a natural number n is less than m, then the successor of n is less than the successor of m."

example := #leansearch "If a natural number n is less than m, then the successor of n is less than the successor of m."

example : 3 ≤ 5 := by
  #leansearch "If a natural number n is less than m, then the successor of n is less than the successor of m."
  sorry
```
 -/
syntax (name := leansearch_search_cmd) "#leansearch" (str)? : command

@[command_elab leansearch_search_cmd] def leanSearchCommandImpl : CommandElab :=
  fun stx =>
  match stx with
  | `(command| #leansearch $s) => do
    leanSearchServer.searchCommandSuggestions  stx s
  | `(command| #leansearch) => do
    logWarning leanSearchServer.incompleteSearchQuery
  | _ => throwUnsupportedSyntax

/-- Search [Moogle](https://www.moogle.ai/api/search) from within Lean.
Queries should be a string that ends with a `.` or `?`. This works as a command, as a term
and as a tactic as in the following examples. In tactic mode, only valid tactics are displayed.

```lean
#moogle "If a natural number n is less than m, then the successor of n is less than the successor of m."

example := #moogle "If a natural number n is less than m, then the successor of n is less than the successor of m."

example : 3 ≤ 5 := by
  #moogle "If a natural number n is less than m, then the successor of n is less than the successor of m."
  sorry
```
 -/
syntax (name := moogle_search_cmd) "#moogle" (str)? : command

@[command_elab moogle_search_cmd] def moogleCommandImpl : CommandElab :=
  fun stx =>
  match stx with
  | `(command| #moogle $s) => do
    moogleServer.searchCommandSuggestions  stx s
  | `(command| #moogle) => do
    logWarning moogleServer.incompleteSearchQuery
  | _ => throwUnsupportedSyntax

@[inherit_doc leansearch_search_cmd]
syntax (name := leansearch_search_term) "#leansearch" (str)? : term

@[term_elab leansearch_search_term] def leanSearchTermImpl : TermElab :=
  fun stx expectedType? => do
  match stx with
  | `(#leansearch $s) =>
    leanSearchServer.searchTermSuggestions stx s
    defaultTerm expectedType?
  | `(#leansearch) => do
    logWarning leanSearchServer.incompleteSearchQuery
    defaultTerm expectedType?
  | _ => throwUnsupportedSyntax

@[inherit_doc moogle_search_cmd]
syntax (name := moogle_search_term) "#moogle" (str)? : term

@[term_elab moogle_search_term] def moogleTermImpl : TermElab :=
  fun stx expectedType? => do
  match stx with
  | `(#moogle $s) =>
    moogleServer.searchTermSuggestions stx s
    defaultTerm expectedType?
  | `(#moogle) => do
    logWarning moogleServer.incompleteSearchQuery
    defaultTerm expectedType?
  | _ => throwUnsupportedSyntax

@[inherit_doc leansearch_search_cmd]
syntax (name := leansearch_search_tactic)
  withPosition("#leansearch" (colGt str)?) : tactic

@[tactic leansearch_search_tactic] def leanSearchTacticImpl : Tactic :=
  fun stx => withMainContext do
  match stx with
  | `(tactic|#leansearch $s) =>
    leanSearchServer.searchTacticSuggestions stx s
  | `(tactic|#leansearch) => do
    logWarning leanSearchServer.incompleteSearchQuery
  | _ => throwUnsupportedSyntax

@[inherit_doc moogle_search_cmd]
syntax (name := moogle_search_tactic)
  withPosition("#moogle" (colGt str)?) : tactic

@[tactic moogle_search_tactic] def moogleTacticImpl : Tactic :=
  fun stx => withMainContext do
  match stx with
  | `(tactic|#moogle $s) =>
    moogleServer.searchTacticSuggestions stx s
  | `(tactic|#moogle) => do
    logWarning moogleServer.incompleteSearchQuery
  | _ => throwUnsupportedSyntax
