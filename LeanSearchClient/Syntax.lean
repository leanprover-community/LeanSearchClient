/-
Copyright (c) 2024 Siddhartha Gadgil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil
-/
module

public meta import Lean.Elab.Tactic.Meta
public meta import Lean.Meta.Tactic.TryThis
public meta import LeanSearchClient.Basic
public meta import Lean.Server.Utils
public meta import Lean.Elab.Command

public meta section

/-!
# LeanSearchClient

In this file, we provide syntax for search using the [leansearch API](https://leansearch.net/).
from within Lean. It allows you to search for Lean tactics and theorems using natural language.

We provide syntax to make a query and generate `TryThis` options to click or
use a code action to use the results.

The queries are of three forms. For leansearch these are:

* `Command` syntax: `#leansearch "search query"` as a command.
* `Term` syntax: `#leansearch "search query"` as a term.
* `Tactic` syntax: `#leansearch "search query"` as a tactic.

In all cases results are displayed in the Lean Infoview and clicking these replaces the query text.
In the cases of a query for tactics only valid tactics are displayed.
-/

namespace LeanSearchClient

open Lean Meta Elab Tactic Parser Term

def useragent : CoreM String :=
  return leansearchclient.useragent.get (← getOptions)

initialize leanSearchCache :
  IO.Ref (Std.HashMap (String × Nat) (Array Json)) ← IO.mkRef {}

initialize stateSearchCache :
  IO.Ref (Std.HashMap (String × Nat × String) (Array Json)) ← IO.mkRef {}

def getLeanSearchQueryJson (s : String) (num_results : Nat := 6) : CoreM <| Array Json := do
  let cache ← leanSearchCache.get
  match cache.get? (s, num_results) with
  | some jsArr => return jsArr
  | none => do
    let apiUrl := (← IO.getEnv "LEANSEARCHCLIENT_LEANSEARCH_API_URL").getD "https://leansearch.net/search"
    -- let q := apiUrl ++ s!"?query={s'}&num_results={num_results}"
    let js := Json.mkObj [("query", Json.arr #[toJson s]), ("num_results", num_results)]
    let out ← IO.Process.output {cmd := "curl", args := #["-X", "POST", apiUrl, "--user-agent", ← useragent, "-H", "accept: application/json", "-H", "Content-Type: application/json", "--data", js.pretty]}
    let js ← match Json.parse out.stdout with
      | Except.ok js => pure js
      | Except.error e => IO.throwServerError s!"Could not parse response from LeanSearch server, error: {e}"
    match js.getArr? with
    | Except.ok jsArr => do
      match jsArr[0]!.getArr?  with
        | Except.ok jsArr =>
        leanSearchCache.modify fun m => m.insert (s, num_results) jsArr
        return jsArr
        | Except.error e => IO.throwServerError s!"Could not obtain inner array from {js}; error: {e}"
    | Except.error e =>
      IO.throwServerError s!"Could not obtain outer array from {js}; error: {e}"

def getStateSearchQueryJson (s : String) (num_results : Nat := 6) (rev : String) : CoreM <| Array Json := do
  let cache ← stateSearchCache.get
  match cache.get? (s, num_results, rev) with
  | .some jsArr => return jsArr
  | none => do
    let apiUrl := (← IO.getEnv "LEANSEARCHCLIENT_LEANSTATESEARCH_API_URL").getD "https://premise-search.com/api/search"
    let s' := System.Uri.escapeUri s
    let q := apiUrl ++ s!"?query={s'}&results={num_results}&rev={rev}"
    let out ← IO.Process.output {cmd := "curl", args := #["-X", "GET", "--user-agent", ← useragent, q]}
    let js ← match Json.parse out.stdout |>.toOption with
      | some js => pure js
      | none => IO.throwServerError s!"Could not contact LeanStateSearch server"
    match js.getArr? with
    | Except.ok jsArr => do
      stateSearchCache.modify fun m => m.insert (s, num_results, rev) jsArr
      return jsArr
    | Except.error e =>
      let .ok err := js.getObjVal? "error"
        | IO.throwServerError s!"{e}"
      let .ok schema := js.getObjVal? "schema"
        | IO.throwServerError s!"{e}"
      let .ok desc := schema.getObjVal? "description"
        | IO.throwServerError s!"{e}"
      IO.throwServerError s!"error: {err}\ndescription: {desc}"

structure SearchResult where
  name : String
  type? : Option String
  docString? : Option String
  doc_url? : Option String
  kind? : Option String
  deriving Repr

namespace SearchResult

def ofLeanSearchJson? (js : Json) : Option SearchResult :=
  match js.getObjVal? "result" with
  | Except.ok js =>
    match js.getObjValAs? (List String) "name" with
    | Except.ok nameList =>
        let name := nameList.foldl (init := "") fun acc s =>
          if acc == "" then s else acc ++ "." ++ s
        let type? := js.getObjValAs? String "type" |>.toOption
        let doc? := js.getObjValAs? String "docstring" |>.toOption
        let doc? := doc?.filter fun s => s != ""
        let docurl? := js.getObjValAs? String "doc_url" |>.toOption
        let kind? := js.getObjValAs? String "kind" |>.toOption
        some {name := name, type? := type?, docString? := doc?, doc_url? := docurl?, kind? := kind?}
    | _ =>
      none
  | _ =>
    none

def ofLoogleJson? (js : Json) : Option SearchResult :=
  match js.getObjValAs? String "name" with
  | Except.ok name =>
      let type? := js.getObjValAs? String "type" |>.toOption
      let doc? := js.getObjValAs? String "doc" |>.toOption
      let doc? := doc?.filter fun s => s != ""
      some {name := name, type? := type?, docString? := doc?, doc_url? := none, kind? := none}
  | _ => none

def ofStateSearchJson? (js : Json) : Option SearchResult :=
  match js.getObjValAs? String "name" with
  | Except.ok name =>
      let type? := js.getObjValAs? String "formal_type" |>.toOption
      let doc? := js.getObjValAs? String "doc" |>.toOption
      let doc? := doc?.filter fun s => s != ""
      let kind? := js.getObjValAs? String "kind" |>.toOption
      some {name := name, type? := type?, docString? := doc?, doc_url? := none, kind? := kind?}
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

def queryStateSearch (s : String) (num_results : Nat) (rev : String):
    MetaM <| Array SearchResult := do
  let jsArr ← getStateSearchQueryJson s num_results rev
  return jsArr.filterMap SearchResult.ofStateSearchJson?

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

You can modify the LeanSearch URL by setting the `LEANSEARCHCLIENT_LEANSEARCH_API_URL` environment variable.
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

/-- Search from within Lean, depending on the option `leansearchclient.backend` (currently only leansearch).
Queries should be a string that ends with a `.` or `?`. This works as a command, as a term
and as a tactic as in the following examples. In tactic mode, only valid tactics are displayed.

```lean
#search "If a natural number n is less than m, then the successor of n is less than the successor of m."

example := #search "If a natural number n is less than m, then the successor of n is less than the successor of m."

example : 3 ≤ 5 := by
  #search "If a natural number n is less than m, then the successor of n is less than the successor of m."
  sorry

In tactic mode, if the query string is not supplied, then [LeanStateSearch](https://premise-search.com) is queried based on the goal state.
```
 -/
syntax (name := search_cmd) "#search" (str)? : command
@[command_elab search_cmd] def searchCommandImpl : CommandElab :=
  fun stx => do
  let server ←  match leansearchclient.backend.get (← getOptions) with
  | "leansearch" => pure leanSearchServer
  | s => throwError s!"Invalid backend {s}, must be leansearch"
  match stx with
  | `(command| #search $s) => do
    server.searchCommandSuggestions  stx s
  | `(command| #search) => do
    logWarning server.incompleteSearchQuery
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

@[inherit_doc search_cmd]
syntax (name := search_term) "#search" (str)? : term

@[term_elab search_term] def searchTermImpl : TermElab :=
  fun stx expectedType? => do
  let server ←  match leansearchclient.backend.get (← getOptions) with
  | "leansearch" => pure leanSearchServer
  | s => throwError s!"Invalid backend {s}, should be leansearch"
  match stx with
  | `(#search $s) =>
    server.searchTermSuggestions stx s
    defaultTerm expectedType?
  | `(#search) => do
    logWarning server.incompleteSearchQuery
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

/-- Search [LeanStateSearch](https://premise-search.com) from within Lean.
Your current main goal is sent as query. The revision to search can be set
using the `statesearch.revision` option. The number of results can be set
using the `statesearch.queries` option.

Hint: If you want to modify the query, you need to use the web interface.

```lean
set_option statesearch.queries 1
set_option statesearch.revision "v4.16.0"

example : 0 ≤ 1 := by
  #statesearch
  sorry
```

You can modify the LeanStateSearch URL by setting the `LEANSEARCHCLIENT_LEANSTATESEARCH_API_URL` environment variable.
-/
syntax (name := statesearch_search_tactic)
  withPosition("#statesearch") : tactic

@[tactic statesearch_search_tactic] def stateSearchTacticImpl : Tactic :=
  fun stx => withMainContext do
  let goal ← getMainGoal
  let target ← getMainTarget
  let state := (← Meta.ppGoal goal).pretty
  let num_results := (statesearch.queries.get (← getOptions))
  let rev := (statesearch.revision.get (← getOptions))
  match stx with
  | `(tactic|#statesearch) =>
    let results ← queryStateSearch state num_results rev
    let suggestionGroups := results.map fun sr =>
      let fullName := match sr.type? with
      | some type => s!"{sr.name} (type: {type})"
      | none => sr.name
    (fullName, sr.toTacticSuggestions)
    let mut foundValidTactic := false
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
          foundValidTactic := true
          TryThis.addSuggestions stx sg (header := s!"From: {name}")
    unless foundValidTactic do
      TryThis.addSuggestions stx (results.map SearchResult.toCommandSuggestion)
  | _ => throwUnsupportedSyntax

@[inherit_doc search_cmd]
syntax (name := search_tactic) "#search" (str)? : tactic

@[tactic search_tactic] def searchTacticImpl : Tactic :=
  fun stx => withMainContext do
  match stx with
  | `(tactic|#search $s) =>
    let server ←  match leansearchclient.backend.get (← getOptions) with
    | "leansearch" => pure leanSearchServer
    | s => throwError s!"Invalid backend {s}, should be leansearch"
    server.searchTacticSuggestions stx s
  | `(tactic|#search) => do
    evalTactic (← `(tactic|#statesearch))
  | _ => throwUnsupportedSyntax

end LeanSearchClient
