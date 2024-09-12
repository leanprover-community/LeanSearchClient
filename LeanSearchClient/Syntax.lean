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

def getLeanSearchQueryJson (s : String) (num_results : Nat := 6) : IO <| Array Json := do
  let apiUrl := "https://leansearch.net/api/search"
  let s' := s.replace " " "%20"
  let q := apiUrl ++ s!"?query={s'}&num_results={num_results}"
  let s ← IO.Process.output {cmd := "curl", args := #["-X", "GET", q]}
  let js := Json.parse s.stdout |>.toOption |>.get!
  return js.getArr? |>.toOption |>.get!

def getMoogleQueryJson (s : String) (num_results : Nat := 6) : IO <| Array Json := do
  let apiUrl := "https://www.moogle.ai/api/search"
  let data := Json.arr
    #[Json.mkObj [("isFind", false), ("contents", s)]]
  let s ← IO.Process.output {cmd := "curl", args := #[apiUrl, "-H", "content-type: application/json",  "--data", data.pretty]}
  match Json.parse s.stdout with
  | Except.error e =>
    IO.throwServerError s!"Could not parse JSON from {s.stdout}; error: {e}"
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

def leansearchQueryNum : CoreM Nat := do
  return leansearch.queries.get (← getOptions)

def moogleQueryNum : CoreM Nat := do
  return moogle.queries.get (← getOptions)
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
      let docurl? := none
      let kind? := js.getObjValAs? String "declarationType" |>.toOption
      return some {name := name, type? := type?, docString? := doc?, doc_url? := docurl?, kind? := kind?}
  | _ => return none

def queryLeanSearch (s : String) (num_results : Nat) :
    IO <| Array SearchResult := do
  let jsArr ← getLeanSearchQueryJson s num_results
  return jsArr.filterMap ofLeanSearchJson?

def queryMoogle (s : String) (num_results : Nat) :
    MetaM <| Array SearchResult := do
  let jsArr ← getMoogleQueryJson s num_results
  jsArr.filterMapM ofMoogleJson?



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

def getLeanSearchQueryCommandSuggestions (s : String) (num_results : Nat) :
    IO <| Array TryThis.Suggestion := do
  let searchResults ←  SearchResult.queryLeanSearch s num_results
  return searchResults.map SearchResult.toCommandSuggestion

def getLeanSearchQueryTermSuggestions (s : String) (num_results : Nat) :
    IO <| Array TryThis.Suggestion := do
  let searchResults ←  SearchResult.queryLeanSearch s num_results
  return searchResults.map SearchResult.toTermSuggestion

def getLeanSearchQueryTacticSuggestionGroups (s : String) (num_results : Nat) :
    IO <| Array (String ×  Array TryThis.Suggestion) := do
  let searchResults ←  SearchResult.queryLeanSearch s num_results
  return searchResults.map fun sr =>
    let fullName := match sr.type? with
      | some type => s!"{sr.name} (type: {type})"
      | none => sr.name
    (fullName, sr.toTacticSuggestions)

def getMoogleQueryCommandSuggestions (s: String)(num_results : Nat) :
  MetaM <| Array TryThis.Suggestion := do
    let searchResults ←  SearchResult.queryMoogle s num_results
    return searchResults.map SearchResult.toCommandSuggestion

def getMoogleQueryTermSuggestions (s: String)(num_results : Nat) :
  MetaM <| Array TryThis.Suggestion := do
    let searchResults ←  SearchResult.queryMoogle s num_results
    return searchResults.map SearchResult.toTermSuggestion

def getMoogleQueryTacticSuggestionGroups (s: String)(num_results : Nat) :
  MetaM <| Array (String ×  Array TryThis.Suggestion) := do
    let searchResults ←  SearchResult.queryMoogle s num_results
    return searchResults.map fun sr =>
      let fullName := match sr.type? with
        | some type => s!"{sr.name} (type: {type})"
        | none => sr.name
      (fullName, sr.toTacticSuggestions)

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

def incompleteSearchQuery (name url : String) : String :=
  s!"{name} query should end with a `.` or `?`.\n\
   Note this command sends your query to an external service at {url}."




open Command

syntax (name := leansearch_cmd) "#leansearch" str : command

@[command_elab leansearch_cmd] def leanSearchCommandImpl : CommandElab :=
  fun stx => Command.liftTermElabM do
  match stx with
  | `(command| #leansearch $s) =>
    let s := s.getString
    if s.endsWith "." || s.endsWith "?" then
      let suggestions ← getLeanSearchQueryCommandSuggestions s (← leansearchQueryNum)
      TryThis.addSuggestions stx suggestions (header := "Lean Search Results")
    else
      logWarning <| incompleteSearchQuery "#leansearch" "https://leansearch.net/"
  | _ => throwUnsupportedSyntax

syntax (name := leansearch_term) "#leansearch" str : term

@[term_elab leansearch_term] def leanSearchTermImpl : TermElab :=
  fun stx expectedType? => do
  match stx with
  | `(#leansearch $s) =>
    let s := s.getString
    if s.endsWith "." || s.endsWith "?" then
      let suggestions ← getLeanSearchQueryTermSuggestions s (← leansearchQueryNum)
      TryThis.addSuggestions stx suggestions (header := "Lean Search Results")
    else
      logWarning <| incompleteSearchQuery "#leansearch" "https://leansearch.net/"
    defaultTerm expectedType?
  | _ => throwUnsupportedSyntax

syntax (name := leansearch_tactic) "#leansearch" str : tactic

@[tactic leansearch_tactic] def leanSearchTacticImpl : Tactic :=
  fun stx => withMainContext do
  match stx with
  | `(tactic|#leansearch $s) =>
    let s := s.getString
    if s.endsWith "." || s.endsWith "?" then
      let target ← getMainTarget
      let suggestionGroups ←
          getLeanSearchQueryTacticSuggestionGroups s (← leansearchQueryNum)
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
      logWarning <| incompleteSearchQuery "#leansearch" "https://leansearch.net/"
  | _ => throwUnsupportedSyntax

syntax (name := moogle_cmd) "#moogle" str : command

@[command_elab moogle_cmd] def moogleCommandImpl : CommandElab :=
  fun stx => Command.liftTermElabM do
  match stx with
  | `(command| #moogle $s) =>
    let s := s.getString
    if s.endsWith "." || s.endsWith "?" then
      let suggestions ← getMoogleQueryCommandSuggestions s (← moogleQueryNum)
      TryThis.addSuggestions stx suggestions (header := "Moogle Results")
    else
      logWarning <| incompleteSearchQuery "#moogle" "https://www.moogle.ai/api/search"
  | _ => throwUnsupportedSyntax

syntax (name := moogle_term) "#moogle" str : term

@[term_elab moogle_term] def moogleTermImpl : TermElab :=
  fun stx expectedType? => do
  match stx with
  | `(#moogle $s) =>
    let s := s.getString
    if s.endsWith "." || s.endsWith "?" then
      let suggestions ← getMoogleQueryTermSuggestions s (← moogleQueryNum)
      TryThis.addSuggestions stx suggestions (header := "Moogle Results")
    else
      logWarning <| incompleteSearchQuery "#moogle" "https://www.moogle.ai/api/search"
    defaultTerm expectedType?
  | _ => throwUnsupportedSyntax

syntax (name := moogle_tactic) "#moogle" str : tactic

@[tactic moogle_tactic] def moogleTacticImpl : Tactic :=
  fun stx => withMainContext do
  match stx with
  | `(tactic|#moogle $s) =>
    let s := s.getString
    if s.endsWith "." || s.endsWith "?" then
      let target ← getMainTarget
      let suggestionGroups ←
          getMoogleQueryTacticSuggestionGroups s (← moogleQueryNum)
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
      logWarning <| incompleteSearchQuery "#moogle" "https://www.moogle.ai/api/search"
  | _ => throwUnsupportedSyntax
