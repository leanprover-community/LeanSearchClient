/-
Copyright (c) 2024 Siddhartha Gadgil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil
-/
import Lean
import LeanSearchClient.Basic
import ProofWidgets

/-!
# LeanSearchClient

In this file, we provide syntax for search using the [leansearch API](https://leansearch.net/) from within Lean. It allows you to search for Lean tactics and theorems using natural language.

We provide syntax to make a query and generate `TryThis` options to click or use a code action to use the results. The queries are of three forms:

* `Command` syntax: `#leansearch "search query"` as a command.
* `Term` syntax: `#leansearch "search query"` as a term.
* `Tactic` syntax: `#leansearch "search query"` as a tactic.

In all cases results are displayed in the Lean Infoview and clicking these replaces the query text. In the cases of a query for tactics only valid tactics are displayed.
-/

open Lean Meta Elab Tactic Parser Term ProofWidgets Server

def getQueryJson (s: String)(num_results : Nat := 6) : IO <| Array Json := do
  let apiUrl := "https://leansearch.net/api/search"
  let s' := s.replace " " "%20"
  let q := apiUrl++ s!"?query={s'}&num_results={num_results}"
  let s ← IO.Process.output {cmd := "curl", args := #["-X", "GET", q]}
  let js := Json.parse s.stdout |>.toOption |>.get!
  return js.getArr? |>.toOption |>.get!

structure SearchResult where
  name : String
  type? : Option String
  docString? : Option String
  doc_url? : Option String
  kind? : Option String

def queryNum : CoreM Nat := do
  return leansearch.queries.get (← getOptions)

namespace SearchResult


def ofJson? (js: Json) : Option SearchResult :=
  match js.getObjValAs? String "formal_name" with
  | Except.ok name =>
      let type? := js.getObjValAs? String "formal_type" |>.toOption
      let doc? := js.getObjValAs? String "docstring" |>.toOption
      let doc? := doc?.filter fun s => s != ""
      let docurl? := js.getObjValAs? String "doc_url" |>.toOption
      let kind? := js.getObjValAs? String "kind" |>.toOption
      some {name := name, type? := type?, docString? := doc?, doc_url? := docurl?, kind? := kind?}
  | _ => none

def query (s: String)(num_results : Nat) :
    IO <| Array SearchResult := do
  let jsArr ← getQueryJson s num_results
  return jsArr.filterMap ofJson?

def toCommandSuggestion (sr : SearchResult) : TryThis.Suggestion :=
  let data := match sr.docString? with
    | some doc => s!"{doc}\n"
    | none => ""
  {suggestion := s!"#check {sr.name}", postInfo? := sr.type?.map fun s => s!" -- {s}" ++ s!"\n{data}"}

def toTermSuggestion (sr: SearchResult) : TryThis.Suggestion :=
  match sr.type? with
  | some type => {suggestion := sr.name, postInfo? := some s!" (type: {type})"}
  | none => {suggestion := sr.name}

def toTacticSuggestions (sr: SearchResult) : Array TryThis.Suggestion :=
  match sr.type? with
  | some type => #[{suggestion := s!"apply {sr.name}"},
        {suggestion := s!"have : {type} := {sr.name}"},
        {suggestion := s!"rw [{sr.name}]"},
        {suggestion := s!"rw [← {sr.name}]" }]
  | none => #[]

open scoped Jsx in
def toHtml (sr : SearchResult) : TermElabM (Option Html) := do
  try
    let resultExpr ← mkConstWithLevelParams sr.name.toName
    let resultWithInfos ← Widget.ppExprTagged resultExpr
    return <InteractiveCode fmt={resultWithInfos} />
  catch e =>
    pure none

end SearchResult

def getQueryCommandSuggestions (s: String)(num_results : Nat) :
  IO <| Array TryThis.Suggestion := do
    let searchResults ←  SearchResult.query s num_results
    return searchResults.map SearchResult.toCommandSuggestion

def getQueryTermSuggestions (s: String)(num_results : Nat) :
  IO <| Array TryThis.Suggestion := do
    let searchResults ←  SearchResult.query s num_results
    return searchResults.map SearchResult.toTermSuggestion

def getQueryTacticSuggestionGroups (s: String)(num_results : Nat) :
  IO <| Array (String ×  Array TryThis.Suggestion) := do
    let searchResults ←  SearchResult.query s num_results
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

def checkTactic (target: Expr)(tac: Syntax):
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

open Command

syntax (name := leansearch_cmd) "#leansearch" str : command
open scoped Jsx Json in
@[command_elab leansearch_cmd] def leanSearchImpl : CommandElab :=
  fun stx => Command.liftTermElabM do
  match stx with
  | `(command| #leansearch $s) =>
    let s := s.getString
    if s.endsWith "." || s.endsWith "?" then
      let searchResults ← SearchResult.query s (← queryNum)
      let codeBlocks ← searchResults.filterMapM (liftM <| ·.toHtml)
      let html : Html := .element "ul" #[] (codeBlocks.map (<li>{·}</li>))
      Widget.savePanelWidgetInfo (hash := HtmlDisplay.javascriptHash) (stx := stx)
        (props := do return json% { html : $(← rpcEncode html) })
    else
      logWarning "Lean search query should end with a full stop (period) or a question mark. Note this command sends your query to an external service at https://leansearch.net/."
  | _ => throwUnsupportedSyntax

syntax (name := leansearch_term) "#leansearch" str : term
open scoped Jsx Json in
@[term_elab leansearch_term] def leanSearchTermImpl : TermElab :=
  fun stx expectedType? => do
  match stx with
  | `(#leansearch $s) =>
    let s := s.getString
    if s.endsWith "." || s.endsWith "?" then
      let searchResults ← SearchResult.query s (← queryNum)
      let codeBlocks ← searchResults.filterMapM (liftM <| ·.toHtml)
      let html : Html := .element "ul" #[] (codeBlocks.map (<li>{·}</li>))
      Widget.savePanelWidgetInfo (hash := HtmlDisplay.javascriptHash) (stx := stx)
        (props := do return json% { html : $(← rpcEncode html) })
    else
      logWarning "Lean search query should end with a full stop (period) or a question mark. Note this command sends your query to an external service at https://leansearch.net/."
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
          getQueryTacticSuggestionGroups s (← queryNum)
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
          TryThis.addSuggestions stx sg (header:= s!"From: {name}")
    else
      logWarning "Lean search query should end with a full stop (period) or a question mark. Note this command sends your query to an external service at https://leansearch.net/."
  | _ => throwUnsupportedSyntax
