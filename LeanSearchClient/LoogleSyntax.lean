/-
Copyright (c) 2024 Siddhartha Gadgil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil
-/
import Lean.Elab.Tactic.Meta
import Lean.Meta.Tactic.TryThis
import LeanSearchClient.Basic
import LeanSearchClient.Syntax

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

structure LoogleMatch where
  name : String
  type : String
  doc? : Option String
  deriving Inhabited, Repr

inductive LoogleResult where
  | success : Array SearchResult →  LoogleResult
  | failure (error : String) (suggestions: Option <| List String) : LoogleResult
  deriving Inhabited, Repr

def getLoogleQueryJson (s : String) (num_results : Nat := 6) :
  IO <| LoogleResult:= do
  let apiUrl := "https://loogle.lean-lang.org/json"
  let s' := System.Uri.escapeUri s
  let q := apiUrl ++ s!"?q={s'}"
  let s ← IO.Process.output {cmd := "curl", args := #["-X", "GET", q]}
  match Json.parse s.stdout with
  | Except.error e =>
    IO.throwServerError s!"Could not parse JSON from {s.stdout}; error: {e}"
  | Except.ok js =>
  let result? := js.getObjValAs?  Json "hits" |>.toOption
  let result? := result?.filter fun js => js != Json.null
  match result? with
    | some result => do
        match result.getArr? with
        | Except.ok arr =>
          let arr :=  arr[0:num_results] |>.toArray
          let xs : Array SearchResult ←
            arr.mapM fun js => do
              let doc? := js.getObjValAs? String "doc" |>.toOption
              let name? := js.getObjValAs? String "name"
              let type? := js.getObjValAs? String "type"
              match name?, type? with
              | Except.ok name, Except.ok type =>
                pure <| {name := name, type? := some type, docString? := doc?, doc_url? := none, kind? := none}
              | _, _ =>
                IO.throwServerError s!"Could not obtain name and type from {js}"
          return LoogleResult.success xs
        | Except.error e => IO.throwServerError s!"Could not obtain array from {js}; error: {e}, query :{s'}, hits: {result}"
    | _ =>
      let error? := js.getObjValAs? String "error"
      match error? with
        | Except.ok error =>
          let suggestions? :=
            js.getObjValAs? (List String) "suggestions" |>.toOption
          pure <| LoogleResult.failure error suggestions?
        | _ =>
          IO.throwServerError s!"Could not obtain hits or error from {js}"

-- #eval getLoogleQueryJson "List"

def loogleUsage : String :=
  "Loogle Usage

Loogle finds definitions and lemmas in various ways:

By constant:
🔍 Real.sin
finds all lemmas whose statement somehow mentions the sine function.

By lemma name substring:
🔍 \"differ\"
finds all lemmas that have \"differ\" somewhere in their lemma name.

By subexpression:
🔍 _ * (_ ^ _)
finds all lemmas whose statements somewhere include a product where the second argument is raised to some power.

The pattern can also be non-linear, as in
🔍 Real.sqrt ?a * Real.sqrt ?a

If the pattern has parameters, they are matched in any order. Both of these will find List.map:
🔍 (?a -> ?b) -> List ?a -> List ?b
🔍 List ?a -> (?a -> ?b) -> List ?b

By main conclusion:
🔍 |- tsum _ = _ * tsum _
finds all lemmas where the conclusion (the subexpression to the right of all → and ∀) has the given shape.

As before, if the pattern has parameters, they are matched against the hypotheses of the lemma in any order; for example,
🔍 |- _ < _ → tsum _ < tsum _
will find tsum_lt_tsum even though the hypothesis f i < g i is not the last.

If you pass more than one such search filter, separated by commas Loogle will return lemmas which match all of them. The search
🔍 Real.sin, \"two\", tsum, _ * _, _ ^ _, |- _ < _ → _
woould find all lemmas which mention the constants Real.sin and tsum, have \"two\" as a substring of the lemma name, include a product and a power somewhere in the type, and have a hypothesis of the form _ < _ (if there were any such lemmas). Metavariables (?a) are assigned independently in each filter."

open Command
syntax (name := loogle_cmd) "#loogle" str "go" : command
@[command_elab loogle_cmd] def loogleCmdImpl : CommandElab := fun stx =>
  Command.liftTermElabM do
  match stx with
  | `(command| #loogle $s go) =>
    let s := s.getString
    let result ← getLoogleQueryJson s
    match result with
    | LoogleResult.success xs =>
      let suggestions := xs.map SearchResult.toCommandSuggestion
      if suggestions.isEmpty then
        logWarning "Loogle search returned no results"
        logInfo loogleUsage
      else
        TryThis.addSuggestions stx suggestions (header := s!"Loogle Search Results")
    | LoogleResult.failure error suggestions? =>
      logWarning s!"Loogle search failed with error: {error}"
      logInfo loogleUsage
      match suggestions? with
      | some suggestions =>
        let suggestions : List TryThis.Suggestion :=
          suggestions.map fun s =>
            let s := s.replace "\"" "\\\""
            {suggestion := .string s!"#loogle \"{s}\" go"}
        unless suggestions.isEmpty do
          TryThis.addSuggestions stx suggestions.toArray (header := s!"Did you maybe mean")
      | none => pure ()
  | _ => throwUnsupportedSyntax

#loogle "List ?a → ?b" go

#loogle "nonsense" go

#loogle "?a → ?b" go

end LeanSearchClient
