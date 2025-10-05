/-
Copyright (c) 2024 Siddhartha Gadgil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil
-/
module

public meta import Lean.Elab.Tactic.Meta
public meta import Lean.Parser.Basic
public meta import Lean.Meta.Tactic.TryThis
public meta import LeanSearchClient.Basic
public meta import LeanSearchClient.Syntax

public meta section

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
  | empty : LoogleResult
  | success : Array SearchResult →  LoogleResult
  | failure (error : String) (suggestions: Option <| List String) : LoogleResult
  deriving Inhabited, Repr

initialize loogleCache :
  IO.Ref (Std.HashMap (String × Nat) LoogleResult) ← IO.mkRef {}

def getLoogleQueryJson (s : String) (num_results : Nat := 6) :
  CoreM <| LoogleResult:= do
  let s := s.splitOn "/-" |>.getD 0 s |>.trim
  let s := s.replace "\n" " "
  let cache ← loogleCache.get
  match cache.get? (s, num_results) with
  | some r => return r
  | none => do
    let apiUrl := (← IO.getEnv "LEANSEARCHCLIENT_LOOGLE_API_URL").getD "https://loogle.lean-lang.org/json"
    let s' := System.Uri.escapeUri s
    if s.trim == "" then
      return LoogleResult.empty
    let q := apiUrl ++ s!"?q={s'}"
    let out ← IO.Process.output {cmd := "curl", args := #["-X", "GET", "--user-agent", ← useragent,  q]}
    match Json.parse out.stdout with
    | Except.error _ =>
      IO.throwServerError s!"Could not contact Loogle server"
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
            loogleCache.modify fun m => m.insert (s, num_results) (LoogleResult.success xs)
            return LoogleResult.success xs
          | Except.error e => IO.throwServerError s!"Could not obtain array from {js}; error: {e}, query :{s'}, hits: {result}"
      | _ =>
        let error? := js.getObjValAs? String "error"
        match error? with
          | Except.ok error =>
            let suggestions? :=
              js.getObjValAs? (List String) "suggestions" |>.toOption
            loogleCache.modify fun m => m.insert (s, num_results) (LoogleResult.failure error suggestions?)
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

open Lean.Parser
private def unicode_turnstile := nonReservedSymbol "⊢ "
private def ascii_turnstile := nonReservedSymbol "|- "

/-- The turnstyle uesd bin `#find`, unicode or ascii allowed -/
syntax turnstyle := patternIgnore(unicode_turnstile <|> ascii_turnstile)

/-- a single `#find` filter. The `term` can also be an ident or a strlit,
these are distinguished in `parseFindFilters` -/
syntax loogle_filter := (turnstyle term) <|> term

/-- The argument to `#find`, a list of filters -/
syntax loogle_filters := loogle_filter,*

open Command
/--
Search [Loogle](https://loogle.lean-lang.org/json) from within Lean. This can be used as a command, term or tactic as in the following examples. In the case of a tactic, only valid tactics are displayed.


```lean
#loogle List ?a → ?a

example := #loogle List ?a → ?a

example : 3 ≤ 5 := by
  #loogle Nat.succ_le_succ
  sorry

```

## Loogle Usage

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
woould find all lemmas which mention the constants Real.sin and tsum, have \"two\" as a substring of the lemma name, include a product and a power somewhere in the type, and have a hypothesis of the form _ < _ (if there were any such lemmas). Metavariables (?a) are assigned independently in each filter.

You can modify the Loogle server URL by setting the `LEANSEARCHCLIENT_LOOGLE_API_URL` environment variable.
-/
syntax (name := loogle_cmd) "#loogle" loogle_filters  : command
@[command_elab loogle_cmd] def loogleCmdImpl : CommandElab := fun stx =>
  Command.liftTermElabM do
  match stx with
  | `(command| #loogle $args:loogle_filters) =>
    let s := (← PrettyPrinter.ppCategory ``loogle_filters args).pretty
    let result ← getLoogleQueryJson s
    match result with
    | LoogleResult.empty =>
      logInfo loogleUsage
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
            {suggestion := .string s!"#loogle {s}"}
        unless suggestions.isEmpty do
          TryThis.addSuggestions stx suggestions.toArray (header := s!"Did you maybe mean")
      | none => pure ()
  | _ => throwUnsupportedSyntax

@[inherit_doc loogle_cmd]
syntax (name := just_loogle_cmd)(priority := low) "#loogle" loogle_filters  : command
@[command_elab just_loogle_cmd] def justLoogleCmdImpl : CommandElab := fun _ => return


@[inherit_doc loogle_cmd]
syntax (name := loogle_term) "#loogle" loogle_filters  : term
@[term_elab loogle_term] def loogleTermImpl : TermElab :=
    fun stx expectedType? => do
  match stx with
  | `(#loogle $args) =>
    let s := (← PrettyPrinter.ppCategory ``loogle_filters args).pretty
    let result ← getLoogleQueryJson s
    match result with
    | LoogleResult.empty =>
      logInfo loogleUsage
    | LoogleResult.success xs =>
      let suggestions := xs.map SearchResult.toTermSuggestion
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
            {suggestion := .string s!"#loogle \"{s}\""}
        unless suggestions.isEmpty do
          TryThis.addSuggestions stx suggestions.toArray (header := s!"Did you maybe mean")
      | none => pure ()
    defaultTerm expectedType?
  | _ => throwUnsupportedSyntax

@[inherit_doc loogle_cmd]
syntax (name := loogle_tactic)
  withPosition("#loogle" (ppSpace colGt (loogle_filters)))  : tactic
@[tactic loogle_tactic] def loogleTacticImpl : Tactic :=
    fun stx => do
  match stx with
  | `(tactic|#loogle $args) =>
    let s := (← PrettyPrinter.ppCategory ``loogle_filters args).pretty
    let result ← getLoogleQueryJson s
    match result with
    | LoogleResult.empty =>
      logInfo loogleUsage
    | LoogleResult.success xs => do
      let suggestionGroups := xs.map fun sr =>
         (sr.name, sr.toTacticSuggestions)
      for (name, sg) in suggestionGroups do
        let sg ←  sg.filterM fun s =>
          let sugTxt := s.suggestion
          match sugTxt with
          | .string s => do
            let stx? := runParserCategory (← getEnv) `tactic s
            match stx? with
            | Except.ok stx =>
              let n? ← checkTactic (← getMainTarget) stx
              return n?.isSome
            | Except.error _ =>
              pure false
          | _ => pure false
        unless sg.isEmpty do
          TryThis.addSuggestions stx sg (header := s!"From: {name}")
    | LoogleResult.failure error suggestions? =>
      logWarning s!"Loogle search failed with error: {error}"
      logInfo loogleUsage
      match suggestions? with
      | some suggestions =>
        let suggestions : List TryThis.Suggestion :=
          suggestions.map fun s =>
            {suggestion := .string s!"#loogle \"{s}\""}
        unless suggestions.isEmpty do
          TryThis.addSuggestions stx suggestions.toArray (header := s!"Did you maybe mean")
      | none => pure ()
  | _ => throwUnsupportedSyntax

syntax (name := just_loogle_tactic)(priority := low) "#loogle"  : tactic
@[tactic just_loogle_tactic] def justLoogleTacticImpl : Tactic :=
  fun _ => do
    logWarning loogleUsage

example : 3 ≤ 5 := by
  -- #loogle Nat.succ_le_succ
  decide

-- example := #loogle List ?a → ?b

end LeanSearchClient

-- #loogle "sin", Real → Real, |- Real
