module

public meta import LeanSearchClient.LoogleSyntax

public meta section

/-!
# Loogle query construction

Offline regression tests for
[issue #8](https://github.com/leanprover-community/LeanSearchClient/issues/8):
comments written after (or inside) a `#loogle` command must not leak into the query
sent to the Loogle server, so that the behavior of `#loogle` — in particular under
`#guard_msgs` — does not depend on surrounding comments.

These tests only check the query string constructed from the syntax; they do not
contact the Loogle server.
-/

open Lean Parser LeanSearchClient

/-- Parse a `#loogle` command from a string and return the query it would send. -/
def loogleQueryOfString (src : String) : CoreM String := do
  let stx ← ofExcept <| runParserCategory (← getEnv) `command src
  match stx with
  | `(command| #loogle $args:loogle_filters) => ppLoogleQuery args
  | _ => throwError "not a `#loogle` command"

/-- info: "Option ?a → ?a, \"get!\"" -/
#guard_msgs in
#eval loogleQueryOfString "#loogle Option ?a → ?a, \"get!\""

-- A block comment following the command on a later line (the issue's example).
/-- info: "Option ?a → ?a, \"get!\"" -/
#guard_msgs in
#eval loogleQueryOfString "#loogle Option ?a → ?a, \"get!\"\n\n/- hello -/\n"

-- A line comment following the command on the same line.
/-- info: "Option ?a → ?a, \"get!\"" -/
#guard_msgs in
#eval loogleQueryOfString "#loogle Option ?a → ?a, \"get!\" -- foo\n"

-- A line comment between the command and the next command.
/-- info: "Option ?a → ?a, \"get!\"" -/
#guard_msgs in
#eval loogleQueryOfString "#loogle Option ?a → ?a, \"get!\"\n\n-- a comment\n"

-- A block comment in the middle of the query.
/-- info: "Option ?a → ?a, \"get!\"" -/
#guard_msgs in
#eval loogleQueryOfString "#loogle Option /- mid-query -/ ?a → ?a, \"get!\""

-- A query spread over several lines is collapsed onto a single line.
/-- info: "Option ?a → ?a, \"get!\"" -/
#guard_msgs in
#eval loogleQueryOfString "#loogle Option ?a →\n  ?a, \"get!\""

-- String literals containing comment-like text are unaffected.
/-- info: true -/
#guard_msgs in
#eval show CoreM Bool from
  return (← loogleQueryOfString "#loogle \"a--b\", \"a/-b\"") == "\"a--b\", \"a/-b\""
