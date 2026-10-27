module

public meta import LeanSearchClient.LoogleSyntax

public meta section

/-!
# Query encoding tests

Offline regression tests for
<https://github.com/leanprover-community/LeanSearchClient/issues/27>.

`#loogle Ideal.span {_, _}` used to reach the Loogle server as `Ideal.span _, _`:
the query was escaped with `System.Uri.escapeUri`, which leaves `{` and `}`
untouched, and curl's URL globbing then dropped (or expanded) the braces,
so the server saw a bare `_` filter and reported
"Cannot search for _. Did you forget to put a term pattern in parentheses?".

These tests pin down the behaviour of `escapeQueryParam` used to build the
request URL: braces and other curl globbing characters are percent-encoded,
and the encoding round-trips through `System.Uri.unescapeUri`. They never
contact a server.
-/

open LeanSearchClient

-- The issue's query: braces must be percent-encoded.
/-- info: "Ideal.span%20%7B_%2C%20_%7D" -/
#guard_msgs in
#eval escapeQueryParam "Ideal.span {_, _}"

-- The parenthesised variants from the issue.
/-- info: "%28Ideal.span%20%7B_%2C%20_%7D%29" -/
#guard_msgs in
#eval escapeQueryParam "(Ideal.span {_, _})"

/-- info: "Ideal.span%20%28%7B_%2C%20_%7D%29" -/
#guard_msgs in
#eval escapeQueryParam "Ideal.span ({_, _})"

-- Characters that were already encoded keep their encoding.
/-- info: "List%20%3Fa%20%E2%86%92%20%3Fa" -/
#guard_msgs in
#eval escapeQueryParam "List ?a → ?a"

/-- info: "Real.sin%2C%20%22two%22%2C%20tsum%2C%20_%20%2A%20_%2C%20_%20%5E%20_%2C%20%7C-%20_%20%3C%20_%20%E2%86%92%20_" -/
#guard_msgs in
#eval escapeQueryParam "Real.sin, \"two\", tsum, _ * _, _ ^ _, |- _ < _ → _"

/-- All encodings round-trip through `System.Uri.unescapeUri`, and the encoded
query contains no characters that curl's URL globbing could interpret
(`{`, `}`, `[`, `]`). -/
def roundTripAndGlobSafe (qs : List String) : Bool :=
  qs.all fun q =>
    let e := escapeQueryParam q
    System.Uri.unescapeUri e == q &&
    !(e.any fun c => c == '{' || c == '}' || c == '[' || c == ']')

/-- info: true -/
#guard_msgs in
#eval roundTripAndGlobSafe
  [ "Ideal.span {_, _}"
  , "(Ideal.span {_, _})"
  , "Ideal.span ({_, _})"
  , "Real.sin, \"two\", tsum, _ * _, _ ^ _, |- _ < _ → _"
  , "List ?a → ?a"
  , "⊢ tsum _ = _ * tsum _"
  , "|- _ < _ → tsum _ < tsum _"
  , "Set.Icc 0 1, {_, _}"
  , "ℕ → ℕ"
  , "\"differ\""
  , "a  b" ]

-- Unreserved characters are passed through unchanged.
/-- info: true -/
#guard_msgs in
#eval escapeQueryParam "AZaz09-._~" == "AZaz09-._~"
