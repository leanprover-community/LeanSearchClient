module

public meta import Lean.Data.Options

public meta section

register_option leansearch.queries : Nat :=
  { defValue := 6
    descr := "Number of results requested from leansearch (default 6)" }

register_option loogle.queries : Nat :=
  { defValue := 6
    descr := "Number of results requested from loogle (default 6)" }

register_option statesearch.queries : Nat :=
  { defValue := 6
    descr := "Number of results requested from statesearch (default 6)" }

register_option statesearch.revision : String :=
  { defValue := s!"v{Lean.versionString}"
    descr := "Revision of LeanStateSearch to use" }

register_option leansearchclient.useragent : String :=
  { defValue := "LeanSearchClient"
    descr := "Username for leansearchclient" }

register_option leansearchclient.backend : String :=
  { defValue := "leansearch"
    descr := "The backend to use by default, currently only leansearch" }

namespace LeanSearchClient

/-- Hex digit (`'0'`-`'9'`, `'A'`-`'F'`) for a nibble. -/
private def nibbleToHex (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('A'.toNat + (n - 10))

/-- The RFC 3986 "unreserved" characters, which may appear in a URI without
percent-encoding: `A-Z a-z 0-9 - . _ ~`. -/
private def isUnreservedByte (b : UInt8) : Bool :=
  (0x30 ≤ b && b ≤ 0x39) || -- 0-9
  (0x41 ≤ b && b ≤ 0x5A) || -- A-Z
  (0x61 ≤ b && b ≤ 0x7A) || -- a-z
  b == 0x2D || b == 0x2E || -- - .
  b == 0x5F || b == 0x7E    -- _ ~

/-- Percent-encode a string for use as the value of a URI query parameter.

`System.Uri.escapeUri` only encodes the RFC 3986 reserved characters and
control characters, and lets characters that are invalid in URIs such as
`{` and `}` through unchanged. Literal braces are not merely invalid:
curl interprets them (as well as `[...]`) as URL globbing expressions and
silently rewrites or splits the request, so a `#loogle` query for
`Ideal.span {_, _}` used to reach the server as `Ideal.span _, _`
(<https://github.com/leanprover-community/LeanSearchClient/issues/27>).

This function percent-encodes every byte that is not RFC 3986 unreserved,
so the result decodes to the original string on the server and contains no
characters that curl's URL globbing could interpret. -/
def escapeQueryParam (s : String) : String :=
  s.toUTF8.foldl (init := "") fun out b =>
    if isUnreservedByte b then
      -- `isUnreservedByte` only holds for ASCII bytes, so this is exact.
      out.push (Char.ofNat b.toNat)
    else
      out.push '%' |>.push (nibbleToHex (b.toNat / 16)) |>.push (nibbleToHex (b.toNat % 16))

end LeanSearchClient
