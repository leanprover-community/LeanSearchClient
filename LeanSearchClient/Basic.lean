import Lean.Data.Options

register_option leansearch.queries : Nat :=
  { defValue := 6
    group := "leansearch"
    descr := "Number of results requested from leansearch (default 6)" }

register_option moogle.queries : Nat :=
  { defValue := 6
    group := "moogle"
    descr := "Number of results requested from moogle (default 6)" }

register_option loogle.queries : Nat :=
  { defValue := 6
    group := "loogle"
    descr := "Number of results requested from loogle (default 6)" }
