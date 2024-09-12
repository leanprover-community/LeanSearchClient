import Lean.Data.Options

register_option leansearch.queries : Nat :=
  { defValue := 6
    group := "leansearch"
    descr := "Number of results requested from leansearch (default 6)" }
