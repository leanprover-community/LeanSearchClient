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

register_option statesearch.queries : Nat :=
  { defValue := 6
    group := "statesearch"
    descr := "Number of results requested from statesearch (default 6)" }

register_option statesearch.revision : String :=
  { defValue := s!"v{Lean.versionString}"
    group := "statesearch"
    descr := "Revision of LeanStateSearch to use" }

register_option leansearchclient.useragent : String :=
  { defValue := "LeanSearchClient"
    group := "leansearchclient"
    descr := "Username for leansearchclient" }

register_option leansearchclient.backend : String :=
  { defValue := "leansearch"
    group := "leansearchclient"
    descr := "The backend to use by default, one of leansearch and moogle" }
