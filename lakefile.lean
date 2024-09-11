import Lake
open Lake DSL

package "LeanSearchClient" where
  -- add package configuration options here

lean_lib «LeanSearchClient» where
  -- add library configuration options here

@[default_target]
lean_exe "leansearchclient" where
  root := `Main
