import Lake
open Lake DSL

package "LeanSearchClient" where
  -- add package configuration options here

lean_lib «LeanSearchClient» where
  -- add library configuration options here

require proofwidgets from git "https://github.com/leanprover-community/ProofWidgets4"@"v0.0.42"
