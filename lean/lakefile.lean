import Lake
open Lake DSL

package «gridgraphs» where
  -- add configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

@[default_target]
lean_lib GridGraphs where
  -- add library configuration options here
