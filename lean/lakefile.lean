import Lake
open Lake DSL

package «gridgraphs» where
  -- add configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.33.1"

@[default_target]
lean_lib GridGraphs where
  -- add library configuration options here
