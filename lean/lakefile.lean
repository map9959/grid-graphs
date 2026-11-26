import Lake
open Lake DSL

package «gridgraphs» where
  -- add configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.33.1"

@[default_target]
lean_lib GridGraphs where
  -- add library configuration options here

input_file southCapWitness where
  path := "GridGraphs/ResidueTwoUpper/OneGap/SouthCapCoverageAll.xz"
  text := false

/-- Keep the expensive replay's input and native checker in Lake's
build trace, including when the module is opened in the editor. -/
lean_lib SouthCapCertificate where
  needs := #[southCapWitness]
  dynlibs := #[`+GridGraphs.ResidueTwoUpper.TwoGapCoverageRup:dynlib]
