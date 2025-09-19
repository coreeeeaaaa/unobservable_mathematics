import Lake
open Lake DSL

package UEM

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.8.0"

@[default_target]
lean_lib UEM where
  srcDir := "lean/src"