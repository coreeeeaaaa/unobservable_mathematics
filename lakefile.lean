import Lake
open Lake DSL

package UEM where
  version := v!"1.0.0"
  keywords := #["math", "formal verification"]
  description := "Unobservable Epistemic Mathematics"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.8.0"

@[default_target]
lean_lib UEM where
  srcDir := "src"