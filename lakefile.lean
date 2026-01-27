import Lake
open Lake DSL

package "lean-code" where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib «A087719-existence» where
  -- add library configuration options here

