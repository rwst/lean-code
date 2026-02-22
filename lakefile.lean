import Lake
open Lake DSL

package "lean-code" where
  version := v!"0.1.0"
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"


lean_lib C1
lean_lib C2
lean_lib CRoz
lean_lib POListBool
lean_lib CRozLemma21
lean_lib CRozLemma22
lean_lib CRozLemma23

