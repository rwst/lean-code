/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
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


lean_lib Corpus where
  globs := #[.submodules `Corpus]

lean_lib DistributionModOne where
  globs := #[.submodules `DistributionModOne]

lean_lib ForMathlib where
  globs := #[.submodules `ForMathlib]

lean_lib BertinPisot where
  globs := #[.submodules `BertinPisot]

