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

lean_lib Bugeaud where
  globs := #[.submodules `Bugeaud]

lean_lib WeylCriteria where
  globs := #[.submodules `WeylCriteria]

lean_lib SRS where
  globs := #[.submodules `SRS]

lean_lib CC where
  globs := #[.submodules `CC]

lean_lib CITED where
  globs := #[.submodules `CITED]

lean_lib AB where
  globs := #[.submodules `AB]

lean_lib BL where
  globs := #[.submodules `BL]

lean_lib B3 where
  globs := #[.submodules `B3]

lean_lib L90 where
  globs := #[.submodules `L90]

lean_lib RT where
  globs := #[.submodules `RT]

-- Author-original results for research-program.html Part I (paradoxical Collatz
-- sequences).  Files live in ./paradoxical/ (a research dir with PDFs/HTML/Python);
-- globbed like the other libs (module namespace = the lowercase dir name).
lean_lib Paradoxical where
  globs := #[.submodules `paradoxical]

-- "Three halves": M4/A3 program (plan-M4A3.html) — subword complexity of the
-- (3/2)^n steering word.  Extract.lean corpusRoots registration: user's call.
lean_lib TH where
  globs := #[.submodules `TH]

-- Flatto–Lagarias–Pollington ⅓-spread theorem (plan-FLT.html, ref "FLP95") —
-- milestone M3 of the (3/2)ⁿ equidistribution ladder.  Build-only registration;
-- Extract.lean corpusRoots registration + db regen: user's call.
lean_lib FLP where
  globs := #[.submodules `FLP]

-- Rational base number system 3/2 (plans plan-B1E2.html + plan-B2A2.html, refs
-- "AFS08"/"Dub09") — the orbit ⌈3x/2⌉, its minimal word g_{3/2}, and K = ω_{3/2}.
-- Shared root of both plans.  Build-only registration; Extract.lean corpusRoots
-- registration + db regen: user's call.
lean_lib RB where
  globs := #[.submodules `RB]

