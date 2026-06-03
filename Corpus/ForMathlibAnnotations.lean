/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import ForMathlib.Analysis.Equidistribution.ModOne
import ForMathlib.Data.Real.NearestInt
import ForMathlib.NumberTheory.Lacunary
import ForMathlib.NumberTheory.PisotNumber
import ForMathlib.LinearAlgebra.Matrix.Hankel
import ForMathlib.LinearAlgebra.Matrix.Determinant.AntiDiagonal
import ForMathlib.RingTheory.PowerSeries.Rationality
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Theorem-database annotations for `ForMathlib` notions

The `ForMathlib/` files are kept clean (Mathlib-style, upstreamable) and do **not**
depend on the corpus annotation attributes. This file applies the database
`@[category]`/`@[AMS]` tags to those declarations *post-hoc* via the `attribute`
command, so they extract as annotated nodes without coupling `ForMathlib` to
`Corpus.Util.Attributes`.

All are tagged `category API` (supporting notions/lemmas for the corpus). The subject is
`AMS 11` (number theory; the power-series block is linear-recurrence theory, 11B37), except the
pure linear-algebra files (Hankel matrices and determinants), which carry `AMS 15`. The
linear-algebra and power-series blocks additionally carry the literature reference `ref "Ber92"`
(Bertin, *Pisot and Salem Numbers*, 1992; the key is expanded in the relevant module docstrings).

Exception: `ForMathlib/NumberTheory/ContinuedFractions/Lagrange.lean` carries its
annotations in-file (`lagrange` is `research solved`), so it is not listed here.
-/

-- `ForMathlib/Analysis/Equidistribution/ModOne.lean`
attribute [category API, AMS 11] IsEquidistributed IsEquidistributedModuloOne

-- `ForMathlib/Data/Real/NearestInt.lean`
attribute [category API, AMS 11] distToNearestInt

-- `ForMathlib/NumberTheory/Lacunary.lean`
attribute [category API, AMS 11]
  IsLacunary IsLacunary.eventually_lt IsLacunaryReal isLacunary_iff_isLacunaryReal
  IsLacunaryReal.eventually_lt

-- `ForMathlib/NumberTheory/PisotNumber.lean`
attribute [category API, AMS 11] IsPisot isPisot_goldenRatio

-- `ForMathlib/LinearAlgebra/Matrix/Hankel.lean`
-- [Ber92] Bertin, Marie José. *Pisot and Salem Numbers.* Springer Science & Business Media, 1992.
attribute [category API, AMS 15, ref "Ber92"]
  Matrix.hankel Matrix.hankel_apply Matrix.hankel_isSymm
  Matrix.kroneckerDet Matrix.kroneckerDet_def

-- `ForMathlib/LinearAlgebra/Matrix/Determinant/AntiDiagonal.lean`
attribute [category API, AMS 15, ref "Ber92"] Matrix.det_eq_unit_mul_pow_of_antidiag_const

-- `ForMathlib/RingTheory/PowerSeries/Rationality.lean`
-- [Ber92] Bertin, Marie José. *Pisot and Salem Numbers.* Springer Science & Business Media, 1992.
attribute [category API, AMS 11, ref "Ber92"]
  IsRationalSeries coeff_coe_mul IsRationalSeries.exists_recurrence
  exists_recurrence.isRationalSeries isRationalSeries_iff_exists_recurrence
  hankelMatrix hankelMatrix_apply kroneckerDet
  kroneckerDet_step eq_zero_of_forall_kroneckerDet_eq_zero
  isRationalSeries_iff_kroneckerDet_eventually_zero
