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
import ForMathlib.RingTheory.PowerSeries.OrderConvergence
import ForMathlib.Analysis.Complex.HardySpace
import ForMathlib.Analysis.InnerProductSpace.Hadamard
import ForMathlib.Algebra.BigOperators.Dyadic
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Theorem-database annotations for `ForMathlib` notions

The `ForMathlib/` files are kept clean (Mathlib-style, upstreamable) and do **not**
depend on the corpus annotation attributes. This file applies the database
`@[category]`/`@[AMS]` tags to those declarations *post-hoc* via the `attribute`
command, so they extract as annotated nodes without coupling `ForMathlib` to
`Corpus.Util.Attributes`.

Most are tagged `category API` (supporting notions/lemmas for the corpus). The subject is
`AMS 11` (number theory; the power-series block is linear-recurrence theory, 11B37), except the
pure linear-algebra files (Hankel matrices and determinants), which carry `AMS 15`, the dyadic
big-operators identities (`AMS 5`, combinatorics), the power-series order-convergence helper
(`AMS 13`, formal power series), and the Hardy-space block, which carries `AMS 30`
(complex analysis, Hardy spaces 30H10). The
linear-algebra, power-series, and Hardy-space blocks additionally carry the literature reference
`ref "Ber92"` (Bertin, *Pisot and Salem Numbers*, 1992; the key is expanded in the relevant module
docstrings). The headline Hardy `H²` characterisation `Complex.memHardy_two_iff_summable` is tagged
`research solved` (a proved, named result), in the spirit of the Lagrange exception below.

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
  multiplierCoeff multiplierMatrix multiplierMatrix_apply

-- `ForMathlib/Analysis/Complex/HardySpace.lean`
-- [Ber92] Bertin, Marie José. *Pisot and Salem Numbers.* Springer Science & Business Media, 1992.
attribute [category API, AMS 30, ref "Ber92"] Complex.hardyIntegralMean Complex.MemHardy
attribute [category research solved, AMS 30, ref "Ber92"] Complex.memHardy_two_iff_summable

-- `ForMathlib/Analysis/InnerProductSpace/Hadamard.lean` — Hadamard's determinant inequality
attribute [category API, AMS 15]
  OrthonormalBasis.norm_det_le_prod_norm Matrix.norm_det_le_prod_col_norm
-- Bertin's Lemma 1.2.5 (Hadamard + AM–GM): squared Frobenius norm `< n` forces `‖det‖ < 1`.
attribute [category API, AMS 15, ref "Ber92"] Matrix.norm_det_lt_one_of_sum_normSq_lt

-- `ForMathlib/Algebra/BigOperators/Dyadic.lean` — dyadic decomposition of `ℕ`-interval sums
attribute [category API, AMS 5] Finset.sum_Ico_two_pow_mul Finset.sum_Ico_one_two_pow

-- `ForMathlib/RingTheory/PowerSeries/OrderConvergence.lean` — order convergence ⇒ coefficient stabilisation
attribute [category API, AMS 13] PowerSeries.coeff_eventuallyEq_of_order_tendsto_top
