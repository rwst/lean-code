/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import ForMathlib.Analysis.Equidistribution.ModOne
import ForMathlib.Data.Real.NearestInt
import ForMathlib.NumberTheory.Lacunary
import ForMathlib.NumberTheory.PisotNumber
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

All are tagged `category API` (supporting notions/lemmas for the corpus) with subject
`AMS 11` (number theory; the power-series block is linear-recurrence theory, 11B37).

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

-- `ForMathlib/RingTheory/PowerSeries/Rationality.lean`
attribute [category API, AMS 11]
  IsRationalSeries coeff_coe_mul IsRationalSeries.exists_recurrence
  exists_recurrence.isRationalSeries isRationalSeries_iff_exists_recurrence
  hankelMatrix hankelMatrix_apply kroneckerDet det_eq_unit_mul_pow_of_antidiag_const
  kroneckerDet_step eq_zero_of_forall_kroneckerDet_eq_zero
  isRationalSeries_iff_kroneckerDet_eventually_zero
