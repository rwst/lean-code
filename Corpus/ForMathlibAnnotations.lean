/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import ForMathlib.Analysis.Equidistribution.ModOne
import ForMathlib.Analysis.Equidistribution.IntegralCriterion
import ForMathlib.Analysis.Equidistribution.AddCircleWeyl
import ForMathlib.Data.Real.NearestInt
import ForMathlib.NumberTheory.Lacunary
import ForMathlib.NumberTheory.PisotNumber
import ForMathlib.LinearAlgebra.Matrix.Hankel
import ForMathlib.LinearAlgebra.FiltrationGrowth
import ForMathlib.LinearAlgebra.Matrix.Determinant.AntiDiagonal
import ForMathlib.RingTheory.PowerSeries.Rationality
import ForMathlib.RingTheory.PowerSeries.EventuallyPeriodic
import ForMathlib.RingTheory.PowerSeries.OrderConvergence
import ForMathlib.RingTheory.Polynomial.CoprimeFractionMap
import ForMathlib.Analysis.Complex.HardySpace
import ForMathlib.Analysis.Complex.TaylorSeries
import ForMathlib.Analysis.InnerProductSpace.Hadamard
import ForMathlib.Algebra.BigOperators.Dyadic
import ForMathlib.Analysis.AbsoluteValue.Equivalence
import ForMathlib.NumberTheory.RatPadicValuationNorm
import ForMathlib.NumberTheory.RatPadicFinitePlace
import ForMathlib.NumberTheory.HeightLiouville
import ForMathlib.NumberTheory.HeightTuple
import ForMathlib.NumberTheory.HeightExtension
import ForMathlib.NumberTheory.FinitePlaceProduct
import ForMathlib.NumberTheory.AdjoinRealPlace
import ForMathlib.FieldTheory.RegularExtension
import ForMathlib.Algebra.MvPolynomial.OptionEquiv
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
big-operators identities (`AMS 5`, combinatorics), the power-series order-convergence helper and the
Gauss coprimality-descent helper (`AMS 13`, formal power series / polynomial rings), and the
Hardy-space and Taylor-series blocks, which carry `AMS 30`
(complex analysis, Hardy spaces 30H10). The
linear-algebra, power-series, Hardy-space, and Taylor-series blocks additionally carry the literature reference
`ref "Ber92"` (Bertin, *Pisot and Salem Numbers*, 1992; the key is expanded in the relevant module
docstrings). The headline Hardy `H²` characterisation `Complex.memHardy_two_iff_summable` is tagged
`research solved` (a proved, named result), in the spirit of the Lagrange exception below.

`ForMathlib/NumberTheory/ContinuedFractions/Lagrange.lean` carries **no** corpus annotations and
does **not** import `Corpus.Util.Attributes` — its literature references live in its module docstring,
so it is not listed here. New `ForMathlib/` additions follow the same rule: no in-file
`@[category]`/`@[ref]` annotations and no `Corpus.Util.Attributes` import; citations go in docstrings.
-/

-- `ForMathlib/Analysis/Equidistribution/ModOne.lean`
attribute [category API, AMS 11] IsEquidistributed IsEquidistributedModuloOne
-- Half-open counting: the definition uses closed subintervals, but digit blocks and partition arcs
-- are half-open. The boundary is killed by the degenerate instance `[d, d]` of the hypothesis.
attribute [category API, AMS 11] IsEquidistributedModuloOne.tendsto_count_Ico
-- `WeylCriterion` is the single shared home for the exponential-sum condition: the `BertinPisot`
-- development (Bertin Thm 4.3.2) and the `Bugeaud` chapters (Bugeaud Thm 1.2) formerly each carried
-- a character-for-character identical private copy.
attribute [category API, AMS 11, ref "Ber92" "Bug12"] WeylCriterion

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

-- `ForMathlib/RingTheory/PowerSeries/EventuallyPeriodic.lean`
-- Bertin's Proposition 1.1 composed with the Morse–Hedlund determinism pigeonhole: over an
-- integral domain, a series whose coefficients take finitely many values is rational iff that
-- coefficient sequence is eventually periodic.  [AF17] §8.1 states the hypothesis in the
-- bounded-integer form recorded by the last two.
attribute [category API, AMS 11, ref "Ber92"]
  rightDeterministic_of_recurrence isEventuallyPeriodic_of_recurrence
  isRationalSeries_of_isEventuallyPeriodic_coeff finite_range_of_abs_le
attribute [category research solved, AMS 11, ref "Ber92" "AF17"]
  IsRationalSeries.isEventuallyPeriodic_coeff not_isRationalSeries_of_not_isEventuallyPeriodic
  isRationalSeries_iff_isEventuallyPeriodic_coeff
  IsRationalSeries.isEventuallyPeriodic_coeff_of_abs_le

-- `ForMathlib/LinearAlgebra/FiltrationGrowth.lean`
-- A filtration generated by iterating an injective endomorphism on a finite-dimensional subspace
-- has eventually *exactly* linear dimension growth.  This is the abstract content of the
-- dimension estimate [AF22] Lemma 2.2 (Adamczewski–Faverjon, arXiv:2210.14528), consumed by
-- `CITED/AdamczewskiFaverjonBidegree.lean`; the proof needs no basis and no dual space.
attribute [category API, AMS 15, ref "AF22"]
  Submodule.IsIteratedFiltration Submodule.IsIteratedFiltration.injective_pow
  Submodule.IsIteratedFiltration.finiteDimensional_map
  Submodule.IsIteratedFiltration.finiteDimensional Submodule.IsIteratedFiltration.monotone
  Submodule.IsIteratedFiltration.finrank_map
attribute [category research solved, AMS 15, ref "AF22"]
  Submodule.IsIteratedFiltration.exists_finrank_eq
  Submodule.IsIteratedFiltration.exists_tendsto_finrank_div

-- `ForMathlib/Analysis/Complex/HardySpace.lean`
-- [Ber92] Bertin, Marie José. *Pisot and Salem Numbers.* Springer Science & Business Media, 1992.
attribute [category API, AMS 30, ref "Ber92"] Complex.hardyIntegralMean Complex.MemHardy
attribute [category research solved, AMS 30, ref "Ber92"] Complex.memHardy_two_iff_summable

-- `ForMathlib/Analysis/Complex/TaylorSeries.lean`
-- [Ber92] Bertin, Marie José. *Pisot and Salem Numbers.* Springer Science & Business Media, 1992.
attribute [category API, AMS 30, ref "Ber92"]
  Complex.taylorSeries Complex.taylorSeries_coeff Complex.taylorSeries_eq_mk

-- `ForMathlib/Analysis/InnerProductSpace/Hadamard.lean` — Hadamard's determinant inequality
attribute [category API, AMS 15]
  OrthonormalBasis.norm_det_le_prod_norm Matrix.norm_det_le_prod_col_norm
-- Bertin's Lemma 1.2.5 (Hadamard + AM–GM): squared Frobenius norm `< n` forces `‖det‖ < 1`.
attribute [category API, AMS 15, ref "Ber92"] Matrix.norm_det_lt_one_of_sum_normSq_lt

-- `ForMathlib/Algebra/BigOperators/Dyadic.lean` — dyadic decomposition of `ℕ`-interval sums
attribute [category API, AMS 5] Finset.sum_Ico_two_pow_mul Finset.sum_Ico_one_two_pow

-- `ForMathlib/RingTheory/PowerSeries/OrderConvergence.lean` — order convergence ⇒ coefficient stabilisation
attribute [category API, AMS 13] PowerSeries.coeff_eventuallyEq_of_order_tendsto_top
-- [Ber92] Bertin's `TendstoFormal` — convergence of formal power series in the `X`-adic topology
attribute [category API, AMS 13, ref "Ber92"] PowerSeries.TendstoFormal PowerSeries.tendstoFormal_iff

-- `ForMathlib/RingTheory/Polynomial/CoprimeFractionMap.lean` — Gauss's lemma: unit gcd in `ℤ[X]` ⇒ coprime images in `ℚ[X]`
attribute [category API, AMS 13] Polynomial.isCoprime_map_of_isUnit_gcd

-- `ForMathlib/Analysis/Equidistribution/IntegralCriterion.lean` — Weyl's Riemann-integral criterion
-- [Ber92] Bertin, Marie José. *Pisot and Salem Numbers.* Springer Science & Business Media, 1992.
attribute [category API, AMS 11, ref "Ber92"]
  pieceLen pieceSet pieceIdx stepFun lowerStep upperStep isRiemann_dct
attribute [category research solved, AMS 11, ref "Ber92"]
  tendsto_average_of_indicator_equidistributed

-- `ForMathlib/Analysis/Equidistribution/AddCircleWeyl.lean` — Weyl's criterion on the circle
attribute [category research solved, AMS 11]
  tendsto_average_of_tendsto_fourier tendsto_average_real_of_tendsto_fourier
  tendsto_average_of_weylSums tendsto_average_complex_of_weylSums integral_fourier_eq_zero
attribute [category API, AMS 11]
  haarAddCircle_eq_volume measureReal_closedBall circBump circBump_nonneg circBump_le_one
  circBump_eq_one circBump_eq_zero integral_circBump_le le_integral_circBump
  tendsto_fourier_of_weylSums

-- `ForMathlib/Analysis/AbsoluteValue/Equivalence.lean` — `≤ 1` characterisation of equivalence
attribute [category API, AMS 11]
  AbsoluteValue.isEquiv_iff_le_one_iff AbsoluteValue.IsEquiv.eq_of_apply_eq

-- `ForMathlib/NumberTheory/RatPadicValuationNorm.lean` — padic valuation/norm share a unit ball
attribute [category API, AMS 11] Rat.padicValuation_le_one_iff_padicNorm

-- `ForMathlib/NumberTheory/RatPadicFinitePlace.lean` — finite places of `ℚ` are the `p`-adic abs values
attribute [category API, AMS 11] Rat.HeightOneSpectrum.primeSpectrum
attribute [category research solved, AMS 11]
  Rat.HeightOneSpectrum.place_embedding_primeSpectrum Rat.HeightOneSpectrum.isFinitePlace_padic

-- `ForMathlib/NumberTheory/HeightLiouville.lean`
-- Liouville's inequality `log |β| ≥ -[k : ℚ] h(β)` ([Wal00] p. 82) on top of Mathlib's
-- `NumberTheory/Height`, together with the affine (non-homogeneous) evaluation bound; both are
-- absent from Mathlib, which has the arithmetic inequalities and the projective bound only.
attribute [category API, AMS 11, ref "Wal00"]
  Height.apply_le_mulHeight₁_of_mem_archAbsVal Height.apply_le_mulHeight₁_of_mem_nonarchAbsVal
attribute [category research solved, AMS 11, ref "Wal00"]
  Height.inv_mulHeight₁_le_of_mem_archAbsVal Height.inv_mulHeight₁_le_of_mem_nonarchAbsVal
  Height.neg_logHeight₁_le_log_of_mem_archAbsVal
  Height.neg_logHeight₁_le_log_of_mem_nonarchAbsVal
  Height.abs_log_le_logHeight₁_of_mem_archAbsVal
  Height.logHeight₁_eval_le Height.logHeight₁_eval_le_of_polynomial
  NumberField.inv_mulHeight₁_le_infinitePlace NumberField.neg_logHeight₁_le_log_infinitePlace
  NumberField.inv_mulHeight₁_le_norm NumberField.neg_logHeight₁_le_log_norm

-- `ForMathlib/NumberTheory/HeightTuple.lean`
-- The *projective* height of a tuple under sums drawn from one tuple, hence under matrix
-- products: the cost of one multiplication is an additive `totalWeight K * log m` instead of the
-- multiplicative `m` that the entry-by-entry `Height.mulHeight₁_sum_le` charges.  Mathlib has the
-- matrix-times-vector case (`Height.mulHeight_linearMap_apply_le`) but neither the general
-- form, nor matrix times matrix, nor the two bridges between projective and affine heights.
-- `Height.exists_not_mulHeight_add_le` records why the naive tuple analogue of
-- `mulHeight₁_sum_le` is absent from Mathlib: it is false.
attribute [category API, AMS 11, ref "AF22"]
  Height.hasFiniteMulSupport_iSup_nonarchAbsVal Height.iSup_apply_sum_le
  Height.iSup_apply_sum_le_of_isNonarchimedean
  Matrix.mulHeight Matrix.logHeight Matrix.logHeight_eq_log_mulHeight
  Matrix.one_le_mulHeight Matrix.mulHeight_pos Matrix.mulHeight_ne_zero Matrix.logHeight_nonneg
  Matrix.mulHeight_one Matrix.logHeight_one
attribute [category research solved, AMS 11, ref "AF22"]
  Height.mulHeight_sum_comp_le Height.logHeight_sum_comp_le
  Height.mulHeight_le_prod_mulHeight₁ Height.logHeight_le_sum_logHeight₁
  Height.mulHeight₁_div_le_mulHeight Height.logHeight₁_div_le_logHeight
  Height.not_mulHeight_add_le_of_lt_mulHeight₁ Height.exists_not_mulHeight_add_le
  Matrix.mulHeight_mul_le Matrix.logHeight_mul_le Matrix.logHeight_listProd_le
  Matrix.mulHeight_le_prod_mulHeight₁ Matrix.logHeight_le_sum_logHeight₁
-- The **affine** height of a tuple (a `1` appended to the projective one), which is what bounds
-- the entries of an iterated matrix product, and the sharp height bound for the value of a
-- multivariate polynomial ([Wal00] Lemma 3.7), in which the degree in each variable enters once
-- rather than once per monomial.  Both are absent from Mathlib.
attribute [category API, AMS 11, ref "AF22"]
  Height.iSup_apply_sum_le' Height.iSup_apply_sum_le_of_isNonarchimedean'
  Height.mulHeightAff Height.logHeightAff Height.logHeightAff_eq_log_mulHeightAff
  Height.one_le_mulHeightAff Height.mulHeightAff_pos Height.mulHeightAff_ne_zero
  Height.logHeightAff_nonneg Height.mulHeight_le_mulHeightAff
  Matrix.mulHeightAff Matrix.logHeightAff Matrix.logHeightAff_eq_log_mulHeightAff
  Matrix.one_le_mulHeightAff Matrix.mulHeightAff_pos Matrix.mulHeightAff_ne_zero
  Matrix.logHeightAff_nonneg Matrix.mulHeightAff_one Matrix.logHeightAff_one
attribute [category research solved, AMS 11, ref "AF22"]
  Height.mulHeight_sum_comp_le' Height.mulHeight₁_le_mulHeightAff Height.logHeight₁_le_logHeightAff
  Height.mulHeightAff_le_prod_mulHeight₁ Height.logHeightAff_le_sum_logHeight₁
  Height.mulHeight_pow_le Height.mulHeight_monomial_le
  Matrix.mulHeight₁_le_mulHeightAff Matrix.logHeight₁_le_logHeightAff
  Matrix.mulHeightAff_le_prod_mulHeight₁ Matrix.logHeightAff_le_sum_logHeight₁
  Matrix.mulHeightAff_mul_le Matrix.logHeightAff_mul_le Matrix.logHeightAff_listProd_le
attribute [category research solved, AMS 11, ref "Wal00"]
  Height.mulHeight₁_eval_le_of_degreeOf Height.logHeight₁_eval_le_of_degreeOf

-- `ForMathlib/NumberTheory/HeightExtension.lean`
-- Base change for Mathlib's *relative* height: over a number field `K` of degree `D` the height
-- of a rational point is the `D`-th power of its height over `ℚ` (`h_K = D · h_ℚ`).  Mathlib has
-- no base-change lemmas at all — extending the scalars is listed as a TODO in
-- `Mathlib/NumberTheory/Height/Basic.lean` — so a Subspace-type theorem instantiated over `K`
-- and fed rational data had no way back to the naive height.  The route is the coprime integer
-- tuple, at which every finite place of `K` is invisible (the Bézout argument of
-- `Rat.iSup_finitePlace_apply_eq_one_of_gcd_eq_one`, which never used `ℚ`) and the infinite
-- places contribute `∑_v mult v = [K:ℚ]`; `Rat.exists_primitive_smul` reduces the general tuple
-- to that case by scaling invariance.
attribute [category API, AMS 11, ref "BG06" "B1E2a2"]
  NumberField.iSup_finitePlace_intCast_eq_one_of_gcd_eq_one Rat.exists_primitive_smul
  NumberField.mulHeight₁_ratCast_eq_max NumberField.mulHeight₁_intCast
  NumberField.logHeight₁_intCast NumberField.mulHeight₁_natCast
attribute [category research solved, AMS 11, ref "BG06" "B1E2a2"]
  NumberField.mulHeight_intCast_of_gcd_eq_one
  NumberField.mulHeight_ratCast NumberField.logHeight_ratCast
  NumberField.mulHeight₁_ratCast NumberField.logHeight₁_ratCast
  NumberField.mulHeight_algebraMap_rat NumberField.mulHeight₁_algebraMap_rat

-- `ForMathlib/NumberTheory/FinitePlaceProduct.lean`
-- Values of the places of a number field on rational numbers.  The infinite places give `|q|`;
-- the finite ones are evaluated *jointly* by the product formula,
-- `∏ᶠ w : FinitePlace K, w q = (|q|^{[K:ℚ]})⁻¹`, which computes the finite contribution of a
-- rational `S`-unit with no ramification theory (no local degrees, no `∑_{w|v} e f = D`).
-- `prod_finitePlace_ratCast` is the consumable form: a finite place set carrying the whole
-- support suffices.  Companion of `HeightExtension.lean` for the left-hand side of a
-- Subspace-type inequality.
attribute [category API, AMS 11, ref "BG06" "B1E2a2"]
  NumberField.InfinitePlace.val_apply NumberField.FinitePlace.val_apply
  NumberField.InfinitePlace.apply_ratCast
  NumberField.FinitePlace.apply_intCast_le_one NumberField.FinitePlace.apply_natCast_le_one
  NumberField.FinitePlace.apply_natCast_eq_one_of_mul_eq_one
  NumberField.FinitePlace.val_ne_infinitePlace_val
  NumberField.prod_finitePlace_intCast_le_one
attribute [category research solved, AMS 11, ref "BG06" "B1E2a2"]
  NumberField.finprod_finitePlace_ratCast NumberField.prod_finitePlace_ratCast

-- `ForMathlib/NumberTheory/AdjoinRealPlace.lean`
-- The field generated by a real algebraic number and its defining place: `ℚ⟮δ⟯` is a number
-- field, and the inclusion `ℚ⟮δ⟯ ↪ ℝ` induces the archimedean absolute value that sees `δ`
-- itself rather than a conjugate.  `realEmbeddingPlace_ratCast` is the compatibility a
-- Subspace-type theorem with algebraic coefficients asks of the chosen extension of the
-- distinguished place of `ℚ`.
attribute [category API, AMS 11, ref "Schmidt91" "B1E2a2"]
  NumberField.numberField_adjoin_of_isAlgebraic NumberField.realEmbeddingPlace_apply
  NumberField.realEmbeddingPlace_ratCast

-- `ForMathlib/FieldTheory/RegularExtension.lean`
-- *Regular ⇒ linearly disjoint from algebraic extensions* (Lang, Chap. VIII) in the one direction
-- and for the simple extensions that a primitive element supplies.  Mathlib has the relative
-- algebraic closure `algebraicClosure F E` and the `IntermediateField.LinearDisjoint` API, but no
-- implication between them.
attribute [category API, AMS 12, ref "Lan02"]
  algebraicClosure.minpoly_eq_map_of_eq_bot algebraicClosure.natDegree_minpoly_eq_of_eq_bot
attribute [category research solved, AMS 12, ref "Lan02"]
  algebraicClosure.linearIndependent_pow_of_eq_bot algebraicClosure.eq_zero_of_sum_pow_eq_zero
  algebraicClosure.linearDisjoint_adjoin_of_eq_bot

-- `ForMathlib/Algebra/MvPolynomial/OptionEquiv.lean`
-- The coefficient and degree dictionary for `MvPolynomial.optionEquivRight`, the isomorphism
-- `MvPolynomial (Option σ) R ≃ MvPolynomial σ R[X]`.  Mathlib gives it three defining equations
-- and nothing else, while its left-handed twin `optionEquivLeft` has a full coefficient API.
-- The degree bounds are what turn a bidegree bound on a polynomial in `Y` with coefficients in
-- `R[z]` into per-variable degree bounds for the corresponding polynomial in `Option σ`
-- variables — the shape `Height.logHeight₁_eval_le_of_degreeOf` needs.
attribute [category API, AMS 13, ref "AF22"]
  MvPolynomial.optionEquivRight_monomial MvPolynomial.coeff_coeff_optionEquivRight
  MvPolynomial.coeff_optionEquivRight_symm MvPolynomial.eval₂_optionEquivRight
attribute [category research solved, AMS 13, ref "AF22"]
  MvPolynomial.degreeOf_some_optionEquivRight_symm_le
  MvPolynomial.degreeOf_none_optionEquivRight_symm_le
  MvPolynomial.eval_optionEquivRight_symm
