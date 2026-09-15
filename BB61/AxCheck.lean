/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.RouteA
import BB61.Pressure
import BB61.Bernoulli
import BB61.ProductFormula
import BB61.LimitLaw
import BB61.Multiplier
import BB61.NonVanishing
import BB61.Folding
import BB61.TailEvent
import BB61.DiscrepancyFloor
import BB61.Ladder
import BB61.Invariant
import BB61.Certificate
import BB61.Cantor
import BB61.Confinement
import BB61.Realization
import BB61.Saturation
import BB61.PressureCriterion
import BB61.Window
import BB61.Floor
import BB61.Criterion
import BB61.BoxDim
import BB61.Hausdorff
import BB61.Admissible
import BB61.TraceLadder
import BB61.Plateau
import BB61.WeylProduct
import BB61.RouteACeiling
import BB61.FullSupport
import BB61.RouteANormalForm
import BB61.RouteADepth
import BB61.RouteAFamily
import BB61.WindowDiam
import BB61.BlockRecoding
import BB61.CycleMean
import BB61.PriceCompleteness
import BB61.TheoremE
import BB61.Raster
import BB61.GapSqrtThree
import BB61.EntropyBudget
import BB61.LadderReduction
import BB61.LadderScope
import BB61.KernelCriterion
import BB61.Tube
import ForMathlib.Topology.MetricSpace.BoxDimension
import ForMathlib.Topology.Algebra.DenseCover

/-!
# Axiom hygiene for the `BB61` root

Every claimed declaration depends on the standard three axioms
`propext, Classical.choice, Quot.sound` and nothing else — no `native_decide`, no `sorry` —
**with one declared exception**: the four declarations of the cited lane at the bottom of this
file, which additionally report `LY.entropyRate_floor`.  Rebuild this module to check.

Nothing else in `BB61/` is imported from the literature: the splitting, the covering, the
engine and the capstone at `2 + √5` are all proved here, so that result carries no
citation.  The numeric certificate (`goldenFive_cert`) is exact rational arithmetic
checked by the kernel via `norm_num`, not by `native_decide`.

The same holds of the M4 pressure certificate at `2 + √3` (`BB61/Pressure.lean`): its
64-state vector certificate is checked by `decide` on closed `Nat` arithmetic and its
final comparison by `norm_num` on integers of 64 digits.  So does the window modelling
lemma (`BB61/Window.lean`), whose `128`-word cell table is `decide` on closed `Int`
arithmetic.

**The one cited axiom** is `LY.entropyRate_floor` of `CITED/LedrappierYoung.lean` — M3
Theorem 11, the entropy floor for a counterexample, resting on the dimension theory of
hyperbolic measures ([You82] at `d = 2`, [LY85], [BPS99]).  It is quarantined to that file
and consumed only by `BB61/Floor.lean`, which is where `2 + √3` becomes unconditional; the
capstones of `BB61/Window.lean` still carry the floor as a hypothesis and stay std3.

`BB61/Bernoulli.lean` (M5, Route E) is arithmetic only, and self-contained: the integer
pair recursion, the trace identity, the Pisot decay, and the two non-vanishing lemmas
for the factors of the Erdős product.  What it does *not* formalise is again declared in
its docstring — convergence of the infinite products, and the ergodic-theorem step that
identifies the product with the Weyl limit.  Those are §3–4 of `note-1061-M5.html`.

`BB61/Cantor.lean` is M1 Lemma 1, and is where `α > 2` first enters the problem: the two
branches `f₀[0,1] = [0, α⁻¹]` and `f₁[0,1] = [(α-1)/α, 1]` of the coding IFS are separated
by exactly `g = (α-2)/α`, and `g > 0` **iff** `α > 2` (`gap_pos_iff`).  Carried down the
tree that becomes the strong-separation estimate `|π(ε) - π(ε')| ≥ g α^{-k}` for two words
that first differ at letter `k` — parts (ii) and (iv).  Part (i) is the attractor identity
`C(α) = f₀(C(α)) ∪ f₁(C(α))` and the extreme values `min C(α) = 0`, `max C(α) = 1`.  Part
(iii) is injectivity — read straight off (iv) at the first index where two words differ —
and hence `piHomeomorph`, `π` being a continuous bijection from a compact space to a
Hausdorff one; and `volume_cantorSet`, `Leb(C(α)) = 0`.  The note derives that last one
from `dim_H C(α) = log2/log α < 1`, but no dimension theory is needed: `C(α)` is the
*disjoint* union of two copies of itself scaled by `α⁻¹`, so `v = 2α⁻¹v` with `2α⁻¹ < 1`
and `v < ∞`.  Part (v) is the conjugacy `π ∘ σ = τ_α ∘ π` with the one-sided full
`2`-shift, `τ_α` reading the first digit off the threshold `(α-1)/α` — legitimate exactly
because of (ii).  What it does *not* formalise is the dimension *values*
`dim_H C(α) = dim_B C(α) = log 2 / log α` — Mathlib has `HausdorffDimension` but no
self-similar-set formula, and no box dimension at all.

`BB61/Factor.lean` and `BB61/Invariant.lean` (M1 Lemma 6 and Theorem 7) carry the only
measure theory in the root: the continuous factor map `F : {0,1}^ℤ → 𝕋`, the identity
`F(σⁿ ω̃) = ξ αⁿ mod 1`, and the master target — if no `σ`-invariant Borel probability
measure `μ` of the full `2`-shift has `F_*μ = Leb`, then 10.61 holds at `α`.  Everything
there is proved from Mathlib (Prokhorov's compactness of `ProbabilityMeasure` on a compact
space, and the repository's own Riemann criterion for equidistribution); no literature axiom
is cited.

`BB61/Confinement.lean` (M1 Lemma 3 and Prop. 4) is the set-level reading of the same two
files.  The window `K = range wVal` is compact because `{0,1}^ℕ` is, its two endpoints are
attained by the greedy words, and `∑ c_m = -1` gives `diam K ≥ 1 = d - 1` — the note's reason
why no `K`-versus-gap comparison can settle 10.61 at any degree.  Proposition 4 is then a
restatement of `Factor.lean`: the confinement set `X(α) = (C(α) - K) mod 1` *is* the range of
the factor map (the two halves of a two-sided word being independent, `joinW`), so it is
compact for free, and `{ξ αⁿ} ∈ X(α)` holds with **no error term**.  Since `X(α)` is closed
and its complement `1`-periodic, `X(α) ≠ 𝕋` yields one open interval of `(0,1)` missed by
every orbit at every time, hence 10.61 at `α` in the strong form — not even dense
(`not_denseModuloOne_of_confCircle_ne_univ`).  What is *not* here is M1 Cor. 5, the ceiling
`dim_B X(α) ≤ log2/log α + log2/log(1/ρ)` that forces `α > 2^d` for a Route A firing: Mathlib
has no box dimension.  `BB61/Covering.lean` is the effective companion, certifying
`X(α) ≠ 𝕋` by a finite candidate count without ever naming `X(α)`.

`BB61/Realization.lean` (M1 Prop. 8(i)) is the converse of that target for an *ergodic* `μ`:
every ergodic `σ`-invariant measure is realized by a point of `C(α)`, in the sense that the
empirical measures `λ_N` of some orbit `({ξ αⁿ})` converge weak-\* to `F_*μ`.  It is the one
file in the root that leaves Mathlib: it consumes Birkhoff's *pointwise* ergodic theorem from
the vendored `BirkhoffErgodicThm` library (Apache-2.0, `lua-vr/pointwise-birkhoff`), Mathlib
carrying only the mean theorem.  No axiom is added — the port is sorry-free and std3.  One
thing it does not do: the intermediate `ν_N → μ` on the shift space itself, which needs a
cylinder modulus for every continuous observable, where `F`'s own modulus suffices for the
`λ_N` statement.  Nothing downstream uses the stronger form.  The converse of
`tendsto_emp_of_equidistributed` — that `λ_N → Leb` *is* uniform distribution in the counting
sense — is proved in `BB61/WeakStar.lean` (`equidistributed_of_tendsto_emp`) by feeding the
Weyl sums contained in weak-\* convergence to the repository's own converse half of Weyl's
criterion.

`BB61/Words.lean`, `BB61/MeanSelect.lean` and `BB61/Saturation.lean` (M1 Prop. 8(ii) and
Cor. 9) remove the ergodicity, which is what Corollary 9 needs: the master target quantifies
over *all* invariant measures, Lebesgue measure is not extreme, and ergodic decomposition does
not bridge the gap — `Leb = ∫ F_*ν_x dμ(x)` does not force any component to push to `Leb`.
The note cites saturation of the full shift ([BM86] Th. VII, or Sigmund's specification
argument); the proof here uses **no ergodic theorem at all**, so `BB61/Saturation.lean` does
not import the Birkhoff port.  Two observations replace it.  Invariance says the target is an
*exact* mean: `∫ (1/N) ∑_{n<N} φ(σⁿ ω) dμ(ω) = ∫ φ dμ` for every `N`
(`QuadSetup.integral_orbAvg`).  And a mean is realized by an equal-weight sample, chosen
greedily: `MeanSelect.exists_greedy_le` picks points `ω_0, ω_1, …` killing finitely many
mean-zero observables at once, because the partial-sum vector obeys
`‖s_{q+1}‖² ≤ ‖s_q‖² + m C²` — *some* point has `⟨s_q, g⟩ ≤ 0`.  `BB61/Words.lean`
concatenates the sampled windows into one digit word and `BB61/Saturation.lean` runs the
Toeplitz estimate on the running average.  Consequence: M1 Cor. 9 is an **equivalence**
(`equidistributed_iff_exists_invariant`), so the master target of `Invariant.lean` is no
longer merely sufficient, and M3 Theorem 9 holds in the note's own form
(`forall_not_equidistributed_iff_exists_trigCertificate`).

`BB61/Certificate.lean` (M3 Theorem 9) is the completeness statement on top of that: the
hypothesis of the master target — no `σ`-invariant `μ` has `F_*μ = Leb` — holds if and only
if a *finite* certificate witnesses it, a mean-zero real trigonometric polynomial `G` on `𝕋`
with `∫ G ∘ F dμ ≥ c > 0` for every invariant `μ`.  The proof is compactness of `M(σ)` (to
reduce the test functions to finitely many), convexity of `M(σ)` (through explicit mixtures),
and geometric Hahn–Banach in `ℝⁿ`; the trigonometric form is a Fejér approximation.  Note
that the note's Theorem 9 has "10.61 holds at `α`" on the left of its equivalence: passing
between that and the invariant-measure statement is M1 Cor. 9, which
`BB61/Saturation.lean` now supplies, so the note's form is exported there
(`forall_not_equidistributed_iff_exists_trigCertificate`).  M3 Corollary 10 (`Σ₁`-ness)
additionally needs the variational principle for topological pressure, absent from Mathlib,
and is not formalised.

`BB61/Ladder.lean` (M7) is the same kind of file one level up: the arithmetic of a
*trace ladder*.  It proves the dead zone — that the reduced weight profile of the mode
`hₖ` is exponentially small everywhere except in two bands at depths `±k` — from one
identity, `h_{k+1} - α hₖ = e₀ βᵏ`, and nothing else; the past half needs `|b| = 1`,
which is where the plateau's restriction to quadratic *units* comes from.  What it does
*not* formalise is the analysis on top: convergence of the two band products, their
decoupling for a mixing measure, and the resulting limit (§4–§6 of
`note-1061-M7.html`).
-/

-- The Cantor map and the splitting
#print axioms BB61.piVal_le_one
#print axioms BB61.alpha_mul_tPart
#print axioms BB61.QuadSetup.xi_mul_pow
#print axioms BB61.QuadSetup.fract_split
#print axioms BB61.QuadSetup.abs_sPart_le
#print axioms BB61.QuadSetup.sPart_eq_sum

-- The covering
#print axioms BB61.abs_piVal_sub_tCand
#print axioms BB61.QuadSetup.abs_sPart_sub_sCand
#print axioms BB61.QuadSetup.card_cands_le
#print axioms BB61.QuadSetup.exists_cand_near

-- The engine
#print axioms BB61.QuadSetup.exists_avoided_interval

-- M1 Lemma 3 and Prop. 4: the window and the confinement set (`BB61/Confinement.lean`)
#print axioms BB61.futures_joinW
#print axioms BB61.pasts_joinW
#print axioms BB61.QuadSetup.isCompact_windowSet
#print axioms BB61.QuadSetup.wMax_mem_windowSet
#print axioms BB61.QuadSetup.wMin_mem_windowSet
#print axioms BB61.QuadSetup.windowSet_subset_Icc
#print axioms BB61.QuadSetup.tsum_cCoef
#print axioms BB61.QuadSetup.one_le_wMax_sub_wMin
#print axioms BB61.QuadSetup.confSet_eq
#print axioms BB61.QuadSetup.isCompact_confCircle
#print axioms BB61.QuadSetup.confCircle_eq_image
#print axioms BB61.QuadSetup.coe_mem_confCircle
#print axioms BB61.QuadSetup.coe_mul_pow_mem_confCircle
#print axioms BB61.not_denseModuloOne_of_avoided
#print axioms BB61.not_equidistributed_of_avoided
#print axioms BB61.QuadSetup.exists_avoided_interval_of_ne_univ
#print axioms BB61.QuadSetup.not_denseModuloOne_of_confCircle_ne_univ
#print axioms BB61.QuadSetup.not_equidistributed_of_confCircle_ne_univ
#print axioms BB61.exists_padZ_agree
#print axioms BB61.fract_eq_of_coe_eq
#print axioms BB61.QuadSetup.exists_agreeBound_lt
#print axioms BB61.QuadSetup.confSet_subset_closure_orbitRaw
#print axioms BB61.QuadSetup.closure_orbitRaw
#print axioms BB61.QuadSetup.confCircle_subset_closure_orbitCircle
#print axioms BB61.QuadSetup.confCircle_ne_univ_of_avoided

-- The capstone at 2 + √5
#print axioms BB61.goldenFive_cert
#print axioms BB61.routeA_two_add_sqrt5
#print axioms BB61.two_add_sqrt5_not_denseModuloOne
#print axioms BB61.two_add_sqrt5_not_equidistributed
#print axioms BB61.goldenFive_confCircle_ne_univ

-- The M4 pressure certificate at 2 + √3
#print axioms BB61.outEdges_shiftE
#print axioms BB61.sum_outEdges_shiftE
#print axioms BB61.TwoAddSqrt3.certOK_true
#print axioms BB61.TwoAddSqrt3.cert
#print axioms BB61.TwoAddSqrt3.psum_le_pow
#print axioms BB61.TwoAddSqrt3.lt_alpha_pow_four
#print axioms BB61.TwoAddSqrt3.ratio_lt_floor
#print axioms BB61.TwoAddSqrt3.log_rate_lt_floor

-- M5 (Route E): why no factor of the Erdos product vanishes
#print axioms BB61.QuadSetup.pw_eval
#print axioms BB61.QuadSetup.trace_pw
#print axioms BB61.QuadSetup.abs_sub_trace
#print axioms BB61.QuadSetup.exists_int_close
#print axioms BB61.QuadSetup.cos_future_ne_zero
#print axioms BB61.QuadSetup.pw_snd_ne_zero
#print axioms BB61.QuadSetup.cos_past_ne_zero
#print axioms BB61.QuadSetup.past_eq_future
#print axioms BB61.cos_future_ne_zero_twoAddSqrt3
#print axioms BB61.cos_past_ne_zero_twoAddSqrt3
#print axioms BB61.pisot_decay_twoAddSqrt3

-- M7 (Route C, re-scoped): the dead zone of a trace ladder
#print axioms BB61.QuadSetup.lad_step
#print axioms BB61.QuadSetup.lad_pow_sub
#print axioms BB61.QuadSetup.bulk_future
#print axioms BB61.QuadSetup.alpha_mul_abs_beta
#print axioms BB61.QuadSetup.bulk_past
#print axioms BB61.QuadSetup.twoAddSqrt3_lad_four
#print axioms BB61.QuadSetup.twoAddSqrt3_ladE
#print axioms BB61.QuadSetup.bulk_future_twoAddSqrt3

-- M1 Lemma 1: the coding IFS, the gap, separation, the homeomorphism, the conjugacy
#print axioms BB61.gap_pos_iff
#print axioms BB61.sub_inv_eq_gap
#print axioms BB61.image_ifsMap_false
#print axioms BB61.image_ifsMap_true
#print axioms BB61.gap_le_sub_ifsMap
#print axioms BB61.disjoint_image_ifsMap
#print axioms BB61.piVal_eq_ifsMap
#print axioms BB61.gap_le_piVal_sub
#print axioms BB61.piVal_sub_eq_pow_mul
#print axioms BB61.gap_mul_le_abs_piVal_sub
#print axioms BB61.piVal_consW
#print axioms BB61.cantorSet_eq_union
#print axioms BB61.piVal_const_true
#print axioms BB61.isLeast_cantorSet
#print axioms BB61.isGreatest_cantorSet
#print axioms BB61.continuous_piVal
#print axioms BB61.isCompact_cantorSet
#print axioms BB61.injective_piVal
#print axioms BB61.piHomeomorph
#print axioms BB61.volume_image_ifsMap
#print axioms BB61.volume_cantorSet
#print axioms BB61.tauMap_piVal
#print axioms BB61.tauMap_mapsTo

-- M1 Lemma 6: the factor map
#print axioms BB61.shiftZ_iterate
#print axioms BB61.futures_iterate_padZ
#print axioms BB61.pasts_iterate_padZ
#print axioms BB61.QuadSetup.wVal_padWord
#print axioms BB61.QuadSetup.continuous_fMap
#print axioms BB61.abs_piVal_sub_le_of_agree
#print axioms BB61.QuadSetup.abs_wVal_sub_le_of_agree
#print axioms BB61.QuadSetup.abs_fRaw_sub_le_of_agree
#print axioms BB61.QuadSetup.holder_fRaw
#print axioms BB61.QuadSetup.fMap_iterate_padZ

-- M1 Theorem 7: the invariant-measure lemma and the master target
#print axioms BB61.integral_emp
#print axioms BB61.map_empMeasure
#print axioms BB61.integral_haarT
#print axioms BB61.tendsto_emp_of_equidistributed
#print axioms BB61.QuadSetup.map_orbitEmp
#print axioms BB61.QuadSetup.exists_invariant_of_tendsto
#print axioms BB61.QuadSetup.not_equidistributed_of_no_invariant
#print axioms BB61.QuadSetup.exists_invariant_of_equidistributed
#print axioms BB61.QuadSetup.not_equidistributed_of_no_invariant_measure
#print axioms BB61.QuadSetup.exists_invariant_measure_of_equidistributed

-- M1 Prop. 8(i): the ergodic realization converse
#print axioms BB61.invCondexp_ae_eq_const
#print axioms BB61.tendsto_birkhoffAverage_of_ergodic
#print axioms BB61.tendsto_of_dense_of_tendsto_integral
#print axioms BB61.tendsto_cesaro_sub_of_dist
#print axioms BB61.padZ_futures_apply
#print axioms BB61.QuadSetup.abs_fRaw_sub_padZ_le
#print axioms BB61.QuadSetup.tendsto_dist_fMap_padZ
#print axioms BB61.QuadSetup.exists_tendsto_map_of_ergodic
#print axioms BB61.QuadSetup.exists_tendsto_haarT_of_ergodic
#print axioms BB61.integral_fourierRe_eq_zero
#print axioms BB61.integral_fourierIm_eq_zero
#print axioms BB61.weylCriterion_of_tendsto_emp
#print axioms BB61.equidistributed_of_tendsto_emp
#print axioms BB61.QuadSetup.exists_equidistributed_of_ergodic

-- M3 Theorem 9: completeness of the certificate scheme
#print axioms BB61.isCompact_invMeasures
#print axioms BB61.mix_mem_invMeasures
#print axioms BB61.Certificate.no_invariant
#print axioms BB61.Certificate.not_equidistributed
#print axioms BB61.integral_trigPoly_eq_zero
#print axioms BB61.QuadSetup.integral_combo
#print axioms BB61.QuadSetup.exists_certificate
#print axioms BB61.QuadSetup.nonempty_certificate_iff
#print axioms BB61.QuadSetup.exists_trigCertificate
#print axioms BB61.QuadSetup.not_equidistributed_of_trigPoly
#print axioms BB61.QuadSetup.exists_trigCertificate_iff

-- M1 Prop. 8(ii): saturation, and Cor. 9 as an equivalence
#print axioms BB61.sum_range_mul
#print axioms BB61.dist_addCircle_coe_le
#print axioms BB61.exists_common_modulus
#print axioms BB61.abs_sum_sub_le_of_bdd
#print axioms BB61.StageData.word_eq
#print axioms BB61.StageData.agree_shift
#print axioms BB61.StageData.sum_stgLen
#print axioms BB61.StageData.abs_sum_T_sub
#print axioms BB61.StageData.tendsto_avg_of_stage
#print axioms BB61.exists_nonpos_of_integral_eq_zero
#print axioms BB61.exists_greedy_sq_le
#print axioms BB61.exists_greedy_le
#print axioms BB61.QuadSetup.tendsto_winErr
#print axioms BB61.QuadSetup.exists_window
#print axioms BB61.QuadSetup.abs_fRaw_sub_le_agree
#print axioms BB61.QuadSetup.map_iterate_shiftZ
#print axioms BB61.QuadSetup.integral_orbAvg
#print axioms BB61.QuadSetup.abs_orbAvg_le
#print axioms BB61.QuadSetup.atom_estimate
#print axioms BB61.QuadSetup.stage_estimate
#print axioms BB61.QuadSetup.exists_word_of_invariant
#print axioms BB61.QuadSetup.exists_tendsto_map_of_invariant
#print axioms BB61.QuadSetup.exists_equidistributed_of_invariant
#print axioms BB61.QuadSetup.equidistributed_iff_exists_invariant
#print axioms BB61.QuadSetup.equidistributed_iff_exists_invariant_measure
#print axioms BB61.QuadSetup.forall_not_equidistributed_iff
#print axioms BB61.QuadSetup.forall_not_equidistributed_iff_exists_trigCertificate

-- M3 Theorem 12: the pressure criterion, on the ForMathlib topological-pressure file
-- (`ForMathlib/Dynamics/TopologicalPressure.lean`, itself std3 and citation-free)
#print axioms Real.sum_mul_add_negMulLog_le_log_sum_exp
#print axioms MeasureTheory.partitionEntropy_add_integral_le
#print axioms MeasureTheory.integral_birkhoffSum
#print axioms MeasureTheory.entropyRate_add_integral_le_partitionPressure
#print axioms MeasureTheory.entropyRate_le_partitionPressure_of_integral_eq_zero
#print axioms MeasureTheory.le_integral_of_partitionPressure_le
#print axioms Dynamics.partitionPressure_zero
#print axioms Dynamics.partitionPressure_mono
#print axioms Dynamics.partitionPressure_add_const
#print axioms Dynamics.partitionPressure_le
#print axioms Dynamics.le_partitionPressure
#print axioms BB61.measurableSet_coordPartition_fiber
#print axioms BB61.integrable_of_bounded
#print axioms BB61.forall_not_equidistributed_of_partitionPressure_lt
#print axioms BB61.no_invariant_of_partitionPressure_lt
#print axioms Dynamics.joinIter_succ
#print axioms Dynamics.partitionSum_le_sum_stateSum
#print axioms Dynamics.stateSum_le_psum
#print axioms Dynamics.partitionSum_le_of_transferBound
#print axioms Dynamics.partitionPressure_le_of_transferBound
#print axioms PathGrowth.outEdges_detE
#print axioms PathGrowth.psum_detE_succ
#print axioms BB61.TwoAddSqrt3.one_le_vv
#print axioms BB61.TwoAddSqrt3.certB
#print axioms BB61.forall_not_equidistributed_of_transferBound
#print axioms BB61.two_add_sqrt3_not_equidistributed_of_window

-- M4: the window modelling lemma at `2 + sqrt 3` (`BB61/Window.lean`).  The `128`-word cell
-- table is checked by `decide` on closed `Int` arithmetic -- comparisons `0 ≤ A + B√3` are
-- decided by squaring, so `√3` never enters the kernel computation.
#print axioms BB61.TwoAddSqrt3.nonneg_of_nnneg3
#print axioms BB61.TwoAddSqrt3.pos_of_pos3
#print axioms BB61.TwoAddSqrt3.windowOK_true
#print axioms BB61.TwoAddSqrt3.cwZ_bounds
#print axioms BB61.TwoAddSqrt3.cwZ_floor_le
#print axioms BB61.TwoAddSqrt3.stVal_lt
#print axioms BB61.TwoAddSqrt3.stateOf_shiftZ
#print axioms BB61.TwoAddSqrt3.wB_eq_wcert
#print axioms BB61.TwoAddSqrt3.bitAt_wordOf
#print axioms BB61.abs_piVal_sub_range
#print axioms BB61.abs_wVal_sub_range
#print axioms BB61.abs_fRaw_back3_sub
#print axioms BB61.TwoAddSqrt3.trace_eq_four
#print axioms BB61.TwoAddSqrt3.beta_eq
#print axioms BB61.TwoAddSqrt3.inv_alpha
#print axioms BB61.TwoAddSqrt3.winSum_eq
#print axioms BB61.TwoAddSqrt3.eps_eq
#print axioms BB61.TwoAddSqrt3.measurable_gWin
#print axioms BB61.TwoAddSqrt3.abs_gWin_le
#print axioms BB61.TwoAddSqrt3.exp_gWin_le
#print axioms BB61.TwoAddSqrt3.cellPot_add_int
#print axioms BB61.TwoAddSqrt3.cellPotC_coe
#print axioms BB61.TwoAddSqrt3.measurable_cellPotC
#print axioms BB61.TwoAddSqrt3.integral_cell
#print axioms BB61.TwoAddSqrt3.integral_cellPot_unit
#print axioms BB61.TwoAddSqrt3.integral_cellPotC
#print axioms BB61.TwoAddSqrt3.integral_gWin
#print axioms BB61.TwoAddSqrt3.two_add_sqrt3_not_equidistributed_of_mean
#print axioms BB61.TwoAddSqrt3.two_add_sqrt3_not_equidistributed
#print axioms BB61.TwoAddSqrt3.sqrtThree_beta
#print axioms BB61.TwoAddSqrt3.cantorSet_two_add_sqrt3_not_equidistributed

-- `BB61/Criterion.lean`: M1 Corollary 5, the asymptotic form of the covering engine.  The
-- geometric criterion `exists_avoided_interval_of_geom` and its logarithmic reading
-- `routeAExponent < 1`; at `2 + √5` the criterion fires at `(p,q) = (1,1)`, which reproves
-- `routeA_two_add_sqrt5` without the depth-`(70,70)` certificate.  All std3.
#print axioms BB61.QuadSetup.intBound_spec
#print axioms BB61.QuadSetup.cert_ray
#print axioms BB61.QuadSetup.exists_avoided_interval_of_geom
#print axioms BB61.QuadSetup.exists_avoided_interval_of_routeAExponent_lt_one
#print axioms BB61.QuadSetup.not_denseModuloOne_of_routeAExponent_lt_one
#print axioms BB61.QuadSetup.not_equidistributed_of_routeAExponent_lt_one
#print axioms BB61.QuadSetup.confCircle_ne_univ_of_routeAExponent_lt_one
#print axioms BB61.goldenFive_ratio_alpha
#print axioms BB61.goldenFive_ratio_beta
#print axioms BB61.routeA_two_add_sqrt5_of_geom

-- `ForMathlib/Topology/MetricSpace/BoxDimension.lean`: box-counting dimension, the missing
-- ingredient of M1 Lemma 1(iii), Lemma 3 and Corollary 5 as *stated* (the Corollary's
-- conclusion is `BB61/Criterion.lean`, which needs none of this).  ForMathlib-strict: std3,
-- no cited axioms.
#print axioms Metric.upperBoxDimWith_eq
#print axioms Metric.lowerBoxDimWith_eq
#print axioms Metric.lowerBoxDim_le_upperBoxDim
#print axioms Metric.upperBoxDim_le_of_covering
#print axioms Metric.upperBoxDim_le_of_covering_nat
#print axioms Metric.upperBoxDim_le_of_covering_mul_nat
#print axioms Metric.le_upperBoxDim_of_separated
#print axioms Metric.le_lowerBoxDim_of_separated
#print axioms Metric.coveringGrowth_const_mul
#print axioms Metric.coveringGrowthInf_const_mul
#print axioms Metric.exists_isCover_encard_eq_externalCoveringNumber
#print axioms Metric.externalCoveringNumber_add_le
#print axioms Metric.upperBoxDim_add_le
#print axioms Metric.externalCoveringNumber_neg
#print axioms Metric.upperBoxDim_sub_le
#print axioms Real.volume_le_externalCoveringNumber_mul
#print axioms Real.volume_eq_zero_of_upperBoxDim_lt_one
#print axioms Metric.dimH_le_upperBoxDim

-- `BB61/BoxDim.lean`: M1 Lemma 1(iii), Lemma 3 and Corollary 5 *as stated*, on the
-- ForMathlib box dimension.  `dim_B C(α) = log2/log α` (both the upper and the lower value),
-- `dim_B K ≤ log2/log(1/ρ)`, `dim_B X(α) ≤ A(α)`, and the note's own route to 10.61:
-- `A(α) < 1 ⇒ Leb(X(α)) = 0 ⇒ X(α) ≠ 𝕋`.  At `2 + √5` this is a third proof of the capstone.
-- `dimH_cantorSet_le`/`dimH_confSet_le` carry both ceilings over to Mathlib's Hausdorff
-- dimension.  All std3, no citation.
#print axioms BB61.isCover_tCandSet
#print axioms BB61.upperBoxDim_cantorSet_le
#print axioms BB61.isSeparated_cantorPoints
#print axioms BB61.le_lowerBoxDim_cantorSet
#print axioms BB61.upperBoxDim_cantorSet
#print axioms BB61.lowerBoxDim_cantorSet
#print axioms BB61.upperBoxDim_cantorSet_lt_one
#print axioms BB61.dimH_cantorSet_le
#print axioms BB61.QuadSetup.abs_wVal_sub_sCand
#print axioms BB61.QuadSetup.isCover_sCandSet
#print axioms BB61.QuadSetup.upperBoxDim_windowSet_le
#print axioms BB61.QuadSetup.upperBoxDim_confSet_le
#print axioms BB61.QuadSetup.dimH_confSet_le
#print axioms BB61.QuadSetup.volume_confSet_eq_zero_of_routeAExponent_lt_one
#print axioms BB61.QuadSetup.confCircle_ne_univ_of_volume_confSet_eq_zero
#print axioms BB61.QuadSetup.confCircle_ne_univ_of_routeAExponent_lt_one'
#print axioms BB61.goldenFive_inv_absBeta
#print axioms BB61.goldenFive_routeAExponent_lt_one
#print axioms BB61.goldenFive_upperBoxDim_cantorSet
#print axioms BB61.goldenFive_upperBoxDim_confSet_lt_one
#print axioms BB61.goldenFive_volume_confSet
#print axioms BB61.two_add_sqrt5_not_equidistributed_of_boxDim

-- `ForMathlib/MeasureTheory/MassDistribution.lean` and `BB61/Hausdorff.lean`: the Hausdorff
-- *floor*, which completes M1 Lemma 1(iii) to `dim_H C(α) = dim_B C(α) = log2/log α`.  Mathlib
-- has no IFS theory, so the measure the mass distribution principle needs is built here: the
-- fair coin on `{0,1}^ℕ` pushed forward by `π`, Frostman-estimated off Lemma 1(iv).  All std3,
-- no citation.
#print axioms MeasureTheory.Measure.smul_le_hausdorffMeasure_of_frostman
#print axioms MeasureTheory.Measure.le_dimH_of_frostman
#print axioms BB61.coinMeasure_agreeSet
#print axioms BB61.codingMeasure_cantorSet
#print axioms BB61.preimage_subset_agreeSet
#print axioms BB61.codingMeasure_le_pow_of_sep
#print axioms BB61.codingMeasure_le_pow_of_ediam
#print axioms BB61.inv_rpow_logRatio
#print axioms BB61.codingMeasure_frostman
#print axioms BB61.le_dimH_cantorSet
#print axioms BB61.dimH_cantorSet
#print axioms BB61.dimH_eq_upperBoxDim_cantorSet

-- `BB61/Admissible.lean`: M1 Proposition 14 -- the licence for citing the theta-shift
-- literature at `C(alpha)` at all.  Every `{0,1}`-word IS the greedy Renyi-Parry
-- alpha-expansion of its own value, and the converse (`greedy_tsum`) makes the note's
-- "hence" an equality: `C(alpha) = (alpha-1) * B(alpha)`.  All std3, no citation.
#print axioms BB61.greedyDigit_boolVal
#print axioms BB61.betaT_boolVal
#print axioms BB61.greedyExp_boolVal
#print axioms BB61.isAdmissible_bitZ
#print axioms BB61.range_bitZ_subset_admissible
#print axioms BB61.range_bitZ_subset_closure_admissible
#print axioms BB61.boolVal_const_true_lt_one_iff
#print axioms BB61.two_le_floor
#print axioms BB61.bitZ_lt_floor
#print axioms BB61.greedy_partial
#print axioms BB61.greedy_tsum
#print axioms BB61.injOn_greedyExp
#print axioms BB61.boolCoded_eq_range
#print axioms BB61.cantorSet_eq_image_boolCoded

-- `ForMathlib/NumberTheory/TraceLadder.lean` and `BB61/TraceLadder.lean`: M1 Proposition 15 --
-- the integer solutions of alpha's recurrence are EXACTLY the trace ladders Tr(lambda alpha^k)
-- over the codifferent, and lambda |-> (h_k) is a Z-module isomorphism d^-1 = R = Z^d.  Euler's
-- identity d^-1 = f'(alpha)^-1 Z[alpha] is Mathlib's `traceForm_dualSubmodule_adjoin`.  All
-- std3, no citation.
#print axioms TraceLadder.IsRecSeq.ext
#print axioms TraceLadder.IsRecSeq.mem_of_init_mem
#print axioms TraceLadder.mem_codiff_iff
#print axioms TraceLadder.ladderMap_injective
#print axioms TraceLadder.finrank_eq_natDegree
#print axioms TraceLadder.exists_ladder_eq_init
#print axioms BB61.recurrence_of_trace_ladder
#print axioms BB61.mem_codifferent_iff
#print axioms BB61.integer_recurrence_iff_trace_ladder
#print axioms BB61.codifferentEquivLadders
#print axioms BB61.laddersEquivInit
#print axioms BB61.codifferent_eq_smul_adjoin
#print axioms BB61.QuadSetup.isRecSeq_lad
#print axioms BB61.QuadSetup.eq_lad_of_isRecSeq
#print axioms BB61.QuadSetup.recModule_eq_range_lad
#print axioms BB61.QuadSetup.lad_iff_trace_ladder

-- `BB61/Plateau.lean`: M1 Observation 16(ii) -- the exact shape of the two weight bands of a ladder
-- mode, and the mirror.  The past profile is the future profile times |b|^d |beta-1|/(alpha-1), so
-- the two are one shape read in opposite directions EXACTLY at a quadratic unit.  Plus the rate:
-- each band is within C rho^{2k} of a fixed shape.  All std3, no citation.
#print axioms BB61.QuadSetup.lad_conj_step
#print axioms BB61.QuadSetup.lad_binet
#print axioms BB61.QuadSetup.abs_beta_eq_inv_alpha_iff
#print axioms BB61.QuadSetup.inv_alpha_lt_abs_beta
#print axioms BB61.QuadSetup.lad_mul_beta_pow
#print axioms BB61.QuadSetup.abs_lad_mul_beta_pow_sub_int
#print axioms BB61.QuadSetup.abs_future_sub_shape
#print axioms BB61.QuadSetup.abs_past_sub_shape
#print axioms BB61.QuadSetup.abs_shapePast_profile
#print axioms BB61.QuadSetup.abs_future_band
#print axioms BB61.QuadSetup.abs_past_band
#print axioms BB61.QuadSetup.shapePast_eq_of_norm_one
#print axioms BB61.QuadSetup.past_weight_eq_neg_future_weight

-- `BB61/WeylProduct.lean`: M1 Observation 16(i) -- the two one-sided Erdos products themselves.
-- Both are `Multipliable` at every mode; along a ladder the future factor converges to
-- `biProd (shapeFut)` unconditionally and the past factor to `biProd (shapePast)` at a unit,
-- so the Weyl limit converges to the product.  At norm +1 the two are equal at every mode;
-- at any unit they agree once `lambda' = +- alpha^s lambda` (`e0 = -f0` is `s = 0`), and NOT
-- in general -- see `BB61/m1_obs16i.py`.  All std3, no citation.
#print axioms BB61.ncos_eq_of_add_int
#print axioms BB61.abs_ncos_sub_ncos_le
#print axioms BB61.abs_tprod_sub_tprod_le
#print axioms BB61.multipliable_ncos_of_geom_tail
#print axioms BB61.QuadSetup.multipliable_futProd
#print axioms BB61.QuadSetup.multipliable_pastProd
#print axioms BB61.QuadSetup.shapeProd_succ
#print axioms BB61.QuadSetup.tendsto_shapeProd
#print axioms BB61.QuadSetup.lad_eq_of_binet
#print axioms BB61.QuadSetup.shapeFut_pow_add
#print axioms BB61.QuadSetup.shapePast_pow_add
#print axioms BB61.QuadSetup.shapeFutC_pow_add
#print axioms BB61.QuadSetup.goodAmp_shapeFut
#print axioms BB61.QuadSetup.goodAmp_shapePast
#print axioms BB61.QuadSetup.abs_futProd_sub_shapeProd_le
#print axioms BB61.QuadSetup.abs_pastProd_sub_shapeProd_le
#print axioms BB61.QuadSetup.tendsto_futProd
#print axioms BB61.QuadSetup.tendsto_pastProd
#print axioms BB61.QuadSetup.tendsto_weylProd
#print axioms BB61.QuadSetup.pastProd_eq_futProd
#print axioms BB61.QuadSetup.weylProd_eq_sq
#print axioms BB61.QuadSetup.ncos_mul_beta_pow
#print axioms BB61.QuadSetup.biProd_eq_of_reflect
#print axioms BB61.QuadSetup.biProd_shapePast_eq_shapeFutC
#print axioms BB61.QuadSetup.biProd_mul_alpha
#print axioms BB61.QuadSetup.biProd_shapePast_eq_of_pow
#print axioms BB61.QuadSetup.ladE_eq_neg_ladF_iff
#print axioms BB61.QuadSetup.tendsto_pastProd_shapeFut
#print axioms BB61.QuadSetup.tendsto_weylProd_sq
#print axioms BB61.QuadSetup.tendsto_weylProd_sq_trace
#print axioms BB61.weylProd_eq_sq_twoAddSqrt3

-- `BB61/RouteACeiling.lean` is M1 Corollary 5's lower bound on rho and the ceiling
-- alpha > 2^d, at general degree (a monic integer polynomial with nonzero constant term,
-- whose product of roots is therefore a nonzero integer) and at degree two, where the whole
-- bound is the single identity alpha |beta| = |b| >= 1.  All std3, no citation.
#print axioms BB61.norm_multisetProd_le_pow
#print axioms BB61.one_le_mul_pow_of_monic_int
#print axioms BB61.card_add_one_eq_natDegree
#print axioms BB61.rpow_neg_inv_le_of_one_le_mul_pow
#print axioms BB61.mul_log_inv_le_log
#print axioms BB61.routeA_ge_of_one_le_mul_pow
#print axioms BB61.two_pow_lt_of_routeA_lt_one
#print axioms BB61.two_pow_natDegree_lt_of_routeA_lt_one
#print axioms BB61.QuadSetup.b_ne_zero_of_beta_ne_zero
#print axioms BB61.QuadSetup.one_le_alpha_mul_abs_beta
#print axioms BB61.QuadSetup.inv_alpha_le_abs_beta
#print axioms BB61.QuadSetup.log_two_div_log_alpha_le_routeAExponent
#print axioms BB61.QuadSetup.two_lt_alpha_of_routeAExponent_lt_one
#print axioms BB61.QuadSetup.routeAExponent_of_beta_eq_zero
#print axioms BB61.QuadSetup.two_mul_log_two_div_log_alpha_le_routeAExponent
#print axioms BB61.QuadSetup.four_lt_alpha_of_routeAExponent_lt_one
#print axioms BB61.QuadSetup.one_le_routeAExponent_of_alpha_le_four
#print axioms BB61.QuadSetup.quadPoly_monic
#print axioms BB61.QuadSetup.quadPoly_map_eq
#print axioms BB61.QuadSetup.quadPoly_roots
#print axioms BB61.QuadSetup.one_le_alpha_mul_abs_beta_of_monic
#print axioms BB61.QuadSetup.quadPoly_natDegree

-- `BB61/FullSupport.lean` is the R0 note of `plan-BB61-counterexample.html`: the first
-- POSITIVE instances of `confCircle` in the folder.  `C(alpha) - K` is computed exactly at
-- the two quadratic Pisot units in (2,3] -- [-sqrt2/2, 2+sqrt2/2] at 1+sqrt2 and [0,2] at
-- (3+sqrt5)/2 -- by one greedy covering lemma and (at 1+sqrt2) one digit relabelling, so
-- X(alpha) = T at both.  No thickness, no gap lemma, no citation.  All std3.
#print axioms BB61.sub_covDigitAt_mem
#print axioms BB61.covRes_mem
#print axioms BB61.covRes_partial
#print axioms BB61.tsum_covDigit
#print axioms BB61.tsum_digit_mem_Icc
#print axioms BB61.dR_loBit_add_dR_hiBit
#print axioms BB61.QuadSetup.piVal_eq_tsum
#print axioms BB61.QuadSetup.wVal_eq_tsum
#print axioms BB61.QuadSetup.confCircle_eq_univ_of_Icc_subset
#print axioms BB61.QuadSetup.mem_confSet
#print axioms BB61.QuadSetup.sub_wVal_eq_of_beta_eq_inv
#print axioms BB61.goldenSq_beta_eq_inv
#print axioms BB61.goldenSq_one_le_three_beta
#print axioms BB61.goldenSq_Icc_subset_confSet
#print axioms BB61.goldenSq_wMax
#print axioms BB61.goldenSq_wMin
#print axioms BB61.goldenSq_confSet
#print axioms BB61.goldenSq_confCircle
#print axioms BB61.goldenSq_no_avoided_interval
#print axioms BB61.tsum_ite_even
#print axioms BB61.tsum_ite_odd
#print axioms BB61.tsum_dR_parityFlip
#print axioms BB61.tsum_dR_consW
#print axioms BB61.silver_inv
#print axioms BB61.silver_beta
#print axioms BB61.silver_odd_sum
#print axioms BB61.silver_even_sum
#print axioms BB61.silver_sub_wVal
#print axioms BB61.silver_Icc_subset_confSet
#print axioms BB61.silver_wMax
#print axioms BB61.silver_wMin
#print axioms BB61.silver_diam_window
#print axioms BB61.silver_confSet
#print axioms BB61.silver_confSet_length
#print axioms BB61.silver_confCircle
#print axioms BB61.silver_no_avoided_interval

-- `BB61/RouteANormalForm.lean` is M2 Proposition 1: the normal form of the Route A
-- criterion.  With L = log2 alpha and R = log2(1/rho), the four statements A(alpha) < 1,
-- (L-1)(R-1) > 1, R > L/(L-1) and rho < 2^{-L/(L-1)} are equivalent, and A(alpha) log2 alpha
-- = 1 + L/R.  Corollary 6 follows at degree two, where rho = |b|/alpha exactly: Route A
-- covers the quadratic units in exactly (4, infinity).  Pure algebra plus `Real.logb`; the
-- note's own QA records that Proposition 1 uses nothing.  All std3, no citation.
#print axioms BB61.inv_add_inv_lt_one_iff
#print axioms BB61.one_lt_mul_sub_one_iff
#print axioms BB61.one_lt_div_sub_one
#print axioms BB61.div_sub_one_lt_div_sub_one
#print axioms BB61.tendsto_div_sub_one_atTop
#print axioms BB61.lt_logb_two_inv_iff_lt_rpow
#print axioms BB61.inv_add_inv_mul_eq
#print axioms BB61.QuadSetup.routeAExponent_eq_inv_add_inv
#print axioms BB61.QuadSetup.one_lt_logAlpha_iff
#print axioms BB61.QuadSetup.one_lt_logAlpha
#print axioms BB61.QuadSetup.logAlpha_pos
#print axioms BB61.QuadSetup.logRhoInv_pos
#print axioms BB61.QuadSetup.routeAExponent_lt_one_iff_one_lt_normalForm
#print axioms BB61.QuadSetup.routeAExponent_lt_one_iff_threshold_lt_logRhoInv
#print axioms BB61.QuadSetup.routeAExponent_lt_one_iff_abs_beta_lt_rpow
#print axioms BB61.QuadSetup.routeAExponent_mul_logAlpha
#print axioms BB61.QuadSetup.one_lt_logRhoInv_of_lt_one
#print axioms BB61.QuadSetup.not_equidistributed_of_normalForm
#print axioms BB61.QuadSetup.not_equidistributed_of_abs_beta_lt_rpow
#print axioms BB61.QuadSetup.confCircle_ne_univ_of_normalForm
#print axioms BB61.QuadSetup.beta_ne_zero_of_b_ne_zero
#print axioms BB61.QuadSetup.abs_beta_eq_div
#print axioms BB61.QuadSetup.logRhoInv_eq_sub
#print axioms BB61.QuadSetup.routeAExponent_lt_one_iff_quadratic
#print axioms BB61.QuadSetup.routeAExponent_lt_one_iff_four_lt

-- `BB61/RouteADepth.lean` is M2 Theorem 2(i): certified depths exist, along the BALANCED ray
-- M' = ceil(M L / R).  The covering total T(M,M') = 2^{M+M'}(alpha^{-M} + C rho^{M'}/(1-rho))
-- obeys log2 T <= 1 + log2(1 + C/(1-rho)) + M (1-(L-1)(R-1))/R, whose slope is negative
-- EXACTLY under Proposition 1's normal form, so T -> 0 and every threshold is eventually
-- cleared.  At degree two the engine's certificate value is 2(2K+1) times T with C = 1+rho,
-- so Route A's avoided interval comes out at a named depth.  All std3, no citation.
#print axioms BB61.slope_eq
#print axioms BB61.slope_neg_iff
#print axioms BB61.pow_balancedDepth_le
#print axioms BB61.two_pow_balancedDepth_le
#print axioms BB61.coverTotal_balancedDepth_le
#print axioms BB61.coverTotal_pos
#print axioms BB61.logb_coverTotal_balancedDepth_le
#print axioms BB61.tendsto_bound_atBot
#print axioms BB61.tendsto_coverTotal_balancedDepth
#print axioms BB61.eventually_coverTotal_balancedDepth_lt
#print axioms BB61.coverTotal_balancedDepth_lt_of_logb_le
#print axioms BB61.QuadSetup.two_rpow_logAlpha
#print axioms BB61.QuadSetup.two_rpow_neg_logRhoInv
#print axioms BB61.QuadSetup.cert_eq_coverTotal
#print axioms BB61.QuadSetup.routeA_depth_bound
#print axioms BB61.QuadSetup.slope_neg_iff_routeAExponent_lt_one
#print axioms BB61.QuadSetup.eventually_certificate_balancedDepth
#print axioms BB61.QuadSetup.certificate_of_balancedDepth_bound
#print axioms BB61.QuadSetup.exists_avoided_interval_at_balancedDepth
#print axioms BB61.QuadSetup.not_equidistributed_at_balancedDepth

-- `BB61/RouteAFamily.lean` is M2 Theorem 5: the explicit family X^d - aX^{d-1} - 1 that
-- inhabits Route A in every degree.  (i) alpha is the ONLY root of modulus >= 1 and is simple,
-- so alpha is Pisot; its minimal polynomial IS the trinomial, so the degree is exactly d and
-- alpha is a unit.  (ii) every conjugate has a |z|^{d-1} <= 2.  (iii) a >= 2^{d+1} forces
-- A(alpha) < 1.  (iv) at d = 2 the member is a QuadSetup, so the conclusion is 10.61 itself for
-- every a >= 4, first member 2+sqrt5; at d = 3 the conjugates have |z|^2 alpha = 1, so
-- A log2 alpha = 3 (ON the Prop. 4 ceiling) and A < 1 iff alpha > 8 iff a >= 8.  Rouche is not
-- used (Mathlib has no Rouche): the root count is a product-of-moduli argument in integer
-- powers only.  All std3, no citation.
#print axioms BB61.familyPoly_monic
#print axioms BB61.familyPoly_natDegree
#print axioms BB61.familyPoly_coeff_zero
#print axioms BB61.aeval_familyPoly
#print axioms BB61.exists_root_Ioo
#print axioms BB61.pow_card_le_multisetProd
#print axioms BB61.multisetProd_pow
#print axioms BB61.norm_multisetProd_eq
#print axioms BB61.familyPoly_map
#print axioms BB61.eval_familyPoly_map
#print axioms BB61.root_mul_eq_one
#print axioms BB61.norm_pow_mul_norm_sub
#print axioms BB61.le_norm_of_one_le_norm
#print axioms BB61.inv_le_norm_pow_of_norm_lt_one
#print axioms BB61.mul_norm_pow_le_two
#print axioms BB61.card_big_roots_eq_one
#print axioms BB61.norm_lt_one_of_mem_roots_of_ne
#print axioms BB61.isPisot_family
#print axioms BB61.familyConjBound_pos
#print axioms BB61.familyConjBound_pow
#print axioms BB61.norm_le_familyConjBound
#print axioms BB61.inv_add_inv_lt_one_of_deg
#print axioms BB61.routeA_family_lt_one
#print axioms BB61.familyQuad_root
#print axioms BB61.lt_familyQuad_alpha
#print axioms BB61.familyQuad_isPisot
#print axioms BB61.four_lt_familyQuad_alpha_iff
#print axioms BB61.familyQuad_routeAExponent_lt_one_iff
#print axioms BB61.familyQuad_not_equidistributed
#print axioms BB61.familyQuad_not_denseModuloOne
#print axioms BB61.familyQuad_four_alpha
#print axioms BB61.multisetProd_le_one
#print axioms BB61.multisetProd_lt_one
#print axioms BB61.minpoly_eq_familyPoly
#print axioms BB61.familyPoly_irreducible
#print axioms BB61.minpoly_natDegree_family
#print axioms BB61.minpoly_coeff_zero_family
#print axioms BB61.norm_sq_of_quadratic
#print axioms BB61.norm_sq_mul_eq_one_cubic
#print axioms BB61.routeA_cubic_mul_logb
#print axioms BB61.routeA_cubic_lt_one_iff
#print axioms BB61.eight_lt_iff_of_mem_Ioo

-- `BB61/WindowDiam.lean` is M2 Proposition 7: the width of the window K, and the vacuity of the
-- criterion X7 (`plans/plan-1061.html` section 7).  Three layers.  (1) Abstract: for any
-- absolutely summable c : N -> R the subset-sum set K = {sum c_m delta_m} has diam K = sum |c_m|
-- EXACTLY (both endpoints are hit by greedy words), and diam K = -(sum c_m) + 2 sum_{c_m>0} c_m,
-- so the bound diam K >= |sum c_m| is attained iff no c_m is positive.  (2) Conjugates: for a
-- multiset s inside the unit disc, sum_m c_m = -card s with c_m = sum_j (alpha_j-1) alpha_j^m,
-- whence card s <= diam K <= Delta.  (3) X7: since g = (alpha-2)/alpha < 1 always, 2Delta >= 2
-- diam K >= 2(d-1) >= 2 > 1 > g, so `2Delta < g` is EMPTY.  Zero margin: the family X^2 - aX + 1
-- has Delta = diam K = d-1 = 1 (all three equal, since beta = 1/alpha in (0,1) makes every c_m
-- negative), and 2Delta/g -> 2 along it, so the constant 2 is the exact infimum.  All std3, no
-- citation.
#print axioms BB61.windowOf
#print axioms BB61.posSum
#print axioms BB61.negSum
#print axioms BB61.posWord
#print axioms BB61.negWord
#print axioms BB61.summable_mul_dR
#print axioms BB61.summable_max
#print axioms BB61.summable_min
#print axioms BB61.posSum_add_negSum
#print axioms BB61.posSum_sub_negSum
#print axioms BB61.wOf_le_posSum
#print axioms BB61.negSum_le_wOf
#print axioms BB61.windowOf_subset_Icc
#print axioms BB61.posSum_mem_windowOf
#print axioms BB61.negSum_mem_windowOf
#print axioms BB61.isBounded_windowOf
#print axioms BB61.diam_windowOf
#print axioms BB61.diam_windowOf_eq_two_mul_posSum
#print axioms BB61.abs_tsum_le_diam_windowOf
#print axioms BB61.posSum_nonneg
#print axioms BB61.posSum_eq_zero_iff
#print axioms BB61.diam_windowOf_eq_neg_tsum_iff
#print axioms BB61.conjCoefC
#print axioms BB61.conjCoef
#print axioms BB61.conjDelta
#print axioms BB61.conjNormCoef
#print axioms BB61.hasSum_conjCoefC
#print axioms BB61.hasSum_conjNormCoef
#print axioms BB61.abs_conjCoef_le
#print axioms BB61.summable_abs_conjCoef
#print axioms BB61.tsum_conjCoef
#print axioms BB61.tsum_abs_conjCoef_le_conjDelta
#print axioms BB61.diam_windowOf_conjCoef_le
#print axioms BB61.card_le_diam_windowOf_conjCoef
#print axioms BB61.card_le_conjDelta
#print axioms BB61.cantorSet_inter_gapIoo_eq_empty
#print axioms BB61.X7Criterion
#print axioms BB61.gap_lt_one
#print axioms BB61.gap_lt_two_mul_diam_windowOf
#print axioms BB61.not_x7Criterion
#print axioms BB61.not_x7Criterion_of_natDegree
#print axioms BB61.two_div_gap_le_ratio
#print axioms BB61.QuadSetup.quadConj
#print axioms BB61.QuadSetup.card_quadConj
#print axioms BB61.QuadSetup.quadConj_ne_zero
#print axioms BB61.QuadSetup.norm_lt_one_of_mem_quadConj
#print axioms BB61.QuadSetup.conjCoef_quadConj
#print axioms BB61.QuadSetup.conjDelta_quadConj
#print axioms BB61.QuadSetup.windowSet_eq_windowOf
#print axioms BB61.QuadSetup.diam_windowSet
#print axioms BB61.QuadSetup.diam_windowSet_eq_conjDelta
#print axioms BB61.QuadSetup.wMax_add_wMin
#print axioms BB61.QuadSetup.diam_windowSet_eq_one_add_two_mul_wMax
#print axioms BB61.QuadSetup.one_le_diam_windowSet
#print axioms BB61.QuadSetup.diam_windowSet_eq_one_iff
#print axioms BB61.QuadSetup.cCoef_nonpos_of_beta_nonneg
#print axioms BB61.QuadSetup.diam_windowSet_eq_one_of_beta_nonneg
#print axioms BB61.QuadSetup.beta_pos_of_b_eq_neg_one
#print axioms BB61.QuadSetup.diam_windowSet_eq_one_of_b_eq_neg_one
#print axioms BB61.QuadSetup.not_x7Criterion_quad
#print axioms BB61.sq_sqrt_sq_sub_four
#print axioms BB61.unitQuad
#print axioms BB61.unitQuad_b
#print axioms BB61.unitQuad_alpha
#print axioms BB61.two_lt_unitQuad_alpha
#print axioms BB61.unitQuad_four_alpha
#print axioms BB61.diam_windowSet_unitQuad
#print axioms BB61.conjDelta_unitQuad
#print axioms BB61.unitQuadSeq
#print axioms BB61.unitQuadSeq_alpha
#print axioms BB61.conjDelta_unitQuadSeq
#print axioms BB61.tendsto_alpha_unitQuadSeq
#print axioms BB61.tendsto_gap_atTop
#print axioms BB61.tendsto_ratio_unitQuadSeq

-- `BB61/BlockRecoding.lean` is M2 Proposition 8: block recoding is exactly neutral, so gate
-- G-R's progression freedom (proving 10.61 along n = 0 mod p, i.e. in base alpha^p) is worthless
-- to every criterion of Route A's kind.  Three layers.  (1) Abstract: a ratio criterion sees only
-- (log #alphabet, log base, log 1/contraction), block recoding multiplies all three by p, and the
-- two ratios L = log base/log #alphabet and R = log(1/contraction)/log #alphabet are invariant --
-- so `apply_ratios_block` is ONE no-go, not four cancellations, A = 1/L + 1/R and dim = 1/L and
-- the entropy deficit and Mendes-France all being functions of (L,R).  The converse
-- `ratios_eq_iff` says the fibres of `ratios` ARE the rescaling orbits, so factoring through the
-- ratios is what neutrality means.  (2) The recoded contraction is earned: `power` builds the
-- actual power polynomial X^2 - t_p X + (-b)^p from the integer trace ladder t_n = alpha^n +
-- beta^n, `power_beta` proves its second root is beta^p, and `blockData` is defined from THAT
-- polynomial's roots -- `blockData_eq_block` is the theorem that it lands on p times the original
-- data (the note's check P8, instantiated at its three cases (2+sqrt3)^2, (1+sqrt2)^2,
-- (1+sqrt2)^3).  (3) The trap: `routeAExponent_power` shows alpha -> alpha^p WITHOUT enlarging
-- the alphabet divides A by p, hence fires everywhere (`exists_power_routeAExponent_lt_one`),
-- including at 1+sqrt2 where Route A provably does not -- because that is a thinner Cantor set,
-- not a recoding.  All std3, no citation; [BM86] Th. XIII is what makes the freedom available and
-- is NOT consumed, the statement proved being that the freedom is neutral.
#print axioms BB61.RatioData
#print axioms BB61.RatioData.scale
#print axioms BB61.RatioData.block
#print axioms BB61.RatioData.L
#print axioms BB61.RatioData.R
#print axioms BB61.RatioData.ratios
#print axioms BB61.RatioData.expo
#print axioms BB61.RatioData.dim
#print axioms BB61.RatioData.EntropyDeficit
#print axioms BB61.RatioData.MFCriterion
#print axioms BB61.RatioData.RouteACriterion
#print axioms BB61.RatioData.expo_eq_inv_add_inv
#print axioms BB61.RatioData.dim_eq_inv_L
#print axioms BB61.RatioData.scale_one
#print axioms BB61.RatioData.scale_scale
#print axioms BB61.RatioData.block_one
#print axioms BB61.RatioData.L_scale
#print axioms BB61.RatioData.R_scale
#print axioms BB61.RatioData.ratios_scale
#print axioms BB61.RatioData.expo_scale
#print axioms BB61.RatioData.dim_scale
#print axioms BB61.RatioData.entropyDeficit_scale
#print axioms BB61.RatioData.mfCriterion_scale
#print axioms BB61.RatioData.routeACriterion_scale
#print axioms BB61.RatioData.cast_ne_zero
#print axioms BB61.RatioData.L_block
#print axioms BB61.RatioData.R_block
#print axioms BB61.RatioData.ratios_block
#print axioms BB61.RatioData.expo_block
#print axioms BB61.RatioData.dim_block
#print axioms BB61.RatioData.entropyDeficit_block
#print axioms BB61.RatioData.mfCriterion_block
#print axioms BB61.RatioData.routeACriterion_block
#print axioms BB61.RatioData.apply_ratios_block
#print axioms BB61.RatioData.ratios_eq_iff
#print axioms BB61.RatioData.eq_of_ratios_eq
#print axioms BB61.QuadSetup.sysData
#print axioms BB61.QuadSetup.sysData_L
#print axioms BB61.QuadSetup.sysData_R
#print axioms BB61.QuadSetup.expo_sysData
#print axioms BB61.QuadSetup.dim_sysData
#print axioms BB61.QuadSetup.entropyDeficit_sysData_iff
#print axioms BB61.QuadSetup.mfCriterion_sysData_iff
#print axioms BB61.QuadSetup.traceSeq
#print axioms BB61.QuadSetup.traceSeq_zero
#print axioms BB61.QuadSetup.traceSeq_one
#print axioms BB61.QuadSetup.traceSeq_add_two
#print axioms BB61.QuadSetup.traceSeq_cast
#print axioms BB61.QuadSetup.traceSeq_two
#print axioms BB61.QuadSetup.traceSeq_three
#print axioms BB61.QuadSetup.power
#print axioms BB61.QuadSetup.power_a
#print axioms BB61.QuadSetup.power_b
#print axioms BB61.QuadSetup.power_alpha
#print axioms BB61.QuadSetup.power_beta
#print axioms BB61.QuadSetup.blockData
#print axioms BB61.QuadSetup.blockData_eq_block
#print axioms BB61.QuadSetup.L_blockData
#print axioms BB61.QuadSetup.R_blockData
#print axioms BB61.QuadSetup.ratios_blockData
#print axioms BB61.QuadSetup.blockRecoding_expo
#print axioms BB61.QuadSetup.expo_blockData
#print axioms BB61.QuadSetup.dim_blockData
#print axioms BB61.QuadSetup.entropyDeficit_blockData_iff
#print axioms BB61.QuadSetup.mfCriterion_blockData_iff
#print axioms BB61.QuadSetup.routeACriterion_blockData_iff
#print axioms BB61.QuadSetup.routeACriterion_blockData_iff_four_lt
#print axioms BB61.QuadSetup.apply_ratios_blockData
#print axioms BB61.QuadSetup.upperBoxDim_cantorSet_blockData
#print axioms BB61.QuadSetup.dimH_cantorSet_blockData
#print axioms BB61.QuadSetup.routeAExponent_power
#print axioms BB61.QuadSetup.exists_power_routeAExponent_lt_one
#print axioms BB61.twoAddSqrt3_power_two_a
#print axioms BB61.twoAddSqrt3_power_two_b
#print axioms BB61.twoAddSqrt3_power_two_alpha
#print axioms BB61.silver_power_two_a
#print axioms BB61.silver_power_two_b
#print axioms BB61.silver_power_two_alpha
#print axioms BB61.silver_power_three_a
#print axioms BB61.silver_power_three_b
#print axioms BB61.silver_power_three_alpha
#print axioms BB61.sqrt_two_lt_two
#print axioms BB61.silver_abs_b
#print axioms BB61.silver_beta_ne_zero
#print axioms BB61.silver_not_routeAExponent_lt_one
#print axioms BB61.exists_silver_power_routeAExponent_lt_one
#print axioms BB61.silver_not_routeACriterion_blockData

-- M2 Proposition 9 (`BB61/Raster.lean`, `BB61/GapSqrtThree.lean`): the X8 raster criterion,
-- and the certified gap at `2 + √3`.
--
-- Two independent things are checked here.
--
-- (a) The raster procedure of M0 §6 is modelled exactly -- bins are the fibres of
--     `binIdx G x = ⌊x·G⌋` -- and both directions are proved: `runSet_inter_occSet_eq_empty`
--     is soundness (a reported run is a true gap), `exists_zeroRun` is completeness at a given
--     resolution, and `prop9` is the note's Proposition 9, with the resolution
--     `G ≥ 2^{W+3}/(1-3T)` named in advance.  `exists_X8Cert_of_cert` is `Route A ⊆ X8`.
--
-- (b) `GapThree` is M0 §6.2's certificate at `α = 2 + √3`, at depth `(2,2)` and exact in
--     `ℤ[√3]`.  `problem_10_61_two_add_sqrt3_axiom_free` proves **10.61 at `2 + √3`** with NO
--     citation: it must report the standard three and nothing else, and in particular NOT
--     `LY.entropyRate_floor`, which the pressure-lane proof of the same statement
--     (`BB61.problem_10_61_two_add_sqrt3`, below) does report.  The two proofs are independent.
--     `routeA_subset_X8_strict` is the converse half of Proposition 9: `Route A ⊊ X8`.
#print axioms BB61.Raster.binIdx
#print axioms BB61.Raster.bin
#print axioms BB61.Raster.mem_bin_iff
#print axioms BB61.Raster.mem_bin_binIdx
#print axioms BB61.Raster.Occupied
#print axioms BB61.Raster.occSet
#print axioms BB61.Raster.subset_occSet
#print axioms BB61.Raster.occSet_mono
#print axioms BB61.Raster.occSet_dist
#print axioms BB61.Raster.ZeroRun
#print axioms BB61.Raster.runSet
#print axioms BB61.Raster.runSet_inter_occSet_eq_empty
#print axioms BB61.Raster.exists_zeroRun
#print axioms BB61.Raster.inter_occSet_eq_empty_of_shrink
#print axioms BB61.Raster.exists_certified_gap
#print axioms BB61.Raster.gap_pos_of_resolution
#print axioms BB61.Raster.prop9
#print axioms BB61.QuadSetup.covSet
#print axioms BB61.QuadSetup.orbitFract_mem_covSet
#print axioms BB61.QuadSetup.orbitFractSet
#print axioms BB61.QuadSetup.orbitFractSet_subset_covSet
#print axioms BB61.QuadSetup.X8Cert
#print axioms BB61.QuadSetup.avoided_interval_of_X8Cert
#print axioms BB61.QuadSetup.not_equidistributed_of_X8Cert
#print axioms BB61.QuadSetup.exists_gap_in_covSet
#print axioms BB61.QuadSetup.exists_X8Cert_of_cert
#print axioms BB61.tPart_two_step
#print axioms BB61.dR_zero_or_one
#print axioms BB61.QuadSetup.sPart_two_step
#print axioms BB61.QuadSetup.neg_sPart_mem_Icc
#print axioms BB61.GapThree.wOne
#print axioms BB61.GapThree.wTwo
#print axioms BB61.GapThree.epsTwo
#print axioms BB61.GapThree.lend
#print axioms BB61.GapThree.gapLo
#print axioms BB61.GapThree.gapHi
#print axioms BB61.GapThree.covThree
#print axioms BB61.GapThree.sq_sqrt3
#print axioms BB61.GapThree.tPart_expand
#print axioms BB61.GapThree.neg_sPart_expand
#print axioms BB61.GapThree.fract_mem_covThree
#print axioms BB61.GapThree.covThree_inter_gapIoo_eq_empty
#print axioms BB61.GapThree.gap_two_add_sqrt3
#print axioms BB61.GapThree.two_add_sqrt3_not_denseModuloOne_of_gap
#print axioms BB61.GapThree.two_add_sqrt3_not_equidistributed_of_gap
#print axioms BB61.GapThree.confCircle_ne_univ_two_add_sqrt3
#print axioms BB61.GapThree.problem_10_61_two_add_sqrt3_axiom_free
#print axioms BB61.GapThree.exists_zeroRun_two_add_sqrt3
#print axioms BB61.GapThree.not_routeAExponent_lt_one_twoAddSqrt3
#print axioms BB61.GapThree.routeA_subset_X8_strict

-- M3 Corollary 13 (`BB61/EntropyBudget.lean`): the entropy floor and the Route A exponent are
-- reciprocal up to `log 2`, so `A(alpha) < 1` iff `log 2 < h_min(alpha)`.  Only the DEFINITION
-- `LY.hMin` is used, never the cited axiom `LY.entropyRate_floor`, so every one of these must
-- report the standard three -- that is the point of listing them here rather than below.
#print axioms BB61.QuadSetup.log_alpha_pos
#print axioms BB61.QuadSetup.log_abs_beta_inv_pos
#print axioms BB61.QuadSetup.routeAExponent_eq_log_two_mul
#print axioms BB61.QuadSetup.hMin_eq_inv_add_inv
#print axioms BB61.QuadSetup.hMin_pos
#print axioms BB61.QuadSetup.routeAExponent_mul_hMin
#print axioms BB61.QuadSetup.routeAExponent_eq_log_two_div_hMin
#print axioms BB61.QuadSetup.routeAExponent_lt_one_iff_log_two_lt_hMin
#print axioms BB61.QuadSetup.zero_lt_entropyBudget_iff
#print axioms BB61.QuadSetup.log_two_lt_hMin_iff_four_lt_of_unit
#print axioms BB61.QuadSetup.routeAExponent_lt_one_iff_four_lt_of_floor

-- M3 Theorem 4 (`BB61/LadderReduction.lean`): the trace-ladder reduction.  The whole file is
-- an identity between real numbers plus one Lipschitz estimate, so all of it must report the
-- standard three; `not_equidistributed_of_ladder` in particular is Problem 10.61 from the
-- future marginal alone, with no cited input.
#print axioms BB61.dR_futures_add
#print axioms BB61.dR_futures_sub
#print axioms BB61.fourier_intMul_coe
#print axioms BB61.norm_fourier_int_add_sub
#print axioms BB61.QuadSetup.ladderHead
#print axioms BB61.QuadSetup.ladderErr
#print axioms BB61.QuadSetup.futureWeight_eq
#print axioms BB61.QuadSetup.ladderHead_cast
#print axioms BB61.QuadSetup.traceSeq_mul_piVal_futures
#print axioms BB61.QuadSetup.wConst
#print axioms BB61.QuadSetup.wConst_nonneg
#print axioms BB61.QuadSetup.abs_cCoef
#print axioms BB61.QuadSetup.abs_window_tail_le
#print axioms BB61.QuadSetup.abs_ladderErr_le
#print axioms BB61.QuadSetup.phiCoeff
#print axioms BB61.QuadSetup.futureCoeff
#print axioms BB61.QuadSetup.integral_comp_shiftZ_iterate
#print axioms BB61.QuadSetup.norm_fourier_traceSeq_sub
#print axioms BB61.QuadSetup.thm4
#print axioms BB61.QuadSetup.tendsto_futureCoeff
#print axioms BB61.QuadSetup.exists_tendsto_futureCoeff
#print axioms BB61.QuadSetup.phiCoeff_eq_zero
#print axioms BB61.QuadSetup.tendsto_futureCoeff_zero
#print axioms BB61.QuadSetup.not_equidistributed_of_ladder

-- M3 Corollary 6 (`BB61/LadderScope.lean`): which ladders may enter a proof.  The positive
-- half rides on Theorem 4, the negative half is a parity argument on the integer ladder, and
-- the bridge to the codifferent is M1 Proposition 15 -- all of it elementary, so every line
-- must report the standard three.  `silver_not_intOrbitLadder` is the one that spends M1's
-- factor 452: the half-ladder is legal as a character and inadmissible as a proof.
#print axioms BB61.QuadSetup.trForm
#print axioms BB61.QuadSetup.trForm_cast
#print axioms BB61.QuadSetup.two_dvd_trForm_iff
#print axioms BB61.QuadSetup.half_trForm_eq
#print axioms BB61.QuadSetup.traceSeqZ
#print axioms BB61.QuadSetup.traceSeqZ_natCast
#print axioms BB61.QuadSetup.beta_ne_zero_of_unit
#print axioms BB61.QuadSetup.traceSeqZ_cast
#print axioms BB61.QuadSetup.two_dvd_traceSeq
#print axioms BB61.QuadSetup.two_dvd_traceSeqZ
#print axioms BB61.QuadSetup.lad_smul
#print axioms BB61.QuadSetup.halfLad
#print axioms BB61.QuadSetup.halfLad_zero
#print axioms BB61.QuadSetup.two_mul_halfLad
#print axioms BB61.QuadSetup.halfLad_isTraceLadder
#print axioms BB61.QuadSetup.IntOrbitLadder
#print axioms BB61.QuadSetup.tendsto_futureCoeff_orbit
#print axioms BB61.QuadSetup.two_dvd_of_intOrbitLadder
#print axioms BB61.QuadSetup.not_intOrbitLadder_halfLad
#print axioms BB61.QuadSetup.cor6
#print axioms BB61.QuadSetup.no_half_character
#print axioms BB61.silver_halfLad_values
#print axioms BB61.silver_not_intOrbitLadder
#print axioms BB61.twoAddSqrt3_halfLad_values
#print axioms BB61.twoAddSqrt3_not_intOrbitLadder

-- M3 Theorems 7 and 8 (`BB61/KernelCriterion.lean`): the kernel criterion and the collapse of
-- Route B.  The note imports two theorems here -- Bochner for `Q >= 0` and Fejer-Riesz for the
-- realisation -- and neither is used: the Gram form makes positivity an inspection and one
-- explicit sum of squares does the realisation.  So the whole file, including the three-way
-- equivalence `exists_kernel_iff` and the two pointwise no-gos, must report the standard three.
#print axioms BB61.fourier_sub_apply
#print axioms BB61.matKernel
#print axioms BB61.matKernel_apply
#print axioms BB61.matTrace
#print axioms BB61.gram
#print axioms BB61.gram_posSemidef
#print axioms BB61.gramTrace
#print axioms BB61.matKernel_gram
#print axioms BB61.matKernel_gram_nonneg
#print axioms BB61.matTrace_gram
#print axioms BB61.coe_sub_eq_zero_iff
#print axioms BB61.integral_fourier_circle_zero
#print axioms BB61.integral_fourier_circle_ne
#print axioms BB61.integral_matKernel
#print axioms BB61.QuadSetup.integral_matKernel_comp
#print axioms BB61.QuadSetup.integral_matKernel_comp_eq_trace
#print axioms BB61.QuadSetup.kernelCertificate
#print axioms BB61.QuadSetup.not_equidistributed_of_kernel
#print axioms BB61.QuadSetup.no_invariant_of_kernel
#print axioms BB61.QuadSetup.no_killer_of_kernel
#print axioms BB61.QuadSetup.integrable_fourier_fMap
#print axioms BB61.QuadSetup.phiCoeff_re
#print axioms BB61.QuadSetup.phiCoeff_im
#print axioms BB61.QuadSetup.integral_trigPoly_comp
#print axioms BB61.QuadSetup.no_killer_of_trigCertificate
#print axioms BB61.QuadSetup.exists_trigCertificate_of_no_killer
#print axioms BB61.normSq_fourier
#print axioms BB61.QuadSetup.exists_kernel_of_trigCertificate
#print axioms BB61.QuadSetup.exists_kernel_iff
#print axioms BB61.QuadSetup.integral_matKernel_comp_le
#print axioms BB61.QuadSetup.exists_gap_of_pointwise
#print axioms BB61.QuadSetup.confCircle_ne_univ_of_kernel
#print axioms BB61.silver_not_pointwise_kernel
#print axioms BB61.goldenSq_not_pointwise_kernel

-- M3 Proposition 1 (`BB61/Tube.lean`, on `ForMathlib/Topology/Algebra/DenseCover.lean`): the
-- tube criterion of Route B move 3 is vacuous.  The note proves the density of the image of
-- the line by Pontryagin duality, which Mathlib does not have; here the covering question is
-- algebraic (`tube_add_eq_univ_iff`) and the only analytic input is that `0` is not isolated
-- in `Z + betaZ`, from `beta^n -> 0`.  Nothing is cited, so all of this must report the
-- standard three -- including the `delta = 0` half, which consumes M1 Lemma 3 through
-- `BB61/BoxDim.lean` (itself std3).
#print axioms QuotientAddGroup.image_mk_eq_univ_iff
#print axioms add_dense_eq_univ
#print axioms BB61.tube
#print axioms BB61.mem_tube
#print axioms BB61.shadow
#print axioms BB61.mem_shadow
#print axioms BB61.tube_add_eq_univ_iff
#print axioms BB61.image_mk_tube_eq_univ_iff
#print axioms BB61.image_mk_tube_eq_univ
#print axioms BB61.measure_image_mk_tube
#print axioms BB61.QuadSetup.emb
#print axioms BB61.QuadSetup.lattice
#print axioms BB61.QuadSetup.mem_lattice
#print axioms BB61.QuadSetup.mem_shadow_lattice
#print axioms BB61.QuadSetup.alpha_mul_beta
#print axioms BB61.QuadSetup.beta_ne_zero_of_b
#print axioms BB61.QuadSetup.beta_pow_mem_shadow
#print axioms BB61.QuadSetup.dense_shadow
#print axioms BB61.QuadSetup.prop1
#print axioms BB61.QuadSetup.measure_prop1
#print axioms BB61.QuadSetup.prop1_thickening
#print axioms BB61.QuadSetup.no_tube_criterion
#print axioms BB61.QuadSetup.covol
#print axioms BB61.QuadSetup.covol_pos
#print axioms BB61.QuadSetup.covol_sq
#print axioms BB61.QuadSetup.exists_tube_small_shadow
#print axioms BB61.QuadSetup.countable_shadow
#print axioms BB61.QuadSetup.volume_add_shadow
#print axioms BB61.QuadSetup.image_mk_tube_ne_univ_of_volume_zero
#print axioms BB61.QuadSetup.volume_windowSet_eq_zero
#print axioms BB61.QuadSetup.tube_window_dichotomy
#print axioms BB61.QuadSetup.dense_image_mk_line
#print axioms BB61.silver_abs_beta_lt_half
#print axioms BB61.silver_tube_window_dichotomy
#print axioms BB61.goldenSq_abs_beta_lt_half
#print axioms BB61.goldenSq_tube_window_dichotomy

-- The one cited axiom of the root.  `CITED/LedrappierYoung.lean` carries M3 Theorem 11 (the
-- Ledrappier-Young entropy floor) and `BB61/Floor.lean` is the only file that consumes it:
-- these three declarations are expected to report `LY.entropyRate_floor` on top of the standard
-- three, and NOTHING above reports it.
#print axioms LY.hMin_eq_of_unit
#print axioms LY.entropyRate_floor_unit
#print axioms BB61.floor_of_quadratic_unit
#print axioms BB61.two_add_sqrt3_not_equidistributed_cited
#print axioms BB61.problem_10_61_two_add_sqrt3

-- R2b: the max-plus (entropy-free) reading of the SAME certificate `Pressure.lean` discharges
-- by `decide`.  `max <= sum` for naturals, so no new numerical data enters; these must report
-- the standard three and nothing else.
#print axioms BB61.CycleMean.cert_of_sum
#print axioms BB61.CycleMean.walk_le
#print axioms BB61.CycleMean.cycle_le
#print axioms BB61.CycleMean.cycle_le_real
#print axioms BB61.TwoAddSqrt3.certMax
#print axioms BB61.TwoAddSqrt3.cycle_prod_le

-- M5 Theorem 2 (`BB61/ProductFormula.lean`): the Bernoulli Fourier coefficients of `F_*mu_p`.
-- The product formula itself, its Fourier reading, the bridge that makes `WeylProduct.lean`'s
-- real product the modulus of a Fourier coefficient, and the non-vanishing at mode 1 that says
-- the fair coin is not a counterexample measure.  All of these must report the standard three:
-- no cited axiom enters M5, and the numerics of the note are nowhere consumed.
#print axioms BB61.integral_bernZ_finset_prod
#print axioms BB61.integral_bernZ_cexp1_tsum
#print axioms BB61.QuadSetup.tsum_freq_mul_bitR
#print axioms BB61.QuadSetup.integral_cexp1_fRaw
#print axioms BB61.QuadSetup.integral_fourier_map_fMap
#print axioms BB61.QuadSetup.norm_weylC_half
#print axioms BB61.QuadSetup.weylC_half_one_ne_zero
#print axioms BB61.QuadSetup.map_fMap_bernZ_half_ne_volume
#print axioms BB61.QuadSetup.map_fMap_bernZ_half_ne_volume_twoAddSqrt3

-- M5 Theorem 1 (`BB61/LimitLaw.lean`): the limit law at a generic word, and the corollaries it
-- carries.  Theorem 1 itself, its u.d. criterion and its Fourier form; Corollary 2 (Birkhoff);
-- the Bernoulli natural extension and the ergodicity of the one-sided Bernoulli shift
-- (Kolmogorov 0-1); Corollary 4 with the explicit constant `G_p(h)` and its `p = 1/2` case;
-- Corollary 5 = [MF67] Th. II.2.2.  All of these must report the standard three: M5 consumes
-- no cited axiom, and in particular the vendored pointwise Birkhoff theorem is proved, not
-- assumed.
#print axioms BB61.tendsto_weylSum_of_tendsto_emp
#print axioms BB61.QuadSetup.tendsto_emp_of_generic
#print axioms BB61.QuadSetup.equidistributed_iff_map_eq_haarT
#print axioms BB61.QuadSetup.tendsto_weylSum_of_generic
#print axioms BB61.ae_isGenericFor_of_ergodic
#print axioms BB61.isNaturalExtension_bern
#print axioms BB61.ergodic_shiftN_bernN
#print axioms BB61.exists_isGenericFor_bern
#print axioms BB61.QuadSetup.tendsto_weylSum_bern
#print axioms BB61.QuadSetup.not_equidistributed_of_bern_half_generic
#print axioms BB61.QuadSetup.not_equidistributed_of_bern_half_generic_twoAddSqrt3
#print axioms BB61.QuadSetup.ae_not_equidistributed_bern_half
#print axioms BB61.QuadSetup.measure_equidistributed_bern_half_eq_zero
#print axioms BB61.QuadSetup.ae_not_equidistributed_bern_half_twoAddSqrt3

-- M5 Corollary 6 (`BB61/Multiplier.lean`): the multiplier version.  The `ℤ[α]` toolbox and the
-- one arithmetic lemma that replaces the whole of Theorem 3 at a unit; the twisted trace and
-- orbit identity; Theorem 1 and Theorem 2 for the twisted coding `F^λ`; the non-vanishing of
-- `G^λ_p(h)`; and Corollary 6 itself with its a.e. and null-set forms and the `2+√3` instance.
#print axioms BB61.QuadSetup.isIntComb_inv_alpha
#print axioms BB61.QuadSetup.cos_pi_ne_zero_of_isIntComb
#print axioms BB61.QuadSetup.phi_ne_zero_of_isIntComb
#print axioms BB61.QuadSetup.lamR_aPart_add_lamC_sPart
#print axioms BB61.QuadSetup.fMapL_iterate_padZ
#print axioms BB61.QuadSetup.tendsto_emp_of_generic_mul
#print axioms BB61.QuadSetup.equidistributed_iff_map_eq_haarT_mul
#print axioms BB61.QuadSetup.integral_cexp1_fRawL
#print axioms BB61.QuadSetup.integral_fourier_map_fMapL
#print axioms BB61.QuadSetup.weylCL_ne_zero
#print axioms BB61.QuadSetup.map_fMapL_bernZ_ne_volume
#print axioms BB61.QuadSetup.tendsto_weylSum_bern_mul
#print axioms BB61.QuadSetup.not_equidistributed_of_bern_generic_mul
#print axioms BB61.QuadSetup.ae_not_equidistributed_bern_mul
#print axioms BB61.QuadSetup.measure_equidistributed_bern_mul_eq_zero
#print axioms BB61.not_equidistributed_of_bern_half_generic_mul_twoAddSqrt3
#print axioms BB61.ae_not_equidistributed_bern_half_mul_twoAddSqrt3

-- M5 Theorem 3 at any degree (`BB61/NonVanishing.lean`, with `ForMathlib/NumberTheory/`'s
-- `RationalAlgebraicInteger.lean`, `ConjugatePowerSum.lean` and `PisotFractionalParts.lean`).
-- The section's Lean now matches its stated generality: the past half needs only
-- `IsIntegral ℤ α` -- not `α > 2`, not `Irrational α`, not `h ≠ 0` -- the future half at a unit
-- carries a multiplier for free, and the degree-two file and the cubic `X³ - 2X² - 1` are both
-- instances.  Also the general-degree Pisot decay behind Theorem 8.  Everything here is
-- standard-three: the trace identity is proved, not assumed.
#print axioms exists_int_of_isIntegral_ratCast
#print axioms IsIntegral.ne_intCast_add_half
#print axioms IsIntegral.cos_pi_ne_zero
#print axioms conj_shiftedPowerSum_isInt
#print axioms conj_erase_sum_add
#print axioms exists_int_sub_le_of_conj
#print axioms IsPisot.exists_int_pow_close
#print axioms IsPisot.exists_int_sub_one_mul_pow_close
#print axioms BB61.phi_ne_zero_of_isIntegral
#print axioms BB61.cos_ne_zero_of_isIntegral_ladder
#print axioms BB61.exists_int_pastLadder_add
#print axioms BB61.phi_pastLadder_ne_zero
#print axioms BB61.cos_future_ne_zero_of_two_lt
#print axioms BB61.cos_future_ne_zero_of_isIntegral_inv
#print axioms BB61.pow_le_of_future_half
#print axioms BB61.exists_int_close_of_isPisot
#print axioms BB61.QuadSetup.isIntegral_alpha
#print axioms BB61.QuadSetup.isIntegral_of_isIntComb
#print axioms BB61.QuadSetup.isIntegral_inv_alpha
#print axioms BB61.QuadSetup.cos_past_ne_zero_of_isIntegral
#print axioms BB61.isIntegral_alphaCubic
#print axioms BB61.isIntegral_inv_alphaCubic
#print axioms BB61.cos_past_ne_zero_alphaCubic
#print axioms BB61.cos_future_ne_zero_alphaCubic
#print axioms BB61.phi_ne_zero_alphaCubic

-- M5 Theorem 7 (`BB61/Folding.lean`): what folding at a quadratic unit of norm `+1` buys.
-- The ladder identity was already `Bernoulli.past_eq_future` and the `p = 1/2` modulus
-- conclusion `WeylProduct.weylProd_eq_sq`; these are the three the note states and nothing had:
-- the window is minus the Cantor set (so `F̃` is a plain SUM and `X(α) = (C+C) mod 1`), the
-- Fourier coefficient `G_p(h)` itself is a square at EVERY `p`, and the norm `-1` branch.
#print axioms BB61.QuadSetup.cCoef_eq_neg_future
#print axioms BB61.QuadSetup.wVal_eq_neg_piVal
#print axioms BB61.QuadSetup.windowSet_eq_neg
#print axioms BB61.QuadSetup.fRaw_eq_add
#print axioms BB61.QuadSetup.confSet_eq_add
#print axioms BB61.QuadSetup.confCircle_eq_image_add
#print axioms BB61.QuadSetup.pastProdC_eq_futProdC
#print axioms BB61.QuadSetup.weylC_eq_sq
#print axioms BB61.QuadSetup.beta_eq_neg_inv
#print axioms BB61.QuadSetup.cCoef_eq_of_norm_neg_one

-- M5 Theorem 8 and Corollary 10 (`BB61/TailEvent.lean`, on the new ForMathlib
-- `weylCriterion_of_tendsto_sub_int`).  `U(α)` is a tail event, and a counterexample to 10.61
-- could not be isolated: if one point of `C(α)` had a u.d. orbit, the set of such points would
-- be dense in `C(α)`.  Neither `α > 2` nor irrationality is used; the analysis is one lemma
-- (Weyl sums do not see a perturbation that vanishes mod one) and the rest is the Pisot decay.
#print axioms weylCriterion_of_tendsto_sub_int
#print axioms Bugeaud.theorem_1_2_weyl
#print axioms BB61.QuadSetup.piVal_sub_of_eq_off
#print axioms BB61.QuadSetup.abs_orbit_sub_int_le
#print axioms BB61.QuadSetup.mem_udWords_of_eq_off
#print axioms BB61.QuadSetup.mem_udWords_iff_of_eq_off
#print axioms BB61.QuadSetup.mem_udWords_iff_of_agree_from
#print axioms BB61.QuadSetup.abs_piVal_graft_sub_le
#print axioms BB61.QuadSetup.cantorSet_subset_closure_udPoints

-- M5 Corollary 4's discrepancy floor (`BB61/DiscrepancyFloor.lean`, on the new ForMathlib
-- `BoundedVariation/{Monotone,Trigonometric}`).  Everything up to and including the total
-- variation `V(cos 2πhx) = V(sin 2πhx) = 4h` is PROVED — Mathlib knows a monotone function has
-- bounded variation but not what it is, and has no discrepancy at all.  Only the step from the
-- variation to the quadrature error is cited: `Koksma.abs_average_sub_integral_le`,
-- [KN74] Ch. 2 Thm 5.1, the single axiom of `CITED/KoksmaInequality.lean`, which is therefore
-- the only non-std3 entry in the block below.
#print axioms eVariationOn.eq_ofReal_sub_of_monotoneOn
#print axioms eVariationOn.eq_ofReal_sub_of_antitoneOn
#print axioms eVariationOn.eq_ofReal_abs_sub
#print axioms eVariationOn_cos_piece
#print axioms eVariationOn_sin_piece
#print axioms eVariationOn_cos_two_pi_mul
#print axioms eVariationOn_sin_two_pi_mul
#print axioms boundedVariationOn_cos_two_pi_mul
#print axioms boundedVariationOn_sin_two_pi_mul
#print axioms toReal_eVariationOn_cos_two_pi_mul
#print axioms toReal_eVariationOn_sin_two_pi_mul
#print axioms BB61.periodic_cos_char
#print axioms BB61.periodic_sin_char
#print axioms BB61.integral_cos_char
#print axioms BB61.integral_sin_char
#print axioms BB61.norm_le_sqrt_two_mul
#print axioms BB61.re_average_char
#print axioms BB61.im_average_char
#print axioms BB61.abs_average_cos_le
#print axioms BB61.abs_average_sin_le
#print axioms BB61.norm_average_char_le
#print axioms BB61.QuadSetup.eventually_le_starDiscrepancy
#print axioms BB61.QuadSetup.le_liminf_starDiscrepancy
#print axioms BB61.QuadSetup.starDiscrepancy_floor_pos

-- Theorem B(iii), the exact price (`BB61/Price.lean`, `BB61/PriceCompleteness.lean`, on the new
-- ForMathlib `Dynamics/EntropySemicontinuity`).  The duality `⨅_a sup_μ (h(μ) + ∫ψ_a dμ) = E_H(α)`
-- is PROVED — Lagrange duality by geometric Hahn–Banach, in place of Sion's minimax theorem, on
-- concavity and upper semicontinuity of the entropy in the measure — and so is the easy half of
-- the paper's own statement, `E_H(α) ≤ ⨅_a P(ψ_a)`.  Only the passage from the supremum over
-- measures to the topological pressure is cited: `Walters.partitionPressure_le_measurePressure`,
-- [Wal82] Thm 9.10, the single axiom of `CITED/WaltersVariationalPrinciple.lean`.  It, and the
-- entropy floor in (iv) ⇒ (i), are the only non-std3 entries in the block below.
#print axioms MeasureTheory.partitionEntropy_smul_add_smul_le
#print axioms MeasureTheory.entropyRate_smul_add_smul_le
#print axioms MeasureTheory.continuous_partitionEntropy
#print axioms MeasureTheory.upperSemicontinuous_entropyRate
#print axioms BB61.upperSemicontinuous_shiftEntropy
#print axioms BB61.shiftEntropy_mix_ge
#print axioms BB61.isClosed_le_shiftEntropy
#print axioms BB61.invMeasures_nonempty
#print axioms BB61.integral_fourierPotential
#print axioms BB61.momVec_eq_zero_iff
#print axioms BB61.isCompact_flatSet
#print axioms BB61.exists_priceEntropy_eq
#print axioms BB61.priceEntropy_mono
#print axioms BB61.convex_entropyHypograph
#print axioms BB61.isClosed_entropyHypograph
#print axioms BB61.priceEntropy_le_iInf_measurePressure
#print axioms BB61.exists_measurePressure_lt
#print axioms BB61.iInf_measurePressure_eq_priceEntropy
#print axioms BB61.measurePressure_le_partitionPressure
#print axioms BB61.priceEntropy_le_iInf_partitionPressure
#print axioms Walters.partitionPressure_eq_measurePressure
#print axioms BB61.iInf_partitionPressure_eq_priceEntropy
#print axioms BB61.exists_flatSet_eq_empty
#print axioms BB61.priceEntropy_eq_bot_of_flatSet_eq_empty
#print axioms BB61.exists_partitionPressure_lt
#print axioms BB61.forall_not_equidistributed_of_partitionPressure_lt_floor
#print axioms BB61.problem_10_61_tfae
#print axioms BB61.entDegree_le_flatDegree

-- Theorem E and Theorem 9.1, the linear-programming lower bounds (`BB61/LowerBound.lean`,
-- `BB61/TheoremE.lean`).  The dual reading of Theorem 3.4: a pool of invariant measures that is
-- Fourier-flat to degree `H` bounds `E_H(α)` from BELOW, and a bound above the entropy floor
-- forbids every certificate of that degree.  EVERY declaration below is std3 — the consumer runs
-- on `priceEntropy_le_iInf_partitionPressure`, whose only ingredient is the *Jensen* half of the
-- variational principle, so neither `Walters.partitionPressure_le_measurePressure` nor
-- `LY.entropyRate_floor` is reached.  The pools of Theorem E are hypotheses (`BB61.FlatPool`),
-- not axioms: see the module doc of `BB61/TheoremE.lean`.
#print axioms MeasureTheory.partitionEntropy_sum_smul_le
#print axioms MeasureTheory.entropyRate_sum_smul_le
#print axioms BB61.map_finsetSum_measure
#print axioms BB61.poolMix_mem_invMeasures
#print axioms BB61.le_shiftEntropy_poolMix
#print axioms BB61.integral_poolMix
#print axioms BB61.fourierMoment_poolMix
#print axioms BB61.integral_fourierPotential_re
#print axioms BB61.abs_integral_fourierPotential_le
#print axioms BB61.FlatPool.mixture_mem_flatSet
#print axioms BB61.FlatPool.entropy_le_shiftEntropy_mixture
#print axioms BB61.FlatPool.entropy_le_priceEntropy
#print axioms BB61.sub_le_measurePressure_of_approxFlat
#print axioms BB61.sub_le_partitionPressure_of_approxFlat
#print axioms BB61.floor_lt_partitionPressure_of_le_priceEntropy
#print axioms BB61.not_priceEntropy_lt_of_le
#print axioms BB61.forall_le_floor_lt_partitionPressure
#print axioms BB61.lt_entDegree_of_le_priceEntropy
#print axioms BB61.lt_norm_one_of_partitionPressure_lt
#print axioms BB61.priceEntropy_le_log_two
#print axioms BB61.pow_one_add_div_le_exp
#print axioms BB61.log_div_two_lt_of_lt_pow
#print axioms BB61.onePlusSqrt2_floor_lt
#print axioms BB61.halfThreePlusSqrt5_floor_lt
#print axioms BB61.halfThreePlusSqrt13_floor_lt
#print axioms BB61.theoremE_onePlusSqrt2
#print axioms BB61.theoremE_halfThreePlusSqrt5
#print axioms BB61.theoremE_halfThreePlusSqrt13
#print axioms BB61.theoremE_onePlusSqrt2_entDegree
#print axioms BB61.onePlusSqrt2_floor_lt_045
#print axioms BB61.theoremE_onePlusSqrt2_approx
