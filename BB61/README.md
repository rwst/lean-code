<!-- (C) 2026 Ralf Stephan, in collaboration with Claude Code. Released under CC0 1.0 Universal. -->
# BB61 — Bugeaud Problem 10.61

> For a Pisot number α > 2 and `C(α) = { (α−1) Σ_{k≥1} ε_k α^{−k} : ε ∈ {0,1}^ℕ }`,
> show that `(ξαⁿ)` is never uniformly distributed mod 1 for ξ ∈ C(α).

Plan: `plans/plan-1061.html`. Notes: `note-1061-L0*.html` (literature audit),
`note-1061-GR.html` (gate G-R), `note-1061-M0.html` (the numerics milestone),
`note-1061-R0.html` (gate G-1 of the counterexample lane).
Engine: `plan_BB61_improve_m3_entropy.html` (the `m3_entropy.py` rewrite, WP1-WP9, and
W4 -- last two sections; **W4 decides `(3+sqrt5)/2` and `(3+sqrt13)/2`**),
`plan-BB61-1+sqrt2.html` (the case none of it reaches).

## M0 — numerics (milestone M0 of the plan, discharged 2026-08-23)

Write-up: **`note-1061-M0.html`**. Headline: the confinement set misses an interval at
α = 2+√3 and at 15 further Pisot numbers, which settles 10.61 there by certificate.

| script | what it does |
| --- | --- |
| `m0_engine.py` | the §2.1 splitting `{ξαⁿ} = {t_n − S_n}`, two stable recursions + a 200-dps check |
| `m0_fourier.py` | closed form of `F̂_*μ_p(h)` for Bernoulli digits (a doubly infinite Erdős product) |
| `m0_scan.py` | mode scan; the trace ladder `h_k = Tr(λαᵏ)`, λ in the codifferent |
| `m0_validate.py` | Monte Carlo check of the closed form at N = 2·10⁶ |
| `m0_coverage.py` | Pisot enumeration (9287 numbers); the two coverage no-gos for Route A and X7 |
| `m0_gaps.py`, `m0_gapsweep.py`, `m0_verify_gap.py` | the confinement-gap certificates, two independent implementations |
| `m0_words.py`, `m0_run_words.py` | 14 structured digit words: Weyl sums, star discrepancy, histograms |
| `m0_markov.py`, `m0_run_adv.py` | exact `F̂` for order-r Markov measures; the adversarial estimate of c(α) |
| `m0_collapse.py` | how the Bernoulli bias constant collapses as ρ → 1 |
| `m0_hist_svg.py` | the histogram figures in the note |

`m0_*.json` are the recorded outputs.

## M1 - the reductions, made rigorous (milestone M1 of the plan, discharged 2026-08-24)

Write-up: **`note-1061-M1.html`**. Section 2 of the plan written as sixteen proved
statements, each verified at five alpha: two quadratic units, a quadratic **non-unit**
(so that multiplication by alpha is a genuine 2-to-1 endomorphism of the torus), a cubic
with a complex conjugate pair, and a totally real cubic.

| script | what it does |
| --- | --- |
| `m1_field.py` | exact arithmetic in `Q(alpha)` on the basis `1,a,..,a^(d-1)` (`fractions.Fraction`): companion matrix, `Tr`, `N`, inverse, `f'(a)`, the codifferent test |
| `m1_torus.py` | the Minkowski torus `R^d / iota(Z[alpha])`: embedding, lattice, trace character tau, endomorphism `Mbar`, the coding `Phi` |
| `m1_verify.py` | one check per numbered result of the note; writes `m1_verify.json` |
| `m1_obs16.py` | Observation 16 at adaptive mpmath precision: the two one-sided Erdos factors along a trace ladder, at units of both norms and at non-units; writes `m1_obs16.json` |
| `m1_obs16i.py` | Observation 16(i): the two one-sided Erdos products against their Lean limits `biProd(shapeFut)` / `biProd(shapePast)`, the reflection, the rate `rho^{2k}`, and the counterexample to (i) as stated; writes `m1_obs16i.json` |
| `m1_cor5.py` | Corollary 5's lower bound on `rho` and the ceiling `alpha > 2^d`, over every monic integer quadratic and cubic with a real root `> 1` and all conjugates inside the unit disc (1561 + 2038 of them): the norm bound, `rho >= alpha^{-1/(d-1)}`, sharpness of `min A log2 alpha = d`, and that no `alpha <= 2^d` fires; roots refined to 30 digits with mpmath; writes `m1_cor5.json` |
| `m2_prop1_lean.py` | numeric companion of `RouteANormalForm.lean`: M2 Prop. 1 and Cor. 6 re-run in the *`QuadSetup` coordinates* the Lean file uses (`beta = a - alpha`, the norm as the constant coefficient `b`) rather than the note's `(rho, |N|)` -- the four-way equivalence and `A log2 alpha = 1 + L/R` over all 9287 Pisot, and `|beta| = |b|/alpha`, `R = L - log2|b|`, Cor. 6 and the unit case over the 440 quadratics, recomputed from their integer coefficients at 60 digits; writes `m2_prop1_lean.json` |
| `m2_thm2i_lean.py` | numeric companion of `RouteADepth.lean`: the balanced ray `M' = ceil(ML/R)` -- the three estimates the Theorem 2(i) proof is made of, the affine bound at both constants over all 9287 Pisot at ten depths, the engine identity `cert = 2(2K+1)*coverTotal`, Cor. 3's own pairs `(17,17)` and `(751,1502)` reproduced, and the *Lean* engine's first balanced certified depth at `2+sqrt5`; writes `m2_thm2i_lean.json` |
| `m2_thm5_lean.py` | numeric companion of `RouteAFamily.lean`: each step of the *Rouché-free* root count separately (`|z|>=1 => |z|>=a-1/2`, `|z|<1 => |z|^{d-1}>=1/(a+1)`, product of all moduli `= 1`, exactly one big root) over 91 `(d,a)` pairs at 60 digits, the counting inequality swept to `d < 40`, the conjugate bound, and the note's own §5 rows (`A(4,16)=1.00329` misses, `A(4,17)=0.98152` fires, …); irreducibility cross-checked with sympy; writes `m2_thm5_lean.json` |
| `m2_prop7_lean.py` | numeric companion of `WindowDiam.lean`: every step of Prop. 7 separately over all 9287 enumerated Pisot numbers at 60 digits -- `Σ_m c_m = -(d-1)` from the closed form (deviation `0.0`), `diam K = Σ|c_m|` and the identity `diam K = (d-1) + 2P` on 1514 rows with an explicit float64 tail bound, greedy words never beaten by 4000 random ones, the equality case, and the note's own minima `min 2Δ/g = 2.20/4.81/8.34`; writes `m2_prop7_lean.json` |
| `m2_prop8_lean.py` | numeric companion of `BlockRecoding.lean`: every step of Prop. 8 separately at 60 digits -- the integer trace ladder `t_n = α^n + β^n` on all 440 quadratics, the power polynomial's integrality and its second root `β^p` (which the naive reading misses by up to `0.731`), the scaling identity and Prop. 8's display on all 9287 enumerated Pisot numbers at eight exponents (deviation `3.8e-56`), the fibre theorem, the note's own three instances, the unit coverage `(4,∞)` at every order, and the trap `A(α^p) = A(α)/p` with the block-constant sliver identity checked to `7.8e-62` and its properness certified; writes `m2_prop8_lean.json` |
| `m2_prop9_lean.py` | numeric companion of `Raster.lean` and `GapSqrtThree.lean`: the raster model and both of its directions on random instances (the alignment loss never exceeds 2 bins), Prop. 9's arithmetic in exact rationals, the **one-sided** depth-2 remainders at `2+√3` against the engine's unusable two-sided `delta 2 2 = 0.196`, the nine endpoints and the eighteen comparisons in exact `ℤ[√3]` with the two zero margins located, the two gaps of length `11√3-19 = 0.0525589` reproduced against `m0_verify_gap.py`'s FFT-free method, **depth 1 giving no gap at all**, zero landings in 20000 orbit points at 400 digits, and the run lengths at `G = 100`, `2^12` and M0's `2^21`; writes `m2_prop9_lean.json` |
| `m3_cor13_lean.py` | numeric companion of `EntropyBudget.lean`: both constants recomputed at 60 digits from the polynomial roots of all 42 candidates of `m0_gapsweep.json` (the sweep M3 sec. 10 ran at 200 dps), the identity `A(alpha) * h_min(alpha) = log 2` to `7.8e-62`, Cor. 13 itself with **zero exceptions** (Route A fires at 6 of the 42, and the floor clears `log 2` at exactly those 6), the entropy budget at `1+sqrt2`, `2+sqrt3` and `(3+sqrt5)/2`, `h_min = (1/2) log alpha` on the 9 quadratic units, and the two criteria crossing at the single point `alpha = 4`; writes `m3_cor13_lean.json` |
| `m3_thm4_lean.py` | numeric companion of `LadderReduction.lean`, at **120 digits**: the decomposition `(alpha-1)alpha^j = T_j - c_j` and the ladder identity to `1e-112`, the error bound `(W+1)|beta|^m` on 672 instances (worst ratio `0.48`, and **neither summand of `W+1` can be dropped**), the `2pi|n|`-Lipschitz character with worst ratio `0.9997`, Theorem 4 itself on 1248 periodic-orbit instances, Bernoulli(1/2) in closed form converging at or below the proved rate (the successive ratios oscillate at norm `-1`), Cor. 5 on non-Bernoulli measures, and the anchor that `phiCoeff` **is** the note's `Phi` -- it reproduces M0's plateau table value `0.359300` at `2+sqrt3` along M0's own ladder `780, 2911, 10864, ...`; writes `m3_thm4_lean.json` |
| `m3_cor6_lean.py` | numeric companion of `LadderScope.lean`, at **120 digits**: the trace-form criterion `Tr(Z[alpha]) subset 2Z <=> 2 | a` against brute force over the order (the half frequency is legal at 9 of the 15 quadratics of `m0_gapsweep.json`), `2 H_k = T_k`, **M1's F8 ladder table reproduced exactly** (`1,1,3,7,17,41,99,239` at `1+sqrt2` and `1,2,7,26,97,362,1351` at `2+sqrt3`), the two-sided ladder `T_n = alpha^n + beta^n` over `[-25,25]` to `1.1e-99`, an exhaustive search over `0 < |n| <= 400`, `|j| <= 20` finding **no** realisation of the half-ladder, **M1's plateau table recomputed** (`451.9` at `1+sqrt2`, `3.64` the other way at `2+sqrt3`, against the note's `452` and `3.6`), the orbit limit independent of the entry point to `8.8e-15`, the half-character's sign flip, and the `lad 2 4` caveat; writes `m3_cor6_lean.json` |
| `m3_thm78_lean.py` | numeric companion of `KernelCriterion.lean`: the Gram identity `Q_B = sum_k |P_k|^2` to `9.0e-49` with PSD eigenvalues (the **Bochner-free** reading), `int_T Q_B = tr B`, the measure computation on periodic-orbit invariant measures, the certificate `G = c(0) - Q` having zero mean, Theorem 8(c)'s identity `Q = c(0) - 2G` **exact**, a check that this construction is **not** a re-derivation of the note's Fejer-Riesz one (the two nonneg polynomials differ by at least `3.73` in sup norm), `sup_T Q >= c(0)` always, and the anchor -- an explicit convex combination of 9 periodic orbits at `1+sqrt2` killing the first 4 Fourier modes, after which **every** kernel of that reach has `int Q.F dmu = tr B` to `1.8e-16`, which is M3 sec. 7's `c(alpha) = 0` re-derived from Theorem 8(a); writes `m3_thm78_lean.json` |
| `m3_prop1_lean.py` | numeric companion of `Tube.lean`: the witness sets for the two-dimensional tube condition and for the one-dimensional `z_2 - (u + v beta) in B` are **identical** over a search box, `alpha beta = -b` and the integer recursion `(p,q) -> (q b, p + q a)` behind `beta^n in Z + beta Z`, `covol^2 = a^2 + 4b`, **the plan's ratio `Leb(B)/covol` driven from `0.0707` down to `7.07e-7` with coverage intact at every step** (only the witness box grows, `N = 8` to `2^20`), an explicit `N(delta)` making `{v beta}` delta-dense, `dim_B K < 1` **exactly when** `|beta| < 1/2` -- the plan's own expected-coverage condition -- with the outer measures of the `2^n` covers, the plan's bound on `Leb_1(K)` against its true value `0`, and the `1/N` gap decay of the note's line `L`; writes `m3_prop1_lean.json` |
| `r0_lean.py` | numeric companion of `FullSupport.lean`: the *Lean* greedy (`min n floor(w)`, a different one from `r0_support.py`'s) run at 60 digits, its `[0,L]` invariant, and the reconstruction of `(eps, delta)` from `(b, u)` checked against M1's own `pi` and `w` over 801 targets per alpha; also `P`, `Q`, the hull and `sum_{m odd} rho^m = 1/2`; writes `r0_lean.json` |
| `m1_htmlcheck.py` | house validator for the `note-1061-*.html` family: tag balance, MathJax delimiter balance and config, raw angle brackets inside math |

Requires numpy, scipy, mpmath.

## Lean formalization (`lean_lib BB61`, 2026-08-24)

The M2 Route A theorem formalized at degree two, **sorry-free and axiom-clean**
(std3 only: `propext, Classical.choice, Quot.sound` -- checked by `AxCheck.lean`;
no cited axiom, no `native_decide`).

**One declared exception**, added 2026-08-25: `BB61/Floor.lean` consumes the single cited axiom
`LY.entropyRate_floor` (`CITED/LedrappierYoung.lean`, M3 Theorem 11 -- the Ledrappier-Young
entropy floor), which is what makes 10.61 at `2 + sqrt3` unconditional.  Everything else in the
root, including all the capstones of `Window.lean`, stays std3; `AxCheck.lean` checks that the
axiom appears in exactly four declarations and nowhere else.

| file | contents |
| --- | --- |
| `Defs.lean` | the Cantor map `piVal`/`cantorSet`, the setting `QuadSetup` (`a b : Z`, `alpha^2 = a alpha + b`, `1 < alpha`, `\|a - alpha\| < 1`), the integer conjugate-pair recursion `uv` (no number-field machinery) |
| `Cantor.lean` | **M1 Lemma 1**: the coding IFS `ifsMap`, the attractor identity `cantorSet_eq_union` and the extreme values (i); the gap `gap alpha = (alpha-2)/alpha` with `gap_pos_iff` (`g > 0` iff `alpha > 2`), the branch images and their disjointness (ii); `injective_piVal`, the homeomorphism `piHomeomorph` and `volume_cantorSet` (`Leb(C(alpha)) = 0`) (iii); strong separation `gap_mul_le_abs_piVal_sub` (iv); and the conjugacy `tauMap_piVal` (v) (see below) |
| `Admissible.lean` | **M1 Proposition 14**: the Renyi-Parry transformation `betaT`, the greedy expansion `greedyExp`, and `greedyExp_boolVal` -- for `alpha > 2` the greedy `alpha`-expansion of the value of a `{0,1}`-word *is* that word, so every `{0,1}`-word is admissible (`isAdmissible_bitZ`, `range_bitZ_subset_closure_admissible`), which is the licence for citing the `theta`-shift literature at `C(alpha)` at all.  With the converse `greedy_tsum` the note's "hence" becomes an equality: `cantorSet_eq_image_boolCoded`, `C(alpha) = (alpha-1) B(alpha)` (see below) |
| `TraceLadder.lean` | **M1 Proposition 15**: the integer solutions of `alpha`'s recurrence are exactly the trace ladders `h_k = Tr(lambda alpha^k)` over the codifferent `d^-1 = {gamma : Tr(gamma Z[alpha]) subset Z}` (`integer_recurrence_iff_trace_ladder`), with `lambda |-> (h_k)` a Z-module isomorphism `d^-1 = R = Z^d` (`codifferentEquivLadders`, `laddersEquivInit`) and Euler's `d^-1 = f'(alpha)^-1 Z[alpha]` (`codifferent_eq_smul_adjoin`).  Degree-two bridge: the M7 ladders of `Ladder.lean` ARE `R` (`QuadSetup.recModule_eq_range_lad`, `lad_iff_trace_ladder`).  Built on `ForMathlib/NumberTheory/TraceLadder.lean` (see below) |
| `Plateau.lean` | **M1 Observation 16(ii)**: division-free Binet (`lad_binet`), the reflection identity (`lad_mul_beta_pow`), and the *exact* shape of the two weight bands of a ladder mode (`abs_future_sub_shape`, `abs_past_sub_shape`).  The mirror: `abs_shapePast_profile` -- the past profile is the future profile times `|b|^d |beta-1|/(alpha-1)`, a **constant** iff `|b| = 1` (`abs_beta_eq_inv_alpha_iff`, `inv_alpha_lt_abs_beta`).  Plus the rate `rho^{2k}` (`abs_future_band`, `abs_past_band`) and the norm-`+1` exactness (`past_weight_eq_neg_future_weight`).  Numerics `m1_obs16.py` |
| `WeylProduct.lean` | **M1 Observation 16(i)**: the two one-sided Erdos products themselves.  `multipliable_futProd` / `multipliable_pastProd` (they converge, at every mode); `tendsto_futProd` -> `biProd(shapeFut)` at **every** quadratic `alpha`, `tendsto_pastProd` -> `biProd(shapePast)` at a unit, `tendsto_weylProd` for the plateau.  At norm `+1` `pastProd_eq_futProd` makes the two products *equal at every mode* (`weylProd_eq_sq`).  The exact criterion: `biProd_shapePast_eq_shapeFutC` and `biProd_shapePast_eq_of_pow` -- (i) as stated is **false** for a general ladder.  Numerics `m1_obs16i.py` |
| `Splitting.lean` | the exact splitting `Int.fract (xi alpha^n) = Int.fract (t_n - S_n)` (`fract_split`, M1 Lemma 2/Prop. 4 at degree 2), window sum and bound |
| `Covering.lean` | truncation errors, the finite candidate set (at most `2^M 2^M' (2K+1)` values, uniform in `xi` and `n`), the avoided-interval engine `exists_avoided_interval` |
| `Criterion.lean` | **M1 Corollary 5**: the covering engine as a *criterion*.  Along the ray `(M,M') = (pn,qn)` the certificate value is `(4K+2)(x^n + c y^n)` with `x = 2^{p+q} alpha^{-p}`, `y = 2^{p+q} rho^q`, so it fires as soon as both ratios are `< 1` (`exists_avoided_interval_of_geom`); taking logarithms this is exactly `routeAExponent = log2/log alpha + log2/log(1/rho) < 1`, M2's normal form `(L-1)(R-1) > 1` (`not_equidistributed_of_routeAExponent_lt_one`) (see below) |
| `Hausdorff.lean` | **M1 Lemma 1(iii), the Hausdorff half**: the fair coin on `{0,1}^N` (`coinMeasure`) pushed forward by `pi` (`codingMeasure`), Lemma 1(iv) read backwards (`preimage_subset_agreeSet`: a set of diameter below `g alpha^{-M}` has all its preimages in one depth-`M` cylinder), the Frostman estimate (`codingMeasure_frostman`, off `alpha^{-d} = 1/2` at `d = log2/log alpha`), and hence `dim_H C(alpha) = log2/log alpha` (`dimH_cantorSet`) and `dim_H = dim_B` (`dimH_eq_upperBoxDim_cantorSet`).  Uses `ForMathlib/MeasureTheory/MassDistribution.lean` (see below) |
| `BoxDim.lean` | **M1 Lemma 1(iii), Lemma 3 and Corollary 5 as *stated***, on `ForMathlib/Topology/MetricSpace/BoxDimension.lean`: `dim_B C(alpha) = log2/log alpha` -- and it *exists*, upper and lower value agreeing (`upperBoxDim_cantorSet`, `lowerBoxDim_cantorSet`), from the truncation cover against the `2^M` separated words of Lemma 1(iv); `dim_B K <= log2/log(1/rho)` (`upperBoxDim_windowSet_le`); `dim_B X(alpha) <= A(alpha)` (`upperBoxDim_confSet_le`) by subadditivity on difference sets; the same two ceilings for the Hausdorff dimension (`dimH_cantorSet_le`, `dimH_confSet_le`); and the note's own route to 10.61, `A(alpha) < 1` => `Leb(X(alpha)) = 0` => `X(alpha) != T` (`confCircle_ne_univ_of_volume_confSet_eq_zero`) (see below) |
| `RouteACeiling.lean` | **M1 Corollary 5's lower bound on `rho`**, the note's last prose clause.  At general degree: for a monic `p` in `Z[X]` with `p(0) != 0` whose complex roots are `alpha` together with a multiset `s` of modulus `<= rho`, `1 <= alpha rho^card s` (`one_le_mul_pow_of_monic_int` -- the product of the roots is `+- p(0)`, a nonzero integer), hence `rho >= alpha^{-1/(d-1)}` (`rpow_neg_inv_le_of_one_le_mul_pow`), `d log2/log alpha <= A(alpha)` (`routeA_ge_of_one_le_mul_pow`) and **`A(alpha) < 1` forces `alpha > 2^d`** (`two_pow_natDegree_lt_of_routeA_lt_one`).  At degree two the whole bound is `alpha |beta| = |b| >= 1` (`one_le_alpha_mul_abs_beta`), so `4 < alpha` (`four_lt_alpha_of_routeAExponent_lt_one`) and **Route A never touches `2 < alpha <= 4`** (`one_le_routeAExponent_of_alpha_le_four`); `quadPoly_roots` checks that the two are the same statement.  Numerics `m1_cor5.py` |
| `RouteANormalForm.lean` | **M2 Proposition 1, the normal form**, and **Corollary 6**.  With `L = logAlpha = log2 alpha` and `R = logRhoInv = log2(1/rho)`, `A(alpha) = 1/L + 1/R` (`routeAExponent_eq_inv_add_inv`) and the four statements `A < 1`, `(L-1)(R-1) > 1`, `R > L/(L-1)`, `rho < 2^{-L/(L-1)}` are equivalent (`routeAExponent_lt_one_iff_one_lt_normalForm`, `..._iff_threshold_lt_logRhoInv`, `..._iff_abs_beta_lt_rpow`); `A log2 alpha = 1 + L/R` (`routeAExponent_mul_logAlpha`).  The asymptotes are theorems: `L/(L-1) > 1` always (`one_lt_div_sub_one`), strictly decreasing, tending to `1`, so **`R > 1` is necessary however large `alpha` is** (`one_lt_logRhoInv_of_lt_one`).  At degree two `rho = |b|/alpha` exactly (`abs_beta_eq_div`), so `R = L - log2|b|` and **`A < 1` iff `(log2 alpha - 1)(log2(alpha/|b|) - 1) > 1`** (`routeAExponent_lt_one_iff_quadratic`), which at units is **`alpha > 4`** (`routeAExponent_lt_one_iff_four_lt`) -- the converse `RouteACeiling.lean` lacked.  Numerics `m2_prop1_lean.py` |
| `RouteADepth.lean` | **M2 Theorem 2(i): certified depths exist**, along the *balanced* ray `M' = ceil(ML/R)` (`balancedDepth`).  The covering total `T(M,M') = 2^{M+M'}(alpha^{-M} + C rho^{M'}/(1-rho))` (`coverTotal`) obeys **`log2 T <= 1 + log2(1+C/(1-rho)) + M (1-(L-1)(R-1))/R`** (`logb_coverTotal_balancedDepth_le`) off three isolated estimates -- `pow_balancedDepth_le` (`rho^{M'} <= alpha^{-M}`, i.e. `Nat.le_ceil`), `two_pow_balancedDepth_le` (the ceiling costs exactly one factor `2`) and `slope_eq`.  `slope_neg_iff`: the slope is negative **exactly** under Prop. 1's normal form, so `T -> 0` (`tendsto_coverTotal_balancedDepth`) with an explicit sufficient `M` (`coverTotal_balancedDepth_lt_of_logb_le`).  At degree two the engine's certificate is `2(2K+1)*T` at `C = 1+rho` (`cert_eq_coverTotal`), giving `exists_avoided_interval_at_balancedDepth` and `not_equidistributed_at_balancedDepth` -- `Criterion.lean`'s conclusion by the note's own route.  Numerics `m2_thm2i_lean.py` |
| `RouteAFamily.lean` | **M2 Theorem 5: the explicit family `X^d - aX^{d-1} - 1`, in every degree.**  (i) `card_big_roots_eq_one` — `α` is the only root of modulus `≥ 1`, **proved without Rouché** (Mathlib has none) by a product-of-moduli count in integer powers; hence `isPisot_family`, and by the same argument on a cofactor `minpoly_eq_familyPoly`, so `familyPoly_irreducible`, **degree exactly `d`** and **a unit**.  (ii) `norm_le_familyConjBound`: `a‖z‖^{d-1} ≤ 2`.  (iii) `routeA_family_lt_one`: `a ≥ 2^{d+1}` forces `A(α) < 1`.  (iv) `d = 2` — `familyQuad` is a `QuadSetup`, so the conclusion is **10.61 itself for every `a ≥ 4`** (`familyQuad_not_equidistributed`), threshold an *iff*, first member `2+√5`; `d = 3` — `norm_sq_mul_eq_one_cubic` gives `ρ = α^{-1/2}`, so `A·log₂α = 3` (**on** the Prop. 4 ceiling) and `A < 1 ↔ a ≥ 8`.  Numerics `m2_thm5_lean.py` |
| `WindowDiam.lean` | **M2 Proposition 7: the width of the window, and the death of X7.**  `diam_windowOf` — `diam K = Σ_m |c_m|` **exactly** (both endpoints hit by greedy words, so an identity, not M1 Lemma 3's estimate); `diam_windowOf_eq_two_mul_posSum` — `diam K = -(Σ c_m) + 2Σ_{c_m>0} c_m`, i.e. `|x| = 2max(x,0) - x` summed; `diam_windowOf_eq_neg_tsum_iff` — the bound is attained iff no `c_m > 0`.  `hasSum_conjCoefC` — one geometric series per conjugate, each worth exactly `-1`, so `Σ_m c_m = -(d-1)`.  Hence `not_x7Criterion`: `2Δ < g` is **empty**.  Zero margin: `unitQuad` (`X² - aX + 1`) has `Δ = diam K = d-1 = 1` — every inequality of the chain an equality — and `tendsto_ratio_unitQuadSeq` sends `2Δ/g → 2`.  Numerics `m2_prop7_lean.py` |
| `BlockRecoding.lean` | **M2 Proposition 8: block recoding is exactly neutral.**  `RatioData` is the triple `(log #alphabet, log base, log 1/contraction)` a ratio criterion sees; `RatioData.block` multiplies all three by `p`; `ratios_scale` leaves `(L,R)` fixed, so `apply_ratios_block` is **one** no-go covering Route A, the dimension, the entropy deficit and Mendès-France at once.  `ratios_eq_iff` is the converse — the fibres of `ratios` *are* the recoding orbits.  `power` builds the actual power polynomial `X² - t_p X + (-b)^p` from the integer ladder `traceSeq`, `power_beta` proves its second root is `β^p`, and `blockData_eq_block` is check P8.  Display: `blockRecoding_expo`; coverage: `routeACriterion_blockData_iff_four_lt`.  The trap: `routeAExponent_power` (`A(α^p) = A(α)/p`).  Numerics `m2_prop8_lean.py` |
| `Raster.lean` | **M2 Proposition 9: the X8 raster criterion, both directions.**  Bins are the fibres of `binIdx G x = ⌊x·G⌋`, so everything rests on two facts: a raster never loses a point (`subset_occSet`) and gains less than one bin (`occSet_dist`).  `runSet_inter_occSet_eq_empty` is soundness — M0's direction, what makes X8 a *proof* method; `exists_zeroRun` is completeness at a given resolution, with the alignment loss of 2 bins the only loss and no hypothesis at all; `exists_certified_gap` composes; `gap_pos_of_resolution` is the note's `2^3 > 6`; `prop9` is Proposition 9.  §5 on the engine: `X8Cert`, `not_equidistributed_of_X8Cert`, and `exists_X8Cert_of_cert` = **Route A ⊆ X8**.  Numerics `m2_prop9_lean.py` |
| `GapSqrtThree.lean` | **The certified gap at `2+√3`, and `Route A ⊊ X8`.**  M0 §6.2's certificate, at depth `(2,2)` and exact in `ℤ[√3]`: nine intervals, eighteen comparisons, **two of them equalities**.  `covThree_inter_gapIoo_eq_empty` is the certificate, `gap_two_add_sqrt3` the avoided interval `(11-6√3, 5√3-8)`, and `problem_10_61_two_add_sqrt3_axiom_free` is **10.61 at `2+√3` with no citation** — the same statement `Floor.lean` proves through the cited entropy floor.  `routeA_subset_X8_strict` is the strictness.  Numerics `m2_prop9_lean.py` |
| `EntropyBudget.lean` | **M3 Corollary 13: entropy alone cannot beat Route A**, and the first statement in which the root's two lanes meet.  `routeAExponent_mul_hMin` is the identity `A(alpha) * h_min(alpha) = log 2` between `Criterion.lean`'s exponent and `CITED/LedrappierYoung.lean`'s floor; hence `routeAExponent_lt_one_iff_log_two_lt_hMin` (**`A < 1` iff `log 2 < h_min`**) and `zero_lt_entropyBudget_iff` (the budget `log 2 - h_min` is positive exactly when Route A fails).  Readings: `log_two_lt_hMin_iff_four_lt_of_unit` puts M2 Prop. 1's `alpha > 4` on the floor, and `routeAExponent_lt_one_iff_four_lt_of_floor` runs it backwards -- a **third** proof of the unit threshold.  Uses only the *definition* `LY.hMin`, never the cited axiom, so the file is axiom-free.  Numerics `m3_cor13_lean.py` |
| `LadderReduction.lean` | **M3 Theorem 4: the past drops out.**  At degree two the theorem is an *identity between real numbers*, `Tr_m * t(omega+) = (an integer) + Ftilde(sigma^m omega) + E_m` (`traceSeq_mul_piVal_futures`), whose mechanism is `Bernoulli.lean`'s `trace_pw` read backwards: `(alpha-1)alpha^j = T_j - c_j` (`futureWeight_eq`), the `j`-th **future** weight is an integer minus the `j`-th **window** weight.  `abs_ladderErr_le` is the note's `W + d - 1` at `d = 2`; `thm4` is Theorem 4 for measures; `tendsto_futureCoeff` is `Phi_h(mu) = lim_m nu-hat(h Tr_m)`; `exists_tendsto_futureCoeff` is **M3 Cor. 5 at integer frequencies** -- the plateau exists for *every* invariant measure; `not_equidistributed_of_ladder` is 10.61 from the future marginal alone.  No unit hypothesis, no ergodic theorem.  Numerics `m3_thm4_lean.py` |
| `LadderScope.lean` | **M3 Corollary 6: which ladders may enter a proof**, and the answer to M1's `452`.  `tendsto_futureCoeff_orbit` is the positive half -- every entry point `j` into the `alpha`-orbit of an integer frequency gives the *same* limit, so an orbit carries **one** constraint.  The negative half is parity, and one condition does both: `two_dvd_trForm_iff` (`Tr(Z[alpha]) subset 2Z` iff `2 | a`) is exactly when `gamma = 1/2` is legal, and exactly then `not_intOrbitLadder_halfLad` -- the half-ladder is **odd at the origin** while `two_dvd_traceSeqZ` makes every `n T_{k+j}` even.  `cor6` joins them; `halfLad_isTraceLadder` certifies via M1 Prop. 15 that the half-ladder is a genuine codifferent ladder; `no_half_character` is the analytic register (`e(x/2)` does not descend to `R/Z`).  Parity is an obstruction, **not** a classification (`lad 2 4`).  Numerics `m3_cor6_lean.py` |
| `KernelCriterion.lean` | **M3 Theorems 7 and 8: the B-criterion, and Route B = Route D.**  Stated over `Gamma subset Z`, which M3 Cor. 6 licenses (the note's reach `H_Gamma` collapses and its condition (i) is vacuous).  **Neither theorem the note imports is needed**: the Gram form makes `Q >= 0` an inspection (`matKernel_gram`, `gram_posSemidef`), and Fejer-Riesz is replaced by one explicit sum of squares -- the one-term polynomials `1 - a_h e(h.)` give `Q = c(0) - 2G` exactly (`exists_kernel_of_trigCertificate`).  Read backwards that is Theorem 7: `kernelCertificate` makes a kernel a Route D certificate `G = c(0) - Q`.  `no_killer_of_kernel` is 8(a); 8(b) is both directions, the hard one being M3 Thm 9's separation with the test family *prescribed*; **`exists_kernel_iff`** is the three-way equivalence.  Sanity check: `confCircle_ne_univ_of_kernel` -- a *pointwise* kernel is never more than X8's confinement gap, hence **empty** at `1+sqrt2` and `(3+sqrt5)/2` (`silver_not_pointwise_kernel`).  Numerics `m3_thm78_lean.py` |
| `Tube.lean` | **M3 Proposition 1: the tube criterion is vacuous.**  The covering question is one-dimensional and purely algebraic -- `tube_add_eq_univ_iff` says `T_B + Lambda = R^d` iff `B + shadow Lambda = R^{d-1}`, no topology, no discreteness, any degree -- so Proposition 1 is `add_dense_eq_univ` applied to the shadow (`image_mk_tube_eq_univ`, `prop1`).  The density of `Z + beta Z` needs **neither Pontryagin duality nor irrationality**: `beta^n` is a non-zero element of it tending to `0` (`dense_shadow`).  `prop1_thickening` is the note's "for every window" -- the plan's tube is over `K_delta`, which is open.  `exists_tube_small_shadow` refutes "morally `Leb_1(K)`/covolume" quantitatively, and **`tube_window_dichotomy`** is the sharp form: on the plan's own target family `|beta| < 1/2` the fattened tube is everything for every `delta > 0` and the exact one is null.  Numerics `m3_prop1_lean.py` |
| `Factor.lean` | **M1 Lemma 6**: the two-sided shift `Shift = Z -> Bool`, the window map `wVal`, the factor map `fMap : Shift -> AddCircle 1`, its Hoelder estimate, and the orbit identity `fMap (sigma^n omega~) = xi alpha^n mod 1` (see below) |
| `FullSupport.lean` | **R0 Theorem 1 and Corollary 3**, and the folder's first *positive* `confCircle`: the covering lemma `tsum_covDigit` (greedy digit `min n floor(w)`, invariant `residual in [0,L]`), the parity relabelling `parityFlip`/`tsum_dR_parityFlip` with `sum_{m odd} rho^m = 1/2` at `1+sqrt2`, hence `silver_confSet = [-sqrt2/2, 2+sqrt2/2]` and `goldenSq_confSet = [0,2]` **exactly**, hence **`confCircle = Set.univ`** at both (`silver_confCircle`, `goldenSq_confCircle`) and *no* avoided interval can exist there (`silver_no_avoided_interval`).  Numerics `r0_lean.py` |
| `Confinement.lean` | **M1 Lemma 3 and Prop. 4**: the window `windowSet = range wVal` (compact, endpoints attained, `diam K >= 1`), the confinement set `confCircle = X(alpha) = (C(alpha) - K) mod 1` (compact, and **equal to the range of the factor map**), exact confinement `coe_mul_pow_mem_confCircle` with no error term, sharpness `closure_orbitRaw`, and the criterion `not_denseModuloOne_of_confCircle_ne_univ` (see below) |
| `Invariant.lean` | **M1 Theorem 7**: empirical measures, `lambda_N = F_* nu_N` (`map_orbitEmp`), every weak-* limit is `F_* mu` with `mu` shift-invariant (`exists_invariant_of_tendsto`), and the **master target** `not_equidistributed_of_no_invariant` (see below) |
| `WeakStar.lean` | the weak-* toolbox both realization converses use: testing convergence on a dense family (`tendsto_of_dense_of_tendsto_integral`), Cesaro comparison of nearby orbits, and the bridge `equidistributed_of_tendsto_emp` (weak-* convergence to Haar **is** u.d. mod 1) |
| `Realization.lean` | **M1 Prop. 8(i)**: the ergodic realization converse -- every ergodic `sigma`-invariant `mu` on `{0,1}^Z` is realized by a point of `C(alpha)`, `exists_tendsto_map_of_ergodic`, and **M1 Cor. 9** for ergodic `mu` (`exists_equidistributed_of_ergodic`).  The one file in the root that leaves Mathlib: it runs the vendored pointwise Birkhoff theorem (`lean_lib BirkhoffErgodicThm`) (see below) |
| `Words.lean` | the combinatorics of **M1 Prop. 8(ii)**: `StageData`, the staged word `word` (stage `j` fills `[T j, T (j+1))` with `AA j` atoms of length `NN j` copied off sources `om j l`), and `agree_shift` -- deep inside an atom the padded staged word and its source see the same central window (see below) |
| `MeanSelect.lean` | the **greedy sampling lemma**: finitely many mean-zero bounded observables on any probability space are killed simultaneously by the equal-weight averages of a greedily chosen sequence, `exists_greedy_le`.  No independence, no ergodic theorem (see below) |
| `Saturation.lean` | **M1 Prop. 8(ii) and Cor. 9**: `exists_tendsto_map_of_invariant` (**every** invariant `mu`, not only the ergodic ones, is realized by a point of `C(alpha)`) and the equivalence `equidistributed_iff_exists_invariant`; also M3 Theorem 9 in the note's own form, `forall_not_equidistributed_iff_exists_trigCertificate` (see below) |
| `RouteA.lean` | the capstone at `alpha = 2 + sqrt 5`: `routeA_two_add_sqrt5` (one uniform missed interval), `two_add_sqrt5_not_denseModuloOne`, `two_add_sqrt5_not_equidistributed` -- **Problem 10.61 at `2 + sqrt 5`, machine-checked**; and `goldenFive_confCircle_ne_univ`, the same certificate read as M1 Prop. 4.  `routeA_two_add_sqrt5_of_geom` reproves the capstone from the criterion at `(p,q) = (1,1)`, the smallest possible parameters, replacing the depth-`(70,70)` rational certificate by two `sqrt 5` estimates; and `two_add_sqrt5_not_equidistributed_of_boxDim` proves it a third time by the note's own route, `A(2+sqrt5) = log 4 / log alpha < 1` (the norm is `-1`, so `rho = 1/alpha` and the two summands coincide) hence `Leb(X) = 0` hence `X != T` |
| `Pressure.lean` | the M4 pressure certificate at `alpha = 2 + sqrt 3`, exact in `Z[sqrt3]` (see below) |
| `PressureCriterion.lean` | **M3 Theorem 12 and the M4 criterion**: pressure below the entropy floor forbids every counterexample measure, hence 10.61 at `alpha` (`forall_not_equidistributed_of_partitionPressure_lt`); its transfer-certificate form (`forall_not_equidistributed_of_transferBound`); and the capstone `two_add_sqrt3_not_equidistributed_of_window`, which reduces 10.61 at `2+sqrt3` to one window modelling lemma.  Built on `ForMathlib/Dynamics/{TopologicalPressure,PressureTransfer}.lean` (see below) |
| `Window.lean` | **the window modelling lemma at `alpha = 2 + sqrt 3`**: the state observable `stateOf` and its transition rule `stateOf_shiftZ`, the exact `Z[sqrt3]` window value of all 128 words and the cell bound `cwZ_floor_le`, M1 Lemma 6's sharp truncation `eps = 123 - 71 sqrt3`, and the Lebesgue mean `integral_gWin`.  Capstone `two_add_sqrt3_not_equidistributed`: **Problem 10.61 at `2 + sqrt 3`, on the cited entropy floor alone** (see below) |
| `Bernoulli.lean` | the M5 arithmetic core: the pair recursion `pw`, the trace identity, the exact Pisot decay `|(alpha-1)alpha^m - T_m| = |beta-1||beta|^m`, and the two lemmas that keep the Erdos product away from zero (see below) |
| `Ladder.lean` | the M7 arithmetic core: a trace ladder `lad`, the one-step identity `h_{k+1} - alpha h_k = e_0 beta^k`, and the **dead zone** -- the reduced weight of the mode `h_k` is `O(|beta|^{k-i})` at every future depth `i` and `O(alpha^{m-k})` at every past depth `m`, so the profile is `O(1)` only in two bands at depths `+-k` (see below) |
| `Certificate.lean` | **M3 Theorem 9**: `invMeasures` = `M(sigma)` (compact, convex), the `Certificate` structure, `exists_certificate` (Hahn-Banach completeness) and its trigonometric form `exists_trigCertificate_iff` (see below) |
| `Floor.lean` | **the cited lane**: the entropy floor of `CITED/LedrappierYoung.lean` packaged as `floor_of_quadratic_unit`, and the unconditional capstone `problem_10_61_two_add_sqrt3` -- **Problem 10.61 at `2 + sqrt 3`, machine-checked on one cited axiom** (see below) |
| `AxCheck.lean` | axiom hygiene (`#print axioms` over the chain) |

### M1 Lemma 3 and Proposition 4 -- the window and exact confinement (2026-08-25)

`Confinement.lean` is the set-level reading of `Factor.lean`, and the file the note's
Prop. 4 asks for.

**Lemma 3.**  `windowSet = Set.range wVal` is the note's `K`.  It is compact because
`{0,1}^N` is (`isCompact_windowSet`) -- no closure is taken, which is the point.  `wMax` and
`wMin` are the note's `P = sum_{c_m>0} c_m` and `-Q = sum_{c_m<0} c_m`; both are *attained*,
by the greedy words `wPos`/`wNeg`, and `windowSet_subset_Icc` is `K` inside `[-Q, P]`.  The
diameter bound is `tsum_cCoef`: `sum_{m>=0} c_m = -1` at degree two, so
`one_le_wMax_sub_wMin` gives `diam K >= 1 = d - 1`.  That inequality is why no
`K`-versus-gap argument can ever settle 10.61: the window is at least as wide as the unit
interval at every degree `>= 2`.

**Proposition 4.**  The identification that makes it short is that the confinement set *is*
the range of the factor map.  The two halves of a two-sided word are independent (`joinW`,
`futures_joinW`, `pasts_joinW`), so `confSet_eq` reads `range fRaw = C(alpha) - K`, and
`confCircle = Set.range fMap` is `X(alpha) = (C(alpha) - K) mod 1`, compact for free.
Exact confinement is then `fMap_iterate_padZ` read as a membership
(`coe_mul_pow_mem_confCircle`): `{xi alpha^n} in X(alpha)` for every `xi in C(alpha)` and
every `n`, **with no error term** -- the truncated past is a point of `K`, not an
approximation to one (`wVal_padWord`).

**The criterion, and that it is sharp.**  `X(alpha)` is closed and its preimage in `R` is
`1`-periodic, so if `X(alpha) != T` a whole open interval of `(0,1)` is missed by every
orbit at every time (`exists_avoided_interval_of_ne_univ`), hence 10.61 at `alpha` in the
strong form -- not even dense (`not_denseModuloOne_of_confCircle_ne_univ`).  The converse
holds too: `exists_padZ_agree` says every two-sided word is matched on its central block by
a shifted zero-padded one, so with M1 Lemma 6's modulus of continuity
`closure_orbitRaw` gives `X(alpha) = closure(orbits)`, and
`confCircle_ne_univ_of_avoided` turns a missed interval back into `X(alpha) != T`.  So the
covering engine of `Covering.lean` -- which never names `X(alpha)` -- is *exactly* a proof
of Prop. 4's hypothesis; `goldenFive_confCircle_ne_univ` in `RouteA.lean` is that reading at
`2 + sqrt 5`.

M1 Cor. 5, the box-dimension ceiling
`dim_B X(alpha) <= log2/log alpha + log2/log(1/rho)`, is `BoxDim.lean`, on a box dimension
written for the purpose (Mathlib has none).  What the ceiling is *for* -- that a Route A firing
needs `alpha > 2^d`, via `rho >= alpha^{-1/(d-1)}` -- stays prose: it is a statement about the
conjugates of an algebraic number of degree `d`, and `QuadSetup` fixes `d = 2`.

### M1 Lemma 6 and Theorem 7 (2026-08-25)

`Factor.lean` and `Invariant.lean` carry the only measure theory in the root, and they
formalise the two statements the paper's headline rests on.

**Lemma 6 (`Factor.lean`).**  `Shift = Z -> Bool` with the product topology; `shiftZ` is the
left shift, `futures`/`pasts` the two halves, `padZ eps` the word `eps` padded by zeros on
the non-positive coordinates.  The window map is `wVal delta = sum_m c_m delta_m` with
`c_m = (beta-1) beta^m`, and `fRaw omega = t(omega^+) - S(omega^-)`, `fMap = fRaw mod 1`
valued in `AddCircle (1 : R)`.  Two theorems:

* `abs_fRaw_sub_le_of_agree` -- words agreeing on the block `[-N, N]` have
  `|F omega - F omega'| <= alpha^-N + (1+|beta|)|beta|^(N+1)/(1-|beta|)`.  The note's shift
  metric is `d = 2^-N`, so `holder_fRaw` restates it as Hoelder continuity for any exponent
  `theta` with `2^theta <= alpha` and `2^theta |beta| <= 1` -- the largest being the note's
  `theta = min(log alpha, log(1/rho))/log 2`.  `continuous_fMap` is what Theorem 7 consumes.
* `fMap_iterate_padZ` -- `F(sigma^n omega~) = xi alpha^n mod 1` for every `n >= 0`.  It is
  `fract_split` read on the circle, and it turns the orbit into a *shift* orbit.  The
  `O(rho^n)`-free form survives because `wVal_padWord` says the truncated past is a point
  of `K`, not an approximation to one (M1 Prop. 4).

**Theorem 7 (`Invariant.lean`).**  `emp x N` is the empirical measure
`(N+1)^-1 sum_{n<=N} delta_{x n}`, bundled as a `ProbabilityMeasure`.  Then

* `map_orbitEmp` -- `lambda_N = F_* nu_N`, the first sentence of the theorem;
* `exists_invariant_of_tendsto` -- if `lambda_N -> lambda` along **any** `NeBot` filter
  refining `atTop` (the full sequence, or any subsequence), then `lambda = F_* mu` for a
  `sigma`-invariant Borel probability `mu` on `{0,1}^Z`.  The three ingredients are the
  note's: compactness of `ProbabilityMeasure {0,1}^Z` (Mathlib's Prokhorov instance,
  `{0,1}^Z` being compact metrisable), the telescoping bound `|A nu_N - B nu_N| <=
  2||f||/(N+1) -> 0` forcing invariance, and continuity of `F`;
* `not_equidistributed_of_no_invariant` (and `..._measure`, the unbundled form) -- **the
  master target**, exactly as boxed in the note: if no `sigma`-invariant `mu` has
  `F_* mu = Leb`, then 10.61 holds at `alpha`.

The bridge from the counting definition of uniform distribution to weak-* convergence is
`tendsto_emp_of_equidistributed`, which runs the repo's own Riemann criterion
(`ForMathlib/Analysis/Equidistribution/IntegralCriterion.lean`) on the circle, together with
`AddCircle.integral_preimage`.  std3, no `sorry`, no cited axiom.

The other half of M1 Cor. 9 -- **M1 Prop. 8**, the realization converse -- is
`Realization.lean` (see below) for ergodic `mu` and `Saturation.lean` in general.  With the
latter the target here is an **equivalence** (`equidistributed_iff_exists_invariant`): nothing
is lost in the reduction.

Certificate depth `(70, 70)` with integer-part bound `K = 3`, discharged by `norm_num`
(exact rational arithmetic in the kernel).  The Lean engine covers with candidate
*points* (a factor `2K+1 = 7` instead of the note's mod-1 tiling identity), so its
depth is deeper than `m2_verify.py`'s `(17, 17)` -- same criterion, simpler
bookkeeping.  Registered as `lean_lib BB61` in the lakefile; build with
`LEAN_NUM_THREADS=3 lake build BB61`.

### M3 Theorem 9 -- completeness of the certificate scheme (2026-08-25)

`Certificate.lean` sits directly on top of `Invariant.lean` and answers the question M1
Theorem 7 leaves open: *when* is the master target's hypothesis true, and can that always be
seen from finite data?  Theorem 9 says yes.

* `invMeasures` -- `M(sigma)`, the shift-invariant Borel probability measures of the full
  2-shift, with `isCompact_invMeasures` (closed in the compact `ProbabilityMeasure {0,1}^Z`)
  and `mix_mem_invMeasures` (convexity, through explicit mixtures `mixMeasure`).
* `Certificate P` -- a bounded continuous `G : T -> R` with `int G dLeb = 0` and a constant
  `c > 0` with `int G(F omega) dmu >= c` for every `mu` in `M(sigma)`.
* `Certificate.no_invariant`, `Certificate.not_equidistributed` -- the easy direction: a
  certificate kills every invariant measure, hence (M1 Theorem 7) proves 10.61 at `alpha`.
  This is the note's "Route D is always available".
* `exists_certificate` -- the content of Theorem 9: if no invariant `mu` has `F_* mu = Leb`,
  a certificate exists.  The proof is the note's separation argument with the separation
  moved to finite dimension: compactness of `M(sigma)` first cuts the family of test
  functions down to a finite `u` (`IsCompact.elim_finite_subfamily_closed`, with
  `ext_of_forall_integral_eq_of_IsFiniteMeasure` supplying "all test integrals agree =>
  `F_* mu = Leb`"), then `0` is separated from the compact convex image
  `V = {(int g F dmu - int g)_{g in u} : mu in M(sigma)} <= R^u` by
  `geometric_hahn_banach_point_closed`, and the separating functional's coordinates are the
  coefficients of `G`.  This avoids Hahn-Banach in the product `prod_{h != 0} C` of the note,
  and with it the characterisation of that space's dual.
* `nonempty_certificate_iff` -- the equivalence.
* `trigPoly H a = Re sum_{h in H} a_h e(h .)` and `exists_trigCertificate_iff` -- **Theorem 9
  in the note's own form**: the certificate can be taken to be a real *trigonometric
  polynomial* on a finite set of non-zero frequencies, so it is finite data.  Passing from
  the continuous certificate is a Fejer approximation (`span_fourier_closure_eq_top`)
  followed by removal of the constant term; each step costs at most `c/3`, so the certified
  gap survives as `c/3`.  Mean-zero is then automatic (`integral_trigPoly_eq_zero`, from
  `integral_fourier_eq_zero` in `ForMathlib/.../AddCircleWeyl.lean`).
* `not_equidistributed_of_trigPoly` -- the exported implication `certificate => 10.61 at
  alpha`.

std3, no `sorry`, no cited axiom.  Two things the note has and this file does not.  (i) The
note states Theorem 9 with "10.61 holds at `alpha`" on *both* sides of the equivalence;
translating between that and the invariant-measure statement is M1 Cor. 9, whose converse
half is Prop. 8.  This file exports only `certificate => 10.61`; the note's own form is
`forall_not_equidistributed_iff_exists_trigCertificate` in `Saturation.lean`, once Prop. 8(ii)
is available.  (ii) **Corollary 10** (10.61 at a fixed computable `alpha` is `Sigma_1`) needs the
variational principle for topological pressure to turn `min_mu int g dmu > 0` into a
terminating computation; Mathlib has no topological pressure, so Cor. 10 is not formalised.

### M1 Corollary 5 -- the criterion, and box dimension in ForMathlib (2026-08-25)

`Covering.lean` gives the engine in *finite* form: at depths `(M,M')` at most
`2^M 2^{M'} (2K+1)` candidate points cover the orbit of fractional parts within
`delta = alpha^{-M} + (1+rho) rho^{M'}/(1-rho)`, and the numeric certificate
`card * 2 delta < 1` produces a uniformly missed interval.  That is a test, discharged at
`2 + sqrt 5`.  `Criterion.lean` says which `alpha` the test eventually passes.

Run the engine along the ray `(M,M') = (pn,qn)`.  The certificate value factors as a sum of two
geometric sequences,

    card * 2 delta = (4K+2) ( x^n + c y^n ),   x = 2^{p+q} alpha^{-p},  y = 2^{p+q} rho^q,

so it tends to zero, and is eventually below 1, as soon as both ratios are `< 1`
(`exists_avoided_interval_of_geom`).  Taking logarithms, `x < 1` and `y < 1` say
`(p+q)/p < log_2 alpha` and `(p+q)/q < log_2 (1/rho)`, and a ratio `p/(p+q)` strictly between
`log2/log alpha` and `1 - log2/log(1/rho)` exists exactly when

    A(alpha) := log2/log alpha + log2/log(1/rho) < 1     (`routeAExponent`),

which is M2's normal form `(L-1)(R-1) > 1` at `L = log_2 alpha`, `R = log_2(1/rho)`: the two are
the same inequality, since `1/L + 1/R < 1` iff `(L-1)(R-1) > 1` for `L, R > 1`.  Hence
`not_equidistributed_of_routeAExponent_lt_one` -- **Problem 10.61 at every `alpha` with
`A(alpha) < 1`** -- and its Prop. 4 reading `confCircle_ne_univ_of_routeAExponent_lt_one`.  The
rational `p/(p+q)` is produced by `exists_rat_btwn`; the degenerate integer case `beta = 0` is
excluded, `rho = 0` making the second summand of `A(alpha)` a junk value rather than the
intended `0`.

Note what is *not* used: the note proves Corollary 5 from `dim_B(C-K) <= dim_B C + dim_B K` and
`Leb(X(alpha)) = 0`, but the covering counts that define those dimensions are the engine's own
`card` and `delta`, so the asymptotics can be done directly on the certificate.  The dimensions
are needed for the *statement* of Lemma 1(iii), Lemma 3 and Corollary 5, not for the conclusion.

`exists_avoided_interval_of_geom` is also the practical form: at a concrete `alpha` a small pair
`(p,q)` is a certificate with no logarithms in it.  At `2 + sqrt 5` both ratios are `4/alpha` and
`4|beta|`, below 1 at `p = q = 1` because `alpha > 4` and `|beta| < 1/4`, so
`routeA_two_add_sqrt5_of_geom` reproves the capstone from two `sqrt 5` estimates instead of the
depth-`(70,70)` rational arithmetic.

The dimensions themselves are now in `ForMathlib/Topology/MetricSpace/BoxDimension.lean`
(std3, no cited axioms), which Mathlib does not have.  Mathlib gained
`Metric.externalCoveringNumber`/`packingNumber` in 2025 and `ExpGrowth.expGrowthSup` (limsup of
`log u_n / n`), and the file is built on those: `coveringGrowth r A` is the growth rate of the
covering numbers along the scales `r^n`, and `upperBoxDimWith r A = coveringGrowth r A / log r^-1`.
The structural theorem is that the ratio does not matter (`upperBoxDimWith_eq`, and the `liminf`
twin), proved by reindexing one geometric scale by `ceil(n c)` against the other; that is also the
practical point, since a self-similar set is covered naturally at its own contraction ratio, not
at dyadic scales.  On top sit the upper bound from an explicit cover
(`upperBoxDim_le_of_covering`), the matching lower bound from separated subsets
(`le_upperBoxDim_of_separated`, through `packingNumber_two_mul_le_externalCoveringNumber`),
submultiplicativity of covering numbers on sumsets (`externalCoveringNumber_add_le` -- new, and
the reason `upperBoxDim_add_le` holds), and, in `R`, that upper box dimension `< 1` forces
Lebesgue measure zero (`Real.volume_eq_zero_of_upperBoxDim_lt_one`, no Hausdorff measure
involved).  Three side results are about Mathlib objects only and are stated for their own sake:
an optimal *external* cover exists when the covering number is finite (the external analogue of
`exists_set_encard_eq_coveringNumber`), and an index shift does not change an exponential growth
rate (`Monotone.expGrowthSup_comp_add`, and the `liminf` twin).

### The dimensions themselves: `BoxDim.lean` (2026-08-26)

`BoxDim.lean` wires that file into the root and states all three dimension claims of M1.

**Lemma 1(iii), and it is an equality of *both* box dimensions.**  The upper bound is the
depth-`M` truncation cover: `abs_piVal_sub_tCand` puts every point of `C(alpha)` within
`alpha^{-M}` of one of the `2^M` values `tCandSet alpha M`, so
`externalCoveringNumber (alpha^{-M}) <= 2^M` and `upperBoxDim <= log2/log alpha` at the
*natural* ratio `alpha^{-1}` -- which is legitimate only because of `upperBoxDimWith_eq`.  The
lower bound is Lemma 1(iv): the `2^M` words supported in `[0,M)` have distinct `pi`-values
pairwise at least `g alpha^{-k}` apart at the first index `k < M` where they differ, hence at
least `g alpha * alpha^{-M} > g alpha^{-M}` apart -- a `g alpha^{-M}`-separated set of `2^M`
points, which is what `le_lowerBoxDim_of_separated` consumes.  Separated sets at *every* scale
bound the `liminf` as well, so `lowerBoxDim = upperBoxDim = log2/log alpha`: the box dimension
of `C(alpha)` **exists**, and is `< 1` exactly because `alpha > 2`.

That the lower bound lands on `lowerBoxDim` is worth a line, because it is free here and is
not free in general: it needs the separated sets to exist at every scale of the geometric
ladder, which strong separation supplies and a merely-open-set-condition IFS does not.

**Lemma 3.**  `abs_wVal_sub_sCand` is `abs_sPart_sub_sCand` for the whole window `K` rather
than for the finite sums `S_n` inside it: truncating the window series at depth `M'` costs at
most `(1+rho) rho^{M'}/(1-rho)`.  The radius therefore carries a constant, which is why
`Metric.upperBoxDim_le_of_covering_mul_nat` was added upstream -- a fixed factor in the radius
is absorbed by a bounded shift of the scale index (`coveringGrowth_const_mul`).  Only `<=` is
claimed, and only `<=` is true in general: `K` can be much smaller than its coding suggests.
`beta != 0` is required, `rho = 0` making `log(1/rho)` a junk value.

**Corollary 5.**  `confSet_eq` says `X(alpha) = C(alpha) - K` on the nose, and
`Metric.upperBoxDim_sub_le` (new upstream, from `upperBoxDim_add_le` and the fact that `x -> -x`
is an isometry) gives `dim_B X(alpha) <= dim_B C(alpha) + dim_B K = A(alpha)`.  Then
`Real.volume_eq_zero_of_upperBoxDim_lt_one` gives `Leb(X(alpha)) = 0` when `A(alpha) < 1`, and
`confCircle_ne_univ_of_volume_confSet_eq_zero` closes the note's loop: `X(alpha)` is compact,
so inside `[-N,N]`, so its at most `2N+2` integer translates would have to cover `[0,1)`, of
measure one -- impossible for a null set.  This is a **second, independent proof** of
`confCircle_ne_univ_of_routeAExponent_lt_one`, which `Criterion.lean` gets from an explicit
missed interval instead, and the two agree on the hypothesis `A(alpha) < 1` exactly.

At `2 + sqrt 5` the whole chain is sharp: the norm is `-1`, so `rho = 1/alpha`
(`goldenFive_inv_absBeta`), the two summands of `A` coincide, and
`A(2+sqrt5) = log 4 / log alpha < 1` iff `alpha > 4` -- the same inequality as the first
geometric ratio of the criterion.  `two_add_sqrt5_not_equidistributed_of_boxDim` is then a
third proof of the capstone, after the depth-`(70,70)` certificate and the `(p,q) = (1,1)`
criterion.

**The Hausdorff ceilings.**  ForMathlib's `Metric.dimH_le_upperBoxDim` (`dim_H A <= dim_B A`
for nonempty `A`) carries both bounds over: `dimH_cantorSet_le` is
`dim_H C(alpha) <= log2/log alpha` and `dimH_confSet_le` is `dim_H X(alpha) <= A(alpha)`.
For Corollary 5 that detour through the box dimension is not a convenience but the only
route available: the Hausdorff dimension is **not** subadditive on difference sets, so there
is no `dim_H X <= dim_H C(alpha) + dim_H K` to appeal to.

The matching Hausdorff **floor** is `Hausdorff.lean` (below), so Lemma 1(iii) is now complete:
`dim_H C(alpha) = dim_B C(alpha) = log2/log alpha`.

### M1 Cor. 5 -- the lower bound on `rho`, and the ceiling `alpha > 2^d` (2026-08-26)

`Criterion.lean` and `BoxDim.lean` carry Corollary 5's *effective* half: `A(alpha) < 1` proves
10.61 at `alpha`.  What the note left as prose was the **negative** half -- the one clause it
flagged as "a statement about the conjugates of an algebraic number of degree `d`, where the
Lean setting fixes `d = 2`, and that alone":

> for `d >= 2`, `rho >= alpha^{-1/(d-1)}` and therefore `A(alpha) >= d log2 / log alpha`,
> so Route A can fire only when `alpha > 2^d`.

`RouteACeiling.lean` is that clause, and it is formalised at **general degree**, not only at
`d = 2`.  The mathematical content is one line -- `1 <= |N(alpha)| = alpha prod_{j>=2}|alpha_j|
<= alpha rho^{d-1}` -- and the file is mostly the bookkeeping that makes the line honest.

**The norm bound.**  `one_le_mul_pow_of_monic_int`: let `p` be a monic integer polynomial with
`p(0) != 0`, let `alpha > 0` be real, and suppose the complex roots of `p` (with multiplicity)
are `alpha` together with a multiset `s` all of whose members have modulus at most `rho`.  Then
`1 <= alpha * rho^(card s)`.  Two Mathlib facts do the work: `Splits.coeff_zero_eq_prod_roots_of_monic`
says the product of the roots is `(-1)^d p(0)`, and `IsAlgClosed.splits` says a complex
polynomial splits at all.  **Integrality enters exactly once**, and only there: `p(0)` is a
*nonzero rational integer*, so `|p(0)| >= 1`.  Irreducibility is never used and is not needed --
the minimal polynomial is one admissible `p` among many.  `card_add_one_eq_natDegree` then says
`card s = d - 1`, from `Splits.natDegree_eq_card_roots`.

**The three consequences.**  `rpow_neg_inv_le_of_one_le_mul_pow` is the note's own shape,
`alpha^{-1/(d-1)} <= rho`, by raising `alpha^{-1} <= rho^{d-1}` to the power `1/(d-1)`.
`routeA_ge_of_one_le_mul_pow` is the ceiling as an inequality, `d log2/log alpha <= A(alpha)`:
take logarithms, `(d-1) log(1/rho) <= log alpha`, and divide.  `two_pow_lt_of_routeA_lt_one`
and its degree form `two_pow_natDegree_lt_of_routeA_lt_one` are the ceiling itself,
`A(alpha) < 1  =>  2^d < alpha`.

**At degree two the whole thing is one identity.**  `N(alpha) = alpha beta = -b`, so
`one_le_alpha_mul_abs_beta` is `alpha |beta| = |b| >= 1` and nothing else -- three lines off
`alpha_mul_beta` and `Int.one_le_abs`.  This is the *proof* of the inequality M0 found
empirically and `Plateau.lean` (Obs. 16(ii)) explains: `rho >= 1/alpha` always, with equality
exactly at the units.  Then `four_lt_alpha_of_routeAExponent_lt_one` is `A(alpha) < 1 => 4 < alpha`
and `one_le_routeAExponent_of_alpha_le_four` its contrapositive: **Route A never touches the hard
slice `2 < alpha <= 4`**.  M0's sixteen new certificates all live in that slice, so they are out
of Route A's reach by a theorem, not by accident.

**The `d = 1` case is included, and it is not a special case.**  For integer `alpha` the
conjugate is `beta = 0`, the window is a point, and Lean's junk values make the second summand
of `A(alpha)` exactly `0` (`routeAExponent_of_beta_eq_zero`) -- which is the right answer, since
`dim_B K = 0`.  The ceiling then reads `2^1 < alpha`.  Uniformly, at either degree,
`two_lt_alpha_of_routeAExponent_lt_one` says Route A never fires at `alpha <= 2`: the criterion
can never reach outside Problem 10.61's own hypothesis.

**The two halves are checked to be the same statement, not merely compatible.**  `quadPoly` is
`X^2 - aX - b` over `Z`, `quadPoly_map_eq` factors it over `C` as `(X-alpha)(X-beta)` (which is
just `alpha + beta = a`, `alpha beta = -b`), `quadPoly_roots` reads off the root multiset, and
`one_le_alpha_mul_abs_beta_of_monic` re-derives `1 <= alpha |beta|` from the general lemma at
`d = 2`.  `quadPoly_natDegree` confirms `d = 2`, so the general `2^d < alpha` really is the
`4 < alpha` above.

**Operational.**  `m1_cor5.py`, 7/7 verdicts.  It enumerates *every* monic integer polynomial of
degree 2 and 3 in a coefficient box that has one real root `alpha > 1` and all other roots inside
the open unit disc -- 1561 quadratics and 2038 cubics -- and checks the norm bound, the `rho`
bound, the ceiling, the hard slice, and the degree-two identity `alpha|beta| = |b|`.  Two things
the numerics add to the Lean:

* **the bound is sharp, and sharp at both degrees.**  `min A(alpha) log2 alpha` is exactly `2`
  over the quadratics and exactly `3` over the cubics, so no smaller `d` can be put in the
  ceiling.  Equality holds exactly at the units: quadratic units have `rho = 1/alpha`, and a
  cubic unit with a complex conjugate pair has `|alpha_2| = |alpha_3| = alpha^{-1/2}`, both
  forcing `log(1/rho) = log alpha/(d-1)` on the nose.
* **the smallest `alpha` where Route A fires is the capstone.**  Over the quadratics it is
  `alpha = 4.2360679775 = 2+sqrt5`, root of `X^2-4X-1`; over the cubics `8.0155643786`, root of
  `X^3-8X^2-1`.  Both sit just above `2^d`, so the ceiling is not slack in practice either.

One precision trap, the same one as everywhere in this root: `np.roots` on a cubic is good to
about `1e-8`, which reports `min A log2 alpha` over the cubics as `2.9999999985` and makes the
sharpness claim untestable.  The script filters with float64 and then **re-solves every retained
polynomial with `mpmath.polyroots` at 30 digits**, where the minimum is `3` to all digits shown.
The same refinement is what makes the `rho = 1/alpha`-iff-unit dichotomy decidable at all.

### The Hausdorff floor: `Hausdorff.lean` (2026-08-26)

Mathlib has no iterated function systems, so it has no Hutchinson/Moran formula and no
ready-made measure on a self-similar set.  What it *does* have is the sharp form of the mass
distribution principle, `Measure.le_hausdorffMeasure`: a measure satisfying
`mu s <= (diam s)^d` on small sets is below the `d`-dimensional Hausdorff measure.  A real
Frostman estimate always carries a constant, and reinstating it is one line -- apply the sharp
form to `C^{-1} . mu`.  That is all of
`ForMathlib/MeasureTheory/MassDistribution.lean` (`smul_le_hausdorffMeasure_of_frostman`,
`le_dimH_of_frostman`).

The measure has to be built here, and it is the obvious one.  `coinMeasure` is the fair coin
product `Measure.infinitePi` on `{0,1}^N`, with `coinMeasure_agreeSet`: a depth-`M` cylinder
has mass `2^{-M}`.  `codingMeasure alpha` is its push-forward by `pi`, a probability measure
carried by `C(alpha)` (`codingMeasure_cantorSet` = 1, which is the nonvanishing the principle
needs).

**`preimage_subset_agreeSet` is Lemma 1(iv) read backwards**, and it is the whole idea: if a
set has diameter below `g alpha^{-M}` then *all* its `pi`-preimages agree on `[0,M)`, because
two words that first differ at `k < M` have `pi`-values at least `g alpha^{-k} >= g alpha^{-M}`
apart.  So such a set meets one depth-`M` cylinder and has `codingMeasure` at most `2^{-M}`.
An arbitrary set is passed through the closed ball it sits in
(`codingMeasure_le_pow_of_ediam`), which costs a factor two in the diameter and nothing else.

`codingMeasure_frostman` then chooses `M` as large as the separation allows -- least `N` with
`g alpha^{-N} <= 2 diam s`, and `M = N-1` -- so that `2^{-M}` and `(diam s)^d` are within a
fixed factor of each other.  The identity that makes them scale alike is
`inv_rpow_logRatio`: **`alpha^{-d} = 1/2` exactly at `d = log2/log alpha`**.  The threshold
`diam s <= g/4` is what guarantees `N >= 1`; a set of diameter *zero* is handled by the same
cylinder bound at every depth, which forces measure zero.

Out comes `le_dimH_cantorSet` and hence `dimH_cantorSet` and
`dimH_eq_upperBoxDim_cantorSet`: `dim_H C(alpha) = dim_B C(alpha) = log2/log alpha` for
`alpha > 2`, which is M1 Lemma 1(iii) in full.  No analogous floor is claimed for `X(alpha)`,
which is not self-similar; there only the ceiling `dimH_confSet_le` holds.

### M1 Obs. 16 -- the mirror, and a correction to (i) (2026-08-26)

Observation 16 explains M0's empirical "`rho >= 1/alpha` with equality iff quadratic unit; the
ladder is quadratic-unit-only".  Part (i) -- the future and past factors of the Bernoulli(1/2)
Weyl limit converge to the same `L`, so the plateau is `L^2` -- is an observation supported by
numerics; part (ii) is its mechanism, and (ii) is what `Plateau.lean` proves.

`Ladder.lean` (M7) already showed the weight profile of a ladder mode `h_k` is `O(1)` only in
two bands, at future depth `~ k` and past depth `~ k`.  `Plateau.lean` identifies the **shape**
of each band, exactly rather than up to a constant.  Division-free Binet
`(alpha-beta) h_k = f_0 alpha^k - e_0 beta^k` -- two lines from `lad_step` and its conjugate
`lad_conj_step`, with `f_0 = h_1 - beta h_0` -- gives

    future weight at depth j  =  A alpha^{k-j}   up to  |e_0|(alpha-1) rho^k / ((alpha-beta) alpha^j)
    past weight   at depth m  =  (-b)^m B alpha^{k-m}  up to  |e_0||beta-1| rho^{k+m} / (alpha-beta)

with `A = f_0(alpha-1)/(alpha-beta)`, `B = f_0(beta-1)/(alpha-beta)`.  Both are **equalities**.

**The mirror is then one line.**  `abs_shapePast_profile`: the past profile equals the future
profile times `|b|^d * |beta-1|/(alpha-1)`, at every rung and every depth.  So the two profiles
are one shape read in opposite directions **exactly** when `|b| = 1`; off a unit the factor
`|b|^d` grows and they part company exponentially in the depth.  The whole dichotomy comes off
the single identity `alpha rho = |b|` (`abs_beta_eq_inv_alpha_iff`, `inv_alpha_lt_abs_beta`).
The note's own reflection identity is `lad_mul_beta_pow`, division-free, and
`abs_lad_mul_beta_pow_sub_int` is its consequence at a unit -- `(-b)^m h_{k-m}` is an *integer*,
which is why the past coordinate is near-integral exactly as far as the future one is.

**Two corrections to (i), both checked numerically and both now proved or provable.**

* At a quadratic unit of **norm +1 there is no limit to take**.  M5 Thm 7 (`past_eq_future`)
  says `c_m = -(alpha-1)/alpha^{m+1}` *exactly*, so the past weight of *any* mode at depth `m`
  is minus its future weight at depth `m+1` (`past_weight_eq_neg_future_weight`): the two
  one-sided products are equal **term by term**, at every rung.  The plateau is a square for an
  algebraic reason, not an asymptotic one.  Correspondingly `B = -A/alpha`.
* At a quadratic unit of **norm -1** a limit is genuinely involved, and it converges at rate
  **`rho^{2k}`** -- `abs_future_band` and `abs_past_band` put each band within
  `C rho^{2k}/alpha^{offset}` of a *fixed* shape.  The note states no rate.  Checked at four
  norm-(-1) units (`1+sqrt2`, `(3+sqrt13)/2`, `(5+sqrt29)/2`, the golden mean): the four-step
  ratio of `|future - past|` is `rho^8` to four decimals in every case.

So the note's quoted agreement "to `3e-15` by `k = 20`" describes the norm-(-1) case; at
`2+sqrt3` (norm +1) the agreement is exact at every `k`.

**Operational.**  `m1_obs16.py` runs in mpmath at precision set from `k`, with exact integer
ladders.  In `float64` the check dies at `k ~ 16/log10(alpha)` and returns plausible-looking
garbage -- the note's own F10 trap, and the reason the first pass of this check appeared to show
the plateau breaking down at `k = 22` at `2+sqrt3`.  9/9 cases pass, including two non-units
where the past factor collapses to `0` while the future one settles.

Part (i) itself -- convergence of the products -- is `WeylProduct.lean`, the next section; it
turns the second bullet above into a theorem and shows the first is the whole story at norm `+1`.

### M1 Obs. 16(i) -- the products, and why (i) is false as stated (2026-08-26)

`Plateau.lean` left (i) open: it proved the *profiles*, not the *products*.  `WeylProduct.lean`
supplies the products.  Write `ncos x = |cos(pi x)|` for the modulus of the Bernoulli(1/2)
characteristic function; the two one-sided factors of the Erdos product `G_{1/2}(h)` of M5 are

    futProd h  = prod_{j>=1} ncos (h (alpha-1) alpha^-j)
    pastProd h = prod_{m>=0} ncos (h c_m),   c_m = (beta-1) beta^m
    weylProd h = futProd h * pastProd h

**They converge.**  `multipliable_futProd`, `multipliable_pastProd`: both are `Multipliable` for
*every* real mode `h`, because the arguments decay geometrically and `ncos` is `pi`-Lipschitz with
`ncos N = 1` at every integer, so `sum |factor - 1| < infinity`.  (Non-vanishing of the individual
factors was already `Bernoulli.lean`; multipliability is what was missing.)

**Each factor converges along a ladder, to an explicit limit.**  With `A = shapeFut` and
`B = shapePast` the two profiles of `Plateau.lean`, and

    biProd x  =  prod_{n in Z} ncos (x alpha^n)

(the **bi-infinite** Erdos product of amplitude `x`, written in Lean as its two one-sided halves),

    tendsto_futProd  :  futProd h_k  ->  biProd A     -- every quadratic alpha, unit or not
    tendsto_pastProd :  pastProd h_k ->  biProd B     -- needs |b| = 1
    tendsto_weylProd :  weylProd h_k ->  biProd A * biProd B

The future statement being unconditional *is* the note's "the future factor still settles" at a
non-unit; and `m1_obs16i.py` checks that off a unit the past factor really does collapse to `0`
while `biProd B` does not, so the hypothesis is necessary, not an artefact.

**The device is two lines.**  Every factor of `futProd h_k` differs from the corresponding factor
of the shape product by at most `pi` times the profile error of `abs_future_sub_shape`, and
`|prod f - prod g| <= sum |f - g|` for factors in `[0,1]` (`abs_prod_sub_prod_le`, and its `tprod`
form).  Those errors sum geometrically:

    |futProd h_k - shapeProd A k|   <=  pi |e_0| rho^k / (alpha - beta)
    |pastProd h_k - shapeProd B (k+1)| <= pi |e_0| |beta-1| rho^k / ((alpha-beta)(1-rho))

and `shapeProd x k = prod_{j>=1} ncos (x alpha^{k-j})` is exactly a one-sided truncation of
`biProd x`, taken further and further out as `k` grows (`shapeProd_succ`,
`shapeProd_eq_prod_range`, `tendsto_shapeProd`).  So no shifting-window epsilon/3 argument is
needed anywhere.  The bound `rho^k` is not sharp -- the observed rate is `rho^{2k}`, because `ncos`
is quadratically flat at its maxima -- but it is what the limit needs, and the `rho^{2k}` rate is
`abs_future_band` of `Plateau.lean`, confirmed numerically here (measured exponent `2.00 +- 0.03`).

**The correction: (i) as stated is FALSE for a general ladder.**  Unwinding the limits,

    futProd h_k -> biProd(lambda (alpha-1)),    pastProd h_k -> biProd(lambda' (alpha-1))

where `lambda` is the codifferent parameter of the ladder (M1 Prop. 15) and `lambda'` its
conjugate.  The second identification is `biProd_shapePast_eq_shapeFutC`, and it is the real
content of the "mirror": at a unit `beta^n = +- alpha^-n`, and a shape plus its algebraic
conjugate is always an integer, so `biProd` simply does not care which way it is read
(`biProd_eq_of_reflect`, off three trace identities `shapeFut_pow_add`, `shapePast_pow_add`,
`shapeFutC_pow_add`, each an instance of division-free Binet read backwards).

So the two limits agree **iff** `biProd(lambda(alpha-1)) = biProd(lambda'(alpha-1))`, for which
`lambda' = +- alpha^s lambda` suffices -- `biProd` is invariant under negation and under
multiplying the amplitude by `alpha` (`biProd_neg`, `biProd_mul_alpha`, `biProd_mul_pow`), which
gives `biProd_shapePast_eq_of_pow`.  Its `s = 0` case is `e_0 = -f_0`, equivalently the integer
condition `2 h_1 = a h_0` (`ladE_eq_neg_ladF_iff`), equivalently `lambda` **rational** -- the
ladder a rational multiple of the trace ladder.  Both of the note's numerical witnesses
(`lambda = 1` and `lambda = 1/2` at `1+sqrt2`) satisfy it, which is why the note did not see the
failure.  It fails in general:

| `alpha` | ladder | `lambda'/lambda` | future limit | past limit |
|---|---|---|---|---|
| `(3+sqrt13)/2` | `2, 3, 11, 36, 119, ...` (trace) | `1` | `0.0781588238` | `0.0781588238` |
| `(3+sqrt13)/2` | `1, 4, 13, 43, 142, ...` | `-0.16204...` | **`0.4004074010`** | **`0.0126597907`** |

Both settled to 16 digits by `k = 36`, and `-0.16204...` is not `+- alpha^s`.  So the plateau is
`L^2` for the trace ladder and for every rational multiple of it, and a product of two *different*
one-sided constants otherwise; Route E's infinite-product bound still only has to reach one of
them, but which one depends on the mode.

**Norm `+1` is not a limit statement at all.**  `pastProd_eq_futProd`: when `b = -1`, M5 Thm 7
makes `c_m = -(alpha-1)/alpha^{m+1}` exactly, so the two products are equal factor by factor for
*every* mode `h` -- so `weylProd h = futProd h ^ 2` at every rung, with no ladder and no limit
(`weylProd_eq_sq`, and `weylProd_eq_sq_twoAddSqrt3` at `2+sqrt3`).  That is why the `2+sqrt3`
rows above agree even though `lambda' /= lambda` there.

**Operational.**  `m1_obs16i.py`, 8/8 verdicts, mpmath at precision set from `k` (12 cases: three
norm-`-1` units, one golden, three ladders at `2+sqrt3`, two non-units).  The tolerance has to be
measured in `rho^{2 KMAX}`, not in machine epsilon -- the products settle at exactly that rate, so
a fixed `1e-30` threshold fails the golden mean at `k = 40` for a wholly uninteresting reason.

### M1 Prop. 15 -- the ladder is the whole codifferent (2026-08-26)

Proposition 15 answers M0's open normalisation question -- is the biased-mode ladder
`h_k = Tr(alpha^k)` or its half? -- with "neither is canonical, the ladder is the whole
module", and then identifies the module: `d^-1 = f'(alpha)^-1 Z[alpha]`, the same module that
indexes the characters of the Minkowski torus in section 4.1.  The keyfact box after it prices
the answer: at `1 + sqrt 2` the half-ladder beats the trace ladder by a factor **452**, so a
search that had tested only `Tr(alpha^k)` would have reported the wrong `alpha` as the hard
case.

The mathematics is `ForMathlib/NumberTheory/TraceLadder.lean`, at the note's own generality
(`alpha` an algebraic integer generating a number field -- the note works in `K_f`).  Three
inputs, proved apart because they are genuinely different:

* **the recurrence** holds for *every* `lambda`, integrality nowhere in sight.  The note says
  "since each `alpha_j^k` does"; that routes through a splitting field and is not needed --
  `sum_i f_i alpha^i = f(alpha) = 0` in `K_f` itself, and the trace is linear.  Five lines
  (`isRecSeq_ladder`), and no conjugates anywhere in the file;
* **integrality** is where the codifferent enters, and it is a tautology once one knows `Z[alpha]`
  is spanned by the powers of `alpha`: `Tr(lambda alpha^k) in Z` for every `k` IS
  `Tr(lambda Z[alpha]) subset Z` (`mem_codiff_iff`).  The note's "iff for `0 <= k <= d-1`" is the
  forward propagation of integrality along a *monic* recurrence, isolated as
  `IsRecSeq.mem_of_init_mem` -- stated for an arbitrary Z-submodule, which is what makes it
  reusable;
* **surjectivity** is nondegeneracy of the trace form: `lambda |-> (Tr(lambda alpha^i))_{i<d}` is
  injective between two `d`-dimensional Q-spaces, so onto (`exists_ladder_eq_init`).  Dimension
  count needs `[L:Q] = deg minpoly_Z(alpha)` (`finrank_eq_natDegree`).

**Euler's identity is free.**  `d^-1 = f'(alpha)^-1 Z[alpha]` -- which the note derives from
`Tr(alpha^i/f'(alpha)) = delta_{i,d-1}`, and which is the only part of section 6 that is not
elementary -- is already in Mathlib as `traceForm_dualSubmodule_adjoin`, needing only
`A = Z, K = Q, L = K_f`.  It is recorded (`codifferent_eq_smul_adjoin`), not reproved.  That was
the half this root had listed as blocked.

**The degree-two bridge** is what connects Proposition 15 to the machinery that consumes it.
`QuadSetup.charPoly = X^2 - aX - b`, and `recModule_eq_range_lad` says the ladders
`lad P h_0 h_1` of `Ladder.lean` (M7) are *exactly* the integer solutions -- every solution is
the one started at its own first two terms.  With Proposition 15 that gives
`lad_iff_trace_ladder`: for any root `alpha` of `X^2 - aX - b` generating a quadratic field, a
sequence is an M7 ladder iff it is `Tr(lambda alpha^k)` for some `lambda` in the codifferent.
That is the licence for M7's search over `lambda in d^-1`, which `Ladder.lean` had only asserted
in prose.

**Implementation note worth keeping.**  `IsRecSeq` is stated for sequences in an arbitrary
additive group, so the Z-valued and Q-valued recurrences are the *same* definition and
`IsRecSeq.map` / `IsRecSeq.of_map` move between them along `Z -> Q`.  The integer sequence
underlying an integer-valued rational sequence is extracted canonically as `(u k).num`, so the
bundled isomorphisms involve **no choice**.

### M1 Prop. 14 -- admissibility, the licence for the citations (2026-08-26)

Proposition 14 is the smallest statement in the note and the one that everything cited from
[BM86]/[BM85] rests on: those papers are written for the `theta`-shift, and nothing entitles
one to read `C(alpha)` inside it until one knows that `{0,1}^N` is a subshift of the
`alpha`-shift.  The note calls it "ours (trivially)" and observes that it is *nowhere stated*
in the eight batch-1 papers.

The note argues by **Parry's criterion** -- `a` is admissible iff `sigma^k a <_lex d*(1,alpha)`
for every `k`, and the comparison is decided at the first letter because `d*(1,alpha)` starts
with `floor(alpha) >= 2` while every letter of a `{0,1}`-word is `0` or `1`.  That route wants
the quasi-greedy expansion `d*(1,alpha)` and Parry's theorem, neither of which exists in
Mathlib and both of which are real work.

`Admissible.lean` takes the **definition** instead, which turns out to be cheaper *and*
stronger.  `IsAdmissible alpha a` says `a` is the greedy Renyi-Parry `alpha`-expansion of a
point of `[0,1)`; `greedyExp_boolVal` exhibits the point:

    greedyExp alpha (boolVal alpha eps) = eps,   boolVal alpha eps = pi(eps)/(alpha-1)

So one does not merely learn that `{0,1}`-words are admissible -- one learns *which* points
they expand, and the note's "up to the `(alpha-1)` normalisation" stops being a caveat and
becomes an identity (`piVal_eq_boolVal`).  The proof is `alpha_mul_boolVal` (M1 Lemma 1(v)
with the `(alpha-1)` divided out) plus one floor computation, iterated.

**Where `alpha > 2` enters is a single inequality, and it is sharp.**  The algorithm
reproduces the word iff every tail value stays inside `[0,1)`, and the largest tail value is
`boolVal alpha 1^inf = (alpha-1)^{-1}`, which is `< 1` **iff** `alpha > 2`
(`boolVal_const_true_lt_one_iff`).  At `alpha = 2` the word `1^inf` has value `1`, leaves the
domain, and the `{0,1}`-coding stops being a restriction of the `alpha`-expansion coding --
exactly the note's "what breaks at `alpha <= 2`" for use **U3**.

The converse direction is `greedy_tsum`: on `[0,1)` the greedy algorithm loses nothing, a
point being the sum of its own expansion (`greedy_partial` plus the squeeze
`0 <= alpha^{-n} T^n x <= alpha^{-n}`).  Hence `greedyExp alpha` is injective there
(`injOn_greedyExp`), and hence the note's "hence" is an **equality** and not an inclusion:

    cantorSet_eq_image_boolCoded :  C(alpha) = (alpha-1) . B(alpha)

with `B(alpha)` the set of points of `[0,1)` whose `alpha`-expansion is a `{0,1}`-word.  That
is the sentence the citations actually need.

`greedyDigit_one`, `two_le_floor`, `two_le_floor_sub_one` and `bitZ_lt_floor` record the
note's own first-letter count -- `d(1,alpha)` begins with `floor(alpha) >= 2`, the integer
case `d*(1,alpha) = (floor(alpha)-1)^inf` still has its letter `>= 2`, every letter of a
`{0,1}`-word is `< 2`.  They are not used above; they are what a reader holding the note next
to the file will look for.

### M1 Lemma 1 -- the coding IFS, the gap, the homeomorphism, the conjugacy (2026-08-25)

`Cantor.lean` is where `alpha > 2` first enters the problem.  `C(alpha)` is the attractor of
the IFS `f_0 x = x/alpha`, `f_1 x = (x + alpha - 1)/alpha` on `[0,1]` (`ifsMap`), and
`piVal_eq_ifsMap` is the self-similarity `pi(eps) = f_{eps_0}(pi(sigma eps))` -- M1 Lemma 1(i)
and (v) in the only form the separation argument needs.

**(ii) the gap.**  `image_ifsMap_false` and `image_ifsMap_true` compute the two branch images
as `[0, 1/alpha]` and `[(alpha-1)/alpha, 1]`; `sub_inv_eq_gap` says the two are separated by
exactly `g = (alpha-2)/alpha` (`gap`), and `gap_pos_iff` that `g > 0` **iff** `alpha > 2`.
That is use U1 of the hypothesis in the note's Section 5, isolated as one iff.
`disjoint_image_ifsMap` is the disjointness itself, and `gap_le_piVal_sub` its digit form:
a word beginning with `1` and a word beginning with `0` have `pi`-values at least `g` apart.
The constant is sharp -- at `alpha = 3`, `pi(1000...) - pi(0111...) = 2/3 - 1/3 = g`.

**(iv) strong separation.**  `piVal_sub_eq_pow_mul`: words agreeing on `[0, k)` have
`pi(eps) - pi(eps') = alpha^-k (pi(sigma^k eps) - pi(sigma^k eps'))`, the first `k` terms
cancelling *exactly* (induction on the backward recursion `alpha t_n = (alpha-1) eps_n +
t_{n+1}` of `Defs.lean`, no tail estimate).  Composing with (ii) gives
`gap_mul_le_abs_piVal_sub`: if the two words first differ at letter `k` then
`|pi(eps) - pi(eps')| >= g alpha^-k`.  This is the input to M1 Prop. 12's entropy lower
bound and to the M4 gap certificates.

Both parts are proved for every `alpha > 1`; `alpha > 2` enters only through `0 < gap alpha`,
which is where the bound acquires content.  `QuadSetup` deliberately does not assume
`alpha > 2`, so `gap` is carried as a quantity, not as a standing hypothesis.  std3, no
`sorry`, no cited axiom.

**(i) the attractor, and the extreme values.**  `consW` prefixes a letter and `piVal_consW`
says that is applying a branch, `pi(b :: delta) = f_b(pi(delta))`; with the self-similarity
that gives `cantorSet_eq_union`, `C(alpha) = f_0(C(alpha)) union f_1(C(alpha))`.  The extreme
values are attained at the constant words: `piVal_const_false` and `piVal_const_true` (the
latter is `(alpha-1) * (alpha-1)^-1` through `tsum_inv_pow_succ`, moved into `Defs.lean` for
it), whence `isLeast_cantorSet` and `isGreatest_cantorSet`.

**(iii) the homeomorphism, and Lebesgue-nullity.**  `injective_piVal` reads straight off (iv)
at `Nat.find` of the first index where two words differ, since `g alpha^-k > 0`.  With
`continuous_piVal` and compactness of `{0,1}^N` that is `piHomeomorph`, a continuous bijection
from a compact space to a Hausdorff one: **`pi : {0,1}^N ~= C(alpha)`**, which with (v) below
is the topological conjugacy the note asserts.  `volume_cantorSet` is `Leb(C(alpha)) = 0`.
The note gets that from `dim_H C(alpha) = log2/log alpha < 1`; **no dimension theory is
needed**.  By (i) and (ii) `C(alpha)` is the *disjoint* union of two copies of itself scaled
by `alpha^-1` (`volume_image_ifsMap`), so its measure `v` obeys `v = 2 alpha^-1 v` with
`2 alpha^-1 < 1` and `v < infinity`, forcing `v = 0`.

**(v) the conjugacy.**  `tauMap alpha x = alpha x - (alpha-1) eps_1(x)`, the first digit read
off `x` by the threshold `(alpha-1)/alpha` -- well defined on `C(alpha)` exactly because of
(ii).  `tauMap_piVal` is `pi . sigma = tau_alpha . pi` and `tauMap_mapsTo` that `tau_alpha`
preserves `C(alpha)`.

The dimension *values* of (iii), `dim_H C(alpha) = dim_B C(alpha) = log 2 / log alpha`, are
not here but in `BoxDim.lean` and `Hausdorff.lean` (both below), where they are proved in
full -- the box-dimension equality from strong separation, the Hausdorff one from a coin
measure built by hand, Mathlib having no self-similar-set (Hutchinson) formula.

### M1 Prop. 8(i) -- the ergodic realization converse (2026-08-25)

`Realization.lean` proves the converse of the master target for an **ergodic** invariant
measure: for every ergodic `sigma`-invariant Borel probability `mu` on `{0,1}^Z` there is a
`xi in C(alpha)` whose empirical measures `lambda_N` converge weak-* to `F_* mu`
(`exists_tendsto_map_of_ergodic`); `exists_tendsto_haarT_of_ergodic` is the case
`F_* mu = Leb` that M1 Cor. 9 consumes.

This is the one file of the root that consumes something outside Mathlib: **Birkhoff's
pointwise ergodic theorem**, vendored as `lean_lib BirkhoffErgodicThm` (Apache-2.0, a port of
`lua-vr/pointwise-birkhoff` by Lua V. R., Oliver Butterley and Pietro Monticone; Mathlib
carries only the mean/von Neumann theorem).  The port is sorry-free and std3, so no axiom is
added.  Three steps:

* `tendsto_birkhoffAverage_of_ergodic` -- the port returns `invCondexp mu f phi =
  mu[phi | invariants f]`; ergodicity collapses that to a constant (Mathlib's
  `PreErgodic.ae_eq_const_of_ae_eq_comp`, the invariant `sigma`-algebra being `mu`-trivial),
  and the constant is `int phi dmu` because conditional expectation preserves the integral.
* the **countable** family of test functions: `C(T, R)` is separable, so one `mu`-full set of
  generic `omega` serves every `G` at once (`ae_ball_iff`), and
  `tendsto_of_dense_of_tendsto_integral` upgrades weak-* convergence from a dense family to
  all of `T ->b R` by the usual `3 epsilon`.
* the **padding estimate** `abs_fRaw_sub_padZ_le`.  Replacing `omega` by its own future
  padded with zeros leaves every `futures (sigma^n omega)` unchanged and moves only the far
  past of the window, so `|F(sigma^n omega~) - F(sigma^n omega)| <= (1+|beta|)|beta|^n /
  (1-|beta|)`, and Cesaro means do not see it (`tendsto_cesaro_sub_of_dist`, uniform
  continuity on the compact circle plus `Filter.Tendsto.cesaro`).  The note argues this with
  the shift metric `2^-n`; here it is the window bound of `Factor.lean`, which is sharper and
  already available.

std3, no `sorry`, no cited axiom.  What is **not** here: the intermediate `nu_N -> mu` on
the shift space itself.  That needs the modulus "words agreeing on a long central block have
close `phi`-values" for *every* `phi in C({0,1}^Z, R)`, a point-set fact about the product
topology with no Mathlib support -- whereas `F`'s own modulus, which is all the `lambda_N`
statement needs, is already proved.  Nothing downstream uses the stronger form.  **Prop.
8(ii)**, the non-ergodic case, is `Saturation.lean` (see below); the ergodic case does *not*
imply it, since `F_* mu = Leb` need not descend to the ergodic components of `mu`.

**The converse bridge, and M1 Cor. 9 on the ergodic class.**
`equidistributed_of_tendsto_emp` is the converse of `tendsto_emp_of_equidistributed`: weak-*
convergence `lambda_N -> Leb` *is* uniform distribution in the counting sense of
`IsEquidistributedModuloOne`.  The cheap route is not portmanteau on arcs but Weyl: weak-*
convergence contains the vanishing of every non-trivial Weyl sum
(`weylCriterion_of_tendsto_emp`, two real characters as test functions), and the converse half
of Weyl's criterion is already proved in this repository -- the `circBump` sandwich of
`ForMathlib/Analysis/Equidistribution/AddCircleWeyl.lean`, carried out in
`Bertin.uniformlyDistributedModOne_of_weylCriterion`, plus
`Bertin.uniformlyDistributedModOne_iff_isEquidistributedModuloOne`.  Both are axiom-free, so
the bridge is std3 as well.  Feeding it `exists_tendsto_haarT_of_ergodic` gives
`exists_equidistributed_of_ergodic`: **an ergodic `mu` with `F_* mu = Leb` makes 10.61 fail at
`alpha`**.

So M1 Cor. 9 is complete on the ergodic class.  Its two halves there are
`exists_equidistributed_of_ergodic` (`exists ergodic mu, F_* mu = Leb  =>  10.61 fails`) and
`exists_invariant_measure_of_equidistributed` (`10.61 fails  =>  exists invariant mu,
F_* mu = Leb`).  Ergodic decomposition does **not** close the gap between "ergodic" and
"invariant": `Leb = int F_* nu_x dmu(x)` does not force any component `nu_x` to push forward
to `Leb`, Lebesgue measure being an average of non-uniform measures.  What closes it is
Prop. 8(ii) itself -- saturation of the full shift -- and nothing weaker.  That is the next
section.

### M1 Prop. 8(ii) -- saturation, and Cor. 9 as an equivalence (2026-08-25)

Lean: **`BB61/Words.lean`**, **`BB61/MeanSelect.lean`**, **`BB61/Saturation.lean`**
(std3, no `sorry`, no cited axiom).

`exists_tendsto_map_of_invariant`: for **every** `sigma`-invariant Borel probability measure
`mu` on `{0,1}^Z` there is `xi in C(alpha)` with `lambda_N -> F_* mu`.  Hence Cor. 9 as an
*iff* (`equidistributed_iff_exists_invariant`, and `..._measure` unbundled): some `xi in
C(alpha)` has `(xi alpha^n)` u.d. mod 1 **iff** some invariant `mu` has `F_* mu = Leb`.  The
master target of `Invariant.lean` is therefore not merely sufficient -- a counterexample to it
would be a counterexample to 10.61.  `forall_not_equidistributed_iff` is the same statement
read as "10.61 at `alpha` iff no invariant measure has Lebesgue image", and feeding it to
`Certificate.lean` gives M3 Theorem 9 in the note's own form,
`forall_not_equidistributed_iff_exists_trigCertificate`.

**The note cites [BM86] Th. VII or Sigmund's specification argument.  The proof here uses no
ergodic theorem at all** -- neither Birkhoff nor von Neumann, and no ergodic decomposition --
so `Saturation.lean` does not import the vendored port.  Two observations replace it.

*Invariance is a statement about means.*  For invariant `mu` and any observable `phi` the
window average `H_N(omega) = (1/N) sum_{n<N} phi(sigma^n omega)` has `int H_N dmu = int phi
dmu` **exactly**, for every `N`, by invariance alone (`QuadSetup.integral_orbAvg`).  The
target value is a mean, not a limit -- which is precisely what Birkhoff would have been
called for.

*A mean is realized by an equal-weight sample, greedily.*  `MeanSelect.exists_greedy_le`: for
mean-zero bounded observables `g_0, ..., g_{m-1}` there are points `omega_0, omega_1, ...`
with `|(1/q) sum_{l<q} g_i(omega_l)| <= delta` for all `i < m` once `q >= m C^2/delta^2`.  The
proof is one line of geometry: writing `s_q` for the partial-sum vector in `R^m`, mean-zero
gives `int <s_q, g(x)> dmu(x) = 0`, so *some* `x` has `<s_q, g(x)> <= 0`, and picking it makes
`||s_{q+1}||^2 <= ||s_q||^2 + m C^2`; hence `||s_q||^2 <= q m C^2 = o(q^2)`.  No independence,
no product measure, no law of large numbers.

*The word.*  `Words.lean` concatenates the sampled windows.  A `StageData` gives, for each
stage `j`, an atom length `NN j`, an atom count `AA j` and sources `om j l`; stage `j` fills
`[T j, T (j+1))` with `word (T j + NN j * l + r) = om j l (r+1)`.  The offset `r+1` is the one
`padZ` wants, and `agree_shift` is the payoff: for `R + 1 <= r <= NN j - R` the padded staged
word at time `T j + NN j * l + r` and the source at time `r` agree on the whole window
`[-R, R]`, so `Factor.lean`'s modulus applies.  The construction pays exactly `2R` lost
positions per atom.

*The bookkeeping.*  `Saturation.lean` assembles it.  Stage `j` works with the first `j+1` test
functions at accuracy `1/(j+1)`, split evenly between the modulus of continuity, the greedy
sampling error and the window boundary; all stage parameters are functions of `j` alone, so
**no recursion is needed** to define them.  `stage_estimate` bounds every prefix of a stage by
`p * delta_j + K_j`, and `StageData.tendsto_avg_of_stage` turns that into convergence of the
running average: the completed stages form a Toeplitz average of stage averages, and an
incomplete stage is covered by the same bound, so intermediate `N` costs nothing.  The atom
count `AA j` is chosen large enough that the additive `K` of all stages up to `j+1` is
negligible against `T (j+1)` -- again a closed formula in `j`.

What is *not* formalised: the intermediate `nu_N -> mu` on the shift space itself, for the
same reason as in Prop. 8(i) (no cylinder modulus in Mathlib), and nothing downstream needs
it.

### M3 Theorem 12 -- the pressure criterion (2026-08-25)

Lean: **`ForMathlib/Dynamics/TopologicalPressure.lean`** and **`BB61/PressureCriterion.lean`**
(std3, no `sorry`, no cited axiom).

The criterion of M3 sec. 7 is one line of the variational principle, and neither half of it
existed in Lean: Mathlib carries *topological* entropy (`Mathlib/Dynamics/TopologicalEntropy/`)
but no pressure at all, and no measure-theoretic entropy either -- that is
`ForMathlib/Dynamics/KolmogorovSinai.lean`, whose docstring lists the variational principle as
out of scope.  Checked against the Tau Ceti roadmap repository on 2026-08-25: no roadmap, no
open pull request and no registered intention there touches pressure, the variational principle,
topological entropy or symbolic dynamics, so this is not work that will arrive from upstream.

`ForMathlib/Dynamics/TopologicalPressure.lean` supplies the combinatorial half in general form:

* `Dynamics.partitionSum T phi P n` = `sum over cells A of Vee_{i<n} T^{-i}P of exp (sup_A S_n phi)`,
  the partition function, taken in `ENNReal` so that an empty cell weighs `0` and no
  boundedness hypothesis is needed to *state* it;
* `Dynamics.partitionPressure T phi P` = `limsup (1/n) log Z_n`, its exponential growth rate.
  For a symbolic system with `P` the time-zero coordinate partition this is the topological
  pressure -- the quantity `m3_entropy.py` and `m4_lean_cert.py` compute;
* `MeasureTheory.entropyRate_add_integral_le_partitionPressure` -- **the easy (Jensen) half of
  the variational principle**, `h_mu(T,P) + int phi dmu <= P(T,phi,P)`.  No ergodic theorem, no
  compactness, no continuity of the potential: the whole proof is the Gibbs bound
  `sum_i (p_i a_i - p_i log p_i) <= log sum_i exp a_i`
  (`Real.sum_mul_add_negMulLog_le_log_sum_exp`, the summed form of the `log x <= x - 1` lemma
  already in `KolmogorovSinai.lean`) applied to the join and the Birkhoff sum, divided by `n`;
* the calculus: `partitionPressure_zero` (the pressure of `0` is the entropy along `P`),
  `partitionPressure_mono`, `partitionPressure_add_const` (`P(phi + c) = P(phi) + c`), hence the
  sandwich `h_top + inf phi <= P(phi) <= h_top + sup phi`;
* `MeasureTheory.le_integral_of_partitionPressure_le` -- the **pressure sandwich** of M3 Cor. 10,
  `-P(-beta g)/beta <= int g dmu` for every invariant `mu`.  Its companion upper bound is the
  sandwich above, so the bracket has width `h_top/beta`: that is why the Route-D search
  terminates.

`BB61/PressureCriterion.lean` joins that to M1 Cor. 9.  With `coordPartition omega = omega 0`,
`forall_not_equidistributed_of_partitionPressure_lt` says: if a bounded measurable `psi` is
annihilated by every invariant `mu` with `F_* mu = Leb`, those `mu` obey an entropy floor
`h_min`, and `partitionPressure shiftZ psi coordPartition < h_min`, then **no** `xi in C(alpha)`
is u.d. mod 1.  The proof is `h_min <= h_mu(sigma,P) = h_mu(sigma,P) + int psi dmu <= P(psi) <
h_min`, the middle equality being the annihilation and the inequality the Jensen half.

Two inputs stay hypotheses, deliberately.  The floor is M3 Theorem 11, which rests on [BPS99]
and [LY85]; the annihilation is M1's `Phi_h(mu) = 0`, immediate for a trigonometric `psi` and
left open so that the criterion applies verbatim to M4's *bounded Borel* potentials.  The floor
is stated with `entropyRate sigma mu coordPartition`, not `kolmogorovSinai sigma mu`: the two
agree because the coordinate partition generates, but that is the Kolmogorov-Sinai generator
theorem, which is not proved here.  Since the floor is cited either way, the relative form costs
nothing and keeps the file citation-free.

### The transfer bridge and the capstone at `2+sqrt3` (2026-08-25)

Lean: **`ForMathlib/Dynamics/PressureTransfer.lean`**, plus `PathGrowth.detE` and the
`Bool`-alphabet restatement `TwoAddSqrt3.certB` (std3, no `sorry`, no cited axiom).

The step that was left -- identifying the partition function with the path sums of a transfer
operator -- is done, and in general form rather than at `2+sqrt3` only.  A
**`Dynamics.TransferBound T phi P V`** is: a state observable `state : alpha -> V` into a finite
set with `state (T x) = tgt (state x) (P x)` (the state is driven by the partition symbol), and
integer edge weights with `exp (phi x) <= weight (state x) (P x)`.  Then

* `partitionSum_le_of_transferBound`: `Z_n(phi,P) <= sum over q of psum (detE tgt) weight 1 q n`;
* `partitionPressure_le_of_transferBound`: with `PathGrowth`'s vector certificate
  `b (M v) <= a v`, `P(T,phi,P) <= log(a/b)`.

The proof runs on `stateSum`, the partition sum refined by the state: summing over states dominates
`partitionSum`, and each refined sum obeys the transfer recursion, by induction on `n` after
splitting a word of length `n+1` into its first symbol and the rest (`joinIter_succ`,
`sum_pi_fin_succ`).  No analysis anywhere.

`forall_not_equidistributed_of_transferBound` is then the M4 criterion verbatim -- transfer bound,
vector certificate, Lebesgue mean `m`, entropy floor, and `log(a/b) - m < h_min` -- the mean
correction being `partitionPressure_add_const`.  Note the potential is required only to be
**bounded and measurable**: that is exactly M4's observation, and it is what lets the cellwise
constant potentials with rational weights replace M3's Hoelder ones.

`two_add_sqrt3_not_equidistributed_of_window` is the capstone: **every numeric input at
`alpha = 2 + sqrt3` is discharged** (`certB` and `log_rate_lt_floor`, both exact in `Z[sqrt3]`),
and 10.61 at `2+sqrt3` follows from three supplied facts:

1. the **window modelling lemma** -- a state observable recording the `N = M = 3` window, sliding
   under the shift and dominating the cell potential;
2. the **Lebesgue mean**, that `F_* mu = Leb` forces `int g dmu = (1/8) log W`;
3. the **entropy floor**, M3 Theorem 11, cited ([BPS99], [LY85]).

`Window.lean` (next section) discharges 1 and 2.

`2+sqrt3` is the smallest `alpha` of the M0 sweep where Route A is blind (`A(alpha) = 1.0526`), so
this is not reachable by `RouteA.lean`.

### The window modelling lemma, and 10.61 at `2+sqrt3` (2026-08-25)

Lean: **`BB61/Window.lean`** (std3, no `sorry`, no cited axiom).  Data:
**`BB61/m4_window_tables.py`** -> `Window_data.txt`, cross-checked entry by entry against
`m4_lean_cert.json`.

**The observable.**  The transfer operator shifts states *downwards*, so the letter it appends
must be the one the partition reads.  That fixes the bit convention: bit `i` of the window word is
`omega(i-6)`, the state `stateOf omega` is bits `0..5`, and the new letter `omega 0` is bit `6`.
`stateOf_shiftZ` is then the certificate's successor map `tgtB` on the nose, and `wB_eq_wcert`
reads its edge weight off the word.  The window of `note-1061-M3.html` looks `M = 3` letters
*ahead*, so the potential is the cell potential of `F` evaluated three steps in the past
(`back3`); that costs nothing, every measure in sight being shift-invariant.

**The arithmetic.**  With `beta = 2 - sqrt3 = alpha^{-1}`, all seven window weights are
`(1-beta) beta^k`, `k <= 3` -- `-1+sqrt3`, `-5+3sqrt3`, `-19+11sqrt3`, `-71+41sqrt3` -- so the
window value of each of the 128 words is an exact `p + q sqrt3` (`winP`, `winQ`, `winSum_eq`), and
M1 Lemma 6's truncation bound is exact too:

`eps = alpha^{-3} + |beta-1| |beta|^4/(1-|beta|) = (2-sqrt3)^3 + (2-sqrt3)^4 = 123 - 71 sqrt3`.

That needs the **sharp** window constant: `Factor.lean`'s `abs_wVal_sub_le_of_agree` charges
`(1+|beta|)` where `|c_m| = |beta-1| |beta|^m` is exact, and the difference here is the whole
margin (`0.0244` against nearly `0.028`), the cell tables being computed at the former.
`abs_wVal_sub_range` proves the sharp form.

**The cell bound.**  With `L u = floor(8(F~-eps))` and `H u = floor(8(F~+eps))` tabulated, four
facts per word -- `8(F~-eps) >= L`, `8(F~+eps) < H+1`, `L <= H <= L+1` (this is where `16 eps < 1`
enters), and `cw(L mod 8), cw(H mod 8) <= wcert u` -- give `floor(8x) in {L,H}` for every `x`
within `eps` of `F~`, hence `cwZ_floor_le`.  All four run in `Z` by `decide`: comparisons
`0 <= A + B sqrt3` are decided by squaring (`nnneg3`, `pos3`), so `sqrt3` never enters the kernel
computation.  The fourth fact is the definition `wcert u = max(cw lo, cw hi)` that
`m4_lean_cert.py` used to build the transfer weights in the first place -- the certificate and the
model are the same table read twice.

**The mean.**  The potential being a step function makes its Lebesgue mean a finite sum: splitting
`[0,1]` into the eight cells gives `int_0^1 cellPot = (1/8) log W`, and `integral_gWin` transports
it to any `mu` with `F_* mu = Leb` (`back3 . sigma^3 = id`, `map_map`, `integral_map`).

**`two_add_sqrt3_not_equidistributed`**: no point of `C(2+sqrt3)` has `(xi alpha^n)` u.d. mod 1,
**given the entropy floor and nothing else**.  `alpha = 2 + sqrt3` is forced to have trace `4`
(`trace_eq_four`, by irrationality of `sqrt3`), so the conjugate is `2 - sqrt3` and no extra
hypothesis on the `QuadSetup` is needed; `sqrtThree` is the witness and
`cantorSet_two_add_sqrt3_not_equidistributed` states the result at the number itself.

### The cited lane: 10.61 at `2+sqrt3` unconditionally (2026-08-25)

Lean: **`CITED/LedrappierYoung.lean`** (namespace `LY`, one axiom) and **`BB61/Floor.lean`**
(the only consumer in the root).

`LY.entropyRate_floor` is `note-1061-M3.html` Theorem 11 in the quadratic-unit case: a
`sigma`-invariant probability measure on the full 2-shift with `F_* mu = Leb` has
`h_min(alpha) <= entropyRate sigma mu coordPartition`, where
`h_min(alpha) = (1/log alpha + 1/log(1/rho))^{-1}`.  `LY.hMin_eq_of_unit` proves that for a unit
(`alpha beta = -b`, `|b| = 1`, so `rho = 1/alpha`) this is `(1/2) log alpha`, so
`LY.entropyRate_floor_unit` has the shape the capstones consume.

What the citation folds in, beyond the sources: the M1 sec 2/4 coding (`Phi`, the torus
`T^2_Lambda`, `Mbar` an automorphism *because* `alpha` is a unit, `taubar . Phi = F`), ergodic
decomposition and measurability of the Lebesgue decomposition in `e`, Jacobs affinity of entropy,
the factor inequality `h(mu) >= h(lambda)`, and -- **the one fold beyond the note's own
reckoning** -- the Kolmogorov-Sinai generator theorem, since the note's `h(mu)` is
`kolmogorovSinai` while the Lean statement is `entropyRate ... coordPartition`.  The available
Mathlib-side inequality runs the wrong way, so this cannot be discharged; every consumer must keep
the relative spelling.

Sources: **[You82] Thm 4.4** is the one that actually applies (`Mbar` acts on a *two*-dimensional
torus, where Young's formula is an equality); [LY85] II and [BPS99] are the general-dimension
statements the note cites.

`BB61/Floor.lean` then gives `problem_10_61_two_add_sqrt3`: **no point of `C(2+sqrt3)` has
`(xi alpha^n)` u.d. mod 1**, with no hypothesis left.  Trace and norm are both forced by
`alpha = 2 + sqrt3` (`trace_eq_four`, `norm_eq_neg_one`), so `two_add_sqrt3_not_equidistributed_cited`
applies to any `QuadSetup` carrying that root.

## M2 - the Route A theorem (milestone M2 of the plan, discharged 2026-08-24)

Write-up: **`note-1061-M2.html`**. The criterion `A = log2/log(alpha) + log2/log(1/rho) < 1`
proved as an effective theorem (one explicit interval missed by every orbit at every time),
with the normal form `(log2(alpha)-1)(log2(1/rho)-1) > 1`, the ceiling's equality case
(units with equimodular conjugates), and an explicit infinite Pisot-unit family
`X^d - aX^{d-1} - 1` firing in every degree.

| script | what it does |
| --- | --- |
| `m2_verify.py` | one check per numbered result of the note (11 checks: two certified coverings, orbit avoidance, sweeps over all 9287 Pisot of `m0_coverage.json`, 20 family members, three recodings); writes `m2_verify.json` |
| `m2_prop1_lean.py` | the Lean companion of Prop. 1 and Cor. 6 -- see the last section |
| `m2_thm2i_lean.py` | the Lean companion of Thm 2(i) -- see the last section |
| `m2_thm5_lean.py` | the Lean companion of Thm 5 -- see the last section |
| `m2_prop7_lean.py` | the Lean companion of Prop. 7 -- see the last section |
| `m2_prop8_lean.py` | the Lean companion of Prop. 8 -- see the last section |
| `m2_prop9_lean.py` | the Lean companion of Prop. 9 -- see the last section |
| `m3_thm4_lean.py` | the Lean companion of M3 Thm. 4 -- see the last section |
| `m3_cor13_lean.py` | the Lean companion of M3 Cor. 13 -- see the last section |
| `m3_cor6_lean.py` | the Lean companion of M3 Cor. 6 -- see the last section |
| `m3_thm78_lean.py` | the Lean companion of M3 Thms 7-8 -- see the last section |
| `m3_prop1_lean.py` | the Lean companion of M3 Prop. 1 -- see the last section |

Proposition 1 and Corollary 6 are formalised in `RouteANormalForm.lean`, Theorem 2(i) in
`RouteADepth.lean`, Theorem 5 in `RouteAFamily.lean`, Proposition 7 in `WindowDiam.lean` and
Proposition 8 in `BlockRecoding.lean` and Proposition 9 in `Raster.lean` +
`GapSqrtThree.lean`; see the six `M2 ... in Lean` sections below.  **M2 is now fully
formalised**, and the last of the six carries a result the milestone did not ask for:
Problem 10.61 at `2 + √3` with no citation.

## M3 - Route B, audited and replaced (milestone M3 of the plan, discharged 2026-08-24)

Write-up: **`note-1061-M3.html`**.  Verdict: **Route B's stated deliverable is refuted**
and replaced.  The three moves are misstated (Meyer), circular (transport) and vacuous
(`Haar(T_K) < 1` is always 1), and the repaired kernel criterion **collapses onto Route D**
-- non-integer frequencies are inert.  At `1+sqrt2`, `(3+sqrt5)/2` and `(3+sqrt13)/2` there
are invariant measures killing the **first 256 Fourier modes**, so no certificate of degree
<= 256 exists there and the constant `c(alpha)` of the X5 lane is exactly **0**.

What replaces it: the past drops out (`lambda-hat(h) = lim_m nu-hat(h Tr(alpha^m))`, so 10.61
is a statement about `T`-invariant measures on `C(alpha)` alone); Route D is **complete**, so
10.61 at a fixed alpha is `Sigma_1`; and a new criterion containing Routes A, B and D,

        P( Re sum_h a_h e(h F) )  <  h_min(alpha) = (1/log alpha + 1/log(1/rho))^{-1}

(`a = 0` is exactly Route A; `h_min -> 0` is exactly Route B/D).  It fires at `2+sqrt3` with
one cosine: `psi = -(9/4) cos(2 pi F)` has pressure `0.5102 < 0.6585 = h_min`.

Coverage at `H <= 8` over the 42 candidates: **ten alpha fire**, all ten decided (five at
`N = M = 8`, five by the second pass at `N = M = 10` or `12`), and all ten also carry an M0
gap certificate -- at this depth the criterion cheapens X8's coverage rather than extending
it.

**Corollary 13 is now in Lean** (`EntropyBudget.lean`, 2026-08-27): the reason the criterion
cheapens rather than extends is an identity, `A(alpha) * h_min(alpha) = log 2`, so the floor
used *alone* is Route A's criterion written in entropy units.  See the last section.

**Theorem 4 is now in Lean too** (`LadderReduction.lean`, 2026-08-27), and with it Corollary 5
at integer frequencies.

**And Corollary 6** (`LadderScope.lean`, 2026-08-27), which is the scope restriction attached
to Theorem 4 and the answer to M1's factor `452`: the half-ladder at `1+sqrt2` is a legal
character and an **inadmissible** proof instrument, because the same condition `2 | a` that
makes `gamma = 1/2` a frequency at all makes the half-ladder odd where every constrained ladder
is even.  See the last section.

**And Theorems 7-8** (`KernelCriterion.lean`, 2026-08-28), the correct B-criterion and the
collapse itself: Route B's kernels and Route D's certificates are the *same object* up to a
change of sign, `Q = c(0) - G`, and **neither Bochner nor Fejer-Riesz is needed** to say so.

**And Proposition 1** (`Tube.lean`, 2026-08-28), which closes the audit of sec. 3: move 3's
criterion `Haar(T_K) < 1` has no instances, because the tube is free in the `tau-bar`
direction and the covering question is therefore about the conjugate coordinate alone.  See
the last section.  What remains unformalised from M3: all of sec. 9.

| script | what it does |
| --- | --- |
| `m3_entropy.py` | the pressure machine: transfer operator of the full 2-shift with the window potential `psi_a(F)`, the rigorous truncation slack `delta`, `h_min`, and the closed-form Bernoulli products.  Rewritten under WP1-WP7 of `plan_BB61_improve_m3_entropy.html`; see the final section |
| `m3_hull.py` | periodic-orbit Fourier vectors `Phi_h`, the convex-hull test (0 inside = no certificate of that degree), witnesses and interior certificates |
| `m3_run_2r3.py` | the `2+sqrt3` certificate at four window depths and at a rational multiplier; writes `m3_2r3.json` |
| `m3_run_hull.py`, `m3_run_hull2.py` | how far the Fourier route is from firing at the four quadratic units; writes `m3_hull.json`, `m3_hull2.json` |
| `m3_run_cert.py` | entropy-certificate coverage sweep over the 42 candidates of `m0_gapsweep.json`; writes `m3_cert.json` |
| `m3_run_cert2.py` | second pass, **run**: recovers `a*` at `N=M=8` and *evaluates* it at `N=M=10,12`, where `delta` has fallen by `rho^2`/`rho^4`; also re-audits pass 1's own certificates with the Collatz-Wielandt bound.  All five pending alpha are certificates; writes `m3_cert2.json` |
| `m3_verify.py` | one check per numbered statement of the note (12 checks); writes `m3_verify.json` |

The pressure computation is one-sided and safe: **any** multiplier vector `a` gives
`E(H) <= P_ub + delta` with `delta = 2 pi (sum_h h |a_h|) * err`, so a certificate is a
finite object `(a, N, M)` -- a single spectral radius plus an explicit tail bound.  Window
`N = M = n` costs `2^{2n}` states; `n = 12` is about 40 s per evaluation, `n = 13` is the
practical ceiling.

`P_ub` is `Window.pressure_ub`: after the power iteration, one more sweep gives the
Collatz-Wielandt bound `lambda <= max_u (A r)_u / r_u`, valid for **any** `r > 0`.  Use it,
not the iterate's own `lam`.  It costs one matrix-vector product and it takes the eigensolver
out of the trusted base -- and it is not academic: pass 1's certificate at
`X^3-7X^2+4X-1` reported `P = -26.37` from a power iteration on an operator whose weights had
underflowed at the edge of the `|a_h| <= 60` box (the tell was a gradient residual of 0.77 at a
claimed optimum).  `pressure_ub` returns `+inf` there.  Warm-started along the mode ladder
inside `|a_h| <= 4` the row fires honestly at `P_ub = -0.2009`.  **Bound the multipliers.**

Because `a` is a *certificate*, not a quantity to recompute, the cheap idiom is: optimise at a
shallow window, then evaluate that same `a` deep.  `P_ub` moves by `<= 1.1e-2` between `n = 8`
and `n = 12`; the depth buys margin through `delta`, not through `P`.

### Two precision traps these scripts exist to avoid

1. Evaluating `{xi alpha^n}` directly needs `n*log10(alpha)` **guard digits**. At
   alpha = 5.37 and n = 300 that is 220; mpmath at a fixed `dps=200` returns a
   uniform-looking sequence of garbage rather than an error.
2. Iterating `Mbar` on the torus in float64 is stable for only about `16/log10(alpha)`
   steps. Reduction mod the lattice bounds the point, not the error. Use the section 2.1
   recursions (`m0_engine.orbit`), which are contracting in both directions.

## M4 - the frontier, extended (milestone M4 of the plan, 2026-08-24)

Write-up: **`note-1061-M4.html`**.  Lean: **`BB61/Pressure.lean`**, **`Bugeaud/Chapter10.lean`**.

M3 left a criterion that fired at ten alpha, *all ten already covered by the X8 gap raster*.
M4 asks whether it can reach anything new, and the answer is yes -- after three fixes, none
of which is about finding better multipliers.

**(a) The potential need not be continuous.**  `F_*mu = Leb` gives `int g(F) dmu = int g dLeb`
for every *bounded Borel* `g`, and the Jensen half of the variational principle never used
continuity either.  So the certificate class is all bounded `g` of Lebesgue mean zero; a
partition of the circle into `B` cells is as legitimate as a Fourier truncation, and has
rational weights.

**(b) The window truncation is an enclosure, not a slack.**  M3 bounded it by
`delta = eps * max|g'|`.  The right object is word-wise: the true `F` lies in
`[F~ - eps, F~ + eps]`, so the edge weight need only dominate the sup of `e^g` over that
interval -- a *pointwise* `eps |g'(F~)|` carried where the Gibbs measure sits.  For a step
potential `max|g'| = infinity` and M3's form is vacuous, while the enclosure is exact.

**(c) The window must be balanced, not square.**  `eps(N,M) = alpha^-M + C_alpha rho^(N+1)/(1-rho)`
has two terms decaying at different rates, so the optimum has `M log alpha ~ (N+1) log(1/rho)`.
For a quadratic unit `rho = 1/alpha` and `N = M` is already optimal -- which is why M3, whose
targets were all quadratic units, never noticed.  In degree 3 the balanced window is worth
5-15x in `eps` **at identical operator size**, and that factor decides the frontier: at
`X^3-4X^2-3X-1`, at the same `2^20` states, the square window `(10,10)` gives `Lambda <= 0.5700`
and fails, the balanced `(13,7)` gives `0.4765` and fires, against a floor of `0.5148`.

The census that makes the question sharp: of the 42 candidates, **22 carry an X8 gap**, Route A
decides 6 and M3 decided 10 -- both subsets of those 22.  So **20 are undecided**, 3 of them
non-units (no entropy floor), leaving **17 live targets**.  That is the M4 sweep.

One hope died: the `c_alpha` price of M3 sec 9.2 is **not** a Fourier artefact.  A partition
potential, whose dual norm is total variation and which ought to see the non-Rajchman bias,
loses to Fourier at matched parameter count in all 25 comparisons over 5 alpha.  The gain is a
second-order (covariance) quantity, so the accounting is `l^2` and Parseval-invariant.

| script | what it does |
| --- | --- |
| `m4_step.py` | the partition-potential machine: cells, exact interval enclosure of the window value, `logspec`/`logspec_ub`, and `E(B)` = max entropy subject to `F_*mu` equidistributing over the cells |
| `m4_fourier.py` | the trigonometric side: `enclose` (word-wise, no delta), `certify`, `search` (minimises the *certifiable* surrogate, not the pressure), and `best_window` (the balanced split) |
| `m4_run_frontier.py` | the sweep over the 17 undecided units: warm-started mode ladder at `L=16`, then certification at `L=20,22,24`; writes `m4_frontier.json` |
| `m4_run_basis.py` | Fourier vs partition at matched free-parameter count; writes `m4_basis.json` |
| `m4_lean_cert.py` | generates and checks the `2+sqrt3` certificate in exact `Z[sqrt3]`; writes `m4_lean_cert.json`, `Pressure_data.txt` |
| `m4_window_tables.py` | the *modelling* tables for `BB61/Window.lean`: the exact `Z[sqrt3]` window value of each of the 128 words and the two integer floors `floor(8(F~ -+ eps))`, cross-checked entry by entry against `m4_lean_cert.json`; writes `Window_data.txt` |
| `m4_verify.py` | one check per numbered statement of the note; writes `m4_verify.json` |

### The Lean certificate

`BB61/Pressure.lean` machine-checks a 64-state pressure certificate at `alpha = 2 + sqrt3` --
the smallest alpha of the sweep where Route A is blind, so `BB61/RouteA.lean` cannot reach it.
Everything is exact: at this alpha

        eps(3,3) = (2-sqrt3)^3 + (2-sqrt3)^4 = (2-sqrt3)^3 (3-sqrt3) = 123 - 71 sqrt3

is itself an algebraic integer and every window value is an exact `A + B sqrt3`, so each of the
128 cell assignments is an integer comparison.  The growth bound consumes the repo's own
`ForMathlib/Combinatorics/PathGrowth.lean` (`psum_le_pow`) -- the Collatz-Wielandt shadow was
already there, written for `Z32/`, so no engine had to be built.  The certificate is
`a = 95035770`, `b = 2^20`, `W = 37279413043200`, and the criterion is one inequality:

        (a/b)^8 < W * alpha^4     i.e.     log(a/b) - (1/8) log W = 0.600637 < 0.658479 = h_min.

std3, no `sorry`, no `native_decide`, no cited axiom.  What is *not* formalised, and is said so
in the file: the identification of `psum` with the partition function of the window potential,
and M3 Theorem 11 (the Ledrappier-Young floor).  `Bugeaud/Chapter10.lean` carries the statement
of Problem 10.61 itself, with the single `sorry` that marks an open problem.

## M5 - Route E, with constants (milestone M5 of the plan, 2026-08-24)

Companion note `note-1061-M5.html`.  The row was re-scoped by the L0 audit to "citation +
the `(alpha-1)`-adapted [BM86] Th. XIV + explicit constants only", and in M1's coordinates
that turns out to be three short arguments:

* **Birkhoff.** If the digit word is generic for *any* shift-invariant `nu`, the orbit
  `({xi alpha^n})` has the limit law `F_* nu-hat` (Thm 1).  Nothing else is needed -- no
  Davenport-Erdos-LeVeque, no second moment, no 0-1 law.
* **Independence.** `omega^+` and `omega^-` occupy disjoint coordinates, so for a
  Bernoulli measure the Fourier coefficients factor completely (Thm 2):

        G_p(h) = prod_{j>=1} phi_p(h(alpha-1)alpha^-j) * prod_{m>=0} phi_p(-h c_m),
        phi_p(x) = (1-p) + p e(x),

  the doubly infinite Erdos product, with `h c_m = -h(alpha-1)alpha^m mod 1`.
* **Arithmetic.** No factor vanishes (Thm 3).  `phi_p(x) = 0` needs `p = 1/2` and
  `x = 1/2 mod 1`; the past factors are safe because `h(alpha-1)alpha^m` is an *algebraic
  integer* and `1/2 + Z` contains none, and the future factors are safe because
  `(alpha-1)/alpha > 1/2` (this is `alpha > 2`, used **exactly once in the whole route**)
  while `(alpha-1)/alpha^j < 1/2` for `j >= 2`.  At `alpha = 2` that first factor *is*
  `cos(pi/2) = 0` -- correctly, since `C(2) = [0,1]` and the coding measure is Lebesgue.

New relative to the literature: the `(alpha-1)` adaptation of [BM86] Th. XIV.1 (flagged
"routine but not in print" by L0 batch 1) and its multiplier version, which [BM97] p. 188
asserts without proof; a **folding theorem** -- at a quadratic unit of *norm +1*,
`c_m = -(alpha-1)alpha^{-m-1}` exactly, so `K = -C(alpha)`, `X(alpha) = (C+C) mod 1` and
`G_p(h)` is a perfect square at every `h` and `p` (this sharpens M1's F9, whose stated
hypothesis "a quadratic unit" was too weak: at norm `-1` the numerator is `alpha+1` and
only the ladder limit folds); and the observation that **any counterexample set is dense**
in `C(alpha)`, the u.d. set being a tail event and `pi` a homeomorphism.

Two plan items are retired.  **X3** (the Kolmogorov 0-1 law): Birkhoff gives the dichotomy
wherever it would, since an invariant event is a tail event.  **X10** (the second moment):
for an ergodic measure it converges to `|G(h)|^2`, the square of Thm 2 -- so it computes
nothing new, and Route **C2**, which L0-5 had already emptied down to X10, closes with it.

Honest ceiling, recorded in the note as Prop. 11-12: M3's entropy floor already subsumes
the Bernoulli case at 5 of the 42 candidates (the quadratic units `> 4`) and on the
low-entropy part of `p` everywhere; and what M5 leaves open is comeager and of full
Hausdorff dimension `log 2 / log alpha`.  **The a.e. statement is an introduction and a
constant, not progress on the core.**

| script | what it does |
| --- | --- |
| `m5_bernoulli.py` | the product `G_p(h)` at 50 digits with a *rigorous* truncation enclosure, the Theorem-3 audits, discrepancy floors, `h_min` and the entropy window |
| `m5_run_bias.py` | the constants at all 42 candidates -> `m5_bias.json` |
| `m5_direct.py` | orbit simulation against the closed form, phase included (48 comparisons at CLT scale) -> `m5_direct.json` |
| `m5_markov.py`, `m5_memory.py` | `G_P(h)` for Markov measures of memory 1 and of any memory `k`, by conditional independence across the origin |
| `m5_run_markov.py`, `m5_run_memory.py`, `m5_run_polish.py`, `m5_run_wide.py` | the memory ladder and its two audits (mode truncation, entropy constraint) |
| `m5_sections.py` | regenerates the note's data sections |
| `m5_verify.py` | one check per numbered statement (21/21 PASS) |

One step past Bernoulli comes free: `omega^+` and `omega^-` are conditionally independent
given the block at the origin, so `G_P(h)` has an exact transfer-matrix form at every
Markov memory `k` (Thm 13).  The ladder `Psi_k = min_P max_h |G_P(h)|` is a finite probe
of the master target -- **but only after two audits, and the naive version fails both**:
the objective must constrain more modes than the chain has parameters (at `k = 4` the
`H = 12` optimum often hides its largest mode at `h ~ 20`), and the measure must satisfy
M3's entropy floor (at `2 + sqrt3` every rung of the naive ladder lies below it).  Audited
at `H = 32` and subject to `h(mu) >= h_min`, the ladder is **flat at `2 + sqrt3`**
(`0.318, 0.305, 0.307, 0.318`) and drops by only `1.2` to `4` elsewhere, essentially all
at `k = 1 -> 2`.  Rule of thumb worth keeping: *minimise against more modes than
parameters and impose the entropy floor, or the number is a property of the search.*

### The Lean core

`BB61/Bernoulli.lean` is arithmetic only and self-contained: the integer pair recursion
`(alpha-1)alpha^m = u_m + v_m alpha` at either root, the trace identity, the exact Pisot
decay `|(alpha-1)alpha^m - T_m| = |beta-1| |beta|^m` (the perturbation bound behind the
tail-event lemma), `cos_future_ne_zero` (where `alpha > 2` is spent), `cos_past_ne_zero`
(the algebraic-integer argument), `past_eq_future` (the folding identity at `b = -1`), and
the instance `twoAddSqrt3` with three corollaries.  std3, no `sorry`, no `native_decide`,
no cited axiom.  Not formalised, and said so in the docstring rather than axiomatised:
convergence of the infinite products, the ergodic-theorem step of Thm 1, and the
`p != 1/2` case.


## M7 - Route C, re-scoped (milestone M7 of the plan, 2026-08-25)

Write-up: **`note-1061-M7.html`**.  Lean: **`BB61/Ladder.lean`**.

Route C's two legs were already closed before this run (L0-5 emptied C1 down to *the
missing converse* of the Hochman-Shmerkin criterion; M5 emptied C2).  What the row still
owned was uniformity in `alpha` and the first case of the master target beyond
independence.  Both are answered, and two structural theorems come out.

**The exact price (`m7_price.py`).**  `E_H(alpha) := inf_a P(psi_a)` equals
`max { h(mu) : mu invariant, Phi_h(mu) = 0 for h <= H }` -- the pressure minimisation of
M3/M4 is a constrained-entropy maximisation, by Sion's minimax theorem, and at the
optimum the equilibrium state *is* the extremal Fourier-flat measure.  Consequences: M3
Thm 12 is complete, not merely sufficient; the degree it needs (`H_ent`) is not the
degree M3 sec 9.1 bounds (`H_flat`); and a failed search proves nothing until it is
paired with a lower bound.

**Lower bounds, hence the first no-go theorems (`m7_run_price.py`).**  Any finite family
of invariant measures lower-bounds `E_H` by one linear program (entropy is affine on the
invariant simplex).  With memory-12 Markov measures -- exact `Phi_h` by M5 Thm 13, made
sparse -- seeded at the optimiser's own Gibbs states, the bracket closes to `1e-5`:
**no trigonometric certificate of degree <= 64 exists at `1+sqrt2`**, and likewise at
`(3+sqrt5)/2` and `(3+sqrt13)/2`.

**The two bands (`m7_ladder.py`).**  By M1 Lemma 2 the weight profile of `h F` is the
single geometric sequence `<h(alpha-1)alpha^{-p}>` over *all* `p` in `Z`.  Along a trace
ladder -- `h_k = Tr(lam alpha^k)`, equivalently any integer solution of the
minimal-polynomial recurrence, `lam` in the inverse different -- that profile is one
fixed shape carried outward: `O(1)` only in two bands at depths `+-k`, exponentially
small in the bulk between.  So `Phi_{h_k}(mu)` is a **correlation at lag `2k`** of two
fixed observables; the lags are lacunary, which is exactly why no ergodic-average
technology reaches the problem.

**The plateau is a theorem, and it is universal.**  For every mixing invariant `mu` the
ladder coefficients converge (in modulus always; in value along each parity class, and
outright iff `N(alpha) = +1`).  At the fair coin the limit is `P(lam)^2`, the square of
an Erdos product over the limit profile -- verified to six digits on ten ladders at three
`alpha`.  And it exists **exactly at quadratic units**: the past band's amplitude is
`sum_j lam_j (alpha_j alpha)^k`, which survives iff `|alpha_j alpha| = 1` for every
conjugate, forcing `d = 2`.  Measured at the cubics: `|alpha_j alpha| = 2.16, 2.34` and
`|Phi_{h_k}|` down to `1e-10`.  This is why `S(H) = sum_{h<=H} |Phi_h|^2` grows like
`log H` at a quadratic unit and *saturates* at a cubic.

**The first case beyond independence (`m7_run_ladder.py`).**  `inf_k Psi_k > 0` iff 10.61
holds at `alpha` (compactness), so uniformity in the memory is the whole problem; at
fixed memory it is finite-dimensional, and `sup_h |Phi_h| >= max_lam |L_lam|` turns it
into a handful of numbers per chain with no `h`-scan.  A multi-start search over memory
`<= 4` at four quadratic units finds no chain killing the ladder limits, and at memory 1
an exhaustive grid puts the minimum at the fair coin itself.  **That half is a search,
not a proof**; a branch-and-bound version at `k <= 3` is a bounded piece of work and is
handed on.

**No uniformity in `alpha` (`m7_alpha2.py`).**  Along the Pisot family `X^{n+1}-2X^n-1`
decreasing to 2, the budget `log 2 - h_min` rises to its maximum while the available bias
collapses: `sup_{h<=4096} |Phi_h(Bern)| = 8.7e-22` already at `alpha = 2.0019`.  Proved
rate at the first mode: `|Phi_1| <= sin(pi(alpha-2)/(2 alpha))`.  Any structural proof of
10.61 must degenerate at 2, and the rate is now measured.

**M4's sweep is completed (`m7_run_sweep.py`).**  The ten `alpha` M4 left, with M4's own
machine and parameters, so the rows are directly comparable.

| script | what it does |
| --- | --- |
| `m7_price.py` | `BlockChain` (exact `Phi_h` and entropy of a memory-`L` Markov measure, sparse), `lp_lower` (the LP of Thm 5), and WP9's steered pool: `lp_bound` (the same LP with its dual and an `l^1` residual), `farkas_direction`, `gibbs_columns`, `cutting_plane_lower` |
| `m7_ladder.py` | ladders from integer seeds, the reduced profile, the limit profile and its Erdos product |
| `m7_run_price.py` | the `E_H` bracket at the hard quadratic units -> `m7_price.json` |
| `m7_run_ladder.py` | the memory ladder of the ladder limits -> `m7_ladder.json` |
| `m7_run_sweep.py` | the ten remaining frontier `alpha` -> `m7_frontier.json` |
| `m7_alpha2.py` | the degeneration at `alpha = 2` -> `m7_alpha2.json` |
| `m7_sections.py` | splices the note's tables from the JSON (idempotent) |
| `m7_verify.py` | 16 checks, one per numbered statement -> `m7_verify.json` |
| `m7_sz_check.py` | L0 batch 7: the five checks against [Ber92] Ch. 15 -> `m7_sz_check.log` |

### L0 batch 7 (Salem-Zygmund), 2026-08-25

Write-up: **`note-1061-L0-batch7.html`**.  Source: `[Ber92]` Ch. 15, book pp. 271-291,
extracted to `SalemZygmundCh.pdf` in the repo root -- read as page images, since the
OCR text layer drops every product and sum.

L0 item (iii) is closed, negatively, and L0 is complete: the `U`-set lane *provably*
cannot contain 10.61.  Meyer's Prop. 15.4.1 is a confinement criterion (`h(t_j E)`
inside a compact `K != G`), sec 15.4.3 verifies its hypothesis with our own
`theta^j E_theta` inside `Lambda_theta + E_theta` -- which is M1 Prop. 4 -- and
properness of `K_theta` costs only Lebesgue-nullity, so the hypothesis holds at every
Pisot `alpha > 2` and is satisfied by any counterexample to 10.61.  Two citations fall
out (M1 sec 4's torus is that section's own construction; Route A is Prop. 15.4.1 at
`R/Z`), and `m7_sz_check.py` V5 identifies `|Phi_h(mu_half)|` with a product of two
classical `L`-measure transforms -- a square when `N(alpha) = +1`, which is M5's
folding theorem.  Senge-Strauss (Thm 15.5.1, 1973) is the earliest off-diagonal
reversal in the audit; its Lemma 15.5.1 is filed as a lead.

### The Lean core

`BB61/Ladder.lean` machine-checks the arithmetic half of the two-band theorem at degree
two, on the existing `QuadSetup`: the ladder `lad`, the one-step identity `lad_step`
(everything follows from it, because `alpha beta = -b`), `lad_pow_sub`, `bulk_future`,
`alpha_mul_abs_beta` (where the unit hypothesis enters, and with it the restriction of
the plateau to degree two), `bulk_past`, and the instance `1, 4, 15, 56, 209` at
`2 + sqrt3`, where the defect is `e_0 = beta` and the dead-zone constant is `< 1`, so the
bound is exactly `(2 - sqrt3)^j`.  std3, no `sorry`, no `native_decide`, no cited axiom.
Not formalised, and said so in the docstring: convergence of the two band products, their
decoupling for a mixing measure, and the limit itself.

## The engine rewrite (`plan_BB61_improve_m3_entropy.html`, WP1-WP9, 2026-08-25)

Plan: **`plan_BB61_improve_m3_entropy.html`**.  Gates: **`m8_gates.py`** -> `m8_gates.json`.
Milestone W4: **`m8_w4.py`** -> `m8_w4.json`, `m8_w4_ext.json`, `m8_w4_g2.json`,
`m8_w4_gates.json`.
Companion: **`plan-BB61-1+sqrt2.html`** (why none of this helps at `1+sqrt2`).

The certificate machine was already *sound* at any degree: `Window.pressure_ub` is a
Collatz-Wielandt bound independent of the eigensolver, and `delta_bound` is the M4 Prop. 3
enclosure.  What it lacked was reach.  An `O(H 2^L)` inner loop priced out `H > 64`, and
`H` is the whole remaining shortfall at the two middle units (M4 sec 8 measures 60 % and
40 % of the entropy budget already spent at `H = 64`).  Nine work packages, none of which
changes the mathematics.

| WP | what changed | file |
| --- | --- | --- |
| 1 | `word`, `tgt`, `qidx`, `sidx` are slices in disguise: the operator step is one fused `(2^(L-1), 2)` reshape, with the same arithmetic in the same order and bitwise-identical output.  They survive as lazy properties only because `m4_step`, `m4_fourier` and `m7_price` still read them | `m3_entropy.py` |
| 2 | the two power iterations are warm-started, and stop on the Collatz-Wielandt bracket rather than on an iterate difference -- the bracket bounds the quantity the certificate actually needs.  `Window.stop = 'vector'` restores the old rule bit for bit | `m3_entropy.py` |
| 3 | `psi_a` depends on the state only through `F` and, the modes being integers, is 1-periodic in it: one `irfft` onto a grid of `G` points plus one gather replaces the mode loop, and **`H` leaves the per-state cost entirely** | `m3_entropy.py` |
| 4 | `Phi_h` is the Fourier transform of a weighted histogram of `F`: one `rfft` returns all `H` coefficients at once, with each mass split linearly between its two neighbouring bins so the error is `O((pi h/G)^2)`.  Gradient only, kept textually apart from the certificate path | `m3_entropy.py` |
| 5 | the grid perturbs the potential by at most `Lip(psi_a)/2G`, and pressure is 1-Lipschitz in the sup norm, so the enclosure absorbs it: `eps = err + 1/(2G)` (`Window.eps`), and `delta_bound` reads `eps`, never `err` | `m3_entropy.py` |
| 6 | `a -> P(psi_a)` is convex with exact gradient `Phi_h(mu_a)`, so no multi-start and the stopping criterion belongs in the objective: the cutting planes are minimised over the box by LP, bracketing the solve from below (`W.last_solve`).  The `cap` box is audited on every run (warns, or raises under `strict_box`).  `E_curve` runs the whole `H`-ladder, each rung warm-started from the last | `m3_entropy.py` |
| 7 | the window is fixed by the multiplier norm `S1 = sum_h h|a_h|` and by nothing else -- not by the mode count, and not by the `log h/h_min` resolution rule, which is weaker at every `H <= 10^3`: `window_eps`, `best_split`, `choose_window`, and `E_curve` choosing each rung's window from the `S1` the previous rung measured (M3's operational lesson (a): the window is chosen after the multiplier) | `m3_entropy.py` |
| 8 | seven gates, run as one script | `m8_gates.py` |
| 9 | the lower-bound side, steered rather than enlarged: `lp_bound` (the LP of M7 Thm 5 with its dual and an `l^1`-penalised residual), `farkas_direction`, `gibbs_columns`, `cutting_plane_lower` | `m7_price.py` |

**Measured** (`alpha = (3+sqrt5)/2`, one `pressure` call, one core):

| L | H | before | after | speedup |
| --- | --- | --- | --- | --- |
| 20 | 64 | 6.76 s | 0.82 s | 8.3x |
| 20 | 256 | 22.96 s | 0.81 s | 28x |
| 22 | 128 | 44.43 s | 3.50 s | 12.7x |
| 22 | 512 | 165.43 s | 3.68 s | **45x** |

The last two rows are the point: the cost is now flat in `H` (3.50 s at `H = 128` against
3.68 s at `H = 512`), so the degree has stopped being the cost driver.  Extrapolated to
the plan's `L = 24, H = 512` row, four days of L-BFGS becomes a couple of hours.  The plan
predicted half an hour; that was optimistic about WP2, and the honest figure is a few
hours.

### WP9: what the steered pool buys

M7 sec 4 has five rows reading "pool too small": `lp_lower` returned infeasible because 0
was not in the convex hull of the pool's `Phi`-vectors, which is a statement about the
pool and not about `alpha`.  Two steering rules, both read off the same LP.  While the
hull misses 0, Farkas gives a separator `c` with `<c, g_j> >= gamma > 0` for every member,
and the window Gibbs measure at `x* - t c` is tilted towards the side the pool is missing.
Once the hull contains 0, the LP dual `(y_0, y)` prices the missing column *exactly*: the
constraint it enforces is `h(nu_j) + <y, g(nu_j)> <= value`, so the column to add is the
maximiser of `h(mu) + int psi_{a(y)} dmu`, which is the definition of `P(psi_{a(y)})` and
whose maximiser is again the window Gibbs measure.

That second rule closes the bracket for nothing: `E_H <= P(psi_{a(y)})` whatever `y` is,
and `E_H >= value` because the LP is a restriction.  It is the M7 Thm 1 saddle walked from
the other side -- WP6 descends to `E_H` in the multipliers, WP9 climbs to it in the
measures.  At `(3+sqrt5)/2, H = 1`, where M7 sec 4 records `E_lb = infeasible` from a
17-vector pool, the steered pool reaches feasibility in two rounds and brackets

    E_1((3+sqrt5)/2) in [0.689241445, 0.689242713],   raw gap 1.3e-06,

against the optimiser's `0.689241479`.  Same at `(3+sqrt13)/2, H = 2`.

### The gates (`m8_gates.py`, 7/7, about four minutes)

| gate | what it demands |
| --- | --- |
| G1 | **bitwise.** `Window` against a naive reference re-implemented in the same file -- four index arrays, the mode loop, the iterate-difference rule -- with `stop='vector'`, `warm=False` and the FFT crossover disabled.  240 comparisons over 4 `alpha`, 3 windows, 5 mode counts.  Not a diff against a saved copy of the old file, which would only prove two copies agree |
| G2 | **the published rows.**  `m3_2r3.json`'s 8 recorded `(P, delta)` pairs at their own windows (worst 1.7e-13); `m4_frontier.json`'s stored certificates re-certified from their own multipliers (0.0e+00); `m4_lean_cert.json`'s integer certificate; every recorded M7 bracket |
| G3 | **the accounting.**  `pressure_ub + delta_bound` encloses the reported pressure everywhere; `eps == err + 1/(2G)` exactly; the WP3 grid deviation is 0.81 of `pi S1/G` and the WP4 coefficient deviation 0.10 of `(pi H/G)^2/2`, both already charged by `delta_bound` |
| G4 | **the box.**  `max_h |a_h| = 2.815` over every stored certificate against those runs' `cap = 8`; a fresh optimum inactive at `cap = 60`; and at `cap = 0.5` the same run reports active, warns, and raises under `strict_box` |
| G5 | **WP6's bracket** is a lower bound: 25 sampled box points and a deeper restart all stay above `lb_box` |
| G6 | **WP7's window arithmetic**: `window_eps == Window.err` on 864 windows, `best_split == m4_fourier.best_window` on 138 lengths |
| G7 | **WP9** turns a "pool too small" row into a two-sided bound |

After the rewrite, `m3_verify.py` 12/12, `m4_verify.py` 12/12, `m7_verify.py` 16/16 and
`m4_lean_cert.json` byte-identical.  The only rows that moved are at the 1e-13 level and
all come from WP2's stopping rule (M4 V3 `2.7e-15 -> 2.9e-15`, V11 `2.2e-16 -> 1.5e-13`,
M7 V3 `1.3e-10 -> 1.4e-09`).

### Two traps these choices exist to avoid

**The grid is sized by WP4, not by WP5.**  The plan sizes `G` from the truncation error,
`G >= S1/eps_{N,M}`.  That is the wrong constraint and it is too loose: at `L = 12, H = 16`
it picks `G = 4096`, the FFT gradient then reports `|Phi| ~ 2e-06`, and M7 V3 -- which
asserts `|Phi| < 1e-06` at the optimum -- fails.  The binding requirement is the reported
`Phi_h`, because that is what the optimiser is steered by, so `_grid_size` also demands
`(pi h_max/G)^2/2 <= 1e-07`, i.e. `G >= 8192 h_max`.  As a side effect this fixes the
crossover: the FFT path is never taken at a window so shallow that the grid it would need
costs more than the mode loop it replaces.

**The WP9 LP carries a slack, not a hard equality.**  Exactly where WP9 is needed the
pool's hull has 0 on its *boundary*, and with a hard flatness equality the solver reports
infeasibility while the separating direction has already collapsed below `1e-12` -- the
loop stalls with nothing to steer by.  With an `l^1`-penalised slack the LP always solves,
`resid` is the honest flatness measure, and `lb` is gated on `resid <= feas_tol`.  A value
reported with a larger residual is **not** a bound on `E_H`: the mixture it comes from is
not flat.

### What is not done

WP1-WP9 are implemented and gated, and W4 has been run -- see the next section.  Of the
plan's milestones, W5 (`cutting_plane_lower` at the W4 rows, so that a *failure* to
certify would also be a theorem) and W6 (the note) remain.  W5 is now the smaller
question it was always meant to be: at both `alpha` the search succeeded, so there is no
silence left to turn into a no-go there.


## W4: the two middle quadratic units, decided (`m8_w4.py`, 2026-08-25)

M4 sec 8 measured 60 % and 40 % of the entropy budget consumed at `H = 64` at these two
`alpha`, called M3 sec 9.2's `H* ~ 1.8e4` and `1.3e4` proxies "badly pessimistic at the
two middle units", and read the remaining gap as "a few hundred modes away, not `10^4`".
W4 is that reading's test, and it is now cheap enough to run: **both certificates fire.**

| alpha | `h_min` | first fires | `Lambda_enc` | margin | M3 sec 9.2's `H*` |
| --- | --- | --- | --- | --- | --- |
| `(3+sqrt5)/2` | 0.481212 | `H = 256`, `L = 22` | **0.450645** | +0.030567 | `1.8e4` (70x out) |
| `(3+sqrt13)/2` | 0.597382 | `H = 1024`, `L = 22` | **0.591005** | +0.006377 | `1.3e4` (13x out) |

So Problem 10.61 holds at `(3+sqrt5)/2` and at `(3+sqrt13)/2`, on the same footing as the
`2+sqrt3` certificate of M4 sec 9: modulo the two analytic inputs M3 states and does not
prove -- Theorem 11 (the Ledrappier-Young entropy floor) and the variational principle --
the finite half is an explicit multiplier vector and a Collatz-Wielandt bound on a
`2^22`-state operator.  Both are stored in `m8_w4.json` / `m8_w4_ext.json` and are
recomputed from the file by G-5.  M4 sec 8's reading was right and M3 sec 9.2's `H*` proxy
is pessimistic by 70x and 13x; `1+sqrt2` remains what M4 called it, the genuine outlier,
and is `plan-BB61-1+sqrt2.html`'s problem.

The two ladders, and the deep certificates at every rung:

| alpha | H | `Lambda_enc` L=22 | `Lambda_enc` L=24 | `Lambda_cw` L=24 | margin (L=24) |
| --- | --- | --- | --- | --- | --- |
| `(3+sqrt5)/2` | 64 | 0.544970 | 0.542308 | 0.553003 | -0.06110 |
| | 128 | 0.520755 | 0.516669 | 0.539564 | -0.03546 |
| | 256 | 0.450645 | **0.441841** | 0.482520 | **+0.03937** |
| | 512 | 0.408749 | **0.391467** | **0.440063** | **+0.08975** |
| `(3+sqrt13)/2` | 64 | 0.654819 | 0.654723 | 0.655102 | -0.05734 |
| | 128 | 0.641624 | 0.641414 | 0.642458 | -0.04403 |
| | 256 | 0.625752 | 0.625262 | 0.628938 | -0.02788 |
| | 512 | 0.607380 | 0.606414 | 0.614517 | -0.00903 |
| | 1024 | **0.591005** | **0.589216** | 0.605593 | **+0.00817** |
| | 2048 | **0.574095** | **0.570866** | **0.592503** | **+0.02652** |

**The stop rule cleared on the first try.**  `E_128 = 0.514108` against `E_64 = 0.540694`
at the same window, a gain of `+0.0266` against the plan's threshold of `0.02` (and
`+0.0301` against M7 sec 4's `E_64 = 0.544161` at `L = 12`).  The gains per doubling at
`(3+sqrt13)/2` do not merely hold up, they *grow* through `H = 1024` and then hold --
0.0133, 0.0162, 0.0188, 0.0172 in `Lambda_enc` at `L = 24` -- which is the shape M4 sec 8
predicted and not the `S(H) ~ c_alpha log H` saturation M3 sec 9.2 feared.

### The certificate that fires is the word-wise one, and it is not close

`Lambda_cw = pressure_ub + delta_bound` is the plan's own G-3 object, and it charges the
uniform `2 pi (sum_h h|a_h|) eps` to every word.  `Lambda_enc = m4_fourier.certify` is M4
Prop. 3's word-wise enclosure `g + eps|g'| + eps^2 M2/2`, which charges the truncation
where it acts.  At these degrees that is not a refinement -- it is the difference between
a theorem and nothing:

| alpha | fires under `Lambda_enc` | fires under `Lambda_cw` |
| --- | --- | --- |
| `(3+sqrt5)/2` | `H = 256` | `H = 512` |
| `(3+sqrt13)/2` | `H = 1024` | `H = 2048` (`L = 24` only) |

The reason is `S1 = sum_h h|a_h|`, which the optimiser drives to 700 at `H = 512` and 3800
at `H = 2048`: the uniform slack is `2 pi S1 eps`, so it grows linearly in a quantity the
search has every incentive to grow.  Pointwise `|g'|` is nowhere near its supremum, and
the enclosure is 4x to 10x tighter for it.  Two consequences worth carrying forward:

* the search must minimise the *certifiable* surrogate `P~ + 2 pi eps_deep sum_h h|a_h|`
  (`m4_fourier.search`), not `P`.  Minimising `P` alone at the shallow window drives `S1`
  to 170 at `H = 64` here, against M4's 52, for a gain of 0.02 in `P` that the deep window
  charges back threefold.  `minimize_pressure` is the wrong tool for this milestone and
  `m4_fourier.search` is the right one.
* WP5's accounting is exactly right about the grid and exactly the wrong shape for the
  window.  `delta_bound` should not be the reported certificate at large `H`.

### How W4 is run, and its gates

    m8_w4.py run [key ...]   the ladder at --search, one certificate per rung at --deep
    m8_w4.py g2  [key ...]   G-2: m4_run_frontier.py's own pipeline, re-run
    m8_w4.py gates           G-2 + G-3 + G-4 + G-5 from the JSONs

The shape is M4 sec 7's: search shallow (`--search 18`, two window-steps deeper than M4's
16), certify deep (`--deep 22,24`).  That is sound because both deep bounds are
Collatz-Wielandt and hold for whatever strictly positive vector they end up with, so
neither cares which window produced the multiplier; and it is calibrated, because
`P_deep - P~` came out at `1.7e-3` at `H = 256`, the same order M4 measured for a search
four window-steps shallower.

| gate | verdict |
| --- | --- |
| G-2 | **PASS.**  `m4_frontier.json`'s pipeline re-run through the rewritten engine with the pre-WP2/WP3 switches restored (`stop='vector'`, `fft_min_modes=inf`, `warm=False`).  The deterministic half is bitwise 12/12; the search reproduces to the ulp at `H <= 8` and to `1.3e-08` at `H <= 16`; 9 of 12 published certificates agree to the printed six decimals and none is worse by more than `+3.1e-07` |
| G-3 | **PASS.**  20 deep certificates: `Lambda_enc - P_deep >= 4.2e-05`, `Lambda_cw - P_deep >= 4.2e-04`, `Lambda_cw >= Lambda_enc` always, and every `eps == err + 1/(2G)` to the last bit |
| G-4 | **PASS.**  `max|x_j| = 1.853` and `0.534` over 8 and 10 rungs against `cap = 20`: the box is inactive, so the values are `E_H` and not `inf` over a box |
| G-5 | **PASS.**  Both firing certificates recomputed in a fresh process from the stored multiplier by `m4_fourier.certify` itself -- `+0.0e+00` both times -- and M4 Prop. 3 re-checked *at the window that fired* against 240 exact bi-infinite completions summed in mpmath: `|F - F~| <= eps` always, worst `3.38e-05` against `eps = 3.49e-05` |

G-5 exists because m4_verify V2 checked the enclosure at `L = 12` and V9 recomputed
certificates that were already in the file.  A certificate at `L = 22` deserves both
again, at `L = 22`, from its own stored multiplier.

Beyond H = 16 the G-2 reproduction stops being bitwise, and the reason is not a
regression: `sum_h h|a_h|` drifts by up to 0.43 while the value moves by at most `3.0e-04`
and always downwards.  That is what a flat minimum looks like from an L-BFGS trajectory
that a single ulp has nudged, and it is why the three certificates that move all come out
*better* than M4's.

### One operational trap, worth more than it sounds

**Pin the BLAS thread count.**  With OpenBLAS left at its default (this build reports
`MAX_THREADS=64`), the W4 ladder ran at over 1000 % CPU and `H = 32` took 164 s;
`OPENBLAS_NUM_THREADS=2` took the same rung to 14 s.  A **12x** speedup, on work that is
memory-bandwidth-bound and single-threaded in numpy anyway -- the threads were spinning,
not computing.  Worse, the threaded reductions are not deterministic across thread counts:
the first G-2 attempt reproduced M4's `H = 4` row to `2.2e-16` instead of exactly, and the
whole reproduction drifted from there.  Pinned, the same rows come back to the ulp.  Both
runs in `m8_w4.log` and `m8_w4_ext.log` were made with

    OPENBLAS_NUM_THREADS=2 OMP_NUM_THREADS=2 MKL_NUM_THREADS=2

and the whole of W4 -- two `alpha`, ten rungs, twenty deep certificates -- is 2.7 hours on
one machine.  The plan priced the `L = 24, H = 512` row alone at four days.


## R0: the support precondition at `1+sqrt2` (`r0_support.py`, 2026-08-26)

Write-up: **`note-1061-R0.html`**.  Gate G-1 of `plan-BB61-counterexample.html`, which asks
whether Route 4's one structural obstruction is absent: by Prop. C of that plan, if
`F(Omega(alpha))` misses an arc then no shift-invariant `mu` with `F_*mu = Leb` can exist,
and by M1 Prop. 11 + Prop. 4 that set is the confinement set `X(alpha) = (C-K) mod 1`.

**It passes, and the cited route turned out to be unnecessary.**  At `alpha = 1+sqrt2`

    C - K = [ -sqrt2/2 , 2 + sqrt2/2 ]      (length 2+sqrt2 = 1 + diam K)

as an **identity of sets**, not the inclusion the gap lemma gives.  The proof is elementary
and constructive:

1. `c_m = -sqrt2 (-rho)^m` with `rho = sqrt2-1 = 1/alpha`, so `C = sqrt2 rho A0` and
   `K = -sqrt2 B` with `A0`, `B` digit systems in the base `rho`;
2. `sum_{m odd} rho^m = 1/2` *exactly* at this alpha, so `delta_m <-> a_m` (m even),
   `delta_m <-> 1-a_m` (m odd) is a bijection proving `B = A0 - 1/2`, whence
   `C - K = sqrt2 (A0 + rho A0) - sqrt2/2`;
3. each free bit occurs in exactly one coefficient of `A0 + rho A0`, so the coefficients are
   independent: `A0 + rho A0 = {0,1} + rho E`, digits `{0,1,2}` in base `rho`;
4. the covering lemma (`E = [0, n/(1-r)]` as soon as `1 <= r n/(1-r)`; the `m=3` case is
   Utz's theorem, reproved in `SZ/CoverGame.lean`) applies twice, both times as
   `rho L = sqrt2 >= 1`.

Same argument at `(3+sqrt5)/2`: `C - K = [0,2]`.  Reach: the single-base step needs alpha to
be a unit and then `rho >= 1/3`, i.e. `alpha <= 3` -- **exactly the two quadratic Pisot units
in (2,3]**, which is exactly where Theorem T fires among the units.  Two criteria with no
shared input, one frontier; worth having, since the T-T route rests on [New79]/[PT93] and
plan-dubD1O5's audit records that neither is in `papers/`.

`r0_support.py` runs 46 checks, all exact in `Z[sqrt2]` / `Z[sqrt5]` except block 3, which is
the constructive cross-check: it produces `(eps, delta)` for each of 4001 targets by the
greedy of step 4 and evaluates `pi` and `w` from M1's definitions, worst error `1.3e-15` at
digit depth 200.  Output recorded in `r0_support.out`.

Two by-products.  (a) A correction: `plans/plan-1061.html` stated Theorem T's conclusion as
`C-K = [-diam K, 1]` in two places; the length is right, the endpoints are `[-P, 1+Q]`
(`[-diam K, 1]` would need every `c_m >= 0`, and `sum c_m = -(d-1)` forbids it).  Both
occurrences are repaired; no consumer used the endpoints.  (b) A cheap Lean target: every
criterion in `Confinement.lean` is of the form `confCircle != univ`, and there is no positive
instance anywhere in the folder.  `confCircle = Set.univ` at `1+sqrt2` needed one greedy
with a `[0,L]` invariant and one geometric-series limit -- the shape of `SZ/CoverGame.lean`'s
`pick`/`W_mem`, but uniform in the target and hence simpler.  **Done the same day:
`FullSupport.lean`; see the next section.**

**Scope discipline.**  `X = T` is *necessary* for a counterexample and nothing more: the same
gate passes at `(3+sqrt5)/2`, where 10.61 is **proved** (W4, `H = 256`).  R0 removes an
obstruction; it is not evidence for the lane's thesis.

## R0 in Lean: `confCircle = Set.univ`, the first positive instance (`FullSupport.lean`, 2026-08-26)

Everything the folder had ever said about `X(alpha) = confCircle` was negative --
`confCircle_ne_univ_of_avoided`, `not_equidistributed_of_confCircle_ne_univ`, M2's
`confCircle_ne_univ_of_routeAExponent_lt_one`.  `FullSupport.lean` is the other side, at
both quadratic Pisot units in `(2,3]`, and it computes the set rather than bounding it:

    silver_confSet   : silver.confSet   = Icc (-(sqrt 2 / 2)) (2 + sqrt 2 / 2)     -- R0 Thm 1
    goldenSq_confSet : goldenSq.confSet = Icc 0 2                                  -- R0 Cor. 3
    silver_confCircle   : silver.confCircle   = Set.univ
    goldenSq_confCircle : goldenSq.confCircle = Set.univ

`silver` is `1+sqrt2` (`X^2-2X-1`, norm `-1`); `goldenSq` is `(3+sqrt5)/2 = phi^2`
(`X^2-3X+1`, norm `+1`).  Both are `QuadSetup`s, so every M1 consumer applies to them
unchanged.

**The covering lemma is the whole engine.**  `tsum_covDigit`: if `n + rL = L` and `rL >= 1`
then every `y` in `[0,L]` is `sum_i u_i r^i` with `u_i` in `{0,..,n}`.  The digits are the
greedy `covDigitAt n w = min n (Nat.floor w)`, and the one thing to prove is that the greedy
step lands in `[0, rL]` (`sub_covDigitAt_mem`), which splits on `floor w <= n`: below the
cap the residue is `fract w < 1 <= rL`, above it the residue is `w - n <= L - n = rL`.  The
invariant `covRes_mem` then runs for ever, `covRes_partial` gives
`y = sum_{i<m} u_i r^i + r^m (residual)`, and `r^m (residual) -> 0` because the residual is
bounded.  No IFS uniqueness, no attractor theory, no thickness -- and no `Nat.floor`
pathology, since the invariant keeps `w >= 0`.

**Degree two splits by the sign of the norm, and only the `-1` case is work.**

* Norm `+1` (`goldenSq`): `beta = alpha^{-1}`, so `pi(eps)` and `S(delta)` are digit systems
  in the *same* base with the *same* scale `1-beta`, and
  `sub_wVal_eq_of_beta_eq_inv : pi(loBit u) - S(hiBit u) = (1-beta) sum_k u_k beta^k`.  One
  application of the covering lemma at `n = 2` (`3 rho >= 1`, i.e. `alpha <= 3`) is the whole
  of Corollary 3.
* Norm `-1` (`silver`): the past sits in base `-rho`.  `parityFlip` is R0 (S2) and
  `tsum_dR_parityFlip` is its identity; the constant it costs is `sum_{m odd} rho^m`, which
  is `rho/(1-rho^2)` and equals **exactly `1/2`** here (`silver_odd_sum`) because
  `1 - rho^2 = 2 rho` at `rho = sqrt2 - 1`.  That single identity is what makes the
  relabelling free, and by R0 Prop. 4 it holds at no other quadratic Pisot unit.  Then (S3)
  is `silver_sub_wVal`: with `a = consW b (hiBit u)` and `delta = parityFlip a`,

      pi(loBit u) - S(delta) = sqrt2 (a_0 + rho sum_k u_k rho^k) - sqrt2/2,

  the `{0,1} + rho E` shape.  The target `y` fixes `w = (y + sqrt2/2)/sqrt2` in `[0, 1+sqrt2]`,
  the top bit is `b = (sqrt2 < w)`, and the greedy runs on `(w - a_0)/rho` in `[0, 2+sqrt2]`.

**The reverse inclusion is M1 Lemma 3 with the constants computed.**  `silver_wMax` and
`silver_wMin` give `P = sqrt2/2` and `Q = 1 + sqrt2/2` by the same two parity sums
(`tsum_ite_even`, `tsum_ite_odd`), so `C - K` is contained in `[-P, 1+Q]` -- which is what the
greedy fills.  Hence `silver_confSet_length`: the interval has length `1 + diam K`, the
largest possible, so Theorem 1 computes the convex hull and spends no slack.  (`diam K`
itself is `1 + sqrt2`, comfortably above M1 Lemma 3's floor `diam K >= d-1 = 1`.)

**What it buys.**  `silver_no_avoided_interval` and `goldenSq_no_avoided_interval`: at these
two alpha *no* open subinterval of `(0,1)` is missed by every orbit at every time.  That is
the exact hypothesis of the covering engine in `Covering.lean`, so the machine-checked
statement is "the support lane is shut here" -- and shut citation-free, without Newhouse
thickness ([New79]) or the corrected gap lemma ([CHM02] §4, [PT93] Ch. 4), none of which is
in `papers/`.  Gate G-1 of `plan-BB61-counterexample.html` is therefore discharged in Lean,
not only in Python.

**Operational.**  `r0_lean.py`, 10/10 verdicts at `mp.dps = 60`, depth 400, 801 targets per
alpha.  It exists because the Lean greedy is **not** `r0_support.py`'s: the note's script
takes the largest digit keeping the residual in `[0,L]`, the Lean takes
`min n (Nat.floor w)`, and the two produce different words for the same target.  So the
reconstruction `(b, u) |-> (eps, delta)` is re-evaluated through M1's *original* `pi` and `w`
-- worst error `6.2e-61` -- which is the block that would catch a sign error in (S2) or an
indexing error in (S3).  Both branches of the top-bit choice are exercised (332 of 801
targets set it).

**Scope, restated.**  `X = T` is necessary for a Route 4 counterexample and nothing more.
The same theorem holds at `(3+sqrt5)/2`, where 10.61 is *proved* (W4, `H = 256`).  What
`FullSupport.lean` adds is the first machine-checked statement in the folder about the
*limits* of the method rather than about a decided alpha.


## R1a: rigorous enclosures of `Phi_h(nu)` (`r1a_enclose.py`, `r1a_pool.py`, 2026-08-26)

Work package R1a of `plan-BB61-counterexample.html`.  R1b wants to certify
`0 in int conv{Phi(nu_j)}` in `R^2H`, which is stable under perturbations below the margin
-- so the `Phi(nu_j)` have to be **enclosed**, not estimated.  Gate: the radius must sit
below the `1e-5` at which M7 sec 4's two brackets cross.

**Met by eight orders of magnitude, and the interesting part is where the difficulty
actually was.**

| component | size at `1+sqrt2` | why |
| --- | --- | --- |
| truncation, M4 Prop. 3 in Fourier form | `8.7e-21` at `h=64`, `(J,M)=(60,60)` | `\|Phi_h - Phi~_h\| <= 2 pi \|h\| eps(J,M)` for **every** invariant measure at once |
| float64 rounding, a-priori bound | `1.5e-13` over `K=121` emissions | every intermediate has modulus `<= 1`, so nothing amplifies |
| `mpmath.iv` reference engine | `3.1e-21` | agrees with the float pass to `3e-17`, `4600x` inside its own bound |

`eps(J,M) = a^-J + |abar-1| rho^(M+1)/(1-rho)` is `1.8e-5` at `(20,20)` and `4e-36` at
`(100,100)`: **the `1e-5` scale of M7 sec 4 is exactly the `(20,20)` line**, i.e. an artefact
of a transfer operator whose `2^(N+M)` states cap `N+M` near 12.  A Fourier enclosure has no
operator and therefore no cap.

### The finding: parametrise the pool by circulations, not by conditional probabilities

`Phi` depends on the stationary vector linearly -- `|Phi~ - sum_b pi~_b W_b| <= ||pi - pi~||_1`
because `|W| <= 1` -- and given `q`, `pi` is the Perron eigenvector of a `2^L x 2^L` matrix.
That is **the one place where M7 sec 4's "Phi_h computed exactly" is optimistic**:
`BlockChain.stationary` is a numerical solve (measured accurate to `6e-16` here, against M7
margins of `1e-1`, so no M7 number moves -- but it is not certified).

A memory-`L` Markov measure given instead as an exact rational **circulation** on the order-`L`
de Bruijn graph, `sum_x p(bx) = sum_y p(yb)`, has

    pi(b) = p(b0) + p(b1),   q(b) = p(b1)/pi(b)

exactly, as rationals: conservation *is* shift-invariance, so there is nothing left to verify,
at any entropy.  The cheap alternative -- a Dobrushin residual bound
`||pi - pi~||_1 <= ||pi~ P^k - pi~||_1 / (1 - tau(P^k))`, `tau(P^k) <= 1 - sum_u min_b P^k(b,u)`
-- was measured and it splits:

| chain (L = 8) | `h(mu)` | `tau(P^32)` | `tau(P^64)` |
| --- | --- | --- | --- |
| random word + uniform 1/20 | 0.669 | `1.1e-06` | `2.0e-14` |
| periodic `110100` + uniform 1/1000 | 0.0008 | `9.997e-01` | `9.993e-01` |

so it works for high-entropy chains and collapses (amplification `1476x`, and growing) exactly
on the low-entropy witnesses the counterexample lane may need.

### Converting M7's pool costs `1e-7`

`circ_from_weights` rounds `w = pi~ q~` to multiples of `1/T`, which leaves a divergence of at
most 2 per node, and repairs it deterministically: between any two `L`-blocks the de Bruijn walk
is read off the bits of the target and has length exactly `L`, so the total added flow is below
`L 2^L / T` -- `8.6e-7` at `L = 12`, `T = 1e10`.  No sampling.  The converted pool at `1+sqrt2`:

| `H` | pool | upper (optimiser) | lower, circulations | lower, M7 sec 4 | atoms | radius |
| --- | --- | --- | --- | --- | --- | --- |
| 4 | 65 | 0.691068 | **0.691073** | 0.691073 | 9 = 2H+1 | `1.5e-13` |
| 8 | 129 | 0.690096 | **0.690102** | 0.690102 | 17 = 2H+1 | `1.5e-13` |
| 16 | 257 | 0.689063 | 0.689054 | 0.689054 | 32 != 2H+1 | `1.5e-13` |

### What this already says about R1b, and one correction

On the Caratheodory simplex the entropy LP returns: `w_min * s = 4.6e-8` at `H = 4` and
`1.9e-7` at `H = 8`, against `eps = 1.5e-13` -- **five to six orders of margin, so R1b's
certificate fires and `K_4, K_8 != empty` at `1+sqrt2` become provable.**

But the simplex should not be read off that LP.  Its objective `sum lam_j h(nu_j)` is linear,
so the optimum sits at a vertex and the weights are pushed to the boundary of the weight
simplex.  Under a maximin objective (`max t` s.t. `sum lam_j Phi_j = 0`, `lam_j >= t`, still one
LP) **every** pool member carries `lam >= 1.4e-2 / 6.4e-3 / 3.3e-3` at `H = 4 / 8 / 16`, with
residual `<= 8.6e-16`; with `sigma_min(V) ~ 0.21-0.27` that is a margin of `7e-4` to `3.7e-3`,
`1e9`-`1e10` times the enclosure radius.  Two consequences:

* R1b should certify with all `m` members and the maximin depth, not with a `2H+1` simplex;
* at `H = 16` the entropy LP returns 32 atoms at residual `2.1e-8` and calls the converted pool
  infeasible, while the maximin LP puts 0 at depth `3.3e-3`.  A `1.3e-7` perturbation flipped
  that verdict.  **M7 sec 4's four "pool too small" rows are statements about the objective as
  much as about the pool** and should be re-tested before that reading is relied on.

Not enclosed, and not needed by R1b: the entropies `h(nu_j)`.  The LP *lower bound* is therefore
still a float quantity; `0 in conv` is not, and the counterexample lane needs no entropy anywhere.

Files: `r1a_enclose.py` (15 checks, `r1a_enclose.out`), `r1a_pool.py` (`r1a_pool.log`,
`r1a_hull.out`, `r1a_pool.json` -- enclosed `Phi` as midpoint plus radius, with provenance).
`python3 r1a_pool.py --report` re-reads the JSON and prints the hull geometry.

## R1b: `K_H != empty`, proved -- the interior-of-hull certificate (`r1b_certify.py`, `r1b_pool.py`, 2026-08-26)

Work package R1b of `plan-BB61-counterexample.html`.  `K_H = {mu invariant : Phi_h(mu) = 0,
h <= H}` is cut out of `M(sigma)` by `2H` exact linear equations, so it has empty interior and
**no approximate witness is evidence of anything**; that was sec 4's QA finding, and it is what
R1b removes.

### The theorem (one lemma, and it fixes the plan's open constant)

With `Phi(nu) in R^2H`, `V` the matrix of computed values, `W = [V ; 1^T]`, weights `lam >= t`
with `1^T lam = 1`, and `r = V lam`:

        |Phi(nu_j) - V_j|_2 <= e2   for all j
        delta := t * sigma_min(W) - |r|_2 - e2 > 0
    ==> there is lam'' in the simplex with sum_j lam''_j Phi(nu_j) = 0,  so K_H != empty,
        and  h(mu) >= sum_j lam_j h(nu_j) - (|r|_2 + e2) sqrt(m) log2 / sigma_min(W).

Proof: (i) `y |-> lam + W^+(y,0)` realises every point of the ball `B(r, t sigma)` as a convex
combination -- the row of ones is what lets it move `V lam` while keeping `1^T lam = 1`;
(ii) `w |-> sum_j L(w)_j e_j` maps `B(0,e2)` into itself, and Brouwer's fixed point is the
witness.  Consequences for the plan's sec 6.1 recipe `(eps, w_min, s, kappa)`:

* **`kappa = 1`** -- the constant it left open is exactly 1, no factor in between;
* the conditioning that matters is `sigma_min[V ; 1^T]`, **not** `sigma_min` of vertex differences;
* no Caratheodory selection: all `m` pool members are used, which is worth four orders of margin;
* Brouwer returns the *weights*, so the entropy -- hence `H_ent`, the degree M3 Thm 12 needs --
  comes for free.

### Every number, and the direction of its error

| input | how | why the direction is right |
| --- | --- | --- |
| the pool | exact rational circulations (R1a) | conservation *is* shift-invariance |
| `e2 = eps sqrt(H)` | R1a's `eps = 1.481e-13` per mode | truncation + a-priori float64 bound |
| `t`, `1^T lam = 1` | `lam_j = a_j/D`, integers, `D = 1e14` | exact identities, not solver output |
| `\|r\|_2` | exact rational `V lam`, then integer-sqrt up | rounded the way it enters `delta` |
| `sigma` | interval Cholesky of `[G] - sigma^2 I`, `[G] >= W W^T` by the `gamma_m` bound | success proves PD, so `lam_min(W W^T) > sigma^2`; returned rounded down |
| `h(nu_j)` | float64 from the exact circulation, minus `1e-11` | the only platform `log`; affects `E_H` only, never `K_H != empty` |

18 self-checks, all passing, test these as mechanisms rather than on the data: the interval class
against exact `Fraction` arithmetic on 20000 triples; the interval Cholesky against `eigvalsh`
(60 matrices) with no false positive on 80 shifted ones; the ball of step (i) constructively at
`0.999 t sigma`, and shown non-vacuous (at `8 t sigma` the construction leaves the simplex 263
times in 300); `sqrt_upper` on 2000 random fractions; the `gamma_m` Gram bound against 40-digit
arithmetic; a one-sided pool rejected; a rank-deficient (`m < 2H+1`) pool rejected; the dual
certificate below checked in both directions; the entropy routine against interval logarithms and
against 30-digit mpmath on an order-12 repaired circulation; and the generalised emission ladder
against `m7_price.BlockChain.phis` at all three units (`3e-11`).

### The dual half: "pool too small", proved

If `<u, V_j> >= d` for every `j` with `d > |u|_2 e2`, then `<u, Phi(nu_j)> >= d - |u|_2 e2 > 0`
for every `j`, so `0` is not in `conv{Phi(nu_j)}`.  One line of Cauchy-Schwarz; `u` is proposed by
an LP, then rounded to rationals and `min_j <u, V_j>` recomputed exactly, so the verdict rests on
the solver no more than Theorem 1's does.  This proves nothing about `K_H` itself -- that is a
statement about all of `M(sigma)` and needs the ergodic-optimisation minimum of the plan's sec 6.3
-- but it does hand over the missing *direction*: `u` is exactly the Farkas vector the
pool-augmentation loop consumes, so the member to add is the Gibbs measure at `a* - t u`.

### The certificates

`alpha = 1+sqrt2`, pool = M7 sec 4's own (`m = 16H+1` memory-12 Gibbs chains, converted):

| `H` | pool | `t` | `sigma_min(W)` | `\|r\|_2` | `e2` | **`delta`** | `delta/e2` | certified `E_H >=` | M7 sec 4 LP |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 4 | 65 | `1.384e-2` | 0.2654 | `8.2e-15` | `3.0e-13` | **`3.674e-3`** | `1.2e10` | 0.691073498 | 0.691073 |
| 8 | 129 | `6.427e-3` | 0.2605 | `1.5e-14` | `4.2e-13` | **`1.674e-3`** | `4.0e9` | 0.690101873 | 0.690102 |
| 16 | 257 | `3.265e-3` | 0.2133 | `1.7e-14` | `5.9e-13` | **`6.964e-4`** | `1.2e9` | 0.689054039 | 0.689054 |
| 32 | 513 | `1.532e-3` | 0.1983 | `2.3e-14` | `8.4e-13` | **`3.038e-4`** | `3.6e8` | 0.687024430 | 0.687024 |
| 64 | 1025 | `5.216e-4` | 0.1432 | `2.6e-14` | `1.2e-12` | **`7.470e-5`** | `6.3e7` | 0.677497034 | 0.677497 |

`h_min(1+sqrt2) = 0.440687`, so every row also gives `E_H > h_min`.  Hence

    H_flat(1+sqrt2) > 64   and   H_ent(1+sqrt2) > 64,

the second being the stronger (`H_ent <= H_flat`) and the one M3 Thm 12 needs: **M7 F3's headline,
"no trigonometric certificate of degree <= 64 exists at `1+sqrt2`", is now a theorem.**  The
certified lower bounds reproduce M7 sec 4's LP column to the digit it prints, at every `H`.

**The enclosure is nowhere the binding term.**  `delta/e2` runs from `1.2e10` down to `6.3e7`;
`delta ~ t sigma_min(W)` decays like `H^-gamma` with `gamma ~ 1.2` up to `H=32` and `~ 2.0` from
32 to 64, against `e2 ~ H^0.5`, so the two would meet somewhere between `H = 1e5` and `1e6` --
far beyond where the pool build (a `2^(N+M)`-state transfer operator, M7 sec 5) gives out.  What
binds is the pool, and the cheapest lever on it is `circ_from_word`: the block counts of any
cyclic word are a circulation, for free.

### Two QA consequences

**(a) M7 sec 4's crossing is on the upper side, as its own footnote predicted.**  At `1+sqrt2`,
`H = 4` and `8`, the *certified* lower bound exceeds the optimiser's upper bound -- by `5.7e-6`
and `5.8e-6`, measured against the optimiser value recomputed here at full precision, not against
the 6-decimal table entry.  The same happens at `(3+sqrt13)/2`, `1.6e-7` at `H=2` and `1.2e-9` at
`H=1`.  In every case the excess sits at or below the truncation scale of the upper side
(`eps_{N,M} = 1.01e-2` at `1+sqrt2`, `1.2e-3` at `(3+sqrt13)/2`), which is what the diagnosis
predicts and a different mechanism would not.  Consequence: the "upper" column is **not** an upper
bound for `E_H` at the `1e-5` level and no argument should use it as one.  Nothing M7 concludes
changes -- its verdicts compare against margins of `1e-1`.

**(b) M7 sec 4's four "pool too small" rows are artefacts of the objective.**  This discharges
R1a's QA item (b).  The entropy LP maximises a linear functional, so its optimum sits at a vertex
and a `2e-8` residual reads as "0 is on the boundary"; the maximin LP over the *same* pool asks
the question a certificate actually needs.

| `alpha` | `H` | entropy LP (M7's objective) | maximin depth `t` | R1b |
| --- | --- | --- | --- | --- |
| `(3+sqrt5)/2` | 1 | infeasible | `5.64e-2` | `K_1 != empty` **proved** |
| `(3+sqrt5)/2` | 64 | infeasible | **infeasible too** | **genuinely too small, and proved so**: `<u,Phi(nu_j)> >= 5.47e-2` for all 1025 members, `4.6e10 x e2` |
| `(3+sqrt13)/2` | 2 | infeasible | `2.87e-2` | `K_2 != empty` **proved** |
| `(3+sqrt13)/2` | 8 | infeasible | `6.74e-3` | `K_8 != empty` **proved** |

So the four rows **split**: three were artefacts of the objective, one is real -- and the real one
now comes with the direction that fixes it.  The `(3+sqrt5)/2, H=1` row also gains the `E_H` lower
bound it never had (0.689241444, against an optimiser upper of 0.689241479).

### The other two units

| `alpha` | `h_min` | certified | `H_flat >` , `H_ent >` |
| --- | --- | --- | --- |
| `(3+sqrt5)/2` | 0.481212 | `H = 1, 2, 4, 8, 16, 32` (`delta` from `2.15e-2` to `3.03e-5`); at `H = 64` the pool is **proved** too small | 32 |
| `(3+sqrt13)/2` | 0.597382 | `H = 1, 2, 4, 8, 16, 32, 64` (`delta` from `8.98e-3` to `1.55e-5`) | 64 |

**18 certificates and one refutation: every row M7 sec 4 was able to report is now certified, and
so is one it was not.**

### One implementation lesson

The naive interval Cholesky (flat entrywise radius, no scaling) **fails at `d = 2H+1 = 129`**,
returning `sigma = 0` where `lam_min(G) = 8.9e-4` -- a false negative, so nothing unsound follows,
but the `H = 64` rows are lost.  Two changes recover them and they compose:

* **Jacobi scaling.**  Run on `D^-1 ([G] - s I) D^-1`, `D = diag(sqrt(G_ii))`.  Congruence by a
  positive diagonal preserves definiteness exactly, and the appended row of ones makes `G_dd = m`
  while a high-mode row has `G_ii` orders of magnitude smaller -- a near-flat measure has tiny high
  Fourier coefficients, which is the point of the pool.
* **A Cauchy-Schwarz radius.**  `|fl(G_ij) - (W W^T)_ij| <= gamma_m sum_k |W_ik W_jk|
  <= gamma_m sqrt(G_ii G_jj)`, so in the *scaled* matrix the radius is the constant
  `gamma_m ~ 1.1e-13` -- three orders tighter at `d = 129` than the flat `gamma_m m max|W|^2`,
  and exactly matched to the scaling.

With both, `sigma_min` is certified to within 0.05% of its true value at every row.

### Files

`r1b_certify.py` (the theorem + the 15 self-checks; `--checks` runs those alone),
`r1b_pool.py` (the pool at an arbitrary quadratic Pisot unit), `r1b_certify.json`,
`r1b_certify.out`, `r1b_pool64.json`, `r1b_pool_golden2.json`, `r1b_pool_root13.json`,
note `note-1061-R1b.html`.  `r1a_enclose.py` gained `set_alpha(A, B)` -- the emission ladder
`(a-1)a^-k` / `(1-abar)abar^m` at any `x^2 = A x + B` -- with `(2,1) = 1+sqrt2` as the default,
verified to leave every recorded R1a number bit-for-bit unchanged.  `r1a_pool.py` gained
`--out` and `--resume` (it now stores `xstar`, so a killed ladder restarts at the last rung).

### `H_ent` is now bracketed on both sides

At the two units where 10.61 is *proved*, M8's W4 run supplies the upper side -- its firing
certificates are `L=22, H=256` at `(3+sqrt5)/2` (value 0.450644576 < `h_min` = 0.481212) and
`L=22, H=1024` at `(3+sqrt13)/2` (0.591004815 < 0.597382), each saying `E_H < h_min`, i.e.
`H_ent <= H`.  With R1b's lower bounds:

    32 < H_ent((3+sqrt5)/2)  <= 256          64 < H_ent((3+sqrt13)/2) <= 1024

The folder's first two-sided brackets on a certificate degree -- and a consistency check between
two unrelated machines (a windowed transfer operator with a Collatz-Wielandt bound, against a
Fourier enclosure over exact circulations) that had to pass, and did.  Note the asymmetry:
**nothing bounds `H_flat` from above anywhere.**  A certificate of degree `H` gives `E_H < h_min`,
not `K_H = empty` -- that is the plan's sec 6.3 "catch" and needs the dual minimiser (R2b).

## M2 Proposition 1 in Lean: the normal form of the criterion (`RouteANormalForm.lean`, 2026-08-27)

`Criterion.lean` proves 10.61 at every `alpha` with `A(alpha) < 1`, and `RouteACeiling.lean`
bounds where that can happen at all.  Both state the criterion in the mixed `log`-quotient
shape it is *derived* in.  The shape it is *used* in is M2 Proposition 1's, and until now the
folder had it only in prose -- `Criterion.lean`'s own module docstring asserts the first
equivalence without proving it.  `RouteANormalForm.lean` proves it, together with Corollary 6.

**The two coordinates.**  `logAlpha = L = log2 alpha` and `logRhoInv = R = log2(1/rho)` with
`rho = |beta|`, so that `A(alpha) = 1/L + 1/R` (`routeAExponent_eq_inv_add_inv`; this is just
`log 2 / log x = (log2 x)^{-1}`).  `L > 1` is exactly `alpha > 2` (`one_lt_logAlpha_iff`), and
`R > 0` is exactly `beta != 0`, i.e. the setup being genuinely quadratic (`logRhoInv_pos`).

**Proposition 1.**  The four statements

| | |
| --- | --- |
| `A(alpha) < 1` | the criterion as `Criterion.lean` states it |
| `(L - 1)(R - 1) > 1` | `routeAExponent_lt_one_iff_one_lt_normalForm` |
| `R > L/(L - 1)` | `routeAExponent_lt_one_iff_threshold_lt_logRhoInv` |
| `rho < 2^{-L/(L-1)}` | `routeAExponent_lt_one_iff_abs_beta_lt_rpow` |

are equivalent, and `A(alpha) log2 alpha = 1 + L/R` (`routeAExponent_mul_logAlpha`) -- the
quantity `RouteACeiling.lean` bounds below by the degree.  The first equivalence is one line:
both sides are `L + R < LR` after clearing denominators, and the left side factors.  **No
hypothesis beyond positivity is needed**, `R <= 1` included: there `1/R >= 1` makes the left
side false and `(R-1) <= 0` makes the right side false, so the equivalence holds without a case
split.  The abstract halves are stated for two bare positive reals
(`inv_add_inv_lt_one_iff`, `one_lt_mul_sub_one_iff`, `lt_logb_two_inv_iff_lt_rpow`,
`inv_add_inv_mul_eq`) and instantiated afterwards; nothing in them mentions `alpha`.

**The hyperbola, as theorems.**  The note describes the criterion as a hyperbola in the
`(L,R)`-plane with asymptotes `L = 1` and `R = 1`: a large base buys tolerance of a slow
conjugate and vice versa, but neither `L -> infinity` nor `R -> infinity` alone suffices.  That
is three statements about the threshold `L/(L-1)`, and all three are proved:
`one_lt_div_sub_one` (it exceeds `1` for every `L > 1`), `div_sub_one_lt_div_sub_one` (it is
strictly decreasing in `L`) and `tendsto_div_sub_one_atTop` (it decreases *to* `1`).
Consequently `R > 1` is necessary however large `alpha` is
(`one_lt_logRhoInv_of_lt_one`), and by the symmetry of `(L-1)(R-1)` the same holds with the
roles exchanged.  This is the precise sense in which the marginal costs are governed by the
product and not by either factor.

**Three consumer forms**, each one composition with `Criterion.lean`:
`not_equidistributed_of_normalForm` and `not_equidistributed_of_abs_beta_lt_rpow` prove
Problem 10.61 from `(L-1)(R-1) > 1` and from the explicit threshold on `rho` directly, and
`confCircle_ne_univ_of_normalForm` gives the same statement as M1 Proposition 4.  The threshold
form is the practical one: at a fixed base, Route A fires exactly below a computable bound on
the conjugate.

**Corollary 6, and what it settles.**  At degree two `alpha beta = -b`, so `rho = |b|/alpha`
**exactly** (`abs_beta_eq_div` -- `RouteACeiling.lean` uses only the inequality `1 <= alpha|beta|`
that follows from it) and hence `R = L - log2|b|` (`logRhoInv_eq_sub`).  Proposition 1 then reads
entirely in `alpha` and the constant coefficient:

> `A(alpha) < 1` **iff** `(log2 alpha - 1)(log2(alpha/|b|) - 1) > 1`
> (`routeAExponent_lt_one_iff_quadratic`),

and for units `|b| = 1` this collapses to **`alpha > 4`**
(`routeAExponent_lt_one_iff_four_lt`).  The forward half of the unit statement was already
`RouteACeiling.lean`'s `four_lt_alpha_of_routeAExponent_lt_one`, proved there for every `b`; the
converse is new here.  Together they say that **on quadratic units Route A covers exactly
`(4, infinity)`** -- `2 + sqrt 5` of `RouteA.lean` being the first Pisot number in that range,
and the hard slice `2 < alpha <= 4`, where every one of M0's sixteen certificates lives and
`1 + sqrt 2` with it, lying outside it by a theorem.  Read alongside `FullSupport.lean`, which
proves `X(1+sqrt2) = T`, the two files fence the support route from both sides at the same
`alpha`: Route A cannot reach it, and no other support argument can either.

**Operational.**  `m2_prop1_lean.py`, 10/10 verdicts at `mp.dps = 60`.  `m2_verify.py` already
sweeps P3 and C6, but in the note's coordinates `(rho, |N(alpha)|)`; the Lean file uses the
`QuadSetup` ones (`beta = a - alpha`, and the norm entering as the constant coefficient `b` of
`X^2 - aX - b`), so the sweep is re-run through those, with the 440 quadratic rows recomputed
from their integer coefficients at 60 digits -- checks L6 and L7 then test the identities
`|beta| = |b|/alpha` and `R = L - log2|b|` rather than the stored floats (deviations `1.9e-60`
and `4.2e-59`).  `m2_verify.py` was re-run unchanged as a regression: 11/11, P3 and C6 included.

**Dependency cone.**  Pure algebra on two positive reals plus Mathlib's `Real.logb` API.  The
note's own quality-assurance section records that "Theorem 2's proof uses Prop. 1, which is pure
algebra; Prop. 1 uses nothing", and the Lean file honours that: no covering, no dynamics, no
citation, `std3` throughout.

## R2a: the conditioned margin, the Farkas loop, and the truncation wall (`r2a_margin.py`, `r2a_pool.py`, `r2a_flat.py`, 2026-08-27)

Work package R2a of `plan-BB61-counterexample.html`, gate **G-2: which row of sec 6.3's
dichotomy**.  Answer: **row 2** -- `m(H)` decays as a clean power, witnesses continue, the
pool merely thins.  Full account in `note-1061-R2a.html`.

**Theorem 1' (the observable, corrected).**  R1b's certificate is
`delta = t sigma_min(W) - |r|_2 - e2` with `t = min_j lam_j`, and weights that sum to one
satisfy `t <= 1/m`: a full factor `(16H+1)^{-1}` of any exponent read off it is bookkeeping,
not geometry.  Replacing the uniform floor by the pseudoinverse row norms,

    g_j >= |e_j^T W^+|_2 ,   lam_j >= R g_j ,   1^T lam = 1 ,   r = V lam
    delta := R - |r|_2 - e2 > 0   ==>   K_H != empty ,   and   delta <= rho(H)

with the same proof (only step (i) changes: `|e_j^T W^+ (y,0)| <= g_j |y|_2 <= lam_j`
coordinatewise, in place of the operator-norm bound), the same `kappa = 1`, and the same
entropy corollary.  R1b's Theorem 1 is the case `g_j = 1/sigma_min(W)`.  Worth 5.3x at
`H = 4` to 7.2x at `H = 64`, and what survives is `m^{-1/2}` rather than `m^{-1}`.  The
ceiling of the argument is `delta <= 1/sum_j g_j <= 1/|W^+|_F <= sigma_min(W)`; on the
cross-polytope, where the true inradius is known exactly, it certifies 35% of it, so a
factor ~2.8 of the bracket below is intrinsic and the rest is the pool.

**The ladder, bracketed both ways.**  `rho(H) = dist(0, boundary conv{Phi(nu_j)})
= min_{|u|=1} max_j <u,Phi(nu_j)>` is certified from below by Theorem 1' and bounded from
above by vertex hopping on the polar body `{u : <u,V_j> <= 1}` (Frank-Wolfe; every iterate
is a valid upper bound, so an early stop costs sharpness and never soundness).  At
`1+sqrt2`, `H = 4..64`:

    H          4          8         16         32         64
    delta   3.307e-2   1.159e-2   4.164e-3   2.000e-3   6.057e-4
    rho_up  1.188e-1   7.456e-2   3.920e-2   2.250e-2   8.471e-3

`rho ~ H^{-0.95}` fitted over the four octaves (rung to rung 0.67, 0.93, 0.80, 1.41) and
`delta ~ H^{-1.44}`, the difference being the `m^{-1/2}`.  **Clean power decay, no zero, no
super-polynomial collapse: row 2.**

**And the control fires where the trust rule says it should.**  Rebuilding `H = 32` and
`H = 64` on the `L = 14` window -- identical construction, identical `H`, four times the cost
a member -- the numbers agree at `H = 32` (`delta` 0.99x, `rho_up` 0.94x; `H eps_12 = 0.323`)
and diverge at `H = 64` (`delta` 1.45x, `rho_up` 1.83x; `H eps_12 = 0.646`).  The local
exponent over `32 -> 64` falls from `gamma_delta = 1.72` to `1.17` and from `gamma_rho = 1.41`
to `0.44`: **the apparent acceleration at the top of the `L = 12` ladder is the truncation**,
and with it removed the decay is a single clean power across all four octaves.  The entropies in `r2a_margin.json` are a by-product and
are NOT a sharpening of R1b's `E_H` -- the margin-maximising weights are not the
entropy-maximising ones, and the wide-tilt members are more ordered.  R1b's `E_H` bounds and
`H_ent > 64` stand unchanged.

**The loop.**  sec 6.2 predicts a margin-increasing loop.  Measured, it is one only at the
right tilt scale.  Steered at M7's `t in {0.01,0.04,0.15,0.5}` it runs BACKWARDS (at `H = 8`,
`8.88e-3 -> 7.08e-3` over five rounds) while `rho_up` rises: the hull grows and the
certificate does not follow, because `delta <= 1/sum_j g_j` and `sum_j g_j` grows like
`sqrt(m) |W^+|_F` when the new members duplicate directions the pool already spans.  Steered
at the measured optimum it does what sec 6.2 says: 1.68x at `H = 4`, 1.31x at `H = 8`,
1.12x at `H = 64`, with `sigma_min(W)` up 3.2x.  The gain decays with `H` because the loop
adds `O(1)` directions a round into a hull with `2H` of them.  `m(H)` is taken to be the best
`delta` over the rounds, which is sound: each round certifies the same statement from a
sub-pool of the final one.

**The M7 pool is not redundant.**  Certifying on sub-pools:

    H     full m   delta full   75% of m   delta      50% of m   delta
    8     129      8.881e-3     96         3.532e-3   64         1.081e-3
    32    513      1.841e-3     384        8.363e-4   256        1.948e-4
    64    1025     5.403e-4     768        1.156e-4   512        INFEASIBLE

`0` sits inside the hull only by the collective action of all `16H+1` members.  So the loop
may add and must never prune -- and the Farkas half never fires at `1+sqrt2`, the pool being
feasible at round 0 at every reachable `H`.

**The one lever: M7's tilt scale.**  Rebuilding the identical construction over a grid of
scales, the certified margin peaks at `t in {0.1,0.5,2.5,12}` -- **1.44x M7's at `H = 8` and
1.44x again at `H = 32`**, on 92 and 358 members against M7's 129 and 513, the rest lost
because the tilted chain degenerates and its weights are no longer a near-circulation.
Beyond `t ~ 12` the losses outrun the gain; eight scales instead of four is slightly worse.
Not the member count, not the steering direction: the tilt magnitude, and M7's is an order of
magnitude too small.

**Row 1, tested directly (`r2a_flat.py`).**  For `mu in K_H`, `int psi_a dmu = 0` for every
`a`, so `h(mu) <= P(psi_a)` and `E_H <= P(psi_a)` for EVERY `a`; since `h >= 0`,

    P(psi_a) < 0  for a single a   ==>   E_H < 0   ==>   K_H = empty .          (F)

That is M7 Thm 5's own inequality with the threshold moved from `h_min` to `0`: `cert < h_min`
bounds `H_ent` and is what M3/M7/M8 have always tested, `cert < 0` bounds `H_flat` -- the
degree R1b could bound from below and nothing in the folder could bound from above.  Same
machine: `Window.pressure_ub` (Collatz-Wielandt, valid at any strictly positive test vector)
and `delta_bound = 2 pi (sum_h h|a_h|) eps_L`.

It **fires** -- `pressure_ub = -2.339` at `L = 12, H = 128`, the first firing of row 1
anywhere in this folder -- and it fires at the truncation scale:

    L    eps_L      last clean H (H eps)   onset H (H eps, |a|_inf)   runaway H (H eps)
    12   1.010e-2   96  (0.970)            112 (1.131, 0.701)          128 (1.293)
    14   4.184e-3   224 (0.937)            256 (1.071, 0.678)          320 (1.339)
    16   1.733e-3   512 (0.887)            640 (1.109, 0.743)          > 640

**The onset is at `H eps_L = 1.10 +- 0.03` across three windows spanning a factor 5.8 in
`eps`, and the threshold itself, bisected, is `H_0(12) = 120` and `H_0(14) = 288` --
`H_0 eps_L = 1.2122` and `1.2050`, the same to 0.6%, with `H_0(16) > 640` consistent.**  `|F - F~_L| <= eps_L`, so `e(h F~)` and `e(h F)` part company once
`2 pi H eps_L >~ 1`, and `K_H(F~_L)` empties for exactly that reason.  The control is
decisive: re-price the very direction that drives the `L = 12` pressure below zero at finer
windows.  At its own window it is worth `kappa/tau ~ 8e-4`; at `L = 14` and `L = 16`
`pressure_ub` turns from `-0.54` to `+42`, so it does not separate at all.

**The same wall closes the one row R1b left open.**  At `(3+sqrt5)/2, H = 64` the Farkas loop
kills its first direction outright (16 tilted members land at `<u,Phi>` between `-1.33` and
`-0.23`) and then stalls forever on the second, 135 members later, gap unmoved at
`4.790298e-2`.  The diagnosis is exact and it is the same sentence: the pool members are
equilibrium states of the WINDOW observable, so the pressure is convex in `a` with gradient
`Phi~(mu_a)` and WP9's tilt is monotone in `<u, Phi~>` **for every u** -- while the
certificate is written in the enclosed `Phi`.  Along the stalled direction `<u,Phi~>` sweeps
`-0.363` to `+0.309` and crosses the plane at `s ~ -0.2`; `<u,Phi>` never crosses, and every
`s` at which `Phi~` is safely across (`|s| >= 2`) has NO MEMBER, the tilted chain having
degenerated.  What R1b called "a computed next step rather than a dead end" is, measured, a
dead end for this machinery.

**A trust rule for the whole folder.**  A degree-`H` run on an `L`-window measures `F` only
while `H eps_L <~ 0.9`.

    R1b ladder 1+sqrt2      L=12  eps 1.010e-2   H=64    H eps 0.646   safe (closest on record)
    R1b ladder (3+sqrt5)/2  L=12  eps 4.292e-3   H=64    H eps 0.275   safe
    R1b ladder (3+sqrt13)/2 L=12  eps 1.206e-3   H=64    H eps 0.077   safe
    M8 W4 (3+sqrt5)/2       L=22  eps 3.490e-5   H=512   H eps 0.018   safe by 50x
    M8 W4 (3+sqrt13)/2      L=22  eps 3.070e-6   H=1024  H eps 0.003   safe by 290x
    the plan's H<=512       L=12  eps 1.010e-2   H=512   H eps 5.172   PAST THE WALL by 6x

Reachable `H` is `<~ 0.9/eps_L` with `eps_L ~ rho^{L/2}` and cost `~2^L`, so **reachable `H`
grows like (cost)^0.63**.  `H = 512` needs `L ~ 20`; `H = 1e4` needs `L ~ 26`.

**And a price for the lane at `1+sqrt2`.**  On `L = 16`, over the four trustworthy octaves,
the constrained pressure falls from `0.687379` (`H = 32`) to `0.674160` (`H = 512`):
`3.3e-3 per doubling of H`.  `h_min = 0.440687` is `0.2335` away -- about **70 further
doublings**, `H ~ 1e24`.  At `(3+sqrt5)/2`, M8 W4's sweep falls `4.4e-2` per doubling,
**thirteen times faster**, and spends its whole budget by `H ~ 256`, exactly where M8's
certificate fires.  **M8's W4 machine has never been run at `1+sqrt2`** (`m8_w4.log` covers
only the two units where the answer was already expected); its `Lambda_enc` beats
`pressure_ub + delta_bound` by 0.10 at `(3+sqrt5)/2`, and the crude bound never beats
`log 2` at `1+sqrt2` at any `(L,H)` tried here.  That is R2c in the plan's sec 12.

**Machinery notes.**
* `sigma_min` is now Rump's criterion in LAPACK (`pd_verified`): if the ordinary float
  Cholesky of `A - c I` with `c = gamma_{d+1} max_i A_ii` completes, `A > 0`.  A hundred
  times faster than R1b's interval Cholesky at `d = 129` and **sharper** -- within `3e-9` of
  the SVD value where the interval version lost `5e-4` relative.  The two are independent
  verified methods and they agree; keep the interval one as the cross-check it now is.
* The residual `|V lam|_2` is exact in **integers** (float64 entries are dyadic, so `2^e V`
  is an integer matrix), which is what makes `m` in the thousands affordable.
* `BlockChain.stationary`'s dense `2^L x 2^L` solve is replaced by a warm-started power
  iteration: 500x faster and **no rigour is spent** -- `pi` only decides which invariant
  measure the member is, and `circ_from_weights` turns whatever weights it is given into an
  exact rational circulation.  A warm start also PROPAGATES failure, so `member()` retries
  from cold and rejects rather than poisoning the rest of the pool.
* `_const_table` is memoised; the enclosure loop is memory-bandwidth-bound at
  `121 H 2^L` complex operations a member and does not respond to layout changes.
* 24 self-checks: `python3 BB61/r2a_margin.py --checks`.

**Files.**  `r2a_margin.py` (Theorem 1', the bracket, the loop, `--ladder`, `--farkas`,
`--checks`), `r2a_pool.py` (fast member builder, `--build` ladder, `--check` reproduces the
R1b pool bit-for-bit), `r2a_flat.py` (`--sweep`, `--ray`), `r2a_checknote.py` (reads the
numbers back out of `note-1061-R2a.html` and compares them with the recorded runs -- prose
drifts when a run is repeated, and this catches it).  `python3 r2a_margin.py` with no
arguments runs the self-checks and reproduces the recorded ladder.  Outputs `r2a_margin.json`,
`r2a_farkas.json`, `r2a_flat.json`, `r2a_margin.log`, `r2a_flat.log`,
`r2a_pool_1+sqrt2_L14_*.npz`.  Note `note-1061-R2a.html`.

## M2 Theorem 2(i) in Lean: certified depths exist, on a named ray (`RouteADepth.lean`, 2026-08-27)

`Criterion.lean` already proves the covering certificate is *satisfiable* when `A(alpha) < 1`.
But it does so along a rational ray `(M,M') = (pn,qn)` pulled out of `exists_rat_btwn`: the
depths exist, and nothing more is known about them.  Theorem 2(i) of `note-1061-M2.html` is the
sharper statement, and it is what M2 Corollary 3 evaluates: it **names the ray** and bounds the
covering total on it by an explicit affine function of `M`.

**The ray.**  `balancedDepth L R M = ceil(M*L/R)`, and `coverTotal alpha rho C M M' =
2^{M+M'}(alpha^{-M} + C rho^{M'}/(1-rho))` -- the number of covering intervals times a bound
for each one's length.  `C` is left free: the note uses `C_alpha = sum_j |alpha_j - 1|`,
`Covering.lean` uses the bound `1 + rho`.

**The theorem.**

> `log2 T(M, ceil(ML/R)) <= 1 + log2(1 + C/(1-rho)) + M * (1 - (L-1)(R-1))/R`
> (`logb_coverTotal_balancedDepth_le`)

and the right-hand side tends to `-infinity` (`tendsto_bound_atBot`), so `T -> 0`
(`tendsto_coverTotal_balancedDepth`) and every threshold is eventually cleared
(`eventually_coverTotal_balancedDepth_lt`).

**The proof is three lines, and each is isolated as a lemma.**

| | |
| --- | --- |
| `pow_balancedDepth_le` | `rho^{M'} <= alpha^{-M}` -- this is what the balanced ray *means*.  With `alpha = 2^L` and `rho = 2^{-R}` it reads `R*M' >= L*M`, which is `Nat.le_ceil`.  The window error and the Cantor error then collapse into one term. |
| `two_pow_balancedDepth_le` | `2^{M+M'} <= 2 * 2^{M(1+L/R)}`, from `ceil x < x + 1`.  That lone factor `2` is the **entire** price of the ceiling, and it is the leading `1 +` of the bound. |
| `slope_eq` | `1 + L/R - L = (1-(L-1)(R-1))/R`.  One line of algebra, and the door through which `RouteANormalForm.lean` walks. |

**The hinge.**  `slope_neg_iff`: the slope is negative **exactly** when `(L-1)(R-1) > 1`, i.e.
exactly when `A(alpha) < 1` (`QuadSetup.slope_neg_iff_routeAExponent_lt_one`).  That single
sign is the whole of "certified depths exist"; everything else in the file is bookkeeping.
Note also what is *not* used: the abstract half needs no property of `alpha` beyond
`alpha = 2^L`, so it is a statement about four real numbers and holds at every degree, exactly
as the note states it.

**Explicit, not asymptotic.**  `coverTotal_balancedDepth_lt_of_logb_le` takes no limit: a
single numeric inequality on `M` -- the affine bound below `log2 eps` -- already certifies.
At degree two, `QuadSetup.certificate_of_balancedDepth_bound` is the same statement with
`eps = 1/(2(2K+1))` folded in, which is the form Corollary 3 evaluates.

**Meeting the engine.**  `QuadSetup.cert_eq_coverTotal`: the certificate value of
`Covering.lean` is *exactly* `2(2K+1) * coverTotal` at `C = 1 + |beta|`, so Theorem 2(i)
applies to it verbatim and
`QuadSetup.exists_avoided_interval_at_balancedDepth` /
`QuadSetup.not_equidistributed_at_balancedDepth` re-prove `Criterion.lean`'s conclusion **by
the note's own route**, at a named depth.  One small coincidence worth recording: the additive
constant `1 + (1+rho)/(1-rho)` of the bound is exactly the quantity `QuadSetup.intBound` rounds
up -- the engine's integer-part budget and Theorem 2(i)'s constant are the same number.

**The Corollary 3 warning is visible in the statement.**  The slope `(1-(L-1)(R-1))/R` tends to
`0^-` as `A(alpha)` climbs to `1`, so the certified `M` grows like `1/(1-(L-1)(R-1))` and the
interval count `2^{M+M'}` like `2^{Theta(1/(1-A))}`.  Theorem 2 *proves* a gap once one is known
to exist; it must never be used to *find* one.  That is M4's job, and check `D10` measures the
blow-up: over the 221 firing Pisot numbers of the enumeration, the smallest predicted `M` among
those within `0.05` of the ceiling is `100`, while the largest among those comfortably clear of
it is `4`.

**Operational.**  `m2_thm2i_lean.py`, 10/10 verdicts at `mp.dps = 60`.  The three estimates and
the affine bound are swept over all 9287 Pisot numbers at ten depths, at *both* constants; the
largest excess of `log2 T` over the bound is `0.0`, so the bound is attained and not merely
valid.  `D7` checks the engine identity to `0.0` relative.  `D9` reproduces Corollary 3's own
pairs with `C_alpha`: `T(17,17) = 0.9877` at `2+sqrt5` (the note prints `0.987`) and
`T(751,1502) = 0.9994` at `X^3-8X^2-1`.  `D8` then locates the *Lean* engine's own first
balanced certified depth at `2+sqrt5`: `L = R` there, so the balanced ray is `(M,M)`;
`K = intBound = 3` and the factor `2(2K+1) = 14`; the affine bound guarantees `M = 75` and
direct evaluation first certifies at `M = 63`.  **`RouteA.lean` discharges `(70,70)`, which sits
between the two** -- deeper than the first crossing, shallower than the bound's guarantee, which
is exactly where a hand-chosen certificate should land.

**Dependency cone.**  `Nat.le_ceil`, `Nat.ceil_lt_add_one`, the `Real.rpow`/`Real.logb` API, and
Proposition 1.  `std3`, no citation, no dynamics.

## M2 Theorem 5 in Lean: the family that inhabits Route A (`RouteAFamily.lean`, 2026-08-27)

`RouteACeiling.lean` says where the criterion *cannot* fire, `RouteANormalForm.lean` says exactly
when it does, `RouteADepth.lean` says at what depth.  All three are about the shape of the
criterion.  Theorem 5 supplies its **inhabitants**: for `d ≥ 2` and `a ≥ 3` the trinomial
`p_{d,a}(X) = X^d - aX^{d-1} - 1` (`familyPoly`) is irreducible, has a unique root outside the
closed unit disc — real, in `(a, a+1)`, a Pisot unit of degree `d` — every conjugate has modulus
at most `(2/a)^{1/(d-1)}`, and for `a ≥ 2^{d+1}` the Route A exponent drops below one.

**Rouché is not used, because Mathlib does not have Rouché.**  The note counts the roots outside
the unit circle by Rouché on `|z| = 1`.  The Lean proof is a different, elementary one, and it is
the substance of the file:

| step | statement |
| --- | --- |
| the root equation | `‖z‖^{d-1}·‖z - a‖ = 1` (`norm_pow_mul_norm_sub`) |
| large roots | `‖z‖ ≥ 1` ⟹ `‖z-a‖ ≤ 1` ⟹ `‖z‖ ≥ a-1 ≥ 2` ⟹ `‖z‖^{d-1} ≥ 2` ⟹ `‖z-a‖ ≤ 1/2` ⟹ **`‖z‖ ≥ a - 1/2`** (`le_norm_of_one_le_norm`) |
| small roots | `‖z‖ < 1` ⟹ `‖z-a‖ ≤ a+1` ⟹ **`‖z‖^{d-1} ≥ 1/(a+1)`** (`inv_le_norm_pow_of_norm_lt_one`) |
| the budget | the product of *all* the moduli is `1`, because the constant term is `-1` |
| the count | two large roots give `(a-1/2)^{2(d-1)} ≤ (a+1)^{d-2} ≤ (a-1/2)^{2(d-2)}` — impossible at base `> 1` (`card_big_roots_eq_one`) |

Only **integer powers** occur, so there is no `rpow` and no complex analysis anywhere in the
count.  The second pass — from `a-1` to `a-1/2` — is load-bearing rather than cosmetic: with the
cruder bound the chain degenerates to `(a-1)² ≤ a+1`, i.e. `4 ≤ 4` at `a = 3`, and proves
nothing.  Check `F5` records exactly that.

**The same argument gives irreducibility.**  `minpoly ℤ α ∣ familyPoly d a` (ℤ is integrally
closed), the cofactor `r` is monic with `|r(0)| = 1`, and all its roots are roots of `p` other
than `α` — `α` being a *simple* root is again `card_big_roots_eq_one`.  So if `r` were
nonconstant its constant term would have modulus `< 1`.  Hence `minpoly ℤ α = familyPoly d a`
(`minpoly_eq_familyPoly`), and with it `familyPoly_irreducible`, `minpoly_natDegree_family`
(**degree exactly `d`** — the sense in which this is a family *in every degree*) and
`minpoly_coeff_zero_family` (**a unit**).

**(iii)** is short once (ii) is in hand: `L = log₂ α > log₂ a ≥ d+1` and
`(d-1)·R ≥ log₂(a/2) ≥ d`, so `1/L + 1/R < 1/(d+1) + (d-1)/d = (d²+d-1)/(d²+d) < 1`
(`inv_add_inv_lt_one_of_deg`, `routeA_family_lt_one`).

**(iv), `d = 2`: the conclusion is 10.61 itself.**  The member is a `QuadSetup`
(`familyQuad a ha`, `α = (a+√(a²+4))/2`), so the whole engine of the folder applies:
`familyQuad_routeAExponent_lt_one_iff` gives the threshold as an **iff** (`A < 1 ↔ a ≥ 4`, via
`RouteANormalForm.lean`'s unit case), and `familyQuad_not_equidistributed` /
`familyQuad_not_denseModuloOne` are **Problem 10.61 at `α_{2,a}` for every `a ≥ 4`** — an
explicit infinite family, machine-checked end to end.  `familyQuad_four_alpha` identifies the
first member as `2 + √5`, the capstone of `RouteA.lean`; `α_{2,3} = (3+√13)/2 = 3.3028` is the
last member that misses.

**(iv), `d = 3`: no calculus either.**  The note gets "exactly one real root" from the critical
values of `p'`.  That is not needed: dividing by `X - α` leaves the *real* quadratic
`X² + (α-a)X + (α²-aα)`, and since `α²(α-a) = 1` its discriminant is `1/α⁴ - 4/α`, negative for
free.  Negativity does both jobs — it forces the remaining pair to be non-real, and it computes
the modulus (`norm_sq_of_quadratic`): `‖z‖²·α = 1`, i.e. `ρ = α^{-1/2}`
(`norm_sq_mul_eq_one_cubic`).  Hence `A·log₂ α = 3` (`routeA_cubic_mul_logb`) — **the cubic
members sit exactly on the ceiling of M2 Proposition 4**, which `RouteACeiling.lean` proves is
`≥ d` — and `A < 1 ↔ α > 8 ↔ a ≥ 8` (`routeA_cubic_lt_one_iff`, `eight_lt_iff_of_mem_Ioo`).  So
the firing thresholds are exactly `a = 2^d` in degrees 2 and 3.

**Operational.**  `m2_thm5_lean.py`, 10/10 verdicts at `mp.dps = 60` over 91 `(d,a)` pairs.  Each
step of the count is checked *separately* rather than only its conclusion (`F2`, `F3`, `F4`), the
counting inequality is swept to `d < 40` and `a < 200` (`F5`), and the note's own §5 rows are
reproduced exactly (`F7`): `A(d=4,a=16) = 1.00329` misses and `A(4,17) = 0.98152` fires;
`1.00215 / 0.99323` at `d = 5`; `1.00111 / 0.99736` at `d = 6`.  `F8` and `F9` sweep the two
low-degree cases to `a < 60` and confirm `α_{2,3} = 3.3028 < 4 < 4.2361 = α_{2,4}` and
`α_{3,7} = 7.0203 < 8 < 8.0156 = α_{3,8}` — the latter being the cubic of M2 Corollary 3.  `F10`
cross-checks irreducibility with sympy.

**Dependency cone.**  `Polynomial.roots` and `Splits`, `minpoly` over an integrally closed
domain, the intermediate value theorem, and integer-power arithmetic.  `std3`, no citation.

## M2 Proposition 7 in Lean: the window is too wide, and X7 dies (`WindowDiam.lean`, 2026-08-27)

X7 (`plans/plan-1061.html` §7) was §7's cheapest idea: with `Δ = Σ_{j≥2} |α_j-1|/(1-|α_j|)` the
`ℓ¹` size of the conjugate shadow and `g = (α-2)/α` the first gap of `C(α)`, *if `2Δ < g` then
every orbit misses a fixed interval* — Problem 10.61 at `α` with no dynamics and no dimension
theory at all.  Proposition 7 says the hypothesis is never satisfied, and says so by an identity
rather than an estimate.  That is what makes the row dead rather than merely unpromising: an
estimate can be sharpened, an identity cannot.

**The abstract layer.**  For any `c : ℕ → ℝ` with `Σ|c_m| < ∞`, `windowOf c` is the set of subset
sums `{Σ_m c_m δ_m : δ ∈ {0,1}^ℕ}`.  The greedy words `posWord`/`negWord` hit both endpoints of
`[-Q, P]`, so

* `diam_windowOf` : `Metric.diam (windowOf c) = Σ_m |c_m|` — an **equality**.  M1 Lemma 3 had only
  compared the two endpoints; `Metric.diam` appears here for the first time in the root.
* `diam_windowOf_eq_two_mul_posSum` : `diam K = -(Σ_m c_m) + 2 posSum c`.  This is `|x| =
  2 max(x,0) - x` summed, and nothing else.
* `diam_windowOf_eq_neg_tsum_iff` : `diam K = |Σ_m c_m|` **iff** no `c_m` is positive.

**The conjugate layer.**  For a multiset `s ⊆ {‖z‖ < 1}` and `c_m = Re Σ_j (α_j-1)α_j^m`
(`conjCoef`), `hasSum_conjCoefC` runs one geometric series per conjugate, each contributing
exactly `-1`:  `Σ_m c_m = -card s`, whatever the conjugates are.  Taking the real part costs
nothing — for the conjugate multiset of a real algebraic number the sum is already real — and it
spares the file the closed-under-conjugation argument.  Hence `card s ≤ diam K ≤ Δ`
(`card_le_diam_windowOf_conjCoef`, `diam_windowOf_conjCoef_le`).

**The no-go.**  `gap_lt_one`: `g < 1` for *every* `α > 0`.  So `2Δ ≥ 2 diam K ≥ 2(d-1) ≥ 2 > 1 > g`
and `not_x7Criterion` holds — with `not_x7Criterion_of_natDegree` stating it in the degree (a
monic integer polynomial of degree `d ≥ 2`, all roots but `α` inside the unit disc), and
`gap_lt_two_mul_diam_windowOf` the sharper form that spends only `diam K`.  For the record,
`cantorSet_inter_gapIoo_eq_empty` confirms the criterion was comparing against something real:
`C(α)` misses `(1/α, (α-1)/α)`, whose length is `gap α`.

**Zero margin.**  The file constructs `unitQuad a` (`a ≥ 3`), the larger root of `X² - aX + 1`, as
a `QuadSetup`; `unitQuad 4` is `2 + √3` (`unitQuad_four_alpha`), M0's first certified `α`.  There
`β = 1/α ∈ (0,1)`, so every `c_m = (β-1)βᵐ` is negative and

    Δ  =  diam K  =  d - 1  =  1        (`conjDelta_unitQuad`, `diam_windowSet_unitQuad`)

— **all three at once**, so every inequality of the note's chain except the last is an equality on
this family.  The last one degenerates too: `tendsto_ratio_unitQuadSeq` sends `2Δ/g` to `2` along
it.  The constant `2` is therefore the exact infimum of the failure ratio, approached and never
attained; the enumeration edge `X² - 22X + 1` behind the sweep's `2.20` is itself a member.

**Two corrections to the note.**  (a) The failure factor is `≥ 2/g`, not `> 2/g`: it *equals*
`2/g` wherever `Δ = d - 1`, which the family shows is a nonempty condition.  What survives
strictly is `2Δ/g > 2`.  (b) `Δ = diam K` is not special to degree two.  At `d = 2` it is
unconditional (`diam_windowSet_eq_conjDelta`) because one conjugate leaves the triangle inequality
nothing to lose; above it, `Δ = diam K` holds exactly when every conjugate is real and they share
a sign — 92 of the 2020 cubics of the enumeration, and none of the 6827 quartics.

**Operational.**  `m2_prop7_lean.py`, 10/10 verdicts at `mp.dps = 60`.  `P1` checks
`Σ_m c_m = -(d-1)` over all 9287 enumerated Pisot numbers from the closed form
`Σ_j (α_j-1)/(1-α_j)`, and finds deviation `0.0` in both the real and the imaginary part.  `P2`–`P4`
recompute the window on 1514 rows in float64 with an explicit geometric tail bound (`≤ 9.9e-14`),
checking the identity, the equality case, and that 4000 random words per row never beat the greedy
ones.  `P5`–`P7` sweep the chain, the criterion and the sharper criterion over all 9287:
`min 2Δ/g = 2.20 / 4.81 / 8.34` at degrees 2/3/4, reproducing the note, and 20000 sampled points of
`C(α)` at 24 different `α` all avoid the gap interval.  `P8` establishes the `Δ = diam K`
characterisation above, `P9` the attainment family, `P10` the limit.

**Dependency cone.**  `tsum`, `Metric.diam`, one geometric series, and `Multiset.induction_on`.
No dynamics, no dimension theory, no citation.  `std3`.

## M2 Proposition 8 in Lean: block recoding is exactly neutral (`BlockRecoding.lean`, 2026-08-27)

Gate **G-R** (`note-1061-GR.html`, 2026-08-23) opened a degree of freedom on the quadratic-unit
class: 10.61 may be proved along a *single* arithmetic progression `n = 0 (mod p)`, i.e. in base
`alpha^p`, licensed by [BM86] Th. XIII.  Proposition 8 says the freedom is worthless to Route A --
and to every criterion of Route A's kind -- and the note proves it in one sentence, *every `p`
cancels*.  A one-sentence proof is exactly the case where the Lean file has to be about something
else, so this one is about the **action**, not the cancellation.

**The action.**  A criterion of this kind sees three numbers and nothing else,
`(log #alphabet, log base, log 1/contraction)` (`RatioData`), and block recoding multiplies all
three by `p` (`RatioData.block`, an instance of `RatioData.scale` -- `blockData_eq_block` below is
what earns that sentence).  Write `L = log base / log #alphabet` and
`R = log(1/contraction) / log #alphabet`.  Then `L` and `R` are invariant (`L_scale`, `R_scale`),
and every quantity the note and the plan list is a function of the pair:

| | |
| --- | --- |
| `A = 1/L + 1/R` | `expo_eq_inv_add_inv` |
| `dim C(alpha) = 1/L` | `dim_eq_inv_L` |
| entropy deficit `log 2 < log alpha` | `EntropyDeficit`, i.e. `L > 1` |
| Mendès-France `rho < 1/2` | `MFCriterion`, i.e. `R > 1` |

So the plan's four named invariants are not four cancellations but corollaries of **one** no-go:
`apply_ratios_block` -- *for every* `F`, `F` of the recoded ratios equals `F` of the original
ratios.  Nothing about `F` is assumed, so the statement covers criteria nobody has written down.

**The converse, which is what makes it a no-go and not an observation.**  `ratios_eq_iff` proves
that two ratio data have the same `(L,R)` **exactly when** one is a rescaling of the other: the
fibres of `ratios` *are* the recoding orbits (the real interpolation of the integer `p`).  Hence
`eq_of_ratios_eq`: a quantity that cannot tell a system from its recodings cannot tell apart two
systems with the same `(L,R)`.  Factoring through the ratios is therefore not a convenient
sufficient condition for neutrality -- it is what neutrality *is*, and the note's closing sentence
("only an argument that sees digit *positions* can spend that freedom") is its contrapositive.

**One correction to the note this forces.**  Proposition 8 says the no-go covers "any criterion
that is a function of the ratio data `(log #alphabet, log base, log 1/contraction)`".  As written
that is too generous: a function of the *raw triple* need not be neutral, because recoding scales
the triple.  `log base > 1` is a function of it, and at `alpha = 1+sqrt2` (`log alpha = 0.8814`)
it is false before recoding and true after recoding at `p = 2`.  What is needed -- and, by
`ratios_eq_iff`, what is also sufficient -- is that the criterion be a function of the two
*ratios*, equivalently that it be scale-invariant.  All four of the named criteria are; the
distinction is invisible in the note because it never writes down one that is not.  The Lean file
therefore states the invariance of the two order criteria for *positive* scalars
(`entropyDeficit_scale`, `mfCriterion_scale`) and of the two numerical ones for nonzero scalars,
which is the exact homogeneity each one has.

*A second, smaller one:* the note's list "`dim_B C(alpha) = log2/log alpha` and the entropy-deficit
ratio" has three entries and two contents -- the entropy-deficit *ratio* is `log2/log alpha`, i.e.
the dimension again.  The plan's own anchor (xvii)(b) has the four genuinely distinct invariants,
and it is those the file proves: `A`, `dim`, the entropy deficit as the *predicate* `L > 1`, and
Mendès-France's `rho < 1/2` as `R > 1`.

**The recoded contraction is earned.**  This is the whole point of the note's check P8: the
recoding's base and contraction must be `alpha^p` and `rho^p` *of the actual power polynomial*.
`traceSeq` is the integer trace ladder `t_n = alpha^n + beta^n` -- `BB61/Ladder.lean`'s `lad`
started at `(2, a)`, with `traceSeq_cast` the two-step induction that identifies it -- and `power`
builds `X^2 - t_p X + (-b)^p` as a genuine `QuadSetup`, `one_lt` and `conj_lt` included.
`power_beta` then proves that its **second root is `beta^p`**, which is a fact about that
polynomial and not a definition; `blockData` is defined from *its* roots, and `blockData_eq_block`
is the theorem that reading base and contraction off it lands on `p ·` the original triple.
Proposition 8's display is `blockRecoding_expo`:

> `log 2^p / log alpha^p + log 2^p / log(1/rho^p) = A(alpha)`,

with the left side computed from the power polynomial's own roots.  The coverage consequence is
`routeACriterion_blockData_iff_four_lt`: on quadratic units the recoded criterion fires **exactly
on `(4, infinity)`, at every order `p`** -- M2 Corollary 6 transported through Proposition 8, so
the G-R freedom buys Route A not one new `alpha`.  `silver_not_routeACriterion_blockData` says it
at the one `alpha` the whole programme is about.

**Grounding.**  `dimH_cantorSet_blockData` and `upperBoxDim_cantorSet_blockData` check the recoded
`dim` against `Hausdorff.lean` and `BoxDim.lean`: the recoded description computes the dimension
of the *same, unchanged* set `C(alpha)`.  Recoding is a change of description, not of object --
which is exactly what distinguishes it from the trap.

**The trap, and the falsification test.**  Raising the base to the `p`-th power *without*
enlarging the alphabet is a different operation and a seductive one: `routeAExponent_power` gives
`A(alpha^p) = A(alpha)/p`, so by `exists_power_routeAExponent_lt_one` it eventually drives the
criterion below `1` at **every** `alpha` -- including `alpha = 1+sqrt2`, where Route A provably
does not fire (`silver_not_routeAExponent_lt_one`, M2 Cor. 6, against
`exists_silver_power_routeAExponent_lt_one`).  It proves nothing about 10.61 because the binary
system at base `alpha^p` is a *thinner* Cantor set -- the words of `C(alpha)` constant on blocks
of length `p` -- and not a recoding of `C(alpha)`.  The pair of theorems is the test any future
attempt to spend the G-R freedom must pass: **an argument that survives block recoding unchanged
has not spent the freedom, and an argument that gains from `alpha -> alpha^p` has changed the
set.**

**Operational.**  `m2_prop8_lean.py`, 10/10 verdicts at `mp.dps = 60`.  Because the note's proof
is one sentence, the script checks the *translation* rather than the conclusion, one check per
group of declarations: `P1` the integer ladder against `alpha^n + beta^n` on all 440 quadratics
for `n = 0..20`; `P2` that `X^2 - t_p X - (-(-b)^p)` really is monic with integer coefficients and
has `alpha^p > 1` as a root; `P3` that its second root is `beta^p` -- and that the *naive* reading
(keeping `rho`) is wrong by up to `0.731`, which is why the note recomputes from the actual
polynomial; `P4` the scaling identity and `P5` Prop. 8's display on all 9287 enumerated Pisot
numbers at eight exponents (deviations `5.0e-60` and `3.8e-56`); `P6` the other three invariants,
with neither the entropy deficit nor `rho < 1/2` flipping anywhere; `P7` the fibre theorem in both
directions, plus the raw-triple counterexample above; `P8` the note's own three instances by name -- `(2+sqrt3)^2` is `X^2-14X+1`,
`(1+sqrt2)^2` is `X^2-6X+1`, `(1+sqrt2)^3` is `X^2-14X-1`, and `A` recomputed from each power
polynomial's own roots with alphabet `2^p` equals `A(alpha)`; `P9` the unit coverage (36 of the 40
quadratic units fire, 4 do not, at every exponent); `P10` the trap, with the block-constant sliver
identity verified to `7.8e-62` and its *properness* certified -- the word `10^inf` of `C(alpha)`
sits `2.4e-01` from every depth-14 point of `C(alpha^2)`, against a tail bound of `4.4e-06`.

**Dependency cone.**  Elementary algebra on three reals, one two-step induction, and `Real.log_pow`
-- plus `Hausdorff.lean`/`BoxDim.lean` for the grounding alone.  `std3` throughout, and **no
citation**: [BM86] Th. XIII is what makes the freedom *available*, and nothing here consumes it,
because the statement proved is that the freedom is *neutral*.

## M2 Proposition 9 in Lean: X8 is sound, complete on Route A's range, and strictly larger (`Raster.lean`, `GapSqrtThree.lean`, 2026-08-27)

M2 Proposition 9 has two halves, and they are formalised in two files.

**Half one: the procedure (`Raster.lean`).**  M0 §6 built the X8 procedure -- over-approximate
`C(alpha)` and `K` by their depth-`(M,M')` point sets fattened by the tail bounds, rasterise the
difference on `G` bins, dilate, look for a run of empty bins -- and Proposition 9 says that on
Route A's range it is *guaranteed* to find one, at a resolution nameable in advance:
`T := T(M,M') < 1/3` and `G >= 2^(M+M'+3)/(1-3T)`.

The raster is modelled exactly rather than approximated: `bin G i = [i/G, (i+1)/G)` is the fibre
of `binIdx G x = floor(x*G)`, so the bins partition `R` for free and every statement below is
about that partition.  Two facts then carry the file, and only two:

* `subset_occSet` -- a raster **never loses a point**, `S ⊆ occSet G S`;
* `occSet_dist` -- a raster **gains less than one bin**, `x ∈ occSet G S -> ∃ y ∈ S, |x-y| < 1/G`.

From the first, `runSet_inter_occSet_eq_empty`: **soundness**, M0's direction, that a reported run
of empty bins is a true gap.  This is the step that makes X8 a *proof* method and not a heuristic,
and M0's note asserts it without proving it here.  From the second, `exists_zeroRun`:
**completeness at a given resolution**, that an interval of length `b-a` missing the occupied set
contains a run of `ell >= (b-a)*G - 2` empty bins whose own interval sits inside it.  The `2` is
the alignment loss, one bin at each end, and it is the *only* loss -- there is no hypothesis on
`a`, `b` or `G`.  `inter_occSet_eq_empty_of_shrink` adds the implementation's over-approximation
`e`, `exists_certified_gap` composes the three at `(b-a-2e)*G - 4`, and `prop9` is the
Proposition, `gap_pos_of_resolution` supplying the note's own arithmetic `2^3 > 6`.

**One correction, in the harmless direction.**  The note allows `O(1)` bins, "`<= 3/G` on each
side of each arc", so `6/G` in total.  The accounting above spends `1/G` per side for the
rasterisation and one bin per side for the alignment: `4/G` suffices, and the surviving run is at
least *half* the guaranteed gap rather than a quarter.  Both are proved -- `gap_pos_of_resolution`
carries the note's `6/G` form as well -- so the displayed choice of `G` is verified as written and
the sharper constant is a bonus, not a substitution.

§5 instantiates on the quadratic engine of `Covering.lean`: `covSet M M' K` is what the procedure
rasterises, `orbitFract_mem_covSet` is `exists_cand_near` (it really does contain every
`{xi alpha^n}`), `X8Cert` is the certificate, `not_equidistributed_of_X8Cert` turns a certificate
into 10.61 at `alpha`, and `exists_X8Cert_of_cert` is **Route A ⊆ X8**.  One small repair was
needed on the way: `Covering.lean`'s `exists_avoided_interval` proves the gap against the
*covering* and then throws that away, keeping only the statement about the orbit; the procedure
needs the covering version, so `exists_gap_in_covSet` restates it.

**What is taken as a hypothesis.**  Exactly what the note's proof takes: the true gap of Theorem
2(ii) and its length `(1-T)2^-W`.  Theorem 2(i) is `RouteADepth.lean`; the *quantitative* form of
2(ii) -- that `N` closed arcs of total length `T < 1` leave an open arc of length `>= (1-T)/N` --
is a statement about the interval structure of the complement and is not formalised.  Its
qualitative form is, and suffices for the containment, at the cost of choosing `G` *after* seeing
the gap rather than in advance.  That is precisely the distance the note's own closing paragraph
measures: `2^42` guaranteed against `2^21` observed.

**Half two: the converse (`GapSqrtThree.lean`), and an unbudgeted result.**  Proposition 9's
second sentence is that X8 fires strictly below Route A's ceiling, at `alpha = 2+sqrt3`, where
`A = 1.0526 > 1`.  M0 §6.2 found the certificate at depth `(11,9)` on `2^21` raster bins.  **It is
in fact a depth-`(2,2)` fact, exact in `Z[sqrt3]`** -- sixteen closed intervals, nine distinct --
and that is what is proved.

Why depth two is enough, and why it is `2+sqrt3` that allows it: the minimal polynomial is
`X^2-4X+1`, norm `+1`, so `beta = 1/alpha`.  Hence the window weights `|c_m| = (1-beta)beta^m` and
the Cantor weights `(alpha-1)alpha^-(m+1)` are the **same sequence**, the confinement set is
`(C+C) mod 1`, and both factors truncate at depth `2` with the same **one-sided** error
`beta^2 = alpha^-2 = 7-4sqrt3 = 0.0718`.

That one-sidedness is the whole trick, and it is the reason the existing engine cannot see this
certificate: `Covering.lean`'s `delta M M'` is the *two-sided* bound
`alpha^-M + (1+|beta|)|beta|^M'/(1-|beta|)`, which at `M = M' = 2` is `0.196` -- seven and a half
times the half-gap.  `tPart_expand` and `neg_sPart_expand` supply the sharp one-sided expansions
instead, and the past one needs `neg_sPart_mem_Icc`, the sharp window bound `S_n ∈ [-1,0]`, which
is M2 Proposition 7's `diam K = d-1 = 1` in recursion form (`|beta| + |beta-1| = 1` exactly, so
`[-1,0]` is invariant).  The generic bound `(1+|beta|)/(1-|beta|)` is `sqrt3` and is useless here.

The covering `covThree` is then nine intervals `[w2*p + w1*q, +2(7-4sqrt3)]` with `p,q ∈ {0,1,2}`,
`w2 = sqrt3-1`, `w1 = 3sqrt3-5`, times two integer shifts, and
`covThree_inter_gapIoo_eq_empty` is eighteen exact comparisons.  **Two of them are equalities**:

    2(sqrt3-1) + (14-8sqrt3) = 12-6sqrt3 = 1 + gapLo
    2(sqrt3-1) + (3sqrt3-5)  = 5sqrt3-7  = 1 + gapHi

so the covering *touches* the gap at both ends and the openness of the gap is load-bearing.  There
is no numerical tolerance anywhere in the certificate.

The gap is `(11-6sqrt3, 5sqrt3-8)`, of length `11sqrt3-19 = 0.0525589`, at `0.60770` -- M0 §6.2's
`0.052558` at `0.6077`, and `m0_verify_gap.py` reproduces it independently at `0.052558`.

**The consequence M2 did not ask for.**  `gap_two_add_sqrt3` is one avoided interval, uniform in
`xi ∈ C(alpha)` and in `n`; `two_add_sqrt3_not_denseModuloOne_of_gap` and
`problem_10_61_two_add_sqrt3_axiom_free` follow.  The latter is **Problem 10.61 at `2+sqrt3` with
no citation and no axiom beyond the standard three.**  `Floor.lean` proves the same statement
through M3's entropy floor and the root's single cited axiom `LY.entropyRate_floor`
(`CITED/LedrappierYoung.lean`, resting on [You82]/[LY85]/[BPS99]).  The two proofs are independent
and agree, so **the root's headline unconditional result no longer rests on a citation.**  Both
are kept: the pressure lane is the general machine and the certificate is one `alpha`.

`exists_zeroRun_two_add_sqrt3` re-reads the certificate as the *output* of `Raster.lean`'s
procedure -- at every resolution `G >= 100` the raster reports a nonempty run of empty bins whose
interval misses every orbit point; the threshold is `4/(gapHi-gapLo) = 76.11`.  And
`routeA_subset_X8_strict` is **Route A ⊊ X8**, Route A's blindness being
`not_routeAExponent_lt_one_twoAddSqrt3`: on the quadratic units `A(alpha) < 1` is exactly
`alpha > 4` (M2 Cor. 6), and `2+sqrt3 = 3.7320508`.

**Operational.**  `m2_prop9_lean.py`, 10/10 verdicts at `mp.dps = 60` -- 400 for the orbit test,
since `{xi alpha^n}` at `n = 250` needs about 145 digits merely to exist.  `P1` the raster model
(bins really are the fibres, `S ⊆ occSet(S)`, and the gain never reaches `1/G`); `P2` completeness
with the alignment loss never exceeding 2 bins over 6000 random `(G,a,b)`; `P3` the composed
accounting over 4000 random covers; `P4` the note's arithmetic in **exact rationals** (the bounds
are *attained*, so floating point would report a spurious failure); `P5` the one-sided depth-2
remainders over 3000 random `(word, n)`, against the engine's unusable `delta 2 2`; `P6` the nine
endpoints and the width in exact `Z[sqrt3]`; `P7` the eighteen comparisons with the two zero
margins located by name; `P8` the two gaps against M0's own FFT-free method, **depth 1 giving no
gap at all** -- so depth 2 is the first depth that certifies -- and zero landings in 20000 orbit
points; `P9` the run lengths at `G = 100`, `2^12` and M0's `2^21`; `P10` `A(2+sqrt3) = 1.052649`
against the enumeration's own column, with the unit criterion `alpha > 4` exact on all 40.

**Dependency cone.**  `Raster.lean`: `Int.floor`, `Int.ceil` and arithmetic, plus `Covering.lean`
and `Confinement.lean` for §5.  `GapSqrtThree.lean`: the two recursions of `Splitting.lean`, two
`linear_combination`s over `Z[sqrt3]`, and an eighteen-case `interval_cases`.  `std3` throughout,
**no citation**, no `native_decide`, and no `decide` over anything large.

## R2b: the entropy-free dual minimiser, and the three vetoes (`r2b_ergodic.py`, `r2b_orbits.py`, 2026-08-27)

Work package R2b of `plan-BB61-counterexample.html` sec 6.3, gate **can it certify
`K_H = empty` at any `H`?**  Answer: **no, and now provably not at any `(H, L)` the folder
can reach** -- and because the criterion is *complete*, that is a measurement of
`K_H != empty` rather than a defect of the machine.  Full account in `note-1061-R2b.html`
(67 claims re-verified by `r2b_checknote.py`).

**Theorem 1 (the observable).**  With `Phi_h(mu) = int e(hF) dmu`,

    nu_H := min_{mu in M(sigma)} max_{1 <= h <= H} |Phi_h(mu)| / h

is non-decreasing in `H`; `nu_H > 0` iff `K_H = empty`; and `nu_H > 0` for a single `H`
proves 10.61 at `alpha` -- with no entropy, no `h_min`, no Ledrappier-Young.  The weights
`1/h` are the shape of the truncation error, which is what makes this the observable and
not one of a family.

**Theorem 2 (the machine).**  For the window observable `F~`, `psi_a(F~)` is an edge weight
on the order-`L` de Bruijn graph, and

    max_{mu} int psi_a(F~) dmu  =  max cycle mean ,
    lambda <= max_e (w_e + p_head - p_tail)   for any node potential p .

That is `Window.pressure_ub`'s own Collatz-Wielandt argument in the **max-plus semiring**:
the power iteration `v'(u) = max_j (w(2u+j) + v((2u+j) mod 2^L))` brackets `lambda` on both
sides at every step, and `howard()` terminates at the exact value with an exact bias.
Since `max <= sum`, `beta <= P`: this fires no later than R2a's row-1 pressure test, and
the gap between them is the entropy the pressure route pays.  Checked against Karp's
`O(VE)` algorithm on twelve random graphs to `2.6e-14`.

**Theorem 3 (soundness AND completeness).**  With `tau(a) = delta_bound(W, a)`,

    kappa(a) := -max_mu int psi_a(F~) dmu  >  tau(a)   ==>   K_H(F) = empty ,

both sides homogeneous of degree one, so on `sum_h h|a_h| = 1` the supremum of `kappa` is
`nu~_H` and the criterion reads `nu~_H > 2 pi eps_L` -- geometrically, the rotation set
misses the truncation polydisc.  And `|nu_H - nu~_H| <= 2 pi eps_L`, so **`K_H != empty`
forbids the criterion at every window depth.**

### The three vetoes

  * **R1b.**  `mu in K_{H0}` gives `nu_H <= 1/(H0+1)` for every `H`.  R1b's `H0 = 64`
    certificate therefore kills `H <= 64` at any depth, and prices everything above it.
    The two work packages are in direct tension: R1b's success prices R2b out.
  * **Bernoulli.**  `max_h |Phi_h(Bern)|/h = 1.5321e-2` at `1+sqrt2`, **constant in `H`**
    (the maximum sits at `h = 3`).  So `L <= 14` is dead at every degree -- and R2a's and
    R1b's whole ladders were run at `L = 12, 14`.  `L = 16` is the first window that even
    permits the question.
  * **The orbit hull.**  `nu_H <= nu^(q)_H`, the flattest convex combination of Bernoulli
    and the periodic orbits of period `<= q`.  At `H <= 16` this reaches `1e-12`: an
    explicit member of `K_H` built out of periodic orbits.  A witness inside the polydisc
    blocks EVERY direction at once, and one exists at every `(H, L)` with `H <= 256`,
    `L <= 22`.

        nu^(q)_H, true Phi, no window
             H     q<=4       q<=6      q<=8     q<=10     q<=12     q<=14
             8  1.60e-2  2.98e-3   7.70e-7   1.29e-12  1.38e-12  1.45e-12
            16  1.61e-2  3.14e-3   2.32e-3   2.42e-06  3.77e-11  3.80e-12
            32  1.60e-2  3.29e-3   2.75e-3   4.66e-04  2.39e-05  6.90e-06
            64  1.60e-2  3.34e-3   2.55e-3   1.26e-03  3.68e-04  1.77e-04
           128  1.60e-2  3.35e-3   2.63e-3   1.15e-03  5.53e-04  2.70e-04

**The price.**  Firing at degree `H` needs `2 pi eps_L < nu_H`, and `eps_L ~ alpha^(-L/2)`,
so `2^L ~ nu_H^(-2 log2 / log alpha) = nu_H^(-1.5729)`.  The measured `nu^(14)_128` already
demands `L >= 24.4`, i.e. `2.2e7` states -- five thousand times R2a's `L = 12` machine --
and that is a *lower* bound on the price.  Best `kappa/tau` anywhere in the folder:
`9.50e-4`, short of `1` by a factor **1053**.

### Which half was the bottleneck

Not the evaluator.  R2a's own row-1 direction, re-priced exactly: `beta = -0.0265` at
`L=12` but `+0.880, +0.805, +0.821` at `L = 14, 16, 18` -- converging, so the `L=12`
firing IS the truncation, measured (the real error is `0.85` against a certified
`tau_12 = 27.8`, i.e. M4 Prop. 3 is loose by `33`).  At `L=12, H=128` the entropy-free
certificate fires where the pressure one from the same generator does not.  But the
Frank-Wolfe search with the exact oracle does **not** find a certifying direction at
`H = 120` in 200 iterations, where `minimize_pressure` finds one in a single L-BFGS run
and is never improved on afterwards.  **Pressure proposes, max-plus prices.**

**Trust rule, sharpened.**  For anything transferred to the true `F` the binding constant
is `2 pi`: mode `h` is informative only while `2 pi h eps_L < 1`, i.e. `H < 1/(2 pi eps_L)`
-- `15.8` at `L=12`, `38` at `L=14`, `91` at `L=16`, `221` at `L=18`.

### By-product: periodic orbits are a better pool than M7's

The generators are a pool in R1b's sense and a far cheaper one -- no stationary solve, no
rounding repair, no window, enclosure below `1.3e-12` from `orbit_phi_true`.  Fed to
R2a's Theorem 1' (`r2a_margin.margin`, unmodified) they certify `K_H != empty`:

    alpha           H   q<=10     q<=12     q<=14    R2a's M7 pool
    1+sqrt2        32   2.22e-3   1.65e-2   1.89e-2   2.00e-3      (9.5x)
    1+sqrt2        64   --        5.91e-3   1.19e-2   6.06e-4     (19.6x)
    (3+sqrt5)/2    32   1.98e-3   5.34e-3   5.60e-3   certified
    (3+sqrt5)/2    64   --        --        2.30e-3   REFUTED (pool too small)
    (3+sqrt13)/2   64   --        6.40e-3   7.47e-3

**R1b's one refutation is closed, positively**: at `(3+sqrt5)/2, H=64` the period-`<=14`
hull certifies `K_64 != empty` where the M7 pool was proved too small.  It needs the period
bound -- `q <= 10` and `q <= 12` both fail there -- so the venue really is the harder one.

### Convention (a self-check found it)

`Window` indexes the `(L+1)`-block so that bit `b` is the position `b - N`, while
`circ_from_word` puts `word[i]` in the MOST significant bit.  So the window reads a word in
the opposite direction from the series of `orbit_F_true`, and `phi_orbit(lw, w)` is the true
`Phi` of the orbit of the **reversed** word.  Nothing depends on it: reversal permutes the
necklaces among themselves, so the hull of all orbits of period `<= q` is the same set
either way, and Bernoulli is symmetric.  Both halves are pinned by self-checks.

### Lean

**DONE: `BB61/CycleMean.lean`, std3, sorry-free, no new numerical data.**  `Pressure.lean`
already carries `cert : bb * (w0 s * vv (t0 s) + w1 s * vv (t1 s)) <= aa * vv s` by `decide`;
replacing the sum by a maximum turns it into an ergodic-optimisation certificate, and
`max <= sum` means the max-plus version is *implied* by the existing one at the same
potential, so the same `decide` carries both.  `Cert` (the max-plus hypothesis, arbitrary
state type), `cert_of_sum` (**depends on no axioms at all** -- it IS `beta <= P` with the
entropy named), `walk_le` (telescoping induction), `cycle_le` (endpoint cancels since `vv`
is positive), `cycle_le_real` (`prod w <= (aa/bb)^n`), and the instance
`TwoAddSqrt3.cycle_prod_le`.  Six new `#print axioms` lines in `AxCheck.lean`, all standard
three.  The folder's first entropy-free certificate.  Still open: the cycles-to-measures
bridge, shared with `PressureCriterion.lean`.

Files: `r2b_ergodic.py` (24 self-checks; `--selfcheck`, `--ladder`, `--nu L H q`),
`r2b_orbits.py`, `r2b_checknote.py` (67 claims); recorded `r2b_ergodic.json/.log`,
`r2b_fwflat.json/.log`, `r2b_hybrid.json/.log`, `r2b_orbits.json/.log`.

## R2d: the orbit hull as a pool (`r2d_hull.py`, 2026-08-27)

Work package R2d of `plan-BB61-counterexample.html` sec 12, gate **a better `m(H)`, and
`H_flat, H_ent` pushed past 64 at all three units**.  Answer: **both halves met**, and the
second one by a pool that is neither R2b's nor M7's.  Full account in `note-1061-R2d.html`.

**Theorem 1 (the generators are the Lyndon words).**  A periodic orbit is a rotation class
of a *primitive* word, so the distinct orbits of period `<= q` are the Lyndon words of
length `<= q` (Duval, `O(1)` amortised each).  R2b's `necklaces(q)` lists an imprimitive
word once per length it divides -- 2616 rows for 2538 measures at `q = 14`.  The duplicates
cost: Theorem 1' has `R <= 1/sum_j g_j`, so a repeated column raises the denominator and
adds no hull.  Deleting them is worth `1.031x` at `H = 8` and `1.028x` at `H = 64` -- an
improvement obtained by making the pool SMALLER, which nothing else in the folder does.

**Theorem 2 (the two enclosure engines are the same object).**

    orbit_phi_true(alpha, w, H)  ==  phi_fl(circ_from_word(L, w), 1..H, J, M)

to `6.2e-15` at all three units, against a claimed radius of `1e-12`; on the REVERSED word
they differ by `0.9`.  Two engines with no shared code -- two geometric series with
`math.fsum`, against R1a's forward pass over the order-`L` de Bruijn graph.  So orbit rows,
M7 rows and Bernoulli rows may be stacked into one pool, and the orientation of the orbit
series is pinned externally.  (The flip R2b documented is between the orbit series and the
*window's* block encoding, not between it and R1a.)

**Corollary (the reciprocal unit, new).**  If `abar = 1/alpha` -- `x^2 - Ax + 1`, so
`(3+sqrt5)/2`, `2+sqrt3`, ... -- then `c_m = -(alpha-1) alpha^-(m+1)` and

    F(omega) = sum_{j>=1} (alpha-1) alpha^-j (omega_j + omega_{1-j}) ,

which the flip `iota: omega_i -> omega_{1-i}` fixes exactly (checked to 0.0 on the seven
shifts of 0010111).  Measured: of the 747 Lyndon words of period `<= 12`, the number with
`Phi(w) = Phi(reverse w)` to `1e-12` is **747 at `(3+sqrt5)/2`** against 293 at `1+sqrt2`
and 277 at `(3+sqrt13)/2`.  Since `iota sigma iota = sigma^-1`, `iota_*` preserves `M(sigma)`,
every `Phi_h` and the entropy: at a reciprocal unit the whole problem carries a `Z/2`
symmetry, and reversal-paired Lyndon words carry the SAME `Phi`, so the orbit pool has
about half as many distinct vertices there as its row count.  **This is why `(3+sqrt5)/2`
is the hard unit for every pool the folder has built.**

**Theorem 3 (what the ladder measures).**  `Phi_H` is affine and weak-* continuous and
`M(sigma)` is convex compact, so `R_H := Phi_H(M(sigma))` is a compact convex body -- the
rotation set -- and `K_H != empty` iff `0 in R_H`.  Periodic measures are weak-* dense, so
the orbit hulls INCREASE to it: `rho(q,H) ↑ rho_inf(H)`.  The M7 pool converges to nothing
in particular; its Farkas loop has no limit that is an object of the problem.

*Corollary tying R2d to R2b.*  `nu_H` (R2b) measures how far `0` is OUTSIDE `R_H`,
`rho_inf` how far INSIDE; at most one is positive.  So every ladder-A row with `delta > 0`
proves **`nu_H = 0` exactly**, where R2b had only `nu_128 <= 2.70e-4` from the same
generators -- and R2b's criterion provably cannot fire there at any window depth.

### The two halves of the gate

**(a) `m(H)` is better, and better in the way that matters.**  Theorem 1' at the maximin
weights, same theorem on both pools:

| alpha | delta, M7 pool (H=64) | delta, orbit hull (H=64) | gain |
|---|---|---|---|
| `1+sqrt2` | `5.402976e-4` | `1.181447e-2` | `21.9x` (`19.5x` over R2a's post-loop `6.0570e-4`) |
| `(3+sqrt5)/2` | separated from 0 | `2.611026e-3` | infinite -- R1b's refutation |
| `(3+sqrt13)/2` | `2.489064e-4` | `7.272943e-3` | `29.2x` |

The M7 entry at `1+sqrt2` reproduces R2a's round-0 value `5.4030e-04` to the last digit
through a different linear programme (`rmax_sub`, the `m`-free reformulation -- R2a's own
`weighted_maximin_lp` builds a dense `m x (m+1)` block, 620 MB at `m = 8800`).

And the DECAY halves.  In the scale-free reading `rho^ = sqrt(2H) rho`:

    H =         4      8     16     32     64    128
    1+sqrt2   0.9492 1.1535 1.1636 1.1734 1.1764 1.1622   gamma_rho: .51 .50 .49 .52
    root13    0.7061 0.7255 1.1331 1.1449 1.1600 1.1716   gamma_rho: .85 .49 .48 .49
    golden2   0.5006 0.6066 0.6474 0.4232 0.3275   --     gamma_rho: .41 1.12 .87
    M7, L=12  0.3361 0.2982 0.2217 0.1800 0.0958   --     gamma_rho: .93 .80 1.41

`gamma_rho = 0.50 +- 0.02` at the two NON-reciprocal units against R2a's `0.95` on the M7
pool: the depth falls exactly at the rate the ambient scale grows, i.e. **the hull does not
thin at all**.  The exception is `golden2`, the reciprocal unit, where `rho^` falls by a
factor 2 from `H=16` to `H=64` -- either because the pool is effectively half the size
there (reversal-paired orbits carry the same `Phi`) or because `R_H` is genuinely thinner
at that `alpha`.  This run does not separate the two, but the second is the folder's own
expectation: `(3+sqrt5)/2` is where the certificate lane is cheapest and where 10.61 is
already proved by the W4 enclosure.  **The one unit where `rho^` decays is the one unit
where the criterion is close to biting.**
R2a's `rho ~ H^-0.95` was a property of the pool, and the "thinning hull" reading of gate
G-2 should be withdrawn.  (Row 2 still fires -- `m(H)` does not hit 0 and does not collapse
super-polynomially -- but for a weaker reason than R2a's number suggested.)

**(b) `H_flat` and `H_ent` past 64 at all three units.**  The missing one was
`(3+sqrt5)/2` at `H = 64`, R1b's single recorded REFUTATION.  Three pools there:

| pool | m | delta | `E_64 >=` |
|---|---|---|---|
| M7 | 1025 | `0 not in conv`, gap `5.471e-2` | nothing |
| orbits + Bernoulli(p) | 8807 | `2.596e-9` | `0.113757` |
| **union**, `q <= 16` | 9832 | `2.607e-9` | **`0.481560`** |
| **union**, `q <= 18` | 32074 | `2.391e-9` | **`0.483661`** |

against `h_min = 0.481212` and the optimiser's `E_64 <= 0.544161`.  **`H_flat, H_ent > 64`
at `(3+sqrt5)/2`.**  The two pools fail in exactly complementary ways -- every periodic
orbit has entropy 0, so orbit weight is entropy dead weight and the Bernoulli mass a hull
of depth `rho` can absorb is at most `rho/(rho + |Phi(Bern)|_2)`; the M7 members all carry
within 0.15 of `log 2` but their hull is thin.  The union repairs both at once, and it is
NOT reachable by R2a's Farkas loop: the loop's step is a Gibbs measure at `a* - tu`, and no
tilt of a window potential is a periodic orbit.

### Two findings that were not asked for

**The certificate is not monotone in the pool; the hull is.**  At `(3+sqrt13)/2, H = 32`,
`delta` peaks at `q <= 12` (`1.4716e-2`) and FALLS at `q = 14` and `q = 16`
(`1.3875e-2`, `1.2793e-2`), while `rho` rises throughout.  Same cause as R2a's "the loop
runs backwards": `R <= 1/sum_j g_j`, and 6262 new columns raise the denominator faster than
the new vertices push the boundary out.  Reporting `delta` alone reads this as a thinning
hull; it is a thickening hull and a loosening certificate.  This is why `depth_upper`
(R2a's) has to be run alongside.

**The binding constraint on `H_ent` is that no Gibbs pool above `H = 64` exists.**
`H_flat` rides on the orbit hull alone and reaches **256 at `1+sqrt2`** (`q <= 16`; the
`q <= 14` hull already gives 128), **128 at `(3+sqrt5)/2`** (`q <= 16`; `H = 256` fails even
at `q <= 18`) and **512 at `(3+sqrt13)/2`** (`q <= 18`), against R1b's 64, 32, 64.  `H_ent` needs a
positive-entropy generator with an enclosed `Phi`, and the folder has exactly one supply --
the memory-12 chains of `r1b_pool*.json`, whose rows stop at `H = 64`.  That is a run of
`m7_ladder.py`, not a new idea.

### Machinery

`r2d_hull.py` (17 self-checks) + `r2d_checknote.py` (88 claims read back out of the note)
-- `lyndon` (Duval), `orbit_rows`, `bern_rows` (Bernoulli(p)
through R1a's own `phi_fl`, so the radius is R1a's), `m7_rows`, `rmax_sub` (the `m`-free
maximin LP), `ent_lp_w` (R1b's `entropy_lp` with Theorem 1's row-norm floor), `cache_of`,
`flat` (ladder A/B), `entrow` (ladder C), `extra`, `table`.  Modes: `--checks`, `--extra`,
`--table`, `--one NAME H q`.  Recorded `r2d_hull.json`, `r2d_hull.log`.

**No new Lean.**  R2d adds no numerical data type the folder does not already have;
`BB61/CycleMean.lean` (R2b) is still the entropy-free Lean target and the cycles-to-measures
bridge is still the open one.

**Gotcha carried forward.**  `MG.margin` multiplies its `eps` argument by `sqrt(H)`, so it
wants a PER-COEFFICIENT radius; `Z.orbit_phi_radius` already returns a 2-norm bound with
the `sqrt(H)` in it.  R2b passed the latter straight in, which is sound but conservative by
`sqrt(H)`; R2d divides it out.  The difference is invisible (`delta` is `1e-2`, `e2` is
`1e-12`) and self-check 10a prices it: `1.893318e-02` either way.

## M3 Corollary 13 in Lean: the floor is Route A in entropy units (EntropyBudget.lean, 2026-08-27)

`note-1061-M3.html` Corollary 13 is the sharp statement of what the M3/M4 pressure lane may
**not** hope for.  Until this file it lived in the folder only as a 200-digit numerical check
over the 42 candidates (M3 Lemma 2), and -- more to the point -- the two constants it is about
had **never appeared in the same Lean statement**:

* `QuadSetup.routeAExponent` = `log 2 / log alpha + log 2 / log (1/rho)`, `Criterion.lean`,
  the sum of the two box dimensions of M1 Corollary 5;
* `LY.hMin` = `(1 / log alpha + 1 / log (1/rho))^-1`, `CITED/LedrappierYoung.lean`, the floor
  of M3 Theorem 11.

`grep` across the repository returned nothing joining them.  They are the same number twice.

### The identity

`routeAExponent_eq_log_two_mul` writes `A(alpha) = log 2 * ((log alpha)^-1 + (log 1/rho)^-1)`
and `hMin_eq_inv_add_inv` writes `h_min(alpha)` as the inverse of that same sum -- the only
gap between the two files is that one spells `1/x` and the other `x^-1`.  Hence

**`routeAExponent_mul_hMin`**: `A(alpha) * h_min(alpha) = log 2`,

at every `QuadSetup` with `beta != 0`, and with it

**`routeAExponent_lt_one_iff_log_two_lt_hMin`** -- Corollary 13 -- `A(alpha) < 1` **iff**
`log 2 < h_min(alpha)`: Route A fires exactly when the entropy floor of a hypothetical
counterexample would exceed the entropy `log 2` available on the full 2-shift.  The budget
phrasing is `zero_lt_entropyBudget_iff`: `0 < log 2 - h_min(alpha)` iff `1 < A(alpha)`.

What this says about the lane: the floor is not an independent obstruction.  Every alpha it
decides *by itself* is one Route A already decides, and the M3/M4 machinery earns its keep
only by spending a potential against the budget -- which is exactly what
`PressureCriterion.lean`'s `P(psi) < h_min` does, and why M4's three fixes (bounded-Borel
potentials, word-wise enclosure, balanced windows) were needed to reach anything new.

### The unit threshold, read on both lanes

At a quadratic unit `rho = 1/alpha`, so `h_min = (1/2) log alpha` (`LY.hMin_eq_of_unit`) and
the threshold `log 2 < h_min` is `alpha > 4`.  Both directions are recorded:

* `log_two_lt_hMin_iff_four_lt_of_unit` transports M2 Proposition 1's
  `routeAExponent_lt_one_iff_four_lt` onto the floor;
* `routeAExponent_lt_one_iff_four_lt_of_floor` runs it backwards, giving a **third** proof of
  the unit threshold -- through `h_min = (1/2) log alpha` and `log 4 = 2 log 2` rather than
  through the `logb` normal form of `RouteANormalForm.lean` or the ceiling of
  `RouteACeiling.lean`.

### Axioms

Only the **definition** `LY.hMin` is used, never the cited axiom `LY.entropyRate_floor`.  All
eleven declarations report the standard three, and `AxCheck.lean` lists them *above* the cited
block for that reason.  The root's non-std3 count is unchanged at four.

### Numerics

`m3_cor13_lean.py`, 6/6 at `mp.dps = 60`, recomputing `alpha` and `rho` from the polynomial
roots rather than trusting the sweep's float64 columns:

| check | result |
| --- | --- |
| C1 | both constants over all 42 candidates; agreement with the stored columns `4.4e-16` |
| C2 | `A * h_min = log 2`, worst deviation `7.8e-62` |
| C3 | Corollary 13, **0 exceptions**: Route A fires at 6 of the 42, the floor clears `log 2` at exactly those 6 |
| C4 | the budget is positive exactly where Route A fails; `0.2525` at `1+sqrt2`, `0.0347` at `2+sqrt3`, `0.2119` at `(3+sqrt5)/2` |
| C5 | `h_min = (1/2) log alpha` on the 9 quadratic units to `7.8e-62`; threshold `alpha > 4`, 0 exceptions; smallest unit above 4 is `2+sqrt5` |
| C6 | on the unit locus both criteria cross at the *same* point: `A(4) = 1` and `h_min(4) = log 2`, both to `0.0e+00` |

C3's "6 of the 42" is the census the M4 section quotes from the other side (`Route A decides
6`), recomputed here from the entropy inequality instead.

## R2c: the deep-window enclosure at `1+sqrt2` (`r2c_deep.py`, 2026-08-27)

Write-up: **`note-1061-R2c.html`** (verified back out of itself by `r2c_checknote.py`,
43 claims).  Machinery `r2c_deep.py` (18 self-checks), on `m8_w4.py` and `m4_fourier.py`
unchanged.  Recorded `r2c_deep.json`, `r2c_deep.log`, `r2c_repro.json`, `r2c_repro.log`.

W4 certified the two *middle* quadratic units.  It had never been pointed at the named case.
The folder's only certified upper bound for `E_H(1+sqrt2)` was M4's `24/16` row, `0.689990`
— log 2 minus 0.0032, at `H = 16`, on a multiplier of norm `sum_h h|a_h| = 0.73` that the
search then never moved again through `H = 64`.

**Gate met.  `E_H(1+sqrt2) <= 0.681768`** at `H = 512`, `L = 26` — `log2 - 1.138e-2`, i.e.
**3.60x** M4's total gain — and the `H = 16` stall turns out to be a property of the search
surrogate rather than of `alpha`.

### Theorem 1 (the enclosure law), and why it matters

With `psi_u = g(F~_u)` on the `2^(L+1)` window words, `phi_u = eps|g'(F~_u)| + eps^2 M2/2`
the M4 Prop. 3 enclosure, and `mu_psi` the equilibrium measure of the de Bruijn operator:

    Lambda(psi) + eps <|g'|>_mu + eps^2 M2/2
      <= Lambda(psi + phi)
      <= Lambda(psi) + eps sup|g'| + eps^2 M2/2
      <= Lambda(psi) + 2 pi (sum_h h|a_h|) eps + eps^2 M2/2

Proof: the finite-state variational principle makes `Lambda` a maximum of affine functionals
of the potential; evaluate that maximum at `nu = mu_psi` for the left inequality, bound
`<phi,nu>` by `max phi` uniformly in `nu` for the middle, and `|g'| <= 2 pi sum h|a_h|`
pointwise for the right.

Three readings.  **M3's `delta_bound` is the right-hand end of a chain of three**, and M4
Prop. 3 buys two *different* steps: `2 pi sum h|a_h| -> sup|g'|` is about the multiplier,
`sup|g'| -> <|g'|>_mu` is about where the Gibbs measure sits, and the second is the larger.
**The left end is a floor**, hence a no-go: Corollary 1 says a certificate fires only if
`Lambda(psi_a) < h_min` *before* the window is chosen, so **window depth can never substitute
for degree**.  And **the left end is numerically an equality** — 4e-5 to 2.4e-3 relative on
all 31 certificates — so it is a predictive formula, i.e. the surrogate the search should have
been minimising.

### The measured over-charge, and the stall

`kappa_ww := (Lambda_enc - P_deep) / (2 pi (sum_h h|a_h|) eps)`, read straight off W4's twenty
stored certificates with nothing re-run:

| alpha | range of `kappa_ww` |
| --- | --- |
| `(3+sqrt5)/2`, L=22,24, H=64..512 | 0.0947 .. 0.2082 |
| `(3+sqrt13)/2`, L=22,24, H=64..2048 | 0.0442 .. 0.1060 |
| **all twenty** | **[0.0442, 0.2082]**, median 0.0981 |

So `m4_fourier.search` is charged **4.8x to 22.6x** what the certificate pays.  At the two
middle units the pressure falls fast enough to buy past that; at `1+sqrt2`, thirteen times
slower (R2a), it does not, and the ladder freezes at the first rung where the penalty overtakes
the gain.  Normalise by `err`, not by `W.eps`: `enclose`/`certify` evaluate from `W.F` by the
trigonometric loop and never touch the WP3 grid, so the `1/(2G)` term that `delta_bound` rightly
charges is not part of what `Lambda_enc` pays (a 0.3 % correction here, and getting it the other
way round would bias the constant).

**The saturation degree is a function of the penalty rate.**  Ladders were run at
`eps_target = kappa * eps(L=24)` for `kappa in {1, 1/4, 1/16, 0}`; `kappa = 1` is W4's own
protocol and `kappa = 0` the unpenalised control:

| penalty rate | saturates at | largest mode used | `sum_h h|a_h|` |
| --- | --- | --- | --- |
| M4, `eps_20 = 2.974e-4` | `H = 16` | 16 | 0.73 |
| `kappa = 1`, `eps_24 = 5.102e-5` | `H = 64` | 50 | 6.31 |
| `kappa = 1/4` | not by `H = 512` | 289 | 34.36 |
| `kappa = 1/16` | not by `H = 512` | 309 | 119.24 |
| `kappa = 0` | never | 512 | 299.04 |

That is **gate G-A1 of `plan-BB61-1+sqrt2.html` §3 answered YES** — the outcome that plan
called unexpected — and answered without the `L = 28, 30` runs it asked for.  It was never the
window; it was the exchange rate.

**But the penalty must not be switched off.**  `kappa = 0` at `H = 512` certifies `0.718830`,
*above* log 2 and so worse than trivial, while carrying the run's lowest pressure `0.678079`.
The optimum in `kappa` is interior, and it moves with the window: `1/4` wins at `L = 22`,
`1/16` at `L = 24` and `L = 26`.

### The certificates

Best `Lambda_enc` per degree, over the whole `kappa` grid (`h_min = 0.440687`, log 2 =
0.693147; nothing fires, closest approach 0.2424):

| H | L=22 | L=24 | L=26 |
| --- | --- | --- | --- |
| 16 | 0.689454 | 0.689241 | |
| 32 | 0.688131 | 0.687695 | |
| 64 | 0.686790 | 0.685479 | |
| 128 | 0.686703 | 0.684372 | 0.683077 |
| 256 | 0.686739 | 0.684408 | |
| 512 | 0.687384 | 0.684382 | **0.681768** |

**The word-wise enclosure is not a refinement here, it is the entire certificate.**  At every
winning rung `Lambda_cw = pressure_ub + delta_bound` is 0.698, 0.704, 0.724, 0.775 — all
*above* log 2, reporting nothing — while `Lambda_enc` is below it at each.  R2a's "the crude
bound never beats log 2 at `1+sqrt2`" holds exactly where it matters; at the *stalled*
multiplier it does dip under, by 2.8e-3, because there is almost nothing to charge for.

### `E_H(1+sqrt2)` bracketed on both sides, for the first time

| H | certified `E_H >=` | source | certified `E_H <=` | width |
| --- | --- | --- | --- | --- |
| 4 | 0.691073498 | R1b | 0.691200 | 1.26e-4 |
| 8 | 0.690101873 | R1b | 0.690351 | 2.49e-4 |
| 16 | 0.689054039 | R1b | 0.689241 | 1.87e-4 |
| 32 | 0.687024430 | R1b | 0.687695 | 6.70e-4 |
| 64 | 0.677794296 | R2d union | 0.685479 | 7.69e-3 |
| 128 | **0.605736201** | **R2e union** | 0.683077 | 7.73e-2 |
| 256 | — | | 0.683077 | — |
| 512 | — | | **0.681768** | — |

*(the `H = 128` lower side and the `H = 256` upper side are R2e, below; the raw `U(256)` was
0.684408 and monotone tightening replaces it)*

Two machines that share no code — a `2^25`-state windowed transfer operator with a
Collatz-Wielandt bound over the word-wise enclosure, against a convex-hull certificate over
exact rational circulations with an interval Gram matrix — pin `E_H` to four decimals at
`H <= 32`.  This meets the `1e-4` target of A2 in `plan-BB61-1+sqrt2.html` at the low rungs.
It also settles R1b's QA item from the other side: M7 §4's LP *upper* column reads 0.691068,
0.690096, 0.689063, 0.687346, 0.683271 — the last three sit inside these brackets and the
first two sit 5.7e-6 *below* the certified lower bound, which is impossible for an upper bound
on `E_H` and is exactly the window truncation R1b diagnosed.  Above `H = 64` there is no lower
bound because `r1b_pool*.json` stops there — the blocker R2d already named.  **R2e (below)
removes it at `H = 128` and shows that the "one run of `m7_ladder.py`" it was supposed to take
returns an empty pool.**

### What a window level buys, and the price on two axes

M4 §8 measured the window's worth here as `3e-4` for `eps_20 -> eps_24` and concluded "the
window is irrelevant to their shortfall".  That was measured at `sum_h h|a_h| = 0.73`, where by
Theorem 1 there is nothing for it to be worth.  On a multiplier the corrected surrogate
produces (`kappa = 1/16`, `H = 128`, `S1 = 48.3`):

| L | eps | `Lambda_enc` | `Lambda_enc - P_deep` | `kappa_ww` |
| --- | --- | --- | --- | --- |
| 22 | 1.2317e-4 | 0.688072 | 5.841e-3 | 0.1563 |
| 24 | 5.1018e-5 | 0.684372 | 2.119e-3 | 0.1369 |
| 26 | 2.1132e-5 | **0.683077** | 8.264e-4 | 0.1289 |

and the same `L = 26` window at `H = 512`, where `sum_h h|a_h| = 119.2`, gives the run's best
certificate `0.681768` (gap 2.233e-3, `kappa_ww = 0.1411`) — a rung that certified `0.685648`
at `L = 24` and `0.698331`, *above* log 2, at `L = 22`.  The turning point in `H` moves right
as the window deepens.

Two levels are worth 3.70e-3 and the next two 1.30e-3 — an order of magnitude over M4's
measurement, falling like `eps` itself, which is Theorem 1's prediction and not a fit.

The window price is `2^L ~ eps^(-2 log2 / log alpha)`, exponent **1.5729** at `1+sqrt2` — which
is `m4_frontier.json`'s own `routeA` field and **R2b's exponent for the dual route**: both are
paying for `||F - F~_L||_inf`.  (1.4404 and 1.1603 at the middle units; measured per-level
factor 0.6464 against `alpha^{-1/2} = 0.6436`.)  In absolute terms, matching the enclosure W4
bought at `(3+sqrt5)/2, L=24` needs `L = 28` here, 16x the states; matching `(3+sqrt13)/2,
L=24` needs `L = 34`, 1024x.  **`1+sqrt2` is the outlier on both axes**, where M4 named it the
outlier on the degree axis alone.

On the degree axis, min `P_deep` per `H` (16..512) is 0.68909, 0.687385, 0.684492, 0.682136,
0.681705, 0.679221: 1.97e-3 per doubling on average and 2.89e-3 at best, against a shortfall of
0.2374 to `h_min` — 120 and 82 doublings.  That confirms M3 §9.2's order of magnitude at this
`alpha` but not its constant, which is a second-order expansion around `a = 0` and a different
object.

### The baseline, re-run first

M4's published rows are reproduced through W4's own `reproduce` (the pre-WP2/WP3 switches put
back, the combination `m8_gates` G-1 proved bitwise identical to the pre-rewrite code) before
any new number is offered: seven ladder rungs and three certificates agree to `5.0e-7`, every
certificate moving *down* (a better multiplier on a flat minimum, not a different bound),
`enclose_blk == m4_fourier.enclose` and `cw_ub == m4_fourier.spec_ub` bitwise, and the
saturation reproduces at `sum_h h|a_h| = 0.7299` at `H = 16, 24, 32, 48, 64` alike.

### Cost

`L = 26` is `2^27` words: 1.07 GB for `F~` alone, ~8.8 GB peak, 814 s for one `H = 128`
certificate (1921 s at `H = 512`).  It is the deepest window run anywhere in this folder, and at `1+sqrt2` it still
only matches the enclosure W4 bought at `(3+sqrt5)/2` with `L = 22`.


## R2e: the Gibbs pool above H=64 (`r2e_pool256.py`, 2026-08-28)

Work package R2e: the step that both `note-1061-R2c.html` §10 (*"a Gibbs pool above H=64
closes the bracket at 128 and 256"*) and `note-1061-R2d.html` §7 (*"that is a run of
`m7_ladder.py`, not a new idea"*) named as next.  Full account in `note-1061-R2e.html`.

**The named run does not work, and that is the first result.**  `r1a_pool.py` at `H = 128` on
the `L = 12` window returns an **empty** pool — 0 of 2049 members representable — and dies in
`hull_distance` on a 0-row array.  `r2e_pool256.py diag` measures the state it is in:

| H | centre | P | max abs x | sum h abs a | chains | representable |
| --- | --- | --- | --- | --- | --- | --- |
| 128 | optimised | -17.195496 | 59.7924 | 58647.72 | 2049 | **0** |
| 128 | frozen at H0=64 | +0.683271 | 0.0928 | 24.97 | 2049 | **2049** |
| 256 | optimised | -10.902530 | 21.4135 | 15477.40 | 4097 | 4097 |
| 256 | frozen at H0=64 | +0.683271 | 0.0928 | 24.97 | 4097 | 4097 |

`minimize_pressure` carries no penalty (M4's `search` does, the pool builder does not), and
past `H ~ 120` at `L = 12` the constrained pressure is unbounded below — R2a's row-1 table,
`P = -23.23` with `x` at the cap.  L-BFGS runs to 59.79 against a box cap of 60, `exp` of the
weights overflows, `from_window` evaluates 0/0 and the finiteness guard discards everything.
**It is not a wall in `H`:** at `H = 256` the same code stops at 21.41 and every chain
survives.  Where a descent leaves an unbounded ray is arbitrary, so "the pool exists at `H`"
is not a property of `H`.

*Theorem 2 (soundness is independent of the centre).*  For any `a*` whatever, each pool member
is a memory-`L` Markov measure; `Phi_h` comes from `phi_fl` at `J = M = 60` with an a-priori
enclosure that knows neither `H` nor `L`, and the entropy from `circulant.entropy()` on the
same exact rational weights.  The window enters only the *choice* of members.  So the trust
rule `2 pi H eps_L < 1` governs pool **quality**, never validity — and freezing `a*` at
`H0 = 64`, zero-padding, and letting the `16H+1` one-mode tilts carry the higher modes is
sound at every `H`.  The padded centre's windowed pressure is 0.6832708852034778 at `H = 128`
and 0.6832708852034775 at `H = 256` against the stored `H = 64` value 0.6832708852034777 —
agreement to the last digit, which is the check that `pad` and `set_modes` compose.

The frozen pool at `H = 128`: 2049 members, 0 skipped, entropies in [0.552506, 0.684441] (mean
0.666529, median 0.681813, **all** above `h_min = 0.440687`, 99.0 % above 0.60), radius
1.4810e-13, repair 8.808e-7, hull distance **1.0455e-2**, 47402 s.  That last number is the
trust wall arriving: at every rung up to 64 the M7 pool contains `0` in its own hull, and at
128 it does not.  The sharpened rule puts the wall at `H < 15.8` for `L = 12`; the pool in fact
survives to 4.1x it and fails at 8.1x — the first measurement of where the slack runs out.

### The certificate at H = 128

| pool | m | sigma_min | R_max | delta | drift | `E_128 >=` | margin over h_min |
| --- | --- | --- | --- | --- | --- | --- | --- |
| M7 | 2049 | — | — | 0 not in conv, gap 1.0455e-2 | | — | — |
| orb+B | 8807 | 9.355247 | 6.976999e-3 | 6.8435e-9 | 3.22e-11 | 0.448496 | +7.8093e-3 |
| **union** | 10856 | 9.357972 | 6.931743e-3 | 6.8975e-9 | 3.60e-11 | **0.605736** | **+0.165049** |

Theorem 1' gives `R <= 1/sum_j g_j`, so every column loads the ceiling.  The 2049 Gibbs
columns cost **0.649 %** of `R_max` and buy **+0.157240** of certified entropy.  This is R2d
Theorem 3 (the two pools fail complementarily) at a degree R2d could not test, and the effect
is an order of magnitude larger than the `+2.97e-4` R2d measured at `H = 64` — because at 64
the M7 pool enclosed `0` by itself and had nothing to gain from the orbits, and at 128 the two
halves are doing genuinely different jobs: orbits supply the enclosure, Gibbs rows the entropy.

### Why `H = 256` needs the pool

| H | pool | delta | `E_H >=` | margin over h_min | verdict |
| --- | --- | --- | --- | --- | --- |
| 64 | orb+B | 1.180e-8 | 0.499723 | +5.9036e-2 | H_flat, H_ent > 64 |
| 128 | orb+B | 6.8435e-9 | 0.448496 | +7.8093e-3 | H_flat, H_ent > 128 |
| 256 | orb+B | 3.2245e-9 | 0.398581 | **-4.2106e-2** | **H_flat > 256 only** |

The margin falls 7.56x per doubling and changes sign.  Every periodic orbit has entropy exactly
0, so all the certified entropy comes from the Bernoulli directions, and the mass a hull of
depth `rho` can put on them is at most `rho/(rho + |Phi(Bern)|_2)`.  **Above `H = 128` there is
no orbit-only certificate for `H_ent` at `1+sqrt2`, and there cannot be one at any `q`:**
raising `q` deepens the hull but adds only zero-entropy columns, each loading `sum_j g_j`.

The `H_flat` side reproduces R2d exactly — `q <= 14` infeasible at `H = 256` (`rho_hat =
-1.6042e-3`, m = 2538), `q <= 16` feasible with `delta = 3.353588436042504e-03`, m = 8800, R2d's
stored value to all 16 digits through a different driver.

### Theorem 1: monotone tightening

`K_{H+1} <= K_H`, so `E_H` is non-increasing, so `U*(H) = min_{H'<=H} U(H')` and
`L*(H) = max_{H'>=H} L(H')` are certified, and `L* <= U*` is a real cross-engine test (the
lower side is an LP over pools with a Brouwer repair, the upper a penalised pressure
maximisation over a deep window; no shared code).  The raw uppers are **not** monotone —

    raw U(H):  4:0.691200  8:0.690351  16:0.689241  32:0.687695  64:0.685479
               128:0.683077  256:0.684408  512:0.681768

— so the tightening fires once, at `H = 256`.  Passed at all eight rungs, tightest instance
`0.691073 <= 0.691200` at `H = 4` (0.018 %).

### The price, re-read

Decrements of `U*` per doubling: 8.49e-4, 1.11e-3, 1.55e-3, 2.22e-3, 2.40e-3, 0, 1.31e-3.  They
grow to `H = 128` and then stop, and the zero is Theorem 1 replacing a non-monotone raw value —
the upper-bound engine has hit its own resolution limit at `L = 26`.  Against a gap
`U*(512) - h_min = 0.241082`:

| rate | value | doublings | H | L from `2 pi H eps_L < 1` | states `2^L` |
| --- | --- | --- | --- | --- | --- |
| best single decrement (64->128) | 2.4023e-3 | 100 | 1e30.2 | >~160 | 1e48 |
| mean over 4..512 | 1.3473e-3 | 179 | 1e53.9 | >~284 | 1e86 |
| mean over 64..512 | 1.2370e-3 | 195 | 1e58.7 | >~309 | 1e93 |

These extrapolate seven terms over fifty orders of magnitude and are not predictions.  What the
table is good for is a lower bound on ambition: any claim that the certificate lane reaches
`h_min` at `1+sqrt2` has to say where a decrement two orders of magnitude larger comes from.
**R2e makes this worse, not better** — tightening lowered `U*(256)`, flattening the tail and
raising R2c's estimate from `H ~ 1e25` to `1e30..1e54`.

### Machinery

`r2e_pool256.py` (16 self-checks) + `r2e_checknote.py` (88 claims read back out of the note),
on `r1a_pool.py`, `r1a_enclose.py`, `m7_price.py`, `m3_entropy.py`, `m4_fourier.py`,
`r2a_margin.py`, `r2d_hull.py`.  Subcommands `checks build diag orb flat bracket ent table`;
the pool is `build --hs H --h0 64`, the certificate `ent --hs H --q 16 --pool
r2e_pool_frozen.json`.  Recorded `r2e_pool256.json`, `r2e_pool_frozen.json`,
`r2e_frozen128.log`, `r2e_diag.log`, `r2e_orb.log`.  R1b's own `r1b_pool64.json` is never
written to; the extension lives in `r1b_pool256.json` and the frozen rows in their own file.

**Open.** The `H = 256` frozen build (`build --hs 256 --h0 64`, ~52 h for 4097 members) is the
only route to `H_ent > 256`.  Then R2f: a *penalised* `minimize_pressure` at `L = 16` or 18,
where the trust wall sits at `H = 91` and 221, which is the only way to a Gibbs pool that
encloses `0` at `H >= 128` on its own.  Small: `r1a_pool.py` should report "0 members survived"
rather than raise an `IndexError` twenty lines later.

**No new Lean.**  R2e adds no numerical object the folder does not have; `BB61/CycleMean.lean`
remains the entropy-free Lean target.

### The H = 256 rung (landed 2026-08-28, 3.1 h)

The frozen-centre build at `H = 256` finished in **11058 s** — not the 52 h estimated from
the `H = 128` run — with **4097 of 4097** members, 0 skipped, entropies in
[0.526185, 0.684441], radius 1.4810e-13, repair 8.916e-7, hull distance **1.2044e-2**
(against 1.0455e-2 at `H = 128`: the M7 half still does not enclose 0 alone, and the gap
widens slowly).  On the union pool:

| H | pool | m | q | delta | E_H >= | margin over h_min | verdict |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 256 | orb+B | 8807 | 16 | 3.2245e-9 | 0.398581 | -4.2106e-2 | `H_flat > 256` only |
| 256 | **union** | 12904 | 16 | 3.1454e-9 | **0.582936** | **+0.142249** | **`H_flat, H_ent > 256`** |

So **`H_ent(1+sqrt2) > 256`** and `E_256 in [0.582936, 0.683077]`.  The 4097 Gibbs columns
buy **+0.184355** of entropy — more than the +0.157240 they bought at 128 — for 2.45 % of
the certified depth.  A Gibbs pool above `H = 64` was the only way to move this column, and
it moved it twice.

## R3a: the enclosure and plateau accounting at degree 3 and 4 (`r3a_degree.py`, 2026-08-28)

Work package R3a of `plan-BB61-counterexample.html`: *"re-derive the enclosure and plateau
accounting at degree d = 3, 4"*, so that *"§7.2's numbers become usable rather than
indicative"*.  The caveat being discharged is §7.3 (ii): *"M7 Thm 9's plateau analysis and
M4's balanced-window results are stated for quadratic units; the enclosure accounting has to
be redone at higher degree before any number from §7.2 is used as more than a signpost."*
Full account in `note-1061-R3a.html`; 28 self-checks in `r3a_degree.py`, 133 claims read back
out of the note by `r3a_checknote.py`.

**The column survives as a number and dies as a reading.**  Every entry of M7 §8's
degeneration table is now certified — relative width below 1e-80, agreeing with the float that
produced it to eleven digits — and it is not what §7.2 calls it.

### Certified conjugates at any degree (Smith discs)

`r1a_enclose` is quadratic by construction (`ABAR = 1 - sqrt2`, `set_alpha(A, B)`), because at
`1+sqrt2` every constant is a rational combination of `sqrt2` and `mpmath.iv` encloses that.
At degree `d` there is no such form.  Smith's theorem: with `zhat_i` the approximate roots of
the monic integer `p`, every root lies in some `D(zhat_i, r_i)`,
`r_i = d |p(zhat_i)| / prod_{j != i} |zhat_i - zhat_j|`, and a disc disjoint from the others
holds exactly one.  At 200 digits the radii are 6.6e-302 .. 1.5e-300 and the discs are
pairwise disjoint at `d = 2..11` (minimum separation 0.54 at `d = 11`), so the conjugates are
interval constants and `c_m`, `eps(J,M)`, the Erdos products and the ladder data are all
enclosures.  Two ties to the old engine: at `d = 2` the certified conjugate is `1 - sqrt2` to
1e-190, and at `d = 3` the family's cubic is a unit with one complex pair so `rho` must equal
`alpha^{-1/2}` exactly — it does, to 1e-30.

The column that decides everything is `rho*alpha`: 1.00000 (d=2), 1.48512, 1.71460, 1.82690,
1.88773, 1.92364, 1.94626 (d=8).  It is 1 at `d = 2` not approximately but to 1e-190, since
`alpha |beta| = |N(alpha)| = 1`.  That is M7 Thm 10.

### Theorem A: the window law at any degree

    ||F - F~_{J,M}||_inf  <=  eps(J,M) := alpha^-J + sum_{j>=2} |alpha_j - 1| |alpha_j|^{M+1} / (1 - |alpha_j|)

with the past tail taken **one conjugate at a time**, and hence
`|Phi_h - Phi~_h| <= 2 pi |h| eps(J,M)` for every invariant `mu` at once.  At `d = 2` this is
exactly `r1a_enclose.eps_trunc` (agrees to 25 digits at (10,10), (40,40), (60,60)).  M4's
`best_window` uses `C_alpha rho^{M+1}/(1-rho)` with the single largest modulus; the per-
conjugate form is 1.00, 1.00, **1.44**, 2.30, 3.25, 4.25, 5.31 times tighter at `d = 2..8`
(worth 3 units of `M` at `d = 4`, 71 at `d = 8`).

| d | rho | eps(60,60) | 2 pi H eps, H=4096 | verdict | need J | need M | K | eps at L=12 | % of range F |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 2 | 0.414214 | 2.160e-23 | 5.559e-19 | OK | 47 | 47 | 95 | 1.010e-2 | 0.3 |
| 3 | 0.673348 | 2.627e-10 | 6.761e-06 | weak | 52 | 108 | 161 | 2.443e-1 | 3.9 |
| 4 | 0.813796 | 3.834e-05 | **9.868e-01** | **noise** | 55 | 209 | 265 | 1.516 | 16.0 |
| 5 | 0.888584 | 1.100e-02 | 2.832e+02 | noise | 57 | 368 | 426 | 4.923 | 36.7 |
| 6 | 0.930339 | 2.389e-01 | 6.149e+03 | noise | 58 | 605 | 664 | 1.171e+1 | 64.5 |
| 7 | 0.954690 | 1.501 | 3.862e+04 | noise | 59 | 949 | 1009 | 2.234e+1 | 93.9 |
| 8 | 0.969441 | 4.902 | 1.262e+05 | noise | 59 | 1425 | 1485 | 3.712e+1 | 122.4 |

**For the enclosure the news is good.**  `J` barely moves (`alpha -> 2` slowly); the past
depth is the whole cost, and it is linear in the work — `K` triples between `d = 2` and
`d = 4`, so a certified `Phi` at `d = 4, H = 4096, tau = 1e-13` costs **2.8x** the quadratic
case.  That is the price of caveat (ii), and it is small.  **Warning**: the folder's default
`(60,60)` gives an enclosure radius of 0.99 at `d = 4, H = 4096`.  Anything run at `d >= 4`
with the default reports nothing.

**For the pool the news is fatal.**  The last two columns are a different object: the memory-L
window that *defines* a Gibbs member, not the depth at which `Phi` is evaluated.  R2a §8.1's
trust rule (`H eps_L <~ 0.9`, `eps_L ~ rho^{L/2}`) at `H = 64` licenses

| d | 2 | 3 | 4 | 5 | 6 | 7 |
| --- | --- | --- | --- | --- | --- | --- |
| L licensed at H=64 | **12** | 23 | 41 | 68 | 111 | 173 |
| 2^L states per member | 4096 | 8.4e6 | 2.2e12 | 3.0e20 | 2.6e33 | 1.2e52 |
| L licensed at H=4096 | 21 | 39 | 67 | 109 | 174 | 268 |

The `d = 2` entry is the check that the rule is read correctly: `L = 12` at `H = 64` is
exactly what R1a, R1b, R2d and R2e run, and it was not chosen to match.  R2a's own cost
formula `121 * H * 2^L` prices one `d = 4` member at `H = 64` at 1.7e16 operations, and R2e's
pool has `16H+1 = 1025` of them.  Equivalently: at `d = 4` the `L = 12` window is uncertain by
**16 % of the entire range of F**, and by `d = 7` by more than all of it.

### Theorem B: the dead zone at any degree, and the absent plateau

M7 Thm 8 is stated *"degree two, for readability"* and has two halves.  The **future** half
survives verbatim: with `e_k = h_{k+1} - alpha h_k = sum_{i>=1} lambda^(i) (alpha_i - alpha) alpha_i^k`
and `E = sum_{i>=1} |lambda^(i)| |alpha_i - alpha|`, so `|e_k| <= E rho^k`,

    | h_{i+j} (alpha-1) alpha^-i - (h_{j+1} - h_j) |  <=  E rho^j (1 + (alpha-1)/(alpha-rho)).

Proof is one unrolling: `h_{i+j} = alpha^i h_j + sum_{t=j}^{i+j-1} alpha^{i+j-1-t} e_t`, and the
left side is `|-e_j + (alpha-1) sum_{t>=j} alpha^{j-1-t} e_t|`.  At degree two `E = |e_0|` and
`rho = |beta|`.  Verified at `d = 2..5` over three ladders each and all `i+j <= 40`: worst
ratio to the bound 0.586, 0.560, 0.515, 0.500 — true and tight to a factor two.

The **past** half used `alpha |beta| = 1`, which by M7 Thm 10 holds exactly at quadratic units.
The invariant is the past band's amplitude `sum_{j>=1} lambda^(j) (alpha_j alpha)^k`, and on
the trace ladder `h_k = Tr(alpha^k)`:

| d | h_k, k=0..9 | past-band amplitude |
| --- | --- | --- |
| 2 | 2, 2, 6, 14, 34, 82, 198, 478, 1154, 2786 | 1, 1, 1, 1, 1, 1, 1, 1, 1, 1 |
| 3 | 3, 2, 4, 11, 24, 52, 115, 254, 560, 1235 | 2, 0.45, 4.2, 2.9, 8.0, 10, 13, 28, 16, 69 |
| 4 | 4, 2, 4, 8, 20, 42, 88, 184, 388, 818 | 3, 0.23, 2.0, 12.7, 5.8, 20, 46, 56, 122, 120 |

so from `d = 3` the band never stabilises, and the certified `|Phi_{h_k}(Bern)|` falls through
twelve orders with no limit but zero, against `d = 2`'s convergence to 7.637e-5 by the sixth
rung.  **The plateau is not degraded above degree two; it is absent.**

*A quadratic-unit remark, exact.*  The plateau being present is not the same as its being
non-zero.  At `1+sqrt2` the Pell ladder `h_k = 1, 2, 5, 12, 29, 70, 169, 408, ...` has
`lambda = 1/(2 sqrt2)`, so `lambda (alpha-1) = 1/2` **exactly**, the `i = 0` factor of the
Erdos product `P(lambda)` is `cos(pi/2) = 0`, and the limit is 0.  Measured: 8.74e-3, 8.10e-4,
2.07e-5, 6.24e-7, ..., 4.05e-16 — a geometric death at a quadratic unit, from a *vanishing*
plateau rather than an absent one.  The two mechanisms are told apart by `rho*alpha`, not by
the decay.

### What §7.2's column actually is

Certified, with its maximiser and a certified upper bound on the rest of the spectrum.  The
device for the last: every factor of the Erdos product has modulus <= 1, so any sub-product is
an upper bound at every `h` at once; grow `K` until the sub-product bound at the runner-up
meets the certified value there.

| d | certified sup, h<=4096 | h* | certified sup over h != h* | at h | K | concentration |
| --- | --- | --- | --- | --- | --- | --- |
| 2 | 4.596235e-02 | **3** | 3.4862e-02 | 17 | 18 | 1.318 |
| 3 | 1.955255e-03 | **1** | 4.8719e-04 | 36 | 40 | 4.013 |
| 4 | 1.609878e-03 | **1** | 5.6228e-06 | 2 | 64 | 286.3 |
| 5 | 3.205489e-05 | **1** | 1.5119e-09 | 11 | 124 | 2.120e+04 |
| 6 | 1.802807e-07 | **1** | 2.6809e-13 | 3 | 184 | 6.725e+05 |
| 7 | 4.738540e-09 | **1** | 9.1843e-18 | 2 | 278 | 5.159e+08 |
| 8 | 4.159791e-13 | **1** | 7.8827e-23 | 2 | 416 | 5.277e+09 |

**Proposition C (measured, certified).**  For `d = 3..8` in the family `X^{n+1} - 2X^n - 1`,
and for every `H` in {4, 16, 64, 256, 1024, 4096, 16384},
`sup_{h<=H} |Phi_h(Bern_{1/2})| = |Phi_1(Bern_{1/2})|`.  At `d = 2` the maximiser is `h = 3`,
a rung of 1, 3, 7, 17, 41, ..., and it is a maximiser for the plateau's reason.

So the `H`-independence at `d >= 3` is not the plateau but its opposite.  Dyadic block maxima
over `[2^k, 2^{k+1})`, `k = 0..11`: at `d = 2`, 8.74e-3, 4.60e-2, 3.24e-2, 2.16e-2, 3.49e-2,
3.45e-2, ..., 3.45e-2 — flat.  At `d = 4`, 1.61e-3, 5.62e-6, 5.60e-8, 1.37e-7, 6.74e-8,
5.57e-10, 4.91e-8, 4.90e-11, ..., 9.32e-12 — nine orders in twelve octaves.

### The reading

(i) **The residual is rank two at `d >= 4`.**  The Newton problem is `2H` real equations; at
`d = 4` Bernoulli satisfies `2H-2` of them to 5.62e-6 or better and misses two by 1.61e-3; at
`d = 8`, 7.88e-23 against 4.16e-13.  The family does not shrink the problem uniformly, it
retires all but two coordinates.

(ii) **`residual / s_{H,L}` is therefore the wrong gate, pessimistically.**  The Newton step is
`v = -DPhi^+ r` and `||v|| <= ||r|| / s_{H,L}` is tight only when `r` lies along the smallest
right-singular direction.  With `r` supported on the two `h = 1` coordinates the bound is loose
by up to the condition number, so G-3 as posed can read *negative* for a lane that works.

(iii) **The structural input §7.3 promises is in the wrong place.**  Prop. 12's `cos(pi/alpha)`
exceeds the measured residual by 5.8, 74.6, 49.5, 1.33e3, 1.25e5, 2.46e6 at `d = 2..7`, so the
collapse is far below the linear rate — but it is a collapse *of the first mode*, and `h = 1`
is the one mode with no ladder structure (Theorem B is vacuous at `k = 0`).  Everything M7
§5–§6 knows about the geometry of `e(hF)` is knowledge about ladder modes, and at `d >= 3` the
ladder modes are exactly the collapsed ones.

**G-3 replaced.**  *G-3a*: is `||DPhi^+ r||` bounded in `H` for the certified residual `r` —
one least-squares solve per `(H, d)`, not a singular-value sweep?  *G-3b*: is there a direction
in the memory-L family moving `Phi_1` at first order while moving `Phi_h, 2 <= h <= H`, by
`o(|Phi_1|)`?  Both are stated at `d = 3, 4` with the enclosure engine above; neither needs a
pool.

### What this does not say

It does not bound `s_{H,L}`; G-3 is untouched as a question and R3b is *unblocked and cheaper*
than §12 priced it.  It does not contradict M7 §8: that table is reproduced to eleven digits
and its no-go — `H_ent(alpha) -> infinity`, no certificate scheme uniform in `alpha` — is about
`S(H)` and the entropy budget, and is untouched.

One flagged defect, no number changes: `m7_alpha2.bern` stops its past product at the first `m`
with `|c_m| H < tol`, but at `d >= 3` the `c_m` oscillate and can vanish accidentally (at
`d = 2` they cannot: `c_m = (beta-1) beta^m`).  The break fires at `m = 114, 219, 360, ..., 3575`
against window depths 118, 227, 397, ..., 4201, and the omitted factors are all within 1e-16 of
1, so nothing published moves.  `r3a_degree.bern_scan` runs to the depth the tail law prescribes.

## R3b: DPhi at Bernoulli, and the gate it settles (`r3b_jacobian.py`, 2026-08-28)

Work package R3b: *"`DPhi` at Bernoulli: sparsity from M7 Thm 8, and `s_{H,L}`"*, gate G-3,
as replaced in `note-1061-R3a.html` §6 by **G-3a** (is `||DPhi^+ r||` bounded in H?) and
**G-3b** (a direction moving `Phi_1` while moving `Phi_h, h>=2` by `o(|Phi_1|)`?).  Full
account in `note-1061-R3b.html`; 13 self-checks, 48 claims read back by `r3b_checknote.py`.

### The derivative, in closed form (Theorem C)

Parametrise by conditionals `q(b) = 1/2 + t u(b)`; Bernoulli is `t = 0`, interior.  Linear
response (`psi_k = 2u(b_k)(2w_k-1)`, `E psi = 0`) plus factorisation gives
`dPhi_h/dt = <g_h, u>_{L^2(pi)}` with

    g_h(b) = sum_k ( e(h gamma_k) - 1 ) P_k e( h sum_{j=1..L} gamma_{k-L+j-1} b_j ),
    P_k    = prod_{p not in [k-L,k]} phi(h gamma_p),   phi(x) = (1+e(x))/2,

`P_k` as prefix*suffix, never a quotient.  Each `k`-term's block dependence is a
Kronecker-rank-one character, so all `2^L` values cost `2^L` by doubling.  Checked four
ways: at `L = 0` it is `d/dp` of the Erdos product (9e-15); constant `u` recovers the same
(1e-15); against central differences on the exact chain, 9.3e-10 / 1.1e-9 / 2.1e-9 at
d = 2/3/4; and the assembled residual reproduces R3a's certified `|Phi_1|`.

**Away from Bernoulli** (§2.1) the same identity gives, by one forward and one backward pass,
`dPhi_h/du(b) = sum_p V_p[b] ( e(h gamma_p) W_{p+1}[t1[b]] - W_{p+1}[t0[b]] )`, `V_{-M} = pi`.
**No `dpi/dq` appears** — linear response already contains the change of the stationary
measure, so R1a's "one expensive step" is not needed for the derivative.  Validated by
`sum_b V_{J+1}[b] = Phi_h` to 7.9e-18, by central differences at a non-Bernoulli point to
2.7e-9, and against Theorem C at Bernoulli to 3.9e-16.

### Sparsity: M7 Thm 8 on the nose

At `1+sqrt2`, `h = 1393`, window (40,40): the reduced weights exceed 1e-3 at **exactly**
`p in [-16,-2] u [2,16]` — M7 §5's quoted support, 30 of 81 positions — and 90 % of the
k-mass of `g_h` sits on **11 of 81**.  Across d = 2,3,4 and h = 1, 2 and three ladder rungs,
90 % of the k-mass is on 1.1 %–12.6 % of the positions.

### G-3a and G-3b: both pass, and §7.3's statistic is off by 1e15

| d | L | quantity | H=4 | H=32 | H=64 | H=256 |
| --- | --- | --- | --- | --- | --- | --- |
| 4 | 16 | `||DPhi^+ r||` | 1.2151e-3 | 1.2165e-3 | 1.2166e-3 | 1.2595e-3 |
| 4 | 16 | `lambda_1` | 1.3249 | 1.3239 | 1.3238 | 1.3232 |
| 4 | 16 | `||r||/s_min` | 1.129e-2 | 2.891e+1 | 2.828e+4 | 3.583e+9 |
| 4 | 12 | `||DPhi^+ r||` | 1.6016e-3 | 1.6329e-3 | 1.6392e-3 | 2.0418e-3 |
| 3 | 16 | `||DPhi^+ r||` | 1.4386e-3 | 1.4985e-3 | 2.2570e-3 | 2.3032e-3 |
| 2 | 14 | `||DPhi^+ r||` | 3.2299e-2 | 5.3872e-2 | 6.5051e-2 | 9.7111e-2 |

`||r|| = 1.6099e-3` in every d = 4 row and does not move with H, because by R3a Prop. C it
**is** `|Phi_1|`.  `lambda_1 = dist(g_1, span{Re g_h, Im g_h : 2 <= h <= H})` is constant to
four digits.  Looseness `(||r||/s_min)/||DPhi^+ r||` reaches **1.03e15** at d=4, L=10, H=256.

### The iteration — and what `s_min` really governs

`s_min` collapses in H at fixed L (d=4, L=12: 6.98e-3, 3.87e-6, 1.37e-9, 1.97e-15 at
H = 4, 32, 64, 256) and improves with L (H=64: 3.27e-10, 1.37e-9, 7.70e-9, 5.69e-8 at
L = 10..16).  Three solvers on the same problem, floor `2 pi H eps(J,M) ~ 7e-14`:

| d | H | L | chord | Levenberg-Marquardt | full Newton | floor |
| --- | --- | --- | --- | --- | --- | --- |
| 4 | 32 | 12 | 3.9e-10 | 6.96e-11 | **7.49e-15** (9 its) | 6.9e-14 |
| 4 | 64 | 12 | diverges | 2.70e-11 | **2.02e-12** (39 its) | 7.1e-14 |
| 4 | 64 | 14 | 6.1e-9 | 1.21e-10 | **2.11e-13** (19 its) | 7.1e-14 |
| 4 | 128 | 12 | 1.7e-8 | 2.57e-9 | **4.18e-12** (39 its) | 7.3e-14 |

The chord failure is diagnosed, not guessed: at d=4/H=64/L=12 the run goes
`1.610e-3 -> 3.400e-6 -> 6.398e-8`, then the surviving residual sits on a singular direction
of size ~6e-7, the least-norm correction is 0.108 in `L^2(pi)` (`max|dq| = 0.364`), it
overshoots, and the next step has norm 1.09e4.  Not the stationary solve: a longdouble
4000-step power iteration agrees to `|dPhi| <= 1.3e-17`.  **So `s_min` bounds the radius over
which a frozen Jacobian stays usable — a Newton-Kantorovich convergence hypothesis, i.e.
R3c's business — not whether `K_H` is reachable.**

`L*(H,d)`, smallest L at which full Newton reaches the window floor:

| | H=8 | 16 | 32 | 64 | 128 |
| --- | --- | --- | --- | --- | --- |
| d=2 | 8 | 8 | 8 | 10 | 12 |
| d=3 | 8 | 8 | 8 | 8 | 10 |
| d=4 | 8 | 8 | 10 | 12 | 14 |

`L* - log2 H` stays in [2, 7] over the whole grid and varies by at most 3 within a degree, so
`2^{L*}` is between `4H` and `128H` — **not exponential**, which reverses §7.3's
"`2^L >> 2H` is free; the question is entirely the conditioning, not the parameter count".
`max_b |dq(b)|` is 4.147e-3 at d=4/H=32/L=12 and 8.415e-3 at H=128, against the positivity
limit 1/2.  At d=2, where the residual is 30x larger, it is 0.30–0.45.

### What this is not

**Not a proof that `K_H != empty`.**  The iteration is float and drives `|Phi~_h|` to ~1e-14,
not to 0; `K_H` needs `Phi_h = 0` exactly, and that is Newton-Kantorovich, i.e. R3c.  And
`Phi~` is the windowed coefficient, so the certified statement is
`|Phi_h| <= |Phi~_h| + 2 pi H eps ~ 8e-14` — flatness, not membership.  What it does say is
that no measure this flat has ever been produced in this folder except by convex
combination, and that a pool centred at the Newton point would contain 0 with a margin no
Gibbs centre reaches — cheap to test at H = 128, where R2e's M7 half misses by 1.0455e-2.

## R3c: Newton-Kantorovich, and the first exact members of `K_H` (`r3c_kantorovich.py`, 2026-08-28)

Work package R3c: *"Newton-Kantorovich existence in a ball around Bernoulli, at the best `d`"*,
deliverable *"an exact `mu` in `K_H` with `H` unbounded in the family"*.  Full account in
`note-1061-R3c.html`; 17 self-checks, 282 claims read back by `r3c_checknote.py`.
**Half of it lands**: at every rung below there is now an exact shift-invariant Markov measure
`mu` with `Phi_h(mu) = 0` for every `h <= H` — a theorem about the TRUE `Phi`, not the windowed
one — with a certified lower bound on `h(mu)`, hence on `E_H`.  "Unbounded in `H`" does not.

### Theorem D, and why the frame matters

Underdetermined chord-Kantorovich.  With `V in R^{N x m}` spanning the row space of
`A = DPhi(xbar)`, `G(xi) = Phi(xbar + V xi)` and `T(xi) = xi - B G(xi)`:

    (i)   box  { x : |x - xbar|_inf <= rho ||V||_{2->inf} }  lies in U
    (ii)  kappa := sup_box || I - B DPhi(x) V ||  <  1
    (iii) eta   := || B Phi(xbar) ||  <=  (1 - kappa) rho

give a unique fixed point `xi*` with `||xi*|| <= eta/(1-kappa)`, and `Phi(xbar + V xi*) = 0`
EXACTLY.  Proof: mean value on `T`, then Banach.

**Both hypotheses are invariant under `Phi -> S Phi`, `B -> B S^{-1}`.**  So no singular value
of `DPhi` occurs in Theorem D; `s_min` enters only through the choice `B = (AV)^{-1}`.  With
that choice the theorem holds as soon as

    4 Lambda_1 ||V||_{2->inf} ||Phi(xbar)|| / s_min^2  <=  1,

which is **§7.3's own gate G-3, `residual/s_{H,L}`, squared and read at the Newton point**.
R3a was right that it is the wrong statistic for the first Newton step and R3b measured it
wrong there by 1.03e15; R3c is the stage where it is exactly right, because Newton-Kantorovich
*is* the chord iteration whose radius R3b found `s_min` governing.  The difference is that
`||Phi||` at the Newton point is 1e-30, not Bernoulli's 1.6e-3.

### The four certified inputs

* **Prop. E** (the Lipschitz constant of `DPhi`): three convex-combination recursions on
  `S_p = ||W_p||_inf`, `N_p = ||V_p||_1` of R3b §2.1.  Loose by 1e4–1e6 against the measured
  variation — harmless, because the box half-width is `beta ~ 1e-24`.  Looseness in `Lambda`
  costs bits of `S`; looseness in `s_min` would cost rungs.
* **pi**: R1a's "verified eigenvector, the one expensive step in the whole lane" is discharged
  cheaply.  The order-`L` de Bruijn chain forgets in exactly `L` steps — each block is reached
  from any block along one deterministic path — so `tau(P^L) <= 1 - (2m)^L`,
  `m = min_b min(q_b, 1-q_b)`.  The price is a hard cap on `max_b |q(b) - 1/2|` (0.30 at d=2,
  0.25 at d>=3), which costs a unit or two of `L` and *raises* `h(mu)`.
* **arithmetic**: every quantity in the forward pass has modulus <= 1, so the pass runs in
  EXACT FIXED POINT — pairs of Python integers over `2^S`, `S = 160` — with radius
  `6K(1+eta_c) 2^-S ~ 1e-30` instead of longdouble's 1e-15.  **Precision is logarithmic**
  (`S >~ 2 log2(1/s_min)`) and never binds.  What binds instead is `||B|| ||A_float - DPhi||`,
  the *Jacobian's* arithmetic, so that runs in longdouble too: at d=4, H=16 that one change
  takes `kappa` from 1.57e-3 to 9.32e-7.
* **window**: R3a Theorem A at `2 pi H eps <= 1e-30` (`K` = 175 / 296 / 486 at d = 2/3/4,
  against 87 / 148 / 244 at the folder's 1e-13).  Prop. G bounds the truncation of the
  *derivative* by `2 pi h eps (6K+1)`, by running Prop. E's recursions with the perturbation in
  the constants rather than in `q`.

### The frontier, and `E_H`

`h(mu) >=` at each certified rung (`L`, and Theorem D's contraction factor):

| d | H=8 | H=16 | H=32 | H=64 | H=128 | H=256 |
| --- | --- | --- | --- | --- | --- | --- |
| 2 | 0.689761 (L=8, k=4.6e-12) | 0.687719 (L=8, k=1.6e-11) | 0.686209 (L=10, k=9.6e-11) | 0.682967 (L=12, k=8.1e-10) | 0.680787 (L=14, k=2.8e-02) | 0.674709 (L=14, k=2.9e-08) |
| 3 | 0.693136 (L=8, k=4.9e-10) | 0.693106 (L=8, k=9.3e-10) | 0.693072 (L=8, k=2.9e-08) | 0.692945 (L=10, k=6.5e-08) | 0.693043 (L=12, k=5.0e-07) | — |
| 4 | 0.693092 (L=8, k=8.8e-08) | 0.693091 (L=8, k=9.3e-07) | 0.693134 (L=10, k=2.0e-05) | 0.693142 (L=12, k=1.5e-03) | — | — |

Every entry is a theorem: *there is a shift-invariant memory-`L` Markov measure with
`int e(hF) dmu = 0` for all `h <= H`, of entropy at least that number.*  The `d = 3`
(`X^3-2X^2-1`) and `d = 4` (`X^4-2X^3-1`) rows are **new outright** — before this note the
folder's knowledge of the degeneration family was the Bernoulli column of §7.2 — and they
clear the Ledrappier-Young floor `h_min` by at least 0.42928 and 0.53167, against floors of
0.263662 and 0.161416.

At `1+sqrt2` the single measure overtakes the pool lane from `H = 64` on: `E_64 >= 0.682967` (was 0.677794), `E_128 >= 0.680787` (was 0.605736), `E_256 >= 0.674709` (was 0.582936) — so the
H=128 bracket narrows from 7.734e-2 to 2.290e-3 (a factor 34) and the H=256 bracket from 1.001e-1
to 8.368e-3 (a factor 12).  Cost: eleven minutes for H=128 in longdouble, thirteen hours for H=256
in fixed point, against the sixteen hours R2e's two pools cost for brackets an order wider.
The pool bound is a linear programme that *maximises* entropy over a hull, so it wins at
`H <= 32` (R2c's `E_16 >= 0.689054`, `E_32 >= 0.687024`); the Newton point is only the
least-norm zero nearest Bernoulli and nothing here looks for the maximiser.  From `H = 64` the
pool degrades — R2e's M7 half stops enclosing 0 and the LP has to spend hull on entropy-free
periodic orbits — while the Newton measure does not move.

### What this is not

**Not a refutation of 10.61.**  That needs `K_H != empty` with entropy above `h_min` for
*every* `H` at one fixed alpha; this is finitely many `H` at each of three alpha, each rung its
own certificate with its own `xbar` and its own `L`.  **Gate G-4** is the uniform-in-`H`
question, and a parameter count says not to expect one inside the Markov family: `2^L`
parameters against `2H` equations is overdetermined once `2H > 2^L` — a count, not a proof —
and R3b's `L*(H) ~ log2 H` is what the machine measures.
The entropies are lower bounds on `E_H` and loose ones — a projected ascent along the
`(2^L - 2H)`-dimensional solution manifold would raise every row and costs one Jacobian per
step.  And flatness to degree `H` is not flatness: `Phi_h(mu) = 0` for `h <= H` constrains
`2H` Fourier coefficients of `F_*mu`, nothing more.

## M3 Theorem 4 in Lean: the past drops out (LadderReduction.lean, 2026-08-27)

Theorem 4 is M3's own item (i), the reduction that deleted the past.  The note proves it on
the torus `T^d_Lambda`: `lambda-hat(gamma) = lambda-hat(alpha gamma)` by `Mbar`-invariance,
then the corrected Meyer estimate (Prop. 2) applied to `alpha^m gamma`.  At degree two that
whole apparatus can be skipped, and the theorem is an **identity between real numbers**:

```
Tr_m * t(omega+) = (an integer) + Ftilde(sigma^m omega) + E_m(omega),   |E_m| <= (W+1)|beta|^m
```

`traceSeq_mul_piVal_futures` and `abs_ladderErr_le`, with `Tr_m = alpha^m + beta^m` the trace
ladder of `BlockRecoding.lean` and `Ftilde = t(omega+) - S(omega-)` the factor map of
`Factor.lean` before reduction mod one.

### Why the past drops out

One line of `Bernoulli.lean`, read backwards.  `trace_pw` says
`(alpha-1)alpha^j + (beta-1)beta^j = T_j` is a rational integer; read as a *decomposition*,

```
(alpha-1) alpha^j  =  T_j  -  c_j            (futureWeight_eq)
```

the `j`-th **future** weight is an integer minus the `j`-th **window** weight.  Multiplying
`t(omega+)` by `alpha^m` walks the first `m` future letters backwards past the origin; each
lands on `(alpha-1)alpha^j`, and `futureWeight_eq` converts it -- modulo an integer, which the
character cannot see -- into exactly the window weight it would have carried in
`S((sigma^m omega)-)`.  **The past coordinates were the future coordinates all along**, and
the trace ladder is the change of variables.  The two leftovers are the window beyond depth
`m` and the conjugate leak `beta^m t(omega+)`; both are `O(|beta|^m)`, and they are the note's
`W` and its `d - 1` at `d = 2`.

Nothing here needs `alpha` to be a unit -- Theorem 4 is the one result of sec. 4 that does not
-- and nothing needs an ergodic theorem.  Only `sigma`-invariance of `mu`.

### The statements

| declaration | content |
| --- | --- |
| `traceSeq_mul_piVal_futures` | the identity, at every word and every depth |
| `abs_ladderErr_le` | `|E_m| <= (W+1)|beta|^m`, `W = |beta-1|/(1-|beta|)` |
| `norm_fourier_int_add_sub` | `e(.)` is `2pi|n|`-Lipschitz and blind to the integer head |
| `thm4` | **Theorem 4**: `||nu-hat(h Tr_m) - Phi_h(mu)|| <= 2 pi |h| (W+1) |beta|^m` |
| `tendsto_futureCoeff` | `Phi_h(mu) = lim_m nu-hat(h Tr_m)`, geometric rate |
| `exists_tendsto_futureCoeff` | **M3 Cor. 5 at integer frequencies**: the plateau exists for *every* invariant measure |
| `not_equidistributed_of_ladder` | 10.61 at `alpha` from the future marginal alone |

`phiCoeff mu h = int e(hF) dmu` and `futureCoeff mu n = int e(n t(omega+)) dmu` are the two
coefficients; the second is `nu-hat` for the future marginal `nu = t_*mu`, a measure on
`C(alpha)`.

### What is deliberately not here

1. **General frequencies.**  Prop. 2 and Thm. 4 are stated for every `gamma` in the
   codifferent `f'(alpha)^-1 Z[alpha]`; here `gamma` is an ordinary integer `h`.  That is the
   case the criterion uses, and by M3 Cor. 6 it is the only case that may enter a proof -- but
   Cor. 6 needs the codifferent, which `TraceLadder.lean` has and this file does not consume.

2. **The converse.**  The note's displayed equivalence also uses that every `T`-invariant `nu`
   on `C(alpha)` is the future marginal of a `sigma`-invariant `mu` (its natural extension).
   That is not formalised, so `not_equidistributed_of_ladder` proves the direction that does
   not need it.

### Numerics

`m3_thm4_lean.py`, 8/8 at `mp.dps = 120`:

| check | result |
| --- | --- |
| T1 | `(alpha-1)alpha^j = T_j - c_j` over 6 setups and 40 depths, residual `2.9e-95`, every `T_j` an integer |
| T2 | the identity on 576 (setup, periodic word, depth) triples, residual `5.7e-112` |
| T3 | `|E_m| <= (W+1)|beta|^m` on 672 instances, worst ratio `0.4822`; the window tail alone already saturates `1*|beta|^m`, so **neither summand of `W+1` can be dropped** |
| T4 | the character estimate on 4000 random inputs: Lipschitz ratio up to `0.9997` (the constant `2pi|n|` is nearly sharp), integer head invisible to `2.99e-116` |
| T5 | Theorem 4 on 1248 periodic-orbit instances -- each a genuine invariant measure -- worst ratio `0.1667` |
| T6 | Bernoulli(1/2) in closed form: `nu-hat(Tr_m) -> Phi_1` on all 6 setups, geometric rate at or below `|beta|` everywhere; **not attained** (at `2+sqrt3`, `0.1004` against `0.2679`), and at norm `-1` the successive ratios oscillate |
| T7 | Cor. 5 on 36 non-Bernoulli invariant measures: the ladder limit exists and equals `Phi_h`, residual `1.3e-05` by depth 14 |
| T8 | **anchor**: `|Phi_h|` along M0's own ladder `780, 2911, 10864, ...` at `2+sqrt3` settles at `0.359300`, exactly M0's plateau-table value -- so the Lean `phiCoeff` is the note's `Phi`, same normalisation |

T8 is what makes the rest checkable against the folder's own history: the plateau M0 measured
in its sec. 4 table is `lim_k |Phi_{h_k}|` for Bernoulli, and the Lean `phiCoeff` reproduces it
to every printed digit.

## M3 Corollary 6 in Lean: which ladders may enter a proof (LadderScope.lean, 2026-08-27)

Corollary 6 is the scope restriction that comes attached to Theorem 4, and it is aimed at M1.

M1 Proposition 15 (`TraceLadder.lean`) identified the ladders as the whole codifferent
`d^-1 = f'(alpha)^-1 Z[alpha]`, and M1's finding F8 then measured what the choice inside it is
worth: at `alpha = 1+sqrt2` the **half-ladder** `1,1,3,7,17,41,99,239` (`gamma = 1/2`) plateaus
at `3.4511464e-2` against the trace ladder's `7.6370923e-5`, a **factor 452**, so M1 prescribed
*maximise over* `gamma in d^-1 / alpha^Z`.  Corollary 6 says that is a **detection**
instruction and not a **proof** instruction:

> `tau-bar_* lambda = Leb` forces `lambda-hat(gamma) = 0` **exactly** for
> `gamma in alpha^Z (Z \ {0}) cap d^-1`.  Outside that set the hypothesis says nothing, so the
> corresponding ladder cannot appear in a proof by contradiction.

### One divisibility condition does both halves

That is the shape of the file, and it is why the note's example is `1+sqrt2`.  The trace form
on `Z[alpha]` in the basis `(1, alpha)` is `Tr(u + v alpha) = 2u + av` (`trForm`), so

```
gamma = 1/2  in  d^-1     <=>     Tr(Z[alpha]) subset 2Z     <=>     2 | a
```

(`two_dvd_trForm_iff`) -- which is M1's own reason, "every `Tr(alpha^k)` is even", now stated
as an *iff* so that it also disqualifies the odd-trace case.  And **exactly when the half-ladder
exists it is odd at the origin**, while the trace ladder is even throughout and stays even
under the `alpha`-action in both directions (`two_dvd_traceSeq`, `two_dvd_traceSeqZ`).  So the
same condition that creates the competitor disqualifies it (`not_intOrbitLadder_halfLad`).

### One constraint per orbit

The positive half rides on Theorem 4.  In ladder coordinates `gamma = n alpha^j`, `j in Z`, has
`Tr(gamma alpha^k) = n T_{k+j}` for the two-sided ladder `traceSeqZ`, whose backwards half is
`T_{-m} = (-b)^m T_m` (grounded at a unit by `traceSeqZ_cast`: `T_n = alpha^n + beta^n` for
every `n in Z`).  `tendsto_futureCoeff_orbit` proves all of them have the **same** limit
`Phi_n(mu)`: an `alpha`-orbit of integer frequencies carries **one** constraint, not infinitely
many, whatever entry point one chooses.

### The statements

| declaration | content |
| --- | --- |
| `trForm`, `trForm_cast`, `half_trForm_eq` | the trace form `2u + av`, and `Tr(u+v alpha)/2 = u + cv` |
| `two_dvd_trForm_iff` | `Tr(Z[alpha]) subset 2Z` **iff** `2 | a` -- when `gamma = 1/2` is legal |
| `traceSeqZ`, `traceSeqZ_natCast`, `traceSeqZ_cast` | the two-sided trace ladder, and `T_n = alpha^n + beta^n` for `n in Z` at a unit |
| `two_dvd_traceSeq`, `two_dvd_traceSeqZ` | evenness, forwards and backwards |
| `lad_smul`, `halfLad`, `two_mul_halfLad` | ladders are `Z`-linear in `(h_0, h_1)`; the half-ladder, and `2 H_k = T_k` |
| `halfLad_isTraceLadder` | M1 Prop. 15: the half-ladder **is** `Tr(gamma alpha^k)` for a genuine `gamma in d^-1` |
| `IntOrbitLadder` | the admissible family, `Tr(gamma alpha^k) = n T_{k+j}` |
| `tendsto_futureCoeff_orbit` | one constraint per orbit |
| `two_dvd_of_intOrbitLadder`, `not_intOrbitLadder_halfLad` | the parity obstruction |
| **`cor6`** | both halves: every admissible ladder vanishes in the limit under `F_*mu = Leb`, and the half-ladder is not admissible |
| `no_half_character` | `e(x/2)` does not descend to `R/Z` |
| `silver_not_intOrbitLadder`, `twoAddSqrt3_not_intOrbitLadder` | the two named cases, with their F8 ladder values |

`no_half_character` is what "the hypothesis says nothing" means for *measures* rather than for
ladders: `tau-bar_* lambda` is a measure on `R/Z`, and `e(x/2) = exp(i pi x)` changes sign under
`x -> x+1`, so it is not a function on `R/Z` at all.  No hypothesis about `tau-bar` modulo one
can constrain `lambda-hat(1/2)` in any way.

### What this is not

**A decision procedure.**  Parity certifies inadmissibility; it does not classify.  At
`1+sqrt2` the ladder `lad 2 4 = 2,4,10,24,58,140,...` is even throughout and is still outside
`alpha^Z Z` (its frequency is `(1+alpha)/2`).  An all-even ladder need not be admissible; an odd
one is certainly not, and that is all Corollary 6 needs.

`IntOrbitLadder` is the **ladder-level** definition of `alpha^Z (Z \ {0})`, justified by
`traceSeqZ_cast` plus linearity of the trace, not derived inside the number-field API.
`halfLad_isTraceLadder` is the bridge in the other direction, and it is the one place the file
consumes the codifferent: without it the half-ladder would be a sequence of integers rather than
a competitor.

### Numerics

`m3_cor6_lean.py`, 8/8 at `mp.dps = 120`:

| check | result |
| --- | --- |
| C1 | `Tr(Z[alpha]) subset 2Z <=> 2 | a` against brute force over the order, 0 exceptions on the 15 quadratics of `m0_gapsweep.json`; `gamma = 1/2` is legal at **9** of them (including `1+sqrt2` and `2+sqrt3`, illegal at `(3+sqrt5)/2`), and `Tr(u+v alpha)/2 = u + cv` to `1e-100` |
| C2 | `2 H_k = T_k` for `k <= 30` on all 9, and **M1's F8 ladder table reproduced exactly**: `2,2,6,14,34,82,198,478` / `1,1,3,7,17,41,99,239` at `1+sqrt2`, `2,4,14,52,194,724,2702` / `1,2,7,26,97,362,1351` at `2+sqrt3` |
| C3 | `T_n = alpha^n + beta^n` for every `n in [-25,25]` on the 9 quadratic units, worst deviation `1.13e-99` |
| C4 | every `n T_{k+j}` even (`|n| <= 40`, `|j| <= 12`, 0 exceptions); an exhaustive search over `0 < |n| <= 400`, `|j| <= 20` finds **no** `(n,j)` with `H_k = n T_{k+j}` |
| C5 | **M1's F8 plateau table recomputed** at rung 26: `7.6370923e-05` / `3.4511464e-02` at `1+sqrt2`, a factor `451.9` (note: 452); `8.2320916e-02` / `2.2641698e-02` at `2+sqrt3`, a factor `3.64` the other way (note: 3.6) |
| C6 | entering the orbit at `j in {-4,-2,0,2,4}` gives the same limit: worst spread `8.8e-15` over 2 alphas and `n in {1,2,3}` |
| C7 | `exp(i pi (x+1)) = -exp(i pi x)` at all 39 sample points, while `e(hx)` is unchanged for `h in {1,2,-3}` |
| C8 | the stated caveat: `lad 2 4` at `1+sqrt2` is even throughout and still has no `(n,j)` |

C5 is the anchor.  It recomputes, at 120 digits, the exact quantity M1's F8 table reports --
and Corollary 6 is the statement that the larger of the two numbers is the one a proof may not
use.

## M3 Theorems 7-8 in Lean: Route B is Route D with a minus sign (KernelCriterion.lean, 2026-08-28)

Section 5 of the note is where Route B is repaired and then dissolved.  Theorem 7 states the
B-criterion correctly; Theorem 8 says it has no strength outside the integers, so Route B
collapses onto Route D.  Both are now machine-checked, and the interesting part is what the
Lean proof does *not* need.

### Why the file is stated over `Z`

Because M3 Corollary 6 (`LadderScope.lean`) says nothing else is available.  Under the
counterexample hypothesis only `gamma in alpha^Z (Z \ {0})` is forced to vanish, and by
Theorem 4 the whole `alpha`-orbit of an integer `h` carries the single constraint `Phi_h(mu)`.
So over `Z` the note's integer reach `H_Gamma = {h : alpha^m h in Gamma - Gamma}` collapses to
`(Gamma - Gamma) \ {0}` and its condition (i) is **vacuous** -- which is exactly what
Theorem 8(c) observes.  The formalisation is therefore for `Gamma : Finset Z` and
`B : Matrix Gamma Gamma C`, and the reduction that licenses it is already in the repository.

### Two imported theorems, neither of them needed

**Bochner.**  The note gets `Q >= 0` from `B psd` by Bochner's theorem.  Put `B` in *Gram*
form, `B_{gg'} = sum_k w_k(g) conj(w_k(g'))`, and

```
Q_B  =  sum_k | sum_g w_k(g) e(g .) |^2          (matKernel_gram)
```

is nonnegative by inspection.  `gram_posSemidef` records that these are honest positive
semi-definite matrices.  And positivity turns out to be irrelevant to the *validity* of
Theorem 7: the proof never uses it, and `not_equidistributed_of_kernel` is stated for an
**arbitrary** matrix.  `B psd` is what makes the criterion satisfiable, not what makes it
sound.

**Fejer-Riesz.**  The note proves 8(c) by factoring `A - G = |P|^2`.  Mathlib has no such
factorisation, and it is not needed, because the criterion has slack: it is enough to write
down *one* explicit sum of squares with the right non-constant part.  The one-term polynomials
`1 - a_h e(h .)` do it -- their squared moduli are `1 + |a_h|^2 - 2 Re(a_h e(h .))` -- so on
`Gamma = {0} u H`,

```
Q  =  c(0) - 2G        exactly       (exists_kernel_of_trigCertificate)
```

with `c(0) = sum_h (1 + |a_h|^2)`.  This is **not** a re-derivation of the note's kernel: the
numerics check that the two nonnegative trigonometric polynomials differ by at least `3.73` in
sup norm.  It is a different object doing the same job, which is all the criterion asks for.

### The collapse, in one line

The same identity read backwards is Theorem 7.  A kernel with a uniform gap **is** a Route D
certificate, namely `G = c(0) - Q` (`kernelCertificate`), because `int_T Q_B = tr B` makes
`c(0)` the kernel's own Lebesgue mean.  So *Route B and Route D are the same object up to a
change of sign*, and that is the whole of Theorem 8.

### The statements

| declaration | content |
| --- | --- |
| `matKernel`, `matTrace` | `Q_B = sum B_{gg'} e((g-g') .)` and `c(0) = tr B` |
| `integral_matKernel` | `int_T Q_B = c(0)` |
| `integral_matKernel_comp`, `..._eq_trace` | `int Q_B . F dmu` in the coefficients `Phi_delta(mu)`; the one computation Theorems 7 and 8(a) both run on |
| `kernelCertificate`, `not_equidistributed_of_kernel` | **Theorem 7** |
| `no_killer_of_kernel` | **Theorem 8(a)**: a kernel forbids every invariant measure killing its integer reach |
| `no_killer_of_trigCertificate` | **8(b)**, easy direction |
| `exists_trigCertificate_of_no_killer` | **8(b)**, completeness -- M3 Thm 9's separation with the test family *prescribed*, in `R^{H x Bool}` |
| `exists_kernel_of_trigCertificate` | **Theorem 8(c)** |
| **`exists_kernel_iff`** | **Theorem 8**: integer kernel, trigonometric certificate and the master target of M1 Thm 7 are one condition |
| `exists_gap_of_pointwise`, `confCircle_ne_univ_of_kernel` | the note's first sanity check |
| `silver_not_pointwise_kernel`, `goldenSq_not_pointwise_kernel` | the two `alpha` where it is empty |

### The sanity check, and where it bites

The note's parenthetical strong form of (ii), `sup_Omega Q < c(0)`, does supply the uniform gap
(`exists_gap_of_pointwise`, by compactness of `X(alpha)`), so it is a genuine sufficient
condition.  But it forces `X(alpha) != T`, and the proof is one line of bookkeeping: `int_T Q`
*is* `c(0)`, so `Q < c(0)` everywhere on `T` contradicts `Q`'s own mean.  **A pointwise kernel
is never more than M4/X8's confinement gap.**  With `FullSupport.lean`'s `X(1+sqrt2) = T` and
`X((3+sqrt5)/2) = T` that makes it *empty* at exactly the two `alpha` where M4 is known to be
blind -- Route B has no reserve of strength there.

### What is not here

* The note's **second** sanity check (the G-R freedom is neutral) is M2 Proposition 8,
  `BlockRecoding.lean`, and is not repeated.
* **`Gamma` inside the full codifferent**, with the note's condition (i).  Corollary 6 is the
  reason: over the non-integer part the hypothesis supplies nothing, so (i) is the demand that
  the kernel not use what it cannot know.  Making it precise needs the solenoid characters
  `chi_gamma`, which the repository does not have and which Theorem 8 says are inert.
* **`PosSemidef -> Gram`** (Cholesky), absent from Mathlib.  Only `gram_posSemidef` is proved,
  and nothing is lost: Theorem 7 holds for an arbitrary matrix and 8(c) lands in the Gram class.

### Numerics

`m3_thm78_lean.py`, 8/8 at `mp.dps = 50`:

| check | result |
| --- | --- |
| T1 | `Q_B = sum_k |P_k|^2` to `9.0e-49` on 24 random Gram kernels, `Q_B >= 0` with 0 violations, Gram matrices PSD to `-8.9e-16` |
| T2 | `int_T Q_B = tr B`, worst `1.8e-49` over a 4096-point grid |
| T3 | `int Q.F dmu = Re sum B_ij Phi_{gi-gj}(mu)` on 12 periodic-orbit instances to `1.1e-50`; a measure killing the off-diagonal reach gives exactly `tr B` |
| T4 | `G = c(0) - Q` has zero mean, worst `2.6e-50` |
| T5 | Theorem 8(c) on 20 random `(H, a)`: `Q = c(0) - 2G` exact to `2.1e-50`, `c(0) = sum (1+|a_h|^2)`, Gram PSD |
| T6 | this file's `Q` and the note's `A - G` differ by **at least `3.73`** in sup norm on all 12 instances, and `Q` stays nonnegative at all 480 sample points |
| T7 | `sup_T Q >= int_T Q = c(0)` on 15 random kernels (worst margin `0.271`) |
| T8 | **anchor**: an explicit convex combination of 9 periodic orbits at `1+sqrt2` kills the first 4 Fourier modes (residual `1.3e-17`), and then **every** kernel of that reach has `int Q.F dmu = tr B` to `1.8e-16` |

T8 is the anchor because it re-derives M3's own section 7 finding -- `c(alpha) = 0` exactly, no
kernel of bounded reach certifies anything at `1+sqrt2` -- from Theorem 8(a) rather than from
the hull LP, and it agrees with `m3_hull.json`, which reports `inside` at all 16 tested degrees
up to `H = 256`.

## M3 Proposition 1 in Lean: the tube criterion is vacuous (Tube.lean, 2026-08-28)

Section 3 of the note audits the three moves of Route B in reverse order of damage, and
Proposition 1 is the one that kills move 3 outright.  The plan's engine was to

> kill `tau_* lambda = Leb` whenever the **tube** `T_K := {(u,w) : w in K_delta} mod Sigma` is
> not all of `T^d_Sigma` in measure -- a much weaker condition than Route A's,

with the B-criterion `Haar(T_K) < 1` read "morally: `Leb_{d-1}(K)` small relative to the
covolume of `Sigma`", and an expected coverage of **all quadratic Pisot `alpha > 2` with
`|alpha_2| < 1/2`, in particular every `X^2 - aX +- 1`, including the first genuinely hard case
`alpha = 1 + sqrt2`".  Proposition 1 says the criterion has no instances at all.

`Tube.lean` (486 lines, 36 declarations, std3, 0 cited axioms, 0 sorries) plus the two general
lemmas on `ForMathlib/Topology/Algebra/DenseCover.lean`.

### The criterion is one-dimensional, and that part is algebra

The tube is unrestricted in the first coordinate, so a lattice vector's first coordinate can
always be absorbed and only its **shadow** -- the conjugate coordinates,
`shadow Lambda := Prod.snd '' Lambda` -- is ever tested:

`tube_add_eq_univ_iff : T_B + Lambda = R^d  <->  B + shadow Lambda = R^{d-1}`.

No topology, no discreteness of `Lambda`, no restriction on the degree, and in particular
nothing about the *size* of `B`.  `QuotientAddGroup.image_mk_eq_univ_iff` (ForMathlib) carries
it to the torus, and Proposition 1 is then one line: a set with non-empty interior plus a dense
set is everything (`add_dense_eq_univ`, also ForMathlib), so

`image_mk_tube_eq_univ (hLambda : Dense (shadow Lambda)) (hB : (interior B).Nonempty)`

is the general-degree theorem, with the density of the shadow as its only input.  That is a
clean split: everything before `namespace QuadSetup` holds in every degree; only the input is
discharged at `d = 2`.

### The note's Pontryagin duality is avoidable -- which matters, since Mathlib has none

The note proves the density of `L` (the image of the line `R x {0}`) by duality on
`T^d_Lambda`: a character is trivial on `L` only if it is `0`.  Mathlib has no Pontryagin
duality (the same wall as the W13 defect taxonomy), and it is not needed.  At degree two the
shadow is `Z + beta Z` and

* `beta^n` lies in it, by the integer recursion `(p,q) -> (q b, p + q a)` from
  `beta^2 = a beta + b` (`beta_pow_mem_shadow`);
* it is non-zero exactly when `b != 0`, since `alpha beta = -b` (`alpha_mul_beta`);
* and `|beta| < 1` sends it to `0`.

So `0` is not isolated, and `AddSubgroup.dense_of_not_isolated_zero` finishes (`dense_shadow`).
No irrationality lemma appears either: a rational `beta` would be an integer of modulus `< 1`,
hence `0`.  `dense_image_mk_line` records the note's own statement as a corollary, but the main
proof does not route through it -- the tube already contains a whole line through each of its
points, so the covering question collapses to the shadow directly.

### What the criterion actually depends on

Not measure.  `exists_tube_small_shadow`: for every `eps > 0` there is a tube whose base has
Lebesgue measure below `eps * covol` and whose image is still all of the torus, with
`covol = |alpha - beta|`, `covol^2 = a^2 + 4b`.  The plan's "morally `Leb_1(K)`/covolume" is a
real number, but it is not the Haar measure of anything, and no inequality between it and `1`
can ever produce a margin.  `no_tube_criterion` is the verdict in one statement: there is no
`B` with non-empty interior whose tube has measure `< 1`.

### The dichotomy at `delta = 0`

This is what makes the vacuity sharp rather than accidental, and it lands exactly on Route B's
target family.  When `|beta| < 1/2` -- the plan's own expected-coverage condition -- M1
Lemma 3 (`BoxDim.lean`) gives `dim_B K <= log 2 / log |beta|^-1 < 1`, so the **exact** window is
Lebesgue-null (`volume_windowSet_eq_zero`), and a null base never covers, because its
one-dimensional trace `B + (Z + beta Z)` is a countable union of null translates
(`image_mk_tube_ne_univ_of_volume_zero`).  Therefore

`tube_window_dichotomy` : `delta > 0 => T_{K_delta}` is everything, and `T_K` is not.

The function `delta -> Haar(T_{K_delta})` is identically `1` on `delta > 0` and drops to `0` at
`delta = 0`; it takes no intermediate value.  A trigonometric kernel is continuous and cannot
concentrate on a null set, so the plan's fattening is forced -- and at every `delta` it is
allowed, the tube is the whole torus.  There is no `delta` at which move 3 has a margin.
`silver_tube_window_dichotomy` and `goldenSq_tube_window_dichotomy` instantiate it at
`1 + sqrt2` and `(3 + sqrt5)/2`, the two `alpha` where `FullSupport.lean` shows M4 is blind.

### What is not proved here

* **Degree `> 2` needs its density input.**  For general `d` the abstract statements assume
  `Dense (shadow Lambda)`, i.e. that `{(sigma_2(x),...,sigma_d(x)) : x in Z[alpha]}` is dense in
  `R^{d-1}`.  True, but not formalised: the note's route is duality, and the contraction used
  here gives only non-discreteness once `d - 1 > 1`.
* **No Haar measure on the torus is built.**  `measure_prop1` and `no_tube_criterion` are
  stated for an arbitrary probability measure -- all a conclusion of `= 1` needs -- and the
  `delta = 0` half is a set identity plus a one-dimensional Lebesgue statement.
* **`Omega subset T_K` is not restated.**  That `lambda = Phi_* mu` lives on the tube over the
  window is M1 (`Confinement.lean`); Proposition 1 uses none of it.

### Numerics

`m3_prop1_lean.py`, 8/8 at `mp.dps = 80`:

| check | result |
| --- | --- |
| P1 | over 40 (target, interval) pairs at `1+sqrt2` the witness sets `(u,v)` for the two-dimensional tube condition and for the one-dimensional `z_2 - (u + v beta) in B` are **identical** and non-empty in every case |
| P2 | `alpha beta = -b` to `1e-70` on all 15 sweep quadratics; the integer recursion reproduces `beta^n` for `n <= 60` to `1e-60` on every one with `b != 0` |
| P3 | `covol^2 = a^2 + 4b` to `1e-70`; `covol = 2.8284271` at `1+sqrt2`, `3.4641016` at `2+sqrt3` |
| P4 | `Leb(B)/covol` driven from `0.0707` to `7.07e-7` with **zero** coverage failures; only the witness box grows, `N = 8, 128, 1024, 8192, 131072, 1048576` |
| P5 | `{v beta mod 1}` is `delta`-dense with `N(delta) = 8, 128, 1024, 8192` for `delta = 1e-1 .. 1e-4`, at all three `alpha` |
| P6 | over the 15 sweep quadratics with `beta != 0`, `dim_B K <= log2/log|beta|^-1` is `< 1` **exactly when** `|beta| < 1/2`; outer measures of the `2^n` covers at `n = 4, 8, 16, 32` |
| P7 | the plan's "expected coverage" holds for all **9** sweep units with `alpha > 2` (there `|beta| = 1/alpha`); its bound on `Leb_1(K)` over `covol` is `0.854` at `1+sqrt2` and `0.289` at `2+sqrt3`, against the true `Leb_1(K) = 0` |
| P8 | the max gap of `{v beta mod 1}` decays like `1/N` (`gap*N` between `1.2` and `1.8`) -- the note's `L` is dense -- while `|beta|^n` is the non-zero element below `1e-6` that the Lean proof uses instead |

P7 is the anchor: the plan's own criterion quantity is computed at the four named `alpha` and
compared with the two things it was supposed to be.  The Haar measure it stood for is `1` at
every `delta > 0`; the `Leb_1(K)` it bounds is `0`.  It is neither.
