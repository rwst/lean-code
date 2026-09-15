/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.Confinement
import BB61.WeylProduct
import ForMathlib.Analysis.Equidistribution.AddCircleWeyl
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# M5 Theorem 2: the Bernoulli Fourier coefficients of `F_*μ_p`

Formal companion of `note-1061-M5.html` (milestone M5 of `plans/plan-1061.html`) §4,
quadratic case.

`BB61/Factor.lean` built the factor map `F : {0,1}^ℤ → 𝕋`, `F(ω) = t(ω⁺) - S(ω⁻)`, and
`BB61/WeylProduct.lean` built the two real products `futProd`, `pastProd` and proved they
converge.  Neither file ever says what those products *are*.  This file says it:

> **Theorem 2.**  For `p ∈ [0,1]` and `h ∈ ℤ`,
> `G_p(h) := (F_*μ_p)^(h) = ∏_{j≥1} φ_p(h(α-1)α^{-j}) · ∏_{m≥0} φ_p(-h c_m)`,
> where `μ_p` is the Bernoulli(`p`) product measure on `{0,1}^ℤ`, `c_m = (β-1)βᵐ` and
> `φ_p(x) = (1-p) + p e(x)`.

## The route

The proof is the note's: independence, then a limit.

* `bern p`, `bernZ p` — the one-digit Bernoulli law and its product over `ℤ`.
* `integral_bernZ_finset_prod` — **independence**: the integral of a finite product of
  one-coordinate observables factorises.  This is Mathlib's
  `integral_restrict_infinitePi` followed by `integral_fintype_prod_eq_prod`; no
  `iIndepFun` bookkeeping is needed.
* `integral_bernZ_cexp1_tsum` — **the limit**: for an absolutely summable family of
  frequencies `y : ℤ → ℝ`, `∫ e(∑_k y_k ω_k) dμ_p = ∏_k φ_p(y_k)`.  Dominated convergence
  along `atTop` on `Finset ℤ` (the bound is `1`, the measure a probability measure), against
  `multipliable_phi` on the product side.
* `freq`, `zsplit`, `tsum_freq_mul_bitR` — **the ladder is the coding**: with
  `y_k = h(α-1)α^{-k}` for `k ≥ 1` and `y_k = -h c_{-k}` for `k ≤ 0`, one has
  `h·F(ω) = ∑_{k∈ℤ} y_k ω_k`.  The future/past split is the reindexing `ℕ ⊕ ℕ ≃ ℤ`, done on
  the analytic side (`Summable.tsum_sum`, `Multipliable.tprod_sum`) rather than on the
  measure, so the product measure over `ℤ` is never taken apart.
* `integral_cexp1_fRaw` — **Theorem 2**, and `integral_fourier_map_fMap` the same statement
  read as a Fourier coefficient of the push-forward `F_*μ_p` on `AddCircle 1`.

## What it buys

* `norm_weylC_half` — `‖G_{1/2}(h)‖ = weylProd h`.  The real product of
  `BB61/WeylProduct.lean` had no consumer; it is now the modulus of a Fourier coefficient of
  a measure, which is what the note always claimed it was.
* `weylC_half_one_ne_zero` — `G_{1/2}(1) ≠ 0`, by `BB61/Bernoulli.lean`'s two factor
  non-vanishing lemmas (`cos_future_ne_zero`, where `α > 2` is spent, and
  `cos_past_ne_zero`) together with `tprod_phi_ne_zero` for the product itself.
* `map_fMap_bernZ_half_ne_volume` — hence `F_*μ_{1/2} ≠ Leb`: **the fair coin is not a
  counterexample measure** for Problem 10.61, at every quadratic Pisot `α > 2`.  This is the
  measure-level content of M5 Corollary 5, and the instance at `α = 2 + √3` is
  `map_fMap_bernZ_half_ne_volume_twoAddSqrt3`.

Not here: the genericity step (M5 Theorem 1 — a `ν`-generic digit word gives the orbit the
limit law `F_*ν̂`), which is what turns this measure statement into a statement about the
points of `C(α)`; and the `p ≠ 1/2` case of the non-vanishing, where every factor is
non-zero for the trivial reason `|φ_p| ≥ |1-2p|`.
-/

namespace BB61

open MeasureTheory Filter Topology

/-! ## Digits, characters -/

/-- The digit `b ∈ {0,1}` as a real number. -/
def bitR (b : Bool) : ℝ := if b then 1 else 0

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem dR_eq_bitR (ε : ℕ → Bool) (k : ℕ) : dR ε k = bitR (ε k) := rfl

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_bitR_le_one (b : Bool) : |bitR b| ≤ 1 := by
  unfold bitR; cases b <;> norm_num

/-- The additive character `e(x) = exp(2πi x)`. -/
noncomputable def cexp1 (x : ℝ) : ℂ := Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem norm_cexp1 (x : ℝ) : ‖cexp1 x‖ = 1 := by
  rw [cexp1, Complex.norm_exp_ofReal_mul_I]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cexp1_zero : cexp1 0 = 1 := by simp [cexp1]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cexp1_add (x y : ℝ) : cexp1 (x + y) = cexp1 x * cexp1 y := by
  rw [cexp1, cexp1, cexp1, ← Complex.exp_add]
  congr 1
  push_cast
  ring

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem continuous_cexp1 : Continuous cexp1 := by
  unfold cexp1
  fun_prop

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cexp1_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    cexp1 (∑ i ∈ s, f i) = ∏ i ∈ s, cexp1 (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [cexp1_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, cexp1_add, ih, Finset.prod_insert ha]

/-! ## The Bernoulli measure -/

/-- Bernoulli(`p`) on a single digit: mass `p` on `1`, mass `1-p` on `0`. -/
noncomputable def bern (p : ℝ) : Measure Bool :=
  ENNReal.ofReal (1 - p) • Measure.dirac false + ENNReal.ofReal p • Measure.dirac true

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem bern_apply_true (p : ℝ) : bern p {true} = ENNReal.ofReal p := by
  simp [bern]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem bern_apply_false (p : ℝ) : bern p {false} = ENNReal.ofReal (1 - p) := by
  simp [bern]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isProbabilityMeasure_bern {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    IsProbabilityMeasure (bern p) := by
  constructor
  have : (Set.univ : Set Bool) = {false} ∪ {true} := by
    ext b; cases b <;> simp
  rw [this, measure_union (by simp) (measurableSet_singleton _),
    bern_apply_true, bern_apply_false, ← ENNReal.ofReal_add (by linarith) h0]
  norm_num

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem bern_real_true {p : ℝ} (h0 : 0 ≤ p) : (bern p).real {true} = p := by
  rw [measureReal_def, bern_apply_true, ENNReal.toReal_ofReal h0]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem bern_real_false {p : ℝ} (h1 : p ≤ 1) : (bern p).real {false} = 1 - p := by
  rw [measureReal_def, bern_apply_false, ENNReal.toReal_ofReal (by linarith)]

/-- The integral against one Bernoulli digit. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem integral_bern {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (g : Bool → ℂ) :
    ∫ b, g b ∂(bern p) = ((1 - p : ℝ) : ℂ) * g false + ((p : ℝ) : ℂ) * g true := by
  have := isProbabilityMeasure_bern h0 h1
  rw [integral_fintype Integrable.of_finite, Fintype.sum_bool,
    bern_real_true h0, bern_real_false h1]
  simp only [Complex.real_smul]
  push_cast
  ring

/-- The characteristic function of one Bernoulli digit, `φ_p(x) = (1-p) + p e(x)`. -/
noncomputable def phi (p x : ℝ) : ℂ := ((1 - p : ℝ) : ℂ) + ((p : ℝ) : ℂ) * cexp1 x

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem integral_bern_cexp1 {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (x : ℝ) :
    ∫ b, cexp1 (x * bitR b) ∂(bern p) = phi p x := by
  rw [integral_bern h0 h1]
  simp [bitR, cexp1_zero, phi]

/-- The Bernoulli(`p`) product measure `μ_p` on the two-sided shift space `{0,1}^ℤ`. -/
noncomputable def bernZ (p : ℝ) : Measure Shift := Measure.infinitePi fun _ : ℤ => bern p

/-- **Independence of the coordinates**: the integral of a finite product of one-coordinate
observables is the product of their integrals. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem integral_bernZ_finset_prod {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (s : Finset ℤ) (g : ℤ → Bool → ℂ) :
    ∫ ω, ∏ k ∈ s, g k (ω k) ∂(bernZ p) = ∏ k ∈ s, ∫ b, g k b ∂(bern p) := by
  have := isProbabilityMeasure_bern h0 h1
  unfold bernZ
  have hres : ∀ ω : Shift, (fun y : (∀ k : s, Bool) => ∏ k : s, g k (y k)) (s.restrict ω)
      = ∏ k ∈ s, g k (ω k) := by
    intro ω
    simp only [Finset.restrict]
    exact Finset.prod_coe_sort s (fun k => g k (ω k))
  calc ∫ ω, ∏ k ∈ s, g k (ω k) ∂(Measure.infinitePi fun _ : ℤ => bern p)
      = ∫ ω, (fun y : (∀ k : s, Bool) => ∏ k : s, g k (y k)) (s.restrict ω)
          ∂(Measure.infinitePi fun _ : ℤ => bern p) := by
        simp only [hres]
    _ = ∫ y, ∏ k : s, g k (y k) ∂(Measure.pi fun k : s => bern p) :=
        integral_restrict_infinitePi (f := fun y : (∀ k : s, Bool) => ∏ k : s, g k (y k))
          (fun _ : ℤ => bern p)
          (Integrable.of_finite (μ := Measure.pi fun k : s => bern p)).aestronglyMeasurable
    _ = ∏ k : s, ∫ b, g k b ∂(bern p) := integral_fintype_prod_eq_prod _
    _ = ∏ k ∈ s, ∫ b, g k b ∂(bern p) :=
        Finset.prod_coe_sort s (fun k => ∫ b, g k b ∂(bern p))

/-! ## The characteristic function of a Bernoulli series -/

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem phi_sub_one (p x : ℝ) : phi p x - 1 = ((p : ℝ) : ℂ) * (cexp1 x - 1) := by
  simp only [phi]
  push_cast
  ring

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem norm_phi_sub_one_le {p : ℝ} (h0 : 0 ≤ p) {x : ℝ} (hx : 2 * Real.pi * |x| ≤ 1) :
    ‖phi p x - 1‖ ≤ 4 * Real.pi * p * |x| := by
  have hπ : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have hz : ‖((2 * Real.pi * x : ℝ) : ℂ) * Complex.I‖ = 2 * Real.pi * |x| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
  have hb : ‖cexp1 x - 1‖ ≤ 2 * (2 * Real.pi * |x|) := by
    rw [cexp1]
    have := Complex.norm_exp_sub_one_le (x := ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
      (by rw [hz]; exact hx)
    rwa [hz] at this
  calc ‖phi p x - 1‖ = p * ‖cexp1 x - 1‖ := by
        rw [phi_sub_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
    _ ≤ p * (2 * (2 * Real.pi * |x|)) := by
        exact mul_le_mul_of_nonneg_left hb h0
    _ = 4 * Real.pi * p * |x| := by ring

/-- Absolute convergence of the Erdős product, in the form `∑ ‖φ_p(y_k) - 1‖ < ∞`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem summable_norm_phi_sub_one {p : ℝ} (h0 : 0 ≤ p) {ι : Type*} {y : ι → ℝ}
    (hy : Summable fun k => |y k|) : Summable fun k : ι => ‖phi p (y k) - 1‖ := by
  refine Summable.of_norm_bounded_eventually
    (g := fun k : ι => 4 * Real.pi * p * |y k|) ((hy.mul_left _)) ?_
  have hcof : Tendsto (fun k : ι => |y k|) cofinite (nhds 0) := hy.tendsto_cofinite_zero
  have hev : ∀ᶠ k in Filter.cofinite, |y k| < 1 / (2 * Real.pi) :=
    hcof (Iio_mem_nhds (by positivity : (0 : ℝ) < 1 / (2 * Real.pi)))
  filter_upwards [hev] with k hk
  have h2 : (0 : ℝ) < 2 * Real.pi := by positivity
  have hx : 2 * Real.pi * |y k| ≤ 1 := by
    calc 2 * Real.pi * |y k| ≤ 2 * Real.pi * (1 / (2 * Real.pi)) :=
          mul_le_mul_of_nonneg_left hk.le h2.le
      _ = 1 := by field_simp
  simpa using norm_phi_sub_one_le h0 hx

/-- The Erdős product `∏ φ_p(y_k)` converges absolutely whenever `∑ |y_k|` does. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem multipliable_phi {p : ℝ} (h0 : 0 ≤ p) {ι : Type*} {y : ι → ℝ}
    (hy : Summable fun k => |y k|) : Multipliable fun k : ι => phi p (y k) := by
  have hrw : (fun k : ι => phi p (y k)) = fun k : ι => 1 + (phi p (y k) - 1) := by
    funext k; ring
  rw [hrw]
  exact multipliable_one_add_of_summable (summable_norm_phi_sub_one h0 hy)

/-- The product is **non-zero** as soon as no factor vanishes. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tprod_phi_ne_zero {p : ℝ} (h0 : 0 ≤ p) {ι : Type*} {y : ι → ℝ}
    (hy : Summable fun k => |y k|) (hne : ∀ k, phi p (y k) ≠ 0) :
    ∏' k : ι, phi p (y k) ≠ 0 := by
  have hrw : (fun k : ι => phi p (y k)) = fun k : ι => 1 + (phi p (y k) - 1) := by
    funext k; ring
  rw [hrw]
  exact tprod_one_add_ne_zero_of_summable (fun k => by simpa using hne k)
    (summable_norm_phi_sub_one h0 hy)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem measurable_bitR : Measurable bitR := measurable_from_top

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isProbabilityMeasure_bernZ {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    IsProbabilityMeasure (bernZ p) := by
  have := isProbabilityMeasure_bern h0 h1
  unfold bernZ
  infer_instance

/-- **M5 Theorem 2, the analytic half.**  For an absolutely summable family of frequencies
`y : ℤ → ℝ`, the expectation of the character `e(∑_k y_k ω_k)` under the Bernoulli(`p`)
product measure is the absolutely convergent product `∏_k φ_p(y_k)`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem integral_bernZ_cexp1_tsum {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) {y : ℤ → ℝ}
    (hy : Summable fun k => |y k|) :
    ∫ ω, cexp1 (∑' k : ℤ, y k * bitR (ω k)) ∂(bernZ p) = ∏' k : ℤ, phi p (y k) := by
  have hprobZ := isProbabilityMeasure_bernZ h0 h1
  have hsum : ∀ ω : Shift, Summable fun k : ℤ => y k * bitR (ω k) := by
    intro ω
    refine Summable.of_norm_bounded hy fun k => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_bitR_le_one _)
  have hmeas : ∀ s : Finset ℤ,
      Measurable fun ω : Shift => cexp1 (∑ k ∈ s, y k * bitR (ω k)) := by
    intro s
    refine continuous_cexp1.measurable.comp (Finset.measurable_sum s fun k _ => ?_)
    exact measurable_const.mul (measurable_bitR.comp (measurable_pi_apply k))
  have hfin : ∀ s : Finset ℤ, ∫ ω, cexp1 (∑ k ∈ s, y k * bitR (ω k)) ∂(bernZ p)
      = ∏ k ∈ s, phi p (y k) := by
    intro s
    have hprod : ∀ ω : Shift,
        cexp1 (∑ k ∈ s, y k * bitR (ω k)) = ∏ k ∈ s, cexp1 (y k * bitR (ω k)) :=
      fun ω => cexp1_sum s _
    simp_rw [hprod]
    rw [integral_bernZ_finset_prod h0 h1 s fun k b => cexp1 (y k * bitR b)]
    exact Finset.prod_congr rfl fun k _ => integral_bern_cexp1 h0 h1 (y k)
  have hlim : Tendsto (fun s : Finset ℤ => ∫ ω, cexp1 (∑ k ∈ s, y k * bitR (ω k)) ∂(bernZ p))
      atTop (nhds (∫ ω, cexp1 (∑' k : ℤ, y k * bitR (ω k)) ∂(bernZ p))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => 1)
      (Eventually.of_forall fun s => (hmeas s).aestronglyMeasurable)
      (Eventually.of_forall fun s => ae_of_all _ fun ω => ?_)
      (integrable_const 1) (ae_of_all _ fun ω => ?_)
    · exact le_of_eq (norm_cexp1 _)
    · exact (continuous_cexp1.tendsto _).comp (hsum ω).hasSum
  refine tendsto_nhds_unique ?_ (multipliable_phi h0 hy).hasProd
  rw [SummationFilter.unconditional_filter]
  simpa only [hfin] using hlim

/-! ## The two-sided frequency ladder -/

/-- The future/past split of the index line: `inl j ↦ j+1`, `inr m ↦ -m`. -/
def zsplit : ℕ ⊕ ℕ ≃ ℤ where
  toFun := Sum.elim (fun j => (j : ℤ) + 1) (fun m => -(m : ℤ))
  invFun k := if 1 ≤ k then Sum.inl (k - 1).toNat else Sum.inr (-k).toNat
  left_inv := by
    rintro (j | m)
    · show (if 1 ≤ ((j : ℤ) + 1) then Sum.inl (((j : ℤ) + 1) - 1).toNat
          else Sum.inr (-((j : ℤ) + 1)).toNat) = Sum.inl j
      split_ifs with hh
      · exact congrArg Sum.inl (by omega)
      · exact absurd (by omega : (1 : ℤ) ≤ (j : ℤ) + 1) hh
    · show (if 1 ≤ (-(m : ℤ)) then Sum.inl ((-(m : ℤ)) - 1).toNat
          else Sum.inr (-(-(m : ℤ))).toNat) = Sum.inr m
      split_ifs with hh
      · exact absurd hh (by omega)
      · exact congrArg Sum.inr (by omega)
  right_inv := by
    intro k
    show Sum.elim (fun j : ℕ => (j : ℤ) + 1) (fun m : ℕ => -(m : ℤ))
        (if 1 ≤ k then Sum.inl (k - 1).toNat else Sum.inr (-k).toNat) = k
    split_ifs with hk
    · simp only [Sum.elim_inl]; omega
    · simp only [Sum.elim_inr]; omega

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem zsplit_inl (j : ℕ) : zsplit (Sum.inl j) = (j : ℤ) + 1 := rfl

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem zsplit_inr (m : ℕ) : zsplit (Sum.inr m) = -(m : ℤ) := rfl

namespace QuadSetup

variable (P : QuadSetup)

/-- The two-sided frequency ladder of the mode `h`: the future frequency
`h(α-1)α^{-k}` at an index `k ≥ 1`, the past frequency `-h c_{-k}` at an index `k ≤ 0`. -/
noncomputable def freq (h : ℝ) : ℤ → ℝ := fun k =>
  if 1 ≤ k then h * (P.α - 1) / P.α ^ k.toNat else -(h * P.cCoef (-k).toNat)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem freq_inl (h : ℝ) (j : ℕ) :
    P.freq h (zsplit (Sum.inl j)) = h * (P.α - 1) / P.α ^ (j + 1) := by
  rw [zsplit_inl]
  unfold freq
  split_ifs with hh
  · rw [show ((j : ℤ) + 1).toNat = j + 1 by omega]
  · exact absurd (by omega : (1 : ℤ) ≤ (j : ℤ) + 1) hh

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem freq_inr (h : ℝ) (m : ℕ) :
    P.freq h (zsplit (Sum.inr m)) = -(h * P.cCoef m) := by
  rw [zsplit_inr]
  unfold freq
  split_ifs with hh
  · exact absurd hh (by omega)
  · rw [show (-(-(m : ℤ))).toNat = m by omega]

/-! ### Summability of the ladder -/

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem summable_abs_freq_inl (h : ℝ) :
    Summable fun j : ℕ => |h * (P.α - 1) / P.α ^ (j + 1)| := by
  have hα := P.one_lt
  have hpos : (0 : ℝ) < P.α := P.alpha_pos
  have hrw : ∀ j : ℕ, |h * (P.α - 1) / P.α ^ (j + 1)|
      = |h * (P.α - 1)| * (P.α⁻¹ ^ (j + 1)) := by
    intro j
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < P.α ^ (j+1)), div_eq_mul_inv, ← inv_pow]
  simp only [hrw]
  exact (summable_geom_succ (inv_pos_of_one_lt hα).le (inv_lt_one_of_one_lt hα)).mul_left _

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem summable_abs_freq_inr (h : ℝ) :
    Summable fun m : ℕ => |(-(h * P.cCoef m))| := by
  have : ∀ m : ℕ, |(-(h * P.cCoef m))| = |h| * |P.cCoef m| := by
    intro m; rw [abs_neg, abs_mul]
  simp only [this]
  exact P.summable_abs_cCoef.mul_left _

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem summable_abs_freq (h : ℝ) : Summable fun k : ℤ => |P.freq h k| := by
  rw [← zsplit.summable_iff]
  refine Summable.sum _ ?_ ?_
  · refine (P.summable_abs_freq_inl h).congr fun j => ?_
    simp only [Function.comp_apply, P.freq_inl h j]
  · refine (P.summable_abs_freq_inr h).congr fun m => ?_
    simp only [Function.comp_apply, P.freq_inr h m]

/-! ## The two one-sided Erdős products -/

/-- The **future factor** `∏_{j≥1} φ_p(h(α-1)α^{-j})` of the Bernoulli(`p`) Weyl limit. -/
noncomputable def futProdC (p h : ℝ) : ℂ := ∏' j : ℕ, phi p (h * (P.α - 1) / P.α ^ (j + 1))

/-- The **past factor** `∏_{m≥0} φ_p(-h c_m)`. -/
noncomputable def pastProdC (p h : ℝ) : ℂ := ∏' m : ℕ, phi p (-(h * P.cCoef m))

/-- `G_p(h)`, the `h`-th Fourier coefficient of `F_*μ_p`. -/
noncomputable def weylC (p h : ℝ) : ℂ := P.futProdC p h * P.pastProdC p h

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem multipliable_futProdC {p : ℝ} (h0 : 0 ≤ p) (h : ℝ) :
    Multipliable fun j : ℕ => phi p (h * (P.α - 1) / P.α ^ (j + 1)) :=
  multipliable_phi h0 (P.summable_abs_freq_inl h)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem multipliable_pastProdC {p : ℝ} (h0 : 0 ≤ p) (h : ℝ) :
    Multipliable fun m : ℕ => phi p (-(h * P.cCoef m)) :=
  multipliable_phi h0 (P.summable_abs_freq_inr h)

/-- The two halves of the ladder reassemble into the two one-sided products. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tprod_phi_freq {p : ℝ} (h0 : 0 ≤ p) (h : ℝ) :
    ∏' k : ℤ, phi p (P.freq h k) = P.weylC p h := by
  have hinl : ∀ j : ℕ, phi p (P.freq h (zsplit (Sum.inl j)))
      = phi p (h * (P.α - 1) / P.α ^ (j + 1)) := fun j => by rw [P.freq_inl h j]
  have hinr : ∀ m : ℕ, phi p (P.freq h (zsplit (Sum.inr m))) = phi p (-(h * P.cCoef m)) :=
    fun m => by rw [P.freq_inr h m]
  calc ∏' k : ℤ, phi p (P.freq h k)
      = ∏' i : ℕ ⊕ ℕ, phi p (P.freq h (zsplit i)) :=
        (zsplit.tprod_eq fun k : ℤ => phi p (P.freq h k)).symm
    _ = (∏' j : ℕ, phi p (P.freq h (zsplit (Sum.inl j))))
        * ∏' m : ℕ, phi p (P.freq h (zsplit (Sum.inr m))) :=
        Multipliable.tprod_sum
          ((P.multipliable_futProdC h0 h).congr fun j => (hinl j).symm)
          ((P.multipliable_pastProdC h0 h).congr fun m => (hinr m).symm)
    _ = P.weylC p h := by rw [weylC, futProdC, pastProdC, tprod_congr hinl, tprod_congr hinr]

/-! ## The ladder is the coding -/

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem summable_future (h : ℝ) (ε : ℕ → Bool) :
    Summable fun j : ℕ => (h * (P.α - 1) / P.α ^ (j + 1)) * dR ε j := by
  have hα := P.one_lt
  have hrw : ∀ j : ℕ, (h * (P.α - 1) / P.α ^ (j + 1)) * dR ε j
      = (h * (P.α - 1)) * (dR ε j * (P.α⁻¹) ^ (j + 1)) := by
    intro j; rw [inv_pow]; ring
  simp only [hrw]
  exact (summable_dR_pow (inv_pos_of_one_lt hα).le (inv_lt_one_of_one_lt hα) ε).mul_left _

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem summable_past (h : ℝ) (δ : ℕ → Bool) :
    Summable fun m : ℕ => (-(h * P.cCoef m)) * dR δ m := by
  have hrw : ∀ m : ℕ, (-(h * P.cCoef m)) * dR δ m = (-h) * (P.cCoef m * dR δ m) := by
    intro m; ring
  simp only [hrw]
  exact (P.summable_cCoef δ).mul_left _

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tsum_future (h : ℝ) (ε : ℕ → Bool) :
    ∑' j : ℕ, (h * (P.α - 1) / P.α ^ (j + 1)) * dR ε j = h * piVal P.α ε := by
  have hrw : ∀ j : ℕ, (h * (P.α - 1) / P.α ^ (j + 1)) * dR ε j
      = (h * (P.α - 1)) * (dR ε j * (P.α⁻¹) ^ (j + 1)) := by
    intro j; rw [inv_pow]; ring
  simp only [hrw, tsum_mul_left, piVal]
  ring

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tsum_past (h : ℝ) (δ : ℕ → Bool) :
    ∑' m : ℕ, (-(h * P.cCoef m)) * dR δ m = -(h * P.wVal δ) := by
  have hrw : ∀ m : ℕ, (-(h * P.cCoef m)) * dR δ m = (-h) * (P.cCoef m * dR δ m) := by
    intro m; ring
  simp only [hrw, tsum_mul_left, wVal]
  ring

/-- **The ladder computes the coding**: `h · F(ω) = ∑_{k∈ℤ} y_k ω_k`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tsum_freq_mul_bitR (h : ℝ) (ω : Shift) :
    ∑' k : ℤ, P.freq h k * bitR (ω k) = h * P.fRaw ω := by
  have hinl : ∀ j : ℕ, P.freq h (zsplit (Sum.inl j)) * bitR (ω (zsplit (Sum.inl j)))
      = (h * (P.α - 1) / P.α ^ (j + 1)) * dR (futures ω) j := by
    intro j
    rw [P.freq_inl h j, show bitR (ω (zsplit (Sum.inl j))) = dR (futures ω) j from rfl]
  have hinr : ∀ m : ℕ, P.freq h (zsplit (Sum.inr m)) * bitR (ω (zsplit (Sum.inr m)))
      = (-(h * P.cCoef m)) * dR (pasts ω) m := by
    intro m
    rw [P.freq_inr h m, show bitR (ω (zsplit (Sum.inr m))) = dR (pasts ω) m from rfl]
  calc ∑' k : ℤ, P.freq h k * bitR (ω k)
      = ∑' i : ℕ ⊕ ℕ, P.freq h (zsplit i) * bitR (ω (zsplit i)) :=
        (zsplit.tsum_eq fun k : ℤ => P.freq h k * bitR (ω k)).symm
    _ = (∑' j : ℕ, P.freq h (zsplit (Sum.inl j)) * bitR (ω (zsplit (Sum.inl j))))
        + ∑' m : ℕ, P.freq h (zsplit (Sum.inr m)) * bitR (ω (zsplit (Sum.inr m))) :=
        Summable.tsum_sum ((P.summable_future h (futures ω)).congr fun j => (hinl j).symm)
          ((P.summable_past h (pasts ω)).congr fun m => (hinr m).symm)
    _ = h * piVal P.α (futures ω) + -(h * P.wVal (pasts ω)) := by
        rw [tsum_congr hinl, tsum_congr hinr, P.tsum_future h (futures ω),
          P.tsum_past h (pasts ω)]
    _ = h * P.fRaw ω := by rw [fRaw]; ring

/-! ## M5 Theorem 2 -/

/-- **M5 Theorem 2 (the product formula).**  Under the Bernoulli(`p`) measure on `{0,1}^ℤ`
the expectation of the character `e(h F(ω))` is the doubly infinite Erdős product
`G_p(h) = ∏_{j≥1} φ_p(h(α-1)α^{-j}) · ∏_{m≥0} φ_p(-h c_m)`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem integral_cexp1_fRaw {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (h : ℝ) :
    ∫ ω, cexp1 (h * P.fRaw ω) ∂(bernZ p) = P.weylC p h := by
  calc ∫ ω, cexp1 (h * P.fRaw ω) ∂(bernZ p)
      = ∫ ω, cexp1 (∑' k : ℤ, P.freq h k * bitR (ω k)) ∂(bernZ p) := by
        refine integral_congr_ae (ae_of_all _ fun ω => ?_)
        show cexp1 (h * P.fRaw ω) = cexp1 (∑' k : ℤ, P.freq h k * bitR (ω k))
        rw [P.tsum_freq_mul_bitR h ω]
    _ = ∏' k : ℤ, phi p (P.freq h k) := integral_bernZ_cexp1_tsum h0 h1 (P.summable_abs_freq h)
    _ = P.weylC p h := P.tprod_phi_freq h0 h

/-! ## `weylProd` is the modulus of a Fourier coefficient -/

end QuadSetup

/-- At `p = 1/2` the one-digit characteristic function has modulus `|cos π x|`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem norm_phi_half (x : ℝ) : ‖phi (1 / 2) x‖ = ncos x := by
  have hrepr : phi (1 / 2) x
      = ((1 / 2 + 1 / 2 * Real.cos (2 * Real.pi * x) : ℝ) : ℂ)
        + ((1 / 2 * Real.sin (2 * Real.pi * x) : ℝ) : ℂ) * Complex.I := by
    rw [phi, cexp1, Complex.exp_mul_I]
    push_cast [Complex.ofReal_cos, Complex.ofReal_sin]
    ring
  have hcos : Real.cos (2 * Real.pi * x) = 2 * Real.cos (Real.pi * x) ^ 2 - 1 := by
    rw [show 2 * Real.pi * x = 2 * (Real.pi * x) by ring, Real.cos_two_mul]
  have hsin : Real.sin (2 * Real.pi * x)
      = 2 * Real.sin (Real.pi * x) * Real.cos (Real.pi * x) := by
    rw [show 2 * Real.pi * x = 2 * (Real.pi * x) by ring, Real.sin_two_mul]
  have hkey : (1 / 2 + 1 / 2 * Real.cos (2 * Real.pi * x)) ^ 2
      + (1 / 2 * Real.sin (2 * Real.pi * x)) ^ 2 = Real.cos (Real.pi * x) ^ 2 := by
    rw [hcos, hsin]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * x)]
  rw [hrepr, Complex.norm_add_mul_I, hkey, Real.sqrt_sq_eq_abs, ncos]

namespace QuadSetup

variable (P : QuadSetup)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem norm_futProdC_half (h : ℝ) : ‖P.futProdC (1 / 2) h‖ = P.futProd h := by
  have hmap := (P.multipliable_futProdC (by norm_num : (0:ℝ) ≤ 1 / 2) h).hasProd.map
    (normHom : ℂ →*₀ ℝ) continuous_norm
  simp only [Function.comp_def, normHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
    norm_phi_half] at hmap
  exact hmap.unique (P.multipliable_futProd h).hasProd

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem norm_pastProdC_half (h : ℝ) : ‖P.pastProdC (1 / 2) h‖ = P.pastProd h := by
  have hmap := (P.multipliable_pastProdC (by norm_num : (0:ℝ) ≤ 1 / 2) h).hasProd.map
    (normHom : ℂ →*₀ ℝ) continuous_norm
  simp only [Function.comp_def, normHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
    norm_phi_half, ncos_neg] at hmap
  exact hmap.unique (P.multipliable_pastProd h).hasProd

/-- **`weylProd` is a Fourier modulus.**  The real product of `BB61/WeylProduct.lean` is the
modulus of the `h`-th Fourier coefficient of `F_*μ_{1/2}` computed by Theorem 2. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem norm_weylC_half (h : ℝ) : ‖P.weylC (1 / 2) h‖ = P.weylProd h := by
  rw [weylC, norm_mul, P.norm_futProdC_half h, P.norm_pastProdC_half h, weylProd]

/-! ## `G_p(h)` is a Fourier coefficient of `F_*μ_p` -/

/-- **M5 Theorem 2, in Fourier form.**  `G_p(h)` is the `h`-th Fourier coefficient of the
push-forward measure `F_*μ_p` on the circle. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem integral_fourier_map_fMap {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (n : ℤ) :
    ∫ z, fourier n z ∂(Measure.map P.fMap (bernZ p)) = P.weylC p (n : ℝ) := by
  rw [integral_map P.measurable_fMap.aemeasurable
      (map_continuous (fourier n)).aestronglyMeasurable,
    ← P.integral_cexp1_fRaw h0 h1 (n : ℝ)]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  show fourier n (P.fMap ω) = cexp1 ((n : ℝ) * P.fRaw ω)
  rw [fMap, fourier_coe_apply, cexp1]
  congr 1
  push_cast
  ring

/-! ## `G_{1/2}(1) ≠ 0`: the fair coin is not a counterexample measure -/

/-- Every factor of the mode-`1` ladder is non-zero at `p = 1/2`: the future factors by
`BB61/Bernoulli.lean`'s `cos_future_ne_zero` (this is where `α > 2` is spent), the past
factors by `cos_past_ne_zero` (the algebraic-integer argument). -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem phi_half_freq_one_ne_zero (h2 : 2 < P.α) (hirr : Irrational P.α) (k : ℤ) :
    phi (1 / 2) (P.freq 1 k) ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_phi_half, ncos, abs_ne_zero]
  unfold freq
  split_ifs with hk
  · rw [show (1 : ℝ) * (P.α - 1) / P.α ^ k.toNat = (P.α - 1) / P.α ^ k.toNat by ring]
    exact P.cos_future_ne_zero h2 (by omega)
  · rw [show Real.pi * -(1 * P.cCoef (-k).toNat)
        = -(Real.pi * (((1 : ℤ) : ℝ) * ((P.β - 1) * P.β ^ (-k).toNat))) by
      rw [cCoef]; push_cast; ring, Real.cos_neg]
    exact P.cos_past_ne_zero h2 hirr one_ne_zero _

/-- **`G_{1/2}(1) ≠ 0`** — M5 Theorem 3(iv) at `p = 1/2`, with the infinite product. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem weylC_half_one_ne_zero (h2 : 2 < P.α) (hirr : Irrational P.α) :
    P.weylC (1 / 2) 1 ≠ 0 := by
  rw [← P.tprod_phi_freq (by norm_num : (0:ℝ) ≤ 1 / 2) 1]
  exact tprod_phi_ne_zero (by norm_num) (P.summable_abs_freq 1)
    (P.phi_half_freq_one_ne_zero h2 hirr)

/-- **The fair coin is not a counterexample measure.**  `F_*μ_{1/2} ≠ Leb` for every
quadratic Pisot `α > 2`: its first Fourier coefficient is `G_{1/2}(1) ≠ 0`.  This is the
measure-level content of M5 Corollary 5. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem map_fMap_bernZ_half_ne_volume (h2 : 2 < P.α) (hirr : Irrational P.α) :
    Measure.map P.fMap (bernZ (1 / 2)) ≠ (volume : Measure (AddCircle (1 : ℝ))) := by
  intro hcon
  have h1 := P.integral_fourier_map_fMap (by norm_num : (0:ℝ) ≤ 1 / 2)
    (by norm_num : (1:ℝ) / 2 ≤ 1) 1
  rw [hcon, ← haarAddCircle_eq_volume, integral_fourier_eq_zero one_ne_zero] at h1
  exact P.weylC_half_one_ne_zero h2 hirr (by simpa using h1.symm)

/-- The instance of `BB61/Bernoulli.lean`: at `α = 2 + √3`, `F_*μ_{1/2} ≠ Leb`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem map_fMap_bernZ_half_ne_volume_twoAddSqrt3 :
    Measure.map twoAddSqrt3.fMap (bernZ (1 / 2)) ≠ (volume : Measure (AddCircle (1 : ℝ))) :=
  twoAddSqrt3.map_fMap_bernZ_half_ne_volume two_lt_twoAddSqrt3 irrational_twoAddSqrt3

end QuadSetup

end BB61
