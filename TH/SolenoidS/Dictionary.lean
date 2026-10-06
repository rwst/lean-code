/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BertinPisot.UniformDistribution
import ForMathlib.NumberTheory.Solenoid.Characters
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The Weyl dictionary on `Σ_S`, for every `S`-unit

Deliverable D5 of plan-udmf-O5 (milestone M5): the dictionary of Proposition 1(c) of
plan-udmf-F2ii §1.3, for an arbitrary finite set of primes `S` and an arbitrary unit `u` of
`ℤ[1/N_S]` (`hu : IsSUnit S u`).  For a real `ξ`, the `σ_u`-orbit of the winding point `wind ξ`
is the sequence `ξ uⁿ` seen inside `Σ_S` (`Solenoid.smulAut_iter_wind`), and

> **The following are equivalent** (`weyl_dictionary`):
> 1. the empirical measures of `(σ_uⁿ wind ξ)_{n<N}` converge weak-∗ to Haar measure on `Σ_S`
>    (`Equidistributed hu ξ`);
> 2. `(1/N) Σ_{n<N} e(r ξ uⁿ) → 0` for every `r ∈ ℤ[1/N_S] \ {0}` (`WeylFamily S u ξ`);
> 3. `(r ξ uⁿ)_n` is u.d. mod 1 for every `r ∈ ℤ[1/N_S] \ {0}` (`UDFamily S u ξ`).

`(1) ⇒ (2)` is orthogonality (`Solenoid.integral_e_eq_zero`); `(2) ⇒ (1)` is Stone–Weierstrass
(`Solenoid.dense_span_char`) plus the contraction bounds `norm_birkhoff_le`, `norm_integral_le`;
`(2) ⇔ (3)` is Weyl's criterion (`Bertin.uniformlyDistributedModOne_iff_weylCriterion`) together
with `(ℤ \ {0}) · (ℤ[1/N_S] \ {0}) ⊆ ℤ[1/N_S] \ {0}` (`Subring.mul_mem` + `intCast_mem`).

The `S = {2, 3}`, `u = 3/2` instance is `TH.S6.weyl_dictionary`; the proofs transplant verbatim.

**No `ξ` is shown to equidistribute.**  The dictionary is an equivalence between three
formulations of the same open statement; ground rules GR1 (nothing uniform in `ξ`) and GR5 (an
a.e. criterion is not a criterion at `ξ`) are untouched.  For an integer base the three statements
collapse further to u.d. of `(ξ bⁿ)` alone (`TH.SolS.equidistributed_iff_ud`, `IntegerBase.lean`).

## Main statements

* `weyl_dictionary` — **(1) ⇔ (2) ⇔ (3)**, for every `S`-unit `u`.
* `equidistributed_iff_weylFamily`, `weylFamily_iff_udFamily` — the two halves.
* `ud_of_equidistributed` — the `r = 1` slice: u.d. mod 1 of `(ξ uⁿ)`.
* `not_equidistributed_zero` — the conditions are not vacuous.

## Status

Everything in this file is standard; the contribution is the formalisation.

## References

* plan-udmf-O5 §1.4 (D5), plan-udmf-F2ii §1.3 (Proposition 1), plan-A1+ §2.2.
* [Wey16] H. Weyl, *Über die Gleichverteilung von Zahlen mod. Eins*, Math. Ann. 77 (1916).
* [EW11] M. Einsiedler, T. Ward, *Ergodic Theory with a view towards Number Theory*, Springer
  (2011), Ch. 4 and 8.
-/

namespace TH.SolS

open Metric Set MeasureTheory Filter Complex Solenoid Rat
open scoped Topology ENNReal

variable {S : Finset Nat.Primes} {u : ℚ}

/-! ### Birkhoff averages along the winding orbit -/

/-- The Birkhoff average of `f` over the first `N` points of the `σ_u`-orbit of `wind ξ`; by
`smulAut_iter_wind` these points are the images of `ξ uⁿ`. -/
noncomputable def birkhoff (hu : IsSUnit S u) (f : C(Solenoid S, ℂ)) (ξ : ℝ) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f ((smulAut hu)^[n] (wind ξ))

@[category API, AMS 11 37, ref "udmfO5", group "th_solenoid_s_dictionary"]
theorem birkhoff_zero (hu : IsSUnit S u) (ξ : ℝ) (N : ℕ) : birkhoff hu 0 ξ N = 0 := by
  simp [birkhoff]

@[category API, AMS 11 37, ref "udmfO5", group "th_solenoid_s_dictionary"]
theorem birkhoff_add (hu : IsSUnit S u) (f g : C(Solenoid S, ℂ)) (ξ : ℝ) (N : ℕ) :
    birkhoff hu (f + g) ξ N = birkhoff hu f ξ N + birkhoff hu g ξ N := by
  simp only [birkhoff, ContinuousMap.add_apply, Finset.sum_add_distrib, mul_add]

@[category API, AMS 11 37, ref "udmfO5", group "th_solenoid_s_dictionary"]
theorem birkhoff_sub (hu : IsSUnit S u) (f g : C(Solenoid S, ℂ)) (ξ : ℝ) (N : ℕ) :
    birkhoff hu (f - g) ξ N = birkhoff hu f ξ N - birkhoff hu g ξ N := by
  simp only [birkhoff, ContinuousMap.sub_apply, Finset.sum_sub_distrib, mul_sub]

@[category API, AMS 11 37, ref "udmfO5", group "th_solenoid_s_dictionary"]
theorem birkhoff_smul (hu : IsSUnit S u) (c : ℂ) (f : C(Solenoid S, ℂ)) (ξ : ℝ) (N : ℕ) :
    birkhoff hu (c • f) ξ N = c * birkhoff hu f ξ N := by
  simp only [birkhoff, ContinuousMap.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

@[category API, AMS 11 37, ref "udmfO5", group "th_solenoid_s_dictionary"]
theorem birkhoff_one (hu : IsSUnit S u) (ξ : ℝ) {N : ℕ} (hN : 0 < N) :
    birkhoff hu 1 ξ N = 1 := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  simp only [birkhoff, ContinuousMap.one_apply, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ hN0

/-- The Birkhoff averages are contractions: `‖birkhoff hu f ξ N‖ ≤ ‖f‖`. -/
@[category API, AMS 11 37, ref "udmfO5", group "th_solenoid_s_dictionary"]
theorem norm_birkhoff_le (hu : IsSUnit S u) (f : C(Solenoid S, ℂ)) (ξ : ℝ) (N : ℕ) :
    ‖birkhoff hu f ξ N‖ ≤ ‖f‖ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [birkhoff]
  · have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hs : ‖∑ n ∈ Finset.range N, f ((smulAut hu)^[n] (wind ξ))‖ ≤ (N : ℝ) * ‖f‖ := by
      calc ‖∑ n ∈ Finset.range N, f ((smulAut hu)^[n] (wind ξ))‖
          ≤ ∑ n ∈ Finset.range N, ‖f ((smulAut hu)^[n] (wind ξ))‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ Finset.range N, ‖f‖ :=
            Finset.sum_le_sum fun n _ => ContinuousMap.norm_coe_le_norm f _
        _ = (N : ℝ) * ‖f‖ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [birkhoff, norm_mul, norm_inv]
    have hcast : ‖(N : ℂ)‖ = (N : ℝ) := by simp
    rw [hcast, inv_mul_le_iff₀ hNpos]
    exact hs

/-- The Haar integral is a contraction too. -/
@[category API, AMS 11 37, ref "udmfO5", group "th_solenoid_s_dictionary"]
theorem norm_integral_le (f : C(Solenoid S, ℂ)) : ‖∫ x, f x ∂haar S‖ ≤ ‖f‖ := by
  have h := MeasureTheory.norm_integral_le_of_norm_le_const (μ := haar S) (C := ‖f‖)
    (Filter.Eventually.of_forall fun x => ContinuousMap.norm_coe_le_norm f x)
  simpa using h

/-! ### The three statements -/

/-- **(1)** Weak-∗ convergence of the empirical measures of the `σ_u`-orbit of `wind ξ` to Haar
measure on `Σ_S`. -/
def Equidistributed (hu : IsSUnit S u) (ξ : ℝ) : Prop :=
  ∀ f : C(Solenoid S, ℂ), Tendsto (fun N => birkhoff hu f ξ N) atTop (𝓝 (∫ x, f x ∂haar S))

variable (S) in
/-- **(2)** Every Weyl sum of the master family `{r ξ uⁿ : r ∈ ℤ[1/N_S]}` vanishes. -/
def WeylFamily (u : ℚ) (ξ : ℝ) : Prop :=
  ∀ r : sIntegers S, (r : ℚ) ≠ 0 →
    Tendsto (fun N => (∑ n ∈ Finset.range N,
        Complex.exp (2 * Real.pi * Complex.I * (((r : ℚ) : ℝ) * (ξ * (u : ℝ) ^ n)))) / N)
      atTop (𝓝 0)

variable (S) in
/-- **(3)** The whole `ℤ[1/N_S]`-scaled family is uniformly distributed modulo one. -/
def UDFamily (u : ℚ) (ξ : ℝ) : Prop :=
  ∀ r : sIntegers S, (r : ℚ) ≠ 0 →
    Bertin.UniformlyDistributedModOne (fun n => ((r : ℚ) : ℝ) * (ξ * (u : ℝ) ^ n))

/-! ### The character values along the orbit are the Weyl summands -/

/-- On the winding line, `e_r` is the exponential `e(r η)`. -/
@[category API, AMS 11 37, ref "udmfO5", group "th_solenoid_s_dictionary"]
theorem e_wind (r : sIntegers S) (η : ℝ) :
    e r (wind η) = Complex.exp (2 * Real.pi * Complex.I * (((r : ℚ) : ℝ) * η)) := by
  show fourier (T := (1 : ℝ)) 1 (χ r (wind η)) = _
  rw [χ_wind, fourier_coe_apply]
  push_cast
  ring_nf

/-- **The Birkhoff average of a character is the Weyl sum** of `(r ξ uⁿ)`. -/
@[category research solved, AMS 11 37, ref "udmfO5", group "th_solenoid_s_dictionary"]
theorem birkhoff_e (hu : IsSUnit S u) (r : sIntegers S) (ξ : ℝ) (N : ℕ) :
    birkhoff hu (e r) ξ N = (∑ n ∈ Finset.range N,
      Complex.exp (2 * Real.pi * Complex.I * (((r : ℚ) : ℝ) * (ξ * (u : ℝ) ^ n)))) / N := by
  rw [birkhoff, div_eq_inv_mul]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [smulAut_iter_wind, e_wind]
  push_cast
  ring_nf

/-! ### (1) ⇔ (2) -/

/-- Convergence of Birkhoff averages propagates from the span of the characters to all of
`C(Σ_S, ℂ)`: an `ε/3` argument using `dense_span_char` and the two contraction bounds. -/
@[category API, AMS 11 37, ref "udmfO5", group "th_solenoid_s_dictionary"]
theorem tendsto_birkhoff_of_span (hu : IsSUnit S u) {ξ : ℝ}
    (h : ∀ f ∈ (Submodule.span ℂ (Set.range (e (S := S))) : Set C(Solenoid S, ℂ)),
      Tendsto (fun N => birkhoff hu f ξ N) atTop (𝓝 (∫ x, f x ∂haar S)))
    (f : C(Solenoid S, ℂ)) :
    Tendsto (fun N => birkhoff hu f ξ N) atTop (𝓝 (∫ x, f x ∂haar S)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hgmem, hfg⟩ := Metric.mem_closure_iff.mp (dense_span_char f) (ε / 3) (by linarith)
  have hg := h g hgmem
  rw [Metric.tendsto_atTop] at hg
  obtain ⟨N₀, hN₀⟩ := hg (ε / 3) (by linarith)
  refine ⟨N₀, fun N hN => ?_⟩
  have h1 : dist (birkhoff hu f ξ N) (birkhoff hu g ξ N) < ε / 3 := by
    rw [dist_eq_norm, ← birkhoff_sub]
    exact lt_of_le_of_lt (norm_birkhoff_le _ _ _ _) (by rwa [← dist_eq_norm])
  have h2 : dist (∫ x, g x ∂haar S) (∫ x, f x ∂haar S) < ε / 3 := by
    rw [dist_eq_norm, ← MeasureTheory.integral_sub (integrable_char g) (integrable_char f)]
    have hgf : ∫ x, (g x - f x) ∂haar S = ∫ x, (g - f) x ∂haar S := by simp
    rw [hgf]
    refine lt_of_le_of_lt (norm_integral_le _) ?_
    rw [← dist_eq_norm, dist_comm]
    exact hfg
  calc dist (birkhoff hu f ξ N) (∫ x, f x ∂haar S)
      ≤ dist (birkhoff hu f ξ N) (birkhoff hu g ξ N)
        + dist (birkhoff hu g ξ N) (∫ x, g x ∂haar S)
        + dist (∫ x, g x ∂haar S) (∫ x, f x ∂haar S) := dist_triangle4 _ _ _ _
    _ < ε := by linarith [hN₀ N hN]

/-- **(1) ⇔ (2)**: weak-∗ convergence to Haar is exactly the vanishing of all non-trivial Weyl
sums of the master family. -/
@[category research solved, AMS 11 37, ref "udmfO5" "EW11", group "th_solenoid_s_dictionary"]
theorem equidistributed_iff_weylFamily (hu : IsSUnit S u) (ξ : ℝ) :
    Equidistributed hu ξ ↔ WeylFamily S u ξ := by
  constructor
  · intro h r hr
    have := h (e r)
    rwa [integral_e_eq_zero hr, funext (birkhoff_e hu r ξ)] at this
  · intro h
    refine tendsto_birkhoff_of_span hu ?_
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨r, rfl⟩ := hf
      by_cases hr : (r : ℚ) = 0
      · have hr0 : r = 0 := Subtype.ext hr
        subst hr0
        rw [e_zero]
        have hev : (fun _ : ℕ => (1 : ℂ)) =ᶠ[atTop]
            fun N => birkhoff hu (1 : C(Solenoid S, ℂ)) ξ N := by
          filter_upwards [eventually_gt_atTop 0] with N hN using (birkhoff_one hu ξ hN).symm
        rw [show (∫ x, (1 : C(Solenoid S, ℂ)) x ∂haar S) = 1 by simp]
        exact Tendsto.congr' hev tendsto_const_nhds
      · rw [integral_e_eq_zero hr, funext (birkhoff_e hu r ξ)]
        exact h r hr
    | zero =>
      simp [birkhoff_zero]
    | add f g _ _ hf hg =>
      simp only [birkhoff_add]
      rw [show (∫ x, (f + g) x ∂haar S) = (∫ x, f x ∂haar S) + ∫ x, g x ∂haar S by
        simp only [ContinuousMap.add_apply]
        exact MeasureTheory.integral_add (integrable_char f) (integrable_char g)]
      exact hf.add hg
    | smul c f _ hf =>
      simp only [birkhoff_smul]
      rw [show (∫ x, (c • f) x ∂haar S) = c * ∫ x, f x ∂haar S by
        simp only [ContinuousMap.smul_apply, smul_eq_mul]
        exact MeasureTheory.integral_const_mul c _]
      exact hf.const_mul c

/-! ### (2) ⇔ (3) -/

/-- Weyl's criterion, in the shape in which the family statement uses it. -/
@[category API, AMS 11, ref "udmfO5", group "th_solenoid_s_dictionary"]
theorem weylCriterion_iff_scaled (t : ℕ → ℝ) :
    WeylCriterion t ↔ ∀ h : ℤ, h ≠ 0 →
      Tendsto (fun N => (∑ n ∈ Finset.range N,
        Complex.exp (2 * Real.pi * Complex.I * ((h : ℝ) * t n))) / N) atTop (𝓝 0) := by
  have hrw : ∀ (h : ℤ) (N : ℕ), (∑ n ∈ Finset.range N,
      Complex.exp (2 * Real.pi * Complex.I * h * t n)) / N = (∑ n ∈ Finset.range N,
      Complex.exp (2 * Real.pi * Complex.I * ((h : ℝ) * t n))) / N := fun h N => by
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    push_cast
    ring
  simp only [WeylCriterion, hrw]

/-- **(2) ⇔ (3)**: the Weyl sums of the whole `ℤ[1/N_S]`-family vanish iff every member of the
family is u.d. mod 1, because `ℤ \ {0}` maps `ℤ[1/N_S] \ {0}` into itself. -/
@[category research solved, AMS 11, ref "udmfO5" "Wey16", group "th_solenoid_s_dictionary"]
theorem weylFamily_iff_udFamily (ξ : ℝ) : WeylFamily S u ξ ↔ UDFamily S u ξ := by
  constructor
  · intro hw r hr
    rw [Bertin.uniformlyDistributedModOne_iff_weylCriterion, weylCriterion_iff_scaled]
    intro h hh
    have hrmem : ((h : ℚ) * (r : ℚ)) ∈ sIntegers S := Subring.mul_mem _ (intCast_mem _ h) r.2
    have hne : ((⟨(h : ℚ) * (r : ℚ), hrmem⟩ : sIntegers S) : ℚ) ≠ 0 := by
      simp only [ne_eq, mul_eq_zero]
      push Not
      exact ⟨by exact_mod_cast hh, hr⟩
    refine Tendsto.congr (fun N => ?_) (hw ⟨(h : ℚ) * (r : ℚ), hrmem⟩ hne)
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    push_cast
    ring
  · intro hu r hr
    have hw := (Bertin.uniformlyDistributedModOne_iff_weylCriterion _).mp (hu r hr)
    rw [weylCriterion_iff_scaled] at hw
    refine Tendsto.congr (fun N => ?_) (hw 1 one_ne_zero)
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    push_cast
    ring

/-! ### The dictionary -/

/-- **The Weyl dictionary on `Σ_S`** (plan-udmf-F2ii, Proposition 1(c)).  For every `S`-unit `u`
and every real `ξ` the following are equivalent:

1. the empirical measures of the `σ_u`-orbit of `wind ξ` converge weak-∗ to Haar measure;
2. every Weyl sum `(1/N) Σ_{n<N} e(r ξ uⁿ)` with `r ∈ ℤ[1/N_S] \ {0}` tends to `0`;
3. every sequence `(r ξ uⁿ)_n` with `r ∈ ℤ[1/N_S] \ {0}` is u.d. mod 1.

This is a theorem about the object, not about any particular `ξ`. -/
@[category research solved, AMS 11 37, ref "udmfO5" "EW11", group "th_solenoid_s_dictionary"]
theorem weyl_dictionary (hu : IsSUnit S u) (ξ : ℝ) :
    [Equidistributed hu ξ, WeylFamily S u ξ, UDFamily S u ξ].TFAE := by
  tfae_have 1 ↔ 2 := equidistributed_iff_weylFamily hu ξ
  tfae_have 2 ↔ 3 := weylFamily_iff_udFamily ξ
  tfae_finish

/-- **Equidistribution in `Σ_S` implies u.d. mod 1 of `(ξ uⁿ)`**: the `r = 1` slice of the
dictionary, which delivers the whole master family `{ξ r uⁿ}` at the same time. -/
@[category research solved, AMS 11 37, ref "udmfO5", group "th_solenoid_s_dictionary"]
theorem ud_of_equidistributed {hu : IsSUnit S u} {ξ : ℝ} (h : Equidistributed hu ξ) :
    Bertin.UniformlyDistributedModOne (fun n => ξ * (u : ℝ) ^ n) := by
  have hud := (weylFamily_iff_udFamily ξ).mp ((equidistributed_iff_weylFamily hu ξ).mp h)
  simpa using hud 1 (by norm_num)

/-! ### Sanity: the dictionary is not vacuous -/

/-- **Non-vacuity**: `ξ = 0` fails (2) — every Weyl sum of the `r = 1` member is identically
`1`. -/
@[category test, AMS 11, ref "udmfO5", group "th_solenoid_s_dictionary"]
theorem not_weylFamily_zero : ¬ WeylFamily S u 0 := by
  intro h
  have hev : (fun N : ℕ => (∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I *
      ((((1 : sIntegers S) : ℚ) : ℝ) * (0 * (u : ℝ) ^ n)))) / N) =ᶠ[atTop] fun _ => (1 : ℂ) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    simp only [zero_mul, mul_zero, Complex.exp_zero, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one]
    exact div_self (Nat.cast_ne_zero.mpr hN.ne')
  exact zero_ne_one (tendsto_nhds_unique ((h 1 one_ne_zero).congr' hev) tendsto_const_nhds)

/-- `ξ = 0` is not equidistributed: its orbit is the fixed point `0`. -/
@[category test, AMS 11 37, ref "udmfO5", group "th_solenoid_s_dictionary"]
theorem not_equidistributed_zero (hu : IsSUnit S u) : ¬ Equidistributed hu 0 := fun h =>
  not_weylFamily_zero ((equidistributed_iff_weylFamily hu 0).mp h)

end TH.SolS
