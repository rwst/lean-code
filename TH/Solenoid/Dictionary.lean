/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BertinPisot.UniformDistribution
import TH.Solenoid.Characters
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The Weyl dictionary on `Σ₆`, and the finite-level bridge to floor residues

Work package W3 of plan-A1+ (§2.2, §4 L3), second half — the capstone of the unconditional part of
the architecture.  For a real `ξ`, write `μ_N` for the empirical measure of the first `N` points of
the `T`-orbit of the winding point `x_ξ = wind ξ`; by `T32_iter_wind` that orbit is exactly the
sequence `(3/2)ⁿ ξ` seen inside `Σ₆`.  The dictionary is:

> **The following are equivalent** (`weyl_dictionary`):
> 1. `μ_N → Haar(Σ₆)` weak-∗ (`Equidistributed`);
> 2. `(1/N) Σ_{n<N} e(r ξ (3/2)ⁿ) → 0` for every `r ∈ ℤ[1/6] \ {0}` (`WeylFamily`);
> 3. `(r ξ (3/2)ⁿ)_n` is u.d. mod 1 for every `r ∈ ℤ[1/6] \ {0}` (`UDFamily`).

`(1) ⇒ (2)` is orthogonality (`integral_e_eq_zero`) applied to `χ_r`; `(2) ⇒ (1)` is
Stone–Weierstrass (`dense_span_char`) plus the uniform bound `‖·‖ ≤ ‖f‖` shared by the Birkhoff
averages and by the Haar integral; `(2) ⇔ (3)` is Weyl's criterion
(`Bertin.uniformlyDistributedModOne_iff_weylCriterion`) together with the observation that
`ℤ \ {0}` scales `ℤ[1/6] \ {0}` into itself.

In particular `Equidistributed ξ` implies the target statement **T** of the plan, u.d. mod 1 of
`(ξ (3/2)ⁿ)` (`ud_of_equidistributed`, the `r = 1` slice) — and it implies it *simultaneously for
the whole master family* `{ξ m/6ᵏ}`, in exact agreement with report2-A12 §1.5.  Equidistribution
in `Σ₆` is genuinely stronger than **T**: it is `T` for a countable family at once.

## The finite-level bridge

Shifting `wind η` into the fundamental domain subtracts the integer part
(`wind_repr`): the representative is `(⟨η⟩, -⌊η⌋, -⌊η⌋) ∈ [0,1) × ℤ₂ × ℤ₃`.  Hence membership of
`wind η` in a level-`(k, j)` cell is *exactly* the joint condition

`⟨η⟩ ∈ (a, b)`,  `⌊η⌋ ≡ n (mod 2ᵏ)`,  `⌊η⌋ ≡ m (mod 3ʲ)`

(`level_bridge`), and by W2 that cell has Haar mass `(b - a) 2⁻ᵏ 3⁻ʲ`.  So equidistribution in
`Σ₆` says precisely that fractional part and floor residues uniformize *jointly*.  These are the
objects of `Z32/Dictionary.lean`, whose `Z32.floor_emod_iff_fract_mem`
(`⌊t⌋ ≡ r (mod m) ↔ ⟨t/m⟩ ∈ [r/m, (r+1)/m)`) is the same dictionary read downstairs, on the real
line, after rescaling.  The two files are kept independent — nothing here imports `Z32` — because
the content of the bridge is the *statement*, and stating it in `Σ₆` coordinates is what makes the
`Z32` machinery plug in without translation.

## Main statements

* `weyl_dictionary` — **(1) ⇔ (2) ⇔ (3)**, the capstone.
* `equidistributed_iff_weylFamily`, `weylFamily_iff_udFamily` — the two halves.
* `ud_of_equidistributed` — equidistribution in `Σ₆` implies u.d. mod 1 of `(ξ (3/2)ⁿ)`.
* `wind_repr`, `level_bridge` — the residue packaging and the finite-level cells.

## References

Plan A1+ §2.2 (the box "The Weyl dictionary (unconditional; W3's capstone)") and §4 (L3).
Weyl's criterion is [Wey16]; the compact-group form used here is the standard one, see
[EW11, Ch. 4].
-/

namespace TH.S6

open Metric Set MeasureTheory Filter Complex
open scoped Topology ENNReal

/-! ### Birkhoff averages along the winding orbit -/

/-- The Birkhoff average of `f` over the first `N` points of the `T`-orbit of `wind ξ`.  By
`T32_iter_wind` these points are the images of `ξ (3/2)ⁿ`, so this is the integral of `f` against
the empirical measure `μ_N` of the plan (whose measure-theoretic packaging is W4). -/
noncomputable def birkhoff (f : C(S6, ℂ)) (ξ : ℝ) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f (T32^[n] (wind ξ))

@[category API, AMS 11, ref "A1plus", group "th_solenoid_dictionary"]
theorem birkhoff_zero (ξ : ℝ) (N : ℕ) : birkhoff 0 ξ N = 0 := by
  simp [birkhoff]

@[category API, AMS 11, ref "A1plus", group "th_solenoid_dictionary"]
theorem birkhoff_add (f g : C(S6, ℂ)) (ξ : ℝ) (N : ℕ) :
    birkhoff (f + g) ξ N = birkhoff f ξ N + birkhoff g ξ N := by
  simp only [birkhoff, ContinuousMap.add_apply, Finset.sum_add_distrib, mul_add]

@[category API, AMS 11, ref "A1plus", group "th_solenoid_dictionary"]
theorem birkhoff_sub (f g : C(S6, ℂ)) (ξ : ℝ) (N : ℕ) :
    birkhoff (f - g) ξ N = birkhoff f ξ N - birkhoff g ξ N := by
  simp only [birkhoff, ContinuousMap.sub_apply, Finset.sum_sub_distrib, mul_sub]

@[category API, AMS 11, ref "A1plus", group "th_solenoid_dictionary"]
theorem birkhoff_smul (c : ℂ) (f : C(S6, ℂ)) (ξ : ℝ) (N : ℕ) :
    birkhoff (c • f) ξ N = c * birkhoff f ξ N := by
  simp only [birkhoff, ContinuousMap.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

@[category API, AMS 11, ref "A1plus", group "th_solenoid_dictionary"]
theorem birkhoff_one (ξ : ℝ) {N : ℕ} (hN : 0 < N) : birkhoff 1 ξ N = 1 := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  simp only [birkhoff, ContinuousMap.one_apply, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ hN0

/-- The Birkhoff averages are contractions: `‖birkhoff f ξ N‖ ≤ ‖f‖`.  This uniform bound is what
lets a statement proved on a dense subspace propagate to all of `C(Σ₆, ℂ)`. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_dictionary"]
theorem norm_birkhoff_le (f : C(S6, ℂ)) (ξ : ℝ) (N : ℕ) : ‖birkhoff f ξ N‖ ≤ ‖f‖ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [birkhoff]
  · have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hs : ‖∑ n ∈ Finset.range N, f (T32^[n] (wind ξ))‖ ≤ (N : ℝ) * ‖f‖ := by
      calc ‖∑ n ∈ Finset.range N, f (T32^[n] (wind ξ))‖
          ≤ ∑ n ∈ Finset.range N, ‖f (T32^[n] (wind ξ))‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ Finset.range N, ‖f‖ :=
            Finset.sum_le_sum fun n _ => ContinuousMap.norm_coe_le_norm f _
        _ = (N : ℝ) * ‖f‖ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [birkhoff, norm_mul, norm_inv]
    have hcast : ‖(N : ℂ)‖ = (N : ℝ) := by simp
    rw [hcast, inv_mul_le_iff₀ hNpos]
    exact hs

/-- The Haar integral is a contraction too. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_dictionary"]
theorem norm_integral_le (f : C(S6, ℂ)) : ‖∫ x, f x ∂haar‖ ≤ ‖f‖ := by
  have h := MeasureTheory.norm_integral_le_of_norm_le_const (μ := haar) (C := ‖f‖)
    (Filter.Eventually.of_forall fun x => ContinuousMap.norm_coe_le_norm f x)
  simpa using h

/-! ### The three statements -/

/-- **(1)** Weak-∗ convergence of the empirical measures of the orbit of `wind ξ` to Haar
measure. -/
def Equidistributed (ξ : ℝ) : Prop :=
  ∀ f : C(S6, ℂ), Tendsto (fun N => birkhoff f ξ N) atTop (𝓝 (∫ x, f x ∂haar))

/-- **(2)** Every Weyl sum of the master family `{r ξ (3/2)ⁿ : r ∈ ℤ[1/6]}` vanishes. -/
def WeylFamily (ξ : ℝ) : Prop :=
  ∀ r : Z16, (r : ℚ) ≠ 0 →
    Tendsto (fun N => (∑ n ∈ Finset.range N,
        Complex.exp (2 * Real.pi * Complex.I * (((r : ℚ) : ℝ) * (ξ * (3 / 2) ^ n)))) / N)
      atTop (𝓝 0)

/-- **(3)** The whole `ℤ[1/6]`-scaled family is uniformly distributed modulo one. -/
def UDFamily (ξ : ℝ) : Prop :=
  ∀ r : Z16, (r : ℚ) ≠ 0 →
    Bertin.UniformlyDistributedModOne (fun n => ((r : ℚ) : ℝ) * (ξ * (3 / 2) ^ n))

/-! ### The character values along the orbit are the Weyl summands -/

/-- On the winding line, `e_r` is the exponential `e(r ξ)`. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_dictionary"]
theorem e_wind (r : Z16) (η : ℝ) :
    e r (wind η) = Complex.exp (2 * Real.pi * Complex.I * (((r : ℚ) : ℝ) * η)) := by
  show fourier (T := (1 : ℝ)) 1 (χ r (wind η)) = _
  rw [χ_wind, fourier_coe_apply]
  push_cast
  ring_nf

/-- **The Birkhoff average of a character is the Weyl sum.**  This is the identity that makes the
solenoid picture and the classical one the same computation. -/
@[category research solved, AMS 11, ref "A1plus", group "th_solenoid_dictionary"]
theorem birkhoff_e (r : Z16) (ξ : ℝ) (N : ℕ) :
    birkhoff (e r) ξ N = (∑ n ∈ Finset.range N,
      Complex.exp (2 * Real.pi * Complex.I * (((r : ℚ) : ℝ) * (ξ * (3 / 2) ^ n)))) / N := by
  rw [birkhoff, div_eq_inv_mul]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [T32_iter_wind, e_wind]
  congr 1
  push_cast
  ring

/-! ### (1) ⇔ (2) -/

/-- Convergence of Birkhoff averages propagates from the span of the characters to all of
`C(Σ₆, ℂ)`: an `ε/3` argument using `dense_span_char` and the two contraction bounds. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_dictionary"]
theorem tendsto_birkhoff_of_span {ξ : ℝ}
    (h : ∀ f ∈ (Submodule.span ℂ (Set.range e) : Set C(S6, ℂ)),
      Tendsto (fun N => birkhoff f ξ N) atTop (𝓝 (∫ x, f x ∂haar)))
    (f : C(S6, ℂ)) : Tendsto (fun N => birkhoff f ξ N) atTop (𝓝 (∫ x, f x ∂haar)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hgmem, hfg⟩ := Metric.mem_closure_iff.mp (dense_span_char f) (ε / 3) (by linarith)
  have hg := h g hgmem
  rw [Metric.tendsto_atTop] at hg
  obtain ⟨N₀, hN₀⟩ := hg (ε / 3) (by linarith)
  refine ⟨N₀, fun N hN => ?_⟩
  have h1 : dist (birkhoff f ξ N) (birkhoff g ξ N) < ε / 3 := by
    rw [dist_eq_norm, ← birkhoff_sub]
    exact lt_of_le_of_lt (norm_birkhoff_le _ _ _) (by rwa [← dist_eq_norm])
  have h2 : dist (∫ x, g x ∂haar) (∫ x, f x ∂haar) < ε / 3 := by
    rw [dist_eq_norm, ← MeasureTheory.integral_sub (integrable_char g) (integrable_char f)]
    have hgf : ∫ x, (g x - f x) ∂haar = ∫ x, (g - f) x ∂haar := by simp
    rw [hgf]
    refine lt_of_le_of_lt (norm_integral_le _) ?_
    rw [← dist_eq_norm, dist_comm]
    exact hfg
  calc dist (birkhoff f ξ N) (∫ x, f x ∂haar)
      ≤ dist (birkhoff f ξ N) (birkhoff g ξ N) + dist (birkhoff g ξ N) (∫ x, g x ∂haar)
        + dist (∫ x, g x ∂haar) (∫ x, f x ∂haar) := dist_triangle4 _ _ _ _
    _ < ε := by linarith [hN₀ N hN]

/-- **(1) ⇔ (2)**: weak-∗ convergence to Haar is exactly the vanishing of all non-trivial Weyl
sums of the master family. -/
@[category research solved, AMS 11, ref "A1plus", group "th_solenoid_dictionary"]
theorem equidistributed_iff_weylFamily (ξ : ℝ) : Equidistributed ξ ↔ WeylFamily ξ := by
  constructor
  · intro h r hr
    have := h (e r)
    rwa [integral_e_eq_zero hr, funext (birkhoff_e r ξ)] at this
  · intro h
    refine tendsto_birkhoff_of_span ?_
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨r, rfl⟩ := hf
      by_cases hr : (r : ℚ) = 0
      · have hr0 : r = 0 := Subtype.ext hr
        subst hr0
        rw [e_zero]
        have hev : (fun _ : ℕ => (1 : ℂ)) =ᶠ[atTop] fun N => birkhoff (1 : C(S6, ℂ)) ξ N := by
          filter_upwards [eventually_gt_atTop 0] with N hN using (birkhoff_one ξ hN).symm
        rw [show (∫ x, (1 : C(S6, ℂ)) x ∂haar) = 1 by simp]
        exact Tendsto.congr' hev tendsto_const_nhds
      · rw [integral_e_eq_zero hr, funext (birkhoff_e r ξ)]
        exact h r hr
    | zero =>
      simp [birkhoff_zero]
    | add f g _ _ hf hg =>
      simp only [birkhoff_add]
      rw [show (∫ x, (f + g) x ∂haar) = (∫ x, f x ∂haar) + ∫ x, g x ∂haar by
        simp only [ContinuousMap.add_apply]
        exact MeasureTheory.integral_add (integrable_char f) (integrable_char g)]
      exact hf.add hg
    | smul c f _ hf =>
      simp only [birkhoff_smul]
      rw [show (∫ x, (c • f) x ∂haar) = c * ∫ x, f x ∂haar by
        simp only [ContinuousMap.smul_apply, smul_eq_mul]
        exact MeasureTheory.integral_const_mul c _]
      exact hf.const_mul c

/-! ### (2) ⇔ (3) -/

/-- Weyl's criterion, in the shape in which the family statement uses it. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_dictionary"]
theorem weylCriterion_iff_scaled (t : ℕ → ℝ) :
    WeylCriterion t ↔ ∀ h : ℤ, h ≠ 0 →
      Tendsto (fun N => (∑ n ∈ Finset.range N,
        Complex.exp (2 * Real.pi * Complex.I * ((h : ℝ) * t n))) / N) atTop (𝓝 0) := by
  constructor
  · intro hw h hh
    refine Tendsto.congr (fun N => ?_) (hw h hh)
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    push_cast
    ring
  · intro hw h hh
    refine Tendsto.congr (fun N => ?_) (hw h hh)
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    push_cast
    ring

/-- **(2) ⇔ (3)**: the Weyl sums of the whole `ℤ[1/6]`-family vanish iff every member of the
family is u.d. mod 1.  The point is that `ℤ \ {0}` maps `ℤ[1/6] \ {0}` into itself, so the integer
frequencies demanded by Weyl's criterion for one member of the family are already members of the
family. -/
@[category research solved, AMS 11, ref "A1plus", group "th_solenoid_dictionary"]
theorem weylFamily_iff_udFamily (ξ : ℝ) : WeylFamily ξ ↔ UDFamily ξ := by
  constructor
  · intro hw r hr
    rw [Bertin.uniformlyDistributedModOne_iff_weylCriterion, weylCriterion_iff_scaled]
    intro h hh
    have hrmem : ((h : ℚ) * (r : ℚ)) ∈ Z16 := Subring.mul_mem _ (intCast_mem _ h) r.2
    have hne : ((⟨(h : ℚ) * (r : ℚ), hrmem⟩ : Z16) : ℚ) ≠ 0 := by
      simp only [ne_eq, mul_eq_zero]
      push Not
      exact ⟨by exact_mod_cast hh, hr⟩
    have hlim := hw ⟨(h : ℚ) * (r : ℚ), hrmem⟩ hne
    refine Tendsto.congr (fun N => ?_) hlim
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    push_cast
    ring
  · intro hu r hr
    have hw := (Bertin.uniformlyDistributedModOne_iff_weylCriterion _).mp (hu r hr)
    rw [weylCriterion_iff_scaled] at hw
    have hlim := hw 1 one_ne_zero
    refine Tendsto.congr (fun N => ?_) hlim
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    push_cast
    ring

/-! ### The dictionary -/

/-- **The Weyl dictionary** (plan-A1+ §2.2, W3's capstone).  For every real `ξ` the following are
equivalent:

1. the empirical measures of the `T`-orbit of `wind ξ` converge weak-∗ to Haar measure on `Σ₆`;
2. every Weyl sum `(1/N) Σ_{n<N} e(r ξ (3/2)ⁿ)` with `r ∈ ℤ[1/6] \ {0}` tends to `0`;
3. every sequence `(r ξ (3/2)ⁿ)_n` with `r ∈ ℤ[1/6] \ {0}` is uniformly distributed mod 1.

Nothing here is conditional: this is a theorem about the object, not about `(3/2)ⁿ`. -/
@[category research solved, AMS 11, ref "A1plus", group "th_solenoid_dictionary"]
theorem weyl_dictionary (ξ : ℝ) : [Equidistributed ξ, WeylFamily ξ, UDFamily ξ].TFAE := by
  tfae_have 1 ↔ 2 := equidistributed_iff_weylFamily ξ
  tfae_have 2 ↔ 3 := weylFamily_iff_udFamily ξ
  tfae_finish

/-- **Equidistribution in `Σ₆` implies the target statement `T`**: `(ξ (3/2)ⁿ)` is u.d. mod 1.
It is the `r = 1` slice of the dictionary — and the dictionary delivers the whole master family
`{ξ m/6ᵏ}` at the same time. -/
@[category research solved, AMS 11, ref "A1plus", group "th_solenoid_dictionary"]
theorem ud_of_equidistributed {ξ : ℝ} (h : Equidistributed ξ) :
    Bertin.UniformlyDistributedModOne (fun n => ξ * (3 / 2) ^ n) := by
  have hud := (weylFamily_iff_udFamily ξ).mp ((equidistributed_iff_weylFamily ξ).mp h)
  have h1 := hud 1 (by norm_num)
  simpa using h1

/-! ### Sanity: the dictionary is not vacuous -/

/-- The frequency group is non-trivial. -/
@[category test, AMS 11, ref "A1plus", group "th_solenoid_dictionary"]
theorem exists_freq_ne_zero : ∃ r : Z16, (r : ℚ) ≠ 0 := ⟨1, one_ne_zero⟩

/-- Characters have modulus one. -/
@[category test, AMS 11, ref "A1plus", group "th_solenoid_dictionary"]
theorem norm_e_eq_one (r : Z16) (x : S6) : ‖e r x‖ = 1 := by
  rw [e_apply]
  exact Circle.norm_coe _

/-- **Non-vacuity**: `ξ = 0` is *not* equidistributed — its orbit is the fixed point `0`, and every
Weyl sum is identically `1`.  So the three statements of the dictionary are genuine conditions on
`ξ`, not tautologies. -/
@[category test, AMS 11, ref "A1plus", group "th_solenoid_dictionary"]
theorem not_weylFamily_zero : ¬ WeylFamily 0 := by
  intro h
  have h1 := h 1 one_ne_zero
  have hev : (fun N : ℕ => (∑ _n ∈ Finset.range N,
      Complex.exp (2 * Real.pi * Complex.I * ((((1 : Z16) : ℚ) : ℝ) * (0 * (3 / 2) ^ _n)))) / N)
      =ᶠ[atTop] fun _ => (1 : ℂ) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hone : ∀ n ∈ Finset.range N,
        Complex.exp (2 * Real.pi * Complex.I * ((((1 : Z16) : ℚ) : ℝ) * (0 * (3 / 2) ^ n)))
          = 1 := by
      intro n _
      norm_num
    rw [Finset.sum_congr rfl hone, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact div_self (Nat.cast_ne_zero.mpr hN.ne')
  have := tendsto_nhds_unique (h1.congr' hev) tendsto_const_nhds
  exact zero_ne_one this

@[category test, AMS 11, ref "A1plus", group "th_solenoid_dictionary"]
theorem not_equidistributed_zero : ¬ Equidistributed 0 := fun h =>
  not_weylFamily_zero ((equidistributed_iff_weylFamily 0).mp h)

/-! ### The finite-level bridge: cells are floor residues -/

/-- **The residue packaging.**  Shifting `wind η` into the fundamental domain subtracts the integer
part: the representative is `(⟨η⟩, -⌊η⌋, -⌊η⌋)`.  So the `Σ₆`-orbit of the winding point carries
*jointly* the fractional parts and the floor residues at both finite places. -/
@[category research solved, AMS 11, ref "A1plus", group "th_solenoid_dictionary"]
theorem wind_repr (η : ℝ) :
    wind η = QuotientAddGroup.mk (Int.fract η, -((⌊η⌋ : ℤ) : ℚ_[2]), -((⌊η⌋ : ℤ) : ℚ_[3])) := by
  rw [wind, QuotientAddGroup.eq]
  refine mem_Δ₆.mpr ⟨-((⌊η⌋ : ℤ) : ℚ), neg_mem (intCast_mem _ _), ?_⟩
  rw [diag_apply]
  refine Prod.ext_iff.mpr ⟨?_, Prod.ext_iff.mpr ⟨?_, ?_⟩⟩
  · show ((-((⌊η⌋ : ℤ) : ℚ) : ℚ) : ℝ) = -η + Int.fract η
    rw [Int.fract]
    push_cast
    ring
  · show ((-((⌊η⌋ : ℤ) : ℚ) : ℚ) : ℚ_[2]) = -0 + -((⌊η⌋ : ℤ) : ℚ_[2])
    push_cast
    ring
  · show ((-((⌊η⌋ : ℤ) : ℚ) : ℚ) : ℚ_[3]) = -0 + -((⌊η⌋ : ℤ) : ℚ_[3])
    push_cast
    ring

/-- The fundamental-domain representative of `wind η` really lies in `D`. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_dictionary"]
theorem wind_repr_mem_D (η : ℝ) :
    (Int.fract η, -((⌊η⌋ : ℤ) : ℚ_[2]), -((⌊η⌋ : ℤ) : ℚ_[3])) ∈ D := by
  refine mem_D.mpr ⟨⟨Int.fract_nonneg η, Int.fract_lt_one η⟩, ?_, ?_⟩
  · rw [norm_neg]
    exact Padic.norm_int_le_one _
  · rw [norm_neg]
    exact Padic.norm_int_le_one _

/-- A point of the fundamental domain lies in the image of `R ⊆ D` iff it lies in `R`: the cells
are read off the representative with no folding. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_dictionary"]
theorem mk_mem_mk_image_iff {R : Set G6} (hR : R ⊆ D) {u : G6} (hu : u ∈ D) :
    (QuotientAddGroup.mk u : S6) ∈ QuotientAddGroup.mk '' R ↔ u ∈ R := by
  constructor
  · intro h
    have hmem : u ∈ (QuotientAddGroup.mk (s := Δ₆)) ⁻¹'
        ((QuotientAddGroup.mk (s := Δ₆)) '' R) ∩ D := ⟨h, hu⟩
    rwa [preimage_image_inter_D hR] at hmem
  · intro h
    exact ⟨u, h, rfl⟩

/-- Congruence of integers is membership in a `p`-adic residue ball. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_dictionary"]
theorem neg_intCast_mem_residueBall_iff {p : ℕ} [Fact p.Prime] (k : ℕ) (n m : ℤ) :
    (-((n : ℤ) : ℚ_[p])) ∈ Padic.residueBall p k (-((m : ℤ) : ℚ_[p])) ↔
      ((p : ℤ) ^ k ∣ n - m) := by
  rw [Padic.mem_residueBall]
  have hrw : (-((n : ℤ) : ℚ_[p])) - (-((m : ℤ) : ℚ_[p])) = (((m - n : ℤ) : ℚ) : ℚ_[p]) := by
    push_cast
    ring
  rw [hrw, Padic.eq_padicNorm]
  have hpow : ((p : ℤ) ^ k ∣ n - m) ↔ (((p ^ k : ℕ) : ℤ) ∣ (m - n)) := by
    rw [show (((p ^ k : ℕ) : ℤ)) = ((p : ℤ) ^ k) by push_cast; ring, dvd_sub_comm]
  rw [hpow, padicNorm.dvd_iff_norm_le,
    show ((p : ℝ) ^ (-k : ℤ)) = (((p : ℚ) ^ (-k : ℤ) : ℚ) : ℝ) by push_cast; ring]
  exact Rat.cast_le

/-- **The finite-level bridge.**  For `η` real, the winding point `wind η` lies in the level-`(k, j)`
cell over `(a, b)` centred at the classes of `-n` and `-m` **iff** the fractional part of `η` lies
in `(a, b)` and the floor of `η` is congruent to `n` mod `2ᵏ` and to `m` mod `3ʲ`.  Combined with
`haar_cell` (W2), which gives that cell the mass `(b - a) 2⁻ᵏ 3⁻ʲ`, this is the statement that
equidistribution in `Σ₆` *is* the joint uniformization of fractional part and floor residues — the
`Σ₆`-side of `Z32.floor_emod_iff_fract_mem`. -/
@[category research solved, AMS 11, ref "A1plus", group "th_solenoid_dictionary"]
theorem level_bridge {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (k j : ℕ) (n m : ℤ) (η : ℝ) :
    wind η ∈ cell a b k (-((n : ℤ) : ℚ_[2])) j (-((m : ℤ) : ℚ_[3])) ↔
      (Int.fract η ∈ Set.Ioo a b ∧ (2 : ℤ) ^ k ∣ ⌊η⌋ - n ∧ (3 : ℤ) ^ j ∣ ⌊η⌋ - m) := by
  have hsub : (Ioo a b ×ˢ (Padic.residueBall 2 k (-((n : ℤ) : ℚ_[2]))
      ×ˢ Padic.residueBall 3 j (-((m : ℤ) : ℚ_[3])))) ⊆ D := by
    rintro ⟨x, y, z⟩ ⟨hx, hy, hz⟩
    exact ⟨⟨ha.trans hx.1.le, hx.2.trans_le hb⟩,
      Padic.residueBall_subset_unitBall (by rw [norm_neg]; exact Padic.norm_int_le_one _) k hy,
      Padic.residueBall_subset_unitBall (by rw [norm_neg]; exact Padic.norm_int_le_one _) j hz⟩
  rw [cell, wind_repr, mk_mem_mk_image_iff hsub (wind_repr_mem_D η)]
  rw [Set.mem_prod, Set.mem_prod]
  rw [neg_intCast_mem_residueBall_iff (p := 2), neg_intCast_mem_residueBall_iff (p := 3)]
  norm_num

end TH.S6
