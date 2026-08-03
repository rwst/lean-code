/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

@[expose] public section

/-!
# Weyl's equidistribution criterion on the circle

If the Fourier (character) sums of a point sequence `(Yₙ)` on `AddCircle T` converge to the
integrals of the characters, then the averages of *every* continuous function converge to its
integral against the Haar (probability) measure:
`tendsto_average_of_tendsto_fourier`. This is the harmonic-analytic heart of Weyl's criterion: a
generating set (the characters `fourier k`, whose `ℂ`-span is dense in `C(AddCircle T, ℂ)` by
`span_fourier_closure_eq_top`) is convergence-determining for weak-* convergence of the empirical
measures to Haar measure.

The proof is the standard two-step argument: linearity propagates the hypothesis from characters to
their finite `ℂ`-linear combinations (`Submodule.span_induction`), and a uniform (sup-norm)
approximation `ε`-squeeze extends it from the dense span to all of `C(AddCircle T, ℂ)`.

## Converse of Weyl's criterion

The rest of the file turns that statement into the usable converse half of Weyl's criterion for a
real sequence `(xₙ)` on the unit circle `AddCircle (1 : ℝ)`:

* `tendsto_average_real_of_tendsto_fourier` — the real-valued form of the above;
* `tendsto_average_of_weylSums` — the hypothesis in its arithmetic shape: if the exponential sums
  `(1/N) Σ_{n<N} exp(2πi k xₙ)` vanish for every `k ≠ 0`, then the averages of every continuous
  `G : C(AddCircle 1, ℝ)` along `(xₙ mod 1)` converge to `∫ G` against Haar;
* `circBump` — the continuous plateau bump used to squeeze an arc's indicator between continuous
  functions, with `integral_circBump_le` and `le_integral_circBump` bounding its integral by the
  Haar measure of the two concentric arcs (`measureReal_closedBall`).

Together these reduce the converse of Weyl's criterion (Kuipers–Niederreiter, Theorem 1.2.1; Weyl
1916) to a bookkeeping argument about the centered fractional part; that final step is carried out
in `BertinPisot.UniformDistribution`.
-/

open MeasureTheory Filter Topology AddCircle

variable {T : ℝ} [hT : Fact (0 < T)]

/-- **Weyl's criterion on `AddCircle T`.** Let `Y : ℕ → AddCircle T`. If for every integer `k` the
averages of the character `fourier k` along `Y` converge to its Haar integral, then for *every*
continuous `F : C(AddCircle T, ℂ)` the averages converge to the Haar integral of `F`. -/
theorem tendsto_average_of_tendsto_fourier (Y : ℕ → AddCircle T)
    (hfou : ∀ k : ℤ, Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, fourier k (Y n)) / N) atTop
      (𝓝 (∫ b, fourier k b ∂(haarAddCircle (T := T))))) :
    ∀ F : C(AddCircle T, ℂ), Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, F (Y n)) / N) atTop
      (𝓝 (∫ b, F b ∂(haarAddCircle (T := T)))) := by
  set μ : Measure (AddCircle T) := haarAddCircle with hμ
  have hint : ∀ g : C(AddCircle T, ℂ), Integrable g μ := fun g =>
    g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  -- the property holds on the span of the characters, by linearity
  have hspan : ∀ g ∈ Submodule.span ℂ (Set.range (fourier (T := T))),
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, g (Y n)) / N) atTop (𝓝 (∫ b, g b ∂μ)) := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hgmem => obtain ⟨k, rfl⟩ := hgmem; exact hfou k
    | zero =>
        simp only [ContinuousMap.zero_apply, Finset.sum_const_zero, zero_div, integral_zero]
        exact tendsto_const_nhds
    | add g₁ g₂ _ _ ih₁ ih₂ =>
        simp only [ContinuousMap.add_apply, Finset.sum_add_distrib, add_div,
          integral_add (hint g₁) (hint g₂)]
        exact ih₁.add ih₂
    | smul c g _ ih =>
        simp only [ContinuousMap.smul_apply, smul_eq_mul, ← Finset.mul_sum, mul_div_assoc,
          integral_const_mul]
        exact ih.const_mul c
  -- extend from the dense span to all continuous functions by uniform approximation
  intro F
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hF : F ∈ closure (Submodule.span ℂ (Set.range (fourier (T := T))) : Set _) := by
    rw [← Submodule.topologicalClosure_coe, span_fourier_closure_eq_top, Submodule.top_coe]
    exact Set.mem_univ F
  obtain ⟨p, hp, hdist⟩ := Metric.mem_closure_iff.mp hF (ε / 3) (by positivity)
  rw [dist_eq_norm] at hdist
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp (hspan p hp)) (ε / 3) (by positivity)
  refine ⟨N₀, fun N hN => ?_⟩
  have hbound : ∀ z : AddCircle T, ‖F z - p z‖ ≤ ‖F - p‖ := fun z => by
    simpa using (F - p).norm_coe_le_norm z
  -- the sample averages of `F` and `p` differ by at most `‖F - p‖`
  have h1 : ‖(∑ n ∈ Finset.range N, F (Y n)) / N - (∑ n ∈ Finset.range N, p (Y n)) / N‖
      ≤ ‖F - p‖ := by
    rw [div_sub_div_same, ← Finset.sum_sub_distrib, norm_div, Complex.norm_natCast]
    rcases Nat.eq_zero_or_pos N with h | h
    · simp [h]
    · rw [div_le_iff₀ (by exact_mod_cast h)]
      calc ‖∑ n ∈ Finset.range N, (F (Y n) - p (Y n))‖
          ≤ ∑ n ∈ Finset.range N, ‖F (Y n) - p (Y n)‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ Finset.range N, ‖F - p‖ := Finset.sum_le_sum (fun n _ => hbound _)
        _ = ‖F - p‖ * N := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
  -- their integrals differ by at most `‖F - p‖` (Haar is a probability measure)
  have h2 : ‖(∫ b, p b ∂μ) - ∫ b, F b ∂μ‖ ≤ ‖F - p‖ := by
    rw [← integral_sub (hint p) (hint F)]
    calc ‖∫ b, (p b - F b) ∂μ‖ ≤ ∫ b, ‖p b - F b‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ _b, ‖F - p‖ ∂μ := by
          refine integral_mono_of_nonneg (by filter_upwards with z using norm_nonneg _)
            (integrable_const _) ?_
          filter_upwards with z; rw [norm_sub_rev]; exact hbound z
      _ = ‖F - p‖ := by simp
  have hN0' := hN₀ N hN
  rw [dist_eq_norm] at hN0' ⊢
  have htri : ‖(∑ n ∈ Finset.range N, F (Y n)) / N - ∫ b, F b ∂μ‖
      ≤ ‖(∑ n ∈ Finset.range N, F (Y n)) / N - (∑ n ∈ Finset.range N, p (Y n)) / N‖
        + ‖(∑ n ∈ Finset.range N, p (Y n)) / N - ∫ b, p b ∂μ‖
        + ‖(∫ b, p b ∂μ) - ∫ b, F b ∂μ‖ := by
    have heq : (∑ n ∈ Finset.range N, F (Y n)) / N - ∫ b, F b ∂μ
        = ((∑ n ∈ Finset.range N, F (Y n)) / N - (∑ n ∈ Finset.range N, p (Y n)) / N)
          + ((∑ n ∈ Finset.range N, p (Y n)) / N - ∫ b, p b ∂μ)
          + ((∫ b, p b ∂μ) - ∫ b, F b ∂μ) := by ring
    rw [heq]; exact norm_add₃_le
  linarith [htri, h1, h2, hN0', hdist]

/-- Real-valued form of `tendsto_average_of_tendsto_fourier`: under the same hypothesis, the
averages of every *real*-valued continuous function converge to its Haar integral. -/
theorem tendsto_average_real_of_tendsto_fourier (Y : ℕ → AddCircle T)
    (hfou : ∀ k : ℤ, Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, fourier k (Y n)) / N) atTop
      (𝓝 (∫ b, fourier k b ∂(haarAddCircle (T := T)))))
    (G : C(AddCircle T, ℝ)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, G (Y n)) / N) atTop
      (𝓝 (∫ b, G b ∂(haarAddCircle (T := T)))) := by
  have hC := tendsto_average_of_tendsto_fourier Y hfou
    ⟨fun z => ((G z : ℝ) : ℂ), Complex.continuous_ofReal.comp G.continuous⟩
  simp only [ContinuousMap.coe_mk, integral_complex_ofReal] at hC
  have hpush : ∀ N : ℕ, (∑ n ∈ Finset.range N, ((G (Y n) : ℝ) : ℂ)) / (N : ℂ)
      = (((∑ n ∈ Finset.range N, G (Y n)) / N : ℝ) : ℂ) := by
    intro N; push_cast; ring
  simp only [hpush] at hC
  have h2 := (Complex.continuous_re.tendsto _).comp hC
  simpa [Function.comp_def] using h2

/-! ### The unit circle -/

/-- On the unit circle `AddCircle 1` the Haar probability measure *is* the Lebesgue volume. -/
theorem haarAddCircle_eq_volume :
    (haarAddCircle : Measure (AddCircle (1 : ℝ))) = volume := by
  rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]

/-- The Haar measure of the arc `closedBall c s` on the unit circle is `min 1 (2s)`. -/
theorem measureReal_closedBall (c : AddCircle (1 : ℝ)) {s : ℝ} (hs : 0 ≤ s) :
    (haarAddCircle : Measure (AddCircle (1 : ℝ))).real (Metric.closedBall c s)
      = min 1 (2 * s) := by
  rw [measureReal_def, haarAddCircle_eq_volume, AddCircle.volume_closedBall,
    ENNReal.toReal_ofReal (le_min zero_le_one (by linarith))]

/-- The continuous *plateau bump* of the arc `closedBall c s` with skirt width `η`: it equals `1`
on `closedBall c (s - η)`, vanishes off `closedBall c s`, and takes values in `[0, 1]`. -/
noncomputable def circBump (c : AddCircle (1 : ℝ)) (s η : ℝ) : C(AddCircle (1 : ℝ), ℝ) :=
  ⟨fun z => max 0 (min 1 ((s - ‖z - c‖) / η)), by fun_prop⟩

variable {c : AddCircle (1 : ℝ)} {s η : ℝ} {z : AddCircle (1 : ℝ)}

theorem circBump_nonneg : 0 ≤ circBump c s η z := le_max_left _ _

theorem circBump_le_one : circBump c s η z ≤ 1 := max_le zero_le_one (min_le_left _ _)

/-- The bump is `1` on the inner arc. -/
theorem circBump_eq_one (hη : 0 < η) (hz : ‖z - c‖ ≤ s - η) : circBump c s η z = 1 := by
  have h1 : (1 : ℝ) ≤ (s - ‖z - c‖) / η := by rw [le_div_iff₀ hη]; linarith
  simp only [circBump, ContinuousMap.coe_mk, min_eq_left h1, max_eq_right zero_le_one]

/-- The bump vanishes off the outer arc. -/
theorem circBump_eq_zero (hη : 0 < η) (hz : s ≤ ‖z - c‖) : circBump c s η z = 0 := by
  have h1 : (s - ‖z - c‖) / η ≤ 0 := by rw [div_le_iff₀ hη]; linarith
  simp only [circBump, ContinuousMap.coe_mk]
  exact max_eq_left (le_trans (min_le_right _ _) h1)

private theorem integrable_circBump (c : AddCircle (1 : ℝ)) (s η : ℝ) :
    Integrable (circBump c s η) (haarAddCircle : Measure (AddCircle (1 : ℝ))) :=
  (circBump c s η).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The bump's integral is at most the measure of the outer arc. -/
theorem integral_circBump_le (c : AddCircle (1 : ℝ)) {s η : ℝ} (hs : 0 ≤ s) (hη : 0 < η) :
    ∫ z, circBump c s η z ∂(haarAddCircle : Measure (AddCircle (1 : ℝ))) ≤ min 1 (2 * s) := by
  have hle : ∀ z, circBump c s η z
      ≤ (Metric.closedBall c s).indicator (1 : AddCircle (1 : ℝ) → ℝ) z := by
    intro z
    by_cases hz : z ∈ Metric.closedBall c s
    · rw [Set.indicator_of_mem hz]; exact circBump_le_one
    · rw [Set.indicator_of_notMem hz, circBump_eq_zero hη]
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      exact le_of_not_ge hz
  calc ∫ z, circBump c s η z ∂(haarAddCircle : Measure (AddCircle (1 : ℝ)))
      ≤ ∫ z, (Metric.closedBall c s).indicator (1 : AddCircle (1 : ℝ) → ℝ) z
          ∂(haarAddCircle : Measure (AddCircle (1 : ℝ))) :=
        integral_mono (integrable_circBump c s η)
          ((integrable_const (1 : ℝ)).indicator measurableSet_closedBall) hle
    _ = min 1 (2 * s) := by
        rw [integral_indicator_one measurableSet_closedBall, measureReal_closedBall c hs]

/-- The bump's integral is at least the measure of the inner arc. -/
theorem le_integral_circBump (c : AddCircle (1 : ℝ)) {s η : ℝ} (hη : 0 < η) (hs : 0 ≤ s - η) :
    min 1 (2 * (s - η))
      ≤ ∫ z, circBump c s η z ∂(haarAddCircle : Measure (AddCircle (1 : ℝ))) := by
  have hle : ∀ z, (Metric.closedBall c (s - η)).indicator (1 : AddCircle (1 : ℝ) → ℝ) z
      ≤ circBump c s η z := by
    intro z
    by_cases hz : z ∈ Metric.closedBall c (s - η)
    · have hz' : ‖z - c‖ ≤ s - η := by rwa [Metric.mem_closedBall, dist_eq_norm] at hz
      rw [Set.indicator_of_mem hz, circBump_eq_one hη hz']
      exact le_rfl
    · rw [Set.indicator_of_notMem hz]; exact circBump_nonneg
  calc min 1 (2 * (s - η))
      = ∫ z, (Metric.closedBall c (s - η)).indicator (1 : AddCircle (1 : ℝ) → ℝ) z
          ∂(haarAddCircle : Measure (AddCircle (1 : ℝ))) := by
        rw [integral_indicator_one measurableSet_closedBall, measureReal_closedBall c hs]
    _ ≤ _ := integral_mono ((integrable_const (1 : ℝ)).indicator measurableSet_closedBall)
        (integrable_circBump c s η) hle

/-- The integral of a character over the unit circle vanishes for every non-zero frequency. -/
theorem integral_fourier_eq_zero {k : ℤ} (hk : k ≠ 0) :
    ∫ z, fourier k z ∂(haarAddCircle : Measure (AddCircle (1 : ℝ))) = 0 := by
  have hc : (2 * (Real.pi : ℂ) * Complex.I * k) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
      (Int.cast_ne_zero.mpr hk)
  have hpre := AddCircle.intervalIntegral_preimage (1 : ℝ) 0 (fun z => fourier k z)
  rw [haarAddCircle_eq_volume, ← hpre]
  have hfun : ∀ t : ℝ, fourier k ((t : ℝ) : AddCircle (1 : ℝ))
      = Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * k) * t) := by
    intro t; rw [fourier_coe_apply]; congr 1; push_cast; ring
  simp only [hfun]
  rw [integral_exp_mul_complex hc]
  have h1 : (2 * (Real.pi : ℂ) * Complex.I * k) * ((0 : ℝ) + 1 : ℝ)
      = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by push_cast; ring
  have h0 : (2 * (Real.pi : ℂ) * Complex.I * k) * ((0 : ℝ) : ℂ) = 0 := by push_cast; ring
  rw [h1, h0, Complex.exp_int_mul_two_pi_mul_I, Complex.exp_zero, sub_self, zero_div]

/-- Vanishing exponential sums give the Fourier-coefficient hypothesis of
`tendsto_average_of_tendsto_fourier` at `T = 1`. The `k = 0` character contributes the constant `1`
(both sides), and each `k ≠ 0` character has vanishing Haar integral (`integral_fourier_eq_zero`),
so the hypothesis is exactly the vanishing of the `k`-th Weyl sum. -/
theorem tendsto_fourier_of_weylSums {x : ℕ → ℝ}
    (hw : ∀ k : ℤ, k ≠ 0 → Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * k * x n)) / N) atTop (𝓝 0))
    (k : ℤ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, fourier k ((x n : ℝ) : AddCircle (1 : ℝ))) / N) atTop
      (𝓝 (∫ b, fourier k b ∂(haarAddCircle (T := (1 : ℝ))))) := by
  rcases eq_or_ne k 0 with rfl | hk
  · have hint : ∫ z, fourier (0 : ℤ) z ∂(haarAddCircle : Measure (AddCircle (1 : ℝ))) = 1 := by
      simp
    rw [hint]
    refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (1 : ℂ)))
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    simp [Finset.sum_const, Finset.card_range, div_self hN']
  · rw [integral_fourier_eq_zero hk]
    refine (hw k hk).congr fun N => ?_
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring

/-- **Weyl's criterion, converse direction** (Weyl 1916; Kuipers–Niederreiter, Theorem 1.2.1), in
the shape in which it is used: if the exponential sums `(1/N) Σ_{n<N} exp(2πi k xₙ)` vanish in the
limit for every non-zero integer `k`, then for every continuous `G` on the circle the averages of
`G` along `(xₙ mod 1)` converge to the Haar integral of `G`. -/
theorem tendsto_average_of_weylSums {x : ℕ → ℝ}
    (hw : ∀ k : ℤ, k ≠ 0 → Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * k * x n)) / N) atTop (𝓝 0))
    (G : C(AddCircle (1 : ℝ), ℝ)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, G ((x n : ℝ) : AddCircle (1 : ℝ))) / N) atTop
      (𝓝 (∫ z, G z ∂(haarAddCircle : Measure (AddCircle (1 : ℝ))))) :=
  tendsto_average_real_of_tendsto_fourier (fun n => ((x n : ℝ) : AddCircle (1 : ℝ)))
    (tendsto_fourier_of_weylSums hw) G

/-- The complex-valued companion of `tendsto_average_of_weylSums`: vanishing Weyl sums make the
averages of every continuous `F : C(AddCircle 1, ℂ)` along `(xₙ mod 1)` converge to `∫ F` against
Haar. This is the form needed to transport the criterion to continuous 1-periodic functions
`ℝ → ℂ`. -/
theorem tendsto_average_complex_of_weylSums {x : ℕ → ℝ}
    (hw : ∀ k : ℤ, k ≠ 0 → Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * k * x n)) / N) atTop (𝓝 0))
    (F : C(AddCircle (1 : ℝ), ℂ)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, F ((x n : ℝ) : AddCircle (1 : ℝ))) / N) atTop
      (𝓝 (∫ z, F z ∂(haarAddCircle : Measure (AddCircle (1 : ℝ))))) :=
  tendsto_average_of_tendsto_fourier (fun n => ((x n : ℝ) : AddCircle (1 : ℝ)))
    (tendsto_fourier_of_weylSums hw) F
