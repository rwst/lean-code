/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.Fourier.AddCircle

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
