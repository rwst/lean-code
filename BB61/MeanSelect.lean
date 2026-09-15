/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Realising a mean by an equal-weight sample

Formal companion of `note-1061-M1.html` (milestone M1 of `plans/plan-1061.html`),
Proposition 8(ii).

The combinatorial input to saturation is this: given finitely many bounded observables
`g 0, …, g (m-1)` on a probability space, each of mean **zero**, one can pick a *sequence* of
points `ω 0, ω 1, …` whose equal-weight averages kill all `m` means simultaneously,

`|(1/q) ∑_{l<q} g i (ω l)| ≤ δ`   for every `i < m` and every `q ≥ m C²/δ²`.

No independence, no product measure, no law of large numbers: the points are chosen
**greedily**.  Writing `s_q ∈ ℝ^m` for the vector of partial sums, the mean-zero hypothesis
says `∫ ⟨s_q, g(x)⟩ dμ(x) = 0`, so *some* `x` has `⟨s_q, g(x)⟩ ≤ 0`; taking `ω q` to be such a
point makes

`‖s_{q+1}‖² = ‖s_q‖² + 2⟨s_q, g(ω q)⟩ + ‖g(ω q)‖² ≤ ‖s_q‖² + m C²`,

hence `‖s_q‖² ≤ q m C²`, which is `o(q²)`.  This is the whole of `exists_greedy_sq_le`; the
`δ`-form `exists_greedy_le` is the version the construction consumes.

The choice at each step is a `Classical.choose`, so the sequence is a genuine selection, not a
random sample — the price is that nothing is said about *which* points are picked.
-/

namespace BB61

open MeasureTheory Filter BoundedContinuousFunction

section MeanSelect

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable (μ : Measure X) [IsProbabilityMeasure μ]

/-- A bounded observable of mean zero is somewhere non-positive. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_nonpos_of_integral_eq_zero (f : X →ᵇ ℝ) (hf : ∫ x, f x ∂μ = 0) :
    ∃ x : X, f x ≤ 0 := by
  by_contra hcon
  push Not at hcon
  have hpos : 0 < ∫ x, f x ∂μ := by
    rw [integral_pos_iff_support_of_nonneg (fun x => (hcon x).le) (f.integrable μ)]
    have : Function.support (f : X → ℝ) = Set.univ :=
      Set.eq_univ_iff_forall.mpr fun x => (hcon x).ne'
    rw [this, measure_univ]
    exact zero_lt_one
  rw [hf] at hpos
  exact lt_irrefl 0 hpos

/-- **The greedy selection.**  For finitely many bounded observables of mean zero there is a
sequence of points along which every partial sum stays `O(√q)` in the euclidean norm. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_greedy_sq_le (m : ℕ) (g : ℕ → X →ᵇ ℝ) (Cb : ℝ)
    (hCb : ∀ i, i < m → ‖g i‖ ≤ Cb) (hmean : ∀ i, i < m → ∫ x, g i x ∂μ = 0) :
    ∃ ω : ℕ → X, ∀ q : ℕ,
      ∑ i ∈ Finset.range m, (∑ l ∈ Finset.range q, g i (ω l)) ^ 2 ≤ q * (m * Cb ^ 2) := by
  classical
  -- at each state `s ∈ ℝ^m` some point makes the inner product `⟨s, g(x)⟩` non-positive
  have key : ∀ s : ℕ → ℝ, ∃ x : X, ∑ i ∈ Finset.range m, s i * g i x ≤ 0 := by
    intro s
    set F : X →ᵇ ℝ := ∑ i ∈ Finset.range m, (s i) • g i with hFdef
    have hFapp : ∀ x, F x = ∑ i ∈ Finset.range m, s i * g i x := by
      intro x
      rw [hFdef]
      simp [BoundedContinuousFunction.coe_sum, Finset.sum_apply]
    have hF0 : ∫ x, F x ∂μ = 0 := by
      have : ∫ x, F x ∂μ = ∑ i ∈ Finset.range m, s i * ∫ x, g i x ∂μ := by
        rw [show (fun x => F x) = fun x => ∑ i ∈ Finset.range m, s i * g i x from funext hFapp]
        rw [integral_finsetSum _ (fun i _ => ((g i).integrable μ).const_mul (s i))]
        exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
      rw [this]
      exact Finset.sum_eq_zero fun i hi => by
        rw [hmean i (Finset.mem_range.mp hi), mul_zero]
    obtain ⟨x, hx⟩ := exists_nonpos_of_integral_eq_zero μ F hF0
    exact ⟨x, by rwa [hFapp] at hx⟩
  set pick : (ℕ → ℝ) → X := fun s => (key s).choose with hpickdef
  have hpick : ∀ s : ℕ → ℝ, ∑ i ∈ Finset.range m, s i * g i (pick s) ≤ 0 :=
    fun s => (key s).choose_spec
  -- the greedy state: the vector of partial sums
  let st : ℕ → ℕ → ℝ := fun q =>
    Nat.rec (motive := fun _ => ℕ → ℝ) (fun _ => (0 : ℝ)) (fun _ s i => s i + g i (pick s)) q
  have hst0 : ∀ i, st 0 i = 0 := fun _ => rfl
  have hstS : ∀ q i, st (q + 1) i = st q i + g i (pick (st q)) := fun _ _ => rfl
  refine ⟨fun q => pick (st q), fun q => ?_⟩
  -- the state *is* the partial sum
  have hsum : ∀ q i, st q i = ∑ l ∈ Finset.range q, g i (pick (st l)) := by
    intro q
    induction q with
    | zero => intro i; rw [hst0, Finset.range_zero, Finset.sum_empty]
    | succ q ih => intro i; rw [hstS, Finset.sum_range_succ, ih i]
  -- the greedy inequality
  have hmain : ∀ q : ℕ, ∑ i ∈ Finset.range m, (st q i) ^ 2 ≤ q * (m * Cb ^ 2) := by
    intro q
    induction q with
    | zero => simp [hst0]
    | succ q ih =>
      have hexp : ∀ i ∈ Finset.range m, (st (q + 1) i) ^ 2
          = (st q i) ^ 2 + 2 * (st q i * g i (pick (st q))) + (g i (pick (st q))) ^ 2 := by
        intro i _
        rw [hstS]; ring
      have hcross : ∑ i ∈ Finset.range m, 2 * (st q i * g i (pick (st q))) ≤ 0 := by
        rw [← Finset.mul_sum]
        have := hpick (st q)
        nlinarith [this]
      have hsq : ∑ i ∈ Finset.range m, (g i (pick (st q))) ^ 2 ≤ m * Cb ^ 2 := by
        calc ∑ i ∈ Finset.range m, (g i (pick (st q))) ^ 2
            ≤ ∑ _i ∈ Finset.range m, Cb ^ 2 := by
              refine Finset.sum_le_sum fun i hi => ?_
              have h1 : |g i (pick (st q))| ≤ Cb := by
                refine le_trans ?_ (hCb i (Finset.mem_range.mp hi))
                simpa [Real.norm_eq_abs] using (g i).norm_coe_le_norm (pick (st q))
              nlinarith [abs_nonneg (g i (pick (st q))), sq_abs (g i (pick (st q)))]
          _ = m * Cb ^ 2 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib, Finset.sum_add_distrib]
      push_cast
      linarith
  have := hmain q
  refine le_trans (le_of_eq ?_) this
  exact Finset.sum_congr rfl fun i _ => by rw [hsum q i]

/-- **The greedy selection, `δ`-form.**  Once `q` exceeds `m C²/δ²` the equal-weight average
of the sample is within `δ` of the mean, simultaneously in all `m` observables. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_greedy_le (m : ℕ) (g : ℕ → X →ᵇ ℝ) (Cb δ : ℝ) (hδ : 0 < δ)
    (hCb : ∀ i, i < m → ‖g i‖ ≤ Cb) (hmean : ∀ i, i < m → ∫ x, g i x ∂μ = 0) :
    ∃ ω : ℕ → X, ∀ q : ℕ, m * Cb ^ 2 ≤ δ ^ 2 * q → ∀ i, i < m →
      |∑ l ∈ Finset.range q, g i (ω l)| ≤ δ * q := by
  obtain ⟨ω, hω⟩ := exists_greedy_sq_le μ m g Cb hCb hmean
  refine ⟨ω, fun q hq i hi => ?_⟩
  have hterm : (∑ l ∈ Finset.range q, g i (ω l)) ^ 2
      ≤ ∑ i' ∈ Finset.range m, (∑ l ∈ Finset.range q, g i' (ω l)) ^ 2 :=
    Finset.single_le_sum (f := fun i' => (∑ l ∈ Finset.range q, g i' (ω l)) ^ 2)
      (fun i' _ => sq_nonneg _) (Finset.mem_range.mpr hi)
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hbound : (∑ l ∈ Finset.range q, g i (ω l)) ^ 2 ≤ (δ * q) ^ 2 := by
    calc (∑ l ∈ Finset.range q, g i (ω l)) ^ 2
        ≤ (q : ℝ) * (m * Cb ^ 2) := le_trans hterm (hω q)
      _ ≤ (q : ℝ) * (δ ^ 2 * q) := by nlinarith
      _ = (δ * q) ^ 2 := by ring
  have hnn : (0 : ℝ) ≤ δ * q := by positivity
  rcases abs_cases (∑ l ∈ Finset.range q, g i (ω l)) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;>
    nlinarith [hbound]

end MeanSelect

end BB61
