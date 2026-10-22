/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import BB47.QuadraticTails

/-!
# `√(8/π)` ones infinitely often in the binary expansion of `√2`

The current record for the number of ones among the first `N` binary digits of `√2` *infinitely
often* is `(√(8/π) − ε)√N` ([Dub19, Thm. 3 (6)], announced in [Van18, Rem. 7.1]); for *all* `N`
it is `√(2N)(1 + o(1))` ([Van18, Thm. 1.1]; `BB47.QuadraticTails.sqrt_two_ones`).  This file
proves the `√(8/π)` bound (`plans/report-sqrtnorm.html`, rank #4: the formal base line any
improvement of the constant has to beat).

## The argument

For a finite `A ⊆ ℕ` let `U(k) = #{a ∈ A : a ≤ k}` and let `V(N) = #{(a, a') ∈ A² : a + a' ≤ N}`
count the restricted sumset with multiplicity.

* **Upper bound (the sumset inequality, [Dub19, Thm. 1] for `α = 1`).**  If `U(k) ≤ ω√k + C`
  for all `k ≤ N`, then `V(N) ≤ (π/4) ω² N + 2ωC√N + C²` (`V_le`).  Dubickas proves this by a
  minimax lemma over `2m` intervals and a Riemann sum; here it is two lines of **Abel summation**:
  `V(N) = ∑_{a ≤ N} U(N − a)` (`V_eq`), and
  `∑_{a ≤ N} √(N − a) = ∑_{k < N} U(k) (√(N − k) − √(N − k − 1))` (`abel`), and the discrete
  integral `∑_{k < N} √k (√(N − k) − √(N − k − 1)) ≤ (π/4) N` (`arcsine_sum_le`) is controlled
  by the antiderivative `F(x) = (N/4) arccos(1 − 2x/N) − ½√(x(N − x))` of `√x / (2√(N − x))`.
* **Lower bound for `√2` ([Van18, (6), (8)], [Dub19, (28)]).**  With `A` the positions `≤ N` of
  the ones of `√2` and `Y = ⌊2^N √2⌋`, `Y² = H + L`, where `H` collects the pairs with
  `a + a' ≤ N` and `L < 2^{N + 2ℓ}`, `ℓ = ⌊log₂(N + 1)⌋ + 1`.  The borrow block
  `Y² = 2^{2N+1} − R`, `0 < R ≤ 2^{N+2}`, gives `s₂(H) ≥ N − 2ℓ`; pairing the cross terms of `H`
  gives `2 s₂(H) ≤ V(N) + U(N)`.  Hence `V(N) ≥ 2N − U(N) − 4ℓ` (`sqrt_two_V_ge`).

If `U(N) ≤ ω√N` for all large `N` with `πω²/4 < 2`, the two bounds contradict each other.

## Main results

* `BB47.RestrictedSumset.V_le` — the restricted-sumset inequality, finite form.
* `BB47.RestrictedSumset.sqrt_two_V_ge` — `V(N) ≥ 2N − U(N) − 4ℓ` for `√2`.
* `BB47.RestrictedSumset.sqrt_two_ones_io` — **for every `ω < √(8/π)` there are infinitely many
  `N` with more than `ω√N` ones among the binary digits of `√2` at positions `0, …, N`.**

## References

* [Dub19] A. Dubickas, *On the size of a restricted sumset with application to the binary
  expansion of `√d`*, Appl. Anal. Discrete Math. **13** (2019), 346–360,
  doi:10.2298/AADM180720014D — Thm. 1, Thm. 3.
* [Van18] J. Vandehey, *On the binary digits of `√2`*, Integers **18** (2018), #A30,
  arXiv:1711.01722 — Thm. 1.1, Thm. 1.2, Rem. 7.1.
-/

namespace BB47.RestrictedSumset

open Finset Real BB47.Popcount BB47.QuadraticTails

/-! ## Counting functions -/

section Counting

variable (A : Finset ℕ)

/-- `U(k) = #{a ∈ A : a ≤ k}`. -/
@[category API, AMS 11, ref "Dub19", group "bugeaud_10_47"]
def U (k : ℕ) : ℕ := (A.filter (· ≤ k)).card

/-- `V(N) = #{(a, a') ∈ A² : a + a' ≤ N}`, the restricted sumset counted with multiplicity. -/
@[category API, AMS 11, ref "Dub19", group "bugeaud_10_47"]
def V (N : ℕ) : ℕ := ((A ×ˢ A).filter fun p => p.1 + p.2 ≤ N).card

lemma V_eq (N : ℕ) : V A N = ∑ a ∈ A.filter (· ≤ N), U A (N - a) := by
  classical
  simp only [V, U, card_filter, sum_product, sum_filter]
  refine sum_congr rfl fun a _ => ?_
  split_ifs with ha
  · exact sum_congr rfl fun a' _ => by congr 1; exact propext (by omega)
  · exact sum_eq_zero fun a' _ => by split_ifs <;> first | rfl | omega

/-- **Abel summation** against a sequence `g`. -/
lemma abel (g : ℕ → ℝ) (N : ℕ) :
    ∑ a ∈ A.filter (· ≤ N), (g a - g N) = ∑ k ∈ range N, (g k - g (k + 1)) * U A k := by
  have htel : ∀ a ∈ A.filter (· ≤ N), g a - g N = ∑ k ∈ Ico a N, (g k - g (k + 1)) := by
    intro a ha
    have hle : a ≤ N := (mem_filter.mp ha).2
    have := sum_Ico_sub (fun i => -g i) hle
    rw [show g a - g N = -g N - -g a by ring, ← this]
    exact sum_congr rfl fun k _ => by ring
  rw [sum_congr rfl htel]
  rw [sum_comm' (t' := range N) (s' := fun k => A.filter (· ≤ k))]
  · refine sum_congr rfl fun k _ => ?_
    rw [sum_const, nsmul_eq_mul, U, mul_comm]
  · intro a k
    simp only [mem_filter, mem_Ico, mem_range]
    constructor
    · rintro ⟨⟨h1, _⟩, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, by omega⟩, h2, h3⟩

lemma U_mono {k k' : ℕ} (h : k ≤ k') : U A k ≤ U A k' :=
  card_le_card fun a ha => by
    rw [mem_filter] at ha ⊢; exact ⟨ha.1, ha.2.trans h⟩

end Counting

/-! ## The arcsine sum -/

section Arcsine

/-- The antiderivative `F(x) = (N/4) arccos(1 − 2x/N) − ½√(x(N − x))` of `√x / (2√(N − x))`. -/
noncomputable def F (N x : ℝ) : ℝ := N / 4 * arccos (1 - 2 * x / N) - √(x * (N - x)) / 2

lemma F_step {N : ℝ} {k : ℕ} (hk : (k : ℝ) + 1 ≤ N) :
    √(k : ℝ) * (√(N - k) - √(N - (k + 1))) ≤ F N (k + 1) - F N k := by
  have hN : 0 < N := by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  set G : ℝ → ℝ := fun x => F N x + √(k : ℝ) * √(N - x) with hG
  suffices hmono : G k ≤ G (k + 1) by simp only [hG] at hmono; linarith
  have hcont : ContinuousOn G (Set.Icc (k : ℝ) (k + 1)) := by
    simp only [hG, F]
    fun_prop
  have hderiv : ∀ x ∈ Set.Ioo (k : ℝ) (k + 1), HasDerivAt G
      (N / 4 * (-(1 / √(1 - (1 - 2 * x / N) ^ 2)) * (-(2 / N)))
        - (1 * (N - x) + x * (-1)) / (2 * √(x * (N - x))) / 2
        + √(k : ℝ) * ((-1) / (2 * √(N - x)))) x := by
    intro x hx
    have hx0 : 0 < x := lt_of_le_of_lt (Nat.cast_nonneg k) hx.1
    have hxN : x < N := lt_of_lt_of_le hx.2 hk
    have hu : HasDerivAt (fun y : ℝ => 1 - 2 * y / N) (-(2 / N)) x := by
      have := ((hasDerivAt_id x).const_mul 2).div_const N
      simpa [neg_div] using this.const_sub 1
    have h1 : 1 - 2 * x / N ≠ -1 := by
      intro h; field_simp at h; linarith
    have h2 : 1 - 2 * x / N ≠ 1 := by
      intro h; field_simp at h; linarith
    have harc := ((hasDerivAt_arccos h1 h2).comp x hu).const_mul (N / 4)
    have hprod : HasDerivAt (fun y : ℝ => y * (N - y)) (1 * (N - x) + x * (-1)) x :=
      (hasDerivAt_id x).mul ((hasDerivAt_id x).const_sub N |>.congr_deriv (by simp))
    have hs1 := (hprod.sqrt (by positivity)).div_const 2
    have hs2 := (((hasDerivAt_id x).const_sub N).sqrt
      (sub_pos.mpr hxN).ne').const_mul √(k : ℝ)
    exact (harc.sub hs1).add hs2
  have hmon := monotoneOn_of_deriv_nonneg (convex_Icc (k : ℝ) (k + 1)) hcont
    (fun x hx => by
      rw [interior_Icc] at hx
      exact (hderiv x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => by
      rw [interior_Icc] at hx
      rw [(hderiv x hx).deriv]
      have hx0 : 0 < x := lt_of_le_of_lt (Nat.cast_nonneg k) hx.1
      have hxN : x < N := lt_of_lt_of_le hx.2 hk
      set a := √x
      set b := √(N - x)
      have ha : 0 < a := Real.sqrt_pos.mpr hx0
      have hb : 0 < b := Real.sqrt_pos.mpr (by linarith)
      have ha2 : a ^ 2 = x := Real.sq_sqrt hx0.le
      have hb2 : b ^ 2 = N - x := Real.sq_sqrt (by linarith)
      have hab : √(x * (N - x)) = a * b := Real.sqrt_mul hx0.le _
      have h1u : √(1 - (1 - 2 * x / N) ^ 2) = 2 * a * b / N := by
        rw [show 1 - (1 - 2 * x / N) ^ 2 = (2 * a * b / N) ^ 2 by
          field_simp; rw [ha2, hb2]; ring]
        exact Real.sqrt_sq (by positivity)
      have hka : √(k : ℝ) ≤ a := Real.sqrt_le_sqrt hx.1.le
      rw [h1u, hab]
      have hNab : N = a ^ 2 + b ^ 2 := by rw [ha2, hb2]; ring
      have : N / 4 * (-(1 / (2 * a * b / N)) * (-(2 / N)))
          - (1 * (N - x) + x * (-1)) / (2 * (a * b)) / 2
          + √(k : ℝ) * ((-1) / (2 * b)) = (a - √(k : ℝ)) / (2 * b) := by
        rw [← ha2]
        field_simp
        rw [hNab]
        ring
      rw [this]
      exact div_nonneg (by linarith) (by positivity))
  exact hmon (Set.left_mem_Icc.mpr (by linarith)) (Set.right_mem_Icc.mpr (by linarith))
    (by linarith)

/-- **The discrete arcsine integral.**  `∑_{k < N} √k (√(N − k) − √(N − k − 1)) ≤ (π/4) N`. -/
@[category API, AMS 11, ref "Dub19", group "bugeaud_10_47"]
theorem arcsine_sum_le (N : ℕ) :
    ∑ k ∈ range N, √(k : ℝ) * (√((N : ℝ) - k) - √((N : ℝ) - (k + 1))) ≤ π / 4 * N := by
  calc ∑ k ∈ range N, √(k : ℝ) * (√((N : ℝ) - k) - √((N : ℝ) - (k + 1)))
      ≤ ∑ k ∈ range N, (F N ((k + 1 : ℕ) : ℝ) - F N (k : ℕ)) := by
        refine sum_le_sum fun k hk => ?_
        have : (k : ℝ) + 1 ≤ N := by
          have := mem_range.mp hk; exact_mod_cast this
        push_cast
        exact F_step this
    _ = F N N - F N 0 := by rw [sum_range_sub (fun k : ℕ => F N (k : ℝ))]; simp
    _ = π / 4 * N := by
        rcases Nat.eq_zero_or_pos N with rfl | hN
        · simp [F]
        have : (N : ℝ) ≠ 0 := by positivity
        simp only [F]
        rw [show 1 - 2 * (N : ℝ) / N = -1 by field_simp; ring, arccos_neg_one]
        simp
        ring

end Arcsine

/-! ## The restricted-sumset inequality -/

section Upper

variable (A : Finset ℕ)

/-- **The restricted-sumset inequality** ([Dub19, Thm. 1] for `α = 1`, finite form): if
`U(k) ≤ ω√k + C` for all `k ≤ N`, then `V(N) ≤ (π/4) ω² N + 2ωC√N + C²`. -/
@[category research solved, AMS 11, ref "Dub19", group "bugeaud_10_47"]
theorem V_le {ω C : ℝ} (hω : 0 ≤ ω) (hC : 0 ≤ C) (N : ℕ)
    (hU : ∀ k ≤ N, (U A k : ℝ) ≤ ω * √(k : ℝ) + C) :
    (V A N : ℝ) ≤ π / 4 * ω ^ 2 * N + 2 * ω * C * √(N : ℝ) + C ^ 2 := by
  set g : ℕ → ℝ := fun a => √((N : ℝ) - a)
  have hgN : g N = 0 := by simp [g]
  set d : ℕ → ℝ := fun k => g k - g (k + 1)
  have hd : ∀ k, 0 ≤ d k := fun k => by
    simp only [d, g]; push_cast
    exact sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  -- `∑_{a ≤ N} √(N − a) ≤ ω (π/4) N + C √N`
  have hS : ∑ a ∈ A.filter (· ≤ N), g a ≤ ω * (π / 4 * N) + C * √(N : ℝ) := by
    have h1 := abel A g N
    simp only [hgN, sub_zero] at h1
    rw [h1]
    calc ∑ k ∈ range N, d k * U A k ≤ ∑ k ∈ range N, d k * (ω * √(k : ℝ) + C) :=
          sum_le_sum fun k hk => mul_le_mul_of_nonneg_left
            (hU k (mem_range.mp hk).le) (hd k)
      _ = ω * ∑ k ∈ range N, √(k : ℝ) * d k + C * ∑ k ∈ range N, d k := by
          rw [mul_sum, mul_sum, ← sum_add_distrib]
          exact sum_congr rfl fun k _ => by ring
      _ ≤ ω * (π / 4 * N) + C * √(N : ℝ) := by
          have h2 : ∑ k ∈ range N, d k = √(N : ℝ) := by
            simp only [d]
            rw [sum_range_sub' g N, hgN]; simp [g]
          rw [h2]
          have h3 := arcsine_sum_le N
          have : ∑ k ∈ range N, √(k : ℝ) * d k
              = ∑ k ∈ range N, √(k : ℝ) * (√((N : ℝ) - k) - √((N : ℝ) - (k + 1))) := by
            refine sum_congr rfl fun k _ => ?_
            simp only [d, g]; push_cast; ring_nf
          rw [this]
          nlinarith
  have hV : (V A N : ℝ) ≤ ω * ∑ a ∈ A.filter (· ≤ N), g a + C * U A N := by
    rw [V_eq, Nat.cast_sum]
    calc ∑ a ∈ A.filter (· ≤ N), (U A (N - a) : ℝ)
        ≤ ∑ a ∈ A.filter (· ≤ N), (ω * g a + C) := by
          refine sum_le_sum fun a ha => ?_
          have haN : a ≤ N := (mem_filter.mp ha).2
          have := hU (N - a) (Nat.sub_le N a)
          simp only [g]
          rw [Nat.cast_sub haN] at this
          linarith
      _ = ω * ∑ a ∈ A.filter (· ≤ N), g a + C * U A N := by
          rw [sum_add_distrib, mul_sum, sum_const, nsmul_eq_mul, U]; ring
  have hUN := hU N le_rfl
  have hsq : 0 ≤ √(N : ℝ) := Real.sqrt_nonneg _
  calc (V A N : ℝ) ≤ ω * (ω * (π / 4 * N) + C * √(N : ℝ)) + C * (ω * √(N : ℝ) + C) := by
        have := mul_le_mul_of_nonneg_left hS hω
        have := mul_le_mul_of_nonneg_left hUN hC
        linarith
    _ = π / 4 * ω ^ 2 * N + 2 * ω * C * √(N : ℝ) + C ^ 2 := by ring

end Upper

/-! ## Pairing the cross terms of the restricted square -/

section Pairing

variable (A : Finset ℕ) (N : ℕ)

/-- The part `H = ∑_{a + a' ≤ N} 2^{(N − a) + (N − a')}` of `Y²`, `Y = ∑_{a ∈ A} 2^{N − a}`. -/
def H : ℕ := ∑ p ∈ (A ×ˢ A).filter (fun p => p.1 + p.2 ≤ N), 2 ^ ((N - p.1) + (N - p.2))

private lemma swap_sum (P : Finset (ℕ × ℕ)) (hP : ∀ p ∈ P, p.swap ∈ P) (f : ℕ × ℕ → ℕ)
    (hf : ∀ p, f p.swap = f p) :
    ∑ p ∈ P.filter (fun p => ¬ p.1 = p.2 ∧ ¬ p.1 < p.2), f p
      = ∑ p ∈ P.filter (fun p => ¬ p.1 = p.2 ∧ p.1 < p.2), f p := by
  refine sum_nbij' Prod.swap Prod.swap ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl)
    (fun p _ => (hf p).symm)
  · intro p hp
    simp only [mem_filter] at hp ⊢
    exact ⟨hP p hp.1, by simp only [Prod.fst_swap, Prod.snd_swap]; omega⟩
  · intro p hp
    simp only [mem_filter] at hp ⊢
    exact ⟨hP p hp.1, by simp only [Prod.fst_swap, Prod.snd_swap]; omega⟩

private lemma split3 (P : Finset (ℕ × ℕ)) (hP : ∀ p ∈ P, p.swap ∈ P) (f : ℕ × ℕ → ℕ)
    (hf : ∀ p, f p.swap = f p) :
    ∑ p ∈ P, f p = ∑ p ∈ P.filter (fun p => p.1 = p.2), f p
      + 2 * ∑ p ∈ P.filter (fun p => ¬ p.1 = p.2 ∧ p.1 < p.2), f p := by
  rw [← sum_filter_add_sum_filter_not P (fun p => p.1 = p.2),
    ← sum_filter_add_sum_filter_not (P.filter fun p => ¬ p.1 = p.2) (fun p => p.1 < p.2),
    filter_filter, filter_filter, swap_sum P hP f hf]
  ring

/-- **Pairing the cross terms**: `2 s₂(H) ≤ V(N) + |A|`. -/
@[category API, AMS 11, ref "Van18", group "bugeaud_10_47"]
theorem two_ds_H_le : 2 * ds 2 (H A N) ≤ V A N + A.card := by
  classical
  set P := (A ×ˢ A).filter (fun p => p.1 + p.2 ≤ N)
  have hP : ∀ p ∈ P, p.swap ∈ P := by
    intro p hp
    simp only [P, mem_filter, mem_product, Prod.fst_swap, Prod.snd_swap] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, by omega⟩
  set Pd := P.filter (fun p => p.1 = p.2)
  set Pl := P.filter (fun p => ¬ p.1 = p.2 ∧ p.1 < p.2)
  have hH : H A N = ∑ p ∈ Pd, 2 ^ ((N - p.1) + (N - p.2))
      + 2 * ∑ p ∈ Pl, 2 ^ ((N - p.1) + (N - p.2)) :=
    split3 P hP _ (fun p => by simp only [Prod.fst_swap, Prod.snd_swap]; ring_nf)
  have hcard : V A N = Pd.card + 2 * Pl.card := by
    have := split3 P hP (fun _ => 1) (fun _ => rfl)
    simp only [sum_const, smul_eq_mul, mul_one] at this
    exact this
  have hds1 : ds 2 (∑ p ∈ Pd, 2 ^ ((N - p.1) + (N - p.2))) ≤ Pd.card := by
    refine (ds_sum_le le_rfl _ _).trans ?_
    simp [ds_pow le_rfl]
  have hds2 : ds 2 (∑ p ∈ Pl, 2 ^ ((N - p.1) + (N - p.2))) ≤ Pl.card := by
    refine (ds_sum_le le_rfl _ _).trans ?_
    simp [ds_pow le_rfl]
  have hds : ds 2 (H A N) ≤ Pd.card + Pl.card := by
    rw [hH]
    refine (ds_add_le le_rfl _ _).trans ?_
    rw [ds_mul_base le_rfl]
    omega
  have hPd : Pd.card ≤ A.card := by
    refine card_le_card_of_injOn Prod.fst (fun p hp => ?_) (fun p hp q hq hpq => ?_)
    · have hp' := mem_filter.mp (mem_coe.mp hp)
      exact mem_coe.mpr (mem_product.mp (mem_filter.mp hp'.1).1).1
    · simp only [Pd, P, coe_filter, mem_filter, mem_product, Set.mem_ofPred_eq] at hp hq
      exact Prod.ext hpq (by rw [← hp.2, ← hq.2]; exact hpq)
  omega

end Pairing

/-! ## The lower bound for `√2` -/

section SqrtTwo

variable {t : ℕ → ℕ} (ht : StrictMono t)

/-- The positions `≤ N` of the ones of `y = ∑_j 2^{-t_j}`. -/
noncomputable def ones (N : ℕ) : Finset ℕ := (range (kappa ht N)).image t

include ht in
lemma kappa_mono {k k' : ℕ} (h : k ≤ k') : kappa ht k ≤ kappa ht k' := by
  by_contra hlt
  push Not at hlt
  have h1 := (lt_kappa_iff ht k (kappa ht k')).mp hlt
  have h2 := t_kappa_gt ht k'
  omega

lemma U_ones {N k : ℕ} (hk : k ≤ N) : U (ones ht N) k = kappa ht k := by
  have : (ones ht N).filter (· ≤ k) = (range (kappa ht k)).image t := by
    ext a
    simp only [ones, mem_filter, mem_image, mem_range]
    constructor
    · rintro ⟨⟨j, _, rfl⟩, hle⟩; exact ⟨j, (lt_kappa_iff ht k j).mpr hle, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      have := (lt_kappa_iff ht k j).mp hj
      exact ⟨⟨j, (lt_kappa_iff ht N j).mpr (by omega), rfl⟩, this⟩
  rw [U, this, card_image_of_injective _ ht.injective, card_range]

lemma ones_le {N a : ℕ} (ha : a ∈ ones ht N) : a ≤ N := by
  obtain ⟨j, hj, rfl⟩ := mem_image.mp ha
  exact (lt_kappa_iff ht N j).mp (mem_range.mp hj)

lemma sq_le_four_two_pow (n : ℕ) : n ^ 2 ≤ 4 * 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have := Nat.lt_two_pow_self (n := n)
    rw [pow_succ 2 n]
    nlinarith

/-- **The lower bound** ([Van18, (6), (8)], [Dub19, (28)]): with `A` the positions `≤ N` of the
ones of `√2` and `ℓ = ⌊log₂(N + 1)⌋ + 1`, `2N ≤ V(N) + U(N) + 4ℓ`. -/
@[category research solved, AMS 11, ref "Van18", group "bugeaud_10_47"]
theorem sqrt_two_V_ge (hy : sparseValue 2 t = √2) (N : ℕ) :
    2 * N ≤ V (ones ht N) N + U (ones ht N) N + 4 * (Nat.log 2 (N + 1) + 1) := by
  classical
  set A := ones ht N
  set ℓ := Nat.log 2 (N + 1) + 1
  have hb : 2 ≤ 2 := le_rfl
  have hAle : ∀ a ∈ A, a ≤ N := fun a ha => ones_le ht ha
  have hUA : U A N = A.card := by
    rw [U, filter_true_of_mem (fun a ha => hAle a ha)]
  set e := N + 2 * ℓ
  by_cases he : 2 * N + 1 < e
  · omega
  push Not at he
  obtain ⟨R, hR0, hRle, hX⟩ := sqrt_two_borrow ht hy N
  -- `Y = ∑_{a ∈ A} 2^{N − a}` and `Y² = H + L`
  have hY : ∑ j ∈ range (kappa ht N), 2 ^ (N - t j) = ∑ a ∈ A, 2 ^ (N - a) := by
    rw [show A = (range (kappa ht N)).image t from rfl, sum_image (fun i _ j _ h => ht.injective h)]
  set L := ∑ p ∈ (A ×ˢ A).filter (fun p => ¬ p.1 + p.2 ≤ N), 2 ^ ((N - p.1) + (N - p.2))
  have hsq : (∑ a ∈ A, 2 ^ (N - a)) ^ 2 = H A N + L := by
    rw [sq, sum_mul_sum, ← sum_product', H, sum_filter_add_sum_filter_not]
    exact sum_congr rfl fun p _ => by rw [pow_add]
  rw [hY, hsq] at hX
  -- `L < 2^e`
  have hcardA : A.card ≤ N + 1 := by
    calc A.card ≤ (range (N + 1)).card :=
          card_le_card fun a ha => mem_range.mpr (by have := hAle a ha; omega)
      _ = N + 1 := card_range _
  have hL : L < 2 ^ e := by
    have hterm : ∀ p ∈ (A ×ˢ A).filter (fun p => ¬ p.1 + p.2 ≤ N),
        2 ^ ((N - p.1) + (N - p.2)) ≤ 2 ^ N := by
      intro p hp
      simp only [mem_filter, mem_product] at hp
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hlog : N + 1 < 2 ^ ℓ := Nat.lt_pow_succ_log_self (by norm_num) _
    calc L ≤ ∑ p ∈ (A ×ˢ A).filter (fun p => ¬ p.1 + p.2 ≤ N), 2 ^ N := sum_le_sum hterm
      _ = ((A ×ˢ A).filter (fun p => ¬ p.1 + p.2 ≤ N)).card * 2 ^ N := by
          rw [sum_const, smul_eq_mul]
      _ ≤ (N + 1) ^ 2 * 2 ^ N := by
          refine Nat.mul_le_mul_right _ ((card_filter_le _ _).trans ?_)
          rw [card_product, sq]; exact Nat.mul_le_mul hcardA hcardA
      _ < (2 ^ ℓ) ^ 2 * 2 ^ N :=
          Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_left hlog (by norm_num)) (by positivity)
      _ = 2 ^ e := by rw [← pow_mul, ← pow_add]; congr 1; omega
  -- the top of `Y²` is a block of ones
  set m := 2 * N + 1 - e
  have hRe : R ≤ 2 ^ e := hRle.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hm1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hdivX : (H A N + L) / 2 ^ e = 2 ^ m - 1 := by
    have hpow : 2 ^ (2 * N + 1) = 2 ^ m * 2 ^ e := by rw [← pow_add]; congr 1; omega
    have hXeq : H A N + L = (2 ^ e - R) + (2 ^ m - 1) * 2 ^ e := by
      rw [hpow] at hX
      have : 2 ^ e ≤ 2 ^ m * 2 ^ e := Nat.le_mul_of_pos_left _ (by positivity)
      zify [hRe, hm1, this] at hX ⊢
      linarith
    rw [hXeq, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt (by omega), zero_add]
  have hlow : m ≤ ds 2 ((H A N + L) / 2 ^ e) := by
    rw [hdivX, ds_pow_sub_one hb]; omega
  -- `⌊(H + L)/2^e⌋ = ⌊H/2^e⌋ + c` with `c ≤ 1`
  have hsplitH : H A N = H A N % 2 ^ e + 2 ^ e * (H A N / 2 ^ e) := (Nat.mod_add_div _ _).symm
  have hc : (H A N % 2 ^ e + L) / 2 ^ e ≤ 1 := by
    have := Nat.mod_lt (H A N) (show 0 < 2 ^ e by positivity)
    have : (H A N % 2 ^ e + L) / 2 ^ e < 2 := (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by omega)
    omega
  have hdiv2 : (H A N + L) / 2 ^ e = (H A N % 2 ^ e + L) / 2 ^ e + H A N / 2 ^ e := by
    conv_lhs => rw [hsplitH]
    rw [show H A N % 2 ^ e + 2 ^ e * (H A N / 2 ^ e) + L
        = (H A N % 2 ^ e + L) + 2 ^ e * (H A N / 2 ^ e) by ring,
      Nat.add_mul_div_left _ _ (by positivity)]
  have hup : ds 2 ((H A N + L) / 2 ^ e) ≤ 1 + ds 2 (H A N) := by
    rw [hdiv2]
    refine (ds_add_le hb _ _).trans (Nat.add_le_add ?_ ?_)
    · rw [ds_of_lt hb (by omega)]; exact hc
    · rw [ds_split hb e (H A N)]; omega
  have hpair := two_ds_H_le A N
  omega

end SqrtTwo

/-! ## `√(8/π)` infinitely often -/

/-- **`√(8/π)` ones infinitely often** ([Dub19, Thm. 3 (6)] for `d = 2`; announced in
[Van18, Rem. 7.1]).  For every `ω < √(8/π) ≈ 1.5958` there are infinitely many `N` such that
more than `ω√N` of the binary digits of `√2` at positions `0, …, N` are ones.  This improves
[Van18, Thm. 1.2] (`2/√(2√2 − 1) ≈ 1.4791`). -/
@[category research solved, AMS 11, ref "Dub19", group "bugeaud_10_47"]
theorem sqrt_two_ones_io {t : ℕ → ℕ} (ht : StrictMono t) (hy : sparseValue 2 t = √2)
    {ω : ℝ} (hω : ω < √(8 / π)) (N₀ : ℕ) :
    ∃ N ≥ N₀, ω * √(N : ℝ) < kappa ht N := by
  by_contra hcon
  push Not at hcon
  set W := max ω 0
  have hW0 : 0 ≤ W := le_max_right _ _
  have hWlt : W < √(8 / π) := max_lt hω (Real.sqrt_pos.mpr (by positivity))
  have hW2 : W ^ 2 < 8 / π := (Real.lt_sqrt hW0).mp hWlt
  have hcon' : ∀ N ≥ N₀, (kappa ht N : ℝ) ≤ W * √(N : ℝ) := fun N hN =>
    (hcon N hN).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
  set δ := 2 - π / 4 * W ^ 2
  have hδ : 0 < δ := by
    have : π / 4 * W ^ 2 < π / 4 * (8 / π) := mul_lt_mul_of_pos_left hW2 (by positivity)
    rw [show π / 4 * (8 / π) = 2 by field_simp; ring] at this
    simp only [δ]; linarith
  set C : ℝ := (kappa ht N₀ : ℝ)
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have hUk : ∀ k : ℕ, (kappa ht k : ℝ) ≤ W * √(k : ℝ) + C := by
    intro k
    have hWk : 0 ≤ W * √(k : ℝ) := by positivity
    rcases le_total k N₀ with hk | hk
    · have : (kappa ht k : ℝ) ≤ C := by simp only [C]; exact_mod_cast kappa_mono ht hk
      linarith
    · linarith [hcon' k hk]
  set M := 2 * W * C + W + C ^ 2 + C + 12
  have hM : 0 ≤ M := by positivity
  -- the two bounds at a single large `N`
  have key : ∀ N : ℕ, δ * ((N : ℝ) + 1) ≤ (M + δ) * √((N : ℝ) + 1) := by
    intro N
    set s := √((N : ℝ) + 1)
    have hs1 : 1 ≤ s := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
    have hsN : √(N : ℝ) ≤ s := Real.sqrt_le_sqrt (by linarith)
    have hs2 : s ^ 2 = (N : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have hVle := V_le (ones ht N) hW0 hC N (fun k hk => by rw [U_ones ht hk]; exact hUk k)
    have hVge : (2 * N : ℝ) ≤ V (ones ht N) N + U (ones ht N) N
        + 4 * ((Nat.log 2 (N + 1) : ℝ) + 1) := by exact_mod_cast sqrt_two_V_ge ht hy N
    rw [U_ones ht le_rfl] at hVge
    -- `ℓ ≤ 3 s`
    have hℓ : (Nat.log 2 (N + 1) : ℝ) + 1 ≤ 3 * s := by
      have h1 := sq_le_four_two_pow (Nat.log 2 (N + 1) + 1)
      have h2 : 2 ^ (Nat.log 2 (N + 1) + 1) ≤ 2 * (N + 1) := by
        rw [pow_succ, mul_comm]
        exact Nat.mul_le_mul_left _ (Nat.pow_log_le_self 2 (by omega))
      have h3 : ((Nat.log 2 (N + 1) : ℝ) + 1) ^ 2 ≤ 8 * ((N : ℝ) + 1) := by
        have : (Nat.log 2 (N + 1) + 1) ^ 2 ≤ 8 * (N + 1) := by omega
        exact_mod_cast this
      nlinarith
    have hUN := hUk N
    have hWs : W * √(N : ℝ) ≤ W * s := mul_le_mul_of_nonneg_left hsN hW0
    have hWCs : 2 * W * C * √(N : ℝ) ≤ 2 * W * C * s :=
      mul_le_mul_of_nonneg_left hsN (by positivity)
    have : δ * N ≤ M * s := by
      simp only [δ, M]
      nlinarith
    nlinarith
  obtain ⟨n, hn⟩ := exists_nat_gt (((M + δ) / δ) ^ 2)
  set N := max N₀ n
  have hk := key N
  set s := √((N : ℝ) + 1)
  have hs2 : s ^ 2 = (N : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have hspos : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs_le : s ≤ (M + δ) / δ := by
    rw [le_div_iff₀ hδ]
    have : δ * s ^ 2 ≤ (M + δ) * s := by rw [hs2]; exact hk
    nlinarith
  have hNn : ((M + δ) / δ) ^ 2 < (N : ℝ) + 1 := by
    have : (n : ℝ) ≤ N := by exact_mod_cast le_max_right N₀ n
    linarith
  have : (M + δ) / δ < s := by
    rw [Real.lt_sqrt (by positivity)]; exact hNn
  linarith

end BB47.RestrictedSumset
