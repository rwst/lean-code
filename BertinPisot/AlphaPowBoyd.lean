/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/

import ForMathlib.Data.Real.NearestInt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Data.Set.Countable
import Mathlib.Order.Interval.Set.Basic
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Boyd's Theorem 1 — uncountably many reals with badly distributed powers

David W. Boyd, *Transcendental numbers with badly distributed powers* ([Boy69]), Theorem 1: the
**sharpness counterpart** to Pisot's theorem (Bertin's Theorem 5.1.1).

Given real `3 < α < β` and an integer `a₀ > (α+1)(α-1)⁻¹(β-α)⁻¹`, there is an *uncountable* set
`S ⊆ [α, β]` such that every `θ ∈ S` has a real `λ = λ(θ) > 0` with `‖λθⁿ‖ ≤ (α-1)⁻¹(θ-1)⁻¹` for all
`n`, and `a₀` is the nearest integer to `λ(θ)`. Since the algebraic numbers are countable, `S`
contains (uncountably many) transcendental `θ`; so the bound in Pisot's theorem (Bertin Thm 5.1.1)
cannot be weakened to one of order `(2eθ(θ+1)(1+log λ))⁻¹` while still forcing `θ` to be algebraic.

The proof is Boyd's explicit Cantor-type construction: for each `f : ℕ → Bool`, build a positive
integer sequence `Aₙ(f)` with `Aₙ₊₂ = ⌊Aₙ₊₁²/Aₙ⌋ + f(n)`; the ratios `rₙ = Aₙ₊₁/Aₙ` stay in `(α,β)`
and converge to `θ(f)`; distinct `f` give distinct `θ` (uncountability), and `λ = lim Aₙθ⁻ⁿ > 0`
yields the bound. Formalized here in full (no `sorry`, no extra axioms).

*References:*
  - [Boy69] Boyd, David W. "Transcendental numbers with badly distributed powers."
    *Proc. Amer. Math. Soc.* 23 (1969), 424–427. (MR0248094.) Theorem 1.
  - [Ber92] Bertin, Marie José et al. *Pisot and Salem Numbers.* Birkhäuser, 1992. §5.1.
-/

open Filter Topology

namespace Bertin.AlphaPow.Boyd

/-! ### Geometric / telescoping helpers (independent of the construction) -/

/-- `∑_{j<N} (α⁻¹)^(j+1) ≤ (α-1)⁻¹`. -/
lemma geo_tail (α : ℝ) (hα : 3 < α) (N : ℕ) :
    ∑ j ∈ Finset.range N, (α⁻¹ : ℝ) ^ (j + 1) ≤ (α - 1)⁻¹ := by
  have hαpos : (0 : ℝ) < α := by linarith
  have hαlt : α⁻¹ < 1 := by rw [inv_lt_one₀ hαpos]; linarith
  have hsum : Summable (fun k => (α⁻¹ : ℝ) ^ (k + 1)) := by
    simpa [pow_succ'] using (summable_geometric_of_lt_one (by positivity) hαlt).mul_left α⁻¹
  calc ∑ j ∈ Finset.range N, (α⁻¹ : ℝ) ^ (j + 1)
      ≤ ∑' k, (α⁻¹ : ℝ) ^ (k + 1) := hsum.sum_le_tsum _ (fun k _ => by positivity)
    _ = (α - 1)⁻¹ := by
        simp_rw [pow_succ']; rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hαlt]
        field_simp

/-- Abstract tail bound: for a sequence `R → θ` with per-step bound `|R(k+1)−R k| ≤ Ar(k+1)⁻¹` and
relative growth `αʲ·Ar n ≤ Ar(n+j)`, one has `|θ − R n| ≤ Ar n⁻¹ (α-1)⁻¹`. -/
lemma tail_bound (α θ : ℝ) (hα : 3 < α) (Ar R : ℕ → ℝ) (hArpos : ∀ k, 0 < Ar k)
    (hstep : ∀ k, |R (k + 1) - R k| ≤ (Ar (k + 1))⁻¹)
    (hgrowrel : ∀ n j, α ^ j * Ar n ≤ Ar (n + j))
    (htend : Tendsto R atTop (𝓝 θ)) (n : ℕ) : |θ - R n| ≤ (Ar n)⁻¹ * (α - 1)⁻¹ := by
  have hαpos : (0 : ℝ) < α := by linarith
  have hrel : ∀ m, n ≤ m → |R m - R n| ≤ (Ar n)⁻¹ * (α - 1)⁻¹ := by
    intro m hm
    have htel : R m - R n = ∑ j ∈ Finset.range (m - n), (R (n + (j + 1)) - R (n + j)) := by
      have h := Finset.sum_range_sub (fun j => R (n + j)) (m - n)
      rw [Nat.add_sub_cancel' hm, Nat.add_zero] at h
      exact h.symm
    rw [htel]
    calc |∑ j ∈ Finset.range (m - n), (R (n + (j + 1)) - R (n + j))|
        ≤ ∑ j ∈ Finset.range (m - n), |R (n + (j + 1)) - R (n + j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range (m - n), (Ar n)⁻¹ * (α⁻¹) ^ (j + 1) := by
          apply Finset.sum_le_sum
          intro j _
          have h1 : |R (n + (j + 1)) - R (n + j)| ≤ (Ar (n + (j + 1)))⁻¹ := hstep (n + j)
          have h2 : (Ar (n + (j + 1)))⁻¹ ≤ (Ar n)⁻¹ * (α⁻¹) ^ (j + 1) := by
            have hg : α ^ (j + 1) * Ar n ≤ Ar (n + (j + 1)) := hgrowrel n (j + 1)
            have hp : (0 : ℝ) < α ^ (j + 1) * Ar n := mul_pos (pow_pos hαpos (j + 1)) (hArpos n)
            have hh : (1 : ℝ) / Ar (n + (j + 1)) ≤ 1 / (α ^ (j + 1) * Ar n) :=
              one_div_le_one_div_of_le hp hg
            rwa [one_div, one_div, mul_inv, ← inv_pow, mul_comm] at hh
          linarith
      _ ≤ (Ar n)⁻¹ * (α - 1)⁻¹ := by
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left (geo_tail α hα _) (inv_nonneg.mpr (hArpos n).le)
  have htendabs : Tendsto (fun m => |R m - R n|) atTop (𝓝 |θ - R n|) :=
    (htend.sub_const (R n)).abs
  exact le_of_tendsto htendabs (eventually_atTop.mpr ⟨n, hrel⟩)

/-- `round x = k` when `x` is within `1/2` of the integer `k`. -/
lemma round_eq_of_abs_lt (x : ℝ) (k : ℤ) (h : |x - (k : ℝ)| < 1 / 2) : round x = k := by
  rw [abs_lt] at h
  rw [round_eq, Int.floor_eq_iff]
  constructor <;> linarith

/-- `(α-1)⁻¹(θ-1)⁻¹ < 1/4` for `α, θ > 3`. -/
lemma quarter_bound (α θ : ℝ) (hα : 3 < α) (hθ : 3 < θ) : (α - 1)⁻¹ * (θ - 1)⁻¹ < 1 / 4 := by
  rw [← mul_inv, inv_lt_comm₀ (by nlinarith) (by norm_num)]
  nlinarith

/-! ### The construction -/

/-- `{0,1}`-valued perturbation. -/
def boolToInt (b : Bool) : ℤ := if b then 1 else 0

variable (α : ℝ) (a₀ : ℤ)

/-- The starting integer `a₁`: the smallest integer `> a₀α + (α-1)⁻¹`. -/
noncomputable def a1 : ℤ := ⌊(a₀ : ℝ) * α + (α - 1)⁻¹⌋ + 1

/-- The pair `(Aₙ, Aₙ₊₁)` of the Boyd sequence; `Aₙ₊₂ = ⌊Aₙ₊₁²/Aₙ⌋ + f(n)`. -/
noncomputable def Apair (f : ℕ → Bool) : ℕ → ℤ × ℤ
  | 0 => (a₀, a1 α a₀)
  | (n + 1) => ((Apair f n).2, (Apair f n).2 ^ 2 / (Apair f n).1 + boolToInt (f n))

/-- The Boyd integer sequence `Aₙ(f)`. -/
noncomputable def A (f : ℕ → Bool) (n : ℕ) : ℤ := (Apair α a₀ f n).1

/-- The ratio `rₙ = Aₙ₊₁/Aₙ` (real). -/
noncomputable def r (f : ℕ → Bool) (n : ℕ) : ℝ := (A α a₀ f (n + 1) : ℝ) / (A α a₀ f n : ℝ)

variable (f : ℕ → Bool)

lemma A_succ_aux (n : ℕ) : A α a₀ f (n + 1) = (Apair α a₀ f n).2 := rfl

/-- The defining recursion. -/
lemma A_rec (n : ℕ) :
    A α a₀ f (n + 2) = (A α a₀ f (n + 1)) ^ 2 / (A α a₀ f n) + boolToInt (f n) := by
  show (Apair α a₀ f (n + 2)).1 = _
  rw [A_succ_aux]; rfl

lemma A_succ_eq (n : ℕ) (hn : 0 < A α a₀ f n) :
    (A α a₀ f (n + 1) : ℝ) = r α a₀ f n * (A α a₀ f n : ℝ) := by
  rw [r]; field_simp

/-- Estimate (6): `|rₙ₊₁ − rₙ| ≤ Aₙ₊₁⁻¹`. -/
lemma step6 (n : ℕ) (hn : 0 < A α a₀ f n) (hn1 : 0 < A α a₀ f (n + 1)) :
    |r α a₀ f (n + 1) - r α a₀ f n| ≤ ((A α a₀ f (n + 1) : ℝ))⁻¹ := by
  have hrec : A α a₀ f (n + 2) = (A α a₀ f (n + 1)) ^ 2 / (A α a₀ f n) + boolToInt (f n) :=
    A_rec α a₀ f n
  have hqs : (A α a₀ f (n + 1)) ^ 2 % A α a₀ f n
        + A α a₀ f n * ((A α a₀ f (n + 1)) ^ 2 / A α a₀ f n) = (A α a₀ f (n + 1)) ^ 2 :=
    Int.emod_add_mul_ediv _ _
  have hb : boolToInt (f n) = 0 ∨ boolToInt (f n) = 1 := by unfold boolToInt; split <;> simp
  have hs0 : 0 ≤ (A α a₀ f (n + 1)) ^ 2 % A α a₀ f n := Int.emod_nonneg _ (by omega)
  have hs1 : (A α a₀ f (n + 1)) ^ 2 % A α a₀ f n < A α a₀ f n := Int.emod_lt_of_pos _ hn
  have hDabs : |A α a₀ f (n + 2) * A α a₀ f n - (A α a₀ f (n + 1)) ^ 2| ≤ A α a₀ f n := by
    rw [hrec, abs_le]
    refine ⟨?_, ?_⟩ <;> rcases hb with h | h <;> rw [h] <;> nlinarith [hqs, hs0, hs1]
  have hAnR : (0 : ℝ) < (A α a₀ f n : ℝ) := by exact_mod_cast hn
  have hAn1R : (0 : ℝ) < (A α a₀ f (n + 1) : ℝ) := by exact_mod_cast hn1
  have hdiff : r α a₀ f (n + 1) - r α a₀ f n
      = ((A α a₀ f (n + 2) * A α a₀ f n - (A α a₀ f (n + 1)) ^ 2 : ℤ) : ℝ)
        / ((A α a₀ f (n + 1) : ℝ) * (A α a₀ f n : ℝ)) := by
    simp only [r]
    rw [show n + 1 + 1 = n + 2 from rfl]
    have h1 := hAn1R.ne'; have h2 := hAnR.ne'
    push_cast; field_simp
  rw [hdiff, abs_div,
    abs_of_pos (show (0 : ℝ) < (A α a₀ f (n + 1) : ℝ) * (A α a₀ f n : ℝ) by positivity),
    div_le_iff₀ (show (0 : ℝ) < (A α a₀ f (n + 1) : ℝ) * (A α a₀ f n : ℝ) by positivity),
    inv_mul_cancel_left₀ hAn1R.ne']
  rw [← Int.cast_abs]; exact_mod_cast hDabs

/-! ### Positivity, growth, and the ratio invariant -/

variable (β : ℝ)

lemma a0_pos (hα : 3 < α) (hαβ : α < β)
    (ha₀ : (α + 1) * (α - 1)⁻¹ * (β - α)⁻¹ < (a₀ : ℝ)) : 0 < a₀ := by
  have h1 : (0 : ℝ) < (α + 1) * (α - 1)⁻¹ * (β - α)⁻¹ := by
    have : 0 < α - 1 := by linarith
    have : 0 < β - α := by linarith
    positivity
  have : (0 : ℝ) < (a₀ : ℝ) := lt_trans h1 ha₀
  exact_mod_cast this

/-- The bound (4) on `a₁`. -/
lemma a1_bounds (hα : 3 < α) (hαβ : α < β)
    (ha₀ : (α + 1) * (α - 1)⁻¹ * (β - α)⁻¹ < (a₀ : ℝ)) :
    (a₀ : ℝ) * α + (α - 1)⁻¹ < (a1 α a₀ : ℝ) ∧ (a1 α a₀ : ℝ) < (a₀ : ℝ) * β - (α - 1)⁻¹ := by
  have hα1 : (0 : ℝ) < α - 1 := by linarith
  have hβα : (0 : ℝ) < β - α := by linarith
  have hkey : (α + 1) * (α - 1)⁻¹ < (a₀ : ℝ) * (β - α) := by
    have h := mul_lt_mul_of_pos_right ha₀ hβα
    rwa [mul_assoc, inv_mul_cancel₀ hβα.ne', mul_one] at h
  have he : (α + 1) * (α - 1)⁻¹ = 1 + 2 * (α - 1)⁻¹ := by field_simp; ring
  have hgap : 1 < (a₀ : ℝ) * (β - α) - 2 * (α - 1)⁻¹ := by linarith [hkey, he]
  set x := (a₀ : ℝ) * α + (α - 1)⁻¹ with hx
  have hcast : (a1 α a₀ : ℝ) = (⌊x⌋ : ℝ) + 1 := by simp only [a1]; rw [← hx]; push_cast; ring
  refine ⟨?_, ?_⟩
  · rw [hcast]; have := Int.lt_floor_add_one x; linarith
  · rw [hcast]
    have h1 := Int.floor_le x
    have h2 : x + 1 < (a₀ : ℝ) * β - (α - 1)⁻¹ := by rw [hx]; nlinarith [hgap]
    linarith

lemma hApos (hα : 3 < α) (ha0 : 0 < a₀) :
    ∀ n, (∀ k, k < n → α < r α a₀ f k) → 0 < A α a₀ f n := by
  intro n
  induction n with
  | zero => intro _; exact ha0
  | succ m ih =>
    intro h
    have hm : 0 < A α a₀ f m := ih (fun k hk => h k (by omega))
    have hrm : α < r α a₀ f m := h m (by omega)
    have hmR : (0 : ℝ) < (A α a₀ f m : ℝ) := by exact_mod_cast hm
    have : (0 : ℝ) < (A α a₀ f (m + 1) : ℝ) := by
      rw [A_succ_eq α a₀ f m hm]; nlinarith [hrm, hmR]
    exact_mod_cast this

lemma hgrow (hα : 3 < α) (ha0 : 0 < a₀) :
    ∀ n, (∀ k, k < n → α < r α a₀ f k) → (a₀ : ℝ) * α ^ n ≤ (A α a₀ f n : ℝ) := by
  intro n
  induction n with
  | zero => intro _; simp [A, Apair]
  | succ m ih =>
    intro h
    have hbelow : ∀ k, k < m → α < r α a₀ f k := fun k hk => h k (by omega)
    have hm : 0 < A α a₀ f m := hApos α a₀ f hα ha0 m hbelow
    have hmR : (0 : ℝ) < (A α a₀ f m : ℝ) := by exact_mod_cast hm
    have hgm : (a₀ : ℝ) * α ^ m ≤ (A α a₀ f m : ℝ) := ih hbelow
    have hrm : α < r α a₀ f m := h m (by omega)
    rw [A_succ_eq α a₀ f m hm, pow_succ]
    calc (a₀ : ℝ) * (α ^ m * α) = α * ((a₀ : ℝ) * α ^ m) := by ring
      _ ≤ α * (A α a₀ f m : ℝ) := by apply mul_le_mul_of_nonneg_left hgm (by linarith)
      _ ≤ r α a₀ f m * (A α a₀ f m : ℝ) := by
          apply mul_le_mul_of_nonneg_right (le_of_lt hrm) hmR.le

/-- The telescoping/geometric bound: `|rₙ − r₀| ≤ a₀⁻¹(α-1)⁻¹`, under the ratios-exceed-α hypothesis. -/
lemma htele (hα : 3 < α) (ha0 : 0 < a₀) (n : ℕ) (h : ∀ k, k < n → α < r α a₀ f k) :
    |r α a₀ f n - r α a₀ f 0| ≤ (a₀ : ℝ)⁻¹ * (α - 1)⁻¹ := by
  have hαpos : (0 : ℝ) < α := by linarith
  have hbound : ∀ k, k < n → |r α a₀ f (k + 1) - r α a₀ f k| ≤ (a₀ : ℝ)⁻¹ * (α⁻¹) ^ (k + 1) := by
    intro k hk
    have hbk : ∀ j, j < k → α < r α a₀ f j := fun j hj => h j (by omega)
    have hbk1 : ∀ j, j < k + 1 → α < r α a₀ f j := fun j hj => h j (by omega)
    have hAk : 0 < A α a₀ f k := hApos α a₀ f hα ha0 k hbk
    have hAk1 : 0 < A α a₀ f (k + 1) := hApos α a₀ f hα ha0 (k + 1) hbk1
    have hs6 := step6 α a₀ f k hAk hAk1
    have hgk1 : (a₀ : ℝ) * α ^ (k + 1) ≤ (A α a₀ f (k + 1) : ℝ) := hgrow α a₀ f hα ha0 (k + 1) hbk1
    have hpos : (0 : ℝ) < (a₀ : ℝ) * α ^ (k + 1) := by
      have : (0 : ℝ) < (a₀ : ℝ) := by exact_mod_cast ha0
      positivity
    have hinv : (A α a₀ f (k + 1) : ℝ)⁻¹ ≤ (a₀ : ℝ)⁻¹ * (α⁻¹) ^ (k + 1) := by
      have h1 : (1 : ℝ) / (A α a₀ f (k + 1) : ℝ) ≤ 1 / ((a₀ : ℝ) * α ^ (k + 1)) :=
        one_div_le_one_div_of_le hpos hgk1
      rwa [one_div, one_div, mul_inv, ← inv_pow] at h1
    linarith [hs6, hinv]
  have htel : r α a₀ f n - r α a₀ f 0 = ∑ k ∈ Finset.range n, (r α a₀ f (k + 1) - r α a₀ f k) :=
    (Finset.sum_range_sub (r α a₀ f) n).symm
  rw [htel]
  have hαlt : α⁻¹ < 1 := by rw [inv_lt_one₀ hαpos]; linarith
  calc |∑ k ∈ Finset.range n, (r α a₀ f (k + 1) - r α a₀ f k)|
      ≤ ∑ k ∈ Finset.range n, |r α a₀ f (k + 1) - r α a₀ f k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range n, (a₀ : ℝ)⁻¹ * (α⁻¹) ^ (k + 1) :=
        Finset.sum_le_sum (fun k hk => hbound k (Finset.mem_range.mp hk))
    _ ≤ (a₀ : ℝ)⁻¹ * (α - 1)⁻¹ := by
        rw [← Finset.mul_sum]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hsum : Summable (fun k => (α⁻¹ : ℝ) ^ (k + 1)) := by
          simpa [pow_succ'] using (summable_geometric_of_lt_one (by positivity) hαlt).mul_left α⁻¹
        calc ∑ k ∈ Finset.range n, (α⁻¹ : ℝ) ^ (k + 1)
            ≤ ∑' k, (α⁻¹ : ℝ) ^ (k + 1) := hsum.sum_le_tsum _ (fun k _ => by positivity)
          _ = (α - 1)⁻¹ := by
              simp_rw [pow_succ']
              rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hαlt]
              field_simp

/-- The **ratio invariant**: every `rₙ` stays in `(α, β)`. -/
lemma hr (hα : 3 < α) (hαβ : α < β)
    (ha₀ : (α + 1) * (α - 1)⁻¹ * (β - α)⁻¹ < (a₀ : ℝ)) :
    ∀ n, α < r α a₀ f n ∧ r α a₀ f n < β := by
  have ha0 : 0 < a₀ := a0_pos α a₀ β hα hαβ ha₀
  have ha0R : (0 : ℝ) < (a₀ : ℝ) := by exact_mod_cast ha0
  have hab := a1_bounds α a₀ β hα hαβ ha₀
  have hr0eq : r α a₀ f 0 = (a1 α a₀ : ℝ) / (a₀ : ℝ) := by simp [r, A, Apair]
  have h0lo : α + (a₀ : ℝ)⁻¹ * (α - 1)⁻¹ < r α a₀ f 0 := by
    rw [hr0eq, lt_div_iff₀ ha0R]
    have he : (α + (a₀ : ℝ)⁻¹ * (α - 1)⁻¹) * (a₀ : ℝ) = (a₀ : ℝ) * α + (α - 1)⁻¹ := by
      field_simp
    rw [he]; exact hab.1
  have h0hi : r α a₀ f 0 < β - (a₀ : ℝ)⁻¹ * (α - 1)⁻¹ := by
    rw [hr0eq, div_lt_iff₀ ha0R]
    have he : (β - (a₀ : ℝ)⁻¹ * (α - 1)⁻¹) * (a₀ : ℝ) = (a₀ : ℝ) * β - (α - 1)⁻¹ := by
      field_simp
    rw [he]; exact hab.2
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hbelow : ∀ k, k < n → α < r α a₀ f k := fun k hk => (ih k hk).1
    have ht := htele α a₀ f hα ha0 n hbelow
    rw [abs_le] at ht
    exact ⟨by linarith [ht.1, h0lo], by linarith [ht.2, h0hi]⟩

/-! ### The limit `θ(f)` -/

/-- Per-step geometric bound on the ratios (global version, via the ratio invariant). -/
lemma hstep_bound (hα : 3 < α) (hαβ : α < β)
    (ha₀ : (α + 1) * (α - 1)⁻¹ * (β - α)⁻¹ < (a₀ : ℝ)) (n : ℕ) :
    |r α a₀ f (n + 1) - r α a₀ f n| ≤ (a₀ : ℝ)⁻¹ * (α⁻¹) ^ (n + 1) := by
  have ha0 : 0 < a₀ := a0_pos α a₀ β hα hαβ ha₀
  have hrall : ∀ k, α < r α a₀ f k := fun k => (hr α a₀ f β hα hαβ ha₀ k).1
  have hAk : 0 < A α a₀ f n := hApos α a₀ f hα ha0 n (fun k _ => hrall k)
  have hAk1 : 0 < A α a₀ f (n + 1) := hApos α a₀ f hα ha0 (n + 1) (fun k _ => hrall k)
  have hs6 := step6 α a₀ f n hAk hAk1
  have hgk1 : (a₀ : ℝ) * α ^ (n + 1) ≤ (A α a₀ f (n + 1) : ℝ) :=
    hgrow α a₀ f hα ha0 (n + 1) (fun k _ => hrall k)
  have hpos : (0 : ℝ) < (a₀ : ℝ) * α ^ (n + 1) := by
    have h0 : (0 : ℝ) < (a₀ : ℝ) := by exact_mod_cast ha0
    have : (0 : ℝ) < α := by linarith
    positivity
  have hinv : (A α a₀ f (n + 1) : ℝ)⁻¹ ≤ (a₀ : ℝ)⁻¹ * (α⁻¹) ^ (n + 1) := by
    have h1 : (1 : ℝ) / (A α a₀ f (n + 1) : ℝ) ≤ 1 / ((a₀ : ℝ) * α ^ (n + 1)) :=
      one_div_le_one_div_of_le hpos hgk1
    rwa [one_div, one_div, mul_inv, ← inv_pow] at h1
  linarith [hs6, hinv]

/-- `θ(f)`: the limit of the ratios `rₙ`. -/
noncomputable def θ : ℝ := atTop.limUnder (r α a₀ f)

lemma hcauchy (hα : 3 < α) (hαβ : α < β)
    (ha₀ : (α + 1) * (α - 1)⁻¹ * (β - α)⁻¹ < (a₀ : ℝ)) : CauchySeq (r α a₀ f) := by
  have ha0 : 0 < a₀ := a0_pos α a₀ β hα hαβ ha₀
  have hαlt : α⁻¹ < 1 := by rw [inv_lt_one₀ (by linarith)]; linarith
  apply cauchySeq_of_le_geometric α⁻¹ ((a₀ : ℝ)⁻¹ * α⁻¹) hαlt
  intro n
  rw [Real.dist_eq, abs_sub_comm]
  calc |r α a₀ f (n + 1) - r α a₀ f n| ≤ (a₀ : ℝ)⁻¹ * (α⁻¹) ^ (n + 1) :=
        hstep_bound α a₀ f β hα hαβ ha₀ n
    _ = (a₀ : ℝ)⁻¹ * α⁻¹ * (α⁻¹) ^ n := by rw [pow_succ']; ring

lemma htendsto (hα : 3 < α) (hαβ : α < β)
    (ha₀ : (α + 1) * (α - 1)⁻¹ * (β - α)⁻¹ < (a₀ : ℝ)) :
    Tendsto (r α a₀ f) atTop (𝓝 (θ α a₀ f)) :=
  (hcauchy α a₀ f β hα hαβ ha₀).tendsto_limUnder

/-- `θ(f) ∈ [α, β]`. -/
lemma hθ_mem (hα : 3 < α) (hαβ : α < β)
    (ha₀ : (α + 1) * (α - 1)⁻¹ * (β - α)⁻¹ < (a₀ : ℝ)) :
    α ≤ θ α a₀ f ∧ θ α a₀ f ≤ β := by
  have ht := htendsto α a₀ f β hα hαβ ha₀
  refine ⟨ge_of_tendsto ht (.of_forall (fun n => (hr α a₀ f β hα hαβ ha₀ n).1.le)),
    le_of_tendsto ht (.of_forall (fun n => (hr α a₀ f β hα hαβ ha₀ n).2.le))⟩

/-- Relative growth `αʲ Aₙ ≤ Aₙ₊ⱼ`. -/
lemma hgrow_rel (hα : 3 < α) (hαβ : α < β)
    (ha₀ : (α + 1) * (α - 1)⁻¹ * (β - α)⁻¹ < (a₀ : ℝ)) (n j : ℕ) :
    (α : ℝ) ^ j * (A α a₀ f n : ℝ) ≤ (A α a₀ f (n + j) : ℝ) := by
  have ha0 : 0 < a₀ := a0_pos α a₀ β hα hαβ ha₀
  have hrall : ∀ k, α < r α a₀ f k := fun k => (hr α a₀ f β hα hαβ ha₀ k).1
  induction j with
  | zero => simp
  | succ i ih =>
    have hpos : 0 < A α a₀ f (n + i) := hApos α a₀ f hα ha0 (n + i) (fun k _ => hrall k)
    have hposR : (0 : ℝ) < (A α a₀ f (n + i) : ℝ) := by exact_mod_cast hpos
    rw [show n + (i + 1) = (n + i) + 1 from by ring, A_succ_eq α a₀ f (n + i) hpos, pow_succ]
    calc (α : ℝ) ^ i * α * (A α a₀ f n : ℝ) = α * ((α : ℝ) ^ i * (A α a₀ f n : ℝ)) := by ring
      _ ≤ α * (A α a₀ f (n + i) : ℝ) := by apply mul_le_mul_of_nonneg_left ih (by linarith)
      _ ≤ r α a₀ f (n + i) * (A α a₀ f (n + i) : ℝ) :=
          mul_le_mul_of_nonneg_right (hrall (n + i)).le hposR.le

/-- The tail bound (14): `|θ − rₙ| ≤ Aₙ⁻¹(α-1)⁻¹`. -/
lemma htail (hα : 3 < α) (hαβ : α < β)
    (ha₀ : (α + 1) * (α - 1)⁻¹ * (β - α)⁻¹ < (a₀ : ℝ)) (n : ℕ) :
    |θ α a₀ f - r α a₀ f n| ≤ (A α a₀ f n : ℝ)⁻¹ * (α - 1)⁻¹ := by
  have ha0 : 0 < a₀ := a0_pos α a₀ β hα hαβ ha₀
  have hrall : ∀ k, α < r α a₀ f k := fun k => (hr α a₀ f β hα hαβ ha₀ k).1
  exact tail_bound α (θ α a₀ f) hα (fun k => (A α a₀ f k : ℝ)) (r α a₀ f)
    (fun k => by exact_mod_cast hApos α a₀ f hα ha0 k (fun j _ => hrall j))
    (fun k => step6 α a₀ f k (hApos α a₀ f hα ha0 k (fun j _ => hrall j))
      (hApos α a₀ f hα ha0 (k + 1) (fun j _ => hrall j)))
    (fun m j => hgrow_rel α a₀ f β hα hαβ ha₀ m j) (htendsto α a₀ f β hα hαβ ha₀) n

/-! ### The multiplier `λ(f)` -/

lemma hθ3 (hα : 3 < α) (hαβ : α < β)
    (ha₀ : (α + 1) * (α - 1)⁻¹ * (β - α)⁻¹ < (a₀ : ℝ)) : 3 < θ α a₀ f :=
  lt_of_lt_of_le hα (hθ_mem α a₀ f β hα hαβ ha₀).1

/-- `λ(f)`: the limit of `Aₙ/θⁿ`. -/
noncomputable def lam : ℝ := atTop.limUnder (fun n => (A α a₀ f n : ℝ) / (θ α a₀ f) ^ n)

/-- The per-step bound on `bₙ = Aₙ/θⁿ`. -/
lemma hb_step (hα : 3 < α) (hαβ : α < β)
    (ha₀ : (α + 1) * (α - 1)⁻¹ * (β - α)⁻¹ < (a₀ : ℝ)) (n : ℕ) :
    |(A α a₀ f (n + 1) : ℝ) / (θ α a₀ f) ^ (n + 1) - (A α a₀ f n : ℝ) / (θ α a₀ f) ^ n|
      ≤ ((α - 1) * (θ α a₀ f) ^ (n + 1))⁻¹ := by
  have ha0 : 0 < a₀ := a0_pos α a₀ β hα hαβ ha₀
  have hrall : ∀ k, α < r α a₀ f k := fun k => (hr α a₀ f β hα hαβ ha₀ k).1
  have hApn : 0 < A α a₀ f n := hApos α a₀ f hα ha0 n (fun j _ => hrall j)
  have hApnR : (0 : ℝ) < (A α a₀ f n : ℝ) := by exact_mod_cast hApn
  have hθ : 3 < θ α a₀ f := hθ3 α a₀ f β hα hαβ ha₀
  have hθpos : 0 < θ α a₀ f := by linarith
  have hθn : (0 : ℝ) < (θ α a₀ f) ^ (n + 1) := by positivity
  have hAsucc : (A α a₀ f (n + 1) : ℝ) = r α a₀ f n * (A α a₀ f n : ℝ) := A_succ_eq α a₀ f n hApn
  have hdiff : (A α a₀ f (n + 1) : ℝ) / (θ α a₀ f) ^ (n + 1) - (A α a₀ f n : ℝ) / (θ α a₀ f) ^ n
      = (A α a₀ f n : ℝ) * (r α a₀ f n - θ α a₀ f) / (θ α a₀ f) ^ (n + 1) := by
    rw [hAsucc, pow_succ]; field_simp
  rw [hdiff, abs_div, abs_of_pos hθn, div_le_iff₀ hθn]
  have heq : ((α - 1) * (θ α a₀ f) ^ (n + 1))⁻¹ * (θ α a₀ f) ^ (n + 1) = (α - 1)⁻¹ := by
    rw [mul_inv, mul_assoc, inv_mul_cancel₀ hθn.ne', mul_one]
  rw [heq, abs_mul, abs_of_pos hApnR]
  have h := htail α a₀ f β hα hαβ ha₀ n
  rw [abs_sub_comm] at h
  calc (A α a₀ f n : ℝ) * |r α a₀ f n - θ α a₀ f|
      ≤ (A α a₀ f n : ℝ) * ((A α a₀ f n : ℝ)⁻¹ * (α - 1)⁻¹) := mul_le_mul_of_nonneg_left h hApnR.le
    _ = (α - 1)⁻¹ := mul_inv_cancel_left₀ hApnR.ne' _

lemma hcauchy_b (hα : 3 < α) (hαβ : α < β)
    (ha₀ : (α + 1) * (α - 1)⁻¹ * (β - α)⁻¹ < (a₀ : ℝ)) :
    CauchySeq (fun n => (A α a₀ f n : ℝ) / (θ α a₀ f) ^ n) := by
  have hθ : 3 < θ α a₀ f := hθ3 α a₀ f β hα hαβ ha₀
  have hθpos : 0 < θ α a₀ f := by linarith
  have hθinvlt : (θ α a₀ f)⁻¹ < 1 := by rw [inv_lt_one₀ hθpos]; linarith
  apply cauchySeq_of_le_geometric (θ α a₀ f)⁻¹ ((α - 1)⁻¹ * (θ α a₀ f)⁻¹) hθinvlt
  intro n
  rw [Real.dist_eq]
  calc |(A α a₀ f n : ℝ) / (θ α a₀ f) ^ n - (A α a₀ f (n + 1) : ℝ) / (θ α a₀ f) ^ (n + 1)|
      = |(A α a₀ f (n + 1) : ℝ) / (θ α a₀ f) ^ (n + 1) - (A α a₀ f n : ℝ) / (θ α a₀ f) ^ n| :=
        abs_sub_comm _ _
    _ ≤ ((α - 1) * (θ α a₀ f) ^ (n + 1))⁻¹ := hb_step α a₀ f β hα hαβ ha₀ n
    _ = (α - 1)⁻¹ * (θ α a₀ f)⁻¹ * ((θ α a₀ f)⁻¹) ^ n := by
        rw [mul_inv, ← inv_pow, pow_succ']; ring

lemma htendsto_b (hα : 3 < α) (hαβ : α < β)
    (ha₀ : (α + 1) * (α - 1)⁻¹ * (β - α)⁻¹ < (a₀ : ℝ)) :
    Tendsto (fun n => (A α a₀ f n : ℝ) / (θ α a₀ f) ^ n) atTop (𝓝 (lam α a₀ f)) :=
  (hcauchy_b α a₀ f β hα hαβ ha₀).tendsto_limUnder

/-- The estimate (13): `|Aₙ − λθⁿ| ≤ (α-1)⁻¹(θ-1)⁻¹`. -/
lemma hlam_bound (hα : 3 < α) (hαβ : α < β)
    (ha₀ : (α + 1) * (α - 1)⁻¹ * (β - α)⁻¹ < (a₀ : ℝ)) (n : ℕ) :
    |(A α a₀ f n : ℝ) - lam α a₀ f * (θ α a₀ f) ^ n| ≤ (α - 1)⁻¹ * (θ α a₀ f - 1)⁻¹ := by
  have hθ : 3 < θ α a₀ f := hθ3 α a₀ f β hα hαβ ha₀
  have hθpos : 0 < θ α a₀ f := by linarith
  have hθn : (0 : ℝ) < (θ α a₀ f) ^ n := by positivity
  have hbound := tail_bound (θ α a₀ f) (lam α a₀ f) hθ (fun k => (α - 1) * (θ α a₀ f) ^ k)
    (fun n => (A α a₀ f n : ℝ) / (θ α a₀ f) ^ n) (fun k => mul_pos (by linarith) (pow_pos hθpos k))
    (fun k => hb_step α a₀ f β hα hαβ ha₀ k) (fun m j => le_of_eq (by rw [pow_add]; ring))
    (htendsto_b α a₀ f β hα hαβ ha₀) n
  have hrw : (A α a₀ f n : ℝ) - lam α a₀ f * (θ α a₀ f) ^ n
      = -((θ α a₀ f) ^ n * (lam α a₀ f - (A α a₀ f n : ℝ) / (θ α a₀ f) ^ n)) := by
    field_simp; ring
  rw [hrw, abs_neg, abs_mul, abs_of_pos hθn]
  calc (θ α a₀ f) ^ n * |lam α a₀ f - (A α a₀ f n : ℝ) / (θ α a₀ f) ^ n|
      ≤ (θ α a₀ f) ^ n * (((α - 1) * (θ α a₀ f) ^ n)⁻¹ * (θ α a₀ f - 1)⁻¹) :=
        mul_le_mul_of_nonneg_left hbound hθn.le
    _ = (α - 1)⁻¹ * (θ α a₀ f - 1)⁻¹ := by rw [mul_inv]; field_simp

/-- `|a₀ − λ| ≤ (α-1)⁻¹(θ-1)⁻¹` (the `n = 0` case, with `A₀ = a₀`). -/
lemma hlam_a0 (hα : 3 < α) (hαβ : α < β)
    (ha₀ : (α + 1) * (α - 1)⁻¹ * (β - α)⁻¹ < (a₀ : ℝ)) :
    |(a₀ : ℝ) - lam α a₀ f| ≤ (α - 1)⁻¹ * (θ α a₀ f - 1)⁻¹ := by
  have hb := hlam_bound α a₀ f β hα hαβ ha₀ 0
  rw [pow_zero, mul_one] at hb
  exact hb

lemma hlam_pos (hα : 3 < α) (hαβ : α < β)
    (ha₀ : (α + 1) * (α - 1)⁻¹ * (β - α)⁻¹ < (a₀ : ℝ)) : 0 < lam α a₀ f := by
  have h := hlam_a0 α a₀ f β hα hαβ ha₀
  have hq := quarter_bound α (θ α a₀ f) hα (hθ3 α a₀ f β hα hαβ ha₀)
  have h1 : (1 : ℝ) ≤ (a₀ : ℝ) := by exact_mod_cast a0_pos α a₀ β hα hαβ ha₀
  rw [abs_le] at h
  linarith [h.1, h.2, h1, hq]

lemma hround_lam (hα : 3 < α) (hαβ : α < β)
    (ha₀ : (α + 1) * (α - 1)⁻¹ * (β - α)⁻¹ < (a₀ : ℝ)) : round (lam α a₀ f) = a₀ := by
  apply round_eq_of_abs_lt
  have h := hlam_a0 α a₀ f β hα hαβ ha₀
  have hq := quarter_bound α (θ α a₀ f) hα (hθ3 α a₀ f β hα hαβ ha₀)
  rw [abs_sub_comm]; linarith [h, hq]

/-- The badly-distributed-powers bound (17): `‖λθⁿ‖ ≤ (α-1)⁻¹(θ-1)⁻¹`. -/
lemma hdist_bound (hα : 3 < α) (hαβ : α < β)
    (ha₀ : (α + 1) * (α - 1)⁻¹ * (β - α)⁻¹ < (a₀ : ℝ)) (n : ℕ) :
    distToNearestInt (lam α a₀ f * (θ α a₀ f) ^ n) ≤ (α - 1)⁻¹ * (θ α a₀ f - 1)⁻¹ := by
  have hb := hlam_bound α a₀ f β hα hαβ ha₀ n
  have hq := quarter_bound α (θ α a₀ f) hα (hθ3 α a₀ f β hα hαβ ha₀)
  have hround : round (lam α a₀ f * (θ α a₀ f) ^ n) = A α a₀ f n := by
    apply round_eq_of_abs_lt
    rw [abs_sub_comm]; linarith [hb]
  rw [distToNearestInt, hround, abs_sub_comm]
  exact hb

/-! ### Injectivity: distinct `f` give distinct `θ(f)` -/

lemma hinj (hα : 3 < α) (hαβ : α < β)
    (ha₀ : (α + 1) * (α - 1)⁻¹ * (β - α)⁻¹ < (a₀ : ℝ)) :
    Function.Injective (fun f => θ α a₀ f) := by
  intro f g hfg
  by_contra hne
  have ha0 : 0 < a₀ := a0_pos α a₀ β hα hαβ ha₀
  have hex : ∃ k, f k ≠ g k := Function.ne_iff.mp hne
  set m := Nat.find hex with hmdef
  have hm_spec : f m ≠ g m := Nat.find_spec hex
  have hm_min : ∀ k, k < m → f k = g k := fun k hk => not_not.mp (Nat.find_min hex hk)
  -- `Apair` agrees up to `m`, hence `A` agrees up to `m + 1`.
  have hpaireq : ∀ n, n ≤ m → Apair α a₀ f n = Apair α a₀ g n := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      have hpj : Apair α a₀ f j = Apair α a₀ g j := ih (by omega)
      have hfgj : f j = g j := hm_min j (by omega)
      show ((Apair α a₀ f j).2, _) = ((Apair α a₀ g j).2, _)
      rw [hpj, hfgj]
  have hAeq : ∀ n, n ≤ m + 1 → A α a₀ f n = A α a₀ g n := by
    intro n hn
    rcases Nat.lt_or_ge n (m + 1) with h | h
    · show (Apair α a₀ f n).1 = (Apair α a₀ g n).1
      rw [hpaireq n (by omega)]
    · have hnm : n = m + 1 := by omega
      subst hnm
      show (Apair α a₀ f m).2 = (Apair α a₀ g m).2
      rw [hpaireq m (le_refl m)]
  -- The sequences differ by exactly `±1` at index `m + 2`.
  have hANdiff : (A α a₀ f (m + 2) : ℝ) - (A α a₀ g (m + 2) : ℝ)
      = ((boolToInt (f m) - boolToInt (g m) : ℤ) : ℝ) := by
    rw [A_rec, A_rec, hAeq (m + 1) (le_refl _), hAeq m (by omega)]; push_cast; ring
  have hbool_diff : |((boolToInt (f m) - boolToInt (g m) : ℤ) : ℝ)| = 1 := by
    rw [← Int.cast_abs]
    have : |boolToInt (f m) - boolToInt (g m)| = 1 := by
      cases ha : f m <;> cases hb : g m <;> simp_all [boolToInt]
    rw [this]; norm_num
  have hrall_f : ∀ k, α < r α a₀ f k := fun k => (hr α a₀ f β hα hαβ ha₀ k).1
  have hcpos : 0 < A α a₀ f (m + 1) := hApos α a₀ f hα ha0 (m + 1) (fun k _ => hrall_f k)
  have hcposR : (0 : ℝ) < (A α a₀ f (m + 1) : ℝ) := by exact_mod_cast hcpos
  have hceq : (A α a₀ g (m + 1) : ℝ) = (A α a₀ f (m + 1) : ℝ) := by rw [hAeq (m + 1) (le_refl _)]
  -- `|r_f(m+1) − r_g(m+1)| = A_{m+1}⁻¹`.
  have hrNdiff : |r α a₀ f (m + 1) - r α a₀ g (m + 1)| = (A α a₀ f (m + 1) : ℝ)⁻¹ := by
    show |(A α a₀ f (m + 2) : ℝ) / (A α a₀ f (m + 1) : ℝ)
        - (A α a₀ g (m + 2) : ℝ) / (A α a₀ g (m + 1) : ℝ)| = _
    rw [hceq, div_sub_div_same, abs_div, abs_of_pos hcposR, hANdiff, hbool_diff, one_div]
  have htf := htail α a₀ f β hα hαβ ha₀ (m + 1)
  have htg := htail α a₀ g β hα hαβ ha₀ (m + 1)
  rw [hceq] at htg
  -- Triangle inequality + the bound `α > 3` give a contradiction with `θ f = θ g`.
  have htri : |r α a₀ f (m + 1) - r α a₀ g (m + 1)|
      ≤ |r α a₀ f (m + 1) - θ α a₀ f| + |θ α a₀ f - θ α a₀ g|
        + |θ α a₀ g - r α a₀ g (m + 1)| := by
    have e : r α a₀ f (m + 1) - r α a₀ g (m + 1)
        = r α a₀ f (m + 1) - θ α a₀ f + (θ α a₀ f - θ α a₀ g)
          + (θ α a₀ g - r α a₀ g (m + 1)) := by ring
    rw [e]
    have h1 := abs_add_le (r α a₀ f (m + 1) - θ α a₀ f + (θ α a₀ f - θ α a₀ g))
      (θ α a₀ g - r α a₀ g (m + 1))
    have h2 := abs_add_le (r α a₀ f (m + 1) - θ α a₀ f) (θ α a₀ f - θ α a₀ g)
    linarith [h1, h2]
  rw [hrNdiff] at htri
  have hmid : |θ α a₀ f - θ α a₀ g| = 0 := by
    have hh : θ α a₀ f = θ α a₀ g := hfg
    rw [hh, sub_self, abs_zero]
  have hb1 : |r α a₀ f (m + 1) - θ α a₀ f| ≤ (A α a₀ f (m + 1) : ℝ)⁻¹ * (α - 1)⁻¹ := by
    rw [abs_sub_comm]; exact htf
  rw [hmid] at htri
  have hα1 : (0 : ℝ) < α - 1 := by linarith
  have hcinv : (0 : ℝ) < (A α a₀ f (m + 1) : ℝ)⁻¹ := by positivity
  have hfinal : (A α a₀ f (m + 1) : ℝ)⁻¹ ≤ 2 * ((A α a₀ f (m + 1) : ℝ)⁻¹ * (α - 1)⁻¹) := by
    linarith [htri, hb1, htg]
  have hmulc : (α - 1) * (α - 1)⁻¹ = 1 := mul_inv_cancel₀ hα1.ne'
  nlinarith [hfinal, hcinv, hcposR, hα1, hmulc, mul_pos hcinv hα1]

/-- The set `S = {θ(f) : f}` is uncountable (`{0,1}^ℕ` is uncountable and `θ` is injective). -/
lemma huncountable (hα : 3 < α) (hαβ : α < β)
    (ha₀ : (α + 1) * (α - 1)⁻¹ * (β - α)⁻¹ < (a₀ : ℝ)) :
    ¬ (Set.range (fun f => θ α a₀ f)).Countable := by
  haveI : Uncountable (ℕ → Bool) := by
    rw [← Cardinal.aleph0_lt_mk_iff]
    have h : Cardinal.mk (ℕ → Bool) = 2 ^ Cardinal.aleph0 := by rw [Cardinal.mk_arrow]; simp
    rw [h]; exact Cardinal.cantor _
  rw [← Set.countable_coe_iff]
  intro hc
  exact not_countable ((Equiv.ofInjective _ (hinj α a₀ β hα hαβ ha₀)).countable_iff.mpr hc)

end Bertin.AlphaPow.Boyd

namespace Bertin.AlphaPow

/-- **Boyd's Theorem 1** (proved). -/
@[category research solved, AMS 11, ref "Boy69", formal_uses distToNearestInt]
theorem boyd_theorem_1 (α β : ℝ) (hα : 3 < α) (hαβ : α < β) (a₀ : ℤ)
    (ha₀ : (α + 1) * (α - 1)⁻¹ * (β - α)⁻¹ < (a₀ : ℝ)) :
    ∃ S : Set ℝ, S ⊆ Set.Icc α β ∧ ¬ S.Countable ∧
      ∀ θ ∈ S, ∃ lam : ℝ, 0 < lam ∧
        (∀ n : ℕ, distToNearestInt (lam * θ ^ n) ≤ (α - 1)⁻¹ * (θ - 1)⁻¹) ∧
        round lam = a₀ := by
  refine ⟨Set.range (fun f => Boyd.θ α a₀ f), ?_, Boyd.huncountable α a₀ β hα hαβ ha₀, ?_⟩
  · rintro x ⟨f, rfl⟩
    exact Set.mem_Icc.mpr (Boyd.hθ_mem α a₀ f β hα hαβ ha₀)
  · rintro x ⟨f, rfl⟩
    exact ⟨Boyd.lam α a₀ f, Boyd.hlam_pos α a₀ f β hα hαβ ha₀,
      fun n => Boyd.hdist_bound α a₀ f β hα hαβ ha₀ n, Boyd.hround_lam α a₀ f β hα hαβ ha₀⟩

end Bertin.AlphaPow
