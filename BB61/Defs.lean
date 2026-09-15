/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Bugeaud Problem 10.61, Route A: the quadratic setting

Formal companion of `note-1061-M2.html` (milestone M2 of `plans/plan-1061.html`), built on
the reductions of `note-1061-M1.html` (milestone M1).

> **Problem 10.61** ([Bug12] Ch. 10). Let `α > 2` be Pisot and
> `C(α) = {(α-1) ∑_{k≥1} ε_k α^{-k} : ε ∈ {0,1}^ℕ}`.  Show that `(ξ αⁿ)` is never
> uniformly distributed modulo one for `ξ ∈ C(α)`.

This root formalises the **degree-two Route A engine**: for a real `α` satisfying a monic
integer quadratic `α² = aα + b` with `1 < α` and conjugate `β = a - α`, `|β| < 1`,

* the exact splitting `{ξ αⁿ} = {t_n - S_n}` (M1 Lemma 2 / Prop. 4, degree 2), carried by
  an **integer pair recursion** `(u_n, v_n) ∈ ℤ²` with `A_n = u_n + v_n α`,
  `S_n = u_n + v_n β`, `A_n + S_n = 2u_n + a v_n ∈ ℤ` — no number-field machinery;
* the finite-candidate covering of the orbit of fractional parts (M2 Theorem 2);
* the uniform avoided-interval theorem, and the capstone at `α = 2 + √5`
  (`BB61/RouteA.lean`), the smallest Pisot number of degree ≥ 2 where Route A fires.

## Conventions

* Digits are `ε : ℕ → Bool`, zero-indexed: the note's `ε_k` is `ε (k-1)` here, so
  `piVal α ε = (α-1) ∑_{k≥0} ε k · α^{-(k+1)}` and `cantorSet α = C(α)`.
* The hypotheses on `α` are the *minimal* ones the engine consumes: `α² = aα + b`
  (`a b : ℤ`), `1 < α`, `|a - α| < 1`.  Irreducibility, `α > 2`, and the Pisot property
  are **not** needed; integer `α` (with `β = 0`) is included as the degenerate case
  `d = 1` of the note.

## References

* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*,
  Cambridge Tracts in Math. 193, CUP 2012.  Problem 10.61.
* `note-1061-M1.html` §3 (the splitting; exact confinement), `note-1061-M2.html` §3
  (the covering); verification scripts `BB61/m1_verify.py`, `BB61/m2_verify.py`.
-/

namespace BB61

/-- The digit `ε k ∈ {0,1}` as a real number. -/
def dR (ε : ℕ → Bool) (k : ℕ) : ℝ := if ε k then 1 else 0

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem dR_nonneg (ε : ℕ → Bool) (k : ℕ) : 0 ≤ dR ε k := by
  unfold dR; split <;> norm_num

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem dR_le_one (ε : ℕ → Bool) (k : ℕ) : dR ε k ≤ 1 := by
  unfold dR; split <;> norm_num

/-- The Cantor map: `piVal α ε = (α-1) ∑_{k≥0} ε k · α^{-(k+1)}`, so that
`cantorSet α = C(α)` of [Bug12] Problem 10.61. -/
noncomputable def piVal (α : ℝ) (ε : ℕ → Bool) : ℝ :=
  (α - 1) * ∑' k : ℕ, dR ε k * (α⁻¹) ^ (k + 1)

/-- `C(α)`, the Cantor set of Problem 10.61. -/
noncomputable def cantorSet (α : ℝ) : Set ℝ := Set.range (piVal α)

/-- The word shifted by `n` letters: the digit stream seen at time `n`. -/
def shift (ε : ℕ → Bool) (n : ℕ) : ℕ → Bool := fun k => ε (n + k)

/-- The future part `t_n = π(σⁿ ε) ∈ C(α)` of the splitting. -/
noncomputable def tPart (α : ℝ) (ε : ℕ → Bool) (n : ℕ) : ℝ := piVal α (shift ε n)

/-! ## Geometric-series toolbox -/

section Geom

variable {r : ℝ}

/-- Comparison test against the geometric series, in the form used throughout. -/
theorem summable_of_le_geom (hr0 : 0 ≤ r) (hr1 : r < 1) {f : ℕ → ℝ}
    (h0 : ∀ k, 0 ≤ f k) (h1 : ∀ k, f k ≤ r ^ k) : Summable f :=
  Summable.of_nonneg_of_le h0 h1 (summable_geometric_of_lt_one hr0 hr1)

theorem summable_dR_pow (hr0 : 0 ≤ r) (hr1 : r < 1) (ε : ℕ → Bool) :
    Summable fun k : ℕ => dR ε k * r ^ (k + 1) := by
  refine summable_of_le_geom hr0 hr1 (fun k => ?_) (fun k => ?_)
  · exact mul_nonneg (dR_nonneg ε k) (pow_nonneg hr0 _)
  · calc dR ε k * r ^ (k + 1) ≤ 1 * r ^ (k + 1) :=
          mul_le_mul_of_nonneg_right (dR_le_one ε k) (pow_nonneg hr0 _)
    _ = r ^ (k + 1) := one_mul _
    _ ≤ r ^ k := pow_le_pow_of_le_one hr0 hr1.le (Nat.le_succ k)

theorem summable_dR_pow' (hr0 : 0 ≤ r) (hr1 : r < 1) (ε : ℕ → Bool) :
    Summable fun k : ℕ => dR ε k * r ^ k := by
  refine summable_of_le_geom hr0 hr1 (fun k => ?_) (fun k => ?_)
  · exact mul_nonneg (dR_nonneg ε k) (pow_nonneg hr0 _)
  · calc dR ε k * r ^ k ≤ 1 * r ^ k :=
          mul_le_mul_of_nonneg_right (dR_le_one ε k) (pow_nonneg hr0 _)
    _ = r ^ k := one_mul _

theorem summable_geom_succ (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun k : ℕ => r ^ (k + 1) := by
  have : (fun k : ℕ => r ^ (k + 1)) = fun k : ℕ => r * r ^ k := by
    funext k; rw [pow_succ']
  rw [this]
  exact (summable_geometric_of_lt_one hr0 hr1).mul_left _

/-- `∑_{k≥0} r^{k+1} = r/(1-r)`. -/
theorem tsum_geom_succ (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' k : ℕ, r ^ (k + 1) = r * (1 - r)⁻¹ := by
  have : (fun k : ℕ => r ^ (k + 1)) = fun k : ℕ => r * r ^ k := by
    funext k; rw [pow_succ']
  rw [this, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]

end Geom

section Alpha

variable {α : ℝ} (hα : 1 < α)

theorem inv_pos_of_one_lt (hα : 1 < α) : 0 < α⁻¹ := inv_pos.mpr (lt_trans one_pos hα)

theorem inv_lt_one_of_one_lt (hα : 1 < α) : α⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ hα

include hα in
/-- `∑_{k≥0} α^{-(k+1)} = (α-1)⁻¹`: the normalising sum behind `piVal α 1^∞ = 1`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tsum_inv_pow_succ : ∑' k : ℕ, (α⁻¹ : ℝ) ^ (k + 1) = (α - 1)⁻¹ := by
  have hr0 := (inv_pos_of_one_lt hα).le
  have hr1 := inv_lt_one_of_one_lt hα
  have hαne : α ≠ 0 := by positivity
  rw [tsum_geom_succ hr0 hr1]
  rw [show (1 : ℝ) - α⁻¹ = (α - 1) / α by field_simp]
  rw [inv_div]
  field_simp

include hα in
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem piVal_nonneg (ε : ℕ → Bool) : 0 ≤ piVal α ε := by
  refine mul_nonneg (by linarith) (tsum_nonneg fun k => ?_)
  exact mul_nonneg (dR_nonneg ε k) (pow_nonneg (inv_pos_of_one_lt hα).le _)

include hα in
/-- `piVal α ε ≤ 1`: the value `1` is `π(1^∞)` (M1 Lemma 1(i)). -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem piVal_le_one (ε : ℕ → Bool) : piVal α ε ≤ 1 := by
  have hr0 := (inv_pos_of_one_lt hα).le
  have hr1 := inv_lt_one_of_one_lt hα
  have hαne : α ≠ 0 := by positivity
  have hsum : ∑' k : ℕ, dR ε k * (α⁻¹) ^ (k + 1) ≤ ∑' k : ℕ, (α⁻¹) ^ (k + 1) := by
    refine (summable_dR_pow hr0 hr1 ε).tsum_le_tsum (fun k => ?_)
      (summable_geom_succ hr0 hr1)
    calc dR ε k * (α⁻¹) ^ (k + 1) ≤ 1 * (α⁻¹) ^ (k + 1) :=
          mul_le_mul_of_nonneg_right (dR_le_one ε k) (pow_nonneg hr0 _)
    _ = (α⁻¹) ^ (k + 1) := one_mul _
  have hval : ∑' k : ℕ, (α⁻¹) ^ (k + 1) = (α - 1)⁻¹ := tsum_inv_pow_succ hα
  calc piVal α ε ≤ (α - 1) * (α - 1)⁻¹ := by
        rw [piVal]
        exact mul_le_mul_of_nonneg_left (le_of_le_of_eq hsum hval) (by linarith)
  _ = 1 := mul_inv_cancel₀ (by linarith)

include hα in
/-- The backward recursion of the future part:
`α t_n = (α-1) ε_n + t_{n+1}` (M1 Lemma 1(v), rearranged). -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem alpha_mul_tPart (ε : ℕ → Bool) (n : ℕ) :
    α * tPart α ε n = (α - 1) * dR ε n + tPart α ε (n + 1) := by
  have hr0 := (inv_pos_of_one_lt hα).le
  have hr1 := inv_lt_one_of_one_lt hα
  have hαne : α ≠ 0 := by positivity
  have hs : Summable fun k : ℕ => dR (shift ε n) k * (α⁻¹) ^ k :=
    summable_dR_pow' hr0 hr1 _
  have hpull : ∀ k : ℕ, α * (α⁻¹ : ℝ) ^ (k + 1) = (α⁻¹) ^ k := fun k => by
    rw [pow_succ', ← mul_assoc, mul_inv_cancel₀ hαne, one_mul]
  have key : α * ∑' k : ℕ, dR (shift ε n) k * (α⁻¹) ^ (k + 1)
      = ∑' k : ℕ, dR (shift ε n) k * (α⁻¹) ^ k := by
    rw [← tsum_mul_left]
    congr 1; funext k
    rw [mul_left_comm, hpull k]
  have split : ∑' k : ℕ, dR (shift ε n) k * (α⁻¹) ^ k
      = dR ε n + ∑' k : ℕ, dR (shift ε (n + 1)) k * (α⁻¹) ^ (k + 1) := by
    rw [hs.tsum_eq_zero_add]
    congr 1
    · simp [shift, dR]
    · congr 1; funext k
      have hk : n + (k + 1) = n + 1 + k := by omega
      simp only [dR, shift, hk]
      rfl
  calc α * tPart α ε n
      = (α - 1) * (α * ∑' k : ℕ, dR (shift ε n) k * (α⁻¹) ^ (k + 1)) := by
        rw [tPart, piVal]; ring
  _ = (α - 1) * (dR ε n + ∑' k : ℕ, dR (shift ε (n + 1)) k * (α⁻¹) ^ (k + 1)) := by
        rw [key, split]
  _ = (α - 1) * dR ε n + tPart α ε (n + 1) := by rw [tPart, piVal]; ring

end Alpha

/-! ## The quadratic setting -/

/-- The data Route A consumes at degree two: a real root `α > 1` of a monic integer
quadratic `X² - aX - b`, whose conjugate `β = a - α` lies strictly inside the unit disc.
Neither irreducibility nor `α > 2` is needed: the fields carry exactly the three facts
every lemma uses. -/
structure QuadSetup where
  /-- the linear coefficient — the trace of the quadratic -/
  a : ℤ
  /-- the constant coefficient — minus the norm -/
  b : ℤ
  /-- the distinguished real root -/
  α : ℝ
  /-- `α` is a root of `X² - aX - b` -/
  root : α ^ 2 = a * α + b
  /-- `α` exceeds one -/
  one_lt : 1 < α
  /-- the conjugate `a - α` lies strictly inside the unit interval in modulus -/
  conj_lt : |(a : ℝ) - α| < 1

namespace QuadSetup

variable (P : QuadSetup)

/-- The algebraic conjugate `β = a - α` of `α`. -/
noncomputable def β : ℝ := (P.a : ℝ) - P.α

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem alpha_add_beta : P.α + P.β = (P.a : ℝ) := by unfold β; ring

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_beta_lt_one : |P.β| < 1 := P.conj_lt

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem beta_root : P.β ^ 2 = (P.a : ℝ) * P.β + P.b := by
  have h := P.root
  unfold β
  nlinarith [h]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem alpha_pos : 0 < P.α := lt_trans one_pos P.one_lt

/-- The digit as an integer. -/
def bitZ (ε : ℕ → Bool) (n : ℕ) : ℤ := if ε n then 1 else 0

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem bitZ_cast (ε : ℕ → Bool) (n : ℕ) : ((bitZ ε n : ℤ) : ℝ) = dR ε n := by
  unfold bitZ dR; split <;> norm_num

/-- The integer pair recursion carrying `A_n = (α-1) ∑_{k=1}^n ε_k α^{n-k} ∈ ℤ[α]`:
`A_n = u_n + v_n α` with `(u_0, v_0) = (0,0)`,
`u_{n+1} = b v_n - ε_n`, `v_{n+1} = u_n + a v_n + ε_n`.
This is `BB61/m1_field.py`'s arithmetic specialised to degree 2, and the whole of the
"trace" machinery the quadratic case needs. -/
def uv (ε : ℕ → Bool) : ℕ → ℤ × ℤ
  | 0 => (0, 0)
  | n + 1 => (P.b * (uv ε n).2 - bitZ ε n, (uv ε n).1 + P.a * (uv ε n).2 + bitZ ε n)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem uv_zero (ε : ℕ → Bool) : P.uv ε 0 = (0, 0) := rfl

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem uv_succ (ε : ℕ → Bool) (n : ℕ) :
    P.uv ε (n + 1)
      = (P.b * (P.uv ε n).2 - bitZ ε n,
         (P.uv ε n).1 + P.a * (P.uv ε n).2 + bitZ ε n) := rfl

/-- The algebraic part `A_n = u_n + v_n α`, evaluated at the root `α`. -/
noncomputable def aPart (ε : ℕ → Bool) (n : ℕ) : ℝ :=
  ((P.uv ε n).1 : ℝ) + ((P.uv ε n).2 : ℝ) * P.α

/-- The conjugate shadow `S_n = σ₂(A_n) = u_n + v_n β` — the window part of the
splitting (M1 Lemma 2, degree 2). -/
noncomputable def sPart (ε : ℕ → Bool) (n : ℕ) : ℝ :=
  ((P.uv ε n).1 : ℝ) + ((P.uv ε n).2 : ℝ) * P.β

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem aPart_zero (ε : ℕ → Bool) : P.aPart ε 0 = 0 := by simp [aPart, uv_zero]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem sPart_zero (ε : ℕ → Bool) : P.sPart ε 0 = 0 := by simp [sPart, uv_zero]

/-- `A_{n+1} = α A_n + (α-1) ε_n`: the forward recursion, transferred through the root
identity `α² = aα + b`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem aPart_succ (ε : ℕ → Bool) (n : ℕ) :
    P.aPart ε (n + 1) = P.α * P.aPart ε n + (P.α - 1) * dR ε n := by
  have hroot := P.root
  have hcast := bitZ_cast ε n
  simp only [aPart, uv_succ]
  push_cast
  rw [hcast]
  linear_combination (-((P.uv ε n).2 : ℝ)) * hroot

/-- `S_{n+1} = β S_n + (β-1) ε_n`: the same recursion at the conjugate. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem sPart_succ (ε : ℕ → Bool) (n : ℕ) :
    P.sPart ε (n + 1) = P.β * P.sPart ε n + (P.β - 1) * dR ε n := by
  have hroot := P.beta_root
  have hcast := bitZ_cast ε n
  simp only [sPart, uv_succ]
  push_cast
  rw [hcast]
  linear_combination (-((P.uv ε n).2 : ℝ)) * hroot

/-- `A_n + S_n = 2u_n + a v_n ∈ ℤ`: the trace identity, with no number field in sight. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem aPart_add_sPart (ε : ℕ → Bool) (n : ℕ) :
    P.aPart ε n + P.sPart ε n = ((2 * (P.uv ε n).1 + P.a * (P.uv ε n).2 : ℤ) : ℝ) := by
  have h := P.alpha_add_beta
  simp only [aPart, sPart]
  push_cast
  linear_combination ((P.uv ε n).2 : ℝ) * h

end QuadSetup

end BB61
