/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import RB.Basic
import RB.Rigidity
import RB.ClosedForm
import ForMathlib.Data.Rat.NearestInt
import Mathlib.Tactic.LinearCombination
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The orbit `W`-identity and the kernel contraction (plan-B2A2, WP3)

The bridge from the *dynamics* of `xₙ₊₁ = ⌈3xₙ/2⌉` to a *Diophantine* statement about the
orbit of `(3/2)ⁿ`: a repetition in the carry word `RB.wmin` forces `K·((3/2)^c − (3/2)^a)` to
sit exponentially close to an integer.

## The tail defect

`RB.tail x₀ n := K(x₀)·(3/2)ⁿ − xₙ` is [B2A2] §2.1's `θₙ`, and it lands in **`[0, 1)`** —
strictly better than the plan's advertised `[0, 2)`, because `RB.ClosedForm` already proves
`xₙ = ⌊K(3/2)ⁿ⌋` unconditionally (`tail_nonneg`, `tail_lt_one`).  The sharper window is worth
having: it drops the constant in `abs_tail_sub_le_of_repetition` from `2` to `1`, so the
contraction reads `|θ_c − θ_a| ≤ (2/3)^k` with no stray factor.

## The `K`-terms cancel

`W_closed` mirrors `TH.W_closed` letter for letter with `θ` in place of `ε`:

  `W(a,k) = 3^k·θ_a − 2^k·θ_{a+k}`,

because `3^k(3/2)^a = 2^k(3/2)^{a+k}` — the `K`-terms cancel *exactly*, which is why an
unknown `K` costs nothing here.  Equal blocks give equal `W`'s (`RB.W_eq_of_repetition`), so a
repetition at `(a, c)` of length `k` yields `3^k(θ_c − θ_a) = 2^k(θ_{c+k} − θ_{a+k})`, whence

  `‖K((3/2)^c − (3/2)^a)‖ ≤ |θ_c − θ_a| ≤ (2/3)^k`,

the nearest integer being `x_c − x_a` (`dist_le_of_repetition`).  Note where the hypothesis
`K = δ ∈ ℚ` enters: **only** in the last step, to land the value in `ℚ` where the corpus's
Diophantine axioms live ([B2A2] §2.2's gate).  The contraction itself is `K`-agnostic.

## The growth ceiling

`repetition_le_add`: `k ≤ c + x₀`.  Crude — the sharp slope is `log₂(3/2) = 0.585`
(`RB.repetition_linear_bound`, which is `x₀ = 1`-only) — but it is uniform in `x₀` and it is
all the Stage-1 reduction needs, which only wants `k → ∞ ⇒ c → ∞`.  Proof: `3^c ≤ 4^c` turns
`RB.repetition_pow_lt`'s `2^{k+c} < 3^c(x₀+1)` into `2^k < 2^c(x₀+1)`, and `x₀+1 < 2^{x₀+1}`
closes it.

## Contents

* `RB.tail`, `RB.tail_nonneg`, `RB.tail_lt_one` — the defect `θₙ ∈ [0, 1)`.
* **`RB.W_closed`** — `W(a,k) = 3^k·θ_a − 2^k·θ_{a+k}` (the `TH.W_closed` mirror).
* `RB.lemmaR_tail`, `RB.abs_tail_sub_le_of_repetition` — the contraction `|θ_c − θ_a| ≤ (2/3)^k`.
* **`RB.dist_le_of_repetition`** — repetition ⇒ kernel violator, in `ℚ`.
* `RB.repetition_le_add` — the growth ceiling `k ≤ c + x₀`.

## References

* [B2A2] `plans/plan-B2A2.html`: §2.1 (this file), WP3.
* [M4A3] `plan-M4A3.html`: `TH.W_closed`, `TH.abs_eps_sub_le_of_repetition` — the templates.
* [AFS08] Akiyama, Frougny, Sakarovitch. Israel J. Math. **168** (2008), 53–91.
-/

namespace RB

/-! ## The tail defect `θₙ` -/

/-- **The tail defect** `θₙ := K(x₀)·(3/2)ⁿ − xₙ` ([B2A2] §2.1), the `RB` counterpart of
`TH.eps`. -/
@[category API, AMS 11 68, ref "B2A2", group "rb_rational_base"]
noncomputable def tail (x₀ n : ℕ) : ℝ := K x₀ * (3 / 2) ^ n - x x₀ n

/-- `0 ≤ θₙ` — the orbit never overshoots (`RB.x_le_K_mul_pow`). -/
@[category API, AMS 11 68, ref "B2A2", group "rb_rational_base"]
lemma tail_nonneg (x₀ n : ℕ) : 0 ≤ tail x₀ n := by
  have := x_le_K_mul_pow x₀ n
  unfold tail
  linarith

/-- `θₙ < 1` — the sharp upper end, from the unconditional closed form `xₙ = ⌊K(3/2)ⁿ⌋`
(`RB.K_lt_add_one` at `xₙ`, transported by `RB.K_shift`).  [B2A2] §2.1 advertises only
`θ ∈ [0,2)`; the closed form does better. -/
@[category API, AMS 11 68, ref "OW91" "AFS08", group "rb_rational_base"]
lemma tail_lt_one {x₀ : ℕ} (hx₀ : 0 < x₀) (n : ℕ) : tail x₀ n < 1 := by
  have h := K_lt_add_one (x_pos hx₀ n)
  rw [K_shift] at h
  unfold tail
  linarith

/-- Two defects differ by less than `1` in absolute value. -/
@[category API, AMS 11 68, ref "B2A2", group "rb_rational_base"]
lemma abs_tail_sub_le_one {x₀ : ℕ} (hx₀ : 0 < x₀) (m n : ℕ) :
    |tail x₀ m - tail x₀ n| ≤ 1 := by
  have h1 := tail_nonneg x₀ m
  have h2 := tail_lt_one hx₀ m
  have h3 := tail_nonneg x₀ n
  have h4 := tail_lt_one hx₀ n
  rw [abs_le]
  constructor <;> linarith

/-! ## The `W`-identity: the `K`-terms cancel -/

/-- **The orbit `W`-identity** ([B2A2] §2.1): `W(a,k) = 3^k·θ_a − 2^k·θ_{a+k}` — the exact
mirror of `TH.W_closed`.

The `K`-terms cancel because `2^k·(3/2)^{a+k} = 3^k·(3/2)^a`; this is why the *unknown*
constant `K` is no obstruction to the repetition algebra. -/
@[category research solved, AMS 11 68, ref "B2A2", group "rb_rational_base"]
theorem W_closed (x₀ a k : ℕ) :
    (W x₀ a k : ℝ) = 3 ^ k * tail x₀ a - 2 ^ k * tail x₀ (a + k) := by
  have hcs : (2 : ℝ) ^ k * x x₀ (a + k) = 3 ^ k * x x₀ a + W x₀ a k := by
    exact_mod_cast circuit_sum x₀ a k
  have h23 : (2 : ℝ) ^ k * (3 / 2 : ℝ) ^ k = 3 ^ k := by
    rw [← mul_pow]
    norm_num
  unfold tail
  rw [pow_add]
  linear_combination (-1 : ℝ) * hcs + (K x₀ * (3 / 2 : ℝ) ^ a) * h23

/-- **Lemma R for the orbit word**: a repetition equates the two `W`'s, so
`3^k(θ_c − θ_a) = 2^k(θ_{c+k} − θ_{a+k})`. -/
@[category research solved, AMS 11 68, ref "B2A2", group "rb_rational_base"]
theorem lemmaR_tail {x₀ a c k : ℕ} (h : IsRepetition x₀ a c k) :
    (3 : ℝ) ^ k * (tail x₀ c - tail x₀ a) = 2 ^ k * (tail x₀ (c + k) - tail x₀ (a + k)) := by
  have h1 := W_closed x₀ a k
  have h2 := W_closed x₀ c k
  rw [W_eq_of_repetition h] at h1
  linear_combination h1 - h2

/-- **The contraction**: a length-`k` repetition squeezes the defects to within `(2/3)^k`.
The `[0,1)` window of `tail` is what makes the constant `1` rather than [B2A2] §2.1's `2`. -/
@[category research solved, AMS 11 68, ref "B2A2", group "rb_rational_base"]
theorem abs_tail_sub_le_of_repetition {x₀ : ℕ} (hx₀ : 0 < x₀) {a c k : ℕ}
    (h : IsRepetition x₀ a c k) : |tail x₀ c - tail x₀ a| ≤ (2 / 3 : ℝ) ^ k := by
  have hR := lemmaR_tail h
  have h3 : (0 : ℝ) < 3 ^ k := by positivity
  have hkey : tail x₀ c - tail x₀ a
      = (2 / 3 : ℝ) ^ k * (tail x₀ (c + k) - tail x₀ (a + k)) := by
    rw [div_pow]
    field_simp
    linear_combination hR
  rw [hkey, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 / 3 : ℝ) ^ k)]
  calc (2 / 3 : ℝ) ^ k * |tail x₀ (c + k) - tail x₀ (a + k)|
      ≤ (2 / 3 : ℝ) ^ k * 1 :=
        mul_le_mul_of_nonneg_left (abs_tail_sub_le_one hx₀ _ _) (by positivity)
    _ = (2 / 3 : ℝ) ^ k := mul_one _

/-! ## Repetition ⇒ kernel violator -/

/-- **Repetition ⇒ kernel violator** ([B2A2] §2.1, the deliverable): if `K(x₀) = δ` is
rational and the carry word repeats at `(a, c)` for length `k`, then

  `‖δ·((3/2)^c − (3/2)^a)‖ ≤ (2/3)^k`,

the nearest integer being `x_c − x_a`.  This is the *only* place the rationality of `K`
is used in the whole chain — it lands the value in `ℚ`, where the corpus's Diophantine
axioms (`CZ.pseudoPisot_approx_of_subspace`, `NKR.sUnit_pair_integrality_of_subspace`)
are stated.  See [B2A2] §2.2: for arbitrary *real* multipliers the downstream statement is
outright **false** (Liouville construction), so this gate is not a formalization artifact. -/
@[category research solved, AMS 11 68, ref "B2A2", group "rb_rational_base"]
theorem dist_le_of_repetition {x₀ : ℕ} (hx₀ : 0 < x₀) {δ : ℚ} (hδ : (δ : ℝ) = K x₀)
    {a c k : ℕ} (h : IsRepetition x₀ a c k) :
    (δ * ((3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a)).distToNearestInt ≤ (2 / 3 : ℚ) ^ k := by
  set D : ℤ := (x x₀ c : ℤ) - x x₀ a with hD
  have hreal : ((δ * ((3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a) - (D : ℚ) : ℚ) : ℝ)
      = tail x₀ c - tail x₀ a := by
    unfold tail
    rw [hD]
    push_cast
    rw [hδ]
    ring
  have habs : |δ * ((3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a) - (D : ℚ)| ≤ (2 / 3 : ℚ) ^ k := by
    have hcast : ((|δ * ((3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a) - (D : ℚ)| : ℚ) : ℝ)
        = |tail x₀ c - tail x₀ a| := by
      rw [Rat.cast_abs, hreal]
    have hle := abs_tail_sub_le_of_repetition hx₀ h
    rw [← hcast] at hle
    have h23 : (((2 / 3 : ℚ) ^ k : ℚ) : ℝ) = (2 / 3 : ℝ) ^ k := by push_cast; ring
    rw [← h23, Rat.cast_le] at hle
    exact hle
  exact le_trans (Rat.distToNearestInt_le_abs_sub_intCast _ D) habs

/-! ## The growth ceiling -/

/-- **The growth ceiling** `k ≤ c + x₀`: repetitions cannot be long relative to their position.

Crude by design — the sharp slope is `log₂(3/2) = 0.585…` (`RB.repetition_linear_bound`, which
is `x₀ = 1`-only) — but uniform in `x₀`, and the Stage-1 reduction only needs `k → ∞ ⇒ c → ∞`.
From `RB.repetition_pow_lt` (`2^{k+c} < 3^c(x₀+1)`) via `3^c ≤ 4^c` and `x₀+1 < 2^{x₀+1}`. -/
@[category research solved, AMS 11 68, ref "B2A2", group "rb_rational_base"]
theorem repetition_le_add {x₀ a c k : ℕ} (hx₀ : 0 < x₀) (hac : a < c)
    (h : IsRepetition x₀ a c k) : k ≤ c + x₀ := by
  by_contra hk
  push Not at hk
  have hlt := repetition_pow_lt hx₀ hac h
  have h34 : (3 : ℕ) ^ c ≤ 4 ^ c := Nat.pow_le_pow_left (by norm_num) c
  have hx1 : x₀ + 1 < 2 ^ (x₀ + 1) := Nat.lt_two_pow_self
  have e1 : (2 : ℕ) ^ (2 * c + x₀ + 1) ≤ 2 ^ (k + c) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have e2 : (2 : ℕ) ^ (2 * c + x₀ + 1) = 4 ^ c * 2 ^ (x₀ + 1) := by
    rw [show 2 * c + x₀ + 1 = 2 * c + (x₀ + 1) by ring, pow_add, pow_mul]
    norm_num
  have e3 : 3 ^ c * (x₀ + 1) < 4 ^ c * 2 ^ (x₀ + 1) :=
    calc 3 ^ c * (x₀ + 1) ≤ 4 ^ c * (x₀ + 1) := Nat.mul_le_mul_right _ h34
      _ < 4 ^ c * 2 ^ (x₀ + 1) := mul_lt_mul_of_pos_left hx1 (by positivity)
  omega

end RB
