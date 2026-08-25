/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import SZ.Defs
import Mathlib.Tactic.LinearCombination

/-!
# The trace engine: a two-term integer recurrence and its real realisation

The arithmetic half of the *sign-compensated trace-parity design* of
`plans/plan-dubD1.html` §1.  Everything in `SZ/` that produces a member of `𝒵` from an
algebraic `α` factors through this file.

Let `α, β` be the two roots of `x² = A x + B` (`A, B ∈ ℤ`).  For reals `u, v` the sequence
`n ↦ u αⁿ + v βⁿ` satisfies the same recurrence, so if its first two values `u + v` and
`u α + v β` are *integers* `t₀, t₁`, then

> `u αⁿ + v βⁿ = rec2 A B t₀ t₁ n ∈ ℤ`   for every `n`  (`rec2_real`).

Because `|β| < 1` the term `v βⁿ` is eventually a small real, so `⌊u αⁿ⌋` is `rec2 … n`
corrected by the *sign* of `v βⁿ` — and the whole design consists of choosing the seeds
`t₀, t₁` so that the residue class of `rec2 … n` compensates that sign.  Two seed
patterns do all the work in this root:

* `t₀ = t₁ = 0 (mod m)` keeps the whole sequence `≡ 0`, which is what a *positive* second
  conjugate needs (`SZ/PellDesign.lean`, cell `β ∈ (0,1)`);
* `t₀ = 1, t₁ = 0` gives the alternating pattern `1, 0, 1, 0, …` modulo `m` as soon as
  `m ∣ A` and `m ∣ B - 1`, which is exactly what a *negative* second conjugate needs
  (`rec2_dvd_sub`).  For quadratics `x² - a x - b` that reads `a ≡ 0`, `b ≡ 1 (mod m)`;
  at `m = 2` it is the lattice criterion `(x+1)² ∣ P` in `𝔽₂[x]`.

## References

* [Dub06EO] A. Dubickas, *Even and odd integral parts of powers of a real number*,
  Glasgow Math. J. **48** (2006), 331–336.
-/

namespace SZ

/-- Two-step induction, with named cases. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_sz_trace"]
theorem twoStep {P : ℕ → Prop} (h0 : P 0) (h1 : P 1)
    (hs : ∀ n, P n → P (n + 1) → P (n + 2)) (n : ℕ) : P n :=
  Nat.twoStepInduction h0 h1 hs n

/-- The two-term integer recurrence `t (n+2) = A · t (n+1) + B · t n` with seeds `t₀, t₁`. -/
def rec2 (A B t₀ t₁ : ℤ) : ℕ → ℤ
  | 0 => t₀
  | 1 => t₁
  | (n + 2) => A * rec2 A B t₀ t₁ (n + 1) + B * rec2 A B t₀ t₁ n

@[simp, category API, AMS 11, ref "Dub06EO", group "dub06_sz_trace"]
theorem rec2_zero (A B t₀ t₁ : ℤ) : rec2 A B t₀ t₁ 0 = t₀ := rfl

@[simp, category API, AMS 11, ref "Dub06EO", group "dub06_sz_trace"]
theorem rec2_one (A B t₀ t₁ : ℤ) : rec2 A B t₀ t₁ 1 = t₁ := rfl

@[category API, AMS 11, ref "Dub06EO", group "dub06_sz_trace"]
theorem rec2_add_two (A B t₀ t₁ : ℤ) (n : ℕ) :
    rec2 A B t₀ t₁ (n + 2) = A * rec2 A B t₀ t₁ (n + 1) + B * rec2 A B t₀ t₁ n := rfl

/-! ## The real realisation -/

/-- **The trace identity.**  If `α` and `β` both satisfy `x² = A x + B`, and the two seeds
`u + v` and `u α + v β` are the integers `t₀, t₁`, then `u αⁿ + v βⁿ` is the integer
`rec2 A B t₀ t₁ n` for every `n`. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_sz_trace"]
theorem rec2_real {A B t₀ t₁ : ℤ} {α β u v : ℝ}
    (hα : α ^ 2 = A * α + B) (hβ : β ^ 2 = A * β + B)
    (h0 : u + v = (t₀ : ℝ)) (h1 : u * α + v * β = (t₁ : ℝ)) (n : ℕ) :
    u * α ^ n + v * β ^ n = (rec2 A B t₀ t₁ n : ℝ) := by
  induction n using SZ.twoStep with
  | h0 => simpa using h0
  | h1 => simpa using h1
  | hs n ih1 ih2 =>
    have eα : α ^ (n + 2) = A * α ^ (n + 1) + B * α ^ n := by
      have e : α ^ (n + 2) = α ^ n * α ^ 2 := by ring
      rw [e, hα]; ring
    have eβ : β ^ (n + 2) = A * β ^ (n + 1) + B * β ^ n := by
      have e : β ^ (n + 2) = β ^ n * β ^ 2 := by ring
      rw [e, hβ]; ring
    rw [eα, eβ, rec2_add_two]
    push_cast
    linear_combination (A : ℝ) * ih2 + (B : ℝ) * ih1

/-! ## The two seed patterns -/

/-- **The constant pattern.**  Even seeds give an even sequence, whatever `A` and `B`. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_sz_trace"]
theorem rec2_even {A B t₀ t₁ : ℤ} (h0 : Even t₀) (h1 : Even t₁) (n : ℕ) :
    Even (rec2 A B t₀ t₁ n) := by
  induction n using SZ.twoStep with
  | h0 => simpa using h0
  | h1 => simpa using h1
  | hs n ih1 ih2 =>
    rw [rec2_add_two]
    exact (ih2.mul_left A).add (ih1.mul_left B)

/-- **The alternating pattern.**  If `m ∣ A` and `m ∣ B - 1` then the recurrence is
`t (n+2) ≡ t n (mod m)`, so the sequence alternates between its two seeds modulo `m`.

For a quadratic `x² - a x - b` (so `A = a`, `B = b`) this is `a ≡ 0`, `b ≡ 1 (mod m)`; at
`m = 2` it says `(x+1)² ∣ x² - a x - b` in `𝔽₂[x]`, the lattice criterion of
`plans/plan-dubD1.html` §1.2. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_sz_trace"]
theorem rec2_dvd_sub {m A B t₀ t₁ : ℤ} (hA : m ∣ A) (hB : m ∣ (B - 1)) (n : ℕ) :
    m ∣ (rec2 A B t₀ t₁ n - if n % 2 = 0 then t₀ else t₁) := by
  induction n using SZ.twoStep with
  | h0 => simp
  | h1 => simp
  | hs n ih1 ih2 =>
    have key : rec2 A B t₀ t₁ (n + 2) - rec2 A B t₀ t₁ n
        = A * rec2 A B t₀ t₁ (n + 1) + (B - 1) * rec2 A B t₀ t₁ n := by
      rw [rec2_add_two]; ring
    have h2 : m ∣ (rec2 A B t₀ t₁ (n + 2) - rec2 A B t₀ t₁ n) := by
      rw [key]; exact dvd_add (hA.mul_right _) (hB.mul_right _)
    have hmod : (n + 2) % 2 = n % 2 := by omega
    rw [hmod]
    have e : rec2 A B t₀ t₁ (n + 2) - (if n % 2 = 0 then t₀ else t₁)
        = (rec2 A B t₀ t₁ (n + 2) - rec2 A B t₀ t₁ n)
          + (rec2 A B t₀ t₁ n - (if n % 2 = 0 then t₀ else t₁)) := by ring
    rw [e]
    exact dvd_add h2 ih1

end SZ
