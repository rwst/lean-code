/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.Defs
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The exact splitting `{ξ αⁿ} = {t_n - S_n}` at degree two

M1 Lemma 2 and Proposition 4 of `note-1061-M1.html`, quadratic case: for
`ξ = piVal α ε ∈ C(α)`,

* `ξ αⁿ = A_n + t_n` with `A_n = u_n + v_n α` the integer-pair part
  (`xi_mul_pow`);
* `A_n + S_n = 2u_n + a v_n ∈ ℤ`, so `Int.fract (ξ αⁿ) = Int.fract (t_n - S_n)`
  **exactly, for every `n ≥ 0`** (`fract_split`) — the `O(ρⁿ)`-free form that makes
  every confinement conclusion unconditional;
* `S_n = ∑_{m<n} c_m ε_{n-1-m}` with `c_m = (β-1) βᵐ` (`sPart_eq_sum`), and the window
  bound `|S_n| ≤ (1+|β|)/(1-|β|)` (`abs_sPart_le`).

Verified numerically at five `α` by `BB61/m1_verify.py` (checks L2, P3); the covering
consequences live in `BB61/Covering.lean`.
-/

namespace BB61

namespace QuadSetup

variable (P : QuadSetup)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem shift_zero (ε : ℕ → Bool) : shift ε 0 = ε := by
  funext k; simp [shift]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tPart_zero_eq (α : ℝ) (ε : ℕ → Bool) : tPart α ε 0 = piVal α ε := by
  rw [tPart, shift_zero]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tPart_nonneg (ε : ℕ → Bool) (n : ℕ) : 0 ≤ tPart P.α ε n :=
  piVal_nonneg P.one_lt _

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tPart_le_one (ε : ℕ → Bool) (n : ℕ) : tPart P.α ε n ≤ 1 :=
  piVal_le_one P.one_lt _

/-- **The splitting, additive form** (M1 Lemma 2, degree 2): `ξ αⁿ = A_n + t_n`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem xi_mul_pow (ε : ℕ → Bool) (n : ℕ) :
    piVal P.α ε * P.α ^ n = P.aPart ε n + tPart P.α ε n := by
  induction n with
  | zero => rw [pow_zero, mul_one, P.aPart_zero, tPart_zero_eq, zero_add]
  | succ n ih =>
      have hrec := alpha_mul_tPart P.one_lt ε n
      have hA := P.aPart_succ ε n
      calc piVal P.α ε * P.α ^ (n + 1)
          = piVal P.α ε * P.α ^ n * P.α := by ring
      _ = (P.aPart ε n + tPart P.α ε n) * P.α := by rw [ih]
      _ = P.α * P.aPart ε n + P.α * tPart P.α ε n := by ring
      _ = P.α * P.aPart ε n + ((P.α - 1) * dR ε n + tPart P.α ε (n + 1)) := by rw [hrec]
      _ = P.aPart ε (n + 1) + tPart P.α ε (n + 1) := by rw [hA]; ring

/-- **The exact splitting of the fractional part** (M1 Lemma 2 / Prop. 4, degree 2):
`{ξ αⁿ} = {t_n - S_n}`, with no error term, for every `n ≥ 0`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem fract_split (ε : ℕ → Bool) (n : ℕ) :
    Int.fract (piVal P.α ε * P.α ^ n) = Int.fract (tPart P.α ε n - P.sPart ε n) := by
  rw [Int.fract_eq_fract]
  refine ⟨2 * (P.uv ε n).1 + P.a * (P.uv ε n).2, ?_⟩
  have h1 := P.xi_mul_pow ε n
  have h2 := P.aPart_add_sPart ε n
  rw [h1]
  push_cast at h2 ⊢
  linarith [h2]

/-- The window bound `|S_n| ≤ (1+|β|)/(1-|β|)` (M1 Lemma 3, degree 2). -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_sPart_le (ε : ℕ → Bool) (n : ℕ) :
    |P.sPart ε n| ≤ (1 + |P.β|) / (1 - |P.β|) := by
  have hβ := P.abs_beta_lt_one
  have hβ0 : (0 : ℝ) ≤ |P.β| := abs_nonneg _
  have hden : (0 : ℝ) < 1 - |P.β| := by linarith
  induction n with
  | zero =>
      rw [P.sPart_zero, abs_zero]
      positivity
  | succ n ih =>
      rw [P.sPart_succ]
      calc |P.β * P.sPart ε n + (P.β - 1) * dR ε n|
          ≤ |P.β * P.sPart ε n| + |(P.β - 1) * dR ε n| := abs_add_le _ _
      _ = |P.β| * |P.sPart ε n| + |P.β - 1| * |dR ε n| := by rw [abs_mul, abs_mul]
      _ ≤ |P.β| * ((1 + |P.β|) / (1 - |P.β|)) + (1 + |P.β|) * 1 := by
            have h1 : |P.β - 1| ≤ |P.β| + 1 := by
              rcases abs_cases P.β with ⟨h, _⟩ | ⟨h, _⟩ <;>
                rcases abs_cases (P.β - 1) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> linarith
            have h2 : |dR ε n| ≤ 1 := by
              rw [abs_of_nonneg (dR_nonneg ε n)]; exact dR_le_one ε n
            have h3 : (0 : ℝ) ≤ |dR ε n| := abs_nonneg _
            gcongr
            linarith
      _ = (1 + |P.β|) / (1 - |P.β|) := by field_simp; ring

/-- The window as a finite sum over the past digits (M1 Lemma 2):
`S_n = ∑_{m<n} c_m ε_{n-1-m}` with `c_m = (β-1) βᵐ`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem sPart_eq_sum (ε : ℕ → Bool) (n : ℕ) :
    P.sPart ε n = ∑ m ∈ Finset.range n, (P.β - 1) * P.β ^ m * dR ε (n - 1 - m) := by
  induction n with
  | zero => rw [P.sPart_zero, Finset.range_zero, Finset.sum_empty]
  | succ n ih =>
      rw [P.sPart_succ, ih, Finset.sum_range_succ']
      have hterm : ∀ m ∈ Finset.range n,
          (P.β - 1) * P.β ^ (m + 1) * dR ε (n + 1 - 1 - (m + 1))
            = P.β * ((P.β - 1) * P.β ^ m * dR ε (n - 1 - m)) := by
        intro m hm
        have : n + 1 - 1 - (m + 1) = n - 1 - m := by omega
        rw [this, pow_succ']
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      have h0 : (P.β - 1) * P.β ^ 0 * dR ε (n + 1 - 1 - 0) = (P.β - 1) * dR ε n := by
        norm_num
      rw [h0]

end QuadSetup

end BB61
