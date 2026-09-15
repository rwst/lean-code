/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.Bernoulli
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Bugeaud Problem 10.61: the dead zone of a trace ladder

Formal companion of `note-1061-M7.html` (milestone M7 of `plans/plan-1061.html`),
quadratic case.

M1 Lemma 2 (`BB61.QuadSetup.trace_pw`) says that the weight profile of `h F` is, modulo
one, the *single* geometric sequence `h(α-1)α^{-p}` on **both** sides of the origin: the
future weight at depth `p ≥ 1` is `h(α-1)α^{-p}`, and the past weight at depth `m ≥ 0`
is `-h c_m ≡ h(α-1)αᵐ`.  M7's theorem is that along a **trace ladder** — an integer
solution `hₖ` of the minimal-polynomial recurrence `h_{k+2} = a h_{k+1} + b hₖ`,
equivalently `hₖ = Tr(λ αᵏ)` for `λ` in the codifferent — that profile is one fixed
shape carried outward: it is `O(1)` only in two bands of bounded width at depths `±k`
and exponentially small in the whole bulk between them.  So `e(hₖ F)` reads two thin
bands of digits and is constant on everything in between, and `Φ_{hₖ}(μ)` is a
correlation at lag `2k` of two fixed observables.

This file machine-checks the arithmetic half of that statement: the **dead zone**.

* `lad`, `lad_step` — the ladder, and the one-step identity `h_{k+1} - α hₖ = e₀ βᵏ`
  with `e₀ = h₁ - α h₀`.  It holds because `αβ = -b`; no Binet formula is needed, and
  every estimate below is a corollary of it.
* `lad_pow_sub` — `|h_{i+j} - α^i h_j| (α - |β|) ≤ |e₀| |β|^j (α^i - |β|^i)`.
* `bulk_future` — `h_{i+j}(α-1)/α^i` is within `C |β|^j` of the integer `h_{j+1} - h_j`.
  Reading `k = i+j` as the rung and `i` as the future depth: the future weight of the
  mode `hₖ` at depth `i` is exponentially close to an integer as soon as `i` is well
  below `k`, i.e. it carries **no phase** there.
* `abs_beta_mul_alpha`, `bulk_past` — the same on the past side, at a unit (`|b| = 1`),
  where `α|β| = 1` is exactly what stops `αᵐ` from destroying the estimate.  This is why
  M7's plateau is a quadratic-*unit* phenomenon.
* `twoAddSqrt3` instance: the ladder `1, 4, 15, 56, 209, …` of `α = 2 + √3`.

What is **not** formalised here: that the two band shapes converge (an Erdős product),
that they decouple for a mixing measure, and the resulting limit — those are analysis,
and note-1061-M7.html §4–§6 carries them.
-/

namespace BB61

namespace QuadSetup

variable (P : QuadSetup)

/-! ## The ladder and its one-step identity -/

/-- A **trace ladder**: an integer solution of `h_{k+2} = a h_{k+1} + b hₖ`, the
recurrence satisfied by `Tr(λ αᵏ)` for `λ` in the codifferent of `ℚ(α)`. -/
def lad (P : QuadSetup) (h₀ h₁ : ℤ) : ℕ → ℤ
  | 0 => h₀
  | 1 => h₁
  | k + 2 => P.a * lad P h₀ h₁ (k + 1) + P.b * lad P h₀ h₁ k

variable (h₀ h₁ : ℤ)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem lad_zero : P.lad h₀ h₁ 0 = h₀ := rfl

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem lad_one : P.lad h₀ h₁ 1 = h₁ := rfl

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem lad_add_two (k : ℕ) :
    P.lad h₀ h₁ (k + 2) = P.a * P.lad h₀ h₁ (k + 1) + P.b * P.lad h₀ h₁ k := by
  simp [lad]

/-- `αβ = -b`: the product of the two roots. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem alpha_mul_beta : P.α * P.β = -(P.b : ℝ) := by
  have hβ : P.β = (P.a : ℝ) - P.α := rfl
  rw [hβ]; linear_combination -P.root

/-- The initial defect `e₀ = h₁ - α h₀` of the ladder against `α`. -/
noncomputable def ladE : ℝ := (h₁ : ℝ) - P.α * h₀

/-- **The one-step identity.**  `h_{k+1} - α hₖ = e₀ βᵏ`: the defect against `α` is
multiplied by the conjugate at every step, because `αβ = -b`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem lad_step (k : ℕ) :
    (P.lad h₀ h₁ (k + 1) : ℝ) - P.α * P.lad h₀ h₁ k = P.ladE h₀ h₁ * P.β ^ k := by
  induction k with
  | zero => simp [ladE, lad_zero, lad_one]
  | succ k ih =>
      have hβ : P.β = (P.a : ℝ) - P.α := rfl
      have hstep : (P.lad h₀ h₁ (k + 2) : ℝ)
          = (P.a : ℝ) * P.lad h₀ h₁ (k + 1) + (P.b : ℝ) * P.lad h₀ h₁ k := by
        rw [lad_add_two]; push_cast; ring
      have hfac : (P.a : ℝ) * P.lad h₀ h₁ (k + 1) + (P.b : ℝ) * P.lad h₀ h₁ k
              - P.α * P.lad h₀ h₁ (k + 1)
            = P.β * ((P.lad h₀ h₁ (k + 1) : ℝ) - P.α * P.lad h₀ h₁ k) := by
        rw [hβ]; linear_combination (-(P.lad h₀ h₁ k : ℝ)) * P.root
      rw [hstep, hfac, ih, pow_succ]; ring

/-! ## The dead zone -/

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem alpha_sub_abs_beta_pos : 0 < P.α - |P.β| := by
  have h1 := P.one_lt
  have h2 := P.abs_beta_lt_one
  linarith

/-- Dividing the rung `h_{i+j}` down by `α^i` lands within `O(|β|^j)` of the rung `h_j`:
the ladder is self-similar under multiplication by `α`, with a geometric error governed
by the conjugate.  Stated without division, so that no positivity side conditions are
needed. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem lad_pow_sub (j i : ℕ) :
    |(P.lad h₀ h₁ (i + j) : ℝ) - P.α ^ i * P.lad h₀ h₁ j| * (P.α - |P.β|)
      ≤ |P.ladE h₀ h₁| * |P.β| ^ j * (P.α ^ i - |P.β| ^ i) := by
  have hα : (0 : ℝ) < P.α := P.alpha_pos
  have hpos := P.alpha_sub_abs_beta_pos
  have hβ0 : (0 : ℝ) ≤ |P.β| := abs_nonneg _
  induction i with
  | zero => simp
  | succ i ih =>
      set D : ℝ := (P.lad h₀ h₁ (i + j) : ℝ) - P.α ^ i * P.lad h₀ h₁ j with hD
      have hrec : (P.lad h₀ h₁ (i + 1 + j) : ℝ) - P.α ^ (i + 1) * P.lad h₀ h₁ j
          = P.α * D + P.ladE h₀ h₁ * P.β ^ (i + j) := by
        have hij : i + 1 + j = (i + j) + 1 := by ring
        have hs := P.lad_step h₀ h₁ (i + j)
        rw [hij, hD, pow_succ]
        linear_combination hs
      have habs : |P.α * D + P.ladE h₀ h₁ * P.β ^ (i + j)|
          ≤ P.α * |D| + |P.ladE h₀ h₁| * (|P.β| ^ j * |P.β| ^ i) := by
        calc |P.α * D + P.ladE h₀ h₁ * P.β ^ (i + j)|
            ≤ |P.α * D| + |P.ladE h₀ h₁ * P.β ^ (i + j)| := abs_add_le _ _
          _ = P.α * |D| + |P.ladE h₀ h₁| * (|P.β| ^ j * |P.β| ^ i) := by
              rw [abs_mul, abs_mul, abs_pow, abs_of_pos hα, pow_add]; ring
      have hEβ : (0 : ℝ) ≤ |P.ladE h₀ h₁| * |P.β| ^ j := by positivity
      have hgeo : P.α * (|P.ladE h₀ h₁| * |P.β| ^ j * (P.α ^ i - |P.β| ^ i))
            + |P.ladE h₀ h₁| * |P.β| ^ j * |P.β| ^ i * (P.α - |P.β|)
          = |P.ladE h₀ h₁| * |P.β| ^ j * (P.α ^ (i + 1) - |P.β| ^ (i + 1)) := by
        rw [pow_succ, pow_succ]; ring
      rw [hrec]
      calc |P.α * D + P.ladE h₀ h₁ * P.β ^ (i + j)| * (P.α - |P.β|)
          ≤ (P.α * |D| + |P.ladE h₀ h₁| * (|P.β| ^ j * |P.β| ^ i)) * (P.α - |P.β|) :=
            mul_le_mul_of_nonneg_right habs hpos.le
        _ = P.α * (|D| * (P.α - |P.β|))
              + |P.ladE h₀ h₁| * |P.β| ^ j * |P.β| ^ i * (P.α - |P.β|) := by ring
        _ ≤ P.α * (|P.ladE h₀ h₁| * |P.β| ^ j * (P.α ^ i - |P.β| ^ i))
              + |P.ladE h₀ h₁| * |P.β| ^ j * |P.β| ^ i * (P.α - |P.β|) := by
            have := mul_le_mul_of_nonneg_left ih hα.le
            linarith
        _ = |P.ladE h₀ h₁| * |P.β| ^ j * (P.α ^ (i + 1) - |P.β| ^ (i + 1)) := hgeo

/-- **The future dead zone.**  The weight of the ladder mode `h_{i+j}` at future depth
`i` is within `C |β|^j` of an integer — so for `i` well below the rung index it carries
no phase at all.  The integer is the ladder's own first difference `h_{j+1} - h_j`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem bulk_future (j i : ℕ) :
    ∃ N : ℤ, |(P.lad h₀ h₁ (i + j) : ℝ) * (P.α - 1) / P.α ^ i - (N : ℝ)|
      ≤ |P.ladE h₀ h₁| * |P.β| ^ j * (1 + (P.α - 1) / (P.α - |P.β|)) := by
  have hα : (0 : ℝ) < P.α := P.alpha_pos
  have hpos := P.alpha_sub_abs_beta_pos
  have hαi : (0 : ℝ) < P.α ^ i := by positivity
  refine ⟨P.lad h₀ h₁ (j + 1) - P.lad h₀ h₁ j, ?_⟩
  set D : ℝ := (P.lad h₀ h₁ (i + j) : ℝ) - P.α ^ i * P.lad h₀ h₁ j with hD
  have hs := P.lad_step h₀ h₁ j
  have hsplit : (P.lad h₀ h₁ (i + j) : ℝ) * (P.α - 1) / P.α ^ i
        - ((P.lad h₀ h₁ (j + 1) - P.lad h₀ h₁ j : ℤ) : ℝ)
      = (P.α - 1) * D / P.α ^ i - P.ladE h₀ h₁ * P.β ^ j := by
    rw [hD]
    push_cast
    field_simp
    linear_combination (-(P.α ^ i)) * hs
  rw [hsplit]
  set E : ℝ := |P.ladE h₀ h₁| * |P.β| ^ j with hE
  have hE0 : (0 : ℝ) ≤ E := by rw [hE]; positivity
  have hone : (0 : ℝ) < P.α - 1 := by linarith [P.one_lt]
  have h1 : |(P.α - 1) * D / P.α ^ i - P.ladE h₀ h₁ * P.β ^ j|
      ≤ (P.α - 1) * |D| / P.α ^ i + E := by
    have hq : |(P.α - 1) * D / P.α ^ i| = (P.α - 1) * |D| / P.α ^ i := by
      rw [abs_div, abs_mul, abs_pow, abs_of_pos hα, abs_of_pos hone]
    have hr : |P.ladE h₀ h₁ * P.β ^ j| = E := by rw [hE, abs_mul, abs_pow]
    calc |(P.α - 1) * D / P.α ^ i - P.ladE h₀ h₁ * P.β ^ j|
        ≤ |(P.α - 1) * D / P.α ^ i| + |P.ladE h₀ h₁ * P.β ^ j| := abs_sub _ _
      _ = (P.α - 1) * |D| / P.α ^ i + E := by rw [hq, hr]
  have h2 : |D| * (P.α - |P.β|) ≤ E * (P.α ^ i - |P.β| ^ i) := P.lad_pow_sub h₀ h₁ j i
  have hbi : (0 : ℝ) ≤ |P.β| ^ i := pow_nonneg (abs_nonneg _) i
  have hDle : |D| ≤ E * P.α ^ i / (P.α - |P.β|) := by
    rw [le_div_iff₀ hpos]
    nlinarith [mul_nonneg hE0 hbi]
  have h3 : (P.α - 1) * |D| / P.α ^ i ≤ E * ((P.α - 1) / (P.α - |P.β|)) := by
    rw [div_le_iff₀ hαi]
    have hm := mul_le_mul_of_nonneg_left hDle hone.le
    have hid : (P.α - 1) * (E * P.α ^ i / (P.α - |P.β|))
        = E * ((P.α - 1) / (P.α - |P.β|)) * P.α ^ i := by
      field_simp
    calc (P.α - 1) * |D| ≤ (P.α - 1) * (E * P.α ^ i / (P.α - |P.β|)) := hm
      _ = E * ((P.α - 1) / (P.α - |P.β|)) * P.α ^ i := hid
  have hfin : E * ((P.α - 1) / (P.α - |P.β|)) + E
      = E * (1 + (P.α - 1) / (P.α - |P.β|)) := by ring
  linarith [h1, h3]

/-! ## The dead zone, past side -/

/-- At a **unit** (`|b| = 1`) the two roots have `α|β| = 1`.  This is exactly what keeps
the past estimate alive: `|β|ᵏ αᵐ = α^{m-k}`, so the past weight decays as soon as the
depth `m` is below the rung index `k`.  At degree `≥ 3` no such identity is available,
and M7's plateau disappears. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem alpha_mul_abs_beta (hb : |(P.b : ℝ)| = 1) : P.α * |P.β| = 1 := by
  have h := P.alpha_mul_beta
  have : |P.α * P.β| = |(P.b : ℝ)| := by rw [h, abs_neg]
  rwa [abs_mul, abs_of_pos P.alpha_pos, hb] at this

/-- **The past dead zone.**  By M1 Lemma 2 the past weight of the mode `h` at depth `m`
is `-h c_m ≡ h(α-1)αᵐ` mod one; along the ladder that quantity is within
`|e₀| |β|ᵏ αᵐ · C` of an integer, so — at a unit, where `|β|ᵏαᵐ = α^{m-k}` — it too
carries no phase for `m` well below the rung index `k`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem bulk_past (k m : ℕ) :
    ∃ N : ℤ, |(P.lad h₀ h₁ k : ℝ) * (P.α - 1) * P.α ^ m - (N : ℝ)|
      ≤ |P.ladE h₀ h₁| * (|P.β| ^ k * P.α ^ m) * (1 + (P.α - 1) / (P.α - |P.β|)) := by
  have hα : (0 : ℝ) < P.α := P.alpha_pos
  have hpos := P.alpha_sub_abs_beta_pos
  have hone : (0 : ℝ) < P.α - 1 := by linarith [P.one_lt]
  have hαm : (0 : ℝ) < P.α ^ m := by positivity
  refine ⟨P.lad h₀ h₁ (m + k + 1) - P.lad h₀ h₁ (m + k), ?_⟩
  set E : ℝ := |P.ladE h₀ h₁| with hEdef
  set D : ℝ := (P.lad h₀ h₁ (m + k) : ℝ) - P.α ^ m * P.lad h₀ h₁ k with hD
  have hs := P.lad_step h₀ h₁ (m + k)
  have hsplit : (P.lad h₀ h₁ k : ℝ) * (P.α - 1) * P.α ^ m
        - ((P.lad h₀ h₁ (m + k + 1) - P.lad h₀ h₁ (m + k) : ℤ) : ℝ)
      = -(P.α - 1) * D - P.ladE h₀ h₁ * P.β ^ (m + k) := by
    rw [hD]; push_cast; linear_combination -hs
  rw [hsplit]
  have hDb : |D| * (P.α - |P.β|) ≤ E * |P.β| ^ k * (P.α ^ m - |P.β| ^ m) :=
    P.lad_pow_sub h₀ h₁ k m
  have hE0 : (0 : ℝ) ≤ E := abs_nonneg _
  have hbk : (0 : ℝ) ≤ |P.β| ^ k := pow_nonneg (abs_nonneg _) k
  have hbm : (0 : ℝ) ≤ |P.β| ^ m := pow_nonneg (abs_nonneg _) m
  have hDle : |D| ≤ E * |P.β| ^ k * P.α ^ m / (P.α - |P.β|) := by
    rw [le_div_iff₀ hpos]
    nlinarith [mul_nonneg (mul_nonneg hE0 hbk) hbm]
  have h1 : |-(P.α - 1) * D - P.ladE h₀ h₁ * P.β ^ (m + k)|
      ≤ (P.α - 1) * |D| + E * (|P.β| ^ m * |P.β| ^ k) := by
    calc |-(P.α - 1) * D - P.ladE h₀ h₁ * P.β ^ (m + k)|
        ≤ |-(P.α - 1) * D| + |P.ladE h₀ h₁ * P.β ^ (m + k)| := abs_sub _ _
      _ = (P.α - 1) * |D| + E * (|P.β| ^ m * |P.β| ^ k) := by
          rw [abs_mul, abs_mul, abs_neg, abs_pow, abs_of_pos hone, pow_add, hEdef]
  have hmono : |P.β| ^ m ≤ P.α ^ m :=
    pow_le_pow_left₀ (abs_nonneg _) (by linarith [P.abs_beta_lt_one, P.one_lt]) m
  have hterm : E * (|P.β| ^ m * |P.β| ^ k) ≤ E * (|P.β| ^ k * P.α ^ m) := by
    have := mul_le_mul_of_nonneg_right hmono hbk
    nlinarith
  have h3 : (P.α - 1) * |D| ≤ E * (|P.β| ^ k * P.α ^ m) * ((P.α - 1) / (P.α - |P.β|)) := by
    have hm := mul_le_mul_of_nonneg_left hDle hone.le
    have hid : (P.α - 1) * (E * |P.β| ^ k * P.α ^ m / (P.α - |P.β|))
        = E * (|P.β| ^ k * P.α ^ m) * ((P.α - 1) / (P.α - |P.β|)) := by
      field_simp
    linarith [hm, hid.le, hid.ge]
  nlinarith [h1, h3, hterm]

/-! ## An instance: the ladder `1, 4, 15, 56, 209, …` of `α = 2 + √3` -/

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem twoAddSqrt3_lad_four : twoAddSqrt3.lad 1 4 4 = 209 := by
  have h2 : twoAddSqrt3.lad 1 4 2 = 15 := by simp [lad, twoAddSqrt3]
  have h3 : twoAddSqrt3.lad 1 4 3 = 56 := by
    rw [show (3 : ℕ) = 1 + 2 by rfl, lad_add_two, h2]; simp [lad, twoAddSqrt3]
  rw [show (4 : ℕ) = 2 + 2 by rfl, lad_add_two, h3, h2]; simp [twoAddSqrt3]

/-- The seed `(1,4)` has defect `e₀ = 4 - α = β`, so the ladder estimate at `2+√3` is
governed by the conjugate alone. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem twoAddSqrt3_ladE : twoAddSqrt3.ladE 1 4 = twoAddSqrt3.β := by
  rw [ladE, twoAddSqrt3_beta, twoAddSqrt3_alpha]; push_cast; ring

/-- The dead zone at `α = 2+√3`, with a clean constant: the future weight of the ladder
mode `h_{i+j}` at depth `i` is within `(2-√3)^j` of an integer. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem bulk_future_twoAddSqrt3 (j i : ℕ) :
    ∃ N : ℤ, |(twoAddSqrt3.lad 1 4 (i + j) : ℝ) * (twoAddSqrt3.α - 1) / twoAddSqrt3.α ^ i
        - (N : ℝ)| ≤ (2 - Real.sqrt 3) ^ j := by
  obtain ⟨N, hN⟩ := twoAddSqrt3.bulk_future 1 4 j i
  refine ⟨N, hN.trans ?_⟩
  have hs1 := sqrt3_lt
  have hs2 := lt_sqrt3
  have hβ : twoAddSqrt3.β = 2 - Real.sqrt 3 := twoAddSqrt3_beta
  have habs : |twoAddSqrt3.β| = 2 - Real.sqrt 3 := by
    rw [hβ, abs_of_pos (by linarith)]
  have hE : |twoAddSqrt3.ladE 1 4| = 2 - Real.sqrt 3 := by
    rw [twoAddSqrt3_ladE, habs]
  have hα : twoAddSqrt3.α = 2 + Real.sqrt 3 := twoAddSqrt3_alpha
  have hc : |twoAddSqrt3.ladE 1 4| * (1 + (twoAddSqrt3.α - 1)
      / (twoAddSqrt3.α - |twoAddSqrt3.β|)) ≤ 1 := by
    rw [hE, habs, hα]
    have ht : (0 : ℝ) < Real.sqrt 3 := by linarith
    have hsq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    have key : (2 - Real.sqrt 3) * (1 + (2 + Real.sqrt 3 - 1)
        / (2 + Real.sqrt 3 - (2 - Real.sqrt 3)))
        = (2 - Real.sqrt 3) * (3 * Real.sqrt 3 + 1) / (2 * Real.sqrt 3) := by
      have hd : (2 + Real.sqrt 3 - (2 - Real.sqrt 3)) = 2 * Real.sqrt 3 := by ring
      rw [hd]; field_simp; ring
    rw [key, div_le_one (by positivity)]
    nlinarith [hs1, hs2, hsq]
  have hpow : (0 : ℝ) ≤ |twoAddSqrt3.β| ^ j := pow_nonneg (abs_nonneg _) j
  calc |twoAddSqrt3.ladE 1 4| * |twoAddSqrt3.β| ^ j
        * (1 + (twoAddSqrt3.α - 1) / (twoAddSqrt3.α - |twoAddSqrt3.β|))
      = (|twoAddSqrt3.ladE 1 4| * (1 + (twoAddSqrt3.α - 1)
          / (twoAddSqrt3.α - |twoAddSqrt3.β|))) * |twoAddSqrt3.β| ^ j := by ring
    _ ≤ 1 * |twoAddSqrt3.β| ^ j := mul_le_mul_of_nonneg_right hc hpow
    _ = (2 - Real.sqrt 3) ^ j := by rw [one_mul, habs]


end QuadSetup

end BB61
