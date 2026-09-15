/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.Ladder
import BB61.Factor
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# M1 Observation 16: why there is a plateau, and only at quadratic units

Formal companion of `note-1061-M1.html` §6, Observation 16 — the mechanism behind M0's
empirical "`ρ ≥ 1/α` with equality iff quadratic unit; the ladder is quadratic-unit-only".

> **Observation 16.** (i) Along a ladder the future factor and the past factor of the
> Bernoulli(½) Weyl limit converge to the *same* value `L`, so the plateau is `L²`.
> (ii) This happens exactly when `α` is a quadratic **unit**.

Part (i) is an observation supported by numerics; part (ii) is its mechanism, and (ii) is
what is proved here, in a sharper form than the note states it.

## The two profiles

`BB61/Ladder.lean` (M7) shows the weight profile of a ladder mode `hₖ` is `O(1)` only in two
bands, at future depth `≈ k` and past depth `≈ k`.  This file identifies the **shape** of
each band, exactly rather than up to a constant.  With
`e₀ = h₁ - α h₀`, `f₀ = h₁ - β h₀` and Binet in its division-free form
`(α-β)hₖ = f₀αᵏ - e₀βᵏ` (`lad_binet`, two lines from `lad_step` and its conjugate
`lad_conj_step`):

* `abs_future_sub_shape` — the future weight at depth `j` is `A α^{k-j}` up to
  `|e₀|(α-1)ρᵏ/((α-β)αʲ)`, where `A = f₀(α-1)/(α-β)`;
* `abs_past_sub_shape` — the past weight `hₖ c_m` is `(-b)ᵐ B α^{k-m}` up to
  `|e₀||β-1|ρ^{k+m}/(α-β)`, where `B = f₀(β-1)/(α-β)`.

Both are **equalities**, not estimates.

## The mirror, and where the hypothesis is spent

`abs_shapePast_profile` is the conclusion: the past profile equals the future profile times
`|b|ᵈ·|β-1|/(α-1)` — at every rung and every depth.  So the two profiles are **one shape read
in opposite directions exactly when `|b| = 1`**, i.e. exactly at a quadratic unit; off a unit
the factor `|b|ᵈ` grows and they part company exponentially in the depth.  The dichotomy is
`abs_beta_eq_inv_alpha_iff` (`ρ = 1/α ↔ |b| = 1`) and `inv_alpha_lt_abs_beta`
(`ρ > 1/α` strictly when `|b| ≥ 2`), off the single identity `αρ = |b|`.

`lad_mul_beta_pow` is the note's own reflection identity, division-free: with `k = m + n`,
`(α-β)(h_{m+n}βᵐ - (-b)ᵐhₙ) = e₀((-b)ᵐβⁿ - β^{n+2m})`,
and `abs_lad_mul_beta_pow_sub_int` its consequence at a unit — `(-b)ᵐh_{k-m}` is an *integer*
and `hₖβᵐ` sits within `|e₀|(ρ^{k-m} + ρ^{k+m})/(α-β)` of it.  That is the note's
`‖hₖα₂ᵐ‖ ≤ |λ'|(ρ^{k-m} + ρ^{k+m})`, with `λ' = -e₀/(α-β)`.

## What this adds to the note

**The note treats (i) as one phenomenon; it is two.**

* At a quadratic unit of **norm `+1`** there is no limit to take at all.  `past_eq_future`
  (M5 Thm 7, `BB61/Bernoulli.lean`) says `c_m = -(α-1)/α^{m+1}` exactly, so the past weight
  of *any* mode at depth `m` is minus its future weight at depth `m+1`
  (`past_weight_eq_neg_future_weight`), and the two one-sided products are equal **term by
  term**, at every rung.  `shapePast_eq_of_norm_one`: `B = -A/α`.
* At a quadratic unit of **norm `-1`** a limit is genuinely involved, and it converges at
  rate `ρ^{2k}`: `abs_future_band` and `abs_past_band` say each band is within
  `C ρ^{2k}/α^{offset}` of a *fixed* shape.  The note states no rate.

Both are confirmed numerically by `BB61/m1_obs16.py` (mpmath at adaptive precision — in
`float64` the check dies at `k ≈ 16/log₁₀α`, the note's own F10 trap): at norms `+1` the two
factors agree to working precision at every `k`, at norm `-1` `|future - past|` decays by
exactly `ρ²` per rung, and at non-units the past factor collapses to `0` while the future one
settles.

What is **not** formalised: the convergence of the products themselves, i.e. Observation
16(i) as stated.  That needs infinite-product analysis on top of the profiles proved here;
`BB61/Bernoulli.lean` carries the non-vanishing of the individual factors.

## References

* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, CUP 2012,
  Problem 10.61.
* `note-1061-M1.html` §6 (Observation 16), `note-1061-M7.html` §4–§6 (the analysis),
  `note-1061-M5.html` (Route E and the folding at norm `+1`).
-/

namespace BB61

namespace QuadSetup

variable (P : QuadSetup) (h₀ h₁ : ℤ)

/-! ## The conjugate defect, and Binet without division -/

/-- The **conjugate defect** `f₀ = h₁ - β h₀` of the ladder against `β`, the mirror of
`ladE = h₁ - α h₀`. -/
noncomputable def ladF : ℝ := (h₁ : ℝ) - P.β * h₀

/-- The one-step identity at the conjugate: `h_{k+1} - β hₖ = f₀ αᵏ`.  The mirror of
`lad_step`, and it holds for the same reason, `αβ = -b`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem lad_conj_step (k : ℕ) :
    (P.lad h₀ h₁ (k + 1) : ℝ) - P.β * P.lad h₀ h₁ k = P.ladF h₀ h₁ * P.α ^ k := by
  induction k with
  | zero => simp [ladF, lad_zero, lad_one]
  | succ k ih =>
      have hstep : (P.lad h₀ h₁ (k + 2) : ℝ)
          = (P.a : ℝ) * P.lad h₀ h₁ (k + 1) + (P.b : ℝ) * P.lad h₀ h₁ k := by
        rw [lad_add_two]; push_cast; ring
      have hβ : P.β = (P.a : ℝ) - P.α := rfl
      have hfac : (P.a : ℝ) * P.lad h₀ h₁ (k + 1) + (P.b : ℝ) * P.lad h₀ h₁ k
              - P.β * P.lad h₀ h₁ (k + 1)
            = P.α * ((P.lad h₀ h₁ (k + 1) : ℝ) - P.β * P.lad h₀ h₁ k) := by
        rw [hβ]
        linear_combination (-(P.lad h₀ h₁ k : ℝ)) * P.root
      rw [hstep, hfac, ih, pow_succ]
      ring

/-- **Binet, without division**: `(α - β) hₖ = f₀ αᵏ - e₀ βᵏ`.  Two lines from the two
one-step identities, and the only place where a "closed form" for the ladder is needed. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem lad_binet (k : ℕ) :
    (P.α - P.β) * P.lad h₀ h₁ k = P.ladF h₀ h₁ * P.α ^ k - P.ladE h₀ h₁ * P.β ^ k := by
  have h1 := P.lad_step h₀ h₁ k
  have h2 := P.lad_conj_step h₀ h₁ k
  linarith

variable {P}

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem alpha_sub_beta_pos : 0 < P.α - P.β := by
  have h1 := P.one_lt
  have h2 := P.abs_beta_lt_one
  have h3 : P.β ≤ |P.β| := le_abs_self _
  linarith

/-! ## The unit dichotomy: `ρ = 1/α` exactly at a unit -/

/-- `α ρ = |b|`, so the conjugate modulus is pinned by the norm. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem alpha_mul_abs_beta_eq : P.α * |P.β| = |(P.b : ℝ)| := by
  have h := P.alpha_mul_beta
  have habs : |P.α * P.β| = |(P.b : ℝ)| := by rw [h, abs_neg]
  rwa [abs_mul, abs_of_pos P.alpha_pos] at habs

/-- `ρⁿ = |b|ⁿ / αⁿ`: every conjugate power is a power of `1/α` corrected by the norm. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_beta_pow (n : ℕ) : |P.β| ^ n = |(P.b : ℝ)| ^ n / P.α ^ n := by
  have h := alpha_mul_abs_beta_eq (P := P)
  have hα : (0 : ℝ) < P.α := P.alpha_pos
  field_simp
  rw [← mul_pow, mul_comm (|P.β|) P.α, h]

/-- **`ρ = 1/α` if and only if `α` is a unit.**  This is the whole of Observation 16(ii)'s
dichotomy: the mirror symmetry below needs `α ρ = 1`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_beta_eq_inv_alpha_iff : |P.β| = P.α⁻¹ ↔ |(P.b : ℝ)| = 1 := by
  have hα : (0 : ℝ) < P.α := P.alpha_pos
  rw [← alpha_mul_abs_beta_eq (P := P)]
  constructor
  · intro h; rw [h, mul_inv_cancel₀ hα.ne']
  · intro h
    field_simp at h ⊢
    linarith [h]

/-- Off a unit the conjugate is strictly larger than `1/α` — the note's "`ρ > 1/α`
strictly". -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem inv_alpha_lt_abs_beta (hb : (2 : ℝ) ≤ |(P.b : ℝ)|) : P.α⁻¹ < |P.β| := by
  have hα : (0 : ℝ) < P.α := P.alpha_pos
  have h := alpha_mul_abs_beta_eq (P := P)
  rw [inv_lt_iff_one_lt_mul₀ hα]
  nlinarith [h]

/-! ## Observation 16(ii): the reflection identity -/

variable (P)

/-- `α^{m+n} βᵐ = (-b)ᵐ αⁿ`: multiplication by `β` is multiplication by `α⁻¹` up to the
norm.  Written without subtraction, `n` being the reflected depth `k - m`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem alpha_pow_mul_beta_pow (n m : ℕ) :
    P.α ^ (m + n) * P.β ^ m = (-(P.b : ℝ)) ^ m * P.α ^ n := by
  rw [pow_add]
  calc P.α ^ m * P.α ^ n * P.β ^ m = (P.α * P.β) ^ m * P.α ^ n := by rw [mul_pow]; ring
    _ = (-(P.b : ℝ)) ^ m * P.α ^ n := by rw [P.alpha_mul_beta]

/-- **The reflection identity** — M1 Observation 16(ii).  With `k = m + n`, so that `n` is
the reflected depth `k - m`,
`(α-β)(h_{m+n} βᵐ - (-b)ᵐ hₙ) = e₀ ((-b)ᵐ βⁿ - β^{n+2m})`.
The note derives it from Binet with `λ' = -e₀/(α-β)`; here it is division-free. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem lad_mul_beta_pow (n m : ℕ) :
    (P.α - P.β) * ((P.lad h₀ h₁ (m + n) : ℝ) * P.β ^ m
        - (-(P.b : ℝ)) ^ m * P.lad h₀ h₁ n)
      = P.ladE h₀ h₁ * ((-(P.b : ℝ)) ^ m * P.β ^ n - P.β ^ (n + 2 * m)) := by
  have h1 := P.lad_binet h₀ h₁ (m + n)
  have h2 := P.lad_binet h₀ h₁ n
  have hab := P.alpha_pow_mul_beta_pow n m
  have hβ : P.β ^ (m + n) * P.β ^ m = P.β ^ (n + 2 * m) := by
    rw [← pow_add]
    congr 1
    omega
  calc (P.α - P.β) * ((P.lad h₀ h₁ (m + n) : ℝ) * P.β ^ m
          - (-(P.b : ℝ)) ^ m * P.lad h₀ h₁ n)
      = ((P.α - P.β) * P.lad h₀ h₁ (m + n)) * P.β ^ m
          - (-(P.b : ℝ)) ^ m * ((P.α - P.β) * P.lad h₀ h₁ n) := by ring
    _ = (P.ladF h₀ h₁ * P.α ^ (m + n) - P.ladE h₀ h₁ * P.β ^ (m + n)) * P.β ^ m
          - (-(P.b : ℝ)) ^ m * (P.ladF h₀ h₁ * P.α ^ n - P.ladE h₀ h₁ * P.β ^ n) := by
        rw [h1, h2]
    _ = P.ladF h₀ h₁ * (P.α ^ (m + n) * P.β ^ m)
          - P.ladE h₀ h₁ * (P.β ^ (m + n) * P.β ^ m)
          - (-(P.b : ℝ)) ^ m * P.ladF h₀ h₁ * P.α ^ n
          + (-(P.b : ℝ)) ^ m * P.ladE h₀ h₁ * P.β ^ n := by ring
    _ = P.ladF h₀ h₁ * ((-(P.b : ℝ)) ^ m * P.α ^ n)
          - P.ladE h₀ h₁ * P.β ^ (n + 2 * m)
          - (-(P.b : ℝ)) ^ m * P.ladF h₀ h₁ * P.α ^ n
          + (-(P.b : ℝ)) ^ m * P.ladE h₀ h₁ * P.β ^ n := by rw [hab, hβ]
    _ = P.ladE h₀ h₁ * ((-(P.b : ℝ)) ^ m * P.β ^ n - P.β ^ (n + 2 * m)) := by ring

/-- **Observation 16(ii), the bound.**  At a quadratic unit the reflected rung
`(-b)ᵐ h_{k-m}` is an *integer* and `hₖ βᵐ` sits within `|e₀|(ρ^{k-m} + ρ^{k+m})/(α-β)`
of it: the past coordinates of the mode `hₖ` are near-integral exactly as far as the
future ones are. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_lad_mul_beta_pow_sub_int (hb : |(P.b : ℝ)| = 1) (n m : ℕ) :
    |(P.lad h₀ h₁ (m + n) : ℝ) * P.β ^ m - (((-P.b) ^ m * P.lad h₀ h₁ n : ℤ) : ℝ)|
      ≤ |P.ladE h₀ h₁| * (|P.β| ^ n + |P.β| ^ (n + 2 * m)) / (P.α - P.β) := by
  have hu := alpha_sub_beta_pos (P := P)
  have hcast : (((-P.b) ^ m * P.lad h₀ h₁ n : ℤ) : ℝ)
      = (-(P.b : ℝ)) ^ m * P.lad h₀ h₁ n := by push_cast; ring
  rw [hcast, le_div_iff₀ hu, mul_comm _ (P.α - P.β), ← abs_of_pos hu, ← abs_mul,
    P.lad_mul_beta_pow h₀ h₁ n m, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc |(-(P.b : ℝ)) ^ m * P.β ^ n - P.β ^ (n + 2 * m)|
      ≤ |(-(P.b : ℝ)) ^ m * P.β ^ n| + |P.β ^ (n + 2 * m)| := abs_sub _ _
    _ = |P.β| ^ n + |P.β| ^ (n + 2 * m) := by
        rw [abs_mul, abs_pow, abs_pow, abs_pow, abs_neg, hb, one_pow, one_mul]

/-! ## The two profiles, and the mirror -/

/-- The **future shape** `A = f₀(α-1)/(α-β)`: the limit profile of the future weights of a
ladder mode, read at offset `t` from the rung as `A/αᵗ`. -/
noncomputable def shapeFut : ℝ := P.ladF h₀ h₁ * (P.α - 1) / (P.α - P.β)

/-- The **past shape** `B = f₀(β-1)/(α-β)`. -/
noncomputable def shapePast : ℝ := P.ladF h₀ h₁ * (P.β - 1) / (P.α - P.β)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem shapeFut_mul : P.shapeFut h₀ h₁ * (P.α - P.β) = P.ladF h₀ h₁ * (P.α - 1) := by
  rw [shapeFut, div_mul_cancel₀ _ (ne_of_gt (alpha_sub_beta_pos (P := P)))]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem shapePast_mul : P.shapePast h₀ h₁ * (P.α - P.β) = P.ladF h₀ h₁ * (P.β - 1) := by
  rw [shapePast, div_mul_cancel₀ _ (ne_of_gt (alpha_sub_beta_pos (P := P)))]

/-- **The future profile, exactly.**  The future weight of the rung `hₖ` at depth `j` is
`A α^{k-j}` up to `|e₀|(α-1)ρᵏ/((α-β)αʲ)` — an equality, not an estimate. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_future_sub_shape (k j : ℕ) :
    |(P.lad h₀ h₁ k : ℝ) * (P.α - 1) / P.α ^ j - P.shapeFut h₀ h₁ * P.α ^ k / P.α ^ j|
      = |P.ladE h₀ h₁| * (P.α - 1) * |P.β| ^ k / ((P.α - P.β) * P.α ^ j) := by
  have hu := alpha_sub_beta_pos (P := P)
  have hα : (0 : ℝ) < P.α := P.alpha_pos
  have hone : (0 : ℝ) < P.α - 1 := by linarith [P.one_lt]
  have hαj : (0 : ℝ) < P.α ^ j := by positivity
  have hbin := P.lad_binet h₀ h₁ k
  have hsh := P.shapeFut_mul h₀ h₁
  have step2 : (P.lad h₀ h₁ k : ℝ) * (P.α - 1) - P.shapeFut h₀ h₁ * P.α ^ k
      = -(P.ladE h₀ h₁ * P.β ^ k * (P.α - 1)) / (P.α - P.β) := by
    rw [eq_div_iff (ne_of_gt hu)]
    linear_combination (P.α - 1) * hbin - P.α ^ k * hsh
  have hkey : (P.lad h₀ h₁ k : ℝ) * (P.α - 1) / P.α ^ j - P.shapeFut h₀ h₁ * P.α ^ k / P.α ^ j
      = -(P.ladE h₀ h₁ * P.β ^ k * (P.α - 1)) / ((P.α - P.β) * P.α ^ j) := by
    rw [div_sub_div_same, step2, div_div]
  rw [hkey, abs_div, abs_neg, abs_mul, abs_mul, abs_pow,
    abs_of_pos (show (0 : ℝ) < (P.α - P.β) * P.α ^ j by positivity), abs_of_pos hone]
  ring

/-- `(-b)ᵐ αᵏ/αᵐ = αᵏ βᵐ`: the reflected shape written on the future side. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem neg_b_pow_mul_div (k m : ℕ) :
    (-(P.b : ℝ)) ^ m * P.α ^ k / P.α ^ m = P.α ^ k * P.β ^ m := by
  have hα : (0 : ℝ) < P.α := P.alpha_pos
  rw [← P.alpha_mul_beta, mul_pow]
  field_simp

/-- **The past profile, exactly.**  The past weight `hₖ c_m` is `(-b)ᵐ B α^{k-m}` up to
`|e₀||β-1|ρ^{k+m}/(α-β)`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_past_sub_shape (k m : ℕ) :
    |(P.lad h₀ h₁ k : ℝ) * P.cCoef m
        - P.shapePast h₀ h₁ * ((-(P.b : ℝ)) ^ m * P.α ^ k / P.α ^ m)|
      = |P.ladE h₀ h₁| * |P.β - 1| * |P.β| ^ (k + m) / (P.α - P.β) := by
  have hu := alpha_sub_beta_pos (P := P)
  have hbin := P.lad_binet h₀ h₁ k
  have hsh := P.shapePast_mul h₀ h₁
  have hkey : (P.lad h₀ h₁ k : ℝ) * P.cCoef m
        - P.shapePast h₀ h₁ * ((-(P.b : ℝ)) ^ m * P.α ^ k / P.α ^ m)
      = -(P.ladE h₀ h₁ * (P.β ^ k * P.β ^ m) * (P.β - 1)) / (P.α - P.β) := by
    rw [P.neg_b_pow_mul_div k m, cCoef, eq_div_iff (ne_of_gt hu)]
    linear_combination (P.β - 1) * P.β ^ m * hbin - P.α ^ k * P.β ^ m * hsh
  rw [hkey, ← pow_add, abs_div, abs_neg, abs_mul, abs_mul, abs_pow, abs_of_pos hu]
  ring

/-- **The mirror image** — the conclusion of M1 Observation 16(ii).  The past profile is the
future profile multiplied by `|b|ᵈ·|β-1|/(α-1)`, at every rung `k` and every depth `d`.  At a
quadratic unit that factor is the **constant** `|β-1|/(α-1)`, so the two profiles are one
shape read in opposite directions; off a unit it grows like `|b|ᵈ` and the past profile parts
company with the future one exponentially in the depth. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_shapePast_profile (k d : ℕ) :
    |P.shapePast h₀ h₁ * ((-(P.b : ℝ)) ^ d * P.α ^ k / P.α ^ d)|
      = |(P.b : ℝ)| ^ d * (|P.β - 1| / (P.α - 1))
          * |P.shapeFut h₀ h₁ * P.α ^ k / P.α ^ d| := by
  have hu := alpha_sub_beta_pos (P := P)
  have hα : (0 : ℝ) < P.α := P.alpha_pos
  have hone : (0 : ℝ) < P.α - 1 := by linarith [P.one_lt]
  simp only [shapePast, shapeFut, abs_mul, abs_div, abs_pow, abs_neg,
    abs_of_pos hu, abs_of_pos hα, abs_of_pos hone]
  field_simp

/-! ## At a unit: the band, and the rate `ρ^{2k}` -/

/-- At a unit `ρⁿ = α^{-n}`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_beta_pow_unit (hb : |(P.b : ℝ)| = 1) (n : ℕ) : |P.β| ^ n = 1 / P.α ^ n := by
  rw [abs_beta_pow (P := P) n, hb, one_pow]

/-- **The future band, and its rate.**  At offset `t` beyond the rung the future weight of
`hₖ` is within `|e₀|(α-1)ρ^{2k}/((α-β)αᵗ)` of the *fixed* shape `A/αᵗ`: the profile settles
at rate `ρ^{2k}` — which is exactly the observed `|future - past| ≍ ρ^{2k}`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_future_band (hb : |(P.b : ℝ)| = 1) (k t : ℕ) :
    |(P.lad h₀ h₁ k : ℝ) * (P.α - 1) / P.α ^ (k + t) - P.shapeFut h₀ h₁ / P.α ^ t|
      = |P.ladE h₀ h₁| * (P.α - 1) * |P.β| ^ (2 * k) / ((P.α - P.β) * P.α ^ t) := by
  have hα : (0 : ℝ) < P.α := P.alpha_pos
  have h := P.abs_future_sub_shape h₀ h₁ k (k + t)
  have hshdiv : P.shapeFut h₀ h₁ * P.α ^ k / P.α ^ (k + t) = P.shapeFut h₀ h₁ / P.α ^ t := by
    rw [pow_add]
    field_simp
  rw [hshdiv] at h
  rw [h, abs_beta_pow_unit (P := P) hb k, abs_beta_pow_unit (P := P) hb (2 * k), pow_add,
    two_mul, pow_add]
  field_simp

/-- **The past band, and the same rate.**  At offset `s` beyond the rung the past weight
`hₖ c_{k+s}` is within `|e₀||β-1|ρ^{2k}/((α-β)αˢ)` of the fixed shape
`(-b)^{k+s} B/αˢ`.  Same `ρ^{2k}`: the two bands settle together, which is the mechanism
behind Observation 16(i). -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_past_band (hb : |(P.b : ℝ)| = 1) (k s : ℕ) :
    |(P.lad h₀ h₁ k : ℝ) * P.cCoef (k + s)
        - P.shapePast h₀ h₁ * (-(P.b : ℝ)) ^ (k + s) / P.α ^ s|
      = |P.ladE h₀ h₁| * |P.β - 1| * |P.β| ^ (2 * k) / ((P.α - P.β) * P.α ^ s) := by
  have hα : (0 : ℝ) < P.α := P.alpha_pos
  have h := P.abs_past_sub_shape h₀ h₁ k (k + s)
  have hshdiv : P.shapePast h₀ h₁ * ((-(P.b : ℝ)) ^ (k + s) * P.α ^ k / P.α ^ (k + s))
      = P.shapePast h₀ h₁ * (-(P.b : ℝ)) ^ (k + s) / P.α ^ s := by
    rw [pow_add]
    field_simp
    ring
  rw [hshdiv] at h
  rw [h, show k + (k + s) = 2 * k + s by ring, abs_beta_pow_unit (P := P) hb (2 * k + s),
    abs_beta_pow_unit (P := P) hb (2 * k), pow_add]
  field_simp

/-! ## Norm `+1`: no limit to take -/

/-- At a quadratic unit of norm `+1` the two shapes are the same one: `B = -A/α`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem shapePast_eq_of_norm_one (hb : P.b = -1) :
    P.shapePast h₀ h₁ = -(P.shapeFut h₀ h₁ / P.α) := by
  have hα : (0 : ℝ) < P.α := P.alpha_pos
  have hβ := P.beta_eq_inv hb
  rw [shapePast, shapeFut, hβ]
  field_simp
  ring

/-- **At a quadratic unit of norm `+1` there is no limit to take.**  `past_eq_future`
(M5 Thm 7) says `c_m = -(α-1)/α^{m+1}` *exactly*, so the past weight of **any** `h` at depth
`m` is minus its future weight at depth `m+1`.  The two one-sided products of
Observation 16(i) are then equal term by term, at every rung and for every mode — not merely
in the limit.  Only at norm `-1` is a limit involved, and there `abs_future_band` /
`abs_past_band` give the rate `ρ^{2k}`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem past_weight_eq_neg_future_weight (hb : P.b = -1) (h : ℝ) (m : ℕ) :
    h * P.cCoef m = -(h * (P.α - 1) / P.α ^ (m + 1)) := by
  rw [cCoef, P.past_eq_future hb]
  ring

end QuadSetup

end BB61
