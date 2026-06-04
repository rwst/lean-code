/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/

import Mathlib.Algebra.ContinuedFractions.Computation.Basic
import Mathlib.Algebra.ContinuedFractions.Computation.Translations
import Mathlib.Algebra.ContinuedFractions.Computation.ApproximationCorollaries
import Mathlib.Analysis.RCLike.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.NumberTheory.Real.Irrational
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Lagrange's theorem on periodic continued fractions

A real number is a quadratic irrational — algebraic of degree exactly two over `ℚ` —
if and only if its simple continued fraction expansion is eventually periodic. It is the
continued-fraction input to `DistributionModOne/Problem10_8.lean` (de Mathan–Teulié's
quadratic case of the `p`-adic Littlewood conjecture), whose proof formally uses the
`quadratic_partialQuotients_bounded` corollary below.

The two implications have very different histories and difficulty, so they are stated as
separate lemmas and combined into `lagrange`:
* `euler_periodic_imp_quadratic` — the easy half (Euler, 1737): an irrational whose
  expansion is eventually periodic is a quadratic irrational.
* `lagrange_quadratic_imp_periodic` — the hard half (Lagrange, 1770): every quadratic
  irrational has an eventually periodic expansion. Its engine
  `completeQuotient_isIntegral_bounded` (uniformly bounded integer coefficient-triples) also
  yields the cheaper `quadratic_partialQuotients_bounded` (bounded partial quotients) — the
  fact the Problem 10.8 application actually needs — without the pigeonhole step.

The hard direction follows the substitution/bounded-coefficient/pigeonhole proof common to
Hardy–Wright, Niven–Zuckerman–Montgomery, and Khinchin, not the reduced-surd/Galois route of
Olds. The bounded-coefficient core (`qCoeffs_bounded`) is developed self-contained on integer
continuant pairs (`qConv`): the convergent/Möbius relation (`qConv_mobius`) and the unimodular
determinant (`qConv_det`) are proved directly from the complete-quotient recursion
`ξₙ = ⌊ξₙ⌋ + 1/ξₙ₊₁`, rather than routed through Mathlib's `GenContFract` convergent API.

*References:*
  - [HW79] Hardy, G.H. and Wright, E.M. *An Introduction to the Theory of Numbers.*
    5th ed., Oxford University Press, 1979. Ch. X, Theorem 177.
  - [NZM91] Niven, I., Zuckerman, H.S. and Montgomery, H.L. *An Introduction to the
    Theory of Numbers.* 5th ed., Wiley, 1991. Ch. 7.
  - [Khi64] Khinchin, A.Ya. *Continued Fractions.* Univ. of Chicago Press, 1964. Ch. 1, §5.
-/

/-- The continued fraction expansion of `ξ` is **eventually periodic**: from some index
`N` on, the sequence of its terms repeats with a fixed positive period `p`. (For an
irrational `ξ` this sequence is infinite, so the condition is non-vacuous.) -/
@[category API, AMS 11]
def IsEventuallyPeriodicContFrac (ξ : ℝ) : Prop :=
  ∃ N p : ℕ, 0 < p ∧ ∀ n : ℕ, N ≤ n →
    (GenContFract.of ξ).s.get? (n + p) = (GenContFract.of ξ).s.get? n

/-- The `n`-th **complete quotient** of `ξ`: `ξ₀ = ξ` and `ξₙ₊₁ = 1/{ξₙ}`, the reciprocal of
the fractional part `{ξₙ} = ξₙ - ⌊ξₙ⌋`. This is exactly the sequence produced by the
continued fraction algorithm, and the partial quotients are its floors `aₙ = ⌊ξₙ⌋`; the
eventual periodicity of this sequence is what drives Lagrange's direction. -/
@[category API, AMS 11]
noncomputable def completeQuotient (ξ : ℝ) : ℕ → ℝ
  | 0 => ξ
  | n + 1 => (Int.fract (completeQuotient ξ n))⁻¹

/-- Every complete quotient of an irrational is itself irrational: `ξ` irrational, and each
step `ξₖ₊₁ = 1/{ξₖ}` preserves irrationality (`{ξₖ}` is irrational and nonzero). -/
@[category API, AMS 11]
theorem completeQuotient_irrational {ξ : ℝ} (hirr : Irrational ξ) (n : ℕ) :
    Irrational (completeQuotient ξ n) := by
  induction n with
  | zero => exact hirr
  | succ k IH =>
    show Irrational (Int.fract (completeQuotient ξ k))⁻¹
    refine Irrational.inv ?_
    show Irrational (completeQuotient ξ k - ↑⌊completeQuotient ξ k⌋)
    exact IH.sub_intCast _

/-- A real number whose minimal polynomial over `ℚ` has degree two is irrational: a rational
`ξ = ↑q` is a root of the degree-one `X - C q`, so `minpoly ℚ ξ` divides it and has degree
`≤ 1`, contradicting degree `2`. (General-purpose; supplies the `Irrational` half of the hard
direction.) -/
@[category API, AMS 11]
theorem irrational_of_minpoly_natDegree_two {ξ : ℝ} (hξ : (minpoly ℚ ξ).natDegree = 2) :
    Irrational ξ := by
  rintro ⟨q, hq⟩
  have hann : (Polynomial.aeval ξ) (Polynomial.X - Polynomial.C q) = 0 := by
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, eq_ratCast, hq, sub_self]
  have hdvd : minpoly ℚ ξ ∣ (Polynomial.X - Polynomial.C q) := minpoly.dvd ℚ ξ hann
  have hle := Polynomial.natDegree_le_of_dvd hdvd (Polynomial.monic_X_sub_C q).ne_zero
  rw [Polynomial.natDegree_X_sub_C, hξ] at hle
  omega

/-- The integer quadratic coefficients carried along the complete-quotient recursion. Starting
from any integer quadratic `(A, B, C)` for `ξ`, the substitution `ξₙ = ⌊ξₙ⌋ + 1/ξₙ₊₁` turns the
quadratic for `ξₙ` into one for `ξₙ₊₁`: with `k = ⌊ξₙ⌋`,
`(aₙ₊₁, bₙ₊₁, cₙ₊₁) = (aₙk² + bₙk + cₙ, 2aₙk + bₙ, aₙ)`. -/
@[category API, AMS 11]
noncomputable def qCoeffs (ξ : ℝ) (A B C : ℤ) : ℕ → ℤ × ℤ × ℤ
  | 0 => (A, B, C)
  | n + 1 =>
    ((qCoeffs ξ A B C n).1 * ⌊completeQuotient ξ n⌋ ^ 2
        + (qCoeffs ξ A B C n).2.1 * ⌊completeQuotient ξ n⌋ + (qCoeffs ξ A B C n).2.2,
      2 * (qCoeffs ξ A B C n).1 * ⌊completeQuotient ξ n⌋ + (qCoeffs ξ A B C n).2.1,
      (qCoeffs ξ A B C n).1)

/-- **Discriminant invariance.** The substitution preserves the discriminant
`bₙ² − 4aₙcₙ`, so every `qCoeffs` triple has the same discriminant `B² − 4AC` as the original.
This is what bounds `bₙ` once `aₙ, cₙ` are bounded. -/
@[category API, AMS 11]
theorem qCoeffs_discrim {ξ : ℝ} {A B C : ℤ} (n : ℕ) :
    (qCoeffs ξ A B C n).2.1 ^ 2 - 4 * (qCoeffs ξ A B C n).1 * (qCoeffs ξ A B C n).2.2
      = B ^ 2 - 4 * A * C := by
  induction n with
  | zero => rfl
  | succ k IH => simp only [qCoeffs]; linear_combination IH

/-- Each complete quotient `ξₙ` is a root of its `qCoeffs` triple `aₙ X² + bₙ X + cₙ`. Proved
by induction via the substitution `ξₙ = ⌊ξₙ⌋ + 1/ξₙ₊₁`. -/
@[category API, AMS 11]
theorem qCoeffs_quad {ξ : ℝ} {A B C : ℤ} (hirr : Irrational ξ)
    (h0 : (A : ℝ) * ξ ^ 2 + (B : ℝ) * ξ + (C : ℝ) = 0) (n : ℕ) :
    ((qCoeffs ξ A B C n).1 : ℝ) * completeQuotient ξ n ^ 2
      + ((qCoeffs ξ A B C n).2.1 : ℝ) * completeQuotient ξ n
      + ((qCoeffs ξ A B C n).2.2 : ℝ) = 0 := by
  induction n with
  | zero => exact h0
  | succ k IH =>
    have hkne : completeQuotient ξ (k + 1) ≠ 0 :=
      (completeQuotient_irrational hirr (k + 1)).ne_zero
    have hsub : completeQuotient ξ k
        = (⌊completeQuotient ξ k⌋ : ℝ) + (completeQuotient ξ (k + 1))⁻¹ := by
      have h1 : completeQuotient ξ (k + 1) = (Int.fract (completeQuotient ξ k))⁻¹ := rfl
      have h2 : Int.fract (completeQuotient ξ k)
          = completeQuotient ξ k - (⌊completeQuotient ξ k⌋ : ℝ) := rfl
      rw [h1, inv_inv, h2]; ring
    have key : ((qCoeffs ξ A B C (k + 1)).1 : ℝ) * completeQuotient ξ (k + 1) ^ 2
        + ((qCoeffs ξ A B C (k + 1)).2.1 : ℝ) * completeQuotient ξ (k + 1)
        + ((qCoeffs ξ A B C (k + 1)).2.2 : ℝ)
        = completeQuotient ξ (k + 1) ^ 2 * (((qCoeffs ξ A B C k).1 : ℝ) * completeQuotient ξ k ^ 2
          + ((qCoeffs ξ A B C k).2.1 : ℝ) * completeQuotient ξ k
          + ((qCoeffs ξ A B C k).2.2 : ℝ)) := by
      simp only [qCoeffs]
      push_cast
      set K : ℝ := (⌊completeQuotient ξ k⌋ : ℝ)
      rw [hsub]
      field_simp
      ring
    rw [key, IH, mul_zero]

/-- The discriminant of a quadratic irrational is nonzero: were `B² − 4AC = 0`, the quadratic
`AX² + BX + C` would have the rational double root `−B/(2A)`, contradicting `ξ` irrational. -/
@[category API, AMS 11]
theorem discrim_ne_zero {ξ : ℝ} {A B C : ℤ} (hirr : Irrational ξ) (hA : A ≠ 0)
    (h0 : (A : ℝ) * ξ ^ 2 + (B : ℝ) * ξ + (C : ℝ) = 0) :
    B ^ 2 - 4 * A * C ≠ 0 := by
  intro hD
  have hDR : (B : ℝ) ^ 2 - 4 * (A : ℝ) * (C : ℝ) = 0 := by exact_mod_cast hD
  have hsq : (2 * (A : ℝ) * ξ + B) ^ 2 = 0 := by linear_combination 4 * (A : ℝ) * h0 + hDR
  have hlin : 2 * (A : ℝ) * ξ + B = 0 := (pow_eq_zero_iff (by norm_num)).mp hsq
  have hAR : (A : ℝ) ≠ 0 := by exact_mod_cast hA
  apply hirr
  refine ⟨(-B : ℚ) / (2 * A), ?_⟩
  rw [Rat.cast_div]
  push_cast
  rw [div_eq_iff (mul_ne_zero two_ne_zero hAR)]
  linear_combination -hlin

/-- The leading coefficient `aₙ` is never zero: `ξₙ` is irrational, so its `qCoeffs` quadratic
is genuinely degree two. (If `aₙ = 0`, then `bₙ ξₙ + cₙ = 0`; the invariant discriminant gives
`bₙ² = B² − 4AC ≠ 0` so `bₙ ≠ 0`, making `ξₙ = −cₙ/bₙ` rational.) -/
@[category API, AMS 11]
theorem qCoeffs_fst_ne {ξ : ℝ} {A B C : ℤ} (hirr : Irrational ξ) (hA : A ≠ 0)
    (h0 : (A : ℝ) * ξ ^ 2 + (B : ℝ) * ξ + (C : ℝ) = 0) (n : ℕ) :
    (qCoeffs ξ A B C n).1 ≠ 0 := by
  intro ha0
  have hquad := qCoeffs_quad hirr h0 n
  have hdisc := qCoeffs_discrim (ξ := ξ) (A := A) (B := B) (C := C) n
  set a := (qCoeffs ξ A B C n).1 with hadef
  set b := (qCoeffs ξ A B C n).2.1 with hbdef
  set c := (qCoeffs ξ A B C n).2.2 with hcdef
  rw [ha0] at hquad hdisc
  simp only [Int.cast_zero, zero_mul, zero_add, mul_zero, sub_zero] at hquad hdisc
  have hbne : b ≠ 0 := by
    intro hb
    apply discrim_ne_zero hirr hA h0
    rw [← hdisc, hb]; ring
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hbne
  apply completeQuotient_irrational hirr n
  refine ⟨(-(c : ℚ)) / (b : ℚ), ?_⟩
  rw [Rat.cast_div]
  push_cast
  rw [div_eq_iff hbR]
  linear_combination -hquad

/-- Integer continuant pairs `(numₖ, denₖ)` of the continued fraction `[⌊ξ₀⌋; ⌊ξ₁⌋, …]` driven by
the complete quotients `ξₙ = completeQuotient ξ n`. The seeds `qConv 0 = (0, 1)` and
`qConv 1 = (1, 0)` are the two virtual convergents `p₋₂/q₋₂ = 0/1` and `p₋₁/q₋₁ = 1/0`, so that
`qConv (k + 2)` is the genuine `k`-th convergent. By `qCoeffs_eq_qConv`, the leading `qCoeffs`
coefficient is exactly the binary quadratic form evaluated at the previous convergent. -/
@[category API, AMS 11]
noncomputable def qConv (ξ : ℝ) : ℕ → ℤ × ℤ
  | 0 => (0, 1)
  | 1 => (1, 0)
  | n + 2 =>
    (⌊completeQuotient ξ n⌋ * (qConv ξ (n + 1)).1 + (qConv ξ n).1,
      ⌊completeQuotient ξ n⌋ * (qConv ξ (n + 1)).2 + (qConv ξ n).2)

/-- The `qCoeffs` triple is exactly the binary quadratic form `(A, B, C)` transported along the
convergent pairs: `aₙ = A·numₙ₋₁² + B·numₙ₋₁·denₙ₋₁ + C·denₙ₋₁²`, `cₙ` the same at the previous
convergent, and `bₙ` the associated bilinear cross term. Pure integer induction matching the
`qCoeffs` recursion to the `qConv` recursion. -/
@[category API, AMS 11]
theorem qCoeffs_eq_qConv {ξ : ℝ} {A B C : ℤ} (n : ℕ) :
    (qCoeffs ξ A B C n).1 = A * (qConv ξ (n + 1)).1 ^ 2
        + B * (qConv ξ (n + 1)).1 * (qConv ξ (n + 1)).2 + C * (qConv ξ (n + 1)).2 ^ 2
      ∧ (qCoeffs ξ A B C n).2.1 = 2 * A * (qConv ξ (n + 1)).1 * (qConv ξ n).1
          + B * ((qConv ξ (n + 1)).1 * (qConv ξ n).2 + (qConv ξ n).1 * (qConv ξ (n + 1)).2)
          + 2 * C * (qConv ξ (n + 1)).2 * (qConv ξ n).2
      ∧ (qCoeffs ξ A B C n).2.2 = A * (qConv ξ n).1 ^ 2
          + B * (qConv ξ n).1 * (qConv ξ n).2 + C * (qConv ξ n).2 ^ 2 := by
  induction n with
  | zero => refine ⟨?_, ?_, ?_⟩ <;> simp [qCoeffs, qConv]
  | succ k IH =>
    obtain ⟨IH1, IH2, IH3⟩ := IH
    refine ⟨?_, ?_, ?_⟩ <;> simp only [qCoeffs, qConv, IH1, IH2, IH3] <;> ring

/-- The continuant determinant is `±1`: `numₙ·denₙ₋₁ − numₙ₋₁·denₙ = (−1)ⁿ`. The integer-quadratic
discriminant is invariant under the convergent substitution precisely because this determinant
squares to one. -/
@[category API, AMS 11]
theorem qConv_det {ξ : ℝ} (n : ℕ) :
    (qConv ξ (n + 1)).1 * (qConv ξ n).2 - (qConv ξ n).1 * (qConv ξ (n + 1)).2 = (-1) ^ n := by
  induction n with
  | zero => simp [qConv]
  | succ k IH =>
    simp only [qConv]
    linear_combination -IH

/-- Every complete quotient past the first is `≥ 1`: `ξₙ₊₁ = 1/{ξₙ}` and the fractional part of an
irrational lies in `(0, 1)`. -/
@[category API, AMS 11]
theorem completeQuotient_one_le {ξ : ℝ} (hirr : Irrational ξ) (n : ℕ) :
    1 ≤ completeQuotient ξ (n + 1) := by
  show 1 ≤ (Int.fract (completeQuotient ξ n))⁻¹
  have hpos : 0 < Int.fract (completeQuotient ξ n) :=
    Int.fract_pos.mpr ((completeQuotient_irrational hirr n).ne_int _)
  exact (one_le_inv₀ hpos).mpr (Int.fract_lt_one _).le

/-- The convergent denominators are nonnegative, and strictly past the seeds they are `≥ 1`
(`denₖ ≥ 1` for `k ≥ 2`). Drives the denominator positivity behind the approximation bound. -/
@[category API, AMS 11]
theorem qConv_den {ξ : ℝ} (hirr : Irrational ξ) (n : ℕ) :
    0 ≤ (qConv ξ (n + 1)).2 ∧ 1 ≤ (qConv ξ (n + 2)).2 := by
  induction n with
  | zero => refine ⟨?_, ?_⟩ <;> simp [qConv]
  | succ k IH =>
    obtain ⟨IH1, IH2⟩ := IH
    have hfloor : (1 : ℤ) ≤ ⌊completeQuotient ξ (k + 1)⌋ :=
      Int.le_floor.mpr (by exact_mod_cast completeQuotient_one_le hirr k)
    refine ⟨?_, ?_⟩
    · exact zero_le_one.trans IH2
    · have hrec : (qConv ξ (k + 1 + 2)).2
          = ⌊completeQuotient ξ (k + 1)⌋ * (qConv ξ (k + 2)).2 + (qConv ξ (k + 1)).2 := rfl
      rw [hrec]
      nlinarith [IH1, IH2, hfloor, mul_nonneg (sub_nonneg.mpr hfloor) (sub_nonneg.mpr IH2)]

/-- The convergent/Möbius relation: `ξ = (ξₙ·numₙ₋₁ + numₙ₋₂)/(ξₙ·denₙ₋₁ + denₙ₋₂)`, written
cleared of denominators. Induction on `n` via `ξₙ = ⌊ξₙ⌋ + 1/ξₙ₊₁`. -/
@[category API, AMS 11]
theorem qConv_mobius {ξ : ℝ} (hirr : Irrational ξ) (n : ℕ) :
    ξ * (completeQuotient ξ n * ((qConv ξ (n + 1)).2 : ℝ) + ((qConv ξ n).2 : ℝ))
      = completeQuotient ξ n * ((qConv ξ (n + 1)).1 : ℝ) + ((qConv ξ n).1 : ℝ) := by
  induction n with
  | zero => simp [qConv, completeQuotient]
  | succ n IH =>
    have hs : completeQuotient ξ (n + 1) ≠ 0 :=
      (lt_of_lt_of_le one_pos (completeQuotient_one_le hirr n)).ne'
    have hsub : completeQuotient ξ n
        = (⌊completeQuotient ξ n⌋ : ℝ) + (completeQuotient ξ (n + 1))⁻¹ := by
      rw [show (completeQuotient ξ (n + 1))⁻¹ = Int.fract (completeQuotient ξ n) from inv_inv _]
      exact (Int.floor_add_fract _).symm
    simp only [qConv]
    push_cast
    rw [hsub] at IH
    field_simp [hs] at IH ⊢
    linear_combination IH

/-- The leading `qCoeffs` coefficients `aₙ` are uniformly bounded. The Möbius relation and the
`±1` determinant give the approximation `|ξ·denₙ₋₁ − numₙ₋₁| = 1/(ξₙ·denₙ₋₁ + denₙ₋₂) ≤ 1/denₙ₋₁`,
whence `aₙ = −denₙ₋₁(ξ·denₙ₋₁ − numₙ₋₁)(A·cₙ + A·ξ + B)` is bounded by `|A|(2|ξ| + 1) + |B|`. -/
@[category API, AMS 11]
theorem qCoeffs_fst_le {ξ : ℝ} {A B C : ℤ} (hirr : Irrational ξ) (hA : A ≠ 0)
    (h0 : (A : ℝ) * ξ ^ 2 + (B : ℝ) * ξ + (C : ℝ) = 0) :
    ∃ M : ℤ, ∀ n, |(qCoeffs ξ A B C n).1| ≤ M := by
  have hNξ : |ξ| ≤ (⌊|ξ|⌋ : ℝ) + 1 := le_of_lt (Int.lt_floor_add_one |ξ|)
  have hNξ0 : (0 : ℤ) ≤ ⌊|ξ|⌋ + 1 := by positivity
  -- Uniform bound on the binary quadratic form at convergent index `≥ 2`.
  have key : ∀ k : ℕ, |A * (qConv ξ (k + 2)).1 ^ 2
      + B * (qConv ξ (k + 2)).1 * (qConv ξ (k + 2)).2
      + C * (qConv ξ (k + 2)).2 ^ 2| ≤ |A| * (2 * (⌊|ξ|⌋ + 1) + 1) + |B| := by
    intro k
    have hq1 : (1 : ℤ) ≤ (qConv ξ (k + 2)).2 := (qConv_den hirr k).2
    have hq'0 : (0 : ℤ) ≤ (qConv ξ (k + 1)).2 := (qConv_den hirr k).1
    have ht1 : (1 : ℝ) ≤ completeQuotient ξ (k + 1) := completeQuotient_one_le hirr k
    have hmob : ξ * (completeQuotient ξ (k + 1) * ((qConv ξ (k + 2)).2 : ℝ)
          + ((qConv ξ (k + 1)).2 : ℝ))
        = completeQuotient ξ (k + 1) * ((qConv ξ (k + 2)).1 : ℝ) + ((qConv ξ (k + 1)).1 : ℝ) :=
      qConv_mobius hirr (k + 1)
    have hdet : ((qConv ξ (k + 2)).1 : ℝ) * ((qConv ξ (k + 1)).2 : ℝ)
        - ((qConv ξ (k + 1)).1 : ℝ) * ((qConv ξ (k + 2)).2 : ℝ) = (-1) ^ (k + 1) := by
      exact_mod_cast qConv_det (ξ := ξ) (k + 1)
    rw [← Int.cast_le (R := ℝ), Int.cast_abs]
    push_cast
    have hQ1 : (1 : ℝ) ≤ ((qConv ξ (k + 2)).2 : ℝ) := by exact_mod_cast hq1
    have hQ'0 : (0 : ℝ) ≤ ((qConv ξ (k + 1)).2 : ℝ) := by exact_mod_cast hq'0
    have hQ0 : (0 : ℝ) ≤ ((qConv ξ (k + 2)).2 : ℝ) := le_trans zero_le_one hQ1
    set P : ℝ := ((qConv ξ (k + 2)).1 : ℝ)
    set Q : ℝ := ((qConv ξ (k + 2)).2 : ℝ)
    set P' : ℝ := ((qConv ξ (k + 1)).1 : ℝ)
    set Q' : ℝ := ((qConv ξ (k + 1)).2 : ℝ)
    set t : ℝ := completeQuotient ξ (k + 1)
    have hdpos : (0 : ℝ) < t * Q + Q' := by nlinarith [ht1, hQ1, hQ'0]
    have hdQ : Q ≤ t * Q + Q' := by nlinarith [ht1, hQ1, hQ'0]
    have heq : (ξ * Q - P) * (t * Q + Q') = -((-1) ^ (k + 1)) := by
      linear_combination Q * hmob - hdet
    have hone : |ξ * Q - P| * (t * Q + Q') = 1 := by
      rw [← abs_of_pos hdpos, ← abs_mul, heq]
      simp
    have hdq1 : |ξ * Q - P| ≤ 1 := by nlinarith [hone, hdQ, hQ1, abs_nonneg (ξ * Q - P)]
    have hdqQ : |ξ * Q - P| * Q ≤ 1 := by nlinarith [hone, hdQ, abs_nonneg (ξ * Q - P)]
    have hquad : (A : ℝ) * P ^ 2 + B * P * Q + C * Q ^ 2
        = -(ξ * Q - P) * (A * P + A * ξ * Q + B * Q) := by
      linear_combination Q ^ 2 * h0
    rw [hquad, abs_mul, abs_neg]
    have hfac : |(A : ℝ) * P + A * ξ * Q + B * Q|
        ≤ |2 * (A : ℝ) * ξ + B| * Q + |(A : ℝ)| * |ξ * Q - P| := by
      have hPe : (A : ℝ) * P + A * ξ * Q + B * Q
          = (2 * A * ξ + B) * Q + (-(A * (ξ * Q - P))) := by ring
      rw [hPe]
      calc |(2 * (A : ℝ) * ξ + B) * Q + (-(A * (ξ * Q - P)))|
          ≤ |(2 * (A : ℝ) * ξ + B) * Q| + |(-(A * (ξ * Q - P)))| := abs_add_le _ _
        _ = |2 * (A : ℝ) * ξ + B| * Q + |(A : ℝ)| * |ξ * Q - P| := by
            rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg hQ0]
    calc |ξ * Q - P| * |(A : ℝ) * P + A * ξ * Q + B * Q|
        ≤ |ξ * Q - P| * (|2 * (A : ℝ) * ξ + B| * Q + |(A : ℝ)| * |ξ * Q - P|) :=
          mul_le_mul_of_nonneg_left hfac (abs_nonneg _)
      _ = |2 * (A : ℝ) * ξ + B| * (|ξ * Q - P| * Q)
            + |(A : ℝ)| * (|ξ * Q - P| * |ξ * Q - P|) := by ring
      _ ≤ |2 * (A : ℝ) * ξ + B| * 1 + |(A : ℝ)| * 1 := by
          gcongr
          · nlinarith [hdq1, abs_nonneg (ξ * Q - P)]
      _ = |2 * (A : ℝ) * ξ + B| + |(A : ℝ)| := by ring
      _ ≤ |(A : ℝ)| * (2 * ((⌊|ξ|⌋ : ℝ) + 1) + 1) + |(B : ℝ)| := by
          have htri : |2 * (A : ℝ) * ξ + B| ≤ 2 * |(A : ℝ)| * |ξ| + |(B : ℝ)| := by
            calc |2 * (A : ℝ) * ξ + B| ≤ |2 * (A : ℝ) * ξ| + |(B : ℝ)| := abs_add_le _ _
              _ = 2 * |(A : ℝ)| * |ξ| + |(B : ℝ)| := by rw [abs_mul, abs_mul]; norm_num
          nlinarith [htri, mul_nonneg (abs_nonneg (A : ℝ)) (sub_nonneg.mpr hNξ),
            abs_nonneg (A : ℝ)]
  -- Assemble: index `0` gives `A`; indices `≥ 1` are covered by `key`.
  refine ⟨|A| * (2 * (⌊|ξ|⌋ + 1) + 1) + |B|, fun n => ?_⟩
  rw [(qCoeffs_eq_qConv n).1]
  cases n with
  | zero =>
    simp only [qConv]
    have : A * (1 : ℤ) ^ 2 + B * 1 * 0 + C * 0 ^ 2 = A := by ring
    rw [this]
    nlinarith [abs_nonneg A, abs_nonneg B, mul_nonneg (abs_nonneg A) hNξ0]
  | succ k => exact key k

/-- **The crux bound.** The `qCoeffs` triples are bounded uniformly in `n`. The leading
coefficients `aₙ` are bounded by `qCoeffs_fst_le` (convergent substitution + the approximation
`|ξ − numₙ₋₁/denₙ₋₁| ≤ 1/denₙ₋₁²`); then `cₙ = aₙ₋₁` and the invariant discriminant
(`qCoeffs_discrim`, `bₙ² = (B² − 4AC) + 4aₙcₙ`) bound `cₙ` and `bₙ`. -/
@[category API, AMS 11]
theorem qCoeffs_bounded {ξ : ℝ} {A B C : ℤ} (hirr : Irrational ξ) (hA : A ≠ 0)
    (h0 : (A : ℝ) * ξ ^ 2 + (B : ℝ) * ξ + (C : ℝ) = 0) :
    ∃ M : ℤ, ∀ n, |(qCoeffs ξ A B C n).1| ≤ M ∧ |(qCoeffs ξ A B C n).2.1| ≤ M
      ∧ |(qCoeffs ξ A B C n).2.2| ≤ M := by
  obtain ⟨M₁, hM₁⟩ := qCoeffs_fst_le hirr hA h0
  have hM₁0 : (0 : ℤ) ≤ M₁ := le_trans (abs_nonneg _) (hM₁ 0)
  -- `cₙ` bound: `c₀ = C` and `cₙ₊₁ = aₙ`.
  have hc : ∀ n, |(qCoeffs ξ A B C n).2.2| ≤ max |C| M₁ := by
    intro n
    cases n with
    | zero => exact le_max_left _ _
    | succ k => exact (hM₁ k).trans (le_max_right _ _)
  -- `bₙ` bound from the invariant discriminant `bₙ² = (B² − 4AC) + 4aₙcₙ`.
  have hb : ∀ n, |(qCoeffs ξ A B C n).2.1| ≤ |B ^ 2 - 4 * A * C| + 4 * M₁ * max |C| M₁ := by
    intro n
    have hdisc := qCoeffs_discrim (ξ := ξ) (A := A) (B := B) (C := C) n
    have ha := hM₁ n
    have hcc := hc n
    have hsq : (qCoeffs ξ A B C n).2.1 ^ 2 ≤ |B ^ 2 - 4 * A * C| + 4 * M₁ * max |C| M₁ := by
      nlinarith [hdisc, le_abs_self (B ^ 2 - 4 * A * C),
        le_abs_self ((qCoeffs ξ A B C n).1 * (qCoeffs ξ A B C n).2.2),
        abs_mul ((qCoeffs ξ A B C n).1) ((qCoeffs ξ A B C n).2.2),
        mul_le_mul ha hcc (abs_nonneg _) hM₁0]
    exact (Int.abs_eq_natAbs _ ▸ Int.natAbs_le_self_sq _).trans hsq
  refine ⟨max M₁ (max (max |C| M₁) (|B ^ 2 - 4 * A * C| + 4 * M₁ * max |C| M₁)),
    fun n => ⟨(hM₁ n).trans (le_max_left _ _), ?_, ?_⟩⟩
  · exact (hb n).trans ((le_max_right _ _).trans (le_max_right _ _))
  · exact (hc n).trans ((le_max_left _ _).trans (le_max_right _ _))

/-- A real of minimal-polynomial degree two is the root of an integer quadratic with nonzero
leading coefficient (clear the denominators of the rational `minpoly ℚ ξ`). -/
@[category API, AMS 11]
theorem exists_int_quadratic_of_minpoly {ξ : ℝ} (hξ : (minpoly ℚ ξ).natDegree = 2) :
    ∃ A B C : ℤ, A ≠ 0 ∧ (A : ℝ) * ξ ^ 2 + (B : ℝ) * ξ + (C : ℝ) = 0 := by
  have hint : IsIntegral ℚ ξ := by
    by_contra h
    rw [minpoly.eq_zero h, Polynomial.natDegree_zero] at hξ
    exact absurd hξ (by norm_num)
  have h2 : (minpoly ℚ ξ).coeff 2 = 1 := by
    have h := (minpoly.monic hint).coeff_natDegree; rwa [hξ] at h
  have haeval : (Polynomial.aeval ξ) (minpoly ℚ ξ) = 0 := minpoly.aeval ℚ ξ
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, hξ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_one] at haeval
  simp only [pow_zero, pow_one, mul_one, one_mul, h2, map_one] at haeval
  set q1 := (minpoly ℚ ξ).coeff 1
  set q0 := (minpoly ℚ ξ).coeff 0
  have hd1 : (q1.den : ℝ) ≠ 0 := by exact_mod_cast q1.den_pos.ne'
  have hd0 : (q0.den : ℝ) ≠ 0 := by exact_mod_cast q0.den_pos.ne'
  have hn1 : (q1.num : ℝ) = algebraMap ℚ ℝ q1 * (q1.den : ℝ) := by
    rw [eq_ratCast (algebraMap ℚ ℝ) q1, Rat.cast_def]; field_simp
  have hn0 : (q0.num : ℝ) = algebraMap ℚ ℝ q0 * (q0.den : ℝ) := by
    rw [eq_ratCast (algebraMap ℚ ℝ) q0, Rat.cast_def]; field_simp
  refine ⟨(q1.den : ℤ) * (q0.den : ℤ), q1.num * (q0.den : ℤ), q0.num * (q1.den : ℤ),
    mul_ne_zero (by exact_mod_cast q1.den_pos.ne') (by exact_mod_cast q0.den_pos.ne'), ?_⟩
  push_cast
  linear_combination (q1.den : ℝ) * (q0.den : ℝ) * haeval + (q0.den : ℝ) * ξ * hn1
    + (q1.den : ℝ) * hn0

/-- **Bounded coefficients** — the engine of Lagrange's direction. For a quadratic irrational
`ξ`, every complete quotient `ξₙ` is a root of an integer quadratic `aₙ X² + bₙ X + cₙ`
(`aₙ ≠ 0`) whose coefficients are bounded *uniformly in `n`*. Assembled from the
complete-quotient recursion `qCoeffs`: `qCoeffs_quad` (root), `qCoeffs_fst_ne` (`aₙ ≠ 0`), and
`qCoeffs_bounded` (the uniform bound, via `qCoeffs_discrim`).

This is the shared heart of the hard direction: the cheap `quadratic_partialQuotients_bounded`
and the full `lagrange_quadratic_imp_periodic` both reduce to it, the latter by additionally
pigeonholing the finitely many bounded triples. -/
@[category research solved, AMS 11, ref "HW79" "NZM91" "Khi64", solved_by "Lagrange" 1770,
  formal_uses qCoeffs_quad qCoeffs_fst_ne qCoeffs_bounded exists_int_quadratic_of_minpoly]
theorem completeQuotient_isIntegral_bounded {ξ : ℝ} (hξ : (minpoly ℚ ξ).natDegree = 2) :
    ∃ M : ℤ, ∀ n, ∃ a b c : ℤ, a ≠ 0 ∧
      (a : ℝ) * completeQuotient ξ n ^ 2 + (b : ℝ) * completeQuotient ξ n + (c : ℝ) = 0 ∧
      |a| ≤ M ∧ |b| ≤ M ∧ |c| ≤ M := by
  obtain ⟨A, B, C, hA, h0⟩ := exists_int_quadratic_of_minpoly hξ
  have hirr := irrational_of_minpoly_natDegree_two hξ
  obtain ⟨M, hM⟩ := qCoeffs_bounded hirr hA h0
  exact ⟨M, fun n => ⟨(qCoeffs ξ A B C n).1, (qCoeffs ξ A B C n).2.1, (qCoeffs ξ A B C n).2.2,
    qCoeffs_fst_ne hirr hA h0 n, qCoeffs_quad hirr h0 n, (hM n).1, (hM n).2.1, (hM n).2.2⟩⟩

/-- **Bounded partial quotients** — the cheap corollary actually consumed by the `p`-adic
Littlewood / Problem 10.8 quadratic case. A quadratic irrational has uniformly bounded
partial quotients `aₙ = ⌊ξₙ⌋`.

This follows from `completeQuotient_isIntegral_bounded` *without* the pigeonhole/periodicity
step: each `ξₙ` is a root of a bounded-coefficient quadratic with nonzero leading
coefficient, hence `|ξₙ| ≤ M'`, hence `⌊ξₙ⌋ ≤ M'`. -/
@[category research solved, AMS 11, ref "HW79" "NZM91" "Khi64", solved_by "Lagrange" 1770,
  formal_uses completeQuotient_isIntegral_bounded]
theorem quadratic_partialQuotients_bounded {ξ : ℝ} (hξ : (minpoly ℚ ξ).natDegree = 2) :
    ∃ M : ℤ, ∀ n, ⌊completeQuotient ξ n⌋ ≤ M := by
  -- The engine hands us, for each `n`, an integer quadratic `a·ξₙ² + b·ξₙ + c = 0` with
  -- `a ≠ 0` and `|a|, |b|, |c| ≤ M`. A root of such a quadratic is bounded: `|ξₙ| ≤ 2M`.
  obtain ⟨M, hM⟩ := completeQuotient_isIntegral_bounded hξ
  refine ⟨2 * M, fun n => ?_⟩
  obtain ⟨a, b, c, ha, heq, hMa, hMb, hMc⟩ := hM n
  set x := completeQuotient ξ n
  have hM1 : (1 : ℤ) ≤ M := le_trans (Int.one_le_abs ha) hMa
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  have haR : (1 : ℝ) ≤ |(a : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs ha
  have hbR : |(b : ℝ)| ≤ (M : ℝ) := by rw [← Int.cast_abs]; exact_mod_cast hMb
  have hcR : |(c : ℝ)| ≤ (M : ℝ) := by rw [← Int.cast_abs]; exact_mod_cast hMc
  have hxabs : |x| ≤ 2 * (M : ℝ) := by
    by_cases hx1 : |x| ≤ 1
    · linarith
    · push Not at hx1
      have hxpos : (0 : ℝ) < |x| := lt_trans one_pos hx1
      have key : |(a : ℝ)| * |x| ^ 2 ≤ |(b : ℝ)| * |x| + |(c : ℝ)| := by
        have e2 : (a : ℝ) * x ^ 2 = -((b : ℝ) * x + (c : ℝ)) := by linear_combination heq
        have e3 : |(a : ℝ)| * |x| ^ 2 = |(a : ℝ) * x ^ 2| := by rw [abs_mul, abs_pow]
        rw [e3, e2, abs_neg]
        calc |(b : ℝ) * x + (c : ℝ)| ≤ |(b : ℝ) * x| + |(c : ℝ)| := abs_add_le _ _
          _ = |(b : ℝ)| * |x| + |(c : ℝ)| := by rw [abs_mul]
      have step1 : |x| ^ 2 ≤ |(a : ℝ)| * |x| ^ 2 := le_mul_of_one_le_left (sq_nonneg _) haR
      have step2 : |(b : ℝ)| * |x| ≤ (M : ℝ) * |x| :=
        mul_le_mul_of_nonneg_right hbR (le_of_lt hxpos)
      have step3 : |(c : ℝ)| ≤ (M : ℝ) * |x| :=
        le_trans hcR (le_mul_of_one_le_right (by linarith) (le_of_lt hx1))
      have step4 : |x| * |x| ≤ 2 * (M : ℝ) * |x| := by nlinarith [step1, step2, step3, key]
      exact le_of_mul_le_mul_right step4 hxpos
  have hxle : x ≤ 2 * (M : ℝ) := le_trans (le_abs_self x) hxabs
  have hfloor : (⌊x⌋ : ℝ) ≤ ((2 * M : ℤ) : ℝ) := by push_cast; linarith [Int.floor_le x]
  exact_mod_cast hfloor

/-- A nonzero real quadratic has only finitely many roots (the explicit-quadratic packaging of
`Polynomial.finite_setOf_isRoot`). Used to confine the complete quotients to a finite set. -/
@[category API, AMS 11]
theorem setOf_quadratic_eq_zero_finite (a b c : ℝ) (ha : a ≠ 0) :
    {x : ℝ | a * x ^ 2 + b * x + c = 0}.Finite := by
  set p : Polynomial ℝ :=
    Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c with hp
  have hp0 : p ≠ 0 := by
    have hd : p.natDegree = 2 := by rw [hp]; exact Polynomial.natDegree_quadratic ha
    intro h
    rw [h, Polynomial.natDegree_zero] at hd
    exact absurd hd (by norm_num)
  have hset : {x : ℝ | a * x ^ 2 + b * x + c = 0} = {x | p.IsRoot x} := by
    ext x
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, hp, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  rw [hset]
  exact Polynomial.finite_setOf_isRoot hp0

/-- Helper (pigeonhole, engine ⇒ recurrence): for a quadratic irrational, two complete
quotients coincide. The bounded integer triples from `completeQuotient_isIntegral_bounded`
confine every `ξₙ` to the finite union of root-sets of the (finitely many) bounded-coefficient
quadratics, so the map `ℕ → {values}` repeats: `ξₘ = ξₙ` for some `m < n`. -/
@[category API, AMS 11, formal_uses completeQuotient_isIntegral_bounded]
theorem completeQuotient_eq_of_quadratic {ξ : ℝ} (hξ : (minpoly ℚ ξ).natDegree = 2) :
    ∃ m n, m < n ∧ completeQuotient ξ m = completeQuotient ξ n := by
  obtain ⟨M, hM⟩ := completeQuotient_isIntegral_bounded hξ
  set R : Set ℝ := {x | ∃ a b c : ℤ, a ≠ 0 ∧ |a| ≤ M ∧ |b| ≤ M ∧ |c| ≤ M ∧
      (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0} with hRdef
  have hmem : ∀ n, completeQuotient ξ n ∈ R := by
    intro n
    obtain ⟨a, b, c, ha, heq, hMa, hMb, hMc⟩ := hM n
    rw [hRdef]
    exact ⟨a, b, c, ha, hMa, hMb, hMc, heq⟩
  have hRfin : R.Finite := by
    set T : Set (ℤ × ℤ × ℤ) :=
      {t | |t.1| ≤ M ∧ |t.2.1| ≤ M ∧ |t.2.2| ≤ M ∧ t.1 ≠ 0} with hTdef
    have hTfin : T.Finite := by
      apply Set.Finite.subset
        ((Set.finite_Icc (-M) M).prod ((Set.finite_Icc (-M) M).prod (Set.finite_Icc (-M) M)))
      intro t ht
      obtain ⟨a, b, c⟩ := t
      rw [hTdef] at ht
      obtain ⟨hMa, hMb, hMc, -⟩ := ht
      exact Set.mk_mem_prod (Set.mem_Icc.mpr (abs_le.mp hMa))
        (Set.mk_mem_prod (Set.mem_Icc.mpr (abs_le.mp hMb)) (Set.mem_Icc.mpr (abs_le.mp hMc)))
    have hbU : (⋃ t ∈ T, {x : ℝ | (t.1 : ℝ) * x ^ 2 + (t.2.1 : ℝ) * x + (t.2.2 : ℝ) = 0}).Finite := by
      apply Set.Finite.biUnion hTfin
      intro t ht
      rw [hTdef] at ht
      exact setOf_quadratic_eq_zero_finite _ _ _ (Int.cast_ne_zero.mpr ht.2.2.2)
    apply Set.Finite.subset hbU
    intro x hx
    rw [hRdef] at hx
    obtain ⟨a, b, c, ha, hMa, hMb, hMc, heq⟩ := hx
    exact Set.mem_biUnion (show (a, b, c) ∈ T from by rw [hTdef]; exact ⟨hMa, hMb, hMc, ha⟩) heq
  obtain ⟨m, -, n, -, hmn, hfeq⟩ :=
    Set.infinite_univ.exists_ne_map_eq_of_mapsTo (fun k _ => hmem k) hRfin
  rcases lt_or_gt_of_ne hmn with h | h
  · exact ⟨m, n, h, hfeq⟩
  · exact ⟨n, m, h, hfeq.symm⟩

/-- Helper (a) (recursion ⇒ sequence periodicity): if two complete quotients coincide
(`ξₘ = ξₙ`, `m < n`) then the `completeQuotient` sequence is periodic from `m` on with period
`n − m`: `ξ_{k+(n-m)} = ξ_k` for every `k ≥ m`. Pure induction on `ξₖ₊₁ = 1/{ξₖ}`. -/
@[category API, AMS 11]
theorem completeQuotient_periodic_of_eq {ξ : ℝ} {m n : ℕ} (hmn : m < n)
    (h : completeQuotient ξ m = completeQuotient ξ n) :
    ∀ k, m ≤ k → completeQuotient ξ (k + (n - m)) = completeQuotient ξ k := by
  have hrec : ∀ j, completeQuotient ξ (j + 1) = (Int.fract (completeQuotient ξ j))⁻¹ :=
    fun _ => rfl
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => rw [Nat.add_sub_cancel' hmn.le]; exact h.symm
  | succ k _ IH =>
    have hk1 : k + 1 + (n - m) = (k + (n - m)) + 1 := by omega
    rw [hk1, hrec, IH, hrec]

/-- The bridge to Mathlib's continued-fraction algorithm: for irrational `ξ`, the
integer/fractional-part stream never terminates and its `n`-th entry is exactly
`IntFractPair.of (completeQuotient ξ n)` (so its integer part is `⌊completeQuotient ξ n⌋`,
the `n`-th partial quotient). Proved by induction on Mathlib's `stream` recurrence. -/
@[category API, AMS 11]
theorem intFractPair_stream_eq {ξ : ℝ} (hirr : Irrational ξ) (n : ℕ) :
    GenContFract.IntFractPair.stream ξ n
      = some (GenContFract.IntFractPair.of (completeQuotient ξ n)) := by
  induction n with
  | zero => exact (GenContFract.IntFractPair.stream_zero ξ).trans rfl
  | succ k IH =>
    have hfr : (GenContFract.IntFractPair.of (completeQuotient ξ k)).fr ≠ 0 := by
      show completeQuotient ξ k - ↑⌊completeQuotient ξ k⌋ ≠ 0
      rw [sub_ne_zero]
      exact (completeQuotient_irrational hirr k).ne_int _
    exact (GenContFract.IntFractPair.stream_succ_of_some IH hfr).trans rfl

/-- Helper (b) (continued-fraction link): for an irrational `ξ` whose `completeQuotient`
sequence is eventually periodic, the continued fraction `GenContFract.of ξ` is eventually
periodic. Via `intFractPair_stream_eq`, the `n`-th partial-quotient pair of `GenContFract.of ξ`
is determined by `completeQuotient ξ (n+1)`, so periodicity of the complete quotients transfers
to `(GenContFract.of ξ).s.get?`. -/
@[category API, AMS 11]
theorem isEventuallyPeriodicContFrac_of_completeQuotient_periodic {ξ : ℝ} (hirr : Irrational ξ)
    {m p : ℕ} (hp : 0 < p)
    (hper : ∀ k, m ≤ k → completeQuotient ξ (k + p) = completeQuotient ξ k) :
    IsEventuallyPeriodicContFrac ξ := by
  refine ⟨m, p, hp, fun n _ => ?_⟩
  rw [GenContFract.get?_of_eq_some_of_succ_get?_intFractPair_stream
        (intFractPair_stream_eq hirr (n + p + 1)),
      GenContFract.get?_of_eq_some_of_succ_get?_intFractPair_stream
        (intFractPair_stream_eq hirr (n + 1))]
  have hcq : completeQuotient ξ (n + p + 1) = completeQuotient ξ (n + 1) := by
    have h2 := hper (n + 1) (by omega)
    rwa [show n + 1 + p = n + p + 1 from by omega] at h2
  rw [hcq]

/-- Helper (continued-fraction bridge): if two complete quotients coincide, the continued
fraction is eventually periodic. Combines the recursion-periodicity
`completeQuotient_periodic_of_eq` (a) with the continued-fraction link
`isEventuallyPeriodicContFrac_of_completeQuotient_periodic` (b). -/
@[category API, AMS 11]
theorem isEventuallyPeriodicContFrac_of_completeQuotient_eq {ξ : ℝ} (hirr : Irrational ξ)
    {m n : ℕ} (hmn : m < n)
    (h : completeQuotient ξ m = completeQuotient ξ n) :
    IsEventuallyPeriodicContFrac ξ :=
  isEventuallyPeriodicContFrac_of_completeQuotient_periodic hirr (Nat.sub_pos_of_lt hmn)
    (completeQuotient_periodic_of_eq hmn h)

/-- **Lagrange's direction** (the hard half, 1770). A quadratic irrational
(`(minpoly ℚ ξ).natDegree = 2`) is irrational and has an eventually periodic continued
fraction expansion. The irrationality is `irrational_of_minpoly_natDegree_two`; the
periodicity combines the pigeonhole step `completeQuotient_eq_of_quadratic` with the
continued-fraction bridge `isEventuallyPeriodicContFrac_of_completeQuotient_eq`. -/
@[category research solved, AMS 11, ref "HW79" "NZM91" "Khi64", solved_by "Lagrange" 1770,
  formal_uses completeQuotient_eq_of_quadratic isEventuallyPeriodicContFrac_of_completeQuotient_eq]
theorem lagrange_quadratic_imp_periodic {ξ : ℝ} (hξ : (minpoly ℚ ξ).natDegree = 2) :
    Irrational ξ ∧ IsEventuallyPeriodicContFrac ξ := by
  have hirr := irrational_of_minpoly_natDegree_two hξ
  refine ⟨hirr, ?_⟩
  obtain ⟨m, n, hmn, h⟩ := completeQuotient_eq_of_quadratic hξ
  exact isEventuallyPeriodicContFrac_of_completeQuotient_eq hirr hmn h

/-- The complete-quotient operator composes additively: the `j`-th complete quotient of the
`m`-th complete quotient of `ξ` is the `(m + j)`-th complete quotient of `ξ`. -/
@[category API, AMS 11]
theorem completeQuotient_add (ξ : ℝ) (m j : ℕ) :
    completeQuotient (completeQuotient ξ m) j = completeQuotient ξ (m + j) := by
  induction j with
  | zero => rfl
  | succ k IH =>
    show (Int.fract (completeQuotient (completeQuotient ξ m) k))⁻¹
      = (Int.fract (completeQuotient ξ (m + k)))⁻¹
    rw [IH]

/-- An irrational root of an integer quadratic `a X² + b X + c` with `a ≠ 0` is a quadratic
irrational: `(minpoly ℚ ξ).natDegree = 2` (`≤ 2` as a root of the degree-two polynomial, `≠ 1`
by irrationality, `≠ 0` by integrality). The finisher for Euler's direction. -/
@[category API, AMS 11]
theorem minpoly_natDegree_two_of_irrational_quadratic {ξ : ℝ} (hirr : Irrational ξ)
    {a b c : ℤ} (ha : a ≠ 0) (hr : (a : ℝ) * ξ ^ 2 + b * ξ + c = 0) :
    (minpoly ℚ ξ).natDegree = 2 := by
  set p : Polynomial ℚ := Polynomial.C (a : ℚ) * Polynomial.X ^ 2
    + Polynomial.C (b : ℚ) * Polynomial.X + Polynomial.C (c : ℚ) with hp
  have hpdeg : p.natDegree = 2 := by rw [hp]; compute_degree!
  have hp0 : p ≠ 0 := fun h0 => by rw [h0, Polynomial.natDegree_zero] at hpdeg; norm_num at hpdeg
  have haeval : Polynomial.aeval ξ p = 0 := by
    rw [hp]
    simp only [map_add, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, eq_ratCast]
    push_cast; linear_combination hr
  have hint : IsIntegral ℚ ξ := IsAlgebraic.isIntegral ⟨p, hp0, haeval⟩
  have hle : (minpoly ℚ ξ).natDegree ≤ 2 := by
    rw [← hpdeg]; exact Polynomial.natDegree_le_of_dvd (minpoly.dvd ℚ ξ haeval) hp0
  have hpos : 0 < (minpoly ℚ ξ).natDegree := minpoly.natDegree_pos hint
  have hne1 : (minpoly ℚ ξ).natDegree ≠ 1 := by
    intro h1
    have hev : Polynomial.aeval ξ (minpoly ℚ ξ) = 0 := minpoly.aeval ℚ ξ
    have hform : minpoly ℚ ξ = Polynomial.C ((minpoly ℚ ξ).coeff 1) * Polynomial.X
        + Polynomial.C ((minpoly ℚ ξ).coeff 0) :=
      Polynomial.eq_X_add_C_of_natDegree_le_one (by omega)
    have hcoeff : (minpoly ℚ ξ).coeff 1 = 1 := by
      have hm := (minpoly.monic hint).coeff_natDegree; rw [h1] at hm; exact hm
    rw [hform, hcoeff] at hev
    simp only [map_add, Polynomial.aeval_C, Polynomial.aeval_X, map_one, one_mul, eq_ratCast]
      at hev
    exact hirr ⟨-(minpoly ℚ ξ).coeff 0, by push_cast; linarith [hev]⟩
  omega

/-- For irrational `v`, the `n`-th term of `GenContFract.of v` is the pair `⟨1, ⌊vₙ₊₁⌋⟩`: its
partial denominator is the `(n+1)`-th partial quotient `⌊completeQuotient v (n + 1)⌋`. -/
@[category API, AMS 11]
theorem of_s_get?_eq {v : ℝ} (hirr : Irrational v) (n : ℕ) :
    (GenContFract.of v).s.get? n = some ⟨1, (⌊completeQuotient v (n + 1)⌋ : ℝ)⟩ := by
  exact GenContFract.get?_of_eq_some_of_succ_get?_intFractPair_stream
    (intFractPair_stream_eq hirr (n + 1))

/-- **Complete quotients are eventually periodic** (the analytic heart of Euler's direction). If
the continued-fraction terms of an irrational `ξ` are eventually periodic, then two complete
quotients coincide, `ξ_M = ξ_{M+p}`: the equal partial-quotient tails make
`GenContFract.of ξ_M = GenContFract.of ξ_{M+p}` (identical floor data), and continued-fraction
convergence (`GenContFract.of_convergence`) forces the two limits to agree. -/
@[category API, AMS 11]
theorem completeQuotient_eq_of_isEvPeriodic {ξ : ℝ} (hirr : Irrational ξ)
    (hper : IsEventuallyPeriodicContFrac ξ) :
    ∃ M p : ℕ, 0 < M ∧ 0 < p ∧ completeQuotient ξ M = completeQuotient ξ (M + p) := by
  obtain ⟨N, p, hp, hper⟩ := hper
  have hpq : ∀ m, N + 1 ≤ m → ⌊completeQuotient ξ (m + p)⌋ = ⌊completeQuotient ξ m⌋ := by
    intro m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hget := hper k (by omega)
    rw [of_s_get?_eq hirr (k + p), of_s_get?_eq hirr k] at hget
    simp only [Option.some.injEq, GenContFract.Pair.mk.injEq, Int.cast_inj] at hget
    rw [show k + 1 + p = k + p + 1 from by omega]
    exact hget.2
  refine ⟨N + 1, p, Nat.succ_pos N, hp, ?_⟩
  set M := N + 1 with hM
  have hiu : Irrational (completeQuotient ξ M) := completeQuotient_irrational hirr M
  have hiw : Irrational (completeQuotient ξ (M + p)) := completeQuotient_irrational hirr (M + p)
  have hfloor : ∀ j, ⌊completeQuotient (completeQuotient ξ M) j⌋
      = ⌊completeQuotient (completeQuotient ξ (M + p)) j⌋ := by
    intro j
    rw [completeQuotient_add, completeQuotient_add, show M + p + j = M + j + p from by omega]
    exact (hpq (M + j) (by omega)).symm
  have hof : GenContFract.of (completeQuotient ξ M)
      = GenContFract.of (completeQuotient ξ (M + p)) := by
    apply GenContFract.ext
    · rw [GenContFract.of_h_eq_floor, GenContFract.of_h_eq_floor]
      exact_mod_cast (hpq M (by omega)).symm
    · apply Stream'.Seq.ext
      intro n
      rw [of_s_get?_eq hiu n, of_s_get?_eq hiw n, hfloor (n + 1)]
  have h1 := GenContFract.of_convergence (completeQuotient ξ M)
  have h2 := GenContFract.of_convergence (completeQuotient ξ (M + p))
  rw [hof] at h1
  exact tendsto_nhds_unique h1 h2

/-- **Euler's direction** (the easy half, 1737). If `ξ` is irrational and its continued
fraction expansion is eventually periodic, then `ξ` is a quadratic irrational:
`(minpoly ℚ ξ).natDegree = 2`.

*Idea.* Eventual periodicity yields two coinciding complete quotients `ξ_M = ξ_{M+p}`
(`completeQuotient_eq_of_isEvPeriodic`). Applying the convergent/Möbius relation `qConv_mobius`
to `ξ_M` over the period (using `ξ_{M+p} = ξ_M`) makes `ξ_M` a root of an integer quadratic with
nonzero leading coefficient; substituting `ξ = (ξ_M·numₘ + numₘ₋₁)/(ξ_M·denₘ + denₘ₋₁)` then
yields an integer quadratic for `ξ`, whose leading coefficient is nonzero because `ξ_M` is
irrational (so that quadratic has no rational root). The finisher is
`minpoly_natDegree_two_of_irrational_quadratic`. -/
@[category research solved, AMS 11, ref "HW79" "NZM91" "Khi64", solved_by "Euler" 1737]
theorem euler_periodic_imp_quadratic {ξ : ℝ} (hirr : Irrational ξ)
    (hper : IsEventuallyPeriodicContFrac ξ) :
    (minpoly ℚ ξ).natDegree = 2 := by
  obtain ⟨M, p, hM0, hp, hMp⟩ := completeQuotient_eq_of_isEvPeriodic hirr hper
  have hiw : Irrational (completeQuotient ξ M) := completeQuotient_irrational hirr M
  -- `ξ_M`'s integer quadratic, from `qConv_mobius` over the period (`ξ_{M+p} = ξ_M`).
  have hmobw := qConv_mobius hiw p
  have hcqw : completeQuotient (completeQuotient ξ M) p = completeQuotient ξ M := by
    rw [completeQuotient_add]; exact hMp.symm
  rw [hcqw] at hmobw
  set Cw := (qConv (completeQuotient ξ M) (p + 1)).2 with hCw
  set Dw := (qConv (completeQuotient ξ M) p).2 with hDw
  set Aw := (qConv (completeQuotient ξ M) (p + 1)).1 with hAw
  set Bw := (qConv (completeQuotient ξ M) p).1 with hBw
  have hquadw : (Cw : ℝ) * completeQuotient ξ M ^ 2
      + ((Dw : ℝ) - Aw) * completeQuotient ξ M - Bw = 0 := by linear_combination hmobw
  have hCw1 : (1 : ℤ) ≤ Cw := by
    obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
    rw [hCw, hq]; exact (qConv_den hiw q).2
  -- `ξ = (ξ_M·numₘ + numₘ₋₁)/(ξ_M·denₘ + denₘ₋₁)`.
  have hmobξ := qConv_mobius hirr M
  set e := (qConv ξ (M + 1)).1 with he
  set f := (qConv ξ M).1 with hf
  set g := (qConv ξ (M + 1)).2 with hg
  set hh := (qConv ξ M).2 with hhh
  have hg1 : (1 : ℤ) ≤ g := by
    obtain ⟨q, hq⟩ : ∃ q, M = q + 1 := ⟨M - 1, by omega⟩
    rw [hg, hq]; exact (qConv_den hirr q).2
  have hgR : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have hge : (g : ℝ) * ξ - e ≠ 0 := by
    intro h0
    refine hirr ⟨(e : ℚ) / g, ?_⟩
    rw [Rat.cast_div]; push_cast; rw [div_eq_iff hgR.ne']; linear_combination -h0
  have hsub : (f : ℝ) - hh * ξ = completeQuotient ξ M * ((g : ℝ) * ξ - e) := by
    linear_combination -hmobξ
  -- Eliminate `ξ_M`: an integer quadratic for `ξ`.
  have hξquad : ((Cw * hh ^ 2 - (Dw - Aw) * hh * g - Bw * g ^ 2 : ℤ) : ℝ) * ξ ^ 2
      + ((-2 * Cw * f * hh + (Dw - Aw) * (f * g + hh * e) + 2 * Bw * g * e : ℤ) : ℝ) * ξ
      + ((Cw * f ^ 2 - (Dw - Aw) * f * e - Bw * e ^ 2 : ℤ) : ℝ) = 0 := by
    have hexp : ((Cw * hh ^ 2 - (Dw - Aw) * hh * g - Bw * g ^ 2 : ℤ) : ℝ) * ξ ^ 2
        + ((-2 * Cw * f * hh + (Dw - Aw) * (f * g + hh * e) + 2 * Bw * g * e : ℤ) : ℝ) * ξ
        + ((Cw * f ^ 2 - (Dw - Aw) * f * e - Bw * e ^ 2 : ℤ) : ℝ)
        = (Cw : ℝ) * ((f : ℝ) - hh * ξ) ^ 2
          + ((Dw : ℝ) - Aw) * ((f : ℝ) - hh * ξ) * ((g : ℝ) * ξ - e)
          - (Bw : ℝ) * ((g : ℝ) * ξ - e) ^ 2 := by push_cast; ring
    rw [hexp, hsub]; linear_combination ((g : ℝ) * ξ - e) ^ 2 * hquadw
  -- Leading coefficient is nonzero (else `ξ_M` would be rational).
  have hα : (Cw * hh ^ 2 - (Dw - Aw) * hh * g - Bw * g ^ 2 : ℤ) ≠ 0 := by
    intro h0
    have h0R : (Cw : ℝ) * (hh : ℝ) ^ 2 - ((Dw : ℝ) - Aw) * hh * g - Bw * (g : ℝ) ^ 2 = 0 := by
      exact_mod_cast h0
    have hgne : (g : ℝ) ≠ 0 := hgR.ne'
    have hCwR : (Cw : ℝ) ≠ 0 := by
      have : (0 : ℝ) < Cw := by exact_mod_cast (by omega : (0 : ℤ) < Cw)
      exact this.ne'
    have hfac : ((g : ℝ) * completeQuotient ξ M + hh)
        * ((Cw : ℝ) * ((g : ℝ) * completeQuotient ξ M - hh) + ((Dw : ℝ) - Aw) * g) = 0 := by
      linear_combination (g : ℝ) ^ 2 * hquadw - h0R
    rcases mul_eq_zero.mp hfac with h1 | h2
    · refine hiw ⟨-(hh : ℚ) / g, ?_⟩
      rw [Rat.cast_div]; push_cast; rw [div_eq_iff hgne]; linear_combination -h1
    · refine hiw ⟨((Cw : ℚ) * hh - (Dw - Aw) * g) / (Cw * g), ?_⟩
      rw [Rat.cast_div]; push_cast; rw [div_eq_iff (mul_ne_zero hCwR hgne)]
      linear_combination -h2
  exact minpoly_natDegree_two_of_irrational_quadratic hirr hα hξquad

/-- **Lagrange's theorem.** A real number `ξ` is a quadratic irrational — algebraic of
degree exactly two over `ℚ`, i.e. `(minpoly ℚ ξ).natDegree = 2` — if and only if it is
irrational and its simple continued fraction expansion is eventually periodic. Combines
`euler_periodic_imp_quadratic` (`⇐`, Euler 1737) and `lagrange_quadratic_imp_periodic`
(`⇒`, Lagrange 1770). -/
@[category research solved, AMS 11, ref "HW79" "NZM91" "Khi64", solved_by "Euler" 1737, solved_by "Lagrange" 1770]
theorem lagrange (ξ : ℝ) :
    (minpoly ℚ ξ).natDegree = 2 ↔ Irrational ξ ∧ IsEventuallyPeriodicContFrac ξ :=
  ⟨lagrange_quadratic_imp_periodic, fun h => euler_periodic_imp_quadratic h.1 h.2⟩
