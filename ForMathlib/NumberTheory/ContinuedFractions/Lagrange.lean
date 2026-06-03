/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/

import Mathlib.Algebra.ContinuedFractions.Computation.Basic
import Mathlib.Algebra.ContinuedFractions.Computation.Translations
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
Hardy–Wright, Niven–Zuckerman–Montgomery, and Khinchin (the one that maps cleanly onto the
existing Mathlib continued-fraction API: `GenContFract.determinant`, `abs_sub_convs_le`,
`sub_convs_eq`), not the reduced-surd/Galois route of Olds.

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

/-- **Euler's direction** (the easy half, 1737). If `ξ` is irrational and its continued
fraction expansion is eventually periodic, then `ξ` is a quadratic irrational:
`(minpoly ℚ ξ).natDegree = 2`.

*Idea.* Over one period the convergent recurrence expresses `ξ` as a fractional-linear
(Möbius) transform of itself, `ξ = (A·ξ + B)/(C·ξ + D)` with integer `A, B, C, D`; clearing
denominators yields an integer quadratic with `ξ` as a root, so `ξ` is algebraic of degree
`≤ 2`, and irrationality rules out degree `≤ 1`. -/
@[category research solved, AMS 11, ref "HW79" "NZM91" "Khi64", solved_by "Euler" 1737]
theorem euler_periodic_imp_quadratic {ξ : ℝ} (hirr : Irrational ξ)
    (hper : IsEventuallyPeriodicContFrac ξ) :
    (minpoly ℚ ξ).natDegree = 2 := by
  sorry

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

/-- **The crux bound.** The `qCoeffs` triples are bounded uniformly in `n`. Via the convergent
substitution `aₙ = qₙ₋₁² · f(pₙ₋₁/qₙ₋₁)` and the approximation `|ξ − pₙ₋₁/qₙ₋₁| < 1/qₙ₋₁²`
(`GenContFract.abs_sub_convs_le`), `|aₙ| ≤ |A|(|ξ − ξ'| + 1)`; then `cₙ = aₙ₋₁` and the invariant
discriminant (`qCoeffs_discrim`) bound `cₙ` and `bₙ`. -/
@[category API, AMS 11]
theorem qCoeffs_bounded {ξ : ℝ} {A B C : ℤ} (hirr : Irrational ξ) (hA : A ≠ 0)
    (h0 : (A : ℝ) * ξ ^ 2 + (B : ℝ) * ξ + (C : ℝ) = 0) :
    ∃ M : ℤ, ∀ n, |(qCoeffs ξ A B C n).1| ≤ M ∧ |(qCoeffs ξ A B C n).2.1| ≤ M
      ∧ |(qCoeffs ξ A B C n).2.2| ≤ M := by
  sorry

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

/-- **Lagrange's theorem.** A real number `ξ` is a quadratic irrational — algebraic of
degree exactly two over `ℚ`, i.e. `(minpoly ℚ ξ).natDegree = 2` — if and only if it is
irrational and its simple continued fraction expansion is eventually periodic. Combines
`euler_periodic_imp_quadratic` (`⇐`, Euler 1737) and `lagrange_quadratic_imp_periodic`
(`⇒`, Lagrange 1770). -/
@[category research solved, AMS 11, ref "HW79" "NZM91" "Khi64", solved_by "Euler" 1737, solved_by "Lagrange" 1770]
theorem lagrange (ξ : ℝ) :
    (minpoly ℚ ξ).natDegree = 2 ↔ Irrational ξ ∧ IsEventuallyPeriodicContFrac ξ :=
  ⟨lagrange_quadratic_imp_periodic, fun h => euler_periodic_imp_quadratic h.1 h.2⟩
