/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The skew branch: Diophantine constraints, and the surviving sliver

This is §§8–9 of `BB47/M3.tex`, milestone M3 of `plans/plan-1047.html`.

Theorem C of that note puts branch (b) of the structure theorem into arithmetic normal form: if
the `ω`-limit set of the base-`b` digit word of `ξ` contains a periodic orbit, then

  `ξ = ρ + δ · ∑_{j} b^{-t_j}`,  `ρ, δ ∈ ℚ`, `δ ≠ 0`,  `t_{j+1} − t_j → ∞`,

where the `t_j` are the positions of the defects.  All the `δ`-coefficients are **equal** — the
plan had predicted a signed, blocked sparse series and flagged that as an obstacle to applying
Bailey–Borwein–Crandall–Pomerance; the structure theorem removes the obstacle, because the defect
vertices of `G'_n(Ω)` form a single simple path with one entry and one exit, so every defect
traverses it with the same periodic phase before and after.  Since `ρ, δ` are rational, `ξ` is
algebraic of degree `D` if and only if the **sparse number**

  `y = ∑_{j} b^{-t_j}`  (`BB47.sparseValue`)

is, and every constraint below applies to `ξ`.

This file states those constraints.  One of them is proved here from a cited theorem; two are
themselves the cited theorems, transcribed to base `b`.

## Main results

* `BB47.ridout` — [Rid57], cited: rational approximations with `b`-smooth denominators.
* `BB47.irrational_of_one_lt_minpoly_natDegree` — degree `> 1` forces irrationality.
* `BB47.theorem_D` — **proved**: [M3, Thm. 8.1].  If `y` is algebraic irrational then
  `t_{J+1} ≤ (1+ε)·t_J + log_b 2` eventually, for every `ε > 0`.
* `BB47.theorem_D_ratio` — the quotable form `t_{J+1}/t_J → 1`.
* `BB47.bbcp_base_b` — [BBCP04, Thm. 7.1] in base `b`, cited: `t_j ≪ j^D`.
* `BB47.nesterenko_theta` — [Nes96] through [M3, Thm. 8.4(ii)], cited: `t_j = a·j² + d` makes `y`
  a theta value, hence transcendental.
* `BB47.superlinear_of_gaps` — **proved**: the gap condition `t_{j+1} − t_j → ∞` of [M3, Prop.
  6.1] forces `t_j/j → ∞`.  This is constraint (b1) of the sliver.
* `BB47.sliver` — **[M3, Cor. 9.1(b)]**: the four constraints (b1)–(b4), assembled.

## Why the sliver is not empty

Constraint (b2) forbids geometric growth and (b3) forbids growth faster than `j^D`, so for a
*quadratic* `ξ` the defect positions must satisfy `j·ω(1) ≤ t_j ≤ O(j²)` with `t_{j+1}/t_j → 1`
— i.e. grow like `j^{2−o(1)}` — and by (b4) must do so irregularly.  Nesterenko's theorem governs
the **full** theta series `∑_{j ∈ ℤ} Q^{j²}`, and a general quadratic `t_j = a j² + c j + d`
produces a *partial* theta `∑_{j ≥ 1} Q^{j²} z^j`, which is out of its reach when `a ∤ c`.  That
gap is exactly what keeps the sliver non-empty; closing it would close branch (b) of Problem
10.47 outright.

## Scope

Theorem C itself — the passage from the skew branch to the normal form — is **not** formalized
here: it needs the two-sided structure theorem [M3, Thm. 4.1], whose proof runs through
compactness of the `ω`-limit subshift and the classification of Coven–Hedlund.  What is machine-
checked in this root of that chain is its combinatorial engine, `BB47.mem_of_outClosed`.  The
sparse series is therefore taken as the hypothesis here, which is how §§8–9 of [M3] are written
anyway.

## References

* [Rid57] D. Ridout, *Rational approximations to algebraic numbers*, Mathematika **4** (1957),
  125–131.
* [BBCP04] D. Bailey, J. Borwein, R. Crandall, C. Pomerance, *On the binary expansions of
  algebraic numbers*, J. Théor. Nombres Bordeaux **16** (2004), 487–518 — Thm. 7.1, and §§2, 3, 6.
* [Nes96] Yu. Nesterenko, *Modular functions and transcendence questions*, Mat. Sb. **187**
  (1996), 65–96; with D. Bertrand, Ramanujan J. **1** (1997), 339–350.
* [M3] `BB47/M3.tex` (this repository, 2026-09) — §§6–9, Thms. 8.1–8.3, Cor. 9.1.
-/

namespace BB47

/-- The **sparse number** `∑_j b^{-t_j}`: the base-`b` number whose digits are `1` exactly at the
positions `t j` and `0` elsewhere. -/
@[category API, AMS 11 37, ref "BBCP04", group "bugeaud_10_47"]
noncomputable def sparseValue (b : ℕ) (t : ℕ → ℕ) : ℝ := ∑' j : ℕ, ((b : ℝ) ^ t j)⁻¹

/-! ## Elementary facts about the sparse series -/

section Elementary

variable {b : ℕ} (hb : 2 ≤ b) {t : ℕ → ℕ} (ht : StrictMono t)

include hb in
private lemma one_lt_b : (1 : ℝ) < (b : ℝ) := by
  have : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  linarith

include hb in
private lemma inv_b_le_half : (b : ℝ)⁻¹ ≤ 1 / 2 := by
  have h2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have h0 : (0 : ℝ) < (b : ℝ) := by linarith
  have hbinv : (b : ℝ)⁻¹ * (b : ℝ) = 1 := inv_mul_cancel₀ (ne_of_gt h0)
  have hinvpos : (0 : ℝ) < (b : ℝ)⁻¹ := inv_pos.mpr h0
  nlinarith [mul_nonneg (le_of_lt hinvpos) (by linarith : (0 : ℝ) ≤ (b : ℝ) - 2)]

include hb in
private lemma inv_b_lt_one : (b : ℝ)⁻¹ < 1 := by
  have := inv_b_le_half hb
  linarith

include ht in
private lemma add_le_strictMono (m i : ℕ) : t m + i ≤ t (m + i) := by
  induction i with
  | zero => simp
  | succ k ih =>
    have h1 : t (m + k) < t (m + k + 1) := ht (Nat.lt_succ_self _)
    have h2 : m + (k + 1) = m + k + 1 := by omega
    rw [h2]
    omega

include hb ht in
private lemma summable_sparse : Summable fun j : ℕ => ((b : ℝ) ^ t j)⁻¹ := by
  have hb1 := one_lt_b hb
  have hgeo : Summable fun j : ℕ => ((b : ℝ)⁻¹) ^ j :=
    summable_geometric_of_lt_one (by positivity) (inv_b_lt_one hb)
  refine hgeo.of_nonneg_of_le (fun j => by positivity) fun j => ?_
  rw [← inv_pow]
  exact pow_le_pow_of_le_one (by positivity) (le_of_lt (inv_b_lt_one hb)) ht.le_apply

include hb ht in
/-- The tail of the sparse series past index `J` is at most `2·b^{-t_{J+1}}`: the exponents grow
by at least one at each step, so the tail is dominated by a geometric series of ratio `1/b ≤ 1/2`.
-/
private lemma tail_le (J : ℕ) :
    (∑' i : ℕ, ((b : ℝ) ^ t (i + (J + 1)))⁻¹) ≤ 2 * ((b : ℝ) ^ t (J + 1))⁻¹ := by
  have hb1 := one_lt_b hb
  have hsum : Summable fun i : ℕ => ((b : ℝ) ^ t (i + (J + 1)))⁻¹ :=
    (summable_sparse hb ht).comp_injective (add_left_injective (J + 1))
  have hgeo : Summable fun i : ℕ => ((b : ℝ) ^ t (J + 1))⁻¹ * ((b : ℝ)⁻¹) ^ i :=
    Summable.mul_left _ (summable_geometric_of_lt_one (by positivity) (inv_b_lt_one hb))
  have hle : ∀ i : ℕ, ((b : ℝ) ^ t (i + (J + 1)))⁻¹
      ≤ ((b : ℝ) ^ t (J + 1))⁻¹ * ((b : ℝ)⁻¹) ^ i := by
    intro i
    have hexp : t (J + 1) + i ≤ t (i + (J + 1)) := by
      have := add_le_strictMono ht (J + 1) i
      rwa [show J + 1 + i = i + (J + 1) by omega] at this
    have hrhs : ((b : ℝ) ^ t (J + 1))⁻¹ * ((b : ℝ)⁻¹) ^ i
        = ((b : ℝ) ^ (t (J + 1) + i))⁻¹ := by
      rw [← inv_pow, ← pow_add, inv_pow]
    rw [hrhs, inv_le_inv₀ (by positivity) (by positivity)]
    exact pow_le_pow_right₀ (le_of_lt hb1) hexp
  refine le_trans (hsum.tsum_le_tsum hle hgeo) ?_
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) (inv_b_lt_one hb)]
  have hH : (1 : ℝ) / 2 ≤ 1 - (b : ℝ)⁻¹ := by have := inv_b_le_half hb; linarith
  have hposH : (0 : ℝ) < 1 - (b : ℝ)⁻¹ := by linarith
  have hXH : (1 - (b : ℝ)⁻¹)⁻¹ * (1 - (b : ℝ)⁻¹) = 1 := inv_mul_cancel₀ (ne_of_gt hposH)
  have hXpos : (0 : ℝ) < (1 - (b : ℝ)⁻¹)⁻¹ := inv_pos.mpr hposH
  have hfac : (1 - (b : ℝ)⁻¹)⁻¹ ≤ 2 := by
    nlinarith [mul_nonneg (le_of_lt hXpos) (by linarith : (0 : ℝ) ≤ (1 - (b : ℝ)⁻¹) - 1 / 2)]
  have hpos2 : (0 : ℝ) ≤ ((b : ℝ) ^ t (J + 1))⁻¹ := by positivity
  nlinarith

include hb ht in
/-- The truncation of the sparse series is the rational `A_J / b^{t_J}` with `A_J` an integer. -/
private lemma partial_sum_eq (J : ℕ) :
    ∑ j ∈ Finset.range (J + 1), ((b : ℝ) ^ t j)⁻¹
      = ((∑ j ∈ Finset.range (J + 1), b ^ (t J - t j) : ℕ) : ℝ) / (b : ℝ) ^ t J := by
  have hbpos : (0 : ℝ) < (b : ℝ) := by linarith [one_lt_b hb]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  have hle : t j ≤ t J := ht.monotone (by omega)
  rw [eq_div_iff (by positivity : ((b : ℝ) ^ t J) ≠ 0), inv_mul_eq_div,
    div_eq_iff (by positivity : ((b : ℝ) ^ t j) ≠ 0), ← pow_add,
    show t J - t j + t j = t J by omega]

end Elementary

/-! ## Ridout's theorem, and Theorem D -/

/-- **[Rid57], Ridout's theorem** in the shape used by [M3, Thm. 8.1]: for an algebraic `y` and
every `ε > 0`, the inequality `|y − A/b^m| < b^{−m(1+ε)}` has only finitely many solutions
`(A, m) ∈ ℤ × ℕ`.

Transcribed with the equivalent quantifier `∃ m₀, ∀ m ≥ m₀, ∀ A` — equivalent because for each
fixed `m` the inequality already confines `A` to at most two values, so a solution set meeting
infinitely many `m` is infinite.

This is the `μ = 1, ν = 0` specialisation of Ridout's theorem, i.e. Roth's theorem with the
denominator's `b`-smooth part discounted: the exponent is `1 + ε` instead of `2 + ε`.  Cited
axiom.

`Irrational y` is **not** decoration: Ridout's theorem is about algebraic *irrational* numbers,
and for `y = A/b^m` the left-hand side is positive while the right-hand side vanishes.  Dropping
it would make this axiom inconsistent. -/
@[category research solved, AMS 11 37, ref "Rid57", group "bugeaud_10_47"]
axiom ridout (b : ℕ) (hb : 2 ≤ b) (y : ℝ) (hy : IsAlgebraic ℚ y) (hirr : Irrational y)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℕ, ∀ (A : ℤ) (m : ℕ), m₀ ≤ m →
      (b : ℝ) ^ (-(m : ℝ) * (1 + ε)) ≤ |y - (A : ℝ) / (b : ℝ) ^ m|

/-- **[M3, Thm. 8.1] (Theorem D).**  If the sparse number `∑_j b^{-t_j}` is algebraic then the
exponents grow sub-geometrically: for every `ε > 0`, eventually
`t_{J+1} ≤ (1 + ε)·t_J + log_b 2`.

The truncation `y_J = ∑_{j ≤ J} b^{-t_j}` is a fraction with denominator `b^{t_J}` — the
`b`-smooth denominator Ridout discounts — and the error `y − y_J` is at most `2·b^{-t_{J+1}}`, so
a large gap `t_{J+1} ≫ t_J` would give an approximation too good for an algebraic number. -/
@[category research solved, AMS 11 37, ref "Rid57", group "bugeaud_10_47"]
theorem theorem_D (b : ℕ) (hb : 2 ≤ b) (t : ℕ → ℕ) (ht : StrictMono t)
    (halg : IsAlgebraic ℚ (sparseValue b t)) (hirr : Irrational (sparseValue b t))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J →
      (t (J + 1) : ℝ) ≤ (1 + ε) * (t J : ℝ) + Real.logb b 2 := by
  have hb1 : (1 : ℝ) < (b : ℝ) := one_lt_b hb
  have hbpos : (0 : ℝ) < (b : ℝ) := by linarith
  obtain ⟨m₀, hm₀⟩ := ridout b hb (sparseValue b t) halg hirr hε
  refine ⟨m₀, fun J hJ => ?_⟩
  set A : ℤ := ((∑ j ∈ Finset.range (J + 1), b ^ (t J - t j) : ℕ) : ℤ) with hA
  have hsum := summable_sparse hb ht
  have hsplit : (∑ j ∈ Finset.range (J + 1), ((b : ℝ) ^ t j)⁻¹)
      + (∑' i : ℕ, ((b : ℝ) ^ t (i + (J + 1)))⁻¹) = sparseValue b t :=
    hsum.sum_add_tsum_nat_add (J + 1)
  have hpart := partial_sum_eq hb ht J
  have hdiff : sparseValue b t - (A : ℝ) / (b : ℝ) ^ t J
      = ∑' i : ℕ, ((b : ℝ) ^ t (i + (J + 1)))⁻¹ := by
    rw [← hsplit, hpart, hA]
    push_cast
    ring
  have hnn : (0 : ℝ) ≤ ∑' i : ℕ, ((b : ℝ) ^ t (i + (J + 1)))⁻¹ :=
    tsum_nonneg fun i => by positivity
  have hsmall := tail_le hb ht J
  have hmJ : m₀ ≤ t J := le_trans hJ ht.le_apply
  have hrid := hm₀ A (t J) hmJ
  rw [hdiff, abs_of_nonneg hnn] at hrid
  have hkey : (b : ℝ) ^ (-(t J : ℝ) * (1 + ε)) ≤ 2 * ((b : ℝ) ^ t (J + 1))⁻¹ :=
    le_trans hrid hsmall
  have hrw : ((b : ℝ) ^ t (J + 1))⁻¹ = (b : ℝ) ^ (-(t (J + 1) : ℝ)) := by
    rw [Real.rpow_neg (le_of_lt hbpos), Real.rpow_natCast]
  rw [hrw] at hkey
  have hpos : (0 : ℝ) < (b : ℝ) ^ ((t (J + 1) : ℝ)) := Real.rpow_pos_of_pos hbpos _
  have hmul : (b : ℝ) ^ ((t (J + 1) : ℝ) - (t J : ℝ) * (1 + ε)) ≤ 2 := by
    have hstep := mul_le_mul_of_nonneg_right hkey (le_of_lt hpos)
    rw [mul_assoc, ← Real.rpow_add hbpos, ← Real.rpow_add hbpos, neg_add_cancel,
      Real.rpow_zero, mul_one] at hstep
    rw [show (t (J + 1) : ℝ) - (t J : ℝ) * (1 + ε)
      = -(t J : ℝ) * (1 + ε) + (t (J + 1) : ℝ) by ring]
    exact hstep
  have hlog := Real.logb_le_logb_of_le hb1 (Real.rpow_pos_of_pos hbpos _) hmul
  rw [Real.logb_rpow hbpos (by linarith : (b : ℝ) ≠ 1)] at hlog
  linarith

/-- The quotable form of Theorem D: `t_{J+1}/t_J → 1`.  Stated as: for every `ε > 0`, eventually
`t_{J+1} ≤ (1 + ε)·t_J`.  (The additive `log_b 2 ≤ 1` of `BB47.theorem_D` is absorbed because
`t_J ≥ J → ∞`.) -/
@[category research solved, AMS 11 37, ref "Rid57", group "bugeaud_10_47"]
theorem theorem_D_ratio (b : ℕ) (hb : 2 ≤ b) (t : ℕ → ℕ) (ht : StrictMono t)
    (halg : IsAlgebraic ℚ (sparseValue b t)) (hirr : Irrational (sparseValue b t))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → (t (J + 1) : ℝ) ≤ (1 + ε) * (t J : ℝ) := by
  have hb1 : (1 : ℝ) < (b : ℝ) := one_lt_b hb
  obtain ⟨J₁, hJ₁⟩ := theorem_D b hb t ht halg hirr (half_pos hε)
  -- `log_b 2 ≤ 1` because `b ≥ 2`
  have hlogb : Real.logb b 2 ≤ 1 := by
    have h2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    have := Real.logb_le_logb_of_le hb1 (by norm_num : (0 : ℝ) < 2) h2
    rwa [Real.logb_self_eq_one hb1] at this
  -- choose `J₀` so large that `1 ≤ (ε/2)·t_J`
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
  refine ⟨max J₁ N, fun J hJ => ?_⟩
  have hJ1 : J₁ ≤ J := le_trans (le_max_left _ _) hJ
  have hJN : N ≤ J := le_trans (le_max_right _ _) hJ
  have htJ : (N : ℝ) ≤ (t J : ℝ) := by
    have : N ≤ t J := le_trans hJN ht.le_apply
    exact_mod_cast this
  have habs : 1 ≤ ε / 2 * (t J : ℝ) := by
    have h1 : 2 / ε ≤ (t J : ℝ) := le_trans (le_of_lt hN) htJ
    rw [div_le_iff₀ hε] at h1
    nlinarith
  have := hJ₁ J hJ1
  nlinarith

/-! ## The quoted constraints -/

/-- **[BBCP04, Thm. 7.1] in base `b`** ([M3, Thm. 8.2]).  If the sparse number is algebraic of
degree `D > 1`, the digit-`1` positions satisfy `t_j ≪ j^D`; equivalently the counting function
`R(N) = #{j : t_j ≤ N}` is `≫ N^{1/D}`.

Cited axiom.  [BBCP04] prove it in base `2`; [M3, Thm. 8.2] checks that all six ingredients of
their §§2, 3, 6, 7 transcribe to base `b` unchanged — in particular [BBCP04, Lem. 6.2], the
propagation of positivity, which uses only `A_D > 0` and `r_D ≥ 0`.  That transcription is the
reason the *unsigned, unblocked* normal form of [M3, Thm. 7.1] matters: had the coefficients
varied in sign, Lem. 6.2 would have failed and sparseness would have been destroyed by borrow
propagation. -/
@[category research solved, AMS 11 37, ref "BBCP04", group "bugeaud_10_47"]
axiom bbcp_base_b (b : ℕ) (hb : 2 ≤ b) (t : ℕ → ℕ) (ht : StrictMono t)
    (halg : IsAlgebraic ℚ (sparseValue b t))
    (hdeg : 1 < (minpoly ℚ (sparseValue b t)).natDegree) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, 1 ≤ j →
      (t j : ℝ) ≤ C * (j : ℝ) ^ (minpoly ℚ (sparseValue b t)).natDegree

/-- **[Nes96] through [M3, Thm. 8.4(ii)]**.  If the digit-`1` positions are eventually
`t_j = a·j² + d` with `a ≥ 1`, the sparse number is a value of the theta function `θ₃` at the
algebraic point `b^{-a}` in the punctured unit disc, hence transcendental by Nesterenko's theorem
on the algebraic independence of `P, Q, R` at algebraic points.

Cited axiom.  Note that this does **not** extend for free to a general quadratic
`t_j = a·j² + c·j + d`: the resulting series is a *partial* theta `∑_{j≥1} Q^{j²} z^j`, and
Nesterenko's theorem governs the full theta `∑_{j ∈ ℤ}`.  That gap is exactly what keeps the
sliver of [M3, §9] non-empty. -/
@[category research solved, AMS 11 37, ref "Nes96", group "bugeaud_10_47"]
axiom nesterenko_theta (b : ℕ) (hb : 2 ≤ b) (t : ℕ → ℕ) (ht : StrictMono t) (a d : ℕ)
    (ha : 1 ≤ a) (h : ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → t j = a * j ^ 2 + d) :
    Transcendental ℚ (sparseValue b t)

/-- An algebraic number whose minimal polynomial has degree `> 1` is irrational.  This is what
lets `BB47.sliver` feed `BB47.theorem_D` without an extra hypothesis: a sparse number of degree
`D > 1` is automatically irrational. -/
@[category API, AMS 11 37, ref "Rid57", group "bugeaud_10_47"]
theorem irrational_of_one_lt_minpoly_natDegree {y : ℝ} (h : 1 < (minpoly ℚ y).natDegree) :
    Irrational y := by
  rintro ⟨q, rfl⟩
  have hmin : minpoly ℚ ((q : ℝ)) = Polynomial.X - Polynomial.C q := by
    simpa using minpoly.eq_X_sub_C (A := ℚ) (B := ℝ) q
  rw [hmin, Polynomial.natDegree_X_sub_C] at h
  omega

/-! ## Constraint (b1), and the assembly -/

/-- **Constraint (b1)** of [M3, Cor. 9.1].  Gaps tending to infinity force `t_j/j → ∞`: the
defect positions of the skew branch are superlinear.

This is why Theorem A of [M1M2] never reaches branch (b) — it needs `s_n = O(n)` along a
subsequence, and by [M3, Rem. 9.2] `s_n = t_{J(n)} + O(n)`. -/
@[category research solved, AMS 11 37, ref "BBCP04", group "bugeaud_10_47"]
theorem superlinear_of_gaps {t : ℕ → ℕ} (ht : StrictMono t)
    (hgap : ∀ M : ℕ, ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → M ≤ t (j + 1) - t j) (M : ℕ) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → M * j ≤ t j := by
  obtain ⟨j₁, hj₁⟩ := hgap (2 * M)
  set c : ℕ := 2 * M with hc
  have key : ∀ d : ℕ, t j₁ + c * d ≤ t (j₁ + d) := by
    intro d
    induction d with
    | zero => simp
    | succ k ih =>
      have hg := hj₁ (j₁ + k) (by omega)
      have hmono : t (j₁ + k) ≤ t (j₁ + k + 1) := ht.monotone (by omega)
      have hstep : c * (k + 1) = c * k + c := by rw [Nat.mul_succ]
      rw [show j₁ + (k + 1) = j₁ + k + 1 by omega]
      omega
  refine ⟨2 * j₁ + 1, fun j hj => ?_⟩
  have hd := key (j - j₁)
  rw [show j₁ + (j - j₁) = j by omega] at hd
  have hcoef : M * j ≤ c * (j - j₁) := by
    have hb2 : j ≤ 2 * (j - j₁) := by omega
    calc M * j ≤ M * (2 * (j - j₁)) := Nat.mul_le_mul_left M hb2
      _ = c * (j - j₁) := by rw [hc]; ring
  omega

/-- **[M3, Cor. 9.1(b)]: the surviving sliver.**  For a sparse number `y = ∑_j b^{-t_j}` with
gaps tending to infinity — the arithmetic normal form of the skew branch, [M3, Thm. 7.1] — being
algebraic of degree `D > 1` forces *all four* constraints simultaneously:

* **(b1)** `t_j / j → ∞` (from the gap hypothesis, `BB47.superlinear_of_gaps`);
* **(b2)** `t_{J+1} / t_J → 1` (Ridout, `BB47.theorem_D_ratio`);
* **(b3)** `t_j ≪ j^D` (Bailey–Borwein–Crandall–Pomerance, `BB47.bbcp_base_b`);
* **(b4)** `(t_j)` is not eventually a pure quadratic `a·j² + d` (Nesterenko,
  `BB47.nesterenko_theta`).

For a **quadratic** `ξ` this reads `j·ω(1) ≤ t_j ≤ O(j²)` with `t_{J+1}/t_J → 1`: the defect
positions must grow like `j^{2−o(1)}` and must do so irregularly. -/
@[category research solved, AMS 11 37, ref "Rid57" "BBCP04" "Nes96", group "bugeaud_10_47"]
theorem sliver (b : ℕ) (hb : 2 ≤ b) (t : ℕ → ℕ) (ht : StrictMono t)
    (hgap : ∀ M : ℕ, ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → M ≤ t (j + 1) - t j)
    (halg : IsAlgebraic ℚ (sparseValue b t))
    (hdeg : 1 < (minpoly ℚ (sparseValue b t)).natDegree) :
    (∀ M : ℕ, ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → M * j ≤ t j) ∧
    (∀ ε : ℝ, 0 < ε → ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → (t (J + 1) : ℝ) ≤ (1 + ε) * (t J : ℝ)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, 1 ≤ j →
      (t j : ℝ) ≤ C * (j : ℝ) ^ (minpoly ℚ (sparseValue b t)).natDegree) ∧
    (∀ a d : ℕ, 1 ≤ a → ¬ ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → t j = a * j ^ 2 + d) := by
  have hirr : Irrational (sparseValue b t) := irrational_of_one_lt_minpoly_natDegree hdeg
  refine ⟨superlinear_of_gaps ht hgap, fun ε hε => theorem_D_ratio b hb t ht halg hirr hε,
    bbcp_base_b b hb t ht halg hdeg, fun a d ha hq => ?_⟩
  exact nesterenko_theta b hb t ht a d ha hq halg

end BB47
