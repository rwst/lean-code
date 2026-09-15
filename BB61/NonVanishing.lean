/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.Multiplier
import ForMathlib.NumberTheory.RationalAlgebraicInteger
import ForMathlib.NumberTheory.PisotFractionalParts
import Mathlib.Tactic.ComputeDegree
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# M5 §5 at any degree: no factor of the Erdős product vanishes

Formal companion of `note-1061-M5.html` (milestone M5 of `plans/plan-1061.html`) §5.  The note
states its Bernoulli section for **every** Pisot `α > 2` and its table of constants contains
cubics; `BB61/Bernoulli.lean` proves it at degree two, through the explicit integer pair
`(α-1)αᵐ = uₘ + vₘ α`.  This file removes the degree restriction from the arithmetic.

> **Theorem 3 (no factor vanishes).**  Let `α > 2` be Pisot, `p ∈ (0,1)`, `h ≠ 0`.  Recall
> `φ_p(x) = 0` iff `p = 1/2` and `x ≡ 1/2 (mod 1)`.
> (i) *Past.* `φ_p(-h c_m) ≠ 0` for every `m ≥ 0`.
> (ii) *Off the symmetric point.* If `p ≠ 1/2` then `|φ_p(x)| ≥ |1-2p| > 0`.
> (iii) *Future at `h = 1`.* `(α-1)α^{-j} ∈ (0,1) \ {1/2}` for every `j ≥ 1`.
> (v) If `α` is a **unit**, `G_p(h) ≠ 0` for every `h ≠ 0` and every `p`; for a non-unit the
> only possible vanishing is at a future index with `α^j ≤ 2|h|(α-1)`.

## What the lift costs, and what it buys

The degree-two proof of (i) runs through `pw_snd_ne_zero` — "`vₘ ≠ 0`, hence `(α-1)αᵐ ∉ ℚ`" —
and therefore needs both `Irrational α` and `α > 2`.  Neither is needed.  The general proof is
the note's own two-line argument:

* the **trace identity** `c_m + (α-1)αᵐ = Tr((α-1)αᵐ) ∈ ℤ`, which is
  `ForMathlib/NumberTheory/ConjugatePowerSum.lean`'s `conj_shiftedPowerSum_isInt` together with
  `conj_erase_sum_add`, so that the past argument is congruent mod `1` to `-h(α-1)αᵐ`;
* **a rational algebraic integer is a rational integer**, which is
  `ForMathlib/NumberTheory/RationalAlgebraicInteger.lean`'s `IsIntegral.ne_intCast_add_half`:
  `1/2 + ℤ` contains no algebraic integer.

So `cos_ne_zero_of_isIntegral_ladder` — the past half at **any** degree — has exactly one
hypothesis, `IsIntegral ℤ α`, and holds for every `h` (including `h = 0`) and every `m`.  The
degree-two statement `QuadSetup.cos_past_ne_zero` of `BB61/Bernoulli.lean` is recovered here as
`QuadSetup.cos_past_ne_zero_of_isIntegral` **without** its `2 < α` and `Irrational α`
hypotheses; the same lemma is the general-degree form of `BB61/Multiplier.lean`'s
`cos_pi_ne_zero_of_isIntComb`, whose `IsIntComb` is `ℤ[α]` written in the degree-two basis.

Part (iii) is degree-free as it stands and is restated here for a bare real `α > 2`
(`cos_future_ne_zero_of_two_lt`); part (v) becomes `cos_future_ne_zero_of_isIntegral_inv`, where
the unit hypothesis appears in its invariant form `IsIntegral ℤ α⁻¹` — and it carries a
multiplier `λ` for free, which is Corollary 6's arithmetic at any degree.

## What is *not* lifted

Theorems 1 and 2 — the limit law and the product formula — remain degree two: they need the
coding `F`, its padding modulus and the convergence of the two infinite products, and that is a
separate construction, not a change of hypothesis.  What this file supplies is the input those
theorems consume, at any degree, plus the Pisot decay `‖(α-1)αᵐ‖ ≤ Cρᵐ`
(`exists_int_close_of_isPisot`, the general-degree form of `QuadSetup.exists_int_close`) that
drives M5 Theorem 8.

## The instance

`alphaCubic` is the real root of `X³ - 2X² - 1`, the `d = 3` line of `BB61/r3a_bern.log`.  It is
a unit (constant term `-1`), so `α⁻¹ = α² - 2α` is an algebraic integer and **both** ladders are
covered: `cos_past_ne_zero_alphaCubic` and `cos_future_ne_zero_alphaCubic` hold at every `h` and
every multiplier `λ ∈ ℤ[α]`.  No irrationality, no Pisot property and no numerical bound beyond
`2 < α` is used.
-/

namespace BB61

open Polynomial

/-! ## Theorem 3(i): the past factors, at any degree -/

/-- **No factor of an Erdős product with an algebraic-integer ladder vanishes.**  `φ_p(x) = 0`
forces `p = 1/2` and `x ∈ 1/2 + ℤ`, and `1/2 + ℤ` contains no algebraic integer. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem phi_ne_zero_of_isIntegral {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) {x : ℝ}
    (hx : IsIntegral ℤ x) : phi p x ≠ 0 := by
  rcases eq_or_ne p (1 / 2) with hp | hp
  · subst hp
    rw [← norm_ne_zero_iff, norm_phi_half, ncos, abs_ne_zero]
    exact hx.cos_pi_ne_zero
  · exact QuadSetup.phi_ne_zero_of_ne_half h0 h1 hp x

/-- **Theorem 3(i), any degree.**  The past argument `-h c_m` is congruent mod `1` to
`h(α-1)αᵐ`, an algebraic integer; so its cosine does not vanish.  Stated in the normal form
`N + h(α-1)αᵐ` with `N ∈ ℤ` arbitrary, which covers both signs.

Note the hypotheses: only `IsIntegral ℤ α`.  Neither `α > 2` nor `Irrational α` nor `h ≠ 0`
plays any role. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cos_ne_zero_of_isIntegral_ladder {θ : ℝ} (hθ : IsIntegral ℤ θ) (N h : ℤ) (m : ℕ) :
    Real.cos (Real.pi * ((N : ℝ) + (h : ℝ) * ((θ - 1) * θ ^ m))) ≠ 0 :=
  IsIntegral.cos_pi_ne_zero <|
    (isIntegral_intCast N).add
      ((isIntegral_intCast h).mul ((hθ.sub isIntegral_one).mul (hθ.pow m)))

/-- The `φ_p` form of `cos_ne_zero_of_isIntegral_ladder`, valid for every `p ∈ [0,1]`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem phi_ne_zero_of_isIntegral_ladder {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) {θ : ℝ}
    (hθ : IsIntegral ℤ θ) (N h : ℤ) (m : ℕ) :
    phi p ((N : ℝ) + (h : ℝ) * ((θ - 1) * θ ^ m)) ≠ 0 :=
  phi_ne_zero_of_isIntegral h0 h1 <|
    (isIntegral_intCast N).add
      ((isIntegral_intCast h).mul ((hθ.sub isIntegral_one).mul (hθ.pow m)))

/-- The **past ladder** at any degree: `c_m = ∑_{β ≠ α} (β-1)βᵐ`, the sum over the non-dominant
conjugates.  At degree two this is `(β-1)βᵐ` with `β` the single conjugate. -/
noncomputable def pastLadder (θ : ℝ) (m : ℕ) : ℂ :=
  ((((minpoly ℚ θ).aroots ℂ).erase (θ : ℂ)).map (fun z => (z - 1) * z ^ m)).sum

/-- **The trace identity at any degree.**  `c_m + (α-1)αᵐ` is a rational integer: it is the full
conjugate sum `Tr((α-1)αᵐ)`.  In particular `c_m` is real. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_int_pastLadder_add {θ : ℝ} (hθ : IsIntegral ℤ θ) (m : ℕ) :
    ∃ T : ℤ, pastLadder θ m + (((θ - 1) * θ ^ m : ℝ) : ℂ) = (T : ℂ) := by
  obtain ⟨T, hT⟩ := conj_shiftedPowerSum_isInt θ hθ m
  refine ⟨T, ?_⟩
  rw [pastLadder, ← hT, ← conj_erase_sum_add θ hθ (fun z => (z - 1) * z ^ m)]
  push_cast
  ring

/-- **Theorem 3(i), any degree, on the ladder itself.**  If `c` is the (real) past ladder entry
`c_m`, then no past factor `φ_p(-h c)` of the Erdős product vanishes. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem phi_pastLadder_ne_zero {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) {θ : ℝ}
    (hθ : IsIntegral ℤ θ) (h : ℤ) (m : ℕ) {c : ℝ} (hc : ((c : ℝ) : ℂ) = pastLadder θ m) :
    phi p (-((h : ℝ) * c)) ≠ 0 := by
  obtain ⟨T, hT⟩ := exists_int_pastLadder_add hθ m
  rw [← hc] at hT
  have hcT : c + (θ - 1) * θ ^ m = (T : ℝ) := by
    have h : (((c + (θ - 1) * θ ^ m : ℝ)) : ℂ) = ((T : ℝ) : ℂ) := by
      push_cast
      push_cast at hT
      linear_combination hT
    exact_mod_cast h
  have hrw : -((h : ℝ) * c) = ((-(h * T) : ℤ) : ℝ) + (h : ℝ) * ((θ - 1) * θ ^ m) := by
    push_cast
    linear_combination (-(h : ℝ)) * hcT
  rw [hrw]
  exact phi_ne_zero_of_isIntegral_ladder h0 h1 hθ _ h m

/-! ## Theorem 3(iii) and (v): the future factors, at any degree -/

/-- **Theorem 3(iii), any degree.**  `(α-1)/α^j ∈ (0,1) \ {1/2}` for every `j ≥ 1`: the first
entry exceeds `1/2` precisely because `α > 2`, and every later one is below `1/2` for free.
This is where — and the only place where — `α > 2` is spent in Route E. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cos_future_ne_zero_of_two_lt {θ : ℝ} (h2 : 2 < θ) {j : ℕ} (hj : 1 ≤ j) :
    Real.cos (Real.pi * ((θ - 1) / θ ^ j)) ≠ 0 := by
  have hα0 : (0 : ℝ) < θ := by linarith
  have hpow : (0 : ℝ) < θ ^ j := pow_pos hα0 j
  have hle : θ ≤ θ ^ j := by
    calc θ = θ ^ 1 := (pow_one _).symm
      _ ≤ θ ^ j := pow_le_pow_right₀ (by linarith) hj
  refine QuadSetup.cos_pi_ne_zero_of_mem (div_pos (by linarith) hpow) ?_ ?_
  · rw [div_lt_one hpow]; linarith
  · rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · have hj1 : j = 1 := by omega
      subst hj1
      rw [pow_one]
      intro hcon
      rw [div_eq_iff (ne_of_gt hα0)] at hcon
      linarith
    · have hpow2 : θ ^ 2 ≤ θ ^ j := pow_le_pow_right₀ (by linarith) hj2
      have hθ2 : (0 : ℝ) < θ ^ 2 := pow_pos hα0 2
      have hlt : (θ - 1) / θ ^ j ≤ (θ - 1) / θ ^ 2 :=
        div_le_div_of_nonneg_left (by linarith) hθ2 hpow2
      have hhalf : (θ - 1) / θ ^ 2 < 1 / 2 := by
        rw [div_lt_iff₀ hθ2]; nlinarith
      intro hcon
      rw [hcon] at hlt
      linarith

/-- The `φ_p` form of `cos_future_ne_zero_of_two_lt`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem phi_future_ne_zero_of_two_lt {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) {θ : ℝ} (h2 : 2 < θ)
    {j : ℕ} (hj : 1 ≤ j) : phi p ((θ - 1) / θ ^ j) ≠ 0 := by
  rcases eq_or_ne p (1 / 2) with hp | hp
  · subst hp
    rw [← norm_ne_zero_iff, norm_phi_half, ncos, abs_ne_zero]
    exact cos_future_ne_zero_of_two_lt h2 hj
  · exact QuadSetup.phi_ne_zero_of_ne_half h0 h1 hp _

/-- **Theorem 3(v), any degree, with a multiplier.**  At a *unit* — the invariant form of the
hypothesis being `IsIntegral ℤ α⁻¹` — the future ladder consists of algebraic integers too, so
part (i)'s argument covers it at every frequency `h` and every multiplier `λ ∈ ℤ[α]`.  This is
the arithmetic of Corollary 6 at any degree; `α > 2` is not used. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cos_future_ne_zero_of_isIntegral_inv {θ lam : ℝ} (hθ : IsIntegral ℤ θ)
    (hinv : IsIntegral ℤ θ⁻¹) (hlam : IsIntegral ℤ lam) (h : ℤ) (j : ℕ) :
    Real.cos (Real.pi * ((h : ℝ) * lam * (θ - 1) / θ ^ j)) ≠ 0 := by
  refine IsIntegral.cos_pi_ne_zero ?_
  have hrw : (h : ℝ) * lam * (θ - 1) / θ ^ j = (h : ℝ) * lam * (θ - 1) * (θ⁻¹) ^ j := by
    rw [inv_pow, div_eq_mul_inv]
  rw [hrw]
  exact (((isIntegral_intCast h).mul hlam).mul (hθ.sub isIntegral_one)).mul (hinv.pow j)

/-- The `φ_p` form of `cos_future_ne_zero_of_isIntegral_inv`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem phi_future_ne_zero_of_isIntegral_inv {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) {θ lam : ℝ}
    (hθ : IsIntegral ℤ θ) (hinv : IsIntegral ℤ θ⁻¹) (hlam : IsIntegral ℤ lam) (h : ℤ) (j : ℕ) :
    phi p ((h : ℝ) * lam * (θ - 1) / θ ^ j) ≠ 0 := by
  refine phi_ne_zero_of_isIntegral h0 h1 ?_
  have hrw : (h : ℝ) * lam * (θ - 1) / θ ^ j = (h : ℝ) * lam * (θ - 1) * (θ⁻¹) ^ j := by
    rw [inv_pow, div_eq_mul_inv]
  rw [hrw]
  exact (((isIntegral_intCast h).mul hlam).mul (hθ.sub isIntegral_one)).mul (hinv.pow j)

/-- **Theorem 3(v), the non-unit candidate list.**  If a future factor does vanish, i.e.
`h(α-1)α^{-j} ∈ 1/2 + ℤ`, then `2h(α-1) = s α^j` with `s` an odd integer, so `|s| ≥ 1` and
`α^j ≤ 2|h|(α-1)`: a finite, explicitly checkable list of indices `j`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem pow_le_of_future_half {θ : ℝ} (h2 : 2 < θ) {h : ℤ} {j : ℕ} {k : ℤ}
    (heq : (h : ℝ) * (θ - 1) / θ ^ j = (k : ℝ) + 1 / 2) :
    θ ^ j ≤ 2 * |(h : ℝ)| * (θ - 1) := by
  have hα0 : (0 : ℝ) < θ := by linarith
  have hpow : (0 : ℝ) < θ ^ j := pow_pos hα0 j
  have hs : 2 * (h : ℝ) * (θ - 1) = ((2 * k + 1 : ℤ) : ℝ) * θ ^ j := by
    rw [div_eq_iff (ne_of_gt hpow)] at heq
    push_cast
    linarith
  have hone : (1 : ℝ) ≤ |((2 * k + 1 : ℤ) : ℝ)| := by
    have h0 : (2 * k + 1 : ℤ) ≠ 0 := by omega
    have : (1 : ℤ) ≤ |2 * k + 1| := Int.one_le_abs h0
    exact_mod_cast this
  have habs : |2 * (h : ℝ) * (θ - 1)| = |((2 * k + 1 : ℤ) : ℝ)| * θ ^ j := by
    rw [hs, abs_mul, abs_of_pos hpow]
  have h1 : θ ^ j ≤ |((2 * k + 1 : ℤ) : ℝ)| * θ ^ j := by nlinarith
  have h2' : |2 * (h : ℝ) * (θ - 1)| = 2 * |(h : ℝ)| * (θ - 1) := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos (by linarith : (0 : ℝ) < θ - 1)]
  linarith [habs, h1, h2']

/-! ## Pisot decay at any degree -/

/-- **M5 Theorem 8's input, at any degree.**  For a Pisot `α`, `(α-1)αᵐ` approaches the rational
integers geometrically.  At degree two this is `QuadSetup.exists_int_close`, with the constant
`1 + |β|` and ratio `|β|`; here the constant is `(d-1)(1+ρ)` and the ratio `ρ = max_{j≥2}|α_j|`.
This is what makes "`(ξαⁿ)` is u.d." a tail event. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_int_close_of_isPisot {θ : ℝ} (hθ : IsPisot θ) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ m : ℕ, ∃ T : ℤ, |(θ - 1) * θ ^ m - (T : ℝ)| ≤ C * ρ ^ m :=
  hθ.exists_int_sub_one_mul_pow_close

/-! ## Degree two is an instance -/

namespace QuadSetup

variable (P : QuadSetup)

/-- `α` is an algebraic integer: it is a root of the monic `X² - aX - b`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isIntegral_alpha : IsIntegral ℤ P.α := by
  refine ⟨X ^ 2 - C P.a * X - C P.b, by monicity!, ?_⟩
  rw [← aeval_def]
  simp only [map_sub, map_mul, map_pow, aeval_X, eq_intCast, map_intCast]
  linarith [P.root]

/-- Every element of `ℤ[α]`, written in the degree-two basis by `IsIntComb`, is an algebraic
integer.  This is the bridge from `BB61/Multiplier.lean`'s arithmetic to the general one. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isIntegral_of_isIntComb {x : ℝ} (hx : P.IsIntComb x) : IsIntegral ℤ x := by
  obtain ⟨u, v, rfl⟩ := hx
  exact (isIntegral_intCast u).add ((isIntegral_intCast v).mul P.isIntegral_alpha)

/-- At a quadratic unit, `α⁻¹ = b(α - a)` is an algebraic integer. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isIntegral_inv_alpha (hb : P.b * P.b = 1) : IsIntegral ℤ P.α⁻¹ :=
  P.isIntegral_of_isIntComb (P.isIntComb_inv_alpha hb)

/-- **`BB61/Bernoulli.lean`'s `cos_past_ne_zero`, with both of its hypotheses removed.**  The
degree-two proof needs `2 < α` (through `pw_snd_ne_zero`) and `Irrational α`; the general proof
needs neither, and works at `h = 0` as well. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cos_past_ne_zero_of_isIntegral (h : ℤ) (m : ℕ) :
    Real.cos (Real.pi * ((h : ℝ) * ((P.β - 1) * P.β ^ m))) ≠ 0 := by
  have hrw : (h : ℝ) * ((P.β - 1) * P.β ^ m)
      = ((h * P.traceZ m : ℤ) : ℝ) + ((-h : ℤ) : ℝ) * ((P.α - 1) * P.α ^ m) := by
    push_cast
    linear_combination (h : ℝ) * P.trace_pw m
  rw [hrw]
  exact cos_ne_zero_of_isIntegral_ladder P.isIntegral_alpha _ (-h) m

end QuadSetup

/-! ## A cubic instance: the real root of `X³ - 2X² - 1` -/

/-- `X³ - 2X² - 1` has a real root above `2`: it is `-1` at `2` and `8` at `3`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_cubicRoot : ∃ x : ℝ, 2 < x ∧ x ^ 3 - 2 * x ^ 2 - 1 = 0 := by
  have hcont : ContinuousOn (fun x : ℝ => x ^ 3 - 2 * x ^ 2 - 1) (Set.Icc 2 3) := by fun_prop
  have hsub := intermediate_value_Icc (by norm_num : (2 : ℝ) ≤ 3) hcont
  have hmem : (0 : ℝ) ∈ Set.Icc ((2 : ℝ) ^ 3 - 2 * 2 ^ 2 - 1) ((3 : ℝ) ^ 3 - 2 * 3 ^ 2 - 1) := by
    norm_num
  obtain ⟨x, hx, hfx⟩ := hsub hmem
  refine ⟨x, ?_, hfx⟩
  rcases lt_or_eq_of_le hx.1 with h' | h'
  · exact h'
  · exfalso; rw [← h'] at hfx; norm_num at hfx

/-- **The cubic of `BB61/r3a_bern.log`**: `α ≈ 2.2056`, the real root of `X³ - 2X² - 1`, a Pisot
unit (the other two conjugates have modulus `≈ 0.673`). -/
noncomputable def alphaCubic : ℝ := exists_cubicRoot.choose

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem two_lt_alphaCubic : 2 < alphaCubic := exists_cubicRoot.choose_spec.1

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem alphaCubic_root : alphaCubic ^ 3 - 2 * alphaCubic ^ 2 - 1 = 0 :=
  exists_cubicRoot.choose_spec.2

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isIntegral_alphaCubic : IsIntegral ℤ alphaCubic := by
  refine ⟨X ^ 3 - C 2 * X ^ 2 - 1, by monicity!, ?_⟩
  rw [← aeval_def]
  simp only [map_sub, map_mul, map_pow, map_one, aeval_X, eq_intCast, map_intCast]
  push_cast
  linarith [alphaCubic_root]

/-- `α` is a unit: the constant term of its minimal polynomial is `-1`, and explicitly
`α · (α² - 2α) = 1`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem inv_alphaCubic : alphaCubic⁻¹ = alphaCubic ^ 2 - 2 * alphaCubic :=
  inv_eq_of_mul_eq_one_right (by linear_combination alphaCubic_root)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isIntegral_inv_alphaCubic : IsIntegral ℤ alphaCubic⁻¹ := by
  have h2 : IsIntegral ℤ ((2 : ℝ)) := by simpa using isIntegral_intCast (R := ℤ) (B := ℝ) 2
  rw [inv_alphaCubic]
  exact (isIntegral_alphaCubic.pow 2).sub (h2.mul isIntegral_alphaCubic)

/-- **Route E at the cubic, past half.**  No past factor vanishes, at any frequency `h` and any
`m` — degree three, and nothing degree-two about the proof. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cos_past_ne_zero_alphaCubic (N h : ℤ) (m : ℕ) :
    Real.cos (Real.pi * ((N : ℝ) + (h : ℝ) * ((alphaCubic - 1) * alphaCubic ^ m))) ≠ 0 :=
  cos_ne_zero_of_isIntegral_ladder isIntegral_alphaCubic N h m

/-- **Route E at the cubic, future half, with a multiplier.**  `α` is a unit, so the future
ladder is made of algebraic integers as well and no future factor vanishes either — at every
`h` and every `λ ∈ ℤ[α]`.  This is Corollary 6's arithmetic at degree three. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cos_future_ne_zero_alphaCubic {lam : ℝ} (hlam : IsIntegral ℤ lam) (h : ℤ) (j : ℕ) :
    Real.cos (Real.pi * ((h : ℝ) * lam * (alphaCubic - 1) / alphaCubic ^ j)) ≠ 0 :=
  cos_future_ne_zero_of_isIntegral_inv isIntegral_alphaCubic isIntegral_inv_alphaCubic hlam h j

/-- **Theorem 3 at the cubic, both halves, in `φ_p` form.**  For every `p ∈ [0,1]`, every
frequency `h` and every `λ ∈ ℤ[α]`, no factor of the Erdős product vanishes. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem phi_ne_zero_alphaCubic {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) {lam : ℝ}
    (hlam : IsIntegral ℤ lam) (N h : ℤ) (m j : ℕ) :
    phi p ((N : ℝ) + (h : ℝ) * ((alphaCubic - 1) * alphaCubic ^ m)) ≠ 0 ∧
      phi p ((h : ℝ) * lam * (alphaCubic - 1) / alphaCubic ^ j) ≠ 0 :=
  ⟨phi_ne_zero_of_isIntegral_ladder h0 h1 isIntegral_alphaCubic N h m,
    phi_future_ne_zero_of_isIntegral_inv h0 h1 isIntegral_alphaCubic isIntegral_inv_alphaCubic
      hlam h j⟩

end BB61
