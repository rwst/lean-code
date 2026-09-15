/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.NumberTheory.Real.Irrational
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Bugeaud Problem 10.61, Route E: why the Erdős product does not vanish

Formal companion of `note-1061-M5.html` (milestone M5 of `plans/plan-1061.html`),
quadratic case.  Route E computes the Weyl limit of `(ξ αⁿ)` for a digit word generic
for the Bernoulli(`p`) measure as a doubly infinite product

  `G_p(h) = ∏_{j≥1} φ_p(h(α-1)α^{-j}) · ∏_{m≥0} φ_p(-h c_m)`,  `c_m = (β-1)βᵐ`,

with `φ_p(x) = (1-p) + p e(x)`; at `p = 1/2` each factor has modulus `|cos(π x)|`.  The
whole of Route E rests on the fact that **no factor vanishes**, and that fact is pure
arithmetic.  This file formalises it at degree two:

* `pw_alpha` / `pw_beta` — the integer pair `(α-1)αᵐ = uₘ + vₘ α` and its conjugate;
* `trace_pw`, `abs_sub_trace`, `exists_int_close` — `(α-1)αᵐ` is within `|β-1||β|ᵐ` of an
  integer.  This is the Pisot decay that makes "`(ξαⁿ)` is u.d." a *tail* event (M5
  Thm 8), and it is what turns the past factors into the non-negative half of the
  doubly infinite product;
* `cos_future_ne_zero` — **`α > 2` is used exactly once in Route E**: `(α-1)/α > 1/2`
  and `(α-1)/α^j < 1/2` for `j ≥ 2`, so no future factor is `cos(π/2)`.  At `α = 2` the
  first factor *is* zero, which is correct: `C(2) = [0,1]` and the coding measure is
  Lebesgue;
* `pw_snd_ne_zero`, `cos_past_ne_zero` — no past factor vanishes either, because
  `h(α-1)αᵐ` is an algebraic integer and `1/2 + ℤ` contains none;
* `past_eq_future` — at a quadratic unit of norm `+1` (`b = -1`) the past ladder *is*
  the future ladder shifted by one, so `G_p(h)` is a perfect square (M5 Thm 7);
* the instance `twoAddSqrt3` and its four corollaries.

What is **not** formalised here: convergence of the two infinite products (classical,
`∑ |c_m| < ∞`), the identification of `G_p(h)` with the Weyl limit (M5 Thm 1+2, an
ergodic-theorem argument), and the `p ≠ 1/2` case (where every factor is trivially
nonzero, `|φ_p| ≥ |1-2p|`).  See `note-1061-M5.html` §9.
-/

namespace BB61

namespace QuadSetup

variable (P : QuadSetup)

/-! ## The integer pair of `(α-1)αᵐ` -/

/-- `(α-1)αᵐ = uₘ + vₘ α` in `ℤ[α]`, by the pair recursion `(u,v) ↦ (b v, u + a v)`
started at `(-1, 1)`.  The same pair evaluates the conjugate `(β-1)βᵐ`. -/
def pw : ℕ → ℤ × ℤ
  | 0 => (-1, 1)
  | m + 1 => (P.b * (pw m).2, (pw m).1 + P.a * (pw m).2)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem pw_zero : P.pw 0 = (-1, 1) := rfl

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem pw_succ (m : ℕ) :
    P.pw (m + 1) = (P.b * (P.pw m).2, (P.pw m).1 + P.a * (P.pw m).2) := rfl

/-- The pair evaluates `(x-1)xᵐ` at **either** root of `X² - aX - b`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem pw_eval (m : ℕ) {x : ℝ} (hx : x ^ 2 = (P.a : ℝ) * x + P.b) :
    (x - 1) * x ^ m = ((P.pw m).1 : ℝ) + ((P.pw m).2 : ℝ) * x := by
  induction m with
  | zero => rw [pw_zero]; push_cast; ring
  | succ m ih =>
      have hstep : (x - 1) * x ^ (m + 1) = ((x - 1) * x ^ m) * x := by ring
      rw [hstep, ih, pw_succ]
      push_cast
      linear_combination ((P.pw m).2 : ℝ) * hx

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem pw_alpha (m : ℕ) :
    (P.α - 1) * P.α ^ m = ((P.pw m).1 : ℝ) + ((P.pw m).2 : ℝ) * P.α :=
  P.pw_eval m P.root

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem pw_beta (m : ℕ) :
    (P.β - 1) * P.β ^ m = ((P.pw m).1 : ℝ) + ((P.pw m).2 : ℝ) * P.β :=
  P.pw_eval m P.beta_root

/-! ## Pisot decay -/

/-- The trace `Tₘ = (α-1)αᵐ + (β-1)βᵐ = 2uₘ + a vₘ`, a rational integer. -/
def traceZ (m : ℕ) : ℤ := 2 * (P.pw m).1 + P.a * (P.pw m).2

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem trace_pw (m : ℕ) :
    (P.α - 1) * P.α ^ m + (P.β - 1) * P.β ^ m = (P.traceZ m : ℝ) := by
  rw [pw_alpha, pw_beta, traceZ]
  push_cast
  linear_combination ((P.pw m).2 : ℝ) * P.alpha_add_beta

/-- The Pisot decay, with the exact constant: `(α-1)αᵐ` sits at distance
`|β-1| · |β|ᵐ` from the integer `Tₘ`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_sub_trace (m : ℕ) :
    |(P.α - 1) * P.α ^ m - (P.traceZ m : ℝ)| = |P.β - 1| * |P.β| ^ m := by
  have h : (P.α - 1) * P.α ^ m - (P.traceZ m : ℝ) = -((P.β - 1) * P.β ^ m) := by
    have := P.trace_pw m; linarith
  rw [h, abs_neg, abs_mul, abs_pow]

/-- Changing one digit of `ξ` moves `ξ αⁿ` by an amount whose distance to `ℤ` is
`O(|β|ⁿ)`: the perturbation lemma behind the tail-event structure of M5 Thm 8. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_int_close (m : ℕ) :
    ∃ N : ℤ, |(P.α - 1) * P.α ^ m - (N : ℝ)| ≤ (1 + |P.β|) * |P.β| ^ m := by
  refine ⟨P.traceZ m, ?_⟩
  rw [abs_sub_trace]
  have h1 : |P.β - 1| ≤ 1 + |P.β| := by
    calc |P.β - 1| ≤ |P.β| + |(1 : ℝ)| := abs_sub _ _
      _ = 1 + |P.β| := by rw [abs_one]; ring
  have h2 : (0 : ℝ) ≤ |P.β| ^ m := pow_nonneg (abs_nonneg _) m
  exact mul_le_mul_of_nonneg_right h1 h2

/-! ## No factor of the Erdős product vanishes -/

/-- `cos (π y) ≠ 0` for `y ∈ (0,1)`, `y ≠ 1/2`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cos_pi_ne_zero_of_mem {y : ℝ} (h0 : 0 < y) (h1 : y < 1) (hh : y ≠ 1 / 2) :
    Real.cos (Real.pi * y) ≠ 0 := by
  rw [Ne, Real.cos_eq_zero_iff]
  rintro ⟨k, hk⟩
  have hpi := Real.pi_pos
  have hy : y = (k : ℝ) + 1 / 2 := by
    have h : Real.pi * y = Real.pi * ((k : ℝ) + 1 / 2) := by rw [hk]; ring
    exact mul_left_cancel₀ (ne_of_gt hpi) h
  have hlo : (-1 : ℝ) < 2 * (k : ℝ) := by rw [hy] at h0; linarith
  have hhi : (2 : ℝ) * (k : ℝ) < 1 := by rw [hy] at h1; linarith
  have hlo' : (-1 : ℤ) < 2 * k := by exact_mod_cast hlo
  have hhi' : (2 : ℤ) * k < 1 := by exact_mod_cast hhi
  have hk0 : k = 0 := by omega
  apply hh
  rw [hy, hk0]
  norm_num

/-- **Where `α > 2` is spent.** Every future factor `(α-1)/α^j`, `j ≥ 1`, lies in
`(0,1) \ {1/2}`: the first one is `> 1/2` precisely because `α > 2`, and all the others
are `< 1/2` for free. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cos_future_ne_zero (h2 : 2 < P.α) {j : ℕ} (hj : 1 ≤ j) :
    Real.cos (Real.pi * ((P.α - 1) / P.α ^ j)) ≠ 0 := by
  have hα0 : (0 : ℝ) < P.α := P.alpha_pos
  have hpow : (0 : ℝ) < P.α ^ j := pow_pos hα0 j
  have hle : P.α ≤ P.α ^ j := by
    calc P.α = P.α ^ 1 := (pow_one _).symm
      _ ≤ P.α ^ j := pow_le_pow_right₀ (le_of_lt P.one_lt) hj
  refine cos_pi_ne_zero_of_mem (div_pos (by linarith) hpow) ?_ ?_
  · rw [div_lt_one hpow]; linarith
  · rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · -- j = 1 : (α-1)/α > 1/2 ⟺ α > 2
      have hj1 : j = 1 := by omega
      subst hj1
      rw [pow_one]
      intro hcon
      rw [div_eq_iff (ne_of_gt hα0)] at hcon
      linarith
    · -- j ≥ 2 : (α-1)/α^j ≤ (α-1)/α² < 1/2
      have hpow2 : P.α ^ 2 ≤ P.α ^ j := pow_le_pow_right₀ (le_of_lt P.one_lt) hj2
      have hα2 : (0 : ℝ) < P.α ^ 2 := pow_pos hα0 2
      have hlt : (P.α - 1) / P.α ^ j ≤ (P.α - 1) / P.α ^ 2 :=
        div_le_div_of_nonneg_left (by linarith) hα2 hpow2
      have hhalf : (P.α - 1) / P.α ^ 2 < 1 / 2 := by
        rw [div_lt_iff₀ hα2]
        nlinarith
      intro hcon
      rw [hcon] at hlt
      linarith

/-- `vₘ ≠ 0`: `(α-1)αᵐ` is irrational whenever `α` is. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem pw_snd_ne_zero (h2 : 2 < P.α) (m : ℕ) : (P.pw m).2 ≠ 0 := by
  intro h0
  have ha := P.pw_alpha m
  have hb := P.pw_beta m
  rw [h0] at ha hb
  push_cast at ha hb
  rw [zero_mul, add_zero] at ha hb
  have hβ : |P.β| < 1 := P.abs_beta_lt_one
  have heq : (P.α - 1) * P.α ^ m = (P.β - 1) * P.β ^ m := by rw [ha, hb]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [pow_zero, mul_one] at heq
    have := (abs_lt.mp hβ).2
    linarith
  · have hb2 : |(P.β - 1) * P.β ^ m| ≤ 2 := by
      rw [abs_mul, abs_pow]
      have h1 : |P.β - 1| ≤ 2 := by
        have h := abs_lt.mp hβ
        rw [abs_le]; constructor <;> linarith [h.1, h.2]
      have h3 : |P.β| ^ m ≤ 1 := pow_le_one₀ (abs_nonneg _) (le_of_lt hβ)
      nlinarith [abs_nonneg (P.β - 1), pow_nonneg (abs_nonneg P.β) m]
    have ha2 : (2 : ℝ) < (P.α - 1) * P.α ^ m := by
      have hαm : (2 : ℝ) < P.α ^ m := by
        calc (2 : ℝ) < P.α := h2
          _ = P.α ^ 1 := (pow_one _).symm
          _ ≤ P.α ^ m := pow_le_pow_right₀ (le_of_lt P.one_lt) hm
      nlinarith
    rw [heq] at ha2
    linarith [le_abs_self ((P.β - 1) * P.β ^ m)]

/-- No past factor vanishes: `h(α-1)αᵐ` is an algebraic integer, and `1/2 + ℤ`
contains none.  (Stated through the trace identity, on `c_m = (β-1)βᵐ`.) -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cos_past_ne_zero (h2 : 2 < P.α) (hirr : Irrational P.α) {k : ℤ} (hk : k ≠ 0)
    (m : ℕ) : Real.cos (Real.pi * ((k : ℝ) * ((P.β - 1) * P.β ^ m))) ≠ 0 := by
  rw [Ne, Real.cos_eq_zero_iff]
  rintro ⟨n, hn⟩
  have hpi := Real.pi_pos
  have hval : (2 : ℝ) * ((k : ℝ) * ((P.β - 1) * P.β ^ m)) = 2 * (n : ℝ) + 1 := by
    have h : Real.pi * ((k : ℝ) * ((P.β - 1) * P.β ^ m))
        = Real.pi * (((2 * (n : ℝ) + 1)) / 2) := by rw [hn]; ring
    have := mul_left_cancel₀ (ne_of_gt hpi) h
    rw [this]; ring
  -- (β-1)βᵐ = Tₘ - (uₘ + vₘ α)
  have hc : (P.β - 1) * P.β ^ m = (P.traceZ m : ℝ) - (((P.pw m).1 : ℝ)
      + ((P.pw m).2 : ℝ) * P.α) := by
    have h1 := P.trace_pw m
    have h2 := P.pw_alpha m
    linarith
  rw [hc] at hval
  set v : ℤ := (P.pw m).2 with hv
  have hvne : v ≠ 0 := P.pw_snd_ne_zero h2 m
  have hkv : (2 * k * v : ℤ) ≠ 0 := by
    simp only [mul_ne_zero_iff]
    exact ⟨⟨two_ne_zero, hk⟩, hvne⟩
  have hirr' : Irrational (((2 * k * v : ℤ) : ℝ) * P.α) := hirr.intCast_mul hkv
  have heq : ((2 * k * v : ℤ) : ℝ) * P.α
      = ((2 * k * P.traceZ m - 2 * k * (P.pw m).1 - (2 * n + 1) : ℤ) : ℝ) := by
    push_cast
    linarith
  exact hirr'.ne_int _ heq

/-! ## Folding at a quadratic unit of norm `+1` -/

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem beta_eq_inv (hb : P.b = -1) : P.β = P.α⁻¹ := by
  have hα0 : (0 : ℝ) < P.α := P.alpha_pos
  have hprod : P.α * P.β = 1 := by
    have h := P.root
    rw [hb] at h
    unfold QuadSetup.β
    push_cast at h ⊢
    nlinarith [h]
  field_simp
  linarith [hprod]

/-- **M5 Thm 7.** At a quadratic unit of norm `+1` the past ladder is the future ladder
shifted by one: `c_m = -(α-1)/α^{m+1}`.  Hence the window `K` is `-C(α)` and the Weyl
limit `G_p(h)` is a perfect square. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem past_eq_future (hb : P.b = -1) (m : ℕ) :
    (P.β - 1) * P.β ^ m = -((P.α - 1) / P.α ^ (m + 1)) := by
  have hα0 : (0 : ℝ) < P.α := P.alpha_pos
  rw [P.beta_eq_inv hb, inv_pow]
  field_simp
  ring

end QuadSetup

/-! ## The instance `α = 2 + √3` -/

open QuadSetup

theorem sqrt3_lt : Real.sqrt 3 < 1.7320509 :=
  (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)

theorem lt_sqrt3 : (1.7320508 : ℝ) < Real.sqrt 3 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)

/-- `α = 2 + √3`, the root of `X² - 4X + 1`: trace `4`, norm `+1`, conjugate `2 - √3`.
The smallest `α` of the M4 sweep where Route A is blind. -/
noncomputable def twoAddSqrt3 : QuadSetup where
  a := 4
  b := -1
  α := 2 + Real.sqrt 3
  root := by
    have h : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    push_cast
    nlinarith [h]
  one_lt := by have := Real.sqrt_nonneg 3; linarith
  conj_lt := by
    have h1 := lt_sqrt3
    have h2 := sqrt3_lt
    rw [abs_lt]
    push_cast
    constructor <;> linarith

theorem twoAddSqrt3_alpha : twoAddSqrt3.α = 2 + Real.sqrt 3 := rfl

theorem twoAddSqrt3_beta : twoAddSqrt3.β = 2 - Real.sqrt 3 := by
  show ((4 : ℤ) : ℝ) - (2 + Real.sqrt 3) = 2 - Real.sqrt 3
  push_cast
  ring

theorem two_lt_twoAddSqrt3 : (2 : ℝ) < twoAddSqrt3.α := by
  have := lt_sqrt3
  show (2 : ℝ) < 2 + Real.sqrt 3
  linarith

theorem irrational_twoAddSqrt3 : Irrational twoAddSqrt3.α := by
  show Irrational (2 + Real.sqrt 3)
  have h : Irrational (Real.sqrt 3) := by
    simpa using (Nat.prime_three).irrational_sqrt
  simpa using h.intCast_add 2

/-- **Route E at `2 + √3`, future half.** No factor `cos(π(1+√3)/(2+√3)^j)` vanishes. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cos_future_ne_zero_twoAddSqrt3 {j : ℕ} (hj : 1 ≤ j) :
    Real.cos (Real.pi * ((1 + Real.sqrt 3) / (2 + Real.sqrt 3) ^ j)) ≠ 0 := by
  have := twoAddSqrt3.cos_future_ne_zero two_lt_twoAddSqrt3 hj
  simpa [twoAddSqrt3_alpha, show (2 : ℝ) + Real.sqrt 3 - 1 = 1 + Real.sqrt 3 by ring]
    using this

/-- **Route E at `2 + √3`, past half.** No factor `cos(π h (1-√3)(2-√3)ᵐ)` vanishes,
for any `h ≠ 0`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cos_past_ne_zero_twoAddSqrt3 {k : ℤ} (hk : k ≠ 0) (m : ℕ) :
    Real.cos (Real.pi * ((k : ℝ) * ((1 - Real.sqrt 3) * (2 - Real.sqrt 3) ^ m))) ≠ 0 := by
  have := twoAddSqrt3.cos_past_ne_zero two_lt_twoAddSqrt3 irrational_twoAddSqrt3 hk m
  simpa [twoAddSqrt3_beta, show (2 : ℝ) - Real.sqrt 3 - 1 = 1 - Real.sqrt 3 by ring]
    using this

/-- **Pisot decay at `2 + √3`**: `(1+√3)(2+√3)ᵐ` is within `(√3-1)(2-√3)ᵐ` of an
integer — the perturbation bound behind M5 Thm 8. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem pisot_decay_twoAddSqrt3 (m : ℕ) :
    ∃ N : ℤ, |(1 + Real.sqrt 3) * (2 + Real.sqrt 3) ^ m - (N : ℝ)|
      = (Real.sqrt 3 - 1) * (2 - Real.sqrt 3) ^ m := by
  refine ⟨twoAddSqrt3.traceZ m, ?_⟩
  have h := twoAddSqrt3.abs_sub_trace m
  rw [twoAddSqrt3_alpha, twoAddSqrt3_beta] at h
  have h1 : |(2 : ℝ) - Real.sqrt 3 - 1| = Real.sqrt 3 - 1 := by
    rw [abs_of_nonpos (by nlinarith [lt_sqrt3])]; ring
  have h2 : |(2 : ℝ) - Real.sqrt 3| = 2 - Real.sqrt 3 := by
    rw [abs_of_nonneg (by nlinarith [sqrt3_lt])]
  rw [h1, h2] at h
  rw [show (1 : ℝ) + Real.sqrt 3 = 2 + Real.sqrt 3 - 1 by ring]
  exact h

end BB61
