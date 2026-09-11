/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import ForMathlib.Analysis.BoundedVariation.Monotone
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Group.Pointwise.Interval

/-!
# The total variation of the trigonometric characters on the unit interval

The `h`-th character `x ↦ e(hx)` traverses the unit circle `h` times as `x` runs over `[0,1]`,
so each of its two real parts has total variation exactly `4h`:

  `V(cos 2πhx) = V(sin 2πhx) = 4h` on `[0,1]`.

This is the constant in **Koksma's inequality** applied to a Weyl sum, and it is what turns a
lower bound on `|N⁻¹ ∑ e(h xₙ)|` into a lower bound on the star discrepancy of `(xₙ)`.

The proof is the obvious one.  `cos 2πhx` is monotone on each of the `2h` intervals
`[j/2h, (j+1)/2h]`, with oscillation `2` there; `sin 2πhx` is monotone on each of the `4h`
intervals `[j/4h, (j+1)/4h]`, with oscillation `1`.  `eVariationOn.sum'` adds the pieces up,
and each piece is computed by pulling it back to `[0,1]` along an increasing affine map
(`eVariationOn.comp_eq_of_monotoneOn`), where it becomes `±cos πt`, `±sin(πt/2)` or
`±cos(πt/2)` and `eVariationOn.eq_ofReal_abs_sub` applies.

## Main results

* `eVariationOn_cos_two_pi_mul`, `eVariationOn_sin_two_pi_mul` — the two variations, in `ℝ≥0∞`;
* `boundedVariationOn_cos_two_pi_mul`, `boundedVariationOn_sin_two_pi_mul`;
* `toReal_eVariationOn_cos_two_pi_mul`, `toReal_eVariationOn_sin_two_pi_mul` — the real form,
  which is what Koksma's inequality consumes.
-/

open Set Real

namespace eVariationOn

/-- Multiplying by a sign preserves being monotone-or-antitone. -/
theorem monotoneOn_or_antitoneOn_sign_mul {s : Set ℝ} {g : ℝ → ℝ} {c : ℝ} (hc : c = 1 ∨ c = -1)
    (hg : MonotoneOn g s ∨ AntitoneOn g s) :
    MonotoneOn (fun x => c * g x) s ∨ AntitoneOn (fun x => c * g x) s := by
  rcases hc with rfl | rfl
  · simpa using hg
  · rcases hg with hg | hg
    · exact Or.inr fun x hx y hy hxy => by
        have := hg hx hy hxy; simp only; linarith
    · exact Or.inl fun x hx y hy hxy => by
        have := hg hx hy hxy; simp only; linarith

/-- The variation of a signed monotone piece: `|c| = 1` scales nothing. -/
theorem sign_mul_eq_ofReal {c : ℝ} (hc : c = 1 ∨ c = -1) {g : ℝ → ℝ} {a b v : ℝ} (hab : a ≤ b)
    (hg : MonotoneOn g (Icc a b) ∨ AntitoneOn g (Icc a b)) (hv : |g b - g a| = v) :
    eVariationOn (fun t => c * g t) (Icc a b) = ENNReal.ofReal v := by
  rw [eq_ofReal_abs_sub hab (monotoneOn_or_antitoneOn_sign_mul hc hg), ← mul_sub, abs_mul, hv]
  have : |c| = 1 := by rcases hc with rfl | rfl <;> norm_num
  rw [this, one_mul]

end eVariationOn

/-! ## The three monotone shapes on `[0,1]` -/

theorem antitoneOn_cos_pi_mul : AntitoneOn (fun t : ℝ => Real.cos (π * t)) (Icc 0 1) := by
  intro x hx y hy hxy
  have hpi := Real.pi_pos
  exact Real.cos_le_cos_of_nonneg_of_le_pi (by nlinarith [hx.1]) (by nlinarith [hy.2])
    (by nlinarith)

theorem monotoneOn_sin_pi_mul_div_two :
    MonotoneOn (fun t : ℝ => Real.sin (π * t / 2)) (Icc 0 1) := by
  intro x hx y hy hxy
  have hpi := Real.pi_pos
  exact Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith [hx.1]) (by nlinarith [hy.2])
    (by nlinarith)

theorem antitoneOn_cos_pi_mul_div_two :
    AntitoneOn (fun t : ℝ => Real.cos (π * t / 2)) (Icc 0 1) := by
  intro x hx y hy hxy
  have hpi := Real.pi_pos
  exact Real.cos_le_cos_of_nonneg_of_le_pi (by nlinarith [hx.1]) (by nlinarith [hy.2])
    (by nlinarith)

/-! ## The pieces -/

/-- One half-period of `cos 2πhx` carries variation `2`. -/
theorem eVariationOn_cos_piece {h : ℕ} (hh : 0 < h) (j : ℕ) :
    eVariationOn (fun x : ℝ => Real.cos (2 * π * h * x))
      (Icc ((j : ℝ) / (2 * h)) (((j : ℝ) + 1) / (2 * h))) = 2 := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hne : (2 : ℝ) * h ≠ 0 := by positivity
  set c : ℝ := (2 * (h : ℝ))⁻¹ with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have himg : (fun t : ℝ => c * t + (j : ℝ) / (2 * h)) '' Icc (0 : ℝ) 1
      = Icc ((j : ℝ) / (2 * h)) (((j : ℝ) + 1) / (2 * h)) := by
    rw [Set.image_affine_Icc' hcpos]
    congr 1
    · ring
    · rw [hc]; field_simp; ring
  have hmono : MonotoneOn (fun t : ℝ => c * t + (j : ℝ) / (2 * h)) (Icc 0 1) :=
    fun x _ y _ hxy => by simp only; nlinarith
  rw [← himg, ← eVariationOn.comp_eq_of_monotoneOn _ _ hmono]
  have hfun : (fun x : ℝ => Real.cos (2 * π * h * x)) ∘ (fun t : ℝ => c * t + (j : ℝ) / (2 * h))
      = fun t : ℝ => (-1 : ℝ) ^ j * Real.cos (π * t) := by
    funext t
    simp only [Function.comp_apply]
    have harg : 2 * π * h * (c * t + (j : ℝ) / (2 * h)) = π * t + (j : ℝ) * π := by
      rw [hc]; field_simp
    rw [harg, Real.cos_add_nat_mul_pi]
  have hsign : (-1 : ℝ) ^ j = 1 ∨ (-1 : ℝ) ^ j = -1 := by
    rcases Nat.even_or_odd j with hj | hj
    · exact Or.inl hj.neg_one_pow
    · exact Or.inr hj.neg_one_pow
  have hval : |Real.cos (π * 1) - Real.cos (π * 0)| = 2 := by
    rw [mul_one, mul_zero, Real.cos_pi, Real.cos_zero]
    norm_num
  rw [hfun, eVariationOn.sign_mul_eq_ofReal hsign zero_le_one (Or.inr antitoneOn_cos_pi_mul) hval]
  norm_num

/-- One quarter-period of `sin 2πhx` carries variation `1`. -/
theorem eVariationOn_sin_piece {h : ℕ} (hh : 0 < h) (j : ℕ) :
    eVariationOn (fun x : ℝ => Real.sin (2 * π * h * x))
      (Icc ((j : ℝ) / (4 * h)) (((j : ℝ) + 1) / (4 * h))) = 1 := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  set c : ℝ := (4 * (h : ℝ))⁻¹ with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have himg : (fun t : ℝ => c * t + (j : ℝ) / (4 * h)) '' Icc (0 : ℝ) 1
      = Icc ((j : ℝ) / (4 * h)) (((j : ℝ) + 1) / (4 * h)) := by
    rw [Set.image_affine_Icc' hcpos]
    congr 1
    · ring
    · rw [hc]; field_simp; ring
  have hmono : MonotoneOn (fun t : ℝ => c * t + (j : ℝ) / (4 * h)) (Icc 0 1) :=
    fun x _ y _ hxy => by simp only; nlinarith
  rw [← himg, ← eVariationOn.comp_eq_of_monotoneOn _ _ hmono]
  rcases Nat.even_or_odd j with ⟨q, hq⟩ | ⟨q, hq⟩
  · -- `j = q + q`: the piece is `±sin(πt/2)`, rising from `0` to `1`
    have hfun : (fun x : ℝ => Real.sin (2 * π * h * x)) ∘ (fun t : ℝ => c * t + (j : ℝ) / (4 * h))
        = fun t : ℝ => (-1 : ℝ) ^ q * Real.sin (π * t / 2) := by
      funext t
      simp only [Function.comp_apply]
      have hjq : (j : ℝ) = 2 * q := by rw [hq]; push_cast; ring
      have harg : 2 * π * h * (c * t + (j : ℝ) / (4 * h)) = π * t / 2 + (q : ℝ) * π := by
        rw [hc, hjq]; field_simp; ring
      rw [harg, Real.sin_add_nat_mul_pi]
    have hsign : (-1 : ℝ) ^ q = 1 ∨ (-1 : ℝ) ^ q = -1 := by
      rcases Nat.even_or_odd q with hqq | hqq
      · exact Or.inl hqq.neg_one_pow
      · exact Or.inr hqq.neg_one_pow
    have hval : |Real.sin (π * 1 / 2) - Real.sin (π * 0 / 2)| = 1 := by
      rw [mul_one, mul_zero, zero_div, Real.sin_zero, Real.sin_pi_div_two]
      norm_num
    rw [hfun, eVariationOn.sign_mul_eq_ofReal hsign zero_le_one
      (Or.inl monotoneOn_sin_pi_mul_div_two) hval]
    norm_num
  · -- `j = 2q + 1`: the piece is `±cos(πt/2)`, falling from `1` to `0`
    have hfun : (fun x : ℝ => Real.sin (2 * π * h * x)) ∘ (fun t : ℝ => c * t + (j : ℝ) / (4 * h))
        = fun t : ℝ => (-1 : ℝ) ^ q * Real.cos (π * t / 2) := by
      funext t
      simp only [Function.comp_apply]
      have hjq : (j : ℝ) = 2 * q + 1 := by rw [hq]; push_cast; ring
      have harg : 2 * π * h * (c * t + (j : ℝ) / (4 * h))
          = (π * t / 2 + π / 2) + (q : ℝ) * π := by
        rw [hc, hjq]; field_simp; ring
      rw [harg, Real.sin_add_nat_mul_pi, Real.sin_add_pi_div_two]
    have hsign : (-1 : ℝ) ^ q = 1 ∨ (-1 : ℝ) ^ q = -1 := by
      rcases Nat.even_or_odd q with hqq | hqq
      · exact Or.inl hqq.neg_one_pow
      · exact Or.inr hqq.neg_one_pow
    have hval : |Real.cos (π * 1 / 2) - Real.cos (π * 0 / 2)| = 1 := by
      rw [mul_one, mul_zero, zero_div, Real.cos_zero, Real.cos_pi_div_two]
      norm_num
    rw [hfun, eVariationOn.sign_mul_eq_ofReal hsign zero_le_one
      (Or.inr antitoneOn_cos_pi_mul_div_two) hval]
    norm_num

/-! ## The two variations -/

private theorem monotone_grid {d : ℕ} (hd : 0 < d) :
    Monotone (fun j : ℕ => (j : ℝ) / (d : ℝ)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  intro i j hij
  have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  simp only [div_eq_mul_inv]
  have : (0 : ℝ) ≤ (d : ℝ)⁻¹ := by positivity
  nlinarith

/-- **`V(cos 2πhx) = 4h` on `[0,1]`.** -/
theorem eVariationOn_cos_two_pi_mul {h : ℕ} (hh : 0 < h) :
    eVariationOn (fun x : ℝ => Real.cos (2 * π * h * x)) (Icc (0 : ℝ) 1) = 4 * h := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hgrid : Monotone (fun j : ℕ => (j : ℝ) / ((2 * h : ℕ) : ℝ)) :=
    monotone_grid (by omega)
  have hsum := eVariationOn.sum' (fun x : ℝ => Real.cos (2 * π * h * x)) hgrid (n := 2 * h)
  have hzero : ((0 : ℕ) : ℝ) / ((2 * h : ℕ) : ℝ) = 0 := by simp
  have hone : ((2 * h : ℕ) : ℝ) / ((2 * h : ℕ) : ℝ) = 1 := by
    have : ((2 * h : ℕ) : ℝ) ≠ 0 := by push_cast; positivity
    field_simp
  rw [hzero, hone] at hsum
  have hpieces : ∀ j ∈ Finset.range (2 * h),
      eVariationOn (fun x : ℝ => Real.cos (2 * π * h * x))
        (Icc ((j : ℝ) / ((2 * h : ℕ) : ℝ)) (((j + 1 : ℕ) : ℝ) / ((2 * h : ℕ) : ℝ))) = 2 := by
    intro j _
    have e1 : ((2 * h : ℕ) : ℝ) = 2 * (h : ℝ) := by push_cast; ring
    have e2 : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
    rw [e1, e2]
    exact eVariationOn_cos_piece hh j
  rw [Finset.sum_congr rfl hpieces, Finset.sum_const, Finset.card_range] at hsum
  rw [← hsum, nsmul_eq_mul]
  push_cast
  ring

/-- **`V(sin 2πhx) = 4h` on `[0,1]`.** -/
theorem eVariationOn_sin_two_pi_mul {h : ℕ} (hh : 0 < h) :
    eVariationOn (fun x : ℝ => Real.sin (2 * π * h * x)) (Icc (0 : ℝ) 1) = 4 * h := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hgrid : Monotone (fun j : ℕ => (j : ℝ) / ((4 * h : ℕ) : ℝ)) :=
    monotone_grid (by omega)
  have hsum := eVariationOn.sum' (fun x : ℝ => Real.sin (2 * π * h * x)) hgrid (n := 4 * h)
  have hzero : ((0 : ℕ) : ℝ) / ((4 * h : ℕ) : ℝ) = 0 := by simp
  have hone : ((4 * h : ℕ) : ℝ) / ((4 * h : ℕ) : ℝ) = 1 := by
    have : ((4 * h : ℕ) : ℝ) ≠ 0 := by push_cast; positivity
    field_simp
  rw [hzero, hone] at hsum
  have hpieces : ∀ j ∈ Finset.range (4 * h),
      eVariationOn (fun x : ℝ => Real.sin (2 * π * h * x))
        (Icc ((j : ℝ) / ((4 * h : ℕ) : ℝ)) (((j + 1 : ℕ) : ℝ) / ((4 * h : ℕ) : ℝ))) = 1 := by
    intro j _
    have e1 : ((4 * h : ℕ) : ℝ) = 4 * (h : ℝ) := by push_cast; ring
    have e2 : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
    rw [e1, e2]
    exact eVariationOn_sin_piece hh j
  rw [Finset.sum_congr rfl hpieces, Finset.sum_const, Finset.card_range] at hsum
  rw [← hsum, nsmul_eq_mul]
  push_cast
  ring

theorem boundedVariationOn_cos_two_pi_mul {h : ℕ} (hh : 0 < h) :
    BoundedVariationOn (fun x : ℝ => Real.cos (2 * π * h * x)) (Icc (0 : ℝ) 1) := by
  rw [BoundedVariationOn, eVariationOn_cos_two_pi_mul hh]
  exact ENNReal.mul_ne_top (by simp) (by simp)

theorem boundedVariationOn_sin_two_pi_mul {h : ℕ} (hh : 0 < h) :
    BoundedVariationOn (fun x : ℝ => Real.sin (2 * π * h * x)) (Icc (0 : ℝ) 1) := by
  rw [BoundedVariationOn, eVariationOn_sin_two_pi_mul hh]
  exact ENNReal.mul_ne_top (by simp) (by simp)

theorem toReal_eVariationOn_cos_two_pi_mul {h : ℕ} (hh : 0 < h) :
    (eVariationOn (fun x : ℝ => Real.cos (2 * π * h * x)) (Icc (0 : ℝ) 1)).toReal = 4 * h := by
  rw [eVariationOn_cos_two_pi_mul hh]
  simp

theorem toReal_eVariationOn_sin_two_pi_mul {h : ℕ} (hh : 0 < h) :
    (eVariationOn (fun x : ℝ => Real.sin (2 * π * h * x)) (Icc (0 : ℝ) 1)).toReal = 4 * h := by
  rw [eVariationOn_sin_two_pi_mul hh]
  simp
