/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.LimitLaw
import CITED.KoksmaInequality
import ForMathlib.Analysis.BoundedVariation.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# M5 Corollary 4: the discrepancy floor

Formal companion of `note-1061-M5.html` (milestone M5 of `plans/plan-1061.html`) §5, the
half of Corollary 4 that `BB61/LimitLaw.lean` left open:

> **Corollary 4 (discrepancy form).**  At a Bernoulli(`p`)-generic digit word `ε`, the orbit
> `(ξ αⁿ)` of `ξ = π(ε)` has
> `liminf_N D*_N ≥ max_{h ≥ 1} |G_p(h)| / (4√2 h) `.

`BB61/LimitLaw.lean` supplies the Weyl sums (`tendsto_weylSum_bern`: the `h`-th Weyl average
converges to `G_p(h)`); `CITED/KoksmaInequality.lean` supplies [KN74] Ch. 2 Thm 5.1 in its
1-periodic form; and `ForMathlib/Analysis/BoundedVariation/Trigonometric.lean` supplies the
constant, `V(cos 2πhx) = V(sin 2πhx) = 4h` on `[0,1]`.  This file is the assembly.

## The three steps

1. **The characters are Koksma integrands.**  `periodic_cos_char`, `integral_cos_char` (and
   their `sin` twins): `x ↦ cos 2πhx` is 1-periodic with mean zero for `h ≥ 1`, so Koksma
   reads `|N⁻¹ ∑ cos 2πh xₙ| ≤ 4h · D*_N` — `abs_average_cos_le`, `abs_average_sin_le`.
2. **Real and imaginary parts recombine.**  `‖z‖ ≤ √2 max(|Re z|, |Im z|)`, whence
   `norm_average_char_le`: `‖N⁻¹ ∑ e(h xₙ)‖ ≤ 4√2 h · D*_N`, for *any* real sequence.  This
   is the note's `|S_N| ≤ 4√2 h D*_N`, and it is where the `√2` is spent.
3. **The limit is the floor.**  `|S_N| → |G_p(h)|` cannot happen if `D*_N` dips below
   `|G_p(h)|/(4√2 h)` infinitely often — `eventually_le_starDiscrepancy` and its liminf form
   `le_liminf_starDiscrepancy`.

Nothing here needs `G_p(h) ≠ 0`: the floor is stated for every `h ≥ 1` and is vacuous at the
frequencies where the Erdős product vanishes.  Positivity at `p = 1/2, h = 1` is
`BB61/ProductFormula.lean`'s `weylC_half_one_ne_zero`, and gives the file's headline
`starDiscrepancy_floor_pos`.

## Axiom status

Every declaration below is std3 **except** through `Koksma.abs_average_sub_integral_le`, the
single cited axiom of `CITED/KoksmaInequality.lean` ([KN74] Ch. 2, Thm 5.1).  That is the only
non-`sorry`-free input; in particular the total variation `4h` is *proved*, not assumed.

## References
* [KN74] Kuipers, L. and Niederreiter, H. *Uniform Distribution of Sequences.* Wiley, 1974.
* [Bug12] Bugeaud, Y. *Distribution Modulo One and Diophantine Approximation.* CUP, 2012,
  Problem 10.61.
-/

namespace BB61

open Filter Topology Koksma

/-! ## Step 1: the characters as Koksma integrands -/

/-- `x ↦ cos 2πhx` has period `1`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem periodic_cos_char (h : ℕ) :
    Function.Periodic (fun x : ℝ => Real.cos (2 * Real.pi * h * x)) 1 := by
  intro x
  have e : 2 * Real.pi * (h : ℝ) * (x + 1) = 2 * Real.pi * h * x + (h : ℝ) * (2 * Real.pi) := by
    ring
  simp only [e, Real.cos_add_nat_mul_two_pi]

/-- `x ↦ sin 2πhx` has period `1`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem periodic_sin_char (h : ℕ) :
    Function.Periodic (fun x : ℝ => Real.sin (2 * Real.pi * h * x)) 1 := by
  intro x
  have e : 2 * Real.pi * (h : ℝ) * (x + 1) = 2 * Real.pi * h * x + (h : ℝ) * (2 * Real.pi) := by
    ring
  simp only [e, Real.sin_add_nat_mul_two_pi]

/-- A non-trivial character has mean zero over a period. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem integral_cos_char {h : ℕ} (hh : 0 < h) :
    ∫ t in (0:ℝ)..1, Real.cos (2 * Real.pi * h * t) = 0 := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hc : (2 * Real.pi * (h : ℝ)) ≠ 0 := by positivity
  have hsin : Real.sin (2 * Real.pi * (h : ℝ) * 1) = 0 := by
    rw [show 2 * Real.pi * (h : ℝ) * 1 = ((2 * h : ℕ) : ℝ) * Real.pi by push_cast; ring]
    exact Real.sin_nat_mul_pi _
  rw [intervalIntegral.integral_comp_mul_left (f := Real.cos) (a := (0:ℝ)) (b := 1)
      (c := 2 * Real.pi * (h : ℝ)) hc, integral_cos, mul_zero, Real.sin_zero, hsin]
  simp

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem integral_sin_char {h : ℕ} (hh : 0 < h) :
    ∫ t in (0:ℝ)..1, Real.sin (2 * Real.pi * h * t) = 0 := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hc : (2 * Real.pi * (h : ℝ)) ≠ 0 := by positivity
  have hcos : Real.cos (2 * Real.pi * (h : ℝ) * 1) = 1 := by
    rw [show 2 * Real.pi * (h : ℝ) * 1 = (h : ℝ) * (2 * Real.pi) by ring]
    exact Real.cos_nat_mul_two_pi _
  rw [intervalIntegral.integral_comp_mul_left (f := Real.sin) (a := (0:ℝ)) (b := 1)
      (c := 2 * Real.pi * (h : ℝ)) hc, integral_sin, mul_zero, Real.cos_zero, hcos]
  simp

/-- **Koksma against `cos 2πhx`**: the cosine averages of any real sequence are bounded by
`4h` times its star discrepancy.  [KN74] Ch. 2 Thm 5.1 with `V(cos 2πhx) = 4h`. -/
@[category research solved, AMS 11, ref "KN74", group "bugeaud_10_61"]
theorem abs_average_cos_le {h : ℕ} (hh : 0 < h) (x : ℕ → ℝ) (N : ℕ) :
    |(∑ n ∈ Finset.range N, Real.cos (2 * Real.pi * h * x n)) / N|
      ≤ 4 * h * starDiscrepancy x N := by
  have key := Koksma.abs_average_sub_integral_le_of_periodic
    (boundedVariationOn_cos_two_pi_mul hh) (periodic_cos_char h) x N
  rwa [integral_cos_char hh, sub_zero, toReal_eVariationOn_cos_two_pi_mul hh] at key

/-- **Koksma against `sin 2πhx`.** -/
@[category research solved, AMS 11, ref "KN74", group "bugeaud_10_61"]
theorem abs_average_sin_le {h : ℕ} (hh : 0 < h) (x : ℕ → ℝ) (N : ℕ) :
    |(∑ n ∈ Finset.range N, Real.sin (2 * Real.pi * h * x n)) / N|
      ≤ 4 * h * starDiscrepancy x N := by
  have key := Koksma.abs_average_sub_integral_le_of_periodic
    (boundedVariationOn_sin_two_pi_mul hh) (periodic_sin_char h) x N
  rwa [integral_sin_char hh, sub_zero, toReal_eVariationOn_sin_two_pi_mul hh] at key

/-! ## Step 2: recombining the two parts -/

/-- `‖z‖ ≤ √2 · M` as soon as both `|Re z|` and `|Im z|` are at most `M`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem norm_le_sqrt_two_mul {z : ℂ} {M : ℝ} (hre : |z.re| ≤ M) (him : |z.im| ≤ M) :
    ‖z‖ ≤ Real.sqrt 2 * M := by
  have hM : 0 ≤ M := (abs_nonneg _).trans hre
  have h1 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have h2 : z.re ^ 2 ≤ M ^ 2 := by nlinarith [sq_abs z.re, abs_nonneg z.re]
  have h3 : z.im ^ 2 ≤ M ^ 2 := by nlinarith [sq_abs z.im, abs_nonneg z.im]
  have h5 : 0 ≤ Real.sqrt 2 * M := by positivity
  have h4 : ‖z‖ ^ 2 ≤ (Real.sqrt 2 * M) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    linarith
  calc ‖z‖ = Real.sqrt (‖z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg z)).symm
    _ ≤ Real.sqrt ((Real.sqrt 2 * M) ^ 2) := Real.sqrt_le_sqrt h4
    _ = Real.sqrt 2 * M := Real.sqrt_sq h5

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem re_average_char (h : ℕ) (x : ℕ → ℝ) (N : ℕ) :
    ((∑ n ∈ Finset.range N, cexp1 ((h : ℝ) * x n)) / (N : ℂ)).re
      = (∑ n ∈ Finset.range N, Real.cos (2 * Real.pi * h * x n)) / N := by
  rw [Complex.div_natCast_re, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [cexp1, Complex.exp_ofReal_mul_I_re]
  congr 1
  ring

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem im_average_char (h : ℕ) (x : ℕ → ℝ) (N : ℕ) :
    ((∑ n ∈ Finset.range N, cexp1 ((h : ℝ) * x n)) / (N : ℂ)).im
      = (∑ n ∈ Finset.range N, Real.sin (2 * Real.pi * h * x n)) / N := by
  rw [Complex.div_natCast_im, Complex.im_sum]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [cexp1, Complex.exp_ofReal_mul_I_im]
  congr 1
  ring

/-- **`|S_N| ≤ 4√2 h D*_N`** — the note's discrepancy bound on a Weyl sum, for an arbitrary
real sequence.  This is the whole content of Koksma's inequality for Weyl sums. -/
@[category research solved, AMS 11, ref "KN74", group "bugeaud_10_61"]
theorem norm_average_char_le {h : ℕ} (hh : 0 < h) (x : ℕ → ℝ) (N : ℕ) :
    ‖(∑ n ∈ Finset.range N, cexp1 ((h : ℝ) * x n)) / (N : ℂ)‖
      ≤ 4 * Real.sqrt 2 * h * starDiscrepancy x N := by
  have key := norm_le_sqrt_two_mul (z := (∑ n ∈ Finset.range N, cexp1 ((h : ℝ) * x n)) / (N : ℂ))
    (M := 4 * h * starDiscrepancy x N)
    (by rw [re_average_char]; exact abs_average_cos_le hh x N)
    (by rw [im_average_char]; exact abs_average_sin_le hh x N)
  have e : Real.sqrt 2 * (4 * (h : ℝ) * starDiscrepancy x N)
      = 4 * Real.sqrt 2 * h * starDiscrepancy x N := by ring
  linarith [key, e.le, e.ge]

/-! ## Step 3: the floor -/

namespace QuadSetup

variable (P : QuadSetup)

/-- **M5 Corollary 4, the eventual form.**  At a Bernoulli(`p`)-generic word the star
discrepancy of the orbit eventually exceeds every value below `|G_p(h)|/(4√2 h)`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem eventually_le_starDiscrepancy {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) {ε : ℕ → Bool}
    (hgen : IsGenericFor (bernNP h0 h1) ε) {h : ℕ} (hh : 0 < h) {c : ℝ}
    (hc : c < ‖P.weylC p (h : ℝ)‖ / (4 * Real.sqrt 2 * h)) :
    ∀ᶠ N in atTop,
      c ≤ starDiscrepancy (fun n => piVal P.α ε * P.α ^ n) N := by
  set x : ℕ → ℝ := fun n => piVal P.α ε * P.α ^ n with hxdef
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hsqrt : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hA : (0 : ℝ) < 4 * Real.sqrt 2 * h := by positivity
  have hcA : c * (4 * Real.sqrt 2 * (h : ℝ)) < ‖P.weylC p (h : ℝ)‖ := by
    rw [lt_div_iff₀ hA] at hc; exact hc
  have hcast : (((h : ℤ) : ℝ)) = (h : ℝ) := by push_cast; ring
  have htend := P.tendsto_weylSum_bern h0 h1 hgen (h : ℤ)
  rw [hcast] at htend
  have hnorm := htend.norm
  have hev := hnorm.eventually_const_lt hcA
  have hbd : ∀ N : ℕ, ‖(∑ n ∈ Finset.range (N + 1), cexp1 ((h : ℝ) * x n)) / ((N : ℂ) + 1)‖
      ≤ 4 * Real.sqrt 2 * h * starDiscrepancy x (N + 1) := by
    intro N
    have e2 : ((N : ℂ) + 1) = ((N + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [e2]
    exact norm_average_char_le hh x (N + 1)
  have hstep : ∀ᶠ N in atTop, c ≤ starDiscrepancy x (N + 1) := by
    filter_upwards [hev] with N hN
    have hb := hbd N
    have : c * (4 * Real.sqrt 2 * (h : ℝ))
        < 4 * Real.sqrt 2 * (h : ℝ) * starDiscrepancy x (N + 1) := lt_of_lt_of_le hN hb
    nlinarith [this, hA]
  rw [Filter.eventually_atTop] at hstep ⊢
  obtain ⟨N₀, hN₀⟩ := hstep
  refine ⟨N₀ + 1, fun M hM => ?_⟩
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  exact hN₀ M' (by omega)

/-- **M5 Corollary 4, the discrepancy floor.**  At a Bernoulli(`p`)-generic digit word `ε`, the
orbit of `ξ = π(ε)` obeys `liminf_N D*_N ≥ |G_p(h)|/(4√2 h)` at every frequency `h ≥ 1`.

Taking the maximum over `h` is the note's statement; taking `h = 1`, `p = 1/2` and
`weylC_half_one_ne_zero` makes it positive (`starDiscrepancy_floor_pos`). -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem le_liminf_starDiscrepancy {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) {ε : ℕ → Bool}
    (hgen : IsGenericFor (bernNP h0 h1) ε) {h : ℕ} (hh : 0 < h) :
    ‖P.weylC p (h : ℝ)‖ / (4 * Real.sqrt 2 * h)
      ≤ liminf (fun N => starDiscrepancy (fun n => piVal P.α ε * P.α ^ n) N) atTop := by
  set x : ℕ → ℝ := fun n => piVal P.α ε * P.α ^ n with hxdef
  have hcob : IsCoboundedUnder (· ≥ ·) atTop (fun N => starDiscrepancy x N) :=
    Filter.isCoboundedUnder_ge_of_le atTop (fun N => starDiscrepancy_le_one x N)
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨c, hc1, hc2⟩ := exists_between hcon
  exact absurd (Filter.le_liminf_of_le hcob
    (P.eventually_le_starDiscrepancy h0 h1 hgen hh hc2)) (not_le.mpr hc1)

/-- **The floor is positive at the fair coin.**  For a quadratic Pisot `α > 2` and a
`μ_{1/2}`-generic word, `liminf_N D*_N ≥ |G_{1/2}(1)|/(4√2) > 0`: the orbit is not merely
non-equidistributed, its discrepancy stays bounded away from `0`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem starDiscrepancy_floor_pos (h2 : 2 < P.α) (hirr : Irrational P.α) {ε : ℕ → Bool}
    (hgen : IsGenericFor (bernNP (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2 ≤ 1)) ε) :
    0 < liminf (fun N => starDiscrepancy (fun n => piVal P.α ε * P.α ^ n) N) atTop := by
  have hne : P.weylC (1 / 2) 1 ≠ 0 := P.weylC_half_one_ne_zero h2 hirr
  have hpos : 0 < ‖P.weylC (1 / 2) ((1 : ℕ) : ℝ)‖ := by
    simpa using norm_pos_iff.mpr hne
  have hA : (0 : ℝ) < 4 * Real.sqrt 2 * ((1 : ℕ) : ℝ) := by
    have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    positivity
  refine lt_of_lt_of_le (div_pos hpos hA) ?_
  exact P.le_liminf_starDiscrepancy (by norm_num) (by norm_num) hgen Nat.one_pos

end QuadSetup

end BB61
