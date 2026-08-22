/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.CensusSweep

/-!
# The archimedean half of the span surplus

`BB13/SpanStrata.lean` stratifies the line cover by the **span** `b − a` of a relation-tower and
spends the surplus at the `2`-adic place alone: from `2ᵇ⁻ᵃ ∣ mₐ` (`BB13.sameTower_dvd`) it
sharpens `f₂` from `θ` to `θ(1 + γ)` whenever `b − a ≥ γ·a`, so the budget becomes
`θ + θ(1+γ) + 1 = 2 + (ε* + γθ)` and at `γ = 1/4` the count falls from
`K(ε*) = 1 856 360 182 227` to `K(ε* + θ/4) = 537 048 098 048`.

**Half the surplus was left on the table.**  Collinearity constrains the *archimedean* place too.
Along a line the residues scale, `k_b = 3ᵇ⁻ᵃ·kₐ` (`BB13.sameTower_resid`), so if the companion
`b` is itself an exception, `|k_b| < (3/2)ᵇ`, then

`|kₐ| = |k_b|/3ᵇ⁻ᵃ < (3/2)ᵃ·(3/2)ᵇ⁻ᵃ/3ᵇ⁻ᵃ = (3/2)ᵃ·2^{−(b−a)} ≤ (3/2)ᵃ·2^{−γa}`,

which is exactly `f_∞ = θ(1 + γ)` in the frame.  Both non-trivial places now carry the surplus:

`θ(1+γ) + θ(1+γ) + 1 = 2 + (ε* + 2γθ)`,

and the Bugeaud–Evertse count runs at **twice** the sharpened exponent.  At `γ = 1/4`:

`K(ε* + θ/2) = 249 269 834 049` against `K(ε* + θ/4) = 537 048 098 048` — a further factor
`2.154`, and `7.45` below `K(ε*)`.

## What it costs, and what it buys back

`BB13.tall_towers_line_cover` needs only that `a` is an exception and that `b` is *collinear*
with it — `b` itself need not be an exception.  The archimedean sharpening does need `b` to be an
exception: without it the only bound on `k_b` is the rounding bound `|k_b| ≤ 2ᵇ⁻¹`
(`BB13.frame_archimedean_trivial`), which is weaker than `(3/2)ᵇ` by `(4/3)ᵇ` and gives nothing.
This is no loss where the stratification is used, because a line carrying several exceptions has
all of its members exceptions by definition.

What is bought back is the hypothesis on `a`: the archimedean bound for the base now *comes*
from the companion, so `IsFailure a` is no longer assumed — indeed it follows
(`isFailure_of_sameTower_failure`: a collinear predecessor of an exception is an exception).
Compare `BB13.span_ratio_lt`, which already needed `b` to be an exception, so the ceiling
`γ < log(3/2)/log 2 = 0.58496…` on the useful range is unchanged.

Footprint: `std3 + BugeaudEvertse.ridout_line_cover`.

## References

* [BE08] Bugeaud–Evertse, Acta Arith. **133** (2008), Cor. 5.2 — the line count.
* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, 2012 (Prob. 10.13).
* `plans/report3-BB13.html`, §Theorem D; `plans/suggestions-BB13.md`, item 1.
-/

namespace BB13

open scoped Real

/-! ### The sharpened archimedean condition -/

/-- **The residue of a tower base, sharpened by the span.**  If `a < b` lie on one line and `b`
is an exception, then `|kₐ| < (3/2)ᵃ·2^{−(b−a)}`: the base residue is the companion's, divided by
`3ᵇ⁻ᵃ`, and the exception bound on `k_b` converts the extra `3ᵇ⁻ᵃ` into `2^{−(b−a)}`.

The `γ = 0` reading is `BB13.abs_resid_lt_of_isFailure` for `a`; the `|kₐ| ≥ 1` reading is
`BB13.sameTower_gap`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem abs_resid_lt_of_sameTower_failure {a b : ℕ} (hab : a < b)
    (hfb : IsFailure 3 2 (3 / 4) b) (h : SameTower a b) :
    |((resid 3 2 a : ℤ) : ℝ)| < (3 / 2 : ℝ) ^ a * (1 / 2 : ℝ) ^ (b - a) := by
  set d := b - a with hd
  have hb : b = a + d := by omega
  have hk : resid 3 2 b = (3 : ℤ) ^ d * resid 3 2 a := sameTower_resid (le_of_lt hab) h
  have hkR : |((resid 3 2 b : ℤ) : ℝ)| = (3 : ℝ) ^ d * |((resid 3 2 a : ℤ) : ℝ)| := by
    rw [hk]; push_cast; rw [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
  have hkb := abs_resid_lt_of_isFailure hfb
  rw [hkR, hb, pow_add] at hkb
  have hsplit : (3 / 2 : ℝ) ^ d = (3 : ℝ) ^ d * (1 / 2 : ℝ) ^ d := by
    rw [← mul_pow]; norm_num
  rw [hsplit, show (3 / 2 : ℝ) ^ a * ((3 : ℝ) ^ d * (1 / 2 : ℝ) ^ d)
      = (3 : ℝ) ^ d * ((3 / 2 : ℝ) ^ a * (1 / 2 : ℝ) ^ d) by ring] at hkb
  exact lt_of_mul_lt_mul_left hkb (by positivity)

/-- **A collinear predecessor of an exception is an exception.**  The `2^{−(b−a)} ≤ 1/2` reading
of `abs_resid_lt_of_sameTower_failure`: the base of a relation-tower over an exception inherits
the smallness, with room to spare. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem isFailure_of_sameTower_failure {a b : ℕ} (hab : a < b)
    (hfb : IsFailure 3 2 (3 / 4) b) (h : SameTower a b) : IsFailure 3 2 (3 / 4) a := by
  have hlt := abs_resid_lt_of_sameTower_failure hab hfb h
  have hhalf : (1 / 2 : ℝ) ^ (b - a) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h32 : (0 : ℝ) < (3 / 2 : ℝ) ^ a := by positivity
  have key : |((resid 3 2 a : ℤ) : ℝ)| < (3 / 2 : ℝ) ^ a := by nlinarith
  simp only [IsFailure]
  norm_num
  exact key

/-- **The archimedean condition, sharpened by the span**: `|1 − x/y| ≤ y^{−θ(1+γ)}` for the frame
point of the base `a`, given a collinear exception `b` at distance at least `γ·a`.  The
`γ = 0` case is `BB13.frame_archimedean`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem frame_archimedean_sharp {a b : ℕ} {γ : ℝ} (hab : a < b)
    (hfb : IsFailure 3 2 (3 / 4) b) (h : SameTower a b)
    (hspan : γ * (a : ℝ) ≤ ((b - a : ℕ) : ℝ)) :
    |(1 : ℝ) - (frameX a : ℝ) / (frameY a : ℝ)|
      ≤ ((frameY a : ℤ) : ℝ) ^ (-(theta * (1 + γ))) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ a := by positivity
  rw [frame_arch_eq, frameY_cast]
  have hlt := abs_resid_lt_of_sameTower_failure hab hfb h
  have hstep : |((resid 3 2 a : ℤ) : ℝ)| / (3 : ℝ) ^ a
      < ((3 / 2 : ℝ) ^ a * (1 / 2 : ℝ) ^ (b - a)) / (3 : ℝ) ^ a := by gcongr
  have hbase : ((1 : ℝ) / 2) ^ a * (3 : ℝ) ^ a = (3 / 2 : ℝ) ^ a := by
    rw [← mul_pow]; norm_num
  have hpow : ((3 / 2 : ℝ) ^ a * (1 / 2 : ℝ) ^ (b - a)) / (3 : ℝ) ^ a
      = (1 / 2 : ℝ) ^ (a + (b - a)) := by
    rw [pow_add, div_eq_iff (by positivity : ((3 : ℝ) ^ a) ≠ 0)]
    linear_combination (-((1 : ℝ) / 2) ^ (b - a)) * hbase
  rw [hpow] at hstep
  exact le_trans (le_of_lt hstep) (two_pow_le_rpow_of_span hspan)

/-! ### The doubly stratified cover -/

/-- **Tall towers over an exception span far fewer lines.**  The bases `a ≥ 10` of relation-towers
of span at least `γ·a` whose *top* is an exception lie on at most `K(ε* + 2γθ)` lines through the
origin — the same Bugeaud–Evertse count as `BB13.tall_towers_line_cover`, run at **twice** the
sharpened exponent, because the tower pays at the archimedean place as well as the `2`-adic one.

No failure hypothesis on `a` is needed: it follows (`isFailure_of_sameTower_failure`). -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem tall_exception_towers_line_cover (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ R : Finset ℚ, R.card ≤ BugeaudEvertse.lineBound (epsStar + 2 * γ * theta) ∧
      ∀ a b : ℕ, 10 ≤ a → a < b → IsFailure 3 2 (3 / 4) b → SameTower a b →
        γ * (a : ℝ) ≤ ((b - a : ℕ) : ℝ) → linePoint a ∈ R := by
  have hth := theta_pos
  have hes := epsStar_pos
  have hε : 0 < epsStar + 2 * γ * theta := by nlinarith
  obtain ⟨R, hcard, hR⟩ := BugeaudEvertse.ridout_line_cover_23 1 (epsStar + 2 * γ * theta)
    (theta * (1 + γ)) (theta * (1 + γ)) 1 hε (by nlinarith) (by nlinarith) zero_le_one
    (by linear_combination theta_add_theta_add_one)
  refine ⟨R, hcard, fun a b ha hab hfb hsame hspan => ?_⟩
  have hheight : max (2 * ((BugeaudEvertse.ratHeight 1 : ℕ) : ℝ))
      ((2 : ℝ) ^ ((4 : ℝ) / (epsStar + 2 * γ * theta))) < ((frameY a : ℤ) : ℝ) := by
    rw [frameY_cast, BugeaudEvertse.ratHeight_one]
    refine max_lt ?_ ?_
    · have h1 : (3 : ℝ) ^ 10 ≤ (3 : ℝ) ^ a := pow_le_pow_right₀ (by norm_num) ha
      norm_num at h1 ⊢
      linarith
    · refine lt_of_le_of_lt ?_ (two_rpow_four_div_epsStar_lt ha)
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_
      exact div_le_div_of_nonneg_left (by norm_num) hes (by nlinarith)
  refine hR (frameX a) (frameY a) (frameY_pos a) hheight ?_ ?_ (frame_three_adic a)
  · simpa using frame_archimedean_sharp hab hfb hsame hspan
  · rw [frameY_cast]
    exact le_trans (frame_two_adic_sharp (sameTower_dvd (le_of_lt hab) hsame))
      (two_pow_le_rpow_of_span hspan)

/-- **The doubly stratified count**: at most `K(ε* + 2γθ)` lines carry a relation-tower of span
`≥ γ·(base)` topped by an exception. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem tall_exception_towerBases_card_le (γ : ℝ) (hγ : 0 ≤ γ) :
    {r : ℚ | ∃ a b : ℕ, 10 ≤ a ∧ a < b ∧ IsFailure 3 2 (3 / 4) b ∧ SameTower a b ∧
      γ * (a : ℝ) ≤ ((b - a : ℕ) : ℝ) ∧ linePoint a = r}.ncard
        ≤ BugeaudEvertse.lineBound (epsStar + 2 * γ * theta) := by
  obtain ⟨R, hcard, hR⟩ := tall_exception_towers_line_cover γ hγ
  have hsub : {r : ℚ | ∃ a b : ℕ, 10 ≤ a ∧ a < b ∧ IsFailure 3 2 (3 / 4) b ∧ SameTower a b ∧
      γ * (a : ℝ) ≤ ((b - a : ℕ) : ℝ) ∧ linePoint a = r} ⊆ ↑R := by
    rintro r ⟨a, b, ha, hab, hfb, hsame, hspan, rfl⟩
    exact hR a b ha hab hfb hsame hspan
  calc {r : ℚ | ∃ a b : ℕ, 10 ≤ a ∧ a < b ∧ IsFailure 3 2 (3 / 4) b ∧ SameTower a b ∧
        γ * (a : ℝ) ≤ ((b - a : ℕ) : ℝ) ∧ linePoint a = r}.ncard
      ≤ (↑R : Set ℚ).ncard := Set.ncard_le_ncard hsub R.finite_toSet
    _ = R.card := Set.ncard_coe_finset R
    _ ≤ BugeaudEvertse.lineBound (epsStar + 2 * γ * theta) := hcard

/-! ### The constant at `γ = 1/4` -/

/-- `1 + 1/(ε* + θ/2) ≤ 2.73213`, i.e. `2.73213·log 3 ≤ 4.330325·log 2`.  The margin is
`9.7·10⁻⁷` on the certified enclosures — the tightest step of the file. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem one_add_inv_epsStar_half_le : 1 + (epsStar + (1 / 2 : ℝ) * theta)⁻¹ ≤ 2.73213 := by
  have hval : epsStar + (1 / 2 : ℝ) * theta
      = (2.5 * Real.log 2 - Real.log 3) / Real.log 3 := by
    rw [epsStar, theta, log_four_thirds_eq]
    field_simp
    ring
  have hden : (0 : ℝ) < 2.5 * Real.log 2 - Real.log 3 := by
    linarith [Real.log_two_gt_d9, log_three_le]
  have hinv : (epsStar + (1 / 2 : ℝ) * theta)⁻¹
      = Real.log 3 / (2.5 * Real.log 2 - Real.log 3) := by
    rw [hval, inv_div]
  have hkey : Real.log 3 ≤ 1.73213 * (2.5 * Real.log 2 - Real.log 3) := by
    linarith [Real.log_two_gt_d9, log_three_le]
  have hdiv : Real.log 3 / (2.5 * Real.log 2 - Real.log 3) ≤ 1.73213 :=
    (div_le_iff₀ hden).mpr hkey
  rw [hinv]
  linarith

/-- `log(128/27) = 7·log 2 − 3·log 3 ≤ 1.5561934001` — the anchor of the nested logarithm.  The
`ε*` chain of `BB13/Constants.lean` anchors at `8`; here the argument is `4.895…` and `128/27`
is the nearest `2ᵃ3ᵇ`, which keeps the `log(1+t) ≤ t` step inside `3.3%`. -/
@[category API, AMS 11, ref "BE08", group "bugeaud_10_13"]
theorem log_128_div_27_le : Real.log (128 / 27 : ℝ) ≤ 1.5561934001 := by
  rw [show (128 / 27 : ℝ) = 2 ^ 7 / 3 ^ 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
  push_cast
  linarith [Real.log_two_lt_d9, log_three_ge]

/-- **`K(ε* + θ/2) ≤ 2.5 · 10¹¹`**, certified; the true value is `249 269 834 049`.  A tower of
span at least a quarter of its base, topped by an exception, is confined to `2.154` times fewer
lines than `BB13.lineBound_epsStar_quarter_le` allows, and `7.45` times fewer than `K(ε*)`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem lineBound_epsStar_half_le :
    BugeaudEvertse.lineBound (epsStar + (1 / 2 : ℝ) * theta) ≤ 250000000000 := by
  rw [BugeaudEvertse.lineBound]
  refine Nat.ceil_le.mpr ?_
  have hth := theta_pos
  have hes := epsStar_pos
  have hεpos : (0 : ℝ) < epsStar + (1 / 2 : ℝ) * theta := by nlinarith
  have hA := one_add_inv_epsStar_half_le
  have h1 : (1 : ℝ) ≤ 1 + (epsStar + (1 / 2 : ℝ) * theta)⁻¹ := by
    have : 0 < (epsStar + (1 / 2 : ℝ) * theta)⁻¹ := by positivity
    linarith
  have hA0 : (0 : ℝ) ≤ 1 + (epsStar + (1 / 2 : ℝ) * theta)⁻¹ := by linarith
  have hB := log_six_le
  have hB0 : (0 : ℝ) ≤ Real.log 6 := by linarith [one_le_log_six]
  have hargpos : (0 : ℝ) < (1 + (epsStar + (1 / 2 : ℝ) * theta)⁻¹) * Real.log 6 := by
    nlinarith [one_le_log_six]
  have hargle : (1 + (epsStar + (1 / 2 : ℝ) * theta)⁻¹) * Real.log 6 ≤ 4.8954 := by
    nlinarith [mul_le_mul hA hB hB0 (by norm_num : (0 : ℝ) ≤ 2.73213)]
  have hC : Real.log ((1 + (epsStar + (1 / 2 : ℝ) * theta)⁻¹) * Real.log 6) ≤ 1.58882 := by
    refine le_trans (Real.log_le_log hargpos hargle) ?_
    rw [show (4.8954 : ℝ) = (128 / 27) * (4.8954 * 27 / 128) by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4.8954 * 27 / 128 by norm_num)
    linarith [log_128_div_27_le]
  have hC0 : (0 : ℝ) ≤ Real.log ((1 + (epsStar + (1 / 2 : ℝ) * theta)⁻¹) * Real.log 6) := by
    refine Real.log_nonneg ?_
    nlinarith [one_le_log_six]
  push_cast
  calc (2 : ℝ) ^ 32 * (1 + (epsStar + (1 / 2 : ℝ) * theta)⁻¹) ^ 3 * Real.log 6
        * Real.log ((1 + (epsStar + (1 / 2 : ℝ) * theta)⁻¹) * Real.log 6)
      ≤ (2 : ℝ) ^ 32 * 2.73213 ^ 3 * 1.79175947 * 1.58882 := by gcongr
    _ ≤ 250000000000 := by norm_num

/-- **The doubly stratified count in decimal form**: at most `2.5 · 10¹¹` lines carry a
relation-tower whose span is at least a quarter of its base and whose top is an exception. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem tall_exception_towerBases_card_le_decimal :
    {r : ℚ | ∃ a b : ℕ, 10 ≤ a ∧ a < b ∧ IsFailure 3 2 (3 / 4) b ∧ SameTower a b ∧
      (1 / 4 : ℝ) * (a : ℝ) ≤ ((b - a : ℕ) : ℝ) ∧ linePoint a = r}.ncard
        ≤ 250000000000 := by
  have h := tall_exception_towerBases_card_le (1 / 4 : ℝ) (by norm_num)
  rw [show (2 : ℝ) * (1 / 4 : ℝ) * theta = (1 / 2 : ℝ) * theta by ring] at h
  exact le_trans h lineBound_epsStar_half_le

end BB13
