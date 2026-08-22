/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.Constants

/-!
# Span-stratified line counts: tall towers are rarer (W8 of plan2-BB13)

The line cover of `BB13/LineCover.lean` spends the whole exponent budget `2 + ε*` on a bare
failure.  A failure that is the **base of a tall relation-tower** carries more than that: if
`a` and `b` lie on one line then `2ᵇ⁻ᵃ ∣ mₐ` (`BB13.sameTower_dvd`), so the frame point
`x = mₐ2ᵃ` is `2`-adically small to depth `a + (b − a)`, not merely `a`.  Feeding the surplus
back into the system sharpens the `2`-adic exponent from `θ` to `θ(1 + γ)` whenever the span is
at least `γ·a`, and the budget becomes

`θ + θ(1 + γ) + 1 = 2 + (ε* + γθ)`,

so the very same Bugeaud–Evertse corollary now counts lines at the *larger* exponent `ε* + γθ`,
where its constant is smaller.  At `γ = 1/4`:

`K(ε* + θ/4) = 537 048 098 048` against `K(ε*) = 1 856 360 182 227` — a factor `3.46`.

When the companion `b` is itself a failure, the archimedean place carries a surplus of exactly the
same size and the exponent **doubles**, to `ε* + 2γθ`: see `BB13/SpanStrataSharp.lean`, where
`K(ε* + θ/2) = 249 269 834 049` at `γ = 1/4`.

The stratification is not vacuous only for `γ` below the confinement exponent: `span_ratio_lt`
shows a relation-tower always has `γ < log(3/2)/log 2 = 0.58496…`, so the useful range is
`0 < γ < 0.58496…` and the count degenerates to `BB13.towersAbove_card_le` at `γ = 0`.

## The corrected form of a natural mistake

A referee suggested stratifying by a **fixed absolute surplus** instead — counting the events
`‖(3/2)ⁿ‖ < 2^{−d}(3/4)ⁿ` at the frame `ε* + δ`.  That inequality runs the wrong way: the frame
demands `2^{−d} ≤ 3^{−nδ}`, i.e. `n ≤ d·log 2/(δ·log 3)`, an *upper* bound on `n` — a fixed
absolute surplus is worth less and less as `n` grows, and the set it captures is finite for
trivial reasons.  What survives is the **span-proportional** stratification above.  Its
`2`-adic half asks nothing of the companion, the divisibility `2ᵇ⁻ᵃ ∣ mₐ` being unconditional;
its archimedean half asks that the companion be a failure, and is `BB13/SpanStrataSharp.lean`'s
`tall_exception_towers_line_cover`, at the doubled exponent `ε* + 2γθ`.  The two are worth the
same `γθ`, and a fixed absolute surplus is worth neither.

The other variant — a count decaying in the *absolute* height `t` of a tower, uniformly in the
base — is equivalent to the open per-line problem and cannot come from Cor. 5.2 at all.

Footprint: `std3 + BugeaudEvertse.ridout_line_cover`.

## References

* [BE08] Bugeaud–Evertse, Acta Arith. **133** (2008), Cor. 5.2 — the line count.
* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, 2012 (Prob. 10.13).
* `plans/plan2-BB13.html` (W8); `plans/report-BB13.md` items A.3, B.6.
-/

namespace BB13

open scoped Real

/-! ### The sharpened `2`-adic condition -/

/-- **The `2`-adic surplus of a tower base**: if `2ᴰ ∣ mₐ` then `|x|₂ ≤ 2^{−(a+D)}` for the frame
point `x = mₐ2ᵃ` — the plain `frame_two_adic` is the case `D = 0`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem frame_two_adic_sharp {a D : ℕ} (hdvd : (2 : ℤ) ^ D ∣ Mnum 3 2 a) :
    ((padicNorm 2 ((frameX a : ℤ) : ℚ) : ℚ) : ℝ) ≤ (1 / 2 : ℝ) ^ (a + D) := by
  obtain ⟨k, hk⟩ := hdvd
  have hdvd' : ((2 ^ (a + D) : ℕ) : ℤ) ∣ frameX a := by
    refine ⟨k, ?_⟩
    rw [frameX, hk]
    push_cast
    rw [pow_add]
    ring
  have h := padicNorm.dvd_iff_norm_le.mp hdvd'
  have hcast : (((2 : ℚ) ^ (-((a + D : ℕ) : ℤ)) : ℚ) : ℝ) = (1 / 2 : ℝ) ^ (a + D) := by
    rw [zpow_neg, zpow_natCast]
    push_cast
    rw [one_div, inv_pow]
  rw [← hcast]
  exact_mod_cast h

/-- **The surplus, converted into an exponent**: `2^{−(a+D)} ≤ (3ᵃ)^{−θ(1+γ)}` as soon as the
span satisfies `D ≥ γ·a`. -/
@[category API, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem two_pow_le_rpow_of_span {a D : ℕ} {γ : ℝ} (hspan : γ * (a : ℝ) ≤ (D : ℝ)) :
    (1 / 2 : ℝ) ^ (a + D) ≤ ((3 : ℝ) ^ a) ^ (-(theta * (1 + γ))) := by
  have h3a : (0 : ℝ) < (3 : ℝ) ^ a := by positivity
  have hlhs : (0 : ℝ) < (1 / 2 : ℝ) ^ (a + D) := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [Real.rpow_def_of_pos h3a, ← Real.exp_log hlhs, Real.exp_le_exp, Real.log_pow, Real.log_pow,
    show Real.log (1 / 2 : ℝ) = -Real.log 2 by rw [← Real.log_inv]; norm_num]
  have hrhs : (a : ℝ) * Real.log 3 * (-(theta * (1 + γ)))
      = -((a : ℝ) * (1 + γ) * Real.log 2) := by
    rw [← theta_mul_log_three]; ring
  rw [hrhs]
  push_cast
  nlinarith [hspan, hl2]

/-! ### The stratified cover -/

/-- **Tall towers span fewer lines.**  The bases `a ≥ 10` of relation-towers of span at least
`γ·a` lie on at most `K(ε* + γθ)` lines through the origin — the same Bugeaud–Evertse count, run
at a larger exponent because the tower's `2`-adic surplus pays for it.

Only collinearity of the two frame points is used, not that `b` is itself a failure — which is
precisely what the sharp form (`BB13.tall_exception_towers_line_cover`) trades away in exchange
for the archimedean half of the surplus. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem tall_towers_line_cover (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ R : Finset ℚ, R.card ≤ BugeaudEvertse.lineBound (epsStar + γ * theta) ∧
      ∀ a b : ℕ, 10 ≤ a → a < b → IsFailure 3 2 (3 / 4) a → SameTower a b →
        γ * (a : ℝ) ≤ ((b - a : ℕ) : ℝ) → linePoint a ∈ R := by
  have hth := theta_pos
  have hes := epsStar_pos
  have hε : 0 < epsStar + γ * theta := by nlinarith
  obtain ⟨R, hcard, hR⟩ := BugeaudEvertse.ridout_line_cover_23 1 (epsStar + γ * theta) theta
    (theta * (1 + γ)) 1 hε theta_pos.le (by nlinarith) zero_le_one
    (by linear_combination theta_add_theta_add_one)
  refine ⟨R, hcard, fun a b ha hab hfa hsame hspan => ?_⟩
  have hheight : max (2 * ((BugeaudEvertse.ratHeight 1 : ℕ) : ℝ))
      ((2 : ℝ) ^ ((4 : ℝ) / (epsStar + γ * theta))) < ((frameY a : ℤ) : ℝ) := by
    rw [frameY_cast, BugeaudEvertse.ratHeight_one]
    refine max_lt ?_ ?_
    · have h1 : (3 : ℝ) ^ 10 ≤ (3 : ℝ) ^ a := pow_le_pow_right₀ (by norm_num) ha
      norm_num at h1 ⊢
      linarith
    · refine lt_of_le_of_lt ?_ (two_rpow_four_div_epsStar_lt ha)
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_
      exact div_le_div_of_nonneg_left (by norm_num) hes (by nlinarith)
  refine hR (frameX a) (frameY a) (frameY_pos a) hheight ?_ ?_ (frame_three_adic a)
  · simpa using frame_archimedean hfa
  · rw [frameY_cast]
    exact le_trans (frame_two_adic_sharp (sameTower_dvd (le_of_lt hab) hsame))
      (two_pow_le_rpow_of_span hspan)

/-- **The stratified count**: at most `K(ε* + γθ)` lines carry a relation-tower of span
`≥ γ·(base)`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem tall_towerBases_card_le (γ : ℝ) (hγ : 0 ≤ γ) :
    {r : ℚ | ∃ a b : ℕ, 10 ≤ a ∧ a < b ∧ IsFailure 3 2 (3 / 4) a ∧ SameTower a b ∧
      γ * (a : ℝ) ≤ ((b - a : ℕ) : ℝ) ∧ linePoint a = r}.ncard
        ≤ BugeaudEvertse.lineBound (epsStar + γ * theta) := by
  obtain ⟨R, hcard, hR⟩ := tall_towers_line_cover γ hγ
  have hsub : {r : ℚ | ∃ a b : ℕ, 10 ≤ a ∧ a < b ∧ IsFailure 3 2 (3 / 4) a ∧ SameTower a b ∧
      γ * (a : ℝ) ≤ ((b - a : ℕ) : ℝ) ∧ linePoint a = r} ⊆ ↑R := by
    rintro r ⟨a, b, ha, hab, hfa, hsame, hspan, rfl⟩
    exact hR a b ha hab hfa hsame hspan
  calc {r : ℚ | ∃ a b : ℕ, 10 ≤ a ∧ a < b ∧ IsFailure 3 2 (3 / 4) a ∧ SameTower a b ∧
        γ * (a : ℝ) ≤ ((b - a : ℕ) : ℝ) ∧ linePoint a = r}.ncard
      ≤ (↑R : Set ℚ).ncard := Set.ncard_le_ncard hsub R.finite_toSet
    _ = R.card := Set.ncard_coe_finset R
    _ ≤ BugeaudEvertse.lineBound (epsStar + γ * theta) := hcard

/-! ### The useful range of `γ` -/

/-- **The stratification saturates at the confinement exponent**: a relation-tower over `a` has
span less than `(log₂3 − 1)·a = 0.58496…·a`, so no `γ` beyond that captures anything.  (Combined
with `tall_towers_line_cover`, the counts interpolate between `K(ε*)` at `γ = 0` and the empty
statement at `γ = log(3/2)/log 2`.) -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem span_ratio_lt {a b : ℕ} {γ : ℝ} (ha : 1 ≤ a) (hab : a < b)
    (hfb : IsFailure 3 2 (3 / 4) b) (h : SameTower a b)
    (hspan : γ * (a : ℝ) ≤ ((b - a : ℕ) : ℝ)) :
    γ < Real.log (3 / 2) / Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha' : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hsp := sameTower_span_lt ha hab hfb h
  rw [lt_div_iff₀ hl2]
  nlinarith [mul_le_mul_of_nonneg_right hspan hl2.le]

/-! ### The constant at `γ = 1/4` -/

/-- `1 + 1/(ε* + θ/4) ≤ 3.384`, i.e. `3.384·log 3 ≤ 5.364·log 2`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem one_add_inv_epsStar_quarter_le : 1 + (epsStar + (1 / 4 : ℝ) * theta)⁻¹ ≤ 3.384 := by
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hval : epsStar + (1 / 4 : ℝ) * theta
      = (2.25 * Real.log 2 - Real.log 3) / Real.log 3 := by
    rw [epsStar, theta, log_four_thirds_eq]
    field_simp
    ring
  have hden : (0 : ℝ) < 2.25 * Real.log 2 - Real.log 3 := by
    linarith [Real.log_two_gt_d9, log_three_le]
  have hinv : (epsStar + (1 / 4 : ℝ) * theta)⁻¹
      = Real.log 3 / (2.25 * Real.log 2 - Real.log 3) := by
    rw [hval, inv_div]
  have hkey : Real.log 3 ≤ 2.384 * (2.25 * Real.log 2 - Real.log 3) := by
    linarith [Real.log_two_gt_d9, log_three_le]
  have hdiv : Real.log 3 / (2.25 * Real.log 2 - Real.log 3) ≤ 2.384 :=
    (div_le_iff₀ hden).mpr hkey
  rw [hinv]
  linarith

/-- **`K(ε* + θ/4) ≤ 5.38 · 10¹¹`**, certified; the true value is `537 048 098 048`.  Towers of
span at least a quarter of their base are confined to `3.46` times fewer lines than failures in
general. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem lineBound_epsStar_quarter_le :
    BugeaudEvertse.lineBound (epsStar + (1 / 4 : ℝ) * theta) ≤ 538000000000 := by
  rw [BugeaudEvertse.lineBound]
  refine Nat.ceil_le.mpr ?_
  have hth := theta_pos
  have hes := epsStar_pos
  have hεpos : (0 : ℝ) < epsStar + (1 / 4 : ℝ) * theta := by nlinarith
  have hA := one_add_inv_epsStar_quarter_le
  have h1 : (1 : ℝ) ≤ 1 + (epsStar + (1 / 4 : ℝ) * theta)⁻¹ := by
    have : 0 < (epsStar + (1 / 4 : ℝ) * theta)⁻¹ := by positivity
    linarith
  have hA0 : (0 : ℝ) ≤ 1 + (epsStar + (1 / 4 : ℝ) * theta)⁻¹ := by linarith
  have hB := log_six_le
  have hB0 : (0 : ℝ) ≤ Real.log 6 := by linarith [one_le_log_six]
  have hargpos : (0 : ℝ) < (1 + (epsStar + (1 / 4 : ℝ) * theta)⁻¹) * Real.log 6 := by
    nlinarith [one_le_log_six]
  have hargle : (1 + (epsStar + (1 / 4 : ℝ) * theta)⁻¹) * Real.log 6 ≤ 6.06332 := by
    nlinarith [mul_le_mul hA hB hB0 (by norm_num : (0 : ℝ) ≤ 3.384)]
  have hC : Real.log ((1 + (epsStar + (1 / 4 : ℝ) * theta)⁻¹) * Real.log 6) ≤ 1.80232 := by
    refine le_trans (Real.log_le_log hargpos hargle) ?_
    rw [show (6.06332 : ℝ) = 6 * (6.06332 / 6) by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 6.06332 / 6 by norm_num)
    linarith [log_six_le]
  have hC0 : (0 : ℝ) ≤ Real.log ((1 + (epsStar + (1 / 4 : ℝ) * theta)⁻¹) * Real.log 6) := by
    refine Real.log_nonneg ?_
    nlinarith [one_le_log_six]
  push_cast
  calc (2 : ℝ) ^ 32 * (1 + (epsStar + (1 / 4 : ℝ) * theta)⁻¹) ^ 3 * Real.log 6
        * Real.log ((1 + (epsStar + (1 / 4 : ℝ) * theta)⁻¹) * Real.log 6)
      ≤ (2 : ℝ) ^ 32 * 3.384 ^ 3 * 1.79175947 * 1.80232 := by gcongr
    _ ≤ 538000000000 := by norm_num

/-- **The stratified count in decimal form**: at most `5.38 · 10¹¹` lines carry a relation-tower
whose span is at least a quarter of its base. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem tall_towerBases_card_le_decimal :
    {r : ℚ | ∃ a b : ℕ, 10 ≤ a ∧ a < b ∧ IsFailure 3 2 (3 / 4) a ∧ SameTower a b ∧
      (1 / 4 : ℝ) * (a : ℝ) ≤ ((b - a : ℕ) : ℝ) ∧ linePoint a = r}.ncard
        ≤ 538000000000 :=
  le_trans (tall_towerBases_card_le (1 / 4 : ℝ) (by norm_num)) lineBound_epsStar_quarter_le

end BB13
