/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.CensusSweep

/-!
# Dickson's condition on the swept range, and the Waring count re-anchored

`BB13/Waring.lean` pays an exponent for the cutoff of its kernel arm.  A failure of Dickson's
condition `(Dₙ)` gives only the weaker smallness `‖(3/2)ⁿ‖ < (3/4)ⁿ⁻¹`
(`BB13.notDickson_imp_distBound`), i.e. `|kₙ| < (4/3)·(3/2)ⁿ`, so the frame point loses a factor
`4/3` at the archimedean place.  Buying it back costs `ε*/C` where `C` is the cutoff, because
`(3ᶜ)^{ε*/C} = (4/3)` exactly; with `C = 257` — the reach of the naive `decide` over `residNat`
(`BB13.dicksonCond_of_le_256`) — the budget becomes `2 + ε_W`, `ε_W = ε*(1 − 1/257)`, and
`K(ε_W) = 1 876 339 827 243` sits `1.1%` above `K(ε*) = 1 856 360 182 227`.

**The cutoff was a cost per index, not a mathematical obstruction.**  `BB13/CensusSweep.lean`
shows the state `(2ⁿ, ⌊3ⁿ/2ⁿ⌋, 3ⁿ mod 2ⁿ)` advances by one multiplication by `3`
(`BB13.sweep_spec`) — and that state *is* the data of Dickson's condition, which reads
`r + q + 2 ≤ 2ⁿ` in exactly those three coordinates.  So the same sweep that certified
`𝓔 ∩ [1, 10⁵] = {1,2,3,4,7}` certifies `(Dₙ)` for every `3 ≤ n ≤ 10⁵` at the same price, and the
cutoff moves from `257` to `100001`:

`ε_W′ = ε*(1 − 1/100001)`,  `K(ε_W′) = 1 856 411 140 906 ≤ 1.86·10¹²`,

against `K(ε*) = 1 856 360 182 227`.  The shave is not eliminated — it is `10⁻⁵` of `ε*` instead
of `4·10⁻³` — but it becomes **invisible at three significant digits**: the Waring count is now
quoted with the same constant `1.86·10¹²` as the exception count of `BB13.failures_card_le_decimal`,
so the Waring application no longer costs anything against Problem 10.13 itself.

Note that Dickson's condition is *not* the exception predicate: a Dickson failure needs only
`|kₙ| < (4/3)·(3/2)ⁿ`, a strictly weaker demand than `IsFailure`'s `|kₙ| < (3/2)ⁿ`, so
`BB13.failures_up_to_100000` does not imply anything here and the scan has to be run again on its
own predicate.  It confirms what [KW90] and [Cum25] report over the far longer range
`n ≤ 2³⁶ + 2³⁴`: below `100001` the only failures of `(Dₙ)` are `n = 1` and `n = 2`.

## What is superseded

`BB13.epsW`, `BB13.thetaW`, `BB13.notDickson_line_cover`,
`BB13.dickson_exceptions_card_le_of_heightBound`, `BB13.waring_exceptions_card_le_of_heightBound`
and `BB13.lineBound_epsW_le` are the `C = 257` versions of everything below.  They remain valid;
the primed statements here strictly improve them and are what the paper quotes.

Footprint: `std3` for the scan and the constants (kernel `decide`, no `native_decide`);
`std3 + BugeaudEvertse.ridout_line_cover` for the covers, plus
`BB13.waringNumber_ideal_of_dickson` for the `g(n)` count — the same footprints as the `257` row.

## References

* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, 2012, §3.7.
* [Dic36] L. E. Dickson, Bull. AMS **42** (1936) — the ideal Waring formula under `(Dₙ)`.
* [BE08] Bugeaud–Evertse, Acta Arith. **133** (2008), Cor. 5.2 — the line count.
* [KW90] Kubina–Wunderlich, Math. Comp. **55** (1990) — the computational range.
* `plans/report3-BB13.html`, §Theorem C; `plans/suggestions-BB13.md`, item 2.
-/

namespace BB13

open scoped Real

/-! ## 1. Dickson's condition on the sweep state -/

/-- Dickson's condition read off the sweep state: `r + q + 2 ≤ 2ⁿ` in the coordinates
`(2ⁿ, q, r)` of `BB13.sweep`.  The companion of `BB13.failBool`, on the `(4/3)`-event. -/
def dicksonBool (s : ℕ × ℕ × ℕ) : Bool := decide (s.2.2 + s.2.1 + 2 ≤ s.1)

/-- **The state decides Dickson's condition.** -/
@[category research solved, AMS 11, ref "Bug12" "Dic36", group "bugeaud_10_13"]
theorem dicksonBool_sweep (n : ℕ) : dicksonBool (sweep n) = true ↔ DicksonCond n := by
  simp only [dicksonBool, sweep_spec, DicksonCond, waringQuot, decide_eq_true_eq]

/-- The Dickson scan: `dicksonRun k` runs the sweep from `n = 1` through `n = k`, demanding
`(Dₙ)` at every index above `2`.  The two low failures `n = 1, 2` are let through by the
`st.2.1 ≤ 2` clause — they are genuine, and are the `2` in the counts below. -/
def dicksonRun : ℕ → Bool × ℕ × (ℕ × ℕ × ℕ)
  | 0 => (true, 1, sweep 1)
  | k + 1 =>
      let st := dicksonRun k
      (st.1 && (dicksonBool st.2.2 || decide (st.2.1 ≤ 2)), st.2.1 + 1, sweepStep st.2.2)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem dicksonRun_state (k : ℕ) : (dicksonRun k).2 = (k + 1, sweep (k + 1)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h1 : (dicksonRun k).2.1 = k + 1 := by rw [ih]
    have h2 : (dicksonRun k).2.2 = sweep (k + 1) := by rw [ih]
    simp only [dicksonRun, h1, h2, sweep_succ]

/-- **Soundness of the Dickson scan.**  A `true` verdict at `k` is the statement about the real
`DicksonCond`, index by index. -/
@[category research solved, AMS 11, ref "Bug12" "Dic36", group "bugeaud_10_13"]
theorem dicksonRun_sound : ∀ {k : ℕ}, (dicksonRun k).1 = true → ∀ {n : ℕ}, 3 ≤ n → n ≤ k →
    DicksonCond n := by
  intro k
  induction k with
  | zero => intro _ n h1 h2; omega
  | succ k ih =>
    intro hrun n h1 h2
    have hstate := dicksonRun_state k
    have hsplit : (dicksonRun (k + 1)).1
        = ((dicksonRun k).1
            && (dicksonBool (dicksonRun k).2.2 || decide ((dicksonRun k).2.1 ≤ 2))) := rfl
    rw [hsplit, Bool.and_eq_true] at hrun
    rcases Nat.lt_or_ge n (k + 1) with h | h
    · exact ih hrun.1 h1 (by omega)
    · have hn : n = k + 1 := by omega
      have hb := hrun.2
      simp only [hstate, Bool.or_eq_true, decide_eq_true_eq] at hb
      rcases hb with hb | hb
      · rw [hn]; exact (dicksonBool_sweep (k + 1)).mp hb
      · omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
/-- The kernel scan of Dickson's condition to `100000`, on the incremental sweep.  The naive
`decide` over the recomputed `3ⁿ` stops near `256` (`BB13.dicksonCond_of_le_256`); the recurrence
covers `10⁵` in roughly the two minutes `BB13.census_scan_100000` takes. -/
@[category test, AMS 11, ref "Bug12" "Dic36", group "bugeaud_10_13"]
theorem dickson_scan_100000 : (dicksonRun 100000).1 = true := by decide

/-- **Dickson's condition holds for every `3 ≤ n ≤ 100000`** — the kernel arm extended by a factor
`391` over `BB13.dicksonCond_of_le_256`, against the same exact-integer `DicksonCond`.  Below
`100001` the only failures are `n = 1` and `n = 2`.  Footprint `std3`. -/
@[category research solved, AMS 11, ref "Bug12" "Dic36", group "bugeaud_10_13"]
theorem dicksonCond_of_le_100000 {n : ℕ} (h3 : 3 ≤ n) (h : n ≤ 100000) : DicksonCond n :=
  dicksonRun_sound dickson_scan_100000 h3 h

/-! ## 2. The re-anchored Waring exponent -/

/-- The re-anchored Waring exponent `ε_W′ = ε*(1 − 1/100001) = 0.2618568…`: the sharp `ε*` shaved
by what the `(3/4)ⁿ⁻¹` event costs at the new cutoff `n = 100001`. -/
noncomputable def epsW' : ℝ := epsStar - epsStar / 100001

/-- The archimedean exponent of the re-anchored Waring frame, `θ_W′ = θ − ε*/100001`. -/
noncomputable def thetaW' : ℝ := theta - epsStar / 100001

@[category API, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem epsW'_pos : 0 < epsW' := by
  have := epsStar_pos
  rw [epsW']; linarith

@[category API, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem thetaW'_nonneg : 0 ≤ thetaW' := by
  have h1 := epsStar_pos
  have h2 := epsStar_lt_theta
  rw [thetaW']; linarith

/-- **The re-anchored Waring budget identity** `θ_W′ + θ + 1 = 2 + ε_W′`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem thetaW'_add_theta_add_one : thetaW' + theta + 1 = 2 + epsW' := by
  have := theta_add_theta_add_one
  rw [thetaW', epsW']; linarith

/-- The height condition (5.12) for the re-anchored frame, from the cutoff on. -/
@[category API, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem two_rpow_four_div_epsW'_lt {n : ℕ} (hn : 100001 ≤ n) :
    (2 : ℝ) ^ ((4 : ℝ) / epsW') < (3 : ℝ) ^ n := by
  refine two_rpow_four_div_lt epsW'_pos ?_
  have hlog : epsW' * Real.log 3 = Real.log (4 / 3) - Real.log (4 / 3) / 100001 := by
    rw [epsW', sub_mul, epsStar_mul_log_three, div_mul_eq_mul_div, epsStar_mul_log_three]
  have hn' : (100001 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hl43 : 0 < Real.log (4 / 3) := Real.log_pos (by norm_num)
  rw [hlog]
  nlinarith [four_log_two_lt, mul_le_mul_of_nonneg_right hn' hl43.le]

/-- **The shaved exponent buys back the factor `4/3`**: `(4/3)·2⁻ⁿ ≤ (3ⁿ)^{−θ_W′}` for
`n ≥ 100001`, since `(3ⁿ)^{ε*/100001} = (4/3)^{n/100001} ≥ 4/3` there.  This is the one place the
cutoff is spent, and moving it from `257` to `100001` is the whole content of the sharpening. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem rpow_neg_thetaW'_ge {n : ℕ} (hn : 100001 ≤ n) :
    (4 / 3 : ℝ) * (1 / 2 : ℝ) ^ n ≤ ((3 : ℝ) ^ n) ^ (-thetaW') := by
  have h3n : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hlhs : (0 : ℝ) < (4 / 3 : ℝ) * (1 / 2 : ℝ) ^ n := by positivity
  rw [Real.rpow_def_of_pos h3n, ← Real.exp_log hlhs, Real.exp_le_exp]
  have hlogL : Real.log ((4 / 3 : ℝ) * (1 / 2 : ℝ) ^ n)
      = Real.log (4 / 3) - (n : ℝ) * Real.log 2 := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
      show Real.log (1 / 2 : ℝ) = -Real.log 2 by rw [← Real.log_inv]; norm_num]
    ring
  have hrhs : Real.log ((3 : ℝ) ^ n) * (-thetaW') = -((n : ℝ) * (thetaW' * Real.log 3)) := by
    rw [Real.log_pow]; ring
  have hlt : thetaW' * Real.log 3 = Real.log 2 - Real.log (4 / 3) / 100001 := by
    rw [thetaW', sub_mul, theta_mul_log_three, div_mul_eq_mul_div, epsStar_mul_log_three]
  rw [hlogL, hrhs, hlt]
  have hn' : (100001 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hl43 : 0 < Real.log (4 / 3) := Real.log_pos (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_right hn' hl43.le]

/-! ## 3. The re-anchored line cover and counts -/

/-- The Dickson failures beyond the swept range. -/
def dicksonHigh' : Set ℕ := {n : ℕ | 100001 ≤ n ∧ ¬ DicksonCond n}

/-- The Dickson failures beyond the swept range on the line of slope `r`. -/
def dicksonFibre' (r : ℚ) : Set ℕ := {n : ℕ | 100001 ≤ n ∧ ¬ DicksonCond n ∧ linePoint n = r}

/-- **A single line carries finitely many Waring events** — the `K = 4/3` case of the elementary
confinement `BB13.sameTower_le_two_mul_of_bound`, above the new cutoff. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem dicksonFibre'_finite (r : ℚ) : (dicksonFibre' r).Finite := by
  rcases Set.eq_empty_or_nonempty (dicksonFibre' r) with he | ⟨a, ha⟩
  · rw [he]; exact Set.finite_empty
  · have ha0 : 100001 ≤ a := ha.1
    apply Set.Finite.subset (Set.finite_Iic (2 * a))
    intro b hb
    simp only [Set.mem_Iic]
    rcases le_or_gt b a with hle | hlt
    · omega
    · exact sameTower_le_two_mul_of_bound (by omega) hlt (by norm_num)
        (abs_resid_lt_of_notDickson (by omega) hb.2.1) (ha.2.2.trans hb.2.2.symm)

/-- **The re-anchored Waring line cover**: the Dickson failures `n ≥ 100001` lie on at most
`K(ε_W′) = 1 856 411 140 906` lines through the origin.  Instance of [BE08] Cor. 5.2 at the frame
`(θ_W′, θ, 1)`, budget `2 + ε_W′`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem notDickson_line_cover' :
    ∃ R : Finset ℚ, R.card ≤ BugeaudEvertse.lineBound epsW' ∧
      ∀ n : ℕ, 100001 ≤ n → ¬ DicksonCond n → linePoint n ∈ R := by
  obtain ⟨R, hcard, hR⟩ := BugeaudEvertse.ridout_line_cover_23 1 epsW' thetaW' theta 1
    epsW'_pos thetaW'_nonneg theta_pos.le zero_le_one thetaW'_add_theta_add_one
  refine ⟨R, hcard, fun n hn hnd => ?_⟩
  have hheight : max (2 * ((BugeaudEvertse.ratHeight 1 : ℕ) : ℝ)) ((2 : ℝ) ^ ((4 : ℝ) / epsW'))
      < ((frameY n : ℤ) : ℝ) := by
    rw [frameY_cast, BugeaudEvertse.ratHeight_one]
    refine max_lt ?_ (two_rpow_four_div_epsW'_lt hn)
    have h1 : (3 : ℝ) ^ 10 ≤ (3 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at h1 ⊢
    linarith
  refine hR (frameX n) (frameY n) (frameY_pos n) hheight ?_ (frame_two_adic n) (frame_three_adic n)
  have harch : |(1 : ℝ) - (frameX n : ℝ) / (frameY n : ℝ)|
      ≤ ((frameY n : ℤ) : ℝ) ^ (-thetaW') := by
    have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
    rw [frame_arch_eq, frameY_cast]
    have hres := abs_resid_lt_of_notDickson (by omega) hnd
    have hstep : |((resid 3 2 n : ℤ) : ℝ)| / (3 : ℝ) ^ n
        < ((4 / 3 : ℝ) * (3 / 2 : ℝ) ^ n) / (3 : ℝ) ^ n := by gcongr
    have hpow : ((4 / 3 : ℝ) * (3 / 2 : ℝ) ^ n) / (3 : ℝ) ^ n = (4 / 3 : ℝ) * (1 / 2 : ℝ) ^ n := by
      rw [mul_div_assoc, ← div_pow]; norm_num
    rw [hpow] at hstep
    exact le_trans (le_of_lt hstep) (rpow_neg_thetaW'_ge hn)
  simpa using harch

/-- **The re-anchored Dickson-failure count**: `#{n ≥ 1 : ¬(Dₙ)} ≤ 2 + H·K(ε_W′)`, conditional on
a per-line bound `H` above the swept range.  The `2` is exact — `n = 1` and `n = 2` do fail — and
by `dicksonCond_of_le_100000` nothing else below `100001` does. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem dickson_exceptions_card_le_of_heightBound' (H : ℕ)
    (hfib : ∀ r : ℚ, (dicksonFibre' r).ncard ≤ H) :
    {n : ℕ | 1 ≤ n ∧ ¬ DicksonCond n}.ncard ≤ 2 + H * BugeaudEvertse.lineBound epsW' := by
  obtain ⟨R, hcard, hR⟩ := notDickson_line_cover'
  have hfin : dicksonHigh'.Finite := by
    apply Set.Finite.subset (R.finite_toSet.biUnion (fun r _ => dicksonFibre'_finite r))
    rintro n ⟨hn, hnd⟩
    exact Set.mem_biUnion (hR n hn hnd) ⟨hn, hnd, rfl⟩
  have hfib' : ∀ r : ℚ, {n ∈ dicksonHigh' | linePoint n = r}.ncard ≤ H := by
    intro r
    have heq : {n ∈ dicksonHigh' | linePoint n = r} = dicksonFibre' r := by
      ext n
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
    rw [heq]; exact hfib r
  have himg : linePoint '' dicksonHigh' ⊆ ↑R := by
    rintro _ ⟨n, ⟨hn, hnd⟩, rfl⟩; exact hR n hn hnd
  have hhigh : dicksonHigh'.ncard ≤ H * BugeaudEvertse.lineBound epsW' := by
    calc dicksonHigh'.ncard
        ≤ H * (linePoint '' dicksonHigh').ncard :=
          Set.ncard_le_mul_ncard_image hfin linePoint H hfib'
      _ ≤ H * (↑R : Set ℚ).ncard :=
          Nat.mul_le_mul (le_refl H) (Set.ncard_le_ncard himg R.finite_toSet)
      _ = H * R.card := by rw [Set.ncard_coe_finset]
      _ ≤ H * BugeaudEvertse.lineBound epsW' := Nat.mul_le_mul (le_refl H) hcard
  have hsub : {n : ℕ | 1 ≤ n ∧ ¬ DicksonCond n} ⊆ ({1, 2} : Set ℕ) ∪ dicksonHigh' := by
    rintro n ⟨hn1, hnd⟩
    rcases lt_or_ge n 3 with h | h
    · exact Or.inl (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; omega)
    · rcases le_or_gt n 100000 with h100 | h100
      · exact absurd (dicksonCond_of_le_100000 h h100) hnd
      · exact Or.inr ⟨by omega, hnd⟩
  calc {n : ℕ | 1 ≤ n ∧ ¬ DicksonCond n}.ncard
      ≤ (({1, 2} : Set ℕ) ∪ dicksonHigh').ncard :=
        Set.ncard_le_ncard hsub (((Set.finite_singleton 2).insert 1).union hfin)
    _ ≤ ({1, 2} : Set ℕ).ncard + dicksonHigh'.ncard := Set.ncard_union_le _ _
    _ ≤ 2 + H * BugeaudEvertse.lineBound epsW' := by
        have h2 : ({1, 2} : Set ℕ).ncard = 2 := Set.ncard_pair (by norm_num)
        omega

/-- **The re-anchored Waring exception count**: `#{n ≥ 2 : g(n) ≠ 2ⁿ + ⌊(3/2)ⁿ⌋ − 2} ≤ H·K(ε_W′)`,
with no additive constant.  Every exception fails `(Dₙ)`; `dicksonCond_of_le_100000` clears
`[3, 100000]`, and `n = 2` — which does fail `(Dₙ)` — satisfies the ideal formula anyway. -/
@[category research solved, AMS 11, ref "BE08" "Bug12" "Dic36", group "bugeaud_10_13"]
theorem waring_exceptions_card_le_of_heightBound' (H : ℕ)
    (hfib : ∀ r : ℚ, (dicksonFibre' r).ncard ≤ H) :
    {n : ℕ | 2 ≤ n ∧ Nat.waringNumber n ≠ 2 ^ n + waringQuot n - 2}.ncard
      ≤ H * BugeaudEvertse.lineBound epsW' := by
  obtain ⟨R, hcard, hR⟩ := notDickson_line_cover'
  have hfin : dicksonHigh'.Finite := by
    apply Set.Finite.subset (R.finite_toSet.biUnion (fun r _ => dicksonFibre'_finite r))
    rintro n ⟨hn, hnd⟩
    exact Set.mem_biUnion (hR n hn hnd) ⟨hn, hnd, rfl⟩
  have hsub : {n : ℕ | 2 ≤ n ∧ Nat.waringNumber n ≠ 2 ^ n + waringQuot n - 2} ⊆ dicksonHigh' := by
    rintro n ⟨hn2, hne⟩
    have hnd : ¬ DicksonCond n := fun hd => hne (waringNumber_ideal_of_dickson n hn2 hd)
    refine ⟨?_, hnd⟩
    by_contra hlt
    rcases lt_or_ge n 3 with h | h
    · have hn : n = 2 := by omega
      subst hn
      exact hne (by rw [Nat.waringNumber_two]; decide)
    · exact hnd (dicksonCond_of_le_100000 h (by omega))
  have hfib' : ∀ r : ℚ, {n ∈ dicksonHigh' | linePoint n = r}.ncard ≤ H := by
    intro r
    have heq : {n ∈ dicksonHigh' | linePoint n = r} = dicksonFibre' r := by
      ext n
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
    rw [heq]; exact hfib r
  have himg : linePoint '' dicksonHigh' ⊆ ↑R := by
    rintro _ ⟨n, ⟨hn, hnd⟩, rfl⟩; exact hR n hn hnd
  calc {n : ℕ | 2 ≤ n ∧ Nat.waringNumber n ≠ 2 ^ n + waringQuot n - 2}.ncard
      ≤ dicksonHigh'.ncard := Set.ncard_le_ncard hsub hfin
    _ ≤ H * (linePoint '' dicksonHigh').ncard :=
        Set.ncard_le_mul_ncard_image hfin linePoint H hfib'
    _ ≤ H * (↑R : Set ℚ).ncard :=
        Nat.mul_le_mul (le_refl H) (Set.ncard_le_ncard himg R.finite_toSet)
    _ = H * R.card := by rw [Set.ncard_coe_finset]
    _ ≤ H * BugeaudEvertse.lineBound epsW' := Nat.mul_le_mul (le_refl H) hcard

/-! ## 4. The constant -/

/-- `1 + 1/ε_W′ ≤ 4.81894`, from `1/ε_W′ = (100001/100000)/ε*` — against `4.83382` at the old
cutoff `257`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem one_add_inv_epsW'_le : 1 + epsW'⁻¹ ≤ 4.81894 := by
  have hpos := epsStar_pos
  have hepsW : epsW' = epsStar * (100000 / 100001) := by rw [epsW']; ring
  have hinv : epsW'⁻¹ = (100001 / 100000) * epsStar⁻¹ := by
    rw [hepsW, mul_inv]
    norm_num
    ring
  have hA := one_add_inv_epsStar_le
  rw [hinv]
  linarith [hA]

@[category API, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem one_add_inv_epsW'_nonneg : (0 : ℝ) ≤ 1 + epsW'⁻¹ := by
  have := epsW'_pos
  positivity

/-- **`K(ε_W′) ≤ 1.86 · 10¹²`.**  The line count at the re-anchored Waring exponent; true value
`1 856 411 140 906`, against `1 876 339 827 243` at the cutoff `257` and
`1 856 360 182 227 = K(ε*)` at no shave at all.  The `10⁻⁵` shave costs `3·10⁻⁵` in the constant:
the Waring row is now quoted with the same three digits as the exception row. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem lineBound_epsW'_le : BugeaudEvertse.lineBound epsW' ≤ 1860000000000 := by
  rw [BugeaudEvertse.lineBound]
  refine Nat.ceil_le.mpr ?_
  have hA := one_add_inv_epsW'_le
  have hA0 := one_add_inv_epsW'_nonneg
  have hB := log_six_le
  have hB0 : (0 : ℝ) ≤ Real.log 6 := by linarith [one_le_log_six]
  have h1 : (1 : ℝ) ≤ 1 + epsW'⁻¹ := by
    have h := epsW'_pos
    have : 0 < epsW'⁻¹ := by positivity
    linarith
  have hargpos : (0 : ℝ) < (1 + epsW'⁻¹) * Real.log 6 := by nlinarith [one_le_log_six]
  have hargle : (1 + epsW'⁻¹) * Real.log 6 ≤ 8.63439 := by
    nlinarith [mul_le_mul hA hB hB0 (by norm_num : (0 : ℝ) ≤ 4.81894)]
  have hC : Real.log ((1 + epsW'⁻¹) * Real.log 6) ≤ 2.15875 := by
    refine le_trans (Real.log_le_log hargpos hargle) ?_
    rw [show (8.63439 : ℝ) = 8 * (8.63439 / 8) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8.63439 / 8 by norm_num)
    push_cast
    linarith [Real.log_two_lt_d9]
  have hC0 : (0 : ℝ) ≤ Real.log ((1 + epsW'⁻¹) * Real.log 6) := by
    refine Real.log_nonneg ?_
    nlinarith [one_le_log_six]
  push_cast
  calc (2 : ℝ) ^ 32 * (1 + epsW'⁻¹) ^ 3 * Real.log 6 * Real.log ((1 + epsW'⁻¹) * Real.log 6)
      ≤ (2 : ℝ) ^ 32 * 4.81894 ^ 3 * 1.79175947 * 2.15875 := by gcongr
    _ ≤ 1860000000000 := by norm_num

/-! ## 5. The counts in decimal form -/

/-- **`#{n ≥ 1 : ¬(Dₙ)} ≤ 2 + H · 1.86·10¹²`** — the re-anchored Dickson-failure count. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem dickson_exceptions_card_le_decimal' (H : ℕ)
    (hfib : ∀ r : ℚ, (dicksonFibre' r).ncard ≤ H) :
    {n : ℕ | 1 ≤ n ∧ ¬ DicksonCond n}.ncard ≤ 2 + H * 1860000000000 :=
  le_trans (dickson_exceptions_card_le_of_heightBound' H hfib)
    (Nat.add_le_add_left (Nat.mul_le_mul (le_refl H) lineBound_epsW'_le) 2)

/-- **`#{n ≥ 2 : g(n) ≠ 2ⁿ + ⌊(3/2)ⁿ⌋ − 2} ≤ H · 1.86·10¹²`** — the ideal Waring formula with the
re-anchored constant and no additive term, matching `BB13.failures_card_le_decimal` digit for
digit. -/
@[category research solved, AMS 11, ref "BE08" "Bug12" "Dic36", group "bugeaud_10_13"]
theorem waring_exceptions_card_le_decimal' (H : ℕ)
    (hfib : ∀ r : ℚ, (dicksonFibre' r).ncard ≤ H) :
    {n : ℕ | 2 ≤ n ∧ Nat.waringNumber n ≠ 2 ^ n + waringQuot n - 2}.ncard
      ≤ H * 1860000000000 :=
  le_trans (waring_exceptions_card_le_of_heightBound' H hfib)
    (Nat.mul_le_mul (le_refl H) lineBound_epsW'_le)

end BB13
