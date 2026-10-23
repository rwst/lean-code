/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.LineCoverSharp
import BB13.CensusCount
import BB13.DicksonSweep
import BB13.SpanStrataSharp

/-!
# Theorems A′–D′: the counts of Problem 10.13 without a cited Subspace input (WP A4)

[paper-BB13] states four theorems on the exceptions `‖(3/2)ⁿ‖ < (3/4)ⁿ` whose constant is the
line count `K(ε*) = 1 856 360 182 227` of [BE08] Cor. 5.2, a cited axiom
(`BugeaudEvertse.ridout_line_cover`). Two counts replace it, both with no cited axiom:
Subspace-Theorems' explicit two-variable count puts the exceptions `n ≥ 20` on at most
`3 870 000 000` lines (`BB13.failures_line_cover_ST_num`, WP A3), and its interval result,
counted with BB13's elementary gap `ρ₀ = 1.2618`, on at most `1 050 000 000` lines
(`BB13.failures_line_cover_rho_num`, WP A5). The same interval result at the frame's own
parameters (item M3: exact weights, Chernoff by the variance, Siegel at the exponent `999`,
Layer 5.2's pattern read per place) gives at most `N = 22 900` lines (`BB13.failures_line_cover_sharp_num`). This file re-proves the
four theorems:

* **A′** `failures_line_cover_ten_ST`: the exceptions `n ≥ 10` lie on at most `3.87·10⁹` lines
  (the generic count); **A″** `BB13.failures_line_cover_ten_rho`, `towersAbove_card_le_ten_rho`:
  on at most `1.05·10⁹` lines; **A‴** `BB13.failures_line_cover_ten_sharp`,
  `towersAbove_card_le_ten_sharp`: on at most `N` lines. The range `[10, 20)` holds no exception
  (`BB13.failures_up_to_256`).
* **B′** `failures_card_le_ST`: `#𝓔 ≤ 5 + H·N`, `H` bounding the fibres above `10⁵`.
* **C′** `waring_exceptions_card_le_ST`: at most `H·N` exceptions to the ideal Waring formula,
  `H` bounding the Dickson fibres above `10⁵`.
* **D′** `tall_towerBases_card_le_ST`: the tall-tower bases lie on at most `N` lines.

Theorem C′ needs no Waring frame of its own: **every Dickson failure `n ≥ 3` is an exception**
(`isFailure_of_notDickson`). `¬(Dₙ)` says `r + q + 1 ≥ 2ⁿ` for `3ⁿ = 2ⁿq + r`; the borderline
`r + q + 1 = 2ⁿ` would give `3ⁿ = (2ⁿ − 1)(q + 1)`, so `2ⁿ − 1` would be a power of `3`, which it
is not modulo `8`; hence `2ⁿ − r ≤ q` and `2ⁿ‖(3/2)ⁿ‖ ≤ q < 3ⁿ/2ⁿ`. This drops the exponent
`ε_W < ε*` of `BB13/Waring.lean` altogether.

Theorem D′ is the stratified count at `N`; it does not improve with the span `γ`, since the
frame system of `BB13/FrameSystem.lean` is built at `δ ≤ ε* − 1/1000` only. Even so, `N` is
below `K(ε* + 2γθ)` for every `γ` up to the saturation point `log(3/2)/log 2`.

As by-products, Mahler's finiteness for `(3/2, 3/4)` (`failures_finite_ST`) and the finiteness of
the Dickson failures (`dickson_exceptions_finite_ST`) are now std3, with no cited axiom at all.

Footprint: std3 for A′, A″, A‴, B′, D′ and the finiteness statements; std3 + `waringNumber_ideal_of_dickson`
([Dic36]) for C′.

## References

* [BE08] Bugeaud–Evertse, Acta Arith. **133** (2008), Cor. 5.2 — the count replaced here.
* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, 2012 (Prob. 10.13).
* [Dic36] L. E. Dickson, Amer. J. Math. **58** (1936) — the ideal Waring formula under `(Dₙ)`.
* `plans/plan-beyond-BB13.html`, §3.4, WPs A4, A5; §7, item M3.
-/

namespace BB13

/-! ### Theorem A′: the line count from `n ≥ 10` -/

/-- **Theorem A′.** The exceptions `‖(3/2)ⁿ‖ < (3/4)ⁿ` with `n ≥ 10` lie on at most
`3 870 000 000` lines through the origin: their slopes `linePoint n` lie in a set of at most that
many rationals. No cited axiom; `[10, 20)` holds no exception by the kernel census. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem failures_line_cover_ten_ST :
    ∃ R : Finset ℚ, R.card ≤ 3870000000 ∧
      ∀ n : ℕ, 10 ≤ n → IsFailure 3 2 (3 / 4) n → linePoint n ∈ R := by
  obtain ⟨R, hcard, hR⟩ := failures_line_cover_ST_num
  refine ⟨R, hcard, fun n hn hnf => ?_⟩
  rcases lt_or_ge n 20 with h | h
  · rcases (failures_up_to_256 n (by omega) (by omega)).1 hnf with h' | h' | h' | h' | h' <;>
      omega
  · exact hR n h hnf

/-- **Theorem A′ in counting form**: the exceptions `n ≥ 10` span at most `3 870 000 000` scaling
families (against `K(ε*) ≈ 1.86·10¹²` in `BB13.towersAbove_card_le`). -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem towersAbove_card_le_ten_ST :
    {r : ℚ | ∃ n : ℕ, 10 ≤ n ∧ IsFailure 3 2 (3 / 4) n ∧ linePoint n = r}.ncard
      ≤ 3870000000 := by
  obtain ⟨R, hcard, hR⟩ := failures_line_cover_ten_ST
  have hsub : {r : ℚ | ∃ n : ℕ, 10 ≤ n ∧ IsFailure 3 2 (3 / 4) n ∧ linePoint n = r} ⊆ ↑R := by
    rintro r ⟨n, hn, hnf, rfl⟩; exact hR n hn hnf
  calc {r : ℚ | ∃ n : ℕ, 10 ≤ n ∧ IsFailure 3 2 (3 / 4) n ∧ linePoint n = r}.ncard
      ≤ (↑R : Set ℚ).ncard := Set.ncard_le_ncard hsub R.finite_toSet
    _ = R.card := Set.ncard_coe_finset R
    _ ≤ 3870000000 := hcard

/-- **Mahler's finiteness for `(3/2, 3/4)`, std3.** The exceptions lie on finitely many lines
(`failures_line_cover_ten_rho`) and each line carries finitely many (`lineFibre_finite`); the
third proof of `BB13.failures_finite`, and the first with no cited axiom. -/
@[category research solved, AMS 11, ref "BE08" "Bug12" "Mah57", group "bugeaud_10_13"]
theorem failures_finite_ST : {n : ℕ | 1 ≤ n ∧ IsFailure 3 2 (3 / 4) n}.Finite := by
  obtain ⟨R, -, hR⟩ := failures_line_cover_ten_rho
  apply ((Set.finite_Iio 10).union
    (R.finite_toSet.biUnion (fun r _ => lineFibre_finite r))).subset
  rintro n ⟨-, hnf⟩
  rcases lt_or_ge n 10 with h | h
  · exact Or.inl h
  · exact Or.inr (Set.mem_biUnion (hR n h hnf) ⟨by omega, hnf, rfl⟩)

/-- **Theorem A″ in counting form**: the exceptions `n ≥ 10` span at most `1 050 000 000` scaling
families (`BB13.failures_line_cover_ten_rho`, the count with the elementary gap `ρ₀`). -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem towersAbove_card_le_ten_rho :
    {r : ℚ | ∃ n : ℕ, 10 ≤ n ∧ IsFailure 3 2 (3 / 4) n ∧ linePoint n = r}.ncard
      ≤ 1050000000 := by
  obtain ⟨R, hcard, hR⟩ := failures_line_cover_ten_rho
  have hsub : {r : ℚ | ∃ n : ℕ, 10 ≤ n ∧ IsFailure 3 2 (3 / 4) n ∧ linePoint n = r} ⊆ ↑R := by
    rintro r ⟨n, hn, hnf, rfl⟩; exact hR n hn hnf
  calc {r : ℚ | ∃ n : ℕ, 10 ≤ n ∧ IsFailure 3 2 (3 / 4) n ∧ linePoint n = r}.ncard
      ≤ (↑R : Set ℚ).ncard := Set.ncard_le_ncard hsub R.finite_toSet
    _ = R.card := Set.ncard_coe_finset R
    _ ≤ 1050000000 := hcard

/-- **Theorem A‴ in counting form**: the exceptions `n ≥ 10` span at most `22 900` scaling
families (`BB13.failures_line_cover_ten_sharp`, Subspace-Theorems' interval result at the frame's
own parameters, counted with the elementary gap `ρ₀`). -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem towersAbove_card_le_ten_sharp :
    {r : ℚ | ∃ n : ℕ, 10 ≤ n ∧ IsFailure 3 2 (3 / 4) n ∧ linePoint n = r}.ncard
      ≤ 22900 := by
  obtain ⟨R, hcard, hR⟩ := failures_line_cover_ten_sharp
  have hsub : {r : ℚ | ∃ n : ℕ, 10 ≤ n ∧ IsFailure 3 2 (3 / 4) n ∧ linePoint n = r} ⊆ ↑R := by
    rintro r ⟨n, hn, hnf, rfl⟩; exact hR n hn hnf
  calc {r : ℚ | ∃ n : ℕ, 10 ≤ n ∧ IsFailure 3 2 (3 / 4) n ∧ linePoint n = r}.ncard
      ≤ (↑R : Set ℚ).ncard := Set.ncard_le_ncard hsub R.finite_toSet
    _ = R.card := Set.ncard_coe_finset R
    _ ≤ 22900 := hcard

/-! ### Theorem B′: the conditional exception count -/

/-- The exceptions above the census are finite, std3. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem failuresHigh'_finite_ST : failuresHigh'.Finite :=
  failures_finite_ST.subset fun _ ⟨hn, hnf⟩ => ⟨by omega, hnf⟩

/-- **Theorem B′: `#𝓔 ≤ 5 + H · 22 900`**, for any `H` bounding the number of exceptions
`n ≥ 100001` on a single line. The `5` is the certified `𝓔 ∩ [1, 10⁵] = {1, 2, 3, 4, 7}`; the
line count is `failures_line_cover_ten_sharp`. Std3: no cited axiom. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem failures_card_le_ST (H : ℕ) (hfib : ∀ r : ℚ, (highFibre' r).ncard ≤ H) :
    {n : ℕ | 1 ≤ n ∧ IsFailure 3 2 (3 / 4) n}.ncard ≤ 5 + H * 22900 := by
  obtain ⟨R, hcard, hR⟩ := failures_line_cover_ten_sharp
  have hfin := failuresHigh'_finite_ST
  have hfib' : ∀ r : ℚ, {n ∈ failuresHigh' | linePoint n = r}.ncard ≤ H := by
    intro r
    have heq : {n ∈ failuresHigh' | linePoint n = r} = highFibre' r := by
      ext n
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
    rw [heq]; exact hfib r
  have himg : linePoint '' failuresHigh' ⊆ ↑R := by
    rintro _ ⟨n, ⟨hn, hnf⟩, rfl⟩; exact hR n (by omega) hnf
  have hhigh : failuresHigh'.ncard ≤ H * 22900 := by
    calc failuresHigh'.ncard
        ≤ H * (linePoint '' failuresHigh').ncard :=
          Set.ncard_le_mul_ncard_image hfin linePoint H hfib'
      _ ≤ H * (↑R : Set ℚ).ncard :=
          Nat.mul_le_mul (le_refl H) (Set.ncard_le_ncard himg R.finite_toSet)
      _ = H * R.card := by rw [Set.ncard_coe_finset]
      _ ≤ H * 22900 := Nat.mul_le_mul (le_refl H) hcard
  have hsub : {n : ℕ | 1 ≤ n ∧ IsFailure 3 2 (3 / 4) n} ⊆ failuresUpTo 100000 ∪ failuresHigh' := by
    rintro n ⟨h1, hf⟩
    rcases le_or_gt n 100000 with h | h
    · exact Or.inl ⟨h1, h, hf⟩
    · exact Or.inr ⟨by omega, hf⟩
  calc {n : ℕ | 1 ≤ n ∧ IsFailure 3 2 (3 / 4) n}.ncard
      ≤ (failuresUpTo 100000 ∪ failuresHigh').ncard :=
        Set.ncard_le_ncard hsub ((failuresUpTo_finite 100000).union hfin)
    _ ≤ (failuresUpTo 100000).ncard + failuresHigh'.ncard := Set.ncard_union_le _ _
    _ = 5 + failuresHigh'.ncard := by rw [failuresUpTo_100000_ncard]
    _ ≤ 5 + H * 22900 := by omega

/-! ### Theorem C′: Dickson failures are exceptions -/

/-- `3ᵏ ≡ 1` or `3 (mod 8)`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem three_pow_mod_eight (k : ℕ) : 3 ^ k % 8 = 1 ∨ 3 ^ k % 8 = 3 := by
  induction k with
  | zero => left; rfl
  | succ k ih => rw [pow_succ]; omega

/-- **Every Dickson failure `n ≥ 3` is an exception** `‖(3/2)ⁿ‖ < (3/4)ⁿ`. Write `3ⁿ = 2ⁿq + r`.
`¬(Dₙ)` is `r + q + 1 ≥ 2ⁿ`; equality would give `3ⁿ = (2ⁿ − 1)(q + 1)`, so `2ⁿ − 1 = 3ᵏ`, but
`2ⁿ − 1 ≡ 7` and `3ᵏ ≡ 1, 3 (mod 8)`. Hence `2ⁿ − r ≤ q` and `2ⁿ‖(3/2)ⁿ‖ ≤ 2ⁿq < 3ⁿ`, as `r` is
odd. Sharper than `BB13.notDickson_imp_distBound`, which loses the factor `4/3`. -/
@[category research solved, AMS 11, ref "Bug12" "Dic36", group "bugeaud_10_13"]
theorem isFailure_of_notDickson {n : ℕ} (hn : 3 ≤ n) (hnd : ¬ DicksonCond n) :
    IsFailure 3 2 (3 / 4) n := by
  rw [isFailure_iff_failNat]
  have h8 : 8 ∣ 2 ^ n := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num]; exact Nat.pow_dvd_pow 2 hn
  have hodd : 3 ^ n % 2 ^ n % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega : n ≠ 0)), Nat.pow_mod]; norm_num
  have hdiv := Nat.div_add_mod (3 ^ n) (2 ^ n)
  have hone : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  simp only [DicksonCond, waringQuot] at hnd
  have hres : residNat n ≤ 2 ^ n - 3 ^ n % 2 ^ n := min_le_right _ _
  have hne : 3 ^ n % 2 ^ n + 3 ^ n / 2 ^ n + 1 ≠ 2 ^ n := by
    intro heq
    have hfac : (2 ^ n - 1) * (3 ^ n / 2 ^ n + 1) = 3 ^ n := by
      zify [hone] at heq hdiv ⊢
      linear_combination hdiv - heq
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (Dvd.intro _ hfac)
    have := three_pow_mod_eight k
    omega
  have hq : residNat n ≤ 3 ^ n / 2 ^ n := by omega
  have hpos : 0 < 3 ^ n % 2 ^ n := by omega
  calc 2 ^ n * residNat n ≤ 2 ^ n * (3 ^ n / 2 ^ n) := Nat.mul_le_mul_left _ hq
    _ < 2 ^ n * (3 ^ n / 2 ^ n) + 3 ^ n % 2 ^ n := Nat.lt_add_of_pos_right hpos
    _ = 3 ^ n := hdiv

/-- A Dickson fibre above the census is contained in the exception fibre: one per-line bound `H`
serves Theorems B′ and C′ together. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem dicksonFibre'_subset_highFibre' (r : ℚ) : dicksonFibre' r ⊆ highFibre' r := by
  rintro n ⟨hn, hnd, hr⟩; exact ⟨hn, isFailure_of_notDickson (by omega) hnd, hr⟩

/-- **The Waring line cover from Theorem A‴**: the Dickson failures `n ≥ 10` lie on at most
`22 900` lines (against `K(ε_W) ≈ 1.88·10¹²` in `BB13.notDickson_line_cover`). -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem notDickson_line_cover_ST :
    ∃ R : Finset ℚ, R.card ≤ 22900 ∧
      ∀ n : ℕ, 10 ≤ n → ¬ DicksonCond n → linePoint n ∈ R := by
  obtain ⟨R, hcard, hR⟩ := failures_line_cover_ten_sharp
  exact ⟨R, hcard, fun n hn hnd => hR n hn (isFailure_of_notDickson (by omega) hnd)⟩

/-- **The Dickson failures are finite, std3.** -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem dickson_exceptions_finite_ST : {n : ℕ | 1 ≤ n ∧ ¬ DicksonCond n}.Finite := by
  apply ((Set.finite_Iio 3).union failures_finite_ST).subset
  rintro n ⟨h1, hnd⟩
  rcases lt_or_ge n 3 with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h1, isFailure_of_notDickson h hnd⟩

/-- **`#{n ≥ 1 : ¬(Dₙ)} ≤ 2 + H · 22 900`**, for any `H` bounding the Dickson failures
`n ≥ 100001` on a single line. The `2` is `n = 1, 2`. Std3. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem dickson_exceptions_card_le_ST (H : ℕ) (hfib : ∀ r : ℚ, (dicksonFibre' r).ncard ≤ H) :
    {n : ℕ | 1 ≤ n ∧ ¬ DicksonCond n}.ncard ≤ 2 + H * 22900 := by
  obtain ⟨R, hcard, hR⟩ := notDickson_line_cover_ST
  have hfin : dicksonHigh'.Finite :=
    dickson_exceptions_finite_ST.subset fun _ ⟨hn, hnd⟩ => ⟨by omega, hnd⟩
  have hfib' : ∀ r : ℚ, {n ∈ dicksonHigh' | linePoint n = r}.ncard ≤ H := by
    intro r
    have heq : {n ∈ dicksonHigh' | linePoint n = r} = dicksonFibre' r := by
      ext n
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
    rw [heq]; exact hfib r
  have himg : linePoint '' dicksonHigh' ⊆ ↑R := by
    rintro _ ⟨n, ⟨hn, hnd⟩, rfl⟩; exact hR n (by omega) hnd
  have hhigh : dicksonHigh'.ncard ≤ H * 22900 := by
    calc dicksonHigh'.ncard
        ≤ H * (linePoint '' dicksonHigh').ncard :=
          Set.ncard_le_mul_ncard_image hfin linePoint H hfib'
      _ ≤ H * (↑R : Set ℚ).ncard :=
          Nat.mul_le_mul (le_refl H) (Set.ncard_le_ncard himg R.finite_toSet)
      _ = H * R.card := by rw [Set.ncard_coe_finset]
      _ ≤ H * 22900 := Nat.mul_le_mul (le_refl H) hcard
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
    _ ≤ 2 + H * 22900 := by
        have h2 : ({1, 2} : Set ℕ).ncard = 2 := Set.ncard_pair (by norm_num)
        omega

/-- **Theorem C′: `#{n ≥ 2 : g(n) ≠ 2ⁿ + ⌊(3/2)ⁿ⌋ − 2} ≤ H · 22 900`**, with no additive
constant, for any `H` bounding the Dickson failures `n ≥ 100001` on a single line (in particular
for the `H` of Theorem B′, by `dicksonFibre'_subset_highFibre'`). Every exception fails `(Dₙ)`,
the sweep clears `[3, 10⁵]`, and `n = 2` satisfies the formula. Footprint std3 +
`waringNumber_ideal_of_dickson`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12" "Dic36", group "bugeaud_10_13"]
theorem waring_exceptions_card_le_ST (H : ℕ) (hfib : ∀ r : ℚ, (dicksonFibre' r).ncard ≤ H) :
    {n : ℕ | 2 ≤ n ∧ Nat.waringNumber n ≠ 2 ^ n + waringQuot n - 2}.ncard
      ≤ H * 22900 := by
  obtain ⟨R, hcard, hR⟩ := notDickson_line_cover_ST
  have hfin : dicksonHigh'.Finite :=
    dickson_exceptions_finite_ST.subset fun _ ⟨hn, hnd⟩ => ⟨by omega, hnd⟩
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
    rintro _ ⟨n, ⟨hn, hnd⟩, rfl⟩; exact hR n (by omega) hnd
  calc {n : ℕ | 2 ≤ n ∧ Nat.waringNumber n ≠ 2 ^ n + waringQuot n - 2}.ncard
      ≤ dicksonHigh'.ncard := Set.ncard_le_ncard hsub hfin
    _ ≤ H * (linePoint '' dicksonHigh').ncard :=
        Set.ncard_le_mul_ncard_image hfin linePoint H hfib'
    _ ≤ H * (↑R : Set ℚ).ncard :=
        Nat.mul_le_mul (le_refl H) (Set.ncard_le_ncard himg R.finite_toSet)
    _ = H * R.card := by rw [Set.ncard_coe_finset]
    _ ≤ H * 22900 := Nat.mul_le_mul (le_refl H) hcard

/-! ### Theorem D′: the tall towers -/

/-- **Theorem D′.** For every `γ`, the bases `a ≥ 10` of relation-towers of span at least `γ·a`
lie on at most `22 900` lines (against `K(ε* + γθ)`, `≤ 5.38·10¹¹` at `γ = 1/4`, in
`BB13.tall_towerBases_card_le_decimal`). The base is an exception, so this is a subset of
Theorem A‴'s lines. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem tall_towerBases_card_le_ST (γ : ℝ) :
    {r : ℚ | ∃ a b : ℕ, 10 ≤ a ∧ a < b ∧ IsFailure 3 2 (3 / 4) a ∧ SameTower a b ∧
      γ * (a : ℝ) ≤ ((b - a : ℕ) : ℝ) ∧ linePoint a = r}.ncard ≤ 22900 := by
  refine le_trans (Set.ncard_le_ncard ?_ ?_) towersAbove_card_le_ten_sharp
  · rintro r ⟨a, -, ha, -, hfa, -, -, rfl⟩; exact ⟨a, ha, hfa, rfl⟩
  · obtain ⟨R, -, hR⟩ := failures_line_cover_ten_sharp
    exact R.finite_toSet.subset fun r ⟨n, hn, hnf, hr⟩ => hr ▸ hR n hn hnf

/-- **Theorem D′, sharp form.** The bases `a ≥ 10` of relation-towers of span at least `γ·a`
topped by an exception lie on at most `22 900` lines (against `K(ε* + 2γθ)`, `≤ 2.5·10¹¹`
at `γ = 1/4`). The base inherits the failure (`isFailure_of_sameTower_failure`). -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem tall_exception_towerBases_card_le_ST (γ : ℝ) :
    {r : ℚ | ∃ a b : ℕ, 10 ≤ a ∧ a < b ∧ IsFailure 3 2 (3 / 4) b ∧ SameTower a b ∧
      γ * (a : ℝ) ≤ ((b - a : ℕ) : ℝ) ∧ linePoint a = r}.ncard ≤ 22900 := by
  refine le_trans (Set.ncard_le_ncard ?_ ?_) towersAbove_card_le_ten_sharp
  · rintro r ⟨a, b, ha, hab, hfb, hsame, -, rfl⟩
    exact ⟨a, ha, isFailure_of_sameTower_failure hab hfb hsame, rfl⟩
  · obtain ⟨R, -, hR⟩ := failures_line_cover_ten_sharp
    exact R.finite_toSet.subset fun r ⟨n, hn, hnf, hr⟩ => hr ▸ hR n hn hnf

end BB13
