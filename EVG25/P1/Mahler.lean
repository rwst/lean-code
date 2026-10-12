/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Bugeaud.Chapter3.ParityIdentity
import EVG25.UniformCorrespondence

/-!
# Simple normality of `U`-words kills Mahler's Z-numbers (Theorem A of the P1 paper)

Plan EVGQ17-M0, §7.4, milestone C1.  A **Z-number** (Mahler 1968) is a real `ξ > 0` with
`{ξ (3/2)ⁿ} < 1/2` for all `n` (`Bugeaud.IsZNumber`).  We show:

* `U_add_one`, `U_iter_add_one` — **F1**: `U(n) + 1 = V(n+1)` with `V(m) = ⌈3m/2⌉`, so `U`-orbits are
  Mahler / Josephus orbits shifted by one;
* `floor_eq_U_iter` — the floor orbit `xₙ = ⌊ξ (3/2)ⁿ⌋` of a Z-number is `U^n(a) + 1`, where
  `a = ⌊ξ⌋ - 1` (`zSeed ξ`); in particular `⌊ξ⌋ ≥ 1`;
* `not_one_one`, `zeros_after_one_zero_one` — the **gap lemma**: the parity word of a Z-number has
  no factor `11`, and `101` is always followed by `00000`.  In `U`-word terms (letter `1` = odd
  iterate) the first statement is Mahler's criterion: the `U`-word of `a` has no factor `22`;
* `three_mul_count_le` — a word with both gap properties has at most `(k+4)/3` ones in every window
  of length `k`;
* `two_mul_le_three_mul_numOddU` — hence `3·S_k(a) + 4 ≥ 2k` for the seed `a` of any Z-number: its
  `U`-word has lower odd-density `≥ 2/3`;
* `not_isZNumber_of_U_orbit_density`, `no_Z_numbers_of_conjecture_U_orbit_density` —
  **Theorem A**: if the `U`-orbit of `a` has odd-density `1/2` (EVG25 Question 17 at one seed),
  there is no Z-number in `[a+1, a+2)`; so a positive answer to Question 17 implies Mahler's
  conjecture.

The `β = 3/2` description of Z-number itineraries is Flatto's [Fla92]; the step taken here is that
the gap lemma caps the frequency of the digit at `1/3`, so *simple* normality (letter density
`1/2`) already excludes Z-numbers.  Andrieu–Eliahou–Vivion (Thm 1.5) need full normality, used only
to produce one factor `22`.  The gap lemma is proved directly from the step
`2{ξ(3/2)ⁿ⁺¹} = 3{ξ(3/2)ⁿ} - εₙ` (`Bugeaud.three_zFrac`), without Parry's admissibility criterion.
-/

open Filter Topology Finset CC CC.Base3div2

namespace EVG25.P1

/-! ## F1: `U`-orbits are `⌈3x/2⌉`-orbits -/

/-- Mahler's map `V(m) = ⌈3m/2⌉`, written in `ℕ`. -/
def V (m : ℕ) : ℕ := (3 * m + 1) / 2

theorem two_mul_U (m : ℕ) : 2 * U m = 3 * m + 2 - m % 2 := by
  unfold U; split <;> omega

/-- **F1.** `U(n) + 1 = V(n + 1)`. -/
@[category API, AMS 11 37, ref "EVG25", group "evgq17_p1"]
theorem U_add_one (n : ℕ) : U n + 1 = V (n + 1) := by
  unfold U V; split <;> omega

/-- **F1, iterated.** `U^k(n) + 1 = V^k(n + 1)`. -/
@[category API, AMS 11 37, ref "EVG25", group "evgq17_p1"]
theorem U_iter_add_one (k n : ℕ) : U_iter k n + 1 = V^[k] (n + 1) := by
  induction k with
  | zero => simp [U_iter]
  | succ k ih => rw [U_iter_succ, U_add_one, ih, Function.iterate_succ_apply']

/-! ## The floor orbit of a Z-number -/

variable {ξ : ℝ}

/-- The integer parts `xₙ = ⌊ξ (3/2)ⁿ⌋`. -/
noncomputable def zFloor (ξ : ℝ) (n : ℕ) : ℤ := ⌊ξ * (3 / 2) ^ n⌋

theorem zFloor_nonneg (hξ : Bugeaud.IsZNumber ξ) (n : ℕ) : 0 ≤ zFloor ξ n :=
  Int.floor_nonneg.2 (mul_nonneg hξ.1.le (pow_nonneg (by norm_num) n))

theorem zFloor_step (hξ : Bugeaud.IsZNumber ξ) (n : ℕ) :
    2 * zFloor ξ (n + 1) = 3 * zFloor ξ n + zFloor ξ n % 2 :=
  Bugeaud.floor_step hξ n

/-- A Z-number is at least `1`: otherwise its floor orbit would stay at `0`, while
`ξ (3/2)ⁿ → ∞`. -/
theorem one_le_zFloor_zero (hξ : Bugeaud.IsZNumber ξ) : 1 ≤ zFloor ξ 0 := by
  by_contra h
  have h0 : ∀ n, zFloor ξ n = 0 := by
    intro n
    induction n with
    | zero => have := zFloor_nonneg hξ 0; omega
    | succ n ih => have := zFloor_step hξ n; rw [ih] at this; omega
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / ξ) (by norm_num : (1 : ℝ) < 3 / 2)
  have h1 : 1 ≤ ξ * (3 / 2) ^ n := by
    have := (div_lt_iff₀ hξ.1).1 hn
    linarith [mul_comm ξ ((3 / 2 : ℝ) ^ n)]
  have : (1 : ℤ) ≤ zFloor ξ n := Int.le_floor.2 (by simpa using h1)
  rw [h0 n] at this
  omega

/-- The seed of a Z-number: `a = ⌊ξ⌋ - 1`. -/
noncomputable def zSeed (ξ : ℝ) : ℕ := (zFloor ξ 0).toNat - 1

/-- The floor orbit of a Z-number is the `U`-orbit of its seed, shifted by one
(equivalently, by F1, the `V`-orbit of `⌊ξ⌋`). -/
@[category API, AMS 11 37, ref "Mahler68" "Bug12", group "evgq17_p1"]
theorem floor_eq_U_iter (hξ : Bugeaud.IsZNumber ξ) (n : ℕ) :
    (U_iter n (zSeed ξ) : ℤ) + 1 = zFloor ξ n := by
  induction n with
  | zero =>
    have := one_le_zFloor_zero hξ
    simp only [U_iter, zSeed]
    omega
  | succ n ih =>
    have hs := zFloor_step hξ n
    have hU := two_mul_U (U_iter n (zSeed ξ))
    rw [U_iter_succ]
    omega

/-- A letter of the seed's `U`-word is odd exactly when the integer part is even. -/
theorem U_iter_odd_iff (hξ : Bugeaud.IsZNumber ξ) (n : ℕ) :
    U_iter n (zSeed ξ) % 2 = 1 ↔ Bugeaud.zParity ξ n = 0 := by
  have h := floor_eq_U_iter hξ n
  unfold Bugeaud.zParity
  change _ ↔ zFloor ξ n % 2 = 0
  omega

/-! ## The gap lemma -/

/-- The fractional parts `fₙ = {ξ (3/2)ⁿ}`. -/
noncomputable def zFrac (ξ : ℝ) (n : ℕ) : ℝ := Int.fract (ξ * (3 / 2) ^ n)

theorem zFrac_nonneg (n : ℕ) : 0 ≤ zFrac ξ n := Int.fract_nonneg _

theorem zFrac_lt (hξ : Bugeaud.IsZNumber ξ) (n : ℕ) : zFrac ξ n < 1 / 2 := hξ.2 n

theorem zFrac_step (hξ : Bugeaud.IsZNumber ξ) (n : ℕ) :
    3 * zFrac ξ n = (Bugeaud.zParity ξ n : ℝ) + 2 * zFrac ξ (n + 1) :=
  Bugeaud.three_zFrac hξ n

theorem zFrac_succ_of_zero (hξ : Bugeaud.IsZNumber ξ) {n : ℕ} (h : Bugeaud.zParity ξ n = 0) :
    zFrac ξ (n + 1) = 3 / 2 * zFrac ξ n := by
  have := zFrac_step hξ n; rw [h] at this; push_cast at this; linarith

theorem zFrac_succ_of_one (hξ : Bugeaud.IsZNumber ξ) {n : ℕ} (h : Bugeaud.zParity ξ n = 1) :
    zFrac ξ (n + 1) = 3 / 2 * zFrac ξ n - 1 / 2 := by
  have := zFrac_step hξ n; rw [h] at this; push_cast at this; linarith

/-- The digit `1` needs `fₙ ≥ 1/3`. -/
theorem third_le_of_one (hξ : Bugeaud.IsZNumber ξ) {n : ℕ} (h : Bugeaud.zParity ξ n = 1) :
    1 / 3 ≤ zFrac ξ n := by
  have := zFrac_succ_of_one hξ h; have := zFrac_nonneg (ξ := ξ) (n + 1); linarith

theorem zero_of_lt_third (hξ : Bugeaud.IsZNumber ξ) {n : ℕ} (h : zFrac ξ n < 1 / 3) :
    Bugeaud.zParity ξ n = 0 := by
  rcases Bugeaud.zParity_eq_zero_or_one ξ n with h0 | h1
  · exact h0
  · exact absurd (third_le_of_one hξ h1) (not_le.2 h)

/-- **Gap lemma (i).** No factor `11` in the parity word of a Z-number.  In `U`-word terms: no two
consecutive even iterates, i.e. no factor `22` (Mahler's criterion). -/
@[category API, AMS 11 37, ref "Mahler68" "Fla92", group "evgq17_p1"]
theorem not_one_one (hξ : Bugeaud.IsZNumber ξ) (n : ℕ) :
    ¬ (Bugeaud.zParity ξ n = 1 ∧ Bugeaud.zParity ξ (n + 1) = 1) := by
  rintro ⟨h0, h1⟩
  have := zFrac_succ_of_one hξ h0
  have := third_le_of_one hξ h1
  have := zFrac_lt hξ n
  linarith

/-- **Gap lemma (ii).** `101` in the parity word of a Z-number is followed by `00000`. -/
@[category API, AMS 11 37, ref "Fla92", group "evgq17_p1"]
theorem zeros_after_one_zero_one (hξ : Bugeaud.IsZNumber ξ) {n : ℕ}
    (h0 : Bugeaud.zParity ξ n = 1) (h1 : Bugeaud.zParity ξ (n + 1) = 0)
    (h2 : Bugeaud.zParity ξ (n + 2) = 1) :
    ∀ i, 3 ≤ i → i < 8 → Bugeaud.zParity ξ (n + i) = 0 := by
  have e1 := zFrac_succ_of_one hξ h0
  have e2 := zFrac_succ_of_zero hξ h1
  have e3 := zFrac_succ_of_one hξ h2
  have hlt := zFrac_lt hξ n
  -- `f_{n+3} < 1/16`, and the next four steps multiply by `3/2` while below `1/3`
  have f3 : zFrac ξ (n + 3) < 1 / 16 := by
    rw [show n + 3 = n + 2 + 1 by ring, e3, show n + 2 = n + 1 + 1 by ring, e2, e1]; linarith
  have z3 := zero_of_lt_third hξ (n := n + 3) (by linarith)
  have f4 : zFrac ξ (n + 4) < 3 / 32 := by
    rw [show n + 4 = n + 3 + 1 by ring, zFrac_succ_of_zero hξ z3]; linarith
  have z4 := zero_of_lt_third hξ (n := n + 4) (by linarith)
  have f5 : zFrac ξ (n + 5) < 9 / 64 := by
    rw [show n + 5 = n + 4 + 1 by ring, zFrac_succ_of_zero hξ z4]; linarith
  have z5 := zero_of_lt_third hξ (n := n + 5) (by linarith)
  have f6 : zFrac ξ (n + 6) < 27 / 128 := by
    rw [show n + 6 = n + 5 + 1 by ring, zFrac_succ_of_zero hξ z5]; linarith
  have z6 := zero_of_lt_third hξ (n := n + 6) (by linarith)
  have f7 : zFrac ξ (n + 7) < 81 / 256 := by
    rw [show n + 7 = n + 6 + 1 by ring, zFrac_succ_of_zero hξ z6]; linarith
  have z7 := zero_of_lt_third hξ (n := n + 7) (by linarith)
  intro i hi3 hi8
  interval_cases i <;> assumption

/-! ## Counting: the gap lemma caps the frequency of `1` at `1/3` -/

/-- Number of `n + i`, `i < k`, satisfying `P`. -/
def cnt (P : ℕ → Prop) [DecidablePred P] (n k : ℕ) : ℕ :=
  ∑ i ∈ range k, if P (n + i) then 1 else 0

variable {P : ℕ → Prop} [DecidablePred P]

theorem cnt_add (n j k : ℕ) : cnt P n (j + k) = cnt P n j + cnt P (n + j) k := by
  unfold cnt; rw [sum_range_add]; simp only [add_assoc]

theorem cnt_le_length (n k : ℕ) : cnt P n k ≤ k := by
  unfold cnt
  calc ∑ i ∈ range k, (if P (n + i) then 1 else 0) ≤ ∑ _i ∈ range k, 1 :=
        sum_le_sum fun i _ => by split <;> omega
    _ = k := by simp

theorem cnt_one (n : ℕ) : cnt P n 1 = if P n then 1 else 0 := by
  simp only [cnt, sum_range_one, add_zero]

theorem cnt_mono (n : ℕ) {j k : ℕ} (h : j ≤ k) : cnt P n j ≤ cnt P n k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [cnt_add]; omega

/-- **Counting lemma.** If `P` has no factor `11` and every `101` is followed by `00000`, then every
window of length `k` contains at most `(k+4)/3` positions of `P`. -/
@[category API, AMS 68, group "evgq17_p1"]
theorem three_mul_count_le (h11 : ∀ n, ¬ (P n ∧ P (n + 1)))
    (h101 : ∀ n, P n → ¬ P (n + 1) → P (n + 2) → ∀ i, 3 ≤ i → i < 8 → ¬ P (n + i)) :
    ∀ k n, 3 * cnt P n k ≤ k + 4 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro n
  rcases Nat.lt_or_ge k 3 with hk | hk
  · -- at most one position in a window of length `≤ 2`
    have : cnt P n k ≤ 1 := by
      interval_cases k
      · simp [cnt]
      · simp only [cnt_one]; split <;> omega
      · rw [show (2 : ℕ) = 1 + 1 from rfl, cnt_add, cnt_one, cnt_one]
        have := h11 n
        by_cases a : P n <;> by_cases b : P (n + 1) <;> simp_all
    omega
  by_cases p0 : P n
  · have p1 : ¬ P (n + 1) := fun h => h11 n ⟨p0, h⟩
    have hsplit3 := cnt_add (P := P) n 3 (k - 3)
    rw [show 3 + (k - 3) = k by omega] at hsplit3
    by_cases p2 : P (n + 2)
    · have hz := h101 n p0 p1 p2
      have c8 : cnt P n 8 = 2 := by
        simp only [cnt, sum_range_succ, sum_range_zero, add_zero, p0, p1, p2,
          hz 3 (by norm_num) (by norm_num), hz 4 (by norm_num) (by norm_num),
          hz 5 (by norm_num) (by norm_num), hz 6 (by norm_num) (by norm_num),
          hz 7 (by norm_num) (by norm_num), ite_true, ite_false]
      rcases Nat.lt_or_ge k 8 with hk8 | hk8
      · have := cnt_mono (P := P) n hk8.le; omega
      · have h8 := cnt_add (P := P) n 8 (k - 8)
        rw [show 8 + (k - 8) = k by omega] at h8
        have := ih (k - 8) (by omega) (n + 8)
        omega
    · have c3 : cnt P n 3 = 1 := by
        simp only [cnt, sum_range_succ, sum_range_zero, add_zero, p0, p1, p2, ite_true, ite_false]
      have := ih (k - 3) (by omega) (n + 3)
      omega
  · have h1 := cnt_add (P := P) n 1 (k - 1)
    rw [show 1 + (k - 1) = k by omega, cnt_one] at h1
    simp only [p0, ite_false] at h1
    have := ih (k - 1) (by omega) (n + 1)
    omega

/-! ## Theorem A -/

/-- **The seed of a Z-number is heavily odd.**  For a Z-number `ξ` with seed `a = ⌊ξ⌋ - 1`, the
first `k` letters of the `U`-word of `a` contain at least `(2k - 4)/3` odd iterates: lower
odd-density `≥ 2/3`. -/
@[category research solved, AMS 11 37, ref "Fla92" "Mahler68", group "evgq17_p1"]
theorem two_mul_le_three_mul_numOddU (hξ : Bugeaud.IsZNumber ξ) (k : ℕ) :
    2 * k ≤ 3 * numOddU k (zSeed ξ) + 4 := by
  classical
  have hc := three_mul_count_le (P := fun n => Bugeaud.zParity ξ n = 1)
    (fun n => not_one_one hξ n)
    (fun n h0 h1 h2 i hi hi' => by
      have h1' : Bugeaud.zParity ξ (n + 1) = 0 := by
        rcases Bugeaud.zParity_eq_zero_or_one ξ (n + 1) with h | h
        · exact h
        · exact absurd h h1
      rw [zeros_after_one_zero_one hξ h0 h1' h2 i hi hi']; norm_num) k 0
  have hsum : numOddU k (zSeed ξ) + cnt (fun n => Bugeaud.zParity ξ n = 1) 0 k = k := by
    unfold numOddU cnt
    rw [card_filter, ← sum_add_distrib]
    rw [show k = ∑ _i ∈ range k, 1 by simp]
    refine sum_congr (by simp) fun i _ => ?_
    simp only [zero_add]
    have := U_iter_odd_iff hξ i
    rcases Bugeaud.zParity_eq_zero_or_one ξ i with h | h <;> simp_all
  omega

/-- **Theorem A (one seed).** If the `U`-orbit of `a` has odd-density `1/2`, there is no Z-number
with seed `a`, i.e. none in `[a + 1, a + 2)`. -/
@[category research solved, AMS 11 37, ref "Fla92" "Mahler68" "EVG25", group "evgq17_p1"]
theorem not_isZNumber_of_U_orbit_density (hξ : Bugeaud.IsZNumber ξ) :
    ¬ U_orbit_density (zSeed ξ) := by
  intro hX
  have hev : ∀ᶠ k : ℕ in atTop, (11 / 18 : ℚ) ≤ (numOddU k (zSeed ξ) : ℚ) / k := by
    filter_upwards [eventually_ge_atTop 24] with k hk
    have h := two_mul_le_three_mul_numOddU hξ k
    have hk0 : (0 : ℚ) < k := by exact_mod_cast (show 0 < k by omega)
    rw [le_div_iff₀ hk0]
    have hq : (2 * k : ℚ) ≤ 3 * numOddU k (zSeed ξ) + 4 := by exact_mod_cast h
    have hk24 : (24 : ℚ) ≤ k := by exact_mod_cast hk
    linarith
  have := ge_of_tendsto hX hev
  norm_num at this

/-- **Theorem A.** A positive answer to EVG25 Question 17 (every `U`-orbit has odd-density `1/2`)
implies Mahler's conjecture: there are no Z-numbers. -/
@[category research solved, AMS 11 37, ref "Fla92" "Mahler68" "EVG25", group "evgq17_p1"]
theorem no_Z_numbers_of_conjecture_U_orbit_density (hX : conjecture_U_orbit_density) :
    ∀ ξ : ℝ, ¬ Bugeaud.IsZNumber ξ :=
  fun _ hξ => not_isZNumber_of_U_orbit_density hξ (hX _)

end EVG25.P1
