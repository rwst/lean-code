import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

open Nat

/-!
Define $\varsigma(n)$ the smallest prime factor of $n$ (`Nat.minFac`). Let $a_n$ be the least
number such that the count of numbers $k \le a_n$ with $k > \varsigma(k)^n$ exceeds the count
of numbers with $k \le \varsigma(k)^n$.

The conjecture states that $a_n = 3^n + 3 \cdot 2^n + 6$ for $n \ge 1$.

*References:* [oeis.org/A087719](https://oeis.org/A087719)
-/

public section

/-- Count of numbers k in {1, ..., m} where k > (minFac k)^n. -/
def countExceeding (n m : ℕ) : ℕ :=
  (Finset.Icc 1 m).filter (fun k => k > k.minFac ^ n) |>.card

/-- Count of numbers k in {1, ..., m} where k ≤ (minFac k)^n. -/
def countNotExceeding (n m : ℕ) : ℕ :=
  (Finset.Icc 1 m).filter (fun k => k ≤ k.minFac ^ n) |>.card

/-- There exists m such that countExceeding n m > countNotExceeding n m. -/
theorem a_exists (n : ℕ) : ∃ m, countExceeding n m > countNotExceeding n m := by
  -- Choose a sufficiently large witness. m = 12 * 4^n is convenient.
  let m := 12 * 4^n
  use m

  -- We define two disjoint subsets of the numbers satisfying the condition.
  -- 1. Even numbers strictly greater than 2^n
  let S_even := (Finset.Icc 1 m).filter (fun k => 2 ∣ k ∧ k > 2^n)
  -- 2. Odd multiples of 3 strictly greater than 3^n
  let S_odd3 := (Finset.Icc 1 m).filter (fun k => 3 ∣ k ∧ ¬2 ∣ k ∧ k > 3^n)

  -- Helper: S_even and S_odd3 satisfy the exceeding condition
  have h_subset : S_even ∪ S_odd3 ⊆ (Finset.Icc 1 m).filter (fun k => k > k.minFac ^ n) := by
    intro k hk
    rw [Finset.mem_union] at hk
    rw [Finset.mem_filter]
    cases hk with
    | inl h_even =>
      -- Case: k is even and > 2^n
      rw [Finset.mem_filter] at h_even
      exact ⟨h_even.1, by rw [(Nat.minFac_eq_two_iff k).mpr h_even.2.1]; exact h_even.2.2⟩
    | inr h_odd3 =>
      -- Case: k is odd multiple of 3 and > 3^n
      rw [Finset.mem_filter] at h_odd3
      refine ⟨h_odd3.1, ?_⟩
      have h_k_ne_1 : k ≠ 1 := by
        intro h
        rw [h] at h_odd3
        simp at h_odd3
      have h_minfac : k.minFac = 3 := by
        -- k is divisible by 3 and not by 2
        have h_minFac_le : k.minFac ≤ 3 := Nat.minFac_le_of_dvd (by omega) h_odd3.2.1
        have h_minFac_ne_2 : k.minFac ≠ 2 := by
          intro h
          have : 2 ∣ k := (Nat.minFac_eq_two_iff k).mp h
          exact h_odd3.2.2.1 this
        have h_minFac_prime : k.minFac.Prime := Nat.minFac_prime h_k_ne_1
        have h_minFac_gt_1 : 1 < k.minFac := h_minFac_prime.one_lt
        omega
      rw [h_minfac]
      exact h_odd3.2.2.2

  -- Helper: S_even and S_odd3 are disjoint
  have h_disjoint : Disjoint S_even S_odd3 := by
    rw [Finset.disjoint_left]
    intro a ha hb
    -- a is even and not even - contradiction
    rw [Finset.mem_filter] at ha hb
    exact hb.2.2.1 ha.2.1

  -- Calculate/Bound cardinalities
  -- 1. |S_even| >= m/2 - 2^n
  have h_card_even : S_even.card ≥ m / 2 - 2^n := by
    -- Count of evens in 1..m is exactly m/2
    let Evens := (Finset.Icc 1 m).filter (fun k => 2 ∣ k)
    have h_evens_card : Evens.card = m / 2 := by
      have h_m_half : m / 2 = 6 * 4^n := by show 12 * 4^n / 2 = 6 * 4^n; omega
      have hm_eq : m = 12 * 4^n := rfl
      have hbij : Evens = (Finset.Icc 1 (m / 2)).map ⟨(2 * ·), mul_right_injective₀ (by omega : (2 : ℕ) ≠ 0)⟩ := by
        ext x
        rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_map]
        constructor
        · intro ⟨⟨h1, h2⟩, hdiv⟩
          obtain ⟨k, rfl⟩ := hdiv
          refine ⟨k, ?_, rfl⟩
          rw [Finset.mem_Icc, h_m_half]
          exact ⟨by omega, by have hk_bound : 2 * k ≤ m := h2; rw [hm_eq] at hk_bound; linarith⟩
        · intro ⟨k, hk, hx⟩
          rw [Finset.mem_Icc, h_m_half] at hk
          simp only [Function.Embedding.coeFn_mk] at hx
          subst hx
          exact ⟨⟨by omega, by rw [hm_eq]; linarith⟩, ⟨k, rfl⟩⟩
      rw [hbij, Finset.card_map, Nat.card_Icc, h_m_half]
      omega

    -- S_even = Evens \ {k <= 2^n}
    -- We use a loose bound: |Evens \ S_even| <= 2^n
    have h_diff : Evens.card - S_even.card ≤ 2^n := by
      -- Evens \ S_even = evens with k <= 2^n
      have hdiff_eq : Evens \ S_even = (Finset.Icc 1 m).filter (fun k => 2 ∣ k ∧ k ≤ 2^n) := by
        ext x
        rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
        simp only [not_and, not_lt]
        exact ⟨fun ⟨⟨hx_mem, hdiv⟩, hnot⟩ => ⟨hx_mem, hdiv, hnot hx_mem hdiv⟩,
               fun ⟨hx_mem, hdiv, hle⟩ => ⟨⟨hx_mem, hdiv⟩, fun _ _ => hle⟩⟩
      -- Bound: |Evens \ S_even| <= |Icc 1 (2^n)| = 2^n
      have hbound : (Evens \ S_even).card ≤ 2^n := by
        rw [hdiff_eq]
        calc ((Finset.Icc 1 m).filter (fun k => 2 ∣ k ∧ k ≤ 2^n)).card
            ≤ (Finset.Icc 1 (2^n)).card := by
              apply Finset.card_le_card
              intro x hx
              rw [Finset.mem_filter, Finset.mem_Icc] at hx
              rw [Finset.mem_Icc]
              exact ⟨hx.1.1, hx.2.2⟩
          _ = 2^n := by
              rw [Nat.card_Icc]
              have h : 0 < 2^n := pow_pos (by omega : (0 : ℕ) < 2) n
              omega
      -- |Evens| - |S_even| = |Evens \ S_even| (since S_even ⊆ Evens)
      have hcard_eq : Evens.card - S_even.card = (Evens \ S_even).card := by
        have hsubset : S_even ⊆ Evens := fun x hx => by
          rw [Finset.mem_filter] at hx ⊢
          exact ⟨hx.1, hx.2.1⟩
        have hi : S_even ∩ Evens = S_even := Finset.inter_eq_left.mpr hsubset
        rw [Finset.card_sdiff, hi]
      omega

    -- Arithmetic manipulation
    omega

  -- 2. |S_odd3| >= m/6 - 3^n
  have h_card_odd3 : S_odd3.card ≥ m / 6 - 3^n := by
    -- Count of odd multiples of 3 is m/6
    let Odd3s := (Finset.Icc 1 m).filter (fun k => 3 ∣ k ∧ ¬2 ∣ k)
    have h_odd3s_card : Odd3s.card = m / 6 := by
      have h_m_sixth : m / 6 = 2 * 4^n := by show 12 * 4^n / 6 = 2 * 4^n; omega
      have hm_eq : m = 12 * 4^n := rfl
      -- Odd multiples of 3 in [1, m] are 3, 9, 15, ..., m-3
      -- Bijection: k ∈ [1, m/6] ↔ 6k - 3 ∈ Odd3s
      have hinj : Function.Injective (fun k : ℕ => 6 * k - 3) := fun a b h => by
        simp only at h
        omega
      have hbij : Odd3s = (Finset.Icc 1 (m / 6)).map ⟨(fun k => 6 * k - 3), hinj⟩ := by
        ext x
        rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_map]
        simp only [Function.Embedding.coeFn_mk]
        constructor
        · intro ⟨⟨h1, h2⟩, h3_div, h2_ndiv⟩
          obtain ⟨k, rfl⟩ := h3_div
          have hk_pos : k ≥ 1 := by omega
          have hk_odd : Odd k := by
            by_contra h
            rw [Nat.not_odd_iff_even] at h
            obtain ⟨j, rfl⟩ := h
            apply h2_ndiv
            exact ⟨3 * j, by ring⟩
          obtain ⟨j, rfl⟩ := hk_odd
          refine ⟨j + 1, ?_, ?_⟩
          · rw [Finset.mem_Icc, h_m_sixth]
            exact ⟨by omega, by rw [hm_eq] at h2; omega⟩
          · ring_nf
            omega
        · intro ⟨k, hk, hx⟩
          rw [Finset.mem_Icc, h_m_sixth] at hk
          subst hx
          exact ⟨⟨by omega, by rw [hm_eq]; omega⟩, ⟨2 * k - 1, by omega⟩, fun ⟨j, hj⟩ => by omega⟩
      rw [hbij, Finset.card_map, Nat.card_Icc, h_m_sixth]
      omega

    -- S_odd3 = Odd3s \ {k <= 3^n}
    have h_diff : Odd3s.card - S_odd3.card ≤ 3^n := by
      -- Odd3s \ S_odd3 = odd multiples of 3 with k <= 3^n
      have hdiff_eq : Odd3s \ S_odd3 = (Finset.Icc 1 m).filter (fun k => 3 ∣ k ∧ ¬2 ∣ k ∧ k ≤ 3^n) := by
        ext x
        rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
        simp only [not_and, not_lt]
        exact ⟨fun ⟨⟨hx_mem, h3, h2n⟩, hnot⟩ => ⟨hx_mem, h3, h2n, hnot hx_mem h3 h2n⟩,
               fun ⟨hx_mem, h3, h2n, hle⟩ => ⟨⟨hx_mem, h3, h2n⟩, fun _ _ _ => hle⟩⟩
      -- Bound: |Odd3s \ S_odd3| <= |Icc 1 (3^n)| = 3^n
      have hbound : (Odd3s \ S_odd3).card ≤ 3^n := by
        rw [hdiff_eq]
        calc ((Finset.Icc 1 m).filter (fun k => 3 ∣ k ∧ ¬2 ∣ k ∧ k ≤ 3^n)).card
            ≤ (Finset.Icc 1 (3^n)).card := by
              apply Finset.card_le_card
              intro x hx
              rw [Finset.mem_filter, Finset.mem_Icc] at hx
              rw [Finset.mem_Icc]
              exact ⟨hx.1.1, hx.2.2.2⟩
          _ = 3^n := by
              rw [Nat.card_Icc]
              have h : 0 < 3^n := pow_pos (by omega : (0 : ℕ) < 3) n
              omega
      -- |Odd3s| - |S_odd3| = |Odd3s \ S_odd3| (since S_odd3 ⊆ Odd3s)
      have hcard_eq : Odd3s.card - S_odd3.card = (Odd3s \ S_odd3).card := by
        have hsubset : S_odd3 ⊆ Odd3s := fun x hx => by
          rw [Finset.mem_filter] at hx ⊢
          exact ⟨hx.1, hx.2.1, hx.2.2.1⟩
        have hi : S_odd3 ∩ Odd3s = S_odd3 := Finset.inter_eq_left.mpr hsubset
        rw [Finset.card_sdiff, hi]
      omega

    omega

  -- Main Inequality
  -- We want: countExceeding > m - countExceeding (equivalent to countExceeding > m/2)
  -- Sufficient: |S_even| + |S_odd3| > m/2
  have h_total : countExceeding n m ≥ S_even.card + S_odd3.card := by
    rw [←Finset.card_union_of_disjoint h_disjoint]
    apply Finset.card_le_card h_subset

  -- The two counts partition the range
  have h_sum : countExceeding n m + countNotExceeding n m = m := by
    unfold countExceeding countNotExceeding
    have hdisj : Disjoint ((Finset.Icc 1 m).filter (fun k => k > k.minFac ^ n))
                         ((Finset.Icc 1 m).filter (fun k => k ≤ k.minFac ^ n)) :=
      Finset.disjoint_filter.mpr fun x _ hgt hle => by omega
    have hcompl : (Finset.Icc 1 m).filter (fun k => k > k.minFac ^ n) ∪
                  (Finset.Icc 1 m).filter (fun k => k ≤ k.minFac ^ n) = Finset.Icc 1 m := by
      ext x; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]; omega
    rw [← Finset.card_union_of_disjoint hdisj, hcompl, Nat.card_Icc]; omega

  -- Now prove the main inequality
  -- We have: S_even.card ≥ m/2 - 2^n and S_odd3.card ≥ m/6 - 3^n
  -- So: S_even.card + S_odd3.card ≥ m/2 + m/6 - 2^n - 3^n = 2m/3 - 2^n - 3^n
  -- We need to show this is > m/2, i.e., m/6 > 2^n + 3^n
  -- Since m = 12 * 4^n, we have m/6 = 2 * 4^n
  -- We need: 2 * 4^n > 2^n + 3^n (for n ≥ 1)

  -- Handle n = 0 separately since 2 * 4^0 = 2 is not > 2^0 + 3^0 = 2
  cases n with
  | zero =>
    -- For n = 0: countExceeding counts k > 1, countNotExceeding counts k ≤ 1
    -- m = 12, so countExceeding = 11, countNotExceeding = 1
    simp only [pow_zero] at *
    unfold countExceeding countNotExceeding
    -- Direct calculation
    native_decide
  | succ n =>
    -- For n ≥ 1, the inequality 2 * 4^(n+1) > 2^(n+1) + 3^(n+1) holds
    -- Key inequality: 2 * 4^(n+1) > 2^(n+1) + 3^(n+1), hence m/6 > 2^(n+1) + 3^(n+1)
    have h_key : m / 6 > 2^(n+1) + 3^(n+1) := by
      have h_4_ge_3 : 4^n ≥ 3^n := Nat.pow_le_pow_left (by omega) n
      have h_3_ge_2 : 3^n ≥ 2^n := Nat.pow_le_pow_left (by omega) n
      have h_4_pos : 4^n ≥ 1 := Nat.one_le_pow n 4 (by omega)
      omega

    -- Combine: 2 * (S_even.card + S_odd3.card) > m
    have h_double : 2 * (S_even.card + S_odd3.card) > m := by omega

    calc countExceeding (n+1) m
        ≥ S_even.card + S_odd3.card := h_total
      _ > countNotExceeding (n+1) m := by omega

/-- The sequence a(n): least m such that countExceeding n m > countNotExceeding n m. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.find (a_exists n)

/-- a(1) = 15. -/
theorem a_one : a 1 = 15 := by
  unfold a
  native_decide

/-- a(2) = 27. -/
theorem a_two : a 2 = 27 := by
  unfold a
  native_decide

/-- a(3) = 57. -/
theorem a_three : a 3 = 57 := by
  unfold a
  native_decide

/-- The formula value. -/
def formula (n : ℕ) : ℕ := 3 ^ n + 3 * 2 ^ n + 6

/-! ## Subgoals for the proof of `a_formula` -/

/-- Subgoal 1: For n ≥ 3, 5^n > formula n, so composites with minFac ≥ 5 are bounded. -/
theorem five_pow_gt_formula {n : ℕ} (hn : n ≥ 3) : 5 ^ n > formula n := by
  unfold formula
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n _ ih =>
    simp only [pow_succ]
    have := Nat.one_le_pow' n 2
    have := Nat.one_le_pow' n 1
    omega

/-- Subgoal 2: For k with minFac ≥ 5, if k ≤ formula n and n ≥ 1, then k ≤ (minFac k)^n.
    This means such k never contributes to countExceeding. -/
theorem large_minFac_not_exceeding {n k : ℕ} (hn : n ≥ 1) (hk : k ≤ formula n)
    (hfac : k.minFac ≥ 5) : k ≤ k.minFac ^ n := by
  by_cases hprime : k.Prime
  · -- k is prime, so k = minFac k and k ≤ k^n
    rw [Nat.Prime.minFac_eq hprime]
    exact Nat.le_self_pow (by omega : n ≠ 0) k
  · -- k is composite (or k ≤ 1)
    have hkpos : 0 < k := by
      rcases k with _ | k
      · simp [Nat.minFac] at hfac
      · omega
    -- Since k > 0 and not prime, k is composite, so (minFac k)² ≤ k
    have hcomp : k.minFac ^ 2 ≤ k := Nat.minFac_sq_le_self hkpos hprime
    have hfac2 : k.minFac ^ 2 ≥ 25 := by nlinarith
    match n with
    | 1 =>
      -- formula 1 = 15 < 25 ≤ k, contradiction
      simp only [formula] at hk
      omega
    | 2 =>
      -- k ≤ 27, k ≥ 25, and (minFac k)² ≥ 25
      -- Need k ≤ (minFac k)². Since (minFac k)² ≤ k, we need k = (minFac k)²
      -- The only composite k in [25, 27] with minFac ≥ 5 is k = 25
      simp only [formula] at hk
      have hk_ge : k ≥ 25 := hfac2.trans hcomp
      interval_cases k
      · native_decide  -- k = 25
      · exact absurd (by decide : (26 : ℕ).minFac < 5) (not_lt.mpr hfac)
      · exact absurd (by native_decide : (27 : ℕ).minFac < 5) (not_lt.mpr hfac)
    | n + 3 =>
      -- Use five_pow_gt_formula: k ≤ formula(n+3) < 5^(n+3) ≤ (minFac k)^(n+3)
      have h5 := five_pow_gt_formula (by omega : n + 3 ≥ 3)
      exact (hk.trans_lt h5).le.trans (Nat.pow_le_pow_left hfac _)

/-- Subgoal 3: Count of even numbers k in {1,...,m} with k > 2^n. -/
def countEvenExceeding (n m : ℕ) : ℕ :=
  (Finset.Icc 1 m).filter (fun k => 2 ∣ k ∧ k > 2 ^ n) |>.card

/-- Subgoal 4: Count of odd multiples of 3 k in {1,...,m} with k > 3^n. -/
def countOddThreeExceeding (n m : ℕ) : ℕ :=
  (Finset.Icc 1 m).filter (fun k => 3 ∣ k ∧ ¬(2 ∣ k) ∧ k > 3 ^ n) |>.card

/-- Helper: minFac k = 3 when 3 ∣ k and ¬(2 ∣ k) and k ≠ 1. -/
private theorem minFac_eq_three {k : ℕ} (hk : k ≠ 1) (h3 : 3 ∣ k) (h2 : ¬(2 ∣ k)) :
    k.minFac = 3 := by
  have hk_ge_3 : k ≥ 3 := by
    rcases k with _ | _ | _ | k
    · omega
    · omega
    · exact absurd (dvd_refl 2) h2
    · omega
  apply Nat.le_antisymm
  · exact Nat.minFac_le_of_dvd (by omega) h3
  · have hne2 : k.minFac ≠ 2 := by
      intro h
      rw [Nat.minFac_eq_two_iff] at h
      exact h2 h
    have hprime := Nat.minFac_prime (by omega : k ≠ 1)
    have h2le := hprime.two_le
    omega

/-- Subgoal 5: For n ≥ 1 and m ≤ formula n, countExceeding equals the sum of
    even exceeding and odd-three exceeding counts. -/
theorem countExceeding_eq_sum {n m : ℕ} (hn : n ≥ 1) (hm : m ≤ formula n) :
    countExceeding n m = countEvenExceeding n m + countOddThreeExceeding n m := by
  unfold countExceeding countEvenExceeding countOddThreeExceeding
  -- The two filtered sets are disjoint (one requires 2 ∣ k, the other ¬(2 ∣ k))
  have hdisj : Disjoint
      ((Finset.Icc 1 m).filter (fun k => 2 ∣ k ∧ k > 2 ^ n))
      ((Finset.Icc 1 m).filter (fun k => 3 ∣ k ∧ ¬(2 ∣ k) ∧ k > 3 ^ n)) := by
    simp only [Finset.disjoint_filter]
    intro k _ ⟨h2div, _⟩ ⟨_, h2ndiv, _⟩
    exact h2ndiv h2div
  rw [← Finset.card_union_of_disjoint hdisj]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union]
  constructor
  · -- If k > k.minFac^n, show k is in one of the two sets
    intro ⟨⟨hk1, hkm⟩, hkexc⟩
    by_cases h2 : 2 ∣ k
    · -- k is even, so minFac k = 2
      left
      have hminFac : k.minFac = 2 := (Nat.minFac_eq_two_iff k).mpr h2
      refine ⟨⟨hk1, hkm⟩, h2, ?_⟩
      simp only [hminFac] at hkexc
      exact hkexc
    · -- k is odd
      right
      have hk_ge_2 : k ≥ 2 := by
        rcases k with _ | _ | k
        · omega  -- k = 0 contradicts hk1
        · -- k = 1: minFac 1 = 1, so 1 > 1^n is false
          simp only [show (0 : ℕ) + 1 = 1 from rfl, Nat.minFac_one, one_pow] at hkexc
          omega
        · omega
      have hminFac_ne_2 : k.minFac ≠ 2 := by
        intro h
        rw [Nat.minFac_eq_two_iff] at h
        exact h2 h
      have hminFac_ge : k.minFac ≥ 3 := by
        have hprime := Nat.minFac_prime (by omega : k ≠ 1)
        have h2le := hprime.two_le
        omega
      -- minFac k must be exactly 3 (not ≥ 5 by large_minFac_not_exceeding)
      have hminFac_lt_5 : k.minFac < 5 := by
        by_contra h
        push_neg at h
        have := large_minFac_not_exceeding hn (hkm.trans hm) h
        omega
      have hminFac : k.minFac = 3 := by
        have hprime := Nat.minFac_prime (by omega : k ≠ 1)
        interval_cases k.minFac <;> first | rfl | omega | exact absurd hprime (by decide)
      exact ⟨⟨hk1, hkm⟩, hminFac ▸ Nat.minFac_dvd k, h2, hminFac ▸ hkexc⟩
  · -- If k is in one of the two sets, show k > k.minFac^n
    intro h
    rcases h with ⟨⟨hk1, hkm⟩, h2div, hkexc⟩ | ⟨⟨hk1, hkm⟩, h3div, h2ndiv, hkexc⟩
    · -- k is even with k > 2^n
      exact ⟨⟨hk1, hkm⟩, (Nat.minFac_eq_two_iff k).mpr h2div ▸ hkexc⟩
    · -- k is odd multiple of 3 with k > 3^n
      have hk_ne_1 : k ≠ 1 := by intro h; simp only [h] at h3div; norm_num at h3div
      exact ⟨⟨hk1, hkm⟩, minFac_eq_three hk_ne_1 h3div h2ndiv ▸ hkexc⟩

/-- Count of even numbers in [1, m]. -/
private theorem card_even_Icc (m : ℕ) :
    ((Finset.Icc 1 m).filter (fun k => 2 ∣ k)).card = m / 2 := by
  have h : (Finset.Icc 1 m).filter (fun k => 2 ∣ k) =
           (Finset.Icc 1 (m/2)).image (fun k => 2 * k) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · intro ⟨⟨hk1, hkm⟩, hdvd⟩
      obtain ⟨j, rfl⟩ := hdvd
      exact ⟨j, ⟨by omega, by omega⟩, rfl⟩
    · intro ⟨j, ⟨hj1, hjm⟩, hk⟩
      subst hk
      refine ⟨⟨by omega, ?_⟩, dvd_mul_right 2 j⟩
      calc 2 * j ≤ 2 * (m / 2) := by omega
           _ ≤ m := Nat.mul_div_le m 2
  rw [h, Finset.card_image_of_injective]
  · simp only [Nat.card_Icc, Nat.add_sub_cancel]
  · intro a b hab
    simp only at hab
    omega

/-- Subgoal 6: Explicit formula for countEvenExceeding using floor division. -/
theorem countEvenExceeding_eq {n m : ℕ} (hn : n ≥ 1) (hm : m ≥ 2 ^ n) :
    countEvenExceeding n m = m / 2 - 2 ^ (n - 1) := by
  unfold countEvenExceeding
  -- Even numbers k with 2^n < k ≤ m are counted
  -- This equals (even numbers in [1,m]) - (even numbers in [1, 2^n])
  -- = m/2 - 2^n/2 = m/2 - 2^(n-1)
  have h2n : 2 ^ n / 2 = 2 ^ (n - 1) := by
    cases n with
    | zero => omega
    | succ n => simp [pow_succ]
  -- Split the filter into two conditions
  have hsplit : (Finset.Icc 1 m).filter (fun k => 2 ∣ k ∧ k > 2 ^ n) =
      (Finset.Icc 1 m).filter (fun k => 2 ∣ k) \
      (Finset.Icc 1 (2 ^ n)).filter (fun k => 2 ∣ k) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_sdiff]
    constructor
    · intro ⟨⟨hk1, hkm⟩, hdvd, hgt⟩
      exact ⟨⟨⟨hk1, hkm⟩, hdvd⟩, fun ⟨⟨_, hk2n⟩, _⟩ => by omega⟩
    · intro ⟨⟨⟨hk1, hkm⟩, hdvd⟩, hnotin⟩
      refine ⟨⟨hk1, hkm⟩, hdvd, ?_⟩
      by_contra hle
      push_neg at hle
      exact hnotin ⟨⟨hk1, hle⟩, hdvd⟩
  rw [hsplit]
  have hsub : (Finset.Icc 1 (2 ^ n)).filter (fun k => 2 ∣ k) ⊆
              (Finset.Icc 1 m).filter (fun k => 2 ∣ k) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk ⊢
    exact ⟨⟨hk.1.1, hk.1.2.trans hm⟩, hk.2⟩
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, card_even_Icc, card_even_Icc, h2n]

/-- Count of odd multiples of 3 in [1, m]. -/
private theorem card_odd_three_Icc (m : ℕ) :
    ((Finset.Icc 1 m).filter (fun k => 3 ∣ k ∧ ¬(2 ∣ k))).card = (m + 3) / 6 := by
  -- Odd multiples of 3 are: 3, 9, 15, ... = 6j - 3 for j ≥ 1
  have h : (Finset.Icc 1 m).filter (fun k => 3 ∣ k ∧ ¬(2 ∣ k)) =
           (Finset.Icc 1 ((m + 3) / 6)).image (fun j => 6 * j - 3) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · intro ⟨⟨hk1, hkm⟩, h3dvd, h2ndvd⟩
      obtain ⟨q, rfl⟩ := h3dvd
      have hq_odd : Odd q := by
        rw [Nat.odd_iff]
        by_contra hne1
        have hmod : q % 2 = 0 := by omega
        apply h2ndvd
        have : 2 ∣ q := Nat.dvd_of_mod_eq_zero hmod
        exact Dvd.dvd.mul_left this 3
      obtain ⟨j, rfl⟩ := hq_odd
      refine ⟨j + 1, ⟨?_, ?_⟩, ?_⟩
      · omega
      · have : 3 * (2 * j + 1) ≤ m := hkm
        omega
      · omega
    · intro ⟨j, ⟨hj1, hjm⟩, hk⟩
      subst hk
      refine ⟨⟨by omega, ?_⟩, ⟨2 * j - 1, by omega⟩, fun h2dvd => by omega⟩
      calc 6 * j - 3 ≤ 6 * ((m + 3) / 6) - 3 := by omega
           _ ≤ (m + 3) - 3 := by have := Nat.div_mul_le_self (m + 3) 6; omega
           _ = m := by omega
  rw [h, Finset.card_image_of_injective]
  · simp only [Nat.card_Icc, Nat.add_sub_cancel]
  · intro a b hab
    simp only at hab
    omega

/-- Subgoal 7: Explicit formula for countOddThreeExceeding using floor division. -/
theorem countOddThreeExceeding_eq {n m : ℕ} (hm : m ≥ 3 ^ n) :
    countOddThreeExceeding n m = (m + 3) / 6 - (3 ^ n + 3) / 6 := by
  unfold countOddThreeExceeding
  -- Odd multiples of 3 with k > 3^n in [1, m]
  -- = (odd multiples of 3 in [1, m]) - (odd multiples of 3 in [1, 3^n])
  -- = (m + 3) / 6 - (3^n + 3) / 6
  have hsplit : (Finset.Icc 1 m).filter (fun k => 3 ∣ k ∧ ¬(2 ∣ k) ∧ k > 3 ^ n) =
      (Finset.Icc 1 m).filter (fun k => 3 ∣ k ∧ ¬(2 ∣ k)) \
      (Finset.Icc 1 (3 ^ n)).filter (fun k => 3 ∣ k ∧ ¬(2 ∣ k)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_sdiff]
    constructor
    · intro ⟨⟨hk1, hkm⟩, h3dvd, h2ndvd, hgt⟩
      exact ⟨⟨⟨hk1, hkm⟩, h3dvd, h2ndvd⟩, fun ⟨⟨_, hk3n⟩, _⟩ => by omega⟩
    · intro ⟨⟨⟨hk1, hkm⟩, h3dvd, h2ndvd⟩, hnotin⟩
      refine ⟨⟨hk1, hkm⟩, h3dvd, h2ndvd, ?_⟩
      by_contra hle
      push_neg at hle
      exact hnotin ⟨⟨hk1, hle⟩, h3dvd, h2ndvd⟩
  rw [hsplit]
  have hsub : (Finset.Icc 1 (3 ^ n)).filter (fun k => 3 ∣ k ∧ ¬(2 ∣ k)) ⊆
              (Finset.Icc 1 m).filter (fun k => 3 ∣ k ∧ ¬(2 ∣ k)) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk ⊢
    exact ⟨⟨hk.1.1, hk.1.2.trans hm⟩, hk.2⟩
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, card_odd_three_Icc, card_odd_three_Icc]

/-- 3^n is always odd. -/
private theorem pow_three_odd (n : ℕ) : 3 ^ n % 2 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [pow_succ, Nat.mul_mod, ih]

/-- formula n is always odd for n ≥ 1. -/
private theorem formula_odd {n : ℕ} (hn : n ≥ 1) : formula n % 2 = 1 := by
  unfold formula
  have h3 : 3 ^ n % 2 = 1 := pow_three_odd n
  have h2 : (3 * 2 ^ n) % 2 = 0 := by
    cases n with
    | zero => omega
    | succ n => simp [pow_succ, Nat.mul_mod]
  omega

/-- Key simplification: the odd-three difference equals 2^(n-1) + 1. -/
private theorem odd_three_diff {n : ℕ} (hn : n ≥ 1) :
    (formula n + 3) / 6 - (3 ^ n + 3) / 6 = 2 ^ (n - 1) + 1 := by
  unfold formula
  -- Prove that 6 divides both terms
  have hdiv6a : 6 ∣ (3 ^ n + 3) := by
    have h3div : 3 ∣ (3 ^ n + 3) := by
      have : 3 ∣ 3 ^ n := dvd_pow_self 3 (by omega : n ≠ 0)
      omega
    have h2div : 2 ∣ (3 ^ n + 3) := by
      have hodd := pow_three_odd n
      omega
    have hcop : Nat.Coprime 2 3 := by decide
    exact hcop.mul_dvd_of_dvd_of_dvd h2div h3div
  have hdiv6b : 6 ∣ (3 ^ n + 3 * 2 ^ n + 6 + 3) := by
    have h3div : 3 ∣ (3 ^ n + 3 * 2 ^ n + 6 + 3) := by
      have h1 : 3 ∣ 3 ^ n := dvd_pow_self 3 (by omega : n ≠ 0)
      have h2 : 3 ∣ (3 * 2 ^ n) := dvd_mul_right 3 _
      omega
    have h2div : 2 ∣ (3 ^ n + 3 * 2 ^ n + 6 + 3) := by
      have hodd := pow_three_odd n
      have h2pow : 2 ∣ (3 * 2 ^ n) := by
        have : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega : n ≠ 0)
        omega
      omega
    have hcop : Nat.Coprime 2 3 := by decide
    exact hcop.mul_dvd_of_dvd_of_dvd h2div h3div
  -- Get the quotients
  obtain ⟨qa, hqa⟩ := hdiv6a
  obtain ⟨qb, hqb⟩ := hdiv6b
  -- Compute the quotients explicitly
  have hqa_eq : qa = (3 ^ n + 3) / 6 := by omega
  have hqb_eq : qb = (3 ^ n + 3 * 2 ^ n + 6 + 3) / 6 := by omega
  rw [← hqa_eq, ← hqb_eq]
  -- From hqa and hqb, we get: 6 * qb - 6 * qa = 3 * 2^n + 6
  -- So qb - qa = (3 * 2^n + 6) / 6 = (2^n + 2) / 2 = 2^(n-1) + 1
  have hdiff : 6 * qb - 6 * qa = 3 * 2 ^ n + 6 := by omega
  have hqb_ge_qa : qb ≥ qa := by omega
  have hqdiff : qb - qa = (3 * 2 ^ n + 6) / 6 := by
    have h : 6 * (qb - qa) = 3 * 2 ^ n + 6 := by omega
    omega
  rw [hqdiff]
  -- (3 * 2^n + 6) / 6 = (2^n + 2) / 2
  have h1 : (3 * 2 ^ n + 6) / 6 = (2 ^ n + 2) / 2 := by
    have h : 3 * 2 ^ n + 6 = 3 * (2 ^ n + 2) := by omega
    rw [h]
    have heven : 2 ∣ (2 ^ n + 2) := by
      have : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega : n ≠ 0)
      omega
    obtain ⟨k, hk⟩ := heven
    rw [hk]
    omega
  rw [h1]
  -- (2^n + 2) / 2 = 2^(n-1) + 1
  cases n with
  | zero => omega
  | succ n => simp [pow_succ, Nat.add_div_right]

/-- The total count equals m. -/
private theorem count_total (n m : ℕ) :
    countExceeding n m + countNotExceeding n m = m := by
  unfold countExceeding countNotExceeding
  have h : (Finset.Icc 1 m).filter (fun k => k > k.minFac ^ n) ∪
           (Finset.Icc 1 m).filter (fun k => k ≤ k.minFac ^ n) = Finset.Icc 1 m := by
    ext k
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro h
      rcases h with ⟨hk, _⟩ | ⟨hk, _⟩ <;> exact hk
    · intro hk
      by_cases h : k > k.minFac ^ n
      · left; exact ⟨hk, h⟩
      · right; exact ⟨hk, le_of_not_gt h⟩
  have hdisj : Disjoint
      ((Finset.Icc 1 m).filter (fun k => k > k.minFac ^ n))
      ((Finset.Icc 1 m).filter (fun k => k ≤ k.minFac ^ n)) := by
    simp only [Finset.disjoint_filter]
    intro k _ hgt hle
    omega
  rw [← Finset.card_union_of_disjoint hdisj, h, Nat.card_Icc]
  omega

/-- Subgoal 8: At m = formula n, countExceeding > countNotExceeding for n ≥ 1. -/
theorem formula_exceeds {n : ℕ} (hn : n ≥ 1) :
    countExceeding n (formula n) > countNotExceeding n (formula n) := by
  -- Use the decomposition and explicit formulas
  have hm_ge_2n : formula n ≥ 2 ^ n := by
    unfold formula
    calc 2 ^ n ≤ 3 * 2 ^ n := Nat.le_mul_of_pos_left (2 ^ n) (by omega)
         _ ≤ 3 ^ n + 3 * 2 ^ n := Nat.le_add_left _ _
         _ ≤ 3 ^ n + 3 * 2 ^ n + 6 := Nat.le_add_right _ _
  have hm_ge_3n : formula n ≥ 3 ^ n := by
    unfold formula
    exact le_add_right (le_add_right (Nat.le_refl _))
  have htotal := count_total n (formula n)
  have hcount := countExceeding_eq_sum hn (le_refl _)
  have heven := countEvenExceeding_eq hn hm_ge_2n
  have hodd := countOddThreeExceeding_eq hm_ge_3n
  -- Key insight: the odd-three difference simplifies to 2^(n-1) + 1
  have hdiff := odd_three_diff hn
  -- Use that formula n is odd
  have hodd_form := formula_odd hn
  -- Compute the exceeding count directly
  have hexc_eq : countExceeding n (formula n) = formula n / 2 + 1 := by
    rw [hcount, heven, hodd, hdiff]
    have h2n : 2 ^ (n - 1) ≤ formula n / 2 := by
      unfold formula
      cases n with
      | zero => omega
      | succ n =>
        simp only [Nat.succ_sub_one, pow_succ]
        have h := Nat.one_le_pow' n 2
        omega
    omega
  -- Use that formula n is odd to compute not-exceeding count
  have hnotexc_eq : countNotExceeding n (formula n) = formula n / 2 := by
    have hne : countNotExceeding n (formula n) = formula n - countExceeding n (formula n) := by
      omega
    rw [hne, hexc_eq]
    have hdiv2 : formula n / 2 * 2 = formula n - 1 := by omega
    omega
  -- Now the inequality is trivial
  rw [hexc_eq, hnotexc_eq]
  -- Goal: formula n / 2 + 1 > formula n / 2
  exact Nat.lt_succ_self _

/-- For m < formula n, the odd-three difference is at most 2^(n-1). -/
private theorem odd_three_diff_le {n m : ℕ} (hn : n ≥ 1) (hm : m < formula n) :
    (m + 3) / 6 - (3 ^ n + 3) / 6 ≤ 2 ^ (n - 1) := by
  -- Key: (formula n + 3) is divisible by 6, and
  -- (formula n + 3)/6 - (3^n + 3)/6 = 2^(n-1) + 1 by odd_three_diff
  -- For m < formula n, (m+3)/6 ≤ (formula n + 2)/6 = (formula n + 3)/6 - 1
  have hdiff := odd_three_diff hn
  -- Show 6 | (formula n + 3)
  have hdiv6 : 6 ∣ (formula n + 3) := by
    unfold formula
    have h3 : 3 ∣ (3 ^ n + 3 * 2 ^ n + 9) := by
      have h1 : 3 ∣ 3 ^ n := dvd_pow_self 3 (by omega : n ≠ 0)
      have h2 : 3 ∣ 3 * 2 ^ n := dvd_mul_right 3 _
      omega
    have h2 : 2 ∣ (3 ^ n + 3 * 2 ^ n + 9) := by
      have hodd := pow_three_odd n
      have h2pow : 2 ∣ (3 * 2 ^ n) := by
        have : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega : n ≠ 0)
        omega
      omega
    have hcop : Nat.Coprime 2 3 := by decide
    exact hcop.mul_dvd_of_dvd_of_dvd h2 h3
  obtain ⟨k, hk⟩ := hdiv6
  -- (formula n + 3) / 6 = k
  have hk_form : (formula n + 3) / 6 = k := by omega
  -- (formula n + 2) / 6 = k - 1
  have hk_pred : (formula n + 2) / 6 = k - 1 := by omega
  -- (m + 3) / 6 ≤ (formula n + 2) / 6
  have h1 : (m + 3) / 6 ≤ (formula n + 2) / 6 := Nat.div_le_div_right (by omega)
  -- (3^n + 3) / 6 ≤ (formula n + 2) / 6
  have hp : (3 ^ n + 3) / 6 ≤ (formula n + 2) / 6 := by
    have : formula n + 2 ≥ 3 ^ n + 3 := by unfold formula; omega
    exact Nat.div_le_div_right this
  -- k ≥ (3^n + 3)/6 + 2 from hdiff
  have h_k_ge : k ≥ (3 ^ n + 3) / 6 + 2 := by
    have : (formula n + 3) / 6 - (3 ^ n + 3) / 6 = 2 ^ (n - 1) + 1 := hdiff
    have h2n : 2 ^ (n - 1) ≥ 1 := Nat.one_le_pow' (n - 1) 1
    omega
  calc (m + 3) / 6 - (3 ^ n + 3) / 6
      ≤ (formula n + 2) / 6 - (3 ^ n + 3) / 6 := Nat.sub_le_sub_right h1 _
    _ = k - (3 ^ n + 3) / 6 - 1 := by rw [hk_pred]; omega
    _ = (formula n + 3) / 6 - (3 ^ n + 3) / 6 - 1 := by rw [hk_form]
    _ = 2 ^ (n - 1) := by rw [hdiff]; omega

/-- Subgoal 9: For all m < formula n, countExceeding ≤ countNotExceeding for n ≥ 1. -/
theorem below_formula_not_exceeds {n m : ℕ} (hn : n ≥ 1) (hm : m < formula n) :
    countExceeding n m ≤ countNotExceeding n m := by
  -- Equivalent to 2 * countExceeding ≤ m
  have htotal := count_total n m
  suffices h : 2 * countExceeding n m ≤ m by omega
  by_cases hm2 : m < 2 ^ n
  · -- Case 1: m < 2^n, so countExceeding = 0
    have hexc_zero : countExceeding n m = 0 := by
      unfold countExceeding
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k hk hkexc
      simp only [Finset.mem_Icc] at hk
      by_cases hk1 : k = 1
      · simp [hk1] at hkexc
      · have hminFac_ge : k.minFac ≥ 2 := (Nat.minFac_prime hk1).two_le
        have hpow : k.minFac ^ n ≥ 2 ^ n := Nat.pow_le_pow_left hminFac_ge n
        omega
    simp [hexc_zero]
  · -- Case 2: m ≥ 2^n
    push_neg at hm2
    by_cases hm3 : m < 3 ^ n
    · -- Case 2a: 2^n ≤ m < 3^n, countOddThreeExceeding = 0
      have hodd_zero : countOddThreeExceeding n m = 0 := by
        unfold countOddThreeExceeding
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro k hk ⟨h3dvd, h2ndvd, hkexc⟩
        simp only [Finset.mem_Icc] at hk
        have hk_ne_1 : k ≠ 1 := by
          intro h
          simp only [h] at h3dvd
          norm_num at h3dvd
        have hminFac : k.minFac = 3 := minFac_eq_three hk_ne_1 h3dvd h2ndvd
        have : k > 3 ^ n := hkexc
        omega
      have hcount := countExceeding_eq_sum hn hm.le
      have heven := countEvenExceeding_eq hn hm2
      rw [hcount, heven, hodd_zero, add_zero]
      -- Need: 2 * (m/2 - 2^(n-1)) ≤ m
      have h2pow : 2 ^ (n - 1) ≤ m / 2 := by
        have h2n : 2 ^ n ≤ m := hm2
        have h2n1 : 2 ^ (n - 1) * 2 = 2 ^ n := by
          cases n with
          | zero => omega
          | succ n => simp [pow_succ, mul_comm]
        have h2n1_le : 2 ^ (n - 1) * 2 ≤ m := h2n1 ▸ h2n
        omega
      calc 2 * (m / 2 - 2 ^ (n - 1))
          ≤ 2 * (m / 2) := Nat.mul_le_mul_left 2 (Nat.sub_le _ _)
        _ ≤ m := Nat.mul_div_le m 2
    · -- Case 2b: m ≥ 3^n, use full formulas
      push_neg at hm3
      have hcount := countExceeding_eq_sum hn hm.le
      have heven := countEvenExceeding_eq hn hm2
      have hodd := countOddThreeExceeding_eq hm3
      rw [hcount, heven, hodd]
      -- Need: 2 * (m/2 - 2^(n-1) + (m+3)/6 - (3^n+3)/6) ≤ m
      have hdiff_le := odd_three_diff_le hn hm
      have h2pow : 2 ^ (n - 1) ≤ m / 2 := by
        have h2n : 2 ^ n ≤ m := hm2
        have h2n1 : 2 ^ (n - 1) * 2 = 2 ^ n := by
          cases n with
          | zero => omega
          | succ n => simp [pow_succ, mul_comm]
        have h2n1_le : 2 ^ (n - 1) * 2 ≤ m := h2n1 ▸ h2n
        omega
      -- exceeding = m/2 - 2^(n-1) + (m+3)/6 - (3^n+3)/6 ≤ m/2 - 2^(n-1) + 2^(n-1) = m/2
      calc 2 * (m / 2 - 2 ^ (n - 1) + ((m + 3) / 6 - (3 ^ n + 3) / 6))
          ≤ 2 * (m / 2 - 2 ^ (n - 1) + 2 ^ (n - 1)) := by omega
        _ = 2 * (m / 2) := by omega
        _ ≤ m := Nat.mul_div_le m 2

/-- Conjecture: a(n) = 3^n + 3 * 2^n + 6 for n ≥ 1. -/
theorem a_formula {n : ℕ} (hn : n ≥ 1) : a n = 3 ^ n + 3 * 2 ^ n + 6 := by
  rw [a, Nat.find_eq_iff]
  exact ⟨formula_exceeds hn, fun m hm => not_lt.mpr (below_formula_not_exceeds hn hm)⟩

end
