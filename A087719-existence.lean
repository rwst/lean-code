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

