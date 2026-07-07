import CollatzMapBasics.Terras
import CollatzMapBasics.Decomposition
import CollatzMapBasics.Base3div2.Base3div2Basics
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Filter.AtTopBot.Basic

namespace CollatzMapBasics

open Classical Filter

-- ============================================================
-- Forward direction helpers
-- ============================================================

/-- `num_odd_steps` splits over concatenation of orbits. -/
lemma num_odd_steps_split (a b n : ℕ) :
    num_odd_steps (a + b) n = num_odd_steps a n + num_odd_steps b (T_iter a n) := by
  simp [num_odd_steps, Finset.sum_range_add, Nat.add_comm, ← T_iter_add]

/-- T applied 2j times to 1 gives 1. -/
lemma T_iter_one_even (j : ℕ) : T_iter (2 * j) 1 = 1 := by
  induction j <;> simp_all [T_iter, T_one, T_two]

/-- T applied 2j+1 times to 1 gives 2. -/
lemma T_iter_one_odd (j : ℕ) : T_iter (2 * j + 1) 1 = 2 := by
  rw [T_iter, T_iter_one_even, T_one]

/-- The parity indicator of T^i(1): 1 when i is even, 0 when i is odd. -/
lemma X_T_iter_one (i : ℕ) : X (T_iter i 1) = if i % 2 = 0 then 1 else 0 := by
  rcases Nat.even_or_odd i with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
  simp [show j + j = 2 * j by ring, T_iter_one_even, T_iter_one_odd, X_odd, X_even]

/-- The number of odd steps starting from 1 over 2j steps is exactly j. -/
lemma num_odd_steps_one_even (j : ℕ) : num_odd_steps (2 * j) 1 = j := by
  induction j with | zero => rfl | succ j ih =>
    rw [Nat.mul_succ, num_odd_steps_split, ih, T_iter_one_even, num_odd_steps]; rfl

/-- The number of odd steps starting from 1 over 2j+1 steps is j+1. -/
lemma num_odd_steps_one_odd (j : ℕ) : num_odd_steps (2 * j + 1) 1 = j + 1 := by
  rw [num_odd_steps_split (2 * j) 1, num_odd_steps_one_even, T_iter_one_even, num_odd_steps]; rfl

/-- The number of odd steps from 1 over m steps satisfies 2·s ∈ {m, m+1}. -/
lemma num_odd_steps_one_bounds (m : ℕ) :
    m ≤ 2 * num_odd_steps m 1 + 1 ∧ 2 * num_odd_steps m 1 ≤ m + 1 := by
  rcases Nat.even_or_odd m with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · simp [← two_mul, num_odd_steps_one_even]
  · simp [num_odd_steps_one_odd]; omega

/-- After reaching 1, the even proportion of iterates tends to 1/2. -/
lemma forward (n : ℕ) (_hn : n ≥ 1) (k₀ : ℕ) (hk₀ : k₀ ≥ 1) (hreach : T_iter k₀ n = 1) :
    Tendsto (fun k => (↑(k - num_odd_steps k n) : ℚ) / ↑k)
      atTop (nhds (1 / 2 : ℚ)) := by
  have hc_le : num_odd_steps k₀ n ≤ k₀ := num_odd_steps_le k₀ n
  -- For k ≥ k₀: odd step count decomposes via the 1→2→1→2 tail
  have hsplit : ∀ k, k ≥ k₀ →
      num_odd_steps k n = num_odd_steps k₀ n + num_odd_steps (k - k₀) 1 := by
    intro k hk
    conv_lhs => rw [show k = k₀ + (k - k₀) from by omega]
    rw [num_odd_steps_split, hreach]
  -- ℕ bounds avoiding subtraction: 2·s_k is sandwiched
  have hbounds : ∀ k, k ≥ k₀ →
      2 * num_odd_steps k n ≤ k + (k₀ + 1) ∧
      k ≤ 2 * num_odd_steps k n + (k₀ + 1) := by
    intro k hk
    have hs := hsplit k hk
    have ⟨lb, ub⟩ := num_odd_steps_one_bounds (k - k₀)
    constructor <;> omega
  rw [tendsto_order]
  constructor
  · -- Lower bound: for a < 1/2, eventually a < f(k)
    intro a ha
    rw [Filter.eventually_atTop]
    have h12a : (0 : ℚ) < 1 - 2 * a := by linarith
    obtain ⟨N, hN⟩ := exists_nat_gt ((↑k₀ + 1 : ℚ) / (1 - 2 * a))
    refine ⟨max N (k₀ + 1), fun k hk => ?_⟩
    have hk_pos : (0 : ℚ) < ↑k := Nat.cast_pos.mpr (by omega)
    have hs_le : num_odd_steps k n ≤ k := num_odd_steps_le k n
    rw [Nat.cast_sub hs_le, lt_div_iff₀ hk_pos]
    have hlo : 2 * (num_odd_steps k n : ℚ) ≤ ↑k + (↑k₀ + 1) := by
      exact_mod_cast (hbounds k (by omega)).1
    have hk_gt : (↑k₀ + 1 : ℚ) / (1 - 2 * a) < ↑k :=
      lt_of_lt_of_le hN (by exact_mod_cast show N ≤ k by omega)
    nlinarith [(div_lt_iff₀ h12a).mp hk_gt]
  · -- Upper bound: for b > 1/2, eventually f(k) < b
    intro b hb
    rw [Filter.eventually_atTop]
    have h2b1 : (0 : ℚ) < 2 * b - 1 := by linarith
    obtain ⟨N, hN⟩ := exists_nat_gt ((↑k₀ + 1 : ℚ) / (2 * b - 1))
    refine ⟨max N (k₀ + 1), fun k hk => ?_⟩
    have hk_pos : (0 : ℚ) < ↑k := Nat.cast_pos.mpr (by omega)
    have hs_le : num_odd_steps k n ≤ k := num_odd_steps_le k n
    rw [Nat.cast_sub hs_le, div_lt_iff₀ hk_pos]
    have hhi : (↑k : ℚ) ≤ 2 * (num_odd_steps k n : ℚ) + (↑k₀ + 1) := by
      exact_mod_cast (hbounds k (by omega)).2
    have hk_gt : (↑k₀ + 1 : ℚ) / (2 * b - 1) < ↑k :=
      lt_of_lt_of_le hN (by exact_mod_cast show N ≤ k by omega)
    nlinarith [(div_lt_iff₀ h2b1).mp hk_gt]

-- ============================================================
-- Backward direction helpers
-- ============================================================

/-- Every n from 1 to 9 eventually reaches 1 under T. -/
lemma small_cases (n : ℕ) (hn : 1 ≤ n) (hn9 : n ≤ 9) :
    ∃ k, k ≥ 1 ∧ T_iter k n = 1 := by
  interval_cases n
  · exact ⟨2, by omega, by native_decide⟩
  · exact ⟨1, by omega, by native_decide⟩
  · exact ⟨5, by omega, by native_decide⟩
  · exact ⟨2, by omega, by native_decide⟩
  · exact ⟨4, by omega, by native_decide⟩
  · exact ⟨6, by omega, by native_decide⟩
  · exact ⟨11, by omega, by native_decide⟩
  · exact ⟨3, by omega, by native_decide⟩
  · exact ⟨13, by omega, by native_decide⟩

/-- For odd n ≥ 10: 10(3n+1) ≤ 31n, i.e., T(n) ≤ 31n/20. -/
lemma T_odd_upper (n : ℕ) (hn : n ≥ 10) (hodd : n % 2 = 1) :
    10 * (3 * n + 1) ≤ 31 * n := by omega

/-- Inductive bound: if all iterates of n stay ≥ 10, then
    10^s · 2^k · T^k(n) ≤ 31^s · n, where s = num_odd_steps k n. -/
lemma T_iter_bound (k n : ℕ) (h : ∀ j, j ≤ k → T_iter j n ≥ 10) :
    10 ^ num_odd_steps k n * (2 ^ k * T_iter k n) ≤
    31 ^ num_odd_steps k n * n := by
  induction k with
  | zero => simp [num_odd_steps, T_iter]
  | succ k ih =>
    have ih' := ih (fun j hj => h j (Nat.le_succ_of_le hj))
    have hnk : T_iter k n ≥ 10 := h k (Nat.le_succ k)
    rw [num_odd_steps_succ]
    rcases Nat.even_or_odd (T_iter k n) with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- Even: X = 0
      have hx : X (T_iter k n) = 0 := X_even (by omega)
      rw [hx, Nat.add_zero]
      -- T_{k+1} = T(nk), and 2 * T(nk) = nk (even case)
      show 10 ^ num_odd_steps k n * (2 ^ (k + 1) * T (T_iter k n)) ≤ _
      have hexp : 2 * T (T_iter k n) = T_iter k n := by
        have := T_expand (T_iter k n); rw [hx] at this; linarith
      calc 10 ^ num_odd_steps k n * (2 ^ (k + 1) * T (T_iter k n))
          = 10 ^ num_odd_steps k n * (2 ^ k * (2 * T (T_iter k n))) := by ring
        _ = 10 ^ num_odd_steps k n * (2 ^ k * T_iter k n) := by rw [hexp]
        _ ≤ 31 ^ num_odd_steps k n * n := ih'
    · -- Odd: X = 1
      have hx : X (T_iter k n) = 1 := X_odd (by omega)
      rw [hx]
      show 10 ^ (num_odd_steps k n + 1) * (2 ^ (k + 1) * T (T_iter k n)) ≤
           31 ^ (num_odd_steps k n + 1) * n
      -- 2 * T(nk) = 3 * nk + 1
      have hexp : 2 * T (T_iter k n) = 3 * T_iter k n + 1 := by
        have := T_expand (T_iter k n); rw [hx] at this; linarith
      have hbound : 10 * (3 * T_iter k n + 1) ≤ 31 * T_iter k n :=
        T_odd_upper _ hnk (by omega)
      calc 10 ^ (num_odd_steps k n + 1) * (2 ^ (k + 1) * T (T_iter k n))
          = 10 ^ num_odd_steps k n * (2 ^ k * (10 * (2 * T (T_iter k n)))) := by ring
        _ = 10 ^ num_odd_steps k n * (2 ^ k * (10 * (3 * T_iter k n + 1))) := by rw [hexp]
        _ ≤ 10 ^ num_odd_steps k n * (2 ^ k * (31 * T_iter k n)) := by
            apply Nat.mul_le_mul_left; apply Nat.mul_le_mul_left; exact hbound
        _ = 31 * (10 ^ num_odd_steps k n * (2 ^ k * T_iter k n)) := by ring
        _ ≤ 31 * (31 ^ num_odd_steps k n * n) := Nat.mul_le_mul_left 31 ih'
        _ = 31 ^ (num_odd_steps k n + 1) * n := by ring

/-- If 5s+1 ≤ 3k then 31^s < 2^k · 10^s. Proved by induction on s with step 3,
    using the key arithmetic fact 31³ < 2⁵ · 10³. -/
lemma ratio_bound : ∀ s k : ℕ, 5 * s + 1 ≤ 3 * k → 31 ^ s < 2 ^ k * 10 ^ s := by
  -- By strong induction on s, with step 3.
  intro s
  induction s using Nat.strongRecOn with
  | _ s ih =>
    intro k h
    rcases s with _ | _ | _ | s
    · -- s = 0: 1 < 2^k. From h: k ≥ 1.
      simp only [pow_zero, mul_one]
      exact one_lt_pow₀ (by omega : (1 : ℕ) < 2) (by omega : k ≠ 0)
    · -- s = 1: 31 < 2^k * 10. From h: k ≥ 2.
      calc (31 : ℕ) < 40 := by omega
        _ = 2 ^ 2 * 10 ^ 1 := by norm_num
        _ ≤ 2 ^ k * 10 ^ 1 := by
          apply Nat.mul_le_mul_right; exact Nat.pow_le_pow_right (by omega) (by omega)
    · -- s = 2: 961 < 2^k * 100. From h: k ≥ 4.
      calc (31 : ℕ) ^ 2 = 961 := by norm_num
        _ < 1600 := by omega
        _ = 2 ^ 4 * 10 ^ 2 := by norm_num
        _ ≤ 2 ^ k * 10 ^ 2 := by
          apply Nat.mul_le_mul_right; exact Nat.pow_le_pow_right (by omega) (by omega)
    · -- s + 3: use IH with (s, k-5).
      have hk5 : k ≥ 6 := by omega
      have ih' := ih s (by omega) (k - 5) (by omega)
      calc 31 ^ (s + 3) = 31 ^ 3 * 31 ^ s := by ring
        _ < 31 ^ 3 * (2 ^ (k - 5) * 10 ^ s) := by
          exact Nat.mul_lt_mul_of_pos_left ih' (by norm_num)
        _ ≤ (2 ^ 5 * 10 ^ 3) * (2 ^ (k - 5) * 10 ^ s) := by
          apply Nat.mul_le_mul_right; norm_num
        _ = 2 ^ k * 10 ^ (s + 3) := by
          have h5k : 5 + (k - 5) = k := by omega
          rw [show (2 : ℕ) ^ 5 * 10 ^ 3 * (2 ^ (k - 5) * 10 ^ s)
              = (2 ^ 5 * 2 ^ (k - 5)) * (10 ^ 3 * 10 ^ s) from by ring,
              ← pow_add, ← pow_add, h5k, Nat.add_comm 3 s]

/-- If m is the minimal element that never reaches 1, then its orbit stays ≥ m. -/
lemma orbit_lower_bound (m : ℕ) (hm : m ≥ 1)
    (h_never : ∀ k, k ≥ 1 → T_iter k m ≠ 1)
    (h_min : ∀ n, n < m → n ≥ 1 → ∃ k, k ≥ 1 ∧ T_iter k n = 1) :
    ∀ j, T_iter j m ≥ m := by
  intro j; by_contra hlt; push Not at hlt
  cases j with
  | zero => simp [T_iter] at hlt
  | succ j =>
    obtain ⟨k, hk, hreach⟩ := h_min _ hlt (T_iter_pos hm _)
    have := h_never (k + (j + 1)) (by omega)
    rw [T_iter_add] at this
    exact this hreach

/-- From the Tendsto condition, extract a concrete k where 5·s+1 ≤ 3·k. -/
lemma exists_ratio_bound_of_tendsto (n : ℕ)
    (ht : Tendsto (fun k => (↑(k - num_odd_steps k n) : ℚ) / ↑k)
      atTop (nhds (1 / 2 : ℚ))) :
    ∃ k : ℕ, k ≥ 1 ∧ 5 * num_odd_steps k n + 1 ≤ 3 * k := by
  have hev : ∀ᶠ k in atTop,
      (↑(k - num_odd_steps k n) : ℚ) / ↑k ∈ Set.Ioo (2/5 : ℚ) (3/5) :=
    ht.eventually (Ioo_mem_nhds (by norm_num) (by norm_num))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨max N 1, le_max_right _ _, ?_⟩
  have hmemk := (hN (max N 1) (le_max_left _ _)).1
  have hk_pos : (0 : ℚ) < ↑(max N 1) := by norm_cast; omega
  rw [Nat.cast_sub (num_odd_steps_le _ _), lt_div_iff₀ hk_pos] at hmemk
  have : 5 * (num_odd_steps (max N 1) n : ℚ) < 3 * ↑(max N 1) := by linarith
  exact_mod_cast this

-- ============================================================
-- Main theorem
-- ============================================================

/-- Conjectures 2.4 and 2.5 are equivalent:
  2.4: every n ≥ 1 eventually reaches 1 under T;
  2.5: for every n ≥ 1, the proportion of even iterates tends to 1/2. -/
lemma conjecture_2_4_iff_2_5 :
    (∀ n : ℕ, n ≥ 1 → ∃ k, k ≥ 1 ∧ T_iter k n = 1) ↔
    (∀ n : ℕ, n ≥ 1 → Tendsto (fun k => (↑(k - num_odd_steps k n) : ℚ) / ↑k)
      atTop (nhds (1 / 2 : ℚ))) := by
  constructor
  · -- Forward: reaching 1 implies even density → 1/2
    intro h24 n hn
    obtain ⟨k₀, hk₀, hreach⟩ := h24 n hn
    exact forward n hn k₀ hk₀ hreach
  · -- Backward: even density → 1/2 implies reaching 1
    intro h25
    by_contra h_neg
    push Not at h_neg
    obtain ⟨n₀, hn₀, h_never₀⟩ := h_neg
    -- Minimal counterexample
    let P : ℕ → Prop := fun n => n ≥ 1 ∧ ∀ k, k ≥ 1 → T_iter k n ≠ 1
    have hP_exists : ∃ n, P n := ⟨n₀, hn₀, h_never₀⟩
    let m := Nat.find hP_exists
    have hm : P m := Nat.find_spec hP_exists
    have hm_min : ∀ n, n < m → ¬P n := fun n hn => Nat.find_min hP_exists hn
    -- m ≥ 10 by small_cases
    have hm_ge_10 : m ≥ 10 := by
      by_contra hlt; push Not at hlt
      obtain ⟨k, hk, hreach⟩ := small_cases m hm.1 (by omega)
      exact hm.2 k hk hreach
    -- T_iter j m ≥ m for all j, by minimality
    have h_orbit : ∀ j, T_iter j m ≥ m :=
      orbit_lower_bound m hm.1 hm.2 (fun n hn hn1 => by
        by_contra h_neg2; push Not at h_neg2
        exact hm_min n hn ⟨hn1, h_neg2⟩)
    -- Tendsto for m
    have h_tend := h25 m hm.1
    -- Extract k with 5·s+1 ≤ 3·k
    obtain ⟨k, hk1, hk_bound⟩ := exists_ratio_bound_of_tendsto m h_tend
    -- All iterates ≥ 10
    have h_ge_10 : ∀ j, j ≤ k → T_iter j m ≥ 10 :=
      fun j _ => le_trans hm_ge_10 (h_orbit j)
    -- Inductive bound + ratio bound → T_iter k m < m
    have h_bound := T_iter_bound k m h_ge_10
    have h_ratio := ratio_bound (num_odd_steps k m) k hk_bound
    have h_lt : T_iter k m < m := by
      by_contra hge; push Not at hge
      have h10 : 0 < 10 ^ num_odd_steps k m := Nat.pos_of_ne_zero (by positivity)
      have : 31 ^ num_odd_steps k m * m
          < 10 ^ num_odd_steps k m * (2 ^ k * m) := by
        calc 31 ^ num_odd_steps k m * m
            < 2 ^ k * 10 ^ num_odd_steps k m * m := by nlinarith [h_ratio]
          _ = 10 ^ num_odd_steps k m * (2 ^ k * m) := by ring
      linarith [h_bound, Nat.mul_le_mul_left (10 ^ num_odd_steps k m)
        (Nat.mul_le_mul_left (2 ^ k) hge)]
    -- Contradiction
    exact absurd (h_orbit k) (not_le.mpr h_lt)

-- ============================================================
-- Conjectures 4.2 and 4.3 (Eliahou–Verger-Gaugry, §4)
-- ============================================================

open Base3div2

/-- The j-th digit of the infinite saturated word ⟨sat(∞)⟩ = limₖ ⟨sat(k)⟩.
    By Proposition 3.9, digit j is `1` when `sat j` is odd, `2` when even. -/
def satWord (j : ℕ) : ℕ := if sat j % 2 = 1 then 1 else 2

/-- Number of `1`-digits among the first `k` digits of ⟨sat(∞)⟩. -/
def numOnesSat (k : ℕ) : ℕ :=
  ((Finset.range k).filter (fun j => sat j % 2 = 1)).card

/-- Conjecture 4.2: The proportion of digits `1` in ⟨sat(k)⟩ tends to 1/2. -/
def conjecture_4_2 : Prop :=
  Tendsto (fun k => (numOnesSat k : ℚ) / ↑k) atTop (nhds (1 / 2 : ℚ))

/-- Number of positions `i < n` where the length-`|w|` subword of ⟨sat(∞)⟩
    starting at position `i` equals `w`. -/
def subwordCount (w : List ℕ) (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun i =>
    (List.range w.length).map (fun j => satWord (i + j)) = w)).card

/-- Conjecture 4.3: The infinite word ⟨sat(∞)⟩ is **normal** over {1, 2}.
    Every word of length ℓ over {1, 2} appears with asymptotic frequency 1/2^ℓ. -/
def conjecture_4_3 : Prop :=
  ∀ (w : List ℕ), (∀ d ∈ w, d = 1 ∨ d = 2) →
    Tendsto (fun n => (subwordCount w n : ℚ) / ↑n) atTop (nhds (1 / 2 ^ w.length : ℚ))

/-- Conjecture 4.3 (normality) implies Conjecture 4.2 (digit-1 density). -/
theorem conjecture_4_3_implies_4_2 : conjecture_4_3 → conjecture_4_2 := by
  intro h43
  have h := h43 [1] (by simp)
  simp only [List.length_cons, List.length_nil] at h
  suffices heq : ∀ n, subwordCount [1] n = numOnesSat n by
    simp only [heq] at h; exact h
  intro n
  simp only [subwordCount, numOnesSat, satWord]
  congr 1; ext j; simp [List.cons.injEq]

-- ============================================================
-- U-orbit density (option B): density along U-orbits
-- ============================================================

/-- Count of odd values among the first `k` iterates `U_iter 0 n₀, …, U_iter (k-1) n₀`. -/
def numOddU (k n₀ : ℕ) : ℕ :=
  ((Finset.range k).filter (fun j => U_iter j n₀ % 2 = 1)).card

/-- The U-orbit density conjecture for a fixed starting point `n₀`:
    the proportion of odd values in `U_iter j n₀` tends to 1/2. -/
def U_orbit_density (n₀ : ℕ) : Prop :=
  Tendsto (fun k => (numOddU k n₀ : ℚ) / ↑k) atTop (nhds (1 / 2 : ℚ))

/-- The universal U-orbit density conjecture: for every starting point,
    the odd-density of the U-orbit tends to 1/2. -/
def conjecture_U_orbit_density : Prop := ∀ n₀ : ℕ, U_orbit_density n₀

/-- Conjecture 4.2 is exactly the U-orbit density for `n₀ = 0`:
    `sat j = U_iter j 0`, so counting odd `sat j` is counting odd `U_iter j 0`. -/
theorem conjecture_4_2_eq_U_orbit_zero : conjecture_4_2 ↔ U_orbit_density 0 := by
  unfold conjecture_4_2 U_orbit_density numOddU numOnesSat sat
  rfl

end CollatzMapBasics
