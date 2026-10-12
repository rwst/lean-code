/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import ForMathlib.Combinatorics.CoinTail
import ForMathlib.Combinatorics.NatDensity
import EVG25.M0.Prefix

/-!
# The natural horizon: almost all `U`-words are balanced up to `log₂ n₀`

Theorem 2 of plan EVGQ17-M0.  Write `S_k(n₀) = CC.numOddU k n₀` for the number of letters `1` among
the first `k` letters of the `U`-word of `n₀`, and `λ(n₀) = Nat.log 2 n₀ + 1` for its bit length.

* `hasNatDensity_unbalanced_below_horizon` — **(a)** for every `ε > 0` and every `h → ∞`, the
  seeds with `|S_k(n₀) - k/2| > εk` for some `k ∈ [h(n₀), λ(n₀)]` have natural density `0`;
* `card_unbalanced_window_le` — **(b)** the window form: in every interval of length `L`, at most
  `4L·q^{k₀}/(1-q)` seeds (`q = e^{-2ε²}`) are unbalanced at some `k ∈ [k₀, log₂ L]`;
* `hasNatDensity_envelope_below_horizon` — **(c)** the envelope: for every `c > 1/2`, the seeds with
  `|S_k(n₀) - k/2| > √(c·k·ln k)` for some `k ∈ [h(n₀), λ(n₀)]` have natural density `0`.

All three are instances of one counting lemma, `card_window_le`, for an arbitrary threshold `θ`:
Theorem 1 (`EVG25.M0.card_filter_uPrefix_mem`) turns the seeds of an interval of length `L` that
are unbalanced at time `k` into at most `(L + 2^k)/2^k` copies of the set of unbalanced coin
words, whose size the coin-tail bound (`CoinTail.card_filter_abs_sub_gt_le`) controls.  The horizon
enters only through `2^k ≤ 2n`, i.e. `k ≤ λ(n)`: past it, an interval of seeds is a proper subset of
a period and Theorem 1 says nothing.

The statement is folklore for the whole Matthews–Watts class (immediate from Theorem 1); see
plan EVGQ17-M0 §2 and §4.
-/

open Filter Topology Finset CC CC.Base3div2

namespace EVG25.M0

/-! ## Counting letters through the prefix -/

/-- `S_k(n)` counts the letters `1` of the length-`k` prefix. -/
theorem numOddU_eq_card_uPrefix (k n : ℕ) :
    numOddU k n = (univ.filter fun i : Fin k => uPrefix k n i = true).card := by
  unfold numOddU uPrefix uLetter
  rw [card_filter, card_filter]
  simp only [decide_eq_true_eq]
  exact (Fin.sum_univ_eq_sum_range (fun i => if U_iter i n % 2 = 1 then 1 else 0) k).symm

/-- Unbalanced at time `k` with threshold `θ k`. -/
def Unbal (θ : ℕ → ℝ) (k n : ℕ) : Prop := θ k < |(numOddU k n : ℝ) - k / 2|

/-- The unbalanced coin words of length `k`. -/
noncomputable def badWords (θ : ℕ → ℝ) (k : ℕ) : Finset (Fin k → Bool) :=
  univ.filter fun w => θ k < |((univ.filter fun i => w i = true).card : ℝ) - k / 2|

theorem unbal_iff_mem_badWords (θ : ℕ → ℝ) (k n : ℕ) :
    Unbal θ k n ↔ uPrefix k n ∈ badWords θ k := by
  simp [Unbal, badWords, numOddU_eq_card_uPrefix]

noncomputable instance (θ : ℕ → ℝ) (k : ℕ) : DecidablePred (Unbal θ k) :=
  fun n => inferInstanceAs (Decidable (θ k < |(numOddU k n : ℝ) - k / 2|))

/-- Unbalanced at some time `k ∈ [k₀, K]`. -/
def UnbalIn (θ : ℕ → ℝ) (k₀ K n : ℕ) : Prop := ∃ k ∈ Icc k₀ K, Unbal θ k n

noncomputable instance (θ : ℕ → ℝ) (k₀ K : ℕ) : DecidablePred (UnbalIn θ k₀ K) :=
  fun n => inferInstanceAs (Decidable (∃ k ∈ Icc k₀ K, Unbal θ k n))

/-! ## The counting lemma -/

section Counting

variable (θ g : ℕ → ℝ) (hW : ∀ k, ((badWords θ k).card : ℝ) ≤ 2 ^ k * g k)
include hW

omit hW in
theorem nonneg_of_badWords {θ g : ℕ → ℝ}
    (hW : ∀ k, ((badWords θ k).card : ℝ) ≤ 2 ^ k * g k) (k : ℕ) : 0 ≤ g k := by
  have := hW k
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  nlinarith [(Nat.cast_nonneg (badWords θ k).card : (0 : ℝ) ≤ _)]

/-- One time `k`: in an interval of length `L`, at most `(L + 2^k)·g k` seeds are unbalanced. -/
theorem card_unbal_Ico_le (a L k : ℕ) :
    (((Ico a (a + L)).filter fun n => Unbal θ k n).card : ℝ) ≤ (L + 2 ^ k) * g k := by
  classical
  have hp : 0 < 2 ^ k := by positivity
  set t := L / 2 ^ k + 1
  have hsub : (Ico a (a + L)).filter (fun n => Unbal θ k n)
      ⊆ (Ico a (a + t * 2 ^ k)).filter (uPrefix k · ∈ badWords θ k) := by
    intro n hn
    simp only [mem_filter, mem_Ico] at hn ⊢
    have : L < t * 2 ^ k := by rw [mul_comm]; exact Nat.lt_mul_div_succ L hp
    refine ⟨⟨hn.1.1, by omega⟩, (unbal_iff_mem_badWords θ k n).1 hn.2⟩
  have hc := card_le_card hsub
  rw [card_filter_uPrefix_mem] at hc
  have ht : (t : ℝ) * 2 ^ k ≤ L + 2 ^ k := by
    have := Nat.div_mul_le_self L (2 ^ k)
    have : (t * 2 ^ k : ℕ) ≤ L + 2 ^ k := by simp only [t, add_mul, one_mul]; omega
    exact_mod_cast this
  have hg := nonneg_of_badWords hW k
  calc (((Ico a (a + L)).filter fun n => Unbal θ k n).card : ℝ)
      ≤ t * (badWords θ k).card := by exact_mod_cast hc
    _ ≤ t * (2 ^ k * g k) := by gcongr; exact hW k
    _ = (t * 2 ^ k) * g k := by ring
    _ ≤ (L + 2 ^ k) * g k := by gcongr

/-- **The counting lemma.** In an interval of length `L`, the seeds unbalanced at some time
`k ∈ [k₀, K]` number at most `(L + B)·∑_{k ∈ [k₀, K]} g k`, provided `2^k ≤ B` on that range. -/
theorem card_window_le (a L k₀ K B : ℕ) (hB : ∀ k ∈ Icc k₀ K, 2 ^ k ≤ B) :
    (((Ico a (a + L)).filter (UnbalIn θ k₀ K)).card : ℝ)
      ≤ (L + B) * ∑ k ∈ Icc k₀ K, g k := by
  have hsub : (Ico a (a + L)).filter (UnbalIn θ k₀ K)
      ⊆ (Icc k₀ K).biUnion fun k => (Ico a (a + L)).filter fun n => Unbal θ k n := by
    intro n hn
    simp only [mem_filter, mem_biUnion, UnbalIn] at hn ⊢
    obtain ⟨hn, k, hk, hu⟩ := hn
    exact ⟨k, hk, hn, hu⟩
  calc (((Ico a (a + L)).filter (UnbalIn θ k₀ K)).card : ℝ)
      ≤ ∑ k ∈ Icc k₀ K, (((Ico a (a + L)).filter fun n => Unbal θ k n).card : ℝ) := by
        exact_mod_cast (card_le_card hsub).trans card_biUnion_le
    _ ≤ ∑ k ∈ Icc k₀ K, (L + B) * g k := by
        refine sum_le_sum fun k hk => (card_unbal_Ico_le θ g hW a L k).trans ?_
        have := nonneg_of_badWords hW k
        have : (2 : ℝ) ^ k ≤ B := by exact_mod_cast hB k hk
        gcongr
    _ = (L + B) * ∑ k ∈ Icc k₀ K, g k := by rw [mul_sum]

/-- A finite stretch of a summable nonnegative series is bounded by its tail. -/
theorem sum_Icc_le_tsum_tail (hg : Summable g) (k₀ K : ℕ) :
    ∑ k ∈ Icc k₀ K, g k ≤ ∑' i, g (i + k₀) := by
  have hg0 := nonneg_of_badWords hW
  rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  simp_rw [add_comm k₀]
  exact ((summable_nat_add_iff k₀).2 hg).sum_le_tsum _ fun i _ => hg0 _

/-- **Density form of the counting lemma.** If the unbalanced words of length `k` number at most
`2^k·g k` with `g` summable, then for every `h → ∞` the seeds unbalanced at some time
`k ∈ [h(n), λ(n)]` have natural density `0`. -/
theorem hasNatDensity_of_summable (hg : Summable g) {h : ℕ → ℕ} (hh : Tendsto h atTop atTop)
    [DecidablePred (· ∈ {n | ∃ k ∈ Icc (h n) (Nat.log 2 n + 1), Unbal θ k n})] :
    HasNatDensity {n | ∃ k ∈ Icc (h n) (Nat.log 2 n + 1), Unbal θ k n} 0 := by
  have hg0 := nonneg_of_badWords hW
  have htail := tendsto_sum_nat_add g
  unfold HasNatDensity
  refine tendsto_order.2 ⟨fun d hd => Eventually.of_forall fun N => lt_of_lt_of_le hd
    (by positivity), fun d hd => ?_⟩
  -- choose `k₀` with `3 · tail(k₀) < d/2`, then `M` with `h n ≥ k₀` for `n ≥ M`
  obtain ⟨k₀, hk₀⟩ := (eventually_atTop.1 ((tendsto_order.1 htail).2 (d / 6) (by linarith)))
  have hk₀' := hk₀ k₀ le_rfl
  obtain ⟨M, hM⟩ := eventually_atTop.1 (tendsto_atTop.1 hh k₀)
  filter_upwards [eventually_ge_atTop (M + 1), eventually_gt_atTop (⌈4 * M / d⌉₊)] with N hN hN'
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  -- seeds below `N` in `S`: either `< M`, or unbalanced at some `k ∈ [k₀, log₂ N + 1]`
  have hsub : (range N).filter (· ∈ {n | ∃ k ∈ Icc (h n) (Nat.log 2 n + 1), Unbal θ k n})
      ⊆ range M ∪
      (Ico 0 (0 + N)).filter (UnbalIn θ k₀ (Nat.log 2 N + 1)) := by
    intro n hn
    simp only [mem_filter, mem_range, Set.mem_ofPred_eq, mem_Icc] at hn
    obtain ⟨hnN, k, ⟨hk1, hk2⟩, hu⟩ := hn
    by_cases hnM : n < M
    · exact mem_union_left _ (mem_range.2 hnM)
    · refine mem_union_right _ ?_
      rw [mem_filter]
      refine ⟨by simp [hnN], k, mem_Icc.2 ⟨?_, ?_⟩, hu⟩
      · exact (hM n (by omega)).trans hk1
      · exact hk2.trans (by have := Nat.log_mono_right (b := 2) hnN.le; omega)
  have hB : ∀ k ∈ Icc k₀ (Nat.log 2 N + 1), 2 ^ k ≤ 2 * N := by
    intro k hk
    have h1 := Nat.pow_log_le_self 2 (show N ≠ 0 by omega)
    calc 2 ^ k ≤ 2 ^ (Nat.log 2 N + 1) := Nat.pow_le_pow_right (by norm_num) (mem_Icc.1 hk).2
      _ = 2 * 2 ^ Nat.log 2 N := by ring
      _ ≤ 2 * N := by omega
  have hw := card_window_le θ g hW 0 N k₀ (Nat.log 2 N + 1) (2 * N) hB
  have hs := sum_Icc_le_tsum_tail θ g hW hg k₀ (Nat.log 2 N + 1)
  have hcount : (natDensityCount {n | ∃ k ∈ Icc (h n) (Nat.log 2 n + 1), Unbal θ k n} N : ℝ)
      ≤ M + 3 * N * (d / 6) := by
    unfold natDensityCount
    have h1 := (card_le_card hsub).trans (card_union_le _ _)
    rw [card_range] at h1
    have hc : (((range N).filter
        (· ∈ {n | ∃ k ∈ Icc (h n) (Nat.log 2 n + 1), Unbal θ k n})).card : ℝ)
        ≤ M + (((Ico 0 (0 + N)).filter (UnbalIn θ k₀ (Nat.log 2 N + 1))).card : ℝ) := by
      exact_mod_cast h1
    have hpos : (0 : ℝ) ≤ N + 2 * N := by positivity
    have h2 : ((N : ℝ) + ((2 * N : ℕ) : ℝ)) * ∑ k ∈ Icc k₀ (Nat.log 2 N + 1), g k
        ≤ 3 * N * (d / 6) := by
      push_cast
      calc ((N : ℝ) + 2 * N) * ∑ k ∈ Icc k₀ (Nat.log 2 N + 1), g k
          ≤ (N + 2 * N) * ∑' i, g (i + k₀) := mul_le_mul_of_nonneg_left hs hpos
        _ ≤ 3 * N * (d / 6) := by nlinarith
    linarith
  have hMN : (M : ℝ) < d / 4 * N := by
    have h1 : (4 * M / d : ℝ) < N := (Nat.le_ceil _).trans_lt (by exact_mod_cast hN')
    rw [div_lt_iff₀ hd] at h1; linarith
  rw [div_lt_iff₀ hN0]
  nlinarith

end Counting

/-! ## Theorem 2 -/

theorem card_badWords_le_exp (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ((badWords (fun k => ε * k) k).card : ℝ) ≤ 2 ^ k * (2 * Real.exp (-2 * ε ^ 2 * k)) := by
  have := CoinTail.card_filter_abs_sub_gt_le k hε
  unfold badWords; linarith

theorem exp_neg_eq_pow (ε : ℝ) (k : ℕ) :
    Real.exp (-2 * ε ^ 2 * k) = Real.exp (-2 * ε ^ 2) ^ k := by
  rw [← Real.exp_nat_mul]; ring_nf

theorem summable_exp_neg {ε : ℝ} (hε : 0 < ε) :
    Summable fun k : ℕ => 2 * Real.exp (-2 * ε ^ 2 * k) := by
  simp_rw [exp_neg_eq_pow]
  refine (summable_geometric_of_lt_one (Real.exp_pos _).le ?_).mul_left 2
  rw [Real.exp_lt_one_iff]; nlinarith

/-- **Theorem 2(a) (the natural horizon).** For every `ε > 0` and every `h → ∞`, the seeds `n₀`
with `|S_k(n₀) - k/2| > εk` for some `k ∈ [h(n₀), λ(n₀)]` have natural density `0`. -/
@[category research solved, AMS 11 37, ref "Mat10", group "evgq17_m0_horizon"]
theorem hasNatDensity_unbalanced_below_horizon {h : ℕ → ℕ} (hh : Tendsto h atTop atTop)
    {ε : ℝ} (hε : 0 < ε) [DecidablePred (· ∈ {n | ∃ k ∈ Icc (h n) (Nat.log 2 n + 1),
      ε * k < |(numOddU k n : ℝ) - k / 2|})] :
    HasNatDensity {n | ∃ k ∈ Icc (h n) (Nat.log 2 n + 1),
      ε * k < |(numOddU k n : ℝ) - k / 2|} 0 :=
  by
    convert hasNatDensity_of_summable (fun k => ε * k) _ (fun k => card_badWords_le_exp k hε)
      (summable_exp_neg hε) hh
    all_goals exact Iff.rfl

/-- **Theorem 2(b) (window form).** In every interval of length `L`, at most `4L·q^{k₀}/(1-q)`
seeds, `q = e^{-2ε²}`, are unbalanced at some `k ∈ [k₀, log₂ L]`. -/
@[category research solved, AMS 11 37, ref "Mat10", group "evgq17_m0_horizon"]
theorem card_unbalanced_window_le (a L k₀ : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (((Ico a (a + L)).filter fun n => ∃ k ∈ Icc k₀ (Nat.log 2 L),
        ε * k < |(numOddU k n : ℝ) - k / 2|).card : ℝ)
      ≤ 4 * L * Real.exp (-2 * ε ^ 2) ^ k₀ / (1 - Real.exp (-2 * ε ^ 2)) := by
  set q := Real.exp (-2 * ε ^ 2)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by rw [Real.exp_lt_one_iff]; nlinarith
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp
  have hB : ∀ k ∈ Icc k₀ (Nat.log 2 L), 2 ^ k ≤ L := fun k hk =>
    (Nat.pow_le_pow_right (by norm_num) (mem_Icc.1 hk).2).trans
      (Nat.pow_log_le_self 2 (by omega))
  have hw := card_window_le (fun k => ε * k) (fun k => 2 * Real.exp (-2 * ε ^ 2 * k))
    (fun k => card_badWords_le_exp k hε) a L k₀ (Nat.log 2 L) L hB
  have hgeo : ∑ k ∈ Icc k₀ (Nat.log 2 L), 2 * Real.exp (-2 * ε ^ 2 * k)
      ≤ 2 * (q ^ k₀ / (1 - q)) := by
    simp_rw [exp_neg_eq_pow, ← mul_sum]
    gcongr
    rw [← Finset.Ico_add_one_right_eq_Icc]
    exact geom_sum_Ico_le_of_lt_one hq0 hq1
  have hL0 : (0 : ℝ) ≤ L + L := by positivity
  refine hw.trans ((mul_le_mul_of_nonneg_left hgeo hL0).trans (le_of_eq ?_))
  ring

/-! ## The envelope -/

theorem card_badWords_le_rpow {c : ℝ} (hc : 0 < c) (k : ℕ) :
    ((badWords (fun k => Real.sqrt (c * k * Real.log k)) k).card : ℝ)
      ≤ 2 ^ k * (2 * ((k : ℝ) ^ (-2 * c)) + if k ≤ 1 then 1 else 0) := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · -- `k ≤ 1`: at most `2^k` words in total
    have : ((badWords (fun k => Real.sqrt (c * k * Real.log k)) k).card : ℝ) ≤ 2 ^ k := by
      have := card_le_univ (badWords (fun k => Real.sqrt (c * k * Real.log k)) k)
      simp only [Fintype.card_pi, Fintype.card_bool, prod_const, card_univ,
        Fintype.card_fin] at this
      exact_mod_cast this
    have h0 : (0 : ℝ) ≤ 2 * ((k : ℝ) ^ (-2 * c)) := by positivity
    simp only [show k ≤ 1 by omega, ite_true]
    nlinarith [show (0 : ℝ) < 2 ^ k by positivity]
  · have hk1 : (1 : ℝ) < k := by exact_mod_cast hk
    have hk0 : (0 : ℝ) < k := by linarith
    have hlog : 0 < Real.log k := Real.log_pos hk1
    set t := Real.sqrt (c * k * Real.log k)
    have ht : 0 < t := Real.sqrt_pos.2 (by positivity)
    have hε : 0 < t / k := by positivity
    have := CoinTail.card_filter_abs_sub_gt_le k hε
    have he : t / k * k = t := by field_simp
    have hexp : Real.exp (-2 * (t / k) ^ 2 * k) = (k : ℝ) ^ (-2 * c) := by
      rw [Real.rpow_def_of_pos hk0]
      congr 1
      rw [div_pow, Real.sq_sqrt (by positivity)]
      field_simp
    simp only [he, hexp] at this
    simp only [show ¬ k ≤ 1 by omega, ite_false, add_zero]
    unfold badWords; linarith

/-- **Theorem 2(c) (envelope).** For every `c > 1/2` and every `h → ∞`, the seeds `n₀` with
`|S_k(n₀) - k/2| > √(c·k·ln k)` for some `k ∈ [h(n₀), λ(n₀)]` have natural density `0`. -/
@[category research solved, AMS 11 37, ref "Mat10", group "evgq17_m0_horizon"]
theorem hasNatDensity_envelope_below_horizon {h : ℕ → ℕ} (hh : Tendsto h atTop atTop)
    {c : ℝ} (hc : 1 / 2 < c) [DecidablePred (· ∈ {n | ∃ k ∈ Icc (h n) (Nat.log 2 n + 1),
      Real.sqrt (c * k * Real.log k) < |(numOddU k n : ℝ) - k / 2|})] :
    HasNatDensity {n | ∃ k ∈ Icc (h n) (Nat.log 2 n + 1),
      Real.sqrt (c * k * Real.log k) < |(numOddU k n : ℝ) - k / 2|} 0 := by
  have hs : Summable fun k : ℕ => 2 * ((k : ℝ) ^ (-2 * c)) + if k ≤ 1 then 1 else 0 := by
    refine ((Real.summable_nat_rpow.2 (by linarith)).mul_left 2).add ?_
    refine summable_of_ne_finset_zero (s := range 2) fun k hk => ?_
    simp only [mem_range, not_lt] at hk
    simp [show ¬ k ≤ 1 by omega]
  convert hasNatDensity_of_summable (fun k => Real.sqrt (c * k * Real.log k)) _
    (card_badWords_le_rpow (by linarith)) hs hh
  all_goals exact Iff.rfl

end EVG25.M0
