/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CC.Decomposition
import RT.CRozLemma32
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The exact product identity (Rozier–Terracol Theorem 4.2★)

This file formalizes the harmonic-mean-free **exact product identity** underlying
Theorem 4.2 of [Roz25], together with the harmonic-mean forms of Theorem 4.2 and
Corollaries 4.3, 4.4 derived from it.

For a positive integer `n` and `j ≥ 0`, write `q = qⱼ(n)` for the number of odd terms
among `n, T(n), …, T^{j-1}(n)`, and let `m₀, …, m_{q-1}` be those odd terms.  With
`C = Cⱼ(n) = 3^q / 2^j` and `E = Eⱼ(n)` the linear-decomposition data
(`T^j(n) = C·n + E`), the identity is

  `1 + E / (C·n) = ∏ₖ (1 + 1/(3 mₖ))`.                            (`correction_exact_product`)

This mentions no mean at all and is strictly stronger than the paper's Theorem 4.2
upper bound, which is recovered from it by AM–GM (using the harmonic mean `h` of the
`mₖ`); the min-term bound `RT.correction_ratio_bound_theorem_4_1` is recovered by the
worst-case factor `1 + 1/(3mₖ) ≤ 1 + 1/(3m)`.

* [Eli93] S. Eliahou, "The 3x+1 problem: new lower bounds on nontrivial cycle lengths."
* [Roz25] Rozier, Olivier, and Claude Terracol. "Paradoxical behavior in Collatz sequences."
  arXiv preprint arXiv:2502.00948 (2025). Theorem 4.2, Corollaries 4.3, 4.4.
-/

open Classical

open CC

namespace RT

/-- The multiplicative factor contributed by the iterate `x = Tᵏ(n)` to the exact product
    identity: `1 + 1/(3x)` when `x` is odd, and `1` when `x` is even. -/
@[category API, AMS 11 37, ref "Roz25", group "roz_thm_42"]
def oddFactor (x : ℕ) : ℚ := if x % 2 = 1 then 1 + 1 / (3 * (x : ℚ)) else 1

@[category API, AMS 11 37, ref "Roz25", group "roz_thm_42"]
lemma oddFactor_even {x : ℕ} (h : x % 2 = 0) : oddFactor x = 1 := by
  simp [oddFactor, h]

@[category API, AMS 11 37, ref "Roz25", group "roz_thm_42"]
lemma oddFactor_odd {x : ℕ} (h : x % 2 = 1) : oddFactor x = 1 + 1 / (3 * (x : ℚ)) := by
  simp [oddFactor, h]

@[category API, AMS 11 37, ref "Roz25", group "roz_thm_42"]
lemma one_le_oddFactor (x : ℕ) : 1 ≤ oddFactor x := by
  unfold oddFactor
  split
  · have : (0 : ℚ) ≤ 1 / (3 * (x : ℚ)) := by positivity
    linarith
  · exact le_refl 1

@[category API, AMS 11 37, ref "Roz25", group "roz_thm_42"]
lemma oddFactor_pos (x : ℕ) : 0 < oddFactor x := lt_of_lt_of_le one_pos (one_le_oddFactor x)

/-- **The engine.** `T^j(n)` equals `n · Cⱼ(n)` times the running product of odd-term factors.
    Proved by induction on `j`, tracking `T^{k+1}/T^k = 1/2` (even step) or
    `(3/2)(1 + 1/(3·Tᵏ))` (odd step). -/
@[category API, AMS 11 37, ref "Roz25", group "roz_thm_42"]
theorem T_iter_eq_prod (j n : ℕ) :
    (T_iter j n : ℚ) = (n : ℚ) * C j n * ∏ k ∈ Finset.range j, oddFactor (T_iter k n) := by
  induction j with
  | zero => simp [C, num_odd_steps, T_iter]
  | succ j ih =>
    rw [Finset.prod_range_succ]
    set P := ∏ k ∈ Finset.range j, oddFactor (T_iter k n) with hP
    by_cases hodd : T_iter j n % 2 = 1
    · -- odd step
      have ht_pos : (0 : ℚ) < (T_iter j n : ℚ) := by exact_mod_cast (by omega : 0 < T_iter j n)
      have ht_ne : (T_iter j n : ℚ) ≠ 0 := ne_of_gt ht_pos
      have hToddQ : (T (T_iter j n) : ℚ) = (3 * (T_iter j n : ℚ) + 1) / 2 := by
        rw [T_odd hodd, Nat.cast_div (by omega : 2 ∣ 3 * T_iter j n + 1) (by norm_num : (2 : ℚ) ≠ 0)]
        push_cast; ring
      have hof : oddFactor (T_iter j n) = 1 + 1 / (3 * (T_iter j n : ℚ)) := oddFactor_odd hodd
      have hC_succ : C (j + 1) n = C j n * 3 / 2 := by
        unfold C
        rw [num_odd_steps_succ, X_odd hodd, pow_succ, pow_succ]
        ring
      show (T (T_iter j n) : ℚ) = (n : ℚ) * C (j + 1) n * (P * oddFactor (T_iter j n))
      calc (T (T_iter j n) : ℚ)
          = (3 * (T_iter j n : ℚ) + 1) / 2 := hToddQ
        _ = (T_iter j n : ℚ) * (3 / 2 * oddFactor (T_iter j n)) := by rw [hof]; field_simp
        _ = ((n : ℚ) * C j n * P) * (3 / 2 * oddFactor (T_iter j n)) := by rw [ih]
        _ = (n : ℚ) * C (j + 1) n * (P * oddFactor (T_iter j n)) := by rw [hC_succ]; ring
    · -- even step
      have heven : T_iter j n % 2 = 0 := by omega
      have hTevenQ : (T (T_iter j n) : ℚ) = (T_iter j n : ℚ) / 2 := by
        rw [T_even heven, Nat.cast_div (by omega : 2 ∣ T_iter j n) (by norm_num : (2 : ℚ) ≠ 0)]
        norm_num
      have hof : oddFactor (T_iter j n) = 1 := oddFactor_even heven
      have hC_succ : C (j + 1) n = C j n / 2 := by
        unfold C
        rw [num_odd_steps_succ, X_even heven, add_zero, pow_succ]
        ring
      show (T (T_iter j n) : ℚ) = (n : ℚ) * C (j + 1) n * (P * oddFactor (T_iter j n))
      calc (T (T_iter j n) : ℚ)
          = (T_iter j n : ℚ) / 2 := hTevenQ
        _ = ((n : ℚ) * C j n * P) / 2 := by rw [ih]
        _ = (n : ℚ) * (C j n / 2) * (P * 1) := by ring
        _ = (n : ℚ) * C (j + 1) n * (P * oddFactor (T_iter j n)) := by rw [hC_succ, hof]

/-- **Theorem 4.2★** (Rozier–Terracol, exact and harmonic-mean-free). With `m₀, …, m_{q-1}`
    the odd terms of `Ω_{j-1}(n)`, the correction ratio satisfies

    `1 + Eⱼ(n) / (Cⱼ(n) · n) = ∏ₖ (1 + 1/(3 mₖ))`.

    This is the exact identity used inside the proof of Theorem 4.2; it is strictly stronger
    than the paper's harmonic-mean upper bound and implies the min-term bound. -/
@[category research solved, AMS 11 37, ref "Roz25" "Eli93", group "roz_thm_42"]
theorem correction_exact_product (j n : ℕ) (hn : 0 < n) :
    1 + E j n / (C j n * (n : ℚ)) = ∏ k ∈ Finset.range j, oddFactor (T_iter k n) := by
  have hCpos : (0 : ℚ) < C j n := by unfold C; positivity
  have hnne : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hCne : C j n ≠ 0 := ne_of_gt hCpos
  have hLD : (T_iter j n : ℚ) = C j n * n + E j n := linear_decomposition' j n
  have hProd : (T_iter j n : ℚ) =
      (n : ℚ) * C j n * ∏ k ∈ Finset.range j, oddFactor (T_iter k n) := T_iter_eq_prod j n
  have hE : E j n = C j n * (n : ℚ) * (∏ k ∈ Finset.range j, oddFactor (T_iter k n) - 1) := by
    have hcombine : C j n * (n : ℚ) + E j n =
        (n : ℚ) * C j n * ∏ k ∈ Finset.range j, oddFactor (T_iter k n) := by rw [← hLD, hProd]
    linear_combination hcombine
  rw [hE]
  field_simp
  ring

/-- The paradoxical criterion (paper eq. (9)): if `Ωⱼ(n)` is paradoxical then
    `0 < 1 - C ≤ E/n`. -/
@[category API, AMS 11 37, ref "Roz25", group "roz_thm_42"]
lemma isParadoxical_bound {j n : ℕ} (hn : n > 0) (h : IsParadoxical j n) :
    0 < 1 - C j n ∧ 1 - C j n ≤ E j n / n :=
  ⟨by linarith [h.2], by
    have hnq : (n : ℚ) > 0 := by positivity
    rw [le_div_iff₀ hnq]
    have hd := linear_decomposition' j n
    have ht : (n : ℚ) ≤ T_iter j n := by exact_mod_cast h.1
    nlinarith⟩

/-- The set of indices `k < j` at which the iterate `Tᵏ(n)` is odd. -/
@[category API, AMS 11 37, ref "Roz25", group "roz_thm_42"]
def oddIdx (j n : ℕ) : Finset ℕ := (Finset.range j).filter (fun k => T_iter k n % 2 = 1)

/-- The odd-index set has exactly `q = num_odd_steps j n` elements. -/
@[category API, AMS 11 37, ref "Roz25", group "roz_thm_42"]
lemma oddIdx_card (j n : ℕ) : (oddIdx j n).card = num_odd_steps j n := by
  unfold oddIdx num_odd_steps
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [X_eq_mod]
  split <;> omega

/-- The product over `range j` collapses to the product over the odd indices, since even
    iterates contribute a factor `1`. -/
@[category API, AMS 11 37, ref "Roz25", group "roz_thm_42"]
lemma prod_range_oddFactor_eq_oddIdx (j n : ℕ) :
    ∏ k ∈ Finset.range j, oddFactor (T_iter k n) = ∏ k ∈ oddIdx j n, oddFactor (T_iter k n) := by
  symm
  apply Finset.prod_subset (Finset.filter_subset _ _)
  intro k hk hk_not
  simp only [Finset.mem_filter, not_and] at hk_not
  exact oddFactor_even (by have := hk_not hk; omega)

/-- **AM–GM inequality** (unweighted, product form): for nonnegative reals over a nonempty
    finset, the product is at most the arithmetic mean raised to the cardinality. -/
@[category API, AMS 26, ref "Roz25", group "roz_thm_42"]
theorem geom_mean_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i)
    (hs : s.Nonempty) :
    ∏ i ∈ s, f i ≤ ((∑ i ∈ s, f i) / s.card) ^ s.card := by
  have hcard : 0 < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hs
  have hcard_ne : (s.card : ℝ) ≠ 0 := ne_of_gt hcard
  have hprod_nonneg : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg hf
  have key := Real.geom_mean_le_arith_mean s (fun _ => 1) f
      (fun i _ => zero_le_one) (by simpa using hcard) hf
  simp only [Real.rpow_one, one_mul, Finset.sum_const, nsmul_eq_mul, mul_one] at key
  calc ∏ i ∈ s, f i
      = ((∏ i ∈ s, f i) ^ ((s.card : ℝ)⁻¹)) ^ s.card := by
        rw [← Real.rpow_natCast ((∏ i ∈ s, f i) ^ ((s.card : ℝ)⁻¹)) s.card,
            ← Real.rpow_mul hprod_nonneg, inv_mul_cancel₀ hcard_ne, Real.rpow_one]
    _ ≤ ((∑ i ∈ s, f i) / s.card) ^ s.card := by gcongr

/-! ### The harmonic mean and the harmonic-mean forms of Theorem 4.2 -/

/-- Sum of reciprocals of the odd terms of `Ω_{j-1}(n)`. -/
@[category API, AMS 11 37, ref "Roz25", group "roz_thm_42"]
noncomputable def recipSum (j n : ℕ) : ℝ := ∑ k ∈ oddIdx j n, 1 / (T_iter k n : ℝ)

/-- The harmonic mean `h` of the odd terms of `Ω_{j-1}(n)`: `q / Σ (1/mₖ)`. -/
@[category API, AMS 11 37, ref "Roz25", group "roz_thm_42"]
noncomputable def harmonicMean (j n : ℕ) : ℝ := (num_odd_steps j n : ℝ) / recipSum j n

@[category API, AMS 11 37, ref "Roz25", group "roz_thm_42"]
lemma recipSum_pos (j n : ℕ) (hn : 0 < n) (hq : 0 < num_odd_steps j n) : 0 < recipSum j n := by
  refine Finset.sum_pos (fun k _ => ?_) (Finset.card_pos.mp (by rw [oddIdx_card]; exact hq))
  exact div_pos one_pos (by exact_mod_cast T_iter_pos hn k)

@[category API, AMS 11 37, ref "Roz25", group "roz_thm_42"]
lemma harmonicMean_pos (j n : ℕ) (hn : 0 < n) (hq : 0 < num_odd_steps j n) :
    0 < harmonicMean j n :=
  div_pos (by exact_mod_cast hq) (recipSum_pos j n hn hq)

/-- The sum of the odd-term factors equals `q + (1/3)·Σ(1/mₖ)`. -/
@[category API, AMS 11 37, ref "Roz25", group "roz_thm_42"]
lemma sum_oddFactor_eq (j n : ℕ) :
    ∑ k ∈ oddIdx j n, ((oddFactor (T_iter k n) : ℚ) : ℝ)
      = (num_odd_steps j n : ℝ) + (1 / 3) * recipSum j n := by
  have hcard : (num_odd_steps j n : ℝ) = ∑ _k ∈ oddIdx j n, (1 : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, oddIdx_card]
  rw [hcard, recipSum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  simp only [oddIdx, Finset.mem_filter] at hk
  rw [oddFactor_odd hk.2]
  push_cast
  ring

/-- The exact product is bounded above by the harmonic-mean factor raised to `q` (AM–GM). -/
@[category API, AMS 11 37, ref "Roz25" "Eli93", group "roz_thm_42"]
theorem prod_oddFactor_le_harmonic (j n : ℕ) (hn : 0 < n) (hq : 0 < num_odd_steps j n) :
    ∏ k ∈ Finset.range j, ((oddFactor (T_iter k n) : ℚ) : ℝ)
      ≤ (1 + 1 / (3 * harmonicMean j n)) ^ num_odd_steps j n := by
  have hne : (oddIdx j n).Nonempty := Finset.card_pos.mp (by rw [oddIdx_card]; exact hq)
  have hf : ∀ k ∈ oddIdx j n, (0 : ℝ) ≤ ((oddFactor (T_iter k n) : ℚ) : ℝ) :=
    fun k _ => by exact_mod_cast (oddFactor_pos (T_iter k n)).le
  have hgm := geom_mean_le (oddIdx j n) (fun k => ((oddFactor (T_iter k n) : ℚ) : ℝ)) hf hne
  rw [oddIdx_card] at hgm
  have hcast : ∏ k ∈ Finset.range j, ((oddFactor (T_iter k n) : ℚ) : ℝ)
      = ∏ k ∈ oddIdx j n, ((oddFactor (T_iter k n) : ℚ) : ℝ) := by
    rw [← Rat.cast_prod, ← Rat.cast_prod, prod_range_oddFactor_eq_oddIdx]
  rw [hcast]
  refine le_trans hgm (le_of_eq ?_)
  congr 1
  rw [sum_oddFactor_eq]
  unfold harmonicMean
  have hrs : recipSum j n ≠ 0 := ne_of_gt (recipSum_pos j n hn hq)
  have hqR : (num_odd_steps j n : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  field_simp

/-- **Theorem 4.2** (Rozier–Terracol, upper bound, harmonic-mean form). Derived from the exact
    product identity `correction_exact_product` by AM–GM.  With `h` the harmonic mean of the odd
    terms of `Ω_{j-1}(n)` and `q = qⱼ(n) > 0`,

    `Eⱼ(n) / n ≤ ((3 + h⁻¹)^q − 3^q) / 2^j`.

    (The lower bound `1 − C ≤ E/n`, valid when `Ωⱼ(n)` is paradoxical, is `isParadoxical_bound`.) -/
@[category research solved, AMS 11 37, ref "Roz25" "Eli93", group "roz_thm_42"]
theorem correction_ratio_bound_harmonic (j n : ℕ) (hn : 0 < n) (hq : 0 < num_odd_steps j n) :
    (E j n : ℝ) / (n : ℝ)
      ≤ ((3 + 1 / harmonicMean j n) ^ num_odd_steps j n - 3 ^ num_odd_steps j n) / 2 ^ j := by
  have hh_pos : 0 < harmonicMean j n := harmonicMean_pos j n hn hq
  have hh_ne : harmonicMean j n ≠ 0 := ne_of_gt hh_pos
  have hCpos : (0 : ℝ) < (C j n : ℝ) := by
    have h0 : (0 : ℚ) < C j n := by unfold C; positivity
    exact_mod_cast h0
  have hCne : (C j n : ℝ) ≠ 0 := ne_of_gt hCpos
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hCEP := congrArg (fun x : ℚ => (x : ℝ)) (correction_exact_product j n hn)
  push_cast at hCEP
  have hAMGM := prod_oddFactor_le_harmonic j n hn hq
  have hEC : (E j n : ℝ) / ((C j n : ℝ) * (n : ℝ))
      ≤ (1 + 1 / (3 * harmonicMean j n)) ^ num_odd_steps j n - 1 := by
    have hstep1 : 1 + (E j n : ℝ) / ((C j n : ℝ) * (n : ℝ))
        ≤ (1 + 1 / (3 * harmonicMean j n)) ^ num_odd_steps j n := by rw [hCEP]; exact hAMGM
    linarith
  have hEn : (E j n : ℝ) / (n : ℝ) = (C j n : ℝ) * ((E j n : ℝ) / ((C j n : ℝ) * (n : ℝ))) := by
    field_simp
  rw [hEn]
  calc (C j n : ℝ) * ((E j n : ℝ) / ((C j n : ℝ) * (n : ℝ)))
      ≤ (C j n : ℝ) * ((1 + 1 / (3 * harmonicMean j n)) ^ num_odd_steps j n - 1) :=
        mul_le_mul_of_nonneg_left hEC (le_of_lt hCpos)
    _ = ((3 + 1 / harmonicMean j n) ^ num_odd_steps j n - 3 ^ num_odd_steps j n) / 2 ^ j := by
        have hCval : (C j n : ℝ) = (3 : ℝ) ^ num_odd_steps j n / (2 : ℝ) ^ j := by
          unfold C; push_cast; ring
        have hbase : (3 : ℝ) * (1 + 1 / (3 * harmonicMean j n)) = 3 + 1 / harmonicMean j n := by
          field_simp
        have hpow : (3 : ℝ) ^ num_odd_steps j n * (1 + 1 / (3 * harmonicMean j n)) ^ num_odd_steps j n
            = (3 + 1 / harmonicMean j n) ^ num_odd_steps j n := by
          rw [← mul_pow, hbase]
        rw [hCval, mul_sub, mul_one, div_mul_eq_mul_div, hpow, ← sub_div]

/-! ### Real-analytic cores (parametrised by a positive real lower bound `μ`)

These generalize the lower bound on the odd terms from a natural number to an arbitrary positive
real `μ`, so that both the harmonic-mean forms (with `μ = h`) below and the min-term forms
(`RT.paradoxical_ratio_bounds`, `RT.paradoxical_m_bound`, with `μ = m`) reuse them. -/

/-- The ones-ratio `q/j` is squeezed between `log 2 / log(3 + μ⁻¹)` and `log 2 / log 3`, given the
    paradoxical lower bound and an upper bound on `E/n` of the `μ`-shape. -/
@[category API, AMS 11 37, ref "Roz25", group "roz_cor_43"]
lemma paradoxical_ratio_real (j q : ℕ) (μ : ℝ) (hj_pos : j > 0) (hμ : 0 < μ)
    (h_para : (1 : ℝ) - (3 : ℝ) ^ q / (2 : ℝ) ^ j > 0)
    (h_E : (1 : ℝ) - (3 : ℝ) ^ q / (2 : ℝ) ^ j ≤ ((3 + 1 / μ) ^ q - (3 : ℝ) ^ q) / (2 : ℝ) ^ j) :
    Real.log 2 / Real.log (3 + 1 / μ) ≤ (q : ℝ) / (j : ℝ) ∧
    (q : ℝ) / (j : ℝ) < Real.log 2 / Real.log 3 := by
  have hjR_pos : (j : ℝ) > 0 := by exact_mod_cast hj_pos
  have h2j_pos : (0 : ℝ) < 2 ^ j := by positivity
  -- Upper bound
  have h_upper1 : (3 : ℝ) ^ q / (2 : ℝ) ^ j < 1 := by linarith
  have h_upper2 : (3 : ℝ) ^ q < (2 : ℝ) ^ j := (div_lt_one (by positivity)).mp h_upper1
  have h_upper3 : Real.log ((3 : ℝ) ^ q) < Real.log ((2 : ℝ) ^ j) :=
    Real.log_lt_log (by positivity) h_upper2
  rw [Real.log_pow, Real.log_pow] at h_upper3
  have hlog3_pos : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have h_upper_final : (q : ℝ) / (j : ℝ) < Real.log 2 / Real.log 3 := by
    rw [div_lt_div_iff₀ hjR_pos hlog3_pos]; linarith
  -- Lower bound
  have h_lower1 : (2 : ℝ) ^ j - (3 : ℝ) ^ q ≤ (3 + 1 / μ) ^ q - (3 : ℝ) ^ q := by
    have h_times : ((1 : ℝ) - (3 : ℝ) ^ q / (2 : ℝ) ^ j) * (2 : ℝ) ^ j ≤
        (((3 + 1 / μ) ^ q - (3 : ℝ) ^ q) / (2 : ℝ) ^ j) * (2 : ℝ) ^ j :=
      mul_le_mul_of_nonneg_right h_E (by positivity)
    have hr1 : ((1 : ℝ) - (3 : ℝ) ^ q / (2 : ℝ) ^ j) * (2 : ℝ) ^ j = (2 : ℝ) ^ j - (3 : ℝ) ^ q := by
      calc ((1 : ℝ) - (3 : ℝ) ^ q / (2 : ℝ) ^ j) * (2 : ℝ) ^ j
        _ = 1 * (2 : ℝ) ^ j - ((3 : ℝ) ^ q / (2 : ℝ) ^ j) * (2 : ℝ) ^ j := by ring
        _ = (2 : ℝ) ^ j - (3 : ℝ) ^ q := by rw [one_mul, div_mul_cancel₀ _ (by positivity)]
    have hr2 : (((3 + 1 / μ) ^ q - (3 : ℝ) ^ q) / (2 : ℝ) ^ j) * (2 : ℝ) ^ j =
        (3 + 1 / μ) ^ q - (3 : ℝ) ^ q := div_mul_cancel₀ _ (by positivity)
    linarith
  have h_lower2 : (2 : ℝ) ^ j ≤ (3 + 1 / μ) ^ q := by linarith
  have h_lower3 : Real.log ((2 : ℝ) ^ j) ≤ Real.log ((3 + 1 / μ) ^ q) :=
    Real.log_le_log (by positivity) h_lower2
  rw [Real.log_pow, Real.log_pow] at h_lower3
  have hlog3m_pos : (0 : ℝ) < Real.log (3 + 1 / μ) := by
    apply Real.log_pos; have : (0 : ℝ) < 1 / μ := one_div_pos.mpr hμ; linarith
  have h_lower_final : Real.log 2 / Real.log (3 + 1 / μ) ≤ (q : ℝ) / (j : ℝ) := by
    rw [le_div_iff₀ hjR_pos, div_mul_eq_mul_div, div_le_iff₀ hlog3m_pos]; linarith
  exact ⟨h_lower_final, h_upper_final⟩

@[category API, AMS 11, ref "Roz25", group "roz_cor_44"]
lemma log_ratio_not_int (j k : ℕ) (hj_ge_2 : j ≥ 2) :
    (j : ℝ) * Real.log 2 / Real.log 3 ≠ (k : ℝ) := by
  intro h
  have h1 : ξ = (k : ℝ) / (j : ℝ) := by
    calc ξ = Real.log 2 / Real.log 3 := rfl
         _ = ((j : ℝ) * Real.log 2 / Real.log 3) / (j : ℝ) := by
           rw [mul_div_assoc]
           exact (mul_div_cancel_left₀ _ (by exact_mod_cast (by omega : j ≠ 0))).symm
         _ = (k : ℝ) / (j : ℝ) := by rw [h]
  have h2 : (k : ℝ) / (j : ℝ) = (((k : ℚ) / (j : ℚ) : ℚ) : ℝ) := by push_cast; rfl
  rw [h2] at h1
  exact irrational_xi ⟨(k : ℚ) / (j : ℚ), h1.symm⟩

@[category API, AMS 11, ref "Roz25", group "roz_cor_44"]
lemma strict_floor_log_ratio (j : ℕ) (hj_ge_2 : j ≥ 2) :
    ((⌊(j : ℝ) * Real.log 2 / Real.log 3⌋ : ℤ) : ℝ) < (j : ℝ) * Real.log 2 / Real.log 3 := by
  have h_le := Int.floor_le ((j : ℝ) * Real.log 2 / Real.log 3)
  have h_ne : ((⌊(j : ℝ) * Real.log 2 / Real.log 3⌋ : ℤ) : ℝ) ≠ (j : ℝ) * Real.log 2 / Real.log 3 := by
    set k_int := ⌊(j : ℝ) * Real.log 2 / Real.log 3⌋
    by_cases hpos : k_int < 0
    · have h_j_pos : (0 : ℝ) < j := by exact_mod_cast (by omega : j > 0)
      have h1 : (0 : ℝ) < (j : ℝ) * Real.log 2 / Real.log 3 := by positivity
      have h2 : ((k_int : ℤ) : ℝ) < 0 := by exact_mod_cast hpos
      linarith
    · push Not at hpos
      obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = k_int := ⟨k_int.toNat, Int.toNat_of_nonneg hpos⟩
      rw [← hk]; push_cast
      exact (log_ratio_not_int j k hj_ge_2).symm
  exact lt_of_le_of_ne h_le h_ne

/-- The `μ`-lower-bound version, phrased with the ratio `j/q`. -/
@[category API, AMS 11 37, ref "Roz25", group "roz_cor_44"]
lemma paradoxical_m_bound_q_real (j q : ℕ) (μ : ℝ) (hj_pos : j > 0) (hq_pos : q > 0) (hμ : 0 < μ)
    (h_ratio_lower : Real.log 2 / Real.log (3 + 1 / μ) ≤ (q : ℝ) / (j : ℝ))
    (h_ratio_upper : (q : ℝ) / (j : ℝ) < Real.log 2 / Real.log 3) :
    (2 : ℝ) ^ ((j : ℝ) / (q : ℝ)) - 3 > 0 ∧
    μ ≤ 1 / ((2 : ℝ) ^ ((j : ℝ) / (q : ℝ)) - 3) := by
  have hj : (j : ℝ) > 0 := by exact_mod_cast hj_pos
  have hq : (q : ℝ) > 0 := by exact_mod_cast hq_pos
  have hlogm : Real.log (3 + 1 / μ) > 0 := by
    apply Real.log_pos; have : (0 : ℝ) < 1 / μ := one_div_pos.mpr hμ; linarith
  have hlog3 : Real.log 3 > 0 := Real.log_pos (by norm_num)
  have h_denom_pos : (2 : ℝ) ^ ((j : ℝ) / (q : ℝ)) > 3 := by
    have h1 : (q : ℝ) * Real.log 3 < (j : ℝ) * Real.log 2 := by
      have htemp : (q : ℝ) * Real.log 3 < Real.log 2 * (j : ℝ) := (div_lt_div_iff₀ hj hlog3).mp h_ratio_upper
      rwa [mul_comm (Real.log 2) _] at htemp
    have h2 : Real.log 3 < ((j : ℝ) / (q : ℝ)) * Real.log 2 := by
      have htemp : Real.log 3 < (j : ℝ) * Real.log 2 / (q : ℝ) := (lt_div_iff₀' hq).mpr h1
      rwa [mul_comm, ← mul_div_assoc, mul_comm]
    have h3 : Real.log 3 < Real.log ((2 : ℝ) ^ ((j : ℝ) / (q : ℝ))) := by
      have h_pow' : Real.log ((2 : ℝ) ^ ((j : ℝ) / (q : ℝ))) = ((j : ℝ) / (q : ℝ)) * Real.log 2 :=
        Real.log_rpow (by norm_num) _
      rwa [← h_pow'] at h2
    have h2pow_pos : (0 : ℝ) < (2 : ℝ) ^ ((j : ℝ) / (q : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    exact (Real.log_lt_log_iff (by norm_num) h2pow_pos).mp h3
  have h_denom_gt_0 : (2 : ℝ) ^ ((j : ℝ) / (q : ℝ)) - 3 > 0 := by linarith
  have h3m : ((j : ℝ) / (q : ℝ)) * Real.log 2 ≤ Real.log (3 + 1 / μ) := by
    have h1 := (div_le_div_iff₀ hlogm hj).mp h_ratio_lower
    rw [show ((j : ℝ) / (q : ℝ)) * Real.log 2 = Real.log 2 * (j : ℝ) / (q : ℝ) from by ring]
    exact (div_le_iff₀ hq).mpr (by nlinarith)
  have h4m : Real.log ((2 : ℝ) ^ ((j : ℝ) / (q : ℝ))) ≤ Real.log (3 + 1 / μ) := by
    rw [Real.log_rpow (by norm_num) _]; exact h3m
  have h5m : (2 : ℝ) ^ ((j : ℝ) / (q : ℝ)) ≤ 3 + 1 / μ := by
    have h2pow_pos : (0 : ℝ) < (2 : ℝ) ^ ((j : ℝ) / (q : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    have h3M_pos : (0 : ℝ) < 3 + 1 / μ := by positivity
    exact (Real.log_le_log_iff h2pow_pos h3M_pos).mp h4m
  have h6m : (2 : ℝ) ^ ((j : ℝ) / (q : ℝ)) - 3 ≤ 1 / μ := by linarith
  have h_bound : μ ≤ 1 / ((2 : ℝ) ^ ((j : ℝ) / (q : ℝ)) - 3) := by
    rw [le_div_iff₀ h_denom_gt_0]
    have h7 := mul_le_mul_of_nonneg_left h6m (le_of_lt hμ)
    have h8 : μ * (1 / μ) = 1 := by field_simp
    linarith
  exact ⟨h_denom_gt_0, h_bound⟩

/-- The `μ`-lower-bound version, phrased with `r = j / ⌊(log2/log3) j⌋`. -/
@[category API, AMS 11 37, ref "Roz25", group "roz_cor_44"]
lemma paradoxical_m_bound_floor_real (j q : ℕ) (μ : ℝ) (hj_ge_2 : j ≥ 2) (hμ : 0 < μ)
    (h_q_bounds : Real.log 2 / Real.log (3 + 1 / μ) ≤ (q : ℝ) / (j : ℝ) ∧
                  (q : ℝ) / (j : ℝ) < Real.log 2 / Real.log 3) :
    let r := (j : ℝ) / ⌊(j : ℝ) * Real.log 2 / Real.log 3⌋
    (2 : ℝ) ^ r - 3 > 0 ∧ μ ≤ 1 / ((2 : ℝ) ^ r - 3) := by
  have hj_pos : j > 0 := by omega
  have hj : (j : ℝ) > 0 := by exact_mod_cast hj_pos
  have hq_pos : q > 0 := by
    by_contra h0
    have hz : q = 0 := by omega
    subst hz
    have hc : Real.log 2 / Real.log (3 + 1 / μ) ≤ 0 := by
      have : (0 : ℝ) / (j : ℝ) = 0 := zero_div _
      linarith [h_q_bounds.1]
    have hc2 : Real.log 2 / Real.log (3 + 1 / μ) > 0 := by
      have h2 : Real.log 2 > 0 := Real.log_pos (by norm_num)
      have h_logm : (0 : ℝ) < Real.log (3 + 1 / μ) := by
        apply Real.log_pos; have : (0 : ℝ) < 1 / μ := one_div_pos.mpr hμ; linarith
      positivity
    linarith
  have h_q_real := paradoxical_m_bound_q_real j q μ hj_pos hq_pos hμ h_q_bounds.1 h_q_bounds.2
  have ht : (q : ℝ) < (j : ℝ) * Real.log 2 / Real.log 3 := by
    have hlog3_pos := Real.log_pos (show (1 : ℝ) < 3 by norm_num)
    have h := (div_lt_div_iff₀ hj hlog3_pos).mp h_q_bounds.2
    exact (lt_div_iff₀ hlog3_pos).mpr (by nlinarith)
  have ht_z : ((q : ℤ) : ℝ) ≤ (j : ℝ) * Real.log 2 / Real.log 3 := le_of_lt (by exact_mod_cast ht)
  have h_floor : (q : ℤ) ≤ ⌊(j : ℝ) * Real.log 2 / Real.log 3⌋ := Int.le_floor.mpr ht_z
  have hq_le : (q : ℝ) ≤ ⌊(j : ℝ) * Real.log 2 / Real.log 3⌋ := by exact_mod_cast h_floor
  set r := (j : ℝ) / ⌊(j : ℝ) * Real.log 2 / Real.log 3⌋
  have hf_strict := strict_floor_log_ratio j hj_ge_2
  have h_floor_pos : (0 : ℝ) < ⌊(j : ℝ) * Real.log 2 / Real.log 3⌋ := by
    have hq_real_pos : (0 : ℝ) < q := by exact_mod_cast hq_pos
    calc (0 : ℝ) < (q : ℝ) := hq_real_pos
         _ ≤ ⌊(j : ℝ) * Real.log 2 / Real.log 3⌋ := hq_le
  have hq_real_pos : (q : ℝ) > 0 := by exact_mod_cast hq_pos
  have h_r_ge : r ≤ (j : ℝ) / (q : ℝ) := div_le_div_of_nonneg_left (le_of_lt hj) hq_real_pos hq_le
  have h_denom : (2 : ℝ) ^ r ≤ (2 : ℝ) ^ ((j : ℝ) / (q : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h_r_ge
  have h_r_gt_log : r > Real.log 3 / Real.log 2 := by
    have h2 : Real.log 2 > 0 := Real.log_pos (by norm_num)
    have h3 : Real.log 3 > 0 := Real.log_pos (by norm_num)
    have hd1 : 1 / ((⌊(j : ℝ) * Real.log 2 / Real.log 3⌋ : ℤ) : ℝ) >
        1 / ((j : ℝ) * (Real.log 2 / Real.log 3)) := by
      apply one_div_lt_one_div_of_lt h_floor_pos
      have : (j : ℝ) * Real.log 2 / Real.log 3 = (j : ℝ) * (Real.log 2 / Real.log 3) := by ring
      linarith
    have hd2 : (j : ℝ) * (1 / ((⌊(j : ℝ) * Real.log 2 / Real.log 3⌋ : ℤ) : ℝ)) >
        (j : ℝ) * (1 / ((j : ℝ) * (Real.log 2 / Real.log 3))) := by nlinarith [hd1]
    calc r = (j : ℝ) * (1 / ((⌊(j : ℝ) * Real.log 2 / Real.log 3⌋ : ℤ) : ℝ)) := by ring
         _ > (j : ℝ) * (1 / ((j : ℝ) * (Real.log 2 / Real.log 3))) := hd2
         _ = (j : ℝ) / ((j : ℝ) * (Real.log 2 / Real.log 3)) := by ring
         _ = 1 / (Real.log 2 / Real.log 3) := by rw [div_mul_eq_div_div, div_self (ne_of_gt hj), one_div]
         _ = Real.log 3 / Real.log 2 := by rw [one_div, inv_div]
  have h_2r : (2 : ℝ) ^ r > 3 := by
    have h2 : Real.log 2 > 0 := Real.log_pos (by norm_num)
    have h_r_log : r * Real.log 2 > Real.log 3 := (div_lt_iff₀ h2).mp h_r_gt_log
    have h_exp : Real.log ((2 : ℝ) ^ r) > Real.log 3 := by
      rw [Real.log_rpow (by norm_num) r]; exact h_r_log
    exact (Real.log_lt_log_iff (by norm_num) (Real.rpow_pos_of_pos (by norm_num) r)).mp h_exp
  have h_pos : (2 : ℝ) ^ r - 3 > 0 := by linarith
  have h_bound : μ ≤ 1 / ((2 : ℝ) ^ r - 3) := by
    calc μ ≤ 1 / ((2 : ℝ) ^ ((j : ℝ) / (q : ℝ)) - 3) := h_q_real.2
         _ ≤ 1 / ((2 : ℝ) ^ r - 3) := by
           apply one_div_le_one_div_of_le (by linarith); linarith
  exact ⟨h_pos, h_bound⟩

/-- **Corollary 4.3** (Rozier–Terracol, harmonic-mean form): for a paradoxical `Ωⱼ(n)` with at
    least one odd term, the ones-ratio `q/j` satisfies
    `log 2 / log(3 + h⁻¹) ≤ q/j < log 2 / log 3`. -/
@[category research solved, AMS 11 37, ref "Roz25", group "roz_cor_43"]
theorem paradoxical_ratio_bounds_harmonic (j n : ℕ) (hn : 0 < n) (hq : 0 < num_odd_steps j n)
    (h_para : IsParadoxical j n) :
    Real.log 2 / Real.log (3 + 1 / harmonicMean j n) ≤ (num_odd_steps j n : ℝ) / (j : ℝ) ∧
    (num_odd_steps j n : ℝ) / (j : ℝ) < Real.log 2 / Real.log 3 := by
  have h_bound1 := isParadoxical_bound hn h_para
  have hj_pos : j > 0 := by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [num_odd_steps] at hq
    · exact hj
  have hh_pos : 0 < harmonicMean j n := harmonicMean_pos j n hn hq
  have h_para_real : (1 : ℝ) - (3 : ℝ) ^ num_odd_steps j n / (2 : ℝ) ^ j > 0 := by
    have hC : C j n = (3 ^ num_odd_steps j n : ℚ) / 2 ^ j := rfl
    have hl : (0 : ℚ) < 1 - C j n := h_bound1.1
    rw [hC] at hl
    have h_cast : (((0 : ℚ) : ℝ) < (((1 : ℚ) - (3 ^ num_odd_steps j n : ℚ) / 2 ^ j : ℚ) : ℝ)) := by
      exact_mod_cast hl
    push_cast at h_cast; exact h_cast
  have h_E_real : (1 : ℝ) - (3 : ℝ) ^ num_odd_steps j n / (2 : ℝ) ^ j ≤
      ((3 + 1 / harmonicMean j n) ^ num_odd_steps j n - 3 ^ num_odd_steps j n) / 2 ^ j := by
    have h_upper := correction_ratio_bound_harmonic j n hn hq
    have h_lower_real : (1 : ℝ) - (3 : ℝ) ^ num_odd_steps j n / (2 : ℝ) ^ j ≤ (E j n : ℝ) / (n : ℝ) := by
      have hl := h_bound1.2
      have hC : C j n = (3 ^ num_odd_steps j n : ℚ) / 2 ^ j := rfl
      rw [hC] at hl
      have h_cast : (((1 : ℚ) - (3 ^ num_odd_steps j n : ℚ) / 2 ^ j : ℚ) : ℝ) ≤
          ((E j n / (n : ℚ) : ℚ) : ℝ) := by exact_mod_cast hl
      push_cast at h_cast; exact h_cast
    linarith
  exact paradoxical_ratio_real j (num_odd_steps j n) (harmonicMean j n) hj_pos hh_pos h_para_real h_E_real

/-- **Corollary 4.4** (Rozier–Terracol, harmonic-mean form): with
    `r = j / ⌊(log2/log3)·j⌋`, a paradoxical `Ωⱼ(n)` (with at least one odd term and `j ≥ 2`)
    satisfies `h ≤ 1 / (2^r − 3)`. -/
@[category research solved, AMS 11 37, ref "Roz25", group "roz_cor_44"]
theorem paradoxical_m_bound_harmonic (j n : ℕ) (hj_ge_2 : j ≥ 2) (hn : 0 < n)
    (hq : 0 < num_odd_steps j n) (h_para : IsParadoxical j n) :
    let r := (j : ℝ) / ⌊(j : ℝ) * Real.log 2 / Real.log 3⌋
    (2 : ℝ) ^ r - 3 > 0 ∧ harmonicMean j n ≤ 1 / ((2 : ℝ) ^ r - 3) := by
  have hl := paradoxical_ratio_bounds_harmonic j n hn hq h_para
  exact paradoxical_m_bound_floor_real j (num_odd_steps j n) (harmonicMean j n) hj_ge_2
    (harmonicMean_pos j n hn hq) hl

end RT
