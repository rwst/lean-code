/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Round
import EVG25.UniformCorrespondence

/-!
# Past the horizon: the window formula and the run lemma (P1 paper, §5)

Plan EVGQ17-M0, §7.4, milestone C2; the mathematics is `plans/note-EVGQ17M0-Q.html`.

* `two_pow_mul_U_iter` — **the window formula, integer form**: for every seed `n`,
  `2^j · U^j(n) = 3^j · n + Σ_{t<j} (2 - v_t) · 3^(j-1-t) · 2^t`, where `v_t = U^t(n) mod 2` is the
  `t`-th letter.  So letter `j` of `n` is a function of `n mod 2^(j+1)` and of the first `j`
  letters, through one subset sum; this is the source of Proposition F.
* `dyadic_chain` — a dyadic chain (`θ_s = a_s/2^s`, `a_s` odd, `2θ_{s+1} ≡ 3θ_s mod 1`) has signed
  representatives `e_s = θ_s - round θ_s` with `2e_{s+1} - 3e_s ∈ ℤ`, `|e_s| ≥ 2^{-s}`, `|e_s| ≤ 1/2`,
  and `|cos π e_s| = |cos π θ_s|`.
* `run_lemma` — **Lemma R**: on a stretch of `L` consecutive steps with `|e| < 1/5` starting at
  step `s`, one has `L ≤ 2s`.  (The paper proves the sharp `L ≤ 1 + s·log 2/log(3/2)`.)
* `add_two_le_mul_three_pow_bad` — the bad steps (`|e| ≥ 1/5`) on `[s₀, N)` number at least
  `log₃((N+2)/(s₀+2))` when `s₀` is bad;
* `prod_abs_cos_le` — **Theorem A′ (Lean form)**: `∏_{s₀ ≤ s < N} |cos π e_s| ≤ cos(π/5)^B` with `B`
  the number of bad steps, so every chain decays at least like `N^{-log(sec(π/5))/log 3}`.
-/

open Finset Real CC CC.Base3div2

namespace EVG25.P1

/-! ## The window formula -/

/-- The appended digit `c_t = 2 - v_t ∈ {1, 2}`. -/
def cDigit (n t : ℕ) : ℕ := 2 - U_iter t n % 2

theorem two_mul_U' (m : ℕ) : 2 * U m = 3 * m + (2 - m % 2) := by
  unfold U; split <;> omega

/-- **Window formula.** `2^j U^j(n) = 3^j n + Σ_{t<j} c_t 3^(j-1-t) 2^t`. -/
@[category API, AMS 11 37, group "evgq17_p1"]
theorem two_pow_mul_U_iter (j n : ℕ) :
    2 ^ j * U_iter j n = 3 ^ j * n + ∑ t ∈ range j, cDigit n t * 3 ^ (j - 1 - t) * 2 ^ t := by
  induction j with
  | zero => simp [U_iter]
  | succ j ih =>
    have hU := two_mul_U' (U_iter j n)
    have h1 : 2 ^ (j + 1) * U (U_iter j n)
        = 3 * (2 ^ j * U_iter j n) + 2 ^ j * cDigit n j := by
      simp only [cDigit]
      calc 2 ^ (j + 1) * U (U_iter j n) = 2 ^ j * (2 * U (U_iter j n)) := by ring
        _ = _ := by rw [hU]; ring
    have hs : ∑ t ∈ range j, cDigit n t * 3 ^ (j + 1 - 1 - t) * 2 ^ t
        = 3 * ∑ t ∈ range j, cDigit n t * 3 ^ (j - 1 - t) * 2 ^ t := by
      rw [mul_sum]; refine sum_congr rfl fun t ht => ?_
      have : j + 1 - 1 - t = (j - 1 - t) + 1 := by have := mem_range.1 ht; omega
      rw [this, pow_succ]; ring
    rw [U_iter_succ, h1, ih, sum_range_succ, hs, show j + 1 - 1 - j = 0 by omega, pow_zero,
      mul_one, pow_succ]
    ring

/-! ## Dyadic chains and their signed representatives -/

/-- The chain relation `2e_{s+1} - 3e_s ∈ ℤ` holds at every step, including `s = 0`. -/
theorem dyadic_chain_rel (a : ℕ → ℤ) (hrel : ∀ s, (2 : ℤ) ^ s ∣ a (s + 1) - 3 * a s) (s : ℕ) :
    let θ : ℕ → ℝ := fun s => (a s : ℝ) / 2 ^ s
    let e : ℕ → ℝ := fun s => θ s - round (θ s)
    ∃ z : ℤ, 2 * e (s + 1) - 3 * e s = z := by
  intro θ e
  obtain ⟨q, hq⟩ := hrel s
  refine ⟨q - 2 * round (θ (s + 1)) + 3 * round (θ s), ?_⟩
  have ha : (a (s + 1) : ℝ) = 3 * a s + 2 ^ s * q := by
    have : (a (s + 1) : ℝ) - 3 * a s = 2 ^ s * q := by exact_mod_cast hq
    linarith
  have key : 2 * ((a (s + 1) : ℝ) / 2 ^ (s + 1)) - 3 * ((a s : ℝ) / 2 ^ s) = q := by
    rw [ha, pow_succ]; field_simp; ring
  simp only [e, θ]
  push_cast
  linarith

/-- **Chains.** If `a_s` is odd and `2^s ∣ a_{s+1} - 3 a_s`, then `θ_s = a_s/2^s` and its signed
representative `e_s = θ_s - round θ_s` satisfy the chain relation, the dyadic lower bound and the
size bound, and `|cos π e_s| = |cos π θ_s|`. -/
@[category API, AMS 11 42, group "evgq17_p1"]
theorem dyadic_chain (a : ℕ → ℤ) (hodd : ∀ s, Odd (a s))
    (hrel : ∀ s, (2 : ℤ) ^ s ∣ a (s + 1) - 3 * a s) (s : ℕ) (hs : 1 ≤ s) :
    let θ : ℕ → ℝ := fun s => (a s : ℝ) / 2 ^ s
    let e : ℕ → ℝ := fun s => θ s - round (θ s)
    (∃ z : ℤ, 2 * e (s + 1) - 3 * e s = z) ∧ (1 / 2 : ℝ) ^ s ≤ |e s| ∧ |e s| ≤ 1 / 2 ∧
      |Real.cos (π * e s)| = |Real.cos (π * θ s)| := by
  intro θ e
  have h2s : (0 : ℝ) < 2 ^ s := by positivity
  refine ⟨?_, ?_, abs_sub_round _, ?_⟩
  · exact dyadic_chain_rel a hrel s
  · -- `e_s = (a_s - 2^s r)/2^s` with an odd numerator
    simp only [e, θ]
    set r := round ((a s : ℝ) / 2 ^ s)
    have hnum : (a s : ℝ) / 2 ^ s - r = ((a s - 2 ^ s * r : ℤ) : ℝ) / 2 ^ s := by
      push_cast; field_simp
    rw [hnum, abs_div, abs_of_pos h2s, one_div_pow, div_le_div_iff_of_pos_right h2s]
    have hne : a s - 2 ^ s * r ≠ 0 := by
      intro h0
      have h2 : (2 : ℤ) ∣ a s := by
        have : a s = 2 ^ s * r := by linarith
        rw [this]; exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) r
      exact (Int.not_even_iff_odd.2 (hodd s)) (even_iff_two_dvd.2 h2)
    have : (1 : ℤ) ≤ |a s - 2 ^ s * r| := Int.one_le_abs hne
    exact_mod_cast this
  · simp only [e]
    rw [show π * (θ s - (round (θ s) : ℝ)) = π * θ s - (round (θ s) : ℝ) * π by ring,
      Real.cos_sub_int_mul_pi]
    rcases Int.even_or_odd (round (θ s)) with h | h
    · rw [h.neg_one_zpow]; simp
    · rw [h.neg_one_zpow]; simp [abs_neg]

/-! ## Lemma R -/

variable {e : ℕ → ℝ}

/-- Two consecutive good steps force the `×3/2` branch: `e_{u+1} = (3/2) e_u`. -/
theorem step_of_good (hrel : ∀ u, ∃ z : ℤ, 2 * e (u + 1) - 3 * e u = z) {u : ℕ}
    (h0 : |e u| < 1 / 5) (h1 : |e (u + 1)| < 1 / 5) : e (u + 1) = 3 / 2 * e u := by
  obtain ⟨z, hz⟩ := hrel u
  have hb : |(z : ℝ)| < 1 := by
    rw [← hz]
    calc |2 * e (u + 1) - 3 * e u| ≤ |2 * e (u + 1)| + |3 * e u| := abs_sub _ _
      _ = 2 * |e (u + 1)| + 3 * |e u| := by rw [abs_mul, abs_mul]; norm_num
      _ < 1 := by linarith
  have : z = 0 := by
    have : |z| < 1 := by exact_mod_cast hb
    exact Int.abs_lt_one_iff.1 this
  rw [this] at hz; push_cast at hz; linarith

/-- On a good stretch the signed representative grows geometrically. -/
theorem good_stretch (hrel : ∀ u, ∃ z : ℤ, 2 * e (u + 1) - 3 * e u = z) {s L : ℕ}
    (hgood : ∀ i < L, |e (s + i)| < 1 / 5) : ∀ i < L, |e (s + i)| = (3 / 2) ^ i * |e s| := by
  intro i hi
  induction i with
  | zero => simp
  | succ i ih =>
    rw [← add_assoc, step_of_good hrel (hgood i (by omega)) (by rw [add_assoc]; exact hgood _ hi),
      abs_mul, ih (by omega), pow_succ]
    norm_num; ring

/-- **Lemma R.** A stretch of `L` consecutive steps with `|e| < 1/5` that starts at step `s` has
`L ≤ 2s`, because `|e_s| ≥ 2^{-s}` and `(3/2)² > 2`. -/
@[category research solved, AMS 11 42, group "evgq17_p1"]
theorem run_lemma (hrel : ∀ u, ∃ z : ℤ, 2 * e (u + 1) - 3 * e u = z) {s L : ℕ}
    (hlow : (1 / 2 : ℝ) ^ s ≤ |e s|) (hgood : ∀ i < L, |e (s + i)| < 1 / 5) : L ≤ 2 * s := by
  by_contra hL
  push Not at hL
  have h := good_stretch hrel hgood (2 * s) hL
  have hg := hgood (2 * s) hL
  rw [h] at hg
  have h94 : (2 : ℝ) ^ s ≤ (3 / 2) ^ (2 * s) := by
    rw [pow_mul]; exact pow_le_pow_left₀ (by norm_num) (by norm_num) s
  have : (1 : ℝ) ≤ (3 / 2) ^ (2 * s) * |e s| := by
    calc (1 : ℝ) = 2 ^ s * (1 / 2) ^ s := by rw [← mul_pow]; norm_num
      _ ≤ (3 / 2) ^ (2 * s) * |e s| := by gcongr
  linarith

/-! ## Counting bad steps -/

open Classical in
/-- Number of bad steps (`|e| ≥ 1/5`) in `[s₀, N)`. -/
noncomputable def badCount (e : ℕ → ℝ) (s₀ N : ℕ) : ℕ :=
  ((Ico s₀ N).filter fun s => 1 / 5 ≤ |e s|).card

theorem badCount_succ_of_bad {s₀ N : ℕ} (hN : s₀ ≤ N) (h : 1 / 5 ≤ |e N|) :
    badCount e s₀ (N + 1) = badCount e s₀ N + 1 := by
  classical
  unfold badCount
  rw [Nat.Ico_succ_right_eq_insert_Ico hN, filter_insert]
  simp only [h, ↓reduceIte]
  rw [card_insert_of_notMem (by simp)]

theorem badCount_succ_of_good {s₀ N : ℕ} (hN : s₀ ≤ N) (h : ¬ 1 / 5 ≤ |e N|) :
    badCount e s₀ (N + 1) = badCount e s₀ N := by
  classical
  unfold badCount
  rw [Nat.Ico_succ_right_eq_insert_Ico hN, filter_insert]
  simp only [h, ↓reduceIte]

theorem badCount_mono {s₀ M N : ℕ} (h : M ≤ N) : badCount e s₀ M ≤ badCount e s₀ N := by
  classical
  exact card_le_card (filter_subset_filter _ (Ico_subset_Ico_right h))

/-- **Bad steps are at least logarithmic in number.** If step `s₀` is bad, then
`N + 2 ≤ (s₀ + 2) · 3^B` with `B` the number of bad steps in `[s₀, N)`, for every `N ≥ s₀`. -/
@[category research solved, AMS 11 42, group "evgq17_p1"]
theorem add_two_le_mul_three_pow_bad (hrel : ∀ u, ∃ z : ℤ, 2 * e (u + 1) - 3 * e u = z)
    (hlow : ∀ s, 1 ≤ s → (1 / 2 : ℝ) ^ s ≤ |e s|) {s₀ : ℕ} (hbad : 1 / 5 ≤ |e s₀|) :
    ∀ N, s₀ ≤ N → N + 2 ≤ (s₀ + 2) * 3 ^ badCount e s₀ N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro hN
  rcases Nat.eq_or_lt_of_le hN with h | h
  · subst h; simp [badCount]
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hM : s₀ ≤ M := by omega
  by_cases hb : 1 / 5 ≤ |e M|
  · rw [badCount_succ_of_bad hM hb, pow_succ]
    have := ih M (by omega) hM
    nlinarith
  · classical
    rw [badCount_succ_of_good hM hb]
    -- `b`: the last bad step in `[s₀, M)`
    have hsM : s₀ < M := by
      rcases Nat.eq_or_lt_of_le hM with h | h
      · subst h; exact absurd hbad hb
      · exact h
    let Q : ℕ → Prop := fun b => s₀ ≤ b ∧ b < M ∧ 1 / 5 ≤ |e b|
    have hQ0 : Q s₀ := ⟨le_rfl, hsM, hbad⟩
    set b := Nat.findGreatest Q M with hbdef
    have hbQ : Q b := Nat.findGreatest_spec (P := Q) hsM.le hQ0
    have hgood : ∀ i < M - b, |e (b + 1 + i)| < 1 / 5 := by
      intro i hi
      by_contra hc
      push Not at hc
      rcases Nat.lt_or_ge (b + 1 + i) M with hlt | hge
      · have := Nat.le_findGreatest (P := Q) hlt.le ⟨by have := hbQ.1; omega, hlt, hc⟩
        omega
      · have : b + 1 + i = M := by omega
        rw [this] at hc; exact hb hc
    have hrun := run_lemma hrel (hlow (b + 1) (by omega)) hgood
    have hib := ih b (by have := hbQ.2.1; omega) hbQ.1
    have hB : badCount e s₀ b + 1 ≤ badCount e s₀ M := by
      rw [← badCount_succ_of_bad hbQ.1 hbQ.2.2]; exact badCount_mono (by have := hbQ.2.1; omega)
    have hpow : (3 : ℕ) ^ (badCount e s₀ b + 1) ≤ 3 ^ badCount e s₀ M :=
      Nat.pow_le_pow_right (by norm_num) hB
    rw [pow_succ] at hpow
    have : M + 1 + 2 ≤ 3 * (b + 2) := by omega
    nlinarith

/-- `|cos π e| ≤ cos(π/5)` on a bad step with `|e| ≤ 1/2`. -/
theorem abs_cos_le_of_bad {x : ℝ} (h1 : 1 / 5 ≤ |x|) (h2 : |x| ≤ 1 / 2) :
    |Real.cos (π * x)| ≤ Real.cos (π / 5) := by
  have hc : Real.cos (π * x) = Real.cos (π * |x|) := by
    rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, mul_neg, Real.cos_neg]
  have hnn : 0 ≤ Real.cos (π * |x|) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by nlinarith [Real.pi_pos, abs_nonneg x])
      (by nlinarith [Real.pi_pos])
  rw [hc, abs_of_nonneg hnn]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_pos])
    (by nlinarith [Real.pi_pos])

/-- **Theorem A′ (Lean form).** Along any chain, `∏_{s₀ ≤ s < N} |cos π e_s| ≤ cos(π/5)^B`, `B` the
number of bad steps; with `add_two_le_mul_three_pow_bad` this is polynomial decay in `N`. -/
@[category research solved, AMS 11 42, group "evgq17_p1"]
theorem prod_abs_cos_le (hhalf : ∀ s, |e s| ≤ 1 / 2) (s₀ N : ℕ) :
    ∏ s ∈ Ico s₀ N, |Real.cos (π * e s)| ≤ Real.cos (π / 5) ^ badCount e s₀ N := by
  classical
  have hc5 : 0 ≤ Real.cos (π / 5) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  rw [← prod_filter_mul_prod_filter_not (Ico s₀ N) (fun s => 1 / 5 ≤ |e s|)]
  have h1 : ∏ s ∈ (Ico s₀ N).filter (fun s => 1 / 5 ≤ |e s|), |Real.cos (π * e s)|
      ≤ Real.cos (π / 5) ^ badCount e s₀ N := by
    unfold badCount
    rw [← prod_const]
    exact prod_le_prod₀ (fun _ _ => abs_nonneg _)
      (fun s hs => abs_cos_le_of_bad (mem_filter.1 hs).2 (hhalf s))
  have h2 : ∏ s ∈ (Ico s₀ N).filter (fun s => ¬ 1 / 5 ≤ |e s|), |Real.cos (π * e s)| ≤ 1 :=
    prod_le_one₀ (fun _ _ => abs_nonneg _) (fun _ _ => Real.abs_cos_le_one _)
  calc _ ≤ Real.cos (π / 5) ^ badCount e s₀ N * 1 :=
        mul_le_mul h1 h2 (prod_nonneg fun _ _ => abs_nonneg _) (pow_nonneg hc5 _)
    _ = _ := mul_one _

end EVG25.P1
