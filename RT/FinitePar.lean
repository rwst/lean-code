/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import RT.MoreParadoxical
import RT.ExcursionRecords
import RT.CrossingLemmas
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Theorem 5.3 and Corollary 5.4 (Step 4): finitely many paradoxical sequences

This file assembles the excursion/delay records (`RT.ExcursionRecords`), the crossing lemmas
(`RT.CrossingLemmas`), and the min-term corollaries 4.3′/4.4′ (`RT.MoreParadoxical`) into the
capstones of [Roz25] §5, following the proof on p. 16.

* `theorem_5_3` — the **dichotomy**: every paradoxical `Ωⱼ(n)` with `n ≥ 3` satisfies either
  `n ≤ 4614 ∧ j ≤ 92` (the exhaustively-searched base region) or `2.8×10¹⁹ < n ∧ 301994 ≤ j`.
  The `harmonic mean is never used` — everything runs on the min-term layer.
* `no_paradoxical_mid_j`, `no_paradoxical_mid_n` — the paper's two "no others" bullets.
* `cst_below` — **Corollary 5.4**: the coefficient-stopping-time conjecture (`t(n) = τ(n)`) holds
  for all `2 ≤ n ≤ 2.8×10¹⁹`, bootstrapping the small verified range via Theorem 5.3.

The proof of Theorem 5.3 is a two-pass argument. For `n > 10⁹`, let `m` be the smallest term of
`Ω_{j-1}(n)`; then `M_T(m) ≥ Tʲ(n) ≥ n`, so the excursion records force `m ≥ m₀ = 113383`,
Corollary 4.4 gives `m ≤ H(j)`, the crossing `H_cross_j0` gives `j ≥ 1539`, Corollary 4.3 gives
`q ≥ 971`, hence `d_Col(n) ≥ 2510 > 2456` (the delay record), forcing `n > 2.8×10¹⁹`; a second pass
with `m₁ = 23035537407` and `j1_cross` gives `j ≥ 301994`.

## References
* [Roz25] Rozier, Olivier, and Claude Terracol. "Paradoxical behavior in Collatz sequences."
  arXiv preprint arXiv:2502.00948 (2025). Theorem 5.3, Corollary 5.4 (pp. 15–17).
* [Ter76] Terras, Riho. "A stopping time problem on the positive integers."
  Acta Arithmetica 30 (1976): 241-252.
-/

open Classical

open CC

namespace RT

/-! ### Helper lemmas -/

/-- A paradoxical sequence has length `j ≥ 2`: `j = 0` gives `C = 1`, and `j = 1` gives either
`C₁ = 3/2 ≥ 1` (odd `n`) or `T(n) = n/2 < n` (even `n`). -/
@[category API, AMS 11 37, ref "Roz25", group "roz_thm_53"]
lemma two_le_j_of_paradoxical (j n : ℕ) (h_para : IsParadoxical j n) (hn : 1 ≤ n) : 2 ≤ j := by
  rcases Nat.lt_or_ge j 2 with h | h
  · exfalso
    obtain ⟨hge, hlt⟩ := h_para
    interval_cases j
    · rw [show C 0 n = 1 from by simp [C, num_odd_steps]] at hlt; linarith
    · rcases (show X n = 0 ∨ X n = 1 by rw [X_eq_mod]; omega) with hX | hX
      · -- even: T(n) = n/2, contradicts T(n) ≥ n
        have hC : C 1 n = 1 / 2 := by simp [C, num_odd_steps, T_iter, hX]
        have hE : E 1 n = 0 := by simp [E, decomposition_correction, T_iter, hX]
        have hd := linear_decomposition' 1 n
        rw [hC, hE] at hd
        have hge' : (n : ℚ) ≤ T_iter 1 n := by exact_mod_cast hge
        have hnpos : (0 : ℚ) < n := by exact_mod_cast hn
        rw [hd] at hge'; linarith
      · -- odd: C₁ = 3/2 ≥ 1
        have hC : C 1 n = 3 / 2 := by simp [C, num_odd_steps, T_iter, hX]
        rw [hC] at hlt; linarith
  · exact h

/-- Every orbit value of `a` is `≤` its maximal excursion `M_T(a)`. -/
@[category API, AMS 11 37, ref "Roz25", group "roz_excursion_records"]
lemma le_maxExcursion (a i : ℕ) : (T_iter i a : ℕ∞) ≤ maxExcursion a :=
  le_iSup (fun i => (T_iter i a : ℕ∞)) i

/-- Bridge from Corollary 4.4 (`paradoxical_m_bound`) to `H j`: the smallest odd-term lower bound
`m` satisfies `m ≤ H j`. -/
@[category API, AMS 11 37, ref "Roz25", group "roz_thm_53"]
lemma m_le_H {j n m : ℕ} (hj2 : 2 ≤ j) (hn : 0 < n) (hm_pos : 0 < m)
    (h_odd_bounded : ∀ k, k < j → T_iter k n % 2 = 1 → T_iter k n ≥ m)
    (h_para : IsParadoxical j n) : (m : ℝ) ≤ H j := by
  have h := (paradoxical_m_bound j n m hj2 hn hm_pos h_odd_bounded h_para).2
  simpa [H, rExp] using h

/-- The Collatz delay dominates `j + qⱼ(n)` whenever the `j`-th term exceeds `2` (eq. (14) of
[Roz25]; `d_T(n) ≥ j` since the orbit of `1` stays in `{1,2}`). -/
@[category API, AMS 11 37, ref "Roz25", group "roz_thm_53"]
lemma paradoxical_delayCol_ge (j n : ℕ) (hn2 : 2 < T_iter j n) :
    (↑(j + num_odd_steps j n) : ℕ∞) ≤ delayCol n := by
  by_cases h : ∃ i, T_iter i n = 1
  · unfold delayCol
    rw [dif_pos h]
    have hd_spec : T_iter (Nat.find h) n = 1 := Nat.find_spec h
    have hjd : j ≤ Nat.find h := by
      by_contra hlt
      push Not at hlt
      have hsplit : T_iter j n = T_iter (j - Nat.find h) (T_iter (Nat.find h) n) := by
        rw [← T_iter_add]; congr 1; omega
      rw [hd_spec] at hsplit
      rcases T_iter_one_cycle (j - Nat.find h) with h1 | h1 <;> rw [h1] at hsplit <;> omega
    have hmono : num_odd_steps j n ≤ num_odd_steps (Nat.find h) n := num_odd_steps_mono hjd n
    exact_mod_cast Nat.add_le_add hjd hmono
  · unfold delayCol
    rw [dif_neg h]
    exact le_top

/-! ### Theorem 5.3 -/

/-- **Theorem 5.3** (Rozier–Terracol; min-term proof, harmonic mean never used). Every paradoxical
`Ωⱼ(n)` with `n ≥ 3` lies in one of two regions: the base region `n ≤ 4614 ∧ j ≤ 92`, or
`2.8×10¹⁹ < n ∧ 301994 ≤ j`. In particular there are none with `93 ≤ j ≤ 301993` or with
`4615 ≤ n ≤ 2.8×10¹⁹`. -/
@[category research solved, AMS 11 37, ref "Roz25", group "roz_thm_53"]
theorem theorem_5_3 (j n : ℕ) (h_para : IsParadoxical j n) (hn : 3 ≤ n) :
    (n ≤ 4614 ∧ j ≤ 92) ∨ (28 * 10 ^ 18 < n ∧ 301994 ≤ j) := by
  by_cases hle : n ≤ 10 ^ 9
  · exact Or.inl (base_case_exhaustive j n h_para hn hle)
  · right
    push Not at hle
    have hn1 : 1 ≤ n := by omega
    have hj2 : 2 ≤ j := two_le_j_of_paradoxical j n h_para hn1
    -- smallest term `m` of the window
    obtain ⟨ks, hks_mem, hks_min⟩ := Finset.exists_min_image (Finset.range j)
      (fun k => T_iter k n) ⟨0, Finset.mem_range.mpr (by omega)⟩
    set m := T_iter ks n with hm_def
    have hks_lt : ks < j := Finset.mem_range.mp hks_mem
    have hm_pos : 0 < m := T_iter_pos hn1 ks
    have h_odd_bounded : ∀ k, k < j → T_iter k n % 2 = 1 → T_iter k n ≥ m :=
      fun k hk _ => hks_min k (Finset.mem_range.mpr hk)
    -- `M_T(m) ≥ Tʲ(n) ≥ n`
    have hTj_ge_n : n ≤ T_iter j n := h_para.1
    have hTj_eq : T_iter j n = T_iter (j - ks) m := by
      rw [hm_def, ← T_iter_add]; congr 1; omega
    have hMexc : (n : ℕ∞) ≤ maxExcursion m := by
      calc (n : ℕ∞) ≤ (T_iter j n : ℕ∞) := by exact_mod_cast hTj_ge_n
        _ = (T_iter (j - ks) m : ℕ∞) := by rw [hTj_eq]
        _ ≤ maxExcursion m := le_maxExcursion m (j - ks)
    -- Cor 4.4 bridge and the base of both passes
    have hmH : (m : ℝ) ≤ H j := m_le_H hj2 (by omega) hm_pos h_odd_bounded h_para
    have hTj2 : 2 < T_iter j n := by omega
    -- First pass: m ≥ m₀ = 113383, so j ≥ 1539 and q ≥ 971, so n > 2.8×10¹⁹.
    have hm_m0 : 113383 ≤ m := by
      apply maxexc_record_m0
      exact le_trans (by exact_mod_cast (show (10 ^ 9 : ℕ) ≤ n by omega)) hMexc
    have hH_m0 : (113383 : ℝ) ≤ H j := le_trans (by exact_mod_cast hm_m0) hmH
    have hj1539 : 1539 ≤ j := H_cross_j0 j (by omega) hH_m0
    have hq971 : 971 ≤ num_odd_steps j n := by
      apply q_lower_from_j0 j (num_odd_steps j n) hj1539
      have hmono : Real.log (3 + 1 / (m : ℝ)) ≤ Real.log (3 + 1 / (113383 : ℝ)) := by
        apply Real.log_le_log (by positivity)
        have : (1 : ℝ) / m ≤ 1 / 113383 :=
          one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hm_m0)
        linarith
      have hlogpos : (0 : ℝ) < Real.log (3 + 1 / (m : ℝ)) := Real.log_pos (by
        have : (0 : ℝ) < 1 / m := by positivity
        linarith)
      calc Real.log 2 / Real.log (3 + 1 / (113383 : ℝ))
          ≤ Real.log 2 / Real.log (3 + 1 / (m : ℝ)) := by gcongr
        _ ≤ (num_odd_steps j n : ℝ) / (j : ℝ) := (paradoxical_ratio_bounds j n m (by omega) hm_pos h_odd_bounded h_para).1
    have hn_big : 28 * 10 ^ 18 < n := by
      have hdelay := paradoxical_delayCol_ge j n hTj2
      rcases delay_record_col n (by omega) with hle2456 | hbig
      · exfalso
        have hcast : (↑(j + num_odd_steps j n) : ℕ∞) ≤ (2456 : ℕ) := le_trans hdelay hle2456
        have : j + num_odd_steps j n ≤ 2456 := by exact_mod_cast hcast
        omega
      · exact hbig
    -- Second pass: m ≥ m₁ = 23035537407, so j ≥ 301994.
    have hMexc2 : (28 * 10 ^ 18 : ℕ) < maxExcursion m :=
      lt_of_lt_of_le (by exact_mod_cast hn_big) hMexc
    have hm_m1 : 23035537407 ≤ m := maxexc_record_m1 m hMexc2
    have hH_m1 : (23035537407 : ℝ) ≤ H j := le_trans (by exact_mod_cast hm_m1) hmH
    have hj301994 : 301994 ≤ j := j1_cross j (by omega) hH_m1
    exact ⟨hn_big, hj301994⟩

/-- **No paradoxical sequences of intermediate length** ([Roz25], Thm 5.3, first bullet): there is
no paradoxical `Ωⱼ(n)` with `n ≥ 3` and `93 ≤ j ≤ 301993`. -/
@[category research solved, AMS 11 37, ref "Roz25", group "roz_thm_53"]
theorem no_paradoxical_mid_j (j n : ℕ) (h_para : IsParadoxical j n) (hn : 3 ≤ n)
    (hj : 93 ≤ j) : 301994 ≤ j := by
  rcases theorem_5_3 j n h_para hn with ⟨_, hj92⟩ | ⟨_, hj301994⟩
  · omega
  · exact hj301994

/-- **No paradoxical sequences of intermediate size** ([Roz25], Thm 5.3, second bullet): there is
no paradoxical `Ωⱼ(n)` with `4615 ≤ n ≤ 2.8×10¹⁹`. -/
@[category research solved, AMS 11 37, ref "Roz25", group "roz_thm_53"]
theorem no_paradoxical_mid_n (j n : ℕ) (h_para : IsParadoxical j n) (hn : 4615 ≤ n) :
    28 * 10 ^ 18 < n := by
  rcases theorem_5_3 j n h_para (by omega) with ⟨hn4614, _⟩ | ⟨hnbig, _⟩
  · omega
  · exact hnbig

/-! ### Corollary 5.4 -/

/-- The coefficient stopping time never exceeds the stopping time: at the stopping time `t`,
`Tᵗ(n) < n` forces `Cₜ(n) < 1` (since `Tᵗ(n) = Cₜ·n + Eₜ` with `Eₜ ≥ 0`), so `τ ≤ t`. -/
@[category API, AMS 11 37, ref "Ter76", group "roz_thm_53"]
lemma coeff_le_stopping (n : ℕ) : coeff_stopping_time n ≤ stopping_time n := by
  by_cases ht : ∃ k : ℕ, k ≥ 1 ∧ T_iter k n < n
  · set t := Nat.find ht with ht_def
    have hspec := Nat.find_spec ht
    have hnpos : (0 : ℚ) < n := by
      have : 0 < n := by omega
      exact_mod_cast this
    have hCt : C t n < 1 := by
      have hd := linear_decomposition' t n
      have hE : (0 : ℚ) ≤ E t n := by unfold E; positivity
      have hTlt : (T_iter t n : ℚ) < n := by exact_mod_cast hspec.2
      have h1 : C t n * n < 1 * n := by rw [one_mul]; linarith [hd, hE, hTlt]
      exact lt_of_mul_lt_mul_right h1 (le_of_lt hnpos)
    have hce : ∃ j : ℕ, j ≥ 1 ∧ C j n < 1 := ⟨t, hspec.1, hCt⟩
    rw [show coeff_stopping_time n = (Nat.find hce : ℕ∞) from by
          unfold coeff_stopping_time; rw [dif_pos hce],
        show stopping_time n = (t : ℕ∞) from by unfold stopping_time; rw [dif_pos ht]]
    have hfind : Nat.find hce ≤ t := Nat.find_le ⟨hspec.1, hCt⟩
    exact_mod_cast hfind
  · rw [show stopping_time n = ⊤ from by unfold stopping_time; rw [dif_neg ht]]
    exact le_top

/-- **Verified base range of the CST conjecture** (Terras [Ter76], extended by Garner [Gar81]):
`t(n) = τ(n)` for `2 ≤ n ≤ 250000`. A cited numerical fact. -/
@[category research solved, AMS 11 37, ref "Roz25" "Ter76" "Gar81", group "roz_thm_53"]
axiom cst_verified_small :
    ∀ n : ℕ, 2 ≤ n → n ≤ 250000 → stopping_time n = coeff_stopping_time n

/-- **Corollary 5.4** (Rozier–Terracol). The coefficient-stopping-time conjecture holds far beyond
the directly verified range: `t(n) = τ(n)` for every `2 ≤ n ≤ 2.8×10¹⁹`.  If `t(n) ≠ τ(n)` then
`Ω_{τ(n)}(n)` is paradoxical, so Theorem 5.3 forces `n ≤ 4614`, already inside the verified range —
a contradiction. -/
@[category research solved, AMS 11 37, ref "Roz25", group "roz_thm_53"]
theorem cst_below (n : ℕ) (hn2 : 2 ≤ n) (hle : n ≤ 28 * 10 ^ 18) :
    stopping_time n = coeff_stopping_time n := by
  by_cases hsmall : n ≤ 250000
  · exact cst_verified_small n hn2 hsmall
  · push Not at hsmall
    by_contra hne
    have hlt : coeff_stopping_time n < stopping_time n :=
      lt_of_le_of_ne (coeff_le_stopping n) (fun h => hne h.symm)
    have hce : ∃ j : ℕ, j ≥ 1 ∧ C j n < 1 := by
      by_contra hnce
      rw [show coeff_stopping_time n = ⊤ from by unfold coeff_stopping_time; rw [dif_neg hnce]] at hlt
      exact absurd hlt not_top_lt
    set τ₀ := Nat.find hce with hτ₀_def
    have hcoeff_eq : coeff_stopping_time n = (τ₀ : ℕ∞) := by
      unfold coeff_stopping_time; rw [dif_pos hce]
    have hτspec := Nat.find_spec hce
    have hTge : n ≤ T_iter τ₀ n := by
      by_contra hlt2
      push Not at hlt2
      have hstop_le : stopping_time n ≤ (τ₀ : ℕ∞) := by
        have hex : ∃ k, k ≥ 1 ∧ T_iter k n < n := ⟨τ₀, hτspec.1, hlt2⟩
        rw [show stopping_time n = (Nat.find hex : ℕ∞) from by
              unfold stopping_time; rw [dif_pos hex]]
        have hfind : Nat.find hex ≤ τ₀ := Nat.find_le ⟨hτspec.1, hlt2⟩
        exact_mod_cast hfind
      rw [hcoeff_eq] at hlt
      exact absurd (lt_of_lt_of_le hlt hstop_le) (lt_irrefl _)
    have h_para : IsParadoxical τ₀ n := ⟨hTge, hτspec.2⟩
    rcases theorem_5_3 τ₀ n h_para (by omega) with ⟨hn4614, _⟩ | ⟨hnbig, _⟩ <;> omega

end RT
