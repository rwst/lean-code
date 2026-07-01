/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import RT.FinitePar
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# §6 heuristic analysis (Step 5): conditional finiteness

This file formalizes the algebraic heart of [Roz25] §6 — the chain of inequalities (19)–(21) that,
assuming Conjecture 6.2, constrain the paradoxical sequences.  Following the plan, the two
conjectures 6.1 and 6.2 are recorded as **`Prop` definitions** (hypotheses / documentation), never
asserted as facts, and the heuristic is a theorem *conditional* on Conjecture 6.2.  The harmonic
mean is eliminated throughout: everything runs on the smallest term via Corollary 4.3′.

* `heuristic_19` — the **unconditional** inequality (19): from Corollary 4.3′,
  `0 < j/q − log3/log2 < 1/(3 m log 2)` for any lower bound `m ≥ 1` on the odd terms.
* `Conjecture61`, `Conjecture62` — the two conjectures as `Prop`s.
* `heuristic_chain` — assuming `Conjecture62 α β`, every paradoxical `Ωⱼ(n)` (`n > 2`) satisfies
  the §6 inequality (21): `0 < j log2 − q log3 < (q/3)·exp(−j/(αβ))`.

The finiteness conclusion of §6 combines (21) with Rhin's linear-forms-in-logarithms bound
(Prop 6.3, `|j log2 − q log3| ≥ j^{-13.3}`), a cited transcendence result that the paper leaves
external; per the plan that final step is not reformalized here.

## References
* [Roz25] Rozier, Olivier, and Claude Terracol. "Paradoxical behavior in Collatz sequences."
  arXiv preprint arXiv:2502.00948 (2025). §6, eqs (15)–(21), Conjectures 6.1, 6.2.
* [Rhi87] G. Rhin, effective irrationality measure (Prop 6.3).
-/

open Classical

open CC

namespace RT

/-- **Inequality (19)** of [Roz25] (unconditional). For a paradoxical `Ωⱼ(n)` with ones-ratio
`q/j` constrained by Corollary 4.3′ (lower bound with any `m ≥ 1`, upper bound `< log2/log3`),
`0 < j/q − log3/log2 < 1/(3 m log 2)`. -/
@[category research solved, AMS 11 37, ref "Roz25", group "roz_heuristic"]
theorem heuristic_19 (j q m : ℕ) (hj : 0 < j) (hq : 0 < q) (hm : 1 ≤ m)
    (h_ratio : Real.log 2 / Real.log (3 + 1 / (m : ℝ)) ≤ (q : ℝ) / (j : ℝ))
    (h_upper : (q : ℝ) / (j : ℝ) < Real.log 2 / Real.log 3) :
    0 < (j : ℝ) / (q : ℝ) - Real.log 3 / Real.log 2 ∧
    (j : ℝ) / (q : ℝ) - Real.log 3 / Real.log 2 < 1 / (3 * (m : ℝ) * Real.log 2) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hL : (0 : ℝ) < Real.log (3 + 1 / (m : ℝ)) := Real.log_pos (by
    have : (0 : ℝ) < 1 / m := by positivity
    linarith)
  have hfact : (3 : ℝ) + 1 / m = 3 * (1 + 1 / (3 * m)) := by field_simp
  have hlogfact : Real.log (3 + 1 / (m : ℝ)) = Real.log 3 + Real.log (1 + 1 / (3 * (m : ℝ))) := by
    rw [hfact, Real.log_mul (by norm_num) (by positivity)]
  refine ⟨?_, ?_⟩
  · -- lower bound: from q/j < log2/log3
    rw [div_lt_div_iff₀ hjR hlog3] at h_upper
    rw [sub_pos, div_lt_div_iff₀ hlog2 hqR]
    nlinarith [h_upper]
  · -- upper bound: from log2/log(3+1/m) ≤ q/j
    have hcross : Real.log 2 * j ≤ q * Real.log (3 + 1 / (m : ℝ)) := by
      rw [div_le_div_iff₀ hL hjR] at h_ratio; linarith [h_ratio]
    have hle : (j : ℝ) / q ≤ Real.log (3 + 1 / (m : ℝ)) / Real.log 2 := by
      rw [div_le_div_iff₀ hqR hlog2]; nlinarith [hcross]
    have hloglt : Real.log (1 + 1 / (3 * (m : ℝ))) < 1 / (3 * (m : ℝ)) := by
      have h1 : (0 : ℝ) < 1 + 1 / (3 * m) := by positivity
      have h2 : (1 : ℝ) + 1 / (3 * m) ≠ 1 := ne_of_gt (by
        have : (0 : ℝ) < 1 / (3 * m) := by positivity
        linarith)
      linarith [Real.log_lt_sub_one_of_pos h1 h2]
    calc (j : ℝ) / q - Real.log 3 / Real.log 2
        ≤ Real.log (3 + 1 / (m : ℝ)) / Real.log 2 - Real.log 3 / Real.log 2 := by linarith [hle]
      _ = Real.log (1 + 1 / (3 * (m : ℝ))) / Real.log 2 := by rw [hlogfact]; ring
      _ < (1 / (3 * (m : ℝ))) / Real.log 2 := by gcongr
      _ = 1 / (3 * (m : ℝ) * Real.log 2) := by rw [div_div]

/-! ### The conjectures (Props; never asserted) -/

/-- The T-delay `d_T(n)`: the least `i` with `Tⁱ(n) = 1` (`0` if none). -/
@[category API, AMS 11 37, ref "Roz25", group "roz_heuristic"]
noncomputable def dT (n : ℕ) : ℕ := if h : ∃ i, T_iter i n = 1 then Nat.find h else 0

/-- **Conjecture 6.1** (Rozier–Terracol): there is no paradoxical sequence for `T` whose first term
exceeds `4614`. An open conjecture — recorded as a `Prop`, never asserted. Stronger than both the
Collatz and CST conjectures (Corollary 3.3). -/
@[category API, AMS 11 37, ref "Roz25", group "roz_heuristic"]
def Conjecture61 : Prop := ∀ j n : ℕ, IsParadoxical j n → n ≤ 4614

/-- **Conjecture 6.2** (Rozier–Terracol), in the effective form used in §6: a delay bound (15),
`d_T(n) ≤ α log n`, together with the derived maximal-excursion bound (16), `M_T(n) ≤ n^β`
(phrased as `Tᵏ(n) ≤ n^β` for every `k`). An open hypothesis — recorded as a `Prop`. -/
@[category API, AMS 11 37, ref "Roz25", group "roz_heuristic"]
def Conjecture62 (α β : ℝ) : Prop :=
  0 < α ∧ 0 < β ∧
  (∀ n : ℕ, 2 ≤ n → (∃ i, T_iter i n = 1) ∧ (dT n : ℝ) ≤ α * Real.log n) ∧
  (∀ n : ℕ, 2 ≤ n → ∀ k, (T_iter k n : ℝ) ≤ (n : ℝ) ^ β)

/-! ### The conditional heuristic -/

/-- **The §6 heuristic** ([Roz25], eqs (17)–(21)). Assuming Conjecture 6.2, every paradoxical
`Ωⱼ(n)` with `n > 2` satisfies inequality (21):

  `0 < j·log 2 − q·log 3 < (q/3)·exp(−j/(αβ))`.

Combined with Rhin's Proposition 6.3 (external), the right-hand side forces `j` to be bounded,
supporting Conjecture 6.1 (finiteness of paradoxical sequences). Proved on the min-term layer via
`heuristic_19`; the harmonic mean is never used. -/
@[category research solved, AMS 11 37, ref "Roz25", group "roz_heuristic"]
theorem heuristic_chain (α β : ℝ) (hConj : Conjecture62 α β) (j n : ℕ)
    (h_para : IsParadoxical j n) (hn : 2 < n) :
    0 < (j : ℝ) * Real.log 2 - (num_odd_steps j n : ℝ) * Real.log 3 ∧
    (j : ℝ) * Real.log 2 - (num_odd_steps j n : ℝ) * Real.log 3
      < (num_odd_steps j n : ℝ) / 3 * Real.exp (-(j : ℝ) / (α * β)) := by
  obtain ⟨hα, hβ, hdelay, hexc⟩ := hConj
  have hn1 : 1 ≤ n := by omega
  have hj2 : 2 ≤ j := two_le_j_of_paradoxical j n h_para hn1
  have hTj2 : 2 < T_iter j n := by have := h_para.1; omega
  -- smallest term m of the window
  obtain ⟨ks, hks_mem, hks_min⟩ := Finset.exists_min_image (Finset.range j)
    (fun k => T_iter k n) ⟨0, Finset.mem_range.mpr (by omega)⟩
  set m := T_iter ks n with hm_def
  have hks_lt : ks < j := Finset.mem_range.mp hks_mem
  have h_odd_bounded : ∀ k, k < j → T_iter k n % 2 = 1 → T_iter k n ≥ m :=
    fun k hk _ => hks_min k (Finset.mem_range.mpr hk)
  -- m ≥ 3 (no window term hits the {1,2} cycle, else Tʲ(n) ∈ {1,2})
  have hm3 : 3 ≤ m := by
    rcases Nat.lt_or_ge m 3 with hlt | hge
    · exfalso
      have hm1 : 1 ≤ m := T_iter_pos hn1 ks
      have hTj : T_iter j n = T_iter (j - ks) m := by rw [hm_def, ← T_iter_add]; congr 1; omega
      have hcyc : T_iter (j - ks) m = 1 ∨ T_iter (j - ks) m = 2 := by
        rcases (show m = 1 ∨ m = 2 by omega) with h | h
        · rw [h]; exact T_iter_one_cycle (j - ks)
        · rw [h, show T_iter (j - ks) 2 = T_iter (j - ks + 1) 1 from by rw [← T_one, ← T_iter_succ_right]]
          exact T_iter_one_cycle _
      omega
    · exact hge
  have hm_pos : 0 < m := by omega
  -- Corollary 4.3′ and q > 0
  have hratio := paradoxical_ratio_bounds j n m (by omega) hm_pos h_odd_bounded h_para
  have hq : 0 < num_odd_steps j n := by
    by_contra h0
    push Not at h0
    have hq0 : num_odd_steps j n = 0 := by omega
    have hb := hratio.1
    rw [hq0] at hb
    have hpos : 0 < Real.log 2 / Real.log (3 + 1 / (m : ℝ)) :=
      div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by
        have : (0 : ℝ) < 1 / m := by positivity
        linarith))
    simp only [Nat.cast_zero, zero_div] at hb
    linarith
  -- inequality (19)
  have h19 := heuristic_19 j (num_odd_steps j n) m (by omega) hq (by omega) hratio.1 hratio.2
  -- (18): j < α log n
  have hreach : ∃ i, T_iter i n = 1 := (hdelay n (by omega)).1
  have hdT_eq : dT n = Nat.find hreach := by unfold dT; rw [dif_pos hreach]
  have hjdt : j < dT n := by
    rw [hdT_eq]
    by_contra hle
    push Not at hle
    have h1 : T_iter (Nat.find hreach) n = 1 := Nat.find_spec hreach
    have hsplit : T_iter j n = T_iter (j - Nat.find hreach) (T_iter (Nat.find hreach) n) := by
      rw [← T_iter_add]; congr 1; omega
    rw [h1] at hsplit
    rcases T_iter_one_cycle (j - Nat.find hreach) with hc | hc <;> rw [hc] at hsplit <;> omega
  have hj_lt : (j : ℝ) < α * Real.log n := by
    have h1 : (j : ℝ) < (dT n : ℝ) := by exact_mod_cast hjdt
    have h2 := (hdelay n (by omega)).2
    linarith
  -- (17): n ≤ m^β, hence log n ≤ β log m
  have hnmb : (n : ℝ) ≤ (m : ℝ) ^ β := by
    have hk := hexc m (by omega) (j - ks)
    have hkeq : T_iter (j - ks) m = T_iter j n := by rw [hm_def, ← T_iter_add]; congr 1; omega
    rw [hkeq] at hk
    calc (n : ℝ) ≤ (T_iter j n : ℝ) := by exact_mod_cast h_para.1
      _ ≤ (m : ℝ) ^ β := hk
  have hlogn_le : Real.log n ≤ β * Real.log m := by
    have h1 := Real.log_le_log (by positivity : (0 : ℝ) < n) hnmb
    rwa [Real.log_rpow (by positivity : (0 : ℝ) < m)] at h1
  -- log m > j/(αβ)
  have hlogm : (j : ℝ) / (α * β) < Real.log m := by
    have hlogn_gt : (j : ℝ) / α < Real.log n := by
      rw [div_lt_iff₀ hα]; nlinarith [hj_lt]
    have hβlm : (j : ℝ) / α < β * Real.log m := lt_of_lt_of_le hlogn_gt hlogn_le
    rw [div_lt_iff₀ hα] at hβlm
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < α * β)]
    nlinarith [hβlm]
  -- 1/m < exp(-j/(αβ))
  have hexp_lt : (1 : ℝ) / m < Real.exp (-(j : ℝ) / (α * β)) := by
    have hem : Real.exp ((j : ℝ) / (α * β)) < m := by
      rw [← Real.exp_log (by positivity : (0 : ℝ) < m)]
      exact Real.exp_lt_exp.mpr hlogm
    rw [neg_div, Real.exp_neg, ← one_div]
    exact one_div_lt_one_div_of_lt (Real.exp_pos _) hem
  -- assemble (21)
  have hq' : (num_odd_steps j n : ℝ) ≠ 0 := by positivity
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hql2 : (0 : ℝ) < (num_odd_steps j n : ℝ) * Real.log 2 := by positivity
  have heq : (j : ℝ) * Real.log 2 - (num_odd_steps j n : ℝ) * Real.log 3
      = ((j : ℝ) / (num_odd_steps j n : ℝ) - Real.log 3 / Real.log 2)
        * ((num_odd_steps j n : ℝ) * Real.log 2) := by
    field_simp
  refine ⟨?_, ?_⟩
  · rw [heq]; exact mul_pos h19.1 hql2
  · rw [heq]
    calc ((j : ℝ) / (num_odd_steps j n : ℝ) - Real.log 3 / Real.log 2)
          * ((num_odd_steps j n : ℝ) * Real.log 2)
        < (1 / (3 * (m : ℝ) * Real.log 2)) * ((num_odd_steps j n : ℝ) * Real.log 2) :=
          mul_lt_mul_of_pos_right h19.2 hql2
      _ = (num_odd_steps j n : ℝ) / 3 * (1 / (m : ℝ)) := by
          field_simp
      _ < (num_odd_steps j n : ℝ) / 3 * Real.exp (-(j : ℝ) / (α * β)) :=
          mul_lt_mul_of_pos_left hexp_lt (by positivity)

end RT
