/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import RT.FinitePar
import RT.CRozLemma22
import CITED.RhinLogForm
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# §6 heuristic analysis (Step 5): finiteness of paradoxical sequences

This file formalizes [Roz25] §6 — the chain of inequalities (19)–(21) that, assuming Conjecture 6.2,
constrain the paradoxical sequences, and their combination with Rhin's linear-forms-in-logarithms
bound (Proposition 6.3) to force the excursion length `j` to be **bounded** (the §6 finiteness
conclusion).  The harmonic mean is eliminated throughout: everything runs on the smallest odd term
via Corollary 4.3′.

* `heuristic_19` — the **unconditional** inequality (19): from Corollary 4.3′,
  `0 < j/q − log3/log2 < 1/(3 m log 2)` for any lower bound `m ≥ 1` on the odd terms.
* `Conjecture62` — the effective-bound predicate of §6 (delay bound (15) + excursion bound (16)).
* `conjecture_61`, `conjecture_62` — Conjectures 6.1 and 6.2, recorded as **`research open`
  theorems with `sorry`** (never asserted as established facts); `conjecture_62` asserts that
  effective constants `α, β` exist, i.e. `∃ α β, Conjecture62 α β`.
* `heuristic_chain` — assuming `Conjecture62 α β`, every paradoxical `Ωⱼ(n)` (`n > 2`) satisfies the
  §6 inequality (21): `0 < j log2 − q log3 < (q/3)·exp(−j/(αβ))`.
* `paradoxical_length_bounded_of_conjecture_62` — the **§6 finiteness argument**, a pure implication
  from `conjecture_62`'s statement: combining (21) with Rhin's Proposition 6.3 (`CITED.RhinLogForm`,
  `Rhin.logForm_lower_bound`, `|j log2 − q log3| ≥ j^{-13.3}`), `∃ α β, Conjecture62 α β` implies the
  excursion length `j` of a paradoxical `Ωⱼ(n)` (`n > 2`) is bounded by a constant.  Sorry-free —
  rests only on Rhin's cited bound (an exp-versus-power crossover discharges the boundedness).
* `paradoxical_start_le` — a paradoxical `Ωⱼ(n)` (`n > 2`) has starting value `n ≤ 2^j · 3^j`.
* `finite_paradoxical_of_length` — for each **fixed** length `j`, only finitely many paradoxical
  `Ωⱼ(n)` (`n > 2`).
* `finitely_many_paradoxical_of_paradoxical_length_bounded` — if the length is bounded (the conclusion
  of `paradoxical_length_bounded_of_conjecture_62`), the set of paradoxical sequences (`n > 2`) is
  finite.  Chaining the two implications through `conjecture_62` yields finiteness outright,
  contingent only on that open conjecture.

## References
* [Roz25] Rozier, Olivier, and Claude Terracol. "Paradoxical behavior in Collatz sequences."
  arXiv preprint arXiv:2502.00948 (2025). §6, eqs (15)–(21), Conjectures 6.1, 6.2, Proposition 6.3.
* [Rhi87] G. Rhin, effective irrationality measure for `u₀ + u₁ log 2 + u₂ log 3` (Proposition 6.3),
  formalized in `CITED.RhinLogForm`.
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

/-! ### The conjectures (open; recorded as `sorry`ed theorems, never asserted) -/

/-- The T-delay `d_T(n)`: the least `i` with `Tⁱ(n) = 1` (`0` if none). -/
@[category API, AMS 11 37, ref "Roz25", group "roz_heuristic"]
noncomputable def dT (n : ℕ) : ℕ := if h : ∃ i, T_iter i n = 1 then Nat.find h else 0

/-- **Conjecture 6.1** (Rozier–Terracol): there is no paradoxical sequence for `T` whose first term
exceeds `4614`. An **open** conjecture (stronger than both the Collatz and CST conjectures,
Corollary 3.3) — recorded as a `research open` theorem with `sorry`, not established here. -/
@[category research open, AMS 11 37, ref "Roz25", group "roz_heuristic"]
theorem conjecture_61 : ∀ j n : ℕ, IsParadoxical j n → n ≤ 4614 := by
  sorry

/-- The effective-bound predicate of §6: for constants `α, β > 0`, a delay bound (15)
`d_T(n) ≤ α log n` (and every `n ≥ 2` reaches `1`), together with the derived maximal-excursion
bound (16) `M_T(n) ≤ n^β` (phrased as `Tᵏ(n) ≤ n^β` for every `k`). This is the content of
Conjecture 6.2 for a *given* pair of constants; `conjecture_62` asserts such constants exist. -/
@[category API, AMS 11 37, ref "Roz25", group "roz_heuristic"]
def Conjecture62 (α β : ℝ) : Prop :=
  0 < α ∧ 0 < β ∧
  (∀ n : ℕ, 2 ≤ n → (∃ i, T_iter i n = 1) ∧ (dT n : ℝ) ≤ α * Real.log n) ∧
  (∀ n : ℕ, 2 ≤ n → ∀ k, (T_iter k n : ℝ) ≤ (n : ℝ) ^ β)

/-- **Conjecture 6.2** (Rozier–Terracol): there exist effective constants `α, β > 0` for which the
delay bound (15) and maximal-excursion bound (16) hold. An **open** hypothesis — recorded as a
`research open` theorem with `sorry`, not established here. -/
@[category research open, AMS 11 37, ref "Roz25", group "roz_heuristic"]
theorem conjecture_62 : ∃ α β : ℝ, Conjecture62 α β := by
  sorry

/-! ### The conditional heuristic -/

/-- **The §6 heuristic** ([Roz25], eqs (17)–(21)). Assuming Conjecture 6.2, every paradoxical
`Ωⱼ(n)` with `n > 2` satisfies inequality (21):

  `0 < j·log 2 − q·log 3 < (q/3)·exp(−j/(αβ))`.

Combined with Rhin's Proposition 6.3 (`paradoxical_length_bounded_of_conjecture_62`), the right-hand
side forces `j` to be bounded, supporting Conjecture 6.1 (finiteness of paradoxical sequences).
Proved on the min-term layer via `heuristic_19`; the harmonic mean is never used. -/
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

/-! ### §6 finiteness: (21) + Rhin's Proposition 6.3 bound the excursion length -/

/-- **§6 finiteness argument** ([Roz25], §6), as a pure implication from Conjecture 6.2. Given
`h : ∃ α β, Conjecture62 α β` (the statement of `conjecture_62`), the excursion length `j` of every
paradoxical `Ωⱼ(n)` with `n > 2` is bounded by a single constant, so there are only finitely many
possible lengths.

The mechanism is [Roz25]'s: inequality (21) (`heuristic_chain`) gives
`Λ := j·log 2 − q·log 3 < (q/3)·exp(−j/(αβ)) ≤ (j/3)·exp(−j/(αβ))` (using `q ≤ j`), while Rhin's
Proposition 6.3 (`Rhin.logForm_lower_bound`, with `(u₀,u₁,u₂) = (0, j, −q)`, whence
`H = max(j,q) = j`) gives `j^(−13.3) ≤ Λ`. Chaining, `3 < j^(14.3)·exp(−j/(αβ))`, which the
exp-versus-power crossover `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero` refutes for large `j`.
No `sorry`: rests only on Rhin's cited bound. Discharge the hypothesis with the open `conjecture_62`. -/
@[category research solved, AMS 11 37, ref "Roz25" "Rhi87", group "roz_heuristic"]
theorem paradoxical_length_bounded_of_conjecture_62
    (h : ∃ α β : ℝ, Conjecture62 α β) :
    ∃ J : ℕ, ∀ j n : ℕ, IsParadoxical j n → 2 < n → j ≤ J := by
  obtain ⟨α, β, hConj⟩ := h
  have hα : 0 < α := hConj.1
  have hβ : 0 < β := hConj.2.1
  have hb : (0 : ℝ) < 1 / (α * β) := by positivity
  -- `exp` outgrows the `14.3`-power: eventually `x^14.3 · exp(−x/(αβ)) < 3`.
  have htend := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 14.3 (1 / (α * β)) hb
  have hev := htend.eventually_lt_const (show (0 : ℝ) < 3 by norm_num)
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hev
  refine ⟨⌈M⌉₊, ?_⟩
  intro j n h_para hn
  by_contra hjJ
  push Not at hjJ
  -- basic facts about this paradoxical window
  have hn1 : 1 ≤ n := by omega
  have hj2 : 2 ≤ j := two_le_j_of_paradoxical j n h_para hn1
  have hj0 : (0 : ℝ) < (j : ℝ) := by positivity
  -- inequality (21)
  have hchain := heuristic_chain α β hConj j n h_para hn
  have hE_pos : (0 : ℝ) < Real.exp (-(j : ℝ) / (α * β)) := Real.exp_pos _
  have hqj_le : (num_odd_steps j n : ℝ) ≤ (j : ℝ) := by exact_mod_cast num_odd_steps_le j n
  have hΛ_ub : (j : ℝ) * Real.log 2 - (num_odd_steps j n : ℝ) * Real.log 3
      < (j : ℝ) / 3 * Real.exp (-(j : ℝ) / (α * β)) := by
    refine lt_of_lt_of_le hchain.2 ?_
    refine mul_le_mul_of_nonneg_right ?_ (le_of_lt hE_pos)
    linarith [hqj_le]
  -- Rhin Prop 6.3 with `(u₀,u₁,u₂) = (0, j, −q)`: `H = max j q = j` and `|Λ| = Λ`.
  have hqj_int : (num_odd_steps j n : ℤ) ≤ (j : ℤ) := by exact_mod_cast num_odd_steps_le j n
  have hH_eq : Rhin.logHeight (j : ℤ) (-(num_odd_steps j n : ℤ)) = (j : ℤ) := by
    simp only [Rhin.logHeight, abs_neg,
      abs_of_nonneg (show (0 : ℤ) ≤ (j : ℤ) by positivity),
      abs_of_nonneg (show (0 : ℤ) ≤ (num_odd_steps j n : ℤ) by positivity)]
    exact max_eq_left hqj_int
  have hH2 : (2 : ℤ) ≤ Rhin.logHeight (j : ℤ) (-(num_odd_steps j n : ℤ)) := by
    rw [hH_eq]; exact_mod_cast hj2
  have hrhin := Rhin.logForm_lower_bound 0 (j : ℤ) (-(num_odd_steps j n : ℤ)) hH2
  rw [hH_eq] at hrhin
  have hform : Rhin.logForm 0 (j : ℤ) (-(num_odd_steps j n : ℤ))
      = (j : ℝ) * Real.log 2 - (num_odd_steps j n : ℝ) * Real.log 3 := by
    simp only [Rhin.logForm]; push_cast; ring
  rw [hform, abs_of_pos hchain.1] at hrhin
  push_cast at hrhin
  -- `j^(−13.3) < (j/3)·E`
  have hRC : (j : ℝ) ^ (-(13.3 : ℝ)) < (j : ℝ) / 3 * Real.exp (-(j : ℝ) / (α * β)) :=
    lt_of_le_of_lt hrhin hΛ_ub
  -- rearrange to `3 < j^(14.3)·E`
  have hP : (0 : ℝ) < (j : ℝ) ^ (13.3 : ℝ) := Real.rpow_pos_of_pos hj0 _
  have e1 : (j : ℝ) ^ (-(13.3 : ℝ)) * (j : ℝ) ^ (13.3 : ℝ) = 1 := by
    rw [← Real.rpow_add hj0, show (-(13.3 : ℝ) + 13.3) = 0 by norm_num, Real.rpow_zero]
  have e2 : (j : ℝ) ^ (14.3 : ℝ) = (j : ℝ) ^ (13.3 : ℝ) * (j : ℝ) := by
    rw [show (14.3 : ℝ) = 13.3 + 1 by norm_num, Real.rpow_add hj0, Real.rpow_one]
  have key : (3 : ℝ) < (j : ℝ) ^ (14.3 : ℝ) * Real.exp (-(j : ℝ) / (α * β)) := by
    have hm := mul_lt_mul_of_pos_right hRC hP
    rw [e1] at hm
    rw [show ((j : ℝ) / 3 * Real.exp (-(j : ℝ) / (α * β))) * (j : ℝ) ^ (13.3 : ℝ)
          = (j : ℝ) ^ (14.3 : ℝ) * Real.exp (-(j : ℝ) / (α * β)) / 3 by rw [e2]; ring] at hm
    linarith
  -- contradiction with the crossover at `x = j`
  have hjM : M ≤ (j : ℝ) :=
    le_of_lt (lt_of_le_of_lt (Nat.le_ceil M) (by exact_mod_cast hjJ))
  have hcross : (j : ℝ) ^ (14.3 : ℝ) * Real.exp (-(1 / (α * β)) * (j : ℝ)) < 3 := hM (j : ℝ) hjM
  rw [show -(1 / (α * β)) * (j : ℝ) = -(j : ℝ) / (α * β) by ring] at hcross
  linarith [key, hcross]

/-! ### Finiteness of the set of paradoxical sequences -/

/-- For a paradoxical `Ωⱼ(n)` with `n > 2` the starting value is bounded in terms of the length:
`n ≤ 2^j · 3^j`.  Indeed `T_iter j n = C_j(n)·n + E_j(n)` (`linear_decomposition'`) with
`T_iter j n ≥ n`, so `n·(1 − C_j(n)) ≤ E_j(n) ≤ R(q) ≤ 3^q ≤ 3^j` (Theorem 2.2, `q ≤ j`), while
`C_j(n) = 3^q/2^j < 1` forces `2^j − 3^q ≥ 1`, i.e. `1 − C_j(n) ≥ 2^{-j}`; combining pins `n`. -/
@[category research solved, AMS 11 37, ref "Roz25", group "roz_heuristic"]
theorem paradoxical_start_le (j n : ℕ) (h : IsParadoxical j n) (hn : 2 < n) :
    n ≤ 2 ^ j * 3 ^ j := by
  have hn0 : 0 < n := by omega
  have hj : 0 < j := by have := two_le_j_of_paradoxical j n h (by omega); omega
  have hnQ : (0 : ℚ) < n := by exact_mod_cast hn0
  have h2j : (0 : ℚ) < 2 ^ j := by positivity
  have hqj : num_odd_steps j n ≤ j := num_odd_steps_le j n
  -- paradoxical ⟹ `1 − C ≤ E/n`; Theorem 2.2 ⟹ `E ≤ R q`
  have hb := (isParadoxical_bound hn0 h).2
  have hEub : E j n ≤ R (num_odd_steps j n) := (E_bounds j n hj).2
  -- `n·(1 − C) ≤ R q`
  have hnC : (n : ℚ) * (1 - C j n) ≤ R (num_odd_steps j n) := by
    rw [le_div_iff₀ hnQ] at hb
    nlinarith [hEub]
  -- `3^q < 2^j`, hence `3^q + 1 ≤ 2^j`
  have h3q : (3 : ℚ) ^ num_odd_steps j n < 2 ^ j := by
    have hC := h.2; rw [C, div_lt_one h2j] at hC; exact hC
  have h3qn : (3 : ℚ) ^ num_odd_steps j n + 1 ≤ 2 ^ j := by
    have hnat : (3 : ℕ) ^ num_odd_steps j n < 2 ^ j := by exact_mod_cast h3q
    calc (3 : ℚ) ^ num_odd_steps j n + 1 = ((3 ^ num_odd_steps j n + 1 : ℕ) : ℚ) := by push_cast; ring
      _ ≤ ((2 ^ j : ℕ) : ℚ) := by exact_mod_cast hnat
      _ = 2 ^ j := by push_cast; ring
  -- `1/2^j ≤ 1 − C`
  have hge1 : (1 : ℚ) / 2 ^ j ≤ 1 - C j n := by
    rw [C, le_sub_iff_add_le, ← add_div, div_le_one h2j]; linarith [h3qn]
  -- `n ≤ R q · 2^j`
  have hnR : (n : ℚ) ≤ R (num_odd_steps j n) * 2 ^ j := by
    have hstep : (n : ℚ) * (1 / 2 ^ j) ≤ R (num_odd_steps j n) :=
      le_trans (mul_le_mul_of_nonneg_left hge1 (le_of_lt hnQ)) hnC
    rw [mul_one_div, div_le_iff₀ h2j] at hstep
    exact hstep
  -- `R q ≤ 3^q ≤ 3^j`
  have hRq : R (num_odd_steps j n) ≤ 3 ^ num_odd_steps j n := by
    rw [R, div_le_iff₀ (by positivity : (0 : ℚ) < 2 ^ num_odd_steps j n)]
    have h1 : (1 : ℚ) ≤ 2 ^ num_odd_steps j n := one_le_pow₀ (by norm_num)
    have h3 : (0 : ℚ) < 3 ^ num_odd_steps j n := by positivity
    nlinarith [mul_nonneg (le_of_lt h3) (show (0 : ℚ) ≤ 2 ^ num_odd_steps j n - 1 by linarith), h1]
  have h3j : (3 : ℚ) ^ num_odd_steps j n ≤ 3 ^ j := pow_le_pow_right₀ (by norm_num) hqj
  -- assemble and drop to `ℕ`
  have hfin : (n : ℚ) ≤ 2 ^ j * 3 ^ j :=
    calc (n : ℚ) ≤ R (num_odd_steps j n) * 2 ^ j := hnR
      _ ≤ 3 ^ j * 2 ^ j := by
          apply mul_le_mul_of_nonneg_right (le_trans hRq h3j) (le_of_lt h2j)
      _ = 2 ^ j * 3 ^ j := by ring
  exact_mod_cast hfin

/-- **Finitely many paradoxical sequences of a given length.** For each fixed length `j`, only
finitely many `n > 2` yield a paradoxical `Ωⱼ(n)` — their starting values are all `≤ 2^j · 3^j`
(`paradoxical_start_le`). -/
@[category research solved, AMS 11 37, ref "Roz25", group "roz_heuristic"]
theorem finite_paradoxical_of_length (j : ℕ) :
    {n : ℕ | IsParadoxical j n ∧ 2 < n}.Finite := by
  apply Set.Finite.subset (Set.finite_Iic (2 ^ j * 3 ^ j))
  intro n hn
  exact paradoxical_start_le j n hn.1 hn.2

/-- **Bounded length ⟹ finitely many paradoxical sequences.** If the excursion length `j` of every
paradoxical `Ωⱼ(n)` with `n > 2` is bounded by a single constant (the conclusion of
`paradoxical_length_bounded_of_conjecture_62`), then there are only finitely many such paradoxical
sequences (pairs `(j, n)`): there are finitely many admissible lengths, and for each the starting
value is bounded by `paradoxical_start_le`. A pure implication — no `sorry`.

Chaining the two implications, `finitely_many_paradoxical_of_paradoxical_length_bounded
(paradoxical_length_bounded_of_conjecture_62 conjecture_62)` gives the finiteness of the paradoxical
set outright, contingent (only) on the open `conjecture_62`. -/
@[category research solved, AMS 11 37, ref "Roz25", group "roz_heuristic"]
theorem finitely_many_paradoxical_of_paradoxical_length_bounded
    (h : ∃ J : ℕ, ∀ j n : ℕ, IsParadoxical j n → 2 < n → j ≤ J) :
    {p : ℕ × ℕ | IsParadoxical p.1 p.2 ∧ 2 < p.2}.Finite := by
  obtain ⟨J, hJ⟩ := h
  apply Set.Finite.subset (Set.finite_Icc ((0, 0) : ℕ × ℕ) (J, 2 ^ J * 3 ^ J))
  rintro ⟨j, n⟩ ⟨hpar, hn⟩
  have hjJ : j ≤ J := hJ j n hpar hn
  have hnB : n ≤ 2 ^ J * 3 ^ J :=
    le_trans (paradoxical_start_le j n hpar hn)
      (Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hjJ)
        (Nat.pow_le_pow_right (by norm_num) hjJ))
  simp only [Set.mem_Icc, Prod.mk_le_mk]
  exact ⟨⟨Nat.zero_le _, Nat.zero_le _⟩, hjJ, hnB⟩

end RT
