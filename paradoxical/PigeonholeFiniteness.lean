/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import RT.Heuristic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Per-`R` conditional finiteness of a paradoxical slice (research program I.1.2)

The Lean core of the bounded-circuit Baker reduction for a *fixed number of
circuits* `R` (`length-bound.html` §4d; mechanized in `nearcycle_baker.py`).  For a
class `P` of paradoxical sequences with `R` circuits the reduction assembles three
inputs — two unconditional, one open:

* **pigeonhole** (unconditional): `max(aᵢ,eᵢ) ≥ j/(2R)`, so the excursion satisfies
  `2^{j/(2R)} - 1 ≤ Exc j n`;
* **least-term bound** (unconditional, RT Cor 4.4 + Rhin): `m j n ≤ C·j^Pw`
  (with `Pw = 14.3`);
* **excursion bound** (the one missing hypothesis, RT Conjecture 6.2):
  `Exc j n ≤ (m j n)^β`.

The heart is `exp_poly_collision`: an exponential lower bound `exp(a·j)` capped by a
polynomial `K·j^Q` forces `j` bounded.  Chaining
`2^{j/(2R)} - 1 ≤ Exc ≤ m^β ≤ (C j^Pw)^β = C^β j^{Pw·β}` (exponential ≤ polynomial)
bounds the length; per-length finiteness (`RT.paradoxical_start_le`,
`n ≤ 2^j·3^j`) then makes the whole slice finite: `finite_of_pigeonhole`.

`Exc`, `m` and the two unconditional bounds enter as *hypotheses* (they are the
unconditional links of the reduction, verified numerically in `nearcycle_baker.py`);
only the excursion bound `hexc` is conjectural.  This mirrors
`RT.finitely_many_paradoxical_of_paradoxical_length_bounded`, which likewise takes
length-boundedness as a hypothesis.  Instantiate `P j n` as “`Ωⱼ(n)` is paradoxical
with `n > 2`, `Tʲ(n) = n+1`, and `R` circuits”, `Exc`/`m` as the actual excursion
and least odd term; then `hpigeon`/`hmH` are the unconditional facts and `hexc` is
the sole conjectural input.  A bound uniform over *all* `R` would be Collatz itself.

`sorry`-free (`propext, Classical.choice, Quot.sound`).
-/

open Filter

namespace Paradoxical

open RT CC

/-- **Exponential beats polynomial.**  If `exp(a·j) - 1 ≤ K·j^Q` for `a > 0`,
`K, Q ≥ 0`, then `j` is bounded: there is a `J` with `j ≤ J` for every such `j`.
The analytic engine of the per-`R` length bound. -/
lemma exp_poly_collision (a : ℝ) (ha : 0 < a) (K Q : ℝ) (hK : 0 ≤ K) (hQ : 0 ≤ Q) :
    ∃ J : ℕ, ∀ j : ℕ, Real.exp (a * j) - 1 ≤ K * (j : ℝ) ^ Q → j ≤ J := by
  have htend := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero Q a ha
  have hev := htend.eventually_lt_const (show (0 : ℝ) < 1 / (K + 1) by positivity)
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hev
  refine ⟨⌈M⌉₊, ?_⟩
  intro j hj
  by_contra hjJ
  have hjJ' : ⌈M⌉₊ < j := not_le.mp hjJ
  have hjge1 : 1 ≤ j := by omega
  have hjR : M ≤ (j : ℝ) := le_of_lt (lt_of_le_of_lt (Nat.le_ceil M) (by exact_mod_cast hjJ'))
  have h1 : (j : ℝ) ^ Q * Real.exp (-a * j) < 1 / (K + 1) := hM (j : ℝ) hjR
  have hexp_pos : (0 : ℝ) < Real.exp (a * j) := Real.exp_pos _
  have hjQ1 : (1 : ℝ) ≤ (j : ℝ) ^ Q := Real.one_le_rpow (by exact_mod_cast hjge1) hQ
  have hK1 : (0 : ℝ) < K + 1 := by linarith
  have he : (j : ℝ) ^ Q * Real.exp (-a * j) * Real.exp (a * j) = (j : ℝ) ^ Q := by
    have h0 : -a * (j : ℝ) + a * (j : ℝ) = 0 := by ring
    rw [mul_assoc, ← Real.exp_add, h0, Real.exp_zero, mul_one]
  have hmul := mul_lt_mul_of_pos_right h1 hexp_pos
  rw [he] at hmul
  have h3 : (K + 1) * (j : ℝ) ^ Q < Real.exp (a * j) := by
    have hml := mul_lt_mul_of_pos_left hmul hK1
    rwa [show (K + 1) * (1 / (K + 1) * Real.exp (a * j)) = Real.exp (a * j) by field_simp] at hml
  have h4 : Real.exp (a * j) ≤ (K + 1) * (j : ℝ) ^ Q := by
    calc Real.exp (a * j) ≤ K * (j : ℝ) ^ Q + 1 := by linarith [hj]
      _ ≤ K * (j : ℝ) ^ Q + (j : ℝ) ^ Q := by linarith [hjQ1]
      _ = (K + 1) * (j : ℝ) ^ Q := by ring
  linarith [h3, h4]

/-- **Per-`R` conditional finiteness.**  Fix `R ≥ 1` and constants `β, Pw ≥ 0`,
`C > 0`.  Let `P` be a class of paradoxical sequences (`n > 2`) with

* pigeonhole excursion lower bound  `2^{j/(2R)} - 1 ≤ Exc j n`  (unconditional),
* least-term upper bound  `m j n ≤ C·j^Pw`  (unconditional; `1 ≤ m j n`), and
* excursion bound  `Exc j n ≤ (m j n)^β`  (the sole conjectural hypothesis).

Then `{(j, n) | P j n}` is **finite**: the collision caps the length `j ≤ J`, and
each length admits only finitely many starts (`n ≤ 2^j·3^j`). -/
theorem finite_of_pigeonhole (R : ℕ) (hR : 0 < R) (β Pw C : ℝ)
    (hβ : 0 ≤ β) (hPw : 0 ≤ Pw) (hC : 0 < C)
    (P : ℕ → ℕ → Prop) (Exc m : ℕ → ℕ → ℝ)
    (hpar : ∀ j n, P j n → IsParadoxical j n)
    (hn : ∀ j n, P j n → 2 < n)
    (hpigeon : ∀ j n, P j n → (2 : ℝ) ^ ((j : ℝ) / (2 * R)) - 1 ≤ Exc j n)
    (hm1 : ∀ j n, P j n → 1 ≤ m j n)
    (hmH : ∀ j n, P j n → m j n ≤ C * (j : ℝ) ^ Pw)
    (hexc : ∀ j n, P j n → Exc j n ≤ (m j n) ^ β) :
    {p : ℕ × ℕ | P p.1 p.2}.Finite := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hRR : (0 : ℝ) < R := by exact_mod_cast hR
  have h2R : (0 : ℝ) < 2 * R := by positivity
  set a := Real.log 2 / (2 * R) with ha_def
  have ha : 0 < a := div_pos hlog2 h2R
  obtain ⟨J, hJ⟩ := exp_poly_collision a ha (C ^ β) (Pw * β)
    (Real.rpow_nonneg (le_of_lt hC) β) (mul_nonneg hPw hβ)
  -- length bound for the slice `P`, via the exponential-vs-polynomial collision
  have hlen : ∀ j n, P j n → j ≤ J := by
    intro j n hp
    apply hJ j
    have hjnn : (0 : ℝ) ≤ (j : ℝ) := by positivity
    have hconv : (2 : ℝ) ^ ((j : ℝ) / (2 * R)) = Real.exp (a * j) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ha_def]; congr 1; ring
    have hexpand : (C * (j : ℝ) ^ Pw) ^ β = C ^ β * (j : ℝ) ^ (Pw * β) := by
      rw [Real.mul_rpow (le_of_lt hC) (Real.rpow_nonneg hjnn Pw), ← Real.rpow_mul hjnn]
    rw [← hconv]
    calc (2 : ℝ) ^ ((j : ℝ) / (2 * R)) - 1
        ≤ Exc j n := hpigeon j n hp
      _ ≤ (m j n) ^ β := hexc j n hp
      _ ≤ (C * (j : ℝ) ^ Pw) ^ β :=
          Real.rpow_le_rpow (by linarith [hm1 j n hp]) (hmH j n hp) hβ
      _ = C ^ β * (j : ℝ) ^ (Pw * β) := hexpand
  -- finiteness: bounded length × bounded start (RT.paradoxical_start_le)
  apply Set.Finite.subset (Set.finite_Icc ((0, 0) : ℕ × ℕ) (J, 2 ^ J * 3 ^ J))
  rintro ⟨j, n⟩ hp
  simp only [Set.mem_setOf_eq] at hp
  have hjJ : j ≤ J := hlen j n hp
  have hnB : n ≤ 2 ^ J * 3 ^ J :=
    le_trans (paradoxical_start_le j n (hpar j n hp) (hn j n hp))
      (Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hjJ)
        (Nat.pow_le_pow_right (by norm_num) hjJ))
  simp only [Set.mem_Icc, Prod.mk_le_mk]
  exact ⟨⟨Nat.zero_le _, Nat.zero_le _⟩, hjJ, hnB⟩

end Paradoxical
