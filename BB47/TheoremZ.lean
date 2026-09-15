/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB47.OmegaLimit
import Mathlib.Analysis.Asymptotics.ExpGrowth

/-!
# Theorem Z: the eventual complexity carries the whole entropy

**Theorem Z.**  For every infinite word `u` over a finite alphabet the ordinary factor complexity
`p(n, u)` and the eventual complexity `p_∞(n, u)` have the *same* exponential growth rate:

  `lim (log p(n, u)) / n = lim (log p_∞(n, u)) / n`,

and both limits exist.  In the vocabulary of `plans/plan2-1047.html` §3.1: the topological entropy
of the orbit closure of `u` equals the topological entropy of its `ω`-limit subshift `Ω(u)`.

The consequence that makes this worth stating is the last theorem of the file.  Under the standing
hypothesis (H) of `BB47/M3.tex` — `u` not eventually periodic and `p_∞(n, u) = n + 1` — the
*whole* expansion has zero entropy, `p(n, u) = e^{o(n)}`, even though `p(n, u)` itself is
completely unconstrained by (H): the horizon `s_n` may grow arbitrarily fast.  Contrapositively,
**a base-`b` expansion of positive entropy cannot satisfy (H)**, so Problem 10.47 sits strictly
below the conjecture that algebraic irrationals have positive-entropy expansions — and, through
`BB47.pInf_eq_complexity` together with [M3, Lem. 3.2], below Mahler's missing-digit problem.
Problem 10.47 is the lowest rung of the zero-entropy ladder.

## The proof that is formalized

The note `BB47/af.md` gives two proofs.  The first is the variational principle: an invariant
measure on the orbit closure gives zero mass to the (non-recurrent) orbit itself, so it lives on
`Ω(u)`.  That route needs the whole measure-theoretic apparatus.  The second is elementary,
quantitative and is the one formalized here, in the following sharp form:

  `p(m · k, u) ≤ s_m + p_∞(m, u) ^ k`   (`BB47.pComplexity_mul_le_horizon_add_pInf_pow`)

for **every** `m` and `k`.  Its proof is two lines of counting.  A length-`(m·k)` block occurring
at a position `≥ s_m` splits into `k` consecutive length-`m` blocks, each of which occurs at a
position `≥ s_m` and is therefore recurrent; so such a block is one of at most `p_∞(m)^k`
concatenations.  Every other length-`(m·k)` block occurs only at positions `< s_m`, and there are
at most `s_m` of those.  This replaces the Rauzy-graph walk count of `af.md` — the reduced Rauzy
graph is not needed, only submultiplicativity of the complexity of the tail
(`ForMathlib.SubwordComplexity.pComplexity_mul_le`).

Dividing and letting `k → ∞` gives `h(u) ≤ log p_∞(m) / m` for every `m ≥ 1`, hence
`h(u) ≤ liminf (log p_∞(n)) / n`; and `p_∞ ≤ p` gives the reverse.  All four quantities —
`limsup` and `liminf` of `log p(n)/n` and of `log p_∞(n)/n` — therefore coincide, which is why
both limits exist (`BB47.tendsto_log_pComplexity_div`, `BB47.tendsto_log_pInf_div`).  No Fekete
argument is needed: the `m`-fold bound does the work of the subadditivity lemma.

## Main results

* `BB47.pComplexity_le_horizon_add_pInf` — the **horizon bound** `p(n) ≤ s_n + p_∞(n)`, face 1 of
  the wall of `plans/plan2-1047.html` §2.
* `BB47.pComplexity_mul_le_horizon_add_pInf_pow`, `BB47.pComplexity_le_horizon_add_pInf_pow` —
  the quantitative form of Theorem Z.
* `BB47.wordEntropy`, `BB47.pInfEntropy` — the two growth rates, as `EReal`s.
* `BB47.theoremZ` — **Theorem Z**: `wordEntropy u = pInfEntropy u`.
* `BB47.tendsto_log_pComplexity_div`, `BB47.tendsto_log_pInf_div` — the two limits exist.
* `BB47.wordEntropy_eq_zero_of_pInf_eq_succ`, `BB47.wordEntropy_eq_zero_of_frequently` — **zero
  entropy under (H)**, stated both with "for all `n`" and with the "for infinitely many `n`" form
  that [M3] uses (the two are equivalent by `BB47.pInf_eq_succ_of_frequently`).
* `BB47.exists_pInf_ne_succ_of_wordEntropy_pos` — the contrapositive: positive entropy of the
  expansion refutes (H).  This is "Conjecture E ⇒ Problem 10.47" of `plans/plan2-1047.html` §3.1.

## References

* [Bug12] Y. Bugeaud, *Distribution Modulo One and Diophantine Approximation*, Cambridge Tracts
  193, CUP 2012 — Problem 10.47, p. 221.
* [MH38] M. Morse, G. A. Hedlund, *Symbolic dynamics*, Amer. J. Math. **60** (1938), 815–866.
* [M3] `BB47/M3.tex` (this repository, 2026-09) — the standing hypothesis (H), Lem. 3.2.
* [af] `BB47/af.md` (this repository, 2026-09) — §2, Theorem Z with both proofs; merged as
  `plans/plan2-1047.html` §3.1.
-/

namespace BB47

open ForMathlib.SubwordComplexity ExpGrowth ENNReal Filter

variable {α : Type*} [Finite α]

/-! ## Two elementary comparisons -/

omit [Finite α] in
/-- A recurrent block is in particular a block. -/
@[category API, AMS 11 37 68, ref "Bug12", group "bugeaud_10_47"]
theorem recFactorSet_subset_factorSet (u : ℕ → α) (n : ℕ) :
    recFactorSet u n ⊆ factorSet u n := by
  intro v hv
  obtain ⟨i, -, hfi⟩ := hv 0
  exact ⟨i, hfi⟩

/-- `p_∞(n) ≤ p(n)`: the eventual complexity never exceeds the complexity. -/
@[category API, AMS 11 37 68, ref "Bug12", group "bugeaud_10_47"]
theorem pInf_le_pComplexity (u : ℕ → α) (n : ℕ) : pInf u n ≤ pComplexity u n :=
  Set.ncard_le_ncard (recFactorSet_subset_factorSet u n) (Set.toFinite _)

/-- `p_∞(n) ≥ 1`: over a finite alphabet *some* block of each length recurs — the one sitting at
the horizon. -/
@[category API, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem pInf_pos (u : ℕ → α) (n : ℕ) : 0 < pInf u n :=
  (Set.ncard_pos (Set.toFinite _)).mpr
    ⟨factor u n (horizon u n), recurrent_of_horizon_le le_rfl⟩

/-! ## The counting bound -/

omit [Finite α] in
/-- **Splitting the positions at `s`.**  A length-`N` block either occurs at one of the `s`
positions `< s`, or it is a block of the tail `tail u s`. -/
@[category API, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem pComplexity_le_add_pComplexity_tail (u : ℕ → α) (s N : ℕ) :
    pComplexity u N ≤ s + pComplexity (tail u s) N := by
  have hsplit : factorSet u N = factor u N '' Set.Iio s ∪ factorSet (tail u s) N := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      rcases lt_or_ge i s with h | h
      · exact Or.inl ⟨i, h, rfl⟩
      · exact Or.inr ⟨i - s, by rw [factor_tail, show s + (i - s) = i by omega]⟩
    · rintro (⟨i, -, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨i, rfl⟩
      · exact ⟨s + i, (factor_tail u s N i).symm⟩
  have h1 : (factor u N '' Set.Iio s).ncard ≤ s := by
    refine le_trans (Set.ncard_image_le (Set.finite_Iio s)) ?_
    rw [← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]
  calc pComplexity u N
      = (factor u N '' Set.Iio s ∪ factorSet (tail u s) N).ncard := by rw [pComplexity, hsplit]
    _ ≤ (factor u N '' Set.Iio s).ncard + (factorSet (tail u s) N).ncard := Set.ncard_union_le _ _
    _ ≤ s + pComplexity (tail u s) N := Nat.add_le_add_right h1 _

/-- **The horizon bound** `p(n) ≤ s_n + p_∞(n)` — face 1 of the wall: the only unconditional
link between the complexity of `u` and the function of Problem 10.47, and it is useless on its
own because `s_n` is unconstrained. -/
@[category research solved, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem pComplexity_le_horizon_add_pInf (u : ℕ → α) (n : ℕ) :
    pComplexity u n ≤ horizon u n + pInf u n := by
  have h := pComplexity_le_add_pComplexity_tail u (horizon u n) n
  rwa [← pInf_eq_pComplexity_tail (le_refl (horizon u n))] at h

/-- **The quantitative form of Theorem Z.**  For *every* pair `(m, k)`,

  `p(m · k, u) ≤ s_m + p_∞(m, u) ^ k`.

Past the horizon `s_m` a length-`(m·k)` block is a concatenation of `k` recurrent length-`m`
blocks; before it there are at most `s_m` positions.  Note the asymmetry that makes the theorem
work: the *constant* `s_m` depends only on `m`, while the exponential depends only on `p_∞`. -/
@[category research solved, AMS 11 37 68, ref "Bug12" "BKK26", group "bugeaud_10_47"]
theorem pComplexity_mul_le_horizon_add_pInf_pow (u : ℕ → α) (m k : ℕ) :
    pComplexity u (m * k) ≤ horizon u m + pInf u m ^ k := by
  have h1 := pComplexity_le_add_pComplexity_tail u (horizon u m) (m * k)
  have h2 := pComplexity_mul_le (tail u (horizon u m)) m k
  rw [← pInf_eq_pComplexity_tail (le_refl (horizon u m))] at h2
  exact le_trans h1 (Nat.add_le_add_left h2 _)

/-- The same bound at every length, not only the multiples of `m`. -/
@[category research solved, AMS 11 37 68, ref "Bug12" "BKK26", group "bugeaud_10_47"]
theorem pComplexity_le_horizon_add_pInf_pow {u : ℕ → α} {N m k : ℕ} (hN : N ≤ m * k) :
    pComplexity u N ≤ horizon u m + pInf u m ^ k :=
  le_trans (monotone_pComplexity u hN) (pComplexity_mul_le_horizon_add_pInf_pow u m k)

/-! ## The two growth rates -/

/-- **The entropy of the word** `u`: the exponential growth rate `lim (log p(n, u)) / n` of its
factor complexity, equivalently the topological entropy of the orbit closure of `u`.  (The
definition is a `limsup`; `BB47.tendsto_log_pComplexity_div` shows the limit exists.) -/
@[category API, AMS 11 37 68, ref "Bug12", group "bugeaud_10_47"]
noncomputable def wordEntropy (u : ℕ → α) : EReal :=
  expGrowthSup fun n => (pComplexity u n : ℝ≥0∞)

/-- **The eventual entropy** of `u`: the growth rate of `p_∞`.  By `BB47.pInf_eq_complexity` this
is the topological entropy of the `ω`-limit subshift `Ω(u)`. -/
@[category API, AMS 11 37 68, ref "Bug12", group "bugeaud_10_47"]
noncomputable def pInfEntropy (u : ℕ → α) : EReal :=
  expGrowthSup fun n => (pInf u n : ℝ≥0∞)

/-- `pInfEntropy u` is the topological entropy of `Ω(u)` — [M1M2, Prop. 2.4] at the level of
growth rates. -/
@[category API, AMS 11 37 68, ref "Bug12", group "bugeaud_10_47"]
theorem pInfEntropy_eq_omegaLimit [TopologicalSpace α] [DiscreteTopology α] (u : ℕ → α) :
    pInfEntropy u = expGrowthSup fun n => (((omegaLimitSubshift u).complexity n : ℕ) : ℝ≥0∞) := by
  rw [pInfEntropy]
  exact congrArg expGrowthSup (funext fun n => by rw [pInf_eq_complexity])

@[category API, AMS 11 37 68, ref "MH38", group "bugeaud_10_47"]
lemma monotone_pComplexity_cast (u : ℕ → α) :
    Monotone fun n => ((pComplexity u n : ℕ) : ℝ≥0∞) := by
  intro a b h
  dsimp only
  exact_mod_cast monotone_pComplexity u h

/-- The single inequality Theorem Z rests on: `h(u) ≤ (log p_∞(m)) / m` for **every** `m ≥ 1`.
Dividing the quantitative bound by `m·k` and letting `k → ∞` kills the constant `s_m`. -/
@[category research solved, AMS 11 37 68, ref "Bug12", group "bugeaud_10_47"]
theorem wordEntropy_le_log_div (u : ℕ → α) {m : ℕ} (hm : 0 < m) :
    wordEntropy u ≤ ENNReal.log ((pInf u m : ℕ) : ℝ≥0∞) / (m : EReal) := by
  rw [EReal.le_div_iff_mul_le (by exact_mod_cast hm) (EReal.natCast_ne_top m)]
  have key : ∀ n : ℕ, ((pComplexity u (m * n) : ℕ) : ℝ≥0∞)
      ≤ ((horizon u m + 1 : ℕ) : ℝ≥0∞) * (((pInf u m : ℕ) : ℝ≥0∞)) ^ n := by
    intro n
    have hpos : 0 < pInf u m ^ n := pow_pos (pInf_pos u m) n
    have hnat : pComplexity u (m * n) ≤ (horizon u m + 1) * pInf u m ^ n := by
      calc pComplexity u (m * n) ≤ horizon u m + pInf u m ^ n :=
            pComplexity_mul_le_horizon_add_pInf_pow u m n
        _ ≤ horizon u m * pInf u m ^ n + pInf u m ^ n :=
            Nat.add_le_add_right (Nat.le_mul_of_pos_right _ hpos) _
        _ = (horizon u m + 1) * pInf u m ^ n := by ring
    exact_mod_cast hnat
  have hle : expGrowthSup (fun n => ((pComplexity u (m * n) : ℕ) : ℝ≥0∞))
      ≤ expGrowthSup (fun n => (((pInf u m : ℕ) : ℝ≥0∞)) ^ n) :=
    expGrowthSup_le_of_eventually_le (ENNReal.natCast_ne_top _) (Eventually.of_forall key)
  rw [expGrowthSup_pow] at hle
  have hcm : expGrowthSup (fun n => ((pComplexity u (m * n) : ℕ) : ℝ≥0∞))
      = (m : EReal) * wordEntropy u :=
    (monotone_pComplexity_cast u).expGrowthSup_comp_mul hm.ne'
  rw [hcm] at hle
  rwa [EReal.mul_comm]

/-- Consequently `h(u)` is below the **liminf** of `(log p_∞(n)) / n`, not merely its limsup.
This is what collapses all four growth rates at once. -/
@[category research solved, AMS 11 37 68, ref "Bug12", group "bugeaud_10_47"]
theorem wordEntropy_le_expGrowthInf_pInf (u : ℕ → α) :
    wordEntropy u ≤ expGrowthInf (fun n => ((pInf u n : ℕ) : ℝ≥0∞)) := by
  rw [expGrowthInf]
  refine le_liminf_of_le (h := ?_)
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact wordEntropy_le_log_div u hn

/-! ## Theorem Z -/

/-- **Theorem Z.**  The whole word and its `ω`-limit subshift have the same entropy:

  `lim (log p(n, u)) / n = lim (log p_∞(n, u)) / n`.

The non-recurrent part of `u` — of which the horizon `s_n` is the only measure, and which (H)
leaves completely free — contributes nothing to the exponential growth rate. -/
@[category research solved, AMS 11 37 68, ref "Bug12" "BKK26", group "bugeaud_10_47"]
theorem theoremZ (u : ℕ → α) : wordEntropy u = pInfEntropy u := by
  refine le_antisymm ?_ ?_
  · exact le_trans (wordEntropy_le_expGrowthInf_pInf u) expGrowthInf_le_expGrowthSup
  · exact expGrowthSup_monotone fun n => by exact_mod_cast pInf_le_pComplexity u n

/-- The `liminf` of `(log p_∞(n)) / n` agrees with its `limsup`. -/
@[category research solved, AMS 11 37 68, ref "Bug12", group "bugeaud_10_47"]
theorem expGrowthInf_pInf_eq (u : ℕ → α) :
    expGrowthInf (fun n => ((pInf u n : ℕ) : ℝ≥0∞)) = pInfEntropy u :=
  le_antisymm expGrowthInf_le_expGrowthSup
    (by rw [← theoremZ]; exact wordEntropy_le_expGrowthInf_pInf u)

/-- …and so does the `liminf` of `(log p(n)) / n`. -/
@[category research solved, AMS 11 37 68, ref "Bug12", group "bugeaud_10_47"]
theorem expGrowthInf_pComplexity_eq (u : ℕ → α) :
    expGrowthInf (fun n => ((pComplexity u n : ℕ) : ℝ≥0∞)) = wordEntropy u :=
  le_antisymm expGrowthInf_le_expGrowthSup
    (le_trans (wordEntropy_le_expGrowthInf_pInf u)
      (expGrowthInf_monotone fun n => by exact_mod_cast pInf_le_pComplexity u n))

/-- **The limit exists**: `(log p(n, u)) / n → wordEntropy u`.  The `lim` of Theorem Z is a genuine
limit, not a `limsup`. -/
@[category research solved, AMS 11 37 68, ref "MH38", group "bugeaud_10_47"]
theorem tendsto_log_pComplexity_div (u : ℕ → α) :
    Tendsto (fun n : ℕ => ENNReal.log ((pComplexity u n : ℕ) : ℝ≥0∞) / (n : EReal))
      atTop (nhds (wordEntropy u)) :=
  tendsto_of_liminf_eq_limsup (expGrowthInf_pComplexity_eq u) rfl

/-- …and so does the limit for `p_∞`, to the same value. -/
@[category research solved, AMS 11 37 68, ref "Bug12", group "bugeaud_10_47"]
theorem tendsto_log_pInf_div (u : ℕ → α) :
    Tendsto (fun n : ℕ => ENNReal.log ((pInf u n : ℕ) : ℝ≥0∞) / (n : EReal))
      atTop (nhds (wordEntropy u)) := by
  rw [theoremZ]
  exact tendsto_of_liminf_eq_limsup (expGrowthInf_pInf_eq u) rfl

/-! ## Zero entropy under the standing hypothesis (H) -/

/-- A sequence of **exactly linear** growth has exponential growth rate `0`.

The proof is the doubling trick, which avoids any analysis of `log n / n`: the growth rate `x`
satisfies `2 x ≤ x` because `v (2n) ≤ 2 · v n`, and `0 ≤ x ≤ log 2 < ⊤`, so `x = 0`. -/
@[category API, AMS 11 37, ref "MH38", group "bugeaud_10_47"]
lemma expGrowthSup_natCast_succ : expGrowthSup (fun n : ℕ => ((n : ℝ≥0∞) + 1)) = 0 := by
  set v : ℕ → ℝ≥0∞ := fun n => (n : ℝ≥0∞) + 1 with hvdef
  have hmono : Monotone v := by
    intro a b h
    simp only [hvdef]
    gcongr
  have hv0 : v ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp [hvdef] at h0
  have hnn : 0 ≤ expGrowthSup v := hmono.expGrowthSup_nonneg hv0
  have hub : expGrowthSup v ≤ ENNReal.log 2 := by
    have h2 : v ≤ fun n => (2 : ℝ≥0∞) ^ n := by
      intro n
      simp only [hvdef]
      have hn : (n + 1 : ℕ) ≤ 2 ^ n := Nat.succ_le_of_lt Nat.lt_two_pow_self
      calc (n : ℝ≥0∞) + 1 = ((n + 1 : ℕ) : ℝ≥0∞) := by push_cast; ring
        _ ≤ ((2 ^ n : ℕ) : ℝ≥0∞) := by exact_mod_cast hn
        _ = (2 : ℝ≥0∞) ^ n := by push_cast; ring
    calc expGrowthSup v ≤ expGrowthSup (fun n => (2 : ℝ≥0∞) ^ n) := expGrowthSup_monotone h2
      _ = ENNReal.log 2 := expGrowthSup_pow
  have hpt : ∀ n : ℕ, v (2 * n) ≤ 2 * v n := by
    intro n
    simp only [hvdef]
    push_cast
    rw [mul_add, mul_one]
    gcongr
    norm_num
  have hdouble : ((2 : ℕ) : EReal) * expGrowthSup v ≤ expGrowthSup v := by
    have h1 : expGrowthSup (fun n => v (2 * n)) = ((2 : ℕ) : EReal) * expGrowthSup v :=
      hmono.expGrowthSup_comp_mul (by norm_num)
    have h2 : expGrowthSup (fun n => v (2 * n)) ≤ expGrowthSup v :=
      expGrowthSup_le_of_eventually_le (b := 2) (by simp) (Eventually.of_forall hpt)
    rw [h1] at h2
    exact h2
  have hxtop : expGrowthSup v ≠ ⊤ := by
    intro h
    rw [h, top_le_iff, ENNReal.log_eq_top_iff] at hub
    simp at hub
  set x := expGrowthSup v with hxdef
  lift x to ℝ using ⟨hxtop, fun hb => by simp [hb] at hnn⟩ with r
  rw [← EReal.coe_natCast, ← EReal.coe_mul, EReal.coe_le_coe_iff] at hdouble
  have h2 : (0 : ℝ) ≤ r := by exact_mod_cast hnn
  have hr : r = 0 := by push_cast at hdouble; linarith
  rw [hr]
  rfl

/-- **Zero entropy under (H).**  If `p_∞(n, u) = n + 1` for every `n`, then the *whole* word has
zero entropy: `p(n, u) = e^{o(n)}`.

This is the headline consequence for Problem 10.47.  The hypothesis says nothing at all about
`p(n, u)`, which the horizon `s_n` may push up arbitrarily fast at any fixed scale; Theorem Z
says the growth *rate* is nevertheless pinned to `0`. -/
@[category research solved, AMS 11 37 68, ref "Bug12", group "bugeaud_10_47"]
theorem wordEntropy_eq_zero_of_pInf_eq_succ {u : ℕ → α} (h : ∀ n, pInf u n = n + 1) :
    wordEntropy u = 0 := by
  rw [theoremZ, pInfEntropy]
  have hfun : (fun n => ((pInf u n : ℕ) : ℝ≥0∞)) = fun n : ℕ => ((n : ℝ≥0∞) + 1) := by
    funext n
    rw [h n]
    push_cast
    ring
  rw [hfun, expGrowthSup_natCast_succ]

/-- The same, with the hypothesis in the form (H) is actually stated in: minimal eventual
complexity at *infinitely many* scales.  The two are equivalent by `BB47.pInf_eq_succ_of_frequently`. -/
@[category research solved, AMS 11 37 68, ref "Bug12", group "bugeaud_10_47"]
theorem wordEntropy_eq_zero_of_frequently {u : ℕ → α} (hu : ¬ IsEventuallyPeriodic u)
    (h : ∀ N, ∃ n, N ≤ n ∧ pInf u n = n + 1) : wordEntropy u = 0 :=
  wordEntropy_eq_zero_of_pInf_eq_succ (pInf_eq_succ_of_frequently hu h)

/-- The explicit subexponential bound under (H): `p(N) ≤ s_m + (m+1)^k` whenever `N ≤ m · k`.
Taking `m` slowly increasing turns this into `p(N) = e^{o(N)}`; taking `m` fixed it is already the
useful form, since `s_m` is a constant. -/
@[category research solved, AMS 11 37 68, ref "Bug12", group "bugeaud_10_47"]
theorem pComplexity_le_of_pInf_eq_succ {u : ℕ → α} (h : ∀ n, pInf u n = n + 1) {N m k : ℕ}
    (hN : N ≤ m * k) : pComplexity u N ≤ horizon u m + (m + 1) ^ k := by
  have hb := pComplexity_le_horizon_add_pInf_pow (u := u) hN
  rwa [h m] at hb

/-- **Conjecture E ⇒ Problem 10.47.**  A word whose complexity grows exponentially cannot have
`p_∞(n) = n + 1` at every scale.  So the conjecture that the base-`b` expansion of an algebraic
irrational has positive entropy — far weaker than normality, and implied by it — already settles
Problem 10.47, in the strong form "`p_∞` is not subexponential". -/
@[category research solved, AMS 11 37 68, ref "Bug12", group "bugeaud_10_47"]
theorem exists_pInf_ne_succ_of_wordEntropy_pos {u : ℕ → α} (h : 0 < wordEntropy u) :
    ∃ n, pInf u n ≠ n + 1 := by
  by_contra hc
  push Not at hc
  exact absurd (wordEntropy_eq_zero_of_pInf_eq_succ hc) h.ne'

end BB47
