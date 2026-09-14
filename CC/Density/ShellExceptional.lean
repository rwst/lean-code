/-
(C) 2026 Nikolay Metchev, in collaboration with GitHub Copilot.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CC.Density.DescentFromResidue
import CC.Density.ShellCount
import CC.SRSBridge
import CET.VaryingShellDensity
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Shell exceptional ratio for Terras density-1

Step 4 of the roadmap in [CC/Density/TerrasDensity.lean](./TerrasDensity.lean):
fixing the shell → parameter choice and driving the shell exceptional fraction
to zero. The headline theorem itself is assembled in `TerrasDensity.lean` from
`shellExceptionalRatio_Descends_tendsto_zero` below.

## One ratio, used twice

Everything quantitative in this file descends from the single numerical fact

  `3 ^ 5 = 243 ≤ 256 = 2 ^ 8`,

i.e. `5 / 8 ≤ log 2 / log 3 = CC.SRSBridge.criticalRatio ≈ 0.63093`. The
parametric lemma `pow_three_ratio_lt_pow_two` turns that one fact into
`3 ^ (5 · j / 8) < 2 ^ j` for every `j ≥ 1`, and it is instantiated twice:

* at `j = M` for the **shell condition** `3 ^ shellLevel M ≤ 2 ^ M`, the
  `3 ^ k ≤ n` hypothesis of `descent_of_not_mem_badResidues`;
* at `j = shellLevel M` for the **gap condition**
  `3 ^ shellBudget M + 1 ≤ 2 ^ shellLevel M`, its other hypothesis.

So `shellLevel` and `shellBudget` are the *only* places the ratio `5/8`
occurs, and the Hoeffding slack is not an independent dial either: it is
forced to be `hoeffdingSlack = 5/8 − 1/2 = 1/8`, the distance from the budget
ratio down to the mean. The decay rate `2 · hoeffdingSlack ^ 2 = 1/32` is
likewise derived, never written as a literal in a statement. Retuning the
argument means editing `shellLevel`, `shellBudget`, `hoeffdingSlack` and the
`decide` that checks `3 ^ 5 ≤ 2 ^ 8` — nothing else.

## Contents

* `Descends` — the "positive-step descent" predicate; definitionally the
  right-hand side of `CC.stopping_time_ne_top_iff`, hence an `abbrev`.
* `pow_three_ratio_le_pow_two`, `pow_three_ratio_lt_pow_two` — the parametric
  arithmetic: from `3 ^ a ≤ 2 ^ b` to `3 ^ (a · k / b) < 2 ^ k`.
* `five_eighths_le_criticalRatio` — the link tying `3 ^ 5 ≤ 2 ^ 8` back to
  `CC.SRSBridge.criticalRatio`, so the `Nat` bounds are not an independent
  treatment of the same threshold.
* `shellLevel`, `shellBudget`, `hoeffdingSlack` — the shell → parameter choice.
* `shellBad_Descends_subset` — the shell inclusion, contrapositive of
  `descent_of_not_mem_badResidues`.
* `shellExceptionalRatio_Descends_le` — the resulting shell fraction bound,
  and `..._le_exp_div` its explicit `exp (−shellLevel M / 32)` form.
* `shellExceptionalRatio_Descends_tendsto_zero` — that fraction tends to `0`.
-/

namespace CC

namespace Density

open CET.QuantitativeDensity
open Filter Topology

/-! ### Positive-step descent -/

/-- **Positive-step descent.** `Descends n` iff some strictly positive number
of Terras iterates lands `n` below itself.

This is definitionally the right-hand side of `CC.stopping_time_ne_top_iff`,
so it is an `abbrev` rather than a `def`: it names an existing statement, it
does not introduce a new one. -/
@[category API, AMS 11 37, ref "Ter76", group "terras_density"]
abbrev Descends (n : ℕ) : Prop := ∃ k : ℕ, 1 ≤ k ∧ T_iter k n < n

@[category API, AMS 11 37, ref "Ter76", group "terras_density"]
theorem Descends_iff_stopping_time_ne_top (n : ℕ) :
    Descends n ↔ CC.stopping_time n ≠ ⊤ :=
  (CC.stopping_time_ne_top_iff n).symm

/-- The descent set as an equation between the two natural formulations. -/
@[category API, AMS 11 37, group "terras_density"]
theorem setOf_Descends_eq :
    {n | Descends n} = {n | CC.stopping_time n ≠ ⊤} := by
  ext n; exact Descends_iff_stopping_time_ne_top n

/-! ### Parametric arithmetic: one ratio fact, both shell inequalities

`CC.SRSBridge.criticalRatio = log 2 / log 3` is the exact threshold separating
contracting from expanding ones-ratios (see `CC.SRSBridge.tropWeight_neg_iff_ratio`).
The two inequalities this file needs are both the statement that a *rational*
ratio `a / b` lies at or below that threshold, transported to `ℕ` as
`3 ^ a ≤ 2 ^ b`. The lemmas below make that transport once and for all, so no
hand-rolled induction on a particular ratio is needed. -/

/-- **Ratio transport.** If `3 ^ a ≤ 2 ^ b` — equivalently `a / b ≤ criticalRatio`
— then `3 ^ (a · k / b) ≤ 2 ^ k` for every `k`, with `Nat` division on the left.

Proof by raising both sides to the `b`-th power, where the floor disappears:
`(3 ^ (a·k/b)) ^ b = 3 ^ ((a·k/b)·b) ≤ 3 ^ (a·k) = (3 ^ a) ^ k ≤ (2 ^ b) ^ k = (2 ^ k) ^ b`. -/
@[category API, AMS 11, group "terras_density"]
theorem pow_three_ratio_le_pow_two {a b : ℕ} (hb : 0 < b) (h : 3 ^ a ≤ 2 ^ b)
    (k : ℕ) : 3 ^ (a * k / b) ≤ 2 ^ k := by
  have hmb : a * k / b * b ≤ a * k := Nat.div_mul_le_self (a * k) b
  have hchain : (3 ^ (a * k / b)) ^ b ≤ (2 ^ k) ^ b := by
    calc (3 ^ (a * k / b)) ^ b
        = 3 ^ (a * k / b * b) := by rw [← pow_mul]
      _ ≤ 3 ^ (a * k) := Nat.pow_le_pow_right (by norm_num) hmb
      _ = (3 ^ a) ^ k := by rw [← pow_mul]
      _ ≤ (2 ^ b) ^ k := Nat.pow_le_pow_left h k
      _ = (2 ^ k) ^ b := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  exact (Nat.pow_le_pow_iff_left hb.ne').mp hchain

/-- **Strict ratio transport.** The same hypothesis gives the *strict*
inequality `3 ^ (a · k / b) < 2 ^ k` as soon as `k ≥ 1`, written Nat-safely as
`3 ^ (a · k / b) + 1 ≤ 2 ^ k`.

Strictness is free: `3 ^ m` is odd and `2 ^ k` is even for `k ≥ 1`, so the two
can never be equal. -/
@[category API, AMS 11, group "terras_density"]
theorem pow_three_ratio_lt_pow_two {a b : ℕ} (hb : 0 < b) (h : 3 ^ a ≤ 2 ^ b)
    {k : ℕ} (hk : 1 ≤ k) : 3 ^ (a * k / b) + 1 ≤ 2 ^ k := by
  have hle := pow_three_ratio_le_pow_two hb h k
  have hodd : 3 ^ (a * k / b) % 2 = 1 := by
    rw [Nat.pow_mod]; norm_num
  have heven : 2 ^ k % 2 = 0 := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ]
    exact Nat.mul_mod_left _ _
  omega

/-! ### Concrete shell → parameter choice -/

/-- Level `k` used on shell `M`: `k = ⌊5M/8⌋`, the largest level for which the
shell condition `3 ^ k ≤ 2 ^ M` still follows from `3 ^ 5 ≤ 2 ^ 8`. -/
@[category API, AMS 11 37, group "terras_density"]
def shellLevel (M : ℕ) : ℕ := 5 * M / 8

/-- Odd-step budget used on shell `M`: `J₀ = ⌊5k/8⌋` with `k = shellLevel M`.
A residue is "good" when at most `J₀` of its first `k` Terras steps triple;
`3 ^ J₀ < 2 ^ k` then forces a descent. Same ratio as `shellLevel`, same
source: `3 ^ 5 ≤ 2 ^ 8`. -/
@[category API, AMS 11 37, group "terras_density"]
def shellBudget (M : ℕ) : ℕ := 5 * shellLevel M / 8

/-- The Hoeffding slack, `hoeffdingSlack = 5/8 − 1/2 = 1/8`. **Not an
independent parameter**: it is the distance from the budget ratio `5/8` down to
the mean ones-ratio `1/2`, so it is determined by `shellBudget`. The shell
decay rate is `2 · hoeffdingSlack ^ 2 = 1/32`. -/
@[category API, AMS 11 60, group "terras_density"]
noncomputable def hoeffdingSlack : ℝ := 1 / 8

@[category API, AMS 11 60, group "terras_density"]
theorem hoeffdingSlack_eq_sub : hoeffdingSlack = 5 / 8 - 1 / 2 := by
  unfold hoeffdingSlack; norm_num

@[category API, AMS 11 60, group "terras_density"]
theorem hoeffdingSlack_nonneg : 0 ≤ hoeffdingSlack := by
  unfold hoeffdingSlack; norm_num

@[category API, AMS 11 37, group "terras_density"]
theorem shellLevel_le (M : ℕ) : shellLevel M ≤ M := by
  unfold shellLevel; omega

@[category API, AMS 11 37, group "terras_density"]
theorem one_le_shellLevel {M : ℕ} (hM : 2 ≤ M) : 1 ≤ shellLevel M := by
  unfold shellLevel; omega

/-! ### The two shell inequalities, both instantiations of the same lemma -/

/-- The numerical fact the whole argument rests on: `3 ^ 5 = 243 ≤ 256 = 2 ^ 8`,
i.e. `5 / 8 ≤ CC.SRSBridge.criticalRatio`. -/
@[category API, AMS 11, group "terras_density"]
theorem pow_three_five_le_pow_two_eight : (3 : ℕ) ^ 5 ≤ 2 ^ 8 := by decide

/-- **The same fact, at the real threshold.** `3 ^ 5 ≤ 2 ^ 8` is exactly the
statement that the ratio `5 / 8` does not exceed the contraction threshold
`CC.SRSBridge.criticalRatio = log 2 / log 3` of `CC/SRSBridge.lean`. This lemma
is what makes the `Nat` inequalities above the arithmetic shadow of the
real-valued threshold, rather than an independent hand-rolled bound. -/
@[category API, AMS 11 26, group "terras_density"]
theorem five_eighths_le_criticalRatio :
    (5 : ℝ) / 8 ≤ CC.SRSBridge.criticalRatio := by
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hlog : Real.log ((3 : ℝ) ^ (5 : ℕ)) ≤ Real.log ((2 : ℝ) ^ (8 : ℕ)) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at hlog
  push_cast at hlog
  rw [CC.SRSBridge.criticalRatio, le_div_iff₀ hlog3]
  linarith

/-- **Shell condition.** `3 ^ shellLevel M ≤ 2 ^ M`: the `3 ^ k ≤ n` hypothesis
of `descent_of_not_mem_badResidues`, on the shell `[2 ^ M, 2 ^ (M+1))`. -/
@[category API, AMS 11 37, group "terras_density"]
theorem pow_three_shellLevel_le_pow_two (M : ℕ) :
    3 ^ shellLevel M ≤ 2 ^ M :=
  pow_three_ratio_le_pow_two (by norm_num) pow_three_five_le_pow_two_eight M

/-- **Gap condition.** `3 ^ shellBudget M + 1 ≤ 2 ^ shellLevel M` for `M ≥ 2`:
the other hypothesis of `descent_of_not_mem_badResidues`. Same lemma as the
shell condition, one level down. -/
@[category API, AMS 11 37, group "terras_density"]
theorem pow_three_shellBudget_lt_pow_two {M : ℕ} (hM : 2 ≤ M) :
    3 ^ shellBudget M + 1 ≤ 2 ^ shellLevel M :=
  pow_three_ratio_lt_pow_two (by norm_num) pow_three_five_le_pow_two_eight
    (one_le_shellLevel hM)

/-! ### The Hoeffding cut

`shellBudget M = ⌊5k/8⌋` sits at least `hoeffdingSlack · k` above the mean
`k/2`, which is exactly what `card_shellBadResidues_le_hoeffding` asks for. -/

/-- **Hoeffding cut.** `(1/2 + hoeffdingSlack) · k ≤ shellBudget M + 1` for
`k = shellLevel M`. The `+1` absorbs the floor in `shellBudget`. -/
@[category API, AMS 11 60, group "terras_density"]
theorem hoeffding_cut (M : ℕ) :
    (1 / 2 + hoeffdingSlack) * (shellLevel M : ℝ) ≤ (shellBudget M : ℝ) + 1 := by
  have hnat : 5 * shellLevel M ≤ 8 * shellBudget M + 7 := by
    unfold shellBudget; omega
  have hreal : (5 : ℝ) * (shellLevel M : ℝ) ≤ 8 * (shellBudget M : ℝ) + 7 := by
    exact_mod_cast hnat
  unfold hoeffdingSlack
  linarith

/-! ### Shell inclusion: non-descending integers have bad residues -/

/-- **Shell inclusion.** If `n` sits on the dyadic shell `[2 ^ M, 2 ^ (M+1))`
with `M ≥ 2` and does not descend within any positive number of Terras steps,
then its residue mod `2 ^ shellLevel M` exceeds the odd-step budget.

Direct contrapositive of `descent_of_not_mem_badResidues`, using the gap and
shell conditions proved above. -/
@[category research solved, AMS 11 37, ref "Ter76", group "terras_density"]
theorem mem_shellBadResidues_of_not_Descends
    {M n : ℕ} (hM : 2 ≤ M)
    (hn : 2 ^ M ≤ n ∧ n < 2 ^ (M + 1))
    (h_no_descent : ¬ Descends n) :
    n ∈ shellBadResidues (shellLevel M) M (shellBudget M) := by
  rw [mem_shellBadResidues]
  refine ⟨hn, ?_⟩
  by_contra h_not_bad
  exact h_no_descent ⟨shellLevel M, one_le_shellLevel hM,
    descent_of_not_mem_badResidues h_not_bad
      (pow_three_shellBudget_lt_pow_two hM)
      (le_trans (pow_three_shellLevel_le_pow_two M) hn.1)⟩

/-- Set-level restatement: the shell-exceptional set for `Descends` on shell
`M ≥ 2` is contained in `shellBadResidues`. This is the input the final
natural-density-one argument consumes. -/
@[category research solved, AMS 11 37, ref "Ter76", group "terras_density"]
theorem shellBad_Descends_subset {M : ℕ} (hM : 2 ≤ M) :
    shellBad {n | Descends n} M
      ⊆ shellBadResidues (shellLevel M) M (shellBudget M) := by
  intro n hn
  simp only [shellBad, dyadicShell, Finset.mem_filter, Finset.mem_Ico,
    Set.mem_ofPred_eq] at hn
  obtain ⟨⟨h1, h2⟩, hnot⟩ := hn
  exact mem_shellBadResidues_of_not_Descends hM ⟨h1, h2⟩ hnot

/-! ### Shell-ratio decay -/

/-- **Shell-ratio decay.** On shell `M ≥ 2`, the exceptional fraction of the
descent set is at most `exp (−2 · hoeffdingSlack ² · shellLevel M)`.

The shell inclusion `shellBad_Descends_subset` transports the cardinality into
`card_shellBadResidues_le_hoeffding`, whose hypothesis is `hoeffding_cut`. -/
@[category research solved, AMS 11 37 60, ref "Ter76", group "terras_density"]
theorem shellExceptionalRatio_Descends_le {M : ℕ} (hM : 2 ≤ M) :
    shellExceptionalRatio {n | Descends n} M ≤
      Real.exp (-2 * hoeffdingSlack ^ 2 * (shellLevel M : ℝ)) := by
  have hoeff := card_shellBadResidues_le_hoeffding
    (k := shellLevel M) (M := M) (J₀ := shellBudget M) (t := hoeffdingSlack)
    (shellLevel_le M) hoeffdingSlack_nonneg (hoeffding_cut M)
  have hcard_le_real :
      ((shellBad {n | Descends n} M).card : ℝ)
        ≤ ((shellBadResidues (shellLevel M) M (shellBudget M)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (shellBad_Descends_subset hM)
  have h2pow_pos : (0 : ℝ) < (2 : ℝ) ^ M := by positivity
  unfold shellExceptionalRatio
  rw [div_le_iff₀ h2pow_pos, mul_comm]
  exact hcard_le_real.trans hoeff

/-- The decay rate spelled out: `2 · hoeffdingSlack ² = 1/32`, so the shell
fraction is at most `exp (−shellLevel M / 32)`, and since
`shellLevel M = ⌊5M/8⌋`, at most about `exp (−5M/256)`. -/
@[category research solved, AMS 11 37 60, ref "Ter76", group "terras_density"]
theorem shellExceptionalRatio_Descends_le_exp_div {M : ℕ} (hM : 2 ≤ M) :
    shellExceptionalRatio {n | Descends n} M ≤
      Real.exp (-(shellLevel M : ℝ) / 32) := by
  have h := shellExceptionalRatio_Descends_le hM
  have hrate : -2 * hoeffdingSlack ^ 2 * (shellLevel M : ℝ)
      = -(shellLevel M : ℝ) / 32 := by
    unfold hoeffdingSlack; ring
  rwa [hrate] at h

/-! ### Tendsto: shell ratio → 0 -/

private lemma shellLevel_cast_tendsto_atTop :
    Tendsto (fun M : ℕ => (shellLevel M : ℝ)) atTop atTop := by
  -- `8 · ⌊5M/8⌋ ≥ 5M − 7 ≥ 4M` once `M ≥ 7`, i.e. `shellLevel M ≥ M / 2`.
  have hlb : ∀ᶠ M : ℕ in atTop, (M : ℝ) / 2 ≤ (shellLevel M : ℝ) := by
    filter_upwards [eventually_ge_atTop 7] with M hM
    have hnat : 2 * shellLevel M ≥ M := by unfold shellLevel; omega
    have hreal : (2 : ℝ) * (shellLevel M : ℝ) ≥ (M : ℝ) := by exact_mod_cast hnat
    linarith
  have hlim : Tendsto (fun M : ℕ => (M : ℝ) / 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 2)
  exact tendsto_atTop_mono' _ hlb hlim

private lemma exp_neg_shellLevel_tendsto_zero :
    Tendsto (fun M => Real.exp (-(shellLevel M : ℝ) / 32)) atTop (𝓝 0) := by
  refine Real.tendsto_exp_atBot.comp ?_
  have h1 : Tendsto (fun M : ℕ => (shellLevel M : ℝ) / 32) atTop atTop :=
    shellLevel_cast_tendsto_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 32)
  have h2 : Tendsto (fun M : ℕ => -((shellLevel M : ℝ) / 32)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp h1
  simpa [neg_div] using h2

/-- **Shell ratio → 0.** The shell exceptional fraction of the descent set
tends to `0` as `M → ∞`, by squeeze between `0` and `exp (−shellLevel M / 32)`. -/
@[category research solved, AMS 11 37, ref "Ter76", group "terras_density"]
theorem shellExceptionalRatio_Descends_tendsto_zero :
    Tendsto (fun M => shellExceptionalRatio {n | Descends n} M)
      atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun _ => (0 : ℝ))
    (h := fun M => Real.exp (-(shellLevel M : ℝ) / 32))
    tendsto_const_nhds exp_neg_shellLevel_tendsto_zero ?_ ?_
  · exact Eventually.of_forall (fun M => shellExceptionalRatio_nonneg _ M)
  · filter_upwards [eventually_ge_atTop 2] with M hM
    exact shellExceptionalRatio_Descends_le_exp_div hM

end Density

end CC
