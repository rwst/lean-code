/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TH.ExplicitRate
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Sort

/-!
# A14(ii): `s`-point kernels, the counting transfer, and the fixed-scale ceiling

Angle A14 item (ii) of `plans/plan-A1+.html` §5 (work package W10′), the escalation of the
two-point kernel of `TH/KernelReduction.lean`:

> an `s`-tuple of aligned repetitions yields an `s`-term `S`-unit relation `∑ ±(3/2)^{cᵢ}` small,
> refutable by Evertse–Schlickewei at `n = s+1`, with subspace-counting turning configuration
> counts into complexity: target `p_T(k) ≫ k^{1+δ}` or `k²/log k`.

Executed here, with the feasibility calc the plan gated on.  **Verdict: the `s`-point escalation
works and buys a strictly weaker hypothesis, but it cannot reach the advertised targets — for a
reason that is structural and has nothing to do with the strength of the Diophantine input.**

## Part 1 — the `s`-point route, executed

`tupleViolators s θ` is the set of aligned `(s+1)`-configurations `2 ≤ A₀ < … < A_s` all of whose
pairs violate (K) at scale `θ`; `KernelTuple s` is its finiteness at every rational scale.  Then

* `kernelTuple_of_kernel` — (K) ⟹ (K_s): the tuple hypothesis is *implied by* the pair hypothesis,
  hence weaker;
* `kernelTuple_mono` — and it keeps weakening as `s` grows;
* `superlinear_of_kernelTuple` — **(K_s) ⟹ M4**, by an `s`-fold pigeonhole in a window of length
  `s·C·k`: the escalation delivers the *same* conclusion from a weaker hypothesis.

`tuple_sum_distToNearestInt_le` extracts the promised relation: `∑_{i>0}(3/2)^{Aᵢ} − s·(3/2)^{A₀}`
is within `∑_{i>0} θ^{Aᵢ} ≤ s·θ^{A₀}` of an integer.  Note how it is proved — by *summing the pair
bounds*.  The `(s+1)`-term relation is a **consequence** of the `s` two-point relations, with the
error multiplied by `s`; whatever Evertse–Schlickewei is fed at `n = s+1` is strictly less than what
the pair statement already provides at `n = 2`.  That is the first half of the verdict.

## Part 2 — the fixed-scale ceiling (the no-go)

The second half is quantitative and decides the targets.  Every route from configurations to
complexity — finiteness, tuples, or *counting* — runs the same window pigeonhole, and the window is
capped by the Lemma-R budget.  Two theorems bracket it:

* `window_le_complexity_add` — **the counting transfer**, executed in its sharp elementary form:
  if every violator at scale `θ` with second coordinate `≤ N+1` lies in a finite set `V`, then
  `N ≤ p_T(k) + #V` for every `k` with `N + 1 ≤ L·k`, where `L` is any Bernoulli exponent for `θ`
  (`(2/3) ≤ θ^L`).  With `V = ∅` (`complexity_ge_of_no_violators`) this is `p_T(k) ≥ N` — the
  strongest conclusion any hypothesis about `kernelViolators θ` can produce from a window of
  length `N`.
* `pow_lt_pow_of_budget` — **the window cannot be longer**: past position `(L+1)·k` the Lemma-R
  certificate `ρ^k ≤ θ^c` is *false*, for `ρ = 2/3` and in fact for any contraction base `ρ < 1`
  (`exists_contraction_budget` supplies `L`).

Together: at a fixed scale `θ` the usable window has length `Θ_θ(k)`, so the conclusion is
`p_T(k) ≥ L(θ)·k` and no better — **linear in `k`, whatever the Diophantine input says**.  The cap
is on the bridge, not on the input: the only thing a repetition supplies is the contraction bound,
and a contraction bound of *any* base places the repetition at position `O_θ(k)` or nowhere.
Counting refines nothing either — in `window_le_complexity_add` the count enters additively, so a
bound `#V = o(N)` and the ideal `#V = 0` give the same linear conclusion.  Both `k^{1+δ}` and
`k²/log k` are therefore out of reach at any fixed scale.

## Part 3 — what would lift the ceiling

Superlinearity in `TH.superlinear_of_kernel` comes only from letting `θ = θ(C) → 1`, and a
conclusion at a *moving* scale needs the growth of the violator bound in `θ` — that is, the
`KernelCeiling` of `TH/ExplicitRate.lean`.  Made precise here:

* `complexity_gt_of_polyCeiling` / `complexity_polynomial_of_polyCeiling` — a **polynomial** ceiling
  `B(θ(C)) < (C+2)^d` gives exactly A14(ii)'s first target,
  `p_T(k) > (k^{1/d} − 2)·k` along `k = m^d`.

So A14(ii) has **no blocker of its own**: its targets are equivalent to growth rates of the W10
ceiling, and W10 is where the obstruction lives ([BE08] gives covers, not ceilings).  The `s`-point
apparatus is not what is missing.

Everything in this file is `std3` — no cited axioms.  (`TH.ExplicitRate` is imported for `bScale`
and `KernelCeiling`; the [BE08] declaration it carries is not used here.)

## Contents

* `tupleViolators`, `TupleRepulsion`, `KernelTuple` — the `s`-point kernel.
* `pairRepulsion_iff_tupleRepulsion_one` — the ladder's base rung is (K) itself.
* `tupleRepulsion_of_pairRepulsion`, `kernelTuple_of_kernel`, `kernelTuple_mono` — the ladder is
  monotone: higher `s` is a weaker demand.
* `superlinear_of_kernelTuple` — the `s`-fold pigeonhole: (K_s) ⟹ M4.
* `tuple_sum_distToNearestInt_le` — the `(s+1)`-term `S`-unit relation, derived from the pairs.
* `firstSame` and its API — the least window position with a given factor.
* `window_le_complexity_add`, `complexity_ge_of_no_violators` — the counting transfer and its
  best case.
* `pow_lt_pow_of_budget`, `exists_contraction_budget` — the window budget, for any contraction base.
* `complexity_gt_of_polyCeiling`, `complexity_polynomial_of_polyCeiling` — the polynomial target,
  from a polynomial ceiling.

## References

* [A1plus] `plans/plan-A1+.html` (this repository, 2026-08): §5 A14(ii), §7.3 (W10′).
* [M4A3] `plan-M4A3.html` (this repository, 2026-07): §4 (the kernel and the reduction).
* [BE08] Bugeaud, Evertse. *On two notions of complexity of algebraic numbers.*
  Acta Arith. **133** (2008) — Cor. 5.2 and Rem. 7.4 (the per-line problem), the lane audited in
  `TH/ExplicitRate.lean`.
-/

namespace TH

open Finset

/-! ## Part 1 — `s`-point kernels -/

/-- An **aligned `(s+1)`-configuration** at scale `θ`: a strictly increasing tuple
`2 ≤ A 0 < A 1 < … < A s` every pair of which is a (K)-violator at scale `θ`.  This is the
configuration an `s`-fold pigeonhole produces, and the object A14(ii) proposes to refute by
Evertse–Schlickewei at `n = s + 1`. -/
@[category API, AMS 11 68, ref "A1plus", group "weyl_a14_spoint"]
def tupleViolators (s : ℕ) (θ : ℚ) : Set (Fin (s + 1) → ℕ) :=
  {A | 2 ≤ A 0 ∧ StrictMono A ∧ ∀ i j : Fin (s + 1), i < j → (A i, A j) ∈ kernelViolators θ}

/-- **`s`-point repulsion at scale `θ`**: only finitely many aligned `(s+1)`-configurations. -/
@[category API, AMS 11 68, ref "A1plus", group "weyl_a14_spoint"]
def TupleRepulsion (s : ℕ) (θ : ℚ) : Prop := (tupleViolators s θ).Finite

/-- **The `s`-point kernel (K_s)**: `s`-point repulsion at every rational scale `θ ∈ (0,1)`.
The ladder starts at `TH.Kernel` itself — a `2`-tuple is a pair
(`pairRepulsion_iff_tupleRepulsion_one`) — and weakens from there (`kernelTuple_mono`). -/
@[category API, AMS 11 68, ref "A1plus", group "weyl_a14_spoint"]
def KernelTuple (s : ℕ) : Prop := ∀ θ : ℚ, 0 < θ → θ < 1 → TupleRepulsion s θ

/-- A tuple's largest entry is the second coordinate of one of its pairs — the handle by which
pair information bounds a configuration.  Needs `1 ≤ s` (a `1`-tuple has no pair). -/
@[category API, AMS 11 68, ref "A1plus", group "weyl_a14_spoint"]
lemma mem_kernelViolators_zero_last {s : ℕ} (hs : 1 ≤ s) {θ : ℚ} {A : Fin (s + 1) → ℕ}
    (hA : A ∈ tupleViolators s θ) : (A 0, A (Fin.last s)) ∈ kernelViolators θ := by
  refine hA.2.2 0 (Fin.last s) (Fin.lt_def.mpr ?_)
  simp only [Fin.val_zero, Fin.val_last]
  omega

/-- Pair repulsion implies `s`-point repulsion (`1 ≤ s`): a bound on the second coordinates of
the violating pairs bounds every entry of a configuration. -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_spoint"]
theorem tupleRepulsion_of_pairRepulsion {s : ℕ} (hs : 1 ≤ s) {θ : ℚ}
    (h : PairRepulsion θ) : TupleRepulsion s θ := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ p ∈ kernelViolators θ, p.2 ≤ M := by
    obtain ⟨M, hM⟩ := (h.image Prod.snd).bddAbove
    exact ⟨M, fun p hp => hM (Set.mem_image_of_mem _ hp)⟩
  refine Set.Finite.subset
    (Set.Finite.pi' (t := fun _ : Fin (s + 1) => Set.Icc 0 M) fun _ => Set.finite_Icc _ _) ?_
  intro A hA i
  have hlast : A (Fin.last s) ≤ M := hM _ (mem_kernelViolators_zero_last hs hA)
  exact Set.mem_Icc.mpr ⟨Nat.zero_le _, le_trans (hA.2.1.monotone (Fin.le_last i)) hlast⟩

/-- **The base rung is (K) itself**: `tupleViolators 1 θ` is `kernelViolators θ` transcribed as
`2`-tuples, so `(K_1) ⟺ (K)`.  The escalation therefore starts *at* the two-point kernel — there
is no gain hidden in the passage from pairs to `2`-tuples. -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_spoint"]
theorem pairRepulsion_iff_tupleRepulsion_one {θ : ℚ} :
    PairRepulsion θ ↔ TupleRepulsion 1 θ := by
  refine ⟨tupleRepulsion_of_pairRepulsion le_rfl, fun h => ?_⟩
  refine Set.Finite.subset (h.image fun A : Fin 2 → ℕ => (A 0, A 1)) ?_
  rintro ⟨a, c⟩ hp
  have hmono : StrictMono (![a, c] : Fin 2 → ℕ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [hp.2.1]
  exact ⟨![a, c], ⟨hp.1, hmono, by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩, rfl⟩

/-- **(K) ⟹ (K_s)**: the `s`-point hypothesis is implied by the two-point one, hence is no
stronger.  This is the whole gain of the escalation — a weaker input for the same output
(`superlinear_of_kernelTuple`). -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_spoint"]
theorem kernelTuple_of_kernel {s : ℕ} (hs : 1 ≤ s) (hK : Kernel) : KernelTuple s :=
  fun θ h0 h1 => tupleRepulsion_of_pairRepulsion hs (hK θ h0 h1)

/-- **The ladder is monotone**: `(K_s) ⟹ (K_{s'})` for `1 ≤ s ≤ s'`.  A long configuration
contains a short one *ending at the same place* (shift the index window to the right), so a bound
from arity `s` already bounds the last entry at arity `s'`. -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_spoint"]
theorem kernelTuple_mono {s s' : ℕ} (hss : s ≤ s')
    (hKs : KernelTuple s) : KernelTuple s' := by
  intro θ hθ0 hθ1
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ A ∈ tupleViolators s θ, A (Fin.last s) ≤ M := by
    obtain ⟨M, hM⟩ := ((hKs θ hθ0 hθ1).image fun A => A (Fin.last s)).bddAbove
    exact ⟨M, fun A hA => hM (Set.mem_image_of_mem _ hA)⟩
  refine Set.Finite.subset
    (Set.Finite.pi' (t := fun _ : Fin (s' + 1) => Set.Icc 0 M) fun _ => Set.finite_Icc _ _) ?_
  intro A hA i
  -- the right-aligned sub-configuration `A' i = A (i + (s' − s))`
  set d : ℕ := s' - s with hd
  have hshift : ∀ i : Fin (s + 1), (i : ℕ) + d < s' + 1 := by
    intro i
    have := i.isLt
    omega
  set A' : Fin (s + 1) → ℕ := fun i => A ⟨(i : ℕ) + d, hshift i⟩ with hA'
  have hmono' : StrictMono A' := by
    intro i j hij
    refine hA.2.1 ?_
    exact Fin.lt_def.mpr (by simpa using Fin.lt_def.mp hij)
  have hmem' : A' ∈ tupleViolators s θ := by
    refine ⟨?_, hmono', fun i j hij => hA.2.2 _ _ ?_⟩
    · exact le_trans hA.1 (hA.2.1.monotone (Fin.zero_le _))
    · exact Fin.lt_def.mpr (by simpa using Fin.lt_def.mp hij)
  have hlast' : A' (Fin.last s) = A (Fin.last s') := by
    simp only [hA', Fin.last]
    congr 1
    exact Fin.ext (by simp [hd]; omega)
  have hlast : A (Fin.last s') ≤ M := hlast' ▸ hM A' hmem'
  exact Set.mem_Icc.mpr ⟨Nat.zero_le _, le_trans (hA.2.1.monotone (Fin.le_last i)) hlast⟩

/-- **The `s`-point route, executed**: `(K_s) ⟹ M4`.  An `s`-fold pigeonhole in the window
`[2, s·C·k + 2]` produces an aligned `(s+1)`-configuration at the Bernoulli scale `θ(s·C)`, and
`(K_s)` bounds its last entry; the growth ceiling then bounds `k`.

Compare `TH.superlinear_of_kernel`: the *conclusion* is identical.  Escalating from pairs to
`(s+1)`-tuples weakens the hypothesis (`kernelTuple_of_kernel`) at the price of a window `s` times
longer — it does not sharpen the complexity bound, and by `window_le_complexity_add` below it
cannot. -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_spoint"]
theorem superlinear_of_kernelTuple {s : ℕ} (hs : 1 ≤ s) (hKs : KernelTuple s) : Superlinear := by
  classical
  intro C
  obtain ⟨θ, hθ0, hθ1, hθpow⟩ :=
    exists_pow_ge (2 / 3) (by norm_num) (by norm_num) (s * C + 2) (by omega)
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ A ∈ tupleViolators s θ, A (Fin.last s) ≤ M := by
    obtain ⟨M, hM⟩ := ((hKs θ hθ0 hθ1).image fun A => A (Fin.last s)).bddAbove
    exact ⟨M, fun A hA => hM (Set.mem_image_of_mem _ hA)⟩
  refine ⟨M + 1, fun k hk => ?_⟩
  by_contra hle
  have hple : complexity k ≤ C * k := Nat.not_lt.mp hle
  have hncard : complexity k = (factorSet_finite k).toFinset.card :=
    Set.ncard_eq_toFinset_card _ (factorSet_finite k)
  have hmaps : ∀ a ∈ Finset.Icc 2 (s * C * k + 2),
      factor a k ∈ (factorSet_finite k).toFinset := fun a _ => by
    rw [Set.Finite.mem_toFinset]
    exact ⟨a, rfl⟩
  have hcard : (factorSet_finite k).toFinset.card * s
      < (Finset.Icc 2 (s * C * k + 2)).card := by
    rw [Nat.card_Icc, ← hncard]
    have h1 : complexity k * s ≤ C * k * s := Nat.mul_le_mul_right s hple
    have h2 : C * k * s = s * C * k := by ring
    omega
  -- `s`-fold pigeonhole: one factor is taken at more than `s` window positions
  obtain ⟨y, -, hy⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hcard
  obtain ⟨G, hGsub, hGcard⟩ :=
    Finset.exists_subset_card_eq (s := {x ∈ Finset.Icc 2 (s * C * k + 2) | factor x k = y})
      (n := s + 1) hy
  set A : Fin (s + 1) → ℕ := fun i => G.orderEmbOfFin hGcard i with hAdef
  have hAmemG : ∀ i, A i ∈ G := fun i => G.orderEmbOfFin_mem hGcard i
  have hAwin : ∀ i, 2 ≤ A i ∧ A i ≤ s * C * k + 2 ∧ factor (A i) k = y := by
    intro i
    have := Finset.mem_filter.mp (hGsub (hAmemG i))
    exact ⟨(Finset.mem_Icc.mp this.1).1, (Finset.mem_Icc.mp this.1).2, this.2⟩
  have hmono : StrictMono A := (G.orderEmbOfFin hGcard).strictMono
  have hk1 : 1 ≤ k := by omega
  have hpair : ∀ i j : Fin (s + 1), i < j → (A i, A j) ∈ kernelViolators θ := by
    intro i j hij
    have hrep : IsRepetition (A i) (A j) k :=
      factor_eq_iff.mp ((hAwin i).2.2.trans (hAwin j).2.2.symm)
    have hck : A j ≤ (s * C + 2) * k := by
      have h2k : 2 ≤ 2 * k := by omega
      have := (hAwin j).2.1
      have hexp : (s * C + 2) * k = s * C * k + 2 * k := by ring
      omega
    exact mem_kernelViolators_of_repetition hθ0 hθ1 hθpow (hAwin i).1 (hmono hij) hck hrep
  have hAmem : A ∈ tupleViolators s θ := ⟨(hAwin 0).1, hmono, hpair⟩
  have hlast : A (Fin.last s) ≤ M := hM A hAmem
  have h0last : (0 : Fin (s + 1)) < Fin.last s := by
    refine Fin.lt_def.mpr ?_
    simp only [Fin.val_zero, Fin.val_last]
    omega
  have hrep : IsRepetition (A 0) (A (Fin.last s)) k :=
    factor_eq_iff.mp ((hAwin 0).2.2.trans (hAwin (Fin.last s)).2.2.symm)
  have hbound := repetition_linear_bound (hAwin 0).1 (hmono h0last) hrep
  omega

/-- Subadditivity of `Rat.distToNearestInt` over a finite sum. -/
private lemma dist_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℚ) :
    (∑ i ∈ s, f i).distToNearestInt ≤ ∑ i ∈ s, (f i).distToNearestInt := by
  induction s using Finset.cons_induction with
  | empty => simp [Rat.distToNearestInt]
  | cons a s ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons]
      exact le_trans (Rat.distToNearestInt_add_le _ _) (by linarith)

/-- **The `(s+1)`-term `S`-unit relation of A14(ii)**: an aligned configuration puts
`∑_{i>0}(3/2)^{Aᵢ} − s·(3/2)^{A₀}` within `∑_{i>0} θ^{Aᵢ}` of an integer — the input the plan
proposes to feed to Evertse–Schlickewei at `n = s + 1`.

**And here is what the proof shows.**  The relation is obtained by *adding up* the `s` two-point
relations, so it carries no information the pairs did not already carry, and its error is the
*sum* of theirs.  At `n = s + 1` the Diophantine theorem is therefore fed a strictly weaker
statement than the pair case feeds it at `n = 2`; the escalation is one of arity, not of content. -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_spoint"]
theorem tuple_sum_distToNearestInt_le {s : ℕ} {θ : ℚ} {A : Fin (s + 1) → ℕ}
    (hA : A ∈ tupleViolators s θ) :
    (∑ i ∈ Finset.univ.erase (0 : Fin (s + 1)), (3 / 2 : ℚ) ^ A i
        - (s : ℚ) * (3 / 2 : ℚ) ^ A 0).distToNearestInt
      ≤ ∑ i ∈ Finset.univ.erase (0 : Fin (s + 1)), θ ^ A i := by
  classical
  have hcard : (Finset.univ.erase (0 : Fin (s + 1))).card = s := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  have hsplit : ∑ i ∈ Finset.univ.erase (0 : Fin (s + 1)), (3 / 2 : ℚ) ^ A i
      - (s : ℚ) * (3 / 2 : ℚ) ^ A 0
      = ∑ i ∈ Finset.univ.erase (0 : Fin (s + 1)),
          ((3 / 2 : ℚ) ^ A i - (3 / 2 : ℚ) ^ A 0) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, hcard, nsmul_eq_mul]
  rw [hsplit]
  refine le_trans (dist_sum_le _ _) (Finset.sum_le_sum fun i hi => ?_)
  have hne : i ≠ 0 := (Finset.mem_erase.mp hi).1
  have h0i : (0 : Fin (s + 1)) < i := by
    rcases Nat.eq_zero_or_pos (i : ℕ) with h | h
    · exact absurd (Fin.ext (by simpa using h)) hne
    · exact Fin.lt_def.mpr (by simpa using h)
  exact (hA.2.2 0 i h0i).2.2

/-! ## Part 2 — the counting transfer and the fixed-scale ceiling -/

/-- The Lemma-R contraction with the **budget exponent** exposed: any `L` with `θ^L ≥ 2/3`
certifies every length-`k` repetition sitting at positions `≤ L·k`.  (`TH.exists_pow_ge` supplies
`θ` from `L`; `exists_window_budget` below supplies the largest `L` from `θ`.) -/
@[category API, AMS 11 68, ref "A1plus" "M4A3", group "weyl_a14_spoint"]
theorem mem_kernelViolators_of_repetition_budget {θ : ℚ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {L k a c : ℕ} (hθpow : (2 / 3 : ℚ) ≤ θ ^ L) (ha : 2 ≤ a) (hac : a < c)
    (hcL : c ≤ L * k) (hrep : IsRepetition a c k) :
    (a, c) ∈ kernelViolators θ := by
  refine ⟨ha, hac, ?_⟩
  calc ((3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a).distToNearestInt
      ≤ |eps c - eps a| := distToNearestInt_orbit_le a c
    _ ≤ (2 / 3 : ℚ) ^ k := abs_eps_sub_le_of_repetition hrep
    _ ≤ (θ ^ L) ^ k := pow_le_pow_left₀ (by norm_num) hθpow k
    _ = θ ^ (L * k) := (pow_mul θ L k).symm
    _ ≤ θ ^ c := pow_le_pow_of_le_one hθ0.le hθ1.le hcL

/-- The least position `≥ 2` carrying the same length-`k` factor as `a` — the canonical
representative of `a`'s repetition class.  Total by `Nat.sInf`; the class is nonempty at `a`. -/
@[category API, AMS 11 68, ref "A1plus", group "weyl_a14_spoint"]
noncomputable def firstSame (k a : ℕ) : ℕ := sInf {x | 2 ≤ x ∧ factor x k = factor a k}

@[category API, AMS 11 68, ref "A1plus", group "weyl_a14_spoint"]
lemma firstSame_spec {k a : ℕ} (ha : 2 ≤ a) :
    2 ≤ firstSame k a ∧ factor (firstSame k a) k = factor a k := by
  have hne : {x | 2 ≤ x ∧ factor x k = factor a k}.Nonempty := ⟨a, ha, rfl⟩
  exact Nat.sInf_mem hne

@[category API, AMS 11 68, ref "A1plus", group "weyl_a14_spoint"]
lemma firstSame_le {k a : ℕ} (ha : 2 ≤ a) : firstSame k a ≤ a :=
  Nat.sInf_le (show a ∈ {x | 2 ≤ x ∧ factor x k = factor a k} from ⟨ha, rfl⟩)

/-- Positions in the same repetition class have the same representative. -/
@[category API, AMS 11 68, ref "A1plus", group "weyl_a14_spoint"]
lemma firstSame_congr {k a b : ℕ} (h : factor a k = factor b k) :
    firstSame k a = firstSame k b := by
  unfold firstSame
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, h]

/-- **The counting transfer** — A14(ii)'s "configuration counts into complexity", in its sharp
elementary form.  Let `L` be a budget exponent for `θ` and let `V` collect the (K)-violators with
second coordinate `≤ N+1`.  Then for every `k` with `N + 1 ≤ L·k`

`N ≤ p_T(k) + #V`.

Proof: split the window `[2, N+1]` (of size `N`) into class representatives and repeats.  The
representatives carry distinct factors, so there are at most `p_T(k)` of them; each repeat `a`
contributes the distinct violator `(firstSame k a, a)`, so there are at most `#V` of them.

This is the *strongest* statement the schema can extract from a window of length `N`, and it is
what any Diophantine input — finiteness, an `s`-point statement, or a genuine count — feeds.  Note
that the count enters *additively*: a bound `#V = o(N)` gives `p_T(k) ≥ N − o(N)`, the same linear
conclusion as `#V = 0`.  Counting buys nothing beyond the window length. -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_spoint"]
theorem window_le_complexity_add {θ : ℚ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {L N k : ℕ}
    (hθpow : (2 / 3 : ℚ) ≤ θ ^ L) (hNk : N + 1 ≤ L * k)
    (V : Finset (ℕ × ℕ)) (hV : ∀ p ∈ kernelViolators θ, p.2 ≤ N + 1 → p ∈ V) :
    N ≤ complexity k + V.card := by
  classical
  set W : Finset ℕ := Finset.Icc 2 (N + 1) with hW
  have hWcard : W.card = N := by rw [hW, Nat.card_Icc]; omega
  have hsplit := Finset.card_filter_add_card_filter_not (s := W)
    (fun a => firstSame k a = a)
  -- (a) class representatives carry distinct factors
  have hrep_le : (W.filter (fun a => firstSame k a = a)).card ≤ complexity k := by
    have hinj : Set.InjOn (fun a => factor a k)
        ↑(W.filter (fun a => firstSame k a = a)) := by
      intro x hx y hy hxy
      have hx' := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
      have hy' := Finset.mem_filter.mp (Finset.mem_coe.mp hy)
      have := firstSame_congr (k := k) hxy
      rw [hx'.2, hy'.2] at this
      exact this
    have hsub : ((W.filter (fun a => firstSame k a = a)).image fun a => factor a k)
        ⊆ (factorSet_finite k).toFinset := by
      intro w hw
      rw [Set.Finite.mem_toFinset]
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hw
      exact ⟨x, rfl⟩
    have hncard : complexity k = (factorSet_finite k).toFinset.card :=
      Set.ncard_eq_toFinset_card _ (factorSet_finite k)
    calc (W.filter (fun a => firstSame k a = a)).card
        = ((W.filter (fun a => firstSame k a = a)).image fun a => factor a k).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (factorSet_finite k).toFinset.card := Finset.card_le_card hsub
      _ = complexity k := hncard.symm
  -- (b) each repeat contributes a distinct violator
  have hrepeat_le : (W.filter (fun a => ¬ (firstSame k a = a))).card ≤ V.card := by
    refine Finset.card_le_card_of_injOn (fun a => (firstSame k a, a)) ?_
      (fun a _ b _ hab => congrArg Prod.snd hab)
    intro a ha
    obtain ⟨haW, hne⟩ := Finset.mem_filter.mp ha
    rw [hW, Finset.mem_Icc] at haW
    have hspec := firstSame_spec (k := k) haW.1
    have hlt : firstSame k a < a := lt_of_le_of_ne (firstSame_le haW.1) hne
    have hmem : (firstSame k a, a) ∈ kernelViolators θ :=
      mem_kernelViolators_of_repetition_budget hθ0 hθ1 hθpow hspec.1 hlt
        (by omega) (factor_eq_iff.mp hspec.2)
    exact hV _ hmem haW.2
  omega

/-- **The best case of the schema**: if the Diophantine input says there is *no* violator at
scale `θ` in the window at all, the window positions carry pairwise distinct factors and
`p_T(k) ≥ N`.  No hypothesis about `kernelViolators θ` can do better than this. -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_spoint"]
theorem complexity_ge_of_no_violators {θ : ℚ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {L N k : ℕ}
    (hθpow : (2 / 3 : ℚ) ≤ θ ^ L) (hNk : N + 1 ≤ L * k)
    (hno : ∀ p ∈ kernelViolators θ, N + 1 < p.2) :
    N ≤ complexity k := by
  have := window_le_complexity_add hθ0 hθ1 hθpow hNk ∅
    (fun p hp hle => absurd hle (Nat.not_le.mpr (hno p hp)))
  simpa using this

/-- **The window budget**: past position `(L+1)·k` a contraction certificate of base `ρ` cannot be
met at scale `θ`, once `θ^{L+1} < ρ`.  Stated for an arbitrary base `ρ`, because the cap does not
depend on Lemma R's constant: a repetition of length `k` contracts by `ρ^k` for some fixed `ρ < 1`,
and `ρ^k ≤ θ^c` forces `c = O_{θ,ρ}(k)` whatever `ρ` is. -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_spoint"]
theorem pow_lt_pow_of_budget {θ ρ : ℚ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {L k c : ℕ}
    (hL : θ ^ (L + 1) < ρ) (hk : 1 ≤ k) (hc : (L + 1) * k ≤ c) : θ ^ c < ρ ^ k := by
  calc θ ^ c ≤ θ ^ ((L + 1) * k) := pow_le_pow_of_le_one hθ0.le hθ1 hc
    _ = (θ ^ (L + 1)) ^ k := pow_mul θ (L + 1) k
    _ < ρ ^ k := pow_lt_pow_left₀ hL (by positivity) (by omega)

/-- Such an `L` always exists, for any base `ρ > 0` and any scale `θ < 1`. -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_spoint"]
theorem exists_contraction_budget {θ ρ : ℚ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hρ : 0 < ρ) :
    ∃ L : ℕ, θ ^ (L + 1) < ρ := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hρ hθ1
  refine ⟨n, ?_⟩
  calc θ ^ (n + 1) ≤ θ ^ n := pow_le_pow_of_le_one hθ0.le hθ1.le (by omega)
    _ < ρ := hn

/-- **The fixed-scale ceiling, packaged — the A14(ii) no-go.**  Every scale `θ ∈ (0,1)` has a
budget exponent `L(θ)` which is *sharp on both sides*:

* `(2/3) ≤ θ^L`, so `window_le_complexity_add` applies to windows of length `L·k` and the schema
  concludes at most `p_T(k) ≥ L·k`;
* for `c ≥ (L+1)·k` the Lemma-R certificate `(2/3)^k ≤ θ^c` is **false**, so the window cannot be
  extended — no hypothesis about `kernelViolators θ` reaches position `(L+1)·k`.

Hence at a fixed scale the schema's output is `Θ_θ(k)`: **linear**, with a constant `L(θ)` that is
a property of `θ` alone.  `s`-point configurations (Part 1) and violator counts
(`window_le_complexity_add`) live inside the same window and are subject to the same cap, so
neither `k^{1+δ}` nor `k²/log k` is reachable this way.  Superlinearity in
`TH.superlinear_of_kernel` comes *only* from `θ(C) → 1`, i.e. from the growth of the violator bound
in `θ` — Part 3. -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_spoint"]
theorem exists_window_budget {θ : ℚ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∃ L : ℕ, (2 / 3 : ℚ) ≤ θ ^ L ∧
      ∀ k c : ℕ, 1 ≤ k → (L + 1) * k ≤ c → θ ^ c < (2 / 3 : ℚ) ^ k := by
  have hex : ∃ n : ℕ, θ ^ n < 2 / 3 := exists_pow_lt_of_lt_one (by norm_num) hθ1
  obtain ⟨n₀, hspec, hmin⟩ :
      ∃ n : ℕ, θ ^ n < 2 / 3 ∧ ∀ m : ℕ, m < n → ¬ (θ ^ m < 2 / 3) :=
    ⟨sInf {n : ℕ | θ ^ n < 2 / 3}, Nat.sInf_mem hex, fun _ hm => Nat.notMem_of_lt_sInf hm⟩
  have hpos : 0 < n₀ := by
    rcases Nat.eq_zero_or_pos n₀ with h | h
    · rw [h] at hspec; norm_num at hspec
    · exact h
  obtain ⟨L, rfl⟩ : ∃ L : ℕ, n₀ = L + 1 := ⟨n₀ - 1, by omega⟩
  exact ⟨L, not_lt.mp (hmin L (by omega)),
    fun _ _ hk hc => pow_lt_pow_of_budget hθ0 hθ1.le hspec hk hc⟩

/-! ## Part 3 — what would lift the ceiling: a polynomial kernel ceiling -/

/-- With a **polynomial** kernel ceiling `B(θ(C)) < (C+2)^d`, every slope `C` is beaten from the
explicit threshold `(C+2)^d` on. -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_spoint"]
theorem complexity_gt_of_polyCeiling {B : ℚ → ℕ} (hB : KernelCeiling B) {d : ℕ}
    (hpoly : ∀ C : ℕ, B (bScale C) < (C + 2) ^ d) (C k : ℕ) (hk : (C + 2) ^ d ≤ k) :
    C * k < complexity k :=
  complexity_gt_of_kernelCeiling hB C k (lt_of_lt_of_le (hpoly C) hk)

/-- **A14(ii)'s first target, from a polynomial ceiling**: `p_T(m^d) > (m − 2)·m^d`, i.e.
`p_T(k) > (k^{1/d} − 2)·k` along `k = m^d` — superlinear with the polynomial rate `δ = 1/d`.

This is where A14(ii) actually sits.  Its targets are *not* blocked by anything about `s`-point
configurations or subspace counting; they are exactly the statement that the W10 ceiling grows
polynomially in `1/(1−θ)`.  The obstruction is W10's: the quantitative lane produces covers, not
ceilings (`TH/ExplicitRate.lean`, `gapwiseFinite_not_ceiling`). -/
@[category research solved, AMS 11 68, ref "A1plus", group "weyl_a14_spoint"]
theorem complexity_polynomial_of_polyCeiling {B : ℚ → ℕ} (hB : KernelCeiling B) {d : ℕ}
    (hpoly : ∀ C : ℕ, B (bScale C) < (C + 2) ^ d) {m : ℕ} (hm : 2 ≤ m) :
    (m - 2) * m ^ d < complexity (m ^ d) := by
  have h : (m - 2 + 2) ^ d = m ^ d := by
    congr 1
    omega
  exact complexity_gt_of_polyCeiling hB hpoly (m - 2) (m ^ d) (le_of_eq h)

end TH
