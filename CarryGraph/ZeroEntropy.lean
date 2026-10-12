/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CarryGraph.Horseshoe
import Mathlib.Tactic.TFAE

/-!
# Zero entropy, six ways ([LM95] §§2.2, 4.1, 4.4; [BJG09] §1.5)

For a finite carry graph the following are equivalent (`zeroEntropy_tfae`):

1. a labelled rank exists (`IsLRank`) — the common shape of the corpus certificates
   `DubC.CertOK`, `DubC2.Gen.detOK`, `FollowerCheck.nodeOK`;
2. no vertex has two distinct arcs inside its strong component (`LNoBranch`);
3. every infinite labelled path is eventually periodic, vertices and labels with one period
   (`AllEvPer`);
4. the number of labelled paths grows polynomially (`PolyGrowth`);
5. the entropy is `≤ 0` (it is `0` when there is a cycle and `⊥` otherwise);
6. every strong component carrying a cycle is a simple cycle (`SimpleCycles`): a cyclic vertex
   has exactly one arc staying in its component — the phase face of [Oda26] Thm. 21 for
   letter-labelled graphs.

The unlabelled theory is the special case of the label-forgetting graph `X.forget`
(`noBranch_tfae`): a rank exists ⟺ no vertex branches inside its strong component ⟺ every
infinite walk is eventually periodic ⟺ the walk count grows polynomially ⟺ `X.forget` has
entropy `≤ 0`.  This extends the zero-entropy theorem of the preliminary `CG/` by two faces.

## Contents

* `AllEvPer`, `SimpleCycles`, `lnoBranch_iff_simpleCycles`, `allEvPer_of_isLRank`,
  `lnoBranch_of_allEvPer`.
* `zeroEntropy_tfae` — the six-way equivalence.
* `under_forget`, `reach_forget`, `isLRank_forget_iff`, `lnoBranch_forget_iff`,
  `noBranch_tfae` — the unlabelled reading.
* `Decidable` instances for `IsRank`, `IsLRank`, `NoBranch`, `LNoBranch`, `Functional`,
  `RightResolving`, `IsSuperEigen`, `IsSubEigen` (finite `V`, `A`), so small witnesses can be
  checked by `decide`.

## References

* [LM95] D. Lind, B. Marcus, *An Introduction to Symbolic Dynamics and Coding*, Cambridge UP,
  1995.
* [BJG09] J. Bang-Jensen, G. Gutin, *Digraphs: Theory, Algorithms and Applications*, 2nd ed.,
  Springer, 2009.
* [Oda26] Odagiri, floor-function certificates (2026).
-/

namespace CarryGraph

variable {V A : Type*} {X : CarryGraph V A}

variable (X) in
/-- Every infinite labelled path is eventually periodic, vertices and labels with one period. -/
def AllEvPer : Prop :=
  ∀ s ℓ, X.IsIPath s ℓ → ∃ n₀ L, 0 < L ∧ ∀ m, n₀ ≤ m → s (m + L) = s m ∧ ℓ (m + L) = ℓ m

variable (X) in
/-- Every strong component carrying a cycle is a simple cycle: a cyclic vertex has exactly one
arc whose target returns to it. -/
def SimpleCycles : Prop :=
  ∀ v, X.Cyc v → ∃ a t, X.Adj v a t ∧ X.Reach t v ∧
    ∀ b u, X.Adj v b u → X.Reach u v → b = a ∧ u = t

/-- **Face 6**: no branching ⟺ the cyclic components are simple cycles. -/
@[category textbook, AMS 05 37, ref "LM95" "BJG09", group "carry_zero_entropy"]
theorem lnoBranch_iff_simpleCycles : X.LNoBranch ↔ X.SimpleCycles := by
  constructor
  · intro h v hv
    obtain ⟨t, ⟨a, hat⟩, htv⟩ := cyc_iff.1 hv
    exact ⟨a, t, hat, htv, fun b u hbu huv => h v b a u t hbu hat huv htv⟩
  · intro h v a b t u hvt hvu htv huv
    obtain ⟨c, w, -, -, huniq⟩ := h v (cyc_iff.2 ⟨t, ⟨a, hvt⟩, htv⟩)
    obtain ⟨rfl, rfl⟩ := huniq a t hvt htv
    obtain ⟨rfl, rfl⟩ := huniq b u hvu huv
    exact ⟨rfl, rfl⟩

/-- **(1 ⇒ 3)** is `IsLRank.evPer`. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_zero_entropy"]
theorem allEvPer_of_isLRank [Finite V] {ρ : V → ℕ} (h : X.IsLRank ρ) : X.AllEvPer :=
  fun _ _ hs => h.evPer hs (Set.toFinite _)

/-- **(3 ⇒ 2)**: a branching vertex carries a two-petal horseshoe, hence an infinite path that
is not eventually periodic. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_zero_entropy"]
theorem lnoBranch_of_allEvPer (h : X.AllEvPer) : X.LNoBranch := by
  intro v a b t u hvt hvu htv huv
  by_contra hne
  obtain ⟨H⟩ := exists_horseshoe_of_branch hvt hvu hne htv huv
  obtain ⟨s, ℓ, -, hs, hnot⟩ := H.exists_not_evPer (i := true) (j := false) (by decide)
  exact hnot (h s ℓ hs)

/-- **Zero entropy of a finite carry graph, six ways** ([LM95] §§2.2, 4.1, 4.4; [BJG09] §1.5;
[Oda26] Thm. 21). -/
@[category textbook, AMS 05 37, ref "LM95" "BJG09" "Oda26", group "carry_zero_entropy"]
theorem zeroEntropy_tfae [Fintype V] [Fintype A] [DecidableEq V] :
    [∃ ρ, X.IsLRank ρ, X.LNoBranch, X.AllEvPer, X.PolyGrowth, X.entropy ≤ 0,
      X.SimpleCycles].TFAE := by
  tfae_have 1 ↔ 2 := exists_isLRank_iff_lnoBranch
  tfae_have 1 → 3 := fun ⟨_, h⟩ => allEvPer_of_isLRank h
  tfae_have 3 → 2 := lnoBranch_of_allEvPer
  tfae_have 2 → 4 := polyGrowth_of_lnoBranch
  tfae_have 4 → 5 := entropy_le_zero_of_polyGrowth
  tfae_have 5 → 2 := entropy_le_zero_iff.1
  tfae_have 2 ↔ 6 := lnoBranch_iff_simpleCycles
  tfae_finish

/-! ### The unlabelled reading -/

section forget

variable [Fintype A] [DecidableEq V]

@[category API, AMS 05, group "carry_zero_entropy"]
theorem under_forget {v w : V} : X.forget.under v w ↔ X.under v w :=
  ⟨fun ⟨_, h⟩ => adj_forget.1 h, fun h => ⟨(), adj_forget.2 h⟩⟩

@[category API, AMS 05, group "carry_zero_entropy"]
theorem under_forget_eq : X.forget.under = X.under :=
  funext₂ fun _ _ => propext under_forget

@[category API, AMS 05, group "carry_zero_entropy"]
theorem reach_forget {v w : V} : X.forget.Reach v w ↔ X.Reach v w := by
  unfold Reach
  rw [under_forget_eq]

@[category API, AMS 05, group "carry_zero_entropy"]
theorem isLRank_forget_iff {ρ : V → ℕ} : X.forget.IsLRank ρ ↔ X.IsRank ρ := by
  simp only [IsLRank, IsRank, adj_forget, true_and]
  exact ⟨fun ⟨h1, h2⟩ =>
    ⟨fun s t h => h1 s () t h, fun s t u ht hu h3 h4 => h2 s () () t u ht hu h3 h4⟩,
    fun ⟨h1, h2⟩ => ⟨fun s _ t h => h1 s t h, fun s _ _ t u ht hu h3 h4 => h2 s t u ht hu h3 h4⟩⟩

@[category API, AMS 05, group "carry_zero_entropy"]
theorem lnoBranch_forget_iff : X.forget.LNoBranch ↔ X.NoBranch := by
  simp only [LNoBranch, NoBranch, adj_forget, reach_forget, true_and]
  exact ⟨fun h v t u ht hu h1 h2 => h v () () t u ht hu h1 h2,
    fun h v _ _ t u ht hu h1 h2 => h v t u ht hu h1 h2⟩

/-- **Zero entropy of the underlying digraph, five ways** (unlabelled; the
entropy face is new): a rank exists ⟺ no branching inside strong components ⟺ every
infinite walk is eventually periodic ⟺ walk counts grow polynomially ⟺ entropy `≤ 0`. -/
@[category textbook, AMS 05 37, ref "LM95" "BJG09", group "carry_zero_entropy"]
theorem noBranch_tfae [Fintype V] :
    [∃ ρ, X.IsRank ρ, X.NoBranch,
      ∀ s : ℕ → V, (∀ n, X.under (s n) (s (n + 1))) →
        ∃ n₀ L, 0 < L ∧ ∀ m, n₀ ≤ m → s (m + L) = s m,
      X.forget.PolyGrowth, X.forget.entropy ≤ 0].TFAE := by
  have T := X.forget.zeroEntropy_tfae
  tfae_have 1 ↔ 2 := exists_isRank_iff_noBranch
  tfae_have 2 ↔ 4 := by
    rw [← lnoBranch_forget_iff]
    exact T.out 2 4
  tfae_have 2 ↔ 5 := by
    rw [← lnoBranch_forget_iff]
    exact T.out 2 5
  tfae_have 2 ↔ 3 := by
    rw [← lnoBranch_forget_iff, (T.out 2 3 :)]
    constructor
    · intro h s hs
      obtain ⟨n₀, L, hL, hper⟩ := h s (fun _ => ()) fun n => adj_forget.2 (hs n)
      exact ⟨n₀, L, hL, fun m hm => (hper m hm).1⟩
    · intro h s ℓ hs
      obtain ⟨n₀, L, hL, hper⟩ := h s fun n => adj_forget.1 (hs n)
      exact ⟨n₀, L, hL, fun m hm => ⟨hper m hm, rfl⟩⟩
  tfae_finish

end forget

/-! ### Decidability of the witness predicates -/

section decide

variable [Fintype V] [Fintype A] [DecidableEq V]

instance decAdj (s : V) (a : A) (t : V) : Decidable (X.Adj s a t) :=
  inferInstanceAs (Decidable (t ∈ X.succ s a))

instance decIsRank (ρ : V → ℕ) : Decidable (X.IsRank ρ) := by unfold IsRank; infer_instance

instance decIsLRank [DecidableEq A] (ρ : V → ℕ) : Decidable (X.IsLRank ρ) :=
  have : ∀ s a b t u, Decidable
      (X.Adj s a t → X.Adj s b u → ρ t = ρ s → ρ u = ρ s → a = b ∧ t = u) :=
    fun _ _ _ _ _ => inferInstance
  by unfold IsLRank; infer_instance

instance decNoBranch : Decidable X.NoBranch := by unfold NoBranch; infer_instance

instance decLNoBranch [DecidableEq A] : Decidable X.LNoBranch :=
  have : ∀ v a b t u, Decidable
      (X.Adj v a t → X.Adj v b u → X.Reach t v → X.Reach u v → a = b ∧ t = u) :=
    fun _ _ _ _ _ => inferInstance
  by unfold LNoBranch; infer_instance

instance decFunctional [DecidableEq A] : Decidable X.Functional :=
  have : ∀ v a b u w, Decidable (X.Adj v a u → X.Adj v b w → a = b ∧ u = w) :=
    fun _ _ _ _ _ => inferInstance
  by unfold Functional; infer_instance

instance decRightResolving : Decidable X.RightResolving := by
  unfold RightResolving; infer_instance

instance decIsSuperEigen (w : V → ℕ) (a b : ℕ) : Decidable (X.IsSuperEigen w a b) := by
  unfold IsSuperEigen; infer_instance

instance decIsSubEigen (w : V → ℕ) (a b : ℕ) : Decidable (X.IsSubEigen w a b) := by
  unfold IsSubEigen; infer_instance

end decide

end CarryGraph
