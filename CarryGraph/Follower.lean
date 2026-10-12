/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CarryGraph.Language
import Mathlib.Data.Set.Card

/-!
# The follower-set graph and minimal presentations ([LM95] §§3.2–3.3)

The **follower-set graph** `followerGraph A` is one carry graph on *all* languages over `A`: from
`L`, the letter `a` leads to the follower set `L.leftQuotient [a]` when `[a] ∈ L`.  It is
right-resolving, and from any prefix-closed `L` it presents `L` itself
(`langFrom_followerGraph`).  The vertices reachable from `L` are exactly the follower sets of the
words of `L` (`reach_followerGraph`), so

* `L` is sofic iff finitely many vertices are reachable from it (`sofic_iff_finite_reach`);
* a right-resolving presentation `(X, v)` maps onto the reachable part by `x ↦ X.langFrom x`, the
  merging of follower-equivalent states [LM95, Lemma 3.3.8] (`toFollower`).  So the follower-set
  graph is the minimal right-resolving presentation: it has at most `|V|` reachable states
  (`ncard_reach_le_of_rr`), and at most `2^|V|` for an arbitrary presentation
  (`ncard_reach_le`);
* if `L` is not sofic, geodesic Kőnig gives an infinite word all of whose prefixes have pairwise
  distinct follower sets (`exists_injective_of_not_sofic`).  This is the generic half of
  `DubC2.Gen.Follower.exists_injective_path`.

The construction is noncomputable (membership in a language is not decidable in general).  Its
use is to state and prove minimality and soficity, and not to compute.

## Contents

* `followerGraph`, `adj_followerGraph`, `followerGraph_rightResolving`, `reads_followerGraph`,
  `langFrom_followerGraph`, `reach_iff_exists_reads`, `reach_followerGraph`,
  `leftQuotient_eq_empty`.
* `sofic_iff_finite_reach`, `exists_injective_of_not_sofic`.
* `RightResolving.reads_eq`, `langFrom_eq_leftQuotient`, `toFollower`, `ncard_reach_le_of_rr`,
  `ncard_reach_le`, `allPer_of_followerGraph`.

## References

* [LM95] D. Lind, B. Marcus, *An Introduction to Symbolic Dynamics and Coding*, Cambridge UP,
  1995.
-/

namespace CarryGraph

variable {V A : Type*} {X : CarryGraph V A}

/-! ### Reachability by words -/

@[category API, AMS 05 37 68, group "carry_follower"]
theorem reach_iff_exists_reads {v u : V} : X.Reach v u ↔ ∃ w, X.Reads v w u := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨[], rfl⟩
    | tail _ hst ih =>
      obtain ⟨w, hw⟩ := ih
      obtain ⟨a, ha⟩ := hst
      exact ⟨w ++ [a], reads_append.2 ⟨_, hw, reads_cons.2 ⟨_, ha, rfl⟩⟩⟩
  · rintro ⟨w, hw⟩
    induction w generalizing v with
    | nil => rw [reads_nil] at hw; rw [hw]; exact Reach.refl _
    | cons a w ih =>
      obtain ⟨t, ht, hw⟩ := reads_cons.1 hw
      exact Reach.head ⟨a, ht⟩ (ih hw)

/-! ### The follower-set graph -/

variable (A) in
open Classical in
/-- **The follower-set graph** [LM95, §3.2] on all languages over `A` (the derivative automaton):
from `L`, the letter `a` leads to `L.leftQuotient [a]` when `[a] ∈ L`. -/
noncomputable def followerGraph : CarryGraph (Language A) A where
  succ L a := if [a] ∈ L then {L.leftQuotient [a]} else ∅

@[category API, AMS 05 37 68, ref "LM95", group "carry_follower"]
theorem adj_followerGraph {L L' : Language A} {a : A} :
    (followerGraph A).Adj L a L' ↔ [a] ∈ L ∧ L' = L.leftQuotient [a] := by
  classical
  simp only [Adj, followerGraph]
  split_ifs with h
  · simp [h]
  · simp [h]

@[category textbook, AMS 05 37 68, ref "LM95", group "carry_follower"]
theorem followerGraph_rightResolving : (followerGraph A).RightResolving := fun L a => by
  classical
  simp only [followerGraph]
  split_ifs <;> simp

/-- From a prefix-closed `L`, reading `w` in the follower-set graph is possible iff `w ∈ L`, and
it ends at the follower set of `w`. -/
@[category textbook, AMS 05 37 68, ref "LM95", group "carry_follower"]
theorem reads_followerGraph : ∀ {w : List A} {L L' : Language A}, PrefixClosed L →
    ((followerGraph A).Reads L w L' ↔ w ∈ L ∧ L' = L.leftQuotient w)
  | [], L, L', hL => by simp [reads_nil, hL.1]
  | a :: w, L, L', hL => by
    rw [reads_cons]
    have e : L.leftQuotient (a :: w) = (L.leftQuotient [a]).leftQuotient w :=
      L.leftQuotient_append [a] w
    constructor
    · rintro ⟨t, ht, h⟩
      obtain ⟨ha, rfl⟩ := adj_followerGraph.1 ht
      obtain ⟨hw, rfl⟩ := (reads_followerGraph (hL.leftQuotient ha)).1 h
      exact ⟨hw, e.symm⟩
    · rintro ⟨hw, rfl⟩
      have ha : [a] ∈ L := hL.2 [a] w hw
      exact ⟨_, adj_followerGraph.2 ⟨ha, rfl⟩,
        (reads_followerGraph (hL.leftQuotient ha)).2 ⟨hw, e⟩⟩

/-- **The follower-set graph presents every prefix-closed language**, from the language
itself. -/
@[category textbook, AMS 05 37 68, ref "LM95", group "carry_follower"]
theorem langFrom_followerGraph {L : Language A} (hL : PrefixClosed L) :
    (followerGraph A).langFrom L = L :=
  Language.ext fun _ => ⟨fun ⟨_, h⟩ => ((reads_followerGraph hL).1 h).1,
    fun hw => ⟨_, (reads_followerGraph hL).2 ⟨hw, rfl⟩⟩⟩

/-- The vertices reachable from `L` are the follower sets of the words of `L`. -/
@[category textbook, AMS 05 37 68, ref "LM95", group "carry_follower"]
theorem reach_followerGraph {L C : Language A} (hL : PrefixClosed L) :
    (followerGraph A).Reach L C ↔ ∃ u ∈ L, C = L.leftQuotient u := by
  rw [reach_iff_exists_reads]
  exact ⟨fun ⟨u, h⟩ => ⟨u, (reads_followerGraph hL).1 h⟩,
    fun ⟨u, hu, h⟩ => ⟨u, (reads_followerGraph hL).2 ⟨hu, h⟩⟩⟩

/-- Outside a prefix-closed language the follower set is empty. -/
@[category API, AMS 05 37 68, ref "LM95", group "carry_follower"]
theorem leftQuotient_eq_empty {L : Language A} (hL : PrefixClosed L) {u : List A} (hu : u ∉ L) :
    L.leftQuotient u = 0 :=
  Language.ext fun w => ⟨fun h => hu (hL.2 u w h), fun h => absurd h (Language.notMem_zero w)⟩

/-- **A prefix-closed language is sofic iff finitely many vertices of the follower-set graph are
reachable from it.** -/
@[category textbook, AMS 05 37 68, ref "LM95", group "carry_follower"]
theorem sofic_iff_finite_reach {L : Language A} (hL : PrefixClosed L) :
    Sofic L ↔ {C | (followerGraph A).Reach L C}.Finite := by
  rw [sofic_iff hL]
  constructor
  · refine fun h => h.subset fun C hC => ?_
    obtain ⟨u, -, rfl⟩ := (reach_followerGraph hL).1 hC
    exact ⟨u, rfl⟩
  · refine fun h => (h.insert 0).subset ?_
    rintro _ ⟨u, rfl⟩
    by_cases hu : u ∈ L
    · exact Set.mem_insert_of_mem _ ((reach_followerGraph hL).2 ⟨u, hu, rfl⟩)
    · rw [leftQuotient_eq_empty hL hu]
      exact Set.mem_insert _ _

/-- **A non-sofic language has an infinite word whose prefixes have pairwise distinct follower
sets** (geodesic Kőnig on the follower-set graph; finite alphabet).  This is the generic half of
`DubC2.Gen.Follower.exists_injective_path`. -/
@[category textbook, AMS 05 37 68, ref "LM95" "BJG09", group "carry_follower"]
theorem exists_injective_of_not_sofic [Fintype A] {L : Language A} (hL : PrefixClosed L)
    (h : ¬ Sofic L) :
    ∃ ℓ : ℕ → A, (∀ n, (List.range n).map ℓ ∈ L) ∧
      Function.Injective fun n => L.leftQuotient ((List.range n).map ℓ) := by
  classical
  rw [sofic_iff_finite_reach hL] at h
  obtain ⟨s, hs0, hs, -, hinj⟩ := exists_injective_walk_of_infinite_reach h
  choose ℓ hℓ using hs
  have hpath : (followerGraph A).IsIPath s ℓ := hℓ
  have key : ∀ n, (List.range n).map ℓ ∈ L ∧ s n = L.leftQuotient ((List.range n).map ℓ) := by
    intro n
    have := hpath.reads 0 n
    simp only [zero_add, hs0] at this
    exact (reads_followerGraph hL).1 this
  refine ⟨ℓ, fun n => (key n).1, fun m n hmn => hinj ?_⟩
  simp only at hmn
  rw [(key m).2, (key n).2, hmn]

/-! ### Minimality -/

@[category API, AMS 05 37 68, ref "LM95", group "carry_follower"]
theorem RightResolving.reads_eq (hrr : X.RightResolving) :
    ∀ {v t t' : V} {w : List A}, X.Reads v w t → X.Reads v w t' → t = t'
  | v, t, t', [], h1, h2 => by rw [reads_nil] at h1 h2; rw [h1, h2]
  | v, t, t', a :: w, h1, h2 => by
    obtain ⟨x, hx, h1⟩ := reads_cons.1 h1
    obtain ⟨x', hx', h2⟩ := reads_cons.1 h2
    obtain rfl := hrr.eq hx hx'
    exact RightResolving.reads_eq hrr h1 h2

/-- In a right-resolving presentation the follower set of a word is the language of the vertex
it reaches. -/
@[category textbook, AMS 05 37 68, ref "LM95", group "carry_follower"]
theorem langFrom_eq_leftQuotient (hrr : X.RightResolving) {v t : V} {u : List A}
    (hr : X.Reads v u t) : X.langFrom t = (X.langFrom v).leftQuotient u := by
  refine Language.ext fun w => ?_
  rw [mem_leftQuotient_langFrom]
  exact ⟨fun hw => ⟨t, hr, hw⟩, fun ⟨t', h', hw⟩ => by rwa [hrr.reads_eq hr h']⟩

/-- **Merging follower-equivalent states** [LM95, Lemma 3.3.8]: in a right-resolving carry graph,
`x ↦ X.langFrom x` is a homomorphism onto the follower-set graph. -/
@[category textbook, AMS 05 37 68, ref "LM95", group "carry_follower"]
def toFollower (hrr : X.RightResolving) : Hom X (followerGraph A) where
  toFun := X.langFrom
  map_adj {_ _ w} h := adj_followerGraph.2
    ⟨isWord_cons.2 ⟨w, h, isWord_nil w⟩, langFrom_eq_leftQuotient hrr (reads_cons.2 ⟨w, h, rfl⟩)⟩

/-- **The follower-set graph is the minimal right-resolving presentation**: a right-resolving
presentation on `V` has at least as many vertices as there are follower sets of its words. -/
@[category textbook, AMS 05 37 68, ref "LM95", group "carry_follower"]
theorem ncard_reach_le_of_rr [Fintype V] (hrr : X.RightResolving) (v : V) :
    {C | (followerGraph A).Reach (X.langFrom v) C}.ncard ≤ Fintype.card V := by
  have hsub : {C | (followerGraph A).Reach (X.langFrom v) C} ⊆ X.langFrom '' Set.univ := by
    intro C hC
    obtain ⟨u, ⟨t, ht⟩, rfl⟩ := (reach_followerGraph (langFrom_prefixClosed v)).1 hC
    exact ⟨t, Set.mem_univ _, langFrom_eq_leftQuotient hrr ht⟩
  calc _ ≤ (X.langFrom '' Set.univ).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (Set.univ : Set V).ncard := Set.ncard_image_le
    _ = Fintype.card V := by rw [Set.ncard_univ, Nat.card_eq_fintype_card]

/-- **An arbitrary presentation on `V` has at most `2^|V|` follower sets** (through the subset
construction). -/
@[category textbook, AMS 05 37 68, ref "LM95", group "carry_follower"]
theorem ncard_reach_le [Fintype V] [DecidableEq V] (v : V) :
    {C | (followerGraph A).Reach (X.langFrom v) C}.ncard ≤ 2 ^ Fintype.card V := by
  rw [← langFrom_det_singleton v, ← Fintype.card_finset]
  exact ncard_reach_le_of_rr det_rightResolving {v}

/-- **Soundness of minimization**: the label form of the follower-set graph implies the label
form of every right-resolving presentation. -/
@[category textbook, AMS 05 37 68, ref "LM95", group "carry_follower"]
theorem allPer_of_followerGraph (hrr : X.RightResolving) (h : (followerGraph A).AllPer) :
    X.AllPer :=
  allPer_of_hom (toFollower hrr) h

end CarryGraph
