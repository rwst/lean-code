/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CarryGraph.Path
import Mathlib.Logic.Relation
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Card

/-!
# Reachability and strong components ([BJG09] §1.4–1.5, §4.2; [LM95] §4.4)

Reachability in a carry graph is reachability in its underlying digraph.  On a finite vertex
type it is **computable**: the ball `X.ball v k` of vertices within distance `k` grows until it
stops, and it stops after at most `|V|` rounds (`CarryGraph.mem_reachSet`), so `Reach` is
decidable.  Mathlib has no decidable reachability for relations; this file is the replacement.

The two canonical ranks of [BJG09] §1.5 are the descendant count `desc` and the predecessor count
`preds`.  Both are **acyclic orderings of the strong component digraph** in rank form: `desc`
never increases along an arc and drops exactly across components (`desc_eq_iff`,
`desc_lt_of_not_reach`); `preds` is the dual (`preds_ssubset`, `desc_reverse`).

## Contents

* `Reach`, `SameSCC`, `Cyc`; `ReachIn n` (a walk of length exactly `n`).
* `ball v k`, `mem_ball`; `reachSet v` (for `[Fintype V]`), `mem_reachSet`, `Reach` decidable.
* `descSet`, `desc`, `desc_le_of_under`, `desc_eq_iff`, `desc_lt_of_not_reach`; `predsSet`,
  `preds`, `preds_le_of_under`, `preds_ssubset`; `reach_reverse`, `desc_reverse`.
* `reach_rank_le` — a rank non-increasing along arcs is non-increasing along paths.
* **Geodesic Kőnig** `exists_injective_walk_of_infinite_reach`: if infinitely many vertices are
  reachable from `v` in a carry graph over a finite alphabet, an infinite walk from `v` visits
  pairwise distinct vertices.

## References

* [BJG09] J. Bang-Jensen, G. Gutin, *Digraphs: Theory, Algorithms and Applications*, 2nd ed.,
  Springer, 2009.
* [LM95] D. Lind, B. Marcus, *An Introduction to Symbolic Dynamics and Coding*, Cambridge UP,
  1995.
-/

namespace CarryGraph

variable {V A : Type*} (X : CarryGraph V A)

/-- Reachability: a (possibly empty) walk from `u` to `v`. -/
def Reach : V → V → Prop := Relation.ReflTransGen X.under

/-- `u` and `v` lie in one strong component. -/
def SameSCC (u v : V) : Prop := X.Reach u v ∧ X.Reach v u

/-- `v` lies on a cycle. -/
def Cyc (v : V) : Prop := Relation.TransGen X.under v v

/-- A walk of length exactly `n` from `u` to `v`. -/
def ReachIn : ℕ → V → V → Prop
  | 0, u, v => u = v
  | n + 1, u, v => ∃ t, X.under u t ∧ ReachIn n t v

variable {X}

@[category API, AMS 05, ref "BJG09", group "carry_reach"]
theorem Reach.refl (v : V) : X.Reach v v := Relation.ReflTransGen.refl

@[category API, AMS 05, ref "BJG09", group "carry_reach"]
theorem Reach.single {u v : V} (h : X.under u v) : X.Reach u v := Relation.ReflTransGen.single h

@[category API, AMS 05, ref "BJG09", group "carry_reach"]
theorem Reach.trans {u v w : V} (h : X.Reach u v) (h' : X.Reach v w) : X.Reach u w :=
  Relation.ReflTransGen.trans h h'

@[category API, AMS 05, ref "BJG09", group "carry_reach"]
theorem Reach.head {u v w : V} (h : X.under u v) (h' : X.Reach v w) : X.Reach u w :=
  Relation.ReflTransGen.head h h'

@[category API, AMS 05, ref "BJG09", group "carry_reach"]
theorem Reach.tail {u v w : V} (h : X.Reach u v) (h' : X.under v w) : X.Reach u w :=
  Relation.ReflTransGen.tail h h'

@[category API, AMS 05, ref "BJG09", group "carry_reach"]
theorem SameSCC.refl (v : V) : X.SameSCC v v := ⟨Reach.refl v, Reach.refl v⟩

@[category API, AMS 05, ref "BJG09", group "carry_reach"]
theorem SameSCC.symm {u v : V} (h : X.SameSCC u v) : X.SameSCC v u := ⟨h.2, h.1⟩

@[category API, AMS 05, ref "BJG09", group "carry_reach"]
theorem SameSCC.trans {u v w : V} (h : X.SameSCC u v) (h' : X.SameSCC v w) : X.SameSCC u w :=
  ⟨h.1.trans h'.1, h'.2.trans h.2⟩

/-- Being in the same strong component is an equivalence relation [BJG09, §1.5]. -/
@[category textbook, AMS 05, ref "BJG09", group "carry_reach"]
theorem sameSCC_equivalence : Equivalence X.SameSCC :=
  ⟨SameSCC.refl, SameSCC.symm, SameSCC.trans⟩

/-- `v` lies on a cycle iff it has a successor reaching back to it. -/
@[category API, AMS 05, ref "BJG09", group "carry_reach"]
theorem cyc_iff {v : V} : X.Cyc v ↔ ∃ t, X.under v t ∧ X.Reach t v := by
  constructor
  · intro h
    obtain ⟨t, ht, h'⟩ := Relation.TransGen.head'_iff.1 h
    exact ⟨t, ht, h'⟩
  · rintro ⟨t, ht, h'⟩
    exact Relation.TransGen.head' ht h'

/-- Every vertex on a closed walk through a cyclic vertex is cyclic. -/
@[category API, AMS 05, ref "BJG09", group "carry_reach"]
theorem Cyc.of_sameSCC {u v : V} (h : X.Cyc u) (huv : X.SameSCC u v) : X.Cyc v := by
  exact Relation.TransGen.trans_right huv.2 (Relation.TransGen.trans_left h huv.1)

/-- Reachability inside a forward-closed set is reachability in the restriction to it. -/
@[category API, AMS 05, ref "BJG09", group "carry_reach"]
theorem Reach.restrict {S : Set V} [DecidablePred (· ∈ S)]
    (hS : ∀ v ∈ S, ∀ w, X.under v w → w ∈ S) {v w : V} (hv : v ∈ S) (h : X.Reach v w) :
    (X.restrict S).Reach v w := by
  have key : ∀ w, X.Reach v w → w ∈ S ∧ (X.restrict S).Reach v w := by
    intro w h
    induction h with
    | refl => exact ⟨hv, Reach.refl v⟩
    | tail _ hbc ih =>
      obtain ⟨a, hab⟩ := hbc
      have hc := hS _ ih.1 _ ⟨a, hab⟩
      exact ⟨hc, ih.2.tail ⟨a, adj_restrict.2 ⟨ih.1, hab, hc⟩⟩⟩
  exact (key w h).2

/-- Homomorphisms preserve reachability. -/
@[category API, AMS 05, ref "BJG09", group "carry_reach"]
theorem Hom.reach_map {W : Type*} {Y : CarryGraph W A} (f : Hom X Y) {u v : V}
    (h : X.Reach u v) : Y.Reach (f.toFun u) (f.toFun v) := by
  induction h with
  | refl => exact Reach.refl _
  | tail _ hbc ih => exact ih.tail (f.map_under hbc)

/-- **Homomorphisms preserve cycles** (generic form of `DubC.onCycle_proj`). -/
@[category textbook, AMS 05, ref "BJG09", group "carry_reach"]
theorem Hom.cyc_map {W : Type*} {Y : CarryGraph W A} (f : Hom X Y) {v : V} (h : X.Cyc v) :
    Y.Cyc (f.toFun v) := by
  obtain ⟨t, ht, htv⟩ := cyc_iff.1 h
  exact cyc_iff.2 ⟨f.toFun t, f.map_under ht, f.reach_map htv⟩

/-! ### Walks of a given length -/

@[category API, AMS 05, ref "BJG09", group "carry_reach"]
theorem reachIn_succ' : ∀ {n : ℕ} {u v : V},
    X.ReachIn (n + 1) u v ↔ ∃ t, X.ReachIn n u t ∧ X.under t v
  | 0, u, v => by simp [ReachIn]
  | n + 1, u, v => by
    simp only [ReachIn] at *
    constructor
    · rintro ⟨t, ht, h⟩
      obtain ⟨s, hs, hsv⟩ := reachIn_succ'.1 h
      exact ⟨s, ⟨t, ht, hs⟩, hsv⟩
    · rintro ⟨s, ⟨t, ht, hs⟩, hsv⟩
      exact ⟨t, ht, reachIn_succ'.2 ⟨s, hs, hsv⟩⟩

@[category API, AMS 05, ref "BJG09", group "carry_reach"]
theorem reach_iff_exists_reachIn {u v : V} : X.Reach u v ↔ ∃ n, X.ReachIn n u v := by
  constructor
  · intro h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨0, rfl⟩
    | head hut _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, _, hut, hn⟩
  · rintro ⟨n, hn⟩
    induction n generalizing u with
    | zero => exact hn ▸ Reach.refl u
    | succ n ih =>
      obtain ⟨t, ht, h⟩ := hn
      exact Reach.head ht (ih h)

@[category API, AMS 05, ref "BJG09", group "carry_reach"]
theorem ReachIn.isWalk : ∀ {n : ℕ} {u v : V}, X.ReachIn n u v →
    ∃ g, g 0 = u ∧ g n = v ∧ X.IsWalk g n
  | 0, u, v, h => ⟨fun _ => u, rfl, h, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | n + 1, u, v, ⟨t, ht, h⟩ => by
    obtain ⟨g, hg0, hgn, hg⟩ := ReachIn.isWalk h
    refine ⟨fun i => if i = 0 then u else g (i - 1), rfl, by simpa using hgn, fun i hi => ?_⟩
    rcases i with _ | i
    · simpa [hg0] using ht
    · simpa using hg i (by omega)

/-! ### Balls and the computable reach set -/

section ball

variable [Fintype A] [DecidableEq V]

variable (X) in
/-- The vertices within distance `k` of `v`. -/
def ball (v : V) : ℕ → Finset V
  | 0 => {v}
  | k + 1 => ball v k ∪ (ball v k).biUnion X.out

@[category API, AMS 05, ref "BJG09", group "carry_reach"]
theorem mem_ball {v w : V} : ∀ {k : ℕ}, w ∈ X.ball v k ↔ ∃ n ≤ k, X.ReachIn n v w
  | 0 => by
    simp only [ball, Finset.mem_singleton, Nat.le_zero, exists_eq_left, ReachIn]
    exact eq_comm
  | k + 1 => by
    simp only [ball, Finset.mem_union, Finset.mem_biUnion, mem_out, mem_ball]
    constructor
    · rintro (⟨n, hn, h⟩ | ⟨u, ⟨n, hn, h⟩, huw⟩)
      · exact ⟨n, by omega, h⟩
      · exact ⟨n + 1, by omega, reachIn_succ'.2 ⟨u, h, huw⟩⟩
    · rintro ⟨n, hn, h⟩
      rcases Nat.lt_or_ge n (k + 1) with hlt | hge
      · exact Or.inl ⟨n, by omega, h⟩
      · obtain rfl : n = k + 1 := by omega
        obtain ⟨u, hu, huw⟩ := reachIn_succ'.1 h
        exact Or.inr ⟨u, ⟨k, le_rfl, hu⟩, huw⟩

@[category API, AMS 05, ref "BJG09", group "carry_reach"]
theorem ball_mono {v : V} {k l : ℕ} (h : k ≤ l) : X.ball v k ⊆ X.ball v l := fun w hw => by
  obtain ⟨n, hn, h'⟩ := mem_ball.1 hw
  exact mem_ball.2 ⟨n, hn.trans h, h'⟩

@[category API, AMS 05, ref "BJG09", group "carry_reach"]
theorem reach_of_mem_ball {v w : V} {k : ℕ} (h : w ∈ X.ball v k) : X.Reach v w :=
  let ⟨n, _, h⟩ := mem_ball.1 h
  reach_iff_exists_reachIn.2 ⟨n, h⟩

/-- Once a ball stops growing, it contains everything reachable. -/
@[category API, AMS 05, ref "BJG09", group "carry_reach"]
theorem mem_ball_of_stable {v : V} {k : ℕ} (hk : X.ball v (k + 1) = X.ball v k) {w : V}
    (h : X.Reach v w) : w ∈ X.ball v k := by
  induction h with
  | refl => exact mem_ball.2 ⟨0, by omega, rfl⟩
  | tail _ htw ih =>
    rw [← hk, ball]
    exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨_, ih, mem_out.2 htw⟩)

/-- **The ball stabilises within `|V|` rounds**: a strictly growing chain of balls would have
more than `|V|` elements. -/
@[category research solved, AMS 05, ref "BJG09", group "carry_reach"]
theorem exists_ball_stable [Fintype V] (v : V) :
    ∃ k ≤ Fintype.card V, X.ball v (k + 1) = X.ball v k := by
  by_contra! hc
  have hgrow : ∀ k ≤ Fintype.card V, k + 1 ≤ (X.ball v k).card := by
    intro k hk
    induction k with
    | zero => simp [ball]
    | succ k ih =>
      have hss : X.ball v k ⊂ X.ball v (k + 1) :=
        Finset.ssubset_iff_subset_ne.2 ⟨ball_mono (by omega), (hc k (by omega)).symm⟩
      have := Finset.card_lt_card hss
      have := ih (by omega)
      omega
  have := hgrow _ le_rfl
  have := Finset.card_le_univ (X.ball v (Fintype.card V))
  omega

variable (X) in
/-- The set of vertices reachable from `v`, computed as the ball of radius `|V|`. -/
def reachSet [Fintype V] (v : V) : Finset V := X.ball v (Fintype.card V)

/-- **`reachSet` computes reachability.** -/
@[category research solved, AMS 05, ref "BJG09", group "carry_reach"]
theorem mem_reachSet [Fintype V] {v w : V} : w ∈ X.reachSet v ↔ X.Reach v w := by
  refine ⟨reach_of_mem_ball, fun h => ?_⟩
  obtain ⟨k, hk, hst⟩ := exists_ball_stable (X := X) v
  exact ball_mono hk (mem_ball_of_stable hst h)

instance decReach [Fintype V] : DecidableRel X.Reach := fun v w =>
  decidable_of_iff (w ∈ X.reachSet v) mem_reachSet

end ball

/-- A rank that never increases along an arc never increases along a path. -/
@[category API, AMS 05, ref "BJG09", group "carry_reach"]
theorem reach_rank_le (ρ : V → ℕ) (hle : ∀ s t, X.under s t → ρ t ≤ ρ s) {u v : V}
    (h : X.Reach u v) : ρ v ≤ ρ u := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih => exact (hle _ _ hbc).trans ih

/-! ### The two canonical ranks -/

section ranks

variable [Fintype V] [Fintype A] [DecidableEq V]

variable (X) in
/-- The vertices reachable from `v`. -/
def descSet (v : V) : Finset V := Finset.univ.filter (X.Reach v)

variable (X) in
/-- **The descendant count**, an acyclic ordering of the strong component digraph in rank
form. -/
def desc (v : V) : ℕ := (X.descSet v).card

variable (X) in
/-- The vertices from which `v` is reachable. -/
def predsSet (v : V) : Finset V := Finset.univ.filter (X.Reach · v)

variable (X) in
/-- **The predecessor count**, the dual acyclic ordering. -/
def preds (v : V) : ℕ := (X.predsSet v).card

@[category API, AMS 05, ref "BJG09", group "carry_reach"]
theorem mem_descSet {v u : V} : u ∈ X.descSet v ↔ X.Reach v u := by simp [descSet]

@[category API, AMS 05, ref "BJG09", group "carry_reach"]
theorem mem_predsSet {v u : V} : u ∈ X.predsSet v ↔ X.Reach u v := by simp [predsSet]

@[category API, AMS 05, ref "BJG09", group "carry_reach"]
theorem descSet_subset_of_reach {s t : V} (h : X.Reach s t) : X.descSet t ⊆ X.descSet s :=
  fun _ hu => mem_descSet.2 (h.trans (mem_descSet.1 hu))

@[category API, AMS 05, ref "BJG09", group "carry_reach"]
theorem predsSet_subset_of_reach {s t : V} (h : X.Reach s t) : X.predsSet s ⊆ X.predsSet t :=
  fun _ hu => mem_predsSet.2 ((mem_predsSet.1 hu).trans h)

/-- [BJG09, §1.5]: the descendant count never increases along an arc. -/
@[category textbook, AMS 05, ref "BJG09", group "carry_reach"]
theorem desc_le_of_under {s t : V} (h : X.under s t) : X.desc t ≤ X.desc s :=
  Finset.card_le_card (descSet_subset_of_reach (Reach.single h))

/-- [BJG09, §1.5]: an arc `s → t` keeps the descendant count iff it lies inside a strong
component. -/
@[category textbook, AMS 05, ref "BJG09", group "carry_reach"]
theorem desc_eq_iff {s t : V} (h : X.under s t) : X.desc t = X.desc s ↔ X.Reach t s := by
  constructor
  · intro heq
    have hsub := descSet_subset_of_reach (Reach.single h)
    have := Finset.eq_of_subset_of_card_le hsub (by rw [desc, desc] at heq; omega)
    exact mem_descSet.1 (this ▸ mem_descSet.2 (Reach.refl s))
  · intro hts
    exact le_antisymm (desc_le_of_under h) (Finset.card_le_card (descSet_subset_of_reach hts))

/-- **Acyclic ordering** [BJG09, Prop. 1.4.3, §1.5]: an arc leaving a strong component strictly
lowers the descendant count. -/
@[category textbook, AMS 05, ref "BJG09", group "carry_reach"]
theorem desc_lt_of_not_reach {s t : V} (h : X.under s t) (hts : ¬ X.Reach t s) :
    X.desc t < X.desc s :=
  lt_of_le_of_ne (desc_le_of_under h) fun he => hts ((desc_eq_iff h).1 he)

@[category API, AMS 05, ref "BJG09", group "carry_reach"]
theorem desc_le_card (v : V) : X.desc v ≤ Fintype.card V := Finset.card_le_univ _

/-- The predecessor count never decreases along an arc. -/
@[category textbook, AMS 05, ref "BJG09", group "carry_reach"]
theorem preds_le_of_under {s t : V} (h : X.under s t) : X.preds s ≤ X.preds t :=
  Finset.card_le_card (predsSet_subset_of_reach (Reach.single h))

/-- Across an arc between two strong components, `predsSet s ⊊ predsSet t` ([Oda26] §6.2,
`Oda.WG.preds_ssubset`). -/
@[category textbook, AMS 05, ref "BJG09" "Oda26", group "carry_reach"]
theorem preds_ssubset {s t : V} (h : X.under s t) (hts : ¬ X.Reach t s) :
    X.predsSet s ⊂ X.predsSet t :=
  Finset.ssubset_iff_of_subset (predsSet_subset_of_reach (Reach.single h)) |>.2
    ⟨t, mem_predsSet.2 (Reach.refl t), fun hm => hts (mem_predsSet.1 hm)⟩

end ranks

/-! ### Duality: reversing the arcs -/

@[category API, AMS 05, ref "BJG09", group "carry_reach"]
theorem under_reverse [Fintype V] [DecidableEq V] {v w : V} :
    X.reverse.under v w ↔ X.under w v := by
  simp only [under, adj_reverse]

@[category textbook, AMS 05, ref "BJG09", group "carry_reach"]
theorem reach_reverse [Fintype V] [DecidableEq V] {v w : V} :
    X.reverse.Reach v w ↔ X.Reach w v := by
  constructor
  · intro h
    induction h with
    | refl => exact Reach.refl _
    | tail _ hbc ih => exact Reach.head (under_reverse.1 hbc) ih
  · intro h
    induction h with
    | refl => exact Reach.refl _
    | tail _ hbc ih => exact Reach.head (under_reverse.2 hbc) ih

/-- **Duality of the canonical ranks**: descendants in the reverse graph are predecessors. -/
@[category textbook, AMS 05, ref "BJG09", group "carry_reach"]
theorem desc_reverse [Fintype V] [Fintype A] [DecidableEq V] (v : V) :
    X.reverse.desc v = X.preds v := by
  unfold desc preds
  congr 1
  ext u
  rw [mem_descSet, mem_predsSet, reach_reverse]

/-! ### Geodesic Kőnig -/

section geodesic

open Classical in
/-- The distance from `v` (`0` for unreachable vertices). -/
noncomputable def dist (v w : V) : ℕ :=
  if h : ∃ n, X.ReachIn n v w then Nat.find h else 0

@[category API, AMS 05, ref "BJG09", group "carry_reach"]
theorem reachIn_dist {v w : V} (h : X.Reach v w) : X.ReachIn (X.dist v w) v w := by
  classical
  have h' := reach_iff_exists_reachIn.1 h
  simp only [dist, h', ↓reduceDIte]
  exact Nat.find_spec h'

@[category API, AMS 05, ref "BJG09", group "carry_reach"]
theorem dist_le {v w : V} {n : ℕ} (h : X.ReachIn n v w) : X.dist v w ≤ n := by
  classical
  have h' : ∃ n, X.ReachIn n v w := ⟨n, h⟩
  simp only [dist, h', ↓reduceDIte]
  exact Nat.find_min' _ h

@[category API, AMS 05, ref "BJG09", group "carry_reach"]
theorem dist_succ_le {v u w : V} (hu : X.Reach v u) (h : X.under u w) :
    X.dist v w ≤ X.dist v u + 1 :=
  dist_le (reachIn_succ'.2 ⟨u, reachIn_dist hu, h⟩)

variable [Fintype A] [DecidableEq V]

variable (X) in
open Classical in
/-- The geodesic graph from `v`: the arcs `u → w` with `u` reachable and `dist w = dist u + 1`. -/
noncomputable def geo (v : V) : CarryGraph V Unit :=
  ⟨fun u _ => (X.out u).filter fun w => X.Reach v u ∧ X.dist v w = X.dist v u + 1⟩

@[category API, AMS 05, ref "BJG09", group "carry_reach"]
theorem under_geo {v u w : V} :
    (X.geo v).under u w ↔ X.under u w ∧ X.Reach v u ∧ X.dist v w = X.dist v u + 1 := by
  simp [geo, under, Adj, mem_out]

/-- Every reachable vertex is reached from `v` along geodesic arcs in exactly `dist` steps. -/
@[category API, AMS 05, ref "BJG09", group "carry_reach"]
theorem geo_reachIn {v : V} :
    ∀ (n : ℕ) {w : V}, X.Reach v w → X.dist v w = n → (X.geo v).ReachIn n v w
  | 0, w, h, hd => by
    have := reachIn_dist h
    rw [hd] at this
    exact this
  | n + 1, w, h, hd => by
    have h1 := reachIn_dist h
    rw [hd] at h1
    obtain ⟨u, hu, huw⟩ := reachIn_succ'.1 h1
    have hru : X.Reach v u := reach_iff_exists_reachIn.2 ⟨n, hu⟩
    have hdu : X.dist v u = n := by
      have := dist_le hu
      have := dist_succ_le hru huw
      omega
    exact reachIn_succ'.2 ⟨u, geo_reachIn n hru hdu, under_geo.2 ⟨huw, hru, by omega⟩⟩

/-- **Geodesic Kőnig** (generic form of `DubC2.Gen.Follower.exists_injective_path`): if
infinitely many vertices are reachable from `v` in a carry graph over a finite alphabet, then an
infinite walk from `v` visits pairwise distinct vertices; indeed `dist v (s n) = n`. -/
@[category research solved, AMS 05, ref "BJG09", group "carry_reach"]
theorem exists_injective_walk_of_infinite_reach {v : V} (hinf : {w | X.Reach v w}.Infinite) :
    ∃ s : ℕ → V, s 0 = v ∧ (∀ n, X.under (s n) (s (n + 1))) ∧ (∀ n, X.dist v (s n) = n) ∧
      Function.Injective s := by
  -- walks of every length in the geodesic graph
  have hw : ∀ n, (X.geo v).HasWalk v n := by
    intro n
    obtain ⟨w, hw, hwn⟩ := hinf.exists_notMem_finset (X.ball v n)
    have hr : X.Reach v w := hw
    have hd : n ≤ X.dist v w := by
      by_contra hlt
      exact hwn (mem_ball.2 ⟨_, by omega, reachIn_dist hr⟩)
    obtain ⟨g, hg0, -, hg⟩ := (geo_reachIn _ hr rfl).isWalk
    exact (hasWalk_iff.2 ⟨g, hg0, hg⟩).mono hd
  obtain ⟨s, hs0, hs⟩ := exists_walk_of_forall_hasWalk hw
  have hd : ∀ n, X.dist v (s n) = n := by
    intro n
    induction n with
    | zero =>
      rw [hs0]
      have := dist_le (X := X) (show X.ReachIn 0 v v from rfl)
      omega
    | succ n ih => rw [(under_geo.1 (hs n)).2.2, ih]
  refine ⟨s, hs0, fun n => (under_geo.1 (hs n)).1, hd, fun m n h => ?_⟩
  rw [← hd m, ← hd n, h]

end geodesic

end CarryGraph
