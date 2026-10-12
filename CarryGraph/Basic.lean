/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Image

/-!
# Carry graphs ([LM95] §2.2, §3.1; [BJG09] §1.2)

A **carry graph** over a label alphabet `A` is a labelled digraph with vertex type `V` whose
out-neighbourhood under each label is a finite set: `succ v a : Finset V`.  The label is the
carry `s` of the recurrence `q·x_{n+1} = p·x_n + s` in every instance studied in this root, which
gives the object its name.  `V` may be infinite (the follower automaton of an affine carry graph
is, in general); finiteness is assumed by hypotheses `[Fintype V]` where it is needed.

Arcs are `X.Adj v a w`, a decidable proposition; forgetting labels gives the relation
`X.under v w`, the carrier `adm : V → V → Prop` of the unlabelled theory.  Every finite labelled
relation is a carry graph (`CarryGraph.ofRel`), and so is every finite arc set
(`CarryGraph.ofFinset`), the carrier of `ForMathlib.Combinatorics.PathGrowth`.

## Contents

* `CarryGraph`, `CarryGraph.Adj`, `CarryGraph.under`, `CarryGraph.out`.
* Constructors `CarryGraph.ofRel`, `CarryGraph.ofFinset`, `CarryGraph.arcs` (the arc set of a
  finite carry graph) and the round trip `CarryGraph.ofFinset_arcs`.
* Operations `CarryGraph.reverse`, `CarryGraph.restrict`, `CarryGraph.relabel`,
  `CarryGraph.forget`.
* `CarryGraph.Hom` — label-preserving homomorphisms.

## References

* [LM95] D. Lind, B. Marcus, *An Introduction to Symbolic Dynamics and Coding*, Cambridge UP,
  1995.
* [BJG09] J. Bang-Jensen, G. Gutin, *Digraphs: Theory, Algorithms and Applications*, 2nd ed.,
  Springer, 2009.
-/

/-- A **carry graph**: a finitely branching digraph on `V` with arcs labelled by `A`.  The arcs
from `v` with label `a` end in the finite set `succ v a`. -/
structure CarryGraph (V A : Type*) where
  /-- The `a`-successors of `v`. -/
  succ : V → A → Finset V

namespace CarryGraph

variable {V W A B : Type*}

/-! ### Arcs -/

/-- `X.Adj v a w`: there is an arc `v → w` with label `a`. -/
def Adj (X : CarryGraph V A) (v : V) (a : A) (w : V) : Prop := w ∈ X.succ v a

instance [DecidableEq V] (X : CarryGraph V A) (v : V) (a : A) : DecidablePred (X.Adj v a) :=
  fun w => inferInstanceAs (Decidable (w ∈ X.succ v a))

/-- The underlying unlabelled digraph: `v → w` if some label leads from `v` to `w`. -/
def under (X : CarryGraph V A) (v w : V) : Prop := ∃ a, X.Adj v a w

instance [DecidableEq V] [Fintype A] (X : CarryGraph V A) : DecidableRel X.under :=
  fun v w => inferInstanceAs (Decidable (∃ a, w ∈ X.succ v a))

/-- All successors of `v`, under any label. -/
def out [Fintype A] [DecidableEq V] (X : CarryGraph V A) (v : V) : Finset V :=
  Finset.univ.biUnion (X.succ v)

@[category API, AMS 05, ref "LM95", group "carry_basic"]
theorem mem_out [Fintype A] [DecidableEq V] {X : CarryGraph V A} {v w : V} :
    w ∈ X.out v ↔ X.under v w := by
  simp [out, under, Adj]

@[category API, AMS 05, ref "LM95", group "carry_basic"]
theorem ext' {X Y : CarryGraph V A} (h : ∀ v a w, X.Adj v a w ↔ Y.Adj v a w) : X = Y := by
  cases X; cases Y
  congr 1
  funext v a
  ext w
  exact h v a w

/-! ### Constructors -/

/-- The carry graph of a labelled relation on a finite vertex type. -/
def ofRel [Fintype V] (E : V → A → V → Prop) [∀ v a, DecidablePred (E v a)] : CarryGraph V A :=
  ⟨fun v a => Finset.univ.filter (E v a)⟩

@[category API, AMS 05, ref "LM95", group "carry_basic"]
theorem adj_ofRel [Fintype V] {E : V → A → V → Prop} [∀ v a, DecidablePred (E v a)]
    {v : V} {a : A} {w : V} : (ofRel E).Adj v a w ↔ E v a w := by
  simp [ofRel, Adj]

/-- The carry graph of a finite arc set `E ⊆ V × A × V` (the carrier of
`ForMathlib.Combinatorics.PathGrowth`). -/
def ofFinset [DecidableEq V] [DecidableEq A] (E : Finset (V × A × V)) : CarryGraph V A :=
  ⟨fun v a => (E.filter fun e => e.1 = v ∧ e.2.1 = a).image fun e => e.2.2⟩

@[category API, AMS 05, ref "LM95", group "carry_basic"]
theorem adj_ofFinset [DecidableEq V] [DecidableEq A] {E : Finset (V × A × V)} {v : V} {a : A}
    {w : V} : (ofFinset E).Adj v a w ↔ (v, a, w) ∈ E := by
  simp only [ofFinset, Adj, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨v', a', w'⟩, ⟨h, rfl, rfl⟩, rfl⟩
    exact h
  · intro h
    exact ⟨_, ⟨h, rfl, rfl⟩, rfl⟩

/-- The arc set of a carry graph with finite vertex and label types. -/
def arcs [Fintype V] [Fintype A] [DecidableEq V] (X : CarryGraph V A) : Finset (V × A × V) :=
  Finset.univ.filter fun e => X.Adj e.1 e.2.1 e.2.2

@[category API, AMS 05, ref "LM95", group "carry_basic"]
theorem mem_arcs [Fintype V] [Fintype A] [DecidableEq V] {X : CarryGraph V A} {v : V} {a : A}
    {w : V} : (v, a, w) ∈ X.arcs ↔ X.Adj v a w := by
  simp [arcs]

@[category API, AMS 05, ref "LM95", group "carry_basic"]
theorem ofFinset_arcs [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
    (X : CarryGraph V A) : ofFinset X.arcs = X :=
  ext' fun _ _ _ => by rw [adj_ofFinset, mem_arcs]

@[category API, AMS 05, ref "LM95", group "carry_basic"]
theorem arcs_ofFinset [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
    (E : Finset (V × A × V)) : (ofFinset E).arcs = E := by
  ext ⟨v, a, w⟩
  rw [mem_arcs, adj_ofFinset]

/-! ### Operations -/

/-- The reverse carry graph: every arc turned around, labels kept [BJG09, §1.3]. -/
def reverse [Fintype V] [DecidableEq V] (X : CarryGraph V A) : CarryGraph V A :=
  ⟨fun v a => Finset.univ.filter fun u => v ∈ X.succ u a⟩

@[category API, AMS 05, ref "BJG09", group "carry_basic"]
theorem adj_reverse [Fintype V] [DecidableEq V] {X : CarryGraph V A} {v : V} {a : A} {w : V} :
    X.reverse.Adj v a w ↔ X.Adj w a v := by
  simp [reverse, Adj]

/-- The subgraph induced on `S ⊆ V` (vertices outside `S` keep no arcs). -/
def restrict (X : CarryGraph V A) (S : Set V) [DecidablePred (· ∈ S)] : CarryGraph V A :=
  ⟨fun v a => if v ∈ S then (X.succ v a).filter (· ∈ S) else ∅⟩

@[category API, AMS 05, ref "BJG09", group "carry_basic"]
theorem adj_restrict {X : CarryGraph V A} {S : Set V} [DecidablePred (· ∈ S)] {v : V} {a : A}
    {w : V} : (X.restrict S).Adj v a w ↔ v ∈ S ∧ X.Adj v a w ∧ w ∈ S := by
  show w ∈ (if v ∈ S then (X.succ v a).filter (· ∈ S) else ∅) ↔ _
  split_ifs with h <;> simp [h, Adj]

/-- Relabel the arcs along `g : A → B`. -/
def relabel [Fintype A] [DecidableEq B] [DecidableEq V] (X : CarryGraph V A) (g : A → B) :
    CarryGraph V B :=
  ⟨fun v b => (Finset.univ.filter fun a => g a = b).biUnion (X.succ v)⟩

@[category API, AMS 05, ref "LM95", group "carry_basic"]
theorem adj_relabel [Fintype A] [DecidableEq B] [DecidableEq V] {X : CarryGraph V A}
    {g : A → B} {v : V} {b : B} {w : V} :
    (X.relabel g).Adj v b w ↔ ∃ a, g a = b ∧ X.Adj v a w := by
  simp [relabel, Adj]

/-- Forget the labels: the one-letter carry graph on the underlying digraph. -/
def forget [Fintype A] [DecidableEq V] (X : CarryGraph V A) : CarryGraph V Unit :=
  ⟨fun v _ => X.out v⟩

@[category API, AMS 05, ref "LM95", group "carry_basic"]
theorem adj_forget [Fintype A] [DecidableEq V] {X : CarryGraph V A} {v w : V} {u : Unit} :
    X.forget.Adj v u w ↔ X.under v w :=
  mem_out

/-! ### Homomorphisms -/

/-- A label-preserving **homomorphism** of carry graphs ([LM95] Def. 2.2.?, graph
homomorphism; [BJG09] §1.3). -/
structure Hom (X : CarryGraph V A) (Y : CarryGraph W A) where
  /-- The vertex map. -/
  toFun : V → W
  /-- Arcs go to arcs with the same label. -/
  map_adj : ∀ {v a w}, X.Adj v a w → Y.Adj (toFun v) a (toFun w)

@[category API, AMS 05, ref "LM95", group "carry_basic"]
theorem Hom.map_under {X : CarryGraph V A} {Y : CarryGraph W A} (f : Hom X Y) {v w : V}
    (h : X.under v w) : Y.under (f.toFun v) (f.toFun w) :=
  let ⟨a, ha⟩ := h
  ⟨a, f.map_adj ha⟩

/-- The identity homomorphism. -/
def Hom.id (X : CarryGraph V A) : Hom X X := ⟨fun v => v, fun h => h⟩

/-- Composition of homomorphisms. -/
def Hom.comp {U : Type*} {X : CarryGraph U A} {Y : CarryGraph V A} {Z : CarryGraph W A}
    (g : Hom Y Z) (f : Hom X Y) : Hom X Z :=
  ⟨g.toFun ∘ f.toFun, fun h => g.map_adj (f.map_adj h)⟩

end CarryGraph
