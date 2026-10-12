/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CarryGraph.Labelled
import Mathlib.Computability.MyhillNerode
import Mathlib.Computability.NFA

/-!
# Presented languages and sofic languages ([LM95] §§1.3, 3.1–3.2)

A rooted carry graph `(X, v)` presents the language `X.langFrom v` of label words of its finite
walks from `v`, a `Language A` in Mathlib's sense.  Such languages are prefix-closed and contain
the empty word (`PrefixClosed`).  A language is **sofic** (one-sided, rooted) if some finite carry
graph presents it.

The main result connects this with Mathlib's automata theory:

  `Sofic L  ⟺  L.IsRegular ∧ PrefixClosed L`             (`sofic_iff_isRegular_and_prefixClosed`)

"⇒" goes through `toNFA X v` (every state accepting) and Mathlib's subset construction
`NFA.toDFA`, which is `CarryGraph.det` read as a DFA (`toDFA_evalFrom_toNFA`).  "⇐" restricts a
DFA to its accepting states.  With Mathlib's Myhill–Nerode theorem
(`Language.isRegular_iff_finite_range_leftQuotient`) this gives the one-sided rooted form of
[LM95, Thm 3.2.10]: a prefix-closed language is sofic iff it has finitely many follower sets
(`sofic_iff`).  The follower set of `u` in `L` [LM95, Def. 3.2.4] is Mathlib's left quotient
`L.leftQuotient u`, and no separate definition is made.

The preliminary `CG/` proved the same theorem directly through the follower-set graph.  Here it
is a corollary of Mathlib, and the follower-set graph reappears in
`Follower.lean` as the minimal presentation.

## Contents

* `langFrom`, `PrefixClosed`, `langFrom_prefixClosed`, `PrefixClosed.leftQuotient`,
  `Hom.reads`, `langFrom_subset_of_hom`, `transport`, `langFrom_transport`.
* `Sofic`, `sofic_of_finite`, `langFrom_det_singleton`.
* `toNFA`, `mem_evalFrom_toNFA`, `toNFA_accepts`, `toDFA_evalFrom_toNFA`.
* `Sofic.isRegular`, `sofic_of_isRegular`, `sofic_iff_isRegular_and_prefixClosed`, `sofic_iff`.

## References

* [LM95] D. Lind, B. Marcus, *An Introduction to Symbolic Dynamics and Coding*, Cambridge UP,
  1995.
-/

namespace CarryGraph

variable {V W A : Type*} {X : CarryGraph V A}

/-! ### The language of a rooted carry graph -/

variable (X) in
/-- The language presented by `X` from `v`: the label words of finite walks from `v`. -/
def langFrom (v : V) : Language A := {w | X.IsWord v w}

@[category API, AMS 05 37 68, ref "LM95", group "carry_language"]
theorem mem_langFrom {v : V} {w : List A} : w ∈ X.langFrom v ↔ X.IsWord v w := Iff.rfl

/-- Prefix-closed and containing the empty word. -/
def PrefixClosed (L : Language A) : Prop := [] ∈ L ∧ ∀ u w, u ++ w ∈ L → u ∈ L

@[category API, AMS 05 37 68, ref "LM95", group "carry_language"]
theorem langFrom_prefixClosed (v : V) : PrefixClosed (X.langFrom v) :=
  ⟨isWord_nil v, fun _ _ h => IsWord.of_append h⟩

/-- A follower set of a prefix-closed language at one of its words is prefix-closed. -/
@[category API, AMS 05 37 68, ref "LM95", group "carry_language"]
theorem PrefixClosed.leftQuotient {L : Language A} (hL : PrefixClosed L) {u : List A}
    (hu : u ∈ L) : PrefixClosed (L.leftQuotient u) :=
  ⟨by simpa using hu, fun x y h => hL.2 (u ++ x) y (by
    rw [Language.mem_leftQuotient] at h
    rwa [List.append_assoc])⟩

/-- The follower set of `u` from `v` is the union of the languages of the vertices `u` reaches. -/
@[category textbook, AMS 05 37 68, ref "LM95", group "carry_language"]
theorem mem_leftQuotient_langFrom {v : V} {u w : List A} :
    w ∈ (X.langFrom v).leftQuotient u ↔ ∃ t, X.Reads v u t ∧ X.IsWord t w := by
  simp only [Language.mem_leftQuotient, mem_langFrom, IsWord, reads_append]
  exact ⟨fun ⟨x, t, h1, h2⟩ => ⟨t, h1, x, h2⟩, fun ⟨t, h1, x, h2⟩ => ⟨x, t, h1, h2⟩⟩

/-- Homomorphisms carry walks to walks with the same word. -/
@[category API, AMS 05 37 68, ref "LM95", group "carry_language"]
theorem Hom.reads {Y : CarryGraph W A} (f : Hom X Y) :
    ∀ {v u : V} {w : List A}, X.Reads v w u → Y.Reads (f.toFun v) w (f.toFun u)
  | v, u, [], h => by rw [reads_nil] at h ⊢; rw [h]
  | v, u, a :: w, h => by
    obtain ⟨t, ht, h⟩ := reads_cons.1 h
    exact reads_cons.2 ⟨_, f.map_adj ht, Hom.reads f h⟩

@[category API, AMS 05 37 68, ref "LM95", group "carry_language"]
theorem langFrom_subset_of_hom {Y : CarryGraph W A} (f : Hom X Y) (v : V) :
    ∀ w, w ∈ X.langFrom v → w ∈ Y.langFrom (f.toFun v) :=
  fun _ ⟨_, h⟩ => ⟨_, f.reads h⟩

variable (X) in
/-- The copy of `X` along an equivalence of vertex types. -/
def transport (e : V ≃ W) : CarryGraph W A := ⟨fun w a => (X.succ (e.symm w) a).map e.toEmbedding⟩

@[category API, AMS 05 37 68, group "carry_language"]
theorem adj_transport {e : V ≃ W} {w w' : W} {a : A} :
    (X.transport e).Adj w a w' ↔ X.Adj (e.symm w) a (e.symm w') := by
  simp [transport, Adj, Finset.mem_map_equiv]

@[category API, AMS 05 37 68, group "carry_language"]
theorem langFrom_transport (e : V ≃ W) (v : V) : (X.transport e).langFrom (e v) = X.langFrom v := by
  let f : Hom X (X.transport e) := ⟨e, fun h => adj_transport.2 (by simpa using h)⟩
  let g : Hom (X.transport e) X := ⟨e.symm, fun h => adj_transport.1 h⟩
  ext w
  exact ⟨fun h => by simpa [g] using langFrom_subset_of_hom g (e v) w h,
    langFrom_subset_of_hom f v w⟩

/-! ### Sofic languages -/

/-- A language is **sofic** (one-sided, rooted) if a finite carry graph presents it. -/
def Sofic (L : Language A) : Prop :=
  ∃ (n : ℕ) (Y : CarryGraph (Fin n) A) (v : Fin n), Y.langFrom v = L

/-- Every finite presentation can be renumbered on `Fin n`. -/
@[category API, AMS 05 37 68, ref "LM95", group "carry_language"]
theorem sofic_of_finite [Finite V] (X : CarryGraph V A) (v : V) : Sofic (X.langFrom v) := by
  have := Fintype.ofFinite V
  exact ⟨_, X.transport (Fintype.equivFin V), _, langFrom_transport _ v⟩

/-- **Finite reach suffices**: if only finitely many vertices are reachable from `v` (the vertex
type may be infinite, as for the `DubC2` follower automaton), the language from `v` is sofic. -/
@[category textbook, AMS 05 37 68, ref "LM95", group "carry_language"]
theorem sofic_of_finite_reach {v : V} (h : {w | X.Reach v w}.Finite) : Sofic (X.langFrom v) := by
  classical
  have : Finite {w // X.Reach v w} := h.to_subtype
  let Y : CarryGraph {w // X.Reach v w} A :=
    ⟨fun w a => (X.succ w.1 a).subtype fun u => X.Reach v u⟩
  have key : ∀ (x : List A) (w : {w // X.Reach v w}), Y.IsWord w x ↔ X.IsWord w.1 x := by
    intro x
    induction x with
    | nil => exact fun w => ⟨fun _ => isWord_nil _, fun _ => isWord_nil _⟩
    | cons a x ih =>
      intro w
      rw [isWord_cons, isWord_cons]
      constructor
      · rintro ⟨u, hu, hx⟩
        exact ⟨u.1, by simpa [Y, Adj] using hu, (ih u).1 hx⟩
      · rintro ⟨u, hu, hx⟩
        exact ⟨⟨u, w.2.tail ⟨a, hu⟩⟩, by simpa [Y, Adj] using hu, (ih _).2 hx⟩
  have hL : Y.langFrom ⟨v, Relation.ReflTransGen.refl⟩ = X.langFrom v := by
    ext x
    exact key x _
  rw [← hL]
  exact sofic_of_finite Y _

@[category API, AMS 05 37 68, ref "LM95", group "carry_language"]
theorem Sofic.prefixClosed {L : Language A} (h : Sofic L) : PrefixClosed L := by
  obtain ⟨n, Y, v, rfl⟩ := h
  exact langFrom_prefixClosed v

/-- The subset construction presents the same language from `{v}`. -/
@[category textbook, AMS 05 37 68, ref "LM95", group "carry_language"]
theorem langFrom_det_singleton [DecidableEq V] (v : V) : X.det.langFrom {v} = X.langFrom v := by
  ext w
  exact isWord_det_singleton

/-! ### The Mathlib bridge: NFAs and regular languages -/

variable (X) in
/-- `X` rooted at `v` as an NFA in which every state accepts. -/
def toNFA (v : V) : NFA A V := ⟨fun s a => ↑(X.succ s a), {v}, Set.univ⟩

@[category API, AMS 05 37 68, ref "LM95", group "carry_language"]
theorem mem_evalFrom_toNFA {v s : V} :
    ∀ {S : Set V} {w : List A}, s ∈ (X.toNFA v).evalFrom S w ↔ ∃ t ∈ S, X.Reads t w s
  | S, [] => by simp [reads_nil]
  | S, a :: w => by
    rw [NFA.evalFrom_cons, mem_evalFrom_toNFA]
    simp only [NFA.mem_stepSet, toNFA, Finset.mem_coe, reads_cons, Adj]
    constructor
    · rintro ⟨t, ⟨t', ht', ht⟩, h⟩
      exact ⟨t', ht', t, ht, h⟩
    · rintro ⟨t', ht', t, ht, h⟩
      exact ⟨t, ⟨t', ht', ht⟩, h⟩

/-- **The NFA accepts the presented language.** -/
@[category textbook, AMS 05 37 68, ref "LM95", group "carry_language"]
theorem toNFA_accepts (v : V) : (X.toNFA v).accepts = X.langFrom v := by
  ext w
  rw [NFA.mem_accepts]
  simp only [mem_evalFrom_toNFA]
  constructor
  · rintro ⟨s, -, t, ht, h⟩
    obtain rfl : t = v := ht
    exact ⟨s, h⟩
  · rintro ⟨s, h⟩
    exact ⟨s, Set.mem_univ _, v, rfl, h⟩

/-- **`det` is Mathlib's subset construction**: the DFA `(X.toNFA v).toDFA` run from a finite
set `S` ends in the state `X.ends S w`, which is the state `X.det` reaches from `S`. -/
@[category textbook, AMS 05 37 68, ref "LM95", group "carry_language"]
theorem toDFA_evalFrom_toNFA [DecidableEq V] (v : V) (S : Finset V) (w : List A) :
    (X.toNFA v).toDFA.evalFrom ↑S w = ↑(X.ends S w) := by
  ext s
  change s ∈ (X.toNFA v).evalFrom ↑S w ↔ _
  rw [mem_evalFrom_toNFA, Finset.mem_coe, mem_ends]
  rfl

/-- **Sofic ⇒ regular.** -/
@[category textbook, AMS 05 37 68, ref "LM95", group "carry_language"]
theorem Sofic.isRegular {L : Language A} (h : Sofic L) : L.IsRegular := by
  obtain ⟨n, Y, v, rfl⟩ := h
  exact ⟨Set (Fin n), inferInstance, (Y.toNFA v).toDFA, by rw [NFA.toDFA_correct, toNFA_accepts]⟩

/-- **Regular and prefix-closed ⇒ sofic**: a DFA restricted to its accepting states presents a
prefix-closed language. -/
@[category textbook, AMS 05 37 68, ref "LM95", group "carry_language"]
theorem sofic_of_isRegular {L : Language A} (hreg : L.IsRegular) (hL : PrefixClosed L) :
    Sofic L := by
  classical
  obtain ⟨σ, _, M, rfl⟩ := hreg
  let Y : CarryGraph σ A := ⟨fun s a => if M.step s a ∈ M.accept then {M.step s a} else ∅⟩
  have hY : ∀ s a t, Y.Adj s a t ↔ t = M.step s a ∧ M.step s a ∈ M.accept := by
    intro s a t
    simp only [Adj, Y]
    split_ifs with h
    · simp [h]
    · simp [h]
  have key : ∀ w u, u ∈ M.accepts → (Y.IsWord (M.eval u) w ↔ u ++ w ∈ M.accepts) := by
    intro w
    induction w with
    | nil => intro u hu; rw [List.append_nil]; exact ⟨fun _ => hu, fun _ => isWord_nil _⟩
    | cons a w ih =>
      intro u hu
      have hacc : M.step (M.eval u) a ∈ M.accept ↔ u ++ [a] ∈ M.accepts := by
        rw [DFA.mem_accepts, DFA.eval_append_singleton]
      rw [isWord_cons, show u ++ a :: w = u ++ [a] ++ w by simp]
      by_cases ha : u ++ [a] ∈ M.accepts
      · rw [← ih _ ha, DFA.eval_append_singleton]
        constructor
        · rintro ⟨t, ht, hw⟩
          rwa [(hY _ _ _).1 ht |>.1] at hw
        · exact fun hw => ⟨_, (hY _ _ _).2 ⟨rfl, hacc.2 ha⟩, hw⟩
      · refine iff_of_false ?_ fun h => ha (hL.2 _ w h)
        rintro ⟨t, ht, -⟩
        exact ha (hacc.1 ((hY _ _ _).1 ht).2)
  have : M.accepts = Y.langFrom M.start := by
    ext w
    exact (key w [] hL.1).symm
  rw [this]
  exact sofic_of_finite Y _

/-- **A language is sofic iff it is regular and prefix-closed.** -/
@[category textbook, AMS 05 37 68, ref "LM95", group "carry_language"]
theorem sofic_iff_isRegular_and_prefixClosed {L : Language A} :
    Sofic L ↔ L.IsRegular ∧ PrefixClosed L :=
  ⟨fun h => ⟨h.isRegular, h.prefixClosed⟩, fun ⟨h1, h2⟩ => sofic_of_isRegular h1 h2⟩

/-- **[LM95, Thm 3.2.10], one-sided rooted form**: a prefix-closed language is sofic iff it has
finitely many follower sets.  Through Mathlib's Myhill–Nerode theorem. -/
@[category textbook, AMS 05 37 68, ref "LM95", group "carry_language"]
theorem sofic_iff {L : Language A} (hL : PrefixClosed L) :
    Sofic L ↔ (Set.range L.leftQuotient).Finite := by
  rw [sofic_iff_isRegular_and_prefixClosed, Language.isRegular_iff_finite_range_leftQuotient]
  exact ⟨And.left, fun h => ⟨h, hL⟩⟩

end CarryGraph
