/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import ForMathlib.Dynamics.SymbolicDynamics.Complexity
import Mathlib.Logic.Relation
import Mathlib.Tactic.Common
import Mathlib.Tactic.Push

/-!
# Rauzy graphs of a subshift

The **Rauzy graph** `G_n(X)` of a subshift has the legal words of length `n` as vertices and the
legal words of length `n + 1` as edges, an edge `e` running from `e` with its last letter dropped
to `e` with its first letter dropped.  It is the finite approximation through which the
combinatorics of a subshift is usually read: the walks of `G_n(X)` are the length-`n` windows of
the points of `X`, and `X` is the inverse limit of the `G_n(X)`.

The graph is not packaged as a `SimpleGraph` or a `Quiver` — it is a relation on a finite type, and
reachability is `Relation.ReflTransGen`, which already has the induction principle every proof here
uses.

## Main definitions

* `edgeSrc e = e ∘ Fin.castSucc`, `edgeTgt e = e ∘ Fin.succ` — the two ends of an edge.
* `Step L n a b` — there is an edge of `L (n+1)` from `a` to `b`; `Reach L n` is its
  reflexive-transitive closure.
* `IsRightSpecial L n v` — `v` has two distinct right extensions in `L (n+1)`, i.e. out-degree at
  least two in `G_n`; `IsLeftSpecial L n v` is the mirror, in-degree at least two.
* `Subshift.IsStronglyConnected Y n` — every vertex of `G_n(Y)` reaches every other.

## Main results

* `IsLanguage.exists_outEdge`, `IsLanguage.exists_inEdge` — every vertex has in- and out-degree at
  least one.  This is [M1M2, Prop. 3.3] and it is exactly the extendability half of `IsLanguage`.
* `mem_of_reach` — **the exclusion engine**: a set of vertices closed under out-edges absorbs
  everything reachable from any of its members.  With strong connectivity this is
  `Subshift.not_properOutClosed`, [M3, Prop. 5.2]: the Rauzy graph of a strongly connected subshift
  has no proper non-empty out-closed set of vertices.
* `add_two_le_ncard_of_isRightSpecial` — **the counting lemma**: two distinct right-special words
  of length `n` force `p(n+1) ≥ p(n) + 2`.  Contrapositive `eq_of_isRightSpecial`: if the
  complexity grows by at most one at level `n`, there is at most one right-special word; with
  `exists_isRightSpecial` that is [M1M2, Prop. 3.3], exactly one when `p(n+1) = p(n) + 1`.
  `add_two_le_ncard_of_isLeftSpecial`, `eq_of_isLeftSpecial` and `exists_isLeftSpecial` are the
  left mirrors — same proofs with `edgeTgt` for `edgeSrc`, because both degree sums count
  `𝓛ₙ₊₁`.
* `isStronglyConnected_omegaLimitSubshift` — **[M1M2, Prop. 3.2]**: the Rauzy graph of an
  `ω`-limit set is strongly connected, for every `n` and with no hypothesis on the word beyond a
  finite alphabet.
* `orbit_eq_of_isPeriodicPoint` and `orbit_eq_of_pRecurrent_eq` — **[M3, Lem. 3.3]**: a strongly
  connected subshift whose complexity grows by at most one at level `p + q` contains at most one
  periodic orbit; in particular `Ω(u)` does, when `p_∞(n, u) = n + 1`.
* `Subshift.mem_iff_forall_block_mem` — **`Y` is the inverse limit of its Rauzy graphs**: a
  configuration is a point of `Y` exactly when each of its block sequences is a bi-infinite walk in
  `G_n(Y)`.

## Implementation notes

**Strong connectivity does not come from topological transitivity.**  Mathlib's
`AddAction.IsTopologicallyTransitive ℤ ↥Y` asks for *some* `m : ℤ` with `(m +ᵥ U) ∩ V` non-empty,
and a negative `m` produces a walk in the wrong direction.  The gap is real and not an artefact:
the orbit closure of `…000·0101…` ([M3, Ex. 5.3]) has a dense orbit, hence is transitive in that
sense, yet no walk in its Rauzy graph leads from `01` back to `00`.  What makes `G_n(Ω u)`
strongly connected is the **one-sidedness** of `u`: a recurrent word occurs arbitrarily late, and
beyond the last occurrence of the finitely many non-recurrent words *every* window is recurrent
(`exists_forall_isRecurrentFactor`, the `ForMathlib` form of the horizon `s_n`).

**Cycles and periodic points are not interchangeable.**  A periodic point of `Y` sweeps out a
cycle in every `G_n(Y)` (`exists_edge_of_mem_language_orbit`), but a single cycle of `G_n(Y)` only
produces a point of the level-`n` approximation of `Y`, not of `Y` itself.  The converse that does
hold is `mem_of_isPeriodicPoint_of_forall_block_mem`: a periodic configuration all of whose blocks
are legal — at *every* length — is a point of `Y`.

**Relation to `BB47/`.**  This file is the single source for the statements below; `BB47/Rauzy.lean`
and `BB47/Degrees.lean` are now thin corpus-facing layers that re-export them in the vocabulary of
Problem 10.47, and the word-level proofs they used to carry have been retired.  In particular
`reach_recurrentLanguage` replaces `BB47.exists_walk`, `mem_of_reach` replaces
`BB47.mem_of_outClosed`, and `exists_isRightSpecial`/`eq_of_isRightSpecial` (with their left
mirrors) replace the degree-sum proof of `BB47.exists_unique_rightSpecial`.  What stays on the
`BB47/` side is only what this file does not express: degrees as `Finset.card`s of fibres and the
two sum identities.  The re-proofs here are not transcriptions — reachability is
`Relation.ReflTransGen` rather than a window of `u`, and the counting lemma deletes two superfluous
edges instead of summing out-degrees over the vertex set, which is what lets it run on `Set.ncard`
for an arbitrary subshift.

## References

* [BKK26] Y. Bugeaud, H. Kaneko, D. H. Kim, arXiv:2510.17177 — Def. 2.5, the reduced Rauzy graph.
* [M1M2] `BB47/M1M2.tex` (this repository, 2026-09) — §3: Prop. 3.2 (strong connectivity),
  Prop. 3.3 (degrees), Rem. 3.4 and Ex. 3.5 (strong connectivity does not imply transitivity).
* [M3] `BB47/M3.tex` (this repository, 2026-09) — Lem. 3.2 (shape), Lem. 3.3 (at most one periodic
  orbit), Prop. 5.2 and Ex. 5.3.
* [CH73] E. M. Coven, G. A. Hedlund, *Sequences with minimal block growth*, Math. Systems Theory
  **7** (1973), 138–153.
* J. Cassaigne, F. Nicolas, in *Combinatorics, Automata and Number Theory*, CUP 2010, §4.3 — Rauzy
  graphs and the first-difference formula `p(n+1) - p(n) = Σ (deg⁺ - 1)`.
-/

namespace ForMathlib.SubwordComplexity

variable {α : Type*}

/-- **Beyond a finite horizon every window of a one-sided word is recurrent.**  The non-recurrent
length-`n` words are finitely many and each has a last occurrence, so the supremum of those
positions works.  This is the `ForMathlib` form of `BB47.horizon`, stated as the property the
Rauzy-graph proofs actually use rather than as a number. -/
theorem exists_forall_isRecurrentFactor [Finite α] (u : ℕ → α) (n : ℕ) :
    ∃ N : ℕ, ∀ i, N ≤ i → IsRecurrentFactor u n (factor u n i) := by
  classical
  have : Fintype (Fin n → α) := Fintype.ofFinite _
  have key : ∀ v : Fin n → α, ∃ N : ℕ,
      ¬ IsRecurrentFactor u n v → ∀ i, N ≤ i → factor u n i ≠ v := by
    intro v
    by_cases hv : IsRecurrentFactor u n v
    · exact ⟨0, fun h => absurd hv h⟩
    · rw [IsRecurrentFactor] at hv
      push Not at hv
      obtain ⟨N, hN⟩ := hv
      exact ⟨N, fun _ i hi => hN i hi⟩
  choose N hN using key
  refine ⟨Finset.univ.sup N, fun i hi => ?_⟩
  by_contra hcon
  exact hN (factor u n i) hcon i (le_trans (Finset.le_sup (Finset.mem_univ _)) hi) rfl

end ForMathlib.SubwordComplexity

namespace SymbolicDynamics.FullShift

open ForMathlib.SubwordComplexity

variable {α : Type*}

/-! ## Edges -/

/-- The **source** of a Rauzy edge: drop the last letter. -/
def edgeSrc {n : ℕ} (e : Fin (n + 1) → α) : Fin n → α := e ∘ Fin.castSucc

/-- The **target** of a Rauzy edge: drop the first letter. -/
def edgeTgt {n : ℕ} (e : Fin (n + 1) → α) : Fin n → α := e ∘ Fin.succ

@[simp] lemma edgeSrc_block (x : ℤ → α) (n : ℕ) (i : ℤ) :
    edgeSrc (block x (n + 1) i) = block x n i := block_comp_castSucc x n i

@[simp] lemma edgeTgt_block (x : ℤ → α) (n : ℕ) (i : ℤ) :
    edgeTgt (block x (n + 1) i) = block x n (i + 1) := block_comp_succ x n i

@[simp] lemma edgeSrc_factor (u : ℕ → α) (n i : ℕ) :
    edgeSrc (factor u (n + 1) i) = factor u n i := (factor_castSucc u n i).symm

@[simp] lemma edgeTgt_factor (u : ℕ → α) (n i : ℕ) :
    edgeTgt (factor u (n + 1) i) = factor u n (i + 1) := factor_comp_succ u n i

section Language

variable {L : ∀ n, Set (Fin n → α)} {n : ℕ}

/-- The graph is well defined: the source of an edge is a vertex. -/
lemma IsLanguage.edgeSrc_mem (hL : IsLanguage L) {e : Fin (n + 1) → α} (he : e ∈ L (n + 1)) :
    edgeSrc e ∈ L n := hL.init he

/-- …and so is its target. -/
lemma IsLanguage.edgeTgt_mem (hL : IsLanguage L) {e : Fin (n + 1) → α} (he : e ∈ L (n + 1)) :
    edgeTgt e ∈ L n := hL.tail he

/-- **[M1M2, Prop. 3.3]: every vertex has out-degree at least one.**  This *is* the
right-extendability clause of `IsLanguage`. -/
lemma IsLanguage.exists_outEdge (hL : IsLanguage L) {v : Fin n → α} (hv : v ∈ L n) :
    ∃ e ∈ L (n + 1), edgeSrc e = v := hL.extendRight hv

/-- **[M1M2, Prop. 3.3]: every vertex has in-degree at least one.** -/
lemma IsLanguage.exists_inEdge (hL : IsLanguage L) {v : Fin n → α} (hv : v ∈ L n) :
    ∃ e ∈ L (n + 1), edgeTgt e = v := hL.extendLeft hv

/-! ## Walks -/

/-- One step in the Rauzy graph `G_n(L)`: an edge from `a` to `b`. -/
def Step (L : ∀ n, Set (Fin n → α)) (n : ℕ) (a b : Fin n → α) : Prop :=
  ∃ e ∈ L (n + 1), edgeSrc e = a ∧ edgeTgt e = b

/-- Reachability in `G_n(L)`: a walk from `a` to `b`, possibly of length zero. -/
def Reach (L : ∀ n, Set (Fin n → α)) (n : ℕ) : (Fin n → α) → (Fin n → α) → Prop :=
  Relation.ReflTransGen (Step L n)

lemma Reach.refl (L : ∀ n, Set (Fin n → α)) (n : ℕ) (a : Fin n → α) : Reach L n a a :=
  Relation.ReflTransGen.refl

lemma Step.reach {a b : Fin n → α} (h : Step L n a b) : Reach L n a b :=
  Relation.ReflTransGen.single h

lemma Reach.tail {a b c : Fin n → α} (h : Reach L n a b) (hb : Step L n b c) : Reach L n a c :=
  Relation.ReflTransGen.tail h hb

lemma Reach.trans {a b c : Fin n → α} (h : Reach L n a b) (h' : Reach L n b c) : Reach L n a c :=
  Relation.ReflTransGen.trans h h'

/-- Consecutive blocks of a configuration are joined by an edge, whenever that edge is legal. -/
lemma step_block {x : ℤ → α} {i : ℤ} (he : block x (n + 1) i ∈ L (n + 1)) :
    Step L n (block x n i) (block x n (i + 1)) :=
  ⟨block x (n + 1) i, he, edgeSrc_block x n i, edgeTgt_block x n i⟩

/-- **The exclusion engine.**  A set of vertices closed under out-edges contains everything
reachable from any of its members. -/
theorem mem_of_reach {S : Set (Fin n → α)}
    (hclosed : ∀ e ∈ L (n + 1), edgeSrc e ∈ S → edgeTgt e ∈ S) {a b : Fin n → α}
    (hab : Reach L n a b) (ha : a ∈ S) : b ∈ S := by
  induction hab with
  | refl => exact ha
  | tail _ hstep ih =>
      obtain ⟨e, he, hsrc, htgt⟩ := hstep
      exact htgt ▸ hclosed e he (hsrc ▸ ih)

/-! ## Right-special words and the first difference of the complexity -/

/-- A word is **right-special** when it has two distinct extensions on the right — out-degree at
least two in the Rauzy graph. -/
def IsRightSpecial (L : ∀ n, Set (Fin n → α)) (n : ℕ) (v : Fin n → α) : Prop :=
  ∃ e₁ ∈ L (n + 1), ∃ e₂ ∈ L (n + 1), edgeSrc e₁ = v ∧ edgeSrc e₂ = v ∧ e₁ ≠ e₂

lemma IsRightSpecial.mem (hL : IsLanguage L) {v : Fin n → α} (h : IsRightSpecial L n v) :
    v ∈ L n := by
  obtain ⟨e₁, he₁, -, -, hs₁, -, -⟩ := h
  exact hs₁ ▸ hL.edgeSrc_mem he₁

/-- **A right-special word exists** as soon as the complexity strictly increases: otherwise
`edgeSrc` would be injective on `𝓛ₙ₊₁`.  With `eq_of_isRightSpecial` this is [M1M2, Prop. 3.3]:
under `p(n+1) = p(n) + 1` there is exactly one right-special word of length `n`. -/
theorem exists_isRightSpecial [Finite α] (hL : IsLanguage L)
    (hp : (L n).ncard < (L (n + 1)).ncard) : ∃ v ∈ L n, IsRightSpecial L n v := by
  by_contra hcon
  push Not at hcon
  have hinj : Set.InjOn edgeSrc (L (n + 1)) := by
    intro e₁ he₁ e₂ he₂ hs
    by_contra hne
    exact hcon (edgeSrc e₁) (hL.edgeSrc_mem he₁) ⟨e₁, he₁, e₂, he₂, rfl, hs.symm, hne⟩
  have := Set.ncard_le_ncard_of_injOn edgeSrc (fun e he => hL.edgeSrc_mem he) hinj
    (Set.toFinite _)
  omega

/-- **The counting lemma.**  Two distinct right-special words of length `n` make the complexity
jump by at least two: the map `edgeSrc : 𝓛ₙ₊₁ → 𝓛ₙ` is onto, and deleting one superfluous edge
above each of the two vertices leaves it onto.

This is the first-difference formula `p(n+1) - p(n) = Σᵥ (deg⁺(v) - 1)` in the only form the
applications need, and proving it this way avoids summing over the vertex set. -/
theorem add_two_le_ncard_of_isRightSpecial [Finite α] (hL : IsLanguage L) {v₁ v₂ : Fin n → α}
    (h₁ : IsRightSpecial L n v₁) (h₂ : IsRightSpecial L n v₂) (hne : v₁ ≠ v₂) :
    (L n).ncard + 2 ≤ (L (n + 1)).ncard := by
  classical
  obtain ⟨e₁, he₁, e₁', he₁', hs₁, hs₁', hd₁⟩ := h₁
  obtain ⟨e₂, he₂, e₂', he₂', hs₂, hs₂', hd₂⟩ := h₂
  -- the two deleted edges are distinct, since they sit above distinct vertices
  have hne' : e₁' ≠ e₂' := fun h => hne (by rw [← hs₁', h, hs₂'])
  have hsub : ({e₁', e₂'} : Set (Fin (n + 1) → α)) ⊆ L (n + 1) := by
    rintro e (rfl | rfl) <;> assumption
  set T : Set (Fin (n + 1) → α) := L (n + 1) \ {e₁', e₂'} with hT
  -- every vertex still has an out-edge in `T`
  have hcover : L n ⊆ edgeSrc '' T := by
    intro v hv
    obtain ⟨e, he, hsrc⟩ := hL.exists_outEdge hv
    by_cases h1 : e = e₁'
    · refine ⟨e₁, ⟨he₁, ?_⟩, ?_⟩
      · rintro (rfl | rfl)
        · exact hd₁ rfl
        · exact hne (by rw [← hs₁, hs₂'])
      · rw [hs₁, ← hs₁', ← h1, hsrc]
    · by_cases h2 : e = e₂'
      · refine ⟨e₂, ⟨he₂, ?_⟩, ?_⟩
        · rintro (rfl | rfl)
          · exact hne (by rw [← hs₁', hs₂])
          · exact hd₂ rfl
        · rw [hs₂, ← hs₂', ← h2, hsrc]
      · exact ⟨e, ⟨he, by rintro (rfl | rfl) <;> [exact h1 rfl; exact h2 rfl]⟩, hsrc⟩
  have hfin : (L (n + 1)).Finite := Set.toFinite _
  have h1 : (L n).ncard ≤ T.ncard :=
    le_trans (Set.ncard_le_ncard hcover (Set.toFinite _)) (Set.ncard_image_le (Set.toFinite _))
  have h2 : T.ncard + ({e₁', e₂'} : Set (Fin (n + 1) → α)).ncard = (L (n + 1)).ncard :=
    Set.ncard_sdiff_add_ncard_of_subset hsub hfin
  rw [Set.ncard_pair hne'] at h2
  omega

/-- **At most one right-special word**, when the complexity grows by at most one.  This is the
degree half of [M3, Lem. 3.2] — the part the structure theory actually consumes. -/
theorem eq_of_isRightSpecial [Finite α] (hL : IsLanguage L)
    (hp : (L (n + 1)).ncard ≤ (L n).ncard + 1) {v₁ v₂ : Fin n → α}
    (h₁ : IsRightSpecial L n v₁) (h₂ : IsRightSpecial L n v₂) : v₁ = v₂ := by
  by_contra hne
  have := add_two_le_ncard_of_isRightSpecial hL h₁ h₂ hne
  omega

/-! ## Left-special words -/

/-- A word is **left-special** when it has two distinct extensions on the left — in-degree at
least two in the Rauzy graph.  The mirror of `IsRightSpecial`, and the two are genuinely
independent: [M3, Lem. 3.2]'s shape statement is about where the unique right-special and the
unique left-special word sit relative to one another. -/
def IsLeftSpecial (L : ∀ n, Set (Fin n → α)) (n : ℕ) (v : Fin n → α) : Prop :=
  ∃ e₁ ∈ L (n + 1), ∃ e₂ ∈ L (n + 1), edgeTgt e₁ = v ∧ edgeTgt e₂ = v ∧ e₁ ≠ e₂

lemma IsLeftSpecial.mem (hL : IsLanguage L) {v : Fin n → α} (h : IsLeftSpecial L n v) :
    v ∈ L n := by
  obtain ⟨e₁, he₁, -, -, ht₁, -, -⟩ := h
  exact ht₁ ▸ hL.edgeTgt_mem he₁

/-- **A left-special word exists** as soon as the complexity strictly increases: otherwise
`edgeTgt` would be injective on `𝓛ₙ₊₁`.  With `eq_of_isLeftSpecial` this is the left half of
[M1M2, Prop. 3.3]. -/
theorem exists_isLeftSpecial [Finite α] (hL : IsLanguage L)
    (hp : (L n).ncard < (L (n + 1)).ncard) : ∃ v ∈ L n, IsLeftSpecial L n v := by
  by_contra hcon
  push Not at hcon
  have hinj : Set.InjOn edgeTgt (L (n + 1)) := by
    intro e₁ he₁ e₂ he₂ ht
    by_contra hne
    exact hcon (edgeTgt e₁) (hL.edgeTgt_mem he₁) ⟨e₁, he₁, e₂, he₂, rfl, ht.symm, hne⟩
  have := Set.ncard_le_ncard_of_injOn edgeTgt (fun e he => hL.edgeTgt_mem he) hinj
    (Set.toFinite _)
  omega

/-- **The counting lemma, left form.**  Two distinct left-special words of length `n` make the
complexity jump by at least two.  Same proof as `add_two_le_ncard_of_isRightSpecial` with
`edgeTgt` in place of `edgeSrc`: the two counts `Σᵥ deg⁺(v)` and `Σᵥ deg⁻(v)` are both
`#𝓛ₙ₊₁`, so the first-difference formula holds on either side of the graph. -/
theorem add_two_le_ncard_of_isLeftSpecial [Finite α] (hL : IsLanguage L) {v₁ v₂ : Fin n → α}
    (h₁ : IsLeftSpecial L n v₁) (h₂ : IsLeftSpecial L n v₂) (hne : v₁ ≠ v₂) :
    (L n).ncard + 2 ≤ (L (n + 1)).ncard := by
  classical
  obtain ⟨e₁, he₁, e₁', he₁', ht₁, ht₁', hd₁⟩ := h₁
  obtain ⟨e₂, he₂, e₂', he₂', ht₂, ht₂', hd₂⟩ := h₂
  have hne' : e₁' ≠ e₂' := fun h => hne (by rw [← ht₁', h, ht₂'])
  have hsub : ({e₁', e₂'} : Set (Fin (n + 1) → α)) ⊆ L (n + 1) := by
    rintro e (rfl | rfl) <;> assumption
  set T : Set (Fin (n + 1) → α) := L (n + 1) \ {e₁', e₂'} with hT
  have hcover : L n ⊆ edgeTgt '' T := by
    intro v hv
    obtain ⟨e, he, htgt⟩ := hL.exists_inEdge hv
    by_cases h1 : e = e₁'
    · refine ⟨e₁, ⟨he₁, ?_⟩, ?_⟩
      · rintro (rfl | rfl)
        · exact hd₁ rfl
        · exact hne (by rw [← ht₁, ht₂'])
      · rw [ht₁, ← ht₁', ← h1, htgt]
    · by_cases h2 : e = e₂'
      · refine ⟨e₂, ⟨he₂, ?_⟩, ?_⟩
        · rintro (rfl | rfl)
          · exact hne (by rw [← ht₁', ht₂])
          · exact hd₂ rfl
        · rw [ht₂, ← ht₂', ← h2, htgt]
      · exact ⟨e, ⟨he, by rintro (rfl | rfl) <;> [exact h1 rfl; exact h2 rfl]⟩, htgt⟩
  have hfin : (L (n + 1)).Finite := Set.toFinite _
  have h1 : (L n).ncard ≤ T.ncard :=
    le_trans (Set.ncard_le_ncard hcover (Set.toFinite _)) (Set.ncard_image_le (Set.toFinite _))
  have h2 : T.ncard + ({e₁', e₂'} : Set (Fin (n + 1) → α)).ncard = (L (n + 1)).ncard :=
    Set.ncard_sdiff_add_ncard_of_subset hsub hfin
  rw [Set.ncard_pair hne'] at h2
  omega

/-- **At most one left-special word**, when the complexity grows by at most one. -/
theorem eq_of_isLeftSpecial [Finite α] (hL : IsLanguage L)
    (hp : (L (n + 1)).ncard ≤ (L n).ncard + 1) {v₁ v₂ : Fin n → α}
    (h₁ : IsLeftSpecial L n v₁) (h₂ : IsLeftSpecial L n v₂) : v₁ = v₂ := by
  by_contra hne
  have := add_two_le_ncard_of_isLeftSpecial hL h₁ h₂ hne
  omega

end Language

/-! ## The Rauzy graph of a subshift -/

section Subshift

variable [TopologicalSpace α] {Y : Subshift α ℤ}

/-- `G_n(Y)` is **strongly connected**: every vertex reaches every vertex. -/
def Subshift.IsStronglyConnected (Y : Subshift α ℤ) (n : ℕ) : Prop :=
  ∀ a ∈ Y.language n, ∀ b ∈ Y.language n, Reach Y.language n a b

/-- **[M3, Prop. 5.2].**  The Rauzy graph of a strongly connected subshift has no proper non-empty
set of vertices closed under out-edges. -/
theorem Subshift.not_properOutClosed {n : ℕ} (hsc : Y.IsStronglyConnected n)
    {S : Set (Fin n → α)}
    (hclosed : ∀ e ∈ Y.language (n + 1), edgeSrc e ∈ S → edgeTgt e ∈ S)
    {a : Fin n → α} (ha : a ∈ Y.language n) (haS : a ∈ S)
    {b : Fin n → α} (hb : b ∈ Y.language n) (hbS : b ∉ S) : False :=
  hbS (mem_of_reach hclosed (hsc a ha b hb) haS)

/-- **`Y` is the inverse limit of its Rauzy graphs.**  A configuration belongs to `Y` exactly when,
at every level `n`, its blocks are vertices of `G_n(Y)`; they are then automatically joined by the
edges `block x (n+1) i`, so `x` *is* a bi-infinite walk in every `G_n(Y)`, compatibly in `n`.

This is the description `plans/plan-1047.html` §2.2 takes as the definition of `Ω`; here it is a
theorem, and after `Duality.lean` a cheap one. -/
theorem Subshift.mem_iff_forall_block_mem (Y : Subshift α ℤ) (x : ℤ → α) :
    x ∈ Y ↔ ∀ (n : ℕ) (i : ℤ), block x n i ∈ Y.language n :=
  ⟨fun hx n i => Subshift.block_mem_language hx n i,
    fun h => mem_of_forall_block_mem_language Y h⟩

/-- The walk half of the previous statement: consecutive blocks of a point are joined by an edge. -/
lemma Subshift.step_block_of_mem {x : ℤ → α} (hx : x ∈ Y) (n : ℕ) (i : ℤ) :
    Step Y.language n (block x n i) (block x n (i + 1)) :=
  step_block (Subshift.block_mem_language hx (n + 1) i)

/-! ## Periodic orbits are cycles -/

omit [TopologicalSpace α] in
/-- Each vertex swept out by a periodic point has an out-edge that stays on the orbit: the cycle
the orbit traces in `G_n(Y)`. -/
lemma exists_edge_of_mem_language_orbit (x : ℤ → α) (n : ℕ) {v : Fin n → α}
    (hv : v ∈ language (orbit x) n) :
    ∃ e ∈ language (orbit x) (n + 1), edgeSrc e = v ∧ edgeTgt e ∈ language (orbit x) n := by
  rw [language_orbit] at hv
  obtain ⟨i, rfl⟩ := hv
  refine ⟨block x (n + 1) i, ?_, edgeSrc_block x n i, ?_⟩
  · rw [language_orbit]; exact ⟨i, rfl⟩
  · rw [edgeTgt_block, language_orbit]; exact ⟨i + 1, rfl⟩

/-- **Away from the right-special words, a periodic orbit is out-closed.**  A vertex of the orbit
already has one out-edge along the orbit; if it is not right-special that edge is its only one, so
no edge of `G_n(Y)` leaves the orbit. -/
lemma outClosed_language_orbit {x : ℤ → α} (hx : x ∈ Y) {n : ℕ}
    (hns : ∀ v ∈ language (orbit x) n, ¬ IsRightSpecial Y.language n v) :
    ∀ e ∈ Y.language (n + 1), edgeSrc e ∈ language (orbit x) n →
      edgeTgt e ∈ language (orbit x) n := by
  intro e he hsrc
  obtain ⟨e₀, he₀, hsrc₀, htgt₀⟩ := exists_edge_of_mem_language_orbit x n hsrc
  have he₀Y : e₀ ∈ Y.language (n + 1) := language_orbit_subset hx (n + 1) he₀
  by_cases h : e = e₀
  · rw [h]; exact htgt₀
  · exact absurd ⟨e, he, e₀, he₀Y, rfl, hsrc₀, fun hcon => h hcon⟩ (hns _ hsrc)

/-- The converse direction that does hold: a periodic configuration all of whose blocks are legal —
at *every* length — is a point of `Y`.  Periodicity is what makes the hypothesis finite at each
level: only the positions `0, …, p-1` need to be checked. -/
theorem mem_of_isPeriodicPoint_of_forall_block_mem {x : ℤ → α} {p : ℕ} (hp : 0 < p)
    (hxp : IsPeriodicPoint x p) (h : ∀ (n : ℕ) (i : ℕ), i < p → block x n i ∈ Y.language n) :
    x ∈ Y := by
  refine mem_of_forall_block_mem_language Y fun n i => ?_
  have hp' : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp
  have h1 : 0 ≤ i % (p : ℤ) := Int.emod_nonneg i (by omega)
  have h2 : i % (p : ℤ) < (p : ℤ) := Int.emod_lt_of_pos i hp'
  have hb : block x n i = block x n (i % (p : ℤ)) :=
    hxp.block_eq n (Int.emod_add_mul_ediv i (p : ℤ)).symm
  rw [hb, ← Int.toNat_of_nonneg h1]
  exact h n _ (by omega)

/-! ## At most one periodic orbit -/

variable [Finite α]

/-- **[M3, Lem. 3.3].**  In a strongly connected subshift whose complexity grows by at most one at
level `p + q`, two periodic points of periods `p` and `q` lie on the same orbit.

The proof is the Fine–Wilf separation of `Periodic.lean` against the exclusion engine.  Distinct
orbits have disjoint languages at level `p + q`; at most one word of that length is right-special,
so it misses one of the two orbits entirely; that orbit's language is then a non-empty out-closed
set of vertices missing the other orbit's language, which strong connectivity forbids.

M3 argues instead through the *shape* of `G_n(Ω)` — two vertex-disjoint simple cycles in a graph
that has exactly two simple cycles, and they meet.  The route here needs only the degree half of
that lemma, and no case analysis on whether the right-special and left-special vertices coincide. -/
theorem orbit_eq_of_isPeriodicPoint {x y : ℤ → α} {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hxY : x ∈ Y) (hyY : y ∈ Y) (hx : IsPeriodicPoint x p) (hy : IsPeriodicPoint y q)
    (hsc : Y.IsStronglyConnected (p + q))
    (hcount : (Y.language (p + q + 1)).ncard ≤ (Y.language (p + q)).ncard + 1) :
    orbit x = orbit y := by
  by_contra hne
  have hdis := disjoint_language_of_orbit_ne hp hq hx hy hne
  have hL : IsLanguage Y.language := Y.isLanguage ⟨x, hxY⟩
  have hax : block x (p + q) 0 ∈ language (orbit x) (p + q) := by
    rw [language_orbit]; exact ⟨0, rfl⟩
  have hby : block y (p + q) 0 ∈ language (orbit y) (p + q) := by
    rw [language_orbit]; exact ⟨0, rfl⟩
  -- at most one word of length `p + q` is right-special, so it misses one of the two orbits
  by_cases hsx : ∃ v ∈ language (orbit x) (p + q), IsRightSpecial Y.language (p + q) v
  · -- the right-special word lies on the orbit of `x`, so the orbit of `y` is out-closed
    obtain ⟨v₁, hv₁, hrs₁⟩ := hsx
    have hns : ∀ v ∈ language (orbit y) (p + q), ¬ IsRightSpecial Y.language (p + q) v := by
      intro v hv hrs
      exact Set.disjoint_left.mp hdis hv₁ (eq_of_isRightSpecial hL hcount hrs₁ hrs ▸ hv)
    exact Subshift.not_properOutClosed hsc (outClosed_language_orbit hyY hns)
      (language_orbit_subset hyY _ hby) hby
      (language_orbit_subset hxY _ hax) (Set.disjoint_left.mp hdis hax)
  · -- no vertex of the orbit of `x` is right-special, so that orbit is out-closed
    push Not at hsx
    exact Subshift.not_properOutClosed hsc (outClosed_language_orbit hxY hsx)
      (language_orbit_subset hxY _ hax) hax
      (language_orbit_subset hyY _ hby) (Set.disjoint_right.mp hdis hby)

end Subshift

/-! ## The Rauzy graph of an `ω`-limit set -/

section OmegaLimit

variable [TopologicalSpace α] [DiscreteTopology α] [Finite α]

omit [TopologicalSpace α] [DiscreteTopology α] in
/-- **[M1M2, Prop. 3.2]: the Rauzy graph of an `ω`-limit set is strongly connected.**  There is no
hypothesis on `u` beyond a finite alphabet.  `a` occurs beyond the horizon of level `n + 1`, `b`
occurs later still, and the stretch of `u` between the two occurrences is the walk: past the
horizon every window is recurrent, so every block it passes through is a vertex and every block it
crosses is an edge. -/
theorem reach_recurrentLanguage (u : ℕ → α) (n : ℕ) {a b : Fin n → α}
    (ha : a ∈ recurrentLanguage u n) (hb : b ∈ recurrentLanguage u n) :
    Reach (recurrentLanguage u) n a b := by
  obtain ⟨N, hN⟩ := exists_forall_isRecurrentFactor u (n + 1)
  obtain ⟨i, hi, hfi⟩ := ha N
  obtain ⟨j, hj, hfj⟩ := hb i
  have walk : ∀ d : ℕ, Reach (recurrentLanguage u) n (factor u n i) (factor u n (i + d)) := by
    intro d
    induction d with
    | zero => exact Reach.refl _ _ _
    | succ k ih =>
        exact ih.tail ⟨factor u (n + 1) (i + k), hN (i + k) (by omega), edgeSrc_factor u n (i + k),
          by rw [edgeTgt_factor, Nat.add_assoc]⟩
  have hw := walk (j - i)
  rwa [show i + (j - i) = j by omega, hfi, hfj] at hw

lemma language_omegaLimitSubshift_eq (u : ℕ → α) :
    (omegaLimitSubshift u).language = recurrentLanguage u :=
  funext (language_omegaLimitSubshift u)

theorem isStronglyConnected_omegaLimitSubshift (u : ℕ → α) (n : ℕ) :
    (omegaLimitSubshift u).IsStronglyConnected n := by
  intro a ha b hb
  rw [language_omegaLimitSubshift_eq] at ha hb ⊢
  exact reach_recurrentLanguage u n ha hb

/-- **[M3, Lem. 3.3] for `ω`-limit sets.**  If `p_∞(·, u)` grows by at most one at level `p + q`,
then `Ω(u)` contains at most one periodic orbit. -/
theorem orbit_eq_of_pRecurrent {u : ℕ → α} {x y : ℤ → α} {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hxY : x ∈ omegaLimitSubshift u) (hyY : y ∈ omegaLimitSubshift u)
    (hx : IsPeriodicPoint x p) (hy : IsPeriodicPoint y q)
    (hcount : pRecurrent u (p + q + 1) ≤ pRecurrent u (p + q) + 1) :
    orbit x = orbit y := by
  refine orbit_eq_of_isPeriodicPoint hp hq hxY hyY hx hy
    (isStronglyConnected_omegaLimitSubshift u (p + q)) ?_
  rw [language_omegaLimitSubshift_eq]
  exact hcount

/-- **[M3, Lem. 3.3] under the standing hypothesis (H).**  If `p_∞(n, u) = n + 1` for all `n`, the
`ω`-limit set of `u` contains at most one periodic orbit. -/
theorem orbit_eq_of_pRecurrent_eq {u : ℕ → α} (hu : ∀ n : ℕ, pRecurrent u n = n + 1)
    {x y : ℤ → α} {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hxY : x ∈ omegaLimitSubshift u) (hyY : y ∈ omegaLimitSubshift u)
    (hx : IsPeriodicPoint x p) (hy : IsPeriodicPoint y q) : orbit x = orbit y := by
  refine orbit_eq_of_pRecurrent hp hq hxY hyY hx hy ?_
  rw [hu, hu]

end OmegaLimit

end SymbolicDynamics.FullShift
