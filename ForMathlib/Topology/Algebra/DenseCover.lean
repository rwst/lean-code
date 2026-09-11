/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Covering a quotient group; covering by a dense set

Two elementary lemmas about when a subset of an abelian group covers everything.

* `QuotientAddGroup.image_mk_eq_univ_iff` — the image of `S ⊆ G` in `G ⧸ N` is all of `G ⧸ N`
  if and only if `S + N` is all of `G`.  Purely algebraic: no topology is involved, and `N`
  need not be discrete or closed.
* `add_dense_eq_univ` — in a topological additive group, a set with non-empty interior plus a
  dense set is everything.  The proof is the one-line "the open set `x - interior B` meets the
  dense set", which is why no local compactness, metrisability or measure is needed.

Together they say that a set covers a quotient group as soon as its *interior* is non-empty
and the subgroup one quotients by is dense — a coverage criterion that is insensitive to how
small the set is.

Only the additive versions are stated; that is the intended use.
-/

open Pointwise Set

namespace QuotientAddGroup

/-- **The image of `S` in `G ⧸ N` is everything iff `S + N` is everything.**  Both sides say
that every `z : G` differs from a point of `S` by an element of `N`. -/
theorem image_mk_eq_univ_iff {G : Type*} [AddCommGroup G] (N : AddSubgroup G) (S : Set G) :
    ((QuotientAddGroup.mk '' S : Set (G ⧸ N)) = Set.univ) ↔ S + (N : Set G) = Set.univ := by
  constructor
  · intro h
    refine Set.eq_univ_of_forall fun z => ?_
    have hz : (QuotientAddGroup.mk z : G ⧸ N) ∈ (QuotientAddGroup.mk '' S : Set (G ⧸ N)) := by
      rw [h]; trivial
    obtain ⟨s, hs, hsz⟩ := hz
    have hmem : s - z ∈ N := QuotientAddGroup.eq_iff_sub_mem.mp hsz
    exact Set.mem_add.mpr ⟨s, hs, z - s, by simpa using neg_mem hmem, by abel⟩
  · intro h
    refine Set.eq_univ_of_forall fun q => ?_
    obtain ⟨z, rfl⟩ := Quot.mk_surjective q
    obtain ⟨s, hs, n, hn, hsum⟩ := Set.mem_add.mp (h ▸ Set.mem_univ z)
    refine ⟨s, hs, ?_⟩
    exact QuotientAddGroup.eq_iff_sub_mem.mpr (by simpa [← hsum] using neg_mem hn)

end QuotientAddGroup

/-- **A set with non-empty interior plus a dense set is everything.**  Given `x`, the open set
`x - interior B` is non-empty and therefore meets `S`. -/
theorem add_dense_eq_univ {E : Type*} [AddCommGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] {B S : Set E} (hB : (interior B).Nonempty) (hS : Dense S) :
    B + S = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨s, hs, hmem⟩ :=
    hS.exists_mem_open (isOpenMap_sub_left x _ isOpen_interior) (hB.image _)
  obtain ⟨b, hb, hbs⟩ := hmem
  simp only at hbs
  refine Set.mem_add.mpr ⟨b, interior_subset hb, s, hs, ?_⟩
  rw [← hbs]
  abel
