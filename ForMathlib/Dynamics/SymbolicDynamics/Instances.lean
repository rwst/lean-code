/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Data.SetLike.Basic
import Mathlib.Dynamics.Minimal
import Mathlib.Dynamics.SymbolicDynamics.Basic
import Mathlib.Dynamics.Transitive
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Topology.Constructions

/-!
# Order and action instances for subshifts

`Mathlib.Dynamics.SymbolicDynamics.Basic` introduces the shift action on the full shift `G → A`
and bundles a **subshift** as a structure `Subshift A G` carrying a `carrier : Set (G → A)`
together with proofs that it is closed and shift-invariant.  That file declares *no instances at
all*, so a `Subshift` is a bare structure: one cannot write `x ∈ Y`, `Y ≤ Z` or `⨅ i, Y i`, and —
more consequentially — the shift does not act on `Y`, so none of the general topological dynamics
in `Mathlib.Dynamics.Minimal` and `Mathlib.Dynamics.Transitive` can see a subshift.

This file supplies exactly those instances.  It contains no new mathematics; every proof is one
step from the corresponding fact about closed sets.

## Main definitions and results

* `SetLike (Subshift A G) (G → A)` and `PartialOrder (Subshift A G)` (by `.ofSetLike`) —
  membership, inclusion order (`le_def`) and extensionality.
* `CompleteLattice (Subshift A G)` — arbitrary intersections of subshifts are subshifts, and
  `sInf` is the intersection (`coe_sInf`, `mem_sInf`).  Two facts special to subshifts, both false
  for most subobject lattices: `⊥` is the *empty* subshift (`coe_bot`), and the join is the plain
  **union** (`coe_sup`) — no closure operation is needed, because a union of two closed
  shift-invariant sets is already closed and shift-invariant.
* `union`, `inter`, `empty` — the three explicit constructors behind `coe_sup`, `coe_inf` and
  `coe_bot`, kept as definitions because a reader wanting the union of two subshifts should not
  have to know that it happens to be the lattice join.
* `AddAction G (G → A)` and `AddAction G Y` for commutative `G`, with `ContinuousConstVAdd` —
  both `scoped`, see the implementation note.  With them in scope, `AddAction.IsMinimal G Y` and
  `AddAction.IsTopologicallyTransitive G Y` are the correct notions of a minimal and of a
  topologically transitive subshift, and Mathlib's lemmas about them apply verbatim; the two
  sample corollaries `dense_orbit_of_isMinimal` and `eq_bot_or_eq_of_isMinimal` are proved here to
  witness that.

## Implementation notes

* The action instances are `scoped`.  The reason is a genuine diamond: `G → A` is `∀ _ : G, A`,
  so whenever `A` itself carries a `G`-action, `Pi.instAddAction` provides a *pointwise* action of
  `G` on `G → A`, which is not the shift.  Downstream files should `open scoped
  SymbolicDynamics.FullShift`.
* Commutativity of `G` is needed for the action axiom and only for it: `shift_add` composes the
  two shifts in the opposite order, `shift (g₁ + g₂) = shift g₂ ∘ shift g₁`.  For the group of
  interest, `G = ℤ`, this costs nothing.
* Nothing here assumes the alphabet finite or discrete.

## References

* Mathlib, `Mathlib/Dynamics/SymbolicDynamics/Basic.lean` (S. Gangloff, 2025) — the structure
  this file equips.
* M. Lothaire, *Algebraic Combinatorics on Words*, CUP 2002, Ch. 1 — subshifts as closed
  shift-invariant sets.
* B. P. Kitchens, *Symbolic Dynamics*, Springer 1998, Ch. 1.
-/

namespace SymbolicDynamics.FullShift

variable {A G : Type*} [TopologicalSpace A] [AddMonoid G]

/-! ## Membership -/

instance : SetLike (Subshift A G) (G → A) where
  coe Y := Y.carrier
  coe_injective Y Z h := by
    cases Y
    cases Z
    subst h
    rfl

@[simp] lemma mem_carrier {Y : Subshift A G} {x : G → A} : x ∈ Y.carrier ↔ x ∈ Y := Iff.rfl

@[simp] lemma coe_carrier (Y : Subshift A G) : (Y.carrier : Set (G → A)) = Y := rfl

@[ext] lemma subshift_ext {Y Z : Subshift A G} (h : ∀ x, x ∈ Y ↔ x ∈ Z) : Y = Z := SetLike.ext h

/-- A subshift is a closed set. -/
lemma isClosed_coe (Y : Subshift A G) : IsClosed (Y : Set (G → A)) := Y.isClosed

/-- A subshift is shift-invariant, in membership form. -/
lemma shift_mem (Y : Subshift A G) (g : G) {x : G → A} (hx : x ∈ Y) : shift g x ∈ Y :=
  Y.mapsTo g hx

/-- The order on subshifts is inclusion. -/
instance : PartialOrder (Subshift A G) := .ofSetLike (Subshift A G) (G → A)

lemma le_def {Y Z : Subshift A G} : Y ≤ Z ↔ ∀ ⦃x⦄, x ∈ Y → x ∈ Z := SetLike.le_def

/-! ## The complete lattice of subshifts -/

instance : InfSet (Subshift A G) where
  sInf S :=
    { carrier := ⋂ Y ∈ S, (Y : Set (G → A))
      isClosed := isClosed_biInter fun Y _ => Y.isClosed
      mapsTo := by
        intro g x hx
        simp only [Set.mem_iInter] at hx ⊢
        exact fun Y hY => shift_mem Y g (hx Y hY) }

@[simp] lemma coe_sInf (S : Set (Subshift A G)) :
    ((sInf S : Subshift A G) : Set (G → A)) = ⋂ Y ∈ S, (Y : Set (G → A)) := rfl

@[simp] lemma mem_sInf {S : Set (Subshift A G)} {x : G → A} :
    x ∈ sInf S ↔ ∀ Y ∈ S, x ∈ Y := by
  change x ∈ ⋂ Y ∈ S, (Y : Set (G → A)) ↔ _
  simp

instance : CompleteLattice (Subshift A G) :=
  completeLatticeOfInf _ fun S => by
    constructor
    · intro Y hY x hx
      exact mem_sInf.mp hx Y hY
    · intro Z hZ x hx
      exact mem_sInf.mpr fun Y hY => hZ hY hx

/-- The union of two subshifts is a subshift: a union of two closed sets is closed, and
invariance is inherited.  It is the join of the lattice, see `coe_sup`. -/
def union (Y Z : Subshift A G) : Subshift A G where
  carrier := (Y : Set (G → A)) ∪ (Z : Set (G → A))
  isClosed := Y.isClosed.union Z.isClosed
  mapsTo := by
    intro g x hx
    exact hx.imp (fun h => shift_mem Y g h) (fun h => shift_mem Z g h)

@[simp] lemma mem_union {Y Z : Subshift A G} {x : G → A} :
    x ∈ union Y Z ↔ x ∈ Y ∨ x ∈ Z := Iff.rfl

/-- The intersection of two subshifts is a subshift.  It is the meet of the lattice,
see `coe_inf`. -/
def inter (Y Z : Subshift A G) : Subshift A G where
  carrier := (Y : Set (G → A)) ∩ (Z : Set (G → A))
  isClosed := Y.isClosed.inter Z.isClosed
  mapsTo := by
    intro g x hx
    exact ⟨shift_mem Y g hx.1, shift_mem Z g hx.2⟩

@[simp] lemma mem_inter {Y Z : Subshift A G} {x : G → A} :
    x ∈ inter Y Z ↔ x ∈ Y ∧ x ∈ Z := Iff.rfl

/-- The empty set is a subshift; it is the bottom of the lattice, see `coe_bot`. -/
def empty : Subshift A G where
  carrier := ∅
  isClosed := isClosed_empty
  mapsTo := by intro _ _ h; exact h.elim

@[simp] lemma coe_top : ((⊤ : Subshift A G) : Set (G → A)) = Set.univ :=
  Set.eq_univ_of_forall fun x => (le_top : fullShift A G ≤ ⊤) (Set.mem_univ x)

/-- **The bottom subshift is empty.**  Unlike most subobject lattices, the lattice of subshifts
has an empty least element: the empty set is closed and vacuously shift-invariant. -/
@[simp] lemma coe_bot : ((⊥ : Subshift A G) : Set (G → A)) = ∅ :=
  Set.eq_empty_of_subset_empty fun _ hx => (bot_le : (⊥ : Subshift A G) ≤ empty) hx

@[simp] lemma mem_top {x : G → A} : x ∈ (⊤ : Subshift A G) := by
  have hx : x ∈ ((⊤ : Subshift A G) : Set (G → A)) := by rw [coe_top]; trivial
  exact hx

@[simp] lemma not_mem_bot {x : G → A} : x ∉ (⊥ : Subshift A G) := by
  intro hx
  have hx' : x ∈ ((⊥ : Subshift A G) : Set (G → A)) := hx
  rw [coe_bot] at hx'
  exact hx'

/-- **The join of two subshifts is their union** — no closure operation is needed.  This is
special to subshifts and is what makes a decomposition such as `Orb(x) ⊔ P` (an orbit together
with a periodic orbit, the shape of the skew branch of [CH73]) an honest lattice statement. -/
@[simp] lemma coe_sup (Y Z : Subshift A G) :
    ((Y ⊔ Z : Subshift A G) : Set (G → A)) = (Y : Set (G → A)) ∪ (Z : Set (G → A)) := by
  refine Set.Subset.antisymm (fun x hx => ?_) ?_
  · exact (sup_le (show Y ≤ union Y Z from fun _ h => Or.inl h)
      (show Z ≤ union Y Z from fun _ h => Or.inr h)) hx
  · rintro x (h | h)
    · exact (le_sup_left : Y ≤ Y ⊔ Z) h
    · exact (le_sup_right : Z ≤ Y ⊔ Z) h

@[simp] lemma coe_inf (Y Z : Subshift A G) :
    ((Y ⊓ Z : Subshift A G) : Set (G → A)) = (Y : Set (G → A)) ∩ (Z : Set (G → A)) := by
  refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
  · exact ⟨(inf_le_left : Y ⊓ Z ≤ Y) hx, (inf_le_right : Y ⊓ Z ≤ Z) hx⟩
  · exact (le_inf (show inter Y Z ≤ Y from fun _ h => h.1)
      (show inter Y Z ≤ Z from fun _ h => h.2)) hx

/-! ## The shift as an action

For a commutative monoid `G` the shift is an honest `AddAction`, on the full shift and on every
subshift.  Both instances are `scoped`; see the implementation notes. -/

section Action

variable {A G : Type*} [TopologicalSpace A] [AddCommMonoid G]

/-- The shift action of `G` on the full shift `G → A`.  `scoped`, to avoid clashing with the
pointwise action `Pi.instAddAction` when `A` itself is a `G`-set. -/
scoped instance instAddActionFullShift : AddAction G (G → A) where
  vadd := shift
  zero_vadd := shift_zero
  add_vadd g₁ g₂ x := by
    show shift (g₁ + g₂) x = shift g₁ (shift g₂ x)
    rw [add_comm, shift_add]

omit [TopologicalSpace A] in
@[simp] lemma vadd_eq_shift (g : G) (x : G → A) : g +ᵥ x = shift g x := rfl

scoped instance : ContinuousConstVAdd G (G → A) where
  continuous_const_vadd g := continuous_shift g

/-- The shift action of `G` on a subshift `Y`, by restriction. -/
scoped instance instAddActionSubshift (Y : Subshift A G) : AddAction G Y where
  vadd g x := ⟨shift g x, shift_mem Y g x.2⟩
  zero_vadd x := Subtype.ext (shift_zero (x : G → A))
  add_vadd g₁ g₂ x := Subtype.ext (by
    show shift (g₁ + g₂) (x : G → A) = shift g₁ (shift g₂ (x : G → A))
    rw [add_comm, shift_add])

@[simp] lemma coe_vadd_subshift (Y : Subshift A G) (g : G) (x : Y) :
    ((g +ᵥ x : Y) : G → A) = shift g (x : G → A) := rfl

scoped instance (Y : Subshift A G) : ContinuousConstVAdd G Y where
  continuous_const_vadd g :=
    Continuous.subtype_mk ((continuous_shift g).comp continuous_subtype_val) _

/-! ### Payoff: the general theory now applies

The two corollaries below are used nowhere in this file; they are here to witness that
`AddAction.IsMinimal` and the lemmas around it typecheck on a subshift, which is the entire point
of the instances above. -/

/-- On a minimal subshift every orbit is dense. -/
theorem dense_orbit_of_isMinimal (Y : Subshift A G) [AddAction.IsMinimal G Y] (x : Y) :
    Dense (AddAction.orbit G x) :=
  AddAction.dense_orbit G x

/-- A minimal subshift has no proper non-empty sub-subshift.  This is the form in which
minimality is used in the analysis of `ω`-limit subshifts ([M3, Lem. 3.3] and the Coven–Hedlund
branch count). -/
theorem eq_bot_or_eq_of_isMinimal {Y Z : Subshift A G} [AddAction.IsMinimal G Y] (hZY : Z ≤ Y) :
    Z = ⊥ ∨ Z = Y := by
  rcases Set.eq_empty_or_nonempty (Z : Set (G → A)) with hZ | hZ
  · exact Or.inl (SetLike.ext' (by rw [coe_bot]; exact hZ))
  refine Or.inr (le_antisymm hZY fun x hx => ?_)
  -- the trace of `Z` on `Y` is closed, shift-invariant and non-empty, hence dense, hence all of `Y`
  set S : Set Y := Subtype.val ⁻¹' (Z : Set (G → A)) with hSdef
  have hSclosed : IsClosed S := Z.isClosed.preimage continuous_subtype_val
  obtain ⟨z, hz⟩ := hZ
  have hzS : (⟨z, hZY hz⟩ : Y) ∈ S := hz
  have hdense : Dense S := by
    refine (AddAction.dense_orbit G (⟨z, hZY hz⟩ : Y)).mono ?_
    rintro _ ⟨g, rfl⟩
    exact shift_mem Z g hz
  have hSuniv : S = Set.univ := by rw [← hSclosed.closure_eq, hdense.closure_eq]
  have hmem : (⟨x, hx⟩ : Y) ∈ S := by rw [hSuniv]; exact Set.mem_univ _
  exact hmem

end Action

end SymbolicDynamics.FullShift
