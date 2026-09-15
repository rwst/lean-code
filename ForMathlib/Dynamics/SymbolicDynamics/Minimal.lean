/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import ForMathlib.Dynamics.SymbolicDynamics.Complexity
import Mathlib.Order.Zorn
import Mathlib.Tactic.Common

/-!
# Minimal subshifts and uniformly recurrent languages

A subshift is **minimal** when it has no non-empty proper sub-subshift.  This file proves the
three standard descriptions of that condition and the theorem that makes it useful:

* every non-empty subshift over a finite alphabet **contains** a minimal one, and
* a subshift is minimal exactly when its language is **uniformly recurrent** — every legal word
  occurs in every legal word of some bounded length, equivalently occurs in every point of the
  subshift with bounded gaps.

Neither notion exists anywhere in Mathlib: `Mathlib.Dynamics.Minimal` defines a minimal *action*
(every orbit dense) but has no minimal-subsystem theorem, and `UniformlyRecurrent` appears
nowhere.  The first gap is closed here for subshifts by Zorn's lemma; the second is closed by a
definition, which — as the plan warned — is ours to get right, so both the word form and the
bounded-gap form are given and proved equivalent.

## Main definitions

* `SymbolicDynamics.FullShift.subword` — the window of a *finite* word, the counterpart of `block`
  for statements that mention no configuration at all.
* `SymbolicDynamics.FullShift.IsUniformlyRecurrent` — a family of languages is uniformly recurrent
  when every word of it occurs in every sufficiently long word of it.  This is a property of the
  language alone.
* `Subshift.IsMinimal` — non-empty, and every non-empty sub-subshift is the whole thing.
* `Subshift.OccursEverywhere`, `Subshift.HasBoundedGaps` — every legal word occurs in every point,
  respectively occurs in every window of some bounded length of every point.

## Main results

* `Subshift.isMinimal_iff_forall_orbitClosure_eq` — minimal ⟺ every orbit is dense, in the form
  `orbitClosure x = Y`.  No hypothesis on the alphabet.
* `Subshift.isMinimal_iff_addAction` — …and that is Mathlib's `AddAction.IsMinimal ℤ Y`, through
  the action instances of `Instances.lean`.  This is the payoff those instances were built for.
* `Subshift.exists_isMinimal_le` — **every non-empty subshift over a finite alphabet contains a
  minimal subshift.**  Zorn's lemma over the sub-subshifts ordered by `⊇`; the chain step is
  Cantor's intersection theorem for a directed family of non-empty compact closed sets.
* `Subshift.isMinimal_iff_occursEverywhere` — minimal ⟺ every legal word occurs in *every* point.
  This needs no compactness: it is the statement that the language determines the subshift, read
  twice.
* `Subshift.isMinimal_iff_isUniformlyRecurrent`, `Subshift.isMinimal_iff_hasBoundedGaps` —
  **minimal ⟺ uniformly recurrent.**  Only the step from "occurs somewhere in every point" to
  "occurs within a bounded window" costs anything, and what it costs is compactness of the
  subshift: the sets of points seeing the word within distance `N` of the origin form a directed
  open cover.
* `isUniformlyRecurrent_iff_isMinimal_ofLanguage` — the same equivalence read on the language
  side of the duality: a factorial extendable family is uniformly recurrent exactly when the
  subshift it defines is minimal.
* `Subshift.IsMinimal.exists_isPeriodicPoint_of_finite` — a finite minimal subshift is a single
  periodic orbit; with `Subshift.IsMinimal.add_one_le_complexity_of_forall_not_isPeriodicPoint`,
  an aperiodic minimal subshift is infinite and so obeys the Morse–Hedlund floor `p(n) ≥ n + 1`.
* `exists_isMinimal_le_omegaLimitSubshift`, `exists_isUniformlyRecurrent_le_recurrentLanguage` —
  the two corollaries for `ω`-limit sets.

## Implementation notes

* Minimality is stated as a `Prop` about the bundled subshift rather than as Mathlib's class
  `AddAction.IsMinimal ℤ Y`.  The two agree (`Subshift.isMinimal_iff_addAction`) for a non-empty
  `Y`, and only for a non-empty one: Mathlib's condition is vacuously true on the empty subshift,
  which is exactly the subsystem Zorn's lemma must be prevented from returning.
* Zorn is run on `Subshift α ℤ` itself, in the order dual, not on carriers.  The lattice of
  `Instances.lean` already gives the lower bound of a chain as `sInf`, so the only thing left to
  prove is that it is non-empty — nothing has to be rebuilt into a subshift afterwards.
* `IsUniformlyRecurrent` is stated for a family `L : ∀ n, Set (Fin n → α)` and not only for the
  language of a subshift, so that `ofLanguage` transports it; `subword` exists for that reason
  alone.  Its offset bound is `k + n ≤ N`, i.e. the occurrence is required to fit inside the word.
* The bounded-gap form uses the window `[i, i + N]` and not a two-sided window: shift-invariance
  makes the two interchangeable, and the one-sided form is what a Rauzy-graph argument reads.

## Relation to `BB47/`

This is WP7 of `plans/plan-subshift.html`, the compactness half of gap 4a.  What Problem 10.47
consumes is `exists_isMinimal_le_omegaLimitSubshift`: the `ω`-limit set of a word contains a
minimal subsystem, whose language is uniformly recurrent, which is the "generic aperiodic point"
of [M3, Lem. 3.4].  The other half of gap 4 — that a minimal aperiodic subshift with
`p(n) = n + 1` is Sturmian — is the Coven–Hedlund classification and is deliberately out of scope.

## References

* M. Lothaire, *Algebraic Combinatorics on Words*, CUP 2002, §1.5 — uniformly recurrent
  (there: "uniformly recurrent" = "minimal") infinite words.
* N. Pytheas Fogg, *Substitutions in Dynamics, Arithmetics and Combinatorics*, LNM 1794,
  Prop. 5.1.11 — minimal ⟺ uniformly recurrent language.
* B. P. Kitchens, *Symbolic Dynamics*, Springer 1998, §1.4.
* [CH73] E. M. Coven, G. A. Hedlund, *Sequences with minimal block growth*, Math. Systems Theory
  **7** (1973), 138–153 — the classification this file stops short of.
-/

namespace SymbolicDynamics.FullShift

open ForMathlib.SubwordComplexity

variable {α : Type*}

/-! ## Windows of a finite word

`block` reads a window of a bi-infinite configuration.  A statement about a language alone
mentions no configuration, so it needs the same operation on a finite word. -/

/-- The length-`n` **sub-word** of `w` starting at offset `k`, defined when the window fits. -/
def subword {N : ℕ} (w : Fin N → α) (k n : ℕ) (h : k + n ≤ N) : Fin n → α :=
  fun s => w ⟨k + (s : ℕ), by have := s.isLt; omega⟩

@[simp] lemma subword_apply {N : ℕ} (w : Fin N → α) (k n : ℕ) (h : k + n ≤ N) (s : Fin n) :
    subword w k n h s = w ⟨k + (s : ℕ), by have := s.isLt; omega⟩ := rfl

/-- A window of a block of `x` is a block of `x`. -/
lemma subword_block (x : ℤ → α) {N : ℕ} (i : ℤ) (k n : ℕ) (h : k + n ≤ N) :
    subword (block x N i) k n h = block x n (i + k) := by
  funext s
  simp only [subword_apply, block_apply]
  congr 1
  push_cast
  ring

/-! ## Uniformly recurrent languages -/

/-- A family of languages is **uniformly recurrent** when every word of it occurs in every
sufficiently long word of it: for each `v ∈ L n` there is a length `N` such that every `w ∈ L N`
contains `v`.

For the language of a subshift this is equivalent to minimality
(`Subshift.isMinimal_iff_isUniformlyRecurrent`).  Note that the bound `N` depends on `v`, not only
on `n`; demanding a bound depending on `n` alone is *linear* recurrence, a strictly stronger
condition, and is not what is defined here. -/
def IsUniformlyRecurrent (L : ∀ n, Set (Fin n → α)) : Prop :=
  ∀ n : ℕ, ∀ v ∈ L n, ∃ N : ℕ, ∀ w ∈ L N, ∃ k : ℕ, ∃ h : k + n ≤ N, subword w k n h = v

section Subshift

variable [TopologicalSpace α] {Y : Subshift α ℤ}

/-- Every legal word occurs in **every** point of the subshift. -/
def Subshift.OccursEverywhere (Y : Subshift α ℤ) : Prop :=
  ∀ n : ℕ, ∀ v ∈ Y.language n, ∀ x ∈ Y, ∃ i : ℤ, block x n i = v

/-- Every legal word occurs in every point **with bounded gaps**: for each `v` there is an `N` such
that every window of length `N` of every point of `Y` contains `v`. -/
def Subshift.HasBoundedGaps (Y : Subshift α ℤ) : Prop :=
  ∀ n : ℕ, ∀ v ∈ Y.language n, ∃ N : ℕ, ∀ x ∈ Y, ∀ i : ℤ,
    ∃ j : ℤ, i ≤ j ∧ j ≤ i + N ∧ block x n j = v

lemma Subshift.HasBoundedGaps.occursEverywhere (h : Y.HasBoundedGaps) : Y.OccursEverywhere := by
  intro n v hv x hx
  obtain ⟨N, hN⟩ := h n v hv
  obtain ⟨j, -, -, hj⟩ := hN x hx 0
  exact ⟨j, hj⟩

/-- **The bounded-gap form and the word form are the same condition.**  Bounded gaps of size `N`
become words of length `N + n` on one side; on the other, a window of length `N` of a point is
itself a legal word.  No hypothesis on the alphabet is used. -/
theorem Subshift.hasBoundedGaps_iff_isUniformlyRecurrent :
    Y.HasBoundedGaps ↔ IsUniformlyRecurrent Y.language := by
  constructor
  · intro h n v hv
    obtain ⟨N, hN⟩ := h n v hv
    refine ⟨N + n, ?_⟩
    rintro w ⟨x, hx, i, rfl⟩
    obtain ⟨j, hij, hjN, hj⟩ := hN x hx i
    refine ⟨(j - i).toNat, by omega, ?_⟩
    rw [subword_block, show i + ((j - i).toNat : ℤ) = j by omega]
    exact hj
  · intro h n v hv
    obtain ⟨N, hN⟩ := h n v hv
    refine ⟨N, fun x hx i => ?_⟩
    obtain ⟨k, hk, hkv⟩ := hN (block x N i) (Subshift.block_mem_language hx N i)
    rw [subword_block] at hkv
    exact ⟨i + k, by omega, by omega, hkv⟩

/-! ## Minimal subshifts -/

/-- A subshift is **minimal** when it is non-empty and every non-empty sub-subshift is all of it.

The non-emptiness clause is not decoration: without it `⊥` would be minimal, and then
`Subshift.exists_isMinimal_le` would be a vacuous existence statement. -/
def Subshift.IsMinimal (Y : Subshift α ℤ) : Prop :=
  (Y : Set (ℤ → α)).Nonempty ∧
    ∀ Z : Subshift α ℤ, Z ≤ Y → (Z : Set (ℤ → α)).Nonempty → Z = Y

lemma Subshift.IsMinimal.nonempty (h : Y.IsMinimal) : (Y : Set (ℤ → α)).Nonempty := h.1

lemma Subshift.IsMinimal.eq_of_le (h : Y.IsMinimal) {Z : Subshift α ℤ} (hZY : Z ≤ Y)
    (hZ : (Z : Set (ℤ → α)).Nonempty) : Z = Y := h.2 Z hZY hZ

/-- **Minimal ⟺ every orbit is dense.**  The orbit closure of a point of `Y` is the smallest
subshift containing it, so minimality says exactly that it is already `Y`. -/
theorem Subshift.isMinimal_iff_forall_orbitClosure_eq :
    Y.IsMinimal ↔ (Y : Set (ℤ → α)).Nonempty ∧ ∀ x ∈ Y, orbitClosure x = Y := by
  constructor
  · rintro ⟨hne, hmin⟩
    exact ⟨hne, fun x hx => hmin _ (orbitClosure_le_of_mem hx) ⟨x, self_mem_orbitClosure x⟩⟩
  · rintro ⟨hne, h⟩
    refine ⟨hne, fun Z hZY hZ => ?_⟩
    obtain ⟨x, hx⟩ := hZ
    refine le_antisymm hZY ?_
    rw [← h x (hZY hx)]
    exact orbitClosure_le_of_mem hx

/-- The orbit of a point of `Y` is dense **in `Y`** exactly when `Y` is contained in its orbit
closure.  This is the bridge from the subtype `↥Y`, where Mathlib's `AddAction.IsMinimal` lives,
to the ambient full shift, where everything else in this development lives. -/
lemma dense_orbit_iff_le_orbitClosure (Y : Subshift α ℤ) (z : Y) :
    Dense (AddAction.orbit ℤ z) ↔ Y ≤ orbitClosure (z : ℤ → α) := by
  have himg : (((↑) : _ → (ℤ → α)) '' AddAction.orbit ℤ z) = orbit (z : ℤ → α) := by
    ext y
    constructor
    · rintro ⟨p, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g +ᵥ z, ⟨g, rfl⟩, rfl⟩
  constructor
  · intro h y hy
    have hmem := closure_subtype.mp (h ⟨y, hy⟩)
    rw [himg, ← coe_orbitClosure_eq_closure_orbit] at hmem
    exact hmem
  · intro h p
    rw [closure_subtype, himg, ← coe_orbitClosure_eq_closure_orbit]
    exact h p.2

/-- **Minimality of a subshift is minimality of the shift action on it**, in Mathlib's sense.
This is what the `scoped` action instances of `Instances.lean` were for: with them, all of
`Mathlib.Dynamics.Minimal` applies to a subshift verbatim.

Non-emptiness must be assumed on the right-hand side, because `AddAction.IsMinimal` holds
vacuously on the empty subshift. -/
theorem Subshift.isMinimal_iff_addAction (hY : (Y : Set (ℤ → α)).Nonempty) :
    Y.IsMinimal ↔ AddAction.IsMinimal ℤ Y := by
  rw [Subshift.isMinimal_iff_forall_orbitClosure_eq]
  constructor
  · rintro ⟨-, h⟩
    exact ⟨fun z => (dense_orbit_iff_le_orbitClosure Y z).mpr (le_of_eq (h z z.2).symm)⟩
  · intro h
    refine ⟨hY, fun x hx => le_antisymm (orbitClosure_le_of_mem hx) ?_⟩
    exact (dense_orbit_iff_le_orbitClosure Y ⟨x, hx⟩).mp (h.dense_orbit _)

/-! ## Existence of a minimal subsystem -/

section Finite

variable [Finite α]

/-- **Every non-empty subshift contains a minimal one.**

Zorn's lemma, run on `Subshift α ℤ` in the order dual: the sub-subshifts of `Y` that are non-empty
form a set in which every chain has a lower bound, namely its `sInf`, which is a subshift for free
and is non-empty by Cantor's intersection theorem — a chain is a directed family of non-empty
compact closed sets.  Compactness of `ℤ → α` is where finiteness of the alphabet enters, and it is
the only place in this theorem where anything is assumed about `α`. -/
theorem Subshift.exists_isMinimal_le {Y : Subshift α ℤ} (hY : (Y : Set (ℤ → α)).Nonempty) :
    ∃ Z ≤ Y, Z.IsMinimal := by
  classical
  set S : Set (Subshift α ℤ) := {Z | Z ≤ Y ∧ (Z : Set (ℤ → α)).Nonempty} with hSdef
  have hchain : ∀ c ⊆ S, (∀ Z₁ ∈ c, ∀ Z₂ ∈ c, Z₁ ≤ Z₂ ∨ Z₂ ≤ Z₁) →
      ∃ lb ∈ S, ∀ Z ∈ c, lb ≤ Z := by
    intro c hcS hc
    rcases c.eq_empty_or_nonempty with rfl | hne
    · exact ⟨Y, ⟨le_rfl, hY⟩, fun Z hZ => hZ.elim⟩
    refine ⟨sInf c, ⟨?_, ?_⟩, fun Z hZ => sInf_le hZ⟩
    · obtain ⟨Z₀, hZ₀⟩ := hne
      exact le_trans (sInf_le hZ₀) (hcS hZ₀).1
    · have : Nonempty ↥c := hne.to_subtype
      have hdir : Directed (· ⊇ ·) fun Z : ↥c => ((Z : Subshift α ℤ) : Set (ℤ → α)) := by
        rintro ⟨Z₁, h₁⟩ ⟨Z₂, h₂⟩
        rcases hc Z₁ h₁ Z₂ h₂ with h | h
        · exact ⟨⟨Z₁, h₁⟩, subset_rfl, SetLike.coe_subset_coe.mpr h⟩
        · exact ⟨⟨Z₂, h₂⟩, SetLike.coe_subset_coe.mpr h, subset_rfl⟩
      obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
        (fun Z : ↥c => ((Z : Subshift α ℤ) : Set (ℤ → α))) hdir (fun Z => (hcS Z.2).2)
        (fun Z => (isClosed_coe _).isCompact) fun Z => isClosed_coe _
      simp only [Set.mem_iInter] at hx
      exact ⟨x, mem_sInf.mpr fun Z hZ => hx ⟨Z, hZ⟩⟩
  obtain ⟨m, hm⟩ : ∃ m, Minimal (· ∈ S) m :=
    (@zorn_le₀ (Subshift α ℤ)ᵒᵈ _ S) fun c hcS hc =>
      hchain c hcS fun Z₁ h₁ Z₂ h₂ => by
        rcases eq_or_ne Z₁ Z₂ with rfl | hne
        · exact Or.inl le_rfl
        · exact (hc h₁ h₂ hne).symm
  exact ⟨m, hm.1.1, hm.1.2, fun Z hZm hZ =>
    le_antisymm hZm (hm.2 ⟨hZm.trans hm.1.1, hZ⟩ hZm)⟩

end Finite

/-! ## Minimal means uniformly recurrent -/

section Discrete

variable [DiscreteTopology α]

/-- **Minimal ⟺ every legal word occurs in every point.**

Both directions are the duality theorem of `Duality.lean` in disguise, and neither needs
compactness or a finite alphabet.  Forwards: the orbit closure of `x` is `Y`, and the language of
an orbit closure is the set of blocks of the point.  Backwards: if every block of `y` occurs in
`z`, then `y` lies in every subshift containing `z`. -/
theorem Subshift.isMinimal_iff_occursEverywhere :
    Y.IsMinimal ↔ (Y : Set (ℤ → α)).Nonempty ∧ Y.OccursEverywhere := by
  rw [Subshift.isMinimal_iff_forall_orbitClosure_eq]
  refine and_congr_right fun _ => ⟨fun h n v hv x hx => ?_, fun h x hx => ?_⟩
  · rw [← h x hx, language_orbitClosure] at hv
    exact hv
  · refine le_antisymm (orbitClosure_le_of_mem hx) fun y hy => ?_
    refine mem_of_forall_block_mem_language _ fun n i => ?_
    rw [language_orbitClosure]
    exact h n (block y n i) (Subshift.block_mem_language hy n i) x hx

variable [Finite α]

/-- **Occurring everywhere is occurring with bounded gaps.**  This is the one step of the
characterisation that costs something, and what it costs is compactness: the sets of points that
see `v` within distance `N` of the origin are open, increase with `N` and cover `Y`, so one of
them already contains `Y`.  Shift-invariance then moves the window anywhere. -/
theorem Subshift.OccursEverywhere.hasBoundedGaps (h : Y.OccursEverywhere) : Y.HasBoundedGaps := by
  intro n v hv
  -- the points that see `v` within distance `N` of the origin
  let U : ℕ → Set (ℤ → α) :=
    fun N => {x | ∃ j : ℤ, -(N : ℤ) ≤ j ∧ j ≤ (N : ℤ) ∧ block x n j = v}
  have hUopen : ∀ N : ℕ, IsOpen (U N) := by
    intro N
    have he : U N = ⋃ j : ℤ, ⋃ _ : -(N : ℤ) ≤ j ∧ j ≤ (N : ℤ),
        {x : ℤ → α | block x n j = v} := by
      ext x
      constructor
      · rintro ⟨j, hj1, hj2, hjv⟩
        exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨⟨hj1, hj2⟩, hjv⟩⟩
      · intro hx
        obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
        obtain ⟨⟨hj1, hj2⟩, hjv⟩ := Set.mem_iUnion.mp hj
        exact ⟨j, hj1, hj2, hjv⟩
    rw [he]
    exact isOpen_iUnion fun j => isOpen_iUnion fun _ =>
      (isOpen_discrete {v}).preimage (continuous_block n j)
  have hcover : (Y : Set (ℤ → α)) ⊆ ⋃ N, U N := by
    intro x hx
    obtain ⟨i, hi⟩ := h n v hv x hx
    exact Set.mem_iUnion.mpr ⟨i.natAbs, i, by omega, by omega, hi⟩
  have hdir : Directed (· ⊆ ·) U := by
    refine fun N M => ⟨max N M, ?_, ?_⟩ <;>
      · rintro x ⟨j, hj1, hj2, hjv⟩
        exact ⟨j, by omega, by omega, hjv⟩
  obtain ⟨N, hN⟩ :=
    ((isClosed_coe Y).isCompact).elim_directed_cover U hUopen hcover hdir
  refine ⟨2 * N, fun x hx i => ?_⟩
  obtain ⟨j, hj1, hj2, hjv⟩ := hN (shift_mem Y (i + N) hx)
  rw [block_shift] at hjv
  exact ⟨i + N + j, by omega, by omega, hjv⟩

/-- **Minimal ⟺ the language has bounded gaps.** -/
theorem Subshift.isMinimal_iff_hasBoundedGaps :
    Y.IsMinimal ↔ (Y : Set (ℤ → α)).Nonempty ∧ Y.HasBoundedGaps :=
  Subshift.isMinimal_iff_occursEverywhere.trans
    (and_congr_right fun _ =>
      ⟨fun h => h.hasBoundedGaps, Subshift.HasBoundedGaps.occursEverywhere⟩)

/-- **A subshift is minimal exactly when its language is uniformly recurrent.**  The equivalence
the Theorem-B chain consumes, and the reason `IsUniformlyRecurrent` is worth defining. -/
theorem Subshift.isMinimal_iff_isUniformlyRecurrent :
    Y.IsMinimal ↔ (Y : Set (ℤ → α)).Nonempty ∧ IsUniformlyRecurrent Y.language :=
  Subshift.isMinimal_iff_hasBoundedGaps.trans
    (and_congr_right fun _ => Subshift.hasBoundedGaps_iff_isUniformlyRecurrent)

/-- The subshift defined by a factorial extendable language is non-empty.  The `ω`-limit case is
`omegaLimitSubshift_nonempty`; the argument is the same and uses nothing but
`language_ofLanguage` at level `0`. -/
lemma nonempty_ofLanguage {L : ∀ n, Set (Fin n → α)} (hL : IsLanguage L) :
    ((ofLanguage L : Subshift α ℤ) : Set (ℤ → α)).Nonempty := by
  obtain ⟨v, hv⟩ := hL.nonempty 0
  rw [← language_ofLanguage hL 0] at hv
  obtain ⟨x, hx, -⟩ := Subshift.mem_language.mp hv
  exact ⟨x, hx⟩

/-- **Uniform recurrence is a property of the language alone**, and it says of the language
exactly what minimality says of the subshift.  Together with the duality of `Duality.lean` this
makes minimal subshifts and uniformly recurrent languages the same objects under two names. -/
theorem isUniformlyRecurrent_iff_isMinimal_ofLanguage {L : ∀ n, Set (Fin n → α)}
    (hL : IsLanguage L) : IsUniformlyRecurrent L ↔ (ofLanguage L).IsMinimal := by
  have he : (ofLanguage L : Subshift α ℤ).language = L := funext (language_ofLanguage hL)
  rw [Subshift.isMinimal_iff_isUniformlyRecurrent, he, and_iff_right (nonempty_ofLanguage hL)]

/-! ## Minimal subshifts: periodic or of full complexity -/

omit [Finite α] in
/-- **A finite minimal subshift is a single periodic orbit.** -/
theorem Subshift.IsMinimal.exists_isPeriodicPoint_of_finite (hmin : Y.IsMinimal)
    (hfin : (Y : Set (ℤ → α)).Finite) :
    ∃ (x : ℤ → α) (p : ℕ), 0 < p ∧ x ∈ Y ∧ IsPeriodicPoint x p ∧
      (Y : Set (ℤ → α)) = orbit x := by
  obtain ⟨x, hx⟩ := hmin.nonempty
  obtain ⟨p, hp, hper⟩ := Subshift.exists_period_of_finite hfin hx
  refine ⟨x, p, hp, hx, hper, ?_⟩
  rw [← (Subshift.isMinimal_iff_forall_orbitClosure_eq.mp hmin).2 x hx]
  exact hper.coe_orbitClosure hp

/-- **An aperiodic minimal subshift obeys the Morse–Hedlund floor.**  It cannot be finite, since a
finite minimal subshift is a periodic orbit, so `p(n) ≥ n + 1` at every level.  This is the shape
in which [M3, Lem. 3.4] hands its generic point to the complexity count. -/
theorem Subshift.IsMinimal.add_one_le_complexity_of_forall_not_isPeriodicPoint
    (hmin : Y.IsMinimal) (hap : ∀ x ∈ Y, ∀ p : ℕ, 0 < p → ¬ IsPeriodicPoint x p) (n : ℕ) :
    n + 1 ≤ Y.complexity n := by
  refine Subshift.add_one_le_complexity_of_infinite (fun hfin => ?_) n
  obtain ⟨x, p, hp, hx, hper, -⟩ := hmin.exists_isPeriodicPoint_of_finite hfin
  exact hap x hx p hp hper

end Discrete

end Subshift

/-! ## The `ω`-limit case -/

section OmegaLimit

variable [TopologicalSpace α] [DiscreteTopology α] [Finite α]

/-- **The `ω`-limit set of a word contains a minimal subsystem.**  The compactness half of
[M3, Lem. 3.4]: `Ω u` is a non-empty subshift, so Zorn applies to it. -/
theorem exists_isMinimal_le_omegaLimitSubshift (u : ℕ → α) :
    ∃ Z ≤ omegaLimitSubshift u, Z.IsMinimal :=
  Subshift.exists_isMinimal_le (omegaLimitSubshift_nonempty u)

/-- …and its language is a uniformly recurrent sub-language of the recurrent language of `u`.
This is the statement Problem 10.47 consumes: inside the blocks that recur in `u` there is a
uniformly recurrent family, obtained with no hypothesis on `u` whatsoever. -/
theorem exists_isUniformlyRecurrent_le_recurrentLanguage (u : ℕ → α) :
    ∃ Z : Subshift α ℤ, (Z : Set (ℤ → α)).Nonempty ∧ IsUniformlyRecurrent Z.language ∧
      ∀ n, Z.language n ⊆ recurrentLanguage u n := by
  obtain ⟨Z, hZ, hmin⟩ := exists_isMinimal_le_omegaLimitSubshift u
  obtain ⟨hne, hur⟩ := Subshift.isMinimal_iff_isUniformlyRecurrent.mp hmin
  refine ⟨Z, hne, hur, fun n => ?_⟩
  rw [← language_omegaLimitSubshift u n]
  exact language_mono (SetLike.coe_subset_coe.mpr hZ) n

end OmegaLimit

end SymbolicDynamics.FullShift
