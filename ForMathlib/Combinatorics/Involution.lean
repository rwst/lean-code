/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Group.Even
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Linarith

/-!
# Fixed-point-free involutions have even orbit count

A finite set closed under an involution with no fixed points has even cardinality: the involution
pairs its elements off.  This is the standard parity device behind, for instance, Zagier's
one-sentence proof of the two-squares theorem, and behind "the conjugates of a reciprocal
irreducible polynomial come in pairs `{δ, δ⁻¹}`".

Mathlib has the group-theoretic special case (`FixedPointFree.odd_card_of_involutive`, about a
fixed-point-free automorphism of a group) but not the bare `Finset` statement, so it is proved
here by strong induction on the set: remove a pair `{a, f a}` and recurse.

## Main results

* `Finset.even_card_of_involution` — `s` closed under `f`, `f ∘ f = id`, `f x ≠ x` on `s`
  ⇒ `Even s.card`.
* `Set.Finite.even_ncard_of_involution` — the same for a finite `Set`.

Note that `f` is only ever applied to elements of `s`, but it is stated for a global involution
because that is what the applications carry (`z ↦ z⁻¹`, `z ↦ conj z`, `x ↦ -x`).
-/

namespace Finset

/-- **A fixed-point-free involution pairs off a finite set**: if `f` is an involution, `s` is
closed under `f`, and `f` fixes no element of `s`, then `s` has even cardinality.

By strong induction: pick `a ∈ s`, note `f a ∈ s` and `f a ≠ a`, and delete both.  What remains is
still closed under `f` (if `f x = a` then `x = f a`, and if `f x = f a` then `x = a`), so induction
gives `Even (s.card - 2)`. -/
theorem even_card_of_involution {α : Type*} [DecidableEq α] {f : α → α}
    (hinv : ∀ x, f (f x) = x) {s : Finset α} (hmaps : ∀ x ∈ s, f x ∈ s)
    (hne : ∀ x ∈ s, f x ≠ x) : Even s.card := by
  induction s using Finset.strongInduction with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · simp
    · have hfa : f a ∈ s := hmaps a ha
      have hane : f a ≠ a := hne a ha
      have hfamem : f a ∈ s.erase a := Finset.mem_erase.mpr ⟨hane, hfa⟩
      set t := (s.erase a).erase (f a) with ht
      have hsub : t ⊂ s := lt_of_le_of_lt (Finset.erase_subset _ _) (Finset.erase_ssubset ha)
      have hmem : ∀ x ∈ t, x ∈ s ∧ x ≠ a ∧ x ≠ f a := by
        intro x hx
        have h1 := Finset.mem_erase.mp hx
        have h2 := Finset.mem_erase.mp h1.2
        exact ⟨h2.2, h2.1, h1.1⟩
      have hmaps' : ∀ x ∈ t, f x ∈ t := by
        intro x hx
        obtain ⟨hxs, hxa, hxfa⟩ := hmem x hx
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hmaps x hxs⟩⟩
        · intro h; exact hxa (by rw [← hinv x, h, hinv])
        · intro h; exact hxfa (by rw [← h, hinv])
      have hne' : ∀ x ∈ t, f x ≠ x := fun x hx => hne x (hmem x hx).1
      have hcard : t.card = s.card - 2 := by
        rw [ht, Finset.card_erase_of_mem hfamem, Finset.card_erase_of_mem ha]; omega
      have hge : 2 ≤ s.card := by
        have hss : ({a, f a} : Finset α) ⊆ s := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact ha
          · rw [Finset.mem_singleton] at hx; exact hx ▸ hfa
        have := Finset.card_le_card hss
        rwa [Finset.card_insert_of_notMem (by simp [Ne.symm hane]), Finset.card_singleton] at this
      have hev := ih t hsub hmaps' hne'
      rw [hcard] at hev
      rcases Nat.even_or_odd s.card with h | h
      · exact h
      · exfalso
        obtain ⟨m, hm⟩ := h
        rw [hm] at hev
        obtain ⟨j, hj⟩ := hev
        omega

end Finset

namespace Set

/-- The `Set` form of `Finset.even_card_of_involution`. -/
theorem Finite.even_ncard_of_involution {α : Type*} {f : α → α} (hinv : ∀ x, f (f x) = x)
    {s : Set α} (hs : s.Finite) (hmaps : ∀ x ∈ s, f x ∈ s) (hne : ∀ x ∈ s, f x ≠ x) :
    Even s.ncard := by
  classical
  rw [Set.ncard_eq_toFinset_card s hs]
  exact Finset.even_card_of_involution hinv
    (fun x hx => hs.mem_toFinset.mpr (hmaps x (hs.mem_toFinset.mp hx)))
    (fun x hx => hne x (hs.mem_toFinset.mp hx))

end Set
