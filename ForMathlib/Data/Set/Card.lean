/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Data.Set.Card
import Mathlib.Tactic

/-!
# A fibre-count bound for `Set.ncard`

The `Set.ncard` analogue of `Finset.card_le_mul_card_image`: a finite set whose image under `f`
has every fibre of size at most `H` has at most `H · #(image)` elements.  Used to turn a covering
map (each element assigned to one of few "buckets", each bucket small) into a cardinality bound.
-/

/-- **Fibre count for `Set.ncard`.**  If `S` is finite and every fibre `{a ∈ S | f a = b}` has at
most `H` elements, then `#S ≤ H · #(f '' S)`. -/
theorem Set.ncard_le_mul_ncard_image {α β : Type*} {S : Set α} (hS : S.Finite) (f : α → β)
    (H : ℕ) (hfib : ∀ b, {a ∈ S | f a = b}.ncard ≤ H) :
    S.ncard ≤ H * (f '' S).ncard := by
  classical
  have h1 : S.ncard = hS.toFinset.card := by rw [← Set.ncard_coe_finset, hS.coe_toFinset]
  have h2 : (f '' S).ncard = (hS.toFinset.image f).card := by
    rw [← Set.ncard_coe_finset, Finset.coe_image, hS.coe_toFinset]
  rw [h1, h2]
  apply Finset.card_le_mul_card_image hS.toFinset H
  intro b _
  have hcoe : (↑(hS.toFinset.filter (fun a => f a = b)) : Set α) = {a ∈ S | f a = b} := by
    ext x; simp only [Finset.coe_filter, Set.mem_setOf_eq, Set.Finite.mem_toFinset]
  have := hfib b
  rwa [← hcoe, Set.ncard_coe_finset] at this
