/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/

import paradoxical.Defs
import paradoxical.RCircuitSlice
import RT.Heuristic
import Mathlib.Data.List.TakeWhile
import Mathlib.Data.Set.Finite.Lattice

/-!
# Canonical shapes: the slices cover, and the uniform-over-`R` connection

Two complements to the assembled Baker reduction (`BakerReduction.lean`).

**Coverage.**  Every binary word is the shape word of its canonical run
decomposition: `shapeOf w` groups a maximal burst of `1`s and the following
maximal gap into one circuit, and `wordOfShape (shapeOf w) = w` on binary words
(`wordOfShape_shapeOf`).  Hence every paradoxical `Ωⱼ(n)` with `n > 2` lies in the
slice of its canonical circuit count `circuitCount j n = (shapeOf (pbits j n)).length`
(`rCircuitSlice_circuitCount`), and the slices exhaust the paradoxical set:
`⋃ R, RCircuitSlice R = {paradoxical, n > 2}` (`iUnion_rCircuitSlice`).

**The uniform-over-`R` connection.**  The per-`R` theorem `finite_RCircuitSlice`
internally derives a *length bound* `j ≤ J(R)` on the slice.  The uniform version —
one `J` for **all** `R` — is, via coverage, *equivalent* to the finiteness of the
whole paradoxical set (`uniform_slice_length_bound_iff_finitely_many_paradoxical`,
forward direction `finitely_many_paradoxical_of_uniform_slice_length_bound` through
`RT.finitely_many_paradoxical_of_paradoxical_length_bounded`).  This formalizes the
"a bound uniform over all `R` would be Collatz itself" remark: the uniform length
bound is not merely sufficient but *equivalent* to paradoxical finiteness.

Note what is **not** claimed: the excursion hypothesis `hexc` holding uniformly in
`R` does *not* yield the uniform length bound through this chain — for a sequence
with `R ≈ j/2` circuits the pigeonhole exponent `j/(2R)` degenerates to a constant
and the collision disappears.  That gap is exactly the Collatz-hardness of the
uniform statement.

`sorry`-free; this file is elementary (std3) — the transcendence input sits in
`BakerReduction`/`RhinPolyBound`, not here.

## References
* [Roz25] Rozier, Olivier, and Claude Terracol. "Paradoxical behavior in Collatz
  sequences." arXiv:2502.00948 (2025). §5 (circuits), §6 (finiteness heuristic).
-/

namespace Paradoxical

open CC RT

/-! ### The canonical run decomposition -/

/-- The **canonical run decomposition** of a parity word: each circuit is a maximal
burst of `1`s followed by the maximal gap up to the next `1` (on binary words the
gap is a maximal run of `0`s).  A word starting with `0` yields a first circuit
with empty burst (`a₁ = 0`), matching the `wordOfShape` conventions. -/
def shapeOf : List ℕ → List (ℕ × ℕ)
  | [] => []
  | x :: xs =>
    (((x :: xs).takeWhile (· == 1)).length,
      (((x :: xs).dropWhile (· == 1)).takeWhile (· != 1)).length) ::
      shapeOf (((x :: xs).dropWhile (· == 1)).dropWhile (· != 1))
termination_by w => w.length
decreasing_by
  have hs1 : ((x :: xs).takeWhile (· == 1)).length
      + ((x :: xs).dropWhile (· == 1)).length = (x :: xs).length := by
    rw [← List.length_append, List.takeWhile_append_dropWhile]
  have hs2 : (((x :: xs).dropWhile (· == 1)).takeWhile (· != 1)).length
      + (((x :: xs).dropWhile (· == 1)).dropWhile (· != 1)).length
      = ((x :: xs).dropWhile (· == 1)).length := by
    rw [← List.length_append, List.takeWhile_append_dropWhile]
  have hlc : (x :: xs).length = xs.length + 1 := rfl
  by_cases hx : x = 1
  · -- the burst eats the head
    have ht : 0 < ((x :: xs).takeWhile (· == 1)).length := by
      simp [hx]
    omega
  · -- the gap eats the head
    have ht2 : 0 < (((x :: xs).dropWhile (· == 1)).takeWhile (· != 1)).length := by
      simp [hx]
    omega

/-- A nonempty word has a nonempty canonical decomposition. -/
lemma shapeOf_ne_nil {w : List ℕ} (hw : w ≠ []) : shapeOf w ≠ [] := by
  cases w with
  | nil => exact absurd rfl hw
  | cons x xs => simp [shapeOf]

/-- **Canonical-shape existence** (roundtrip): on binary words the canonical run
decomposition reconstructs the word, `wordOfShape (shapeOf w) = w`. -/
theorem wordOfShape_shapeOf : ∀ w : List ℕ, (∀ x ∈ w, x = 0 ∨ x = 1) →
    wordOfShape (shapeOf w) = w := by
  intro w
  induction w using shapeOf.induct with
  | case1 => intro _; simp [shapeOf, wordOfShape]
  | case2 x xs ih =>
    intro hw
    -- burst letters are `1`
    have h1mem : ∀ b ∈ (x :: xs).takeWhile (· == 1), b = 1 := by
      intro b hb
      simpa using List.mem_takeWhile_imp hb
    -- gap letters are `≠ 1`, hence `0` on a binary word
    have h2mem : ∀ b ∈ ((x :: xs).dropWhile (· == 1)).takeWhile (· != 1), b = 0 := by
      intro b hb
      have hne : b ≠ 1 := by simpa using List.mem_takeWhile_imp hb
      have hb_r : b ∈ (x :: xs).dropWhile (· == 1) := by
        have h' := List.mem_append_left
          ((((x :: xs).dropWhile (· == 1)).dropWhile (· != 1))) hb
        rwa [List.takeWhile_append_dropWhile] at h'
      have hb_w : b ∈ x :: xs := by
        have h' := List.mem_append_right ((x :: xs).takeWhile (· == 1)) hb_r
        rwa [List.takeWhile_append_dropWhile] at h'
      rcases hw b hb_w with h0 | h1
      · exact h0
      · exact absurd h1 hne
    -- the tail stays binary
    have hbin2 : ∀ y ∈ ((x :: xs).dropWhile (· == 1)).dropWhile (· != 1),
        y = 0 ∨ y = 1 := by
      intro y hy
      apply hw
      have h' := List.mem_append_right
        (((x :: xs).dropWhile (· == 1)).takeWhile (· != 1)) hy
      rw [List.takeWhile_append_dropWhile] at h'
      have h'' := List.mem_append_right ((x :: xs).takeWhile (· == 1)) h'
      rwa [List.takeWhile_append_dropWhile] at h''
    -- unfold one layer and reassemble the two splits
    simp only [shapeOf, wordOfShape]
    rw [ih hbin2, ← List.eq_replicate_of_mem h1mem, ← List.eq_replicate_of_mem h2mem,
      List.append_assoc, List.takeWhile_append_dropWhile, List.takeWhile_append_dropWhile]

/-- The canonical decomposition has the right total length. -/
lemma wlen_shapeOf (w : List ℕ) (hw : ∀ x ∈ w, x = 0 ∨ x = 1) :
    wlen (shapeOf w) = w.length := by
  rw [← wordOfShape_length, wordOfShape_shapeOf w hw]

/-! ### The parity window is a binary word -/

/-- The parity word has length `j`. -/
lemma length_pbits (j n : ℕ) : (pbits j n).length = j := by
  simp [pbits]

/-- The parity word is binary. -/
lemma pbits_binary (j n : ℕ) : ∀ x ∈ pbits j n, x = 0 ∨ x = 1 := by
  intro x hx
  simp only [pbits, List.mem_map, List.mem_range] at hx
  obtain ⟨k, -, rfl⟩ := hx
  rw [X_eq_mod]
  omega

/-! ### Coverage: every paradoxical sequence lies in its canonical slice -/

/-- The **canonical circuit count** of the length-`j` parity window of `n`. -/
def circuitCount (j n : ℕ) : ℕ := (shapeOf (pbits j n)).length

/-- A window of positive length has at least one circuit. -/
lemma circuitCount_pos (j n : ℕ) (hj : 0 < j) : 0 < circuitCount j n := by
  unfold circuitCount
  cases hw : pbits j n with
  | nil =>
    have := congrArg List.length hw
    simp [pbits] at this
    omega
  | cons a l => simp [shapeOf]

/-- **Coverage.**  Every paradoxical `Ωⱼ(n)` with `n > 2` lies in the slice of its
canonical circuit count. -/
theorem rCircuitSlice_circuitCount (j n : ℕ) (hn : 2 < n) (hpara : IsParadoxical j n) :
    RCircuitSlice (circuitCount j n) j n :=
  ⟨hn, hpara, shapeOf (pbits j n), rfl,
    by rw [wlen_shapeOf _ (pbits_binary j n), length_pbits],
    (wordOfShape_shapeOf _ (pbits_binary j n)).symm⟩

/-- **Exhaustion.**  The `R`-circuit slices cover the paradoxical set exactly:
`⋃ R, RCircuitSlice R = {(j, n) | Ωⱼ(n) paradoxical, n > 2}`. -/
theorem iUnion_rCircuitSlice :
    ⋃ R : ℕ, {p : ℕ × ℕ | RCircuitSlice R p.1 p.2}
      = {p : ℕ × ℕ | IsParadoxical p.1 p.2 ∧ 2 < p.2} := by
  ext ⟨j, n⟩
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨R, hs⟩
    exact ⟨hs.2.1, hs.1⟩
  · rintro ⟨hpara, hn⟩
    exact ⟨circuitCount j n, rCircuitSlice_circuitCount j n hn hpara⟩

/-! ### The uniform-over-`R` connection -/

/-- **The uniform-over-`R` version implies full paradoxical finiteness.**  The per-`R`
reduction `finite_RCircuitSlice` internally derives a length bound `j ≤ J(R)` on the
`R`-circuit slice; if that bound holds with a single `J` for **all** `R`, then — via
coverage by the canonical shapes — every paradoxical length is `≤ J`, and per-length
finiteness (`RT.finitely_many_paradoxical_of_paradoxical_length_bounded`) makes the
whole paradoxical set finite.  This is the formal content of "a bound uniform over
all `R` would be Collatz itself". -/
theorem finitely_many_paradoxical_of_uniform_slice_length_bound
    (h : ∃ J : ℕ, ∀ R j n : ℕ, RCircuitSlice R j n → j ≤ J) :
    {p : ℕ × ℕ | IsParadoxical p.1 p.2 ∧ 2 < p.2}.Finite := by
  obtain ⟨J, hJ⟩ := h
  apply finitely_many_paradoxical_of_paradoxical_length_bounded
  exact ⟨J, fun j n hpar hn =>
    hJ (circuitCount j n) j n (rCircuitSlice_circuitCount j n hn hpar)⟩

/-- **The uniform slice length bound is *equivalent* to paradoxical finiteness.**
Forward: `finitely_many_paradoxical_of_uniform_slice_length_bound`.  Backward: a
finite paradoxical set has finitely many lengths, and every slice member is
paradoxical.  So the uniform-over-`R` version of the reduction is not merely
sufficient for — it is a reformulation of — the finiteness of the paradoxical set. -/
theorem uniform_slice_length_bound_iff_finitely_many_paradoxical :
    (∃ J : ℕ, ∀ R j n : ℕ, RCircuitSlice R j n → j ≤ J) ↔
      {p : ℕ × ℕ | IsParadoxical p.1 p.2 ∧ 2 < p.2}.Finite := by
  constructor
  · exact finitely_many_paradoxical_of_uniform_slice_length_bound
  · intro hfin
    obtain ⟨J, hJ⟩ := (hfin.image Prod.fst).bddAbove
    refine ⟨J, fun R j n hs => ?_⟩
    exact hJ ⟨(j, n), ⟨hs.2.1, hs.1⟩, rfl⟩

end Paradoxical
