/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import ForMathlib.Dynamics.SymbolicDynamics.Instances
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Ring

/-!
# Blocks and the language of a two-sided configuration set

Mathlib's `Mathlib.Dynamics.SymbolicDynamics.Basic` records the language of a set of
configurations as a set of `Pattern`s over a `Finset G` support.  That is the right generality for
an arbitrary monoid, but it is not the currency of combinatorics on words, where a length-`n`
factor is a tuple `Fin n → α` and the shapes that matter are intervals.  This file introduces the
interval form on `G = ℤ`.

## Main definitions

* `block x n i : Fin n → α` — the length-`n` block of `x : ℤ → α` read at position `i`,
  deliberately the two-sided mirror of `ForMathlib.SubwordComplexity.factor` for one-sided words.
* `language X n : Set (Fin n → α)` — the length-`n` blocks occurring somewhere in some point of
  `X`, and `Subshift.language` for a bundled subshift.
* `IsLanguage L` — the two conditions a family `L : ∀ n, Set (Fin n → α)` must satisfy to be the
  language of a subshift: *factorial* (closed under taking sub-blocks) and *extendable* (every
  word extends by one letter on either side).  `isLanguage_language` proves that the language of a
  non-empty set of configurations always satisfies them; the converse, that every such family is
  the language of a subshift, is `ForMathlib/Dynamics/SymbolicDynamics/Duality.lean`.

## Implementation notes

* Positions are `ℤ` and lengths are `ℕ`, so `block x n i` reads `x i, x (i+1), …, x (i+n-1)`.
  Mixing the two is deliberate: lengths are the index of the language, positions are acted on by
  the shift, and keeping them in different types stops `omega` from being handed nonsense.
* `language` is *position-free*: a word belongs to it if it occurs anywhere in any point of `X`.
  For a shift-invariant `X` this loses nothing and is what makes `language X` a factorial
  extendable family without further hypotheses.

## References

* M. Lothaire, *Algebraic Combinatorics on Words*, CUP 2002, Ch. 1 — factorial extendable
  languages and the subshifts they define.
* B. P. Kitchens, *Symbolic Dynamics*, Springer 1998, §1.2.
-/

namespace SymbolicDynamics.FullShift

variable {α : Type*}

/-! ## Blocks -/

/-- The length-`n` **block** of the configuration `x : ℤ → α` starting at position `i`: the tuple
`(x i, x (i+1), …, x (i+n-1))`, indexed by `Fin n`.  This is the two-sided counterpart of
`ForMathlib.SubwordComplexity.factor`. -/
def block (x : ℤ → α) (n : ℕ) (i : ℤ) : Fin n → α := fun s => x (i + s)

@[simp] lemma block_apply (x : ℤ → α) (n : ℕ) (i : ℤ) (s : Fin n) : block x n i s = x (i + s) :=
  rfl

@[simp] lemma block_zero (x : ℤ → α) (i : ℤ) : block x 0 i = Fin.elim0 := by
  funext s; exact s.elim0

/-- Shifting a configuration translates its blocks. -/
lemma block_shift (x : ℤ → α) (g : ℤ) (n : ℕ) (i : ℤ) :
    block (shift g x) n i = block x n (g + i) := by
  funext s; simp [block, shift, add_assoc]

/-- Dropping the last letter of a block gives the shorter block at the same position. -/
lemma block_comp_castSucc (x : ℤ → α) (n : ℕ) (i : ℤ) :
    block x (n + 1) i ∘ Fin.castSucc = block x n i := by
  funext s; simp [block]

/-- Dropping the first letter of a block gives the shorter block one position later. -/
lemma block_comp_succ (x : ℤ → α) (n : ℕ) (i : ℤ) :
    block x (n + 1) i ∘ Fin.succ = block x n (i + 1) := by
  funext s
  simp only [Function.comp_apply, block_apply, Fin.val_succ]
  congr 1
  push_cast
  ring

/-- The first `m` letters of a block of length `m + n`. -/
lemma block_comp_castAdd (x : ℤ → α) (m n : ℕ) (i : ℤ) :
    block x (m + n) i ∘ Fin.castAdd n = block x m i := by
  funext s
  simp [block, Fin.val_castAdd]

/-- The last `n` letters of a block of length `m + n`. -/
lemma block_comp_natAdd (x : ℤ → α) (m n : ℕ) (i : ℤ) :
    block x (m + n) i ∘ Fin.natAdd m = block x n (i + m) := by
  funext s
  simp only [Function.comp_apply, block_apply, Fin.val_natAdd]
  congr 1
  push_cast
  ring

/-! ## The language -/

/-- The **language** of a set of configurations at level `n`: the length-`n` blocks occurring at
some position in some point of `X`. -/
def language (X : Set (ℤ → α)) (n : ℕ) : Set (Fin n → α) :=
  { v | ∃ x ∈ X, ∃ i : ℤ, block x n i = v }

lemma mem_language {X : Set (ℤ → α)} {n : ℕ} {v : Fin n → α} :
    v ∈ language X n ↔ ∃ x ∈ X, ∃ i : ℤ, block x n i = v := Iff.rfl

lemma block_mem_language {X : Set (ℤ → α)} {x : ℤ → α} (hx : x ∈ X) (n : ℕ) (i : ℤ) :
    block x n i ∈ language X n := ⟨x, hx, i, rfl⟩

lemma language_mono {X Y : Set (ℤ → α)} (h : X ⊆ Y) (n : ℕ) : language X n ⊆ language Y n := by
  rintro v ⟨x, hx, i, rfl⟩
  exact ⟨x, h hx, i, rfl⟩

/-! ## Factorial extendable families -/

/-- `IsLanguage L` says that the family `L` of sets of words is **factorial** — closed under
dropping the first or the last letter — and **extendable**: every word of `L` is the head, and
also the tail, of a longer word of `L`.  Together with non-emptiness these are exactly the
conditions under which `L` is the language of a subshift
(`ForMathlib/Dynamics/SymbolicDynamics/Duality.lean`). -/
structure IsLanguage (L : ∀ n, Set (Fin n → α)) : Prop where
  /-- Every level is inhabited. -/
  nonempty (n : ℕ) : (L n).Nonempty
  /-- Dropping the last letter stays in the language. -/
  init {n : ℕ} {v : Fin (n + 1) → α} : v ∈ L (n + 1) → v ∘ Fin.castSucc ∈ L n
  /-- Dropping the first letter stays in the language. -/
  tail {n : ℕ} {v : Fin (n + 1) → α} : v ∈ L (n + 1) → v ∘ Fin.succ ∈ L n
  /-- Every word extends by one letter on the right. -/
  extendRight {n : ℕ} {v : Fin n → α} : v ∈ L n → ∃ w ∈ L (n + 1), w ∘ Fin.castSucc = v
  /-- Every word extends by one letter on the left. -/
  extendLeft {n : ℕ} {v : Fin n → α} : v ∈ L n → ∃ w ∈ L (n + 1), w ∘ Fin.succ = v

/-- **The language of a non-empty set of configurations is factorial and extendable.**  No
topology, no invariance and no finiteness of the alphabet are needed: a sub-block of a block is a
block, and a block of `x` always extends inside `x` itself. -/
theorem isLanguage_language {X : Set (ℤ → α)} (hX : X.Nonempty) : IsLanguage (language X) where
  nonempty n := by
    obtain ⟨x, hx⟩ := hX
    exact ⟨block x n 0, block_mem_language hx n 0⟩
  init := by
    rintro n v ⟨x, hx, i, rfl⟩
    exact ⟨x, hx, i, (block_comp_castSucc x n i).symm⟩
  tail := by
    rintro n v ⟨x, hx, i, rfl⟩
    exact ⟨x, hx, i + 1, (block_comp_succ x n i).symm⟩
  extendRight := by
    rintro n v ⟨x, hx, i, rfl⟩
    exact ⟨block x (n + 1) i, block_mem_language hx (n + 1) i, block_comp_castSucc x n i⟩
  extendLeft := by
    rintro n v ⟨x, hx, i, rfl⟩
    exact ⟨block x (n + 1) (i - 1), block_mem_language hx (n + 1) (i - 1), by
      rw [block_comp_succ]; congr 1; ring⟩

section Subshift

variable [TopologicalSpace α]

/-- The language of a bundled subshift. -/
def Subshift.language (Y : Subshift α ℤ) (n : ℕ) : Set (Fin n → α) :=
  FullShift.language (Y : Set (ℤ → α)) n

lemma Subshift.mem_language {Y : Subshift α ℤ} {n : ℕ} {v : Fin n → α} :
    v ∈ Y.language n ↔ ∃ x ∈ Y, ∃ i : ℤ, block x n i = v := Iff.rfl

lemma Subshift.block_mem_language {Y : Subshift α ℤ} {x : ℤ → α} (hx : x ∈ Y) (n : ℕ) (i : ℤ) :
    block x n i ∈ Y.language n := ⟨x, hx, i, rfl⟩

theorem Subshift.isLanguage (Y : Subshift α ℤ) (hY : (Y : Set (ℤ → α)).Nonempty) :
    IsLanguage Y.language :=
  isLanguage_language hY

end Subshift

end SymbolicDynamics.FullShift
