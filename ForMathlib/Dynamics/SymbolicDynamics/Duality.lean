/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import ForMathlib.Dynamics.SymbolicDynamics.Blocks
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Tactic.Common

/-!
# A subshift is its language

This file proves the duality that all of symbolic dynamics is written in: over a finite discrete
alphabet, closed shift-invariant subsets of `ℤ → α` and factorial extendable languages are the
same thing.

## Main results

* `mem_closure_iff_forall_exists_block_eq` — **blocks decide closure**: `y ∈ closure S` iff every
  block of `y` is realised in the same position by a member of `S`.  The `←` half assumes nothing
  about `α` and is the engine of the recovery theorem; the `→` half needs discreteness.
* `mem_of_forall_block_mem_language` — **a subshift is recovered from its language**: if every
  block of `x` occurs in `Y`, then `x ∈ Y`.  This needs no finiteness and no discreteness; only
  that `Y` is closed and shift-invariant.
* `Subshift.ext_language` — two subshifts with the same language are equal.
* `ofLanguage L` — the subshift of configurations all of whose blocks are legal, and
  `language_ofLanguage`: its language is `L` again, for any factorial extendable `L`.  This is the
  direction with content; the proof extends a given word indefinitely in both directions and takes
  a limit by compactness.
* `ofLanguage_language` — the two constructions are mutually inverse.

## The proof of `language_ofLanguage`

The inclusion `⊆` is the definition.  For `⊇`, given `v ∈ L n` one must exhibit a configuration
all of whose blocks are legal and in which `v` occurs.  Extendability gives, for each `k`, a legal
word of length `n + 2k` with `v` in the middle (`exists_extendRightN`, `exists_extendLeftN`, each
a one-letter step by `Function.update` iterated); realising it as a configuration gives a
non-empty closed set `C k`, and the `C k` decrease because sub-blocks of legal blocks are legal
(`IsLanguage.sub`).  A point of `⋂ k, C k` — non-empty by compactness of `ℤ → α` — is the
required configuration.  This is the only place where finiteness of the alphabet is used.

## References

* M. Lothaire, *Algebraic Combinatorics on Words*, CUP 2002, Prop. 1.5.10 and §1.5 generally.
* B. P. Kitchens, *Symbolic Dynamics*, Springer 1998, §1.2 (Thm. 1.2.4 for the correspondence).
* D. Lind, B. Marcus, *An Introduction to Symbolic Dynamics and Coding*, CUP 1995, §6.1.
-/

namespace SymbolicDynamics.FullShift

variable {α : Type*}

/-! ## Sub-blocks of legal blocks -/

section Sub

variable {L : ∀ n, Set (Fin n → α)} {x : ℤ → α}

lemma IsLanguage.dropLast (hL : IsLanguage L) {m : ℕ} {i : ℤ}
    (h : block x (m + 1) i ∈ L (m + 1)) : block x m i ∈ L m := by
  have h' := hL.init h
  rwa [block_comp_castSucc] at h'

lemma IsLanguage.dropFirst (hL : IsLanguage L) {m : ℕ} {i : ℤ}
    (h : block x (m + 1) i ∈ L (m + 1)) : block x m (i + 1) ∈ L m := by
  have h' := hL.tail h
  rwa [block_comp_succ] at h'

/-- Shortening a legal block from the right keeps it legal. -/
lemma IsLanguage.dropRight (hL : IsLanguage L) :
    ∀ {k m : ℕ} {i : ℤ}, m ≤ k → block x k i ∈ L k → block x m i ∈ L m := by
  intro k
  induction k with
  | zero =>
      intro m i hm h
      obtain rfl : m = 0 := Nat.le_zero.mp hm
      exact h
  | succ k ih =>
      intro m i hm h
      rcases Nat.lt_or_ge m (k + 1) with hlt | hge
      · exact ih (Nat.lt_succ_iff.mp hlt) (hL.dropLast h)
      · obtain rfl : m = k + 1 := le_antisymm hm hge
        exact h

/-- Shortening a legal block from the left keeps it legal. -/
lemma IsLanguage.dropFirstN (hL : IsLanguage L) {m : ℕ} :
    ∀ (d : ℕ) {i : ℤ}, block x (m + d) i ∈ L (m + d) → block x m (i + d) ∈ L m := by
  intro d
  induction d with
  | zero => intro i h; simpa using h
  | succ d ih =>
      intro i h
      have h2 := ih (hL.dropFirst h)
      have e : i + 1 + (d : ℤ) = i + ((d + 1 : ℕ) : ℤ) := by push_cast; ring
      rwa [e] at h2

lemma IsLanguage.dropLeft (hL : IsLanguage L) {k m d : ℕ} {i : ℤ} (hk : m + d ≤ k)
    (h : block x k i ∈ L k) : block x m (i + d) ∈ L m :=
  hL.dropFirstN d (hL.dropRight hk h)

/-- **Every sub-block of a legal block is legal.**  This is the workhorse: it turns the two
one-letter conditions of `IsLanguage` into the statement that legality is inherited by arbitrary
sub-intervals. -/
lemma IsLanguage.sub (hL : IsLanguage L) {m m' : ℕ} {i i' : ℤ}
    (h : block x m i ∈ L m) (h1 : i ≤ i') (h2 : i' + m' ≤ i + m) :
    block x m' i' ∈ L m' := by
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, i' = i + d := ⟨(i' - i).toNat, by omega⟩
  exact hL.dropLeft (k := m) (m := m') (d := d) (by omega) h

end Sub

/-! ## A subshift is recovered from its language -/

section Recovery

variable [TopologicalSpace α]

/-! ### Blocks detect closure

A configuration lies in the closure of a set of configurations exactly when each of its blocks is
realised, *in the same position*, by some member of that set.  The `←` direction is elementary and
assumes nothing about `α`: a basic open set of `ℤ → α` constrains only finitely many coordinates,
and a single block covers them all.  The `→` direction is where discreteness of the alphabet
enters, since that is what makes "agrees with `y` along a block" a neighbourhood of `y`. -/

/-- **One block at a time suffices to enter a closure.**  No hypothesis on the alphabet. -/
lemma mem_closure_of_forall_exists_block_eq {S : Set (ℤ → α)} {y : ℤ → α}
    (h : ∀ (n : ℕ) (i : ℤ), ∃ z ∈ S, block z n i = block y n i) : y ∈ closure S := by
  rw [mem_closure_iff]
  intro O hO hyO
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hO y hyO
  rcases I.eq_empty_or_nonempty with rfl | hI
  · obtain ⟨z, hz, -⟩ := h 0 0
    exact ⟨z, hsub (by simp), hz⟩
  · set i := I.min' hI with hi
    set M := I.max' hI with hM
    set n := (M - i + 1).toNat with hn
    have hiM : i ≤ M := I.min'_le M (I.max'_mem hI)
    obtain ⟨z, hz, hzb⟩ := h n i
    refine ⟨z, hsub ?_, hz⟩
    intro a ha
    have h1 : i ≤ a := I.min'_le a ha
    have h2 : a ≤ M := I.le_max' a ha
    have hlt : (a - i).toNat < n := by omega
    have hval := congrFun hzb ⟨(a - i).toNat, hlt⟩
    simp only [block_apply] at hval
    have e1 : i + (((a - i).toNat : ℕ) : ℤ) = a := by omega
    rw [e1] at hval
    rw [hval]
    exact (hu a ha).2

/-- Shift-invariance turns a block of `Y` *somewhere* into a point of `Y` carrying that block
*here*.  This is the only place the position bookkeeping of `language` is paid for. -/
lemma Subshift.exists_mem_block_eq (Y : Subshift α ℤ) {x : ℤ → α} {n : ℕ} {i : ℤ}
    (h : block x n i ∈ Y.language n) : ∃ z ∈ (Y : Set (ℤ → α)), block z n i = block x n i := by
  obtain ⟨y, hy, j, hj⟩ := Subshift.mem_language.mp h
  refine ⟨shift (j - i) y, shift_mem Y _ hy, ?_⟩
  rw [block_shift, sub_add_cancel, hj]

/-- **A subshift is recovered from its language.**  If every block of `x` occurs somewhere in `Y`,
then `x` itself lies in `Y`.  Closedness supplies the limit and shift-invariance moves each
witness into position; neither finiteness nor discreteness of the alphabet is needed. -/
theorem mem_of_forall_block_mem_language (Y : Subshift α ℤ) {x : ℤ → α}
    (h : ∀ (n : ℕ) (i : ℤ), block x n i ∈ Y.language n) : x ∈ Y := by
  have hx : x ∈ (Y : Set (ℤ → α)) := by
    rw [← (isClosed_coe Y).closure_eq]
    exact mem_closure_of_forall_exists_block_eq fun n i => Y.exists_mem_block_eq (h n i)
  exact hx

/-- A subshift is a subset of another as soon as its language is. -/
theorem Subshift.le_of_language_subset {Y Z : Subshift α ℤ}
    (h : ∀ n, Y.language n ⊆ Z.language n) : Y ≤ Z := fun _ hx =>
  mem_of_forall_block_mem_language Z fun n i => h n (Subshift.block_mem_language hx n i)

/-- **Two subshifts with the same language are equal.**  The reason the whole subject may be
conducted in the language of words. -/
theorem Subshift.ext_language {Y Z : Subshift α ℤ} (h : ∀ n, Y.language n = Z.language n) :
    Y = Z :=
  le_antisymm (Subshift.le_of_language_subset fun n => (h n).le)
    (Subshift.le_of_language_subset fun n => (h n).ge)

/-- Reading off a block is continuous: it is a finite tuple of coordinate evaluations. -/
lemma continuous_block (n : ℕ) (i : ℤ) : Continuous fun x : ℤ → α => block x n i :=
  continuous_pi fun s => continuous_apply (i + (s : ℕ))

section Discrete

variable [DiscreteTopology α]

/-- Over a discrete alphabet, agreeing with `y` along a block is a neighbourhood condition, so
membership in a closure is *detected* by blocks. -/
lemma exists_mem_block_eq_of_mem_closure {S : Set (ℤ → α)} {y : ℤ → α} (hy : y ∈ closure S)
    (n : ℕ) (i : ℤ) : ∃ z ∈ S, block z n i = block y n i := by
  have hV : IsOpen {z : ℤ → α | block z n i = block y n i} :=
    isOpen_discrete {block y n i} |>.preimage (continuous_block n i)
  obtain ⟨z, hzV, hzS⟩ := mem_closure_iff.mp hy _ hV rfl
  exact ⟨z, hzS, hzV⟩

/-- **Blocks decide closure** — the two directions above, packaged. -/
theorem mem_closure_iff_forall_exists_block_eq {S : Set (ℤ → α)} {y : ℤ → α} :
    y ∈ closure S ↔ ∀ (n : ℕ) (i : ℤ), ∃ z ∈ S, block z n i = block y n i :=
  ⟨fun hy => exists_mem_block_eq_of_mem_closure hy, mem_closure_of_forall_exists_block_eq⟩

end Discrete

end Recovery

/-! ## Extending a legal block -/

section Extend

variable {L : ∀ n, Set (Fin n → α)}

/-- A legal block extends to a legal block one letter longer on the right, at the cost of changing
the configuration only at the one position just past its end. -/
lemma exists_extendRight (hL : IsLanguage L) {x : ℤ → α} {m : ℕ} {i : ℤ}
    (h : block x m i ∈ L m) :
    ∃ y : ℤ → α, block y (m + 1) i ∈ L (m + 1) ∧ ∀ j, j ≠ i + m → y j = x j := by
  classical
  obtain ⟨w, hw, hwv⟩ := hL.extendRight h
  refine ⟨Function.update x (i + m) (w (Fin.last m)), ?_, fun j hj => Function.update_of_ne hj _ _⟩
  have hb : block (Function.update x (i + m) (w (Fin.last m))) (m + 1) i = w := by
    funext s
    induction s using Fin.lastCases with
    | last =>
        simp only [block_apply, Fin.val_last]
        rw [Function.update_self]
    | cast t =>
        have hne : i + ((t.castSucc : Fin (m + 1)) : ℕ) ≠ i + m := by
          have : (t : ℕ) < m := t.isLt
          simp only [Fin.val_castSucc]
          omega
        simp only [block_apply]
        rw [Function.update_of_ne hne]
        have := congrFun hwv t
        simp only [Function.comp_apply, block_apply] at this
        simpa [Fin.val_castSucc] using this.symm
  rw [hb]
  exact hw

/-- The mirror image of `exists_extendRight`. -/
lemma exists_extendLeft (hL : IsLanguage L) {x : ℤ → α} {m : ℕ} {i : ℤ}
    (h : block x m i ∈ L m) :
    ∃ y : ℤ → α, block y (m + 1) (i - 1) ∈ L (m + 1) ∧ ∀ j, j ≠ i - 1 → y j = x j := by
  classical
  obtain ⟨w, hw, hwv⟩ := hL.extendLeft h
  refine ⟨Function.update x (i - 1) (w 0), ?_, fun j hj => Function.update_of_ne hj _ _⟩
  have hb : block (Function.update x (i - 1) (w 0)) (m + 1) (i - 1) = w := by
    funext s
    induction s using Fin.cases with
    | zero =>
        simp only [block_apply, Fin.val_zero, Nat.cast_zero, add_zero]
        rw [Function.update_self]
    | succ t =>
        have hne : i - 1 + ((t.succ : Fin (m + 1)) : ℕ) ≠ i - 1 := by
          simp only [Fin.val_succ]
          push_cast
          omega
        have hval := congrFun hwv t
        simp only [Function.comp_apply, block_apply] at hval
        simp only [block_apply]
        rw [Function.update_of_ne hne, hval]
        congr 1
        simp only [Fin.val_succ]
        push_cast
        ring
  rw [hb]
  exact hw

/-- Iterating `exists_extendRight`: a legal block extends `k` letters to the right, leaving the
configuration unchanged on the original window. -/
lemma exists_extendRightN (hL : IsLanguage L) {x : ℤ → α} {m : ℕ} {i : ℤ}
    (h : block x m i ∈ L m) (k : ℕ) :
    ∃ y : ℤ → α, block y (m + k) i ∈ L (m + k) ∧ ∀ j, i ≤ j → j < i + m → y j = x j := by
  induction k with
  | zero => exact ⟨x, h, fun _ _ _ => rfl⟩
  | succ k ih =>
      obtain ⟨y, hy, hagree⟩ := ih
      obtain ⟨z, hz, hz'⟩ := exists_extendRight hL hy
      refine ⟨z, hz, fun j h1 h2 => ?_⟩
      refine (hz' j ?_).trans (hagree j h1 h2)
      have : (m : ℤ) ≤ ((m + k : ℕ) : ℤ) := by push_cast; omega
      omega

/-- Iterating `exists_extendLeft`. -/
lemma exists_extendLeftN (hL : IsLanguage L) {x : ℤ → α} {m : ℕ} {i : ℤ}
    (h : block x m i ∈ L m) (k : ℕ) :
    ∃ y : ℤ → α, block y (m + k) (i - k) ∈ L (m + k) ∧ ∀ j, i ≤ j → j < i + m → y j = x j := by
  induction k with
  | zero => exact ⟨x, by simpa using h, fun _ _ _ => rfl⟩
  | succ k ih =>
      obtain ⟨y, hy, hagree⟩ := ih
      obtain ⟨z, hz, hz'⟩ := exists_extendLeft hL hy
      refine ⟨z, ?_, fun j h1 h2 => ?_⟩
      · have e : i - ((k + 1 : ℕ) : ℤ) = i - (k : ℤ) - 1 := by push_cast; ring
        rw [e]
        exact hz
      · refine (hz' j ?_).trans (hagree j h1 h2)
        have : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
        omega

/-- A configuration realising a given word at position `0`, used only to start the extension. -/
private def constBlock {n : ℕ} (v : Fin n → α) (a : α) : ℤ → α :=
  fun j => if h : 0 ≤ j ∧ j.toNat < n then v ⟨j.toNat, h.2⟩ else a

private lemma block_constBlock {n : ℕ} (v : Fin n → α) (a : α) :
    block (constBlock v a) n 0 = v := by
  classical
  funext s
  have h0 : (0 : ℤ) ≤ ((s : ℕ) : ℤ) := Int.natCast_nonneg _
  have h1 : (((s : ℕ) : ℤ)).toNat < n := by simp
  simp only [block_apply, zero_add, constBlock]
  split
  · congr 1
  · rename_i hcon
    exact absurd ⟨h0, h1⟩ hcon

end Extend

/-! ## The subshift defined by a language -/

section OfLanguage

variable [TopologicalSpace α]

/-- The configurations all of whose blocks are legal for `L`. -/
def legalSet (L : ∀ n, Set (Fin n → α)) : Set (ℤ → α) := { x | ∀ n i, block x n i ∈ L n }

omit [TopologicalSpace α] in
lemma mem_legalSet {L : ∀ n, Set (Fin n → α)} {x : ℤ → α} :
    x ∈ legalSet L ↔ ∀ n i, block x n i ∈ L n := Iff.rfl

variable [DiscreteTopology α]

lemma isClosed_legalSet (L : ∀ n, Set (Fin n → α)) : IsClosed (legalSet L) := by
  have he : legalSet L = ⋂ n : ℕ, ⋂ i : ℤ, (fun x : ℤ → α => block x n i) ⁻¹' L n := by
    ext x; simp [legalSet]
  rw [he]
  exact isClosed_iInter fun n => isClosed_iInter fun i =>
    (isClosed_discrete (L n)).preimage (continuous_block n i)

/-- **The subshift defined by a language**: the configurations all of whose blocks are legal.
No hypothesis on `L` is needed to make this a subshift; `language_ofLanguage` is where
`IsLanguage L` enters. -/
def ofLanguage (L : ∀ n, Set (Fin n → α)) : Subshift α ℤ where
  carrier := legalSet L
  isClosed := isClosed_legalSet L
  mapsTo := by
    intro g x hx n i
    rw [block_shift]
    exact hx n (g + i)

@[simp] lemma mem_ofLanguage {L : ∀ n, Set (Fin n → α)} {x : ℤ → α} :
    x ∈ ofLanguage L ↔ ∀ n i, block x n i ∈ L n := Iff.rfl

/-- **The language of `ofLanguage L` is `L`.**  The inclusion `⊆` is the definition; the content
is `⊇`, proved by extending a word of `L` indefinitely in both directions and taking a limit by
compactness of `ℤ → α`. -/
theorem language_ofLanguage [Finite α] {L : ∀ n, Set (Fin n → α)} (hL : IsLanguage L) (n : ℕ) :
    (ofLanguage L).language n = L n := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro v ⟨x, hx, i, rfl⟩
    exact hx n i
  intro v hv
  have : Nonempty α := ⟨(hL.nonempty 1).choose 0⟩
  classical
  set a : α := Classical.arbitrary α with ha
  set C : ℕ → Set (ℤ → α) := fun k =>
    { x | block x n 0 = v ∧ block x (n + k + k) (-(k : ℤ)) ∈ L (n + k + k) } with hC
  -- each `C k` is non-empty
  have hCne : ∀ k, (C k).Nonempty := by
    intro k
    have h0 : block (constBlock v a) n 0 ∈ L n := by rw [block_constBlock]; exact hv
    obtain ⟨y₁, hy₁, hag₁⟩ := exists_extendRightN hL h0 k
    obtain ⟨y₂, hy₂, hag₂⟩ := exists_extendLeftN hL hy₁ k
    refine ⟨y₂, ?_, by simpa using hy₂⟩
    rw [← block_constBlock v a]
    funext s
    have hs : ((s : ℕ) : ℤ) < n := by exact_mod_cast s.isLt
    have hs0 : (0 : ℤ) ≤ ((s : ℕ) : ℤ) := Int.natCast_nonneg _
    have hk : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg _
    simp only [block_apply, zero_add]
    rw [hag₂ _ hs0 (by push_cast; omega), hag₁ _ hs0 (by omega)]
  -- the `C k` decrease
  have hCanti : ∀ k, C (k + 1) ⊆ C k := by
    intro k x hx
    refine ⟨hx.1, ?_⟩
    refine hL.sub hx.2 (by push_cast; omega) (by push_cast; omega)
  -- each `C k` is closed
  have hCcl : ∀ k, IsClosed (C k) := by
    intro k
    have e : C k = ((fun x : ℤ → α => block x n 0) ⁻¹' {v}) ∩
        ((fun x : ℤ → α => block x (n + k + k) (-(k : ℤ))) ⁻¹' L (n + k + k)) := rfl
    rw [e]
    exact ((isClosed_discrete _).preimage (continuous_block n 0)).inter
      ((isClosed_discrete _).preimage (continuous_block _ _))
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    C hCanti hCne ((hCcl 0).isCompact) hCcl
  simp only [Set.mem_iInter] at hx
  refine ⟨x, ?_, 0, (hx 0).1⟩
  intro m j
  have habs0 : (0 : ℤ) ≤ |j| := abs_nonneg j
  have habs1 : j ≤ |j| := le_abs_self j
  have habs2 : -|j| ≤ j := neg_abs_le j
  set k : ℕ := (|j| + m + n).toNat with hk
  have hkz : ((k : ℕ) : ℤ) = |j| + m + n := Int.toNat_of_nonneg (by omega)
  refine hL.sub (hx k).2 (by omega) ?_
  push_cast
  omega

/-- **The two constructions are mutually inverse.**  Together with `language_ofLanguage` this is
the bijection between subshifts of `ℤ → α` and factorial extendable languages. -/
theorem ofLanguage_language (Y : Subshift α ℤ) : ofLanguage Y.language = Y := by
  ext x
  constructor
  · intro hx
    exact mem_of_forall_block_mem_language Y hx
  · intro hx n i
    exact Subshift.block_mem_language hx n i

end OfLanguage

end SymbolicDynamics.FullShift
