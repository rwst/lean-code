/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import ForMathlib.Dynamics.SymbolicDynamics.Periodic
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.Common
import Mathlib.Tactic.Push

/-!
# Factor complexity of a subshift, and Morse–Hedlund

The **factor complexity** of a subshift `Y` is `p(n) = #𝓛ₙ(Y)`, the number of distinct length-`n`
blocks occurring in points of `Y`.  This file develops its elementary properties and proves the
Morse–Hedlund dichotomy in the form the two-sided theory needs.

## Main definitions

* `pSubshift X n` — `(language X n).ncard`, and `Subshift.complexity Y n` for a bundled subshift.
* `ForMathlib.SubwordComplexity.pRecurrent u n` — `(recurrentLanguage u n).ncard`, the number of
  length-`n` blocks occurring infinitely often in the one-sided word `u`.

## Main results

* `Subshift.complexity_mono`, `Subshift.complexity_add_le` — monotone and submultiplicative,
  `p(m+n) ≤ p(m)·p(n)`.
* `Subshift.eq_of_block_eq` — **the plateau theorem**.  If `p(n+1) = p(n)` then a single block of
  length `n+1` determines the whole configuration: both truncation maps `𝓛ₙ₊₁ → 𝓛ₙ` are then
  bijections, so a legal word of length `n` has a unique legal extension on *each* side, and the
  two determinisms propagate a block equality over all of `ℤ`.
* `Subshift.finite_of_complexity_succ_eq`, `Subshift.exists_period_of_complexity_succ_eq` — its two
  consequences: at a plateau `Y` is finite, with `#Y ≤ p(n+1)`, and every point of `Y` is periodic.
* `Subshift.finite_iff_exists_complexity_le` — **Morse–Hedlund for subshifts**: a non-empty
  subshift over a finite alphabet is finite iff `p(n) ≤ n` for some `n`, iff `p` is bounded.  The
  remaining link of the chain, finite iff all points share a period, needs no complexity and is
  `Subshift.finite_iff_exists_common_period` in
  `ForMathlib/Dynamics/SymbolicDynamics/Periodic.lean`.
* `Subshift.add_one_le_complexity_of_infinite` — the floor `p(n) ≥ n + 1` for an infinite subshift.
* `Subshift.complexity_omegaLimitSubshift` — **M1M2 Prop. 2.4**: `p(n, Ω u) = p_∞(n, u)`.

## Implementation notes

The one-sided engine of `ForMathlib/Combinatorics/InfiniteComplexity.lean` does not transfer:
right-determinism on `ℕ` propagates a repetition forward forever, which is all one can ask there,
but on `ℤ` it gives periodicity of the forward ray only.  For a *subshift* the fix is not to work
harder on the right but to notice that a plateau makes the **left** truncation map bijective too,
by exactly the same cardinality argument.  Left determinism then walks the block equality backwards
and `Int.induction_on` closes the loop in one induction.

"Every point is periodic" is stated with a period **common to all points** (`IsPeriodicPoint`,
`Periodic.lean`).  That is what the proofs here produce and what the counting argument consumes;
the *a priori* weaker statement, each point periodic with its own period, is also equivalent, but
only through a compactness argument that is not needed for anything in this development.

## References

* M. Morse, G. A. Hedlund, *Symbolic dynamics*, Amer. J. Math. **60** (1938), 815–866.
* M. Lothaire, *Algebraic Combinatorics on Words*, CUP 2002, §1.3 and §10.
* N. Pytheas Fogg, *Substitutions in Dynamics, Arithmetics and Combinatorics*, Springer LNM 1794,
  §1.2 and §4.1.
-/

namespace ForMathlib.SubwordComplexity

/-- **`p_∞(n, u)`**: the number of length-`n` blocks of the one-sided word `u` that occur
infinitely often.  Definitionally `BB47.pInf`. -/
noncomputable def pRecurrent {α : Type*} (u : ℕ → α) (n : ℕ) : ℕ := (recurrentLanguage u n).ncard

end ForMathlib.SubwordComplexity

namespace SymbolicDynamics.FullShift

open ForMathlib.SubwordComplexity

variable {α : Type*}

/-! ## The complexity function -/

/-- The **factor complexity** of a set of configurations: the number of distinct length-`n` blocks
occurring in it. -/
noncomputable def pSubshift (X : Set (ℤ → α)) (n : ℕ) : ℕ := (language X n).ncard

lemma pSubshift_zero {X : Set (ℤ → α)} (hX : X.Nonempty) : pSubshift X 0 = 1 := by
  have h : language X 0 = {Fin.elim0} := by
    ext v
    constructor
    · rintro ⟨x, hx, i, rfl⟩
      simp
    · rintro rfl
      obtain ⟨x, hx⟩ := hX
      exact ⟨x, hx, 0, by simp⟩
  rw [pSubshift, h, Set.ncard_singleton]

lemma pSubshift_mono_set [Finite α] {X Z : Set (ℤ → α)} (h : X ⊆ Z) (n : ℕ) :
    pSubshift X n ≤ pSubshift Z n :=
  Set.ncard_le_ncard (language_mono h n) (Set.toFinite _)

section Subshift

variable [TopologicalSpace α]

/-- The factor complexity of a bundled subshift. -/
noncomputable def Subshift.complexity (Y : Subshift α ℤ) (n : ℕ) : ℕ :=
  pSubshift (Y : Set (ℤ → α)) n

lemma Subshift.complexity_eq (Y : Subshift α ℤ) (n : ℕ) :
    Y.complexity n = (Y.language n).ncard := rfl

lemma Subshift.complexity_zero {Y : Subshift α ℤ} (hY : (Y : Set (ℤ → α)).Nonempty) :
    Y.complexity 0 = 1 := pSubshift_zero hY

variable [Finite α]

lemma Subshift.language_finite (Y : Subshift α ℤ) (n : ℕ) : (Y.language n).Finite :=
  Set.toFinite _

/-! ### The two truncation maps

Over a non-empty subshift both of them are surjective onto the next level down, by factoriality
and extendability.  Everything in this file turns on what happens when they are also injective. -/

omit [Finite α] in
lemma Subshift.image_comp_castSucc {Y : Subshift α ℤ} (hY : (Y : Set (ℤ → α)).Nonempty) (n : ℕ) :
    (fun w : Fin (n + 1) → α => w ∘ Fin.castSucc) '' Y.language (n + 1) = Y.language n := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact (Y.isLanguage hY).init hw
  · intro v hv
    obtain ⟨w, hw, hwv⟩ := (Y.isLanguage hY).extendRight hv
    exact ⟨w, hw, hwv⟩

omit [Finite α] in
lemma Subshift.image_comp_succ {Y : Subshift α ℤ} (hY : (Y : Set (ℤ → α)).Nonempty) (n : ℕ) :
    (fun w : Fin (n + 1) → α => w ∘ Fin.succ) '' Y.language (n + 1) = Y.language n := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact (Y.isLanguage hY).tail hw
  · intro v hv
    obtain ⟨w, hw, hwv⟩ := (Y.isLanguage hY).extendLeft hv
    exact ⟨w, hw, hwv⟩

/-! ### Monotonicity and submultiplicativity -/

lemma Subshift.complexity_le_succ {Y : Subshift α ℤ} (hY : (Y : Set (ℤ → α)).Nonempty) (n : ℕ) :
    Y.complexity n ≤ Y.complexity (n + 1) := by
  rw [Subshift.complexity_eq, Subshift.complexity_eq, ← Subshift.image_comp_castSucc hY n]
  exact Set.ncard_image_le (Set.toFinite _)

lemma Subshift.complexity_mono {Y : Subshift α ℤ} (hY : (Y : Set (ℤ → α)).Nonempty) :
    Monotone Y.complexity :=
  monotone_nat_of_le_succ (Subshift.complexity_le_succ hY)

/-- **Submultiplicativity**: a block of length `m + n` is determined by its two halves, each of
which is legal. -/
lemma Subshift.complexity_add_le (Y : Subshift α ℤ) (m n : ℕ) :
    Y.complexity (m + n) ≤ Y.complexity m * Y.complexity n := by
  rw [Subshift.complexity_eq, Subshift.complexity_eq, Subshift.complexity_eq, ← Set.ncard_prod]
  refine Set.ncard_le_ncard_of_injOn
    (fun v : Fin (m + n) → α => (v ∘ Fin.castAdd n, v ∘ Fin.natAdd m)) ?_ ?_ (Set.toFinite _)
  · rintro _ ⟨x, hx, i, rfl⟩
    exact ⟨⟨x, hx, i, (block_comp_castAdd x m n i).symm⟩,
      ⟨x, hx, i + m, (block_comp_natAdd x m n i).symm⟩⟩
  · intro v _ w _ h
    obtain ⟨h1, h2⟩ := Prod.mk.injEq .. ▸ h
    funext s
    induction s using Fin.addCases with
    | left s => exact congrFun h1 s
    | right s => exact congrFun h2 s

/-! ## The plateau theorem -/

section Plateau

variable {Y : Subshift α ℤ} {n : ℕ}

/-- At a plateau of `p`, the right-truncation map is injective: a legal word of length `n` has a
**unique** legal extension to the right. -/
lemma Subshift.injOn_comp_castSucc (hY : (Y : Set (ℤ → α)).Nonempty)
    (h : Y.complexity (n + 1) = Y.complexity n) :
    Set.InjOn (fun w : Fin (n + 1) → α => w ∘ Fin.castSucc) (Y.language (n + 1)) := by
  refine Set.injOn_of_ncard_image_eq ?_ (Set.toFinite _)
  rw [Subshift.image_comp_castSucc hY n]
  exact h.symm

/-- At a plateau of `p`, the left-truncation map is injective too.  This is the step the one-sided
theory has no analogue of, and it is free: the same cardinality count applies. -/
lemma Subshift.injOn_comp_succ (hY : (Y : Set (ℤ → α)).Nonempty)
    (h : Y.complexity (n + 1) = Y.complexity n) :
    Set.InjOn (fun w : Fin (n + 1) → α => w ∘ Fin.succ) (Y.language (n + 1)) := by
  refine Set.injOn_of_ncard_image_eq ?_ (Set.toFinite _)
  rw [Subshift.image_comp_succ hY n]
  exact h.symm

variable (hY : (Y : Set (ℤ → α)).Nonempty) (h : Y.complexity (n + 1) = Y.complexity n)
include hY h

/-- Right determinism: a matching pair of blocks stays matching one step later. -/
lemma Subshift.block_step_succ {x y : ℤ → α} (hx : x ∈ Y) (hy : y ∈ Y) {i j : ℤ}
    (hb : block x (n + 1) i = block y (n + 1) j) :
    block x (n + 1) (i + 1) = block y (n + 1) (j + 1) := by
  refine Subshift.injOn_comp_castSucc hY h (Subshift.block_mem_language hx _ _)
    (Subshift.block_mem_language hy _ _) ?_
  show block x (n + 1) (i + 1) ∘ Fin.castSucc = block y (n + 1) (j + 1) ∘ Fin.castSucc
  rw [block_comp_castSucc, block_comp_castSucc]
  have hb' := congrArg (fun w : Fin (n + 1) → α => w ∘ Fin.succ) hb
  simpa only [block_comp_succ] using hb'

/-- Left determinism: a matching pair of blocks was already matching one step earlier. -/
lemma Subshift.block_step_pred {x y : ℤ → α} (hx : x ∈ Y) (hy : y ∈ Y) {i j : ℤ}
    (hb : block x (n + 1) i = block y (n + 1) j) :
    block x (n + 1) (i - 1) = block y (n + 1) (j - 1) := by
  refine Subshift.injOn_comp_succ hY h (Subshift.block_mem_language hx _ _)
    (Subshift.block_mem_language hy _ _) ?_
  show block x (n + 1) (i - 1) ∘ Fin.succ = block y (n + 1) (j - 1) ∘ Fin.succ
  rw [block_comp_succ, block_comp_succ, show i - 1 + 1 = i by ring, show j - 1 + 1 = j by ring]
  have hb' := congrArg (fun w : Fin (n + 1) → α => w ∘ Fin.castSucc) hb
  simpa only [block_comp_castSucc] using hb'

/-- **At a plateau one block determines every block.**  Both determinisms are available, so a
single agreement propagates over all of `ℤ` by integer induction. -/
theorem Subshift.block_eq_of_block_eq {x y : ℤ → α} (hx : x ∈ Y) (hy : y ∈ Y) {i j : ℤ}
    (hb : block x (n + 1) i = block y (n + 1) j) (d : ℤ) :
    block x (n + 1) (i + d) = block y (n + 1) (j + d) := by
  induction d using Int.induction_on with
  | zero => simpa using hb
  | succ k ih =>
      rw [show i + ((k : ℤ) + 1) = (i + (k : ℤ)) + 1 by ring,
        show j + ((k : ℤ) + 1) = (j + (k : ℤ)) + 1 by ring]
      exact Subshift.block_step_succ hY h hx hy ih
  | pred k ih =>
      rw [show i + (-(k : ℤ) - 1) = (i + -(k : ℤ)) - 1 by ring,
        show j + (-(k : ℤ) - 1) = (j + -(k : ℤ)) - 1 by ring]
      exact Subshift.block_step_pred hY h hx hy ih

/-- **The plateau theorem.**  At a plateau of the complexity function a point of `Y` is determined
by one block of length `n + 1`. -/
theorem Subshift.eq_of_block_eq {x y : ℤ → α} (hx : x ∈ Y) (hy : y ∈ Y)
    (hb : block x (n + 1) 0 = block y (n + 1) 0) : x = y := by
  funext m
  have hm := Subshift.block_eq_of_block_eq hY h hx hy hb m
  have := congrFun hm ⟨0, Nat.succ_pos n⟩
  simpa using this

/-- At a plateau the subshift is finite. -/
theorem Subshift.finite_of_complexity_succ_eq : (Y : Set (ℤ → α)).Finite :=
  Set.Finite.of_finite_image (Set.toFinite ((fun x : ℤ → α => block x (n + 1) 0) '' _))
    fun _ hx _ hy hb => Subshift.eq_of_block_eq hY h hx hy hb

/-- …and no bigger than the number of legal words of length `n + 1`. -/
theorem Subshift.ncard_le_complexity :
    (Y : Set (ℤ → α)).ncard ≤ Y.complexity (n + 1) :=
  Set.ncard_le_ncard_of_injOn (fun x : ℤ → α => block x (n + 1) 0)
    (fun _ hx => Subshift.block_mem_language hx _ _)
    (fun _ hx _ hy hb => Subshift.eq_of_block_eq hY h hx hy hb) (Set.toFinite _)

/-- At a plateau every point of `Y` is periodic. -/
theorem Subshift.exists_period_of_complexity_succ_eq {x : ℤ → α} (hx : x ∈ Y) :
    ∃ q : ℕ, 0 < q ∧ IsPeriodicPoint x q := by
  obtain ⟨i, j, hij, hb⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun i : ℤ => block x (n + 1) i)
  have key : ∀ a b : ℤ, a < b → block x (n + 1) a = block x (n + 1) b →
      ∃ q : ℕ, 0 < q ∧ IsPeriodicPoint x q := by
    intro a b hab hab'
    refine ⟨(b - a).toNat, by omega, fun m => ?_⟩
    have hd := Subshift.block_eq_of_block_eq hY h hx hx hab' (m - a)
    have h0 := congrFun hd ⟨0, Nat.succ_pos n⟩
    simp only [block_apply, Nat.cast_zero, add_zero] at h0
    rw [show (((b - a).toNat : ℕ) : ℤ) = b - a by omega,
      show m + (b - a) = b + (m - a) by ring, ← h0]
    congr 1
    ring
  rcases hij.lt_or_gt with hlt | hlt
  · exact key i j hlt hb
  · exact key j i hlt hb.symm

end Plateau

/-! ## Morse–Hedlund -/

/-- Below the first plateau the complexity grows by at least one at each step, so it is at least
`n + 1` at level `n`. -/
theorem Subshift.add_one_le_complexity_of_forall_ne {Y : Subshift α ℤ}
    (hY : (Y : Set (ℤ → α)).Nonempty) :
    ∀ n : ℕ, (∀ k < n, Y.complexity (k + 1) ≠ Y.complexity k) → n + 1 ≤ Y.complexity n := by
  intro n
  induction n with
  | zero => intro _; rw [Subshift.complexity_zero hY]
  | succ n ih =>
      intro hne
      have h1 : n + 1 ≤ Y.complexity n := ih fun k hk => hne k (by omega)
      have h2 : Y.complexity n ≤ Y.complexity (n + 1) := Subshift.complexity_le_succ hY n
      have h3 : Y.complexity (n + 1) ≠ Y.complexity n := hne n (by omega)
      omega

/-- A level at which the complexity fails to exceed its index forces a plateau below it. -/
theorem Subshift.exists_complexity_succ_eq {Y : Subshift α ℤ}
    (hY : (Y : Set (ℤ → α)).Nonempty) {n : ℕ} (hn : Y.complexity n ≤ n) :
    ∃ k, Y.complexity (k + 1) = Y.complexity k := by
  by_contra hcon
  push Not at hcon
  have := Subshift.add_one_le_complexity_of_forall_ne hY n fun k _ => hcon k
  omega

/-- **The Morse–Hedlund floor.**  An infinite subshift has complexity at least `n + 1`. -/
theorem Subshift.add_one_le_complexity_of_infinite {Y : Subshift α ℤ}
    (hinf : (Y : Set (ℤ → α)).Infinite) (n : ℕ) : n + 1 ≤ Y.complexity n := by
  by_contra hcon
  obtain ⟨k, hk⟩ := Subshift.exists_complexity_succ_eq hinf.nonempty (n := n) (by omega)
  exact hinf (Subshift.finite_of_complexity_succ_eq hinf.nonempty hk)

/-! ### From finiteness back to low complexity -/

/-- A common period bounds the complexity: every block occurs already at a position in `[0, Q)`,
and there are only `#Y · Q` such choices. -/
theorem Subshift.complexity_le_of_common_period {Y : Subshift α ℤ}
    (hfin : (Y : Set (ℤ → α)).Finite) {Q : ℕ} (hQ : 0 < Q)
    (hper : ∀ x ∈ Y, IsPeriodicPoint x Q) (n : ℕ) :
    Y.complexity n ≤ (Y : Set (ℤ → α)).ncard * Q := by
  classical
  have hsub : Y.language n ⊆ (fun p : (ℤ → α) × ℕ => block p.1 n (p.2 : ℤ)) ''
      ((Y : Set (ℤ → α)) ×ˢ (↑(Finset.range Q) : Set ℕ)) := by
    rintro _ ⟨x, hx, i, rfl⟩
    have hQ' : (0 : ℤ) < (Q : ℤ) := by exact_mod_cast hQ
    have h1 : 0 ≤ i % (Q : ℤ) := Int.emod_nonneg i (by omega)
    have h2 : i % (Q : ℤ) < (Q : ℤ) := Int.emod_lt_of_pos i hQ'
    refine ⟨(x, (i % (Q : ℤ)).toNat), ⟨hx, ?_⟩, ?_⟩
    · simp only [Finset.coe_range, Set.mem_Iio]
      omega
    · show block x n (((i % (Q : ℤ)).toNat : ℕ) : ℤ) = block x n i
      rw [Int.toNat_of_nonneg h1]
      exact ((hper x hx).block_eq n (Int.emod_add_mul_ediv i (Q : ℤ)).symm).symm
  calc Y.complexity n ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ ((Y : Set (ℤ → α)) ×ˢ (↑(Finset.range Q) : Set ℕ)).ncard :=
        Set.ncard_image_le (hfin.prod (Set.toFinite _))
    _ = (Y : Set (ℤ → α)).ncard * Q := by
        rw [Set.ncard_prod, Set.ncard_coe_finset, Finset.card_range]

/-- **Morse–Hedlund for subshifts.**  For a non-empty subshift over a finite alphabet, being finite,
having a common period, having bounded complexity and dipping to `p(n) ≤ n` are all the same. -/
theorem Subshift.finite_iff_exists_complexity_le {Y : Subshift α ℤ}
    (hY : (Y : Set (ℤ → α)).Nonempty) :
    (Y : Set (ℤ → α)).Finite ↔ ∃ n, Y.complexity n ≤ n := by
  constructor
  · intro hfin
    obtain ⟨Q, hQ, hper⟩ := Subshift.exists_common_period hfin
    exact ⟨(Y : Set (ℤ → α)).ncard * Q,
      Subshift.complexity_le_of_common_period hfin hQ hper _⟩
  · rintro ⟨n, hn⟩
    obtain ⟨k, hk⟩ := Subshift.exists_complexity_succ_eq hY hn
    exact Subshift.finite_of_complexity_succ_eq hY hk

end Subshift

/-! ## The `ω`-limit subshift: `p_∞` is a subshift complexity -/

section OmegaLimit

variable [TopologicalSpace α] [DiscreteTopology α] [Finite α]

/-- **The eventual complexity of a word is the factor complexity of its `ω`-limit subshift.**
[M1M2, Prop. 2.4]. -/
theorem complexity_omegaLimitSubshift (u : ℕ → α) (n : ℕ) :
    (omegaLimitSubshift u).complexity n = pRecurrent u n := by
  rw [Subshift.complexity_eq, language_omegaLimitSubshift, pRecurrent]

/-- The Morse–Hedlund floor, transported to `p_∞`. -/
theorem add_one_le_pRecurrent_of_infinite (u : ℕ → α)
    (hinf : ((omegaLimitSubshift u : Set (ℤ → α))).Infinite) (n : ℕ) :
    n + 1 ≤ pRecurrent u n := by
  rw [← complexity_omegaLimitSubshift]
  exact Subshift.add_one_le_complexity_of_infinite hinf n

end OmegaLimit

end SymbolicDynamics.FullShift
