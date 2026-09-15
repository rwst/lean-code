/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import ForMathlib.Combinatorics.SubwordComplexity
import ForMathlib.Dynamics.SymbolicDynamics.Duality
import Mathlib.Data.Fintype.Card
import Mathlib.Dynamics.OmegaLimit
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Push

/-!
# The `ω`-limit subshift of a one-sided word

A one-sided infinite word `u : ℕ → α` is not a point of the two-sided full shift, so it has no
orbit closure of its own.  What it does have is the set of configurations all of whose blocks
recur in `u` — classically the **`ω`-limit set** of `u`, written `Ω(u)`.  This file constructs it,
identifies its language, and proves that it really is the `ω`-limit set in Mathlib's topological
sense, of any two-sided extension of `u`.

## Main definitions

* `ForMathlib.SubwordComplexity.IsRecurrentFactor u n v` — the block `v` occurs in `u` at
  arbitrarily late positions; `recurrentLanguage u n` is the set of such `v`.
* `SymbolicDynamics.FullShift.orbitClosure x` — the orbit closure of a configuration, as a
  subshift; `orbitClosure_le_of_mem` is its minimality.
* `SymbolicDynamics.FullShift.omegaLimitSubshift u` — `Ω(u)`, defined as `ofLanguage` of the
  recurrent language.
* `SymbolicDynamics.FullShift.IsTwoSidedExtension x u` — `x : ℤ → α` agrees with `u` on `ℕ`.

## Main results

* `isLanguage_recurrentLanguage` — over a **finite** alphabet the recurrent language is factorial
  and extendable on both sides.  The four obligations are exactly the classical statements that
  every vertex of the reduced Rauzy graph of `u` has positive in- and out-degree; each one is a
  pigeonhole along a cofinal set of positions (`exists_frequently_eq`).
* `language_omegaLimitSubshift` — `𝓛ₙ(Ω u) = recurrentLanguage u n`.  This is where the duality
  of `Duality.lean` is spent: the inclusion with content is that every recurrent block really
  occurs in a *configuration* of `Ω u`.
* `omegaLimitSubshift_tail` — `Ω` forgets any finite prefix of `u`.
* `coe_omegaLimitSubshift_eq_omegaLimit` — **the topological identity**: for any two-sided
  extension `x` of `u`, the carrier of `Ω u` is Mathlib's `omegaLimit atTop (shift ·) {x}`.
  `omegaLimit_eq_of_isTwoSidedExtension` records the corollary that the right-hand side does not
  depend on the extension chosen — the formal content of "`Ω` only sees the tail of `u`".

## Implementation notes

`IsRecurrentFactor` is phrased as `∀ N, ∃ i ≥ N, factor u n i = v` rather than through
`Filter.atTop`; `isRecurrentFactor_iff_frequently` is the bridge.  The explicit form is what the
index arithmetic of the extension lemmas wants, and it is the form in which the predicate is
consumed downstream.

Finiteness of the alphabet is needed only for `isLanguage_recurrentLanguage` and its consequences
(`language_omegaLimitSubshift`, `omegaLimitSubshift_nonempty`): it is the pigeonhole, and it is
also exactly the hypothesis under which `Ω u` can fail to be empty.  The topological identity
needs no finiteness, only discreteness.

## References

* M. Queffélec, *Substitution Dynamical Systems — Spectral Analysis*, Springer LNM 1294, §4.1.
* M. Lothaire, *Algebraic Combinatorics on Words*, CUP 2002, §1.5 and §10.
* N. Pytheas Fogg, *Substitutions in Dynamics, Arithmetics and Combinatorics*, Springer LNM 1794,
  §1.2 and §4.1 for the `ω`-limit subshift and the Rauzy graph.
-/

namespace ForMathlib.SubwordComplexity

variable {α : Type*}

/-! ## Pigeonhole along a cofinal set of positions -/

/-- **Pigeonhole along a cofinal set of positions.**  If a property `P` of natural numbers holds
at arbitrarily late positions and `f` takes finitely many values, then some single value of `f` is
attained at arbitrarily late positions at which `P` holds.

This is the one finiteness argument behind the whole file: applied with `P` trivial it produces a
recurrent block, with `P i := factor u n i = v` a recurrent right extension of `v`, and with a
shifted `f` a recurrent left extension. -/
theorem exists_frequently_eq {γ : Type*} [Finite γ] {P : ℕ → Prop} (f : ℕ → γ)
    (hP : ∀ N : ℕ, ∃ i, N ≤ i ∧ P i) : ∃ c : γ, ∀ N : ℕ, ∃ i, N ≤ i ∧ P i ∧ f i = c := by
  classical
  have : Fintype γ := Fintype.ofFinite γ
  by_contra hcon
  push Not at hcon
  choose N hN using hcon
  obtain ⟨i, hi, hPi⟩ := hP (Finset.univ.sup N)
  exact hN (f i) i (le_trans (Finset.le_sup (Finset.mem_univ (f i))) hi) hPi rfl

/-! ## Recurrent factors -/

/-- A length-`n` block `v` is a **recurrent factor** of the one-sided word `u` when it occurs at
arbitrarily late positions — equivalently, at infinitely many positions. -/
def IsRecurrentFactor (u : ℕ → α) (n : ℕ) (v : Fin n → α) : Prop :=
  ∀ N : ℕ, ∃ i : ℕ, N ≤ i ∧ factor u n i = v

/-- The **recurrent language** of `u` at level `n`: the blocks occurring infinitely often.  It is
the language of the `ω`-limit subshift `Ω u`, by `language_omegaLimitSubshift`. -/
def recurrentLanguage (u : ℕ → α) (n : ℕ) : Set (Fin n → α) := {v | IsRecurrentFactor u n v}

@[simp]
lemma mem_recurrentLanguage {u : ℕ → α} {n : ℕ} {v : Fin n → α} :
    v ∈ recurrentLanguage u n ↔ IsRecurrentFactor u n v := Iff.rfl

/-- Recurrence is frequency along `atTop`. -/
lemma isRecurrentFactor_iff_frequently {u : ℕ → α} {n : ℕ} {v : Fin n → α} :
    IsRecurrentFactor u n v ↔ ∃ᶠ i in Filter.atTop, factor u n i = v := by
  simp [IsRecurrentFactor, Filter.frequently_atTop]

/-- A recurrent factor is in particular a factor. -/
lemma IsRecurrentFactor.exists_eq {u : ℕ → α} {n : ℕ} {v : Fin n → α}
    (h : IsRecurrentFactor u n v) : ∃ i, factor u n i = v := by
  obtain ⟨i, -, hi⟩ := h 0
  exact ⟨i, hi⟩

/-! ### The four language axioms -/

/-- Over a finite alphabet some block of each length recurs. -/
lemma recurrentLanguage_nonempty [Finite α] (u : ℕ → α) (n : ℕ) :
    (recurrentLanguage u n).Nonempty := by
  obtain ⟨v, hv⟩ := exists_frequently_eq (P := fun _ => True) (factor u n)
    fun N => ⟨N, le_rfl, trivial⟩
  refine ⟨v, fun N => ?_⟩
  obtain ⟨i, hi, -, hfi⟩ := hv N
  exact ⟨i, hi, hfi⟩

/-- Recurrence passes to the prefix: every occurrence of `v` carries one of its truncation. -/
lemma IsRecurrentFactor.init {u : ℕ → α} {n : ℕ} {v : Fin (n + 1) → α}
    (h : IsRecurrentFactor u (n + 1) v) : IsRecurrentFactor u n (v ∘ Fin.castSucc) := by
  intro N
  obtain ⟨i, hi, hfi⟩ := h N
  exact ⟨i, hi, by rw [factor_castSucc u n i, hfi]⟩

/-- Recurrence passes to the suffix: an occurrence at `i` gives one of the truncation at `i+1`. -/
lemma IsRecurrentFactor.tail {u : ℕ → α} {n : ℕ} {v : Fin (n + 1) → α}
    (h : IsRecurrentFactor u (n + 1) v) : IsRecurrentFactor u n (v ∘ Fin.succ) := by
  intro N
  obtain ⟨i, hi, hfi⟩ := h N
  exact ⟨i + 1, by omega, by rw [← factor_comp_succ, hfi]⟩

/-- **Every recurrent block extends to the right.**  Classically: every vertex of the reduced
Rauzy graph of `u` has out-degree at least one. -/
lemma IsRecurrentFactor.extendRight [Finite α] {u : ℕ → α} {n : ℕ} {v : Fin n → α}
    (h : IsRecurrentFactor u n v) :
    ∃ w, IsRecurrentFactor u (n + 1) w ∧ w ∘ Fin.castSucc = v := by
  obtain ⟨w, hw⟩ := exists_frequently_eq (P := fun i => factor u n i = v) (factor u (n + 1)) h
  refine ⟨w, fun N => ?_, ?_⟩
  · obtain ⟨i, hi, -, hfi⟩ := hw N
    exact ⟨i, hi, hfi⟩
  obtain ⟨i, -, hv, hfi⟩ := hw 0
  rw [← hfi, ← factor_castSucc, hv]

/-- **Every recurrent block extends to the left.**  Classically: every vertex of the reduced
Rauzy graph of `u` has in-degree at least one.  The left extension has to be read off one position
earlier, which is why the pigeonhole is applied to `fun i => factor u (n+1) (i - 1)`. -/
lemma IsRecurrentFactor.extendLeft [Finite α] {u : ℕ → α} {n : ℕ} {v : Fin n → α}
    (h : IsRecurrentFactor u n v) :
    ∃ w, IsRecurrentFactor u (n + 1) w ∧ w ∘ Fin.succ = v := by
  obtain ⟨w, hw⟩ := exists_frequently_eq (P := fun i => 1 ≤ i ∧ factor u n i = v)
    (fun i => factor u (n + 1) (i - 1))
    (fun N => by obtain ⟨i, hi, hfi⟩ := h (N + 1); exact ⟨i, by omega, by omega, hfi⟩)
  refine ⟨w, fun N => ?_, ?_⟩
  · obtain ⟨i, hi, -, hfi⟩ := hw (N + 1)
    exact ⟨i - 1, by omega, hfi⟩
  obtain ⟨i, -, ⟨h1, hv⟩, hfi⟩ := hw 0
  rw [← hfi, factor_comp_succ, show i - 1 + 1 = i by omega, hv]

/-! ### `Ω` forgets the head -/

/-- The recurrent language is a **tail invariant**: discarding a finite prefix of `u` changes
nothing.  This is the language form of the fact that `Ω u` only sees the tail of `u`. -/
theorem recurrentLanguage_tail (u : ℕ → α) (m n : ℕ) :
    recurrentLanguage (fun k => u (m + k)) n = recurrentLanguage u n := by
  ext v
  constructor
  · intro h N
    obtain ⟨i, hi, hfi⟩ := h N
    refine ⟨m + i, by omega, ?_⟩
    funext s
    have := congrFun hfi s
    simp only [factor] at this ⊢
    rw [show m + i + (s : ℕ) = m + (i + (s : ℕ)) by omega]
    exact this
  · intro h N
    obtain ⟨i, hi, hfi⟩ := h (m + N)
    refine ⟨i - m, by omega, ?_⟩
    funext s
    have := congrFun hfi s
    simp only [factor] at this ⊢
    rw [show m + (i - m + (s : ℕ)) = i + (s : ℕ) by omega]
    exact this

end ForMathlib.SubwordComplexity

namespace SymbolicDynamics.FullShift

open ForMathlib.SubwordComplexity

variable {α : Type*}

/-! ## Orbit closures -/

section OrbitClosure

variable [TopologicalSpace α]

/-- The **orbit closure** of a configuration, as a subshift: the closure of `{shift g x}` is
closed by construction and shift-invariant because `shift g` is continuous and maps the orbit into
itself. -/
def orbitClosure (x : ℤ → α) : Subshift α ℤ where
  carrier := closure (Set.range fun g : ℤ => shift g x)
  isClosed := isClosed_closure
  mapsTo g := by
    refine Set.MapsTo.closure_left ?_ (continuous_shift g) isClosed_closure
    rintro _ ⟨g', rfl⟩
    exact subset_closure ⟨g' + g, shift_add g' g x⟩

@[simp]
lemma mem_orbitClosure {x y : ℤ → α} :
    y ∈ orbitClosure x ↔ y ∈ closure (Set.range fun g : ℤ => shift g x) := Iff.rfl

lemma self_mem_orbitClosure (x : ℤ → α) : x ∈ orbitClosure x :=
  subset_closure ⟨0, shift_zero x⟩

/-- **The orbit closure is the smallest subshift containing the point.**  A subshift is closed and
shift-invariant, so it contains the whole orbit and its closure. -/
lemma orbitClosure_le_of_mem {Y : Subshift α ℤ} {x : ℤ → α} (hx : x ∈ Y) : orbitClosure x ≤ Y := by
  intro y hy
  refine closure_minimal ?_ (isClosed_coe Y) hy
  rintro _ ⟨g, rfl⟩
  exact shift_mem Y g hx

/-- The language of an orbit closure is the set of blocks of the point itself: taking the closure
adds no new finite blocks.  Discreteness is what makes a block a neighbourhood condition. -/
theorem language_orbitClosure [DiscreteTopology α] (x : ℤ → α) (n : ℕ) :
    (orbitClosure x).language n = {v | ∃ i : ℤ, block x n i = v} := by
  ext v
  constructor
  · rintro ⟨y, hy, i, rfl⟩
    obtain ⟨z, ⟨g, rfl⟩, hz⟩ := exists_mem_block_eq_of_mem_closure hy n i
    exact ⟨g + i, by rw [← block_shift]; exact hz⟩
  · rintro ⟨i, rfl⟩
    exact ⟨x, self_mem_orbitClosure x, i, rfl⟩

end OrbitClosure

/-! ## The recurrent language is a language -/

/-- **The recurrent language of a word over a finite alphabet is factorial and extendable.**  The
two truncation clauses hold for any alphabet; the two extension clauses and non-emptiness are the
pigeonhole. -/
theorem isLanguage_recurrentLanguage [Finite α] (u : ℕ → α) :
    IsLanguage (recurrentLanguage u) where
  nonempty n := recurrentLanguage_nonempty u n
  init h := h.init
  tail h := h.tail
  extendRight h := by obtain ⟨w, hw, hwv⟩ := h.extendRight; exact ⟨w, hw, hwv⟩
  extendLeft h := by obtain ⟨w, hw, hwv⟩ := h.extendLeft; exact ⟨w, hw, hwv⟩

/-! ## The `ω`-limit subshift -/

section OmegaLimit

variable [TopologicalSpace α] [DiscreteTopology α]

/-- **The `ω`-limit subshift `Ω u` of a one-sided word**: the configurations all of whose blocks
recur in `u`.  Defined by its language; `coe_omegaLimitSubshift_eq_omegaLimit` identifies it with
the topological `ω`-limit set of any two-sided extension of `u`. -/
def omegaLimitSubshift (u : ℕ → α) : Subshift α ℤ := ofLanguage (recurrentLanguage u)

@[simp]
lemma mem_omegaLimitSubshift {u : ℕ → α} {x : ℤ → α} :
    x ∈ omegaLimitSubshift u ↔ ∀ (n : ℕ) (i : ℤ), IsRecurrentFactor u n (block x n i) :=
  mem_ofLanguage

/-- **The language of `Ω u` is the recurrent language of `u`.**  The inclusion with content is
`⊇`: a block recurring in `u` must be realised by an actual configuration of `Ω u`, which is the
compactness argument of `language_ofLanguage`. -/
theorem language_omegaLimitSubshift [Finite α] (u : ℕ → α) (n : ℕ) :
    (omegaLimitSubshift u).language n = recurrentLanguage u n :=
  language_ofLanguage (isLanguage_recurrentLanguage u) n

/-- Over a finite alphabet `Ω u` is never empty. -/
theorem omegaLimitSubshift_nonempty [Finite α] (u : ℕ → α) :
    (omegaLimitSubshift u : Set (ℤ → α)).Nonempty := by
  obtain ⟨v, hv⟩ := recurrentLanguage_nonempty u 0
  rw [← language_omegaLimitSubshift u 0] at hv
  obtain ⟨x, hx, -⟩ := Subshift.mem_language.mp hv
  exact ⟨x, hx⟩

/-- **`Ω` forgets the head of the word.**  Discarding any finite prefix leaves `Ω u` unchanged. -/
theorem omegaLimitSubshift_tail (u : ℕ → α) (m : ℕ) :
    omegaLimitSubshift (fun k => u (m + k)) = omegaLimitSubshift u := by
  unfold omegaLimitSubshift
  congr 1
  funext n
  exact recurrentLanguage_tail u m n

end OmegaLimit

/-! ## Two-sided extensions and the topological identity -/

section Extension

variable [TopologicalSpace α]

/-- `x : ℤ → α` is a **two-sided extension** of the one-sided word `u` when the two agree on
`ℕ ⊆ ℤ`.  Nothing is asked of `x` on the negative half-line. -/
def IsTwoSidedExtension (x : ℤ → α) (u : ℕ → α) : Prop := ∀ k : ℕ, x (k : ℤ) = u k

omit [TopologicalSpace α] in
/-- Every one-sided word over a non-empty alphabet has a two-sided extension. -/
lemma exists_isTwoSidedExtension [Nonempty α] (u : ℕ → α) :
    ∃ x : ℤ → α, IsTwoSidedExtension x u :=
  ⟨fun j => if 0 ≤ j then u j.toNat else Classical.arbitrary α, fun k => by simp⟩

omit [TopologicalSpace α] in
/-- Blocks of a two-sided extension at non-negative positions are factors of the word. -/
lemma block_natCast_eq_factor {x : ℤ → α} {u : ℕ → α} (hx : IsTwoSidedExtension x u) (n j : ℕ) :
    block x n (j : ℤ) = factor u n j := by
  funext s
  simp only [block_apply, factor]
  rw [show (j : ℤ) + ((s : ℕ) : ℤ) = ((j + (s : ℕ) : ℕ) : ℤ) by push_cast; ring]
  exact hx _

/-- Membership in an `atTop` `ω`-limit of a single point, unfolded to a family of closure
conditions on the tails of the forward orbit.  This is just `mem_closure_iff_nhds` and
`frequently_atTop` with the two universal quantifiers exchanged. -/
lemma mem_omegaLimit_shift_singleton_iff (x y : ℤ → α) :
    y ∈ omegaLimit Filter.atTop (fun m : ℕ => (shift (m : ℤ) : (ℤ → α) → ℤ → α)) {x} ↔
      ∀ N : ℕ, y ∈ closure ((fun m : ℕ => shift (m : ℤ) x) '' Set.Ici N) := by
  rw [mem_omegaLimit_singleton_iff_mapClusterPt, mapClusterPt_iff_frequently]
  constructor
  · intro h N
    rw [mem_closure_iff_nhds]
    intro V hV
    obtain ⟨m, hm, hmV⟩ := Filter.frequently_atTop.mp (h V hV) N
    exact ⟨shift (m : ℤ) x, hmV, ⟨m, Set.mem_Ici.mpr hm, rfl⟩⟩
  · intro h V hV
    rw [Filter.frequently_atTop]
    intro N
    obtain ⟨z, hzV, ⟨m, hm, rfl⟩⟩ := mem_closure_iff_nhds.mp (h N) V hV
    exact ⟨m, Set.mem_Ici.mp hm, hzV⟩

variable [DiscreteTopology α]

/-- **The `ω`-limit subshift is the `ω`-limit set.**  For any two-sided extension `x` of `u`, the
carrier of `Ω u` is Mathlib's `omegaLimit atTop (shift ·) {x}`.

Both inclusions are the same dictionary read in opposite directions: a block of `y` recurs in `u`
exactly when arbitrarily late forward shifts of `x` agree with `y` along that block.  Finiteness
of the alphabet plays no part; only discreteness, which is what makes agreement along a block a
neighbourhood condition. -/
theorem coe_omegaLimitSubshift_eq_omegaLimit (u : ℕ → α) {x : ℤ → α}
    (hx : IsTwoSidedExtension x u) :
    (omegaLimitSubshift u : Set (ℤ → α))
      = omegaLimit Filter.atTop (fun m : ℕ => (shift (m : ℤ) : (ℤ → α) → ℤ → α)) {x} := by
  ext y
  rw [SetLike.mem_coe, mem_omegaLimitSubshift, mem_omegaLimit_shift_singleton_iff]
  constructor
  · intro hy N
    refine mem_closure_of_forall_exists_block_eq fun n i => ?_
    obtain ⟨j, hj, hfj⟩ := hy n i (N + i.natAbs)
    refine ⟨shift ((((j : ℤ) - i).toNat : ℕ) : ℤ) x,
      ⟨((j : ℤ) - i).toNat, Set.mem_Ici.mpr (by omega), rfl⟩, ?_⟩
    rw [block_shift, show ((((j : ℤ) - i).toNat : ℕ) : ℤ) + i = (j : ℤ) by omega,
      block_natCast_eq_factor hx, hfj]
  · intro hy n i N
    obtain ⟨z, ⟨m, hm, rfl⟩, hz⟩ :=
      exists_mem_block_eq_of_mem_closure (hy (N + i.natAbs)) n i
    have hm' : N + i.natAbs ≤ m := Set.mem_Ici.mp hm
    refine ⟨((m : ℤ) + i).toNat, by omega, ?_⟩
    rw [← block_natCast_eq_factor hx,
      show ((((m : ℤ) + i).toNat : ℕ) : ℤ) = (m : ℤ) + i by omega, ← block_shift]
    exact hz

/-- The `ω`-limit set of a two-sided extension does not depend on the extension chosen — the
formal content of "`Ω` only sees the tail of `u`". -/
theorem omegaLimit_eq_of_isTwoSidedExtension {u : ℕ → α} {x x' : ℤ → α}
    (hx : IsTwoSidedExtension x u) (hx' : IsTwoSidedExtension x' u) :
    omegaLimit Filter.atTop (fun m : ℕ => (shift (m : ℤ) : (ℤ → α) → ℤ → α)) {x}
      = omegaLimit Filter.atTop (fun m : ℕ => (shift (m : ℤ) : (ℤ → α) → ℤ → α)) {x'} :=
  (coe_omegaLimitSubshift_eq_omegaLimit u hx).symm.trans
    (coe_omegaLimitSubshift_eq_omegaLimit u hx')

/-- `Ω u` sits inside the orbit closure of any two-sided extension. -/
theorem omegaLimitSubshift_le_orbitClosure [Finite α] (u : ℕ → α) {x : ℤ → α}
    (hx : IsTwoSidedExtension x u) : omegaLimitSubshift u ≤ orbitClosure x := by
  refine Subshift.le_of_language_subset fun n => ?_
  rw [language_omegaLimitSubshift, language_orbitClosure]
  intro v hv
  obtain ⟨j, hj⟩ := IsRecurrentFactor.exists_eq hv
  exact ⟨(j : ℤ), by rw [block_natCast_eq_factor hx]; exact hj⟩

end Extension

end SymbolicDynamics.FullShift
