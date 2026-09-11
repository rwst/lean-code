/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Linear independence through restriction of scalars

Let `F ⊆ K` be a finite field extension of degree `d = finrank F K`, let `V` be a `K`-vector
space, and let `f : V →ₗ[F] W` be an `F`-linear map into a vector space `W` over a third field
`E ⊇ F`.  If the images `f (u i)` of a finite family `u : ι → V` are linearly independent *over
`E`*, then the family `u` spans a `K`-subspace of dimension at least `card ι / d`:

* `LinearIndependent.fintype_card_le_finrank_mul_finrank_span` —
  `card ι ≤ d * finrank K (span K (range u))`.

The reason is one line: `span K (range u)` has `F`-dimension `d * finrank K (span K (range u))`
by the tower law, and its image under `f` spans over `E` a subspace of at most that dimension,
which must accommodate `card ι` independent vectors.

On top of it we prove a greedy selection lemma, pure linear algebra over one field:

* `exists_linearIndependent_comp_of_lt_finrank_span` — if the first `m j + 1` vectors of
  `u : Fin n → V` span a subspace of `K`-dimension `> j` for each `j < k`, then some
  subfamily `u ∘ s` with `(s j : ℕ) ≤ m j` is `K`-linearly independent — the selected vectors
  are *members* of the family, not merely combinations of it;

and the combination of the two:

* `LinearIndependent.exists_linearIndependent_comp_finrank_mul` — from
  `u : Fin (d * k) → V` with `f ∘ u` linearly independent over `E`, a `K`-linearly independent
  subfamily `u ∘ s` of size `k` with `(s j : ℕ) ≤ d * j`.

## Why this is stated this way (Siegel's lemma without adèles)

This is the extraction step of the *real* route to the Bombieri–Vaaler refinement of Siegel's
lemma (Bombieri–Vaaler, *On Siegel's lemma*, Invent. Math. 73 (1983); Bombieri–Gubler, *Heights
in Diophantine Geometry*, Thm 2.9.4).  There `F = ℚ`, `K` is a number field of degree `d`,
`V = Kᴺ`, `E = ℝ`, and `f` is the canonical (Minkowski) embedding into
`(K ⊗_ℚ ℝ)ᴺ ≃ ℝ^{dN}`.  Minkowski's second theorem, applied to the `ℤ`-lattice
`σ(V₀ ∩ 𝓞_Kᴺ)` of a solution space `V₀` of `K`-dimension `k`, produces `d·k` lattice vectors
`u 0, …, u (d·k − 1)`, independent over `ℝ` and ordered by the successive minima
`λ 1 ≤ ⋯ ≤ λ (d·k)`.  Bombieri and Vaaler pass to the adèles precisely because over `𝓞_K`
(not a PID in general) one cannot triangularize a sublattice to convert these into `k` vectors
independent over `K` with the minima still controlled (§I.3 of their paper).  The lemmas here
recover that conversion with no adelic input and no loss:

* the corollary yields `y j := u (s j)`, independent over `K`, with `s j ≤ d * j`, hence with
  all archimedean norms at most `λ (d·j + 1)`; and
* since the minima are nondecreasing, `λ (d·j + 1) ^ d ≤ ∏_{r = 1}^{d} λ (d·j + r)`, so
  `∏_j H(y j) ≤ ∏_i λ i` — the full product Minkowski's second theorem bounds.

The selected vectors being members of the original family is what makes the height bound
possible: a `K`-linear combination of lattice vectors has no controlled norm, a *chosen* lattice
vector keeps the norm bound it arrived with.
-/

open Module Submodule

section Selection

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Greedy selection of an independent subfamily under prescribed index bounds.  If for each
`j < k` the vectors of `u` with index at most `m j` span a subspace of dimension greater than
`j`, then there is a `K`-linearly independent subfamily `u ∘ s` of size `k` with
`(s j : ℕ) ≤ m j` for every `j`.  The bound function `m` need not be monotone.  Note the
conclusion picks *members* of the family: `u (s j)`, not a linear combination. -/
theorem exists_linearIndependent_comp_of_lt_finrank_span
    {n : ℕ} (u : Fin n → V) {k : ℕ} (m : Fin k → ℕ)
    (hm : ∀ j : Fin k, j.val < finrank K (span K (u '' {i : Fin n | i.val ≤ m j}))) :
    ∃ s : Fin k → Fin n, LinearIndependent K (u ∘ s) ∧ ∀ j : Fin k, (s j).val ≤ m j := by
  induction k with
  | zero => exact ⟨Fin.elim0, linearIndependent_empty_type, fun j => j.elim0⟩
  | succ k ih =>
    obtain ⟨s', hs'ind, hs'le⟩ := ih (m ∘ Fin.castSucc) fun j => hm j.castSucc
    -- Some `u i` with `i ≤ m (last k)` avoids the span of the vectors selected so far, since
    -- that span has dimension at most `k` while the first `m (last k) + 1` vectors span more.
    have hex : ∃ i : Fin n, i.val ≤ m (Fin.last k) ∧
        u i ∉ span K (Set.range (u ∘ s')) := by
      by_contra hcon
      push Not at hcon
      have hsub : span K (u '' {i : Fin n | i.val ≤ m (Fin.last k)}) ≤
          span K (Set.range (u ∘ s')) := by
        rw [span_le]
        rintro _ ⟨i, hi, rfl⟩
        exact hcon i hi
      have hfin : Module.Finite K (span K (Set.range (u ∘ s'))) :=
        FiniteDimensional.span_of_finite K (Set.finite_range _)
      have h1 : finrank K (span K (u '' {i : Fin n | i.val ≤ m (Fin.last k)})) ≤
          finrank K (span K (Set.range (u ∘ s'))) :=
        Submodule.finrank_mono hsub
      have h2 : finrank K (span K (Set.range (u ∘ s'))) ≤ k := by
        classical
        calc finrank K (span K (Set.range (u ∘ s')))
            ≤ (Set.range (u ∘ s')).toFinset.card := finrank_span_le_card _
          _ ≤ Fintype.card (Fin k) := by
              rw [Set.toFinset_range]; exact Finset.card_image_le.trans (by simp)
          _ = k := by simp
      have h3 := hm (Fin.last k)
      rw [Fin.val_last] at h3
      omega
    obtain ⟨i, hile, hinot⟩ := hex
    refine ⟨Fin.snoc s' i, ?_, ?_⟩
    · have hcomp : u ∘ Fin.snoc s' i = Fin.snoc (u ∘ s') (u i) := Fin.comp_snoc u s' i
      rw [hcomp]
      exact linearIndependent_finSnoc.mpr ⟨hs'ind, hinot⟩
    · intro j
      induction j using Fin.lastCases with
      | last => simpa using hile
      | cast j' => simpa using hs'le j'

end Selection

section RestrictScalars

variable {F K E V W : Type*}
variable [Field F] [Field K] [Field E]
variable [Algebra F K] [Algebra F E] [FiniteDimensional F K]
variable [AddCommGroup V] [Module F V] [Module K V] [IsScalarTower F K V]
variable [AddCommGroup W] [Module F W] [Module E W] [IsScalarTower F E W]

/-- A family of vectors of a `K`-vector space whose image under an `F`-linear map is linearly
independent over a field `E ⊇ F` has size at most `finrank F K` times the `K`-dimension of its
span.  With `F = ℚ`, `K` a number field, `E = ℝ` and `f` the canonical embedding: `ℝ`-linearly
independent lattice vectors of a `K`-solution space span, over `K`, a subspace of dimension at
least their number divided by the degree. -/
theorem LinearIndependent.fintype_card_le_finrank_mul_finrank_span
    (f : V →ₗ[F] W) {ι : Type*} [Fintype ι] {u : ι → V}
    (h : LinearIndependent E (f ∘ u)) :
    Fintype.card ι ≤ finrank F K * finrank K (span K (Set.range u)) := by
  classical
  set S : Submodule K V := span K (Set.range u) with hS
  have : Module.Finite K S := FiniteDimensional.span_of_finite K (Set.finite_range u)
  have : Module.Finite F S := Module.Finite.trans K S
  -- The `F`-linear restriction of `f` to `S`, whose range contains every `f (u i)`.
  let g : S →ₗ[F] W := f.comp ((S.subtype).restrictScalars F)
  let b := Module.finBasis F S
  -- Everything in `g '' S` is an `E`-combination of the `finrank F S` vectors `g (b j)`,
  -- because `F`-scalars act through `E` by the tower `F ⊆ E`.
  have hg : ∀ s : S, g s ∈ span E (Set.range (g ∘ b)) := by
    intro s
    have hs := b.sum_repr s
    have hsum : g s = ∑ j, b.repr s j • g (b j) := by
      conv_lhs => rw [← hs, map_sum]
      simp only [map_smul]
    rw [hsum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [← algebraMap_smul E (b.repr s j) (g (b j))]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hmem : ∀ i, (f ∘ u) i ∈ span E (Set.range (g ∘ b)) := by
    intro i
    have hui : u i ∈ S := subset_span (Set.mem_range_self i)
    simpa [g] using hg ⟨u i, hui⟩
  have h1 : Fintype.card ι = finrank E (span E (Set.range (f ∘ u))) :=
    (finrank_span_eq_card h).symm
  have h2 : span E (Set.range (f ∘ u)) ≤ span E (Set.range (g ∘ b)) := by
    rw [span_le]; rintro _ ⟨i, rfl⟩; exact hmem i
  have : Module.Finite E (span E (Set.range (g ∘ b))) :=
    FiniteDimensional.span_of_finite E (Set.finite_range _)
  have h3 : finrank E (span E (Set.range (f ∘ u))) ≤ finrank E (span E (Set.range (g ∘ b))) :=
    Submodule.finrank_mono h2
  have h4 : finrank E (span E (Set.range (g ∘ b))) ≤ finrank F S := by
    have hle := finrank_span_le_card (R := E) (Set.range (g ∘ b))
    calc finrank E (span E (Set.range (g ∘ b))) ≤ (Set.range (g ∘ b)).toFinset.card := hle
      _ ≤ Fintype.card (Fin (finrank F S)) := by
          rw [Set.toFinset_range]; exact Finset.card_image_le.trans (by simp)
      _ = finrank F S := by simp
  have h5 : finrank F K * finrank K S = finrank F S := Module.finrank_mul_finrank F K S
  omega

/-- **The extraction step of the non-adelic route to Bombieri–Vaaler.**  Let `d = finrank F K`.
From `d * k` vectors of a `K`-vector space whose images under an `F`-linear map `f` are linearly
independent over `E ⊇ F`, one can select `k` of them, linearly independent over `K`, the `j`-th
chosen among the first `d * j + 1` (indices `0, …, d * j`).  Applied to the vectors realizing the
successive minima `λ 1 ≤ ⋯ ≤ λ (d·k)` of a lattice `σ(V₀ ∩ 𝓞_Kᴺ)` under the canonical
embedding `σ`, it yields a `K`-basis of the solution space `V₀` with `j`-th height at most
`λ (d·j + 1) ^ d`, whose product `∏_j λ (d·j + 1) ^ d ≤ ∏_i λ i` is exactly the quantity
Minkowski's second theorem bounds — the conversion Bombieri and Vaaler perform adelically. -/
theorem LinearIndependent.exists_linearIndependent_comp_finrank_mul
    (f : V →ₗ[F] W) {k : ℕ} {u : Fin (finrank F K * k) → V}
    (h : LinearIndependent E (f ∘ u)) :
    ∃ s : Fin k → Fin (finrank F K * k), LinearIndependent K (u ∘ s) ∧
      ∀ j : Fin k, (s j).val ≤ finrank F K * j.val := by
  have hd1 : 1 ≤ finrank F K := Module.finrank_pos
  refine exists_linearIndependent_comp_of_lt_finrank_span u (fun j => finrank F K * j.val) ?_
  intro j
  have hjk : j.val + 1 ≤ k := j.isLt
  have hjn : finrank F K * j.val + 1 ≤ finrank F K * k := by
    calc finrank F K * j.val + 1 ≤ finrank F K * j.val + finrank F K := by omega
      _ = finrank F K * (j.val + 1) := by rw [Nat.mul_succ]
      _ ≤ finrank F K * k := Nat.mul_le_mul_left _ hjk
  -- Restrict to the first `d * j + 1` vectors and apply the counting theorem.
  let e : Fin (finrank F K * j.val + 1) → Fin (finrank F K * k) :=
    fun i => ⟨i.val, lt_of_lt_of_le i.isLt hjn⟩
  have he : Function.Injective e := by
    intro a b hab
    simpa [e, Fin.ext_iff] using hab
  have h' : LinearIndependent E (f ∘ (u ∘ e)) := h.comp e he
  have hker := LinearIndependent.fintype_card_le_finrank_mul_finrank_span (K := K) f h'
  have hrange : Set.range (u ∘ e) =
      u '' {i : Fin (finrank F K * k) | i.val ≤ finrank F K * j.val} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e i, Nat.lt_succ_iff.mp i.isLt, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      refine ⟨⟨i.val, Nat.lt_succ_of_le hi⟩, ?_⟩
      have hei : e ⟨i.val, Nat.lt_succ_of_le hi⟩ = i := Fin.ext rfl
      rw [Function.comp_apply, hei]
  rw [hrange, Fintype.card_fin] at hker
  by_contra hcon
  push Not at hcon
  have hmul : finrank F K * finrank K (span K
      (u '' {i : Fin (finrank F K * k) | i.val ≤ finrank F K * j.val})) ≤
      finrank F K * j.val :=
    Nat.mul_le_mul_left _ hcon
  omega

end RestrictScalars
