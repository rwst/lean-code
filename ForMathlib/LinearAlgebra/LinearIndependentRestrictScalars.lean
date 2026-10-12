/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import ArithmeticHeights.Extraction

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

end Selection

section RestrictScalars

variable {F K E V W : Type*}
variable [Field F] [Field K] [Field E]
variable [Algebra F K] [Algebra F E] [FiniteDimensional F K]
variable [AddCommGroup V] [Module F V] [Module K V] [IsScalarTower F K V]
variable [AddCommGroup W] [Module F W] [Module E W] [IsScalarTower F E W]

end RestrictScalars
