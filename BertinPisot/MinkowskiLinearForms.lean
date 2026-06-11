/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Minkowski's linear forms theorem (Bertin §5.2, Theorem 5.2.1)

Bertin's **Theorem 5.2.1** (*Pisot and Salem Numbers* [Ber92], §5.2) — the classical **Minkowski
linear forms theorem** from the geometry of numbers:

> Let `L₁, …, Lₙ` be `n` linear forms in `n` variables with real coefficients whose determinant
> `Δ = det(Lᵢ)` is nonzero, and let `γ₁, …, γₙ` be positive reals with `∏ᵢ γᵢ ≥ |Δ|`. Then there is
> a nonzero integer vector `u ∈ ℤⁿ` with `|Lᵢ(u)| ≤ γᵢ` for all `i`.

The forms are the rows of a real matrix `A`, so `Lᵢ(u) = ∑ⱼ Aᵢⱼ uⱼ` and `Δ = A.det`.

**Status — `cited` axiom (provable from Mathlib, not yet formalized).** Unlike the Rouché-type
statements of §5.2, this is *not* a genuine Mathlib gap: the abstract Minkowski convex-body theorem
is available as `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure` — the
compact, non-strict `≤` form, exactly what the boundary case `∏ᵢ γᵢ = |Δ|` requires. The
linear-forms corollary follows by the standard reduction (see the `informal_result` below): the body
`{x | ∀ i, |Lᵢ(x)| ≤ γᵢ}` is the preimage under `A` of the box `∏ᵢ [-γᵢ, γᵢ]`, a compact, convex,
centrally symmetric set of volume `2ⁿ · ∏ᵢ γᵢ / |Δ| ≥ 2ⁿ`, so Minkowski's theorem (the covolume of
`ℤⁿ` is `1`) yields a nonzero lattice point. Assembling this corollary — linear-map Haar change of
variables (`MeasureTheory.Measure.addHaar_preimage_linearMap`), the box volume, the `ℤⁿ`
fundamental domain, and compactness of the body via invertibility of `A` — is a self-contained
(~200-line) measure-theoretic formalization, recorded here as a `cited` axiom pending that work. The
hypothesis `0 < n` is required: for `n = 0` the only integer vector is `0`, so the statement would be
false.

**Complex coefficients (Bertin's remark following Thm 5.2.1).** Minkowski's theorem stays valid for
forms `Lᵢ` with *complex* coefficients, provided one considers each `Lᵢ` together with its conjugate
form `L̄ᵢ(u) = ∑ⱼ conj(Aᵢⱼ) uⱼ`: one then gets a nonzero integer `u` with `|Lᵢ(u)| ≤ γᵢ` **and**
`|L̄ᵢ(u)| ≤ γᵢ`. The added conjugate bound is automatic, because on an *integer* point `u` the
conjugate form takes the conjugate value, `L̄ᵢ(u) = conj(Lᵢ(u))`, so `|L̄ᵢ(u)| = |Lᵢ(u)|`
(`conj_linearForm_norm_eq` below). This is `minkowski_complex_forms`, **proved** from that identity:
given any integer point realizing the `Lᵢ`-bounds (the content of Thm 5.2.1 for the complex system),
the conjugate bounds hold for free.

*References:*
  - [Ber92] Bertin, Marie José et al. *Pisot and Salem Numbers.* Birkhäuser, 1992. §5.2, Thm 5.2.1.
  - H. Minkowski, *Geometrie der Zahlen.* Teubner, Leipzig, 1896.
-/

open Matrix Finset

namespace Bertin

/- Minkowski's linear forms theorem reduces to the abstract Minkowski convex-body theorem (which
*is* available in Mathlib) applied to the parallelepiped `{x | ∀ i, |Lᵢ(x)| ≤ γᵢ}`, the preimage of
a box under the invertible map `A`. -/
informal_result "minkowski-linear-forms"
  latex "Let $L_1,\\dots,L_n$ be linear forms with real coefficients and nonzero determinant $\\Delta$, and let $\\gamma_1,\\dots,\\gamma_n>0$ with $\\prod_i\\gamma_i\\ge|\\Delta|$. Writing $L_i(x)=\\sum_j A_{ij}x_j$ with $\\det A=\\Delta$, the set $C=\\{x\\in\\mathbb{R}^n:|L_i(x)|\\le\\gamma_i\\ \\forall i\\}=A^{-1}\\big(\\prod_i[-\\gamma_i,\\gamma_i]\\big)$ is compact, convex and centrally symmetric, with volume $\\operatorname{vol}(C)=|\\Delta|^{-1}\\prod_i(2\\gamma_i)=2^n|\\Delta|^{-1}\\prod_i\\gamma_i\\ge 2^n$. Since $\\mathbb{Z}^n$ has covolume $1$, Minkowski's convex-body theorem in its closed (non-strict) form $\\operatorname{vol}(C)\\ge 2^n$ yields a nonzero $u\\in\\mathbb{Z}^n\\cap C$, i.e. $|L_i(u)|\\le\\gamma_i$ for all $i$."
  refs "Ber92"

/-- **Minkowski's linear forms theorem** (Bertin §5.2, Theorem 5.2.1). For `n` linear forms
`Lᵢ(u) = ∑ⱼ Aᵢⱼ uⱼ` with real coefficients and nonzero determinant `Δ = A.det`, and positive reals
`γᵢ` with `∏ᵢ γᵢ ≥ |Δ|`, there is a nonzero `u ∈ ℤⁿ` with `|Lᵢ(u)| ≤ γᵢ` for every `i`.

Provable from Mathlib's convex-body theorem
(`MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure`) via the convex-body
reduction recorded in the `informal_result` `"minkowski-linear-forms"`; kept here as a `cited` axiom
pending that (self-contained, measure-theoretic) formalization. The hypothesis `0 < n` is necessary —
for `n = 0` no nonzero integer vector exists. -/
@[category research solved, AMS 11, ref "Ber92", informal_uses "minkowski-linear-forms"]
axiom minkowski_linear_forms {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.det ≠ 0) (γ : Fin n → ℝ) (hγ : ∀ i, 0 < γ i) (hprod : |A.det| ≤ ∏ i, γ i) :
    ∃ u : Fin n → ℤ, u ≠ 0 ∧ ∀ i, |∑ j, A i j * (u j : ℝ)| ≤ γ i

/-- On an integer point, a complex linear form and its conjugate-coefficient form have equal
modulus: `‖∑ⱼ conj(Aᵢⱼ) uⱼ‖ = ‖∑ⱼ Aᵢⱼ uⱼ‖` (because `uⱼ ∈ ℤ` is fixed by conjugation, so the
conjugate form takes the conjugate value). This is the elementary fact behind Bertin's complex
extension of Theorem 5.2.1. -/
private lemma conj_linearForm_norm_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℤ)
    (i : Fin n) :
    ‖∑ j, (starRingEnd ℂ) (A i j) * (u j : ℂ)‖ = ‖∑ j, A i j * (u j : ℂ)‖ := by
  have key : (∑ j, (starRingEnd ℂ) (A i j) * (u j : ℂ))
      = (starRingEnd ℂ) (∑ j, A i j * (u j : ℂ)) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [map_mul, map_intCast])
  rw [key, RCLike.norm_conj]

/-- **Minkowski's theorem for complex forms** (Bertin §5.2, the remark after Thm 5.2.1). If `n`
complex linear forms `Lᵢ(u) = ∑ⱼ Aᵢⱼ uⱼ` admit a nonzero integer point `u` with `|Lᵢ(u)| ≤ γᵢ` for
all `i` (the conclusion of Theorem 5.2.1 applied to the complex system), then that same `u`
simultaneously satisfies the conjugate-form bounds `|L̄ᵢ(u)| ≤ γᵢ`, where `L̄ᵢ(u) = ∑ⱼ conj(Aᵢⱼ) uⱼ`.
Indeed `|L̄ᵢ(u)| = |Lᵢ(u)|` on integer points (`conj_linearForm_norm_eq`), so the conjugate bounds
are free. Thus Minkowski's theorem "remains valid" for complex coefficients once each `Lᵢ` is paired
with its conjugate `L̄ᵢ`. -/
@[category research solved, AMS 11, ref "Ber92"]
theorem minkowski_complex_forms {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (γ : Fin n → ℝ)
    (hex : ∃ u : Fin n → ℤ, u ≠ 0 ∧ ∀ i, ‖∑ j, A i j * (u j : ℂ)‖ ≤ γ i) :
    ∃ u : Fin n → ℤ, u ≠ 0 ∧ (∀ i, ‖∑ j, A i j * (u j : ℂ)‖ ≤ γ i) ∧
      (∀ i, ‖∑ j, (starRingEnd ℂ) (A i j) * (u j : ℂ)‖ ≤ γ i) := by
  obtain ⟨u, hu, hb⟩ := hex
  exact ⟨u, hu, hb, fun i => (conj_linearForm_norm_eq A u i).le.trans (hb i)⟩

end Bertin
