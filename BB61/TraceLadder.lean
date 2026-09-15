/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.Ladder
import ForMathlib.NumberTheory.TraceLadder
import Mathlib.Tactic.ComputeDegree
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# M1 Proposition 15: the trace ladder is the whole codifferent

Formal companion of `note-1061-M1.html` §6, Proposition 15 — the statement that settles M0's
open normalisation question and reopens it as a quantitative one.

> **Proposition 15.** Let `𝓡 = {(h_k) ∈ ℤ^{ℕ₀} : h_{k+d} + c₁h_{k+d-1} + ⋯ + c_d h_k = 0}` be
> the integer sequences obeying `α`'s recurrence.  Then
> `𝓡 = {(Tr(λ αᵏ))_{k≥0} : λ ∈ 𝔡⁻¹ = f'(α)⁻¹ℤ[α]}`, and `λ ↦ (h_k)` is a `ℤ`-module
> isomorphism `𝔡⁻¹ ≅ 𝓡 ≅ ℤ^d`.

The mathematics is `ForMathlib/NumberTheory/TraceLadder.lean`, stated there for any algebraic
integer generating a number field — which is the note's own generality, the note working in
`K_f = ℚ(α)`.  This file records the statements under the corpus attributes and connects them
to the degree-two ladder `QuadSetup.lad` that `BB61/Ladder.lean` (M7) runs on.

## What the proof needs, and what it does not

The note's proof is three steps, and they are proved separately upstream because they need
different inputs.

* **The recurrence** holds for *every* `λ ∈ K_f`, integrality nowhere in sight.  The note says
  "since each `α_jᵏ` does"; that is a detour through a splitting field and is not needed —
  `∑ᵢ fᵢ αⁱ = f(α) = 0` in `K_f` itself, and the trace is linear (`recurrence_of_trace_ladder`).
* **Integrality** is where the codifferent enters, and once one knows `ℤ[α]` is spanned by the
  powers of `α` it is a tautology: `Tr(λ αᵏ) ∈ ℤ` for every `k` *is* `Tr(λ ℤ[α]) ⊆ ℤ`
  (`mem_codifferent_iff`).  The note's "iff `Tr(λ αᵏ) ∈ ℤ` for `0 ≤ k ≤ d-1`" is the forward
  propagation of integrality along a *monic* recurrence.
* **Surjectivity** is the nondegeneracy of the trace form, exactly as the note says.

`codifferent_eq_smul_adjoin` is **Euler's identity** `𝔡⁻¹ = f'(α)⁻¹ℤ[α]` — the note derives it
from `Tr(αⁱ/f'(α)) = δ_{i,d-1}`; it is in Mathlib as `traceForm_dualSubmodule_adjoin`, and it is
the only part of §6 that is not elementary.

## Main results

* `recurrence_of_trace_ladder`, `mem_codifferent_iff` — the two halves of the correspondence;
* `integer_recurrence_iff_trace_ladder` — **Proposition 15**, `𝓡 = {(Tr(λ αᵏ)) : λ ∈ 𝔡⁻¹}`;
* `codifferentEquivLadders`, `laddersEquivInit` — `𝔡⁻¹ ≃ₗ[ℤ] 𝓡 ≃ₗ[ℤ] ℤ^d`;
* `codifferent_eq_smul_adjoin` — Euler's identity;
* `QuadSetup.recModule_eq_range_lad` and `QuadSetup.lad_iff_trace_ladder` — the degree-two
  bridge: the M7 ladders `lad P h₀ h₁` are *exactly* `𝓡` at `d = 2`, hence exactly the trace
  ladders over the codifferent of any root of `X² - aX - b`.

## References

* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, CUP 2012,
  Problem 10.61.
* `note-1061-M1.html` §6 (Proposition 15 and the keyfact box that follows it: the ladder is the
  whole module, and the choice of `λ` inside it is worth a factor `452` at `1 + √2`).
  Numerical check: `BB61/m1_field.py` (the codifferent test), `BB61/m1_verify.py` row **P15**.
-/

open Polynomial TraceLadder Pointwise

namespace BB61

/-! ## Proposition 15 -/

section Prop15

variable {L : Type*} [Field L] [NumberField L] {α : L}

/-- **M1 Proposition 15**, the recurrence half: `k ↦ Tr(λ αᵏ)` obeys `α`'s recurrence for
*every* `λ`, integrality nowhere involved. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem recurrence_of_trace_ladder (lam : L) :
    IsRecSeq (minpoly ℤ α) (ladder α lam) :=
  isRecSeq_ladder lam

/-- **M1 Proposition 15**, the integrality half: `λ` lies in the codifferent
`𝔡⁻¹ = {γ : Tr(γ ℤ[α]) ⊆ ℤ}` exactly when its whole trace ladder is integral. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem mem_codifferent_iff {lam : L} :
    lam ∈ codiff α ↔ ∀ k, ladder α lam k ∈ (1 : Submodule ℤ ℚ) :=
  mem_codiff_iff

/-- **M1 Proposition 15**: the integer solutions of `α`'s recurrence are exactly the trace
ladders `h_k = Tr(λ αᵏ)` with `λ` in the codifferent. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem integer_recurrence_iff_trace_ladder (hgen : Algebra.adjoin ℚ ({α} : Set L) = ⊤)
    (hint : IsIntegral ℤ α) (h : ℕ → ℤ) :
    IsRecSeq (minpoly ℤ α) h ↔ ∃ lam ∈ codiff α, ∀ k, ladder α lam k = (h k : ℚ) :=
  isRecSeq_iff_exists_codiff hgen hint h

/-- **M1 Proposition 15**: `λ ↦ (Tr(λ αᵏ))` is a `ℤ`-module isomorphism `𝔡⁻¹ ≅ 𝓡`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
noncomputable def codifferentEquivLadders (hgen : Algebra.adjoin ℚ ({α} : Set L) = ⊤)
    (hint : IsIntegral ℤ α) : codiff α ≃ₗ[ℤ] recModule (minpoly ℤ α) :=
  codiffEquivRec hgen hint

/-- **M1 Proposition 15**: `𝓡 ≅ ℤ^d`, a solution being free on its first `d` terms. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
noncomputable def laddersEquivInit (hgen : Algebra.adjoin ℚ ({α} : Set L) = ⊤)
    (hint : IsIntegral ℤ α) :
    recModule (minpoly ℤ α) ≃ₗ[ℤ] (Fin (minpoly ℤ α).natDegree → ℤ) :=
  recEquivInit hgen hint

/-- **Euler's identity**, M1 §4.1 and §6: the codifferent is `f'(α)⁻¹ℤ[α]`.  This is the one
statement of §6 that is not elementary, and it is in Mathlib. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem codifferent_eq_smul_adjoin (hgen : Algebra.adjoin ℚ ({α} : Set L) = ⊤)
    (hint : IsIntegral ℤ α) :
    codiff α = (aeval α (derivative (minpoly ℚ α)))⁻¹ •
      Subalgebra.toSubmodule (Algebra.adjoin ℤ ({α} : Set L)) :=
  codiff_eq_smul_adjoin hgen hint

end Prop15

/-! ## The degree-two bridge to `BB61/Ladder.lean` -/

namespace QuadSetup

variable (P : QuadSetup)

/-- `X² - aX - b`, the characteristic polynomial of the degree-two setting. -/
noncomputable def charPoly : ℤ[X] := X ^ 2 - C P.a * X - C P.b

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem charPoly_monic : P.charPoly.Monic := by
  unfold charPoly; monicity!

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem natDegree_charPoly : P.charPoly.natDegree = 2 := by
  unfold charPoly; compute_degree!

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem coeff_charPoly_zero : P.charPoly.coeff 0 = -P.b := by
  simp only [charPoly, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C]
  norm_num

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem coeff_charPoly_one : P.charPoly.coeff 1 = -P.a := by
  simp only [charPoly, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C]
  norm_num

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem coeff_charPoly_two : P.charPoly.coeff 2 = 1 := by
  simp only [charPoly, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C]
  norm_num

variable {P}

/-- The M7 ladder obeys the degree-two recurrence. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isRecSeq_lad (h₀ h₁ : ℤ) : IsRecSeq P.charPoly (P.lad h₀ h₁) := by
  intro k
  rw [natDegree_charPoly]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    coeff_charPoly_zero, coeff_charPoly_one, coeff_charPoly_two]
  simp only [Nat.add_zero, smul_eq_mul, one_mul, neg_mul, lad_add_two]
  ring

/-- Conversely every integer solution is an M7 ladder, namely the one started at its own first
two terms. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem eq_lad_of_isRecSeq {h : ℕ → ℤ} (hh : IsRecSeq P.charPoly h) :
    h = P.lad (h 0) (h 1) := by
  refine hh.ext (charPoly_monic P) (isRecSeq_lad _ _) fun i hi => ?_
  rw [natDegree_charPoly] at hi
  interval_cases i
  · rw [lad_zero]
  · rw [lad_one]

/-- **`𝓡` at degree two is exactly the set of M7 ladders.** -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem recModule_eq_range_lad :
    (recModule P.charPoly : Set (ℕ → ℤ)) = Set.range fun v : ℤ × ℤ => P.lad v.1 v.2 := by
  ext h
  constructor
  · intro hh
    exact ⟨(h 0, h 1), (eq_lad_of_isRecSeq (mem_recModule.mp hh)).symm⟩
  · rintro ⟨v, rfl⟩
    exact isRecSeq_lad v.1 v.2

/-- **M1 Proposition 15 at degree two**: if `α` is a root of `X² - aX - b` generating a
quadratic field, the ladders of `BB61/Ladder.lean` are exactly the trace ladders `Tr(λ αᵏ)`
over the codifferent.  This is the licence for M7's search over `λ ∈ 𝔡⁻¹`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem lad_iff_trace_ladder {L : Type*} [Field L] [NumberField L] {α : L}
    (hgen : Algebra.adjoin ℚ ({α} : Set L) = ⊤) (hint : IsIntegral ℤ α)
    (hmin : minpoly ℤ α = P.charPoly) (h : ℕ → ℤ) :
    (∃ h₀ h₁ : ℤ, h = P.lad h₀ h₁) ↔ ∃ lam ∈ codiff α, ∀ k, ladder α lam k = (h k : ℚ) := by
  rw [← integer_recurrence_iff_trace_ladder hgen hint h, hmin]
  exact ⟨fun ⟨h₀, h₁, hh⟩ => hh ▸ isRecSeq_lad h₀ h₁,
    fun hh => ⟨h 0, h 1, eq_lad_of_isRecSeq hh⟩⟩

end QuadSetup

end BB61
