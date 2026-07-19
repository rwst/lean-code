/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Finite.Basic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Polynomial.ScaleRoots
import ForMathlib.Data.Real.NearestInt
import CITED.CorvajaZannier
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The Corvaja–Zannier Main Theorem (Acta 2004), algebraic-multiplier specialization

The **Main Theorem** of Corvaja–Zannier ([CZ04], p. 2) once more — see
`CITED/CorvajaZannier.lean` for the full quotation — this time specialized with the
multiplier `δ` **algebraic** rather than rational, which is how the source states it:

> Let `Γ ⊂ 𝔸*` be a finitely generated multiplicative group, let `δ ≠ 0` be a fixed
> algebraic number and let `ε > 0`.  Then there are only finitely many pairs
> `(q, u) ∈ ℤ × Γ`, `d := [ℚ(u) : ℚ]`, such that `|δqu| > 1`, `δqu` is **not
> pseudo-Pisot**, and `0 < ‖δqu‖ < H(u)^{-ε} · q^{-d-ε}`.       (1.1)

## Why a second transcription — and why an axiom again

The `δ ∈ ℚ` instance is **derived** from the Subspace Theorem in
`CITED/CorvajaZannierProof.lean` (`CZ.pseudoPisot_approx_of_subspace`, the 2026-07-14
one-axiom refactor).  That derivation is genuinely rational: it runs over the places
`{∞, 2, 3}` of `ℚ` with rational-coefficient linear forms.  For algebraic irrational
`δ` the same argument needs the Subspace Theorem over the number field `ℚ(δ)` — places
above `2`, `3`, `∞`, relative heights, `S`-enlargement at the places where `δ` is not
a unit — a substantial formalization program of its own (the cited
`Subspace.evertseSchlickewei` is already stated over a general number field, so the
axiom side is ready; the *bookkeeping* is not).  Meanwhile the algebraic-`δ` statement
is exactly what [CZ04] prints and proves (Acta Mathematica, **refereed**).  Per the
corpus's layered-QA policy this file therefore records it as a **cited axiom**,
`CZ.pseudoPisot_approx_alg`, in a *new, separate lane*: nothing that previously held
with footprint std3 + `Subspace.evertseSchlickewei` gains this axiom — only the
algebraic-multiplier extension in `RB/AlgebraicKernel.lean` carries it.

Two fidelity anchors:

* the machine-*derived* rational instance is independent evidence for the
  transcription (same clause list, same threshold shape); the specializations below
  only weaken the printed statement;
* over `ℚ` the spelled-out pseudo-Pisot predicate of this file collapses to the
  `∉ ℤ` clause used there (`CZ.isPseudoPisot_ratCast_iff`), so the two transcriptions
  cohere on their overlap.

## Statement conventions

As in `CITED/CorvajaZannier.lean` (all safe weakenings of the source): `Γ = ⟨2, 3⟩ ≤ ℚ*`
exponent-encoded (so `d = [ℚ(u) : ℚ] = 1` and the `q`-tax is `q^{-1-ε}`), `q ≥ 1`,
height `H(u) = CZ.height23`.  Differences:

* **Multiplier**: `δ : ℝ` with `IsAlgebraic ℚ δ`, `δ ≠ 0`.  ([CZ04] allows any algebraic
  `δ`; restricting to the real ones is a weakening.  For `‖·‖` to make sense the value
  `δqu` must be real, which it is: `u ∈ ℚ`.)
* **Norm**: `‖·‖ = distToNearestInt : ℝ → ℝ` (`ForMathlib/Data/Real/NearestInt.lean`) —
  the value `δqu` is now a real number, not a rational.
* **Pseudo-Pisot, spelled out in full** (`CZ.IsPseudoPisot`, [CZ04] Definition p. 2):
  `|α| > 1`, every conjugate of `α` other than `α` itself has modulus `< 1`, and the
  trace (the sum of all conjugates) is a rational integer.  Conjugates are encoded as
  the complex roots of `minpoly ℚ α`, the corpus convention of `BertinPisot/SetSTU.lean`.
  Over `ℚ` the conjugate clause is vacuous and the trace is the number itself, which
  recovers the `∉ ℤ` reading of the sibling file.

The finiteness is **ineffective** (Subspace-based), as before.

## The discharge lemmas

A consumer must refute `IsPseudoPisot (δqu)` along its family.  For the families this
corpus uses — a fixed algebraic irrational `x` times a growing rational `r` — the
conjugate-modulus clause does the work, and the discharge is *provable*:
`minpoly ℚ (r·x) = (minpoly ℚ x).scaleRoots r` (Mathlib's
`IsIntegrallyClosed.minpoly_smul`), so the conjugates of `r·x` are `r` times the
conjugates of `x` (`CZ.aroots_minpoly_ratCast_mul`); an irrational algebraic `x` has a
conjugate `z ≠ x`, `z ≠ 0` (`CZ.exists_conjugate_ne`), and `|r·z| ≥ 1` once
`r ≥ |z|⁻¹` — some conjugate of `r·x` other than `r·x` leaves the unit disc, so `r·x`
is not pseudo-Pisot (`CZ.not_isPseudoPisot_mul_ratCast`).  No number-field machinery
beyond `minpoly` is needed.

## Contents

* `CZ.IsPseudoPisot` — [CZ04]'s pseudo-Pisot predicate, spelled out over `ℝ`.
* `CZ.svalR` — the value `δ·q·2^x·3^y`, now `ℝ`-valued.
* **`CZ.pseudoPisot_approx_alg`** — the Main Theorem, algebraic-`δ` specialization
  (cited `axiom`, the one Diophantine input of `RB/AlgebraicKernel.lean`).
* `CZ.aroots_minpoly_ratCast_mul`, `CZ.exists_conjugate_ne`,
  **`CZ.not_isPseudoPisot_mul_ratCast`** — the (proved) pseudo-Pisot discharge.
* `CZ.isPseudoPisot_ratCast_iff` — coherence with the `δ ∈ ℚ` transcription.

## References

* [CZ04] Corvaja, Pietro, and Umberto Zannier. "On the rational approximations to
  the powers of an algebraic number: solution of two problems of Mahler and
  Mendès France." *Acta Mathematica* **193** (2004), 175–191. arXiv `math/0403522`.
  (Main Theorem and Definition, p. 2.)
* `CITED/CorvajaZannier.lean`, `CITED/CorvajaZannierProof.lean` — the `δ ∈ ℚ`
  instance, derived from `Subspace.evertseSchlickewei`.
* [B1E2] `plans/plan-B1E2.html`; `plans/report2-B1E2.html` **S13** (the
  algebraic-multiplier program this file opens).
-/

namespace CZ

/-! ## The pseudo-Pisot predicate, spelled out -/

/-- **Pseudo-Pisot** ([CZ04] Definition, p. 2): a real `α` with `|α| > 1`, algebraic
over `ℚ`, all of whose conjugates other than `α` itself have modulus `< 1`, and whose
trace — the sum of all conjugates, i.e. of the complex roots of `minpoly ℚ α` — is a
rational integer.  (A pseudo-Pisot number need *not* be an algebraic integer; Pisot
numbers are exactly the pseudo-Pisot algebraic integers `> 1`.)  Conjugates-as-`aroots`
is the corpus convention of `BertinPisot/SetSTU.lean`. -/
@[category API, AMS 11, ref "CZ04", group "rb_rational_base"]
def IsPseudoPisot (v : ℝ) : Prop :=
  1 < |v| ∧ IsAlgebraic ℚ v ∧
    (∀ z ∈ (minpoly ℚ v).aroots ℂ, z ≠ (v : ℂ) → ‖z‖ < 1) ∧
    ∃ n : ℤ, ((minpoly ℚ v).aroots ℂ).sum = (n : ℂ)

/-- The value `δ·q·u` of the Main Theorem under the exponent encoding `u = 2^x·3^y`
of `Γ = ⟨2, 3⟩` — the `ℝ`-valued sibling of `CZ.sval`, as needed for an algebraic
multiplier `δ`. -/
@[category API, AMS 11, ref "CZ04", group "rb_rational_base"]
noncomputable def svalR (δ : ℝ) (q : ℕ) (x y : ℤ) : ℝ :=
  δ * q * ((2 : ℝ) ^ x * (3 : ℝ) ^ y)

/-! ## The Main Theorem, algebraic-`δ` specialization -/

/-- **The Corvaja–Zannier Main Theorem** ([CZ04] p. 2), specialized to `Γ = ⟨2, 3⟩ ≤ ℚ*`
(exponent-encoded, `d = 1`, `q ≥ 1`) with the multiplier `δ` real **algebraic**: only
finitely many `(q, (x, y))` satisfy `|δqu| > 1`, `δqu` not pseudo-Pisot, and
`0 < ‖δqu‖ < H(u)^{-ε}·q^{-1-ε}`, where `u = 2^x·3^y`.

Recorded as a **cited axiom** on the authority of [CZ04] (Acta Mathematica,
**refereed**) — a new lane, separate from `Subspace.evertseSchlickewei`: see the module
doc for why the algebraic-`δ` case is not (yet) derived, and note that the `δ ∈ ℚ`
instance *is* derived (`CZ.pseudoPisot_approx_of_subspace`), which anchors this
transcription.  The finiteness is ineffective. -/
@[category research solved, AMS 11, ref "CZ04", group "rb_rational_base"]
axiom pseudoPisot_approx_alg (δ : ℝ) (hδalg : IsAlgebraic ℚ δ) (hδ : δ ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    {p : ℕ × ℤ × ℤ | 1 ≤ p.1 ∧
      1 < |svalR δ p.1 p.2.1 p.2.2| ∧
      ¬ IsPseudoPisot (svalR δ p.1 p.2.1 p.2.2) ∧
      0 < distToNearestInt (svalR δ p.1 p.2.1 p.2.2) ∧
      distToNearestInt (svalR δ p.1 p.2.1 p.2.2)
        < (height23 p.2.1 p.2.2 : ℝ) ^ (-ε) * (p.1 : ℝ) ^ (-1 - ε)}.Finite

/-! ## The pseudo-Pisot discharge -/

/-- Conjugates scale along rational multiples: for algebraic `x` and `r ∈ ℚ*`, the
conjugates of `r·x` are exactly `r` times the conjugates of `x`.  Via Mathlib's
`IsIntegrallyClosed.minpoly_smul` (`minpoly ℚ (r • x) = (minpoly ℚ x).scaleRoots r`). -/
@[category API, AMS 11, ref "CZ04", group "rb_rational_base"]
theorem aroots_minpoly_ratCast_mul {x : ℝ} (hx : IsAlgebraic ℚ x) {r : ℚ} (hr : r ≠ 0) :
    (minpoly ℚ ((r : ℝ) * x)).aroots ℂ
      = ((minpoly ℚ x).aroots ℂ).map (fun z => (r : ℂ) * z) := by
  have hint : IsIntegral ℚ x := hx.isIntegral
  have hsmul : (r : ℝ) * x = r • x := (Rat.smul_def r x).symm
  have halg : (algebraMap ℚ ℂ) r = (r : ℂ) := eq_ratCast _ r
  rw [hsmul, IsIntegrallyClosed.minpoly_smul hr hint]
  unfold Polynomial.aroots
  rw [Polynomial.map_scaleRoots _ _ _ (by
    rw [(minpoly.monic hint).leadingCoeff]
    simp), halg]
  exact Polynomial.roots_scaleRoots _
    (isUnit_iff_ne_zero.mpr (by exact_mod_cast hr : ((r : ℚ) : ℂ) ≠ 0))

/-- An **irrational** algebraic real number has a conjugate other than itself, and that
conjugate is nonzero: `minpoly` has degree `≥ 2`, is separable (characteristic `0`), and
has nonzero constant coefficient. -/
@[category API, AMS 11, ref "CZ04", group "rb_rational_base"]
theorem exists_conjugate_ne {x : ℝ} (hx : IsAlgebraic ℚ x) (hirr : Irrational x) :
    ∃ z ∈ (minpoly ℚ x).aroots ℂ, z ≠ (x : ℂ) ∧ z ≠ 0 := by
  have hint : IsIntegral ℚ x := hx.isIntegral
  have hne : minpoly ℚ x ≠ 0 := minpoly.ne_zero hint
  -- degree ≥ 2: degree 1 would make `x` rational
  have hdeg : 2 ≤ (minpoly ℚ x).natDegree := by
    by_contra h
    push Not at h
    have hpos : 0 < (minpoly ℚ x).natDegree := minpoly.natDegree_pos hint
    have h1 : (minpoly ℚ x).natDegree = 1 := by omega
    obtain ⟨q, hq⟩ := minpoly.natDegree_eq_one_iff.mp h1
    rw [eq_ratCast (algebraMap ℚ ℝ) q] at hq
    exact hirr ⟨q, hq⟩
  -- `x` is one of the roots
  have hmem : (x : ℂ) ∈ (minpoly ℚ x).aroots ℂ := by
    rw [Polynomial.mem_aroots]
    refine ⟨hne, ?_⟩
    have h0 := minpoly.aeval ℚ x
    have := Polynomial.aeval_algebraMap_apply ℂ x (minpoly ℚ x)
    rw [h0, map_zero] at this
    simpa using this
  -- the roots are distinct (separability in characteristic 0)
  have hnodup : ((minpoly ℚ x).aroots ℂ).Nodup :=
    Polynomial.nodup_roots ((minpoly.irreducible hint).separable.map)
  -- so a second root exists
  have hcard : ((minpoly ℚ x).aroots ℂ).card = (minpoly ℚ x).natDegree :=
    IsAlgClosed.card_aroots_eq_natDegree
  have herase : 0 < (((minpoly ℚ x).aroots ℂ).erase (x : ℂ)).card := by
    have hce : (((minpoly ℚ x).aroots ℂ).erase (x : ℂ)).card + 1
        = ((minpoly ℚ x).aroots ℂ).card := by
      conv_rhs => rw [← Multiset.cons_erase hmem]
      rw [Multiset.card_cons]
    omega
  obtain ⟨z, hz⟩ := Multiset.card_pos_iff_exists_mem.mp herase
  have hzmem : z ∈ (minpoly ℚ x).aroots ℂ := Multiset.mem_of_mem_erase hz
  have hzne : z ≠ (x : ℂ) := (hnodup.mem_erase_iff.mp hz).1
  refine ⟨z, hzmem, hzne, ?_⟩
  -- a zero root would kill the constant coefficient
  intro h0
  have hx0 : x ≠ 0 := hirr.ne_zero
  have hc0 : (minpoly ℚ x).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hx0
  rw [h0, Polynomial.mem_aroots] at hzmem
  apply hc0
  have := hzmem.2
  rw [Polynomial.aeval_def, Polynomial.eval₂_at_zero,
    eq_ratCast (algebraMap ℚ ℂ) ((minpoly ℚ x).coeff 0)] at this
  exact_mod_cast this

/-- **The discharge**: an irrational algebraic `x` times a large rational `r` is never
pseudo-Pisot — the conjugate `r·z` (with `z` the second conjugate of `x`) leaves the
unit disc as soon as `r ≥ |z|⁻¹`, violating the conjugate-modulus clause.  This is what
a consumer of `pseudoPisot_approx_alg` uses along its family, mirroring how
`CZ.not_intCast_of_distToNearestInt_pos` discharges the clause in the rational case. -/
@[category API, AMS 11, ref "CZ04", group "rb_rational_base"]
theorem not_isPseudoPisot_mul_ratCast {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hirr : Irrational x) :
    ∃ A : ℚ, 0 < A ∧ ∀ r : ℚ, A ≤ r → ¬ IsPseudoPisot (x * r) := by
  obtain ⟨z, hzmem, hzx, hz0⟩ := exists_conjugate_ne hx hirr
  obtain ⟨A, hA⟩ := exists_rat_gt (max 1 ‖z‖⁻¹)
  have hA1 : (1 : ℝ) < A := lt_of_le_of_lt (le_max_left _ _) hA
  have hAz : ‖z‖⁻¹ < (A : ℝ) := lt_of_le_of_lt (le_max_right _ _) hA
  have hA0 : (0 : ℚ) < A := by
    have h01 : (0 : ℝ) < (A : ℝ) := lt_trans zero_lt_one hA1
    exact_mod_cast h01
  refine ⟨A, hA0, ?_⟩
  intro r hAr hPP
  have hrpos : (0 : ℚ) < r := lt_of_lt_of_le hA0 hAr
  have hr0 : r ≠ 0 := hrpos.ne'
  obtain ⟨-, -, hconj, -⟩ := hPP
  -- the scaled conjugate is a conjugate of the scaled number …
  have hmem' : (r : ℂ) * z ∈ (minpoly ℚ (x * r)).aroots ℂ := by
    rw [mul_comm x (r : ℝ), aroots_minpoly_ratCast_mul hx hr0]
    exact Multiset.mem_map_of_mem _ hzmem
  -- … distinct from it …
  have hne' : (r : ℂ) * z ≠ ((x * r : ℝ) : ℂ) := by
    intro h
    have hrC : ((r : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hr0
    exact hzx (mul_left_cancel₀ hrC (h.trans (by push_cast; ring)))
  -- … and outside the unit disc.
  have hbig : (1 : ℝ) ≤ ‖(r : ℂ) * z‖ := by
    rw [norm_mul]
    have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hrA : ‖z‖⁻¹ ≤ (r : ℝ) := le_trans hAz.le (by exact_mod_cast hAr)
    have hnormr : ‖((r : ℚ) : ℂ)‖ = (r : ℝ) := by
      rw [show ((r : ℚ) : ℂ) = ((r : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by exact_mod_cast hrpos)]
    rw [hnormr]
    calc (1 : ℝ) = ‖z‖⁻¹ * ‖z‖ := (inv_mul_cancel₀ hnz.ne').symm
      _ ≤ (r : ℝ) * ‖z‖ := mul_le_mul_of_nonneg_right hrA hnz.le
  exact absurd (hconj _ hmem' hne') (not_lt.mpr hbig)

/-! ## Coherence with the rational transcription -/

/-- Over `ℚ` the spelled-out pseudo-Pisot predicate collapses to
`|v| > 1 ∧ v ∈ ℤ` — exactly the reading used by the derived rational instance
(`CITED/CorvajaZannier.lean`, module doc): the conjugate clause is vacuous and the
trace of a rational number is itself. -/
@[category API, AMS 11, ref "CZ04", group "rb_rational_base"]
theorem isPseudoPisot_ratCast_iff (v : ℚ) :
    IsPseudoPisot (v : ℝ) ↔ 1 < |v| ∧ ∃ n : ℤ, v = n := by
  have hminp : minpoly ℚ ((v : ℚ) : ℝ) = Polynomial.X - Polynomial.C v := by
    rw [show ((v : ℚ) : ℝ) = algebraMap ℚ ℝ v from (eq_ratCast (algebraMap ℚ ℝ) v).symm]
    exact minpoly.eq_X_sub_C_of_algebraMap_inj _ (algebraMap ℚ ℝ).injective
  have haroots : (minpoly ℚ ((v : ℚ) : ℝ)).aroots ℂ = {(v : ℂ)} := by
    rw [hminp]
    have : (Polynomial.X - Polynomial.C v).aroots ℂ
        = (Polynomial.X - Polynomial.C ((v : ℂ))).roots := by
      unfold Polynomial.aroots
      congr 1
      simp
    rw [this, Polynomial.roots_X_sub_C]
  constructor
  · rintro ⟨habs, -, -, n, hsum⟩
    refine ⟨by exact_mod_cast habs, n, ?_⟩
    rw [haroots, Multiset.sum_singleton] at hsum
    exact_mod_cast hsum
  · rintro ⟨habs, n, hn⟩
    have halg : IsAlgebraic ℚ ((v : ℚ) : ℝ) := by
      rw [show ((v : ℚ) : ℝ) = algebraMap ℚ ℝ v from (eq_ratCast (algebraMap ℚ ℝ) v).symm]
      exact isAlgebraic_algebraMap v
    refine ⟨by exact_mod_cast habs, halg, ?_, n, ?_⟩
    · intro z hz hzne
      rw [haroots, Multiset.mem_singleton] at hz
      exact absurd (by rw [hz]; push_cast; ring) hzne
    · rw [haroots, Multiset.sum_singleton, hn]
      push_cast
      ring

end CZ
