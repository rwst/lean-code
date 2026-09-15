/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TShift.MultiplierTransfer
import Mathlib.Tactic.LinearCombination
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Scale invariance: no invariant functional of a pair certifies a floor

`TShift/CycleNormForm.lean` §5 proves that the elimination ledger cannot see a congruence imposed
on the coefficients of a pair of forms: `TShift.transfer_bound_scale`, the transfer bound is
homogeneous of degree `0` under `(aᵢ, bᵢ) ↦ (t·aᵢ, t·bᵢ)`.  That was stated about one bound.  This
file states it about the *class*: item D1 of `plans/plan-Tshift-NoGo.html`, the observation that
S7's verdict ("form quality is projective, so no sublattice can pay") and S10's ("the
`[CDT26]` functional `(2.2)/(2.4)` is invariant under `fᵢ ↦ cᵢfᵢ`, so it cannot see content") are
the **same theorem**, which had never been written down.

## The statement

A pair `p` of independent integer forms `aᵢ·2^N + bᵢ·3^N` certifies, through Proposition 1
(`TShift.transfer_prop_one`), the floor

`certifiedFloor D N p = (2^N − D·Λ(p))/B(p)`,  `Λ(p) = maxᵢ|ℓᵢ|`,  `B(p) = maxᵢ|bᵢ|`.

Scaling `p ↦ t·p` multiplies `Λ` and `B` by `|t|` at once, so the certified floor is **divided** by
at least `|t|` (`certifiedFloor_scale_le`) and eventually turns negative, i.e. vacuous
(`exists_certifiedFloor_neg`).  Hence for any real-valued `F` of a pair with `F(t·p) = F(p)` for
all `t ≠ 0`, and any proposed bound of the shape "`quality ≥ φ(F(p))` for every admissible `p`":
evaluating along the orbit `{t·p}` leaves the right-hand side constant while the left-hand side
goes to `0`, so

`φ(F(p)) ≤ 0`  for every `p`  (`no_floor_from_scaleInvariant`).

No scale-invariant functional of a pair yields a positive floor — not for a cleverer choice of `φ`,
not for a cleverer choice of `F`.  The statement actually proved
(`no_floor_from_scaleInvariant_of_orbit`) is stronger: the proposed bound need only be claimed
along the scaling orbit of the single pair in question, which is what a lag-, congruence- or
sublattice-constrained family supplies.

## Why the quantifier is honest

"No method of class `X` works" is not a Lean statement unless `X` is a Lean definition.  Here it is:
`ScaleInvariant` is a predicate on `FormPair → ℝ`, and the theorem quantifies over that predicate's
whole extension.  The class is also visibly inhabited by something one might actually have proposed
— `qualityRatio N = Λ/B`, the projective ratio, which is scale-invariant
(`scaleInvariant_qualityRatio`) and **non-constant** (`qualityRatio_not_constant`: it is `1/16` at
the corpus's own orientation instance and `81` at the standard basis).  Without that witness the
theorem could be true for silly reasons.

## Two consequences, which are the two lanes that died

* **Sublattices cannot pay** (S7).  A construction whose forms are constrained to a proper
  sublattice is, up to a primitive representative, working with scaled pairs, and
  `certifiedFloor_scale_le` says the scaling is a loss, never a gain.  The corpus already carried
  the measured version (`plans/note-Tshift-S7-WPD.html`, Q1: "same lattice, no integrality gain");
  this is its proof.
* **The engine has no content lemma** (S10).  `plans/note-Tshift-S10-WPG.html` G3 priced the
  invariance of one printed functional at `0.00%` of the demand.  `no_floor_from_scaleInvariant`
  upgrades that from a property of one engine to a property of every engine of that shape.

## What is *not* claimed

* **No engine is ruled out.**  The theorem is about functionals that are constant on scaling
  orbits.  A construction that gains by any other route — by content, which is exactly the slot
  scaling cannot reach — is untouched, and the record for `‖(3/2)^k‖` has advanced through that
  slot at every step since 1975.
* **The four T-shift walls (S7, S8, S10, S11) remain measured, not proved.**  The pricings
  (`×2.30`, `0.00%`, `10^183/10^34`, `×1.1072`) are comparisons against printed papers and are not
  formalizable; the capacity half of S11 is out of Mathlib's reach.  Nothing here says "nothing
  works".
* `certifiedFloor` is Proposition 1's guarantee, not the truth about `‖D(3/2)^N‖`.  What scaling
  destroys is the *certificate*, not the quantity: `certifiedFloor_le` is an inequality in one
  direction only.

## Trust ledger

`std3` (`propext`, `Classical.choice`, `Quot.sound`) throughout: **zero cited axioms**, no `sorry`,
no `native_decide`.  The file imports `TShift.MultiplierTransfer` only, so it stays
`#print axioms`-disjoint from every engine lane.

## Claim level

Formalization of a negative pricing, in the one place where the class of methods admits an honest
Lean definition.  The mathematics is a two-line orbit argument; the content is that the class is
defined, the witness is exhibited, and the quantifier is real.

## References

* `plans/plan-Tshift-NoGo.html` §1.1 D1 (the derivation), §3 target N2 and the witness N2′, §7
  gate G-D (the overclaim gate this file's "What is *not* claimed" answers).
* `plans/note-Tshift-S7-WPD.html` — the flagship measurement (Q2, O-3's falsification), 2026-08-11.
* `plans/note-Tshift-S10-WPG.html` — G3, the `0.00%` pricing this generalizes.
* `TShift/CycleNormForm.lean` §5 — the same invariance for one bound (`transfer_bound_scale`).
* [CDT26] F. Calegari, V. Dimitrov, Y. Tang, *Arithmetic holonomy bounds and effective Diophantine
  approximation*, Proc. ICM 2026, Vol. 3, SIAM, 2026, 356–376 — §4, and the functional
  `(2.2)/(2.4)` whose invariance this theorem generalizes.
-/

namespace TShift

/-! ## 1. A pair of independent forms, and what it certifies

The columns are the critical family `X = 2^N`, `Y = 3^N`, so a pair is four integers plus an
independence certificate.  The size slot `Λ` and the coefficient slot `B` are *defined* as the
maxima rather than left as parameters: Proposition 1 is monotone in both, so the maxima are the
best a given pair supplies, and a no-go must be stated at the best. -/

/-- Two independent integer forms `aᵢ·X + bᵢ·Y`, as bare data.  This is `TShift.TwoForms` with the
box parameters removed — here they are computed from the pair rather than supplied with it. -/
structure FormPair where
  /-- First coefficient of the first form. -/
  a₁ : ℤ
  /-- Second coefficient of the first form. -/
  b₁ : ℤ
  /-- First coefficient of the second form. -/
  a₂ : ℤ
  /-- Second coefficient of the second form. -/
  b₂ : ℤ
  /-- The two forms are independent. -/
  det : a₁ * b₂ ≠ a₂ * b₁

namespace FormPair

/-- **The scaling action**, `p ↦ t·p`.  Independence survives because the determinant scales by
`t² ≠ 0`.  This is the operation "constrain the forms to the sublattice `t·ℒ`", and equally the
operation `fᵢ ↦ t·fᵢ` on the two forms. -/
@[category API, AMS 11, ref "TshiftNoGo", group "tshift_nogo"]
def scale (p : FormPair) {t : ℤ} (ht : t ≠ 0) : FormPair where
  a₁ := t * p.a₁
  b₁ := t * p.b₁
  a₂ := t * p.a₂
  b₂ := t * p.b₂
  det := fun h => p.det (mul_left_cancel₀ (mul_ne_zero ht ht) (by linear_combination h))

end FormPair

/-- The size slot of a pair at date `N`: `Λ(p) = maxᵢ|aᵢ·2^N + bᵢ·3^N|`. -/
@[category API, AMS 11, ref "TshiftNoGo", group "tshift_nogo"]
noncomputable def pairSize (N : ℕ) (p : FormPair) : ℝ :=
  max |(p.a₁ : ℝ) * 2 ^ N + (p.b₁ : ℝ) * 3 ^ N| |(p.a₂ : ℝ) * 2 ^ N + (p.b₂ : ℝ) * 3 ^ N|

/-- The coefficient slot of a pair: `B(p) = maxᵢ|bᵢ|`. -/
@[category API, AMS 11, ref "TshiftNoGo", group "tshift_nogo"]
noncomputable def pairCoeff (p : FormPair) : ℝ := max |(p.b₁ : ℝ)| |(p.b₂ : ℝ)|

/-- **The certified floor**: the right-hand side of Proposition 1 at the pair's own slots,
`(2^N − D·Λ(p))/B(p)`.  Every effective `‖D(3/2)^N‖` bound in the Padé lane is this number for
some pair. -/
@[category API, AMS 11, ref "TshiftNoGo", group "tshift_nogo"]
noncomputable def certifiedFloor (D N : ℕ) (p : FormPair) : ℝ :=
  ((2 : ℝ) ^ N - (D : ℝ) * pairSize N p) / pairCoeff p

/-- The coefficient slot is positive: `b₁ = b₂ = 0` would make the determinant vanish. -/
@[category research solved, AMS 11, ref "TshiftNoGo", group "tshift_nogo"]
theorem pairCoeff_pos (p : FormPair) : 0 < pairCoeff p := by
  have hb : p.b₁ ≠ 0 ∨ p.b₂ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact p.det (by rw [hcon.1, hcon.2]; ring)
  rw [pairCoeff, lt_max_iff]
  rcases hb with h | h
  · exact Or.inl (abs_pos.mpr (Int.cast_ne_zero.mpr h))
  · exact Or.inr (abs_pos.mpr (Int.cast_ne_zero.mpr h))

/-- The size slot is positive: both forms vanishing would put the two coefficient vectors on one
line through the origin, i.e. make the determinant vanish. -/
@[category research solved, AMS 11, ref "TshiftNoGo", group "tshift_nogo"]
theorem pairSize_pos (N : ℕ) (p : FormPair) : 0 < pairSize N p := by
  rw [pairSize, lt_max_iff]
  by_contra hcon
  push Not at hcon
  obtain ⟨h₁, h₂⟩ := hcon
  have e₁ : (p.a₁ : ℝ) * 2 ^ N + (p.b₁ : ℝ) * 3 ^ N = 0 :=
    abs_eq_zero.mp (le_antisymm h₁ (abs_nonneg _))
  have e₂ : (p.a₂ : ℝ) * 2 ^ N + (p.b₂ : ℝ) * 3 ^ N = 0 :=
    abs_eq_zero.mp (le_antisymm h₂ (abs_nonneg _))
  have hpow : ((2 : ℝ) ^ N) ≠ 0 := by positivity
  have hkey : ((p.a₁ : ℝ) * (p.b₂ : ℝ) - (p.a₂ : ℝ) * (p.b₁ : ℝ)) * 2 ^ N = 0 := by
    linear_combination (p.b₂ : ℝ) * e₁ - (p.b₁ : ℝ) * e₂
  have hR : (p.a₁ : ℝ) * (p.b₂ : ℝ) = (p.a₂ : ℝ) * (p.b₁ : ℝ) :=
    sub_eq_zero.mp ((mul_eq_zero.mp hkey).resolve_right hpow)
  exact p.det (by exact_mod_cast hR)

/-- **The floor is Proposition 1's**, tying the definition to `TShift.transfer_prop_one`: the pair
`p` really does force `|D·3^N − m·2^N| ≥ certifiedFloor D N p` at every `m`. -/
@[category research solved, AMS 11, ref "TshiftNoGo", group "tshift_nogo"]
theorem certifiedFloor_le {D N : ℕ} (hD : 0 < D) (p : FormPair) (m : ℤ) :
    certifiedFloor D N p ≤ |(D : ℝ) * 3 ^ N - (m : ℝ) * 2 ^ N| :=
  transfer_prop_one hD (pairCoeff_pos p) p.det (le_max_left _ _) (le_max_right _ _)
    (le_max_left _ _) (le_max_right _ _) m

/-! ## 2. Scaling is a loss

Both slots are homogeneous of degree `1`, so the certified floor loses a factor `|t|` in the
denominator while the numerator only shrinks.  This is D1, and it is the proof of S7's measured
"a sublattice buys nothing". -/

/-- The size slot scales by `|t|`. -/
@[category research solved, AMS 11, ref "TshiftNoGo", group "tshift_nogo"]
theorem pairSize_scale (N : ℕ) (p : FormPair) {t : ℤ} (ht : t ≠ 0) :
    pairSize N (p.scale ht) = |(t : ℝ)| * pairSize N p := by
  have h₁ : ((t * p.a₁ : ℤ) : ℝ) * 2 ^ N + ((t * p.b₁ : ℤ) : ℝ) * 3 ^ N
      = (t : ℝ) * ((p.a₁ : ℝ) * 2 ^ N + (p.b₁ : ℝ) * 3 ^ N) := by push_cast; ring
  have h₂ : ((t * p.a₂ : ℤ) : ℝ) * 2 ^ N + ((t * p.b₂ : ℤ) : ℝ) * 3 ^ N
      = (t : ℝ) * ((p.a₂ : ℝ) * 2 ^ N + (p.b₂ : ℝ) * 3 ^ N) := by push_cast; ring
  simp only [pairSize, FormPair.scale, h₁, h₂, abs_mul]
  exact (mul_max_of_nonneg _ _ (abs_nonneg ((t : ℝ)))).symm

/-- The coefficient slot scales by `|t|`. -/
@[category research solved, AMS 11, ref "TshiftNoGo", group "tshift_nogo"]
theorem pairCoeff_scale (p : FormPair) {t : ℤ} (ht : t ≠ 0) :
    pairCoeff (p.scale ht) = |(t : ℝ)| * pairCoeff p := by
  simp only [pairCoeff, FormPair.scale, Int.cast_mul, abs_mul]
  exact (mul_max_of_nonneg _ _ (abs_nonneg ((t : ℝ)))).symm

/-- The certified floor of a scaled pair, in closed form: `(2^N − D·|t|·Λ)/(|t|·B)`. -/
@[category research solved, AMS 11, ref "TshiftNoGo", group "tshift_nogo"]
theorem certifiedFloor_scale (D N : ℕ) (p : FormPair) {t : ℤ} (ht : t ≠ 0) :
    certifiedFloor D N (p.scale ht)
      = ((2 : ℝ) ^ N - (D : ℝ) * (|(t : ℝ)| * pairSize N p)) / (|(t : ℝ)| * pairCoeff p) := by
  rw [certifiedFloor, pairSize_scale, pairCoeff_scale]

/-- **D1: scaling strictly loses.**  `certifiedFloor D N (t·p) ≤ certifiedFloor D N p / |t|`.
The content refund and the size cost cancel — that is `TShift.transfer_bound_scale` — and what is
left is the bare `|t|` in the coefficient slot, which is a division.  Imposing a congruence on the
coefficients of a pair can therefore never improve what the pair certifies. -/
@[category research solved, AMS 11, ref "TshiftNoGo", group "tshift_nogo"]
theorem certifiedFloor_scale_le (D N : ℕ) (p : FormPair) {t : ℤ} (ht : t ≠ 0) :
    certifiedFloor D N (p.scale ht) ≤ certifiedFloor D N p / |(t : ℝ)| := by
  have hT : (1 : ℝ) ≤ |(t : ℝ)| := by
    have : (1 : ℤ) ≤ |t| := Int.one_le_abs (by omega)
    calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
      _ ≤ ((|t| : ℤ) : ℝ) := by exact_mod_cast this
      _ = |(t : ℝ)| := by rw [Int.cast_abs]
  have hB : 0 < pairCoeff p := pairCoeff_pos p
  have hΛ : 0 < pairSize N p := pairSize_pos N p
  have hTB : 0 < |(t : ℝ)| * pairCoeff p := by positivity
  have hT0 : |(t : ℝ)| ≠ 0 := by linarith
  have hB0 : pairCoeff p ≠ 0 := hB.ne'
  have key : certifiedFloor D N p / |(t : ℝ)| - certifiedFloor D N (p.scale ht)
      = (D : ℝ) * pairSize N p * (|(t : ℝ)| - 1) / (|(t : ℝ)| * pairCoeff p) := by
    rw [certifiedFloor_scale, certifiedFloor]
    field_simp
    ring
  have hnn : 0 ≤ (D : ℝ) * pairSize N p * (|(t : ℝ)| - 1) / (|(t : ℝ)| * pairCoeff p) :=
    div_nonneg
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) D) hΛ.le) (by linarith)) hTB.le
  linarith

/-- **And eventually vacuous.**  Past `|t| > 2^N/(D·Λ)` the numerator is negative, so the scaled
pair certifies a negative number — no information at all.  The orbit of any pair therefore contains
certificates of arbitrarily poor quality. -/
@[category research solved, AMS 11, ref "TshiftNoGo", group "tshift_nogo"]
theorem exists_certifiedFloor_neg {D : ℕ} (hD : 0 < D) (N : ℕ) (p : FormPair) :
    ∃ (t : ℤ) (ht : t ≠ 0), certifiedFloor D N (p.scale ht) < 0 := by
  have hB : 0 < pairCoeff p := pairCoeff_pos p
  have hΛ : 0 < pairSize N p := pairSize_pos N p
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  obtain ⟨n, hn⟩ := exists_nat_gt ((2 : ℝ) ^ N / ((D : ℝ) * pairSize N p))
  refine ⟨(n : ℤ) + 1, by omega, ?_⟩
  have habs : |(((n : ℤ) + 1 : ℤ) : ℝ)| = (n : ℝ) + 1 := by
    rw [show ((((n : ℤ) + 1 : ℤ)) : ℝ) = (n : ℝ) + 1 by push_cast; ring,
      abs_of_pos (by positivity)]
  have hnum : (2 : ℝ) ^ N - (D : ℝ) * (((n : ℝ) + 1) * pairSize N p) < 0 := by
    have h : (2 : ℝ) ^ N < (D : ℝ) * pairSize N p * ((n : ℝ) + 1) := by
      rw [div_lt_iff₀ (by positivity)] at hn
      nlinarith [mul_pos hDR hΛ]
    nlinarith
  rw [certifiedFloor_scale, habs]
  exact div_neg_of_neg_of_pos hnum (by positivity)

/-! ## 3. The class, and the no-go

`ScaleInvariant` is the class the S10 pricing observed one member of.  Because it is a Lean
definition, "no functional of this class certifies a floor" is a Lean theorem rather than a
sentence about methods. -/

/-- **The class.**  A real-valued functional of a pair that cannot see the scaling — `F(t·p) = F(p)`
for every `t ≠ 0`.  Equivalently: `F` is a function on the projective data of the pair.  This is
the invariance `[CDT26]`'s `(2.2)/(2.4)` has under `fᵢ ↦ cᵢfᵢ`, and the invariance behind "form
quality is projective". -/
@[category API, AMS 11, ref "TshiftNoGo" "CDT26", group "tshift_nogo"]
def ScaleInvariant (F : FormPair → ℝ) : Prop :=
  ∀ (p : FormPair) {t : ℤ} (ht : t ≠ 0), F (p.scale ht) = F p

/-- **N2, orbit form: no scale-invariant functional certifies a positive floor.**  Let `F` be any
scale-invariant real-valued functional of a pair and `φ` any function whatever, and suppose the
proposed bound `φ(F(·)) ≤ certifiedFloor D N ·` holds along the scaling orbit of a single pair `p`.
Then `φ(F(p)) ≤ 0`: the criterion is empty at `p`.

The proof is the orbit `{t·p}` itself.  The right-hand side of the proposed bound is constant along
it because `F` is invariant; the left-hand side is at most `certifiedFloor D N p / |t| → 0` by
`certifiedFloor_scale_le`.  A positive value would beat itself.

The hypothesis is deliberately orbit-local rather than global.  A criterion is usually advertised
only for *admissible* pairs — those a particular construction produces — and the objection to a
global hypothesis is that the scalings of an admissible pair need not be admissible.  But the
constraints that motivate such a criterion in the first place (a lag, a congruence, a sublattice)
are themselves closed under scaling, so the orbit-local hypothesis is exactly what they supply.

This is S7's and S10's shared cause, and the only quantifier over a class of methods the T-shift
programme is entitled to: the class is the extension of `ScaleInvariant`, and it is inhabited by
a non-constant member (`scaleInvariant_qualityRatio`, `qualityRatio_not_constant`). -/
@[category research solved, AMS 11, ref "TshiftNoGo" "CDT26", group "tshift_nogo"]
theorem no_floor_from_scaleInvariant_of_orbit {D N : ℕ} {F : FormPair → ℝ} (hF : ScaleInvariant F)
    {φ : ℝ → ℝ} {p : FormPair}
    (hcert : ∀ (t : ℤ) (ht : t ≠ 0), φ (F (p.scale ht)) ≤ certifiedFloor D N (p.scale ht)) :
    φ (F p) ≤ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨n, hn⟩ := exists_nat_gt (certifiedFloor D N p / φ (F p))
  set t : ℤ := (n : ℤ) + 1 with hdef
  have ht : t ≠ 0 := by omega
  have habs : |(t : ℝ)| = (n : ℝ) + 1 := by
    rw [hdef, show (((n : ℤ) + 1 : ℤ) : ℝ) = (n : ℝ) + 1 by push_cast; ring,
      abs_of_pos (by positivity)]
  have hTpos : (0 : ℝ) < |(t : ℝ)| := by rw [habs]; positivity
  have hlt : certifiedFloor D N p / φ (F p) < |(t : ℝ)| := by rw [habs]; linarith
  have hkey : certifiedFloor D N p < |(t : ℝ)| * φ (F p) := (div_lt_iff₀ hcon).mp hlt
  have hstep : certifiedFloor D N p / |(t : ℝ)| < φ (F p) :=
    (div_lt_iff₀ hTpos).mpr (by linarith)
  have hchain : φ (F p) ≤ certifiedFloor D N p / |(t : ℝ)| := by
    calc φ (F p) = φ (F (p.scale ht)) := by rw [hF p ht]
      _ ≤ certifiedFloor D N (p.scale ht) := hcert t ht
      _ ≤ certifiedFloor D N p / |(t : ℝ)| := certifiedFloor_scale_le D N p ht
  linarith

/-- **N2, as a criterion is usually stated.**  If a proposed bound "`quality ≥ φ(F)`" with `F`
scale-invariant holds at *every* pair, then it is empty at every pair.  The corollary of the orbit
form, and the shape in which the S10 engine's output was priced. -/
@[category research solved, AMS 11, ref "TshiftNoGo" "CDT26", group "tshift_nogo"]
theorem no_floor_from_scaleInvariant {D N : ℕ} {F : FormPair → ℝ} (hF : ScaleInvariant F)
    {φ : ℝ → ℝ} (hcert : ∀ p : FormPair, φ (F p) ≤ certifiedFloor D N p) (p : FormPair) :
    φ (F p) ≤ 0 :=
  no_floor_from_scaleInvariant_of_orbit hF (fun _ _ => hcert _)

/-! ## 4. The witness: the class is inhabited by something one might propose

Without this section the theorem above could be true for silly reasons — it would apply to the
constant functionals and to nothing else anyone would write down.  The projective ratio `Λ/B` is
the natural quality measure of a pair, it is scale-invariant, and it is not constant. -/

/-- The projective ratio `Λ(p)/B(p)` — the size slot measured in units of the coefficient slot.
This is the quality measure a Padé construction is optimised for, and it is the shape of the
`[CDT26]` functional's invariant. -/
@[category API, AMS 11, ref "TshiftNoGo", group "tshift_nogo"]
noncomputable def qualityRatio (N : ℕ) (p : FormPair) : ℝ := pairSize N p / pairCoeff p

/-- **N2′(a): the witness is in the class.** -/
@[category research solved, AMS 11, ref "TshiftNoGo", group "tshift_nogo"]
theorem scaleInvariant_qualityRatio (N : ℕ) : ScaleInvariant (qualityRatio N) := by
  intro p t ht
  have hT : (t : ℝ) ≠ 0 := Int.cast_ne_zero.mpr ht
  rw [qualityRatio, qualityRatio, pairSize_scale, pairCoeff_scale]
  exact mul_div_mul_left _ _ (abs_ne_zero.mpr hT)

/-- The corpus's own orientation instance (`TShift.transfer_prop_one_sanity`): the forms
`−5·2⁴ + 3⁴ = 1` and `−81·2⁴ + 16·3⁴ = 0`, independent with determinant `1`. -/
@[category API, AMS 11, ref "TshiftNoGo", group "tshift_nogo"]
def pairSanity : FormPair where
  a₁ := -5
  b₁ := 1
  a₂ := -81
  b₂ := 16
  det := by norm_num

/-- The standard basis `(1, 0)`, `(0, 1)`: two independent forms with the worst possible size and
the best possible coefficients. -/
@[category API, AMS 11, ref "TshiftNoGo", group "tshift_nogo"]
def pairBasis : FormPair where
  a₁ := 1
  b₁ := 0
  a₂ := 0
  b₂ := 1
  det := by norm_num

/-- At the orientation instance the ratio is `Λ/B = 1/16`. -/
@[category test, AMS 11, ref "TshiftNoGo", group "tshift_nogo"]
theorem qualityRatio_pairSanity : qualityRatio 4 pairSanity = 1 / 16 := by
  norm_num [qualityRatio, pairSize, pairCoeff, pairSanity]

/-- At the standard basis it is `Λ/B = 81`. -/
@[category test, AMS 11, ref "TshiftNoGo", group "tshift_nogo"]
theorem qualityRatio_pairBasis : qualityRatio 4 pairBasis = 81 := by
  norm_num [qualityRatio, pairSize, pairCoeff, pairBasis]

/-- **N2′(b): the witness is not constant.**  So `no_floor_from_scaleInvariant` is not a statement
about constants: it applies to a functional that separates pairs, and would apply to any refinement
of it. -/
@[category research solved, AMS 11, ref "TshiftNoGo", group "tshift_nogo"]
theorem qualityRatio_not_constant : qualityRatio 4 pairSanity ≠ qualityRatio 4 pairBasis := by
  rw [qualityRatio_pairSanity, qualityRatio_pairBasis]
  norm_num

/-- **The no-go at the witness.**  No criterion of the form "the certified floor is at least
`φ(Λ/B)`" can be non-trivial, whatever `φ`.  This is the printed shape of the S10 engine's output,
and the instance of N2 that the pricing note was about. -/
@[category research solved, AMS 11, ref "TshiftNoGo" "CDT26", group "tshift_nogo"]
theorem no_floor_from_qualityRatio {D N : ℕ} {φ : ℝ → ℝ}
    (hcert : ∀ p : FormPair, φ (qualityRatio N p) ≤ certifiedFloor D N p) (p : FormPair) :
    φ (qualityRatio N p) ≤ 0 :=
  no_floor_from_scaleInvariant (scaleInvariant_qualityRatio N) hcert p

end TShift
