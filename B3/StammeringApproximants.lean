/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import B3.AutomaticParityVectors
import AB.StammeringSequences
import B3.DigitPeriodicity
import Mathlib.Analysis.SpecificLimits.Normed
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Stammering of the parity vector and the geometric-series form of `Φ` (Route (i), Phase 2)

**Phase 2** of `B3/plan-automatic-cc.md`: *translate the automaton "stammering" structure into the
Bernstein–Lagarias map* `Φ`. Building on Phase 1 ([[b3-automatic-cc-corpus-root]],
`B3.AutomaticParityVectors`) and the Adamczewski–Bugeaud stammering machinery (`AB.StammeringSequences`,
[[ab-complexity-corpus-root]]), this file carries out the three steps of the plan:

* **Step 2.1 — Isolate the block structure.** An automatic, irrational parity vector `v` is a
  *stammering sequence* (`binaryDigit_isStammering`): its binary expansion satisfies Adamczewski–Bugeaud
  Condition (∗)_w. This is `AB.isStammering_of_automatic` (automatic + non-eventually-periodic ⟹
  stammering) combined with the standard bridge that an *irrational* `2`-adic integer
  (`v ∉ RatInt`) has a *non-eventually-periodic* binary expansion
  (`not_isEventuallyPeriodic_binaryDigit`, cited).
* **Step 2.2 — Apply the B-L formula.** Feed a repeating bit-pattern into the explicit formula `(1.6)`
  `Φ(x) = −∑ᵢ 3^{−(i+1)} 2^{dᵢ}` (`BL.Φ_eq_neg_tsum`).
* **Step 2.3 — Express as a geometric series.** A purely periodic bit-pattern (period `s`) makes the `dᵢ`
  an arithmetic progression, so the sum over the repeating block collapses to a **geometric series**.
  The unit fact `isUnit_one_sub_of_norm_lt_one` (`‖R‖ < 1 ⟹ 1 − R` invertible in `ℤ₂`) underlies that
  collapse; the geometric-series identities and the closed form of `Φ` on a repeated block are carried
  out in the block files (`B3.BlockApproximants`, `B3.PrefixApproximants`).

The ratios `R = 2^s` and `R = 3⁻¹·2^s` have `2`-adic norm `2^{−s} < 1`, so all these geometric series
converge in `ℤ₂` (which is complete) and `1 − R` is a unit (`isUnit_one_sub_of_norm_lt_one`); the
inverse `(1−R)⁻¹` is `Ring.inverse (1−R)` (`ℤ₂` is not a field, but these `1−R` are units). The
single supporting `axiom`, `not_isEventuallyPeriodic_binaryDigit` (now collected with its forward
companion in `B3.DigitPeriodicity`), is the standard fact that a rational `2`-adic integer has an
eventually periodic expansion (so an irrational one does not); it carries a literature `ref` and is not
an open conjecture.

## Contents
* `not_isEventuallyPeriodic_binaryDigit` — (cited, **imported** from `B3.DigitPeriodicity`) irrational
  `v` has a non-eventually-periodic binary expansion; used by `binaryDigit_isStammering` below.
* `binaryDigit_isStammering` — (proved) an automatic, irrational parity vector is stammering (Step 2.1).
* `isUnit_one_sub_of_norm_lt_one` — (proved) `‖R‖ < 1 ⟹ 1 − R` is a unit in `ℤ₂` (Step 2.3).

## References
* [BL96] Bernstein, Daniel J., and Jeffrey C. Lagarias. *The 3x+1 conjugacy map.* Canadian J. Math. 48
  (1996), no. 6, 1154–1169 (the explicit formula `(1.6)`).
* [AB07] Adamczewski, Boris, and Yann Bugeaud. *On the complexity of algebraic numbers I.* Annals of
  Mathematics 165 (2007), 547–565 (Condition (∗)_w; rationality ⟺ eventual periodicity).
-/

namespace B3

open BL AB Function Filter

/-! ### Step 2.1 — The parity vector is a stammering sequence -/

/-- **Step 2.1 (proved).** *An automatic, irrational parity vector is a stammering sequence.* If the
binary expansion of `v` is automatic (`IsAutomatic2Adic v`) and `v` is irrational (`v ∉ RatInt`), then
`binaryDigit v` satisfies Adamczewski–Bugeaud Condition (∗)_w for some `w > 1` (`AB.IsStammering`). This
is `AB.isStammering_of_automatic` (automatic + non-eventually-periodic ⟹ stammering) applied via
`not_isEventuallyPeriodic_binaryDigit`. It isolates the repeating block structure `Uₙ Vₙ^w` that
Steps 2.2–2.3 feed into the B-L formula. -/
@[category research solved, AMS 11 68, ref "AB07" "BL96", group "b3_missing_lemma"]
theorem binaryDigit_isStammering (v : ℤ_[2]) (hauto : IsAutomatic2Adic v) (hirr : v ∉ RatInt) :
    AB.IsStammering (binaryDigit v) :=
  AB.isStammering_of_automatic (binaryDigit v) hauto (not_isEventuallyPeriodic_binaryDigit v hirr)

/-! ### Step 2.3 — Geometric series in `ℤ₂` -/

/-- If `‖R‖ < 1` in `ℤ₂` then `1 − R` is a **unit**: `R` lies in the maximal ideal (`2 ∣ R`), so
`1 − R ≡ 1 (mod 2)` is odd, hence `‖1 − R‖ = 1`. Thus `(1 − R)⁻¹ = Ring.inverse (1 − R)` exists, which
the geometric-series sum needs (`ℤ₂` is not a field). -/
@[category API, AMS 11, ref "BL96"]
theorem isUnit_one_sub_of_norm_lt_one {R : ℤ_[2]} (hR : ‖R‖ < 1) : IsUnit (1 - R) := by
  rw [PadicInt.isUnit_iff]
  have hR0 : PadicInt.toZMod R = 0 := by
    rw [← two_dvd_iff_toZMod_eq_zero]
    exact_mod_cast (PadicInt.norm_lt_one_iff_dvd R).mp hR
  have hdvd : ¬ (2 : ℤ_[2]) ∣ (1 - R) := by
    rw [two_dvd_iff_toZMod_eq_zero, map_sub, map_one, hR0, sub_zero]
    decide
  rcases lt_or_eq_of_le (PadicInt.norm_le_one (1 - R)) with hlt | heq
  · exact absurd ((PadicInt.norm_lt_one_iff_dvd _).mp hlt) hdvd
  · exact heq

end B3
