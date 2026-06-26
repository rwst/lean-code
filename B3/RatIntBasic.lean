/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import B3.AutomaticParityVectors
import Mathlib.NumberTheory.Padics.WithVal
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# `RatInt` basics: a rational `2`-adic integer has odd denominator

A single shared fact about the rational `2`-adic integers `RatInt = ℚ ∩ ℤ₂`, factored into its own
**upstream** file so it can be imported by *both* the approximant chain (`B3.HoverWiring`, which feeds the
Subspace machinery) *and* `B3.DigitPeriodicity` (which proves the forward digit-periodicity direction).
Keeping it here avoids an import cycle: `DigitPeriodicity` is imported by `B3.StammeringApproximants`,
which the whole `HoverWiring`/`PrefixApproximants` chain depends on, so `DigitPeriodicity` cannot import
those files — but both can import this small upstream file.

## References
* [BL96] Bernstein, Daniel J., and Jeffrey C. Lagarias. *The 3x+1 conjugacy map.* Canadian J. Math. 48
  (1996), no. 6, 1154–1169.
-/

namespace B3

open BL

/-- **A rational `2`-adic integer has odd denominator (proved).** If `x : ℤ_[2]` has rational value `q`
(`(x : ℚ_[2]) = (q : ℚ_[2])`, the `RatInt` witness), then `q.den` is **odd**: `x ∈ ℤ_[2]` gives
`‖(q : ℚ_[2])‖ ≤ 1` (`PadicInt.norm_le_one`), hence `2 ∤ q.den`
(`Padic.norm_rat_le_one_iff_padicValuation_le_one`, `Rat.padicValuation_le_one_iff`). So `q.den` is a
`2`-adic unit — exactly the unit hypothesis the place-`2` factor needs, *without* the explicit base-`3`
denominator. -/
@[category research solved, AMS 11 37, ref "BL96", group "b3_missing_lemma"]
theorem ratInt_odd_den {x : ℤ_[2]} (q : ℚ) (hx : (x : ℚ_[2]) = (q : ℚ_[2])) : Odd ((q.den : ℤ)) := by
  have hnorm : ‖(q : ℚ_[2])‖ ≤ 1 := by
    rw [← hx, PadicInt.padic_norm_e_of_padicInt]; exact PadicInt.norm_le_one x
  have hden : ¬ (2 : ℕ) ∣ q.den :=
    Rat.padicValuation_le_one_iff.mp ((Padic.norm_rat_le_one_iff_padicValuation_le_one 2).mp hnorm)
  rw [Int.odd_coe_nat]
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hden)

end B3
