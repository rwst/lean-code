import B3.AutomaticParityVectors
import AB.StammeringSequences
import B3.DigitPeriodicity
import Mathlib.Analysis.SpecificLimits.Normed
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

namespace B3

open BL AB Function Filter

@[category research solved, AMS 11 68, ref "AB07" "BL96", group "b3_missing_lemma"]
theorem binaryDigit_isStammering (v : ℤ_[2]) (hauto : IsAutomatic2Adic v) (hirr : v ∉ RatInt) :
    AB.IsStammering (binaryDigit v) :=
  AB.isStammering_of_automatic (binaryDigit v) hauto (not_isEventuallyPeriodic_binaryDigit v hirr)

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
