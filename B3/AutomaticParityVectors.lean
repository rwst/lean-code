import BL.ConjugacyMap
import CITED.AlloucheShallitBasic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

namespace B3

open BL Function

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

@[category API, AMS 11 37, ref "BL96"]
noncomputable def binaryDigit (v : ℤ_[2]) (k : ℕ) : ℕ := parity (S^[k] v)

@[category API, AMS 11 68, ref "AB07" "BL96"]
def IsAutomatic2Adic (v : ℤ_[2]) : Prop := AS.IsAutomatic (binaryDigit v)

@[category API, AMS 11 37, ref "BL96" "Lag85"]
noncomputable def parityVector (n : ℕ) : ℤ_[2] := Q (n : ℤ_[2])

@[category API, AMS 11 37, ref "BL96"]
theorem Φ_parityVector (n : ℕ) : Φ (parityVector n) = (n : ℤ_[2]) := by
  unfold parityVector
  rw [← Φ_symm_eq_Q]
  exact Φ.apply_symm_apply _

end B3
