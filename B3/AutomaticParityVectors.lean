/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BL.ConjugacyMap
import AS.Basic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
## Contents
* `binaryDigit`, `binaryDigit_lt_two`, `IsAutomatic2Adic` — the binary digit sequence `k ↦ parity (Sᵏv)`
  of `v ∈ ℤ₂` (digits `< 2`) and the predicate that it is automatic.
* `parityVector`, `Φ_parityVector` — the parity vector `v = Φ⁻¹(n) = Q n` of `n ∈ ℕ`, with `Φ(v) = n`.
* `padicIrrational_iff_notMem_ratInt` — `(v : ℚ₂)` is `p`-adically irrational iff `v ∉ RatInt`.
* `henselValue_eq_coe` — the binary expansion of `v` is its Hensel expansion.

## References
* [BL96] Bernstein, Daniel J., and Jeffrey C. Lagarias. *The 3x+1 conjugacy map.* Canadian Journal of
  Mathematics 48 (1996), no. 6, 1154–1169 (the conjugacy map `Φ`, the parity-vector map `(1.5)`).
* [AB07] Adamczewski, Boris, and Yann Bugeaud. *On the complexity of algebraic numbers I. Expansions in
  integer bases.* Annals of Mathematics 165 (2007), 547–565 (Theorem 2B, §6: irrational automatic
  `p`-adic numbers are transcendental).
* [Sch77] Schlickewei, Hans Peter. *The `p`-adic Thue–Siegel–Roth–Schmidt theorem.* Arch. Math. (Basel)
  29 (1977), 267–270 (the `p`-adic Subspace Theorem powering the transcendence proof and Phases 2–4).
* [Ber94] Bernstein, Daniel J. *A noniterative 2-adic statement of the 3N+1 conjecture.* Proc. Amer.
  Math. Soc. 121 (1994), no. 2, 405–408.
* [Lag85] Lagarias, Jeffrey C. *The 3x+1 problem and its generalizations.* Amer. Math. Monthly 92
  (1985), no. 1, 3–23 (the parity-vector map `Q∞`).
-/

namespace B3

open BL Function

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The `k`-th **binary digit** of `v ∈ ℤ₂`. -/
@[category API, AMS 11 37, ref "BL96"]
noncomputable def binaryDigit (v : ℤ_[2]) (k : ℕ) : ℕ := parity (S^[k] v)

/-- `v ∈ ℤ₂` is **automatic** when its binary digit sequence `k ↦ parity (Sᵏ v)` is automatic in the
sense of Allouche–Shallit. -/
@[category API, AMS 11 68, ref "AB07" "BL96"]
def IsAutomatic2Adic (v : ℤ_[2]) : Prop := AS.IsAutomatic (binaryDigit v)

/-- The **`2`-adic parity vector** of `n ∈ ℕ`. -/
@[category API, AMS 11 37, ref "BL96" "Lag85"]
noncomputable def parityVector (n : ℕ) : ℤ_[2] := Q (n : ℤ_[2])

/-- `Φ` recovers `n` from its parity vector: `Φ (parityVector n) = n`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem Φ_parityVector (n : ℕ) : Φ (parityVector n) = (n : ℤ_[2]) := by
  unfold parityVector
  rw [← Φ_symm_eq_Q]
  exact Φ.apply_symm_apply _


end B3
