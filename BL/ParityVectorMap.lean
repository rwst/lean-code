/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BL.Basic
import BL.SolenoidalMaps
import CC.TerrasBijection
import Mathlib.Analysis.SpecificLimits.Normed
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The parity-vector map `Q∞` and the construction of the conjugacy `Φ` (BL96, §1; toward discharging
`exists_normalized_conjugacy`)

The 3x+1 conjugacy map `Φ` is recorded in `BL.ConjugacyMap` only through the cited existence axiom
`BL.exists_normalized_conjugacy`. This file builds the **explicit construction** that will discharge
that axiom, via Lagarias's **parity-vector map**

  `qMap x = ∑_{i≥0} (parity (T₂ⁱ x)) · 2ⁱ`   (`Q∞`, the 2-adic integer whose `i`-th binary digit is
the parity of the `i`-th `T₂`-iterate of `x`).

The conjugacy is then `Φ := qMap⁻¹`: `qMap` conjugates `T₂` to the shift `S` (`qMap_semiconj`,
`qMap (T₂ x) = S (qMap x)`) and fixes `0` (`qMap_apply_zero`), so its inverse conjugates `S` to `T₂`
with `Φ 0 = 0`. The remaining input — that `qMap` is a **homeomorphism** — comes from Appendix A:
`qMap` is **solenoidal** and **bijective on every** `ZMod (2ⁿ)` (the finite Terras–Everett bijection
`CC.terras_bijection`), so `BL.lemma_A2` / `BL.corollary_A3` upgrade it to a 2-adic isometry, hence a
homeomorphism.

**Status (Phase 1).** This file currently establishes the *algebraic core* of the construction:
`qMap` is well-defined (`qMap_summable`), satisfies the bit-peel recursion
`qMap x = parity x + 2 · qMap (T₂ x)` (`qMap_peel`), has lowest digit `parity (qMap x) = parity x`
(`qMap_parity`), conjugates `T₂` to `S` (`qMap_semiconj`), and fixes `0` (`qMap_apply_zero`). The
solenoidality, level-bijectivity wiring (via `CC.terras_bijection`), and the final assembly into
`exists_normalized_conjugacy` are the next phases.

## Contents
* `qMap`, `qMap_summable` — the parity-vector map and convergence of its defining series.
* `qMap_peel` — the bit-peel recursion `qMap x = parity x + 2 · qMap (T₂ x)`.
* `qMap_parity` — the lowest binary digit: `parity (qMap x) = parity x`.
* `qMap_semiconj` — `Function.Semiconj qMap T₂ S` (`qMap (T₂ x) = S (qMap x)`).
* `qMap_apply_zero` — `qMap 0 = 0`.

## References
* [BL96] Bernstein, Daniel J., and Jeffrey C. Lagarias. *The 3x+1 conjugacy map.* Canadian J. Math. 48
  (1996), no. 6, 1154–1169.
* [Ber94] Bernstein, Daniel J. *A noniterative 2-adic statement of the 3N+1 conjecture.* Proc. AMS 121
  (1994), no. 2, 405–408 (the explicit formula `(1.5)` for `Φ⁻¹ = Q∞`).
* [Ter76] Terras, Riho. *A stopping time problem on the positive integers.* Acta Arith. 30 (1976),
  241–252 (the finite parity-vector bijection feeding the level-wise bijectivity).
-/

namespace BL

open PadicInt Function Filter

/-- **The parity-vector map `Q∞`** `qMap x = ∑_{i≥0} (parity (T₂ⁱ x)) · 2ⁱ`: the 2-adic integer whose
`i`-th binary digit is `parity (T₂^[i] x)`. This is Lagarias's `Q∞`; `Φ := qMap⁻¹` is the 3x+1
conjugacy map. (Same series as `BL.Q` in `BL.ConjugacyMap`, defined here independently so the
construction can *discharge* the existence axiom rather than depend on it.) -/
@[category API, AMS 11 37, ref "BL96" "Ber94", group "bl_conjugacy_construction"]
noncomputable def qMap (x : ℤ_[2]) : ℤ_[2] := ∑' i : ℕ, (parity (T₂^[i] x) : ℤ_[2]) * 2 ^ i

/-- The defining series of `qMap` **converges**: the terms `parity (T₂ⁱ x) · 2ⁱ` are norm-bounded by
the convergent geometric series `‖2‖ⁱ` (`‖2‖ < 1` in `ℤ₂`, which is complete). -/
@[category API, AMS 11 37, ref "BL96"]
theorem qMap_summable (x : ℤ_[2]) :
    Summable (fun i : ℕ => (parity (T₂^[i] x) : ℤ_[2]) * 2 ^ i) := by
  have h2lt : ‖(2 : ℤ_[2])‖ < 1 := by
    rw [PadicInt.norm_lt_one_iff_dvd]; exact_mod_cast dvd_refl (2 : ℤ_[2])
  have hbound : ∀ i, ‖(parity (T₂^[i] x) : ℤ_[2]) * 2 ^ i‖ ≤ ‖(2 : ℤ_[2])‖ ^ i := by
    intro i
    have h1 : ‖(parity (T₂^[i] x) : ℤ_[2]) * 2 ^ i‖
        ≤ ‖((parity (T₂^[i] x) : ℕ) : ℤ_[2])‖ * ‖(2 : ℤ_[2]) ^ i‖ := norm_mul_le _ _
    rw [norm_pow] at h1
    exact h1.trans (mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) i) (PadicInt.norm_le_one _))
  exact Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg _) h2lt) hbound

/-- **Bit-peel recursion.** `qMap x = parity x + 2 · qMap (T₂ x)`: splitting off the `i = 0` term
(`parity x`) and factoring `2` out of the rest reindexes the tail to `qMap (T₂ x)` (using
`T₂^[i+1] x = T₂^[i] (T₂ x)`). This is the engine of both `qMap_parity` and `qMap_semiconj`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem qMap_peel (x : ℤ_[2]) : qMap x = (parity x : ℤ_[2]) + 2 * qMap (T₂ x) := by
  rw [qMap, ← sum_add_tsum_nat_add 1 (qMap_summable x), Finset.sum_range_one]
  congr 1
  · simp
  · rw [qMap, ← tsum_mul_left]
    apply tsum_congr
    intro i
    rw [Function.iterate_succ_apply, pow_succ]
    ring

/-- **Lowest binary digit.** `parity (qMap x) = parity x`: in `qMap x = parity x + 2·qMap(T₂ x)` the
`2·(…)` term is even, so reducing mod `2` leaves `parity x` (`toZMod_natCast_parity`). This is `(1.4)`
read off the explicit formula. -/
@[category API, AMS 11 37, ref "BL96"]
theorem qMap_parity (x : ℤ_[2]) : parity (qMap x) = parity x := by
  unfold parity
  rw [qMap_peel x, map_add, map_mul]
  have h2 : PadicInt.toZMod (2 : ℤ_[2]) = 0 := by
    have e : (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) := by norm_num
    rw [e, map_natCast]; decide
  rw [h2, zero_mul, add_zero, toZMod_natCast_parity]

/-- **`qMap` conjugates `T₂` to the shift `S`**: `qMap (T₂ x) = S (qMap x)`, i.e.
`Function.Semiconj qMap T₂ S`. *Proof:* `2 · S (qMap x) = qMap x − parity (qMap x)` (`two_mul_S`)
`= qMap x − parity x` (`qMap_parity`) `= 2 · qMap (T₂ x)` (`qMap_peel`); cancel `2`. So `Φ := qMap⁻¹`
will conjugate `S` to `T₂`. -/
@[category research solved, AMS 11 37, ref "BL96" "Ber94", group "bl_conjugacy_construction"]
theorem qMap_semiconj : Function.Semiconj qMap T₂ S := by
  intro x
  have h := two_mul_S (qMap x)
  rw [qMap_parity x] at h
  have h2 : (2 : ℤ_[2]) * S (qMap x) = 2 * qMap (T₂ x) := by rw [h, qMap_peel x]; ring
  exact (mul_left_cancel₀ (by norm_num) h2).symm

/-- **`qMap` fixes `0`**: `qMap 0 = 0`. Every `T₂`-iterate of `0` is `0` (`T₂ 0 = 0`), so all parity
digits vanish and the series is `0`. Gives the normalisation `Φ 0 = 0`. -/
@[category research solved, AMS 11 37, ref "BL96", group "bl_conjugacy_construction"]
theorem qMap_apply_zero : qMap (0 : ℤ_[2]) = 0 := by
  have hp0 : parity (0 : ℤ_[2]) = 0 := by simp [parity]
  have hT0 : T₂ (0 : ℤ_[2]) = 0 := by
    have h := two_mul_T₂ (0 : ℤ_[2])
    rw [numer, hp0] at h
    simp only [Nat.cast_zero, add_zero, pow_zero, mul_one] at h
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  have hT : ∀ i, T₂^[i] (0 : ℤ_[2]) = 0 := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [Function.iterate_succ_apply', ih, hT0]
  rw [qMap]
  simp only [hT, hp0, Nat.cast_zero, zero_mul, tsum_zero]

/-! ### The normalised conjugacy (existence)

The construction target. `Φ := qMap⁻¹` is the unique normalised conjugacy; once `qMap` is shown to be
a homeomorphism (Phases 2–3: solenoidal + level-bijective via `CC.terras_bijection`, then
`BL.corollary_A3`), the existence axiom below becomes a **theorem** proved from `qMap_semiconj` and
`qMap_apply_zero`. It lives here (rather than in `BL.ConjugacyMap`) so the construction can replace it
in place. -/

/-- **(cited; Bernstein–Lagarias 1996, also [BFK90].)** A conjugacy satisfying `(1.3)` can be chosen
with the **normalisation `Φ 0 = 0`**. (The map has been constructed several times in the
literature.) Existence is cited; uniqueness is proved in `BL.ConjugacyMap`. *Slated to become a
theorem* via the `qMap` construction in this file (see `qMap_semiconj`, `qMap_apply_zero`). -/
@[category research solved, AMS 37 11, ref "BL96" "BFK90" "Ber94", group "bl_conjugacy_map"]
axiom exists_normalized_conjugacy :
    ∃ Φ : ℤ_[2] ≃ₜ ℤ_[2], Function.Semiconj (⇑Φ) S T₂ ∧ Φ 0 = 0

end BL
