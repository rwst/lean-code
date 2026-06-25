/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BL.Basic
import BL.SolenoidalMaps
import CC.TerrasBijection
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.Padics.ProperSpace
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
  rw [qMap, (qMap_summable x).tsum_eq_zero_add]
  congr 1
  · simp
  · rw [qMap, ← (qMap_summable (T₂ x)).tsum_mul_left]
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

/-! ### Solenoidality of `qMap` (digit locality)

`qMap` is **solenoidal**: `x ≡ y (mod 2ⁿ)` makes the first `n` orbit parities agree, so the first `n`
binary digits of `qMap x`, `qMap y` agree, i.e. `qMap x ≡ qMap y (mod 2ⁿ)`. The engine is the one-step
solenoidality of `T₂` (each step loses one power of `2`), iterated. -/

/-- `toZMod 2 = 0`: `2` reduces to `0` mod `2`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem toZMod_two : PadicInt.toZMod (2 : ℤ_[2]) = 0 := by
  have e : (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) := by norm_num
  rw [e, map_natCast]; decide

/-- Equal lowest digit from a congruence mod `2`: `2 ∣ (x − y) ⟹ parity x = parity y`
(`toZMod (x − y) = 0`, so `toZMod x = toZMod y`). -/
@[category API, AMS 11 37, ref "BL96"]
theorem parity_eq_of_two_dvd_sub {x y : ℤ_[2]} (h : (2 : ℤ_[2]) ∣ (x - y)) :
    parity x = parity y := by
  unfold parity
  congr 1
  have hz : PadicInt.toZMod (x - y) = 0 := by
    obtain ⟨w, hw⟩ := h
    rw [hw, map_mul, toZMod_two, zero_mul]
  rw [map_sub, sub_eq_zero] at hz
  exact hz

/-- **One-step solenoidality of `T₂`.** `2^{k+1} ∣ (x − y) ⟹ 2^k ∣ (T₂ x − T₂ y)`. The parities agree
(mod `2`), so `2·(T₂ x − T₂ y) = (x − y)·3^{parity x}`; divide one factor of `2`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem T₂_dvd_sub_of_dvd_succ {k : ℕ} {x y : ℤ_[2]}
    (h : (2 : ℤ_[2]) ^ (k + 1) ∣ (x - y)) : (2 : ℤ_[2]) ^ k ∣ (T₂ x - T₂ y) := by
  have h2dvd : (2 : ℤ_[2]) ∣ (x - y) := (dvd_pow_self (2 : ℤ_[2]) (Nat.succ_ne_zero k)).trans h
  have hpar : parity x = parity y := parity_eq_of_two_dvd_sub h2dvd
  have hnum : (2 : ℤ_[2]) * (T₂ x - T₂ y) = (x - y) * 3 ^ parity x := by
    have hx := two_mul_T₂ x
    have hy := two_mul_T₂ y
    rw [numer] at hx hy
    rw [mul_sub, hx, hy, hpar]; ring
  have hd : (2 : ℤ_[2]) ^ (k + 1) ∣ (2 * (T₂ x - T₂ y)) := by rw [hnum]; exact h.mul_right _
  rw [pow_succ] at hd
  obtain ⟨t, ht⟩ := hd
  refine ⟨t, ?_⟩
  have h2 : (2 : ℤ_[2]) * (T₂ x - T₂ y) = 2 * (2 ^ k * t) := by rw [ht]; ring
  exact mul_left_cancel₀ (by norm_num) h2

/-- **Iterated solenoidality / digit agreement.** `2^n ∣ (x − y)` makes the first `n` orbit parities
agree: `parity (T₂^[i] x) = parity (T₂^[i] y)` for `i < n`. (After `i < n` steps, at least one power
of `2` of congruence remains — enough to pin the parity.) -/
@[category API, AMS 11 37, ref "BL96"]
theorem parity_T₂_iterate_congr {n : ℕ} {x y : ℤ_[2]} (h : (2 : ℤ_[2]) ^ n ∣ (x - y))
    (i : ℕ) (hi : i < n) : parity (T₂^[i] x) = parity (T₂^[i] y) := by
  have key : ∀ j, j ≤ n → (2 : ℤ_[2]) ^ (n - j) ∣ (T₂^[j] x - T₂^[j] y) := by
    intro j
    induction j with
    | zero => intro _; simpa using h
    | succ j ih =>
      intro hj
      have hd := ih (by omega)
      rw [show n - j = (n - (j + 1)) + 1 from by omega] at hd
      have hstep := T₂_dvd_sub_of_dvd_succ hd
      rwa [← Function.iterate_succ_apply' T₂ j x, ← Function.iterate_succ_apply' T₂ j y] at hstep
  have hik := key i (le_of_lt hi)
  have h2 : (2 : ℤ_[2]) ∣ (T₂^[i] x - T₂^[i] y) :=
    (dvd_pow_self (2 : ℤ_[2]) (by omega : n - i ≠ 0)).trans hik
  exact parity_eq_of_two_dvd_sub h2

/-- `qMap x` agrees with its **degree-`< n` partial sum** mod `2ⁿ`: the tail `∑_{i ≥ n} parity·2ⁱ`
factors as `2ⁿ · (…)`, so `2ⁿ ∣ (qMap x − ∑_{i<n} parity·2ⁱ)`. -/
@[category API, AMS 11 37, ref "BL96"]
theorem qMap_partialSum_dvd (n : ℕ) (x : ℤ_[2]) :
    (2 : ℤ_[2]) ^ n ∣ (qMap x - ∑ i ∈ Finset.range n, (parity (T₂^[i] x) : ℤ_[2]) * 2 ^ i) := by
  have hsum := qMap_summable x
  have hg : Summable (fun i => (parity (T₂^[i + n] x) : ℤ_[2]) * 2 ^ i) := by
    simpa [Function.iterate_add_apply] using qMap_summable (T₂^[n] x)
  have htail : ∑' i, (parity (T₂^[i + n] x) : ℤ_[2]) * 2 ^ (i + n)
             = 2 ^ n * ∑' i, (parity (T₂^[i + n] x) : ℤ_[2]) * 2 ^ i := by
    rw [← hg.tsum_mul_left]
    apply tsum_congr; intro i; rw [pow_add]; ring
  have key : qMap x = (∑ i ∈ Finset.range n, (parity (T₂^[i] x) : ℤ_[2]) * 2 ^ i)
      + 2 ^ n * ∑' i, (parity (T₂^[i + n] x) : ℤ_[2]) * 2 ^ i := by
    rw [qMap, ← htail, ← hsum.sum_add_tsum_nat_add n]
  rw [key, add_sub_cancel_left]
  exact dvd_mul_right _ _

/-- **`qMap` is solenoidal.** `x ≡ y (mod 2ⁿ)` makes the first `n` orbit parities agree
(`parity_T₂_iterate_congr`), so the degree-`< n` partial sums of `qMap x`, `qMap y` are *equal*; both
agree with their `qMap` mod `2ⁿ` (`qMap_partialSum_dvd`), so `qMap x ≡ qMap y (mod 2ⁿ)`. -/
@[category research solved, AMS 11 37, ref "BL96", group "bl_conjugacy_construction"]
theorem qMap_solenoidal : Solenoidal qMap := by
  intro n x y hxy
  have hP : (∑ i ∈ Finset.range n, (parity (T₂^[i] x) : ℤ_[2]) * 2 ^ i)
          = ∑ i ∈ Finset.range n, (parity (T₂^[i] y) : ℤ_[2]) * 2 ^ i :=
    Finset.sum_congr rfl fun i hi => by
      rw [parity_T₂_iterate_congr hxy i (Finset.mem_range.mp hi)]
  have heq : qMap x - qMap y
      = (qMap x - ∑ i ∈ Finset.range n, (parity (T₂^[i] x) : ℤ_[2]) * 2 ^ i)
      - (qMap y - ∑ i ∈ Finset.range n, (parity (T₂^[i] y) : ℤ_[2]) * 2 ^ i) := by
    rw [hP]; ring
  rw [heq]
  exact dvd_sub (qMap_partialSum_dvd n x) (qMap_partialSum_dvd n y)

/-- **The level map of `qMap`.** `toZModPow n (qMap x) = ∑_{i<n} (parity (T₂ⁱ x)) · 2ⁱ` in
`ZMod (2ⁿ)`: reducing mod `2ⁿ` keeps exactly the first `n` binary digits (the tail dies by
`qMap_partialSum_dvd`). This identifies the canonical inverse-limit family of `qMap` with the encoded
parity vectors, feeding `CC.terras_bijection` in Phase 3. -/
@[category API, AMS 11 37, ref "BL96" "Ter76"]
theorem toZModPow_qMap (n : ℕ) (x : ℤ_[2]) :
    PadicInt.toZModPow n (qMap x)
      = ∑ i ∈ Finset.range n, (parity (T₂^[i] x) : ZMod (2 ^ n)) * 2 ^ i := by
  have hd := qMap_partialSum_dvd n x
  rw [← toZModPow_eq_iff_dvd_sub] at hd
  rw [hd, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h2 : PadicInt.toZModPow n (2 : ℤ_[2]) = 2 := by
    have e : (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) := by norm_num
    rw [e, map_natCast]; norm_num
  rw [map_mul, map_pow, map_natCast, h2]

/-! ### Binary uniqueness (the `ZMod (2ⁿ)` encoding of a bit vector is injective)

The level map `Fam n` of `qMap` sends a residue to `∑_{i<n} (parity digit)·2ⁱ` in `ZMod (2ⁿ)`. To read
the digits back (and so invoke `CC.terras_bijection`) we need that this binary encoding of a `{0,1}`-bit
vector is injective: distinct bit vectors give distinct residues. -/

/-- The binary value `∑_{i<n} v i · 2ⁱ` of a digit vector `v`. -/
@[category API, AMS 11, ref "BL96"]
def encNat (n : ℕ) (v : ℕ → ℕ) : ℕ := ∑ i ∈ Finset.range n, v i * 2 ^ i

/-- Peel the lowest digit: `encNat (n+1) v = 2 · encNat n (v ∘ (·+1)) + v 0`. -/
@[category API, AMS 11, ref "BL96"]
theorem encNat_succ (n : ℕ) (u : ℕ → ℕ) :
    encNat (n + 1) u = 2 * encNat n (fun j => u (j + 1)) + u 0 := by
  unfold encNat
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_zero, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_succ]; ring

/-- A length-`n` bit vector has value `< 2ⁿ`. -/
@[category API, AMS 11, ref "BL96"]
theorem encNat_lt : ∀ (n : ℕ) (v : ℕ → ℕ), (∀ i < n, v i ≤ 1) → encNat n v < 2 ^ n := by
  intro n
  induction n with
  | zero => intro v _; simp [encNat]
  | succ n ih =>
    intro v hv
    rw [encNat_succ]
    have h1 := ih (fun j => v (j + 1)) (fun i hi => hv (i + 1) (by omega))
    have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
    have hv0 : v 0 ≤ 1 := hv 0 (by omega)
    omega

/-- **Binary uniqueness (ℕ).** Two length-`n` bit vectors with the same value agree digit-by-digit. -/
@[category API, AMS 11, ref "BL96"]
theorem encNat_inj : ∀ (n : ℕ) (v w : ℕ → ℕ), (∀ i < n, v i ≤ 1) → (∀ i < n, w i ≤ 1) →
    encNat n v = encNat n w → ∀ i < n, v i = w i := by
  intro n
  induction n with
  | zero => intro v w _ _ _ i hi; omega
  | succ n ih =>
    intro v w hv hw heq i hi
    rw [encNat_succ, encNat_succ] at heq
    have hv0 : v 0 ≤ 1 := hv 0 (by omega)
    have hw0 : w 0 ≤ 1 := hw 0 (by omega)
    have h0 : v 0 = w 0 := by omega
    have hAB : encNat n (fun j => v (j + 1)) = encNat n (fun j => w (j + 1)) := by omega
    have hih := ih (fun j => v (j + 1)) (fun j => w (j + 1))
      (fun j hj => hv (j + 1) (by omega)) (fun j hj => hw (j + 1) (by omega)) hAB
    rcases i with _ | j
    · exact h0
    · exact hih j (by omega)

/-- The `ZMod (2ⁿ)` encoding of a bit vector equals the natural-number value cast in. -/
@[category API, AMS 11, ref "BL96"]
theorem encZMod_eq (n : ℕ) (v : ℕ → ℕ) :
    (∑ i ∈ Finset.range n, (v i : ZMod (2 ^ n)) * 2 ^ i) = ((encNat n v : ℕ) : ZMod (2 ^ n)) := by
  unfold encNat
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

/-- **Binary uniqueness (`ZMod (2ⁿ)`).** Two length-`n` bit vectors with equal `ZMod (2ⁿ)` encodings
agree digit-by-digit (lift to ℕ: both values are `< 2ⁿ`, so the congruence is equality). -/
@[category API, AMS 11, ref "BL96"]
theorem encZMod_inj (n : ℕ) (v w : ℕ → ℕ) (hv : ∀ i < n, v i ≤ 1) (hw : ∀ i < n, w i ≤ 1)
    (h : (∑ i ∈ Finset.range n, (v i : ZMod (2 ^ n)) * 2 ^ i)
       = ∑ i ∈ Finset.range n, (w i : ZMod (2 ^ n)) * 2 ^ i) :
    ∀ i < n, v i = w i := by
  rw [encZMod_eq, encZMod_eq, ZMod.natCast_eq_natCast_iff] at h
  have h2 : encNat n v % 2 ^ n = encNat n w % 2 ^ n := h
  rw [Nat.mod_eq_of_lt (encNat_lt n v hv), Nat.mod_eq_of_lt (encNat_lt n w hw)] at h2
  exact encNat_inj n v w hv hw h2

/-! ### `qMap` is a bijection (Terras–Everett at every level)

The canonical inverse-limit family of the solenoidal `qMap` is, level by level, the binary encoding of
the length-`n` parity vector (`toZModPow_qMap` + `parity_T₂_iterate_natCast`); each level map is
injective by `CC.terras_forward'` and `encZMod_inj`, hence a permutation of `ZMod (2ⁿ)`. `lemma_A2`
lifts this to bijectivity of `qMap` on `ℤ₂`. -/

/-- **`qMap` is a bijection of `ℤ₂`.** Via `solenoidal_iff_isInverseLimit` its level family `Fam n`
satisfies `Fam n s = ∑_{i<n} (X (Tⁱ s.val)) · 2ⁱ` (`toZModPow_qMap`); each `Fam n` is injective (equal
encodings ⟹ equal parity vectors by `encZMod_inj`, ⟹ congruent residues by `CC.terras_forward'`),
hence a permutation, so `qMap` is bijective by `lemma_A2`. -/
@[category research solved, AMS 11 37, ref "BL96" "Ter76", group "bl_conjugacy_construction"]
theorem qMap_bijective : Function.Bijective qMap := by
  obtain ⟨Fam, hcompat, hlim⟩ := (solenoidal_iff_isInverseLimit qMap).mp qMap_solenoidal
  have hFs : ∀ (n : ℕ) (s : ZMod (2 ^ n)),
      Fam n s = PadicInt.toZModPow n (qMap ((s.val : ℕ) : ℤ_[2])) := by
    intro n s
    have hsect : PadicInt.toZModPow n ((s.val : ℕ) : ℤ_[2]) = s := by
      rw [map_natCast, ZMod.natCast_val, ZMod.cast_id]
    have hl := hlim n ((s.val : ℕ) : ℤ_[2])
    rw [hsect] at hl
    exact hl.symm
  have hfam : ∀ n, Function.Bijective (Fam n) := by
    intro n
    haveI : NeZero ((2 : ℕ) ^ n) := ⟨pow_ne_zero n (by norm_num)⟩
    rw [← Finite.injective_iff_bijective]
    intro a b hab
    rw [hFs n a, hFs n b, toZModPow_qMap, toZModPow_qMap] at hab
    simp only [parity_T₂_iterate_natCast] at hab
    have hbits := encZMod_inj n (fun i => CC.X (CC.T_iter i a.val))
      (fun i => CC.X (CC.T_iter i b.val))
      (fun i _ => by simp only [CC.X_eq_mod]; omega) (fun i _ => by simp only [CC.X_eq_mod]; omega) hab
    have hev : CC.E_vec n a.val = CC.E_vec n b.val := by
      funext i
      rw [CC.E_vec_apply, CC.E_vec_apply]
      exact hbits i.val i.isLt
    have hmod := CC.terras_forward' n a.val b.val hev
    rw [Nat.mod_eq_of_lt (ZMod.val_lt a), Nat.mod_eq_of_lt (ZMod.val_lt b)] at hmod
    exact ZMod.val_injective _ hmod
  exact ((lemma_A2 qMap Fam hcompat hlim).out 1 0).mp hfam

/-! ### The normalised conjugacy (existence) — PROVED from the `qMap` construction

The existence axiom is now **discharged**: `Φ := qMapHomeo⁻¹`, where `qMapHomeo` packages `qMap` (a
continuous bijection of the compact Hausdorff `ℤ₂`) as a homeomorphism. -/

/-- The parity-vector map `qMap` as a **homeomorphism** of `ℤ₂`: it is continuous
(`solenoidal_continuous` ∘ `qMap_solenoidal`) and bijective (`qMap_bijective`), and `ℤ₂` is compact
Hausdorff, so a continuous bijection is a homeomorphism. -/
@[category API, AMS 37 11, ref "BL96"]
noncomputable def qMapHomeo : ℤ_[2] ≃ₜ ℤ_[2] :=
  Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective qMap qMap_bijective)
    (solenoidal_continuous qMap qMap_solenoidal)

/-- `qMapHomeo` is `qMap` as a function. -/
@[category API, AMS 37 11, ref "BL96"]
theorem qMapHomeo_apply : ⇑qMapHomeo = qMap := by
  unfold qMapHomeo
  rw [← Homeomorph.coe_toEquiv, Continuous.toEquiv_homeoOfEquivCompactToT2]
  rfl

/-- **(PROVED; formerly a cited axiom.)** A conjugacy satisfying `(1.3)` exists with the normalisation
`Φ 0 = 0`. Witnessed by `Φ := qMapHomeo⁻¹` (`qMap = Q∞`): `qMap` conjugates `T₂` to the shift `S`
(`qMap_semiconj`) and fixes `0` (`qMap_apply_zero`) and is a homeomorphism (`qMapHomeo`), so its
inverse conjugates `S` to `T₂` with `Φ 0 = 0`. This discharges the Bernstein–Lagarias existence
statement *constructively* (Bernstein's noniterative parity-vector map, [Ber94]); the finite
level-wise bijectivity is Terras–Everett ([Ter76], `CC.terras_bijection`). Uniqueness is
`BL.ConjugacyMap.eq_Φ_of_normalized`. -/
@[category research solved, AMS 37 11, ref "BL96" "Ber94" "Ter76", group "bl_conjugacy_map"]
theorem exists_normalized_conjugacy :
    ∃ Φ : ℤ_[2] ≃ₜ ℤ_[2], Function.Semiconj (⇑Φ) S T₂ ∧ Φ 0 = 0 := by
  refine ⟨qMapHomeo.symm, fun z => ?_, ?_⟩
  · apply qMapHomeo.injective
    rw [Homeomorph.apply_symm_apply, qMapHomeo_apply, qMap_semiconj (qMapHomeo.symm z),
        ← qMapHomeo_apply, Homeomorph.apply_symm_apply]
  · rw [Homeomorph.symm_apply_eq, qMapHomeo_apply, qMap_apply_zero]

end BL
