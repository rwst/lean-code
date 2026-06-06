/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integral

/-!
# Coprimality of integer polynomials descends to the rationals (Gauss's lemma)

`Polynomial.isCoprime_map_of_isUnit_gcd`: if two integer polynomials `P, Q : ℤ[X]` have a unit `gcd`
in `ℤ[X]` (no common factor of positive degree and trivial common content), then their images
`P, Q : ℚ[X]` under `Int.castRingHom ℚ` are coprime (`IsCoprime`) over the field `ℚ`.

This is the *coprimality* half of Gauss's lemma. The converse fails: `2 * X` and `2` are coprime over
`ℚ[X]` (`2` is a unit there) while their `ℤ[X]`-gcd is `2`, not a unit.

The proof reduces (`gcd_isUnit_iff`) to showing the `ℚ[X]`-gcd `d` of the images is a unit, then
descends a primitive integer model of `d` — `(integerNormalization ℤ⁰ d).primPart`, primitive by
Gauss — to a common divisor of `P` and `Q` in `ℤ[X]`
(`IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast`), hence a divisor of their unit gcd, hence a unit;
`isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart` then lifts unit-ness back to `d`.
-/

open Polynomial

namespace Polynomial

/-- **Gauss's lemma (coprimality form), `ℤ → ℚ`.** If `P, Q : ℤ[X]` have a unit `gcd` in `ℤ[X]`,
then their images in `ℚ[X]` along `Int.castRingHom ℚ` are coprime. The integer hypothesis is strictly
weaker than `ℚ[X]`-coprimality of the images would impose on `ℤ[X]`: e.g. `2 * X` and `2` map to a
coprime pair over `ℚ`, while their `ℤ[X]`-gcd is `2`. -/
theorem isCoprime_map_of_isUnit_gcd {P Q : ℤ[X]} (h : IsUnit (gcd P Q)) :
    IsCoprime (P.map (Int.castRingHom ℚ)) (Q.map (Int.castRingHom ℚ)) := by
  rw [← gcd_isUnit_iff]
  set a := P.map (Int.castRingHom ℚ) with ha
  set b := Q.map (Int.castRingHom ℚ) with hb
  set d := gcd a b with hd
  by_cases hd0 : d = 0
  · rw [hd, gcd_eq_zero_iff] at hd0
    obtain ⟨ha0, hb0⟩ := hd0
    rw [ha, Polynomial.map_eq_zero_iff (Int.cast_injective)] at ha0
    rw [hb, Polynomial.map_eq_zero_iff (Int.cast_injective)] at hb0
    rw [ha0, hb0, gcd_zero_left, normalize_zero] at h
    exact absurd h not_isUnit_zero
  · apply isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart (R := ℤ) (K := ℚ) hd0
    set E := (IsLocalization.integerNormalization (nonZeroDivisors ℤ) d).primPart with hE
    have hEprim : E.IsPrimitive := isPrimitive_primPart _
    have hEd : E.map (Int.castRingHom ℚ) ∣ d := by
      set N := IsLocalization.integerNormalization (nonZeroDivisors ℤ) d with hN
      obtain ⟨c, hcmem, hc⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) d
      have hc' : c ≠ 0 := nonZeroDivisors.ne_zero hcmem
      have hN0 : N ≠ 0 := by
        rw [hN, Ne, IsFractionRing.integerNormalization_eq_zero_iff]; exact hd0
      have hNc : N.content ≠ 0 := by rw [Ne, content_eq_zero_iff]; exact hN0
      have hmap : N.map (Int.castRingHom ℚ)
          = C ((N.content : ℤ) : ℚ) * E.map (Int.castRingHom ℚ) := by
        conv_lhs => rw [eq_C_content_mul_primPart N]
        rw [Polynomial.map_mul, Polynomial.map_C]; rfl
      rw [Algebra.smul_def] at hc
      have halg : (algebraMap ℤ (ℚ[X]) c) = C ((c : ℚ)) := by simp
      rw [halg, algebraMap_int_eq] at hc
      rw [hmap] at hc
      have huc : IsUnit (C ((c : ℚ))) :=
        isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by exact_mod_cast hc'))
      have hdvd1 : E.map (Int.castRingHom ℚ) ∣ C ((c : ℚ)) * d := by
        rw [← hc]; exact Dvd.intro_left _ rfl
      exact (huc.dvd_mul_left).mp hdvd1
    have key : ∀ (X : ℤ[X]), E.map (Int.castRingHom ℚ) ∣ X.map (Int.castRingHom ℚ) → E ∣ X := by
      intro X hEmapX
      by_cases hX : X = 0
      · rw [hX]; exact dvd_zero E
      · rw [← IsPrimitive.dvd_primPart_iff_dvd hEprim hX]
        rw [IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast E X.primPart hEprim (isPrimitive_primPart X)]
        have hXc : X.content ≠ 0 := by rw [Ne, content_eq_zero_iff]; exact hX
        have hmapX : X.map (Int.castRingHom ℚ)
            = C ((X.content : ℤ) : ℚ) * X.primPart.map (Int.castRingHom ℚ) := by
          conv_lhs => rw [eq_C_content_mul_primPart X]
          rw [Polynomial.map_mul, Polynomial.map_C]; rfl
        have huc : IsUnit (C (((X.content : ℤ) : ℚ))) :=
          isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by exact_mod_cast hXc))
        have hXdvd : X.map (Int.castRingHom ℚ) ∣ X.primPart.map (Int.castRingHom ℚ) := by
          rw [hmapX]; exact (huc.mul_left_dvd).mpr dvd_rfl
        exact hEmapX.trans hXdvd
    have hEP : E ∣ P := key P (hEd.trans (hd ▸ ha ▸ gcd_dvd_left a b))
    have hEQ : E ∣ Q := key Q (hEd.trans (hd ▸ hb ▸ gcd_dvd_right a b))
    exact isUnit_of_dvd_unit (dvd_gcd hEP hEQ) h

end Polynomial
