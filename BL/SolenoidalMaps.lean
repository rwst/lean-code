/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.RingHoms
import ForMathlib.NumberTheory.PadicIntDvdNorm
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Bernstein–Lagarias — Appendix A: Solenoidal maps (BL96, §7)

Daniel J. Bernstein and Jeffrey C. Lagarias, *The 3x+1 conjugacy map*, Canadian Journal of
Mathematics **48** (1996), no. 6, 1154–1169.

Appendix A of the paper. A map `F : ℤ₂ → ℤ₂` is **solenoidal** `(A.1)` if it respects congruence
modulo `2ⁿ` for every `n`:

  `x ≡ y (mod 2ⁿ) ⟹ F(x) ≡ F(y) (mod 2ⁿ)`     (`Solenoidal`)

— equivalently, `F` induces a map on each `ℤ/2ⁿℤ` (`ℤ₂` is the inverse limit of these, a *solenoid*).
The appendix records:

* `(A.2)` Solenoidality is the same as being **nonexpanding** for the 2-adic metric,
  `‖F(x) − F(y)‖ ≤ ‖x − y‖` (`Nonexpanding`): `solenoidal_iff_nonExpanding`. The key input is the
  general fact that in `ℤ_[p]` divisibility is governed by the norm,
  `a ∣ b ↔ ‖b‖ ≤ ‖a‖` (`PadicInt.dvd_iff_norm_le`, in `ForMathlib`).
* Solenoidal maps are **closed under composition**: `F₁ ∘ F₂` is solenoidal whenever `F₁` and `F₂`
  are (`Solenoidal.comp`).
* **Lemma A.1**: `F` is solenoidal **iff** it is the **inverse limit of a compatible family**
  `{Fₙ : ℤ/2ⁿℤ → ℤ/2ⁿℤ}` `(A.3)` (`solenoidal_iff_isInverseLimit`) — the structural reason for the
  name (`ℤ₂ = lim ℤ/2ⁿℤ` is the 2-adic *solenoid*).
* **Lemma A.2**: for `U` an inverse limit of a compatible family `{Uₙ}`, **TFAE**: `U` is a bijection;
  each `Uₙ` is a permutation; `U` reflects congruences mod `2ⁿ` (`lemma_A2`). Uses that every compatible
  family has an inverse limit (`exists_isInverseLimit_of_compatible`).
* **Corollary A.3**: for any `U`, **TFAE**: solenoidal bijection; solenoidal homeomorphism; 2-adic
  isometry `‖U x − U y‖ = ‖x − y‖` (`corollary_A3`). In particular a solenoidal bijection of `ℤ₂` is
  automatically an isometry (solenoidal maps are continuous, `solenoidal_continuous`).

This is the abstract notion behind `BL.Φ_solenoidal`/`BL.Q_solenoidal` (the conjugacy map and its
inverse are solenoidal); `Solenoidal` itself is defined here and reused there.

## Contents
* `Solenoidal` `(A.1)`, `Nonexpanding` `(A.2)` — the two equivalent conditions.
* `dvd_pow_iff_norm_le`, `norm_le_iff_forall_dvd` — the divisibility-by-`2ⁿ` ↔ norm dictionary.
* `solenoidal_iff_nonExpanding` — `(A.2)`: solenoidal ⟺ nonexpanding (proved).
* `Solenoidal.comp` — solenoidal maps are closed under composition (proved).
* `Compatible`, `IsInverseLimit`, `toZModPow_eq_iff_dvd_sub` — compatible families and `(A.3)`.
* `solenoidal_iff_isInverseLimit` — **Lemma A.1**: solenoidal ⟺ inverse limit of a compatible family
  (proved).
* `exists_toZModPow_eq_thread`, `exists_isInverseLimit_of_compatible` — inverse-limit points exist;
  every compatible family has an inverse limit (proved).
* `lemma_A2` — **Lemma A.2**: TFAE for a bijective inverse limit (proved).
* `solenoidal_continuous`, `reflects_iff_norm_le` — solenoidal ⟹ continuous; reflecting ⟺ expanding.
* `corollary_A3` — **Corollary A.3**: solenoidal bijection ⟺ solenoidal homeomorphism ⟺ isometry
  (proved).

## References
* [BL96] Bernstein, Daniel J., and Jeffrey C. Lagarias. *The 3x+1 conjugacy map.* Canadian Journal
  of Mathematics 48 (1996), no. 6, 1154–1169 (Appendix A).
-/

namespace BL

open PadicInt

/-- **(A.1)** A map on `ℤ₂` is **solenoidal** if it respects congruence modulo `2ⁿ` for every `n`:
`2ⁿ ∣ (x - y) ⟹ 2ⁿ ∣ (f x - f y)`. Equivalently, `f` induces a map on `ℤ/2ⁿℤ` for each `n` (so on the
2-adic solenoid `ℤ₂ = lim ℤ/2ⁿℤ`). -/
@[category API, AMS 11 37, ref "BL96"]
def Solenoidal (f : ℤ_[2] → ℤ_[2]) : Prop :=
  ∀ (n : ℕ) (x y : ℤ_[2]), (2 ^ n : ℤ_[2]) ∣ (x - y) → (2 ^ n : ℤ_[2]) ∣ (f x - f y)

/-- **(A.2) condition.** A map on `ℤ₂` is **nonexpanding** for the 2-adic metric if
`‖f x - f y‖ ≤ ‖x - y‖` for all `x, y` — i.e. it is `1`-Lipschitz. By `solenoidal_iff_nonExpanding`
this is equivalent to `Solenoidal`. -/
@[category API, AMS 11 37, ref "BL96"]
def Nonexpanding (f : ℤ_[2] → ℤ_[2]) : Prop := ∀ x y : ℤ_[2], ‖f x - f y‖ ≤ ‖x - y‖

/-- Divisibility by a power of `2` as a norm bound: `2ⁿ ∣ z ↔ ‖z‖ ≤ 2^(-n)` in `ℤ₂` (the kernel of
`ℤ₂ → ℤ/2ⁿℤ` is the closed ball of radius `2^(-n)`). -/
@[category API, AMS 11 37, ref "BL96"]
theorem dvd_pow_iff_norm_le (z : ℤ_[2]) (n : ℕ) :
    (2 : ℤ_[2]) ^ n ∣ z ↔ ‖z‖ ≤ ((2 : ℕ) : ℝ) ^ (-(n : ℤ)) := by
  have e2 : ((2 : ℕ) : ℤ_[2]) = (2 : ℤ_[2]) := by norm_num
  rw [← e2, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]

/-- Comparing 2-adic norms by divisibility: `‖a‖ ≤ ‖b‖` iff every power of `2` dividing `b` divides
`a`. (Powers of `2` are cofinal in the value group, so they detect the norm.) -/
@[category API, AMS 11 37, ref "BL96"]
theorem norm_le_iff_forall_dvd (a b : ℤ_[2]) :
    ‖a‖ ≤ ‖b‖ ↔ ∀ n : ℕ, (2 : ℤ_[2]) ^ n ∣ b → (2 : ℤ_[2]) ^ n ∣ a := by
  constructor
  · intro hab n hnb
    rw [dvd_pow_iff_norm_le] at hnb ⊢
    exact le_trans hab hnb
  · intro h
    rcases eq_or_ne b 0 with hb | hb
    · subst hb
      have ha : ∀ n : ℕ, (2 : ℤ_[2]) ^ n ∣ a := fun n => h n (dvd_zero _)
      rcases eq_or_ne a 0 with ha0 | ha0
      · simp [ha0]
      · exfalso
        have h1 := ha (a.valuation + 1)
        rw [dvd_pow_iff_norm_le, PadicInt.norm_le_pow_iff_le_valuation a ha0] at h1
        omega
    · have hbval : (2 : ℤ_[2]) ^ b.valuation ∣ b :=
        (dvd_pow_iff_norm_le b b.valuation).mpr
          ((PadicInt.norm_le_pow_iff_le_valuation b hb b.valuation).mpr (le_refl _))
      have hda := h b.valuation hbval
      rw [dvd_pow_iff_norm_le] at hda
      rw [PadicInt.norm_eq_zpow_neg_valuation hb]
      exact hda

/-- **(A.2) Bernstein–Lagarias.** A map on `ℤ₂` is **solenoidal iff it is nonexpanding** for the
2-adic metric: `Solenoidal F ↔ ∀ x y, ‖F x - F y‖ ≤ ‖x - y‖`. **Proved.** The nonexpanding ⟹
solenoidal direction is just `2ⁿ ∣ (x-y) ∣ (F x - F y)` (transitivity, via the general norm-divisor
dictionary `PadicInt.dvd_iff_norm_le`); the converse reads the norm bound off all the
power-of-`2` divisors (`norm_le_iff_forall_dvd`). -/
@[category research solved, AMS 11 37, ref "BL96", group "bl_solenoidal_maps"]
theorem solenoidal_iff_nonExpanding (F : ℤ_[2] → ℤ_[2]) :
    Solenoidal F ↔ Nonexpanding F := by
  constructor
  · intro h x y
    exact (norm_le_iff_forall_dvd (F x - F y) (x - y)).mpr (fun n hn => h n x y hn)
  · intro h n x y hxy
    exact hxy.trans ((PadicInt.dvd_iff_norm_le (x - y) (F x - F y)).mpr (h x y))

/-- **Solenoidal maps are closed under composition** (Bernstein–Lagarias, Appendix A): if `F₁` and
`F₂` are solenoidal then so is `F₁ ∘ F₂`. (A congruence `x ≡ y (mod 2ⁿ)` is preserved by `F₂`, then
by `F₁`.) -/
@[category research solved, AMS 11 37, ref "BL96", group "bl_solenoidal_maps"]
theorem Solenoidal.comp {F₁ F₂ : ℤ_[2] → ℤ_[2]} (h₁ : Solenoidal F₁) (h₂ : Solenoidal F₂) :
    Solenoidal (F₁ ∘ F₂) :=
  fun n x y hxy => h₁ n (F₂ x) (F₂ y) (h₂ n x y hxy)

/-! ### Lemma A.1: solenoidal maps are the inverse limits of compatible families

`ℤ₂` is the inverse limit `lim ℤ/2ⁿℤ` along the reduction projections `πₙ : ℤ/2ⁿ⁺¹ℤ → ℤ/2ⁿℤ`. A
**compatible family** `{Fₙ : ℤ/2ⁿℤ → ℤ/2ⁿℤ}` (one commuting with the projections) therefore has an
**inverse limit** `F : ℤ₂ → ℤ₂` with `F(x) ≡ Fₙ(x) (mod 2ⁿ)` for all `n` `(A.3)`; Lemma A.1 says these
inverse limits are *exactly* the solenoidal maps — which justifies the name (`ℤ₂` is the 2-adic
*solenoid*). -/

/-- `x ≡ y (mod 2ⁿ)` in residue-ring terms: `toZModPow n x = toZModPow n y ↔ 2ⁿ ∣ (x - y)` (the
residue map `ℤ₂ → ℤ/2ⁿℤ` has kernel `(2ⁿ)`). -/
@[category API, AMS 11 37, ref "BL96"]
theorem toZModPow_eq_iff_dvd_sub (x y : ℤ_[2]) (n : ℕ) :
    PadicInt.toZModPow n x = PadicInt.toZModPow n y ↔ (2 : ℤ_[2]) ^ n ∣ (x - y) := by
  rw [← sub_eq_zero, ← map_sub]
  have e2 : ((2 : ℕ) : ℤ_[2]) = (2 : ℤ_[2]) := by norm_num
  rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton, e2]

/-- A family `{Fₙ : ℤ/2ⁿℤ → ℤ/2ⁿℤ}` is **compatible** if it commutes with the reduction projections
`πₙ : ℤ/2ⁿ⁺¹ℤ → ℤ/2ⁿℤ` (`ZMod.castHom`): `πₙ ∘ Fₙ₊₁ = Fₙ ∘ πₙ`. -/
@[category API, AMS 11 37, ref "BL96"]
def Compatible (Fam : (n : ℕ) → ZMod (2 ^ n) → ZMod (2 ^ n)) : Prop :=
  ∀ (n : ℕ) (r : ZMod (2 ^ (n + 1))),
    (ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ n)) (ZMod (2 ^ n))) (Fam (n + 1) r)
      = Fam n ((ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ n)) (ZMod (2 ^ n))) r)

/-- `F : ℤ₂ → ℤ₂` is the **inverse limit** of a family `{Fₙ}` if `(A.3)` `F(x) ≡ Fₙ(x) (mod 2ⁿ)` for
every `n`, i.e. `toZModPow n (F x) = Fₙ (toZModPow n x)`. -/
@[category API, AMS 11 37, ref "BL96"]
def IsInverseLimit (F : ℤ_[2] → ℤ_[2]) (Fam : (n : ℕ) → ZMod (2 ^ n) → ZMod (2 ^ n)) : Prop :=
  ∀ (n : ℕ) (x : ℤ_[2]), PadicInt.toZModPow n (F x) = Fam n (PadicInt.toZModPow n x)

/-- **Lemma A.1 (Bernstein–Lagarias).** `F` is **solenoidal iff it is the inverse limit of a
compatible family** `{Fₙ}`. **Proved.** If `F` is solenoidal, the residue-induced maps
`Fₙ(r) := toZModPow n (F r̃)` (for any lift `r̃` of `r`, well defined by solenoidality) form a
compatible family with inverse limit `F`; conversely `(A.3)` transports congruences `mod 2ⁿ` through
`F`. The induced family is constructed via the canonical lift `r ↦ (r.val : ℤ₂)`, and compatibility
comes from `PadicInt.zmod_cast_comp_toZModPow`. -/
@[category research solved, AMS 11 37, ref "BL96", group "bl_solenoidal_maps"]
theorem solenoidal_iff_isInverseLimit (F : ℤ_[2] → ℤ_[2]) :
    Solenoidal F ↔ ∃ Fam, Compatible Fam ∧ IsInverseLimit F Fam := by
  have hsect : ∀ (n : ℕ) (s : ZMod (2 ^ n)), PadicInt.toZModPow n ((s.val : ℕ) : ℤ_[2]) = s :=
    fun n s => by rw [map_natCast, ZMod.natCast_val, ZMod.cast_id]
  constructor
  · intro hsol
    refine ⟨fun n s => PadicInt.toZModPow n (F ((s.val : ℕ) : ℤ_[2])), ?_, ?_⟩
    · intro n r
      have hcast : (ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ n)) (ZMod (2 ^ n)))
          (PadicInt.toZModPow (n + 1) (F (((r.val : ℕ) : ℤ_[2]))))
          = PadicInt.toZModPow n (F (((r.val : ℕ) : ℤ_[2]))) := by
        rw [← RingHom.comp_apply, PadicInt.zmod_cast_comp_toZModPow n (n + 1) (Nat.le_succ n)]
      have hcr : (ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ n)) (ZMod (2 ^ n))) r
          = PadicInt.toZModPow n (((r.val : ℕ) : ℤ_[2])) := by
        rw [map_natCast, ZMod.natCast_val, ZMod.castHom_apply]
      show (ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ n)) (ZMod (2 ^ n)))
          (PadicInt.toZModPow (n + 1) (F (((r.val : ℕ) : ℤ_[2]))))
          = PadicInt.toZModPow n (F ((((ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ n))
              (ZMod (2 ^ n))) r).val : ℕ) : ℤ_[2]))
      rw [hcast, hcr]
      exact (toZModPow_eq_iff_dvd_sub _ _ n).mpr
        (hsol n _ _ ((toZModPow_eq_iff_dvd_sub _ _ n).mp (hsect n _).symm))
    · intro n x
      show PadicInt.toZModPow n (F x)
          = PadicInt.toZModPow n (F (((PadicInt.toZModPow n x).val : ℕ) : ℤ_[2]))
      exact (toZModPow_eq_iff_dvd_sub _ _ n).mpr
        (hsol n x _ ((toZModPow_eq_iff_dvd_sub _ _ n).mp (hsect n _).symm))
  · rintro ⟨Fam, _hcompat, hlim⟩
    intro n x y hxy
    rw [← toZModPow_eq_iff_dvd_sub, hlim n x, hlim n y]
    congr 1
    exact (toZModPow_eq_iff_dvd_sub x y n).mpr hxy

/-! ### Lemma A.2: bijective inverse limits -/

/-- **Existence of inverse-limit points.** A **compatible thread** of residues
`c : ∀ n, ℤ/2ⁿℤ` (`castHom (c (n+1)) = c n`) is realised by a `2`-adic integer:
`∃ z, ∀ n, toZModPow n z = c n`. (The thread's `ℤ`-lifts `n ↦ (c n).val` are `2`-adically Cauchy, by
`PadicInt.ofIntSeq`/`isCauSeq_padicNorm_of_pow_dvd_sub`.) -/
@[category API, AMS 11 37, ref "BL96"]
theorem exists_toZModPow_eq_thread (c : (n : ℕ) → ZMod (2 ^ n))
    (hc : ∀ n, (ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ n)) (ZMod (2 ^ n))) (c (n + 1)) = c n) :
    ∃ z : ℤ_[2], ∀ n, PadicInt.toZModPow n z = c n := by
  have hi : ∀ i, ((2 : ℕ) : ℤ) ^ i ∣ ((c (i + 1)).val : ℤ) - ((c i).val : ℤ) := by
    intro i
    have h1 : ((c (i + 1)).val : ZMod (2 ^ i)) = ((c i).val : ZMod (2 ^ i)) := by
      simpa [ZMod.castHom_apply, ZMod.natCast_val] using hc i
    rw [ZMod.natCast_eq_natCast_iff] at h1
    have hd : ((2 : ℕ) : ℤ) ^ i ∣ ((c i).val : ℤ) - ((c (i + 1)).val : ℤ) := by
      exact_mod_cast Nat.modEq_iff_dvd.mp h1
    have hneg : ((c (i + 1)).val : ℤ) - ((c i).val : ℤ)
        = -(((c i).val : ℤ) - ((c (i + 1)).val : ℤ)) := by ring
    rw [hneg]; exact dvd_neg.mpr hd
  refine ⟨PadicInt.ofIntSeq (fun n => ((c n).val : ℤ))
      (isCauSeq_padicNorm_of_pow_dvd_sub _ 2 hi), fun n => ?_⟩
  rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub _ 2 hi n]
  push_cast
  rw [ZMod.natCast_val, ZMod.cast_id]

/-- **Every compatible family has an inverse limit** (the existence companion to Lemma A.1):
`Compatible Fam → ∃ F, IsInverseLimit F Fam`. For each `x`, the thread `n ↦ Fₙ (toZModPow n x)` is
compatible (by `Compatible` and `PadicInt.zmod_cast_comp_toZModPow`), hence realised by a point
`F x` (`exists_toZModPow_eq_thread`); `Classical.axiomOfChoice` assembles these into `F`. -/
@[category research solved, AMS 11 37, ref "BL96", group "bl_solenoidal_maps"]
theorem exists_isInverseLimit_of_compatible (Fam : (n : ℕ) → ZMod (2 ^ n) → ZMod (2 ^ n))
    (h : Compatible Fam) : ∃ F, IsInverseLimit F Fam := by
  have key : ∀ x : ℤ_[2], ∃ z : ℤ_[2],
      ∀ n, PadicInt.toZModPow n z = Fam n (PadicInt.toZModPow n x) := by
    intro x
    apply exists_toZModPow_eq_thread (fun n => Fam n (PadicInt.toZModPow n x))
    intro n
    rw [h n (PadicInt.toZModPow (n + 1) x), ← RingHom.comp_apply,
      PadicInt.zmod_cast_comp_toZModPow n (n + 1) (Nat.le_succ n)]
  obtain ⟨F, hF⟩ := Classical.axiomOfChoice key
  exact ⟨F, fun n x => hF x n⟩

/-- **Lemma A.2 (Bernstein–Lagarias).** For `U` the inverse limit of a compatible family `{Uₙ}`, the
following are **equivalent**:
1. `U` is a **bijection**;
2. each `Uₙ` is a **permutation** of `ℤ/2ⁿℤ`;
3. `U` **reflects** congruences mod `2ⁿ`: `U(x) ≡ U(y) (mod 2ⁿ) ⟹ x ≡ y (mod 2ⁿ)`.

**Proved.** `1 ⇒ 2`: `U` surjective makes each `Uₙ` surjective, hence a permutation (finite).
`2 ⇒ 3`: each `Uₙ` is injective. `3 ⇒ 2`: each `Uₙ` is injective, hence a permutation (finite).
`2 ⇒ 1`: the pointwise inverses `{Uₙ⁻¹}` form a compatible family whose inverse limit `W`
(`exists_isInverseLimit_of_compatible`) is a two-sided inverse of `U`. -/
@[category research solved, AMS 11 37, ref "BL96", group "bl_solenoidal_maps"]
theorem lemma_A2 (U : ℤ_[2] → ℤ_[2]) (Fam : (n : ℕ) → ZMod (2 ^ n) → ZMod (2 ^ n))
    (hcompat : Compatible Fam) (hlim : IsInverseLimit U Fam) :
    List.TFAE [Function.Bijective U, ∀ n, Function.Bijective (Fam n),
               ∀ (n : ℕ) (x y : ℤ_[2]),
                 PadicInt.toZModPow n (U x) = PadicInt.toZModPow n (U y)
                 → PadicInt.toZModPow n x = PadicInt.toZModPow n y] := by
  have hsect : ∀ (n : ℕ) (s : ZMod (2 ^ n)), PadicInt.toZModPow n ((s.val : ℕ) : ℤ_[2]) = s :=
    fun n s => by rw [map_natCast, ZMod.natCast_val, ZMod.cast_id]
  tfae_have 1 → 2 := by
    rintro hU n
    have : NeZero ((2 : ℕ) ^ n) := ⟨pow_ne_zero n (by norm_num)⟩
    have hsurj : Function.Surjective (Fam n) := fun s => by
      obtain ⟨x, hx⟩ := hU.surjective (((s.val : ℕ) : ℤ_[2]))
      exact ⟨PadicInt.toZModPow n x, by rw [← hlim n x, hx]; exact hsect n s⟩
    exact ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
  tfae_have 2 → 3 := by
    rintro hperm n x y hxy
    rw [hlim n x, hlim n y] at hxy
    exact (hperm n).injective hxy
  tfae_have 3 → 2 := by
    rintro hrefl n
    have : NeZero ((2 : ℕ) ^ n) := ⟨pow_ne_zero n (by norm_num)⟩
    have hinj : Function.Injective (Fam n) := fun a b hab => by
      have key : PadicInt.toZModPow n (U (((a.val : ℕ) : ℤ_[2])))
          = PadicInt.toZModPow n (U (((b.val : ℕ) : ℤ_[2]))) := by
        rw [hlim n _, hlim n _, hsect n a, hsect n b]; exact hab
      have hxy := hrefl n _ _ key
      rwa [hsect n a, hsect n b] at hxy
    exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩
  tfae_have 2 → 1 := by
    rintro hperm
    have hVcompat : Compatible (fun n => Function.invFun (Fam n)) := by
      intro n s
      obtain ⟨r, rfl⟩ := (hperm (n + 1)).surjective s
      show (ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ n)) (ZMod (2 ^ n)))
            (Function.invFun (Fam (n + 1)) (Fam (n + 1) r))
          = Function.invFun (Fam n)
            ((ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ n)) (ZMod (2 ^ n))) (Fam (n + 1) r))
      rw [Function.leftInverse_invFun (hperm (n + 1)).injective r, hcompat n r,
        Function.leftInverse_invFun (hperm n).injective _]
    obtain ⟨W, hW⟩ := exists_isInverseLimit_of_compatible _ hVcompat
    refine Function.bijective_iff_has_inverse.mpr ⟨W, fun x => ?_, fun z => ?_⟩
    · rw [← PadicInt.ext_of_toZModPow]; intro n
      rw [hW n (U x), hlim n x]
      exact Function.leftInverse_invFun (hperm n).injective _
    · rw [← PadicInt.ext_of_toZModPow]; intro n
      rw [hlim n (W z), hW n z]
      exact Function.rightInverse_invFun (hperm n).surjective _
  tfae_finish

/-! ### Corollary A.3: solenoidal bijection = isometry -/

/-- **Solenoidal maps are continuous.** A solenoidal map is nonexpanding
(`solenoidal_iff_nonExpanding`), hence `1`-Lipschitz for the 2-adic metric, hence continuous. So a
solenoidal bijection with solenoidal inverse is automatically a homeomorphism. -/
@[category API, AMS 11 37, ref "BL96"]
theorem solenoidal_continuous (U : ℤ_[2] → ℤ_[2]) (hU : Solenoidal U) : Continuous U := by
  have hne := (solenoidal_iff_nonExpanding U).mp hU
  have hlip : LipschitzWith 1 U := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    rw [dist_eq_norm, dist_eq_norm]
    simpa using hne x y
  exact hlip.continuous

/-- `U` **reflects** congruences mod `2ⁿ` iff it is **expanding**, `‖x - y‖ ≤ ‖U x - U y‖`. (The
norm-comparison `norm_le_iff_forall_dvd` rephrased through `toZModPow_eq_iff_dvd_sub`.) Together with
`solenoidal_iff_nonExpanding` (the `≤` half), this is what upgrades a solenoidal bijection to an
isometry. -/
@[category API, AMS 11 37, ref "BL96"]
theorem reflects_iff_norm_le (U : ℤ_[2] → ℤ_[2]) :
    (∀ (n : ℕ) (x y : ℤ_[2]), PadicInt.toZModPow n (U x) = PadicInt.toZModPow n (U y)
        → PadicInt.toZModPow n x = PadicInt.toZModPow n y)
      ↔ ∀ x y : ℤ_[2], ‖x - y‖ ≤ ‖U x - U y‖ := by
  constructor
  · intro h x y
    rw [norm_le_iff_forall_dvd]
    intro n hn
    rw [← toZModPow_eq_iff_dvd_sub]
    exact h n x y ((toZModPow_eq_iff_dvd_sub _ _ n).mpr hn)
  · intro h n x y hxy
    rw [toZModPow_eq_iff_dvd_sub]
    exact (norm_le_iff_forall_dvd (x - y) (U x - U y)).mp (h x y) n
      ((toZModPow_eq_iff_dvd_sub _ _ n).mp hxy)

/-- **Corollary A.3 (Bernstein–Lagarias).** For `U : ℤ₂ → ℤ₂` the following are **equivalent**:
1. `U` is a **solenoidal bijection** (`Solenoidal U ∧ Bijective U`);
2. `U` is a **solenoidal homeomorphism** (`Solenoidal U ∧ Bijective U ∧ Solenoidal (Function.invFun U)`
   — both `U` and its inverse solenoidal, hence both continuous by `solenoidal_continuous`, so a
   genuine homeomorphism);
3. `U` is a **2-adic isometry**: `‖U x - U y‖ = ‖x - y‖` for all `x, y`.

**Proved.** `1 ⇒ 3`: solenoidal gives `≤` (`solenoidal_iff_nonExpanding`); bijective gives `≥` via
Lemma A.1 (`U` is an inverse limit) and Lemma A.2 (`i ⇒ iii`, `U` reflects congruences,
`reflects_iff_norm_le`). `3 ⇒ 2`: `≤` ⟹ solenoidal; `≥` ⟹ reflects ⟹ (Lemma A.2 `iii ⇒ i`) bijective;
the isometry passes to `U⁻¹`, which is therefore solenoidal too. `2 ⇒ 1`: immediate. -/
@[category research solved, AMS 11 37, ref "BL96", group "bl_solenoidal_maps"]
theorem corollary_A3 (U : ℤ_[2] → ℤ_[2]) :
    List.TFAE [Solenoidal U ∧ Function.Bijective U,
               Solenoidal U ∧ Function.Bijective U ∧ Solenoidal (Function.invFun U),
               ∀ x y : ℤ_[2], ‖U x - U y‖ = ‖x - y‖] := by
  tfae_have 1 → 3 := by
    rintro ⟨hsol, hbij⟩ x y
    refine le_antisymm ((solenoidal_iff_nonExpanding U).mp hsol x y) ?_
    obtain ⟨Fam, hcompat, hlim⟩ := (solenoidal_iff_isInverseLimit U).mp hsol
    exact (reflects_iff_norm_le U).mp (((lemma_A2 U Fam hcompat hlim).out 1 3).mp hbij) x y
  tfae_have 3 → 2 := by
    intro hiso
    have hsol : Solenoidal U :=
      (solenoidal_iff_nonExpanding U).mpr (fun x y => le_of_eq (hiso x y))
    have hbij : Function.Bijective U := by
      obtain ⟨Fam, hcompat, hlim⟩ := (solenoidal_iff_isInverseLimit U).mp hsol
      exact ((lemma_A2 U Fam hcompat hlim).out 1 3).mpr
        ((reflects_iff_norm_le U).mpr (fun x y => ge_of_eq (hiso x y)))
    refine ⟨hsol, hbij, (solenoidal_iff_nonExpanding _).mpr (fun a b => le_of_eq ?_)⟩
    rw [← hiso (Function.invFun U a) (Function.invFun U b),
      Function.rightInverse_invFun hbij.surjective a,
      Function.rightInverse_invFun hbij.surjective b]
  tfae_have 2 → 1 := fun ⟨hsol, hbij, _⟩ => ⟨hsol, hbij⟩
  tfae_finish

end BL
