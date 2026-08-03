/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import ForMathlib.NumberTheory.PadicFracPart
import TH.Solenoid.Haar
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The character group of `Σ₆`, and the frequency collapse `χ_r ∘ T = χ_{(3/2)r}`

Work package W3 of plan-A1+ (§4, L3), first half.  The dual of the solenoid
`Σ₆ = (ℝ × ℚ₂ × ℚ₃)/ℤ[1/6]` is the *discrete* group `ℤ[1/6]`: for `r ∈ ℤ[1/6]`,

`χ_r [x, y, z] = r x - {r y}₂ - {r z}₃ ∈ ℝ/ℤ`,

where `{·}_p = Padic.fracPart p` is the canonical character of `ℚ_[p]` with kernel `ℤ_[p]`
(`ForMathlib/NumberTheory/PadicFracPart.lean`).  Well-definedness is the *partial fraction*
identity: for `s ∈ ℤ[1/6]`, writing `s = m/6ᵏ = mv/2ᵏ + mu/3ᵏ` with `u 2ᵏ + v 3ᵏ = 1` (Bézout),
the `2`-adic principal part of `s` is `mv/2ᵏ` and its `3`-adic principal part is `mu/3ᵏ`, so

`s - {s}₂ - {s}₃ = 0` exactly (`charRat_eq_zero`).

Three facts make this the right family:

* **On the winding line the finite places are invisible**: `χ_r (wind ξ) = [r ξ]`
  (`χ_wind`), because `wind ξ = [(ξ, 0, 0)]` and `fracPart p 0 = 0`.  So the Birkhoff sums of
  `χ_r` along the `T`-orbit of `wind ξ` are literally the Weyl sums of `(r ξ (3/2)ⁿ)`.
* **Frequency collapse**: `χ_r ∘ T = χ_{(3/2) r}` (`χ_T32`), *exactly* — not up to `O(1/N)`.
  Hence the Weyl data of an orbit factors through `(ℤ[1/6] \ {0}) / ⟨3/2⟩`.  This is the
  conceptual home of `Z32.weylSum_collapse` (`Z32/PairStatistics.lean`), which is the same
  statement at integer frequencies.
* **Separation**: the `χ_r` separate the points of `Σ₆` (`exists_χ_ne_zero`), by a three-case
  argument on the fundamental-domain representative — the archimedean coordinate is caught by
  `r = 1`, the `2`-adic one by `r = 2⁻ᵏ`, the `3`-adic one by `r = 3⁻ᵏ`.

Composing with `AddCircle.toCircle` turns the `χ_r` into the continuous functions
`e r : C(Σ₆, ℂ)`; they span a self-adjoint unital subalgebra, so Stone–Weierstrass gives density
(`charSubalgebra_closure_eq_top`), which is what makes the Weyl dictionary of
`TH/Solenoid/Dictionary.lean` an equivalence rather than an implication.  The pattern is Mathlib's
own `fourierSubalgebra` for `AddCircle`.

Finally `integral_e_eq_zero`: a non-trivial character integrates to `0` against Haar measure —
the orthogonality that turns "all Weyl sums vanish" into "the empirical measures converge".

## Main statements

* `charRat_eq_zero` — the partial-fraction identity `s = {s}₂ + {s}₃` in `ℝ/ℤ` for `s ∈ ℤ[1/6]`.
* `χ`, `χ_mk`, `χ_add`, `continuous_χ` — the characters.
* `χ_wind`, `χ_T32`, `χ_T32_iter` — the winding line and the **frequency collapse**.
* `exists_χ_ne_zero`, `χ_separatesPoints` — the characters separate points.
* `e`, `charSubalgebra_closure_eq_top` — Stone–Weierstrass density in `C(Σ₆, ℂ)`.
* `integral_e_eq_zero` — orthogonality against Haar measure.

## References

Plan A1+ §2.2 (the box "The Weyl dictionary") and §4 (L3).  For the duality
`(ℝ × ℚ₂ × ℚ₃)/ℤ[1/6]` ↔ `ℤ[1/6]` see [EW11, Ch. 8] or [Sch95]; the concrete formula is the
adelic character restricted to the three places of `S = {∞, 2, 3}`.
-/

namespace TH.S6

open Metric Set MeasureTheory
open scoped ENNReal

/-! ### The character attached to a rational frequency -/

/-- The value `s - {s}₂ - {s}₃ ∈ ℝ/ℤ` attached to a rational `s`.  It vanishes exactly on
`ℤ[1/6]` — the "product formula" that makes `χ_r` well defined on the quotient. -/
noncomputable def charRat (t : ℚ) : AddCircle (1 : ℝ) :=
  ((t : ℝ) : AddCircle (1 : ℝ)) - Padic.fracPart 2 ((t : ℚ_[2])) - Padic.fracPart 3 ((t : ℚ_[3]))

/-- **The partial-fraction identity.**  For `s = m/6ᵏ ∈ ℤ[1/6]`, Bézout splits `s` into a `2`-adic
principal part `mv/2ᵏ` and a `3`-adic principal part `mu/3ᵏ` (`u·2ᵏ + v·3ᵏ = 1`); each is invisible
at the other finite place, so it *is* the principal part there, and `s - {s}₂ - {s}₃ = 0`. -/
@[category research solved, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem charRat_eq_zero {t : ℚ} (ht : t ∈ Z16) : charRat t = 0 := by
  obtain ⟨m, k, rfl⟩ := ht
  have hcop : IsCoprime ((2 ^ k : ℕ) : ℤ) ((3 ^ k : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow k k (by decide : Nat.Coprime 2 3))
  obtain ⟨u, v, huv⟩ := hcop
  have hu : (u : ℚ) * 2 ^ k + (v : ℚ) * 3 ^ k = 1 := by exact_mod_cast huv
  set a : ℚ := ((m * v : ℤ) : ℚ) / (2 : ℚ) ^ k with ha
  set b : ℚ := ((m * u : ℤ) : ℚ) / (3 : ℚ) ^ k with hb
  have h6 : (6 : ℚ) ^ k = 2 ^ k * 3 ^ k := by
    rw [show (6 : ℚ) = 2 * 3 by norm_num, mul_pow]
  have hsum : (m : ℚ) / 6 ^ k = a + b := by
    have hm : (m : ℚ) = m * ((u : ℚ) * 2 ^ k + (v : ℚ) * 3 ^ k) := by rw [hu]; ring
    rw [ha, hb, h6]
    push_cast
    field_simp
    linear_combination (-(m : ℚ)) * hu
  -- the two principal parts
  have h2 : Padic.fracPart 2 ((((m : ℚ) / 6 ^ k : ℚ)) : ℚ_[2]) = ((a : ℝ) : AddCircle (1 : ℝ)) := by
    have hnb : padicNorm 2 b ≤ 1 := by
      rw [hb]
      simpa using padicNorm_intCast_div_natPow_le_one (p := 2) (q := 3) (by decide) (m * u) k
    have hdiff : (m : ℚ) / 6 ^ k - ((m * v : ℤ) : ℚ) / ((2 : ℕ) : ℚ) ^ k = b := by
      rw [hsum, ha]; push_cast; ring
    have := Padic.fracPart_ratCast_eq (p := 2) (m := m * v) (k := k) (by rw [hdiff]; exact hnb)
    rw [this, ha]
    norm_num
  have h3 : Padic.fracPart 3 ((((m : ℚ) / 6 ^ k : ℚ)) : ℚ_[3]) = ((b : ℝ) : AddCircle (1 : ℝ)) := by
    have hna : padicNorm 3 a ≤ 1 := by
      rw [ha]
      simpa using padicNorm_intCast_div_natPow_le_one (p := 3) (q := 2) (by decide) (m * v) k
    have hdiff : (m : ℚ) / 6 ^ k - ((m * u : ℤ) : ℚ) / ((3 : ℕ) : ℚ) ^ k = a := by
      rw [hsum, hb]; push_cast; ring
    have := Padic.fracPart_ratCast_eq (p := 3) (m := m * u) (k := k) (by rw [hdiff]; exact hna)
    rw [this, hb]
    norm_num
  rw [charRat, h2, h3, ← QuotientAddGroup.mk_sub, ← QuotientAddGroup.mk_sub]
  have hR : ((((m : ℚ) / 6 ^ k : ℚ) : ℝ)) - (a : ℝ) - (b : ℝ) = 0 := by
    rw [hsum]; push_cast; ring
  rw [hR]
  exact QuotientAddGroup.mk_zero _

/-! ### The character of `G₆` attached to a frequency -/

/-- The character of the ambient group `G₆ = ℝ × ℚ₂ × ℚ₃` at frequency `r ∈ ℚ`:
`(x, y, z) ↦ r x - {r y}₂ - {r z}₃`. -/
noncomputable def charG (r : ℚ) : G6 →+ AddCircle (1 : ℝ) where
  toFun g := (((r : ℝ) * g.1 : ℝ) : AddCircle (1 : ℝ))
    - Padic.fracPart 2 ((r : ℚ_[2]) * g.2.1) - Padic.fracPart 3 ((r : ℚ_[3]) * g.2.2)
  map_zero' := by simp [Padic.fracPart_zero]
  map_add' g h := by
    simp only [Prod.fst_add, Prod.snd_add, mul_add]
    rw [Padic.fracPart_add, Padic.fracPart_add, QuotientAddGroup.mk_add]
    abel

@[category API, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem charG_apply (r : ℚ) (g : G6) :
    charG r g = (((r : ℝ) * g.1 : ℝ) : AddCircle (1 : ℝ))
      - Padic.fracPart 2 ((r : ℚ_[2]) * g.2.1) - Padic.fracPart 3 ((r : ℚ_[3]) * g.2.2) := rfl

/-- The frequency enters additively: `χ_{r+s} = χ_r + χ_s`. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem charG_add_left (r s : ℚ) (g : G6) : charG (r + s) g = charG r g + charG s g := by
  simp only [charG_apply]
  push_cast
  simp only [add_mul]
  rw [QuotientAddGroup.mk_add, Padic.fracPart_add, Padic.fracPart_add]
  abel

@[category API, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem charG_zero_left (g : G6) : charG 0 g = 0 := by
  simp [charG_apply, Padic.fracPart_zero]

/-- On the diagonal, the character only sees the product of the two frequencies. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem charG_diag (r s : ℚ) : charG r (diag s) = charRat (r * s) := by
  simp only [charG_apply, diag_apply, charRat]
  push_cast
  ring_nf

/-- **The character kills the lattice.**  This is `charRat_eq_zero` applied to `r · s ∈ ℤ[1/6]`. -/
@[category research solved, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem charG_eq_zero_of_mem_Δ₆ {r : ℚ} (hr : r ∈ Z16) {g : G6} (hg : g ∈ Δ₆) :
    charG r g = 0 := by
  obtain ⟨s, hs, rfl⟩ := mem_Δ₆.mp hg
  rw [charG_diag]
  exact charRat_eq_zero (Subring.mul_mem _ hr hs)

@[category API, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem continuous_charG (r : ℚ) : Continuous (charG r) := by
  have h1 : Continuous fun g : G6 => (((r : ℝ) * g.1 : ℝ) : AddCircle (1 : ℝ)) :=
    QuotientAddGroup.continuous_mk.comp (continuous_const.mul continuous_fst)
  have h2 : Continuous fun g : G6 => Padic.fracPart 2 ((r : ℚ_[2]) * g.2.1) :=
    Padic.continuous_fracPart.comp (by fun_prop)
  have h3 : Continuous fun g : G6 => Padic.fracPart 3 ((r : ℚ_[3]) * g.2.2) :=
    Padic.continuous_fracPart.comp (by fun_prop)
  exact (h1.sub h2).sub h3

/-! ### The characters of `Σ₆` -/

/-- **The character of `Σ₆` at frequency `r ∈ ℤ[1/6]`**: `χ_r [x, y, z] = r x - {r y}₂ - {r z}₃`.
The dual group of `Σ₆` is `ℤ[1/6]`, discrete. -/
noncomputable def χ (r : Z16) : S6 →+ AddCircle (1 : ℝ) :=
  QuotientAddGroup.lift Δ₆ (charG (r : ℚ)) fun _ hx => charG_eq_zero_of_mem_Δ₆ r.2 hx

@[category API, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem χ_mk (r : Z16) (g : G6) : χ r (QuotientAddGroup.mk g) = charG (r : ℚ) g := rfl

@[category API, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem χ_add (r s : Z16) (x : S6) : χ (r + s) x = χ r x + χ s x := by
  obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [χ_mk, χ_mk, χ_mk, show ((r + s : Z16) : ℚ) = (r : ℚ) + (s : ℚ) from rfl]
  exact charG_add_left _ _ g

@[category API, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem χ_zero (x : S6) : χ 0 x = 0 := by
  obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [χ_mk, show ((0 : Z16) : ℚ) = (0 : ℚ) from rfl]
  exact charG_zero_left g

@[category API, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem continuous_χ (r : Z16) : Continuous (χ r) := by
  rw [(QuotientAddGroup.isQuotientMap_mk Δ₆).continuous_iff]
  exact continuous_charG (r : ℚ)

/-! ### The winding line and the frequency collapse -/

/-- **On the winding line the finite places are invisible.**  `χ_r (wind ξ) = [r ξ]`: the Birkhoff
sums of `χ_r` along the orbit of `wind ξ` are the Weyl sums of `(r ξ (3/2)ⁿ)`. -/
@[category research solved, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem χ_wind (r : Z16) (ξ : ℝ) :
    χ r (wind ξ) = ((((r : ℚ) : ℝ) * ξ : ℝ) : AddCircle (1 : ℝ)) := by
  rw [wind, χ_mk, charG_apply]
  simp [Padic.fracPart_zero]

/-- `3/2` is a unit of `ℤ[1/6]`, hence acts on the frequency group. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem threeHalves_mem_Z16 : (3 / 2 : ℚ) ∈ Z16 := ⟨9, 1, by norm_num⟩

/-- The frequency `(3/2) r`, the image of `r` under the dual of `T`. -/
noncomputable def freq32 (r : Z16) : Z16 :=
  ⟨(3 / 2 : ℚ) * (r : ℚ), Subring.mul_mem _ threeHalves_mem_Z16 r.2⟩

@[category API, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem freq32_coe (r : Z16) : ((freq32 r : Z16) : ℚ) = (3 / 2 : ℚ) * (r : ℚ) := rfl

/-- **The frequency-collapse lemma**, exactly: `χ_r ∘ T = χ_{(3/2) r}`.  Not an `O(1/N)` estimate —
an identity.  Consequently the Weyl data of a `T`-orbit factors through the quotient of
`ℤ[1/6] \ {0}` by the `⟨3/2⟩`-action, whose canonical representatives are `± m 2⁻ʲ` with
`gcd(m, 6) = 1`.  `Z32.weylSum_collapse` is the shadow of this at integer frequencies. -/
@[category research solved, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem χ_T32 (r : Z16) (x : S6) : χ r (T32 x) = χ (freq32 r) x := by
  obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [T32_mk, χ_mk, χ_mk, charG_apply, charG_apply, freq32_coe]
  have hr : (((3 / 2 : ℚ) • g).1 : ℝ) = (3 / 2 : ℝ) * g.1 := by
    simp [Prod.smul_fst, Rat.smul_def]
  have h2 : (((3 / 2 : ℚ) • g).2.1 : ℚ_[2]) = ((3 / 2 : ℚ) : ℚ_[2]) * g.2.1 := by
    simp [Prod.smul_snd, Prod.smul_fst, Rat.smul_def]
  have h3 : (((3 / 2 : ℚ) • g).2.2 : ℚ_[3]) = ((3 / 2 : ℚ) : ℚ_[3]) * g.2.2 := by
    simp [Prod.smul_snd, Rat.smul_def]
  rw [hr, h2, h3]
  push_cast
  ring_nf

/-- The iterated collapse: the frequency of `χ_r ∘ Tⁿ` is `(3/2)ⁿ r`. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem χ_T32_iter (r : Z16) (n : ℕ) (x : S6) : χ r (T32^[n] x) = χ (freq32^[n] r) x := by
  induction n generalizing r with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', χ_T32, ih, Function.iterate_succ_apply]

/-! ### The characters separate points -/

/-- The frequency `2⁻ᵏ ∈ ℤ[1/6]`, which detects the `2`-adic coordinate at level `k`. -/
noncomputable def invPow2 (k : ℕ) : Z16 :=
  ⟨(1 : ℚ) / (2 : ℚ) ^ k, by simpa using div_two_pow_mem_Z16 1 k⟩

/-- The frequency `3⁻ᵏ ∈ ℤ[1/6]`, which detects the `3`-adic coordinate at level `k`. -/
noncomputable def invPow3 (k : ℕ) : Z16 :=
  ⟨(1 : ℚ) / (3 : ℚ) ^ k, by simpa using div_three_pow_mem_Z16 1 k⟩

@[category API, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem invPow2_coe (k : ℕ) : ((invPow2 k : Z16) : ℚ) = (1 : ℚ) / (2 : ℚ) ^ k := rfl

@[category API, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem invPow3_coe (k : ℕ) : ((invPow3 k : Z16) : ℚ) = (1 : ℚ) / (3 : ℚ) ^ k := rfl

/-- `2⁻ᵏ` is a `3`-adic integer: the frequency that resolves the `2`-adic coordinate does not
disturb the `3`-adic one. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem norm_invPow2_three_le_one (k : ℕ) : ‖(((1 : ℚ) / (2 : ℚ) ^ k : ℚ) : ℚ_[3])‖ ≤ 1 := by
  rw [Padic.eq_padicNorm]
  have := padicNorm_intCast_div_natPow_le_one (p := 3) (q := 2) (by decide) 1 k
  norm_num at this ⊢
  exact_mod_cast this

@[category API, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem norm_invPow3_two_le_one (k : ℕ) : ‖(((1 : ℚ) / (3 : ℚ) ^ k : ℚ) : ℚ_[2])‖ ≤ 1 := by
  rw [Padic.eq_padicNorm]
  have := padicNorm_intCast_div_natPow_le_one (p := 2) (q := 3) (by decide) 1 k
  norm_num at this ⊢
  exact_mod_cast this

/-- The norm of the frequency `2⁻ᵏ` at the place `2`. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem norm_invPow2_two (k : ℕ) : ‖(((1 : ℚ) / (2 : ℚ) ^ k : ℚ) : ℚ_[2])‖ = (2 : ℝ) ^ k := by
  have hc : ((1 : ℚ) / (2 : ℚ) ^ k : ℚ) = ((1 : ℚ) / ((2 : ℕ) : ℚ) ^ k : ℚ) := by norm_num
  rw [hc, Padic.norm_ratCast_inv_pow 2 k]
  norm_num

/-- The norm of the frequency `3⁻ᵏ` at the place `3`. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem norm_invPow3_three (k : ℕ) : ‖(((1 : ℚ) / (3 : ℚ) ^ k : ℚ) : ℚ_[3])‖ = (3 : ℝ) ^ k := by
  have hc : ((1 : ℚ) / (3 : ℚ) ^ k : ℚ) = ((1 : ℚ) / ((3 : ℕ) : ℚ) ^ k : ℚ) := by norm_num
  rw [hc, Padic.norm_ratCast_inv_pow 3 k]
  norm_num

/-- A point of the fundamental domain whose real coordinate lies in `(0, 1)` is not killed by the
trivial-frequency character. -/
private theorem coe_ne_zero_of_mem_Ioo {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) (ht : t ≠ 0) :
    ((t : ℝ) : AddCircle (1 : ℝ)) ≠ 0 := by
  intro hcon
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hcon
  rw [zsmul_eq_mul, mul_one] at hn
  have hn0 : n = 0 := by
    have h1' : (n : ℝ) < 1 := by rw [hn]; exact h1
    have h0' : (0 : ℝ) ≤ (n : ℝ) := by rw [hn]; exact h0
    have : (0 : ℤ) ≤ n := by exact_mod_cast h0'
    have : n < 1 := by exact_mod_cast h1'
    omega
  rw [hn0] at hn
  exact ht (by simpa using hn.symm)

/-- **The characters separate the origin.**  Given `x ≠ 0` in `Σ₆`, some `χ_r` does not kill it.
The proof is a three-case argument on the fundamental-domain representative `(t, y, z)`: if
`t ≠ 0` take `r = 1` (both finite places are then invisible); if `t = 0` and `y ≠ 0` take
`r = 2⁻ᵏ` with `2ᵏ‖y‖ > 1`, which pushes `y` out of `ℤ₂` while leaving `z` in `ℤ₃`; symmetrically
for `z`. -/
@[category research solved, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem exists_χ_ne_zero {x : S6} (hx : x ≠ 0) : ∃ r : Z16, χ r x ≠ 0 := by
  obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨d, ⟨hdD, hd⟩, -⟩ := exists_unique_fundamental g
  have hmk : (QuotientAddGroup.mk g : S6) = QuotientAddGroup.mk d := by
    rw [QuotientAddGroup.eq, neg_add_eq_sub]
    have hneg := AddSubgroup.neg_mem _ hd
    rwa [neg_sub] at hneg
  rw [hmk] at hx ⊢
  rw [mem_D] at hdD
  obtain ⟨⟨ht0, ht1⟩, hy, hz⟩ := hdD
  have hd0 : ¬ (d.1 = 0 ∧ d.2.1 = 0 ∧ d.2.2 = 0) := by
    rintro ⟨h1, h2, h3⟩
    refine hx ?_
    have hzero : d = 0 := Prod.ext_iff.mpr ⟨h1, Prod.ext_iff.mpr ⟨h2, h3⟩⟩
    rw [hzero]
    exact QuotientAddGroup.mk_zero _
  by_cases ht : d.1 = 0
  · by_cases hy0 : d.2.1 = 0
    · -- the `3`-adic coordinate is the non-zero one: the frequency `3⁻ᵏ` detects it
      have hz0 : d.2.2 ≠ 0 := fun h => hd0 ⟨ht, hy0, h⟩
      have hzpos : 0 < ‖d.2.2‖ := norm_pos_iff.mpr hz0
      obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / ‖d.2.2‖) (by norm_num : (1 : ℝ) < 3)
      rw [div_lt_iff₀ hzpos] at hk
      have hgt : 1 < ‖(((1 : ℚ) / (3 : ℚ) ^ k : ℚ) : ℚ_[3]) * d.2.2‖ := by
        rw [norm_mul, norm_invPow3_three]
        linarith
      refine ⟨invPow3 k, ?_⟩
      have hval : χ (invPow3 k) (QuotientAddGroup.mk d)
          = - Padic.fracPart 3 ((((1 : ℚ) / (3 : ℚ) ^ k : ℚ) : ℚ_[3]) * d.2.2) := by
        rw [χ_mk, charG_apply, invPow3_coe, ht, hy0, mul_zero, mul_zero, Padic.fracPart_zero,
          QuotientAddGroup.mk_zero]
        abel
      rw [hval, neg_ne_zero]
      exact fun hcon => absurd (Padic.fracPart_eq_zero_iff.mp hcon) (not_le.mpr hgt)
    · -- the `2`-adic coordinate is the non-zero one: the frequency `2⁻ᵏ` detects it
      have hypos : 0 < ‖d.2.1‖ := norm_pos_iff.mpr hy0
      obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / ‖d.2.1‖) (by norm_num : (1 : ℝ) < 2)
      rw [div_lt_iff₀ hypos] at hk
      have hgt : 1 < ‖(((1 : ℚ) / (2 : ℚ) ^ k : ℚ) : ℚ_[2]) * d.2.1‖ := by
        rw [norm_mul, norm_invPow2_two]
        linarith
      have h3int : ‖(((1 : ℚ) / (2 : ℚ) ^ k : ℚ) : ℚ_[3]) * d.2.2‖ ≤ 1 := by
        rw [norm_mul]
        exact mul_le_one₀ (norm_invPow2_three_le_one k) (norm_nonneg _) hz
      refine ⟨invPow2 k, ?_⟩
      have hval : χ (invPow2 k) (QuotientAddGroup.mk d)
          = - Padic.fracPart 2 ((((1 : ℚ) / (2 : ℚ) ^ k : ℚ) : ℚ_[2]) * d.2.1) := by
        rw [χ_mk, charG_apply, invPow2_coe, ht, mul_zero, QuotientAddGroup.mk_zero,
          Padic.fracPart_of_norm_le_one h3int]
        abel
      rw [hval, neg_ne_zero]
      exact fun hcon => absurd (Padic.fracPart_eq_zero_iff.mp hcon) (not_le.mpr hgt)
  · -- the archimedean coordinate is the non-zero one: the frequency `1` detects it
    refine ⟨1, ?_⟩
    have hval : χ (1 : Z16) (QuotientAddGroup.mk d) = ((d.1 : ℝ) : AddCircle (1 : ℝ)) := by
      rw [χ_mk, charG_apply, show ((1 : Z16) : ℚ) = (1 : ℚ) from rfl]
      simp only [Rat.cast_one, one_mul]
      rw [Padic.fracPart_of_norm_le_one hy, Padic.fracPart_of_norm_le_one hz, sub_zero, sub_zero]
    rw [hval]
    exact coe_ne_zero_of_mem_Ioo ht0 ht1 ht

/-- **The characters separate points.** -/
@[category research solved, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem χ_separatesPoints {x y : S6} (hxy : x ≠ y) : ∃ r : Z16, χ r x ≠ χ r y := by
  obtain ⟨r, hr⟩ := exists_χ_ne_zero (sub_ne_zero.mpr hxy)
  refine ⟨r, fun hcon => hr ?_⟩
  rw [map_sub, hcon, sub_self]

/-! ### The characters as continuous complex functions -/

/-- The character `χ_r` read as a continuous function `Σ₆ → ℂ` of modulus one:
`e r x = exp(2π i · χ_r x)`.  This is `fourier 1` of `AddCircle 1` pulled back along `χ_r`. -/
noncomputable def e (r : Z16) : C(S6, ℂ) := (fourier (T := (1 : ℝ)) 1).comp ⟨χ r, continuous_χ r⟩

@[category API, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem e_apply (r : Z16) (x : S6) : e r x = (AddCircle.toCircle (χ r x) : ℂ) := fourier_one

@[category API, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem χ_neg (r : Z16) (x : S6) : χ (-r) x = - χ r x := by
  have h := χ_add r (-r) x
  rw [add_neg_cancel, χ_zero] at h
  linear_combination (norm := abel) -h

@[category API, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem toCircle_neg (a : AddCircle (1 : ℝ)) :
    AddCircle.toCircle (-a) = (AddCircle.toCircle a)⁻¹ := by
  have h := AddCircle.toCircle_add a (-a)
  rw [add_neg_cancel, AddCircle.toCircle_zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-- The family `e` is multiplicative in the frequency: it is a homomorphism `ℤ[1/6] → C(Σ₆, ℂ)ˣ`. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem e_add (r s : Z16) : e (r + s) = e r * e s := by
  ext x
  rw [ContinuousMap.mul_apply, e_apply, e_apply, e_apply, χ_add, AddCircle.toCircle_add,
    Circle.coe_mul]

@[category API, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem e_zero : e 0 = 1 := by
  ext x
  rw [e_apply, χ_zero, AddCircle.toCircle_zero, ContinuousMap.one_apply, Circle.coe_one]

/-- The family is self-adjoint: `e_{-r} = conj e_r`. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem e_neg (r : Z16) : e (-r) = star (e r) := by
  ext x
  rw [e_apply, χ_neg, toCircle_neg, Circle.coe_inv_eq_conj, ContinuousMap.star_apply, e_apply]
  simp

/-! ### Stone–Weierstrass -/

/-- The star subalgebra of `C(Σ₆, ℂ)` generated by the characters — the analogue of Mathlib's
`fourierSubalgebra` for `AddCircle`. -/
noncomputable def charSubalgebra : StarSubalgebra ℂ C(S6, ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (Set.range e)
  star_mem' := by
    change Algebra.adjoin ℂ (Set.range e) ≤ star (Algebra.adjoin ℂ (Set.range e))
    refine Algebra.adjoin_le ?_
    rintro - ⟨r, rfl⟩
    exact Algebra.subset_adjoin ⟨-r, e_neg r⟩

/-- The subalgebra generated by the characters is their linear span: the characters are already
closed under multiplication (`e_add`) and contain `1` (`e_zero`). -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem charSubalgebra_coe :
    Subalgebra.toSubmodule charSubalgebra.toSubalgebra = Submodule.span ℂ (Set.range e) := by
  apply Algebra.adjoin_eq_span_of_subset
  refine Set.Subset.trans ?_ Submodule.subset_span
  intro x hx
  refine Submonoid.closure_induction (fun _ => id) ⟨0, ?_⟩ ?_ hx
  · exact e_zero
  · rintro - - - - ⟨m, rfl⟩ ⟨n, rfl⟩
    exact ⟨m + n, e_add m n⟩

/-- **The characters separate points of `Σ₆`** — the Stone–Weierstrass hypothesis. -/
@[category research solved, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem charSubalgebra_separatesPoints : charSubalgebra.SeparatesPoints := by
  intro x y hxy
  obtain ⟨r, hr⟩ := χ_separatesPoints hxy
  refine ⟨_, ⟨e r, Algebra.subset_adjoin ⟨r, rfl⟩, rfl⟩, ?_⟩
  dsimp only
  rw [e_apply, e_apply]
  intro hc
  rw [Subtype.coe_inj] at hc
  exact hr (AddCircle.injective_toCircle one_ne_zero hc)

/-- **Stone–Weierstrass on the solenoid**: the characters generate a dense subalgebra of
`C(Σ₆, ℂ)`. -/
@[category research solved, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem charSubalgebra_closure_eq_top : charSubalgebra.topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints charSubalgebra
    charSubalgebra_separatesPoints

/-- **The linear span of the characters is dense in `C(Σ₆, ℂ)`.**  This is the form the Weyl
dictionary consumes: a statement about all characters upgrades to a statement about all continuous
functions. -/
@[category research solved, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem span_char_closure_eq_top :
    (Submodule.span ℂ (Set.range e)).topologicalClosure = ⊤ := by
  rw [← charSubalgebra_coe]
  exact congr_arg (Subalgebra.toSubmodule <| StarSubalgebra.toSubalgebra ·)
    charSubalgebra_closure_eq_top

@[category research solved, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem dense_span_char :
    Dense ((Submodule.span ℂ (Set.range e) : Submodule ℂ C(S6, ℂ)) : Set C(S6, ℂ)) := by
  rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe, span_char_closure_eq_top]
  simp

/-! ### Orthogonality against Haar measure -/

/-- A non-trivial character takes a value `≠ 1`: it is non-trivial already on the winding line, at
`ξ = 1/(2r)`. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem exists_e_ne_one {r : Z16} (hr : (r : ℚ) ≠ 0) : ∃ a : S6, e r a ≠ 1 := by
  have hr' : ((r : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hr
  refine ⟨wind (1 / (2 * ((r : ℚ) : ℝ))), ?_⟩
  have hval : χ r (wind (1 / (2 * ((r : ℚ) : ℝ)))) = (((1 / 2 : ℝ)) : AddCircle (1 : ℝ)) := by
    rw [χ_wind]
    congr 1
    field_simp
  rw [e_apply, hval]
  intro hc
  have hc' : AddCircle.toCircle (((1 / 2 : ℝ)) : AddCircle (1 : ℝ))
      = AddCircle.toCircle (0 : AddCircle (1 : ℝ)) := by
    rw [AddCircle.toCircle_zero]
    exact Subtype.coe_inj.mp (by rw [hc]; rfl)
  exact coe_ne_zero_of_mem_Ioo (by norm_num) (by norm_num) (by norm_num)
    (AddCircle.injective_toCircle one_ne_zero hc')

@[category API, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem integrable_char (f : C(S6, ℂ)) : Integrable f haar :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- **Orthogonality.**  A non-trivial character integrates to zero against Haar measure: translate
by a point where the character is `≠ 1`.  This is what turns "every Weyl sum vanishes" into
"the empirical measures converge to Haar". -/
@[category research solved, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem integral_e_eq_zero {r : Z16} (hr : (r : ℚ) ≠ 0) : ∫ x, e r x ∂haar = 0 := by
  obtain ⟨a, ha⟩ := exists_e_ne_one hr
  have hmul : ∀ x : S6, e r (a + x) = e r a * e r x := by
    intro x
    rw [e_apply, e_apply, e_apply, map_add, AddCircle.toCircle_add, Circle.coe_mul]
  have hshift : ∫ x, e r (a + x) ∂haar = ∫ x, e r x ∂haar :=
    MeasureTheory.integral_add_left_eq_self (fun x => e r x) a
  simp only [hmul, MeasureTheory.integral_const_mul] at hshift
  have hz : (e r a - 1) * ∫ x, e r x ∂haar = 0 := by
    rw [sub_mul, hshift, one_mul, sub_self]
  rcases mul_eq_zero.mp hz with h | h
  · exact absurd (sub_eq_zero.mp h) ha
  · exact h

/-- The trivial character integrates to `1`. -/
@[category API, AMS 11, ref "A1plus", group "th_solenoid_characters"]
theorem integral_e_zero : ∫ x, e 0 x ∂haar = 1 := by
  simp [e_zero]

end TH.S6
