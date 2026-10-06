/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import ForMathlib.NumberTheory.Solenoid.Haar

@[expose] public section

/-!
# The characters of the `S`-adic solenoid, and the natural-extension projection

The dual of `Σ_S = (ℝ × ∏_{p ∈ S} ℚ_p) / ℤ[1/N_S]` is the discrete group `ℤ[1/N_S]`: for
`r ∈ ℤ[1/N_S]`,

`χ_r [x, (y_p)] = r x - ∑_{p ∈ S} {r y_p}_p ∈ ℝ/ℤ`,

where `{·}_p = Padic.fracPart p` is the canonical character of `ℚ_p` with kernel `ℤ_p`.

* **Well-definedness** is partial fractions without Bézout
  (`Rat.exists_sub_sum_principalPart_eq_intCast`): for `s ∈ ℤ[1/N_S]`,
  `s - ∑_{p ∈ S} {s}_p = 0` in `ℝ/ℤ` (`charRat_eq_zero`).
* **On the winding line the finite places are invisible**: `χ_r (wind ξ) = [r ξ]` (`χ_wind`).
* **Frequency collapse**: `χ_r ∘ σ_u = χ_{u r}` exactly (`χ_smulAut`).
* **Separation**: the `χ_r` separate points (`exists_χ_ne_zero`): on the fundamental-domain
  representative, `r = 1` catches the real coordinate and `r = p⁻ᵏ` the `p`-adic one, which is
  invisible at every other prime of `S`.
* **The dual is `ℤ[1/N_S]`**: `r ↦ χ_r` is injective (`χ_injective`), and the span of the
  `e r = exp(2πi χ_r)` is dense in `C(Σ_S, ℂ)` (Stone–Weierstrass, `dense_span_char`).
* **Orthogonality**: `∫ e r d(haar S) = 0` for `r ≠ 0` (`integral_e_eq_zero`).

The **natural-extension projection** is `proj = χ_1 : Σ_S → ℝ/ℤ`: `proj (wind ξ) = ξ mod 1`,
`proj ∘ σ_b = b · proj` for an integer `b` supported on `S` (`proj_smulAut_natCast`), and
`proj_* haar = volume` on `ℝ/ℤ` (`map_proj_haar`).  So for integer `b` the solenoid is the natural
extension of `×b` on the circle; for a non-integer unit such as `3/2` the projection does not
intertwine (`χ_1 ∘ σ_{3/2} = χ_{3/2}`).

## Main declarations

* `Solenoid.charRat`, `charRat_eq_zero`; `Solenoid.charAmbient`, `charAmbient_eq_zero_of_mem_lattice`.
* `Solenoid.χ`, `χ_mk`, `χ_add`, `χ_neg`, `χ_nsmul`, `continuous_χ`, `χ_wind`.
* `Solenoid.smulFreq`, `χ_smulAut`, `χ_smulAut_iter`.
* `Solenoid.exists_χ_ne_zero`, `χ_separatesPoints`, `χ_injective`.
* `Solenoid.e`, `charSubalgebra`, `charSubalgebra_closure_eq_top`, `dense_span_char`.
* `Solenoid.integral_e_eq_zero`.
* `Solenoid.proj`, `proj_wind`, `proj_surjective`, `proj_smulAut_natCast`, `map_proj_haar`.

## Implementation notes

For `S = {2, 3}` this specialises `TH/Solenoid/Characters.lean`, where well-definedness used a
two-prime Bézout identity.  The `PontryaginDual` packaging of `χ_injective` + density is left out.

## Status

Everything in this file is standard; the contribution is the formalisation.

## References

* M. Einsiedler and T. Ward, *Ergodic Theory with a view towards Number Theory*, Springer (2011),
  Chapter 8.
* K. Schmidt, *Dynamical Systems of Algebraic Origin*, Birkhäuser (1995).
* D. Ramakrishnan and R. Valenza, *Fourier Analysis on Number Fields*, GTM 186, Springer (1999),
  Ch. 3–5 (local additive characters).
-/

namespace Solenoid

open Metric Set MeasureTheory Rat
open scoped ENNReal

variable {S : Finset Nat.Primes}

/-! ### The character attached to a rational -/

variable (S) in
/-- The value `t - ∑_{p ∈ S} {t}_p ∈ ℝ/ℤ` attached to a rational `t`.  It vanishes on
`ℤ[1/N_S]` (`charRat_eq_zero`). -/
noncomputable def charRat (t : ℚ) : AddCircle (1 : ℝ) :=
  ((t : ℝ) : AddCircle (1 : ℝ)) - ∑ p : S, Padic.fracPart _ (t : ℚ_[((p : Nat.Primes) : ℕ)])

/-- **Partial fractions in `ℝ/ℤ`.**  For `t ∈ ℤ[1/N_S]`, `t = ∑_{p ∈ S} {t}_p` modulo `ℤ`. -/
theorem charRat_eq_zero {t : ℚ} (ht : t ∈ sIntegers S) : charRat S t = 0 := by
  obtain ⟨n, hn⟩ := exists_sub_sum_principalPart_eq_intCast ht
  have hsum : ∑ p : S, Padic.fracPart _ (t : ℚ_[((p : Nat.Primes) : ℕ)]) =
      ((((∑ p ∈ S, Padic.principalPart (p : ℕ) (t : ℚ_[(p : ℕ)]) : ℚ)) : ℝ) :
        AddCircle (1 : ℝ)) := by
    rw [Finset.sum_coe_sort S (fun p : Nat.Primes ↦ Padic.fracPart (p : ℕ) (t : ℚ_[(p : ℕ)])),
      Rat.cast_sum]
    exact (map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) _ S).symm
  rw [charRat, hsum, Padic.coe_eq_coe_of_sub_int hn, sub_self]

/-! ### The character of the ambient group attached to a frequency -/

/-- The character of `G_S` at frequency `r ∈ ℚ`: `(x, (y_p)) ↦ r x - ∑_{p ∈ S} {r y_p}_p`. -/
noncomputable def charAmbient (r : ℚ) : ambient S →+ AddCircle (1 : ℝ) where
  toFun g := (((r : ℝ) * g.1 : ℝ) : AddCircle (1 : ℝ)) -
    ∑ p : S, Padic.fracPart _ ((r : ℚ_[((p : Nat.Primes) : ℕ)]) * g.2 p)
  map_zero' := by simp [Padic.fracPart_zero]
  map_add' g h := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, Padic.fracPart_add,
      Finset.sum_add_distrib, AddCircle.coe_add]
    abel

theorem charAmbient_apply (r : ℚ) (g : ambient S) :
    charAmbient r g = (((r : ℝ) * g.1 : ℝ) : AddCircle (1 : ℝ)) -
      ∑ p : S, Padic.fracPart _ ((r : ℚ_[((p : Nat.Primes) : ℕ)]) * g.2 p) := rfl

/-- The frequency enters additively. -/
theorem charAmbient_add_left (r s : ℚ) (g : ambient S) :
    charAmbient (r + s) g = charAmbient r g + charAmbient s g := by
  simp only [charAmbient_apply, Rat.cast_add, add_mul, Padic.fracPart_add,
    Finset.sum_add_distrib, AddCircle.coe_add]
  abel

theorem charAmbient_zero_left (g : ambient S) : charAmbient 0 g = 0 := by
  simp [charAmbient_apply, Padic.fracPart_zero]

/-- On the diagonal the character only sees the product of the two frequencies. -/
theorem charAmbient_diag (r s : ℚ) : charAmbient r (diag S s) = charRat S (r * s) := by
  simp only [charAmbient_apply, diag_fst, diag_snd, charRat]
  push_cast
  rfl

/-- **The character kills the lattice.** -/
theorem charAmbient_eq_zero_of_mem_lattice {r : ℚ} (hr : r ∈ sIntegers S) {g : ambient S}
    (hg : g ∈ lattice S) : charAmbient r g = 0 := by
  obtain ⟨s, hs, rfl⟩ := mem_lattice.mp hg
  rw [charAmbient_diag]
  exact charRat_eq_zero (mul_mem hr hs)

theorem continuous_charAmbient (r : ℚ) : Continuous (charAmbient (S := S) r) := by
  have h1 : Continuous fun g : ambient S ↦ (((r : ℝ) * g.1 : ℝ) : AddCircle (1 : ℝ)) :=
    QuotientAddGroup.continuous_mk.comp (continuous_const.mul continuous_fst)
  have h2 : Continuous fun g : ambient S ↦
      ∑ p : S, Padic.fracPart _ ((r : ℚ_[((p : Nat.Primes) : ℕ)]) * g.2 p) :=
    continuous_finsetSum _ fun p _ ↦ Padic.continuous_fracPart.comp (by fun_prop)
  exact h1.sub h2

/-! ### The characters of `Σ_S` -/

/-- **The character of `Σ_S` at frequency `r ∈ ℤ[1/N_S]`**:
`χ_r [x, (y_p)] = r x - ∑_{p ∈ S} {r y_p}_p`. -/
noncomputable def χ (r : sIntegers S) : Solenoid S →+ AddCircle (1 : ℝ) :=
  QuotientAddGroup.lift (lattice S) (charAmbient (r : ℚ)) fun _ hx ↦
    charAmbient_eq_zero_of_mem_lattice r.2 hx

theorem χ_mk (r : sIntegers S) (g : ambient S) :
    χ r (QuotientAddGroup.mk g) = charAmbient (r : ℚ) g := rfl

theorem χ_add (r s : sIntegers S) (x : Solenoid S) : χ (r + s) x = χ r x + χ s x := by
  obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective x
  exact charAmbient_add_left _ _ g

theorem χ_zero (x : Solenoid S) : χ 0 x = 0 := by
  obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective x
  exact charAmbient_zero_left g

theorem χ_neg (r : sIntegers S) (x : Solenoid S) : χ (-r) x = -χ r x := by
  have h := χ_add r (-r) x
  rw [add_neg_cancel, χ_zero] at h
  linear_combination (norm := abel) -h

theorem χ_sub (r s : sIntegers S) (x : Solenoid S) : χ (r - s) x = χ r x - χ s x := by
  rw [sub_eq_add_neg, χ_add, χ_neg, sub_eq_add_neg]

theorem χ_nsmul (n : ℕ) (r : sIntegers S) (x : Solenoid S) : χ (n • r) x = n • χ r x := by
  induction n with
  | zero => simp [χ_zero]
  | succ n ih => rw [succ_nsmul, χ_add, ih, succ_nsmul]

theorem continuous_χ (r : sIntegers S) : Continuous (χ r) := by
  rw [(QuotientAddGroup.isQuotientMap_mk (lattice S)).continuous_iff]
  exact continuous_charAmbient (r : ℚ)

/-! ### The winding line and the frequency collapse -/

/-- **On the winding line the finite places are invisible**: `χ_r (wind ξ) = [r ξ]`. -/
theorem χ_wind (r : sIntegers S) (ξ : ℝ) :
    χ r (wind ξ) = ((((r : ℚ) : ℝ) * ξ : ℝ) : AddCircle (1 : ℝ)) := by
  rw [wind, χ_mk, charAmbient_apply]
  simp [Padic.fracPart_zero]

variable {u : ℚ}

/-- The frequency `u r`, the image of `r` under the dual of `σ_u`. -/
def smulFreq (hu : IsSUnit S u) (r : sIntegers S) : sIntegers S :=
  ⟨u * r, mul_mem hu.mem r.2⟩

theorem smulFreq_coe (hu : IsSUnit S u) (r : sIntegers S) :
    ((smulFreq hu r : sIntegers S) : ℚ) = u * r := rfl

/-- **The frequency collapse**, exactly: `χ_r ∘ σ_u = χ_{u r}`. -/
theorem χ_smulAut (hu : IsSUnit S u) (r : sIntegers S) (x : Solenoid S) :
    χ r (smulAut hu x) = χ (smulFreq hu r) x := by
  obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [smulAut_mk, χ_mk, χ_mk, charAmbient_apply, charAmbient_apply, smulFreq_coe]
  simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, Rat.smul_def, Rat.cast_mul, mul_assoc,
    mul_left_comm (u : ℝ), mul_left_comm (u : ℚ_[_])]

/-- The iterated collapse: the frequency of `χ_r ∘ σ_uⁿ` is `uⁿ r`. -/
theorem χ_smulAut_iter (hu : IsSUnit S u) (r : sIntegers S) (n : ℕ) (x : Solenoid S) :
    χ r ((smulAut hu)^[n] x) = χ ((smulFreq hu)^[n] r) x := by
  induction n generalizing r with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', χ_smulAut, ih, Function.iterate_succ_apply]

/-! ### The characters separate points -/

/-- The frequency `p⁻ᵏ ∈ ℤ[1/N_S]`, which detects the `p`-adic coordinate at level `k`. -/
noncomputable def invPow (p : S) (k : ℕ) : sIntegers S :=
  ⟨1 / (((p : Nat.Primes) : ℕ) : ℚ) ^ k, by simpa using div_pow_mem_sIntegers p.2 1 k⟩

theorem invPow_coe (p : S) (k : ℕ) :
    ((invPow p k : sIntegers S) : ℚ) = 1 / (((p : Nat.Primes) : ℕ) : ℚ) ^ k := rfl

/-- `p⁻ᵏ` is a `q`-adic integer for every other prime `q`. -/
theorem norm_invPow_le_one {p q : Nat.Primes} (h : p ≠ q) (k : ℕ) :
    ‖(((1 : ℚ) / ((p : ℕ) : ℚ) ^ k : ℚ) : ℚ_[(q : ℕ)])‖ ≤ 1 := by
  rw [Padic.eq_padicNorm]
  have := padicNorm.intCast_div_pow_le_one_of_not_dvd (p := (q : ℕ)) (q := (p : ℕ))
    (fun hd ↦ h (Subtype.ext ((Nat.prime_dvd_prime_iff_eq q.2 p.2).mp hd).symm)) 1 k
  push_cast at this
  exact_mod_cast this

private theorem coe_ne_zero_of_mem_Ico {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) (ht : t ≠ 0) :
    ((t : ℝ) : AddCircle (1 : ℝ)) ≠ 0 := by
  intro hcon
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hcon
  rw [zsmul_eq_mul, mul_one] at hn
  have hn0 : n = 0 := by
    have h1' : (n : ℝ) < 1 := hn ▸ h1
    have h0' : (0 : ℝ) ≤ n := hn ▸ h0
    have : (0 : ℤ) ≤ n := by exact_mod_cast h0'
    have : n < 1 := by exact_mod_cast h1'
    omega
  rw [hn0] at hn
  exact ht (by simpa using hn.symm)

/-- **The characters separate the origin.**  On the fundamental-domain representative `(t, (y_p))`
of `x ≠ 0`: if `t ≠ 0`, `r = 1` detects it (every `p`-adic coordinate is invisible); otherwise
some `y_p ≠ 0`, and `r = p⁻ᵏ` with `pᵏ ‖y_p‖ > 1` pushes `y_p` out of `ℤ_p` while leaving every
other coordinate integral. -/
theorem exists_χ_ne_zero {x : Solenoid S} (hx : x ≠ 0) : ∃ r : sIntegers S, χ r x ≠ 0 := by
  obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨d, ⟨hdD, hd⟩, -⟩ := exists_unique_fundamental g
  have hmk : (QuotientAddGroup.mk g : Solenoid S) = QuotientAddGroup.mk d := by
    rw [QuotientAddGroup.eq, neg_add_eq_sub]
    simpa [neg_sub] using neg_mem hd
  rw [hmk] at hx ⊢
  rw [mem_D] at hdD
  obtain ⟨⟨ht0, ht1⟩, hy⟩ := hdD
  by_cases ht : d.1 = 0
  · have hex : ∃ p, d.2 p ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hx (by rw [show d = 0 from Prod.ext ht (funext hall)]; exact QuotientAddGroup.mk_zero _)
    obtain ⟨p, hp0⟩ := hex
    have hpos : 0 < ‖d.2 p‖ := norm_pos_iff.mpr hp0
    have hp1 : (1 : ℝ) < ((p : Nat.Primes) : ℕ) := by exact_mod_cast (p : Nat.Primes).2.one_lt
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / ‖d.2 p‖) hp1
    rw [div_lt_iff₀ hpos] at hk
    have hgt : 1 < ‖(((1 : ℚ) / (((p : Nat.Primes) : ℕ) : ℚ) ^ k : ℚ) :
        ℚ_[((p : Nat.Primes) : ℕ)]) * d.2 p‖ := by
      rw [norm_mul, Padic.norm_ratCast_inv_pow]
      linarith
    refine ⟨invPow p k, ?_⟩
    have hval : χ (invPow p k) (QuotientAddGroup.mk d) = -Padic.fracPart _
        ((((1 : ℚ) / (((p : Nat.Primes) : ℕ) : ℚ) ^ k : ℚ) : ℚ_[((p : Nat.Primes) : ℕ)]) *
          d.2 p) := by
      rw [χ_mk, charAmbient_apply, invPow_coe, ht, mul_zero, AddCircle.coe_zero, zero_sub,
        Finset.sum_eq_single p (fun q _ hqp ↦ Padic.fracPart_of_norm_le_one (by
          rw [norm_mul]
          exact mul_le_one₀ (norm_invPow_le_one (fun h ↦ hqp (Subtype.ext h).symm) k)
            (norm_nonneg _) (hy q))) (by simp)]
    rw [hval, neg_ne_zero]
    exact fun hcon ↦ absurd (Padic.fracPart_eq_zero_iff.mp hcon) (not_le.mpr hgt)
  · refine ⟨1, ?_⟩
    have hval : χ (1 : sIntegers S) (QuotientAddGroup.mk d) = ((d.1 : ℝ) : AddCircle (1 : ℝ)) := by
      rw [χ_mk, charAmbient_apply]
      simp only [OneMemClass.coe_one, Rat.cast_one, one_mul]
      rw [Finset.sum_eq_zero fun p _ ↦ Padic.fracPart_of_norm_le_one (hy p), sub_zero]
    rw [hval]
    exact coe_ne_zero_of_mem_Ico ht0 ht1 ht

/-- **The characters separate points.** -/
theorem χ_separatesPoints {x y : Solenoid S} (hxy : x ≠ y) :
    ∃ r : sIntegers S, χ r x ≠ χ r y := by
  obtain ⟨r, hr⟩ := exists_χ_ne_zero (sub_ne_zero.mpr hxy)
  exact ⟨r, fun hcon ↦ hr (by rw [map_sub, hcon, sub_self])⟩

/-- A nonzero frequency gives a nontrivial character: on the winding line at `ξ = 1/(2r)` it
takes the value `1/2`. -/
theorem χ_wind_half {r : sIntegers S} (hr : (r : ℚ) ≠ 0) :
    χ r (wind (1 / (2 * ((r : ℚ) : ℝ)))) = ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) := by
  have hr' : ((r : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hr
  rw [χ_wind]
  congr 1
  field_simp

private theorem half_ne_zero : ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) ≠ 0 :=
  coe_ne_zero_of_mem_Ico (by norm_num) (by norm_num) (by norm_num)

/-- **The dual of `Σ_S` is `ℤ[1/N_S]`**: distinct frequencies give distinct characters. -/
theorem χ_injective : Function.Injective (χ (S := S)) := by
  intro r s h
  by_contra hrs
  have hne : ((r - s : sIntegers S) : ℚ) ≠ 0 := fun h0 ↦ hrs (sub_eq_zero.mp (Subtype.ext h0))
  have := χ_wind_half hne
  rw [χ_sub, h, sub_self] at this
  exact half_ne_zero this.symm

/-! ### The characters as continuous complex functions -/

/-- `χ_r` as a continuous function `Σ_S → ℂ` of modulus one: `e r x = exp(2πi χ_r x)`. -/
noncomputable def e (r : sIntegers S) : C(Solenoid S, ℂ) :=
  (fourier (T := (1 : ℝ)) 1).comp ⟨χ r, continuous_χ r⟩

theorem e_apply (r : sIntegers S) (x : Solenoid S) :
    e r x = (AddCircle.toCircle (χ r x) : ℂ) := fourier_one

theorem toCircle_neg (a : AddCircle (1 : ℝ)) :
    AddCircle.toCircle (-a) = (AddCircle.toCircle a)⁻¹ := by
  have h := AddCircle.toCircle_add a (-a)
  rw [add_neg_cancel, AddCircle.toCircle_zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem e_add (r s : sIntegers S) : e (r + s) = e r * e s := by
  ext x
  rw [ContinuousMap.mul_apply, e_apply, e_apply, e_apply, χ_add, AddCircle.toCircle_add,
    Circle.coe_mul]

theorem e_zero : e (0 : sIntegers S) = 1 := by
  ext x
  rw [e_apply, χ_zero, AddCircle.toCircle_zero, ContinuousMap.one_apply, Circle.coe_one]

theorem e_neg (r : sIntegers S) : e (-r) = star (e r) := by
  ext x
  rw [e_apply, χ_neg, toCircle_neg, Circle.coe_inv_eq_conj, ContinuousMap.star_apply, e_apply]
  simp

/-! ### Stone–Weierstrass -/

variable (S) in
/-- The star subalgebra of `C(Σ_S, ℂ)` generated by the characters. -/
noncomputable def charSubalgebra : StarSubalgebra ℂ C(Solenoid S, ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (Set.range e)
  star_mem' := by
    change Algebra.adjoin ℂ (Set.range e) ≤ star (Algebra.adjoin ℂ (Set.range e))
    refine Algebra.adjoin_le ?_
    rintro - ⟨r, rfl⟩
    exact Algebra.subset_adjoin ⟨-r, e_neg r⟩

/-- The subalgebra generated by the characters is their linear span. -/
theorem charSubalgebra_coe :
    Subalgebra.toSubmodule (charSubalgebra S).toSubalgebra = Submodule.span ℂ (Set.range e) := by
  apply Algebra.adjoin_eq_span_of_subset
  refine Set.Subset.trans ?_ Submodule.subset_span
  intro x hx
  refine Submonoid.closure_induction (fun _ ↦ id) ⟨0, e_zero⟩ ?_ hx
  rintro - - - - ⟨m, rfl⟩ ⟨n, rfl⟩
  exact ⟨m + n, e_add m n⟩

theorem charSubalgebra_separatesPoints : (charSubalgebra S).SeparatesPoints := by
  intro x y hxy
  obtain ⟨r, hr⟩ := χ_separatesPoints hxy
  refine ⟨_, ⟨e r, Algebra.subset_adjoin ⟨r, rfl⟩, rfl⟩, ?_⟩
  dsimp only
  rw [e_apply, e_apply]
  intro hc
  rw [Circle.coe_inj] at hc
  exact hr (AddCircle.injective_toCircle one_ne_zero hc)

/-- **Stone–Weierstrass on the solenoid.** -/
theorem charSubalgebra_closure_eq_top : (charSubalgebra S).topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
    charSubalgebra_separatesPoints

theorem span_char_closure_eq_top :
    (Submodule.span ℂ (Set.range (e (S := S)))).topologicalClosure = ⊤ := by
  rw [← charSubalgebra_coe]
  exact congr_arg (Subalgebra.toSubmodule <| StarSubalgebra.toSubalgebra ·)
    charSubalgebra_closure_eq_top

/-- **The linear span of the characters is dense in `C(Σ_S, ℂ)`.** -/
theorem dense_span_char :
    Dense ((Submodule.span ℂ (Set.range (e (S := S))) : Submodule ℂ C(Solenoid S, ℂ)) :
      Set C(Solenoid S, ℂ)) := by
  rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe, span_char_closure_eq_top]
  simp

/-! ### Orthogonality against Haar measure -/

theorem exists_e_ne_one {r : sIntegers S} (hr : (r : ℚ) ≠ 0) : ∃ a : Solenoid S, e r a ≠ 1 := by
  refine ⟨wind (1 / (2 * ((r : ℚ) : ℝ))), ?_⟩
  rw [e_apply, χ_wind_half hr]
  intro hc
  have hc' : AddCircle.toCircle ((1 / 2 : ℝ) : AddCircle (1 : ℝ))
      = AddCircle.toCircle (0 : AddCircle (1 : ℝ)) := by
    rw [AddCircle.toCircle_zero]
    exact Subtype.coe_inj.mp (by rw [hc]; rfl)
  exact half_ne_zero (AddCircle.injective_toCircle one_ne_zero hc')

theorem integrable_char (f : C(Solenoid S, ℂ)) : Integrable f (haar S) :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- **Orthogonality.**  A nontrivial character integrates to zero against Haar measure. -/
theorem integral_e_eq_zero {r : sIntegers S} (hr : (r : ℚ) ≠ 0) : ∫ x, e r x ∂haar S = 0 := by
  obtain ⟨a, ha⟩ := exists_e_ne_one hr
  have hmul : ∀ x : Solenoid S, e r (a + x) = e r a * e r x := fun x ↦ by
    rw [e_apply, e_apply, e_apply, map_add, AddCircle.toCircle_add, Circle.coe_mul]
  have hshift : ∫ x, e r (a + x) ∂haar S = ∫ x, e r x ∂haar S :=
    integral_add_left_eq_self (fun x ↦ e r x) a
  simp only [hmul, integral_const_mul] at hshift
  have hz : (e r a - 1) * ∫ x, e r x ∂haar S = 0 := by
    rw [sub_mul, hshift, one_mul, sub_self]
  rcases mul_eq_zero.mp hz with h | h
  · exact absurd (sub_eq_zero.mp h) ha
  · exact h

theorem integral_e_zero : ∫ x, e (0 : sIntegers S) x ∂haar S = 1 := by
  simp [e_zero]

/-! ### The natural-extension projection -/

variable (S) in
/-- The projection `Σ_S → ℝ/ℤ`, `[x, (y_p)] ↦ x - ∑_{p ∈ S} {y_p}_p`: the character `χ_1`. -/
noncomputable def proj : Solenoid S →+ AddCircle (1 : ℝ) := χ 1

theorem continuous_proj : Continuous (proj S) := continuous_χ 1

/-- `proj (wind ξ) = ξ mod 1`. -/
theorem proj_wind (ξ : ℝ) : proj S (wind ξ) = (ξ : AddCircle (1 : ℝ)) := by
  rw [proj, χ_wind]
  simp

theorem proj_surjective : Function.Surjective (proj S) := by
  intro y
  obtain ⟨ξ, rfl⟩ := QuotientAddGroup.mk_surjective y
  exact ⟨wind ξ, proj_wind ξ⟩

/-- **`σ_b` is the natural extension of `×b`**: for an integer `b` which is an `S`-unit,
`proj ∘ σ_b = b · proj`. -/
theorem proj_smulAut_natCast {b : ℕ} (hb : IsSUnit S (b : ℚ)) (x : Solenoid S) :
    proj S (smulAut hb x) = b • proj S x := by
  rw [proj, χ_smulAut, ← χ_nsmul]
  congr 1

/-- **The projection carries Haar measure to Lebesgue measure on `ℝ/ℤ`.** -/
theorem map_proj_haar : Measure.map (proj S) (haar S) = volume := by
  have : (Measure.map (proj S) (haar S)).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map (haar S) (proj S) continuous_proj proj_surjective
      (by rw [Filter.cocompact_eq_bot]; exact Filter.tendsto_bot)
  have h1 : Measure.map (proj S) (haar S) univ = 1 := by
    rw [Measure.map_apply continuous_proj.measurable MeasurableSet.univ, preimage_univ,
      measure_univ]
  rw [← (Measure.addHaarMeasure_eq_iff ⊤ (Measure.map (proj S) (haar S))).mpr h1,
    (Measure.addHaarMeasure_eq_iff ⊤ volume).mpr UnitAddCircle.measure_univ]

end Solenoid

/-! ### Examples -/

section Examples

open Solenoid Rat

/-- On `Σ_{2,3}`, `σ₆` is the natural extension of `×6` on the circle. -/
example (x : Solenoid (Nat.primesOf 6)) :
    proj _ (smulAut (isSUnit_natCast (b := 6) (by norm_num) le_rfl) x) = 6 • proj _ x :=
  proj_smulAut_natCast _ x

/-- ... while `σ_{3/2}` does not intertwine `proj`: `proj ∘ σ_{3/2} = χ_{3/2}`. -/
example (h : IsSUnit (Nat.primesOf 6) (3 / 2)) (x : Solenoid (Nat.primesOf 6)) :
    proj _ (smulAut h x) = χ ⟨3 / 2, by simpa using h.mem⟩ x := by
  rw [proj, χ_smulAut]
  exact congrArg (fun r ↦ χ r x) (Subtype.ext (by rw [smulFreq_coe]; simp))

end Examples
