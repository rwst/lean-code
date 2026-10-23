/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.LineCover
import BB13.Constants
import DiophantineApproximation.SubspaceSystem
import DiophantineApproximation.RationalPlaces
import ArithmeticHeights.Absolute
import ArithmeticHeights.Extension

/-!
# The frame of Problem 10.13 as a normalized system (gate G-2 of plan-beyond-BB13)

The failures `‖(3/2)ⁿ‖ < (3/4)ⁿ` give the frame points `x = (mₙ2ⁿ, 3ⁿ)` (`BB13.frameX`,
`BB13.frameY`). This file shows that, for every `0 < δ ≤ ε* − 1/1000` and every failure `n ≥ 20`,
`x` is a solution of a system in **Evertse's normalization** (2.4), the form in which
Subspace-Theorems' explicit two-variable count
(`NumberField.exists_finset_submodule_of_isNormalizedSystem_two`) takes it. Over `K = E = ℚ`,
`S = {2, 3}`, with constants `1`:

| place | forms | exponents |
|---|---|---|
| `∞` | `X₁ − X₂`, `X₂` | `1 − θ`, `1` |
| `2` | `X₁`, `X₂` | `−θ + η`, `0` |
| `3` | `X₁`, `X₂` | `0`, `−1 + η` |

with `η = (ε* − δ)/2`, so the weight is `1 − 2θ + 2η = −δ` exactly
(`BB13.frameSystem_isNormalized`; `3` distinct forms, coefficients of height `1`, determinant `1`
at every place).

## Why `η > 0`, and why it costs nothing

Under (2.4) the constants are forced to be `1`: the form `X₂` at `∞` with exponent `1` needs
`3ⁿ ≤ C_∞ H(x)`, and `H(x) = 3ⁿ` whenever `mₙ2ⁿ ≤ 3ⁿ`; the forms `X₂` at `2` and `X₁` at `3`
(exponent `0`) need `C₂, C₃ ≥ 1`; and `C_∞ C₂ C₃ ≤ |det|^{1/2} = 1`. But the affine height is
`H(x) = max(mₙ2ⁿ, 3ⁿ)`, which exceeds `3ⁿ` by the factor `1 + 2⁻ⁿ` when `kₙ < 0`, and then the
exact exponents `−θ` at `2` and `−1` at `3` fail. Raising both by `η` absorbs the factor as soon
as `3^{nη} ≥ 1 + 2⁻ⁿ`, which `n ≥ 20` and `η ≥ 1/2000` guarantee (`BB13.one_add_two_pow_le`).
The count moves continuously in `δ`: at `δ = 13/50` it is `3.86·10⁹` instead of `3.78·10⁹`
(gate G-1, `BB13/g1_count.py`).

## Main results

* `BB13.frameSystem_isNormalized`: the system is normalized, with `H = 1`, `D = 1`, `R = 3`.
* `BB13.frame_mem_systemSet`: every failure `n ≥ 20` gives a solution.
* `BB13.thirteen_fiftieths_le`: `δ = 13/50` is admissible.

## References

* J.-H. Evertse, *On the Quantitative Subspace Theorem*, J. Math. Sci. **171** (2010), §2, (2.3)
  and (2.4).
* `plans/plan-beyond-BB13.html`, §3.4, gates G-1 and G-2.
-/

namespace BB13

open NumberField IsDedekindDomain Height Module

/-! ### The places -/

/-- The prime `2`. -/
def prime2 : Nat.Primes := ⟨2, Nat.prime_two⟩

/-- The prime `3`. -/
def prime3 : Nat.Primes := ⟨3, Nat.prime_three⟩

/-- The prime ideal of `𝓞 ℚ` over `2`. -/
noncomputable def v2 : HeightOneSpectrum (𝓞 ℚ) := (Rat.finitePlace prime2).maximalIdeal

/-- The prime ideal of `𝓞 ℚ` over `3`. -/
noncomputable def v3 : HeightOneSpectrum (𝓞 ℚ) := (Rat.finitePlace prime3).maximalIdeal

theorem finitePlace_mk_v2 : FinitePlace.mk v2 = Rat.finitePlace prime2 :=
  FinitePlace.mk_maximalIdeal _

theorem finitePlace_mk_v3 : FinitePlace.mk v3 = Rat.finitePlace prime3 :=
  FinitePlace.mk_maximalIdeal _

theorem v2_ne_v3 : v2 ≠ v3 := by
  intro h
  have h' := congrArg FinitePlace.mk h
  rw [finitePlace_mk_v2, finitePlace_mk_v3] at h'
  have := congrArg Subtype.val (Rat.finitePlace_injective h')
  simp [prime2, prime3] at this

open scoped Classical in
/-- `S = {2, 3}`. -/
noncomputable def frameS : Finset (HeightOneSpectrum (𝓞 ℚ)) := {v2, v3}

/-! ### The forms and the exponents -/

/-- The forms at `∞`: `X₁ − X₂`, `X₂`. -/
noncomputable def formsInf : Fin 2 → Dual ℚ (Fin 2 → ℚ) :=
  ![LinearMap.proj (R := ℚ) (φ := fun _ : Fin 2 ↦ ℚ) 0 - LinearMap.proj 1, LinearMap.proj 1]

/-- The forms at `2` and `3`: the coordinates. -/
noncomputable def formsFin : Fin 2 → Dual ℚ (Fin 2 → ℚ) :=
  ![LinearMap.proj (R := ℚ) (φ := fun _ : Fin 2 ↦ ℚ) 0, LinearMap.proj 1]

open scoped Classical in
/-- The forms of the frame, by absolute value. -/
noncomputable def frameForms (v : AbsoluteValue ℚ ℝ) : Fin 2 → Dual ℚ (Fin 2 → ℚ) :=
  if v = Rat.infinitePlace.1 then formsInf else formsFin

open scoped Classical in
/-- The exponents of the frame, with slack `η` at the primes. -/
noncomputable def frameExp (η : ℝ) : InfinitePlace ℚ ⊕ frameS → Fin 2 → ℝ
  | .inl _ => ![1 - theta, 1]
  | .inr q => if q.1 = v2 then ![-theta + η, 0] else ![0, -1 + η]

/-- The constants of the frame: all `1`. -/
def frameConst : InfinitePlace ℚ ⊕ frameS → ℝ := fun _ ↦ 1

/-- The frame point `(mₙ2ⁿ, 3ⁿ)` as a point of `ℚ²`. -/
noncomputable def framePt (n : ℕ) : Fin 2 → ℚ := ![(frameX n : ℚ), (frameY n : ℚ)]

/-! ### The places of the system, computed -/

theorem infinitePlace_eq (v : InfinitePlace ℚ) : v = Rat.infinitePlace := Subsingleton.elim _ _

theorem frameForms_inl (v : InfinitePlace ℚ) :
    frameForms (systemPlace frameS (.inl v)) = formsInf := by
  simp [frameForms, systemPlace, infinitePlace_eq v]

theorem mem_frameS_iff (q : HeightOneSpectrum (𝓞 ℚ)) : q ∈ frameS ↔ q = v2 ∨ q = v3 := by
  classical
  simp [frameS]

theorem systemPlace_inr_v2 (q : frameS) (hq : q.1 = v2) :
    systemPlace frameS (.inr q) = Rat.AbsoluteValue.padic (prime2 : ℕ) := by
  simp only [systemPlace, hq, finitePlace_mk_v2, Rat.finitePlace_val]

theorem systemPlace_inr_v3 (q : frameS) (hq : q.1 = v3) :
    systemPlace frameS (.inr q) = Rat.AbsoluteValue.padic (prime3 : ℕ) := by
  simp only [systemPlace, hq, finitePlace_mk_v3, Rat.finitePlace_val]

theorem frameForms_padic (p : Nat.Primes) :
    frameForms (Rat.AbsoluteValue.padic (p : ℕ)) = formsFin := by
  rw [frameForms, ite_eq_right_of_eq_false]
  simp only [eq_iff_iff, iff_false]
  exact fun h ↦ Rat.infinitePlace_val_ne_padic p h.symm

theorem frameForms_inr (q : frameS) : frameForms (systemPlace frameS (.inr q)) = formsFin := by
  rcases (mem_frameS_iff q.1).1 q.2 with hq | hq
  · rw [systemPlace_inr_v2 q hq]; exact frameForms_padic prime2
  · rw [systemPlace_inr_v3 q hq]; exact frameForms_padic prime3

theorem systemValue_inl (v : InfinitePlace ℚ) (i : Fin 2) (x : Fin 2 → ℚ) :
    systemValue frameS (fun v ↦ v) frameForms (.inl v) i x = |((formsInf i x : ℚ) : ℝ)| := by
  have hv := infinitePlace_eq v
  subst hv
  rw [systemValue, frameForms_inl, systemAbs, systemMult,
    InfinitePlace.IsReal.mult_eq_one Rat.isReal_infinitePlace, pow_one]
  simp only [systemPlace, Algebra.algebraMap_self, RingHom.id_apply]
  exact (InfinitePlace.coe_apply _ _).trans ((Rat.infinitePlace_apply _ _).trans (by simp))

theorem systemValue_inr_v2 (q : frameS) (hq : q.1 = v2) (i : Fin 2) (x : Fin 2 → ℚ) :
    systemValue frameS (fun v ↦ v) frameForms (.inr q) i x = ((padicNorm 2 (x i) : ℚ) : ℝ) := by
  rw [systemValue, frameForms_inr, systemAbs, systemMult, pow_one, systemPlace_inr_v2 q hq]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, Rat.AbsoluteValue.padic_eq_padicNorm]
  fin_cases i <;> simp [formsFin] <;> rfl

theorem systemValue_inr_v3 (q : frameS) (hq : q.1 = v3) (i : Fin 2) (x : Fin 2 → ℚ) :
    systemValue frameS (fun v ↦ v) frameForms (.inr q) i x = ((padicNorm 3 (x i) : ℚ) : ℝ) := by
  rw [systemValue, frameForms_inr, systemAbs, systemMult, pow_one, systemPlace_inr_v3 q hq]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, Rat.AbsoluteValue.padic_eq_padicNorm]
  fin_cases i <;> simp [formsFin] <;> rfl

/-! ### The normalization (2.4) -/

theorem epsStar_eq_two_theta_sub_one : epsStar = 2 * theta - 1 := by
  linarith [theta_add_theta_add_one]

theorem theta_lt_one : theta < 1 := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h23 : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  have := theta_mul_log_three
  nlinarith

theorem absMulHeight₁_rat (x : ℚ) : absMulHeight₁ x = mulHeight₁ x := by
  have h := absMulHeight₁_pow_finrank x
  rwa [finrank_self, pow_one] at h

theorem det_pi_formsInf : LinearMap.det (LinearMap.pi formsInf) = 1 := by
  rw [← LinearMap.det_toMatrix', Matrix.det_fin_two]
  simp [LinearMap.toMatrix'_apply, formsInf]

theorem det_pi_formsFin : LinearMap.det (LinearMap.pi formsFin) = 1 := by
  rw [← LinearMap.det_toMatrix', Matrix.det_fin_two]
  simp [LinearMap.toMatrix'_apply, formsFin]

theorem frameForms_basis_mem (v : AbsoluteValue ℚ ℝ) (i j : Fin 2) :
    frameForms v i (Pi.basisFun ℚ (Fin 2) j) = 0 ∨ frameForms v i (Pi.basisFun ℚ (Fin 2) j) = 1 ∨
      frameForms v i (Pi.basisFun ℚ (Fin 2) j) = -1 := by
  unfold frameForms
  split_ifs <;> fin_cases i <;> fin_cases j <;> simp [formsInf, formsFin]

open scoped Classical in
/-- **The frame is a normalized system** (Evertse's (2.4)), for every `0 < δ ≤ ε* − 1/1000`, with
slack `η = (ε* − δ)/2` at the primes: coefficients of height `H = 1` and degree `D = 1`, `R = 3`
distinct forms, constants `1`, determinant `1` at every place, weight exactly `−δ`. -/
@[category API, AMS 11, ref "BE08", group "bugeaud_10_13"]
theorem frameSystem_isNormalized {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ epsStar - 1 / 1000) :
    IsNormalizedSystem frameS (fun v ↦ v) frameForms frameConst
      (frameExp ((epsStar - δ) / 2)) 1 1 3 δ where
  height_le p i j := by
    rcases frameForms_basis_mem (systemPlace frameS p) i j with h | h | h <;>
      rw [h, absMulHeight₁_rat] <;> simp [mulHeight₁_neg]
  degree_le p i j := (minpoly.natDegree_le _).trans_eq (finrank_self ℚ)
  ncard_le := by
    have hsub : (Set.range fun q : (InfinitePlace ℚ ⊕ frameS) × Fin 2 ↦
        frameForms (systemPlace frameS q.1) q.2) ⊆ {formsInf 0, formsInf 1, formsFin 0} := by
      rintro _ ⟨⟨p, i⟩, rfl⟩
      rcases p with v | q
      · show frameForms (systemPlace frameS (.inl v)) i ∈ _
        rw [frameForms_inl]; fin_cases i <;> simp
      · show frameForms (systemPlace frameS (.inr q)) i ∈ _
        rw [frameForms_inr]
        fin_cases i
        · simp
        · simp [formsInf, formsFin]
    refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
    refine (Set.ncard_insert_le _ _).trans ?_
    have := Set.ncard_insert_le (formsInf 1) {formsFin 0}
    rw [Set.ncard_singleton] at this
    omega
  const_pos _ := one_pos
  const_le := by
    have hdet : systemDet frameS (fun v ↦ v) frameForms = 1 := by
      refine Finset.prod_eq_one fun p _ ↦ ?_
      rcases p with v | q
      · rw [systemAbs, frameForms_inl, det_pi_formsInf]; simp
      · rw [systemAbs, frameForms_inr, det_pi_formsFin]; simp
    rw [hdet, Real.one_rpow, systemConst]
    simp [frameConst]
  delta_pos := hδ0
  delta_le_one := by
    have h1 : epsStar < 1 := by rw [epsStar_eq_two_theta_sub_one]; linarith [theta_lt_one]
    linarith
  weight_le := by
    have hpair : ∑ q : frameS, ∑ i, frameExp ((epsStar - δ) / 2) (.inr q) i
        = ∑ q ∈ frameS, ∑ i : Fin 2,
          (if q = v2 then ![-theta + (epsStar - δ) / 2, 0] else ![0, -1 + (epsStar - δ) / 2]) i :=
      Finset.sum_coe_sort frameS fun q ↦ ∑ i : Fin 2,
        (if q = v2 then ![-theta + (epsStar - δ) / 2, 0] else ![0, -1 + (epsStar - δ) / 2]) i
    rw [systemWeight, Fintype.sum_sum_type, hpair]
    unfold frameS
    rw [Finset.sum_pair v2_ne_v3, Fintype.sum_unique]
    simp only [frameExp, Fin.sum_univ_two, v2_ne_v3.symm, ite_true, ite_false]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [epsStar_eq_two_theta_sub_one]
    linarith
  exponent_le p i := by
    have hη : (epsStar - δ) / 2 ≤ theta - 1 / 2 := by
      rw [epsStar_eq_two_theta_sub_one]; linarith
    have hθ := theta_pos
    rcases p with v | q
    · simp only [systemExponent, InfinitePlace.IsReal.mult_eq_one
        (infinitePlace_eq v ▸ Rat.isReal_infinitePlace), finrank_self]
      fin_cases i <;> simp [frameExp]
      linarith
    · simp only [systemExponent, frameExp]
      split_ifs <;> fin_cases i <;> simp <;> linarith [theta_lt_one]
  exists_exponent_eq p := by
    rcases p with v | q
    · refine ⟨1, ?_⟩
      simp [systemExponent, frameExp]
    · simp only [systemExponent, frameExp]
      split_ifs
      · exact ⟨1, by simp⟩
      · exact ⟨0, by simp⟩

/-! ### Membership: the height of a frame point -/

/-- The frame point with the affine coordinate `1`, as integers. -/
noncomputable def frameInt (n : ℕ) : Option (Fin 2) → ℤ := fun o ↦ o.elim 1 ![frameX n, frameY n]

theorem frameInt_cast (n : ℕ) :
    (fun o : Option (Fin 2) ↦ o.elim 1 (framePt n)) = ((↑) : ℤ → ℚ) ∘ frameInt n := by
  funext o
  rcases o with _ | i
  · simp [frameInt]
  · fin_cases i <;> simp [frameInt, framePt]

theorem frameInt_gcd (n : ℕ) : Finset.univ.gcd (frameInt n) = 1 := by
  have hdvd : Finset.univ.gcd (frameInt n) ∣ 1 := Finset.gcd_dvd (Finset.mem_univ none)
  have hnn : 0 ≤ Finset.univ.gcd (frameInt n) := by
    rw [← Finset.normalize_gcd, ← Int.abs_eq_normalize]; exact abs_nonneg _
  exact Int.eq_one_of_dvd_one hnn hdvd

/-- The affine height of the frame point is the largest of `1`, `|mₙ2ⁿ|` and `3ⁿ`. -/
theorem mulHeightAff_framePt (n : ℕ) :
    mulHeightAff (framePt n) = ((⨆ o, |frameInt n o| : ℤ) : ℝ) := by
  rw [mulHeightAff, frameInt_cast, Rat.mulHeight_eq_max_abs_of_gcd_eq_one (frameInt_gcd n)]

theorem pow_le_mulHeightAff_framePt (n : ℕ) : (3 : ℝ) ^ n ≤ mulHeightAff (framePt n) := by
  rw [mulHeightAff_framePt]
  have h : |frameInt n (some 1)| ≤ ⨆ o, |frameInt n o| :=
    le_ciSup (f := fun o ↦ |frameInt n o|) (Finite.bddAbove_range _) (some (1 : Fin 2))
  have h3 : |frameInt n (some 1)| = 3 ^ n := by simp [frameInt, frameY]
  rw [h3] at h
  exact_mod_cast h

theorem mulHeightAff_framePt_le {n : ℕ} (hnf : IsFailure 3 2 (3 / 4) n) :
    mulHeightAff (framePt n) ≤ (3 : ℝ) ^ n * (1 + (1 / 2 : ℝ) ^ n) := by
  rw [mulHeightAff_framePt]
  have hX : |((frameX n : ℤ) : ℝ)| ≤ (3 : ℝ) ^ n * (1 + (1 / 2 : ℝ) ^ n) := by
    have hres : ((frameX n : ℤ) : ℝ) = (3 : ℝ) ^ n - ((resid 3 2 n : ℤ) : ℝ) := by
      rw [frameX_cast, resid]; push_cast; ring
    have hk := abs_resid_lt_of_isFailure hnf
    have hp : (3 : ℝ) ^ n * (1 + (1 / 2 : ℝ) ^ n) = (3 : ℝ) ^ n + (3 / 2 : ℝ) ^ n := by
      rw [mul_add, ← mul_pow]; norm_num
    rw [hres, hp]
    have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ n := by positivity
    calc |(3 : ℝ) ^ n - ((resid 3 2 n : ℤ) : ℝ)| ≤ |(3 : ℝ) ^ n| + |((resid 3 2 n : ℤ) : ℝ)| :=
          abs_sub _ _
      _ ≤ _ := by rw [abs_of_nonneg h3]; linarith
  have h1 : (1 : ℝ) ≤ (3 : ℝ) ^ n * (1 + (1 / 2 : ℝ) ^ n) := by
    have : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
    have : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
    nlinarith
  have hsup : ((⨆ o, |frameInt n o| : ℤ) : ℝ) = ⨆ o, ((|frameInt n o| : ℤ) : ℝ) :=
    Monotone.map_ciSup_of_continuousAt (f := ((↑) : ℤ → ℝ)) continuous_of_discreteTopology.continuousAt
      Int.cast_mono (Finite.bddAbove_range _)
  rw [hsup]
  refine ciSup_le fun o ↦ ?_
  rcases o with _ | i
  · simpa [frameInt] using h1
  · fin_cases i
    · simpa [frameInt] using hX
    · simp [frameInt, frameY]

/-! ### Membership: the slack `η` absorbs the excess of the height -/

/-- **`1 + 2⁻ⁿ ≤ 3^{nη}`** for `n ≥ 20` and `η ≥ 1/2000`: the excess `H(x)/3ⁿ ≤ 1 + 2⁻ⁿ` of the
affine height is paid for by the slack. -/
@[category API, AMS 11, ref "BE08", group "bugeaud_10_13"]
theorem one_add_two_pow_le {n : ℕ} (hn : 20 ≤ n) {η : ℝ} (hη : 1 / 2000 ≤ η) :
    1 + (1 / 2 : ℝ) ^ n ≤ ((3 : ℝ) ^ n) ^ η := by
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  rw [Real.rpow_def_of_pos h3, Real.log_pow]
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := by linarith [log_three_ge]
  have hn' : (20 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (1 / 100 : ℝ) ≤ n * Real.log 3 * η := by
    have : (20 : ℝ) * 1 ≤ n * Real.log 3 := mul_le_mul hn' hlog3 zero_le_one (by positivity)
    nlinarith
  have h2 : (1 / 2 : ℝ) ^ n ≤ 1 / 100 := by
    calc (1 / 2 : ℝ) ^ n ≤ (1 / 2) ^ 20 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
      _ ≤ 1 / 100 := by norm_num
  linarith [Real.add_one_le_exp (n * Real.log 3 * η)]

/-- With `3ⁿ ≤ H ≤ 3ⁿ (1 + 2⁻ⁿ)`, every power `H^a` with `0 ≤ a ≤ 1` is at most `(3ⁿ)^{a+η}`. -/
theorem rpow_le_of_height {n : ℕ} (hn : 20 ≤ n) {η : ℝ} (hη : 1 / 2000 ≤ η) {H a : ℝ}
    (hH0 : (3 : ℝ) ^ n ≤ H) (hH1 : H ≤ (3 : ℝ) ^ n * (1 + (1 / 2 : ℝ) ^ n)) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) : H ^ a ≤ ((3 : ℝ) ^ n) ^ (a + η) := by
  have h3 : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
  have hH : H ≤ ((3 : ℝ) ^ n) ^ (1 + η) := by
    rw [Real.rpow_add (by linarith), Real.rpow_one]
    exact hH1.trans (mul_le_mul_of_nonneg_left (one_add_two_pow_le hn hη) (by linarith))
  calc H ^ a ≤ (((3 : ℝ) ^ n) ^ (1 + η)) ^ a := Real.rpow_le_rpow (by linarith) hH ha0
    _ = ((3 : ℝ) ^ n) ^ ((1 + η) * a) := by rw [← Real.rpow_mul (by linarith)]
    _ ≤ ((3 : ℝ) ^ n) ^ (a + η) :=
        Real.rpow_le_rpow_of_exponent_le h3 (by nlinarith)

/-! ### Membership -/

/-- **Every failure `n ≥ 20` is a solution of the frame system**, for every
`0 < δ ≤ ε* − 1/1000`: its frame point `(mₙ2ⁿ, 3ⁿ)` has integer coordinates and meets the six
inequalities with constants `1`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem frame_mem_systemSet {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ epsStar - 1 / 1000) {n : ℕ}
    (hn : 20 ≤ n) (hnf : IsFailure 3 2 (3 / 4) n) :
    framePt n ∈ systemSet frameS (fun v ↦ v) frameForms frameConst
      (frameExp ((epsStar - δ) / 2)) := by
  classical
  set η := (epsStar - δ) / 2 with hηdef
  set H := mulHeightAff (framePt n) with hHdef
  have hη : 1 / 2000 ≤ η := by rw [hηdef]; linarith
  have hηθ : η ≤ theta - 1 / 2 := by rw [hηdef, epsStar_eq_two_theta_sub_one]; linarith
  have hθ1 := theta_lt_one
  have hH0 := pow_le_mulHeightAff_framePt n
  have hH1 := mulHeightAff_framePt_le hnf
  have h3pos : (0 : ℝ) < 3 ^ n := by positivity
  have hHpos : 0 < H := lt_of_lt_of_le h3pos hH0
  refine ⟨fun j ↦ ?_, fun p i ↦ ?_⟩
  · fin_cases j
    · simp [framePt]
    · simp [framePt]
  rw [frameConst, one_mul]
  rcases p with v | q
  · rw [systemValue_inl]
    fin_cases i
    · -- `|mₙ2ⁿ − 3ⁿ| = |kₙ| < (3/2)ⁿ = (3ⁿ)^{1−θ} ≤ H^{1−θ}`
      have hval : ((formsInf 0 (framePt n) : ℚ) : ℝ) = -((resid 3 2 n : ℤ) : ℝ) := by
        simp [formsInf, framePt, frameX, frameY, resid]
      have hpow : ((3 : ℝ) ^ n) ^ (1 - theta) = (3 / 2 : ℝ) ^ n := by
        have hθpow : ((3 : ℝ) ^ n) ^ theta = 2 ^ n := by
          have h := rpow_neg_theta n
          rw [Real.rpow_neg h3pos.le, one_div, inv_pow] at h
          exact inv_injective h
        rw [Real.rpow_sub h3pos, Real.rpow_one, hθpow, div_pow]
      show |((formsInf 0 (framePt n) : ℚ) : ℝ)| ≤ H ^ (1 - theta)
      rw [hval, abs_neg]
      refine (abs_resid_lt_of_isFailure hnf).le.trans ?_
      rw [← hpow]
      exact Real.rpow_le_rpow h3pos.le hH0 (by linarith)
    · show |((formsInf 1 (framePt n) : ℚ) : ℝ)| ≤ H ^ (1 : ℝ)
      have h1 : ((formsInf 1 (framePt n) : ℚ) : ℝ) = 3 ^ n := by
        simp [formsInf, framePt, frameY]
      rw [Real.rpow_one, h1, abs_of_pos h3pos]
      exact hH0
  · rcases (mem_frameS_iff q.1).1 q.2 with hq | hq
    · rw [systemValue_inr_v2 q hq]
      fin_cases i
      · -- `|mₙ2ⁿ|₂ ≤ 2⁻ⁿ = (3ⁿ)^{−θ} ≤ H^{−θ+η}`
        have h2 := frame_two_adic n
        rw [frameY_cast] at h2
        show ((padicNorm 2 (framePt n 0) : ℚ) : ℝ) ≤
          H ^ (if q.1 = v2 then ![-theta + η, 0] else ![0, -1 + η]) 0
        simp only [hq, ↓reduceIte]
        show _ ≤ H ^ (-theta + η)
        refine (by simpa [framePt] using h2 : _ ≤ ((3 : ℝ) ^ n) ^ (-theta)).trans ?_
        have hle := rpow_le_of_height hn hη hH0 hH1 (a := theta - η) (by linarith) (by linarith)
        rw [sub_add_cancel] at hle
        rw [show -theta + η = -(theta - η) by ring, Real.rpow_neg hHpos.le, Real.rpow_neg h3pos.le]
        exact inv_anti₀ (Real.rpow_pos_of_pos hHpos _) hle
      · show ((padicNorm 2 (framePt n 1) : ℚ) : ℝ) ≤
          H ^ (if q.1 = v2 then ![-theta + η, 0] else ![0, -1 + η]) 1
        simp only [hq, ↓reduceIte]
        show _ ≤ H ^ (0 : ℝ)
        rw [Real.rpow_zero]
        simpa [framePt, frameY] using (by exact_mod_cast padicNorm.of_int (p := 2) (3 ^ n) :
          ((padicNorm 2 ((3 ^ n : ℤ) : ℚ) : ℚ) : ℝ) ≤ 1)
    · have hq2 : q.1 ≠ v2 := hq ▸ v2_ne_v3.symm
      rw [systemValue_inr_v3 q hq]
      fin_cases i
      · show ((padicNorm 3 (framePt n 0) : ℚ) : ℝ) ≤
          H ^ (if q.1 = v2 then ![-theta + η, 0] else ![0, -1 + η]) 0
        simp only [hq2, ↓reduceIte]
        show _ ≤ H ^ (0 : ℝ)
        rw [Real.rpow_zero]
        simpa [framePt] using (by exact_mod_cast padicNorm.of_int (p := 3) (frameX n) :
          ((padicNorm 3 ((frameX n : ℤ) : ℚ) : ℚ) : ℝ) ≤ 1)
      · -- `|3ⁿ|₃ = 3⁻ⁿ = (3ⁿ)^{−1} ≤ H^{−1+η}`
        show ((padicNorm 3 (framePt n 1) : ℚ) : ℝ) ≤
          H ^ (if q.1 = v2 then ![-theta + η, 0] else ![0, -1 + η]) 1
        simp only [hq2, ↓reduceIte]
        show _ ≤ H ^ (-1 + η)
        have hle := rpow_le_of_height hn hη hH0 hH1 (a := 1 - η) (by linarith) (by linarith)
        rw [sub_add_cancel, Real.rpow_one] at hle
        have hv : ((padicNorm 3 (framePt n 1) : ℚ) : ℝ) = ((3 : ℝ) ^ n)⁻¹ := by
          simp [framePt, frameY]
          have h33 : padicValRat 3 (3 : ℚ) = 1 := by
            simpa using padicValRat.self (p := 3) (by norm_num)
          rw [h33]
          simp
        rw [hv, show -1 + η = -(1 - η) by ring, Real.rpow_neg hHpos.le]
        exact inv_anti₀ (Real.rpow_pos_of_pos hHpos _) hle

/-- **`δ = 13/50` is admissible**: `13/50 ≤ ε* − 1/1000`, i.e. `0.261 log 3 ≤ log(4/3)`. At this `δ`
the two-variable count is `3.86·10⁹` (gate G-1). -/
@[category API, AMS 11, ref "BE08", group "bugeaud_10_13"]
theorem thirteen_fiftieths_le : (13 / 50 : ℝ) ≤ epsStar - 1 / 1000 := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hkey : (13 / 50 + 1 / 1000 : ℝ) * Real.log 3 ≤ Real.log (4 / 3) := by
    nlinarith [log_four_thirds_ge, log_three_le]
  have : (13 / 50 + 1 / 1000 : ℝ) ≤ epsStar := by
    rw [epsStar, le_div_iff₀ h3]; exact hkey
  linarith

end BB13
