/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BL.ConjugacyMap
import ForMathlib.NumberTheory.PadicIntHaar
import ForMathlib.Dynamics.Bernoulli
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.Probability.ProductMeasure
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Bernstein–Lagarias — the 2-adic shift `S` is Bernoulli (BL96, §1; PROVED)

Daniel J. Bernstein and Jeffrey C. Lagarias, *The 3x+1 conjugacy map*, Canadian Journal of
Mathematics **48** (1996), no. 6, 1154–1169.

This file **discharges the cited axiom `BL.S_bernoulli`**: the 2-adic shift `S` (digit drop) is the
one-sided Bernoulli `(½,½)` shift, i.e. `MeasureTheory.IsBernoulli S μ` for any 2-adic Haar
probability measure `μ`.

## The argument

The **binary digit map** `e x = (n ↦ toZMod (Sⁿ x))` is a measurable equivalence
`ℤ₂ ≃ᵐ (ℕ → ZMod 2)`. It trivially intertwines `S` with the coordinate shift `seqShift`
(`e (S x) n = toZMod (Sⁿ⁺¹ x) = e x (n+1)`), and it carries Haar to the i.i.d. uniform product
measure `Measure.infinitePi (fun _ => uniform)`. The latter is the substance: by the projective-limit
characterisation of `infinitePi`, it suffices that for each initial segment the joint law of the first
`n` digits is uniform on `(ZMod 2)ⁿ`, and this is the general fact
`PadicInt.measure_toZModPow_fiber` (every `toZModPow n` fiber has Haar measure `2⁻ⁿ`), transported
across the binary digit/residue bijection `toZModPow_eq_iff_parity`.

The general (non-2-adic) inputs live in `ForMathlib`: `PadicInt.measure_toZModPow_fiber` and the
Bernoulli machinery `MeasureTheory.{seqShift, IsBernoulli}`.

## References
* [BL96] Bernstein, Daniel J., and Jeffrey C. Lagarias. *The 3x+1 conjugacy map.* Canadian Journal
  of Mathematics 48 (1996), no. 6, 1154–1169.
* [Kin09] Kingsbery, James, et al. *Dynamics of the `p`-adic shift and applications.* arXiv:0903.4226.
-/

namespace BL

open PadicInt MeasureTheory Filter Topology
open scoped ENNReal

/-! ### The binary digit/residue bijection `ℤ₂ → ZMod (2ⁿ)`

The standard binary expansion via the shift: `toZModPow n x = ∑_{i<n} parity (Sⁱ x) · 2ⁱ`. -/

/-- Summability of the binary digit series (extracted from `tsum_parity_S`). -/
private theorem summable_parity_S (y : ℤ_[2]) :
    Summable (fun i : ℕ => (parity (S^[i] y) : ℤ_[2]) * 2 ^ i) := by
  have h2lt : ‖(2 : ℤ_[2])‖ < 1 := by
    rw [PadicInt.norm_lt_one_iff_dvd]; exact_mod_cast dvd_refl (2 : ℤ_[2])
  have hbound : ∀ i, ‖(parity (S^[i] y) : ℤ_[2]) * 2 ^ i‖ ≤ ‖(2 : ℤ_[2])‖ ^ i := by
    intro i
    have h1 : ‖(parity (S^[i] y) : ℤ_[2]) * 2 ^ i‖
        ≤ ‖((parity (S^[i] y) : ℕ) : ℤ_[2])‖ * ‖(2 : ℤ_[2]) ^ i‖ := norm_mul_le _ _
    rw [norm_pow] at h1
    exact h1.trans (mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) i) (PadicInt.norm_le_one _))
  exact Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg _) h2lt) hbound

/-- **One-step solenoidality of `S`.** `2^{k+1} ∣ (x − y) ⟹ 2^k ∣ (S x − S y)`. The parities agree
(mod `2`), so `2·(S x − S y) = (x − y)`; divide one factor of `2`. -/
private theorem S_dvd_sub_of_dvd_succ {k : ℕ} {x y : ℤ_[2]}
    (h : (2 : ℤ_[2]) ^ (k + 1) ∣ (x - y)) : (2 : ℤ_[2]) ^ k ∣ (S x - S y) := by
  have h2 : (2 : ℤ_[2]) ∣ (x - y) := (dvd_pow_self (2 : ℤ_[2]) (Nat.succ_ne_zero k)).trans h
  have hpar : parity x = parity y := parity_eq_of_two_dvd_sub h2
  have hnum : (2 : ℤ_[2]) * (S x - S y) = x - y := by
    rw [mul_sub, two_mul_S, two_mul_S, hpar]; ring
  have hd : (2 : ℤ_[2]) ^ (k + 1) ∣ (2 * (S x - S y)) := by rw [hnum]; exact h
  rw [pow_succ'] at hd
  exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ_[2]) ≠ 0)).mp hd

/-- **Iterated solenoidality of `S`.** `2^n ∣ (x − y)` makes the first `n` digits agree:
`parity (Sⁱ x) = parity (Sⁱ y)` for `i < n`. -/
private theorem parity_S_iterate_congr {n : ℕ} {x y : ℤ_[2]} (h : (2 : ℤ_[2]) ^ n ∣ (x - y))
    (i : ℕ) (hi : i < n) : parity (S^[i] x) = parity (S^[i] y) := by
  have key : ∀ j, j ≤ n → (2 : ℤ_[2]) ^ (n - j) ∣ (S^[j] x - S^[j] y) := by
    intro j
    induction j with
    | zero => intro _; simpa using h
    | succ j ih =>
      intro hj
      have hd := ih (by omega)
      rw [show n - j = (n - (j + 1)) + 1 from by omega] at hd
      have hstep := S_dvd_sub_of_dvd_succ hd
      rwa [← Function.iterate_succ_apply' S j x, ← Function.iterate_succ_apply' S j y] at hstep
  have hik := key i (le_of_lt hi)
  have h2 : (2 : ℤ_[2]) ∣ (S^[i] x - S^[i] y) :=
    (dvd_pow_self (2 : ℤ_[2]) (by omega : n - i ≠ 0)).trans hik
  exact parity_eq_of_two_dvd_sub h2

/-- `x` agrees with its degree-`< n` binary partial sum mod `2ⁿ`. -/
private theorem S_partialSum_dvd (n : ℕ) (x : ℤ_[2]) :
    (2 : ℤ_[2]) ^ n ∣ (x - ∑ i ∈ Finset.range n, (parity (S^[i] x) : ℤ_[2]) * 2 ^ i) := by
  have hg : Summable (fun i => (parity (S^[i + n] x) : ℤ_[2]) * 2 ^ i) := by
    simpa [Function.iterate_add_apply] using summable_parity_S (S^[n] x)
  have htail : ∑' i, (parity (S^[i + n] x) : ℤ_[2]) * 2 ^ (i + n)
             = 2 ^ n * ∑' i, (parity (S^[i + n] x) : ℤ_[2]) * 2 ^ i := by
    rw [← hg.tsum_mul_left]
    apply tsum_congr; intro i; rw [pow_add]; ring
  have key : x = (∑ i ∈ Finset.range n, (parity (S^[i] x) : ℤ_[2]) * 2 ^ i)
      + 2 ^ n * ∑' i, (parity (S^[i + n] x) : ℤ_[2]) * 2 ^ i := by
    rw [← htail, (summable_parity_S x).sum_add_tsum_nat_add n]; exact (tsum_parity_S x).symm
  nth_rewrite 1 [key]
  rw [add_sub_cancel_left]
  exact dvd_mul_right _ _

/-- **The binary level map.** `toZModPow n x = ∑_{i<n} parity (Sⁱ x) · 2ⁱ` in `ZMod (2ⁿ)`. -/
private theorem toZModPow_digit_sum_S (n : ℕ) (x : ℤ_[2]) :
    PadicInt.toZModPow n x
      = ∑ i ∈ Finset.range n, (parity (S^[i] x) : ZMod (2 ^ n)) * 2 ^ i := by
  have hd := S_partialSum_dvd n x
  rw [← toZModPow_eq_iff_dvd_sub] at hd
  rw [hd, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h2 : PadicInt.toZModPow n (2 : ℤ_[2]) = 2 := by
    have e : (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) := by norm_num
    rw [e, map_natCast]; norm_num
  rw [map_mul, map_pow, map_natCast, h2]

/-- **Binary digit/residue bijection.** Two `2`-adic integers have the same residue mod `2ⁿ` iff their
first `n` binary digits agree. -/
private theorem toZModPow_eq_iff_parity (n : ℕ) (x y : ℤ_[2]) :
    PadicInt.toZModPow n x = PadicInt.toZModPow n y
      ↔ ∀ i, i < n → parity (S^[i] x) = parity (S^[i] y) := by
  constructor
  · intro h i hi
    rw [toZModPow_eq_iff_dvd_sub] at h
    exact parity_S_iterate_congr h i hi
  · intro h
    rw [toZModPow_digit_sum_S, toZModPow_digit_sum_S]
    exact Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.mp hi)]


/-! ### The uniform measure on `ZMod 2` -/

/-- The uniform `(½,½)` probability measure on `ZMod 2`: half the counting measure. -/
private noncomputable def uZMod2 : Measure (ZMod 2) := (2⁻¹ : ℝ≥0∞) • Measure.count

private theorem uZMod2_apply (a : ZMod 2) : uZMod2 {a} = 2⁻¹ := by
  rw [uZMod2, Measure.smul_apply, Measure.count_singleton, smul_eq_mul, mul_one]

private instance : IsProbabilityMeasure uZMod2 := by
  constructor
  rw [uZMod2, Measure.smul_apply, smul_eq_mul]
  rw [show Measure.count (Set.univ : Set (ZMod 2)) = 2 by
    rw [Measure.count_apply_finite _ Set.finite_univ]; simp]
  rw [ENNReal.inv_mul_cancel] <;> norm_num

/-! ### The binary digit map and its inverse (purely algebraic) -/

/-- `‖(2 : ℤ_[2])‖ = 2⁻¹`. -/
private theorem norm_two : ‖(2 : ℤ_[2])‖ = 2⁻¹ := by
  have e : (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) := by norm_num
  rw [e, PadicInt.norm_p]; norm_num

/-- The **binary digit map** `dig x n = toZMod (Sⁿ x)`. -/
private noncomputable def dig (x : ℤ_[2]) : ℕ → ZMod 2 := fun n => PadicInt.toZMod (S^[n] x)

/-- `dig` intertwines `S` with the coordinate shift `seqShift`. -/
private theorem dig_semiconj : Function.Semiconj dig S seqShift := by
  intro x; funext n
  simp only [dig, seqShift, Function.iterate_succ_apply]

/-- The reconstruction map: a digit sequence `↦` the `2`-adic integer with those binary digits. -/
private noncomputable def recd (d : ℕ → ZMod 2) : ℤ_[2] := ∑' i, ((d i).val : ℤ_[2]) * 2 ^ i

private theorem summable_recd (d : ℕ → ZMod 2) :
    Summable (fun i : ℕ => ((d i).val : ℤ_[2]) * 2 ^ i) := by
  have h2lt : ‖(2 : ℤ_[2])‖ < 1 := by
    rw [PadicInt.norm_lt_one_iff_dvd]; exact_mod_cast dvd_refl (2 : ℤ_[2])
  have hbound : ∀ i, ‖((d i).val : ℤ_[2]) * 2 ^ i‖ ≤ ‖(2 : ℤ_[2])‖ ^ i := by
    intro i
    have h1 : ‖((d i).val : ℤ_[2]) * 2 ^ i‖ ≤ ‖((d i).val : ℤ_[2])‖ * ‖(2 : ℤ_[2]) ^ i‖ :=
      norm_mul_le _ _
    rw [norm_pow] at h1
    exact h1.trans (mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) i) (PadicInt.norm_le_one _))
  exact Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg _) h2lt) hbound

private theorem recd_dig (x : ℤ_[2]) : recd (dig x) = x := tsum_parity_S x

private theorem seqShift_iterate_apply (n : ℕ) :
    ∀ (d : ℕ → ZMod 2) (j : ℕ), seqShift^[n] d j = d (j + n) := by
  induction n with
  | zero => intro d j; simp
  | succ k ih =>
    intro d j
    rw [Function.iterate_succ_apply, ih (seqShift d) j]
    rfl

private theorem recd_peel (d : ℕ → ZMod 2) :
    recd d = ((d 0).val : ℤ_[2]) + 2 * recd (seqShift d) := by
  rw [recd, (summable_recd d).tsum_eq_zero_add]
  congr 1
  · simp
  · rw [recd, ← (summable_recd (seqShift d)).tsum_mul_left]
    apply tsum_congr; intro i
    simp only [seqShift]; rw [pow_succ]; ring

private theorem parity_recd (d : ℕ → ZMod 2) : parity (recd d) = (d 0).val := by
  have h2 : (2 : ℤ_[2]) ∣ (recd d - ((d 0).val : ℤ_[2])) := ⟨recd (seqShift d), by rw [recd_peel]; ring⟩
  rw [parity_eq_of_two_dvd_sub h2, parity_natCast, CC.X_eq_mod]
  exact Nat.mod_eq_of_lt (ZMod.val_lt (d 0))

private theorem S_recd (d : ℕ → ZMod 2) : S (recd d) = recd (seqShift d) := by
  have h := two_mul_S (recd d)
  rw [parity_recd] at h
  rw [show recd d - ((d 0).val : ℤ_[2]) = 2 * recd (seqShift d) by rw [recd_peel]; ring] at h
  exact mul_left_cancel₀ (by norm_num : (2 : ℤ_[2]) ≠ 0) h

private theorem S_iterate_recd (d : ℕ → ZMod 2) (n : ℕ) :
    S^[n] (recd d) = recd (seqShift^[n] d) := by
  induction n generalizing d with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, S_recd, ih (seqShift d), ← Function.iterate_succ_apply]

private theorem dig_recd (d : ℕ → ZMod 2) : dig (recd d) = d := by
  funext n
  have hval : (dig (recd d) n).val = (d n).val := by
    show (PadicInt.toZMod (S^[n] (recd d))).val = (d n).val
    rw [S_iterate_recd]
    show parity (recd (seqShift^[n] d)) = (d n).val
    rw [parity_recd, seqShift_iterate_apply n d 0, Nat.zero_add]
  exact ZMod.val_injective 2 hval

private theorem dig_bijective : Function.Bijective dig :=
  Function.bijective_iff_has_inverse.mpr ⟨recd, recd_dig, dig_recd⟩

/-- A `2`-adic integer realizing a prescribed length-`(N+1)` digit pattern. -/
private noncomputable def cylRealizer (N : ℕ) (d : (i : Finset.Iic N) → ZMod 2) : ℤ_[2] :=
  recd (fun n => if h : n ≤ N then d ⟨n, Finset.mem_Iic.mpr h⟩ else 0)

private theorem dig_cylRealizer (N : ℕ) (d : (i : Finset.Iic N) → ZMod 2) (i : Finset.Iic N) :
    dig (cylRealizer N d) ↑i = d i := by
  rw [cylRealizer, dig_recd, dif_pos (Finset.mem_Iic.mp i.2)]

/-! ### Measurability (needs the Borel structure) -/

variable [MeasurableSpace ℤ_[2]] [BorelSpace ℤ_[2]]

/-- The shift `S` is `2`-Lipschitz, hence continuous and measurable. -/
private theorem measurable_S : Measurable S := by
  have hlip : LipschitzWith 2 S := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    rw [dist_eq_norm, dist_eq_norm]
    by_cases hp : parity x = parity y
    · have hkey : (2 : ℤ_[2]) * (S x - S y) = x - y := by
        rw [mul_sub, two_mul_S, two_mul_S, hp]; ring
      have hnn : ‖x - y‖ = 2⁻¹ * ‖S x - S y‖ := by rw [← hkey, norm_mul, norm_two]
      rw [hnn]; push_cast; nlinarith [norm_nonneg (S x - S y)]
    · have hnd : ¬ (2 : ℤ_[2]) ∣ (x - y) := fun hdvd => hp (parity_eq_of_two_dvd_sub hdvd)
      have hge : ¬ ‖x - y‖ < 1 := fun hlt => hnd ((PadicInt.norm_lt_one_iff_dvd _).mp hlt)
      have hxy1 : ‖x - y‖ = 1 := le_antisymm (PadicInt.norm_le_one _) (not_lt.mp hge)
      have hsle : ‖S x - S y‖ ≤ 1 := PadicInt.norm_le_one _
      rw [hxy1]; push_cast; linarith
  exact hlip.continuous.measurable

/-- `toZMod : ℤ_[2] → ZMod 2` is measurable (its fibers are clopen). -/
private theorem measurable_toZMod : Measurable (PadicInt.toZMod : ℤ_[2] → ZMod 2) := by
  apply measurable_to_countable'
  intro a
  obtain ⟨r, hr⟩ := ZMod.ringHom_surjective PadicInt.toZMod a
  have hset : (PadicInt.toZMod (p := 2)) ⁻¹' {a}
      = (fun x => -r + x) ⁻¹' ((PadicInt.toZMod (p := 2)) ⁻¹' {0}) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, map_add, map_neg, hr]
    rw [neg_add_eq_zero, eq_comm]
  have h0 : (PadicInt.toZMod (p := 2)) ⁻¹' {0} = {x : ℤ_[2] | ‖x‖ < 1} := by
    ext x
    rw [Set.mem_preimage, Set.mem_singleton_iff, ← RingHom.mem_ker, ker_toZMod,
      PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton, Set.mem_setOf_eq,
      ← PadicInt.norm_lt_one_iff_dvd]
  rw [hset]
  exact (measurable_const_add (-r)) (by rw [h0]; exact (isOpen_lt continuous_norm
    continuous_const).measurableSet)

private theorem measurable_dig : Measurable dig :=
  measurable_pi_iff.mpr fun n => measurable_toZMod.comp (measurable_S.iterate n)

private theorem measurable_recd : Measurable recd := by
  have hmeas : ∀ N, Measurable
      (fun d : ℕ → ZMod 2 => ∑ i ∈ Finset.range N, ((d i).val : ℤ_[2]) * 2 ^ i) := by
    intro N
    refine Finset.measurable_sum _ fun i _ => ?_
    fun_prop
  have hlim : Tendsto (fun N (d : ℕ → ZMod 2) => ∑ i ∈ Finset.range N, ((d i).val : ℤ_[2]) * 2 ^ i)
      atTop (𝓝 recd) := tendsto_pi_nhds.mpr fun d => (summable_recd d).hasSum.tendsto_sum_nat
  exact measurable_of_tendsto_metrizable hmeas hlim

/-! ### The measurable equivalence, pushforward, and the result -/

/-- The binary digit map as a measurable equivalence `ℤ₂ ≃ᵐ (ℕ → ZMod 2)`. -/
private noncomputable def digEquiv : ℤ_[2] ≃ᵐ (ℕ → ZMod 2) where
  toEquiv := Equiv.ofBijective dig dig_bijective
  measurable_toFun := measurable_dig
  measurable_invFun := by
    have heq : ⇑(Equiv.ofBijective dig dig_bijective).symm = recd := by
      funext d
      have h1 : dig ((Equiv.ofBijective dig dig_bijective).symm d) = d :=
        (Equiv.ofBijective dig dig_bijective).apply_symm_apply d
      exact dig_bijective.injective (h1.trans (dig_recd d).symm)
    rw [heq]; exact measurable_recd

/-- The joint law of the first `N+1` digits under Haar is uniform on `(ZMod 2)^{Iic N}`. -/
private theorem map_proj_dig (μ : Measure ℤ_[2]) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (N : ℕ) :
    μ.map (fun x => (Finset.Iic N).restrict (dig x)) = Measure.pi (fun _ : Finset.Iic N => uZMod2) := by
  have hproj : Measurable (fun x => (Finset.Iic N).restrict (dig x)) :=
    (Finset.measurable_restrict _).comp measurable_dig
  apply Measure.ext_of_singleton
  intro d
  rw [Measure.map_apply hproj (MeasurableSet.singleton d)]
  -- RHS singleton
  have hRHS : Measure.pi (fun _ : Finset.Iic N => uZMod2) {d} = (2⁻¹ : ℝ≥0∞) ^ (N + 1) := by
    rw [show ({d} : Set ((i : Finset.Iic N) → ZMod 2)) = Set.univ.pi (fun i => {d i}) by
      ext y; simp [funext_iff]]
    rw [Measure.pi_pi]
    simp only [uZMod2_apply]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe, Nat.card_Iic]
  rw [hRHS]
  -- LHS = a toZModPow fiber
  have hset : (fun x => (Finset.Iic N).restrict (dig x)) ⁻¹' {d}
      = (PadicInt.toZModPow (N + 1)) ⁻¹' {PadicInt.toZModPow (N + 1) (cylRealizer N d)} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [toZModPow_eq_iff_parity]
    constructor
    · intro hx j hj
      have hi : j ∈ Finset.Iic N := Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp hj)
      have e1 : dig x j = d ⟨j, hi⟩ := congrFun hx ⟨j, hi⟩
      have e2 : dig (cylRealizer N d) j = d ⟨j, hi⟩ := dig_cylRealizer N d ⟨j, hi⟩
      have hz : PadicInt.toZMod (S^[j] x) = PadicInt.toZMod (S^[j] (cylRealizer N d)) := by
        rw [show PadicInt.toZMod (S^[j] x) = dig x j from rfl,
            show PadicInt.toZMod (S^[j] (cylRealizer N d)) = dig (cylRealizer N d) j from rfl,
            e1, e2]
      unfold parity; rw [hz]
    · intro hx
      funext i
      have hj : (↑i : ℕ) < N + 1 := Nat.lt_succ_iff.mpr (Finset.mem_Iic.mp i.2)
      have hz : PadicInt.toZMod (S^[(↑i : ℕ)] x) = PadicInt.toZMod (S^[(↑i : ℕ)] (cylRealizer N d)) :=
        ZMod.val_injective 2 (hx ↑i hj)
      show dig x ↑i = d i
      rw [show dig x ↑i = PadicInt.toZMod (S^[(↑i : ℕ)] x) from rfl, hz,
          show PadicInt.toZMod (S^[(↑i : ℕ)] (cylRealizer N d)) = dig (cylRealizer N d) ↑i from rfl,
          dig_cylRealizer N d i]
  rw [hset, PadicInt.measure_toZModPow_fiber μ (N + 1), ENNReal.inv_pow]
  norm_num

/-- The digit map carries Haar to the i.i.d. uniform product measure. -/
private theorem map_dig (μ : Measure ℤ_[2]) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ] :
    μ.map dig = Measure.infinitePi (fun _ : ℕ => uZMod2) := by
  haveI : IsProbabilityMeasure (μ.map dig) :=
    Measure.isProbabilityMeasure_map measurable_dig.aemeasurable
  refine ext_of_generate_finite _ generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders ?_ (by rw [measure_univ, measure_univ])
  intro s hs
  rw [measurableCylinders_nat] at hs
  simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hs
  obtain ⟨N, S, hS, rfl⟩ := hs
  have hcyl : (Measure.infinitePi (fun _ : ℕ => uZMod2)) (cylinder (Finset.Iic N) S)
      = (Measure.pi (fun _ : Finset.Iic N => uZMod2)) S := by
    have h1 : (Measure.infinitePi (fun _ : ℕ => uZMod2)).map (Finset.Iic N).restrict
        = Measure.pi (fun _ : Finset.Iic N => uZMod2) :=
      Measure.infinitePi_map_restrict (fun _ : ℕ => uZMod2)
    rw [← h1, Measure.map_apply (Finset.measurable_restrict (Finset.Iic N)) hS]
    rfl
  rw [Measure.map_apply measurable_dig (MeasurableSet.cylinder _ hS),
    show dig ⁻¹' cylinder (Finset.Iic N) S = (fun x => (Finset.Iic N).restrict (dig x)) ⁻¹' S from rfl,
    ← Measure.map_apply (f := fun x => (Finset.Iic N).restrict (dig x))
      ((Finset.measurable_restrict _).comp measurable_dig) hS, map_proj_dig μ N, hcyl]

/-- **(Kingsbery et al. 2009; PROVED.)** The 2-adic shift `S` is a Bernoulli system: the binary-digit
map carries Haar to the i.i.d. uniform `(½,½)` product measure and intertwines `S` with the shift. -/
@[category research solved, AMS 37 28, ref "Kin09", group "bl_conjugacy"]
theorem S_bernoulli (μ : Measure ℤ_[2]) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ] :
    IsBernoulli S μ :=
  ⟨ZMod 2, inferInstance, uZMod2, inferInstance, digEquiv,
    ⟨digEquiv.measurable, by rw [show ⇑digEquiv = dig from rfl]; exact map_dig μ⟩, dig_semiconj⟩

end BL
