/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Data.Set.Finite.Basic
import CITED.CorvajaZannier
import CITED.CorvajaZannierAlgebraic
import CITED.SubspaceTheorem
import CorvajaZannier2004.MainTheorem
import ArithmeticHeights.Absolute
import ArithmeticHeights.Extension
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The Corvaja–Zannier Main Theorem at `Γ = ⟨2, 3⟩`, from the Subspace-Theorems library

[CZ04]'s Main Theorem in the specialization this corpus uses — `u = 2ˣ3ʸ`, `q ∈ ℕ`, multiplier
`δ` rational (`CZ.pseudoPisot_approx_of_subspace`) or real algebraic (`CZ.pseudoPisot_approx_alg`)
— and the toolkit around it.  Footprint `std3`.

**History.**  Both statements were cited axioms until 2026-07-14 (`δ ∈ ℚ`) and 2026-08-07
(`δ` algebraic), then theorems of a 1800-line derivation through Ridout's theorem
(`Ridout.finite_ratios`, `Ridout.finite_ratios_alg`) resting on the cited axioms
`Subspace.evertseSchlickewei` and `Subspace.schmidt1D'`.  Since 2026-10-12 both are corollaries
of the Subspace-Theorems library's `finite_setOf_not_isPseudoPisot` (`CorvajaZannier2004/`), the
Main Theorem for every finitely generated `Γ ≤ ℝˣ` of algebraic numbers, and the Ridout chain is
gone.

**The specialization.**  `Γ = ⟨2, 3⟩` is finitely generated and rational
(`gamma23_fg`, `gamma23_isAlgebraic`); `(q, x, y) ↦ (q, 2ˣ3ʸ)` is injective
(`unit23_injective`, via the `2`- and `3`-adic absolute values); `u = 2ˣ3ʸ` has degree
`[ℚ(u) : ℚ] = 1` (`finrank_adjoin_ratCast`) and absolute height `H(u) ≤ height23 x y`
(`absMulHeight₁_unit23_le`), so the library's `H(u)^{-ε} |q|^{-[ℚ(u):ℚ]-ε}` is at least this
file's `height23^{-ε} q^{-1-ε}`.  The rational case follows from the algebraic one, a rational
`δqu` being pseudo-Pisot only if it is an integer.

**The toolkit** kept from the Ridout derivation is consumed elsewhere: the `height23` bounds
(`finite_height23_le`, `u_le_height23`, `one_le_height23`; NKR), the `p`-adic values of
`2ˣ3ʸ` (`padic_two_sUnit`, `padic_three_sUnit`) and the closed form of the `S = {∞, 2, 3}`
Subspace product on a coprime pair (`approxProduct_pair_eq`, `approxProduct_smul`;
`CITED/SubspaceTriple.lean`, `RB/AnchoredPlaces.lean`).

## References

* [CZ04] Corvaja–Zannier, Acta Math. **193** (2004), 175–191 (`CITED/CorvajaZannier.lean`
  carries the statement vocabulary).
* Subspace-Theorems, `CorvajaZannier2004/MainTheorem.lean` — the Main Theorem in full.
-/

namespace CZ

open Subspace Rat.AbsoluteValue Height

/-- `2 ^ |x| ≤ height23 x y`: the height dominates the `2`-part of the `S`-unit. -/
private lemma two_pow_natAbs_le_height23 (x y : ℤ) : 2 ^ x.natAbs ≤ height23 x y := by
  unfold height23
  rcases le_total 0 x with hx | hx
  · have hnat : x.natAbs = x.toNat := by omega
    calc 2 ^ x.natAbs = 2 ^ x.toNat := by rw [hnat]
      _ ≤ 2 ^ x.toNat * 3 ^ y.toNat := Nat.le_mul_of_pos_right _ (by positivity)
      _ ≤ _ := le_max_left _ _
  · have hnat : x.natAbs = (-x).toNat := by omega
    calc 2 ^ x.natAbs = 2 ^ (-x).toNat := by rw [hnat]
      _ ≤ 2 ^ (-x).toNat * 3 ^ (-y).toNat := Nat.le_mul_of_pos_right _ (by positivity)
      _ ≤ _ := le_max_right _ _

/-- `3 ^ |y| ≤ height23 x y`: the height dominates the `3`-part of the `S`-unit. -/
private lemma three_pow_natAbs_le_height23 (x y : ℤ) : 3 ^ y.natAbs ≤ height23 x y := by
  unfold height23
  rcases le_total 0 y with hy | hy
  · have hnat : y.natAbs = y.toNat := by omega
    calc 3 ^ y.natAbs = 3 ^ y.toNat := by rw [hnat]
      _ ≤ 2 ^ x.toNat * 3 ^ y.toNat := Nat.le_mul_of_pos_left _ (by positivity)
      _ ≤ _ := le_max_left _ _
  · have hnat : y.natAbs = (-y).toNat := by omega
    calc 3 ^ y.natAbs = 3 ^ (-y).toNat := by rw [hnat]
      _ ≤ 2 ^ (-x).toNat * 3 ^ (-y).toNat := Nat.le_mul_of_pos_left _ (by positivity)
      _ ≤ _ := le_max_right _ _

/-- **Finitely many `S`-unit exponent pairs of bounded height** ([CZ04], ℚ-case):
for any real `B`, only finitely many `(x, y) ∈ ℤ²` have `height23 x y ≤ B`: the
exponents are confined to a box (from `2^{|x|}, 3^{|y|} ≤ height23 x y`). -/
@[category API, AMS 11, ref "CZ04", group "three_halves_m4"]
theorem finite_height23_le (B : ℝ) :
    {q : ℤ × ℤ | (height23 q.1 q.2 : ℝ) ≤ B}.Finite := by
  set M : ℕ := ⌊B⌋₊ with hM
  apply Set.Finite.subset
    ((Set.finite_Icc (-(M : ℤ)) M).prod (Set.finite_Icc (-(M : ℤ)) M))
  rintro ⟨x, y⟩ hxy
  simp only [Set.mem_ofPred_eq] at hxy
  have hle : height23 x y ≤ M := Nat.le_floor hxy
  have hx2 : 2 ^ x.natAbs ≤ M := le_trans (two_pow_natAbs_le_height23 x y) hle
  have hy3 : 3 ^ y.natAbs ≤ M := le_trans (three_pow_natAbs_le_height23 x y) hle
  have hxb : x.natAbs < M := lt_of_lt_of_le Nat.lt_two_pow_self hx2
  have hyb : y.natAbs < M :=
    lt_of_lt_of_le (lt_of_lt_of_le Nat.lt_two_pow_self
      (Nat.pow_le_pow_left (by norm_num) _)) hy3
  exact Set.mem_prod.mpr ⟨Set.mem_Icc.mpr ⟨by omega, by omega⟩,
    Set.mem_Icc.mpr ⟨by omega, by omega⟩⟩

/-- **The 2-adic absolute value of the `S`-unit `2^x 3^y` is `2^{-x}`**
(`|·|₂ = Rat.AbsoluteValue.padic 2 = padicNorm 2`). -/
@[category API, AMS 11, ref "CZ04", group "three_halves_m4"]
theorem padic_two_sUnit (x y : ℤ) :
    padic 2 ((2 : ℚ) ^ x * (3 : ℚ) ^ y) = (2 : ℝ) ^ (-x) := by
  have h2 : padic 2 (2 : ℚ) = (2 : ℝ)⁻¹ := by
    rw [padic_eq_padicNorm, show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num,
      padicNorm.padicNorm_p_of_prime]; norm_num
  have h3q : padicNorm 2 (3 : ℚ) = 1 := by
    rw [show (3 : ℚ) = ((3 : ℤ) : ℚ) by norm_num]
    exact (padicNorm.int_eq_one_iff 3).mpr (by norm_num)
  have h3 : padic 2 (3 : ℚ) = 1 := by rw [padic_eq_padicNorm, h3q]; norm_num
  rw [map_mul, map_zpow₀, map_zpow₀, h2, h3, one_zpow, mul_one, inv_zpow, ← zpow_neg]

/-- **The 3-adic absolute value of the `S`-unit `2^x 3^y` is `3^{-y}`**. -/
@[category API, AMS 11, ref "CZ04", group "three_halves_m4"]
theorem padic_three_sUnit (x y : ℤ) :
    padic 3 ((2 : ℚ) ^ x * (3 : ℚ) ^ y) = (3 : ℝ) ^ (-y) := by
  have h3 : padic 3 (3 : ℚ) = (3 : ℝ)⁻¹ := by
    rw [padic_eq_padicNorm, show (3 : ℚ) = ((3 : ℕ) : ℚ) by norm_num,
      padicNorm.padicNorm_p_of_prime]; norm_num
  have h2q : padicNorm 3 (2 : ℚ) = 1 := by
    rw [show (2 : ℚ) = ((2 : ℤ) : ℚ) by norm_num]
    exact (padicNorm.int_eq_one_iff 2).mpr (by norm_num)
  have h2 : padic 3 (2 : ℚ) = 1 := by rw [padic_eq_padicNorm, h2q]; norm_num
  rw [map_mul, map_zpow₀, map_zpow₀, h2, h3, one_zpow, one_mul, inv_zpow, ← zpow_neg]

/-!
### The Subspace product on a coprime pair

At the places `S = {∞, 2, 3}`, with the forms `X₀ − δX₁, X₁` at `∞` and the coordinates at `2`
and `3`, the Subspace product of a coprime integer pair has a closed form
(`approxProduct_pair_eq`): every finite local norm of a coprime pair is `1`
(`coprime_padic_max`).
-/

attribute [local instance] Classical.propDecidable

/-- The per-place linear forms of the CZ Subspace application: at the real place the pair
`X₀ − δ·X₁, X₁` (so the first form measures `p₀ − δ·qu`, whose size is `‖sval‖`), and at
every other place the coordinate forms `X₀, X₁` (measuring the `p`-adic sizes of the two
coordinates). -/
@[category API, AMS 11, ref "CZ04", group "three_halves_m4"]
noncomputable def Lforms (δ : ℚ) (v : AbsoluteValue ℚ ℝ) : Fin 2 → ((Fin 2 → ℚ) →ₗ[ℚ] ℚ) :=
  if v = Rat.AbsoluteValue.real
  then ![LinearMap.proj 0 - δ • LinearMap.proj 1, LinearMap.proj 1]
  else ![LinearMap.proj 0, LinearMap.proj 1]

/-- The local sup-norm of a pair `‖![a,b]‖_v = max(|a|_v, |b|_v)`. -/
@[category API, AMS 11, ref "CZ04", group "three_halves_m4"]
lemma localNorm_pair (v : AbsoluteValue ℚ ℝ) (a b : ℚ) :
    localNorm v ![a, b] = max (v a) (v b) := by
  unfold localNorm
  have hcoe : ∀ i : Fin 2, v (![a, b] i) = ![v a, v b] i := by intro i; fin_cases i <;> simp
  rw [show (⨆ i, v (![a, b] i)) = ⨆ i, ![v a, v b] i from iSup_congr hcoe]
  refine (eq_of_forall_ge_iff ?_).symm
  intro c; simp [ciSup_le_iff, Fin.forall_fin_two]

/-- **Coprimality kills the finite places**: for coprime integers `A, B` and any prime `p`,
`max(|A|_p, |B|_p) = 1`.  This is what collapses the Subspace product formula on the
coprime-integer representative — every non-archimedean local norm is `1`. -/
@[category API, AMS 11, ref "CZ04", group "three_halves_m4"]
lemma coprime_padic_max (p : ℕ) [Fact p.Prime] (A B : ℤ) (h : IsCoprime A B) :
    max (padic p (A : ℚ)) (padic p (B : ℚ)) = 1 := by
  have hpp : p.Prime := Fact.out
  have hA1 : padic p (A : ℚ) ≤ 1 := by rw [padic_eq_padicNorm]; exact_mod_cast padicNorm.of_int A
  have hB1 : padic p (B : ℚ) ≤ 1 := by rw [padic_eq_padicNorm]; exact_mod_cast padicNorm.of_int B
  by_cases hAdvd : (p : ℤ) ∣ A
  · have hBndvd : ¬ (p : ℤ) ∣ B := by
      intro hBdvd
      have hu : IsUnit (p : ℤ) := h.isUnit_of_dvd' hAdvd hBdvd
      rw [Int.isUnit_iff] at hu; have := hpp.two_le; omega
    have hB : padic p (B : ℚ) = 1 := by
      rw [padic_eq_padicNorm]; exact_mod_cast (padicNorm.int_eq_one_iff B).mpr hBndvd
    rw [max_eq_right (by rw [hB]; exact hA1)]; exact hB
  · have hA : padic p (A : ℚ) = 1 := by
      rw [padic_eq_padicNorm]; exact_mod_cast (padicNorm.int_eq_one_iff A).mpr hAdvd
    rw [max_eq_left (by rw [hA]; exact hB1)]; exact hA

/-- The real place is distinct from the `2`-adic place (they disagree at `2`). -/
@[category API, AMS 11, ref "CZ04", group "three_halves_m4"]
lemma real_ne_padic2 : (Rat.AbsoluteValue.real) ≠ padic 2 := by
  intro h
  have := congrArg (fun v => v (2 : ℚ)) h
  simp only [real_eq_abs] at this
  rw [padic_eq_padicNorm, show (2:ℚ) = ((2:ℕ):ℚ) by norm_num, padicNorm.padicNorm_p_of_prime] at this
  norm_num at this

/-- The real place is distinct from the `3`-adic place (they disagree at `3`). -/
@[category API, AMS 11, ref "CZ04", group "three_halves_m4"]
lemma real_ne_padic3 : (Rat.AbsoluteValue.real) ≠ padic 3 := by
  intro h
  have := congrArg (fun v => v (3 : ℚ)) h
  simp only [real_eq_abs] at this
  rw [padic_eq_padicNorm, show (3:ℚ) = ((3:ℕ):ℚ) by norm_num, padicNorm.padicNorm_p_of_prime] at this
  norm_num at this

/-- The `2`-adic and `3`-adic places are distinct (they disagree at `2`). -/
@[category API, AMS 11, ref "CZ04", group "three_halves_m4"]
lemma padic2_ne_padic3 : (padic 2) ≠ padic 3 := by
  intro h
  have := congrArg (fun v => v (2 : ℚ)) h
  rw [padic_eq_padicNorm, padic_eq_padicNorm, show (2:ℚ) = ((2:ℕ):ℚ) by norm_num,
    padicNorm.padicNorm_p_of_prime] at this
  have h3 : padicNorm 3 ((2:ℕ):ℚ) = 1 := by
    rw [show ((2:ℕ):ℚ) = ((2:ℤ):ℚ) by norm_num]
    exact (padicNorm.int_eq_one_iff 2).mpr (by norm_num)
  rw [h3] at this; norm_num at this

/-- **The Subspace product on the coprime-integer representative, in closed form.**
For coprime integers `A, B`, the `S = {∞, 2, 3}` double product of `Lforms δ` at the point
`![A, B]` collapses (all finite local norms are `1`, by `coprime_padic_max`) to
`|A − δB|·|B| / max(|A|,|B|)² · |A|₂|B|₂ · |A|₃|B|₃`. -/
@[category API, AMS 11, ref "CZ04", group "three_halves_m4"]
lemma approxProduct_pair_eq (δ : ℚ) (A B : ℤ) (hAB : IsCoprime A B) :
    approxProduct {Rat.AbsoluteValue.real, padic 2, padic 3} (Lforms δ) ![(A : ℚ), (B : ℚ)]
    = real ((A : ℚ) - δ * B) * real (B : ℚ) / (max (real (A : ℚ)) (real (B : ℚ))) ^ 2
      * (padic 2 (A : ℚ) * padic 2 (B : ℚ))
      * (padic 3 (A : ℚ) * padic 3 (B : ℚ)) := by
  have hLNr : localNorm Rat.AbsoluteValue.real ![(A : ℚ), (B : ℚ)]
      = max (real (A : ℚ)) (real (B : ℚ)) := localNorm_pair _ _ _
  have hLN2 : localNorm (padic 2) ![(A : ℚ), (B : ℚ)] = 1 := by
    rw [localNorm_pair]; exact coprime_padic_max 2 A B hAB
  have hLN3 : localNorm (padic 3) ![(A : ℚ), (B : ℚ)] = 1 := by
    rw [localNorm_pair]; exact coprime_padic_max 3 A B hAB
  unfold approxProduct
  rw [show ({Rat.AbsoluteValue.real, padic 2, padic 3} : Finset (AbsoluteValue ℚ ℝ))
      = insert Rat.AbsoluteValue.real (insert (padic 2) {padic 3}) from rfl,
    Finset.prod_insert (by simp [real_ne_padic2, real_ne_padic3]),
    Finset.prod_insert (by simp [padic2_ne_padic3]), Finset.prod_singleton]
  rw [hLNr, hLN2, hLN3]
  simp only [Lforms, ite_true, ite_eq_right real_ne_padic2.symm, ite_eq_right real_ne_padic3.symm,
    Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  ring

/-! ### Scale invariance of the Subspace product -/

/-- The local sup-norm scales by `|c|_v`: `‖c • x‖_v = |c|_v · ‖x‖_v`. -/
@[category API, AMS 11, ref "CZ04", group "three_halves_m4"]
lemma localNorm_smul {n : ℕ} (v : AbsoluteValue ℚ ℝ) (c : ℚ) (x : Fin n → ℚ) :
    localNorm v (c • x) = v c * localNorm v x := by
  unfold localNorm
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  rw [Real.mul_iSup_of_nonneg (v.nonneg c)]

/-- **`approxProduct` is scale-invariant** (a projective quantity): `approxProduct S L (c•x) =
approxProduct S L x` for `c ≠ 0`, so it may be evaluated on a coprime integer representative. -/
@[category API, AMS 11, ref "CZ04", group "three_halves_m4"]
lemma approxProduct_smul {n : ℕ} (S : Finset (AbsoluteValue ℚ ℝ))
    (L : AbsoluteValue ℚ ℝ → Fin n → ((Fin n → ℚ) →ₗ[ℚ] ℚ)) (c : ℚ) (hc : c ≠ 0)
    (x : Fin n → ℚ) :
    approxProduct S L (c • x) = approxProduct S L x := by
  unfold approxProduct
  refine Finset.prod_congr rfl (fun v _ => Finset.prod_congr rfl (fun i _ => ?_))
  have hvc : v c ≠ 0 := (AbsoluteValue.ne_zero_iff v).mpr hc
  have hL : (L v i) (c • x) = c * (L v i) x := by rw [← smul_eq_mul, ← map_smul]
  rw [localNorm_smul, hL, map_mul]
  exact mul_div_mul_left _ _ hvc

/-! ### Bounds for `height23` -/

/-- The `S`-unit `2^x·3^y` is bounded by its height `height23`. -/
@[category API, AMS 11, ref "CZ04", group "three_halves_m4"]
lemma u_le_height23 (x y : ℤ) : (2 : ℚ) ^ x * (3 : ℚ) ^ y ≤ (height23 x y : ℚ) := by
  have h2 : (2 : ℚ) ^ x ≤ (2 : ℚ) ^ x.toNat := by
    rw [show ((2:ℚ) ^ x.toNat) = (2:ℚ) ^ (x.toNat : ℤ) by rw [zpow_natCast]]
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  have h3 : (3 : ℚ) ^ y ≤ (3 : ℚ) ^ y.toNat := by
    rw [show ((3:ℚ) ^ y.toNat) = (3:ℚ) ^ (y.toNat : ℤ) by rw [zpow_natCast]]
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  calc (2 : ℚ) ^ x * (3 : ℚ) ^ y
      ≤ (2 : ℚ) ^ x.toNat * (3 : ℚ) ^ y.toNat := by gcongr
    _ = ((2 ^ x.toNat * 3 ^ y.toNat : ℕ) : ℚ) := by push_cast; ring
    _ ≤ (height23 x y : ℚ) := by rw [height23]; exact_mod_cast le_max_left _ _

/-- `height23 ≥ 1`. -/
@[category API, AMS 11, ref "CZ04", group "three_halves_m4"]
lemma one_le_height23 (x y : ℤ) : 1 ≤ height23 x y := by
  rw [height23]; exact le_max_of_le_left (Nat.one_le_iff_ne_zero.mpr (by positivity))

/-! ## The Main Theorem, from the Subspace-Theorems library

`Γ = ⟨2, 3⟩ ≤ ℝˣ`, the injective encoding `(q, x, y) ↦ (q, 2ˣ3ʸ)`, and the two facts about
`u = 2ˣ3ʸ` that turn the library's general bound `H(u)^{-ε} |q|^{-[ℚ(u):ℚ]-ε}` into this file's
`height23^{-ε} q^{-1-ε}`. -/

section MainTheorem

open NumberField IntermediateField

/-- The group `Γ = ⟨2, 3⟩ ≤ ℝˣ` of the Main Theorem in this specialization. -/
@[category API, AMS 11, ref "CZ04", group "three_halves_m4"]
noncomputable def gamma23 : Subgroup ℝˣ :=
  Subgroup.closure {Units.mk0 (2 : ℝ) two_ne_zero, Units.mk0 (3 : ℝ) three_ne_zero}

/-- `Γ = ⟨2, 3⟩` is finitely generated. -/
@[category API, AMS 11, ref "CZ04", group "three_halves_m4"]
lemma gamma23_fg : gamma23.FG :=
  (Subgroup.fg_iff _).mpr ⟨_, rfl, Set.toFinite _⟩

/-- Every element of `Γ = ⟨2, 3⟩` is algebraic (it is rational). -/
@[category API, AMS 11, ref "CZ04", group "three_halves_m4"]
lemma gamma23_isAlgebraic : ∀ u ∈ gamma23, IsAlgebraic ℚ (u : ℝ) := by
  intro u hu
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℝ) (2 : ℚ)
    · simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℝ) (3 : ℚ)
  | one => simpa using isAlgebraic_one
  | mul x y _ _ hx hy => simpa using hx.mul hy
  | inv x _ hx => simpa using hx.inv

/-- The element `2ˣ3ʸ` of `Γ`: the exponent encoding of `CZ.sval`. -/
@[category API, AMS 11, ref "CZ04", group "three_halves_m4"]
noncomputable def unit23 (x y : ℤ) : gamma23 :=
  ⟨Units.mk0 (2 : ℝ) two_ne_zero ^ x * Units.mk0 (3 : ℝ) three_ne_zero ^ y,
    gamma23.mul_mem (gamma23.zpow_mem (Subgroup.subset_closure (by simp)) x)
      (gamma23.zpow_mem (Subgroup.subset_closure (by simp)) y)⟩

/-- `2ˣ3ʸ ∈ Γ` is the real number `2ˣ3ʸ`, a rational. -/
@[category API, AMS 11, ref "CZ04", group "three_halves_m4"]
lemma unit23_val (x y : ℤ) :
    (((unit23 x y : gamma23) : ℝˣ) : ℝ) = (((2 : ℚ) ^ x * (3 : ℚ) ^ y : ℚ) : ℝ) := by
  simp [unit23, Units.val_zpow_eq_zpow_val]

/-- `aˣ = a^{x⁺} / a^{x⁻}`. -/
@[category API, AMS 11, ref "CZ04", group "three_halves_m4"]
lemma zpow_eq_div_toNat (a : ℚ) (x : ℤ) : a ^ x = a ^ x.toNat / a ^ (-x).toNat := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg x <;> simp

/-- **The absolute height of `2ˣ3ʸ` is at most `height23 x y`** (in fact equal): `H` of a
rational is `max(|num|, den)`, and `2ˣ3ʸ = A / B` with `max(A, B) = height23 x y`. -/
@[category API, AMS 11, ref "CZ04", group "three_halves_m4"]
lemma absMulHeight₁_unit23_le (x y : ℤ) :
    absMulHeight₁ ((((2 : ℚ) ^ x * (3 : ℚ) ^ y : ℚ) : ℝ)) ≤ height23 x y := by
  set r : ℚ := (2 : ℚ) ^ x * (3 : ℚ) ^ y
  have hcomp := absMulHeight₁_comp (Algebra.ofId ℚ ℝ) r
  rw [show (Algebra.ofId ℚ ℝ) r = (r : ℝ) from rfl] at hcomp
  rw [hcomp]
  have h := absMulHeight₁_pow_finrank r
  rw [Module.finrank_self, pow_one, Rat.mulHeight₁_eq_max] at h
  rw [h]
  set A : ℤ := 2 ^ x.toNat * 3 ^ y.toNat
  set B : ℤ := 2 ^ (-x).toNat * 3 ^ (-y).toNat
  have hA : 0 < A := by positivity
  have hB : 0 < B := by positivity
  have hr : r = Rat.divInt A B := by
    rw [Rat.divInt_eq_div]
    simp only [r, A, B, zpow_eq_div_toNat (2 : ℚ) x, zpow_eq_div_toNat (3 : ℚ) y]
    push_cast
    field_simp
  have hnum : r.num.natAbs ≤ A.natAbs := by
    rw [hr]; exact Int.natAbs_le_of_dvd_ne_zero (Rat.num_dvd A hB.ne') hA.ne'
  have hden : (r.den : ℤ) ≤ B := by
    rw [hr]; exact Int.le_of_dvd hB (Rat.den_dvd A B)
  have hmax : max r.num.natAbs r.den ≤ height23 x y := by
    unfold height23
    refine max_le_max ?_ ?_
    · have : A.natAbs = 2 ^ x.toNat * 3 ^ y.toNat := by simp [A, Int.natAbs_mul, Int.natAbs_pow]
      omega
    · have : (B : ℤ) = ((2 ^ (-x).toNat * 3 ^ (-y).toNat : ℕ) : ℤ) := by push_cast [B]; rfl
      omega
  exact_mod_cast hmax

/-- A rational number generates the trivial extension: `[ℚ(r) : ℚ] = 1`. -/
@[category API, AMS 11, ref "CZ04", group "three_halves_m4"]
lemma finrank_adjoin_ratCast (r : ℚ) : Module.finrank ℚ ℚ⟮(r : ℝ)⟯ = 1 := by
  rw [IntermediateField.adjoin_simple_eq_bot_iff.mpr ⟨r, by simp⟩, IntermediateField.finrank_bot]

/-- The exponents are determined by `2ˣ3ʸ`, through its `2`- and `3`-adic absolute values. -/
@[category API, AMS 11, ref "CZ04", group "three_halves_m4"]
lemma unit23_injective {x y x' y' : ℤ} (h : unit23 x y = unit23 x' y') : x = x' ∧ y = y' := by
  have hv := congrArg (fun u : gamma23 ↦ (((u : ℝˣ) : ℝ))) h
  simp only [unit23_val, Rat.cast_inj] at hv
  have h2 := padic_two_sUnit x y
  have h3 := padic_three_sUnit x y
  rw [hv, padic_two_sUnit] at h2
  rw [hv, padic_three_sUnit] at h3
  exact ⟨neg_injective (zpow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num) h2).symm,
    neg_injective (zpow_right_injective₀ (by norm_num : (0 : ℝ) < 3) (by norm_num) h3).symm⟩

/-- **The Corvaja–Zannier Main Theorem, `Γ = ⟨2, 3⟩`, algebraic multiplier** ([CZ04]): for real
algebraic `δ ≠ 0` and `ε > 0`, only finitely many `(q, x, y)` with `q ≥ 1` have `|δqu| > 1`,
`δqu` not pseudo-Pisot and `0 < ‖δqu‖ < H(u)^{-ε} q^{-1-ε}`, where `u = 2ˣ3ʸ`.

The specialization of the Subspace-Theorems library's `finite_setOf_not_isPseudoPisot` (the Main
Theorem for every finitely generated `Γ ≤ ℝˣ` of algebraic numbers) at `Γ = ⟨2, 3⟩`:
`(q, x, y) ↦ (q, 2ˣ3ʸ)` is injective (`unit23_injective`), `[ℚ(u) : ℚ] = 1`
(`finrank_adjoin_ratCast`) and `H(u) ≤ height23 x y` (`absMulHeight₁_unit23_le`).  The
predicates `CZ.IsPseudoPisot` and the library's `IsPseudoPisot` have the same definition.  The
finiteness is ineffective. -/
@[category research solved, AMS 11, ref "CZ04" "Schmidt91", group "rb_rational_base"]
theorem pseudoPisot_approx_alg (δ : ℝ) (hδalg : IsAlgebraic ℚ δ) (hδ : δ ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    {p : ℕ × ℤ × ℤ | 1 ≤ p.1 ∧
      1 < |svalR δ p.1 p.2.1 p.2.2| ∧
      ¬ IsPseudoPisot (svalR δ p.1 p.2.1 p.2.2) ∧
      0 < distToNearestInt (svalR δ p.1 p.2.1 p.2.2) ∧
      distToNearestInt (svalR δ p.1 p.2.1 p.2.2)
        < (height23 p.2.1 p.2.2 : ℝ) ^ (-ε) * (p.1 : ℝ) ^ (-1 - ε)}.Finite := by
  have hST := _root_.finite_setOf_not_isPseudoPisot gamma23_fg gamma23_isAlgebraic hδalg hδ hε
  set g : ℕ × ℤ × ℤ → ℤ × gamma23 := fun p ↦ ((p.1 : ℤ), unit23 p.2.1 p.2.2) with hg
  have hginj : Function.Injective g := by
    rintro ⟨q, x, y⟩ ⟨q', x', y'⟩ h
    simp only [hg, Prod.mk.injEq, Nat.cast_inj] at h
    obtain ⟨rfl, hu⟩ := h
    obtain ⟨rfl, rfl⟩ := unit23_injective hu
    rfl
  refine (hST.preimage hginj.injOn).subset ?_
  rintro ⟨q, x, y⟩ ⟨hq, h1, hPP, h0, hlt⟩
  have hsv : svalR δ q x y = δ * ((q : ℤ) : ℝ) * (((unit23 x y : gamma23) : ℝˣ) : ℝ) := by
    rw [unit23_val]; push_cast [svalR]; ring
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, hg]
  rw [← hsv]
  refine ⟨h1, hPP, h0, lt_of_lt_of_le hlt ?_⟩
  rw [unit23_val, finrank_adjoin_ratCast]
  have hH1 : (1 : ℝ) ≤ absMulHeight₁ ((((2 : ℚ) ^ x * (3 : ℚ) ^ y : ℚ) : ℝ)) := one_le_absMulHeight₁ _
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  rw [Int.cast_natCast, abs_of_pos hq0, Nat.cast_one]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact Real.rpow_le_rpow_of_nonpos (by linarith) (absMulHeight₁_unit23_le x y) (by linarith)

/-- **The Corvaja–Zannier Main Theorem, `Γ = ⟨2, 3⟩`, rational multiplier** ([CZ04]): for
`δ ∈ ℚ*` and `ε > 0`, only finitely many `(q, x, y)` with `q ≥ 1` have `|δqu| > 1`, `δqu ∉ ℤ`
and `0 < ‖δqu‖ < H(u)^{-ε} q^{-1-ε}`, `u = 2ˣ3ʸ`.  The case `δ ∈ ℚ` of `pseudoPisot_approx_alg`:
a rational `δqu` is pseudo-Pisot only if it is an integer (`isPseudoPisot_ratCast_iff`). -/
@[category research solved, AMS 11, ref "CZ04", group "three_halves_m4"]
theorem pseudoPisot_approx_of_subspace (δ : ℚ) (hδ : δ ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    {p : ℕ × ℤ × ℤ | 1 ≤ p.1 ∧
      1 < |sval δ p.1 p.2.1 p.2.2| ∧
      ¬ (∃ n : ℤ, sval δ p.1 p.2.1 p.2.2 = n) ∧
      0 < (sval δ p.1 p.2.1 p.2.2).distToNearestInt ∧
      ((sval δ p.1 p.2.1 p.2.2).distToNearestInt : ℝ)
        < (height23 p.2.1 p.2.2 : ℝ) ^ (-ε) * (p.1 : ℝ) ^ (-1 - ε)}.Finite := by
  refine (pseudoPisot_approx_alg (δ : ℝ) (by simpa using isAlgebraic_algebraMap (A := ℝ) δ)
    (by exact_mod_cast hδ) ε hε).subset ?_
  rintro ⟨q, x, y⟩ ⟨hq, h1, hn, h0, hlt⟩
  have hsv : svalR (δ : ℝ) q x y = ((sval δ q x y : ℚ) : ℝ) := by
    push_cast [sval, svalR]; ring
  have hd : distToNearestInt ((sval δ q x y : ℚ) : ℝ)
      = (((sval δ q x y).distToNearestInt : ℚ) : ℝ) := by
    simp [distToNearestInt, Rat.distToNearestInt, Rat.round_cast]
  refine ⟨hq, ?_, ?_, ?_, ?_⟩ <;> simp only [hsv]
  · exact_mod_cast h1
  · rw [isPseudoPisot_ratCast_iff]; exact fun h ↦ hn h.2
  · rw [hd]; exact_mod_cast h0
  · rw [hd]; exact hlt

end MainTheorem

/-! ## The exceptional set, named

The set whose finiteness the Main Theorem asserts, given a name for the consumers that need to
speak about it (`BB13/Subspace.lean`).  Relocated here on 2026-07-21 from the deleted
`CITED/CorvajaZannierEffective.lean`; its companion axiom (an *effective* bound on the
cardinality) was retired — see `CITED/BugeaudEvertseRidout.lean` for what the quantitative
literature does prove. -/

/-- The **Corvaja–Zannier exceptional set** of `CZ.pseudoPisot_approx_of_subspace`, named: the
triples `(q, x, y)` with `u = 2ˣ3ʸ`, `1 < |δqu|`, `δqu ∉ ℤ`, and
`0 < ‖δqu‖ < H(u)^{-ε}·q^{-1-ε}`. -/
def approxSet (δ : ℚ) (ε : ℝ) : Set (ℕ × ℤ × ℤ) :=
  {p : ℕ × ℤ × ℤ | 1 ≤ p.1 ∧ 1 < |sval δ p.1 p.2.1 p.2.2| ∧
    ¬ (∃ m : ℤ, sval δ p.1 p.2.1 p.2.2 = m) ∧
    0 < (sval δ p.1 p.2.1 p.2.2).distToNearestInt ∧
    ((sval δ p.1 p.2.1 p.2.2).distToNearestInt : ℝ)
      < (height23 p.2.1 p.2.2 : ℝ) ^ (-ε) * (p.1 : ℝ) ^ (-1 - ε)}

/-- The Corvaja–Zannier exceptional set is finite (qualitative theorem, restated on the named
set).  Footprint `std3`. -/
@[category research solved, AMS 11, ref "CZ04", group "three_halves_m4"]
theorem approxSet_finite (δ : ℚ) (hδ : δ ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    (approxSet δ ε).Finite :=
  pseudoPisot_approx_of_subspace δ hδ ε hε

end CZ
