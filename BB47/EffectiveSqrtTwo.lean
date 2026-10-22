/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Complex.ExponentialBounds
import CITED.Matveev
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# An explicit effective exponent for `‖2ⁿ √2‖`

Bennett and Bugeaud [BB12, Thm. 1.2] prove that for every quadratic `ξ` and base `b`,
`‖bⁿ ξ‖ > c(ξ, b) b^{-(1 - τ(ξ, P))n}` with `τ` *effectively computable*, and make `τ` explicit
only for `√(b^{2k} + 1)` (Thms. 1.3, 1.4); `√2` in base `2` is not covered.  Here
(`plans/report-sqrtnorm.html` §5.1, rank #3) we make it explicit for `ξ = √2`, `b = 2`:

  `‖2ⁿ √2‖ ≥ 2^{-(1 - τ)n} / 24`  for all `n`,  with  `τ = 2^{-42}`.

So no run of equal binary digits of `√2` starting after position `n` is longer than
`(1 - 2^{-42}) n + 5`.

## The argument

Let `m` be odd with `ε = |m − 2ⁿ√2| < 1/2` (even `m` halve to `n − 1`; `ε ≥ 1/2` is trivial).
In `ℤ[√2]` put `γ = m + 2ⁿ√2`, of norm `Δ = m² − 2^{2n+1}`, odd, `|Δ| = ε γ`.  Write `γ = β η^k`
with `η = 1 + √2` and `k ≥ 0` chosen so that `√|Δ| ≤ β < η √|Δ|`.  Then both conjugates of `β` are
`≤ η√|Δ|`, so `h(β) ≤ log |Δ| + 2 log η`, while

  `Λ = log β + k log η − (2n + 3) log √2 = log (γ / (γ − γ̄))`,  `0 < |Λ| ≤ |Δ| / 2^{2n+1}`.

The three logarithms are `ℤ`-independent (take norms: `2` vs odd `|Δ| ≥ 3`).  Matveev's
Theorem 2.1 with the *weighted* `B = max |b_j| A_j / A_β ≍ n / log |Δ|` (Feldman's device, as in
[BB12, §2]) gives `log(1/|Λ|) ≪ log|Δ| · log(n / log|Δ|)`, which forces `log |Δ| ≥ 2^{-42} n log 2`.
This is the archimedean form of Bennett–Bugeaud's `p`-adic argument; it needs only the corpus's
cited Matveev (`CITED/Matveev.lean`), not a `p`-adic two-log bound over `ℚ(√2)`.

**Axioms.**  `dist_ge` and `run_le` use the standard three plus the cited
`Matveev.linearForms_logs_indep` (Theorem 2.1 of [Mat00], checked against the paper: `A_j ≥
max{D h(α_j), |log α_j|}`, weighted `B` of (1.3) with `b_n ≠ 0`, `C(n,κ)`, `C₀`, `W₀` as printed).
A `p`-adic two-log bound (Bugeaud–Laurent over `ℚ(√2)`) would give a larger `τ`, but the corpus
transcribes it only over `ℚ`.

## Main results

* `BB47.EffectiveSqrtTwo.core` — `log |Δ| + 2 log η ≥ 2^{-43}(2n + 4) log 2` (Matveev).
* `BB47.EffectiveSqrtTwo.dist_ge` — `|2ⁿ√2 − m| ≥ 2^{-(1-τ)n}/24` for all `n : ℕ`, `m : ℤ`.
* `BB47.EffectiveSqrtTwo.run_le` — a run of `L` equal binary digits of `√2` at positions
  `n + 1, …, n + L` has `L ≤ (1 − τ) n + 5`.

## References

* [BB12] M. A. Bennett, Y. Bugeaud, *Effective results for restricted rational approximation to
  quadratic irrationals*, Acta Arith. **155** (2012), 259–269, doi:10.4064/aa155-3-3 — Thm. 1.2
  and its proof, §2.
* [Mat00] E. M. Matveev, Izv. Math. **64** (2000) — Thm. 2.1 (`CITED/Matveev.lean`).
-/

namespace BB47.EffectiveSqrtTwo

open IntermediateField Polynomial

/-! ## The field `ℚ(√2) ⊂ ℝ` -/

lemma sqrt2_mul_self : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)

lemma isIntegral_sqrt2 : IsIntegral ℚ (Real.sqrt 2) :=
  ⟨X ^ 2 - C 2, monic_X_pow_sub_C _ (by norm_num), by simp [sq]⟩

/-- The real quadratic field `ℚ(√2)`, as a subfield of `ℝ`. -/
@[category API, AMS 11, ref "BB12", group "bugeaud_10_47"]
noncomputable abbrev K : IntermediateField ℚ ℝ := ℚ⟮Real.sqrt 2⟯

instance : FiniteDimensional ℚ K := adjoin.finiteDimensional isIntegral_sqrt2

instance : NumberField K := ⟨⟩

lemma minpoly_sqrt2 : minpoly ℚ (Real.sqrt 2) = X ^ 2 - C 2 := by
  refine (minpoly.eq_of_irreducible_of_monic ?_ (by simp [sq])
    (monic_X_pow_sub_C _ (by norm_num))).symm
  refine X_pow_sub_C_irreducible_of_prime Nat.prime_two fun b hb => ?_
  have h : ((|b| : ℚ) : ℝ) = Real.sqrt 2 := by
    rw [show (2 : ℝ) = (b : ℝ) ^ 2 by exact_mod_cast hb.symm, Real.sqrt_sq_eq_abs]; push_cast; rfl
  exact irrational_sqrt_two ⟨|b|, h⟩

lemma finrank_K : Module.finrank ℚ K = 2 := by
  rw [adjoin.finrank isIntegral_sqrt2, minpoly_sqrt2, natDegree_X_pow_sub_C]

/-- `√2 ∈ K`. -/
noncomputable def r : K := ⟨Real.sqrt 2, mem_adjoin_simple_self ℚ _⟩

/-- The real embedding `ℤ√2 → ℝ`. -/
noncomputable def ψ : ℤ√2 →+* ℝ := Zsqrtd.lift ⟨Real.sqrt 2, by simp⟩

/-- `ℤ√2 → K`. -/
noncomputable def ι : ℤ√2 →+* K := Zsqrtd.lift ⟨r, Subtype.ext (by simp [r]; rfl)⟩

/-- The embedding `K → ℂ` (through `ℝ`). -/
noncomputable def φ : K →+* ℂ := Complex.ofRealHom.comp K.val.toRingHom

lemma ψ_apply (z : ℤ√2) : ψ z = z.re + z.im * Real.sqrt 2 := by
  simp [ψ]

lemma ψ_star (z : ℤ√2) : ψ (star z) = z.re - z.im * Real.sqrt 2 := by
  simp [ψ_apply]; ring

lemma val_ι (z : ℤ√2) : ((ι z : K) : ℝ) = ψ z := by
  simp [ι, ψ_apply, r]

lemma φ_ι (z : ℤ√2) : φ (ι z) = (ψ z : ℂ) := by
  simp [φ, val_ι]

lemma ψ_injective : Function.Injective ψ :=
  Zsqrtd.lift_injective _ fun n h => by
    have h2 : ((|n| : ℤ) : ℝ) = Real.sqrt 2 := by
      rw [show (2 : ℝ) = (n : ℝ) ^ 2 by rw [sq]; exact_mod_cast h, Real.sqrt_sq_eq_abs]
      push_cast; rfl
    exact irrational_sqrt_two ⟨|n|, by exact_mod_cast h2⟩

/-! ## Heights of elements of `ℤ[√2]` -/

lemma ι_eq (z : ℤ√2) : ι z = (z.re : K) + (z.im : K) * r := by simp [ι]

lemma r_mul_r : r * r = ((2 : ℕ) : K) := by
  apply Subtype.ext
  rw [MulMemClass.coe_mul]
  simp only [r, sqrt2_mul_self]
  rfl

/-- The height of `a + b√2 ∈ ℤ[√2]` is at most `2 log⁺ (|a| + |b|√2)`: finite places see an
integer, and every complex embedding sends `√2` to `±√2`. -/
lemma logHeight_ι_le (z : ℤ√2) :
    Height.logHeight₁ (ι z) ≤ 2 * Real.posLog (|(z.re : ℝ)| + |(z.im : ℝ)| * Real.sqrt 2) := by
  set L := |(z.re : ℝ)| + |(z.im : ℝ)| * Real.sqrt 2
  rw [NumberField.logHeight₁_eq]
  have hfin : ∑ᶠ v : NumberField.FinitePlace K, Real.posLog (v (ι z)) = 0 := by
    refine finsum_eq_zero_of_forall_eq_zero fun v => ?_
    rw [Real.posLog_eq_zero_iff, abs_of_nonneg (apply_nonneg v _)]
    have hv : IsNonarchimedean (v ·) := NumberField.FinitePlace.add_le v
    have H (n : ℤ) : v n ≤ 1 :=
      hv.apply_intCast_le_one (map_zero_le v 1) (map_one v) (map_neg_eq_map v)
    have hr : v r ≤ 1 := by
      have h2 : v r * v r ≤ 1 := by
        rw [← map_mul, r_mul_r]; exact_mod_cast H 2
      nlinarith [apply_nonneg v r]
    rw [ι_eq]
    refine (hv _ _).trans (max_le (H _) ?_)
    show v (_ * r) ≤ 1
    rw [map_mul]; nlinarith [H z.im, apply_nonneg v r, apply_nonneg v ((z.im : ℤ) : K)]
  have hinf : ∀ w : NumberField.InfinitePlace K, w (ι z) ≤ L := by
    intro w
    have hw2 : w r = Real.sqrt 2 := by
      have h2 : w r * w r = 2 := by rw [← map_mul, r_mul_r, w.map_natCast]; norm_num
      rw [← h2, Real.sqrt_mul_self (apply_nonneg w r)]
    rw [ι_eq, NumberField.InfinitePlace.coe_apply]
    refine (w.1.add_le _ _).trans ?_
    rw [map_mul, ← NumberField.InfinitePlace.coe_apply, ← NumberField.InfinitePlace.coe_apply,
      ← NumberField.InfinitePlace.coe_apply, hw2, w.map_intCast, w.map_intCast]
    simp [L, Int.norm_eq_abs]
  rw [hfin, add_zero]
  calc ∑ w : NumberField.InfinitePlace K, (w.mult : ℝ) * Real.posLog (w (ι z))
      ≤ ∑ w : NumberField.InfinitePlace K, (w.mult : ℝ) * Real.posLog L := by
        refine Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        exact Real.posLog_le_posLog (by linarith [apply_nonneg w (ι z)]) (hinf w)
    _ = 2 * Real.posLog L := by
        rw [← Finset.sum_mul, ← Nat.cast_sum, NumberField.InfinitePlace.sum_mult_eq, finrank_K]
        norm_num

/-! ## The three bases `√2`, `η = 1 + √2`, `β` -/

/-- `√2 ∈ ℤ[√2]`. -/
def s₀ : ℤ√2 := ⟨0, 1⟩

/-- The fundamental unit `η = 1 + √2 ∈ ℤ[√2]`. -/
def η₀ : ℤ√2 := ⟨1, 1⟩

/-- `η⁻¹ = √2 − 1 ∈ ℤ[√2]`. -/
def ηi₀ : ℤ√2 := ⟨-1, 1⟩

/-- The fundamental unit `η = 1 + √2` of `ℤ[√2]`, as a real number. -/
@[category API, AMS 11, ref "BB12", group "bugeaud_10_47"]
noncomputable def η : ℝ := 1 + Real.sqrt 2

lemma sqrt2_gt : 1.41 < Real.sqrt 2 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

lemma sqrt2_lt : Real.sqrt 2 < 1.42 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

lemma one_lt_η : 1 < η := by unfold η; linarith [sqrt2_gt]

lemma η_pos : 0 < η := by linarith [one_lt_η]

lemma log_η_pos : 0 < Real.log η := Real.log_pos one_lt_η

lemma ψ_s₀ : ψ s₀ = Real.sqrt 2 := by simp [ψ_apply, s₀]

lemma ψ_η₀ : ψ η₀ = η := by simp [ψ_apply, η₀, η]

lemma ψ_ηi₀ : ψ ηi₀ = η⁻¹ := by
  have h : (-1 + Real.sqrt 2) * η = 1 := by unfold η; nlinarith [sqrt2_mul_self]
  rw [ψ_apply]; simpa [ηi₀] using eq_inv_of_mul_eq_one_left h

lemma ψ_star_ηi₀ : ψ (star ηi₀) = -η := by
  rw [ψ_star]; simp [ηi₀, η]; ring

lemma two_log_η_le : 2 * Real.log η ≤ 3 * Real.log 2 := by
  have h1 : Real.log (η ^ 2) = 2 * Real.log η := by simp [Real.log_pow]
  have h2 : Real.log (2 ^ 3) = 3 * Real.log 2 := by simp [Real.log_pow]
  rw [← h1, ← h2]
  refine Real.log_le_log (pow_pos η_pos 2) ?_
  unfold η; nlinarith [sqrt2_mul_self, sqrt2_lt]

lemma norm_log_φ_ι (z : ℤ√2) (h : 0 < ψ z) :
    ‖Complex.log (φ (ι z))‖ = |Real.log (ψ z)| := by
  rw [φ_ι, ← Complex.ofReal_log h.le, Complex.norm_real, Real.norm_eq_abs]

lemma clamp_nonneg (z : ℤ√2) : 0 ≤ Matveev.clampHeightIndep φ (ι z) :=
  le_max_of_le_right (norm_nonneg _)

lemma A_s₀ : Matveev.clampHeightIndep φ (ι s₀) ≤ Real.log 2 := by
  have hl : Real.log (Real.sqrt 2) = Real.log 2 / 2 := Real.log_sqrt (by norm_num)
  refine max_le ((logHeight_ι_le s₀).trans (le_of_eq ?_)) ?_
  · simp only [s₀, Int.cast_zero, abs_zero, Int.cast_one, abs_one, one_mul, zero_add]
    rw [Real.posLog_eq_log (by rw [abs_of_pos (by positivity)]; linarith [sqrt2_gt]), hl]; ring
  · rw [norm_log_φ_ι _ (by rw [ψ_s₀]; positivity), ψ_s₀, hl,
      abs_of_nonneg (by linarith [(Real.log_pos one_lt_two)])]
    linarith [(Real.log_pos one_lt_two)]

lemma A_η₀ : Matveev.clampHeightIndep φ (ι η₀) ≤ 2 * Real.log η := by
  refine max_le ((logHeight_ι_le η₀).trans (le_of_eq ?_)) ?_
  · simp only [η₀, Int.cast_one, abs_one, one_mul]
    rw [Real.posLog_eq_log (by rw [abs_of_pos (by positivity)]; linarith [Real.sqrt_nonneg 2])]
    rfl
  · rw [norm_log_φ_ι _ (by rw [ψ_η₀]; exact η_pos), ψ_η₀, abs_of_pos log_η_pos]
    linarith [log_η_pos]

/-- `|a| + |b|√2 ≤ max(|a + b√2|, |a − b√2|)`. -/
lemma abs_add_abs_le_max (p q : ℝ) : |p| + |q| ≤ max |p + q| |p - q| := by
  rcases le_total 0 p with hp | hp <;> rcases le_total 0 q with hq | hq <;>
    simp only [abs_of_nonneg, abs_of_nonpos, hp, hq] <;>
    first
    | exact le_max_of_le_left (by linarith [le_abs_self (p + q), neg_abs_le (p + q)])
    | exact le_max_of_le_right (by linarith [le_abs_self (p - q), neg_abs_le (p - q)])

lemma re_im_le (z : ℤ√2) :
    |(z.re : ℝ)| + |(z.im : ℝ)| * Real.sqrt 2 ≤ max |ψ z| |ψ (star z)| := by
  have h := abs_add_abs_le_max (z.re : ℝ) (z.im * Real.sqrt 2)
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Real.sqrt 2)] at h
  rwa [ψ_apply, ψ_star]

/-! ## Elementary lemmas -/

/-- `|log (1 + u)| ≤ 2|u|` for `|u| ≤ 1/2`. -/
lemma abs_log_one_add_le {u : ℝ} (hu : |u| ≤ 1 / 2) : |Real.log (1 + u)| ≤ 2 * |u| := by
  have hu' := abs_le.mp hu
  have h0 : 0 < 1 + u := by linarith
  have h1 := Real.log_le_sub_one_of_pos h0
  have h2 := Real.one_sub_inv_le_log_of_pos h0
  have h3 : (1 + u)⁻¹ ≤ 1 + 2 * |u| := by
    rw [inv_le_iff_one_le_mul₀ h0]
    rcases le_total 0 u with h | h
    · rw [abs_of_nonneg h]; nlinarith
    · rw [abs_of_nonpos h]; nlinarith
  rw [abs_le]; constructor <;> linarith [le_abs_self u]

/-- `a ↦ a log(Q/a)` is increasing while `log(Q/a) ≥ 1`. -/
lemma mul_log_le {a T Q : ℝ} (ha : 0 < a) (haT : a ≤ T) (hQ : 1 ≤ Real.log (Q / T))
    (hQ0 : 0 < Q) : a * Real.log (Q / a) ≤ T * Real.log (Q / T) := by
  have hT : 0 < T := ha.trans_le haT
  have h1 : Real.log (Q / a) = Real.log (Q / T) + Real.log (T / a) := by
    rw [← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp
  have h2 : Real.log (T / a) ≤ T / a - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h3 : a * (T / a - 1) = T - a := by field_simp
  rw [h1, mul_add]
  nlinarith [mul_le_mul_of_nonneg_left h2 ha.le, mul_le_mul_of_nonneg_left hQ (sub_nonneg.2 haT)]

/-- If `2^a D^c = 2^b D^d` with `D ≥ 3` odd, then `a = b` and `c = d`. -/
lemma two_pow_odd_pow_inj {a b c d D : ℕ} (hD : Odd D) (hD3 : 3 ≤ D)
    (h : 2 ^ a * D ^ c = 2 ^ b * D ^ d) : a = b ∧ c = d := by
  have hD0 : D ≠ 0 := by omega
  have h2 : ¬ 2 ∣ D := by rintro ⟨e, rfl⟩; exact (Nat.not_even_iff_odd.2 hD) (even_two_mul e)
  have hv : ∀ x y : ℕ, padicValNat 2 (2 ^ x * D ^ y) = x := fun x y => by
    rw [padicValNat.mul (by positivity) (by positivity), padicValNat.prime_pow,
      padicValNat.pow (p := 2) D y, padicValNat.eq_zero_of_not_dvd h2, mul_zero, add_zero]
  have hab : a = b := by rw [← hv a c, h, hv]
  subst hab
  exact ⟨rfl, Nat.pow_right_injective (by omega) (Nat.eq_of_mul_eq_mul_left (by positivity) h)⟩

/-- For odd `m` and `n ≥ 2`, `|m² − 2^{2n+1}| ≥ 3`. -/
lemma three_le_abs_Δ (n : ℕ) (hn : 2 ≤ n) (m : ℤ) (hm : Odd m) :
    3 ≤ |m ^ 2 - 2 * 4 ^ n| := by
  obtain ⟨j, rfl⟩ := hm
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
  have h4 : (2 * j + 1) ^ 2 - 2 * (4 : ℤ) ^ (n' + 2) = 4 * (j * (j + 1)) + 1 - 32 * 4 ^ n' := by
    ring
  rw [h4]
  have hP1 : (1 : ℤ) ≤ 4 ^ n' := one_le_pow₀ (by norm_num)
  by_contra hlt
  push Not at hlt
  have hw : j * (j + 1) = 2 ^ (2 * n' + 3) := by
    rw [abs_lt] at hlt
    have : j * (j + 1) = 8 * 4 ^ n' := by omega
    rw [this, pow_add, pow_mul]; norm_num; ring
  -- the odd one of `j, j + 1` divides a power of `2`, so it is `±1`
  have hunit : ∀ o : ℤ, Odd o → o ∣ 2 ^ (2 * n' + 3) → o.natAbs = 1 := by
    intro o ho hdvd
    have h := Int.natAbs_dvd_natAbs.mpr hdvd
    rw [Int.natAbs_pow] at h
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h
    rcases i with _ | i
    · simpa using hi
    · exfalso
      have h2 : (2 : ℤ) ∣ o := Int.ofNat_dvd_left.mpr ⟨2 ^ i, by rw [hi]; ring⟩
      exact (Int.not_even_iff_odd.2 ho) (even_iff_two_dvd.2 h2)
  have h8 : (8 : ℤ) ≤ 2 ^ (2 * n' + 3) :=
    calc (8 : ℤ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * n' + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hsmall : ∀ o : ℤ, o.natAbs = 1 → (o = j ∨ o = j + 1) → j * (j + 1) ≤ 2 := by
    intro o ho hj
    rcases Int.natAbs_eq_iff.mp ho with h | h <;> push_cast at h <;>
      rcases hj with rfl | rfl <;> nlinarith
  rcases Int.even_or_odd j with he | ho
  · have := hsmall _ (hunit (j + 1) he.add_one ⟨j, by rw [← hw]; ring⟩) (Or.inr rfl)
    omega
  · have := hsmall _ (hunit j ho ⟨j + 1, by rw [← hw]⟩) (Or.inl rfl)
    omega

/-! ## Numerics -/

/-- `μ = 2^{-43}`; the exponent is `τ = 2μ = 2^{-42}`. -/
@[category API, AMS 11, ref "BB12", group "bugeaud_10_47"]
noncomputable def μ : ℝ := 1 / 2 ^ 43

/-- The constant `κ' = 3e log(2e)` inside Matveev's `W₀` at `D = 2`. -/
noncomputable def κ' : ℝ := 3 / 2 * Real.exp 1 * 2 * Real.log (Real.exp 1 * 2)

lemma C_eq : Matveev.C 3 1 = 11796480 * Real.exp 1 ^ 4 := by
  simp [Matveev.C, Nat.factorial, -Real.exp_one_pow]; ring

lemma C_le : Matveev.C 3 1 ≤ 6.45e8 := by
  have he := Real.exp_one_lt_d9
  have h4 : Real.exp 1 ^ 4 ≤ 2.7182818286 ^ 4 := pow_le_pow_left₀ (Real.exp_pos 1).le he.le 4
  rw [C_eq]; nlinarith

lemma log_e2 : Real.log (Real.exp 1 * 2) = 1 + Real.log 2 := by
  rw [Real.log_mul (Real.exp_pos 1).ne' (by norm_num), Real.log_exp]

lemma one_le_log_e2 : 1 ≤ Real.log (Real.exp 1 * 2) := by
  rw [log_e2]; linarith [Real.log_pos one_lt_two]

lemma C₀_eq : Matveev.C₀ 3 2 = 20.2 + 11 / 2 * Real.log 3 + 2 * Real.log 2
    + Real.log (Real.log (Real.exp 1 * 2)) := by
  have hl := one_le_log_e2
  unfold Matveev.C₀
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_rpow (by norm_num),
    Real.log_pow]
  push_cast; ring

lemma C₀_le : Matveev.C₀ 3 2 ≤ 30 := by
  have h3 : Real.log 3 ≤ 2 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num)]; exact Real.log_le_log (by norm_num) (by norm_num)
  have hl : Real.log (Real.log (Real.exp 1 * 2)) ≤ Real.log 2 := by
    have := Real.log_le_sub_one_of_pos (lt_of_lt_of_le one_pos one_le_log_e2)
    rw [log_e2] at this ⊢; linarith
  have h2 := Real.log_two_lt_d9
  rw [C₀_eq]; nlinarith

lemma C₀_nonneg : 0 ≤ Matveev.C₀ 3 2 := by
  have h3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hl : 0 ≤ Real.log (Real.log (Real.exp 1 * 2)) := Real.log_nonneg one_le_log_e2
  rw [C₀_eq]; linarith [Real.log_pos one_lt_two]

lemma κ'_eq : κ' = 3 * Real.exp 1 * (1 + Real.log 2) := by
  rw [κ', log_e2]; ring

lemma one_le_κ' : 1 ≤ κ' := by
  rw [κ'_eq]; nlinarith [Real.add_one_le_exp 1, Real.log_pos one_lt_two]

lemma log_κ'_div_le : Real.log (κ' / μ) ≤ 47 * Real.log 2 := by
  have he := Real.exp_one_lt_d9
  have h2 := Real.log_two_lt_d9
  have hκ : κ' ≤ 16 := by rw [κ'_eq]; nlinarith [Real.log_pos one_lt_two, Real.exp_pos 1]
  have : κ' / μ ≤ 2 ^ 47 := by
    rw [μ, div_div_eq_mul_div, div_one]; nlinarith
  calc Real.log (κ' / μ) ≤ Real.log (2 ^ 47) :=
        Real.log_le_log (div_pos (by linarith [one_le_κ']) (by norm_num [μ])) this
    _ = 47 * Real.log 2 := by simp [Real.log_pow]

lemma numeric :
    Matveev.C 3 1 * Matveev.C₀ 3 2 * 4 * (Real.log 2 * (3 * Real.log 2)) *
      (μ * Real.log (κ' / μ)) ≤ 0.45 := by
  have hC := C_le
  have hC0 := C₀_le
  have hC0' := C₀_nonneg
  have hCp : 0 ≤ Matveev.C 3 1 := by rw [C_eq]; positivity
  have hl := log_κ'_div_le
  have h2 := Real.log_two_lt_d9
  have h2p := Real.log_pos one_lt_two
  have hμ : μ = 1 / 2 ^ 43 := rfl
  have hA : Matveev.C 3 1 * Matveev.C₀ 3 2 ≤ 6.45e8 * 30 :=
    mul_le_mul hC hC0 hC0' (by norm_num)
  have hB : μ * Real.log (κ' / μ) ≤ 47 * Real.log 2 / 2 ^ 43 := by
    rw [hμ]; rw [hμ] at hl; nlinarith
  have hL : Real.log 2 * (3 * Real.log 2) * (47 * Real.log 2 / 2 ^ 43) ≤
      0.6931471808 * (3 * 0.6931471808) * (47 * 0.6931471808 / 2 ^ 43) := by
    gcongr
  calc _ ≤ 6.45e8 * 30 * 4 * (Real.log 2 * (3 * Real.log 2)) * (47 * Real.log 2 / 2 ^ 43) := by
        have hκ := one_le_κ'
        have hpos : 0 ≤ μ * Real.log (κ' / μ) := mul_nonneg (by norm_num [μ])
          (Real.log_nonneg (by rw [le_div_iff₀ (by norm_num [μ])]; norm_num [μ]; linarith))
        have h4 : 0 ≤ Real.log 2 * (3 * Real.log 2) := by positivity
        calc _ ≤ 6.45e8 * 30 * 4 * (Real.log 2 * (3 * Real.log 2)) * (μ * Real.log (κ' / μ)) := by
              gcongr
          _ ≤ _ := by gcongr
    _ ≤ 0.45 := by nlinarith

/-! ## The core estimate -/

lemma log_κ'_div_ge : 1 ≤ Real.log (κ' / μ) := by
  rw [Real.le_log_iff_exp_le (div_pos (by linarith [one_le_κ']) (by norm_num [μ]))]
  have he := Real.exp_one_lt_d9
  rw [le_div_iff₀ (by norm_num [μ])]
  have := one_le_κ'
  norm_num [μ]; nlinarith

/-- The arithmetic end of the core estimate: Matveev's lower bound for `|Λ|` (with `A_√2 ≤ log 2`,
`A_η ≤ 2 log η`, `A_β = a ≤ T`) contradicts `|Λ| ≤ |Δ| / 2^{2n+1}` once
`T = log |Δ| + 2 log η < μ (2n + 4) log 2`. -/
lemma final_contra {n : ℕ} (hn : 2 ≤ n) {a D A₀ A₁ lam : ℝ} (ha0 : 0 < a)
    (haT : a ≤ Real.log D + 2 * Real.log η)
    (hTμ : Real.log D + 2 * Real.log η < μ * ((2 * n + 4) * Real.log 2))
    (hA₀' : A₀ ≤ Real.log 2) (hA₁ : 0 ≤ A₁) (hA₁' : A₁ ≤ 2 * Real.log η)
    (hlam : lam ≤ Real.log D - (2 * n + 1) * Real.log 2)
    (hM : lam > -(Matveev.C 3 1 * Matveev.C₀ 3 ((2 : ℕ) : ℝ) *
      Matveev.W₀ ((2 * n + 4) * Real.log 2 / a) ((2 : ℕ) : ℝ) * ((2 : ℕ) : ℝ) ^ 2 *
        (A₀ * A₁ * a))) : False := by
  set Cn : ℝ := (2 * n + 4) * Real.log 2 with hCn
  set T := Real.log D + 2 * Real.log η with hTdef
  have hl2 := Real.log_pos one_lt_two
  have hμ1 : μ ≤ 1 / 100 := by norm_num [μ]
  have hCn0 : 0 < Cn := by rw [hCn]; positivity
  have haC : a ≤ Cn := by
    have : μ * Cn ≤ Cn := mul_le_of_le_one_left hCn0.le (by linarith)
    linarith
  set B := Cn / a with hB
  have hB1 : 1 ≤ B := by rw [hB, le_div_iff₀ ha0]; linarith
  set Q := κ' * Cn with hQ
  have hW : Matveev.W₀ B ((2 : ℕ) : ℝ) = Real.log (Q / a) := by
    unfold Matveev.W₀; rw [hQ, κ', hB]; push_cast; congr 1; field_simp
  have hQa : 1 ≤ Q / a := by
    rw [hQ, mul_div_assoc, ← hB]; exact one_le_mul_of_one_le_of_one_le one_le_κ' hB1
  have hW0 : 0 ≤ Real.log (Q / a) := Real.log_nonneg hQa
  have h01 : A₀ * A₁ ≤ Real.log 2 * (3 * Real.log 2) :=
    mul_le_mul hA₀' (hA₁'.trans two_log_η_le) hA₁ hl2.le
  set Kc := Matveev.C 3 1 * Matveev.C₀ 3 2 * 4 * (Real.log 2 * (3 * Real.log 2)) with hKc
  have hR1 : Matveev.C 3 1 * Matveev.C₀ 3 ((2 : ℕ) : ℝ) * Matveev.W₀ B ((2 : ℕ) : ℝ) *
      ((2 : ℕ) : ℝ) ^ 2 * (A₀ * A₁ * a) ≤ Kc * (a * Real.log (Q / a)) := by
    rw [hW, hKc]
    push_cast
    calc _ = (Matveev.C 3 1 * Matveev.C₀ 3 2 * 4 * Real.log (Q / a) * a) * (A₀ * A₁) := by ring
      _ ≤ (Matveev.C 3 1 * Matveev.C₀ 3 2 * 4 * Real.log (Q / a) * a) *
          (Real.log 2 * (3 * Real.log 2)) :=
          mul_le_mul_of_nonneg_left h01 (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
            (by rw [C_eq]; positivity) C₀_nonneg) (by norm_num)) hW0) ha0.le)
      _ = _ := by ring
  have hTpos : 0 < T := ha0.trans_le haT
  have hQμ : Q / (μ * Cn) = κ' / μ := by rw [hQ]; field_simp
  have hlogQT : 1 ≤ Real.log (Q / T) := by
    have hQpos : 0 < Q := mul_pos (by linarith [one_le_κ']) hCn0
    refine log_κ'_div_ge.trans (Real.log_le_log (div_pos (by linarith [one_le_κ'])
      (by norm_num [μ])) ?_)
    rw [← hQμ]
    exact div_le_div_of_nonneg_left hQpos.le hTpos hTμ.le
  have hQpos : 0 < Q := mul_pos (by linarith [one_le_κ']) hCn0
  have hR2 : a * Real.log (Q / a) ≤ μ * Cn * Real.log (κ' / μ) :=
    (mul_log_le ha0 haT hlogQT hQpos).trans
      (hQμ ▸ mul_log_le hTpos hTμ.le (hQμ ▸ log_κ'_div_ge) hQpos)
  have hKc0 : 0 ≤ Kc := by
    rw [hKc]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by rw [C_eq]; positivity) C₀_nonneg) (by norm_num))
      (by positivity)
  have hR3 : Kc * (a * Real.log (Q / a)) ≤ 0.45 * Cn := by
    calc _ ≤ Kc * (μ * Cn * Real.log (κ' / μ)) := mul_le_mul_of_nonneg_left hR2 hKc0
      _ = Kc * (μ * Real.log (κ' / μ)) * Cn := by
          rw [show μ * Cn * Real.log (κ' / μ) = μ * Real.log (κ' / μ) * Cn by ring, ← mul_assoc]
      _ ≤ 0.45 * Cn := mul_le_mul_of_nonneg_right numeric hCn0.le
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogDμ : Real.log D < μ * Cn := by linarith [log_η_pos]
  have hfin0 := lt_of_lt_of_le (neg_lt.mp hM) hR1
  have hfin1 : (2 * n + 1) * Real.log 2 - Real.log D < 0.45 * Cn := by
    linarith [hfin0, hlam, hR3]
  have hfin2 : (2 * n + 1) * Real.log 2 < (0.45 + μ) * ((2 * n + 4) * Real.log 2) := by
    rw [hCn] at hfin1 hlogDμ; linarith
  have hpos' : 0 < ((2 * n + 1) - (0.45 + μ) * (2 * n + 4)) * Real.log 2 :=
    mul_pos (by nlinarith only [hnr, hμ1]) hl2
  linarith

/-- The logarithms of `√2`, `η` and `β ∈ ℤ[√2]` are `ℤ`-linearly independent when `|N(β)|` is
odd and `≥ 3`: compare the norms `2`, `1`, `|N(β)|` of a multiplicative relation. -/
lemma log_indep (β₀ : ℤ√2) (hβ : 0 < ψ β₀) (hodd : Odd (Zsqrtd.norm β₀).natAbs)
    (h3 : 3 ≤ (Zsqrtd.norm β₀).natAbs) (c : Fin 3 → ℤ)
    (hr : ∑ i, (c i : ℝ) * Real.log (ψ (![s₀, η₀, β₀] i)) = 0) : ∀ i, c i = 0 := by
  set zz : Fin 3 → ℤ√2 := ![s₀, η₀, β₀] with hzz
  have hpos : ∀ i, 0 < ψ (zz i) := by
    intro i; fin_cases i
    · simp [hzz, ψ_s₀]
    · simp [hzz, ψ_η₀, η_pos]
    · simpa [hzz] using hβ
  -- split `c = P − Q` into nonnegative parts and exponentiate
  set P : Fin 3 → ℕ := fun i => (c i).toNat with hP
  set Q : Fin 3 → ℕ := fun i => (-c i).toNat with hQ
  have hcPQ : ∀ i, (c i : ℝ) = P i - Q i := fun i => by
    simp only [hP, hQ]; exact_mod_cast (Int.toNat_sub_toNat_neg (c i)).symm
  have hne : ∀ i, ψ (zz i) ≠ 0 := fun i => (hpos i).ne'
  have hprod : ∏ i, ψ (zz i) ^ P i = ∏ i, ψ (zz i) ^ Q i := by
    refine Real.log_injOn_pos (Set.mem_Ioi.2 (Finset.prod_pos fun i _ => pow_pos (hpos i) _))
      (Set.mem_Ioi.2 (Finset.prod_pos fun i _ => pow_pos (hpos i) _)) ?_
    rw [Real.log_prod (fun i _ => pow_ne_zero _ (hne i)),
      Real.log_prod (fun i _ => pow_ne_zero _ (hne i))]
    simp only [Real.log_pow]
    have : ∑ i, ((P i : ℝ) - Q i) * Real.log (ψ (zz i)) = 0 := by
      rw [← hr]; exact Finset.sum_congr rfl fun i _ => by rw [hcPQ]
    simp only [sub_mul, Finset.sum_sub_distrib] at this
    linarith
  have hZ : ∏ i, zz i ^ P i = ∏ i, zz i ^ Q i :=
    ψ_injective (by simpa only [map_prod, map_pow] using hprod)
  -- the norms
  set N : ℤ√2 →* ℕ := Int.natAbsHom.toMonoidHom.comp Zsqrtd.normMonoidHom with hN
  have hN0 : N s₀ = 2 := by
    show (Zsqrtd.norm s₀).natAbs = 2; simp [s₀, Zsqrtd.norm_def]
  have hN1 : N η₀ = 1 := by
    show (Zsqrtd.norm η₀).natAbs = 1; simp [η₀, Zsqrtd.norm_def]
  have hN2 : N β₀ = (Zsqrtd.norm β₀).natAbs := rfl
  have hNZ := congrArg N hZ
  simp only [Fin.prod_univ_three, hzz, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hNZ
  simp only [map_mul, map_pow, hN0, hN1, hN2, one_pow, mul_one] at hNZ
  obtain ⟨h0, h2⟩ := two_pow_odd_pow_inj hodd h3 hNZ
  have hc0 : (c 0 : ℝ) = 0 := by rw [hcPQ, h0, sub_self]
  have hc2 : (c 2 : ℝ) = 0 := by rw [hcPQ, h2, sub_self]
  rw [Fin.sum_univ_three, hc0, hc2] at hr
  simp only [zero_mul, zero_add, add_zero, hzz, Matrix.cons_val_one, Matrix.cons_val_zero,
    ψ_η₀] at hr
  have hc1 : (c 1 : ℝ) = 0 := by
    rcases mul_eq_zero.mp hr with h | h
    · exact h
    · exact absurd h log_η_pos.ne'
  intro i
  fin_cases i
  · exact_mod_cast hc0
  · exact_mod_cast hc1
  · exact_mod_cast hc2

/-- **Core estimate.**  For `n ≥ 2` and odd `m` with `|m − 2ⁿ√2| < 1/2`, the norm
`Δ = m² − 2^{2n+1}` of `m + 2ⁿ√2` satisfies `log |Δ| + 2 log η ≥ μ (2n + 4) log 2`.  Matveev's
Theorem 2.1, applied to `log β + k log η − (2n + 3) log √2`. -/
@[category research solved, AMS 11, ref "BB12", group "bugeaud_10_47"]
theorem core (n : ℕ) (hn : 2 ≤ n) (m : ℤ) (hm : Odd m)
    (hε : |(m : ℝ) - 2 ^ n * Real.sqrt 2| < 1 / 2) :
    μ * ((2 * n + 4) * Real.log 2) ≤
      Real.log |((m ^ 2 - 2 * 4 ^ n : ℤ) : ℝ)| + 2 * Real.log η := by
  by_contra hT
  push Not at hT
  set Δ : ℤ := m ^ 2 - 2 * 4 ^ n with hΔdef
  set S : ℝ := 2 ^ n * Real.sqrt 2 with hS
  set G : ℝ := m + S with hG
  set D : ℝ := |(Δ : ℝ)| with hD
  set Cn : ℝ := (2 * n + 4) * Real.log 2 with hCn
  have hl2 := Real.log_pos one_lt_two
  have hpn : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hS1 : 2 ^ n ≤ S := by rw [hS]; nlinarith [sqrt2_gt]
  have hε' := abs_lt.mp hε
  have hG1 : 2 ^ (n + 1) ≤ G := by rw [hG, pow_succ]; nlinarith [sqrt2_gt]
  have hG2 : G ≤ 2 ^ (n + 2) := by rw [hG, pow_add]; nlinarith [sqrt2_lt]
  have hGpos : 0 < G := lt_of_lt_of_le (by positivity) hG1
  have hSsq : S * S = 2 * 4 ^ n := by
    rw [hS, show (4 : ℝ) ^ n = 2 ^ n * 2 ^ n by rw [← mul_pow]; norm_num]
    linear_combination (2 : ℝ) ^ n * 2 ^ n * sqrt2_mul_self
  have hΔr : (Δ : ℝ) = ((m : ℝ) - S) * G := by
    rw [hΔdef, hG]; push_cast; linear_combination hSsq
  have hD3 : 3 ≤ D := by
    have := three_le_abs_Δ n hn m hm; rw [hD]; exact_mod_cast this
  have hDeq : D = |(m : ℝ) - S| * G := by rw [hD, hΔr, abs_mul, abs_of_pos hGpos]
  have hmS : |(m : ℝ) - S| < 1 / 2 := hε
  have hDG : D ≤ G * G := by
    rw [hDeq]; nlinarith [abs_nonneg ((m : ℝ) - S)]
  -- the unit decomposition `γ = β η^k`
  set sD := Real.sqrt D with hsD
  have hsDsq : sD * sD = D := Real.mul_self_sqrt (by linarith)
  have hsD1 : 1 ≤ sD := by rw [hsD, Real.one_le_sqrt]; linarith
  have hsDG : sD ≤ G := by
    rw [hsD, show G = Real.sqrt (G * G) from (Real.sqrt_mul_self hGpos.le).symm]
    exact Real.sqrt_le_sqrt hDG
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near ((one_le_div (by positivity)).mpr hsDG) one_lt_η
  obtain ⟨γ₀, hγ₀⟩ : ∃ γ₀ : ℤ√2, γ₀ = ⟨m, 2 ^ n⟩ := ⟨_, rfl⟩
  set β₀ : ℤ√2 := γ₀ * ηi₀ ^ k with hβ₀
  have hψγ : ψ γ₀ = G := by rw [hγ₀, ψ_apply, hG, hS]; push_cast; ring
  have hηk : 0 < η ^ k := pow_pos η_pos k
  have hψβ : ψ β₀ = G / η ^ k := by
    rw [hβ₀, map_mul, map_pow, hψγ, ψ_ηi₀, inv_pow, div_eq_mul_inv]
  set b := ψ β₀ with hbdef
  have hb1 : sD ≤ b := by
    rw [hψβ, le_div_iff₀ hηk]; rw [le_div_iff₀ (by positivity)] at hk1; linarith
  have hb2 : b < η * sD := by
    rw [hψβ, div_lt_iff₀ hηk]; rw [div_lt_iff₀ (by positivity)] at hk2
    rw [pow_succ] at hk2; linarith
  have hbpos : 0 < b := by linarith
  have hbs : |ψ (star β₀)| ≤ sD := by
    have h1 : ψ (star β₀) = ((m : ℝ) - S) * (-η) ^ k := by
      rw [hβ₀, star_mul, star_pow, map_mul, map_pow, ψ_star_ηi₀, ψ_star, hγ₀, hS]
      push_cast; ring
    have h2 : |ψ (star β₀)| * b = D := by
      rw [h1, abs_mul, abs_pow, abs_neg, abs_of_pos η_pos, hψβ, hDeq]
      field_simp
    have h3 : |ψ (star β₀)| * b ≤ sD * b := by rw [h2, ← hsDsq]; nlinarith
    exact le_of_mul_le_mul_right h3 hbpos
  -- the height of `β`
  set T := Real.log D + 2 * Real.log η with hTdef
  have hlogsD : Real.log sD = Real.log D / 2 := Real.log_sqrt (by linarith)
  have hlogηsD : Real.log (η * sD) = Real.log η + Real.log D / 2 := by
    rw [Real.log_mul η_pos.ne' (by linarith), hlogsD]
  have hlogD : 0 < Real.log D := Real.log_pos (by linarith)
  have hHβ : Height.logHeight₁ (ι β₀) ≤ T := by
    refine (logHeight_ι_le β₀).trans ?_
    have hsη : sD ≤ η * sD := le_mul_of_one_le_left (by linarith) one_lt_η.le
    have hmax := (re_im_le β₀).trans
      (max_le ((abs_of_pos hbpos).le.trans hb2.le) (hbs.trans hsη))
    have h1 : 1 ≤ η * sD := hsD1.trans hsη
    have hx0 : -1 ≤ |(β₀.re : ℝ)| + |(β₀.im : ℝ)| * Real.sqrt 2 := by
      have := abs_nonneg (β₀.re : ℝ)
      have := mul_nonneg (abs_nonneg (β₀.im : ℝ)) (Real.sqrt_nonneg 2)
      linarith
    calc 2 * Real.posLog _ ≤ 2 * Real.posLog (η * sD) := by
          gcongr
      _ = T := by
          rw [Real.posLog_eq_log (by rw [abs_of_pos (by linarith)]; exact h1), hlogηsD, hTdef]
          ring
  set a := Matveev.clampHeightIndep φ (ι β₀) with hadef
  have hnormβ : ‖Complex.log (φ (ι β₀))‖ = Real.log b := by
    rw [norm_log_φ_ι _ hbpos, abs_of_nonneg (Real.log_nonneg (by linarith))]
  have hlogb1 : Real.log D / 2 ≤ Real.log b := by
    rw [← hlogsD]; exact Real.log_le_log (by linarith) hb1
  have hlogb2 : Real.log b ≤ Real.log η + Real.log D / 2 := by
    rw [← hlogηsD]; exact Real.log_le_log hbpos hb2.le
  have haT : a ≤ T := max_le hHβ (by rw [hnormβ]; linarith [log_η_pos])
  have ha0 : 0 < a := lt_of_lt_of_le (by linarith) (le_max_of_le_right hnormβ.ge)
  -- `k log η ≤ (n + 2) log 2`
  have hk : (k : ℝ) * Real.log η ≤ (n + 2) * Real.log 2 := by
    have h1 : η ^ k ≤ 2 ^ (n + 2) := hk1.trans ((div_le_self hGpos.le hsD1).trans hG2)
    have h2 := Real.log_le_log hηk h1
    rw [Real.log_pow, Real.log_pow] at h2; push_cast at h2; exact h2
  -- the linear form
  set zz : Fin 3 → ℤ√2 := ![s₀, η₀, β₀] with hzz
  set α : Fin 3 → K := fun i => ι (zz i) with hα
  set bv : Fin 3 → ℤ := ![-(2 * n + 3 : ℤ), k, 1] with hbv
  have hpos : ∀ i, 0 < ψ (zz i) := by
    intro i; fin_cases i
    · simp [hzz, ψ_s₀]
    · simp [hzz, ψ_η₀, η_pos]
    · simpa [hzz] using hbpos
  have hφlog : ∀ i, Complex.log (φ (α i)) = ((Real.log (ψ (zz i)) : ℝ) : ℂ) := fun i => by
    rw [hα, φ_ι, ← Complex.ofReal_log (hpos i).le]
  have hnormβ : (Zsqrtd.norm β₀).natAbs = Δ.natAbs := by
    have h1 : Zsqrtd.norm ηi₀ = -1 := by simp [ηi₀, Zsqrtd.norm_def]
    have h2 : Zsqrtd.norm γ₀ = Δ := by
      rw [hγ₀, Zsqrtd.norm_def, hΔdef, show (4 : ℤ) ^ n = 2 ^ n * 2 ^ n by
        rw [← mul_pow]; norm_num]
      ring
    have h3 : Zsqrtd.norm β₀ = Δ * (-1) ^ k := by
      rw [hβ₀, Zsqrtd.norm_mul, h2, ← h1]
      exact congrArg _ (map_pow Zsqrtd.normMonoidHom ηi₀ k)
    simp [h3, Int.natAbs_mul, Int.natAbs_pow]
  have hodd : Odd (Zsqrtd.norm β₀).natAbs := by
    rw [hnormβ, Int.natAbs_odd, hΔdef]
    exact (hm.pow).sub_even ⟨4 ^ n, by ring⟩
  have h3 : 3 ≤ (Zsqrtd.norm β₀).natAbs := by
    have := three_le_abs_Δ n hn m hm
    rw [← hΔdef, ← Int.natCast_natAbs] at this; rw [hnormβ]; exact_mod_cast this
  have hindep : ∀ c : Fin 3 → ℤ,
      (∑ i, (c i : ℂ) * Complex.log (φ (α i))) = 0 → ∀ i, c i = 0 := by
    intro c hc
    refine log_indep β₀ hbpos hodd h3 c ?_
    have h : ((∑ i, (c i : ℝ) * Real.log (ψ (zz i)) : ℝ) : ℂ) = 0 := by
      rw [← hc]; push_cast; simp only [hφlog]
    exact_mod_cast h
  have hSpos : 0 < S := lt_of_lt_of_le (by positivity) hS1
  have hreal : -((2 * n + 3 : ℝ)) * Real.log (Real.sqrt 2) + k * Real.log η + Real.log b
      = Real.log (G / (2 * S)) := by
    have hl : Real.log (Real.sqrt 2) = Real.log 2 / 2 := Real.log_sqrt (by norm_num)
    rw [hψβ, Real.log_div hGpos.ne' hηk.ne', Real.log_pow,
      Real.log_div hGpos.ne' (by positivity), hS,
      Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, hl]
    ring
  have hΛ : (∑ i, (bv i : ℂ) * Complex.log (φ (α i))) = ((Real.log (G / (2 * S)) : ℝ) : ℂ) := by
    rw [← hreal, Fin.sum_univ_three]
    simp only [hφlog, hbv, hzz, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, ψ_s₀, ψ_η₀]
    push_cast; ring
  have hΛne : Real.log (G / (2 * S)) ≠ 0 := fun h => by
    have := hindep bv (by rw [hΛ, h, Complex.ofReal_zero]) 2
    simp [hbv] at this
  have hΛle : |Real.log (G / (2 * S))| ≤ D / 2 ^ (2 * n + 1) := by
    have hu : G / (2 * S) = 1 + ((m : ℝ) - S) / (2 * S) := by
      rw [hG]; field_simp; ring
    have hmS0 := abs_nonneg ((m : ℝ) - S)
    have hGS : (2 : ℝ) ^ (2 * n + 1) ≤ G * S := by
      calc (2 : ℝ) ^ (2 * n + 1) = 2 ^ (n + 1) * 2 ^ n := by ring
        _ ≤ G * S := mul_le_mul hG1 hS1 (by positivity) hGpos.le
    rw [hu]
    refine (abs_log_one_add_le ?_).trans ?_
    · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * S), div_le_iff₀ (by positivity)]
      linarith
    · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * S), hDeq,
        show (2 : ℝ) * (|(m : ℝ) - S| / (2 * S)) = |(m : ℝ) - S| / S by field_simp,
        div_le_div_iff₀ hSpos (by positivity)]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hGS hmS0
  -- Matveev's Theorem 2.1, with the weighted `B = Cn / A_β`
  have hμ1 : μ ≤ 1 / 100 := by norm_num [μ]
  have hμ0 : 0 < μ := by norm_num [μ]
  have hCn0 : 0 < Cn := by rw [hCn]; positivity
  have hTμ : T < μ * Cn := hT
  have haC : a ≤ Cn := by
    have : μ * Cn ≤ Cn := mul_le_of_le_one_left hCn0.le (by linarith)
    linarith
  set B := Cn / a with hB
  have hB1 : 1 ≤ B := by rw [hB, le_div_iff₀ ha0]; linarith
  have hαne : ∀ i, α i ≠ 0 := fun i h => by
    have h' := congrArg φ h
    rw [map_zero, hα, φ_ι] at h'
    exact (hpos i).ne' (by exact_mod_cast h')
  have hα2 : α 2 = ι β₀ := by simp [hα, hzz]
  have hBw : ∀ j, (|bv j| : ℝ) * Matveev.clampHeightIndep φ (α j) /
      Matveev.clampHeightIndep φ (α 2) ≤ B := by
    intro j
    rw [hα2, ← hadef, hB]
    refine div_le_div_of_nonneg_right ?_ ha0.le
    fin_cases j
    · have h0 : α 0 = ι s₀ := by simp [hα, hzz]
      simp only [Fin.zero_eta, h0, hbv, Matrix.cons_val_zero]
      have : |((-(2 * n + 3 : ℤ) : ℤ) : ℝ)| = 2 * n + 3 := by
        push_cast; rw [abs_neg, abs_of_pos (by positivity)]
      rw [this, hCn]
      calc (2 * (n : ℝ) + 3) * Matveev.clampHeightIndep φ (ι s₀) ≤ (2 * n + 3) * Real.log 2 :=
            mul_le_mul_of_nonneg_left A_s₀ (by positivity)
        _ ≤ (2 * n + 4) * Real.log 2 := by linarith only [hl2]
    · have h1 : α 1 = ι η₀ := by simp [hα, hzz]
      simp only [Fin.mk_one, h1, hbv, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _), hCn]
      calc (k : ℝ) * Matveev.clampHeightIndep φ (ι η₀) ≤ k * (2 * Real.log η) :=
            mul_le_mul_of_nonneg_left A_η₀ (Nat.cast_nonneg k)
        _ ≤ (2 * n + 4) * Real.log 2 := by linarith only [hk]
    · simp only [Fin.reduceFinMk, hα2, hbv, Matrix.cons_val_two, Matrix.tail_cons,
        Matrix.head_cons, Int.cast_one, abs_one, one_mul, ← hadef]
      exact haC
  have hM := Matveev.linearForms_logs_indep (by norm_num : 2 ≤ 3) φ 1
    (Or.inl ⟨rfl, fun x => by simp [φ]⟩) α hαne hindep bv 2 (by simp [hbv]) B hB1 hBw
  rw [hΛ, finrank_K, Fin.prod_univ_three, hα2, ← hadef, Complex.norm_real,
    Real.norm_eq_abs] at hM
  have h0 : α 0 = ι s₀ := by simp [hα, hzz]
  have h1 : α 1 = ι η₀ := by simp [hα, hzz]
  rw [h0, h1] at hM
  -- the upper bound for `|Λ|`
  have hlogΛ : Real.log |Real.log (G / (2 * S))| ≤ Real.log D - (2 * n + 1) * Real.log 2 := by
    calc _ ≤ Real.log (D / 2 ^ (2 * n + 1)) := Real.log_le_log (abs_pos.mpr hΛne) hΛle
      _ = _ := by
        rw [Real.log_div (by linarith) (by positivity), Real.log_pow]; push_cast; ring
  exact final_contra hn ha0 haT hTμ A_s₀ (clamp_nonneg _) A_η₀ hlogΛ hM

/-! ## The main theorem -/

/-- The exponent `τ = 2^{-42}`. -/
@[category API, AMS 11, ref "BB12", group "bugeaud_10_47"]
noncomputable def τ : ℝ := 1 / 2 ^ 42

lemma τ_eq : τ = 2 * μ := by norm_num [τ, μ]

lemma τ_pos : 0 < τ := by norm_num [τ]

lemma τ_le : τ ≤ 1 / 2 := by norm_num [τ]

lemma Δ_eq (n : ℕ) (m : ℤ) : ((m ^ 2 - 2 * 4 ^ n : ℤ) : ℝ) =
    ((m : ℝ) - 2 ^ n * Real.sqrt 2) * ((m : ℝ) + 2 ^ n * Real.sqrt 2) := by
  push_cast
  rw [show (4 : ℝ) ^ n = 2 ^ n * 2 ^ n by rw [← mul_pow]; norm_num]
  linear_combination (2 : ℝ) ^ n * 2 ^ n * sqrt2_mul_self

lemma η_sq_le : η ^ 2 ≤ 6 := by unfold η; nlinarith [sqrt2_mul_self, sqrt2_lt]

lemma two_le_η_sq : 2 ≤ η ^ 2 := by unfold η; nlinarith [sqrt2_gt]

/-- `2^{τn} ≤ |Δ| η²` for odd `m` near `2ⁿ√2`. -/
lemma rpow_le_abs_Δ (n : ℕ) (m : ℤ) (hm : Odd m)
    (hε : |(m : ℝ) - 2 ^ n * Real.sqrt 2| < 1 / 2) :
    (2 : ℝ) ^ (τ * n) ≤ |((m ^ 2 - 2 * 4 ^ n : ℤ) : ℝ)| * η ^ 2 := by
  set D := |((m ^ 2 - 2 * 4 ^ n : ℤ) : ℝ)| with hD
  have hodd : Odd (m ^ 2 - 2 * 4 ^ n) := (hm.pow).sub_even ⟨4 ^ n, by ring⟩
  have hne : (m ^ 2 - 2 * 4 ^ n : ℤ) ≠ 0 := fun h => by
    rw [h] at hodd; exact Int.not_odd_zero hodd
  have hD1 : 1 ≤ D := by
    have := Int.one_le_abs hne
    rw [hD, ← Int.cast_abs]; exact_mod_cast this
  rcases le_or_gt n 1 with h | h
  · have hτn : τ * n ≤ 1 := by
      have : (n : ℝ) ≤ 1 := by exact_mod_cast h
      nlinarith [τ_pos, τ_le]
    calc (2 : ℝ) ^ (τ * n) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hτn
      _ ≤ η ^ 2 := by rw [Real.rpow_one]; exact two_le_η_sq
      _ ≤ D * η ^ 2 := le_mul_of_one_le_left (by positivity) hD1
  · have hc := core n h m hm hε
    rw [← hD] at hc
    rw [Real.rpow_def_of_pos two_pos]
    have h2 : Real.exp (2 * Real.log η) = η ^ 2 := by
      rw [show 2 * Real.log η = Real.log (η ^ 2) by rw [Real.log_pow]; push_cast; ring,
        Real.exp_log (pow_pos η_pos 2)]
    calc Real.exp (Real.log 2 * (τ * n)) ≤ Real.exp (Real.log D + 2 * Real.log η) := by
          refine Real.exp_le_exp.2 (le_trans ?_ hc)
          rw [τ_eq]
          nlinarith [Real.log_pos one_lt_two, (by norm_num [μ] : (0 : ℝ) < μ)]
      _ = D * η ^ 2 := by rw [Real.exp_add, Real.exp_log (by linarith), h2]

/-- The odd case of the main theorem. -/
lemma odd_case (n : ℕ) (m : ℤ) (hm : Odd m)
    (hε : |(m : ℝ) - 2 ^ n * Real.sqrt 2| < 1 / 2) :
    (2 : ℝ) ^ (-(1 - τ) * n) / 24 ≤ |2 ^ n * Real.sqrt 2 - m| := by
  have h1 := rpow_le_abs_Δ n m hm hε
  rw [Δ_eq, abs_mul] at h1
  set S := (2 : ℝ) ^ n * Real.sqrt 2 with hS
  have hpn : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hε' := abs_lt.mp hε
  have hG : 0 < (m : ℝ) + S := by rw [hS]; nlinarith [sqrt2_gt]
  have hG2 : (m : ℝ) + S ≤ 4 * 2 ^ n := by rw [hS]; nlinarith [sqrt2_lt]
  rw [abs_of_pos hG] at h1
  have hsplit : (2 : ℝ) ^ (-(1 - τ) * n) = 2 ^ (τ * n) / 2 ^ n := by
    rw [show -(1 - τ) * (n : ℝ) = τ * n - n by ring, Real.rpow_sub two_pos, Real.rpow_natCast]
  rw [hsplit, abs_sub_comm]
  have hη := η_sq_le
  have hηp : 0 < η ^ 2 := pow_pos η_pos 2
  have hd0 := abs_nonneg ((m : ℝ) - S)
  rw [div_div, div_le_iff₀ (by positivity)]
  calc (2 : ℝ) ^ (τ * n) ≤ |(m : ℝ) - S| * ((m : ℝ) + S) * η ^ 2 := h1
    _ ≤ |(m : ℝ) - S| * (4 * 2 ^ n) * 6 := by gcongr
    _ = |(m : ℝ) - S| * (2 ^ n * 24) := by ring

/-- **Explicit effective exponent for `‖2ⁿ√2‖`.**  For every `n ≥ 0` and every integer `m`,
`|2ⁿ√2 − m| ≥ 2^{-(1-τ)n} / 24` with `τ = 2^{-42}`.  Bennett–Bugeaud [BB12, Thm. 1.2] give such a
`τ` only as effectively computable. -/
@[category research solved, AMS 11, ref "BB12", group "bugeaud_10_47"]
theorem dist_ge (n : ℕ) (m : ℤ) :
    (2 : ℝ) ^ (-(1 - τ) * n) / 24 ≤ |2 ^ n * Real.sqrt 2 - m| := by
  induction n generalizing m with
  | zero =>
    rw [Nat.cast_zero, mul_zero, Real.rpow_zero, pow_zero, one_mul]
    rcases le_or_gt m 1 with h | h
    · have : (m : ℝ) ≤ 1 := by exact_mod_cast h
      rw [abs_of_pos (by linarith [sqrt2_gt])]; linarith [sqrt2_gt]
    · have : (2 : ℝ) ≤ m := by exact_mod_cast h
      rw [abs_of_neg (by linarith [sqrt2_lt])]; linarith [sqrt2_lt]
  | succ n ih =>
    have hle1 : (2 : ℝ) ^ (-(1 - τ) * ((n + 1 : ℕ) : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
        (by nlinarith [τ_le, (Nat.cast_nonneg (n + 1) : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ))])
    by_cases hbig : 1 / 2 ≤ |2 ^ (n + 1) * Real.sqrt 2 - m|
    · linarith
    push Not at hbig
    rcases Int.even_or_odd m with ⟨m', rfl⟩ | hm
    · -- `m` even: halve
      have h := ih m'
      have heq : |2 ^ (n + 1) * Real.sqrt 2 - ((m' + m' : ℤ) : ℝ)| =
          2 * |2 ^ n * Real.sqrt 2 - m'| := by
        rw [← abs_two, ← abs_mul, abs_two]; push_cast; ring_nf
      rw [heq]
      have hstep : (2 : ℝ) ^ (-(1 - τ) * ((n + 1 : ℕ) : ℝ)) ≤ 2 * 2 ^ (-(1 - τ) * (n : ℝ)) := by
        rw [show -(1 - τ) * ((n + 1 : ℕ) : ℝ) = -(1 - τ) * n + -(1 - τ) by push_cast; ring,
          Real.rpow_add two_pos]
        have : (2 : ℝ) ^ (-(1 - τ)) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith [τ_le])
        nlinarith [Real.rpow_pos_of_pos (two_pos : (0 : ℝ) < 2) (-(1 - τ) * n)]
      linarith
    · rw [abs_sub_comm] at hbig
      exact odd_case (n + 1) m hm hbig

/-! ## Runs of equal binary digits -/

lemma floor_two_mul (t : ℝ) : ⌊2 * t⌋ = 2 * ⌊t⌋ + ⌊2 * t⌋ % 2 := by
  have h1 : 2 * ⌊t⌋ ≤ ⌊2 * t⌋ := Int.le_floor.2 (by push_cast; linarith [Int.floor_le t])
  have h2 : ⌊2 * t⌋ < 2 * ⌊t⌋ + 2 :=
    Int.floor_lt.2 (by push_cast; linarith [Int.lt_floor_add_one t])
  omega

/-- **Runs.**  If the binary digits `⌊2ᵏ√2⌋ mod 2` of `√2` at positions `n + 1, …, n + L` are all
equal, then `L ≤ (1 − τ) n + 5`, with `τ = 2^{-42}`. -/
@[category research solved, AMS 11, ref "BB12", group "bugeaud_10_47"]
theorem run_le (n L : ℕ) (d : ℤ)
    (h : ∀ j, 1 ≤ j → j ≤ L → ⌊(2 : ℝ) ^ (n + j) * Real.sqrt 2⌋ % 2 = d) :
    (L : ℝ) ≤ (1 - τ) * n + 5 := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp only [CharP.cast_eq_zero]; nlinarith [τ_le, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  set F : ℕ → ℤ := fun j => ⌊(2 : ℝ) ^ (n + j) * Real.sqrt 2⌋ with hF
  have hd0 : 0 ≤ d := by rw [← h 1 le_rfl hL]; exact Int.emod_nonneg _ (by norm_num)
  have hd1 : d ≤ 1 := by
    rw [← h 1 le_rfl hL]; have := Int.emod_lt_of_pos (F 1) (by norm_num : (0 : ℤ) < 2); omega
  have hrec : ∀ j, j < L → F (j + 1) = 2 * F j + d := fun j hj => by
    have := floor_two_mul ((2 : ℝ) ^ (n + j) * Real.sqrt 2)
    rw [← mul_assoc, ← pow_succ'] at this
    show ⌊(2 : ℝ) ^ (n + (j + 1)) * Real.sqrt 2⌋ = 2 * ⌊(2 : ℝ) ^ (n + j) * Real.sqrt 2⌋ + d
    rw [← add_assoc, this, ← h (j + 1) (by omega) (by omega), ← add_assoc]
  have hFj : ∀ j, j ≤ L → F j = 2 ^ j * F 0 + d * (2 ^ j - 1) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      rw [hrec j (by omega), ih (by omega)]; ring
  have hFL := hFj L le_rfl
  -- `2ⁿ√2` lies within `2^{-L}` of the integer `F 0 + d`
  have hlo := Int.floor_le ((2 : ℝ) ^ (n + L) * Real.sqrt 2)
  have hhi := Int.lt_floor_add_one ((2 : ℝ) ^ (n + L) * Real.sqrt 2)
  have hcast : ((F L : ℤ) : ℝ) = 2 ^ L * F 0 + d * (2 ^ L - 1) := by
    rw [hFL]; push_cast; ring
  change (F L : ℝ) ≤ _ at hlo
  change _ < (F L : ℝ) + 1 at hhi
  rw [hcast, pow_add] at hlo hhi
  have hpL : (0 : ℝ) < 2 ^ L := by positivity
  have hd0' : (0 : ℝ) ≤ d := by exact_mod_cast hd0
  have hd1' : (d : ℝ) ≤ 1 := by exact_mod_cast hd1
  have hclose : |2 ^ n * Real.sqrt 2 - ((F 0 + d : ℤ) : ℝ)| ≤ 1 / 2 ^ L := by
    set y := (2 : ℝ) ^ n * Real.sqrt 2 - ((F 0 + d : ℤ) : ℝ) with hy
    have hy' : 2 ^ L * y = 2 ^ n * 2 ^ L * Real.sqrt 2 - (2 ^ L * F 0 + d * (2 ^ L - 1)) - d := by
      rw [hy]; push_cast; ring
    rw [le_div_iff₀ hpL, ← abs_of_pos hpL, ← abs_mul, mul_comm, abs_le]
    constructor <;> linarith
  have hkey := (dist_ge n (F 0 + d)).trans hclose
  -- take `log₂`
  have h24 : (2 : ℝ) ^ (-(1 - τ) * n) ≤ 2 ^ (5 - (L : ℝ)) := by
    rw [Real.rpow_sub two_pos, Real.rpow_natCast]
    have : (2 : ℝ) ^ (5 : ℝ) = 32 := by norm_num
    rw [this]
    rw [div_le_div_iff₀ (by norm_num) hpL] at hkey
    rw [le_div_iff₀ hpL]; linarith
  have := (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).1 h24
  linarith

end BB47.EffectiveSqrtTwo
