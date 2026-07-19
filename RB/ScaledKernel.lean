/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CITED.CorvajaZannierProof
import CITED.NairKumarRoutProof
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Function
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The `δ`-scaled Diophantine kernel (plan-B2A2, WP2/WP4)

**`RB.scaledViolators_finite`**: for every *rational* `δ ≠ 0` and every rational scale
`θ ∈ (0,1)`, only finitely many pairs `2 ≤ a < c` satisfy

  `‖δ·((3/2)^c − (3/2)^a)‖ ≤ θ^c`.

This is `TH.pairRepulsion_all` with the multiplier slot **opened up**: `TH` proves exactly the
`δ = 1` case (its steering word has multiplier `1`), while the orbit word of `xₙ₊₁ = ⌈3xₙ/2⌉`
needs `δ = K(x₀)` ([B2A2] §2.2's gate).  The whole file is `δ`-general, so `TH`'s statement is
the instance `δ = 1`.

## Relation to `TH` — a generalization, not a copy

[B2A2] WP2 offers two routes: generalize `TH/KernelReduction.lean` in place, or fork.  Modifying
a completed program's files is the user's call, so this file takes the **third** option: it
re-derives the dichotomy `δ`-generally in `RB/`, leaving `TH` untouched and bit-identical.  The
duplication is real but bounded (the `ℝ`-side window lemmas and the parity facts), and it buys a
strictly stronger statement.  Should the user want the consolidation, `TH.pairRepulsion_all`
can later be repointed at `scaledViolators_finite 1` — no proof would change.

## Where `δ` actually costs something

Opening the multiplier slot is *not* free; three of `TH`'s steps used `δ = 1` silently:

1. **Degeneracy.** `TH` gets `‖(3/2)^c − (3/2)^a‖ > 0` from an odd numerator over `2^c`, for
   *every* pair.  With a multiplier this fails: `δ` can cancel the `2`-power, and then the
   value **is** an integer and no Diophantine theorem applies.  `dist_pos_of_num_le` locates
   the damage exactly — `δ·((3/2)^c − (3/2)^a) ∈ ℤ` forces `2^c ∣ δ.num` (the cofactor
   `3^a(3^{c−a} − 2^{c−a})` is odd), hence `2^c ≤ |δ.num|`, hence `c < |δ.num|`.  So the
   degenerate pairs are confined to a *bounded* box and are disposed of by finiteness, not by
   parity.  This is [B2A2] §2.3's "degenerate violators" step, and it is why
   `scaledViolators_finite` needs `δ ≠ 0` and nothing else.
2. **The CZ size proviso.** `CZ.pseudoPisot_approx_of_subspace` wants `1 < |δ·q·u|`.  At
   `δ = 1` and `a ≥ 2` this is automatic; in general it holds only once `(3/2)^a > 2/|δ|`, so
   `boundedGap_slice_finite` discards an initial segment of `a` first (Archimedean, `n₁`).
3. **Rationality is the gate, not a convenience.** `δ : ℚ` is forced. Both cited theorems take
   rational coefficients, and *must*: for arbitrary real `δ` the statement is **false** — take
   `δ = Σ 2^{-xₖ}` with `x_{k+1} ≥ (1+ε)xₖ` ([B2A2] §2.2's Liouville construction).  So this
   file cannot be de-hypothesized; see `RB.RationalK` for how the hypothesis is threaded.

## The dichotomy

Unchanged from [M4A3] §6.3 route 1, modulo the above: split the (assumed infinite) violator set
by its gaps `s = c − a`.  Finitely many gaps ⇒ the CZ 2004 bounded-gap slices kill it
(`gapBounded_slice_finite`, data `δ_CZ = δ((3/2)^{s₀} − 1)`, `q = 1`, `u = (3/2)^a`).
Infinitely many gaps ⇒ one violator per gap gives a family of tuples `((3/2)^c, (3/2)^a)` with
pairwise-distinct ratios, and the repaired [NKR25] Thm 1.3(i) (`α₁ = δ`, `α₂ = −δ`) makes
`(3/2)^c` an integer — absurd.

**Axiom footprint**: std3 + `Subspace.evertseSchlickewei` (Evertse–Schlickewei, **refereed**) —
both Diophantine inputs are *derived* from that single canonical axiom
(`CITED/CorvajaZannierProof.lean`, `CITED/NairKumarRoutProof.lean`), the bespoke `CZ04` and
`NKR25` axioms having been retired on 2026-07-14.  So **nothing here is assumed on an
unrefereed preprint's authority**, notwithstanding [B1E2] T1b's "preprint lane" label, which
predates that refactor.  Ineffective, inherited from the Subspace Theorem.

## Contents

* `RB.scaledViolators` — the `δ`-scaled (K)-violating pairs at scale `θ`.
* **`RB.dist_pos_of_num_le`** — the degeneracy bound: `c ≥ |δ.num|` ⇒ `‖·‖ > 0`.
* `RB.boundedGap_slice_finite`, `RB.gapBounded_slice_finite` — the CZ slices.
* **`RB.scaledViolators_finite`** — the `δ`-general kernel.

## References

* [CZ04] Corvaja, Zannier. Acta Math. **193** (2004), 175–191. (Main Theorem, derived.)
* [NKR25] Nair, Kumar, Rout. arXiv:2506.02898 (v3, 2025, an unrefereed preprint — but *nothing
  is taken on its authority*: its Thm 1.3(i) is **false as stated** (`NKR.thm13i_unrepaired_false`)
  and is used only in the repaired form, itself **derived** from the Subspace Theorem.)
* [B2A2] `plans/plan-B2A2.html`: §2.2 (the multiplier gate), §2.3 (the rational-`K` branch), WP2/WP4.
* [M4A3] `plan-M4A3.html`: §6.2, §6.3 — the `δ = 1` templates (`TH.GapSlices`, `TH.GapDichotomy`).
-/

namespace RB

/-! ## The `δ`-scaled kernel -/

/-- The **`δ`-scaled (K)-violating pairs** at scale `θ` ([B2A2] §2.1): `2 ≤ a < c` with
`‖δ·((3/2)^c − (3/2)^a)‖ ≤ θ^c`.  At `δ = 1` this is `TH.kernelViolators`. -/
@[category API, AMS 11, ref "B2A2", group "rb_rational_base"]
def scaledViolators (δ θ : ℚ) : Set (ℕ × ℕ) :=
  {p | 2 ≤ p.1 ∧ p.1 < p.2 ∧
    (δ * ((3 / 2 : ℚ) ^ p.2 - (3 / 2 : ℚ) ^ p.1)).distToNearestInt ≤ θ ^ p.2}

/-! ## Arithmetic of the orbit difference -/

private lemma two_zpow_neg_mul_three_zpow (n : ℕ) :
    (2 : ℚ) ^ (-(n : ℤ)) * (3 : ℚ) ^ ((n : ℤ)) = (3 / 2) ^ n := by
  rw [zpow_neg, zpow_natCast, zpow_natCast, div_pow, inv_mul_eq_div]

private lemma isCoprime_two_pow_odd {O : ℤ} (hO : Odd O) (c : ℕ) :
    IsCoprime ((2 : ℤ) ^ c) O := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd]
  simp only [Int.natAbs_pow]
  exact Nat.Coprime.pow_left c (Nat.coprime_two_left.mpr (Int.natAbs_odd.mpr hO))

/-- The numerator of `(3/2)^c − (3/2)^a` over `2^c` is **odd** — this is what the multiplier
`δ` has to fight against in `dist_pos_of_num_le`. -/
private lemma odd_orbit_num (a d : ℕ) (hd : 1 ≤ d) :
    Odd ((3 : ℤ) ^ a * (3 ^ d - 2 ^ d)) := by
  refine (Odd.pow (by decide)).mul ?_
  rw [Int.odd_sub]
  exact iff_of_true (Odd.pow (by decide)) (Int.even_pow.mpr ⟨by decide, by omega⟩)

/-- `(3/2)^c − (3/2)^a = 3^a(3^{c−a} − 2^{c−a}) / 2^c` — the fraction in lowest `2`-adic terms. -/
private lemma orbit_diff_eq {a c : ℕ} (hac : a < c) :
    (3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a
      = ((3 ^ a * (3 ^ (c - a) - 2 ^ (c - a)) : ℤ) : ℚ) / (2 : ℚ) ^ c := by
  obtain ⟨d, rfl⟩ : ∃ d, c = a + d := ⟨c - a, by omega⟩
  rw [show a + d - a = d from by omega]
  push_cast
  simp only [div_pow]
  rw [pow_add]
  field_simp
  ring

/-- `(3/2)^c` is never an integer for `c ≥ 1`: `2^c·(3/2)^c = 3^c` is odd. -/
private lemma three_halves_pow_not_int {c : ℕ} (hc : 1 ≤ c) (n : ℤ)
    (h : (3 / 2 : ℚ) ^ c = n) : False := by
  have key : ((3 : ℤ) ^ c : ℚ) = ((2 ^ c * n : ℤ) : ℚ) := by
    push_cast
    rw [← h, div_pow]
    field_simp
  have keyZ : (3 : ℤ) ^ c = 2 ^ c * n := by exact_mod_cast key
  have h3 : (3 : ℤ) ^ c % 2 = 1 :=
    Int.odd_iff.mp ((Int.odd_iff.mpr (by norm_num)).pow)
  have h2 : ((2 : ℤ) ^ c * n) % 2 = 0 := by
    obtain ⟨j, rfl⟩ : ∃ j, c = j + 1 := ⟨c - 1, by omega⟩
    rw [show (2 : ℤ) ^ (j + 1) * n = 2 * (2 ^ j * n) by ring]
    exact Int.mul_emod_right 2 _
  omega

/-! ## Degeneracy: where the multiplier can cancel the `2`-power -/

/-- **The degeneracy bound** ([B2A2] §2.3, "degenerate violators"): once `c ≥ |δ.num|`, the
value `δ·((3/2)^c − (3/2)^a)` is **not** an integer, so `‖·‖ > 0` and the cited theorems apply.

At `δ = 1` (`TH`) this holds for *all* pairs by parity.  A general multiplier can cancel the
`2^c` in the denominator — but only finitely often: if the value is an integer `n` then
`δ.num·3^a(3^{c−a} − 2^{c−a}) = n·2^c·δ.den`, and since the cofactor is odd
(`odd_orbit_num`), coprimality forces `2^c ∣ δ.num`, hence `2^c ≤ |δ.num|`, hence `c < 2^c ≤
|δ.num|`.  So degeneracy is confined to `c < |δ.num|` — a bounded box, disposed of by
finiteness rather than by parity. -/
@[category research solved, AMS 11, ref "B2A2", group "rb_rational_base"]
theorem dist_pos_of_num_le {δ : ℚ} (hδ : δ ≠ 0) {a c : ℕ} (hac : a < c)
    (hc : δ.num.natAbs ≤ c) :
    0 < (δ * ((3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a)).distToNearestInt := by
  rcases (Rat.distToNearestInt_nonneg
      (δ * ((3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a))).lt_or_eq with h | h
  · exact h
  exfalso
  obtain ⟨n, hn⟩ := Rat.distToNearestInt_eq_zero_iff.mp h.symm
  have hModd : Odd ((3 : ℤ) ^ a * (3 ^ (c - a) - 2 ^ (c - a))) :=
    odd_orbit_num a (c - a) (by omega)
  rw [orbit_diff_eq hac] at hn
  have h2c : ((2 : ℚ) ^ c) ≠ 0 := by positivity
  have hmul : δ * ((3 ^ a * (3 ^ (c - a) - 2 ^ (c - a)) : ℤ) : ℚ) = (n : ℚ) * 2 ^ c := by
    field_simp at hn
    linear_combination hn
  have hden : ((δ.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr δ.den_nz
  have hq : ((δ.num * (3 ^ a * (3 ^ (c - a) - 2 ^ (c - a))) : ℤ) : ℚ)
      = ((n * 2 ^ c * δ.den : ℤ) : ℚ) := by
    push_cast
    rw [← Rat.num_div_den δ] at hmul
    field_simp at hmul
    push_cast at hmul
    linear_combination hmul
  have hZ : δ.num * (3 ^ a * (3 ^ (c - a) - 2 ^ (c - a))) = n * 2 ^ c * δ.den := by
    exact_mod_cast hq
  have hdvd : (2 : ℤ) ^ c ∣ δ.num * (3 ^ a * (3 ^ (c - a) - 2 ^ (c - a))) :=
    ⟨n * δ.den, by rw [hZ]; ring⟩
  have hdvdnum : (2 : ℤ) ^ c ∣ δ.num :=
    (isCoprime_two_pow_odd hModd c).dvd_of_dvd_mul_right hdvd
  have hnum0 : δ.num ≠ 0 := Rat.num_ne_zero.mpr hδ
  have hle : (2 : ℤ) ^ c ≤ |δ.num| :=
    Int.le_of_dvd (abs_pos.mpr hnum0) ((dvd_abs _ _).mpr hdvdnum)
  rw [Int.abs_eq_natAbs] at hle
  have hleN : (2 : ℕ) ^ c ≤ δ.num.natAbs := by exact_mod_cast hle
  have := Nat.lt_two_pow_self (n := c)
  omega

/-! ## `ℝ`-side helpers: the ε-window conversions -/

private lemma log_three_pos : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)

private lemma log_inv_pos {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) : 0 < Real.log θ⁻¹ := by
  rw [Real.log_inv]
  have := Real.log_neg hθ0 hθ1
  linarith

/-- CZ window: `θ^a < (3^a)^{-ε}` for `ε = log θ⁻¹ / (2 log 3)` and `a ≥ 1`. -/
private lemma pow_lt_rpow_neg {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {a : ℕ} (ha : 1 ≤ a) :
    θ ^ a < ((3 : ℝ) ^ a) ^ (-(Real.log θ⁻¹ / (2 * Real.log 3))) := by
  have h3 := log_three_pos
  have hlogθ : Real.log θ < 0 := Real.log_neg hθ0 hθ1
  have hpow3 : (0 : ℝ) < (3 : ℝ) ^ a := by positivity
  have hθa : (0 : ℝ) < θ ^ a := by positivity
  rw [Real.rpow_def_of_pos hpow3, ← Real.exp_log hθa, Real.log_pow, Real.log_pow,
    Real.exp_lt_exp, Real.log_inv]
  have hkey : (a : ℝ) * Real.log 3 * (-(-Real.log θ / (2 * Real.log 3)))
      = (a : ℝ) * Real.log θ / 2 := by field_simp
  rw [hkey]
  have ha' : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hneg : (a : ℝ) * Real.log θ < 0 := mul_neg_of_pos_of_neg (by linarith) hlogθ
  linarith

/-- NKR window: for `a < c`, `θ^c < (3^c·3^a)^{-ε₁}` with `ε₁ = log θ⁻¹/(2 log 3)`. -/
private lemma theta_pow_lt_height_rpow {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {a c : ℕ}
    (hac : a < c) :
    θ ^ c < (((3 ^ c * 3 ^ a : ℕ)) : ℝ) ^ (-(Real.log θ⁻¹ / (2 * Real.log 3))) := by
  have h3 := log_three_pos
  have hlogθ : Real.log θ < 0 := Real.log_neg hθ0 hθ1
  have hcast : (((3 ^ c * 3 ^ a : ℕ)) : ℝ) = (3 : ℝ) ^ c * 3 ^ a := by push_cast; ring
  have hpos : (0 : ℝ) < (3 : ℝ) ^ c * 3 ^ a := by positivity
  have hθc : (0 : ℝ) < θ ^ c := by positivity
  have hLHS : θ ^ c = Real.exp ((c : ℝ) * Real.log θ) := by
    rw [← Real.log_pow, Real.exp_log hθc]
  have hRHS : ((3 : ℝ) ^ c * 3 ^ a) ^ (-(Real.log θ⁻¹ / (2 * Real.log 3)))
      = Real.exp (((c : ℝ) * Real.log 3 + (a : ℝ) * Real.log 3)
          * (-(Real.log θ⁻¹ / (2 * Real.log 3)))) := by
    rw [Real.rpow_def_of_pos hpos]
    congr 1
    rw [Real.log_mul (by positivity : (0 : ℝ) < (3 : ℝ) ^ c).ne'
      (by positivity : (0 : ℝ) < (3 : ℝ) ^ a).ne', Real.log_pow, Real.log_pow]
  rw [hcast, hLHS, hRHS, Real.exp_lt_exp, Real.log_inv]
  have hkey : ((c : ℝ) * Real.log 3 + (a : ℝ) * Real.log 3)
      * (-(-Real.log θ / (2 * Real.log 3))) = ((c : ℝ) + a) * Real.log θ / 2 := by field_simp
  rw [hkey]
  have hca : (a : ℝ) < (c : ℝ) := by exact_mod_cast hac
  nlinarith [mul_neg_of_pos_of_neg (show (0 : ℝ) < (c : ℝ) - a by linarith) hlogθ]

/-! ## The CZ bounded-gap slices -/

/-- **The fixed-gap slice** ([B2A2] §2.3, mirroring [M4A3] §6.2): for every fixed gap `s₀ ≥ 1`,
only finitely many `a` satisfy `‖δ((3/2)^{a+s₀} − (3/2)^a)‖ ≤ θ^{a+s₀}`.

CZ data: `δ_CZ = δ·((3/2)^{s₀} − 1)`, `q = 1`, `u = (3/2)^a`, `H(u) = 3^a`.  Beyond the `δ = 1`
template, an initial segment of `a` is discarded twice over: below `n₁` the CZ size proviso
`1 < |δ_CZ·(3/2)^a|` can fail, and below `|δ.num|` the value can be an integer
(`dist_pos_of_num_le`).  Ineffective; footprint std3 + Subspace. -/
@[category research solved, AMS 11, ref "CZ04" "B2A2", group "rb_rational_base"]
theorem boundedGap_slice_finite (δ : ℚ) (hδ : δ ≠ 0) (s₀ : ℕ) (hs₀ : 1 ≤ s₀)
    (θ : ℚ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    {a : ℕ | 2 ≤ a ∧
      (δ * ((3 / 2 : ℚ) ^ (a + s₀) - (3 / 2 : ℚ) ^ a)).distToNearestInt
        ≤ θ ^ (a + s₀)}.Finite := by
  have hθ0' : (0 : ℝ) < (θ : ℝ) := by exact_mod_cast hθ0
  have hθ1' : (θ : ℝ) < 1 := by exact_mod_cast hθ1
  have hfac : (0 : ℚ) < (3 / 2 : ℚ) ^ s₀ - 1 := by
    have h1 : (3 / 2 : ℚ) ^ 1 ≤ (3 / 2 : ℚ) ^ s₀ := pow_le_pow_right₀ (by norm_num) hs₀
    rw [pow_one] at h1
    linarith
  have hδ'0 : δ * ((3 / 2 : ℚ) ^ s₀ - 1) ≠ 0 := mul_ne_zero hδ hfac.ne'
  have hεpos : 0 < Real.log (θ : ℝ)⁻¹ / (2 * Real.log 3) :=
    div_pos (log_inv_pos hθ0' hθ1') (by positivity)
  have hfin := CZ.pseudoPisot_approx_of_subspace (δ * ((3 / 2 : ℚ) ^ s₀ - 1)) hδ'0
    (Real.log (θ : ℝ)⁻¹ / (2 * Real.log 3)) hεpos
  have hδabs : (0 : ℚ) < |δ| := abs_pos.mpr hδ
  obtain ⟨n₁, hn₁⟩ := pow_unbounded_of_one_lt (2 / |δ|) (show (1 : ℚ) < 3 / 2 by norm_num)
  have hginj : Function.Injective (fun a : ℕ => ((1, -(a : ℤ), (a : ℤ)) : ℕ × ℤ × ℤ)) := by
    intro p q hpq
    simpa using hpq
  refine Set.Finite.subset
    ((Set.finite_Iio (max n₁ δ.num.natAbs)).union (hfin.preimage hginj.injOn)) ?_
  rintro a ⟨ha2, hdist⟩
  by_cases hsmall : a < max n₁ δ.num.natAbs
  · exact Or.inl hsmall
  right
  push Not at hsmall
  have hn₁le : n₁ ≤ a := le_trans (le_max_left _ _) hsmall
  have hnumle : δ.num.natAbs ≤ a := le_trans (le_max_right _ _) hsmall
  rw [Set.mem_preimage, Set.mem_setOf_eq]
  have hsval : CZ.sval (δ * ((3 / 2 : ℚ) ^ s₀ - 1)) 1 (-(a : ℤ)) (a : ℤ)
      = δ * ((3 / 2 : ℚ) ^ (a + s₀) - (3 / 2 : ℚ) ^ a) := by
    unfold CZ.sval
    rw [two_zpow_neg_mul_three_zpow]
    push_cast
    rw [pow_add]
    ring
  have hdpos : 0 < (δ * ((3 / 2 : ℚ) ^ (a + s₀) - (3 / 2 : ℚ) ^ a)).distToNearestInt :=
    dist_pos_of_num_le hδ (by omega) (by omega)
  refine ⟨le_refl 1, ?_, ?_, ?_, ?_⟩
  · -- the CZ size proviso `1 < |δ_CZ · (3/2)^a|`
    rw [hsval, show δ * ((3 / 2 : ℚ) ^ (a + s₀) - (3 / 2 : ℚ) ^ a)
        = (δ * ((3 / 2 : ℚ) ^ s₀ - 1)) * (3 / 2 : ℚ) ^ a by rw [pow_add]; ring,
      abs_mul, abs_mul]
    have hhalf : (1 / 2 : ℚ) ≤ |(3 / 2 : ℚ) ^ s₀ - 1| := by
      rw [abs_of_pos hfac]
      have h1 : (3 / 2 : ℚ) ^ 1 ≤ (3 / 2 : ℚ) ^ s₀ := pow_le_pow_right₀ (by norm_num) hs₀
      rw [pow_one] at h1
      linarith
    have hpa : 2 < |δ| * |(3 / 2 : ℚ) ^ a| := by
      rw [abs_of_pos (show (0 : ℚ) < (3 / 2 : ℚ) ^ a by positivity)]
      have h2 : (2 / |δ|) < (3 / 2 : ℚ) ^ a :=
        lt_of_lt_of_le hn₁ (pow_le_pow_right₀ (by norm_num) hn₁le)
      rw [div_lt_iff₀ hδabs] at h2
      linarith
    calc (1 : ℚ) = (1 / 2) * 2 := by norm_num
      _ < (1 / 2) * (|δ| * |(3 / 2 : ℚ) ^ a|) := by linarith
      _ ≤ |(3 / 2 : ℚ) ^ s₀ - 1| * (|δ| * |(3 / 2 : ℚ) ^ a|) :=
          mul_le_mul_of_nonneg_right hhalf (by positivity)
      _ = |δ| * |(3 / 2 : ℚ) ^ s₀ - 1| * |(3 / 2 : ℚ) ^ a| := by ring
  · rw [hsval]
    exact CZ.not_intCast_of_distToNearestInt_pos hdpos
  · rw [hsval]
    exact hdpos
  · rw [hsval, CZ.height23_neg_natCast, Nat.cast_one, Real.one_rpow, mul_one,
      show ((3 ^ a : ℕ) : ℝ) = (3 : ℝ) ^ a by push_cast; ring]
    calc ((δ * ((3 / 2 : ℚ) ^ (a + s₀) - (3 / 2 : ℚ) ^ a)).distToNearestInt : ℝ)
        ≤ ((θ ^ (a + s₀) : ℚ) : ℝ) := by exact_mod_cast hdist
      _ = (θ : ℝ) ^ (a + s₀) := by push_cast; ring
      _ ≤ (θ : ℝ) ^ a := pow_le_pow_of_le_one hθ0'.le hθ1'.le (Nat.le_add_right a s₀)
      _ < ((3 : ℝ) ^ a) ^ (-(Real.log (θ : ℝ)⁻¹ / (2 * Real.log 3))) :=
          pow_lt_rpow_neg hθ0' hθ1' (by omega)

/-- The **gap-bounded slice**: `δ`-scaled violators of gap `≤ S` are finite in number — the
union of the fixed-gap slices. -/
@[category research solved, AMS 11, ref "CZ04" "B2A2", group "rb_rational_base"]
theorem gapBounded_slice_finite (δ : ℚ) (hδ : δ ≠ 0) (S : ℕ) (θ : ℚ) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) : {p ∈ scaledViolators δ θ | p.2 ≤ p.1 + S}.Finite := by
  have hsub : {p ∈ scaledViolators δ θ | p.2 ≤ p.1 + S} ⊆
      ⋃ s₀ ∈ Finset.Icc 1 S, (fun a => (a, a + s₀)) ''
        {a : ℕ | 2 ≤ a ∧
          (δ * ((3 / 2 : ℚ) ^ (a + s₀) - (3 / 2 : ℚ) ^ a)).distToNearestInt
            ≤ θ ^ (a + s₀)} := by
    rintro ⟨a, c⟩ ⟨⟨ha, hac, hdist⟩, hgap⟩
    have hs₀ : c - a ∈ Finset.Icc 1 S := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    refine Set.mem_biUnion hs₀ ⟨a, ⟨ha, ?_⟩, ?_⟩
    · rw [show a + (c - a) = c by omega]
      exact hdist
    · simp only [Prod.mk.injEq, true_and]
      omega
  refine Set.Finite.subset ?_ hsub
  refine Set.Finite.biUnion (Finset.finite_toSet _) fun s₀ hs₀ => ?_
  exact Set.Finite.image _
    (boundedGap_slice_finite δ hδ s₀ (Finset.mem_Icc.mp hs₀).1 θ hθ0 hθ1)

/-! ## The NKR branch -/

private def enc (p : ℕ × ℕ) : (ℤ × ℤ) × (ℤ × ℤ) :=
  ((-(p.2 : ℤ), (p.2 : ℤ)), (-(p.1 : ℤ), (p.1 : ℤ)))

private lemma enc_fst_fst (p : ℕ × ℕ) : (enc p).1.1 = -(p.2 : ℤ) := rfl
private lemma enc_fst_snd (p : ℕ × ℕ) : (enc p).1.2 = (p.2 : ℤ) := rfl
private lemma enc_snd_fst (p : ℕ × ℕ) : (enc p).2.1 = -(p.1 : ℤ) := rfl
private lemma enc_snd_snd (p : ℕ × ℕ) : (enc p).2.2 = (p.1 : ℤ) := rfl

private lemma enc_injective : Function.Injective enc := by
  intro p p' h
  have h1 : ((p.2 : ℤ)) = (p'.2 : ℤ) := congrArg (fun q => q.1.2) h
  have h2 : ((p.1 : ℤ)) = (p'.1 : ℤ) := congrArg (fun q => q.2.2) h
  exact Prod.ext (by exact_mod_cast h2) (by exact_mod_cast h1)

private lemma three_halves_pow_injective :
    Function.Injective (fun n : ℕ => (3 / 2 : ℚ) ^ n) := by
  have h : StrictMono (fun n : ℕ => (3 / 2 : ℚ) ^ n) := fun m n hmn =>
    pow_lt_pow_right₀ (by norm_num) hmn
  exact h.injective

private lemma three_halves_div_pow {a c : ℕ} (hac : a ≤ c) :
    (3 / 2 : ℚ) ^ c / (3 / 2 : ℚ) ^ a = (3 / 2 : ℚ) ^ (c - a) := by
  rw [pow_sub₀ (3 / 2 : ℚ) (by norm_num) hac]
  exact div_eq_mul_inv _ _

/-- **The infinitely-many-gaps branch** ([M4A3] §6.3 route 1, `δ`-generalized): a family of
`δ`-scaled violators with pairwise-distinct gaps, all past the degeneracy box, is finite.
NKR data: `α₁ = δ`, `α₂ = −δ`, `(u₁, u₂) = ((3/2)^c, (3/2)^a)`.  Footprint std3 + Subspace. -/
private lemma finite_of_gap_injOn (δ : ℚ) (hδ : δ ≠ 0) (θ : ℚ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {T : Set (ℕ × ℕ)} (hTsub : T ⊆ scaledViolators δ θ)
    (hTnum : ∀ p ∈ T, δ.num.natAbs ≤ p.2)
    (hinj : Set.InjOn (fun p : ℕ × ℕ => p.2 - p.1) T) : T.Finite := by
  by_contra hTfin
  have hTinf : T.Infinite := hTfin
  have hθ0' : (0 : ℝ) < (θ : ℝ) := by exact_mod_cast hθ0
  have hθ1' : (θ : ℝ) < 1 := by exact_mod_cast hθ1
  have hεpos : 0 < Real.log (θ : ℝ)⁻¹ / (2 * Real.log 3) :=
    div_pos (log_inv_pos hθ0' hθ1') (by positivity)
  -- the value slot: `δ·u₁ + (−δ)·u₂ = δ·((3/2)^c − (3/2)^a)`
  have hval : ∀ p : ℕ × ℕ,
      δ * NKR.uval (enc p).1.1 (enc p).1.2 + (-δ) * NKR.uval (enc p).2.1 (enc p).2.2
        = δ * ((3 / 2 : ℚ) ^ p.2 - (3 / 2 : ℚ) ^ p.1) := by
    intro p
    simp only [enc_fst_fst, enc_fst_snd, enc_snd_fst, enc_snd_snd, NKR.uval_neg_natCast]
    ring
  have habs : ∀ q ∈ enc '' T,
      1 ≤ |NKR.uval q.1.1 q.1.2| ∧ 1 ≤ |NKR.uval q.2.1 q.2.2| := by
    rintro q ⟨p, -, rfl⟩
    simp only [enc_fst_fst, enc_fst_snd, enc_snd_fst, enc_snd_snd, NKR.uval_neg_natCast]
    rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
    exact ⟨one_le_pow₀ (by norm_num), one_le_pow₀ (by norm_num)⟩
  have hP2 : ∀ q ∈ enc '' T, NKR.uval q.1.1 q.1.2 ≠ -NKR.uval q.2.1 q.2.2 := by
    rintro q ⟨p, -, rfl⟩
    simp only [enc_fst_fst, enc_fst_snd, enc_snd_fst, enc_snd_snd, NKR.uval_neg_natCast]
    have h1 : (0 : ℚ) < (3 / 2 : ℚ) ^ p.2 := by positivity
    have h2 : (0 : ℚ) < (3 / 2 : ℚ) ^ p.1 := by positivity
    intro h
    rw [h] at h1
    linarith
  have hratio : ∀ q ∈ enc '' T, ∀ q' ∈ enc '' T, q ≠ q' →
      NKR.uval q.1.1 q.1.2 / NKR.uval q.2.1 q.2.2
        ≠ NKR.uval q'.1.1 q'.1.2 / NKR.uval q'.2.1 q'.2.2 ∧
      NKR.uval q.2.1 q.2.2 / NKR.uval q.1.1 q.1.2
        ≠ NKR.uval q'.2.1 q'.2.2 / NKR.uval q'.1.1 q'.1.2 := by
    rintro q ⟨p, hpT, rfl⟩ q' ⟨p', hp'T, rfl⟩ hqq'
    have hpp' : p ≠ p' := fun h => hqq' (congrArg enc h)
    obtain ⟨-, hac, -⟩ := hTsub hpT
    obtain ⟨-, hac', -⟩ := hTsub hp'T
    have hgap : p.2 - p.1 ≠ p'.2 - p'.1 := fun h => hpp' (hinj hpT hp'T h)
    have hne : (3 / 2 : ℚ) ^ (p.2 - p.1) ≠ (3 / 2 : ℚ) ^ (p'.2 - p'.1) :=
      fun h => hgap (three_halves_pow_injective h)
    simp only [enc_fst_fst, enc_fst_snd, enc_snd_fst, enc_snd_snd, NKR.uval_neg_natCast]
    refine ⟨?_, ?_⟩
    · rw [three_halves_div_pow hac.le, three_halves_div_pow hac'.le]
      exact hne
    · intro h
      apply hne
      have h' := congrArg (·⁻¹) h
      simp only [inv_div] at h'
      rwa [three_halves_div_pow hac.le, three_halves_div_pow hac'.le] at h'
  have hposd : ∀ q ∈ enc '' T,
      0 < (δ * NKR.uval q.1.1 q.1.2 + (-δ) * NKR.uval q.2.1 q.2.2).distToNearestInt := by
    rintro q ⟨p, hpT, rfl⟩
    obtain ⟨ha2, hac, -⟩ := hTsub hpT
    rw [hval p]
    exact dist_pos_of_num_le hδ hac (hTnum p hpT)
  have happrox : ∀ q ∈ enc '' T,
      ((δ * NKR.uval q.1.1 q.1.2 + (-δ) * NKR.uval q.2.1 q.2.2).distToNearestInt : ℝ)
        < ((CZ.height23 q.1.1 q.1.2 * CZ.height23 q.2.1 q.2.2 : ℕ) : ℝ)
            ^ (-(Real.log (θ : ℝ)⁻¹ / (2 * Real.log 3))) := by
    rintro q ⟨p, hpT, rfl⟩
    obtain ⟨ha2, hac, hdist⟩ := hTsub hpT
    rw [hval p]
    simp only [enc_fst_fst, enc_fst_snd, enc_snd_fst, enc_snd_snd, CZ.height23_neg_natCast]
    calc ((δ * ((3 / 2 : ℚ) ^ p.2 - (3 / 2 : ℚ) ^ p.1)).distToNearestInt : ℝ)
        ≤ ((θ ^ p.2 : ℚ) : ℝ) := by exact_mod_cast hdist
      _ = (θ : ℝ) ^ p.2 := by push_cast; ring
      _ < _ := theta_pow_lt_height_rpow hθ0' hθ1' hac
  obtain ⟨q, hq𝒩, ⟨n, hn⟩, -⟩ := NKR.sUnit_pair_integrality_of_subspace δ (-δ) hδ
    (neg_ne_zero.mpr hδ) (Real.log (θ : ℝ)⁻¹ / (2 * Real.log 3)) hεpos (enc '' T)
    (hTinf.image enc_injective.injOn) habs hP2 hratio hposd happrox
  obtain ⟨p, hpT, rfl⟩ := hq𝒩
  obtain ⟨ha2, hac, -⟩ := hTsub hpT
  rw [enc_fst_fst, enc_fst_snd, NKR.uval_neg_natCast] at hn
  exact three_halves_pow_not_int (by omega) n hn

/-! ## The `δ`-general kernel -/

/-- **The `δ`-scaled kernel** ([B2A2] §2.3): for every rational `δ ≠ 0` and every rational
scale `θ ∈ (0,1)`, only finitely many pairs `2 ≤ a < c` satisfy
`‖δ·((3/2)^c − (3/2)^a)‖ ≤ θ^c`.

`TH.pairRepulsion_all` is the case `δ = 1`.  The proof splits three ways: the degeneracy box
`c < |δ.num|` (finite outright, [B2A2] §2.3), bounded gaps (CZ 2004 slices), and unbounded gaps
(the repaired [NKR25] pair theorem at `α₁ = δ`, `α₂ = −δ`).

Ineffective (Subspace).  Footprint: std3 + `Subspace.evertseSchlickewei` (**refereed**), via
`CZ.pseudoPisot_approx_of_subspace` and `NKR.sUnit_pair_integrality_of_subspace` — both derived,
neither assumed.  No preprint dependency; see the module doc. -/
@[category research solved, AMS 11, ref "CZ04" "NKR25" "B2A2", group "rb_rational_base"]
theorem scaledViolators_finite (δ : ℚ) (hδ : δ ≠ 0) (θ : ℚ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (scaledViolators δ θ).Finite := by
  -- past the degeneracy box, `‖·‖ > 0`; inside it, there is nothing to prove
  have hsplit : scaledViolators δ θ ⊆
      {p ∈ scaledViolators δ θ | δ.num.natAbs ≤ p.2} ∪
        (Set.Iio δ.num.natAbs ×ˢ Set.Iio δ.num.natAbs) := by
    rintro p hp
    by_cases h : δ.num.natAbs ≤ p.2
    · exact Or.inl ⟨hp, h⟩
    · obtain ⟨-, hac, -⟩ := hp
      exact Or.inr (Set.mem_prod.mpr ⟨Set.mem_Iio.mpr (by omega), Set.mem_Iio.mpr (by omega)⟩)
  refine Set.Finite.subset (Set.Finite.union ?_
    ((Set.finite_Iio _).prod (Set.finite_Iio _))) hsplit
  -- the gap dichotomy on the non-degenerate part
  by_contra hVfin
  have hVinf : {p ∈ scaledViolators δ θ | δ.num.natAbs ≤ p.2}.Infinite := hVfin
  set V : Set (ℕ × ℕ) := {p ∈ scaledViolators δ θ | δ.num.natAbs ≤ p.2} with hVdef
  set gap : ℕ × ℕ → ℕ := fun p => p.2 - p.1 with hgapdef
  by_cases hg : (gap '' V).Finite
  · -- bounded gaps: the CZ slice
    obtain ⟨S, hS⟩ := hg.bddAbove
    apply hVinf
    apply Set.Finite.subset (gapBounded_slice_finite δ hδ S θ hθ0 hθ1)
    intro p hp
    refine ⟨hp.1, ?_⟩
    have h1 := hS (Set.mem_image_of_mem gap hp)
    obtain ⟨-, hac, -⟩ := hp.1
    have h2 : gap p = p.2 - p.1 := rfl
    omega
  · -- unbounded gaps: a gap-injective section, then NKR
    have hginf : (gap '' V).Infinite := hg
    have hsec : ∀ y ∈ gap '' V, ∃ a ∈ V, gap a = y := by
      rintro y ⟨p, hp, rfl⟩
      exact ⟨p, hp, rfl⟩
    have hgapinv : ∀ y ∈ gap '' V, gap (Function.invFunOn gap V y) = y :=
      fun y hy => Function.invFunOn_eq (hsec y hy)
    have hTsub : Function.invFunOn gap V '' (gap '' V) ⊆ V := by
      rintro t ⟨y, hy, rfl⟩
      exact Function.invFunOn_mem (hsec y hy)
    have hinvinj : Set.InjOn (Function.invFunOn gap V) (gap '' V) := by
      intro y1 hy1 y2 hy2 h
      rw [← hgapinv y1 hy1, ← hgapinv y2 hy2, h]
    have hTinf : (Function.invFunOn gap V '' (gap '' V)).Infinite := hginf.image hinvinj
    have hinjT : Set.InjOn gap (Function.invFunOn gap V '' (gap '' V)) := by
      rintro t1 ⟨y1, hy1, rfl⟩ t2 ⟨y2, hy2, rfl⟩ h
      rw [hgapinv y1 hy1, hgapinv y2 hy2] at h
      rw [h]
    exact hTinf (finite_of_gap_injOn δ hδ θ hθ0 hθ1
      (fun p hp => (hTsub hp).1) (fun p hp => (hTsub hp).2) hinjT)

end RB
