/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import RB.Cocycle
import CITED.CorvajaZannierProof
import CITED.NairKumarRoutProof
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Function
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The cocycle kernel and the divergent-Collatz class theorem (plan-B2A2, WP8 / T3b)

The Diophantine half of [B2A2] §3.2, and the capstone the plan is named for:

> **`RB.Collatz.divergent_superlinear_of_geometric_ratK`** — a uniformly geometrically divergent
> Collatz orbit whose cocycle constant is **rational** has **superlinear** parity-word
> complexity, hence (Cobham) a **non-automatic** parity word.

This is the first statement of any kind putting divergent Collatz orbits and superlinear
complexity in one theorem.  Its two inputs are `RB/Cocycle.lean`'s violator
(`dist_le_of_repetition`) and the `S`-unit kernel below.

## The kernel, and how it differs from the model's

`RB.scaledViolators_finite` ([B2A2] §2.3) kills pairs `‖δ((3/2)^c − (3/2)^a)‖ ≤ θ^c`.  Here the
`S`-units are the cocycles `Λₙ = 3^{Sₙ}/2ⁿ` — **arbitrary** members of `⟨2,3⟩`, since the odd-step
counts `Sₙ` are not `n`.  That is exactly the generality [CZ04]/[NKR25] are stated in (their
exponent pairs `(x,y)` are free), so no new Diophantine input is needed — but the bookkeeping
changes in three places, which is the "fiddly new part" WP8 predicted:

1. **The dichotomy is on the ratio value, not the gap.**  `Λ_c/Λ_a = 2^{a−c}3^{S_c−S_a}` is no
   longer determined by `c − a`, so the split is: finitely many ratio *values* (each fibre killed
   by a CZ slice at `δ_CZ = δ(r−1)`, `u = Λ_a`) versus infinitely many (a ratio-injective section,
   killed by NKR at `α₁ = δ`, `α₂ = −δ`, `(u₁,u₂) = (Λ_c, Λ_a)`).
2. **A fixed-`a` strip has to be disposed of separately** (`oneTerm_slice_finite`).  NKR needs
   `1 ≤ |uᵢ|`, and `Λ_a < 1` is possible for small `a`.  For fixed `a` the inhomogeneous condition
   `‖δΛ_c − δΛ_a‖ ≤ Aθ^c` clears its denominator to the *one-term* condition `‖δ'Λ_c‖ ≤ A'θ^c`
   (`δ' = den(δΛ_a)·δ`), which CZ kills outright.
3. **Degeneracy is the same odd-numerator argument** as [B2A2] §2.3's: `2^c(Λ_c − Λ_a)` is the odd
   integer `3^{S_c} − 3^{S_a}2^{c−a}`, so `δ(Λ_c − Λ_a) ∈ ℤ` forces `2^c ∣ δ.num`, confining
   degenerate pairs to `c < |δ.num|`.

The absurdity at the end of the NKR branch is `Λ_c ∈ ℤ`, i.e. `2^c ∣ 3^{S_c}` — the exact
analogue of "`(3/2)^c` is an integer".

## Honest scope — read this before quoting the capstone

* **Two hypotheses, both restrictive.**  *Uniform* geometric divergence is strictly stronger than
  [B2A2] §3.2's liminf form (`RB/Cocycle.lean`'s module doc explains why the liminf form cannot
  work: the defect `θ` need not even be bounded), and a numerically typical divergent orbit —
  with even-runs of length `≍ log n` — fails it.  Rationality of the cocycle constant `K` is the
  same gate as [B2A2] §2.2's, and equally unavailable: the contrapositive reads as an
  *irrationality criterion* for `K` of a hypothetical divergent orbit.
* **This is not progress on the `3x+1` conjecture**, nor on the unconditional A.2 (T3c).  A
  divergent orbit is not known to exist; if one does, neither hypothesis is known to hold for it.
  Indeed **under the `3x+1` conjecture the hypothesis class is empty** — every orbit enters the
  cycle `1 → 2 → 1`, where `Λ` stops growing — so the theorem is conditionally vacuous, exactly
  as `RB.not_automatic_of_K_algebraic` is under the expected transcendence of `K`.  What it
  delivers is the *architecture*: the transfer of the `(3/2)ⁿ` kernel to genuine Collatz parity
  words, with every step of the reduction formalized and the hypotheses named honestly.
* The rate-based route to the *unconditional* statement stays closed by `RB.not_demand`
  (`RB/NoStammeringRoute.lean`); see [B2A2] §0's do-not-reattempt guard.

**Axiom footprint**: std3 + `Subspace.evertseSchlickewei` (Evertse–Schlickewei, **refereed**),
inherited through `CZ.pseudoPisot_approx_of_subspace` and
`NKR.sUnit_pair_integrality_of_subspace` — both *derived*, neither assumed.  Ineffective.

## Contents

* `RB.Collatz.cocycleViolators` — the `S`-unit violating pairs of the cocycle.
* `RB.Collatz.oneTerm_slice_finite`, `fixedRatio_slice_finite` — the two CZ slices.
* **`RB.Collatz.cocycleViolators_finite`** — the cocycle kernel.
* **`RB.Collatz.divergent_superlinear_of_geometric_ratK`** — T3b, the class theorem.
* **`RB.Collatz.not_automatic_of_geometric_ratK`** — its Cobham corollary, and
  `covering_superlinear_of_geometric_ratK` in the WP7 residue-covering language.

## References

* [B2A2] `plans/plan-B2A2.html`: §3.2 (this file), WP8 / T3b, milestone M4.
* [CZ04] Corvaja, Zannier. Acta Math. **193** (2004), 175–191 (Main Theorem, derived).
* [NKR25] Nair, Kumar, Rout. arXiv:2506.02898 (Thm 1.3(i), **repaired** and derived).
* [Cob72] A. Cobham. Math. Systems Theory **6** (1972), 164–192; [AS03] Allouche–Shallit.
* [Dub09] A. Dubickas. Glasgow Math. J. **51** (2009), 243–252.
-/

namespace RB.Collatz

open CC ForMathlib.SubwordComplexity

/-! ## The cocycle as an `S`-unit -/

/-- The cocycle in the exponent encoding of the Diophantine engines: `Λₙ = 2^{−n}·3^{Sₙ}`. -/
@[category API, AMS 11, ref "B2A2", group "rb_collatz_cocycle"]
lemma cocycle_eq_uval (n₀ n : ℕ) :
    cocycle n₀ n = NKR.uval (-(n : ℤ)) (sOdd n₀ n) := by
  unfold cocycle NKR.uval
  rw [zpow_neg, zpow_natCast, zpow_natCast]
  field_simp

/-- The same, in the `CZ` value slot at `q = 1`. -/
@[category API, AMS 11, ref "B2A2", group "rb_collatz_cocycle"]
lemma sval_eq_cocycle (δ' : ℚ) (n₀ n : ℕ) :
    CZ.sval δ' 1 (-(n : ℤ)) (sOdd n₀ n) = δ' * cocycle n₀ n := by
  unfold CZ.sval
  rw [cocycle_eq_uval]
  unfold NKR.uval
  push_cast
  ring

/-- The height of `Λₙ` is at most `3ⁿ`: `H(2^{−n}3^{Sₙ}) = max(3^{Sₙ}, 2ⁿ) ≤ 3ⁿ` since
`Sₙ ≤ n`. -/
@[category API, AMS 11, ref "B2A2", group "rb_collatz_cocycle"]
lemma height23_cocycle_le (n₀ n : ℕ) :
    CZ.height23 (-(n : ℤ)) (sOdd n₀ n) ≤ 3 ^ n := by
  have h1 : (-(n : ℤ)).toNat = 0 := Int.toNat_of_nonpos (by omega)
  have h2 : ((sOdd n₀ n : ℤ)).toNat = sOdd n₀ n := Int.toNat_natCast _
  have h3 : (-(-(n : ℤ))).toNat = n := by rw [neg_neg]; exact Int.toNat_natCast _
  have h4 : (-((sOdd n₀ n : ℤ))).toNat = 0 := Int.toNat_of_nonpos (by omega)
  unfold CZ.height23
  rw [h1, h2, h3, h4, pow_zero, pow_zero, one_mul, mul_one]
  exact max_le (Nat.pow_le_pow_right (by norm_num) (num_odd_steps_le n n₀))
    (Nat.pow_le_pow_left (by norm_num) n)

@[category API, AMS 11, ref "B2A2", group "rb_collatz_cocycle"]
lemma one_le_height23_cocycle (n₀ n : ℕ) : 1 ≤ CZ.height23 (-(n : ℤ)) (sOdd n₀ n) := by
  unfold CZ.height23
  exact le_max_of_le_left (Nat.one_le_iff_ne_zero.mpr (by positivity))

/-- `2ⁿ·Λₙ = 3^{Sₙ}` is an **odd** integer — the numerator that the multiplier `δ` has to fight
in the degeneracy step. -/
@[category API, AMS 11, ref "B2A2", group "rb_collatz_cocycle"]
lemma two_pow_mul_cocycle (n₀ n : ℕ) :
    (2 : ℚ) ^ n * cocycle n₀ n = ((3 ^ sOdd n₀ n : ℤ) : ℚ) := by
  unfold cocycle
  push_cast
  field_simp

/-- `2^c·(Λ_c − Λ_a) = 3^{S_c} − 3^{S_a}2^{c−a}` is an **odd** integer for `a < c`. -/
@[category API, AMS 11, ref "B2A2", group "rb_collatz_cocycle"]
lemma two_pow_mul_cocycle_sub {n₀ a c : ℕ} (hac : a < c) :
    (2 : ℚ) ^ c * (cocycle n₀ c - cocycle n₀ a)
      = ((3 ^ sOdd n₀ c - 3 ^ sOdd n₀ a * 2 ^ (c - a) : ℤ) : ℚ) := by
  unfold cocycle
  obtain ⟨d, rfl⟩ : ∃ d, c = a + d := ⟨c - a, by omega⟩
  rw [show a + d - a = d from by omega]
  push_cast
  rw [pow_add]
  field_simp

@[category API, AMS 11, ref "B2A2", group "rb_collatz_cocycle"]
lemma odd_cocycle_num (n₀ n : ℕ) : Odd ((3 : ℤ) ^ sOdd n₀ n) := Odd.pow (by decide)

@[category API, AMS 11, ref "B2A2", group "rb_collatz_cocycle"]
lemma odd_cocycle_sub_num {n₀ a c : ℕ} (hac : a < c) :
    Odd ((3 ^ sOdd n₀ c - 3 ^ sOdd n₀ a * 2 ^ (c - a) : ℤ)) := by
  rw [Int.odd_sub]
  refine iff_of_true (Odd.pow (by decide)) ?_
  exact (Int.even_pow.mpr ⟨by decide, by omega⟩).mul_left _

/-- The cocycle is **injective**: its `2`-adic denominator is `2ⁿ`. -/
@[category API, AMS 11, ref "B2A2", group "rb_collatz_cocycle"]
lemma cocycle_injective (n₀ : ℕ) : Function.Injective (cocycle n₀) := by
  have key : ∀ n m : ℕ, n < m → cocycle n₀ n ≠ cocycle n₀ m := by
    intro n m hnm heq
    obtain ⟨d, rfl⟩ : ∃ d, m = n + d := ⟨m - n, by omega⟩
    have hd : 1 ≤ d := by omega
    have hQ : (3 : ℚ) ^ sOdd n₀ n * 2 ^ (n + d) = 3 ^ sOdd n₀ (n + d) * 2 ^ n := by
      unfold cocycle at heq
      have h1 : ((2 : ℚ) ^ n) ≠ 0 := by positivity
      have h2 : ((2 : ℚ) ^ (n + d)) ≠ 0 := by positivity
      field_simp at heq
      linarith [heq]
    have hN : (3 : ℕ) ^ sOdd n₀ n * 2 ^ (n + d) = 3 ^ sOdd n₀ (n + d) * 2 ^ n := by
      exact_mod_cast hQ
    have hcancel : (3 : ℕ) ^ sOdd n₀ n * 2 ^ d = 3 ^ sOdd n₀ (n + d) := by
      have h2 : (0 : ℕ) < 2 ^ n := by positivity
      refine Nat.eq_of_mul_eq_mul_right h2 ?_
      calc 3 ^ sOdd n₀ n * 2 ^ d * 2 ^ n = 3 ^ sOdd n₀ n * 2 ^ (n + d) := by
            rw [pow_add]; ring
        _ = 3 ^ sOdd n₀ (n + d) * 2 ^ n := hN
    have hodd : ¬ (2 ∣ (3 : ℕ) ^ sOdd n₀ (n + d)) := by
      intro hdvd
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdvd
      omega
    exact hodd (hcancel ▸ Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) _)
  intro n m hnm
  rcases lt_trichotomy n m with h | h | h
  · exact absurd hnm (key n m h)
  · exact h
  · exact absurd hnm.symm (key m n h)

/-- `Λ_c` is never an integer for `c ≥ 1` — the absurdity at the end of the NKR branch. -/
@[category API, AMS 11, ref "B2A2", group "rb_collatz_cocycle"]
lemma cocycle_not_intCast {n₀ c : ℕ} (hc : 1 ≤ c) (z : ℤ) : cocycle n₀ c ≠ (z : ℚ) := by
  intro heq
  have h : ((3 ^ sOdd n₀ c : ℤ) : ℚ) = ((2 ^ c * z : ℤ) : ℚ) := by
    rw [← two_pow_mul_cocycle, heq]
    push_cast
    ring
  have hZ : (3 : ℤ) ^ sOdd n₀ c = 2 ^ c * z := by exact_mod_cast h
  have h3 : (3 : ℤ) ^ sOdd n₀ c % 2 = 1 := Int.odd_iff.mp (odd_cocycle_num n₀ c)
  have h2 : ((2 : ℤ) ^ c * z) % 2 = 0 := by
    obtain ⟨j, rfl⟩ : ∃ j, c = j + 1 := ⟨c - 1, by omega⟩
    rw [show (2 : ℤ) ^ (j + 1) * z = 2 * (2 ^ j * z) by ring]
    exact Int.mul_emod_right 2 _
  omega

/-! ## Degeneracy: the odd-numerator repulsion -/

/-- **The degeneracy bound** ([B2A2] §2.3, `S`-unit form; generalizes `RB.dist_pos_of_num_le`):
if `2^c·v = δ·O` with `O` odd and `c ≥ |δ.num|`, then `v` is not an integer.  Otherwise
`δ.num·O = z·2^c·δ.den`, and coprimality of `2^c` with the odd `O` forces `2^c ∣ δ.num`, hence
`c < 2^c ≤ |δ.num|`. -/
@[category research solved, AMS 11, ref "B2A2", group "rb_collatz_cocycle"]
theorem dist_pos_of_odd_num {δ : ℚ} (hδ : δ ≠ 0) {O : ℤ} (hO : Odd O) {c : ℕ} {v : ℚ}
    (hv : (2 : ℚ) ^ c * v = δ * (O : ℚ)) (hc : δ.num.natAbs ≤ c) :
    0 < v.distToNearestInt := by
  rcases (Rat.distToNearestInt_nonneg v).lt_or_eq with h | h
  · exact h
  exfalso
  obtain ⟨z, hz⟩ := Rat.distToNearestInt_eq_zero_iff.mp h.symm
  have hcop : IsCoprime ((2 : ℤ) ^ c) O := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd]
    simp only [Int.natAbs_pow]
    exact Nat.Coprime.pow_left c (Nat.coprime_two_left.mpr (Int.natAbs_odd.mpr hO))
  have hden : ((δ.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr δ.den_nz
  have hq : ((δ.num * O : ℤ) : ℚ) = ((z * 2 ^ c * δ.den : ℤ) : ℚ) := by
    push_cast
    rw [← Rat.num_div_den δ] at hv
    rw [hz] at hv
    field_simp at hv
    linear_combination (-1 : ℚ) * hv
  have hZ : δ.num * O = z * 2 ^ c * δ.den := by exact_mod_cast hq
  have hdvd : (2 : ℤ) ^ c ∣ δ.num * O := ⟨z * δ.den, by rw [hZ]; ring⟩
  have hdvdnum : (2 : ℤ) ^ c ∣ δ.num := hcop.dvd_of_dvd_mul_right hdvd
  have hnum0 : δ.num ≠ 0 := Rat.num_ne_zero.mpr hδ
  have hle : (2 : ℤ) ^ c ≤ |δ.num| :=
    Int.le_of_dvd (abs_pos.mpr hnum0) ((dvd_abs _ _).mpr hdvdnum)
  rw [Int.abs_eq_natAbs] at hle
  have hleN : (2 : ℕ) ^ c ≤ δ.num.natAbs := by exact_mod_cast hle
  have := Nat.lt_two_pow_self (n := c)
  omega

/-! ## The `ε`-window -/

private noncomputable def eps (θ : ℚ) : ℝ := Real.log (θ : ℝ)⁻¹ / (4 * Real.log 3)

private lemma eps_pos {θ : ℚ} (hθ0 : 0 < θ) (hθ1 : θ < 1) : 0 < eps θ := by
  have hθ0' : (0 : ℝ) < (θ : ℝ) := by exact_mod_cast hθ0
  have hθ1' : (θ : ℝ) < 1 := by exact_mod_cast hθ1
  have hlog : Real.log (θ : ℝ) < 0 := Real.log_neg hθ0' hθ1'
  have h3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  unfold eps
  rw [Real.log_inv]
  exact div_pos (by linarith) (by positivity)

/-- **The window lemma**: past a threshold, the geometric quality `A·θⁿ` beats the Diophantine
threshold `H^{-ε}` for every height `H ≤ 3^{2n}`.  This is the `S`-unit-general form of
`RB.ScaledKernel`'s `pow_lt_rpow_neg`/`theta_pow_lt_height_rpow` pair: `ε = log θ⁻¹/(4 log 3)`
makes `(3^{2n})^{-ε} = exp(−nL/2)` while `A·θⁿ = exp(log A − nL)`, `L = log θ⁻¹ > 0`. -/
private lemma exists_window (A θ : ℚ) (hA : 0 < A) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ H : ℕ, 1 ≤ H → H ≤ 3 ^ (2 * n) →
      ((A : ℝ) * (θ : ℝ) ^ n) < (H : ℝ) ^ (-eps θ) := by
  have hθ0' : (0 : ℝ) < (θ : ℝ) := by exact_mod_cast hθ0
  have hθ1' : (θ : ℝ) < 1 := by exact_mod_cast hθ1
  have hA' : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have h3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  set L : ℝ := Real.log (θ : ℝ)⁻¹ with hL
  have hLpos : 0 < L := by
    rw [hL, Real.log_inv]
    have := Real.log_neg hθ0' hθ1'
    linarith
  have hlogθ : Real.log (θ : ℝ) = -L := by rw [hL, Real.log_inv, neg_neg]
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * Real.log (A : ℝ) / L)
  refine ⟨N, fun n hn H hH1 hHle => ?_⟩
  have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogA : Real.log (A : ℝ) < (n : ℝ) * L / 2 := by
    have h1 : 2 * Real.log (A : ℝ) / L < (n : ℝ) := lt_of_lt_of_le hN hn'
    rw [div_lt_iff₀ hLpos] at h1
    linarith
  -- the left side as an exponential
  have hpow : (θ : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log (θ : ℝ)) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  have hLHS : (A : ℝ) * (θ : ℝ) ^ n = Real.exp (Real.log (A : ℝ) - n * L) := by
    rw [hpow, hlogθ, Real.exp_sub, Real.exp_log hA',
      show (n : ℝ) * -L = -((n : ℝ) * L) by ring, Real.exp_neg, div_eq_mul_inv]
  -- the right side, bounded below via the height ceiling
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH1
  have hRHS : (H : ℝ) ^ (-eps θ) = Real.exp (-eps θ * Real.log (H : ℝ)) := by
    rw [Real.rpow_def_of_pos hHpos, mul_comm]
  have hlogH : Real.log (H : ℝ) ≤ 2 * n * Real.log 3 := by
    have hcast : ((H : ℕ) : ℝ) ≤ ((3 ^ (2 * n) : ℕ) : ℝ) := by exact_mod_cast hHle
    have := Real.log_le_log hHpos hcast
    rwa [show ((3 ^ (2 * n) : ℕ) : ℝ) = (3 : ℝ) ^ (2 * n) by push_cast; ring,
      Real.log_pow, show ((2 * n : ℕ) : ℝ) = 2 * n by push_cast; ring] at this
  have hεpos : 0 < eps θ := eps_pos hθ0 hθ1
  have h3ne : Real.log 3 ≠ 0 := ne_of_gt h3
  have hkey : -eps θ * (2 * n * Real.log 3) = -((n : ℝ) * L / 2) := by
    rw [hL]
    unfold eps
    field_simp
    ring
  have hcomp : Real.log (A : ℝ) - n * L < -eps θ * Real.log (H : ℝ) := by
    have h1 : -eps θ * Real.log (H : ℝ) ≥ -eps θ * (2 * n * Real.log 3) := by
      have := mul_le_mul_of_nonneg_left hlogH (le_of_lt hεpos)
      linarith
    rw [hkey] at h1
    linarith
  rw [hLHS, hRHS]
  exact Real.exp_lt_exp.mpr hcomp

/-! ## The violating pairs -/

/-- **The cocycle violators** ([B2A2] §3.2): pairs `a < c` with
`‖δ·(Λ_c − Λ_a)‖ ≤ A·θ^c`. -/
@[category API, AMS 11, ref "B2A2", group "rb_collatz_cocycle"]
def cocycleViolators (n₀ : ℕ) (δ A θ : ℚ) : Set (ℕ × ℕ) :=
  {p | p.1 < p.2 ∧ (δ * (cocycle n₀ p.2 - cocycle n₀ p.1)).distToNearestInt ≤ A * θ ^ p.2}

/-! ## Slice 1: the one-term (fixed-`a`) kernel -/

/-- **The one-term slice**: for a rational `δ' ≠ 0`, only finitely many `c` satisfy
`‖δ'·Λ_c‖ ≤ A·θ^c`.  CZ data: `q = 1`, `u = Λ_c = 2^{−c}3^{S_c}`, `H(u) ≤ 3^c`.  Beyond the
degeneracy box `c < |δ'.num|` and the CZ size proviso `1 < |δ'Λ_c|` (both initial segments, since
`Λ_c → ∞`), this is a direct application. -/
@[category research solved, AMS 11, ref "CZ04" "B2A2", group "rb_collatz_cocycle"]
theorem oneTerm_slice_finite {n₀ : ℕ} {ρ B₀ : ℚ} (hgeo : IsUniformlyGeometric n₀ ρ B₀)
    {δ' A θ : ℚ} (hδ' : δ' ≠ 0) (hA : 0 < A) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    {c : ℕ | (δ' * cocycle n₀ c).distToNearestInt ≤ A * θ ^ c}.Finite := by
  obtain ⟨Nw, hNw⟩ := exists_window A θ hA hθ0 hθ1
  obtain ⟨Ns, hNs⟩ := exists_le_cocycle hgeo (2 / |δ'|)
  have hδabs : (0 : ℚ) < |δ'| := abs_pos.mpr hδ'
  have hfin := CZ.pseudoPisot_approx_of_subspace δ' hδ' (eps θ) (eps_pos hθ0 hθ1)
  have hginj : Function.Injective (fun c : ℕ => ((1, -(c : ℤ), (sOdd n₀ c : ℤ)) : ℕ × ℤ × ℤ)) := by
    intro p q hpq
    have h := congrArg (fun t : ℕ × ℤ × ℤ => t.2.1) hpq
    simp only at h
    omega
  set N := max (max Nw Ns) δ'.num.natAbs with hN
  refine Set.Finite.subset ((Set.finite_Iio N).union (hfin.preimage hginj.injOn)) ?_
  intro c hc
  by_cases hsmall : c < N
  · exact Or.inl hsmall
  right
  push Not at hsmall
  have hcw : Nw ≤ c := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hsmall
  have hcs : Ns ≤ c := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hsmall
  have hcn : δ'.num.natAbs ≤ c := le_trans (le_max_right _ _) hsmall
  have hdist : (δ' * cocycle n₀ c).distToNearestInt ≤ A * θ ^ c := hc
  have hdpos : 0 < (δ' * cocycle n₀ c).distToNearestInt := by
    refine dist_pos_of_odd_num (c := c) hδ' (odd_cocycle_num n₀ c) ?_ hcn
    rw [show (2 : ℚ) ^ c * (δ' * cocycle n₀ c) = δ' * ((2 : ℚ) ^ c * cocycle n₀ c) by ring,
      two_pow_mul_cocycle]
  rw [Set.mem_preimage, Set.mem_setOf_eq]
  refine ⟨le_refl 1, ?_, ?_, ?_, ?_⟩
  · rw [sval_eq_cocycle]
    have hΛ := hNs c hcs
    have hΛpos := cocycle_pos n₀ c
    rw [abs_mul, abs_of_pos hΛpos]
    rw [div_le_iff₀ hδabs] at hΛ
    linarith
  · rw [sval_eq_cocycle]
    exact CZ.not_intCast_of_distToNearestInt_pos hdpos
  · rw [sval_eq_cocycle]; exact hdpos
  · rw [sval_eq_cocycle, Nat.cast_one, Real.one_rpow, mul_one]
    have hHle : CZ.height23 (-(c : ℤ)) (sOdd n₀ c) ≤ 3 ^ (2 * c) := by
      refine le_trans (height23_cocycle_le n₀ c) ?_
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hwin := hNw c hcw _ (one_le_height23_cocycle n₀ c) hHle
    calc (((δ' * cocycle n₀ c).distToNearestInt : ℚ) : ℝ)
        ≤ (((A * θ ^ c : ℚ)) : ℝ) := by exact_mod_cast hdist
      _ = (A : ℝ) * (θ : ℝ) ^ c := by push_cast; ring
      _ < _ := hwin

/-- The **fixed-`a` strip**: for a *fixed* first coordinate only finitely many `c` violate.
Clearing the denominator of `δΛ_a` turns the inhomogeneous condition into the one-term one. -/
@[category research solved, AMS 11, ref "CZ04" "B2A2", group "rb_collatz_cocycle"]
theorem fixedFst_slice_finite {n₀ : ℕ} {ρ B₀ : ℚ} (hgeo : IsUniformlyGeometric n₀ ρ B₀)
    {δ A θ : ℚ} (hδ : δ ≠ 0) (hA : 0 < A) (hθ0 : 0 < θ) (hθ1 : θ < 1) (a : ℕ) :
    {c : ℕ | (δ * (cocycle n₀ c - cocycle n₀ a)).distToNearestInt ≤ A * θ ^ c}.Finite := by
  set y : ℚ := δ * cocycle n₀ a with hy
  set D : ℤ := (y.den : ℤ) with hD
  have hD0 : (0 : ℤ) < D := by
    rw [hD]
    exact_mod_cast Nat.pos_of_ne_zero y.den_nz
  have hDy : (D : ℚ) * y = (y.num : ℚ) := by
    rw [hD]
    push_cast
    rw [mul_comm]
    exact Rat.mul_den_eq_num y
  have hδ' : (D : ℚ) * δ ≠ 0 := mul_ne_zero (by exact_mod_cast hD0.ne') hδ
  have hA' : (0 : ℚ) < (D : ℚ) * A := by
    have : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hD0
    positivity
  refine Set.Finite.subset (oneTerm_slice_finite hgeo hδ' hA' hθ0 hθ1) ?_
  intro c hc
  have hdist : (δ * (cocycle n₀ c - cocycle n₀ a)).distToNearestInt ≤ A * θ ^ c := hc
  have hsplit : (D : ℚ) * δ * cocycle n₀ c
      = (D : ℚ) * (δ * (cocycle n₀ c - cocycle n₀ a)) + (y.num : ℚ) := by
    rw [← hDy, hy]
    ring
  show ((D : ℚ) * δ * cocycle n₀ c).distToNearestInt ≤ (D : ℚ) * A * θ ^ c
  rw [hsplit, Rat.distToNearestInt_add_intCast]
  calc ((D : ℚ) * (δ * (cocycle n₀ c - cocycle n₀ a))).distToNearestInt
      ≤ |(D : ℚ)| * (δ * (cocycle n₀ c - cocycle n₀ a)).distToNearestInt :=
        Rat.distToNearestInt_intCast_mul_le D _
    _ ≤ |(D : ℚ)| * (A * θ ^ c) := by
        have : (0 : ℚ) ≤ |(D : ℚ)| := abs_nonneg _
        nlinarith
    _ = (D : ℚ) * A * θ ^ c := by
        rw [abs_of_pos (by exact_mod_cast hD0 : (0 : ℚ) < (D : ℚ))]
        ring

/-! ## Slice 2: the fixed-ratio (CZ) kernel -/

/-- **The fixed-ratio slice** ([B2A2] §3.2, replacing [B2A2] §2.3's fixed-*gap* slice): for a
fixed ratio value `r ≠ 1`, only finitely many violating pairs have `Λ_c = r·Λ_a`.

CZ data: `δ_CZ = δ(r−1)`, `q = 1`, `u = Λ_a`, so `δ(Λ_c − Λ_a) = δ_CZ·Λ_a` is the CZ value.  The
pair is determined by its first coordinate (`cocycle_injective`), so bounding `a` bounds the
slice. -/
@[category research solved, AMS 11, ref "CZ04" "B2A2", group "rb_collatz_cocycle"]
theorem fixedRatio_slice_finite {n₀ : ℕ} {ρ B₀ : ℚ} (hgeo : IsUniformlyGeometric n₀ ρ B₀)
    {δ A θ r : ℚ} (hδ : δ ≠ 0) (hA : 0 < A) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hr : r ≠ 1) :
    {p ∈ cocycleViolators n₀ δ A θ | cocycle n₀ p.2 = r * cocycle n₀ p.1}.Finite := by
  set W := {p ∈ cocycleViolators n₀ δ A θ | cocycle n₀ p.2 = r * cocycle n₀ p.1} with hW
  have hfstinj : Set.InjOn Prod.fst W := by
    rintro ⟨a, c⟩ hp ⟨a', c'⟩ hp' heq
    have ha : a = a' := heq
    have h1 : cocycle n₀ c = r * cocycle n₀ a := hp.2
    have h2 : cocycle n₀ c' = r * cocycle n₀ a' := hp'.2
    have : cocycle n₀ c = cocycle n₀ c' := by rw [h1, h2, ha]
    have hc : c = c' := cocycle_injective n₀ this
    rw [ha, hc]
  refine Set.Finite.of_finite_image ?_ hfstinj
  -- the CZ multiplier
  have hδCZ : δ * (r - 1) ≠ 0 := mul_ne_zero hδ (sub_ne_zero.mpr hr)
  obtain ⟨Nw, hNw⟩ := exists_window A θ hA hθ0 hθ1
  obtain ⟨Ns, hNs⟩ := exists_le_cocycle hgeo (2 / |δ * (r - 1)|)
  have hδabs : (0 : ℚ) < |δ * (r - 1)| := abs_pos.mpr hδCZ
  have hfin := CZ.pseudoPisot_approx_of_subspace (δ * (r - 1)) hδCZ (eps θ) (eps_pos hθ0 hθ1)
  have hginj : Function.Injective (fun a : ℕ => ((1, -(a : ℤ), (sOdd n₀ a : ℤ)) : ℕ × ℤ × ℤ)) := by
    intro p q hpq
    have h := congrArg (fun t : ℕ × ℤ × ℤ => t.2.1) hpq
    simp only at h
    omega
  set N := max (max Nw Ns) δ.num.natAbs with hN
  refine Set.Finite.subset ((Set.finite_Iio N).union (hfin.preimage hginj.injOn)) ?_
  rintro a ⟨⟨a', c⟩, hp, rfl⟩
  obtain ⟨⟨hac, hdist⟩, hratio⟩ := hp
  simp only at hac hdist hratio ⊢
  by_cases hsmall : a' < N
  · exact Or.inl hsmall
  right
  push Not at hsmall
  have haw : Nw ≤ a' := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hsmall
  have has : Ns ≤ a' := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hsmall
  have han : δ.num.natAbs ≤ a' := le_trans (le_max_right _ _) hsmall
  -- the value slot
  have hval : δ * (cocycle n₀ c - cocycle n₀ a') = δ * (r - 1) * cocycle n₀ a' := by
    rw [hratio]; ring
  have hdpos : 0 < (δ * (cocycle n₀ c - cocycle n₀ a')).distToNearestInt := by
    refine dist_pos_of_odd_num (c := c) hδ (odd_cocycle_sub_num (n₀ := n₀) hac) ?_ (by omega)
    rw [show (2 : ℚ) ^ c * (δ * (cocycle n₀ c - cocycle n₀ a'))
      = δ * ((2 : ℚ) ^ c * (cocycle n₀ c - cocycle n₀ a')) by ring,
      two_pow_mul_cocycle_sub hac]
  rw [Set.mem_preimage, Set.mem_setOf_eq]
  refine ⟨le_refl 1, ?_, ?_, ?_, ?_⟩
  · rw [sval_eq_cocycle]
    have hΛ := hNs a' has
    have hΛpos := cocycle_pos n₀ a'
    rw [abs_mul, abs_of_pos hΛpos]
    rw [div_le_iff₀ hδabs] at hΛ
    linarith
  · rw [sval_eq_cocycle, ← hval]
    exact CZ.not_intCast_of_distToNearestInt_pos hdpos
  · rw [sval_eq_cocycle, ← hval]; exact hdpos
  · rw [sval_eq_cocycle, ← hval, Nat.cast_one, Real.one_rpow, mul_one]
    have hHle : CZ.height23 (-(a' : ℤ)) (sOdd n₀ a') ≤ 3 ^ (2 * a') := by
      refine le_trans (height23_cocycle_le n₀ a') ?_
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hwin := hNw a' haw _ (one_le_height23_cocycle n₀ a') hHle
    have hθ0' : (0 : ℝ) < (θ : ℝ) := by exact_mod_cast hθ0
    have hθ1' : (θ : ℝ) < 1 := by exact_mod_cast hθ1
    have hA' : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
    calc (((δ * (cocycle n₀ c - cocycle n₀ a')).distToNearestInt : ℚ) : ℝ)
        ≤ (((A * θ ^ c : ℚ)) : ℝ) := by exact_mod_cast hdist
      _ = (A : ℝ) * (θ : ℝ) ^ c := by push_cast; ring
      _ ≤ (A : ℝ) * (θ : ℝ) ^ a' := by
          have := pow_le_pow_of_le_one hθ0'.le hθ1'.le (le_of_lt hac)
          nlinarith
      _ < _ := hwin

/-! ## Slice 3: the NKR branch -/

private def enc (n₀ : ℕ) (p : ℕ × ℕ) : (ℤ × ℤ) × (ℤ × ℤ) :=
  ((-(p.2 : ℤ), (sOdd n₀ p.2 : ℤ)), (-(p.1 : ℤ), (sOdd n₀ p.1 : ℤ)))

private lemma enc_injective (n₀ : ℕ) : Function.Injective (enc n₀) := by
  intro p p' h
  have h1 := congrArg (fun q : (ℤ × ℤ) × (ℤ × ℤ) => q.1.1) h
  have h2 := congrArg (fun q : (ℤ × ℤ) × (ℤ × ℤ) => q.2.1) h
  simp only [enc] at h1 h2
  exact Prod.ext (by omega) (by omega)

private lemma uval_enc_fst (n₀ : ℕ) (p : ℕ × ℕ) :
    NKR.uval (enc n₀ p).1.1 (enc n₀ p).1.2 = cocycle n₀ p.2 := (cocycle_eq_uval n₀ p.2).symm

private lemma uval_enc_snd (n₀ : ℕ) (p : ℕ × ℕ) :
    NKR.uval (enc n₀ p).2.1 (enc n₀ p).2.2 = cocycle n₀ p.1 := (cocycle_eq_uval n₀ p.1).symm

/-- **The infinitely-many-ratios branch**: a family of violators with pairwise-distinct ratios
`Λ_c/Λ_a`, all past the thresholds, is finite.  NKR data: `α₁ = δ`, `α₂ = −δ`,
`(u₁, u₂) = (Λ_c, Λ_a)`; the conclusion "`Λ_c` is an integer" is absurd
(`cocycle_not_intCast`). -/
private lemma finite_of_ratio_injOn {n₀ : ℕ} {δ A θ : ℚ} (hδ : δ ≠ 0) (_hA : 0 < A)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) {N : ℕ} (hNw : ∀ n : ℕ, N ≤ n → ∀ H : ℕ, 1 ≤ H →
        H ≤ 3 ^ (2 * n) → ((A : ℝ) * (θ : ℝ) ^ n) < (H : ℝ) ^ (-eps θ))
    (hN1 : ∀ n : ℕ, N ≤ n → 1 ≤ cocycle n₀ n) (hNnum : δ.num.natAbs ≤ N)
    {T : Set (ℕ × ℕ)} (hTsub : T ⊆ cocycleViolators n₀ δ A θ) (hTN : ∀ p ∈ T, N ≤ p.1)
    (hinj : Set.InjOn (fun p : ℕ × ℕ => cocycle n₀ p.2 / cocycle n₀ p.1) T) : T.Finite := by
  by_contra hTfin
  have hTinf : T.Infinite := hTfin
  have hvals : ∀ p ∈ T, δ * NKR.uval (enc n₀ p).1.1 (enc n₀ p).1.2
      + (-δ) * NKR.uval (enc n₀ p).2.1 (enc n₀ p).2.2
      = δ * (cocycle n₀ p.2 - cocycle n₀ p.1) := by
    intro p _
    rw [uval_enc_fst, uval_enc_snd]
    ring
  have habs : ∀ q ∈ enc n₀ '' T,
      1 ≤ |NKR.uval q.1.1 q.1.2| ∧ 1 ≤ |NKR.uval q.2.1 q.2.2| := by
    rintro q ⟨p, hpT, rfl⟩
    have hac := (hTsub hpT).1
    have hNa := hTN p hpT
    rw [uval_enc_fst, uval_enc_snd,
      abs_of_pos (cocycle_pos n₀ p.2), abs_of_pos (cocycle_pos n₀ p.1)]
    exact ⟨hN1 p.2 (by omega), hN1 p.1 hNa⟩
  have hP2 : ∀ q ∈ enc n₀ '' T, NKR.uval q.1.1 q.1.2 ≠ -NKR.uval q.2.1 q.2.2 := by
    rintro q ⟨p, -, rfl⟩
    rw [uval_enc_fst, uval_enc_snd]
    have h1 := cocycle_pos n₀ p.2
    have h2 := cocycle_pos n₀ p.1
    intro h
    linarith
  have hratio : ∀ q ∈ enc n₀ '' T, ∀ q' ∈ enc n₀ '' T, q ≠ q' →
      NKR.uval q.1.1 q.1.2 / NKR.uval q.2.1 q.2.2
        ≠ NKR.uval q'.1.1 q'.1.2 / NKR.uval q'.2.1 q'.2.2 ∧
      NKR.uval q.2.1 q.2.2 / NKR.uval q.1.1 q.1.2
        ≠ NKR.uval q'.2.1 q'.2.2 / NKR.uval q'.1.1 q'.1.2 := by
    rintro q ⟨p, hpT, rfl⟩ q' ⟨p', hp'T, rfl⟩ hqq'
    have hpp' : p ≠ p' := fun hh => hqq' (congrArg (enc n₀) hh)
    have hne : cocycle n₀ p.2 / cocycle n₀ p.1 ≠ cocycle n₀ p'.2 / cocycle n₀ p'.1 :=
      fun hh => hpp' (hinj hpT hp'T hh)
    rw [uval_enc_fst, uval_enc_snd, uval_enc_fst, uval_enc_snd]
    refine ⟨hne, fun hh => hne ?_⟩
    have h1 := cocycle_pos n₀ p.1
    have h2 := cocycle_pos n₀ p.2
    have h3 := cocycle_pos n₀ p'.1
    have h4 := cocycle_pos n₀ p'.2
    field_simp at hh ⊢
    linarith [hh]
  have hpos : ∀ q ∈ enc n₀ '' T,
      0 < (δ * NKR.uval q.1.1 q.1.2 + (-δ) * NKR.uval q.2.1 q.2.2).distToNearestInt := by
    rintro q ⟨p, hpT, rfl⟩
    have hac := (hTsub hpT).1
    have hNa := hTN p hpT
    rw [hvals p hpT]
    refine dist_pos_of_odd_num (c := p.2) hδ (odd_cocycle_sub_num (n₀ := n₀) hac) ?_ (by omega)
    rw [show (2 : ℚ) ^ p.2 * (δ * (cocycle n₀ p.2 - cocycle n₀ p.1))
      = δ * ((2 : ℚ) ^ p.2 * (cocycle n₀ p.2 - cocycle n₀ p.1)) by ring,
      two_pow_mul_cocycle_sub hac]
  have happrox : ∀ q ∈ enc n₀ '' T,
      ((δ * NKR.uval q.1.1 q.1.2 + (-δ) * NKR.uval q.2.1 q.2.2).distToNearestInt : ℝ)
        < ((CZ.height23 q.1.1 q.1.2 * CZ.height23 q.2.1 q.2.2 : ℕ) : ℝ) ^ (-eps θ) := by
    rintro q ⟨p, hpT, rfl⟩
    have hac := (hTsub hpT).1
    have hdist := (hTsub hpT).2
    have hNa := hTN p hpT
    rw [hvals p hpT]
    have hH1 : 1 ≤ CZ.height23 (enc n₀ p).1.1 (enc n₀ p).1.2
        * CZ.height23 (enc n₀ p).2.1 (enc n₀ p).2.2 :=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (Nat.one_le_iff_ne_zero.mp (one_le_height23_cocycle n₀ p.2))
          (Nat.one_le_iff_ne_zero.mp (one_le_height23_cocycle n₀ p.1)))
    have hHle : CZ.height23 (enc n₀ p).1.1 (enc n₀ p).1.2
        * CZ.height23 (enc n₀ p).2.1 (enc n₀ p).2.2 ≤ 3 ^ (2 * p.2) := by
      have h1 := height23_cocycle_le n₀ p.2
      have h2 := height23_cocycle_le n₀ p.1
      have h3 : (3 : ℕ) ^ sOdd n₀ p.1 ≤ 3 ^ p.2 := by
        exact Nat.pow_le_pow_right (by norm_num) (le_trans (num_odd_steps_le p.1 n₀) (by omega))
      calc CZ.height23 (enc n₀ p).1.1 (enc n₀ p).1.2
              * CZ.height23 (enc n₀ p).2.1 (enc n₀ p).2.2
          ≤ 3 ^ p.2 * 3 ^ p.1 := Nat.mul_le_mul h1 h2
        _ ≤ 3 ^ p.2 * 3 ^ p.2 :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
        _ = 3 ^ (2 * p.2) := by rw [← pow_add]; ring_nf
    have hwin := hNw p.2 (by omega) _ hH1 hHle
    calc (((δ * (cocycle n₀ p.2 - cocycle n₀ p.1)).distToNearestInt : ℚ) : ℝ)
        ≤ (((A * θ ^ p.2 : ℚ)) : ℝ) := by exact_mod_cast hdist
      _ = (A : ℝ) * (θ : ℝ) ^ p.2 := by push_cast; ring
      _ < _ := hwin
  obtain ⟨q, hq𝒩, ⟨z, hz⟩, -⟩ := NKR.sUnit_pair_integrality_of_subspace δ (-δ) hδ
    (neg_ne_zero.mpr hδ) (eps θ) (eps_pos hθ0 hθ1) (enc n₀ '' T)
    (hTinf.image (enc_injective n₀).injOn) habs hP2 hratio hpos happrox
  obtain ⟨p, hpT, rfl⟩ := hq𝒩
  have hac := (hTsub hpT).1
  have hNa := hTN p hpT
  rw [uval_enc_fst] at hz
  exact cocycle_not_intCast (n₀ := n₀) (by omega) z hz

/-! ## The cocycle kernel -/

/-- **The cocycle kernel** ([B2A2] §3.2, T3b's Diophantine core): for a rational `δ ≠ 0`, a
constant `A > 0` and a rational scale `θ ∈ (0,1)`, only finitely many pairs `a < c` satisfy

  `‖δ·(Λ_c − Λ_a)‖ ≤ A·θ^c`.

The `Λ`-analogue of `RB.scaledViolators_finite`, proved by the three-way split described in the
module doc: the fixed-`a` strip (one-term CZ), finitely many ratio values (fixed-ratio CZ
slices), infinitely many ratio values (NKR at `α₁ = δ`, `α₂ = −δ`).

Ineffective.  Footprint: std3 + `Subspace.evertseSchlickewei` (**refereed**). -/
@[category research solved, AMS 11, ref "CZ04" "NKR25" "B2A2", group "rb_collatz_cocycle"]
theorem cocycleViolators_finite {n₀ : ℕ} {ρ B₀ : ℚ} (hgeo : IsUniformlyGeometric n₀ ρ B₀)
    {δ A θ : ℚ} (hδ : δ ≠ 0) (hA : 0 < A) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (cocycleViolators n₀ δ A θ).Finite := by
  classical
  obtain ⟨Nw, hNw⟩ := exists_window A θ hA hθ0 hθ1
  obtain ⟨N1, hN1⟩ := exists_le_cocycle hgeo 1
  set N := max (max Nw N1) δ.num.natAbs with hNdef
  have hNw' : ∀ n : ℕ, N ≤ n → ∀ H : ℕ, 1 ≤ H → H ≤ 3 ^ (2 * n) →
      ((A : ℝ) * (θ : ℝ) ^ n) < (H : ℝ) ^ (-eps θ) := fun n hn =>
    hNw n (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn)
  have hN1' : ∀ n : ℕ, N ≤ n → 1 ≤ cocycle n₀ n := fun n hn =>
    hN1 n (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn)
  have hNnum : δ.num.natAbs ≤ N := le_max_right _ _
  -- split off the strip `a < N`
  have hstrip : {p ∈ cocycleViolators n₀ δ A θ | p.1 < N}.Finite := by
    have hsub : {p ∈ cocycleViolators n₀ δ A θ | p.1 < N} ⊆
        ⋃ a ∈ Finset.range N, (fun c => (a, c)) ''
          {c : ℕ | (δ * (cocycle n₀ c - cocycle n₀ a)).distToNearestInt ≤ A * θ ^ c} := by
      rintro ⟨a, c⟩ ⟨⟨hac, hdist⟩, hsmall⟩
      exact Set.mem_biUnion (Finset.mem_range.mpr hsmall) ⟨c, hdist, rfl⟩
    refine Set.Finite.subset (Set.Finite.biUnion (Finset.finite_toSet _) fun a _ => ?_) hsub
    exact Set.Finite.image _ (fixedFst_slice_finite hgeo hδ hA hθ0 hθ1 a)
  have hsplit : cocycleViolators n₀ δ A θ ⊆
      {p ∈ cocycleViolators n₀ δ A θ | p.1 < N} ∪ {p ∈ cocycleViolators n₀ δ A θ | N ≤ p.1} := by
    intro p hp
    by_cases h : p.1 < N
    · exact Or.inl ⟨hp, h⟩
    · exact Or.inr ⟨hp, by omega⟩
  refine Set.Finite.subset (Set.Finite.union hstrip ?_) hsplit
  -- the main part: dichotomy on the ratio value
  set V : Set (ℕ × ℕ) := {p ∈ cocycleViolators n₀ δ A θ | N ≤ p.1} with hVdef
  set ratio : ℕ × ℕ → ℚ := fun p => cocycle n₀ p.2 / cocycle n₀ p.1 with hratiodef
  by_contra hVfin
  have hVinf : V.Infinite := hVfin
  by_cases hg : (ratio '' V).Finite
  · -- finitely many ratio values: each fibre is a CZ slice
    apply hVinf
    have hcover : V ⊆ ⋃ r ∈ ratio '' V,
        {p ∈ cocycleViolators n₀ δ A θ | cocycle n₀ p.2 = r * cocycle n₀ p.1} := by
      intro p hp
      refine Set.mem_biUnion (Set.mem_image_of_mem ratio hp) ⟨hp.1, ?_⟩
      have hpos := cocycle_pos n₀ p.1
      show cocycle n₀ p.2 = cocycle n₀ p.2 / cocycle n₀ p.1 * cocycle n₀ p.1
      field_simp
    refine Set.Finite.subset (Set.Finite.biUnion hg fun r hr => ?_) hcover
    refine fixedRatio_slice_finite (r := r) hgeo hδ hA hθ0 hθ1 ?_
    obtain ⟨p, hp, rfl⟩ := hr
    have hac := hp.1.1
    intro h1
    have hcc : cocycle n₀ p.2 = cocycle n₀ p.1 := by
      have hpos := cocycle_pos n₀ p.1
      have h2 : cocycle n₀ p.2 / cocycle n₀ p.1 = 1 := h1
      field_simp at h2
      linarith
    exact absurd (cocycle_injective n₀ hcc) (by omega)
  · -- infinitely many ratio values: a ratio-injective section, then NKR
    have hginf : (ratio '' V).Infinite := hg
    have hsec : ∀ y ∈ ratio '' V, ∃ p ∈ V, ratio p = y := by
      rintro y ⟨p, hp, rfl⟩
      exact ⟨p, hp, rfl⟩
    have hratioinv : ∀ y ∈ ratio '' V, ratio (Function.invFunOn ratio V y) = y :=
      fun y hy => Function.invFunOn_eq (hsec y hy)
    have hTsub : Function.invFunOn ratio V '' (ratio '' V) ⊆ V := by
      rintro t ⟨y, hy, rfl⟩
      exact Function.invFunOn_mem (hsec y hy)
    have hinvinj : Set.InjOn (Function.invFunOn ratio V) (ratio '' V) := by
      intro y1 hy1 y2 hy2 h
      rw [← hratioinv y1 hy1, ← hratioinv y2 hy2, h]
    have hTinf : (Function.invFunOn ratio V '' (ratio '' V)).Infinite := hginf.image hinvinj
    have hinjT : Set.InjOn ratio (Function.invFunOn ratio V '' (ratio '' V)) := by
      rintro t1 ⟨y1, hy1, rfl⟩ t2 ⟨y2, hy2, rfl⟩ h
      rw [hratioinv y1 hy1, hratioinv y2 hy2] at h
      rw [h]
    exact hTinf (finite_of_ratio_injOn hδ hA hθ0 hθ1 hNw' hN1' hNnum
      (fun p hp => (hTsub hp).1) (fun p hp => (hTsub hp).2) hinjT)

/-! ## The pigeonhole layer -/

/-- Rational Bernoulli certificate (a private copy of `RB`'s `exists_pow_ge`, kept local so this
file does not import the model-side `RB.RationalK` for one inequality). -/
private lemma exists_pow_ge (r : ℚ) (hr0 : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N) :
    ∃ θ : ℚ, 0 < θ ∧ θ < 1 ∧ r ≤ θ ^ N := by
  have hN0 : (0 : ℚ) < N := by exact_mod_cast hN
  have hdivle : (1 - r) / N ≤ 1 - r := div_le_self (by linarith) (by exact_mod_cast hN)
  have hdivpos : 0 < (1 - r) / N := div_pos (by linarith) hN0
  refine ⟨1 - (1 - r) / N, by linarith, by linarith, ?_⟩
  have hb := one_add_mul_le_pow (a := -((1 - r) / N)) (by linarith) N
  calc r = 1 + (N : ℚ) * (-((1 - r) / N)) := by field_simp; ring
    _ ≤ (1 + -((1 - r) / N)) ^ N := hb
    _ = (1 - (1 - r) / N) ^ N := by rw [← sub_eq_add_neg]

/-- The set of length-`k` factors of the parity word is finite (its letters are `0` or `1`). -/
@[category API, AMS 11 68, ref "B2A2", group "rb_collatz_cocycle"]
lemma factorSet_finite (n₀ k : ℕ) :
    (Set.range fun a : ℕ => factor (parityWord n₀) k a).Finite := by
  refine Set.Finite.subset
    (Set.Finite.pi' (t := fun _ : Fin k => Set.Iic 1) fun _ => Set.finite_Iic _) ?_
  rintro w ⟨a, rfl⟩
  exact fun i => Set.mem_Iic.mpr (parityWord_le_one _ _)

/-- **Pigeonhole**: at most `C·k` distinct length-`k` factors ⇒ two of the `C·k + 1` windows at
positions `0, …, C·k` coincide — a repetition. -/
@[category research solved, AMS 11 68, ref "B2A2", group "rb_collatz_cocycle"]
lemma exists_repetition_of_complexity_le {n₀ C k : ℕ}
    (h : AS.complexity (parityWord n₀) k ≤ C * k) :
    ∃ a c, a < c ∧ c ≤ C * k ∧ IsRepetition n₀ a c k := by
  classical
  have hncard : AS.complexity (parityWord n₀) k = (factorSet_finite n₀ k).toFinset.card :=
    Set.ncard_eq_toFinset_card _ (factorSet_finite n₀ k)
  have hcard : ((factorSet_finite n₀ k).toFinset).card < (Finset.range (C * k + 1)).card := by
    rw [Finset.card_range, ← hncard]
    exact Nat.lt_succ_of_le h
  have hmaps : ∀ a ∈ Finset.range (C * k + 1),
      factor (parityWord n₀) k a ∈ (factorSet_finite n₀ k).toFinset := fun a _ => by
    rw [Set.Finite.mem_toFinset]
    exact ⟨a, rfl⟩
  obtain ⟨u, hu, v, hv, huv, hfeq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  rw [Finset.mem_range] at hu hv
  rcases Nat.lt_or_ge u v with h' | h'
  · exact ⟨u, v, h', by omega, hfeq⟩
  · exact ⟨v, u, by omega, by omega, hfeq.symm⟩

/-! ## T3b: the divergent-Collatz class theorem -/

/-- **T3b of [B2A2]** (§3.2), the capstone WP8 was named for: a **uniformly geometrically
divergent** Collatz orbit whose **cocycle constant is rational** has **superlinear** parity-word
complexity — for every `C` some length `m` has `p(m) > C·m`.

The reduction mirrors [M4A3] §4 / `RB.superlinear_of_K_rat` with `Λₙ` in place of `(3/2)ⁿ`:
pigeonhole ⇒ repetition `(a, c, k)` with `c ≤ C·k` ⇒ (`dist_le_of_repetition`) a cocycle
violator at the Bernoulli scale `θ(C)` ⇒ (`cocycleViolators_finite`) `c` bounded by some `M` ⇒
(`repetition_le_add`) `k ≤ c + t ≤ M + t`.  So the single length `k = M + t + 1` already refutes
`p(k) ≤ C·k`.

Note the shape: **superlinearity**, not a linear floor — a linear lower bound, however large its
constant, is compatible with automaticity, so the covering floor of
`RB.Collatz.complexity_ge_of_injective` (slope `1`) or [Dub09] Cor 4's `1.7095n` could never
serve here.

Scope (module doc): both hypotheses are restrictive and neither is known for any divergent orbit
— indeed no divergent orbit is known.  Ineffective; footprint std3 + `Subspace.evertseSchlickewei`. -/
@[category research solved, AMS 11 37 68, ref "CZ04" "NKR25" "B2A2", group "rb_collatz_cocycle"]
theorem divergent_superlinear_of_geometric_ratK {n₀ : ℕ} (hn₀ : 1 ≤ n₀) {ρ B₀ : ℚ}
    (hgeo : IsUniformlyGeometric n₀ ρ B₀) {δ : ℚ} (hK : IsCocycleConstant n₀ (δ : ℝ)) (C : ℕ) :
    ∃ m, 1 ≤ m ∧ C * m < AS.complexity (parityWord n₀) m := by
  have hρ0 : 0 < ρ := hgeo.1
  have hρ1 : ρ < 1 := hgeo.2.1
  have hB₀ : 1 ≤ B₀ := one_le_growthConst hgeo
  have hB : 0 < tailBound ρ B₀ := by
    unfold tailBound
    have : (0 : ℚ) < 1 - ρ := by linarith
    positivity
  -- the cocycle constant is at least `n₀ ≥ 1`
  have hδ : δ ≠ 0 := by
    have h0 := scaled_le_of_cocycleConstant hK 0
    rw [scaled_zero] at h0
    have : (1 : ℚ) ≤ (n₀ : ℚ) := by exact_mod_cast hn₀
    intro hz
    rw [hz] at h0
    linarith
  -- the violator constant and the Bernoulli scale
  set A : ℚ := B₀ * tailBound ρ B₀ with hA
  have hApos : 0 < A := by rw [hA]; nlinarith
  obtain ⟨θ, hθ0, hθ1, hθpow⟩ := exists_pow_ge ρ hρ0 hρ1 (C + 1) (by omega)
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ p ∈ cocycleViolators n₀ δ A θ, p.2 ≤ M := by
    obtain ⟨M, hM⟩ := ((cocycleViolators_finite hgeo hδ hApos hθ0 hθ1).image Prod.snd).bddAbove
    exact ⟨M, fun p hp => hM (Set.mem_image_of_mem _ hp)⟩
  obtain ⟨t, ht⟩ : ∃ t : ℕ, n₀ < 2 ^ t := ⟨n₀, Nat.lt_two_pow_self⟩
  refine ⟨M + t + 1, by omega, ?_⟩
  set k := M + t + 1 with hkdef
  by_contra hle
  obtain ⟨a, c, hac, hc, hrep⟩ := exists_repetition_of_complexity_le (Nat.not_lt.mp hle)
  have hck : c ≤ (C + 1) * k := le_trans hc (by nlinarith [Nat.zero_le (C * k)])
  have hkv : (a, c) ∈ cocycleViolators n₀ δ A θ := by
    refine ⟨hac, ?_⟩
    calc (δ * (cocycle n₀ c - cocycle n₀ a)).distToNearestInt
        ≤ B₀ * ρ ^ k * tailBound ρ B₀ := dist_le_of_repetition hgeo hK hrep
      _ = A * ρ ^ k := by rw [hA]; ring
      _ ≤ A * (θ ^ (C + 1)) ^ k := by
          have := pow_le_pow_left₀ (le_of_lt hρ0) hθpow k
          nlinarith
      _ = A * θ ^ ((C + 1) * k) := by rw [← pow_mul]
      _ ≤ A * θ ^ c := by
          have := pow_le_pow_of_le_one hθ0.le hθ1.le hck
          nlinarith
  have hcM : c ≤ M := hM (a, c) hkv
  have hbound := repetition_le_add hn₀ hgeo hac ht hrep
  omega

/-- **Cobham's corollary** ([B2A2] §3.2's headline): the parity word of a uniformly
geometrically divergent orbit with rational cocycle constant is **not automatic**.

The A.2 transfer at its honest frontier: conditional, but a statement about genuine `3x+1`
parity words rather than the `(3/2)ⁿ` model. -/
@[category research solved, AMS 11 37 68, ref "CZ04" "NKR25" "Cob72" "B2A2",
  group "rb_collatz_cocycle"]
theorem not_automatic_of_geometric_ratK {n₀ : ℕ} (hn₀ : 1 ≤ n₀) {ρ B₀ : ℚ}
    (hgeo : IsUniformlyGeometric n₀ ρ B₀) {δ : ℚ} (hK : IsCocycleConstant n₀ (δ : ℝ)) :
    ¬ AS.IsAutomatic (parityWord n₀) :=
  AS.not_automatic_of_complexity_superlinear
    (divergent_superlinear_of_geometric_ratK hn₀ hgeo hK)

/-- The same conclusion in the WP7 covering-number language: such an orbit visits
**superlinearly many** residues mod `2^m` (`RB.Collatz.complexity_eq_ncard_residues`). -/
@[category research solved, AMS 11 37 68, ref "CZ04" "NKR25" "B2A2", group "rb_collatz_cocycle"]
theorem covering_superlinear_of_geometric_ratK {n₀ : ℕ} (hn₀ : 1 ≤ n₀) {ρ B₀ : ℚ}
    (hgeo : IsUniformlyGeometric n₀ ρ B₀) {δ : ℚ} (hK : IsCocycleConstant n₀ (δ : ℝ)) (C : ℕ) :
    ∃ m, 1 ≤ m ∧ C * m < (Set.range fun n => (T_iter n n₀ : ZMod (2 ^ m))).ncard := by
  obtain ⟨m, hm, hlt⟩ := divergent_superlinear_of_geometric_ratK hn₀ hgeo hK C
  exact ⟨m, hm, by rwa [complexity_eq_ncard_residues hn₀ m] at hlt⟩

end RB.Collatz
