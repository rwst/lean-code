/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.Bernoulli
import BB61.BlockRecoding
import BB61.Invariant
import ForMathlib.Analysis.Equidistribution.AddCircleWeyl
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# M3 Theorem 4: the past drops out (the trace-ladder reduction)

`note-1061-M3.html` Theorem 4 is the reduction that killed Route B's past.  For a
`σ`-invariant `μ` on the full `2`-shift, with `λ = Φ_*μ` on the torus and `ν = t_*μ` the
**future marginal** on `C(α)`,

`|λ̂(γ) - ν̂(Tr(γαᵐ))| ≤ 2π δ_γ ρᵐ (W + d - 1)`,

so `Φ_h(μ) = lim_m ν̂(h Tr_m)`, and Problem 10.61 becomes a statement about `T`-invariant
measures on the Cantor set alone: the window `K`, the past coordinates, the conjugate shadow
and the two-sided coding all disappear from the statement.

## The proof here is not the note's

The note proves it on the torus `𝕋^d_Λ`, through the characters `χ_γ`, `λ̂(γ) = λ̂(αγ)` and
the corrected Meyer estimate (Proposition 2).  At degree two none of that is needed, and the
whole theorem is an **identity between real numbers**:

`Tr_m · t(ω⁺) = (an integer) + F̃(σᵐω) + E_m(ω)`,   `|E_m(ω)| ≤ (W+1)|β|ᵐ`

(`traceSeq_mul_piVal_futures`, `abs_ladderErr_le`), where `Tr_m = αᵐ + βᵐ` is the trace
ladder of `BB61/BlockRecoding.lean` and `F̃ = t(ω⁺) - S(ω⁻)` is `BB61/Factor.lean`'s factor
map before reduction mod one.

The mechanism is one line of `BB61/Bernoulli.lean` read backwards.  `trace_pw` says
`(α-1)αʲ + (β-1)βʲ = T_j ∈ ℤ`; read as a *decomposition*,

`(α-1)αʲ = T_j - c_j`   (`futureWeight_eq`),

the `j`-th **future** weight is an integer minus the `j`-th **window** weight.  Multiplying
`t(ω⁺)` by `αᵐ` walks the first `m` future letters backwards past the origin; each one lands
on `(α-1)αʲ`, and `futureWeight_eq` converts it, modulo an integer the character cannot see,
into exactly the window weight it would have had in `S((σᵐω)⁻)`.  That is why the past drops
out: *the past coordinates were the future coordinates all along*, and the trace ladder is
the change of variables.  The two leftovers — the window beyond depth `m`, and the conjugate
factor `βᵐ t(ω⁺)` — are the error, and both are `O(|β|ᵐ)`.

No unit hypothesis is needed (Theorem 4 is the one part of §4 that does not need
`ᾱM` to be an automorphism), and no ergodic theorem: only `σ`-invariance of `μ`.

## What is here

* `traceSeq_mul_piVal_futures` — the identity, at every word and every depth;
* `abs_ladderErr_le` — the error bound, with the note's constant `W + d - 1` at `d = 2`;
* `norm_fourier_int_add_sub` — `e(·)` is `2π|n|`-Lipschitz and blind to the integer head;
* `thm4` — Theorem 4: `‖ν̂(h Tr_m) - Φ_h(μ)‖ ≤ 2π|h|(W+1)|β|ᵐ`;
* `tendsto_futureCoeff` — `Φ_h(μ) = lim_m ν̂(h Tr_m)`, and `exists_tendsto_futureCoeff` is
  **M3 Corollary 5 at integer frequencies**: the trace-ladder limit exists for *every*
  invariant measure, not only the Bernoulli ones M0 and M1 tested;
* `not_equidistributed_of_ladder` — 10.61 at `α` from the ladder alone.

## What is not here

Two things the note has and this file does not.

1. **General frequencies.**  Proposition 2 and Theorem 4 are stated for every
   `γ ∈ 𝔡⁻¹ = f'(α)⁻¹ℤ[α]`; here `γ` is an ordinary integer `h`.  That is the case the
   criterion uses (`Φ_h(μ)`, `h ∈ ℤ`), and by M3 Corollary 6 it is also the only case that
   may enter a proof — but Corollary 6 itself needs the codifferent, which
   `BB61/TraceLadder.lean` has and this file does not consume.

2. **The converse.**  The note's displayed equivalence also uses that *every* `T`-invariant
   `ν` on `C(α)` is the future marginal of a `σ`-invariant `μ` — its natural extension.
   That is not formalised, so `not_equidistributed_of_ladder` proves the direction that does
   not need it: a non-vanishing ladder limit forbids a counterexample.

## References

* `note-1061-M3.html` §4 (Theorem 4, Corollaries 5–6) and §3 (Propositions 2–3);
* `note-1061-M1.html` Lemma 2 and Lemma 6 (the splitting and the factor map).
-/

noncomputable section

namespace BB61

open MeasureTheory Filter Topology

/-! ## Re-indexing the two halves of a two-sided word -/

/-- Reading the future `m` places later is reading the future of the shifted word. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem dR_futures_add (ω : Shift) (m k : ℕ) :
    dR (futures ω) (k + m) = dR (futures (shiftZ^[m] ω)) k := by
  have h : futures ω (k + m) = futures (shiftZ^[m] ω) k := by
    simp only [futures, shiftZ_iterate]
    congr 1
    push_cast
    ring
  simp only [dR, h]

/-- The head of the future, read backwards, is the past of the shifted word: for `j < m`
the letter `ω_{m-j}` is both `(ω⁺)_{m-1-j}` and `((σᵐω)⁻)_j`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem dR_futures_sub (ω : Shift) {m j : ℕ} (hj : j < m) :
    dR (futures ω) (m - 1 - j) = dR (pasts (shiftZ^[m] ω)) j := by
  have h : futures ω (m - 1 - j) = pasts (shiftZ^[m] ω) j := by
    simp only [futures, pasts, shiftZ_iterate]
    congr 1
    omega
  simp only [dR, h]

/-! ## The three pieces of the identity -/

namespace QuadSetup

variable (P : QuadSetup)

/-- The integer head `∑_{j<m} T_j ((σᵐω)⁻)_j` of the ladder identity, with
`T_j = (α-1)αʲ + (β-1)βʲ` the integer of `BB61/Bernoulli.lean`. -/
def ladderHead (m : ℕ) (ω : Shift) : ℤ :=
  ∑ j ∈ Finset.range m, if pasts (shiftZ^[m] ω) j then P.traceZ j else 0

/-- The error of the ladder identity: the window tail beyond depth `m`, plus the
conjugate-side leak `βᵐ t(ω⁺)`.  Both are `O(|β|ᵐ)` (`abs_ladderErr_le`). -/
noncomputable def ladderErr (m : ℕ) (ω : Shift) : ℝ :=
  (∑' j : ℕ, P.cCoef (j + m) * dR (pasts (shiftZ^[m] ω)) (j + m))
    + P.β ^ m * piVal P.α (futures ω)

/-- `(α-1)αʲ = T_j - c_j`: the future weight is an integer minus the window weight.  This
is `BB61/Bernoulli.lean`'s `trace_pw` read as a *decomposition*, and it is the whole reason
the past drops out. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem futureWeight_eq (j : ℕ) :
    (P.α - 1) * P.α ^ j = (P.traceZ j : ℝ) - P.cCoef j := by
  have h := P.trace_pw j
  simp only [cCoef]
  linarith

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem ladderHead_cast (m : ℕ) (ω : Shift) :
    (P.ladderHead m ω : ℝ)
      = ∑ j ∈ Finset.range m, (P.traceZ j : ℝ) * dR (pasts (shiftZ^[m] ω)) j := by
  simp only [ladderHead, Int.cast_sum, apply_ite (fun z : ℤ => (z : ℝ)), Int.cast_zero, dR]
  refine Finset.sum_congr rfl fun j _ => ?_
  split <;> simp

/-! ## The ladder identity -/

/-- **M3 Theorem 4, the identity behind the estimate.**  For every two-sided word `ω` and
every depth `m`,

`Tr_m · t(ω⁺) = (an integer) + F̃(σᵐω) + O(|β|ᵐ)`,

where `Tr_m = αᵐ + βᵐ` is the trace ladder and `F̃ = t(ω⁺) - S(ω⁻)` is the factor map before
reduction mod one.  Multiplying the *future* value by the trace ladder therefore reproduces
the factor map at time `m`, modulo one and modulo an error that dies geometrically. -/
@[category research solved, AMS 11 37, ref "Bug12", group "bugeaud_10_61"]
theorem traceSeq_mul_piVal_futures (hα : 1 < P.α) (ω : Shift) (m : ℕ) :
    (P.traceSeq m : ℝ) * piVal P.α (futures ω)
      = (P.ladderHead m ω : ℝ) + (P.fRaw (shiftZ^[m] ω) + P.ladderErr m ω) := by
  have hα0 : (0 : ℝ) < P.α := lt_trans one_pos hα
  have hαne : P.α ≠ 0 := ne_of_gt hα0
  have hr0 : (0 : ℝ) ≤ P.α⁻¹ := (inv_pos_of_one_lt hα).le
  have hr1 : P.α⁻¹ < 1 := inv_lt_one_of_one_lt hα
  have hgs : Summable fun k : ℕ => dR (futures ω) k * (P.α⁻¹) ^ (k + 1) :=
    summable_dR_pow hr0 hr1 _
  -- split the future series at depth `m`
  have hsplit : ∑' k : ℕ, dR (futures ω) k * (P.α⁻¹) ^ (k + 1)
      = (∑ k ∈ Finset.range m, dR (futures ω) k * (P.α⁻¹) ^ (k + 1))
        + ∑' k : ℕ, dR (futures ω) (k + m) * (P.α⁻¹) ^ (k + m + 1) :=
    (hgs.sum_add_tsum_nat_add m).symm
  -- the tail is the future of the shifted word
  have htail : ∑' k : ℕ, dR (futures ω) (k + m) * (P.α⁻¹) ^ (k + m + 1)
      = (P.α⁻¹) ^ m * ∑' k : ℕ, dR (futures (shiftZ^[m] ω)) k * (P.α⁻¹) ^ (k + 1) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    rw [dR_futures_add ω m k]
    ring
  -- the head is the past of the shifted word
  have hhead : (P.α - 1) *
        (P.α ^ m * ∑ k ∈ Finset.range m, dR (futures ω) k * (P.α⁻¹) ^ (k + 1))
      = ∑ j ∈ Finset.range m, ((P.α - 1) * P.α ^ j) * dR (pasts (shiftZ^[m] ω)) j := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_range_reflect
      (fun k => (P.α - 1) * (P.α ^ m * (dR (futures ω) k * (P.α⁻¹) ^ (k + 1)))) m]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjm : j < m := Finset.mem_range.mp hj
    have h1 : m - 1 - j + 1 = m - j := by omega
    have h2 : P.α ^ m = P.α ^ j * P.α ^ (m - j) := by
      rw [← pow_add]; congr 1; omega
    have h3 : P.α ^ m * (P.α⁻¹) ^ (m - 1 - j + 1) = P.α ^ j := by
      rw [h1, inv_pow, h2, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hαne), mul_one]
    rw [dR_futures_sub ω hjm]
    calc (P.α - 1) * (P.α ^ m * (dR (pasts (shiftZ^[m] ω)) j * (P.α⁻¹) ^ (m - 1 - j + 1)))
        = (P.α - 1) * ((P.α ^ m * (P.α⁻¹) ^ (m - 1 - j + 1)) * dR (pasts (shiftZ^[m] ω)) j) := by
          ring
      _ = ((P.α - 1) * P.α ^ j) * dR (pasts (shiftZ^[m] ω)) j := by rw [h3]; ring
  -- the window series, split at the same depth
  have hwsplit : P.wVal (pasts (shiftZ^[m] ω))
      = (∑ j ∈ Finset.range m, P.cCoef j * dR (pasts (shiftZ^[m] ω)) j)
        + ∑' j : ℕ, P.cCoef (j + m) * dR (pasts (shiftZ^[m] ω)) (j + m) :=
    ((P.summable_cCoef _).sum_add_tsum_nat_add m).symm
  -- assemble
  have hcancel : (P.α⁻¹) ^ m * P.α ^ m = 1 := by
    rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hαne)]
  have hexp : ∑ j ∈ Finset.range m, ((P.α - 1) * P.α ^ j) * dR (pasts (shiftZ^[m] ω)) j
      = (P.ladderHead m ω : ℝ)
        - ∑ j ∈ Finset.range m, P.cCoef j * dR (pasts (shiftZ^[m] ω)) j := by
    rw [P.ladderHead_cast m ω, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [P.futureWeight_eq j]
    ring
  rw [P.traceSeq_cast m, ladderErr, fRaw]
  simp only [piVal]
  rw [hsplit, htail]
  linear_combination hhead + hexp + hwsplit + (P.α - 1) *
    (∑' k : ℕ, dR (futures (shiftZ^[m] ω)) k * (P.α⁻¹) ^ (k + 1)) * hcancel

/-! ## The error is `O(|β|ᵐ)` -/

/-- `W = |β-1|/(1-|β|)`, the note's window constant `W = ∑_{j≥2}|α_j-1|/(1-|α_j|)` at degree
two.  It bounds `diam K`, and here it bounds the window tail beyond depth `m`. -/
noncomputable def wConst : ℝ := |P.β - 1| / (1 - |P.β|)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem wConst_nonneg : 0 ≤ P.wConst := by
  have hβ := P.abs_beta_lt_one
  have : (0 : ℝ) < 1 - |P.β| := by linarith
  exact div_nonneg (abs_nonneg _) this.le

/-- `|c_m| = |β-1| |β|ᵐ` exactly — `abs_cCoef_le`'s estimate is not needed here. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_cCoef (m : ℕ) : |P.cCoef m| = |P.β - 1| * |P.β| ^ m := by
  rw [cCoef, abs_mul, abs_pow]

/-- The window tail beyond depth `m` is at most `W |β|ᵐ`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_window_tail_le (δ : ℕ → Bool) (m : ℕ) :
    |∑' j : ℕ, P.cCoef (j + m) * dR δ (j + m)| ≤ P.wConst * |P.β| ^ m := by
  have hβ := P.abs_beta_lt_one
  have hβ0 : (0 : ℝ) ≤ |P.β| := abs_nonneg _
  have hden : (0 : ℝ) < 1 - |P.β| := by linarith
  have hgeom : Summable fun j : ℕ => |P.β - 1| * |P.β| ^ (j + m) := by
    simp only [pow_add]
    exact ((summable_geometric_of_lt_one hβ0 hβ).mul_right _).mul_left _
  have hbd : ∀ j : ℕ, ‖P.cCoef (j + m) * dR δ (j + m)‖ ≤ |P.β - 1| * |P.β| ^ (j + m) := by
    intro j
    rw [Real.norm_eq_abs, abs_mul, P.abs_cCoef]
    calc |P.β - 1| * |P.β| ^ (j + m) * |dR δ (j + m)|
        ≤ |P.β - 1| * |P.β| ^ (j + m) * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [abs_of_nonneg (dR_nonneg δ (j + m))]
          exact dR_le_one δ (j + m)
      _ = |P.β - 1| * |P.β| ^ (j + m) := mul_one _
  have hb := tsum_of_norm_bounded hgeom.hasSum hbd
  rw [Real.norm_eq_abs] at hb
  refine hb.trans_eq ?_
  simp only [pow_add]
  rw [tsum_mul_left, tsum_mul_right, tsum_geometric_of_lt_one hβ0 hβ, wConst]
  field_simp

/-- **The error bound of M3 Theorem 4.**  `|E_m(ω)| ≤ (W+1)|β|ᵐ`, the note's
`δ_γ ρᵐ (W + d - 1)` at degree two with `γ = h`: the window tail contributes `W`, the
conjugate leak `βᵐ t(ω⁺)` contributes `1` because `t(ω⁺) ∈ [0,1]`. -/
@[category research solved, AMS 11 37, ref "Bug12", group "bugeaud_10_61"]
theorem abs_ladderErr_le (hα : 1 < P.α) (ω : Shift) (m : ℕ) :
    |P.ladderErr m ω| ≤ (P.wConst + 1) * |P.β| ^ m := by
  have h1 := P.abs_window_tail_le (pasts (shiftZ^[m] ω)) m
  have h2 : |P.β ^ m * piVal P.α (futures ω)| ≤ |P.β| ^ m := by
    rw [abs_mul, abs_pow]
    calc |P.β| ^ m * |piVal P.α (futures ω)| ≤ |P.β| ^ m * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [abs_of_nonneg (piVal_nonneg hα _)]
          exact piVal_le_one hα _
      _ = |P.β| ^ m := mul_one _
  calc |P.ladderErr m ω|
      ≤ |∑' j : ℕ, P.cCoef (j + m) * dR (pasts (shiftZ^[m] ω)) (j + m)|
          + |P.β ^ m * piVal P.α (futures ω)| := abs_add_le _ _
    _ ≤ P.wConst * |P.β| ^ m + |P.β| ^ m := add_le_add h1 h2
    _ = (P.wConst + 1) * |P.β| ^ m := by ring

end QuadSetup

/-! ## The character `e(·)`: `2π`-Lipschitz, and blind to integers -/

/-- `e(nk x) = e(n (k x))`: an integer factor may be moved onto the argument. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem fourier_intMul_coe (n k : ℤ) (x : ℝ) :
    fourier (n * k) ((x : ℝ) : AddCircle (1 : ℝ))
      = fourier n ((((k : ℝ) * x : ℝ)) : AddCircle (1 : ℝ)) := by
  rw [fourier_coe_apply, fourier_coe_apply]
  congr 1
  push_cast
  ring

/-- The estimate the reduction runs on: `e(·)` is `2π|n|`-Lipschitz and does not see the
integer `k`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem norm_fourier_int_add_sub (n k : ℤ) (x y : ℝ) :
    ‖fourier n (((k : ℝ) + x : ℝ) : AddCircle (1 : ℝ))
        - fourier n ((y : ℝ) : AddCircle (1 : ℝ))‖
      ≤ 2 * Real.pi * |(n : ℝ)| * |x - y| := by
  rw [fourier_coe_apply, fourier_coe_apply]
  simp only [Complex.ofReal_one, div_one]
  have hk : Complex.exp (2 * Real.pi * Complex.I * n * (((k : ℝ) + x : ℝ) : ℂ))
      = Complex.exp (2 * Real.pi * Complex.I * n * (x : ℂ)) := by
    rw [show (2 * Real.pi * Complex.I * n * (((k : ℝ) + x : ℝ) : ℂ))
        = ((n * k : ℤ) : ℂ) * (2 * Real.pi * Complex.I)
          + 2 * Real.pi * Complex.I * n * (x : ℂ) by push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]
  rw [hk]
  have hfac : Complex.exp (2 * Real.pi * Complex.I * n * (x : ℂ))
        - Complex.exp (2 * Real.pi * Complex.I * n * (y : ℂ))
      = Complex.exp (((2 * Real.pi * (n : ℝ) * y : ℝ) : ℂ) * Complex.I)
        * (Complex.exp (Complex.I * ((2 * Real.pi * (n : ℝ) * (x - y) : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    · push_cast; ring_nf
    · push_cast; ring_nf
  rw [hfac, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans_eq ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]

namespace QuadSetup

variable (P : QuadSetup)

/-! ## The two Fourier coefficients -/

/-- `Φ_h(μ) = ∫ e(hF) dμ`, the `h`-th Fourier coefficient of `F_*μ` — the quantity whose
vanishing for all `h ≠ 0` *is* `F_*μ = Leb`. -/
noncomputable def phiCoeff (μ : Measure Shift) (h : ℤ) : ℂ :=
  ∫ ω, fourier h (P.fMap ω) ∂μ

/-- `ν̂(n)` for the **future marginal** `ν = t_*μ`, the image of `μ` under `ω ↦ t(ω⁺)`: a
measure on the Cantor set `C(α)`, and the only thing Theorem 4 leaves standing. -/
noncomputable def futureCoeff (μ : Measure Shift) (n : ℤ) : ℂ :=
  ∫ ω, fourier n ((piVal P.α (futures ω) : ℝ) : AddCircle (1 : ℝ)) ∂μ

/-! ## Theorem 4 -/

/-- Composition with `σᵐ` does not change a complex integral against an invariant measure —
`MeasureTheory.integral_comp_of_measurePreserving` at `ℂ`. -/
@[category API, AMS 11 37, ref "Bug12", group "bugeaud_10_61"]
theorem integral_comp_shiftZ_iterate {μ : Measure Shift} [IsProbabilityMeasure μ]
    (hinv : Measure.map shiftZ μ = μ) (m : ℕ) {φ : Shift → ℂ}
    (hφ : AEStronglyMeasurable φ μ) :
    ∫ ω, φ (shiftZ^[m] ω) ∂μ = ∫ ω, φ ω ∂μ := by
  have hmp : MeasurePreserving shiftZ μ μ := ⟨continuous_shiftZ.measurable, hinv⟩
  have hm : MeasurePreserving (shiftZ^[m]) μ μ := hmp.iterate m
  have h := integral_map (μ := μ) (φ := shiftZ^[m]) (f := φ) hm.measurable.aemeasurable
    (by rwa [hm.map_eq])
  rw [hm.map_eq] at h
  exact h.symm

/-- **M3 Theorem 4, pointwise.**  For every word, `e(h Tr_m t(ω⁺))` and `e(h F(σᵐω))` differ
by at most `2π|h|(W+1)|β|ᵐ`.  The integer head of the ladder identity is invisible to the
character, which is the whole content: *a Pisot frequency is an integer frequency on the
future coordinate*. -/
@[category research solved, AMS 11 37, ref "Bug12", group "bugeaud_10_61"]
theorem norm_fourier_traceSeq_sub (hα : 1 < P.α) (h : ℤ) (m : ℕ) (ω : Shift) :
    ‖fourier (h * P.traceSeq m) ((piVal P.α (futures ω) : ℝ) : AddCircle (1 : ℝ))
        - fourier h (P.fMap (shiftZ^[m] ω))‖
      ≤ 2 * Real.pi * |(h : ℝ)| * ((P.wConst + 1) * |P.β| ^ m) := by
  have hid := P.traceSeq_mul_piVal_futures hα ω m
  have herr := P.abs_ladderErr_le hα ω m
  rw [fourier_intMul_coe, hid, fMap]
  have hbd := norm_fourier_int_add_sub h (P.ladderHead m ω)
    (P.fRaw (shiftZ^[m] ω) + P.ladderErr m ω) (P.fRaw (shiftZ^[m] ω))
  refine hbd.trans ?_
  have : P.fRaw (shiftZ^[m] ω) + P.ladderErr m ω - P.fRaw (shiftZ^[m] ω)
      = P.ladderErr m ω := by ring
  rw [this]
  have hπ : (0 : ℝ) ≤ 2 * Real.pi * |(h : ℝ)| := by positivity
  exact mul_le_mul_of_nonneg_left herr hπ

/-- **M3 Theorem 4 (the ladder reduction).**  Let `μ` be a `σ`-invariant Borel probability
measure on the full `2`-shift and let `ν = t_*μ` be its **future marginal**, the image of `μ`
under `ω ↦ t(ω⁺) ∈ C(α)`.  Then for every integer `h` and every depth `m`,

`|ν̂(h Tr_m) - Φ_h(μ)| ≤ 2π|h|(W+1)|β|ᵐ`,

with `Tr_m = αᵐ + βᵐ` the trace ladder and `Φ_h(μ) = ∫ e(hF) dμ`.  The window `K`, the past
coordinates and the two-sided coding appear only inside the error term. -/
@[category research solved, AMS 11 37, ref "Bug12", group "bugeaud_10_61"]
theorem thm4 (hα : 1 < P.α) (μ : Measure Shift) [IsProbabilityMeasure μ]
    (hinv : Measure.map shiftZ μ = μ) (h : ℤ) (m : ℕ) :
    ‖P.futureCoeff μ (h * P.traceSeq m) - P.phiCoeff μ h‖
      ≤ 2 * Real.pi * |(h : ℝ)| * ((P.wConst + 1) * |P.β| ^ m) := by
  simp only [futureCoeff, phiCoeff]
  have hc1 : Continuous fun ω : Shift =>
      fourier (h * P.traceSeq m) ((piVal P.α (futures ω) : ℝ) : AddCircle (1 : ℝ)) :=
    (map_continuous _).comp (continuous_quotient_mk'.comp (continuous_piVal_futures hα))
  have hc2 : Continuous fun ω : Shift => fourier h (P.fMap ω) :=
    (map_continuous _).comp P.continuous_fMap
  have hi1 : Integrable (fun ω : Shift =>
      fourier (h * P.traceSeq m) ((piVal P.α (futures ω) : ℝ) : AddCircle (1 : ℝ))) μ :=
    hc1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun ω : Shift => fourier h (P.fMap (shiftZ^[m] ω))) μ :=
    (hc2.comp (continuous_shiftZ.iterate m)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hshift : ∫ ω, fourier h (P.fMap (shiftZ^[m] ω)) ∂μ = ∫ ω, fourier h (P.fMap ω) ∂μ :=
    integral_comp_shiftZ_iterate hinv m hc2.aestronglyMeasurable
  rw [← hshift, ← integral_sub hi1 hi2]
  have hpt : ∀ ω : Shift,
      ‖fourier (h * P.traceSeq m) ((piVal P.α (futures ω) : ℝ) : AddCircle (1 : ℝ))
          - fourier h (P.fMap (shiftZ^[m] ω))‖
        ≤ 2 * Real.pi * |(h : ℝ)| * ((P.wConst + 1) * |P.β| ^ m) :=
    fun ω => P.norm_fourier_traceSeq_sub hα h m ω
  have hb := norm_integral_le_of_norm_le_const (μ := μ)
    (C := 2 * Real.pi * |(h : ℝ)| * ((P.wConst + 1) * |P.β| ^ m))
    (Filter.Eventually.of_forall hpt)
  simpa using hb

/-! ## The reduction

`Φ_h(μ)` is the limit of the trace-ladder coefficients of the future marginal.  The past
coordinates, the window `K` and the two-sided coding have disappeared: what is left is a
statement about `T`-invariant measures on `C(α)` alone. -/

/-- **M3 Theorem 4, the limit.**  `Φ_h(μ) = lim_m ν̂(h Tr_m)`, with geometric rate `|β|ᵐ`. -/
@[category research solved, AMS 11 37, ref "Bug12", group "bugeaud_10_61"]
theorem tendsto_futureCoeff (hα : 1 < P.α) (μ : Measure Shift) [IsProbabilityMeasure μ]
    (hinv : Measure.map shiftZ μ = μ) (h : ℤ) :
    Tendsto (fun m : ℕ => P.futureCoeff μ (h * P.traceSeq m)) atTop
      (𝓝 (P.phiCoeff μ h)) := by
  have hβ0 : (0 : ℝ) ≤ |P.β| := abs_nonneg _
  have hgeom : Tendsto (fun m : ℕ => 2 * Real.pi * |(h : ℝ)| * ((P.wConst + 1) * |P.β| ^ m))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => |P.β| ^ m) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 P.abs_beta_lt_one
    simpa using (h1.const_mul (P.wConst + 1)).const_mul (2 * Real.pi * |(h : ℝ)|)
  have h0 : Tendsto (fun m : ℕ => P.futureCoeff μ (h * P.traceSeq m) - P.phiCoeff μ h)
      atTop (𝓝 0) :=
    squeeze_zero_norm (fun m => P.thm4 hα μ hinv h m) hgeom
  simpa using h0.add_const (P.phiCoeff μ h)

/-- **M3 Corollary 5 at integer frequencies (the plateau).**  The trace-ladder limit exists
for *every* `σ`-invariant measure.  M0 and M1 saw it only for Bernoulli measures and read it
as an opportunity; it is a theorem, and therefore also a scope restriction. -/
@[category research solved, AMS 11 37, ref "Bug12", group "bugeaud_10_61"]
theorem exists_tendsto_futureCoeff (hα : 1 < P.α) (μ : Measure Shift) [IsProbabilityMeasure μ]
    (hinv : Measure.map shiftZ μ = μ) (h : ℤ) :
    ∃ L : ℂ, Tendsto (fun m : ℕ => P.futureCoeff μ (h * P.traceSeq m)) atTop (𝓝 L) :=
  ⟨P.phiCoeff μ h, P.tendsto_futureCoeff hα μ hinv h⟩

/-- If `F_*μ` is Lebesgue measure then every nonzero Fourier coefficient of `μ` vanishes:
`Φ_h(μ) = 0` for `h ≠ 0`.  This is the Fourier form of the master target of
`BB61/Invariant.lean`. -/
@[category API, AMS 11 37, ref "Bug12", group "bugeaud_10_61"]
theorem phiCoeff_eq_zero (μ : Measure Shift) [IsProbabilityMeasure μ]
    (hmap : Measure.map P.fMap μ = (volume : Measure (AddCircle (1 : ℝ)))) {h : ℤ}
    (hh : h ≠ 0) : P.phiCoeff μ h = 0 := by
  rw [phiCoeff, ← integral_map P.measurable_fMap.aemeasurable
    (map_continuous (fourier h)).aestronglyMeasurable, hmap, ← haarAddCircle_eq_volume]
  exact integral_fourier_eq_zero hh

/-- **M3 Theorem 4, the consequence.**  A counterexample measure — one whose `F`-image is
Lebesgue — has *all* of its trace-ladder limits equal to zero.  The two-sided coding has been
eliminated: everything is now read off the future marginal. -/
@[category research solved, AMS 11 37, ref "Bug12", group "bugeaud_10_61"]
theorem tendsto_futureCoeff_zero (hα : 1 < P.α) (μ : Measure Shift) [IsProbabilityMeasure μ]
    (hinv : Measure.map shiftZ μ = μ)
    (hmap : Measure.map P.fMap μ = (volume : Measure (AddCircle (1 : ℝ)))) {h : ℤ}
    (hh : h ≠ 0) :
    Tendsto (fun m : ℕ => P.futureCoeff μ (h * P.traceSeq m)) atTop (𝓝 0) := by
  have h1 := P.tendsto_futureCoeff hα μ hinv h
  rwa [P.phiCoeff_eq_zero μ hmap hh] at h1

/-- **Problem 10.61 from the trace ladder alone.**  If every `σ`-invariant measure has *some*
non-vanishing trace-ladder limit, then no point of `C(α)` has `(ξαⁿ)` uniformly distributed
modulo one.  This is the note's displayed equivalence, in the direction that does not need
the natural extension: the criterion is now a statement about `∫ e(h Tr_m t(ω⁺)) dμ`, in
which neither the window nor the past appears. -/
@[category research solved, AMS 11 37, ref "Bug12", group "bugeaud_10_61"]
theorem not_equidistributed_of_ladder (hα : 1 < P.α)
    (hcrit : ∀ μ : Measure Shift, IsProbabilityMeasure μ → Measure.map shiftZ μ = μ →
      ∃ h : ℤ, h ≠ 0 ∧
        ¬ Tendsto (fun m : ℕ => P.futureCoeff μ (h * P.traceSeq m)) atTop (𝓝 0))
    {ξ : ℝ} (hξ : ξ ∈ cantorSet P.α) :
    ¬ IsEquidistributedModuloOne fun n : ℕ => ξ * P.α ^ n := by
  refine P.not_equidistributed_of_no_invariant_measure (fun μ hμ hinv hmap => ?_) hξ
  obtain ⟨h, hh, hne⟩ := hcrit μ hμ hinv
  exact hne (P.tendsto_futureCoeff_zero hα μ hinv hmap hh)

end QuadSetup

end BB61
