/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.RouteANormalForm
import BB61.RouteAConstants
import Mathlib.Order.Filter.AtTopBot.Field
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# M2 Theorem 2(i): certified depths exist, along the balanced ray `M' = ⌈M·L/R⌉`

`BB61/Covering.lean` is Theorem 2's covering: at truncation depths `(M, M')` the orbit is
within `δ(M,M')` of at most `2^M · 2^{M'} · (2K+1)` candidate points, and the numeric
certificate `card · 2δ < 1` produces a uniformly avoided interval.  `BB61/Criterion.lean`
shows the certificate is *satisfiable* when `A(α) < 1`, by running the engine along a
rational ray `(M,M') = (pn,qn)` obtained from `exists_rat_btwn`.

**Theorem 2(i) of `note-1061-M2.html` is a different, and sharper, statement of the same
fact**: it names the ray — the *balanced* one, `M' = ⌈M·L/R⌉` — and bounds the covering
total on it by an explicit affine function of `M`,

`log₂ T(M, ⌈ML/R⌉) ≤ 1 + log₂(1 + C/(1-ρ)) + M · (1 - (L-1)(R-1))/R  ⟶ -∞`,

where `T(M,M') = 2^{M+M'}(α^{-M} + C ρ^{M'}/(1-ρ))` is the total length of the covering
(`coverTotal`).  The slope is negative **exactly** when the normal form of
`BB61/RouteANormalForm.lean` holds, i.e. exactly when `A(α) < 1` (`slope_neg_iff`), and
that single sign is the whole of "certified depths exist".

## The three lines of the proof, isolated

* `pow_balancedDepth_le` — `ρ^{M'} ≤ α^{-M}` at `M' = ⌈ML/R⌉`.  This is the *definition* of
  the balanced ray: writing `α = 2^L` and `ρ = 2^{-R}`, it says `R·M' ≥ L·M`, which
  `Nat.le_ceil` gives.  The window truncation is then no worse than the Cantor truncation,
  and the two error terms of `δ` collapse into one.
* `two_pow_balancedDepth_le` — `2^{M+M'} ≤ 2 · 2^{M(1+L/R)}`, from `⌈x⌉ < x + 1`.  The `2`
  is the *entire* cost of the ceiling, and it is the `1 +` in the note's bound.
* `slope_eq` — `1 + L/R - L = (1 - (L-1)(R-1))/R`, one line of algebra, which is where
  Proposition 1 enters.

Nothing else is used, and in particular no property of `α` beyond `α = 2^L`: the abstract
half of the file is a statement about four real numbers.

## What it gives

* `logb_coverTotal_balancedDepth_le` — the note's displayed inequality, verbatim;
* `tendsto_bound_atBot` — its right-hand side tends to `-∞`;
* `tendsto_coverTotal_balancedDepth` — hence `T ⟶ 0`, and
  `eventually_coverTotal_balancedDepth_lt` — **every** threshold is eventually cleared:
  certified depths exist, and they are cofinal;
* `coverTotal_balancedDepth_lt_of_logb_le` — the *explicit* threshold: a computable `M`
  suffices, which is what M2 Corollary 3 reads off at `2+√5` and at the first cubic firing.

At degree two the engine's own certificate value is `2(2K+1)` times `coverTotal` with
`C = 1 + ρ` (`QuadSetup.cert_eq_coverTotal`), so
`QuadSetup.exists_avoided_interval_at_balancedDepth` re-proves
`BB61/Criterion.lean`'s conclusion **by the note's own route**, with a named ray and an
effective bound rather than an existential rational.  The engine's `C = 1 + |β|` is a bound
for the note's `C_α = Σ_{j≥2}|α_j - 1| = |β - 1|`, so the Lean depths are larger than the
note's; `BB61/m2_thm2i_lean.py` measures by how much.

**The warning of M2 Corollary 3 is visible in the statement.**  The slope
`(1 - (L-1)(R-1))/R` tends to `0⁻` as `A(α) ↑ 1`, so the certified `M` grows like
`1/(1 - (L-1)(R-1))` and the interval count `2^{M+M'}` like `2^{Θ(1/(1-A))}`.  Theorem 2 is
for *proving* a gap once one is known to exist, never for finding one.

## References

* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*,
  Cambridge Tracts in Math. 193, CUP 2012.  Problem 10.61.
* `note-1061-M2.html` §3 Theorem 2(i) and §3 Corollary 3; numerics `BB61/m2_thm2i_lean.py`
  and `BB61/m2_verify.py` check T1.
-/

noncomputable section

namespace BB61

open Filter Topology

/-! ## The covering total and the balanced ray -/

/-- **The balanced depth** `M' = ⌈M·L/R⌉` of Theorem 2(i): the window is truncated exactly
deep enough that its error matches the Cantor error `α^{-M}`. -/
def balancedDepth (L R : ℝ) (M : ℕ) : ℕ := ⌈(M : ℝ) * L / R⌉₊

/-! ## The slope

`1 + L/R - L` is the exponent per unit of `M` in the bound, and Proposition 1 is precisely
the statement that it is negative.
-/

/-- The slope in the note's own shape. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem slope_eq {L R : ℝ} (hR : R ≠ 0) :
    1 + L / R - L = (1 - (L - 1) * (R - 1)) / R := by
  field_simp
  ring

/-- **The slope is negative exactly under the normal form.**  This is the hinge of
Theorem 2(i): Proposition 1 turns `A(α) < 1` into a sign, and the sign is the theorem. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem slope_neg_iff {L R : ℝ} (hR : 0 < R) :
    1 + L / R - L < 0 ↔ 1 < (L - 1) * (R - 1) := by
  rw [slope_eq hR.ne', div_lt_iff₀ hR, zero_mul]
  constructor <;> intro h <;> linarith

/-! ## The two truncation estimates -/

variable {α ρ C L R : ℝ}

/-- **`ρ^{M'} ≤ α^{-M}` at the balanced depth.**  Writing `α = 2^L` and `ρ = 2^{-R}` this is
`L·M ≤ R·⌈ML/R⌉`, i.e. `Nat.le_ceil`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem pow_balancedDepth_le (hα : (2 : ℝ) ^ L = α) (hρ : (2 : ℝ) ^ (-R) = ρ)
    (hR : 0 < R) (M : ℕ) :
    ρ ^ balancedDepth L R M ≤ (α⁻¹) ^ M := by
  have hexp : (M : ℝ) * L ≤ ((balancedDepth L R M : ℕ) : ℝ) * R := by
    have h := Nat.le_ceil ((M : ℝ) * L / R)
    rw [div_le_iff₀ hR] at h
    exact h
  have e1 : ρ ^ balancedDepth L R M
      = (2 : ℝ) ^ (-R * ((balancedDepth L R M : ℕ) : ℝ)) := by
    rw [← hρ, ← Real.rpow_natCast ((2 : ℝ) ^ (-R)) (balancedDepth L R M),
      ← Real.rpow_mul (by norm_num)]
  have e2 : (α⁻¹) ^ M = (2 : ℝ) ^ (-L * (M : ℝ)) := by
    rw [← hα, ← Real.rpow_neg (by norm_num), ← Real.rpow_natCast ((2 : ℝ) ^ (-L)) M,
      ← Real.rpow_mul (by norm_num)]
  rw [e1, e2, Real.rpow_le_rpow_left_iff one_lt_two]
  nlinarith [hexp]

/-- **`2^{M+M'} ≤ 2·2^{M(1+L/R)}` at the balanced depth.**  The lone factor `2` is the whole
price of the ceiling, and it is the `1 +` in the note's bound. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem two_pow_balancedDepth_le (hL : 0 < L) (hR : 0 < R) (M : ℕ) :
    ((2 : ℝ) ^ (M + balancedDepth L R M) : ℝ)
      ≤ 2 * (2 : ℝ) ^ ((M : ℝ) * (1 + L / R)) := by
  have hx : (0 : ℝ) ≤ (M : ℝ) * L / R := by positivity
  have hceil : ((balancedDepth L R M : ℕ) : ℝ) < (M : ℝ) * L / R + 1 :=
    Nat.ceil_lt_add_one hx
  have hsum : ((M + balancedDepth L R M : ℕ) : ℝ) ≤ 1 + (M : ℝ) * (1 + L / R) := by
    have hexp : (M : ℝ) * (1 + L / R) = (M : ℝ) + (M : ℝ) * L / R := by
      field_simp
    push_cast
    rw [hexp]
    linarith
  calc ((2 : ℝ) ^ (M + balancedDepth L R M) : ℝ)
      = (2 : ℝ) ^ (((M + balancedDepth L R M : ℕ) : ℝ)) :=
        (Real.rpow_natCast 2 _).symm
    _ ≤ (2 : ℝ) ^ (1 + (M : ℝ) * (1 + L / R)) :=
        Real.rpow_le_rpow_of_exponent_le one_le_two hsum
    _ = 2 * (2 : ℝ) ^ ((M : ℝ) * (1 + L / R)) := by
        rw [Real.rpow_add (by norm_num), Real.rpow_one]

/-! ## Theorem 2(i) -/

/-- **M2 Theorem 2(i), multiplicative form.**
`T(M, ⌈ML/R⌉) ≤ 2(1 + C/(1-ρ))·2^{M(1+L/R-L)}`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem coverTotal_balancedDepth_le (hα : (2 : ℝ) ^ L = α) (hρ : (2 : ℝ) ^ (-R) = ρ)
    (hL : 0 < L) (hR : 0 < R) (hC : 0 ≤ C) (M : ℕ) :
    coverTotal α ρ C M (balancedDepth L R M)
      ≤ 2 * (1 + C / (1 - ρ)) * (2 : ℝ) ^ ((M : ℝ) * (1 + L / R - L)) := by
  have hρ0 : 0 < ρ := by rw [← hρ]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hρ1 : ρ < 1 := by
    rw [← hρ]; exact Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hden : (0 : ℝ) < 1 - ρ := by linarith
  have hα1 : 1 < α := by
    have h0 : (2 : ℝ) ^ (0 : ℝ) < (2 : ℝ) ^ L :=
      (Real.rpow_lt_rpow_left_iff one_lt_two).mpr hL
    rw [Real.rpow_zero, hα] at h0; exact h0
  have hα0 : (0 : ℝ) < α := by linarith
  set M' := balancedDepth L R M with hM'def
  have hinv : (0 : ℝ) < (α⁻¹) ^ M := pow_pos (inv_pos.mpr hα0) M
  have hCd : (0 : ℝ) ≤ C / (1 - ρ) := div_nonneg hC hden.le
  have hkey := pow_balancedDepth_le hα hρ hR M
  -- the inner factor
  have hinner : (α⁻¹) ^ M + C * ρ ^ M' / (1 - ρ) ≤ (α⁻¹) ^ M * (1 + C / (1 - ρ)) := by
    have h2 : C * ρ ^ M' / (1 - ρ) = C / (1 - ρ) * ρ ^ M' := by ring
    have h3 : C / (1 - ρ) * ρ ^ M' ≤ C / (1 - ρ) * (α⁻¹) ^ M := by gcongr
    rw [h2]
    nlinarith [h3]
  have hinner0 : (0 : ℝ) ≤ (α⁻¹) ^ M + C * ρ ^ M' / (1 - ρ) := by
    have h2 : (0 : ℝ) ≤ C * ρ ^ M' / (1 - ρ) :=
      div_nonneg (mul_nonneg hC (pow_nonneg hρ0.le _)) hden.le
    linarith
  -- the power factor
  have hpow := two_pow_balancedDepth_le (L := L) (R := R) hL hR M
  have hpow0 : (0 : ℝ) ≤ 2 * (2 : ℝ) ^ ((M : ℝ) * (1 + L / R)) := by positivity
  have hinvpow : (α⁻¹) ^ M = (2 : ℝ) ^ (-L * (M : ℝ)) := by
    rw [← hα, ← Real.rpow_neg (by norm_num), ← Real.rpow_natCast ((2 : ℝ) ^ (-L)) M,
      ← Real.rpow_mul (by norm_num)]
  have hsplit : (M : ℝ) * (1 + L / R) + -L * (M : ℝ) = (M : ℝ) * (1 + L / R - L) := by ring
  calc coverTotal α ρ C M M'
      = (2 : ℝ) ^ (M + M') * ((α⁻¹) ^ M + C * ρ ^ M' / (1 - ρ)) := rfl
    _ ≤ (2 * (2 : ℝ) ^ ((M : ℝ) * (1 + L / R))) * ((α⁻¹) ^ M * (1 + C / (1 - ρ))) :=
        mul_le_mul hpow hinner hinner0 hpow0
    _ = 2 * (1 + C / (1 - ρ)) *
          ((2 : ℝ) ^ ((M : ℝ) * (1 + L / R)) * (2 : ℝ) ^ (-L * (M : ℝ))) := by
        rw [hinvpow]; ring
    _ = 2 * (1 + C / (1 - ρ)) * (2 : ℝ) ^ ((M : ℝ) * (1 + L / R - L)) := by
        rw [← Real.rpow_add (by norm_num), hsplit]

/-- `T > 0`, so its logarithm is the honest thing to bound. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem coverTotal_pos (hα : 0 < α) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hC : 0 ≤ C) (M M' : ℕ) :
    0 < coverTotal α ρ C M M' := by
  have hden : (0 : ℝ) < 1 - ρ := by linarith
  have h1 : (0 : ℝ) < (α⁻¹) ^ M := pow_pos (inv_pos.mpr hα) M
  have h2 : (0 : ℝ) ≤ C * ρ ^ M' / (1 - ρ) :=
    div_nonneg (mul_nonneg hC (pow_nonneg hρ0 _)) hden.le
  have h3 : (0 : ℝ) < (2 : ℝ) ^ (M + M') := by positivity
  exact mul_pos h3 (by linarith)

/-- **M2 Theorem 2(i), verbatim.**  At the balanced depth `M' = ⌈M·L/R⌉`,
`log₂ T ≤ 1 + log₂(1 + C/(1-ρ)) + M·(1 - (L-1)(R-1))/R`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem logb_coverTotal_balancedDepth_le (hα : (2 : ℝ) ^ L = α) (hρ : (2 : ℝ) ^ (-R) = ρ)
    (hL : 0 < L) (hR : 0 < R) (hC : 0 ≤ C) (M : ℕ) :
    Real.logb 2 (coverTotal α ρ C M (balancedDepth L R M))
      ≤ 1 + Real.logb 2 (1 + C / (1 - ρ))
        + (M : ℝ) * ((1 - (L - 1) * (R - 1)) / R) := by
  have hρ0 : 0 < ρ := by rw [← hρ]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hρ1 : ρ < 1 := by
    rw [← hρ]; exact Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hden : (0 : ℝ) < 1 - ρ := by linarith
  have hα1 : 1 < α := by
    have h0 : (2 : ℝ) ^ (0 : ℝ) < (2 : ℝ) ^ L :=
      (Real.rpow_lt_rpow_left_iff one_lt_two).mpr hL
    rw [Real.rpow_zero, hα] at h0; exact h0
  have hCd : (0 : ℝ) < 1 + C / (1 - ρ) := by
    have : (0 : ℝ) ≤ C / (1 - ρ) := div_nonneg hC hden.le
    linarith
  have hTpos := coverTotal_pos (α := α) (ρ := ρ) (C := C) (by linarith) hρ0.le hρ1 hC
    M (balancedDepth L R M)
  have hbd := coverTotal_balancedDepth_le hα hρ hL hR hC M
  have hmono := Real.logb_le_logb_of_le one_lt_two hTpos hbd
  refine hmono.trans (le_of_eq ?_)
  have hrp : (0 : ℝ) < (2 : ℝ) ^ ((M : ℝ) * (1 + L / R - L)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  rw [Real.logb_mul (by positivity) hrp.ne', Real.logb_mul (by norm_num) hCd.ne',
    Real.logb_self_eq_one (by norm_num), Real.logb_rpow (by norm_num) (by norm_num),
    slope_eq hR.ne']

/-! ## "Certified depths exist" -/

/-- The bound of Theorem 2(i) tends to `-∞` in `M` once the slope is negative. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tendsto_bound_atBot {c s : ℝ} (hs : s < 0) :
    Tendsto (fun M : ℕ => c + (M : ℝ) * s) atTop atBot :=
  tendsto_atBot_add_const_left atTop c
    (Filter.Tendsto.atTop_mul_const_of_neg hs tendsto_natCast_atTop_atTop)

/-- **The covering total tends to zero along the balanced ray.**  This is the content of the
note's `⟶ -∞`, in the form the engine consumes. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tendsto_coverTotal_balancedDepth (hα : (2 : ℝ) ^ L = α) (hρ : (2 : ℝ) ^ (-R) = ρ)
    (hL : 0 < L) (hR : 0 < R) (hC : 0 ≤ C) (hs : 1 + L / R - L < 0) :
    Tendsto (fun M : ℕ => coverTotal α ρ C M (balancedDepth L R M)) atTop (nhds 0) := by
  have hρ0 : 0 < ρ := by rw [← hρ]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hρ1 : ρ < 1 := by
    rw [← hρ]; exact Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hα1 : 1 < α := by
    have h0 : (2 : ℝ) ^ (0 : ℝ) < (2 : ℝ) ^ L :=
      (Real.rpow_lt_rpow_left_iff one_lt_two).mpr hL
    rw [Real.rpow_zero, hα] at h0; exact h0
  set q : ℝ := (2 : ℝ) ^ (1 + L / R - L) with hqdef
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two hs
  have hqpow : ∀ M : ℕ, (2 : ℝ) ^ ((M : ℝ) * (1 + L / R - L)) = q ^ M := by
    intro M
    rw [hqdef, ← Real.rpow_natCast ((2 : ℝ) ^ (1 + L / R - L)) M,
      ← Real.rpow_mul (by norm_num), mul_comm]
  have hg : Tendsto (fun M : ℕ => 2 * (1 + C / (1 - ρ)) * q ^ M) atTop (nhds 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1).const_mul (2 * (1 + C / (1 - ρ)))
  refine squeeze_zero (g := fun M : ℕ => 2 * (1 + C / (1 - ρ)) * q ^ M)
    (fun M => (coverTotal_pos (by linarith) hρ0.le hρ1 hC M _).le) (fun M => ?_) hg
  exact (coverTotal_balancedDepth_le hα hρ hL hR hC M).trans (by rw [hqpow M])

/-- **Certified depths exist, and they are cofinal.**  Every threshold `ε > 0` is eventually
cleared along the balanced ray. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem eventually_coverTotal_balancedDepth_lt (hα : (2 : ℝ) ^ L = α)
    (hρ : (2 : ℝ) ^ (-R) = ρ) (hL : 0 < L) (hR : 0 < R) (hC : 0 ≤ C)
    (hs : 1 + L / R - L < 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ M : ℕ in atTop, coverTotal α ρ C M (balancedDepth L R M) < ε :=
  (tendsto_coverTotal_balancedDepth hα hρ hL hR hC hs).eventually (gt_mem_nhds hε)

/-- **The explicit certified depth.**  If the affine bound of Theorem 2(i) is already below
`log₂ ε` at `M`, then `M` certifies: no limit is needed, and this is the form M2
Corollary 3 evaluates at `2+√5` and at the first cubic firing. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem coverTotal_balancedDepth_lt_of_logb_le (hα : (2 : ℝ) ^ L = α)
    (hρ : (2 : ℝ) ^ (-R) = ρ) (hL : 0 < L) (hR : 0 < R) (hC : 0 ≤ C) {ε : ℝ} (hε : 0 < ε)
    {M : ℕ}
    (hM : 1 + Real.logb 2 (1 + C / (1 - ρ)) + (M : ℝ) * ((1 - (L - 1) * (R - 1)) / R)
            < Real.logb 2 ε) :
    coverTotal α ρ C M (balancedDepth L R M) < ε := by
  have hρ0 : 0 < ρ := by rw [← hρ]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hρ1 : ρ < 1 := by
    rw [← hρ]; exact Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hα1 : 1 < α := by
    have h0 : (2 : ℝ) ^ (0 : ℝ) < (2 : ℝ) ^ L :=
      (Real.rpow_lt_rpow_left_iff one_lt_two).mpr hL
    rw [Real.rpow_zero, hα] at h0; exact h0
  have hTpos := coverTotal_pos (α := α) (ρ := ρ) (C := C) (by linarith) hρ0.le hρ1 hC
    M (balancedDepth L R M)
  have h := (logb_coverTotal_balancedDepth_le hα hρ hL hR hC M).trans_lt hM
  exact (Real.logb_lt_logb_iff one_lt_two hTpos hε).mp h

/-! ## Degree two: the engine of `BB61/Covering.lean` on the balanced ray -/

namespace QuadSetup

variable (P : QuadSetup)

/-- `α = 2^L` for `L = logAlpha`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem two_rpow_logAlpha : (2 : ℝ) ^ P.logAlpha = P.α :=
  Real.rpow_logb (by norm_num) (by norm_num) P.alpha_pos

/-- `ρ = 2^{-R}` for `R = logRhoInv` and `ρ = |β|`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem two_rpow_neg_logRhoInv (hβ : P.β ≠ 0) : (2 : ℝ) ^ (-P.logRhoInv) = |P.β| := by
  have h0 : 0 < |P.β| := abs_pos.mpr hβ
  simp only [logRhoInv, Real.logb_inv, neg_neg]
  exact Real.rpow_logb (by norm_num) (by norm_num) h0

/-- **The engine's certificate value is the covering total**, times the point-centred
engine's own factor `2(2K+1)`, and with the note's `C_α = |β - 1|` replaced by the bound
`1 + |β|` that `BB61/Covering.lean` carries.  So Theorem 2(i) applies to it verbatim. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cert_eq_coverTotal (M M' K : ℕ) :
    ((2 ^ M * 2 ^ M' * (2 * K + 1) : ℕ) : ℝ) * (2 * P.delta M M')
      = 2 * (2 * (K : ℝ) + 1) * coverTotal P.α |P.β| (1 + |P.β|) M M' := by
  rw [delta, coverTotal]
  push_cast
  ring

/-- **M2 Theorem 2(i) at degree two**, in the folder's own constants.  Note that the
constant `1 + (1+ρ)/(1-ρ)` is exactly the quantity `QuadSetup.intBound` rounds up: the
engine's integer-part budget and Theorem 2(i)'s additive constant are the same number. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem routeA_depth_bound (hβ : P.β ≠ 0) (M : ℕ) :
    Real.logb 2 (coverTotal P.α |P.β| (1 + |P.β|) M
        (balancedDepth P.logAlpha P.logRhoInv M))
      ≤ 1 + Real.logb 2 (1 + (1 + |P.β|) / (1 - |P.β|))
        + (M : ℝ) * ((1 - (P.logAlpha - 1) * (P.logRhoInv - 1)) / P.logRhoInv) :=
  BB61.logb_coverTotal_balancedDepth_le P.two_rpow_logAlpha (P.two_rpow_neg_logRhoInv hβ)
    P.logAlpha_pos (P.logRhoInv_pos hβ) (by positivity) M

/-- **The hinge**: the slope of Theorem 2(i) is negative exactly when Route A fires.  Left
to right this is Proposition 1; right to left it is the reason the balanced ray is the right
one to run the engine along. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem slope_neg_iff_routeAExponent_lt_one (hβ : P.β ≠ 0) :
    1 + P.logAlpha / P.logRhoInv - P.logAlpha < 0 ↔ P.routeAExponent < 1 := by
  rw [slope_neg_iff (P.logRhoInv_pos hβ), ← P.routeAExponent_lt_one_iff_one_lt_normalForm hβ]

/-- **Certified depths exist**, and they are cofinal: for all large `M` the engine's numeric
certificate holds at the balanced pair `(M, ⌈M·L/R⌉)` with `K = intBound`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem eventually_certificate_balancedDepth (hβ : P.β ≠ 0) (h : P.routeAExponent < 1) :
    ∀ᶠ M : ℕ in atTop,
      ((2 ^ M * 2 ^ (balancedDepth P.logAlpha P.logRhoInv M) * (2 * P.intBound + 1) : ℕ) : ℝ)
          * (2 * P.delta M (balancedDepth P.logAlpha P.logRhoInv M)) < 1 := by
  have hs : 1 + P.logAlpha / P.logRhoInv - P.logAlpha < 0 :=
    (P.slope_neg_iff_routeAExponent_lt_one hβ).mpr h
  have hc0 : (0 : ℝ) < 2 * (2 * (P.intBound : ℝ) + 1) := by positivity
  have hev := eventually_coverTotal_balancedDepth_lt P.two_rpow_logAlpha
    (P.two_rpow_neg_logRhoInv hβ) P.logAlpha_pos (P.logRhoInv_pos hβ)
    (by positivity : (0 : ℝ) ≤ 1 + |P.β|) hs
    (ε := (2 * (2 * (P.intBound : ℝ) + 1))⁻¹) (by positivity)
  filter_upwards [hev] with M hM
  rw [P.cert_eq_coverTotal M _ P.intBound]
  have hlt := mul_lt_mul_of_pos_left hM hc0
  rwa [mul_inv_cancel₀ hc0.ne'] at hlt

/-- **The explicit certified depth**, degree two.  A single numeric inequality on `M` — the
affine bound of Theorem 2(i) below `-log₂(2(2K+1))` — already produces the certificate; no
limit is taken.  This is the shape M2 Corollary 3 evaluates. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem certificate_of_balancedDepth_bound (hβ : P.β ≠ 0) {M : ℕ}
    (hM : 1 + Real.logb 2 (1 + (1 + |P.β|) / (1 - |P.β|))
            + (M : ℝ) * ((1 - (P.logAlpha - 1) * (P.logRhoInv - 1)) / P.logRhoInv)
          < -Real.logb 2 (2 * (2 * (P.intBound : ℝ) + 1))) :
    ((2 ^ M * 2 ^ (balancedDepth P.logAlpha P.logRhoInv M) * (2 * P.intBound + 1) : ℕ) : ℝ)
        * (2 * P.delta M (balancedDepth P.logAlpha P.logRhoInv M)) < 1 := by
  have hc0 : (0 : ℝ) < 2 * (2 * (P.intBound : ℝ) + 1) := by positivity
  have hlog : -Real.logb 2 (2 * (2 * (P.intBound : ℝ) + 1))
      = Real.logb 2 (2 * (2 * (P.intBound : ℝ) + 1))⁻¹ := (Real.logb_inv _ _).symm
  have hT := coverTotal_balancedDepth_lt_of_logb_le P.two_rpow_logAlpha
    (P.two_rpow_neg_logRhoInv hβ) P.logAlpha_pos (P.logRhoInv_pos hβ)
    (by positivity : (0 : ℝ) ≤ 1 + |P.β|)
    (ε := (2 * (2 * (P.intBound : ℝ) + 1))⁻¹) (by positivity) (by rw [← hlog]; exact hM)
  rw [P.cert_eq_coverTotal M _ P.intBound]
  have hlt := mul_lt_mul_of_pos_left hT hc0
  rwa [mul_inv_cancel₀ hc0.ne'] at hlt

/-- **M2 Theorem 2, (i) ⇒ (ii).**  The uniformly avoided interval, produced at a *named*
depth `(M, ⌈M·L/R⌉)`.  `BB61/Criterion.lean` reaches the same conclusion through an
existential rational ray from `exists_rat_btwn`; this is the note's own route, and it comes
with the effective bound `routeA_depth_bound`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_avoided_interval_at_balancedDepth (hβ : P.β ≠ 0) (h : P.routeAExponent < 1) :
    ∃ x r : ℝ, 0 < r ∧ Set.Ioo (x - r) (x + r) ⊆ Set.Ioo 0 1 ∧
      ∀ (ε : ℕ → Bool) (n : ℕ),
        Int.fract (piVal P.α ε * P.α ^ n) ∉ Set.Ioo (x - r) (x + r) := by
  obtain ⟨M, hM⟩ := (P.eventually_certificate_balancedDepth hβ h).exists
  exact P.exists_avoided_interval M _ P.intBound P.intBound_spec hM

/-- **M2 Theorem 2(iv) through (i).**  Problem 10.61 at every `α` with `A(α) < 1`, proved
along the balanced ray. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem not_equidistributed_at_balancedDepth (hβ : P.β ≠ 0) (h : P.routeAExponent < 1) :
    ∀ ξ ∈ cantorSet P.α, ¬ IsEquidistributedModuloOne fun n : ℕ => ξ * P.α ^ n := by
  obtain ⟨x, r, hr, hsub, havoid⟩ := P.exists_avoided_interval_at_balancedDepth hβ h
  rintro ξ ⟨ε, rfl⟩
  exact not_equidistributed_of_avoided hr hsub (havoid ε)

end QuadSetup

end BB61

end
