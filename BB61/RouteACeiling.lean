/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.Criterion
import BB61.Ladder
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# M1 Corollary 5: the lower bound on `ρ`, and the ceiling `α > 2^d`

`BB61/Criterion.lean` and `BB61/BoxDim.lean` carry Corollary 5's *effective* half — the
Route A exponent

`A(α) = log 2 / log α + log 2 / log (1/ρ)`   (`QuadSetup.routeAExponent`)

bounds `dim_B X(α)` and `A(α) < 1` proves Problem 10.61 at `α`.  This file adds the
**negative** half, the one clause of the note that was still prose:

> For `d ≥ 2`, `ρ ≥ α^{-1/(d-1)}` and therefore `A(α) ≥ d·log 2 / log α`, so Route A can
> fire only when `α > 2^d`.

The proof is one line of arithmetic on the norm, `1 ≤ |N(α)| = α·∏_{j≥2}|α_j| ≤ α·ρ^{d-1}`,
and the file formalises it at **general degree**: for a monic `p ∈ ℤ[X]` with nonzero
constant term whose complex roots are `α` together with a multiset `s` of modulus `≤ ρ`,

* `one_le_mul_pow_of_monic_int` : `1 ≤ α · ρ ^ card s` — the norm bound.  The product of
  the roots is `± p.coeff 0`, a *nonzero integer*, hence at least `1` in modulus; that is
  the only place integrality is used.
* `card_add_one_eq_natDegree` : `card s + 1 = p.natDegree`, i.e. `card s = d - 1`.
* `rpow_neg_inv_le_of_one_le_mul_pow` : `α ^ (-1/(d-1)) ≤ ρ`, the note's own shape.
* `routeA_ge_of_one_le_mul_pow` : `d · log2/log α ≤ A(α)`.
* `two_pow_lt_of_routeA_lt_one` and `two_pow_natDegree_lt_of_routeA_lt_one` :
  **`A(α) < 1` forces `2^d < α`.**

The Lean setting of this root fixes `d = 2`, where `N(α) = αβ = -b` and the whole bound is
the single identity `α·|β| = |b| ≥ 1`:

* `QuadSetup.one_le_alpha_mul_abs_beta` / `QuadSetup.inv_alpha_le_abs_beta` :
  `1 ≤ α|β|`, i.e. `ρ ≥ 1/α` — the *proof* of the empirical inequality that M1
  Observation 16 explains (`BB61/Plateau.lean` supplies the equality case `|b| = 1`);
* `QuadSetup.four_lt_alpha_of_routeAExponent_lt_one` : `A(α) < 1 → 4 < α`;
* `QuadSetup.one_le_routeAExponent_of_alpha_le_four` : the contrapositive —
  **Route A never touches the hard slice `2 < α ≤ 4`**, so M0's sixteen certificates,
  all of which live there, are out of its reach by a theorem and not by accident.

The degenerate integer case `β = 0` is the note's `d = 1`, and it is included: there the
second summand of `A(α)` is `0` (`QuadSetup.routeAExponent_of_beta_eq_zero`) and the
ceiling reads `2^1 < α`.  Uniformly, at either degree,
`QuadSetup.two_lt_alpha_of_routeAExponent_lt_one` : Route A never fires below `α = 2`,
which is exactly Problem 10.61's own hypothesis.

That the general lemma really is about this setting is checked rather than asserted:
`QuadSetup.quadPoly` is `X² - aX - b`, `quadPoly_roots` computes its complex roots as
`{α, β}`, and `one_le_alpha_mul_abs_beta_of_monic` re-derives the degree-two bound as the
general one at `d = 2`.

## References

* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*,
  Cambridge Tracts in Math. 193, CUP 2012.  Problem 10.61.
* `note-1061-M1.html` Corollary 5 (the Route A ceiling); `note-1061-M0.html` §7 for the
  enumeration in which `min A(α)·log₂ α` is exactly `2` (quadratic) and exactly `3`
  (cubic), i.e. the bound is sharp.  Numerics `BB61/m1_cor5.py`.
-/

noncomputable section

namespace BB61

open Filter Topology

/-! ## The norm bound, at general degree -/

/-- `‖∏ s‖ ≤ ρ ^ card s` for a multiset of complex numbers of modulus at most `ρ`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem norm_multisetProd_le_pow {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∀ s : Multiset ℂ, (∀ z ∈ s, ‖z‖ ≤ ρ) → ‖s.prod‖ ≤ ρ ^ Multiset.card s := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons a t ih =>
      intro h
      have ha : ‖a‖ ≤ ρ := h a (Multiset.mem_cons_self a t)
      have ht : ∀ z ∈ t, ‖z‖ ≤ ρ := fun z hz => h z (Multiset.mem_cons_of_mem hz)
      rw [Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ]
      calc ‖a‖ * ‖t.prod‖ ≤ ρ * ρ ^ Multiset.card t :=
            mul_le_mul ha (ih ht) (norm_nonneg _) hρ
        _ = ρ ^ Multiset.card t * ρ := mul_comm _ _

/-- **M1 Corollary 5, the lower bound on `ρ`, at general degree.**  If `α` is a positive
real root of a monic integer polynomial `p` with `p(0) ≠ 0`, and the remaining complex
roots `s` (with multiplicity) all have modulus at most `ρ`, then `1 ≤ α · ρ ^ card s`.

This is the note's `1 ≤ |N(α)| = α ∏_{j≥2}|α_j| ≤ α ρ^{d-1}`.  Integrality enters exactly
once: the product of *all* the roots is `± p.coeff 0`, a nonzero rational integer. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem one_le_mul_pow_of_monic_int {p : Polynomial ℤ} (hp : p.Monic) (h0 : p.coeff 0 ≠ 0)
    {α ρ : ℝ} (hα : 0 < α) (hρ : 0 ≤ ρ) {s : Multiset ℂ}
    (hroots : (p.map (Int.castRingHom ℂ)).roots = (α : ℂ) ::ₘ s)
    (hs : ∀ z ∈ s, ‖z‖ ≤ ρ) :
    1 ≤ α * ρ ^ Multiset.card s := by
  set q : Polynomial ℂ := p.map (Int.castRingHom ℂ) with hq
  have hqm : q.Monic := hp.map _
  have hsp : q.Splits := IsAlgClosed.splits q
  have hcoeff : q.coeff 0 = ((p.coeff 0 : ℤ) : ℂ) := by
    simp [hq, Polynomial.coeff_map]
  have hprod : q.coeff 0 = (-1) ^ q.natDegree * q.roots.prod :=
    hsp.coeff_zero_eq_prod_roots_of_monic hqm
  -- the product of the roots is a nonzero integer in modulus, hence at least one
  have hone : (1 : ℝ) ≤ ‖q.roots.prod‖ := by
    have h1 : ‖q.coeff 0‖ = ‖q.roots.prod‖ := by
      rw [hprod, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have h2 : ‖q.coeff 0‖ = |((p.coeff 0 : ℤ) : ℝ)| := by
      rw [hcoeff, Complex.norm_intCast]
    have h3 : (1 : ℤ) ≤ |p.coeff 0| := Int.one_le_abs h0
    have h4 : (1 : ℝ) ≤ |((p.coeff 0 : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast h3
    rw [← h1, h2]
    exact h4
  -- split off the distinguished root and bound the rest
  rw [hroots, Multiset.prod_cons, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hα] at hone
  refine hone.trans ?_
  exact mul_le_mul_of_nonneg_left (norm_multisetProd_le_pow hρ s hs) hα.le

/-- The remaining roots number `d - 1`: `card s + 1 = deg p`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem card_add_one_eq_natDegree {p : Polynomial ℤ} (hp : p.Monic) {α : ℝ} {s : Multiset ℂ}
    (hroots : (p.map (Int.castRingHom ℂ)).roots = (α : ℂ) ::ₘ s) :
    Multiset.card s + 1 = p.natDegree := by
  have hqm : (p.map (Int.castRingHom ℂ)).Monic := hp.map _
  have hsp : (p.map (Int.castRingHom ℂ)).Splits := IsAlgClosed.splits _
  have h1 : (p.map (Int.castRingHom ℂ)).natDegree = p.natDegree := hp.natDegree_map _
  have h2 := hsp.natDegree_eq_card_roots
  rw [h1, hroots] at h2
  simp only [Multiset.card_cons] at h2
  omega

/-- The note's own shape of the bound: `α ^ (-1/(d-1)) ≤ ρ`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem rpow_neg_inv_le_of_one_le_mul_pow {α ρ : ℝ} {n : ℕ} (hn : 0 < n) (hα : 0 < α)
    (hρ : 0 < ρ) (h : 1 ≤ α * ρ ^ n) : α ^ (-(n : ℝ)⁻¹) ≤ ρ := by
  have hn0 : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hinv : α⁻¹ ≤ ρ ^ n := by
    rw [inv_le_iff_one_le_mul₀ hα]
    linarith [h]
  have hstep : (α⁻¹) ^ ((n : ℝ)⁻¹) ≤ (ρ ^ n) ^ ((n : ℝ)⁻¹) :=
    Real.rpow_le_rpow (by positivity) hinv (by positivity)
  have hL : (α⁻¹) ^ ((n : ℝ)⁻¹) = α ^ (-(n : ℝ)⁻¹) := by
    rw [Real.inv_rpow hα.le, ← Real.rpow_neg hα.le]
  have hR : ((ρ : ℝ) ^ n) ^ ((n : ℝ)⁻¹) = ρ := by
    rw [← Real.rpow_natCast ρ n, ← Real.rpow_mul hρ.le, mul_inv_cancel₀ hn0, Real.rpow_one]
  rwa [hL, hR] at hstep

/-! ## From the norm bound to the ceiling -/

/-- The bound in logarithmic form: `n · log(1/ρ) ≤ log α`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem mul_log_inv_le_log {α ρ : ℝ} {n : ℕ} (hα : 0 < α) (hρ : 0 < ρ)
    (h : 1 ≤ α * ρ ^ n) : (n : ℝ) * Real.log ρ⁻¹ ≤ Real.log α := by
  have h1 : Real.log 1 ≤ Real.log (α * ρ ^ n) := Real.log_le_log (by norm_num) h
  rw [Real.log_one, Real.log_mul (ne_of_gt hα) (by positivity), Real.log_pow] at h1
  rw [Real.log_inv]
  linarith

/-- **M1 Corollary 5's ceiling, general degree, the inequality.**  With `d = n + 1` the
degree, `d · log2/log α ≤ A(α)`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem routeA_ge_of_one_le_mul_pow {α ρ : ℝ} {n : ℕ} (hα : 1 < α) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (h : 1 ≤ α * ρ ^ n) :
    ((n : ℝ) + 1) * (Real.log 2 / Real.log α)
      ≤ Real.log 2 / Real.log α + Real.log 2 / Real.log ρ⁻¹ := by
  have hla : 0 < Real.log α := Real.log_pos hα
  have hlr : 0 < Real.log ρ⁻¹ := by
    rw [Real.log_inv]; exact neg_pos.mpr (Real.log_neg hρ0 hρ1)
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have key : (n : ℝ) * Real.log ρ⁻¹ ≤ Real.log α :=
    mul_log_inv_le_log (by linarith) hρ0 h
  have hmain : (n : ℝ) * (Real.log 2 / Real.log α) ≤ Real.log 2 / Real.log ρ⁻¹ := by
    rw [show (n : ℝ) * (Real.log 2 / Real.log α) = ((n : ℝ) * Real.log 2) / Real.log α by ring,
      div_le_div_iff₀ hla hlr]
    nlinarith [mul_le_mul_of_nonneg_left key hl2.le]
  nlinarith [hmain]

/-- **M1 Corollary 5's ceiling, general degree.**  `A(α) < 1` forces `2^{n+1} < α`; with
`n + 1 = d` the degree, that is the note's *Route A can fire only when `α > 2^d`*. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem two_pow_lt_of_routeA_lt_one {α ρ : ℝ} {n : ℕ} (hα : 1 < α) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (h : 1 ≤ α * ρ ^ n)
    (hA : Real.log 2 / Real.log α + Real.log 2 / Real.log ρ⁻¹ < 1) :
    (2 : ℝ) ^ (n + 1) < α := by
  have hla : 0 < Real.log α := Real.log_pos hα
  have h1 : ((n : ℝ) + 1) * (Real.log 2 / Real.log α) < 1 :=
    lt_of_le_of_lt (routeA_ge_of_one_le_mul_pow hα hρ0 hρ1 h) hA
  have h2 : ((n : ℝ) + 1) * Real.log 2 < Real.log α := by
    rw [show ((n : ℝ) + 1) * (Real.log 2 / Real.log α)
        = (((n : ℝ) + 1) * Real.log 2) / Real.log α by ring, div_lt_one hla] at h1
    exact h1
  have h3 : Real.log ((2 : ℝ) ^ (n + 1)) = ((n : ℝ) + 1) * Real.log 2 := by
    rw [Real.log_pow]; push_cast; ring
  have h4 : Real.log ((2 : ℝ) ^ (n + 1)) < Real.log α := by rw [h3]; exact h2
  have := Real.exp_lt_exp.mpr h4
  rwa [Real.exp_log (by positivity), Real.exp_log (by linarith)] at this

/-- The ceiling stated in the degree: `A(α) < 1` forces `2^d < α`, `d = deg p`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem two_pow_natDegree_lt_of_routeA_lt_one {p : Polynomial ℤ} (hp : p.Monic)
    (h0 : p.coeff 0 ≠ 0) {α ρ : ℝ} (hα : 1 < α) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {s : Multiset ℂ} (hroots : (p.map (Int.castRingHom ℂ)).roots = (α : ℂ) ::ₘ s)
    (hs : ∀ z ∈ s, ‖z‖ ≤ ρ)
    (hA : Real.log 2 / Real.log α + Real.log 2 / Real.log ρ⁻¹ < 1) :
    (2 : ℝ) ^ p.natDegree < α := by
  have hcard := card_add_one_eq_natDegree hp hroots
  have hbound := one_le_mul_pow_of_monic_int hp h0 (by linarith) hρ0.le hroots hs
  rw [← hcard]
  exact two_pow_lt_of_routeA_lt_one hα hρ0 hρ1 hbound hA

namespace QuadSetup

variable (P : QuadSetup)

/-! ## Degree two: `α|β| = |b| ≥ 1` -/

/-- `β ≠ 0` is the same as `b ≠ 0`: the norm of `α` is `-b`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem b_ne_zero_of_beta_ne_zero (hβ : P.β ≠ 0) : P.b ≠ 0 := by
  intro hb
  have h : P.α * P.β = 0 := by rw [P.alpha_mul_beta, hb]; norm_num
  rcases mul_eq_zero.mp h with h' | h'
  · exact absurd h' (ne_of_gt P.alpha_pos)
  · exact hβ h'

/-- **M1 Corollary 5's lower bound on `ρ` at degree two.**  `α·|β| = |b| ≥ 1`, so
`ρ = |β| ≥ 1/α = α^{-1/(d-1)}`.  This is the *proof* of M0's empirical `ρ ≥ 1/α`;
`BB61/Plateau.lean` (M1 Observation 16(ii)) is the equality case `|b| = 1`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem one_le_alpha_mul_abs_beta (hβ : P.β ≠ 0) : 1 ≤ P.α * |P.β| := by
  have h : P.α * |P.β| = |(P.b : ℝ)| := by
    rw [← abs_of_pos P.alpha_pos, ← abs_mul, P.alpha_mul_beta, abs_neg]
  rw [h, ← Int.cast_abs]
  exact_mod_cast Int.one_le_abs (P.b_ne_zero_of_beta_ne_zero hβ)

/-- `ρ ≥ 1/α`, the note's `ρ ≥ α^{-1/(d-1)}` at `d = 2`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem inv_alpha_le_abs_beta (hβ : P.β ≠ 0) : P.α⁻¹ ≤ |P.β| := by
  have h := P.one_le_alpha_mul_abs_beta hβ
  rw [inv_eq_one_div, div_le_iff₀ P.alpha_pos]
  linarith

/-! ## Degree two: the ceiling -/

/-- The second summand of `A(α)` is nonnegative — also in the degenerate case `β = 0`,
where Lean's junk value makes it `0`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem log_two_div_log_inv_abs_beta_nonneg : 0 ≤ Real.log 2 / Real.log |P.β|⁻¹ := by
  rcases eq_or_ne P.β 0 with h | h
  · simp [h]
  · have hb0 : 0 < |P.β| := abs_pos.mpr h
    have hlb : 0 < Real.log |P.β|⁻¹ := by
      rw [Real.log_inv]; exact neg_pos.mpr (Real.log_neg hb0 P.abs_beta_lt_one)
    exact div_nonneg (Real.log_nonneg one_le_two) hlb.le

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem log_two_div_log_alpha_le_routeAExponent :
    Real.log 2 / Real.log P.α ≤ P.routeAExponent := by
  rw [routeAExponent]
  linarith [P.log_two_div_log_inv_abs_beta_nonneg]

/-- **Route A never fires below `α = 2`** — at either degree, and so in particular never
outside Problem 10.61's own hypothesis `α > 2`.  This is the `d = 1` case of `α > 2^d`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem two_lt_alpha_of_routeAExponent_lt_one (h : P.routeAExponent < 1) : 2 < P.α := by
  have hla : 0 < Real.log P.α := Real.log_pos P.one_lt
  have h1 : Real.log 2 / Real.log P.α < 1 :=
    lt_of_le_of_lt P.log_two_div_log_alpha_le_routeAExponent h
  rw [div_lt_one hla] at h1
  have := Real.exp_lt_exp.mpr h1
  rwa [Real.exp_log (by norm_num), Real.exp_log (by linarith [P.one_lt])] at this

/-- In the degenerate integer case `β = 0` (the note's `d = 1`) the window is a point and
`A(α)` is just `dim_B C(α)`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem routeAExponent_of_beta_eq_zero (hβ : P.β = 0) :
    P.routeAExponent = Real.log 2 / Real.log P.α := by
  rw [routeAExponent, hβ]; simp

/-- **M1 Corollary 5's ceiling at degree two**: `d·log2/log α ≤ A(α)` with `d = 2`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem two_mul_log_two_div_log_alpha_le_routeAExponent (hβ : P.β ≠ 0) :
    2 * Real.log 2 / Real.log P.α ≤ P.routeAExponent := by
  have hb0 : 0 < |P.β| := abs_pos.mpr hβ
  have hone : 1 ≤ P.α * |P.β| ^ 1 := by
    simpa using P.one_le_alpha_mul_abs_beta hβ
  have hge := routeA_ge_of_one_le_mul_pow (n := 1) P.one_lt hb0 P.abs_beta_lt_one hone
  rw [show ((1 : ℕ) : ℝ) + 1 = 2 by norm_num] at hge
  rw [routeAExponent, show 2 * Real.log 2 / Real.log P.α
    = 2 * (Real.log 2 / Real.log P.α) by ring]
  linarith

/-- **Route A can fire only when `α > 2^d`, at `d = 2`.** -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem four_lt_alpha_of_routeAExponent_lt_one (hβ : P.β ≠ 0) (h : P.routeAExponent < 1) :
    4 < P.α := by
  have hb0 : 0 < |P.β| := abs_pos.mpr hβ
  have hone : 1 ≤ P.α * |P.β| ^ 1 := by
    simpa using P.one_le_alpha_mul_abs_beta hβ
  have hA : Real.log 2 / Real.log P.α + Real.log 2 / Real.log |P.β|⁻¹ < 1 := by
    rw [routeAExponent] at h; exact h
  have := two_pow_lt_of_routeA_lt_one (n := 1) P.one_lt hb0 P.abs_beta_lt_one hone hA
  norm_num at this
  exact this

/-- **Route A never touches the hard slice `2 < α ≤ 4`** — the contrapositive, and the
reason M0's sixteen new certificates are all out of its reach. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem one_le_routeAExponent_of_alpha_le_four (hβ : P.β ≠ 0) (h : P.α ≤ 4) :
    1 ≤ P.routeAExponent := by
  by_contra hcon
  push Not at hcon
  linarith [P.four_lt_alpha_of_routeAExponent_lt_one hβ hcon]

/-! ## The degree-two setting is the general lemma at `d = 2` -/

/-- The defining polynomial `X² - aX - b` of the setting, over `ℤ`. -/
def quadPoly : Polynomial ℤ :=
  Polynomial.X ^ 2 - (Polynomial.C P.a * Polynomial.X + Polynomial.C P.b)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem quadPoly_monic : (P.quadPoly).Monic := by
  refine Polynomial.monic_X_pow_sub (n := 2) ?_
  exact lt_of_le_of_lt Polynomial.degree_linear_le (by norm_num)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem quadPoly_coeff_zero : (P.quadPoly).coeff 0 = -P.b := by
  simp [quadPoly]

/-- `X² - aX - b` factors over `ℂ` as `(X - α)(X - β)`: that is `α + β = a`, `αβ = -b`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem quadPoly_map_eq :
    (P.quadPoly).map (Int.castRingHom ℂ)
      = (Polynomial.X - Polynomial.C (P.α : ℂ)) * (Polynomial.X - Polynomial.C (P.β : ℂ)) := by
  have hsum : ((P.a : ℤ) : ℂ) = (P.α : ℂ) + (P.β : ℂ) := by
    rw [← Complex.ofReal_add, P.alpha_add_beta]; norm_cast
  have hmul : ((P.b : ℤ) : ℂ) = -((P.α : ℂ) * (P.β : ℂ)) := by
    rw [← Complex.ofReal_mul, P.alpha_mul_beta]; push_cast; ring
  have key : (Polynomial.X - Polynomial.C (P.α : ℂ)) * (Polynomial.X - Polynomial.C (P.β : ℂ))
      = Polynomial.X ^ 2 - (Polynomial.C ((P.α : ℂ) + (P.β : ℂ)) * Polynomial.X
        + Polynomial.C (-((P.α : ℂ) * (P.β : ℂ)))) := by
    simp only [Polynomial.C_add, Polynomial.C_neg, Polynomial.C_mul]
    ring
  rw [key, ← hsum, ← hmul]
  simp [quadPoly]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem quadPoly_roots :
    ((P.quadPoly).map (Int.castRingHom ℂ)).roots = (P.α : ℂ) ::ₘ {(P.β : ℂ)} := by
  rw [P.quadPoly_map_eq,
    Polynomial.roots_mul (mul_ne_zero (Polynomial.X_sub_C_ne_zero _)
      (Polynomial.X_sub_C_ne_zero _)),
    Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C, Multiset.singleton_add]

/-- The degree-two bound `1 ≤ α|β|`, obtained from the general lemma at `d = 2` rather
than from `αβ = -b` directly: the two agree. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem one_le_alpha_mul_abs_beta_of_monic (hβ : P.β ≠ 0) :
    1 ≤ P.α * |P.β| ^ Multiset.card ({(P.β : ℂ)} : Multiset ℂ) := by
  refine one_le_mul_pow_of_monic_int P.quadPoly_monic ?_ P.alpha_pos (abs_nonneg _)
    P.quadPoly_roots ?_
  · rw [P.quadPoly_coeff_zero]
    simpa using P.b_ne_zero_of_beta_ne_zero hβ
  · intro z hz
    rw [Multiset.mem_singleton] at hz
    subst hz
    rw [Complex.norm_real, Real.norm_eq_abs]

/-- `deg (X² - aX - b) = 2`, so the general ceiling `2^d < α` reads `4 < α` here. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem quadPoly_natDegree : (P.quadPoly).natDegree = 2 := by
  have := card_add_one_eq_natDegree P.quadPoly_monic P.quadPoly_roots
  simpa using this.symm

end QuadSetup

end BB61

end
