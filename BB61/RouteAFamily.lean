/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.RouteADepth
import BB61.RouteAConstants
import ForMathlib.NumberTheory.PisotNumber
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# M2 Theorem 5: the explicit family `X^d - aX^{d-1} - 1`, in every degree

`BB61/RouteACeiling.lean` says where Route A *cannot* fire; `BB61/RouteANormalForm.lean` says
exactly when it does; `BB61/RouteADepth.lean` says at what depth.  Theorem 5 of
`note-1061-M2.html` supplies the *inhabitants*: for `d ≥ 2` and `a ≥ 3`, the trinomial

`p_{d,a}(X) = X^d - a X^{d-1} - 1`   (`familyPoly`)

is irreducible, its unique root outside the closed unit disc is real and lies in `(a, a+1)`, it
is a Pisot unit of degree `d`, every conjugate has modulus at most `(2/a)^{1/(d-1)}`, and for
`a ≥ 2^{d+1}` the Route A exponent drops below one.  **An explicit infinite family in every
degree.**

## What is here

* **(i)** `card_big_roots_eq_one` — `α` is the only root of modulus `≥ 1`, and it is simple;
  `norm_lt_one_of_mem_roots_of_ne`; `isPisot_family` (`ForMathlib`'s `IsPisot`);
  `minpoly_eq_familyPoly`, hence `familyPoly_irreducible`, `minpoly_natDegree_family`
  (**degree exactly `d`**) and `minpoly_coeff_zero_family` (**a unit**).
* **(ii)** `mul_norm_pow_le_two` / `norm_le_familyConjBound` — `a‖z‖^{d-1} ≤ 2`, i.e.
  `‖z‖ ≤ (2/a)^{1/(d-1)}`.
* **(iii)** `routeA_family_lt_one` — `a ≥ 2^{d+1} ⇒ A(α_{d,a}) < 1`, off the arithmetic
  `1/(d+1) + (d-1)/d = (d²+d-1)/(d²+d) < 1` (`inv_add_inv_lt_one_of_deg`).
* **(iv)** `d = 2`: `familyQuad` is a `QuadSetup`, so the folder's engine applies and the
  conclusion is Problem 10.61 itself — `familyQuad_not_equidistributed` for every `a ≥ 4`, with
  `familyQuad_routeAExponent_lt_one_iff` giving the threshold as an *iff* and
  `familyQuad_four_alpha` identifying the first member as `2 + √5`, the capstone of
  `BB61/RouteA.lean`.  `d = 3`: `norm_sq_mul_eq_one_cubic` (`‖z‖²α = 1`, i.e. `ρ = α^{-1/2}`),
  `routeA_cubic_mul_logb` (`A·log₂ α = 3` — the family sits **on** the Proposition 4 ceiling)
  and `routeA_cubic_lt_one_iff` (`A < 1 ↔ α > 8 ↔ a ≥ 8`).
* Existence: `exists_root_Ioo`, by the intermediate value theorem on `[a, a+1]`, where
  `p(a) = -1` and `p(a+1) = (a+1)^{d-1} - 1 > 0`.

## Two deliberate departures from the note's proof

**Rouché is not used, because Mathlib has no Rouché.**  The note counts the roots outside the
unit circle with Rouché's theorem on `|z| = 1`.  Here the count is elementary and uses only the
constant term.  Every root satisfies `‖z‖^{d-1}‖z - a‖ = 1`, so a root with `‖z‖ ≥ 1` has
`‖z - a‖ ≤ 1`, hence `‖z‖ ≥ a - 1 ≥ 2`, hence `‖z‖^{d-1} ≥ 2`, hence `‖z - a‖ ≤ 1/2` and
`‖z‖ ≥ a - 1/2` (`le_norm_of_one_le_norm`); a root with `‖z‖ < 1` has `‖z - a‖ ≤ a + 1`, hence
`‖z‖^{d-1} ≥ 1/(a+1)` (`inv_le_norm_pow_of_norm_lt_one`).  The product of all the moduli is `1`
because the constant term is `-1`.  If `k ≥ 2` roots were large, then
`(a - 1/2)^{k(d-1)} ≤ (a+1)^{d-k} ≤ (a+1)^{d-2} ≤ (a-1/2)^{2(d-2)}`, while the left side is at
least `(a-1/2)^{2(d-1)}` — and `2(d-1) > 2(d-2)` with base `> 1`.  **Only integer powers occur**,
so no `rpow` and no complex analysis; the sharper bound `a - 1/2` (rather than `a - 1`) is what
makes the inequality strict at the boundary case `a = 3`.

**No calculus at `d = 3`.**  The note gets "exactly one real root" from the critical values of
`p'`.  That is not needed: dividing by `X - α` leaves the *real* quadratic
`X² + (α-a)X + (α²-aα)`, whose discriminant `1/α⁴ - 4/α` is negative for free, and negativity
both forces the remaining pair to be non-real and computes its modulus as
`√(α²-aα) = α^{-1/2}` (`norm_sq_of_quadratic`).

## References

* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*,
  Cambridge Tracts in Math. 193, CUP 2012.  Problem 10.61.
* `note-1061-M2.html` §5 Theorem 5; numerics `BB61/m2_thm5_lean.py`.
-/

noncomputable section

namespace BB61

open Polynomial

/-! ## The polynomial -/

/-- `p_{d,a}(X) = X^d - a X^{d-1} - 1`, the family of M2 Theorem 5. -/
def familyPoly (d a : ℕ) : Polynomial ℤ :=
  X ^ d - C (a : ℤ) * X ^ (d - 1) - 1

variable {d a : ℕ}

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem familyPoly_eq_add : familyPoly d a = X ^ d + (-(C (a : ℤ) * X ^ (d - 1)) - 1) := by
  rw [familyPoly]; ring

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem familyPoly_tail_degree_lt (hd : 1 ≤ d) :
    (-(C (a : ℤ) * X ^ (d - 1)) - 1).degree < (X ^ d : Polynomial ℤ).degree := by
  have h1 : (-(C (a : ℤ) * X ^ (d - 1)) - 1 : Polynomial ℤ).degree ≤ ((d - 1 : ℕ) : WithBot ℕ) := by
    refine (degree_sub_le _ _).trans (max_le ?_ ?_)
    · rw [degree_neg]; exact degree_C_mul_X_pow_le _ _
    · exact degree_one_le.trans (by exact_mod_cast Nat.zero_le (d - 1))
  refine h1.trans_lt ?_
  rw [degree_X_pow]
  exact_mod_cast Nat.sub_lt (by omega) one_pos

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem familyPoly_monic (hd : 1 ≤ d) : (familyPoly d a).Monic := by
  rw [familyPoly_eq_add]
  exact (monic_X_pow d).add_of_left (familyPoly_tail_degree_lt hd)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem familyPoly_natDegree (hd : 1 ≤ d) : (familyPoly d a).natDegree = d := by
  rw [familyPoly_eq_add]
  refine natDegree_eq_of_degree_eq_some ?_
  rw [degree_add_eq_left_of_degree_lt (familyPoly_tail_degree_lt hd), degree_X_pow]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem familyPoly_coeff_zero (hd : 2 ≤ d) : (familyPoly d a).coeff 0 = -1 := by
  have h1 : d ≠ 0 := by omega
  have h2 : d - 1 ≠ 0 := by omega
  simp [familyPoly, coeff_X_pow, Ne.symm h1, Ne.symm h2]

/-! ## Evaluation -/

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem aeval_familyPoly {R : Type*} [CommRing R] [Algebra ℤ R] (x : R) :
    (aeval x) (familyPoly d a) = x ^ d - (a : R) * x ^ (d - 1) - 1 := by
  simp [familyPoly]

/-! ## The real root in `(a, a+1)` -/

@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_root_Ioo (hd : 2 ≤ d) (ha : 3 ≤ a) :
    ∃ α ∈ Set.Ioo ((a : ℝ)) ((a : ℝ) + 1), α ^ d - (a : ℝ) * α ^ (d - 1) - 1 = 0 := by
  set f : ℝ → ℝ := fun x => x ^ d - (a : ℝ) * x ^ (d - 1) - 1 with hf
  have hcont : ContinuousOn f (Set.Icc ((a : ℝ)) ((a : ℝ) + 1)) :=
    (((continuous_pow d).sub ((continuous_const).mul (continuous_pow (d - 1)))).sub
      continuous_const).continuousOn
  have hdd : d - 1 + 1 = d := by omega
  have hfa : f (a : ℝ) = -1 := by
    rw [hf]
    have : (a : ℝ) ^ d = (a : ℝ) * (a : ℝ) ^ (d - 1) := by
      rw [← pow_succ' (a : ℝ) (d - 1), hdd]
    simp only []
    rw [this]; ring
  have ha1 : (1 : ℝ) < (a : ℝ) + 1 := by
    have : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    linarith
  have hfb : f ((a : ℝ) + 1) = ((a : ℝ) + 1) ^ (d - 1) - 1 := by
    rw [hf]
    have : ((a : ℝ) + 1) ^ d = ((a : ℝ) + 1) * ((a : ℝ) + 1) ^ (d - 1) := by
      rw [← pow_succ' ((a : ℝ) + 1) (d - 1), hdd]
    simp only []
    rw [this]; ring
  have hpos : (0 : ℝ) < f ((a : ℝ) + 1) := by
    rw [hfb]
    have : (1 : ℝ) < ((a : ℝ) + 1) ^ (d - 1) := one_lt_pow₀ ha1 (by omega)
    linarith
  have hmem : (0 : ℝ) ∈ Set.Ioo (f (a : ℝ)) (f ((a : ℝ) + 1)) := by
    rw [hfa]; exact ⟨by norm_num, hpos⟩
  obtain ⟨α, hα, hα0⟩ := intermediate_value_Ioo (by linarith : (a : ℝ) ≤ (a : ℝ) + 1) hcont hmem
  exact ⟨α, hα, hα0⟩

/-! ## Multiset helpers -/

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem pow_card_le_multisetProd {c : ℝ} (hc : 0 ≤ c) :
    ∀ s : Multiset ℝ, (∀ x ∈ s, c ≤ x) → c ^ Multiset.card s ≤ s.prod := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons x t ih =>
      intro h
      have hx : c ≤ x := h x (Multiset.mem_cons_self x t)
      have ht : ∀ y ∈ t, c ≤ y := fun y hy => h y (Multiset.mem_cons_of_mem hy)
      have hprod : c ^ Multiset.card t ≤ t.prod := ih ht
      rw [Multiset.prod_cons, Multiset.card_cons, pow_succ]
      calc c ^ Multiset.card t * c ≤ t.prod * c :=
            mul_le_mul_of_nonneg_right hprod hc
        _ = c * t.prod := by ring
        _ ≤ x * t.prod := by
            refine mul_le_mul_of_nonneg_right hx ?_
            exact le_trans (pow_nonneg hc _) hprod
        _ = x * t.prod := rfl
      
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem multisetProd_pow (n : ℕ) :
    ∀ s : Multiset ℝ, s.prod ^ n = (s.map (fun x => x ^ n)).prod := by
  intro s
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x t ih => simp [Multiset.prod_cons, mul_pow, ih]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem norm_multisetProd_eq (s : Multiset ℂ) :
    ‖s.prod‖ = (s.map (fun z => ‖z‖)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x t ih => simp [Multiset.prod_cons, ih]

/-! ## The polynomial over a ring, and the root equation -/

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem familyPoly_map {K : Type*} [CommRing K] (f : ℤ →+* K) :
    (familyPoly d a).map f = X ^ d - C (f (a : ℤ)) * X ^ (d - 1) - 1 := by
  simp [familyPoly]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem eval_familyPoly_map (z : ℂ) :
    ((familyPoly d a).map (Int.castRingHom ℂ)).eval z = z ^ d - (a : ℂ) * z ^ (d - 1) - 1 := by
  rw [familyPoly_map]
  simp

/-- The root equation in the form Theorem 5's proof uses: `z^{d-1}(z - a) = 1`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem root_mul_eq_one (hd : 1 ≤ d) {z : ℂ}
    (hz : z ^ d - (a : ℂ) * z ^ (d - 1) - 1 = 0) :
    z ^ (d - 1) * (z - (a : ℂ)) = 1 := by
  have hdd : d - 1 + 1 = d := by omega
  have hp : z ^ d = z ^ (d - 1) * z := by rw [← pow_succ, hdd]
  rw [hp] at hz
  linear_combination hz

/-- The same, in modulus. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem norm_pow_mul_norm_sub (hd : 1 ≤ d) {z : ℂ}
    (hz : z ^ d - (a : ℂ) * z ^ (d - 1) - 1 = 0) :
    ‖z‖ ^ (d - 1) * ‖z - (a : ℂ)‖ = 1 := by
  have h := root_mul_eq_one (a := a) hd hz
  calc ‖z‖ ^ (d - 1) * ‖z - (a : ℂ)‖ = ‖z ^ (d - 1) * (z - (a : ℂ))‖ := by
        rw [norm_mul, norm_pow]
    _ = 1 := by rw [h, norm_one]

/-! ## The dichotomy: every root is either tiny or within `1/2` of `a` -/

/-- **A root of modulus at least one is within `1/2` of `a`.**  In particular there is no root
on the unit circle: `a - 1/2 ≥ 5/2 > 1`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem le_norm_of_one_le_norm (hd : 2 ≤ d) (ha : 3 ≤ a) {z : ℂ}
    (hz : z ^ d - (a : ℂ) * z ^ (d - 1) - 1 = 0) (h1 : 1 ≤ ‖z‖) :
    (a : ℝ) - 1 / 2 ≤ ‖z‖ := by
  have haR : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hkey := norm_pow_mul_norm_sub (a := a) (by omega : 1 ≤ d) hz
  have hzn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hpow1 : (1 : ℝ) ≤ ‖z‖ ^ (d - 1) := one_le_pow₀ h1
  have hsub_pos : (0 : ℝ) < ‖z - (a : ℂ)‖ := by
    rcases eq_or_lt_of_le (norm_nonneg (z - (a : ℂ))) with h | h
    · exfalso; rw [← h, mul_zero] at hkey; exact absurd hkey (by norm_num)
    · exact h
  have hsub_le : ‖z - (a : ℂ)‖ ≤ 1 := by nlinarith [hkey, hpow1, hsub_pos]
  -- first pass: ‖z‖ ≥ a - 1
  have hna : ‖(a : ℂ)‖ = (a : ℝ) := by
    rw [show ((a : ℂ)) = ((a : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have htri : (a : ℝ) - ‖z - (a : ℂ)‖ ≤ ‖z‖ := by
    have := norm_sub_norm_le (a := (a : ℂ)) (b := (a : ℂ) - z)
    have h2 : ‖z - (a : ℂ)‖ = ‖(a : ℂ) - z‖ := by rw [norm_sub_rev]
    have h3 : ‖(a : ℂ) - ((a : ℂ) - z)‖ = ‖z‖ := by ring_nf
    rw [hna, h3] at this
    linarith [this, h2]
  have hfirst : (a : ℝ) - 1 ≤ ‖z‖ := by linarith
  -- second pass: ‖z‖^{d-1} ≥ 2, so ‖z - a‖ ≤ 1/2
  have h2le : (2 : ℝ) ≤ ‖z‖ ^ (d - 1) := by
    have hbase : (2 : ℝ) ≤ ‖z‖ := by linarith
    have : (2 : ℝ) ^ (d - 1) ≤ ‖z‖ ^ (d - 1) := pow_le_pow_left₀ (by norm_num) hbase _
    have h21 : (2 : ℝ) ≤ (2 : ℝ) ^ (d - 1) := by
      have : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ (d - 1) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      simpa using this
    linarith
  have hhalf : ‖z - (a : ℂ)‖ ≤ 1 / 2 := by nlinarith [hkey, h2le, hsub_pos]
  linarith

/-- **A root of modulus below one has `‖z‖^{d-1} ≥ 1/(a+1)`.** -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem inv_le_norm_pow_of_norm_lt_one (hd : 2 ≤ d) (ha : 3 ≤ a) {z : ℂ}
    (hz : z ^ d - (a : ℂ) * z ^ (d - 1) - 1 = 0) (h1 : ‖z‖ < 1) :
    ((a : ℝ) + 1)⁻¹ ≤ ‖z‖ ^ (d - 1) := by
  have haR : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hkey := norm_pow_mul_norm_sub (a := a) (by omega : 1 ≤ d) hz
  have hna : ‖(a : ℂ)‖ = (a : ℝ) := by
    rw [show ((a : ℂ)) = ((a : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hsub_le : ‖z - (a : ℂ)‖ ≤ (a : ℝ) + 1 := by
    have := norm_sub_le z (a : ℂ)
    rw [hna] at this
    linarith
  have hpow_pos : (0 : ℝ) < ‖z‖ ^ (d - 1) := by
    rcases eq_or_lt_of_le (pow_nonneg (norm_nonneg z) (d - 1)) with h | h
    · exfalso; rw [← h, zero_mul] at hkey; exact absurd hkey (by norm_num)
    · exact h
  rw [inv_le_iff_one_le_mul₀ (by linarith)]
  nlinarith [hkey, hsub_le, hpow_pos]

/-- **M2 Theorem 5(ii).**  Every root of modulus at most one satisfies `a‖z‖^{d-1} ≤ 2` — the
note's `|z| ≤ (2/a)^{1/(d-1)}`, in power form. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem mul_norm_pow_le_two {z : ℂ}
    (hz : z ^ d - (a : ℂ) * z ^ (d - 1) - 1 = 0) (h1 : ‖z‖ ≤ 1) :
    (a : ℝ) * ‖z‖ ^ (d - 1) ≤ 2 := by
  have hna : ‖(a : ℂ)‖ = (a : ℝ) := by
    rw [show ((a : ℂ)) = ((a : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have heq : (a : ℂ) * z ^ (d - 1) = z ^ d - 1 := by linear_combination -hz
  have h2 : (a : ℝ) * ‖z‖ ^ (d - 1) = ‖z ^ d - 1‖ := by
    rw [← heq, norm_mul, norm_pow, hna]
  rw [h2]
  calc ‖z ^ d - 1‖ ≤ ‖z ^ d‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = ‖z‖ ^ d + 1 := by rw [norm_pow, norm_one]
    _ ≤ 1 + 1 := by
        have : ‖z‖ ^ d ≤ 1 := pow_le_one₀ (norm_nonneg z) h1
        linarith
    _ = 2 := by norm_num

/-! ## Exactly one root of modulus at least one

The note proves this with Rouché's theorem.  Mathlib has no Rouché, so the argument here is
a different, elementary one: the product of *all* the roots has modulus `1` (the constant term
is `-1`), each root of modulus `≥ 1` is at least `a - 1/2`, each root of modulus `< 1` is at
least `(a+1)^{-1/(d-1)}` in the `(d-1)`-st power, and two large roots already overdraw the
budget.  Only integer powers occur, so no `rpow` is needed.
-/

/-- **The heart of Theorem 5(i)**, Rouché-free: `α` is the *only* root of modulus at least one,
and it is a simple root.  Everything else in the file about the conjugates comes from this. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem card_big_roots_eq_one (hd : 2 ≤ d) (ha : 3 ≤ a) {α : ℝ}
    (hlt : (a : ℝ) < α) (hroot : α ^ d - (a : ℝ) * α ^ (d - 1) - 1 = 0) :
    Multiset.card
        (((familyPoly d a).map (Int.castRingHom ℂ)).roots.filter (fun w => 1 ≤ ‖w‖)) = 1 := by
  have haR : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  set P : Polynomial ℂ := (familyPoly d a).map (Int.castRingHom ℂ) with hPdef
  have hmonicZ : (familyPoly d a).Monic := familyPoly_monic (by omega)
  have hmonic : P.Monic := hmonicZ.map _
  have hP0 : P ≠ 0 := hmonic.ne_zero
  have hdeg : P.natDegree = d := by
    rw [hPdef, hmonicZ.natDegree_map]; exact familyPoly_natDegree (by omega)
  have hsplits : P.Splits := IsAlgClosed.splits P
  have hcard : Multiset.card P.roots = d := by
    rw [← hdeg]; exact hsplits.natDegree_eq_card_roots.symm
  -- every root satisfies the equation
  have hrootz : ∀ w ∈ P.roots, w ^ d - (a : ℂ) * w ^ (d - 1) - 1 = 0 := by
    intro w hw
    have hev := (Polynomial.mem_roots hP0).mp hw
    rw [← eval_familyPoly_map (d := d) (a := a) w]
    exact hev
  -- α is a root, of modulus > 1
  have hαroot : ((α : ℂ)) ^ d - (a : ℂ) * ((α : ℂ)) ^ (d - 1) - 1 = 0 := by
    have : ((α ^ d - (a : ℝ) * α ^ (d - 1) - 1 : ℝ) : ℂ) = 0 := by rw [hroot]; norm_num
    push_cast at this
    exact this
  have hαmem : ((α : ℂ)) ∈ P.roots := by
    refine (Polynomial.mem_roots hP0).mpr ?_
    show P.eval ((α : ℂ)) = 0
    rw [eval_familyPoly_map]
    exact hαroot
  have hαnorm : ‖((α : ℂ))‖ = α := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hαge : (1 : ℝ) ≤ ‖((α : ℂ))‖ := by rw [hαnorm]; linarith
  -- the product of the moduli of all roots is one
  have hcoeff : P.coeff 0 = (-1 : ℂ) := by
    rw [hPdef, Polynomial.coeff_map, familyPoly_coeff_zero hd]; norm_num
  have hprodroots : P.coeff 0 = (-1) ^ P.natDegree * P.roots.prod :=
    hsplits.coeff_zero_eq_prod_roots_of_monic hmonic
  have hnormprod : (P.roots.map (fun w => ‖w‖)).prod = 1 := by
    rw [← norm_multisetProd_eq]
    have h1 : ‖P.coeff 0‖ = ‖P.roots.prod‖ := by
      rw [hprodroots, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    rw [← h1, hcoeff]
    simp
  -- split the roots by modulus
  set B : Multiset ℂ := P.roots.filter (fun w => 1 ≤ ‖w‖) with hBdef
  set S : Multiset ℂ := P.roots.filter (fun w => ¬ (1 ≤ ‖w‖)) with hSdef
  have hsplit : B + S = P.roots := Multiset.filter_add_not _ _
  have hcards : Multiset.card B + Multiset.card S = d := by
    rw [← hcard, ← hsplit, Multiset.card_add]
  have hPBPS : ((B.map fun w => ‖w‖).prod) * ((S.map fun w => ‖w‖).prod) = 1 := by
    rw [← Multiset.prod_add, ← Multiset.map_add, hsplit, hnormprod]
  have hαB : ((α : ℂ)) ∈ B := Multiset.mem_filter.mpr ⟨hαmem, hαge⟩
  -- the counting
  set c : ℝ := (a : ℝ) - 1 / 2 with hcdef
  have hc1 : (1 : ℝ) < c := by rw [hcdef]; linarith
  have hc0 : (0 : ℝ) ≤ c := by linarith
  have hcardB : Multiset.card B = 1 := by
    by_contra hne1
    have hk1 : 1 ≤ Multiset.card B := by
      have hBne : B ≠ 0 := by
        intro h; rw [h] at hαB; exact absurd hαB (by simp)
      exact Nat.one_le_iff_ne_zero.mpr (fun h => hBne (Multiset.card_eq_zero.mp h))
    have hk2 : 2 ≤ Multiset.card B := by omega
    have hPB : c ^ Multiset.card B ≤ (B.map fun w => ‖w‖).prod := by
      have hmem : ∀ x ∈ (B.map fun w => ‖w‖), c ≤ x := by
        intro x hx
        obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hx
        exact le_norm_of_one_le_norm hd ha (hrootz w (Multiset.mem_filter.mp hw).1)
          (Multiset.mem_filter.mp hw).2
      simpa [Multiset.card_map] using pow_card_le_multisetProd hc0 _ hmem
    have hPS : (((a : ℝ) + 1)⁻¹) ^ Multiset.card S
        ≤ ((S.map fun w => ‖w‖).prod) ^ (d - 1) := by
      rw [multisetProd_pow, Multiset.map_map]
      have hmem : ∀ x ∈ (S.map ((fun y : ℝ => y ^ (d - 1)) ∘ (fun w : ℂ => ‖w‖))),
          ((a : ℝ) + 1)⁻¹ ≤ x := by
        intro x hx
        obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hx
        exact inv_le_norm_pow_of_norm_lt_one hd ha (hrootz w (Multiset.mem_filter.mp hw).1)
          (lt_of_not_ge (Multiset.mem_filter.mp hw).2)
      simpa [Multiset.card_map] using
        pow_card_le_multisetProd (c := ((a : ℝ) + 1)⁻¹) (by positivity) _ hmem
    have hkey : (c ^ Multiset.card B) ^ (d - 1) * (((a : ℝ) + 1)⁻¹) ^ Multiset.card S ≤ 1 := by
      have h1 : (c ^ Multiset.card B) ^ (d - 1) ≤ ((B.map fun w => ‖w‖).prod) ^ (d - 1) :=
        pow_le_pow_left₀ (by positivity) hPB _
      have h2 : ((B.map fun w => ‖w‖).prod ^ (d - 1)) * ((S.map fun w => ‖w‖).prod ^ (d - 1))
          = 1 := by rw [← mul_pow, hPBPS, one_pow]
      have hBprod0 : (0 : ℝ) ≤ (B.map fun w => ‖w‖).prod :=
        le_trans (by positivity) hPB
      calc (c ^ Multiset.card B) ^ (d - 1) * (((a : ℝ) + 1)⁻¹) ^ Multiset.card S
          ≤ ((B.map fun w => ‖w‖).prod) ^ (d - 1) * ((S.map fun w => ‖w‖).prod) ^ (d - 1) :=
            mul_le_mul h1 hPS (by positivity) (pow_nonneg hBprod0 _)
        _ = 1 := h2
    have hApos : (0 : ℝ) < ((a : ℝ) + 1) ^ Multiset.card S := by positivity
    have hfinal : c ^ (Multiset.card B * (d - 1)) ≤ ((a : ℝ) + 1) ^ Multiset.card S := by
      rw [inv_pow] at hkey
      have hdiv : (c ^ Multiset.card B) ^ (d - 1) / ((a : ℝ) + 1) ^ Multiset.card S ≤ 1 := by
        rw [div_eq_mul_inv]; exact hkey
      rw [div_le_one hApos] at hdiv
      rw [pow_mul]
      exact hdiv
    have hml : Multiset.card S ≤ d - 2 := by omega
    have step1 : c ^ (2 * (d - 1)) ≤ c ^ (Multiset.card B * (d - 1)) :=
      pow_le_pow_right₀ hc1.le (Nat.mul_le_mul_right _ hk2)
    have step2 : ((a : ℝ) + 1) ^ Multiset.card S ≤ ((a : ℝ) + 1) ^ (d - 2) :=
      pow_le_pow_right₀ (by linarith) hml
    have step3 : ((a : ℝ) + 1) ≤ c ^ 2 := by rw [hcdef]; nlinarith
    have step4 : ((a : ℝ) + 1) ^ (d - 2) ≤ (c ^ 2) ^ (d - 2) :=
      pow_le_pow_left₀ (by linarith) step3 _
    have hchain : c ^ (2 * (d - 1)) ≤ c ^ (2 * (d - 2)) := by
      calc c ^ (2 * (d - 1)) ≤ c ^ (Multiset.card B * (d - 1)) := step1
        _ ≤ ((a : ℝ) + 1) ^ Multiset.card S := hfinal
        _ ≤ ((a : ℝ) + 1) ^ (d - 2) := step2
        _ ≤ (c ^ 2) ^ (d - 2) := step4
        _ = c ^ (2 * (d - 2)) := by rw [← pow_mul]
    have hstrict : c ^ (2 * (d - 2)) < c ^ (2 * (d - 1)) :=
      pow_lt_pow_right₀ hc1 (by omega)
    linarith
  exact hcardB

/-- **Every root other than `α` has modulus `< 1`** — the Pisot property, before minimal
polynomials enter. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem norm_lt_one_of_mem_roots_of_ne (hd : 2 ≤ d) (ha : 3 ≤ a) {α : ℝ}
    (hlt : (a : ℝ) < α) (hroot : α ^ d - (a : ℝ) * α ^ (d - 1) - 1 = 0)
    {z : ℂ} (hz : z ∈ ((familyPoly d a).map (Int.castRingHom ℂ)).roots) (hne : z ≠ (α : ℂ)) :
    ‖z‖ < 1 := by
  have haR : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  set P : Polynomial ℂ := (familyPoly d a).map (Int.castRingHom ℂ) with hPdef
  have hP0 : P ≠ 0 := ((familyPoly_monic (by omega : 1 ≤ d)).map _).ne_zero
  have hαroot : ((α : ℂ)) ^ d - (a : ℂ) * ((α : ℂ)) ^ (d - 1) - 1 = 0 := by
    have hc : ((α ^ d - (a : ℝ) * α ^ (d - 1) - 1 : ℝ) : ℂ) = 0 := by rw [hroot]; norm_num
    push_cast at hc
    exact hc
  have hαmem : ((α : ℂ)) ∈ P.roots := by
    refine (Polynomial.mem_roots hP0).mpr ?_
    show P.eval ((α : ℂ)) = 0
    rw [hPdef, eval_familyPoly_map]; exact hαroot
  have hαnorm : ‖((α : ℂ))‖ = α := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hαB : ((α : ℂ)) ∈ P.roots.filter (fun w => 1 ≤ ‖w‖) :=
    Multiset.mem_filter.mpr ⟨hαmem, by rw [hαnorm]; linarith⟩
  obtain ⟨x, hx⟩ := Multiset.card_eq_one.mp (card_big_roots_eq_one hd ha hlt hroot)
  rw [← hPdef] at hx
  have hxα : x = ((α : ℂ)) := by rw [hx, Multiset.mem_singleton] at hαB; exact hαB.symm
  by_contra hcon
  push Not at hcon
  have hzB : z ∈ P.roots.filter (fun w => 1 ≤ ‖w‖) := Multiset.mem_filter.mpr ⟨hz, hcon⟩
  rw [hx, Multiset.mem_singleton] at hzB
  exact hne (hzB.trans hxα)

/-! ## Theorem 5(i): the family member is a Pisot number -/

/-- **M2 Theorem 5(i), the Pisot half.**  The real root `α > a` of `X^d - aX^{d-1} - 1` is a
Pisot number. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem isPisot_family (hd : 2 ≤ d) (ha : 3 ≤ a) {α : ℝ} (hlt : (a : ℝ) < α)
    (hroot : α ^ d - (a : ℝ) * α ^ (d - 1) - 1 = 0) : IsPisot α := by
  have haR : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hint : IsIntegral ℤ α := by
    refine ⟨familyPoly d a, familyPoly_monic (by omega), ?_⟩
    rw [← aeval_def, aeval_familyPoly]
    exact hroot
  refine ⟨by linarith, hint, ?_⟩
  intro z hz hzne
  have hdvd : minpoly ℚ α ∣ (familyPoly d a).map (Int.castRingHom ℚ) := by
    refine minpoly.dvd ℚ α ?_
    have hev : (aeval α) ((familyPoly d a).map (Int.castRingHom ℚ))
        = α ^ d - (a : ℝ) * α ^ (d - 1) - 1 := by
      simp [familyPoly]
    rw [hev]; exact hroot
  rw [Polynomial.mem_aroots'] at hz
  obtain ⟨g, hg⟩ := hdvd
  have hz0 : (aeval z) ((familyPoly d a).map (Int.castRingHom ℚ)) = 0 := by
    rw [hg, map_mul, hz.2, zero_mul]
  have hzeq : z ^ d - (a : ℂ) * z ^ (d - 1) - 1 = 0 := by
    have hev : (aeval z) ((familyPoly d a).map (Int.castRingHom ℚ))
        = z ^ d - (a : ℂ) * z ^ (d - 1) - 1 := by
      simp [familyPoly]
    rw [← hev]; exact hz0
  have hmonicZ : (familyPoly d a).Monic := familyPoly_monic (by omega)
  have hP0 : ((familyPoly d a).map (Int.castRingHom ℂ)) ≠ 0 := (hmonicZ.map _).ne_zero
  have hmem : z ∈ ((familyPoly d a).map (Int.castRingHom ℂ)).roots := by
    refine (Polynomial.mem_roots hP0).mpr ?_
    show ((familyPoly d a).map (Int.castRingHom ℂ)).eval z = 0
    rw [eval_familyPoly_map]; exact hzeq
  exact norm_lt_one_of_mem_roots_of_ne hd ha hlt hroot hmem hzne

/-! ## Theorem 5(ii): the explicit conjugate bound -/

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem familyConjBound_pos (ha : 3 ≤ a) : 0 < familyConjBound d a := by
  have haR : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  exact Real.rpow_pos_of_pos (by positivity) _

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem familyConjBound_pow (hd : 2 ≤ d) (ha : 3 ≤ a) :
    (familyConjBound d a) ^ (d - 1) = 2 / (a : ℝ) := by
  have haR : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  exact Real.rpow_inv_natCast_pow (by positivity) (by omega)

/-- **M2 Theorem 5(ii).**  Every conjugate has modulus at most `(2/a)^{1/(d-1)}`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem norm_le_familyConjBound (hd : 2 ≤ d) (ha : 3 ≤ a) {α : ℝ} (hlt : (a : ℝ) < α)
    (hroot : α ^ d - (a : ℝ) * α ^ (d - 1) - 1 = 0)
    {z : ℂ} (hz : z ∈ ((familyPoly d a).map (Int.castRingHom ℂ)).roots) (hne : z ≠ (α : ℂ)) :
    ‖z‖ ≤ familyConjBound d a := by
  have haR : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hsmall : ‖z‖ < 1 := norm_lt_one_of_mem_roots_of_ne hd ha hlt hroot hz hne
  have hP0 : ((familyPoly d a).map (Int.castRingHom ℂ)) ≠ 0 :=
    ((familyPoly_monic (by omega : 1 ≤ d)).map _).ne_zero
  have hzeq : z ^ d - (a : ℂ) * z ^ (d - 1) - 1 = 0 := by
    have hev := (Polynomial.mem_roots hP0).mp hz
    rw [← eval_familyPoly_map (d := d) (a := a) z]
    exact hev
  have h2 := mul_norm_pow_le_two (a := a) hzeq hsmall.le
  have hpow : ‖z‖ ^ (d - 1) ≤ (familyConjBound d a) ^ (d - 1) := by
    rw [familyConjBound_pow hd ha, le_div_iff₀ (by linarith)]
    linarith [h2]
  exact le_of_pow_le_pow_left₀ (by omega) (familyConjBound_pos ha).le hpow

/-! ## Theorem 5(iii): the criterion fires for `a ≥ 2^{d+1}` -/

/-- The arithmetic of Theorem 5(iii): `1/(d+1) + (d-1)/d = (d²+d-1)/(d²+d) < 1`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem inv_add_inv_lt_one_of_deg {L R : ℝ} (hd : 2 ≤ d)
    (hL : (d : ℝ) + 1 < L) (hR : (d : ℝ) ≤ ((d : ℝ) - 1) * R) : L⁻¹ + R⁻¹ < 1 := by
  have hD : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hD1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  have hRpos : 0 < R := by nlinarith
  have hLpos : (0 : ℝ) < L := by linarith
  have e1 : L⁻¹ < ((d : ℝ) + 1)⁻¹ := by
    rw [inv_lt_inv₀ hLpos (by linarith)]; exact hL
  have hRinv : R⁻¹ * R = 1 := inv_mul_cancel₀ hRpos.ne'
  have e2 : R⁻¹ ≤ ((d : ℝ) - 1) / (d : ℝ) := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < (d : ℝ))]
    nlinarith [mul_le_mul_of_nonneg_left hR (inv_pos.mpr hRpos).le, hRinv]
  have e3 : ((d : ℝ) + 1)⁻¹ + ((d : ℝ) - 1) / (d : ℝ) < 1 := by
    rw [inv_eq_one_div, div_add_div _ _ (by linarith : ((d:ℝ) + 1) ≠ 0)
      (by linarith : ((d:ℝ)) ≠ 0), div_lt_one (by nlinarith)]
    nlinarith
  linarith

/-- **M2 Theorem 5(iii).**  If `a ≥ 2^{d+1}` then the Route A exponent of the family member is
below one, at any positive conjugate bound `ρ` with `a·ρ^{d-1} ≤ 2` — in particular at
`familyConjBound`, by Theorem 5(ii).

This is a conditional inequality about two reals, and an **ingredient**: nothing derives Problem
10.61 from it above degree two, because the covering criterion that would consume it,
`QuadSetup.not_equidistributed_of_routeAExponent_lt_one`, is stated for a `QuadSetup`.  At
`d = 2` the member *is* a `QuadSetup` — `familyQuad` — and the conclusion does follow, as
`familyQuad_not_equidistributed`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem routeA_family_lt_one (hd : 2 ≤ d) (ha : 2 ^ (d + 1) ≤ a) {α ρ : ℝ}
    (hlt : (a : ℝ) < α) (hρ0 : 0 < ρ) (hρ : (a : ℝ) * ρ ^ (d - 1) ≤ 2) :
    Real.log 2 / Real.log α + Real.log 2 / Real.log ρ⁻¹ < 1 := by
  have haR : (2 : ℝ) ^ (d + 1) ≤ (a : ℝ) := by exact_mod_cast ha
  have h8 : (8 : ℝ) ≤ (2 : ℝ) ^ (d + 1) := by
    calc (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
      _ ≤ (2 : ℝ) ^ (d + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hαpos : (0 : ℝ) < α := by linarith
  have hL : Real.log 2 / Real.log α = (Real.logb 2 α)⁻¹ := by rw [Real.logb, inv_div]
  have hRw : Real.log 2 / Real.log ρ⁻¹ = (Real.logb 2 ρ⁻¹)⁻¹ := by rw [Real.logb, inv_div]
  rw [hL, hRw]
  refine inv_add_inv_lt_one_of_deg hd ?_ ?_
  · have h1 : (2 : ℝ) ^ (((d : ℝ) + 1)) < α := by
      have hcast : (2 : ℝ) ^ (((d : ℝ) + 1)) = (2 : ℝ) ^ (d + 1) := by
        rw [show ((d : ℝ) + 1) = ((d + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
      rw [hcast]; linarith
    exact (Real.lt_logb_iff_rpow_lt one_lt_two hαpos).mpr h1
  · have hd1 : ((d : ℝ) - 1) = ((d - 1 : ℕ) : ℝ) := by
      have h1d : (1 : ℕ) ≤ d := by omega
      rw [Nat.cast_sub h1d]; norm_num
    have hpowpos : (0 : ℝ) < ρ ^ (d - 1) := pow_pos hρ0 _
    have hstep : (2 : ℝ) ^ (d + 1) * ρ ^ (d - 1) ≤ 2 :=
      le_trans (mul_le_mul_of_nonneg_right haR hpowpos.le) hρ
    have hnat : (2 : ℝ) ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ]; ring
    have hstep2 : (2 : ℝ) ^ d * ρ ^ (d - 1) ≤ 1 := by rw [hnat] at hstep; linarith
    have hbound : (2 : ℝ) ^ ((d : ℝ)) ≤ (ρ⁻¹) ^ (d - 1) := by
      rw [Real.rpow_natCast, inv_pow, inv_eq_one_div, le_div_iff₀ hpowpos]
      exact hstep2
    have hlogb : ((d - 1 : ℕ) : ℝ) * Real.logb 2 ρ⁻¹ = Real.logb 2 ((ρ⁻¹) ^ (d - 1)) := by
      rw [Real.logb_pow]
    rw [hd1, hlogb]
    exact (Real.le_logb_iff_rpow_le one_lt_two (by positivity)).mpr hbound

/-! ## Theorem 5(iv) at `d = 2`: Problem 10.61 for every `X² - aX - 1` with `a ≥ 4`

At degree two the family member is a `QuadSetup`, so the whole Route A engine of the folder
applies and the conclusion is 10.61 itself, not just `A(α) < 1`.
-/

private theorem lt_sqrt_sq_add_four {a : ℕ} : (a : ℝ) < Real.sqrt ((a : ℝ) ^ 2 + 4) := by
  rw [show ((a : ℝ)) = |(a : ℝ)| from (abs_of_nonneg (by positivity)).symm]
  rw [Real.lt_sqrt (abs_nonneg _), sq_abs]
  linarith

private theorem sqrt_sq_add_four_lt {a : ℕ} (ha : 1 ≤ a) :
    Real.sqrt ((a : ℝ) ^ 2 + 4) < (a : ℝ) + 2 := by
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  rw [show ((a : ℝ) + 2) = |(a : ℝ) + 2| from (abs_of_nonneg (by linarith)).symm]
  rw [Real.sqrt_lt' (by positivity), sq_abs]
  nlinarith

/-- The degree-two member `X² - aX - 1` of the family, as a `QuadSetup`:
`α_{2,a} = (a + √(a²+4))/2`. -/
noncomputable def familyQuad (a : ℕ) (ha : 1 ≤ a) : QuadSetup where
  a := (a : ℤ)
  b := 1
  α := ((a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 + 4)) / 2
  root := by
    have hs : Real.sqrt ((a : ℝ) ^ 2 + 4) ^ 2 = (a : ℝ) ^ 2 + 4 :=
      Real.sq_sqrt (by positivity)
    push_cast
    linear_combination hs / 4
  one_lt := by
    have h4 : (4 : ℝ) ≤ (a : ℝ) ^ 2 + 4 := by nlinarith [sq_nonneg ((a : ℝ))]
    have h1 : (2 : ℝ) ≤ Real.sqrt ((a : ℝ) ^ 2 + 4) := by
      calc (2 : ℝ) = Real.sqrt 4 := by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        _ ≤ Real.sqrt ((a : ℝ) ^ 2 + 4) := Real.sqrt_le_sqrt h4
    have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    rw [lt_div_iff₀ (by norm_num)]
    linarith
  conj_lt := by
    have h1 := lt_sqrt_sq_add_four (a := a)
    have h2 := sqrt_sq_add_four_lt ha
    push_cast
    rw [abs_lt]
    constructor <;> [linarith; linarith]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem familyQuad_alpha (a : ℕ) (ha : 1 ≤ a) :
    (familyQuad a ha).α = ((a : ℝ) + Real.sqrt ((a : ℝ) ^ 2 + 4)) / 2 := rfl

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem familyQuad_b (a : ℕ) (ha : 1 ≤ a) : (familyQuad a ha).b = 1 := rfl

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem familyQuad_beta_ne_zero (a : ℕ) (ha : 1 ≤ a) : (familyQuad a ha).β ≠ 0 :=
  (familyQuad a ha).beta_ne_zero_of_b_ne_zero (by rw [familyQuad_b]; norm_num)

/-- The degree-two member is a root of `familyPoly 2 a`, so the general-degree results apply. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem familyQuad_root (a : ℕ) (ha : 1 ≤ a) :
    (familyQuad a ha).α ^ 2 - (a : ℝ) * (familyQuad a ha).α ^ (2 - 1) - 1 = 0 := by
  have h := (familyQuad a ha).root
  simp only [familyQuad] at h ⊢
  push_cast at h ⊢
  linarith

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem lt_familyQuad_alpha (a : ℕ) (ha : 1 ≤ a) : (a : ℝ) < (familyQuad a ha).α := by
  have h1 := lt_sqrt_sq_add_four (a := a)
  rw [familyQuad_alpha, lt_div_iff₀ (by norm_num)]
  linarith

/-- **The family member is a Pisot number** (degree two, `a ≥ 3`). -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem familyQuad_isPisot (a : ℕ) (ha : 1 ≤ a) (h3 : 3 ≤ a) : IsPisot (familyQuad a ha).α :=
  isPisot_family (by omega) h3 (lt_familyQuad_alpha a ha) (familyQuad_root a ha)

/-- **The exact firing threshold at `d = 2`**: `α_{2,a} > 4` iff `a ≥ 4`.  So `α_{2,3} = (3+√13)/2
misses and `α_{2,4} = 2+√5` fires — the note's `α_{2,3} < 4 < α_{2,4}`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem four_lt_familyQuad_alpha_iff (a : ℕ) (ha : 1 ≤ a) :
    4 < (familyQuad a ha).α ↔ 4 ≤ a := by
  have h1 := lt_sqrt_sq_add_four (a := a)
  have h2 := sqrt_sq_add_four_lt ha
  rw [familyQuad_alpha, lt_div_iff₀ (by norm_num)]
  constructor
  · intro h
    have haR : (3 : ℝ) < (a : ℝ) := by linarith
    have : (3 : ℕ) < a := by exact_mod_cast haR
    omega
  · intro h
    have haR : (4 : ℝ) ≤ (a : ℝ) := by exact_mod_cast h
    linarith

/-- **M2 Theorem 5(iv), `d = 2`: the complete answer.**  Route A fires at `X² - aX - 1`
exactly when `a ≥ 4`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem familyQuad_routeAExponent_lt_one_iff (a : ℕ) (ha : 1 ≤ a) :
    (familyQuad a ha).routeAExponent < 1 ↔ 4 ≤ a := by
  rw [(familyQuad a ha).routeAExponent_lt_one_iff_four_lt (by rw [familyQuad_b]; norm_num),
    four_lt_familyQuad_alpha_iff]

/-- **The explicit infinite family, degree two: Problem 10.61 holds at `α_{2,a}` for every
`a ≥ 4`.**  This is Theorem 5 delivered all the way to its conclusion — the note's Theorem 2
applied to the family. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem familyQuad_not_equidistributed (a : ℕ) (ha : 1 ≤ a) (h4 : 4 ≤ a) :
    ∀ ξ ∈ cantorSet (familyQuad a ha).α,
      ¬ IsEquidistributedModuloOne fun n : ℕ => ξ * (familyQuad a ha).α ^ n :=
  (familyQuad a ha).not_equidistributed_of_routeAExponent_lt_one (familyQuad_beta_ne_zero a ha)
    ((familyQuad_routeAExponent_lt_one_iff a ha).mpr h4)

/-- …and none of those orbits is even dense. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem familyQuad_not_denseModuloOne (a : ℕ) (ha : 1 ≤ a) (h4 : 4 ≤ a) :
    ∀ ξ ∈ cantorSet (familyQuad a ha).α,
      ¬ IsDenseModuloOne fun n : ℕ => ξ * (familyQuad a ha).α ^ n :=
  (familyQuad a ha).not_denseModuloOne_of_routeAExponent_lt_one (familyQuad_beta_ne_zero a ha)
    ((familyQuad_routeAExponent_lt_one_iff a ha).mpr h4)

/-- The first member that fires is `α_{2,4} = 2 + √5` — the capstone of `BB61/RouteA.lean`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem familyQuad_four_alpha : (familyQuad 4 (by norm_num)).α = 2 + Real.sqrt 5 := by
  rw [familyQuad_alpha]
  have h : ((4 : ℕ) : ℝ) ^ 2 + 4 = 20 := by norm_num
  rw [h, show (20 : ℝ) = 2 ^ 2 * 5 by norm_num, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by norm_num)]
  norm_num
  ring

/-! ## Theorem 5(i), the rest: degree exactly `d`, and a unit

`α` being Pisot needed only the root count.  That the family really is "in every degree", and
that its members are units, needs the minimal polynomial — and the same product-of-roots
argument, run on a putative monic cofactor.
-/

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem multisetProd_le_one : ∀ s : Multiset ℝ, (∀ x ∈ s, 0 ≤ x ∧ x ≤ 1) → s.prod ≤ 1 := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons x t ih =>
      intro h
      have hx := h x (Multiset.mem_cons_self x t)
      have ht : ∀ y ∈ t, 0 ≤ y ∧ y ≤ 1 := fun y hy => h y (Multiset.mem_cons_of_mem hy)
      have h0 : (0 : ℝ) ≤ t.prod := Multiset.prod_nonneg (fun y hy => (ht y hy).1)
      rw [Multiset.prod_cons]
      nlinarith [ih ht, hx.1, hx.2, h0]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem multisetProd_lt_one {s : Multiset ℝ} (h : ∀ x ∈ s, 0 ≤ x ∧ x < 1) (hs : s ≠ 0) :
    s.prod < 1 := by
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hs
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hx
  have hx0 := h x (Multiset.mem_cons_self x t)
  have ht : ∀ y ∈ t, 0 ≤ y ∧ y ≤ 1 := fun y hy =>
    ⟨(h y (Multiset.mem_cons_of_mem hy)).1, (h y (Multiset.mem_cons_of_mem hy)).2.le⟩
  have h0 : (0 : ℝ) ≤ t.prod := Multiset.prod_nonneg (fun y hy => (ht y hy).1)
  rw [Multiset.prod_cons]
  nlinarith [multisetProd_le_one t ht, hx0.1, hx0.2, h0]

/-- **M2 Theorem 5(i), the irreducibility half.**  `X^d - aX^{d-1} - 1` *is* the minimal
polynomial of its root `α > a`: the family really is a family of degree-`d` numbers. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem minpoly_eq_familyPoly (hd : 2 ≤ d) (ha : 3 ≤ a) {α : ℝ} (hlt : (a : ℝ) < α)
    (hroot : α ^ d - (a : ℝ) * α ^ (d - 1) - 1 = 0) : minpoly ℤ α = familyPoly d a := by
  have haR : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hpm : (familyPoly d a).Monic := familyPoly_monic (by omega)
  have hint : IsIntegral ℤ α := by
    refine ⟨familyPoly d a, hpm, ?_⟩
    rw [← aeval_def, aeval_familyPoly]; exact hroot
  have haeval : (aeval α) (familyPoly d a) = 0 := by rw [aeval_familyPoly]; exact hroot
  have : IsIntegrallyClosed ℤ := GCDMonoid.toIsIntegrallyClosed
  obtain ⟨r, hr⟩ := minpoly.isIntegrallyClosed_dvd hint haeval
  have hmp : (minpoly ℤ α).Monic := minpoly.monic hint
  have hrm : r.Monic := hmp.of_mul_monic_left (by rw [← hr]; exact hpm)
  suffices hr1 : r = 1 by rw [hr, hr1, mul_one]
  by_contra hne1
  have hdegr : 1 ≤ r.natDegree := by
    rcases Nat.eq_zero_or_pos r.natDegree with h | h
    · exact absurd (hrm.natDegree_eq_zero.mp h) hne1
    · exact h
  -- move to ℂ
  set Q : Polynomial ℂ := (minpoly ℤ α).map (Int.castRingHom ℂ) with hQdef
  set R : Polynomial ℂ := r.map (Int.castRingHom ℂ) with hRdef
  set P : Polynomial ℂ := (familyPoly d a).map (Int.castRingHom ℂ) with hPdef
  have hQm : Q.Monic := hmp.map _
  have hRm : R.Monic := hrm.map _
  have hPQR : P = Q * R := by rw [hPdef, hQdef, hRdef, hr, Polynomial.map_mul]
  have hP0 : P ≠ 0 := (hpm.map _).ne_zero
  have hroots : P.roots = Q.roots + R.roots := by
    rw [hPQR, Polynomial.roots_mul (by rw [← hPQR]; exact hP0)]
  -- α is a root of Q
  have hQα : ((α : ℂ)) ∈ Q.roots := by
    refine (Polynomial.mem_roots hQm.ne_zero).mpr ?_
    show Q.eval ((α : ℂ)) = 0
    rw [hQdef, Polynomial.eval_map]
    have hz : Polynomial.eval₂ (Int.castRingHom ℝ) α (minpoly ℤ α) = 0 := by
      have h := minpoly.aeval ℤ α
      rwa [Polynomial.aeval_def, algebraMap_int_eq] at h
    have hcomp : (Complex.ofRealHom : ℝ →+* ℂ).comp (Int.castRingHom ℝ)
        = Int.castRingHom ℂ := by ext n; simp
    have hh := Polynomial.hom_eval₂ (minpoly ℤ α) (Int.castRingHom ℝ) Complex.ofRealHom α
    rw [hz, map_zero, hcomp] at hh
    exact hh.symm
  -- α occurs at most once among all roots
  have hcount1 : Multiset.count ((α : ℂ)) P.roots ≤ 1 := by
    have hnorm : (1 : ℝ) ≤ ‖((α : ℂ))‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith
    have h1 : Multiset.count ((α : ℂ)) (P.roots.filter (fun w => 1 ≤ ‖w‖))
        = Multiset.count ((α : ℂ)) P.roots := Multiset.count_filter_of_pos hnorm
    have h2 : Multiset.count ((α : ℂ)) P.roots
        ≤ Multiset.card (P.roots.filter (fun w => 1 ≤ ‖w‖)) := by
      rw [← h1]; exact Multiset.count_le_card _ _
    have h3 : Multiset.card (P.roots.filter (fun w => 1 ≤ ‖w‖)) = 1 := by
      rw [hPdef]; exact card_big_roots_eq_one hd ha hlt hroot
    omega
  -- so α is not a root of R
  have hαR : ((α : ℂ)) ∉ R.roots := by
    intro hmem
    have h1 : 1 ≤ Multiset.count ((α : ℂ)) Q.roots := Multiset.one_le_count_iff_mem.mpr hQα
    have h2 : 1 ≤ Multiset.count ((α : ℂ)) R.roots := Multiset.one_le_count_iff_mem.mpr hmem
    have : Multiset.count ((α : ℂ)) P.roots
        = Multiset.count ((α : ℂ)) Q.roots + Multiset.count ((α : ℂ)) R.roots := by
      rw [hroots, Multiset.count_add]
    omega
  -- every root of R has modulus < 1
  have hRsmall : ∀ w ∈ R.roots, 0 ≤ ‖w‖ ∧ ‖w‖ < 1 := by
    intro w hw
    refine ⟨norm_nonneg w, ?_⟩
    have hwP : w ∈ P.roots := by rw [hroots]; exact Multiset.mem_add.mpr (Or.inr hw)
    refine norm_lt_one_of_mem_roots_of_ne hd ha hlt hroot (by rw [← hPdef]; exact hwP) ?_
    intro hcon; exact hαR (hcon ▸ hw)
  -- but the product of those moduli is one
  have hcoeff : (minpoly ℤ α).coeff 0 * r.coeff 0 = -1 := by
    rw [← Polynomial.mul_coeff_zero, ← hr]; exact familyPoly_coeff_zero hd
  have hunit : |r.coeff 0| = 1 := by
    have hdvd1 : r.coeff 0 ∣ (1 : ℤ) := ⟨-(minpoly ℤ α).coeff 0, by linarith [hcoeff]⟩
    rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd1) with h | h <;> rw [h] <;> norm_num
  have hRprod : ‖R.roots.prod‖ = 1 := by
    have hsp : R.Splits := IsAlgClosed.splits R
    have h1 : R.coeff 0 = (-1) ^ R.natDegree * R.roots.prod :=
      hsp.coeff_zero_eq_prod_roots_of_monic hRm
    have h2 : ‖R.coeff 0‖ = ‖R.roots.prod‖ := by
      rw [h1, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have h3 : R.coeff 0 = ((r.coeff 0 : ℤ) : ℂ) := by rw [hRdef, Polynomial.coeff_map]; simp
    rw [← h2, h3, Complex.norm_intCast, ← Int.cast_abs, hunit]
    norm_num
  have hRne : R.roots ≠ 0 := by
    intro h
    have hsp : R.Splits := IsAlgClosed.splits R
    have := hsp.natDegree_eq_card_roots
    rw [h] at this
    have hrdeg : R.natDegree = r.natDegree := by rw [hRdef, hrm.natDegree_map]
    simp at this
    omega
  have : (R.roots.map fun w => ‖w‖).prod < 1 := by
    refine multisetProd_lt_one ?_ (by simpa using hRne)
    intro x hx
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hx
    exact hRsmall w hw
  rw [← norm_multisetProd_eq, hRprod] at this
  exact absurd this (by norm_num)

/-- **M2 Theorem 5(i), irreducibility.**  `X^d - aX^{d-1} - 1` is irreducible over `ℚ` (indeed
over `ℤ`), being the minimal polynomial of `α`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem familyPoly_irreducible (hd : 2 ≤ d) (ha : 3 ≤ a) {α : ℝ} (hlt : (a : ℝ) < α)
    (hroot : α ^ d - (a : ℝ) * α ^ (d - 1) - 1 = 0) : Irreducible (familyPoly d a) := by
  have hint : IsIntegral ℤ α := by
    refine ⟨familyPoly d a, familyPoly_monic (by omega), ?_⟩
    rw [← aeval_def, aeval_familyPoly]; exact hroot
  rw [← minpoly_eq_familyPoly hd ha hlt hroot]
  exact minpoly.irreducible hint

/-- **The family member has degree exactly `d`** — the sense in which Theorem 5 is a family
"in every degree". -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem minpoly_natDegree_family (hd : 2 ≤ d) (ha : 3 ≤ a) {α : ℝ} (hlt : (a : ℝ) < α)
    (hroot : α ^ d - (a : ℝ) * α ^ (d - 1) - 1 = 0) : (minpoly ℤ α).natDegree = d := by
  rw [minpoly_eq_familyPoly hd ha hlt hroot]; exact familyPoly_natDegree (by omega)

/-- **…and is a unit**: its norm is `±1`, since the constant term of its minimal polynomial
is `-1`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem minpoly_coeff_zero_family (hd : 2 ≤ d) (ha : 3 ≤ a) {α : ℝ} (hlt : (a : ℝ) < α)
    (hroot : α ^ d - (a : ℝ) * α ^ (d - 1) - 1 = 0) : (minpoly ℤ α).coeff 0 = -1 := by
  rw [minpoly_eq_familyPoly hd ha hlt hroot]; exact familyPoly_coeff_zero hd

/-! ## Theorem 5(iv) at `d = 3`: the family sits on the ceiling

At `d = 3` the two conjugates are a complex pair of equal modulus `α^{-1/2}`, so
`A(α)·log₂ α = 3` exactly: the cubic members sit *on* the ceiling of M2 Proposition 4
(`BB61/RouteACeiling.lean`), and `A(α) < 1` iff `α > 8` iff `a ≥ 8`.

No calculus is needed.  Dividing the cubic by `X - α` leaves a real quadratic whose
discriminant is *automatically* negative, which both forces the pair to be non-real and
computes its modulus.
-/

/-- A complex root of a real quadratic with negative discriminant has `‖z‖² = c`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem norm_sq_of_quadratic {b c : ℝ} (hdisc : b ^ 2 < 4 * c) {z : ℂ}
    (hz : z * z + (b : ℂ) * z + (c : ℂ) = 0) : ‖z‖ ^ 2 = c := by
  have hre : z.re * z.re - z.im * z.im + b * z.re + c = 0 := by
    have := congrArg Complex.re hz
    simpa [Complex.add_re, Complex.mul_re, Complex.mul_im] using this
  have him : z.re * z.im + z.im * z.re + b * z.im = 0 := by
    have := congrArg Complex.im hz
    simpa [Complex.add_im, Complex.mul_re, Complex.mul_im] using this
  have hx : z.re = -b / 2 := by
    rcases mul_eq_zero.mp (show z.im * (2 * z.re + b) = 0 by linarith) with h | h
    · exfalso; rw [h] at hre; nlinarith [sq_nonneg (z.re + b / 2)]
    · linarith
  have hy : z.im * z.im = c - b ^ 2 / 4 := by rw [hx] at hre; nlinarith
  have hns : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  rw [hns, hx, hy]; ring

/-- **The cubic conjugates: `‖z‖² · α = 1`.**  Every root other than `α` of `X³ - aX² - 1`
has modulus `α^{-1/2}` — the family is *on* the Proposition 4 ceiling at `d = 3`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem norm_sq_mul_eq_one_cubic (ha : 3 ≤ a) {α : ℝ} (hlt : (a : ℝ) < α)
    (hroot : α ^ 3 - (a : ℝ) * α ^ 2 - 1 = 0)
    {z : ℂ} (hz : z ^ 3 - (a : ℂ) * z ^ 2 - 1 = 0) (hne : z ≠ (α : ℂ)) :
    ‖z‖ ^ 2 * α = 1 := by
  have haR : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hα3 : (3 : ℝ) < α := by linarith
  have hα0 : (0 : ℝ) < α := by linarith
  -- `α²(α - a) = 1`, so `α - a = 1/α²` and `α² - aα = 1/α`
  have hkey : α ^ 2 * (α - (a : ℝ)) = 1 := by linarith [hroot, sq_nonneg α]
  have hb : α - (a : ℝ) = 1 / α ^ 2 := by
    field_simp; linarith [hkey]
  have hc : α ^ 2 - (a : ℝ) * α = 1 / α := by
    field_simp
    nlinarith [hkey]
  -- divide out the known root
  have hαc : ((α : ℂ)) ^ 3 - (a : ℂ) * ((α : ℂ)) ^ 2 - 1 = 0 := by
    have hcast : ((α ^ 3 - (a : ℝ) * α ^ 2 - 1 : ℝ) : ℂ) = 0 := by rw [hroot]; norm_num
    push_cast at hcast; exact hcast
  have hfac : (z - (α : ℂ)) *
      (z * z + (((α : ℝ) - (a : ℝ) : ℝ) : ℂ) * z + (((α : ℝ) ^ 2 - (a : ℝ) * α : ℝ) : ℂ)) = 0 := by
    push_cast
    linear_combination hz - hαc
  have hQ : z * z + (((α : ℝ) - (a : ℝ) : ℝ) : ℂ) * z + (((α : ℝ) ^ 2 - (a : ℝ) * α : ℝ) : ℂ)
      = 0 := by
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · exact h
  -- the discriminant is negative
  have hdisc : ((α : ℝ) - (a : ℝ)) ^ 2 < 4 * ((α : ℝ) ^ 2 - (a : ℝ) * α) := by
    rw [hb, hc]
    have h4 : (1 : ℝ) < 4 * α ^ 3 := by nlinarith
    rw [div_pow, one_pow, show (4 : ℝ) * (1 / α) = 4 / α by ring, div_lt_div_iff₀ (by positivity)
      hα0]
    nlinarith
  have hns := norm_sq_of_quadratic hdisc hQ
  rw [hns, hc]
  field_simp

/-- **M2 Theorem 5(iv), `d = 3`: the exact threshold.**  With the conjugate modulus
`ρ = α^{-1/2}`, `A(α)·log₂ α = 3` and `A(α) < 1` iff `α > 8`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem routeA_cubic_mul_logb {α ρ : ℝ} (hα0 : 1 < α) (hρ0 : 0 < ρ)
    (hρ : ρ ^ 2 * α = 1) :
    ((Real.logb 2 α)⁻¹ + (Real.logb 2 ρ⁻¹)⁻¹) * Real.logb 2 α = 3 := by
  have hL : 0 < Real.logb 2 α := Real.logb_pos one_lt_two hα0
  have hRR : 2 * Real.logb 2 ρ⁻¹ = Real.logb 2 α := by
    have h1 : (ρ⁻¹) ^ 2 = α := by
      field_simp at hρ ⊢
      nlinarith [hρ, hρ0]
    calc 2 * Real.logb 2 ρ⁻¹ = ((2 : ℕ) : ℝ) * Real.logb 2 ρ⁻¹ := by norm_num
      _ = Real.logb 2 ((ρ⁻¹) ^ (2 : ℕ)) := (Real.logb_pow _ _ _).symm
      _ = Real.logb 2 α := by rw [h1]
  have hR : Real.logb 2 ρ⁻¹ = Real.logb 2 α / 2 := by linarith
  rw [hR]
  field_simp
  ring

/-- …and the criterion at `d = 3` reads `α > 8`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem routeA_cubic_lt_one_iff {α ρ : ℝ} (hα0 : 1 < α) (hρ0 : 0 < ρ) (hρ : ρ ^ 2 * α = 1) :
    (Real.logb 2 α)⁻¹ + (Real.logb 2 ρ⁻¹)⁻¹ < 1 ↔ 8 < α := by
  have hL : 0 < Real.logb 2 α := Real.logb_pos one_lt_two hα0
  have hRR : 2 * Real.logb 2 ρ⁻¹ = Real.logb 2 α := by
    have h1 : (ρ⁻¹) ^ 2 = α := by
      field_simp at hρ ⊢
      nlinarith [hρ, hρ0]
    calc 2 * Real.logb 2 ρ⁻¹ = ((2 : ℕ) : ℝ) * Real.logb 2 ρ⁻¹ := by norm_num
      _ = Real.logb 2 ((ρ⁻¹) ^ (2 : ℕ)) := (Real.logb_pow _ _ _).symm
      _ = Real.logb 2 α := by rw [h1]
  have hR : Real.logb 2 ρ⁻¹ = Real.logb 2 α / 2 := by linarith
  have hstep : (Real.logb 2 α)⁻¹ + (Real.logb 2 ρ⁻¹)⁻¹ = 3 / Real.logb 2 α := by
    rw [hR]; field_simp; ring
  rw [hstep, div_lt_one hL]
  constructor
  · intro h
    have h8 : (3 : ℝ) = Real.logb 2 8 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.logb_pow]
      simp
    rw [h8] at h
    exact (Real.logb_lt_logb_iff one_lt_two (by norm_num) (by linarith)).mp h
  · intro h
    have h8 : (3 : ℝ) = Real.logb 2 8 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.logb_pow]
      simp
    rw [h8]
    exact (Real.logb_lt_logb_iff one_lt_two (by norm_num) (by linarith)).mpr h

/-- The threshold `α > 8` is `a ≥ 8`, since `α ∈ (a, a+1)`.  So in degree three Route A fires
exactly from `a = 2³ = 8` on, as in degree two it fires exactly from `a = 2² = 4` on. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem eight_lt_iff_of_mem_Ioo {α : ℝ} (hmem : α ∈ Set.Ioo ((a : ℝ)) ((a : ℝ) + 1)) :
    8 < α ↔ 8 ≤ a := by
  obtain ⟨h1, h2⟩ := hmem
  constructor
  · intro h
    have : (7 : ℝ) < (a : ℝ) := by linarith
    have h7 : (7 : ℕ) < a := by exact_mod_cast this
    omega
  · intro h
    have : (8 : ℝ) ≤ (a : ℝ) := by exact_mod_cast h
    linarith

end BB61

end
