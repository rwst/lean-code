/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.LowerBound
import BB61.RouteA
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Theorem E: the three open quadratic units, and why no small certificate reaches them

`paper.tex`, Theorem E:

> Let `H₀ = 64`.  No trigonometric certificate of degree `≤ H₀` exists at `α = 1 + √2`: an
> explicit convex combination of `129` periodic-orbit measures is flat to degree `64` with entropy
> `≥ 0.677497 > 0.440687 = h_min(1 + √2)`, so `E_64(1 + √2) ≥ 0.677497`.  Likewise
> `E_64 ≥ 0.653915 > h_min = 0.597382` at `(3 + √13)/2`, and `E_32 ≥ 0.576992 > h_min = 0.481212`
> at `(3 + √5)/2`.

This file formalises the theorem's **inference** and its **arithmetic**, at all three `α`.  The
inference is Theorem 9.1 (`BB61/LowerBound.lean`) followed by the easy half of Theorem 3.4; the
arithmetic is the strict inequality `½ log α < c` at each of the three constants, which is what
makes the pool's entropy exceed the Ledrappier–Young floor.  Both are proved from Lean's three
standard axioms.

## What is a hypothesis here, and why

The pools themselves are **not** formalised: each is a mixture of memory-`12` Markov measures
(`BB61/m7_price.py`, `BB61/r1b_pool.py`) whose moments `Φ_h` are infinite series evaluated to
`10⁻¹³` over a `4096`-state stationary chain, and reproducing that computation inside the Lean
kernel with rigorous enclosures is a project of its own.  So each theorem below takes a
`BB61.FlatPool` — the paper's "explicit convex combination", as a *typed object* carrying the
measures, the weights, and the flatness `∑_j λ_j Φ_h(ν_j) = 0` — together with the numeric lower
bound on its entropy, and proves everything that follows from it.  Nothing else is assumed: the
hypothesis is exactly the sentence of Theorem E that the linear program supplies, and no axiom
stands in for it.

Two remarks on the shape of that hypothesis.  It is a `structure`, not an `∃`, so that a future
formalisation of the pool plugs straight in.  And it is stated with `FlatPool.entropy`, the LP's
own objective `∑_j λ_j h(ν_j)`, rather than with `E_H(α)`: that is the quantity the linear program
computes, and Theorem 9.1 is what converts it.

## Main results

* `BB61.onePlusSqrt2`, `BB61.halfThreePlusSqrt5`, `BB61.halfThreePlusSqrt13` — the three `α`, as
  `QuadSetup`s.  All three are quadratic **units** greater than `2`, so `½ log α` really is the
  entropy floor of Theorem B(i).
* `BB61.log_div_two_lt_of_lt_pow` — the arithmetic tool: `x < (1 + 2c/n)ⁿ ⇒ ½ log x < c`.
* `BB61.onePlusSqrt2_floor_lt`, `BB61.halfThreePlusSqrt5_floor_lt`,
  `BB61.halfThreePlusSqrt13_floor_lt` — the three numeric inequalities of Theorem E,
  `h_min(α) < c`.
* `BB61.theoremE_onePlusSqrt2`, `BB61.theoremE_halfThreePlusSqrt5`,
  `BB61.theoremE_halfThreePlusSqrt13` — **Theorem E**: no potential of any degree `≤ H₀` has
  pressure below the floor.
* `BB61.theoremE_onePlusSqrt2_entDegree` — the same as `H₀ < H_ent(α)`.

## Reference

* `paper.tex`, Theorem E and Section 9 (Theorem 9.1, and the bracket table).
-/

namespace BB61

open MeasureTheory Dynamics

/-! ## Bounding `½ log α` from above -/

/-- `(1 + x/n)ⁿ ≤ exp x` for `x ≥ 0`: Bernoulli through `1 + t ≤ exp t`. -/
@[category API, AMS 26, ref "Bug12", group "bugeaud_10_61"]
theorem pow_one_add_div_le_exp {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    (1 + x / n) ^ n ≤ Real.exp x := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using Real.one_le_exp hx
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hstep : 1 + x / n ≤ Real.exp (x / n) := by
    have := Real.add_one_le_exp (x / n); linarith
  have hnn : (0 : ℝ) ≤ 1 + x / n := by positivity
  calc (1 + x / n) ^ n ≤ (Real.exp (x / n)) ^ n := by
        exact pow_le_pow_left₀ hnn hstep n
    _ = Real.exp x := by
        rw [← Real.exp_nat_mul]; congr 1; field_simp

/-- **The arithmetic of Theorem E**: a rational lower bound for `exp (2c)` certifies
`½ log x < c`.  Taking `n = 8` puts all three constants of Theorem E comfortably inside. -/
@[category API, AMS 26, ref "Bug12", group "bugeaud_10_61"]
theorem log_div_two_lt_of_lt_pow {x c : ℝ} (hx : 0 < x) (hc : 0 ≤ c) (n : ℕ)
    (h : x < (1 + 2 * c / n) ^ n) : Real.log x / 2 < c := by
  have hexp : x < Real.exp (2 * c) :=
    lt_of_lt_of_le h (pow_one_add_div_le_exp (by linarith) n)
  have := (Real.log_lt_iff_lt_exp hx).2 hexp
  linarith

/-! ## `√2` and `√13` -/

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem sqrt2_lt : Real.sqrt 2 < 1.4142136 :=
  (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem lt_sqrt2 : (1.4142135 : ℝ) < Real.sqrt 2 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem sqrt13_lt : Real.sqrt 13 < 3.6055514 :=
  (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem lt_sqrt13 : (3.6055512 : ℝ) < Real.sqrt 13 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)

/-! ## The three setups -/

/-- `α = 1 + √2`, the silver ratio: root of `X² - 2X - 1`, trace `2`, norm `-1`, conjugate
`1 - √2`.  The smallest Pisot number above `2`, and the hardest open case of 10.61. -/
noncomputable def onePlusSqrt2 : QuadSetup where
  a := 2
  b := 1
  α := 1 + Real.sqrt 2
  root := by
    have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    push_cast
    nlinarith [h]
  one_lt := by have := Real.sqrt_pos.mpr (show (0:ℝ) < 2 by norm_num); linarith
  conj_lt := by
    have h1 := lt_sqrt2
    have h2 := sqrt2_lt
    rw [abs_lt]
    push_cast
    constructor <;> linarith

@[simp, category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem onePlusSqrt2_alpha : onePlusSqrt2.α = 1 + Real.sqrt 2 := rfl

/-- `α = 1 + √2` is a quadratic unit greater than `2`, so `½ log α` is the entropy floor of
Theorem B(i). -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem onePlusSqrt2_two_lt : 2 < onePlusSqrt2.α := by
  have := lt_sqrt2; rw [onePlusSqrt2_alpha]; linarith

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem onePlusSqrt2_unit : onePlusSqrt2.b = 1 ∨ onePlusSqrt2.b = -1 := Or.inl rfl

/-- `α = (3 + √5)/2 = φ²`: root of `X² - 3X + 1`, trace `3`, norm `1`, conjugate `(3 - √5)/2`. -/
noncomputable def halfThreePlusSqrt5 : QuadSetup where
  a := 3
  b := -1
  α := (3 + Real.sqrt 5) / 2
  root := by
    have h : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    push_cast
    nlinarith [h]
  one_lt := by have := two_lt_sqrt5; linarith
  conj_lt := by
    have h1 := two_lt_sqrt5
    have h2 : Real.sqrt 5 < 3 := lt_trans sqrt5_lt (by norm_num)
    rw [abs_lt]
    push_cast
    constructor <;> linarith

@[simp, category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem halfThreePlusSqrt5_alpha : halfThreePlusSqrt5.α = (3 + Real.sqrt 5) / 2 := rfl

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem halfThreePlusSqrt5_two_lt : 2 < halfThreePlusSqrt5.α := by
  have := two_lt_sqrt5; rw [halfThreePlusSqrt5_alpha]; linarith

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem halfThreePlusSqrt5_unit : halfThreePlusSqrt5.b = 1 ∨ halfThreePlusSqrt5.b = -1 :=
  Or.inr rfl

/-- `α = (3 + √13)/2`: root of `X² - 3X - 1`, trace `3`, norm `-1`, conjugate `(3 - √13)/2`. -/
noncomputable def halfThreePlusSqrt13 : QuadSetup where
  a := 3
  b := 1
  α := (3 + Real.sqrt 13) / 2
  root := by
    have h : Real.sqrt 13 ^ 2 = 13 := Real.sq_sqrt (by norm_num)
    push_cast
    nlinarith [h]
  one_lt := by have := lt_sqrt13; linarith
  conj_lt := by
    have h1 := lt_sqrt13
    have h2 := sqrt13_lt
    rw [abs_lt]
    push_cast
    constructor <;> linarith

@[simp, category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem halfThreePlusSqrt13_alpha : halfThreePlusSqrt13.α = (3 + Real.sqrt 13) / 2 := rfl

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem halfThreePlusSqrt13_two_lt : 2 < halfThreePlusSqrt13.α := by
  have := lt_sqrt13; rw [halfThreePlusSqrt13_alpha]; linarith

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem halfThreePlusSqrt13_unit : halfThreePlusSqrt13.b = 1 ∨ halfThreePlusSqrt13.b = -1 :=
  Or.inl rfl

/-! ## The three numeric inequalities of Theorem E

`h_min(α) = ½ log α` at a quadratic unit (`LY.hMin_eq_of_unit`), so each of these is the paper's
`c > h_min(α)`.  The printed values are `0.440687`, `0.481212`, `0.597382`; the bounds below are
what `pow_one_add_div_le_exp` certifies at `n = 8`, with room to spare. -/

/-- `h_min(1 + √2) = 0.4406867… < 0.677497`. -/
@[category research solved, AMS 37 11, ref "Bug12", group "bugeaud_10_61"]
theorem onePlusSqrt2_floor_lt : Real.log onePlusSqrt2.α / 2 < 0.677497 := by
  refine log_div_two_lt_of_lt_pow ?_ (by norm_num) 8 ?_
  · have := Real.sqrt_nonneg 2; rw [onePlusSqrt2_alpha]; linarith
  · have hb : (3.4 : ℝ) < (1 + 2 * 0.677497 / (8 : ℕ)) ^ 8 := by norm_num
    have := sqrt2_lt
    rw [onePlusSqrt2_alpha]
    linarith

/-- `h_min((3 + √5)/2) = 0.4812118… < 0.576992`. -/
@[category research solved, AMS 37 11, ref "Bug12", group "bugeaud_10_61"]
theorem halfThreePlusSqrt5_floor_lt : Real.log halfThreePlusSqrt5.α / 2 < 0.576992 := by
  refine log_div_two_lt_of_lt_pow ?_ (by norm_num) 8 ?_
  · have := Real.sqrt_nonneg 5; rw [halfThreePlusSqrt5_alpha]; linarith
  · have hb : (2.9 : ℝ) < (1 + 2 * 0.576992 / (8 : ℕ)) ^ 8 := by norm_num
    have := sqrt5_lt
    rw [halfThreePlusSqrt5_alpha]
    linarith

/-- `h_min((3 + √13)/2) = 0.5973816… < 0.653915`. -/
@[category research solved, AMS 37 11, ref "Bug12", group "bugeaud_10_61"]
theorem halfThreePlusSqrt13_floor_lt : Real.log halfThreePlusSqrt13.α / 2 < 0.653915 := by
  refine log_div_two_lt_of_lt_pow ?_ (by norm_num) 8 ?_
  · have := Real.sqrt_nonneg 13; rw [halfThreePlusSqrt13_alpha]; linarith
  · have hb : (3.35 : ℝ) < (1 + 2 * 0.653915 / (8 : ℕ)) ^ 8 := by norm_num
    have := sqrt13_lt
    rw [halfThreePlusSqrt13_alpha]
    linarith

/-! ## Theorem E -/

/-- **Theorem E at `α = 1 + √2`, with `H₀ = 64`.**  A pool of invariant measures, flat to degree
`64`, of entropy at least `0.677497`, forbids every degree-`≤ 64` pressure certificate at
`1 + √2`: the pressure of `ψ_a` stays strictly above the entropy floor `½ log α = 0.440687…`.

The pool is the hypothesis (see the module doc); everything else is proved. -/
@[category research solved, AMS 37 28 11, ref "Bug12", group "bugeaud_10_61"]
theorem theoremE_onePlusSqrt2 (pool : FlatPool onePlusSqrt2 (Finset.Icc 1 (64 : ℤ)))
    (hent : (0.677497 : ℝ) ≤ pool.entropy) (H : ℕ) (hH : H ≤ 64) (a : ℤ → ℂ) :
    ((Real.log onePlusSqrt2.α / 2 : ℝ) : EReal)
      < partitionPressure shiftZ
          (fourierPotential onePlusSqrt2 (Finset.Icc 1 (H : ℤ)) a) coordPartition := by
  refine forall_le_floor_lt_partitionPressure onePlusSqrt2 64 onePlusSqrt2_floor_lt ?_ H hH a
  have hcast : ((64 : ℕ) : ℤ) = (64 : ℤ) := by norm_num
  rw [hcast]
  exact le_trans (by exact_mod_cast hent) pool.entropy_le_priceEntropy

/-- **Theorem E at `α = (3 + √13)/2`, with `H₀ = 64`.** -/
@[category research solved, AMS 37 28 11, ref "Bug12", group "bugeaud_10_61"]
theorem theoremE_halfThreePlusSqrt13 (pool : FlatPool halfThreePlusSqrt13 (Finset.Icc 1 (64 : ℤ)))
    (hent : (0.653915 : ℝ) ≤ pool.entropy) (H : ℕ) (hH : H ≤ 64) (a : ℤ → ℂ) :
    ((Real.log halfThreePlusSqrt13.α / 2 : ℝ) : EReal)
      < partitionPressure shiftZ
          (fourierPotential halfThreePlusSqrt13 (Finset.Icc 1 (H : ℤ)) a) coordPartition := by
  refine forall_le_floor_lt_partitionPressure halfThreePlusSqrt13 64
    halfThreePlusSqrt13_floor_lt ?_ H hH a
  have hcast : ((64 : ℕ) : ℤ) = (64 : ℤ) := by norm_num
  rw [hcast]
  exact le_trans (by exact_mod_cast hent) pool.entropy_le_priceEntropy

/-- **Theorem E at `α = (3 + √5)/2`, with `H₀ = 32`.**  The one case where the paper's bracket
closes only at `32` modes: the pool at `64` was proved too small (`BB61/r1b_pool.py`). -/
@[category research solved, AMS 37 28 11, ref "Bug12", group "bugeaud_10_61"]
theorem theoremE_halfThreePlusSqrt5 (pool : FlatPool halfThreePlusSqrt5 (Finset.Icc 1 (32 : ℤ)))
    (hent : (0.576992 : ℝ) ≤ pool.entropy) (H : ℕ) (hH : H ≤ 32) (a : ℤ → ℂ) :
    ((Real.log halfThreePlusSqrt5.α / 2 : ℝ) : EReal)
      < partitionPressure shiftZ
          (fourierPotential halfThreePlusSqrt5 (Finset.Icc 1 (H : ℤ)) a) coordPartition := by
  refine forall_le_floor_lt_partitionPressure halfThreePlusSqrt5 32
    halfThreePlusSqrt5_floor_lt ?_ H hH a
  have hcast : ((32 : ℕ) : ℤ) = (32 : ℤ) := by norm_num
  rw [hcast]
  exact le_trans (by exact_mod_cast hent) pool.entropy_le_priceEntropy

/-! ## Theorem E on the data the linear programs actually produce

The pools of `BB61/m7_price.py` are flat only to a residual — `|Φ_h| ≤ 3.6·10⁻⁹` at `H = 64` and
`α = 1 + √2` — so the exact `FlatPool` above idealises them.  The degradation clause prices that
residual, and what it buys is a *quantitative* no-go: a certificate that survives the pool must
carry an enormous multiplier.  Nothing is idealised here.
-/

/-- A cruder upper bound for the floor at `1 + √2` than the constant of Theorem E, but a numeric
one: `½ log(1 + √2) = 0.4406867… < 0.45`.  Certified at `n = 32`; the printed `0.440687` itself
would need `n > 3·10⁴`, which is why the theorems above are stated against `c` and not against a
decimal expansion of the floor. -/
@[category API, AMS 37 11, ref "Bug12", group "bugeaud_10_61"]
theorem onePlusSqrt2_floor_lt_045 : Real.log onePlusSqrt2.α / 2 < 0.45 := by
  refine log_div_two_lt_of_lt_pow ?_ (by norm_num) 32 ?_
  · have := Real.sqrt_nonneg 2; rw [onePlusSqrt2_alpha]; linarith
  · have hb : (2.42 : ℝ) < (1 + 2 * 0.45 / (32 : ℕ)) ^ 32 := by norm_num
    have := sqrt2_lt
    rw [onePlusSqrt2_alpha]
    linarith

/-- **Theorem E at `1 + √2`, on the approximate pool.**  A pool of invariant measures whose
moments on `{1, …, 64}` are at most `10⁻⁸` in modulus, of weighted entropy at least `0.677497`,
forces every degree-`64` certificate to have `‖a‖₁ > 2·10⁷`.

This is the form the linear programs of `BB61/m7_price.py` actually support: their residual at
`H = 64` is `3.6·10⁻⁹`.  The exact-flatness hypothesis of `theoremE_onePlusSqrt2` is the paper's
idealisation of it; here nothing is idealised, and the price of the residual is paid explicitly by
the `ℓ¹` bound. -/
@[category research solved, AMS 37 28 11, ref "Bug12", group "bugeaud_10_61"]
theorem theoremE_onePlusSqrt2_approx {ι' : Type*} {s : Finset ι'} {lam : ι' → ℝ}
    {ν : ι' → ProbabilityMeasure Shift}
    (hlam : ∀ j ∈ s, 0 ≤ lam j) (hsum : ∑ j ∈ s, lam j = 1)
    (hν : ∀ j ∈ s, ν j ∈ invMeasures)
    (hε : ∀ h ∈ Finset.Icc (1 : ℤ) 64,
      ‖∑ j ∈ s, (lam j : ℂ) * fourierMoment onePlusSqrt2 h (ν j)‖ ≤ 0.00000001)
    (hent : (0.677497 : ℝ) ≤ ∑ j ∈ s, lam j * shiftEntropy (ν j)) (a : ℤ → ℂ)
    (hpress : partitionPressure shiftZ
        (fourierPotential onePlusSqrt2 (Finset.Icc 1 (64 : ℤ)) a) coordPartition
      < ((Real.log onePlusSqrt2.α / 2 : ℝ) : EReal)) :
    (2 * 10 ^ 7 : ℝ) < ∑ h ∈ Finset.Icc (1 : ℤ) 64, ‖a h‖ := by
  have hpos : (0 : ℝ) < 0.00000001 := by norm_num
  have hmain := lt_norm_one_of_partitionPressure_lt onePlusSqrt2 (Finset.Icc 1 (64 : ℤ))
    hlam hsum hν hpos hε a hpress
  refine lt_of_le_of_lt ?_ hmain
  rw [le_div_iff₀ hpos]
  have harith : (2 * 10 ^ 7 : ℝ) * 0.00000001 = 0.2 := by norm_num
  have hfl := onePlusSqrt2_floor_lt_045
  linarith

/-! ## The same, as a statement about `H_ent` -/

/-- **`64 < H_ent(1 + √2)`.**  The entropy criterion of Corollary 3.5 fires at no degree `≤ 64`.

The extra hypothesis is that it fires at *some* degree — equivalently, by Corollary 3.5, that
10.61 holds at `1 + √2`, which is exactly what is open.  Without it `H_ent` is `sInf ∅ = 0` and the
statement would be about a convention rather than about `α`. -/
@[category research solved, AMS 37 28 11, ref "Bug12", group "bugeaud_10_61"]
theorem theoremE_onePlusSqrt2_entDegree (pool : FlatPool onePlusSqrt2 (Finset.Icc 1 (64 : ℤ)))
    (hent : (0.677497 : ℝ) ≤ pool.entropy)
    (hne : ∃ H : ℕ, priceEntropy onePlusSqrt2 (Finset.Icc 1 (H : ℤ))
      < ((Real.log onePlusSqrt2.α / 2 : ℝ) : EReal)) :
    64 < entDegree onePlusSqrt2 := by
  refine lt_entDegree_of_le_priceEntropy onePlusSqrt2 64 onePlusSqrt2_floor_lt ?_ hne
  have hcast : ((64 : ℕ) : ℤ) = (64 : ℤ) := by norm_num
  rw [hcast]
  exact le_trans (by exact_mod_cast hent) pool.entropy_le_priceEntropy

/-- The pool bound of Theorem E is consistent with the ceiling `E_H(α) ≤ log 2 = 0.693147…`.  At
`1 + √2` the bound `0.677497` uses `93.8%` of the room the ceiling leaves above the floor; the
paper's `96.1%` is the same fraction for the *upper* bound `E_64 = 0.683271` of the bracket. -/
@[category API, AMS 37 28 11, ref "Bug12", group "bugeaud_10_61"]
theorem theoremE_onePlusSqrt2_le_log_two (pool : FlatPool onePlusSqrt2 (Finset.Icc 1 (64 : ℤ))) :
    pool.entropy ≤ Real.log 2 := by
  have h := le_trans pool.entropy_le_priceEntropy
    (priceEntropy_le_log_two onePlusSqrt2 (Finset.Icc 1 (64 : ℤ)))
  exact_mod_cast h

end BB61
