/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TH.CapstoneM4
import CITED.SubspaceTriple
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Stage 2c, direct: the kernel (K) by one three-variable Subspace application

The kernel (K) — for every rational `θ ∈ (0, 1)` only finitely many pairs
`2 ≤ a < c` satisfy `‖(3/2)^c − (3/2)^a‖ ≤ θ^c` — is proved here **directly**, by
a single application of the Subspace Theorem in three variables followed by an
elementary analysis of the exceptional subspaces.  This replaces the earlier
route (gap dichotomy + the Nair–Kumar–Rout `S`-unit pair theorem + the huge-gap
slice of `TH.GapSlices`), which is no longer on the dependency path of
`complexity_superlinear`.  The argument is the one of `short.tex` (Proposition 3).

## The argument

To a violator `(a, c)` with gap `s = c − a ≥ 2` attach the projective point
`x = (M, (3/2)^c, (3/2)^a)`, `M` the integer nearest to `(3/2)^c − (3/2)^a`;
up to the scalar `2^c` this is the integer point `(2^c M, 3^c, 2^s 3^a)`.  With
`S = {∞, 2, 3}`, the forms `X₁ − X₂ − X₀, X₁, X₂` at `∞` and the coordinate forms
at `2` and `3`, the double product collapses to `‖(3/2)^c − (3/2)^a‖·M·3^{-c}
≤ θ^c`, uniformly in the gap (`SubspaceTriple.member_solves`, the engine of the former NKR
derivation, with `α = (1, −1)`).  The Subspace Theorem confines the points to
finitely many proper subspaces; by pigeonhole one subspace `a₀X₀ + a₁X₁ + a₂X₂ = 0`
contains infinitely many of them, and each case is elementary:

* `a₀ = 0`: the ratio `(3/2)^{c−a} = −a₂/a₁` is constant, so the gap is a fixed
  `s₀` and the family lies in the bounded-gap slice, finite by Stage 2b
  (`gapBounded_slice_finite`, i.e. Ridout / Mahler with a rational multiplier).
* `a₀ ≠ 0`: `M` is a fixed rational combination of the two `S`-units, so the
  distance equals `|β₁ (3/2)^c + β₂ (3/2)^a|` with fixed `β₁, β₂`.  If both
  vanish, the parity floor `distToNearestInt_orbit_pos` is contradicted.  If
  `β₁ = 0 ≠ β₂` the distance is `≥ |β₂|`; if `β₁ ≠ 0` and the gap is `≥ s₁`
  (with `(3/2)^{s₁} ≥ 2|β₂|/|β₁|`) the distance is `≥ |β₁|/2`.  A positive floor
  against `≤ θ^c` bounds `c` (`finite_of_dist_ge`); gaps `< s₁` are the
  bounded-gap slice again.

Since `(3/2)^{c−a} → ∞` with the gap, there is no ratio accumulation to control,
which is exactly what made the general NKR theorem (and its Corvaja–Zannier
branch) unnecessary here.

**Axiom footprint**: std3 + `Subspace.evertseSchlickewei` at `n = 3` (this file)
and `n = 2` (the bounded-gap slice, through the derived Corvaja–Zannier Main
Theorem).  Everything is ineffective.

## Contents

* `pairRepulsion_all` — **(K) at every rational scale**.
* `kernel_holds` — the kernel (K), quantified.
* `complexity_superlinear` — **M4**: `p_T(k)/k → ∞`.
* `middleBandViolators_finite` — the middle band is finite (the hypothesis of
  `TH.superlinear_of_middleBand`, discharged).

## References

* [BG06] Bombieri, Gubler. *Heights in Diophantine Geometry*, Ch. 7 (the Subspace
  Theorem, `CITED/SubspaceTheorem.lean`).
* [CZ04] Corvaja, Zannier. Acta Math. **193** (2004), 175–191 (the `n = 2` input,
  `TH/GapSlices.lean`).
* `short.tex` (the `Superlinear-Complexity` paper repository): the two-page proof
  formalized here.
-/

namespace TH

open Subspace Rat.AbsoluteValue Height CZ SubspaceTriple

attribute [local instance] Classical.propDecidable

/-! ## Helpers -/

private lemma three_halves_pow_injective :
    Function.Injective (fun n : ℕ => (3 / 2 : ℚ) ^ n) := by
  have h : StrictMono (fun n : ℕ => (3 / 2 : ℚ) ^ n) := fun m n hmn => by
    exact pow_lt_pow_right₀ (by norm_num) hmn
  exact h.injective

/-- The ε₁-window of the Subspace application: for `a < c`,
`θ^c < (3^c·3^a)^{-ε₁}` with `ε₁ = log θ⁻¹/(2 log 3)`. -/
private lemma theta_pow_lt_height_rpow {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {a c : ℕ} (hac : a < c) :
    θ ^ c < (((3 ^ c * 3 ^ a : ℕ)) : ℝ)
      ^ (-(Real.log θ⁻¹ / (2 * Real.log 3))) := by
  have h3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hlogθ : Real.log θ < 0 := Real.log_neg hθ0 hθ1
  have hcast : (((3 ^ c * 3 ^ a : ℕ)) : ℝ) = (3 : ℝ) ^ c * 3 ^ a := by
    push_cast
    ring
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
      * (-(-Real.log θ / (2 * Real.log 3))) = ((c : ℝ) + a) * Real.log θ / 2 := by
    field_simp
  rw [hkey]
  have hca : (a : ℝ) < (c : ℝ) := by exact_mod_cast hac
  nlinarith [mul_neg_of_pos_of_neg (show (0 : ℝ) < (c : ℝ) - a by linarith) hlogθ]

/-- A positive floor on the kernel distance bounds `c`: the violators with
`‖(3/2)^c − (3/2)^a‖ ≥ b > 0` are finite, since `b ≤ θ^c` forces `c < n` once
`θ^n < b`. -/
private lemma finite_of_dist_ge (θ : ℚ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (b : ℚ)
    (hb : 0 < b) :
    {p ∈ kernelViolators θ |
      b ≤ ((3 / 2 : ℚ) ^ p.2 - (3 / 2 : ℚ) ^ p.1).distToNearestInt}.Finite := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hb hθ1
  apply Set.Finite.subset ((Set.finite_Iio n).prod (Set.finite_Iio n))
  rintro ⟨a, c⟩ ⟨⟨-, hac, hdist⟩, hbdist⟩
  have hc : c < n := by
    by_contra hcn
    push Not at hcn
    have : θ ^ c ≤ θ ^ n := pow_le_pow_of_le_one hθ0.le hθ1.le hcn
    linarith
  exact ⟨Set.mem_Iio.mpr (by omega), Set.mem_Iio.mpr hc⟩

/-- The vector attached to a violating pair `(a, c)`: `(M, (3/2)^c, (3/2)^a)` with
`M = round((3/2)^c − (3/2)^a)`. -/
private noncomputable def xv (p : ℕ × ℕ) : Fin 3 → ℚ :=
  ![((round ((3 / 2 : ℚ) ^ p.2 - (3 / 2 : ℚ) ^ p.1) : ℤ) : ℚ),
    (3 / 2 : ℚ) ^ p.2, (3 / 2 : ℚ) ^ p.1]

private lemma xv_ne_zero (p : ℕ × ℕ) : xv p ≠ 0 := by
  intro h0
  have h1 := congrFun h0 1
  simp only [xv, Matrix.cons_val_one, Pi.zero_apply] at h1
  exact (by positivity : (0 : ℚ) < (3 / 2) ^ p.2).ne' h1

/-- The Subspace inequality for a violator of gap `≥ 2`: `SubspaceTriple.member_solves` with
`α = (1, −1)`, `u₁ = (3/2)^c`, `u₂ = (3/2)^a`. -/
private lemma xv_solves (θ : ℚ) (hθ0 : 0 < θ) (hθ1 : θ < 1) {a c : ℕ}
    (hp : (a, c) ∈ kernelViolators θ) (hgap : a + 2 ≤ c) :
    approxProduct {Rat.AbsoluteValue.real, padic 2, padic 3} (Lforms3 1 (-1)) (xv (a, c))
      ≤ mulHeight (xv (a, c))
          ^ (-(3 : ℝ) - Real.log (θ : ℝ)⁻¹ / (2 * Real.log 3) / 4) := by
  obtain ⟨-, hac, hdist⟩ := hp
  have hθ0' : (0 : ℝ) < (θ : ℝ) := by exact_mod_cast hθ0
  have hθ1' : (θ : ℝ) < 1 := by exact_mod_cast hθ1
  have hεpos : 0 < Real.log (θ : ℝ)⁻¹ / (2 * Real.log 3) := by
    apply div_pos
    · rw [Real.log_inv]
      have := Real.log_neg hθ0' hθ1'
      linarith
    · have := Real.log_pos (show (1 : ℝ) < 3 by norm_num)
      linarith
  have hd : (((1 : ℚ) * uval (-(c : ℤ)) c + (-1 : ℚ) * uval (-(a : ℤ)) a).distToNearestInt : ℝ)
      < ((height23 (-(c : ℤ)) c * height23 (-(a : ℤ)) a : ℕ) : ℝ)
          ^ (-(Real.log (θ : ℝ)⁻¹ / (2 * Real.log 3))) := by
    simp only [uval_neg_natCast, height23_neg_natCast, one_mul, neg_one_mul,
      ← sub_eq_add_neg]
    calc (((3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a).distToNearestInt : ℝ)
        ≤ ((θ ^ c : ℚ) : ℝ) := by exact_mod_cast hdist
      _ = (θ : ℝ) ^ c := by push_cast; ring
      _ < _ := theta_pow_lt_height_rpow hθ0' hθ1' hac
  have hbig : (((|(1 : ℚ)| + |(-1 : ℚ)| + 1 : ℚ) : ℝ)) ^ 2
      ≤ ((height23 (-(c : ℤ) - -(a : ℤ)) ((c : ℤ) - a) : ℕ) : ℝ) := by
    have e1 : -(c : ℤ) - -(a : ℤ) = -((c - a : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hac.le]; ring
    have e2 : (c : ℤ) - a = ((c - a : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hac.le]; ring
    rw [e1, e2, height23_neg_natCast]
    have h9 : (3 : ℝ) ^ 2 ≤ (3 : ℝ) ^ (c - a) := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num
    exact_mod_cast h9
  have h := member_solves 1 (-1) _ hεpos (-(c : ℤ)) c (-(a : ℤ)) a hd hbig
  simp only [uval_neg_natCast, one_mul, neg_one_mul, ← sub_eq_add_neg] at h
  exact h

/-! ## The kernel (K) -/

/-- **The kernel (K) at every rational scale**, by one three-variable Subspace
application (`short.tex`, Proposition 3): for every rational `θ ∈ (0, 1)`, only
finitely many pairs `2 ≤ a < c` satisfy `‖(3/2)^c − (3/2)^a‖ ≤ θ^c`.  The
exceptional subspaces reduce either to a fixed gap (the Stage-2b bounded-gap
slice) or to a positive floor on the distance (which bounds `c`).  Ineffective.
Footprint std3 + `Subspace.evertseSchlickewei`. -/
@[category research solved, AMS 11, ref "BG06", group "three_halves_m4"]
theorem pairRepulsion_all (θ : ℚ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    PairRepulsion θ := by
  by_contra hV
  have hVinf : (kernelViolators θ).Infinite := hV
  have hθ0' : (0 : ℝ) < (θ : ℝ) := by exact_mod_cast hθ0
  have hθ1' : (θ : ℝ) < 1 := by exact_mod_cast hθ1
  have hεpos : 0 < Real.log (θ : ℝ)⁻¹ / (2 * Real.log 3) := by
    apply div_pos
    · rw [Real.log_inv]
      have := Real.log_neg hθ0' hθ1'
      linarith
    · have := Real.log_pos (show (1 : ℝ) < 3 by norm_num)
      linarith
  -- gap ≥ 2 keeps infinitely many violators (gap ≤ 1 is a finite slice)
  set V₂ : Set (ℕ × ℕ) := {p ∈ kernelViolators θ | p.1 + 2 ≤ p.2} with hV₂def
  have hV₂inf : V₂.Infinite := by
    intro hfin
    apply hVinf
    apply Set.Finite.subset (hfin.union (gapBounded_slice_finite 1 θ hθ0 hθ1))
    intro p hp
    by_cases h : p.1 + 2 ≤ p.2
    · exact Or.inl ⟨hp, h⟩
    · exact Or.inr ⟨hp, by omega⟩
  -- the Subspace Theorem at n = 3
  obtain ⟨T, hTproper, hTcover⟩ := evertseSchlickewei_rat (n := 3) (by norm_num)
    {Rat.AbsoluteValue.real, padic 2, padic 3} Subspace.isPlace_real_padic_two_three
    (Lforms3 1 (-1))
    (fun v _ => lforms3_linearIndependent 1 (-1) v)
    (Real.log (θ : ℝ)⁻¹ / (2 * Real.log 3) / 4) (by positivity)
  have hcover : ∀ p ∈ V₂, ∃ W ∈ T, xv p ∈ W := by
    rintro ⟨a, c⟩ ⟨hp, hgap⟩
    apply hTcover (xv (a, c)) (xv_ne_zero _)
    have h := xv_solves θ hθ0 hθ1 hp hgap
    have hexp : (-(3 : ℝ) - Real.log (θ : ℝ)⁻¹ / (2 * Real.log 3) / 4)
        = (-((3 : ℕ) : ℝ) - Real.log (θ : ℝ)⁻¹ / (2 * Real.log 3) / 4) := by norm_num
    rw [hexp] at h
    exact h
  -- pigeonhole: one subspace contains infinitely many of the vectors
  have hWex : ∃ W ∈ T, {p ∈ V₂ | xv p ∈ W}.Infinite := by
    by_contra hall
    push Not at hall
    apply hV₂inf
    have hcov : V₂ ⊆ ⋃ W ∈ T, {p ∈ V₂ | xv p ∈ W} := by
      intro p hp
      obtain ⟨W, hWT, hxW⟩ := hcover p hp
      exact Set.mem_biUnion hWT ⟨hp, hxW⟩
    exact Set.Finite.subset (T.finite_toSet.biUnion
      (fun W hW => hall W (Finset.mem_coe.mp hW))) hcov
  obtain ⟨W, hWT, hWinf⟩ := hWex
  set F : Set (ℕ × ℕ) := {p ∈ V₂ | xv p ∈ W} with hFdef
  have hFsub : F ⊆ kernelViolators θ := fun p hp => hp.1.1
  have hFgap : ∀ p ∈ F, p.1 + 2 ≤ p.2 := fun p hp => hp.1.2
  -- a nonzero functional vanishing on W
  obtain ⟨f, hf0, hfW⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
    (lt_top_iff_ne_top.mpr (hTproper W hWT)) inferInstance
  set a₀ : ℚ := f (fun j => if (0 : Fin 3) = j then 1 else 0) with ha₀def
  set a₁ : ℚ := f (fun j => if (1 : Fin 3) = j then 1 else 0) with ha₁def
  set a₂ : ℚ := f (fun j => if (2 : Fin 3) = j then 1 else 0) with ha₂def
  have hfx : ∀ x : Fin 3 → ℚ, f x = x 0 * a₀ + x 1 * a₁ + x 2 * a₂ := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ f x, Fin.sum_univ_three]
    simp only [smul_eq_mul, ha₀def, ha₁def, ha₂def]
  have hrel : ∀ p ∈ F,
      ((round ((3 / 2 : ℚ) ^ p.2 - (3 / 2 : ℚ) ^ p.1) : ℤ) : ℚ) * a₀
        + (3 / 2 : ℚ) ^ p.2 * a₁ + (3 / 2 : ℚ) ^ p.1 * a₂ = 0 := by
    intro p hp
    have hfx0 : f (xv p) = 0 := by
      have h1 : f (xv p) ∈ W.map f := Submodule.mem_map_of_mem hp.2
      rwa [hfW, Submodule.mem_bot] at h1
    rw [hfx (xv p)] at hfx0
    simpa only [xv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] using hfx0
  have hFne : F.Nonempty := hWinf.nonempty
  have hane : ¬(a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0) := by
    rintro ⟨h0, h1, h2⟩
    apply hf0
    apply LinearMap.ext
    intro x
    rw [hfx x, h0, h1, h2]
    simp
  -- the bounded-gap slices are finite: a gap bound on F is a contradiction
  have hgapbound : ∀ S : ℕ, (∀ p ∈ F, p.2 ≤ p.1 + S) → False := by
    intro S hS
    apply hWinf
    apply Set.Finite.subset (gapBounded_slice_finite S θ hθ0 hθ1)
    intro p hp
    exact ⟨hFsub hp, hS p hp⟩
  rcases eq_or_ne a₀ 0 with ha₀0 | ha₀0
  · -- a₀ = 0: the ratio (3/2)^{c−a} = −a₂/a₁ is constant, so the gap is constant
    have ha₁0 : a₁ ≠ 0 := by
      intro h1
      obtain ⟨r, hrF⟩ := hFne
      have h := hrel r hrF
      rw [ha₀0, h1, mul_zero, mul_zero, zero_add, zero_add] at h
      have ha₂0 : a₂ = 0 :=
        (mul_eq_zero.mp h).resolve_left (by positivity)
      exact hane ⟨ha₀0, h1, ha₂0⟩
    have hconst : ∀ p ∈ F, (3 / 2 : ℚ) ^ (p.2 - p.1) = -a₂ / a₁ := by
      intro p hp
      have h := hrel p hp
      rw [ha₀0, mul_zero, zero_add] at h
      have hsplit : (3 / 2 : ℚ) ^ p.2 = (3 / 2 : ℚ) ^ p.1 * (3 / 2 : ℚ) ^ (p.2 - p.1) := by
        rw [← pow_add]
        congr 1
        have := hFgap p hp
        omega
      have hu₂ : (3 / 2 : ℚ) ^ p.1 ≠ 0 := by positivity
      rw [hsplit] at h
      have h' : (3 / 2 : ℚ) ^ (p.2 - p.1) * a₁ + a₂ = 0 := by
        have hfac : (3 / 2 : ℚ) ^ p.1 * ((3 / 2 : ℚ) ^ (p.2 - p.1) * a₁ + a₂) = 0 := by
          rw [← h]; ring
        exact (mul_eq_zero.mp hfac).resolve_left hu₂
      rw [eq_div_iff ha₁0]
      linear_combination h'
    obtain ⟨p₀, hp₀F⟩ := hFne
    apply hgapbound (p₀.2 - p₀.1)
    intro p hp
    have h := three_halves_pow_injective ((hconst p hp).trans (hconst p₀ hp₀F).symm)
    have := hFgap p hp
    omega
  · -- a₀ ≠ 0: the distance is a fixed combination `|β₁ (3/2)^c + β₂ (3/2)^a|`
    set β₁ : ℚ := 1 + a₁ / a₀ with hβ₁def
    set β₂ : ℚ := a₂ / a₀ - 1 with hβ₂def
    have hdisteq : ∀ p ∈ F,
        ((3 / 2 : ℚ) ^ p.2 - (3 / 2 : ℚ) ^ p.1).distToNearestInt
          = |β₁ * (3 / 2 : ℚ) ^ p.2 + β₂ * (3 / 2 : ℚ) ^ p.1| := by
      intro p hp
      have h := hrel p hp
      have hM : ((round ((3 / 2 : ℚ) ^ p.2 - (3 / 2 : ℚ) ^ p.1) : ℤ) : ℚ)
          = -(a₁ / a₀) * (3 / 2 : ℚ) ^ p.2 - (a₂ / a₀) * (3 / 2 : ℚ) ^ p.1 := by
        field_simp
        linear_combination h
      show |(3 / 2 : ℚ) ^ p.2 - (3 / 2 : ℚ) ^ p.1
          - ((round ((3 / 2 : ℚ) ^ p.2 - (3 / 2 : ℚ) ^ p.1) : ℤ) : ℚ)|
        = |β₁ * (3 / 2 : ℚ) ^ p.2 + β₂ * (3 / 2 : ℚ) ^ p.1|
      rw [hM]
      congr 1
      rw [hβ₁def, hβ₂def]
      ring
    -- a positive floor on the distance over F is a contradiction
    have hfloor : ∀ b : ℚ, 0 < b →
        (∀ p ∈ F, b ≤ ((3 / 2 : ℚ) ^ p.2 - (3 / 2 : ℚ) ^ p.1).distToNearestInt) → False := by
      intro b hb hle
      apply hWinf
      apply Set.Finite.subset (finite_of_dist_ge θ hθ0 hθ1 b hb)
      intro p hp
      exact ⟨hFsub hp, hle p hp⟩
    rcases eq_or_ne β₁ 0 with hβ₁0 | hβ₁0
    · rcases eq_or_ne β₂ 0 with hβ₂0 | hβ₂0
      · -- both vanish: the distance is zero, against the parity floor
        obtain ⟨p, hpF⟩ := hFne
        obtain ⟨ha2, hac, -⟩ := hFsub hpF
        have hpos := distToNearestInt_orbit_pos (a := p.1) (c := p.2) (by omega) hac
        rw [hdisteq p hpF, hβ₁0, hβ₂0, zero_mul, zero_mul, add_zero, abs_zero] at hpos
        exact lt_irrefl 0 hpos
      · -- distance = |β₂|·(3/2)^a ≥ |β₂|
        apply hfloor |β₂| (abs_pos.mpr hβ₂0)
        intro p hp
        rw [hdisteq p hp, hβ₁0, zero_mul, zero_add, abs_mul,
          abs_of_pos (by positivity : (0 : ℚ) < (3 / 2) ^ p.1)]
        have hu : (1 : ℚ) ≤ (3 / 2) ^ p.1 := one_le_pow₀ (by norm_num)
        nlinarith [abs_nonneg β₂]
    · -- β₁ ≠ 0: for gap ≥ s₁ the distance is ≥ |β₁|/2; gaps < s₁ are a finite slice
      obtain ⟨s₁, hs₁⟩ := pow_unbounded_of_one_lt (2 * |β₂| / |β₁|)
        (by norm_num : (1 : ℚ) < 3 / 2)
      have hβ₁pos : 0 < |β₁| := abs_pos.mpr hβ₁0
      have hs₁' : 2 * |β₂| < |β₁| * (3 / 2 : ℚ) ^ s₁ := by
        rw [div_lt_iff₀ hβ₁pos] at hs₁
        linarith
      -- split F by gap
      have hsplit : F ⊆ {p ∈ kernelViolators θ | p.2 ≤ p.1 + s₁} ∪
          {p ∈ kernelViolators θ |
            |β₁| / 2 ≤ ((3 / 2 : ℚ) ^ p.2 - (3 / 2 : ℚ) ^ p.1).distToNearestInt} := by
        intro p hp
        by_cases hg : p.2 ≤ p.1 + s₁
        · exact Or.inl ⟨hFsub hp, hg⟩
        · right
          refine ⟨hFsub hp, ?_⟩
          rw [hdisteq p hp]
          push Not at hg
          set u₂ : ℚ := (3 / 2 : ℚ) ^ p.1 with hu₂def
          have hu₂pos : 0 < u₂ := by positivity
          have hu₁ : (3 / 2 : ℚ) ^ p.2 = (3 / 2 : ℚ) ^ (p.2 - p.1) * u₂ := by
            rw [hu₂def, ← pow_add]
            congr 1
            omega
          have hpow : (3 / 2 : ℚ) ^ s₁ ≤ (3 / 2 : ℚ) ^ (p.2 - p.1) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          have hone : (1 : ℚ) ≤ (3 / 2 : ℚ) ^ (p.2 - p.1) * u₂ := by
            rw [← hu₁]; exact one_le_pow₀ (by norm_num)
          -- |β₂| u₂ ≤ |β₁| u₁ / 2
          have h1 : 2 * |β₂| * u₂ ≤ |β₁| * ((3 / 2 : ℚ) ^ (p.2 - p.1) * u₂) := by
            have := mul_le_mul_of_nonneg_right
              (le_trans hs₁'.le (mul_le_mul_of_nonneg_left hpow (abs_nonneg β₁))) hu₂pos.le
            linarith [this]
          have h2 : |β₁ * (3 / 2 : ℚ) ^ p.2 + β₂ * u₂|
              ≥ |β₁ * (3 / 2 : ℚ) ^ p.2| - |β₂ * u₂| := by
            have := abs_sub_abs_le_abs_sub (β₁ * (3 / 2 : ℚ) ^ p.2) (-(β₂ * u₂))
            rwa [abs_neg, sub_neg_eq_add] at this
          rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℚ) < (3 / 2) ^ p.2),
            abs_of_pos hu₂pos, hu₁] at h2
          rw [hu₁]
          nlinarith [h1, h2, hone, hβ₁pos]
      apply hWinf
      exact Set.Finite.subset ((gapBounded_slice_finite s₁ θ hθ0 hθ1).union
        (finite_of_dist_ge θ hθ0 hθ1 (|β₁| / 2) (by positivity))) hsplit

/-- **The Diophantine kernel (K) holds**: exponential pair repulsion for the orbit
of `(3/2)^n` at every rational scale.  Footprint std3 +
`Subspace.evertseSchlickewei`. -/
@[category research solved, AMS 11, ref "BG06", group "three_halves_m4"]
theorem kernel_holds : Kernel := fun θ hθ0 hθ1 => pairRepulsion_all θ hθ0 hθ1

/-- **M4: the steering word has superlinear subword complexity**, `p_T(k)/k → ∞`:
Lemma R (Stage 0) → the pigeonhole reduction to (K) (Stage 1) → the direct
three-variable Subspace proof of (K) (this file), with the bounded-gap slice of
Stage 2b as the only two-variable input.  Ineffective.  Footprint std3 +
`Subspace.evertseSchlickewei`. -/
@[category research solved, AMS 11, ref "BG06", group "three_halves_m4"]
theorem complexity_superlinear : Superlinear := superlinear_of_kernel kernel_holds

/-- The Stage-2c **middle band is finite** at every scale, gap threshold and band
parameter — the named hypothesis of `TH.superlinear_of_middleBand`, discharged. -/
@[category research solved, AMS 11, ref "BG06", group "three_halves_m4"]
theorem middleBandViolators_finite (θ ε' : ℚ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (S : ℕ) : (middleBandViolators θ ε' S).Finite :=
  Set.Finite.subset (pairRepulsion_all θ hθ0 hθ1) (Set.sep_subset _ _)

end TH
