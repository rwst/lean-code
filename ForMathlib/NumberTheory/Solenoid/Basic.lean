/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import ForMathlib.NumberTheory.PadicMeasurableSpace
public import ForMathlib.NumberTheory.Solenoid.Ambient

@[expose] public section

/-!
# The `S`-adic solenoid `Σ_S` and the automorphisms `σ_u`

For a finite set `S` of primes, the **`S`-adic solenoid** is the compact abelian group

`Σ_S = (ℝ × ∏_{p ∈ S} ℚ_p) / ℤ[1/N_S]`,

with `ℤ[1/N_S]` embedded diagonally.  Every unit `u` of `ℤ[1/N_S]` (`Rat.IsSUnit S u`) acts on it
by the topological group automorphism `σ_u = smulAut hu`, and along the winding line
`wind ξ = [(ξ, 0)]` the orbit of `σ_u` is the sequence `ξ uⁿ`:

`smulAut_iter_wind : (smulAut hu)^[n] (wind ξ) = wind (ξ * uⁿ)`.

For `S = {2, 3}` and `u = 3/2` this is `TH/Solenoid/Sigma6.lean`'s `T32_iter_wind`.

* **Compactness** comes from the fundamental domain of `Ambient.lean`: `Σ_S` is the image of the
  compact box `Dcl S` (`mk_image_Dcl`).  The ambient group is not compact.
* **Hausdorffness, metrizability, second countability** come from instance search, because the
  lattice is closed (`AddSubgroup.isClosed_of_discrete`).
* The **measurable structure** is the quotient σ-algebra `QuotientAddGroup.measurableSpace`, and
  `QuotientAddGroup.borelSpace` identifies it with the Borel σ-algebra (`borelSpace`).  No `borel`
  σ-algebra is declared by hand: that would create a diamond and leave the quotient-Haar machinery
  of `Mathlib/MeasureTheory/Measure/Haar/Quotient.lean` out of reach.

## Main declarations

* `Solenoid S` and its instances `CompactSpace`, `T2Space`, `MetrizableSpace`,
  `SecondCountableTopology`, `BorelSpace`.
* `Solenoid.wind`, `Solenoid.wind_add`, `Solenoid.wind_injective` (for `S` nonempty).
* `Solenoid.smulAut`, `smulAut_mul`, `smulAut_comm`, `smulAut_symm`, `smulAut_wind`,
  `smulAut_iter_wind`.
* `Solenoid.mk_diag_eq_zero_iff`, `smulAut_mk_diag`, `smulAut_mk_diag_eq_self_iff` — the rational
  points `[diag q]`, `q ∈ ℚ`, form the torsion subgroup's natural parametrisation `ℚ/ℤ[1/N_S]`.
* `Solenoid.eq_zero_of_smulAut_eq_self` — if `u - 1` is also an `S`-unit, `σ_u` fixes only `0`.

## Implementation notes

The fixed-point lemma needs `IsSUnit S (u - 1)`, not `u ≠ 1`.  For `u = 3/2` the hypothesis holds
(`u - 1 = 1/2`); for an integer base `b` it can fail, and then `σ_b` has the nonzero fixed point
`[diag (1/(b-1))]` (`smulAut_mk_diag_eq_self_iff`; e.g. `b = 7`, `S = {7}`).  This is a real
difference between `×3/2` and `×b`.  No nonzero point of the winding line is ever fixed, since
`wind` is injective and `σ_u (wind ξ) = wind (u ξ)`.

`wind_injective` needs `S` nonempty: for `S = ∅` the solenoid is `ℝ/ℤ` and `wind` is the
quotient map.

## Status

Everything in this file is standard; the contribution is the formalisation.

## References

* M. Einsiedler and T. Ward, *Ergodic Theory with a view towards Number Theory*, Springer (2011),
  Chapter 8.
* K. Schmidt, *Dynamical Systems of Algebraic Origin*, Birkhäuser (1995).
* D. Lind and T. Ward, *Automorphisms of solenoids and `p`-adic entropy*, Ergodic Theory
  Dynam. Systems 8 (1988), 411–419.
-/

open Metric Set Rat

/-- The **`S`-adic solenoid** `Σ_S = (ℝ × ∏_{p ∈ S} ℚ_p) / ℤ[1/N_S]`. -/
abbrev Solenoid (S : Finset Nat.Primes) : Type := Solenoid.ambient S ⧸ Solenoid.lattice S

namespace Solenoid

variable {S : Finset Nat.Primes}

/-! ### The compact group structure -/

/-- Every point of `Σ_S` is represented in the compact box `Dcl S = [0,1] × ∏_{p ∈ S} ℤ_p`. -/
theorem mk_image_Dcl : (QuotientAddGroup.mk '' Dcl S : Set (Solenoid S)) = univ := by
  refine eq_univ_of_forall fun x ↦ ?_
  obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨d, hd, hmem⟩ := exists_mem_Dcl_sub_mem_lattice g
  refine ⟨d, hd, ?_⟩
  rw [QuotientAddGroup.eq]
  simpa [neg_add_eq_sub] using hmem

/-- **`Σ_S` is compact.**  The ambient group is not; compactness of the quotient is cocompactness
of the lattice, which comes from the fundamental domain. -/
instance instCompactSpace : CompactSpace (Solenoid S) :=
  ⟨by rw [← mk_image_Dcl]; exact (isCompact_Dcl).image QuotientAddGroup.continuous_mk⟩

theorem t2Space : T2Space (Solenoid S) := inferInstance

theorem secondCountableTopology : SecondCountableTopology (Solenoid S) := inferInstance

/-- `Σ_S` is metrizable: `T3` (the lattice is closed) and second countable, so Urysohn applies. -/
theorem metrizableSpace : TopologicalSpace.MetrizableSpace (Solenoid S) := inferInstance

/-- **`Σ_S` is a Borel space for the quotient σ-algebra it already carries**
(`QuotientAddGroup.borelSpace`: a Polish group modulo a closed subgroup). -/
theorem borelSpace : BorelSpace (Solenoid S) := inferInstance

/-! ### The winding line -/

/-- The winding line `ξ ↦ [(ξ, 0)]`, the image of `ℝ` in `Σ_S`. -/
noncomputable def wind (ξ : ℝ) : Solenoid S := QuotientAddGroup.mk (ξ, 0)

@[simp] theorem wind_zero : wind (S := S) 0 = 0 :=
  QuotientAddGroup.mk_zero _

theorem wind_add (ξ η : ℝ) : wind (S := S) (ξ + η) = wind ξ + wind η := by
  simp only [wind, ← QuotientAddGroup.mk_add, Prod.mk_add_mk, add_zero]

theorem continuous_wind : Continuous (wind (S := S)) :=
  QuotientAddGroup.continuous_mk.comp (continuous_id.prodMk continuous_const)

/-- **The winding line is injective** as soon as `S` is nonempty: an element of `Δ_S` whose
`p`-adic coordinate vanishes is `0`.  (For `S = ∅`, `Σ_S = ℝ/ℤ` and `wind` is the quotient map.) -/
theorem wind_injective (hS : S.Nonempty) : Function.Injective (wind (S := S)) := by
  intro ξ η h
  rw [wind, wind, QuotientAddGroup.eq] at h
  obtain ⟨r, hr, hrg⟩ := mem_lattice.mp h
  obtain ⟨p, hp⟩ := hS
  have h1 := congrArg Prod.fst hrg
  have h2 := congrArg (fun g : ambient S ↦ g.2 ⟨p, hp⟩) hrg
  simp only [diag_fst, diag_snd, Prod.fst_add, Prod.fst_neg, Prod.snd_add, Prod.snd_neg,
    Pi.add_apply, Pi.neg_apply, Pi.zero_apply, add_zero] at h1 h2
  have hr0 : r = 0 := by exact_mod_cast h2
  rw [hr0, Rat.cast_zero] at h1
  linarith

/-! ### Multiplication by an `S`-unit -/

/-- Multiplication by a rational on `G_S`, as an additive endomorphism. -/
noncomputable def smulHom (q : ℚ) : ambient S →+ ambient S :=
  AddMonoidHom.mk' (fun g ↦ q • g) (smul_add q)

theorem smulHom_apply (q : ℚ) (g : ambient S) : smulHom q g = q • g := rfl

/-- Multiplication commutes with the diagonal: `q • (r, (r)_p) = (qr, (qr)_p)`. -/
theorem smul_diag (q r : ℚ) : q • diag S r = diag S (q * r) := by
  ext p
  · simp [Rat.smul_def]
  · simp [Rat.smul_def]

/-- Multiplication by an `S`-integer maps the lattice into itself. -/
theorem lattice_le_comap {q : ℚ} (hq : q ∈ sIntegers S) :
    lattice S ≤ (lattice S).comap (smulHom q) := by
  intro g hg
  obtain ⟨r, hr, rfl⟩ := mem_lattice.mp hg
  rw [AddSubgroup.mem_comap, smulHom_apply, smul_diag]
  exact diag_mem_lattice (mul_mem hq hr)

/-- **The automorphism `σ_u` of `Σ_S` induced by an `S`-unit `u`.**  Multiplication by `u`
preserves the lattice in both directions, hence descends to a topological group automorphism. -/
noncomputable def smulAut {u : ℚ} (hu : IsSUnit S u) : Solenoid S ≃ₜ+ Solenoid S where
  toFun := QuotientAddGroup.map _ _ (smulHom u) (lattice_le_comap hu.mem)
  invFun := QuotientAddGroup.map _ _ (smulHom u⁻¹) (lattice_le_comap hu.inv_mem)
  left_inv := by
    rintro ⟨g⟩
    change (QuotientAddGroup.mk (u⁻¹ • u • g) : Solenoid S) = QuotientAddGroup.mk g
    rw [smul_smul, inv_mul_cancel₀ hu.ne_zero, one_smul]
  right_inv := by
    rintro ⟨g⟩
    change (QuotientAddGroup.mk (u • u⁻¹ • g) : Solenoid S) = QuotientAddGroup.mk g
    rw [smul_smul, mul_inv_cancel₀ hu.ne_zero, one_smul]
  map_add' := map_add _
  continuous_toFun := by
    rw [(QuotientAddGroup.isQuotientMap_mk _).continuous_iff]
    exact QuotientAddGroup.continuous_mk.comp (continuous_const_smul u)
  continuous_invFun := by
    rw [(QuotientAddGroup.isQuotientMap_mk _).continuous_iff]
    exact QuotientAddGroup.continuous_mk.comp (continuous_const_smul u⁻¹)

variable {u v : ℚ}

theorem smulAut_mk (hu : IsSUnit S u) (g : ambient S) :
    smulAut hu (QuotientAddGroup.mk g) = QuotientAddGroup.mk (u • g) := rfl

theorem smulAut_symm_mk (hu : IsSUnit S u) (g : ambient S) :
    (smulAut hu).symm (QuotientAddGroup.mk g) = QuotientAddGroup.mk (u⁻¹ • g) := rfl

/-- `σ_u⁻¹ = σ_{u⁻¹}`. -/
theorem smulAut_symm (hu : IsSUnit S u) : (smulAut hu).symm = smulAut hu.inv := by
  ext x
  obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective x
  rfl

/-- `σ_1` is the identity. -/
theorem smulAut_one (x : Solenoid S) : smulAut (IsSUnit.one (S := S)) x = x := by
  obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [smulAut_mk, one_smul]

/-- `σ_{uv} = σ_u ∘ σ_v`: `u ↦ σ_u` is a homomorphism from the `S`-units. -/
theorem smulAut_mul (hu : IsSUnit S u) (hv : IsSUnit S v) :
    smulAut (hu.mul hv) = (smulAut hv).trans (smulAut hu) := by
  ext x
  obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective x
  change (QuotientAddGroup.mk ((u * v) • g) : Solenoid S) = QuotientAddGroup.mk (u • v • g)
  rw [smul_smul]

/-- **Any two `σ_u`, `σ_v` commute**: the `S`-units act on `Σ_S` through an abelian group (for
`S = {2, 3}` this is Furstenberg's `ℤ²`-action `×2, ×3`). -/
theorem smulAut_comm (hu : IsSUnit S u) (hv : IsSUnit S v) (x : Solenoid S) :
    smulAut hu (smulAut hv x) = smulAut hv (smulAut hu x) := by
  obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective x
  simp only [smulAut_mk, smul_smul, mul_comm]

/-- `σ_u (wind ξ) = wind (u ξ)`. -/
theorem smulAut_wind (hu : IsSUnit S u) (ξ : ℝ) : smulAut hu (wind ξ) = wind (u * ξ) := by
  rw [wind, smulAut_mk, wind]
  congr 1
  ext <;> simp [Rat.smul_def]

/-- **The orbit of the winding line under `σ_u` is `ξ uⁿ`.**  For `S = {2, 3}`, `u = 3/2` this is
the identity which makes `Σ_S` the home of the sequence `(3/2)ⁿ ξ`. -/
theorem smulAut_iter_wind (hu : IsSUnit S u) (ξ : ℝ) (n : ℕ) :
    (smulAut hu)^[n] (wind ξ) = wind (ξ * (u : ℝ) ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, smulAut_wind]
    ring_nf

/-- **Fixed points.**  If `u - 1` is also an `S`-unit (as for `u = 3/2`, `u - 1 = 1/2`), the only
fixed point of `σ_u` is `0`: `σ_u x = x` says `(u - 1) x = 0`, and multiplication by `u - 1` is
an automorphism.  For an integer `u = b` the hypothesis can fail, and then `σ_b` fixes the
nonzero point `[diag (1/(b-1))]` (`smulAut_mk_diag_eq_self_iff`). -/
theorem eq_zero_of_smulAut_eq_self (hu : IsSUnit S u) (hu1 : IsSUnit S (u - 1))
    {x : Solenoid S} (h : smulAut hu x = x) : x = 0 := by
  obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [smulAut_mk, QuotientAddGroup.eq] at h
  obtain ⟨r, hr, hrg⟩ := mem_lattice.mp h
  have hu1' : IsSUnit S (1 - u) := by simpa using hu1.neg
  have hg : g = diag S ((1 - u)⁻¹ * r) := by
    rw [← smul_diag, hrg, neg_add_eq_sub, show g - u • g = (1 - u) • g by
      rw [sub_smul, one_smul], smul_smul, inv_mul_cancel₀ hu1'.ne_zero, one_smul]
  rw [QuotientAddGroup.eq_zero_iff, hg]
  exact diag_mem_lattice (mul_mem hu1'.inv_mem hr)

/-! ### Rational points -/

theorem diag_injective : Function.Injective (diag S) := fun q r h ↦ by
  have h1 := congrArg Prod.fst h
  rw [diag_fst, diag_fst] at h1
  exact_mod_cast h1

/-- `[diag q] = 0` in `Σ_S` exactly when `q` is an `S`-integer. -/
theorem mk_diag_eq_zero_iff {q : ℚ} :
    (QuotientAddGroup.mk (diag S q) : Solenoid S) = 0 ↔ q ∈ sIntegers S := by
  rw [QuotientAddGroup.eq_zero_iff, mem_lattice]
  exact ⟨fun ⟨r, hr, h⟩ ↦ diag_injective h ▸ hr, fun h ↦ ⟨q, h, rfl⟩⟩

theorem smulAut_mk_diag (hu : IsSUnit S u) (q : ℚ) :
    smulAut hu (QuotientAddGroup.mk (diag S q)) = QuotientAddGroup.mk (diag S (u * q)) := by
  rw [smulAut_mk, smul_diag]

/-- `[diag q]` is fixed by `σ_u` exactly when `(u - 1) q` is an `S`-integer. -/
theorem smulAut_mk_diag_eq_self_iff (hu : IsSUnit S u) (q : ℚ) :
    smulAut hu (QuotientAddGroup.mk (diag S q)) = QuotientAddGroup.mk (diag S q) ↔
      (u - 1) * q ∈ sIntegers S := by
  rw [smulAut_mk_diag, ← sub_eq_zero, ← QuotientAddGroup.mk_sub, ← map_sub,
    mk_diag_eq_zero_iff, sub_mul, one_mul]

end Solenoid

/-! ### Examples -/

section Examples

open Solenoid

private theorem isSUnit_threeHalves : IsSUnit (Nat.primesOf 6) (3 / 2) :=
  (isSUnit_natCast (by norm_num) (Nat.primesOf_mono (by norm_num) (by norm_num))).div
    (isSUnit_natCast (by norm_num) (Nat.primesOf_mono (by norm_num) (by norm_num)))

/-- On `Σ₆`, `×3/2` moves the winding line along `(3/2)ⁿ ξ` ... -/
example (ξ : ℝ) (n : ℕ) :
    (smulAut isSUnit_threeHalves)^[n] (wind ξ) = wind (ξ * (3 / 2) ^ n) := by
  rw [smulAut_iter_wind]
  norm_num

/-- ... and fixes only `0`, because `3/2 - 1 = 1/2` is again a `{2,3}`-unit. -/
example (x : Solenoid (Nat.primesOf 6)) (h : smulAut isSUnit_threeHalves x = x) : x = 0 :=
  eq_zero_of_smulAut_eq_self isSUnit_threeHalves
    (by
      have h2 : IsSUnit (Nat.primesOf 6) (2 : ℕ) :=
        isSUnit_natCast (by norm_num) (Nat.primesOf_mono (by norm_num) (by norm_num))
      convert h2.inv using 1
      norm_num) h

/-- For an integer base the hypothesis `IsSUnit S (u - 1)` cannot be dropped: on `Σ_{7}`, `×7`
fixes the nonzero point `[diag (1/6)]`. -/
example : ∃ hu : IsSUnit (Nat.primesOf 7) 7,
    smulAut hu (QuotientAddGroup.mk (diag _ (1 / 6))) = QuotientAddGroup.mk (diag _ (1 / 6)) ∧
      (QuotientAddGroup.mk (diag (Nat.primesOf 7) (1 / 6)) : Solenoid _) ≠ 0 := by
  have hu : IsSUnit (Nat.primesOf 7) ((7 : ℕ) : ℚ) := isSUnit_natCast (by norm_num) le_rfl
  push_cast at hu
  refine ⟨hu, (smulAut_mk_diag_eq_self_iff hu _).mpr (by norm_num), ?_⟩
  rw [Ne, mk_diag_eq_zero_iff]
  intro h
  have h2 : (⟨2, Nat.prime_two⟩ : Nat.Primes) ∉ Nat.primesOf 7 := fun hm ↦ by
    have := (Nat.mem_primesOf_iff_dvd (n := 7) (by norm_num)).mp hm
    norm_num at this
  have := padicNorm_le_one_of_mem_sIntegers h h2
  change padicNorm 2 (1 / 6 : ℚ) ≤ 1 at this
  have hval : padicNorm 2 (1 / 6 : ℚ) = 2 := by
    rw [padicNorm.div, padicNorm.one, show (6 : ℚ) = (2 : ℕ) * (3 : ℕ) by norm_num,
      padicNorm.mul, padicNorm.padicNorm_p_of_prime, (padicNorm.nat_eq_one_iff 3).mpr (by decide)]
    norm_num
  rw [hval] at this
  norm_num at this

end Examples
