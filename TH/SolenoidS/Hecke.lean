/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Group
import ForMathlib.NumberTheory.Solenoid.Basic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# `×u` as a Hecke translate: the `GL₂` identity behind the solenoid

Deliverable D7 of plan-udmf-O5 (milestone M6, §1.6): Proposition 1(a) and the algebraic half of
Proposition 1(b) of plan-udmf-F2ii §1.3, for every finite set of primes `S` and every `S`-unit
`u`.

Let `𝒢_S = GL₂(ℝ) × ∏_{p ∈ S} GL₂(ℚ_p)` (`GLS S`), `ι : GL₂(ℚ) → 𝒢_S` the diagonal embedding
(`ιGL`), `Γ_S = ι(GL₂(ℤ[1/N_S]))` (`ΓS S`), and `Γ_S \ 𝒢_S` the space of right cosets
(`CosetSpace S`, the quotient by `QuotientGroup.rightRel`; it carries no group structure, so all
equivariance statements are equalities of classes).  Write `u(g)` for the upper unipotent matrix
with entry `g_v` at each place (`uS g`), `u_∞(ξ) = u(ξ, 0)` (`uInf ξ`), and
`h_u = ι(diag(u⁻¹, 1))` (`hecke hu`).

* **Proposition 1(a)** (`hecke_translate`): `Γ_S u_∞(ξ) h_u = Γ_S u_∞(u ξ)`.  So right
  translation by the Hecke element `h_u ∈ Γ_S` moves the point `ξ` of the horocycle to `u ξ`; for
  `S = {2, 3}`, `u = 3/2` this is the `(3/2)ⁿ` dynamics.
* **Proposition 1(b), algebraic half**: the orbit map `Σ_S → Γ_S \ 𝒢_S`, `[g] ↦ Γ_S u(g)`
  (`orbitMap`) is well defined (`u(diag r) = ι(u(r)) ∈ Γ_S` for `r ∈ ℤ[1/N_S]`), **injective**
  (`orbitMap_injective`: the `(0,1)` entry of `γ` with `ι(γ) = u(g)` is an `S`-integer `r` with
  `g = diag r` at every place), and **equivariant** (`orbitMap_smulAut`:
  `orbit(σ_u z) = orbit(z) · h_u`).  All three rest on one conjugation identity,
  `diag(a, 1) u(x) diag(a, 1)⁻¹ = u(a x)` (`dg_mul_unip_mul_inv`).

The topological half of 1(b) — that `orbitMap` is a homeomorphism onto a closed orbit, i.e. that
`Γ_S` is a lattice in `𝒢_S` — is angle O9 of the plan and is not attempted (decision 3A).

## Status

Everything in this file is standard; the contribution is the formalisation.

## References

* plan-udmf-O5 §1.6 (D7), plan-udmf-F2ii §1.3 (Proposition 1).
* [EL10] M. Einsiedler, E. Lindenstrauss, *Diagonal actions on locally homogeneous spaces*, in
  Homogeneous flows, moduli spaces and arithmetic, Clay Math. Proc. 10 (2010), 155–241.
* [Lin01] E. Lindenstrauss, *`p`-adic foliation and equidistribution*, Israel J. Math. 122
  (2001), 29–42.
-/

namespace TH.SolS

open Matrix Solenoid Rat

/-! ### Unipotent and diagonal elements of `GL₂` over a commutative ring -/

section Generic

variable {R T : Type*} [CommRing R] [CommRing T]

/-- The upper unipotent matrix `!![1, x; 0, 1]` as an element of `GL₂(R)`. -/
def unip (x : R) : GL (Fin 2) R :=
  ⟨!![1, x; 0, 1], !![1, -x; 0, 1], by ext i j; fin_cases i <;> fin_cases j <;> simp,
    by ext i j; fin_cases i <;> fin_cases j <;> simp⟩

/-- The diagonal matrix `diag(a, 1)` for a unit `a`, as an element of `GL₂(R)`. -/
def dg (a : Rˣ) : GL (Fin 2) R :=
  ⟨!![(a : R), 0; 0, 1], !![((a⁻¹ : Rˣ) : R), 0; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp,
    by ext i j; fin_cases i <;> fin_cases j <;> simp⟩

@[category API, AMS 11 22, ref "udmfO5", group "th_solenoid_s_hecke"]
theorem unip_add (x y : R) : unip (x + y) = unip x * unip y := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [unip, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

@[category API, AMS 11 22, ref "udmfO5", group "th_solenoid_s_hecke"]
theorem unip_zero : unip (0 : R) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [unip]

@[category API, AMS 11 22, ref "udmfO5", group "th_solenoid_s_hecke"]
theorem unip_neg (x : R) : unip (-x) = (unip x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← unip_add, neg_add_cancel, unip_zero])

@[category API, AMS 11 22, ref "udmfO5", group "th_solenoid_s_hecke"]
theorem dg_mul (a b : Rˣ) : dg (a * b) = dg a * dg b := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [dg, Matrix.mul_apply, Fin.sum_univ_two]

@[category API, AMS 11 22, ref "udmfO5", group "th_solenoid_s_hecke"]
theorem dg_one : dg (1 : Rˣ) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [dg]

@[category API, AMS 11 22, ref "udmfO5", group "th_solenoid_s_hecke"]
theorem dg_inv (a : Rˣ) : dg a⁻¹ = (dg a)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← dg_mul, inv_mul_cancel, dg_one])

/-- **The conjugation identity** `diag(a, 1) u(x) diag(a, 1)⁻¹ = u(a x)`: the whole content of
"`×a` is a Hecke translate", at one place. -/
@[category API, AMS 11 22, ref "udmfO5", group "th_solenoid_s_hecke"]
theorem dg_mul_unip_mul_inv (a : Rˣ) (x : R) : dg a * unip x * (dg a)⁻¹ = unip (a * x) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [dg, unip, Matrix.mul_apply, Fin.sum_univ_two]

@[category API, AMS 11 22, ref "udmfO5", group "th_solenoid_s_hecke"]
theorem map_unip (f : R →+* T) (x : R) :
    GeneralLinearGroup.map f (unip x) = unip (f x) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [unip]

@[category API, AMS 11 22, ref "udmfO5", group "th_solenoid_s_hecke"]
theorem map_dg (f : R →+* T) (a : Rˣ) :
    GeneralLinearGroup.map f (dg a) = dg (Units.map (f : R →* T) a) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [dg]

@[category API, AMS 11 22, ref "udmfO5", group "th_solenoid_s_hecke"]
theorem unip_apply_zero_one (x : R) : unip x 0 1 = x := rfl

end Generic

/-! ### The `S`-adic group, the diagonal embedding and `Γ_S` -/

variable (S : Finset Nat.Primes)

/-- `𝒢_S = GL₂(ℝ) × ∏_{p ∈ S} GL₂(ℚ_p)`. -/
abbrev GLS : Type := GL (Fin 2) ℝ × ((p : S) → GL (Fin 2) ℚ_[((p : Nat.Primes) : ℕ)])

/-- The diagonal embedding `ι : GL₂(ℚ) → 𝒢_S`. -/
noncomputable def ιGL : GL (Fin 2) ℚ →* GLS S :=
  (GeneralLinearGroup.map (Rat.castHom ℝ)).prod
    (MonoidHom.pi fun p : S ↦ GeneralLinearGroup.map (Rat.castHom ℚ_[((p : Nat.Primes) : ℕ)]))

/-- `Γ_S = ι(GL₂(ℤ[1/N_S]))`. -/
noncomputable def ΓS : Subgroup (GLS S) :=
  ((ιGL S).comp (GeneralLinearGroup.map (sIntegers S).subtype)).range

/-- The space of right cosets `Γ_S \ 𝒢_S`. -/
abbrev CosetSpace : Type := Quotient (QuotientGroup.rightRel (ΓS S))

variable {S}

/-- The unipotent element `u(g) ∈ 𝒢_S` with entry `g_v` at each place `v`. -/
noncomputable def uS (g : ambient S) : GLS S := (unip g.1, fun p ↦ unip (g.2 p))

/-- The real-place unipotent `u_∞(ξ) = (!![1, ξ; 0, 1], 1, …, 1)`. -/
noncomputable def uInf (ξ : ℝ) : GLS S := uS ((ξ, 0) : ambient S)

@[category API, AMS 11 22, ref "udmfO5", group "th_solenoid_s_hecke"]
theorem uInf_eq (ξ : ℝ) : (uInf ξ : GLS S) = (unip ξ, 1) := by
  simp only [uInf, uS, Pi.zero_apply, unip_zero]
  rfl

@[category API, AMS 11 22, ref "udmfO5", group "th_solenoid_s_hecke"]
theorem uS_add (g g' : ambient S) : uS (g + g') = uS g * uS g' := by
  simp only [uS, Prod.fst_add, Prod.snd_add, Pi.add_apply, unip_add]
  rfl

@[category API, AMS 11 22, ref "udmfO5", group "th_solenoid_s_hecke"]
theorem uS_neg (g : ambient S) : uS (-g) = (uS g)⁻¹ := by
  simp only [uS, Prod.fst_neg, Prod.snd_neg, Pi.neg_apply, unip_neg]
  rfl

@[category API, AMS 11 22, ref "udmfO5", group "th_solenoid_s_hecke"]
theorem ιGL_fst (γ : GL (Fin 2) ℚ) :
    (ιGL S γ).1 = GeneralLinearGroup.map (Rat.castHom ℝ) γ := rfl

@[category API, AMS 11 22, ref "udmfO5", group "th_solenoid_s_hecke"]
theorem ιGL_snd (γ : GL (Fin 2) ℚ) (p : S) :
    (ιGL S γ).2 p = GeneralLinearGroup.map (Rat.castHom ℚ_[((p : Nat.Primes) : ℕ)]) γ := rfl

/-- `ι(u(r)) = u(diag r)`. -/
@[category API, AMS 11 22, ref "udmfO5", group "th_solenoid_s_hecke"]
theorem ιGL_unip (r : ℚ) : ιGL S (unip r) = uS (diag S r) :=
  Prod.ext (by rw [ιGL_fst, map_unip]; rfl) (funext fun p ↦ by rw [ιGL_snd, map_unip]; rfl)

/-- The conjugation identity at every place at once:
`ι(diag(a, 1)) u(g) ι(diag(a, 1))⁻¹ = u(a g)`. -/
@[category API, AMS 11 22, ref "udmfO5", group "th_solenoid_s_hecke"]
theorem ιGL_dg_conj (a : ℚˣ) (g : ambient S) :
    ιGL S (dg a) * uS g * (ιGL S (dg a))⁻¹ = uS ((a : ℚ) • g) := by
  refine Prod.ext ?_ (funext fun p ↦ ?_)
  · simp only [Prod.fst_mul, Prod.fst_inv, ιGL_fst, map_dg, uS, dg_mul_unip_mul_inv]
    simp [Rat.smul_def]
  · simp only [Prod.snd_mul, Prod.snd_inv, Pi.mul_apply, Pi.inv_apply, ιGL_snd, map_dg, uS,
      dg_mul_unip_mul_inv]
    simp [Rat.smul_def]

/-- `u(diag r) ∈ Γ_S` for `r ∈ ℤ[1/N_S]`. -/
@[category API, AMS 11 22, ref "udmfO5", group "th_solenoid_s_hecke"]
theorem uS_diag_mem {r : ℚ} (hr : r ∈ sIntegers S) : uS (diag S r) ∈ ΓS S :=
  ⟨unip ⟨r, hr⟩, by simp only [MonoidHom.comp_apply, map_unip]; exact ιGL_unip r⟩

/-- `u(g) ∈ Γ_S` for `g` in the lattice. -/
@[category API, AMS 11 22, ref "udmfO5", group "th_solenoid_s_hecke"]
theorem uS_mem_of_mem_lattice {g : ambient S} (hg : g ∈ lattice S) : uS g ∈ ΓS S := by
  obtain ⟨r, hr, rfl⟩ := mem_lattice.mp hg
  exact uS_diag_mem hr

variable {u : ℚ}

/-- `u` as a unit of `ℚ`. -/
noncomputable def unitOf (hu : IsSUnit S u) : ℚˣ := Units.mk0 u hu.ne_zero

/-- `ι(diag(u, 1)) ∈ Γ_S` for an `S`-unit `u`. -/
@[category API, AMS 11 22, ref "udmfO5", group "th_solenoid_s_hecke"]
theorem ιGL_dg_mem (hu : IsSUnit S u) : ιGL S (dg (unitOf hu)) ∈ ΓS S := by
  let a : (sIntegers S)ˣ := ⟨⟨u, hu.mem⟩, ⟨u⁻¹, hu.inv_mem⟩,
    Subtype.ext (mul_inv_cancel₀ hu.ne_zero), Subtype.ext (inv_mul_cancel₀ hu.ne_zero)⟩
  refine ⟨dg a, ?_⟩
  simp only [MonoidHom.comp_apply, map_dg]
  congr 2

/-- **The Hecke element** `h_u = ι(diag(u⁻¹, 1))`. -/
noncomputable def hecke (hu : IsSUnit S u) : GLS S := (ιGL S (dg (unitOf hu)))⁻¹

@[category API, AMS 11 22, ref "udmfO5", group "th_solenoid_s_hecke"]
theorem hecke_eq (hu : IsSUnit S u) : hecke hu = ιGL S (dg (unitOf hu)⁻¹) := by
  rw [hecke, dg_inv, map_inv]

/-- `h_u ∈ Γ_S`. -/
@[category API, AMS 11 22, ref "udmfO5", group "th_solenoid_s_hecke"]
theorem hecke_mem (hu : IsSUnit S u) : hecke hu ∈ ΓS S :=
  Subgroup.inv_mem _ (ιGL_dg_mem hu)

/-! ### The orbit map -/

variable (S) in
/-- **The orbit map** `Σ_S → Γ_S \ 𝒢_S`, `[g] ↦ Γ_S u(g)`. -/
noncomputable def orbitMap : Solenoid S → CosetSpace S :=
  Quotient.map' uS fun a b h ↦ by
    rw [QuotientGroup.rightRel_apply, ← uS_neg, ← uS_add]
    have hab := QuotientAddGroup.leftRel_apply.mp h
    rw [add_comm] at hab
    exact uS_mem_of_mem_lattice hab

@[category API, AMS 11 22, ref "udmfO5", group "th_solenoid_s_hecke"]
theorem orbitMap_mk (g : ambient S) :
    orbitMap S (QuotientAddGroup.mk g) = (⟦uS g⟧ : CosetSpace S) := rfl

@[category API, AMS 11 22, ref "udmfO5", group "th_solenoid_s_hecke"]
theorem orbitMap_wind (ξ : ℝ) : orbitMap S (wind ξ) = (⟦uInf ξ⟧ : CosetSpace S) := rfl

/-- **The orbit map is injective** (Proposition 1(b), algebraic half): if `u(g) ∈ Γ_S`, the
`(0,1)` entry `r` of a preimage in `GL₂(ℤ[1/N_S])` is an `S`-integer with `g = diag r`. -/
@[category research solved, AMS 11 22, ref "udmfO5" "EL10", group "th_solenoid_s_hecke"]
theorem orbitMap_injective : Function.Injective (orbitMap S) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective y
  have h := QuotientGroup.rightRel_apply.mp (Quotient.exact hxy)
  rw [← uS_neg, ← uS_add] at h
  obtain ⟨γ, hγ⟩ := h
  set r : ℚ := ((γ 0 1 : sIntegers S) : ℚ)
  have h1 := congrArg (fun z : GLS S ↦ z.1 0 1) hγ
  have h2 := fun p : S ↦ congrArg (fun z : GLS S ↦ z.2 p 0 1) hγ
  simp only [MonoidHom.comp_apply, ιGL, MonoidHom.prod_apply, MonoidHom.pi_apply,
    GeneralLinearGroup.map_apply, uS, unip_apply_zero_one] at h1 h2
  refine QuotientAddGroup.eq.mpr (mem_lattice.mpr ⟨r, (γ 0 1).2, ?_⟩)
  rw [add_comm]
  refine Prod.ext ?_ (funext fun p ↦ ?_)
  · rw [diag_fst]; exact h1
  · rw [diag_snd]; exact h2 p

/-- **Equivariance**: `orbit(σ_u z) = orbit(z) · h_u`.  Proof: `u(u g) (u(g) h_u)⁻¹ = ι(diag(u, 1))`
by the conjugation identity, and that lies in `Γ_S`. -/
@[category research solved, AMS 11 22, ref "udmfO5" "EL10", group "th_solenoid_s_hecke"]
theorem orbitMap_smulAut (hu : IsSUnit S u) (g : ambient S) :
    orbitMap S (smulAut hu (QuotientAddGroup.mk g)) = (⟦uS g * hecke hu⟧ : CosetSpace S) := by
  rw [smulAut_mk, orbitMap_mk]
  refine Quotient.sound (QuotientGroup.rightRel_apply.mpr ?_)
  have hconj := ιGL_dg_conj (S := S) (unitOf hu) g
  rw [show ((unitOf hu : ℚˣ) : ℚ) = u from rfl] at hconj
  rw [← hconj, hecke]
  have : uS g * (ιGL S (dg (unitOf hu)))⁻¹ *
      (ιGL S (dg (unitOf hu)) * uS g * (ιGL S (dg (unitOf hu)))⁻¹)⁻¹ =
      (ιGL S (dg (unitOf hu)))⁻¹ := by group
  rw [this]
  exact hecke_mem hu

/-- **Proposition 1(a): `×u` is a Hecke translate.**  `Γ_S u_∞(ξ) h_u = Γ_S u_∞(u ξ)`. -/
@[category research solved, AMS 11 22, ref "udmfO5" "EL10", group "th_solenoid_s_hecke"]
theorem hecke_translate (hu : IsSUnit S u) (ξ : ℝ) :
    (⟦uInf ξ * hecke hu⟧ : CosetSpace S) = ⟦uInf ((u : ℝ) * ξ)⟧ := by
  rw [← orbitMap_wind, ← smulAut_wind hu, uInf]
  exact (orbitMap_smulAut hu _).symm

/-- The iterated form: `Γ_S u_∞(ξ) h_uⁿ = Γ_S u_∞(ξ uⁿ)` — the `σ_u`-orbit of `wind ξ`, read in
`Γ_S \ 𝒢_S`. -/
@[category research solved, AMS 11 22, ref "udmfO5", group "th_solenoid_s_hecke"]
theorem orbitMap_smulAut_iter_wind (hu : IsSUnit S u) (ξ : ℝ) (n : ℕ) :
    orbitMap S ((smulAut hu)^[n] (wind ξ)) = (⟦uInf (ξ * (u : ℝ) ^ n)⟧ : CosetSpace S) := by
  rw [smulAut_iter_wind, orbitMap_wind]

/-! ### Test: the `(3/2)ⁿ` dynamics on `Σ_{2,3}` -/

/-- On `S = {2, 3}`, right translation by `h_{3/2} = ι(diag(2/3, 1))` moves `ξ` to `3ξ/2`. -/
@[category test, AMS 11 22, ref "udmfO5", group "th_solenoid_s_hecke"]
theorem hecke_translate_threeHalves (hu : IsSUnit (Nat.primesOf 6) (3 / 2)) (ξ : ℝ) :
    (⟦uInf ξ * hecke hu⟧ : CosetSpace (Nat.primesOf 6)) = ⟦uInf (3 / 2 * ξ)⟧ := by
  rw [hecke_translate]
  norm_num

end TH.SolS
