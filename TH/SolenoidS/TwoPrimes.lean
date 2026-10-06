/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TH.SolenoidS.IntegerBase

/-!
# Two primes: `Σ_{p,q}`, `σ_p`, `σ_q`, `T_{q/p}` and `σ_{pq}`

Deliverable D8 of plan-udmf-O5 (milestone M7): the specialisation of the general solenoid to
`S = {p, q}` for two distinct primes, restating the `b = 6` objects of `TH/Solenoid` for every
pair.  On `Σ_{p,q} = (ℝ × ℚ_p × ℚ_q) / ℤ[1/pq]`:

* `σp`, `σq` — multiplication by `p` and by `q`; they commute (`σp_comm_σq`);
* `T` — multiplication by `q/p`, and `T = σ_p⁻¹ ; σ_q` (`T_eq`); its orbit of `wind ξ` is
  `ξ (q/p)ⁿ` (`T_iter_wind`);
* `σpq` — multiplication by `pq`, `σ_{pq} = σ_p ; σ_q` (`σpq_eq`); orbit `ξ (pq)ⁿ`;
* `sModulus_pair` — `N_{p,q} = pq`, and `primesOf_mul` — `Nat.primesOf (p q) = {p, q}`, which
  connects `σpq` to the integer-base collapse: `σpq_equidistributed_iff_ud`.

For `p = 2`, `q = 3`: `σ2`, `σ3`, `T32`, the `×6` map `σ6 = σ2.trans σ3` of plan-udmf-F2ii §6 (row
T6, superseded by this file), and the dictionary for `(3/2)ⁿ` (`weyl_dictionary_threeHalves`).
The isomorphism `TH.S6.S6 ≃ₜ+ Solenoid {2, 3}` (optional milestone M7b) is not built: nothing
downstream needs it.

## Status

Everything in this file is standard; the contribution is the formalisation.

## References

* plan-udmf-O5 §1 (D8) and §5 (M7); plan-udmf-F2ii §1.3 (Proposition 1(b)) and §6 (row T6).
* [EW11] M. Einsiedler, T. Ward, *Ergodic Theory with a view towards Number Theory*, Springer
  (2011), Ch. 8 (the solenoid, Furstenberg's `×2, ×3`).
* [Fur67] H. Furstenberg, *Disjointness in ergodic theory, minimal sets, and a problem in
  Diophantine approximation*, Math. Systems Theory 1 (1967), 1–49.
* [EL03] M. Einsiedler, E. Lindenstrauss, *Rigidity properties of `ℤ^d`-actions on tori and
  solenoids*, Electron. Res. Announc. AMS 9 (2003), 99–110.
-/

namespace TH.SolS

open Solenoid Rat

/-- `σ_u` depends only on the value of `u`. -/
@[category API, AMS 11 37, ref "udmfO5", group "th_solenoid_s_two_primes"]
theorem smulAut_congr {S : Finset Nat.Primes} {u v : ℚ} (hu : IsSUnit S u) (hv : IsSUnit S v)
    (h : u = v) : smulAut hu = smulAut hv := by
  subst h; rfl

variable {p q : Nat.Primes}

/-! ### The modulus and the primes of `pq` -/

/-- `N_{p,q} = pq`. -/
@[category API, AMS 11, ref "udmfO5", group "th_solenoid_s_two_primes"]
theorem sModulus_pair (hpq : p ≠ q) : sModulus {p, q} = (p : ℕ) * q := by
  rw [sModulus, Finset.prod_pair hpq]

/-- The primes dividing `p q` are `p` and `q`. -/
@[category API, AMS 11, ref "udmfO5", group "th_solenoid_s_two_primes"]
theorem primesOf_mul : Nat.primesOf ((p : ℕ) * q) = {p, q} := by
  ext ℓ
  rw [Nat.mem_primesOf_iff_dvd (Nat.mul_ne_zero p.2.ne_zero q.2.ne_zero), Finset.mem_insert,
    Finset.mem_singleton, Nat.Prime.dvd_mul ℓ.2, Nat.prime_dvd_prime_iff_eq ℓ.2 p.2,
    Nat.prime_dvd_prime_iff_eq ℓ.2 q.2]
  exact or_congr (Subtype.ext_iff (a1 := ℓ) (a2 := p)).symm (Subtype.ext_iff (a1 := ℓ) (a2 := q)).symm

/-! ### The four automorphisms -/

@[category API, AMS 11, ref "udmfO5", group "th_solenoid_s_two_primes"]
theorem isSUnit_left : IsSUnit {p, q} ((p : ℕ) : ℚ) :=
  isSUnit_prime (Finset.mem_insert_self _ _)

@[category API, AMS 11, ref "udmfO5", group "th_solenoid_s_two_primes"]
theorem isSUnit_right : IsSUnit {p, q} ((q : ℕ) : ℚ) :=
  isSUnit_prime (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

@[category API, AMS 11, ref "udmfO5", group "th_solenoid_s_two_primes"]
theorem isSUnit_mul : IsSUnit {p, q} (((p : ℕ) * q : ℕ) : ℚ) :=
  isSUnit_natCast (Nat.mul_pos p.2.pos q.2.pos) primesOf_mul.le

variable (p q)

/-- `σ_p`: multiplication by `p` on `Σ_{p,q}`. -/
noncomputable abbrev σp : Solenoid {p, q} ≃ₜ+ Solenoid {p, q} := smulAut isSUnit_left

/-- `σ_q`: multiplication by `q` on `Σ_{p,q}`. -/
noncomputable abbrev σq : Solenoid {p, q} ≃ₜ+ Solenoid {p, q} := smulAut isSUnit_right

/-- `T = σ_{q/p}`: multiplication by `q/p`, the `(q/p)ⁿ` dynamics. -/
noncomputable abbrev T : Solenoid {p, q} ≃ₜ+ Solenoid {p, q} :=
  smulAut (isSUnit_right.div isSUnit_left)

/-- `σ_{pq}`: multiplication by `pq`, the natural extension of `×pq` on the circle. -/
noncomputable abbrev σpq : Solenoid {p, q} ≃ₜ+ Solenoid {p, q} := smulAut isSUnit_mul

variable {p q}

/-- **Furstenberg's commuting pair**: `σ_p σ_q = σ_q σ_p`. -/
@[category API, AMS 11 37, ref "udmfO5" "EW11", group "th_solenoid_s_two_primes"]
theorem σp_comm_σq (x : Solenoid {p, q}) : σp p q (σq p q x) = σq p q (σp p q x) :=
  smulAut_comm _ _ x

/-- `T = σ_p⁻¹ ; σ_q`, i.e. `T = σ_q ∘ σ_p⁻¹`. -/
@[category API, AMS 11 37, ref "udmfO5", group "th_solenoid_s_two_primes"]
theorem T_eq : T p q = (σp p q).symm.trans (σq p q) := by
  rw [σp, smulAut_symm, ← smulAut_mul]
  exact smulAut_congr _ _ (div_eq_mul_inv _ _)

/-- `σ_{pq} = σ_p ; σ_q`. -/
@[category API, AMS 11 37, ref "udmfO5", group "th_solenoid_s_two_primes"]
theorem σpq_eq : σpq p q = (σp p q).trans (σq p q) := by
  rw [σpq, σp, σq, ← smulAut_mul]
  exact smulAut_congr _ _ (by push_cast; ring)

/-- The `T`-orbit of the winding point is `ξ (q/p)ⁿ`. -/
@[category API, AMS 11 37, ref "udmfO5", group "th_solenoid_s_two_primes"]
theorem T_iter_wind (ξ : ℝ) (n : ℕ) :
    (T p q)^[n] (wind ξ) = wind (ξ * ((q : ℕ) / (p : ℕ) : ℝ) ^ n) := by
  rw [smulAut_iter_wind]
  push_cast
  rfl

/-- The `σ_{pq}`-orbit of the winding point is `ξ (pq)ⁿ`. -/
@[category API, AMS 11 37, ref "udmfO5", group "th_solenoid_s_two_primes"]
theorem σpq_iter_wind (ξ : ℝ) (n : ℕ) :
    (σpq p q)^[n] (wind ξ) = wind (ξ * ((p : ℕ) * (q : ℕ) : ℝ) ^ n) := by
  rw [smulAut_iter_wind]
  push_cast
  rfl

/-- **`σ_{pq}` is the natural extension of `×pq`**: `proj ∘ σ_{pq} = pq · proj`. -/
@[category research solved, AMS 11 37, ref "udmfO5", group "th_solenoid_s_two_primes"]
theorem proj_σpq (x : Solenoid {p, q}) :
    proj _ (σpq p q x) = ((p : ℕ) * (q : ℕ)) • proj _ x :=
  proj_smulAut_natCast _ x

/-! ### The dictionary on `Σ_{p,q}` -/

/-- **The dictionary for `(q/p)ⁿ`.** -/
@[category research solved, AMS 11 37, ref "udmfO5", group "th_solenoid_s_two_primes"]
theorem weyl_dictionary_T (ξ : ℝ) :
    [Equidistributed (isSUnit_right.div isSUnit_left : IsSUnit {p, q} _) ξ,
      WeylFamily {p, q} ((q : ℕ) / (p : ℕ) : ℚ) ξ,
      UDFamily {p, q} ((q : ℕ) / (p : ℕ) : ℚ) ξ].TFAE :=
  weyl_dictionary _ ξ

/-- **The integer-base collapse on `Σ_{p,q}`**: equidistribution of the `σ_{pq}`-orbit of
`wind ξ` is u.d. mod 1 of `(ξ (pq)ⁿ)` — the irrelevance wall for `×pq`, not progress on any `ξ`. -/
@[category research solved, AMS 11 37, ref "udmfO5", group "th_solenoid_s_two_primes"]
theorem σpq_equidistributed_iff_ud (ξ : ℝ) :
    Equidistributed (isSUnit_mul : IsSUnit {p, q} _) ξ ↔
      Bertin.UniformlyDistributedModOne (fun n => ξ * ((p : ℕ) * (q : ℕ) : ℝ) ^ n) := by
  have key : ∀ (S : Finset Nat.Primes) (_ : S = Nat.primesOf ((p : ℕ) * q))
      (hu : IsSUnit S (((p : ℕ) * q : ℕ) : ℚ)), Equidistributed hu ξ ↔
        Bertin.UniformlyDistributedModOne (fun n => ξ * (((p : ℕ) * q : ℕ) : ℝ) ^ n) := by
    rintro S rfl hu
    exact equidistributed_iff_ud (Nat.mul_pos p.2.pos q.2.pos) ξ
  simpa using key _ primesOf_mul.symm isSUnit_mul

/-! ### The `{2, 3}` instance -/

/-- The prime `2`. -/
def two : Nat.Primes := ⟨2, Nat.prime_two⟩

/-- The prime `3`. -/
def three : Nat.Primes := ⟨3, Nat.prime_three⟩

@[category test, AMS 11, ref "udmfO5", group "th_solenoid_s_two_primes"]
theorem two_ne_three : two ≠ three := fun h ↦ by
  simpa [two, three] using congrArg Subtype.val h

/-- `N_{2,3} = 6`. -/
@[category test, AMS 11, ref "udmfO5", group "th_solenoid_s_two_primes"]
theorem sModulus_two_three : sModulus {two, three} = 6 := by
  rw [sModulus_pair two_ne_three]; rfl

/-- On `Σ_{2,3}`, `T = T32` moves the winding line along `(3/2)ⁿ ξ`. -/
@[category test, AMS 11 37, ref "udmfO5", group "th_solenoid_s_two_primes"]
theorem T32_iter_wind (ξ : ℝ) (n : ℕ) :
    (T two three)^[n] (wind ξ) = wind (ξ * (3 / 2) ^ n) := by
  rw [T_iter_wind]
  norm_num [two, three]

/-- On `Σ_{2,3}`, `σ6 = σ2 ; σ3` moves the winding line along `6ⁿ ξ`. -/
@[category test, AMS 11 37, ref "udmfO5", group "th_solenoid_s_two_primes"]
theorem σ6_iter_wind (ξ : ℝ) (n : ℕ) :
    (σpq two three)^[n] (wind ξ) = wind (ξ * 6 ^ n) := by
  rw [σpq_iter_wind]
  norm_num [two, three]

/-- `T32` fixes only `0` on `Σ_{2,3}`, because `3/2 - 1 = 1/2` is a `{2, 3}`-unit. -/
@[category test, AMS 11 37, ref "udmfO5", group "th_solenoid_s_two_primes"]
theorem eq_zero_of_T32_eq_self {x : Solenoid {two, three}} (h : T two three x = x) : x = 0 := by
  refine eq_zero_of_smulAut_eq_self _ ?_ h
  convert (isSUnit_left (p := two) (q := three)).inv using 1
  norm_num [two, three]

/-- `σ6`-equidistribution of `wind ξ` on `Σ_{2,3}` is u.d. mod 1 of `(ξ 6ⁿ)`. -/
@[category test, AMS 11 37, ref "udmfO5", group "th_solenoid_s_two_primes"]
theorem σ6_equidistributed_iff_ud (ξ : ℝ) :
    Equidistributed (isSUnit_mul : IsSUnit {two, three} _) ξ ↔
      Bertin.UniformlyDistributedModOne (fun n => ξ * 6 ^ n) := by
  rw [σpq_equidistributed_iff_ud]
  norm_num [two, three]

/-- **The dictionary for `(3/2)ⁿ` on `Σ_{2,3}`**, the general form of `TH.S6.weyl_dictionary`. -/
@[category test, AMS 11 37, ref "udmfO5", group "th_solenoid_s_two_primes"]
theorem weyl_dictionary_threeHalves (ξ : ℝ) :
    [Equidistributed (isSUnit_right.div isSUnit_left : IsSUnit {two, three} _) ξ,
      WeylFamily {two, three} (3 / 2) ξ, UDFamily {two, three} (3 / 2) ξ].TFAE := by
  have h : (((three : ℕ) : ℚ) / (two : ℕ)) = 3 / 2 := by norm_num [two, three]
  simpa only [h] using weyl_dictionary_T (p := two) (q := three) ξ

end TH.SolS
