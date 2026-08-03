/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Analysis.Normed.Ring.Ultra
public import Mathlib.Topology.Instances.AddCircle.Defs

@[expose] public section

/-!
# The `p`-adic fractional part, and the canonical character of `ℚ_[p]`

Every `y ∈ ℚ_[p]` is within `1` of an element `m / pᵏ` of `ℤ[1/p]` (`Padic.exists_principal_part`;
this is the density of `ℤ` in `ℤ_[p]` after scaling), and two such *principal parts* differ by a
rational integer.  So

`fracPart p y := [m / pᵏ] ∈ ℝ ⧸ ℤ`

is well defined (`Padic.fracPart_eq`), and it is the canonical surjection

`ℚ_[p] ↠ ℚ_[p] / ℤ_[p] ≅ ℤ[1/p] / ℤ ↪ ℝ / ℤ`

whose kernel is exactly `ℤ_[p]` (`Padic.fracPart_eq_zero_iff`).  Composed with
`AddCircle.toCircle` it is the standard additive character `e_p` of `ℚ_[p]`, the local factor of
the adelic character; it is continuous because it is a homomorphism killing the *open* subgroup
`ℤ_[p]` (`Padic.continuous_fracPart`).

Nothing here is deep; the point is that Mathlib has the pieces (`PadicInt.denseRange_intCast`,
`padicNorm.dvd_iff_norm_le`) but not the map.

## Main declarations

* `Padic.exists_principal_part` — every `y ∈ ℚ_[p]` is within `1` of some `m / pᵏ`.
* `Padic.fracPart`, `Padic.fracPartHom` — the fractional part, as a function and as an
  `AddMonoidHom` to `AddCircle 1 = ℝ ⧸ ℤ`.
* `Padic.fracPart_eq` — its defining property: *any* principal part computes it.
* `Padic.fracPart_eq_zero_iff` — the kernel is `ℤ_[p]`.
* `Padic.continuous_fracPart` — continuity (indeed local constancy).

## References

Standard; see e.g. Tate's thesis, or Ramakrishnan–Valenza, *Fourier Analysis on Number Fields*,
Ch. 3, for the local additive characters.  The normalization here is the usual one:
`fracPart p` is trivial on `ℤ_[p]` and sends `p⁻¹` to `[1/p]`.
-/

namespace Padic

open Metric

variable {p : ℕ} [Fact p.Prime]

/-! ### Principal parts -/

/-- **Strong approximation at one finite place.**  Every `y ∈ ℚ_[p]` differs from an element
`m / pᵏ` of `ℤ[1/p]` by a `p`-adic integer.  Proof: scale `y` into `ℤ_[p]` by a power of `p`, then
use that `ℤ` is dense in `ℤ_[p]`. -/
theorem exists_principal_part (p : ℕ) [Fact p.Prime] (y : ℚ_[p]) :
    ∃ (m : ℤ) (k : ℕ), ‖y - (((m : ℚ) / (p : ℚ) ^ k : ℚ) : ℚ_[p])‖ ≤ 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp1
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖y‖ hp1
  have hpk : ‖((p : ℚ_[p]) ^ k : ℚ_[p])‖ = ((p : ℝ) ^ k)⁻¹ := by
    rw [norm_pow, Padic.norm_p, inv_pow]
  have hw : ‖(p : ℚ_[p]) ^ k * y‖ ≤ 1 := by
    rw [norm_mul, hpk, inv_mul_le_iff₀ (by positivity), mul_one]
    exact hk.le
  set x : ℤ_[p] := ⟨(p : ℚ_[p]) ^ k * y, hw⟩ with hx
  obtain ⟨m, hm⟩ := Metric.denseRange_iff.mp (PadicInt.denseRange_intCast (p := p))
    x (((p : ℝ) ^ k)⁻¹) (by positivity)
  refine ⟨m, k, ?_⟩
  have key : ‖(p : ℚ_[p]) ^ k * y - (m : ℚ_[p])‖ < ((p : ℝ) ^ k)⁻¹ := by
    rw [dist_eq_norm, PadicInt.norm_def] at hm
    have hcoe : ((x - (m : ℤ_[p]) : ℤ_[p]) : ℚ_[p]) = (p : ℚ_[p]) ^ k * y - (m : ℚ_[p]) := by
      rw [hx]; push_cast; ring
    rwa [hcoe] at hm
  have hpk0 : ((p : ℚ_[p]) ^ k) ≠ 0 := by
    apply pow_ne_zero
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hrw : y - (((m : ℚ) / (p : ℚ) ^ k : ℚ) : ℚ_[p])
      = ((p : ℚ_[p]) ^ k * y - (m : ℚ_[p])) / (p : ℚ_[p]) ^ k := by
    push_cast
    field_simp
  rw [hrw, norm_div, hpk, div_le_one (by positivity)]
  exact le_of_lt (by simpa using key)

theorem exists_principal_part' (p : ℕ) [Fact p.Prime] (y : ℚ_[p]) :
    ∃ a : ℤ × ℕ, ‖y - (((a.1 : ℚ) / (p : ℚ) ^ a.2 : ℚ) : ℚ_[p])‖ ≤ 1 := by
  obtain ⟨m, k, h⟩ := exists_principal_part p y
  exact ⟨(m, k), h⟩

/-- A choice of principal part of `y`: a rational of the shape `m / pᵏ` with `‖y - m/pᵏ‖ ≤ 1`.
Only its class modulo `ℤ` is canonical, and that class is `Padic.fracPart`. -/
noncomputable def principalPart (p : ℕ) [Fact p.Prime] (y : ℚ_[p]) : ℚ :=
  ((Classical.choose (exists_principal_part' p y)).1 : ℚ)
    / (p : ℚ) ^ (Classical.choose (exists_principal_part' p y)).2

theorem principalPart_spec (y : ℚ_[p]) : ‖y - ((principalPart p y : ℚ) : ℚ_[p])‖ ≤ 1 :=
  Classical.choose_spec (exists_principal_part' p y)

theorem exists_principalPart_eq (y : ℚ_[p]) :
    ∃ (m : ℤ) (k : ℕ), principalPart p y = (m : ℚ) / (p : ℚ) ^ k :=
  ⟨_, _, rfl⟩

/-! ### Rationals with `p`-power denominator that are `p`-adic integers -/

/-- A rational of the shape `m / pᵏ` which is a `p`-adic integer is a rational integer.  This is
the uniqueness input: two principal parts of the same `y` differ by an integer. -/
theorem exists_intCast_of_padicNorm_le_one {m : ℤ} {k : ℕ}
    (h : padicNorm p ((m : ℚ) / (p : ℚ) ^ k) ≤ 1) : ∃ n : ℤ, (m : ℚ) / (p : ℚ) ^ k = (n : ℚ) := by
  have hp1 : (1 : ℚ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℚ) < p := lt_trans zero_lt_one hp1
  have hdvd : ((p ^ k : ℕ) : ℤ) ∣ m := by
    rw [padicNorm.dvd_iff_norm_le]
    rw [padicNorm.div, IsAbsoluteValue.abv_pow (padicNorm p), padicNorm.padicNorm_p_of_prime,
      div_le_one (by positivity)] at h
    calc padicNorm p (m : ℚ) ≤ ((p : ℚ)⁻¹) ^ k := h
      _ = (p : ℚ) ^ (-k : ℤ) := by rw [zpow_neg, zpow_natCast, inv_pow]
  obtain ⟨n, hn⟩ := hdvd
  refine ⟨n, ?_⟩
  rw [hn]
  push_cast
  field_simp

/-- The norm of `p⁻ᵏ`, in the shape in which it occurs as a frequency: `‖1/pᵏ‖ = pᵏ`. -/
theorem norm_ratCast_inv_pow (p : ℕ) [Fact p.Prime] (k : ℕ) :
    ‖(((1 : ℚ) / (p : ℚ) ^ k : ℚ) : ℚ_[p])‖ = (p : ℝ) ^ k := by
  have hp0 : ((p : ℚ_[p])) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hcast : (((1 : ℚ) / (p : ℚ) ^ k : ℚ) : ℚ_[p]) = ((p : ℚ_[p]) ^ k)⁻¹ := by
    push_cast
    field_simp
  rw [hcast, norm_inv, norm_pow, Padic.norm_p, inv_pow, inv_inv]

/-! ### The fractional part -/

/-- **The `p`-adic fractional part** of `y ∈ ℚ_[p]`: the class modulo `ℤ` of any principal part of
`y`.  It is the canonical character `ℚ_[p] → ℝ/ℤ` with kernel `ℤ_[p]`. -/
noncomputable def fracPart (p : ℕ) [Fact p.Prime] (y : ℚ_[p]) : AddCircle (1 : ℝ) :=
  ((principalPart p y : ℝ) : AddCircle (1 : ℝ))

theorem coe_eq_coe_of_sub_int {a b : ℚ} {n : ℤ} (h : a - b = (n : ℚ)) :
    ((a : ℝ) : AddCircle (1 : ℝ)) = ((b : ℝ) : AddCircle (1 : ℝ)) := by
  rw [← sub_eq_zero, ← QuotientAddGroup.mk_sub]
  refine (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨n, ?_⟩
  have : (a : ℝ) - (b : ℝ) = ((n : ℚ) : ℝ) := by exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) h
  simp only [zsmul_eq_mul, mul_one]
  rw [this]
  push_cast
  ring

/-- **The defining property of `fracPart`**: *any* principal part of `y` computes it. -/
theorem fracPart_eq {y : ℚ_[p]} {m : ℤ} {k : ℕ}
    (h : ‖y - (((m : ℚ) / (p : ℚ) ^ k : ℚ) : ℚ_[p])‖ ≤ 1) :
    fracPart p y = ((((m : ℚ) / (p : ℚ) ^ k : ℚ) : ℝ) : AddCircle (1 : ℝ)) := by
  obtain ⟨m', k', hpp⟩ := exists_principalPart_eq (p := p) y
  have hsp := principalPart_spec (p := p) y
  rw [hpp] at hsp
  set a : ℚ := (m : ℚ) / (p : ℚ) ^ k with ha
  set b : ℚ := (m' : ℚ) / (p : ℚ) ^ k' with hb
  have hnorm : ‖((a - b : ℚ) : ℚ_[p])‖ ≤ 1 := by
    have hrw : ((a - b : ℚ) : ℚ_[p]) = (y - (b : ℚ_[p])) - (y - (a : ℚ_[p])) := by
      push_cast; ring
    rw [hrw, sub_eq_add_neg]
    refine le_trans (Padic.nonarchimedean _ _) (max_le hsp ?_)
    rwa [norm_neg]
  have hp0 : ((p : ℚ)) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hsub : a - b = ((m * (p : ℤ) ^ k' - m' * (p : ℤ) ^ k : ℤ) : ℚ) / (p : ℚ) ^ (k + k') := by
    rw [ha, hb, pow_add]
    push_cast
    field_simp
  have hpn : padicNorm p (((m * (p : ℤ) ^ k' - m' * (p : ℤ) ^ k : ℤ) : ℚ)
      / (p : ℚ) ^ (k + k')) ≤ 1 := by
    rw [← hsub]
    rw [Padic.eq_padicNorm] at hnorm
    exact_mod_cast hnorm
  obtain ⟨n, hn⟩ := exists_intCast_of_padicNorm_le_one hpn
  rw [fracPart, hpp]
  exact (coe_eq_coe_of_sub_int (hsub.trans hn)).symm

theorem fracPart_zero : fracPart p (0 : ℚ_[p]) = 0 := by
  have h : ‖(0 : ℚ_[p]) - (((0 : ℤ) : ℚ) / (p : ℚ) ^ (0 : ℕ) : ℚ)‖ ≤ 1 := by norm_num
  rw [fracPart_eq h]
  norm_num

theorem fracPart_add (y z : ℚ_[p]) :
    fracPart p (y + z) = fracPart p y + fracPart p z := by
  obtain ⟨m, k, hpy⟩ := exists_principalPart_eq (p := p) y
  obtain ⟨m', k', hpz⟩ := exists_principalPart_eq (p := p) z
  have hy := principalPart_spec (p := p) y
  have hz := principalPart_spec (p := p) z
  rw [hpy] at hy
  rw [hpz] at hz
  have hp0 : ((p : ℚ)) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hsum : ((m : ℚ) / (p : ℚ) ^ k) + ((m' : ℚ) / (p : ℚ) ^ k')
      = ((m * (p : ℤ) ^ k' + m' * (p : ℤ) ^ k : ℤ) : ℚ) / (p : ℚ) ^ (k + k') := by
    rw [pow_add]
    push_cast
    field_simp
  have hnorm : ‖(y + z) - ((((m * (p : ℤ) ^ k' + m' * (p : ℤ) ^ k : ℤ) : ℚ)
      / (p : ℚ) ^ (k + k') : ℚ) : ℚ_[p])‖ ≤ 1 := by
    rw [← hsum]
    have hrw : (y + z) - ((((m : ℚ) / (p : ℚ) ^ k) + ((m' : ℚ) / (p : ℚ) ^ k') : ℚ) : ℚ_[p])
        = (y - (((m : ℚ) / (p : ℚ) ^ k : ℚ) : ℚ_[p]))
          + (z - (((m' : ℚ) / (p : ℚ) ^ k' : ℚ) : ℚ_[p])) := by
      push_cast; ring
    rw [hrw]
    exact le_trans (Padic.nonarchimedean _ _) (max_le hy hz)
  rw [fracPart_eq hnorm, fracPart_eq hy, fracPart_eq hz, ← hsum]
  push_cast
  rw [QuotientAddGroup.mk_add]

/-- The `p`-adic fractional part as an additive character `ℚ_[p] → ℝ/ℤ`. -/
noncomputable def fracPartHom (p : ℕ) [Fact p.Prime] : ℚ_[p] →+ AddCircle (1 : ℝ) :=
  AddMonoidHom.mk' (fracPart p) fracPart_add

@[simp]
theorem fracPartHom_apply (y : ℚ_[p]) : fracPartHom p y = fracPart p y := rfl

theorem fracPart_neg (y : ℚ_[p]) : fracPart p (-y) = -fracPart p y :=
  map_neg (fracPartHom p) y

theorem fracPart_sub (y z : ℚ_[p]) : fracPart p (y - z) = fracPart p y - fracPart p z :=
  map_sub (fracPartHom p) y z

/-! ### The kernel is `ℤ_[p]` -/

/-- **The kernel of the canonical character is `ℤ_[p]`.** -/
theorem fracPart_eq_zero_iff {y : ℚ_[p]} : fracPart p y = 0 ↔ ‖y‖ ≤ 1 := by
  constructor
  · intro h
    obtain ⟨m, k, hpp⟩ := exists_principalPart_eq (p := p) y
    have hsp := principalPart_spec (p := p) y
    rw [hpp] at hsp
    rw [fracPart_eq hsp] at h
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h
    have hq : ((m : ℚ) / (p : ℚ) ^ k) = (n : ℚ) := by
      have : (((m : ℚ) / (p : ℚ) ^ k : ℚ) : ℝ) = ((n : ℚ) : ℝ) := by
        rw [← hn]; push_cast; ring
      exact_mod_cast this
    rw [hq] at hsp
    have hrw : y = (y - ((n : ℚ) : ℚ_[p])) + ((n : ℚ) : ℚ_[p]) := by ring
    rw [hrw]
    refine le_trans (Padic.nonarchimedean _ _) (max_le hsp ?_)
    push_cast
    exact Padic.norm_int_le_one n
  · intro h
    have h0 : ‖y - (((0 : ℤ) : ℚ) / (p : ℚ) ^ (0 : ℕ) : ℚ)‖ ≤ 1 := by simpa using h
    rw [fracPart_eq h0]
    norm_num

/-- A `p`-adic integer has zero fractional part. -/
theorem fracPart_of_norm_le_one {y : ℚ_[p]} (h : ‖y‖ ≤ 1) : fracPart p y = 0 :=
  fracPart_eq_zero_iff.mpr h

theorem fracPart_intCast (n : ℤ) : fracPart p (n : ℚ_[p]) = 0 :=
  fracPart_of_norm_le_one (Padic.norm_int_le_one n)

/-- A rational which is a `p`-adic integer has zero fractional part. -/
theorem fracPart_ratCast_of_padicNorm_le_one {s : ℚ} (h : padicNorm p s ≤ 1) :
    fracPart p ((s : ℚ) : ℚ_[p]) = 0 := by
  refine fracPart_of_norm_le_one ?_
  rw [Padic.eq_padicNorm]
  exact_mod_cast h

/-- The fractional part of a *rational* `s`, computed from a decomposition `s = a + (integral)`
with `a = m / pᵏ`. -/
theorem fracPart_ratCast_eq {s : ℚ} {m : ℤ} {k : ℕ}
    (h : padicNorm p (s - (m : ℚ) / (p : ℚ) ^ k) ≤ 1) :
    fracPart p ((s : ℚ) : ℚ_[p]) = ((((m : ℚ) / (p : ℚ) ^ k : ℚ) : ℝ) : AddCircle (1 : ℝ)) := by
  refine fracPart_eq ?_
  have hrw : ((s : ℚ) : ℚ_[p]) - (((m : ℚ) / (p : ℚ) ^ k : ℚ) : ℚ_[p])
      = ((s - (m : ℚ) / (p : ℚ) ^ k : ℚ) : ℚ_[p]) := by push_cast; ring
  rw [hrw, Padic.eq_padicNorm]
  exact_mod_cast h

/-! ### Continuity -/

/-- `fracPart` is constant on every ball of radius `1`: it kills the open subgroup `ℤ_[p]`. -/
theorem fracPart_eq_of_norm_sub_le {y z : ℚ_[p]} (h : ‖y - z‖ ≤ 1) :
    fracPart p y = fracPart p z := by
  have hz := fracPart_sub y z
  rw [fracPart_of_norm_le_one h] at hz
  exact sub_eq_zero.mp hz.symm

/-- **The canonical character is continuous** — indeed locally constant, since it is trivial on the
*open* subgroup `ℤ_[p]`. -/
theorem continuous_fracPart : Continuous (fracPart p) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hball : closedBall y 1 ∈ nhds y :=
    (IsUltrametricDist.isOpen_closedBall y one_ne_zero).mem_nhds (mem_closedBall_self zero_le_one)
  have heq : fracPart p =ᶠ[nhds y] fun _ => fracPart p y := by
    filter_upwards [hball] with u hu
    refine fracPart_eq_of_norm_sub_le ?_
    rwa [mem_closedBall, dist_eq_norm] at hu
  exact continuousAt_const.congr heq.symm

end Padic
