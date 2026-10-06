/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TH.SolenoidS.Dictionary

/-!
# The integer-base collapse: for `u = b ∈ ℕ` the solenoid adds nothing

Deliverable D6 of plan-udmf-O5 (milestone M5, §1.5).  Let `b ≥ 1` and `S = {p ∣ b}`
(`Nat.primesOf b`), so that `ℤ[1/N_S] = ℤ[1/b]` (`mem_sIntegers_primesOf_iff`).  Then

> `UDFamily S b ξ ↔ (ξ bⁿ)ₙ is u.d. mod 1`   (`udFamily_iff_ud`),

and with the dictionary of `Dictionary.lean`,

> `Equidistributed σ_b ξ ↔ (ξ bⁿ)ₙ is u.d. mod 1`   (`equidistributed_iff_ud`).

The proof is folklore: every `r ∈ ℤ[1/b] \ {0}` is `m / bᵏ` with `m ∈ ℤ \ {0}`, so
`r ξ b^{n+k} = m · ξ bⁿ`; integer multiples of a u.d. sequence are u.d.
(`Bertin.UniformlyDistributedModOne.intCast_mul`, Weyl's criterion with `h ↦ h m`), and u.d. is
insensitive to an index shift (`Bertin.UniformlyDistributedModOne.shift`, a Cesàro average changes
by `O(k/N)`).  These two lemmas on the Bertin u.d. predicate are new to the estate.

**This is the irrelevance wall, not progress.**  `equidistributed_iff_ud` is the Lean form of
Proposition 2 of plan-udmf-F2ii §2.1: on the winding orbit the finite places of `Σ_b` are
invisible, and the whole content of "`×b` as a Hecke translate" collapses to Weyl's criterion on
the circle.  It says nothing about any particular `ξ` (ground rules GR1, GR5).  For a non-integer
unit such as `u = 3/2` no analogue is claimed in either direction: `r uⁿ` is not an integer
multiple of `u^{n-k}`, and the master family is genuinely larger than its `r = 1` member as far as
anyone knows.

For `S ⊋ Nat.primesOf b` the forward direction is still `ud_of_equidistributed`; the converse is
equivalent to the classical fact that multiplying a base-`b` normal number by a nonzero rational
keeps it normal (Wall), which is not formalised here.

## Main statements

* `Bertin.UniformlyDistributedModOne.shift`, `Bertin.UniformlyDistributedModOne.intCast_mul`.
* `mem_sIntegers_primesOf_iff` — `ℤ[1/N_S] = {m / bᵏ}` for `S = Nat.primesOf b`.
* `udFamily_iff_ud`, `equidistributed_iff_ud` — the collapse.

## Status

Everything in this file is standard; the contribution is the formalisation.

## References

* plan-udmf-O5 §1.5 (D6), plan-udmf-F2ii §2.1 (Proposition 2).
* [Wey16] H. Weyl, *Über die Gleichverteilung von Zahlen mod. Eins*, Math. Ann. 77 (1916).
* [KN74] L. Kuipers, H. Niederreiter, *Uniform Distribution of Sequences*, Wiley (1974), Ch. 1.
-/

open Filter Finset
open scoped Topology

namespace Bertin

/-- Shifting the index by `k` changes the Cesàro average of a sequence bounded by `1` by at most
`2k/N`; in particular one average tends to `0` iff the other does. -/
@[category API, AMS 11, ref "udmfO5", group "th_solenoid_s_integer_base"]
theorem tendsto_average_shift_iff {c : ℕ → ℂ} (hc : ∀ n, ‖c n‖ ≤ 1) (k : ℕ) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, c (n + k)) / N) atTop (𝓝 0) ↔
      Tendsto (fun N : ℕ => (∑ n ∈ range N, c n) / N) atTop (𝓝 0) := by
  have hbd : ∀ f : ℕ → ℂ, (∀ i, ‖f i‖ ≤ 1) → ‖∑ i ∈ range k, f i‖ ≤ k := fun f hf =>
    calc ‖∑ i ∈ range k, f i‖ ≤ ∑ i ∈ range k, ‖f i‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ range k, (1 : ℝ) := sum_le_sum fun i _ => hf i
      _ = k := by simp
  have hbound : ∀ N : ℕ, ‖(∑ n ∈ range N, c (n + k)) / N - (∑ n ∈ range N, c n) / N‖
      ≤ (2 * k : ℝ) / N := by
    intro N
    have h1 := sum_range_add c N k
    have h2 := sum_range_add c k N
    have hA : ∑ n ∈ range N, c (n + k) = ∑ n ∈ range N, c (k + n) :=
      sum_congr rfl fun n _ => by rw [add_comm]
    have hid : (∑ n ∈ range N, c (n + k)) - ∑ n ∈ range N, c n
        = ∑ i ∈ range k, c (N + i) - ∑ i ∈ range k, c i := by
      rw [add_comm k N] at h2
      rw [hA]
      linear_combination h1 - h2
    rw [← sub_div, hid, norm_div, Complex.norm_natCast]
    gcongr
    calc ‖∑ i ∈ range k, c (N + i) - ∑ i ∈ range k, c i‖
        ≤ ‖∑ i ∈ range k, c (N + i)‖ + ‖∑ i ∈ range k, c i‖ := norm_sub_le _ _
      _ ≤ k + k := add_le_add (hbd _ fun i => hc _) (hbd _ hc)
      _ = 2 * k := by ring
  have hdiff : Tendsto (fun N : ℕ => (∑ n ∈ range N, c (n + k)) / N
      - (∑ n ∈ range N, c n) / N) atTop (𝓝 0) :=
    squeeze_zero_norm hbound (tendsto_const_div_atTop_nhds_zero_nat _)
  constructor
  · intro h
    simpa using h.sub hdiff
  · intro h
    simpa using hdiff.add h

/-- **Weyl's criterion is shift-invariant.** -/
@[category API, AMS 11, ref "udmfO5", group "th_solenoid_s_integer_base"]
theorem weylCriterion_shift_iff {x : ℕ → ℝ} (k : ℕ) :
    WeylCriterion (fun n => x (n + k)) ↔ WeylCriterion x :=
  forall_congr' fun h => imp_congr_right fun _ =>
    tendsto_average_shift_iff (c := fun n => weylChar h (x n))
      (fun n => (norm_weylChar h (x n)).le) k

/-- **Uniform distribution mod 1 is insensitive to an index shift.** -/
@[category textbook, AMS 11, ref "udmfO5" "KN74", group "th_solenoid_s_integer_base"]
theorem UniformlyDistributedModOne.shift {x : ℕ → ℝ} (k : ℕ) :
    UniformlyDistributedModOne (fun n => x (n + k)) ↔ UniformlyDistributedModOne x := by
  rw [uniformlyDistributedModOne_iff_weylCriterion, uniformlyDistributedModOne_iff_weylCriterion,
    weylCriterion_shift_iff]

/-- **Nonzero integer multiples of a u.d. sequence are u.d.**: the Weyl sum of `(m xₙ)` at
frequency `h` is that of `(xₙ)` at frequency `h m ≠ 0`. -/
@[category textbook, AMS 11, ref "udmfO5" "KN74", group "th_solenoid_s_integer_base"]
theorem UniformlyDistributedModOne.intCast_mul {x : ℕ → ℝ} (hx : UniformlyDistributedModOne x)
    {m : ℤ} (hm : m ≠ 0) : UniformlyDistributedModOne (fun n => (m : ℝ) * x n) := by
  rw [uniformlyDistributedModOne_iff_weylCriterion] at hx ⊢
  intro h hh
  refine (hx (h * m) (mul_ne_zero hh hm)).congr fun N => ?_
  congr 1
  refine sum_congr rfl fun n _ => ?_
  congr 1
  push_cast
  ring

end Bertin

namespace TH.SolS

open Solenoid Rat

/-- For `S = Nat.primesOf b`, `ℤ[1/N_S] = ℤ[1/b] = {m / bᵏ}`: the radical `N_S` divides a power of
`b`, and `b` is an `S`-unit. -/
@[category API, AMS 11, ref "udmfO5", group "th_solenoid_s_integer_base"]
theorem mem_sIntegers_primesOf_iff {b : ℕ} (hb : 0 < b) {r : ℚ} :
    r ∈ sIntegers (Nat.primesOf b) ↔ ∃ (m : ℤ) (k : ℕ), r = m / (b : ℚ) ^ k := by
  constructor
  · rintro ⟨m, k, rfl⟩
    set N := sModulus (Nat.primesOf b)
    have hdvd : N ∣ b ^ N := Nat.dvd_pow_self_of_forall_prime_dvd sModulus_ne_zero hb.ne'
      fun ℓ hℓ hℓN => (Nat.mem_primesOf_iff_dvd (l := ⟨ℓ, hℓ⟩) hb.ne').mp
        (dvd_sModulus_iff.mp hℓN)
    obtain ⟨c, hc⟩ := hdvd
    have hc' : (b : ℚ) ^ N = (N : ℚ) * c := by exact_mod_cast hc
    have hc0 : (c : ℚ) ≠ 0 := by
      rintro h0
      rw [h0, mul_zero] at hc'
      exact pow_ne_zero _ (by exact_mod_cast hb.ne') hc'
    refine ⟨m * (c : ℤ) ^ k, N * k, ?_⟩
    rw [pow_mul, hc', mul_pow]
    push_cast
    rw [mul_div_mul_right _ _ (pow_ne_zero k hc0)]
  · rintro ⟨m, k, rfl⟩
    have hu := ((isSUnit_natCast (S := Nat.primesOf b) hb le_rfl).pow k).inv_mem
    rw [div_eq_mul_inv]
    exact Subring.mul_mem _ (intCast_mem _ m) hu

/-- **The integer-base collapse of the master family** (plan-udmf-O5 §1.5).  For `S = {p ∣ b}`,
every `(r ξ bⁿ)` with `r ∈ ℤ[1/b] \ {0}` is u.d. mod 1 as soon as `(ξ bⁿ)` alone is. -/
@[category research solved, AMS 11, ref "udmfO5" "Wey16", group "th_solenoid_s_integer_base"]
theorem udFamily_iff_ud {b : ℕ} (hb : 0 < b) (ξ : ℝ) :
    UDFamily (Nat.primesOf b) b ξ ↔
      Bertin.UniformlyDistributedModOne (fun n => ξ * (b : ℝ) ^ n) := by
  constructor
  · intro h
    simpa using h 1 one_ne_zero
  · intro h r hr
    obtain ⟨m, k, hmk⟩ := (mem_sIntegers_primesOf_iff hb).mp r.2
    have hm : m ≠ 0 := by
      rintro rfl
      exact hr (by simpa using hmk)
    have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
    rw [← Bertin.UniformlyDistributedModOne.shift k]
    convert h.intCast_mul hm using 2 with n
    rw [hmk]
    push_cast
    rw [pow_add]
    field_simp

/-- **Equidistribution of the `σ_b`-orbit of `wind ξ` in `Σ_b` is u.d. mod 1 of `(ξ bⁿ)`.**

This is the Lean form of the irrelevance wall (plan-udmf-F2ii §2.1, Proposition 2): the solenoid
picture of `×b` contains exactly the circle statement and nothing more.  It is **not** progress on
the normality of any given number. -/
@[category research solved, AMS 11 37, ref "udmfO5" "EW11", group "th_solenoid_s_integer_base"]
theorem equidistributed_iff_ud {b : ℕ} (hb : 0 < b) (ξ : ℝ) :
    Equidistributed (isSUnit_natCast (S := Nat.primesOf b) hb le_rfl) ξ ↔
      Bertin.UniformlyDistributedModOne (fun n => ξ * (b : ℝ) ^ n) :=
  (equidistributed_iff_weylFamily _ ξ).trans ((weylFamily_iff_udFamily ξ).trans
    (udFamily_iff_ud hb ξ))

/-! ### Tests -/

/-- On `Σ_{2,3}`, the `u = 3/2` slice: the conclusion of `TH.S6.ud_of_equidistributed`. -/
@[category test, AMS 11 37, ref "udmfO5", group "th_solenoid_s_integer_base"]
theorem ud_threeHalves_of_equidistributed (hu : IsSUnit (Nat.primesOf 6) (3 / 2)) {ξ : ℝ}
    (h : Equidistributed hu ξ) :
    Bertin.UniformlyDistributedModOne (fun n => ξ * (3 / 2) ^ n) := by
  simpa using ud_of_equidistributed h

/-- On `Σ_{2,3}`, `σ₆`-equidistribution of `wind ξ` is base-6 u.d. of `(ξ 6ⁿ)`. -/
@[category test, AMS 11 37, ref "udmfO5", group "th_solenoid_s_integer_base"]
theorem equidistributed_six_iff (ξ : ℝ) :
    Equidistributed (isSUnit_natCast (S := Nat.primesOf 6) (by norm_num) le_rfl) ξ ↔
      Bertin.UniformlyDistributedModOne (fun n => ξ * 6 ^ n) := by
  simpa using equidistributed_iff_ud (b := 6) (by norm_num) ξ

/-- Gate G-4: the separation lemma specialises to `S = {2, 3}` ... -/
@[category test, AMS 11, ref "udmfO5", group "th_solenoid_s_integer_base"]
theorem exists_χ_ne_zero_six {x : Solenoid (Nat.primesOf 6)} (hx : x ≠ 0) :
    ∃ r : sIntegers (Nat.primesOf 6), χ r x ≠ 0 :=
  exists_χ_ne_zero hx

/-- ... and to `S = {2, 3, 5}`. -/
@[category test, AMS 11, ref "udmfO5", group "th_solenoid_s_integer_base"]
theorem exists_χ_ne_zero_thirty {x : Solenoid (Nat.primesOf 30)} (hx : x ≠ 0) :
    ∃ r : sIntegers (Nat.primesOf 30), χ r x ≠ 0 :=
  exists_χ_ne_zero hx

/-- Gate G-4: the fundamental domain specialises to `S = {2, 3}` ... -/
@[category test, AMS 11, ref "udmfO5", group "th_solenoid_s_integer_base"]
theorem exists_unique_fundamental_six (g : ambient (Nat.primesOf 6)) :
    ∃! d, d ∈ D (Nat.primesOf 6) ∧ g - d ∈ lattice (Nat.primesOf 6) :=
  exists_unique_fundamental g

/-- ... and to `S = {2, 3, 5}`. -/
@[category test, AMS 11, ref "udmfO5", group "th_solenoid_s_integer_base"]
theorem exists_unique_fundamental_thirty (g : ambient (Nat.primesOf 30)) :
    ∃! d, d ∈ D (Nat.primesOf 30) ∧ g - d ∈ lattice (Nat.primesOf 30) :=
  exists_unique_fundamental g

end TH.SolS
