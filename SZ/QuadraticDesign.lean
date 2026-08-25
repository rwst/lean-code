/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import SZ.PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.Int.Basic

/-!
# Designed total divisibility, and its instances

Report `plans/report-dubickas.html` §D.4, executed: the trace design of
`SZ/PellDesign.lean` at a general modulus.

[Dub06EO] Theorem 6 (after Dubickas–Zaimi) confines `{ξ αⁿ}` to an `ε`-neighbourhood of
`1/|P_α(1)|`, with `ξ` depending on `ε`; the report asks to systematise the resulting
congruences.  The trace design does better: for a real quadratic pair with a negative
second conjugate and

> `a ≡ 0`,  `b ≡ 1`  (mod `m`),

the **closed-form** `ξ = -β/(α-β)` gives `m ∣ ⌊ξ αⁿ⌋` for *every* `n ≥ 0` — an exact
congruence, not an `ε`-confinement, with no threshold and no limit.  Note
`P_α(1) = 1 - a - b ≡ 0 (mod m)`, so the family lives at `|P_α(1)| ≥ m`: the same regime
as the Dubickas–Zaimi condition `P_α(1) ≤ -(m+1)`, reached by a different route.

The dichotomy this completes: total divisibility by a *designed* modulus is possible for
these algebraic `α`, and impossible for rational non-integer `a`, where [DN05] produces
unavoidable divisor sets.

## Instances

| `α` | `(a,b)` | moduli |
|---|---|---|
| `1 + √2` | `(2,1)` | `2` (`SZ/Silver.lean`, Theorem A) |
| `2 + √5` | `(4,1)` | `2` |
| `3 + √10` | `(6,1)` | `2`, `3`, `6` |

## Main results

* `SZ.eventually_composite` — the arithmetic corollary: all but finitely many `⌊ξ αⁿ⌋`
  are composite, for every design with `m ≥ 2`.
* `SZ.twoAddSqrtFive_mem_MahlerZ`, `SZ.threeAddSqrtTen_mem_MahlerZ` — the instances.
* `SZ.six_dvd_floor_sqrtTen` — `6 ∣ ⌊ξ (3+√10)ⁿ⌋` for every `n`, with `ξ` explicit.

## References

* [Dub06EO] A. Dubickas, *Even and odd integral parts of powers of a real number*,
  Glasgow Math. J. **48** (2006), 331–336, Theorem 6.
* [DN05] A. Dubickas, A. Novikas, *Integer parts of powers of rational numbers*, Math. Z.
  **251** (2005), 635–648 — the rational-base contrast.
-/

namespace SZ

open Real Filter

variable {α β : ℝ} {a b : ℤ}

/-- The designed orbit tends to infinity. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_d4_congruence"]
theorem tendsto_design (h : Pair α β a b) (hβ : β < 0) :
    Tendsto (fun n : ℕ => xiDesign α β * α ^ n) atTop atTop :=
  Tendsto.const_mul_atTop (xiDesign_pos h hβ)
    (tendsto_pow_atTop_atTop_of_one_lt h.one_lt)

/-- **The composite corollary of the design.**  For every modulus `m ≥ 2` admitted by the
design, all but finitely many integral parts `⌊ξ αⁿ⌋` are composite. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_d4_congruence"]
theorem eventually_composite {m : ℤ} (h : Pair α β a b) (hβ : β < 0) (hm : 2 ≤ m)
    (ha : m ∣ a) (hb : m ∣ (b - 1)) :
    ∀ᶠ n in atTop, ¬ Prime ⌊xiDesign α β * α ^ n⌋ ∧ 1 < ⌊xiDesign α β * α ^ n⌋ := by
  have hgt := (tendsto_design h hβ).eventually_gt_atTop ((m : ℝ) + 1)
  refine hgt.mono fun n hn => ?_
  set x : ℤ := ⌊xiDesign α β * α ^ n⌋ with hx
  have hfl : ((m : ℝ) + 1) - 1 < (x : ℝ) :=
    lt_of_lt_of_le (by linarith) (Int.sub_one_lt_floor _ |>.le)
  have hmx : m < x := by exact_mod_cast (by linarith : (m : ℝ) < (x : ℝ))
  have hdvd : m ∣ x := dvd_floor_of_neg h hβ ha hb n
  refine ⟨fun hp => ?_, by omega⟩
  have hpn : Nat.Prime x.natAbs := Int.prime_iff_natAbs_prime.mp hp
  have hmd : m.natAbs ∣ x.natAbs := Int.natAbs_dvd_natAbs.mpr hdvd
  rcases hpn.eq_one_or_self_of_dvd _ hmd with h1 | h1 <;> omega

/-! ## Instances -/

private theorem sqrt_five_facts :
    Real.sqrt 5 ^ 2 = 5 ∧ 2 < Real.sqrt 5 ∧ Real.sqrt 5 < 3 := by
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨hsq, ?_, ?_⟩ <;> nlinarith

private theorem sqrt_ten_facts :
    Real.sqrt 10 ^ 2 = 10 ∧ 3 < Real.sqrt 10 ∧ Real.sqrt 10 < 4 := by
  have hsq : Real.sqrt 10 ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 10 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨hsq, ?_, ?_⟩ <;> nlinarith

/-- `2 + √5` and `2 - √5` are the roots of `x² = 4x + 1`. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_d4_congruence"]
theorem sqrtFive_pair : Pair (2 + Real.sqrt 5) (2 - Real.sqrt 5) 4 1 := by
  obtain ⟨hsq, h2, h3⟩ := sqrt_five_facts
  exact { one_lt := by linarith
          absLt := by rw [abs_lt]; constructor <;> linarith
          sum := by push_cast; ring
          prod := by push_cast; linear_combination -hsq }

/-- The second instance of Theorem A's design: `2 + √5 ∈ 𝒵`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_d4_congruence"]
theorem twoAddSqrtFive_mem_MahlerZ : (2 + Real.sqrt 5) ∈ MahlerZ := by
  obtain ⟨-, h2, h3⟩ := sqrt_five_facts
  exact mem_MahlerZ_of_neg sqrtFive_pair (by linarith) ⟨2, by ring⟩
    (by rintro ⟨k, hk⟩; omega)

/-- `3 + √10` and `3 - √10` are the roots of `x² = 6x + 1`. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_d4_congruence"]
theorem sqrtTen_pair : Pair (3 + Real.sqrt 10) (3 - Real.sqrt 10) 6 1 := by
  obtain ⟨hsq, h3, h4⟩ := sqrt_ten_facts
  exact { one_lt := by linarith
          absLt := by rw [abs_lt]; constructor <;> linarith
          sum := by push_cast; ring
          prod := by push_cast; linear_combination -hsq }

@[category API, AMS 11, ref "Dub06EO", group "dub06_d4_congruence"]
theorem sqrtTen_conj_neg : (3 : ℝ) - Real.sqrt 10 < 0 := by
  obtain ⟨-, h3, -⟩ := sqrt_ten_facts; linarith

/-- **Report §D.4 in one instance.**  `6 ∣ ⌊ξ (3+√10)ⁿ⌋` for every `n ≥ 0`, with the
closed-form `ξ = -(3-√10)/(2√10)`.  Here `a = 6 ≡ 0` and `b = 1 ≡ 1` modulo `6`
simultaneously, so the same `ξ` also realises the moduli `2` and `3`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_d4_congruence"]
theorem six_dvd_floor_sqrtTen (n : ℕ) :
    (6 : ℤ) ∣ ⌊xiDesign (3 + Real.sqrt 10) (3 - Real.sqrt 10) * (3 + Real.sqrt 10) ^ n⌋ :=
  dvd_floor_of_neg sqrtTen_pair sqrtTen_conj_neg ⟨1, by ring⟩ ⟨0, by ring⟩ n

@[category research solved, AMS 11, ref "Dub06EO", group "dub06_d4_congruence"]
theorem three_dvd_floor_sqrtTen (n : ℕ) :
    (3 : ℤ) ∣ ⌊xiDesign (3 + Real.sqrt 10) (3 - Real.sqrt 10) * (3 + Real.sqrt 10) ^ n⌋ :=
  dvd_floor_of_neg sqrtTen_pair sqrtTen_conj_neg ⟨2, by ring⟩ ⟨0, by ring⟩ n

@[category research solved, AMS 11, ref "Dub06EO", group "dub06_d4_congruence"]
theorem threeAddSqrtTen_mem_MahlerZ : (3 + Real.sqrt 10) ∈ MahlerZ :=
  mem_MahlerZ_of_neg sqrtTen_pair sqrtTen_conj_neg ⟨3, by ring⟩
    (by rintro ⟨k, hk⟩; omega)

/-- The composite corollary at `3 + √10`: all but finitely many `⌊ξ (3+√10)ⁿ⌋` are
composite, being divisible by `6`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_d4_congruence"]
theorem eventually_composite_sqrtTen :
    ∀ᶠ n in atTop,
      ¬ Prime ⌊xiDesign (3 + Real.sqrt 10) (3 - Real.sqrt 10) * (3 + Real.sqrt 10) ^ n⌋ ∧
      1 < ⌊xiDesign (3 + Real.sqrt 10) (3 - Real.sqrt 10) * (3 + Real.sqrt 10) ^ n⌋ :=
  eventually_composite (m := 6) sqrtTen_pair sqrtTen_conj_neg (by norm_num) ⟨1, by ring⟩
    ⟨0, by ring⟩

end SZ
