/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import SZ.Trace
import Mathlib.Algebra.Order.Ring.Abs

/-!
# The trace-parity design for a real quadratic pair

Milestone M2 of `plans/plan-dubD1.html`: the mechanism behind Theorem A, and — at a general
modulus — behind report §D.4's designed congruences.

Fix reals `α > 1` and `β` with `|β| < 1` whose sum and product are integers,
`α + β = a`, `α β = -b`; equivalently `α` and `β` are the two roots of `x² = a x + b`.
Put `ξ = -β/(α-β)`, `ξ' = α/(α-β)`, so that `ξ + ξ' = 1` and `ξ α + ξ' β = 0`.  Then
`SZ.rec2_real` gives `ξ αⁿ = T n - ξ' βⁿ` with `T = rec2 a b 1 0` an *integer* sequence,
and `0 < ξ' < 1` whenever `β < 0`.  Since `βⁿ` then alternates in sign,

> `⌊ξ αⁿ⌋ = T n - 1` for even `n`,   `⌊ξ αⁿ⌋ = T n` for odd `n`

— exactly, for every `n ≥ 0`, with no threshold (`floorNeg`).  The design is finished by
`SZ.rec2_dvd_sub`: as soon as `m ∣ a` and `m ∣ b - 1`, the sequence `T` is `≡ 1` at even
`n` and `≡ 0` at odd `n` modulo `m`, so *both* branches leave a multiple of `m`.

**The alternation that kills the confinement engine is the fuel.**  The second conjugate
of `1 + √2` is `1 - √2 ∈ (-1,0)`, so `{ξ αⁿ}` accumulates at both `0` and `1` and no
`ε`-confinement around `1/|P(1)| = 1/2` can decide the parity ([Dub06EO] Thm 6 straddles).
The design does not confine the fractional parts at all — it locks the *integer* part's
residue and lets the sign of `βⁿ` cancel against it.

The companion cell — `β ∈ (0,1)`, the strong Pisot numbers of [Dub06EO] Thm 1(iii) — is
`mem_MahlerZ_of_pos`, on the seeds `t₀ = 0`, `t₁ = 2`: there the whole sequence stays even
and the sign of `ξ' βⁿ` never changes, so no compensation is needed.

## Main results

* `SZ.floorNeg` — the exact floor identity for the negative-conjugate cell.
* `SZ.dvd_floor_of_neg` — **report §D.4 / plan Theorem C**: `m ∣ a`, `m ∣ b - 1` implies
  `m ∣ ⌊ξ αⁿ⌋` for every `n ≥ 0`, with a closed-form `ξ ∈ ℚ(α)`.
* `SZ.mem_MahlerZ_of_neg` — hence `α ∈ 𝒵` when `a` is even and `b` is odd.
* `SZ.mem_MahlerZ_of_pos` — `α ∈ 𝒵` when the second conjugate is positive.

## References

* [Dub06EO] A. Dubickas, *Even and odd integral parts of powers of a real number*,
  Glasgow Math. J. **48** (2006), 331–336.
-/

namespace SZ

/-- A **real quadratic pair**: `α > 1` and `|β| < 1` are the two roots of `x² = a x + b`,
presented by their symmetric functions so that no square root has to be constructed. -/
structure Pair (α β : ℝ) (a b : ℤ) : Prop where
  /-- the dominant root exceeds `1` -/
  one_lt : 1 < α
  /-- the second root is inside the unit disc -/
  absLt : |β| < 1
  /-- `α + β = a` -/
  sum : α + β = (a : ℝ)
  /-- `α β = -b` -/
  prod : α * β = -(b : ℝ)

namespace Pair

variable {α β : ℝ} {a b : ℤ}

@[category API, AMS 11, ref "Dub06EO", group "dub06_sz_design"]
theorem beta_lt_one (h : Pair α β a b) : β < 1 := (abs_lt.mp h.absLt).2

@[category API, AMS 11, ref "Dub06EO", group "dub06_sz_design"]
theorem neg_one_lt_beta (h : Pair α β a b) : -1 < β := (abs_lt.mp h.absLt).1

@[category API, AMS 11, ref "Dub06EO", group "dub06_sz_design"]
theorem sq_alpha (h : Pair α β a b) : α ^ 2 = (a : ℝ) * α + (b : ℝ) := by
  have hs := h.sum
  have hp := h.prod
  have hb : (b : ℝ) = -(α * β) := by linarith
  rw [← hs, hb]; ring

@[category API, AMS 11, ref "Dub06EO", group "dub06_sz_design"]
theorem sq_beta (h : Pair α β a b) : β ^ 2 = (a : ℝ) * β + (b : ℝ) := by
  have hs := h.sum
  have hp := h.prod
  have hb : (b : ℝ) = -(α * β) := by linarith
  rw [← hs, hb]; ring

@[category API, AMS 11, ref "Dub06EO", group "dub06_sz_design"]
theorem sub_pos (h : Pair α β a b) : 0 < α - β := by
  have := h.one_lt; have := h.beta_lt_one; linarith

/-- `|βⁿ| ≤ 1` for every `n`. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_sz_design"]
theorem abs_pow_le (h : Pair α β a b) (n : ℕ) : |β ^ n| ≤ 1 := by
  rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) h.absLt.le

end Pair

/-! ## The negative-conjugate cell: sign-compensated trace parity -/

/-- The designed multiplier `ξ = -β/(α-β) ∈ ℚ(α)`.  At `α = 1 + √2` it is `(2-√2)/4`. -/
noncomputable def xiDesign (α β : ℝ) : ℝ := -β / (α - β)

/-- Its conjugate `ξ' = α/(α-β)`, the coefficient of `βⁿ` in the trace. -/
noncomputable def xiDesign' (α β : ℝ) : ℝ := α / (α - β)

variable {α β : ℝ} {a b : ℤ}

@[category API, AMS 11, ref "Dub06EO", group "dub06_sz_design"]
theorem xiDesign_pos (h : Pair α β a b) (hβ : β < 0) : 0 < xiDesign α β :=
  div_pos (by linarith) h.sub_pos

@[category API, AMS 11, ref "Dub06EO", group "dub06_sz_design"]
theorem xiDesign'_pos (h : Pair α β a b) : 0 < xiDesign' α β :=
  div_pos (lt_trans zero_lt_one h.one_lt) h.sub_pos

@[category API, AMS 11, ref "Dub06EO", group "dub06_sz_design"]
theorem xiDesign'_lt_one (h : Pair α β a b) (hβ : β < 0) : xiDesign' α β < 1 := by
  have hd := h.sub_pos
  show α / (α - β) < 1
  rw [div_lt_one hd]; linarith

/-- The two seeds of the design are the integers `1` and `0`. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_sz_design"]
theorem xiDesign_seed₀ (h : Pair α β a b) :
    xiDesign α β + xiDesign' α β = ((1 : ℤ) : ℝ) := by
  have hd := ne_of_gt h.sub_pos
  show -β / (α - β) + α / (α - β) = ((1 : ℤ) : ℝ)
  field_simp
  ring

@[category API, AMS 11, ref "Dub06EO", group "dub06_sz_design"]
theorem xiDesign_seed₁ (h : Pair α β a b) :
    xiDesign α β * α + xiDesign' α β * β = ((0 : ℤ) : ℝ) := by
  have hd := ne_of_gt h.sub_pos
  show -β / (α - β) * α + α / (α - β) * β = ((0 : ℤ) : ℝ)
  field_simp
  ring

/-- **The exact floor identity.**  For a negative second conjugate the designed `ξ`
produces `⌊ξ αⁿ⌋ = rec2 a b 1 0 n - 1` at even `n` and `= rec2 a b 1 0 n` at odd `n`,
for *every* `n ≥ 0` — no threshold, no tail closure. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_sz_design"]
theorem floorNeg (h : Pair α β a b) (hβ : β < 0) (n : ℕ) :
    ⌊xiDesign α β * α ^ n⌋ = rec2 a b 1 0 n - (if n % 2 = 0 then 1 else 0) := by
  have hp := xiDesign'_pos h
  have hlt := xiDesign'_lt_one h hβ
  have hid : xiDesign α β * α ^ n + xiDesign' α β * β ^ n = (rec2 a b 1 0 n : ℝ) :=
    rec2_real h.sq_alpha h.sq_beta (xiDesign_seed₀ h) (xiDesign_seed₁ h) n
  set r : ℝ := xiDesign' α β * β ^ n with hr
  have hval : xiDesign α β * α ^ n = (rec2 a b 1 0 n : ℝ) - r := by linarith
  have hβ0 : β ≠ 0 := ne_of_lt hβ
  have habs : |r| < 1 := by
    rw [hr, abs_mul, abs_of_pos hp]
    calc xiDesign' α β * |β ^ n| ≤ xiDesign' α β * 1 :=
          mul_le_mul_of_nonneg_left (h.abs_pow_le n) hp.le
      _ = xiDesign' α β := by ring
      _ < 1 := hlt
  obtain ⟨hlo, hhi⟩ := abs_lt.mp habs
  rcases Nat.even_or_odd n with he | ho
  · have hn2 : n % 2 = 0 := Nat.even_iff.mp he
    have hpos : 0 < r := mul_pos hp (he.pow_pos hβ0)
    rw [hn2, ite_eq_left rfl, Int.floor_eq_iff]
    refine ⟨?_, ?_⟩ <;> push_cast <;> rw [hval] <;> linarith
  · have hn2 : n % 2 = 1 := Nat.odd_iff.mp ho
    have hneg : r < 0 := mul_neg_of_pos_of_neg hp (ho.pow_neg hβ)
    rw [hn2, ite_eq_right (by norm_num), sub_zero, Int.floor_eq_iff]
    refine ⟨?_, ?_⟩ <;> rw [hval] <;> linarith

/-- **Report §D.4 / plan Theorem C — designed total divisibility.**  If `m ∣ a` and
`m ∣ b - 1`, then every integral part `⌊ξ αⁿ⌋` of the closed-form `ξ = -β/(α-β)` is
divisible by `m`.  Compare [Dub06EO] Thm 6, which gives only `ε`-confinement of the
fractional parts, with an `ε`-dependent `ξ`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_d4_congruence"]
theorem dvd_floor_of_neg {m : ℤ} (h : Pair α β a b) (hβ : β < 0) (ha : m ∣ a)
    (hb : m ∣ (b - 1)) (n : ℕ) : m ∣ ⌊xiDesign α β * α ^ n⌋ := by
  rw [floorNeg h hβ n]
  exact rec2_dvd_sub (t₀ := (1 : ℤ)) (t₁ := (0 : ℤ)) ha hb n

/-- **The design.**  A real quadratic pair with a negative second conjugate, even `a` and
odd `b` puts `α` in `𝒵`, with the explicit witness `ξ = -β/(α-β)`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_d1_silver"]
theorem mem_MahlerZ_of_neg (h : Pair α β a b) (hβ : β < 0) (ha : Even a) (hb : ¬ Even b) :
    α ∈ MahlerZ := by
  refine ⟨h.one_lt, xiDesign α β, ne_of_gt (xiDesign_pos h hβ), fun n _ => ?_⟩
  have hb2 : (2 : ℤ) ∣ (b - 1) := by
    rcases Int.even_or_odd b with hbe | hbo
    · exact absurd hbe hb
    · obtain ⟨k, hk⟩ := hbo; exact ⟨k, by omega⟩
  obtain ⟨k, hk⟩ := dvd_floor_of_neg h hβ ha.two_dvd hb2 n
  exact ⟨k, by omega⟩

/-! ## The positive-conjugate cell ([Dub06EO] Theorem 1(iii))

Here no compensation is needed: the seeds `t₀ = 0`, `t₁ = 2` keep the entire integer
sequence even, and `βⁿ > 0` throughout, so the floor is that sequence outright — from the
first `n` at which `ξ' βⁿ < 1`.  Tail closure supplies the rest. -/

/-- **[Dub06EO] Theorem 1(iii), quadratic case.**  A real quadratic pair with a *positive*
second conjugate has `α ∈ 𝒵`, with the witness `ξ = 2/(α-β)`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_quadratic_classification"]
theorem mem_MahlerZ_of_pos (h : Pair α β a b) (hβ : 0 < β) : α ∈ MahlerZ := by
  have hd := h.sub_pos
  have hβ1 : β < 1 := h.beta_lt_one
  have hupos : 0 < 2 / (α - β) := div_pos two_pos hd
  have hid : ∀ n : ℕ, 2 / (α - β) * α ^ n + (-(2 / (α - β))) * β ^ n
      = (rec2 a b 0 2 n : ℝ) := by
    refine rec2_real h.sq_alpha h.sq_beta ?_ ?_
    · norm_num
    · have hne : (α - β) ≠ 0 := ne_of_gt hd
      push_cast
      field_simp
      ring
  obtain ⟨N, hN⟩ : ∃ N : ℕ, β ^ N < (α - β) / 2 := exists_pow_lt_of_lt_one (by linarith) hβ1
  refine mem_MahlerZ_of_floor_eq h.one_lt (ne_of_gt hupos) N (rec2 a b 0 2) ?_ ?_
  · exact fun n _ => rec2_even ⟨0, by ring⟩ ⟨1, by ring⟩ n
  · intro n hn
    have hbn : β ^ n ≤ β ^ N := (pow_le_pow_iff_right_of_lt_one₀ hβ hβ1).mpr hn
    have hbpos : 0 < β ^ n := pow_pos hβ n
    have hval : 2 / (α - β) * α ^ n = (rec2 a b 0 2 n : ℝ) + 2 / (α - β) * β ^ n := by
      have := hid n; linarith
    have hstep : 2 / (α - β) * β ^ n < 2 / (α - β) * ((α - β) / 2) :=
      mul_lt_mul_of_pos_left (by linarith) hupos
    have heq : 2 / (α - β) * ((α - β) / 2) = 1 := by field_simp
    have hrpos : 0 < 2 / (α - β) * β ^ n := mul_pos hupos hbpos
    rw [Int.floor_eq_iff]
    refine ⟨?_, ?_⟩ <;> rw [hval] <;> linarith

end SZ
