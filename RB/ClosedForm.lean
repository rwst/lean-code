/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import RB.Basic
import RB.Rigidity
import Mathlib.Algebra.Order.Round
import Mathlib.Tactic.LinearCombination
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The Odlyzko–Wilf closed form `xₙ = ⌊K(3/2)ⁿ⌋ — unconditionally

**`RB.closed_form`**: for every `x₀ > 0` and every `n`, `xₙ = ⌊K·(3/2)ⁿ⌋`.

No hypothesis on `K` — in particular **none on its rationality**.  This is [OW91] Cor. 1
(`D_k^{(3)} = ⌊K(3)(3/2)^k⌋`, the `p = 3` Josephus survivor sequence) and, independently,
[AFS08] Cor. 31 (`G_k = ⌊γ_{p/q}(p/q)^{k+1}⌋` whenever `p ≥ 2q−1`; at `(3,2)`, `3 ≥ 3` ✓).

## Why this file exists: it kills a recurring misreading

The closed form is repeatedly mis-stated in this repository's own notes as *open*, or as
*equivalent to* / *obstructed by* the rationality of `K`.  It is neither.  Two corrections
anchored here:

* **`plans/report-dubickas.html` §F.1** claimed "for `β = 3/2` (A061419) the existence of such
  `c` is open" and proposed proving a "closed form ⟺ confinement" equivalence.  The left side
  is `closed_form` — a theorem — so the equivalence is vacuous.
* **`plans/report-dubickas.html` §B.4** claimed *"any formula `xₙ = ⌊cβⁿ⌋` forces `w` eventually
  periodic"*.  That is **false**, and `closed_form` together with `RB.not_eventually_periodic`
  refutes it outright: the formula holds and the word is *not* eventually periodic.
* **`plans/plan-B2A2.html`** had the same misreading in its T1b motivation (corrected 2026-07-16).

What *is* open is the **irrationality of `K`** — E. T. H. Wang & P. C. Washburn, *Problem
E2604*, Amer. Math. Monthly **84** (1977), 821–822 (cf. OEIS A083286).  [OW91]'s own §5 remark
asks only for an *independent way to compute* `K(3)`, never for its rationality.

## The proof

`RB.Basic` already pins the orbit to the unit window `xₙ ≤ K(3/2)ⁿ ≤ xₙ + 1`.  Only the *upper*
end needs sharpening to strict, and exactly one thing can spoil it:

  `K(3/2)ⁿ − xₙ = (1/3)·Σ_{i≥0} w_{n+i}(2/3)ⁱ = 1`  ⟺  `w_{n+i} = 1` for **all** `i`,

since `Σᵢ(2/3)ⁱ = 3` is attained only by the all-`1` word.  And `RB.not_eventually_periodic`
([AFS08] Prop 26) forbids that: an eventually-all-`1` word is periodic with period `1`.

So the floor is exactly `xₙ`.  Formally the shift identity `K(xₙ) = K(x₀)·(3/2)ⁿ` (`K_shift`,
from `RB.wmin_add`'s shift-invariance) reduces every `n` to the case `n = 0`, i.e. to
`K(x₀) < x₀ + 1` (`K_lt_add_one`).

**Aperiodicity is doing the work.** The closed form is not an accident of `3/2`; it holds because
the carry word never gets stuck on `1`.

## Contents

* **`RB.exists_wmin_eq_zero`** — the word is never eventually all-`1`.
* **`RB.K_lt_add_one`** — `K(x₀) < x₀ + 1`, strictly.
* **`RB.K_shift`** — `K(xₙ) = K(x₀)·(3/2)ⁿ`.
* **`RB.closed_form`** — `⌊K(x₀)·(3/2)ⁿ⌋ = xₙ`.
* **`RB.closed_form_not_periodic`** — the refutation of §B.4's Method claim, packaged.

## References

* [OW91] A. M. Odlyzko, H. S. Wilf. *Functional iteration and the Josephus problem.* Glasgow
  Math. J. **33** (1991), 235–240.  (**Cor. 1** = this closed form at `p = 3`; §5 remark = the
  *computation* question, not a rationality question.  Local copy:
  `odlyzko-wilf-1991-josephus.pdf`.)
* [AFS08] Akiyama, Frougny, Sakarovitch. *Powers of rationals modulo 1 and rational base number
  systems.* Israel J. Math. **168** (2008), 53–91.  (**Cor. 31** = the independent second proof;
  Prop 26 = the aperiodicity this consumes.)
* [WW77] E. T. H. Wang, P. C. Washburn. *Problem E2604.* Amer. Math. Monthly **84** (1977),
  821–822.  (The genuinely open question: is `K` irrational?  OEIS A083286.)
* [B1E2] `plans/plan-B1E2.html` (rev. 2, 2026-07); `plans/report-dubickas.html` §F.1, §B.4;
  `plans/plan-B2A2.html` §2.4 — the notes this corrects.
-/

namespace RB

/-- The minimal word is **never eventually all-`1`**: otherwise it would be eventually periodic
with period `1`, contradicting `not_eventually_periodic` ([AFS08] Prop 26). -/
@[category research solved, AMS 11 68, ref "AFS08", group "rb_rational_base"]
theorem exists_wmin_eq_zero {x₀ : ℕ} (hx₀ : 0 < x₀) : ∃ j, wmin x₀ j = 0 := by
  by_contra h
  push Not at h
  refine not_eventually_periodic hx₀ ⟨0, 1, one_pos, fun n _ => ?_⟩
  have h1 := h (n + 1)
  have h2 := h n
  have b1 := wmin_le_one x₀ (n + 1)
  have b2 := wmin_le_one x₀ n
  omega

/-- **`K(x₀) < x₀ + 1`, strictly** — the sharpening of `RB.K_mul_pow_le` at `n = 0`.

`K(x₀) = x₀ + (1/3)Σⱼwⱼ(2/3)ʲ`, and `Σⱼwⱼ(2/3)ʲ < Σⱼ(2/3)ʲ = 3` because some letter is `0`
(`exists_wmin_eq_zero`).  This single strict inequality is what makes the floor come out right. -/
@[category research solved, AMS 11 68, ref "OW91" "AFS08", group "rb_rational_base"]
theorem K_lt_add_one {x₀ : ℕ} (hx₀ : 0 < x₀) : K x₀ < x₀ + 1 := by
  obtain ⟨j₀, hj₀⟩ := exists_wmin_eq_zero hx₀
  have hgeom : Summable (fun j : ℕ => (2 / 3 : ℝ) ^ j) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hlt : ∑' j, (2 / 3 : ℝ) ^ j * wmin x₀ j < ∑' j, (2 / 3 : ℝ) ^ j := by
    refine Summable.tsum_lt_tsum (i := j₀) (fun j => wmin_term_le x₀ j) ?_ (summable_wmin x₀) hgeom
    rw [hj₀]; simp
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at hlt
  norm_num at hlt
  unfold K
  linarith

/-- **The shift identity** `K(xₙ) = K(x₀)·(3/2)ⁿ`: running the constant from `xₙ` is running it
from `x₀` and rescaling.  Immediate from the shift-invariance `RB.wmin_add`. -/
@[category research solved, AMS 11 68, ref "AFS08", group "rb_rational_base"]
theorem K_shift (x₀ n : ℕ) : K (x x₀ n) = K x₀ * (3 / 2) ^ n := by
  have hs := summable_wmin x₀
  have hsplit := hs.sum_add_tsum_nat_add n
  have hx := x_mul_pow x₀ n
  have hshift : ∑' i, (2 / 3 : ℝ) ^ (i + n) * wmin x₀ (i + n)
      = (2 / 3 : ℝ) ^ n * ∑' i, (2 / 3 : ℝ) ^ i * wmin (x x₀ n) i := by
    rw [← tsum_mul_left]
    refine tsum_congr fun i => ?_
    rw [show i + n = n + i from Nat.add_comm i n, wmin_add, pow_add]
    ring
  have key : K x₀ = (2 / 3 : ℝ) ^ n * K (x x₀ n) := by
    unfold K
    rw [← hsplit]
    linear_combination (-1 : ℝ) * hx + (1 / 3 : ℝ) * hshift
  have hinv : ((2 : ℝ) / 3) ^ n * (3 / 2) ^ n = 1 := by rw [← mul_pow]; norm_num
  calc K (x x₀ n) = 1 * K (x x₀ n) := by ring
    _ = ((2 / 3 : ℝ) ^ n * (3 / 2) ^ n) * K (x x₀ n) := by rw [hinv]
    _ = ((2 / 3 : ℝ) ^ n * K (x x₀ n)) * (3 / 2) ^ n := by ring
    _ = K x₀ * (3 / 2) ^ n := by rw [← key]

/-- **The Odlyzko–Wilf closed form** ([OW91] Cor. 1; [AFS08] Cor. 31): `xₙ = ⌊K·(3/2)ⁿ⌋`.

**Unconditional** — no hypothesis on `K`, and in particular none on its rationality.  Anyone
who reads this closed form as open, or as equivalent to `K ∈ ℚ`, is misreading [OW91]; see the
module doc. -/
@[category research solved, AMS 11 68, ref "OW91" "AFS08", group "rb_rational_base"]
theorem closed_form {x₀ : ℕ} (hx₀ : 0 < x₀) (n : ℕ) :
    ⌊K x₀ * (3 / 2) ^ n⌋ = (x x₀ n : ℤ) := by
  rw [← K_shift]
  have hle : (x x₀ n : ℝ) ≤ K (x x₀ n) := by simpa using le_K (x x₀ n) 0
  have hlt : K (x x₀ n) < (x x₀ n : ℝ) + 1 := K_lt_add_one (x_pos hx₀ n)
  rw [Int.floor_eq_iff]
  exact ⟨by exact_mod_cast hle, by push_cast; exact hlt⟩

/-- **The refutation of `report-dubickas.html` §B.4's Method claim**, packaged: the closed form
`xₙ = ⌊K(3/2)ⁿ⌋` holds **and** the carry word is *not* eventually periodic.

So "any formula `xₙ = ⌊cβⁿ⌋` forces `w` eventually periodic" is false — the two coexist, and the
closed form is in fact *proved using* the aperiodicity (`K_lt_add_one`), not obstructed by it. -/
@[category research solved, AMS 11 68, ref "OW91" "AFS08", group "rb_rational_base"]
theorem closed_form_not_periodic {x₀ : ℕ} (hx₀ : 0 < x₀) :
    (∀ n, ⌊K x₀ * (3 / 2) ^ n⌋ = (x x₀ n : ℤ)) ∧
      ¬ ∃ N p, 0 < p ∧ ∀ n, N ≤ n → wmin x₀ (n + p) = wmin x₀ n :=
  ⟨closed_form hx₀, not_eventually_periodic hx₀⟩

/-! ## Sanity -/

/-- `x 1 = 1,2,3,5,8,…` really is `⌊K(3/2)ⁿ⌋` (A061419 vs A083286). -/
@[category test, AMS 11 68, ref "OW91", group "rb_rational_base"]
theorem closed_form_sanity :
    ⌊K 1 * (3 / 2) ^ 0⌋ = 1 ∧ ⌊K 1 * (3 / 2) ^ 4⌋ = 8 ∧ ⌊K 1 * (3 / 2) ^ 8⌋ = 41 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [closed_form one_pos] <;> rfl

end RB
