/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import RB.Rigidity
import B3.HeightVsRate
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The exponent ledger: the stammering→subspace route is closed (plan-B1E2, WP2)

The **negative mirror**, and the file whose only job is to stop a dead route from being
re-proposed. It makes [B1E2] §2.3's ledger a machine-checked theorem: the repetitions of
`RB.wmin` can *never* meet the index condition that a subspace attack needs.

## The ledger

| | constant | source |
|---|---|---|
| **ceiling** (what the word supplies) | `t/c ≤ log₂(3/2) = 0.5849…` | `RB.repetition_linear_bound` — 2-adic rigidity vs `(3/2)ᶜ` growth |
| **demand** (what a subspace attack needs) | `t/c > 1/log₂(3/2) = 1.7095…` | per-place product over `{∞,2,3}` |

## The gap is structural, not numerical

The two constants are **reciprocal** (`ceiling_mul_demand`), and `log₂(3/2) < 1` because
`3/2 < 2` (`ceiling_lt_one`).  Hence

  `ceiling < 1 < demand`   (`ceiling_lt_one`, `one_lt_demand`),

*always* — no arithmetic accident, no room for a sharper estimate to close it. The very
mechanism that makes the word complex (2-adic rigidity: a length-`t` repetition costs `2ᵗ ∣
x_c − x_a`, and the orbit only has `(3/2)ᶜ` room) is the mechanism that caps repetition
quality below `1`, while the attack needs quality above `1`.

This is the archimedean twin of `B3.ratInt_liouville_two_adic`: there the Liouville floor came
from an odd numerator, here from window rigidity — **coprimality, not an LTE valuation**, so it
owes nothing to plan-A5.

## Contents

* `RB.ceiling_lt_one`, `RB.one_lt_demand`, `RB.ceiling_mul_demand` — the structural statement.
* **`RB.not_demand`** — the integer ledger: no repetition has `t/c > 1.7095`.  Log-free.
* **`RB.not_indexConditionExpFreq`** — the wiring: for *every* family of repetitions with
  `c m → ∞`, `B3.IndexConditionExpFreq τ c t ε` fails, for every `τ > 1` and `ε > 0`.

## Scope: this is the ledger, not a rebuild of B3's approximants

`not_indexConditionExpFreq` takes the family `(a m, c m, t m)` of repetitions as given and reads
`c m` as the height exponent (base `3`) and `t m` as the approximation exponent (base `2`) —
which is exactly the shape of `B3.IndexConditionExpFreq`, and exactly the identification [B1E2]
§2.3 specifies (periodizing the digits at a repetition yields S-unit approximants of height
`≍ 3^c` and 2-adic quality `2^{-t}`).  The approximant construction itself is B3's column
(`B3.Approximants`, `B3.BlockApproximants`) and is not rebuilt here; the point of this file is
that **no** such construction can help, whatever its details, because the exponents do not fit.

## Do not re-propose the `p`-adic subspace pivot

"Switch from `p`-adic Mahler to the `p`-adic subspace theorem, as Adamczewski–Bugeaud did for
Loxton–van der Poorten" **is** the B3 route, and B3 died there (`B3.not_indexCondition_of_bounds`;
memory `phipoints-rate-anatomy`). A reviewer with full literature access independently
re-proposed it during this plan's Gate 0, which is why this file exists.

*Lead worth reading, not a route:* Capuano–Checcoli–Mula–Terracini, *If a machine did it, it is
probably transcendental (even p-adically)* (arXiv:2503.16330, Math. Z.) ports AB to `ℚ_p` via the
`p`-adic Subspace Theorem. Our exact-value framing differs from B3's rate-based one, so it is not
*automatically* dead — but the burden is on the reader to show it evades this ledger.

## References

* [B1E2] `plans/plan-B1E2.html` (rev. 2, 2026-07): §2.3 (the ledger), §0.1 (the reviewer's
  re-proposal), WP2.
* [AB07] Adamczewski, Bugeaud. *On the complexity of algebraic numbers I.* Ann. of Math. **165**
  (2007), 547–565.  (The stammering→subspace method this ledger closes off.)
* [BL96] Bernstein, Lagarias. (B3's companion ref; `B3.HeightVsRate`'s index condition.)
* [M4A3] `plans/plan-M4A3.html`: `TH.repetition_linear_bound`, the `24/41` certificate.
-/

namespace RB

/-! ## The two constants are reciprocal, and straddle `1` -/

/-- The **ceiling** constant `log₂(3/2) = 0.5849…` is `< 1` — simply because `3/2 < 2`. -/
@[category research solved, AMS 11 68, ref "B1E2", group "rb_rational_base"]
lemma ceiling_lt_one : Real.log (3 / 2) / Real.log 2 < 1 := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_lt_one h2]
  exact Real.log_lt_log (by norm_num) (by norm_num)

/-- The **demand** constant `1/log₂(3/2) = 1.7095…` is `> 1`. -/
@[category research solved, AMS 11 68, ref "B1E2", group "rb_rational_base"]
lemma one_lt_demand : 1 < Real.log 2 / Real.log (3 / 2) := by
  have h32 : (0 : ℝ) < Real.log (3 / 2) := Real.log_pos (by norm_num)
  rw [lt_div_iff₀ h32]
  simpa using Real.log_lt_log (by norm_num : (0 : ℝ) < 3 / 2) (by norm_num : (3 : ℝ) / 2 < 2)

/-- **The structural fact**: ceiling and demand are reciprocal.  With `ceiling_lt_one` this
forces `ceiling < 1 < demand` — the gap cannot be closed by any sharpening. -/
@[category research solved, AMS 11 68, ref "B1E2", group "rb_rational_base"]
lemma ceiling_mul_demand :
    (Real.log (3 / 2) / Real.log 2) * (Real.log 2 / Real.log (3 / 2)) = 1 := by
  have h1 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have h2 : Real.log (3 / 2) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp

/-! ## The integer ledger -/

/-- **The ledger, log-free** ([B1E2] §2.3): no repetition of `RB.wmin` meets the subspace demand
`t/c > 1.7095`.  Immediate from the ceiling `41t ≤ 24c + 40`: the two are incompatible already
for `c ≥ 1`, with room to spare (they force `c < 0.868`). -/
@[category research solved, AMS 11 68, ref "B1E2" "AB07", group "rb_rational_base"]
theorem not_demand {a c t : ℕ} (hac : a < c) (h : IsRepetition 1 a c t) :
    ¬ (17095 * c < 10000 * t) := by
  have hceil := repetition_linear_bound hac h
  omega

/-! ## The wiring to `B3`'s index condition -/

/-- **The dead route, as a theorem** ([B1E2] WP2): for every family of repetitions of `RB.wmin`
with positions `c m → ∞`, the index condition `B3.IndexConditionExpFreq τ c t ε` **fails**, for
every `τ > 1` and `ε > 0`.

Here `c m` is the height exponent (base `3`) and `t m` the approximation exponent (base `2`), as
in `B3.HeightVsRate`.  The proof is the ledger: the ceiling gives `t·log 2 < c·log 3` outright
once `c ≥ 3`, and `τ + ε > 1` only makes the demand worse — so the condition fails *eventually*,
which contradicts its `∃ᶠ` shape. -/
@[category research solved, AMS 11 68, ref "B1E2" "AB07" "BL96", group "rb_rational_base"]
theorem not_indexConditionExpFreq
    (a c t : ℕ → ℕ) (τ ε : ℝ) (hτ : 1 < τ) (hε : 0 < ε)
    (hac : ∀ m, a m < c m)
    (hrep : ∀ m, IsRepetition 1 (a m) (c m) (t m))
    (hgrow : Filter.Tendsto c Filter.atTop Filter.atTop) :
    ¬ B3.IndexConditionExpFreq τ c t ε := by
  intro hidx
  have hL2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hL3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have h23 : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  have hev : ∀ᶠ m in Filter.atTop, (t m : ℝ) * Real.log 2 < (τ + ε) * (c m : ℝ) * Real.log 3 := by
    filter_upwards [hgrow.eventually_ge_atTop 3] with m hm
    have hceil : 41 * t m ≤ 24 * c m + 40 := repetition_linear_bound (hac m) (hrep m)
    have hceilR : (41 : ℝ) * (t m : ℝ) ≤ 24 * (c m : ℝ) + 40 := by exact_mod_cast hceil
    have hcR : (3 : ℝ) ≤ (c m : ℝ) := by exact_mod_cast hm
    have hcpos : (0 : ℝ) < (c m : ℝ) := by linarith
    -- the ceiling already beats `log 3 / log 2`, before `τ` is even used
    have hstep : (t m : ℝ) * Real.log 2 < (c m : ℝ) * Real.log 3 := by
      nlinarith [hL2, hL3, h23, hceilR, hcR]
    have hcl : (0 : ℝ) < (c m : ℝ) * Real.log 3 := mul_pos hcpos hL3
    have hgt : (c m : ℝ) * Real.log 3 ≤ (τ + ε) * ((c m : ℝ) * Real.log 3) := by nlinarith [hcl]
    linarith [hstep, hgt]
  exact (hidx.and_eventually hev).exists.elim fun m hm => absurd hm.1 (not_le.mpr hm.2)

end RB
