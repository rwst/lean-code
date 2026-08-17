/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Habsieger's Padé construction for `‖(3/2)^k‖` — cited

The construction data of [Hab03], packaged as the **two independent integer forms** that an
elimination step consumes, with every analytic estimate replaced by an explicit rational-base
surrogate rounded in the direction that weakens the claim.

`Habsieger.PadeData m` is the bundle; `Habsieger.padeData` is the single axiom producing it.
Nothing here mentions a multiplier, a distance to the nearest integer, or a rate: this file
records the *construction*, not any consequence of it.

## What the source proves, and where

[Hab03], Acta Arith. **106**.3 (2003), 299–308.  Fix `α = 15/16`, an integer `m ≥ 2`, and put

> `n = [α(m − 3/2)] + 1 + η`,  `η ∈ {0,1}`  (p. 301)

so that the two candidate indices are `n₀ = [α(m − 3/2)] + 1` and `n₀ + 1`.  Let `Pᵢ, Qᵢ ∈ ℤ[t]`
of degree `≤ i` be the Padé numerator/denominator and `Eᵢ` the remainder, with

> `Pᵢ − Qᵢ·H = (−1)^{i+m} t^{2i+1} Eᵢ`  (2.1)
>
> `P_i Q_{i+1} − P_{i+1} Q_i = (−1)^{i+m} C(3m+i, 2i+m+1) · C(2i+m+2, i+m+1) · t^{2i+1}`  (2.5)
>
> **Lemma 1.**  `l ∈ Eᵢ(m) ⟹ {Pᵢ, Qᵢ} ⊂ l·ℤ[t]`; `Πᵢ = ∏_{l ∈ Eᵢ(m)} l` is squarefree, so
> `Πᵢ` divides the content of both.
>
> `|Qᵢ(−1/8)| ≤ e^{q₁m − q₀}`, `|Eᵢ(−1/8)| ≤ e^{e₁m − e₀}`  ((3.3), (3.4), (3.6); constants
> `q₁ = 1.7721197321`, `q₀ = 0.6711`, `e₁ = 2.3390368029`, `e₀ = 0.1084` printed on p. 308)
>
> `log Πᵢ(15/16) ≥ 0.3945·m + 9`  for `m ≥ 10 740 000`  (3.11)

All of these are `η`-uniform — they hold at both candidate indices with the printed constants,
because `n` carries `η` already; see `plans/note-Tshift-S1-constants.html` §2.1–2.2.

## How the displays become this bundle

Evaluate (2.1) at `t = −1/8`, put `P̂ⁱ = 8ⁱPᵢ(−1/8)`, `Q̂ⁱ = (−1)^m 8ⁱQᵢ(−1/8)` (integers,
divisible by `Πᵢ` by Lemma 1), clear by `8ⁱ·2^{6m}`, and eliminate `H` through its closed form

`H(2m, m; −1/8) = (−1)^m((3/2)^{6m} − W)`,  `W = ∑_{r<m} C(3m, r)·8^{m−r} ∈ ℤ`

(note §2.3).  With `aⁱ := P̂ⁱ + Q̂ⁱW` and `bⁱ := −Q̂ⁱ` this is exactly

`aⁱ·2^{6m} + bⁱ·3^{6m} = (−1)^{i+m+1}·2^{6m}·8^{−i−1}·Eᵢ(−1/8)`,  `|bⁱ| = 8ⁱ|Qᵢ(−1/8)|`

— the two-column form recorded below (note §2.4).  **`W` cancels out of everything downstream**:
it is absorbed into `aⁱ`, it drops out of the determinant, and the estimate that consumes this
bundle never reconstructs it.  So `W` appears in no statement of the corpus, here or later; the
plan's expectation that the `W`-link would be a separate Lean-proved identity is void, in the
harmless direction.

## The rational surrogates, and their direction

Every printed exponential is replaced by a rational base rounded *away* from the claim.  The
per-`m` bases carry ≥ 7 significant digits, because the bound is exponent-critical: the content
constant clears its break-even `0.394489710737` by only `1.03·10⁻⁵` per `m`, which is the entire
budget (note §3.2, §7).  Constants, being paid once, may be coarse.

| printed | recorded surrogate | direction | cost at `m = 10 740 000` |
|---|---|---|---|
| `Πᵢ ≥ e⁹·(e^{0.3945})^m` | `contentConst = 8103 ≤ e⁹`, `contentBase = 7516022/5065927 ≤ e^{0.3945}` | down | 1.43 nats |
| `\|Eᵢ(−1/8)\| ≤ e^{−0.1084}·(e^{2.3390368029})^m` | `e^{−e₀} ↦ 1`, `errorBase = 48489447/4675375 ≥ e^{2.3390368029}` | up | 0.11 nats |
| `\|Qᵢ(−1/8)\| ≤ e^{−0.6711}·(e^{1.7721197321})^m` | `denomConst = 639/1250 ≥ e^{−0.6711}`, `denomBase = 56534214/9609251 ≥ e^{1.7721197321}` | up | 1.2·10⁻⁴ nats |

`e₀` is dropped and `q₀` is kept, and that asymmetry is forced: `q₀` enters the constant
`A_c = −(57/32)log2 + 9 + q₀ = 8.4364` whose worst case `A_c + 5·A_d = 0.1708` is positive by a
hair, so dropping `q₀` would make the `δ = 5` case **false**; `e₀` enters only the correction row,
which is slack by 53 000 nats (note §3, §4).

With these surrogates the transported endgame retains `109.2` nats of margin at the threshold, at
`δ = 5` and `D = 5` — against the `110.5` nats the exact constants give.

## The threshold is `m > 10 740 000`, strictly

(3.11) is *stated* for `m ≥ 10 740 000`, but its proof splits at `m > 5·10¹⁰`,
`5·10¹⁰ ≥ m > 5·10⁷`, `5·10⁷ ≥ m > 1.074·10⁷`, so the single value `m = 10 740 000` lies outside
all three sub-ranges.  Rather than silently widen the axiom, `padeData` requires `mLow < m`.  The
cost is one date: the transported statement starts at `k = 64 440 001` instead of `64 440 000`.

## What this axiom does *not* say

* **Nothing about a multiplier.**  No `D` occurs in any statement of this file; the whole point of
  the plan is that the multiplier enters below the construction, at the elimination step.
* **Not the nonvanishing (3.1).**  Instead the bundle records the *value* of the determinant from
  (2.5), as a product of two binomial coefficients, and `PadeData.det_ne_zero` derives
  nonvanishing in Lean from `Nat.choose_pos`.  The recorded value is taken in absolute value, so
  no sign convention of (2.5) is asserted.
* **No `bⁱ ≠ 0`.**  The printed (4.2) divides by `Qₙ(−1/8)`, whose nonvanishing the source never
  establishes; the two-column route never divides by it (note §6.1), so the hypothesis is absent
  here and downstream.
* **Nothing about `‖(3/2)^k‖`.**  The rate, the `M`-absorption, and the endgame inequality are all
  proved, not cited.

## Trust ledger

One cited axiom, `Habsieger.padeData`, on the authority of [Hab03] (2.1), (2.5), Lemma 1,
(3.3)/(3.4)/(3.6), (3.11).  Everything else in the file is `std3`.

## Claim level

Cited.  The bundle is a faithful weakening of displayed, numbered, `D`-free content of a published
paper; each clause is independently checkable against `papers/Habsieger.pdf`, and every rounding
is recorded above with its direction and its cost.

## References

* [Hab03] L. Habsieger, *Explicit lower bounds for `‖(3/2)^k‖`*, Acta Arith. **106** (2003),
  299–308.  In repo: `papers/Habsieger.pdf`.
* [Beu81] F. Beukers, *Fractional parts of powers of rationals*, Math. Proc. Cambridge Philos.
  Soc. **90** (1981), 13–20 — the Padé construction [Hab03] refines.
* `plans/note-Tshift-S1-constants.html` — the constants audit this file freezes: §1 (the chain),
  §2.1–2.2 (`η`-uniformity), §2.4 (the two-column data and the determinant), §3 (the recomputed
  endgame), §7 (the surrogate table).
* `plans/plan-Tshift-S1.html` §3.2 — the axiom-interface design (option (iii)) and gate G‑C.
-/

namespace Habsieger

/-! ## 1. The frozen constants

Real numerals throughout, so that a consumer compares bases with `norm_num` and never meets
`Real.exp`. -/

/-- `≤ e^{0.3945}`, the base of the content bound (3.11).  Rounded **down**: `1.4836419869`
against `e^{0.3945} = 1.4836421843`. -/
noncomputable def contentBase : ℝ := 7516022 / 5065927

/-- `≤ e⁹ = 8103.0839`, the constant of (3.11). -/
def contentConst : ℝ := 8103

/-- `≥ e^{2.3390368029}`, the base of the remainder bound (3.4)/(3.6).  Rounded **up**:
`10.3712423068` against `e^{2.3390368029} = 10.3712421998`. -/
noncomputable def errorBase : ℝ := 48489447 / 4675375

/-- `≥ e^{1.7721197321}`, the base of the denominator bound (3.3)/(3.6).  Rounded **up**, but
only just: `5.88331119667911682` against `e^{1.7721197321} = 5.88331119667910889`, a relative
margin of `1.3·10⁻¹⁵`.  It is the sharpest of the three surrogates and the cheapest
(`1.2·10⁻⁴` nats at the threshold). -/
noncomputable def denomBase : ℝ := 56534214 / 9609251

/-- `≥ e^{−0.6711} = 0.5111460078`, the constant of (3.3)/(3.6).  This one may **not** be dropped:
see the module docstring. -/
noncomputable def denomConst : ℝ := 639 / 1250

/-- The threshold of (3.11), read strictly (`padeData` asks for `mLow < m`). -/
def mLow : ℕ := 10740000

/-- `Πᵢ ≥ contentBound m` — the content bound (3.11) with rational base. -/
noncomputable def contentBound (m : ℕ) : ℝ := contentConst * contentBase ^ m

/-- `|aⁱ·2^{6m} + bⁱ·3^{6m}| ≤ formBound m n` — the remainder bound, worst-cased over the two
candidate indices (the form at `n + 1` carries `8^{−n−2}`, which is smaller). -/
noncomputable def formBound (m n : ℕ) : ℝ := 2 ^ (6 * m) * errorBase ^ m / 8 ^ (n + 1)

/-- `|bⁱ| ≤ coeffBound m n` — the denominator bound, worst-cased over the two candidate indices
(the form at `n + 1` carries `8^{n+1}`). -/
noncomputable def coeffBound (m n : ℕ) : ℝ := 8 ^ (n + 1) * denomConst * denomBase ^ m

@[category API, AMS 11, ref "Hab03", group "tshift_s1"]
theorem contentBase_pos : 0 < contentBase := by rw [contentBase]; norm_num

@[category API, AMS 11, ref "Hab03", group "tshift_s1"]
theorem errorBase_pos : 0 < errorBase := by rw [errorBase]; norm_num

@[category API, AMS 11, ref "Hab03", group "tshift_s1"]
theorem denomBase_pos : 0 < denomBase := by rw [denomBase]; norm_num

@[category API, AMS 11, ref "Hab03", group "tshift_s1"]
theorem contentBound_pos (m : ℕ) : 0 < contentBound m := by
  rw [contentBound, contentConst]
  have := contentBase_pos
  positivity

@[category API, AMS 11, ref "Hab03", group "tshift_s1"]
theorem formBound_pos (m n : ℕ) : 0 < formBound m n := by
  rw [formBound]
  have := errorBase_pos
  positivity

@[category API, AMS 11, ref "Hab03", group "tshift_s1"]
theorem coeffBound_pos (m n : ℕ) : 0 < coeffBound m n := by
  rw [coeffBound, denomConst]
  have := denomBase_pos
  positivity

/-! ## 2. The bundle -/

/-- **The construction data of [Hab03] at parameter `m`**, in two-column form.

`n` is the smaller Padé index `[15/16·(m − 3/2)] + 1`; the two forms sit at `n` and `n + 1`, and
the range clauses are the `η`-inclusive range `15m/16 − 45/32 < n ≤ 15m/16 − 13/32` of p. 308,
cleared of denominators.

The two contents `Γ₁, Γ₂` are genuinely different integers: `Πᵢ` is built from `Eᵢ(m)`, which
depends on the index.  What (3.11) supplies for both is the common lower bound `contentBound m`. -/
structure PadeData (m : ℕ) where
  /-- The smaller Padé index. -/
  n : ℕ
  /-- `15m/16 − 45/32 < n`, cleared. -/
  n_lower : 30 * m < 32 * n + 45
  /-- `n ≤ 15m/16 − 13/32`, cleared. -/
  n_upper : 32 * n + 13 ≤ 30 * m
  /-- First coefficient of the form at index `n`. -/
  a₁ : ℤ
  /-- Second coefficient of the form at index `n`. -/
  b₁ : ℤ
  /-- Content of the form at index `n` (the paper's `Πₙ`). -/
  Γ₁ : ℤ
  /-- First coefficient of the form at index `n + 1`. -/
  a₂ : ℤ
  /-- Second coefficient of the form at index `n + 1`. -/
  b₂ : ℤ
  /-- Content of the form at index `n + 1`. -/
  Γ₂ : ℤ
  /-- (2.5): the determinant, in absolute value, as the printed product of binomial
  coefficients.  No sign is asserted. -/
  det_eq : |a₁ * b₂ - a₂ * b₁|
    = ((Nat.choose (3 * m + n) (2 * n + m + 1) * Nat.choose (2 * n + m + 2) (n + m + 1) : ℕ) : ℤ)
  /-- Lemma 1 at index `n`. -/
  dvd_a₁ : Γ₁ ∣ a₁
  /-- Lemma 1 at index `n`. -/
  dvd_b₁ : Γ₁ ∣ b₁
  /-- Lemma 1 at index `n + 1`. -/
  dvd_a₂ : Γ₂ ∣ a₂
  /-- Lemma 1 at index `n + 1`. -/
  dvd_b₂ : Γ₂ ∣ b₂
  /-- (3.11) at index `n`. -/
  content₁ : contentBound m ≤ (Γ₁ : ℝ)
  /-- (3.11) at index `n + 1`. -/
  content₂ : contentBound m ≤ (Γ₂ : ℝ)
  /-- (2.1) + (3.4)/(3.6) at index `n`. -/
  size₁ : |(a₁ : ℝ) * 2 ^ (6 * m) + (b₁ : ℝ) * 3 ^ (6 * m)| ≤ formBound m n
  /-- (2.1) + (3.4)/(3.6) at index `n + 1`. -/
  size₂ : |(a₂ : ℝ) * 2 ^ (6 * m) + (b₂ : ℝ) * 3 ^ (6 * m)| ≤ formBound m n
  /-- (3.3)/(3.6) at index `n`. -/
  coeff₁ : |(b₁ : ℝ)| ≤ coeffBound m n
  /-- (3.3)/(3.6) at index `n + 1`. -/
  coeff₂ : |(b₂ : ℝ)| ≤ coeffBound m n

/-- **The cited axiom.**  For every `m` beyond the threshold of (3.11), [Hab03]'s construction
supplies the bundle above.

Recorded on the authority of [Hab03] (2.1), (2.5), Lemma 1, (3.3)/(3.4)/(3.6), (3.11); the source
statements are quoted in the module docstring, together with every rounding and its direction.
One axiom, quantified over `m` — not a family. -/
@[category research solved, AMS 11, ref "Hab03", group "tshift_s1"]
axiom padeData (m : ℕ) (hm : mLow < m) : PadeData m

/-! ## 3. What Lean derives from the bundle

The independence certificate, which the source leaves as an opaque `≠ 0`. -/

namespace PadeData

variable {m : ℕ}

/-- The smaller index is below `m`: from `32n + 13 ≤ 30m`. -/
@[category API, AMS 11, ref "Hab03", group "tshift_s1"]
theorem n_lt (F : PadeData m) : F.n < m := by
  have h := F.n_upper
  omega

/-- **The two forms are independent.**  Both binomial coefficients of (2.5) are positive —
`2n + m + 1 ≤ 3m + n` because `n < m`, and `n + m + 1 ≤ 2n + m + 2` always — so the determinant
recorded by `det_eq` is a nonzero integer.  This is the clause the source states as the
nonvanishing (3.1); here it is proved. -/
@[category research solved, AMS 11, ref "Hab03", group "tshift_s1"]
theorem det_ne_zero (F : PadeData m) : F.a₁ * F.b₂ ≠ F.a₂ * F.b₁ := by
  have hn := F.n_lt
  have h1 : 0 < Nat.choose (3 * m + F.n) (2 * F.n + m + 1) :=
    Nat.choose_pos (by omega)
  have h2 : 0 < Nat.choose (2 * F.n + m + 2) (F.n + m + 1) :=
    Nat.choose_pos (by omega)
  have hpos : (0 : ℤ) < ((Nat.choose (3 * m + F.n) (2 * F.n + m + 1)
      * Nat.choose (2 * F.n + m + 2) (F.n + m + 1) : ℕ) : ℤ) := by
    exact_mod_cast Nat.mul_pos h1 h2
  have habs : |F.a₁ * F.b₂ - F.a₂ * F.b₁| ≠ 0 := by
    rw [F.det_eq]
    exact ne_of_gt hpos
  intro hcon
  exact habs (by rw [hcon, sub_self, abs_zero])

/-- The contents are positive, since `contentBound m` is. -/
@[category API, AMS 11, ref "Hab03", group "tshift_s1"]
theorem content₁_pos (F : PadeData m) : (0 : ℝ) < (F.Γ₁ : ℝ) :=
  lt_of_lt_of_le (contentBound_pos m) F.content₁

/-- The contents are positive, since `contentBound m` is. -/
@[category API, AMS 11, ref "Hab03", group "tshift_s1"]
theorem content₂_pos (F : PadeData m) : (0 : ℝ) < (F.Γ₂ : ℝ) :=
  lt_of_lt_of_le (contentBound_pos m) F.content₂

/-- The content bound in the absolute-value form an elimination step asks for. -/
@[category API, AMS 11, ref "Hab03", group "tshift_s1"]
theorem content₁_abs (F : PadeData m) : contentBound m ≤ |(F.Γ₁ : ℝ)| := by
  rw [abs_of_pos F.content₁_pos]
  exact F.content₁

/-- The content bound in the absolute-value form an elimination step asks for. -/
@[category API, AMS 11, ref "Hab03", group "tshift_s1"]
theorem content₂_abs (F : PadeData m) : contentBound m ≤ |(F.Γ₂ : ℝ)| := by
  rw [abs_of_pos F.content₂_pos]
  exact F.content₂

end PadeData

end Habsieger
