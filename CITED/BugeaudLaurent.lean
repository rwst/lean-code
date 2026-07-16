/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Bugeaud–Laurent's effective p-adic distance between two powers

Bugeaud and Laurent's theorem ([BL96p]): a sharp effective **lower bound for the p-adic
distance** `|α₁^{b₁} − α₂^{b₂}|_p` between two integral powers of algebraic numbers,
obtained by the interpolation-determinant (Schneider) method — the exact p-adic dual of
Laurent's archimedean two-log bound (`CITED/LaurentTwoLogs.lean`).  Equivalently it is an
**upper bound for the valuation** `v(α₁^{b₁} − α₂^{b₂}) = ord_p(α₁^{b₁} − α₂^{b₂})`.

This is the p-adic **two-log specialist**, and its shape mirrors the archimedean Laurent:
a `(log b')²` bound with a *tiny* constant.  Contrast the corpus's general p-adic engine
`CITED/YuPadicForms.lean` (Yu's [Yu07]), whose bound is **linear in `log B` with constant
`~10⁸`–`10¹⁰`**: at the flagship instance `(2, 3)` at `p = 3` (`D = 1`, `g = 1`) the
Bugeaud–Laurent essential constant is `≈ 24`, so the quadratic bound undercuts Yu's linear
one for every `b'` below `~10⁶` — a `~10⁷×` improvement in the two-log window.  Just as
Laurent (`17.9`) beats Baker–Wüstholz/Matveev at `n = 2` archimedean, Bugeaud–Laurent
beats Yu at `n = 2` p-adic.  (Yu remains the engine for `n ≥ 3`.)

This file transcribes the "acquire-later" gap **G-a** of `plan-formalize-logforms.html`
(§7), assessed 2026-07-11: the three fully-explicit corollaries of the paper's Theorem 1,
as cited axioms, plus a proved flagship instance.

## Statement conventions (the ℚ-specialization — the corpus's p-adic habitat)

Exactly the conventions of `CITED/YuPadicForms.lean`:

* **`K = ℚ`, `D = 1`, `𝔭 = p` a rational prime** (so `e = f = 1`, and `D = [ℚ(α₁,α₂):ℚ]/f
  = 1`).  The valuation `v` is the ordinary p-adic exponential valuation, transcribed as
  `padicValRat p : ℚ → ℤ`, cast to `ℝ`.  With `D = 1` the printed factor `D⁴` is `1`, the
  height denominators `log A_i ≥ max{h(αᵢ), log p / D}` become `max{h(αᵢ), log p}`, and
  `2Dh(αᵢ)`-type couplings collapse — see `logA`.  A stray `1/D` would silently strengthen
  the axiom; over `ℚ` there is none.
* **Bases `α₁, α₂ ∈ ℚ`** are non-zero **p-adic units** (`padicValRat p αᵢ = 0`, the
  hypothesis `hu₁`/`hu₂`) — the paper requires `αᵢ ∈ U_v`.  So this engine does **not**
  apply to `2^j − 3^q` (`3` is not a `3`-adic unit, and `ord_p(2^j − 3^q) = 0` anyway —
  that gap is archimedean, `CITED/RhinLogForm`/`CITED/EllisonsTheorem`).  Its live niche is
  **independent-exponent** two-term unit forms `α₁^{b₁} − α₂^{b₂}` with `b₁ ≠ b₂`, which
  the lifting-the-exponent lemma does *not* cover (LTE needs equal exponents `aⁿ − bⁿ`).
* **Exponents `b₁, b₂ ∈ ℕ`, positive**; the form is `Λ = α₁^{b₁} − α₂^{b₂} ∈ ℚ`, with
  `Λ ≠ 0` (else `v(Λ) = +∞`).
* **Height.**  `h(αᵢ) = Height.logHeight₁ (αᵢ)` (the log Weil height; for a rational,
  `log max(|num|, den)`, `Rat.logHeight₁_eq_log_max`) — the same primitive as
  `CITED/BakerWustholz`/`CITED/YuPadicForms`.  Over `ℚ` (`D = 1`) it *is* the normalized
  height `h`.
* **`b' = b₁/(D log A₂) + b₂/(D log A₁)`** with the **crossed indices** (as in Laurent),
  `D = 1`; see `bPrime`.
* **`g`** is the order of the unit part: the least `g ≥ 1` with `αᵢ^g` a principal unit
  (`αᵢ^g ≡ 1 mod p`); `g ∣ p^f − 1 = p − 1` over `ℚ`.  Corollary 1 majorizes `g ≤ p − 1`
  (removing `g` entirely); Corollary 2 is the sharpest case `g = 1` (`αᵢ` themselves
  principal, `hpr₁`/`hpr₂`).

## The three axioms (paper §2, corollaries of Theorem 1)

* `padicDist_lt` — **Corollary 1** ([BL96p], majorizing `g ≤ p^f − 1 = p − 1`): the g-free
  workhorse, constant `24 p (p−1)/((p−1)(log p)⁴) = 24 p/(log p)⁴` (`≤ 208` at `p = 2`).
* `padicDist_lt_principal` — **Corollary 2** ([BL96p], `g = 1`, `αᵢ ∈ U_v¹`): the sharpest,
  constant `24 p/((p−1)(log p)⁴)` (a further `(p−1)×`, e.g. `2×` at `p = 3`).
* `padicDist_lt_tuned` — **Theorem 4** ([BL96p], the `c(μ,ν)` table, `g`-free): the
  plateau-tuning knob, replacing the two `10`-coefficients by `(μ, ν)` from a fixed table
  (best essential constant `c = 18`), en route to the asymptotic `64/9 ≈ 7.1` of Theorem 2.

The parent **Theorem 3** (fully explicit, general `g`, constant `24 p g/((p−1)(log p)⁴)`)
interpolates between Corollaries 1 and 2 and is *not* separately transcribed — its two
printed corollaries bracket it, exactly as `LaurentTwoLogs` records the useful Table-1 rows
rather than the interior.  The asymptotic Theorem 2 (constant `64/9`, "sans utilité
pratique") is likewise doc-only.

## The flagship instance (proved)

`padicDist_two_three_five` discharges Corollary 1 for `α = (2, 3)` at the smallest prime
where **both** are units, `p = 5` (`D = 1`).  Here the `log p` floor **bites at both
bases** (`log 2, log 3 < log 5`), so `log A₁ = log A₂ = log 5` and `b' = (b₁ + b₂)/log 5`:
`v(2^{b₁} − 3^{b₂}) ≤ (24·5/(log 5)⁴)·(max{log b' + log log 5 + 0.4, 10 log 5, 10})²·(log 5)²`.

## References

* [BL96p] Y. Bugeaud, M. Laurent, "Minoration effective de la distance p-adique entre
  puissances de nombres algébriques." *J. Number Theory* **61** (1996), 311–342.  (Théorème
  1 §2, Corollaires 1–2 and Théorème 4, pp. 3–5; the p-adic analogue of [Lau94]/[LMN95],
  read in full 2026-07-11.)
* [Lau08]/[LMN95] the archimedean two-log siblings — `CITED/LaurentTwoLogs.lean`.
* [Yu07] the general p-adic engine (`n ≥ 3`) — `CITED/YuPadicForms.lean`.
* `plan-formalize-logforms.html` §7 gap G-a (this repository).
-/

namespace BugeaudLaurent

/-- Bugeaud–Laurent's p-adic clamped log-height `log Aᵢ = max{h(α), log p / D}`, over `ℚ`
(`D = 1`): `max{Height.logHeight₁ α, log p}`.  Two terms only (the archimedean Laurent has
three) — the p-adic method needs no `|log α|` term. -/
@[category API, AMS 11, ref "BL96p"]
noncomputable def logA (p : ℕ) (α : ℚ) : ℝ := max (Height.logHeight₁ α) (Real.log p)

/-- Bugeaud–Laurent's parameter `b' = b₁/(D log A₂) + b₂/(D log A₁)` over `ℚ` (`D = 1`) —
note the **crossed indices** (`b₁` with `log A₂`, `b₂` with `log A₁`). -/
@[category API, AMS 11, ref "BL96p"]
noncomputable def bPrime (b₁ b₂ : ℕ) (logA₁ logA₂ : ℝ) : ℝ :=
  (b₁ : ℝ) / logA₂ + (b₂ : ℝ) / logA₁

/-- The right-hand side of Bugeaud–Laurent's corollaries (over `ℚ`, `D = 1`):
`c · p · g / ((p−1)(log p)⁴) · (max{log b' + log log p + 0.4, μ log p, ν})² · log A₁ · log A₂`.
The `log b'` term is **squared**; `(μ, ν) = (10, 10)` for Corollaries 1–2, and `g = p − 1`
(Corollary 1, `g` majorized) or `g = 1` (Corollary 2). -/
@[category API, AMS 11, ref "BL96p"]
noncomputable def bound (c : ℝ) (p : ℕ) (g μ ν logA₁ logA₂ bp : ℝ) : ℝ :=
  c * (p : ℝ) * g / (((p : ℝ) - 1) * Real.log p ^ 4)
    * (max (Real.log bp + Real.log (Real.log p) + 0.4) (max (μ * Real.log p) ν)) ^ 2
    * logA₁ * logA₂

/-- The admissible `(μ, ν, c)` rows of [BL96p] Théorème 4 (the constant `c(μ,ν)` table for
`(μ, ν) ∈ {4,6,8,10,15} × {5,10}`).  The `(10, 10, 23.2)` row sharpens the round `24` of
Corollaries 1–2; `(15, 10, 18)` is the smallest essential constant in the table. -/
@[category API, AMS 11, ref "BL96p"]
def tableEntry (μ ν c : ℝ) : Prop :=
  (μ = 4 ∧ ν = 5 ∧ c = 53.8) ∨ (μ = 6 ∧ ν = 5 ∧ c = 36.1) ∨ (μ = 8 ∧ ν = 5 ∧ c = 28.1)
  ∨ (μ = 10 ∧ ν = 5 ∧ c = 24) ∨ (μ = 15 ∧ ν = 5 ∧ c = 18.6)
  ∨ (μ = 4 ∧ ν = 10 ∧ c = 51.7) ∨ (μ = 6 ∧ ν = 10 ∧ c = 34.8) ∨ (μ = 8 ∧ ν = 10 ∧ c = 27.3)
  ∨ (μ = 10 ∧ ν = 10 ∧ c = 23.2) ∨ (μ = 15 ∧ ν = 10 ∧ c = 18)

/-- **Bugeaud–Laurent, Corollary 1** ([BL96p], `g ≤ p^f − 1 = p − 1` majorized), the g-free
workhorse.  Let `α₁, α₂ ∈ ℚ` be non-zero **p-adic units** (`padicValRat p αᵢ = 0`),
multiplicatively independent; let `b₁, b₂` be positive integers with `Λ := α₁^{b₁} − α₂^{b₂}
≠ 0`.  Then, with `A₁, A₂, b'` the clamps above (`D = 1`),
`v(Λ) = ord_p(Λ) ≤ 24 p (p−1)/((p−1)(log p)⁴) · (max{log b' + log log p + 0.4, 10 log p,
10})² · log A₁ log A₂`.  Recorded as a cited `axiom` on the authority of [BL96p] — a p-adic
interpolation-determinant estimate we do not re-derive. -/
@[category research solved, AMS 11, ref "BL96p", group "bugeaud_laurent_padic"]
axiom padicDist_lt (p : ℕ) (hp : p.Prime)
    (α₁ α₂ : ℚ) (hα₁ : α₁ ≠ 0) (hα₂ : α₂ ≠ 0)
    (hu₁ : padicValRat p α₁ = 0) (hu₂ : padicValRat p α₂ = 0)
    (hindep : ∀ m n : ℤ, α₁ ^ m * α₂ ^ n = 1 → m = 0 ∧ n = 0)
    (b₁ b₂ : ℕ) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hΛ : α₁ ^ b₁ - α₂ ^ b₂ ≠ 0) :
    ((padicValRat p (α₁ ^ b₁ - α₂ ^ b₂) : ℤ) : ℝ)
      ≤ bound 24 p ((p : ℝ) - 1) 10 10 (logA p α₁) (logA p α₂)
          (bPrime b₁ b₂ (logA p α₁) (logA p α₂))

/-- **Bugeaud–Laurent, Corollary 2** ([BL96p], `g = 1`), the sharpest case: `α₁, α₂` are
**principal units** (`αᵢ ≡ 1 mod p`, i.e. `0 < padicValRat p (αᵢ − 1)`).  Same shape with
`g = 1`, so the constant is `24 p/((p−1)(log p)⁴)` (`≤ 208 D⁴(…)²…` at `p = 2`) — a further
`(p−1)×` sharper than Corollary 1. -/
@[category research solved, AMS 11, ref "BL96p", group "bugeaud_laurent_padic"]
axiom padicDist_lt_principal (p : ℕ) (hp : p.Prime)
    (α₁ α₂ : ℚ) (hα₁ : α₁ ≠ 0) (hα₂ : α₂ ≠ 0)
    (hu₁ : padicValRat p α₁ = 0) (hu₂ : padicValRat p α₂ = 0)
    (hpr₁ : 0 < padicValRat p (α₁ - 1)) (hpr₂ : 0 < padicValRat p (α₂ - 1))
    (hindep : ∀ m n : ℤ, α₁ ^ m * α₂ ^ n = 1 → m = 0 ∧ n = 0)
    (b₁ b₂ : ℕ) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hΛ : α₁ ^ b₁ - α₂ ^ b₂ ≠ 0) :
    ((padicValRat p (α₁ ^ b₁ - α₂ ^ b₂) : ℤ) : ℝ)
      ≤ bound 24 p 1 10 10 (logA p α₁) (logA p α₂)
          (bPrime b₁ b₂ (logA p α₁) (logA p α₂))

/-- **Bugeaud–Laurent, Théorème 4** ([BL96p], the `c(μ,ν)` table, `g ≤ p − 1` majorized):
the plateau-tuning refinement of Corollary 1.  For any admissible row `tableEntry μ ν c`,
`v(Λ) ≤ c p (p−1)/((p−1)(log p)⁴) · (max{log b' + log log p + 0.4, μ log p, ν})² · log A₁
log A₂`.  Choosing `(μ, ν) = (15, 10)` gives the smallest essential constant `c = 18`. -/
@[category research solved, AMS 11, ref "BL96p", group "bugeaud_laurent_padic"]
axiom padicDist_lt_tuned (p : ℕ) (hp : p.Prime)
    (α₁ α₂ : ℚ) (hα₁ : α₁ ≠ 0) (hα₂ : α₂ ≠ 0)
    (hu₁ : padicValRat p α₁ = 0) (hu₂ : padicValRat p α₂ = 0)
    (hindep : ∀ m n : ℤ, α₁ ^ m * α₂ ^ n = 1 → m = 0 ∧ n = 0)
    (μ ν c : ℝ) (hc : tableEntry μ ν c)
    (b₁ b₂ : ℕ) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hΛ : α₁ ^ b₁ - α₂ ^ b₂ ≠ 0) :
    ((padicValRat p (α₁ ^ b₁ - α₂ ^ b₂) : ℤ) : ℝ)
      ≤ bound c p ((p : ℝ) - 1) μ ν (logA p α₁) (logA p α₂)
          (bPrime b₁ b₂ (logA p α₁) (logA p α₂))

/-- `2` and `3` are multiplicatively independent in `ℚ`: `2ᵐ·3ⁿ = 1 → m = n = 0` (read off
the `2`- and `3`-adic valuations).  Discharges the `hindep` side condition. -/
@[category API, AMS 11, ref "BL96p", group "bugeaud_laurent_padic"]
theorem mulIndep_two_three :
    ∀ m n : ℤ, (2 : ℚ) ^ m * (3 : ℚ) ^ n = 1 → m = 0 ∧ n = 0 := by
  have hf2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf3 : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hzp : ∀ (p : ℕ) [Fact (Nat.Prime p)] (q : ℚ), q ≠ 0 → ∀ k : ℤ,
      padicValRat p (q ^ k) = k * padicValRat p q := by
    intro p _ q hq0 k
    obtain ⟨j, rfl | rfl⟩ := Int.eq_nat_or_neg k
    · rw [zpow_natCast, padicValRat.pow _]
    · rw [zpow_neg, zpow_natCast, padicValRat.inv, padicValRat.pow _]; ring
  have v22 : padicValRat 2 (2 : ℚ) = 1 := by
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num]; exact padicValRat.self (by norm_num)
  have v23 : padicValRat 2 (3 : ℚ) = 0 := by
    rw [show (3 : ℚ) = ((3 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]
    simp [padicValNat.eq_zero_of_not_dvd (by decide : ¬ (2 : ℕ) ∣ 3)]
  have v33 : padicValRat 3 (3 : ℚ) = 1 := by
    rw [show (3 : ℚ) = ((3 : ℕ) : ℚ) by norm_num]; exact padicValRat.self (by norm_num)
  have v32 : padicValRat 3 (2 : ℚ) = 0 := by
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]
    simp [padicValNat.eq_zero_of_not_dvd (by decide : ¬ (3 : ℕ) ∣ 2)]
  intro m n hmn
  refine ⟨?_, ?_⟩
  · have h2 := congrArg (padicValRat 2) hmn
    rw [padicValRat.mul (by positivity) (by positivity), hzp 2 (2 : ℚ) (by norm_num) m,
        hzp 2 (3 : ℚ) (by norm_num) n, v22, v23] at h2
    simp at h2; omega
  · have h3 := congrArg (padicValRat 3) hmn
    rw [padicValRat.mul (by positivity) (by positivity), hzp 3 (2 : ℚ) (by norm_num) m,
        hzp 3 (3 : ℚ) (by norm_num) n, v32, v33] at h3
    simp at h3; omega

/-- The `log p` floor **bites at `α = 2`**: `logA 5 2 = max{log 2, log 5} = log 5`
(`log 2 < log 5`). -/
@[category API, AMS 11, ref "BL96p", group "bugeaud_laurent_padic"]
theorem logA_five_two : logA 5 (2 : ℚ) = Real.log 5 := by
  rw [logA, Rat.logHeight₁_eq_log_max, show ((5 : ℕ) : ℝ) = (5 : ℝ) by norm_num]
  norm_num
  exact Real.log_le_log (by norm_num) (by norm_num)

/-- Likewise `logA 5 3 = max{log 3, log 5} = log 5` (`log 3 < log 5`). -/
@[category API, AMS 11, ref "BL96p", group "bugeaud_laurent_padic"]
theorem logA_five_three : logA 5 (3 : ℚ) = Real.log 5 := by
  rw [logA, Rat.logHeight₁_eq_log_max, show ((5 : ℕ) : ℝ) = (5 : ℝ) by norm_num]
  norm_num
  exact Real.log_le_log (by norm_num) (by norm_num)

/-- **The flagship instance** ([BL96p] Corollary 1 at `α = (2, 3)`, `p = 5`, `D = 1`).  With
the `log p` floor biting at both bases (`log A₁ = log A₂ = log 5`, `b' = (b₁ + b₂)/log 5`),
for positive integers `b₁, b₂` with `2^{b₁} ≠ 3^{b₂}`,
`ord₅(2^{b₁} − 3^{b₂}) ≤ (24·5/(log 5)⁴)·(max{log((b₁+b₂)/log 5) + log log 5 + 0.4, 10 log 5,
10})²·(log 5)²`.  Proved by discharging the side conditions of `padicDist_lt`. -/
@[category research solved, AMS 11, ref "BL96p", group "bugeaud_laurent_padic"]
theorem padicDist_two_three_five (b₁ b₂ : ℕ) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hΛ : (2 : ℚ) ^ b₁ - 3 ^ b₂ ≠ 0) :
    ((padicValRat 5 ((2 : ℚ) ^ b₁ - 3 ^ b₂) : ℤ) : ℝ)
      ≤ 24 * 5 / Real.log 5 ^ 4
          * (max (Real.log ((b₁ : ℝ) / Real.log 5 + (b₂ : ℝ) / Real.log 5)
                    + Real.log (Real.log 5) + 0.4) (max (10 * Real.log 5) 10)) ^ 2
          * Real.log 5 ^ 2 := by
  have hu2 : padicValRat 5 (2 : ℚ) = 0 := by
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]
    simp [padicValNat.eq_zero_of_not_dvd (by decide : ¬ (5 : ℕ) ∣ 2)]
  have hu3 : padicValRat 5 (3 : ℚ) = 0 := by
    rw [show (3 : ℚ) = ((3 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]
    simp [padicValNat.eq_zero_of_not_dvd (by decide : ¬ (5 : ℕ) ∣ 3)]
  have key := padicDist_lt 5 (by decide) 2 3 (by norm_num) (by norm_num) hu2 hu3
    mulIndep_two_three b₁ b₂ hb₁ hb₂ hΛ
  rw [logA_five_two, logA_five_three] at key
  simp only [bPrime, bound, Nat.cast_ofNat] at key
  have hlog5 : Real.log 5 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  refine key.trans_eq ?_
  field_simp

end BugeaudLaurent
