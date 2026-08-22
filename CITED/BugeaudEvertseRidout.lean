/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Field
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The quantitative Ridout theorem of Bugeaud–Evertse (2008), Cor. 5.2 — cited

The **line cover** produced by the quantitative Subspace Theorem: for a fixed exponent budget
`2 + ε` distributed over the archimedean place and finitely many primes, all *high* solutions of
the associated approximation system lie on an explicitly bounded number of lines through the
origin.

## The source statement, verbatim

[BE08], §5, pp. 8–9.  Let `S₁, S₂` be finite, possibly empty sets of primes, `S := {∞} ∪ S₁ ∪ S₂`,
let `ξ` be an algebraic number of degree `d`, let `ε > 0`, and let `f_p` (`p ∈ S`) be reals with

> `f_p ≥ 0` for `p ∈ S`, `∑_{p ∈ S} f_p = 2 + ε`.  (5.10)

Consider the system of inequalities

> `|ξ − x/y| ≤ y^{−f_∞}`, `|x|_p ≤ y^{−f_p}` (`p ∈ S₁`), `|y|_p ≤ y^{−f_p}` (`p ∈ S₂`),
> in `(x, y) ∈ ℤ²` with `y > 0`.  (5.11)

Define the height of `ξ` by `H(ξ) := ∏_{v ∈ M_K} max(1, ‖ξ‖_v)`.

> **Corollary 5.2.** *The set of solutions of (5.11) with*
> `y > max(2H(ξ), 2^{4/ε})`  (5.12)
> *is contained in the union of at most*
> `2³²(1 + ε⁻¹)³ log(6d) log((1 + ε⁻¹) log(6d))`  (5.13)
> *one-dimensional linear subspaces of ℚ².*

Two features of the source are load-bearing and are reproduced below without weakening:

* the conclusion counts **one-dimensional subspaces** (lines), *not* solutions — [BE08] contains
  no per-line multiplicity statement anywhere, and Theorem 5.1 behind it has the same shape;
* the conclusion is restricted to **large height** `y > max(2H(ξ), 2^{4/ε})`; solutions below the
  threshold are not covered at all.

## What is recorded here

`ridout_line_cover` is Cor. 5.2 at `d = 1` (so `ξ ∈ ℚ` and `log(6d) = log 6`) and **arbitrary
finite sets of primes** `S₁`, `S₂`, as in the source.  A one-dimensional subspace of `ℚ²` meeting
the region `y > 0` is determined by the slope `x/y ∈ ℚ` of any of its points, so the line cover is
recorded as a `Finset ℚ` of slopes of cardinality at most `lineBound ε`.  Varying the sets and the
exponents `f_p` inside the budget `2 + ε` is what lets one axiom serve every frame in the corpus.

Two readings of the source have to be pinned down, and both are resolved *against* the axiom (the
recorded statement is the weaker one in each case):

* the budget (5.10) sums over `S = {∞} ∪ S₁ ∪ S₂`, i.e. over the **union** — a prime in both sets
  would contribute once;
* the deduction of Cor. 5.2 from Thm 5.1 on p. 9 sets `e₁ₚ = −f_p, e₂ₚ = 0` for `p ∈ S₁` and
  `e₁ₚ = 0, e₂ₚ = −f_p` for `p ∈ S₂`, which is consistent only for **disjoint** `S₁`, `S₂`.  The
  axiom therefore carries `Disjoint S₁ S₂` as a hypothesis.  Every application has it for free:
  `S₁` is the set of primes of the denominator base and `S₂` that of the numerator base, and the
  two bases are coprime.

Two derived forms are provided, and are what consumers use:

* `ridout_line_cover_23` — the instance `S₁ = {2}`, `S₂ = {3}` of the `‖(3/2)ⁿ‖` problems;
* `ridout_line_cover_pow` — the **coprime-power engine**: for coprime `P, Q` it packages the whole
  per-prime bookkeeping into the two hypotheses `Qⁿ ∣ x` and `y = Pⁿ`, with the budget in the
  closed form `f_∞ + log Q/log P + 1 = 2 + ε`.  This is the form the general effective Mahler
  line-count of `BB13/MahlerFrame.lean` runs on.

## Widening notice (2026-07-22)

Until 2026-07-22 the recorded axiom was the narrow instance now called `ridout_line_cover_23`
(`S₁ = {2}`, `S₂ = {3}`).  It was replaced by the source's own generality — the same theorem, cited
less narrowly — and the narrow form derived from it, so no footprint changed.  The gain is the
general effective Mahler line count of `BB13/MahlerFrame.lean` (report C.8) and rational
multipliers (C.9); see `plans/plan-BB13-generalize.html`.

## Retirement notice (2026-07-21)

This file **replaces** `CITED/CorvajaZannierEffective.lean`, whose axiom
`CZ.pseudoPisot_approx_effective` asserted a bound on the *number of solutions*,
`#A(δ, ε) ≤ (|num δ| + den δ) · K(ε)`.  That statement is **not** Cor. 5.2: passing from the line
count to a solution count needs a uniform bound on the number of solutions per line, which is the
open problem [BE08] itself flags (Remark 7.4) and which Corvaja–Zannier's *ineffective* finiteness
cannot supply.  Under the house policy on cited axioms (literature-proved statements only, never
open ones) it was deleted, together with its consumers' count corollaries; the repaired counts are
conditional on an explicit per-line hypothesis (`BB13/FailureCount.lean`).  See
`plans/plan2-BB13.html`, and `plans/report-BB13.md`, `plans/report2-BB13.md` for the two referee
reports that identified the error.

## References

* [BE08] Y. Bugeaud, J.-H. Evertse, *On two notions of complexity of algebraic numbers*, Acta
  Arith. **133** (2008), 221–250 — Thm 5.1 ((5.7)–(5.9)) and Cor. 5.2 ((5.10)–(5.13)).
* [ES02] J.-H. Evertse, H. P. Schlickewei, *A quantitative version of the Absolute Subspace
  Theorem*, J. reine angew. Math. **548** (2002), 21–127 — the engine behind Thm 5.1.
* [Rid57] D. Ridout, *The p-adic generalization of the Thue–Siegel–Roth theorem*, Mathematika **4**
  (1957), 125–131 — the qualitative ancestor (`CITED/Ridout.lean`).
-/

namespace BugeaudEvertse

open scoped Real

/-- The Bugeaud–Evertse line count (5.13) at degree `d = 1`:
`⌈2³²(1 + ε⁻¹)³ · log 6 · log((1 + ε⁻¹) · log 6)⌉`.

At the sharp exponent `ε* = log(4/3)/log 3` of Bugeaud's Problem 10.13 this is
`1 856 360 182 227 < 1.86 · 10¹²`. -/
noncomputable def lineBound (ε : ℝ) : ℕ :=
  ⌈(2 : ℝ) ^ 32 * (1 + ε⁻¹) ^ 3 * Real.log 6 * Real.log ((1 + ε⁻¹) * Real.log 6)⌉₊

/-- The height `H(ξ) = ∏_v max(1, ‖ξ‖_v)` of a rational number: `max(|num ξ|, den ξ)`. -/
def ratHeight (ξ : ℚ) : ℕ := max ξ.num.natAbs ξ.den

@[category API, AMS 11, ref "BE08", group "bugeaud_10_13"]
theorem ratHeight_one : ratHeight 1 = 1 := by decide

/-- **Quantitative Ridout** ([BE08], Cor. 5.2), the instance `d = 1` (`ξ ∈ ℚ`) with arbitrary
finite sets of primes `S₁`, `S₂`: for exponents `fInf ≥ 0` and `f l ≥ 0` (`l ∈ S₁ ∪ S₂`) with
`fInf + ∑_{l ∈ S₁ ∪ S₂} f l = 2 + ε` — the source's (5.10) — there is a set `R` of at most
`lineBound ε` slopes such that **every** solution `(x, y) ∈ ℤ²`, `y > 0`, of the system (5.11)

* `|ξ − x/y| ≤ y^{−fInf}`,
* `|x|_l ≤ y^{−f l}` for `l ∈ S₁`,
* `|y|_l ≤ y^{−f l}` for `l ∈ S₂`

whose height satisfies (5.12), `y > max(2H(ξ), 2^{4/ε})`, has `x/y ∈ R` — i.e. lies on one of at
most `lineBound ε` lines through the origin.

Recorded as a cited `axiom` on the authority of [BE08] Cor. 5.2 (via [ES02]); the source statement
is quoted verbatim in the module docstring, and the two readings it leaves open are resolved
against the axiom there (sum over the union; `Disjoint S₁ S₂`).  Note what is **not** asserted:
nothing bounds the number of solutions on a single line, and nothing is said about solutions of
height below the threshold. -/
@[category research solved, AMS 11, ref "BE08" "ES02", group "bugeaud_10_13"]
axiom ridout_line_cover (ξ : ℚ) (ε fInf : ℝ) (S₁ S₂ : Finset ℕ) (f : ℕ → ℝ)
    (hS₁ : ∀ l ∈ S₁, l.Prime) (hS₂ : ∀ l ∈ S₂, l.Prime) (hdisj : Disjoint S₁ S₂)
    (hε : 0 < ε) (hInf : 0 ≤ fInf) (hf : ∀ l ∈ S₁ ∪ S₂, 0 ≤ f l)
    (hsum : fInf + ∑ l ∈ S₁ ∪ S₂, f l = 2 + ε) :
    ∃ R : Finset ℚ, R.card ≤ lineBound ε ∧
      ∀ x y : ℤ, 0 < y →
        max (2 * (ratHeight ξ : ℝ)) ((2 : ℝ) ^ ((4 : ℝ) / ε)) < (y : ℝ) →
        |(ξ : ℝ) - (x : ℝ) / (y : ℝ)| ≤ (y : ℝ) ^ (-fInf) →
        (∀ l ∈ S₁, ((padicNorm l (x : ℚ) : ℚ) : ℝ) ≤ (y : ℝ) ^ (-f l)) →
        (∀ l ∈ S₂, ((padicNorm l (y : ℚ) : ℚ) : ℝ) ≤ (y : ℝ) ^ (-f l)) →
        (x : ℚ) / (y : ℚ) ∈ R

/-! ### The two-prime instance `S₁ = {2}`, `S₂ = {3}` -/

/-- **Quantitative Ridout at `S₁ = {2}`, `S₂ = {3}`** — the frame of the `‖(3/2)ⁿ‖` problems
(`BB13/LineCover.lean`, `BB13/Waring.lean`, `BB13/SpanStrata.lean`), where the exponent budget
`2 + ε` is split as `fInf` at the infinite place, `f₂` at `2` and `f₃` at `3`.

Derived from `ridout_line_cover`; it was itself the recorded axiom until 2026-07-22, when the
axiom was widened to the generality of the source. -/
@[category research solved, AMS 11, ref "BE08" "ES02", group "bugeaud_10_13"]
theorem ridout_line_cover_23 (ξ : ℚ) (ε fInf f₂ f₃ : ℝ) (hε : 0 < ε)
    (hInf : 0 ≤ fInf) (h₂ : 0 ≤ f₂) (h₃ : 0 ≤ f₃) (hsum : fInf + f₂ + f₃ = 2 + ε) :
    ∃ R : Finset ℚ, R.card ≤ lineBound ε ∧
      ∀ x y : ℤ, 0 < y →
        max (2 * (ratHeight ξ : ℝ)) ((2 : ℝ) ^ ((4 : ℝ) / ε)) < (y : ℝ) →
        |(ξ : ℝ) - (x : ℝ) / (y : ℝ)| ≤ (y : ℝ) ^ (-fInf) →
        ((padicNorm 2 (x : ℚ) : ℚ) : ℝ) ≤ (y : ℝ) ^ (-f₂) →
        ((padicNorm 3 (y : ℚ) : ℚ) : ℝ) ≤ (y : ℝ) ^ (-f₃) →
        (x : ℚ) / (y : ℚ) ∈ R := by
  have hsum' : fInf + ∑ l ∈ ({2} : Finset ℕ) ∪ {3}, (fun l => if l = 2 then f₂ else f₃) l
      = 2 + ε := by
    rw [show ({2} : Finset ℕ) ∪ {3} = {2, 3} from rfl,
      Finset.sum_pair (by norm_num : (2 : ℕ) ≠ 3)]
    show fInf + ((if (2 : ℕ) = 2 then f₂ else f₃) + (if (3 : ℕ) = 2 then f₂ else f₃)) = 2 + ε
    rw [ite_eq_left rfl, ite_eq_right (by norm_num : ¬((3 : ℕ) = 2))]
    linarith
  obtain ⟨R, hcard, hR⟩ := ridout_line_cover ξ ε fInf {2} {3}
    (fun l => if l = 2 then f₂ else f₃)
    (by simpa using Nat.prime_two) (by simpa using Nat.prime_three) (by decide) hε hInf
    (by intro l hl; simp only [Finset.mem_union, Finset.mem_singleton] at hl
        rcases hl with rfl | rfl
        · simpa using h₂
        · simpa using h₃)
    hsum'
  exact ⟨R, hcard, fun x y hy hht harch h2 h3 =>
    hR x y hy hht harch (by simpa using h2) (by simpa using h3)⟩

/-! ### The coprime-power engine

The form every application of the corpus actually needs: the solutions have `y = Pⁿ` and `x`
divisible by `Qⁿ` for coprime bases `P, Q`, and the per-prime exponents are then forced —
`v_l(Q)·log l/log P` on the primes of `Q` and `v_l(P)·log l/log P` on those of `P`, with sums
`log Q/log P` and `1`.  The lemmas below do that bookkeeping once and for all. -/

/-- `log n = ∑_{l ∣ n} v_l(n)·log l`: the prime factorization, logarithmed.  What turns the
per-prime exponent budget (5.10) into the closed form `log Q/log P + 1`. -/
@[category API, AMS 11, ref "BE08", group "bugeaud_10_13"]
theorem log_eq_sum_factorization {n : ℕ} (hn : n ≠ 0) :
    Real.log n = ∑ l ∈ n.primeFactors, (n.factorization l : ℝ) * Real.log l := by
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod, Nat.support_factorization]
  push_cast
  rw [Real.log_prod (fun l hl => by
    have := Nat.pos_of_mem_primeFactors hl
    positivity)]
  exact Finset.sum_congr rfl fun l _ => Real.log_pow _ _

/-- `(Pⁿ)^{−e·log b/log P} = b^{−e·n}`: the change of base that reads a `y`-exponent as a power of
the prime it lives at.  The general form of `BB13.rpow_neg_theta`. -/
@[category API, AMS 11, ref "BE08", group "bugeaud_10_13"]
theorem rpow_pow_logRatio {P : ℕ} (hP : 1 < P) {b : ℝ} (hb : 0 < b) (e : ℝ) (n : ℕ) :
    ((P : ℝ) ^ n) ^ (-(e * Real.log b / Real.log P)) = b ^ (-(e * n)) := by
  have hP0 : (0 : ℝ) < P := by positivity
  have hP1 : (1 : ℝ) < P := by exact_mod_cast hP
  have hlP : Real.log P ≠ 0 := ne_of_gt (Real.log_pos hP1)
  rw [← Real.rpow_natCast (P : ℝ) n, ← Real.rpow_mul hP0.le, Real.rpow_def_of_pos hP0,
    Real.rpow_def_of_pos hb]
  congr 1
  field_simp

/-- `lᵐ ∣ x → |x|_l ≤ l^{−m}`: `padicNorm.dvd_iff_norm_le`, cast into `ℝ` with a real exponent. -/
@[category API, AMS 11, ref "BE08", group "bugeaud_10_13"]
theorem padicNorm_le_of_dvd_pow {l : ℕ} (hl : l.Prime) {x : ℤ} {m : ℕ} (hdvd : (l : ℤ) ^ m ∣ x) :
    ((padicNorm l (x : ℚ) : ℚ) : ℝ) ≤ (l : ℝ) ^ (-(m : ℝ)) := by
  have : Fact l.Prime := ⟨hl⟩
  have h : ((l ^ m : ℕ) : ℤ) ∣ x := by push_cast; exact hdvd
  have hcast : (((l : ℚ) ^ (-(m : ℤ)) : ℚ) : ℝ) = (l : ℝ) ^ (-(m : ℝ)) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
    push_cast
    rw [zpow_neg, zpow_natCast]
  rw [← hcast]
  exact_mod_cast padicNorm.dvd_iff_norm_le.mp h

/-- The two previous lemmas combined, in the shape the system (5.11) asks for: if `l^{e·n}`
divides `x`, then `|x|_l ≤ (Pⁿ)^{−e·log l/log P}`. -/
@[category API, AMS 11, ref "BE08", group "bugeaud_10_13"]
theorem padicNorm_le_rpow_of_dvd {l P : ℕ} (hl : l.Prime) (hP : 1 < P) {x : ℤ} {e n : ℕ}
    (hdvd : (l : ℤ) ^ (e * n) ∣ x) :
    ((padicNorm l (x : ℚ) : ℚ) : ℝ) ≤ ((P : ℝ) ^ n) ^ (-((e : ℝ) * Real.log l / Real.log P)) := by
  have hlpos : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl.pos
  rw [rpow_pow_logRatio hP hlpos (e : ℝ) n]
  have h := padicNorm_le_of_dvd_pow hl hdvd
  rwa [show ((e * n : ℕ) : ℝ) = (e : ℝ) * (n : ℝ) by push_cast; ring] at h

/-- The exponent function of the coprime-power frame: `v_l(Q)·log l/log P` at the primes of the
`x`-base `Q`, and `v_l(P)·log l/log P` at those of the `y`-base `P`.  The `if` is unambiguous
because `P` and `Q` are coprime in every use. -/
noncomputable def powExp (P Q l : ℕ) : ℝ :=
  (if l ∈ Q.primeFactors then (Q.factorization l : ℝ) else (P.factorization l : ℝ))
    * Real.log l / Real.log P

@[category API, AMS 11, ref "BE08", group "bugeaud_10_13"]
theorem powExp_nonneg (P Q l : ℕ) : 0 ≤ powExp P Q l := by
  have hl : (0 : ℝ) ≤ Real.log l := Real.log_natCast_nonneg l
  have hP : (0 : ℝ) ≤ Real.log P := Real.log_natCast_nonneg P
  rw [powExp]
  refine div_nonneg (mul_nonneg ?_ hl) hP
  split_ifs <;> exact Nat.cast_nonneg _

/-- The `S₁` half of the budget: `∑_{l ∣ Q} v_l(Q)·log l/log P = log Q/log P`. -/
@[category API, AMS 11, ref "BE08", group "bugeaud_10_13"]
theorem sum_powExp_den {P Q : ℕ} (hQ : Q ≠ 0) :
    ∑ l ∈ Q.primeFactors, powExp P Q l = Real.log Q / Real.log P := by
  rw [log_eq_sum_factorization hQ, Finset.sum_div]
  exact Finset.sum_congr rfl fun l hl => by rw [powExp, ite_eq_left hl]

/-- The `S₂` half of the budget: `∑_{l ∣ P} v_l(P)·log l/log P = 1`. -/
@[category API, AMS 11, ref "BE08", group "bugeaud_10_13"]
theorem sum_powExp_num {P Q : ℕ} (hP : 1 < P)
    (hdisj : Disjoint Q.primeFactors P.primeFactors) :
    ∑ l ∈ P.primeFactors, powExp P Q l = 1 := by
  have hP1 : (1 : ℝ) < P := by exact_mod_cast hP
  have hstep : ∑ l ∈ P.primeFactors, powExp P Q l
      = (∑ l ∈ P.primeFactors, (P.factorization l : ℝ) * Real.log l) / Real.log P := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun l hl => by
      rw [powExp, ite_eq_right (Finset.disjoint_right.mp hdisj hl)]
  rw [hstep, ← log_eq_sum_factorization (by omega : P ≠ 0),
    div_self (ne_of_gt (Real.log_pos hP1))]

/-- **Quantitative Ridout, coprime-power form.**  For coprime bases `P > 1`, `Q > 0` and an
exponent `fInf ≥ 0` with

`fInf + log Q/log P + 1 = 2 + ε`,

there are at most `lineBound ε` slopes carrying every pair `(x, Pⁿ)` with `Qⁿ ∣ x`,
`Pⁿ > max(2H(ξ), 2^{4/ε})` and `|ξ − x/Pⁿ| ≤ (Pⁿ)^{−fInf}`.

The budget of (5.10) is spent as follows: `fInf` at the infinite place; `v_l(Q)·log l/log P` at
each prime `l` of `Q` (summing to `log Q/log P`, and paid for by `Qⁿ ∣ x`); `v_l(P)·log l/log P` at
each prime `l` of `P` (summing to `1`, and paid for by `y = Pⁿ`).  Coprimality is what makes the
two families of primes disjoint, as `ridout_line_cover` requires.

This is the form the general effective Mahler line-count runs on (`BB13/MahlerFrame.lean`).
Footprint `std3 + ridout_line_cover`. -/
@[category research solved, AMS 11, ref "BE08" "ES02", group "bugeaud_10_13"]
theorem ridout_line_cover_pow (ξ : ℚ) (ε fInf : ℝ) (P Q : ℕ)
    (hP : 1 < P) (hQ : 0 < Q) (hcop : Nat.Coprime P Q) (hε : 0 < ε) (hInf : 0 ≤ fInf)
    (hsum : fInf + Real.log Q / Real.log P + 1 = 2 + ε) :
    ∃ R : Finset ℚ, R.card ≤ lineBound ε ∧
      ∀ (n : ℕ) (x : ℤ), (Q : ℤ) ^ n ∣ x →
        max (2 * (ratHeight ξ : ℝ)) ((2 : ℝ) ^ ((4 : ℝ) / ε)) < (P : ℝ) ^ n →
        |(ξ : ℝ) - (x : ℝ) / (P : ℝ) ^ n| ≤ ((P : ℝ) ^ n) ^ (-fInf) →
        (x : ℚ) / ((P : ℚ) ^ n) ∈ R := by
  have hdisj : Disjoint Q.primeFactors P.primeFactors := hcop.symm.disjoint_primeFactors
  obtain ⟨R, hcard, hR⟩ := ridout_line_cover ξ ε fInf Q.primeFactors P.primeFactors (powExp P Q)
    (fun l hl => Nat.prime_of_mem_primeFactors hl) (fun l hl => Nat.prime_of_mem_primeFactors hl)
    hdisj hε hInf (fun l _ => powExp_nonneg P Q l)
    (by rw [Finset.sum_union hdisj, sum_powExp_den (by omega : Q ≠ 0),
          sum_powExp_num hP hdisj, ← add_assoc]
        exact hsum)
  refine ⟨R, hcard, fun n x hdvd hht harch => ?_⟩
  have hycast : (((P : ℤ) ^ n : ℤ) : ℝ) = (P : ℝ) ^ n := by push_cast; ring
  have key := hR x ((P : ℤ) ^ n) (by positivity) (by rw [hycast]; exact hht)
    (by rw [hycast]; exact harch) ?_ ?_
  · rw [show (((P : ℤ) ^ n : ℤ) : ℚ) = (P : ℚ) ^ n by push_cast; ring] at key
    exact key
  · -- the `S₁` conditions: `l^{v_l(Q)·n} ∣ Qⁿ ∣ x`
    intro l hl
    have hlp := Nat.prime_of_mem_primeFactors hl
    have hdvd' : (l : ℤ) ^ (Q.factorization l * n) ∣ x := by
      refine dvd_trans ?_ hdvd
      rw [pow_mul]
      exact pow_dvd_pow_of_dvd (Int.natCast_dvd_natCast.mpr (Nat.ordProj_dvd Q l)) n
    rw [hycast, powExp, ite_eq_left hl]
    exact padicNorm_le_rpow_of_dvd hlp hP hdvd'
  · -- the `S₂` conditions: `l^{v_l(P)·n} ∣ Pⁿ`
    intro l hl
    have hlp := Nat.prime_of_mem_primeFactors hl
    have hdvd' : (l : ℤ) ^ (P.factorization l * n) ∣ (P : ℤ) ^ n := by
      rw [pow_mul]
      exact pow_dvd_pow_of_dvd (Int.natCast_dvd_natCast.mpr (Nat.ordProj_dvd P l)) n
    rw [hycast, powExp, ite_eq_right (Finset.disjoint_right.mp hdisj hl)]
    exact padicNorm_le_rpow_of_dvd hlp hP hdvd'

end BugeaudEvertse
