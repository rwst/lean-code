/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.BigOperators.Fin
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Evertse's S-unit sum lower bound (Compositio 1984), ℚ-specialization

The finiteness theorem behind Evertse's work on sums of `S`-units ([Eve84], Theorem 1
and its `ℚ`-form Corollary 1; read in full 2026-07-08), a Thue–Siegel–Roth–Schmidt
(Subspace) consequence: **a sum of `S`-units cannot be much smaller than its largest
term, outside finitely many exceptional proportional classes.**

> Let `S` be a finite set of primes enclosing `S_∞`, `n ≥ 1`, and `ε > 0`.  Then, among
> the **primitive** integer points `x = (x₀ : x₁ : … : xₙ) ∈ ℙⁿ(ℚ)` all of whose
> coordinates are `S`-units and which are **non-degenerate** (no proper subsum
> `x_{i₀}+…+x_{iₛ}` vanishes), only finitely many satisfy
>
>   `|x₀ + x₁ + … + xₙ| < H(x)^{1-ε}`.
>
> ([Eve84], Theorem 1 gives the projective-point / proportional-class count; Corollary 1
> is the explicit `ℚ`-normalization with `gcd = 1`.)

`H(x)` is the absolute (projective) Weil height.  Because `x` is a **primitive integer
point**, `H(x) = max_i |x_i|` — this is the identity ([Eve84], eq. (5)):
`‖x‖ = H(X)` iff `gcd(x₀, …, xₙ) = 1`.  So the height in the statement is the plain
archimedean maximum, and no product-formula machinery is needed.

## Statement conventions (the ℚ-specialization — all uses in this corpus)

Each direction *weakens*, or is *equivalent to*, the source (safe):

* **`S = {∞, 2, 3}`.**  The `S`-units among the rational integers are exactly `±2^a·3^b`
  (`a, b ≥ 0`); this is the predicate `Evertse.IsSUnit`.
* **Proportional classes = primitive integer points.**  Over `ℚ`, every proportional
  class of `S`-unit tuples has a unique-up-to-sign representative that is a *primitive
  integer* point (clear denominators, divide out the common `2^{min aᵢ}·3^{min bᵢ}`);
  primitivity is `gcd(x₀, …, xₙ) = 1`.  This is Evertse's own normalization
  ([Eve84], Corollary 1, eq. (11)), and it is **essential** for the truth of the bound:
  without it the map `x ↦ 2^{-N}·x` shows every direction to be exceptional (the values
  `2^a·3^b` are dense near `1`, so freely scaled `ℤ[1/6]`-unit tuples have arbitrarily
  small sums relative to their max).  Fixing `gcd = 1` — equivalently, passing to
  proportional classes — kills exactly that scaling freedom.
* **Height = archimedean max.**  By `gcd = 1` and [Eve84] eq. (5), `H(x) = max_i |x_i|`,
  recorded as `Finset.univ.sup (|x ·|)` in `ℕ` and cast to `ℝ`; the threshold
  `H(x)^{1-ε}` lives in `ℝ` via `rpow` with `ε : ℝ` free.  Since every coordinate is an
  `S`-unit, `max_i |x_i| ≥ 1` (`IsSUnit.one_le_natAbs`).
* **Non-degeneracy** is transcribed verbatim: `∑_{i ∈ I} x_i ≠ 0` for every proper,
  nonempty `I ⊂ univ` ([Eve84], eq. (8)/(10)).
* **One inequality covers both regimes.**  The exceptional condition
  `|∑ x_i| < H(x)^{1-ε}` includes the exact `S`-unit *equation* `∑ x_i = 0` (Theorem 1
  proper: also finitely many non-degenerate primitive solutions) *and* the approximate
  ("sum is small") case, uniformly.

The finiteness is **ineffective** (Subspace-based): [Eve84] bounds the *number* of
exceptional classes but provides no bound on their size.  Do not expect computable
exceptional bounds downstream.

Role in the program ([M4A3] §8 row 2): a shared `S`-unit engine — bounded-`u` extremal
subfamilies, reusable across the A5/A6 window analyses and BCZ-style `gcd(2ⁿ−1, 3ⁿ−1)`
arguments.  Consumers with `S`-units such as `(3/2)^c = 2^{-c}·3^c` clear denominators to
land on the primitive integer representative.

## Contents

* `Evertse.IsSUnit` — the predicate "`x = ±2^a·3^b`" (an `S`-unit of `ℤ` for
  `S = {∞, 2, 3}`).
* `Evertse.isSUnit_two_pow_three_pow`, `IsSUnit.ne_zero`, `IsSUnit.one_le_natAbs` — the
  basic facts a consumer needs (existence witness; nonvanishing; `max ≥ 1`).
* `Evertse.sUnit_sum_lower` — **Theorem 1 / Corollary 1** of [Eve84], ℚ-specialized; a
  cited Subspace-theorem consequence recorded as an `axiom`.

## References

* [Eve84] Evertse, Jan-Hendrik. "On sums of `S`-units and linear recurrences."
  *Compositio Mathematica* **53**.2 (1984), 225–244.  (Theorem 1, p. 227; Corollary 1,
  p. 227, the `ℚ`-normalization with `gcd = 1`; Theorem 2 is the underlying analytic
  Subspace inequality.)
* [M4A3] `plan-M4A3.html` (this repository, 2026-07): §7 (engine audit), §8 row 2
  (transcription brief), §9 (file listing).
-/

namespace Evertse

open Finset

/-- An `S`-unit of `ℤ` for `S = {∞, 2, 3}`: a rational integer `x = ±2^a·3^b`
(`a, b ≥ 0`).  These are exactly the integers among the `S`-units of `ℚ` (units of
`ℤ[1/6]`) that are algebraic integers. -/
@[category API, AMS 11, ref "Eve84", group "three_halves_m4"]
def IsSUnit (x : ℤ) : Prop := ∃ a b : ℕ, x = 2 ^ a * 3 ^ b ∨ x = -(2 ^ a * 3 ^ b)

/-- The canonical positive witnesses: `2^a·3^b` is an `S`-unit. -/
@[category API, AMS 11, ref "Eve84", group "three_halves_m4"]
lemma isSUnit_two_pow_three_pow (a b : ℕ) : IsSUnit ((2 : ℤ) ^ a * 3 ^ b) :=
  ⟨a, b, Or.inl rfl⟩

/-- An `S`-unit is nonzero. -/
@[category API, AMS 11, ref "Eve84", group "three_halves_m4"]
lemma IsSUnit.ne_zero {x : ℤ} (h : IsSUnit x) : x ≠ 0 := by
  obtain ⟨a, b, h | h⟩ := h <;> subst h
  · positivity
  · rw [neg_ne_zero]; positivity

/-- An `S`-unit has absolute value at least `1`; hence the maximum coordinate of an
`S`-unit tuple is `≥ 1` (so the height base of `sUnit_sum_lower` is `≥ 1`). -/
@[category API, AMS 11, ref "Eve84", group "three_halves_m4"]
lemma IsSUnit.one_le_natAbs {x : ℤ} (h : IsSUnit x) : 1 ≤ x.natAbs :=
  Int.natAbs_pos.mpr h.ne_zero

/-- **Evertse's `S`-unit sum lower bound** ([Eve84], Theorem 1 / Corollary 1),
ℚ-specialized to `S = {∞, 2, 3}` and the primitive-integer (proportional-class)
normalization (see the module doc for the specialization directions):

for every `n ≥ 1` and `ε > 0`, only finitely many tuples `x : Fin n → ℤ` satisfy

  * every coordinate is an `S`-unit `±2^a·3^b`  (`IsSUnit`),
  * `gcd(x₀, …, x_{n-1}) = 1`  (primitivity = the proportional-class representative),
  * non-degeneracy: `∑_{i ∈ I} x_i ≠ 0` for every proper, nonempty `I ⊂ univ`, and
  * `|∑ x_i| < (max_i |x_i|)^{1-ε}`   (the sum is smaller than the height to the `1-ε`).

Equivalently: **all but finitely many** primitive non-degenerate `S`-unit tuples obey
`|∑ x_i| ≥ (max_i |x_i|)^{1-ε}`.  Recorded as a cited `axiom` on the authority of
[Eve84] — a `p`-adic Thue–Siegel–Roth–Schmidt (Subspace) argument (their Theorem 2, an
`S`-unit refinement of Schmidt's Subspace theorem, plus the height normalization eq. (5))
that we do not re-derive.  The finiteness is **ineffective**. -/
@[category research solved, AMS 11, ref "Eve84", group "three_halves_m4"]
axiom sUnit_sum_lower (n : ℕ) (hn : 1 ≤ n) (ε : ℝ) (hε : 0 < ε) :
    { x : Fin n → ℤ |
        (∀ i, IsSUnit (x i)) ∧
        Finset.univ.gcd (fun i => x i) = 1 ∧
        (∀ I : Finset (Fin n), I.Nonempty → I ⊂ Finset.univ → ∑ i ∈ I, x i ≠ 0) ∧
        ((|∑ i, x i| : ℤ) : ℝ) < ((Finset.univ.sup fun i => (x i).natAbs : ℕ) : ℝ) ^ (1 - ε) }.Finite

end Evertse
