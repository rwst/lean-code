/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import RB.Basic
import RB.Rigidity
import CITED.AdamczewskiFaverjon
import CITED.AlloucheShallitComplexity
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.NumberTheory.Real.Irrational
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# T1a: `K` algebraic irrational ⇒ the minimal word is not automatic (plan-B1E2, WP7)

The capstone of plan-B1E2's **refereed lane**: the first statement of any kind linking the
arithmetic nature of `K = ω_{3/2}` to the automaticity of the word `RB.wmin` that generates it.

## The chain

Suppose `w = RB.wmin x₀` is automatic.  Then:

1. `f(z) = Σⱼ wⱼzʲ` is Mahlerian with coefficients in `{0,1}` (`wmin_le_one`), so it converges
   on `|z| < 1` and `α = 2/3` is not a pole; `k = ℚ` contains `α` and the coefficients.
2. [AF17] Cor 1.8 (`AF.transcendental_or_rat_of_automatic`) ⇒ **`f(2/3)` is transcendental, or
   `f(2/3) ∈ ℚ`.**
3. `RB.tsum_wmin_eq` ⇒ `f(2/3) = 3(K − x₀)` with `x₀ ∈ ℕ`, so the alternative transfers to `K`
   verbatim: `3(K − x₀)` is transcendental iff `K` is, and lies in `ℚ` iff `K` does.

Hence **`w` automatic ⇒ `K` transcendental or `K ∈ ℚ`**, i.e. `not_automatic_of_K_algebraic_irrational`.

The point is that an **algebraic irrational** `K` is excluded by *both* branches at once — which
is the only way to extract force from an alternative that AF prove cannot be removed.  (See
`CITED.AdamczewskiFaverjon`'s module doc: reading Cor 1.8 as forcing degeneracy from a *known*
rational value is invalid, and is what sank this plan's rev. 1.)

## Honest scope

`K` is *expected* to be transcendental, so this hypothesis is plausibly vacuous, and the theorem
is **not** a solution to the non-automaticity problem (report-dubickas B.1) — the generic
transcendental case is untouched. Its value is threefold: it is the first link of `K`'s
arithmetic to the word's automaticity; its contrapositive is a *transcendence criterion* for a
constant whose irrationality has been open since 1977 (`transcendental_of_automatic_of_irrational`
— *if the carry word is automatic and `K` is irrational, then `K` is transcendental*); and it
costs exactly one refereed axiom. Do not oversell it. ([B1E2] §2.2's "Honest scope" box.)

## Two lanes, never mixed

* **Refereed lane** (this file): `std3 + AF.transcendental_or_rat_of_automatic` only.
  `lean_verify`-confirmed 2026-07-16.
* **Preprint lane** (T1b, *not built* — milestone M4): removing the `K ∈ ℚ` horn needs
  plan-B2A2's T1a (`K ∈ ℚ ⇒ p_w superlinear ⇒ not automatic`, via `AS.not_automatic_of_complexity_superlinear`),
  which adds the CZ04 + NKR25 axioms. `not_automatic_of_K_algebraic_of_ratCase` below is the
  glue, stated with the B2A2 input as an explicit **hypothesis** so that no preprint axiom ever
  enters this file's footprint.

## Contents

* `RB.tsum_wmin_eq'` — the value in AF's coefficient-first order.
* **`RB.not_automatic_of_K_algebraic_irrational`** — T1a, the refereed-lane capstone.
* `RB.transcendental_of_automatic_of_irrational` — the transcendence-criterion contrapositive.
* `RB.not_automatic_of_K_algebraic_of_ratCase` — the T1b glue, B2A2's input as a hypothesis.

## References

* [AF17] Adamczewski, Faverjon. *Méthode de Mahler …* Proc. LMS **115** (2017), 55–90. (Cor 1.8.)
* [AFS08] Akiyama, Frougny, Sakarovitch. Israel J. Math. **168** (2008), 53–91. (`K = ω_{3/2}`.)
* [B1E2] `plans/plan-B1E2.html` (rev. 2, 2026-07): §2.2 (this chain), WP7, milestones M2/M4.
* [B2A2] `plans/plan-B2A2.html`: T1a = the `K ∈ ℚ` horn.
-/

namespace RB

/-- The word's archimedean value at `2/3`, written in [AF17]'s coefficient-first order
`∑ⱼ aⱼαʲ` so that `AF.transcendental_or_rat_of_automatic` applies literally. -/
@[category API, AMS 11 68, ref "AFS08" "AF17", group "rb_rational_base"]
lemma tsum_wmin_eq' (x₀ : ℕ) :
    ∑' j, (wmin x₀ j : ℝ) * ((2 / 3 : ℚ) : ℝ) ^ j = 3 * (K x₀ - x₀) := by
  rw [← tsum_wmin_eq x₀]
  push_cast
  exact tsum_congr fun j => mul_comm _ _

@[category API, AMS 11 68, ref "AF17", group "rb_rational_base"]
private lemma isAlgebraic_natCast (n : ℕ) : IsAlgebraic ℚ ((n : ℝ)) := by
  simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℝ) (n : ℚ)

/-- **T1a — the refereed-lane capstone** ([B1E2] §2.2): if `K = ω_{3/2}` (from `x₀`) is an
**algebraic irrational**, then the minimal word `RB.wmin x₀` is **not automatic**.

Both branches of [AF17] Cor 1.8 are killed at once: `3(K − x₀)` cannot be transcendental
(`K` is algebraic), and it cannot be rational (`K` is irrational).

Footprint: `std3 + AF.transcendental_or_rat_of_automatic`. No `p`-adic input, no CZ04, no
NKR25. -/
@[category research solved, AMS 11 68, ref "AF17" "AFS08" "B1E2", group "rb_rational_base"]
theorem not_automatic_of_K_algebraic_irrational {x₀ : ℕ}
    (halg : IsAlgebraic ℚ (K x₀)) (hirr : Irrational (K x₀)) :
    ¬ AS.IsAutomatic (wmin x₀) := by
  intro hauto
  rcases AF.transcendental_or_rat_of_automatic (wmin_le_one x₀) hauto
      (α := 2 / 3) (by norm_num) (by norm_num) with htr | ⟨r, hr⟩
  · -- first branch: `3(K − x₀)` would be transcendental, but `K` is algebraic
    rw [tsum_wmin_eq'] at htr
    exact htr ((isAlgebraic_natCast 3).mul (halg.sub (isAlgebraic_natCast x₀)))
  · -- second branch: `3(K − x₀) ∈ ℚ` would make `K = r/3 + x₀` rational
    rw [tsum_wmin_eq'] at hr
    exact hirr ⟨r / 3 + x₀, by push_cast; linarith⟩

/-- **The transcendence criterion** — T1a's contrapositive, and the reading with actual content:
*if the carry word is automatic and `K` is irrational, then `K` is transcendental.*

`K = ω_{3/2} = K(3) = 1.6222705028…` (A083286) is not known to be irrational — that has been
open since 1977 — so this is a conditional statement about a genuinely open constant. -/
@[category research solved, AMS 11 68, ref "AF17" "AFS08" "B1E2", group "rb_rational_base"]
theorem transcendental_of_automatic_of_irrational {x₀ : ℕ}
    (hauto : AS.IsAutomatic (wmin x₀)) (hirr : Irrational (K x₀)) :
    Transcendental ℚ (K x₀) :=
  fun halg => not_automatic_of_K_algebraic_irrational halg hirr hauto

/-- **T1b glue** ([B1E2] M4): `K` algebraic ⇒ `w` not automatic, *given* plan-B2A2's T1a as the
hypothesis `hrat` (`K ∈ ℚ ⇒ w not automatic`, which B2A2 obtains from superlinearity via
`AS.not_automatic_of_complexity_superlinear`).

Stated with `hrat` as a hypothesis **on purpose**: B2A2's route runs through the CZ04 and NKR25
axioms (NKR25 being an unrefereed preprint), and this file must stay in the refereed lane. When
B2A2's T1a lands, discharge `hrat` at the call site — not here. -/
@[category research solved, AMS 11 68, ref "AF17" "B1E2", group "rb_rational_base"]
theorem not_automatic_of_K_algebraic_of_ratCase {x₀ : ℕ}
    (hrat : ¬ Irrational (K x₀) → ¬ AS.IsAutomatic (wmin x₀))
    (halg : IsAlgebraic ℚ (K x₀)) :
    ¬ AS.IsAutomatic (wmin x₀) := by
  by_cases hirr : Irrational (K x₀)
  · exact not_automatic_of_K_algebraic_irrational halg hirr
  · exact hrat hirr

/-- **T1b, with B2A2's obligation named exactly** ([B1E2] M4): `K` algebraic ⇒ `w` not
automatic, given only that a *rational* `K` forces **superlinear** subword complexity.

This is the precise contract for plan-B2A2's T1a: deliver `hsuper`, and T1b follows. The
Cobham step (`AS.not_automatic_of_complexity_superlinear`, [B1E2] WP8a) is already discharged
here, so B2A2 owes complexity — not automata.

Note the shape: superlinearity, **not** a linear lower bound. [Dub09] Cor 4's `1.70951129n` is
linear and therefore cannot serve, however large its constant ([B1E2] §4). -/
@[category research solved, AMS 11 68, ref "AF17" "B1E2" "B2A2", group "rb_rational_base"]
theorem not_automatic_of_K_algebraic_of_superlinear {x₀ : ℕ}
    (hsuper : ¬ Irrational (K x₀) → ∀ C, ∃ m, 1 ≤ m ∧ C * m < AS.complexity (wmin x₀) m)
    (halg : IsAlgebraic ℚ (K x₀)) :
    ¬ AS.IsAutomatic (wmin x₀) :=
  not_automatic_of_K_algebraic_of_ratCase
    (fun hrat => AS.not_automatic_of_complexity_superlinear (hsuper hrat)) halg

end RB
