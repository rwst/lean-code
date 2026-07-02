/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CITED.AlloucheShallitBasic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Adamczewski–Bugeaud — Stammering sequences and Condition (∗)_w (AB07, §4)

Boris Adamczewski and Yann Bugeaud, *On the complexity of algebraic numbers I. Expansions in
integer bases*, Annals of Mathematics **165** (2007), 547–565, **Section 4** ("A transcendence
criterion for stammering sequences").

The transcendence results of the paper (Theorems 1–5, [[ab-complexity-corpus-root]]) all flow from a
single combinatorial criterion (Theorem 5) applied to sequences with a strong repetitive structure,
which the authors — following a suggestion of Guy Barat — call **stammering sequences**. This file
records that structure: **Condition (∗)_w** (AB07, §4) and the fact, extracted from the paper's proof
of Theorem 2 (via Cobham's theorem), that a **non-eventually-periodic automatic sequence is
stammering**.

## Condition (∗)_w (AB07, §4)

For a real number `w > 1`, a sequence `a = (aₖ) = a₀a₁a₂…` over a finite alphabet satisfies
**Condition (∗)_w** if `a` is *not* eventually periodic and there exist two sequences of finite words
`(Uₙ)`, `(Vₙ)` such that, writing `rₙ = |Uₙ|`, `sₙ = |Vₙ|`:

* (i)   `Uₙ Vₙ^w` is a prefix of `a` for every `n`;
* (ii)  `(rₙ / sₙ)ₙ` is bounded from above;
* (iii) `(sₙ)ₙ` is increasing.

Here `Vₙ^w` is the word `Vₙ` repeated `w` times (a real exponent: `⌊w⌋` full copies followed by a
prefix). A sequence satisfying Condition (∗)_w for *some* `w > 1` is a **stammering sequence**
(`IsStammering`).

We encode clause (i) directly on the sequence `a : ℕ → ℕ` (digits `a 0, a 1, …`): "`Uₙ Vₙ^w` is a
prefix" means the block of length `Lₙ := ⌊w · sₙ⌋` starting at position `rₙ` is `sₙ`-periodic, i.e.
`a i = a (i - sₙ)` for `rₙ + sₙ ≤ i < rₙ + Lₙ`. (Using the floor `⌊w·sₙ⌋` is a faithful lower bound on
the length `|Vₙ^w| = ⌊w⌋sₙ + ⌈(w-⌊w⌋)sₙ⌉` of the repeated portion that AB07 guarantees, so the
encoded condition is *implied* by the paper's; this is the form actually used by the criterion.) This
avoids word machinery while keeping the mathematical content exact.

## Automatic ⟹ stammering (AB07, proof of Theorem 2)

In the proof of Theorem 2 the authors show, using Cobham's theorem [Cob72] (an automatic sequence is
the image under a coding of a fixed point of a *uniform* morphism `σ`) and the Dirichlet
*Schubfachprinzip*, that a non-eventually-periodic automatic sequence satisfies Condition (∗)_{1+1/r}
for a suitable integer `r`, hence is stammering. We record this as a **cited `axiom`**
(`isStammering_of_automatic`); the underlying morphism/Cobham machinery is not reconstructed here.

## Contents
* `IsEventuallyPeriodic` — a sequence is eventually periodic.
* `ConditionStar` — **Condition (∗)_w** (AB07, §4).
* `IsStammering` — Condition (∗)_w holds for some `w > 1` (a *stammering sequence*).
* `isStammering_of_automatic` — (cited) a non-eventually-periodic automatic sequence is stammering.

## References
* [AB07] Adamczewski, Boris, and Yann Bugeaud. *On the complexity of algebraic numbers I. Expansions in
  integer bases.* Annals of Mathematics 165 (2007), 547–565 (Section 4: Condition (∗)_w; Section 5:
  proof of Theorem 2).
* [Cob72] Cobham, Alan. *Uniform tag sequences.* Math. Systems Theory 6 (1972), 164–192 (an automatic
  sequence is a coding of a uniform-morphism fixed point).
* [Eil74] Eilenberg, Samuel. *Automata, Languages, and Machines, Vol. A.* Academic Press, 1974.
-/

namespace AB

open AS

/-- A sequence `a : ℕ → ℕ` is **eventually periodic**: there is a preperiod `N` and a period `p > 0`
with `a (k + p) = a k` for all `k ≥ N`. The negation is the first clause of Condition (∗)_w (and, for
a `b`-adic / Hensel expansion, exactly *irrationality* of the number). -/
@[category API, AMS 11 68, ref "AB07"]
def IsEventuallyPeriodic (a : ℕ → ℕ) : Prop :=
  ∃ N p : ℕ, 0 < p ∧ ∀ k, N ≤ k → a (k + p) = a k

/-- **Condition (∗)_w (Adamczewski–Bugeaud 2007, §4).** For `w > 1`, the sequence `a = a₀a₁…` satisfies
Condition (∗)_w if it is **not eventually periodic** and admits prefix words `Uₙ Vₙ^w` (lengths
`rₙ = |Uₙ|`, `sₙ = |Vₙ| > 0`) with `(rₙ/sₙ)` bounded above and `(sₙ)` increasing. Clause (i)
("`Uₙ Vₙ^w` is a prefix") is encoded as `sₙ`-periodicity of `a` on the positions
`[rₙ + sₙ, rₙ + ⌊w·sₙ⌋)`: `a i = a (i - sₙ)` there. -/
@[category API, AMS 11 68, ref "AB07"]
def ConditionStar (w : ℝ) (a : ℕ → ℕ) : Prop :=
  ¬ IsEventuallyPeriodic a ∧
  ∃ r s : ℕ → ℕ,
    (∀ n, 0 < s n) ∧
    (∀ n i, r n + s n ≤ i → i < r n + ⌊w * (s n : ℝ)⌋₊ → a i = a (i - s n)) ∧
    (∃ C : ℝ, ∀ n, (r n : ℝ) ≤ C * (s n : ℝ)) ∧
    StrictMono s

/-- A **stammering sequence** (Adamczewski–Bugeaud 2007, §4): one satisfying Condition (∗)_w for some
real `w > 1`. This is the repetitive structure that the paper's transcendence criterion (Theorem 5)
exploits. -/
@[category API, AMS 11 68, ref "AB07"]
def IsStammering (a : ℕ → ℕ) : Prop := ∃ w : ℝ, 1 < w ∧ ConditionStar w a

/-- **(cited; Adamczewski–Bugeaud 2007, proof of Theorem 2.)** *A non-eventually-periodic automatic
sequence is stammering.* If `a` is automatic (`IsAutomatic`, finite `k`-kernel) and not eventually
periodic, then `a` satisfies Condition (∗)_w for some `w > 1`. In AB07 this is obtained from Cobham's
theorem [Cob72] — `a` is a coding of a fixed point of a uniform morphism `σ` — together with the
Dirichlet Schubfachprinzip, which exhibits a prefix `W₁ u W₂ u W₃` and yields Condition (∗)_{1+1/r}
with `Uₙ = σⁿ(W₁)`, `Vₙ = σⁿ(uW₂)`. Recorded as a cited `axiom`; the morphism machinery is not
reconstructed here. -/
@[category research solved, AMS 11 68, ref "AB07" "Cob72", group "ab_stammering"]
axiom isStammering_of_automatic (a : ℕ → ℕ) (hauto : IsAutomatic a)
    (hnep : ¬ IsEventuallyPeriodic a) : IsStammering a

end AB
