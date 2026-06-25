/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import AB.HenselExpansions
import AB.StammeringSequences
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Adamczewski–Bugeaud — the p-adic stammering transcendence criterion (AB07, Theorem 6)

Boris Adamczewski and Yann Bugeaud, *On the complexity of algebraic numbers I. Expansions in
integer bases*, Annals of Mathematics **165** (2007), 547–565, **Section 6** ("Transcendence of
`p`-adic numbers").

This file records **Theorem 6**, the `p`-adic transcendence *criterion* — the engine behind the
automatic transcendence Theorem 2B ([[ab-complexity-corpus-root]],
`AB.irrational_automatic_padic_transcendental`). Where Theorem 2B takes an *automatic* digit sequence,
Theorem 6 takes the weaker (and more fundamental) hypothesis that the sequence is **stammering**
(satisfies Condition (∗)_w, `AB.ConditionStar`, [[ab-complexity-corpus-root]] `AB.StammeringSequences`):

> **Theorem 6.** *Let `p` be a prime and `(a_k)_{k ≥ −m}` a sequence with values in `{0,…,p−1}`. Let
> `w > 1`. If `(a_k)_{k ≥ 1}` satisfies Condition (∗)_w, then the `p`-adic number
> `α = ∑_{k=−m}^{∞} a_k p^k` is transcendental.*

This is **the application of the Schmidt Subspace Theorem** in the paper. AB's proof reduces to the
integer part `α' = ∑_{k≥1} a_k p^k`, observes that the truncate-and-periodically-complete approximants
`α_n = p_n/(p^{s_n} − 1)` satisfy `|α' − α_n|_p ≤ p^{−r_n − w·s_n}` (the `w > 1` repetition makes them
converge *too fast*), and applies **Schlickewei's `p`-adic Subspace Theorem** [Sch77] (Theorem 4.1 of
[Sch76]) to the linear forms `L₁,ₚ(x,y,z) = x`, `L₂,ₚ = y`, `L₃,ₚ = α'x + α'y + z` (and the trivial
forms at the infinite place) evaluated at `xₙ = (p^{sₙ}, −1, −pₙ)`: were `α'` algebraic, the points
would lie in finitely many subspaces, forcing a contradiction. (See [Eve96] for the quantitative
form.) The criterion is recorded here as a **cited `axiom`** (`transcendental_of_conditionStar`); the
Subspace-Theorem machinery is not reconstructed.

The **underlying Subspace Theorem itself** — Theorem E (AB07 p. 8), Evertse's multidimensional,
all-places (`p`-adic-inclusive) form — is now recorded separately as `AB.subspace_theorem_E`
(`AB.SubspaceTheoremE`). Theorem 6 here is its specialisation to `m = 3` at the places `{p} ∪ {∞}` with
the three forms above and the points `xₙ`; deriving it from `subspace_theorem_E` is exactly AB07 §4/§6
(Lemma 1 + the product estimate), itself a substantial argument, so the criterion stays a cited `axiom`.

Note that Condition (∗)_w *includes* "not eventually periodic", so irrationality is built in — Theorem 6
concludes transcendence directly, with no separate hypothesis. Theorem 2B is the special case obtained
by combining this with "non-eventually-periodic automatic ⟹ stammering"
(`AB.isStammering_of_automatic`).

## Contents
* `transcendental_of_conditionStar` — **Theorem 6** (cited): a Hensel digit sequence satisfying
  Condition (∗)_w gives a transcendental `p`-adic number.
* `transcendental_of_isStammering` — the same for a stammering sequence (`IsStammering`, the existential
  over `w`).

## References
* [AB07] Adamczewski, Boris, and Yann Bugeaud. *On the complexity of algebraic numbers I. Expansions in
  integer bases.* Annals of Mathematics 165 (2007), 547–565 (Theorem 6, §6).
* [Sch77] Schlickewei, Hans Peter. *The `p`-adic Thue–Siegel–Roth–Schmidt theorem.* Arch. Math. (Basel)
  29 (1977), 267–270 (the `p`-adic Subspace Theorem applied in the proof).
* [Sch76] Schlickewei, Hans Peter. *On products of special linear forms with algebraic coefficients.*
  Acta Arith. 31 (1976), 389–398 (Theorem 4.1, the precise form AB07 invoke).
* [Eve96] Evertse, Jan-Hendrik. *An improvement of the quantitative Subspace theorem.* Compositio Math.
  101 (1996), 225–311.
-/

namespace AB

/-- **Theorem 6 (Adamczewski–Bugeaud 2007, §6).** *The `p`-adic stammering transcendence criterion.*

If `p` is prime, `a : ℕ → ℕ` is a Hensel digit sequence (`a k < p`) satisfying **Condition (∗)_w**
(`ConditionStar w a`) for some `w > 1`, then the `p`-adic number `henselValue p m a = ∑ₙ aₙ p^{n−m}` is
**transcendental** over `ℚ`. (Condition (∗)_w forces "not eventually periodic", hence irrational, so no
separate irrationality hypothesis is needed.)

This is the paper's central **application of the Schmidt Subspace Theorem** (via Schlickewei [Sch77];
the truncate-and-complete approximants converge too fast because `w > 1`). Recorded as a cited `axiom`;
Theorem 2B (`irrational_automatic_padic_transcendental`) is the automatic special case, via
`isStammering_of_automatic`. -/
@[category research solved, AMS 11 68, ref "AB07" "Sch77", group "ab_complexity_thm6"]
axiom transcendental_of_conditionStar (p : ℕ) [Fact p.Prime] (m : ℕ) (a : ℕ → ℕ)
    (ha : ∀ k, a k < p) (w : ℝ) (hw : 1 < w) (hcond : ConditionStar w a) :
    Transcendental ℚ (henselValue p m a)

/-- **Theorem 6, stammering form.** A Hensel digit sequence that is **stammering** (`IsStammering a`,
i.e. satisfies Condition (∗)_w for *some* `w > 1`) gives a transcendental `p`-adic number. Immediate
from `transcendental_of_conditionStar` by unpacking the existential. -/
@[category research solved, AMS 11 68, ref "AB07" "Sch77", group "ab_complexity_thm6"]
theorem transcendental_of_isStammering (p : ℕ) [Fact p.Prime] (m : ℕ) (a : ℕ → ℕ)
    (ha : ∀ k, a k < p) (hstam : IsStammering a) :
    Transcendental ℚ (henselValue p m a) := by
  obtain ⟨w, hw, hcond⟩ := hstam
  exact transcendental_of_conditionStar p m a ha w hw hcond

end AB
