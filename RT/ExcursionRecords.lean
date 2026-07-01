/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CC.Decomposition
import RT.CRozLemma32
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Excursion and delay records (cited computational data for Theorem 5.3)

Theorem 5.3 of [Roz25] (finitely many paradoxical sequences below `2.8×10¹⁹`) rests on three
external computations that are genuine large verified searches, **not** theorems we re-derive:

* the exhaustive search over `n ≤ 10⁹` (Table 1 / Appendix C of [Roz25]);
* the maximal-excursion records `M_T` of Oliveira e Silva [OeS];
* the Collatz delay records `d_Col` of Roosendaal [Roosendaal].

Following the layered-QA convention for corpus roots, each is recorded here as a cited `axiom`
carrying a literature `@[ref]` (so the extractor marks every downstream result `cited`, never
`stated_only`).  The record *tables* are the cited facts; the crossing computations
`j₀ = 1539`, `q₀ = 971`, `j₁ = 301994` derived from them are ordinary finite arithmetic and are
to be *proved* (Step 3), not axiomatized.

## Definitions

* `maxExcursion n = M_T(n)` — the supremum of the Terras orbit `{Tᵏ(n)}` in `ℕ∞`.
* `delayCol n = d_Col(n)` — the `Col` (`3n+1`) delay, defined via eq. (14) of [Roz25] from the
  Terras data (`= j + qⱼ(n)` at the first `j` with `Tʲ(n) = 1`), avoiding a second dynamics.

## References
* [Roz25] Rozier, Olivier, and Claude Terracol. "Paradoxical behavior in Collatz sequences."
  arXiv preprint arXiv:2502.00948 (2025). Theorem 5.3, Corollary 5.4 (pp. 15–17); eq. (14).
* [OeS] T. Oliveira e Silva. *Empirical verification of the 3x+1 and related conjectures* —
  maximal-excursion records.
* [Roosendaal] E. Roosendaal. *On the 3x+1 problem* (web) — Collatz delay records.
-/

open Classical

open CC

namespace RT

/-! ### The excursion and delay functionals -/

/-- The **maximal excursion** `M_T(n)`: the supremum of the Terras orbit `{Tᵏ(n) : k ≥ 0}` in
`ℕ∞` (equal to `⊤` iff the orbit is unbounded). Always `≥ n` (attained at `k = 0`). -/
@[category API, AMS 11 37, ref "Roz25", group "roz_excursion_records"]
noncomputable def maxExcursion (n : ℕ) : ℕ∞ := ⨆ k : ℕ, (T_iter k n : ℕ∞)

/-- The **Collatz delay** `d_Col(n)` of the `3n+1` (`Col`) formalism, defined via eq. (14) of
[Roz25] from the Terras data: at the first step `j` with `Tʲ(n) = 1`, each odd Terras step counts
as two `Col` steps, so `d_Col(n) = j + qⱼ(n)`; it is `⊤` when `n` never reaches `1`. Defining it
this way avoids formalizing a second dynamics. -/
@[category API, AMS 11 37, ref "Roz25", group "roz_excursion_records"]
noncomputable def delayCol (n : ℕ) : ℕ∞ :=
  if h : ∃ j, T_iter j n = 1 then ((Nat.find h + num_odd_steps (Nat.find h) n : ℕ) : ℕ∞) else ⊤

/-! ### The cited record data

Each of the following is an external verified computation, recorded on the authority of its
`@[ref]` citation. The concrete constants are those quoted in §5 of [Roz25]. -/

/-- **Exhaustive base case** ([Roz25], Table 1 / Appendix C). Every paradoxical sequence with first
term `3 ≤ n ≤ 10⁹` has `n ≤ 4614` and length `j ≤ 92`. (The bound `3 ≤ n` excludes the trivial
cycle `{1,2}`, whose members are paradoxical for unboundedly large `j`; the exhaustive search of
[Roz25], and Table 1's range `n ≥ 7`, concern `n ≥ 3`.) -/
@[category research solved, AMS 11 37, ref "Roz25", group "roz_excursion_records"]
axiom base_case_exhaustive :
    ∀ j n : ℕ, IsParadoxical j n → 3 ≤ n → n ≤ 10 ^ 9 → n ≤ 4614 ∧ j ≤ 92

/-- **Maximal-excursion record `m₀`** ([OeS]). The smallest `m` whose orbit reaches
`M_T(m) ≥ 10⁹` is `m₀ = 113383`. -/
@[category research solved, AMS 11 37, ref "Roz25" "OeS", group "roz_excursion_records"]
axiom maxexc_record_m0 :
    ∀ m : ℕ, maxExcursion m ≥ (10 ^ 9 : ℕ) → m ≥ 113383

/-- **Collatz delay record** ([Roosendaal]). The largest known `Col`-delay is `2456`, verified for
every `n` up to `2.8×10¹⁹`. -/
@[category research solved, AMS 11 37, ref "Roz25" "Roosendaal", group "roz_excursion_records"]
axiom delay_record_col :
    ∀ n : ℕ, 2 ≤ n → delayCol n ≤ (2456 : ℕ) ∨ n > 28 * 10 ^ 18

/-- **Maximal-excursion record `m₁`** ([OeS]). The smallest `m` whose orbit reaches
`M_T(m) > 2.8×10¹⁹` is `m₁ = 23035537407`. -/
@[category research solved, AMS 11 37, ref "Roz25" "OeS", group "roz_excursion_records"]
axiom maxexc_record_m1 :
    ∀ m : ℕ, maxExcursion m > (28 * 10 ^ 18 : ℕ) → m ≥ 23035537407

end RT
