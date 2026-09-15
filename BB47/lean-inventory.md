# `BB47/` — Lean inventory for paper 1 (milestone M7)

*(C) Ralf Stephan, in collaboration with Claude Code. CC0 1.0.*
*Written 2026-09-13, after milestone M4. Corpus root: `BB47/` (`lean_lib BB47`, namespace `BB47`).*

This note maps **every numbered result** of `BB47/M1M2.tex`, `BB47/M3.tex` and `BB47/M4.tex` —
the three sources of paper 1 — to its status in Lean 4 + Mathlib. The fourth note, `BB47/M5.tex`
(Theorem Z, 2026-09-15), is covered by the addendum at the end rather than by the tables. It is the answer to "which of
the paper's theorems are machine-checked?", and it is meant to be quotable in the paper itself.

## Summary

    lake build BB47        # 12 files, 3145 lines, 166 declarations, sorry-free  (3231 jobs)
    #                        + AB/ComplexityLowerBound.lean, CITED/BugeaudEvertseComplexity.lean
    #                        + ForMathlib/Combinatorics/FineWilf.lean (Fine–Wilf, std3)
    #                        + ForMathlib/Dynamics/SymbolicDynamics/  (8 files, 3046 lines,
    #                          238 declarations, std3 — the subshift API, plan-subshift WP1–WP8, all)

| | count |
|---|---|
| results tabulated below (M1M2 21, M3 18, M4 9) | 48 rows |
| ✅ **machine-checked, no cited axiom** (`propext`, `Classical.choice`, `Quot.sound` only) | **20** (19 distinct: M3 Prop. 2.1 *is* M1M2 Prop. 3.2) — M1M2 Prop. 2.4 joined on 2026-09-14 |
| 🔗 **proved from** a cited axiom | 7 |
| 📚 quoted as a **cited `@[ref]` axiom** | 5 rows, **7 axioms**: [AB07], [BE08], [BK19]×2, [Rid57], [BBCP04], [Nes96] |
| 🟡 partially formalized | 1 |
| ❌ not formalized — nine results, four reasons, all listed below | 9 |
| 📝 / 🔢 prose, tables, measured data | 6 |

Everything that is a finite combinatorial statement about **one one-sided word** is proved, and
since 2026-09-14 so is the passage to the two-sided `ω`-limit subshift: `Ω(u)` is a subshift,
`p_∞(n,u) = p(n, Ω(u))` (M1M2 Prop. 2.4) and `Ω(u)` contains at most one periodic orbit under the
standing hypothesis (M3 Lem. 3.3). What is still not is (i) the Coven–Hedlund **classification**,
a named 1973 theorem, and (ii) the Diophantine engines, which are quoted. The infrastructure the
classification would be stated in — minimal subshifts, uniformly recurrent languages — exists since
2026-09-14 (`ForMathlib/Dynamics/SymbolicDynamics/Minimal.lean`), but the classification itself is
a project of its own.

## Files

| file | content | cited axioms it introduces |
|---|---|---|
| `Basic.lean` | recurrent blocks, `pInf` = `p_∞`, the non-recurrent prefix `horizon` = `s_n`, tails, rigidity | — |
| `Rauzy.lean` | the reduced Rauzy graph; strong connectivity; the out-closed exclusion. **Since 2026-09-14 it proves nothing**: `recFactorSet u = recurrentLanguage u` is `rfl`, so it re-exports `ForMathlib/Dynamics/SymbolicDynamics/Rauzy.lean` (`edgeSrc`/`edgeTgt` by `export`, one constant with two names) | — |
| `Degrees.lean` | in/out-degrees as `Finset.card`s of fibres and the two degree sums — the part `ForMathlib` does not express — plus the unique right- and left-special block, now *derived* from `exists_isRightSpecial`/`eq_of_isRightSpecial` through `isRightSpecial_iff_two_le_outDeg` | — |
| `LemmaA0.lean` | the repetition function `r(n,·)`, **Lemma A0**, and the [BK26] comparison | — |
| `Cited.lean` | `AB.baseValue` wrapper; **[BK19] Thm. 10.4**, both clauses; imports the two complexity theorems | 2 |
| `TheoremA.lean` | **Theorems A and A′** (from [AB07]/[BE08]) and their `_via_repLen` twins (from [BK19]), the `n+k` ladder, the structure corollary | — |
| `Certificate.lean` | the three M4 certificates and **the ceiling** | — |
| `Sliver.lean` | the skew branch's Diophantine constraints; **Theorem D proved from Ridout** | 3 |
| `PeriodicOrbits.lean` | the Fine–Wilf half of [M3, Lem. 3.3] for **one-sided** words: two periodic words sharing one block of length `p + q` are shifts of each other, hence one orbit | — |
| `OmegaLimit.lean` | **(new 2026-09-14, WP8)** `Ω(u)` as a subshift in 10.47's vocabulary: **M1M2 Prop. 2.4** (`pInf_eq_complexity`), `Ω(u)` as an `ω`-limit set of any two-sided extension, `Ω = ⟵lim G'ₙ`, and **M3 Lem. 3.3 complete** (`orbit_eq_of_pInf_eq`, with `orbit_eq_of_pInf_succ_le` the sharper form) | — |
| `TheoremZ.lean` | **(new 2026-09-14)** **Theorem Z** — `p` and `p_∞` have the same exponential growth rate, so under (H) the *whole* expansion has zero entropy. Carries the horizon bound `p(n) ≤ s_n + p_∞(n)`, the quantitative form `p(m·k) ≤ s_m + p_∞(m)^k`, the two growth rates `wordEntropy`/`pInfEntropy` as `EReal`s, the existence of both limits, and the contrapositive **positive entropy ⇒ ¬(H)** (`plans/plan2-1047.html` §3.1) | — |
| `Confinement.lean` | **(new 2026-09-15)** **Proposition C(1)–(2)** — under (H) exactly two letters recur, so past `s_1` the word is two-letter and the other `#α − 2` letters are eventually omitted; and one of the two letters `a` has `aa` non-recurrent, so past `s_2` the tail avoids `aa` (the golden-mean SFT in base 2). `recLetters`, `ncard_recLetters` = `p_∞(1)`, `isEventuallyPeriodic_of_no_transition`, `exists_pair_forbidden_square` (`plans/plan2-1047.html` §3.2) | — |

Dependency shape: `Basic → {Rauzy → Degrees → OmegaLimit → TheoremZ, LemmaA0 → Cited → TheoremA,
Certificate, PeriodicOrbits → OmegaLimit}`; `Sliver` is independent of the rest (it is about a
sparse series, not a word). `PeriodicOrbits` imports `ForMathlib/Combinatorics/FineWilf.lean`;
`Rauzy` and `OmegaLimit` import `ForMathlib/Dynamics/SymbolicDynamics/Rauzy.lean`, and through it
the whole subshift root.

## The design decision worth recording

`p_∞(n, w) = p(n, tail w m)` for **every** `m ≥ s_n` (`BB47.pInf_eq_pComplexity_tail`). Because
`s_n ≤ s_{n+1}`, the *single* word `tail w s_{n+1}` computes `p_∞` at both level `n` and level
`n+1`. So the ordinary Morse–Hedlund machinery already in
`ForMathlib/Combinatorics/InfiniteComplexity.lean` applies verbatim to `p_∞`, and the rigidity
lemma [M3, Lem. 3.1] — that `p_∞` is strictly increasing — comes out in two lines instead of the
Rauzy-graph out-degree sum the note uses. This is the one place where the formalization is
*shorter* than the paper.

Positions are `0`-based throughout (matching `ForMathlib.SubwordComplexity.factor`); the notes
index words from `1`. The two conventions agree on `s_n` (both count the letters of the discarded
prefix) and on `r(n, w)` (both count the letters of the shortest prefix carrying a repetition).
A window starting at `1`-based position `i` starts at `0`-based `i − 1`, so the notes' conclusion
`s_n ≥ i` reads `i − 1 < horizon w n` in Lean.

## M1M2 — the combinatorial core and Theorems A/A′

| result | status | Lean name |
|---|---|---|
| Def. 2.1 — recurrent block, `p_∞` | ✅ | `Recurrent`, `recFactorSet`, `pInf` |
| Prop. 2.2 — the non-recurrent prefix exists and is attained | ✅ | `exists_nRecurrentFrom`, `horizon`, `recurrent_of_horizon_le`, `not_recurrent_pred`, `horizon_spec` |
| Lem. 2.3(i),(iii) — `L_n(z_m) = L_n^∞(w)` for `m ≥ s_n` | ✅ | `factorSet_tail_eq`, `pInf_eq_pComplexity_tail` |
| Lem. 2.3(ii) — `s_n ≤ s_{n+1}` | ✅ | `horizon_mono_succ`, `horizon_mono` |
| Lem. 2.3(iv) — `p_∞(n) ≥ n+1` (the 10.47 baseline) | ✅ | `succ_le_pInf` |
| Prop. 2.4 — `p_∞(n,w) = p(n, Ω(w))` | ✅ **complete** (2026-09-14, plan-subshift WP3+WP4+WP8): `Ω(u)` is a `Subshift α ℤ` built from its language, `𝓛ₙ(Ω(u)) = recFactorSet u n` on the nose, and the complexity identity is a theorem. `coe_omegaLimitSubshift_eq_omegaLimit` checks that `Ω(u)` really is the topological `ω`-limit set of **any** two-sided extension of `u` | `pInf_eq_complexity`, `language_omegaLimitSubshift_eq_recFactorSet`, `coe_omegaLimitSubshift_eq_omegaLimit`, `mem_omegaLimitSubshift_iff_forall_block_mem` |
| Def. 3.1 — the reduced Rauzy graph | ✅ | `edgeSrc`, `edgeTgt`, `recVerts` |
| Prop. 3.2 — `G'_n(w)` is strongly connected | ✅ | `reach_recFactorSet` (was `exists_walk`, retired 2026-09-14 by WP8; the proof is `ForMathlib`'s `reach_recurrentLanguage`) |
| Prop. 3.3 — degrees; one right-special and one left-special vertex | ✅ | `one_le_outDeg`, `one_le_inDeg`, `sum_outDeg`, `sum_inDeg`, `exists_unique_rightSpecial`, `exists_unique_leftSpecial`, `rightSpecial_of_minimal` |
| Rem. 3.4 / Ex. 3.5 — strong connectivity ⇏ transitivity, via `∏ₘ 0ᵐ1ᵐ` | ❌ **not formalized** | — |
| **Lem. 4.1 — the horizon bound** `p(n,w) ≤ s_n + p_∞(n,w)` | ✅ | `pComplexity_le_horizon_add_pInf` |
| **Lem. 4.2 = Lemma A0** — `r(n,w) ≤ p(n,w) + n ≤ s_n + n + p_∞(n,w)`; first half is [BK26, Lem. 2.2] | ✅ | `repLen_le_pComplexity_add`, `lemma_A0`, `hasRepetitionBy_horizon_add`, `pComplexity_add_le_lemma_A0_bound` |
| Thm. 5.1 = [AB07, Thm. 1] — `p(n,ξ,b)/n → ∞` | 📚 **cited axiom** | `AB.tendsto_pComplexity_div_atTop` (`AB/ComplexityLowerBound.lean`) |
| Thm. 5.2 = [BE08, Thm. 2.1] | 📚 **cited axiom** | `BugeaudEvertse.exists_pComplexity_gt` (`CITED/BugeaudEvertseComplexity.lean`) |
| Thm. 5.3 = [BK19, Thm. 10.4] | 📚 **cited axiom** ×2 | `transcendental_of_repLen_liminf`, `transcendental_of_repLen_limsup` |
| **Thm. 6.1 = Theorem A** | 🔗 proved from Thm. 5.1 | `theorem_A`; second route `theorem_A_via_repLen` (Thm. 5.3) |
| **Thm. 6.2 = Theorem A′** | 🔗 proved from Thm. 5.2 | `theorem_Aprime`; second route `theorem_Aprime_via_repLen` (Thm. 5.3) |
| Cor. 6.3 — minimal eventual complexity | 🔗 | `transcendental_of_minimal_pInf` |
| Cor. 6.4 — the whole `n+k` ladder, uniformly | 🔗 | `transcendental_of_pInf_linear`, `transcendental_of_pInf_add_const` |
| Cor. 6.5 — structure of hypothetical counterexamples | 🔗 | `structure_of_algebraic`, `structure_of_algebraic_log`, `exists_pInf_ge_of_algebraic` |
| Rem. 6.6, Rem. 6.7 (no irrationality measure) | 📝 prose | — |

`exists_pInf_ge_of_algebraic` is the conditional form of **Theorem W**: for an algebraic value,
either some `n` has `p_∞(n) ≥ n+2`, or the horizon is superlinear. Theorem W asserts the first
alternative unconditionally; that is open, and this is exactly the frontier of §4.4 of the plan.

## M3 — the structure theorem and the sliver

| result | status | Lean name |
|---|---|---|
| Prop. 2.1 (= M1M2 Prop. 3.2) | ✅ | `reach_recFactorSet` |
| **Lem. 3.1 — `p_∞` is strictly increasing; the (H) upgrade** | ✅ | `pInf_lt_succ`, `strictMono_pInf`, `pInf_eq_succ_of_le`, `pInf_eq_succ_of_frequently` |
| Lem. 3.2 — shape: `n+1` vertices, `n+2` edges, two simple cycles | 🟡 **half**: the counts and the two special vertices are `Degrees.lean`; the cycle decomposition is not | `rightSpecial_of_minimal` |
| Lem. 3.3 — at most one periodic orbit | ✅ **complete** (2026-09-14, WP5 + WP6 + WP8): `BB47.orbit_eq_of_pInf_eq` — under `p_∞(n,u) = n+1` any two periodic points of `Ω(u)` lie on the same orbit. `orbit_eq_of_pInf_succ_le` is sharper than the note: the hypothesis is needed only at the single level `p+q`, and the periods need not be least. **The shape lemma is not used**, only its degree half | `orbit_eq_of_pInf_eq`, `orbit_eq_of_pInf_succ_le`, `orbitClosure_eq_of_pInf_eq`; word half `exists_shift_of_periodic_of_factor_eq`, `factorSet_eq_of_periodic_of_factor_eq`, `recFactorSet_eq_of_periodic_of_factor_eq`, `pInf_eq_of_periodic_of_factor_eq` |
| Lem. 3.4 — a generic aperiodic point exists | ❌ **not formalized**; its *consumer* is, since 2026-09-14 — "every point has dense orbit, thus Ω is minimal" is `Subshift.isMinimal_iff_forall_orbitClosure_eq` (WP7). The note's own proof uses the right-special spine, not minimality; see gap 4 below | — |
| **Thm. 4.1 = Theorem B** — the two-branch structure theorem | ❌ **not formalized** | — |
| Cor. 4.2 — `Ω` transitive, `L(Ω)` balanced | ❌ not formalized; consumed as the hypothesis `BalancedAt` | `BalancedAt` |
| Thm. 5.1 = [CH73] classification | 📝 quoted in prose only | — |
| **Prop. 5.2 — the Coven–Hedlund non-Sturmian branch is impossible** | ✅ **the engine**; the [CH73]-normal-form bookkeeping that feeds it is prose | `mem_of_outClosed`, `not_properOutClosed` |
| Ex. 5.3 — `…000·0101…` | ❌ not formalized | — |
| Rem. 5.4 / Rem. 5.5 — the reversal-test correction | 📝 prose | — |
| Prop. 6.1 — breaks come in pairs; every defect looks the same | ❌ not formalized; consumed as the hypothesis `NoTripleBreakAbove` | `NoTripleBreakAbove` |
| Thm. 7.1 = Theorem C — the arithmetic normal form | ❌ not formalized (needs Thm. 4.1); taken as the hypothesis of `Sliver.lean` | `sparseValue` |
| **Thm. 8.1 = Theorem D (Ridout ⇒ `t_{J+1}/t_J → 1`)** | 🔗 **proved** from cited `ridout` | `theorem_D`, `theorem_D_ratio`, `irrational_of_one_lt_minpoly_natDegree` |
| Thm. 8.2 = Theorem E ([BBCP04] Thm. 7.1 in base `b`) | 📚 **cited axiom** | `bbcp_base_b` |
| Thm. 8.4 = Theorem F (regular patterns) | 📚 **cited axiom** for (ii); (i),(iii) follow from 8.2 | `nesterenko_theta` |
| **Cor. 9.1 — the surviving sliver, constraints (b1)–(b4)** | 🔗 assembled | `sliver`, `superlinear_of_gaps` |
| Rem. 9.2 — the horizon in branch (b) | 📝 prose | — |

## M4 — what a finite prefix can certify

| result | status | Lean name |
|---|---|---|
| **Prop. 2.1 — the block certificate** | ✅ | `lt_horizon_of_card_gt` |
| **Prop. 2.2 — exactness: the scan *computes* `s_n`** | ✅ | `card_image_ge_of_horizon` (with Prop. 2.1) |
| Prop. 2.3 — the balance certificate | ✅ (conditional on M3 Cor. 4.2, as in the note) | `lt_horizon_of_imbalance`, `lt_horizon_of_imbalance_all` |
| Prop. 2.4 — the period certificate | ✅ (conditional on M3 Prop. 6.1, as in the note) | `le_horizon_add_of_tripleBreak` |
| **Rem. 2.5 — the ceiling** | ✅ | `exists_minimal_extension`, `pInf_tail`, `horizon_graft_le` |
| Prop. 3.1 — reversal closure is automatic under (H) | ❌ not formalized (needs [CH73] and M3 Thm. 4.1) | — |
| Prop. 3.2 — the two branches are finitely indistinguishable | ❌ not formalized (needs Christoffel words, [Lot02] Ch. 2) | — |
| Cor. 6.1 — the measured certificate at `10⁹` digits | 🔢 the *statement* is `lt_horizon_of_card_gt` at `K = n+1`; the data is not in Lean | — |
| §6.2–§6.4, Tables 1–3 | 🔢 data | — |

`exists_minimal_extension` is worth singling out: it says that for **any** prefix of length `N`
and any recurrent word `f` of minimal eventual complexity, some infinite word agrees with the
prefix, has `p_∞(n) = n+1` for every `n`, and has `s_n ≤ N`. So no function of a finite portion
of the expansion of `√2` can ever refute `p_∞(n, √2, b) = n+1`. All three certificates bound
`s_n` from below; that is a theorem about finite data, not a limitation of the instruments.

## The seven cited axioms

Five carry `group "bugeaud_10_47"` and live in `BB47/`; two are general literature statements and
live where the repository keeps such things — [AB07] on its own root, [BE08] in `CITED/` beside
the other theorem of that paper the repository uses.

| axiom | source | consumed by |
|---|---|---|
| `AB.tendsto_pComplexity_div_atTop` | **[AB07] Thm. 1**, `p(n,ξ,b)/n → +∞` (`p`-adic Subspace) | `theorem_A` |
| `BugeaudEvertse.exists_pComplexity_gt` | **[BE08] Thm. 2.1**, the `(log n)^{1/11}` refinement (quantitative Subspace) | `theorem_Aprime` |
| `transcendental_of_repLen_liminf` | [BK19] Thm. 10.4, clause 1 (← [AB07] Thm. 5) | `theorem_A_via_repLen` |
| `transcendental_of_repLen_limsup` | [BK19] Thm. 10.4, clause 2 (← [BE08] Thm. 2.1) | `theorem_Aprime_via_repLen` |
| `ridout` | [Rid57], the `μ=1, ν=0` case, for algebraic **irrational** `y` | `theorem_D` |
| `bbcp_base_b` | [BBCP04] Thm. 7.1, transcribed to base `b` by [M3, Thm. 8.2] | `sliver` |
| `nesterenko_theta` | [Nes96] via [M3, Thm. 8.4(ii)] | `sliver` |

Faithfulness notes are in the respective docstrings. Two are worth repeating here. The [BK19]
hypotheses are transcribed in equivalent quantifier form rather than as `Filter.liminf` /
`Filter.limsup` (`liminf r(n)/n < ∞` ⟺ `∃ C : ℕ, r(n) ≤ C·n` for infinitely many `n`). And
Ridout's "only finitely many solutions `(A, m)`" is transcribed as `∃ m₀, ∀ m ≥ m₀, ∀ A` —
equivalent, because for fixed `m` the inequality already confines `A` to at most two values.

`ridout` carries `Irrational y` alongside `IsAlgebraic ℚ y`, and that is load-bearing rather than
decorative: for `y = A/b^m` the left-hand side is positive while the right-hand side vanishes, so
without it the axiom would be **inconsistent**. Downstream, `sliver` does not need the hypothesis
as an input — degree `> 1` already forces irrationality
(`irrational_of_one_lt_minpoly_natDegree`, proved).

Axiom audit (`#print axioms`):

    BB47.pInf_lt_succ, BB47.lemma_A0, BB47.reach_recFactorSet, BB47.mem_of_outClosed,
    BB47.exists_unique_rightSpecial, BB47.exists_unique_leftSpecial,
    BB47.lt_horizon_of_card_gt, BB47.card_image_ge_of_horizon,
    BB47.exists_minimal_extension, BB47.succ_le_pInf, BB47.superlinear_of_gaps,
    BB47.pInf_eq_complexity, BB47.orbit_eq_of_pInf_eq, BB47.orbit_eq_of_pInf_succ_le,
    BB47.mem_omegaLimitSubshift_iff_forall_block_mem
        → [propext, Classical.choice, Quot.sound]              (std3)

    BB47.pComplexity_le_horizon_add_pInf, BB47.repLen_le_pComplexity_add
        → [propext, Classical.choice, Quot.sound]              (std3)

    BB47.theorem_A, BB47.structure_of_algebraic, BB47.exists_pInf_ge_of_algebraic
        → + AB.tendsto_pComplexity_div_atTop                   (one axiom, nothing else)
    BB47.theorem_Aprime, BB47.structure_of_algebraic_log
        → + BugeaudEvertse.exists_pComplexity_gt
    BB47.theorem_A_via_repLen
        → + BB47.transcendental_of_repLen_liminf
    BB47.theorem_Aprime_via_repLen
        → + BB47.transcendental_of_repLen_limsup
    BB47.theorem_D, BB47.theorem_D_ratio
        → + BB47.ridout
    BB47.sliver
        → + BB47.ridout, BB47.bbcp_base_b, BB47.nesterenko_theta

## Why the gaps are gaps

1. ~~**M1M2 Prop. 2.4**~~ **— CLOSED 2026-09-14, see `BB47/OmegaLimit.lean`.** The reasoning that
   made it a gap, kept for the record: `p_∞ = p(·, Ω)` needs the two-sided shift space `α^ℤ`, its compactness,
   and the `ω`-limit set as a nested intersection. Mathlib has the pieces (Tychonoff, `Filter`)
   and, since 2025, a subshift *skeleton* — `Mathlib/Dynamics/SymbolicDynamics/Basic.lean`
   (633 lines: shift action, cylinders, patterns, forbidden sets, the `Subshift` structure,
   `LanguageOn`) — but the skeleton declares **no instances at all**, so a `Subshift` has no
   membership, no lattice, no coercion to a type and no induced `ℤ`-action, and above all there is
   no **language duality**: nothing says a subshift is determined by its language, which is the
   theorem every statement here would rest on. Nothing downstream in M1M2 or M4 uses `Ω` except as
   a frame: every use is of its *language*, which is `recFactorSet`. Scoped and priced in
   `plans/plan-subshift.html` (2026-09-14): ~1270 lines of `ForMathlib/Dynamics/SymbolicDynamics/`
   close this gap and gap 3. **As of 2026-09-14 that infrastructure exists** — WP1–WP6 of that plan
   are done (`Instances`, `Blocks`, `Duality`, `OmegaLimit`, `Periodic`, `Complexity`, `Rauzy`;
   2524 lines, 207 declarations, std3),
   so `Ω u` is a subshift, its language *is* `recFactorSet u`, and — WP4, same day —
   `complexity_omegaLimitSubshift : p(n, Ω u) = p_∞(n, u)` **is M1M2 Prop. 2.4**, with
   `BB47.pInf u n = pRecurrent u n` holding by `rfl`. `BB47.Recurrent` and
   `SymbolicDynamics.FullShift`'s `IsRecurrentFactor` are literally the same predicate. **WP8
   (2026-09-14) closed the gap on this side too**: `BB47.pInf_eq_complexity`
   (`BB47/OmegaLimit.lean`) is Prop. 2.4 in 10.47's vocabulary, and
   `BB47.coe_omegaLimitSubshift_eq_omegaLimit` is the topological half — `Ω(u)` is the `ω`-limit
   set of any two-sided extension of `u`, independently of the extension chosen. The same
   `ForMathlib` file also supplies the Morse–Hedlund floor `p(n) ≥ n+1` for an infinite subshift,
   which is `succ_le_pInf` in subshift form.
2. **M1M2 Ex. 3.5** (`∏ₘ 0ᵐ1ᵐ`) needs the run-structure analysis of that specific word. Feasible,
   but it is a counterexample to a false inference, not an ingredient.
3. ~~**M3 Lem. 3.3**~~ **— CLOSED 2026-09-14.** Lem. 3.3 (at most one periodic orbit) needed the **Fine–Wilf theorem** for words, which
   Mathlib did not have. Proved 2026-09-13 in `ForMathlib/Combinatorics/FineWilf.lean` (`fine_wilf`,
   with `exists_not_hasPeriodOn_gcd` showing the length bound sharp), and applied in
   `BB47/PeriodicOrbits.lean`. **Closed 2026-09-14** by WP5 + WP6 of `plans/plan-subshift.html`:
   `SymbolicDynamics.FullShift.orbit_eq_of_pRecurrent_eq` is Lem. 3.3 entire. WP5 supplied the
   separation (`disjoint_language_of_orbit_ne`) and the frame (`orbit`; a periodic orbit is finite,
   hence closed, hence its own `orbitClosure`); WP6 (`Rauzy.lean`) supplied the counting half, and
   needed only the *degree* part of [M3, Lem. 3.2], not its shape: at most one word of length
   `p + q` is right-special, so it misses one of the two disjoint orbit languages, which is then a
   non-empty proper out-closed set of vertices — impossible in a strongly connected graph
   ([M3, Prop. 5.2]). WP8, same day, added the BB47-side statement `BB47.orbit_eq_of_pInf_eq`
   (`BB47/OmegaLimit.lean`) and the sharper `orbit_eq_of_pInf_succ_le`.
   *Duplication, flagged under the house rule on existing formalizations and then **retired** by
   WP8:* `ForMathlib`'s `Rauzy.lean` restated three results the corpus already had for a one-sided
   word — `reach_recurrentLanguage` = `BB47.exists_walk`, `Subshift.not_properOutClosed` =
   `BB47.not_properOutClosed` (both `BB47/Rauzy.lean`), and `exists_isRightSpecial` +
   `eq_of_isRightSpecial` = `BB47.exists_unique_rightSpecial` (`BB47/Degrees.lean`). The layering
   forced it (`ForMathlib/` cannot import `BB47/`), so WP8 resolved it in the other direction:
   the word-level **proofs are deleted**, `BB47.exists_walk` with them (it is now
   `reach_recFactorSet`, a one-liner), `edgeSrc`/`edgeTgt` are `export`ed rather than redefined,
   and `BB47/Degrees.lean` lost its private arithmetic engine. The left mirrors
   (`IsLeftSpecial`, `exists_isLeftSpecial`, `add_two_le_ncard_of_isLeftSpecial`,
   `eq_of_isLeftSpecial`) were added upstream so that `exists_unique_leftSpecial` could be retired
   the same way as its right twin.
4. **M3 Lem. 3.4 / Thm. 4.1** (Theorem B) need, in addition, the compactness argument producing
   the generic aperiodic point, and the Morse–Hedlund identification of minimal aperiodic
   two-sided subshifts as Sturmian. The second is a genuine piece of symbolic dynamics.
   *(a) — infrastructure, **delivered 2026-09-14** by WP7 of `plans/plan-subshift.html`:*
   `ForMathlib/Dynamics/SymbolicDynamics/Minimal.lean` (442 lines, 25 declarations, std3) has
   minimal subshifts and uniformly recurrent languages, neither of which existed anywhere in
   Mathlib. Every non-empty subshift over a finite alphabet contains a minimal one
   (`Subshift.exists_isMinimal_le`, Zorn on the bundled lattice in the order dual + Cantor's
   intersection theorem), and minimal ⟺ every orbit dense ⟺ every legal word occurs in every point
   ⟺ the language is uniformly recurrent — the only step of that chain that costs anything being
   the last, which is paid for with compactness. Minimality is *also* Mathlib's
   `AddAction.IsMinimal ℤ Y` (`isMinimal_iff_addAction`), so `Dynamics/Minimal.lean` now applies to
   subshifts. **But the plan's reading of where this sits in [M3] was wrong, and the correction
   matters:** Lem. 3.4's own proof uses no minimality at all — it builds the left-infinite
   right-special spine ρ, takes limit points, and runs a gcd argument — and under (H) `Ω(u)` need
   *not* be minimal, since [M3, Thm. 4.1(b)] (the skew branch) has `Ω = Orb(x) ∪ P` with `P` a
   periodic orbit. What `Minimal.lean` serves is the step **after** Lem. 3.4: Thm. 4.1(a) closes
   with "every point of Ω has language L(Ω), hence dense orbit; thus Ω is minimal", which is
   `isMinimal_iff_forall_orbitClosure_eq` verbatim, and then quotes "a minimal aperiodic subshift
   with p(n)=n+1 is Sturmian" — so WP7 is the **interface to 4(b)**, not a route into 4(a).
   Lem. 3.4's *second* statement is cheap and never needed WP7: for aperiodic `x ∈ Ω`,
   `orbitClosure x` is infinite, so `p(n, orbitClosure x) ≥ n+1 = p(n,Ω) ≥ p(n, orbitClosure x)`,
   and `Subshift.ext_language` finishes; it is unwritten only because it is a BB47-side statement
   under (H).
   *(b) — the Coven–Hedlund classification itself: out of scope of that plan by design, and a
   project in its own right.*
5. **M4 Prop. 3.2** (finite indistinguishability) needs Christoffel words and the theorem that
   every finite balanced word is a factor of one ([Lot02] Ch. 2). `ForMathlib/Combinatorics/
   Sturmian.lean` has the bispecial criterion but not the mechanical-word side.

None of these is a soundness risk for the paper: each is a *quoted or classical* statement whose
Lean absence is an infrastructure gap, and each is flagged as such in the table above.

## Reuse from the rest of the corpus

* `ForMathlib/Combinatorics/InfiniteComplexity.lean` — `factor`, `factorSet`, `pComplexity`,
  `IsEventuallyPeriodic`, `pComplexity_lt_succ_of_not_isEventuallyPeriodic`. This is the whole
  Morse–Hedlund engine, and `pInf_eq_pComplexity_tail` is what plugs `p_∞` into it.
* `ForMathlib/Combinatorics/Sturmian.lean` — `succ_le_pComplexity` (the complexity floor),
  `IsSturmian`.
* `ForMathlib/Combinatorics/FineWilf.lean` — new, written for this root: `HasPeriodOn`,
  `fine_wilf`, `List.fine_wilf`, the sharpness witness `exists_not_hasPeriodOn_gcd`, and
  `eq_shift_of_periodic_of_factor_eq`, which is the generic engine behind `PeriodicOrbits.lean`.
* `ForMathlib/Dynamics/SymbolicDynamics/` — new, written for this root (`plans/plan-subshift.html`,
  2026-09-14): the subshift API on Mathlib's skeleton, **8 files / 3046 lines / 238 declarations**,
  sorry-free and std3, the whole plan (WP1–WP8) spent. `BB47/Rauzy.lean` and `BB47/OmegaLimit.lean`
  import it; `Ω u` is `omegaLimitSubshift u` and `BB47.recFactorSet u = recurrentLanguage u` by
  `rfl`, so it is not a translation layer but the same objects under two names. `Minimal.lean`
  (WP7) has no BB47 consumer yet by design — it opens gap 4(a) rather than closing anything.
* `AB/ExpansionsInIntegerBases.lean` — `AB.baseValue`. `BB47.value` is a thin wrapper, so this
  root and the Adamczewski–Bugeaud root name the same real number, and the two cited
  Subspace-theorem consequences sit side by side as the plan's §8 asked.

## References

Keys as in `BB47/L0.md`: [Bug12], [AB07], [BE08], [BK19], [BKK26], [CH73], [FW65], [MH38], [Lot02],
[Rid57], [BBCP04], [Nes96], [FM97]. In-repo: [M1M2] = `BB47/M1M2.tex`, [M3] = `BB47/M3.tex`,
[M4] = `BB47/M4.tex`.

## Addendum, 2026-09-13 — the rewiring

`BB47/L0.md` §L0(ii-bis)c records the horizon bound `p(n,w) ≤ s_n + p_∞(n,w)`, which makes the
hypotheses of Theorems A and A′ hypotheses on the *ordinary* complexity. `M1M2.tex` §§4–6 and this
inventory were rewritten accordingly on 2026-09-13:

* **Each headline theorem now rests on exactly one named literature theorem.** `theorem_A` →
  `AB.tendsto_pComplexity_div_atTop` = [AB07] Thm. 1, and nothing else. `theorem_Aprime` →
  `BugeaudEvertse.exists_pComplexity_gt` = [BE08] Thm. 2.1, and nothing else. Previously both went
  through the packaged criterion [BK19] Thm. 10.4, which is itself derived from those two.
* **Nothing was lost.** The old proofs survive as `theorem_A_via_repLen` and
  `theorem_Aprime_via_repLen`; the [BK19] axioms are still live and still used.
* **One API change.** The primary theorems now take `Irrational (value b w)` where they took
  `¬ IsEventuallyPeriodic w`, matching [M1M2, §6] ("Throughout this section `ξ` is an irrational
  real number"). The `_via_repLen` twins keep `¬ IsEventuallyPeriodic w`, which in Lean is the
  formally weaker hypothesis — the two are equivalent for digit words, but **Mathlib has no
  characterisation of rationals by eventually periodic base-`b` expansions**. That is a second
  upstream gap this project could fill; the first, Fine–Wilf, was filled the same day (see the
  next addendum), so it is now the only one left.
  `exists_pInf_ge_of_algebraic` carries both, because it needs `¬ IsEventuallyPeriodic w` for
  `succ_le_pInf`.

## Addendum, 2026-09-13 (b) — Fine–Wilf, and what it bought

`ForMathlib/Combinatorics/FineWilf.lean` (420 lines, 20 declarations, 2 of them private, std3)
closes the first of the two upstream gaps this root had identified. It proves the periodicity
lemma of [FW65] in the window form the notes use,

    HasPeriodOn u L p → HasPeriodOn u L q → p + q ≤ L + gcd p q → HasPeriodOn u L (gcd p q)

by strong induction on `p + q` — the Euclidean algorithm run on the two periods. The one place the
textbook proof needs care is the step `q = p + d` with `d = gcd p q`, where subtracting the smaller
period leaves nothing to induct on; that case is handled directly, by a chain of `p/d - 1` steps
each of which is legal because `L ≥ 2p`. The file also carries

* `List.fine_wilf` — the same for `l[i]?`, a one-line specialisation, which is the shape Mathlib
  would want;
* `exists_not_hasPeriodOn_gcd` — the length bound is **sharp**: `a^(p-1) b a^(p-1)` has periods `p`
  and `p + 1` at length `2p - 1`, one short of the theorem's `p + (p+1) - 1`; and
  `exists_periodic_not_shift` says the same at the level of orbits — the two periodic extensions of
  that word share those `2p - 1` letters and are not shifts of one another. So the `n ≥ q₁ + q₂`
  of [M3, Lem. 3.3] is exactly right and not a convenience;
* `periodic_gcd`, and `eq_shift_of_periodic_of_factor_eq` — two globally periodic words that agree
  on one window of length `p + q` agree everywhere and both have period `gcd p q`.

`BB47/PeriodicOrbits.lean` (181 lines, 9 declarations, std3) is the application: the word half of
[M3, Lem. 3.3]. Two periodic words sharing one block of length `p + q` are shifts of one another
(`exists_shift_of_periodic_of_factor_eq`), hence have the same factor set at every length, the
same recurrent factor set, and the same `p_∞` — the lemma's conclusion `P₁ = P₂`, stated in the
vocabulary of Problem 10.47 rather than in that of subshifts. The file also records that a
periodic word has every block recurrent, so for it `p_∞ = p` and the horizon is `0`
(`horizon_eq_zero_of_periodic`).

No hypothesis of the note survives into these statements: no complexity bound, no finite alphabet,
no `ω`-limit set. That is the point — the half of Lem. 3.3 that was blocked was blocked on a
missing *general* theorem, and the other half was blocked on missing *infrastructure* (the subshift
API). ~~which is gap 1 above and unchanged~~ **Both are now closed** (2026-09-14): see the addendum
below.

## Addendum, 2026-09-14 — the subshift API, and gaps 1 and 3

`plans/plan-subshift.html` was written, executed and spent in a day. `ForMathlib/Dynamics/
SymbolicDynamics/` is now **8 files, 3046 lines, 238 declarations**, sorry-free and std3:
`Instances` (order and action instances on Mathlib's `Subshift`, which had none), `Blocks` +
`Duality` (the language–subshift correspondence, both directions), `OmegaLimit` (`Ω u` and the
topological identity), `Periodic` (periodic points and the separation of two periodic orbits),
`Complexity` (subshift complexity, the plateau theorem, Morse–Hedlund), `Rauzy` (the Rauzy
graph, its exclusion engine and the counting lemma) and `Minimal` (minimal subshifts and
uniformly recurrent languages, WP7).

For this root the consequences are three:

* **Gap 1 is closed.** `BB47.pInf_eq_complexity` is M1M2 Prop. 2.4, and
  `BB47.coe_omegaLimitSubshift_eq_omegaLimit` says `Ω(u)` is Mathlib's `ω`-limit set of any
  two-sided extension of `u`. The bridge is definitional throughout: `BB47.Recurrent` *is*
  `IsRecurrentFactor`, `recFactorSet u` *is* `recurrentLanguage u`, `pInf u n` *is*
  `pRecurrent u n`.
* **Gap 3 is closed.** `BB47.orbit_eq_of_pInf_eq` is M3 Lem. 3.3, and `orbit_eq_of_pInf_succ_le`
  is sharper than the note (the hypothesis is used at one level only, and the periods need not be
  least). The shape lemma [M3, Lem. 3.2] is *not* needed — only its degree half.
* **The word-level duplicates are retired, not kept.** `BB47/Rauzy.lean` and `BB47/Degrees.lean`
  keep every interface they had, but the proofs are gone: `BB47.exists_walk` is deleted in favour
  of `reach_recFactorSet`, `mem_of_outClosed` is one line on `mem_of_reach`, `edgeSrc`/`edgeTgt`
  are `export`ed rather than redefined, and the degree-sum proof of the unique special block is
  replaced by `exists_isRightSpecial`/`eq_of_isRightSpecial` through the bridge
  `isRightSpecial_iff_two_le_outDeg`. The one remaining degree sum is what fixes the exact values
  `2` and `1`, which is the only thing `ForMathlib` does not say.

* **Gap 4(a) is opened, not closed** (WP7, same day). `Minimal.lean` supplies minimal subshifts
  and uniformly recurrent languages, and `exists_isMinimal_le_omegaLimitSubshift` says `Ω(u)`
  contains a minimal subsystem with uniformly recurrent language — for *every* `u`, with no
  complexity hypothesis. It has no BB47 consumer, deliberately: writing WP7 showed that [M3,
  Lem. 3.4]'s proof does not use minimality, and that under (H) `Ω(u)` need not be minimal at all
  (the skew branch of Thm. 4.1 has a periodic orbit in it). What the file serves is the step
  *after* Lem. 3.4 and the vocabulary in which gap 4(b) is stated. See gap 4 above.

What is *not* closed, and was never in that plan: the Coven–Hedlund classification (gap 4's second
half), M1M2 Ex. 3.5, and M4 Prop. 3.2's Christoffel words.

## Addendum, 2026-09-14 (b) — Theorem Z is machine-checked

`BB47/TheoremZ.lean` (372 lines, 23 declarations, std3, no cited axiom) proves **Theorem Z** of
`BB47/af.md` §2, merged as `plans/plan2-1047.html` §3.1. This is the first result in the root that
does **not** come from the three papers `M1M2/M3/M4`: it belongs to the *postponed* note M5.

    BB47.theoremZ  :  wordEntropy u = pInfEntropy u
    -- i.e.  lim (log p(n,u))/n  =  lim (log p_∞(n,u))/n   for every word over a finite alphabet

Both growth rates are `ExpGrowth.expGrowthSup` of the ℕ-valued count cast into `ℝ≥0∞`, valued in
`EReal` — the same shape Mathlib's own `partitionTopEntropy` uses. By `pInf_eq_complexity`,
`pInfEntropy u` **is** the topological entropy of `Ω(u)` (`pInfEntropy_eq_omegaLimit`).

**The proof that got formalized is not either of the note's two.** `af.md` offers the variational
principle (needs invariant measures) and a Rauzy-walk count (needs `λ_m` and `h_m ↓ h_top`).
Neither is necessary. The whole theorem follows from one counting bound:

    BB47.pComplexity_mul_le_horizon_add_pInf_pow  :  p(m·k, u) ≤ s_m + p_∞(m, u)^k    (∀ m, k)

*Proof.* A length-`(m·k)` block at a position `≥ s_m` splits into `k` consecutive length-`m`
blocks, each again at a position `≥ s_m`, hence each recurrent: at most `p_∞(m)^k` of those. Every
other length-`(m·k)` block occurs only at the `< s_m` early positions: at most `s_m` of those. ∎

The asymmetry is the point: the additive constant `s_m` depends on `m` alone, the exponential on
`p_∞` alone, so dividing by `m·k` and letting `k → ∞` kills the constant and gives
`h(u) ≤ (log p_∞(m))/m` for **every** `m ≥ 1` (`wordEntropy_le_log_div`). Hence `h(u)` is below the
*liminf* of `(log p_∞(n))/n`, while `p_∞ ≤ p` puts it above the *limsup* — so all four growth rates
collapse at once and both limits exist (`tendsto_log_pComplexity_div`, `tendsto_log_pInf_div`).
**No Fekete argument is used**: the `m`-fold bound does the work of the subadditivity lemma.

New in `ForMathlib` for this: `ForMathlib.SubwordComplexity.pComplexity_add_le` —
`p(a+b) ≤ p(a)·p(b)` for a one-sided word, the companion of `Subshift.complexity_add_le` — and its
`k`-fold form `pComplexity_mul_le`, plus `factor_comp_castAdd`/`factor_comp_natAdd` (splitting a
factor into prefix and suffix) and `monotone_pComplexity`. `pComplexity_zero` moved from
`Sturmian.lean` to `InfiniteComplexity.lean`, where `pComplexity` is defined; nothing else changed.

### What it buys Problem 10.47

* `wordEntropy_eq_zero_of_pInf_eq_succ` (and `..._of_frequently`, stated the way [M3] states (H)):
  under the standing hypothesis the **whole** expansion has zero entropy, `p(n,ξ,b) = e^{o(n)}` —
  although (H) constrains `p(n, ξ, b)` not at all at any fixed scale, since `s_n` is free. The
  explicit form is `pComplexity_le_of_pInf_eq_succ`: `p(N) ≤ s_m + (m+1)^k` whenever `N ≤ m·k`.
* `exists_pInf_ne_succ_of_wordEntropy_pos` is the contrapositive, and it is the reason to care:
  **Conjecture E ⇒ Problem 10.47**. Any proof that an algebraic irrational has positive-entropy
  base-`b` expansion — much weaker than normality, implied by it — settles 10.47 outright, in the
  stronger form "`p_∞` is not subexponential". Through [M3, Lem. 3.2] the same argument puts 10.47
  below Mahler's missing-digit problem. 10.47 is the lowest rung of a ladder that is open at every
  rung, and the file says so in Lean.

One auxiliary lemma is of general interest and has no Mathlib home yet:
`BB47.expGrowthSup_natCast_succ`, that a sequence of exactly linear growth has exponential growth
rate `0`. It is proved by a **doubling trick** — `v(2n) ≤ 2·v(n)` gives `2x ≤ x` for the growth
rate `x`, and `0 ≤ x ≤ log 2 < ⊤` forces `x = 0` — which avoids any analysis of `log n / n`.

## Addendum, 2026-09-15 — what `BB47/M5.tex` quotes, and what it does not

The Theorem Z note (`M5.tex`, 17 pp.) is machine-checked exactly through its §3, and not beyond:

| M5 result | Lean |
|---|---|
| Lem. 2.1 counting lemma `p(mk) ≤ s_m + p_∞(m)^k` | `BB47.pComplexity_mul_le_horizon_add_pInf_pow` |
| Lem. 2.3 growth rate along an arithmetic progression | `Monotone.expGrowthSup_comp_mul` (Mathlib) |
| Thm. 1.1 Theorem Z | `BB47.theoremZ` |
| both limits exist | `BB47.tendsto_log_pComplexity_div`, `BB47.tendsto_log_pInf_div` |
| Prop. 3.1 horizon–complexity trade-off | `BB47.pComplexity_le_horizon_add_pInf_pow` |
| Cor. 3.2 regimes (i)–(iii) | (iii) is `BB47.wordEntropy_eq_zero_of_pInf_eq_succ`; (i)–(ii) are not formalized |
| Thm. 4.1 zero entropy under (H) | `BB47.wordEntropy_eq_zero_of_pInf_eq_succ`, `_of_frequently` |
| Cor. 4.5 Conjecture E ⇒ 10.47 | `BB47.exists_pInf_ne_succ_of_wordEntropy_pos` |
| Prop. 4.2 the planted word | not formalized (needs de Bruijn words; `Sturmian.lean` has the tail) |
| Prop. 4.6(1)–(2) eventual confinement | **formalized 2026-09-15**, `BB47/Confinement.lean`: `eventually_two_letters`, `ncard_omitted`, `exists_forbidden_square`, `exists_pair_forbidden_square` |
| Prop. 4.6(3) nested self-similar sets | not formalized — needs [M3, Lem. 3.2] and first-return decomposition; the IFS side is absent from the corpus |
| §5 two-base rigidity | not formalized; Lem. 5.1 is reachable, Thm. 5.3 would be a cited axiom |
| §6 landscape | prose; the costing is not a theorem |

The one status change: `missing-lean.txt` said Proposition C waits on M3 Cor. 4.2 (balance) and
through it the Theorem-B chain. Writing the proof showed it does not — `p_∞(2)=3` plus
aperiodicity is enough, because a non-recurrent `01` or `10` forces an eventually periodic tail.
**Done the same week**: `BB47/Confinement.lean` (2026-09-15, 368 lines, 21 declarations, std3, no
cited axiom) proves C(1) and C(2) from `pInf`, `horizon` and `IsEventuallyPeriodic` alone. The
engine is `isEventuallyPeriodic_of_no_transition`: a word that past some point reads only `a`, `b`
and never `a` then `b` is eventually periodic — which is what forbids a *mixed* `2`-block from
being the non-recurrent one, so the missing block is a square.

For §5, `ForMathlib/Topology/MetricSpace/BoxDimension.lean` already carries upper box dimension
and `Metric.dimH_le_upperBoxDim`, so M5 Lem. 5.1 (cover the orbit closure by the `p(n)` closed
`b`-adic intervals of rank `n`) is formalizable with what exists. Furstenberg's dimension formula
is not needed anywhere in the note — only that inequality.
