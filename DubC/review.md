I've read the full plan. Before writing the analysis, let me independently verify its two most load-bearing numerical claims — the first-moment crossing table and the Perron-root/core computations — since the entire strategy now hangs on them.
The first-moment table checks out exactly, including the crossing between y=41 and y=43. Now the 8-state certificate and the y=19 rung of the ladder:
Both match. Now the serious one — the y=19 ladder rung (modulus M = 9 699 690, claim: λ(19) = 1.102168, core of 48 548 states):
All verification is done — and it materially shapes the critique, so I'll lead with it.

## 0. Independent verification (what I re-ran before judging anything)

| Claim in the plan | My independent check | Result |
|---|---|---|
| First-moment table λ̄(y) = 7∏(1−1/p), crossing at y = 43 | Recomputed exactly (rational arithmetic) | **Exact match**; λ̄(41) = 1.0157 → λ̄(43) = 0.9920 |
| 8-state automaton, λ = 1.51519; r = 14 spurious loop | Rebuilt from the transition rule, eigenvalue via ARPACK | **Confirmed** (1.51519232…); r = 14 is indeed a detached fixed point |
| y = 19 rung: λ(19) = 1.102168 | Full core-pruning over all 9 699 690 residues + power iteration on the core | **Confirmed to all six digits** (1.102168) |
| "Exactly one branching SCC" through y ≤ 29 | SCC decomposition of the y = 19 core | **Confirmed**: 28 cyclic SCCs, exactly one branching (52 392 states, ρ = 1.102168); the all-6 loop r ≡ −1 sits alone as a self-loop, exactly as G-5 describes |
| Core size at y = 19 = 48 548 | Three natural definitions tried | **Not reproduced**: forward core 647 052; bi-infinite core 53 218; recurrent states 52 793. See flaw (c) below |

Bottom line: the entropy-bearing numbers are solid — I now believe the y ≤ 19 mathematics. The one thing that does not reproduce is an auxiliary count, which is exactly the kind of item the plan's own M2′ exists to catch.

---

## 1. Overall strategy — assessment, and the "huge computations" question

### What is genuinely good

**The C(P) reframing is the plan's real invention, and it is provably stronger than what it replaces.** The old §C.1 idea (find an unavoidable divisor set) was dead on arrival; the certificate C(P) — zero-entropy core, i.e. no SCC containing two cycles — is strictly weaker and suffices because periodic survivors die to the Euler return. The plan's own controls contain the cleanest proof that this gap matters: for b = 5, [DubOst06] Thm 4 proves *no unavoidable set can ever exist* (b−1 = 4 not squarefree), yet the ladder shows C({2,3,5}) **holds** for b = 5. So the certificate method succeeds on a base where the divisor-set method is provably impossible. That observation deserves a prominent remark in the paper — it is the one-paragraph answer to "why is this not just DN05 again."

**Risk architecture is excellent.** The gate discipline (read before claiming) killed two dead targets (T1, T6) before any writing; the three-outcome milestone graph ((i) solve, (ii) anti-Conjecture-3 evidence, (iii) metric paper) guarantees a publishable result on every branch; the b = 10 consistency test is a textbook sanity check — the first moment *fails* exactly where [DubOst06] Thm 4 says it must, which both validates the heuristic's domain and shows the authors understand why.

**The Lean layering is well-designed**: untrusted witness data (a corrupt entry can only make the check fail, never prove a falsehood), quarantined `native_decide`, `#print axioms` at every use site, and the formalization actually improved the mathematics (rationality of ξ dropped out — eventually periodic digits feed [Dub09] Thm 4 directly). That is formalization pulling its weight.

### Where the strategy is weak

**(a) Single point of failure, and replication is sequenced too late.** The entire "1967 problem solved for a = 7" claim rests on one fact: zero branching SCCs at y = 31. The four implementations are all by the same author — correlated error (a shared wrong admissibility encoding, a shared off-by-one in digit pinning) is the dominant risk, and my y = 19 exercise shows how easily definitional drift creeps in (see flaw (c)). M2′ (independent replication + referee read) should be a *hard precondition* for M3′, and the certificate data should be timestamped and public early — anyone can now redo this computation (I reproduced the y = 19 rung in about two minutes of CPU), so priority protection and verification point the same way: publish the artifact.

**(b) The heuristics have a mixed track record and must be quarantined in the write-up.** The §4 "structural claim" was argued from a provably wrong heuristic (marginal cost O(1/p), crossing "only in the infinite limit") — the plan honestly records this. But the replacement reasoning ("deficit stabilizes near 0.90, crossing in [23,31]") is a four-point extrapolation that happened to land; and the annealed first moment λ̄ is *not* the Perron root — it treats the per-prime constraints as independent at stationary frequency, which they are not (the deficit itself is the correlation). In the paper these belong in a "numerical evidence" section, nowhere near the theorem statements.

**(c) The title of milestone M3′ is wrong — this is not an unavoidable set.** "An unavoidable set of divisors for base 7" directly contradicts the plan's own central distinction: the core at y = 31 is *nonempty* (371 555 states, 849 cycles), so {p ≤ 31} is precisely **not** unavoidable — it merely has a zero-entropy core. A referee who knows [DubOst06] will pounce on this, and it muddies the paper's best idea. Title it after the certificate ("A zero-entropy certificate…" / "Composites among [ξ7ⁿ] via a finite coprimality certificate").

### Can the results be achieved without huge computations?

Mostly, yes — and the plan itself proved it: the ladder cut the obligation from 2×10¹¹ residues to 2.2×10⁷, and the C-side run is minutes on a workstation. The residual "hugeness" is entirely in making the last check (CoreClosed) machine-verifiable, and there the plan leaves two cheaper options on the table:

- **Collatz–Wielandt instead of ranks and SCCs.** For a 0–1 digraph, C(P) ⟺ ρ(core) ≤ 1, and ρ ≤ 1 is certified by a single positive vector w with A w ≤ w — verification is one pass over the edges, no Tarjan, no condensation height, no 500-deep rank arrays. The plan *mentions* the CW certificate but then builds the much heavier rank/peeling engine anyway. Existence of w is guaranteed when C(P) holds (Perron vector per cyclic SCC, weights inflated upstream along the condensation DAG); the witness still has to be computed, but the *check* becomes trivial and kernel-friendly.
- **Braun trees instead of Array literals.** The measured kernel wall (Array reduces as a List, O(n) indexing, 6.7×10¹⁰ steps) assumes arrays/lists. A Braun tree gives structural O(log n) lookup with plain kernel reduction: 182 092 queries × ~19 steps ≈ 3.5M kernel steps — comfortably feasible. This could move CoreDet (and plausibly CoreClosed) out of `native_decide` into the three-axiom world, removing the plan's one trust-base exception at a stroke.

A genuinely computation-free proof would require understanding *why* mod 31 kills the last branching SCC — the plan's own analysis (the mod-3 translation keeps {2,4,6} branching factor 2 alive at every earlier stage, so no small-modulus collapse exists) says the y = 31 threshold is arithmetic-accidental. Verdict: moderate computation is essential and irreducible, but it is small, and the final certificate can be made third-party-checkable in seconds.

---

## 2. Technical flaws

**(a) Title/claim error (M3′):** "unavoidable set" — see §1(c). Not cosmetic; it mislabels the contribution.

**(b) Core-size discrepancy.** The plan's 48 548 at y = 19 matches none of forward core (647 052), bi-infinite core (53 218), or recurrent states (52 793) under a faithful reimplementation of the stated transition rule, while λ matches exactly. Most likely a definitional variant (ladder-candidate count vs. pruned core), but the paper must define "core" once and make every printed number consistent with it — this is precisely the class of error a referee's re-run would surface.

**(c) Reducible-graph Rayleigh artifact.** The plan flags it correctly for whole-core power iteration (λ ≈ 1.0002 ≠ entropy), but the y = 31 row of the results table should be audited to confirm no float-based λ estimate contaminated it anywhere; the float-free certificate ("branching = 0") is the only form that should appear in print.

**(d) T4 is now understated, not just unresolved.** Once λ(31) = 1 holds, dim_H S₃₁ = log 1/log 7 = **0 — proved, not conjectured** — and since the survivor set {ξ : [ξ7ⁿ] prime cofinitely} ⊆ S₃₁, the "effective Koksma" headline (Hausdorff dimension zero) is already a theorem modulo the computation. Moreover a zero-entropy SFT has *polynomial* word growth, so effective rates are available, not just dimension zero. The plan still carries T4's "conjecturally → 0" framing from before the reversal.

**(e) A garbled heuristic in §5.** "The ∑1/p = ∞ heuristic predicts probability 0 of an infinite chain" conflates two different things. For a fixed chain p_{n+1} = 7p_n + d, the relevant series is ∑ 1/log p_n with p_n ~ 7ⁿ, and the probability that *all* terms are prime vanishes super-exponentially — so any given chain dies almost surely. The existence question is over uncountably many starts, which is exactly where the entropy lives. N3's branching-process framing (used later in the plan) is the right one; §5 should be made consistent with it.

**(f) The all-6 loop is an eternal cycle, and that re-arms G-5.** r ≡ −1 (mod M) is a fixed point (d = 6), and −1 is a unit modulo *every* prime — so this loop lifts through every rung forever. It is harmless to the C-route (periodic ⇒ Euler return), but it means cores *never* literally empty unless the spurious non-floor representation is quotiented out. The moment anyone attacks [DubOst06] Conjecture 3 (cores never empty) using this machinery, G-5 stops being "demoted" and becomes load-bearing again. The plan should say this explicitly — right now the demotion reads as final.

**(g) b = 10 phrasing.** The control shows C(P) *fails* for b = 10 (branching grows 1→2→4→8) — but this is not evidence against Conjecture 2 at b = 10: periodic/constant survivors die to the return trick, and the constant-digit evasions are exactly such survivors. §0-ter states this correctly; §0-bis's "open in both directions" should be worded with the same care so a reader doesn't take the C-failure as negative evidence for Conjecture 2.

**(h) Minor:** the kernel-performance numbers (118 kB/step, 43 GB, 1.5 s/lookup) are machine- and version-specific and will date; the 1–2 week estimate for the unbuilt CoreClosed engine is optimistic against its own specification (peeling over 5 rungs, ~66 M edges, ~1 GB, plus condensation height).

---

## 3. Strategies that turn the plan's results into new results

**A. Classify the 849 cycles — turn the certificate into a structural theorem.** Each cycle is an explicit periodic avoiding word, i.e. an explicit family of rationals whose [ξ7ⁿ] dodge every p ≤ 31 forever. Extract periods, block values, residues; publish "every ξ avoiding {p ≤ 31} has digits eventually equal to one of these 849 patterns." That is a human-readable theorem, an independent second proof route (check each pattern individually), and it converts "trust a computation" into "inspect a classification."

**B. Effective Forman–Shapiro at b = 7.** Transient depth into the core is bounded by the pruning depth, so eventual periodicity comes with *explicit* preperiod and period bounds; the Euler return time is ord_p(7^L) for an explicit p = x_N. Combine: an effective statement "a composite appears at an index bounded explicitly in terms of the first prime term." Nobody has any effective version of these results.

**C. Attack Conjecture 3 at b = 7 by cycle-lifting — with a built-in win-win.** A cycle of period L and block value c lifts through a new prime q iff (7^L − 1)r̃ + c ≡ 0 (mod q) has a solution whose whole orbit avoids 0 mod q — a finite check per (cycle, q), and q ∤ 7^L − 1 makes the solution unique. Track the lift tree of each genuine cycle (quotienting the eternal −1 loop, per flaw (f)): if some cycle survives every q, cores never empty and Conjecture 3(7) is *proved* via Kőnig's lemma; if some q kills all genuine cycles, that q extends the certificate and strengthens the main theorem. Either branch is a paper.

**D. The metric paper, upgraded from conjecture to theorem.** dim_H {ξ : [ξ7ⁿ] prime cofinitely} = 0 unconditionally (flaw (d)), polynomial word-growth bounds, the certified row-sum decay table (FKL-style inequalities instead of numerics), packing-dimension refinements. This was the "fallback paper"; the y = 31 result makes its headline unconditional.

**E. The base atlas y*(b) as a research program, not bulk.** The ladder is base-generic. Every base with the ladder crossing resolves Forman–Shapiro for that integer base (b = 8 next, first-moment crossing near y ≈ 79; then 11, 12, 14, 15, 17, 18, 20, …). State the conjecture the data suggests: y*(b) exists for every b with squarefree b−1 and grows roughly like exp(b e^{−γ}) (matches b = 7: ~51 first-moment vs. actual 31; b = 8: ~89 vs. plan's ~79 — phrase loosely, the deficit grows with b).

**F. b = 10 via the [Dub09] Sturmian-collapse machinery.** C fails there, but that is the exact configuration of [Dub09] Thm 3 (entropy-0 survivors of higher complexity, killed by word combinatorics rather than periodicity). Compute the factor complexity of the b = 10 branching core; if a complexity collapse à la Lemma 8 occurs, the §5–6 permutation-word calculus adapts. This is the natural next frontier and the plan owns all the tools.

**G. The bridge note.** [MPP+24] proves the chain hypothesis for b ≤ 6 without citing Dubickas, Forman–Shapiro, or knowing their conjecture *is* [DubOst06] Conjecture 1; the Dubickas lineage doesn't cite walking-to-infinity. A short note handing both communities the equivalence — plus the b = 5, 6 composites theorems the walkers don't know they have, plus the b = 7 resolution — is cheap, high-citation, and stakes the priority claim publicly before [KL26]'s announced right-truncation paper appears.

**H. Chain-counting with the transfer spectrum (N3/N6), differentiated.** Right truncations are chain-correlated, so the second moment is governed by the transfer spectrum rather than progression estimates — a real technical differentiator from [KL26]. But decide contact-vs-differentiate before M0′-scale investment, as the plan says; the scoop risk here is the one live one.

**I. Composite runs.** [MPP+24] Thm 2.6 (arbitrarily long composite runs via φ-composed Euler return) applied to the periodic survivors strengthens [Dub09] Thm 4's "infinitely often" to "arbitrarily long runs of composites among [ξ7ⁿ] whenever the digit word is eventually periodic" — a garnish theorem that costs nothing and reads well.

**J. The certificate framework as a reusable artifact.** The ladder lemma, rank certificates, compressed-core form, and untrusted-witness/native_decide-quarantine design are a general template for certified finite computations in number theory (unavoidable sets for rational bases, corpus siblings like the ceiling-recurrence RB/). A short methodology note plus the data and a ~100-line standalone verifier under a DOI converts the weakest strategic point (single-author computation) into the strongest (checkable artifact).

**K. Rational bases.** The return engine is base/shift-uniform and the ladder doesn't care that b is an integer; the same certificate route can settle [ξ(b/c)ⁿ] cases where DN05's unavoidable-set method fails — unclaimed territory adjacent to everything already built.

---

### One-paragraph verdict

The strategy's spine — replace unavoidable sets with a zero-entropy-core certificate, reduce to a published theorem ([Dub09] Thm 4), and make the one hard step a checkable finite computation — is correct, and my independent re-run confirms its quantitative foundation through y = 19 (λ = 1.102168 to all printed digits, exactly one branching SCC, the spurious loop where G-5 says it is). The computation is not huge and can be made smaller still (Collatz–Wielandt witness; Braun-tree kernel checking). The real risks are presentational and procedural, not mathematical: don't call it an unavoidable set, fix the core-size definition, quarantine the heuristics, re-sequence independent replication before the write-up, and publish the certificate data early — because after this plan, the y = 31 check is trivially replicable by anyone.
