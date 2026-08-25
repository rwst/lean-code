<!--
(C) Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 (public domain).
-->

# DubC — X2 / X2′: the coprimality subshift of ⌊ξ·7ⁿ⌋

Experimental leg of **plan-dubC1** (`plans/plan-dubC1.html`), §8 experiment **X2**
upgraded to the certificate ladder **X2′** of §0-ter.

The 1967 Forman–Shapiro / DN05 problem asks whether ⌊ξ·aⁿ⌋ contains infinitely
many composites for every integer `a ≥ 7` and every real `ξ > 0`. This directory
runs the computation the plan hinges on. **Its outcome is (i): the certificate
`C(𝒫)` holds at the finite modulus `𝒫 = {p ≤ 31}`.** Per the plan's reduction
that resolves the case `a = 7`, and since 2026-08-09 the whole chain — computation
and reduction — is checked in Lean. Given the stakes, everything here is built for
independent re-checking, and the result is stated as *machine-checked, pending
mathematical review* — the formalization question is closed, the refereeing one
is not.

The **reduction** those runs feed is formalised in Lean and is sorry-free and
axiom-free (milestone M1′, see "The Lean layer" below): if `C(𝒫)` holds at one
finite `𝒫`, the base is settled — and [Dub09] Thm 4, the one input it rests on,
is *proved* in `ReturnEngine.lean` rather than cited.

> **Status, 2026-08-09 — read before quoting anything below.** The `y = 31` check
> is formalised **in full**. `lake build DubC.Cycles` completes in **410 s**
> (exit 0, 5.3 GB peak, `Cycles.olean` 336 640 B), and `lake build DubC` as a
> whole reports all 1 732 targets up to date. So
> **`DubC.Cycles.infinite_composites_seven` is a checked theorem** — the `a = 7`
> case of the 1967 Forman–Shapiro problem — with no remaining hypothesis and no
> cited-literature axiom, on a trusted base of std3 plus the Lean evaluator on
> **three** quarantined `native_decide` calls. `#print axioms` on it returns
> exactly `[propext, Classical.choice, Quot.sound]` together with
> `Cycles.chkCyc_true._native…`, `Rungs.chkAll_true._native…` and
> `Y31.checkDet_true._native…`.
>
> **This file said the opposite twice, in opposite directions, and both times it
> mattered.** Revisions before 2026-08-08 claimed "Machine-checked in Lean
> (2026-07-25) … and therefore the `a = 7` case" while `Cycles.lean` had *never
> compiled* — no olean, a build killed at 2 h 08 min, an earlier attempt past a
> week. The 2026-08-08 revision corrected that to "written but unchecked". On
> 2026-08-09 the cause was found — a heavy `Id.run do` loop inlined in the body of
> a **nullary** `def`, which the evaluator will not finish, while the byte-identical
> body as a *function* takes 10 s — and one line of indirection fixed it. Keep the
> rule that came out of the episode: nothing is called "machine-checked" until an
> olean exists for its module. See `plans/plan-dubC1.html` §0-undecies and R-12.
>
> **Conjecture 1 at `b = 7` is now also a theorem** (`DubC/Truncatable.lean`,
> added 2026-08-09): `DubC.no_infiniteTruncatablePrime_seven` — there is no
> infinite right-truncatable prime in base 7, from any starting prime. Earlier
> revisions of this file called that step "a citation to [DubOst06] §3, not a
> formalized step", which was true of the §3 route and is no longer the state of
> affairs: §3 was **bypassed**, not formalized. `#print axioms` on the new theorem
> returns the same six names as the one above — no new `native_decide`.
>
> One rider stands unchanged: "machine-checked" here means *modulo the Lean
> compiler*, which is not the same as axiom-free.

---

## The model

With `xₙ = ⌊ξ·7ⁿ⌋` one has `xₙ₊₁ = 7·xₙ + dₙ₊₁`, where `dₙ₊₁ ∈ {0,…,6}` is the
`(n+1)`-st base-7 digit of `ξ`. For a finite prime set `𝒫`, `M = ∏_{p∈𝒫} p`, the
digit words keeping `xₙ` coprime to `M` for all `n` form a subshift of finite
type on the units `(ℤ/M)*`:

```
  state r ∈ (ℤ/M)* ,   r --d--> (7r + d) mod M   admissible iff gcd(7r+d, M) = 1 .
```

`λ(𝒫)` = Perron root of the adjacency matrix; entropy `= log λ`; and (plan T4)
`dim_H {ξ : ⌊ξ7ⁿ⌋ avoids 𝒫} = log λ / log 7`.

**Reduction (verified against the literal model for `y ≤ 17`).** Coprimality to 2
forces `d` even; coprimality to 7 forces `d ≠ 0`; so the alphabet collapses to
`{2,4,6}`. Then `r mod 2 ≡ 1` always, and `r mod 7 ≡ d` never constrains a later
step — so the mod-2 and mod-7 coordinates carry no state. The reduced state space
is `∏_{p∈Q}(ℤ/p)*`, `Q = {p ≤ y} ∖ {2,7}`, of size `φ(M)/6`, with `rₚ --d--> 7rₚ+d
mod p`, admissible iff no coordinate hits 0.

**The certificate `C(𝒫)` (plan §0-ter).** After pruning to the bi-infinite core,
`C(𝒫)` holds iff **no strongly connected component contains two distinct cycles**
(equivalently: every cyclic SCC is a simple cycle; equivalently ρ(core) = 1,
zero entropy). If `C(𝒫)` holds for a single finite `𝒫`, every infinite
`𝒫`-avoiding digit word is eventually periodic (an infinite path's ω-limit is one
SCC = one cycle), so every avoiding `ξ` is **rational** — and rational `ξ` have
composites infinitely often, unconditionally, by **[Dub09] Theorem 4** (the Euler
self-return engine). Hence `C(𝒫)` at one finite `𝒫` ⇒ `⌊ξ7ⁿ⌋` composite i.o. for
**all** `ξ`, i.e. the `a = 7` case.

This is strictly weaker than an *unavoidable divisor set* (`λ < 1`, empty core),
which [DubOst06] Conjecture 3 predicts does **not** exist for `b = 7`. `C(𝒫)`
tolerates surviving cycles (they are periodic, hence rational, hence harmless).
That is why this route is not blocked by Conjecture 3.

---

## Results

### X1 recalibrated (clean re-implementation, R-6 discipline) — matches planning to 6 d.p.

| y  | λ(y)       | dim = log λ/log 7 | λ̄(y)=7∏(1−1/p) | ratio λ/λ̄ | C(𝒫) |
|----|------------|-------------------|-----------------|-----------|-------|
| 7  | 1.515192   | 0.213547          | 1.600000        | 0.9470    | fails |
| 11 | 1.366235   | 0.160366          | 1.454545        | 0.9393    | fails |
| 13 | 1.228622   | 0.105808          | 1.342657        | 0.9151    | fails |
| 17 | 1.149522   | 0.071610          | 1.263677        | 0.9097    | fails |

### X2′ ladder — the new rungs

> **Core sizes corrected 2026-07-25.** The "core after pruning" column below came from the
> *reduced*-model pipeline and none of its entries equals the bi-infinite core of the digraph
> the Lean certificate is checked against. An external reviewer re-ran `y = 19` from scratch and
> got 53 218, exactly what the ladder engine produces. **Canonical definition, used everywhere
> from now on:** states = units mod `M_y`; edges `r → 7r+d`, `0 ≤ d < 7`, both ends units;
> *core* = the states with an admissible path infinite in **both** directions (forward-peel to
> the fixpoint, then backward-peel to the fixpoint). The λ values, the branching counts and the
> cycle-level numbers are unaffected. Re-deriving every printed number from the machine-checked
> engine is an open M2′ item; the reduced-model pipeline must be re-audited or retired.
>
> **Amended 2026-08-08 — the delta is now explained, and the pipeline is not buggy.** The
> reduced pipeline computes the *correct core of a different state space*, and the difference is
> exactly one bit of memory. Measured at `y = 19`: the full core projects into `ℤ/(M/14)`
> **exactly onto** the reduced core (image = 48 548 = all of it, none missed), with fibres of
> size 1 (43 878 states) or 2 (4 670) — and `48 548 + 4 670 = 53 218`. The reason:
> `x_{n+1} ≡ d_{n+1} (mod 7)` and `x_n` is odd throughout, so **the mod-14 coordinate *is* the
> last digit**; dropping `p = 2, 7` is the one-step-memory quotient of the same subshift. Same
> language, same entropy, same cycles — different state count, which is why λ and the
> cycle-level numbers were unaffected while every core size differed.
>
> Three consequences. (i) "Every printed core size is wrong" overstates it: both columns are
> correct *for their own encoding*. (ii) "Re-audited or **retired**" is stronger than needed —
> the pipeline needs its state space *named*, not retiring. (iii) The point for any write-up:
> **the core size is an artifact of the encoding, not an invariant of the mathematics.** A
> referee re-deriving it in the natural quotient will get 371 555 and conclude the paper is
> wrong. Say which digraph, once, and give both numbers. Every printed number *has* now been
> re-derived by an outside implementation (`plans/plan-dubC1.html` §0-decies), so the M2′ item
> is discharged; what is left is editorial.

| y  | states (φ(M)/6) | core, as printed | **core (machine-checked)** | λ(y)       | dim       | ratio λ/λ̄ | C(𝒫) |
|----|-----------------|------------------|----------------------------|------------|-----------|-----------|-------|
| 17 | —               | —                | 6 228                      | 1.14952    | 0.072     | —         | fails |
| 19 | 276 480         | ~~48 548~~       | **53 218**                 | 1.102168   | 0.049992  | 0.9206    | fails |
| 23 | 6 082 560       | ~~358 529~~      | **377 594**                | 1.055294   | 0.027658  | 0.9216    | fails |
| 29 | 170 311 680     | ~~738 303~~      | **748 621**                | 1.013061   | 0.006668  | 0.9163    | fails |
| **31** | **5 109 350 400** | ~~371 555~~ | **371 702**                | **1 (exact)** | **0**  | —         | **HOLDS** |
| 37 | (from core 31)  | 4 453 852        | **4 454 022**              | 1 (exact)  | 0         | —         | HOLDS |

**The `y = 37` rung, re-derived 2026-08-08 (experiment X10).** 13 381 272 candidates
mod 7 420 738 134 810; core **4 454 022**; 4 931 cyclic SCCs, **0 branching**, so
`λ(37) = 1` exactly — the reduced-model value survives re-derivation. But the core
**grows by a factor 12** rather than shrinking. X10 asked whether some higher rung
might drop the core near `10⁴` and so under Lean's `~10⁵` elaboration wall, which
would have put `CoreClosed` inside plain `decide` and the trusted base at std3.
**It does not: the `native_decide` quarantine is permanent for this route.** The
halving at `y = 31` was the `λ → 1` phase transition and carried no information
about `y = 37` in either direction. `y = 41` not run — `1.8·10⁸` candidates, and
it would answer nothing further.

At `y = 31` the core (371 702 states = 365 761 on cycles + 5 941 transient) has 849 cyclic
SCCs and **every one is a simple cycle** — 0 branching SCCs, so the spectral radius is exactly
1 and the topological entropy is 0. `C({p ≤ 31})` **holds**.

**The all-6 family (G-5′).** `r ≡ −1` is a fixed point under `d = 6` at *every* modulus, and
`−1` is a unit mod every prime, so it lifts through every rung forever: **the core never empties
in this encoding**, however large `y` grows. At `y = 31` there are two such fixed points
(`M−1` and `4M/6−1 = 133 706 993 419`) and, more to the point, **176 of the 849 cycles have
constant digit word 6**, carrying 11 264 of the 365 761 cycle states. All 176 are the
non-terminating representation of terminating rationals — not floor expansions of any `ξ`. The
genuine content is **673 cycles / 354 497 states**. This is harmless to the theorem (an all-6
word is periodic, so the Euler return kills it; indeed `x_{n+1} = 7x_n + 6` gives
`x_n = 7ⁿ(x_0+1) − 1` outright), but it is load-bearing for anything about [DubOst06]
Conjecture 3 or about "the core is nonempty".

> Note on the `λ = 1.00023…` figure printed by the power iterators: that is a
> reducible-graph artifact of the whole-core Rayleigh quotient (many chained
> simple cycles inflate the ratio above the true radius). The rigorous quantity
> is `max over SCCs of the block Perron root = 1`, certified combinatorially by
> `branching = 0` and by `|edges| = |vertices|` on every cyclic SCC — no floating
> point involved. The dominant-SCC Collatz–Wielandt bracket is `[1, 1]`.

### Method-validation controls (`control.py`) — the machinery discriminates correctly

Same pipeline, arbitrary base `b`, **full** model (no reduction), against cases
with known status:

| base | status | C(𝒫) verdict |
|------|--------|--------------|
| b=3,4,6 | chain hypothesis **proved** (MPPSW Lemma A.1) | **HOLDS at the smallest y** ✓ |
| b=5  | **solved** (DN05 Thm 2) | FAILS at y=3, **HOLDS from y=5** — flips exactly when DN05's own mod-5 collapse kicks in ✓ |
| b=7  | (this work) | FAILS through y=29, **HOLDS at y=31** ✓ |
| b=10 | **open** | FAILS with a *growing* branching count (1→2→4→8) — the open neighbour is **not** falsely solved ✓ |

The method certifies every known-solved base and matches DN05's published `b=5`
mechanism, does not fire early on `b=7`, and keeps the open `b=10` at FAILS. Note
`b=7` carries **exactly one** branching SCC at every rung `7…29`, then it vanishes
at 31 — a single obstruction ground down — while `b=10`'s obstruction multiplies.

---

## Verification depth (why to trust `C({p≤31})`)

The one load-bearing fact — the `y=31` core has **0 branching SCCs** — is
confirmed by **seven implementations**, five of them by the same author (which is
exactly the weakness; see "Still to do" below):

1. `subshift.py` — scipy/`connected_components` reference; matches the C code on
   `y ≤ 23` and reproduces every X1 value. *(reduced model)*
2. `subshift.c` — **direct** full-space engine: prunes all 5 109 350 400 units
   with no incremental assumption → 849 cyclic, **0 branching**. *(reduced model)*
3. `ladder.c` — **incremental** engine (builds core(y) from core(y−)); the
   provably-correct `core(Q∪{p}) ⊆ core(Q)×(ℤ/p)*` shortcut → **bit-identical**
   849 / 0. *(reduced model)*
4. `verify_core.py` — scipy re-analysis of the dumped core: 0 branching nodes, 0
   branching SCCs, and `|edges| = |vertices|` on every cyclic SCC (an orthogonal
   simple-cycle certificate). *(reduced model)*
5. `grid.c` / `grid2.c` / `cond.c` and `DubC/Engine.lean` — the ladder grid
   engine, in the **full** model, in C and in Lean, agreeing exactly at every
   level: cores 6 228 / 53 218 / 377 594 / 748 621 / **371 702**, peel depths
   **528 forward and 319 backward** *(corrected 2026-08-08 from 527/318 — an
   off-by-one against the "rounds that removed something" convention used
   elsewhere in this file)*, condensation rank ≤ 241, and **0 violations**
   of the rank condition against the 365 761 cycle states.
6. An **external reviewer**, 2026-07-25, re-implementing from the stated
   transition rule alone: `λ(19) = 1.102168` to all six digits, 28 cyclic SCCs
   with exactly one branching, and a `y = 19` bi-infinite core of **53 218** —
   identical to (5), and the finding that exposed the reduced-model core-size
   error.
7. A **second outside re-derivation**, 2026-08-08, of the *whole* ladder from the
   canonical definition alone, sharing no code with this directory: all five
   rungs' candidate counts, grid sizes and cores; the forward-fixpoint leftover
   2 704 992 at `p = 29`; the entire cycle layer from `core_y31_cycles.txt` (849
   cycles / 365 761 states, all closing, all units); `CoreDet` with **0
   violations** and **0** edges between distinct cycles; the 147 core states with
   two core-successors; the recurrent set of the core equal to the shipped cycle
   set *exactly*, so the 5 941 transient states carry no cycle; condensation rank
   **241**; `λ(7,11,13,17)` to six digits with exactly one branching SCC at each;
   every row of the 8-state `𝒫 = {2,3,5,7}` table; the whole `λ̄(y)` first-moment
   table; the reviewer's `y = 19` triple (647 052 / 53 218 / 52 793) and 28 cyclic
   SCCs; and the base controls. **Everything reproduced, to the digit.**

Items 1–4 are the reduced model. Their *core counts* differ from (5)–(7) for a
reason now understood — it is the one-step-memory quotient, see the amendment
under the ladder table — and are correct for that encoding; their λ values,
branching counts and cycle-level numbers agree throughout. Item 5 is what the Lean
certificates are checked against, and a wrong entry there makes the check
evaluate to `false` rather than proving anything false.

The base controls further validate that the pipeline returns the *right* verdict
on cases with independently known answers.

---

## The Lean layer (milestone M1′)

Six Lean files formalise the *reduction* that the computation feeds. All six are **sorry-free**
and depend on **no axioms beyond Lean's three** (`propext`, `Classical.choice`, `Quot.sound`)
— no cited-literature axioms, nothing assumed about the C runs. (Re-verified from the oleans
2026-08-08 for `purely_periodic_mod`, `infinite_composites_floorPow_of_certOK`,
`infinite_composites_floorPow_of_coreCert`, `coreClosed_of_ladder`, `not_certOK_seven_thirty`,
`infinite_composites_five_via_core`, `infinite_composites_three_via_cycles` and
`infinite_composites_seven_of_coreCert`.) The seventh row below, `Y31Data`/`Y31`, is the
certified checker and leaves std3 by design — as do `Rungs.lean` and `Cycles.lean`, the two
ladder modules documented in the next section. Those three carry the whole quarantine: three
`native_decide` calls, no more, each in a file nothing axiom-free imports.

| file | content |
|------|---------|
| `ReturnEngine.lean`    | **[Dub09] Theorem 4**: `x_{n+d} = c·x_n + F(x_{n+1},…,x_{n+d-1})` is *purely* periodic mod every `q` coprime to `c`; with `\|x_n\| → ∞` it has infinitely many composite terms |
| `DigitRecurrence.lean` | digit dynamics `x_{n+1} = a·x_n + d_n` of `⌊ξaⁿ⌋`; **eventually periodic digits ⇒ a `d=1` return recurrence along a progression ⇒ composites i.o.**; plus Regime 1 (rational `ξ`, every base) |
| `Certificate.lean`     | the certificate as a **rank function** (never increases along an edge; ≤ 1 rank-preserving successor per state) ⇒ every infinite path eventually periodic ⇒ **one finite `C(𝒫)` settles the base**; plus the plumbing shared by both certificate forms |
| `CoreCertificate.lean` | the certificate as a **compressed core**: a set `K` that catches every cycle and inside which the subshift is deterministic — same conclusion, **no rank data** |
| `Ladder.lean`          | a **rank certificate** for `CoreClosed` (one pass, no SCC computation) and the **projection lemma** (cycles mod `M` project to cycles mod `M'`), which together cut the global obligation from `2·10¹¹` residues to rungs of at most `2.2·10⁷` |
| `Verdict.lean`         | instances: `decide`-checked bases, controls, the `a=7` target in both forms |
| `Y31Data.lean`, `Y31.lean` | the `y = 31` **certified checker**: the 849 cycles as witness data, and a checker run under `native_decide` proving `CoreDet` for the 365 761-state core. The only file that leaves std3 axioms |

**The rank form is `C(𝒫)`.** Take `rank r` = height of `r`'s SCC in the condensation DAG:
edges between SCCs drop the height, edges inside preserve it, so "≤ 1 rank-preserving
successor" says exactly *no state has two outgoing edges inside its own SCC*, i.e. every cyclic
SCC is a simple cycle. Same certificate, in the shape a kernel can check without graph
algorithms.

**The core form is what the computation actually produces.** `CoreClosed` says every residue
lying on a cycle is in `K`; `CoreDet` says a residue of `K` has at most one successor in `K`.
The proof is shorter and needs no potential function: in a finite state space every path
eventually consists of *recurrent* values, a recurrent value lies on a cycle, so the tail lies
in `K` and is forced from there. The two forms are **incomparable** — `CoreDet` forbids edges
between distinct cycles, which `C(𝒫)` allows. `not_coreDet_four_six` pins that down in the
kernel: base `4` at `𝒫 = {2,3}` has two fixed points joined by the edge `1 → 5` (digit `1`),
passes the rank form and fails the core form. What makes the core form the right one for
`a = 7` is a *measured* fact: `compress.py` finds **zero** edges between distinct cycles in the
`y = 31` core, so the rank there is constant and carrying it is pure overhead.

**Kernel-checked bases.** `b = 3, 4` at `𝒫 = {2,3}` and `b = 5, 6` at `𝒫 = {2,3,5}` pass
`decide`, giving the *full* statement for those bases — for every real `ξ > 0`, `⌊ξbⁿ⌋` has
infinitely many composite terms. Nothing new (`b=3,4,6` are [MPP+24] Lemma A.1, `b=5` is [DN05]
Thm 2); the point is that the entire pipeline runs end-to-end in the kernel. `b=4` and `b=6`
need a genuinely non-constant rank — their cores contain surviving cycles (`x ↦ 4x+3` fixes
`1 mod 6`), which the certificate tolerates because a periodic word is harmless.

**Controls, also proved.** `not_certOK_seven_thirty` and `not_certOK_ten_thirty` show **no**
rank function exists at `𝒫 = {2,3,5}` for `b = 7` or `b = 10`, by exhibiting a state with two
distinct successors that both return to it. So the machinery does not fire early on `b=7`, and
does not appear to settle the open `b = 10` — the plan's mandated sanity test, now a theorem.

**The `a = 7` target.** `infinite_composites_seven_of_cert` is a *proved theorem conditional on
the finite certificate* at `primorial31 = ∏_{p≤31} p`:

> given any `rank` with `CertOK 7 primorial31 rank`, for every real `ξ > 0` the sequence
> `⌊ξ·7ⁿ⌋` contains infinitely many composite terms.

`infinite_composites_seven_of_coreCert` is the same conclusion on the *smaller* hypothesis:

> given any set `K` of residues mod `primorial31` such that every residue on a cycle is in `K`
> (`CoreClosed`) and every residue of `K` has at most one successor in `K` (`CoreDet`), for
> every real `ξ > 0` the sequence `⌊ξ·7ⁿ⌋` contains infinitely many composite terms.

Here `K` is exactly the compressed core: the 365 761 cycle states in 849 cycles emitted as
`core_y31_cycles.txt`. The certificate is a **hypothesis, not an axiom** in either form — the
Lean development asserts nothing about the C runs. Discharging it needs the check to run over
data of that size inside the kernel, which `decide` cannot reach on a `2·10¹¹`-element residue
ring. So the reduction is machine-checked and the gap is exactly one finite,
explicitly-stated computation.

`rankcert.py` computes the condensation-height ranks and re-checks them against the *Lean*
`CertOK` conditions; it is what produced the four rank functions in `Verdict.lean`.
`compress.py` does the same job for the core form: it re-derives the cycles from the residues
alone and checks `CoreClosed`/`CoreDet` on the lifted `K`.

**The ladder makes `CoreClosed` finite.** `CoreClosed` is the one hypothesis that quantifies over
the whole residue ring. `Ladder.lean` removes that. Two lemmas:

- `coreClosed_of_rankOn` — a rank `ρ` that never increases along an admissible edge inside a
  candidate set `C`, and *strictly* drops out of every `C`-state not in `K`, forbids any cycle
  outside `K`: a cycle through `r ∉ K` would give `ρ r < ρ r`. One pass; no Tarjan, no iteration.
- `step_proj` / `onCycle_proj` — for `M' ∣ M` the ring hom `ZMod M →+* ZMod M'` sends admissible
  edges to admissible edges (units map to units, `t = a·r + d` survives), hence **cycles to
  cycles**. So a certificate `K'` at `M'` confines every cycle at `M` to `π⁻¹(K')`, which is the
  candidate set `C` for the rank lemma one level up.

`coreClosed_of_ladder` combines them and `forall_of_forall_lift` enumerates the fibre
(`r = r'.val + k·M'`, `k < M/M'`), so a rung costs `|K'| · (M/M') · a`:

| rung | `\|K'\|` (machine-checked) | grid states | candidate residues |
|------|-----------------------------|-------------|--------------------|
| `p ≤ 17` | — | 510 510 | 92 160 |
| `p = 19` | 6 228 | 118 351 | 112 104 |
| `p = 23` | 53 218 | 1 224 037 | 1 170 796 |
| `p = 29` | 377 594 | 10 950 255 | 10 572 632 |
| `p = 31` | 748 621 | 23 207 282 | **22 458 630** |

against `2·10¹¹` for the naive quantifier — a factor of about `10⁴`. (Table corrected
2026-07-25 along with the core sizes; the earlier figures were reduced-model counts.)

**The certified checker (`Y31.lean`), and what it does not need to trust.** `CoreDet` at
`y = 31` is now a theorem: `DubC.Y31.coreDet_seven`, checked by `native_decide` in 16 s over the
365 761 cycle states. The design keeps the trusted base to the Lean compiler and nothing else:

- **The witness data is untrusted.** `K` is *defined* as "what the membership test answers on
  what `cyclesData` decodes to". It is not claimed to be the cycle set, to be sorted, or to be
  anything. A corrupt entry can only make the check *fail* — never make a false theorem
  provable.
- **The search needs no correctness proof.** `bmem` computes some index and then asks the array
  what is stored there, so a positive answer *literally exhibits* the element (`bmem_sound`, four
  lines). Whether the binary search is correct is irrelevant, and completeness is never used.
- **The decoder needs no correctness proof**, for the same reason.

So what must be believed, beyond the compiler, is `detOK_spec` plus two `ZMod`/`Nat` bridges —
all small, all kernel-checked. `#print axioms` shows the split: everything in
`Certificate/CoreCertificate/Ladder/Verdict` stays on Lean's three axioms; only `Y31`'s results
name the `native_decide` axiom.

**Can the compiler be taken out of the loop? Measured: no, not at this scale.** `native_decide`'s
trust is not a debt that can be paid off — that would take a verified Lean compiler. The real
alternative is Lean's kernel-checked evaluator `cbv`, which mimics call-by-value evaluation while
*constructing a proof term*, so its proofs use only the three standard axioms. It was tried here
and misses by two independent margins:

| | measurement | what y=31 needs |
|---|---|---|
| proof-term size | ~118 kB per reduction step (3.82 / 4.41 / 5.59 GB at 5 000 / 10 000 / 20 000 walk steps — linear) | 365 761 walk steps ⇒ **~43 GB**, more than this machine has, before any membership work |
| time | ~2.4 ms per step (~3.4× slower than kernel `decide` on the same loop) | ~15 min for the walk — tolerable, unlike the memory |
| random access | ~1.5 s per lookup into a **10 000**-element array (arrays are terms, so an index is a traversal) | ~2.5 M lookups into a **365 761**-element array |

Same wall as the kernel, for the same reason, with a proof-term wall on top. `cbv` also needs
`set_option cbv.maxSteps`, `maxHeartbeats` and `maxRecDepth` raised. So the choice is not
"compiler trust vs. no compiler trust" but "compiler trust vs. no theorem", and the response is
to **quarantine** rather than eliminate: `Y31` is the only file leaving std3, nothing axiom-free
imports it, and every use site names the dependency.

**Why `CoreClosed` needed a bigger engine.** Two measurements set the shape. First, `K` has to
be the cycle set rather than the core: 147 of the 371 702 core states have *two* core-successors,
so `CoreDet` is false for the core. Second, peeling is deep — the rank reaches 528 forward and
319 backward at the last rung — and is needed at all 22 458 630 candidate residues there. That
is far too large to ship as a literal, so the checker must *compute* it (again with no
correctness proof — it is a witness), by linear-time peeling with reverse adjacency: about 66 M
edges, ~1 GB of arrays.

**The ladder engine (2026-07-25).** Built, in three files. `Rung.lean` is the mathematics: the
rank certificate in ℕ arithmetic so the witness can be plain array lookups
(`coreClosed_of_rankNat`), the same with the arrow reversed (`coreClosed_of_rankRevNat`), the
ℕ-form projection/lift bridge (`coreClosed_comapUnitN`), a nested-fibre enumeration
(`forall_lift_nat`) and a tail-recursive bounded `∀` (`allLt`). It also *proves* the two cheap
digit guards (`digit_guards`): an admissible successor is coprime to `M`, hence odd and not a
multiple of 7, so `d ∈ {2,4,6}` and the checker never computes the successor for the other four
digits. `Engine.lean` is the witness generator — no theorem in it, and nothing in it has to be
correct. `Rungs.lean` instantiates the ladder for `a = 7` and runs the check.

Two design decisions did all the work, and both came from measurement rather than from taste:

- **No searching, anywhere.** The first design binary-searched a sorted state array; measured,
  that costs ~50 minutes *per pass* at the top rung. Indexing a state as `(i, k)` — `i` the
  index at the level below, `k < p` the lift, grid index `(i+1)·p + k` — makes the successor
  pure arithmetic, `succ (i,k) d = (SU'[i][d], ((7r+d) mod M) / M')`, and the lookup structure
  disappears entirely.
- **Forward peeling is not enough, and exactly two stages suffice.** At the `p = 29` rung,
  peeling forward to the fixpoint leaves 2 704 992 states where the core has 748 621 — so each
  rung needs a *reversed* rank certificate as well. It is two and not an unbounded alternation
  because forward-to-fixpoint then backward-to-fixpoint is provably already the bi-infinite
  core; `grid2` confirms a third stage removes nothing at any rung. Both stages are layered
  worklists, `O(E)`: a round-by-round rescan costs 3.9·10⁹ state visits where the worklist
  costs ~10⁸.

One trap worth recording, because the checker caught it as a `false` rather than as a wrong
theorem — the design working as intended: the candidate set at a lifted rung must also exclude
residues `≡ 0 mod p`. They are not subshift states, but they do have subshift states as formal
successors, so leaving them in asks the rank to drop below `0`, and *no* rank function can pass.

## What this does and does not establish

**Machine-checked in Lean (all three stages, complete 2026-08-09):** the *global* half of the
compressed-core certificate at `𝒫 = {p ≤ 31}` — `Rungs.cc4`, every cycle confined to the
371 702-state core, via the five-rung ladder — the *local* half on the cycle set,
`Y31.coreDet_seven`, and the step between them, `Cycles.coreClosed_seven` (core → cycles). All
three verified from the oleans. Hence the target they feed:

> `DubC.Cycles.infinite_composites_seven` — for every real `ξ > 0`, the sequence `⌊ξ7ⁿ⌋`
> contains infinitely many composite terms.

is a checked theorem, carrying **no remaining hypothesis and no cited-literature axiom** —
[Dub09] Theorem 4 is *proved* in `ReturnEngine.lean`, not assumed. That is the `a = 7` case of
the 1967 Forman–Shapiro problem, and [DubOst06] Conjecture 2 at `b = 7`.

**And Conjecture 1 at `b = 7`, without going through §3** (`Truncatable.lean`, 2026-08-09):

> `DubC.no_infiniteTruncatablePrime_seven` — no infinite sequence of primes satisfies
> `pₙ₊₁ = 7·pₙ + dₙ` with digits `dₙ < 7`; i.e. there is no infinite right-truncatable prime in
> base 7.

Earlier revisions listed this as the one clause that was "a citation to [DubOst06] §3, not a
formalized step", because their `Conjecture 2 ⇒ Conjecture 1` direction splits on whether the
digit word ends in `(b−1)^∞` and closes that branch with a separate Fermat argument. **That
route was bypassed rather than formalized.** The `(b−1)^∞` branch is an artefact of passing
through a real number: from a chain one builds `ξ = lim pₙ/7ⁿ` and needs `⌊ξ7ⁿ⌋ = pₙ`, which
fails by exactly one when the tail is all-6. Applying the certificate to the chain directly,
there is no `ξ` and no branch — an all-6 word is eventually periodic like any other, so the
same [Dub09] Theorem 4 return that handles every other word handles it too.

What that cost: the plumbing of `Certificate.lean`/`CoreCertificate.lean` is *stated* for
`floorPow ξ a n` but *uses* only `xₙ₊₁ = a·xₙ + dₙ`, `0 ≤ dₙ < a`, and `‖xₙ‖ → ∞`. Those three
are collected as `DubC.IsDigitRec` and re-proved for an abstract `x`; a prime chain supplies all
three, the growth for free from `pₙ₊₁ ≥ 7pₙ`. `#print axioms` returns the same six names as for
`infinite_composites_seven` — no new `native_decide`, and no cited-literature axiom.

The `b ≤ 6` cases come out of the same lemma against the `decide`-checked certificates of
`Verdict.lean`, at std3 with nothing quarantined: `no_infiniteTruncatablePrime_three`, `_four`,
`_five`, `_six`. That is [MPP+24] Lemma A.1, whose authors prove it by hand alphabet-collapse
plus Fermat without knowing it is [DubOst06] Conjecture 1 — the content of the bridge note
(lane G / M2.5′).

Non-vacuity, since both statements are negations: base 7 has **19** right-truncatable primes,
the longest chain having length 5 — `2 → 19 → 139 → 977 → 6841` (`25642₇`) — the analogue of
Angell–Godwin's 83 base-10 primes topped by `73939133`. The Lean statement allows *any* starting
prime, so it rules out more than that enumeration bounds.

**What it still does not settle.** "Machine-checked" here means *modulo the Lean compiler* (see
the trusted base below), not axiom-free.

**The history, because it is the point of the standing rule.** This file claimed the theorem as
machine-checked from 2026-07-25, when `Cycles.lean` had *never compiled* — no olean, a build
killed at 2 h 08 min, an earlier attempt past a week. That claim was false, and was corrected on
2026-08-08 to "written but unchecked". The mathematics was never in doubt: an outside
re-implementation had already confirmed that the recurrent set of the 371 702-state core is
*exactly* the 365 761 shipped cycle states, so the 5 941 transient states carry no cycle, and
that the condensation rank is exactly 241 — the content of the missing check. On 2026-08-09 the
cause of the hang was found (see `condRankAux` below) and the certificate now exists too.

*Standing rule, after this:* nothing enters this file, the plan, or a memory as
"machine-checked" until an olean exists for its module. "Written", "compiling" and "expected"
are different words. The tell that should have caught the overclaim a fortnight earlier: the
trusted-base sentence below listed `Cycles.chkCyc_true` with a **blank timing**, and a check
with no measured cost has not been run.

**Trusted base:** Lean's three standard axioms, plus the Lean *compiler* on **three** quarantined
`native_decide` checks — `Y31.checkDet_true` (16 s), `Rungs.chkAll_true` (1 159 s) and
`Cycles.chkCyc_true` (410 s for the module). Nothing axiom-free imports those
files and `#print axioms` names the dependency at every use site. This is a real upgrade on "the C code, the Python, and a human
reading of both", and it is **not** the same thing as axiom-free. The alternatives were measured
and do not reach this scale: `cbv` (kernel-checked evaluation, std3 only) costs ~118 kB of proof
term per reduction step, so the 365 761-step cycle walk alone would need ~43 GB before any
membership work, and it represents arrays as terms so an index is a traversal (~1.5 s per lookup
into a *10 000*-element array). Braun trees would fix the lookup cost for the one **shipped**
witness (`CoreDet`) and are worth testing, but cannot touch `CoreClosed`, whose witness is
*computed* — 2.3·10⁷ rank entries from peeling over ~66 M edges. **And X10 has now closed the
last escape route** (see the `y = 37` note above): the core *grows* at the next rung, so no
higher modulus shrinks the object below the elaboration wall. This is the final position for
this route, not an interim one.

**Still to do before this is a *claimed* theorem** (deliberately not asserted here):

- ~~**Make `Cycles.lean` compile.**~~ **Done 2026-08-09, 410 s.** The probe that should have come
  first was finally run — the first `10⁵` candidates of `loop4`, staged against the built oleans —
  and it exonerated the loop: `10⁵ → 0.5 s`, `2·10⁵ → 0.9 s`, `10⁶ → 4.7 s`, dead linear, nothing
  re-evaluated per candidate. Both suspects named here were innocent: `Rungs.D4` *is* memoized (a
  second reference costs 0.1 s after the first costs 229.5 s), and hoisting `isCyc` out of
  `condRank`'s inner loop changes nothing. The fault was in the one-off setup, which a probe that
  prices the loop does not price. **The trigger:** a heavy `Id.run do` loop inlined in the body of
  a **nullary** `def`. Same relaxation, four ways, one process, same data:

  | | |
  |---|---|
  | `def condRank : Array ℕ := Id.run do …` — nullary, as shipped | **> 323 s, unfinished** |
  | the same, `isCyc` hoisted above the loop | **> 324 s, unfinished** |
  | `def condRankIO (log) : IO (Array ℕ)` — a function | 11.1 s |
  | `def condRankFn (z : ℕ) : Array ℕ := Id.run do …` — a function | **10.1 s** |
  | `def condRank : Array ℕ := condRankFn 0` — nullary, body an application | **9.9 s** |

  So it is not `Id` vs `IO`, and not nullary-ness as such. Everything else here is safe by
  accident: every heavy loop in `Engine.lean` takes an argument, and `D0…D4` are nullary but
  their bodies are *applications* of those. **The fix** is `condRankAux (z : ℕ)` opening with
  `let n := D4.L.S.size + z`, plus `def condRank := condRankAux 0` — no proof, statement or
  witness changes, since the rank array is opaque data the check is verified against. The
  mechanism was *not* identified and should not be guessed: minimal reproductions all stay flat
  (~0.65 s at every array size from 10³ to 2.56·10⁵, including one sized by and reading from a
  second nullary constant). The A/B above, on the real definition, is the only reliable test.
  Where the 410 s goes: engine 229.5 s, `Y31.KA` 0.1 s, `isCyc` 2.0 s, `condRank` 10 s,
  enumeration of all 23 207 251 residues ≈109 s.

- **Independent replication, and the artifact.** This is now the binding constraint, and the
  dominant risk is correlated error: every implementation so far is by one author, so a shared
  wrong admissibility encoding would not be caught by re-running. An external review on
  2026-07-25 demonstrated both the risk and the cure — it reproduced `λ(19) = 1.102168` and the
  `y = 19` core (53 218) from scratch, *and* found that every printed core size in this file was
  wrong. Ship `core_y31_cycles.txt`, the engine and a ~100-line standalone verifier under a DOI:
  after this work the `y = 31` check is replicable by anyone in minutes, so verification and
  priority protection point the same way. The Lean layer helps in one specific way — a wrong
  witness makes the check evaluate to `false`, it cannot make a false theorem provable — so the
  residual exposure is the *statement* of `Step`/`Cop` and the Lean compiler.
- ~~**Number reconciliation and G-5′.**~~ **Both measured 2026-08-08.** Every printed quantity
  has been re-derived by an outside implementation, and the reduced-model delta is *explained*
  rather than merely flagged (see the amendment under the ladder table). G-5′'s numbers are
  confirmed — 673 cycles / 354 497 states, branching still 0 afterwards (trivially: `CoreDet`
  holds on all of `K`, hence on any subset), and exactly two all-6 fixed points exist. What
  remains is engineering, not measurement: **implement** the all-6 exclusion in whatever code
  the cycle classification and the cycle-lifting lane actually run on, so the 176 cannot leak
  back in; and label the three quotient-model dumps rather than deleting them.
- ~~A line-by-line audit of the `C(𝒫) ⇒ eventually-periodic ⇒ rational` step and of
  [Dub09] Thm 4's exact hypotheses.~~ **Done, and better than an audit:** the whole reduction
  is machine-checked in Lean, including [Dub09] Thm 4 itself. The formalized chain also
  *shortens* the informal one — rationality of `ξ` is never needed, eventual periodicity of the
  digit word feeds Thm 4 directly.
- ~~A **Lean certificate for `y = 31`**.~~ **Done** — see above. Recorded so they are not
  retried: the plain **kernel** route is out — kernel arithmetic is fine (~1 470 certified
  steps/sec — *corrected 2026-08-08, the printed ~3 300 was wrong by 2.2×: 20 000 steps in
  13.6 s is 1 470/s, which is what the ~4 min below and `cbv`'s "~3.4× slower" both require* —
  so the 365 761-step walk is ~4 min) but the kernel special-cases `Nat` and `String`
  only, so `Array` reduces as a `List` and the 182 092 membership queries cost ~6.7·10¹⁰ steps;
  a **membership-free** local test (replace "successor ∈ K" by "successor survives `D` steps")
  fails, because the death depth of the competing successors has a heavy tail (~4% still alive
  at depth 40, so `D` would be ~319); and **term literals** at that length do not elaborate at
  default settings (a 100 000-element list literal dies at `isDefEq`) — which is why the witness
  ships as 849 strings and is decoded at run time.
- Literature confirmation that no equivalent argument is already in print (the plan's gates
  G-1…G-7 concluded the C-route is novel and `b=7` is open "in both directions" per
  [DubOst06]); an expert / referee read before any announcement.

**Two things this is *not*.** `{p ≤ 31}` is **not an unavoidable set of divisors** — the core is
nonempty, and the whole point of the certificate is that it does not need to be. And this does
**not** refute [DubOst06] Conjecture 3 at `b = 7`; the 673 genuine cycles are 673 explicit
periodic families of `ξ` dodging every `p ≤ 31` forever, i.e. witnesses *for* that conjecture.
The cleanest statement of what the method buys: for `b = 5`, [DubOst06] Thm 4 proves that *no*
unavoidable set can ever exist, yet the ladder shows `C({2,3,5})` holds — the certificate
succeeds on a base where the divisor-set method is provably impossible.

**Machine-checked is not refereed.** As of 2026-08-09 both `b = 7` statements — [DubOst06]
Conjecture 2 and Conjecture 1 — *are* fully machine-checked, all three certificate stages,
`#print axioms` verified. That closes the formalization question, not the reviewing one. Treat it as a result whose computation has been
reproduced by two outside implementations, whose every step is proved in Lean modulo the Lean
compiler on three quarantined evaluations, and which **no person other than its author has
refereed**. That last clause is the binding constraint now, and nothing is announced before it
lifts.

---

## Files

| file | what it does |
|------|--------------|
| `subshift.py`    | scipy reference: full & reduced models, X1 recalibration, `y≤23` |
| `subshift.c`     | direct full-space C engine (pruning + Tarjan + power iter + witness); `./subshift <y> [iters]` |
| `ladder.c`       | incremental C engine climbing the ladder; `./ladder <ymax> [iters] [dump_y]` |
| `cycles.c`       | `ladder.c` + full rung provenance, CRT-reconstructing each core state's residue; `./cycles 31 2000 31` → `core_y31_res.txt` |
| `control.py`     | base-`b` method-validation controls (b=3,4,5,6,7,10) |
| `verify_core.py` | independent scipy re-check of a dumped core; `python3 verify_core.py core_y31.txt` — note that dump is the quotient model, so its state count is 371 555, not 371 702 |
| `rankcert.py`    | condensation-height rank certificates, checked against the Lean `CertOK` conditions |
| `compress.py`    | compresses the core to its cycles and checks them against the Lean `CoreClosed`/`CoreDet` conditions; `python3 compress.py core_y31_res.txt` → `core_y31_cycles.txt` |
| `grid.c`, `grid2.c` | prototype of the **ladder grid** engine that `DubC/Engine.lean` runs, in the same representation, so its rung sizes are the sizes Lean has to cope with; `grid2` also verifies that forward-then-backward peeling reaches the fixpoint in two stages |
| `cond.c`         | the last stage: condensation rank on the `y=31` core, checked against the Lean rank conditions with `C` = core, `K` = cycles; `./cond` |
| `Rung.lean`      | the ladder mathematics: ℕ-form rank certificates (forward and reversed), the ℕ projection/lift bridge, fibre enumeration, bounded `∀`, the `d ∈ {2,4,6}` digit guards; sorry-free, std3 |
| `Engine.lean`    | the witness generator: grid lift, transpose, layered forward/backward peeling, compaction. *No theorem; nothing in it has to be correct* |
| `Rungs.lean`     | the five-rung ladder for `a = 7`; `chkAll = true` over 22 458 630 candidates (`native_decide`, 1 159 s, ~5 GB); ends at `cc4`, the 371 702-state core |
| `Cycles.lean`    | condensation-rank certificate closing the 5 941-state core→cycles gap; `coreClosed_seven`; **`infinite_composites_seven`**. Builds in 410 s since 2026-08-09; it had never compiled before that, for the reason recorded under "Still to do" — do not "simplify" `condRankAux`'s unused argument away |
| `Truncatable.lean` | [DubOst06] **Conjecture 1** at `b = 7`: `InfiniteTruncatablePrime`, **`no_infiniteTruncatablePrime_seven`**, and `_three`/`_four`/`_five`/`_six` ([MPP+24] Lemma A.1). Generalizes the `Certificate.lean`/`CoreCertificate.lean` plumbing from `floorPow ξ a n` to any `IsDigitRec`; **§3 of [DubOst06] is bypassed, not formalized**. Builds in 1.2 s, adds no `native_decide`. Written as a new file *on purpose*: editing the two files it mirrors would rebuild `Rungs.lean` (1 159 s) and `Cycles.lean` (410 s) |
| `*.lean`         | the rest of the Lean layer — see the section above. `lake build DubC` completes; all 1 733 targets up to date as of 2026-08-09 |
| `*.log` | run logs |
| ⚠️ `core_y31.txt`, `core_y31_res.txt`, `core_y29_res.txt` | **quotient-model dumps** — 371 555 / 371 555 / 738 303 states, modulus `primorial/14` (`p = 2, 7` dropped). Correct for that encoding, but they disagree with the canonical 371 702 / 748 621 and have twice been mistaken for authoritative. Do not print a number from these without saying which digraph it counts |
| `core_y31_cycles.txt` | the canonical compression: 849 cycles / 365 761 states mod `primorial31 = 200 560 490 130`. This is the file the Lean witness ships and the one to publish |

Build: `gcc -O3 -march=native -fopenmp -o subshift subshift.c -lm`
(and likewise `ladder`). Full ladder `y=7…37` runs in ~30 s on 28 cores; the
direct `y=31` run takes a few minutes and ~10 GB.

## References

- **[DN05]** Dubickas, Novikas, *Integer parts of powers of rational numbers*,
  Math. Z. 251 (2005). — the `a=5` return trick; states `a≥7` open (p. 637).
- **[Dub09]** Dubickas, *Prime and composite integers close to powers of a
  number*, Monatsh. Math. 158 (2009). — **Theorem 4**, the Euler-return engine
  that disposes of the rational case (the one cited input this result rests on).
- **[DubOst06]** Dubickas, *Truncatable primes and unavoidable sets of divisors*,
  Acta Math. Univ. Ostrav. 14 (2006). — Conjecture 3 (no finite *unavoidable* set
  for `b∉{2,3,4,6}`); `b=7` left open in both directions.
- **[MPP+24]** Miller et al., *Walking to infinity…*, Integers 24 (2024). —
  Lemma A.1 proves the chain hypothesis for `b=3,4,5,6`; our controls reproduce it.
