# Antihydra ↔ Mahler's 3/2 problem / Z-numbers — connections and non-implications

*Technical note accompanying `SRS/AntihydraMahler.lean`. (C) 2026 Ralf Stephan, in collaboration with
Claude Code; CC0.*

This note maps the relationship between three problems that all turn on the multiplicative behaviour
of `3/2` modulo one:

1. **Antihydra** — the BB(6) non-halting candidate (bbchallenge).
2. the **parity / fractional-part distribution** of the orbits `⌊(3/2)ⁿ·c⌋`;
3. **Mahler's 3/2 problem** and **Z-numbers** (Mahler 1968).

Every formal statement below is in the Lean file; the regular-invariant ⟹ bounded-dip machinery it
leans on is already proved in `SRS/AntihydraSRSObstruction.lean`. Where the goal brief mentions
"Report A (equivalence questions)" as a dependency, that report was not available; this note is
self-contained and flags the one place it would have helped.

---

## 0. Definitions and conventions

**Antihydra macro orbit.** Value `aₙ` and counter `bₙ`:

$$a_0 = 8,\qquad a_{n+1} = \left\lfloor \tfrac{3a_n}{2}\right\rfloor,\qquad
b_{n+1} = b_n + \begin{cases} +2 & a_n \text{ even} \\ -1 & a_n \text{ odd.}\end{cases}$$

The machine **halts** iff the counter would go negative, i.e. iff some odd value arrives with `bₙ = 0`.
Writing `pₙ = aₙ mod 2 ∈ {0,1}` and using `eₙ`/`oₙ` for the number of even/odd values among
`a₀,…,a_{n−1}`, the counter is the *ballot sum* `bₙ = b₀ + 2eₙ − oₙ` (Lean: `counterZ_closed`), and

$$\textbf{Antihydra never halts} \iff \forall n,\ b_n \ge 0 \iff \forall n,\ o_n \le 2e_n .$$

Lean names: `valStep a = 3*a/2`, `valOrbit a₀ n` (= `aₙ`), `counterZ b₀ a₀ n` (= `bₙ`, in `ℤ`),
`orbitCounter` (the `ℕ` counter on string configurations), all in `SRS/AntihydraSRS.lean`.

**Mahler's 3/2 problem.** For real `ξ > 0` study `{ξ(3/2)ⁿ}` (`{·}` = fractional part). A **Z-number**
is a `ξ > 0` with `{ξ(3/2)ⁿ} < 1/2` for *all* `n ≥ 0`. **Mahler's conjecture (1968): no Z-numbers
exist.** The integer case `ξ = c ∈ ℕ` is the "powers of 3/2" problem: even *density* of `{(3/2)ⁿ}` in
`[0,1]` is open. Lean: `IsZNumber`, `no_Z_numbers`.

**Mahler's single-floor sequence.** `gₙ = ⌊(3/2)ⁿ·c⌋ = 3ⁿc / 2ⁿ` (`ℕ` division). Lean: `mahlerFloor`.
Note `gₙ` uses **one** floor at step `n`, whereas `aₙ` uses an **iterated** floor.

---

## 1. The rigorous relationships (proved in Lean)

Let `aₙ = valOrbit c n`, `pₙ = aₙ mod 2`.

### R1 — Defect recurrence. `two_mul_valOrbit_succ_add_parity`
$$2a_{n+1} + p_n = 3a_n .$$
One Antihydra step is *exactly* geometric growth by `3/2`, minus a half-unit on odd values. (Proof:
`3a = 2⌊3a/2⌋ + (3a \bmod 2)` and `3a ≡ a (mod 2)`.)

### R2 — Geometric identity. `valOrbit_geometric_identity`
$$3^n c = 2^n a_n + T_n,\qquad T_n = \sum_{k<n} 3^{\,n-1-k}\,2^{k}\,p_k
\quad(\text{Lean: } \texttt{parityWeightedSum}),$$
equivalently
$$\boxed{\,(3/2)^n c - a_n = \tfrac12\sum_{k<n}(3/2)^{\,n-1-k}p_k \ \ge 0\,}.$$
**The deviation of the floored Antihydra orbit from pure `3/2`-geometric growth is precisely the
accumulated parity defect `Tₙ`.** This is the rigorous bridge that puts Antihydra and the `(3/2)ⁿ`
geometric sequence on the same page.

### R3 — Mahler residue bridge. `mahler_residue_eq`
$$3^n c \equiv T_n \pmod{2^n},\qquad\text{i.e.}\qquad
\boxed{\,\{(3/2)^n c\} = \frac{T_n \bmod 2^n}{2^n}\,}.$$
**The Mahler fractional parts of the pure `3/2`-orbit are the `(3/2)`-weighted Antihydra parities
taken mod 1.** This is the formal point of contact with Mahler's `3/2` problem: understanding
`{(3/2)ⁿc}` *is* understanding the weighted parity sums `Tₙ mod 2ⁿ`.

### R4 — Dip = parity excess. `counter_drop_eq_parity_excess`
With `T_{n,L} = o_{n+L} − o_n` the number of **odd** steps in the interval `[n, n+L)` (Lean:
`oddSteps`), the counter drop is exactly
$$\boxed{\,b_n - b_{n+L} = 3\,T_{n,L} - 2L\,},\qquad\text{so}\qquad
D(n) = \max_{L\ge0}\bigl(3T_{n,L} - 2L\bigr),\quad D(n)\ge q \iff \exists L,\ T_{n,L}\ge\tfrac{2L+q}{3}.$$
**A future dip of depth `q` is exactly an interval whose odd-step count exceeds the equilibrium
frequency `2/3` by `q/3`.** (The frequency `2/3` is forced by the counter arithmetic: an odd step
costs `−1`, an even step pays `+2`, so the counter breaks even at two even steps per odd step.) This
recasts the *unbounded-dips* question as a **large-deviation** statement about the parity sequence —
the precise Mahler/`3x+1` input of §3 (Hypothesis M).

### R5 — Odd values recur; no all-even orbit. `exists_valParity_one`, `valParity_one_frequently`
For every seed `a₀ ≥ 2`, **odd values occur at arbitrarily late steps**; in particular the parity
sequence is *not eventually `0`*. Proof: if all parities were `0` then `T_n = 0` by R2, so
`3ⁿa₀ = 2ⁿaₙ`, forcing `2ⁿ ∣ a₀` for every `n` — impossible for `a₀ > 0` once `2ⁿ > a₀`; restart at
step `N` (value still `≥ 2`) for recurrence. This is the elementary integer shadow of the **2-adic
Z-number non-existence** for `f(x) = ⌊3x/2⌋` (§4): no nonzero orbit is permanently confined to the
even cylinder. It is a genuine *known* fact about the parity sequence — the polar opposite of the
*conjectural* upper-excess Hypothesis M — and, as §4 explains, it does **not** imply Hypothesis M.

> **Success criterion (rigorous relationship): met, four times over.** R2–R5 are proved with only the
> standard axioms (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`, no `native_decide`.

---

## 2. The rigorous non-relationship (proved in Lean)

The orbits **differ**: at `c = 8, n = 6`,
$$a_6 = \texttt{valOrbit }8\ 6 = 90,\qquad g_6 = \lfloor(3/2)^6\cdot 8\rfloor = \lfloor 5832/64\rfloor = 91 .$$
(`valOrbit_eight_six`, `mahlerFloor_eight_six`, `valOrbit_ne_mahlerFloor`.) The divergence starts at
`n = 6` because `8 = 2³` absorbs denominators only through `n = 3`; thereafter the iterated floor
loses information the single floor keeps.

Crucially the **parities already disagree** there (`90` even, `91` odd):
$$\texttt{valParity }8\ 6 = 0 \ne 1 = \texttt{mahlerParity }8\ 6 \qquad(\texttt{valParity\_ne\_mahlerParity}).$$

**Consequence.** The Antihydra parity sequence `(pₙ)` is **not** the parity sequence of `⌊(3/2)ⁿ·8⌋`.
Therefore:

* partial results about the Mahler/single-floor sequence `⌊(3/2)ⁿc⌋` do **not** transfer termwise to
  Antihydra;
* there is **no** real `ξ` whose Z-number condition `{ξ(3/2)ⁿ} < 1/2` is literally Antihydra's
  halting test — the halting test reads the *low* bit of an integer `aₙ` (R1), while the Z-number
  test reads whether a *real* fractional part is `< 1/2`. These are different functionals of the
  orbit (related only through R2/R3, not equal).

> **Success criterion (rigorous non-relationship): met.** `valParity_ne_mahlerParity` is proved
> (`decide`, axiom `propext` only).

This is the precise sense in which the likely outcome is "negative (no implication)": the naive
reduction Antihydra ⇄ Z-numbers is blocked at the level of the sequences themselves.

---

## 3. Regular invariants, future dips, and why this is "Mahler-3/2 territory"

Define the **future dip** `D(n) = bₙ − min_{m ≥ n} bₘ` (Lean: `futureDip`). A *finite regular
invariant* — a FAR-style finite-automaton certificate `S` with `p` states that contains all reachable
configurations, is closed under rewriting, and excludes the halting configuration — is the standard
way bbchallenge deciders prove non-halting.

**Already proved** (in `SRS/AntihydraSRSObstruction.lean`, *not* re-derived here):

| Statement | Lean name |
|---|---|
| A `p`-state regular invariant forces `D(n) < p` whenever `bₙ ≥ p` | `futureDip_bound`, `futureDip_lt_card` |
| Hence **unbounded dips ⟹ no regular invariant** of any size | `no_regular_invariant_of_unbounded_dips` |
| The pumping property comes from a genuine `DFA` (suffix pigeonhole) | `dfa_pump`, `regularInvariant_of_dfa` |
| **Unbounded dips ⟹ no finite automaton** certifies non-halting | `no_dfa_invariant_of_unbounded_dips` |

So the implication in the goal brief — *"a finite regular invariant ⟹ a uniform bound on future
dips"* — is a **theorem** (its contrapositive `no_..._of_unbounded_dips`). What remains is the input:

### The Mahler-territory conjecture. `antihydra_future_dips_unbounded` (sorried)
> For the **non-halting** value-`8` orbit, the future dips are unbounded: `∀ q, ∃ n, bₙ ≥ q ∧ D(n) ≥ q`.

By R4 this is **equivalent** to the report's

> **Hypothesis M (parity large deviations).** For every `q` there are `n, L` with `bₙ ≥ q` and
> `T_{n,L} = Σ_{k=n}^{n+L−1} εₖ ≥ (2L+q)/3` — an unbounded *excess* of odd steps over the equilibrium
> frequency `2/3` on long intervals.

Casting `T_{n,L}` as a Birkhoff sum `Σ_{k<L} φ(fᵏ(xₙ))` of `φ(x) = x mod 2` along the 2-adic map
`f(x) = ⌊3x/2⌋`, and rescaling by the excess observable `ψ(x) = φ(x) − 2/3 ∈ {−2/3, +1/3}`, gives
the equivalent dynamical form:

> **Hypothesis M′ (Birkhoff excess for the Mahler 3/2 map).** `sup_{n,L≥1} Σ_{k<L} ψ(fᵏ(fⁿ(8))) = +∞`.

Why this is Mahler-3/2 territory: by `counterZ_closed` the counter is the `{+2,−1}`-walk driven by
the parities `pₖ`, whose distribution is governed — via R2/R3 — by `{(3/2)ᵏ·8}`. Conjecturally the
`pₖ` are equidistributed, the increments `2 − 3pₖ` have mean `+1/2`, and a positive-drift
pseudorandom walk has **unbounded** future excursions (the sup over `n` of `D(n)` is infinite even
though each individual `D(n)` is finite). M/M′ is in fact *stronger* than equidistribution: it asks
for **record-positive** fluctuations, which even for fair coin flips occur only logarithmically often.
The heuristic random-walk model predicts record dips
$$D_{\text{record}}(n) \sim \frac{\ln n}{\ln(1/q)},\qquad q = \tfrac{\sqrt5-1}{2}\approx 0.618
\ \ (\text{golden-ratio reciprocal}),\qquad \text{i.e. } \approx 2.078\ln n,$$
and this is observed empirically over `3·10⁵` exact orbit steps. Proving M/M′ requires exactly the
kind of control over the distribution of `{(3/2)ⁿ·8}` that Mahler's problem is about. Hence:

### The payoff. `antihydra_no_dfa_invariant` (proved, modulo the conjecture)
Instantiating the obstruction with the conjecture gives: **if Antihydra's dips are unbounded then no
finite automaton certifies its non-halting, at any state count.** The Lean corollary derives the
required "orbit doesn't halt" premise for free from any candidate DFA (`macroIter_isSome`), so it adds
no `sorry` of its own — the entire open content is isolated in `antihydra_future_dips_unbounded`.

**This is the rigorous form of the brief's thesis.** "A finite regular invariant would imply a uniform
bound on future dips" is `futureDip_lt_card` (proved); "which is precisely Mahler-3/2-problem
territory" is `antihydra_future_dips_unbounded` (the conjecture whose difficulty is Mahler-flavoured).

---

## 4. Known partial results, and what they do / do not imply

**Mahler (1968).** Z-numbers, if any, are rare: at most one in each `[N, N+1)` and density `0`; a
Z-number's base-2 expansion is highly constrained. This bounds Z-numbers but does **not** settle
existence.

**Flatto–Lagarias–Pollington (1995).** For every `ξ ≠ 0`,
`sup_n {ξ(3/2)ⁿ} − inf_n {ξ(3/2)ⁿ} ≥ 1/3`. This is a genuine constraint on `{ξ(3/2)ⁿ}` but is
**compatible** with all values lying in `[0,1/2)` (a spread of `≥ 1/3` fits inside an interval of
length `1/2`), so it does **not** refute Z-numbers.

**Transfer to Antihydra?** None of these transfer, for the structural reason in §2: they concern the
single-floor real-`ξ` sequence, whereas Antihydra is an iterated-floor integer orbit, and the parity
functionals differ (`valParity_ne_mahlerParity`). The shared object is only the *weighted* residue
`Tₙ mod 2ⁿ` of R3, on which no nontrivial partial result is currently known. Conversely, an Antihydra
resolution would not obviously settle Z-numbers, for the same reason.

### The two-direction independence, made precise

There are *two* Z-number notions in play, and Hypothesis M/M′ is independent of **both**, in **both**
directions:

* **Real Mahler Z-numbers** `{ξ(3/2)ⁿ} ∈ [0,1/2) ∀n`. Non-existence is a statement about fractional
  parts of `(3/2)ⁿξ`; the Antihydra parity `εₙ` depends on *higher* binary digits of `aₙ`, not just
  `{(3/2)ⁿα}`. So no-Z-numbers neither implies nor is implied by M/M′: M/M′ concerns the *single*
  integer orbit of `8`, while a Z-number is a *special real parameter* — different parameter spaces,
  one cannot control the other.
* **2-adic Z-numbers for `f(x)=⌊3x/2⌋`** — a nonzero `x ∈ ℤ₂` with `fⁿ(x) ≡ 0 (mod 2) ∀n` (orbit
  trapped in the even cylinder). Their non-existence is **trivial** and we *prove the integer shadow*
  (R5, `exists_valParity_one`): if `fⁿ(x) ≡ 0 ∀n` then `fⁿ(x) = (3/2)ⁿx`, needing `2ⁿ ∣ x ∀n`, so
  `x = 0`. But this only says every nonzero orbit leaves the even cylinder *at least once*; M′ needs
  **unbounded** positive Birkhoff sums of `ψ`, and leaving the even cylinder once is fully compatible
  with **bounded** dips. So M/M′ is *strictly stronger* and is **not** decided by the (trivial)
  2-adic-Z-number question.

**What would be strong enough** (not the Z-number problem): a dynamical large-deviation principle for
`(f, ψ)` giving record-positive Birkhoff sums along the orbit of `8`. Equidistribution alone (Birkhoff
averages `→ 0`) is *insufficient* — one needs unbounded *upper excursions*. So Antihydra's
finite-automaton-incompleteness is tied to the **distribution** family of Mahler's `(3/2)ⁿ`-mod-1
program, not to the narrower Z-number confinement question.

> The brief's dependency "Report A (equivalence questions)" was not available; this section supplies
> the equivalence/independence analysis directly. Honest status: **no implication in either direction
> between the Z-number problems and Hypothesis M/M′ (≡ Antihydra unbounded dips).**

### Attack strategies for Hypothesis M′ (open, hard)

The report lists four complementary routes, none currently within reach for a deterministic Mahler
map: (1) **equidistribution + large deviations** for `f` on `ℤ₂` (ergodic theory on `ℤ₂`);
(2) **2-adic discrepancy** via `p`-adic Fourier / exponential sums over the orbit (closest to Mahler's
classical `{(3/2)ⁿ}`-distribution problem); (3) **constructive pattern mining** — an explicit infinite
family of high-excess parity intervals the orbit is shown to revisit (bypasses global
equidistribution); (4) a **conditional derandomization certificate** — show any model consistent with
all finite observations must assign positive probability to arbitrarily large dips. Even a partial
result is valuable: a rigorous matching upper bound `≈ 2.078 ln n` on dip growth, or a proof that
*bounded* dips would force an unlikely regularity of the `⌊3·/2⌋`-orbit.

---

## 5. Status table: known / conjectured / open

| Statement | Status | Where |
|---|---|---|
| `2a_{n+1} + p_n = 3a_n` (defect recurrence) | **known** (proved) | `two_mul_valOrbit_succ_add_parity` |
| `3ⁿc = 2ⁿaₙ + Tₙ` (geometric identity) | **known** (proved) | `valOrbit_geometric_identity` |
| `{(3/2)ⁿc} = (Tₙ mod 2ⁿ)/2ⁿ` (residue bridge) | **known** (proved) | `mahler_residue_eq` |
| `bₙ − b_{n+L} = 3T_{n,L} − 2L` (dip = parity excess) | **known** (proved) | `counter_drop_eq_parity_excess` |
| odd values recur; no all-even orbit (2-adic-Z shadow) | **known** (proved) | `exists_valParity_one`, `valParity_one_frequently` |
| Antihydra orbit ≠ Mahler single-floor orbit | **known** (proved) | `valOrbit_ne_mahlerFloor`, `valParity_ne_mahlerParity` |
| `p`-state regular invariant ⟹ `D(n) < p` | **known** (proved) | `futureDip_lt_card` |
| unbounded dips ⟹ no finite-automaton proof | **known** (proved) | `no_dfa_invariant_of_unbounded_dips` |
| Antihydra never halts | **conjectured / open** | (bbchallenge) |
| Antihydra's future dips unbounded ≡ Hypothesis M/M′ | **conjectured / open** (Mahler territory) | `antihydra_future_dips_unbounded` |
| no real Z-numbers exist | **conjectured / open** | `no_Z_numbers` |
| no 2-adic Z-number for `f` | **known** (trivial; shadow proved as R5) | `exists_valParity_one` |
| `{(3/2)ⁿ}` dense / equidistributed in `[0,1]` | **open** | — |
| dip growth law `D_record(n) ≈ 2.078 ln n` (`q=1/φ`) | **empirical / heuristic** | report §3 |
| any implication between either Z-number problem and Hypothesis M/M′ | **open; none in either direction** | §4 |

---

## 6. Summary

* **Rigorous relationships** (five, all proved): R1 defect recurrence, R2 geometric identity, R3
  Mahler residue bridge, R4 dip = parity excess, R5 odd-values-recur (the 2-adic-Z-number shadow).
  Together they tie the Antihydra orbit, its parity sequence, the counter dips, and the Mahler
  fractional parts `{(3/2)ⁿc}` into one exact algebraic picture.
* **Rigorous non-relationship** (proved): the iterated-floor Antihydra orbit and the single-floor
  Mahler sequence already disagree in parity at `n = 6`, blocking any termwise reduction.
* **The mapping itself** (the valuable deliverable even though the implication question is negative):
  a finite regular invariant ⟹ bounded dips is a *theorem* (`futureDip_lt_card`); by R4 the missing
  step "dips are unbounded" is *exactly* Hypothesis M/M′ — record-positive large deviations of the
  `⌊3·/2⌋` parity sequence over the `2/3` frequency — which is genuinely Mahler-3/2-distribution-hard
  and **independent in both directions** of the (real and 2-adic) Z-number problems. That is the
  precise content of "precisely Mahler-3/2-problem territory".

## References

* K. Mahler, *An unsolved problem on the powers of 3/2*, J. Austral. Math. Soc. **8** (1968), 313–321.
* L. Flatto, J. C. Lagarias, A. D. Pollington, *On the range of fractional parts `{ξ(p/q)ⁿ}`*,
  Acta Arith. **70** (1995), 125–147.
* J. C. Lagarias, *The 3x+1 problem and its generalizations*, Amer. Math. Monthly **92** (1985).
* The Busy Beaver Challenge — *Antihydra*; *Finite Automata Reduction (FAR)* deciders,
  <https://bbchallenge.org>.
* E. Yolcu, S. Aaronson, M. J. H. Heule, *An Automated Approach to the Collatz Conjecture*,
  J. Automated Reasoning (2023); arXiv:2105.14697 (the SRS / mixed-base technique).
