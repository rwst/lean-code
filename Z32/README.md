<!--
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 (public domain).
-->

# Z32 — the confinement atlas for {ξ(3/2)ⁿ}

Milestones **M2**, **M3**, **M6** and **M7** of `plans/plan-cert32.html`: the C prototypes, the
X1/X2/X3 sweeps, the **two-colored atlas draft** — which (position, length)
pairs are certified <span>**empty**</span>, which are certified
<span>**nonempty**</span> in the literature, and what is left in the
<span>**band**</span> between them — and the **Lean bridge** that turns an
engine verdict into a kernel-checked theorem.

The Lean side of the same root (`Dictionary`, `EscapeCert`, `ResidueCapture`,
`DubickasWord`, `SmallInterval`, `BlockCert`, and — for `plans/plan-M5A9.html` —
`EscapeLadder`, `ModelEntropy`) builds with `lake build Z32`, std3, zero cited
axioms, no `native_decide`.

Status of the *numbers* below: **computationally established, pending
independent replication** (plan R-5/R-7, the M2′ precondition inherited from
plan-dubC1); reproducible in a few minutes with `sh reproduce.sh` (except the M6 controls,
which take about an hour). Status of the eight entries listed under
**M3 — the Lean bridge**: *proved*, and no longer resting on any engine — see
that section for what changed.

---

## The model

With `xₙ = ⌊ξ(3/2)ⁿ⌋` and `yₙ = {ξ(3/2)ⁿ}`, the identity `3(xₙ+yₙ) = 2(xₙ₊₁+yₙ₊₁)`
gives the **carry coding** (plan §1.1)

```
  y_{n+1} = (3 yₙ + eₙ)/2 ,   eₙ = 3xₙ − 2xₙ₊₁ ∈ {−2,−1,0,1} ,   eₙ ≡ xₙ (mod 2).
```

Confinement of the orbit to a set `U ⊆ [0,1)` is survival of `y` under this
2-branch interval dynamics. The engines compute, **exactly** (all arithmetic is
integer arithmetic over the denominator `Gden·3^k`, no floating point in any
decision path),

```
  S₀ = U ,   S_{k+1} = U ∩ f⁻¹(S_k) ,   f⁻¹(A) = ⋃_e (2A − e)/3 ,
```

so `S_k` = the points of `U` with an admissible continuation staying in `U` for
`k` more steps. `Z(U) ⊆ ⋂ₖ S_k`, always.

For a single window `[s, s+L)` with `L ≤ 1/2` this is affinely conjugate to the
FLP95 picture that `FLP/` formalizes: `θₙ = q({ξ(3/2)ⁿ} − s)` (`FLP.thetaPart`)
satisfies `θₙ₊₁ = f_{β,α}(θₙ)` with `β = 3/2`, `α = {(p−q)s} = s`
(`FLP.alphaSym`), and the survival threshold is `qL = 2L` — at `L = 1/3` exactly
`FLP.survivors (3/2) s`. `hold.c` runs that coordinate, `atlas.c` runs the
`y`-coordinate directly; they are independent implementations of the same
question and agree everywhere they overlap.

### The two certificates

**KILL n** — `S_n = ∅`. Unconditional: no `ξ > 0` has its whole orbit in `U`.
Needs no theory at all.

**CYCLE** — `S_k` is covered by disjoint rational intervals `H₁…H_m` such that
the transition relation

> `i → j` iff `(3·H_i + e)/2` meets `H_j`, for some carry `e`

is a **partial function** (out-degree ≤ 1, so the carry is determined by the
block). Then a confined orbit walks a functional graph, hence its block
itinerary — and therefore its **carry word** — is eventually periodic. But the
carry word of *every* `ξ ≠ 0` is aperiodic:

> `Z32.not_isEventuallyPeriodic_carry` (= [DN05] Lemma 2), **proved** in
> `Z32/DubickasWord.lean`, std3, no cited axiom, no hypothesis beyond `ξ ≠ 0`
> and `p, q` coprime with `p > q > 1`.

So `Z(U) = ∅`. This is DubC's `C(𝒫)` certificate ("no branching SCC ⇒ every
path eventually periodic ⇒ the avoiding ξ are rational ⇒ contradiction")
transplanted to the fractional side, and it is the reason the engine covers the
FLP positions, whose survivor set is a nonempty finite cycle. **It also removes
the plan's R-8 risk**: FLP95's Thm 3.2 (finite survivors ⇒ `Z` empty) is stated
at window length `1/p`, and §4.1(b) flagged its generalization as the plan's own
analytic work. The CYCLE certificate needs no such generalization — it needs no
decoupling, no threshold hypothesis, and it works for unions.

**FAT** — the component count keeps growing: the survivor set is infinite and
the engine decides nothing. `λ` = growth rate of the component count;
`dim_box ≤ log λ / log(3/2)` is the T5 dimension datum. Reported, never hidden.

---

## Results

### X1 — the FLP control, and the length-1/3 line

The five FLP95 Cor 1.4a positions regenerate digit for digit, with the paper's
own escape witnesses:

| s | orbit of 0 under `f_{3/2,s}` | escape N |
|---|---|---|
| 1/6 | 0 → 1/6 → 5/12 → 19/24 | **3** |
| 1/3 | 0 → 1/3 → 5/6 | **2** |
| 1/2 | 0 → 1/2 → 1/4 → 7/8 | **3** |
| 2/3 | 0 → 2/3 | **1** |
| 0 | fixed point, no escape | — |

The exact pruning then reproduces **FLP95 Thm 3.4's trichotomy** as a
measurement: the survivor set has *exactly* `N` components, `N` = the escape
depth (1, 3, 2, 3, 1 at s = 0, 1/6, 1/3, 1/2, 2/3), in both coordinate systems.
The certificates are the exact rational cycles — e.g. at `s = 1/6` the survivor
set is `{4/19, 6/19, 9/19}` with carry word `(0,0,−1)`, denominator `3³−2³ = 19`.

Sweeping every rational position `s = i/G` at `L = 1/3`:

| G | 6 | 12 | 24 | 48 | 96 | 192 | 384 | 768 | 1536 | 3072 | 3888 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| positions | 5 | 9 | 17 | 33 | 65 | 129 | 257 | 513 | 1025 | 2049 | 2593 |
| certified | **all** | all | all | all | all | all | all | all | all | all | **all** |
| max escape depth | 3 | 7 | 11 | 11 | 13 | 13 | 14 | 21 | 21 | 23 | 25 |

**X1's open half is answered, negatively and informatively**: there are *no*
stubborn positions at any rational `s` with denominator ≤ 3888. That is exactly
what [Bug04]/[Kwon15] predict — the exceptional set `E_{3/2}` is
Sturmian-parametrized and of Hausdorff dimension 0, so **no rational sweep can
ever meet it**. The stubborn positions are invisible to this experiment by
nature, not by budget; the length-1/3 line is closed in Lean anyway
(`Z32.ZSet_three_two_third_empty`, all real `s`).

### X2 — the (position, length) map, and the frontier

Full sweep at `G = 360`, all positions, `L = 1/3 … 1/2`, depth 30
(`data/x2_G360.txt`). Fraction of positions certified:

| L | 1/3 | .3361 | .3444 | .3556 | .3667 | .375 | .3833 | .3944 | .4028 | .4056 | ≥ .4083 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| certified | **100 %** | 79.2 % | 55.3 % | 37.3 % | 26.6 % | 22.1 % | 13.0 % | 10.0 % | 6.5 % | 3.7 % | **0 %** |

Refined at `G = 3600`: the last certified length **in this search mode** is

> **L\* = 1466/3600 = 0.407222…**, at 14 positions
> (i/3600 ∈ {961, 965, 971, 985, 986, 1018, 1026, 1108, 1116, 1148, 1149, 1163, 1169, 1173}),

and a full-range scan at `j = 1467…1500` certifies **nothing**, anywhere. The
surviving positions concentrate in `s ∈ [0.267, 0.326]`.

> **Superseded 2026-09-03 by experiment X-F** (see *The frontier, and its exact object* below):
> `L*` is the frontier of the **hull-merge** search, not of the certificate family.
> Rank-stratified, the same row certifies 213 of 236 positions, the corpus now ships a window of
> length `3/7 = 0.4286`, and the family's exact ceiling on the centred line is the Thue–Morse
> constant `(1 − T(2/3))/2 = 0.4287053…`.  Everything else in this section stands.

Three consequences.

1. **M4's decision point (a) is dead.** The certified fraction falls off 100 %
   *immediately* above `L = 1/3` (79 % at `L = 1/3 + 1/360`). There is no
   uniform `δ > 0` reachable this way, so a strengthening of
   `FLP.three_halves_spread` to `1/3 + δ` is not what this engine can deliver.
   The M4 lane is **(b): the two-colored atlas**.
2. **New atlas entries above the 1995 line.** Emptiness of a *longer* window is
   strictly stronger than emptiness of a shorter one, so every certified entry
   with `L > 1/3` is beyond both FLP95 (which certifies only at `t = 1/p`) and
   [Dub09AA] (all `s`, but only at `1/3`). The best is length **0.40722**.
3. **The band below `L*` is provably a band for this model class.** The
   `horse` mode enumerates all cycles of period ≤ P exactly (a period-P cycle is
   the rational `−(Σ 3^{P−1−i}2^i w_i)/(3^P − 2^P)`), giving a *rigorous* lower
   bound on the survivor set:

   | entry | cycles P≤6 | P≤9 | P≤12 |
   |---|---|---|---|
   | certified, e.g. `[1/3,2/3)` or `[4/24,13/24)` | 1 | 1 | 1 |
   | band, e.g. `[0,10/24)` or `[0,150/360)` | 4 | 8 | **16** |

   The count doubles: the hold set of a band entry contains exponentially many
   distinct confined orbits, so **no argument that looks only at the archimedean
   hold set can settle it** — those entries need the dyadic product refinement
   (plan §4.3, experiment X4). The band is a theorem about the method, not a
   budget shortfall.

T5 dimension data comes free from the same run (`dim_box ≤ log λ / log(3/2)`):

| L | .3361 | .3528 | .3694 | .3861 | .4028 | .4194 | .4361 |
|---|---|---|---|---|---|---|---|
| λ (max over positions) | 1.165 | 1.229 | 1.285 | 1.325 | 1.345 | 1.370 | 1.359 |
| dim bound | 0.378 | 0.509 | 0.618 | 0.694 | 0.730 | 0.776 | 0.756 |

(These bound the *hold set*, not `Z_ev(U)`; the T5 target needs the covering
argument of plan §7, which is M5 work. Reported here as calibration.)

### X3 — unions

**Literature controls (positive).**

| set | \|U\| | engine verdict |
|---|---|---|
| [Dub08] Cor 1.2: `[8/39,18/39) ∪ [21/39,31/39)` | 20/39 = .5128 | **CYCLE**, 4 blocks — cycle `{2/5,3/5}`, transients `{4/15,11/15}` |
| [Dub06] complement: `[0,0.238117) ∪ [0.761883,1)` | .476234 | **FAT** — components 394 → 2212 → 9836 → 29472 at depth 12/20/30/40, λ ≈ 1.15 |

So the engine independently reproduces the **half-open shadow** of [Dub08]
Cor 1.2 — the strongest published *explicit* union-emptiness result. `atlas.c`
is half-open throughout, so this row is the shadow and not the corollary; the
printed statement closes both intervals and is strictly stronger. The closed
form is reached instead by `gencert.py --closed --ranked` and proved in Lean —
see the M3 section, which is where the difference turns out to have real
content. It does **not** reach
[Dub06]: there the hold set grows steadily, so that theorem uses more than the
archimedean hold set, and the entry stays in the band. Both engines agree on
both verdicts (394 components at depth 12 for [Dub06], independently).

**Literature controls (negative) — the soundness test that matters.** Every set
the literature proves *nonempty* must come back undecided, and does:

| set | \|U\| | source | verdict |
|---|---|---|---|
| `[0,1/6) ∪ [1/3,2/3) ∪ [5/6,1)` | 2/3 | [KK18] Cor 4.8 (nonempty) | FAT ✓ |
| `‖·‖ < 1/3` | 2/3 | [Dub10] (1.1) (nonempty) | FAT ✓ |
| `[4/65,61/65)` | .8769 | [Pol81] (positive dim.) | FAT ✓ |
| `(5/48,43/48)` | 19/24 | [Dub08] Thm 1.3 (nonempty) | FAT ✓ |
| `[1/19,18/19)` | 17/19 | [Cho80] (nonempty) | FAT ✓ |

**The largeness record (T2(c)).** Goodness is downward closed, so maximal
certified unions can be searched exhaustively at coarse resolution and then
refined (a certified union is the same *set* at any finer grid, so refining can
only help):

| cells N₀ | 12 | 16 | 18 | 20 | 24 | 30 | 36 | 48 | 60 | 120 | 240 | 480 | 720 | 1440 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| method | exh | exh | exh | exh | rnd | rnd | rnd | rnd | rnd | climb | climb | climb | climb | climb |
| best \|U\| | .5833 | .6250 | .6667 | .6000 | .6667 | .6667 | .6944 | .7083 | .7167 | .7250 | .74167 | .74583 | .75000 | **.754167** |

The last three columns were added at experiment X-U (2026-09-03), restarting
`x3climb.py` from the refined 240-record; each verdict was re-checked by the
independent exact funnel in `xu.py`, and each greedy pass bought exactly 1/240
of measure.  The 720-cell record is `540/720 = 3/4` exactly.  All of them are
engine output: at depth 29 with 2801 blocks the certificate data is far outside
the kernel's `decide` budget (see [Why not the 0.7417 record](#why-not-the-07417-record)).

The 240-cell record union (178 of 240 cells, total length 89/120), the largest
one small enough to print:

```
[0,1/30) [1/20,2/15) [3/20,1/5) [13/60,11/30) [5/12,13/30) [9/20,8/15)
[11/20,19/30) [161/240,23/30) [19/24,191/240) [4/5,13/15) [9/10,14/15)
[19/20,79/80) [119/120,239/240)
```

certified CYCLE at depth 30 with 3783 components merging into 2512 blocks, all
of out-degree 1 (the exact funnel of `xu.py` reproduces its level counts
bit-for-bit and reaches out-degree 1 one step earlier, at depth 29 with 2526
blocks — the two implementations coalesce hulls in a different order).
**The current record is 0.754167 against [Dub08] Cor 1.2's 20/39 = 0.5128**,
the best explicit certified-empty union in the twenty-eight sources read at
M0 — i.e. a record on the curve that [KK18] **Problem 6.1** asks about (make
Thm 5.9's non-constructive total-length-`1−ε` union explicit). The curve is
still climbing under refinement, which is the expected shape if Thm 5.9 is the
limit. *Claim the record on the curve, never the problem* (plan R-1).

Note the two colors genuinely interleave: [KK18]'s **nonempty** union has total
length 2/3 < 0.7417. Total length alone decides nothing — which is precisely why
the atlas is a table and not an inequality.

**What the records actually do to the cycles.** Experiment X-U ran the complete
census of the 531 292 orbits of period ≤ 14 (7 138 565 points) against all four
records.  Each keeps **one or two** of them: the fixed point 0, and at the 43/60
and 89/120 records the 3-cycle `2/19 → 3/19 → 14/19`.  So the removed set is a
*transversal* of the cycle census, and that is forced, not incidental — see
[Cycles and the transversal](#cycles-and-the-transversal-x-u) below.

---

## M3 — the Lean bridge

The engines decide; the kernel now checks. `Z32/BlockCert.lean` formalizes the
CYCLE certificate and re-verifies six of the entries above from scratch, with
`decide` — **no `native_decide`, no floating point, no cited axiom**, footprint
`[propext, Classical.choice, Quot.sound]` on every exported declaration.

Since M6 the file is stated for an arbitrary base `p/q`; the `(3,2)` reading
below is the special case its first six entries use. See
[M6 — a second base](#m6--a-second-base).

### What is checked

A certificate for a set `U` is a *funnel* of interval lists

```
  T₀ = U ⊇ T₁ ⊇ … ⊇ T_K =: H   (the blocks),
```

all endpoints integers over one common denominator `D = G·p^K`, subject to two
conditions that are pure integer arithmetic:

| check | statement | consequence |
|---|---|---|
| `funnelOk` | for every `I ∈ T_k`, carry `s`, `J ∈ U`: the piece `{y ∈ J : (py−s)/q ∈ I}` lies in a **single** interval of `T_{k+1}` | a confined orbit lies in every `T_k`, hence in `H` |
| `funcOk` | with the blocks stratified by rank: no successor of larger rank, at most one of equal rank | the rank along an orbit is a non-increasing `ℕ`, hence eventually constant; from there the itinerary is deterministic ⇒ eventually periodic ⇒ so is the carry word |

`strata := []` gives every block rank `0`, and `funcOk` is then the plain "at
most one outgoing edge" condition — which is what five of the six entries use.
The certificate also carries a `closed` flag: with `closed := true` every
interval it mentions is `[a/D, b/D]` rather than `[a/D, b/D)`, and every
comparison flips (a piece is empty iff `hi < lo`, two intervals meet iff they
touch). Both fields default to the old behaviour.

and the carry word of every `ξ ≠ 0` is aperiodic
(`Z32.not_isEventuallyPeriodic_carry`, proved at M1-bis). Hence `Z(U) = ∅`.

`min`/`max` are expanded by hand into disjunctions, and everything is scaled by
`pD`, so the kernel only ever compares integers — which is why the whole file
elaborates in about 16 s (eight certificates).

`Z32/gencert.py` re-runs the exact pruning and emits the funnel; `reproduce.sh`
regenerates all eight and `diff`s them against the file. **The Lean file trusts
no engine**: the conditions are rechecked by the kernel from the literal data.

### The eight entries

| entry | \|U\| | Lean name | funnel |
|---|---|---|---|
| `[1/6, 13/24)` | .375 | `Z32.ZSet_three_two_sixth_3_8` | depth 8, 3 blocks |
| `[961/3600, 2427/3600)` | .40722 | `Z32.ZSet_three_two_frontier` | depth 13, 2 blocks |
| `[8/39,18/39] ∪ [21/39,31/39]` **closed** | 20/39 | `Z32.dubickas_2008_cor_1_2` | depth 3, 12 blocks, 4 rank strata |
| 4-interval union | 7/12 | `Z32.union_seven_twelfths_empty` | depth 7, 1 block |
| 5-interval union | 2/3 | `Z32.union_two_thirds_empty` | depth 9, 12 blocks |
| 6-interval union | **25/36** | `Z32.union_record_empty` | depth 11, 17 blocks |
| `[1/3, 5/8)` at **4/3** | 7/24 | `Z32.ZSet_four_three_beyond_line` | depth 5, 2 blocks |
| `[1/5, 2/5)` at **5/2** | 1/5 | `Z32.ZSet_five_two_fifth` | depth 1, 1 block |

`Z32.not_eventually_mem_sixth_3_8` is the *eventual* form of the first entry
(shift trick, `Z32.mem_ZSet_of_eventually`), and the soundness theorem
`Z32.BlockCert.Cert.not_confined` covers every `ξ ≠ 0` — the certificate never
uses the sign, so these are slightly stronger than the `FLP.ZSet` statements.

Three of these are worth separating out.

1. **`[1/6, 13/24)` is past the 1995 line.** [FLP95] Corollary 1.4a certifies
   emptiness only at length `1/p = 1/3`, and [Dub09AA] Theorem 1 covers every
   position but again only at `1/3`. This window has length `3/8 = 0.375`.
2. **[Dub08] Corollary 1.2 as printed, closed** — the strongest *explicit*
   union-emptiness statement in the twenty-eight sources read at M0, and the
   only entry needing both general features of the certificate (M4′ item P1,
   landed 2026-07-27). The closed/half-open gap has content: the closed set
   contains the 4-cycle `6/13 → 9/13 → 7/13 → 4/13`, which runs through the
   right endpoint `18/39 = 6/13`.

   The prediction attached to P1 in the plan — "expected to succeed, since
   tolerating cycles is what this method does" — was **half right, and the
   wrong half is the interesting one**. Closing the endpoints does not merely
   admit one more cycle: the hold set acquires an infinite backward tree of
   transients feeding *two* disjoint cycles (the 4-cycle and `{2/5, 3/5}`), and
   with it four components per level forever. Measured to depth 40, **no
   partition into blocks of out-degree 1 exists at any depth** — the greedy
   hull merge collapses to a single block with out-degree 2 every time, and
   fattening the half-open set instead of closing it behaves identically. What
   does exist, at depth 3, is a *rank stratification* of the twelve raw
   components: rank 0 is the 4-cycle, rank 2 the two fat blocks holding
   `{2/5, 3/5}` (which also escape downward), ranks 1 and 3 transients. So P1
   cost a genuine weakening of `funcOk`, not just a flag.
3. **`25/36 = 0.6944…` is the formalized union-largeness record**, against
   `20/39 = 0.5128…` in print. Note again that [KK18] Corollary 4.8's
   **nonempty** union has total length `2/3`, and `Z32.union_two_thirds_empty`
   is an **empty** one of exactly the same total length.

### Why not the 0.7417 record (nor the 0.754167 one)

The engine's best union (240 cells, §X3) has 3783 surviving components at depth
30. The funnel for it is thousands of intervals wide, and `decide` cost grows
like `Σ_k |T_k|·|T_{k+1}|·4·|U|`. The 48-cell record (`0.7083`) already
projects to ~4 minutes of kernel time; `25/36` costs about 6 s. Narrowing the
funnel — coarsening the intermediate levels outward, which is sound and only
needs the *containment* to survive — is the obvious next engineering step and is
not on the M3 critical path. The three X-U records (480, 720 and 1440 cells) are
in the same regime, 2526 to 2801 blocks at depth 29, and are equally out of
reach; and X-U's depth–size bound `K + log_{3/2}(B) ≳ 1/(1−|U|)` says the cost
can only grow as the record climbs.

### Negative controls, again

The generator refuses all five sets known nonempty in print
(`[4/65,61/65)`, `[1/19,18/19)`, `[5/48,43/48)`, `‖·‖<1/3`, `X_{3,2}`): no
certificate within depth 60, in the default mode and in the stronger
`--closed --ranked` mode alike. Three Lean lemmas record that the checks have
teeth: `ok_eq_false_of_full` (`[0,1)` fails, its single block has all four
carries outgoing), `ok_eq_false_of_full_closed` (nor does `[0,1]` with a rank of
its own), and `ok_eq_false_of_not_coprime` (a non-coprime base is refused — at
`4/2 = 2` the point `ξ = 1/3` has the periodic orbit `1/3 → 2/3`, so a
certificate there would prove a falsehood).

A certified window is **not** one whose interval-map hold set is empty: at
`[1/6, 13/24)` the hold set is exactly the 3-cycle `4/19 → 6/19 → 9/19` with
carries `(0,0,1)`, and the C engine's `e = (0,0,−1)` is its negative, as the
conventions demand. What the certificate rules out is a *real number* whose
fractional parts follow that cycle.

---

## M6 — a second base

Every engine here, and the Lean bridge, were hardwired to `3/2`: the four
carries `{−1,0,1,2}` and the literals `2` and `3` in the piece arithmetic. **The
mathematics never was.** `Z32.not_isEventuallyPeriodic_carry` — the sole
analytic input — is proved for every coprime `p > q > 1` and every `ξ ≠ 0`, and
`Z32.carry_eq` is stated for general `p, q`. So M6 is a parameterization, not a
research step, and `Cert.not_confined` generalizes with the same proof.

What changes, and nothing else does:

| | at `3/2` | at `p/q` |
|---|---|---|
| carry alphabet | `{−1,0,1,2}` | `{−q+1, …, p−1}`, i.e. `p+q−1` letters |
| branch-`s` preimage of `[a,b)` | `[(2a+s)/3, (2b+s)/3)` | `[(qa+s)/p, (qb+s)/p)` |
| common denominator | `G·3^K` | `G·p^K` |
| `hits` | `3·I₁` vs `2·J₂+sD` | `p·I₁` vs `q·J₂+sD` |

`Cert` gained two fields, `p := 3` and `q := 2`, so **no `(3,2)` certificate
mentions the base**, and `Cert.ok` gained three decidable side conditions —
`1 < q`, `q < p`, `gcd p q = 1` — which are exactly the hypotheses of the
aperiodicity lemma. That is why `Cert.not_confined` still takes no hypothesis
but `ok` itself. `gencert.py --pq p q` emits the base only when it is not
`3/2`; all eight certificates in `BlockCert.lean` regenerate byte-identically,
and `--pq 3 2` reproduces the default path exactly.

**Scope.** The *certificate* path — `gencert.py` → `BlockCert.lean` — is
parametric. The three C *search* engines (`atlas.c`, `hold.c`, `gridcert.c`)
are not, and remain `3/2`-only; the `(4,3)` and `(5,2)` sweeps quoted below ran
on the Python pipeline. Parameterizing the C engines is what a full second
atlas *column* (an X2-scale `(p,q)` map) would need, not what entries need.

### The controls are the point

A second base gives soundness tests the `(3,2)` engine could not run. Run by
`pqcontrols.py`, exact `Fraction` arithmetic, output in `data/m6_controls.txt`:

| | what the literature says | what the engine does |
|---|---|---|
| **(A)** windows of length `1/p`, `1 < q < p < q²` | [Dub09AA] Thm 1: **empty**, every real `s` | **8/8 certified** at each of `(4,3)`, `(5,3)`, `(5,4)`, `(7,5)`. Funnel depth up to 26 at `(4,3)` — the two windows at `1/4` and `1/2` need 26 levels, and a scan cut off at depth 25 wrongly reports them unresolved |
| **(B)** two-cell sets at `p > q²` | [Aki08] Thms 2.4/2.5: **nonempty** Cantor sets of dimension `log q / log(p/q)` | FAT (>1000 components by depth 9) at `(5,2)`, `(7,2)`, `(9,2)` — refused, as it must be |

(A) is a genuine cross-check rather than a new result: the general statement is
`Z32.ZSet_eq_empty_of_lt_sq` in `Z32/SmallInterval.lean`, proved by the Sturmian
route of [Dub09AA]. The block certificate reaches the same conclusion by a
completely different argument. It is not formalized a second time.

### Past the line at `4/3`, and the `p > q²` regime

The `(4,3)` sweep gives a **lower bound** on the frontier for a single
non-wrapping window, not the frontier: length `70/240 = 0.29167` still certifies
at 10 positions (denominator `240`, funnel depth `≤ 20`). A scan of
`72/240 … 94/240` found nothing, **but only to depth 14** — and `(4,3)` is
precisely the base whose length-`1/4` windows need depth **26**, so that scan
proves nothing and the frontier above `0.2917` is open. Against `1/p = 0.25` in
print, that is an overshoot of at least `1.17×`, against `1.22×` (`0.40722` over
`1/3`) at `(3,2)`. `Z32.ZSet_four_three_beyond_line` formalizes
`Z_{4/3}(1/3, 5/8) = ∅`, length `7/24 = 0.2917`.

For `p > q²`, [Dub09AA] §4 says Theorem 1 is **open** — his counting step needs
`p < q²`. The block certificate has no such step, and it certifies *every*
length-`1/p` window tested at `(5,2)`, `(7,2)`, `(9,2)`, `(10,3)`, `(11,3)`,
mostly at depth 1. `Z32.ZSet_five_two_fifth` formalizes one of them,
`Z_{5/2}(1/5, 2/5) = ∅`; its certificate is small enough to check by hand.

**That is not the open theorem, and the gap does not close.** Theorem 1
quantifies over all real `s`; a certificate handles one rational window. The
natural upgrade is a cover — certify the `N` windows `[i/N, i/N + 1/N + 1/p)`
mod 1, and every real window of length `1/p` sits inside one of them, so
`Z32.ZSet_mono` would give the general statement. Measured, it fails:

| base | `N` | element length | certified |
|---|---|---|---|
| `(5,2)` | 5 / 10 / 20 | .4000 / .3000 / .2500 | 0/5, 2/10, **8/20** |
| `(7,2)` | 7 / 14 / 28 | .2857 / .2143 / .1786 | 0/7, 4/14, **14/28** |
| `(9,2)` | 9 / 18 / 36 | .2222 / .1667 / .1389 | 0/9, 6/18, **20/36** |
| `(10,3)` | 10 | .2000 | 0/10 |

The failures are FAT, and the first one is always `i = 0`: the fattened window
contains `0`, which is the fixed point of the `s = 0` branch — the degenerate
position the plan warns about, and the one `FLP.ZSet_empty_zero` handles
separately at `(3,2)`. But they are not *only* degenerate: at `(5,2)` with
`N = 20`, twelve of the twenty fail. So the `p > q²` column is a finite list of
rational windows, **not** the open theorem, and there is no tension with
[Aki08]'s nonempty Cantor sets — the fattened windows are exactly large enough
to hold them. Whether the block certificate can be pushed to a uniform argument
is open; this measurement says the cheap route does not.

---

## M7 — [Aki08] Conjecture 1.4, and the end of the product refinement

**The conjecture** ([Aki08] pp. 92–93): there is no `x > 0` with
`{x(4/3)ⁿ} ∈ [0,¼) ∪ [¾,1)` for every `n ≥ 0`, equivalently `‖x(4/3)ⁿ‖ < ¼`
for all `n`. Akiyama works half-open throughout, so this is verbatim a question
about `U = [0,¼) ∪ [¾,1)` at the base `4/3`.

The archimedean engine cannot touch it: `U` is **exactly forward-invariant**
(`S₁ = U`, hence `S_k = U` for all `k`), so there is no KILL, and the block
graph is `U`'s own two intervals with a nowhere-functional transition relation.
The plan therefore routed M7 through §4.3's **product refinement**: a state
becomes a pair `(cell, xₙ mod qʲ)`, and the two coordinates constrain each
other, because `q x_{n+1} = p xₙ + sₙ` forces

    sₙ ≡ −p xₙ  (mod q),

so the branch is *determined* by the residue — one carry out of `q` instead of
`q`. `prodcert.py` implements it, and the answer is that the machine is empty.

### Theorem A — the residue coordinate is free

> Let `S_k` be the archimedean hold set at depth `k` and `S_k⁽ʲ⁾[r]` the product
> one at level `j`. Then for every `k` and every `j`, `⋃_r S_k⁽ʲ⁾[r] = S_k`.

*Proof.* `⊆` is the projection. For `⊇`, take an archimedean chain
`y₀,…,y_k ∈ U` with carries `s₀,…,s_{k−1}`. Since `gcd(p,q) = 1`, `p` is
invertible mod `qʲ`, so choose **any** `r_k ∈ ℤ/qʲ` and run the residues
*backward*, `r_i := p⁻¹(q r_{i+1} − s_i)`. That is a legal product chain lying
over `y`. ∎

The whole content of the refinement is `q | p x + s`, and it costs exactly what
it buys: forcing the carry divides the branching by `q`, and the `q` lifts of
`x_{n+1} mod qʲ` — which `q x_{n+1} = p xₙ + sₙ` pins only mod `q^{j−1}` —
multiply it straight back. **So the product engine reports KILL at exactly the
archimedean depth, never one step earlier, at any level, any base, any `U`.**
The dyadic ladder cannot empty a set the archimedean engine could not.

### Theorem B — cycle counting lifts, so certificates are capped

> If the hold set of `U` carries `N` distinct periodic orbits, every product
> certificate for `U` — at every level `j` — needs at least `N` blocks. In
> particular, a hold set with infinitely many periodic orbits admits **no**
> product certificate at any level.

*Proof.* Each periodic orbit lifts: run the residues backward as above; over one
period the return map on `ℤ/qʲ` has linear part `p^{−P} q^P`, which vanishes
once `P ≥ j` (replace `P` by a multiple if not), so it is constant and has a
fixed point — a periodic path in the product graph. Conversely a functional
block graph determines, from a block, the entire forward path *and its carry
labels*; and the carries determine the point, since
`yₙ = Σ_{i≥0} qⁱ s_{n+i} / p^{i+1}`. So `orbit ↦ block containing y₀` is
injective. (For the rank-stratified variant, take the block at which the rank
stabilizes: an infinite path has eventually constant rank and is deterministic
from there.) ∎

Theorem B is §4.4's archimedean no-go, lifted verbatim to every level. It is
also the reason a functional certificate means what it means: a hold set with a
CYCLE certificate has **at most one point per block**.

### The measurement

`prodcert.py`, exact `Fraction` arithmetic, output in `data/m7_controls.txt`:

| | | |
|---|---|---|
| **(A0)** Theorem A itself, 5 sets at 3 bases, `j = 1,2,3` | `⋃_r S_k⁽ʲ⁾[r] = S_k` **at every depth**, no mismatch anywhere | the theorem tested as an identity, not through its consequences |
| **(A)** its consequence, 8 sets at `(3,2)`, `j = 1,2,3` | no level ever KILLs earlier than `j = 0` | and on the three entries that certify, the product needs a **deeper** funnel: `certWindow38` 8 → 8, 8, 9; `certUnion712` 7 → 8, 9, 10; `certFrontier` 13 → 13, 14, 15 |
| **(B)** the five sets known nonempty in print | STABLE at every level, never certified | as it must be |
| **(D)** `(4,3)`, Akiyama's `U`, `j = 1…5` | nonempty, exactly invariant, out-degree 2 at every level | `2^{j+1}` components of length `(¾)ʲ/4` over `2^{j+1}−2` residues mod `3ʲ`; mass `3ʲ/2^{j+1}` |
| **(E)** the periodic-orbit census | **`2^L − 1`** points of period dividing `L`, `L ≤ 13`, at `(4,3)` | a full 2-shift ⇒ Theorem B ⇒ no certificate at any level |

The `2^L − 1` is not a coincidence and does not need the machine. On `U` the two
inverse branches

    h_A(y) = ¾y  on [0,¼),  (3y−2)/4 on [¾,1)   → image [0,¼)
    h_B(y) = (3y+3)/4       , (3y+1)/4          → image [¾,1)

both map `U` into `U` with disjoint images and ratio `¾`, so `{h_A, h_B}` is a
horseshoe: every word in `{A,B}^L` has a fixed point, giving `2^L` periodic
points minus the one at `y = 1` that the half-open convention excludes.

**So M7 exits negatively, and rigorously: no block certificate — archimedean or
product, at any level `j` — can prove [Aki08] Conjecture 1.4.** This is exit
(β) of the plan, and it is stronger than the plan asked for: the no-go covers
all levels at once, and Theorems A/B cover all `U` and all bases.

### It is not evidence about the conjecture

Run the identical census at `(3,2)` on `‖ξ(3/2)ⁿ‖ < ¼`'s analogue
`U = [0,⅓) ∪ [⅔,1)` and the counts are **the same `2^L − 1`** — and there
[Dub10] *proves* the set nonempty. The two cases are indistinguishable to this
entire certificate family, so the obstruction says nothing about whether
Akiyama is right.

### X4 answered, and one caveat

X4 asked for the crossover curve of the dyadic ladder near `L = ½`. It is flat.
Theorem A rules out a KILL gain outright; measured at the frontier
`L* = 1466/3600`, `j = 0…3`, funnel depth 30:

| length | `j=0` | `j=1` | `j=2` | `j=3` |
|---|---|---|---|---|
| `1466` (certified) | CYCLE @13 | CYCLE @13 | CYCLE @14 | CYCLE @15 |
| `1467` (band) | — | — | — | — |
| `1470` (band) | — | — | — | — |

(`—` = undecided to depth 30, with the CYCLE test actually run at every level:
the component count stayed under the 400 cap where the cubic block merge would
have been skipped.)

**Caveat, and it matters: the band is not proven out of reach.** Theorem B
bounds a certificate below by the periodic-orbit count, and at these band
entries that count is *small* — 1, 2 and 3 orbits respectively out to period 20
(`[0,2,0,2,…]` with one extra orbit appearing at period 14, and at 12 for
`1470`). So the theorem does not bite there. The correct statement is that this
engine fails on the band, not that every engine must. `L*` remains the frontier
of what is *certified*, not a proved wall.

---

## The `φ_model` ledger (plan-M5A9 milestone N2(a))

The M7 census says the band and the two-cell holes are *fat*, but a count of
periodic orbits is not a growth rate. `Z32/ModelEntropy.lean` replaces the
count by the quantity plan-M5A9 §2 asks for — the entropy of the carry language
of the hold set,

```
  phi_model(U) := limsup (1/n) log #{ carry words of length n realised
                                      by a model orbit confined to U } ,
```

and proves both colors of the ledger. **Neither side is a statement about real
`ξ`**: `phi_model` is a property of the interval-map model, i.e. of what this
family of certificates can and cannot decide (plan risk R-B).

| set | `\|U\|` | certificate | `phi_model` | Lean name |
|---|---|---|---|---|
| `[1/6, 13/24)` | .375 | `certWindow38` | **0** | `Z32.phiModel_eq_zero_window38` |
| `[961/3600, 2427/3600)` | .40722 | `certFrontier` | **0** | `Z32.phiModel_eq_zero_frontier` |
| the five other `strata = []` entries | — | `certUnion712`, `certUnion23`, `certUnion2536`, `certFourThree`, `certFiveTwo` | **0** | `Z32.phiModel_eq_zero_of_cert` |
| `[8/39,18/39] ∪ [21/39,31/39]` closed | 20/39 | `certDub08` (rank-stratified) | 0 (polynomial path count; **not formalized**) | — |
| band `[0, 5/12)` | .41667 | `Z32.horseBand` — 4 words, `L = 6`, `K = [0,1/9]` | **≥ (log 2)/3 = .2310** | `Z32.log_two_div_three_le_phiModel_band` |
| band `[0, 5/12)` | .41667 | `Z32.horseBandRecord` — 14 words, `L = 10`, `K = [0,11/90]` | **≥ (log 14)/10 = .2639** | `Z32.log_fourteen_div_ten_le_phiModel_band` |
| two-cell `[0,1/3) ∪ [2/3,1)` | 2/3 | `Z32.horseTwoCellSmall` — 4 words, `L = 3`, `K = [0,5/19]` | **≥ (log 4)/3 = .4621** | `Z32.log_four_div_three_le_phiModel_two_cell` |
| two-cell `[0,1/3) ∪ [2/3,1)` | 2/3 | `Z32.horseTwoCell` — 16 words, `L = 5`, `K = [0,65/211]` | **≥ (4/5)·log 2 = .5545** | `Z32.four_fifths_log_two_le_phiModel_two_cell` |
| [Dub06] complement | .476 | none found to `L = 7` | engine `λ ≈ 1.15` only | — |

### The certificate

A **horseshoe certificate** is the mirror image of a funnel. Where `BlockCert`
pushes an orbit *forward* into blocks with the expanding branches, this one
carries a closed interval *backwards* with the contracting inverse branches
`h_s(x) = (qx+s)/p`: a base interval `K = [A/D, B/D]` and `N` distinct words of
a common length `L` with

```
  H_{(s_i..s_{L-1})}(K) ⊆ U  for every i < L,     H_w(K) ⊆ K ,
```

all endpoint tests being integer comparisons over `D·p^j`, so the kernel
re-checks the whole thing with `decide`. Every concatenation of the `N` words
then fixes a point of `K` — by the intermediate value theorem, no compactness
and no limits — whose entire orbit stays in `U`, so the language holds at least
`N^k` words of length `kL` and `phi_model ≥ log N / L`.

Two things the search settles. First, **the branching is not at a point**: no
point of any of these hold sets carries two distinct return words of the same
length (checked exhaustively to `L = 6`), so a "two loops at one point"
certificate does not exist and the interval form is necessary. Second, the
minimal candidate for `K` is forced — any invariant `K` contains the fixed point
of each `H_w`, so the hull of those fixed points is optimal and the search over
hulls is exhaustive at each length.

### What the numbers mean

`(log 2)/3` on the band entry is exactly the figure plan-M5A9 §2 reads off the
cycle counts `4/8/16` at periods `≤ 6/9/12`; the certificate turns that reading
into a theorem, and the 14-word entry then passes it. At the two-cell hole the
census measures a **full** 2-shift, and the family `N = 2^{L−1}` on
`K = [0, (3^{L−1}−2^{L−1})/(3^L−2^L)]` certifies `((L−1)/L)·log 2` at every `L`,
so the certified bound tends to `log 2` without ever reaching it: at `L = 1`
invariance would force `K = [0,1]` and hence `U = [0,1]`. That is the precise,
non-negotiable form of the landmine plan-M5A9 flags in N2(d) — the `(4,3)`
disjoint-images horseshoe has no `(3,2)` analogue at length one.

Finally, `Z32.not_cert_and_horse` proves the ledger's two colors **disjoint**:
no set carries both a functional block certificate and a horseshoe. The searches
confirm it from the other side — neither certified window admits a horseshoe at
any length tested (`sh reproduce.sh`, section N2(a)).

---

## The three G-0 experiments (`xg0.py`, `XG0Certs.lean`)

Gate G-0 of `plans/plan-z32-transform.html` opened three runs; `plans/note-z32transform-X.html`
is the write-up, `xg0.py` regenerates the numbers into `data/xg0_{kp,d19,twocell}.txt`, and
`XG0Certs.lean` is what the kernel checks (std3, `decide`, no cited axiom).

### X-KP — Mahler is out of reach of this family, provably

[KP18] Cor. 18 reduces Mahler's problem to the emptiness of `U = [0,1/6) ∪ [1/3,2/3)`, total
length only `1/2`. Its hold set is **exactly** `H = [0,1/15) ∪ [1/3,2/5) ∪ [5/9,3/5)`, measure
`8/45`, and `prune(H,H) = H` — a finite rational identity, so no depth ever empties it. The
transition graph has characteristic polynomial `x(x²−x−1)`: the **golden-mean shift**. Periodic
points of period dividing `n` are the **Lucas numbers** `1,3,4,7,11,18,29,47,…`, agreed on
independently by `tr Aⁿ` and by `prodcert.py cycles`.

| L | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|
| horseshoe words N (`F_L`) | 2 | 3 | 5 | 8 | 13 | **21** |
| log N / L | .2310 | .2747 | .3219 | .3466 | .3664 | **.3806** |

`Z32.log_twentyone_div_eight_le_phiModel_kp` certifies `φ_model ≥ (log 21)/8`; the truth is
`log φ = 0.48121…`. Infinitely many periodic orbits ⇒ **M7 Theorem B forbids every block
certificate, archimedean or product, at every level**. The engine agrees: refused to depth 60 in
the default and the rank-stratified mode alike.

### X-D19 — [Dub19] Thm 1.2 missed by one unit of `1/1539`

The window `[8/57, 805/1539)`, length `31/81 = 0.38272`, is refused at every depth to 61 in both
modes: components grow as exactly `k+1`, the measure → 0 geometrically, and there is **exactly
one** periodic orbit out to period 20 — the 3-cycle `4/19 → 6/19 → 9/19`, the same one
`Z32.ZSet_three_two_sixth_3_8` is built around. The obstruction is the left endpoint alone:
`(3·8/57)/2 = 4/19`, so `8/57` is a preimage of the cycle and drags an infinite backward orbit
(left endpoints `a/(19·3^j)` accumulating at `4/19`) that no finite rank stratification absorbs.

| window | length | verdict |
|---|---|---|
| `[216/1539, 805/1539)` = [Dub19] Thm 1.2 | .382716 | refused, depth 61, both modes |
| `[217/1539, 805/1539)` | .382066 | **CYCLE**, depth 11, 3 blocks — `Z32.ZSet_three_two_d19_shift` |
| `[218/1539, 805/1539)` | .381417 | CYCLE, depth 8, 3 blocks |
| `[216/1539, 804…780/1539)` | .382066….366472 | refused, 41 components, unchanged |

Twenty-five grid units off the right endpoint change nothing; one off the left endpoint decides it.

### X-238 — the `1/5` ceiling was the search mode, not the method

`Z32.two_cell_fifth_empty` (`‖ξ(3/2)ⁿ‖ < 1/5` impossible) was reported at G-0 as the engine's
ceiling, with the default search failing already at `c = 0.21`. That is a property of the **hull
merge**. Run `gencert.py --ranked` — the same relaxation `Z32.dubickas_2008_cor_1_2` needs:

| c | .21 | .23 | .235 | **.238** | .2381 … .2381175 | ≥ .2381177 |
|---|---|---|---|---|---|---|
| funnel depth | 1 | 1 | 3 | **7** | 15 | — |
| blocks / strata | 4/2 | 4/2 | 14/6 | **84/18** | 814 (50 strata at .2381) | — |

`Z32.two_cell_238_empty` and `Z32.not_forall_abs_sub_round_lt_238` are the `c = 0.238` entry,
kernel-checked; they **supersede `Z32.two_cell_fifth_empty`**. The `c = 0.2381` certificate
(814 blocks) is past the `decide` wall — killed after 1848 s of kernel time at `maxHeartbeats 0`,
the same wall as the 0.7417 union. The measured ceiling lies in
`(0.2381175, 0.2381177]`, against the printed `0.238117…` of [Dub06JNT] (Bugeaud, Tract 193,
Thm 3.14) — the two brackets overlap, so print is not beaten, but the gap G-0 priced at `0.038`
is `2·10⁻⁶`.

The ceiling is a property of the model, not of the code: the hold set of `‖·‖ < c` acquires its
periodic orbits one at a time, at exact rationals `a/(3^P − 2^P)`, in a period-doubling cascade —

| period | 1 | 2 | 4 | 8 | 16 | 12 (two orbits) | 10 (two) | 6 (two) |
|---|---|---|---|---|---|---|---|---|
| enters at c | 0 | 1/5 | 3/13 | 23/97 | 10233015/42981185 | 25115/105469 | 13839/58025 | 159/665 |
| | 0 | .2 | .230769 | .237113 | .238081 | .238127 | .238501 | .239098 |

— and the funnel a certificate needs grows with the orbit count it must carry (depth 1 with two
orbits, 7 with four, 15 with five). Above `c = 1/4` the two-cell set is exactly forward-invariant
(`S_k = U` for all `k`) all the way to `1/3`, where [Dub10] proves it nonempty.

---

## G-1 and M1 — the depth-one schema in closed form (`g1schema.py`, `SymbolicCert.lean`)

Gate G-1 of `plans/plan-z32-transform.html` asked whether the thirty grid certificates of the
`p > q²` table anti-unify. They do — into **one** schema in `(p, q, s)`, and it turned out to need
no certificate at all. `plans/note-z32transform-G1.html` is the write-up, `g1schema.py`
regenerates `data/transform/g1_schema.txt`, and `SymbolicCert.lean` is the theorem (std3, no cited axiom,
and **nothing for the kernel to evaluate** — the only `decide` calls in it check `Nat.Coprime p q`
at numeral bases).

**The schema.** For coprime `p > q > 1` and *any real* `s`, put `θ = (p−q)s`, `k = ⌊θ⌋`,
`ε = {θ}`. In the window coordinate `uₙ = {ξ(p/q)ⁿ − s} ∈ [0, 1/p)` the recursion is
`q·u_{n+1} = p·uₙ + θ − sₙ`, so each carry lies in `(θ − q/p, θ + 1)`: `sₙ ∈ {k, k+1}`. Each
letter is then confined to its own block,

| letter | block | image under its own branch |
|---|---|---|
| `k` | `B_low = [0, (q − pε)/p²)` | `[ε/q, 1/p)` — flush against the window's right end |
| `k+1` | `B_high = [(1 − ε)/p, 1/p)` | `[0, ε/q)` — flush against its left end |

The hole between the blocks has width `(p−q)/p²`, independent of `ε`, and the two images meet at
the single point `ε/q = f_k(s) = f_{k+1}(s + 1/p)`. So everything turns on where that one point
sits: **the depth-one certificate closes iff `ε/q` lands in the hole**, i.e.

    ε = 0   or   q ≤ pε   or   q²/(p(p+q)) ≤ ε ≤ q/(p+q).

In the first two cases a block is empty and the carry word is constant; in the third each letter
forbids its own repetition and the word alternates. Either way it is eventually periodic, which
`Z32.not_isEventuallyPeriodic_carry` ([DN05] Lem. 2) forbids for `ξ ≠ 0`. That is the whole proof
— six lines, no interval arithmetic.

**What the engines say.** `g1schema.py` compares the closed form against two independent
implementations — one written from `BlockCert.lean`'s `pieceOk`/`hits`/`funcOk`, one being
`gencert.py` itself — on the thirty table entries (block count = surviving-carry count, and the
three two-block rows are exactly the three with `ε` in the band), on 12 038 (base, position) pairs
with `p ≤ 24` in **both** regimes, at the exact critical `ε` values, on the closed convention, and
on wrapped windows. Zero mismatches everywhere. Out of sample it predicts which of the eight
`(4,3)` windows are depth 1 — and the two it refuses hardest are the two this README records at
funnel depth **26**.

**What it costs the conjecture list.** C-3 of the plan ("in `p > q²` every rational length-`1/p`
window certifies at depth `≤ 2`") is **false**: at `(5,2)`, `s = 1/8` needs depth 3 and
`s = 3/25` needs depth **6**. The thirty table entries all have positions of denominator dividing
6, which mostly misses the two failure bands.

**Reach.** The uncertified positions are two `ε`-bands of equal length, total measure
`2q²/(p(p+q))` — `8/35` at `5/2`, `8/195` at `13/2`, `9/14` at `4/3`. So depth one alone settles
`1 − 2q²/(p(p+q))` of all real positions at every base, for every `ξ ≠ 0` and with no assumption
on its arithmetic nature. Under the **closed** convention the band is the same but open, and
`ε = 0` is lost — because there the left endpoint `s` is a fixed point of its own branch, which is
conjecture C-5 of the plan, proved on this class.

### What `SymbolicCert.lean` states

| name | statement |
|---|---|
| `Z32.SchemaCertified` | the hypothesis on `ε`, denominators cleared |
| `Z32.not_confined_of_certified` | a certified window traps no orbit |
| `Z32.exists_fract_ge_of_certified` | the [Dub09AA]-style "infinitely often" form |
| `Z32.ZSet_eq_empty_of_certified` | `Z_{p/q}(s, s+1/p) = ∅`, every real certified `s`, every base |
| `Z32.ZSet_zero_eq_empty` | target T1: the plan's `𝒮₀`, at every coprime base |
| `Z32.ZSet_half_eq_empty` | the gate's test position `s = 1/2`, for `p − q` even or `p ≥ 2q` |
| `Z32.ZSet_{five_two, seven_two, nine_two, ten_three, eleven_three}` | target T2: the thirty entries of the `p > q²` table, now corollaries |
| `Z32.ZSet_five_two_{upper, band, interval}` | target T3 grade 1: emptiness for a *continuum* of real positions at a base with `p > q²` |

Every one is std3 (`propext`, `Classical.choice`, `Quot.sound`), sorry-free, and uses no
certificate structure; the only `decide` calls check `Nat.Coprime p q` at numeral bases, never
certificate data. The thirty Table 3 entries in `BlockCert.lean`/the atlas are untouched: they
remain the independent kernel-checked route to the same conclusions.

## X-P re-aimed — the two residual bands (`xp.py`)

G-1 left exactly two open bands per base, in the coordinate `ε = frac((p−q)s)`:

    LOW = (0, q²/(p(p+q)))        HIGH = (q/(p+q), q/p)

of total measure `2q²/(p(p+q))`. Experiment X-P of `plans/plan-z32-transform.html`
was re-aimed at those (rather than at all of `[0, 1−t]`) and run on 2026-09-02;
`plans/note-z32transform-XP.html` is the memo, `data/transform/xp_bands.txt` the output.

The right coordinate is the fibre coordinate `u = y − s`, in which the window is the
**constant** interval `U = [0, 1/p)` and the two admissible branches are

    f_j(u) = (p·u + ε − j)/q,   j ∈ {0,1}

(`Z32.branch_base` / `Z32.branch_succ`). So the whole problem is one-parameter in `ε`,
every funnel endpoint is an affine form `a + b·ε`, and the engine carries entire
`ε`-intervals, subdividing at the first crossing of two forms. Nothing is sampled.

| finding | evidence |
|---|---|
| **the involution** `ε ↦ q/p − ε` exchanges LOW and HIGH | `u ↦ 1/p − u` conjugates `f_j` at `ε` to `f_{1−j}` at `q/p − ε`; 1880 `ε`-pairs at ten bases, 0 asymmetries; HIGH's cell word is LOW's reversed, exactly |
| **the decomposition is universal** — the same at every base | at cap 12 the word of (verdict, depth) is *identical* at `(5,2) (7,2) (9,2) (10,3) (11,3) (4,3) (13,2) (17,4) (3,2) (26,5)`, both regimes; cell counts agree at every cap: 9, 17, 27, 41, 57, 71, 95, 119, 139, 171 at caps 4…22 |
| **certified fraction → 1 like `(q/p)^K`** | at `(5,2)`: 0.999874 at cap 12, `1 − 2.2e−8` at cap 22. So the exceptional set of positions is **null** ⇒ T3 grade 2 upgrades from co-finite measure to **full measure** |
| the funnel is **linear**, not Fibonacci | max component count in a residual cell is exactly `K+1` at cap `K`, at every base ⇒ **zero entropy** everywhere in the band |
| `--ranked` **buys nothing here** | on twelve residual cells the rank-stratified criterion returns exactly the same depths, always one stratum. Recorded so it is not retried |
| the residual **nests, and no parent dies** | caps 6→8→10→12→14→16: every sliver lies in a sliver of the previous cap, none escapes, none dies ⇒ the exceptional set is a nonempty decreasing intersection, and null. It is **not** confined to the band endpoints: at `(5,2)` cap 16 there are slivers of width `~1e−12` at `ε ≈ 0.0157634, 0.0061694, 0.0410252, 0.1025643, 0.1125123` — 13.79 %, 5.40 %, 35.90 %, 89.74 % and 98.45 % across the band. Sliver count grows only *polynomially* (5, 9, 14, 21, 29, 36, 48, 60, 70, 86 at caps 4…22, fitting `0.45·K^1.68`, two-level ratio falling 1.80 → 1.23), which forbids a perfect subtree — so countable and dimension 0 *if that law persists*; the box-counting ratio is ≈0.21 at cap 20 and falls only like `log K / K` |

Honest caveats. The decay constant is `q/p` per level, so it is fast when `p/q` is large
and slow when `p/q → 1`: at the `(4,3)` control, cap 16 still leaves **1.1 %** of the band
uncertified, and the grid scan there reaches depth 22 where `(5,2)` reaches 10. "Full
measure" is well-supported evidence in the `p > q²` regime and merely consistent at `(4,3)`.
Nothing in this section is kernel-checked — X-P is an experiment, and two distinct gaps stand
between it and a theorem. *Per cell*: the verdict is uniform over an **interval** of `ε`, and
`decide` checks rational instances, not intervals; one cell becomes one theorem only via the
plan's `ParamCert` endpoint evaluation or via a schema. *Across cells*: "full measure" quantifies
over infinitely many cells, so it needs a closed-form depth-`K` schema (the natural successor to
`SymbolicCert.lean`, and now the target of milestone M3). The measured `1 − 2.2e−8` is evidence
for that theorem, not an instance of it.

Three implementations are compared before anything is believed (house rule R-5): the
parametric engine on affine forms, `scalar_eps` written from the branch maps in `u`, and
`scalar_s` = the corpus's own `gencert.py` in the original `y`-coordinate with the full
carry alphabet. 1434 grid points and 2724 cell/breakpoint checks, 0 disagreements.

## The depth-K schema — M3 (`DepthKSchema.lean`, `m3schema.py`)

X-P's universality is the signature of a closed form, and here it is. Rescale the
window coordinate to `v = p·u ∈ [0,1)`. The two carries become two branches, and
between them a hole from which no step is possible:

    low   p(v+ε) < q,    then  q·v' = p(v+ε)
    high  1 ≤ v+ε,       then  q·v' = p(v+ε−1)
    hole  q/p − ε ≤ v < 1 − ε        (width (p−q)/p, independent of ε)

Run that map **from the window's own left endpoint**: `w₀ = 0`, `w_{i+1}` = the branch
image of `w_i`. `Z32.Escape p q ε K w` says the orbit is defined for `K` steps and
`w_K` lands in the hole (right end closed, which folds in the case where the orbit
returns to `0`). That single condition is the schema, and it contains M1: `K = 0` is
`q ≤ pε`, `K = 1` is the G-1 band `q² ≤ p(p+q)ε ≤ q(p+q)`, and `K ≥ 2` is what the two
residual bands are made of (`Z32.certifiedK_of_certified`). Only `ε = 0` stays outside.

**Why it certifies.** The `K+1` marked points cut `[0,1)` into `K+1` arcs; let
`ν(x) = #{i ≤ K : w_i ≤ x}` be the arc index (`Z32.blockRank`). The branch map is
increasing for the order that cuts at the hole's right end, and its two images tile
`[0,1)`, so with `N_L`, `N_R` the marked points on each branch (`N_L + N_R = K`),

    ν(v') = ν(v) + N_R + 1   on the low branch,     ν(v') + N_L = ν(v)   on the high branch

— the rotation by `N_R+1` on `ℤ/(K+1)` — while `ν` also decides the branch
(`ν ≤ N_L ⟺ low`). So along a confined orbit the rank sequence is deterministic with
`K+1` values, it repeats, the carry word is eventually periodic, and
`Z32.not_isEventuallyPeriodic_carry` closes it. This is also why X-P found the funnel
component count to be exactly `K+1`: the components *are* those arcs.

`Z32/DepthKSchema.lean` is that argument: 766 lines, std3, sorry-free, 0 cited axioms and
**no certificate data for the kernel** — the proof is uniform in `p`, `q`, `s` and `K`, and the
file's only two `decide`s check `Nat.Coprime 5 2` in the numeral instances. Landed:
`ZSet_eq_empty_of_certifiedK`; the closed-form family `LowBand`/`escape_lowOrbit`/
`ZSet_eq_empty_of_lowBand`, namely

    q^{K+1}(p−q) ≤ p·ε·(p^{K+1} − q^{K+1})   and   ε·(p^{K+1} − q^{K+1}) ≤ q^K(p−q),

which at `K = 1` *is* the G-1 band; and the instances `ZSet_five_two_depth_two`
(`{3s} ∈ [8/195, 4/39]`, 54 % of the residual band on its own), `_depth_three`
(`[16/1015, 8/203]`, whose endpoints are two of the interior accumulation points X-P
located) and `_depth_two_interval` (`s ∈ [8/585, 4/117]`, no `Int.fract`). The one
family covers 88 % of the residual LOW band at `(5,2)` and 93–98 % at the other
`p > q²` bases; 60 % at the `(4,3)` control.

**Provenance — this is a formalization, not a new theorem.** The criterion is
[FLP95] Theorem 3.4 — `f^N(0) ≥ 1/β` ⇒ the survivor set is finite, with exactly `N`
elements *cyclically permuted* by the map: the rank rotation, in 1995 — plus [Bug04]
Lemma 1–2 (the returning case, and that together they are an *iff*); the closed-form
family is [Bug04] Lemma 3's interval `J¹_{K+1}(q/p)`, the general branch word being
`J_b^a(q/p)` with `b = K+1` blocks and rotation number `a/b`, `a = N_R+1`; and the
statement that `Z_{p/q}(s, s+1/p) = ∅` for a **full-measure** set of `s` is
[Bug04] Theorem 1, Acta Arith. 114 (2004) 301–311 (`papers/Bugeaud2004.pdf`). Nothing
here may be called new: what the corpus adds is the machine-checked form and the
identification of `Escape(K)` with the *depth* of a block certificate. The remaining
`s` — where the marked orbit never escapes — are the Sturmian numbers of irrational
slope; their emptiness is open in the source, they are null and uncountable
([Bug04] Thm 3), of Hausdorff dimension 0 ([Gai25]) and transcendental ([BKLN21]).

`m3schema.py` is the R-5 bridge (3 s, output `data/transform/depthk_schema.txt`): the
escape depth against the corpus's own funnel engine (1600 `ε` at ten bases, 0
mismatches); `Z32.Escape` and `Z32.LowBand` transcribed field by field from the Lean
file (800/800 and 450/450); the rank rotation and the branch dichotomy on a grid
(241 524 checks, 0 violations); and — independently of all of the above — [Bug04]
Lemma 3's `J_b^a(q/p)` computed from the Sturmian sequence `ε_{−k}(a/b)`, reproducing
the same partition with `b = K+1` and `a = N_R+1` (840 points, 0 mismatches).


## The quantitative escape bound — M2 (`EscapeBound.lean`, `m2escape.py`)

Every emptiness theorem in `Z32/` is a proof by contradiction from
`Z32.not_isEventuallyPeriodic_carry`, so none of them says *when* an orbit leaves the
window. `EscapeBound.lean` extracts the step count that is latent in that argument.
Write `β = p/q`. The budget is

    escapeSteps p q A X L  =  A + 1 + ⌈log_q (X·β^A + 1)⌉ + ⌈log_β (q/L)⌉

with `A` the certificate's **combinatorial budget**: `|H|` (the number of blocks) on top of
`K = |levels|` funnel steps for a block certificate, `K+2` for a depth-`K` schema. The two
theorems say: for `0 < L ≤ ξ ≤ X` there is an `n` inside the budget with
`{ξ(p/q)ⁿ}` outside the certified set — `Z32.BlockCert.Cert.exists_escape_le` (the plan's
`Cert.escape_bound`) and `Z32.exists_escape_le_of_certifiedK`.

**Where the rate comes from.** The funnel is proved on a finite range
(`Cert.memL_blocks_of_le`, new — each level costs one step *at the top*, because a point is
pushed down using the membership of its successor; the old `Cert.exists_block_path` is now
derived from it). Pigeonhole then gives a block repeat among the indices `0 … |H|`, so the
carry word is `P`-periodic from `t` with `t + P ≤ |H|`. From `s_{n+P} = s_n` the ladder
`q·M_{n+1} = p·M_n` for `M_n = x_{n+P} − x_n` gives `q^m·M_{t+m} = p^m·M_t`
(`q_pow_mul_orbDiff`), hence `q^m ∣ M_t` (`q_pow_dvd_orbDiff`) with `m = N − t − P`. Then
the **dichotomy** `Z32.escape_endgame`: either `M_t ≠ 0`, and `q^{N−t−P} ≤ |ξ|β^{t+P} + 1`,
or `M_t = 0`, and `|ξ|β^{N−P}(β−1) < 1`. The first is an upper bound on `N` in terms of `X`,
the second in terms of `1/L` — which is why there are two logarithms.

**Two logarithms, and why the second is not removable.** The plan asked for a bound in an
upper bound for `ξ` alone. That is false, and the counterexample is one of the entries in
this file: the two-cell set `[0,1/5) ∪ [4/5,1)` at `3/2` holds every `ξ ∈ (0,1/5)` for
exactly `⌈log_{3/2}(1/(5ξ))⌉` steps, with `⌊ξ⌋ = 0` throughout (measured: 4, 8, 12, …, 44 at
`ξ = 5^{-2} … 5^{-12}`). At `L = 1` the second term is a constant — 2 at `3/2`, 4 at `4/3`,
1 at `5/2` — and the shape is the promised `A(c) + log_q X`.

**Scope: the ranked certificate is excluded, and no bound exists for it.** The theorems
require `c.strata = []`, a genuinely functional block graph. `funcOk` only forbids *two
equal-rank* edges out of a block, so a block may carry an equal-rank edge and a lower-rank
one; the model orbit can then follow the equal-rank cycle for arbitrarily long and drop only
afterwards, and the periodicity ends exactly where it drops. Counting the drops does not
rescue it: with `R` drops the first branch of the dichotomy would need `log q > R·log β`,
false at `R = 4`, `p/q = 3/2` — i.e. at `certDub08`, the only ranked entry. Nine of the ten
atlas entries are covered; `dubickas_2008_cor_1_2` keeps its qualitative theorem and gets no
escape bound.

The per-entry corollaries, with `A` the additive constant and the bound at `X = 10⁶`,
`ξ ≥ 1` (last column: the largest escape time actually observed on a 448-point exact grid):

    escape_sixth_3_8       [1/6,13/24)      3/2  K=8  |H|=3   A=14   36    8
    escape_frontier        [961,2427]/3600  3/2  K=13 |H|=2   A=18   40    6
    escape_union_712       union 7/12       3/2  K=7  |H|=1   A=11   32    9
    escape_union_23        union 2/3        3/2  K=9  |H|=12  A=24   51   11
    escape_union_2536      union 25/36      3/2  K=11 |H|=17  A=31   61   10
    escape_two_cell_fifth  [0,1/5)∪[4/5,1)  3/2  K=1  |H|=2   A= 6   28    7
    escape_four_three      [1/3,5/8)        4/3  K=5  |H|=2   A=12   26    6
    escape_five_two_fifth  [1/5,2/5)        5/2  K=1  |H|=1   A= 4   26    1
    escape_union_7083      union 17/24      3/2  K=17 |H|=100 A=120 199   11   (UnionRecord.lean)

`escape_sixth_3_8_million` states one of them with no parameters at all: every `ξ ∈ [1,10⁶]`
leaves `[1/6, 13/24)` within 36 steps. The bound is loose by 20–51 steps and the slack grows
with `X`; the `log_q X` term itself is not loose (an orbit really can be confined for
`~log_q|ξ|` steps — that is what `q^m ∣ M_t` says), but reaching it needs `ξ` exponentially
close to the survivor set, and a targeted search along the surviving 3-cycle
`4/19 → 6/19 → 9/19` (546 orbits `b·2^j + y₀`) reached escape time 9.

`EscapeBound.lean` is 889 lines, std3, sorry-free, 0 cited axioms; `escape_union_7083`, the ninth
and last entry a bound reaches, lives in `UnionRecord.lean` beside the certificate whose `decide`
costs 90 s. `m2escape.py` is the R-5
bridge (2 s, output `data/transform/escape_bound.txt`): the certificate shapes re-parsed
from `BlockCert.lean` and `UnionRecord.lean` rather than read off the Lean statements (9/9); 11826 exactly simulated
orbits against the certified bound at `X ∈ {10, 10³, 10⁶}`, 0 violations; every maximal
periodic run of a real carry word checked against the ladder, the divisibility and the
dichotomy (8728 runs, 0 failures); the `log(1/ξ)` counterexample against its closed form (0
mismatches); and the schema front end at eight certified `(p,q,s)` including two from M3
(2400 points, 0 violations).

## Completeness and the obstruction — M4 (`CertComplete.lean`, `m4complete.py`)

`BlockCert.lean` proves the scheme **sound**. `CertComplete.lean` proves the converse half:
which sets the scheme can decide, and what stops it.

**The engine is arithmetic, not dynamical.** The model dynamics is a *relation* — from
`y ∈ [0,1)` there are `q` admissible successors `(py−s)/q`, one for each integer `s` in
`(py−q, py]`. On the part of the dynamics that matters the branching disappears:

> **`Z32.step_unique`.** If `u, v, v' ∈ [0,1)` are rationals whose denominators are coprime
> to `q`, and `qv = pu − s`, `qv' = pu − s'` for integers `s, s'`, then `v = v'`.

Over a common denominator `D` coprime to `q` the two relations read `qb = pa − sD` and
`qc = pa − s'D`, so `D ∣ q(b − c)`, hence `D ∣ b − c`, and `b, c ∈ [0, D)`. Equivalently:
among `q` consecutive admissible carries exactly one lies in the residue class
`s ≡ pad⁻¹ (mod q)`, and that is the only branch keeping the denominator coprime to `q`.
A point the orbit *returns to* is periodic, hence `A/(p^P − q^P)` whose denominator is
coprime to `q` — so **the recurrent part of the dynamics is a function**.

**C-2 at every base.** `Z32.cyclePoint_eq_base`: a `P`-periodic point of `q·y_{i+1} = p·yᵢ − sᵢ`
is `A/(p^P − q^P)`, at every coprime base (the corpus had `Z32.cycle_point_eq` at `3/2` only).
`Z32.hasDenom_of_return` proves it for a return *segment*, which is the form completeness
consumes, and `Z32.cycleDenom_coprime` supplies `gcd(p^P − q^P, q) = 1`.

**T5(i), completeness.** `Z32.holdSet_finite_imp`: if the **hold set** of `U` — the points of
`U` carrying an infinite orbit of the carry relation inside `U` — is finite, then no `ξ ≠ 0`
keeps its orbit in `U`. The chain: a confined orbit has finite range ⟹ some value recurs
infinitely often ⟹ from the first visit every point lies on a loop, so its denominator is
`p^P − q^P` ⟹ `step_unique` makes the tail deterministic ⟹ the orbit and its carry word are
eventually periodic ⟹ [DN05]. The plan asked for the hold set to be "finitely many periodic
orbits plus transients, arranged so that the itinerary is forced"; **the arrangement clause is
free**. What is *not* done is building the `Cert` data from a finite hold set: the class is
decided, the format is not yet proved complete on it.

**T5(iii): the plan's conjecture C-5 is false.** It read "a closed-convention certificate
exists iff no survivor cycle passes through an endpoint of `U`", with the closed
`[0,1/5] ∪ [4/5,1]` and the closed [Dub08] union as its witnesses. Both have endpoint cycles
*and* certificates. What is true:

> **`Cert.eq_of_memI_block`.** For a certificate with `strata = []`, two orbits confined to `U`
> that ever occupy the same block are equal. Hence `U` has at most `|H|` held points, and
> (`Cert.ok_eq_false_of_infinite_hold`) a set with infinitely many held points admits **no
> unranked certificate at any depth**.

With no strata every block has at most one outgoing `(carry, block)` pair, so the carry word of
a confined orbit is determined by its first block; two orbits with the same carry word separate
like `(p/q)ⁿ`, which `[0,1)` cannot hold. And an endpoint cycle is what makes the hold set
infinite: closing `1/5` in the two-cell arc admits the whole backward chain
`1/5, 2/15, 4/45, 8/135, … = (1/5)(2/3)^k → 0`, every term of which runs down into the 2-cycle
`1/5 ↔ 4/5`. In the half-open convention the chain dies at its first step.
`Cert.ok_eq_false_of_covers_two_cell` states it in general: *any* unranked certificate covering
the closed arc is invalid, whatever its denominator and depth — which replaces this file's
recorded search result ("`gencert.py --closed` finds nothing to depth 60") by a theorem.

**Five closed-convention entries.** Ranks are exactly the device that survives an infinite hold
set, so each half-open entry should have a closed companion at the same funnel depth. Five do,
all `decide`-checked:

    certTwoCellFifthClosed  [0,1/5] ∪ [4/5,1]      3/2  D=15          K=1   4 blocks   2 strata
    certWindow38Closed      [1/6,13/24]            3/2  D=157464      K=8   9 blocks   7 strata
    certFrontierClosed      [961/3600,2427/3600]   3/2  D=5739562800  K=13 14 blocks  13 strata
    certFourThreeClosed     [1/3,5/8]              4/3  D=24576       K=5  12 blocks   6 strata
    certFiveTwoClosed       [1/5,2/5]              5/2  D=5           K=0   1 block    0 strata

with theorems `two_cell_fifth_closed`, `sixth_3_8_closed`, `frontier_closed`,
`four_three_closed`, `five_two_fifth_closed`. Closed emptiness is strictly stronger than its
half-open shadow, so four of them are new statements. **The two-cell one is not**:
`Z32.two_cell_238_empty` (`XG0Certs.lean`, experiment X-238) already proves
`‖ξ(3/2)ⁿ‖ < 0.238` impossible and `[0,1/5] ∪ [4/5,1] ⊆ [0,119/500) ∪ [381/500,1)`, so
`two_cell_fifth_closed` is a corollary of it. It is kept for the *certificate*: this is the set
`BlockCert.lean` recorded as refused by `gencert.py --closed` to depth 60, and it certifies at
funnel depth 1 — exactly as `ok_eq_false_of_covers_two_cell` predicts, the refusal being of the
unranked search only. The three union entries have no closed companion to depth 16.

`CertComplete.lean` is 861 lines, std3, sorry-free, 0 cited axioms.  `m4complete.py` is the R-5
bridge (80 s, output `data/transform/cert_complete.txt`):
`funnelOk` and `funcOk` re-implemented from the definitions and re-run on the five new
certificates, with unranked controls that must fail (5 checked, 0 failures, 0 controls wrongly
passing); 6868 points over 15 bases for `step_unique`, every one with **exactly one**
coprime-denominator successor; 26244 cycle points at eight bases for C-2, 0 exceptions; the
two-cell chain re-evaluated from the Lean definitions in both conventions; the ten-entry
closed/half-open depth survey; and `|hold set| ≤ |blocks|` on every unranked entry — tight on
five of the eight (3 = 3 at `[1/6,13/24)`, 2 = 2 at the frontier, 1 = 1 at the `7/12` union,
2 = 2 at the two-cell arc and at `(4,3)`, 1 = 1 at `(5,2)`).

## Cycles and the transversal — X-U (`CycleTransversal.lean`, `xu.py`)

`CertComplete.lean` proved one half of the plan's conjecture C-2: a `P`-periodic point of the
carry relation has denominator dividing `p^P − q^P`.  Experiment X-U needed to *enumerate* those
cycles, and the first thing it produced was the recurrent map's name.

**The recurrent map, in closed form.** On the points of denominator `D` with `gcd(D,q) = 1` the
(unique, by `step_unique`) successor is

    a/D  ↦  (p·a·q⁻¹ mod D) / D,

multiplication by the element `p/q` of `ZMod D` (`Z32.cycOrbit`, `Z32.cycOrbit_rec`).  Two things
follow that are invisible from the relation itself, and both are theorems:

* **no transients in the recurrent set** — multiplication by a unit is a bijection, so every point
  with `gcd(D, p·q) = 1` is *purely* periodic (`Z32.cycOrbit_periodic`);
* **C-2 has a converse** — every point of denominator dividing `p^P − q^P` is periodic with
  period dividing `P` (`Z32.cycOrbit_period_dvd`), so with `cyclePoint_eq_base` the `P`-periodic
  points are *exactly* the `A/(p^P − q^P)`; and every coprime denominator at all is periodic
  (`Z32.exists_periodic_orbit`).

R-5: checked against the brute-force successor rule on 10 200 points over ten bases and all
denominators `D ≤ 59` coprime to `q` — 0 non-unique successors, 0 disagreements; and the converse
of C-2 exhaustively both ways at four bases for all `P ≤ 7`.

**What that costs a certificate.** Periodic orbits are dense, and every one that `U` contains
*entirely* is a hold point.  An unranked certificate needs the hold set finite
(`Cert.eq_of_memI_block`), so:

> `Z32.BlockCert.Cert.ok_eq_false_of_infinite_cycles` — **the removed set must be a transversal.**
> If infinitely many distinct points of denominator coprime to `p·q` keep their whole orbit inside
> `U`, then `c.ok = false` at every depth.

This is the plan's conjecture **C-8** corrected and proved.  C-8 read the record unions as
*removing* neighbourhoods of the period-`≤P` cycle spine; the census says the low-period spine is
what they **keep**.  Of 531 292 orbits of period ≤ 14, the `25/36` and `17/24` records keep exactly
one (the fixed point `0`) and the `43/60` and `89/120` records keep two (`0` and
`2/19 → 3/19 → 14/19`, `Z32.carry_cycle_nineteen`).  Read off the exact funnel instead of the
census, the same picture with the backward tree attached:

    record    K   blocks   alive components = surviving cycles + tree
    25/36    11       17    3    {0} + one component shrinking to 1 ∉ [0,1) + 1 transient
    17/24    17      100    4    {0} + 3 transients
    43/60    20      433   35    {0} + the 3-cycle + 31 transients
    89/120   29     2526   60    {0} + the 3-cycle + 56 transients

**C-8's recipe, tried.** 48 hand-built `U_P` (complement of the cells meeting the period-`≤P`
spine, optionally with `m` levels of backward tree, `P ∈ {2..5}`, `m ∈ {0,1,2}`,
`N ∈ {36,60,240,720}`; in 20 of them the removal exhausts the grid, so 28 are real trials).
The best measure any of them certifies is **1/4**, on grids where the
greedy climb reaches `43/60` and `3/4`.  And the failures are structural, not depth artifacts: for
every larger `U_P` but two, the exact funnel reaches a **fixed point** `T_{d+1} = T_d`, so `T_d` —
a union of 5 to 396 nondegenerate intervals — is contained in the hold set, and
`ok_eq_false_of_infinite_hold` refuses the certificate at *every* depth.  Two were also put through
`gencert.py` itself: the `1/4` set at `(P,m,N) = (3,2,240)` certifies there at depth 4 as well, and
the `29/40` set at `(3,1,240)` is refused to depth 60 in both the default and the `--ranked` mode,
its component count stuck at 63 from level 1 — the funnel fixed point seen from the engine's side.

**The price of largeness.** Two exact facts: `Σ_s |g_s(S) ∩ [0,1)| = 2|S|` where `g_s(v) = (qv+s)/p`,
and every `y` has exactly two successors, so `|f⁻¹(S)| ≥ |S|`.  Hence `|T_k| ≥ 1 − (k+1)δ` with
`δ = 1 − |U|`; and past the certifying depth the block map is a function, so `|T_{K+j}| ≤ (2/3)ʲ·B`.
Comparing gives, for every certificate,

    K + log_{3/2}(B)  ≳  1/(1 − |U|).

At today's measures this is slack by a factor of ten, but it prices C-8's target `1 − C(q/p)^{cP}`
out of existence: funnel depth exponential in `P`, certificate data (denominator `G·p^K`) doubly
exponential.  **Since 2026-09-03 the whole derivation is machine-checked** — see the next section.

`CycleTransversal.lean` is 258 lines, std3, sorry-free, 0 cited axioms, with no data for the
kernel.  `xu.py` is the R-5 bridge (about 8 minutes, output `data/transform/union_autopsy.txt`).
Full write-up: `plans/note-z32transform-XU.html`.


## The depth–size bound — M5(a) (`DepthSize.lean`)

What a certificate *costs*, as a theorem.  Write `δ = |[0,1) ∖ U|` and let `T₀ = U`,
`T_{k+1} = U ∩ f⁻¹(T_k)` be the exact funnel (`Z32.funnel`), with

    f⁻¹(S) = { y ∈ [0,1) : ∃ v ∈ S, ∃ s ∈ ℤ, q·v = p·y − s }        (`Z32.pre`)

the branch preimage of the carry relation — the set the certificate's `levels` over-approximate.

| half | statement | name |
|---|---|---|
| expansion | `\|f⁻¹(S)\| ≥ \|S\|`, hence `\|T_k\| ≥ 1 − (k+1)δ` | `volume_le_volume_pre`, `one_le_volume_funnel_add` |
| contraction | `\|T_{K+j}\| ≤ B·(q/p)ʲ` | `BlockCert.volume_funnel_le_of_cert` |
| headline | `1 ≤ 2δ·(K + 2 + log_{p/q}(2B))` | `depth_size`, `depth_size_logb`, `BlockCert.cert_depth_size` |

with `K = c.levels.length` the funnel depth and `B = c.blocks.length` the block count.  Read
backwards it says a valid unranked certificate **must leave a hole of positive measure**
(`BlockCert.volume_hole_pos`) and certifies a set of measure `< 1`
(`BlockCert.volume_certSet_lt_one`) — a measure-theoretic sharpening of `ok_eq_false_of_full`,
which only ruled out the whole window.  `BlockCert.hole_union_2536` is the bound at the `25/36`
record: `δ ≥ 1/44` from `K = 11`, `B = 17` (both kernel-computed from the certificate, and both
agreeing with `xu.py`'s certifier), against the true `11/36`.

Two representation choices removed every measurability obligation, and neither was foreseen in the
X-U write-up.  The preimage **factors** as

    f⁻¹ = slice_p ∘ fold_q,     fold_q S = { fract(q·v) : v ∈ S },
                                slice_n A = { y ∈ [0,1) : fract(n·y) ∈ A }

(`Z32.pre_eq_slice_fold`) — "multiply by `p` mod 1, then divide by `q` in every admissible way" —
and both maps are written as finite unions of **affine preimages**, never images, so
`Real.volume_preimage_mul_left` and translation invariance apply to *arbitrary* sets.  Unfolding
then preserves measure exactly (`volume_slice`, the `n` pieces are disjoint) and folding cannot
shrink (`subset_slice_fold`: `S ⊆ slice_q (fold_q S)`), which is the whole expansion half; the
exact identity `Σ_s |g_s(S) ∩ [0,1)| = 2|S|` of the X-U note never enters.  For the contraction
half, `Real.volume_le_diam` bounds each block's share of the funnel by its **diameter**, so no
interval list is ever measured and no disjointness is ever checked.

The dynamical input is M4's determinism in a form the corpus lacked: `Cert.eq_of_memI_block` shows
two orbits confined *forever* in the same block are equal; here confinement lasts `K + j` steps and
the conclusion is quantitative — same block ⟹ same carry word ⟹ `|y − y'| ≤ (q/p)ʲ`
(`BlockCert.abs_sub_le_of_memI_block`).  `Z32.exists_chain_of_mem_funnel` bridges the two shapes,
extending a funnel point's finite chain past its end by the canonical successor
`y ↦ fract(p·y)/q`.

Where the bound bites is a *family*, not a set: C-8's `δ_P ≤ C(q/p)^{cP}` forces
`K_P + log_{p/q} B_P ≳ C⁻¹(p/q)^{cP}` — depth exponential in `P`, certificate data doubly
exponential.  Against the records themselves it is slack by 13× (`25/36`) to 27× (the 240-cell
record).  `DepthSize.lean` is 815 lines, std3, sorry-free, 0 cited axioms, no kernel data, and is
the first measure theory in this root.  `depthsize_check.py` is the R-5 bridge: it recomputes all
three statements on the exact funnels of the `25/36` and `17/24` records (and reproduces the
kernel's `K = 11, B = 17` and `K = 17, B = 100` from the engine side) in about two seconds.
Full write-up: `plans/note-z32transform-M5.html`.


## The frontier, and its exact object — X-F (`RankedFrontier.lean`, `xf.py`)

Experiment X-F of `plans/plan-z32-transform.html` (milestone M6, write-up
`plans/note-z32transform-M6.html`) was asked to autopsy the 14 frontier windows above.  It
reproduced them — an independent exact-rational engine, 781 positions, **0 disagreements** with
`data/x2_frontier.txt` — and then found that the frontier they mark is not the certificate
family's.

**`L* = 0.40722` belonged to the hull-merge search.**  `atlas.c` and the default `gencert.py`
merge the surviving components into interval hulls and demand out-degree `≤ 1`.  The
**rank-stratified** criterion (`gencert.py --ranked`; raw components, rank = size of the
forward-reachable set — equivalently *no branching SCC*), sound by the same
`Cert.not_confined` and already used by `dubickas_2008_cor_1_2` and `two_cell_238_empty`,
certifies the same row at **213** of 236 positions instead of 14 — and at *exactly* the positions
`961 ≤ i ≤ 1173`, i.e. exactly the windows whose closure lies in `(4/15, 11/15)`.  (`4/15 ↦ 2/5`
and `11/15 ↦ 3/5`: the two preimages of the surviving 2-cycle nearest to it.  A window containing
one of them traps an infinite backward chain accumulating on the cycle, the alive-component count
is exactly `k+1` at depth `k`, and no finite interval partition separates them — the same
mechanism X-D19 found in [Dub19]'s own window.)

The certified region of the `(s,L)` plane is one **tongue** narrowing onto the axis `s = (1−L)/2`,
and that the axis is a symmetry axis is forced: `y ↦ 1 − y` conjugates the carry relation to itself
with the carry `s ↦ p − q − s`, so the whole atlas is mirror-symmetric and the 14 frontier windows
fall into 7 mirror pairs.  `Z32/RankedFrontier.lean` ships the prettiest point of the tongue:

| entry | \|U\| | Lean name | funnel |
|---|---|---|---|
| `[2/7, 5/7]` **closed** | **3/7 = .428571** | `Z32.ZSet_three_two_two_seven`, `Z32.two_seven_empty` | depth 15, 166 blocks, 32 rank strata |

so that **for every `ξ ≠ 0`, `‖ξ(3/2)ⁿ‖ < 2/7` for infinitely many `n`**
(`Z32.not_forall_two_seven_le_abs_sub_round`) — against the corpus's previous constant `1/3`, and
past the longest single window in print, [Dub19] Thm 1.2's `31/81 = 0.38271`.

### The exact ceiling is a Thue–Morse constant

On the centred line write the window as `[c, 1−c)`; an orbit is inside exactly when
`c ≤ minᵢ ‖yᵢ‖`.  Sorting every orbit of period `≤ 20` by that minimum gives a **period-doubling
cascade** whose carry words are the Thue–Morse prefixes (up to a cyclic shift):

| period | 2 | 4 | 8 | 16 |
|---|---|---|---|---|
| `minᵢ ‖yᵢ‖` | `2/5` | `4/13` | `28/97` | `1948/6817` |
| carry word | `01` | `0011` | `00101101` | `0010110011010011` |
| enters at `L` | `1/5` | `5/13` | `41/97` | `2921/6817` |

with the closed form `4c_k − 1 = 3·∏_{n=1}^{k−2}(3^{2ⁿ} − 2^{2ⁿ}) / (3^{2^{k−1}} + 2^{2^{k−1}})`,
verified against the enumeration for `k ≤ 4`.  Dividing through by powers of `3` gives the limit
immediately:

> `c_k ↓ (1 + T(2/3))/4 = 0.285647324744458851…`,  `T(z) = ∏_{n≥0}(1 − z^{2ⁿ})`,

which is **exactly** [Dub06JNT] Corollary 1's small limit point.  Measured, the family certifies at
`c = 0.2856475` and fails at `c = 0.2856472`: the constant is inside the bracket.  The same cascade
read from the other side is X-238's — `0, 1/5, 3/13, 23/97, 10233015/42981185, … → (3 − T(2/3))/12
= 0.238117558418…`, whose ceiling X-238 measured in `(0.2381175, 0.2381177]`.

**Both of this corpus's engine ceilings are the two constants of [Dub06JNT] Corollary 1, and
neither is attainable**: below either one the set contains every cascade orbit, hence infinitely
many periodic orbits, which `Cert.ok_eq_false_of_infinite_cycles` forbids.  So no further search on
this certificate family can beat print on either side — not for want of effort, but because the
printed constants are the accumulation points of the family's own obstruction.

### What X-F says about the conjectures

* **C-6 is half true.**  Sixteen windows of the `L*` row have the 2-cycle `{2/5, 3/5}` as their
  only orbit to period 20; 14 certify, and `i = 960`, `i = 1174` do not.  The forward half was
  never a conjecture — it is `Cert.eq_of_memI_block`.  The inventory is constant on 35 runs, each
  interior run carrying *one* extra orbit of period `14, 12, 10, 8, 6, 4` inward, and the certified
  positions are exactly the run **boundaries**: mode locking, with the certified set the
  transitions rather than the plateaus.
* **C-7 becomes an equality.**  With `ker(z) = sup{k : z ∈ T_k}`, the ranked funnel depth is *one
  of* `ker(s)`, `ker(s+L)` at **213 of 213** ranked-certified positions, and is `2ᵏ − 1` on the
  `k`-th cascade plateau of the centred line.
* **A caution.**  The alive-component count is *not* an entropy proxy: `[2/7, 5/7)` has alive
  counts `60/370/1180/2740` at depths `10/20/30/40` and still ranked-certifies at depth 15.  A
  component may shrink onto a point outside `U`.  Only the ranked criterion decides.

## The atlas draft (two colors and the band)

Single intervals `[s, s+L)`:

| L | positions | color | certificate |
|---|---|---|---|
| ≤ 1/3 | **every** `s` | **EMPTY** | [Dub09AA]; formalized: `Z32.ZSet_three_two_third_empty` |
| 1/3 | 0, 1/6, 1/3, 1/2, 2/3 | **EMPTY** | escape N = 3,2,3,1; formalized: `Z32.FLP_cor_one_four_a` |
| 1/6 | e.g. `[1/12,3/12)` | **EMPTY** | KILL, depth 3 — unconditional |
| (1/3, 0.40722] | a shrinking set, 79 % → 0 % | **EMPTY** where certified | CYCLE (engine); `[1/6,13/24)` and the frontier now **proved**: `Z32.ZSet_three_two_sixth_3_8`, `Z32.ZSet_three_two_frontier` |
| (1/3, 0.40722] | the rest | **BAND** | §4.3 tried and refuted (M7): the product refinement gains nothing (Thm A), and here the cycle count is too small for Thm B to close it either — genuinely open |
| (0.40722, 19/24) | all | **BAND** | nothing certified either way |
| 19/24 = .7917 | (5/48, 43/48) | **NONEMPTY** | [Dub08] Thm 1.3 (≥1 per unit interval) |
| 57/65 = .8769 | [4/65, 61/65] | **NONEMPTY**, positive `dim_H` | [Pol81]; trap formalized in `Bugeaud/Chapter3/PollingtonConstruction.lean` |
| 17/19 = .8947 | [1/19, 18/19] | **NONEMPTY** | [Cho80] |

Unions:

| \|U\| | set | color | certificate |
|---|---|---|---|
| → 0 | [KK18] Cor 4.11 family | **NONEMPTY** | literature (constructive in principle) |
| 2/3 | `X_{3,2}`, and `‖·‖<1/3` | **NONEMPTY** | [KK18] Cor 4.8, [Dub10] |
| .476 | [Dub06] complement | **EMPTY** in print; **BAND** for this engine | [Dub06]; engine says FAT, λ ≈ 1.15 |
| 20/39 | [Dub08] Cor 1.2, **closed** | **EMPTY** | CYCLE, 12 blocks in 4 rank strata; **proved as printed**: `Z32.dubickas_2008_cor_1_2` |
| 25/36 | the 36-cell union | **EMPTY** | **proved**: `Z32.union_record_empty` (formalized record) |
| **.7417** | the 240-cell union above | **EMPTY** | CYCLE, 2512 blocks (engine record) |
| 1−ε | non-constructive | **EMPTY** | [KK18] Thm 5.9 |

---

## Verification depth (why to trust the verdicts)

Four implementations, two of them genuinely independent on the load-bearing
path:

1. `hold.c` — θ-coordinates (the FLP coordinate the Lean chain uses), single
   windows, exact `__int128` over `G·3^k`, plus the kneading-orbit escape test
   over `G·2^n`.
2. `atlas.c` — `y`-coordinates, arbitrary unions, exact, block-merge certificate.
3. `gridcert.c` — a uniform cell SFT with peeling, Tarjan SCCs and a
   branching-SCC test: a completely different algorithm.
4. `verify_atlas.py` — Python `Fraction` re-implementation, deliberately naive
   (generate every preimage, sort, merge), written to be slow and obviously
   correct.
5. **the Lean kernel** (M3) — for the six entries of `BlockCert.lean` there is a
   fifth checker that shares no code with any of the above: `gencert.py` emits a
   funnel, and the kernel rechecks both certificate conditions from the literal
   integer data. A wrong verdict from every engine at once would still have to
   survive this.

Checks actually run:

- **(1) vs (2)**: identical component counts at all five FLP positions
  (1, 3, 2, 3, 1) and identical certified/undecided verdicts across the `G = 24`
  length sweep.
- **(2) vs (4)**: identical component counts at **every level 15…30** on the
  record union (…1509, 1867, 2252, 2699… and …691, 688, 675…), and identical
  block structure and verdict on the smaller records, on [Dub08], and on the
  FLP positions.
- **Negative controls**: five sets known nonempty in print, all returned FAT.
  A false certificate here would be visible immediately.
- **Falsification test**: `atlas horse` searches for a *horseshoe* — two
  distinct cycles through one point, which implies uncountably many confined
  orbits and would **contradict** any CYCLE certificate. Run on every certified
  record: none found. Run on the X2 band entries at large `L`: the cycle count
  grows exponentially, as it must. **But not on the band entries at the
  frontier** — corrected at M7: `[961/3600, 2428/3600)` has exactly **one**
  cycle (2 orbit points) at `P ≤ 12`, the same as the certified entry beside it,
  and only a second at `P = 14`. Both `atlas horse` and `prodcert.py cycles`
  agree on this, independently.
- **A real bug was found this way.** The first `atlas.c` merged preimages
  against only the previous interval. For a single window of length ≤ 1/2 the
  preimages under different carries are disjoint, so that was correct — but for
  unions they overlap (the preimage of `[0,1)` under `e` is `[−e/3,(2−e)/3)`,
  width 2/3, while consecutive `e` are 1/3 apart), and the naive merge silently
  dropped intervals, producing a bogus "certified" union of total length 11/12.
  The Python cross-check caught it; the fix is a 4-way merge. All single-window
  results (X1, X2) were verified bit-identical before and after. Recorded here
  because plan R-5 says correlated single-author error is the dominant risk, and
  this is exactly what it looks like. Its blast radius was two verdicts, both
  now corrected: the bogus 11/12 union, and a [Dub06] "reproduction" that the
  fixed engine reports as FAT. Every number in this file was regenerated by
  `reproduce.sh` **after** the fix.

**Known limitation, stated up front.** `gridcert.c` cannot certify any `U` whose
hold set contains a cycle: the image of a cell is 1.5 cells wide, so a genuine
periodic point always looks branching, at every resolution. It is kept as an
independent implementation and for the empty-core certificate, not as an
oracle — its `λ` values are grid artifacts and are **not** dimension data.

**Convention.** `U` is half-open, `[lo,hi)` — the corpus `Ico` standard
(`FLP.ZSet`). Closed windows are *not* decided by the C engines: inflating the
right endpoint by a positive amount is too lossy (for [Dub08]'s set the inflated
version already fails at 1/(39·10⁶) — and the M4′ P1 work explains why, since
the closed hold set is genuinely richer, not marginally so). Closed intervals
*are* decided by `gencert.py --closed`, and proved by `BlockCert.lean`;
upgrading `atlas.c`/`gridcert.c` in the same way is still open (plan R-3).

---

## What this does and does not establish

**Does.** (i) The FLP95 chain reproduces exactly, including Thm 3.4's exact-`N`
trichotomy. (ii) The length-1/3 line holds at every rational position tested and
the stubborn set is provably invisible to rational sweeps. (iii) There is a
sharp engine frontier at `L* ≈ 0.40722` for single windows, and no uniform
`δ > 0` — M4 goes to lane (b). (iv) Explicit certified-empty unions exist with
total length up to **0.7417**, past the best published explicit value.
(v) The X2 band entries at large `L` are provably out of reach of hold-set-only
methods — but **not** the ones at the frontier (corrected at M7; see the
falsification test below). (vii) No block certificate of this family, at any
product level, can prove [Aki08] Conjecture 1.4 — M7, Theorems A and B.

(vi) Six of these entries are now **Lean theorems**, kernel-checked, std3, no
`native_decide` — including a window of length `0.375` and one of `0.40722`,
both past the 1995 line, and a certified-empty union of total length `25/36`.

**Does not.** The atlas *as a whole* is not formalized: the sweeps, the
frontier's sharpness (`nothing is certified above 1467/3600`), the λ / dimension
columns and the 0.7417 record remain engine output, and the six Lean entries are
individual points on the map, not the map. Nothing here touches the twin
ceilings `[0,1/2)` and `[1/2,1)` — at `L = 1/2` the engine returns the whole
interval, exactly as plan §1.3(ii) predicts. And no *numerical* claim is
announced before the M2′-style precondition (independent re-run + artifact +
referee read) is met; the six proved entries no longer need it.

---

## The M6 grid (plan-A6+ milestone WP0)

`plans/plan-A6+.html` §3.2 replaces the linear milestone ladder between M5 (every arc is visited
infinitely often) and M7 (uniform distribution) by a **grid**: how *many* visits an arc receives,
resolved per arc.  Three files ship the vocabulary and the exact arithmetic it runs on; all three
are `std3`, no cited axiom, no `native_decide`.

| rung (per arc) | predicate | state |
|---|---|---|
| V0 visits i.o. | `Z32.VisitsIO` | shipped, all `ξ ≠ 0` — see the ladder above |
| V1 `≥ c log N` visits | `Z32.V1` | **open**; WP2 target (sojourn dichotomy) |
| V2 `≥ c N^θ` visits | `Z32.V2` | open |
| V3 positive upper density | `Z32.V3` | open |
| V4 positive lower density | `Z32.V4` | open — **M6 at that arc** |
| V4S syndetic | `Z32.V4S` | open ⟺ bounded sojourns ⟺ `σ(p) = 0` |
| V5 frequency `= |I|` | `Z32.V5` | open — M7 at that arc |

Proved between the rungs: `V5 → V4 → V2 → V1 → V0`, `V4 → V3 → V0`, `V4S → V4`; and
`Z32.M6_iff_dyadic`, which reduces M6 to the countable family of dyadic windows.  The ceiling the
grid records: nothing above V0 can hold *uniformly in `ξ`* —
`Bugeaud.Pollington.exists_forall_dist_ge_of_cert` exhibits a `ξ > 0` avoiding the length-`8/65`
arc at `0` for ever.  Everything above V0 is `ξ = 1` territory.

The exact arithmetic at `ξ = 1` (`Z32/DyadicOrbit.lean`): `xₙ = rₙ/2ⁿ` with `rₙ = 3ⁿ mod 2ⁿ` odd,
so the points are pairwise distinct, separate by `2^{-max(m,n)}`, and — the floor WP2 runs on —
stay `≥ 1/(D·2ⁿ)` away from every rational with odd denominator `D`, i.e. from every cycle point of
`×3/2`.  Its negative companion: `3` has order exactly `2^{k-2}` mod `2ᵏ`, so the low `k` bits of
`rₙ` are purely periodic — the annealed baseline every census statistic is to be compared against.

The statistics (`Z32/PairStatistics.lean`): the lag identity `x_{m+d} - x_m ≡ ((3/2)^d - 1)(3/2)^m`,
the lag decomposition `P_N(s) = Σ_d C_N(s,d)`, the window energy `E_N(w) = Σ_b A_N(w,b)²` with its
exact L² defect identity (an empty window costs `N²/4ʷ`), and the **Weyl collapse**
`|S_N(2h) - S_N(3h)| ≤ 2` for every `h` — an exact consequence of `2(3/2)^{n+1} = 3(3/2)^n`, which
is why testing frequencies is only informative on the skeleton `gcd(m,6) = 1`.

## Balance vectors, and what finite resolution cannot do (plan-A6+ milestone WP1)

`Z32/BalanceVectors.lean` builds C6's measure-free enemy layer: instead of weak-\* limits of
empirical measures on the solenoid (risk R-G), level-`w` frequency vectors and the
flow-conservation equations of the **level-`w` carry graph**.  `std3`, no cited axiom, no
`native_decide`.  (R-G's compactness half has since closed upstream — Mathlib now has Prokhorov,
tightness, Lévy–Prokhorov and portmanteau — so the measure formulation is scheduled, in
`TH/Solenoid/LimitMeasures.lean` of plan-A1+, rather than blocked.  It would not rescue this layer:
the vacuity theorem's witnesses are invariant measures upstairs too.  Details in the file's module
doc.)

*The graph.*  At `ξ = 1` consecutive orbit points obey `2x_{n+1} = 3xₙ - sₙ` with an integer carry
`sₙ ∈ {-1,0,1,2}` (`Z32.exists_carry`, the four letters of `BlockCert.carries 3 2`).  `edgeOk w b b'`
asks whether *some* point of the level-`w` window `b` is carried into the window `b'` by one branch;
scaled by `2ʷ` that is the meeting of two integer intervals, so the graph is a kernel-evaluable
`Bool`.  It is sparse for `w ≥ 3` (at most the four carries per cell, `4·2ʷ` of the `4ʷ` pairs) and
**complete** at `w = 2` (`Z32.edgeOk_complete_two`).  The orbit walks in it: `Z32.edgeOk_orbit`.

*The balance lemma* (`Z32.exists_balanceVec`).  Along any horizon sequence `N k → ∞` the empirical
flow vectors `#{n < N : cellₙ = b, cell_{n+1} = b'}/N` have a convergent subsequence
(Bolzano–Weierstrass on `[0,1]^{cells²}`), and every limit is a `Z32.BalanceVec`: a probability
vector `μ` on the cells with a nonnegative flow `ν` on the graph whose two marginals are both `μ`.
The out-marginal identity is exact; the in-marginal costs only the two boundary dates (`≤ 1/N`).

*The enemy statement* (`Z32.exists_balanceVec_zero_of_not_V4`, `Z32.exists_trap_of_not_V4`).  If a
level-`w` window `b` has zero lower density — M6 fails there — then the graph carries a stationary
vector with **zero mass at `b`**, whose support is a `Z32.IsTrap`: a nonempty set of cells avoiding
`b` in which every cell has a successor and a predecessor, i.e. a subgraph carrying a cycle that
never visits `b`.  Contrapositive criterion: `Z32.V4_of_forall_trap_mem`.

*And the criterion is vacuous* (`Z32.exists_balanceVec_zero`, `Z32.exists_trap_not_mem`).  For every
`w ≥ 2` and every window `b` such a trap exists, so the criterion never fires and **no level-`w`
balance argument can prove M6 at any window, at any resolution**.  The witnesses are exactly C6's
atomic enemies: the fixed point `0` (a self-loop at the zero cell) and the rational 2-cycle
`{2/5, 3/5}` of denominator `5 = 3² - 2²`.  This is the honest WP1 deliverable — the flow layer
handles Front E bookkeeping and provably cannot touch Front D, which is why Front D is Diophantine.

*The cycle-point classification* (`Z32.cycle_point_eq`, `Z32.dist_cycle_point`).  A `p`-periodic
point of the carry relation is `A/(3^p - 2^p)` with `3^p - 2^p` **odd** — the [L90] rational-cycle
shape — so `Z32.dist_odd_denom` applies and the `ξ = 1` orbit stays `≥ 1/((3^p-2^p)2ⁿ)` away from
every `p`-cycle.  That is the quantitative floor C7/WP2 runs on.

## Files

| file | what it does |
|---|---|
| `VisitDensity.lean` | WP0: visit counts, lower/upper density, the V-rungs and their implications, `M6_iff_dyadic` |
| `DyadicOrbit.lean` | WP0: `xₙ = rₙ/2ⁿ` with `rₙ` odd — distinctness, separation, the 2-adic floor, the annealed baseline, the AP rung |
| `PairStatistics.lean` | WP0: lag identity and decomposition, window energy and its defect identity, Weyl sums and the collapse, `𝓔_N(H)` |
| `BalanceVectors.lean` | WP1: the level-`w` carry graph, empirical frequency/flow vectors, the balance lemma, the trap form of the M6 enemy, its proved vacuity at every level, the [L90] cycle-point classification |
| `hold.c` | engine A: θ-model, single windows; `orbit` (kneading escape), `prune`, `x1`, `x2` |
| `atlas.c` | engine C: exact `y`-model for arbitrary unions; `cert`, `win`, `x2`, `x3`, `x3exh`, `horse` |
| `gridcert.c` | engine B: uniform cell SFT, peel + Tarjan + branching-SCC test; `cert`, `ladder`, `search` |
| `verify_atlas.py` | independent Python/`Fraction` re-implementation (the cross-check) |
| `gencert.py` | M3/M6: emits the kernel-checkable funnel for `BlockCert.lean`; refuses the negative controls; `--pq p q`, `--closed`, `--ranked` |
| `pqcontrols.py` | M6: the second-base controls — [Dub09AA]'s length-`1/p` line, [Aki08]'s nonempty sets, and the cover test |
| `prodcert.py` | M7/X4: the §4.3 product refinement `(cell, x mod qʲ)`, the periodic-orbit census, and the two no-go theorems it measures; `cycles`/`hold` subcommands |
| `BlockCert.lean` | M3/M6: the soundness theorem for any coprime `p > q > 1`, and the eight `decide`-checked entries |
| `x3climb.py` | refinement hill-climb for the union record, driving `atlas` as a black box |
| `xg0.py` | the three gate-G-0 experiments X-KP / X-D19 / X-238; writes `data/xg0_*.txt` |
| `g1schema.py` | gate G-1: the closed-form depth-1 schema in `(p,q,s)`, checked against an independent engine and against `gencert.py`; writes `data/transform/g1_schema.txt` |
| `SymbolicCert.lean` | gate G-1 / milestone M1: the depth-one schema as a theorem for every base and every **real** position; T1, T2 (the thirty table entries) and T3 grade 1 as corollaries; no certificate data for the kernel |
| `xp.py` | experiment X-P re-aimed at the two residual bands: the exact parametric `ε`-cell decomposition, plus two independent scalar engines; writes `data/transform/xp_bands.txt` |
| `DepthKSchema.lean` | milestone M3: the depth-`K` schema — `Escape`, the rank rotation, `ZSet_eq_empty_of_certifiedK`, the closed-form `LowBand` family and the `(5,2)` depth-2/3 instances. A formalization of [FLP95] Thm 3.4 + [Bug04] Thm 1 and Lemmas 1–3; no certificate data for the kernel |
| `m3schema.py` | M3's R-5 bridge: the escape criterion against the funnel engine, the Lean predicates transcribed, the rank rotation, and [Bug04] Lemma 3's intervals `J_b^a(q/p)` as an independent literature check; writes `data/transform/depthk_schema.txt` |
| `EscapeBound.lean` | milestone M2: the quantitative escape bound — `escape_endgame` (the dichotomy), `escapeSteps`, both front ends, `Cert.exists_escape_le` (= the plan's `Cert.escape_bound`) and eight per-entry effective corollaries. Needs `c.strata = []`: the ranked `certDub08` admits no such bound |
| `m2escape.py` | M2's R-5 bridge: certificate shapes re-parsed from `BlockCert.lean` and `UnionRecord.lean`, 11826 simulated orbits against the certified bound, 8728 endgame dichotomy checks, and the `log(1/ξ)` counterexample; writes `data/transform/escape_bound.txt` |
| `CertComplete.lean` | milestone M4: completeness on the finite-hold-set class (`step_unique`, `holdSet_finite_imp`), C-2 at every base (`cyclePoint_eq_base`), the unranked obstruction (`Cert.eq_of_memI_block`, `Cert.ok_eq_false_of_infinite_hold`) and five closed-convention entries |
| `m4complete.py` | M4's R-5 bridge: the two Bool checks re-implemented and run on the five new certificates plus unranked controls, `step_unique` and C-2 over many bases, the two-cell chain, the ten-entry depth survey and the block bound; writes `data/transform/cert_complete.txt` |
| `CycleTransversal.lean` | experiment X-U: the recurrent map in closed form (`cycOrbit`, `cycOrbit_rec`), no transients (`cycOrbit_periodic`), the converse of C-2 (`cycOrbit_period_dvd`, `exists_periodic_orbit`), and the transversal theorem `Cert.ok_eq_false_of_infinite_cycles` — the corrected form of conjecture C-8 |
| `xu.py` | X-U's driver and R-5 bridge: the closed-form map against brute force, the period-≤14 census (531 292 orbits) against the four records, each record's hold set from an independent exact funnel, the 48-entry hand-built `U_P` table with funnel-fixed-point detection, the refinement ladder to 1440 cells, and the two measure facts; writes `data/transform/union_autopsy.txt` |
| `DepthSize.lean` | milestone M5(a): the depth–size bound — `slice`/`fold`/`pre` with `pre_eq_slice_fold`, the expansion half `volume_le_volume_pre` and `one_le_volume_funnel_add`, the contraction half `abs_sub_le_of_memI_block` + `volume_funnel_le_of_cert`, the headline `cert_depth_size` (`1 ≤ 2δ(K+2+log_{p/q}2B)`), and the corollaries `volume_hole_pos`, `volume_certSet_lt_one`, `hole_union_2536`. First measure theory in this root; no certificate data for the kernel |
| `depthsize_check.py` | M5(a)'s R-5 bridge: the exact funnel of the `25/36` and `17/24` records against all three statements of the bound (`|T_k| ≥ 1−(k+1)δ`, `|T_{K+j}| ≤ B(q/p)ʲ`, the headline), and the headline arithmetic for the two wider records; writes `data/transform/depth_size.txt` (~2 s) |
| `xf.py` | experiment X-F: the frontier row rechecked without `atlas.c`, the survivor-cycle inventory by carry-word DFS (cross-checked against the denominator census), the trichotomy, the kneading depths, the ranked frontier, the two staircases and the Thue–Morse cascade; writes `data/transform/frontier_autopsy.txt` (~3.5 min) |
| `RankedFrontier.lean` | X-F's kernel-checked output: `certTwoSeven` (closed, rank-stratified, depth 15, 166 blocks over `D = 7·3¹⁵`) with `ZSet_three_two_two_seven`, `two_seven_empty`, `not_eventually_two_seven` and `not_forall_two_seven_le_abs_sub_round` (`‖ξ(3/2)ⁿ‖ < 2/7` infinitely often) |
| `XG0Certs.lean` | their kernel-checked output: `two_cell_238_empty`, `ZSet_three_two_d19_shift`, `log_twentyone_div_eight_le_phiModel_kp` |
| `reproduce.sh` | regenerates every number above into `data/`, with checksums |
| `data/*.txt` | the sweep outputs quoted above |
| `data/transform/*.txt` | the outputs of `plans/plan-z32-transform.html` (gate G-1, experiment X-P, milestones M3, M2 and M4), kept apart so the two plans' data cannot collide |

Build: `gcc -O2 -o atlas atlas.c -lm` (likewise `hold`, `gridcert`).

## References

- **[FLP95]** Flatto, Lagarias, Pollington, *On the range of fractional parts
  ξ(p/q)ⁿ*, Acta Arith. **70** (1995) 125–147. Formalized: `FLP/`.
- **[Dub09AA]** Dubickas, *Powers of a rational number modulo 1 cannot lie in a
  small interval*, Acta Arith. **137** (2009) 233–239. Formalized:
  `Z32/SmallInterval.lean`.
- **[DN05]** Dubickas, Novikas — the aperiodicity lemma. Proved:
  `Z32/DubickasWord.lean`; it is the sole analytic input of the M3 certificate.
- **[Dub06]** Dubickas, J. Number Theory **117** (2006). **[Dub08]** Dubickas,
  Math. Nachr. **281** (2008). **[Dub10]** Dubickas (2010).
- **[Pol81]** Pollington, C. R. Acad. Sci. **292** (1981) 383–384.
  **[Cho80]** Choquet. **[Bug04]** Bugeaud. **[Kwon15]** Kwon.
- **[KK18]** Kari, Kopra — automata and `Z_{p/q}(S)`; Problem 6.1.
- **[KP18]** Kurganskyy, Potapov, *De Bruijn graphs and powers of 3/2*, Trudy IPMM **32**
  (2018), arXiv:1811.02254. Cor. 18 reduces Mahler's problem to `[0,1/6) ∪ [1/3,2/3)`.
- **[Dub19]** Dubickas, Discrete Math. **342** (2019) 1949–1955. Thm 1.2 = the window
  `[8/57, 805/1539]` at `3/2`. **[Dub06JNT]** Dubickas, J. Number Theory **117** (2006) 222–239,
  quoted as Thm 3.14 of Bugeaud's Cambridge Tract 193.
- **[AFS08]** Akiyama, Frougny, Sakarovitch. **[Aki08]** Akiyama.
- Plan: `plans/plan-cert32.html`. Engine ancestor: `plans/plan-dubC1.html`,
  `DubC/README.md`.
