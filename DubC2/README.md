<!-- (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0. -->

# `DubC2/` — plan-dubC2: the search engine (M1) and the Lean chain (M3)

Milestones **M1** and **M3** of `plans/plan-dubC2.html`.
Verdict notes: `plans/note-dubC2-M1.html`, `plans/note-dubC2-M3.html`,
`plans/note-dubC2-T3ii.html`.

Two kinds of file live here and they must not be confused:

* **`*.py`, `*.c` — engine code (M1).** Search, calibration, entropy ledger. Nothing here
  is machine-checked; per house rule R-12 no olean exists for any of it.
* **`*.lean` — the certification chain (M3).** Oleans exist for every module, and
  `#print axioms` reports exactly `propext, Classical.choice, Quot.sound` for every claimed
  declaration — no cited literature axiom, no `native_decide`, no `sorry`.
  Rebuild `DubC2/AxCheck.lean` to re-check that.

**The theorem is machine-checked:** `DubC2.round_divisor_set` in `DubC2/Nearest.lean`.
So are two of the three literature calibrations: `round_divisor_set_five_thirds` ([DN05]
Thm 4(ii)) and `round_divisor_set_seven_fifths` ([DN05] Thm 4(iii)).

---

## The model

`x_n = [ξ(p/q)^n + ν] = ⌊ξ(p/q)^n + ν⌋`, `y_n = {ξ(p/q)^n + ν} ∈ [0,1)`,
carry `s_n = q·x_{n+1} − p·x_n`. With `w := (p−q)ν`,

```
q·y_{n+1} = p·y_n − w − s_n            Dom(s) = [ (s+w)/p , (s+q+w)/p ) ∩ [0,1)
S(p/q,ν)  = { s : Dom(s) ≠ ∅ }          s_n ≡ −p·x_n  (mod q)
```

The windows `Dom(s)` tile `[0,1)` inside each residue class of `s` mod `q`.

Joint graph `G(P,K,D)`, states `(u, r, c)`:

| coordinate | meaning | transition |
|---|---|---|
| `u ∈ Z/q^K` | the q-adic coordinate (`q` prime), `u ≢ 0` if `q ∈ P` | `u' = (p·ũ+s)/q mod q^K` over **all** `q` lifts `ũ` of `u` mod `q^{K+1}` |
| `r` | residues mod the `ℓ ∈ P` with `ℓ ∤ q`, all nonzero | `r'_ℓ = q^{-1}(p·r_ℓ + s) mod ℓ`, must stay nonzero |
| `c` | cell `[c/D, (c+1)/D)` | `c` meets `Dom(s)`, and `c'` meets `T_s(c ∩ Dom(s))` |

`u` is *exactly* a look-ahead of the next `K−1` letters' residues mod `q` — it loses one
level per step and nothing else. At `q=2` with `2 ∈ P` it is **redundant** (the two odd
letters already partition `[0,1)`), which is why the `3/2` verdicts are identical at
`K = 2,3,4,5`. Over-approximation only ever *adds* paths, so certificates are one-sided:
they prove unavoidability, never avoidability.

## The verdict

```
C_det(P):  for every cyclic SCC C of the core, every cyclic SCC of the core
           of det(C) is a simple cycle
```

i.e. *every infinite path has eventually periodic carry word* — which
`Z32.not_isEventuallyPeriodic_carry` ([DN05] Lemma 2, ν-general, ξ ≠ 0) forbids.

**Not** dubC1's state form ("every cyclic SCC of the core is a simple cycle"). That form is
wrong here: a branch `T_s` expands by `p/q`, the grid rounds each image up to the next cell
boundary, and the fixed point of `R ↦ (p/q)R + 1` is `R = q/(p−q)` — so every genuine
periodic orbit appears in the graph as a **tube** of that many cells, which branches. The
tube's width is a number of *cells*, not a length: refining `k` does not shrink it. Every
edge of a tube carries the same letter, so the carry word is still forced. The state form
is not even monotone in `k` (at `5/3` it holds at `k=2`, fails at `k=3,4,5`, holds at `k=6`).

## Files

| file | what |
|---|---|
| `joint.py` | reference engine — exact `Fraction` intervals, worklist peel, scipy Tarjan, frozenset subset construction. Also `--branch-table`, `--cycles`, `--sound`. |
| `joint.c` | independent engine, no shared code — int64 numerators over one denominator, bitset peel, hand-written iterative Tarjan, hashed sorted-`int32` subsets. `gcc -O2 -o joint joint.c -lm` |
| `exact_words.py` | cell-free census: enumerates admissible carry words with their **exact** y-intervals and residues. No grid, no graph, no peel. Gives the exact word complexity `p_n`. |
| `xscan.py` | X0 — avoidance-prefix statistics and the adversarial constructor, computed straight from `x_n = ⌊ξ(p/q)^n+ν⌋` in exact big integers. |
| `g3.py`, `g3.log` | the G-3 gate: runs both engines over the ladder and diffs every field. |

## Reproduction

```sh
gcc -O2 -o joint joint.c -lm
python3 g3.py > g3.log              # both engines, every rung, diffed        (~25 s)
python3 joint.py --pq 3 2 --nu 1/2 --P 2,5 --K 2 --k 8 --det --cycles
python3 joint.py --pq 3 2 --nu 1/2 --P 2,5 --K 2 --k 4 --sound 200
python3 exact_words.py --pq 3 2 --nu 1/2 --P 2,5 --n 40 --words
python3 xscan.py --pq 3 2 --nu 1/2 --P 2,5 --word 1,1,-1,-1 --construct 8,32,128,512
python3 joint.py --pq 3 2 --nu 1/2 --branch-table
```

Single machine; none of the above runs `lake`. Largest graph built: 3.5M nodes / 5.9M edges.
For the Lean side: `LEAN_NUM_THREADS=3 lake build DubC2` (the axiom report is printed by
`DubC2/AxCheck.lean`).  The two independent cross-checks of the Lean chains are
`python3 m3check.py` (`3/2`) and `python3 m3check75.py` (`7/5`); neither imports anything
from the repository.

## Results (M1)

**G-3 calibration — all four known answers reproduced, both engines agreeing on every
field and on λ to 12 digits at every rung.**

| case | `P` | verdict | surviving carry words |
|---|---|---|---|
| `5/3`, ν=½ — [DN05] Thm 4(ii) | `{2,3}` | HOLDS | `(−2,−2,+2,+2)` = `(A²B²)^∞` **and** `(+2,−2)` = `(AB)^∞` |
| `7/5`, ν=½ — [DN05] Thm 4(iii) | `{2,3,5,11}` | HOLDS | periods 3, 6, 9 over `{±2,±4}`, ±-symmetric pairs |
| `3/2`, ν=0 — [DN05] Thm 1 / [FS67] | `{2,5,7,11}` | HOLDS | `(+1)^∞`, an 8-cycle, a 16-cycle |
| `3/2`, ν=½ — **the open case** | `{2,5}` | **HOLDS** | `(−1,−1,+1,+1)^∞` up to rotation |

The cell-free census reproduces the plan's own G-4 numbers from a code path with no grid
in it: `p_32 = 853454` with ratios 1.4998 at `P={2}` (i.e. entropy `log(3/2)`), and
`p_n = 2n` exactly at `5/3`.

Two corrections to the literature and to the plan fell out of the gate:

* **At 5/3 the engine finds two realized periodic orbits**, `(A²B²)^∞` at `y₀=1/34` and
  `(AB)^∞` at `y=1/4` (check: `A(1/4)=3/4`, `B(3/4)=1/4`). [DN05] p. 646 is **correct**:
  it says verbatim "*If the sequence is not `A^∞`, `B^∞` or `(AB)^∞` (`(BA)^∞` is the same),
  then we must have either `A²` or `B²`*" — the case list is complete, and the engine only
  sharpens it (`A^∞`, `B^∞` cannot occur, since `A³`/`B³` are impossible). What drops the
  case is **plan-dubC2 §0's paraphrase**, "the intervals alone force `A²→B²→A²···`" — the
  sentence a T3 formalization of 5/3 must not transcribe literally.
* **The plan's X0 exit test is backwards.** A *successful* `P` leaves one periodic carry
  word, and a periodic carry word yields **arbitrarily long avoiding prefixes**. At
  `P={2,5}`, `xscan.py --construct` produces ξ with verified avoiding prefixes of length
  9, 33, 129, 513. Long prefixes are the signature of success. (Consequence: target T4,
  the bounded-window density upgrade, is *unavailable* for this `P`.)

### Openness (re-checked 2026-08-19 for the specific set)

No scoop. "(3/2)^n + 1/2" occurs in **none** of the 232 local PDFs; "divisible by 2 or 5"
in two, neither at 3/2. The decisive source is **[Nov12]** — see the references. The one
near-miss, [PR19], is for PV/Salem α and does not apply. Corpus: no conflict
(`DubC/Verdict.lean` has integer bases 3,4,5,6 only). Consistency check: `P={2}` fails at
**both** shifts (λ_det = 1.50000 at ν=0, 1.50003 at ν=½), so the method cannot touch
Mahler's problem — which matches [Dub06eo], where "⌊ξ(3/2)ⁿ⌋ even for all n" is recorded as
open and equivalent to Mahler's Z-number question. The prime 5 is doing indispensable work.

### The M1 headline

> For every real ξ ≠ 0, infinitely many of the nearest integers `[ξ(3/2)^n + ½]` are
> divisible by 2 or by 5.

Certified by four independent computations, and short enough to check by hand — the paper
proof is `plans/note-dubC2-M1.html` §4.1. In outline: all-odd forces `s ∈ {−1,+1}`, whose
windows `[0,½)`,`[½,1)` make the letter a function of `y`; `A²` needs `y<1/6` and lands in
`[5/8,1)`, `B²` needs `y≥5/6` and lands in `[0,3/8)`, so no `AAA`, no `BBB`; mod 5,
`x ↦ 4x+3s` kills `2 —A→ 0` and `3 —B→ 0`, leaving `{1,2}` and `{3,4}` invariant, in which
`B`-blocks have even length, hence exactly 2; and the two remaining blocks `A BB`
(domain `[7/18,½)`) and `AA BB` (domain `[5/54,1/6)`) both land in `[0,3/8)`, while
`3/8 < 7/18` — so after one completed block only `AA BB` is reachable. The word is
`(AABB)^∞`, and [DN05] Lemma 2 forbids that.

`{2,5} ⊊ {2,5,7,11}`: the nearest-integer case at `3/2` is **strictly easier** than the
floor case that cost [FS67] eight lemmas. Reason: at ν=½ the two letters split `[0,1)`
evenly, so `A²` and `B²` are both very expensive; at ν=0 the windows are `[0,1/3)` and
`[1/3,1)`, `A²` is impossible and `B`-blocks are unbounded — a far richer language.

### Minimality, and the entropy ledger

`λ_det` of the determinized graph (the honest number; the state-graph λ counts the tube).

| `P` | λ_det at ν=½ | λ_det at ν=0 | first moment `(3/2)·∏(1−1/ℓ)` |
|---|---|---|---|
| `{2}` | 1.50003 | 1.50000 | 1.5 |
| `{2,3}` | 1.50022 | — | 1.5 (3 is inert once 2 ∈ P) |
| `{2,5}` | **1.00000** | 1.32472 | 1.2 |
| `{2,7}` | 1.35032 | 1.28520 | 1.2857 |
| `{2,11}` | 1.39041 | — | 1.3636 |
| `{2,13}` | 1.43405 | — | 1.3846 |
| `{2,5,7}` | **1.00000** | 1.21061 | 1.0286 |
| `{2,7,11}` | — | 1.12563 | 1.1688 |
| `{2,5,7,11}` | **1.00000** | **1.00000** | 0.9351 |

No single prime works; among `{2,ℓ}` with ℓ ≤ 19 only `{2,5}` does. The first moment is a
poor guide in both directions — keep it for scan *ordering* only.

## The Lean chain (M3, 2026-08-19)

The certificate is a **theorem, not emitted data**. M1 found the answer at `|P| = 2` with a
paper proof short enough to check by hand, so the plan's `NearestCert` + `NearestData` pair
(subset construction, SCC ranks, `decide` over a 24-state automaton) collapses to three
lemmas and no data file at all. `DubC2/NearestData.lean` does not exist and is not needed.

| module | content |
|---|---|
| `NearestStep.lean` | the model at `(p,q,ν) = (3,2,½)` as an instance of `Z32.xInt`/`yFract`/`carry`; the `round` bridge; `\|s\| ≤ 2` from the interval and `s ≡ x (mod 2)` from the recurrence, hence the two-letter alphabet; the branch table `stepA`/`stepB`. |
| `ProductState.lean` | `Avoids`; the residue map `r ↦ 4r+3s` mod 5 as six named edges; the two forbidden letters (`A` at `r=2`, `B` at `r=3`) read as windows on `y`. |
| `NearestCert.lean` | `funnel` (block-start cell `[0,3/8)` ⇒ sharp cell `[5/54,1/6)`), `cycle` (the `AABB` block, residues `1→1→1→2→1` and `4→3→4→4→4`), `seed` (entry within 5 steps), and `isEventuallyPeriodic_sN`. |
| `Nearest.lean` | the capstone `round_divisor_set` and the composite corollary `round_composite`. |
| `Calibration53.lean` | target T3(i): **[DN05] Thm 4(ii)** at `5/3`, `P = {2,3}` — the first formalization of a nearest-integer divisor-set theorem from the literature. |
| `SevenFifthsCore.lean` | target T3(ii), part one: the `A,C` subshift at `7/5` as an **abstract** `DubC2.AC.Data`, and the theorem that any such orbit has an eventually periodic carry word. Blocks `AC`, `AC²`, `AC³`; the look-ahead `three_of_ge`; the `V`/`U` dichotomy `threeStep`; the mod-11 peel to `{1,9}`; cycles of period 6, 9 and 3. |
| `Calibration75.lean` | target T3(ii), part two: the model at `(7,5,½)`; the alphabet from `{2,5}`; the mod-3 orientation invariant; the four windows; the **two** instantiations `data_AC` and `data_BD`; `round_divisor_set_seven_fifths`. |
| `m3check75.py` | stdlib-only cross-check of the `7/5` chain: every interval constant, closed form, residue and death table, the peel and the mirror, plus exact-`Fraction` orbit simulation. 0 violations. |
| `AxCheck.lean` | the axiom-hygiene module (35 lines). |

### Why the tube never appears in Lean

The engine had to determinize before `C_det` would fire, because a grid carries every genuine
periodic orbit as a branching tube of `q/(p−q)` cells. A hand proof tracks the real number
`y_n`, not a cell of it, so it never meets the tube. That is the entire difference between the
two routes, and it is why the plan's "one decidable predicate that the emitted subsets are
closed under the label transition" is not needed here.

### The 5/3 calibration, and the shape of the other two

At `3/2` the two windows `[0,½)`, `[½,1)` **partition** `[0,1)`, so the interval forbids
nothing at top level and all the pruning comes from the residues mod 5. At `5/3` it is the
reverse: `2 ∤ x` makes `s` even, `3 ∤ x` makes it prime to 3, and with `|s| ≤ 3` only `s = ±2`
survive — after which the residues say nothing more, and the **gap** `[2/5, 3/5)` between the
two windows does all the work. Two periodic words survive there, not one, and the Lean proof
splits on the single threshold `y < 1/9`: below it the orbit is locked into `(AABB)^∞`
(period 4), and an orbit that never dips below it is trapped in `[1/9, 2/5)` as `(AB)^∞`
(period 2). This is exactly where plan §0's paraphrase must not be transcribed.

At `7/5` a third weighting appears, and the first reading of it was **wrong**. After the
alphabet reduction four letters remain, `s ∈ {±2,±4}`, with windows `[0,2/7)`, `[0,4/7)`,
`[3/7,1)`, `[5/7,1)` that **overlap** — from which an earlier version of this file, and of
`note-dubC2-M3.html` §5, concluded that the letter is not a function of `y` and that no hand
funnel exists. But `P` also contains 3, and mod 3 the letters split into `{A,C} = {−4,2}` and
`{B,D} = {−2,4}`, with `x mod 3` an orbit invariant that selects the pair. *Within* a pair the
windows are disjoint and leave a gap, so there is a branch table after all. The two
orientations are exchanged by `x ↦ −x`, `y ↦ 1−y`, which flips the half-open endpoints;
`DubC2.AC.Data` states the windows with `≤` on both sides, so one abstract theorem covers both
and [DN05]'s "this makes no difference in our argument" becomes a second instantiation rather
than a repeated proof. See `plans/note-dubC2-T3ii.html`.

The remaining calibration is **not** done, and that reason is structural:

* `3/2` at `ν = 0`, `P = {2,5,7,11}` (= [FS67], report §F.3): the letter *is* a function of
  `y`, but `A²` is impossible and `B`-runs are unbounded — so there is no finite block
  decomposition at all, the residue side is a 240-state graph on
  `(Z/5)^× × (Z/7)^× × (Z/11)^×`, and the certifying object is a 28-state determinized
  automaton over a 48-cell grid. That is the emitted-certificate route the plan budgeted, and
  it needs M2's X3 extraction first.

## The atlas (M2, 2026-10-08)

Verdict note: `plans/note-dubC2-M2.html`.

* **Generic certificates.** `GenCert.lean` (Boolean checks `roundOK`, `detOK`, `checkHead`,
  structure `Checked`; oversized det rows split into `detRowOK` pieces and reassembled by
  `detOK_of_rows`) + `GenSound.lean` (`divisor_set_of_checked`: a checked certificate is the
  theorem "for every ξ ≠ 0, infinitely many ⌊ξ(p/q)ⁿ + ν⌋ have a divisor in 𝒫").
* **Emitter.** `gencert.py` — `LeanModel` (exact Lean semantics), `add_instance(p, q, nu, P, D,
  title)` writes `Atlas/<name>/{Data,Part*,Main}.lean`, registry `Atlas/registry.json`, index
  `Atlas.lean`. Instances form ONE linear import chain; build one module at a time.
* **Scan.** `atlas2.py` → `atlas_out/atlas2.jsonl` (21 bases × ν ∈ {0, ½, −1}, primes ≤ 13,
  |𝒫| ≤ 4). All 16 minimal hits are machine-checked (`DubC2.Atlas.*`, std3); R-6 check
  `atlas_sound.py`: 0 violations.
* **[Oda26] bridge.** `OdaBridge.lean` (`first_hit_of_checked`: T4 first-hit bound);
  `ObstructionKit.lean` + generated `ObstructionAtlas.lean` (`obstruction_scan.py --emit`;
  Thm 42 obstruction atlas, T5 partial). The shift-general [Oda26] theory is in `Oda26/`.

## The shift axis (plan-dubC2-transform M0/M1, 2026-10-08)

**X-C cycle census** (`xcensus.py`, outputs `data/transform/xc_*.jsonl`, note §6 of
`plans/note-dubC2T-M0.html`). The exact periodic avoiding pseudo-orbits (y-cycles plus residue lifts)
are compared with the det cycles in each `Data.lean`. The two agree as **sets of words, up to grid
artefacts** (fixed points at the excluded y = 1, or outside [0,1)). There were 0 exceptions over the 16
atlas certificates and 209 ladder certificates. It is not a bijection: several det cycles can carry one
word, and one y-cycle can carry several residue lifts. C-8 (balanced words) is refuted.

**Surviving words, proved** (`GenBlocks.lean`, `Blocks.lean`, generated by `xblocks.py`; std3).
For a checked certificate, every avoiding pseudo-orbit (`Gen.Pseudo`: x, y and letters with the
recursions, no ξ) eventually reads one listed word forever (`Gen.Pseudo.eventually_word`). Grid
artefacts are excluded by `Gen.Pseudo.not_artefact`. This is instantiated at 7/5 {2,3,5,13},
floor 3/2 {2,7,11,13} and floor 3/2 {3,5,7,11}; the other two cells are covered by the hand chains.

**X-DB certificate database** (`certdb.py`, output `data/transform/db/`: `certdb.sqlite`, one CSV
per table, `shortlist.txt`, `oeis_cache.json`; note §7). Regenerated from the registry, the
`Data.lean` files, `atlas_out/` and the X-S/X-C/sweep outputs. Tables: `rows`, `verdicts` (refusals
included), `thm42`, `cells`, `cell_primes` (L20 roles: alphabet, orientation, invariant, word),
`cycles`, `ycycle_counts`, `nu_sweep`, `conjectures`, `oeis`. Rerun: `python3 DubC2/certdb.py`
(the OEIS answers are cached; `--no-oeis` skips the lookups).

**G-3 rerun** (`xg3.py`, data `data/transform/g3/`, note §8). The scan was rerun at primes ≤ 17,
|P| ≤ 5, plus the bases 14/9, 15/8 and 17/9. It reproduced the 63 old rows exactly, found no new hit
and killed no conjecture. At integer ν, Thm 42 kills {2} and {3} on all 1030 rows checked.
Both halves are theorems: `ObstructionTwo.lean`, `DubC2.Gen.not_checked_two_of_int` and
`not_checked_three_of_int` (std3). If `b ∣ a` and all primes are 2 (resp. all are 3), then no
certificate is `Checked`, at any `D`.

**X-H horseshoes** (`xhorse.py`, data `data/transform/xh/`, note §9). A horseshoe witness (residue
`r₀`, two non-commuting return words, a closed interval `K` mapped into itself by both inverse
compositions) gives an aperiodic avoiding pseudo-orbit, so no certificate is `Checked` for that set
or any subset, at any `D` and `M`. Under the G-4 checks (48 certified control cells with 0 witnesses,
an independent exact re-check, and paths of `LeanModel.succMask`) it closes the N-2 rows:
- `(6/5, ½)`: no set of primes ≤ 19 certifies;
- `(7/6, ½)`: no set of primes ≤ 23 certifies;
- `(5/4, ½)`: no set of primes ≤ 17 with at most 5 primes certifies.

Open: `(5/4, ½, {2,3,7,11,13,17})`, with two periodic cycles and no horseshoe to length 40.

In Lean (std3): `Horseshoe.lean` has the witness format `HorseWitness`, the Boolean check `horseOK`
and soundness `not_checked_of_horseOK` (prime lists inside the witness's ⇒ `¬ Checked`, any `D`, `M`).
`HorseshoeAtlas.lean`, generated by `xhorse.py --emit DubC2/HorseshoeAtlas.lean`, proves the rows
`b5_4_nu1_2_killed`, `b6_5_nu1_2_killed`, `b7_6_nu1_2_killed` by one `decide +kernel` each. The 5/4
row's 6 maximal sets kill every set of primes ≤ 17 not containing `{2,3,7,11,13,17}`.

X-H on the other 49 empty rows (`--empty`, `--extend-empty`, `--deep-empty`; note §10): 46 close
at every set of primes ≤ 17. `HorseshoeAtlas.lean` now holds 52 row theorems. Open, with polynomial
word growth to length 36: `(5/4,0)`, `(5/4,−1)`, `(7/5,0)` (and `(5/4,½)`), 26 sets, all containing
`{2,3}`.

**Zero-entropy frontier decided** (`xfrontier.py`, note §11). A state of the exact follower
automaton is a pair: the residue sets mod each prime, and the exact `y`-interval. On all 15 open
cells and 43 certified controls this automaton is finite, and it settles each cell:
- **Only simple SCCs: certified at a larger `D`** (8 cells). At `(5/4,0)`: `{2,3,7,11,13}` at
  D=32 ([DN05]), `{2,3,7,11,17}` at D=48, `{2,3,11,13,17}` at D=128. At `(5/4,−1)`:
  `{2,3,5,7,11,13}` at D=32. At `(7/5,0)`: `{2,3,5,11,13}` ([Oda26]), `{2,3,5,11,17}`,
  `{2,3,7,11,13}`, `{2,3,7,11,17}`, all at D=125.
- **Some SCC branches: a horseshoe** (7 cells). Two closed walks give the witness, with words up to
  length 96.

So `(5/4,0)`, `(5/4,−1)` and `(7/5,0)` have certificates just past the old vertex cap, and
`(5/4,½)` is closed at primes ≤ 17. `HorseshoeFrontier.lean` (generated by `xhorse.py
--emit-frontier`, one theorem per witness, std3) holds 5 theorems. No zero-entropy aperiodic cell
occurs. The certified cells are Python verdicts (`gencert.fast_verdict`), not Lean theorems yet.

**T5(iv), completeness for finite follower automata** (note §12). For a cell whose follower
automaton `F` is finite, four conditions are equivalent:
- some `D` certifies;
- `D_F`, the common denominator of `F`'s interval endpoints, certifies;
- no state of `F` branches;
- the admissible language has polynomial growth.

**Necessity is in Lean, for any `F`.** `Branch.lean` (std3) proves `not_checked_of_branchOK`: a
`BranchWitness`, the decidable trace of a branching follower state (two equal-length words fixing a
residue, and a half-open interval inside each word's clipped image), rules out every certificate at
every `D` and `M`. The proof has four steps:
- `Branch.realize` realizes finite segments backwards;
- `PseudoOrbit.step_of` turns each segment into a path of the cell graph;
- König (`Branch.exists_path_of_forall`) gives an infinite path;
- `isEventuallyPeriodic_of_path` makes its letters eventually periodic, which the squares coding is
  not.

`BranchFrontier.lean` (generated by `xfrontier.py --emit-branch`) holds 4 instances.

**Sufficiency is in Lean too.** `Follower.lean` (std3) defines `F`: residues mod `M` times an
interval, stepped by `Follower.step`, independent of `D`. It proves `exists_checked`: if `F` is finite,
its endpoints lie in `(1/D)ℤ`, and no reachable state is `Branching`, then `∃ C, Checked P C`.
`exists_checked_DF` gives the same at `D_F` (`Follower.DF`, the lcm).
- The certificate (`checked_of_family`) has no peeling. Its det states are `verts X` for the states
  `X` of `F`, and its rank is the number of states reachable from a state. So "one rank-keeping
  letter" is "no branching".
- Only soundness is used (`succ_live`, `succ_dead`), not exactness.
- **The bridge is in Lean too.** `exists_branchOK` builds a `branchOK` witness from any branching
  state: powers of two loops fix every residue (`exists_rep_fix`), and `w₁ = AB`, `w₂ = BA`.
  With it, `not_checked_of_branching` and `checked_iff` hold: for finite `F`, some `D` certifies
  ⟺ `D_F` certifies ⟺ no reachable state branches.
- **The growth link is in Lean too.** `polyGrowth_iff` proves that no reachable branching ⟺ the
  admissible language `lang` grows polynomially (`PolyGrowth`).
  - The language is the finite set `words`, because every live letter is in the alphabet
    (`letter_mem`).
  - With branching, the loops `αβ` and `βα` give `2^m` words.
  - Without branching, the rank induction bounds the count by `(nA+1)^N·(n+1)^N`.
- **`T5iv`** states all four conditions as one `TFAE`, so T5(iv) for finite `F` is fully
  machine-checked.
- `xfrontier.py --exact` (12 controls) still checks the paper's exactness claim.

**Infinite `F`** (`FollowerInfinite.lean`, std3). `finite_of_checked`: a checked certificate, at any
`D`, forces `F` to be finite. Hence `checked_iff_finite`, for every cell: some `D` certifies ⟺ `F` is
finite and no reachable state branches, and then `D_F` certifies.
- `eventuallyPeriodic_of_checked`: under a certificate, every admissible infinite word is
  eventually periodic (realization, König on the cell graph).
- `exists_injective_path`: an infinite `F` has a path of pairwise distinct states (geodesic König).
- `not_injective_of_periodic`: along an eventually periodic word the states repeat. Over a period
  the endpoints follow clipped expanding affine maps, and a bounded orbit of such a map repeats a
  value (`exists_rep_of_clip`).

**The literal T5(iv)** (`FollowerLiteral.lean`, std3). `T5iv_literal`, **for every cell**: some `D`
certifies ⟺ every avoiding `PseudoOrbit` is eventually periodic.
- An uncertified cell has an aperiodic admissible word (`exists_aperiodic_adm`).
- Its limit orbit `ystar` is the supremum of the backward realizations of its prefixes.
- After a hit of `1`, every later value is approached from below and is positive. Between hits
  `b·y*` is an integer (`int_of_hits`). With `gcd(q, b) = 1` the next integer value is unique
  (`det_step`, `hits_finite_cop`).
- Otherwise, two hits force `gcd(q, b) ∣ a` (`gcd_dvd_of_two_hits`). So `hits_finite` holds
  whenever `gcd(q, b)` is prime to `a`.
- Its tail is an aperiodic pseudo-orbit (`exists_aperiodic_pseudoOrbit`).
- `F` and the pseudo-orbits depend on `ν = a/b` only, and `red P` puts `ν` in lowest terms, where
  that condition holds (`step_red`, `pseudoOrbit_of_red`, `coprime_red`).

**Infinite `F` and the open question** (`FollowerOpen.lean`, std3 except the conjecture).
- `triv32_infinite`: the unconstrained cell `3/2` at `ν = 0` has infinite `F` (it also branches).
- `no_zero_entropy_obstruction_iff`: without a reachable branching state, these are equivalent:
  `F` finite, certified, all avoiding pseudo-orbits eventually periodic.
- `no_zero_entropy_obstruction` (**open**, `sorry`): no cell has infinite `F` and no reachable
  branching state.

**Real shift parameter (M3, T3)** (`NuInterval.lean`, `NuCircle.lean`, `NuAtlas/`, std3).
At fixed `D` the certificate graph changes only at `ν ∈ (1/((p−q)D))ℤ`.
- `hullOK P a₀ a₁` is a decidable hull check over `[a₀/b, a₁/b]`.
  `divisor_set_of_checked_hull`: `Checked P C` + `hullOK` ⇒ the divisor-set theorem for
  **every real** `ν` in the interval (`Nu.sound` = `Gen.sound` for real `ν`).
- `frequently_of_circle`: from a fundamental domain to `ℝ/Lℤ` (period `L`, mirror `ν ↦ 1 − ν`).
- `xnu.py` (experiment X‑ν) decomposes the circle into closed cells `[j, j+1]/((p−q)D)` with a
  certificate at each midpoint; `--emit` writes `NuAtlas/`.
- Flagship `NuAtlas.b3_2_P2_5_iv1`: `{2,5}` at `3/2` for every real `ν ∈ [½, 25/48]`.
  `b3_2_P2_5_circle`: 15 intervals, 11.85 % of `ℝ/10ℤ`, from 73 cells (`D ≤ 1536`).
- Gate G‑2 passes in grade-2 form: the rest is branching (uncertifiable at every `D`), and new
  cells appear only at interval edges.
- `(3/2, {2,3})` reproduces `[4/3, 17/3] + 6ℤ` (M1) exactly. Grade 3 at `3/2` is open; branching
  shifts exist for every `𝒫 ⊆` primes `≤ 13`.

**Residue targets (T6(a))** (`ResidueTargets.lean`, std3). `⌊z + ν + k⌋ = ⌊z + ν⌋ + k` makes
the divisor problem at `ν + k` the one-target-per-prime problem at `ν` (`hitsTargets_iff_shift`);
CRT reaches every target tuple (`exists_crt_shift`), so `(ν mod 1, ∏ ℤ/ℓ) ≅ ℝ/Mℤ`
(`hitsTargets_iff_exists_shift`); a certificate is a family of target theorems
(`hitsTargets_of_checked`). Bridge to `Z32.residue_not_eventually_constant`:
`not_eventually_modEq` (hitting targets forbids capture at residues missing them). Instances:
the `ν = −1` column = floor sequences hitting residue 1 (3/2, 4/3 with `{2,3}`; 6/5, 5/2 with
`{2,3,5}`); `⌊ξ(3/2)ⁿ⌋ mod 770` never eventually a unit, for every real `ξ ≠ 0`. Exact
certificates for target *sets* (several residues per prime) need a `succList` filter change: not done.

**Entropy ledger ⇒ dimension of real avoiders (T6(b))** (`EntropyBound.lean`,
`EntropyAtlas.lean`, std3).
- `EntCert`: a subset automaton over the hull vertices (state 0 = all, closed under
  `succList`) plus integer weights `w` and a ratio `a/b` with `b·Σ_letters w(target) ≤ a·w(state)`
  (Collatz–Wielandt: `a/b ≥ λ_det`), checked by `decide +kernel`. This is the Lean meaning of
  `λ_det`; no Perron–Frobenius. `EntCert.dcount_le`: `b^L·#paths_L ≤ a^L·w_i`.
- `cword_mem` (real avoiders are automaton words, via `sound`), `xs_add_eq_runX` (`x_{N+L}` is
  `x_N` run along the carry word), `upperBoxDim_avoiders_le` (bounded pieces), and
  `dimH_eventually_avoids_le`: `dim_H {ξ : xₙ eventually avoids 𝒫} ≤ log(a/b)/log(p/q)`.
- Instances at `(3/2, ν = 0)`, all uncertified: `{2,5}` ≤ 7/10 (`D = 2`, 10 states,
  `λ_det` = plastic number 1.324718), `{2,5,7}` ≤ 12/25 (`D = 2`, 32 states, 1.210608), `{2,7}`
  ≤ 5/8 (`D = 8`, 40 states, 1.285199). Generator: `DubC2/entemit.py` (full hull from all
  vertices, no peeling). `{2}` has `λ_det → 3/2`: the bound is the vacuous 1, as it must be.

**Rank-depth first-hit bound (T4(a), M2 half)** (`FirstHit.lean`, `FirstHitAtlas.lean`, std3).
- `window_bound`: if `xₙ` avoids the divisor set on `[N, N+L]`, then
  `N + L ≤ γ^(R+1)(N + J + (R+1)(|det| + K(ξ) + 1)) + J + 1`, with `γ = 1 + log_q(p/q)`
  ([Oda26] Thm 27's factor), `R` = rank of the root det state (`Cert.depth`), and
  `K(ξ) = log_q(|ξ|+1) + max(0, −log_{p/q}(|ξ|(p/q−1)))` (`Params.kξ`; the second term is the
  small-`|ξ|` end and vanishes once `|ξ|(p/q−1) ≥ 1`). `first_hit_rank`: a hit in
  `[N, bound + 1]`. The exponent is the rank depth, not the vertex count.
- Proof: `rank_bound` is the compounding over constant-rank stretches (pure; any rank-monotone,
  rank-deterministic sequence); `le_of_escape` puts both branches of `Z32.escape_endgame` into
  `e ≤ γ·u + K`; `WinPath`/`win_*` are the peel and det-path lemmas on a finite window.
- `FirstHitAtlas.lean`: the 16 atlas cells with `J`, `|det|`, `R` read off by `rfl`, e.g.
  `(3/2, ½, {2,5})`: `J = 6`, `|det| = 7`, `R = 3`. `R` ranges 0–215 and is between 2/7 and
  5/6 of `|det|` (the generator's rank is a height on the det condensation, not minimized).

**Concrete cells** (`FollowerCheck.lean`, `FollowerAtlas/`, std3).
- `rstep_prodR` is the CRT correspondence: for pairwise coprime `PM` with product `M`, the
  mod-`M` residue step of a product set is the product of the per-prime steps of `xfrontier.py`.
- `checkF` is a kernel-decidable check: a search tree of encoded states (one mask per prime,
  endpoints over `Q`) with SCC labels. Labels may not increase along an edge, and at most one
  letter may keep a node's label. `checkF_sound` gives that `F` is finite, its endpoints lie on
  `(1/Q)ℤ`, and nothing branches. `exists_checked_of_checkF` gives a certificate at `D = Q` that
  is never built.
- `xfcheck.py --emit-dir DubC2/FollowerAtlas` emits 7 frontier cells (4328–13610 states; one file
  per cell in a linear chain; 1–3 min each; peak 6.6 GB). Each has a divisibility theorem and a
  `_T5iv` theorem.
  - New: `7/5` at `ν = 0` with `{2,3,7,11,13}`, `{2,3,5,11,17}`, `{2,3,7,11,17}`; `5/4` at
    `ν = 0` with `{2,3,7,11,17}`; `5/4` at `ν = −1` with `{2,3,5,7,11,13}`.
  - Re-checked: [Oda26] Thm 1 and [DN05] Thm 1.

**Mirror N-1** (`Mirror.lean`, std3). The substitution `(ξ, ν) ↦ (−ξ, 1 − ν)` turns `xₙ` into
`−xₙ`, except when `ξ(p/q)ⁿ + ν` is an integer, which happens only finitely often
(`eventually_fract_ne`). Hence `DubC2.Mirror.frequently_mirror_iff`: for any sign-symmetric
predicate, "infinitely often" holds at `ν` iff it holds at `1 − ν`, so a divisor set is
unavoidable at `ν` iff it is at `1 − ν`. Corollaries: `divisor_set_mirror_of_checked` (every
checked cell at `a/b` also holds at `1 − a/b`), `six_fifths_two_three_five_mirror` (`{2,3,5}` at
`6/5` on `[5/3, 2] + 30ℤ`), and `Pseudo.mirror` for pseudo-orbits with no `yₙ = 0`.

**General reduction (any base).** For coprime `p > q ≥ 2` and any finite set `𝒫` of primes each
dividing `pq`, the orbit eventually avoids `𝒫` iff the carry letters eventually do, i.e. are
coprime to `∏𝒫` (`DubC2.Schema.eventually_avoids_iff`, `isCoprime_prod_iff`); hence
`frequently_dvd_of_letters`: unavoidability follows once every such letter word is eventually
periodic. `carry_window` gives the alphabet `(−q−(p−q)ν, p−(p−q)ν)`.

`ShiftSchema.lean` (std3, no certificate data): `{2,3}` is unavoidable for `⌊ξ(3/2)ⁿ + ν⌋` at
**every real `ν ∈ [4/3, 17/3] + 6ℤ`** (`DubC2.Schema.three_halves_two_three_circle`), and for
`⌊ξ(4/3)ⁿ + ν⌋` at `ν ∈ [3/2, 2] ∪ [5, 11/2]`. Also `{2,5}` at `5/2` for `ν ∈ [8/5, 5/3] ∪ [8/3, 41/15] + (10/3)ℤ`
(`five_halves_two_five`) and `{2,3,5}` at `6/5` for `ν ∈ [−1, −2/3] + 30ℤ`
(`six_fifths_two_three_five`). Mechanism: when every prime of `𝒫` divides `pq`
("residue-free"), avoidance only says that the carries are prime to `∏𝒫`, and the certificate becomes
a one-dimensional open system on `y`. Drivers: `xschema.py` (fixed `𝒫` along a column of bases)
and `xresfree.py` (exact `ν`-sweep of a residue-free cell: GenCert verdict + word growth). Data:
`data/transform/`. Record: `plans/note-dubC2T-M0.html`.

## References

* **[DN05]** A. Dubickas, A. Novikas, *Integer parts of powers of rational numbers*,
  Math. Z. **251** (2005), 635–648. — Lemmas 1–2 (§2), Thm 1, Thm 4(ii),(iii) (§6).
* **[FS67]** W. Forman, H. N. Shapiro, *An arithmetic property of certain rational
  powers*, Comm. Pure Appl. Math. **20** (1967), 561–573. — the `{2,5,7,11}` floor answer.
* **[Dub09AA]** A. Dubickas, Acta Arith. **137** (2009). — the eventual form of Lemma 2,
  formalized here as `Z32.not_isEventuallyPeriodic_carry`.
* **[Nov12]** A. Novikas, *Composite numbers in the sequences of integers*, doctoral
  dissertation, Vilnius University, 2012 (supervisor A. Dubickas). — Ch. 1 = [DN05]; §1.6 is
  the shifted-integer-part lane; the Conclusions give its complete inventory (`{7,5/3,7/5}`
  at ν=½, `6/5` at ν=−1, `5/2` at ν=−1+30k), which does **not** contain `3/2` at ν=½.
* **[Oda26]** Y. Odagiri, *Finite graph certificates for composite terms in rational floor
  sequences*, Zenodo, doi:10.5281/zenodo.22997709 (2026). — prior art for the certificate
  method (unshifted floors at 7/5, 5/2, 5/3).
* **[PR19]** P. Philippon, P. Rath, *On two problems of Hardy and Mahler*, arXiv:1904.00590.
  — has a "closest integer to λαⁿ ≡ i mod b infinitely often" criterion, but for PV and
  Salem α only; empty at rational non-integer α.
* **[Kop20]** J. Kopra, TCS (2020). — the ×(p/q) trace subshift is not sofic, so no finite
  `G(P,K,D)` is ever exact; certificates are necessarily one-sided.
