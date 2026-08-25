# `SZ/` — Dubickas's sets `𝒮` and `𝒵`

The `𝒮`/`𝒵` landscape of

> [Dub06EO] A. Dubickas, *Even and odd integral parts of powers of a real number*,
> Glasgow Math. J. **48** (2006), 331–336.

`𝒵` is the set of real `α > 1` for which some nonzero real `ξ` makes **every** integral
part `⌊ξ αⁿ⌋`, `n ≥ 1`, even; `𝒮` is its complement in `(1, ∞)`.  At `α = 3/2` the
question "is `α ∈ 𝒵`?" is Mahler's, and open.

Plans: `plans/plan-dubD1.html` (the quadratic-Pisot slice) and `plans/plan-dubD1O5.html`
(the square-root slice; `√3 ∈ 𝒵` resolves [Dub06EO] Problem 3).  Notes:
`plans/note-dubD1-M1.html`, `plans/note-dubD1O5-G1.html`, `plans/note-dubD1O5-M1.html`,
`plans/note-dubD1O5-M2.html`.  Paper: `paper-dubD1O5.tex` (*Even integral parts of powers
of square roots*, 24 pp) — its Appendix A is the statement index into this directory.
Parent report: `plans/report-dubickas.html` §D.1, §D.2, §D.4, §D.6, §E.3.

⚠️  The corpus already uses **`[Dub06]`** in docstrings (`Bugeaud/Chapter3/*.lean`,
`TShift/CriticalBox.lean`) for a *different* 2006 Dubickas paper — *Arithmetical
properties of powers of algebraic numbers*, Bull. LMS **38**.  This root therefore writes
**`[Dub06EO]`**.

## Headline results

| theorem | statement |
|---|---|
| `SZ.silver_mem_MahlerZ` | `1 + √2 ∈ 𝒵`, witness `ξ = (2-√2)/4` |
| `SZ.floor_silver_pell` | `⌊ξ (1+√2)^{n+1}⌋ = Pell n - [2 ∤ n]` |
| `SZ.quadPisot_mem_S_iff` | the golden mean is the **only** quadratic Pisot number in `𝒮` |
| `SZ.dvd_floor_of_neg` | `a ≡ 0`, `b ≡ 1 (mod m)` ⟹ `m ∣ ⌊ξ αⁿ⌋` for every `n` |
| `SZ.mem_MahlerZ_of_three_le` | `[3, ∞) ⊆ 𝒵`, by an explicit even greedy |
| `SZ.golden_mem_S` | `φ ∈ 𝒮` |
| `SZ.sqrtThree_mem_MahlerZ` | **`√3 ∈ 𝒵`** — [Dub06EO] **Problem 3**, answered |
| `SZ.exists_digitA_eq_zero` / `..._digitB_eq_two` | lemma L1: the greedy's digit tails are canonical |
| `SZ.pick_residual_mem` | the Cover Lemma at `m = 3` ([Utz51], reproved) |
| `SZ.digitReal_two_eq_zero` | `K₂ = {0}` — the base-`2` degeneracy behind `2^{1/q} ∈ 𝒮` |
| `SZ.sqrtTwo_mem_S` | **`√2 ∈ 𝒮`** — the one `𝒮` cell of Theorem B (paper Prop. 2.3) |
| `SZ.sqrt_natCast_mem_S_iff` | **Theorem B**: for `m ≥ 2`, `√m ∈ 𝒮` ⟺ `m = 2` |
| `SZ.sqrtFive_mem_MahlerZ` … `sqrtEight_...` | the four cells `m ∈ {5,6,7,8}`, `𝒵 ∩ (2,3) ≠ ∅` |
| `SZ.Slice.pick_adm` | the cover lemma for an arbitrary base, modulus and digit alphabet |
| `SZ.Slice.exists_translate` | the translate exists whenever `p ≤ U` (paper Lemma 3.3) |
| `SZ.Slice.dvd_floor_of_uniform` | tail hygiene at `e = m-1`, any `p ≤ √m` (paper Prop. 5.4) |
| `SZ.exists_dvd_floor_sqrt` | **Theorem C**: designed `ξ` with `p ∣ ⌊ξ √mⁿ⌋` for all `n ≥ 1` |
| `SZ.exists_eventually_composite_sqrt` | …and those integral parts are eventually composite |
| `SZ.sqrt_mem_MahlerZ_of_four_le` | Theorem B's non-square cells `m ≥ 4`, by Theorem C at `p = 2` |
| `SZ.eq_intCast_of_even_floors` | rigidity: `⌊t 2ᵏ⌋` even for all `k` ⟹ `t ∈ 2ℤ` |
| `SZ.continuum_le_mk_witnessSet` | **the witness set for `√3` has cardinality `2^ℵ₀`** (paper Thm 9.1) |
| `SZ.exists_transcendental_witness_sqrtThree` | **Problem 3 has a transcendental witness** |

## Modules

```
Defs.lean             𝒵, 𝒮, tail closure; Mahler's question + [Dub06EO] Problem 5 stated
Trace.lean            rec2, its real realisation, the two seed patterns
PellDesign.lean       Pair, the exact floor identity, Theorem C, both conjugate-sign cells
Silver.lean           Pell, Theorem A, the explicit orbit, the {0,1} limit set
Tijdeman.lean         the even greedy and [3,∞) ⊆ 𝒵            (report §D.6)
QuadThm6.lean         S_n ≡ 2 (mod 6) and 1 + √3 ∈ 𝒵
GoldenS.lean          φ ∈ 𝒮
QuadraticDesign.lean  the composite corollary; 2+√5 and 3+√10   (report §D.4)
Classification.lean   IsQuadPisot, Theorem B, the Problem-5 consequence
DigitParity.lean      Lemma D: digit streams, the floor identity, base-2 degeneracy
SqrtTwo.lean          √2 ∈ 𝒮: base-2 rigidity                    (paper Prop. 2.3)
Slice.lean            the cover game at a general base and modulus p: rule, greedy,
                      reduction, translate                       (paper §3–§4)
SliceHygiene.lean     lemma L1 at e = m-1, any p ≤ √m            (paper Prop. 5.4)
Cells.lean            m ∈ {5,6,7,8}, and Theorem B assembled     (paper §6)
ThmC.lean             both branches of Theorem C + its table     (paper §7)
                      + Theorem B's m ≥ 4 cells by the printed proof
CoverGame.lean        the m = 3 cover greedy in ℤ[√3]; the Cover Lemma; lemma L1
SqrtThree.lean        √3 ∈ 𝒵 — [Dub06EO] Problem 3               (plan dubD1O5 §1.4)
CoverTree.lean        ALL plays of the cover game: paper Thm 9.1  (109 decls)
AxCheck.lean          120 `#print axioms` lines — all std3
checks/d1check2.py            R-6 second implementation, dubD1 experiment X1
checks/dubD1O5-x0-checks.py   dubD1O5 X0: the cover certificate and the first witness
checks/dubD1O5-x1-checks.py   dubD1O5 X1: the R-6 second implementation
checks/dubD1O5-x2-radicals.py dubD1O5 X2/X3: the q ≥ 3 frontier (negative)
checks/dubD1O5-x3-leanrule.py dubD1O5 X3/M2: the Lean selection rule, re-implemented
checks/dubD1O5-x4-paper.py    dubD1O5 X4/M4: companion check of paper-dubD1O5.tex
checks/dubD1O5-x5-tree.py     dubD1O5 X5: the admissible tree; paper Thm 9.1 + complexity
checks/dubD1O5-x6-cells.py    dubD1O5 X6: the four cells m ∈ {5,6,7,8} in ℤ[√m]
checks/dubD1O5-x7-thmC.py     dubD1O5 X7: the Theorem C table in ℚ+ℚ√m
```

## The two witnesses for `√3`

The translate equation `x - √3 y = 2√3 - 4`, `x, y ∈ K₃`, has a Cantor set of solutions,
so a witness is pinned only by a preference order.  `SZ/CoverGame.lean` formalises
*prefer `a = 0`, then prefer `b = 2`* — the rule that makes lemma L1 fall out of the region
structure — and produces

```
ξ = 1.3416089979611266516309894306526154258451…      ⌊ξ √3ⁿ⌋ = 2, 4, 6, 12, 20, 36, 62, 108, …
```

The X0/X1 scripts use an alternation-preferring first-fit rule and produce the different
witness `1.341665814942779748832194927978…`, which agrees on the first six floors and
parts company at `n = 7`.  Both answer Problem 3; the Lean one is the machine-checked one.

There are in fact `2^ℵ₀` witnesses — paper Thm 9.1, **machine-checked** in `CoverTree.lean`
(2026-08-21, std3, no cited axiom).  Off the overlap set `O` the cover dynamics is forced,
and its zone graph is `Z₂→Z₂`, `Z₃→Z₃`, `Z₁↛Z₄`, `Z₄↛Z₁`, so a play avoiding `O` forever is
eventually confined to one zone and sits at its fixed point — `0`, `3`, `3√3` or `3+3√3`,
all with `√3`-coefficient `≤ 3`, which the growth bound excludes (`gExists_inO`).  So every
reachable state branches again; hygiene (L1) is *scheduled* by the `Node` flags, since a
play that always takes `a = 2` is admissible and would violate it.  Hence uncountably many
witnesses are transcendental — while the arithmetic nature of the *named* one is out of
reach: its base-3 stream has full factor complexity `p(n) = 2ⁿ` (X5), so no
Adamczewski–Bugeaud criterion applies.

## Hygiene

Every declaration is `[propext, Classical.choice, Quot.sound]` or less.  No cited axiom, no
`native_decide`, no `sorry`.  Group keys: `dub06_sz_defs`, `dub06_sz_trace`,
`dub06_sz_design`, `dub06_d1_silver`, `dub06_d4_congruence`, `dub06_d6_tijdeman`,
`dub06_quadratic_classification`, `dub06_digit_parity`, `dub06_cover_game`,
`dub06_problem3_sqrt3`, `dub06_witness_tree`, `dub06_sqrt_two`, `dub06_slice`, `dub06_thmc`.

The Cover Lemma is **reproved**, not cited to [Utz51], so `SZ.sqrtThree_mem_MahlerZ`
carries no literature axiom.  The one `ref "Utz51"` in `CoverGame.lean` is an attribution
on a theorem proved in place.

`lean_lib SZ` is registered in `lakefile.lean` (build only).  `Extract.lean` `corpusRoots`
registration and the `theoremdb.json` regeneration are the user's call.

## Cross-check

`python3 SZ/checks/d1check2.py` (~1 min, exact arithmetic, no floats, no repo imports).
Independent of `plans/dubD1-x0-checks.py` in both code and representation.

`python3 SZ/checks/dubD1O5-x3-leanrule.py` (~20 s) re-implements `SZ/CoverGame.lean`'s
selection rule from scratch: it asserts the cover invariant at 2000 steps, pins 40 exact
decimals of the witness, and certifies that `⌊ξ √3ⁿ⌋` is even and unambiguous for
`n = 1, …, 1000`.

`python3 SZ/checks/dubD1O5-x4-paper.py` (~2 min) is the companion check of
`paper-dubD1O5.tex`: it produces both witness tables, verifies the cover gap conditions
for every `(p, m)` with `p ≤ 8`, `m < 200`, and confirms the structural facts the paper's
§4–§5 rest on.

`python3 SZ/checks/dubD1O5-x5-tree.py` (~30 s) checks the paper's §9: the tree of Thm 9.1
is fully binary to depth 10 with every segment closing within 12 steps, the listed
survivors never branch, 20000 random states escape within 11 steps, and the a-stream has
`p(n) = 2ⁿ` for `n ≤ 11` over 60000 digits.

`python3 SZ/checks/dubD1O5-x6-cells.py` (~1 min) checks the four cells in exact integer
arithmetic in `ℤ[√m]`: gap conditions and translate, cover invariant and digit alphabet at
each of 2000 steps per cell, all 25 published decimals of the four witnesses reproduced,
floors even and determined for `n ≤ 200` — and, the point of the exercise, it computes the
closed-form rule of `Slice.lean` **and** the abstract description of the paper's Remark 5.1
("smallest admissible `a`, then largest `b`") independently, and asserts they pick the same
offset at every step.

`python3 SZ/checks/dubD1O5-x7-thmC.py` (~10 s) is the same exercise for Theorem C, in
exact arithmetic in `ℚ + ℚ√m`: for each row of the paper's §7 table it checks the branch
hypotheses, re-derives `m > p²` on branch (ii), checks the two gap conditions, computes
the translate of Lemma 3.3 and recovers the published `j`, asserts the cover invariant and
the alphabet `{0, p, …, e}` at 2000 steps, reproduces all 20 published decimals of `ξ` and
the six printed integral parts, and certifies `p ∣ ⌊ξ √mⁿ⌋` determined for `n ≤ 200`.  The
`(p, m) = (3, 7)` row of Remark 7.1 — below the hygiene threshold, where the construction
runs but Prop. 5.4 does not apply — goes through the same checks.
