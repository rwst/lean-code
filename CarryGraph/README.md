<!--
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 (public domain).
-->

# CarryGraph — finite labelled digraphs behind integer parts of powers

Root of `plans/plan-carry.html`. One object, the **carry graph**

```lean
structure CarryGraph (V A : Type*) where
  succ : V → A → Finset V
```

a finitely branching digraph with arcs labelled by the carries `s` of
`q·x_{n+1} = p·x_n + s`. This directory holds its theory in Lean and a book about it.
The Lean files depend only on Mathlib and ForMathlib and never mention certificates. The
per-problem bridges (DubC, DubC2, Z32, Oda26) live in the sibling root `CarryBridge/`.

## Build

```sh
LEAN_NUM_THREADS=3 lake build CarryGraph.Basic   # one module at a time
make                                             # the book -> _build/book.pdf
```

## Status

| milestone | content | state |
|---|---|---|
| M0 | gates G-0 (first half), G-1, G-4, G-6; lakefile; `Basic.lean`; book skeleton, `ch00` draft | done 2026-10-11 |
| M1 | `Path, Reach, Rank`; `CarryBridge/DubC.lean` (rank/peel/ladder part); `ch01`, `ch02`; `AxCheck` both roots | done 2026-10-11 |
| M2 | `Core, Growth, Horseshoe, ZeroEntropy`; `CarryBridge/DubC.lean` (zero-entropy and core part); `ch03`, `ch04`; decidable witness predicates | done 2026-10-11 |
| M3 | `Labelled, Language, Follower, Shift`; `CarryBridge/Oda26.lean`; `ch05` | done 2026-10-11 |
| M4 | `Splitting, Quotient, Product`; gate G-2 (subdivision); `CarryBridge/DubC.lean` (right cover), `CarryBridge/Oda26.lean` (all finite word graphs); `ch06` | done 2026-10-11 |
| M5 | `Cover, Dimension, Affine, Interval`; transfer theorems; generic dimension bound; affine family (residue, block, cell, hull graphs); `ch07`, `ch08` | done 2026-10-11 |
| M6 | `CarryBridge/DubC2.lean`, `CarryBridge/Z32.lean`; gate G-3 (follower automaton); worked examples in `ch08`, bridge table in `appA` | done 2026-10-11 |
| M7 | audit: `AxCheck` both roots complete (537 = 424 + 113, std3), no `sorry`/`native_decide`/`maxHeartbeats`, lines ≤ 100; gate G-5 (kernel cost); `CG/` retired (lean_lib entry removed, archive in `old-plans/`); `appA` file map, `appB`, index; full `latexmk` build (67 pp.) | done 2026-10-11 (the directory `CG/` itself still to be removed by hand) |
| M8 | `Flow.lean` (circulations, flow on cycles, zero-entropy decomposition, generic balance lemma); `CarryBridge/Z32Balance.lean`; `ch09`; overview numbered Chapter 0 so printed numbers match the file names | done 2026-10-11 |
| deferred | the M6 deferred bridge items: DubC2 peel chain + det simulation + cycle certificate, `checkF` rank, horseshoe/branch witnesses, Z32 escape/schema/transversal/type certificates, `RealizesInf` (counterexample + strict theorem), mirror, `Cover.lineGraph` | done 2026-10-11 |

## Files

| file | contents | book |
|---|---|---|
| `Basic.lean` | `CarryGraph`, `Adj`, `under`, `out`, `ofRel`, `ofFinset`, `arcs`, `reverse`, `restrict`, `relabel`, `forget`, `Hom` | ch. 1 |
| `Path.lean` | walks, infinite paths, `Reads`/`IsWord`/`ends`, `words`, `npaths`, right-resolving and functional graphs (`Functional.iPath_eq`), Kőnig `exists_walk_of_forall_hasWalk` | ch. 1 |
| `Reach.lean` | `Reach`, `SameSCC`, `Cyc`, `ReachIn`, balls and the computable `reachSet` (stable within `|V|` rounds; `Reach` decidable), `desc`/`preds` and their duality, homomorphisms preserve cycles, geodesic Kőnig `exists_injective_walk_of_infinite_reach` | ch. 2 |
| `Rank.lean` | `IsRank`, `IsLRank`, `NoBranch`; soundness/completeness (finite and finite-reach infinite `V`), `IsRank.evPer`, `IsLRank.evPer`, peel ranks (forward and reversed), core form ⇒ no branching, rank depth | ch. 2 |
| `Core.lean` | `fwd`, `bwdIn`, `core`, `Essential`; core = largest essential set; `two_stage`; computable forward peel `peel` (`v ∈ peel k` ⟺ a walk of length `k`; stable within `|V|` rounds); escape depth `hasWalk_card_iff`; computable `coreSet`; `core_eq_empty_iff`; functional cores ⇒ simple cycles | ch. 3 |
| `Growth.lean` | `arcsFrom`, `PolyGrowth`, labelled-rank polynomial bound, branching doubling, `polyGrowth_or_exp`; `ntot`, `entropy` (`expGrowthSup`), `entropy_le_zero_iff`; eigenvector brackets `IsSuperEigen`/`IsSubEigen` with `entropy_le_of_superEigen`, `log_le_entropy_of_subEigen` | ch. 4 |
| `Horseshoe.lean` | labelled walks `IsLWalk`; `card_le_npaths` (distinct walks are counted by `npaths`); `Horseshoe` (rose of closed walks), block paths, full-shift embedding, `|ι|^k ≤ npaths`, `log |ι| / L ≤ entropy`, aperiodic path; `exists_horseshoe_of_branch` | ch. 4 |
| `ZeroEntropy.lean` | `zeroEntropy_tfae` (six faces: labelled rank, `LNoBranch`, `AllEvPer`, `PolyGrowth`, `entropy ≤ 0`, `SimpleCycles`); unlabelled `noBranch_tfae` via `forget`; `Decidable` instances for the witness predicates | ch. 4 |
| `Labelled.lean` | `EvPer`, `AllPer` (label form); state form ⇒ label form for any label type (`lnoBranch_isLRank_ncard`); equal on right-resolving graphs; computable subset construction `det : CarryGraph (Finset V) A`; Kőnig lift `exists_iPath_of_det`; `determinization` TFAE with growth, entropy and word-growth legs; `tube53_separates`, `diamond_separates` (`decide`) | ch. 5 |
| `Language.lean` | `langFrom`, `PrefixClosed`, `Sofic`; `toNFA` and `toDFA_evalFrom_toNFA` (`det` = Mathlib `NFA.toDFA`); `sofic_of_finite_reach` (infinite `V`); `sofic_iff_isRegular_and_prefixClosed`; `sofic_iff` via Mathlib Myhill–Nerode | ch. 5 |
| `Follower.lean` | `followerGraph` on all languages; presents every prefix-closed language; sofic ⟺ finite reach; `toFollower` (Moore quotient as a `Hom`); minimality bounds `|V|` (right-resolving) and `2^|V|`; `exists_injective_of_not_sofic` | ch. 5 |
| `Shift.lean` | `blockWords`, `isLanguage_blockWords`, `labelShift` (ForMathlib `ofLanguage`), `language_labelShift`, bi-infinite paths in the shift and in the core; `rauzy` with `under_rauzy` = ForMathlib `Step` | ch. 5 |
| `Splitting.lean` | `RightCover` (path counts; entropy, zero entropy, `core = ∅` with sinks off `U`); `inSplit`, `outSplit` (`sum_npaths_outSplit`: copies carry `|C|`× the paths); `lineGraph` (`ntot_lineGraph`: paths shifted by one) and the shift invariance `expGrowthSup_shift`; invariance of entropy, `LNoBranch`, `core = ∅` under all three | ch. 6 |
| `Quotient.lean` | `Hom.mem_core`, `Hom.core_eq_empty`, the rung `cyc_mem_of_peelRank_of_hom`; locally injective homs (`Hom.npaths_le`, entropy, zero entropy); simulations (`IsSimulation.exists_iPath`, `allPer_of_simulation`); word graphs `WReads`/`WCovers`/`WAllPer`/`WNoBranch`; **subdivision** `subdivide` with the four G-2 lemmas and `wAllPer_iff_det` | ch. 6 |
| `Product.lean` | `labelProduct`, `piProduct`; languages intersect, `Sofic.inter`; soundness from one factor; `detStep_labelProduct`/`detStep_piProduct` (the CRT step); `entropy_labelProduct_le` (≤ sum; ≤ left factor if the right one is right-resolving), `lnoBranch_labelProduct`, word counts ≤ min; monotonicity in the index set | ch. 6 |
| `Cover.lean` | systems (`run`, `Follows`, `orbit`, `AdmForever`), `Cover`, `Realizes`, `RealizesInf`; shadowing `Cover.follows`/`Cover.exists_iPath`; `Cover.mono`/`comap`/`map`/`ofSimulation`/`labelProduct`/`piProduct`/`det`; transfer: `evPer_of_allPer`/`_lnoBranch`/`_det`, `not_allPer`, **`not_allPer_of_horseshoe`** (a realised horseshoe kills every cover), `escape_of_peel`, `escape_of_core_empty`; itinerary counts `ncard_orbitLang_le`, `orbitEntropy_le`, `orbitEntropy_eq` (exact right-resolving covers) | ch. 7 |
| `Dimension.lean` | `Cover.externalCoveringNumber_le`, `Cover.upperBoxDim_le`, `Cover.dimH_le` (dimension ≤ entropy / log λ), `edist_le_of_follows`, `Cover.upperBoxDim_le_of_expanding` | ch. 7 |
| `Affine.lean` | `affStep`, `carry`, carry/fractional recurrences, `carry_window`, `carry_bounds`; `affAdm`; `residueGraph` + `cover_residueGraph`; `blockGraph`, `cellGraph`, `cover_blockGraph` (via the fractional system and `Cover.comap`), `affine` = residue ⊗ cell, `cover_affine`; `realizes_blockGraph` (Markov block graphs are exact); refinement homs `blockGraph_hom`, `cellGraph_hom`; **`dimH_avoiders_le`** (generic `DubC2.Gen.dimH_eventually_avoids_le`) | ch. 8 |
| `Flow.lean` | `outflow`, `inflow`, `IsCirculation`, `flowSupp`; support essential ⊆ core; **`reach_of_pos`** (flow runs on cycles), `eq_zero_of_not_cyc`; `noBranch_perm` (zero entropy ⇒ weighted simple cycles); `visits`/`transits` marginals; **`exists_circulation_of_walk`** (balance lemma), `exists_circulation_avoiding` | ch. 9 |
| `data/tube53_k3.txt` | arcs of the 5/3 tube (`tubeArcs`), moved from `CG/data/` | ch. 5 |
| `Mirror.lean` | `allPer_iff_of_adj_equiv`; `blockArc_mirror`, `cells_rev`, `adj_cellGraph_mirror`, `resOK_neg`, `adj_residueGraph_mirror`, `adj_affine_mirror`, `allPer_affine_mirror_iff` (the label form is invariant under `ν ↦ 1 − ν`) | ch. 8 |
| `Interval.lean` | `blockHull` over `ν ∈ [ν₀, ν₁]`, `adj_blockHull_iff` (hull = union), `cover_blockHull`/`cover_affineHull` for every real `ν` in the interval, `blockHull_mono`, `residueGraph_hom`, `allPer_affine_mono`, `carry_window_of_interval`, `dimH_avoiders_le_hull` | ch. 8 |
| `AxCheck.lean` | `#print axioms` for every theorem (generated) | — |
| `book.tex`, `ch00`–`ch09`, `appA`, `appB`, `carry.bib`, `Makefile` | the book | — |

## Gate log (M0)

* **G-0, first half: pass.** `Basic.lean` builds std3. The unlabelled theory of `CG/` applies to
  `X.under` with no rewriting: `CG.zeroEntropy_tfae (adm := X.under)` elaborates as is.
  Deviation from the plan: the structure carries **no** `[DecidableEq V]` parameter. It is
  assumed per lemma, which `Finset V` allows.
* **G-1, König: pass, bespoke.** `HasWalk X v n` (recursive) and a direct pigeonhole proof of
  "arbitrarily long walks from `v` ⇒ infinite walk from `v`", 25 lines, valid for infinite `V`.
  Mathlib's `Order/KonigLemma` needs a strongly atomic order or an inverse system. Either
  wrapper is longer than the direct proof, so it is not used.
* **G-4, label product = affine: pass, with equality.** On all 16 cells of `DubC2/Atlas`,
  `Params.succList` was compared by exact rational arithmetic (`/home/ralf/math/.venv`) with
  the label product of two graphs: the residue graph `r →s r'` with `q·r' ≡ p·r + s (mod M)`,
  restricted to residues and letters prime to `PM`/`Pq`, and the cell graph
  `c →s c'` iff `(p·[c,c+1)/D − (p−q)ν − s)/q` meets `[c',c'+1)/D`. Arc sets agree at every
  `(k, s)`: 0 mismatches over 30 310 arcs. `affine_eq_labelProduct` is therefore an equality
  and not just an inclusion.
* **G-6, book toolchain: pass.** `make` (latexmk/pdflatex, `amsthm`, bibtex, `alpha` style)
  builds 29 pages with no warnings.

## Gate log (M1)

* **G-0, second half (SCC and rank part): pass.** Porting `CG/SCC.lean`, the rank part of
  `CG/ZeroEntropy.lean`, `DubC.eventually_periodic_of_rank` and `DubC.transGen_self_of_rank`
  needed renames only (`adm` ↦ `X.under`), plus two local changes:
  `Nat.sInf_mem` ↦ `Nat.find` (import), and `[Finite V]` ↦ "finite reach set of the walk",
  which generalises the theorem to infinite carry graphs. No representation change. The growth
  half of `ZeroEntropy` is ported in M2.

## CarryBridge (M1)

`CarryBridge/DubC.lean`: `digitGraph a M` (arcs `r →[d] a·r + d` between units),
`under_digitGraph : under = DubC.Step`, `certOK_iff_isRank`, `certOK_iff_isLRank` (`a ≤ M`),
`certOK_iff_noBranch`, `coreClosed_iff`, `projHom` (reduction mod `M' ∣ M` as a carry-graph
homomorphism). The following are re-derived from the generic theorems:
`digits_eventually_periodic_of_certOK'`, `infinite_composites_floorPow_of_certOK'`,
`coreClosed_of_rankOn'`, `coreClosed_of_rankRevOn'`, `coreClosed_of_ladder'`,
`noBranch_of_coreCert`, `exists_certOK_of_coreCert`. The core, growth and splitting parts of
`CG/BridgeDubC.lean` follow in M2 and M4. All files build with no warnings, and every theorem
uses only std3 axioms (`CarryGraph/AxCheck.lean`: 96, `CarryBridge/AxCheck.lean`: 16).

## Gate log (M2)

* **G-0 closed: the representation holds.** The growth half of `CG/ZeroEntropy.lean` and all of
  `CG/Core.lean` were ported. The proofs are unchanged modulo `adm ↦ X.under`, with one
  deliberate upgrade. The theory is now **labelled**: `npaths` counts labelled paths, the
  six-face theorem is about `IsLRank`/`LNoBranch`, and the unlabelled theorem is its
  specialisation to `X.forget` (`noBranch_tfae`). The (3 ⇒ 2) step now goes through the generic
  horseshoe (`Horseshoe.exists_not_evPer`) and not through an ad-hoc two-loop construction.
* **Import order deviation.** `Horseshoe` comes before `ZeroEntropy`
  (`Core → Growth → Horseshoe → ZeroEntropy`), because the aperiodic-path face of the six-way
  theorem uses the horseshoe. The plan's DAG has been updated.
* **Entropy in `EReal`** (the plan's "verbose bounds" risk): manageable. The one analytic lemma is
  `expGrowthSup_poly_le` (≈30 lines, via `tendsto_pow_const_div_const_pow_of_one_lt`). Both
  brackets reduce to ℕ inequalities plus one `ENNReal` division step. No `entropyReal` was
  needed.
* **Decidability.** `decide` checks the witness predicates on small graphs. On the golden-mean
  graph, `IsSuperEigen ![8,5] 13 8` and `IsSubEigen ![8,5] 8 5` give `entropy ≤ log (13/8)`
  with no hand computation, and `coreSet` is computed by `decide`. Instance search needs the
  five-binder bodies of `IsLRank`, `LNoBranch` and `Functional` supplied by hand (`have`).
* **Not done (stated in the book only):** `entropy_eq_sup_scc` ([LM95] Thm 4.4.4), `sccPeriod`
  ([BJG09] §10.5), `adjMatrix` with its Mathlib `Matrix` bridge, and Perron–Frobenius (D-4).
  None of these is used later.

## CarryBridge (M2)

`CarryBridge/DubC.lean` now imports `CarryGraph.ZeroEntropy` and `DubC.Verdict`.
New: `certOK_iff_polyGrowth`, `certOK_iff_entropy` (unlabelled subshift),
`certOK_iff_allEvPer`, `certOK_iff_entropy_labelled` (`a ≤ M`), `coreClosed_core`,
`coreClosed_of_core_subset`, and the instances `noBranch_six_thirty`,
`noBranch_not_coreDet_four`. This finishes the `CG/BridgeDubC.lean` port except the
splitting part (`step_rightCover`, `certOK_full_iff_reduced`, M4). AxCheck: 179 + 24
theorems, all std3. Two `[propext, Quot.sound]` and one with no axioms.

## Gate log (M3)

* **Port of `CG/Labelled.lean` and `CG/Presentation.lean`: done, with simplifications.** The
  labelled theory of M2 removes the edge-graph detour: `AllPer X ↔ X.det.PolyGrowth` is now
  two TFAE steps, and the growth leg is stated on the words of `X` itself
  (`allPer_iff_wordGrowth`). `det` is a computable carry graph on `Finset V` (it was a `Prop`
  relation in `CG/`), so the det form of a small graph is checked by `decide`
  (`diamond_separates`). The state form ⇒ label form direction no longer needs a finite label
  type (`lnoBranch_isLRank_ncard`), so it applies to the `ℤ`-labelled tube and to Oda26 graphs.
* **Existing formalization reused (flag-existing): Mathlib Myhill–Nerode.** The follower set is
  Mathlib's `Language.leftQuotient`. `CG.sofic_iff` is now a corollary of
  `Language.isRegular_iff_finite_range_leftQuotient` through the new bridge
  `sofic_iff_isRegular_and_prefixClosed`, and not a separate proof.
* **File deviation.** The two-sided material (label shift, Rauzy graphs) is in a fourth file
  `Shift.lean` (`Language → Shift`), so that `Language`/`Follower` do not import topology.
  The plan's "edge shift" is `labelShift X core`; the edge shift proper is the special case of
  arcs labelled by themselves (book only). The converse "every point of the label shift labels a
  bi-infinite path" (compactness) is stated in the book only.
* **Not done:** `rauzy` for ForMathlib's `IsStronglyConnected`, and the minimal
  right-resolving presentation of an *irreducible two-sided* sofic shift ([LM95] Thm 3.3.18).
  The one-sided rooted minimality (`ncard_reach_le_of_rr`) is what the certificates use.
* **G-2 (subdivision): deferred to M4 as planned, fallback not needed for M3.** Every Oda26
  graph the corpus builds (`oneStep`, `oneStepU`, `gPrime`) is one-letter (`isSingle_*`), so the
  bridge needs no subdivision. Only `Oda.WG.contract`/`contractG` carry longer words.

## CarryBridge (M3)

`CarryBridge/Oda26.lean`: `toWG`, `ofWG`, `IsSingle`, `toWG_ofWG`, `reach_ofWG`;
`odaAllPer_iff` (Oda's `AllPer` = label form), `allCert_iff_det` (**[Oda26] Thm 21 for
one-letter graphs = the determinization theorem**: phase test on every SCC ⟺ `det` has no
branching), `allCert_iff_wordGrowth`; `odaProjHom` (Lemma 31 as a `Hom`), `allPer_of_proj`,
`allCert_oneStepU_iff`. AxCheck: 250 + 38 theorems, all std3 (four use a subset of std3: two
`[propext, Quot.sound]` and one `[propext]` in `CarryGraph/`, one `[propext, Quot.sound]` in
`CarryBridge/`; one with no axioms).


## Gate log (M4)

* **G-2, subdivision: pass, at the level of whole graphs.** For a finite word graph
  `E : Finset (V × List A × V)` with non-empty words, `subdivide E` (vertices
  `V ⊕ (E × Fin N)`) satisfies the four lemmas: `reads_subdivide_iff` (reads between old
  vertices = word-path concatenations), `allPer_subdivide_iff` (label form = `WAllPer`),
  `lnoBranch_subdivide_iff` (zero entropy = `WNoBranch`), `mem_langFrom_subdivide` /
  `sofic_wordLang`. Bridge: `Oda.WG.Covers G = WCovers F` for `G` with finite edge set `F`
  (`covers_iff_wCovers`), hence **[Oda26] Thm 21 for every finite word graph**
  (`allCert_iff_subdivide`: `AllCert G ↔ (subdivide F).det.LNoBranch`). This includes the
  contracted normal-form graphs whenever their run set is finite. The per-SCC form
  ("`Certified` on one SCC = phase on its subdivision") was not needed and is not stated.
* **Port of `CG/Splitting.lean`, `CG/Product.lean`: done, upgraded.** Right covers are
  *labelled* (bijection per letter). The DubC instance then needs no digit-collision lemma:
  `digitGraph_rightCover` holds for every `M'`, and `gcd(M', 14) = 1` enters only through
  `exists_unit_lift` (`certOK_full_iff_reduced'`, now about `(reducedGraph M').LNoBranch`).
* **New: out-splitting and line graphs** with entropy/zero-entropy/core invariance.
  `higherBlock X n` is not a separate definition. Higher block graphs are iterated
  `lineGraph`s, and each step preserves everything (book: `thm:linegraph`). The one analytic input is
  `expGrowthSup_shift` (Mathlib has no shift lemma for `expGrowthSup`).
* **Plan correction: `entropy_labelProduct_le (≤ min)` is false for path counts.** The
  one-letter loop times the two-vertex complete one-letter graph has entropy `log 2 > 0`.
  Proved instead: `≤ entropy X + entropy Y` (`entropy_labelProduct_le`), `≤ entropy X` if `Y` is
  right-resolving (`entropy_labelProduct_le_left`), and `≤ min` for *word* counts
  (`card_words_labelProduct_le`).
* **DAG deviation:** `Quotient` imports `Splitting` *and* `Follower` (for `Sofic`,
  `reach_iff_exists_reads`); `Product` imports `Quotient`.
* **Lean gotcha:** `inferInstance` fails for `DecidableEq (V ⊕ (↥E × Fin n))` although every
  component has an instance. `instDecidableEqSum` given explicitly works (`sdDecEq`).
  `if_pos`/`dif_pos` are deprecated in this toolchain (use `ite_eq_left`/`dite_eq_left`).

## CarryBridge (M4)

`CarryBridge/DubC.lean`: `reducedGraph M'` (digits `2, 4, 6` mod `M'`, labelled),
`digitGraph_rightCover`, `npaths_full_eq_reduced`, `exists_unit_lift`,
`certOK_full_iff_reduced'` (re-derives `CG.certOK_full_iff_reduced`). This finishes the port of
`CG/BridgeDubC.lean`. `CarryBridge/Oda26.lean`: `covers_iff_wCovers`, `odaAllPer_iff_subdivide`,
`allCert_iff_subdivide`. AxCheck: 353 + 51 theorems, all std3 or a subset of it (`CarryGraph/`:
one with no axioms, two `[propext, Quot.sound]`, one `[propext]`; `CarryBridge/`: five
`[propext, Quot.sound]`). Book: 53 pages, no undefined references.

## Gate log (M5)

* **G-4 (label product = affine)** passed at M0 with arc-for-arc equality. In Lean, `affine` is
  *defined* as `residueGraph ⊗ cellGraph`, so `affine_eq_labelProduct` is definitional. The
  statement that `DubC2.Gen.Params.succList` lists these arcs is the M6 bridge lemma.
* **Representation decisions.**
  - Letters are `Fin nA`, standing for the carry `s₀ + t`, and not `ℤ`. This gives `Fintype A`,
    which counting and dimension need, and it is exactly `DubC2.Params.letter`.
    `carry_window` gives a window of `p + q + 1` letters, and `carry_window_of_interval` gives one
    for a whole ν-interval.
  - The graphs take a rational `ν` (computable, decidable). The system takes a real `ν`. The hull
    covers every real `ν` in its interval.
* **Realisability lives in the fractional system.** In the affine (real `z`) system the carry
  depends on `⌊z⌋ mod q` (`q x' = p x + s`), so the cell graph alone is *not* exact there.
  `realizes_blockGraph` is stated for the fractional system `y ↦ (p y − (p−q)ν − s)/q`, under the
  Markov condition. The affine system reaches the block graphs through `Cover.comap Int.fract`
  (`fract_semiconj`).
* **`RealizesInf` is a hypothesis, not a theorem.** Nested *half-open* intervals can have an
  empty intersection, so infinite realisation for Markov block graphs needs closed intervals or
  an IVT argument (`Z32.Horse.exists_fixed`). That argument belongs with the Z32 bridge (M6).
  The obstruction theorem `Cover.not_allPer_of_horseshoe` takes `RealizesInf` as input.
* **New: one dimension theorem for every cover.** `dimH_avoiders_le` holds for *any* finite
  carry graph that covers the affine system, with bound `(entropy X / log (p/q)).toENNReal`.
  It is uniform over a ν-interval (`dimH_avoiders_le_hull`). The ForMathlib box-dimension API
  (`coveringGrowth_const_mul`, `upperBoxDim_eq_upperBoxDimWith`, `dimH_le_upperBoxDim`) was
  enough. Nothing new was needed in ForMathlib.
* **Renamed from the plan.**
  - `Cover.card_orbitLang_le` became `Cover.ncard_orbitLang_le`.
  - `Cover.entropy_orbitLang_le` became `Cover.orbitEntropy_le`.
  - `Realizes.le_entropy` became `Cover.orbitEntropy_eq`, which needs a right-resolving cover
    for equality.
  - `Cover.firstHit_of_rank` became `Cover.escape_of_peel`: the escape time is bounded by the
    peel index.
* **DAG deviation:** `Cover → Dimension → Affine → Interval`. `Affine` imports `Dimension` for
  `dimH_avoiders_le`.
* **Deferred to M6 (they are bridge material):**
  - `digitGraph` is already in `CarryBridge/DubC.lean`;
  - `blockGraph` = Z32 `hits` and `cover_of_refinement_tower` (the Z32 funnel; the generic
    refinement homomorphism is `blockGraph_hom`);
  - the mirror isomorphism ν ↦ 1 − ν;
  - `Cover.higherBlock`.
* **AxCheck:** 420 theorems, all std3 or a subset of it. Three use no axioms, four use
  `[propext, Quot.sound]` and two use `[propext]`. Book: 61 pages, no undefined references.

## Gate log (M6)

* **G-3 (follower automaton as a carry graph): passed.** `DubC2.Gen.Follower.FState` derives
  `DecidableEq`, and `folGraph P : CarryGraph FState (Fin nA)` (`succ X t = (step P X (letter t)).toFinset`)
  is a right-resolving carry graph on an infinite vertex type. Reachability from a valid state
  is `Follower.Reach` (`reach_folGraph_iff`), and `Branching` is labelled branching
  (`branching_iff`). The only arithmetic in this dictionary is `letter_mem`: from a valid state,
  every live letter lies in the window.
  - `exists_injective_path` factors through the generic geodesic Kőnig lemma
    `exists_injective_walk_of_infinite_reach` with no further arithmetic
    (`exists_injective_path'`).
  - `finite_of_checked` uses Kőnig plus **one** arithmetic lemma, `not_injective_of_periodic`
    (a periodic letter sequence cannot drive an injective follower path; affine contraction).
    It is re-derived as `finite_of_checked'`.
  - T5(iv) in carry-graph form is `checked_iff_finite'`: finitely many reachable vertices and no
    labelled branching among them. The converse construction `exists_checked_DF` stays in
    `DubC2/`.
* **Generalisation in `CarryGraph/`:** `cover_residueGraph` (and with it `cover_affine`,
  `cover_affineHull` and `dimH_avoiders_le_hull`) used to require primes in `Pq`. It now requires
  only `ℓ ∣ q` and `gcd(ℓ, p) = 1`, which is exactly DubC2's `ParamFacts.Pq`. Chapter 8 is updated.
* **New generic lemmas, used by the bridges:** `carry_bounds`, `Cover.ofSimulation`,
  `sofic_of_finite_reach` and `Functional.iPath_eq`.

## CarryBridge (M6)

`CarryBridge/DubC2.lean`:

* **The dictionary.**
  - `genGraph P := affine p q (a/b) sLo nA M D PM Pq` and `certGraph P` (arcs from `succList`) are
    isomorphic: `encHom`/`decHom`, with `mem_succList` and `adj_of_mem_succList`.
  - `cellArc_iff` is the cell arc in the certificate's integer form.
  - `rnext_val` is the residue step.
* **Checked certificates.** `certGraph_allPer` and `checked_allPer` give the label form.
  `checked_lnoBranch_det` is `C_det`, and `checked_polyGrowth_det` is `λ_det = 1`.
* **The generic divisor theorem.** `frequently_not_avoid_of_allPer`: if *any* cover of the affine
  system has the label form, then for every `ξ ≠ 0` infinitely many `⌊ξ(p/q)ⁿ + ν⌋` meet `P`.
  Its only arithmetic input is [DN05] Lemma 2. The carry window of a cell is `window`, and
  `cover_genGraph` is the cover.
* **Re-derived** (primed names, same statements):
  - `divisor_set_of_checked'`;
  - `divisor_set_of_checked_hull'`, through `cellHullHom`/`hullHom` (the hull check is a
    homomorphism `affineHull → genGraph`);
  - `DubC2.Gen.dimH_eventually_avoids_le'`. Here `entGraph E` is the automaton of an entropy
    certificate, which simulates `genGraph` (`entGraph_simulation`, then `Cover.ofSimulation`),
    and its weights form a super-eigenvector (`entGraph_superEigen`). The generic
    `dimH_avoiders_le` finishes the proof.
* **Pseudo-orbits.** `not_allPer_of_pseudoOrbit`: a pseudo-orbit with aperiodic letters rules
  out the label form of `genGraph P` for every `M` and `D`.
* **The follower automaton** (G-3, above) and the avoiding language.
  - `avoidLang P` is the language of `folGraphZ P` (`mem_avoidLang`).
  - `sofic_of_checked` follows from the generic `sofic_of_finite_reach`.
  - `avoidLang_mono'` comes from `shadow_isSimulation`, whose relation is the shadowing relation
    `Shadow`.
* **The residue automaton as an indexed label product.**
  - `resGraph` and `primeGraph` are the residue automaton and its per-prime factors;
    `adj_resGraph_iff_piProduct` reads one as the indexed label product of the others through
    the CRT map.
  - `rstep_eq_detStep` and `rstep_prodSet` are the subset step.
  - `rstep_prodR'` re-derives `DubC2.Gen.Follower.rstep_prodR`.

This ports every theorem of `CG/BridgeDubC2.lean` and `CG/BridgeProduct.lean` onto `CarryGraph`.
`CG/` is no longer needed by any bridge (D-6; deleted at M7).

`CarryBridge/Z32.lean`:

* `blkGraph c` is the graph on the distinct blocks, with arcs given by `hits`, and
  `mem_outEdges_iff` matches its arcs to `outEdges`.
* **Ranks and functionality.**
  - `isLRank_blkGraph`: `funcOk` *is* a labelled rank.
  - `functional_blkGraph`: with `strata = []` the graph is `Functional`.
  - `lnoBranch_blkGraph` and `allPer_blkGraph` follow.
* `isIPath_blocks` reads the funnel as an infinite path.
* **Re-derived:**
  - `Cert.not_confined'`: funnel, then `IsLRank.evPer`, then [DN05] Lemma 2. This replaces the
    bespoke rank-and-pigeonhole argument.
  - `card_modelLang_le_of_cert'`, by `Functional.iPath_eq`.
  - `not_cert_and_horse'`, by **counting alone**: `N^k ≥ 2^k` horseshoe words against at most
    one word per block. No growth rates are needed.

AxCheck: `CarryGraph/` 424 theorems and `CarryBridge/` 113, all std3 or a subset of it.
`CarryGraph/` has three with no axioms, four `[propext, Quot.sound]` and two `[propext]`.
`CarryBridge/` has eleven `[propext, Quot.sound]` and three `[propext]`.

**Not done at M6** (all done since, see "Deferred bridge items" below):
* the plan's `checked_imp_isRank_det` / `rounds_eq_peel`, which read the bitmask peel rounds as
  `CarryGraph.peel`, and `cycChecked_imp_isCycleCover`;
* `checkF_imp_isRank` for the `FollowerAtlas` trees;
* `horseOK_imp_horseshoe_realized` / `branchOK_…`. The DubC2 witness checkers build their
  pseudo-orbit *inside* the proof, so reaching it needs a split of `DubC2/Horseshoe.lean` and
  `Branch.lean`. `not_allPer_of_pseudoOrbit` is the generic half.
* the Z32 type certificates (`EntropyCert.TypeCert`), the schemas (`SchemaCertified`,
  `DepthKSchema`), the escape bounds and `CycleTransversal`;
* `RealizesInf` for Markov block graphs (Z32's IVT argument proves realisation for finite
  concatenations only);
* the mirror ν ↦ 1 − ν and `Cover.higherBlock`.

## Gate log (M7)

* **G-5, kernel cost of the generic checkers: measured.** Path graph `0 → 1 → … → n-1` with a
  loop at the end, rank `n-1-v`, `decide +kernel`, three threads, 12 GB watchdog (times without
  the ~1.1 s import load):

  | form of the check | n | time | peak RSS |
  |---|---|---|---|
  | `IsRank` unfolded (pairs and triples of vertices) | 20 / 40 / 80 | 0.5 s / 4.5 s / killed | 2.4 / 3.7 / >12 GB |
  | arc-local, `Finset`-valued `succ` | 100 / 300 / 1000 | 2 s / 26 s / killed | 3.5 / 9.7 / >12 GB |
  | arc-local `Bool` on `List`-valued successors | 1000 / 10 000 | 0.4 s / 2.5 s | 1.6 / 2.3 GB |

  The defining form costs `|V|^3`, about ×9 per doubling. `Finset` membership reduces slowly in
  the kernel (through `Multiset` quotients). Advice, now in `appB`: write the check as a `Bool`
  function on lists, prove once that it implies `IsRank`/`IsLRank`, and let the kernel evaluate
  only the `Bool` function, as DubC2 and Z32 already do. `decide` on the defining predicates is
  for examples with a few dozen vertices. No plan change (D-5).
* **D-6, `CG/` retired.** Nothing imports `CG.*`. Its `lean_lib` entry is removed from
  `lakefile.lean`, the remaining doc mentions of `CG.*` names are reworded, and the one data file
  the book cites is now `CarryGraph/data/tube53_k3.txt`. The whole directory (Lean files, gate
  drivers `g2tube.py`, `xsof.py`, `xsplit.py`, `data/`) is archived in
  `old-plans/CG-preliminary-2026-10-11.tar.gz`. The directory itself is still on disk: deleting
  it was refused by the permission check in this session, so it is left for the user
  (`rm -rf CG`). `plans/cert-graph.html` still describes `CG/` as it was.
* **Audit.** `AxCheck.lean` regenerated for both roots and unchanged: every `theorem` in the
  sources is listed (537), every module is imported. `lake build CarryGraph` (2625 jobs) and
  `lake build CarryBridge` (3346 jobs) are green with no warnings in either root. Eleven Lean
  lines over 100 characters were wrapped.
* **Book.** `appA` now has a file → chapter map in front of the bridge table. `appB` (what
  Mathlib and ForMathlib supply, what is missing, what is left out, kernel cost) is written. There
  is an index of the defined terms and the named theorems (63 entries), and the theorem titled
  "gate G-2" is now titled "subdivision". `make` builds 67 pages with no undefined reference and
  no overfull box above 3 pt.

## CarryBridge and gate log (M8)

* **`Flow.lean`** (21 theorems, std3). Circulations on the underlying digraph of a finite carry
  graph. The support is essential, hence in the core. **Every arc carrying flow lies on a cycle**
  (`reach_of_pos`: summing conservation over the set reachable from the head of the arc shows no
  flow enters it), so an acyclic graph carries only `0`. **At zero entropy** (`NoBranch`) a
  circulation is a weighted sum of simple cycles (`noBranch_perm`): the unique flow-carrying
  successor map is onto the support, hence a permutation of it, and the mass is constant along
  it. The **balance lemma** `exists_circulation_of_walk` is `Z32.exists_balanceVec` for an
  arbitrary walk in an arbitrary finite carry graph (Bolzano–Weierstrass on `[0,1]^{V×V}`).
  The general decomposition of a circulation into cycles ([BJG09] ch. 3) is stated in the book
  but not formalised.
* **`CarryBridge/Z32.lean`, balance part** (11 more theorems). `edgeGraph w` = `ofRel edgeOk`
  on `Fin (2^w)`. A `BalanceVec` is a circulation (`isCirculation_balanceFlow`), a trap is a
  nonempty essential set (`isTrap_map_iff`). Re-derived: `BalanceVec.isTrap_supp'`,
  `exists_balanceVec'` (via `toBalanceVec`, a mass-1 circulation read back as a balance vector).
  New for Z32: `BalanceVec.reach_of_pos` (every edge carrying balance flow lies on a cycle of
  the level-`w` graph) and `BalanceVec.mem_core`.
* **Book.** `ch09-flows.tex` written and included (circulations, flow on cycles, zero-entropy
  decomposition, balance lemma, the `3/2` density problem and why the flow criterion is vacuous).
  The overview is now Chapter 0 (`\setcounter{chapter}{-1}`), so printed chapter numbers equal
  the file numbers that the Lean docs cite. Literal chapter numbers in `appB` replaced by
  `\ref`. `Lag90` added to `carry.bib`. 71 pages, no undefined reference, no overfull box above
  3 pt.
* AxCheck: `CarryGraph/` 445, `CarryBridge/` 124, all std3 or a subset.

## Deferred bridge items (done 2026-10-11)

All items logged as "not done" at M6 are now in Lean, std3. AxCheck: `CarryGraph/` 464,
`CarryBridge/` 173 (162 in `AxCheck.lean`, 11 in `AxCheckBalance.lean`: `Z32.BalanceVectors` and
`Z32.CertComplete` both declare `Z32.cycleDenom_cast`, so the balance bridge moved to its own
file `Z32Balance.lean` and has its own audit file).

**Generic additions (`CarryGraph/`).**
* `IsPeelChain`, `IsPeelChain.walk_mem`, `IsPeelChain.core_subset` (Core): what a certificate's
  rounds are. They are *not* `peel`: a round keeps vertices with a successor *and* a predecessor
  witness, so the plan's `rounds_eq_peel` is replaced by "the rounds form a peel chain".
* `allPer_of_peelChain` (Quotient): peel, then simulate by a graph with the label form.
* `Functional.exists_period_of_walk` (Core): a walk in a finite functional graph repeats within
  `|V|` steps (no length hypothesis needed).
* `exists_iPath_of_forall_reads` (Labelled): Kőnig for a fixed label sequence, through the subset
  construction.
* `Reach.restrict` (Reach), `Cover.lineGraph` (Cover; higher block covers by iteration).
* `realizesInf_blockGraph` (Affine) under a **strict** right Markov condition, and
  `not_realizesInf_doubling`: the non-strict statement is **false** (`y ↦ 2y − s` on `[0,1)`,
  the constant path `1` needs the fixed point `1`).
* `Mirror.lean`: the affine graphs at `ν` and `1 − ν` are isomorphic up to relabelling.

**DubC2 (`CarryBridge/DubC2.lean`, `DubC2Witness.lean`).**
* `checked_isPeelChain`, `checked_round_core`, `detGraph`, `checked_isLRank_det`,
  `checked_detSim`, `checked_detTot`; `certGraph_allPer'` re-derives the label form from the
  certificate's own two parts (no `Gen.isEventuallyPeriodic_of_path`).
* `keepGraph`, `checked_keepGraph_functional`, `cycChecked_cyc_listed`: a cycle certificate is a
  peel rank (rank `0` on listed states, potential `+ 1` elsewhere) on the rank-keeping part.
* `checkF_isLRank`: the tree label is a labelled rank of the follower automaton on the reachable
  states; `not_branching_of_checkF'`, `exists_checked_of_checkF'` (any `D`, via
  `checked_iff_finite'`).
* `exists_pseudoOrbit_of_horseOK`, `not_allPer_of_horseOK`, `not_checked_of_horseOK'`;
  `exists_iPath_of_branchOK`, `not_allPer_of_branchOK`, `not_checked_of_branchOK'`.  The
  constructions are repeated in the bridge rather than split out of `DubC2/Horseshoe.lean` and
  `Branch.lean`: those files are imported by `Follower.lean`, so editing them would rebuild the
  kernel-checked `HorseshoeAtlas` and `FollowerAtlas`.
* `window_mirror`, `divisor_set_mirror_of_checked'`: the mirror theorem from graphs alone (no
  orbit-level substitution, no count of integer hits).

**Z32 (`CarryBridge/Z32Cert.lean`, `Z32Type.lean`).**
* `Cert.exists_carry_period_le'`, `Cert.exists_escape_le'`: budget `|blocks|` from
  `Functional.exists_period_of_walk` on the block graph (`card_blk_le`).
* `rotGraph` (functional, `K + 2` ranks, letters = branch), `adj_rankAt`, `isIPath_ranks`;
  `isEventuallyPeriodic_carry_of_certifiedK'`, `not_confined_of_certifiedK'`,
  `exists_carry_period_of_certifiedK'` (budget `K + 2 = |V|`), `exists_escape_le_of_certifiedK'`.
* `Cert.eq_of_memI_block'` via `Functional.iPath_eq`; `Cert.ok_eq_false_of_infinite_hold'`,
  `Cert.ok_eq_false_of_infinite_cycles'`.
* `typeGraph` (right-resolving, letters `Fin 2`), `typeGraph_isSuperEigen`/`isSubEigen`,
  `entropy_typeGraph_le`, `le_entropy_typeGraph`, `exists_iPath_of_modelOrbit`,
  `exists_modelOrbit_of_isWord`, `card_modelLang_eq_words`.

**Book.** ch03 peel chains and functional walks, ch05 Kőnig for a fixed label sequence, ch06
"peel, then simulate", ch07 line-graph covers, ch08 realisability forever (with the
counterexample), the mirror section, the extended bridge paragraphs; appA rows.  77 pages, no
undefined reference, no overfull box above 3 pt.
