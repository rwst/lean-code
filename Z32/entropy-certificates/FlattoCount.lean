/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import FLP.Basic
import Bugeaud.Chapter3.ParityIdentity
import Z32.ModelEntropy
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Counting Mahler's Z-number candidates: Flatto's exponent and the horizon wall

**Status: WP0 stub.**  This file currently carries only the conventions note produced by WP0 of
`plans/plan-B10.html`.  The theorems (L1)–(L4), `T-B10.1` and `T-B10.2` are WP2's deliverable and
are not yet present.

Target contents (WP2):

* (L1)–(L4), the four-lemma core of plan-B10 §2.2;
* **T-B10.1** the horizon-`k` Z-candidate count satisfies `Z k ≤ 3 * (3/2)^k`, hence
  `#{Z-candidates < x} ≤ 3 * x ^ Real.logb 2 (3/2)` — Flatto's exponent with an explicit constant;
* **T-B10.2** the two-sided *horizon wall* `(3/2)^k ≤ Z k ≤ 3 * (3/2)^k` together with
  `Z k = p k`, and `Z32.phiModel 3 2 (Set.Ico 0 (1/2)) = Real.log (3/2)`.

References: [Fla92] L. Flatto, *Z-numbers and β-transformations*, in **Symbolic dynamics and its
applications**, Contemp. Math. **135**, AMS (1992), 181–201; [Mahler68] K. Mahler, *An unsolved
problem on the powers of 3/2*, J. Austral. Math. Soc. **8** (1968), 313–321; [FLP95] for the
cylinder machinery re-used from `FLP/`; [Par60] W. Parry for the admissibility criterion.

## 0.  Conventions note (WP0 deliverable)

### 0.1  Two coordinates, one dynamics

The corpus writes the orbit in the **`y`-coordinate**

`ξ * (3/2)^n = mₙ + yₙ`,  `mₙ = ⌊ξ (3/2)ⁿ⌋ : ℤ`,  `yₙ = Int.fract (ξ (3/2)ⁿ) ∈ [0,1)`,

and the Z-window is `yₙ ∈ [0, 1/2)`.  [Fla92] writes the same orbit in the **`r`-coordinate**

`α * (3/2)^n = gₙ + rₙ/2`,  `rₙ ∈ [0,1)`   ([Fla92] (2.1)),

so that

> **`rₙ = 2 yₙ` and `gₙ = mₙ`**, and Flatto's normalisation `rₙ < 1` *is* the Z-condition
> `yₙ < 1/2`.

This is the plan's `z = 2y` rescaling; it is Flatto's, and it is the reason the `r`-coordinate is
the right one: in it the Z-window is the whole of `[0,1)` and the dynamics is a *bona fide*
β-transformation.  All of §2 of plan-B10 is stated in `y`; all of [Fla92] is stated in `r`.  **WP2
works in `r`** and converts once, at the interface with `Z32.phiModel` / `FLP.ZSet`.

### 0.2  The map and the greedy convention

In the `r`-coordinate the step is the greedy β-transformation at `β = 3/2` ([Fla92] (2.8)):

`f r = if r ∈ I₀ then (3/2) * r else (3/2) * r - 1`,  `I₀ = [0, 2/3)`, `I₁ = [2/3, 1)`.

*Fix once and do not relitigate* (gate K-conv): intervals are **left-closed, right-open**, the
branch point `2/3` belongs to `I₁`, and `f` is the *greedy* (largest-digit) choice.  In the
`y`-coordinate the branch point is `1/3`: digit `0` iff `yₙ < 1/3`.

`FLP.lmo β α x = Int.fract (β * x + α)` at `α = 0` **is** this `f`, and
`FLP.splitPt β 0 = 1/β = 2/3` **is** the branch point — so the FLP vocabulary already names both.

### 0.3  One carry, four names

The following are the same `{0,1}`-valued quantity on the Z-window, and no new name should be
introduced for it:

| name | definition | where |
| --- | --- | --- |
| `sₙ` | `2 mₙ₊₁ - 3 mₙ` | plan-B10 §2, `Z32.carry 3 2 ξ 0 n` |
| `εₙ` | `gₙ % 2` (the `T`-expansion digit, `T g = (3g + g % 2)/2`) | [Fla92] (2.8) |
| `δₙ` | `⌊(3/2) rₙ⌋` (the β-expansion digit of `r₀`) | [Fla92] §3 |
| `zParity ξ n` | `⌊ξ (3/2)ⁿ⌋ % 2` | `Bugeaud.zParity` |

`Z32.carry_eq` gives `sₙ = p yₙ - q yₙ₊₁ - (p-q) ν`, i.e. `sₙ = 3 yₙ - 2 yₙ₊₁` at `(p,q,ν)=(3,2,0)`;
in `r` this is `rₙ₊₁ = (3/2) rₙ - sₙ`, which is Flatto's `f`.  **The corpus sign convention and
Flatto's agree**; `Z32.carry`'s general alphabet is `{-q+1, …, p-1} = {-1,0,1,2}`, and F1 (the
carry is forced on the Z-window) is exactly the statement that it collapses to `{0,1}` there.

**Structural point the plan's F1 under-states.**  There are *two* expansions, not one: the
`T`-expansion `εₙ` of the **integer** part `g₀` and the β-expansion `δₙ` of the **fractional** part
`r₀`.  Each is defined for every `α > 0`.  [Fla92] Proposition P: `α` is a Z-number **iff
`εₙ = δₙ` for all `n`**.  The plan's F1 describes the fractional side, its (L4) the integer side;
the Z-condition is their *coincidence*.  WP2 should state Proposition P explicitly — it is what
makes `Z k = p k` a theorem rather than a coincidence of two counts.

### 0.4  The canonical Z-number object (flag-existing rule)

`IsZNumber` is already defined **twice** in the corpus, with textually identical bodies:

* `Bugeaud.IsZNumber` (`Bugeaud/Chapter3/ParityIdentity.lean`) — sorry-free;
* `StringRewriting.AntihydraSRS.IsZNumber` (`SRS/AntihydraMahler.lean`) — in a file carrying **6
  `sorry`s** (including `no_Z_numbers`) and pulling the SRS rewriting machinery.

**Do not add a third.**  Z32's own idiom is already the general FLP object

`FLP.ZSet p q s t = {ξ | 0 < ξ ∧ ∀ n, Int.fract (ξ (p/q)ⁿ) ∈ Ico s (s+t)}`

(see `Z32.ZSet_mono`, `Z32.mem_ZSet_of_eventually`, `Z32.ZSet_cell_empty`), and

> **the canonical Z-number set for this file is `FLP.ZSet 3 2 0 (1/2)`.**

The bridge `FLP.ZSet 3 2 0 (1/2) = {ξ | Bugeaud.IsZNumber ξ}` is one application of
`Int.fract_nonneg` and should be proved *only if* a consumer needs it; neither `Bugeaud/` nor
`SRS/` is imported here.  Bonus: `FLP.ZSet p q 0 t` is verbatim Flatto's generalised `Z_{t,θ}` of
[Fla92] §7, so Theorems 7.1–7.5 are already statable in existing vocabulary (relevant to T13(c)).

### 0.5  Name-collision guards (standing, plan-B10 §8-O8)

* `p k` here is the **β-shift cylinder count** of the Z-system.  It is **not** the steering-word
  complexity `p_T` nor the parity-word complexity `p_b` of M4/A3: different words, different
  systems, no M4 row is touched.
* No dimension theorem is stated anywhere: the Z-number set is countable ([Fla92] Theorem 7.1 /
  Mahler's first theorem), so its Hausdorff dimension is `0`.  `δ = log₂(3/2)` is a **counting
  exponent** only.
* `no_Z_numbers` (`SRS/`) is untouched: an `O(x^0.585)` count says nothing about emptiness.
* **New guard.**  [Fla92] Theorem 5.1 (`Nₙ(a,b)/Nₙ → b - a`: the `n`-th stage intervals
  equidistribute) counts cylinders *contained in* a window at time `n`.  That is **not**
  confinement and **not** `Z32.phiModel`.  Do not read Theorem 5.1 as an entropy statement about
  the atlas windows of T-B10.3.

## 1.  WP0(a): plan §2 checked against [Fla92]

Every derivation of plan-B10 §2 survives contact with the paper; several are *literally* Flatto's.

| plan-B10 | [Fla92] | verdict |
| --- | --- | --- |
| F1: carry forced; β-shift, branch `2/3` | §2, (2.8)–(2.10) | confirmed verbatim (`r = 2y`) |
| (L1) cylinder image is `[0, r_w)` | Thm 3.3(i)(iii), Lemma 4.2 | confirmed, and **sharpened** (§1.1) |
| (L2) partition, `Σ r_w = (3/2)^k` | Thm 3.3(ii), §4 Remark 2 | confirmed |
| (L3) `p(k) ≤ 3 (3/2)^k` | Thm 4.1(ii)(iv) + summation | confirmed, both routes give `3(3/2)^k - 2` |
| `p(k) ≥ (3/2)^k` | Thm 3.3(iv) + partition | confirmed (Flatto has the ingredient, not the statement) |
| (L4) `m mod 2^k ↔ carry word` bijection | **Thm 3.1**, for general `p/q` | confirmed; Flatto's is stronger |
| F3's `σ(w)`, `N(w) ≡ -σ(w) 3^{-n} (mod 2^n)` | **(3.2)** | confirmed — the identity is Flatto's |
| `Z k = p k` (equality, not `≤`) | (6.3) | confirmed; Flatto writes the equality |
| T-B10.1 | Thm 6.1 (`O`-form) | the explicit constant `3` is new *as stated*, immediate from Thm 4.1(iv) |
| T-B10.2, the wall | **Thm 4.3** (4.10) | see §1.3 — **the wall is already a consequence of [Fla92]** |

### 1.1  The sharpening: cylinder images are orbit points of `1`

Plan (L1) says `r_w ∈ (0,1]`.  [Fla92] Lemma 4.2 says more: `fⁿ` is linear with slope `βⁿ` on each
`n`-th stage interval `Iₙ` and maps it **onto `[0, f^k 1)`** for some `k ≥ 0` — the *type* of `Iₙ`.
So

`r_w ∈ {f^k 1 : k ≥ 0} = {1, 1/2, 3/4, 1/8, 3/16, 9/32, 27/64, 81/128, 243/256, 217/512, …}`,

a countable set of dyadic rationals with odd numerators (hence `3/2` is **not** a β-number and not
simple: `f^k 1 ≠ 0` for all `k`, so `N(β) = ∞` and every `min[n, N-1]` in [Fla92] §4 is just `n`).

With `a_k := ⌊(3/2) · f^k 1⌋ ∈ {0,1}` and `F_{nk}` the number of type-`k` intervals at level `n`,
[Fla92] Theorem 4.1 gives `F₀₀ = 1`, `F_{nk} = F_{n-k,0}`, `F_{n+1,0} = Σ_{k≤n} a_k F_{n-k,0}`,
`F_{n0} ≤ βⁿ`, and `Nₙ = Σ_{j≤n} F_{j0}`.  Since `r_w > 2/3 ↔ a_k = 1` for `w` of type `k`, the
plan's straddle count is *identified*:

> **`#{w admissible, |w| = n : r_w > 2/3} = F_{n+1,0} = p(n+1) - p(n)`.**

`a_k` for `k = 0 … 20`: `1,0,1,0,0,0,0,0,1,0,0,1,0,0,1,0,1,0,0,0,0`.

### 1.2  Sanity data for WP2 (`decide`-checkable)

Computed two independent ways — Flatto's recursion above, and brute force over all `2ⁿ` words
filtered by the Parry criterion ([Fla92] Thm 3.2(ii): every shift `≤ a` lexicographically) — which
**agree for all `n ≤ 16`**:

| `n` | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `F_{n0}` | 1 | 1 | 1 | 2 | 3 | 4 | 6 | 9 | 13 | 20 | 30 | 44 | 67 | 101 | 150 | 226 |
| `p n = Nₙ` | 1 | 2 | 3 | 5 | 8 | 12 | 18 | 27 | 40 | 60 | 90 | 134 | 201 | 302 | 452 | 678 |

This confirms the plan's `p(1) = 2`, `p(2) = 3`.  Note `p n` is Fibonacci only up to `n = 4`
(`1,2,3,5,8`) and breaks at `n = 5` (`12`, not `13`): the word `10101` is inadmissible.  That gap
*is* the difference between Mahler's exponent and Flatto's.

### 1.3  The wall is Flatto's, so T-B10.2 is formalize-the-known

[Fla92] Theorem 4.3 (4.10) states, for non-simple `β` (so `β^{-N} = 0` at `β = 3/2`),

`Nₙ = (β / (σ (β-1))) · βⁿ + O(δⁿ)`,  `σ = Σ_{n≥0} f^n 1 / βⁿ`,  some `0 < δ < β`,

i.e. `p n = (3/σ) (3/2)ⁿ + O(δⁿ)` — a **two-sided** asymptotic.  Numerically
`σ = 1.93417962…`, `3/σ = 1.55104518846…`, and `p n / (3/2)ⁿ` is verified to converge to it
(`1.5510451885` by `n = 40`).  Consequently:

* the plan's bracket `[1, 3]` is correct and contains the true constant, but is loose; the
  empirical maximum of `p n / (3/2)ⁿ` is `1.5802…` (attained at `n = 4 … 7`), so `1.59` is the best
  constant any bound of this shape can have;
* **the horizon wall follows from a 1992 theorem.**  T-B10.2 is therefore *formalize-the-known*,
  not a new negative result.  It is unlike A13/A14/A15, which closed lanes with genuinely new
  no-gos.  What is new here is (i) an *elementary* proof of the lower bound (Flatto's is via
  generating functions, analytic continuation and a residue at `z = 1/β`) and (ii) the
  machine-checking.  **Action for WP7:** correct the §1 ledger's "the B-catalogue's next
  machine-checked negative, in the A13/A14/A15 pattern" and the matching sentence in §8-O7.  The
  §8-O1 re-score is *unaffected* — it already prices T-B10.1/2/3 as formalize-the-known at
  0.80–0.95.
* Theorem 4.3 itself is **out of budget** and should not be a target: it needs `F(z)[1-φ(z)] = 1`,
  analytic continuation past `|z| = 1/β`, and a simple-pole residue.  Record it, cite it, do not
  formalize it.

### 1.4  Two free additions WP2 should take

1. **Mahler's Second Theorem, machine-checked.**  [Fla92] Lemma 6.1 + §6: every β-expansion at
   `β = 3/2` avoids the block `11` (Parry against `a₀a₁ = 10`), the count of `11`-free words of
   length `n` is Fibonacci, hence `|Z(x)| = O(x^{log₂ φ})`, `φ` the golden ratio, `δ = .70…`.  This
   is ~15 lines on top of (L4) and makes the paper's arc complete: **Mahler 0.70 → Flatto 0.59**,
   both machine-checked, with `p 5 = 12 < 13` the exact point where the improvement begins.
2. **Keep the plan's Chebyshev route for (L3).**  Flatto's type route and the plan's mass route
   give the *identical* bound `3(3/2)ⁿ - 2`, so there is nothing to gain in sharpness, and the
   plan's route avoids introducing the type classification (Def 4.1/4.2, Lemma 4.1) altogether.
   Introduce types only if WP2 also wants the exact recursion of §1.1 — which is worth it *only*
   for the `decide`-checkable small values in §1.2.

## 2.  WP0(b): the literature gate G-Lit

**Verdict: G-Lit PASSES.  No published `δ < log₂(3/2)` was found**, so lane L2 remains research
content and is not re-scoped to formalize-the-known.

Checked: the Wikipedia survey of Mahler's 3/2 problem (records Mahler `O(x^{0.7})` → Flatto
`O(x^{log₂(3/2)})` and names no successor); arXiv:2411.03468 *Mahler's 3/2 problem in ℤ⁺*
(**withdrawn** 2025-06-18, and contains no counting statement in any case); and targeted searches
for post-1992 improvements.  The adjacent Dubickas / Akiyama literature that does exist works on
the *range and limit points* of `{ξ(p/q)ⁿ}` and on the existence of `ξ` whose orbit stays in a
Cantor set or a short interval — **not** on the counting exponent.  [FLP95]'s `Ω(p/q) > 1/p` is
likewise a different quantity.  Caveat: this is a web-search-level pass, not a citation sweep of
MathSciNet/zbMATH; if the paper (WP7) claims priority, redo it there.

**Finding: G-Lit is under-scoped in the plan.**  It gates only `δ`, but T-B10.3 (the atlas) has an
active literature of its own that the plan does not cite: survivor sets of β-transformations with
a hole.  Urbański (1986) proved `t ↦ h_top` of the survivor set is a devil's staircase; see also
Kalle–Kong–Langeveld–Li, *The β-transformation with a hole at 0* (arXiv:1803.07338),
*Entropy plateaus, transitivity and bifurcation sets…* (arXiv:2304.06892), and Langeveld's thesis.
**Caveat before reuse:** those papers put the hole **at 0**, whereas the atlas's hole is at the
**right end**.  In the `r`-coordinate an atlas window `y ∈ [0, ℓ)` is `r ∈ [0, 2ℓ)` with
`2ℓ ∈ [0.81444, 1)`, i.e. the survivor set of `f` with hole `[2ℓ, 1)`; since the branch point `2/3`
lies below `0.81444`, the hole sits strictly inside the second branch.  Whether the hole-at-0
results transfer must be decided **before WP4 claims novelty for T-B10.3** — a second G-Lit pass,
which this plan does not currently schedule.

## 3.  WP0(c): corpus API audit

* **(L4) is *not* present.**  `Z32/DyadicOrbit.lean` is about the single point `ξ = 1`
  (`Z32.oddNum n = 3^n % 2^n`), not the bijection.  But its engine is: `Z32.xInt_add`
  (`Z32/DubickasWord.lean`) — `x_{n+m} = (p/q)^m xₙ + (Σ_{r<m} (p/q)^{m-1-r} s_{n+r})/q` — **is**
  [Fla92] (3.2), and Flatto's proof of Theorem 3.1 is one clearing-of-denominators plus
  `Nat.Coprime p q` away from it.  Budget (L4) as *short*, not as fresh work.
* **Carry sign convention: consistent.**  `Z32.carry`, `Z32.carry_eq` as in §0.3 above.  Reuse; do
  not re-define.
* **(L1)/(L3) pattern: `FLP/SurvivorFinite.lean`.**  It has `cyl`, `straddle`, `children`, `alive`,
  `cyl_ordConnected`, `cyl_subset_J`, `false_child_nonempty`, `true_child_nonempty`,
  `children_card_le`, `alive_step`, `alive_card_le`, `eq_of_word_eq`, `survivors_finite` — the
  whole two-branch cylinder idiom, and at `α = 0` its `lmo`/`splitPt` are Flatto's `f` and `2/3`.
  **But it is a pattern, not a library:** FLP's cylinders are confined to `Ico 0 (1/β)`
  (`cyl_subset_J`), i.e. FLP's own *escape* regime, whereas B10 needs the full β-shift on `[0,1)`;
  and `FLP.straddle_filter_card_le_one` ("at most one straddler per level") is exactly the
  escape-regime fact that **fails** here — replacing it with the mass bound is the whole content of
  (L3).  This matches the plan's assessment.
* **`Z32/ModelEntropy.lean` is the T-B10.2 interface.**  `Z32.phiModel p q U`, `Z32.modelLang`,
  `Z32.IsModelOrbit`, plus `Z32.back`/`Z32.backNum` for kernel-checkable endpoints.  The target
  statement is `Z32.phiModel 3 2 (Set.Ico 0 (1/2)) = Real.log (3/2)`, replacing the crude
  `Z32.card_modelLang_le_pow` (`≤ (p+q-1)ⁿ = 4ⁿ`) by `3 (3/2)ⁿ` at the Z-cell.
* **Z-number predicate:** resolved in §0.4 — use `FLP.ZSet 3 2 0 (1/2)`, add no third definition.
* **Annotation keys.**  `@[ref]` strings are opaque (no registry check in
  `Corpus/Util/Attributes/Database.lean`), and the corpus's Mahler key is **`"Mahler68"`**, not the
  plan's `"Mah68"` — WP2 uses `ref "Fla92" "Mahler68"`.  Group key `mahler_z_counting` per the
  plan: per-problem, and deliberately *not* `z32_*`-prefixed, since this is a Mahler-problem
  cluster rather than cert32 machinery; it is distinct from SRS's existing `mahler_z_numbers`
  (existence, not counting).  `[Fla92]` is new to the corpus and needs a bibliography line in
  `Z32/README.md` at WP7.

## 4.  WP0(d): Mathlib probes

* **Walk counting exists only for `SimpleGraph`:** `SimpleGraph.adjMatrix_pow_apply_eq_card_walk`
  (`Mathlib.Combinatorics.SimpleGraph.AdjMatrix`), plus `finsetWalkLength` in
  `…SimpleGraph.Connectivity.WalkCounting`.  Undirected, simple, unlabelled, no multi-edges — not
  usable for a labelled multi-digraph.
* **`Digraph` exists but is empty of what I1 needs:** `Mathlib.Combinatorics.Digraph.Basic` defines
  only `structure Digraph (V) where Adj : V → V → Prop` and its lattice/Boolean-algebra instances.
  There are no walks, no adjacency matrix, no counting; the only other file mentioning it is
  `Digraph/Orientation.lean`.  **Do not try to build I1 on `Digraph`** — keep the plan's minimal
  `Finset` of labelled edges over `Fin S`.
* **No Perron–Frobenius in Mathlib at all** (local search for `Perron` returns nothing).
  `spectralRadius` exists only in the Banach-algebra setting (`Mathlib.Analysis.Normed.Algebra.
  Spectrum`, `…GelfandFormula`) with no nonnegative-matrix theory.  This *confirms* I1's design
  decision to avoid eigentheory rather than merely making it convenient.
* **No β-expansion material.**  Mathlib has integer-base digits only:
  `Real.digits : ℝ → (b : ℕ) → [NeZero b] → ℕ → Fin b` and `Real.ofDigits`
  (`Mathlib.Analysis.Real.OfDigits`).  No non-integer base, no β-shift, no admissibility criterion.
  A15's `parryOrbit` work in `TH/SceneryEdge.lean` remains the nearest in-repo object.

⇒ `ForMathlib/Combinatorics/PathGrowth.lean` (I1) is a genuine Mathlib gap, as the plan predicted,
and is a defensible Mathlib-upstream candidate.

## 5.  Corrections to `plans/plan-B10.html` (for WP7)

1. §5 file table: the Mahler ref key is `"Mahler68"`, not `"Mah68"`.
2. §1 ledger and §8-O7: T-B10.2 is **formalize-the-known** (the wall follows from [Fla92] Thm 4.3),
   not a new negative in the A13/A14/A15 pattern.  Novelty = elementary proof + machine-checking.
   §8-O1's numeric re-score is unaffected.
3. §2.2 (L1): `r_w` is not merely in `(0,1]` — it ranges over the orbit `{f^k 1}`, which yields the
   exact recursion and the identity `#{r_w > 2/3} = p(n+1) - p(n)` (§1.1).
4. §7 gate table: G-Lit should also gate T-B10.3 against the survivor-set-with-a-hole literature
   (§2), scheduled before WP4/WP7 rather than at WP0.
5. §6 WP2: add Mahler's Second Theorem (`δ = log₂ φ`) as a warm-up (§1.4).
6. §10 references: [Fla92] is now in the repo as `Flatto1992.pdf` (extracted from *Symbolic
   dynamics and its applications*, pp. 181–201); the "cf." on it can be dropped, and its content is
   page-verified throughout §1 above.
-/

namespace Z32
namespace Flatto

open Finset

/-! ## 6.  Cylinders by their right endpoint

The whole of (L1)–(L3) is carried by a single rational number per cylinder: its **image's right
endpoint**.  By [Fla92] Theorem 3.3(i)(iii) the image of a nonempty `k`-cylinder under `f^k` is
`[0, r)`; the two branches of `f` then move `r` as follows.  Reading a digit `0` restricts the
cylinder to `f⁻¹[0, 2/3)` and stretches by `3/2`, giving `min (3r/2) 1`; reading a digit `1`
restricts to `f⁻¹[2/3, 1)`, which is nonempty exactly when `r > 2/3`, and gives `3r/2 - 1`.

Working with the endpoint alone means no interval ever appears, which is what disarms gate K-conv:
there are no half-open endpoint fights because there are no endpoints to fight over — only the
exact rational recursion below. -/

/-- One step of the right endpoint of a cylinder image, under the digit `b`. -/
def step (r : ℚ) (b : Bool) : ℚ := if b then 3 * r / 2 - 1 else min (3 * r / 2) 1

@[simp] theorem step_false (r : ℚ) : step r false = min (3 * r / 2) 1 := by simp [step]

@[simp] theorem step_true (r : ℚ) : step r true = 3 * r / 2 - 1 := by simp [step]

/-- The right endpoint of the image of the cylinder of the digit word `w`, read left to right.
A word is admissible exactly when this stays positive. -/
def endAfter (w : List Bool) : ℚ := w.foldl step 1

/-- The digits that may legally follow a cylinder whose image is `[0, r)`: always `0`, and `1`
exactly when the image straddles the branch point `2/3`. -/
def allowed (r : ℚ) : Finset Bool := if 2 / 3 < r then {false, true} else {false}

/-- The **admissible digit words of length `k`** for the greedy `β = 3/2` transformation. -/
def adm : ℕ → Finset (List Bool)
  | 0 => {[]}
  | k + 1 => (adm k).biUnion fun w => (allowed (endAfter w)).image fun b => w ++ [b]

/-- **Flatto's `N_k`** ([Fla92] §4): the number of admissible words of length `k`, equivalently of
nonempty `k`-cylinders.  Written `p k` in plan-B10. -/
def pCount (k : ℕ) : ℕ := (adm k).card

@[simp] theorem endAfter_nil : endAfter [] = 1 := rfl

@[simp] theorem adm_zero : adm 0 = {[]} := rfl

theorem adm_succ (k : ℕ) :
    adm (k + 1) = (adm k).biUnion fun w => (allowed (endAfter w)).image fun b => w ++ [b] := rfl

/-- Appending a digit applies one `step` to the endpoint. -/
@[simp] theorem endAfter_concat (w : List Bool) (b : Bool) :
    endAfter (w ++ [b]) = step (endAfter w) b := by
  simp [endAfter]

theorem mem_allowed_true {r : ℚ} (h : true ∈ allowed r) : 2 / 3 < r := by
  by_contra hr
  simp [allowed, hr] at h

/-- Words counted at stage `k` have length `k`. -/
@[category API, AMS 11 37, ref "Fla92", group "mahler_z_counting"]
theorem length_of_mem_adm : ∀ (k : ℕ) (w : List Bool), w ∈ adm k → w.length = k := by
  intro k
  induction k with
  | zero => intro w hw; simp only [adm_zero, mem_singleton] at hw; simp [hw]
  | succ k ih =>
    intro w hw
    rw [adm_succ, mem_biUnion] at hw
    obtain ⟨u, hu, hw⟩ := hw
    obtain ⟨b, -, rfl⟩ := mem_image.mp hw
    simp [ih u hu]

theorem concat_injective (w : List Bool) : Function.Injective fun b => w ++ [b] := by
  intro b b' h
  simpa using h

/-- Distinct words of a stage extend to disjoint families: the extension remembers its parent. -/
theorem adm_pairwiseDisjoint (k : ℕ) :
    (↑(adm k) : Set (List Bool)).PairwiseDisjoint
      fun w => (allowed (endAfter w)).image fun b => w ++ [b] := by
  intro w hw w' hw' hne
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  rintro u hu hu'
  obtain ⟨b, -, rfl⟩ := mem_image.mp hu
  obtain ⟨b', -, hb'⟩ := mem_image.mp hu'
  refine hne ?_
  have hlen : w'.length = w.length := by
    rw [length_of_mem_adm k w' (by simpa using hw'), length_of_mem_adm k w (by simpa using hw)]
  exact ((List.append_inj hb' hlen).1).symm

/-- **The endpoint invariant**: every admissible cylinder image is a nonempty subinterval of
`[0, 1)`, i.e. its right endpoint lies in `(0, 1]`. -/
@[category API, AMS 11 37, ref "Fla92", group "mahler_z_counting",
  formal_uses mem_allowed_true]
theorem endAfter_mem_Ioc : ∀ (k : ℕ) (w : List Bool), w ∈ adm k → 0 < endAfter w ∧ endAfter w ≤ 1 := by
  intro k
  induction k with
  | zero => intro w hw; simp only [adm_zero, mem_singleton] at hw; norm_num [hw]
  | succ k ih =>
    intro w hw
    rw [adm_succ, mem_biUnion] at hw
    obtain ⟨u, hu, hw⟩ := hw
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hw
    obtain ⟨h0, h1⟩ := ih u hu
    rw [endAfter_concat]
    cases b with
    | false =>
      rw [step_false]
      exact ⟨lt_min (by linarith) one_pos, min_le_right _ _⟩
    | true =>
      have h23 : 2 / 3 < endAfter u := mem_allowed_true hb
      rw [step_true]
      constructor <;> linarith

/-- **(L2), the mass step.**  Whatever the branching, the children's endpoints sum to `3/2` times
the parent's — one child of endpoint `3r/2` when `r ≤ 2/3`, two of endpoints `1` and `3r/2 - 1`
when `r > 2/3`.  This single identity is what makes the count exactly geometric. -/
@[category API, AMS 11 37, ref "Fla92", group "mahler_z_counting"]
theorem sum_step_allowed (r : ℚ) : ∑ b ∈ allowed r, step r b = 3 * r / 2 := by
  by_cases h : 2 / 3 < r
  · rw [allowed, ite_eq_left h, Finset.sum_pair Bool.false_ne_true, step_false, step_true,
      min_eq_right (by linarith)]
    ring
  · rw [allowed, ite_eq_right h, Finset.sum_singleton, step_false,
      min_eq_left (by have := not_lt.mp h; linarith)]

theorem card_allowed (r : ℚ) : (allowed r).card = if 2 / 3 < r then 2 else 1 := by
  by_cases h : 2 / 3 < r <;> simp [allowed, h, Finset.card_pair Bool.false_ne_true]

/-- **(L2).**  The endpoints of the stage-`k` cylinders sum to exactly `(3/2)^k`
([Fla92] §4, Remark 2: `∑_{I_k} λ(I_k) = 1` after rescaling by `β^k`). -/
@[category research solved, AMS 11 37, ref "Fla92", group "mahler_z_counting",
  formal_uses sum_step_allowed adm_pairwiseDisjoint]
theorem sum_endAfter_adm : ∀ k : ℕ, ∑ w ∈ adm k, endAfter w = (3 / 2 : ℚ) ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [adm_succ, Finset.sum_biUnion (adm_pairwiseDisjoint k)]
    have : ∀ w ∈ adm k,
        ∑ u ∈ (allowed (endAfter w)).image fun b => w ++ [b], endAfter u
          = 3 * endAfter w / 2 := by
      intro w _
      rw [Finset.sum_image fun b _ b' _ h => concat_injective w h]
      simp only [endAfter_concat]
      exact sum_step_allowed _
    rw [Finset.sum_congr rfl this]
    calc ∑ w ∈ adm k, 3 * endAfter w / 2
        = (3 / 2 : ℚ) * ∑ w ∈ adm k, endAfter w := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun w _ => by ring
      _ = (3 / 2 : ℚ) ^ (k + 1) := by rw [ih]; ring

/-- The stage count obeys the branch recursion: a cylinder has two children exactly when its image
straddles `2/3`.  (WP0 identifies this straddle count with Flatto's `F_{k+1,0}`.) -/
@[category API, AMS 11 37, ref "Fla92", group "mahler_z_counting",
  formal_uses adm_pairwiseDisjoint card_allowed]
theorem pCount_succ (k : ℕ) :
    pCount (k + 1) = pCount k + ((adm k).filter fun w => 2 / 3 < endAfter w).card := by
  have hcard : (adm (k + 1)).card = ∑ w ∈ adm k, (allowed (endAfter w)).card := by
    rw [adm_succ, Finset.card_biUnion (adm_pairwiseDisjoint k)]
    exact Finset.sum_congr rfl fun w _ =>
      Finset.card_image_of_injective _ (concat_injective w)
  simp only [pCount, hcard, card_allowed, Finset.card_filter]
  rw [Finset.card_eq_sum_ones (adm k), ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun w _ => by by_cases h : 2 / 3 < endAfter w <;> simp [h]

/-- **(L3), the Chebyshev step.**  Cylinders whose image exceeds `2/3` are few, because the total
endpoint mass is only `(3/2)^k`. -/
@[category API, AMS 11 37, ref "Fla92", group "mahler_z_counting",
  formal_uses sum_endAfter_adm endAfter_mem_Ioc]
theorem straddle_card_le (k : ℕ) :
    ((((adm k).filter fun w => 2 / 3 < endAfter w).card : ℚ)) ≤ (3 / 2 : ℚ) ^ (k + 1) := by
  set S := (adm k).filter fun w => 2 / 3 < endAfter w with hS
  have hsub : S ⊆ adm k := Finset.filter_subset _ _
  have h1 : (2 / 3 : ℚ) * S.card ≤ ∑ w ∈ S, endAfter w := by
    rw [mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun w hw => ?_
    have hw' : w ∈ (adm k).filter fun w => 2 / 3 < endAfter w := hw
    exact le_of_lt (Finset.mem_filter.mp hw').2
  have h2 : ∑ w ∈ S, endAfter w ≤ ∑ w ∈ adm k, endAfter w :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun w hw _ => (endAfter_mem_Ioc k w hw).1.le
  rw [sum_endAfter_adm k] at h2
  have : (2 / 3 : ℚ) * S.card ≤ (3 / 2 : ℚ) ^ k := h1.trans h2
  have hpow : (0 : ℚ) < (3 / 2 : ℚ) ^ k := by positivity
  rw [pow_succ]
  nlinarith [this]

/-! ## 7.  T-B10.1 and T-B10.2: the two-sided horizon count -/

/-- **The lower half of the wall.**  `(3/2)^k ≤ N_k`: the endpoints sum to `(3/2)^k` and each is at
most `1`, so there must be at least `(3/2)^k` of them. -/
@[category research solved, AMS 11 37, ref "Fla92", group "mahler_z_counting",
  formal_uses sum_endAfter_adm endAfter_mem_Ioc]
theorem le_pCount (k : ℕ) : (3 / 2 : ℚ) ^ k ≤ pCount k := by
  rw [← sum_endAfter_adm k]
  calc ∑ w ∈ adm k, endAfter w ≤ ∑ _w ∈ adm k, (1 : ℚ) :=
        Finset.sum_le_sum fun w hw => (endAfter_mem_Ioc k w hw).2
    _ = pCount k := by simp [pCount]

/-- **The upper half of the wall**, with Flatto's explicit constant: `N_k ≤ 3 (3/2)^k - 2`.
Summing the Chebyshev step over the stages; the same constant `3` that [Fla92] Theorem 4.1(iv)
gives by the type decomposition. -/
@[category research solved, AMS 11 37, ref "Fla92", group "mahler_z_counting",
  formal_uses pCount_succ straddle_card_le]
theorem pCount_le (k : ℕ) : (pCount k : ℚ) ≤ 3 * (3 / 2 : ℚ) ^ k - 2 := by
  induction k with
  | zero => norm_num [pCount]
  | succ k ih =>
    have hstep := pCount_succ k
    have hstr := straddle_card_le k
    have : (pCount (k + 1) : ℚ)
        = (pCount k : ℚ) + (((adm k).filter fun w => 2 / 3 < endAfter w).card : ℚ) := by
      rw [hstep]; push_cast; ring
    rw [this, pow_succ]
    rw [pow_succ] at hstr
    linarith

/-! ### The block `11` is forbidden

Immediately after a digit `1` the endpoint has dropped to at most `1/2`, which is below the branch
point `2/3`; so only a `0` may follow.  This is the mechanism behind Mahler's own exponent
`log₂ φ` ([Fla92] Lemma 6.1: admissible words avoid `11`, and there are Fibonacci-many such). -/

/-- After a digit `1`, no digit `1` is allowed. -/
@[category research solved, AMS 11 37, ref "Fla92" "Mahler68", group "mahler_z_counting"]
theorem allowed_step_true {r : ℚ} (h : r ≤ 1) : allowed (step r true) = {false} := by
  rw [step_true, allowed, ite_eq_right (by intro hc; linarith)]

/-- Concretely: a stage-`k` word ending in `1` extends only by `0`. -/
@[category research solved, AMS 11 37, ref "Fla92" "Mahler68", group "mahler_z_counting",
  formal_uses allowed_step_true endAfter_mem_Ioc]
theorem allowed_endAfter_concat_true {k : ℕ} {w : List Bool} (hw : w ∈ adm k) :
    allowed (endAfter (w ++ [true])) = {false} := by
  rw [endAfter_concat]
  exact allowed_step_true (endAfter_mem_Ioc k w hw).2

/-! ### Sanity values

Computed by `norm_num` rather than `decide`: kernel reduction cannot evaluate `ℚ` arithmetic,
because `Rat` normalisation goes through the well-founded `Nat.gcd` (plan-B10 D2's "decide in `ℕ`"
applies to the WP3 certificate layer, which is stated over `ℕ` from the start).

These match [Fla92] §4 and WP0's independent computation.  The value `p 5 = 12` — not the Fibonacci
`13` — is the exact point where Flatto's exponent improves on Mahler's: the word `10101` is
inadmissible. -/

@[category test, AMS 11 37, ref "Fla92", group "mahler_z_counting"]
theorem pCount_values :
    pCount 0 = 1 ∧ pCount 1 = 2 ∧ pCount 2 = 3 ∧ pCount 3 = 5 ∧ pCount 4 = 8 ∧ pCount 5 = 12 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [pCount, adm, endAfter, allowed, step]

theorem false_mem_allowed (r : ℚ) : false ∈ allowed r := by
  by_cases h : 2 / 3 < r <;> simp [allowed, h]

theorem true_mem_allowed {r : ℚ} (h : 2 / 3 < r) : true ∈ allowed r := by simp [allowed, h]

/-! ## 8.  Abstract greedy orbits

Everything downstream — Z-numbers, and the model orbits of `Z32.ModelEntropy` — is an instance of
one notion: a sequence in `[0,1)` obeying `rₙ₊₁ = (3/2) rₙ - dₙ` with digits in `{0,1}`.  The
admissibility induction is proved once, here. -/

/-- A **greedy `β = 3/2` orbit**: `rₙ ∈ [0,1)` and `rₙ₊₁ = (3/2) rₙ - dₙ`, `dₙ ∈ {0,1}`. -/
def IsGreedyOrbit (r : ℕ → ℝ) (d : ℕ → Bool) : Prop :=
  (∀ n, r n ∈ Set.Ico (0 : ℝ) 1) ∧
    ∀ n, r (n + 1) = 3 * r n / 2 - (if d n then 1 else 0)

/-- The length-`k` digit word of an orbit, in reading order. -/
def orbWord (d : ℕ → Bool) : ℕ → List Bool
  | 0 => []
  | k + 1 => orbWord d k ++ [d k]

@[simp] theorem orbWord_zero (d : ℕ → Bool) : orbWord d 0 = [] := rfl

@[simp] theorem orbWord_succ (d : ℕ → Bool) (k : ℕ) :
    orbWord d (k + 1) = orbWord d k ++ [d k] := rfl

@[simp] theorem orbWord_length (d : ℕ → Bool) : ∀ k, (orbWord d k).length = k := by
  intro k; induction k with
  | zero => rfl
  | succ k ih => simp [ih]

/-- `orbWord d k` reads only the first `k` digits. -/
theorem orbWord_congr {d d' : ℕ → Bool} : ∀ (k : ℕ), (∀ i < k, d i = d' i) →
    orbWord d k = orbWord d' k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    rw [orbWord_succ, orbWord_succ, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)),
      h k (Nat.lt_succ_self k)]

/-- ... and it determines them: the word recovers its own letters. -/
theorem orbWord_inj_digits {d d' : ℕ → Bool} : ∀ (k : ℕ), orbWord d k = orbWord d' k →
    ∀ i < k, d i = d' i := by
  intro k
  induction k with
  | zero => intro _ i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ k ih =>
    intro h i hi
    rw [orbWord_succ, orbWord_succ] at h
    obtain ⟨hpre, hlast⟩ := List.append_inj h (by simp)
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | rfl
    · exact ih hpre i h'
    · simpa using hlast

/-- The digits of a greedy orbit are the greedy ones: `dₙ = 1` forces `rₙ ≥ 2/3`. -/
theorem greedy_of_digit_true {r d} (h : IsGreedyOrbit r d) {n : ℕ} (hd : d n = true) :
    2 / 3 ≤ r n := by
  have hs := h.2 n
  rw [hd, ite_eq_left rfl] at hs
  have := (h.1 (n + 1)).1
  linarith

/-- Dually, `dₙ = 0` forces `rₙ < 2/3`. -/
theorem greedy_of_digit_false {r d} (h : IsGreedyOrbit r d) {n : ℕ} (hd : d n = false) :
    r n < 2 / 3 := by
  have hs := h.2 n
  rw [hd] at hs
  simp only [Bool.false_eq_true, ite_false] at hs
  have := (h.1 (n + 1)).2
  linarith

/-- **The admissibility induction.**  Every greedy orbit produces admissible words, and its position
inside the cylinder image is strict — the second clause is what lets the next digit be read off. -/
@[category research solved, AMS 11 37, ref "Fla92", group "mahler_z_counting",
  formal_uses greedy_of_digit_true greedy_of_digit_false true_mem_allowed false_mem_allowed]
theorem orbWord_mem_adm {r d} (h : IsGreedyOrbit r d) :
    ∀ k : ℕ, orbWord d k ∈ adm k ∧ r k < ((endAfter (orbWord d k) : ℚ) : ℝ) := by
  intro k
  induction k with
  | zero => exact ⟨by simp, by simpa using (h.1 0).2⟩
  | succ k ih =>
    obtain ⟨hmem, hlt⟩ := ih
    have hs := h.2 k
    cases hd : d k with
    | false =>
      have h23 : r k < 2 / 3 := greedy_of_digit_false h hd
      rw [hd] at hs
      simp only [Bool.false_eq_true, ite_false] at hs
      refine ⟨?_, ?_⟩
      · rw [orbWord_succ, hd, adm_succ]
        exact Finset.mem_biUnion.mpr
          ⟨orbWord d k, hmem, Finset.mem_image.mpr ⟨false, false_mem_allowed _, rfl⟩⟩
      · rw [orbWord_succ, hd, endAfter_concat, step_false]
        push_cast
        exact lt_min (by linarith) (by rw [hs]; linarith)
    | true =>
      have h23 : 2 / 3 ≤ r k := greedy_of_digit_true h hd
      rw [hd, ite_eq_left rfl] at hs
      have hR : (2 / 3 : ℚ) < endAfter (orbWord d k) := by
        have : ((2 / 3 : ℚ) : ℝ) < ((endAfter (orbWord d k) : ℚ) : ℝ) := by push_cast; linarith
        exact_mod_cast this
      refine ⟨?_, ?_⟩
      · rw [orbWord_succ, hd, adm_succ]
        exact Finset.mem_biUnion.mpr
          ⟨orbWord d k, hmem, Finset.mem_image.mpr ⟨true, true_mem_allowed hR, rfl⟩⟩
      · rw [orbWord_succ, hd, endAfter_concat, step_true]
        push_cast
        linarith

/-! ## 9.  The bridge to Mahler's Z-numbers

The only place in this file where a real number is touched.  `Bugeaud.three_zFrac` (Exercise 3.1,
`Bugeaud/Chapter3/ParityIdentity.lean`) already supplies the step relation
`3 yₙ = εₙ + 2 yₙ₊₁` with `εₙ = ⌊ξ (3/2)ⁿ⌋ mod 2`; in Flatto's coordinate `rₙ = 2 yₙ` that reads
`rₙ₊₁ = (3/2) rₙ - εₙ`, i.e. exactly the greedy map `f`.  So the parity word of a Z-number *is* a
`β`-expansion digit word, which is [Fla92] Proposition P in the direction needed here.

This revises §0.4 of the conventions note: `Bugeaud/Chapter3/ParityIdentity.lean` (sorry-free) *is*
imported after all, because it already owns the step relation and Mahler's first theorem, and the
flag-existing rule says reuse rather than reprove.  `Bugeaud.IsZNumber` is therefore the predicate
used here; `zSet_eq` below records its agreement with `FLP.ZSet 3 2 0 (1/2)`. -/

/-- The `β`-digit at step `n`: the parity of the `n`-th integer part. -/
noncomputable def zDigit (ξ : ℝ) (n : ℕ) : Bool := if Bugeaud.zParity ξ n = 1 then true else false

/-- The first `k` digits, in reading order. -/
noncomputable def zWord (ξ : ℝ) : ℕ → List Bool := orbWord (zDigit ξ)

/-- Flatto's rescaled orbit coordinate `rₙ = 2 {ξ (3/2)ⁿ}` ([Fla92] (2.1)). -/
noncomputable def zOrb (ξ : ℝ) (n : ℕ) : ℝ := 2 * Int.fract (ξ * (3 / 2) ^ n)

@[simp] theorem zWord_zero (ξ : ℝ) : zWord ξ 0 = [] := rfl

@[simp] theorem zWord_succ (ξ : ℝ) (k : ℕ) : zWord ξ (k + 1) = zWord ξ k ++ [zDigit ξ k] := rfl

theorem zParity_eq_zero_of_zDigit_false {ξ : ℝ} {n : ℕ} (h : zDigit ξ n = false) :
    Bugeaud.zParity ξ n = 0 := by
  rcases Bugeaud.zParity_eq_zero_or_one ξ n with h0 | h1
  · exact h0
  · simp [zDigit, h1] at h

theorem zParity_eq_one_of_zDigit_true {ξ : ℝ} {n : ℕ} (h : zDigit ξ n = true) :
    Bugeaud.zParity ξ n = 1 := by
  by_contra hne
  simp [zDigit, hne] at h

theorem zOrb_nonneg (ξ : ℝ) (n : ℕ) : 0 ≤ zOrb ξ n :=
  mul_nonneg (by norm_num) (Int.fract_nonneg _)

theorem zOrb_lt_one {ξ : ℝ} (hξ : Bugeaud.IsZNumber ξ) (n : ℕ) : zOrb ξ n < 1 := by
  have := hξ.2 n
  simp only [zOrb]
  linarith

/-- The step relation in Flatto's coordinate: `rₙ₊₁ = (3/2) rₙ - εₙ`, i.e. the greedy `β = 3/2`
transformation with digit `εₙ`. -/
@[category API, AMS 11 37, ref "Fla92" "Bug12", group "mahler_z_counting"]
theorem zOrb_succ {ξ : ℝ} (hξ : Bugeaud.IsZNumber ξ) (n : ℕ) :
    zOrb ξ (n + 1) = 3 * zOrb ξ n / 2 - (Bugeaud.zParity ξ n : ℝ) := by
  have h := Bugeaud.three_zFrac hξ n
  simp only [zOrb, Bugeaud.zParity]
  linarith

/-- The digit is the greedy one: it is `1` exactly when the orbit point has reached the branch
point `2/3`. -/
@[category API, AMS 11 37, ref "Fla92", group "mahler_z_counting", formal_uses zOrb_succ]
theorem zDigit_true_iff {ξ : ℝ} (hξ : Bugeaud.IsZNumber ξ) (n : ℕ) :
    zDigit ξ n = true ↔ 2 / 3 ≤ zOrb ξ n := by
  constructor
  · intro h
    have h1 := zParity_eq_one_of_zDigit_true h
    have hs := zOrb_succ hξ n
    rw [h1] at hs
    have := zOrb_nonneg ξ (n + 1)
    push_cast at hs
    linarith
  · intro h
    by_contra hd
    have h0 : Bugeaud.zParity ξ n = 0 := zParity_eq_zero_of_zDigit_false (by simpa using hd)
    have hs := zOrb_succ hξ n
    rw [h0] at hs
    have := zOrb_lt_one hξ (n + 1)
    push_cast at hs
    linarith

/-- **[Fla92] Proposition P, the direction that counts.**  The parity word of a Z-number is an
admissible `β`-expansion word, and the orbit point sits strictly inside its cylinder image.

The second clause is the induction's engine: it is what lets the next digit be read off. -/
@[category API, AMS 11 37, ref "Fla92" "Bug12", group "mahler_z_counting",
  formal_uses zOrb_succ zOrb_lt_one zOrb_nonneg]
theorem isGreedyOrbit_zOrb {ξ : ℝ} (hξ : Bugeaud.IsZNumber ξ) :
    IsGreedyOrbit (zOrb ξ) (zDigit ξ) := by
  refine ⟨fun n => ⟨zOrb_nonneg ξ n, zOrb_lt_one hξ n⟩, fun n => ?_⟩
  have hs := zOrb_succ hξ n
  cases hd : zDigit ξ n with
  | false =>
    rw [zParity_eq_zero_of_zDigit_false hd] at hs
    simpa [hd] using hs
  | true =>
    rw [zParity_eq_one_of_zDigit_true hd] at hs
    simpa [hd] using hs

@[category research solved, AMS 11 37, ref "Fla92" "Mahler68", group "mahler_z_counting",
  formal_uses orbWord_mem_adm isGreedyOrbit_zOrb]
theorem zWord_mem_adm {ξ : ℝ} (hξ : Bugeaud.IsZNumber ξ) :
    ∀ k : ℕ, zWord ξ k ∈ adm k ∧ zOrb ξ k < ((endAfter (zWord ξ k) : ℚ) : ℝ) :=
  orbWord_mem_adm (isGreedyOrbit_zOrb hξ)

/-! ### The word determines the integer part

[Fla92] Theorem 3.1 for `q = 2`, in the only direction needed: the length-`k` parity word pins
`⌊ξ⌋` modulo `2^k`.  The mechanism is `Bugeaud.floor_step` (`2 g_{n+1} = 3 g_n + ε_n`): equal digits
make the difference `d_n = g_n - g'_n` satisfy `2 d_{n+1} = 3 d_n`, whence `3^k d_0 = 2^k d_k` and
`2^k ∣ d_0` by coprimality. -/

theorem zWord_length (ξ : ℝ) : ∀ k : ℕ, (zWord ξ k).length = k := by
  intro k; induction k with
  | zero => rfl
  | succ k ih => simp [ih]

/-- Equal words mean equal digits. -/
theorem zDigit_eq_of_zWord_eq {ξ ξ' : ℝ} :
    ∀ (k : ℕ), zWord ξ k = zWord ξ' k → ∀ i < k, zDigit ξ i = zDigit ξ' i :=
  orbWord_inj_digits

/-- `3^n (g₀ - g₀') = 2^n (gₙ - gₙ')` whenever the first `n` digits agree. -/
@[category API, AMS 11 37, ref "Fla92" "Bug12", group "mahler_z_counting"]
theorem pow_mul_floor_sub {ξ ξ' : ℝ} (hξ : Bugeaud.IsZNumber ξ) (hξ' : Bugeaud.IsZNumber ξ')
    {k : ℕ} (h : ∀ i < k, zDigit ξ i = zDigit ξ' i) :
    ∀ n ≤ k, (3 : ℤ) ^ n * (⌊ξ⌋ - ⌊ξ'⌋)
      = 2 ^ n * (⌊ξ * (3 / 2) ^ n⌋ - ⌊ξ' * (3 / 2) ^ n⌋) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have hnk : n < k := hn
    have hpar : Bugeaud.zParity ξ n = Bugeaud.zParity ξ' n := by
      rcases Bool.eq_false_or_eq_true (zDigit ξ n) with hd | hd
      · rw [zParity_eq_one_of_zDigit_true hd,
          zParity_eq_one_of_zDigit_true (by rw [← h n hnk]; exact hd)]
      · rw [zParity_eq_zero_of_zDigit_false hd,
          zParity_eq_zero_of_zDigit_false (by rw [← h n hnk]; exact hd)]
    have e1 := Bugeaud.floor_step hξ n
    have e2 := Bugeaud.floor_step hξ' n
    simp only [Bugeaud.zParity] at hpar
    have ihn := ih (Nat.le_of_lt hn)
    have key : 2 * (⌊ξ * (3 / 2) ^ (n + 1)⌋ - ⌊ξ' * (3 / 2) ^ (n + 1)⌋)
        = 3 * (⌊ξ * (3 / 2) ^ n⌋ - ⌊ξ' * (3 / 2) ^ n⌋) := by
      rw [hpar] at e1; omega
    calc (3 : ℤ) ^ (n + 1) * (⌊ξ⌋ - ⌊ξ'⌋)
        = 3 * (3 ^ n * (⌊ξ⌋ - ⌊ξ'⌋)) := by ring
      _ = 3 * (2 ^ n * (⌊ξ * (3 / 2) ^ n⌋ - ⌊ξ' * (3 / 2) ^ n⌋)) := by rw [ihn]
      _ = 2 ^ n * (3 * (⌊ξ * (3 / 2) ^ n⌋ - ⌊ξ' * (3 / 2) ^ n⌋)) := by ring
      _ = 2 ^ n * (2 * (⌊ξ * (3 / 2) ^ (n + 1)⌋ - ⌊ξ' * (3 / 2) ^ (n + 1)⌋)) := by rw [key]
      _ = 2 ^ (n + 1) * (⌊ξ * (3 / 2) ^ (n + 1)⌋ - ⌊ξ' * (3 / 2) ^ (n + 1)⌋) := by ring

/-- **[Fla92] Theorem 3.1, `q = 2`.**  The length-`k` parity word determines `⌊ξ⌋` mod `2^k`. -/
@[category research solved, AMS 11 37, ref "Fla92", group "mahler_z_counting",
  formal_uses pow_mul_floor_sub zDigit_eq_of_zWord_eq]
theorem pow_two_dvd_floor_sub {ξ ξ' : ℝ} (hξ : Bugeaud.IsZNumber ξ) (hξ' : Bugeaud.IsZNumber ξ')
    {k : ℕ} (hw : zWord ξ k = zWord ξ' k) : (2 : ℤ) ^ k ∣ ⌊ξ⌋ - ⌊ξ'⌋ := by
  have hid := pow_mul_floor_sub hξ hξ' (zDigit_eq_of_zWord_eq k hw) k le_rfl
  have hdvd : (2 : ℤ) ^ k ∣ 3 ^ k * (⌊ξ⌋ - ⌊ξ'⌋) := ⟨_, hid⟩
  have hcop : IsCoprime ((2 : ℤ) ^ k) ((3 : ℤ) ^ k) := (IsCoprime.pow (⟨-1, 1, by ring⟩))
  exact hcop.dvd_of_dvd_mul_left hdvd

/-! ## 9.  T-B10.1: Flatto's bound on the number of Z-numbers

Assembling: the parity word of a Z-number below `2^k` is admissible (§8), and it determines the
number, because it determines `⌊ξ⌋` mod `2^k` — hence `⌊ξ⌋` itself, since `0 ≤ ⌊ξ⌋ < 2^k` — and
`⌊ξ⌋` determines the Z-number by Mahler's first theorem (`Bugeaud.eq_of_floor_eq`). -/

/-- The parity word is injective on Z-numbers below `2^k`. -/
@[category research solved, AMS 11 37, ref "Fla92" "Mahler68", group "mahler_z_counting",
  formal_uses pow_two_dvd_floor_sub]
theorem eq_of_zWord_eq {ξ ξ' : ℝ} (hξ : Bugeaud.IsZNumber ξ) (hξ' : Bugeaud.IsZNumber ξ')
    {k : ℕ} (hb : ξ < 2 ^ k) (hb' : ξ' < 2 ^ k) (hw : zWord ξ k = zWord ξ' k) : ξ = ξ' := by
  have hfl : ∀ {η : ℝ}, Bugeaud.IsZNumber η → η < 2 ^ k → 0 ≤ ⌊η⌋ ∧ ⌊η⌋ < (2 : ℤ) ^ k := by
    intro η hη hηb
    refine ⟨Int.floor_nonneg.mpr hη.1.le, ?_⟩
    rw [Int.floor_lt]
    push_cast
    exact hηb
  obtain ⟨h0, h1⟩ := hfl hξ hb
  obtain ⟨h0', h1'⟩ := hfl hξ' hb'
  refine Bugeaud.eq_of_floor_eq hξ hξ' ?_
  by_contra hne
  have hd : ⌊ξ⌋ - ⌊ξ'⌋ ≠ 0 := sub_ne_zero.mpr hne
  have hle : (2 : ℤ) ^ k ≤ |⌊ξ⌋ - ⌊ξ'⌋| :=
    Int.le_of_dvd (abs_pos.mpr hd) ((dvd_abs _ _).mpr (pow_two_dvd_floor_sub hξ hξ' hw))
  have habs : |⌊ξ⌋ - ⌊ξ'⌋| < (2 : ℤ) ^ k := by
    rw [abs_lt]; constructor <;> linarith
  linarith

/-- **T-B10.1.**  Flatto's count with an explicit constant: at most `3 (3/2)^k - 2` Z-numbers lie
below `2^k`, i.e. `#Z(x) ≤ 3 x^{log₂(3/2)}` — [Fla92] Theorem 6.1, machine-checked, with the
constant made explicit.

Stated for an arbitrary finite set of Z-numbers below `2^k`, which needs no prior knowledge that
the Z-set is finite (it is: by Mahler's first theorem it injects into `ℤ`). -/
@[category research solved, AMS 11 37, ref "Fla92" "Mahler68", group "mahler_z_counting",
  formal_uses eq_of_zWord_eq zWord_mem_adm pCount_le]
theorem card_zNumbers_le (k : ℕ) (S : Finset ℝ)
    (hS : ∀ ξ ∈ S, Bugeaud.IsZNumber ξ ∧ ξ < 2 ^ k) :
    S.card ≤ pCount k := by
  refine Finset.card_le_card_of_injOn (fun ξ => zWord ξ k) (fun ξ hξ => ?_) (fun ξ hξ ξ' hξ' h => ?_)
  · exact (zWord_mem_adm (hS ξ hξ).1 k).1
  · exact eq_of_zWord_eq (hS ξ hξ).1 (hS ξ' hξ').1 (hS ξ hξ).2 (hS ξ' hξ').2 h

/-- The same in Flatto's numerical form. -/
@[category research solved, AMS 11 37, ref "Fla92" "Mahler68", group "mahler_z_counting",
  formal_uses card_zNumbers_le pCount_le]
theorem card_zNumbers_le_flatto (k : ℕ) (S : Finset ℝ)
    (hS : ∀ ξ ∈ S, Bugeaud.IsZNumber ξ ∧ ξ < 2 ^ k) :
    (S.card : ℚ) ≤ 3 * (3 / 2 : ℚ) ^ k - 2 :=
  le_trans (by exact_mod_cast card_zNumbers_le k S hS) (pCount_le k)

/-- **T-B10.2, the horizon wall.**  The horizon-`k` candidate count is pinned on both sides by
`(3/2)^k`.  Hence no bound derived at horizon `k = log₂ x` can produce an exponent below
`log₂(3/2)`: Flatto is optimal there.  (WP0: this is a consequence of [Fla92] Theorem 4.3, whose
exact constant is `3/σ = 1.5510…`; what is new here is the elementary proof and the
machine-checking.) -/
@[category research solved, AMS 11 37, ref "Fla92", group "mahler_z_counting",
  formal_uses le_pCount pCount_le]
theorem pCount_two_sided (k : ℕ) :
    (3 / 2 : ℚ) ^ k ≤ pCount k ∧ (pCount k : ℚ) ≤ 3 * (3 / 2 : ℚ) ^ k - 2 :=
  ⟨le_pCount k, pCount_le k⟩

/-- The conventions note's §0.4 bridge, recorded now that there is a consumer: the FLP `Z`-set at
`(p,q) = (3,2)` on the window `[0, 1/2)` is exactly the set of Mahler Z-numbers. -/
@[category API, AMS 11 37, ref "Fla92" "Mahler68" "FLP95", group "mahler_z_counting"]
theorem zSet_eq : FLP.ZSet 3 2 0 (1 / 2) = {ξ : ℝ | Bugeaud.IsZNumber ξ} := by
  have hpq : ((3 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) = 3 / 2 := by norm_num
  ext ξ
  simp only [FLP.ZSet, Bugeaud.IsZNumber, Set.mem_ofPred_eq, Set.mem_Ico, hpq, zero_add]
  exact ⟨fun ⟨h0, h⟩ => ⟨h0, fun n => (h n).2⟩,
    fun ⟨h0, h⟩ => ⟨h0, fun n => ⟨Int.fract_nonneg _, h n⟩⟩⟩

/-! ## 10.  Realizability: every admissible word actually occurs

Part 1 never needed a point inside a cylinder — the endpoint recursion sufficed.  The *lower* bound
on the model language does need one.  Given a word `w` and a target `z`, `pull` inverts the branch
`r ↦ (3/2) r - b`; its back-recursion `pull (w ++ [b]) z = pull w (2 (z + b) / 3)` matches the way
`adm` is built by appending, so the verification is a single induction over the stages. -/

/-- A digit as a rational, `0` or `1`.  Naming it avoids repeated `ite`-on-`Bool` unfolding. -/
def dval (b : Bool) : ℚ := if b then 1 else 0

@[simp] theorem dval_false : dval false = 0 := ite_eq_right Bool.false_ne_true
@[simp] theorem dval_true : dval true = 1 := ite_eq_left rfl

theorem dval_nonneg (b : Bool) : 0 ≤ dval b := by cases b <;> simp

theorem cast_dval (b : Bool) : ((dval b : ℚ) : ℝ) = if b then 1 else 0 := by cases b <;> simp

/-- The greedy digit of `r`. -/
def gdigit (r : ℚ) : Bool := 2 / 3 ≤ r

/-- The greedy `β = 3/2` map, as an exact map on `ℚ`. -/
def gstep (r : ℚ) : ℚ := 3 * r / 2 - dval (gdigit r)

/-- The length-`k` itinerary of `r`. -/
def itin (r : ℚ) : ℕ → List Bool := orbWord fun k => gdigit (gstep^[k] r)

/-- The point whose itinerary is `w` and which lands on `z` after `|w|` steps. -/
def pull : List Bool → ℚ → ℚ
  | [], z => z
  | b :: w, z => 2 * (pull w z + dval b) / 3

theorem gdigit_eq_true {r : ℚ} (h : 2 / 3 ≤ r) : gdigit r = true := by simpa [gdigit] using h

theorem gdigit_eq_false {r : ℚ} (h : r < 2 / 3) : gdigit r = false := by
  simpa [gdigit] using not_le.mpr h

theorem pull_concat (b : Bool) : ∀ (w : List Bool) (z : ℚ),
    pull (w ++ [b]) z = pull w (2 * (z + dval b) / 3) := by
  intro w
  induction w with
  | nil => intro z; simp [pull]
  | cons c w ih => intro z; simp [pull, ih]

/-- The pulled-back target reads back the intended digit. -/
theorem gdigit_pull_one {z : ℚ} (b : Bool) (hz0 : 0 ≤ z) (hz1 : z < 1) :
    gdigit (2 * (z + dval b) / 3) = b := by
  cases b with
  | false => rw [dval_false]; exact gdigit_eq_false (by linarith)
  | true => rw [dval_true]; exact gdigit_eq_true (by linarith)

/-- ... and one greedy step undoes the pull-back. -/
theorem gstep_pull_one {z : ℚ} (b : Bool) (hz0 : 0 ≤ z) (hz1 : z < 1) :
    gstep (2 * (z + dval b) / 3) = z := by
  rw [gstep, gdigit_pull_one b hz0 hz1]
  cases b with
  | false => rw [dval_false]; ring
  | true => rw [dval_true]; ring

/-- The greedy map keeps `[0,1)` invariant. -/
theorem gstep_mem {r : ℚ} (h0 : 0 ≤ r) (h1 : r < 1) : 0 ≤ gstep r ∧ gstep r < 1 := by
  rw [gstep]
  by_cases h : (2 : ℚ) / 3 ≤ r
  · rw [gdigit_eq_true h, dval_true]; constructor <;> linarith
  · rw [gdigit_eq_false (not_le.mp h), dval_false]
    constructor <;> [linarith; skip]
    have := not_le.mp h
    linarith

theorem gstep_iterate_mem {r : ℚ} (h0 : 0 ≤ r) (h1 : r < 1) :
    ∀ n, 0 ≤ gstep^[n] r ∧ gstep^[n] r < 1 := by
  intro n
  induction n with
  | zero => exact ⟨h0, h1⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact gstep_mem ih.1 ih.2

/-- **Realizability.**  Every admissible word is the itinerary of an explicit rational point of
`[0,1)`, which moreover can be made to land on any prescribed target below the cylinder's
endpoint. -/
@[category research solved, AMS 11 37, ref "Fla92", group "mahler_z_counting",
  formal_uses pull_concat gdigit_pull_one gstep_pull_one endAfter_mem_Ioc]
theorem pull_realizes : ∀ (k : ℕ) (w : List Bool), w ∈ adm k → ∀ z : ℚ, 0 ≤ z → z < endAfter w →
    itin (pull w z) k = w ∧ gstep^[k] (pull w z) = z ∧ 0 ≤ pull w z ∧ pull w z < 1 := by
  intro k
  induction k with
  | zero =>
    intro w hw z hz0 hz1
    rw [adm_zero, Finset.mem_singleton] at hw
    subst hw
    rw [endAfter_nil] at hz1
    exact ⟨rfl, rfl, hz0, hz1⟩
  | succ k ih =>
    intro w' hw' z hz0 hz1
    rw [adm_succ, Finset.mem_biUnion] at hw'
    obtain ⟨w, hw, hmem⟩ := hw'
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hmem
    obtain ⟨hR0, hR1⟩ := endAfter_mem_Ioc k w hw
    rw [endAfter_concat] at hz1
    -- the target is below `1`, whichever branch was taken
    have hz1' : z < 1 := by
      cases b with
      | false => exact lt_of_lt_of_le hz1 (by rw [step_false]; exact min_le_right _ _)
      | true => rw [step_true] at hz1; linarith
    set z' : ℚ := 2 * (z + dval b) / 3 with hz'
    have hz'0 : 0 ≤ z' := by
      rw [hz']
      have := dval_nonneg b
      linarith
    have hz'R : z' < endAfter w := by
      rw [hz']
      cases b with
      | false =>
        rw [step_false] at hz1
        have := lt_of_lt_of_le hz1 (min_le_left _ _)
        rw [dval_false]
        linarith
      | true =>
        rw [step_true] at hz1
        rw [dval_true]
        linarith
    obtain ⟨hitin, hland, hp0, hp1⟩ := ih w hw z' hz'0 hz'R
    rw [pull_concat]
    refine ⟨?_, ?_, hp0, hp1⟩
    · show itin (pull w z') (k + 1) = w ++ [b]
      rw [itin, orbWord_succ]
      rw [show orbWord (fun i => gdigit (gstep^[i] (pull w z'))) k = itin (pull w z') k from rfl,
        hitin, hland, gdigit_pull_one b hz0 hz1']
    · rw [Function.iterate_succ_apply', hland, gstep_pull_one b hz0 hz1']

/-- The forward greedy orbit of a rational point of `[0,1)` is a greedy orbit in the abstract
sense — the bridge from §10 back to §8. -/
@[category API, AMS 11 37, ref "Fla92", group "mahler_z_counting", formal_uses gstep_iterate_mem]
theorem isGreedyOrbit_gstep {r : ℚ} (h0 : 0 ≤ r) (h1 : r < 1) :
    IsGreedyOrbit (fun n => ((gstep^[n] r : ℚ) : ℝ)) (fun n => gdigit (gstep^[n] r)) := by
  refine ⟨fun n => ?_, fun n => ?_⟩
  · simp only [Set.mem_Ico]
    obtain ⟨ha, hb⟩ := gstep_iterate_mem h0 h1 n
    exact ⟨by exact_mod_cast ha, by exact_mod_cast hb⟩
  · show ((gstep^[n + 1] r : ℚ) : ℝ)
      = 3 * ((gstep^[n] r : ℚ) : ℝ) / 2 - (if gdigit (gstep^[n] r) then 1 else 0)
    rw [Function.iterate_succ_apply', ← cast_dval]
    show ((gstep (gstep^[n] r) : ℚ) : ℝ) = _
    rw [gstep]
    push_cast
    ring

/-! ## 11.  `φ_model` at the Z-cell equals `log (3/2)`

The last item of WP2: the survivor-subshift entropy of `Z32.ModelEntropy` at the Z-window is
*exactly* `log (3/2)`, so any transfer-operator enclosure on the carry model converges to `3/2`
from above.  Both halves of §7 are needed, and this is where realizability (§10) earns its keep.

The route is an exact identity — `Nat.card (modelLang 3 2 zCell n) = pCount n` — obtained by
showing that `vecWord` is a bijection from the model language onto the admissible words. -/

/-- The Z-window in the `y`-coordinate: `{y | 0 ≤ y < 1/2}`. -/
def zCell : Set ℝ := Set.Ico 0 (1 / 2)

/-- The digit word attached to a length-`n` carry vector.  The out-of-range extension is irrelevant:
`orbWord _ n` reads only the first `n` digits (`orbWord_congr`). -/
def vecWord {n : ℕ} (v : Fin n → ℤ) : List Bool :=
  orbWord (fun i => if h : i < n then decide (v ⟨i, h⟩ = 1) else false) n

theorem vecWord_eq {n : ℕ} (v : Fin n → ℤ) (s : ℕ → ℤ) (h : ∀ i : Fin n, s i = v i) :
    vecWord v = orbWord (fun i => decide (s i = 1)) n := by
  refine (orbWord_congr n fun i hi => ?_).symm
  rw [dite_eq_left hi, h ⟨i, hi⟩]

/-- The vector is recovered from its word, given that the carries are `{0,1}`. -/
theorem vecWord_injective {n : ℕ} {v v' : Fin n → ℤ}
    (hv : ∀ i, v i = 0 ∨ v i = 1) (hv' : ∀ i, v' i = 0 ∨ v' i = 1)
    (h : vecWord v = vecWord v') : v = v' := by
  funext i
  have hd := orbWord_inj_digits n h i i.isLt
  rw [dite_eq_left i.isLt, dite_eq_left i.isLt] at hd
  have hi : (⟨(i : ℕ), i.isLt⟩ : Fin n) = i := rfl
  rw [hi] at hd
  rcases hv i with h0 | h1
  · rcases hv' i with h0' | h1'
    · rw [h0, h0']
    · rw [h0, h1'] at hd; simp at hd
  · rcases hv' i with h0' | h1'
    · rw [h1, h0'] at hd; simp at hd
    · rw [h1, h1']

/-- On the Z-window the model carries are forced into `{0,1}` and the doubled orbit is a greedy
orbit: this is F1 of plan-B10 ("on the Z-window the carry is forced"). -/
@[category research solved, AMS 11 37, ref "Fla92" "Dub09AA", group "mahler_z_counting"]
theorem isGreedyOrbit_of_isModelOrbit {y : ℕ → ℝ} {s : ℕ → ℤ}
    (h : IsModelOrbit 3 2 zCell y s) :
    (∀ i, s i = 0 ∨ s i = 1) ∧
      IsGreedyOrbit (fun i => 2 * y i) (fun i => decide (s i = 1)) := by
  obtain ⟨hU, -, hrec⟩ := h
  have hIco : ∀ i, 0 ≤ y i ∧ y i < 1 / 2 := fun i => ⟨(hU i).1, (hU i).2⟩
  have hrel : ∀ i, (s i : ℝ) = 3 * y i - 2 * y (i + 1) := by
    intro i
    have := hrec i
    push_cast at this
    linarith
  have hzo : ∀ i, s i = 0 ∨ s i = 1 := by
    intro i
    obtain ⟨ha, hb⟩ := hIco i
    obtain ⟨ha', hb'⟩ := hIco (i + 1)
    have h1 : (-1 : ℝ) < (s i : ℝ) := by rw [hrel i]; linarith
    have h2 : (s i : ℝ) < 2 := by rw [hrel i]; linarith
    have h1' : (-1 : ℤ) < s i := by exact_mod_cast h1
    have h2' : s i < 2 := by exact_mod_cast h2
    omega
  refine ⟨hzo, fun i => ?_, fun i => ?_⟩
  · exact ⟨by linarith [(hIco i).1], by linarith [(hIco i).2]⟩
  · have hcast : ((if decide (s i = 1) then 1 else 0 : ℝ)) = (s i : ℝ) := by
      rcases hzo i with h0 | h1
      · rw [h0]; norm_num
      · rw [h1]; norm_num
    rw [hcast, hrel i]
    ring

/-- Every admissible word is realised by a model orbit confined to the Z-cell. -/
@[category research solved, AMS 11 37, ref "Fla92", group "mahler_z_counting",
  formal_uses pull_realizes isGreedyOrbit_gstep endAfter_mem_Ioc]
theorem exists_isModelOrbit {k : ℕ} {w : List Bool} (hw : w ∈ adm k) :
    ∃ (y : ℕ → ℝ) (s : ℕ → ℤ), IsModelOrbit 3 2 zCell y s ∧
      (∀ i, s i = 0 ∨ s i = 1) ∧ orbWord (fun i => decide (s i = 1)) k = w := by
  obtain ⟨hR0, -⟩ := endAfter_mem_Ioc k w hw
  obtain ⟨hitin, -, hp0, hp1⟩ := pull_realizes k w hw 0 le_rfl hR0
  set r : ℚ := pull w 0 with hr
  refine ⟨fun i => ((gstep^[i] r : ℚ) : ℝ) / 2, fun i => if gdigit (gstep^[i] r) then 1 else 0,
    ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩, fun i => ?_, ?_⟩
  · obtain ⟨ha, hb⟩ := gstep_iterate_mem hp0 hp1 i
    have ha' : (0 : ℝ) ≤ ((gstep^[i] r : ℚ) : ℝ) := by exact_mod_cast ha
    have hb' : ((gstep^[i] r : ℚ) : ℝ) < 1 := by exact_mod_cast hb
    exact ⟨by linarith, by linarith⟩
  · obtain ⟨ha, hb⟩ := gstep_iterate_mem hp0 hp1 i
    have ha' : (0 : ℝ) ≤ ((gstep^[i] r : ℚ) : ℝ) := by exact_mod_cast ha
    have hb' : ((gstep^[i] r : ℚ) : ℝ) < 1 := by exact_mod_cast hb
    exact ⟨by linarith, by linarith⟩
  · have hg : gstep^[i + 1] r = 3 * gstep^[i] r / 2 - dval (gdigit (gstep^[i] r)) := by
      rw [Function.iterate_succ_apply']; rfl
    have hcast : ((if gdigit (gstep^[i] r) then (1 : ℤ) else 0 : ℤ) : ℝ)
        = ((dval (gdigit (gstep^[i] r)) : ℚ) : ℝ) := by
      cases gdigit (gstep^[i] r) <;> norm_num
    rw [hcast]
    have : ((gstep^[i + 1] r : ℚ) : ℝ)
        = 3 * ((gstep^[i] r : ℚ) : ℝ) / 2 - ((dval (gdigit (gstep^[i] r)) : ℚ) : ℝ) := by
      rw [hg]; push_cast; ring
    push_cast
    linarith
  · cases gdigit (gstep^[i] r) <;> simp
  · have hdig : ∀ i : ℕ,
        (decide ((if gdigit (gstep^[i] r) then (1 : ℤ) else 0) = 1)) = gdigit (gstep^[i] r) := by
      intro i; cases gdigit (gstep^[i] r) <;> simp
    rw [funext hdig]
    exact hitin

/-- **`Z_k = p(k)` in the entropy currency**: the model language at the Z-cell has exactly `p k`
words of length `k`. -/
@[category research solved, AMS 11 37, ref "Fla92" "Dub09AA", group "mahler_z_counting",
  formal_uses isGreedyOrbit_of_isModelOrbit exists_isModelOrbit orbWord_mem_adm vecWord_injective]
theorem card_modelLang_zCell (n : ℕ) :
    Nat.card (modelLang 3 2 zCell n) = pCount n := by
  classical
  -- every language word has `{0,1}` letters, and its digit word is admissible
  have hzo : ∀ v : modelLang 3 2 zCell n, ∀ i, v.1 i = 0 ∨ v.1 i = 1 := by
    intro v i
    obtain ⟨y, s, horb, hval⟩ := v.2
    obtain ⟨h01, -⟩ := isGreedyOrbit_of_isModelOrbit horb
    rw [← hval i]
    exact h01 i
  have hmap : ∀ v : modelLang 3 2 zCell n, vecWord v.1 ∈ adm n := by
    intro v
    obtain ⟨y, s, horb, hval⟩ := v.2
    obtain ⟨-, hgr⟩ := isGreedyOrbit_of_isModelOrbit horb
    rw [vecWord_eq v.1 s hval]
    exact (orbWord_mem_adm hgr n).1
  refine Eq.trans (Nat.card_eq_of_bijective
    (fun v => (⟨vecWord v.1, hmap v⟩ : {w // w ∈ adm n})) ⟨?_, ?_⟩) ?_
  · intro v v' h
    exact Subtype.ext (vecWord_injective (hzo v) (hzo v') (congrArg Subtype.val h))
  · intro w
    obtain ⟨y, s, horb, h01, hword⟩ := exists_isModelOrbit w.2
    have hmem : (fun i : Fin n => s (i : ℕ)) ∈ modelLang 3 2 zCell n :=
      ⟨y, s, horb, fun _ => rfl⟩
    refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
    show vecWord (fun i : Fin n => s (i : ℕ)) = (w : List Bool)
    rw [vecWord_eq _ s fun _ => rfl]
    exact hword
  · simp [pCount, Nat.card_eq_fintype_card]

/-- **The Z-cell has model entropy exactly `log (3/2)`.**  With T-B10.2 this is the wall in the
`Z32.phiModel` currency: any transfer-operator enclosure on the carry model converges to `3/2` from
above, so no such bound yields an exponent below `log₂ (3/2)`. -/
@[category research solved, AMS 11 37, ref "Fla92" "Dub09AA", group "mahler_z_counting",
  formal_uses card_modelLang_zCell le_pCount pCount_le]
theorem phiModel_zCell : phiModel 3 2 zCell = Real.log (3 / 2) := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < pCount n := by
    intro n
    have := le_pCount n
    have h1 : ((3 / 2 : ℚ) ^ n : ℚ) ≤ (pCount n : ℚ) := this
    have h2 : (0 : ℚ) < (3 / 2 : ℚ) ^ n := by positivity
    have : (0 : ℚ) < (pCount n : ℚ) := lt_of_lt_of_le h2 h1
    exact_mod_cast this
  have hlow : ∀ n : ℕ, 1 ≤ n → Real.log (3 / 2) ≤ Real.log (pCount n) / n := by
    intro n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hle : ((3 : ℝ) / 2) ^ n ≤ (pCount n : ℝ) := by
      have h := le_pCount n
      have h' : (((3 / 2 : ℚ) ^ n : ℚ) : ℝ) ≤ ((pCount n : ℚ) : ℝ) := by exact_mod_cast h
      push_cast at h'
      exact h'
    have := Real.log_le_log (by positivity) hle
    rw [Real.log_pow] at this
    rw [le_div_iff₀ hnR]
    linarith
  have hhigh : ∀ n : ℕ, 1 ≤ n → Real.log (pCount n) / n ≤ Real.log (3 / 2) + Real.log 3 / n := by
    intro n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hle : (pCount n : ℝ) ≤ 3 * ((3 : ℝ) / 2) ^ n := by
      have h := pCount_le n
      have h' : ((pCount n : ℚ) : ℝ) ≤ ((3 * (3 / 2 : ℚ) ^ n - 2 : ℚ) : ℝ) := by exact_mod_cast h
      push_cast at h'
      linarith
    have hlog := Real.log_le_log (hpos n) hle
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlog
    rw [div_le_iff₀ hnR]
    have : Real.log 3 / n * n = Real.log 3 := by field_simp
    rw [add_mul, this]
    linarith
  have hlim : Filter.Tendsto (fun n : ℕ => Real.log (pCount n) / n) Filter.atTop
      (nhds (Real.log (3 / 2))) := by
    have hc : Filter.Tendsto (fun n : ℕ => Real.log (3 / 2) + Real.log 3 / n) Filter.atTop
        (nhds (Real.log (3 / 2))) := by
      have := tendsto_const_div_atTop_nhds_zero_nat (Real.log 3)
      simpa using Filter.Tendsto.const_add (Real.log (3 / 2)) this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hc ?_ ?_
    · exact Filter.eventually_atTop.mpr ⟨1, fun n hn => hlow n hn⟩
    · exact Filter.eventually_atTop.mpr ⟨1, fun n hn => hhigh n hn⟩
  have : phiModel 3 2 zCell
      = Filter.limsup (fun n : ℕ => Real.log (pCount n) / n) Filter.atTop := by
    simp only [phiModel, card_modelLang_zCell]
  rw [this]
  exact hlim.limsup_eq

end Flatto
end Z32
