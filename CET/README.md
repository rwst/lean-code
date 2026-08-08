<!-- (C) 2026 Ralf Stephan, in collaboration with Claude Code. Released under CC0 1.0 Universal.
     The Lean files in this directory are NOT CC0 — see the per-file Apache-2.0 headers. -->

# `CET/` — third-party port

Reusable Lean lifted from **`shaikidris/CET` v2.0.1** (Apache-2.0, © Idris Ali Shaik),
adapted from Lean 4.15.0 to this corpus's toolchain (4.32.0-rc1). Every file keeps its
upstream copyright header; each records its original path and what the adaptation changed.

Registered in `lakefile.lean` as `lean_lib CET` (build-only). Extract `corpusRoots`
registration and `theoremdb.json` regeneration are the user's call.

Build: `LEAN_NUM_THREADS=3 lake build CET` — clean, zero warnings, all results std3
(`propext`, `Classical.choice`, `Quot.sound`), no cited axioms.

## What is here

**(a) `(C,D)`-density and dyadic shells** — the corpus had no natural-density API at all.

| file | contents |
|---|---|
| `QuantitativeDensity.lean` | `positivePrefix`, `badPrefix`, `IsCDDense S C D` (⇔ `#(Sᶜ ∩ [1,N]) ≤ C·N^(1−D)`, Inselmann arXiv:2402.03276 Def. 2.6) and its closure lemmas: `mono_constant`, `mono_set`, `degrade_exponent`, `inter` |
| `ShellToGlobalDensity.lean` | `dyadicShell M = [2^M, 2^(M+1))`, `shellBad`, and `isCDDense_of_shell_bound`: a per-shell exceptional fraction `≤ K·exp(−cM)` with `c < log 2` becomes prefix density with `D = c/log 2`, `C = 2K/(2e^{−c}−1)`. Explicit constants, geometric series summed exactly, no asymptotics |
| `VaryingShellDensity.lean` | `HasNaturalDensityOne`, `assembleDyadic`, `shellExceptionalRatio`, and `hasNaturalDensityOne_assembleDyadic`: shellwise good sets with vanishing exceptional ratio assemble to a density-one set (the varying-rate version a fixed `(C,D)` theorem cannot give) |

**(b) Syracuse numerators on compositions** — the mathematically interesting layer.

| file | contents |
|---|---|
| `SyracuseComposition.lean` | `syracuseNumerator` on `Composition N` via `A(k₁,…,kₛ) = 3^{s−1} + 2^{k₁}A(k₂,…,kₛ)`, and `syracuseNumerator_injective_on_length`: at fixed total **and** fixed part count, distinct positive compositions have distinct numerators. The proof reads the first part off the exact 2-adic valuation and recovers the last from the total |
| `ResidueFiberMoment.lean` | `residueFiber W A m a`, `quotient_injective_on_residueFiber`, and `residueFibers_critical_bound`: the spacing argument — `k` distinct lifts in one class mod `m` force quotients `0,…,k−1`, hence `√m·Σ_a fib_a^{3/2} ≤ 4·Σ_x √(m + A x)`. Stated for an arbitrary injective `A : α → ℕ`, so it is reusable well beyond Collatz |

## What is deliberately *not* here

- **Their Terras parity bijection.** We already have `CC.terras_bijection` / `CC.terras_forward'`
  (used by `BL/ParityVectorMap.lean`). Porting it would duplicate.
- **Their binomial-tail file**, which sits on that bijection — it went to **`CC/BinomialTail.lean`**
  instead (namespace `CC.ParityTail`), rewired onto `CC.parityVec` / `CC.terras_bijection` with word
  weight over `ZMod 2` rather than `Bool`. Gives `#{r : ZMod (2^k) | oddCount k r = j} = choose k j`
  exactly, and Hoeffding-type tails `≤ 2^k·exp(−2t²k)` on both sides.
- **The endpoint-transport bootstrap** (`EndpointDensityStep`, `collatzPullback_dense_centralRenyi`,
  and the ~90 files above them) and its headline claim: natural density one for
  `min_k T^k(n) ≤ exp((log n)^{1−δ})`, `δ < log(1/a₀)/log(2/a₀) ≈ 0.2512`, `a₀ = log₄3`.
  That claim is **unverified here** — it would strictly beat Korec 1994, the best known
  *natural*-density Collatz result, in the regime Tao 2019 had to abandon natural density
  to enter. See `plans/report2-weyl.html` §4.4 (ground rule **GR5**, the transport test).

The files above are independent of that claim: they are the infrastructure it is built
*on*, and each is a self-contained statement about densities or compositions.
