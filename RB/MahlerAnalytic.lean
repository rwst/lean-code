/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import RB.Basic
import RB.MahlerExamples
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Matrix.Mul
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The analytic Mahler system of an automatic sequence (plan-formalize-AF17, WP1 + WP2)

The equation `F(z) = M(z)·F(z^k)` as an identity of *functions* on the open unit disc, against
the matrix `RB.mahlerMatrix` built in `RB/MahlerSystem.lean`.  This closes the omission that
file's module doc records deliberately ("the analytic identity … is *not* built"), and is links
**L1** and **L2** of `plans/plan-formalize-AF17.html` — milestone M1 of the staged architecture
that turned `AF.transcendental_or_rat_of_automatic` from a cited axiom into a theorem (completed
2026-08-04 by WP5, `RB/AutomaticValue.lean`).

## What is proved

For a `ℕ`-valued sequence `s` bounded by `B` and `‖z‖ < 1`, the generating function
`F_s(z) = Σₙ s(n)zⁿ` converges absolutely (`summable_natCast_mul_pow`), and splitting `ℕ` into
residue classes mod `k` — `n = k·m + r` — gives

  `F_s(z) = Σ_{r<k} zʳ · F_{s(k·+r)}(z^k)`   (`genFun_eq_sum`).

That is Cobham's *automatic ⇒ Mahlerian* ([Cob68]; [Bec94] in the `k`-regular generality) with
the combinatorial half already done in `RB/MahlerSystem.lean`: the `k`-kernel is closed under
`s ↦ (n ↦ s(k·n+r))` (`RB.kernel_decimation`), so for a kernel element the decimated sequences
are again kernel elements (`genFun_kernelMap`), and against an abstract decimation
`σ : ι → Fin k → ι` the whole family assembles into the vector identity

  `(F_i(z))_i = M(z) ·ᵥ (F_i(z^k))_i`,  `M = RB.mahlerMatrix k σ` evaluated by `Polynomial.aeval z`

(`mahlerSystem`), instantiated at any kernel model (`IsKernelModel.mahlerSystem`) and, as a
worked row, at Thue–Morse (`thueMorse_mahlerSystem`, `thueMorse_genFun_eq`).

## Link L2: the pole hypothesis (WP2)

`F_s` is not merely a `tsum`: bounded coefficients put the radius of convergence at `≥ 1`
(`one_le_genFunSeries_radius`, against `FormalMultilinearSeries.ofScalars`), so `F_s` is the sum
of its power series on the unit ball (`hasFPowerSeriesOnBall_genFun`) and is **analytic at every
point of the open unit disc** (`analyticAt_genFun`).  Hence no such point is a *pole*: Mathlib's
test for a pole is negativity of `meromorphicOrderAt`
(`tendsto_cobounded_iff_meromorphicOrderAt_neg`), and `genFun_meromorphicOrderAt_nonneg` /
`not_tendsto_cobounded_genFun` rule that out.

That discharges the second of the three facts `CITED/AdamczewskiFaverjon.lean`'s module doc lists
as "folded into the axiom": *bounded coefficients ⇒ radius `≥ 1` ⇒ `α` with `|α| < 1` is not a
pole*.  At the corpus's own instance the chain is completed by `genFun_wmin`
(`F_w(2/3) = 3(K−x₀)`, i.e. `RB.tsum_wmin_eq` with the left-hand side named) and
`analyticAt_genFun_wmin`; `genFun_ratCast` records that the series in the axiom's statement *is*
`genFun a (α : ℝ)`, definitionally, so no consumer statement moves.

## Scope

* **Any complete normed field.**  Nothing here needs `ℂ`: the statements are for `𝕜` a complete
  normed field (`NontriviallyNormedField` from the analyticity section on, which `ℝ` and `ℂ` both
  are), so they apply verbatim to `ℝ` — the corpus's own instance, `RB.tsum_wmin_eq'` evaluating
  at the *real* point `2/3` — and to `ℂ`, where the Mahler method actually lives.  The only
  property of the coefficients used is `‖(s n : 𝕜)‖ ≤ s n` (`norm_natCast_le_of_bound`).
* **Boundedness is free.**  `AS.finite_range_of_isAutomatic'` bounds an automatic sequence, and
  `AS.range_subset_of_mem_kKernel'` transfers the bound to every kernel element with the *same*
  constant (`exists_bound_kKernel`) — which is what makes the vector form uniform in `i`.
* **No downstream gain when written, by design.** Nothing in `RB/` changed here: the axiom was
  still an axiom, and its two consumers still read exactly as they did.  This file bought
  footprint quality, and the later stages spent it — WP3–WP5 (the [AF17] §4 tower, gate G4 and
  `RB/AutomaticValue.lean`) demoted the axiom to [AF17] Thm 1.4 = [AF22] Thm 2.1, i.e. to
  `AF.theoreme_2_1` (`plans/plan-formalize-AF17.html` §5, §9 risk R1).  The two consumers
  still read exactly as they did.

## The shape of the identity

`mahlerMatrix k σ` has entries in `ℤ[z]`; `M(z)` means `(mahlerMatrix k σ).map (aeval z)`, and
`mahlerMatrix_aeval_apply` computes it: the `(i,j)` entry is `Σ_{r : σ i r = j} zʳ`.  Contracting
against the vector of generating functions turns the double sum over `(j, r)` into the single sum
over `r` of `genFun_eq_sum` — the only content of `mahlerSystem` beyond the scalar identity.

Note the direction: the identity is `F(z) = M(z)F(z^k)`, so the matrix acts on the *decimated*
vector.  With `z = 2/3` the iterates `z^{k^l}` are the points at which `RB/Regularity.lean`'s
regularity statements are proved (`RB.regular_two_thirds`), which is why they are stated there
along the orbit rather than at a single point.

## Contents

### WP1 — the system

* `RB.genFun` — the generating function `Σₙ s(n)zⁿ`; `genFun_congr`, `norm_natCast_le_of_bound`.
* **`RB.summable_natCast_mul_pow`** — absolute convergence on `‖z‖ < 1` from boundedness.
* `RB.exists_bound_of_isAutomatic`, **`RB.exists_bound_kKernel`** — the bound, uniform over the
  kernel.
* `RB.tsum_decimate` — splitting a summable series into residue classes mod `k`.
* **`RB.genFun_eq_sum`** — `F_s(z) = Σ_{r<k} zʳ F_{s(k·+r)}(z^k)`.
* **`RB.genFun_kernelMap`** — the same for a kernel element, decimated by `RB.kernelMap`.
* `RB.mahlerMatrix_aeval_apply` — the entries of `M(z)`.
* **`RB.mahlerSystem`** — the vector identity `F(z) = M(z) ·ᵥ F(z^k)`.
* **`RB.IsKernelModel.mahlerSystem`** — instantiated at a kernel model.
* `RB.thueMorse_mahlerSystem`, `RB.thueMorse_genFun_eq` — the worked row.

### WP2 — convergence and the pole hypothesis

* `RB.genFunSeries`, `RB.genFunSeries_sum` — the power series and its sum.
* **`RB.one_le_genFunSeries_radius`** — radius of convergence `≥ 1`.
* `RB.hasFPowerSeriesOnBall_genFun`, `RB.analyticOnNhd_genFun`, **`RB.analyticAt_genFun`** —
  analytic on the open unit disc.
* **`RB.genFun_meromorphicOrderAt_nonneg`**, `RB.not_tendsto_cobounded_genFun` — hence no point
  of the disc is a pole.
* `RB.genFun_ratCast` — the axiom's series *is* `genFun` at a rational point (definitionally).
* **`RB.genFun_wmin`** — `F_w(2/3) = 3(K−x₀)`; `RB.analyticAt_genFun_wmin`,
  `RB.not_tendsto_cobounded_genFun_wmin` — the hypothesis discharged at the corpus's own point.

## References

* [AF17] B. Adamczewski, C. Faverjon. *Méthode de Mahler: relations linéaires, transcendance et
  applications aux nombres automatiques.* Proc. London Math. Soc. **115** (2017), 55–90.  (§1:
  the system `F(z) = A(z)F(z^q)`; Cor 1.8 = the axiom this program would discharge.)
* [Cob68] A. Cobham. *On the Hartmanis–Stearns problem for a class of tag machines.* Conf. Record
  1968 Ninth Ann. Symp. on Switching and Automata Theory, 51–60.  (Automatic ⇒ Mahlerian; [AF17]
  App. A attributes the implication there.)
* [Bec94] P.-G. Becker. *`k`-regular power series and Mahler-type functional equations.* J.
  Number Theory **49** (1994), 269–286.  (The `k`-regular generality of the same implication.)
* [AS03] J.-P. Allouche, J. Shallit. *Automatic Sequences.* CUP 2003.  (The `k`-kernel, Thm
  6.6.2.)
* [AFS08] S. Akiyama, C. Frougny, J. Sakarovitch. *Powers of rationals modulo 1 and rational base
  number systems.* Israel J. Math. **168** (2008), 53–91.  (`K = ω_{3/2}` and the word `RB.wmin`,
  via `RB/Basic.lean`.)
* [AF17f] `plans/plan-formalize-AF17.html` (2026-08-03): §3 links L1/L2, WP1 + WP2,
  milestone M1.
* [B1E2b] `plans/plan-B1E2b.html` (2026-07-28): WP8/WP9, where `mahlerMatrix` and
  `IsKernelModel` come from.
-/

namespace RB

open AS Matrix Polynomial

/-! ## The generating function -/

section GenFun

variable {𝕜 : Type*} [NormedField 𝕜]

/-- The **generating function** `F_s(z) = Σₙ s(n)zⁿ` of a `ℕ`-valued sequence, as an element of a
normed field.  For `‖z‖ < 1` and `s` bounded the series converges absolutely
(`summable_natCast_mul_pow`); elsewhere `tsum`'s junk value makes this notation, not analysis. -/
@[category API, AMS 11 40 68, ref "AF17" "AS03", group "rb_mahler_system"]
noncomputable def genFun (s : ℕ → ℕ) (z : 𝕜) : 𝕜 := ∑' n, (s n : 𝕜) * z ^ n

@[category API, AMS 11 40 68, ref "AF17", group "rb_mahler_system"]
lemma genFun_congr {s t : ℕ → ℕ} (h : ∀ n, s n = t n) (z : 𝕜) : genFun s z = genFun t z := by
  simp only [genFun, h]

/-- A `ℕ`-valued sequence bounded by `B` has all its casts bounded by `B` in norm: the one
property of the coefficients that the whole file uses. -/
@[category API, AMS 11 40, ref "AF17f", group "rb_mahler_system"]
lemma norm_natCast_le_of_bound {s : ℕ → ℕ} {B : ℕ} (hbdd : ∀ n, s n ≤ B) (n : ℕ) :
    ‖(s n : 𝕜)‖ ≤ (B : ℝ) := by
  refine le_trans (Nat.norm_cast_le (s n)) ?_
  rw [norm_one, mul_one]
  exact_mod_cast hbdd n

end GenFun

/-! ## Convergence on the open unit disc -/

section Summable

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

/-- **Absolute convergence from boundedness** ([AF17f] WP1): a `ℕ`-valued sequence bounded by `B`
has `Σₙ s(n)zⁿ` absolutely convergent for `‖z‖ < 1`, by comparison with `B·Σ‖z‖ⁿ`.

The only property of the coefficients used is `‖(s n : 𝕜)‖ ≤ s n`, which holds in every normed
field (`Nat.norm_cast_le` plus `‖1‖ = 1`) — so the lemma is available at `𝕜 = ℝ` and `𝕜 = ℂ`
alike. -/
@[category research solved, AMS 11 40 68, ref "AF17" "AF17f", group "rb_mahler_system"]
theorem summable_natCast_mul_pow {s : ℕ → ℕ} {B : ℕ} (hbdd : ∀ n, s n ≤ B) {z : 𝕜}
    (hz : ‖z‖ < 1) : Summable fun n => (s n : 𝕜) * z ^ n := by
  refine Summable.of_norm_bounded (g := fun n => (B : ℝ) * ‖z‖ ^ n)
    ((summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left _) fun n => ?_
  have hcast : ‖(s n : 𝕜)‖ ≤ (B : ℝ) := norm_natCast_le_of_bound hbdd n
  calc ‖(s n : 𝕜) * z ^ n‖ = ‖(s n : 𝕜)‖ * ‖z‖ ^ n := by rw [norm_mul, norm_pow]
    _ ≤ (B : ℝ) * ‖z‖ ^ n := by gcongr

end Summable

/-! ## The bound, uniformly over the kernel -/

/-- An automatic sequence is bounded: its range is finite (`AS.finite_range_of_isAutomatic'`),
hence bounded above in `ℕ`. -/
@[category research solved, AMS 11 68, ref "AS03", group "rb_mahler_system"]
theorem exists_bound_of_isAutomatic {a : ℕ → ℕ} (hauto : IsAutomatic a) : ∃ B, ∀ n, a n ≤ B := by
  obtain ⟨B, hB⟩ := (finite_range_of_isAutomatic' hauto).bddAbove
  exact ⟨B, fun n => hB ⟨n, rfl⟩⟩

/-- **One bound for the whole kernel** ([AF17f] WP1): every element of the `k`-kernel of an
automatic sequence is bounded by the *same* `B` that bounds the sequence, since its values are
among the values of `a` (`AS.range_subset_of_mem_kKernel'`).

Uniformity in the kernel element is what makes the vector form of the Mahler system a statement
about a single `B`, and hence usable with a `Fintype` index. -/
@[category research solved, AMS 11 68, ref "AS03" "AF17f", group "rb_mahler_system"]
theorem exists_bound_kKernel {k : ℕ} {a : ℕ → ℕ} (hauto : IsAutomatic a) :
    ∃ B, ∀ s ∈ kKernel k a, ∀ n, s n ≤ B := by
  obtain ⟨B, hB⟩ := exists_bound_of_isAutomatic hauto
  refine ⟨B, fun s hs n => ?_⟩
  obtain ⟨m, hm⟩ := range_subset_of_mem_kKernel' (k := k) (a := a) hs ⟨n, rfl⟩
  exact hm ▸ hB m

/-! ## Decimation of a series -/

section Decimate

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

/-- **Splitting a series into residue classes**: for a summable `f : ℕ → 𝕜`,

  `Σₙ f(n) = Σ_{r<k} Σₘ f(k·m + r)`,

the re-indexing `n = k·m + r` carried by `Nat.divModEquiv`.  This is the analytic half of the
decimation identity `a_i(kn+r) = a_{σ(i,r)}(n)` of `RB/MahlerSystem.lean`. -/
@[category research solved, AMS 40, ref "AF17f", group "rb_mahler_system"]
theorem tsum_decimate {f : ℕ → 𝕜} (hf : Summable f) (k : ℕ) [NeZero k] :
    ∑' n, f n = ∑ r : Fin k, ∑' m, f (k * m + r) := by
  classical
  set e : Fin k × ℕ ≃ ℕ := (Equiv.prodComm (Fin k) ℕ).trans (Nat.divModEquiv k).symm with he
  have hval : ∀ p : Fin k × ℕ, e p = k * p.2 + (p.1 : ℕ) := by
    intro p
    simp [he, Nat.mul_comm]
  have hcomp : Summable fun p : Fin k × ℕ => f (e p) := e.summable_iff.mpr hf
  calc ∑' n, f n = ∑' p : Fin k × ℕ, f (e p) := (e.tsum_eq f).symm
    _ = ∑' (r : Fin k), ∑' (m : ℕ), f (e (r, m)) := hcomp.tsum_prod
    _ = ∑ r : Fin k, ∑' m, f (k * m + r) := by
        rw [tsum_fintype]
        exact Finset.sum_congr rfl fun r _ => tsum_congr fun m => by rw [hval (r, m)]

/-- **The Mahler identity, scalar form** ([Cob68]; [AF17] §1): for `s` bounded and `‖z‖ < 1`,

  `F_s(z) = Σ_{r<k} zʳ · F_{s(k·+r)}(z^k)`.

Only the re-indexing `n = k·m + r` is involved — `z^{k·m+r} = zʳ·(z^k)^m` — so the identity is
*not* where automaticity enters.  Automaticity enters by making the decimated sequences
`s(k·+r)` range over a **finite** set (`RB.kernel_decimation`), which is what turns the identity
into a linear system with polynomial coefficients (`mahlerSystem`). -/
@[category research solved, AMS 11 40 68, ref "AF17" "Cob68" "AF17f", group "rb_mahler_system"]
theorem genFun_eq_sum (k : ℕ) [NeZero k] {s : ℕ → ℕ} {B : ℕ} (hbdd : ∀ n, s n ≤ B) {z : 𝕜}
    (hz : ‖z‖ < 1) :
    genFun s z = ∑ r : Fin k, z ^ (r : ℕ) * genFun (fun n => s (k * n + r)) (z ^ k) := by
  rw [genFun, tsum_decimate (summable_natCast_mul_pow hbdd hz) k]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [genFun, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [pow_add, pow_mul]
  ring

end Decimate

/-! ## The kernel form -/

section Kernel

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

/-- **The Mahler identity along the kernel** ([AF17f] WP1): for `s` in the `k`-kernel of an
automatic sequence `a`, the decimated sequences of `genFun_eq_sum` are the kernel elements
`RB.kernelMap k a s r` — no choice, no enumeration.

This is the identity `Fᵢ(z) = Σ_{r<k} zʳ·F_{σ(i,r)}(z^k)` of `RB/MahlerSystem.lean`'s module doc,
stated where `σ` is *the* decimation of the kernel. -/
@[category research solved, AMS 11 40 68, ref "AF17" "Cob68" "AF17f", group "rb_mahler_system"]
theorem genFun_kernelMap {k : ℕ} [NeZero k] {a : ℕ → ℕ} (hauto : IsAutomatic a)
    (s : ↥(kKernel k a)) {z : 𝕜} (hz : ‖z‖ < 1) :
    genFun s.val z = ∑ r : Fin k, z ^ (r : ℕ) * genFun (kernelMap k a s r).val (z ^ k) := by
  obtain ⟨B, hB⟩ := exists_bound_kKernel (k := k) hauto
  rw [genFun_eq_sum k (hbdd := hB s.val s.2) hz]
  exact Finset.sum_congr rfl fun r _ => by
    rw [genFun_congr (fun n => (kernelMap_apply k a s r n).symm)]

end Kernel

/-! ## The vector form `F(z) = M(z)F(z^k)` -/

section System

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [CompleteSpace 𝕜] [Fintype ι] in
/-- The entries of `M(z)`: evaluating `RB.mahlerMatrix` at `z` gives `Σ_{r : σ i r = j} zʳ`. -/
@[category API, AMS 11 68, ref "AF17", group "rb_mahler_system"]
lemma mahlerMatrix_aeval_apply (k : ℕ) (σ : ι → Fin k → ι) (z : 𝕜) (i j : ι) :
    (mahlerMatrix k σ).map (aeval z) i j
      = ∑ r : Fin k, if σ i r = j then z ^ (r : ℕ) else 0 := by
  simp only [Matrix.map_apply, mahlerMatrix, Matrix.of_apply, map_sum, apply_ite (aeval z),
    map_pow, aeval_X, map_zero]

/-- **The analytic Mahler system** ([AF17] §1; [Cob68]) — the identity `RB/MahlerSystem.lean`
declined to build:

  `(Fᵢ(z))ᵢ = M(z) ·ᵥ (Fᵢ(z^k))ᵢ`,   `M = RB.mahlerMatrix k σ` evaluated at `z`,

for any family `φ : ι → ℕ → ℕ` of uniformly bounded sequences carrying a decimation
`σ : ι → Fin k → ι`, i.e. satisfying `φ (σ i r) n = φ i (k·n + r)`.

The hypotheses are exactly the data of `RB.IsKernelModel` minus the injectivity and the
surjectivity onto the kernel, neither of which the identity uses; automaticity is not assumed
either, only the uniform bound `hbdd` (which `AS.finite_range_of_isAutomatic'` supplies for free
in the automatic case, `exists_bound_kKernel`). -/
@[category research solved, AMS 11 40 68, ref "AF17" "Cob68" "AF17f", group "rb_mahler_system"]
theorem mahlerSystem (k : ℕ) [NeZero k] (φ : ι → ℕ → ℕ) (σ : ι → Fin k → ι)
    (hσ : ∀ i r n, φ (σ i r) n = φ i (k * n + r)) {B : ℕ} (hbdd : ∀ i n, φ i n ≤ B) {z : 𝕜}
    (hz : ‖z‖ < 1) :
    (fun i => genFun (φ i) z)
      = (mahlerMatrix k σ).map (aeval z) *ᵥ fun i => genFun (φ i) (z ^ k) := by
  funext i
  rw [genFun_eq_sum k (hbdd i) hz]
  simp only [Matrix.mulVec, dotProduct, mahlerMatrix_aeval_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [genFun_congr (fun n => hσ i r n)]

/-- **The system of a kernel model** ([AF17f] WP1, the plan's "instantiate at
`RB.IsKernelModel`"): a kernel model in base `k ≥ 2` gives the analytic identity outright, the
uniform bound coming from automaticity (`IsKernelModel.isAutomatic` and `exists_bound_kKernel`).

So for every worked row of `RB/MahlerExamples.lean` the matrix displayed there *is* the matrix of
an identity between honest functions on the open unit disc, not merely a bookkeeping device. -/
@[category research solved, AMS 11 40 68, ref "AF17" "AS03" "AF17f", group "rb_mahler_system"]
theorem IsKernelModel.mahlerSystem {k : ℕ} {a : ℕ → ℕ} {φ : ι → ℕ → ℕ} {σ : ι → Fin k → ι}
    (h : IsKernelModel k a φ σ) (hk : 2 ≤ k) {z : 𝕜} (hz : ‖z‖ < 1) :
    (fun i => genFun (φ i) z)
      = (mahlerMatrix k σ).map (aeval z) *ᵥ fun i => genFun (φ i) (z ^ k) := by
  have : NeZero k := ⟨by omega⟩
  obtain ⟨B, hB⟩ := exists_bound_kKernel (k := k) (h.isAutomatic hk)
  exact RB.mahlerSystem k φ σ h.2.2 (fun i n => hB (φ i) (h.2.1 ▸ Set.mem_range_self i) n) hz

end System

/-! ## Worked row: Thue–Morse -/

section ThueMorse

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

/-- The Thue–Morse system as an identity of functions on `‖z‖ < 1`. -/
@[category research solved, AMS 11 40 68, ref "AF17" "AS03" "AF17f", group "rb_mahler_system"]
theorem thueMorse_mahlerSystem {z : 𝕜} (hz : ‖z‖ < 1) :
    (fun i => genFun (tmPhi i) z)
      = (mahlerMatrix 2 tmSigma).map (aeval z) *ᵥ fun i => genFun (tmPhi i) (z ^ 2) :=
  thueMorse_isKernelModel.mahlerSystem (by norm_num) hz

/-- The scalar reading of the row: with `t` the Thue–Morse sequence and `t̄ = 1 - t`,

  `F_t(z) = F_t(z²) + z·F_{t̄}(z²)`,

the first coordinate of `thueMorse_mahlerSystem` — the classical Mahler equation of the
Thue–Morse generating function.  (The second coordinate is the same identity with `t` and `t̄`
exchanged; `tmSigma` is the transposition.) -/
@[category research solved, AMS 11 40 68, ref "AF17" "AS03", group "rb_mahler_system"]
theorem thueMorse_genFun_eq {z : 𝕜} (hz : ‖z‖ < 1) :
    genFun thueMorse z
      = genFun thueMorse (z ^ 2) + z * genFun (fun n => 1 - thueMorse n) (z ^ 2) := by
  have h := congrFun (thueMorse_mahlerSystem (𝕜 := 𝕜) hz) 0
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, mahlerMatrix, tmSigma, tmPhi] using h

end ThueMorse

/-! ## Radius of convergence, and the pole hypothesis ([AF17f] WP2) -/

section Analytic

open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

/-- The formal power series `Σₙ s(n)zⁿ`, as a `FormalMultilinearSeries` — the object carrying
Mathlib's radius of convergence.  Its sum is `RB.genFun s` (`genFunSeries_sum`). -/
@[category API, AMS 11 30 40, ref "AF17f", group "rb_mahler_system"]
noncomputable def genFunSeries (𝕜 : Type*) [NontriviallyNormedField 𝕜] (s : ℕ → ℕ) :
    FormalMultilinearSeries 𝕜 𝕜 𝕜 :=
  FormalMultilinearSeries.ofScalars 𝕜 fun n => (s n : 𝕜)

omit [CompleteSpace 𝕜] in
@[category API, AMS 11 30 40, ref "AF17f", group "rb_mahler_system"]
lemma genFunSeries_sum (s : ℕ → ℕ) : (genFunSeries 𝕜 s).sum = genFun s := by
  funext z
  simp only [genFunSeries, genFun, FormalMultilinearSeries.sum,
    FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]

omit [CompleteSpace 𝕜] in
/-- **Radius of convergence `≥ 1`** ([AF17f] WP2; [AF17] Cor 1.8's standing hypothesis): a
`ℕ`-valued sequence bounded by `B` gives `‖pₙ‖·1ⁿ ≤ B`, so `FormalMultilinearSeries.radius`
is at least `1`.

This is the whole content of "bounded coefficients ⇒ the series is a function on the open unit
disc", and it is the first of the two facts that `CITED/AdamczewskiFaverjon.lean`'s module doc
folds into the axiom on [AF17]'s authority. -/
@[category research solved, AMS 11 30 40, ref "AF17" "AF17f", group "rb_mahler_system"]
theorem one_le_genFunSeries_radius {s : ℕ → ℕ} {B : ℕ} (hbdd : ∀ n, s n ≤ B) :
    1 ≤ (genFunSeries 𝕜 s).radius := by
  have h : ∀ n : ℕ, ‖genFunSeries 𝕜 s n‖ * ((1 : NNReal) : ℝ) ^ n ≤ (B : ℝ) := by
    intro n
    rw [genFunSeries, FormalMultilinearSeries.ofScalars_norm]
    simpa using norm_natCast_le_of_bound hbdd n
  simpa using FormalMultilinearSeries.le_radius_of_bound _ (B : ℝ) h

/-- **The generating function is analytic on the open unit disc**: `genFun s` is the sum of
`genFunSeries 𝕜 s` on the ball of radius `1`, which `one_le_genFunSeries_radius` puts inside the
disc of convergence. -/
@[category research solved, AMS 11 30 40, ref "AF17" "AF17f", group "rb_mahler_system"]
theorem hasFPowerSeriesOnBall_genFun {s : ℕ → ℕ} {B : ℕ} (hbdd : ∀ n, s n ≤ B) :
    HasFPowerSeriesOnBall (genFun s : 𝕜 → 𝕜) (genFunSeries 𝕜 s) 0 1 := by
  have hr := one_le_genFunSeries_radius (𝕜 := 𝕜) hbdd
  have h := (genFunSeries 𝕜 s).hasFPowerSeriesOnBall (lt_of_lt_of_le zero_lt_one hr)
  rw [genFunSeries_sum] at h
  exact h.mono one_pos hr

@[category research solved, AMS 11 30 40, ref "AF17" "AF17f", group "rb_mahler_system"]
theorem analyticOnNhd_genFun {s : ℕ → ℕ} {B : ℕ} (hbdd : ∀ n, s n ≤ B) :
    AnalyticOnNhd 𝕜 (genFun s : 𝕜 → 𝕜) (Metric.eball 0 1) :=
  (hasFPowerSeriesOnBall_genFun hbdd).analyticOnNhd

/-- **`α` with `‖α‖ < 1` is a regular point of `f`, in the analytic sense**: `genFun s` is
analytic at every point of the open unit disc. -/
@[category research solved, AMS 11 30 40, ref "AF17" "AF17f", group "rb_mahler_system"]
theorem analyticAt_genFun {s : ℕ → ℕ} {B : ℕ} (hbdd : ∀ n, s n ≤ B) {z : 𝕜} (hz : ‖z‖ < 1) :
    AnalyticAt 𝕜 (genFun s) z := by
  refine analyticOnNhd_genFun hbdd z ?_
  simpa [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one] using hz

/-- **`α` is not a pole** ([AF17] Cor 1.8's hypothesis, discharged): the meromorphic order of
`genFun s` at a point of the open unit disc is `≥ 0`.

Mathlib's pole test is `tendsto_cobounded_iff_meromorphicOrderAt_neg` — a pole is exactly a
point of negative order — so this is the literal hypothesis "*`α` … qui n'est pas un pôle de
`f`*", in the vocabulary the corpus has.  `not_tendsto_cobounded_genFun` states the same fact in
its `Tendsto` form. -/
@[category research solved, AMS 11 30 40, ref "AF17" "AF17f", group "rb_mahler_system"]
theorem genFun_meromorphicOrderAt_nonneg {s : ℕ → ℕ} {B : ℕ} (hbdd : ∀ n, s n ≤ B) {z : 𝕜}
    (hz : ‖z‖ < 1) : 0 ≤ meromorphicOrderAt (genFun s) z :=
  (analyticAt_genFun hbdd hz).meromorphicOrderAt_nonneg

/-- **`α` is not a pole**, in `Tendsto` form: `genFun s` does not blow up at any point of the
open unit disc. -/
@[category research solved, AMS 11 30 40, ref "AF17" "AF17f", group "rb_mahler_system"]
theorem not_tendsto_cobounded_genFun {s : ℕ → ℕ} {B : ℕ} (hbdd : ∀ n, s n ≤ B) {z : 𝕜}
    (hz : ‖z‖ < 1) :
    ¬ Filter.Tendsto (genFun s) (𝓝[≠] z) (Bornology.cobounded 𝕜) := by
  rw [tendsto_cobounded_iff_meromorphicOrderAt_neg (analyticAt_genFun hbdd hz).meromorphicAt]
  exact not_lt.mpr (genFun_meromorphicOrderAt_nonneg hbdd hz)

end Analytic

/-! ## The corpus's own instance: the word of `K = ω_{3/2}` at `2/3` ([AF17f] WP2) -/

section Corpus

open scoped Topology

/-- **The axiom's series is `genFun` at a rational point** — definitionally.  This is the
"plugs in unchanged" check of [AF17f] WP2: the series in
`AF.transcendental_or_rat_of_automatic` *is* `RB.genFun a (α : ℝ)`, so nothing about the
axiom's statement (and hence no consumer proof) has to move when the machinery of this file is
brought to bear on it. -/
@[category API, AMS 11 40 68, ref "AF17" "AF17f", group "rb_mahler_system"]
theorem genFun_ratCast (a : ℕ → ℕ) (α : ℚ) :
    genFun a ((α : ℝ)) = ∑' j, (a j : ℝ) * (α : ℝ) ^ j := rfl

/-- **The corpus's value**: `RB.tsum_wmin_eq` in generating-function form, `F_w(2/3) = 3(K−x₀)`
— the same identity `RB.tsum_wmin_eq'` feeds to [AF17] Cor 1.8, now with the left-hand side
named. -/
@[category research solved, AMS 11 68, ref "AFS08" "AF17" "AF17f", group "rb_mahler_system"]
theorem genFun_wmin (x₀ : ℕ) : genFun (wmin x₀) ((2 / 3 : ℚ) : ℝ) = 3 * (K x₀ - x₀) := by
  rw [genFun, ← tsum_wmin_eq x₀]
  push_cast
  exact tsum_congr fun j => mul_comm _ _

/-- **The pole hypothesis, discharged at the corpus's own point** ([AF17f] WP2): the minimal word
is `{0,1}`-valued (`RB.wmin_le_one`), so its generating function is analytic at `2/3`.

Together with `genFun_wmin` this is link L2 for the single instance the corpus consumes: the
value `3(K−x₀)` that [AF17] Cor 1.8 is applied to is an honest analytic value of `f` at a
non-pole, not a formal artefact of `tsum`. -/
@[category research solved, AMS 11 30 68, ref "AF17" "AFS08" "AF17f", group "rb_mahler_system"]
theorem analyticAt_genFun_wmin (x₀ : ℕ) :
    AnalyticAt ℝ (genFun (wmin x₀)) ((2 / 3 : ℚ) : ℝ) :=
  analyticAt_genFun (B := 1) (wmin_le_one x₀) (by rw [Real.norm_eq_abs]; norm_num)

/-- The same, in `Tendsto` form: `2/3` is not a pole of the word's generating function. -/
@[category research solved, AMS 11 30 68, ref "AF17" "AFS08" "AF17f", group "rb_mahler_system"]
theorem not_tendsto_cobounded_genFun_wmin (x₀ : ℕ) :
    ¬ Filter.Tendsto (genFun (wmin x₀)) (𝓝[≠] (((2 / 3 : ℚ) : ℝ))) (Bornology.cobounded ℝ) :=
  not_tendsto_cobounded_genFun (B := 1) (wmin_le_one x₀) (by rw [Real.norm_eq_abs]; norm_num)

end Corpus

end RB
