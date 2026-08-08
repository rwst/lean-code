/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CITED.AlloucheShallitBasic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Matrix.PEquiv
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Ring
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Automatic ⇒ a linear Mahler system (plan-B1E2, WP4)

The **decimation data** of an automatic sequence, and the matrix `M(z)` it generates — the
input to `RB.Regularity`'s regularity lemma.

## The decimation

The `k`-kernel is *closed* under `s ↦ (n ↦ s(k·n + r))` for `r < k` (`kernel_decimation`): if
`s(n) = a(kⁱn + j)` with `j < kⁱ`, then

  `s(kn + r) = a(kⁱ(kn+r) + j) = a(k^{i+1}·n + (kⁱ·r + j))`,  `kⁱ·r + j < k^{i+1}`.

So `σ(s, r) := (n ↦ s(k·n + r))` is a map `K × Fin k → K` needing **no choice** — the decimated
sequence is a *specific* function, and the lemma says it lies in `K`.  That is the coefficient
form of Mahler's system: `a_i(kn+r) = a_{σ(i,r)}(n)`, i.e. `Fᵢ(z) = Σ_{r<k} zʳ·F_{σ(i,r)}(z^k)`,
i.e. `F(z) = M(z)F(z^k)` with

  `M(z) = Σ_{r<k} zʳ·Pᵣ`,  `Pᵣ` the incidence matrix of `σ(·, r)` (exactly one `1` per row).

## Scope: the matrix here, the analytic identity in `RB/MahlerAnalytic.lean`

`M(z)` is built here (`mahlerMatrix`), general in `(ι, σ)`, together with the row-sum identity
`Σⱼ M i j = 1 + z + ⋯ + z^{k-1}` and the divisibility it implies, `(1+z+⋯+z^{k-1}) ∣ det M`
(`rowSum_dvd_det`, [B1E2b] WP8) — add every column to one column and pull the common factor out.
The roots of that factor are `k`-th roots of unity, all on `|z| = 1`, and so **never `2/3`**
([B1E2] §0.2(1); check against [AF17] §8.1, where `det A = (1+z-z²)(1+z+z²)` at `k = 3`).

The **analytic** identity `F(z) = M(z)F(z^k)` as an equation of functions on `|z| < 1` was
deliberately omitted when this file was written: WP4's live consumer is `RB.Regularity`, which is
a statement about `det M` alone, and the other consumer (the `p`-adic Mahler step, WP5) is
**parked** on an input that does not exist in the literature ([B1E2] §0.1), so the transport
would have cost convergence machinery for no gain.

It is now built, one file over, in `RB/MahlerAnalytic.lean` (`RB.mahlerSystem`,
`RB.IsKernelModel.mahlerSystem`) — WP1 of `plans/plan-formalize-AF17.html`, i.e. link L1 of the
programme that turned `AF.transcendental_or_rat_of_automatic` from a cited axiom into a theorem
(completed 2026-08-04, WP5).  Nothing here changed to accommodate it.

## Instantiating at the kernel

`mahlerMatrix` is stated for an arbitrary `[Fintype ι] [DecidableEq ι]` and `σ : ι → Fin k → ι`,
so results transfer to *any* decimation structure.  To use it at `ι = ↥(AS.kKernel k a)`, supply
the instances from `(hK : (AS.kKernel k a).Finite)` via `hK.fintype` and `Classical.decEq`.

## Contents

* **`RB.kernel_decimation`** — the kernel is closed under decimation.  (A general `AS` fact;
  a CITED/ForMathlib candidate.)
* `RB.kernelMap`, `RB.kernelMap_apply` — `σ` and the decimation identity `σ(s,r)(n) = s(kn+r)`.
* **`RB.mahlerMatrix`** — `M(z) = Σ_{r<k} zʳPᵣ`.
* **`RB.mahlerMatrix_row_sum`** — every row sums to `1 + z + ⋯ + z^{k-1}`.
* **`RB.rowSum_dvd_det`** — hence `(1 + z + ⋯ + z^{k-1}) ∣ det M`.
* `RB.mahlerMatrix_map_eval_zero` — `M(0) = P₀`, the input to the lever.

## References

* [AF17] Adamczewski, Faverjon. Proc. LMS **115** (2017), 55–90.  (§1: the system; §8.1: the
  `k = 3` example against which the row-sum identity is checked.)
* [AS03] Allouche, Shallit. *Automatic Sequences.* CUP 2003.  (The `k`-kernel.)
* [B1E2] `plans/plan-B1E2.html` (rev. 2, 2026-07): §0.2 (the regularity lemma), WP4, WP5 (parked).
* [B1E2b] `plans/plan-B1E2b.html` (2026-07-28): WP8 (the row-sum divisibility, and the job it
  does — see `RB/Regularity.lean`).
-/

namespace RB

open Polynomial AS

/-! ## The decimation -/

/-- **The kernel is closed under decimation**: if `s` is in the `k`-kernel of `a`, so is
`n ↦ s(k·n + r)` for every `r < k`.

No choice is involved — the decimated sequence is a specific function; the content is that it
lands back in the kernel. -/
@[category research solved, AMS 11 68, ref "AS03" "AF17", group "rb_mahler_system"]
lemma kernel_decimation {k : ℕ} {a : ℕ → ℕ} {s : ℕ → ℕ} (hs : s ∈ kKernel k a)
    {r : ℕ} (hr : r < k) : (fun n => s (k * n + r)) ∈ kKernel k a := by
  obtain ⟨i, j, hj, rfl⟩ := hs
  refine ⟨i + 1, k ^ i * r + j, ?_, ?_⟩
  · calc k ^ i * r + j < k ^ i * r + k ^ i := by omega
      _ = k ^ i * (r + 1) := by ring
      _ ≤ k ^ i * k := Nat.mul_le_mul_left _ (by omega)
      _ = k ^ (i + 1) := by rw [pow_succ]
  · funext n
    show a (k ^ i * (k * n + r) + j) = a (k ^ (i + 1) * n + (k ^ i * r + j))
    congr 1
    rw [pow_succ]
    ring

/-- The decimation map `σ : K × Fin k → K`, `σ(s,r) = (n ↦ s(k·n + r))`. -/
@[category API, AMS 11 68, ref "AF17", group "rb_mahler_system"]
def kernelMap (k : ℕ) (a : ℕ → ℕ) (s : ↥(kKernel k a)) (r : Fin k) : ↥(kKernel k a) :=
  ⟨fun n => s.val (k * n + r), kernel_decimation s.2 r.isLt⟩

/-- **The decimation identity** `a_i(kn+r) = a_{σ(i,r)}(n)` — the coefficient form of Mahler's
system.  True by construction. -/
@[category API, AMS 11 68, ref "AF17", group "rb_mahler_system"]
lemma kernelMap_apply (k : ℕ) (a : ℕ → ℕ) (s : ↥(kKernel k a)) (r : Fin k) (n : ℕ) :
    (kernelMap k a s r).val n = s.val (k * n + r) := rfl

/-! ## The matrix `M(z) = Σ_{r<k} zʳPᵣ` -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The Mahler matrix** `M(z) = Σ_{r<k} zʳ·Pᵣ`, where `Pᵣ` is the incidence matrix of
`σ(·,r)` — exactly one `1` per row, at column `σ(i,r)`. -/
@[category API, AMS 11 68, ref "AF17", group "rb_mahler_system"]
noncomputable def mahlerMatrix (k : ℕ) (σ : ι → Fin k → ι) : Matrix ι ι (Polynomial ℤ) :=
  Matrix.of fun i j => ∑ r : Fin k, if σ i r = j then (X : Polynomial ℤ) ^ (r : ℕ) else 0

/-- **The row-sum identity** ([B1E2] §0.2(1)): every row of `M` sums to `1 + z + ⋯ + z^{k-1}`,
because `σ(i,·)` sends `{0,…,k-1}` somewhere — each `r` contributes `zʳ` to exactly one column.

Hence `𝟙` is an eigenvector with eigenvalue `1+z+⋯+z^{k-1}`, and that factor divides `det M`.
Its roots are `k`-th roots of unity — all on `|z| = 1`, hence **never `2/3`**. -/
@[category research solved, AMS 11 68, ref "AF17" "B1E2", group "rb_mahler_system"]
lemma mahlerMatrix_row_sum (k : ℕ) (σ : ι → Fin k → ι) (i : ι) :
    ∑ j, mahlerMatrix k σ i j = ∑ r : Fin k, (X : Polynomial ℤ) ^ (r : ℕ) := by
  unfold mahlerMatrix
  simp only [Matrix.of_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun r _ => by simp

/-- **The row-sum factor divides the determinant** ([B1E2b] WP8): `(1 + z + ⋯ + z^{k-1}) ∣ det M`.

Add every column of `M` to one fixed column — this changes no determinant — and that column becomes
constantly `1 + z + ⋯ + z^{k-1}` by `mahlerMatrix_row_sum`; pulling the scalar out of the column
(`Matrix.det_updateCol_smul`) exhibits the factor.

The index set must be nonempty: with `ι = ∅` the determinant is `1`, which `1 + z + ⋯ + z^{k-1}`
does not divide for `k ≥ 2`.

This is the fact behind the non-degeneracy hypothesis of `RB.regular_of_not_dvd_lowest_coeff`: for
`k ≥ 2` a Mahler determinant always *has* singular points — the `k`-th roots of unity other than
`1` — so "`det M ≠ 0`", not "`det M` has no roots", is what one can ask for. Those roots sit on
`|z| = 1` and are therefore never the points the method is evaluated at
(`RB.aeval_rowSum_pos`). -/
@[category research solved, AMS 11 68, ref "AF17" "B1E2b", group "rb_mahler_system"]
theorem rowSum_dvd_det [Nonempty ι] (k : ℕ) (σ : ι → Fin k → ι) :
    (∑ r : Fin k, (X : Polynomial ℤ) ^ (r : ℕ)) ∣ (mahlerMatrix k σ).det := by
  obtain ⟨j₀⟩ := ‹Nonempty ι›
  set A := mahlerMatrix k σ with hA
  set s : Polynomial ℤ := ∑ r : Fin k, (X : Polynomial ℤ) ^ (r : ℕ) with hs
  refine ⟨(A.updateCol j₀ (fun _ => 1)).det, ?_⟩
  have h1 := Matrix.det_updateCol_sum A j₀ (fun _ => (1 : Polynomial ℤ))
  have h2 : (fun i => ∑ j, (1 : Polynomial ℤ) • A i j) = (fun _ : ι => s) := by
    funext i
    simp only [one_smul]
    rw [hs, hA, mahlerMatrix_row_sum]
  rw [h2, one_smul] at h1
  rw [← h1, show (fun _ : ι => s) = s • (fun _ : ι => (1 : Polynomial ℤ)) by funext; simp,
    Matrix.det_updateCol_smul]

omit [Fintype ι] in
/-- **`M(0) = P₀`** ([B1E2] §0.2(2)): only the `r = 0` term survives evaluation at `0`.  This is
what turns "`σ(·,0)` is a permutation" into "`det M(0) = ±1`". -/
@[category research solved, AMS 11 68, ref "AF17" "B1E2", group "rb_mahler_system"]
lemma mahlerMatrix_map_eval_zero (k : ℕ) (hk : 0 < k) (σ : ι → Fin k → ι) :
    (mahlerMatrix k σ).map (Polynomial.eval 0)
      = Matrix.of fun i j => if σ i ⟨0, hk⟩ = j then (1 : ℤ) else 0 := by
  ext i j
  simp only [Matrix.map_apply, mahlerMatrix, Matrix.of_apply, Polynomial.eval_finsetSum]
  rw [Finset.sum_eq_single (⟨0, hk⟩ : Fin k)]
  · split <;> simp
  · intro r _ hr
    have hrne : (r : ℕ) ≠ 0 := fun h => hr (Fin.ext h)
    split <;> simp [zero_pow hrne]
  · intro h; exact absurd (Finset.mem_univ _) h

end RB
