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

## Scope: the matrix, not the analytic identity

`M(z)` is built here (`mahlerMatrix`), general in `(ι, σ)`, together with the row-sum identity
`Σⱼ M i j = 1 + z + ⋯ + z^{k-1}` — the structural fact behind `(1+z+⋯+z^{k-1}) ∣ det M`, whose
roots are `k`-th roots of unity, all on `|z| = 1`, and so **never `2/3`** ([B1E2] §0.2(1); check
against [AF17] §8.1, where `det A = (1+z-z²)(1+z+z²)` at `k = 3`).

The **analytic** identity `F(z) = M(z)F(z^k)` as an equation of functions on `|z| < 1` is *not*
built.  It is not needed: WP4's live consumer is `RB.Regularity`, which is a statement about
`det M` alone, and the other consumer (the `p`-adic Mahler step, WP5) is **parked** on an input
that does not exist in the literature ([B1E2] §0.1).  Building the transport would cost
convergence machinery for no current gain; the note is here so the omission is deliberate rather
than forgotten.

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
* `RB.mahlerMatrix_map_eval_zero` — `M(0) = P₀`, the input to the lever.

## References

* [AF17] Adamczewski, Faverjon. Proc. LMS **115** (2017), 55–90.  (§1: the system; §8.1: the
  `k = 3` example against which the row-sum identity is checked.)
* [AS03] Allouche, Shallit. *Automatic Sequences.* CUP 2003.  (The `k`-kernel.)
* [B1E2] `plans/plan-B1E2.html` (rev. 2, 2026-07): §0.2 (the regularity lemma), WP4, WP5 (parked).
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
