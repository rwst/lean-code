/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB47.Basic
import ForMathlib.Combinatorics.FineWilf

/-!
# At most one periodic orbit: the Fine–Wilf half of [M3, Lem. 3.3]

Lemma 3.3 of `BB47/M3.tex` says that under the hypothesis `p_∞(n, u) = n + 1` the `ω`-limit set
`Ω(u)` contains **at most one periodic orbit**.  Its proof has two halves:

1. a word-combinatorial half — two periodic points whose languages meet in one block of length the
   sum of their periods lie on the *same* orbit — which is the theorem of Fine and Wilf, and
2. a Rauzy-graph half — two *distinct* periodic orbits would give two vertex-disjoint simple
   cycles in `G_n(Ω)`, which [M3, Lem. 3.2] forbids.

This file is the first half, and nothing else.  It needs no hypothesis on the complexity, no
finiteness of the alphabet and no subshift: it is a statement about two periodic words.

**The second half is done too, elsewhere.**  Since WP6/WP8 of `plans/plan-subshift.html` the
graph-theoretic half lives in `ForMathlib/Dynamics/SymbolicDynamics/Rauzy.lean` and the assembled
lemma is `BB47.orbit_eq_of_pInf_eq` in `BB47/OmegaLimit.lean`: under `p_∞(n, u) = n + 1` any two
periodic points of `Ω(u)` lie on the same orbit.  It needs no compact space and no simple-cycle
bookkeeping — the periodic orbit enters only as a set of vertices closed under out-edges, which
`BB47.not_properOutClosed` excludes.  The two-sided counterpart of the theorem below, on which
that argument runs, is `SymbolicDynamics.FullShift.orbit_eq_or_disjoint_language`; this file
remains the statement for one-sided words, which is what `p_∞` and `BB47/Certificate.lean` speak.

## Main results

* `BB47.exists_shift_of_periodic_of_factor_eq` — if `x` has period `p > 0`, `y` has period
  `q > 0`, and one length-`(p + q)` block of `x` equals one of `y`, then `x` is a **shift** of
  `y`: `∃ c, ∀ i, x i = y (i + c)`.
* `BB47.factorSet_eq_of_periodic_of_factor_eq`, `BB47.recFactorSet_eq_of_periodic_of_factor_eq` —
  hence the two words have the same language at every length, i.e. they generate the same orbit.
  This is the conclusion "`P₁ = P₂`" of [M3, Lem. 3.3].
* `BB47.recurrent_of_periodic`, `BB47.recFactorSet_eq_factorSet_of_periodic`,
  `BB47.horizon_eq_zero_of_periodic` — for a periodic word every block recurs, so `p_∞` and `p`
  agree on it and the horizon `s_n` is `0`.
* `BB47.pInf_eq_of_periodic_of_factor_eq` — the two words have the same `p_∞`.

## Why the length `p + q` and not less

`ForMathlib.SubwordComplexity.exists_periodic_not_shift` exhibits, for every `p ≥ 2`, a
`p`-periodic word and a `(p+1)`-periodic word that agree on a block of length
`2p - 1 = p + (p + 1) - gcd p (p + 1) - 1` — one letter short — and are *not* shifts of one
another.  So the hypothesis of `exists_shift_of_periodic_of_factor_eq` cannot be weakened by even
one letter, and the `n ≥ q₁ + q₂` of [M3, Lem. 3.3] is exactly right, not a convenience.

## References

* [FW65] N. J. Fine, H. S. Wilf, *Uniqueness theorems for periodic functions*, Proc. Amer. Math.
  Soc. **16** (1965), 109–114 — proved in `ForMathlib/Combinatorics/FineWilf.lean`.
* [M3] `BB47/M3.tex` (this repository, 2026-09) — Lem. 3.2 (shape), Lem. 3.3 (at most one periodic
  orbit), Thm. 4.1 (Theorem B).
* [BK26] Y. Bugeaud, D. H. Kim, arXiv:2510.02059 — Lem. 2.3, the same appeal to Fine and Wilf.
* [CH73] E. M. Coven, G. A. Hedlund, *Sequences with minimal block growth*, Math. Systems Theory
  **7** (1973), 138–153.
-/

namespace BB47

open ForMathlib.SubwordComplexity

variable {α : Type*}

/-! ## Periodic words: every block recurs -/

/-- Shifting the reading position by a multiple of a period does not change the block read. -/
@[category API, AMS 11 37 68, ref "M3", group "bugeaud_10_47"]
theorem factor_add_mul_period {x : ℕ → α} {p : ℕ} (h : Function.Periodic x p) (n i k : ℕ) :
    factor x n (i + k * p) = factor x n i := by
  funext s
  simp only [factor]
  rw [show i + k * p + (s : ℕ) = i + s + k * p by ring]
  exact periodic_add_mul h (i + s) k

/-- **Every block of a periodic word is recurrent**: it reappears in every period. -/
@[category research solved, AMS 11 37 68, ref "M3", group "bugeaud_10_47"]
theorem recurrent_of_periodic {x : ℕ → α} {p : ℕ} (hp : 0 < p) (h : Function.Periodic x p)
    (n i : ℕ) : Recurrent x n (factor x n i) := by
  intro N
  refine ⟨i + N * p, ?_, factor_add_mul_period h n i N⟩
  calc N = N * 1 := (Nat.mul_one N).symm
    _ ≤ N * p := Nat.mul_le_mul_left N hp
    _ ≤ i + N * p := Nat.le_add_left _ _

/-- For a periodic word the recurrent blocks are *all* the blocks: `p_∞ = p` and the horizon
vanishes. -/
@[category research solved, AMS 11 37 68, ref "M3", group "bugeaud_10_47"]
theorem recFactorSet_eq_factorSet_of_periodic {x : ℕ → α} {p : ℕ} (hp : 0 < p)
    (h : Function.Periodic x p) (n : ℕ) : recFactorSet x n = factorSet x n := by
  ext v
  constructor
  · intro hv
    obtain ⟨i, _, hi⟩ := hv 0
    exact ⟨i, hi⟩
  · rintro ⟨i, rfl⟩
    exact recurrent_of_periodic hp h n i

/-- A periodic word has **no non-recurrent prefix**: its horizon `s_n` is `0` at every level. -/
@[category research solved, AMS 11 37 68, ref "M3", group "bugeaud_10_47"]
theorem horizon_eq_zero_of_periodic [Finite α] {x : ℕ → α} {p : ℕ} (hp : 0 < p)
    (h : Function.Periodic x p) (n : ℕ) : horizon x n = 0 :=
  horizon_eq_zero_iff.mpr fun i => recurrent_of_periodic hp h n i

/-! ## Two periodic words with a common block -/

/-- **[M3, Lem. 3.3], the word-combinatorial half.**  If `x` has period `p > 0`, `y` has period
`q > 0`, and *one* block of length `p + q` occurs in both — at position `a` in `x` and at position
`b` in `y` — then `x` is a shift of `y`.

The proof is Fine and Wilf's theorem: the common block has both periods and is long enough, so it
has period `gcd p q`, and that propagates over both words. -/
@[category research solved, AMS 11 37 68, ref "FW65" "M3", group "bugeaud_10_47"]
theorem exists_shift_of_periodic_of_factor_eq {x y : ℕ → α} {p q a b : ℕ} (hp : 0 < p)
    (hq : 0 < q) (hx : Function.Periodic x p) (hy : Function.Periodic y q)
    (hfac : factor x (p + q) a = factor y (p + q) b) : ∃ c, ∀ i, x i = y (i + c) := by
  -- the shared block, read letter by letter
  have hblock : ∀ i, i < p + q → x (a + i) = y (b + i) := by
    intro i hi
    exact congrFun hfac ⟨i, hi⟩
  obtain ⟨hagree, -, -⟩ := eq_shift_of_periodic_of_factor_eq hp hq hx hy hblock
  -- move the reading position of `x` past `a` by a multiple of its period
  have hap : a ≤ a * p := by
    calc a = a * 1 := (Nat.mul_one a).symm
      _ ≤ a * p := Nat.mul_le_mul_left a hp
  refine ⟨a * p + b - a, fun i => ?_⟩
  have e1 : x (i + a * p) = x i := periodic_add_mul hx i a
  have e2 := hagree (i + a * p - a)
  rw [show a + (i + a * p - a) = i + a * p by omega,
    show b + (i + a * p - a) = i + (a * p + b - a) by omega] at e2
  rw [← e1, e2]

/-- Two periodic words with a common block of length the sum of their periods have the **same
language** at every length: they generate the same orbit.  This is the conclusion `P₁ = P₂` of
[M3, Lem. 3.3]. -/
@[category research solved, AMS 11 37 68, ref "FW65" "M3", group "bugeaud_10_47"]
theorem factorSet_eq_of_periodic_of_factor_eq {x y : ℕ → α} {p q a b : ℕ} (hp : 0 < p)
    (hq : 0 < q) (hx : Function.Periodic x p) (hy : Function.Periodic y q)
    (hfac : factor x (p + q) a = factor y (p + q) b) (n : ℕ) : factorSet x n = factorSet y n := by
  obtain ⟨c, hc⟩ := exists_shift_of_periodic_of_factor_eq hp hq hx hy hfac
  -- `x` reads `y` from position `c` on, and `y` is `q`-periodic, so nothing is lost either way
  have hshift : ∀ i, factor x n i = factor y n (i + c) := by
    intro i
    funext s
    simp only [factor]
    rw [hc (i + s), show i + s + c = i + c + s by ring]
  have hcq : c ≤ c * q := by
    calc c = c * 1 := (Nat.mul_one c).symm
      _ ≤ c * q := Nat.mul_le_mul_left c hq
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i + c, (hshift i).symm⟩
  · rintro ⟨j, rfl⟩
    refine ⟨j + c * q - c, ?_⟩
    rw [hshift (j + c * q - c), show j + c * q - c + c = j + c * q by omega]
    exact factor_add_mul_period hy n j c

/-- The same conclusion in the vocabulary of Problem 10.47: two periodic words with a common block
of length the sum of their periods have the same *recurrent* blocks, hence the same `p_∞`. -/
@[category research solved, AMS 11 37 68, ref "FW65" "M3", group "bugeaud_10_47"]
theorem recFactorSet_eq_of_periodic_of_factor_eq {x y : ℕ → α} {p q a b : ℕ} (hp : 0 < p)
    (hq : 0 < q) (hx : Function.Periodic x p) (hy : Function.Periodic y q)
    (hfac : factor x (p + q) a = factor y (p + q) b) (n : ℕ) :
    recFactorSet x n = recFactorSet y n := by
  rw [recFactorSet_eq_factorSet_of_periodic hp hx n, recFactorSet_eq_factorSet_of_periodic hq hy n]
  exact factorSet_eq_of_periodic_of_factor_eq hp hq hx hy hfac n

/-- ... and therefore the same `p_∞` at every level. -/
@[category research solved, AMS 11 37 68, ref "FW65" "M3", group "bugeaud_10_47"]
theorem pInf_eq_of_periodic_of_factor_eq [Finite α] {x y : ℕ → α} {p q a b : ℕ} (hp : 0 < p)
    (hq : 0 < q) (hx : Function.Periodic x p) (hy : Function.Periodic y q)
    (hfac : factor x (p + q) a = factor y (p + q) b) (n : ℕ) : pInf x n = pInf y n := by
  rw [pInf, pInf, recFactorSet_eq_of_periodic_of_factor_eq hp hq hx hy hfac n]

end BB47
