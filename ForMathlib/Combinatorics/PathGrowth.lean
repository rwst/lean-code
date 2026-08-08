/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Growth of word counts in a finite labelled digraph, from vector certificates

A **labelled digraph** is taken here in its most economical form: a `Finset (V × A × V)` of edges,
each carrying a source, a label and a target.  `words E s k` is the finite set of length-`k`
label words realised by paths of `E` that start at `s`.

This file bounds `#(words E s k)` above and below by geometric sequences, from a *vector
certificate*: a weight `v : V → ℕ` and a rational ratio `a / b` satisfying, entrywise,

`b * ∑ (v over the targets of the edges out of s) ≤ a * v s`   (upper), or the reverse (lower).

Both bounds are proved by a single induction on the weighted count, entirely inside `ℕ` — there is
no division, no eigenvalue, and no matrix.  This is deliberate: it is the elementary,
certificate-checkable shadow of the Perron–Frobenius bound "a subinvariant positive vector bounds
the spectral radius" (the Collatz–Wielandt inequality; see e.g. Seneta, *Non-negative Matrices and
Markov Chains*, Ch. 1), which Mathlib does not have — and which is not needed, since a certificate
supplies the eigenvector-like witness by hand.

## Main results

* `words` — the length-`k` words realised from a state, as a `Finset (List A)`.
* `card_words_le` — the upper certificate: `b * (M v) ≤ a * v` and `m ≤ v` give
  `m * (b ^ k * #(words E s k)) ≤ a ^ k * v s`.
* `card_words_le_pow` — its real-valued form `#(words E s k) ≤ (M / m) * (a / b) ^ k`, with the
  constant `M / m` the ratio of the extreme weights.
* `Deterministic`, `card_words_succ` — when source and label determine an edge, the count obeys the
  branch recursion with *equality*, which is what makes a lower bound possible.
* `le_card_words`, `pow_le_card_words` — the lower certificate, in `ℕ` and in `ℝ`.
* `words_mono` — monotone in the edge set, so a lower bound certified on a deterministic
  sub-digraph transfers to the ambient (possibly non-deterministic) one.
* `psum` — the weighted count: each edge carries a multiplicity, each path is charged the product
  along it, and the endpoint carries a weight.  This is the transfer operator `Mᵏ g` of the
  digraph.
* `psum_le`, `le_psum`, `psum_le_pow`, `pow_le_psum` — the same two certificates for `psum`.  The
  lower one needs **no determinism**, and neither needs extreme-weight constants: the bound is
  `(a / b) ^ k * v s` with the certificate's own weight at the starting state.
* `psum_const` — a constant edge weight factors out as `θ ^ k`, the degenerate case a
  single-slope map produces.

## Implementation notes

The state and label types are arbitrary with `DecidableEq`; no `Fintype` is required, because the
extreme weights `m ≤ v ≤ M` enter as hypotheses rather than as computed minima and maxima.  That is
also the shape a machine-generated certificate has.
-/

namespace PathGrowth

variable {V A : Type*} [DecidableEq V] [DecidableEq A]

/-- The edges of `E` leaving the state `s`. -/
def outEdges (E : Finset (V × A × V)) (s : V) : Finset (V × A × V) :=
  E.filter fun e => e.1 = s

/-- `words E s k` is the set of length-`k` label words realised by a path of `E` from `s`. -/
def words (E : Finset (V × A × V)) : V → ℕ → Finset (List A)
  | _, 0 => {[]}
  | s, k + 1 => (outEdges E s).biUnion fun e => (words E e.2.2 k).image (e.2.1 :: ·)

@[simp]
theorem words_zero (E : Finset (V × A × V)) (s : V) : words E s 0 = {[]} := rfl

theorem words_succ (E : Finset (V × A × V)) (s : V) (k : ℕ) :
    words E s (k + 1)
      = (outEdges E s).biUnion fun e => (words E e.2.2 k).image (e.2.1 :: ·) := rfl

@[simp]
theorem card_words_zero (E : Finset (V × A × V)) (s : V) : (words E s 0).card = 1 := rfl

/-- Every realised word has the announced length. -/
theorem length_of_mem_words (E : Finset (V × A × V)) :
    ∀ (k : ℕ) (s : V) {w : List A}, w ∈ words E s k → w.length = k := by
  intro k
  induction k with
  | zero => intro s w hw; simp only [words_zero, Finset.mem_singleton] at hw; simp [hw]
  | succ k ih =>
    intro s w hw
    rw [words_succ, Finset.mem_biUnion] at hw
    obtain ⟨e, -, he⟩ := hw
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp he
    simp [ih e.2.2 hu]

/-- Word counts obey the branch recursion as an inequality, always. -/
theorem card_words_succ_le (E : Finset (V × A × V)) (s : V) (k : ℕ) :
    (words E s (k + 1)).card ≤ ∑ e ∈ outEdges E s, (words E e.2.2 k).card := by
  rw [words_succ]
  exact le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun _ _ => Finset.card_image_le)

/-- The **upper vector certificate**.  If `v` is bounded below by `m` and satisfies
`b * ∑_{s → t} v t ≤ a * v s` at every state, then the length-`k` word count from `s` obeys
`m * (b ^ k * #(words E s k)) ≤ a ^ k * v s`.

The proof is one induction on the weighted count; no eigentheory is involved. -/
theorem card_words_le (E : Finset (V × A × V)) (v : V → ℕ) (a b m : ℕ)
    (hm : ∀ s, m ≤ v s)
    (hcert : ∀ s, b * ∑ e ∈ outEdges E s, v e.2.2 ≤ a * v s) :
    ∀ (k : ℕ) (s : V), m * (b ^ k * (words E s k).card) ≤ a ^ k * v s := by
  intro k
  induction k with
  | zero => intro s; simpa using hm s
  | succ k ih =>
    intro s
    calc m * (b ^ (k + 1) * (words E s (k + 1)).card)
        ≤ m * (b ^ (k + 1) * ∑ e ∈ outEdges E s, (words E e.2.2 k).card) := by
          gcongr
          exact card_words_succ_le E s k
      _ = b * ∑ e ∈ outEdges E s, m * (b ^ k * (words E e.2.2 k).card) := by
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun e _ => by ring
      _ ≤ b * ∑ e ∈ outEdges E s, a ^ k * v e.2.2 :=
          mul_le_mul_right (Finset.sum_le_sum fun e _ => ih e.2.2) _
      _ = a ^ k * (b * ∑ e ∈ outEdges E s, v e.2.2) := by
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun e _ => by ring
      _ ≤ a ^ k * (a * v s) := mul_le_mul_right (hcert s) _
      _ = a ^ (k + 1) * v s := by ring

/-- The real-valued upper bound: with weights confined to `[m, M]` and `m, b > 0`, the length-`k`
word count is at most `(M / m) * (a / b) ^ k`. -/
theorem card_words_le_pow (E : Finset (V × A × V)) (v : V → ℕ) (a b m M : ℕ)
    (hb : 0 < b) (hm : 0 < m) (hmv : ∀ s, m ≤ v s) (hvM : ∀ s, v s ≤ M)
    (hcert : ∀ s, b * ∑ e ∈ outEdges E s, v e.2.2 ≤ a * v s) (k : ℕ) (s : V) :
    ((words E s k).card : ℝ) ≤ (M / m) * (a / b) ^ k := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have key : (m : ℝ) * ((b : ℝ) ^ k * (words E s k).card) ≤ (a : ℝ) ^ k * v s := by
    exact_mod_cast card_words_le E v a b m hmv hcert k s
  have hvM' : ((v s : ℝ)) ≤ (M : ℝ) := by exact_mod_cast hvM s
  rw [div_pow, div_mul_div_comm, le_div_iff₀ (by positivity)]
  calc ((words E s k).card : ℝ) * ((m : ℝ) * (b : ℝ) ^ k)
      = (m : ℝ) * ((b : ℝ) ^ k * (words E s k).card) := by ring
    _ ≤ (a : ℝ) ^ k * (v s : ℝ) := key
    _ ≤ (a : ℝ) ^ k * (M : ℝ) := by gcongr
    _ = (M : ℝ) * (a : ℝ) ^ k := by ring

/-- `E` is **deterministic** when the source and the label of an edge determine its target — i.e.
no state has two outgoing edges carrying the same label. -/
def Deterministic (E : Finset (V × A × V)) : Prop :=
  ∀ e ∈ E, ∀ f ∈ E, e.1 = f.1 → e.2.1 = f.2.1 → e.2.2 = f.2.2

/-- Determinism is a finite check, so a certificate can discharge it by `decide`. -/
instance decidableDeterministic (E : Finset (V × A × V)) : Decidable (Deterministic E) :=
  inferInstanceAs (Decidable (∀ e ∈ E, ∀ f ∈ E, e.1 = f.1 → e.2.1 = f.2.1 → e.2.2 = f.2.2))

/-- For a deterministic edge set the branch recursion holds with **equality**: distinct outgoing
edges contribute disjoint sets of words, because they carry distinct first letters. -/
theorem card_words_succ {E : Finset (V × A × V)} (hdet : Deterministic E) (s : V) (k : ℕ) :
    (words E s (k + 1)).card = ∑ e ∈ outEdges E s, (words E e.2.2 k).card := by
  rw [words_succ, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun _ _ =>
      Finset.card_image_of_injective _ List.cons_injective
  · intro e he f hf hef
    simp only [Finset.mem_coe, outEdges, Finset.mem_filter] at he hf
    simp only [Function.onFun]
    rcases eq_or_ne e.2.1 f.2.1 with hlab | hlab
    · refine absurd ?_ hef
      have h1 : e.1 = f.1 := he.2.trans hf.2.symm
      have h3 : e.2.2 = f.2.2 := hdet e he.1 f hf.1 h1 hlab
      obtain ⟨e1, e2, e3⟩ := e
      obtain ⟨f1, f2, f3⟩ := f
      simp_all
    · rw [Finset.disjoint_left]
      rintro w hw hw'
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨y, -, hy⟩ := Finset.mem_image.mp hw'
      simp only [List.cons.injEq] at hy
      exact hlab hy.1.symm

/-- The **lower vector certificate**.  On a deterministic edge set, if `v` is bounded above by `M`
and satisfies `a * v s ≤ b * ∑_{s → t} v t` at every state, then
`a ^ k * v s ≤ M * (b ^ k * #(words E s k))`. -/
theorem le_card_words {E : Finset (V × A × V)} (hdet : Deterministic E) (v : V → ℕ) (a b M : ℕ)
    (hM : ∀ s, v s ≤ M)
    (hcert : ∀ s, a * v s ≤ b * ∑ e ∈ outEdges E s, v e.2.2) :
    ∀ (k : ℕ) (s : V), a ^ k * v s ≤ M * (b ^ k * (words E s k).card) := by
  intro k
  induction k with
  | zero => intro s; simpa using hM s
  | succ k ih =>
    intro s
    calc a ^ (k + 1) * v s
        = a ^ k * (a * v s) := by ring
      _ ≤ a ^ k * (b * ∑ e ∈ outEdges E s, v e.2.2) := mul_le_mul_right (hcert s) _
      _ = b * ∑ e ∈ outEdges E s, a ^ k * v e.2.2 := by
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun e _ => by ring
      _ ≤ b * ∑ e ∈ outEdges E s, M * (b ^ k * (words E e.2.2 k).card) :=
          mul_le_mul_right (Finset.sum_le_sum fun e _ => ih e.2.2) _
      _ = M * (b ^ (k + 1) * ∑ e ∈ outEdges E s, (words E e.2.2 k).card) := by
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun e _ => by ring
      _ = M * (b ^ (k + 1) * (words E s (k + 1)).card) := by rw [card_words_succ hdet]

/-- The real-valued lower bound: on a deterministic edge set with weights confined to `[m, M]` and
`M, b > 0`, the length-`k` word count is at least `(m / M) * (a / b) ^ k`. -/
theorem pow_le_card_words {E : Finset (V × A × V)} (hdet : Deterministic E) (v : V → ℕ)
    (a b m M : ℕ) (hb : 0 < b) (hM : 0 < M) (hmv : ∀ s, m ≤ v s) (hvM : ∀ s, v s ≤ M)
    (hcert : ∀ s, a * v s ≤ b * ∑ e ∈ outEdges E s, v e.2.2) (k : ℕ) (s : V) :
    ((m : ℝ) / M) * ((a : ℝ) / b) ^ k ≤ ((words E s k).card : ℝ) := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have key : (a : ℝ) ^ k * (v s : ℝ) ≤ (M : ℝ) * ((b : ℝ) ^ k * (words E s k).card) := by
    exact_mod_cast le_card_words hdet v a b M hvM hcert k s
  have hmv' : ((m : ℝ)) ≤ (v s : ℝ) := by exact_mod_cast hmv s
  rw [div_pow, div_mul_div_comm, div_le_iff₀ (by positivity)]
  calc (m : ℝ) * (a : ℝ) ^ k
      = (a : ℝ) ^ k * (m : ℝ) := by ring
    _ ≤ (a : ℝ) ^ k * (v s : ℝ) := by gcongr
    _ ≤ (M : ℝ) * ((b : ℝ) ^ k * (words E s k).card) := key
    _ = ((words E s k).card : ℝ) * ((M : ℝ) * (b : ℝ) ^ k) := by ring

/-- Word sets are monotone in the edge set.  Combined with `pow_le_card_words` this is the
intended lower-bound workflow: certify a *deterministic sub*-digraph, then transfer the bound to
the ambient edge set, which need not be deterministic. -/
theorem words_mono {E E' : Finset (V × A × V)} (h : E' ⊆ E) :
    ∀ (k : ℕ) (s : V), words E' s k ⊆ words E s k := by
  intro k
  induction k with
  | zero => intro s; simp
  | succ k ih =>
    intro s
    rw [words_succ, words_succ]
    refine Finset.biUnion_subset.mpr fun e he => ?_
    have heE : e ∈ outEdges E s := by
      simp only [outEdges, Finset.mem_filter] at he ⊢
      exact ⟨h he.1, he.2⟩
    exact (Finset.image_subset_image (ih e.2.2)).trans
      (Finset.subset_biUnion_of_mem (fun e => (words E e.2.2 k).image (e.2.1 :: ·)) heE)

/-- Consequently the ambient word count dominates that of any sub-digraph. -/
theorem card_words_mono {E E' : Finset (V × A × V)} (h : E' ⊆ E) (k : ℕ) (s : V) :
    (words E' s k).card ≤ (words E s k).card :=
  Finset.card_le_card (words_mono h k s)

/-! ### Weighted path sums

The same certificates bound a *weighted* count, in which each edge carries a multiplicity `θ e`
and a path is charged the product of the multiplicities along it, times a weight `g` at the state
it ends in.  Read as a matrix, `psum E θ g s k` is `(Mᵏ g) s` for the nonnegative matrix `M` with
entries `θ` — the transfer operator of the labelled digraph — so what follows is Collatz–Wielandt
for `M`, in the same certificate-checkable form as above.

Two things are *cheaper* here than for `words`:

* the branch recursion holds **by definition**, so the lower bound needs no determinism
  hypothesis (for `words` it does: see `card_words_succ`);
* the base case is exact, so no extreme-weight constants `m`, `M` are needed — the bound is
  `(a / b) ^ k * v s`, with the certificate's own weight at the starting state as the constant.
-/

/-- `psum E θ g s k` — the total weight of the length-`k` paths of `E` out of `s`: a path is
charged the product of the weights `θ` of its edges, times the weight `g` of the state it ends in.
Equivalently the `k`-th iterate of the transfer operator with matrix `θ`, applied to `g`. -/
def psum (E : Finset (V × A × V)) (θ : V × A × V → ℕ) (g : V → ℕ) : V → ℕ → ℕ
  | s, 0 => g s
  | s, k + 1 => ∑ e ∈ outEdges E s, θ e * psum E θ g e.2.2 k

section Weighted

omit [DecidableEq A]

@[simp]
theorem psum_zero (E : Finset (V × A × V)) (θ : V × A × V → ℕ) (g : V → ℕ) (s : V) :
    psum E θ g s 0 = g s := rfl

theorem psum_succ (E : Finset (V × A × V)) (θ : V × A × V → ℕ) (g : V → ℕ) (s : V) (k : ℕ) :
    psum E θ g s (k + 1) = ∑ e ∈ outEdges E s, θ e * psum E θ g e.2.2 k := rfl

/-- The **upper vector certificate**, weighted.  If `g ≤ v` and `b * (M v) ≤ a * v` entrywise,
then `bᵏ * psum ≤ aᵏ * v s`. -/
theorem psum_le (E : Finset (V × A × V)) (θ : V × A × V → ℕ) (g v : V → ℕ) (a b : ℕ)
    (hg : ∀ s, g s ≤ v s)
    (hcert : ∀ s, b * ∑ e ∈ outEdges E s, θ e * v e.2.2 ≤ a * v s) :
    ∀ (k : ℕ) (s : V), b ^ k * psum E θ g s k ≤ a ^ k * v s := by
  intro k
  induction k with
  | zero => intro s; simpa using hg s
  | succ k ih =>
    intro s
    calc b ^ (k + 1) * psum E θ g s (k + 1)
        = b * ∑ e ∈ outEdges E s, θ e * (b ^ k * psum E θ g e.2.2 k) := by
          rw [psum_succ, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun e _ => by ring
      _ ≤ b * ∑ e ∈ outEdges E s, θ e * (a ^ k * v e.2.2) :=
          Nat.mul_le_mul_left _
            (Finset.sum_le_sum fun e _ => Nat.mul_le_mul_left _ (ih e.2.2))
      _ = a ^ k * (b * ∑ e ∈ outEdges E s, θ e * v e.2.2) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun e _ => by ring
      _ ≤ a ^ k * (a * v s) := Nat.mul_le_mul_left _ (hcert s)
      _ = a ^ (k + 1) * v s := by ring

/-- The **lower vector certificate**, weighted.  No determinism is required: unlike a set of
words, a weighted sum over paths obeys the branch recursion by definition. -/
theorem le_psum (E : Finset (V × A × V)) (θ : V × A × V → ℕ) (g v : V → ℕ) (a b : ℕ)
    (hg : ∀ s, v s ≤ g s)
    (hcert : ∀ s, a * v s ≤ b * ∑ e ∈ outEdges E s, θ e * v e.2.2) :
    ∀ (k : ℕ) (s : V), a ^ k * v s ≤ b ^ k * psum E θ g s k := by
  intro k
  induction k with
  | zero => intro s; simpa using hg s
  | succ k ih =>
    intro s
    calc a ^ (k + 1) * v s
        = a ^ k * (a * v s) := by ring
      _ ≤ a ^ k * (b * ∑ e ∈ outEdges E s, θ e * v e.2.2) := Nat.mul_le_mul_left _ (hcert s)
      _ = b * ∑ e ∈ outEdges E s, θ e * (a ^ k * v e.2.2) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun e _ => by ring
      _ ≤ b * ∑ e ∈ outEdges E s, θ e * (b ^ k * psum E θ g e.2.2 k) :=
          Nat.mul_le_mul_left _
            (Finset.sum_le_sum fun e _ => Nat.mul_le_mul_left _ (ih e.2.2))
      _ = b ^ (k + 1) * psum E θ g s (k + 1) := by
          rw [psum_succ, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun e _ => by ring

/-- The real-valued weighted upper bound. -/
theorem psum_le_pow (E : Finset (V × A × V)) (θ : V × A × V → ℕ) (g v : V → ℕ) (a b : ℕ)
    (hb : 0 < b) (hg : ∀ s, g s ≤ v s)
    (hcert : ∀ s, b * ∑ e ∈ outEdges E s, θ e * v e.2.2 ≤ a * v s) (k : ℕ) (s : V) :
    ((psum E θ g s k : ℕ) : ℝ) ≤ ((a : ℝ) / b) ^ k * v s := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have key : ((b : ℝ)) ^ k * (psum E θ g s k : ℝ) ≤ (a : ℝ) ^ k * v s := by
    exact_mod_cast psum_le E θ g v a b hg hcert k s
  rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  calc ((psum E θ g s k : ℕ) : ℝ) * (b : ℝ) ^ k
      = (b : ℝ) ^ k * ((psum E θ g s k : ℕ) : ℝ) := by ring
    _ ≤ (a : ℝ) ^ k * v s := key

/-- The real-valued weighted lower bound. -/
theorem pow_le_psum (E : Finset (V × A × V)) (θ : V × A × V → ℕ) (g v : V → ℕ) (a b : ℕ)
    (hb : 0 < b) (hg : ∀ s, v s ≤ g s)
    (hcert : ∀ s, a * v s ≤ b * ∑ e ∈ outEdges E s, θ e * v e.2.2) (k : ℕ) (s : V) :
    ((a : ℝ) / b) ^ k * v s ≤ ((psum E θ g s k : ℕ) : ℝ) := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have key : ((a : ℝ)) ^ k * (v s : ℝ) ≤ (b : ℝ) ^ k * psum E θ g s k := by
    exact_mod_cast le_psum E θ g v a b hg hcert k s
  rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  calc (a : ℝ) ^ k * (v s : ℝ) ≤ (b : ℝ) ^ k * ((psum E θ g s k : ℕ) : ℝ) := key
    _ = ((psum E θ g s k : ℕ) : ℝ) * (b : ℝ) ^ k := by ring

end Weighted

/-- A **constant** edge weight factors straight out: on a deterministic edge set the weighted count
is `θ ^ k` times the plain word count.  This is the degenerate case of the transfer operator — the
one a piecewise-affine map with a single slope produces, where the leading eigenvalue is simply
scaled and the pressure is affine in the weight's logarithm. -/
theorem psum_const {E : Finset (V × A × V)} (hdet : Deterministic E) (θ : ℕ) :
    ∀ (k : ℕ) (s : V), psum E (fun _ => θ) (fun _ => 1) s k = θ ^ k * (words E s k).card := by
  intro k
  induction k with
  | zero => intro s; simp
  | succ k ih =>
    intro s
    rw [psum_succ, card_words_succ hdet, Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by rw [ih e.2.2]; ring

/-- With unit weights the weighted sum is the word count itself. -/
theorem psum_one {E : Finset (V × A × V)} (hdet : Deterministic E) (k : ℕ) (s : V) :
    psum E (fun _ => 1) (fun _ => 1) s k = (words E s k).card := by
  simpa using psum_const hdet 1 k s

/-! ### Regression test

The golden-mean shift — binary words avoiding the block `11` — as a two-state labelled digraph,
the state recording the last letter.  Its word counts are the Fibonacci numbers, and everything in
this file is computable enough for the kernel to confirm that. -/

/-- The golden-mean shift: edges `0 -0→ 0`, `0 -1→ 1`, `1 -0→ 0`. -/
def goldenMean : Finset (Fin 2 × Fin 2 × Fin 2) := {(0, 0, 0), (0, 1, 1), (1, 0, 0)}

example : Deterministic goldenMean := by decide

set_option maxRecDepth 4000 in
example :
    ((List.range 9).map fun k => (words goldenMean 0 k).card) = [1, 2, 3, 5, 8, 13, 21, 34, 55] := by
  decide

/- Weighting the letter `1` by `2` and the letter `0` by `1` charges a golden-mean word `2` per
one it contains, giving `aₖ₊₂ = aₖ₊₁ + 2aₖ`, the Jacobsthal numbers.  Unlike the two examples
above, this one exercises a *non-constant* edge weight. -/
set_option maxRecDepth 4000 in
example :
    ((List.range 9).map fun k =>
        psum goldenMean (fun e => if e.2.1 = 1 then 2 else 1) (fun _ => 1) 0 k)
      = [1, 3, 5, 11, 21, 43, 85, 171, 341] := by
  decide

end PathGrowth
