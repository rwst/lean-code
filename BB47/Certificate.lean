/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB47.Basic

/-!
# What a finite prefix can certify — and what it cannot

This is §2 of `BB47/M4.tex`, milestone M4 of `plans/plan-1047.html`: the theorems that the
`10⁹`-digit computation on `√2, √3, φ` in bases `2, 3, 10` instantiates.

The milestone was originally scoped as "evidence that `p_∞(n, √2, b)` is in fact full".  It is not
deliverable at any length, and `BB47.exists_minimal_extension` below is the proof: append a
recurrent minimal-complexity tail to **any** prefix whatsoever and the result has `p_∞(n) = n + 1`
for every `n`, with horizon at most the length of that prefix.  So for every `N` and every `n` the
computed data is consistent with `p_∞(n, ξ, b) = n + 1`, and the only question a computation can
answer is *how far out* the transition would have to be pushed.

What is deliverable is a family of **certificates**, each of the shape

> either `p_∞(n, w) > K`, or the non-recurrent prefix satisfies `s_n > i`,

produced by a finite window of `w` starting at position `i`.  Three of them are proved here.  The
first turns out not to be an estimate at all: under the hypothesis of Problem 10.47 it *computes*
`s_n` (`BB47.card_image_ge_of_horizon` together with `BB47.lt_horizon_of_card_gt`).

## Main results

* `BB47.lt_horizon_of_card_gt` — **[M4, Prop. 2.1], the block certificate.**  A window carrying
  more than `p_∞(n, w)` distinct length-`n` blocks lies (at its left end) inside the non-recurrent
  prefix.
* `BB47.card_image_ge_of_horizon` — **[M4, Prop. 2.2], exactness.**  Conversely, once the data
  reaches far enough to show all `n + 1` recurrent blocks, the window starting one position
  earlier carries `n + 2` of them.  So the backward scan does not estimate `s_n`, it returns it.
* `BB47.lt_horizon_of_imbalance` — **[M4, Prop. 2.3], the balance certificate**, consuming the
  balance of `L(Ω)` proved in [M3, Cor. 4.2].
* `BB47.le_horizon_add_of_tripleBreak` — **[M4, Prop. 2.4], the period certificate**, consuming
  the two-element-run structure of [M3, Prop. 6.1] in the skew branch.
* `BB47.exists_minimal_extension` — **[M4, Rem. 2.5], the ceiling.**

## Indexing, and how to read the certificates against the data

Positions are `0`-based.  A window of `w` beginning at `0`-based position `i` begins at `1`-based
position `i + 1`, and the conclusion `i < horizon w n` of the certificates is the `s_n ≥ i` of the
note, verbatim.

The measured statement of [M4, Cor. 6.1] is the instantiation of `BB47.lt_horizon_of_card_gt` with
`K = n + 1`, `N = 10⁹`, and the window `[N − 2n − 1, N)`: for `√2, √3, φ` in bases `2, 3, 10` and
every `8 ≤ n ≤ n_max` (`n_max = 63, 39, 18`) those last `2n + 1` digits already carry `n + 2`
distinct length-`n` blocks, whence

  `p_∞(n, ξ, b) = n + 1  ⟹  s_n ≥ 10⁹ − 2n`.

That reach is **information-theoretically saturated**: a window carrying `n + 2` distinct
length-`n` blocks must have length at least `2n + 1`, since a window of length `L` carries at most
`L − n + 1` of them.  No longer computation improves it; a `10¹²`-digit run would buy only the
logarithm.  Problem 10.47 is not a computational question.

## References

* [M3] `BB47/M3.tex` (this repository, 2026-09) — Thm. 4.1 (the structure theorem), Cor. 4.2
  (balance), Prop. 6.1 (the two-element runs of the skew branch).
* [M4] `BB47/M4.tex` (this repository, 2026-09) — §2, Props. 2.1–2.4, Rem. 2.5; §6, Cor. 6.1.
* [BKK26] Y. Bugeaud, H. Kaneko, D. H. Kim, arXiv:2510.17177 — Defs. 2.4–2.5.
* [Lot02] M. Lothaire, *Algebraic Combinatorics on Words*, CUP 2002, Ch. 2 — balanced words.
-/

namespace BB47

open ForMathlib.SubwordComplexity

variable {α : Type*}

/-! ## The block certificate -/

/-- **[M4, Prop. 2.1], the block certificate.**  If a set `S` of positions, all at least `i`,
carries more than `K` distinct length-`n` blocks while `p_∞(n, w) ≤ K`, then `i` lies strictly
inside the non-recurrent prefix: `s_n > i`.

This is the only shape of statement a finite prefix supports, and it bounds `s_n` from **below**
only — see `BB47.exists_minimal_extension`. -/
@[category research solved, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem lt_horizon_of_card_gt [Finite α] [DecidableEq α] {u : ℕ → α} {n K i : ℕ}
    (hK : pInf u n ≤ K) (S : Finset ℕ) (hS : ∀ p ∈ S, i ≤ p)
    (hcard : K < (S.image (factor u n)).card) : i < horizon u n := by
  by_contra hcon
  push Not at hcon
  have hfin : (recFactorSet u n).Finite := Set.toFinite _
  have hsub : S.image (factor u n) ⊆ hfin.toFinset := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    rw [Set.Finite.mem_toFinset]
    exact recurrent_of_horizon_le (le_trans hcon (hS p hp))
  have hle : (S.image (factor u n)).card ≤ pInf u n := by
    rw [pInf, Set.ncard_eq_toFinset_card _ hfin]
    exact Finset.card_le_card hsub
  omega

/-- **[M4, Prop. 2.2], exactness — the converse half.**  Suppose `p_∞(n, w) = n + 1` (the
hypothesis of Problem 10.47), the horizon is `h + 1`, and the positions `T`, all beyond the
horizon, already exhibit **every** recurrent length-`n` block.  Then adjoining the single position
`h` produces `n + 2` distinct blocks.

Together with `BB47.lt_horizon_of_card_gt` at `K = n + 1` this says that the largest window start
carrying `n + 2` distinct length-`n` blocks is exactly `h = s_n − 1`: the backward scan
**computes** `s_n` rather than bounding it.  For a Sturmian tail the "already exhibit every
recurrent block" costs `2n + 1` digits, which is what makes the measured reach `2n`. -/
@[category research solved, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem card_image_ge_of_horizon [Finite α] [DecidableEq α] {u : ℕ → α} {n h : ℕ}
    (hp : pInf u n = n + 1) (hh : horizon u n = h + 1) (T : Finset ℕ)
    (hT : ∀ p ∈ T, h + 1 ≤ p) (hfull : recFactorSet u n ⊆ ↑(T.image (factor u n))) :
    n + 2 ≤ ((insert h T).image (factor u n)).card := by
  have hfin : (recFactorSet u n).Finite := Set.toFinite _
  -- the image of `T` is exactly the recurrent language
  have hTsub : T.image (factor u n) ⊆ hfin.toFinset := by
    intro x hx
    obtain ⟨p, hpT, rfl⟩ := Finset.mem_image.mp hx
    rw [Set.Finite.mem_toFinset]
    exact recurrent_of_horizon_le (by rw [hh]; exact hT p hpT)
  have hsup : hfin.toFinset ⊆ T.image (factor u n) := by
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    exact hfull hx
  have hTcard : (T.image (factor u n)).card = n + 1 := by
    have := Finset.Subset.antisymm hTsub hsup
    rw [this, ← Set.ncard_eq_toFinset_card _ hfin, ← pInf, hp]
  -- the block at `h` is not recurrent, hence not in that image
  have hnot : factor u n h ∉ T.image (factor u n) := by
    intro hmem
    exact not_recurrent_pred hh ((Set.Finite.mem_toFinset hfin).mp (hTsub hmem))
  rw [Finset.image_insert, Finset.card_insert_of_notMem hnot, hTcard]

/-! ## The balance certificate -/

section Balance

variable [DecidableEq α]

/-- The number of occurrences of the letter `v` in a block. -/
@[category API, AMS 11 37 68, ref "Lot02", group "bugeaud_10_47"]
def wt {n : ℕ} (v : α) (x : Fin n → α) : ℕ := (Finset.univ.filter fun s => x s = v).card

/-- **Balance at a letter.**  Any two recurrent length-`n` blocks have `v`-weights differing by at
most one.  Under the standing hypothesis (H) of `BB47/M3.tex` the recurrent language is balanced
in this sense at each of the two letters of the recurrent subalphabet [M3, Cor. 4.2] — because
`Ω` is then the orbit closure of an aperiodic point of minimal complexity, hence Sturmian in the
sense of [CH73, Def. 3.08], hence satisfies the Sturmian Block Condition. -/
@[category API, AMS 11 37 68, ref "Lot02" "CH73", group "bugeaud_10_47"]
def BalancedAt [Finite α] (u : ℕ → α) (n : ℕ) (v : α) : Prop :=
  ∀ x ∈ recFactorSet u n, ∀ y ∈ recFactorSet u n, wt v x ≤ wt v y + 1

/-- **[M4, Prop. 2.3], the balance certificate.**  If the recurrent language is balanced at `v`
and two positions `≥ i` carry length-`n` blocks whose `v`-weights differ by at least `2`, then
`s_n > i`.

Quantifying over *every* letter, as [M4, Prop. 2.3] does, is what makes the certificate usable
without knowing which two letters of the alphabet carry the recurrent subalphabet: see
`BB47.lt_horizon_of_imbalance_all`. -/
@[category research solved, AMS 11 37 68, ref "Lot02" "CH73", group "bugeaud_10_47"]
theorem lt_horizon_of_imbalance [Finite α] {u : ℕ → α} {n i p q : ℕ} {v : α}
    (hbal : BalancedAt u n v) (hp : i ≤ p) (hq : i ≤ q)
    (himb : wt v (factor u n p) + 2 ≤ wt v (factor u n q)) : i < horizon u n := by
  by_contra hcon
  push Not at hcon
  have hrp : factor u n p ∈ recFactorSet u n := recurrent_of_horizon_le (le_trans hcon hp)
  have hrq : factor u n q ∈ recFactorSet u n := recurrent_of_horizon_le (le_trans hcon hq)
  have := hbal _ hrq _ hrp
  omega

/-- The form actually run on the data: imbalance witnessed at **every** letter, plus balance at
*some* letter, certifies the horizon.  The hypothesis `hbal` is what [M3, Cor. 4.2] supplies under
(H); the computation supplies `himb`. -/
@[category research solved, AMS 11 37 68, ref "Lot02" "CH73", group "bugeaud_10_47"]
theorem lt_horizon_of_imbalance_all [Finite α] {u : ℕ → α} {n i : ℕ} {v₀ : α}
    (hbal : BalancedAt u n v₀)
    (himb : ∀ v : α, ∃ p q, i ≤ p ∧ i ≤ q ∧ wt v (factor u n p) + 2 ≤ wt v (factor u n q)) :
    i < horizon u n := by
  obtain ⟨p, q, hp, hq, h⟩ := himb v₀
  exact lt_horizon_of_imbalance hbal hp hq h

end Balance

/-! ## The period certificate -/

/-- The lag-`q` **break set** `T_q = {k : w_{k+q} ≠ w_k}` of [M3, Prop. 6.1]. -/
@[category API, AMS 11 37 68, ref "CH73", group "bugeaud_10_47"]
def breakSet (u : ℕ → α) (q : ℕ) : Set ℕ := {k | u (k + q) ≠ u k}

/-- The structural input of [M3, Prop. 6.1]: in the skew branch (b) of [M3, Thm. 4.1] with least
period `q`, every maximal run of consecutive integers in `T_q ∩ (m, ∞)` has exactly two elements,
where `m = s_n + n`.  In particular no three consecutive integers lie in `T_q` beyond `m`. -/
@[category API, AMS 11 37 68, ref "CH73", group "bugeaud_10_47"]
def NoTripleBreakAbove (u : ℕ → α) (q m : ℕ) : Prop :=
  ∀ k, m < k → ¬ (k ∈ breakSet u q ∧ k + 1 ∈ breakSet u q ∧ k + 2 ∈ breakSet u q)

/-- **[M4, Prop. 2.4], the period certificate.**  Under the run structure of [M3, Prop. 6.1], a
*triple* of consecutive lag-`q` breaks at `k` forces `k ≤ s_n + n`, i.e. `s_n ≥ k − n`.

Run over all lags `q ≤ Q` this is the statement "if the `ω`-limit set is in the skew branch with
least period `q ≤ Q`, then `s_n ≥ min_q K_q − n` for every `n > Q + 2`", which is how
`BB47/m4period.py` reports it. -/
@[category research solved, AMS 11 37 68, ref "CH73", group "bugeaud_10_47"]
theorem le_horizon_add_of_tripleBreak [Finite α] {u : ℕ → α} {n q k : ℕ}
    (hrun : NoTripleBreakAbove u q (horizon u n + n))
    (h₀ : k ∈ breakSet u q) (h₁ : k + 1 ∈ breakSet u q) (h₂ : k + 2 ∈ breakSet u q) :
    k ≤ horizon u n + n := by
  by_contra hcon
  exact hrun k (by omega) ⟨h₀, h₁, h₂⟩

/-! ## The ceiling: no finite prefix constrains `p_∞` -/

/-- Graft the tail `f` onto the first `N` letters of `v`. -/
@[category API, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
def graft (v : ℕ → α) (N : ℕ) (f : ℕ → α) : ℕ → α := fun k => if k < N then v k else f (k - N)

@[simp]
lemma graft_of_lt {v f : ℕ → α} {N k : ℕ} (hk : k < N) : graft v N f k = v k := by
  simp [graft, hk]

@[simp]
lemma tail_graft (v : ℕ → α) (N : ℕ) (f : ℕ → α) : tail (graft v N f) N = f := by
  funext k
  simp only [tail, graft]
  split_ifs with h
  · exact absurd h (by omega)
  · congr 1
    omega

/-- **[M4, Rem. 2.5], the ceiling.**  Given *any* prefix of length `N` and any word `f` that is
recurrent with minimal eventual complexity — a Sturmian word, for instance — there is an infinite
word that agrees with the prefix, satisfies `p_∞(n) = n + 1` for **every** `n`, and has
`s_n ≤ N` for every `n`.

So no function of a finite portion of the base-`b` expansion of `√2` can ever refute
`p_∞(n, √2, b) = n + 1`.  All three certificates above bound `s_n` from below; that is not a
limitation of the instruments but a theorem about what finite data can say. -/
@[category research solved, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem exists_minimal_extension [Finite α] (v f : ℕ → α) (N : ℕ)
    (hfrec : ∀ n, horizon f n = 0) (hfmin : ∀ n, pInf f n = n + 1) :
    ∃ g : ℕ → α, (∀ k, k < N → g k = v k) ∧ (∀ n, pInf g n = n + 1) ∧
      (∀ n, horizon g n ≤ N) := by
  refine ⟨graft v N f, fun k hk => graft_of_lt hk, fun n => ?_, fun n => ?_⟩
  · have h1 : pInf (tail (graft v N f) N) n = pInf (graft v N f) n := pInf_tail _ _ _
    rw [tail_graft] at h1
    rw [← h1, hfmin n]
  · have := horizon_le_tail (graft v N f) N n
    rw [tail_graft, hfrec n] at this
    omega

/-- The same statement read as a sensitivity claim: the certificates return the **planted**
horizon, not the length of the data.  This is what `BB47/M4.tex` §5 checks numerically at
`P = 10³, 10⁶, 10⁸`. -/
@[category research solved, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem horizon_graft_le [Finite α] (v f : ℕ → α) (N n : ℕ) :
    horizon (graft v N f) n ≤ N + horizon f n := by
  have := horizon_le_tail (graft v N f) N n
  rwa [tail_graft] at this

end BB47
