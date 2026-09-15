/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import ForMathlib.Combinatorics.Sturmian
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Recurrent blocks, the eventual complexity `p_∞`, and the non-recurrent prefix

This is the combinatorial core of milestone M1 of `plans/plan-1047.html`, i.e. §2 of the note
`BB47/M1M2.tex`, together with the rigidity lemma §3 of `BB47/M3.tex`.  It is the layer that
Bugeaud's Problem 10.47 is stated in.

For an infinite word `u : ℕ → α` a length-`n` factor is **recurrent** when it occurs at
infinitely many positions, and

  `p_∞(n, u) := #{recurrent length-n factors}`  (`BB47.pInf`)

is the function of Problem 10.47: the book asks for a nontrivial lower bound on `p_∞(n, ξ, b)`
for algebraic irrational `ξ`, and remarks that `p_∞(n, √2, b) = n + 1` — the absolute floor —
cannot currently be excluded.

The second object is the **non-recurrent prefix**.  Over a finite alphabet only finitely many
length-`n` blocks fail to recur and each of those has a last occurrence, so there is a least
position beyond which every length-`n` block recurs:

  `s_n = horizon u n`  (`BB47.horizon`),

the `s_n` of Bugeaud–Kaneko–Kim [BKK26, Defs. 2.4–2.5].  *Positions here are `0`-based*, matching
`ForMathlib.SubwordComplexity.factor`; the notes index words from `1`, so `horizon u n` is the
`s_n` of `BB47/M1M2.tex` verbatim (both count the letters of the discarded prefix).

## Main results

* `BB47.exists_nRecurrentFrom` — the horizon exists (finite alphabet).
* `BB47.recurrent_of_horizon_le`, `BB47.not_recurrent_pred` — existence *and minimality*:
  together these are [M1M2, Prop. 2.2].
* `BB47.factorSet_tail_eq`, `BB47.pInf_eq_pComplexity_tail` — [M1M2, Lem. 2.3(i),(iii)]: the
  recurrent language of `u` is the *full* language of any tail beyond the horizon.  This is the
  identity that makes every statement below a statement about one ordinary word.
* `BB47.horizon_mono` — [M1M2, Lem. 2.3(ii)]: `s_n ≤ s_{n+1}`.
* `BB47.succ_le_pInf` — [M1M2, Lem. 2.3(iv)]: the Morse–Hedlund floor `p_∞(n) ≥ n + 1`, i.e. the
  baseline quoted in Problem 10.47.
* `BB47.pInf_lt_succ`, `BB47.strictMono_pInf` — [M3, Lem. 3.1]: `p_∞` is **strictly** increasing.
* `BB47.pInf_eq_succ_of_le`, `BB47.pInf_eq_succ_of_frequently` — the rigidity consequence: minimal
  eventual complexity at one scale forces it at all smaller scales, and at infinitely many scales
  forces it at *every* scale.  This is what lets the standing hypothesis (H) of `BB47/M3.tex` be
  stated with "for infinitely many `n`" and used with "for all `n`".
* `BB47.pInf_tail`, `BB47.horizon_tail_le`, `BB47.horizon_le_tail` — `p_∞` is a tail invariant
  while the horizon moves by at most the length of the discarded prefix.  This is the *ceiling*
  of [M4, Rem. 2.5]; see `BB47/Certificate.lean` for the statement it yields.

## Proof notes

The one trick worth naming is `pInf_eq_pComplexity_tail`: because `s_n ≤ s_{n+1}`, the *single*
word `tail u s_{n+1}` computes `p_∞` at both level `n` and level `n+1`.  So the Morse–Hedlund
machinery of `ForMathlib.Combinatorics.InfiniteComplexity`, which is about ordinary complexity of
one word, applies verbatim and delivers strict monotonicity of `p_∞` in two lines — considerably
shorter than the Rauzy-graph argument of [M3, Lem. 3.1], which computed the increment as a sum of
out-degrees.

## References

* [Bug12] Y. Bugeaud, *Distribution Modulo One and Diophantine Approximation*, Cambridge Tracts
  193, CUP 2012 — Problem 10.47, p. 221.
* [BKK26] Y. Bugeaud, H. Kaneko, D. H. Kim, *On the irrationality exponent of real numbers with
  low complexity expansion*, arXiv:2510.17177 — §2.2, Defs. 2.4–2.5 (the non-recurrent prefix
  `a_n` and `s_n`, and the reduced Rauzy graph).
* [M1M2] `BB47/M1M2.tex` (this repository, 2026-09) — §2 (Prop. 2.2, Lem. 2.3).
* [M3] `BB47/M3.tex` (this repository, 2026-09) — Lem. 3.1 (rigidity).
* [M4] `BB47/M4.tex` (this repository, 2026-09) — Rem. 2.5 (the ceiling).
* [MH38] M. Morse, G. A. Hedlund, *Symbolic dynamics*, Amer. J. Math. **60** (1938), 815–866.
-/

namespace BB47

open ForMathlib.SubwordComplexity

variable {α : Type*}

/-! ## Recurrent factors and `p_∞` -/

/-- A length-`n` block `v` is **recurrent** in `u` when it occurs at arbitrarily late positions,
equivalently at infinitely many positions. -/
@[category API, AMS 11 37 68, ref "Bug12" "BKK26", group "bugeaud_10_47"]
def Recurrent (u : ℕ → α) (n : ℕ) (v : Fin n → α) : Prop :=
  ∀ N, ∃ i, N ≤ i ∧ factor u n i = v

/-- The set of recurrent length-`n` factors of `u` — the language of the `ω`-limit subshift
`Ω(u)` at level `n`. -/
@[category API, AMS 11 37 68, ref "Bug12" "BKK26", group "bugeaud_10_47"]
def recFactorSet (u : ℕ → α) (n : ℕ) : Set (Fin n → α) := {v | Recurrent u n v}

@[simp]
lemma mem_recFactorSet {u : ℕ → α} {n : ℕ} {v : Fin n → α} :
    v ∈ recFactorSet u n ↔ Recurrent u n v := Iff.rfl

/-- **The function of Problem 10.47.**  `p_∞(n, u)` is the number of length-`n` blocks occurring
infinitely often in `u`.  Equivalently (see `BB47/M1M2.tex`, Prop. 2.4) it is the factor
complexity `p(n, Ω(u))` of the `ω`-limit subshift. -/
@[category API, AMS 11 37 68, ref "Bug12" "BKK26", group "bugeaud_10_47"]
noncomputable def pInf [Finite α] (u : ℕ → α) (n : ℕ) : ℕ := (recFactorSet u n).ncard

/-- Recurrence passes to prefixes: every occurrence of `v` carries one of its truncation. -/
@[category API, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
lemma Recurrent.castSucc {u : ℕ → α} {n : ℕ} {v : Fin (n + 1) → α} (h : Recurrent u (n + 1) v) :
    Recurrent u n (v ∘ Fin.castSucc) := by
  intro N
  obtain ⟨i, hi, hfi⟩ := h N
  exact ⟨i, hi, by rw [factor_castSucc u n i, hfi]⟩

/-! ## The non-recurrent prefix -/

/-- `u` is **`n`-recurrent from `N` on**: every length-`n` block at a position `≥ N` recurs. -/
@[category API, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
def NRecurrentFrom (u : ℕ → α) (n N : ℕ) : Prop :=
  ∀ i, N ≤ i → Recurrent u n (factor u n i)

/-- Over a **finite** alphabet a horizon exists: only finitely many length-`n` blocks fail to
recur, and each of those occurs for the last time somewhere. -/
@[category API, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem exists_nRecurrentFrom [Finite α] (u : ℕ → α) (n : ℕ) : ∃ N, NRecurrentFrom u n N := by
  classical
  have : Fintype (Fin n → α) := Fintype.ofFinite _
  have key : ∀ v : Fin n → α, ∃ N, ∀ i, N ≤ i → factor u n i = v → Recurrent u n v := by
    intro v
    by_cases hv : Recurrent u n v
    · exact ⟨0, fun _ _ _ => hv⟩
    · obtain ⟨N, hN⟩ : ∃ N, ¬ ∃ i, N ≤ i ∧ factor u n i = v := not_forall.mp hv
      exact ⟨N, fun i hi hfi => absurd ⟨i, hi, hfi⟩ hN⟩
  choose f hf using key
  refine ⟨Finset.univ.sup f, fun i hi => ?_⟩
  exact hf (factor u n i) i (le_trans (Finset.le_sup (Finset.mem_univ _)) hi) rfl

/-- **The non-recurrent prefix `s_n`** of [BKK26, Defs. 2.4–2.5]: the least position beyond which
every length-`n` block of `u` recurs.  The plan calls it the *defect horizon*. -/
@[category API, AMS 11 37 68, ref "Bug12" "BKK26", group "bugeaud_10_47"]
noncomputable def horizon [Finite α] (u : ℕ → α) (n : ℕ) : ℕ := sInf {N | NRecurrentFrom u n N}

variable [Finite α]

@[category API, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem nRecurrentFrom_horizon (u : ℕ → α) (n : ℕ) : NRecurrentFrom u n (horizon u n) :=
  Nat.sInf_mem (exists_nRecurrentFrom u n)

/-- **Every block past the horizon recurs** — the existence half of [M1M2, Prop. 2.2]. -/
@[category API, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem recurrent_of_horizon_le {u : ℕ → α} {n i : ℕ} (h : horizon u n ≤ i) :
    Recurrent u n (factor u n i) := nRecurrentFrom_horizon u n i h

@[category API, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem horizon_le_of_nRecurrentFrom {u : ℕ → α} {n N : ℕ} (h : NRecurrentFrom u n N) :
    horizon u n ≤ N := Nat.sInf_le h

/-- **The horizon is attained** — the minimality half of [M1M2, Prop. 2.2].  If `s_n = N + 1`
then the length-`n` block at position `N` is *not* recurrent: `s_n` is one past the last
occurrence of a non-recurrent block. -/
@[category API, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem not_recurrent_pred {u : ℕ → α} {n N : ℕ} (h : horizon u n = N + 1) :
    ¬ Recurrent u n (factor u n N) := by
  intro hrec
  have hN : NRecurrentFrom u n N := by
    intro i hi
    rcases eq_or_lt_of_le hi with rfl | hlt
    · exact hrec
    · exact recurrent_of_horizon_le (by omega)
  have := horizon_le_of_nRecurrentFrom hN
  omega

/-- The horizon vanishes exactly when every block of `u` recurs, i.e. when `u` is recurrent at
level `n`. -/
@[category API, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem horizon_eq_zero_iff {u : ℕ → α} {n : ℕ} :
    horizon u n = 0 ↔ ∀ i, Recurrent u n (factor u n i) := by
  constructor
  · intro h i; exact recurrent_of_horizon_le (by omega)
  · intro h; exact Nat.le_zero.mp (horizon_le_of_nRecurrentFrom fun i _ => h i)

/-- [M1M2, Prop. 2.2] in full: the horizon is either `0`, and then `u` is `n`-recurrent, or it is
`N + 1` where `N` is the last position carrying a non-recurrent length-`n` block. -/
@[category API, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem horizon_spec (u : ℕ → α) (n : ℕ) :
    (horizon u n = 0 ∧ ∀ i, Recurrent u n (factor u n i)) ∨
      ∃ N, horizon u n = N + 1 ∧ ¬ Recurrent u n (factor u n N) ∧
        ∀ i, N < i → Recurrent u n (factor u n i) := by
  rcases Nat.eq_zero_or_pos (horizon u n) with h | h
  · exact Or.inl ⟨h, horizon_eq_zero_iff.mp h⟩
  · obtain ⟨N, hN⟩ : ∃ N, horizon u n = N + 1 := ⟨horizon u n - 1, by omega⟩
    exact Or.inr ⟨N, hN, not_recurrent_pred hN, fun i hi => recurrent_of_horizon_le (by omega)⟩

/-! ## Tails -/

/-- The tail of `u` after its first `m` letters. -/
@[category API, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
def tail (u : ℕ → α) (m : ℕ) : ℕ → α := fun k => u (m + k)

omit [Finite α] in
@[simp]
lemma factor_tail (u : ℕ → α) (m n i : ℕ) : factor (tail u m) n i = factor u n (m + i) := by
  funext s
  simp only [factor, tail]
  congr 1
  omega

omit [Finite α] in
@[simp]
lemma tail_zero (u : ℕ → α) : tail u 0 = u := by funext k; simp [tail]

omit [Finite α] in
lemma tail_tail (u : ℕ → α) (m m' : ℕ) : tail (tail u m) m' = tail u (m + m') := by
  funext k
  simp only [tail]
  congr 1
  omega

omit [Finite α] in
/-- A tail of a word that is not eventually periodic is not eventually periodic. -/
@[category API, AMS 11 37 68, ref "MH38", group "bugeaud_10_47"]
theorem not_isEventuallyPeriodic_tail {u : ℕ → α} (hu : ¬ IsEventuallyPeriodic u) (m : ℕ) :
    ¬ IsEventuallyPeriodic (tail u m) := by
  rintro ⟨N, p, hp, h⟩
  refine hu ⟨m + N, p, hp, fun k hk => ?_⟩
  have h' := h (k - m) (by omega)
  simp only [tail] at h'
  rwa [show m + (k - m + p) = k + p by omega, show m + (k - m) = k by omega] at h'

/-- **The key identity** [M1M2, Lem. 2.3(i),(iii)]: past the horizon, the *ordinary* language of
the tail is the *recurrent* language of `u`.  Stated for every `m ≥ s_n`, which is what makes the
single word `tail u s_{n+1}` compute `p_∞` at the two consecutive levels `n` and `n + 1`. -/
@[category API, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem factorSet_tail_eq {u : ℕ → α} {n m : ℕ} (hm : horizon u n ≤ m) :
    factorSet (tail u m) n = recFactorSet u n := by
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    rw [factor_tail]
    exact recurrent_of_horizon_le (by omega)
  · intro hv
    obtain ⟨i, hi, hfi⟩ := hv m
    exact ⟨i - m, by rw [factor_tail, show m + (i - m) = i by omega]; exact hfi⟩

/-- `p_∞` at level `n` is the ordinary complexity of any tail past the horizon `s_n`. -/
@[category API, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem pInf_eq_pComplexity_tail {u : ℕ → α} {n m : ℕ} (hm : horizon u n ≤ m) :
    pInf u n = pComplexity (tail u m) n := by
  rw [pInf, pComplexity, factorSet_tail_eq hm]

/-! ## Monotonicity -/

/-- [M1M2, Lem. 2.3(ii)]: `s_n ≤ s_{n+1}`. -/
@[category API, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem horizon_mono_succ (u : ℕ → α) (n : ℕ) : horizon u n ≤ horizon u (n + 1) := by
  refine horizon_le_of_nRecurrentFrom fun i hi => ?_
  have h2 := (recurrent_of_horizon_le (n := n + 1) hi).castSucc
  rwa [← factor_castSucc] at h2

@[category API, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem horizon_mono (u : ℕ → α) : Monotone (horizon u) :=
  monotone_nat_of_le_succ (horizon_mono_succ u)

/-- [M1M2, Lem. 2.3(iv)]: **the Morse–Hedlund floor for `p_∞`**, i.e. the baseline
`n + 1 ≤ p_∞(n, ξ, b)` quoted in Problem 10.47. -/
@[category API, AMS 11 37 68, ref "Bug12" "MH38", group "bugeaud_10_47"]
theorem succ_le_pInf {u : ℕ → α} (hu : ¬ IsEventuallyPeriodic u) (n : ℕ) : n + 1 ≤ pInf u n := by
  rw [pInf_eq_pComplexity_tail (le_refl (horizon u n))]
  exact succ_le_pComplexity (not_isEventuallyPeriodic_tail hu _) n

/-! ## Rigidity: `p_∞` is strictly increasing -/

/-- **[M3, Lem. 3.1].**  For a word that is not eventually periodic, `p_∞` is strictly
increasing.

Proof: `s_n ≤ s_{n+1}`, so `w := tail u s_{n+1}` computes `p_∞` at *both* levels; and `w` is not
eventually periodic, so ordinary Morse–Hedlund applies to it. -/
@[category research solved, AMS 11 37 68, ref "MH38", group "bugeaud_10_47"]
theorem pInf_lt_succ {u : ℕ → α} (hu : ¬ IsEventuallyPeriodic u) (n : ℕ) :
    pInf u n < pInf u (n + 1) := by
  rw [pInf_eq_pComplexity_tail (horizon_mono_succ u n),
    pInf_eq_pComplexity_tail (le_refl (horizon u (n + 1)))]
  exact pComplexity_lt_succ_of_not_isEventuallyPeriodic (not_isEventuallyPeriodic_tail hu _) n

@[category API, AMS 11 37 68, ref "MH38", group "bugeaud_10_47"]
theorem strictMono_pInf {u : ℕ → α} (hu : ¬ IsEventuallyPeriodic u) : StrictMono (pInf u) :=
  strictMono_nat_of_lt_succ (pInf_lt_succ hu)

/-- The increment form: `p_∞` gains at least one block per level. -/
@[category API, AMS 11 37 68, ref "MH38", group "bugeaud_10_47"]
theorem add_le_pInf_add {u : ℕ → α} (hu : ¬ IsEventuallyPeriodic u) (n d : ℕ) :
    pInf u n + d ≤ pInf u (n + d) := by
  induction d with
  | zero => simp
  | succ k ih =>
    have hstep := pInf_lt_succ hu (n + k)
    rw [show n + (k + 1) = (n + k) + 1 by omega]
    omega

/-- **Rigidity downwards.**  Minimal eventual complexity at one scale forces it at every smaller
scale. -/
@[category research solved, AMS 11 37 68, ref "Bug12", group "bugeaud_10_47"]
theorem pInf_eq_succ_of_le {u : ℕ → α} (hu : ¬ IsEventuallyPeriodic u) {n₀ : ℕ}
    (h : pInf u n₀ = n₀ + 1) {n : ℕ} (hn : n ≤ n₀) : pInf u n = n + 1 := by
  have hfloor := succ_le_pInf hu n
  have hgap := add_le_pInf_add hu n (n₀ - n)
  rw [show n + (n₀ - n) = n₀ by omega] at hgap
  omega

/-- **Rigidity upwards.**  If `p_∞(n) = n + 1` for infinitely many `n`, it holds for *every* `n`.

This is what licenses the standing hypothesis (H) of `BB47/M3.tex` — and of Theorem W — being
*stated* with "infinitely many `n`" and *used* with "all `n`". -/
@[category research solved, AMS 11 37 68, ref "Bug12", group "bugeaud_10_47"]
theorem pInf_eq_succ_of_frequently {u : ℕ → α} (hu : ¬ IsEventuallyPeriodic u)
    (h : ∀ N, ∃ n, N ≤ n ∧ pInf u n = n + 1) (n : ℕ) : pInf u n = n + 1 := by
  obtain ⟨n₀, hn₀, hval⟩ := h n
  exact pInf_eq_succ_of_le hu hval hn₀

/-! ## `p_∞` is a tail invariant — the ceiling of [M4, Rem. 2.5] -/

omit [Finite α] in
/-- **Recurrence is a tail property.**  Discarding a prefix changes neither the set of recurrent
blocks nor their number. -/
@[category research solved, AMS 11 37 68, ref "Bug12", group "bugeaud_10_47"]
theorem recFactorSet_tail (u : ℕ → α) (m n : ℕ) : recFactorSet (tail u m) n = recFactorSet u n := by
  ext v
  constructor
  · intro hv N
    obtain ⟨i, hi, hfi⟩ := hv N
    rw [factor_tail] at hfi
    exact ⟨m + i, by omega, hfi⟩
  · intro hv N
    obtain ⟨i, hi, hfi⟩ := hv (m + N)
    exact ⟨i - m, by omega, by rw [factor_tail, show m + (i - m) = i by omega]; exact hfi⟩

/-- `p_∞` is unchanged by discarding a prefix.  **No finite prefix of `u` carries any information
about `p_∞(n, u)`** — the precise content of the ceiling remark [M4, Rem. 2.5]. -/
@[category research solved, AMS 11 37 68, ref "Bug12", group "bugeaud_10_47"]
theorem pInf_tail (u : ℕ → α) (m n : ℕ) : pInf (tail u m) n = pInf u n := by
  rw [pInf, pInf, recFactorSet_tail]

/-- The horizon can only shrink when a prefix is discarded. -/
@[category API, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem horizon_tail_le (u : ℕ → α) (m n : ℕ) : horizon (tail u m) n ≤ horizon u n := by
  refine horizon_le_of_nRecurrentFrom fun i hi => ?_
  have h : Recurrent u n (factor u n (m + i)) := recurrent_of_horizon_le (by omega)
  rw [factor_tail]
  exact (Set.ext_iff.mp (recFactorSet_tail u m n) (factor u n (m + i))).mpr h

/-- …and by no more than the length of the discarded prefix. -/
@[category API, AMS 11 37 68, ref "BKK26", group "bugeaud_10_47"]
theorem horizon_le_tail (u : ℕ → α) (m n : ℕ) : horizon u n ≤ m + horizon (tail u m) n := by
  refine horizon_le_of_nRecurrentFrom fun i hi => ?_
  have hrec : Recurrent (tail u m) n (factor (tail u m) n (i - m)) :=
    recurrent_of_horizon_le (by omega)
  rw [factor_tail, show m + (i - m) = i by omega] at hrec
  have : recFactorSet (tail u m) n = recFactorSet u n := recFactorSet_tail u m n
  exact (Set.ext_iff.mp this (factor u n i)).mp hrec

end BB47
