/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB6.Runs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Theorem A — reading Problem 10.6 as a growth or a sparsity condition is vacuous

Problem 10.6 [Bug12, Ch. 10] asks for a "very rapidly increasing" sequence of positive integers
that is universally densifying.  This file shows that *every* reading of "very rapidly increasing"
which constrains only the **size** of the terms or the **sparsity** of the set they form is
answered trivially, and simultaneously.

The construction is one sequence, `BB6.runSeq f`, parameterized by an arbitrary growth demand
`f : ℕ → ℕ`.  Position `n` sits in the dyadic block `k = blk n = ⌊log₂(n+1)⌋`, of length `2 ^ k`,
and the sequence runs through consecutive integers inside each block:

  `runSeq f n = runStart f (blk n) + off n`,   `off n = n + 1 - 2 ^ blk n`.

The block starts are pushed up by a three-way `max` in their recursion: far enough to keep the
sequence strictly increasing across a block boundary, past `f` on the whole block (which gives the
growth statement, for an arbitrary and not necessarily monotone `f`), and past the tower
`twr k = 2 ^ 2 ^ 4 ^ k` (which gives the sparsity statement).  Since the blocks are runs of
consecutive integers of unbounded length, `BB6.universallyDensifying_of_hasLongRuns` applies.

The calibration this is for: a run has `mₙ₊₁ - mₙ = 1`, the exact opposite of "rapidly
increasing", yet no bound on size and no bound on sparsity can exclude it.  Only a lower bound on
the *ratios* `mₙ₊₁ / mₙ` can, which is why R3 is the sole non-vacuous reading (`BB6/Readings.lean`).

## Priority

The subexponential half of `theorem_A_growth` is a special case of [Bos83, Thm 1.5], proved in
1983 and in the stronger uniform-distribution form, and [AHK83] reaches every prescribed
subexponential rate.  What is outside those hypotheses is the *unrestricted* `f` here, and the
sparsity of `theorem_A_sparsity`, which is below the `log N` floor that every sublacunary sequence
obeys.  The moral — that sparsity is not the obstruction, arithmetic structure is — is
[Kat01, §2.3].

*References:*
  - [Bug12] Bugeaud, Y. *Distribution modulo one and Diophantine approximation*, CUP 2012, Ch. 10.
  - [Bos83] Boshernitzan, M. "Homogeneously distributed sequences and Poincaré sequences of
    integers of sublacunary growth." Monatsh. Math. 96 (1983), 173–181.
  - [Kat16] Katz, A. "Generalizations of Furstenberg's Diophantine result." arXiv:1607.00670.
-/

namespace BB6

open Filter Set

/-! ## The construction -/

/-- The dyadic block containing position `n`: block `k` is `{n : 2 ^ k ≤ n + 1 < 2 ^ (k+1)}`, of
length `2 ^ k`. -/
@[category API, AMS 11, group "bugeaud_10_6"]
def blk (n : ℕ) : ℕ := Nat.log 2 (n + 1)

/-- The offset of `n` inside its block, so `0 ≤ off n < 2 ^ blk n`. -/
@[category API, AMS 11, group "bugeaud_10_6"]
def off (n : ℕ) : ℕ := n + 1 - 2 ^ blk n

/-- The largest value `f` takes on block `k` or below. Taking a supremum rather than `f k` itself
is what lets the growth statement hold for an **arbitrary** `f`, monotone or not. -/
@[category API, AMS 11, group "bugeaud_10_6"]
def fSup (f : ℕ → ℕ) (k : ℕ) : ℕ := (Finset.range (2 ^ (k + 1))).sup f

/-- The tower forced into the block starts to make the sparsity bound work. -/
@[category API, AMS 11, group "bugeaud_10_6"]
def twr (k : ℕ) : ℕ := 2 ^ (2 ^ (4 ^ k))

/-- The value at which block `k` starts. The three-way `max` encodes the three demands: room for
the previous block (`+ 2 ^ k`, which keeps the sequence strictly increasing), the growth demand
`f`, and the sparsity tower.

Named after `runSeq` rather than after the blocks because `BB6.blockStart` is taken: the historical
sequence of `BB6/AristotleSeq.lean` has block starts of its own, with a different signature. -/
@[category API, AMS 11, group "bugeaud_10_6"]
def runStart (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => max (fSup f 0) (twr 0) + 1
  | k + 1 => max (runStart f k + 2 ^ k) (max (fSup f (k + 1)) (twr (k + 1))) + 1

/-- **The sequence.** Inside block `k` it runs through `2 ^ k` consecutive integers starting at
`runStart f k`. -/
@[category API, AMS 11, group "bugeaud_10_6"]
def runSeq (f : ℕ → ℕ) (n : ℕ) : ℕ := runStart f (blk n) + off n

/-! ## Block algebra -/

@[category API, AMS 11, group "bugeaud_10_6"]
theorem pow_blk_le (n : ℕ) : 2 ^ blk n ≤ n + 1 :=
  Nat.pow_log_le_self 2 (Nat.succ_ne_zero n)

@[category API, AMS 11, group "bugeaud_10_6"]
theorem lt_pow_blk_succ (n : ℕ) : n + 1 < 2 ^ (blk n + 1) :=
  Nat.lt_pow_succ_log_self (by norm_num) _

@[category API, AMS 11, group "bugeaud_10_6"]
theorem off_lt (n : ℕ) : off n < 2 ^ blk n := by
  have h1 := pow_blk_le n
  have h2 := lt_pow_blk_succ n
  have h3 : 2 ^ (blk n + 1) = 2 * 2 ^ blk n := by rw [pow_succ]; ring
  show n + 1 - 2 ^ blk n < 2 ^ blk n
  omega

@[category API, AMS 11, group "bugeaud_10_6"]
theorem blk_mono : Monotone blk := fun _ _ h => Nat.log_mono_right (by omega)

@[category API, AMS 11, group "bugeaud_10_6"]
theorem blk_run (k j : ℕ) (hj : j < 2 ^ k) : blk (2 ^ k - 1 + j) = k := by
  have h1 : 0 < 2 ^ k := Nat.two_pow_pos k
  have h2 : 2 ^ k - 1 + j + 1 = 2 ^ k + j := by omega
  show Nat.log 2 (2 ^ k - 1 + j + 1) = k
  rw [h2]
  refine Nat.log_eq_of_pow_le_of_lt_pow (by omega) ?_
  have h3 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  omega

@[category API, AMS 11, group "bugeaud_10_6"]
theorem off_run (k j : ℕ) (hj : j < 2 ^ k) : off (2 ^ k - 1 + j) = j := by
  have h1 : 0 < 2 ^ k := Nat.two_pow_pos k
  show 2 ^ k - 1 + j + 1 - 2 ^ blk (2 ^ k - 1 + j) = j
  rw [blk_run k j hj]
  omega

/-! ## The block starts -/

@[category API, AMS 11, group "bugeaud_10_6"]
theorem runStart_lt_succ (f : ℕ → ℕ) (k : ℕ) :
    runStart f k + 2 ^ k < runStart f (k + 1) := by
  show runStart f k + 2 ^ k <
    max (runStart f k + 2 ^ k) (max (fSup f (k + 1)) (twr (k + 1))) + 1
  omega

@[category API, AMS 11, group "bugeaud_10_6"]
theorem runStart_strictMono (f : ℕ → ℕ) : StrictMono (runStart f) :=
  strictMono_nat_of_lt_succ fun k => by
    have := runStart_lt_succ f k
    have := Nat.two_pow_pos k
    omega

@[category API, AMS 11, group "bugeaud_10_6"]
theorem fSup_le_runStart (f : ℕ → ℕ) (k : ℕ) : fSup f k ≤ runStart f k := by
  cases k with
  | zero => show fSup f 0 ≤ max (fSup f 0) (twr 0) + 1; omega
  | succ k =>
    show fSup f (k + 1) ≤
      max (runStart f k + 2 ^ k) (max (fSup f (k + 1)) (twr (k + 1))) + 1
    omega

@[category API, AMS 11, group "bugeaud_10_6"]
theorem twr_le_runStart (f : ℕ → ℕ) (k : ℕ) : twr k ≤ runStart f k := by
  cases k with
  | zero => show twr 0 ≤ max (fSup f 0) (twr 0) + 1; omega
  | succ k =>
    show twr (k + 1) ≤
      max (runStart f k + 2 ^ k) (max (fSup f (k + 1)) (twr (k + 1))) + 1
    omega

/-! ## The three properties of `runSeq` -/

@[category API, AMS 11, group "bugeaud_10_6"]
theorem runSeq_run (f : ℕ → ℕ) (k j : ℕ) (hj : j < 2 ^ k) :
    runSeq f (2 ^ k - 1 + j) = runStart f k + j := by
  show runStart f (blk (2 ^ k - 1 + j)) + off (2 ^ k - 1 + j) = runStart f k + j
  rw [blk_run k j hj, off_run k j hj]

/-- The sequence is strictly increasing: inside a block it steps by one, and across a boundary the
gap `runStart f (k+1) - (runStart f k + 2 ^ k) > 0` is what the recursion was built for. -/
@[category research solved, AMS 11, group "bugeaud_10_6"]
theorem runSeq_strictMono (f : ℕ → ℕ) : StrictMono (runSeq f) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  have hle : blk n ≤ blk (n + 1) := blk_mono (Nat.le_succ n)
  rcases eq_or_lt_of_le hle with heq | hlt
  · -- same block: the offset increases by one
    have h1 := pow_blk_le n
    show runStart f (blk n) + off n < runStart f (blk (n + 1)) + off (n + 1)
    rw [← heq]
    show runStart f (blk n) + (n + 1 - 2 ^ blk n) <
      runStart f (blk n) + (n + 1 + 1 - 2 ^ blk (n + 1))
    rw [← heq]
    omega
  · -- new block: the jump clears the whole previous block
    have h1 := off_lt n
    have h2 := runStart_lt_succ f (blk n)
    have h3 : runStart f (blk n + 1) ≤ runStart f (blk (n + 1)) :=
      (runStart_strictMono f).monotone hlt
    show runStart f (blk n) + off n < runStart f (blk (n + 1)) + off (n + 1)
    omega

/-- **The runs.** Block `k` is a run of `2 ^ k` consecutive integers, so runs of every length
occur. -/
@[category research solved, AMS 11, group "bugeaud_10_6"]
theorem runSeq_hasLongRuns (f : ℕ → ℕ) : HasLongRuns (runSeq f) := by
  intro L
  refine ⟨2 ^ (L + 1) - 1, fun j hj => ?_⟩
  have hL : L < 2 ^ (L + 1) := lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ L))
  have hj' : j < 2 ^ (L + 1) := lt_of_le_of_lt hj hL
  have h0 : (0 : ℕ) < 2 ^ (L + 1) := Nat.two_pow_pos _
  rw [runSeq_run f (L + 1) j hj']
  have : runSeq f (2 ^ (L + 1) - 1) = runStart f (L + 1) := by
    have := runSeq_run f (L + 1) 0 h0
    simpa using this
  omega

/-- **The growth.** The sequence dominates an arbitrary prescribed `f` at *every* index — no
monotonicity of `f`, and no restriction on how fast it grows. -/
@[category research solved, AMS 11, group "bugeaud_10_6"]
theorem le_runSeq (f : ℕ → ℕ) (n : ℕ) : f n ≤ runSeq f n := by
  have h1 : f n ≤ fSup f (blk n) := by
    refine Finset.le_sup (Finset.mem_range.2 ?_)
    have := lt_pow_blk_succ n
    omega
  have h2 := fSup_le_runStart f (blk n)
  show f n ≤ runStart f (blk n) + off n
  omega

/-! ## Theorem A -/

/-- **Theorem A, universal density.** The construction is universally densifying, whatever `f` is:
this is Lemma R applied to `runSeq_hasLongRuns`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_6",
  formal_uses universallyDensifying_of_hasLongRuns runSeq_hasLongRuns]
theorem runSeq_universallyDensifying (f : ℕ → ℕ) : UniversallyDensifying (runSeq f) :=
  universallyDensifying_of_hasLongRuns (runSeq_hasLongRuns f)

/-- **Theorem A(i).** For every growth demand `f` there is a strictly increasing universally
densifying sequence dominating `f` everywhere. Reading "very rapidly increasing" as *any* lower
bound on the size of the terms therefore makes Problem 10.6 vacuous. -/
@[category research solved, AMS 11, ref "Bug12" "Bos83", group "bugeaud_10_6",
  formal_uses runSeq_strictMono runSeq_universallyDensifying le_runSeq]
theorem theorem_A_growth (f : ℕ → ℕ) :
    ∃ m : ℕ → ℕ, StrictMono m ∧ UniversallyDensifying m ∧ ∀ n, f n ≤ m n :=
  ⟨runSeq f, runSeq_strictMono f, runSeq_universallyDensifying f, le_runSeq f⟩

/-! ### The sparsity half -/

@[category API, AMS 11, group "bugeaud_10_6"]
theorem runSeq_at_runStart (f : ℕ → ℕ) (k : ℕ) :
    runSeq f (2 ^ k - 1) = runStart f k := by
  simpa using runSeq_run f k 0 (Nat.two_pow_pos k)

/-- Below the start of block `k` the sequence has produced at most `2 ^ k - 1` terms. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem countingFn_le_of_lt_runStart (f : ℕ → ℕ) {N k : ℕ} (h : N < runStart f k) :
    countingFn (runSeq f) N ≤ 2 ^ k - 1 :=
  countingFn_le (runSeq_strictMono f) (by rw [runSeq_at_runStart]; exact h)

/-- **Theorem A(ii).** The same construction can be made so sparse that its counting function is
below `(log log N)²` — an *exponential* below the `log N` floor that every sublacunary sequence
obeys, and below the `r(N) log N` of [Kat16, Cor. 4.10]. Reading "very rapidly increasing" as a
sparsity condition is therefore vacuous too. -/
@[category research solved, AMS 11, ref "Bug12" "Kat16", group "bugeaud_10_6",
  formal_uses countingFn_le_of_lt_runStart twr_le_runStart]
theorem theorem_A_sparsity (f : ℕ → ℕ) :
    ∀ᶠ N : ℕ in atTop,
      (countingFn (runSeq f) N : ℝ) ≤ (Real.log (Real.log N)) ^ 2 := by
  have hlog2 : (0.69 : ℝ) ≤ Real.log 2 := le_of_lt (lt_trans (by norm_num) Real.log_two_gt_d9)
  refine Filter.eventually_atTop.2 ⟨runStart f 2, fun N hN => ?_⟩
  -- the least block start exceeding `N`
  have hex : ∃ k, N < runStart f k :=
    ⟨N + 1, lt_of_lt_of_le (Nat.lt_succ_self N) (runStart_strictMono f).le_apply⟩
  have hk : N < runStart f (Nat.find hex) := Nat.find_spec hex
  have hk3 : 3 ≤ Nat.find hex := by
    by_contra hcon
    have h2 : Nat.find hex ≤ 2 := by omega
    exact absurd (lt_of_lt_of_le hk ((runStart_strictMono f).monotone h2)) (by omega)
  -- write it as `j + 1` with `j ≥ 2`
  obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hj2 : 2 ≤ j := by omega
  have hjN : runStart f j ≤ N := Nat.not_lt.1 (Nat.find_min hex (by omega))
  -- the count
  have hcount : countingFn (runSeq f) N ≤ 2 ^ (j + 1) := by
    have := countingFn_le_of_lt_runStart f (hj ▸ hk)
    have h2 := Nat.two_pow_pos (j + 1)
    omega
  -- the size of `N`
  have hNbig : (2 : ℕ) ^ (2 ^ (4 ^ j)) ≤ N := le_trans (twr_le_runStart f j) hjN
  have hNbig' : ((2 : ℝ)) ^ (2 ^ (4 ^ j)) ≤ (N : ℝ) := by exact_mod_cast hNbig
  -- two peels of the logarithm
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (2 ^ (4 ^ j)) := by positivity
  have hlogN : ((2 : ℝ) ^ (4 ^ j)) * Real.log 2 ≤ Real.log N := by
    have := Real.log_le_log hpos hNbig'
    rwa [Real.log_pow, show (((2 : ℕ) ^ (4 ^ j) : ℕ) : ℝ) = (2 : ℝ) ^ (4 ^ j) by push_cast; ring]
      at this
  have hhalf : (2 : ℝ) ^ (4 ^ j) / 2 ≤ Real.log N := by
    have h1 : (0 : ℝ) < (2 : ℝ) ^ (4 ^ j) := by positivity
    nlinarith
  have hloglog : (((4 : ℝ) ^ j) - 1) * Real.log 2 ≤ Real.log (Real.log N) := by
    have h1 : (0 : ℝ) < (2 : ℝ) ^ (4 ^ j) / 2 := by positivity
    have h2 := Real.log_le_log h1 hhalf
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow,
      show (((4 : ℕ) ^ j : ℕ) : ℝ) = (4 : ℝ) ^ j by push_cast; ring] at h2
    linarith
  -- the elementary estimate `(4^j - 1) log 2 ≥ 2^j` for `j ≥ 2`
  have ht : (4 : ℝ) ≤ (2 : ℝ) ^ j := by
    calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
    _ ≤ (2 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) hj2
  have hsq : ((2 : ℝ) ^ j) ^ 2 = (4 : ℝ) ^ j := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hkey : (2 : ℝ) ^ j ≤ (((4 : ℝ) ^ j) - 1) * Real.log 2 := by
    rw [← hsq]
    have hne : (0 : ℝ) ≤ ((2 : ℝ) ^ j) ^ 2 - 1 := by nlinarith
    calc (2 : ℝ) ^ j ≤ (((2 : ℝ) ^ j) ^ 2 - 1) * 0.69 := by nlinarith [sq_nonneg ((2 : ℝ) ^ j - 4)]
    _ ≤ (((2 : ℝ) ^ j) ^ 2 - 1) * Real.log 2 := mul_le_mul_of_nonneg_left hlog2 hne
  -- and `2^(j+1) ≤ 4^j`
  have hpow : (2 : ℝ) ^ (j + 1) ≤ (4 : ℝ) ^ j := by
    rw [← hsq, pow_succ, mul_comm ((2:ℝ)^j) 2, sq]
    nlinarith
  -- assemble
  calc (countingFn (runSeq f) N : ℝ) ≤ ((2 ^ (j + 1) : ℕ) : ℝ) := by exact_mod_cast hcount
  _ = (2 : ℝ) ^ (j + 1) := by push_cast; ring
  _ ≤ (4 : ℝ) ^ j := hpow
  _ = ((2 : ℝ) ^ j) ^ 2 := hsq.symm
  _ ≤ (Real.log (Real.log N)) ^ 2 := by
      have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ j := by positivity
      exact pow_le_pow_left₀ h0 (le_trans hkey hloglog) 2

/-- **Theorem A(iii).** Both at once: for every growth demand `f` there is a strictly increasing
universally densifying sequence which dominates `f` everywhere *and* has counting function below
`(log log N)²`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_6",
  formal_uses theorem_A_growth theorem_A_sparsity]
theorem theorem_A (f : ℕ → ℕ) :
    ∃ m : ℕ → ℕ, StrictMono m ∧ UniversallyDensifying m ∧ (∀ n, f n ≤ m n) ∧
      ∀ᶠ N : ℕ in atTop, (countingFn m N : ℝ) ≤ (Real.log (Real.log N)) ^ 2 :=
  ⟨runSeq f, runSeq_strictMono f, runSeq_universallyDensifying f, le_runSeq f,
    theorem_A_sparsity f⟩

/-! ## Corollary A′ — the recorded variant is elementary -/

/-- **Corollary A′.** `DistributionModOne.Problem10_6.problem_10_6_variant_2` — a strictly
increasing sequence of intermediate growth that is universally densifying — is **elementary**: it
needs neither [Kat16] nor [Fur67] nor [Bos94], only runs.

Historically the credit for this statement belongs to [Bos83, Thm 1.5] (1983), in the stronger
uniform-distribution form; Katz's contribution to Problem 10.6 is the sparsity side, which is what
`theorem_A_sparsity` calibrates. -/
@[category research solved, AMS 11, ref "Bug12" "Bos83", group "bugeaud_10_6",
  formal_uses theorem_A_growth]
theorem variant_2_of_runs :
    ∃ m : ℕ → ℕ, StrictMono m ∧
      (∃ α : ℝ, 0 < α ∧ α < 1 ∧ Bugeaud06.HasIntermediateGrowth α m) ∧
      ∀ ξ : ℝ, Irrational ξ →
        Dense (Set.range fun n => (↑(ξ * m n) : AddCircle (1 : ℝ))) := by
  classical
  refine ⟨runSeq (fun n => ⌈Real.exp n⌉₊), runSeq_strictMono _, ⟨1 / 2, by norm_num, by norm_num,
    ?_⟩, runSeq_universallyDensifying _⟩
  refine Filter.eventually_atTop.2 ⟨1, fun n hn => ?_⟩
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h2 : ((n : ℝ)) ^ (1 / 2 : ℝ) ≤ (n : ℝ) := by
    calc ((n : ℝ)) ^ (1 / 2 : ℝ) ≤ ((n : ℝ)) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
    _ = (n : ℝ) := Real.rpow_one _
  calc Real.exp (((n : ℝ)) ^ (1 / 2 : ℝ)) ≤ Real.exp n := Real.exp_le_exp.2 h2
  _ ≤ ((⌈Real.exp n⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  _ ≤ ((runSeq (fun n => ⌈Real.exp n⌉₊) n : ℕ) : ℝ) := by
      exact_mod_cast le_runSeq (fun n => ⌈Real.exp n⌉₊) n

end BB6
