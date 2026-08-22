/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Data.Int.Interval
import TH.TwoAdic
import BertinPisot.ModOneEquivalence
import ForMathlib.Analysis.Equidistribution.ModOne
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The annealed package, and the derandomization gap (plan-A1+, A16)

If the parity bits of the orbit of `(3/2)ⁿ ξ` were *fair coins*, uniform distribution would be
a triviality.  This file makes that sentence into theorems — and, in the same breath, into a
precise statement of what is missing.

The orbit `εₙ = {(3/2)ⁿ ξ}` obeys an exact recursion,

  `ε_{n+1} = {(3 εₙ + βₙ) / 2}`,   `βₙ = ⌊(3/2)ⁿ ξ⌋ mod 2`

(`run_parityWord`): a *deterministic* trajectory of a two-branch random map, driven by one
specific binary word.  Replace that word by a fair coin sequence and you get the **annealed
model**.  Three finite, exact, provable-now theorems follow.

* **(i) Exact coset uniformity.**  `3` has order `2^(k-2)` mod `2^k` (`TH.orderOf_three_zmod`,
  already in `TH/TwoAdic.lean`), that cyclic group has index exactly `2` in `(ℤ/2^k)ˣ`
  (`orderOf_three_mul_two`), the powers `3ⁿ` sweep it **exactly once per period**
  (`three_pow_injOn`, `sum_period`), and every nontrivial character of it therefore sums to
  exactly zero over one period (`sum_character_period`).  *Which* index-2 subgroup it is, is
  located mod 8: `⟨3⟩` reduces into `{1, 3}` (`castHom_three_pow`), hence misses `−1`
  (`neg_one_ne_three_pow`), so the units split as `⟨3⟩ ⊔ (−1)·⟨3⟩` — an immediate consequence of
  those two theorems, not separately formalized here.  Nothing in this section is an estimate.
* **(ii) The annealed chain.**  For *any* starting point and *every* `N`, the `2ᴺ` fair-coin
  words send the state to `2ᴺ` distinct points, exactly one in each level-`N` dyadic cell
  (`card_words_eq_one`, `card_words_level`).  The annealed law is not merely
  asymptotically uniform with a spectral gap — it is **exactly uniform, in finitely many
  steps**.  The mechanism is one line: flipping the last bit translates the state by exactly
  `1/2`, so every odd Fourier mode is annihilated in a single step (`ee_step_flip`), and the
  Weyl sums along a random word are an *exactly* orthogonal system
  (`sum_ee_run_mul_conj`), whence the second moment is exactly `N·2ᴺ`
  (`sum_normSq_weylSum`) and the bad set is small by counting alone (`card_Bad_le`).
* **(iii) The gap statement.**  `isEquidistributedModuloOne_iff_notMem_bad`: uniform
  distribution of `((3/2)ⁿ ξ)` holds **iff**, for every `h ≠ 0`, the parity word of `h·ξ`
  eventually avoids the explicitly defined set `Bad`, whose density among all words is at
  most `1/(δ²N)`.  That is the sharpest compiled form of "the problem is derandomization":
  the quantifier that is open is not about the model, it is about *one word*.

## Two no-gos, kept in the file on purpose

This angle is **calibration and interface, not a route**, and two formal facts in the corpus say
why.

* `Z32.exists_balanceVec_zero` (`Z32/BalanceVectors.lean`) proves that finite-level balance data
  cannot reach the M6 rung: the level-`k` statistics that (i) and (ii) make perfectly uniform are
  exactly the data that provably does *not* decide the open question.
* GR4 (the transfer-principle test of `plans/report2-weyl.html` §4.3): over `𝔽₂[t]` with
  `α = (1+t)/t` the annealed law is *also* perfectly uniform, while the conclusion is **false**
  (row `n` of Pascal's triangle mod 2 has only `2^{s₂(n)}` ones).  Any argument that consumes
  only annealed facts proves too much.  Everything below is annealed; therefore nothing below
  can close the gap, and saying so is part of the deliverable.

## A correction to the plan's picture

`plans/plan-A1+.html` §5 A16(ii) predicted "explicit character eigenvalues (products of cosines;
the Diaconis–Fulman carry spectrum in this special case), spectral gap, and exponential
concentration".  What is true is **stronger and different in kind**: because the two branches of
the annealed map differ by exactly `1/2`, the transfer operator does not merely contract a mode,
it **annihilates** it (`ee_step_flip`).  There is no gap to estimate and no cosine product: the
level-`N` law is exactly uniform after `N` steps, and the Diaconis–Fulman carry spectrum
describes a neighbouring object (carries in base-`b` addition), not this chain.  The residual
overstatement is in the *concentration*: what is proved here is Chebyshev-grade
(`card_Bad_le`, density `≤ 1/(δ²N)`), not exponential.  The martingale-difference input that
Azuma–Hoeffding would need is exactly `sum_ee_run_mul_conj`'s one-step lemma and is proved;
the upgrade is deliberately not formalized, because it needs conditional expectation and
filtrations — measure theory, which the "no measure theory beyond counting" design of this
angle was meant to avoid.  Re-grade A16(ii)'s "exponential" to "Chebyshev, exponential
available at the cost of a martingale layer".

## Main results

* `run_parityWord` — the deterministic orbit *is* a trajectory of the annealed chain.
* `orderOf_three_mul_two`, `sum_period`, `sum_character_period`, `castHom_three_pow`,
  `neg_one_ne_three_pow` — (i).
* `card_words_eq_one`, `card_words_level` — (ii), exact uniformity at every level `≤ N`.
* `ee_step_flip`, `sum_ee_run_mul_conj`, `sum_normSq_weylSum` — (ii), the exact spectrum.
* `card_Bad_le` — the bad set has density `≤ 1/(δ²N)`.
* `isEquidistributedModuloOne_iff_notMem_bad` — (iii), the derandomization gap.

## Trust ledger

`std3` (`propext`, `Classical.choice`, `Quot.sound`): no cited axiom, no `sorry`, no
`native_decide`.  The only corpus inputs are `TH.orderOf_three_zmod` (axiom-free) and
Weyl's criterion `Bertin.uniformlyDistributedModOne_iff_weylCriterion` together with
`Bertin.uniformlyDistributedModOne_iff_isEquidistributedModuloOne`, both axiom-free since
hygiene items H1/H2 of `plans/plan-A1+.html` §6.3 landed.

## Claim level

Formalization and calibration only.  Every statement here is elementary and was known to be
elementary; the contribution is that the annealed baseline and the shape of the missing
statement are now compiled objects rather than paragraphs, so that a later "the bits are random
enough" claim has a target it must actually hit.  Graded **off-ladder**: nothing here is a rung.

## References

* `plans/plan-A1+.html` §5, angle A16 (the annealed package and the derandomization gap);
  Table F′ (grade: meta, with new formal side-rungs); W8.
* `plans/report2-weyl.html` §5 (the annealed baseline), §4.3 (GR4 and the `𝔽₂[t]` mirror).
* [DF09] P. Diaconis and J. Fulman, "Carries, shuffling, and an amazing matrix,"
  *Amer. Math. Monthly* **116** (2009), 788–803.  (The plan's spectral reference; see the
  correction above for why the chain here is not that chain.)
* [Ber92] Bertin, M.-J. et al. *Pisot and Salem Numbers.* Birkhäuser, 1992, Theorem 4.3.2
  (Weyl's criterion).
-/

namespace TH.Annealed

open Finset

/-! ## (i) Exact coset uniformity of `3ⁿ` modulo `2^k`

The bottom `k` bits of `3ⁿ` are purely periodic with period `2^(k-2)`, and over one period they
sweep an index-2 subgroup of `(ℤ/2^k)ˣ` **bijectively**.  So every fixed-width bit-window
statistic of `3ⁿ` is *perfectly* uniform over a full period, and the entire content of the
`(3/2)ⁿ` problem is that the range `n ≤ N` truncates that period at `N ≍ k ≪ 2^(k-2)`. -/

section Coset

variable {k : ℕ}

/-- A full period of `3` in `ZMod (2^k)` is trivial (`k ≥ 3`). -/
@[category API, AMS 11, ref "A1plus", group "th_annealed"]
theorem three_pow_period_eq_one (hk : 3 ≤ k) : (3 : ZMod (2 ^ k)) ^ (2 ^ (k - 2)) = 1 := by
  rw [← orderOf_three_zmod hk]
  exact pow_orderOf_eq_one _

/-- Exact periodicity of the bottom `k` bits of `3ⁿ`. -/
@[category research solved, AMS 11, ref "A1plus", group "th_annealed"]
theorem three_pow_add_period (hk : 3 ≤ k) (n : ℕ) :
    (3 : ZMod (2 ^ k)) ^ (n + 2 ^ (k - 2)) = 3 ^ n := by
  rw [pow_add, three_pow_period_eq_one hk, mul_one]

/-- **Every element of the orbit is hit exactly once per period.** -/
@[category research solved, AMS 11, ref "A1plus", group "th_annealed"]
theorem three_pow_injOn (hk : 3 ≤ k) :
    Set.InjOn (fun n : ℕ => (3 : ZMod (2 ^ k)) ^ n) (Set.Iio (2 ^ (k - 2))) := by
  rw [← orderOf_three_zmod hk]
  exact pow_injOn_Iio_orderOf

/-- The orbit of `3` over one period has exactly `2^(k-2)` elements. -/
@[category API, AMS 11, ref "A1plus", group "th_annealed"]
theorem card_image_three_pow (hk : 3 ≤ k) :
    ((Finset.range (2 ^ (k - 2))).image fun n => (3 : ZMod (2 ^ k)) ^ n).card = 2 ^ (k - 2) := by
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  exact three_pow_injOn hk (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) hab

/-- The number of units mod `2^k` is `2^(k-1)`. -/
@[category API, AMS 11, ref "A1plus", group "th_annealed"]
theorem card_units_two_pow (hk : 1 ≤ k) :
    Fintype.card (ZMod (2 ^ k))ˣ = 2 ^ (k - 1) := by
  have : NeZero ((2 : ℕ) ^ k) := ⟨by positivity⟩
  rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow Nat.prime_two (by omega)]
  norm_num

/-- **Index 2.**  The cyclic group generated by `3` has index exactly `2` in `(ℤ/2^k)ˣ`
(`k ≥ 3`) — the exact statement behind "the annealed law is uniform on a half of the units". -/
@[category research solved, AMS 11, ref "A1plus", group "th_annealed"]
theorem orderOf_three_mul_two (hk : 3 ≤ k) :
    orderOf (3 : ZMod (2 ^ k)) * 2 = Fintype.card (ZMod (2 ^ k))ˣ := by
  rw [orderOf_three_zmod hk, card_units_two_pow (by omega), show k - 1 = (k - 2) + 1 by omega,
    pow_succ]

/-- **Perfect sweep.**  Summing any statistic along one full period of `3ⁿ` is the same as
summing it once over each element of the coset: the empirical distribution over a period is
*exactly* the uniform distribution on `⟨3⟩`. -/
@[category research solved, AMS 11, ref "A1plus", group "th_annealed"]
theorem sum_period {M : Type*} [AddCommMonoid M] (hk : 3 ≤ k) (f : ZMod (2 ^ k) → M) :
    ∑ y ∈ (Finset.range (2 ^ (k - 2))).image (fun n => (3 : ZMod (2 ^ k)) ^ n), f y
      = ∑ n ∈ Finset.range (2 ^ (k - 2)), f ((3 : ZMod (2 ^ k)) ^ n) := by
  refine Finset.sum_image ?_
  intro a ha b hb hab
  exact three_pow_injOn hk (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) hab

/-- Geometric-series form of the orthogonality relation on a cyclic group. -/
private lemma sum_pow_period_eq_zero {z : ℂ} (K : ℕ) (hz1 : z ≠ 1) (hzp : z ^ K = 1) :
    ∑ n ∈ Finset.range K, z ^ n = 0 := by
  rw [geom_sum_eq hz1, hzp, sub_self, zero_div]

/-- **Nontrivial character sums over the coset vanish exactly** — not approximately, and with no
cancellation estimate: the geometric series closes. -/
@[category research solved, AMS 11, ref "A1plus", group "th_annealed"]
theorem sum_character_period (hk : 3 ≤ k) (χ : ZMod (2 ^ k) →* ℂ) (hχ : χ 3 ≠ 1) :
    ∑ n ∈ Finset.range (2 ^ (k - 2)), χ ((3 : ZMod (2 ^ k)) ^ n) = 0 := by
  simp only [map_pow]
  refine sum_pow_period_eq_zero _ hχ ?_
  rw [← map_pow, three_pow_period_eq_one hk, map_one]

private lemma eight_dvd_two_pow (hk : 3 ≤ k) : (8 : ℕ) ∣ 2 ^ k := by
  refine ⟨2 ^ (k - 3), ?_⟩
  rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]
  congr 1
  omega

/-- **Which coset.**  `⟨3⟩` lies in `{x ≡ 1, 3 (mod 8)}`, the index-2 subgroup of `(ℤ/2^k)ˣ`
determined mod 8; with `orderOf_three_mul_two` this identifies the coset the powers of `3`
sweep. -/
@[category research solved, AMS 11, ref "A1plus", group "th_annealed"]
theorem castHom_three_pow (hk : 3 ≤ k) (n : ℕ) :
    ZMod.castHom (eight_dvd_two_pow hk) (ZMod 8) ((3 : ZMod (2 ^ k)) ^ n)
      = if Even n then 1 else 3 := by
  rw [map_pow, map_ofNat]
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨m, rfl⟩ := he
    rw [ite_eq_left ⟨m, rfl⟩, show m + m = 2 * m by ring, pow_mul, show (3 : ZMod 8) ^ 2 = 1 by decide,
      one_pow]
  · obtain ⟨m, rfl⟩ := ho
    rw [ite_eq_right (by simp), pow_succ, pow_mul,
      show (3 : ZMod 8) ^ 2 = 1 by decide, one_pow, one_mul]

/-- `−1` is **not** a power of `3` mod `2^k`: it reduces to `7` mod 8, and the powers of `3`
reduce to `1` or `3`.  With `orderOf_three_mul_two` this pins down *which* index-2 subgroup
`⟨3⟩` is — the annealed law is uniform on the half of the units that excludes `−1`, so `3ⁿ` and
`−3ⁿ` between them exhaust the odd residues. -/
@[category research solved, AMS 11, ref "A1plus", group "th_annealed"]
theorem neg_one_ne_three_pow (hk : 3 ≤ k) (n : ℕ) : (3 : ZMod (2 ^ k)) ^ n ≠ -1 := by
  intro hcon
  have h := castHom_three_pow hk n
  rw [hcon, map_neg, map_one] at h
  rcases Nat.even_or_odd n with he | ho
  · rw [ite_eq_left he] at h; exact absurd h (by decide)
  · rw [ite_eq_right (by simpa [Nat.not_even_iff_odd] using ho)] at h; exact absurd h (by decide)

end Coset

/-! ## (ii) The annealed chain

`ε ↦ {(3ε + β)/2}` with `β` a fair bit.  Everything below is *finite* probability: expectations
are sums over the `2ᴺ` words of length `N`, divided by `2ᴺ` where relevant. -/

/-- A bit as an integer. -/
def bit : Bool → ℤ
  | true => 1
  | false => 0

@[simp] lemma bit_true : bit true = 1 := rfl
@[simp] lemma bit_false : bit false = 0 := rfl

/-- One step of the annealed chain: `ε ↦ {(3ε + β)/2}`. -/
noncomputable def step (β : Bool) (x : ℝ) : ℝ := Int.fract ((3 * x + (bit β : ℝ)) / 2)

/-- The chain driven by the word `w`, started at `x` (the state is always in `[0, 1)`). -/
noncomputable def run (w : ℕ → Bool) (x : ℝ) : ℕ → ℝ
  | 0 => Int.fract x
  | n + 1 => step (w n) (run w x n)

@[simp] lemma run_zero (w : ℕ → Bool) (x : ℝ) : run w x 0 = Int.fract x := rfl

@[simp] lemma run_succ (w : ℕ → Bool) (x : ℝ) (n : ℕ) :
    run w x (n + 1) = step (w n) (run w x n) := rfl

private lemma fract_eq (a : ℝ) : Int.fract a = a - (⌊a⌋ : ℝ) := rfl

lemma run_nonneg (w : ℕ → Bool) (x : ℝ) (n : ℕ) : 0 ≤ run w x n := by
  cases n
  · exact Int.fract_nonneg _
  · exact Int.fract_nonneg _

lemma run_lt_one (w : ℕ → Bool) (x : ℝ) (n : ℕ) : run w x n < 1 := by
  cases n
  · exact Int.fract_lt_one _
  · exact Int.fract_lt_one _

/-- The state after `n` steps depends only on the first `n` letters of the word. -/
@[category API, AMS 11, ref "A1plus", group "th_annealed"]
theorem run_congr {w w' : ℕ → Bool} {x : ℝ} {n : ℕ} (h : ∀ i < n, w i = w' i) :
    run w x n = run w' x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [run_succ, run_succ, ih fun i hi => h i (by omega), h n (by omega)]

/-! ### The deterministic orbit is a trajectory of the chain -/

/-- The **parity word** of `ξ`: `βₙ = ⌊(3/2)ⁿ ξ⌋ mod 2`.  This is the one specific word that the
actual orbit rides; the annealed model replaces it by a fair coin. -/
noncomputable def parityWord (ξ : ℝ) (n : ℕ) : Bool :=
  decide (⌊(3 / 2 : ℝ) ^ n * ξ⌋ % 2 = 1)

private lemma bit_parityWord (ξ : ℝ) (n : ℕ) :
    (bit (parityWord ξ n) : ℝ) = ((⌊(3 / 2 : ℝ) ^ n * ξ⌋ % 2 : ℤ) : ℝ) := by
  have h := Int.emod_two_eq_zero_or_one ⌊(3 / 2 : ℝ) ^ n * ξ⌋
  unfold parityWord
  rcases h with h | h <;> simp [h]

/-- **The bridge.**  The orbit `n ↦ {(3/2)ⁿ ξ}` is exactly the trajectory of the annealed chain
driven by the parity word of `ξ`.  So the deterministic problem and the random model differ in
*one quantifier*: which word. -/
@[category research solved, AMS 11, ref "A1plus", group "th_annealed"]
theorem run_parityWord (ξ : ℝ) (n : ℕ) :
    run (parityWord ξ) ξ n = Int.fract ((3 / 2 : ℝ) ^ n * ξ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [run_succ, ih, step]
      set y : ℝ := (3 / 2 : ℝ) ^ n * ξ with hy
      obtain ⟨q, hq⟩ : ∃ q : ℤ, 3 * ⌊y⌋ - ⌊y⌋ % 2 = 2 * q :=
        ⟨(3 * ⌊y⌋ - ⌊y⌋ % 2) / 2, by omega⟩
      refine Int.fract_eq_fract.mpr ⟨-q, ?_⟩
      rw [bit_parityWord, fract_eq]
      have hpow : (3 / 2 : ℝ) ^ (n + 1) * ξ = 3 / 2 * y := by rw [hy]; ring
      rw [hpow]
      have : ((3 * ⌊y⌋ - ⌊y⌋ % 2 : ℤ) : ℝ) = ((2 * q : ℤ) : ℝ) := by rw [hq]
      push_cast at this ⊢
      linarith

/-! ### The exact 2-adic separation of distinct words -/

/-- The scaled state is an integer translate of `3ⁿ x`: `2ⁿ εₙ − 3ⁿ x ∈ ℤ`.  Every word therefore
lands in the *same* residue class mod `2^{-n}`. -/
@[category research solved, AMS 11, ref "A1plus", group "th_annealed"]
theorem exists_int_two_pow_mul_run (w : ℕ → Bool) (x : ℝ) (n : ℕ) :
    ∃ z : ℤ, (2 : ℝ) ^ n * run w x n = 3 ^ n * x + z := by
  induction n with
  | zero => exact ⟨-⌊x⌋, by rw [run_zero, fract_eq]; push_cast; ring⟩
  | succ n ih =>
      obtain ⟨z, hz⟩ := ih
      set A : ℝ := (3 * run w x n + (bit (w n) : ℝ)) / 2 with hA
      refine ⟨3 * z + 2 ^ n * bit (w n) - 2 ^ (n + 1) * ⌊A⌋, ?_⟩
      rw [run_succ, step, ← hA, fract_eq, hA]
      push_cast
      linear_combination (3 : ℝ) * hz

/-- **Exact 2-adic separation.**  If two words first differ at index `j`, then for every `n > j`
the scaled difference of their states is an *odd* multiple of `2ʲ` — in particular never zero.
This is the whole of the injectivity below, and it is an identity, not an estimate. -/
@[category research solved, AMS 11, ref "A1plus", group "th_annealed"]
theorem exists_odd_run_sub {w w' : ℕ → Bool} {x : ℝ} {j : ℕ}
    (hlt : ∀ i < j, w i = w' i) (hne : w j ≠ w' j) (s : ℕ) :
    ∃ m : ℤ, Odd m ∧
      (2 : ℝ) ^ (j + 1 + s) * (run w x (j + 1 + s) - run w' x (j + 1 + s)) = 2 ^ j * m := by
  have hbit : bit (w j) - bit (w' j) = 1 ∨ bit (w j) - bit (w' j) = -1 := by
    rcases Bool.eq_false_or_eq_true (w j) with h | h <;>
      rcases Bool.eq_false_or_eq_true (w' j) with h' | h' <;> simp_all
  induction s with
  | zero =>
      have hy : run w x j = run w' x j := run_congr hlt
      set A : ℝ := (3 * run w x j + (bit (w j) : ℝ)) / 2 with hA
      set A' : ℝ := (3 * run w' x j + (bit (w' j) : ℝ)) / 2 with hA'
      refine ⟨bit (w j) - bit (w' j) + 2 * (⌊A'⌋ - ⌊A⌋), ?_, ?_⟩
      · rcases hbit with h | h <;> rw [h]
        · exact ⟨⌊A'⌋ - ⌊A⌋, by ring⟩
        · exact ⟨⌊A'⌋ - ⌊A⌋ - 1, by ring⟩
      · rw [show j + 1 + 0 = j + 1 by ring, run_succ, run_succ, step, step, ← hA, ← hA',
          fract_eq, fract_eq, hA, hA', hy]
        push_cast
        ring
  | succ s ih =>
      obtain ⟨m, hm, hmeq⟩ := ih
      obtain ⟨r, hr⟩ := hm
      set n := j + 1 + s with hn
      set A : ℝ := (3 * run w x n + (bit (w n) : ℝ)) / 2 with hA
      set A' : ℝ := (3 * run w' x n + (bit (w' n) : ℝ)) / 2 with hA'
      set Z : ℤ := 2 ^ s * (bit (w n) - bit (w' n)) - 2 ^ (s + 1) * (⌊A⌋ - ⌊A'⌋) with hZ
      refine ⟨3 * m + 2 * Z, ⟨3 * r + 1 + Z, by rw [hr]; ring⟩, ?_⟩
      rw [show j + 1 + (s + 1) = n + 1 by omega, run_succ, run_succ, step, step, ← hA, ← hA',
        fract_eq, fract_eq, hA, hA']
      have hnj : (2 : ℝ) ^ (n + 1) = 2 ^ j * (2 ^ (s + 2)) := by
        rw [hn, ← pow_add]; congr 1; omega
      have hnj' : (2 : ℝ) ^ n = 2 ^ j * (2 ^ (s + 1)) := by
        rw [hn, ← pow_add]; congr 1; omega
      have hexp : (2 : ℝ) ^ (n + 1) * ((3 * run w x n + (bit (w n) : ℝ)) / 2 - (⌊A⌋ : ℝ)
            - ((3 * run w' x n + (bit (w' n) : ℝ)) / 2 - (⌊A'⌋ : ℝ)))
          = 3 * ((2 : ℝ) ^ n * (run w x n - run w' x n))
            + 2 ^ n * ((bit (w n) : ℝ) - (bit (w' n) : ℝ))
            - 2 ^ (n + 1) * ((⌊A⌋ : ℝ) - (⌊A'⌋ : ℝ)) := by
        have : (2 : ℝ) ^ (n + 1) = 2 ^ n * 2 := by ring
        rw [this]; ring
      rw [hexp, hmeq, hZ, hnj, hnj']
      push_cast
      ring

/-- Distinct length-`N` prefixes drive the chain to distinct states after `N` steps. -/
@[category research solved, AMS 11, ref "A1plus", group "th_annealed"]
theorem run_eq_imp {w w' : ℕ → Bool} {x : ℝ} {N : ℕ} (h : run w x N = run w' x N) :
    ∀ i < N, w i = w' i := by
  classical
  by_contra hc
  push Not at hc
  obtain ⟨i0, hi0N, hi0⟩ := hc
  have hex : ∃ j, j < N ∧ w j ≠ w' j := ⟨i0, hi0N, hi0⟩
  set j := Nat.find hex with hj
  obtain ⟨hjN, hjne⟩ := Nat.find_spec hex
  have hlt : ∀ i < j, w i = w' i := by
    intro i hi
    have := Nat.find_min hex hi
    by_contra hcon
    exact this ⟨by omega, hcon⟩
  obtain ⟨m, hm, hmeq⟩ := exists_odd_run_sub (x := x) hlt hjne (N - j - 1)
  rw [show j + 1 + (N - j - 1) = N by omega, h, sub_self, mul_zero] at hmeq
  have h2 : (2 : ℝ) ^ j ≠ 0 := by positivity
  have hm0 : (m : ℝ) = 0 := by
    rcases mul_eq_zero.mp hmeq.symm with hcon | hcon
    · exact absurd hcon h2
    · exact hcon
  have hmz : m = 0 := by exact_mod_cast hm0
  rw [hmz, Int.odd_iff] at hm
  omega

/-! ### The annealed law is exactly uniform at every level `≤ N` -/

/-- Extend a length-`N` word to an infinite one (by `false`; the tail is never read). -/
def extend {N : ℕ} (w : Fin N → Bool) : ℕ → Bool :=
  fun n => if h : n < N then w ⟨n, h⟩ else false

/-- Restrict an infinite word to its first `N` letters. -/
def restrict (N : ℕ) (w : ℕ → Bool) : Fin N → Bool := fun i => w i

lemma extend_apply {N : ℕ} (w : Fin N → Bool) {i : ℕ} (hi : i < N) :
    extend w i = w ⟨i, hi⟩ := by simp [extend, hi]

lemma extend_restrict_apply {N : ℕ} (w : ℕ → Bool) {i : ℕ} (hi : i < N) :
    extend (restrict N w) i = w i := by simp [extend, restrict, hi]

lemma run_extend_restrict (w : ℕ → Bool) (x : ℝ) {N n : ℕ} (hn : n ≤ N) :
    run (extend (restrict N w)) x n = run w x n :=
  run_congr fun i hi => extend_restrict_apply w (by omega)

/-- The level-`N` cell index of the endpoint is injective in the word. -/
@[category research solved, AMS 11, ref "A1plus", group "th_annealed"]
theorem floor_run_injective (x : ℝ) (N : ℕ) :
    Function.Injective fun w : Fin N → Bool => ⌊(2 : ℝ) ^ N * run (extend w) x N⌋ := by
  intro w w' hww
  simp only at hww
  obtain ⟨z, hz⟩ := exists_int_two_pow_mul_run (extend w) x N
  obtain ⟨z', hz'⟩ := exists_int_two_pow_mul_run (extend w') x N
  have hsplit : (2 : ℝ) ^ N * run (extend w) x N
      = (2 : ℝ) ^ N * run (extend w') x N + ((z - z' : ℤ) : ℝ) := by
    rw [hz, hz']; push_cast; ring
  have hfl : ⌊(2 : ℝ) ^ N * run (extend w) x N⌋
      = ⌊(2 : ℝ) ^ N * run (extend w') x N⌋ + (z - z') := by
    rw [hsplit, Int.floor_add_intCast]
  have hz0 : z - z' = 0 := by omega
  have haa : (2 : ℝ) ^ N * run (extend w) x N = (2 : ℝ) ^ N * run (extend w') x N := by
    rw [hsplit, hz0]; push_cast; ring
  have h2 : ((2 : ℝ) ^ N) ≠ 0 := by positivity
  have hrun := mul_left_cancel₀ h2 haa
  funext i
  have := run_eq_imp hrun i i.2
  rwa [extend_apply w i.2, extend_apply w' i.2] at this

private lemma floor_run_mem (x : ℝ) (N : ℕ) (w : Fin N → Bool) :
    ⌊(2 : ℝ) ^ N * run (extend w) x N⌋ ∈ Finset.Ico (0 : ℤ) (2 ^ N) := by
  have h1 : (0 : ℝ) ≤ (2 : ℝ) ^ N * run (extend w) x N := by
    have := run_nonneg (extend w) x N; positivity
  have h2 : (2 : ℝ) ^ N * run (extend w) x N < ((2 ^ N : ℤ) : ℝ) := by
    have hr := run_lt_one (extend w) x N
    have hp : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
    push_cast
    nlinarith
  refine Finset.mem_Ico.mpr ⟨Int.floor_nonneg.mpr h1, Int.floor_lt.mpr h2⟩

/-- **The annealed law is a perfect `2^{-N}` net.**  The level-`N` cell index is a bijection from
the `2ᴺ` fair-coin words onto `{0, …, 2ᴺ − 1}`, for *every* starting point. -/
@[category research solved, AMS 11, ref "A1plus", group "th_annealed"]
theorem image_floor_run (x : ℝ) (N : ℕ) :
    (Finset.univ : Finset (Fin N → Bool)).image
        (fun w => ⌊(2 : ℝ) ^ N * run (extend w) x N⌋) = Finset.Ico (0 : ℤ) (2 ^ N) := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro j hj
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hj
    exact floor_run_mem x N w
  · rw [Finset.card_image_of_injective _ (floor_run_injective x N), Int.card_Ico]
    simp

/-- **Perfect uniformity at level `N`**: exactly one length-`N` fair-coin word lands in each of
the `2ᴺ` dyadic cells of resolution `2^{-N}`. -/
@[category research solved, AMS 11, ref "A1plus", group "th_annealed"]
theorem card_words_eq_one (x : ℝ) (N : ℕ) {j : ℤ} (hj : 0 ≤ j) (hj' : j < 2 ^ N) :
    {w ∈ (Finset.univ : Finset (Fin N → Bool)) |
      ⌊(2 : ℝ) ^ N * run (extend w) x N⌋ = j}.card = 1 := by
  have hmem : j ∈ (Finset.univ : Finset (Fin N → Bool)).image
      (fun w => ⌊(2 : ℝ) ^ N * run (extend w) x N⌋) := by
    rw [image_floor_run]; exact Finset.mem_Ico.mpr ⟨hj, hj'⟩
  obtain ⟨w, -, hw⟩ := Finset.mem_image.mp hmem
  refine Finset.card_eq_one.mpr ⟨w, ?_⟩
  ext w'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun h => floor_run_injective x N (h.trans hw.symm), fun h => h ▸ hw⟩

private lemma floor_level_eq_iff (y : ℝ) {k N : ℕ} (hkN : k ≤ N) (j : ℤ) :
    ⌊(2 : ℝ) ^ k * y⌋ = j ↔
      ⌊(2 : ℝ) ^ N * y⌋ ∈ Finset.Ico (j * 2 ^ (N - k)) ((j + 1) * 2 ^ (N - k)) := by
  have hsplit : (2 : ℝ) ^ N = 2 ^ k * 2 ^ (N - k) := by
    rw [← pow_add]; congr 1; omega
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (N - k) := by positivity
  rw [Int.floor_eq_iff, Finset.mem_Ico, Int.le_floor, Int.floor_lt]
  push_cast
  rw [hsplit]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · nlinarith
    · nlinarith
  · rintro ⟨h1, h2⟩
    constructor
    · nlinarith
    · nlinarith

/-- **Perfect uniformity at every coarser level.**  For `k ≤ N`, each of the `2^k` level-`k`
cells receives exactly `2^{N-k}` of the `2^N` words: every fixed-width bit-window statistic of
the annealed chain is *exactly* uniform. -/
@[category research solved, AMS 11, ref "A1plus", group "th_annealed"]
theorem card_words_level (x : ℝ) {k N : ℕ} (hkN : k ≤ N) {j : ℤ} (hj : 0 ≤ j) (hj' : j < 2 ^ k) :
    {w ∈ (Finset.univ : Finset (Fin N → Bool)) |
      ⌊(2 : ℝ) ^ k * run (extend w) x N⌋ = j}.card = 2 ^ (N - k) := by
  classical
  set F : (Fin N → Bool) → ℤ := fun w => ⌊(2 : ℝ) ^ N * run (extend w) x N⌋ with hF
  set S : Finset ℤ := Finset.Ico (j * 2 ^ (N - k)) ((j + 1) * 2 ^ (N - k)) with hS
  have hfilter : {w ∈ (Finset.univ : Finset (Fin N → Bool)) |
        ⌊(2 : ℝ) ^ k * run (extend w) x N⌋ = j}
      = {w ∈ (Finset.univ : Finset (Fin N → Bool)) | F w ∈ S} := by
    refine Finset.filter_congr fun w _ => ?_
    simpa [hF, hS] using floor_level_eq_iff (run (extend w) x N) hkN j
  have hSsub : S ⊆ Finset.Ico (0 : ℤ) (2 ^ N) := by
    intro i hi
    rw [hS, Finset.mem_Ico] at hi
    refine Finset.mem_Ico.mpr ⟨?_, ?_⟩
    · have : (0 : ℤ) ≤ j * 2 ^ (N - k) := by positivity
      omega
    · have hsp : (2 : ℤ) ^ N = 2 ^ k * 2 ^ (N - k) := by rw [← pow_add]; congr 1; omega
      have : (j + 1) * 2 ^ (N - k) ≤ 2 ^ k * 2 ^ (N - k) := by
        have hp : (0 : ℤ) < 2 ^ (N - k) := by positivity
        nlinarith
      omega
  have himg : ({w ∈ (Finset.univ : Finset (Fin N → Bool)) | F w ∈ S}).image F = S := by
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨w, hw, rfl⟩; exact hw
    · intro hi
      have hmem : i ∈ (Finset.univ : Finset (Fin N → Bool)).image F := by
        rw [hF, image_floor_run]; exact hSsub hi
      obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hmem
      exact ⟨w, hi, rfl⟩
  have hcard := Finset.card_image_of_injective
    ({w ∈ (Finset.univ : Finset (Fin N → Bool)) | F w ∈ S}) (floor_run_injective x N)
  rw [himg, hS, Int.card_Ico] at hcard
  rw [hfilter, ← hcard,
    show (j + 1) * 2 ^ (N - k) - j * 2 ^ (N - k) = ((2 ^ (N - k) : ℕ) : ℤ) by push_cast; ring,
    Int.toNat_natCast]

/-! ### The exact spectrum: one step annihilates every odd mode -/

/-- The additive character `t ↦ e(h t)`, in the form used by `WeylCriterion`. -/
noncomputable def ee (h : ℤ) (t : ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) * (t : ℂ))

lemma ee_fract (h : ℤ) (t : ℝ) : ee h (Int.fract t) = ee h t := by
  have hm : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) * ((⌊t⌋ : ℤ) : ℂ)) = 1 := by
    have hh := Complex.exp_int_mul_two_pi_mul_I (h * ⌊t⌋)
    rw [show ((h * ⌊t⌋ : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
        = 2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) * ((⌊t⌋ : ℤ) : ℂ) by push_cast; ring] at hh
    exact hh
  unfold ee
  rw [show ((Int.fract t : ℝ) : ℂ) = (t : ℂ) - ((⌊t⌋ : ℤ) : ℂ) by
      rw [fract_eq]; push_cast; ring,
    mul_sub, Complex.exp_sub, hm, div_one]

lemma ee_add (h : ℤ) (s t : ℝ) : ee h (s + t) = ee h s * ee h t := by
  unfold ee
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma ee_half_odd {h : ℤ} (hh : Odd h) : ee h (1 / 2 : ℝ) = -1 := by
  unfold ee
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) * (((1 : ℝ) / 2 : ℝ) : ℂ)
      = (h : ℂ) * ((Real.pi : ℂ) * Complex.I) by push_cast; ring,
    Complex.exp_int_mul, Complex.exp_pi_mul_I]
  exact hh.neg_one_zpow

lemma norm_ee (h : ℤ) (t : ℝ) : ‖ee h t‖ = 1 := by
  unfold ee
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) * (t : ℂ)
      = ((2 * Real.pi * h * t : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- **The whole spectral content, in one line.**  The two branches of the annealed map differ by
exactly `1/2`, so flipping a bit *negates* every odd Fourier mode.  Averaging over the bit
therefore annihilates the mode — there is no gap to estimate. -/
@[category research solved, AMS 11, ref "A1plus" "DF09", group "th_annealed"]
theorem ee_step_flip {h : ℤ} (hh : Odd h) (y : ℝ) :
    ee h (step true y) = - ee h (step false y) := by
  simp only [step, bit_true, bit_false, ee_fract, Int.cast_one, Int.cast_zero, add_zero]
  rw [show (3 * y + 1) / 2 = 3 * y / 2 + 1 / 2 by ring, ee_add, ee_half_odd hh]
  ring

/-- Flipping the last letter that the state at time `p + 1` reads negates every odd mode. -/
@[category API, AMS 11, ref "A1plus", group "th_annealed"]
theorem ee_run_flip {h : ℤ} (hh : Odd h) {N : ℕ} (x : ℝ) (w : Fin N → Bool) {p : ℕ} (hp : p < N) :
    ee h (run (extend (Function.update w ⟨p, hp⟩ (!w ⟨p, hp⟩))) x (p + 1))
      = - ee h (run (extend w) x (p + 1)) := by
  classical
  set i : Fin N := ⟨p, hp⟩ with hi
  set w' := Function.update w i (!w i) with hw'
  have hagree : ∀ l < p, extend w' l = extend w l := by
    intro l hl
    have hlN : l < N := hl.trans hp
    rw [extend_apply w' hlN, extend_apply w hlN, hw', Function.update_of_ne]
    intro hcon
    exact absurd (congrArg Fin.val hcon) (by simp [hi]; omega)
  have hrun : run (extend w') x p = run (extend w) x p := run_congr hagree
  have hbit : extend w' p = !(extend w p) := by
    rw [extend_apply w' hp, extend_apply w hp, hw']
    simp [hi]
  rw [run_succ, run_succ, hrun, hbit]
  cases hwp : extend w p
  · rw [Bool.not_false]
    exact ee_step_flip hh (run (extend w) x p)
  · rw [Bool.not_true, ee_step_flip hh (run (extend w) x p), neg_neg]

/-- **Exact orthogonality.**  Along a fair-coin word the characters of the states at distinct
times are *exactly* orthogonal — no error term.  (Flip the last bit the later state reads: the
earlier state does not see it, the later one is negated.) -/
@[category research solved, AMS 11, ref "A1plus", group "th_annealed"]
theorem sum_ee_run_mul_conj {h : ℤ} (hh : Odd h) {N : ℕ} (x : ℝ) {n m : ℕ}
    (hmn : m < n) (hnN : n ≤ N) :
    ∑ w : Fin N → Bool,
      ee h (run (extend w) x n) * (starRingEnd ℂ) (ee h (run (extend w) x m)) = 0 := by
  classical
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  have hp : p < N := by omega
  set i : Fin N := ⟨p, hp⟩ with hi
  set σ : (Fin N → Bool) → (Fin N → Bool) := fun v => Function.update v i (!v i) with hσ
  have hinv : Function.Involutive σ := by
    intro v
    simp only [hσ, Function.update_self, Bool.not_not, Function.update_idem,
      Function.update_eq_self]
  set F : (Fin N → Bool) → ℂ := fun v =>
    ee h (run (extend v) x (p + 1)) * (starRingEnd ℂ) (ee h (run (extend v) x m)) with hF
  have hFneg : ∀ v, F (σ v) = - F v := by
    intro v
    have h1 : ee h (run (extend (σ v)) x (p + 1)) = - ee h (run (extend v) x (p + 1)) :=
      ee_run_flip hh x v hp
    have h2 : run (extend (σ v)) x m = run (extend v) x m := by
      refine run_congr fun l hl => ?_
      have hlN : l < N := by omega
      rw [extend_apply _ hlN, extend_apply _ hlN]
      refine Function.update_of_ne (fun hcon => ?_) _ _
      have hlp : l = p := by simpa [hi] using congrArg Fin.val hcon
      omega
    rw [hF]
    simp only
    rw [h1, h2]
    ring
  have hkey : (∑ v, F v) = - ∑ v, F v := by
    calc (∑ v, F v) = ∑ v, F (Function.Involutive.toPerm σ hinv v) := (Equiv.sum_comp _ F).symm
      _ = ∑ v, -F v := Finset.sum_congr rfl fun v _ => hFneg v
      _ = - ∑ v, F v := by rw [Finset.sum_neg_distrib]
  have h2 : (2 : ℂ) * ∑ v, F v = 0 := by linear_combination hkey
  have := mul_eq_zero.mp h2
  rcases this with hcon | hcon
  · exact absurd hcon (by norm_num)
  · exact hcon

/-- The Weyl sum of one trajectory of the chain. -/
noncomputable def weylSum (h : ℤ) (x : ℝ) (w : ℕ → Bool) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, ee h (run w x n)

lemma weylSum_extend_restrict (h : ℤ) (x : ℝ) (w : ℕ → Bool) (N : ℕ) :
    weylSum h x (extend (restrict N w)) N = weylSum h x w N :=
  Finset.sum_congr rfl fun n hn => by
    rw [run_extend_restrict w x (le_of_lt (Finset.mem_range.mp hn))]

/-- **The annealed second moment is exact**: `∑_w |S_N(w)|² = N · 2ᴺ`, with no error term.
Equivalently the mean square of `|S_N|/N` is exactly `1/N` — square-root cancellation on
average, by counting alone. -/
@[category research solved, AMS 11, ref "A1plus", group "th_annealed"]
theorem sum_normSq_weylSum {h : ℤ} (hh : Odd h) (x : ℝ) (N : ℕ) :
    ∑ w : Fin N → Bool, ‖weylSum h x (extend w) N‖ ^ 2 = N * 2 ^ N := by
  classical
  have hdiag : ∀ n : ℕ, ∑ w : Fin N → Bool,
      ee h (run (extend w) x n) * (starRingEnd ℂ) (ee h (run (extend w) x n)) = (2 : ℂ) ^ N := by
    intro n
    have hone : ∀ w : Fin N → Bool,
        ee h (run (extend w) x n) * (starRingEnd ℂ) (ee h (run (extend w) x n)) = 1 := by
      intro w
      rw [Complex.mul_conj', norm_ee]
      norm_num
    rw [Finset.sum_congr rfl fun w _ => hone w]
    simp
  have hC : ∑ w : Fin N → Bool,
      weylSum h x (extend w) N * (starRingEnd ℂ) (weylSum h x (extend w) N)
      = (N : ℂ) * 2 ^ N := by
    have expand : ∀ w : Fin N → Bool,
        weylSum h x (extend w) N * (starRingEnd ℂ) (weylSum h x (extend w) N)
          = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
              ee h (run (extend w) x n) * (starRingEnd ℂ) (ee h (run (extend w) x m)) := by
      intro w
      rw [weylSum, map_sum, Finset.sum_mul_sum]
    rw [Finset.sum_congr rfl fun w _ => expand w, Finset.sum_comm]
    rw [Finset.sum_congr rfl fun n _ => Finset.sum_comm]
    have hinner : ∀ n ∈ Finset.range N, ∑ m ∈ Finset.range N, ∑ w : Fin N → Bool,
        ee h (run (extend w) x n) * (starRingEnd ℂ) (ee h (run (extend w) x m))
          = (2 : ℂ) ^ N := by
      intro n hn
      rw [Finset.sum_eq_single n]
      · exact hdiag n
      · intro m hm hmn
        rcases lt_or_gt_of_ne hmn with hlt | hgt
        · exact sum_ee_run_mul_conj hh x hlt (le_of_lt (Finset.mem_range.mp hn))
        · have hc := sum_ee_run_mul_conj hh x hgt (le_of_lt (Finset.mem_range.mp hm))
          have hcc := congrArg (starRingEnd ℂ) hc
          simp only [map_sum, map_mul, Complex.conj_conj, map_zero] at hcc
          rw [← hcc]
          exact Finset.sum_congr rfl fun w _ => mul_comm _ _
      · intro hcon; exact absurd hn hcon
    rw [Finset.sum_congr rfl hinner]
    simp
  have hcast : ((∑ w : Fin N → Bool, ‖weylSum h x (extend w) N‖ ^ 2 : ℝ) : ℂ)
      = (((N : ℝ) * 2 ^ N : ℝ) : ℂ) := by
    push_cast
    rw [← hC]
    exact Finset.sum_congr rfl fun w _ => (Complex.mul_conj' _).symm
  exact_mod_cast hcast

/-! ### The bad set, and how small it is -/

open scoped Classical in
/-- The **bad set**: the length-`N` words whose mode-1 Weyl sum fails to be `δ`-small.  `x` is
the starting point; taking `x = h·ξ` covers every mode `h` of the orbit of `ξ`. -/
noncomputable def Bad (x : ℝ) (N : ℕ) (δ : ℝ) : Finset (Fin N → Bool) :=
  {w ∈ (Finset.univ : Finset (Fin N → Bool)) | δ * N ≤ ‖weylSum 1 x (extend w) N‖}

/-- **The bad set is small, by counting.**  At most `2ᴺ/(δ²N)` of the `2ᴺ` fair-coin words are
bad — an explicit, unconditional, measure-theory-free bound. -/
@[category research solved, AMS 11, ref "A1plus", group "th_annealed"]
theorem card_Bad_mul_le (x : ℝ) (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ((Bad x N δ).card : ℝ) * (δ * N) ^ 2 ≤ N * 2 ^ N := by
  classical
  have hall := sum_normSq_weylSum (h := 1) odd_one x N
  have hsub : ∑ w ∈ Bad x N δ, ‖weylSum 1 x (extend w) N‖ ^ 2
      ≤ ∑ w : Fin N → Bool, ‖weylSum 1 x (extend w) N‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun w _ _ => by positivity)
  have hlow : ((Bad x N δ).card : ℝ) * (δ * N) ^ 2
      ≤ ∑ w ∈ Bad x N δ, ‖weylSum 1 x (extend w) N‖ ^ 2 := by
    have hpt : ∀ w ∈ Bad x N δ, (δ * N) ^ 2 ≤ ‖weylSum 1 x (extend w) N‖ ^ 2 := by
      intro w hw
      have hge : δ * N ≤ ‖weylSum 1 x (extend w) N‖ := by
        simpa [Bad] using hw
      have hnn : (0 : ℝ) ≤ δ * N := by positivity
      nlinarith
    have := Finset.card_nsmul_le_sum (Bad x N δ) _ ((δ * N) ^ 2) hpt
    simpa [nsmul_eq_mul, mul_comm] using this
  linarith [hlow, hsub, hall]

/-- Density form of `card_Bad_mul_le`. -/
@[category research solved, AMS 11, ref "A1plus", group "th_annealed"]
theorem card_Bad_le (x : ℝ) {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : 0 < δ) :
    ((Bad x N δ).card : ℝ) ≤ 2 ^ N / (δ ^ 2 * N) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have h := card_Bad_mul_le x N hδ
  rw [le_div_iff₀ (by positivity)]
  nlinarith [h]

/-! ## (iii) The derandomization gap, compiled -/

private lemma tendsto_div_iff_eventually {f : ℕ → ℂ} :
    Filter.Tendsto (fun N : ℕ => f N / N) Filter.atTop (nhds 0) ↔
      ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in Filter.atTop, ‖f N‖ < δ * N := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  constructor
  · intro h δ hδ
    filter_upwards [h δ hδ, Filter.eventually_ge_atTop 1] with N hN hN1
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    rw [norm_div, Complex.norm_natCast, div_lt_iff₀ hNpos] at hN
    exact hN
  · intro h δ hδ
    filter_upwards [h δ hδ, Filter.eventually_ge_atTop 1] with N hN hN1
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    rw [norm_div, Complex.norm_natCast, div_lt_iff₀ hNpos]
    exact hN

/-- Mode `h` of the orbit of `ξ` is mode `1` of the orbit of `h·ξ`: the whole Weyl family is a
single functional evaluated at shifted starting points. -/
@[category API, AMS 11, ref "A1plus", group "th_annealed"]
theorem weylSum_parityWord (ξ : ℝ) (h : ℤ) (N : ℕ) :
    weylSum 1 ((h : ℝ) * ξ) (parityWord ((h : ℝ) * ξ)) N
      = ∑ n ∈ Finset.range N,
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (h : ℂ) * (((3 / 2 : ℝ) ^ n * ξ : ℝ) : ℂ)) := by
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [run_parityWord, ee_fract]
  unfold ee
  congr 1
  push_cast
  ring

/-- **The derandomization gap, compiled.**  Uniform distribution of `((3/2)ⁿ ξ)` holds *iff*, for
every nonzero mode `h`, the parity word of `h·ξ` eventually escapes the bad set `Bad` — a set
that `card_Bad_le` shows contains at most a `1/(δ²N)` fraction of all words.

This is the sharpest form the statement "the problem is derandomization" can take: the annealed
model settles every quantifier except *which word*, and the open question is precisely whether
one explicitly given word behaves like almost all of them.  By GR4 no annealed fact can decide
it, and by `Z32.exists_balanceVec_zero` no amount of finite-level data can either. -/
@[category research solved, AMS 11, ref "A1plus" "Ber92", group "th_annealed"]
theorem isEquidistributedModuloOne_iff_notMem_bad (ξ : ℝ) :
    IsEquidistributedModuloOne (fun n => (3 / 2 : ℝ) ^ n * ξ) ↔
      ∀ h : ℤ, h ≠ 0 → ∀ δ : ℝ, 0 < δ →
        ∀ᶠ N : ℕ in Filter.atTop,
          (restrict N (parityWord ((h : ℝ) * ξ))) ∉ Bad ((h : ℝ) * ξ) N δ := by
  classical
  rw [← Bertin.uniformlyDistributedModOne_iff_isEquidistributedModuloOne,
    Bertin.uniformlyDistributedModOne_iff_weylCriterion]
  unfold WeylCriterion
  refine forall_congr' fun h => imp_congr_right fun _ => ?_
  rw [tendsto_div_iff_eventually]
  refine forall_congr' fun δ => imp_congr_right fun _ => ?_
  refine Filter.eventually_congr (Filter.Eventually.of_forall fun N => ?_)
  rw [← weylSum_parityWord ξ h N]
  simp only [Bad, Finset.mem_filter, Finset.mem_univ, true_and, not_le,
    weylSum_extend_restrict]

end TH.Annealed
