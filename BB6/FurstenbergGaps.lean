/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB6.Katz
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# Theorem G — Furstenberg's own sequence fails the ratio-floor reading

[Fur67] shows that the multiplicative semigroup `⟨2,3⟩ = {2ᵃ3ᵇ}` is universally densifying, and it
is the example Bugeaud's Problem 10.6 explicitly gestures at ("Furstenberg's `2ᵐ3ⁿ` is sublacunary
but requires two parameters").  **Theorem G says it is not an answer under reading R3**: its
increasing enumeration has, for every `c > 0`, infinitely many indices at which
`m_{n+1}/m_n < 1 + c/log n`.

The proof is Dirichlet plus one counting bound, and it reuses the whole apparatus of
`BB6/Katz.lean`, because `⟨2,3⟩` is `BB6.twoThreeSet Set.univ`:

* Dirichlet gives `1 ≤ q ≤ Q` with `‖qθ‖ ≤ 1/(Q+1)`, `θ = log₂3`;
* the two elements `3^(q+Q)` and `2^P·3^Q`, `P = round(qθ)`, are distinct, both lie between `3^Q`
  and `3^(2Q+1)`, and their ratio is `exp(log 2 · ‖qθ‖) ≤ exp(log 2/(Q+1))`;
* the *smaller* of the two is some `m_n`, and then `m_{n+1}` is at most the larger — no pigeonhole
  over a chain is needed, because the successor of an element of `A` cannot jump over another
  element of `A` (`BB6.exists_index`);
* `2^Q ≤ m_n` forces `n ≥ Q`, and the counting bound `#(A ∩ [0,3ᵏ]) ≤ (2k+1)(k+1)` at `k = 2Q+1`
  forces `n ≤ 28Q²`, hence `√n ≤ 5.3 Q`.

The last step gives more than R3 asks for.  What comes out is the **quantitative** statement
`∃ᶠ n, m_{n+1}/m_n ≤ 1 + 8/√n` (`BB6.theorem_G_sqrt`), and Theorem G proper is the corollary that
`8/√n` eventually beats `c/log n`.  The `n^(-1/2)` scale is exactly the one [AM05, §4] claims as a
*floor* for this sequence, so the two statements pin the Furstenberg gauge from both sides — and
this half is unconditional, whereas the floor is asserted there "by rather complicated lower
bounds for linear forms".  In particular no floor `1 + c n^(-β)` with `β < 1/2` can hold for
all `n`.

The scaling by `3^Q` is what makes the argument short.  Without it one would have to show that the
Dirichlet denominator `q` tends to infinity with `Q`; multiplying both elements by `3^Q` pushes
them past `2^Q` for free, and the index bound only degrades by a factor.

Theorem G is `std3`.  In particular it does **not** use `Bugeaud06.furstenberg_two_three`: the
statement is about the gaps of `⟨2,3⟩`, not about its density, and the note must keep the two
apart — [Fur67] is what makes the sequence interesting, and Theorem G is what disqualifies it.

## Contents

* `BB6.furstenbergSet`, `BB6.furstenbergSeq` — `⟨2,3⟩` and its increasing enumeration;
* `BB6.factorization_two_pow_mul`, `BB6.exponents_le_of_le_pow` — the coordinates of an element;
* `BB6.card_index_le` — the counting bound, as a bound on the index;
* `BB6.exists_index` — the successor lemma, which packages all `Nat.nth` bookkeeping;
* `BB6.exists_close_pair` — Dirichlet, transported to a close pair of elements of `⟨2,3⟩`;
* `BB6.theorem_G_sqrt` — the quantitative form, `∃ᶠ n, m_{n+1}/m_n ≤ 1 + 8/√n`;
* `BB6.theorem_G`, `BB6.not_isGenuinelySublacunary_furstenbergSeq` — Theorem G.

*References:*
  - [Bug12] Bugeaud, Y. *Distribution modulo one and Diophantine approximation*, CUP 2012, Ch. 10.
  - [Fur67] Furstenberg, H. "Disjointness in ergodic theory, minimal sets, and a problem in
    Diophantine approximation." Math. Systems Theory 1 (1967), 1–49.
  - [AM05] Akhunzhanov, R. K. and Moshchevitin, N. G. "Density modulo 1 of sublacunary
    sequences." Math. Notes 77 (2005), 741–750.  [§4 asserts a floor `1 + c n^(-1/2)` for the
    enumeration of `{2ⁱ3ʲ}`; `BB6.theorem_G_sqrt` is the matching unconditional ceiling.]
-/

namespace BB6

open Filter

/-! ## Furstenberg's sequence -/

/-- The multiplicative semigroup `⟨2,3⟩ = {2ᵃ3ᵇ}` of [Fur67], which is `BB6.twoThreeSet` with no
constraint at all on the exponent of `3`. -/
@[category API, AMS 11, ref "Fur67", group "bugeaud_10_6"]
def furstenbergSet : Set ℕ := twoThreeSet Set.univ

/-- The increasing enumeration of `⟨2,3⟩`. -/
@[category API, AMS 11, ref "Fur67", group "bugeaud_10_6"]
noncomputable def furstenbergSeq : ℕ → ℕ := twoThreeSeq Set.univ

@[category API, AMS 11, group "bugeaud_10_6"]
theorem mem_furstenbergSet (a b : ℕ) : 2 ^ a * 3 ^ b ∈ furstenbergSet := ⟨a, b, trivial, rfl⟩

@[category API, AMS 11, group "bugeaud_10_6"]
theorem furstenbergSeq_strictMono : StrictMono furstenbergSeq :=
  twoThreeSeq_strictMono Set.univ_nonempty

@[category API, AMS 11, group "bugeaud_10_6"]
theorem furstenbergSeq_le (j : ℕ) : furstenbergSeq j ≤ 2 ^ j := by
  have h := twoThreeSeq_le (E := Set.univ) (e₀ := 0) trivial j
  simpa [furstenbergSeq] using h

/-! ## Coordinates of an element -/

@[category API, AMS 11, group "bugeaud_10_6"]
theorem factorization_two_pow_mul (a b : ℕ) :
    (2 ^ a * 3 ^ b).factorization 2 = a ∧ (2 ^ a * 3 ^ b).factorization 3 = b := by
  rw [Nat.factorization_mul (by positivity) (by positivity),
    Nat.Prime.factorization_pow Nat.prime_two, Nat.Prime.factorization_pow Nat.prime_three]
  constructor <;> simp

/-- Every element of `⟨2,3⟩` is recovered from its two exponents, which are its `2`- and
`3`-adic valuations.  This is what makes the counting bound below an injection rather than a
choice. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem eq_pow_factorization {z : ℕ} (hz : z ∈ furstenbergSet) :
    z = 2 ^ (z.factorization 2) * 3 ^ (z.factorization 3) := by
  obtain ⟨a, b, -, rfl⟩ := hz
  rw [(factorization_two_pow_mul a b).1, (factorization_two_pow_mul a b).2]

/-- An element of `⟨2,3⟩` below `3ᵏ` has exponents `a ≤ 2k` and `b ≤ k`. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem exponents_le_of_le_pow {z k : ℕ} (hz : z ∈ furstenbergSet) (h : z ≤ 3 ^ k) :
    z.factorization 2 ≤ 2 * k ∧ z.factorization 3 ≤ k := by
  obtain ⟨a, b, -, rfl⟩ := hz
  rw [(factorization_two_pow_mul a b).1, (factorization_two_pow_mul a b).2]
  have h2 : (2 : ℕ) ^ a ≤ 3 ^ k := le_trans (Nat.le_mul_of_pos_right _ (by positivity)) h
  have h3 : (3 : ℕ) ^ b ≤ 3 ^ k := le_trans (Nat.le_mul_of_pos_left _ (by positivity)) h
  refine ⟨?_, (Nat.pow_le_pow_iff_right (by norm_num)).1 h3⟩
  have h4 : (2 : ℕ) ^ a ≤ 2 ^ (2 * k) := by
    refine le_trans h2 ?_
    calc (3 : ℕ) ^ k ≤ 4 ^ k := Nat.pow_le_pow_left (by norm_num) k
      _ = 2 ^ (2 * k) := by rw [pow_mul]; norm_num
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h4

/-! ## The counting bound, as a bound on the index -/

/-- **Counting.**  At most `(2k+1)(k+1)` elements of `⟨2,3⟩` are `≤ 3ᵏ`, so an index whose value
is `≤ 3ᵏ` is itself `< (2k+1)(k+1)`.  The injection is `z ↦ (v₂ z, v₃ z)`. -/
@[category API, AMS 11, ref "Fur67", group "bugeaud_10_6"]
theorem card_index_le {n k : ℕ} (h : furstenbergSeq n ≤ 3 ^ k) : n + 1 ≤ (2 * k + 1) * (k + 1) := by
  have hmem : ∀ i, furstenbergSeq i ∈ furstenbergSet :=
    fun i => twoThreeSeq_mem (E := Set.univ) Set.univ_nonempty i
  set F : ℕ → ℕ × ℕ :=
    fun i => ((furstenbergSeq i).factorization 2, (furstenbergSeq i).factorization 3) with hF
  have hle : ∀ i ∈ Finset.range (n + 1), furstenbergSeq i ≤ 3 ^ k := by
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    exact le_trans (furstenbergSeq_strictMono.monotone hin) h
  have hmaps : ∀ i ∈ Finset.range (n + 1),
      F i ∈ Finset.range (2 * k + 1) ×ˢ Finset.range (k + 1) := by
    intro i hi
    obtain ⟨h2, h3⟩ := exponents_le_of_le_pow (hmem i) (hle i hi)
    simp only [hF, Finset.mem_product, Finset.mem_range]
    omega
  have hinj : Set.InjOn F (Finset.range (n + 1)) := by
    intro i _ j _ hij
    have h1 : furstenbergSeq i = furstenbergSeq j := by
      rw [eq_pow_factorization (hmem i), eq_pow_factorization (hmem j)]
      simp only [hF, Prod.mk.injEq] at hij
      rw [hij.1, hij.2]
    exact furstenbergSeq_strictMono.injective h1
  calc n + 1 = (Finset.range (n + 1)).card := (Finset.card_range _).symm
    _ ≤ (Finset.range (2 * k + 1) ×ˢ Finset.range (k + 1)).card :=
        Finset.card_le_card_of_injOn F hmaps hinj
    _ = (2 * k + 1) * (k + 1) := by simp

/-! ## The successor lemma -/

/-- **All the `Nat.nth` bookkeeping, in one lemma.**  If `u < v` are two elements of `⟨2,3⟩`, then
`u` is some `m_n`, and `m_{n+1} ≤ v` — the successor of `u` in the enumeration cannot jump over
`v`.  So a *pair* of nearby elements already exhibits a *consecutive* pair at least as near, and
no pigeonhole over the chain between them is needed.  The two index bounds come along: `2^Q ≤ u`
forces `Q ≤ n`, and `u ≤ 3ᵏ` forces `n + 1 ≤ (2k+1)(k+1)`. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem exists_index {u v : ℕ} (hu : u ∈ furstenbergSet) (hv : v ∈ furstenbergSet) (huv : u < v)
    {Q k : ℕ} (hQ : 2 ^ Q ≤ u) (hk : u ≤ 3 ^ k) :
    ∃ n : ℕ, Q ≤ n ∧ n + 1 ≤ (2 * k + 1) * (k + 1) ∧
      furstenbergSeq n = u ∧ furstenbergSeq (n + 1) ≤ v := by
  obtain ⟨n, hn⟩ : ∃ n, furstenbergSeq n = u := Nat.subset_range_nth hu
  refine ⟨n, ?_, ?_, hn, ?_⟩
  · by_contra hcon
    push Not at hcon
    have h1 : furstenbergSeq n < furstenbergSeq Q := furstenbergSeq_strictMono hcon
    have h2 := furstenbergSeq_le Q
    omega
  · exact card_index_le (k := k) (by rw [hn]; exact hk)
  · by_contra hcon
    push Not at hcon
    have := Nat.le_nth_of_lt_nth_succ hcon hv
    rw [show Nat.nth (· ∈ twoThreeSet Set.univ) n = furstenbergSeq n from rfl, hn] at this
    omega

/-! ## Dirichlet, transported to a close pair -/

/-- If the log₂-gap of two elements of `⟨2,3⟩` lies in `[0, δ]`, then the first is the smaller and
their ratio is at most `exp(δ log 2)`.  Used twice, once in each order, so that the sign of
`qθ - P` never has to be pushed through the rest of the argument. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem le_and_ratio_le {n n' e e' : ℕ} {δ : ℝ}
    (hδ0 : 0 ≤ ((n' : ℝ) - n) + ((e' : ℝ) - e) * Real.logb 2 3)
    (hδ : ((n' : ℝ) - n) + ((e' : ℝ) - e) * Real.logb 2 3 ≤ δ) :
    (2 ^ n * 3 ^ e : ℕ) ≤ (2 ^ n' * 3 ^ e' : ℕ) ∧
      ((2 ^ n' * 3 ^ e' : ℕ) : ℝ) / ((2 ^ n * 3 ^ e : ℕ) : ℝ) ≤ Real.exp (Real.log 2 * δ) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hposN : (0 : ℕ) < 2 ^ n * 3 ^ e := by positivity
  have hpos : (0 : ℝ) < ((2 ^ n * 3 ^ e : ℕ) : ℝ) := by exact_mod_cast hposN
  have hratio := twoThree_ratio_eq_exp n n' e e'
  refine ⟨?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ ((2 ^ n' * 3 ^ e' : ℕ) : ℝ) / ((2 ^ n * 3 ^ e : ℕ) : ℝ) := by
      rw [hratio, ← Real.exp_zero]
      exact Real.exp_le_exp.2 (by nlinarith)
    exact_mod_cast (one_le_div hpos).1 h1
  · rw [hratio]
    exact Real.exp_le_exp.2 (by nlinarith)

/-- **The close pair.**  For every `Q ≥ 1` there are two distinct elements `u < v` of `⟨2,3⟩` with
`3^Q ≤ u`, `v ≤ 3^(2Q+1)` and `v/u ≤ exp(log 2/(Q+1))`.  They are `3^(q+Q)` and `2^P·3^Q` with
`q ≤ Q` from Dirichlet and `P = round(q log₂3)`; the common factor `3^Q` is what puts them past
`2^Q` without any information about how large `q` is. -/
@[category research solved, AMS 11, ref "Fur67", group "bugeaud_10_6"]
theorem exists_close_pair {Q : ℕ} (hQ : 1 ≤ Q) :
    ∃ u v : ℕ, u ∈ furstenbergSet ∧ v ∈ furstenbergSet ∧ u < v ∧
      3 ^ Q ≤ u ∧ v ≤ 3 ^ (2 * Q + 1) ∧
      (v : ℝ) / u ≤ Real.exp (Real.log 2 * (1 / (Q + 1))) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hθ : Real.logb 2 3 * Real.log 2 = Real.log 3 := by
    rw [Real.logb]; field_simp
  have hθpos : (0 : ℝ) < Real.logb 2 3 := by
    have : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
    nlinarith
  -- Dirichlet
  obtain ⟨q, hq0, hqQ, hqd⟩ :=
    Real.exists_nat_abs_mul_sub_round_le (Real.logb 2 3) (show 0 < Q by omega)
  have hqθ : (0 : ℝ) < (q : ℝ) * Real.logb 2 3 := by
    have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq0
    nlinarith
  -- the rounded exponent, as a natural number
  have hP0 : 0 ≤ round ((q : ℝ) * Real.logb 2 3) := by
    rw [round_eq]; exact Int.floor_nonneg.2 (by linarith)
  obtain ⟨P, hPcast⟩ : ∃ P : ℕ, ((P : ℕ) : ℝ) = round ((q : ℝ) * Real.logb 2 3) :=
    ⟨(round ((q : ℝ) * Real.logb 2 3)).toNat, by exact_mod_cast Int.toNat_of_nonneg hP0⟩
  have hδ : |(q : ℝ) * Real.logb 2 3 - P| ≤ 1 / (Q + 1) := by rw [hPcast]; exact hqd
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hδ1 : |(q : ℝ) * Real.logb 2 3 - P| ≤ 1 := by
    refine le_trans hδ ?_
    rw [div_le_one (by linarith)]; linarith
  -- the two elements
  have hxA : (2 : ℕ) ^ 0 * 3 ^ (q + Q) ∈ furstenbergSet := mem_furstenbergSet _ _
  have hyA : (2 : ℕ) ^ P * 3 ^ Q ∈ furstenbergSet := mem_furstenbergSet _ _
  -- they are distinct: `3^q` is odd and `> 1`, `2^P` is not
  have hne : (2 : ℕ) ^ 0 * 3 ^ (q + Q) ≠ 2 ^ P * 3 ^ Q := by
    simp only [pow_zero, one_mul, pow_add]
    intro hcon
    have h3 : (3 : ℕ) ^ q = 2 ^ P := by
      have hpos : 0 < (3 : ℕ) ^ Q := by positivity
      exact Nat.eq_of_mul_eq_mul_right hpos hcon
    rcases Nat.eq_zero_or_pos P with hP | hP
    · rw [hP, pow_zero] at h3
      rcases (Nat.pow_eq_one).1 h3 with h | h
      · omega
      · omega
    · have h1 : (3 : ℕ) ^ q % 2 = 1 := by rw [Nat.pow_mod]; norm_num
      have h2 : (2 : ℕ) ^ P % 2 = 0 := by
        obtain ⟨P', rfl⟩ : ∃ P', P = P' + 1 := ⟨P - 1, by omega⟩
        rw [pow_succ]
        omega
      omega
  -- both are at least `3^Q`
  have hxge : (3 : ℕ) ^ Q ≤ 2 ^ 0 * 3 ^ (q + Q) := by
    rw [pow_zero, one_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hyge : (3 : ℕ) ^ Q ≤ 2 ^ P * 3 ^ Q := Nat.le_mul_of_pos_left _ (by positivity)
  -- both are at most `3^(2Q+1)`
  have h2P : (2 : ℕ) ^ P ≤ 2 * 3 ^ q := by
    have hR : (((2 : ℕ) ^ P : ℕ) : ℝ) ≤ ((2 * 3 ^ q : ℕ) : ℝ) := by
      refine (Real.log_le_log_iff (by positivity) (by positivity)).1 ?_
      push_cast
      rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      have hPle : (P : ℝ) ≤ (q : ℝ) * Real.logb 2 3 + 1 := by
        have := abs_le.1 hδ1
        linarith [this.1, this.2]
      nlinarith
    exact_mod_cast hR
  have hxle : (2 : ℕ) ^ 0 * 3 ^ (q + Q) ≤ 3 ^ (2 * Q + 1) := by
    rw [pow_zero, one_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hyle : (2 : ℕ) ^ P * 3 ^ Q ≤ 3 ^ (2 * Q + 1) := by
    calc (2 : ℕ) ^ P * 3 ^ Q ≤ (2 * 3 ^ q) * 3 ^ Q := Nat.mul_le_mul_right _ h2P
      _ = 2 * 3 ^ (q + Q) := by rw [pow_add]; ring
      _ ≤ 3 * 3 ^ (2 * Q) := by
          refine Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega))
      _ = 3 ^ (2 * Q + 1) := by rw [pow_succ]; ring
  -- the ratio, in both orders
  have hδplus : (q : ℝ) * Real.logb 2 3 - P ≤ 1 / (Q + 1) :=
    le_trans (le_abs_self _) hδ
  have hδminus : -((q : ℝ) * Real.logb 2 3 - P) ≤ 1 / (Q + 1) :=
    le_trans (neg_le_abs _) hδ
  by_cases hcase : (P : ℝ) ≤ (q : ℝ) * Real.logb 2 3
  · -- `2^P·3^Q ≤ 3^(q+Q)`
    obtain ⟨hle, hrat⟩ := le_and_ratio_le (n := P) (n' := 0) (e := Q) (e' := q + Q)
      (δ := 1 / ((Q : ℝ) + 1)) (by push_cast; linarith) (by push_cast; linarith)
    exact ⟨2 ^ P * 3 ^ Q, 2 ^ 0 * 3 ^ (q + Q), hyA, hxA, lt_of_le_of_ne hle (Ne.symm hne),
      hyge, hxle, hrat⟩
  · -- `3^(q+Q) < 2^P·3^Q`
    push Not at hcase
    obtain ⟨hle, hrat⟩ := le_and_ratio_le (n := 0) (n' := P) (e := q + Q) (e' := Q)
      (δ := 1 / ((Q : ℝ) + 1)) (by push_cast; nlinarith) (by push_cast; nlinarith)
    exact ⟨2 ^ 0 * 3 ^ (q + Q), 2 ^ P * 3 ^ Q, hxA, hyA, lt_of_le_of_ne hle hne,
      hxge, hyle, hrat⟩

/-! ## Theorem G -/

/-- **Theorem G, quantitative.**  Infinitely often the ratio of consecutive elements of `⟨2,3⟩`
is at most `1 + 8/√n`.  This is the ceiling that matches [AM05, §4]'s claimed floor
`s_{n+1}/s_n ≥ 1 + c n^(-1/2)`: the two together say the Furstenberg gauge is exactly of order
`n^(-1/2)`, and in particular **no floor with exponent `β < 1/2` can hold for all `n`**.  Unlike
the floor, this is unconditional.

The constant `8` is what the proof gives with `√28 ≤ 5.3` and `2 log 2 ≤ 1.3863`; it is not
claimed to be optimal. -/
@[category research solved, AMS 11, ref "Bug12" "Fur67", group "bugeaud_10_6",
  formal_uses exists_close_pair exists_index]
theorem theorem_G_sqrt :
    ∃ᶠ n : ℕ in atTop,
      (furstenbergSeq (n + 1) : ℝ) / furstenbergSeq n ≤ 1 + 8 / Real.sqrt n := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 0.694 := le_of_lt (lt_trans Real.log_two_lt_d9 (by norm_num))
  rw [Filter.frequently_atTop]
  intro N₀
  obtain ⟨Q, hQN, hQ6⟩ : ∃ Q : ℕ, N₀ ≤ Q ∧ 6 ≤ Q := ⟨max N₀ 6, le_max_left _ _, le_max_right _ _⟩
  -- the close pair and the consecutive pair it exhibits
  obtain ⟨u, v, hu, hv, huv, hulb, hvub, hratio⟩ := exists_close_pair (Q := Q) (by omega)
  have hu2 : 2 ^ Q ≤ u := le_trans (Nat.pow_le_pow_left (by norm_num) Q) hulb
  have huk : u ≤ 3 ^ (2 * Q + 1) := le_trans huv.le hvub
  obtain ⟨n, hQn, hnk, hseqn, hseqn1⟩ := exists_index hu hv huv hu2 huk
  refine ⟨n, le_trans hQN hQn, ?_⟩
  -- index bounds: `Q ≤ n ≤ 28 Q²`
  have hQR : (6 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ6
  have hn28 : n ≤ 28 * Q ^ 2 := by nlinarith [hnk, hQ6]
  have hnR : (n : ℝ) ≤ 28 * (Q : ℝ) ^ 2 := by exact_mod_cast hn28
  have hnge : (6 : ℝ) ≤ (n : ℝ) := le_trans hQR (by exact_mod_cast hQn)
  -- `√n ≤ 5.3 Q`
  have hsqrtpos : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
  have hsqrt : Real.sqrt n ≤ 5.3 * (Q : ℝ) := by
    have h3 : 28 * (Q : ℝ) ^ 2 ≤ (5.3 * (Q : ℝ)) ^ 2 := by nlinarith
    calc Real.sqrt n ≤ Real.sqrt (28 * (Q : ℝ) ^ 2) := Real.sqrt_le_sqrt hnR
      _ ≤ Real.sqrt ((5.3 * (Q : ℝ)) ^ 2) := Real.sqrt_le_sqrt h3
      _ = 5.3 * (Q : ℝ) := Real.sqrt_sq (by linarith)
  -- the ratio of the consecutive pair is at most the ratio of the close pair
  have hupos : (0 : ℝ) < (u : ℝ) := by
    have h : 0 < u := lt_of_lt_of_le (by positivity) hulb
    exact_mod_cast h
  have hstep : (furstenbergSeq (n + 1) : ℝ) / furstenbergSeq n ≤ (v : ℝ) / u := by
    rw [hseqn]
    gcongr
  -- `exp t ≤ 1 + 2t` for `0 ≤ t ≤ 1/2`
  have htpos : (0 : ℝ) ≤ Real.log 2 * (1 / ((Q : ℝ) + 1)) := by positivity
  have ht : Real.log 2 * (1 / ((Q : ℝ) + 1)) ≤ 1 / 2 := by
    have h1 : 1 / ((Q : ℝ) + 1) ≤ 1 / 7 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    nlinarith
  have hexp : Real.exp (Real.log 2 * (1 / ((Q : ℝ) + 1)))
      ≤ 1 + 2 * (Real.log 2 * (1 / ((Q : ℝ) + 1))) := by
    set t : ℝ := Real.log 2 * (1 / ((Q : ℝ) + 1)) with htdef
    have h1 : 1 - t ≤ Real.exp (-t) := by linarith [Real.add_one_le_exp (-t)]
    have h2 : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
    have h3 : (1 - t) * Real.exp t ≤ 1 := by
      calc (1 - t) * Real.exp t ≤ Real.exp (-t) * Real.exp t :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos t).le
        _ = 1 := h2
    have h4 : (1 : ℝ) ≤ (1 + 2 * t) * (1 - t) := by nlinarith
    nlinarith [Real.exp_pos t]
  -- and `2 log 2/(Q+1) ≤ 8/√n`
  have hfinal : 2 * (Real.log 2 * (1 / ((Q : ℝ) + 1))) ≤ 8 / Real.sqrt n := by
    have e1 : 2 * (Real.log 2 * (1 / ((Q : ℝ) + 1))) = (2 * Real.log 2) / ((Q : ℝ) + 1) := by ring
    rw [e1, div_le_div_iff₀ (by linarith) hsqrtpos]
    nlinarith
  calc (furstenbergSeq (n + 1) : ℝ) / furstenbergSeq n ≤ (v : ℝ) / u := hstep
    _ ≤ Real.exp (Real.log 2 * (1 / ((Q : ℝ) + 1))) := by exact_mod_cast hratio
    _ ≤ 1 + 2 * (Real.log 2 * (1 / ((Q : ℝ) + 1))) := hexp
    _ ≤ 1 + 8 / Real.sqrt n := by linarith

/-- **Theorem G.**  For every `c > 0` there are infinitely many `n` with
`m_{n+1}/m_n < 1 + c/log n`, where `m` is the increasing enumeration of `⟨2,3⟩`.  So Furstenberg's
sequence — the one Problem 10.6 itself points at — is not an answer under the ratio-floor
reading R3.  It is a corollary of the quantitative form, since `8/√n` beats `c/log n` eventually
for every fixed `c`; the `log n` gauge of R3 is far coarser than what `⟨2,3⟩` actually does. -/
@[category research solved, AMS 11, ref "Bug12" "Fur67", group "bugeaud_10_6",
  formal_uses theorem_G_sqrt eventually_log_le]
theorem theorem_G {c : ℝ} (hc : 0 < c) :
    ∃ᶠ n : ℕ in atTop,
      (furstenbergSeq (n + 1) : ℝ) / furstenbergSeq n < 1 + c / Real.log n := by
  have hev : ∀ᶠ n : ℕ in atTop, 8 / Real.sqrt n < c / Real.log n := by
    have h1 := eventually_log_le (show (0 : ℝ) < c / 16 by positivity)
      (show (0 : ℝ) < 1 / 2 by norm_num)
    filter_upwards [h1, Filter.eventually_ge_atTop 2] with n hn hn2
    rw [← Real.sqrt_eq_rpow] at hn
    have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    have hsq : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
    have hlogn : (0 : ℝ) < Real.log n := Real.log_pos (by linarith)
    rw [div_lt_div_iff₀ hsq hlogn]
    nlinarith
  refine ((theorem_G_sqrt).and_eventually hev).mono ?_
  rintro n ⟨h1, h2⟩
  linarith

/-- **Theorem G, in the reading's own language.**  Furstenberg's sequence is not R3-regular.  Put
beside Theorem&nbsp;F this is the point of §3.3 of the note: both known universally densifying
constructions reduce Problem 10.6 under R3 to the Diophantine behaviour of `log₂3` — Furstenberg's
at polynomial scale, where the answer is *no*, and Katz's at tower scale, where it is open. -/
@[category research solved, AMS 11, ref "Bug12" "Fur67", group "bugeaud_10_6",
  formal_uses theorem_G]
theorem not_isGenuinelySublacunary_furstenbergSeq :
    ¬ Bugeaud06.IsGenuinelySublacunary furstenbergSeq := by
  rintro ⟨c, hc, hev⟩
  have := (theorem_G hc).and_eventually hev
  obtain ⟨n, h1, h2⟩ := this.exists
  linarith

end BB6
