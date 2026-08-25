/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import SZ.Defs
import SZ.CoverGame
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# `√3 ∈ 𝒵`: [Dub06EO] Problem 3, answered

> **Problem 3** ([Dub06EO] p. 335).  *Determine whether `√3` belongs to `𝒮` or to `𝒵`.*

**Answer: `√3 ∈ 𝒵`** — `sqrtThree_mem_MahlerZ`, with the explicit digitally-constructed
witness

`witXi = 1.3416089979611266516309894306526154258451…`

## Which witness?

The translate equation of plan §1.2 has a **Cantor set** of solutions (the survivor tree
branches at rate `≈ 4/3`), so a witness is pinned only once a preference order is fixed.
`plans/plan-dubD1O5.html` §1.4 quotes `1.341665814942779748832194927978…`, the point
selected by the alternation-preferring first-fit greedy of the X0/X1 scripts.  The rule
formalised in `SZ/CoverGame.lean` — *prefer `a = 0`, then prefer `b = 2`* — is the one that
makes lemma L1 fall out of the region structure with no interleaving argument, and it
selects a **different** point of the same solution set; the two agree on the first six
floors `2, 4, 6, 12, 20, 36` and part company at `n = 7`.  Both are valid answers to
Problem 3; this file certifies the second.  See `SZ/checks/dubD1O5-x3-leanrule.py`.

## The assembly (plan §1.2, §1.4)

Split `n` by parity.  With `u = 3 ξ`, `n = 2s` gives `⌊ξ 3^s⌋ = ⌊u 3^{s-1}⌋` and
`n = 2s+1` gives `⌊ξ √3 3^s⌋ = ⌊(u/√3) 3^s⌋`.  So `√3 ∈ 𝒵` as soon as one positive `u`
has *both* `u` and `u/√3` with all base-`3` digits even, i.e. as soon as

`x - √3 y = 2√3 - 4`,  `x, y ∈ K₃`

is solvable with canonical (non-`2̄`-tailed) digit streams.  `SZ/CoverGame.lean` solves it
constructively — that is the plan's collapse of "attack (ii)" to a single-scale base-`3`
cover induction, and at `m = 3` the cover statement is Utz's 1951 theorem — and
`SZ/DigitParity.lean` converts the digit condition into the parity of the floors.

Here the two are glued:

`u = 4 + witX = √3 (2 + witY)`,  `ξ = u / 3`,

`witX` being the greedy's `x`-stream and `witY` the digitwise complement `2 - bᵢ` of its
`y''`-stream.  The two hypotheses that `SZ/DigitParity.lean` cannot supply — infinitely
many `aᵢ = 0`, infinitely many `bᵢ = 2` — are exactly the plan's lemma L1, proved in
`SZ/CoverGame.lean` as `exists_digitA_eq_zero` and `exists_digitB_eq_two`.

## Provenance of the result (note `note-dubD1O5-G1.html` §1)

`√m ∈ 𝒵` is [Dub06EO] Thm 1(i) for `m ≥ 9` (there `√m ≥ 3`) and trivial for perfect
squares (`ξ = 2`).  The cells `m ∈ {3, 5, 6, 7, 8}` are the ones no printed proof was
found for; `m = 3` is Problem 3 itself.  `SZ/Radicals.lean` (plan milestone M3) is to carry
the remaining four.

## References

* [Dub06EO] A. Dubickas, *Even and odd integral parts of powers of a real number*,
  Glasgow Math. J. **48** (2006), 331–336.
* [Utz51] W. R. Utz, *The distance set for the Cantor discontinuum*, Amer. Math. Monthly
  **58** (1951), 407–408.
-/

namespace SZ

/-! ## The witness -/

/-- The `y`-digit stream of the witness: the digitwise complement `2 - bᵢ` of the greedy's
`y''`-stream, so that `witY = 1 - y''` (plan §1.2's involution `y ↦ M₃ - y`). -/
noncomputable def digitY (i : ℕ) : ℤ := 2 - digitB i

@[category API, AMS 11, ref "Dub06EO", group "dub06_problem3_sqrt3"]
theorem digitY_mem (i : ℕ) : digitY i = 0 ∨ digitY i = 2 := by
  rcases digitB_mem i with h | h <;> simp [digitY, h]

@[category API, AMS 11, ref "Dub06EO", group "dub06_problem3_sqrt3"]
theorem digitY_even (i : ℕ) : Even (digitY i) := by
  rcases digitY_mem i with h | h <;> rw [h] <;> decide

@[category API, AMS 11, ref "Dub06EO", group "dub06_problem3_sqrt3"]
theorem isDigits_digitY : IsDigits 3 digitY :=
  { two_le := by norm_num
    nonneg := fun i => by rcases digitY_mem i with h | h <;> omega
    le_sub_one := fun i => by rcases digitY_mem i with h | h <;> omega }

/-- `x = ∑ aᵢ 3^{-i}`, the greedy's first Cantor coordinate. -/
noncomputable def witX : ℝ := digitReal 3 digitA

/-- `y = 1 - ∑ bᵢ 3^{-i}`, the greedy's second Cantor coordinate after the involution. -/
noncomputable def witY : ℝ := digitReal 3 digitY

/-- **The witness** `ξ = (4 + x)/3 = 1.3416089979611266516309894306526154258451…`, the
point of plan §1.2's solution set selected by `pick`'s preference order. -/
noncomputable def witXi : ℝ := (4 + witX) / 3

@[category API, AMS 11, ref "Dub06EO", group "dub06_problem3_sqrt3"]
theorem witY_eq : witY = 1 - digitReal 3 digitB := by
  have hfun : (fun i => ((3 : ℕ) : ℤ) - 1 - digitB i) = digitY := by
    funext i
    simp only [digitY]
    norm_num
  rw [witY, ← hfun, digitReal_compl isDigits_digitB]

/-- **The coupling** `u = 4 + x = √3 (2 + y)` — the whole content of plan §1.2, and the
reason one witness serves both parity classes. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_problem3_sqrt3"]
theorem coupling : 4 + witX = Real.sqrt 3 * (2 + witY) := by
  have h := digitReal_translate
  rw [witY_eq, witX]
  have hs : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  nlinarith [h, hs]

@[category API, AMS 11, ref "Dub06EO", group "dub06_problem3_sqrt3"]
theorem witX_mem : 0 ≤ witX ∧ witX ≤ 1 :=
  ⟨digitReal_nonneg isDigits_digitA, digitReal_le_one isDigits_digitA⟩

/-- The witness is pinned to `[4/3, 5/3]`; the exact value, from the digit stream, is
`1.3416089979611266516309894306526154258451…` (`SZ/checks/dubD1O5-x3-leanrule.py`). -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_problem3_sqrt3"]
theorem witXi_mem : 4 / 3 ≤ witXi ∧ witXi ≤ 5 / 3 := by
  obtain ⟨h0, h1⟩ := witX_mem
  constructor <;> · rw [witXi]; linarith

@[category API, AMS 11, ref "Dub06EO", group "dub06_problem3_sqrt3"]
theorem witXi_pos : 0 < witXi := lt_of_lt_of_le (by norm_num) witXi_mem.1

/-! ## The floors -/

/-- Even `n`: `ξ (√3)^{2(s+1)} = (4 + x) 3ˢ`, whose floor is even by Lemma D — the `aᵢ`
are all even, and L1(a) supplies a `0` beyond index `s`, so the digits are canonical. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_problem3_sqrt3"]
theorem even_floor_even_case (s : ℕ) : Even ⌊witXi * Real.sqrt 3 ^ (2 * (s + 1))⌋ := by
  obtain ⟨i₀, hi₀, hz⟩ := exists_digitA_eq_zero s
  have hval : witXi * Real.sqrt 3 ^ (2 * (s + 1))
      = (((4 : ℤ) : ℝ) + digitReal 3 digitA) * ((3 : ℕ) : ℝ) ^ s := by
    rw [pow_mul, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), witXi, witX]
    push_cast
    rw [pow_succ]
    ring
  rw [hval]
  exact even_floor_add_digitReal_mul_pow isDigits_digitA (by decide) digitA_even s hi₀
    (by omega)

/-- Odd `n`: `ξ (√3)^{2s+1} = (2 + y) 3ˢ`, whose floor is even by Lemma D — L1(b) supplies
a `bᵢ = 2`, i.e. a `y`-digit `0`, beyond index `s`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_problem3_sqrt3"]
theorem even_floor_odd_case (s : ℕ) : Even ⌊witXi * Real.sqrt 3 ^ (2 * s + 1)⌋ := by
  obtain ⟨i₀, hi₀, hz⟩ := exists_digitB_eq_two s
  have hsmall : digitY i₀ ≤ ((3 : ℕ) : ℤ) - 2 := by simp [digitY, hz]
  have hs : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hval : witXi * Real.sqrt 3 ^ (2 * s + 1)
      = (((2 : ℤ) : ℝ) + digitReal 3 digitY) * ((3 : ℕ) : ℝ) ^ s := by
    rw [pow_succ, pow_mul, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), witXi]
    have hc : 4 + witX = Real.sqrt 3 * (2 + witY) := coupling
    rw [show (4 + witX) / 3 = Real.sqrt 3 * (2 + witY) / 3 by rw [hc], witY]
    push_cast
    field_simp
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    ring
  rw [hval]
  exact even_floor_add_digitReal_mul_pow isDigits_digitY (by decide) digitY_even s hi₀ hsmall

/-! ## The capstone -/

@[category API, AMS 11, ref "Dub06EO", group "dub06_problem3_sqrt3"]
theorem one_lt_sqrt_three : (1 : ℝ) < Real.sqrt 3 := by
  have h : Real.sqrt 1 < Real.sqrt 3 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rwa [Real.sqrt_one] at h

/-- **[Dub06EO] Problem 3, answered: `√3 ∈ 𝒵`.**  There is a nonzero real `ξ` — the
explicit `witXi = 1.3416089979611266516309894306526154258451…` built by the cover greedy
— with `⌊ξ (√3)ⁿ⌋` even for every `n ≥ 1`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_problem3_sqrt3"]
theorem sqrtThree_mem_MahlerZ : Real.sqrt 3 ∈ MahlerZ := by
  refine ⟨one_lt_sqrt_three, witXi, ne_of_gt witXi_pos, fun n hn => ?_⟩
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨t, ht⟩ := he
    have ht1 : 1 ≤ t := by omega
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    have : n = 2 * (s + 1) := by omega
    rw [this]
    exact even_floor_even_case s
  · obtain ⟨s, rfl⟩ := ho
    exact even_floor_odd_case s

/-- The complementary statement: `√3 ∉ 𝒮`. -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_problem3_sqrt3"]
theorem sqrtThree_notMem_S : Real.sqrt 3 ∉ S := fun h => h.2 sqrtThree_mem_MahlerZ

/-! ## Sanity checks: the first two floors of the orbit (plan §1.4) -/

/-- `⌊ξ √3⌋ = 2`. -/
@[category test, AMS 11, ref "Dub06EO", group "dub06_problem3_sqrt3"]
theorem floor_witXi_sqrtThree : ⌊witXi * Real.sqrt 3⌋ = 2 := by
  obtain ⟨i₀, hi₀, hz⟩ := exists_digitB_eq_two 0
  have hsmall : digitY i₀ ≤ ((3 : ℕ) : ℤ) - 2 := by simp [digitY, hz]
  have hs : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hval : witXi * Real.sqrt 3
      = (((2 : ℤ) : ℝ) + digitReal 3 digitY) * ((3 : ℕ) : ℝ) ^ 0 := by
    rw [witXi, show (4 + witX) / 3 = Real.sqrt 3 * (2 + witY) / 3 by rw [coupling], witY]
    push_cast
    field_simp
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    ring
  rw [hval, floor_add_digitReal_mul_pow isDigits_digitY 2 0 hi₀ hsmall]
  simp

/-- `⌊3 ξ⌋ = ⌊ξ (√3)²⌋ = 4`. -/
@[category test, AMS 11, ref "Dub06EO", group "dub06_problem3_sqrt3"]
theorem floor_witXi_three : ⌊witXi * Real.sqrt 3 ^ 2⌋ = 4 := by
  obtain ⟨i₀, hi₀, hz⟩ := exists_digitA_eq_zero 0
  have hval : witXi * Real.sqrt 3 ^ 2
      = (((4 : ℤ) : ℝ) + digitReal 3 digitA) * ((3 : ℕ) : ℝ) ^ 0 := by
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), witXi, witX]
    push_cast
    ring
  rw [hval, floor_add_digitReal_mul_pow isDigits_digitA 4 0 hi₀ (by omega)]
  simp

end SZ
