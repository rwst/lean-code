/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Data.Nat.Periodic
import Mathlib.Data.Fintype.Pi
import EVG25.UniformCorrespondence
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The exact prefix law for `U`-words

`U n = ⌊3n/2⌋ + 1` ([EVG25] Notation 3.7, `CC.Base3div2.U`) writes, along the orbit of a seed
`n₀`, an infinite word over `{1, 2}` in rational base 3/2 ([EVG25] Prop. 15); its `i`-th letter is
the parity `U^i(n₀) mod 2` (`uLetter`).  This file proves the finite-horizon half of the
almost-all theory of plan EVGQ17-M0:

* `U_iter_add_mul_two_pow` — the seed shift (F7 with multiples):
  `U^i(n + t·2^m) = U^i(n) + t·3^i·2^(m-i)` for `i ≤ m`;
* `uLetter_add_mul_two_pow` / `uLetter_add_two_pow_self` — adding `t·2^m` changes no letter
  before position `m`, and adding `2^m` flips letter `m`;
* `uPrefix_bijective` — **Theorem 1**: the length-`k` prefix map `ZMod (2^k) → (Fin k → Bool)` is
  a bijection, i.e. the `U`-words of `0, …, 2^k - 1` cut at length `k` are exactly the `2^k`
  coin-toss paths;
* `card_filter_uPrefix_mem` — exact interval counting: on every interval of length `t·2^k`, every
  set `W` of length-`k` words is hit exactly `t·|W|` times.

`U` is a relatively prime generalized 3x+1 map in the sense of Matthews–Watts, and Theorem 1 is
the `U`-instance of [Mat10] Thm 2.2(ii)/Thm 3.1 (credited there to [MW84]); for the 3x+1 map it is
the Terras–Everett bijection (`CC.terras_bijection`).

## References
* [EVG25] S. Eliahou, J.-L. Verger-Gaugry, *The number system in rational base 3/2 and the
  3x+1 problem*, C. R. Math. 363 (2025) 329–336.
* [Mat10] K. R. Matthews, *Generalized 3x+1 mappings: Markov chains and ergodic theory*, in
  *The Ultimate Challenge: The 3x+1 Problem*, AMS 2010, 79–103.
* [MW84] K. R. Matthews, A. M. Watts, *A generalization of Hasse's generalization of the Syracuse
  algorithm*, Acta Arith. 43 (1984) 167–175.
-/

open CC CC.Base3div2

namespace EVG25.M0

/-! ## The seed shift -/

theorem U_add_two_mul (n s : ℕ) : U (n + 2 * s) = U n + 3 * s := by
  unfold U; split <;> split <;> omega

/-- **F7 with multiples.** Shifting the seed by `t·2^m` shifts the `i`-th iterate by
`t·3^i·2^(m-i)`, for every `i ≤ m`. -/
theorem U_iter_add_mul_two_pow {i m : ℕ} (hi : i ≤ m) (n t : ℕ) :
    U_iter i (n + t * 2 ^ m) = U_iter i n + t * 3 ^ i * 2 ^ (m - i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [U_iter_succ, U_iter_succ, ih (by omega)]
    have h : m - i = (m - (i + 1)) + 1 := by omega
    rw [h, pow_succ, show t * 3 ^ i * (2 ^ (m - (i + 1)) * 2)
      = 2 * (t * 3 ^ i * 2 ^ (m - (i + 1))) by ring, U_add_two_mul, pow_succ]
    ring

/-! ## Letters and prefixes -/

/-- The `i`-th letter of the `U`-word of `n`: `true` iff `U^i(n)` is odd (digit `1` appended). -/
def uLetter (n i : ℕ) : Bool := decide (U_iter i n % 2 = 1)

/-- The length-`k` prefix of the `U`-word of `n`. -/
def uPrefix (k n : ℕ) : Fin k → Bool := fun i => uLetter n i

/-- Adding a multiple of `2^m` changes no letter before position `m`. -/
theorem uLetter_add_mul_two_pow {i m : ℕ} (hi : i < m) (n t : ℕ) :
    uLetter (n + t * 2 ^ m) i = uLetter n i := by
  unfold uLetter
  rw [U_iter_add_mul_two_pow hi.le]
  obtain ⟨d, hd⟩ : ∃ d, m - i = d + 1 := ⟨m - i - 1, by omega⟩
  rw [hd, pow_succ]
  have : U_iter i n + t * 3 ^ i * (2 ^ d * 2) = U_iter i n + 2 * (t * 3 ^ i * 2 ^ d) := by ring
  rw [this]; simp [Nat.add_mul_mod_self_left]

/-- Adding `2^m` flips letter `m` (`3^m` is odd). -/
theorem uLetter_add_two_pow_self (m n : ℕ) : uLetter (n + 2 ^ m) m = !uLetter n m := by
  unfold uLetter
  have h := U_iter_add_mul_two_pow (le_refl m) n 1
  rw [one_mul, Nat.sub_self, pow_zero, mul_one, one_mul] at h
  rw [h]
  have hodd : 3 ^ m % 2 = 1 := Nat.pow_mod 3 m 2 ▸ by simp
  by_cases hp : U_iter m n % 2 = 1 <;> simp [hp] <;> omega

theorem uPrefix_add_mul_two_pow (k n t : ℕ) : uPrefix k (n + t * 2 ^ k) = uPrefix k n :=
  funext fun i => uLetter_add_mul_two_pow i.isLt n t

/-- Letters before position `k` depend only on `n mod 2^k`. -/
theorem uLetter_mod_two_pow {i k : ℕ} (hi : i < k) (n : ℕ) :
    uLetter (n % 2 ^ k) i = uLetter n i := by
  conv_rhs => rw [← Nat.mod_add_div n (2 ^ k), mul_comm]
  exact (uLetter_add_mul_two_pow hi _ _).symm

theorem uPrefix_mod_two_pow (k n : ℕ) : uPrefix k (n % 2 ^ k) = uPrefix k n :=
  funext fun i => uLetter_mod_two_pow i.isLt n

/-- The length-`k` prefix determines the seed modulo `2^k`. -/
theorem mod_two_pow_eq_of_uPrefix_eq (k : ℕ) {n n' : ℕ} (h : uPrefix k n = uPrefix k n') :
    n % 2 ^ k = n' % 2 ^ k := by
  induction k generalizing n n' with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    have hk : n % 2 ^ k = n' % 2 ^ k :=
      ih (funext fun i => congr_fun h ⟨i, by omega⟩)
    have hlast : uLetter n k = uLetter n' k := congr_fun h ⟨k, by omega⟩
    rw [← uLetter_mod_two_pow (Nat.lt_succ_self k) n,
      ← uLetter_mod_two_pow (Nat.lt_succ_self k) n'] at hlast
    -- `n mod 2^(k+1)` is `n mod 2^k` or `n mod 2^k + 2^k`
    have split : ∀ x : ℕ, x % 2 ^ (k + 1) = x % 2 ^ k ∨ x % 2 ^ (k + 1) = x % 2 ^ k + 2 ^ k := by
      intro x
      rw [pow_succ, Nat.mod_mul]
      have : x / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by norm_num)
      interval_cases (x / 2 ^ k % 2) <;> simp
    rcases split n with hn | hn <;> rcases split n' with hn' | hn'
    · omega
    · rw [hn, hn', hk, uLetter_add_two_pow_self] at hlast; simp at hlast
    · rw [hn, hn', hk, uLetter_add_two_pow_self] at hlast; simp at hlast
    · omega

/-! ## Theorem 1 -/

/-- The prefix map on residues mod `2^k`, over the canonical representative. -/
def uPrefixMod (k : ℕ) (r : ZMod (2 ^ k)) : Fin k → Bool := uPrefix k r.val

/-- **Theorem 1 (exact prefix law).** The length-`k` prefix map `ZMod (2^k) → (Fin k → Bool)` is
a bijection: every coin-toss path of length `k` is the prefix of the `U`-word of exactly one
residue class mod `2^k`.  The `U`-instance of [Mat10] Thm 2.2(ii), Thm 3.1 ([MW84]). -/
@[category research solved, AMS 11 37, ref "Mat10" "MW84", group "evgq17_m0_prefix"]
theorem uPrefix_bijective (k : ℕ) : Function.Bijective (uPrefixMod k) := by
  have : NeZero ((2 : ℕ) ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun r s hrs => ?_, by simp [ZMod.card]⟩
  have hmod := mod_two_pow_eq_of_uPrefix_eq k hrs
  rw [Nat.mod_eq_of_lt (ZMod.val_lt r), Nat.mod_eq_of_lt (ZMod.val_lt s)] at hmod
  exact ZMod.val_injective _ hmod

/-- Theorem 1 as an equivalence `ZMod (2^k) ≃ (Fin k → Bool)`. -/
noncomputable def uPrefixEquiv (k : ℕ) : ZMod (2 ^ k) ≃ (Fin k → Bool) :=
  Equiv.ofBijective (uPrefixMod k) (uPrefix_bijective k)

/-- On one full period `[0, 2^k)`, every set `W` of words is hit exactly `|W|` times. -/
theorem card_filter_range_uPrefix_mem (k : ℕ) (W : Finset (Fin k → Bool)) :
    ((Finset.range (2 ^ k)).filter (uPrefix k · ∈ W)).card = W.card := by
  have : NeZero ((2 : ℕ) ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
  symm
  refine Finset.card_bij (fun w _ => ((uPrefixEquiv k).symm w).val) ?_ ?_ ?_
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨ZMod.val_lt _, ?_⟩
    show uPrefixMod k ((uPrefixEquiv k).symm w) ∈ W
    rw [show uPrefixMod k ((uPrefixEquiv k).symm w) = w from (uPrefixEquiv k).apply_symm_apply w]
    exact hw
  · intro w _ w' _ h
    exact (uPrefixEquiv k).symm.injective (ZMod.val_injective _ h)
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    refine ⟨uPrefixEquiv k (n : ZMod (2 ^ k)), ?_, ?_⟩
    · simpa [uPrefixEquiv, uPrefixMod, ZMod.val_natCast, Nat.mod_eq_of_lt hn.1] using hn.2
    · simp [ZMod.val_natCast, Nat.mod_eq_of_lt hn.1]

/-- **Exact interval counting.** On every interval of length `t·2^k`, every set `W` of
length-`k` words is hit exactly `t·|W|` times. -/
@[category research solved, AMS 11 37, ref "Mat10" "MW84", group "evgq17_m0_prefix"]
theorem card_filter_uPrefix_mem (k a t : ℕ) (W : Finset (Fin k → Bool)) :
    ((Finset.Ico a (a + t * 2 ^ k)).filter (uPrefix k · ∈ W)).card = t * W.card := by
  have hper : Function.Periodic (fun n => uPrefix k n ∈ W) (2 ^ k) := by
    intro n; simpa using congrArg (· ∈ W) (uPrefix_add_mul_two_pow k n 1)
  have hblock : ∀ b, ((Finset.Ico b (b + 2 ^ k)).filter (uPrefix k · ∈ W)).card = W.card := by
    intro b
    rw [Nat.filter_Ico_card_eq_of_periodic _ _ _ hper, Nat.count_eq_card_filter_range]
    exact card_filter_range_uPrefix_mem k W
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show a + (t + 1) * 2 ^ k = (a + t * 2 ^ k) + 2 ^ k by ring,
      ← Finset.Ico_union_Ico_eq_Ico (b := a + t * 2 ^ k) (Nat.le_add_right _ _)
        (Nat.le_add_right _ _), Finset.filter_union,
      Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)), ih, hblock]
    ring

end EVG25.M0
