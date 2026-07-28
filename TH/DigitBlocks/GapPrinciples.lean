/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TH.BakerInterface
import ForMathlib.Data.Nat.BinaryDigits
import Mathlib.Data.Nat.Log

/-!
# Gap principles for the digit-block program: the all-ones lemma and the shared endgame

Infrastructure for the digit-block theorems B1–B3 of [A4+], sitting one level
above `TH/StewartDigits.lean`.  Two exports:

* `gap_bound_ones` — the **all-ones companion** of Stewart's `gap_bound`
  ([A4+] §2.1, Table 1 row 2).  A run of *one* bits in positions `[x, y)` of
  `3^m` forces the *same* inequality as the shipped zero-run lemma,
  `(M − x)·log 2 ≤ C(3,1)·log 3·(M + 1 − y)·max(log 2m, 1)`, `M := ⌊log₂ 3^m⌋`.
  Writing `3^m = (A₁ + 1)·2^y − (2^x − A₂)` with `A₁ = 3^m / 2^y`,
  `A₂ = 3^m mod 2^x` and `B₂ = 2^x − A₂ ∈ [1, 2^x]`, the three-log form
  `Λ = y·log 2 + log(A₁+1) − m·log 3 = log(1 + B₂/3^m) ∈ (0, 2^{x−M}]` is
  Baker–Wüstholz small.  It is *simpler* than the zero-run lemma: no oddness /
  parity input is needed (`B₂ ≥ 1` is automatic), so it holds even at `x = 0`.

* `windowCount_lower_bound` — the **shared pigeonhole endgame** ([A4+] §2.2,
  the `window_hit`/`log_le_sum_digits` scaffold of `StewartDigits`, made
  quantity-agnostic).  For any counting function `Q : ℕ → ℕ` satisfying the
  window bound `⌊log_θ ⌊log₂ 3^m⌋⌋ ≤ Q m` (over the θ-window scheme, for every
  admissible `θ`), one gets `log m/(log log m + C) − 1 ≤ Q m` for all `m ≥ 2`
  with a single effective `C > 0`.  Stewart's digit-sum theorem and the
  transition count B1 are its two instances.

Axiom footprint: std3 + `BakerWustholz.linearForms_logs` ([BW93]) via
`gap_bound_ones`; `windowCount_lower_bound` is std3 (only the hypothesis `Q`
carries any Baker content).

## References

* [Ste80] Stewart, *On the representation of an integer in two different bases*,
  J. reine angew. Math. **319** (1980).  (The zero-run template.)
* [BW93] Baker, Wüstholz, *Logarithmic forms and group varieties*, J. reine
  angew. Math. **442** (1993).  (Via `CITED/BakerWustholz.lean`.)
* [A4+] `plan-A4+.html` (this repository, 2026-07): §2.1 (Table 1), §2.2
  (window pigeonhole), §5.2 (this file).
-/

namespace TH

/-! ## The all-ones gap lemma -/

set_option maxHeartbeats 1600000 in
/-- **The all-ones gap principle** ([A4+] §2.1, Table 1 row 2): a run of *one*
bits in positions `[x, y)` of the binary expansion of `3^m` (with
`x < y ≤ M := ⌊log₂ 3^m⌋`) forces

  `(M − x)·log 2 ≤ C(3,1)·log 3·(M + 1 − y)·max(log 2m, 1)`,

exactly the conclusion of Stewart's zero-run `gap_bound`.  Writing
`3^m = (A₁+1)·2^y − (2^x − A₂)` with `A₁ = 3^m/2^y`, `A₂ = 3^m mod 2^x`,
`B₂ = 2^x − A₂ ∈ [1, 2^x]`, the three-log form
`Λ = y·log 2 + log(A₁+1) − m·log 3 ∈ (0, 2^{x−M}]` is Baker–Wüstholz small.
Unlike the zero-run lemma this needs no parity input (`B₂ ≥ 1` is automatic),
so it is valid down to `x = 0`. -/
lemma gap_bound_ones {m x y : ℕ} (hm : 1 ≤ m) (hxy : x < y)
    (hyM : y ≤ Nat.log 2 (3 ^ m))
    (hgap : ∀ i, x ≤ i → i < y → (3 ^ m).testBit i = true) :
    ((Nat.log 2 (3 ^ m) : ℝ) - x) * Real.log 2
      ≤ BakerWustholz.C 3 1 * Real.log 3
        * ((Nat.log 2 (3 ^ m) : ℝ) + 1 - y) * max (Real.log ((2 * m : ℕ) : ℝ)) 1 := by
  set N : ℕ := 3 ^ m with hNdef
  set M : ℕ := Nat.log 2 N with hMdef
  have hM2m : M ≤ 2 * m := by
    rw [hMdef, hNdef]
    have h : (3 : ℕ) ^ m ≤ 2 ^ (2 * m) := by
      calc (3 : ℕ) ^ m ≤ 4 ^ m := Nat.pow_le_pow_left (by norm_num) m
        _ = 2 ^ (2 * m) := by rw [pow_mul]; norm_num
    calc Nat.log 2 (3 ^ m) ≤ Nat.log 2 (2 ^ (2 * m)) := Nat.log_mono_right h
      _ = 2 * m := Nat.log_pow (by norm_num) _
  set A₁ : ℕ := N / 2 ^ y with hA₁def
  set A₂ : ℕ := N % 2 ^ x with hA₂def
  set B₂ : ℕ := 2 ^ x - A₂ with hB₂def
  set C₁ : ℕ := A₁ + 1 with hC₁def
  have hNpos : 0 < N := by rw [hNdef]; positivity
  have htop : 2 ^ M ≤ N := Nat.pow_log_le_self 2 hNpos.ne'
  have hlt : N < 2 ^ (M + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have h2xy : (2 : ℕ) ^ x ≤ 2 ^ y := Nat.pow_le_pow_right (by norm_num) hxy.le
  have hA₂lt : A₂ < 2 ^ x := Nat.mod_lt _ (by positivity)
  have hB₂pos : 1 ≤ B₂ := by rw [hB₂def]; exact Nat.sub_pos_of_lt hA₂lt
  have hB₂ub : B₂ ≤ 2 ^ x := by rw [hB₂def]; exact Nat.sub_le _ _
  have hR : N % 2 ^ y = A₂ + (2 ^ y - 2 ^ x) := by
    rw [hA₂def]; exact Nat.mod_two_pow_eq_of_testBit_eq_true hxy.le hgap
  have hsum : A₁ * 2 ^ y + (A₂ + (2 ^ y - 2 ^ x)) = N := by
    rw [← hR, hA₁def, mul_comm]; exact Nat.div_add_mod N (2 ^ y)
  -- the integer identity `(A₁+1)·2^y = 3^m + B₂`
  have hkey : C₁ * 2 ^ y = N + B₂ := by
    have hc : C₁ * 2 ^ y = A₁ * 2 ^ y + 2 ^ y := by rw [hC₁def]; ring
    have hnn : A₂ + (2 ^ y - 2 ^ x) + (2 ^ x - A₂) = 2 ^ y := by
      rw [add_right_comm, Nat.add_sub_cancel' hA₂lt.le, Nat.add_sub_cancel' h2xy]
    calc C₁ * 2 ^ y = A₁ * 2 ^ y + 2 ^ y := hc
      _ = A₁ * 2 ^ y + (A₂ + (2 ^ y - 2 ^ x) + (2 ^ x - A₂)) := by rw [hnn]
      _ = A₁ * 2 ^ y + (A₂ + (2 ^ y - 2 ^ x)) + (2 ^ x - A₂) := by ring
      _ = N + (2 ^ x - A₂) := by rw [hsum]
      _ = N + B₂ := by rw [hB₂def]
  have hA₁ub : A₁ < 2 ^ (M + 1 - y) := by
    have h1 : A₁ * 2 ^ y < 2 ^ (M + 1 - y) * 2 ^ y := by
      calc A₁ * 2 ^ y ≤ N := by rw [← hsum]; exact Nat.le_add_right _ _
        _ < 2 ^ (M + 1) := hlt
        _ = 2 ^ (M + 1 - y) * 2 ^ y := by
            rw [← pow_add, Nat.sub_add_cancel (le_trans hyM (Nat.le_succ M))]
    exact lt_of_mul_lt_mul_right h1 (Nat.zero_le _)
  have hC₁pos : 1 ≤ C₁ := by rw [hC₁def]; exact Nat.le_add_left 1 A₁
  have hC₁ub : C₁ ≤ 2 ^ (M + 1 - y) := by rw [hC₁def]; exact hA₁ub
  -- real versions
  have hC₁R : (1 : ℝ) ≤ (C₁ : ℝ) := by exact_mod_cast hC₁pos
  have hB₂R : (1 : ℝ) ≤ (B₂ : ℝ) := by exact_mod_cast hB₂pos
  have hden : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hkeyR : (C₁ : ℝ) * 2 ^ y = (3 : ℝ) ^ m + (B₂ : ℝ) := by
    have h := hkey; rw [hNdef] at h; exact_mod_cast h
  have hCden : (0 : ℝ) < (C₁ : ℝ) * 2 ^ y := by positivity
  have htopR : (2 : ℝ) ^ M ≤ (3 : ℝ) ^ m := by
    have := htop; rw [hNdef] at this; exact_mod_cast this
  have hB₂ubR : (B₂ : ℝ) ≤ (2 : ℝ) ^ x := by exact_mod_cast hB₂ub
  -- the linear form `Λ = log(C₁·2^y / 3^m) ∈ (0, 2^{x−M}]`
  set Λ : ℝ := (y : ℝ) * Real.log 2 + Real.log (C₁ : ℝ) - (m : ℝ) * Real.log 3 with hΛdef
  have hratio : Λ = Real.log ((C₁ : ℝ) * 2 ^ y / (3 : ℝ) ^ m) := by
    rw [Real.log_div hCden.ne' hden.ne',
      Real.log_mul (by linarith : (C₁ : ℝ) ≠ 0) (by positivity),
      Real.log_pow, Real.log_pow, hΛdef]
    ring
  have hgt : (3 : ℝ) ^ m < (C₁ : ℝ) * 2 ^ y := by rw [hkeyR]; linarith
  have hΛpos : 0 < Λ := by
    rw [hratio]; apply Real.log_pos; rw [lt_div_iff₀ hden]; linarith
  have hΛub : Λ ≤ (2 : ℝ) ^ x / 2 ^ M := by
    have h1 : Λ ≤ (C₁ : ℝ) * 2 ^ y / (3 : ℝ) ^ m - 1 := by
      rw [hratio]; exact Real.log_le_sub_one_of_pos (by positivity)
    have h2 : (C₁ : ℝ) * 2 ^ y / (3 : ℝ) ^ m - 1 = (B₂ : ℝ) / (3 : ℝ) ^ m := by
      rw [hkeyR, add_div, div_self hden.ne']; ring
    have h3 : (B₂ : ℝ) / (3 : ℝ) ^ m ≤ (2 : ℝ) ^ x / 2 ^ M := by
      apply div_le_div₀ (by positivity) hB₂ubR (by positivity) htopR
    linarith
  have hlogΛub : Real.log Λ ≤ (x : ℝ) * Real.log 2 - (M : ℝ) * Real.log 2 := by
    calc Real.log Λ ≤ Real.log ((2 : ℝ) ^ x / 2 ^ M) := Real.log_le_log hΛpos hΛub
      _ = (x : ℝ) * Real.log 2 - (M : ℝ) * Real.log 2 := by
          rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  -- Baker–Wüstholz on `α = (3, 2, A₁+1)`, `b = (−m, y, 1)`
  set α : Fin 3 → ℚ := ![3, 2, (((C₁ : ℕ) : ℤ) : ℚ)] with hαdef
  set b : Fin 3 → ℤ := ![-(m : ℤ), (y : ℤ), 1] with hbdef
  have e0 : α 0 = 3 := rfl
  have e1 : α 1 = 2 := rfl
  have e2 : α 2 = (((C₁ : ℕ) : ℤ) : ℚ) := rfl
  have f0 : b 0 = -(m : ℤ) := rfl
  have f1 : b 1 = (y : ℤ) := rfl
  have f2 : b 2 = 1 := rfl
  have hC₁Z : (1 : ℤ) ≤ ((C₁ : ℕ) : ℤ) := by exact_mod_cast hC₁pos
  have hα : ∀ i, α i ≠ 0 := by
    intro i; fin_cases i
    · exact (by norm_num : (3 : ℚ) ≠ 0)
    · exact (by norm_num : (2 : ℚ) ≠ 0)
    · exact Int.cast_ne_zero.mpr (by omega)
  have hbB : ∀ i, (b i).natAbs ≤ 2 * m := by
    intro i; fin_cases i
    · show (-((m : ℕ) : ℤ)).natAbs ≤ 2 * m
      rw [Int.natAbs_neg, Int.natAbs_natCast]; omega
    · show (((y : ℕ) : ℤ)).natAbs ≤ 2 * m
      rw [Int.natAbs_natCast]; omega
    · show ((1 : ℤ)).natAbs ≤ 2 * m
      simp only [Int.natAbs_one]; omega
  have hlog3 : Complex.log (((3 : ℚ) : ℂ)) = ((Real.log 3 : ℝ) : ℂ) := by
    rw [show ((3 : ℚ) : ℂ) = (((3 : ℝ)) : ℂ) by norm_num, ← Complex.ofReal_log (by norm_num)]
  have hlog2 : Complex.log (((2 : ℚ) : ℂ)) = ((Real.log 2 : ℝ) : ℂ) := by
    rw [show ((2 : ℚ) : ℂ) = (((2 : ℝ)) : ℂ) by norm_num, ← Complex.ofReal_log (by norm_num)]
  have hlogC : Complex.log (((((C₁ : ℕ) : ℤ) : ℚ)) : ℂ)
      = ((Real.log ((C₁ : ℕ) : ℝ) : ℝ) : ℂ) := by
    rw [show (((((C₁ : ℕ) : ℤ) : ℚ)) : ℂ) = ((((C₁ : ℕ) : ℝ)) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by positivity)]
  have hsumBW : (∑ i, ((b i : ℂ) * Complex.log ((Rat.castHom ℂ) (α i)))) = ((Λ : ℝ) : ℂ) := by
    rw [Fin.sum_univ_three, e0, e1, e2, f0, f1, f2, eq_ratCast, eq_ratCast, eq_ratCast,
      hlog3, hlog2, hlogC, hΛdef]
    push_cast; ring
  have hΛneC : (∑ i, ((b i : ℂ) * Complex.log ((Rat.castHom ℂ) (α i)))) ≠ 0 := by
    rw [hsumBW]; exact Complex.ofReal_ne_zero.mpr hΛpos.ne'
  have hBW := BakerWustholz.linearForms_logs (n := 3) (by norm_num)
    (Rat.castHom ℂ) α hα b (B := 2 * m) (by omega) hbB hΛneC
  rw [hsumBW, Complex.norm_real, Real.norm_eq_abs, Real.log_abs, Module.finrank_self,
    Nat.cast_one] at hBW
  rw [show (1 : ℝ) / (1 : ℝ) = 1 by norm_num] at hBW
  -- height product `h'(3)·h'(2)·h'(A₁+1) ≤ log 3·1·(M+1−y)`
  have hmhC : BakerWustholz.modifiedHeight (Rat.castHom ℂ) (((C₁ : ℕ) : ℤ) : ℚ)
      ≤ (M : ℝ) + 1 - y := by
    refine le_trans (mh_intCast hC₁Z) ?_
    have hMy1 : (1 : ℝ) ≤ (M : ℝ) + 1 - y := by
      have hyR : (y : ℝ) ≤ (M : ℝ) := by exact_mod_cast hyM
      linarith
    have hlogC₁ : Real.log (((C₁ : ℕ) : ℤ) : ℝ) ≤ (M : ℝ) + 1 - y := by
      have hcast : (((C₁ : ℕ) : ℤ) : ℝ) = ((C₁ : ℕ) : ℝ) := by push_cast; ring
      rw [hcast]
      have hub : ((C₁ : ℕ) : ℝ) ≤ (2 : ℝ) ^ (M + 1 - y) := by exact_mod_cast hC₁ub
      have hMy : ((M + 1 - y : ℕ) : ℝ) = (M : ℝ) + 1 - y := by
        rw [Nat.cast_sub (by omega : y ≤ M + 1)]; push_cast; ring
      calc Real.log ((C₁ : ℕ) : ℝ) ≤ Real.log ((2 : ℝ) ^ (M + 1 - y)) :=
            Real.log_le_log (by linarith) hub
        _ = ((M + 1 - y : ℕ) : ℝ) * Real.log 2 := by rw [Real.log_pow]
        _ ≤ ((M + 1 - y : ℕ) : ℝ) * 1 := by
            exact mul_le_mul_of_nonneg_left log_two_le_one (by positivity)
        _ = (M : ℝ) + 1 - y := by rw [mul_one, hMy]
    exact max_le hlogC₁ hMy1
  have hmhnn : ∀ q : ℚ, 0 ≤ BakerWustholz.modifiedHeight (Rat.castHom ℂ) q := by
    intro q; rw [modifiedHeight_rat]; positivity
  have hprod : (∏ i, BakerWustholz.modifiedHeight (Rat.castHom ℂ) (α i))
      ≤ Real.log 3 * 1 * ((M : ℝ) + 1 - y) := by
    rw [Fin.prod_univ_three, e0, e1, e2]
    have m01 : BakerWustholz.modifiedHeight (Rat.castHom ℂ) 3
        * BakerWustholz.modifiedHeight (Rat.castHom ℂ) 2 ≤ Real.log 3 * 1 :=
      mul_le_mul mh_three mh_two (hmhnn _) log_three_pos'.le
    exact mul_le_mul m01 hmhC (hmhnn _) (mul_nonneg log_three_pos'.le zero_le_one)
  -- combine, exactly as in the zero-run lemma
  have hCmax : 0 ≤ BakerWustholz.C 3 1 * max (Real.log ((2 * m : ℕ) : ℝ)) 1 :=
    mul_nonneg (C_one_nonneg 3) (le_trans zero_le_one (le_max_right _ _))
  have hlower : -(BakerWustholz.C 3 1 * max (Real.log ((2 * m : ℕ) : ℝ)) 1
      * (Real.log 3 * 1 * ((M : ℝ) + 1 - y))) ≤ Real.log Λ := by
    refine le_trans (neg_le_neg ?_) hBW
    exact mul_le_mul_of_nonneg_left hprod hCmax
  have hexpand : ((M : ℝ) - x) * Real.log 2
      = (M : ℝ) * Real.log 2 - (x : ℝ) * Real.log 2 := by ring
  have harr : BakerWustholz.C 3 1 * max (Real.log ((2 * m : ℕ) : ℝ)) 1
      * (Real.log 3 * 1 * ((M : ℝ) + 1 - y))
      = BakerWustholz.C 3 1 * Real.log 3 * ((M : ℝ) + 1 - y)
        * max (Real.log ((2 * m : ℕ) : ℝ)) 1 := by ring
  rw [harr] at hlower
  rw [hexpand]
  linarith

/-! ## Gap principle P: the 4-log lemma for p-periodic windows -/

set_option maxHeartbeats 2000000 in
/-- **Gap principle P** ([A4+] §2.1, Table 1 row 3): a `p`-periodic window
`[x, y)` of the binary expansion of `3^m` (`bitᵢ = bitᵢ₊ₚ` for `x ≤ i < y − p`,
with `2p ≤ y − x` and `x ≥ 1`) forces
`(M − x)·log 2 ≤ C(4,1)·p·log 3·(M + 2p − y)·max(log(2m+p), 1) + (p+1)·log 2`
(`M := ⌊log₂ 3^m⌋`).  Trimming to `y' = x + p⌊(y−x)/p⌋`, the identity
`(2^p − 1)·3^m = A₁'·2^{y'} + E` with `E = (2^p − 1)A₂ − c·2^x` **odd** (the
parity nondegeneracy) yields a **four**-log form
`Λ = log(2^p−1) + m·log 3 − y'·log 2 − log A₁'`, `|Λ| ≤ 2^{x+2−M}`, which
Baker–Wüstholz bounds below (`α = (2^p−1, 3, 2, A₁')`, heights
`h'(2^p−1) ≤ p`, `h'(A₁') ≤ M+1+p−y'`).  The condition `2p ≤ y − x` keeps
`|Λ| ≤ 1/2`, so the two-sided log estimate applies.  Footprint std3 + [BW93]. -/
lemma gap_principle {m x y p : ℕ} (hm : 1 ≤ m) (hp : 1 ≤ p) (hx : 1 ≤ x) (hxy : x < y)
    (hyM : y ≤ Nat.log 2 (3 ^ m)) (h2p : 2 * p ≤ y - x)
    (hper : ∀ i, x ≤ i → i + p < y → (3 ^ m).testBit i = (3 ^ m).testBit (i + p)) :
    ((Nat.log 2 (3 ^ m) : ℝ) - x) * Real.log 2
      ≤ BakerWustholz.C 4 1 * (p : ℝ) * Real.log 3
          * ((Nat.log 2 (3 ^ m) : ℝ) + 2 * p - y)
          * max (Real.log ((2 * m + p : ℕ) : ℝ)) 1
        + (p + 1) * Real.log 2 := by
  set N : ℕ := 3 ^ m with hNdef
  set M : ℕ := Nat.log 2 N with hMdef
  set G : ℕ := 2 ^ p - 1 with hGdef
  set A₂ : ℕ := N % 2 ^ x with hA₂def
  set c : ℕ := N / 2 ^ x % 2 ^ p with hcdef
  set t : ℕ := (y - x) / p with htdef
  set y' : ℕ := x + t * p with hy'def
  set A₁'' : ℕ := N / 2 ^ y' with hA₁''def
  set A₁' : ℕ := G * A₁'' + c with hA₁'def
  have hNpos : 0 < N := by rw [hNdef]; positivity
  have htop : 2 ^ M ≤ N := Nat.pow_log_le_self 2 hNpos.ne'
  have hlt : N < 2 ^ (M + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have hM2m : M ≤ 2 * m := by
    rw [hMdef, hNdef]
    have h : (3 : ℕ) ^ m ≤ 2 ^ (2 * m) := by
      calc (3 : ℕ) ^ m ≤ 4 ^ m := Nat.pow_le_pow_left (by norm_num) m
        _ = 2 ^ (2 * m) := by rw [pow_mul]; norm_num
    calc Nat.log 2 (3 ^ m) ≤ Nat.log 2 (2 ^ (2 * m)) := Nat.log_mono_right h
      _ = 2 * m := Nat.log_pow (by norm_num) _
  -- trimming
  have hty : y' ≤ y := by rw [hy'def, htdef]; have := Nat.div_mul_le_self (y - x) p; omega
  have ht2 : 2 ≤ t := by rw [htdef, Nat.le_div_iff_mul_le (by omega)]; omega
  have hy'x : x < y' := by rw [hy'def]; nlinarith [ht2, hp]
  have hy'M : y' ≤ M := le_trans hty hyM
  have hxM2 : x + 2 ≤ M := by
    have : x + 2 * p ≤ y' := by rw [hy'def]; nlinarith [ht2, hp]
    omega
  have h2xy' : (2 : ℕ) ^ x ≤ 2 ^ y' := Nat.pow_le_pow_right (by norm_num) hy'x.le
  -- G bounds
  have hGpos : 1 ≤ G := by
    rw [hGdef]
    have h2p2 : 2 ≤ 2 ^ p := by
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp
    omega
  have hGodd : G % 2 = 1 := by
    rw [hGdef]; have : 2 ^ p % 2 = 0 := by
      have : (2:ℕ) ∣ 2 ^ p := dvd_pow_self 2 (by omega); omega
    omega
  have hGlt : G < 2 ^ p := by rw [hGdef]; have : 1 ≤ 2 ^ p := Nat.one_le_two_pow; omega
  -- A₂ odd, < 2^x
  have hA₂lt : A₂ < 2 ^ x := Nat.mod_lt _ (by positivity)
  have hA₂odd : A₂ % 2 = 1 := by
    rw [hA₂def, Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega : x ≠ 0)), hNdef, Nat.pow_mod]
    norm_num
  have hclt : c < 2 ^ p := Nat.mod_lt _ (by positivity)
  -- the periodic identity → key integer identity  hID
  have hPMI : G * (N % 2 ^ y') = G * A₂ + c * (2 ^ y' - 2 ^ x) := by
    have := Nat.periodic_mod_identity hper t (by rw [← hy'def]; exact hty)
    rw [← hy'def, ← hA₂def, ← hcdef, ← hGdef] at this; convert this using 2
  have hdm : A₁'' * 2 ^ y' + N % 2 ^ y' = N := by
    rw [hA₁''def, mul_comm]; exact Nat.div_add_mod N (2 ^ y')
  have hID : G * N + c * 2 ^ x = A₁' * 2 ^ y' + G * A₂ := by
    have e1 : G * N = G * (A₁'' * 2 ^ y') + G * (N % 2 ^ y') := by rw [← Nat.mul_add, hdm]
    have e2 : c * (2 ^ y' - 2 ^ x) + c * 2 ^ x = c * 2 ^ y' := by
      rw [← Nat.mul_add, Nat.sub_add_cancel h2xy']
    calc G * N + c * 2 ^ x
        = G * (A₁'' * 2 ^ y') + G * (N % 2 ^ y') + c * 2 ^ x := by rw [e1]
      _ = G * (A₁'' * 2 ^ y') + (G * A₂ + c * (2 ^ y' - 2 ^ x)) + c * 2 ^ x := by rw [hPMI]
      _ = G * (A₁'' * 2 ^ y') + c * 2 ^ y' + G * A₂ := by rw [← e2]; ring
      _ = A₁' * 2 ^ y' + G * A₂ := by rw [hA₁'def]; ring
  -- A₁'' ≥ 2^(M−y'), A₁' bounds
  have hA₁''lb : 2 ^ (M - y') ≤ A₁'' := by
    rw [hA₁''def, ← Nat.pow_div hy'M (by norm_num)]; exact Nat.div_le_div_right htop
  have hA₁''ub : A₁'' < 2 ^ (M + 1 - y') := by
    have h1 : A₁'' * 2 ^ y' < 2 ^ (M + 1 - y') * 2 ^ y' := by
      calc A₁'' * 2 ^ y' ≤ N := by rw [← hdm]; exact Nat.le_add_right _ _
        _ < 2 ^ (M + 1) := hlt
        _ = 2 ^ (M + 1 - y') * 2 ^ y' := by
            rw [← pow_add, Nat.sub_add_cancel (by omega)]
    exact lt_of_mul_lt_mul_right h1 (Nat.zero_le _)
  have hA₁'pos : 1 ≤ A₁' := by rw [hA₁'def]; nlinarith [hGpos, Nat.one_le_two_pow (n := M - y')]
  have hA₁'ub : A₁' < 2 ^ (M + 1 + p - y') := by
    have h1 : A₁' < 2 ^ p * 2 ^ (M + 1 - y') := by
      rw [hA₁'def]
      calc G * A₁'' + c < 2 ^ p * A₁'' + 2 ^ p := by nlinarith [hGlt, hclt, Nat.one_le_two_pow (n := M-y')]
        _ = 2 ^ p * (A₁'' + 1) := by ring
        _ ≤ 2 ^ p * 2 ^ (M + 1 - y') := by
            apply Nat.mul_le_mul_left; omega
    calc A₁' < 2 ^ p * 2 ^ (M + 1 - y') := h1
      _ = 2 ^ (p + (M + 1 - y')) := by rw [pow_add]
      _ = 2 ^ (M + 1 + p - y') := by congr 1; omega
  -- ## real identity and E ≠ 0
  have hIDR : (G : ℝ) * (3 : ℝ) ^ m + (c : ℝ) * 2 ^ x = (A₁' : ℝ) * 2 ^ y' + (G : ℝ) * A₂ := by
    have h := hID; rw [hNdef] at h; exact_mod_cast h
  set Er : ℝ := (G : ℝ) * A₂ - (c : ℝ) * 2 ^ x with hErdef
  have hGN : (G : ℝ) * (3 : ℝ) ^ m = (A₁' : ℝ) * 2 ^ y' + Er := by rw [hErdef]; linarith
  have hEr_ne : Er ≠ 0 := by
    have hodd : Odd ((G : ℤ) * A₂ - (c : ℤ) * 2 ^ x) := by
      have hGZ : Odd (G : ℤ) := by rw [Int.odd_iff]; omega
      have hAZ : Odd (A₂ : ℤ) := by rw [Int.odd_iff]; omega
      have hev : Even ((c : ℤ) * 2 ^ x) := by
        refine (Int.even_mul).mpr (Or.inr ?_)
        rw [Int.even_iff]; have : (2 : ℤ) ∣ 2 ^ x := dvd_pow_self 2 (by omega); omega
      exact (hGZ.mul hAZ).sub_even hev
    have hne : ((G : ℤ) * A₂ - (c : ℤ) * 2 ^ x) ≠ 0 := by
      have := Int.odd_iff.mp hodd; omega
    have hcast : Er = (((G : ℤ) * A₂ - (c : ℤ) * 2 ^ x : ℤ) : ℝ) := by rw [hErdef]; push_cast; ring
    rw [hcast]; exact_mod_cast hne
  -- ## den > 0 and lower bound
  have hA₁'R : (1 : ℝ) ≤ (A₁' : ℝ) := by exact_mod_cast hA₁'pos
  have hden : (0 : ℝ) < (A₁' : ℝ) * 2 ^ y' := by positivity
  have hGR : (1 : ℝ) ≤ (G : ℝ) := by exact_mod_cast hGpos
  have hden_lb : (G : ℝ) * 2 ^ M ≤ (A₁' : ℝ) * 2 ^ y' := by
    have hA₁'lb : (G : ℝ) * 2 ^ (M - y') ≤ (A₁' : ℝ) := by
      have : (G : ℕ) * 2 ^ (M - y') ≤ A₁' := by rw [hA₁'def]; nlinarith [hA₁''lb, Nat.zero_le c]
      exact_mod_cast this
    calc (G : ℝ) * 2 ^ M = (G : ℝ) * 2 ^ (M - y') * 2 ^ y' := by
          rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hy'M]
      _ ≤ (A₁' : ℝ) * 2 ^ y' := by
          apply mul_le_mul_of_nonneg_right hA₁'lb (by positivity)
  -- ## |Er| bound
  have hEr_ub : |Er| ≤ (2 : ℝ) ^ (x + p) := by
    have hGA₂ : (G : ℝ) * A₂ ≤ (2 : ℝ) ^ (x + p) := by
      have h1 : (G : ℝ) * A₂ ≤ (2 : ℝ) ^ p * 2 ^ x := by
        apply mul_le_mul (by exact_mod_cast hGlt.le) (by exact_mod_cast hA₂lt.le)
          (by positivity) (by positivity)
      rw [pow_add]; linarith [h1]
    have hc2x : (c : ℝ) * 2 ^ x ≤ (2 : ℝ) ^ (x + p) := by
      have h1 : (c : ℝ) * 2 ^ x ≤ (2 : ℝ) ^ p * 2 ^ x := by
        apply mul_le_mul (by exact_mod_cast hclt.le) le_rfl (by positivity) (by positivity)
      rw [pow_add]; linarith [h1]
    have hGA₂nn : (0 : ℝ) ≤ (G : ℝ) * A₂ := by positivity
    have hc2xnn : (0 : ℝ) ≤ (c : ℝ) * 2 ^ x := by positivity
    rw [hErdef, abs_le]
    constructor <;> nlinarith [hGA₂, hc2x, hGA₂nn, hc2xnn]
  -- ## the ratio R and |Λ| bound
  set R : ℝ := (G : ℝ) * (3 : ℝ) ^ m / ((A₁' : ℝ) * 2 ^ y') with hRdef
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hRm1 : R - 1 = Er / ((A₁' : ℝ) * 2 ^ y') := by
    rw [hRdef, div_sub_one hden.ne']; congr 1; linarith [hGN]
  have hGpow : (2 : ℝ) ^ (p - 1) ≤ (G : ℝ) := by
    have : (2 : ℕ) ^ (p - 1) ≤ G := by
      rw [hGdef]
      have h1 : 2 ^ (p - 1) + 2 ^ (p - 1) = 2 ^ p := by
        rw [← two_mul, ← pow_succ']; congr 1; omega
      have h2 : 1 ≤ (2:ℕ) ^ (p - 1) := Nat.one_le_two_pow
      omega
    exact_mod_cast this
  have hRm1_abs : |R - 1| ≤ (2 : ℝ) ^ (x + 1) / 2 ^ M := by
    rw [hRm1, abs_div, abs_of_pos hden]
    calc |Er| / ((A₁' : ℝ) * 2 ^ y')
        ≤ (2 : ℝ) ^ (x + p) / ((G : ℝ) * 2 ^ M) :=
          div_le_div₀ (by positivity) hEr_ub (by positivity) hden_lb
      _ ≤ (2 : ℝ) ^ (x + p) / (2 ^ (p - 1) * 2 ^ M) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right hGpow (by positivity)
      _ = (2 : ℝ) ^ (x + 1) / 2 ^ M := by
          rw [← pow_add, show x + p = (x + 1) + (p - 1) by omega, pow_add]; field_simp; ring
  have hhalf : (2 : ℝ) ^ (x + 1) / 2 ^ M ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 ^ M)]
    have h2 : (2 : ℝ) ^ (x + 1) * 2 ≤ 2 ^ M := by
      rw [← pow_succ]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hR_half : |R - 1| ≤ 1 / 2 := le_trans hRm1_abs hhalf
  have hEr_div_ne : Er / ((A₁' : ℝ) * 2 ^ y') ≠ 0 := div_ne_zero hEr_ne hden.ne'
  have hRne1 : R ≠ 1 := by
    intro h; apply hEr_div_ne; rw [← hRm1, h]; ring
  have hΛne : Real.log R ≠ 0 := by
    intro h; apply hRne1; rw [← Real.exp_log hRpos, h, Real.exp_zero]
  -- the linear form Λ = log G + m log 3 − y' log 2 − log A₁' = log R
  set Λ : ℝ := Real.log (G : ℝ) + (m : ℝ) * Real.log 3 - (y' : ℝ) * Real.log 2
      - Real.log (A₁' : ℝ) with hΛdef
  have hratio : Λ = Real.log R := by
    rw [hRdef, Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, hΛdef]
    ring
  -- |Λ| ≤ 2^(x+2)/2^M, so log|Λ| ≤ (x+2−M) log 2
  have habs_log : |Real.log R| ≤ 2 * |R - 1| := by
    have hRhalf : (1 : ℝ) / 2 ≤ R := by rw [abs_le] at hR_half; linarith [hR_half.1]
    by_cases hR1 : 1 ≤ R
    · rw [abs_of_nonneg (Real.log_nonneg hR1), abs_of_nonneg (by linarith : (0:ℝ) ≤ R - 1)]
      linarith [Real.log_le_sub_one_of_pos hRpos]
    · have hR1' : R < 1 := not_le.mp hR1
      rw [abs_of_neg (Real.log_neg hRpos hR1'), abs_of_neg (by linarith : R - 1 < 0)]
      have hle : Real.log R⁻¹ ≤ R⁻¹ - 1 := Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_inv] at hle
      have hkey : R⁻¹ - 1 ≤ 2 * (1 - R) := by
        rw [inv_eq_one_div, div_sub_one hRpos.ne', div_le_iff₀ hRpos]
        nlinarith [hRhalf]
      linarith
  have hΛabs_ub : |Λ| ≤ (2 : ℝ) ^ (x + 2) / 2 ^ M := by
    rw [hratio]
    calc |Real.log R| ≤ 2 * |R - 1| := habs_log
      _ ≤ 2 * ((2 : ℝ) ^ (x + 1) / 2 ^ M) := by linarith [hRm1_abs]
      _ = (2 : ℝ) ^ (x + 2) / 2 ^ M := by rw [pow_succ]; ring
  have hΛpos_abs : 0 < |Λ| := abs_pos.mpr (by rw [hratio]; exact hΛne)
  have hlogΛ_ub : Real.log |Λ| ≤ ((x : ℝ) + 2 - M) * Real.log 2 := by
    calc Real.log |Λ| ≤ Real.log ((2 : ℝ) ^ (x + 2) / 2 ^ M) :=
          Real.log_le_log hΛpos_abs hΛabs_ub
      _ = ((x : ℝ) + 2 - M) * Real.log 2 := by
          rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
          push_cast; ring
  -- ## Baker–Wüstholz on α = (G, 3, 2, A₁'), b = (1, m, −y', −1)
  set α : Fin 4 → ℚ := ![(((G : ℕ) : ℤ) : ℚ), 3, 2, (((A₁' : ℕ) : ℤ) : ℚ)] with hαdef
  set bb : Fin 4 → ℤ := ![1, (m : ℤ), -(y' : ℤ), -1] with hbbdef
  have e0 : α 0 = (((G : ℕ) : ℤ) : ℚ) := rfl
  have e1 : α 1 = 3 := rfl
  have e2 : α 2 = 2 := rfl
  have e3 : α 3 = (((A₁' : ℕ) : ℤ) : ℚ) := rfl
  have f0 : bb 0 = 1 := rfl
  have f1 : bb 1 = (m : ℤ) := rfl
  have f2 : bb 2 = -(y' : ℤ) := rfl
  have f3 : bb 3 = -1 := rfl
  have hGZ : (1 : ℤ) ≤ ((G : ℕ) : ℤ) := by exact_mod_cast hGpos
  have hA₁'Z : (1 : ℤ) ≤ ((A₁' : ℕ) : ℤ) := by exact_mod_cast hA₁'pos
  have hGQ : (((G : ℕ) : ℤ) : ℚ) ≠ 0 := by
    have : G ≠ 0 := by omega
    exact_mod_cast this
  have hA₁'Q : (((A₁' : ℕ) : ℤ) : ℚ) ≠ 0 := by
    have : A₁' ≠ 0 := by omega
    exact_mod_cast this
  have hα : ∀ i, α i ≠ 0 := by
    intro i; fin_cases i
    · exact hGQ
    · exact (by norm_num : (3 : ℚ) ≠ 0)
    · exact (by norm_num : (2 : ℚ) ≠ 0)
    · exact hA₁'Q
  have hbB : ∀ i, (bb i).natAbs ≤ 2 * m + p := by
    intro i; fin_cases i
    · show ((1 : ℤ)).natAbs ≤ 2 * m + p; simp only [Int.natAbs_one]; omega
    · show ((m : ℤ)).natAbs ≤ 2 * m + p; rw [Int.natAbs_natCast]; omega
    · show (-(y' : ℤ)).natAbs ≤ 2 * m + p; rw [Int.natAbs_neg, Int.natAbs_natCast]; omega
    · show ((-1 : ℤ)).natAbs ≤ 2 * m + p; simp only [Int.natAbs_neg, Int.natAbs_one]; omega
  have hlogG : Complex.log ((((G : ℕ) : ℤ) : ℚ) : ℂ) = ((Real.log (G : ℝ) : ℝ) : ℂ) := by
    rw [show (((((G : ℕ) : ℤ) : ℚ)) : ℂ) = ((((G : ℕ) : ℝ)) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by positivity)]
  have hlog3 : Complex.log (((3 : ℚ) : ℂ)) = ((Real.log 3 : ℝ) : ℂ) := by
    rw [show ((3 : ℚ) : ℂ) = (((3 : ℝ)) : ℂ) by norm_num, ← Complex.ofReal_log (by norm_num)]
  have hlog2 : Complex.log (((2 : ℚ) : ℂ)) = ((Real.log 2 : ℝ) : ℂ) := by
    rw [show ((2 : ℚ) : ℂ) = (((2 : ℝ)) : ℂ) by norm_num, ← Complex.ofReal_log (by norm_num)]
  have hlogA : Complex.log ((((A₁' : ℕ) : ℤ) : ℚ) : ℂ) = ((Real.log (A₁' : ℝ) : ℝ) : ℂ) := by
    rw [show (((((A₁' : ℕ) : ℤ) : ℚ)) : ℂ) = ((((A₁' : ℕ) : ℝ)) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by positivity)]
  have hsumBW : (∑ i, ((bb i : ℂ) * Complex.log ((Rat.castHom ℂ) (α i)))) = ((Λ : ℝ) : ℂ) := by
    rw [Fin.sum_univ_four, e0, e1, e2, e3, f0, f1, f2, f3,
      eq_ratCast, eq_ratCast, eq_ratCast, eq_ratCast, hlogG, hlog3, hlog2, hlogA, hΛdef]
    push_cast; ring
  have hΛne0 : Λ ≠ 0 := by rw [hratio]; exact hΛne
  have hΛneC : (∑ i, ((bb i : ℂ) * Complex.log ((Rat.castHom ℂ) (α i)))) ≠ 0 := by
    rw [hsumBW]; exact Complex.ofReal_ne_zero.mpr hΛne0
  have hBW := BakerWustholz.linearForms_logs (n := 4) (by norm_num)
    (Rat.castHom ℂ) α hα bb (B := 2 * m + p) (by omega) hbB hΛneC
  rw [hsumBW, Complex.norm_real, Real.norm_eq_abs, Real.log_abs, Module.finrank_self,
    Nat.cast_one] at hBW
  rw [show (1 : ℝ) / (1 : ℝ) = 1 by norm_num] at hBW
  -- ## height product
  have hmhnn : ∀ q : ℚ, 0 ≤ BakerWustholz.modifiedHeight (Rat.castHom ℂ) q := by
    intro q; rw [modifiedHeight_rat]; positivity
  have hmhG : BakerWustholz.modifiedHeight (Rat.castHom ℂ) (((G : ℕ) : ℤ) : ℚ) ≤ (p : ℝ) := by
    refine le_trans (mh_intCast hGZ) ?_
    have hlogGp : Real.log (((G : ℕ) : ℤ) : ℝ) ≤ (p : ℝ) := by
      have hcast : (((G : ℕ) : ℤ) : ℝ) = ((G : ℕ) : ℝ) := by push_cast; ring
      rw [hcast]
      have hGub : ((G : ℕ) : ℝ) ≤ (2 : ℝ) ^ p := by exact_mod_cast hGlt.le
      calc Real.log ((G : ℕ) : ℝ) ≤ Real.log ((2 : ℝ) ^ p) := Real.log_le_log (by positivity) hGub
        _ = (p : ℝ) * Real.log 2 := by rw [Real.log_pow]
        _ ≤ (p : ℝ) * 1 := by exact mul_le_mul_of_nonneg_left log_two_le_one (by positivity)
        _ = (p : ℝ) := mul_one _
    exact max_le hlogGp (by exact_mod_cast hp)
  have hmhA : BakerWustholz.modifiedHeight (Rat.castHom ℂ) (((A₁' : ℕ) : ℤ) : ℚ)
      ≤ (M : ℝ) + 1 + p - y' := by
    refine le_trans (mh_intCast hA₁'Z) ?_
    have hMy1 : (1 : ℝ) ≤ (M : ℝ) + 1 + p - y' := by
      have hy'R : (y' : ℝ) ≤ (M : ℝ) := by exact_mod_cast hy'M
      have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      linarith
    have hlogA₁ : Real.log (((A₁' : ℕ) : ℤ) : ℝ) ≤ (M : ℝ) + 1 + p - y' := by
      have hcast : (((A₁' : ℕ) : ℤ) : ℝ) = ((A₁' : ℕ) : ℝ) := by push_cast; ring
      rw [hcast]
      have hub : ((A₁' : ℕ) : ℝ) ≤ (2 : ℝ) ^ (M + 1 + p - y') := by exact_mod_cast hA₁'ub.le
      have hMy : ((M + 1 + p - y' : ℕ) : ℝ) = (M : ℝ) + 1 + p - y' := by
        rw [Nat.cast_sub (by omega : y' ≤ M + 1 + p)]; push_cast; ring
      calc Real.log ((A₁' : ℕ) : ℝ) ≤ Real.log ((2 : ℝ) ^ (M + 1 + p - y')) :=
            Real.log_le_log (by positivity) hub
        _ = ((M + 1 + p - y' : ℕ) : ℝ) * Real.log 2 := by rw [Real.log_pow]
        _ ≤ ((M + 1 + p - y' : ℕ) : ℝ) * 1 := by
            exact mul_le_mul_of_nonneg_left log_two_le_one (by positivity)
        _ = (M : ℝ) + 1 + p - y' := by rw [mul_one, hMy]
    exact max_le hlogA₁ hMy1
  have hprod : (∏ i, BakerWustholz.modifiedHeight (Rat.castHom ℂ) (α i))
      ≤ (p : ℝ) * Real.log 3 * 1 * ((M : ℝ) + 1 + p - y') := by
    rw [Fin.prod_univ_four, e0, e1, e2, e3]
    have hp01 : BakerWustholz.modifiedHeight (Rat.castHom ℂ) (((G : ℕ) : ℤ) : ℚ)
        * BakerWustholz.modifiedHeight (Rat.castHom ℂ) 3 ≤ (p : ℝ) * Real.log 3 :=
      mul_le_mul hmhG mh_three (hmhnn _) (by positivity)
    have hp012 : BakerWustholz.modifiedHeight (Rat.castHom ℂ) (((G : ℕ) : ℤ) : ℚ)
        * BakerWustholz.modifiedHeight (Rat.castHom ℂ) 3
        * BakerWustholz.modifiedHeight (Rat.castHom ℂ) 2 ≤ (p : ℝ) * Real.log 3 * 1 :=
      mul_le_mul hp01 mh_two (hmhnn _)
        (mul_nonneg (Nat.cast_nonneg p) log_three_pos'.le)
    exact mul_le_mul hp012 hmhA (hmhnn _)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg p) log_three_pos'.le) zero_le_one)
  -- ## combine
  have hCmax : 0 ≤ BakerWustholz.C 4 1 * max (Real.log ((2 * m + p : ℕ) : ℝ)) 1 :=
    mul_nonneg (C_one_nonneg 4) (le_trans zero_le_one (le_max_right _ _))
  have hlower : -(BakerWustholz.C 4 1 * max (Real.log ((2 * m + p : ℕ) : ℝ)) 1
      * ((p : ℝ) * Real.log 3 * 1 * ((M : ℝ) + 1 + p - y'))) ≤ Real.log Λ := by
    refine le_trans (neg_le_neg ?_) hBW
    exact mul_le_mul_of_nonneg_left hprod hCmax
  have hbridge : Real.log Λ = Real.log |Λ| := (Real.log_abs Λ).symm
  rw [hbridge] at hlower
  -- rearrange: (M − x) log 2 ≤ C·p·log3·(M+1+p−y')·max + (p+1)·log2
  have hp1 : (2 : ℝ) * Real.log 2 ≤ ((p : ℝ) + 1) * Real.log 2 := by
    have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    nlinarith [log_two_pos']
  have hgoalarr : BakerWustholz.C 4 1 * max (Real.log ((2 * m + p : ℕ) : ℝ)) 1
      * ((p : ℝ) * Real.log 3 * 1 * ((M : ℝ) + 1 + p - y'))
      = BakerWustholz.C 4 1 * (p : ℝ) * Real.log 3 * ((M : ℝ) + 1 + p - y')
        * max (Real.log ((2 * m + p : ℕ) : ℝ)) 1 := by ring
  rw [hgoalarr] at hlower
  -- bound the trimmed height factor (M+1+p−y') ≤ (M+2p−y)
  have hyeq : y' + (y - x) % p = y := by
    have hdm2 : (y - x) / p * p + (y - x) % p = y - x := Nat.div_add_mod' (y - x) p
    rw [hy'def, htdef]; omega
  have hfac : (M : ℝ) + 1 + p - y' ≤ (M : ℝ) + 2 * p - y := by
    have hmodR : (((y - x) % p : ℕ) : ℝ) ≤ (p : ℝ) - 1 := by
      have h1 : (y - x) % p + 1 ≤ p := Nat.mod_lt (y - x) (by omega)
      have : (((y - x) % p : ℕ) : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast h1
      linarith
    have hyeqR : (y' : ℝ) + (((y - x) % p : ℕ) : ℝ) = (y : ℝ) := by exact_mod_cast hyeq
    linarith
  have hprodle : BakerWustholz.C 4 1 * (p : ℝ) * Real.log 3 * ((M : ℝ) + 1 + p - y')
        * max (Real.log ((2 * m + p : ℕ) : ℝ)) 1
      ≤ BakerWustholz.C 4 1 * (p : ℝ) * Real.log 3 * ((M : ℝ) + 2 * p - y)
        * max (Real.log ((2 * m + p : ℕ) : ℝ)) 1 := by
    apply mul_le_mul_of_nonneg_right _ (le_trans zero_le_one (le_max_right _ _))
    apply mul_le_mul_of_nonneg_left hfac
    exact mul_nonneg (mul_nonneg (C_one_nonneg 4) (Nat.cast_nonneg p)) log_three_pos'.le
  have hid : ((M : ℝ) - x) * Real.log 2
      = 2 * Real.log 2 - ((x : ℝ) + 2 - M) * Real.log 2 := by ring
  linarith [hlogΛ_ub, hlower, hp1, hid, hprodle]


/-! ## The shared pigeonhole endgame -/

/-- **The window-count lower bound** ([A4+] §2.2, the quantity-agnostic form of
Stewart's `stewart_digitSum_three_pow` endgame): if a counting function
`Q : ℕ → ℕ` is bounded below by the number `⌊log_θ ⌊log₂ 3^m⌋⌋` of θ-windows —
for *every* admissible window size `θ` (those clearing the gap-principle
threshold) — then

  `log m / (log log m + C) − 1 ≤ Q m`   for all `m ≥ 2`,

with a single effective `C = max(log((4·C(3,1)·log 3 + 4)/log 2), 1) > 0`.
Instantiating `Q m = s₂(3^m)` (with `log_le_sum_digits`) gives Stewart's
theorem; `Q m = transitionCount (3^m)` gives B1.  Footprint std3 (all Baker
content is quarantined in the hypothesis `hQ`). -/
lemma windowCount_lower_bound (Q : ℕ → ℕ)
    (hQ : ∀ m θ : ℕ, 2 ≤ m → 2 ≤ θ →
      2 * (BakerWustholz.C 3 1 * Real.log 3 * max (Real.log ((2 * m : ℕ) : ℝ)) 1)
        < (θ : ℝ) * Real.log 2 →
      Nat.log θ (Nat.log 2 (3 ^ m)) ≤ Q m) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 2 ≤ m →
      Real.log m / (Real.log (Real.log m) + C) - 1 ≤ (Q m : ℝ) := by
  have hCl3 : (0 : ℝ) ≤ BakerWustholz.C 3 1 * Real.log 3 :=
    mul_nonneg (C_one_nonneg 3) log_three_pos'.le
  set c₈ : ℝ := (4 * (BakerWustholz.C 3 1 * Real.log 3) + 4) / Real.log 2 with hc₈def
  have hc₈pos : 0 < c₈ := by
    rw [hc₈def]; exact div_pos (by linarith) log_two_pos'
  refine ⟨max (Real.log c₈) 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro m hm
  have hm2R : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlogm_pos : 0 < Real.log m := Real.log_pos (by linarith)
  set L : ℝ := max (Real.log ((2 * m : ℕ) : ℝ)) 1 with hLdef
  have hL1 : 1 ≤ L := le_max_right _ _
  have hCl3L : 0 ≤ BakerWustholz.C 3 1 * Real.log 3 * L :=
    mul_nonneg hCl3 (le_trans zero_le_one hL1)
  set T : ℝ := 2 * (BakerWustholz.C 3 1 * Real.log 3 * L) with hTdef
  have hTnn : 0 ≤ T := by rw [hTdef]; linarith
  set θ : ℕ := ⌊T / Real.log 2⌋₊ + 2 with hθdef
  have hθ2 : 2 ≤ θ := by rw [hθdef]; omega
  have hθval : ((θ : ℕ) : ℝ) = ((⌊T / Real.log 2⌋₊ : ℕ) : ℝ) + 2 := by
    rw [hθdef]; push_cast; ring
  have hθbig : T < (θ : ℝ) * Real.log 2 := by
    have h1 : T / Real.log 2 < ((⌊T / Real.log 2⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [div_lt_iff₀ log_two_pos'] at h1
    rw [hθval]; nlinarith [log_two_pos']
  have hl2m : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) hm2R
  have hlog2m : Real.log ((2 * m : ℕ) : ℝ) ≤ 2 * Real.log m := by
    have hcast : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
    rw [hcast, Real.log_mul (by norm_num) (by linarith)]
    linarith
  have hL2 : L ≤ 2 * Real.log m := by
    rw [hLdef]; refine max_le hlog2m ?_
    nlinarith [Real.log_two_gt_d9]
  have hT4 : T ≤ 4 * (BakerWustholz.C 3 1 * Real.log 3) * Real.log m := by
    rw [hTdef]; nlinarith [hCl3, hL2, hL1]
  have hθle : (θ : ℝ) ≤ c₈ * Real.log m := by
    have hfloor : ((⌊T / Real.log 2⌋₊ : ℕ) : ℝ) ≤ T / Real.log 2 :=
      Nat.floor_le (by positivity)
    have hmul : T + 2 * Real.log 2
        ≤ (4 * (BakerWustholz.C 3 1 * Real.log 3) + 4) * Real.log m := by
      linarith
    have hgoal : T / Real.log 2 + 2 ≤ c₈ * Real.log m := by
      rw [hc₈def, div_mul_eq_mul_div, le_div_iff₀ log_two_pos', add_mul,
        div_mul_cancel₀ _ log_two_pos'.ne']
      exact hmul
    rw [hθval]; linarith
  have hθbig' : 2 * (BakerWustholz.C 3 1 * Real.log 3
      * max (Real.log ((2 * m : ℕ) : ℝ)) 1) < (θ : ℝ) * Real.log 2 := by
    rw [hTdef, hLdef] at hθbig; exact hθbig
  have hk : Nat.log θ (Nat.log 2 (3 ^ m)) ≤ Q m := hQ m θ hm hθ2 hθbig'
  have hlogθ_pos : 0 < Real.log θ := Real.log_pos (by exact_mod_cast (by omega : 1 < θ))
  have hmM : (m : ℝ) ≤ (Nat.log 2 (3 ^ m) : ℝ) := by
    have h : m ≤ Nat.log 2 (3 ^ m) := by
      have hp : (2 : ℕ) ^ m ≤ 3 ^ m := Nat.pow_le_pow_left (by norm_num) m
      calc m = Nat.log 2 (2 ^ m) := (Nat.log_pow (by norm_num) m).symm
        _ ≤ Nat.log 2 (3 ^ m) := Nat.log_mono_right hp
    exact_mod_cast h
  have hMk : (Nat.log 2 (3 ^ m) : ℝ)
      < ((θ : ℕ) : ℝ) ^ (Nat.log θ (Nat.log 2 (3 ^ m)) + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by omega : 1 < θ) (Nat.log 2 (3 ^ m))
  have hlogm_le : Real.log m
      ≤ ((Nat.log θ (Nat.log 2 (3 ^ m)) : ℝ) + 1) * Real.log θ := by
    calc Real.log m ≤ Real.log (Nat.log 2 (3 ^ m) : ℝ) :=
          Real.log_le_log (by linarith) hmM
      _ ≤ Real.log (((θ : ℕ) : ℝ) ^ (Nat.log θ (Nat.log 2 (3 ^ m)) + 1)) :=
          Real.log_le_log (by linarith) hMk.le
      _ = ((Nat.log θ (Nat.log 2 (3 ^ m)) + 1 : ℕ) : ℝ) * Real.log θ := by
          rw [Real.log_pow]
      _ = ((Nat.log θ (Nat.log 2 (3 ^ m)) : ℝ) + 1) * Real.log θ := by push_cast; ring
  have hlogθ_le : Real.log θ ≤ Real.log (Real.log m) + max (Real.log c₈) 1 := by
    have h1 : Real.log ((θ : ℕ) : ℝ) ≤ Real.log (c₈ * Real.log m) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < θ)) hθle
    rw [Real.log_mul hc₈pos.ne' hlogm_pos.ne'] at h1
    have h2 : Real.log c₈ ≤ max (Real.log c₈) 1 := le_max_left _ _
    linarith
  have hinv_le : (Real.log 2)⁻¹ ≤ 1.45 := by
    have hcancel : Real.log 2 * (Real.log 2)⁻¹ = 1 := mul_inv_cancel₀ log_two_pos'.ne'
    nlinarith [Real.log_two_gt_d9, inv_nonneg.mpr log_two_pos'.le]
  have hloglog2 : (-1 : ℝ) < Real.log (Real.log 2) := by
    have h1 : Real.log (Real.log 2)⁻¹ ≤ (Real.log 2)⁻¹ - 1 :=
      Real.log_le_sub_one_of_pos (inv_pos.mpr log_two_pos')
    rw [Real.log_inv] at h1; linarith
  have hloglogm : Real.log (Real.log 2) ≤ Real.log (Real.log m) :=
    Real.log_le_log log_two_pos' hl2m
  have hden_pos : 0 < Real.log (Real.log m) + max (Real.log c₈) 1 := by
    have h1 : (1 : ℝ) ≤ max (Real.log c₈) 1 := le_max_right _ _
    linarith
  have hk1nn : (0 : ℝ) ≤ (Nat.log θ (Nat.log 2 (3 ^ m)) : ℝ) + 1 := by positivity
  have hstep : Real.log m ≤ ((Nat.log θ (Nat.log 2 (3 ^ m)) : ℝ) + 1)
      * (Real.log (Real.log m) + max (Real.log c₈) 1) :=
    le_trans hlogm_le (mul_le_mul_of_nonneg_left hlogθ_le hk1nn)
  have hfrac : Real.log m / (Real.log (Real.log m) + max (Real.log c₈) 1)
      ≤ (Nat.log θ (Nat.log 2 (3 ^ m)) : ℝ) + 1 := by
    rw [div_le_iff₀ hden_pos]; exact hstep
  have hkR : ((Nat.log θ (Nat.log 2 (3 ^ m)) : ℕ) : ℝ) ≤ (Q m : ℝ) := by exact_mod_cast hk
  linarith

/-- **The window-count lower bound, generalized threshold** — the `p`-scaled
variant of `windowCount_lower_bound` for gap principle P.  If `Q` is bounded
below by the θ-window count `⌊log_θ ⌊log₂ 3^m⌋⌋` whenever `κ·log m < θ·log 2`,
then `log m/(log log m + C) − 1 ≤ Q m` for all `m ≥ 2`, with
`C = max(log((κ+2)/log 2), 1)`.  For B2 the coefficient `κ` grows like `p²·log p`,
giving the `C(1 + log p)` constant of the plan.  Footprint std3. -/
lemma windowCount_lower_bound_gen (Q : ℕ → ℕ) (κ : ℝ) (hκ : 0 < κ)
    (hQ : ∀ m θ : ℕ, 2 ≤ m → 2 ≤ θ → κ * Real.log m < (θ : ℝ) * Real.log 2 →
      Nat.log θ (Nat.log 2 (3 ^ m)) ≤ Q m) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 2 ≤ m →
      Real.log m / (Real.log (Real.log m) + C) - 1 ≤ (Q m : ℝ) := by
  set c : ℝ := (κ + 2) / Real.log 2 with hcdef
  have hcpos : 0 < c := by rw [hcdef]; exact div_pos (by linarith) log_two_pos'
  refine ⟨max (Real.log c) 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro m hm
  have hm2R : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlogm_pos : 0 < Real.log m := Real.log_pos (by linarith)
  have hl2m : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) hm2R
  set T : ℝ := κ * Real.log m with hTdef
  have hTnn : 0 ≤ T := by rw [hTdef]; positivity
  set θ : ℕ := ⌊T / Real.log 2⌋₊ + 2 with hθdef
  have hθ2 : 2 ≤ θ := by omega
  have hθval : ((θ : ℕ) : ℝ) = ((⌊T / Real.log 2⌋₊ : ℕ) : ℝ) + 2 := by
    rw [hθdef]; push_cast; ring
  have hθbig : T < (θ : ℝ) * Real.log 2 := by
    have h1 : T / Real.log 2 < ((⌊T / Real.log 2⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [div_lt_iff₀ log_two_pos'] at h1
    rw [hθval]; nlinarith [log_two_pos']
  have hθbig' : κ * Real.log m < (θ : ℝ) * Real.log 2 := by rw [hTdef] at hθbig; exact hθbig
  have hk : Nat.log θ (Nat.log 2 (3 ^ m)) ≤ Q m := hQ m θ hm hθ2 hθbig'
  -- θ ≤ c · log m
  have hθle : (θ : ℝ) ≤ c * Real.log m := by
    have hfloor : ((⌊T / Real.log 2⌋₊ : ℕ) : ℝ) ≤ T / Real.log 2 := Nat.floor_le (by positivity)
    have hclm : c * Real.log m = T / Real.log 2 + 2 * Real.log m / Real.log 2 := by
      rw [hcdef, hTdef]; field_simp
    have h2le : (2 : ℝ) ≤ 2 * Real.log m / Real.log 2 := by
      rw [le_div_iff₀ log_two_pos']; linarith
    rw [hθval]; rw [hclm]; linarith
  -- log arithmetic (identical to windowCount_lower_bound)
  have hlogθ_pos : 0 < Real.log θ := Real.log_pos (by exact_mod_cast (by omega : 1 < θ))
  have hmM : (m : ℝ) ≤ (Nat.log 2 (3 ^ m) : ℝ) := by
    have h : m ≤ Nat.log 2 (3 ^ m) := by
      have hp : (2 : ℕ) ^ m ≤ 3 ^ m := Nat.pow_le_pow_left (by norm_num) m
      calc m = Nat.log 2 (2 ^ m) := (Nat.log_pow (by norm_num) m).symm
        _ ≤ Nat.log 2 (3 ^ m) := Nat.log_mono_right hp
    exact_mod_cast h
  have hMk : (Nat.log 2 (3 ^ m) : ℝ)
      < ((θ : ℕ) : ℝ) ^ (Nat.log θ (Nat.log 2 (3 ^ m)) + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by omega : 1 < θ) (Nat.log 2 (3 ^ m))
  have hlogm_le : Real.log m
      ≤ ((Nat.log θ (Nat.log 2 (3 ^ m)) : ℝ) + 1) * Real.log θ := by
    calc Real.log m ≤ Real.log (Nat.log 2 (3 ^ m) : ℝ) :=
          Real.log_le_log (by linarith) hmM
      _ ≤ Real.log (((θ : ℕ) : ℝ) ^ (Nat.log θ (Nat.log 2 (3 ^ m)) + 1)) :=
          Real.log_le_log (by linarith) hMk.le
      _ = ((Nat.log θ (Nat.log 2 (3 ^ m)) + 1 : ℕ) : ℝ) * Real.log θ := by rw [Real.log_pow]
      _ = ((Nat.log θ (Nat.log 2 (3 ^ m)) : ℝ) + 1) * Real.log θ := by push_cast; ring
  have hlogθ_le : Real.log θ ≤ Real.log (Real.log m) + max (Real.log c) 1 := by
    have h1 : Real.log ((θ : ℕ) : ℝ) ≤ Real.log (c * Real.log m) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < θ)) hθle
    rw [Real.log_mul hcpos.ne' hlogm_pos.ne'] at h1
    linarith [le_max_left (Real.log c) 1]
  have hloglog2 : (-1 : ℝ) < Real.log (Real.log 2) := by
    have h1 : Real.log (Real.log 2)⁻¹ ≤ (Real.log 2)⁻¹ - 1 :=
      Real.log_le_sub_one_of_pos (inv_pos.mpr log_two_pos')
    rw [Real.log_inv] at h1
    nlinarith [Real.log_two_gt_d9, inv_nonneg.mpr log_two_pos'.le,
      mul_inv_cancel₀ log_two_pos'.ne']
  have hloglogm : Real.log (Real.log 2) ≤ Real.log (Real.log m) :=
    Real.log_le_log log_two_pos' hl2m
  have hden_pos : 0 < Real.log (Real.log m) + max (Real.log c) 1 := by
    have h1 : (1 : ℝ) ≤ max (Real.log c) 1 := le_max_right _ _
    linarith
  have hk1nn : (0 : ℝ) ≤ (Nat.log θ (Nat.log 2 (3 ^ m)) : ℝ) + 1 := by positivity
  have hstep : Real.log m ≤ ((Nat.log θ (Nat.log 2 (3 ^ m)) : ℝ) + 1)
      * (Real.log (Real.log m) + max (Real.log c) 1) :=
    le_trans hlogm_le (mul_le_mul_of_nonneg_left hlogθ_le hk1nn)
  have hfrac : Real.log m / (Real.log (Real.log m) + max (Real.log c) 1)
      ≤ (Nat.log θ (Nat.log 2 (3 ^ m)) : ℝ) + 1 := by
    rw [div_le_iff₀ hden_pos]; exact hstep
  have hkR : ((Nat.log θ (Nat.log 2 (3 ^ m)) : ℕ) : ℝ) ≤ (Q m : ℝ) := by exact_mod_cast hk
  linarith


/-- **From the effective lower bound to `→ ∞`** (the quantity-agnostic form of
Stewart's `digitSum_three_pow_tendsto_atTop`): any counting function `Q` obeying
`log m/(log log m + C) − 1 ≤ Q m` beyond `m ≥ 2` tends to infinity, since the
left side does (`log m` beats `log log m`).  Footprint std3. -/
lemma tendsto_atTop_of_lower_bound (Q : ℕ → ℕ)
    (h : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 2 ≤ m →
      Real.log m / (Real.log (Real.log m) + C) - 1 ≤ (Q m : ℝ)) :
    Filter.Tendsto (fun m : ℕ => Q m) Filter.atTop Filter.atTop := by
  obtain ⟨C, hC, hbound⟩ := h
  rw [Filter.tendsto_atTop_atTop]
  intro bd
  refine ⟨max 2 (⌈Real.exp (((bd + 1 : ℝ) * (2 + C)) ^ 2)⌉₊ + 1), fun m hm => ?_⟩
  set t : ℝ := ((bd + 1 : ℝ) * (2 + C)) ^ 2 with htdef
  have hm2 : 2 ≤ m := le_trans (le_max_left _ _) hm
  have hfm := hbound m hm2
  have hmt : Real.exp t ≤ (m : ℝ) := by
    have h1 : ⌈Real.exp t⌉₊ + 1 ≤ m := le_trans (le_max_right _ _) hm
    calc Real.exp t ≤ (⌈Real.exp t⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (m : ℝ) := by exact_mod_cast Nat.le_of_succ_le h1
  have hbd1 : (1 : ℝ) ≤ (bd : ℝ) + 1 := by
    have h0 : (0 : ℝ) ≤ (bd : ℝ) := Nat.cast_nonneg bd
    linarith
  have h2C : (2 : ℝ) ≤ 2 + C := by linarith
  have hP2 : (2 : ℝ) ≤ (bd + 1 : ℝ) * (2 + C) := by nlinarith [Nat.cast_nonneg (α := ℝ) bd]
  have ht4 : (4 : ℝ) ≤ t := by
    rw [htdef]; nlinarith [hP2, sq_nonneg ((bd + 1 : ℝ) * (2 + C) - 2)]
  have htL : t ≤ Real.log m := by
    rw [← Real.log_exp t]; exact Real.log_le_log (Real.exp_pos t) hmt
  set L : ℝ := Real.log m with hLdef
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hLnn : (0 : ℝ) ≤ L := by linarith
  have hsqrt_pos : 0 < Real.sqrt L := Real.sqrt_pos.mpr (by linarith)
  have hsqrt1 : 1 ≤ Real.sqrt L := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hL1
  have hloglog : Real.log L ≤ 2 * Real.sqrt L := by
    have h1 : Real.log (Real.sqrt L) ≤ Real.sqrt L - 1 :=
      Real.log_le_sub_one_of_pos hsqrt_pos
    have h2 : Real.log (Real.sqrt L) = Real.log L / 2 := Real.log_sqrt hLnn
    linarith
  have hmulself : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hLnn
  have hsqrt_t : (bd + 1 : ℝ) * (2 + C) ≤ Real.sqrt L := by
    have h1 : Real.sqrt t = (bd + 1 : ℝ) * (2 + C) := by
      rw [htdef]; exact Real.sqrt_sq (by linarith)
    rw [← h1]; exact Real.sqrt_le_sqrt htL
  have hdenpos : 0 < Real.log L + C := by
    have h0 : 0 ≤ Real.log L := Real.log_nonneg hL1
    linarith
  have hratio : (bd : ℝ) + 1 ≤ L / (Real.log L + C) := by
    rw [le_div_iff₀ hdenpos]
    have hden2 : Real.log L + C ≤ (2 + C) * Real.sqrt L := by
      have h1 : C ≤ C * Real.sqrt L := le_mul_of_one_le_right hC.le hsqrt1
      nlinarith
    calc ((bd : ℝ) + 1) * (Real.log L + C)
        ≤ ((bd : ℝ) + 1) * ((2 + C) * Real.sqrt L) :=
          mul_le_mul_of_nonneg_left hden2 (by linarith)
      _ = ((bd : ℝ) + 1) * (2 + C) * Real.sqrt L := by ring
      _ ≤ Real.sqrt L * Real.sqrt L :=
          mul_le_mul_of_nonneg_right hsqrt_t (Real.sqrt_nonneg L)
      _ = L := hmulself
  have hfinal : (bd : ℝ) ≤ (Q m : ℝ) := by linarith
  exact_mod_cast hfinal

end TH
