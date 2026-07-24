/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Tactic
import ForMathlib.NumberTheory.WaringNumber
import ForMathlib.Data.Real.NearestInt
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Bugeaud, Chapter 3, §3.7 — Waring's problem and the ideal formula

Yann Bugeaud, *Distribution Modulo One and Diophantine Approximation* (Cambridge Tracts in
Mathematics 193, 2012), §3.7.  Let `g(n)` be the Waring number: the least `s` such that every
positive integer is a sum of `s` nonnegative `n`-th powers (`Nat.waringNumber`,
`ForMathlib.NumberTheory.WaringNumber`).

The section proves the **lower bound** (3.22) and reduces the **ideal formula** to a congruence
condition (3.23) with a clean sufficient inequality (3.24):

> (3.22)  `g(n) ≥ 2ⁿ + ⌊(3/2)ⁿ⌋ - 2`.
>
> Equality holds when (3.23) `2ⁿ{(3/2)ⁿ} + ⌊(3/2)ⁿ⌋ ≤ 2ⁿ`; if (3.23) fails then
> `g(n) = 2ⁿ + ⌊(3/2)ⁿ⌋ + ⌊(4/3)ⁿ⌋ - θ` with `θ ∈ {2, 3}`.
>
> (3.24)  `{(3/2)ⁿ} ≥ (3/4)ⁿ⁻¹`  is sufficient for (3.23).

Writing `3ⁿ = q·2ⁿ + r` with `q = ⌊(3/2)ⁿ⌋ = 3ⁿ / 2ⁿ` (`waringQuot`) and `r = 3ⁿ mod 2ⁿ`, the
congruence condition (3.23) is `r + q + 2 ≤ 2ⁿ` (`DicksonCond`).

## What is formalised

* `Bugeaud.waringNumber_ge` — **the lower bound (3.22)**, `2ⁿ + ⌊(3/2)ⁿ⌋ - 2 ≤ g(n)`, **proved**
  (given that `g(n)` is well defined, i.e. Hilbert–Waring, which is carried as the nonemptiness
  hypothesis).  This is the elementary half the book actually proves, via the general
  `Nat.pillai_le_waringNumber`: the number `2ⁿ⌊(3/2)ⁿ⌋ - 1 < 3ⁿ` can only be built from the powers
  `0, 1, 2ⁿ`, and doing so costs `2ⁿ + ⌊(3/2)ⁿ⌋ - 2` summands.

* `Bugeaud.waringNumber_ideal_of_dickson` — **(3.23) ⟹ equality**, `g(n) = 2ⁿ + ⌊(3/2)ⁿ⌋ - 2`.
  Here only the **hard upper direction** (Dickson's theorem: under (3.23), `2ⁿ + ⌊(3/2)ⁿ⌋ - 2`
  powers suffice for every `N`) is a cited `axiom` (`dickson_ideal_upper`); the `≥` direction is
  the proved lower bound above, so the equality follows by antisymmetry.  This de-axiomatises the
  `≥` half that a bare cited equality would hide.

* `Bugeaud.notDickson_imp_distBound` — **the (3.24) trace**, proved: when (3.23) fails,
  `‖(3/2)ⁿ‖ < (3/4)ⁿ⁻¹`, i.e. the failures are exactly the `‖(3/2)ⁿ‖`-smallness events (3.24)
  excludes.

* `Bugeaud.waring_value_dichotomy` — **the full value of `g(n)`** for `n ≥ 6`: the ideal formula
  (under (3.23)) or the Rubugunday–Niven fallback with `⌊(4/3)ⁿ⌋` and `θ ∈ {2, 3}` (otherwise).
  The fallback (`waringNumber_fallback`) and Bennett's secondary `(4/3)`-bound
  (`distToNearestInt_four_thirds_ge`, `secondary_condition_holds`) are cited classical inputs.

## Scope

This file is the **general §3.7 chain** in the Bugeaud-chapters root.  The *quantitative* side —
turning Mahler's ineffective finiteness of the `‖(3/2)ⁿ‖`-exceptions into an explicit bound on the
Waring exceptions via a Subspace/Ridout line count — is Problem 10.13 material and lives separately
in `BB13.Waring` (which carries its own copy of the cited-equality form of the ideal formula).

## References

* [Bug12] Y. Bugeaud, *Distribution Modulo One and Diophantine Approximation*, CUP 2012, §3.7.
* [Dic36] L. E. Dickson, *On Waring's problem and its generalizations*, 1936 — the ideal formula.
* [Rub42] R. Rubugunday, J. Indian Math. Soc. **6** (1942); [Niv44] I. Niven, Amer. J. Math. **66**
  (1944) — the `θ ∈ {2, 3}` fallback.
* [Zou13] C. Zou, MSc thesis, UBC 2013; [Pup14] V. Yu. Pupyrev, 2014 — `‖(4/3)ⁿ‖ ≥ (4/9)ⁿ`,
  `n ≥ 6` (Bennett's `g₃`-condition), unconditional.
-/

namespace Bugeaud

/-! ### The §3.7 objects -/

/-- `q = ⌊(3/2)ⁿ⌋`, computed as the integer quotient `3ⁿ / 2ⁿ`. -/
def waringQuot (n : ℕ) : ℕ := 3 ^ n / 2 ^ n

/-- `q' = ⌊(4/3)ⁿ⌋`, computed as the integer quotient `4ⁿ / 3ⁿ` (the fallback summand). -/
def waringQuot' (n : ℕ) : ℕ := 4 ^ n / 3 ^ n

/-- **The congruence condition (3.23)**, `r + q + 2 ≤ 2ⁿ` (`r = 3ⁿ mod 2ⁿ`, `q = ⌊(3/2)ⁿ⌋`): the
classical (Dickson) sufficient condition for the ideal Waring formula `g(n) = 2ⁿ + q - 2`. -/
def DicksonCond (n : ℕ) : Prop := 3 ^ n % 2 ^ n + waringQuot n + 2 ≤ 2 ^ n

/-! ### The lower bound (3.22) — proved -/

/-- **The lower bound (3.22)**, `g(n) ≥ 2ⁿ + ⌊(3/2)ⁿ⌋ - 2` (`n ≥ 2`).  The number
`2ⁿ⌊(3/2)ⁿ⌋ - 1` lies below `3ⁿ`, so it can only be represented with the powers `0, 1, 2ⁿ`, and
the cheapest such representation uses `2ⁿ + ⌊(3/2)ⁿ⌋ - 2` of them.  Proved via
`Nat.pillai_le_waringNumber`; the hypothesis `hne` that the Waring number is well defined is
Hilbert–Waring (finiteness of `g(n)`). -/
@[category research solved, AMS 11, ref "Bug12", group "bug_3_22"]
theorem waringNumber_ge {n : ℕ} (hn : 2 ≤ n)
    (hne : {s | ∀ N, Nat.IsSumOfPowers n s N}.Nonempty) :
    2 ^ n + waringQuot n - 2 ≤ Nat.waringNumber n :=
  Nat.pillai_le_waringNumber hn hne

/-! ### Cited classical inputs (Dickson / Rubugunday–Niven / Zou–Pupyrev) -/

/-- **Dickson's ideal Waring theorem, upper direction** ([Bug12] (3.23)–(3.24); Dickson 1936): if
the congruence condition (3.23) holds then `2ⁿ + ⌊(3/2)ⁿ⌋ - 2` nonnegative `n`-th powers suffice to
represent *every* natural number.  This is the hard classical half (Hardy–Wright, Ch. XXI); the
matching lower bound `waringNumber_ge` is proved, so together they give the equality.  Cited
`axiom`. -/
@[category research solved, AMS 11, ref "Bug12" "Dic36", group "bug_3_22"]
axiom dickson_ideal_upper (n : ℕ) (hn : 2 ≤ n) (hd : DicksonCond n) :
    ∀ N, Nat.IsSumOfPowers n (2 ^ n + waringQuot n - 2) N

/-- **The ideal Waring formula (3.23) ⟹ equality**: if the congruence condition (3.23) holds then
`g(n) = 2ⁿ + ⌊(3/2)ⁿ⌋ - 2`.  A **theorem**: the upper bound is the cited `dickson_ideal_upper`, the
lower bound is the proved `waringNumber_ge`. -/
@[category research solved, AMS 11, ref "Bug12" "Dic36", group "bug_3_22",
  formal_uses waringNumber_ge, formal_uses dickson_ideal_upper]
theorem waringNumber_ideal_of_dickson (n : ℕ) (hn : 2 ≤ n) (hd : DicksonCond n) :
    Nat.waringNumber n = 2 ^ n + waringQuot n - 2 := by
  have hwit : ∀ N, Nat.IsSumOfPowers n (2 ^ n + waringQuot n - 2) N := dickson_ideal_upper n hn hd
  have hne : {s | ∀ N, Nat.IsSumOfPowers n s N}.Nonempty := ⟨2 ^ n + waringQuot n - 2, hwit⟩
  exact le_antisymm (Nat.sInf_le hwit) (waringNumber_ge hn hne)

/-- **The Rubugunday–Niven fallback formula** ([Bug12] the display after (3.23); Rubugunday 1942,
Niven 1944): when (3.23) fails (`n ≥ 6`), one has `q·q' + q + q' ≥ 2ⁿ`, and `g(n)` is
`2ⁿ + q + q' - 2` or `2ⁿ + q + q' - 3` according to whether `q·q' + q + q' = 2ⁿ` or `> 2ⁿ`, with
`q = ⌊(3/2)ⁿ⌋`, `q' = ⌊(4/3)ⁿ⌋`.  Classical, cited. -/
@[category research solved, AMS 11, ref "Bug12" "Rub42" "Niv44", group "bug_3_22"]
axiom waringNumber_fallback (n : ℕ) (hn : 6 ≤ n) (hnd : ¬ DicksonCond n) :
    2 ^ n ≤ waringQuot n * waringQuot' n + waringQuot n + waringQuot' n ∧
    Nat.waringNumber n = 2 ^ n + waringQuot n + waringQuot' n
      - (if waringQuot n * waringQuot' n + waringQuot n + waringQuot' n = 2 ^ n then 2 else 3)

/-- **Bennett's `g₃`-condition, settled unconditionally** ([Zou13]; [Pup14]): `‖(4/3)ⁿ‖ ≥ (4/9)ⁿ`
for all `n ≥ 6`.  The secondary Waring condition of the `θ ∈ {2, 3}` branch, needing no counting.
Cited (neither preprint is journal-published; both prove it). -/
@[category research solved, AMS 11, ref "Zou13" "Pup14", group "bug_3_22"]
axiom distToNearestInt_four_thirds_ge (n : ℕ) (hn : 6 ≤ n) :
    ((4 : ℝ) / 9) ^ n ≤ distToNearestInt (((4 : ℝ) / 3) ^ n)

/-! ### The (3.24) trace: a failure of (3.23) is a `‖(3/2)ⁿ‖ < (3/4)ⁿ⁻¹` event -/

/-- **When (3.23) fails, `(3/2)ⁿ` is `(3/4)ⁿ⁻¹`-close to an integer** (`n ≥ 3`): the `(3.24)`
trace, sorry-free.  `¬DicksonCond n` means `2ⁿ - r ≤ q + 1`, so
`‖(3/2)ⁿ‖ ≤ (q+1)/2ⁿ ≤ (3/4)ⁿ + (1/2)ⁿ < (3/4)ⁿ⁻¹` — every Waring failure is a `‖(3/2)ⁿ‖`-smallness
event, of exactly the shape (3.24) rules out. -/
@[category research solved, AMS 11, ref "Bug12", group "bug_3_22"]
theorem notDickson_imp_distBound {n : ℕ} (hn : 3 ≤ n) (hnd : ¬ DicksonCond n) :
    distToNearestInt (((3 : ℝ) / 2) ^ n) < ((3 : ℝ) / 4) ^ (n - 1) := by
  set r : ℝ := ((3 ^ n % 2 ^ n : ℕ) : ℝ) with hrdef
  set q : ℝ := ((3 ^ n / 2 ^ n : ℕ) : ℝ) with hqdef
  clear_value q r
  have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
  have h32 : ((3 : ℝ) / 2) ^ n = (3 : ℝ) ^ n / (2 : ℝ) ^ n := div_pow 3 2 n
  have key : (3 : ℝ) ^ n = (2 : ℝ) ^ n * q + r := by
    rw [hqdef, hrdef]; exact_mod_cast (Nat.div_add_mod (3 ^ n) (2 ^ n)).symm
  have hRlt : r < (2 : ℝ) ^ n := by
    rw [hrdef]; exact_mod_cast Nat.mod_lt (3 ^ n) (show 0 < 2 ^ n by positivity)
  have hnd'' : (2 : ℝ) ^ n ≤ r + q + 1 := by
    have hndnat : 2 ^ n ≤ 3 ^ n % 2 ^ n + 3 ^ n / 2 ^ n + 1 := by
      simp only [DicksonCond, waringQuot] at hnd; omega
    rw [hqdef, hrdef]; exact_mod_cast hndnat
  have hval : ((3 : ℝ) / 2) ^ n - (((3 ^ n / 2 ^ n : ℕ) : ℤ) + 1 : ℤ)
      = (((3 ^ n % 2 ^ n : ℕ) : ℝ) - (2 : ℝ) ^ n) / (2 : ℝ) ^ n := by
    have key0 : (3 : ℝ) ^ n = (2 : ℝ) ^ n * ((3 ^ n / 2 ^ n : ℕ) : ℝ) + ((3 ^ n % 2 ^ n : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod (3 ^ n) (2 ^ n)).symm
    rw [h32, eq_div_iff h2, sub_mul, div_mul_cancel₀ _ h2, Int.cast_add, Int.cast_natCast,
      Int.cast_one]
    linear_combination key0
  have hstep1 : distToNearestInt (((3 : ℝ) / 2) ^ n) ≤ ((2 : ℝ) ^ n - r) / (2 : ℝ) ^ n := by
    have hle := distToNearestInt_le_abs_sub_intCast (((3 : ℝ) / 2) ^ n) (((3 ^ n / 2 ^ n : ℕ) : ℤ) + 1)
    rw [hval, abs_div, abs_of_pos (show (0 : ℝ) < (2 : ℝ) ^ n by positivity),
      abs_of_nonpos (show ((3 ^ n % 2 ^ n : ℕ) : ℝ) - (2 : ℝ) ^ n ≤ 0 by rw [← hrdef]; linarith [hRlt]),
      neg_sub] at hle
    rw [hrdef]; exact hle
  have hstep2 : ((2 : ℝ) ^ n - r) / (2 : ℝ) ^ n ≤ (q + 1) / (2 : ℝ) ^ n := by
    gcongr; linarith [hnd'']
  have h44 : (4 : ℝ) ^ n = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by rw [← mul_pow]; norm_num
  have e1 : ((3 : ℝ) / 4) ^ n = (3 : ℝ) ^ n / ((2 : ℝ) ^ n * (2 : ℝ) ^ n) := by rw [div_pow, h44]
  have e2 : ((1 : ℝ) / 2) ^ n = 1 / (2 : ℝ) ^ n := by rw [div_pow, one_pow]
  have hQle : q ≤ (3 : ℝ) ^ n / (2 : ℝ) ^ n := by
    rw [le_div_iff₀ (show (0 : ℝ) < (2 : ℝ) ^ n by positivity)]; nlinarith [key, hRlt]
  have hstep3 : (q + 1) / (2 : ℝ) ^ n ≤ ((3 : ℝ) / 4) ^ n + ((1 : ℝ) / 2) ^ n :=
    calc (q + 1) / (2 : ℝ) ^ n ≤ ((3 : ℝ) ^ n / (2 : ℝ) ^ n + 1) / (2 : ℝ) ^ n := by gcongr
      _ = (3 : ℝ) ^ n / ((2 : ℝ) ^ n * (2 : ℝ) ^ n) + 1 / (2 : ℝ) ^ n := by field_simp
      _ = ((3 : ℝ) / 4) ^ n + ((1 : ℝ) / 2) ^ n := by rw [e1, e2]
  have hkey : ((1 : ℝ) / 2) ^ n < (1 / 3) * ((3 : ℝ) / 4) ^ n := by
    have h1 : (0 : ℝ) < ((1 : ℝ) / 2) ^ n := by positivity
    have hh2 : ((3 : ℝ) / 4) ^ n = ((3 : ℝ) / 2) ^ n * ((1 : ℝ) / 2) ^ n := by rw [← mul_pow]; norm_num
    have h3 : (3 : ℝ) < ((3 : ℝ) / 2) ^ n := by
      have hmono : ((3 : ℝ) / 2) ^ 3 ≤ ((3 : ℝ) / 2) ^ n := pow_le_pow_right₀ (by norm_num) hn
      nlinarith [hmono]
    rw [hh2]; nlinarith [mul_lt_mul_of_pos_right h3 h1]
  have hstep4 : ((3 : ℝ) / 4) ^ n + ((1 : ℝ) / 2) ^ n < ((3 : ℝ) / 4) ^ (n - 1) := by
    have hpow : ((3 : ℝ) / 4) ^ n = ((3 : ℝ) / 4) ^ (n - 1) * ((3 : ℝ) / 4) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega]
      rw [pow_succ]
    have hexp : ((3 : ℝ) / 4) ^ (n - 1) = (4 / 3) * ((3 : ℝ) / 4) ^ n := by rw [hpow]; ring
    rw [hexp]; linarith [hkey]
  calc distToNearestInt (((3 : ℝ) / 2) ^ n)
      ≤ ((2 : ℝ) ^ n - r) / (2 : ℝ) ^ n := hstep1
    _ ≤ (q + 1) / (2 : ℝ) ^ n := hstep2
    _ ≤ ((3 : ℝ) / 4) ^ n + ((1 : ℝ) / 2) ^ n := hstep3
    _ < ((3 : ℝ) / 4) ^ (n - 1) := hstep4

/-! ### The secondary `(4/3)` condition and the full value dichotomy -/

/-- **The secondary `(4/3)`-event is empty for `n ≥ 6`** — `‖(4/3)ⁿ‖ ≥ (4/9)ⁿ` always holds there
(Zou/Pupyrev), so Bennett's `g₃`-condition needs no counting. -/
@[category research solved, AMS 11, ref "Zou13" "Pup14", group "bug_3_22"]
theorem secondary_condition_holds {n : ℕ} (hn : 6 ≤ n) :
    ¬ distToNearestInt (((4 : ℝ) / 3) ^ n) < ((4 : ℝ) / 9) ^ n :=
  not_lt.mpr (distToNearestInt_four_thirds_ge n hn)

/-- **The full `g(n)` value dichotomy for `n ≥ 6`**: either (3.23) holds and `g(n)` is the ideal
formula `2ⁿ + ⌊(3/2)ⁿ⌋ - 2`, or it fails and `g(n)` is the Rubugunday–Niven fallback
`2ⁿ + ⌊(3/2)ⁿ⌋ + ⌊(4/3)ⁿ⌋ - (2 or 3)`. -/
@[category research solved, AMS 11, ref "Bug12" "Rub42" "Niv44", group "bug_3_22",
  formal_uses waringNumber_ideal_of_dickson, formal_uses waringNumber_fallback]
theorem waring_value_dichotomy (n : ℕ) (hn : 6 ≤ n) :
    (DicksonCond n ∧ Nat.waringNumber n = 2 ^ n + waringQuot n - 2) ∨
    (¬ DicksonCond n ∧ Nat.waringNumber n
      = 2 ^ n + waringQuot n + waringQuot' n
        - (if waringQuot n * waringQuot' n + waringQuot n + waringQuot' n = 2 ^ n then 2 else 3)) := by
  by_cases hd : DicksonCond n
  · exact Or.inl ⟨hd, waringNumber_ideal_of_dickson n (by omega) hd⟩
  · exact Or.inr ⟨hd, (waringNumber_fallback n hn hd).2⟩

end Bugeaud
