/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.FailureCount
import ForMathlib.NumberTheory.WaringNumber

/-!
# Waring packaging for Problem 10.13: the ideal formula `g(n) = 2ⁿ + ⌊(3/2)ⁿ⌋ - 2` (D3 / M4)

Milestone **M4** of `plans/plan-1013.html` — the **Waring corollary** (deliverable **D3**,
target theorem **T3**): the ideal Waring formula
`g(n) = 2ⁿ + ⌊(3/2)ⁿ⌋ - 2`
fails for **at most an explicitly bounded number** of `n`.  This is the headline application of
the count: Mahler's ineffective finiteness of the `‖(3/2)ⁿ‖`-exceptions becomes an explicit bound
on the exceptions to the classical Waring formula.

## The §3.7 chain (Bugeaud (3.22)–(3.24))

Write `3ⁿ = q·2ⁿ + r` with `q = ⌊(3/2)ⁿ⌋` (`waringQuot`) and `0 ≤ r < 2ⁿ` (`r = 3ⁿ mod 2ⁿ`).
**Dickson's condition** `DicksonCond n : r ≤ 2ⁿ - q - 2` is the classical sufficient condition for
the ideal formula:

* `waringNumber_ideal_of_dickson` — Dickson's condition ⟹ `g(n) = 2ⁿ + q - 2`  ([Bug12] (3.24),
  Dickson 1936);
* `waringNumber_fallback` — its failure ⟹ the Rubugunday–Niven fallback with `q' = ⌊(4/3)ⁿ⌋`
  and the `θ ∈ {2, 3}` (subtract-`2`-or-`3`) dichotomy  ([Bug12] (3.22)–(3.23), Rubugunday 1942 /
  Niven 1944).

Both are **classical, literature-proved** theorems, recorded as cited `@[ref]` axioms (corpus
house policy): the *content* delivered here is the assembly with the count.

The elementary bridge (proved, sorry-free) is `notDickson_imp_distBound`: when Dickson's condition
fails, `(3/2)ⁿ` is within `(3/4)ⁿ⁻¹` of an integer — i.e. **every Waring exception is a
`‖(3/2)ⁿ‖ < (3/4)ⁿ⁻¹` event**, of exactly the shape the Subspace count of `BB13.Subspace` bounds.
Feeding it through `mem_approxSet_of_distBound` gives:

* `dickson_exceptions_finite` — the set of `n` failing Dickson's condition is finite;
* `waring_exceptions_finite` — hence **`g(n) = 2ⁿ + ⌊(3/2)ⁿ⌋ - 2` for all but finitely many `n`**;
* `waring_ideal_formula_eventually` — and for all sufficiently large `n`.

## The repaired counts (W5 of `plans/plan2-BB13.html`)

Earlier versions carried `#{n ≥ 1 : ¬DicksonCond n} ≤ 2 + C` and `#{Waring exceptions} ≤ 2 + C`
on a cited axiom asserting an effective *solution* count.  That axiom was retired on 2026-07-21
(it overstated [BE08] Cor. 5.2, which counts *lines* above a height threshold — see
`CITED/BugeaudEvertseRidout.lean`).  What replaces it:

* **the frame.**  A Waring exception satisfies the weaker event `‖(3/2)ⁿ‖ < (3/4)ⁿ⁻¹`, so its
  frame point loses a factor `4/3` at the archimedean place.  Buying it back costs an exponent
  `ε*/257`, giving the budget `θ_W + θ + 1 = 2 + ε_W` with
  `ε_W = ε*(1 − 1/257) = 0.26084…` — a `0.4%` shave, worth a `1.1%` larger constant:
  `K(ε_W) = 1 876 339 827 243` against `K(ε*) = 1 856 360 182 227`.  The cutoff `257` is where
  the kernel arm stops;
* **the kernel arm.**  `dicksonCond_of_le_256`: Dickson's condition *holds* for every
  `3 ≤ n ≤ 256`, by `decide` against the exact-integer definition.  So the only exceptions below
  the cutoff are `n = 1, 2`;
* **`g(2) = 4`.**  `n = 2` fails Dickson's condition but satisfies the ideal formula anyway
  (`2² + ⌊(3/2)²⌋ − 2 = 4 = g(2)`, `Nat.waringNumber_two`).  Hence the Waring count carries **no
  additive constant at all** — the `+2` of the retired statement was never needed;
* **the counts.**  `dickson_exceptions_card_le_of_heightBound` (`≤ 2 + H·K(ε_W)`, the `2` being
  the genuine Dickson exceptions `{1, 2}`) and `waring_exceptions_card_le_of_heightBound`
  (`≤ H·K(ε_W)`), conditional on the same per-line hypothesis `H` as
  `BB13.failures_card_le_of_heightBound`, and `waring_value_dichotomy_count` (F4: the dichotomy
  *and* a count clause, with the footprint the count actually has).

## The secondary `(4/3)` condition

The Rubugunday–Niven fallback needs a secondary bound on `‖(4/3)ⁿ‖` for `q' = ⌊(4/3)ⁿ⌋` to be the
correct summand count.  Bennett's `g₃`-condition `‖(4/3)ⁿ‖ ≥ (4/9)ⁿ` is settled **unconditionally
for `n ≥ 6`** — twice over, Zou 2013 and (independently) Pupyrev 2014 — so no counting is needed:

* `distToNearestInt_four_thirds_ge` — the cited Zou/Pupyrev bound;
* `secondary_condition_holds` — hence the secondary `(4/3)`-event is empty for `n ≥ 6`.

(The general `(4/3, c)` count is available by the same method as `BB13.Subspace` — the CZ frame
`u = (4/3)ⁿ = 2²ⁿ3⁻ⁿ`, `n ↦ (1, 2n, -n)`, `H(u) = 4ⁿ` — but the unconditional bound is sharper,
so it is what we record.)

`waring_value_dichotomy` packages the two branches: for `n ≥ 6`, `g(n)` is either the ideal
formula (Dickson) or the Rubugunday–Niven fallback (¬Dickson); `waring_value_dichotomy_count`
adds the count clause for the second branch, with the footprint that clause actually has.

## References

* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, 2012 — Prob. 10.13;
  §3.7 (Waring chain (3.22)–(3.24)).
* [Dic36] L. E. Dickson, *On Waring's problem and its generalizations*, 1936 — the ideal formula.
* [Rub42] R. Rubugunday, *On `g(k)` in Waring's problem*, J. Indian Math. Soc. **6** (1942).
* [Niv44] I. Niven, *An unsolved case of the Waring problem*, Amer. J. Math. **66** (1944).
* [Zou13] C. Zou, MSc thesis, UBC 2013; [Pup14] V. Yu. Pupyrev, 2014 — `‖(4/3)ⁿ‖ ≥ (4/9)ⁿ`,
  `n ≥ 6`, unconditional (Bennett's `g₃`-condition).
* [BE08] Bugeaud–Evertse, Acta Arith. **133** (2008), Cor. 5.2 — the quantitative Ridout line
  count (`CITED/BugeaudEvertseRidout.lean`), on which the repaired counts run.
-/

namespace BB13

open scoped Real

/-! ### The §3.7 objects -/

/-- `q = ⌊(3/2)ⁿ⌋`, computed as the integer quotient `3ⁿ / 2ⁿ`. -/
def waringQuot (n : ℕ) : ℕ := 3 ^ n / 2 ^ n

/-- `q' = ⌊(4/3)ⁿ⌋`, computed as the integer quotient `4ⁿ / 3ⁿ` (the fallback summand). -/
def waringQuot' (n : ℕ) : ℕ := 4 ^ n / 3 ^ n

/-- **Dickson's condition** `r ≤ 2ⁿ - q - 2` (`r = 3ⁿ mod 2ⁿ`, `q = ⌊(3/2)ⁿ⌋`): the classical
sufficient condition for the ideal Waring formula `g(n) = 2ⁿ + q - 2` ([Bug12] (3.24)). -/
def DicksonCond (n : ℕ) : Prop := 3 ^ n % 2 ^ n + waringQuot n + 2 ≤ 2 ^ n

/-! ### Cited classical inputs (Bugeaud §3.7 / Dickson–Rubugunday–Niven / Zou–Pupyrev) -/

/-- **The ideal Waring formula under Dickson's condition** ([Bug12] (3.24); Dickson 1936): if
`r ≤ 2ⁿ - q - 2` then `g(n) = 2ⁿ + ⌊(3/2)ⁿ⌋ - 2`.  A classical, literature-proved theorem,
recorded as a cited `axiom`. -/
@[category research solved, AMS 11, ref "Bug12" "Dic36", group "bugeaud_10_13"]
axiom waringNumber_ideal_of_dickson (n : ℕ) (hn : 2 ≤ n) (hd : DicksonCond n) :
    Nat.waringNumber n = 2 ^ n + waringQuot n - 2

/-- **The Rubugunday–Niven fallback formula** ([Bug12] (3.22)–(3.23); Rubugunday 1942, Niven 1944):
when Dickson's condition fails (`n ≥ 6`), one has `q·q' + q + q' ≥ 2ⁿ`, and `g(n)` is
`2ⁿ + q + q' - 2` or `2ⁿ + q + q' - 3` according to whether `q·q' + q + q' = 2ⁿ` or `> 2ⁿ` (the
`θ ∈ {2, 3}` dichotomy), with `q = ⌊(3/2)ⁿ⌋`, `q' = ⌊(4/3)ⁿ⌋`.  Classical, cited. -/
@[category research solved, AMS 11, ref "Bug12" "Rub42" "Niv44", group "bugeaud_10_13"]
axiom waringNumber_fallback (n : ℕ) (hn : 6 ≤ n) (hnd : ¬ DicksonCond n) :
    2 ^ n ≤ waringQuot n * waringQuot' n + waringQuot n + waringQuot' n ∧
    Nat.waringNumber n = 2 ^ n + waringQuot n + waringQuot' n
      - (if waringQuot n * waringQuot' n + waringQuot n + waringQuot' n = 2 ^ n then 2 else 3)

/-- **Bennett's `g₃`-condition, settled unconditionally** ([Zou13]; [Pup14]): `‖(4/3)ⁿ‖ ≥ (4/9)ⁿ`
for all `n ≥ 6`.  The secondary Waring condition of the `θ ∈ {2, 3}` branch, needing no counting.
Cited (neither preprint is journal-published; both prove it). -/
@[category research solved, AMS 11, ref "Zou13" "Pup14", group "bugeaud_10_13"]
axiom distToNearestInt_four_thirds_ge (n : ℕ) (hn : 6 ≤ n) :
    ((4 : ℝ) / 9) ^ n ≤ distToNearestInt (((4 : ℝ) / 3) ^ n)

/-! ### The elementary reduction: a Waring exception is a `‖(3/2)ⁿ‖ < (3/4)ⁿ⁻¹` event -/

/-- The Subspace threshold `(3/4)ⁿ⁻¹ < (3ⁿ)^{-ε}` (`ε = epsZero`) for `n ≥ 3`.  Sharper than the
`(3/4)ⁿ` bound (`n ≥ 1`) of `BB13.Subspace` because `(3/4)ⁿ⁻¹ = (4/3)·(3/4)ⁿ`; the condition
`(n-1)·log(4/3) > n·ε·log 3` is `n > 2`. -/
private theorem threshold_waring {n : ℕ} (hn : 3 ≤ n) :
    ((3 : ℝ) / 4) ^ (n - 1) < ((3 : ℝ) ^ n) ^ (-epsZero) := by
  rw [epsZero, ← Real.rpow_natCast (3 / 4 : ℝ) (n - 1), ← Real.rpow_natCast (3 : ℝ) n,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3 / 4),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), Real.exp_lt_exp]
  have e1 : Real.log (3 / 4) = -Real.log (4 / 3) := by rw [← Real.log_inv]; norm_num
  rw [e1, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hrhs : Real.log 3 * (↑n * -(Real.log (4 / 3) / (2 * Real.log 3)))
      = -(↑n * Real.log (4 / 3)) / 2 := by
    have h3 : Real.log 3 ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
    field_simp
  rw [hrhs]
  have hL : 0 < Real.log (4 / 3) := Real.log_pos (by norm_num)
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith [hL, hn3]

/-- **When Dickson's condition fails, `(3/2)ⁿ` is `(3/4)ⁿ⁻¹`-close to an integer** (`n ≥ 3`): the
`(3.24)` trace, sorry-free.  `¬DicksonCond n` means `2ⁿ - r ≤ q + 1`, so
`‖(3/2)ⁿ‖ ≤ (q+1)/2ⁿ ≤ (3/4)ⁿ + (1/2)ⁿ < (3/4)ⁿ⁻¹` — the Waring failure is a `‖(3/2)ⁿ‖`-smallness
event of the same family the count handles. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
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

/-- A Dickson-exception at `n ≥ 3` maps into the Corvaja–Zannier exceptional set (same frame,
same `ε = epsZero` as the `‖(3/2)ⁿ‖ < (3/4)ⁿ` count). -/
@[category research solved, AMS 11, ref "Bug12" "CZ04", group "bugeaud_10_13"]
theorem notDickson_mem {n : ℕ} (hn : 3 ≤ n) (hnd : ¬ DicksonCond n) :
    toTriple n ∈ CZ.approxSet 1 epsZero := by
  apply mem_approxSet_of_distBound (by omega : 1 ≤ n)
  calc distToNearestInt (((3 : ℝ) / 2) ^ n)
      < ((3 : ℝ) / 4) ^ (n - 1) := notDickson_imp_distBound hn hnd
    _ < ((3 : ℝ) ^ n) ^ (-epsZero) := threshold_waring hn

/-! ### The Dickson-exception set is finite and explicitly bounded -/

private theorem dickson_large_finite : {n : ℕ | 3 ≤ n ∧ ¬ DicksonCond n}.Finite := by
  apply Set.Finite.of_finite_image _ toTriple_injective.injOn
  apply (CZ.approxSet_finite 1 (by norm_num) epsZero epsZero_pos).subset
  rintro _ ⟨n, ⟨hn3, hnd⟩, rfl⟩
  exact notDickson_mem hn3 hnd

private theorem dickson_subset :
    {n : ℕ | 1 ≤ n ∧ ¬ DicksonCond n} ⊆ ({1, 2} : Set ℕ) ∪ {n : ℕ | 3 ≤ n ∧ ¬ DicksonCond n} := by
  rintro n ⟨hn1, hnd⟩
  rcases lt_or_ge n 3 with h | h
  · exact Or.inl (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; omega)
  · exact Or.inr ⟨h, hnd⟩

/-- **The set of `n ≥ 1` failing Dickson's condition is finite.**  Footprint
`std3 + Subspace.evertseSchlickewei` (via `notDickson_mem`; no effective input). -/
@[category research solved, AMS 11, ref "Bug12" "CZ04", group "bugeaud_10_13"]
theorem dickson_exceptions_finite : {n : ℕ | 1 ≤ n ∧ ¬ DicksonCond n}.Finite :=
  Set.Finite.subset (((Set.finite_singleton 2).insert 1).union dickson_large_finite)
    dickson_subset

/-! ### T3: the ideal formula holds off a finite exceptional set -/

/-- **The ideal Waring formula fails for finitely many `n`** (T3 finiteness).  Every exception
`g(n) ≠ 2ⁿ + ⌊(3/2)ⁿ⌋ - 2` (`n ≥ 2`) fails Dickson's condition, so lies in the finite Dickson
set. -/
@[category research solved, AMS 11, ref "Bug12" "CZ04", group "bugeaud_10_13"]
theorem waring_exceptions_finite :
    {n : ℕ | 2 ≤ n ∧ Nat.waringNumber n ≠ 2 ^ n + waringQuot n - 2}.Finite := by
  apply dickson_exceptions_finite.subset
  rintro n ⟨hn2, hne⟩
  exact ⟨by omega, fun hd => hne (waringNumber_ideal_of_dickson n hn2 hd)⟩

/-- **The ideal formula holds for all large `n`.**  There is `N₀` past which
`g(n) = 2ⁿ + ⌊(3/2)ⁿ⌋ - 2`. -/
@[category research solved, AMS 11, ref "Bug12" "CZ04", group "bugeaud_10_13"]
theorem waring_ideal_formula_eventually :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Nat.waringNumber n = 2 ^ n + waringQuot n - 2 := by
  obtain ⟨N₀, hN₀⟩ := dickson_exceptions_finite.bddAbove
  refine ⟨N₀ + 2, fun n hn => ?_⟩
  by_cases hd : DicksonCond n
  · exact waringNumber_ideal_of_dickson n (by omega) hd
  · exact absurd (hN₀ ⟨by omega, hd⟩) (by omega)

/-! ### W5: the quantitative lane — kernel arm, Waring frame, line cover, counts -/

set_option maxRecDepth 100000 in
/-- **The kernel arm:** Dickson's condition holds for every `3 ≤ n ≤ 256`, by `decide` against
the exact-integer definition (`r + q + 2 ≤ 2ⁿ`).  Below the cutoff the only exceptions are
`n = 1, 2`.  Axiom-free (`std3`; no `native_decide`). -/
@[category research solved, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem dicksonCond_of_le_256 {n : ℕ} (h3 : 3 ≤ n) (h256 : n ≤ 256) : DicksonCond n := by
  have H : ∀ m, m < 257 → 3 ≤ m → 3 ^ m % 2 ^ m + 3 ^ m / 2 ^ m + 2 ≤ 2 ^ m := by decide
  exact H n (by omega) h3

/-- The Waring exponent `ε_W = ε*(1 − 1/257) = 0.26084…`: the sharp `ε*` shaved by the amount the
`(3/4)ⁿ⁻¹` event costs at the cutoff `n = 257`. -/
noncomputable def epsW : ℝ := epsStar - epsStar / 257

/-- The archimedean exponent of the Waring frame, `θ_W = θ − ε*/257`. -/
noncomputable def thetaW : ℝ := theta - epsStar / 257

@[category API, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem epsStar_lt_theta : epsStar < theta := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h43 : Real.log (4 / 3) < Real.log 2 := Real.log_lt_log (by norm_num) (by norm_num)
  nlinarith [epsStar_mul_log_three, theta_mul_log_three, h43, h3]

@[category API, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem epsW_pos : 0 < epsW := by
  have := epsStar_pos
  rw [epsW]; linarith

@[category API, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem thetaW_nonneg : 0 ≤ thetaW := by
  have h1 := epsStar_pos
  have h2 := epsStar_lt_theta
  rw [thetaW]; linarith

/-- **The Waring budget identity** `θ_W + θ + 1 = 2 + ε_W`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem thetaW_add_theta_add_one : thetaW + theta + 1 = 2 + epsW := by
  have := theta_add_theta_add_one
  rw [thetaW, epsW]; linarith

/-- The height condition (5.12) for the Waring frame, from the cutoff on: `2^{4/ε_W} < 3ⁿ`. -/
@[category API, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem two_rpow_four_div_epsW_lt {n : ℕ} (hn : 257 ≤ n) :
    (2 : ℝ) ^ ((4 : ℝ) / epsW) < (3 : ℝ) ^ n := by
  refine two_rpow_four_div_lt epsW_pos ?_
  have hlog : epsW * Real.log 3 = Real.log (4 / 3) - Real.log (4 / 3) / 257 := by
    rw [epsW, sub_mul, epsStar_mul_log_three, div_mul_eq_mul_div, epsStar_mul_log_three]
  have hn' : (257 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hl43 : 0 < Real.log (4 / 3) := Real.log_pos (by norm_num)
  rw [hlog]
  nlinarith [four_log_two_lt, mul_le_mul_of_nonneg_right hn' hl43.le]

/-- **The shaved exponent buys back the factor `4/3`**: `(4/3)·2⁻ⁿ ≤ (3ⁿ)^{−θ_W}` for `n ≥ 257`.
This is where the cutoff is spent — `(3ⁿ)^{ε*/257} = (4/3)^{n/257} ≥ 4/3`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem rpow_neg_thetaW_ge {n : ℕ} (hn : 257 ≤ n) :
    (4 / 3 : ℝ) * (1 / 2 : ℝ) ^ n ≤ ((3 : ℝ) ^ n) ^ (-thetaW) := by
  have h3n : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hlhs : (0 : ℝ) < (4 / 3 : ℝ) * (1 / 2 : ℝ) ^ n := by positivity
  rw [Real.rpow_def_of_pos h3n, ← Real.exp_log hlhs, Real.exp_le_exp]
  have hlogL : Real.log ((4 / 3 : ℝ) * (1 / 2 : ℝ) ^ n)
      = Real.log (4 / 3) - (n : ℝ) * Real.log 2 := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
      show Real.log (1 / 2 : ℝ) = -Real.log 2 by rw [← Real.log_inv]; norm_num]
    ring
  have hrhs : Real.log ((3 : ℝ) ^ n) * (-thetaW) = -((n : ℝ) * (thetaW * Real.log 3)) := by
    rw [Real.log_pow]; ring
  have hlt : thetaW * Real.log 3 = Real.log 2 - Real.log (4 / 3) / 257 := by
    rw [thetaW, sub_mul, theta_mul_log_three, div_mul_eq_mul_div, epsStar_mul_log_three]
  rw [hlogL, hrhs, hlt]
  have hn' : (257 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hl43 : 0 < Real.log (4 / 3) := Real.log_pos (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_right hn' hl43.le]

/-- **The residue bound of a Waring event**: `¬DicksonCond n` (`n ≥ 3`) forces
`|kₙ| < (4/3)·(3/2)ⁿ` — the `(3/4)ⁿ⁻¹` analogue of `BB13.abs_resid_lt_of_isFailure`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem abs_resid_lt_of_notDickson {n : ℕ} (hn : 3 ≤ n) (hnd : ¬ DicksonCond n) :
    |((resid 3 2 n : ℤ) : ℝ)| < (4 / 3 : ℝ) * (3 / 2 : ℝ) ^ n := by
  have hd := notDickson_imp_distBound hn hnd
  rw [show ((3 : ℝ) / 2) = (((3 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) by norm_num,
    distToNearestInt_eq_resid 3 2 n (by norm_num),
    div_lt_iff₀ (show (0 : ℝ) < ((2 : ℕ) : ℝ) ^ n by positivity)] at hd
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hpow : ((3 : ℝ) / 4) ^ (m + 1 - 1) * ((2 : ℕ) : ℝ) ^ (m + 1)
      = (4 / 3 : ℝ) * (3 / 2 : ℝ) ^ (m + 1) := by
    simp only [Nat.add_sub_cancel]
    have h34 : ((3 : ℝ) / 4) ^ m * (2 : ℝ) ^ m = (3 / 2 : ℝ) ^ m := by
      rw [← mul_pow]; norm_num
    push_cast
    rw [pow_succ, pow_succ]
    linear_combination 2 * h34
  rw [hpow] at hd
  exact hd

/-! ### The Waring line cover and the counts -/

/-- The Dickson exceptions beyond the kernel range. -/
def dicksonHigh : Set ℕ := {n : ℕ | 257 ≤ n ∧ ¬ DicksonCond n}

/-- The Dickson exceptions beyond the kernel range on the line of slope `r`. -/
def dicksonFibre (r : ℚ) : Set ℕ := {n : ℕ | 257 ≤ n ∧ ¬ DicksonCond n ∧ linePoint n = r}

/-- **A single line carries finitely many Waring events** — the `K = 4/3` case of the elementary
confinement `BB13.sameTower_le_two_mul_of_bound`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem dicksonFibre_finite (r : ℚ) : (dicksonFibre r).Finite := by
  rcases Set.eq_empty_or_nonempty (dicksonFibre r) with he | ⟨a, ha⟩
  · rw [he]; exact Set.finite_empty
  · have ha257 : 257 ≤ a := ha.1
    apply Set.Finite.subset (Set.finite_Iic (2 * a))
    intro b hb
    simp only [Set.mem_Iic]
    rcases le_or_gt b a with hle | hlt
    · omega
    · exact sameTower_le_two_mul_of_bound (by omega) hlt (by norm_num)
        (abs_resid_lt_of_notDickson (by omega) hb.2.1) (ha.2.2.trans hb.2.2.symm)

/-- **The Waring line cover**: the Dickson exceptions `n ≥ 257` lie on at most
`K(ε_W) = 1 876 339 827 243` lines through the origin.  Instance of [BE08] Cor. 5.2 at the frame
`(θ_W, θ, 1)`, budget `2 + ε_W`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem notDickson_line_cover :
    ∃ R : Finset ℚ, R.card ≤ BugeaudEvertse.lineBound epsW ∧
      ∀ n : ℕ, 257 ≤ n → ¬ DicksonCond n → linePoint n ∈ R := by
  obtain ⟨R, hcard, hR⟩ := BugeaudEvertse.ridout_line_cover_23 1 epsW thetaW theta 1
    epsW_pos thetaW_nonneg theta_pos.le zero_le_one thetaW_add_theta_add_one
  refine ⟨R, hcard, fun n hn hnd => ?_⟩
  have hheight : max (2 * ((BugeaudEvertse.ratHeight 1 : ℕ) : ℝ)) ((2 : ℝ) ^ ((4 : ℝ) / epsW))
      < ((frameY n : ℤ) : ℝ) := by
    rw [frameY_cast, BugeaudEvertse.ratHeight_one]
    refine max_lt ?_ (two_rpow_four_div_epsW_lt hn)
    have h1 : (3 : ℝ) ^ 10 ≤ (3 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at h1 ⊢
    linarith
  refine hR (frameX n) (frameY n) (frameY_pos n) hheight ?_ (frame_two_adic n) (frame_three_adic n)
  have harch : |(1 : ℝ) - (frameX n : ℝ) / (frameY n : ℝ)| ≤ ((frameY n : ℤ) : ℝ) ^ (-thetaW) := by
    have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
    rw [frame_arch_eq, frameY_cast]
    have hres := abs_resid_lt_of_notDickson (by omega) hnd
    have hstep : |((resid 3 2 n : ℤ) : ℝ)| / (3 : ℝ) ^ n
        < ((4 / 3 : ℝ) * (3 / 2 : ℝ) ^ n) / (3 : ℝ) ^ n := by gcongr
    have hpow : ((4 / 3 : ℝ) * (3 / 2 : ℝ) ^ n) / (3 : ℝ) ^ n = (4 / 3 : ℝ) * (1 / 2 : ℝ) ^ n := by
      rw [mul_div_assoc, ← div_pow]; norm_num
    rw [hpow] at hstep
    exact le_trans (le_of_lt hstep) (rpow_neg_thetaW_ge hn)
  simpa using harch

/-- **The Dickson-exception count**: `#{n ≥ 1 : ¬DicksonCond n} ≤ 2 + H·K(ε_W)`, conditional on a
per-line bound `H` above the kernel range.  The `2` is exact — `n = 1` and `n = 2` do fail
Dickson's condition — and by `dicksonCond_of_le_256` nothing else below `257` does.

Footprint `std3 + BugeaudEvertse.ridout_line_cover`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem dickson_exceptions_card_le_of_heightBound (H : ℕ)
    (hfib : ∀ r : ℚ, (dicksonFibre r).ncard ≤ H) :
    {n : ℕ | 1 ≤ n ∧ ¬ DicksonCond n}.ncard ≤ 2 + H * BugeaudEvertse.lineBound epsW := by
  obtain ⟨R, hcard, hR⟩ := notDickson_line_cover
  have hfin : dicksonHigh.Finite := by
    apply Set.Finite.subset (R.finite_toSet.biUnion (fun r _ => dicksonFibre_finite r))
    rintro n ⟨hn, hnd⟩
    exact Set.mem_biUnion (hR n hn hnd) ⟨hn, hnd, rfl⟩
  have hfib' : ∀ r : ℚ, {n ∈ dicksonHigh | linePoint n = r}.ncard ≤ H := by
    intro r
    have heq : {n ∈ dicksonHigh | linePoint n = r} = dicksonFibre r := by
      ext n
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
    rw [heq]; exact hfib r
  have himg : linePoint '' dicksonHigh ⊆ ↑R := by
    rintro _ ⟨n, ⟨hn, hnd⟩, rfl⟩; exact hR n hn hnd
  have hhigh : dicksonHigh.ncard ≤ H * BugeaudEvertse.lineBound epsW := by
    calc dicksonHigh.ncard
        ≤ H * (linePoint '' dicksonHigh).ncard :=
          Set.ncard_le_mul_ncard_image hfin linePoint H hfib'
      _ ≤ H * (↑R : Set ℚ).ncard :=
          Nat.mul_le_mul (le_refl H) (Set.ncard_le_ncard himg R.finite_toSet)
      _ = H * R.card := by rw [Set.ncard_coe_finset]
      _ ≤ H * BugeaudEvertse.lineBound epsW := Nat.mul_le_mul (le_refl H) hcard
  have hsub : {n : ℕ | 1 ≤ n ∧ ¬ DicksonCond n} ⊆ ({1, 2} : Set ℕ) ∪ dicksonHigh := by
    rintro n ⟨hn1, hnd⟩
    rcases lt_or_ge n 3 with h | h
    · exact Or.inl (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; omega)
    · rcases le_or_gt n 256 with h256 | h256
      · exact absurd (dicksonCond_of_le_256 h h256) hnd
      · exact Or.inr ⟨by omega, hnd⟩
  calc {n : ℕ | 1 ≤ n ∧ ¬ DicksonCond n}.ncard
      ≤ (({1, 2} : Set ℕ) ∪ dicksonHigh).ncard :=
        Set.ncard_le_ncard hsub (((Set.finite_singleton 2).insert 1).union hfin)
    _ ≤ ({1, 2} : Set ℕ).ncard + dicksonHigh.ncard := Set.ncard_union_le _ _
    _ ≤ 2 + H * BugeaudEvertse.lineBound epsW := by
        have h2 : ({1, 2} : Set ℕ).ncard = 2 := Set.ncard_pair (by norm_num)
        omega

/-- **The Waring exception count**: `#{n ≥ 2 : g(n) ≠ 2ⁿ + ⌊(3/2)ⁿ⌋ − 2} ≤ H·K(ε_W)`, with **no
additive constant**.  Every exception fails Dickson's condition; `dicksonCond_of_le_256` clears
`[3, 256]`, and `n = 2` — which does fail Dickson's condition — satisfies the ideal formula
anyway, since `g(2) = 4 = 2² + 2 − 2` (`Nat.waringNumber_two`).  So every exception lies above the
cutoff, where the line cover applies.

Footprint `std3 + waringNumber_ideal_of_dickson + BugeaudEvertse.ridout_line_cover`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12" "Dic36", group "bugeaud_10_13"]
theorem waring_exceptions_card_le_of_heightBound (H : ℕ)
    (hfib : ∀ r : ℚ, (dicksonFibre r).ncard ≤ H) :
    {n : ℕ | 2 ≤ n ∧ Nat.waringNumber n ≠ 2 ^ n + waringQuot n - 2}.ncard
      ≤ H * BugeaudEvertse.lineBound epsW := by
  obtain ⟨R, hcard, hR⟩ := notDickson_line_cover
  have hfin : dicksonHigh.Finite := by
    apply Set.Finite.subset (R.finite_toSet.biUnion (fun r _ => dicksonFibre_finite r))
    rintro n ⟨hn, hnd⟩
    exact Set.mem_biUnion (hR n hn hnd) ⟨hn, hnd, rfl⟩
  have hsub : {n : ℕ | 2 ≤ n ∧ Nat.waringNumber n ≠ 2 ^ n + waringQuot n - 2} ⊆ dicksonHigh := by
    rintro n ⟨hn2, hne⟩
    have hnd : ¬ DicksonCond n := fun hd => hne (waringNumber_ideal_of_dickson n hn2 hd)
    refine ⟨?_, hnd⟩
    by_contra hlt
    rcases lt_or_ge n 3 with h | h
    · -- `n = 2`: the ideal formula holds although Dickson's condition fails
      have hn : n = 2 := by omega
      subst hn
      exact hne (by rw [Nat.waringNumber_two]; decide)
    · exact hnd (dicksonCond_of_le_256 h (by omega))
  have hfib' : ∀ r : ℚ, {n ∈ dicksonHigh | linePoint n = r}.ncard ≤ H := by
    intro r
    have heq : {n ∈ dicksonHigh | linePoint n = r} = dicksonFibre r := by
      ext n
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
    rw [heq]; exact hfib r
  have himg : linePoint '' dicksonHigh ⊆ ↑R := by
    rintro _ ⟨n, ⟨hn, hnd⟩, rfl⟩; exact hR n hn hnd
  calc {n : ℕ | 2 ≤ n ∧ Nat.waringNumber n ≠ 2 ^ n + waringQuot n - 2}.ncard
      ≤ dicksonHigh.ncard := Set.ncard_le_ncard hsub hfin
    _ ≤ H * (linePoint '' dicksonHigh).ncard :=
        Set.ncard_le_mul_ncard_image hfin linePoint H hfib'
    _ ≤ H * (↑R : Set ℚ).ncard :=
        Nat.mul_le_mul (le_refl H) (Set.ncard_le_ncard himg R.finite_toSet)
    _ = H * R.card := by rw [Set.ncard_coe_finset]
    _ ≤ H * BugeaudEvertse.lineBound epsW := Nat.mul_le_mul (le_refl H) hcard

/-! ### The secondary `(4/3)` condition and the full value dichotomy -/

/-- **The secondary `(4/3)`-event is empty for `n ≥ 6`** — `‖(4/3)ⁿ‖ ≥ (4/9)ⁿ` always holds
there (Zou/Pupyrev), so Bennett's `g₃`-condition needs no counting. -/
@[category research solved, AMS 11, ref "Zou13" "Pup14", group "bugeaud_10_13"]
theorem secondary_condition_holds {n : ℕ} (hn : 6 ≤ n) :
    ¬ distToNearestInt (((4 : ℝ) / 3) ^ n) < ((4 : ℝ) / 9) ^ n :=
  not_lt.mpr (distToNearestInt_four_thirds_ge n hn)

/-- **The full `g(n)` value dichotomy for `n ≥ 6`**: either Dickson's condition holds and `g(n)`
is the ideal formula `2ⁿ + ⌊(3/2)ⁿ⌋ - 2`, or it fails and `g(n)` is the Rubugunday–Niven fallback
`2ⁿ + ⌊(3/2)ⁿ⌋ + ⌊(4/3)ⁿ⌋ - (2 or 3)`.  The ideal branch holds off the finite exceptional set
(`waring_exceptions_finite`); this states `g(n)` completely on both branches.

The statement carries **no count clause**: the dichotomy is unconditional for `n ≥ 6`, whereas the
size of the fallback branch is conditional on a per-line bound.  The two are packaged together,
with their true footprints, in `waring_value_dichotomy_count`. -/
@[category research solved, AMS 11, ref "Bug12" "Rub42" "Niv44", group "bugeaud_10_13"]
theorem waring_value_dichotomy (n : ℕ) (hn : 6 ≤ n) :
    (DicksonCond n ∧ Nat.waringNumber n = 2 ^ n + waringQuot n - 2) ∨
    (¬ DicksonCond n ∧ Nat.waringNumber n
      = 2 ^ n + waringQuot n + waringQuot' n
        - (if waringQuot n * waringQuot' n + waringQuot n + waringQuot' n = 2 ^ n then 2 else 3)) := by
  by_cases hd : DicksonCond n
  · exact Or.inl ⟨hd, waringNumber_ideal_of_dickson n (by omega) hd⟩
  · exact Or.inr ⟨hd, (waringNumber_fallback n hn hd).2⟩

/-- **The dichotomy with its count clause** (the repaired form of the paper's Corollary 6.3).  For
every `n ≥ 6` the value `g(n)` is one of the two formulas, and — conditional on a per-line bound
`H` above the kernel range — the second branch occurs at most `H·K(ε_W)` times over all `n ≥ 2`.

Stating the two clauses together makes the footprint honest: the dichotomy needs the two cited
classical axioms, the count needs `waringNumber_ideal_of_dickson` and the line cover.  The first
version of this development printed a count clause on a dichotomy that carried none. -/
@[category research solved, AMS 11, ref "BE08" "Bug12" "Rub42" "Niv44", group "bugeaud_10_13"]
theorem waring_value_dichotomy_count (H : ℕ) (hfib : ∀ r : ℚ, (dicksonFibre r).ncard ≤ H) :
    (∀ n : ℕ, 6 ≤ n →
      (DicksonCond n ∧ Nat.waringNumber n = 2 ^ n + waringQuot n - 2) ∨
      (¬ DicksonCond n ∧ Nat.waringNumber n
        = 2 ^ n + waringQuot n + waringQuot' n
          - (if waringQuot n * waringQuot' n + waringQuot n + waringQuot' n = 2 ^ n then 2 else 3)))
    ∧ {n : ℕ | 2 ≤ n ∧ Nat.waringNumber n ≠ 2 ^ n + waringQuot n - 2}.ncard
        ≤ H * BugeaudEvertse.lineBound epsW :=
  ⟨fun n hn => waring_value_dichotomy n hn, waring_exceptions_card_le_of_heightBound H hfib⟩

end BB13
