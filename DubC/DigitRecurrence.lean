/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC.ReturnEngine
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Floor
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.LinearCombination

/-!
# Digit dynamics of `⌊ξ·aⁿ⌋`, and Regime 1 of the 1967 problem

The 1967 Forman–Shapiro question (= [DubOst06] Conjecture 2) asks whether `⌊ξ·aⁿ⌋` contains
infinitely many composite terms for every real `ξ > 0` and every integer `a ≥ 2`.  This file
sets up the elementary dynamics that turns the question into a statement about **digit words**,
and disposes of the *eventually periodic* case by feeding it to the [Dub09] Theorem 4 engine of
`DubC/ReturnEngine.lean`.

## The dynamics

With `xₙ = ⌊ξaⁿ⌋` and `dₙ = ⌊a·{ξaⁿ}⌋ ∈ {0,…,a-1}` one has the one-step recurrence

  `x_{n+1} = a · xₙ + dₙ`     (`DubC.floorPow_succ`)

so the orbit is a base-`a` "append a digit" walk, and `ξ` enters only through the digit word.

## The reduction (the heart of milestone M1′)

**If the digit word is eventually periodic** with period `L` from `n₀` on, then along the
arithmetic progression `n₀, n₀+L, n₀+2L, …` the sequence satisfies a `d = 1` return
recurrence with a **constant** inhomogeneity,

  `x_{n₀+(k+1)L} = a^L · x_{n₀+kL} + C`,    `C = Σ_{i<L} a^{L-1-i} d_{n₀+i}`

(`DubC.isReturnRec_progression`), which is exactly the hypothesis of [Dub09] Theorem 4 with
`d = 1`, `c = a^L`.  Since `|xₙ| → ∞` for `ξ > 0`, that theorem yields infinitely many
composites (`DubC.infinite_composites_of_periodic_digits`).

Note that this route never passes through "`ξ` is rational": eventual periodicity of the digit
word is *used directly*.  That is what makes `Certificate.lean` — where periodicity of the word
is what the zero-entropy certificate delivers — reduce to this file with nothing left over.

## Regime 1

For rational `ξ` the fractional-part orbit `{ξaⁿ}` is finite, so the digit word *is* eventually
periodic ([Dub09] Lemma 6, easy direction) and we obtain unconditionally, for every base:

  `DubC.infinite_composites_floorPow_of_rat` — for rational `ξ > 0` and `a ≥ 2`, the sequence
  `⌊ξaⁿ⌋` contains infinitely many composite terms.

## References

* **[Dub09]** A. Dubickas, *Prime and composite integers close to powers of a number*,
  Monatsh. Math. **158** (2009) 271–284.  Theorem 4; Lemma 6.
* **[DubOst06]** A. Dubickas, *Truncatable primes and unavoidable sets of divisors*,
  Acta Math. Univ. Ostrav. **14** (2006) 21–25.  Conjecture 2.
-/

namespace DubC

open Filter

/-! ### The sequence and its digits -/

/-- The sequence `⌊ξ·aⁿ⌋` of the 1967 Forman–Shapiro problem. -/
noncomputable def floorPow (ξ : ℝ) (a : ℕ) (n : ℕ) : ℤ := ⌊ξ * (a : ℝ) ^ n⌋

/-- The `n`-th base-`a` digit driving `⌊ξ·aⁿ⌋`, namely `dₙ = ⌊a·{ξaⁿ}⌋ ∈ {0,…,a-1}`. -/
noncomputable def floorDigit (ξ : ℝ) (a : ℕ) (n : ℕ) : ℤ :=
  ⌊(a : ℝ) * Int.fract (ξ * (a : ℝ) ^ n)⌋

/-- The append-a-digit recurrence `x_{n+1} = a·xₙ + dₙ`. -/
@[category API, AMS 11, ref "Dub09", group "dubc_digit_recurrence"]
theorem floorPow_succ (ξ : ℝ) (a n : ℕ) :
    floorPow ξ a (n + 1) = (a : ℤ) * floorPow ξ a n + floorDigit ξ a n := by
  have hy : ξ * (a : ℝ) ^ (n + 1)
      = (((a : ℤ) * ⌊ξ * (a : ℝ) ^ n⌋ : ℤ) : ℝ) + (a : ℝ) * Int.fract (ξ * (a : ℝ) ^ n) := by
    rw [Int.fract]
    push_cast
    rw [pow_succ]
    ring
  rw [floorPow, floorPow, floorDigit, hy, Int.floor_intCast_add]

@[category API, AMS 11, ref "Dub09", group "dubc_digit_recurrence"]
theorem floorDigit_nonneg (ξ : ℝ) (a n : ℕ) : 0 ≤ floorDigit ξ a n :=
  Int.floor_nonneg.mpr (mul_nonneg (by positivity) (Int.fract_nonneg _))

@[category API, AMS 11, ref "Dub09", group "dubc_digit_recurrence"]
theorem floorDigit_lt (ξ : ℝ) {a : ℕ} (ha : 0 < a) (n : ℕ) : floorDigit ξ a n < (a : ℤ) := by
  rw [floorDigit, Int.floor_lt]
  have h0 : (0 : ℝ) < (a : ℝ) := by positivity
  have h1 := Int.fract_lt_one (ξ * (a : ℝ) ^ n)
  push_cast
  nlinarith

/-- For `ξ > 0` and `a ≥ 2` the sequence `⌊ξaⁿ⌋` tends to infinity in absolute value — the
growth hypothesis of [Dub09] Theorem 4. -/
@[category API, AMS 11, ref "Dub09", group "dubc_digit_recurrence"]
theorem tendsto_natAbs_floorPow {a : ℕ} (ha : 2 ≤ a) {ξ : ℝ} (hξ : 0 < ξ) :
    Tendsto (fun n => (floorPow ξ a n).natAbs) atTop atTop := by
  have hone : (1 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : 1 < a)
  have hpow : Tendsto (fun n : ℕ => ξ * (a : ℝ) ^ n) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hξ (tendsto_pow_atTop_atTop_of_one_lt hone)
  refine Filter.tendsto_atTop_atTop.mpr fun B => ?_
  obtain ⟨N, hN⟩ := Filter.tendsto_atTop_atTop.mp hpow ((B : ℝ) + 1)
  refine ⟨N, fun n hn => ?_⟩
  have h1 : ((B : ℤ) + 1) ≤ floorPow ξ a n := by
    refine Int.le_floor.mpr ?_
    push_cast
    exact hN n hn
  have h2 : ((floorPow ξ a n).natAbs : ℤ) = floorPow ξ a n :=
    Int.natAbs_of_nonneg (by omega)
  omega

/-! ### From an eventually periodic digit word to a return recurrence -/

/-- `tailSum a d n L = Σ_{i<L} a^{L-1-i} · d_{n+i}`, in the recursive form that makes
`x_{n+L} = a^L xₙ + tailSum a d n L` a one-line induction. -/
def tailSum (a : ℤ) (dg : ℕ → ℤ) (n : ℕ) : ℕ → ℤ
  | 0 => 0
  | L + 1 => a * tailSum a dg n L + dg (n + L)

/-- Iterating the append-a-digit recurrence `L` times. -/
@[category API, AMS 11, ref "Dub09", group "dubc_digit_recurrence"]
theorem shift_eq (a : ℤ) {x dg : ℕ → ℤ} (h : ∀ n, x (n + 1) = a * x n + dg n) (n L : ℕ) :
    x (n + L) = a ^ L * x n + tailSum a dg n L := by
  induction L with
  | zero => simp [tailSum]
  | succ L ih =>
    have hidx : n + (L + 1) = (n + L) + 1 := by omega
    rw [hidx, h (n + L), ih, tailSum]
    ring

/-- An `L`-periodic digit word (from `n₀` on) has `L`-periodic `tailSum`. -/
@[category API, AMS 11, ref "Dub09", group "dubc_digit_recurrence"]
theorem tailSum_shift (a : ℤ) {dg : ℕ → ℤ} {n₀ L : ℕ}
    (hd : ∀ m, n₀ ≤ m → dg (m + L) = dg m) {n : ℕ} (hn : n₀ ≤ n) (L' : ℕ) :
    tailSum a dg (n + L) L' = tailSum a dg n L' := by
  induction L' with
  | zero => rfl
  | succ L' ih =>
    rw [tailSum, tailSum, ih]
    congr 1
    have hidx : n + L + L' = (n + L') + L := by omega
    rw [hidx, hd (n + L') (by omega)]

/-- **Eventually periodic digits give a `d = 1` return recurrence along a progression.**
If `x_{n+1} = a·xₙ + dₙ` and the digit word has period `L` from `n₀` on, then
`k ↦ x_{n₀+kL}` satisfies `y_{k+1} = a^L·y_k + C` with the *constant* `C = tailSum a d n₀ L`
— the hypothesis of [Dub09] Theorem 4 with `d = 1` and `c = a^L`. -/
@[category research solved, AMS 11, ref "Dub09", group "dubc_digit_recurrence"]
theorem isReturnRec_progression (a : ℤ) {x dg : ℕ → ℤ} (h : ∀ n, x (n + 1) = a * x n + dg n)
    {n₀ L : ℕ} (hd : ∀ m, n₀ ≤ m → dg (m + L) = dg m) :
    IsReturnRec 0 (a ^ L) (fun _ => tailSum a dg n₀ L) (fun k => x (n₀ + k * L)) := by
  have hconst : ∀ k : ℕ, tailSum a dg (n₀ + k * L) L = tailSum a dg n₀ L := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hidx : n₀ + (k + 1) * L = (n₀ + k * L) + L := by ring
      rw [hidx, tailSum_shift a hd (by omega) L, ih]
  intro k
  show x (n₀ + (k + 0 + 1) * L) = a ^ L * x (n₀ + k * L) + tailSum a dg n₀ L
  have hidx : n₀ + (k + 0 + 1) * L = (n₀ + k * L) + L := by ring
  rw [hidx, shift_eq a h (n₀ + k * L) L, hconst k]

/-- **The M1′ reduction.**  An eventually periodic digit word plus unbounded growth forces
infinitely many composite terms.  (Combines `isReturnRec_progression` with [Dub09] Thm 4.) -/
@[category research solved, AMS 11, ref "Dub09", group "dubc_digit_recurrence"]
theorem infinite_composites_of_periodic_digits {a : ℤ} (ha : a ≠ 0) {x dg : ℕ → ℤ}
    (h : ∀ n, x (n + 1) = a * x n + dg n) {n₀ L : ℕ} (hL : 0 < L)
    (hd : ∀ m, n₀ ≤ m → dg (m + L) = dg m)
    (hlim : Tendsto (fun n => (x n).natAbs) atTop atTop) :
    {n | CompositeInt (x n)}.Infinite := by
  -- the progression `k ↦ n₀ + k*L` tends to infinity, so the subsequence still grows
  have hprog : Tendsto (fun k : ℕ => n₀ + k * L) atTop atTop := by
    refine Filter.tendsto_atTop_atTop.mpr fun B => ⟨B, fun k hk => ?_⟩
    have h1 : k * 1 ≤ k * L := Nat.mul_le_mul (le_refl k) hL
    omega
  have hsub : Tendsto (fun k => (x (n₀ + k * L)).natAbs) atTop atTop := hlim.comp hprog
  have hcomp := infinite_composites (fun q => congrPreserving_const q _)
    (isReturnRec_progression a h hd) (pow_ne_zero L ha) hsub
  have hsubset : (fun k : ℕ => n₀ + k * L) '' {k | CompositeInt (x (n₀ + k * L))}
      ⊆ {n | CompositeInt (x n)} := by
    rintro n ⟨k, hk, rfl⟩
    exact hk
  have hinj : Set.InjOn (fun k : ℕ => n₀ + k * L) {k | CompositeInt (x (n₀ + k * L))} := by
    intro p _ q _ hpq
    have hpq' : n₀ + p * L = n₀ + q * L := hpq
    have h1 : p * L = q * L := by omega
    exact Nat.eq_of_mul_eq_mul_right hL h1
  exact Set.Infinite.mono hsubset (hcomp.image hinj)

/-! ### Regime 1: rational `ξ` -/

/-- The base-`a` fractional-part orbit: `{ξ·aⁿ⁺¹} = {a·{ξ·aⁿ}}`. -/
@[category API, AMS 11, ref "Dub09", group "dubc_digit_recurrence"]
theorem fract_pow_succ (ξ : ℝ) (a n : ℕ) :
    Int.fract (ξ * (a : ℝ) ^ (n + 1)) = Int.fract ((a : ℝ) * Int.fract (ξ * (a : ℝ) ^ n)) := by
  refine Int.fract_eq_fract.mpr ⟨(a : ℤ) * ⌊ξ * (a : ℝ) ^ n⌋, ?_⟩
  rw [Int.fract]
  push_cast
  rw [pow_succ]
  ring

/-- **[Dub09] Lemma 6, easy direction.**  For rational `ξ` the base-`a` digit word of `ξ` is
eventually periodic: the fractional-part orbit `{ξaⁿ}` takes only the `v` values `j/v`. -/
@[category research solved, AMS 11, ref "Dub09", group "dubc_digit_recurrence"]
theorem digits_eventually_periodic_of_rat {ξ : ℝ} (a : ℕ) (u : ℤ) {v : ℕ} (hv : 0 < v)
    (hξ : ξ = (u : ℝ) / (v : ℝ)) :
    ∃ n₀ L, 0 < L ∧ ∀ m, n₀ ≤ m → floorDigit ξ a (m + L) = floorDigit ξ a m := by
  have : NeZero v := ⟨by omega⟩
  -- the orbit is `((u aⁿ) mod v)/v`, so it is determined by a residue class mod `v`
  have hval : ∀ n : ℕ,
      Int.fract (ξ * (a : ℝ) ^ n) = (((u * (a : ℤ) ^ n) % (v : ℤ) : ℤ) : ℝ) / (v : ℝ) := by
    intro n
    have hrw : ξ * (a : ℝ) ^ n = ((u * (a : ℤ) ^ n : ℤ) : ℝ) / ((v : ℕ) : ℝ) := by
      rw [hξ]; push_cast; ring
    rw [hrw]
    exact Int.fract_div_intCast_eq_div_intCast_mod
  have hcongr : ∀ m n : ℕ, ((u * (a : ℤ) ^ m : ℤ) : ZMod v) = ((u * (a : ℤ) ^ n : ℤ) : ZMod v) →
      Int.fract (ξ * (a : ℝ) ^ m) = Int.fract (ξ * (a : ℝ) ^ n) := by
    intro m n hmn
    have hmod := (ZMod.intCast_eq_intCast_iff _ _ _).mp hmn
    rw [hval m, hval n, Int.ModEq.eq hmod]
  -- pigeonhole: two orbit points coincide
  obtain ⟨n₁, n₂, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ => ((u * (a : ℤ) ^ n : ℤ) : ZMod v))
  -- propagate periodicity forwards through the orbit map `t ↦ {a·t}`
  have main : ∀ p q : ℕ, p < q → Int.fract (ξ * (a : ℝ) ^ p) = Int.fract (ξ * (a : ℝ) ^ q) →
      ∃ n₀ L, 0 < L ∧ ∀ m, n₀ ≤ m →
        Int.fract (ξ * (a : ℝ) ^ (m + L)) = Int.fract (ξ * (a : ℝ) ^ m) := by
    intro p q hpq hfe
    obtain ⟨L, hL, rfl⟩ : ∃ L, 0 < L ∧ q = p + L := ⟨q - p, by omega, by omega⟩
    refine ⟨p, L, hL, ?_⟩
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact hfe.symm
    | succ m hpm ih =>
      have e1 : m + 1 + L = (m + L) + 1 := by omega
      rw [e1, fract_pow_succ, ih, ← fract_pow_succ]
  have hexists : ∃ n₀ L, 0 < L ∧ ∀ m, n₀ ≤ m →
      Int.fract (ξ * (a : ℝ) ^ (m + L)) = Int.fract (ξ * (a : ℝ) ^ m) := by
    rcases lt_trichotomy n₁ n₂ with h | h | h
    · exact main n₁ n₂ h (hcongr _ _ heq)
    · exact absurd h hne
    · exact main n₂ n₁ h (hcongr _ _ heq.symm)
  obtain ⟨n₀, L, hL, hper⟩ := hexists
  refine ⟨n₀, L, hL, fun m hm => ?_⟩
  rw [floorDigit, floorDigit, hper m hm]

/-- **Regime 1 of the 1967 Forman–Shapiro problem, for every base.**  For every rational
`ξ > 0` and every integer base `a ≥ 2`, the sequence `⌊ξ·aⁿ⌋` contains infinitely many
composite terms.  ([Dub09] Theorem 4 applied through the digit dynamics; unconditional.) -/
@[category research solved, AMS 11, ref "Dub09" "DubOst06", group "dubc_digit_recurrence"]
theorem infinite_composites_floorPow_of_rat {a : ℕ} (ha : 2 ≤ a) {ξ : ℝ} (hpos : 0 < ξ)
    (u : ℤ) {v : ℕ} (hv : 0 < v) (hξ : ξ = (u : ℝ) / (v : ℝ)) :
    {n | CompositeInt (floorPow ξ a n)}.Infinite := by
  obtain ⟨n₀, L, hL, hper⟩ := digits_eventually_periodic_of_rat a u hv hξ
  exact infinite_composites_of_periodic_digits (a := (a : ℤ)) (by positivity)
    (floorPow_succ _ a) hL hper (tendsto_natAbs_floorPow ha hpos)

end DubC
