/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TH.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The Dubickas run cap and the escape ladder for `(3/2)ⁿ`

Angle **A13** of plan-A1+ (§5), work package W11: the *density-vs-runs bookkeeping* that target
**N1** (`δ₀ ∉ limitMeasures 1`) asks for.  This file is the elementary half — pure `ℚ`/`ℤ`/`ℕ`
arithmetic on the objects of `TH/Basic.lean`, no measures and no solenoid.  The measure-theoretic
half, which converts `δ₀ ∈ limitMeasures ξ` into a density statement about exactly the set counted
here, is `TH/Solenoid/NonDegeneracy.lean`.

## The mechanism

Write `(3/2)ⁿ = mₙ + εₙ` with `εₙ ∈ [-1/2, 1/2)` and `εₙ = Rₙ/2ⁿ`, `Rₙ` odd for `n ≥ 1`
(`TH.R_emod_two`).  Say the orbit **escapes** at time `n` when `|εₙ| ≥ 1/5`.  Two facts collide:

* **inside a confinement the step is exact.**  If `|εₙ| < 1/5` and `|εₙ₊₁| < 1/5` then the steering
  letter `tₙ = 3εₙ − 2εₙ₊₁` has `|tₙ| < 1`, and `tₙ` is an integer, so `tₙ = 0` and
  `εₙ₊₁ = (3/2)εₙ` *exactly* — equivalently `Rₙ₊₁ = 3Rₙ`.  Over a confined block `[a, a+k]` this
  iterates to `R_{a+k} = 3ᵏ Rₐ` (`R_add_of_confined`).
* **the denominator floor.**  `Rₐ` is odd, hence `|Rₐ| ≥ 1`, so `|R_{a+k}| ≥ 3ᵏ`; but confinement at
  the right end says `5|R_{a+k}| < 2^{a+k}`.

Hence the **run cap** `5·3ᵏ < 2^{a+k}` (`run_cap`), i.e. `k < a·log 2/log(3/2) = 1.7095…·a`: the
Dubickas slope, whose per-run form the corpus already owns (`RB/DubickasFloor.lean`,
`RB.dubickasConst`; that file is *not* imported here — only the constant is quoted).  In the
multiplied form `5·3ᵇ < 2ᵇ·3ᵃ` (`confined_cap`) it gives the crude but purely combinatorial
consequence `b < 3a` (`lt_three_mul_of_confined`), which is what the counting below runs on.

## What the cap does and does not give

**Positive half** (`escape_ladder`): every `N` satisfies `N + 2 ≤ 5·3^{escCount N}`, so the orbit
must leave the `1/5`-neighbourhood of `ℤ` at least `log₃((N+2)/5)` times before time `N`.  That is a
genuine quantitative statement and, as far as this repository's ledger goes, a new one — but it is
only *logarithmically* many escapes.

**Negative half** (`ladder_permits_density_zero`): the ladder cannot be pushed further by
bookkeeping alone.  The abstract property the escape set satisfies (`LadderProperty`: every `b ≥ 1`
has a member `n ≤ b` with `b < 3n + 3`) is *also* satisfied by the powers of three, whose density is
`0`.  So "escapes at least logarithmically often" is consistent with "escapes have density `0`",
i.e. with full-density confinement.  **A13-N1 does not follow from the Dubickas run cap**; it needs
a genuinely new input at the level of densities.  This is the probe's verdict, machine-checked
rather than asserted.

## Main statements

* `Escapes`, `escCount` — the escape predicate and its counting function.
* `t_eq_zero_of_not_escapes`, `R_add_of_confined` — exactness of the step inside a confinement.
* `run_cap`, `confined_cap`, `run_cap_real` — the cap, in integer and Dubickas-slope form.
* `lt_three_mul_of_confined`, `exists_max_escape` — the combinatorial form and the escape locator.
* `escape_ladder`, `log_le_escCount` — the ladder, integer and logarithmic form.
* `LadderProperty`, `ladderProperty_escapes`, `ladder_permits_density_zero` — the no-go.

## Claim level

The run cap and the ladder are formalization of a standard mechanism ([Dub09], the `2⁻ⁿ` repulsion
floor) in a form this repository had not stated; the no-go is a statement about the *method*, not
about `(3/2)ⁿ`.  Nothing here decides A13-N1.  `std3` throughout: no cited axiom, no `sorry`, no
`native_decide`.

## References

* `plans/plan-A1+.html` §5 (angle A13, targets N1–N5), §7.2 (W11).
* `plans/report2-weyl.html` §7 Table D (A13).
* [Dub09] A. Dubickas, *Powers of a rational number modulo 1 cannot lie in a small interval*,
  Acta Arith. **137** (2009), 233–239.  The slope `log 2/log(3/2)` is `RB.dubickasConst`
  (`RB/DubickasFloor.lean`).
* [M4A3] `plan-M4A3.html` §2–3 for `m`, `eps`, `R`, `t` (`TH/Basic.lean`).
-/

namespace TH

open Filter Topology

/-! ## Escapes -/

/-- The orbit **escapes** at time `n` when `(3/2)ⁿ` is at distance at least `1/5` from `ℤ`.
The threshold `1/5` is forced: `|tₙ| ≤ 3|εₙ| + 2|εₙ₊₁| < 1` needs `|ε| < 1/5` at both ends. -/
@[category API, AMS 11 37, ref "A1plus", group "weyl_a13_limitmeasures"]
def Escapes (n : ℕ) : Prop := 1 / 5 ≤ |eps n|

instance decidableEscapes (n : ℕ) : Decidable (Escapes n) :=
  inferInstanceAs (Decidable (1 / 5 ≤ |eps n|))

/-- The orbit starts on an integer, so time `0` is not an escape. -/
@[category test, AMS 11 37, ref "A1plus", group "weyl_a13_limitmeasures"]
theorem not_escapes_zero : ¬ Escapes 0 := by
  show ¬ ((1 : ℚ) / 5 ≤ |eps 0|)
  rw [eps_zero]
  norm_num

/-- `ε₁ = −1/2`, so time `1` is an escape: the escape set is never empty. -/
@[category test, AMS 11 37, ref "A1plus", group "weyl_a13_limitmeasures"]
theorem escapes_one : Escapes 1 := by
  show (1 : ℚ) / 5 ≤ |eps 1|
  have h : eps 1 = -(1 / 2) := by
    unfold eps
    rw [m_one]
    norm_num
  rw [h]
  norm_num

/-! ## The step is exact inside a confinement -/

/-- **Confinement kills the steering letter.**  `tₙ = 3εₙ − 2εₙ₊₁` is an integer of modulus `< 1`
as soon as both `|εₙ|` and `|εₙ₊₁|` are `< 1/5`. -/
@[category research solved, AMS 11 37, ref "A1plus", group "weyl_a13_limitmeasures"]
theorem t_eq_zero_of_not_escapes {n : ℕ} (h : ¬ Escapes n) (h' : ¬ Escapes (n + 1)) : t n = 0 := by
  have h1 : |eps n| < 1 / 5 := lt_of_not_ge h
  have h2 : |eps (n + 1)| < 1 / 5 := lt_of_not_ge h'
  rw [abs_lt] at h1 h2
  have ht := t_eq_eps n
  have hq : |(t n : ℚ)| < 1 := by
    rw [ht, abs_lt]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hz : |t n| < 1 := by exact_mod_cast hq
  rw [abs_lt] at hz
  omega

/-- With a vanishing steering letter the numerator is multiplied by exactly `3`. -/
@[category API, AMS 11 37, ref "A1plus", group "weyl_a13_limitmeasures"]
theorem R_succ_of_t_zero {n : ℕ} (h : t n = 0) : R (n + 1) = 3 * R n := by
  have h1 : eps (n + 1) = 3 / 2 * eps n := by
    rw [eps_succ, h]
    push_cast
    ring
  have h2 := two_pow_mul_eps (n + 1)
  have h3 := two_pow_mul_eps n
  have hq : ((R (n + 1) : ℚ)) = 3 * (R n : ℚ) := by
    rw [← h2, h1, ← h3]
    ring
  exact_mod_cast hq

/-- **Exactness over a confined block.**  If the orbit stays within `1/5` of `ℤ` throughout
`[a, a+k]` then `R_{a+k} = 3ᵏ Rₐ` — the orbit is on a pure `×(3/2)` branch for the whole block. -/
@[category research solved, AMS 11 37, ref "A1plus", group "weyl_a13_limitmeasures"]
theorem R_add_of_confined {a k : ℕ} (h : ∀ i, i ≤ k → ¬ Escapes (a + i)) :
    R (a + k) = 3 ^ k * R a := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk : R (a + k) = 3 ^ k * R a := ih fun i hi => h i (by omega)
      have hnext : ¬ Escapes (a + k + 1) := by
        have := h (k + 1) le_rfl
        rwa [show a + (k + 1) = a + k + 1 by omega] at this
      have ht : t (a + k) = 0 := t_eq_zero_of_not_escapes (h k (by omega)) hnext
      rw [show a + (k + 1) = a + k + 1 by omega, R_succ_of_t_zero ht, hk]
      ring

/-! ## The run cap -/

/-- `Rₙ` is odd for `n ≥ 1`, hence nonzero: the `2⁻ⁿ` repulsion floor. -/
@[category API, AMS 11 37, ref "A1plus", group "weyl_a13_limitmeasures"]
theorem one_le_abs_R {n : ℕ} (hn : 1 ≤ n) : 1 ≤ |R n| := by
  have hodd := R_emod_two n hn
  have hne : R n ≠ 0 := by
    intro h
    rw [h] at hodd
    simp at hodd
  exact Int.one_le_abs hne

/-- Non-escape at time `n` in numerator form: `5|Rₙ| < 2ⁿ`. -/
@[category API, AMS 11 37, ref "A1plus", group "weyl_a13_limitmeasures"]
theorem five_mul_abs_R_lt {n : ℕ} (h : ¬ Escapes n) : 5 * |R n| < (2 : ℤ) ^ n := by
  have h1 : |eps n| < 1 / 5 := lt_of_not_ge h
  have h2 : (0 : ℚ) < 2 ^ n := by positivity
  have h3 : |(R n : ℚ)| = 2 ^ n * |eps n| := by
    rw [← two_pow_mul_eps n, abs_mul, abs_of_pos h2]
  have hq : (5 : ℚ) * |(R n : ℚ)| < 2 ^ n := by
    rw [h3]
    nlinarith
  have hc : ((5 * |R n| : ℤ) : ℚ) < ((2 ^ n : ℤ) : ℚ) := by push_cast; linarith
  exact_mod_cast hc

/-- **The run cap** ([Dub09]'s slope, in exact integer form).  A block `[a, a+k]` with `a ≥ 1` on
which the orbit never escapes forces `5·3ᵏ < 2^{a+k}`: the block cannot be longer than
`log 2/log(3/2) · a`. -/
@[category research solved, AMS 11 37, ref "Dub09" "A1plus", group "weyl_a13_limitmeasures"]
theorem run_cap {a k : ℕ} (ha : 1 ≤ a) (h : ∀ i, i ≤ k → ¬ Escapes (a + i)) :
    5 * 3 ^ k < 2 ^ (a + k) := by
  have h1 : R (a + k) = 3 ^ k * R a := R_add_of_confined h
  have h2 : 1 ≤ |R a| := one_le_abs_R ha
  have h3 : 5 * |R (a + k)| < (2 : ℤ) ^ (a + k) := five_mul_abs_R_lt (h k le_rfl)
  rw [h1, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ 3 ^ k)] at h3
  have h4 : (0 : ℤ) < 3 ^ k := by positivity
  have h5 : (5 : ℤ) * 3 ^ k ≤ 5 * (3 ^ k * |R a|) := by nlinarith
  have : (5 : ℤ) * 3 ^ k < 2 ^ (a + k) := lt_of_le_of_lt h5 h3
  exact_mod_cast this

/-- The run cap in endpoint form: `5·3ᵇ < 2ᵇ·3ᵃ` for a confined block `[a, b]`, `1 ≤ a ≤ b`. -/
@[category research solved, AMS 11 37, ref "Dub09" "A1plus", group "weyl_a13_limitmeasures"]
theorem confined_cap {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b)
    (h : ∀ n, a ≤ n → n ≤ b → ¬ Escapes n) : 5 * 3 ^ b < 2 ^ b * 3 ^ a := by
  obtain ⟨k, rfl⟩ : ∃ k, b = a + k := ⟨b - a, by omega⟩
  have hcap : 5 * 3 ^ k < 2 ^ (a + k) :=
    run_cap (a := a) (k := k) ha fun i hi => h (a + i) (by omega) (by omega)
  calc 5 * 3 ^ (a + k) = 3 ^ a * (5 * 3 ^ k) := by ring
    _ < 3 ^ a * 2 ^ (a + k) := by
        exact mul_lt_mul_of_pos_left hcap (by positivity)
    _ = 2 ^ (a + k) * 3 ^ a := by ring

private theorem pow_aux {a b : ℕ} (h : 3 * a ≤ b) : 2 ^ b * 3 ^ a ≤ 3 ^ b := by
  obtain ⟨r, rfl⟩ : ∃ r, b = 3 * a + r := ⟨b - 3 * a, by omega⟩
  have e1 : (2 : ℕ) ^ (3 * a + r) * 3 ^ a = 24 ^ a * 2 ^ r := by
    rw [pow_add, pow_mul, show ((2 : ℕ) ^ 3) = 8 from rfl, show (24 : ℕ) = 8 * 3 from rfl, mul_pow]
    ring
  have e2 : (3 : ℕ) ^ (3 * a + r) = 27 ^ a * 3 ^ r := by
    rw [pow_add, pow_mul]
    norm_num
  rw [e1, e2]
  exact Nat.mul_le_mul (Nat.pow_le_pow_left (by norm_num) a) (Nat.pow_le_pow_left (by norm_num) r)

/-- **The combinatorial form of the cap.**  A confined block `[a, b]` with `a ≥ 1` satisfies
`b < 3a`.  The constant `3` is crude — the sharp one is `1 + log 2/log(3/2) = 2.7095…`
(`run_cap_real`) — but it is an inequality between natural numbers, which is what the counting
argument of `escape_ladder` needs. -/
@[category research solved, AMS 11 37, ref "Dub09" "A1plus", group "weyl_a13_limitmeasures"]
theorem lt_three_mul_of_confined {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b)
    (h : ∀ n, a ≤ n → n ≤ b → ¬ Escapes n) : b < 3 * a := by
  by_contra hcon
  have h3 : 3 * a ≤ b := not_lt.mp hcon
  have hc := confined_cap ha hab h
  have hp := pow_aux h3
  have hpos : 0 < (3 : ℕ) ^ b := by positivity
  omega

/-- **The Dubickas slope.**  The real form of `run_cap`: a confined block starting at `a ≥ 1` has
length `k < a · log 2 / log(3/2)`.  The constant is `RB.dubickasConst = 1.70951…`
(`RB/DubickasFloor.lean`, not imported here). -/
@[category research solved, AMS 11 37, ref "Dub09" "A1plus", group "weyl_a13_limitmeasures"]
theorem run_cap_real {a k : ℕ} (ha : 1 ≤ a) (h : ∀ i, i ≤ k → ¬ Escapes (a + i)) :
    (k : ℝ) < Real.log 2 / Real.log (3 / 2) * a := by
  have hcap : (5 : ℝ) * 3 ^ k < 2 ^ (a + k) := by exact_mod_cast run_cap ha h
  have hlog := Real.log_lt_log (by positivity) hcap
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow] at hlog
  have h5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have hd : Real.log (3 / 2 : ℝ) = Real.log 3 - Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
  have hdpos : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
  have hkey : (k : ℝ) * Real.log (3 / 2) < (a : ℝ) * Real.log 2 := by
    rw [hd]
    push_cast at hlog
    nlinarith [hlog, h5]
  rw [div_mul_eq_mul_div, lt_div_iff₀ hdpos]
  linarith [hkey]

/-! ## The escape ladder -/

/-- Locate the **last** escape before `b`, together with the cap it obeys. -/
@[category research solved, AMS 11 37, ref "A1plus", group "weyl_a13_limitmeasures"]
theorem exists_max_escape {b : ℕ} (hb : 1 ≤ b) :
    ∃ g, 1 ≤ g ∧ g ≤ b ∧ Escapes g ∧ (∀ k, g < k → k ≤ b → ¬ Escapes k) ∧ b < 3 * g + 3 := by
  classical
  set S := (Finset.Icc 1 b).filter Escapes with hS
  have h1 : (1 : ℕ) ∈ S := by
    rw [hS, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_rfl, hb⟩, escapes_one⟩
  have hne : S.Nonempty := ⟨1, h1⟩
  set g := S.max' hne with hg
  have hgS : g ∈ S := S.max'_mem hne
  rw [hS, Finset.mem_filter, Finset.mem_Icc] at hgS
  obtain ⟨⟨hg1, hgb⟩, hgE⟩ := hgS
  have hmax : ∀ k, g < k → k ≤ b → ¬ Escapes k := by
    intro k hk1 hk2 hkE
    have hkS : k ∈ S := by
      rw [hS, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, hk2⟩, hkE⟩
    have := S.le_max' k hkS
    omega
  refine ⟨g, hg1, hgb, hgE, hmax, ?_⟩
  rcases eq_or_lt_of_le hgb with h | h
  · omega
  · have hlt : b < 3 * (g + 1) :=
      lt_three_mul_of_confined (by omega) (by omega) fun n hn1 hn2 => hmax n (by omega) hn2
    omega

/-- The number of escapes among the dates `n < N` (the `Z32` counting convention). -/
@[category API, AMS 11 37, ref "A1plus", group "weyl_a13_limitmeasures"]
def escCount (N : ℕ) : ℕ := ((Finset.range N).filter Escapes).card

/-- **The escape ladder.**  `N + 2 ≤ 5·3^{escCount N}`: before time `N` the orbit of `(3/2)ⁿ` must
leave the `1/5`-neighbourhood of `ℤ` at least `log₃((N+2)/5)` times.

The proof is the run cap plus one pigeonhole: the last escape `g < N` satisfies `N − 1 < 3g + 3`
(`exists_max_escape`), and everything before it is the same statement at `g`. -/
@[category research solved, AMS 11 37, ref "Dub09" "A1plus", group "weyl_a13_limitmeasures"]
theorem escape_ladder (N : ℕ) : N + 2 ≤ 5 * 3 ^ escCount N := by
  classical
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases Nat.lt_or_ge N 2 with hN | hN
    · have hzero : (Finset.range N).filter Escapes = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro x hx
        rw [Finset.mem_range] at hx
        rw [show x = 0 by omega]
        exact not_escapes_zero
      rw [escCount, hzero]
      simp only [Finset.card_empty, pow_zero, mul_one]
      omega
    obtain ⟨g, hg1, hgb, hgE, hmax, hlt⟩ := exists_max_escape (b := N - 1) (by omega)
    have hsplit : (Finset.range N).filter Escapes = insert g ((Finset.range g).filter Escapes) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
      constructor
      · rintro ⟨hk1, hkE⟩
        rcases lt_trichotomy k g with hkg | hkg | hkg
        · exact Or.inr ⟨hkg, hkE⟩
        · exact Or.inl hkg
        · exact absurd hkE (hmax k hkg (by omega))
      · rintro (rfl | ⟨hk1, hkE⟩)
        · exact ⟨by omega, hgE⟩
        · exact ⟨by omega, hkE⟩
    have hnot : g ∉ (Finset.range g).filter Escapes := by
      rw [Finset.mem_filter, Finset.mem_range]
      rintro ⟨h1, _⟩
      omega
    have hcard : escCount N = escCount g + 1 := by
      rw [escCount, hsplit, Finset.card_insert_of_notMem hnot, escCount]
    have hih := ih g (by omega)
    set P := 3 ^ escCount g with hP
    have hPpos : 0 < P := by rw [hP]; positivity
    have hpow : 3 ^ escCount N = 3 * P := by
      rw [hcard, hP, pow_succ]
      ring
    rw [hpow]
    omega

/-- The ladder in logarithmic form: `log((N+2)/5) / log 3 ≤ escCount N`. -/
@[category research solved, AMS 11 37, ref "Dub09" "A1plus", group "weyl_a13_limitmeasures"]
theorem log_le_escCount (N : ℕ) :
    Real.log ((N : ℝ) + 2) - Real.log 5 ≤ escCount N * Real.log 3 := by
  have h : ((N : ℝ) + 2) ≤ 5 * 3 ^ escCount N := by exact_mod_cast escape_ladder N
  have hpos : (0 : ℝ) < (N : ℝ) + 2 := by positivity
  have hlog := Real.log_le_log hpos h
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlog
  linarith

/-! ## The no-go: the ladder permits density zero

The escape set of the orbit satisfies an abstract *ladder property* — every `b ≥ 1` has an element
`n ≤ b` with `b < 3n + 3`.  That property is the entire content of the run cap for counting
purposes, and it does **not** force positive density. -/

/-- The abstract property established by `exists_max_escape`: a set that meets every `[b/3, b]`. -/
@[category API, AMS 11 37, ref "A1plus", group "weyl_a13_limitmeasures"]
def LadderProperty (E : ℕ → Prop) : Prop :=
  ∀ b, 1 ≤ b → ∃ n, E n ∧ 1 ≤ n ∧ n ≤ b ∧ b < 3 * n + 3

/-- The escape set of the `(3/2)ⁿ` orbit has the ladder property. -/
@[category research solved, AMS 11 37, ref "Dub09" "A1plus", group "weyl_a13_limitmeasures"]
theorem ladderProperty_escapes : LadderProperty Escapes := by
  intro b hb
  obtain ⟨g, h1, h2, h3, _, h5⟩ := exists_max_escape hb
  exact ⟨g, h3, h1, h2, h5⟩

/-- The comparison set: the powers of three. -/
@[category API, AMS 11 37, ref "A1plus", group "weyl_a13_limitmeasures"]
def IsPowThree (n : ℕ) : Prop := 1 ≤ n ∧ 3 ^ Nat.log 3 n = n

instance decidableIsPowThree (n : ℕ) : Decidable (IsPowThree n) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The powers of three have the ladder property too. -/
@[category API, AMS 11 37, ref "A1plus", group "weyl_a13_limitmeasures"]
theorem ladderProperty_isPowThree : LadderProperty IsPowThree := by
  intro b hb
  refine ⟨3 ^ Nat.log 3 b, ⟨Nat.one_le_pow _ _ (by norm_num), ?_⟩,
    Nat.one_le_pow _ _ (by norm_num), Nat.pow_log_le_self 3 (by omega), ?_⟩
  · rw [Nat.log_pow (by norm_num)]
  · have h := Nat.lt_pow_succ_log_self (b := 3) (by norm_num) b
    rw [pow_succ] at h
    omega

/-- There are at most `log₃ N + 1` powers of three below `N`. -/
@[category API, AMS 11 37, ref "A1plus", group "weyl_a13_limitmeasures"]
theorem card_isPowThree_le (N : ℕ) :
    ((Finset.range N).filter IsPowThree).card ≤ Nat.log 3 N + 1 := by
  classical
  have hsub : (Finset.range N).filter IsPowThree
      ⊆ (Finset.range (Nat.log 3 N + 1)).image (3 ^ ·) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hlt, hn1, hn3⟩ := hn
    refine Finset.mem_image.mpr ⟨Nat.log 3 n, ?_, hn3⟩
    rw [Finset.mem_range]
    have : Nat.log 3 n ≤ Nat.log 3 N := Nat.log_mono_right (by omega)
    omega
  calc ((Finset.range N).filter IsPowThree).card
      ≤ ((Finset.range (Nat.log 3 N + 1)).image (3 ^ ·)).card := Finset.card_le_card hsub
    _ ≤ (Finset.range (Nat.log 3 N + 1)).card := Finset.card_image_le
    _ = Nat.log 3 N + 1 := Finset.card_range _

/-- `(log₃ N + 1)/N → 0`. -/
@[category API, AMS 11 37, ref "A1plus", group "weyl_a13_limitmeasures"]
theorem tendsto_natLog_div_atTop :
    Tendsto (fun N : ℕ => ((Nat.log 3 N : ℝ) + 1) / N) atTop (𝓝 0) := by
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hbase : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hnat : Tendsto (fun N : ℕ => Real.log N / N) atTop (𝓝 0) :=
    hbase.comp tendsto_natCast_atTop_atTop
  have hone : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hsum : Tendsto (fun N : ℕ => (Real.log 3)⁻¹ * (Real.log N / N) + 1 / N) atTop (𝓝 0) := by
    simpa using ((hnat.const_mul (Real.log 3)⁻¹).add hone)
  refine squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_ hsum
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hle : (Nat.log 3 N : ℝ) * Real.log 3 ≤ Real.log N := by
    have h1 : (3 : ℕ) ^ Nat.log 3 N ≤ N := Nat.pow_log_le_self 3 (by omega)
    have h2 : ((3 : ℝ)) ^ Nat.log 3 N ≤ (N : ℝ) := by exact_mod_cast h1
    have := Real.log_le_log (by positivity) h2
    rwa [Real.log_pow] at this
  have hL : (Nat.log 3 N : ℝ) ≤ (Real.log 3)⁻¹ * Real.log N := by
    rw [inv_mul_eq_div, le_div_iff₀ hlog3]
    exact hle
  have hstep : ((Nat.log 3 N : ℝ) + 1) / N ≤ ((Real.log 3)⁻¹ * Real.log N + 1) / N := by gcongr
  refine hstep.trans_eq ?_
  rw [add_div, mul_div_assoc]

/-- **The no-go: the ladder does not force positive density.**  The powers of three satisfy the
same ladder property as the escape set of `(3/2)ⁿ` (`ladderProperty_escapes`), yet their density is
zero.  So no counting argument that uses only the Dubickas run cap can exclude
`δ₀ ∈ limitMeasures 1` (A13-N1): full-density confinement is consistent with the cap.

What N1 needs is therefore a statement about *densities of escapes*, not about run lengths —
see `TH.S6.notMem_limitMeasures_diracProba_of_lowerDensity_pos` for the exact interface. -/
@[category research solved, AMS 11 37, ref "A1plus", group "weyl_a13_limitmeasures"]
theorem ladder_permits_density_zero :
    LadderProperty IsPowThree ∧
      Tendsto (fun N : ℕ => ((((Finset.range N).filter IsPowThree).card : ℝ)) / N)
        atTop (𝓝 0) := by
  refine ⟨ladderProperty_isPowThree, ?_⟩
  refine squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_ tendsto_natLog_div_atTop
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h := card_isPowThree_le N
  have hle : ((((Finset.range N).filter IsPowThree).card : ℝ)) ≤ (Nat.log 3 N : ℝ) + 1 := by
    exact_mod_cast h
  gcongr

end TH
