/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.FloorCore
import Z32.DubickasWord
import Mathlib.Analysis.SpecificLimits.Basic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Calibration: [DN05] Theorem 1 at `3/2` — the Forman–Shapiro set `{2,5,7,11}`

Target T3(iii) of `plans/plan-dubC2.html`, the last of the three calibrations, and report
§F.3's deliverable: the first machine check of the main result of [FS67].

> **[DN05] Thm 1 at `a = 3/2`** ([FS67] + [DN05] Lemma 2).  For every real `ξ ≠ 0`, infinitely
> many of `⌊ξ(3/2)ⁿ⌋` are divisible by `2`, `5`, `7` or `11`.

The combinatorial core is `DubC2/FloorCore.lean` (`DubC2.FS.isEventuallyPeriodic`), which is
pure integer arithmetic.  This file supplies the archimedean side — and the archimedean side is
a single fact.  At `ν = 0` the carry is `sₙ = 3yₙ − 2y_{n+1} ∈ {−1,0,1,2}`, odd `xₙ` makes it
`±1`, and the letter `A` (`sₙ = −1`) sends `y` into `[½,1)`, from which `A` is impossible
(its window is `[0,⅓)`).  So `A²` never occurs — `DubC2.noAA_floor` — and nothing else about
`yₙ` is used.

## Main results

* `DubC2.floor_divisor_set_three_halves` — the theorem above.
* `DubC2.floor_composite_three_halves` — `⌊ξ(3/2)ⁿ⌋` is composite infinitely often, `ξ > 0`.

## References

* [FS67] W. Forman, H. N. Shapiro, *An arithmetic property of certain rational powers*, Comm.
  Pure Appl. Math. **20** (1967), 561–573.
* [DN05] A. Dubickas, A. Novikas, *Integer parts of powers of rational numbers*, Math. Z. **251**
  (2005), 635–648 — Theorem 1 and Lemma 2.
-/

namespace DubC2

open Filter ForMathlib.SubwordComplexity

variable {ξ : ℝ} {N n : ℕ}

/-! ## The model at `(p, q, ν) = (3, 2, 0)` -/

/-- `xₙ = ⌊ξ(3/2)ⁿ⌋`. -/
noncomputable def xF (ξ : ℝ) (n : ℕ) : ℤ := Z32.xInt 3 2 ξ 0 n

/-- `yₙ = {ξ(3/2)ⁿ}`. -/
noncomputable def yF (ξ : ℝ) (n : ℕ) : ℝ := Z32.yFract 3 2 ξ 0 n

/-- `sₙ = 2x_{n+1} − 3xₙ`. -/
noncomputable def sF (ξ : ℝ) (n : ℕ) : ℤ := Z32.carry 3 2 ξ 0 n

@[category API, AMS 11 37, ref "DN05", group "fs67_floor_32"]
theorem xF_eq_floor (ξ : ℝ) (n : ℕ) : xF ξ n = ⌊ξ * ((3 : ℝ) / 2) ^ n⌋ := by
  rw [xF, Z32.xInt, Z32.orb]
  norm_num

/-- `sₙ = 3yₙ − 2y_{n+1}`. -/
@[category API, AMS 11 37, ref "Dub09AA", group "fs67_floor_32"]
theorem sF_eq (ξ : ℝ) (n : ℕ) : (sF ξ n : ℝ) = 3 * yF ξ n - 2 * yF ξ (n + 1) := by
  have h := Z32.carry_eq (p := 3) (q := 2) (ξ := ξ) (ν := 0) (by norm_num) n
  simp only [sF, yF]
  push_cast at h ⊢
  linarith

@[category API, AMS 11 37, ref "Dub09AA", group "fs67_floor_32"]
theorem two_mul_xF_succ (ξ : ℝ) (n : ℕ) : 2 * xF ξ (n + 1) = 3 * xF ξ n + sF ξ n := by
  simp only [sF, xF, Z32.carry]
  push_cast
  ring

/-- `−1 ≤ sₙ ≤ 2`, from `0 ≤ y < 1` alone. -/
@[category API, AMS 11 37, ref "Dub09AA", group "fs67_floor_32"]
theorem sF_bounds (ξ : ℝ) (n : ℕ) : -1 ≤ sF ξ n ∧ sF ξ n ≤ 2 := by
  have h := sF_eq ξ n
  have h0 : 0 ≤ yF ξ n := Z32.yFract_nonneg n
  have h1 : yF ξ n < 1 := Z32.yFract_lt_one n
  have h2 : 0 ≤ yF ξ (n + 1) := Z32.yFract_nonneg (n + 1)
  have h3 : yF ξ (n + 1) < 1 := Z32.yFract_lt_one (n + 1)
  have hup : sF ξ n < 3 := by
    by_contra hc
    push Not at hc
    have : (3 : ℝ) ≤ (sF ξ n : ℝ) := by exact_mod_cast hc
    linarith
  have hlo : -2 < sF ξ n := by
    by_contra hc
    push Not at hc
    have : (sF ξ n : ℝ) ≤ -2 := by exact_mod_cast hc
    linarith
  omega

/-- **Two letters**: odd `xₙ` forces `sₙ = ±1`. -/
@[category API, AMS 11 37, ref "FS67", group "fs67_floor_32"]
theorem sF_mem (h2 : ¬ (2 : ℤ) ∣ xF ξ n) : sF ξ n = -1 ∨ sF ξ n = 1 := by
  have hrec := two_mul_xF_succ ξ n
  have hb := sF_bounds ξ n
  omega

/-- **`A²` is impossible** at `ν = 0`: after `sₙ = −1` the residual is `≥ ½`, while
`s_{n+1} = −1` needs it `< ⅓`. -/
@[category API, AMS 11 37, ref "FS67", group "fs67_floor_32"]
theorem noAA_floor (hA : sF ξ n = -1) : sF ξ (n + 1) ≠ -1 := by
  intro hA'
  have e0 := sF_eq ξ n
  have e1 := sF_eq ξ (n + 1)
  rw [hA] at e0
  rw [hA'] at e1
  have h0 : 0 ≤ yF ξ n := Z32.yFract_nonneg n
  have h2 : yF ξ (n + 1 + 1) < 1 := Z32.yFract_lt_one (n + 1 + 1)
  push_cast at e0 e1
  linarith

/-- An orbit avoiding `{2,5,7,11}` from `N` on is, shifted to `0`, a Forman–Shapiro word. -/
@[category API, AMS 11 37, ref "FS67", group "fs67_floor_32"]
theorem data_floor
    (hav : ∀ m, N ≤ m → ¬ (2 : ℤ) ∣ xF ξ m ∧ ¬ (5 : ℤ) ∣ xF ξ m ∧ ¬ (7 : ℤ) ∣ xF ξ m ∧
      ¬ (11 : ℤ) ∣ xF ξ m) :
    FS.Data (fun n => xF ξ (N + n)) (fun n => sF ξ (N + n)) where
  recur n := two_mul_xF_succ ξ (N + n)
  mem n := sF_mem (hav (N + n) (by omega)).1
  noAA n hn := ((sF_mem (hav (N + (n + 1)) (by omega)).1).resolve_left (noAA_floor hn))
  av5 n := (hav (N + n) (by omega)).2.1
  av7 n := (hav (N + n) (by omega)).2.2.1
  av11 n := (hav (N + n) (by omega)).2.2.2

/-- **[DN05] Theorem 1 at `3/2`, i.e. [FS67]'s theorem, formalised.**  For every real `ξ ≠ 0`,
infinitely many of `⌊ξ(3/2)ⁿ⌋` are divisible by `2`, `5`, `7` or `11`. -/
@[category research solved, AMS 11 37, ref "FS67" "DN05", group "fs67_floor_32"]
theorem floor_divisor_set_three_halves (hξ : ξ ≠ 0) :
    ∃ᶠ n in atTop, (2 : ℤ) ∣ ⌊ξ * ((3 : ℝ) / 2) ^ n⌋ ∨ (5 : ℤ) ∣ ⌊ξ * ((3 : ℝ) / 2) ^ n⌋ ∨
      (7 : ℤ) ∣ ⌊ξ * ((3 : ℝ) / 2) ^ n⌋ ∨ (11 : ℤ) ∣ ⌊ξ * ((3 : ℝ) / 2) ^ n⌋ := by
  rw [Filter.frequently_atTop]
  intro N
  by_contra hc
  push Not at hc
  have hav : ∀ m, N ≤ m → ¬ (2 : ℤ) ∣ xF ξ m ∧ ¬ (5 : ℤ) ∣ xF ξ m ∧ ¬ (7 : ℤ) ∣ xF ξ m ∧
      ¬ (11 : ℤ) ∣ xF ξ m := by
    intro m hm
    rw [xF_eq_floor]
    exact hc m hm
  obtain ⟨M, P, hP, hper⟩ := FS.isEventuallyPeriodic (data_floor hav)
  have hfull : IsEventuallyPeriodic (Z32.carry 3 2 ξ 0) := by
    refine ⟨N + M, P, hP, fun m hm => ?_⟩
    have h2 : sF ξ (N + (m - N + P)) = sF ξ (N + (m - N)) := hper (m - N) (by omega)
    rw [show N + (m - N + P) = m + P by omega, show N + (m - N) = m by omega] at h2
    exact h2
  exact Z32.not_isEventuallyPeriodic_carry (p := 3) (q := 2) (ξ := ξ) (ν := 0)
    (by norm_num) (by norm_num) (by decide) hξ hfull

/-- The composite corollary: for `ξ > 0`, `⌊ξ(3/2)ⁿ⌋` is composite infinitely often. -/
@[category research solved, AMS 11 37, ref "FS67" "DN05", group "fs67_floor_32"]
theorem floor_composite_three_halves (hξ : 0 < ξ) :
    ∃ᶠ n in atTop, ¬ Prime ⌊ξ * ((3 : ℝ) / 2) ^ n⌋ ∧ 1 < ⌊ξ * ((3 : ℝ) / 2) ^ n⌋ := by
  have hgrow : ∀ᶠ n in atTop, (11 : ℤ) < ⌊ξ * ((3 : ℝ) / 2) ^ n⌋ := by
    have h1 : Tendsto (fun n : ℕ => ξ * ((3 : ℝ) / 2) ^ n) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hξ (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
    refine (h1.eventually_ge_atTop 12).mono fun n hn => ?_
    have : (12 : ℤ) ≤ ⌊ξ * ((3 : ℝ) / 2) ^ n⌋ := Int.le_floor.mpr (by exact_mod_cast hn)
    omega
  refine ((floor_divisor_set_three_halves hξ.ne').and_eventually hgrow).mono ?_
  rintro n ⟨hdvd, hgt⟩
  set x : ℤ := ⌊ξ * ((3 : ℝ) / 2) ^ n⌋ with hx
  have hnat : (11 : ℕ) < x.natAbs := by omega
  refine ⟨fun hp => ?_, by omega⟩
  have hpn : Nat.Prime x.natAbs := Int.prime_iff_natAbs_prime.mp hp
  have key : ∀ d : ℕ, (d : ℤ) ∣ x → d ≤ 11 → 1 < d → False := by
    intro d hd hd11 hd1
    have h' : d ∣ x.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr hd; simpa using this
    rcases hpn.eq_one_or_self_of_dvd d h' with h1 | h1 <;> omega
  rcases hdvd with h | h | h | h
  · exact key 2 (by exact_mod_cast h) (by norm_num) (by norm_num)
  · exact key 5 (by exact_mod_cast h) (by norm_num) (by norm_num)
  · exact key 7 (by exact_mod_cast h) (by norm_num) (by norm_num)
  · exact key 11 (by exact_mod_cast h) (by norm_num) (by norm_num)

end DubC2
