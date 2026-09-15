/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.Bernoulli
import BB61.Cantor
import Bugeaud.Chapter1
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# M5 Theorem 8 and Corollary 10: uniform distribution is a tail event

Formal companion of `note-1061-M5.html` (milestone M5 of `plans/plan-1061.html`) §7.

> **Theorem 8 (the perturbation lemma).**  Let `U = {ε : (π(ε)αⁿ) is u.d. mod 1}`.  If `ε` and
> `ε'` agree from some index on, then `ε ∈ U ↔ ε' ∈ U`; that is, `U` is a tail event.
>
> **Corollary 10.**  If some `ξ ∈ C(α)` has `(ξαⁿ)` u.d. mod 1, then
> `{ξ ∈ C(α) : (ξαⁿ) u.d.}` is dense in `C(α)`.

§7 of the note retires X3 and X10 but keeps these two, because Corollary 10 is the one
structural statement about the *shape* of a hypothetical counterexample that no other part of
the programme provides: a counterexample to 10.61 at `α` could not be isolated.

## The two inputs

**The decay.**  `BB61/Bernoulli.lean`'s `abs_sub_trace` — `|(α-1)αᵐ - Tₘ| = |β-1||β|ᵐ` — is
exactly the statement that flipping one digit moves the orbit by something that returns to `ℤ`
geometrically fast.  Flipping the `k`-th digit changes `π(ε)` by `±(α-1)α^{-k-1}`
(`piVal_sub_of_eq_off`), so it changes `ξαⁿ` by `±(α-1)α^{n-k-1}`, which sits within
`|β-1||β|^{n-k-1}` of the integer `±T_{n-k-1}` (`abs_orbit_sub_int_le`).

**The invariance.**  Uniform distribution does not see a perturbation that tends to `0` modulo
one: `ForMathlib/Analysis/Equidistribution/ModOne.lean`'s `weylCriterion_of_tendsto_sub_int`,
transported across `Bugeaud.theorem_1_2_weyl`.  That lemma is where the analysis lives, and it
is three lines of harmonic analysis; everything in this file is arithmetic on top of it.

The general case follows from the one-digit case by induction on the agreement index, walking
from `ε` to `ε'` one flipped digit at a time (`mem_udWords_iff_of_agree_from`).

## What the hypotheses are

`QuadSetup` and nothing else.  **Neither `α > 2` nor `Irrational α` is used** — Theorem 8 is a
statement about the geometric decay `|β| < 1`, which is built into `QuadSetup`, and Corollary
10 only adds `1 < α` (also built in) to control `π`.  The note states both for a Pisot `α > 2`
because that is the setting of the problem, not because the proofs need it.
-/

namespace BB61

open Filter Topology

/-- The digit as an integer. -/
def dZ (ε : ℕ → Bool) (k : ℕ) : ℤ := if ε k then 1 else 0

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem dR_eq_dZ (ε : ℕ → Bool) (k : ℕ) : dR ε k = ((dZ ε k : ℤ) : ℝ) := by
  simp only [dR, dZ]
  split <;> norm_num

/-- The digit difference is `-1`, `0` or `1`, so its absolute value is at most one. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_dR_sub_le_one (ε ε' : ℕ → Bool) (k : ℕ) : |dR ε k - dR ε' k| ≤ 1 := by
  simp only [dR]
  split <;> split <;> norm_num

/-- Grafting: the word that follows `δ` up to the index `k` and `ε` from there on. -/
def graft (k : ℕ) (δ ε : ℕ → Bool) : ℕ → Bool := fun j => if j < k then δ j else ε j

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem graft_of_lt {k : ℕ} (δ ε : ℕ → Bool) {j : ℕ} (hj : j < k) : graft k δ ε j = δ j := by
  simp [graft, hj]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem graft_of_ge {k : ℕ} (δ ε : ℕ → Bool) {j : ℕ} (hj : k ≤ j) : graft k δ ε j = ε j := by
  simp [graft, Nat.not_lt.mpr hj]

namespace QuadSetup

variable (P : QuadSetup)

/-- **`U(α)` of M5 Thm 8**: the digit words whose orbit `(π(ε)αⁿ)` is uniformly distributed
modulo one.  Problem 10.61 asserts that this set is empty. -/
def udWords : Set (ℕ → Bool) :=
  {ε | IsEquidistributedModuloOne fun n : ℕ => piVal P.α ε * P.α ^ n}

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem mem_udWords_iff (ε : ℕ → Bool) :
    ε ∈ P.udWords ↔ IsEquidistributedModuloOne fun n : ℕ => piVal P.α ε * P.α ^ n := Iff.rfl

/-! ## Flipping one digit -/

/-- **One flipped digit.**  If `ε` and `ε'` agree off the index `k`, their Cantor values differ
by `±(α-1)α^{-k-1}`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem piVal_sub_of_eq_off {ε ε' : ℕ → Bool} {k : ℕ} (h : ∀ j, j ≠ k → ε j = ε' j) :
    piVal P.α ε - piVal P.α ε'
      = (dR ε k - dR ε' k) * ((P.α - 1) * (P.α⁻¹) ^ (k + 1)) := by
  have hα1 : (1 : ℝ) < P.α := P.one_lt
  have hinv0 : (0 : ℝ) ≤ P.α⁻¹ := le_of_lt (inv_pos.mpr P.alpha_pos)
  have hinv1 : P.α⁻¹ < 1 := inv_lt_one_of_one_lt hα1
  have hs : Summable fun j : ℕ => dR ε j * (P.α⁻¹) ^ (j + 1) := summable_dR_pow hinv0 hinv1 ε
  have hs' : Summable fun j : ℕ => dR ε' j * (P.α⁻¹) ^ (j + 1) := summable_dR_pow hinv0 hinv1 ε'
  have hsum : (∑' j : ℕ, dR ε j * (P.α⁻¹) ^ (j + 1))
      - (∑' j : ℕ, dR ε' j * (P.α⁻¹) ^ (j + 1))
      = (dR ε k - dR ε' k) * (P.α⁻¹) ^ (k + 1) := by
    rw [← hs.tsum_sub hs']
    have hcongr : ∀ j : ℕ, dR ε j * (P.α⁻¹) ^ (j + 1) - dR ε' j * (P.α⁻¹) ^ (j + 1)
        = (dR ε j - dR ε' j) * (P.α⁻¹) ^ (j + 1) := fun j => by ring
    rw [tsum_congr hcongr]
    refine tsum_eq_single k ?_
    intro j hj
    have : dR ε j = dR ε' j := by simp only [dR, h j hj]
    rw [this]
    ring
  rw [piVal, piVal, ← mul_sub, hsum]
  ring

/-- **The orbit under one flipped digit is exponentially close to an integer.**  For `n ≥ k+1`
the difference of the two orbits at time `n` is within `|β-1||β|^{n-k-1}` of the integer
`±T_{n-k-1}`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_orbit_sub_int_le {ε ε' : ℕ → Bool} {k : ℕ} (h : ∀ j, j ≠ k → ε j = ε' j) {n : ℕ}
    (hn : k + 1 ≤ n) :
    |(piVal P.α ε * P.α ^ n - piVal P.α ε' * P.α ^ n)
        - (((dZ ε k - dZ ε' k) * P.traceZ (n - (k + 1)) : ℤ) : ℝ)|
      ≤ |P.β - 1| * |P.β| ^ (n - (k + 1)) := by
  have hα0 : (0 : ℝ) < P.α := P.alpha_pos
  set m : ℕ := n - (k + 1) with hm
  have hn' : n = (k + 1) + m := by omega
  have hcz : dR ε k - dR ε' k = (((dZ ε k - dZ ε' k : ℤ)) : ℝ) := by
    rw [dR_eq_dZ, dR_eq_dZ]; push_cast; ring
  have hne : (P.α : ℝ) ^ (k + 1) ≠ 0 := by positivity
  have hpow : (P.α⁻¹) ^ (k + 1) * P.α ^ n = P.α ^ m := by
    have h1 : P.α ^ n = P.α ^ (k + 1) * P.α ^ m := by rw [hn', pow_add]
    rw [h1, inv_pow, inv_mul_cancel_left₀ hne]
  have hval : piVal P.α ε * P.α ^ n - piVal P.α ε' * P.α ^ n
      = (((dZ ε k - dZ ε' k : ℤ)) : ℝ) * ((P.α - 1) * P.α ^ m) := by
    have hd := P.piVal_sub_of_eq_off h
    calc piVal P.α ε * P.α ^ n - piVal P.α ε' * P.α ^ n
        = (piVal P.α ε - piVal P.α ε') * P.α ^ n := by ring
      _ = ((dR ε k - dR ε' k) * ((P.α - 1) * (P.α⁻¹) ^ (k + 1))) * P.α ^ n := by rw [hd]
      _ = (dR ε k - dR ε' k) * ((P.α - 1) * ((P.α⁻¹) ^ (k + 1) * P.α ^ n)) := by ring
      _ = (((dZ ε k - dZ ε' k : ℤ)) : ℝ) * ((P.α - 1) * P.α ^ m) := by rw [hpow, hcz]
  rw [hval]
  have hstep : (((dZ ε k - dZ ε' k : ℤ)) : ℝ) * ((P.α - 1) * P.α ^ m)
      - (((dZ ε k - dZ ε' k) * P.traceZ m : ℤ) : ℝ)
      = (((dZ ε k - dZ ε' k : ℤ)) : ℝ) * ((P.α - 1) * P.α ^ m - (P.traceZ m : ℝ)) := by
    push_cast; ring
  rw [hstep, abs_mul, P.abs_sub_trace m]
  have hle : |(((dZ ε k - dZ ε' k : ℤ)) : ℝ)| ≤ 1 := by
    rw [← hcz]; exact abs_dR_sub_le_one ε ε' k
  have hnn : (0 : ℝ) ≤ |P.β - 1| * |P.β| ^ m :=
    mul_nonneg (abs_nonneg _) (pow_nonneg (abs_nonneg _) m)
  nlinarith [hnn, hle, abs_nonneg (((dZ ε k - dZ ε' k : ℤ)) : ℝ)]

/-! ## M5 Theorem 8 -/

/-- One flipped digit does not change uniform distribution. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem mem_udWords_of_eq_off {ε ε' : ℕ → Bool} {k : ℕ} (h : ∀ j, j ≠ k → ε j = ε' j)
    (hε' : ε' ∈ P.udWords) : ε ∈ P.udWords := by
  have hw : WeylCriterion (fun n : ℕ => piVal P.α ε' * P.α ^ n) :=
    (Bugeaud.theorem_1_2_weyl _).mp hε'
  refine (Bugeaud.theorem_1_2_weyl _).mpr
    (weylCriterion_of_tendsto_sub_int (N := fun n : ℕ =>
      (dZ ε k - dZ ε' k) * P.traceZ (n - (k + 1))) ?_ hw)
  have hb : ∀ᶠ n : ℕ in atTop,
      ‖piVal P.α ε * P.α ^ n - piVal P.α ε' * P.α ^ n
          - (((dZ ε k - dZ ε' k) * P.traceZ (n - (k + 1)) : ℤ) : ℝ)‖
        ≤ |P.β - 1| * |P.β| ^ (n - (k + 1)) := by
    filter_upwards [eventually_ge_atTop (k + 1)] with n hn
    simpa [Real.norm_eq_abs] using P.abs_orbit_sub_int_le h hn
  have hg : Tendsto (fun n : ℕ => |P.β - 1| * |P.β| ^ (n - (k + 1))) atTop (𝓝 0) := by
    have hpow : Tendsto (fun m : ℕ => |P.β| ^ m) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg _) P.abs_beta_lt_one
    have hcomp := hpow.comp (tendsto_sub_atTop_nat (k + 1))
    simpa using hcomp.const_mul |P.β - 1|
  exact squeeze_zero_norm' hb hg

/-- Flipping one digit is an equivalence. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem mem_udWords_iff_of_eq_off {ε ε' : ℕ → Bool} {k : ℕ} (h : ∀ j, j ≠ k → ε j = ε' j) :
    ε ∈ P.udWords ↔ ε' ∈ P.udWords :=
  ⟨fun hε => P.mem_udWords_of_eq_off (fun j hj => (h j hj).symm) hε,
    fun hε' => P.mem_udWords_of_eq_off h hε'⟩

/-- **M5 Theorem 8: `U(α)` is a tail event.**  If `ε` and `ε'` agree from the index `k₀` on,
then `(π(ε)αⁿ)` is u.d. mod one iff `(π(ε')αⁿ)` is.

The proof walks from `ε` to `ε'` one digit at a time; each step is
`mem_udWords_iff_of_eq_off`, i.e. the Pisot decay `‖(α-1)αᵐ‖ ≤ |β-1||β|ᵐ`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem mem_udWords_iff_of_agree_from :
    ∀ (k₀ : ℕ) (ε ε' : ℕ → Bool), (∀ j, k₀ ≤ j → ε j = ε' j) →
      (ε ∈ P.udWords ↔ ε' ∈ P.udWords) := by
  intro k₀
  induction k₀ with
  | zero =>
      intro ε ε' h
      have : ε = ε' := funext fun j => h j (Nat.zero_le j)
      rw [this]
  | succ k ih =>
      intro ε ε' h
      set ε'' : ℕ → Bool := fun j => if j = k then ε j else ε' j with hε''
      have h1 : ∀ j, k ≤ j → ε j = ε'' j := by
        intro j hj
        rcases eq_or_lt_of_le hj with rfl | hlt
        · simp [hε'']
        · have hjk : j ≠ k := by omega
          have : ε'' j = ε' j := by simp [hε'', hjk]
          rw [this]
          exact h j (by omega)
      have h2 : ∀ j, j ≠ k → ε'' j = ε' j := by
        intro j hj
        simp [hε'', hj]
      exact (ih ε ε'' h1).trans (P.mem_udWords_iff_of_eq_off h2)

/-! ## M5 Corollary 10 -/

/-- Grafting moves the Cantor value by at most `α^{-k}`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_piVal_graft_sub_le (k : ℕ) (δ ε : ℕ → Bool) :
    |piVal P.α (graft k δ ε) - piVal P.α δ| ≤ (P.α⁻¹) ^ k := by
  have hα1 : (1 : ℝ) < P.α := P.one_lt
  have hsub := piVal_sub_eq_pow_mul (α := P.α) hα1 (ε := graft k δ ε) (ε' := δ) k
    (fun j hj => graft_of_lt δ ε hj)
  rw [hsub, abs_mul, abs_of_nonneg (pow_nonneg (le_of_lt (inv_pos.mpr P.alpha_pos)) k)]
  have h1 : piVal P.α (shift (graft k δ ε) k) ∈ Set.Icc (0 : ℝ) 1 :=
    cantorSet_subset_Icc hα1 ⟨_, rfl⟩
  have h2 : piVal P.α (shift δ k) ∈ Set.Icc (0 : ℝ) 1 := cantorSet_subset_Icc hα1 ⟨_, rfl⟩
  have hb : |piVal P.α (shift (graft k δ ε) k) - piVal P.α (shift δ k)| ≤ 1 := by
    rw [abs_le]
    constructor <;> [linarith [h1.1, h2.2]; linarith [h1.2, h2.1]]
  nlinarith [pow_nonneg (le_of_lt (inv_pos.mpr P.alpha_pos)) k, abs_nonneg
    (piVal P.α (shift (graft k δ ε) k) - piVal P.α (shift δ k))]

/-- **M5 Corollary 10: a counterexample could not be isolated.**  If some point of `C(α)` has
a uniformly distributed orbit, then the set of such points is dense in `C(α)`.

The set is a union of tail classes (Theorem 8), and the tail class of any word is dense in
`{0,1}^ℕ`: prescribe any prefix and follow the given word.  Transported by `π`, which is a
homeomorphism onto `C(α)` (M1 Lemma 1(iii)), that is the statement. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cantorSet_subset_closure_udPoints {ε₀ : ℕ → Bool} (hε₀ : ε₀ ∈ P.udWords) :
    cantorSet P.α ⊆ closure {x : ℝ | x ∈ cantorSet P.α ∧
      IsEquidistributedModuloOne fun n : ℕ => x * P.α ^ n} := by
  have hα1 : (1 : ℝ) < P.α := P.one_lt
  have hinv0 : (0 : ℝ) < P.α⁻¹ := inv_pos.mpr P.alpha_pos
  have hinv1 : P.α⁻¹ < 1 := inv_lt_one_of_one_lt hα1
  rintro _ ⟨δ, rfl⟩
  rw [Metric.mem_closure_iff]
  intro r hr
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hr hinv1
  refine ⟨piVal P.α (graft k δ ε₀), ⟨⟨_, rfl⟩, ?_⟩, ?_⟩
  · have hmem : graft k δ ε₀ ∈ P.udWords :=
      (P.mem_udWords_iff_of_agree_from k _ ε₀ (fun j hj => graft_of_ge δ ε₀ hj)).mpr hε₀
    exact hmem
  · rw [Real.dist_eq, abs_sub_comm]
    exact lt_of_le_of_lt (P.abs_piVal_graft_sub_le k δ ε₀) hk

end QuadSetup

end BB61
