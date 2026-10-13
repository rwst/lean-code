/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.GenSound
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Pseudo-orbits: when no certificate can exist ([Oda26] §7–8, for `DubC2.Gen`)

The generic checker `DubC2.Gen.Checked` only ever uses two facts about the orbit
`xₙ = ⌊ξ(p/q)ⁿ + a/b⌋`: the exact real identity `s·b = p·b·y − q·b·y' − (p−q)·a` between consecutive
fractional parts, and the congruence `q·x_{n+1} ≡ p·xₙ + sₙ (mod M)`.  A **pseudo-orbit** is any
triple of sequences (residues `rₙ`, reals `yₙ ∈ [0,1)`, integer letters `sₙ`) with exactly these two
properties and avoiding the divisor set.  Following [Oda26] Lemma 38 and Theorem 42:

* `DubC2.Gen.PseudoOrbit.isPath` — a pseudo-orbit is a path of the certificate graph (the same
  computation as `Gen.sound`, with the integer sequence forgotten);
* `DubC2.Gen.PseudoOrbit.eventuallyPeriodic` — **[Oda26] Lemma 38** for `Checked`: a checked
  certificate forces every pseudo-orbit's letters to be eventually periodic;
* `DubC2.Gen.not_checked_of_two_letters` — **[Oda26] Theorem 42**, generalized to shifts `ν = a/b`:
  two letters `s₀ ≠ c` satisfying explicit congruence and interval conditions rule out *every*
  certificate, for every number of cells `D`;
* `DubC2.Gen.not_checked_floor_internal` — **[Oda26] Corollary 43**: for the floor orbit
  (`a = 0`), a certificate needs a prime of `M` that neither divides `p` nor equals `2`.

The witness built for Theorem 42 is the sequence `yₙ = x* + μ·Zₙ` with `x*` the fixed point of the
letter `s₀`, `μ = (c − s₀)/p`, and `Zₙ = Σⱼ (q/p)ʲ·χ(n+j)` for the sparse, non-periodic set
`χ = {g(k+1)² : k ∈ ℕ}`; this replaces the paper's nested-interval construction by a series.

## References

* [Oda26] Y. Odagiri, *Finite graph certificates for composite terms in rational floor sequences*,
  Zenodo, doi:10.5281/zenodo.22997709 (2026).
-/

namespace DubC2.Gen

open Filter ForMathlib.SubwordComplexity

/-- An `M`-**pseudo-orbit** of the parameters `P`: residues `r`, fractional parts `y` and letters
`s` with the exact real carry identity, the residue recursion and the avoidance conditions. -/
structure PseudoOrbit (P : Params) (r : ℕ → ℕ) (y : ℕ → ℝ) (s : ℕ → ℤ) : Prop where
  r_lt : ∀ n, r n < P.M
  y_nonneg : ∀ n, 0 ≤ y n
  y_lt : ∀ n, y n < 1
  ident : ∀ n, (s n : ℝ) * P.b = P.p * P.b * y n - P.q * P.b * y (n + 1) - ((P.p : ℝ) - P.q) * P.a
  rstep : ∀ n, r (n + 1) = P.rnext (r n) (s n)
  r_av : ∀ n, ∀ l ∈ P.PM, r n % l ≠ 0
  s_av : ∀ n, ∀ l ∈ P.Pq, s n % (l : ℤ) ≠ 0

namespace PseudoOrbit

variable {P : Params} {r : ℕ → ℕ} {y : ℕ → ℝ} {s : ℕ → ℤ}

/-- The cell of `yₙ`. -/
noncomputable def pcell (y : ℕ → ℝ) (P : Params) (n : ℕ) : ℕ := (⌊(P.D : ℝ) * y n⌋).toNat

/-- The vertex of time `n`. -/
noncomputable def pvtx (P : Params) (r : ℕ → ℕ) (y : ℕ → ℝ) (n : ℕ) : ℕ :=
  r n * P.D + pcell y P n

/-- The letter index of time `n`. -/
def ptix (P : Params) (s : ℕ → ℤ) (n : ℕ) : ℕ := (s n - P.sLo).toNat

/-- The cell of a point of `[0, 1)`; only the time `n` matters. -/
theorem pcell_spec_of (hF : ParamFacts P) (n : ℕ) (hy0 : 0 ≤ y n) (hy1 : y n < 1) :
    ((pcell y P n : ℕ) : ℝ) ≤ P.D * y n ∧ P.D * y n < (pcell y P n : ℕ) + 1 ∧
      pcell y P n < P.D := by
  have hD : (0 : ℝ) < P.D := by exact_mod_cast hF.D0
  have hfl : 0 ≤ ⌊(P.D : ℝ) * y n⌋ := Int.floor_nonneg.2 (by positivity)
  have hc : ((pcell y P n : ℕ) : ℤ) = ⌊(P.D : ℝ) * y n⌋ := Int.toNat_of_nonneg hfl
  have hcR : ((pcell y P n : ℕ) : ℝ) = (⌊(P.D : ℝ) * y n⌋ : ℝ) := by exact_mod_cast hc
  refine ⟨?_, ?_, ?_⟩
  · rw [hcR]; exact Int.floor_le _
  · rw [hcR]; exact Int.lt_floor_add_one _
  · have : ⌊(P.D : ℝ) * y n⌋ < P.D := by
      rw [Int.floor_lt]; push_cast; nlinarith
    omega

theorem pcell_spec (hF : ParamFacts P) (h : PseudoOrbit P r y s) (n : ℕ) :
    ((pcell y P n : ℕ) : ℝ) ≤ P.D * y n ∧ P.D * y n < (pcell y P n : ℕ) + 1 ∧
      pcell y P n < P.D :=
  pcell_spec_of hF n (h.y_nonneg n) (h.y_lt n)

/-- One step of the certificate graph from the facts at the times `n` and `n + 1` alone (used for
finite pseudo-orbit segments by `DubC2/Branch.lean`). -/
theorem step_of (hF : ParamFacts P) (n : ℕ) (hrM : r n < P.M) (hy0 : 0 ≤ y n) (hy1 : y n < 1)
    (hz0 : 0 ≤ y (n + 1)) (hz1 : y (n + 1) < 1)
    (hsb : (s n : ℝ) * P.b = P.p * P.b * y n - P.q * P.b * y (n + 1) - ((P.p : ℝ) - P.q) * P.a)
    (hrs : r (n + 1) = P.rnext (r n) (s n)) (hav : ∀ l ∈ P.PM, r n % l ≠ 0)
    (hav' : ∀ l ∈ P.PM, r (n + 1) % l ≠ 0) (hsav : ∀ l ∈ P.Pq, s n % (l : ℤ) ≠ 0) :
    pvtx P r y n < P.nV ∧ ptix P s n < P.nA ∧ P.letter (ptix P s n) = s n ∧
      pvtx P r y (n + 1) ∈ P.succList (pvtx P r y n) (P.letter (ptix P s n)) := by
  have hD := hF.D0
  obtain ⟨hc0, hc1, hcD⟩ := pcell_spec_of hF n hy0 hy1
  obtain ⟨hd0, hd1, hdD⟩ := pcell_spec_of hF (n + 1) hz0 hz1
  have hpb : (0 : ℝ) ≤ P.p * P.b := by positivity
  have hp0 : (0 : ℝ) < P.p := by exact_mod_cast (by have := hF.pq; omega : 0 < P.p)
  have hb0' : (0 : ℝ) < P.b := by exact_mod_cast hF.b0
  have hqb : (0 : ℝ) < P.q * P.b := by
    have : (0 : ℝ) < P.q := by exact_mod_cast (by have := hF.q1; omega : 0 < P.q)
    positivity
  have hlo : -((P.q : ℤ) * P.b) - ((P.p : ℤ) - P.q) * P.a < s n * P.b := by
    have : -((P.q : ℝ) * P.b) - ((P.p : ℝ) - P.q) * P.a < (s n : ℝ) * P.b := by
      nlinarith [mul_nonneg hpb hy0, mul_lt_mul_of_pos_left hz1 hqb]
    exact_mod_cast this
  have hhi : s n * P.b < (P.p : ℤ) * P.b - ((P.p : ℤ) - P.q) * P.a := by
    have : (s n : ℝ) * P.b < (P.p : ℝ) * P.b - ((P.p : ℝ) - P.q) * P.a := by
      nlinarith [mul_lt_mul_of_pos_left hy1 (by positivity : (0 : ℝ) < P.p * P.b),
        mul_nonneg hqb.le hz0]
    exact_mod_cast this
  have hb0 : (0 : ℤ) < P.b := by exact_mod_cast hF.b0
  have hs1 : P.sLo ≤ s n := by
    have := hF.sLo
    by_contra hc
    push Not at hc
    have : (P.b : ℤ) * s n ≤ P.b * (P.sLo - 1) := mul_le_mul_of_nonneg_left (by omega) hb0.le
    linarith
  have hs2 : s n < P.sLo + P.nA := by
    have := hF.sHi
    by_contra hc
    push Not at hc
    have : (P.b : ℤ) * (P.sLo + P.nA) ≤ P.b * s n := mul_le_mul_of_nonneg_left hc hb0.le
    linarith
  have htix : P.letter (ptix P s n) = s n := by
    simp only [Params.letter, ptix]; omega
  refine ⟨?_, by simp only [ptix]; omega, htix, ?_⟩
  · simp only [pvtx, Params.nV]
    calc r n * P.D + pcell y P n < r n * P.D + P.D := by omega
      _ = (r n + 1) * P.D := by ring
      _ ≤ P.M * P.D := Nat.mul_le_mul_right _ hrM
  rw [htix]
  have hdiv : pvtx P r y n / P.D = r n := by
    simp only [pvtx]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hD, Nat.div_eq_of_lt hcD, zero_add]
  have hmod : pvtx P r y n % P.D = pcell y P n := by
    simp only [pvtx]
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hcD]
  simp only [Params.succList, hdiv, hmod, ← hrs]
  rw [if_pos]
  swap
  · simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq]
    exact ⟨⟨fun l hl => hav l hl, fun l hl => hsav l hl⟩, fun l hl => hav' l hl⟩
  rw [List.mem_map]
  have hE : (P.q : ℝ) * P.b * (P.D * y (n + 1)) =
      P.p * P.b * (P.D * y n) - (((P.p : ℝ) - P.q) * P.a * P.D + s n * P.b * P.D) := by
    linear_combination (P.D : ℝ) * hsb
  set c := pcell y P n
  set c' := pcell y P (n + 1)
  set w : ℤ := (P.q : ℤ) * P.b
  have hw : 0 < w := by
    have := hF.q1
    have : (0 : ℤ) < P.q := by omega
    positivity
  have hA : w * (c' : ℤ) < P.hi c (s n) := by
    simp only [Params.hi, Params.shiftK, w]
    have hq' : (0 : ℝ) ≤ P.q * P.b := hqb.le
    have hp' : (0 : ℝ) < P.p * P.b := by positivity
    have : ((P.q : ℝ) * P.b) * (c' : ℝ) < (P.p : ℝ) * P.b * ((c : ℝ) + 1) -
        (((P.p : ℝ) - P.q) * P.a * P.D + s n * P.b * P.D) := by
      nlinarith [mul_le_mul_of_nonneg_left hd0 hq', mul_lt_mul_of_pos_left hc1 hp']
    exact_mod_cast this
  have hB : P.lo c (s n) < w * ((c' : ℤ) + 1) := by
    simp only [Params.lo, Params.shiftK, w]
    have : (P.p : ℝ) * P.b * (c : ℝ) -
        (((P.p : ℝ) - P.q) * P.a * P.D + s n * P.b * P.D) < ((P.q : ℝ) * P.b) * ((c' : ℝ) + 1) := by
      nlinarith [mul_le_mul_of_nonneg_left hc0 hpb, mul_lt_mul_of_pos_left hd1 hqb]
    exact_mod_cast this
  refine ⟨c', List.mem_filter.2 ⟨?_, ?_⟩, ?_⟩
  · rw [List.mem_range'_1]
    have h1 : P.cLo c (s n) ≤ c' := by
      simp only [Params.cLo]
      rw [Int.toNat_le]
      have : P.lo c (s n) / w < (c' : ℤ) + 1 := by
        rw [Int.ediv_lt_iff_lt_mul hw]; linarith
      change P.lo c (s n) / w ≤ (c' : ℤ)
      omega
    have h2 : c' < P.cHi c (s n) := by
      simp only [Params.cHi]
      refine lt_min hdD ?_
      rw [Int.lt_toNat]
      have : (c' : ℤ) ≤ (P.hi c (s n) - 1) / w := by
        rw [Int.le_ediv_iff_mul_le hw]; linarith
      change (c' : ℤ) < (P.hi c (s n) - 1) / w + 1
      omega
    omega
  · simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hA, hB⟩
  · simp only [pvtx, c']

/-- **Soundness for pseudo-orbits**: each step is an edge of the certificate graph. -/
theorem step (hF : ParamFacts P) (h : PseudoOrbit P r y s) (n : ℕ) :
    pvtx P r y n < P.nV ∧ ptix P s n < P.nA ∧ P.letter (ptix P s n) = s n ∧
      pvtx P r y (n + 1) ∈ P.succList (pvtx P r y n) (P.letter (ptix P s n)) :=
  step_of hF n (h.r_lt n) (h.y_nonneg n) (h.y_lt n) (h.y_nonneg (n + 1)) (h.y_lt (n + 1))
    (h.ident n) (h.rstep n) (h.r_av n) (h.r_av (n + 1)) (h.s_av n)

/-- **[Oda26] Lemma 38 for `Checked`.**  A checked certificate makes the letters of every
pseudo-orbit eventually periodic. -/
@[category research solved, AMS 11 37, ref "Oda26", group "dubc2_obstruction"]
theorem eventuallyPeriodic {C : Cert} (hc : Checked P C) (h : PseudoOrbit P r y s) :
    IsEventuallyPeriodic s := by
  have hF : ParamFacts P := by
    have hh := hc.head
    simp only [checkHead, Bool.and_eq_true] at hh
    exact paramFacts hh.1.1.1.1.1
  have hp : IsPath P 0 (pvtx P r y) (ptix P s) :=
    ⟨fun n _ => (step hF h n).1, fun n _ => (step hF h n).2.1, fun n _ => (step hF h n).2.2.2⟩
  obtain ⟨M₀, per, hper, hp'⟩ := isEventuallyPeriodic_of_path hc hp
  refine ⟨M₀, per, hper, fun k hk => ?_⟩
  rw [← (step hF h k).2.2.1, ← (step hF h (k + per)).2.2.1, hp' k hk]

end PseudoOrbit

/-! ## The sparse non-periodic set and the series `Zₙ` -/

section Series

variable {ρ : ℝ} {χ : ℕ → ℝ}

/-- `Zₙ = Σⱼ ρʲ·χ(n+j)`. -/
noncomputable def Zs (ρ : ℝ) (χ : ℕ → ℝ) (n : ℕ) : ℝ := ∑' j : ℕ, ρ ^ j * χ (n + j)

variable (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hχ0 : ∀ n, 0 ≤ χ n) (hχ1 : ∀ n, χ n ≤ 1)
include hρ0 hρ1 hχ0 hχ1

theorem Zs_summable (n : ℕ) : Summable fun j : ℕ => ρ ^ j * χ (n + j) :=
  Summable.of_nonneg_of_le (fun j => mul_nonneg (pow_nonneg hρ0 _) (hχ0 _))
    (fun j => by
      have := hχ1 (n + j)
      calc ρ ^ j * χ (n + j) ≤ ρ ^ j * 1 := mul_le_mul_of_nonneg_left this (pow_nonneg hρ0 _)
        _ = ρ ^ j := mul_one _)
    (summable_geometric_of_lt_one hρ0 hρ1)

theorem Zs_rec (n : ℕ) : Zs ρ χ n = χ n + ρ * Zs ρ χ (n + 1) := by
  simp only [Zs]
  rw [(Zs_summable hρ0 hρ1 hχ0 hχ1 n).tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, one_mul, add_zero]
  congr 1
  refine tsum_congr fun j => ?_
  rw [pow_succ, show n + (j + 1) = n + 1 + j by ring]; ring

theorem Zs_nonneg (n : ℕ) : 0 ≤ Zs ρ χ n :=
  tsum_nonneg fun j => mul_nonneg (pow_nonneg hρ0 _) (hχ0 _)

theorem Zs_le (n : ℕ) : Zs ρ χ n ≤ 1 / (1 - ρ) := by
  rw [one_div, ← tsum_geometric_of_lt_one hρ0 hρ1]
  refine (Zs_summable hρ0 hρ1 hχ0 hχ1 n).tsum_le_tsum (fun j => ?_)
    (summable_geometric_of_lt_one hρ0 hρ1)
  calc ρ ^ j * χ (n + j) ≤ ρ ^ j * 1 := mul_le_mul_of_nonneg_left (hχ1 _) (pow_nonneg hρ0 _)
    _ = ρ ^ j := mul_one _

theorem Zs_shift {n : ℕ} : ∀ k, (∀ i < k, χ (n + i) = 0) → Zs ρ χ n = ρ ^ k * Zs ρ χ (n + k) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro h
    rw [ih (fun i hi => h i (by omega)), Zs_rec hρ0 hρ1 hχ0 hχ1 (n + k), h k (by omega),
      show n + k + 1 = n + (k + 1) by ring]
    ring

end Series

section SparseSet

/-- The sparse set `{g(k+1)² : k ∈ ℕ}`. -/
def InS (g n : ℕ) : Prop := ∃ k, n = g * (k + 1) ^ 2

theorem InS.exists_ge {g : ℕ} (hg : 1 ≤ g) (n : ℕ) : ∃ d, InS g (n + d) :=
  ⟨g * (n + 1) ^ 2 - n, n, by
    have : n ≤ g * (n + 1) ^ 2 := by nlinarith
    omega⟩

theorem InS.gap {g m i : ℕ} (hm : InS g m) (hi0 : 0 < i) (hig : i < g) : ¬ InS g (m + i) := by
  rintro ⟨j, hj⟩
  obtain ⟨k, rfl⟩ := hm
  have h1 : g * (k + 1) ^ 2 < g * (j + 1) ^ 2 := by omega
  have h2 : (k + 1) ^ 2 < (j + 1) ^ 2 := Nat.lt_of_mul_lt_mul_left h1
  have h3 : g * ((k + 1) ^ 2 + 1) ≤ g * (j + 1) ^ 2 := Nat.mul_le_mul_left _ h2
  nlinarith

theorem InS.not_periodic {g : ℕ} (hg : 1 ≤ g) {N p : ℕ} (hp : 0 < p)
    (h : ∀ k, N ≤ k → (InS g (k + p) ↔ InS g k)) : False := by
  obtain ⟨K, hK⟩ : ∃ K, K = N + p := ⟨_, rfl⟩
  have hm : InS g (g * (K + 1) ^ 2) := ⟨K, rfl⟩
  have hsq : K + 1 ≤ (K + 1) ^ 2 := by nlinarith
  have hgm : (K + 1) ^ 2 ≤ g * (K + 1) ^ 2 := Nat.le_mul_of_pos_left _ hg
  have hN : N ≤ g * (K + 1) ^ 2 := by omega
  obtain ⟨j, hj⟩ := (h _ hN).2 hm
  have h1 : (K + 1) ^ 2 < (j + 1) ^ 2 := by
    have : g * (K + 1) ^ 2 < g * (j + 1) ^ 2 := by omega
    exact Nat.lt_of_mul_lt_mul_left this
  have h2 : (j + 1) ^ 2 < (K + 2) ^ 2 := by
    have e : g * (K + 2) ^ 2 = g * (K + 1) ^ 2 + g * (2 * K + 3) := by ring
    have : 2 * K + 3 ≤ g * (2 * K + 3) := Nat.le_mul_of_pos_left _ hg
    have : g * (j + 1) ^ 2 < g * (K + 2) ^ 2 := by omega
    exact Nat.lt_of_mul_lt_mul_left this
  have h3 : K + 1 < j + 1 := by
    by_contra hc; push Not at hc; nlinarith [Nat.pow_le_pow_left hc 2]
  have h4 : j + 1 < K + 2 := by
    by_contra hc; push Not at hc; nlinarith [Nat.pow_le_pow_left hc 2]
  omega

open Classical in
/-- Indicator of the sparse set, as a real number. -/
noncomputable def chiS (g n : ℕ) : ℝ := if InS g n then 1 else 0

theorem chiS_nonneg (g n : ℕ) : 0 ≤ chiS g n := by unfold chiS; split_ifs <;> norm_num

theorem chiS_le (g n : ℕ) : chiS g n ≤ 1 := by unfold chiS; split_ifs <;> norm_num

variable {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {g : ℕ} (hg : 1 ≤ g)
include hρ0 hρ1 hg

theorem Zs_chiS_pos (n : ℕ) : 0 < Zs ρ (chiS g) n := by
  obtain ⟨d, hd⟩ := InS.exists_ge hg n
  refine (Zs_summable hρ0.le hρ1 (chiS_nonneg g) (chiS_le g) n).tsum_pos
    (fun j => mul_nonneg (pow_nonneg hρ0.le _) (chiS_nonneg g _)) d ?_
  simp only [chiS, if_pos hd, mul_one]
  exact pow_pos hρ0 _

theorem Zs_chiS_le (n : ℕ) : Zs ρ (chiS g) n ≤ 1 + ρ ^ g * (1 / (1 - ρ)) := by
  classical
  have hP : ∃ d, InS g (n + d) := InS.exists_ge hg n
  set d := Nat.find hP
  have hd : InS g (n + d) := Nat.find_spec hP
  have hbef : ∀ i < d, chiS g (n + i) = 0 := fun i hi => by
    simp only [chiS, if_neg (Nat.find_min hP hi)]
  have e1 := Zs_shift hρ0.le hρ1 (chiS_nonneg g) (chiS_le g) d hbef
  have e2 := Zs_rec hρ0.le hρ1 (chiS_nonneg g) (chiS_le g) (n + d)
  have hgap : ∀ i < g - 1, chiS g (n + d + 1 + i) = 0 := fun i hi => by
    simp only [chiS]
    rw [if_neg]
    rw [show n + d + 1 + i = n + d + (i + 1) by ring]
    exact InS.gap hd (by omega) (by omega)
  have e3 := Zs_shift hρ0.le hρ1 (chiS_nonneg g) (chiS_le g) (g - 1) hgap
  have hc1 : chiS g (n + d) = 1 := by simp only [chiS, if_pos hd]
  have hZ := Zs_le hρ0.le hρ1 (chiS_nonneg g) (chiS_le g) (n + d + 1 + (g - 1))
  have hZ0 := Zs_nonneg hρ0.le hρ1 (chiS_nonneg g) (chiS_le g) (n + d)
  have hpd : ρ ^ d ≤ 1 := pow_le_one₀ hρ0.le hρ1.le
  have hg' : ρ ^ g = ρ * ρ ^ (g - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hpg : 0 ≤ ρ ^ (g - 1) := pow_nonneg hρ0.le _
  calc Zs ρ (chiS g) n = ρ ^ d * Zs ρ (chiS g) (n + d) := e1
    _ ≤ 1 * Zs ρ (chiS g) (n + d) := mul_le_mul_of_nonneg_right hpd hZ0
    _ = 1 + ρ ^ g * Zs ρ (chiS g) (n + d + 1 + (g - 1)) := by
        rw [one_mul, e2, hc1, e3, hg']; ring
    _ ≤ 1 + ρ ^ g * (1 / (1 - ρ)) := by gcongr

end SparseSet

/-! ## Residues along a letter sequence -/

section Residues

variable {P : Params}

theorem rnext_lt (hF : ParamFacts P) (r : ℕ) (s : ℤ) : P.rnext r s < P.M := by
  have hM : (0 : ℤ) < P.M := by exact_mod_cast hF.M0
  have h1 := Int.emod_nonneg (((P.p : ℤ) * r + s) * P.qinv) hM.ne'
  have h2 := Int.emod_lt_of_pos (((P.p : ℤ) * r + s) * P.qinv) hM
  simp only [Params.rnext]
  omega

theorem q_mul_rnext (hF : ParamFacts P) (r : ℕ) (s : ℤ) :
    (P.M : ℤ) ∣ (P.q : ℤ) * P.rnext r s - ((P.p : ℤ) * r + s) := by
  have hM : (0 : ℤ) < P.M := by exact_mod_cast hF.M0
  have hcast : ((P.rnext r s : ℕ) : ℤ) = ((P.p : ℤ) * r + s) * P.qinv % P.M :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hM.ne')
  have hq : ((P.q : ℤ) * P.qinv) ≡ 1 [ZMOD P.M] := by
    have := congrArg (Nat.cast : ℕ → ℤ) hF.inv
    push_cast at this
    exact this
  have h1 : ((P.rnext r s : ℕ) : ℤ) ≡ ((P.p : ℤ) * r + s) * P.qinv [ZMOD P.M] := by
    rw [hcast]; exact Int.mod_modEq _ _
  have : (P.q : ℤ) * P.rnext r s ≡ (P.p : ℤ) * r + s [ZMOD P.M] :=
    calc (P.q : ℤ) * P.rnext r s ≡ (P.q : ℤ) * (((P.p : ℤ) * r + s) * P.qinv) [ZMOD P.M] :=
          h1.mul_left _
      _ = ((P.p : ℤ) * r + s) * ((P.q : ℤ) * P.qinv) := by ring
      _ ≡ ((P.p : ℤ) * r + s) * 1 [ZMOD P.M] := hq.mul_left _
      _ = (P.p : ℤ) * r + s := mul_one _
  exact (Int.ModEq.dvd this.symm)

/-- A divisor of `M` is coprime to `q`. -/
theorem isCoprime_q (hF : ParamFacts P) {l : ℤ} (hl : l ∣ P.M) : IsCoprime l (P.q : ℤ) := by
  have hq : ((P.q : ℤ) * P.qinv) ≡ 1 [ZMOD P.M] := by
    have := congrArg (Nat.cast : ℕ → ℤ) hF.inv
    push_cast at this
    exact this
  obtain ⟨k, hk⟩ := hl.trans (Int.ModEq.dvd hq)
  exact ⟨k, P.qinv, by linear_combination -hk⟩

/-- Residues driven by a letter sequence from `r₀`. -/
def rs (P : Params) (r₀ : ℕ) (s : ℕ → ℤ) : ℕ → ℕ
  | 0 => r₀
  | n + 1 => P.rnext (rs P r₀ s n) (s n)

end Residues

/-! ## [Oda26] Theorem 42, for `Checked` and any shift -/

/-- **[Oda26] Theorem 42 (two-letter obstruction), generalized to shifts `ν = a/b`.**  Let
`s₀ ≠ c` be two letters and `r₀ < M` a residue such that every `l ∈ PM` avoids `r₀` and either
divides `p` but neither letter, or divides both `(p−q)·r₀ + s₀` and `c − s₀`; every `l ∈ Pq`
divides neither letter; and, with `x* = s₀/(p−q) + ν` the fixed point of the letter `s₀`,
`0 ≤ x* ≤ 1` and `0 < x* + (c−s₀)/p < 1`.  Then **no** certificate is checked for `P`
(whatever its number of cells `D`): a pseudo-orbit with non-eventually-periodic letters exists. -/
@[category research solved, AMS 11 37, ref "Oda26", group "dubc2_obstruction"]
theorem not_checked_of_two_letters {P : Params} {C : Cert} {s₀ c : ℤ} (hne : c ≠ s₀) {r₀ : ℕ}
    (hr₀ : r₀ < P.M)
    (hPM : ∀ l ∈ P.PM, ¬ (l : ℤ) ∣ r₀ ∧
      (((l : ℤ) ∣ P.p ∧ ¬ (l : ℤ) ∣ s₀ ∧ ¬ (l : ℤ) ∣ c) ∨
        ((l : ℤ) ∣ ((P.p : ℤ) - P.q) * r₀ + s₀ ∧ (l : ℤ) ∣ c - s₀)))
    (hPq : ∀ l ∈ P.Pq, ¬ (l : ℤ) ∣ s₀ ∧ ¬ (l : ℤ) ∣ c)
    (hx0 : 0 ≤ ((s₀ : ℝ) * P.b + ((P.p : ℝ) - P.q) * P.a) / (((P.p : ℝ) - P.q) * P.b))
    (hx1 : ((s₀ : ℝ) * P.b + ((P.p : ℝ) - P.q) * P.a) / (((P.p : ℝ) - P.q) * P.b) ≤ 1)
    (he0 : 0 < ((s₀ : ℝ) * P.b + ((P.p : ℝ) - P.q) * P.a) / (((P.p : ℝ) - P.q) * P.b) +
      ((c : ℝ) - s₀) / P.p)
    (he1 : ((s₀ : ℝ) * P.b + ((P.p : ℝ) - P.q) * P.a) / (((P.p : ℝ) - P.q) * P.b) +
      ((c : ℝ) - s₀) / P.p < 1) :
    ¬ Checked P C := by
  classical
  intro hc
  have hF : ParamFacts P := by
    have hh := hc.head
    simp only [checkHead, Bool.and_eq_true] at hh
    exact paramFacts hh.1.1.1.1.1
  -- real parameters
  have hq0 : (0 : ℝ) < P.q := by exact_mod_cast (by have := hF.q1; omega : 0 < P.q)
  have hpq : (P.q : ℝ) < P.p := by exact_mod_cast hF.pq
  have hp0 : (0 : ℝ) < P.p := by linarith
  have hb0 : (0 : ℝ) < P.b := by exact_mod_cast hF.b0
  set ρ : ℝ := (P.q : ℝ) / P.p with hρ
  have hρ0 : 0 < ρ := div_pos hq0 hp0
  have hρ1 : ρ < 1 := (div_lt_one hp0).2 hpq
  set xs : ℝ := ((s₀ : ℝ) * P.b + ((P.p : ℝ) - P.q) * P.a) / (((P.p : ℝ) - P.q) * P.b) with hxs
  set μ : ℝ := ((c : ℝ) - s₀) / P.p with hμ
  set ε : ℝ := min (xs + μ) (1 - (xs + μ)) with hε
  have hε0 : 0 < ε := lt_min he0 (by linarith)
  -- choose the sparseness `g`
  have hδ : 0 < ε * (1 - ρ) / (|μ| + 1) := by
    have : 0 < 1 - ρ := by linarith
    positivity
  obtain ⟨n₀, hn₀⟩ := exists_pow_lt_of_lt_one hδ hρ1
  set g := n₀ + 1 with hg
  have hg1 : 1 ≤ g := by omega
  have hρg : ρ ^ g ≤ ρ ^ n₀ := pow_le_pow_of_le_one hρ0.le hρ1.le (by omega)
  set K : ℝ := 1 + ρ ^ g * (1 / (1 - ρ)) with hK
  have h1ρ : 0 < 1 - ρ := by linarith
  have hK1 : 1 ≤ K := by
    have : 0 ≤ ρ ^ g * (1 / (1 - ρ)) := by positivity
    linarith
  have hsmall : |μ| * (ρ ^ g * (1 / (1 - ρ))) < ε := by
    have h2 : ρ ^ g < ε * (1 - ρ) / (|μ| + 1) := lt_of_le_of_lt hρg hn₀
    have h3 : ρ ^ g * (1 / (1 - ρ)) < ε / (|μ| + 1) := by
      rw [mul_one_div, div_lt_iff₀ h1ρ]
      calc ρ ^ g < ε * (1 - ρ) / (|μ| + 1) := h2
        _ = ε / (|μ| + 1) * (1 - ρ) := by ring
    have h4 : |μ| * (ρ ^ g * (1 / (1 - ρ))) ≤ |μ| * (ε / (|μ| + 1)) :=
      mul_le_mul_of_nonneg_left h3.le (abs_nonneg _)
    have h5 : |μ| * (ε / (|μ| + 1)) < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [abs_nonneg μ]
    linarith
  set e : ℝ := xs + μ * K with he
  have hediff : |e - (xs + μ)| < ε := by
    have : e - (xs + μ) = μ * (ρ ^ g * (1 / (1 - ρ))) := by rw [he, hK]; ring
    rw [this, abs_mul]
    calc |μ| * |ρ ^ g * (1 / (1 - ρ))| = |μ| * (ρ ^ g * (1 / (1 - ρ))) := by
          rw [abs_of_nonneg (mul_nonneg (pow_nonneg hρ0.le _)
            (by rw [one_div]; exact inv_nonneg.2 h1ρ.le))]
      _ < ε := hsmall
  have hee0 : 0 < e := by
    have := (abs_lt.1 hediff).1
    have : ε ≤ xs + μ := min_le_left _ _
    linarith
  have hee1 : e < 1 := by
    have := (abs_lt.1 hediff).2
    have : ε ≤ 1 - (xs + μ) := min_le_right _ _
    linarith
  -- the pseudo-orbit
  set Z : ℕ → ℝ := Zs ρ (chiS g) with hZ
  set y : ℕ → ℝ := fun n => xs + μ * Z n with hy
  set s : ℕ → ℤ := fun n => if InS g n then c else s₀ with hs
  have hZpos : ∀ n, 0 < Z n := Zs_chiS_pos hρ0 hρ1 hg1
  have hZle : ∀ n, Z n ≤ K := Zs_chiS_le hρ0 hρ1 hg1
  have hyconv : ∀ n, y n = (1 - Z n / K) * xs + (Z n / K) * e := by
    intro n
    simp only [hy, he]
    field_simp
    ring
  have hyb : ∀ n, 0 ≤ y n ∧ y n < 1 := by
    intro n
    have hl0 : 0 < Z n / K := div_pos (hZpos n) (by linarith)
    have hl1 : Z n / K ≤ 1 := (div_le_one (by linarith)).2 (hZle n)
    rw [hyconv n]
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.2 hl1) hx0, mul_pos hl0 hee0]
    · nlinarith [mul_le_mul_of_nonneg_left hx1 (sub_nonneg.2 hl1), mul_lt_mul_of_pos_left hee1 hl0]
  have hrec : ∀ n, (P.p : ℝ) * Z n - P.q * Z (n + 1) = P.p * chiS g n := by
    intro n
    have := Zs_rec hρ0.le hρ1 (chiS_nonneg g) (chiS_le g) n
    simp only [hZ]
    rw [this, hρ]
    field_simp
    ring
  have hΔ : ((P.p : ℝ) - P.q) ≠ 0 := by linarith
  have hxsid : ((P.p : ℝ) - P.q) * P.b * xs = s₀ * P.b + ((P.p : ℝ) - P.q) * P.a := by
    rw [hxs]; field_simp
  have hμp : μ * P.p = (c : ℝ) - s₀ := by rw [hμ]; field_simp
  clear_value xs μ Z
  have hident : ∀ n, (s n : ℝ) * P.b =
      P.p * P.b * y n - P.q * P.b * y (n + 1) - ((P.p : ℝ) - P.q) * P.a := by
    intro n
    have hr := hrec n
    simp only [hy, hs]
    by_cases hn : InS g n
    · have hχ : chiS g n = 1 := by simp only [chiS, if_pos hn]
      rw [hχ] at hr
      simp only [if_pos hn]
      linear_combination -hxsid + (-(P.b : ℝ) * μ) * hr + (-(P.b : ℝ)) * hμp
    · have hχ : chiS g n = 0 := by simp only [chiS, if_neg hn]
      rw [hχ] at hr
      simp only [if_neg hn]
      linear_combination -hxsid + (-(P.b : ℝ) * μ) * hr
  have hsval : ∀ n, s n = c ∨ s n = s₀ := by
    intro n; simp only [hs]; split_ifs <;> simp
  -- residues
  set r := rs P r₀ s with hr
  have hrlt : ∀ n, r n < P.M := by
    intro n; cases n with
    | zero => exact hr₀
    | succ n => exact rnext_lt hF _ _
  have hrstep : ∀ n, r (n + 1) = P.rnext (r n) (s n) := fun n => rfl
  have hstep : ∀ n, (P.M : ℤ) ∣ (P.q : ℤ) * r (n + 1) - ((P.p : ℤ) * r n + s n) := fun n => by
    rw [hrstep]; exact q_mul_rnext hF _ _
  have hrav : ∀ n, ∀ l ∈ P.PM, ¬ (l : ℤ) ∣ (r n : ℤ) := by
    intro n l hl
    obtain ⟨hl0, hcase⟩ := hPM l hl
    have hlM : (l : ℤ) ∣ P.M := by exact_mod_cast Nat.dvd_of_mod_eq_zero (hF.PM l hl)
    rcases hcase with ⟨hlp, hls₀, hlc⟩ | ⟨hl1, hl2⟩
    · cases n with
      | zero => exact hl0
      | succ n =>
        intro hd
        have h1 : (l : ℤ) ∣ (P.q : ℤ) * r (n + 1) := dvd_mul_of_dvd_right hd _
        have h2 := hlM.trans (hstep n)
        have h3 : (l : ℤ) ∣ s n := by
          have : (s n : ℤ) = (P.q : ℤ) * r (n + 1) - ((P.q : ℤ) * r (n + 1) - ((P.p : ℤ) * r n + s n))
              - (P.p : ℤ) * r n := by ring
          rw [this]
          exact dvd_sub (dvd_sub h1 h2) (dvd_mul_of_dvd_left hlp _)
        rcases hsval n with h | h <;> rw [h] at h3
        · exact hlc h3
        · exact hls₀ h3
    · have hinv : ∀ n, (l : ℤ) ∣ (r n : ℤ) - r₀ := by
        intro n
        induction n with
        | zero => simp [hr, rs]
        | succ n ih =>
          have h2 := hlM.trans (hstep n)
          have h4 : (l : ℤ) ∣ s n - s₀ := by
            rcases hsval n with h | h <;> rw [h]
            · exact hl2
            · simp
          have h5 : (l : ℤ) ∣ (P.q : ℤ) * ((r (n + 1) : ℤ) - r₀) := by
            have : (P.q : ℤ) * ((r (n + 1) : ℤ) - r₀) =
                ((P.q : ℤ) * r (n + 1) - ((P.p : ℤ) * r n + s n)) + (P.p : ℤ) * ((r n : ℤ) - r₀)
                  + (s n - s₀) + (((P.p : ℤ) - P.q) * r₀ + s₀) := by ring
            rw [this]
            exact dvd_add (dvd_add (dvd_add h2 (dvd_mul_of_dvd_right ih _)) h4) hl1
          exact (isCoprime_q hF hlM).dvd_of_dvd_mul_left h5
      intro hd
      apply hl0
      have := dvd_sub hd (hinv n)
      simpa using this
  have hpo : PseudoOrbit P r y s := by
    refine ⟨hrlt, fun n => (hyb n).1, fun n => (hyb n).2, hident, hrstep, ?_, ?_⟩
    · intro n l hl h0
      exact hrav n l hl (by exact_mod_cast Nat.dvd_of_mod_eq_zero h0)
    · intro n l hl h0
      have h3 := Int.dvd_of_emod_eq_zero h0
      rcases hsval n with h | h <;> rw [h] at h3
      · exact (hPq l hl).2 h3
      · exact (hPq l hl).1 h3
  obtain ⟨N, per, hper, hpp⟩ := PseudoOrbit.eventuallyPeriodic hc hpo
  refine InS.not_periodic hg1 hper (N := N) fun k hk => ?_
  have := hpp k hk
  simp only [hs] at this
  constructor
  · intro h1
    by_contra h2
    rw [if_pos h1, if_neg h2] at this
    exact hne this
  · intro h1
    by_contra h2
    rw [if_pos h1, if_neg h2] at this
    exact hne this.symm

/-- **[Oda26] Corollary 43 (external primes are necessary), for `Checked`.**  For the floor orbit
`⌊ξ(p/q)ⁿ⌋` (`a = 0`), no certificate is checked whose residue primes `PM` all divide `p` or equal
`2` (with `Pq` the primes of `q` as usual): some prime of `M` must lie outside `2p`. -/
@[category research solved, AMS 11 37, ref "Oda26", group "dubc2_obstruction"]
theorem not_checked_floor_internal {P : Params} {C : Cert} (ha : P.a = 0)
    (hPM : ∀ l ∈ P.PM, 2 ≤ l ∧ ((l : ℤ) ∣ P.p ∨ l = 2)) (hPq : ∀ l ∈ P.Pq, 2 ≤ l) :
    ¬ Checked P C := by
  intro hc
  have hF : ParamFacts P := by
    have hh := hc.head
    simp only [checkHead, Bool.and_eq_true] at hh
    exact paramFacts hh.1.1.1.1.1
  have hq1 := hF.q1
  have hpq := hF.pq
  have hcop := hF.cop
  have hM := hF.M0
  -- `p` and `q` are not both even
  have hnot2 : ¬ (2 ∣ P.p ∧ 2 ∣ P.q) := by
    rintro ⟨h1, h2⟩
    have := Nat.dvd_gcd h1 h2
    rw [hcop] at this
    omega
  -- small integer divisors
  have hsmall : ∀ (l : ℕ) (c : ℤ), 2 ≤ l → (c = 1 ∨ c = -1 ∨ c = 2 ∨ c = -2) → (l : ℤ) ∣ c →
      l = 2 ∧ (c = 2 ∨ c = -2) := by
    intro l c hl hc hd
    have h1 : l ∣ c.natAbs := Int.natCast_dvd.1 hd
    have h2 : c.natAbs ≤ 2 := by omega
    have h3 : 0 < c.natAbs := by omega
    have h4 := Nat.le_of_dvd h3 h1
    have h5 : c.natAbs = 2 := by
      rcases hc with h | h | h | h <;> subst h <;> simp_all
    omega
  -- the choice of the second letter
  obtain ⟨c, hcv, hc2, hcne, hclo, hchi⟩ : ∃ c : ℤ, (c = 1 ∨ c = -1 ∨ c = 2 ∨ c = -2) ∧
      ((c = 2 ∨ c = -2) ↔ (P.p % 2 = 1 ∧ P.q % 2 = 1)) ∧ c ≠ (P.p : ℤ) - P.q ∧
      -(P.q : ℤ) < c ∧ c < (P.p : ℤ) - P.q := by
    by_cases hodd : P.p % 2 = 1 ∧ P.q % 2 = 1
    · by_cases h2 : (P.p : ℤ) - P.q = 2
      · exact ⟨-2, by simp, by simp [hodd], by omega, by omega, by omega⟩
      · exact ⟨2, by simp, by simp [hodd], by omega, by omega, by omega⟩
    · have hΔodd : ((P.p : ℤ) - P.q) % 2 = 1 := by omega
      by_cases h1 : (P.p : ℤ) - P.q = 1
      · exact ⟨-1, by simp, by simp [hodd], by omega, by omega, by omega⟩
      · exact ⟨1, by simp, by simp [hodd], by omega, by omega, by omega⟩
  have hb0 : (0 : ℝ) < P.b := by exact_mod_cast hF.b0
  have hp0 : (0 : ℝ) < P.p := by exact_mod_cast (show 0 < P.p by omega)
  have hΔ : ((P.p : ℝ) - P.q) ≠ 0 := by
    have : (P.q : ℝ) < P.p := by exact_mod_cast hpq
    linarith
  have hxs : (((((P.p : ℤ) - P.q : ℤ)) : ℝ) * P.b + ((P.p : ℝ) - P.q) * P.a) /
      (((P.p : ℝ) - P.q) * P.b) = 1 := by
    rw [ha]; simp only [Int.cast_zero, mul_zero, add_zero]; push_cast; field_simp
  refine not_checked_of_two_letters (s₀ := (P.p : ℤ) - P.q) (c := c) (r₀ := P.M - 1) hcne
    (by omega) ?_ ?_ (by rw [hxs]; norm_num) (by rw [hxs]) ?_ ?_ hc
  · intro l hl
    obtain ⟨hl2, hlcase⟩ := hPM l hl
    have hlM : (l : ℤ) ∣ P.M := by exact_mod_cast Nat.dvd_of_mod_eq_zero (hF.PM l hl)
    refine ⟨?_, ?_⟩
    · intro hd
      have hcast : (((P.M - 1 : ℕ)) : ℤ) = (P.M : ℤ) - 1 := by omega
      rw [hcast] at hd
      have : (l : ℤ) ∣ 1 := by
        have := dvd_sub hlM hd; simpa using this
      have := Int.le_of_dvd one_pos this
      omega
    by_cases hlp : (l : ℤ) ∣ P.p
    · left
      refine ⟨hlp, ?_, ?_⟩
      · intro hd
        have hlq : (l : ℤ) ∣ P.q := by
          have := dvd_sub hlp hd; simpa using this
        have h1 : l ∣ P.p := Int.natCast_dvd_natCast.1 hlp
        have h2 : l ∣ P.q := Int.natCast_dvd_natCast.1 hlq
        have := Nat.dvd_gcd h1 h2
        rw [hcop] at this
        have := Nat.le_of_dvd one_pos this
        omega
      · intro hd
        obtain ⟨rfl, hc22⟩ := hsmall l c hl2 hcv hd
        have := (hc2.1 hc22).1
        have : 2 ∣ P.p := Int.natCast_dvd_natCast.1 hlp
        omega
    · right
      have hl : l = 2 := hlcase.resolve_left hlp
      subst hl
      have hp2 : P.p % 2 = 1 := by
        by_contra h
        exact hlp (Int.natCast_dvd_natCast.2 (Nat.dvd_of_mod_eq_zero (by omega)))
      have hq2 : P.q % 2 = 1 := by
        by_contra h
        have hco := isCoprime_q hF hlM
        have h2q : (2 : ℤ) ∣ P.q := by omega
        have := hco.isUnit_of_dvd' (dvd_refl _) h2q
        rw [Int.isUnit_iff] at this
        omega
      have hc22 := hc2.2 ⟨hp2, hq2⟩
      constructor
      · have hcast : (((P.M - 1 : ℕ)) : ℤ) = (P.M : ℤ) - 1 := by omega
        rw [hcast]
        have : ((P.p : ℤ) - P.q) * ((P.M : ℤ) - 1) + ((P.p : ℤ) - P.q) =
            ((P.p : ℤ) - P.q) * P.M := by ring
        rw [this]
        exact dvd_mul_of_dvd_left (by omega) _
      · push_cast; omega
  · intro l hl
    obtain ⟨hlq, hlp⟩ := hF.Pq l hl
    have hl2 := hPq l hl
    have hlq' : (l : ℤ) ∣ P.q := Int.natCast_dvd_natCast.2 (Nat.dvd_of_mod_eq_zero hlq)
    refine ⟨?_, ?_⟩
    · intro hd
      have : (l : ℤ) ∣ P.p := by
        have := dvd_add hd hlq'; simpa using this
      have h1 : l ∣ P.p := Int.natCast_dvd_natCast.1 this
      have := Nat.dvd_gcd (dvd_refl l) h1
      rw [hlp] at this
      have := Nat.le_of_dvd one_pos this
      omega
    · intro hd
      obtain ⟨rfl, hc22⟩ := hsmall l c hl2 hcv hd
      have := (hc2.1 hc22).2
      omega
  · rw [hxs]
    have : -(P.q : ℝ) < c := by exact_mod_cast hclo
    rw [show (1 : ℝ) + ((c : ℝ) - (((P.p : ℤ) - P.q : ℤ) : ℝ)) / P.p =
      ((c : ℝ) + P.q) / P.p by push_cast; field_simp; ring]
    exact div_pos (by linarith) hp0
  · rw [hxs]
    have : (c : ℝ) < (((P.p : ℤ) - P.q : ℤ) : ℝ) := by exact_mod_cast hchi
    have : ((c : ℝ) - (((P.p : ℤ) - P.q : ℤ) : ℝ)) / P.p < 0 := div_neg_of_neg_of_pos (by linarith) hp0
    linarith

end DubC2.Gen
