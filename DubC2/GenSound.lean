/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.GenCert

/-!
# Soundness of the generic certificate: real orbits are paths

The archimedean half of `DubC2/GenCert.lean`.  For `xₙ = ⌊ξ(p/q)ⁿ + a/b⌋` avoiding the divisor
set `PM ++ Pq` at two consecutive times, the pair (residue `xₙ mod M`, cell `⌊D·yₙ⌋`) steps along
an edge of `Params.succMask` labelled by the true carry (`Gen.sound`) — the plan's §4.1
"soundness lemma, prove once".  With `Gen.isEventuallyPeriodic_of_path` and [DN05] Lemma 2 this
gives the capstone `Gen.divisor_set_of_checked`: a checked certificate is a theorem.
-/

namespace DubC2.Gen

open Filter ForMathlib.SubwordComplexity

variable (P : Params) (ξ : ℝ)

/-- The shift `ν = a/b`. -/
noncomputable def Params.nu : ℝ := (P.a : ℝ) / P.b

/-- `xₙ = ⌊ξ(p/q)ⁿ + ν⌋`. -/
noncomputable def xs (n : ℕ) : ℤ := Z32.xInt P.p P.q ξ P.nu n

/-- `yₙ = {ξ(p/q)ⁿ + ν}`. -/
noncomputable def ys (n : ℕ) : ℝ := Z32.yFract P.p P.q ξ P.nu n

/-- The carry `sₙ = q·x_{n+1} − p·xₙ`. -/
noncomputable def cs (n : ℕ) : ℤ := Z32.carry P.p P.q ξ P.nu n

/-- The cell of `yₙ`. -/
noncomputable def cell (n : ℕ) : ℕ := (⌊(P.D : ℝ) * ys P ξ n⌋).toNat

/-- The residue of `xₙ` mod `M`. -/
noncomputable def res (n : ℕ) : ℕ := (xs P ξ n % P.M).toNat

/-- The vertex of time `n`. -/
noncomputable def vtx (n : ℕ) : ℕ := res P ξ n * P.D + cell P ξ n

/-- The letter index of time `n`. -/
noncomputable def tix (n : ℕ) : ℕ := (cs P ξ n - P.sLo).toNat

/-- `xₙ` avoids the divisor set. -/
def Avoids (n : ℕ) : Prop := ∀ ℓ ∈ P.PM ++ P.Pq, ¬ (ℓ : ℤ) ∣ xs P ξ n

variable {P ξ}

/-- The side conditions, unpacked. -/
structure ParamFacts (P : Params) : Prop where
  q1 : 1 < P.q
  pq : P.q < P.p
  cop : Nat.gcd P.p P.q = 1
  b0 : 0 < P.b
  D0 : 0 < P.D
  M0 : 0 < P.M
  inv : P.q * P.qinv % P.M = 1 % P.M
  PM : ∀ l ∈ P.PM, P.M % l = 0
  Pq : ∀ l ∈ P.Pq, P.q % l = 0 ∧ Nat.gcd l P.p = 1
  sLo : (P.b : ℤ) * (P.sLo - 1) ≤ -((P.q : ℤ) * P.b) - ((P.p : ℤ) - P.q) * P.a
  sHi : (P.p : ℤ) * P.b - ((P.p : ℤ) - P.q) * P.a ≤ (P.b : ℤ) * (P.sLo + P.nA)

theorem paramFacts (h : checkParams P = true) : ParamFacts P := by
  simp only [checkParams, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true]
    at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

section Sound

variable (hF : ParamFacts P)
include hF

omit hF in
theorem q_mul_xs_succ (n : ℕ) : (P.q : ℤ) * xs P ξ (n + 1) = P.p * xs P ξ n + cs P ξ n := by
  simp only [cs, xs, Z32.carry]; ring

/-- The carry identity scaled by `b·D`: `q·b·(D y') = p·b·(D y) − K(s)`. -/
theorem scaled (n : ℕ) :
    (P.q : ℝ) * P.b * (P.D * ys P ξ (n + 1)) =
      P.p * P.b * (P.D * ys P ξ n) - (((P.p : ℝ) - P.q) * P.a * P.D + cs P ξ n * P.b * P.D) := by
  have h := Z32.carry_eq (p := P.p) (q := P.q) (ξ := ξ) (ν := P.nu) (by have := hF.q1; omega) n
  have hb : (P.b : ℝ) ≠ 0 := by have := hF.b0; positivity
  simp only [cs, ys, Params.nu] at h ⊢
  rw [h]
  field_simp
  try ring

/-- The carry scaled by `b`. -/
theorem scaled_b (n : ℕ) :
    (cs P ξ n : ℝ) * P.b = P.p * P.b * ys P ξ n - P.q * P.b * ys P ξ (n + 1) -
      ((P.p : ℝ) - P.q) * P.a := by
  have h := Z32.carry_eq (p := P.p) (q := P.q) (ξ := ξ) (ν := P.nu) (by have := hF.q1; omega) n
  have hb : (P.b : ℝ) ≠ 0 := by have := hF.b0; positivity
  simp only [cs, ys, Params.nu] at h ⊢
  rw [h]
  field_simp
  try ring

theorem cell_spec (n : ℕ) :
    ((cell P ξ n : ℕ) : ℝ) ≤ P.D * ys P ξ n ∧ P.D * ys P ξ n < (cell P ξ n : ℕ) + 1 ∧
      cell P ξ n < P.D := by
  have hy0 : 0 ≤ ys P ξ n := Z32.yFract_nonneg n
  have hy1 : ys P ξ n < 1 := Z32.yFract_lt_one n
  have hD : (0 : ℝ) < P.D := by exact_mod_cast hF.D0
  have hfl : 0 ≤ ⌊(P.D : ℝ) * ys P ξ n⌋ := Int.floor_nonneg.2 (by positivity)
  have hc : ((cell P ξ n : ℕ) : ℤ) = ⌊(P.D : ℝ) * ys P ξ n⌋ := Int.toNat_of_nonneg hfl
  have hcR : ((cell P ξ n : ℕ) : ℝ) = (⌊(P.D : ℝ) * ys P ξ n⌋ : ℝ) := by exact_mod_cast hc
  refine ⟨?_, ?_, ?_⟩
  · rw [hcR]; exact Int.floor_le _
  · rw [hcR]; exact Int.lt_floor_add_one _
  · have : ⌊(P.D : ℝ) * ys P ξ n⌋ < P.D := by
      rw [Int.floor_lt]; push_cast; nlinarith
    omega

theorem res_cast (n : ℕ) : ((res P ξ n : ℕ) : ℤ) = xs P ξ n % P.M :=
  Int.toNat_of_nonneg (Int.emod_nonneg _ (by have := hF.M0; omega))

theorem res_lt (n : ℕ) : res P ξ n < P.M := by
  have h1 := res_cast hF (ξ := ξ) n
  have h2 := Int.emod_lt_of_pos (xs P ξ n) (by have := hF.M0; omega : (0 : ℤ) < P.M)
  omega

theorem res_mod_ne {l : ℕ} (hl : l ∈ P.PM) {n : ℕ} (hn : ¬ (l : ℤ) ∣ xs P ξ n) :
    res P ξ n % l ≠ 0 := by
  intro h0
  apply hn
  have hlM : (l : ℤ) ∣ P.M := by
    exact_mod_cast Nat.dvd_of_mod_eq_zero (hF.PM l hl)
  have h1 : ((res P ξ n % l : ℕ) : ℤ) = xs P ξ n % l := by
    push_cast
    rw [res_cast hF (ξ := ξ), Int.emod_emod_of_dvd _ hlM]
  rw [h0, Nat.cast_zero] at h1
  exact Int.dvd_of_emod_eq_zero h1.symm

theorem rnext_eq (n : ℕ) : P.rnext (res P ξ n) (cs P ξ n) = res P ξ (n + 1) := by
  simp only [Params.rnext, res]
  congr 1
  have hq : ((P.q : ℤ) * P.qinv) ≡ 1 [ZMOD P.M] := by
    have := congrArg (Nat.cast : ℕ → ℤ) hF.inv
    push_cast at this
    exact this
  have hr : ((res P ξ n : ℕ) : ℤ) ≡ xs P ξ n [ZMOD P.M] := by
    rw [res_cast hF (ξ := ξ)]; exact Int.mod_modEq _ _
  have : ((P.p : ℤ) * ((xs P ξ n % P.M).toNat : ℕ) + cs P ξ n) * P.qinv ≡
      xs P ξ (n + 1) [ZMOD P.M] := by
    calc ((P.p : ℤ) * ((xs P ξ n % P.M).toNat : ℕ) + cs P ξ n) * P.qinv
        ≡ ((P.p : ℤ) * xs P ξ n + cs P ξ n) * P.qinv [ZMOD P.M] :=
          ((hr.mul_left _).add_right _).mul_right _
      _ = xs P ξ (n + 1) * ((P.q : ℤ) * P.qinv) := by rw [← q_mul_xs_succ]; ring
      _ ≡ xs P ξ (n + 1) * 1 [ZMOD P.M] := hq.mul_left _
      _ = xs P ξ (n + 1) := mul_one _
  exact this

theorem cs_mod_ne {l : ℕ} (hl : l ∈ P.Pq) {n : ℕ} (hn : ¬ (l : ℤ) ∣ xs P ξ n) :
    cs P ξ n % (l : ℤ) ≠ 0 := by
  intro h0
  apply hn
  obtain ⟨hlq, hlp⟩ := hF.Pq l hl
  have hdc : (l : ℤ) ∣ cs P ξ n := Int.dvd_of_emod_eq_zero h0
  have hdq : (l : ℤ) ∣ P.q := by exact_mod_cast Nat.dvd_of_mod_eq_zero hlq
  have hdp : (l : ℤ) ∣ xs P ξ n * P.p := by
    have : xs P ξ n * P.p = P.q * xs P ξ (n + 1) - cs P ξ n := by
      rw [q_mul_xs_succ]; ring
    rw [this]
    exact dvd_sub (dvd_mul_of_dvd_left hdq _) hdc
  have hcop : IsCoprime (l : ℤ) (P.p : ℤ) := Nat.isCoprime_iff_coprime.2 hlp
  exact hcop.dvd_of_dvd_mul_right hdp

/-- **Soundness.** -/
theorem sound {n : ℕ} (h0 : Avoids P ξ n) (h1 : Avoids P ξ (n + 1)) :
    vtx P ξ n < P.nV ∧ tix P ξ n < P.nA ∧ P.letter (tix P ξ n) = cs P ξ n ∧
      vtx P ξ (n + 1) ∈ P.succList (vtx P ξ n) (P.letter (tix P ξ n)) := by
  have hD := hF.D0
  obtain ⟨hc0, hc1, hcD⟩ := cell_spec hF (ξ := ξ) n
  obtain ⟨hd0, hd1, hdD⟩ := cell_spec hF (ξ := ξ) (n + 1)
  have hrM := res_lt hF (ξ := ξ) n
  -- the alphabet
  have hy0 := Z32.yFract_nonneg (p := P.p) (q := P.q) (ξ := ξ) (ν := P.nu) n
  have hy1 := Z32.yFract_lt_one (p := P.p) (q := P.q) (ξ := ξ) (ν := P.nu) n
  have hz0 := Z32.yFract_nonneg (p := P.p) (q := P.q) (ξ := ξ) (ν := P.nu) (n + 1)
  have hz1 := Z32.yFract_lt_one (p := P.p) (q := P.q) (ξ := ξ) (ν := P.nu) (n + 1)
  have hsb := scaled_b hF (ξ := ξ) n
  simp only [ys] at hsb
  have hpb : (0 : ℝ) ≤ P.p * P.b := by positivity
  have hqb : (0 : ℝ) < P.q * P.b := by
    have := hF.q1; have := hF.b0
    have : (0 : ℝ) < P.q := by exact_mod_cast (by omega : 0 < P.q)
    have : (0 : ℝ) < P.b := by exact_mod_cast hF.b0
    positivity
  have hlo : -((P.q : ℤ) * P.b) - ((P.p : ℤ) - P.q) * P.a < cs P ξ n * P.b := by
    have : -((P.q : ℝ) * P.b) - ((P.p : ℝ) - P.q) * P.a < (cs P ξ n : ℝ) * P.b := by
      nlinarith [mul_nonneg hpb hy0, mul_lt_mul_of_pos_left hz1 hqb]
    exact_mod_cast this
  have hhi : cs P ξ n * P.b < (P.p : ℤ) * P.b - ((P.p : ℤ) - P.q) * P.a := by
    have : (cs P ξ n : ℝ) * P.b < (P.p : ℝ) * P.b - ((P.p : ℝ) - P.q) * P.a := by
      nlinarith [mul_lt_mul_of_pos_left hy1 (by
        have : (0 : ℝ) < P.p := by exact_mod_cast (by have := hF.pq; omega : 0 < P.p)
        have : (0 : ℝ) < P.b := by exact_mod_cast hF.b0
        positivity : (0 : ℝ) < P.p * P.b), mul_nonneg hqb.le hz0]
    exact_mod_cast this
  have hb0 : (0 : ℤ) < P.b := by exact_mod_cast hF.b0
  have hs1 : P.sLo ≤ cs P ξ n := by
    have := hF.sLo
    by_contra hc
    push Not at hc
    have : (P.b : ℤ) * cs P ξ n ≤ P.b * (P.sLo - 1) := mul_le_mul_of_nonneg_left (by omega) hb0.le
    linarith
  have hs2 : cs P ξ n < P.sLo + P.nA := by
    have := hF.sHi
    by_contra hc
    push Not at hc
    have : (P.b : ℤ) * (P.sLo + P.nA) ≤ P.b * cs P ξ n := mul_le_mul_of_nonneg_left hc hb0.le
    linarith
  have htix : P.letter (tix P ξ n) = cs P ξ n := by
    simp only [Params.letter, tix]; omega
  refine ⟨?_, by simp only [tix]; omega, htix, ?_⟩
  · -- the vertex is in range
    simp only [vtx, Params.nV]
    calc res P ξ n * P.D + cell P ξ n < res P ξ n * P.D + P.D := by omega
      _ = (res P ξ n + 1) * P.D := by ring
      _ ≤ P.M * P.D := Nat.mul_le_mul_right _ hrM
  -- the edge
  rw [htix]
  have hdiv : vtx P ξ n / P.D = res P ξ n := by
    simp only [vtx]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hD, Nat.div_eq_of_lt hcD, zero_add]
  have hmod : vtx P ξ n % P.D = cell P ξ n := by
    simp only [vtx]
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hcD]
  simp only [Params.succList, hdiv, hmod, rnext_eq hF (ξ := ξ)]
  rw [if_pos]
  swap
  · simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq]
    refine ⟨⟨fun l hl => res_mod_ne hF hl (h0 l (List.mem_append_left _ hl)),
      fun l hl => cs_mod_ne hF hl (h0 l (List.mem_append_right _ hl))⟩,
      fun l hl => res_mod_ne hF hl (h1 l (List.mem_append_left _ hl))⟩
  rw [List.mem_map]
  -- the overlap, in the reals
  have hE := scaled hF (ξ := ξ) n
  set c := cell P ξ n
  set c' := cell P ξ (n + 1)
  set w : ℤ := (P.q : ℤ) * P.b
  have hw : 0 < w := by
    have := hF.q1
    have : (0 : ℤ) < P.q := by omega
    positivity
  have hA : w * (c' : ℤ) < P.hi c (cs P ξ n) := by
    simp only [Params.hi, Params.shiftK, w]
    have hq' : (0 : ℝ) ≤ P.q * P.b := hqb.le
    have hp' : (0 : ℝ) < P.p * P.b := by
      have : (0 : ℝ) < P.p := by exact_mod_cast (by have := hF.pq; omega : 0 < P.p)
      have : (0 : ℝ) < P.b := by exact_mod_cast hF.b0
      positivity
    have : ((P.q : ℝ) * P.b) * (c' : ℝ) < (P.p : ℝ) * P.b * ((c : ℝ) + 1) -
        (((P.p : ℝ) - P.q) * P.a * P.D + cs P ξ n * P.b * P.D) := by
      nlinarith [mul_le_mul_of_nonneg_left hd0 hq', mul_lt_mul_of_pos_left hc1 hp']
    exact_mod_cast this
  have hB : P.lo c (cs P ξ n) < w * ((c' : ℤ) + 1) := by
    simp only [Params.lo, Params.shiftK, w]
    have hp' : (0 : ℝ) ≤ P.p * P.b := hpb
    have : (P.p : ℝ) * P.b * (c : ℝ) -
        (((P.p : ℝ) - P.q) * P.a * P.D + cs P ξ n * P.b * P.D) < ((P.q : ℝ) * P.b) * ((c' : ℝ) + 1) := by
      nlinarith [mul_le_mul_of_nonneg_left hc0 hp', mul_lt_mul_of_pos_left hd1 hqb]
    exact_mod_cast this
  refine ⟨c', List.mem_filter.2 ⟨?_, ?_⟩, ?_⟩
  · rw [List.mem_range'_1]
    have h1 : P.cLo c (cs P ξ n) ≤ c' := by
      simp only [Params.cLo]
      rw [Int.toNat_le]
      have : P.lo c (cs P ξ n) / w < (c' : ℤ) + 1 := by
        rw [Int.ediv_lt_iff_lt_mul hw]; linarith
      change P.lo c (cs P ξ n) / w ≤ (c' : ℤ)
      omega
    have h2 : c' < P.cHi c (cs P ξ n) := by
      simp only [Params.cHi]
      refine lt_min hdD ?_
      rw [Int.lt_toNat]
      have : (c' : ℤ) ≤ (P.hi c (cs P ξ n) - 1) / w := by
        rw [Int.le_ediv_iff_mul_le hw]; linarith
      change (c' : ℤ) < (P.hi c (cs P ξ n) - 1) / w + 1
      omega
    omega
  · simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hA, hB⟩
  · simp only [vtx, c']

end Sound

/-- **A checked certificate is a theorem**: for every `ξ ≠ 0`, infinitely many of
`⌊ξ(p/q)ⁿ + a/b⌋` are divisible by a member of `PM ++ Pq`. -/
@[category API, AMS 11 37, ref "DN05", group "dubc2_atlas"]
theorem divisor_set_of_checked {C : Cert} (hc : Checked P C) (hξ : ξ ≠ 0) :
    ∃ᶠ n in atTop, ∃ ℓ ∈ P.PM ++ P.Pq, (ℓ : ℤ) ∣ Z32.xInt P.p P.q ξ ((P.a : ℝ) / P.b) n := by
  have hF : ParamFacts P := by
    have hh := hc.head
    simp only [checkHead, Bool.and_eq_true] at hh
    exact paramFacts hh.1.1.1.1.1
  rw [Filter.frequently_atTop]
  intro N
  by_contra hcon
  push Not at hcon
  have hav : ∀ n, N ≤ n → Avoids P ξ n := fun n hn ℓ hℓ => hcon n hn ℓ hℓ
  have hp : IsPath P N (vtx P ξ) (tix P ξ) :=
    ⟨fun n hn => (sound hF (hav n hn) (hav (n + 1) (by omega))).1,
     fun n hn => (sound hF (hav n hn) (hav (n + 1) (by omega))).2.1,
     fun n hn => (sound hF (hav n hn) (hav (n + 1) (by omega))).2.2.2⟩
  obtain ⟨M₀, per, hper, hp'⟩ := isEventuallyPeriodic_of_path hc hp
  apply Z32.not_isEventuallyPeriodic_carry (p := P.p) (q := P.q) (ξ := ξ) (ν := P.nu) hF.q1 hF.pq
    hF.cop hξ
  refine ⟨max M₀ N, per, hper, fun k hk => ?_⟩
  have e1 := (sound hF (hav k (by omega)) (hav (k + 1) (by omega))).2.2.1
  have e2 := (sound hF (hav (k + per) (by omega)) (hav (k + per + 1) (by omega))).2.2.1
  change cs P ξ (k + per) = cs P ξ k
  rw [← e1, ← e2, hp' k (by omega)]

end DubC2.Gen
