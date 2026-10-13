/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.GenSound

/-!
# Certificates with a real shift parameter (plan-dubC2-transform, T3)

`DubC2.Gen.divisor_set_of_checked` proves a divisor-set theorem for one rational shift `ν = a/b`.
Every comparison of the certificate graph (`Params.succList`) is affine in `ν`: an integer against
`(p−q)·D·ν`.  So the graph is constant on the open `ν`-cells `(j, j+1)/((p−q)D)`.

**The hull check.**  For a shift interval `[a₀/b, a₁/b]`, a cell `c'` is a *hull successor* of the
cell `c` under the letter `s` if the image `p·b·[c, c+1) − K(s)` meets `q·b·[c', c'+1)` for some
`ν` in the interval, read on the extreme ends (`K` at `a₁` for the left end, at `a₀` for the right
end).  `hullOK P a₀ a₁` checks that every hull successor is already a successor of the graph of `P`
(at its own shift `P.a/P.b`), and that the alphabet of `P` covers the interval.  It is a finite
decidable check, scanning only the hull-candidate target cells (`hcLo`, `hcHi`).

**Soundness for every real shift.**  For real `ν ∈ [a₀/b, a₁/b]` the orbit of
`⌊ξ(p/q)ⁿ + ν⌋` steps along hull edges (`Nu.sound`), hence along edges of `P` under `hullOK`.  So
a checked certificate of `P` proves the divisor-set theorem for **every real shift in the
interval** (`divisor_set_of_checked_hull`).  The proof is `Gen.sound` with `ν` real: one kernel
check covers a continuum of shifts.

On a closed `ν`-cell `[j, j+1]/((p−q)D)` the hull graph equals the open-cell graph, so `hullOK`
holds with `P` at the cell midpoint; `xnu.py` computes the decomposition of the shift circle.

## Main results

* `DubC2.Gen.hullOK` — the hull check;
* `DubC2.Gen.Nu.sound` — real orbits are hull paths;
* `DubC2.Gen.divisor_set_of_checked_hull` — a checked certificate with `hullOK` is a theorem for
  every real shift in the interval.

## References

* [DN05] A. Dubickas, A. Novikas, *Integer parts of powers of rational numbers*, Math. Z. 251
  (2005) 635–648.
* [Oda26] Y. Odagiri, *Finite graph certificates for composite terms in rational floor sequences*,
  Zenodo, doi:10.5281/zenodo.22997709 (2026).
-/

namespace DubC2.Gen

open Filter ForMathlib.SubwordComplexity

namespace Params

variable (P : Params)

/-- `p·b·c − K(s)` with the shift numerator `a` in place of `P.a`. -/
def loAt (a : ℤ) (c : ℕ) (s : ℤ) : ℤ :=
  (P.p : ℤ) * P.b * c - (((P.p : ℤ) - P.q) * a * P.D + s * P.b * P.D)

/-- `p·b·(c+1) − K(s)` with the shift numerator `a` in place of `P.a`. -/
def hiAt (a : ℤ) (c : ℕ) (s : ℤ) : ℤ :=
  (P.p : ℤ) * P.b * (c + 1) - (((P.p : ℤ) - P.q) * a * P.D + s * P.b * P.D)

/-- The cell `c'` is a hull successor of the cell `c` under `s`, over `[a₀/b, a₁/b]`. -/
def hullEdge (a₀ a₁ : ℤ) (c : ℕ) (s : ℤ) (c₂ : ℕ) : Bool :=
  decide ((P.q : ℤ) * P.b * c₂ < P.hiAt a₀ c s) && decide (P.loAt a₁ c s < (P.q : ℤ) * P.b * (c₂ + 1))

end Params

namespace Params

variable (P : Params)

/-- First hull-candidate target cell. -/
def hcLo (a₁ : ℤ) (c : ℕ) (s : ℤ) : ℕ := (P.loAt a₁ c s / ((P.q : ℤ) * P.b)).toNat

/-- One past the last hull-candidate target cell. -/
def hcHi (a₀ : ℤ) (c : ℕ) (s : ℤ) : ℕ := min P.D ((P.hiAt a₀ c s - 1) / ((P.q : ℤ) * P.b) + 1).toNat

end Params

/-- **The hull check** for the shift interval `[a₀/b, a₁/b]`: the alphabet of `P` covers it, and
every hull successor (scanned over its candidate range) is a successor at the shift of `P`. -/
def hullOK (P : Params) (a₀ a₁ : ℤ) : Bool :=
  decide ((P.b : ℤ) * (P.sLo - 1) ≤ -((P.q : ℤ) * P.b) - ((P.p : ℤ) - P.q) * a₁) &&
  decide ((P.p : ℤ) * P.b - ((P.p : ℤ) - P.q) * a₀ ≤ (P.b : ℤ) * (P.sLo + P.nA)) &&
  (List.range P.D).all fun c => (List.range P.nA).all fun t =>
    (List.range' (P.hcLo a₁ c (P.letter t)) (P.hcHi a₀ c (P.letter t) - P.hcLo a₁ c (P.letter t))).all
      fun c₂ => !(P.hullEdge a₀ a₁ c (P.letter t) c₂) || P.hullEdge P.a P.a c (P.letter t) c₂

theorem hullOK_spec {P : Params} {a₀ a₁ : ℤ} (hq : 0 < P.q) (hb : 0 < P.b) (h : hullOK P a₀ a₁ = true) :
    (P.b : ℤ) * (P.sLo - 1) ≤ -((P.q : ℤ) * P.b) - ((P.p : ℤ) - P.q) * a₁ ∧
    (P.p : ℤ) * P.b - ((P.p : ℤ) - P.q) * a₀ ≤ (P.b : ℤ) * (P.sLo + P.nA) ∧
    ∀ c < P.D, ∀ t < P.nA, ∀ c₂ < P.D, P.hullEdge a₀ a₁ c (P.letter t) c₂ = true →
      (P.q : ℤ) * P.b * c₂ < P.hi c (P.letter t) ∧ P.lo c (P.letter t) < (P.q : ℤ) * P.b * (c₂ + 1) := by
  simp only [hullOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun c hc t ht c₂ hc₂ he => ?_⟩
  have hw : (0 : ℤ) < (P.q : ℤ) * P.b := by positivity
  have he' := he
  simp only [Params.hullEdge, Bool.and_eq_true] at he'
  have hA := of_decide_eq_true he'.1
  have hB := of_decide_eq_true he'.2
  have hmem : c₂ ∈ List.range' (P.hcLo a₁ c (P.letter t))
      (P.hcHi a₀ c (P.letter t) - P.hcLo a₁ c (P.letter t)) := by
    rw [List.mem_range'_1]
    have h1 : P.hcLo a₁ c (P.letter t) ≤ c₂ := by
      simp only [Params.hcLo]
      rw [Int.toNat_le]
      have : P.loAt a₁ c (P.letter t) / ((P.q : ℤ) * P.b) < (c₂ : ℤ) + 1 := by
        rw [Int.ediv_lt_iff_lt_mul hw]; linarith
      omega
    have h2 : c₂ < P.hcHi a₀ c (P.letter t) := by
      simp only [Params.hcHi]
      refine lt_min hc₂ ?_
      rw [Int.lt_toNat]
      have : (c₂ : ℤ) ≤ (P.hiAt a₀ c (P.letter t) - 1) / ((P.q : ℤ) * P.b) := by
        rw [Int.le_ediv_iff_mul_le hw]; linarith
      omega
    omega
  have := (h3 c hc t ht c₂ hmem).resolve_left (by rw [he]; decide)
  simp only [Params.hullEdge, Params.hiAt, Params.loAt, Bool.and_eq_true] at this
  exact ⟨of_decide_eq_true this.1, of_decide_eq_true this.2⟩

namespace Nu

variable (P : Params) (ξ ν : ℝ)

/-- `xₙ = ⌊ξ(p/q)ⁿ + ν⌋`, for a real shift `ν`. -/
noncomputable def xs (n : ℕ) : ℤ := Z32.xInt P.p P.q ξ ν n

/-- `yₙ = {ξ(p/q)ⁿ + ν}`. -/
noncomputable def ys (n : ℕ) : ℝ := Z32.yFract P.p P.q ξ ν n

/-- The carry. -/
noncomputable def cs (n : ℕ) : ℤ := Z32.carry P.p P.q ξ ν n

/-- The cell of `yₙ`. -/
noncomputable def cell (n : ℕ) : ℕ := (⌊(P.D : ℝ) * ys P ξ ν n⌋).toNat

/-- The residue of `xₙ` mod `M`. -/
noncomputable def res (n : ℕ) : ℕ := (xs P ξ ν n % P.M).toNat

/-- The vertex of time `n`. -/
noncomputable def vtx (n : ℕ) : ℕ := res P ξ ν n * P.D + cell P ξ ν n

/-- The letter index of time `n`. -/
noncomputable def tix (n : ℕ) : ℕ := (cs P ξ ν n - P.sLo).toNat

/-- `xₙ` avoids the divisor set. -/
def Avoids (n : ℕ) : Prop := ∀ ℓ ∈ P.PM ++ P.Pq, ¬ (ℓ : ℤ) ∣ xs P ξ ν n

variable {P ξ ν}

section Sound

variable (hF : ParamFacts P)
include hF

omit hF in
theorem q_mul_xs_succ (n : ℕ) :
    (P.q : ℤ) * xs P ξ ν (n + 1) = P.p * xs P ξ ν n + cs P ξ ν n := by
  simp only [cs, xs, Z32.carry]; ring

/-- The carry identity `s·b = p·b·y − q·b·y' − (p−q)·(b·ν)`. -/
theorem scaled_b (n : ℕ) :
    (cs P ξ ν n : ℝ) * P.b = P.p * P.b * ys P ξ ν n - P.q * P.b * ys P ξ ν (n + 1) -
      ((P.p : ℝ) - P.q) * (P.b * ν) := by
  have h := Z32.carry_eq (p := P.p) (q := P.q) (ξ := ξ) (ν := ν) (by have := hF.q1; omega) n
  simp only [cs, ys]
  linear_combination (P.b : ℝ) * h

theorem cell_spec (n : ℕ) :
    ((cell P ξ ν n : ℕ) : ℝ) ≤ P.D * ys P ξ ν n ∧ P.D * ys P ξ ν n < (cell P ξ ν n : ℕ) + 1 ∧
      cell P ξ ν n < P.D := by
  have hy0 : 0 ≤ ys P ξ ν n := Z32.yFract_nonneg n
  have hy1 : ys P ξ ν n < 1 := Z32.yFract_lt_one n
  have hD : (0 : ℝ) < P.D := by exact_mod_cast hF.D0
  have hfl : 0 ≤ ⌊(P.D : ℝ) * ys P ξ ν n⌋ := Int.floor_nonneg.2 (by positivity)
  have hc : ((cell P ξ ν n : ℕ) : ℤ) = ⌊(P.D : ℝ) * ys P ξ ν n⌋ := Int.toNat_of_nonneg hfl
  have hcR : ((cell P ξ ν n : ℕ) : ℝ) = (⌊(P.D : ℝ) * ys P ξ ν n⌋ : ℝ) := by exact_mod_cast hc
  refine ⟨?_, ?_, ?_⟩
  · rw [hcR]; exact Int.floor_le _
  · rw [hcR]; exact Int.lt_floor_add_one _
  · have : ⌊(P.D : ℝ) * ys P ξ ν n⌋ < P.D := by
      rw [Int.floor_lt]; push_cast; nlinarith
    omega

theorem res_cast (n : ℕ) : ((res P ξ ν n : ℕ) : ℤ) = xs P ξ ν n % P.M :=
  Int.toNat_of_nonneg (Int.emod_nonneg _ (by have := hF.M0; omega))

theorem res_lt (n : ℕ) : res P ξ ν n < P.M := by
  have h1 := res_cast hF (ξ := ξ) (ν := ν) n
  have h2 := Int.emod_lt_of_pos (xs P ξ ν n) (by have := hF.M0; omega : (0 : ℤ) < P.M)
  omega

theorem res_mod_ne {l : ℕ} (hl : l ∈ P.PM) {n : ℕ} (hn : ¬ (l : ℤ) ∣ xs P ξ ν n) :
    res P ξ ν n % l ≠ 0 := by
  intro h0
  apply hn
  have hlM : (l : ℤ) ∣ P.M := by
    exact_mod_cast Nat.dvd_of_mod_eq_zero (hF.PM l hl)
  have h1 : ((res P ξ ν n % l : ℕ) : ℤ) = xs P ξ ν n % l := by
    push_cast
    rw [res_cast hF, Int.emod_emod_of_dvd _ hlM]
  rw [h0, Nat.cast_zero] at h1
  exact Int.dvd_of_emod_eq_zero h1.symm

theorem rnext_eq (n : ℕ) : P.rnext (res P ξ ν n) (cs P ξ ν n) = res P ξ ν (n + 1) := by
  simp only [Params.rnext, res]
  congr 1
  have hq : ((P.q : ℤ) * P.qinv) ≡ 1 [ZMOD P.M] := by
    have := congrArg (Nat.cast : ℕ → ℤ) hF.inv
    push_cast at this
    exact this
  have hr : ((res P ξ ν n : ℕ) : ℤ) ≡ xs P ξ ν n [ZMOD P.M] := by
    rw [res_cast hF]; exact Int.mod_modEq _ _
  have : ((P.p : ℤ) * ((xs P ξ ν n % P.M).toNat : ℕ) + cs P ξ ν n) * P.qinv ≡
      xs P ξ ν (n + 1) [ZMOD P.M] := by
    calc ((P.p : ℤ) * ((xs P ξ ν n % P.M).toNat : ℕ) + cs P ξ ν n) * P.qinv
        ≡ ((P.p : ℤ) * xs P ξ ν n + cs P ξ ν n) * P.qinv [ZMOD P.M] :=
          ((hr.mul_left _).add_right _).mul_right _
      _ = xs P ξ ν (n + 1) * ((P.q : ℤ) * P.qinv) := by rw [← q_mul_xs_succ]; ring
      _ ≡ xs P ξ ν (n + 1) * 1 [ZMOD P.M] := hq.mul_left _
      _ = xs P ξ ν (n + 1) := mul_one _
  exact this

theorem cs_mod_ne {l : ℕ} (hl : l ∈ P.Pq) {n : ℕ} (hn : ¬ (l : ℤ) ∣ xs P ξ ν n) :
    cs P ξ ν n % (l : ℤ) ≠ 0 := by
  intro h0
  apply hn
  obtain ⟨hlq, hlp⟩ := hF.Pq l hl
  have hdc : (l : ℤ) ∣ cs P ξ ν n := Int.dvd_of_emod_eq_zero h0
  have hdq : (l : ℤ) ∣ P.q := by exact_mod_cast Nat.dvd_of_mod_eq_zero hlq
  have hdp : (l : ℤ) ∣ xs P ξ ν n * P.p := by
    have : xs P ξ ν n * P.p = P.q * xs P ξ ν (n + 1) - cs P ξ ν n := by
      rw [q_mul_xs_succ]; ring
    rw [this]
    exact dvd_sub (dvd_mul_of_dvd_left hdq _) hdc
  have hcop : IsCoprime (l : ℤ) (P.p : ℤ) := Nat.isCoprime_iff_coprime.2 hlp
  exact hcop.dvd_of_dvd_mul_right hdp

/-- **Soundness for a real shift in a hull interval.** -/
theorem sound {a₀ a₁ : ℤ} (hh : hullOK P a₀ a₁ = true) (hν₀ : (a₀ : ℝ) ≤ P.b * ν)
    (hν₁ : (P.b : ℝ) * ν ≤ a₁) {n : ℕ} (h0 : Avoids P ξ ν n) (h1 : Avoids P ξ ν (n + 1)) :
    vtx P ξ ν n < P.nV ∧ tix P ξ ν n < P.nA ∧ P.letter (tix P ξ ν n) = cs P ξ ν n ∧
      vtx P ξ ν (n + 1) ∈ P.succList (vtx P ξ ν n) (P.letter (tix P ξ ν n)) := by
  obtain ⟨hal₁, hal₀, hedge⟩ :=
    hullOK_spec (by have := hF.q1; omega) hF.b0 hh
  have hD := hF.D0
  obtain ⟨hc0, hc1, hcD⟩ := cell_spec hF (ξ := ξ) (ν := ν) n
  obtain ⟨hd0, hd1, hdD⟩ := cell_spec hF (ξ := ξ) (ν := ν) (n + 1)
  have hrM := res_lt hF (ξ := ξ) (ν := ν) n
  have hy0 : 0 ≤ ys P ξ ν n := Z32.yFract_nonneg n
  have hy1 : ys P ξ ν n < 1 := Z32.yFract_lt_one n
  have hz0 : 0 ≤ ys P ξ ν (n + 1) := Z32.yFract_nonneg (n + 1)
  have hz1 : ys P ξ ν (n + 1) < 1 := Z32.yFract_lt_one (n + 1)
  have hsb := scaled_b hF (ξ := ξ) (ν := ν) n
  have hp0 : (0 : ℝ) < P.p := by exact_mod_cast (by have := hF.pq; omega : 0 < P.p)
  have hq0 : (0 : ℝ) < P.q := by exact_mod_cast (by have := hF.q1; omega : 0 < P.q)
  have hb0' : (0 : ℝ) < P.b := by exact_mod_cast hF.b0
  have hpq : (0 : ℝ) < (P.p : ℝ) - P.q := by
    have : (P.q : ℝ) < P.p := by exact_mod_cast hF.pq
    linarith
  have hpb : (0 : ℝ) < P.p * P.b := by positivity
  have hqb : (0 : ℝ) < P.q * P.b := by positivity
  have e₀ : ((P.p : ℝ) - P.q) * a₀ ≤ ((P.p : ℝ) - P.q) * (P.b * ν) :=
    mul_le_mul_of_nonneg_left hν₀ hpq.le
  have e₁ : ((P.p : ℝ) - P.q) * (P.b * ν) ≤ ((P.p : ℝ) - P.q) * a₁ :=
    mul_le_mul_of_nonneg_left hν₁ hpq.le
  -- the alphabet
  have hb0 : (0 : ℤ) < P.b := by exact_mod_cast hF.b0
  have hs1 : P.sLo ≤ cs P ξ ν n := by
    have h' : ((P.b : ℤ) * (P.sLo - 1) : ℝ) < (P.b : ℝ) * cs P ξ ν n := by
      have : ((P.b * (P.sLo - 1) : ℤ) : ℝ) ≤ -((P.q : ℝ) * P.b) - ((P.p : ℝ) - P.q) * a₁ := by
        exact_mod_cast hal₁
      push_cast at this ⊢
      nlinarith [mul_nonneg hpb.le hy0, mul_lt_mul_of_pos_left hz1 hqb]
    have : (P.b : ℤ) * (P.sLo - 1) < P.b * cs P ξ ν n := by exact_mod_cast h'
    have := lt_of_mul_lt_mul_left this hb0.le
    omega
  have hs2 : cs P ξ ν n < P.sLo + P.nA := by
    have h' : (P.b : ℝ) * cs P ξ ν n < ((P.b : ℤ) * (P.sLo + P.nA) : ℤ) := by
      have : ((P.p : ℝ) * P.b - ((P.p : ℝ) - P.q) * a₀) ≤ (((P.b : ℤ) * (P.sLo + P.nA) : ℤ) : ℝ) := by
        exact_mod_cast hal₀
      nlinarith [mul_lt_mul_of_pos_left hy1 hpb, mul_nonneg hqb.le hz0]
    have : (P.b : ℤ) * cs P ξ ν n < P.b * (P.sLo + P.nA) := by exact_mod_cast h'
    exact lt_of_mul_lt_mul_left this hb0.le
  have htix : P.letter (tix P ξ ν n) = cs P ξ ν n := by
    simp only [Params.letter, tix]; omega
  have htn : tix P ξ ν n < P.nA := by simp only [tix]; omega
  refine ⟨?_, htn, htix, ?_⟩
  · simp only [vtx, Params.nV]
    calc res P ξ ν n * P.D + cell P ξ ν n < res P ξ ν n * P.D + P.D := by omega
      _ = (res P ξ ν n + 1) * P.D := by ring
      _ ≤ P.M * P.D := Nat.mul_le_mul_right _ hrM
  -- the hull edge, in the reals
  set c := cell P ξ ν n
  set c' := cell P ξ ν (n + 1)
  have hD' : (0 : ℝ) < P.D := by exact_mod_cast hF.D0
  have hA : (P.q : ℤ) * P.b * c' < P.hiAt a₀ c (cs P ξ ν n) := by
    simp only [Params.hiAt]
    have : ((P.q : ℝ) * P.b) * (c' : ℝ) < (P.p : ℝ) * P.b * ((c : ℝ) + 1) -
        (((P.p : ℝ) - P.q) * a₀ * P.D + cs P ξ ν n * P.b * P.D) := by
      have k1 := mul_le_mul_of_nonneg_left hd0 hqb.le
      have k2 := mul_lt_mul_of_pos_left hc1 hpb
      have k3 := mul_le_mul_of_nonneg_right e₀ hD'.le
      have k4 : (cs P ξ ν n : ℝ) * P.b * P.D = (P.p * P.b * ys P ξ ν n - P.q * P.b * ys P ξ ν (n + 1) -
          ((P.p : ℝ) - P.q) * (P.b * ν)) * P.D := by rw [hsb]
      nlinarith
    exact_mod_cast this
  have hB : P.loAt a₁ c (cs P ξ ν n) < (P.q : ℤ) * P.b * (c' + 1) := by
    simp only [Params.loAt]
    have : (P.p : ℝ) * P.b * (c : ℝ) - (((P.p : ℝ) - P.q) * a₁ * P.D + cs P ξ ν n * P.b * P.D) <
        ((P.q : ℝ) * P.b) * ((c' : ℝ) + 1) := by
      have k1 := mul_le_mul_of_nonneg_left hc0 hpb.le
      have k2 := mul_lt_mul_of_pos_left hd1 hqb
      have k3 := mul_le_mul_of_nonneg_right e₁ hD'.le
      have k4 : (cs P ξ ν n : ℝ) * P.b * P.D = (P.p * P.b * ys P ξ ν n - P.q * P.b * ys P ξ ν (n + 1) -
          ((P.p : ℝ) - P.q) * (P.b * ν)) * P.D := by rw [hsb]
      nlinarith
    exact_mod_cast this
  have hE : P.hullEdge a₀ a₁ c (P.letter (tix P ξ ν n)) c' = true := by
    simp only [Params.hullEdge, htix, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hA, hB⟩
  obtain ⟨hA', hB'⟩ := hedge c hcD _ htn c' hdD hE
  rw [htix] at hA' hB' ⊢
  -- membership, as in `Gen.sound`
  have hdiv : vtx P ξ ν n / P.D = res P ξ ν n := by
    simp only [vtx]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hD, Nat.div_eq_of_lt hcD, zero_add]
  have hmod : vtx P ξ ν n % P.D = c := by
    simp only [vtx]
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hcD]
  simp only [Params.succList, hdiv, hmod, rnext_eq hF (ξ := ξ) (ν := ν)]
  split_ifs with hcond
  swap
  · exfalso
    apply hcond
    simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq]
    exact ⟨⟨fun l hl => res_mod_ne hF hl (h0 l (List.mem_append_left _ hl)),
      fun l hl => cs_mod_ne hF hl (h0 l (List.mem_append_right _ hl))⟩,
      fun l hl => res_mod_ne hF hl (h1 l (List.mem_append_left _ hl))⟩
  rw [List.mem_map]
  set w : ℤ := (P.q : ℤ) * P.b
  have hw : 0 < w := by
    have := hF.q1
    have : (0 : ℤ) < P.q := by omega
    positivity
  refine ⟨c', List.mem_filter.2 ⟨?_, ?_⟩, ?_⟩
  · rw [List.mem_range'_1]
    have h1 : P.cLo c (cs P ξ ν n) ≤ c' := by
      simp only [Params.cLo]
      rw [Int.toNat_le]
      have : P.lo c (cs P ξ ν n) / w < (c' : ℤ) + 1 := by
        rw [Int.ediv_lt_iff_lt_mul hw]; linarith
      change P.lo c (cs P ξ ν n) / w ≤ (c' : ℤ)
      omega
    have h2 : c' < P.cHi c (cs P ξ ν n) := by
      simp only [Params.cHi]
      refine lt_min hdD ?_
      rw [Int.lt_toNat]
      have : (c' : ℤ) ≤ (P.hi c (cs P ξ ν n) - 1) / w := by
        rw [Int.le_ediv_iff_mul_le hw]; linarith
      change (c' : ℤ) < (P.hi c (cs P ξ ν n) - 1) / w + 1
      omega
    omega
  · simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hA', hB'⟩
  · simp only [vtx, c']

end Sound

end Nu

/-- **A checked certificate with a hull check is a theorem for every real shift in the
interval**: for every real `ν ∈ [a₀/b, a₁/b]` and every `ξ ≠ 0`, infinitely many of
`⌊ξ(p/q)ⁿ + ν⌋` are divisible by a member of `PM ++ Pq`. -/
@[category API, AMS 11 37, ref "DN05", group "dubc2_shift"]
theorem divisor_set_of_checked_hull {P : Params} {C : Cert} (hc : Checked P C) {a₀ a₁ : ℤ}
    (hh : hullOK P a₀ a₁ = true) {ν : ℝ} (hν₀ : (a₀ : ℝ) / P.b ≤ ν) (hν₁ : ν ≤ (a₁ : ℝ) / P.b)
    {ξ : ℝ} (hξ : ξ ≠ 0) :
    ∃ᶠ n in atTop, ∃ ℓ ∈ P.PM ++ P.Pq, (ℓ : ℤ) ∣ Z32.xInt P.p P.q ξ ν n := by
  have hF : ParamFacts P := by
    have hh := hc.head
    simp only [checkHead, Bool.and_eq_true] at hh
    exact paramFacts hh.1.1.1.1.1
  have hb : (0 : ℝ) < P.b := by exact_mod_cast hF.b0
  have h₀ : (a₀ : ℝ) ≤ P.b * ν := by rw [div_le_iff₀ hb] at hν₀; linarith
  have h₁ : (P.b : ℝ) * ν ≤ a₁ := by rw [le_div_iff₀ hb] at hν₁; linarith
  rw [Filter.frequently_atTop]
  intro N
  by_contra hcon
  push Not at hcon
  have hav : ∀ n, N ≤ n → Nu.Avoids P ξ ν n := fun n hn ℓ hℓ => hcon n hn ℓ hℓ
  have hs := fun n (hn : N ≤ n) => Nu.sound hF hh h₀ h₁ (hav n hn) (hav (n + 1) (by omega))
  have hp : IsPath P N (Nu.vtx P ξ ν) (Nu.tix P ξ ν) :=
    ⟨fun n hn => (hs n hn).1, fun n hn => (hs n hn).2.1, fun n hn => (hs n hn).2.2.2⟩
  obtain ⟨M₀, per, hper, hp'⟩ := isEventuallyPeriodic_of_path hc hp
  apply Z32.not_isEventuallyPeriodic_carry (p := P.p) (q := P.q) (ξ := ξ) (ν := ν) hF.q1 hF.pq
    hF.cop hξ
  refine ⟨max M₀ N, per, hper, fun k hk => ?_⟩
  have e1 := (hs k (by omega)).2.2.1
  have e2 := (hs (k + per) (by omega)).2.2.1
  change Nu.cs P ξ ν (k + per) = Nu.cs P ξ ν k
  rw [← e1, ← e2, hp' k (by omega)]

end DubC2.Gen
