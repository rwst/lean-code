/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.GenBlocks
import DubC2.ShiftSchema

/-!
# The mirror `ν ↦ 1 − ν`

plan-dubC2-transform, conjecture N-1 (note-dubC2T-M0 §7): the certified `ν`-set of every
residue-free sweep is invariant under `ν ↦ 1 − ν`.  The reason is the substitution
`(ξ, x, y, s, ν) ↦ (−ξ, −x, 1 − y, −s, 1 − ν)`: `−ξ(p/q)ⁿ + 1 − ν = 1 − (ξ(p/q)ⁿ + ν)`, so
`⌊−ξ(p/q)ⁿ + 1 − ν⌋ = −⌊ξ(p/q)ⁿ + ν⌋` unless `ξ(p/q)ⁿ + ν` is an integer, and that happens for
only finitely many `n` (`eventually_fract_ne`: two hits `n₀ < m` force `q^{m−n₀}` to divide a
fixed integer).  Divisibility is blind to the sign.

## Main results

* `DubC2.Mirror.frequently_mirror_iff` — for coprime `p > q ≥ 2`, `ξ ≠ 0`, any real `ν` and any
  sign-symmetric predicate `R` on `ℤ` (a divisor set, compositeness, …): `R(⌊ξ(p/q)ⁿ + ν⌋)` holds
  infinitely often iff `R(⌊−ξ(p/q)ⁿ + 1 − ν⌋)` does.  As `ξ` ranges over `ℝ ∖ {0}`, so does `−ξ`:
  a divisor set is unavoidable at `ν` iff it is at `1 − ν`.
* `DubC2.Mirror.divisor_set_mirror_of_checked` — a checked certificate at `ν = a/b` is also a
  theorem at `1 − a/b` (e.g. the atlas cells at `ν = −1` give cells at `ν = 2`).
* `DubC2.Mirror.six_fifths_two_three_five_mirror` — the mirror of the `6/5` arc of
  `DubC2/ShiftSchema.lean`: `{2,3,5}` is unavoidable for `⌊ξ(6/5)ⁿ + ν⌋` at every real
  `ν ∈ [5/3, 2] + 30ℤ`.  (The `3/2`, `4/3` and `5/2` arcs there are already mirror-closed.)
* `DubC2.Mirror.Pseudo.mirror` — the same substitution on avoiding pseudo-orbits
  (`DubC2.Gen.Pseudo`) with the shift `a/b` replaced by `(b − a)/b`, provided no `yₙ` is `0`
  (the endpoint of `[0, 1)`).
-/

namespace DubC2.Mirror

open Filter Z32

variable {p q : ℕ} {ξ ν : ℝ}

/-! ## Real orbits -/

theorem orb_mirror (n : ℕ) : orb p q (-ξ) (1 - ν) n = 1 - orb p q ξ ν n := by
  simp only [orb]; ring

/-- Off the integers, the mirror orbit has integer part `−xₙ`. -/
@[category API, AMS 11 37, ref "DN05", group "dubc2_mirror"]
theorem xInt_mirror {n : ℕ} (h : Int.fract (orb p q ξ ν n) ≠ 0) :
    xInt p q (-ξ) (1 - ν) n = -xInt p q ξ ν n := by
  simp only [xInt, orb_mirror]
  set t := orb p q ξ ν n
  have h0 : 0 < Int.fract t := lt_of_le_of_ne (Int.fract_nonneg t) (Ne.symm h)
  have h1 := Int.fract_lt_one t
  rw [Int.floor_eq_iff]
  rw [Int.fract] at h0 h1
  push_cast
  constructor <;> linarith

/-- For coprime `p > q ≥ 2` and `ξ ≠ 0`, the orbit `ξ(p/q)ⁿ + ν` meets `ℤ` only finitely often. -/
@[category API, AMS 11 37, ref "DN05", group "dubc2_mirror"]
theorem eventually_fract_ne (hq : 1 < q) (hpq : q < p) (hcop : Nat.Coprime p q) (hξ : ξ ≠ 0) :
    ∀ᶠ n in atTop, Int.fract (orb p q ξ ν n) ≠ 0 := by
  by_contra hcon
  rw [Filter.not_eventually, Filter.frequently_atTop] at hcon
  simp only [ne_eq, not_not] at hcon
  have hit : ∀ n, Int.fract (orb p q ξ ν n) = 0 → orb p q ξ ν n = (xInt p q ξ ν n : ℝ) := by
    intro n hn
    have := Int.floor_add_fract (orb p q ξ ν n)
    rw [hn, add_zero] at this
    exact this.symm
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hr : (1 : ℝ) < (p : ℝ) / q := by
    rw [one_lt_div hqR]; exact_mod_cast hpq
  -- the difference of two hits `n₀ < n₀ + k`
  have hdiff : ∀ n₀ k, Int.fract (orb p q ξ ν n₀) = 0 → Int.fract (orb p q ξ ν (n₀ + k)) = 0 →
      ((xInt p q ξ ν (n₀ + k) - xInt p q ξ ν n₀ : ℤ) : ℝ) =
        ξ * ((p : ℝ) / q) ^ n₀ * (((p : ℝ) / q) ^ k - 1) := by
    intro n₀ k h₀ h₁
    push_cast
    rw [← hit _ h₀, ← hit _ h₁]
    simp only [orb]; ring
  obtain ⟨n₀, -, h₀⟩ := hcon 0
  obtain ⟨m₁, hm₁, h₁⟩ := hcon (n₀ + 1)
  obtain ⟨k₁, rfl⟩ : ∃ k₁, m₁ = n₀ + k₁ := ⟨m₁ - n₀, by omega⟩
  set d₁ := xInt p q ξ ν (n₀ + k₁) - xInt p q ξ ν n₀ with hd₁
  have e₁ : (d₁ : ℝ) = ξ * ((p : ℝ) / q) ^ n₀ * (((p : ℝ) / q) ^ k₁ - 1) := hdiff n₀ k₁ h₀ h₁
  have hd₁0 : d₁ ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero] at e₁
    have : ((p : ℝ) / q) ^ k₁ - 1 ≠ 0 :=
      sub_ne_zero.2 (one_lt_pow₀ hr (by omega)).ne'
    exact (mul_ne_zero (mul_ne_zero hξ (pow_ne_zero _ (by positivity))) this) e₁.symm
  obtain ⟨m, hm, h₂⟩ := hcon (n₀ + k₁ + d₁.natAbs * q ^ k₁ + 1)
  obtain ⟨k, rfl⟩ : ∃ k, m = n₀ + k := ⟨m - n₀, by omega⟩
  set d := xInt p q ξ ν (n₀ + k) - xInt p q ξ ν n₀
  have e : (d : ℝ) = ξ * ((p : ℝ) / q) ^ n₀ * (((p : ℝ) / q) ^ k - 1) := hdiff n₀ k h₀ h₂
  -- `d (p^{k₁} − q^{k₁}) q^k = d₁ (p^k − q^k) q^{k₁}`
  have key : d * ((p : ℤ) ^ k₁ - (q : ℤ) ^ k₁) * (q : ℤ) ^ k =
      d₁ * ((p : ℤ) ^ k - (q : ℤ) ^ k) * (q : ℤ) ^ k₁ := by
    have hq0 : (q : ℝ) ≠ 0 := hqR.ne'
    have hk : ((p : ℝ) / q) ^ k * (q : ℝ) ^ k = (p : ℝ) ^ k := by
      rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hq0)]
    have hk₁ : ((p : ℝ) / q) ^ k₁ * (q : ℝ) ^ k₁ = (p : ℝ) ^ k₁ := by
      rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hq0)]
    have : (d : ℝ) * ((p : ℝ) ^ k₁ - (q : ℝ) ^ k₁) * (q : ℝ) ^ k =
        (d₁ : ℝ) * ((p : ℝ) ^ k - (q : ℝ) ^ k) * (q : ℝ) ^ k₁ := by
      linear_combination ((p : ℝ) ^ k₁ - (q : ℝ) ^ k₁) * (q : ℝ) ^ k * e -
        ((p : ℝ) ^ k - (q : ℝ) ^ k) * (q : ℝ) ^ k₁ * e₁ +
        ξ * ((p : ℝ) / q) ^ n₀ * ((p : ℝ) ^ k₁ - (q : ℝ) ^ k₁) * hk -
        ξ * ((p : ℝ) / q) ^ n₀ * ((p : ℝ) ^ k - (q : ℝ) ^ k) * hk₁
    exact_mod_cast this
  have hcopZ : IsCoprime ((q : ℤ) ^ k) ((p : ℤ) ^ k - (q : ℤ) ^ k) := by
    have h := (Nat.isCoprime_iff_coprime.2 hcop.symm).pow (m := k) (n := k)
    have := h.add_mul_left_right (-1)
    simpa [sub_eq_add_neg] using this
  have hdvd : (q : ℤ) ^ k ∣ d₁ * (q : ℤ) ^ k₁ := by
    have : (q : ℤ) ^ k ∣ ((p : ℤ) ^ k - (q : ℤ) ^ k) * (d₁ * (q : ℤ) ^ k₁) :=
      ⟨d * ((p : ℤ) ^ k₁ - (q : ℤ) ^ k₁), by linear_combination key.symm⟩
    exact hcopZ.dvd_of_dvd_mul_left this
  have hle : q ^ k ≤ d₁.natAbs * q ^ k₁ := by
    have := Int.natAbs_dvd_natAbs.2 hdvd
    simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at this
    exact Nat.le_of_dvd (Nat.mul_pos (Int.natAbs_pos.2 hd₁0) (by positivity)) this
  have := Nat.lt_pow_self (n := k) hq
  omega

/-- **The mirror, one direction.**  If `R(⌊ξ(p/q)ⁿ + ν⌋)` holds infinitely often for a
sign-symmetric `R`, so does `R(⌊−ξ(p/q)ⁿ + 1 − ν⌋)`. -/
@[category API, AMS 11 37, ref "DN05", group "dubc2_mirror"]
theorem frequently_mirror (hq : 1 < q) (hpq : q < p) (hcop : Nat.Coprime p q) (hξ : ξ ≠ 0)
    {R : ℤ → Prop} (hR : ∀ z, R (-z) ↔ R z) (h : ∃ᶠ n in atTop, R (xInt p q ξ ν n)) :
    ∃ᶠ n in atTop, R (xInt p q (-ξ) (1 - ν) n) :=
  h.mp ((eventually_fract_ne hq hpq hcop hξ).mono fun n hn hR' => by
    rwa [xInt_mirror hn, hR])

/-- **N-1, the mirror symmetry.**  For coprime `p > q ≥ 2`, `ξ ≠ 0`, every real `ν` and every
sign-symmetric `R`: `R(⌊ξ(p/q)ⁿ + ν⌋)` infinitely often iff `R(⌊−ξ(p/q)ⁿ + 1 − ν⌋)` infinitely
often.  For `R z = ∃ ℓ ∈ 𝒫, ℓ ∣ z`: a divisor set is unavoidable at `ν` iff it is at `1 − ν`. -/
@[category research solved, AMS 11 37, ref "DN05", group "dubc2_mirror"]
theorem frequently_mirror_iff (hq : 1 < q) (hpq : q < p) (hcop : Nat.Coprime p q) (hξ : ξ ≠ 0)
    {R : ℤ → Prop} (hR : ∀ z, R (-z) ↔ R z) :
    (∃ᶠ n in atTop, R (xInt p q ξ ν n)) ↔ ∃ᶠ n in atTop, R (xInt p q (-ξ) (1 - ν) n) := by
  refine ⟨frequently_mirror hq hpq hcop hξ hR, fun h => ?_⟩
  simpa using frequently_mirror hq hpq hcop (neg_ne_zero.2 hξ) hR h

/-- Divisibility by a member of a list is sign-symmetric. -/
theorem dvd_list_neg (L : List ℕ) (z : ℤ) :
    (∃ ℓ ∈ L, (ℓ : ℤ) ∣ -z) ↔ ∃ ℓ ∈ L, (ℓ : ℤ) ∣ z := by
  simp only [dvd_neg]

/-- **A checked certificate is also a theorem at the mirror shift `1 − a/b`.** -/
@[category API, AMS 11 37, ref "DN05", group "dubc2_mirror"]
theorem divisor_set_mirror_of_checked {P : Gen.Params} {C : Gen.Cert} (hc : Gen.Checked P C)
    (hξ : ξ ≠ 0) :
    ∃ᶠ n in atTop, ∃ ℓ ∈ P.PM ++ P.Pq, (ℓ : ℤ) ∣ xInt P.p P.q ξ (1 - (P.a : ℝ) / P.b) n := by
  have hF : Gen.ParamFacts P := by
    have hh := hc.head
    simp only [Gen.checkHead, Bool.and_eq_true] at hh
    exact Gen.paramFacts hh.1.1.1.1.1
  have h := Gen.divisor_set_of_checked hc (neg_ne_zero.2 hξ)
  simpa using frequently_mirror (R := fun z => ∃ ℓ ∈ P.PM ++ P.Pq, (ℓ : ℤ) ∣ z) hF.q1 hF.pq
    hF.cop (neg_ne_zero.2 hξ) (dvd_list_neg _) h

/-- **The mirror of the `6/5` arc: `{2,3,5}` is unavoidable for `⌊ξ(6/5)ⁿ + ν⌋` at every real
`ν ∈ [5/3, 2] + 30ℤ`.**  At `ν = 2` this is the mirror of the atlas cell `ν = −1`. -/
@[category research solved, AMS 11 37, ref "DN05" "Nov12", group "dubc2_mirror"]
theorem six_fifths_two_three_five_mirror (hξ : ξ ≠ 0) (k : ℤ) (h1 : 5 / 3 ≤ ν - 30 * k)
    (h2 : ν - 30 * k ≤ 2) :
    ∃ᶠ n in atTop, (2 : ℤ) ∣ xInt 6 5 ξ ν n ∨ (3 : ℤ) ∣ xInt 6 5 ξ ν n ∨
      (5 : ℤ) ∣ xInt 6 5 ξ ν n := by
  have h := Schema.six_fifths_two_three_five (ν := 1 - ν) (neg_ne_zero.2 hξ) (-k)
    (by push_cast; linarith) (by push_cast; linarith)
  have hR : ∀ z : ℤ, ((2 : ℤ) ∣ -z ∨ (3 : ℤ) ∣ -z ∨ (5 : ℤ) ∣ -z) ↔
      ((2 : ℤ) ∣ z ∨ (3 : ℤ) ∣ z ∨ (5 : ℤ) ∣ z) := by
    simp only [dvd_neg, implies_true]
  simpa using frequently_mirror (R := fun z => (2 : ℤ) ∣ z ∨ (3 : ℤ) ∣ z ∨ (5 : ℤ) ∣ z)
    (by norm_num) (by norm_num) (by norm_num) (neg_ne_zero.2 hξ) hR h

/-! ## Pseudo-orbits -/

/-- The mirror cell: the shift `a/b` becomes `(b − a)/b = 1 − a/b`. -/
def _root_.DubC2.Gen.Params.mirror (P : Gen.Params) : Gen.Params := { P with a := P.b - P.a }

/-- **The mirror of an avoiding pseudo-orbit** is an avoiding pseudo-orbit of the mirror cell,
as long as no `yₙ` sits at the endpoint `0`. -/
@[category API, AMS 11 37, ref "Oda26", group "dubc2_mirror"]
theorem Pseudo.mirror {P : Gen.Params} {x : ℕ → ℤ} {y : ℕ → ℝ} {s : ℕ → ℤ} (hb : 0 < P.b)
    (h : Gen.Pseudo P x y s) (hy : ∀ n, y n ≠ 0) :
    Gen.Pseudo P.mirror (fun n => -x n) (fun n => 1 - y n) (fun n => -s n) where
  y0 n := by linarith [h.y1 n]
  y1 n := by linarith [lt_of_le_of_ne (h.y0 n) (hy n).symm]
  recx n := by simp only [Gen.Params.mirror]; linarith [h.recx n]
  recy n := by
    have e := h.recy n
    have hb' : (P.b : ℝ) ≠ 0 := by have : (0 : ℝ) < P.b := by exact_mod_cast hb
                                   exact this.ne'
    simp only [Gen.Params.mirror]
    push_cast
    rw [sub_div, div_self hb']
    linear_combination (-1 : ℝ) * e
  avoid n ℓ hℓ := by simpa [dvd_neg] using h.avoid n ℓ hℓ

end DubC2.Mirror
