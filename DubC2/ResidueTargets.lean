/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.NuCircle
import DubC2.Atlas
import Mathlib.Data.Nat.ChineseRemainder

/-!
# Residue targets and the shift circle (plans/plan-dubC2-transform.html, T6(a))

Since `⌊z + ν + k⌋ = ⌊z + ν⌋ + k` for `k ∈ ℤ`, an integer shift of `ν` translates the target
residues.  The divisor-set problem at `ν + k` ("some `ℓ ∈ 𝒫` divides `xₙ(ν + k)` infinitely
often") *is* the residue-target problem at `ν` with one target `sℓ ≡ −k (mod ℓ)` per modulus
(`Gen.hitsTargets_iff_shift`).  By the Chinese remainder theorem every choice of one target
residue per prime is reached by some `k` (`Gen.exists_crt_shift`), unique mod `M = ∏𝒫`.  So the
parameter space of the one-target problem is

  `(ν mod 1, (sℓ)ℓ ∈ ∏ ℤ/ℓ) ≅ ν mod M`, the shift circle `ℝ/Mℤ` of `DubC2/NuCircle.lean`:

a certificate at shift `a/b` proves the target theorem at every `a/b − k` with the translated
targets (`Gen.hitsTargets_of_checked`), and the `ν = −1` column of the atlas is the floor sequence
hitting residue `1` (`Gen.frequently_modEq_one_of_neg_one`).

The bridge to `Z32.residue_not_eventually_constant` ([cert32] T1: `⌊ξ(3/2)ⁿ⌋ mod m` is not
eventually constant, `ξ > 0`, `m ≥ 3`) is `Gen.not_eventually_modEq`: hitting a target set
infinitely often forbids eventual capture at every residue that misses all targets.  The two
results cover opposite ends: [cert32] T1 has every residue but needs `ξ > 0` and `ν = 0`; an atlas
cell has every real `ξ ≠ 0` and its own `ν`, but only the residues avoiding its targets
(`Atlas.floor_three_halves_not_eventually_unit`: no unit residue mod `770` captures
`⌊ξ(3/2)ⁿ⌋`, for any real `ξ ≠ 0`).

Several targets per modulus are a weaker statement than any one of them; an exact certificate for a
target *set* needs `Gen.Params.succList` to filter by the set, which is not done here.
-/

namespace DubC2.Gen

open Filter

variable {ι : Type*}

/-- Pointwise: with `m ∣ k + s`, `m ∣ x + k` iff `x ≡ s (mod m)`. -/
theorem dvd_add_shift_iff {m k s x : ℤ} (hk : m ∣ k + s) : m ∣ x + k ↔ x ≡ s [ZMOD m] := by
  rw [Int.modEq_iff_dvd]
  constructor
  · intro h
    have := dvd_sub hk h
    rwa [show k + s - (x + k) = s - x by ring] at this
  · intro h
    have := dvd_sub hk h
    rwa [show k + s - (s - x) = x + k by ring] at this

/-- An integer shift turns divisibility into one target residue per modulus. -/
theorem frequently_dvd_shift_iff {x : ℕ → ℤ} {l : List ι} {m s : ι → ℤ} {k : ℤ}
    (hk : ∀ i ∈ l, m i ∣ k + s i) :
    (∃ᶠ n in atTop, ∃ i ∈ l, m i ∣ x n + k) ↔ ∃ᶠ n in atTop, ∃ i ∈ l, x n ≡ s i [ZMOD m i] :=
  ⟨fun h => h.mono fun _ ⟨i, hi, hd⟩ => ⟨i, hi, (dvd_add_shift_iff (hk i hi)).1 hd⟩,
   fun h => h.mono fun _ ⟨i, hi, hd⟩ => ⟨i, hi, (dvd_add_shift_iff (hk i hi)).2 hd⟩⟩

/-- **The translation lemma.**  The divisor-set problem at `ν + k` is the residue-target problem
at `ν` with targets `sᵢ ≡ −k (mod mᵢ)`. -/
@[category API, AMS 11 37, ref "DN05", group "dubc2_shift"]
theorem hitsTargets_iff_shift (p q : ℕ) (ξ ν : ℝ) {l : List ι} {m s : ι → ℤ} {k : ℤ}
    (hk : ∀ i ∈ l, m i ∣ k + s i) :
    (∃ᶠ n in atTop, ∃ i ∈ l, Z32.xInt p q ξ ν n ≡ s i [ZMOD m i]) ↔
      ∃ᶠ n in atTop, ∃ i ∈ l, m i ∣ Z32.xInt p q ξ (ν + k) n := by
  simp_rw [xInt_add_int]
  exact (frequently_dvd_shift_iff hk).symm

/-- **The Chinese remainder step.**  For pairwise coprime positive moduli, every choice of one
target residue per modulus is reached by an integer shift. -/
@[category API, AMS 11, ref "DN05", group "dubc2_shift"]
theorem exists_crt_shift {l : List ι} {m : ι → ℕ} (hl : l.Pairwise (Function.onFun Nat.Coprime m))
    (hpos : ∀ i ∈ l, 0 < m i) (s : ι → ℤ) : ∃ k : ℤ, ∀ i ∈ l, (m i : ℤ) ∣ k + s i := by
  obtain ⟨k, hk⟩ := Nat.chineseRemainderOfList (fun i => ((-s i) % (m i : ℤ)).toNat) m l hl
  refine ⟨k, fun i hi => ?_⟩
  have hm : (0 : ℤ) < m i := by exact_mod_cast hpos i hi
  have h1 : (k : ℤ) ≡ (((-s i) % (m i : ℤ)).toNat : ℤ) [ZMOD m i] :=
    Int.natCast_modEq_iff.2 (hk i hi)
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hm.ne')] at h1
  have h2 : (k : ℤ) ≡ -s i [ZMOD m i] := h1.trans (Int.mod_modEq _ _)
  have := h2.symm.dvd
  rwa [sub_neg_eq_add] at this

/-- **The dictionary** `(ν mod 1, one target per prime) ↔ ν mod M`: for pairwise coprime positive
moduli and any targets there is an integer `k` with: the orbit at `ν` hits a target infinitely
often iff some modulus divides the orbit at `ν + k` infinitely often. -/
@[category research solved, AMS 11 37, ref "DN05", group "dubc2_shift"]
theorem hitsTargets_iff_exists_shift (p q : ℕ) (ξ ν : ℝ) {l : List ι} {m : ι → ℕ}
    (hl : l.Pairwise (Function.onFun Nat.Coprime m)) (hpos : ∀ i ∈ l, 0 < m i) (s : ι → ℤ) :
    ∃ k : ℤ, ((∃ᶠ n in atTop, ∃ i ∈ l, Z32.xInt p q ξ ν n ≡ s i [ZMOD m i]) ↔
      ∃ᶠ n in atTop, ∃ i ∈ l, (m i : ℤ) ∣ Z32.xInt p q ξ (ν + k) n) := by
  obtain ⟨k, hk⟩ := exists_crt_shift hl hpos s
  exact ⟨k, hitsTargets_iff_shift p q ξ ν (m := fun i => (m i : ℤ)) hk⟩

/-- **A certificate is a family of target theorems.**  A checked certificate at shift `a/b`
proves, at every `ν` with `ν + k = a/b` (`k ∈ ℤ`), that `xₙ(ν)` hits the target `sℓ` mod some
`ℓ ∈ PM ++ Pq` infinitely often, whenever `ℓ ∣ k + sℓ`. -/
@[category research solved, AMS 11 37, ref "DN05", group "dubc2_shift"]
theorem hitsTargets_of_checked {P : Params} {C : Cert} (hc : Checked P C) {ξ ν : ℝ} (hξ : ξ ≠ 0)
    {k : ℤ} (hν : ν + k = (P.a : ℝ) / P.b) {s : ℕ → ℤ}
    (hk : ∀ ℓ ∈ P.PM ++ P.Pq, (ℓ : ℤ) ∣ k + s ℓ) :
    ∃ᶠ n in atTop, ∃ ℓ ∈ P.PM ++ P.Pq, Z32.xInt P.p P.q ξ ν n ≡ s ℓ [ZMOD ℓ] := by
  rw [hitsTargets_iff_shift P.p P.q ξ ν (m := fun ℓ : ℕ => (ℓ : ℤ)) hk, hν]
  exact divisor_set_of_checked hc hξ

/-- **The bridge to residue capture.**  If `x` hits one of the targets `sᵢ (mod mᵢ)` infinitely
often, then `x mod L` is not eventually `r` for any `r` that misses every target (`mᵢ ∣ L`). -/
@[category API, AMS 11 37, ref "DN05" "Dub09AA", group "dubc2_shift"]
theorem not_eventually_modEq {x : ℕ → ℤ} {l : List ι} {m s : ι → ℤ} {L r : ℤ}
    (hL : ∀ i ∈ l, m i ∣ L) (hr : ∀ i ∈ l, ¬ r ≡ s i [ZMOD m i])
    (h : ∃ᶠ n in atTop, ∃ i ∈ l, x n ≡ s i [ZMOD m i]) :
    ¬ ∀ᶠ n in atTop, x n ≡ r [ZMOD L] := by
  intro he
  obtain ⟨n, ⟨i, hi, h1⟩, h2⟩ := (h.and_eventually he).exists
  exact hr i hi ((h2.of_dvd (hL i hi)).symm.trans h1)

/-- Divisibility is the target `0`. -/
theorem frequently_modEq_zero_of_dvd {x : ℕ → ℤ} {l : List ℤ}
    (h : ∃ᶠ n in atTop, ∃ ℓ ∈ l, ℓ ∣ x n) :
    ∃ᶠ n in atTop, ∃ ℓ ∈ l, x n ≡ 0 [ZMOD ℓ] :=
  h.mono fun _ ⟨ℓ, hℓ, hd⟩ => ⟨ℓ, hℓ, Int.modEq_zero_iff_dvd.2 hd⟩

/-- **The `ν = −1` column is the floor sequence hitting residue `1`.** -/
@[category API, AMS 11 37, ref "DN05" "Nov12", group "dubc2_shift"]
theorem frequently_modEq_one_of_neg_one {t : ℕ → ℝ} {l : List ℤ}
    (h : ∃ᶠ n in atTop, ∃ ℓ ∈ l, ℓ ∣ ⌊t n + -1⌋) :
    ∃ᶠ n in atTop, ∃ ℓ ∈ l, ⌊t n⌋ ≡ 1 [ZMOD ℓ] :=
  h.mono fun n ⟨ℓ, hℓ, hd⟩ => ⟨ℓ, hℓ, by
    rw [← sub_eq_add_neg, Int.floor_sub_one] at hd
    exact (Int.modEq_iff_dvd.2 hd).symm⟩

end DubC2.Gen

namespace DubC2.Atlas

open Filter DubC2.Gen

/-! ## Instances from the atlas -/

/-- From the `ν = −1` cell `(3/2, {2,3})` ([DN05] Lemma 2 shape): for every real `ξ ≠ 0`,
`⌊ξ(3/2)ⁿ⌋` is odd or `≡ 1 (mod 3)` infinitely often. -/
@[category research solved, AMS 11 37, ref "DN05", group "dubc2_shift"]
theorem floor_three_halves_one_mod_two_three {ξ : ℝ} (hξ : ξ ≠ 0) :
    ∃ᶠ n in atTop, ∃ ℓ ∈ ([2, 3] : List ℤ), ⌊ξ * ((3 : ℝ) / 2) ^ n⌋ ≡ 1 [ZMOD ℓ] :=
  frequently_modEq_one_of_neg_one (b3_2_num1_P2_3 hξ)

/-- From the `ν = −1` cell `(4/3, {2,3})`: `⌊ξ(4/3)ⁿ⌋` is odd or `≡ 1 (mod 3)` infinitely
often, for every real `ξ ≠ 0`. -/
@[category research solved, AMS 11 37, ref "DN05", group "dubc2_shift"]
theorem floor_four_thirds_one_mod_two_three {ξ : ℝ} (hξ : ξ ≠ 0) :
    ∃ᶠ n in atTop, ∃ ℓ ∈ ([2, 3] : List ℤ), ⌊ξ * ((4 : ℝ) / 3) ^ n⌋ ≡ 1 [ZMOD ℓ] :=
  frequently_modEq_one_of_neg_one (b4_3_num1_P2_3 hξ)

/-- From the `ν = −1` cells `(6/5, {2,3,5})` and `(5/2, {2,3,5})` ([DN05] Thm 3, [Nov12]
Thm 1.4 in target form). -/
@[category research solved, AMS 11 37, ref "DN05" "Nov12", group "dubc2_shift"]
theorem floor_one_mod_two_three_five {ξ : ℝ} (hξ : ξ ≠ 0) :
    (∃ᶠ n in atTop, ∃ ℓ ∈ ([2, 3, 5] : List ℤ), ⌊ξ * ((6 : ℝ) / 5) ^ n⌋ ≡ 1 [ZMOD ℓ]) ∧
      ∃ᶠ n in atTop, ∃ ℓ ∈ ([2, 3, 5] : List ℤ), ⌊ξ * ((5 : ℝ) / 2) ^ n⌋ ≡ 1 [ZMOD ℓ] :=
  ⟨frequently_modEq_one_of_neg_one (b6_5_num1_P2_3_5 hξ),
    frequently_modEq_one_of_neg_one (b5_2_num1_P2_3_5 hξ)⟩

/-- **Residue non-capture at every real `ξ ≠ 0`, unit residues** (the bridge to
`Z32.residue_not_eventually_constant`).  For every real `ξ ≠ 0`, `⌊ξ(3/2)ⁿ⌋ mod 770` is not
eventually equal to any residue prime to `770`. -/
@[category research solved, AMS 11 37, ref "DN05" "FS67", group "dubc2_shift"]
theorem floor_three_halves_not_eventually_unit {ξ : ℝ} (hξ : ξ ≠ 0) {r : ℤ}
    (hr : ∀ ℓ ∈ ([2, 5, 7, 11] : List ℤ), ¬ ℓ ∣ r) :
    ¬ ∀ᶠ n in atTop, ⌊ξ * ((3 : ℝ) / 2) ^ n⌋ ≡ r [ZMOD 770] :=
  not_eventually_modEq (m := id) (s := fun _ => 0) (by decide)
    (fun ℓ hℓ h => hr ℓ hℓ (Int.modEq_zero_iff_dvd.1 h))
    (frequently_modEq_zero_of_dvd (b3_2_nu0_P2_5_7_11 hξ))

/-- The same from the `ν = −1` cell: `⌊ξ(3/2)ⁿ⌋ mod 6` is not eventually `0` or `2`, for every
real `ξ ≠ 0`. -/
@[category research solved, AMS 11 37, ref "DN05", group "dubc2_shift"]
theorem floor_three_halves_not_eventually_mod_six {ξ : ℝ} (hξ : ξ ≠ 0) {r : ℤ}
    (hr : r = 0 ∨ r = 2) :
    ¬ ∀ᶠ n in atTop, ⌊ξ * ((3 : ℝ) / 2) ^ n⌋ ≡ r [ZMOD 6] :=
  not_eventually_modEq (m := id) (s := fun _ => 1) (by decide)
    (by rcases hr with rfl | rfl <;> decide) (floor_three_halves_one_mod_two_three hξ)

end DubC2.Atlas
