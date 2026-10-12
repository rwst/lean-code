/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Oda26.OrbitBasics
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Carry words and residues ([Oda26] Lemmas 18, 64, 66, 72)

For a carry word `c₀ c₁ ⋯` put `C₀ = 0`, `C_{j+1} = a·C_j + bʲ·c_j`.  Any integer sequence with
`b·Q_{n+1} = a·Qₙ + cₙ` then satisfies [Oda26] (8): `bʲ·Q_j = aʲ·Q₀ + C_j`.  Everything here is a
consequence of that identity:

* `Oda.pow_mul_eq` — (8).
* `Oda.modEq_of_same_word` — **Lemma 64(i)**: the word of length `ℓ` fixes `Q₀ mod b^ℓ`.
* `Oda.theta_eq`, `Oda.theta0_mem` — **Lemma 64(ii)**, the exact fractional-part interval
  (the converse direction is `Oda.window_realized`).
* `Oda.dvd_iff_root` — **Lemma 64(iii) / Lemma 18**: for `p ∤ ab`, `p ∣ Q_j ⇔ Q₀ ≡ R_j (mod p)`
  with `R_j = −C_j a^{−j}`; `Oda.roots_succ` is the recurrence `R_{j+1} = R_j − c_j bʲ a^{−j−1}`.
* `Oda.affine_iterate` — **Lemma 18**, affine form `q_ℓ = (ab⁻¹)^ℓ q + β_ℓ`.
* `Oda.prime_eq_seed` — **Lemma 66(a)**: a prime `P ≤ b^N` with carry word `c` is the seed `s(c)`.
* `Oda.translation_iff` — **Lemma 72**: when all words of a set act mod `p` as one nonzero
  translation.

## References

* [Oda26] Y. Odagiri, *Finite graph certificates for composite terms in rational floor sequences*,
  Zenodo, doi:10.5281/zenodo.22997709 (2026).
-/

namespace Oda

variable {a b : ℕ}

/-- `C₀ = 0`, `C_{j+1} = a·C_j + bʲ·c_j` (the accumulated carry of [Oda26] (8)). -/
def Ccum (a b : ℕ) (c : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | j + 1 => a * Ccum a b c j + (b : ℤ) ^ j * c j

/-- **[Oda26] (8).**  `bʲ·Q_j = aʲ·Q₀ + C_j`. -/
@[category API, AMS 11, ref "Oda26", group "oda26_words"]
theorem pow_mul_eq {Q c : ℕ → ℤ} (hQ : ∀ n, (b : ℤ) * Q (n + 1) = a * Q n + c n) (j : ℕ) :
    (b : ℤ) ^ j * Q j = (a : ℤ) ^ j * Q 0 + Ccum a b c j := by
  induction j with
  | zero => simp [Ccum]
  | succ j ih =>
    calc (b : ℤ) ^ (j + 1) * Q (j + 1) = (b : ℤ) ^ j * ((b : ℤ) * Q (j + 1)) := by ring
      _ = (b : ℤ) ^ j * (a * Q j + c j) := by rw [hQ]
      _ = a * ((b : ℤ) ^ j * Q j) + (b : ℤ) ^ j * c j := by ring
      _ = (a : ℤ) ^ (j + 1) * Q 0 + Ccum a b c (j + 1) := by rw [ih, Ccum]; ring

/-- **[Oda26] Lemma 64(i).**  Two integer sequences with the same carry word of length `ℓ` agree at
`0` modulo `b^ℓ` (so at most one initial integer in any interval of length `b^ℓ` has the word). -/
@[category research solved, AMS 11, ref "Oda26", group "oda26_words"]
theorem modEq_of_same_word (hcop : Nat.Coprime a b) {Q Q' c : ℕ → ℤ}
    (hQ : ∀ n, (b : ℤ) * Q (n + 1) = a * Q n + c n)
    (hQ' : ∀ n, (b : ℤ) * Q' (n + 1) = a * Q' n + c n) (ℓ : ℕ) :
    Q 0 ≡ Q' 0 [ZMOD (b : ℤ) ^ ℓ] := by
  have h1 := pow_mul_eq hQ ℓ
  have h2 := pow_mul_eq hQ' ℓ
  have hdiv : (b : ℤ) ^ ℓ ∣ (a : ℤ) ^ ℓ * (Q' 0 - Q 0) :=
    ⟨Q' ℓ - Q ℓ, by linear_combination h1 - h2⟩
  have hc : IsCoprime ((b : ℤ) ^ ℓ) ((a : ℤ) ^ ℓ) :=
    (Nat.isCoprime_iff_coprime.2 hcop.symm).pow
  exact (Int.modEq_iff_dvd.2 (hc.dvd_of_dvd_mul_left hdiv))

/-- **[Oda26] Lemma 64(ii)**, the exact map: along a real orbit, `θ_j = (aʲθ₀ − C_j)/bʲ`. -/
@[category research solved, AMS 11, ref "Oda26", group "oda26_words"]
theorem theta_eq {ξ : ℝ} (hb : 0 < b) (j : ℕ) :
    (b : ℝ) ^ j * θf a b ξ 0 j = (a : ℝ) ^ j * θf a b ξ 0 0 - Ccum a b (cf a b ξ 0) j := by
  induction j with
  | zero => simp [Ccum]
  | succ j ih =>
    have e := cf_eq (a := a) (ξ := ξ) (ν := 0) hb j
    simp only [mul_zero, sub_zero] at e
    calc (b : ℝ) ^ (j + 1) * θf a b ξ 0 (j + 1) = (b : ℝ) ^ j * ((b : ℝ) * θf a b ξ 0 (j + 1)) := by
          ring
      _ = (b : ℝ) ^ j * ((a : ℝ) * θf a b ξ 0 j - cf a b ξ 0 j) := by rw [e]; ring
      _ = a * ((b : ℝ) ^ j * θf a b ξ 0 j) - (b : ℝ) ^ j * cf a b ξ 0 j := by ring
      _ = (a : ℝ) ^ (j + 1) * θf a b ξ 0 0 - Ccum a b (cf a b ξ 0) (j + 1) := by
          rw [ih, Ccum]; push_cast; ring

/-- **[Oda26] Lemma 64(ii)**, necessity: `θ₀ ∈ [C_j/aʲ, (C_j + bʲ)/aʲ)` for every `j`. -/
@[category research solved, AMS 11, ref "Oda26", group "oda26_words"]
theorem theta0_mem {ξ : ℝ} (hb : 0 < b) (ha : 0 < a) (j : ℕ) :
    (Ccum a b (cf a b ξ 0) j : ℝ) / (a : ℝ) ^ j ≤ θf a b ξ 0 0 ∧
      θf a b ξ 0 0 < ((Ccum a b (cf a b ξ 0) j : ℝ) + (b : ℝ) ^ j) / (a : ℝ) ^ j := by
  have e := theta_eq (a := a) (ξ := ξ) hb j
  have h0 := Z32.yFract_nonneg (p := a) (q := b) (ξ := ξ) (ν := 0) j
  have h1 := Z32.yFract_lt_one (p := a) (q := b) (ξ := ξ) (ν := 0) j
  have hpa : (0 : ℝ) < (a : ℝ) ^ j := pow_pos (by exact_mod_cast ha) _
  have hpb : (0 : ℝ) < (b : ℝ) ^ j := pow_pos (by exact_mod_cast hb) _
  simp only [θf] at e ⊢
  constructor
  · rw [div_le_iff₀ hpa]; nlinarith [mul_nonneg hpb.le h0]
  · rw [lt_div_iff₀ hpa]; nlinarith [mul_lt_mul_of_pos_left h1 hpb]

/-- The roots `R_j = −C_j·a^{−j}` in `ZMod p`. -/
def roots (a b p : ℕ) (c : ℕ → ℤ) (j : ℕ) : ZMod p := -(Ccum a b c j : ZMod p) * ((a : ZMod p)⁻¹) ^ j

/-- **[Oda26] Lemma 18 / 64(iii)**, the recurrence `R₀ = 0`, `R_{j+1} = R_j − c_j bʲ a^{−j−1}`. -/
@[category research solved, AMS 11, ref "Oda26", group "oda26_words"]
theorem roots_succ {p : ℕ} [Fact p.Prime] (ha : (a : ZMod p) ≠ 0) (c : ℕ → ℤ) (j : ℕ) :
    roots a b p c (j + 1) = roots a b p c j - (c j : ZMod p) * (b : ZMod p) ^ j * ((a : ZMod p)⁻¹) ^ (j + 1) := by
  simp only [roots, Ccum]
  push_cast
  have : (a : ZMod p) * (a : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ ha
  rw [pow_succ]
  linear_combination (-(Ccum a b c j : ZMod p) * ((a : ZMod p)⁻¹) ^ j) * this

/-- **[Oda26] Lemma 64(iii) / Lemma 18 (fixed divisors).**  For a prime `p ∤ ab`,
`p ∣ Q_j ⇔ Q₀ ≡ R_j (mod p)`. -/
@[category research solved, AMS 11, ref "Oda26", group "oda26_words"]
theorem dvd_iff_root {p : ℕ} [hp : Fact p.Prime] (ha : (a : ZMod p) ≠ 0) (hb : (b : ZMod p) ≠ 0)
    {Q c : ℕ → ℤ} (hQ : ∀ n, (b : ℤ) * Q (n + 1) = a * Q n + c n) (j : ℕ) :
    (p : ℤ) ∣ Q j ↔ (Q 0 : ZMod p) = roots a b p c j := by
  have h := congrArg (Int.cast : ℤ → ZMod p) (pow_mul_eq hQ j)
  push_cast at h
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hai : (a : ZMod p) ^ j * ((a : ZMod p)⁻¹) ^ j = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ ha, one_pow]
  constructor
  · intro h0
    rw [h0, mul_zero] at h
    simp only [roots]
    linear_combination (-(((a : ZMod p)⁻¹) ^ j)) * h - (Q 0 : ZMod p) * hai
  · intro h0
    have : (b : ZMod p) ^ j * (Q j : ZMod p) = 0 := by
      rw [h, h0]; simp only [roots]
      linear_combination (-(Ccum a b c j : ZMod p)) * hai
    exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ hb)

/-- **[Oda26] Lemma 18**, affine form: `q_ℓ = (a b⁻¹)^ℓ q₀ + β_ℓ`, `β₀ = 0`,
`β_{i+1} = a b⁻¹ β_i + b⁻¹ c_i`, for the forward iteration `q_{i+1} = b⁻¹(a q_i + c_i)`. -/
@[category research solved, AMS 11, ref "Oda26", group "oda26_words"]
theorem affine_iterate {p : ℕ} (c : ℕ → ℤ) (q : ℕ → ZMod p)
    (hq : ∀ i, q (i + 1) = (b : ZMod p)⁻¹ * ((a : ZMod p) * q i + c i)) (ℓ : ℕ) :
    q ℓ = ((a : ZMod p) * (b : ZMod p)⁻¹) ^ ℓ * q 0 +
      Nat.rec (0 : ZMod p) (fun i β => (a : ZMod p) * (b : ZMod p)⁻¹ * β + (b : ZMod p)⁻¹ * c i) ℓ := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih => rw [hq, ih]; simp only; ring

/-- **[Oda26] Lemma 66(a) (seed).**  An initial value in `(0, b^N]` is determined by the carry word
of length `N`: it is the seed `s(c)`, the representative in `(0, b^N]` of the residue fixed by
Lemma 64(i).  In particular any two primes `≤ b^N` with the same word coincide (primality is not
needed for the uniqueness). -/
@[category research solved, AMS 11, ref "Oda26", group "oda26_words"]
theorem prime_eq_seed (hcop : Nat.Coprime a b) {N : ℕ}
    {Q Q' c : ℕ → ℤ} (hQ : ∀ n, (b : ℤ) * Q (n + 1) = a * Q n + c n)
    (hQ' : ∀ n, (b : ℤ) * Q' (n + 1) = a * Q' n + c n)
    (h0 : 0 < Q 0) (h0' : 0 < Q' 0) (hle : Q 0 ≤ (b : ℤ) ^ N) (hle' : Q' 0 ≤ (b : ℤ) ^ N) :
    Q 0 = Q' 0 := by
  have hm := modEq_of_same_word hcop hQ hQ' N
  rcases (Int.ModEq.dvd hm) with ⟨k, hk⟩
  have hpos : (0 : ℤ) < (b : ℤ) ^ N := by linarith
  rcases lt_trichotomy k 0 with h | h | h
  · have : k ≤ -1 := by omega
    nlinarith
  · subst h; linarith
  · have : 1 ≤ k := by omega
    nlinarith

/-- **[Oda26] Lemma 72 (primes producing a common nonzero translation)**, single-word core: modulo
a prime `p ∤ ab`, the residue map of a word of length `ℓ`, `q ↦ (a^ℓ q + C)/b^ℓ`, is the
translation `q ↦ q + τ` iff `a^ℓ ≡ b^ℓ` and then `τ = C/b^ℓ`; it is nonzero iff `p ∤ C`. -/
@[category research solved, AMS 11, ref "Oda26", group "oda26_words"]
theorem translation_iff {p : ℕ} [Fact p.Prime] (hb : (b : ZMod p) ≠ 0) (ℓ : ℕ) (C : ZMod p)
    (τ : ZMod p) :
    (∀ q : ZMod p, ((a : ZMod p) ^ ℓ * q + C) * ((b : ZMod p) ^ ℓ)⁻¹ = q + τ) ↔
      ((a : ZMod p) ^ ℓ = (b : ZMod p) ^ ℓ ∧ τ = C * ((b : ZMod p) ^ ℓ)⁻¹) := by
  have hbl : (b : ZMod p) ^ ℓ ≠ 0 := pow_ne_zero _ hb
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    simp only [mul_zero, zero_add] at h0
    refine ⟨?_, h0.symm⟩
    rw [h0.symm] at h1
    have : ((a : ZMod p) ^ ℓ + C) * ((b : ZMod p) ^ ℓ)⁻¹ * (b : ZMod p) ^ ℓ
        = (1 + C * ((b : ZMod p) ^ ℓ)⁻¹) * (b : ZMod p) ^ ℓ := by rw [mul_one] at h1; rw [h1]
    rw [inv_mul_cancel_right₀ hbl, add_mul, one_mul, inv_mul_cancel_right₀ hbl] at this
    linear_combination this
  · rintro ⟨h1, h2⟩ q
    rw [h1, h2, add_mul, mul_comm ((b : ZMod p) ^ ℓ) q, mul_inv_cancel_right₀ hbl]

end Oda
