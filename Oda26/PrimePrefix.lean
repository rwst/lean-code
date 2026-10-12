/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Oda26.OrbitBasics

/-!
# Long prime prefixes ([Oda26] App. E.1, Lemma 67)

A prime arithmetic progression `P, P + D, …, P + (L−1)D` that is *narrow* (`P > 48L²D²`) is the
prefix of a floor orbit: with `b ≡ 1 (mod 6)` within `3` of `2P/D`, `a = b + 2` and `ξ = P + ½`,
`⌊ξ(a/b)ʲ⌋ = P + jD` for `j < L`.

* `Oda.pow_le_quad` — `(1+u)ʲ ≤ 1 + ju + (ju)²` for `ju ≤ 1`.
* `Oda.transplant` — **[Oda26] Lemma 67 (transplanting a prime progression)**.

## References

* [Oda26] Y. Odagiri, *Finite graph certificates for composite terms in rational floor sequences*,
  Zenodo, doi:10.5281/zenodo.22997709 (2026).
-/

namespace Oda

/-- `(1+u)ʲ ≤ 1 + ju + (ju)²` when `0 ≤ u` and `ju ≤ 1`. -/
theorem pow_le_quad {u : ℝ} (hu : 0 ≤ u) :
    ∀ j : ℕ, (j : ℝ) * u ≤ 1 → (1 + u) ^ j ≤ 1 + j * u + (j * u) ^ 2 := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    push_cast at hj ⊢
    have hj' : (j : ℝ) * u ≤ 1 := by nlinarith
    have h1 := ih hj'
    have hj0 : (0 : ℝ) ≤ j := by positivity
    have hpos : (0 : ℝ) ≤ 1 + u := by linarith
    calc (1 + u) ^ (j + 1) = (1 + u) ^ j * (1 + u) := pow_succ _ _
      _ ≤ (1 + j * u + (j * u) ^ 2) * (1 + u) := mul_le_mul_of_nonneg_right h1 hpos
      _ ≤ 1 + (j + 1) * u + ((j + 1) * u) ^ 2 := by
        have : (j : ℝ) * u * (j * u * u) ≤ 1 * (j * u * u) :=
          mul_le_mul_of_nonneg_right hj' (by positivity)
        nlinarith [mul_nonneg hj0 hu, mul_nonneg (mul_nonneg hj0 hu) hu]

theorem six_le {P D : ℕ} (hD : 0 < D) (a0 : P % 2 = 1) (a1 : (P + D) % 2 = 1)
    (b0 : P % 3 ≠ 0) (b1 : (P + D) % 3 ≠ 0) (b2 : (P + 2 * D) % 3 ≠ 0) : 6 ≤ D := by
  have e1 := Nat.add_mod P D 3
  have e2 := Nat.add_mod P (2 * D) 3
  have e3 := Nat.mul_mod 2 D 3
  have e4 := Nat.add_mod P D 2
  have hp3 := Nat.mod_lt P (show 0 < 3 by decide)
  have hd3 := Nat.mod_lt D (show 0 < 3 by decide)
  have h3 : D % 3 = 0 := by
    rcases (show P % 3 = 1 ∨ P % 3 = 2 by omega) with h | h <;>
    rcases (show D % 3 = 0 ∨ D % 3 = 1 ∨ D % 3 = 2 by omega) with h' | h' | h' <;>
    simp_all
  have h2 : D % 2 = 0 := by
    rcases (show D % 2 = 0 ∨ D % 2 = 1 by omega) with h' | h' <;> simp_all
  omega

/-- **[Oda26] Lemma 67 (transplanting a prime progression).**  Let `L ≥ 3`, `D ≥ 1`, let
`P, P + D, …, P + (L−1)D` be primes `> 3` with `P > 48L²D²`, and let `b ≡ 1 (mod 6)` with
`|b − 2P/D| ≤ 3`.  Then `t = (b−1)/6 ≥ 1`, `P > a = b + 2`, and `⌊(P + ½)(a/b)ʲ⌋ = P + jD` for
`j < L`. -/
@[category research solved, AMS 11, ref "Oda26", group "oda26_prime_prefix"]
theorem transplant {L P D : ℕ} (hL : 3 ≤ L) (hD : 0 < D) (hpr : ∀ j < L, (P + j * D).Prime)
    (h3 : 3 < P) (hP : 48 * L ^ 2 * D ^ 2 < P) {b : ℕ} (hb6 : b % 6 = 1)
    (hbc : |(b : ℝ) - 2 * P / D| ≤ 3) :
    1 ≤ (b - 1) / 6 ∧ b + 2 < P ∧
      ∀ j < L, Qf (b + 2) b ((P : ℝ) + 1 / 2) 0 j = P + j * D := by
  -- `6 ∣ D`
  have hp0 := hpr 0 (by omega)
  have hp1 := hpr 1 (by omega)
  have hp2 := hpr 2 (by omega)
  simp only [zero_mul, add_zero, one_mul] at hp0 hp1 hp2
  have hodd : ∀ q : ℕ, q.Prime → 3 < q → q % 2 = 1 := fun q hq hq3 => by
    rcases hq.eq_two_or_odd with h | h <;> omega
  have hnot3 : ∀ q : ℕ, q.Prime → 3 < q → q % 3 ≠ 0 := fun q hq hq3 h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 (Nat.dvd_of_mod_eq_zero h)
    omega
  have hD6 : 6 ≤ D := by
    have a0 := hodd P hp0 h3
    have a1 := hodd (P + D) hp1 (by omega)
    have b0 := hnot3 P hp0 h3
    have b1 := hnot3 (P + D) hp1 (by omega)
    have b2 := hnot3 (P + 2 * D) hp2 (by omega)
    exact six_le hD a0 a1 b0 b1 b2
  -- real estimates
  have hp : (48 : ℝ) * L ^ 2 * D ^ 2 < P := by exact_mod_cast hP
  have hLr : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hDr : (6 : ℝ) ≤ D := by exact_mod_cast hD6
  have hDpos : (0 : ℝ) < D := by linarith
  have hPpos : (0 : ℝ) < P := by nlinarith
  have hbc' := abs_le.1 hbc
  -- `p/d ≥ 48L²d ≥ 3`, `b ≥ p/d`
  have hPD : (48 : ℝ) * L ^ 2 * D ≤ (P : ℝ) / D := by
    rw [le_div_iff₀ hDpos]; nlinarith
  have hL2 : (9 : ℝ) ≤ L ^ 2 := by nlinarith
  have hPD3 : (3 : ℝ) ≤ (P : ℝ) / D := by nlinarith
  have h2PD : 2 * (P : ℝ) / D = 2 * ((P : ℝ) / D) := by ring
  have hbge : (P : ℝ) / D ≤ b := by linarith
  have hbpos : (0 : ℝ) < b := by linarith
  refine ⟨?_, ?_, fun j hj => ?_⟩
  · have : (7 : ℝ) ≤ b := by nlinarith
    have : 7 ≤ b := by exact_mod_cast this
    omega
  · have hPD6 : (P : ℝ) / D ≤ P / 6 := div_le_div_of_nonneg_left hPpos.le (by norm_num) hDr
    have : (b : ℝ) + 2 < P := by nlinarith
    exact_mod_cast this
  -- the main estimate
  have hjL : (j : ℝ) + 1 ≤ L := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := by positivity
  set u : ℝ := 2 / b with hu
  have hu0 : 0 ≤ u := by positivity
  have hr : ((b + 2 : ℕ) : ℝ) / b = 1 + u := by
    rw [hu]; push_cast; field_simp
  -- `1/b ≤ d/p`
  have hinvb : 1 / (b : ℝ) ≤ D / P := by
    rw [div_le_div_iff₀ hbpos hPpos, one_mul]
    have := hbge; rw [div_le_iff₀ hDpos] at this; linarith
  have hju : (j : ℝ) * u ≤ 2 * L * D / P := by
    rw [hu, show (j : ℝ) * (2 / b) = 2 * j * (1 / b) by ring]
    have : (2 : ℝ) * j ≤ 2 * L := by linarith
    calc 2 * (j : ℝ) * (1 / b) ≤ 2 * L * (D / P) :=
          mul_le_mul this hinvb (by positivity) (by positivity)
      _ = 2 * L * D / P := by ring
  have hLDP : (2 : ℝ) * L * D / P ≤ 1 := by
    rw [div_le_one hPpos]
    have h1 : (1 : ℝ) ≤ L * D := by nlinarith
    have h2 : (L : ℝ) * D ≤ (L * D) ^ 2 := by nlinarith
    nlinarith
  have hq := pow_le_quad hu0 j (le_trans hju hLDP)
  have hb' := one_add_mul_le_pow (show (-2 : ℝ) ≤ u by linarith) j
  set R := (1 + u) ^ j - 1 - j * u with hR
  have hR0 : 0 ≤ R := by rw [hR]; linarith
  have hR1 : R ≤ (j * u) ^ 2 := by rw [hR]; linarith
  -- `|(2P+1)/b − D| ≤ 4D²/P`
  have hdev : |(2 * (P : ℝ) + 1) / b - D| ≤ 4 * D ^ 2 / P := by
    have e : (2 * (P : ℝ) + 1) / b - D = (2 * P + 1 - D * b) / b := by field_simp
    have h1 : |2 * (P : ℝ) + 1 - D * b| ≤ 4 * D := by
      have e2 : 2 * (P : ℝ) + 1 - D * b = 1 + D * (2 * P / D - b) := by field_simp; ring
      rw [e2]
      have : |(D : ℝ) * (2 * P / D - b)| ≤ D * 3 := by
        rw [abs_mul, abs_of_pos hDpos]
        exact mul_le_mul_of_nonneg_left (by rw [abs_sub_comm]; exact hbc) hDpos.le
      calc |1 + (D : ℝ) * (2 * P / D - b)| ≤ |(1 : ℝ)| + |(D : ℝ) * (2 * P / D - b)| :=
            abs_add_le _ _
        _ ≤ 1 + D * 3 := by rw [abs_one]; linarith
        _ ≤ 4 * D := by linarith
    rw [e, abs_div, abs_of_pos hbpos]
    calc |2 * (P : ℝ) + 1 - D * b| / b = |2 * (P : ℝ) + 1 - D * b| * (1 / b) := by ring
      _ ≤ (4 * D) * (D / P) := mul_le_mul h1 hinvb (by positivity) (by positivity)
      _ = 4 * D ^ 2 / P := by ring
  -- `(P+½)R ≤ 8j²D²/P`
  have hRb : ((P : ℝ) + 1 / 2) * R ≤ 8 * j ^ 2 * D ^ 2 / P := by
    have h1 : (j * u) ^ 2 ≤ (2 * j * D / P) ^ 2 := by
      have : (j : ℝ) * u ≤ 2 * j * D / P := by
        rw [hu, show (j : ℝ) * (2 / b) = 2 * j * (1 / b) by ring,
          show 2 * (j : ℝ) * D / P = 2 * j * (D / P) by ring]
        exact mul_le_mul_of_nonneg_left hinvb (by positivity)
      exact pow_le_pow_left₀ (by positivity) this 2
    have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast (show 1 ≤ P by omega)
    have h2 : ((P : ℝ) + 1 / 2) ≤ 2 * P := by linarith
    calc ((P : ℝ) + 1 / 2) * R ≤ (2 * P) * (2 * j * D / P) ^ 2 :=
          mul_le_mul h2 (le_trans hR1 h1) hR0 (by positivity)
      _ = 8 * j ^ 2 * D ^ 2 / P := by field_simp; ring
  -- assemble
  have hx : ((P : ℝ) + 1 / 2) * (1 + u) ^ j - (P + j * D + 1 / 2) =
      j * ((2 * P + 1) / b - D) + ((P : ℝ) + 1 / 2) * R := by
    have e1 : (1 + u) ^ j = 1 + j * u + R := by rw [hR]; ring
    rw [e1, hu]; ring
  have hjd := abs_le.1 hdev
  have hsmall : (j : ℝ) * (4 * D ^ 2 / P) + 8 * j ^ 2 * D ^ 2 / P < 1 / 4 := by
    have : (j : ℝ) * (4 * D ^ 2 / P) + 8 * j ^ 2 * D ^ 2 / P = (4 * j + 8 * j ^ 2) * D ^ 2 / P := by
      ring
    rw [this, div_lt_iff₀ hPpos]
    have hjL' : (j : ℝ) ≤ L := by linarith
    have hj2 : (j : ℝ) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hj0 hjL' 2
    have hLL : (L : ℝ) ≤ L ^ 2 := by
      rw [sq]; exact le_mul_of_one_le_left (by linarith) (by linarith)
    have : (4 * (j : ℝ) + 8 * j ^ 2) ≤ 12 * L ^ 2 := by linarith only [hjL', hj2, hLL]
    linarith only [mul_le_mul_of_nonneg_right this (by positivity : (0 : ℝ) ≤ D ^ 2), hp]
  have hup : j * ((2 * (P : ℝ) + 1) / b - D) ≤ j * (4 * D ^ 2 / P) :=
    mul_le_mul_of_nonneg_left hjd.2 hj0
  have hlo : -(j * (4 * D ^ 2 / P)) ≤ j * ((2 * (P : ℝ) + 1) / b - D) := by
    have := mul_le_mul_of_nonneg_left hjd.1 hj0; linarith
  have hRnn : 0 ≤ ((P : ℝ) + 1 / 2) * R := by positivity
  simp only [Qf, Z32.xInt, Z32.orb, add_zero]
  rw [hr, Int.floor_eq_iff]
  push_cast
  constructor <;> linarith only [hx, hup, hlo, hRnn, hRb, hsmall]

end Oda
