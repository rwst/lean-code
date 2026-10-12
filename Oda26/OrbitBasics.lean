/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Oda26.Recurrence
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.GCD

/-!
# Orbit arithmetic of `⌊ξ(a/b)ⁿ⌋` ([Oda26] Lemmas 25, 26, 29, 41)

Elementary facts about the floor orbit `Qₙ = ⌊ξ(a/b)ⁿ⌋`, fractional parts `θₙ`, and carries
`cₙ = b·Q_{n+1} − a·Qₙ = a·θₙ − b·θ_{n+1}`, used throughout [Oda26].  Everything is stated for the
shifted orbit `⌊ξ(a/b)ⁿ + ν⌋` (then `cₙ = aθₙ − bθ_{n+1} − (a−b)ν`, `Oda.cf_eq`, with bounds
`Oda.cf_bounds`), except the alphabet `C(a,b)`, whose interval is the `ν = 0` one:

* `Oda.pow_dvd_of_carry_period` — **Lemma 25** (finite nonperiodicity): if the carry word has period
  `d` on a window of length `ℓ`, then `b^{ℓ−d} ∣ Q_{u+d} − Q_u`.  ([DN05] Lemma 2 is its limit.)
* `Oda.Qf_succ_gt` — **Lemma 26**: `xₙ ≥ b/(a−b)` forces `Q_{n+1} ≥ Qₙ + 1`.
* `Oda.carry_mem_alphabet` — **Lemma 29**, orbit form: if `Qₙ Q_{n+1}` is prime to `2ab`, the carry
  lies in `C(a,b) = {c : 1−b ≤ c ≤ a−1, c ≡ b−a (mod 2), gcd(c,ab) = 1}`.
* `Oda.window_realized` — **Lemma 41**: every finite window of residues mod `M`, fractional parts and
  carries satisfying the two local identities is realized by a true orbit with `ξ` as large as
  desired.  This is the bridge from *pseudo-orbits* (the obstruction witnesses of [Oda26] §8) to true
  orbits on every finite window.

## References

* [Oda26] Y. Odagiri, *Finite graph certificates for composite terms in rational floor sequences*,
  Zenodo, doi:10.5281/zenodo.22997709 (2026).
-/

namespace Oda

open Filter

variable {a b : ℕ} {ξ ν : ℝ}

/-- `θₙ = {ξ(a/b)ⁿ + ν}`. -/
noncomputable abbrev θf (a b : ℕ) (ξ ν : ℝ) (n : ℕ) : ℝ := Z32.yFract a b ξ ν n

@[category API, AMS 11, ref "Oda26", group "oda26_orbit"]
theorem cf_eq (hb : 0 < b) (n : ℕ) :
    (cf a b ξ ν n : ℝ) = a * θf a b ξ ν n - b * θf a b ξ ν (n + 1) - ((a : ℝ) - b) * ν :=
  Z32.carry_eq (p := a) (q := b) (ξ := ξ) (ν := ν) hb n

/-- The carry bounds behind [Oda26] Lemma 29, shifted: `−b − (a−b)ν < cₙ < a − (a−b)ν`. -/
@[category API, AMS 11, ref "Oda26", group "oda26_orbit"]
theorem cf_bounds (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    -(b : ℝ) - ((a : ℝ) - b) * ν < cf a b ξ ν n ∧ (cf a b ξ ν n : ℝ) < a - ((a : ℝ) - b) * ν := by
  have he := cf_eq (a := a) (ξ := ξ) (ν := ν) hb n
  have h0 := Z32.yFract_nonneg (p := a) (q := b) (ξ := ξ) (ν := ν) n
  have h1 := Z32.yFract_lt_one (p := a) (q := b) (ξ := ξ) (ν := ν) n
  have h2 := Z32.yFract_nonneg (p := a) (q := b) (ξ := ξ) (ν := ν) (n + 1)
  have h3 := Z32.yFract_lt_one (p := a) (q := b) (ξ := ξ) (ν := ν) (n + 1)
  simp only [θf] at he
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  constructor
  · rw [he]; nlinarith [mul_nonneg haR.le h0, mul_lt_mul_of_pos_left h3 hbR]
  · rw [he]; nlinarith [mul_nonneg hbR.le h2, mul_lt_mul_of_pos_left h1 haR]

/-! ## Lemma 25 -/

/-- **[Oda26] Lemma 25 (finite nonperiodicity).**  If `c_{u+i+d} = c_{u+i}` for `i < ℓ − d`, then
`b^{ℓ−d}` divides `D₀ = Q_{u+d} − Q_u`. -/
@[category research solved, AMS 11, ref "Oda26", group "oda26_orbit"]
theorem pow_dvd_of_carry_period (hcop : Nat.Coprime a b) {u d ℓ : ℕ} (hdl : d ≤ ℓ)
    (hper : ∀ i, i < ℓ - d → cf a b ξ ν (u + i + d) = cf a b ξ ν (u + i)) :
    (b : ℤ) ^ (ℓ - d) ∣ Qf a b ξ ν (u + d) - Qf a b ξ ν u := by
  set D : ℕ → ℤ := fun i => Qf a b ξ ν (u + i + d) - Qf a b ξ ν (u + i)
  have hstep : ∀ i, i < ℓ - d → (b : ℤ) * D (i + 1) = a * D i := by
    intro i hi
    simp only [D]
    have h1 := b_mul_Qf_succ (a := a) (b := b) (ξ := ξ) (ν := ν) (u + i + d)
    have h2 := b_mul_Qf_succ (a := a) (b := b) (ξ := ξ) (ν := ν) (u + i)
    rw [show u + (i + 1) + d = u + i + d + 1 by ring, show u + (i + 1) = u + i + 1 by ring]
    rw [mul_sub, h1, h2, hper i hi]; ring
  have hpow : ∀ k, k ≤ ℓ - d → (b : ℤ) ^ k * D k = (a : ℤ) ^ k * D 0 := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      calc (b : ℤ) ^ (k + 1) * D (k + 1) = (b : ℤ) ^ k * ((b : ℤ) * D (k + 1)) := by ring
        _ = (b : ℤ) ^ k * (a * D k) := by rw [hstep k (by omega)]
        _ = a * ((b : ℤ) ^ k * D k) := by ring
        _ = a * ((a : ℤ) ^ k * D 0) := by rw [ih (by omega)]
        _ = (a : ℤ) ^ (k + 1) * D 0 := by ring
  have hD0 : D 0 = Qf a b ξ ν (u + d) - Qf a b ξ ν u := by simp [D]
  rw [← hD0]
  have hc : IsCoprime ((b : ℤ) ^ (ℓ - d)) ((a : ℤ) ^ (ℓ - d)) :=
    (Nat.isCoprime_iff_coprime.2 hcop.symm).pow
  exact hc.dvd_of_dvd_mul_left ⟨D (ℓ - d), (hpow (ℓ - d) le_rfl).symm.trans (by ring)⟩

/-! ## Lemma 26 -/

/-- **[Oda26] Lemma 26.**  If `xₙ ≥ b/(a−b)` then `Q_{n+1} ≥ Qₙ + 1`. -/
@[category research solved, AMS 11, ref "Oda26", group "oda26_orbit"]
theorem Qf_succ_gt (hb : 0 < b) (hab : b < a) {n : ℕ}
    (hx : (b : ℝ) / (a - b) ≤ ξ * ((a : ℝ) / b) ^ n) : Qf a b ξ ν n + 1 ≤ Qf a b ξ ν (n + 1) := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hab' : (0 : ℝ) < a - b := by have : (b : ℝ) < a := by exact_mod_cast hab
                                    linarith
  set x := ξ * ((a : ℝ) / b) ^ n
  have h1 : 1 ≤ x * ((a : ℝ) - b) / b := by
    rw [le_div_iff₀ hb']; rw [div_le_iff₀ hab'] at hx; linarith
  have h2 : ξ * ((a : ℝ) / b) ^ (n + 1) = x + x * ((a : ℝ) - b) / b := by
    simp only [x, pow_succ]; field_simp; ring
  simp only [Qf, Z32.xInt, Z32.orb]
  rw [h2]
  have : ⌊x + ν⌋ + 1 = ⌊x + ν + 1⌋ := (Int.floor_add_one _).symm
  rw [this]
  exact Int.floor_le_floor (by linarith)

/-! ## Lemma 29 -/

/-- The general carry alphabet `C(a,b)`, for the shift `ν`: `−b < c + (a−b)ν < a`,
`c ≡ b − a (mod 2)`, `gcd(c, ab) = 1`.  At `ν = 0` the bounds are `1 − b ≤ c ≤ a − 1`
(`carryAlphabet_zero`), the alphabet of [Oda26]. -/
def carryAlphabet (a b : ℕ) (ν : ℝ) (c : ℤ) : Prop :=
  -(b : ℝ) < c + ((a : ℝ) - b) * ν ∧ (c : ℝ) + ((a : ℝ) - b) * ν < a ∧
    c % 2 = ((b : ℤ) - a) % 2 ∧ Int.gcd c (a * b) = 1

/-- The unshifted alphabet in integer form. -/
theorem carryAlphabet_zero {c : ℤ} : carryAlphabet a b 0 c ↔
    1 - (b : ℤ) ≤ c ∧ c ≤ (a : ℤ) - 1 ∧ c % 2 = ((b : ℤ) - a) % 2 ∧ Int.gcd c (a * b) = 1 := by
  simp only [carryAlphabet, mul_zero, add_zero]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have h1' : -(b : ℤ) < c := by exact_mod_cast h1
    have h2' : c < (a : ℤ) := by exact_mod_cast h2
    exact ⟨by omega, by omega, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, h3, h4⟩
    · have : -(b : ℤ) < c := by omega
      exact_mod_cast this
    · have : c < (a : ℤ) := by omega
      exact_mod_cast this

/-- **[Oda26] Lemma 29, arithmetic half (any shift).**  If `Qₙ Q_{n+1}` is prime to `2ab`, then
`cₙ ≡ b − a (mod 2)` and `cₙ` is prime to `ab`. -/
@[category research solved, AMS 11, ref "Oda26", group "oda26_orbit"]
theorem cf_parity_gcd (hcop : Nat.Coprime a b) {n : ℕ}
    (hQ : Int.gcd (Qf a b ξ ν n * Qf a b ξ ν (n + 1)) (2 * a * b) = 1) :
    cf a b ξ ν n % 2 = ((b : ℤ) - a) % 2 ∧ Int.gcd (cf a b ξ ν n) (a * b) = 1 := by
  have hrec := b_mul_Qf_succ (a := a) (b := b) (ξ := ξ) (ν := ν) n
  have hQQ : IsCoprime (Qf a b ξ ν n * Qf a b ξ ν (n + 1)) (2 * (a : ℤ) * b) :=
    Int.isCoprime_iff_gcd_eq_one.2 hQ
  have hQn : IsCoprime (Qf a b ξ ν n) (2 * (a : ℤ) * b) := hQQ.of_mul_left_left
  have hQn1 : IsCoprime (Qf a b ξ ν (n + 1)) (2 * (a : ℤ) * b) := hQQ.of_mul_left_right
  have odd_of : ∀ x : ℤ, IsCoprime x (2 * (a : ℤ) * b) → x % 2 = 1 := by
    intro x hx
    by_contra h
    have hx2 : (2 : ℤ) ∣ x := by omega
    have := hx.isUnit_of_dvd' hx2 ⟨a * b, by ring⟩
    rw [Int.isUnit_iff] at this
    omega
  have hcopZ : IsCoprime (a : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.2 hcop
  have hc_eq : cf a b ξ ν n = b * Qf a b ξ ν (n + 1) - a * Qf a b ξ ν n := by linarith
  refine ⟨?_, ?_⟩
  · have o1 := odd_of _ hQn
    have o2 := odd_of _ hQn1
    rw [hc_eq, Int.sub_emod, Int.mul_emod, o2, Int.mul_emod (a : ℤ), o1]
    simp [Int.sub_emod]
  · rw [← Int.isCoprime_iff_gcd_eq_one]
    push_cast
    apply IsCoprime.mul_right
    · have ha1 : IsCoprime (a : ℤ) (Qf a b ξ ν (n + 1)) :=
        (hQn1.of_mul_right_left.of_mul_right_right).symm
      have : IsCoprime (a : ℤ) ((b : ℤ) * Qf a b ξ ν (n + 1)) := hcopZ.mul_right ha1
      have e : cf a b ξ ν n = (b : ℤ) * Qf a b ξ ν (n + 1) + (-(Qf a b ξ ν n)) * a := by
        rw [hc_eq]; ring
      rw [e]; exact (this.add_mul_right_right _).symm
    · have hb1 : IsCoprime (b : ℤ) (Qf a b ξ ν n) := hQn.of_mul_right_right.symm
      have : IsCoprime (b : ℤ) ((a : ℤ) * Qf a b ξ ν n) := hcopZ.symm.mul_right hb1
      have e : cf a b ξ ν n = (-((a : ℤ) * Qf a b ξ ν n)) + Qf a b ξ ν (n + 1) * b := by
        rw [hc_eq]; ring
      rw [e]; exact (this.neg_right.add_mul_right_right _).symm

/-- **[Oda26] Lemma 29, orbit form** (for any shift).  If `Qₙ Q_{n+1}` is prime to `2ab`, then
`cₙ ∈ C(a,b)` (the alphabet of the shift `ν`). -/
@[category research solved, AMS 11, ref "Oda26", group "oda26_orbit"]
theorem carry_mem_alphabet (hb : 0 < b) (hab : b < a) (hcop : Nat.Coprime a b) {n : ℕ}
    (hQ : Int.gcd (Qf a b ξ ν n * Qf a b ξ ν (n + 1)) (2 * a * b) = 1) :
    carryAlphabet a b ν (cf a b ξ ν n) := by
  obtain ⟨hlo, hhi⟩ := cf_bounds (a := a) (ξ := ξ) (ν := ν) (by omega) hb n
  exact ⟨by linarith, by linarith, cf_parity_gcd hcop hQ⟩

/-! ## Lemma 41 -/

/-- **[Oda26] Lemma 41 (finite windows are realized by true orbits).**  Let `q₀, …, q_L` be integers,
`θ₀, …, θ_L ∈ [0,1)` and `c₀, …, c_{L−1}` integers with `aθᵢ − bθᵢ₊₁ − (a−b)ν = cᵢ` and
`b·qᵢ₊₁ ≡ a·qᵢ + cᵢ (mod M)`.  Then for every `T₀` there is `ξ > T₀` whose orbit has
`⌊ξ(a/b)ⁱ + ν⌋ ≡ qᵢ (mod M)` and `{ξ(a/b)ⁱ + ν} = θᵢ` for all `i ≤ L`.  (The paper also assumes
`gcd(qᵢ, M) = 1`; it is not needed.) -/
@[category research solved, AMS 11, ref "Oda26", group "oda26_orbit"]
theorem window_realized (hb : 0 < b) (hcop : Nat.Coprime a b) {M : ℕ} (hM : 0 < M) {L : ℕ}
    {q c : ℕ → ℤ} {θ : ℕ → ℝ} (hθ0 : ∀ i, i ≤ L → 0 ≤ θ i) (hθ1 : ∀ i, i ≤ L → θ i < 1)
    (hcar : ∀ i, i < L → (a : ℝ) * θ i - b * θ (i + 1) - ((a : ℝ) - b) * ν = c i)
    (hcong : ∀ i, i < L → (b : ℤ) * q (i + 1) ≡ a * q i + c i [ZMOD M]) (T₀ : ℝ) :
    ∃ ξ : ℝ, T₀ < ξ ∧ ∀ i, i ≤ L →
      Qf a b ξ ν i ≡ q i [ZMOD M] ∧ θf a b ξ ν i = θ i := by
  -- the integer defects `dᵢ`: `a qᵢ + cᵢ − b qᵢ₊₁ = M dᵢ`
  have hd0 : ∀ i, i < L → ∃ d : ℤ, a * q i + c i - b * q (i + 1) = M * d := fun i hi =>
    (hcong i hi).dvd |>.imp fun d hd => by linarith
  choose! d hd using hd0
  -- `S₀ = 0`, `S_{j+1} = a·S_j + b^j·d_j`
  let S : ℕ → ℤ := fun j => Nat.rec 0 (fun j s => (a : ℤ) * s + (b : ℤ) ^ j * d j) j
  have hS0 : S 0 = 0 := rfl
  have hSs : ∀ j, S (j + 1) = a * S j + (b : ℤ) ^ j * d j := fun j => rfl
  have hSmod : ∀ j k, j ≤ k → S k ≡ (a : ℤ) ^ (k - j) * S j [ZMOD (b : ℤ) ^ j] := by
    intro j k hjk
    induction k, hjk using Nat.le_induction with
    | base => simp
    | succ k hjk ih =>
      rw [hSs, show k + 1 - j = (k - j) + 1 by omega, pow_succ]
      have : (b : ℤ) ^ k * d k ≡ 0 [ZMOD (b : ℤ) ^ j] :=
        (Int.modEq_zero_iff_dvd).2 (Dvd.dvd.mul_right (pow_dvd_pow _ hjk) _)
      calc (a : ℤ) * S k + (b : ℤ) ^ k * d k
          ≡ a * ((a : ℤ) ^ (k - j) * S j) + 0 [ZMOD (b : ℤ) ^ j] := (ih.mul_left _).add this
        _ = (a : ℤ) ^ (k - j) * a * S j := by ring
  obtain ⟨u, v, huv⟩ : IsCoprime ((a : ℤ) ^ L) ((b : ℤ) ^ L) :=
    (Nat.isCoprime_iff_coprime.2 hcop).pow
  -- with `t₀ = −u·S_L + b^L·T`, every `a^j t₀ + S_j` is divisible by `b^j`
  have key : ∀ T : ℤ, ∀ j, j ≤ L →
      (b : ℤ) ^ j ∣ (a : ℤ) ^ j * (-u * S L + (b : ℤ) ^ L * T) + S j := by
    intro T j hj
    have hpow : (a : ℤ) ^ j * (a : ℤ) ^ (L - j) = (a : ℤ) ^ L := by
      rw [← pow_add]; congr 1; omega
    have e : (a : ℤ) ^ j * (-u * S L + (b : ℤ) ^ L * T) + S j
        = (-u * (a : ℤ) ^ j) * (S L - (a : ℤ) ^ (L - j) * S j)
          + S j * v * (b : ℤ) ^ L + (a : ℤ) ^ j * (b : ℤ) ^ L * T := by
      linear_combination (-(S j)) * huv + (-(u * S j)) * hpow
    have hbj : (b : ℤ) ^ j ∣ (b : ℤ) ^ L := pow_dvd_pow _ hj
    rw [e]
    refine dvd_add (dvd_add (Dvd.dvd.mul_left (hSmod j L hj).symm.dvd _)
      (Dvd.dvd.mul_left hbj _)) ((Dvd.dvd.mul_left hbj _).mul_right _)
  let t : ℤ → ℕ → ℤ := fun T j =>
    ((a : ℤ) ^ j * (-u * S L + (b : ℤ) ^ L * T) + S j) / (b : ℤ) ^ j
  have ht : ∀ T j, j ≤ L →
      (b : ℤ) ^ j * t T j = (a : ℤ) ^ j * (-u * S L + (b : ℤ) ^ L * T) + S j :=
    fun T j hj => Int.mul_ediv_cancel' (key T j hj)
  have hbz : (b : ℤ) ≠ 0 := by exact_mod_cast hb.ne'
  have htrec : ∀ T i, i < L → (b : ℤ) * t T (i + 1) = a * t T i + d i := by
    intro T i hi
    have h1 := ht T (i + 1) (by omega)
    have h2 := ht T i (by omega)
    apply mul_left_cancel₀ (pow_ne_zero i hbz)
    calc (b : ℤ) ^ i * ((b : ℤ) * t T (i + 1)) = (b : ℤ) ^ (i + 1) * t T (i + 1) := by ring
      _ = (a : ℤ) ^ (i + 1) * (-u * S L + (b : ℤ) ^ L * T) + S (i + 1) := h1
      _ = (a : ℤ) * ((a : ℤ) ^ i * (-u * S L + (b : ℤ) ^ L * T) + S i) + (b : ℤ) ^ i * d i := by
          rw [hSs]; ring
      _ = (b : ℤ) ^ i * ((a : ℤ) * t T i + d i) := by rw [← h2]; ring
  have ht0 : ∀ T, t T 0 = -u * S L + (b : ℤ) ^ L * T := by
    intro T; have := ht T 0 (Nat.zero_le _); simpa [hS0] using this
  -- choose `T` so that `Q₀ = q₀ + M t₀ > T₀`
  set T : ℤ := |q 0| + M * |u * S L| + ((⌈T₀ + |ν|⌉).toNat : ℤ) + 1 with hTdef
  have hT0 : 0 ≤ T := by positivity
  let Qv : ℕ → ℤ := fun i => q i + M * t T i
  have hQ0 : (⌈T₀ + |ν|⌉).toNat < Qv 0 := by
    simp only [Qv, ht0]
    have hMb : (1 : ℤ) ≤ (M : ℤ) * (b : ℤ) ^ L := by
      have : (1 : ℤ) ≤ (b : ℤ) ^ L := one_le_pow₀ (by exact_mod_cast hb)
      have hM1 : (1 : ℤ) ≤ M := by exact_mod_cast hM
      nlinarith
    have h1 : -|q 0| ≤ q 0 := neg_abs_le _
    have h2 : -|u * S L| ≤ -u * S L := by rw [neg_mul]; exact neg_le_neg (le_abs_self _)
    have hM0 : (0 : ℤ) ≤ M := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 hM0]
  have hQrec : ∀ i, i < L → (b : ℤ) * Qv (i + 1) = a * Qv i + c i := by
    intro i hi
    simp only [Qv]
    linear_combination (M : ℤ) * htrec T i hi - hd i hi
  refine ⟨Qv 0 + θ 0 - ν, ?_, ?_⟩
  · have h1 : T₀ + |ν| ≤ ((⌈T₀ + |ν|⌉.toNat : ℤ) : ℝ) :=
      (Int.le_ceil _).trans (by exact_mod_cast Int.self_le_toNat ⌈T₀ + |ν|⌉)
    have h2 : ((⌈T₀ + |ν|⌉.toNat : ℤ) : ℝ) < ((Qv 0 : ℤ) : ℝ) := by exact_mod_cast hQ0
    linarith [hθ0 0 (Nat.zero_le _), le_abs_self ν]
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hx : ∀ i, i ≤ L → (Qv 0 + θ 0 - ν) * ((a : ℝ) / b) ^ i + ν = Qv i + θ i := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
      have ih' : (Qv 0 + θ 0 - ν) * ((a : ℝ) / b) ^ i = Qv i + θ i - ν := by
        linarith [ih (by omega)]
      have key : (Qv i + θ i - ν) * ((a : ℝ) / b) = (Qv i + θ i - ν) * a / b := by ring
      rw [pow_succ, ← mul_assoc, ih', key, div_add' _ _ _ hbR]
      have e1 : (b : ℝ) * (Qv (i + 1) : ℝ) = (a : ℝ) * Qv i + c i := by
        exact_mod_cast hQrec i (by omega)
      have e2 := hcar i (by omega)
      rw [div_eq_iff hbR]
      linear_combination (-1 : ℝ) * e1 + e2
  intro i hi
  have hfl : Qf a b (Qv 0 + θ 0 - ν) ν i = Qv i := by
    simp only [Qf, Z32.xInt, Z32.orb]
    rw [hx i hi, Int.floor_eq_iff]
    exact ⟨by linarith [hθ0 i hi], by linarith [hθ1 i hi]⟩
  refine ⟨?_, ?_⟩
  · rw [hfl]
    simp only [Qv, Int.ModEq, Int.add_mul_emod_self_left]
  · simp only [θf, Z32.yFract, Z32.orb]
    rw [hx i hi, Int.fract_eq_iff]
    exact ⟨hθ0 i hi, hθ1 i hi, ⟨Qv i, by ring⟩⟩

end Oda
