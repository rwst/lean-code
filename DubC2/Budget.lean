/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.Obstruction
import Oda26.Jacobsthal

/-!
# The external-prime budget for floor certificates ([Oda26] Theorem 42 (28), Theorem 44, Cor. 45)

For the floor orbit `⌊ξ(p/q)ⁿ⌋` (`a = 0`), the two-letter obstruction
`DubC2.Gen.not_checked_of_two_letters` with the letters `Δ = p − q` and `c = Δ − h` gives the
paper's form of Theorem 42: a checked certificate rules out every `c < Δ` with `Δ − c < p`, `c`
prime to the primes of `M` dividing `p`, to the primes of `q`, and `Δ − c` divisible by every
other prime of `M`.  Feeding in a Jacobsthal window turns this into a lower bound on the "external"
part `R` of `M` (the primes outside `2pq`):

* `DubC2.Gen.not_checked_floor_of_letter` — **[Oda26] Theorem 42** (floor form, condition (28)).
* `DubC2.Gen.p_le_of_window` — **[Oda26] Theorem 44 (29)** with any window length `J`:
  `p ≤ 2R·J`.
* `DubC2.Gen.p_le_jacobsthal` — (29) as stated: `p ≤ 2R·J(N₀)`, `N₀` the odd primes of `pq`.
* `DubC2.Gen.p_le_three_pow` — (30): `p ≤ 2R·3^k`, `k = ω(N₀)`.
* `DubC2.Gen.p_le_four_mul_R`, `DubC2.Gen.p_le_six_mul_R` — **[Oda26] Corollary 45** (a), (b).
* `DubC2.Gen.exists_bound_of_R` — **[Oda26] Theorem 44, last part:** with the external primes
  confined to a fixed product `R₀`, only finitely many bases admit a checked floor certificate.

All bounds are independent of the number of cells `D`.

## References

* [Oda26] Y. Odagiri, *Finite graph certificates for composite terms in rational floor sequences*,
  Zenodo, doi:10.5281/zenodo.22997709 (2026).
-/

namespace DubC2.Gen

open Finset Oda Filter Topology

/-- **[Oda26] Theorem 42, floor form.**  For `a = 0`: if `c < Δ = p − q`, `Δ − c < p`, every
`l ∈ PM` either divides `p` but not `c`, or divides `Δ − c`, and no `l ∈ Pq` divides `c`, then no
certificate is checked. -/
@[category research solved, AMS 11 37, ref "Oda26", group "dubc2_obstruction"]
theorem not_checked_floor_of_letter {P : Params} {C : Cert} (ha : P.a = 0) {c : ℤ}
    (hc0 : c < (P.p : ℤ) - P.q) (hc1 : (P.p : ℤ) - P.q - c < P.p)
    (hPM : ∀ l ∈ P.PM, 2 ≤ l ∧
      (((l : ℤ) ∣ P.p ∧ ¬ (l : ℤ) ∣ c) ∨ (l : ℤ) ∣ (P.p : ℤ) - P.q - c))
    (hPq : ∀ l ∈ P.Pq, 2 ≤ l ∧ ¬ (l : ℤ) ∣ c) : ¬ Checked P C := by
  intro hc
  have hF : ParamFacts P := by
    have hh := hc.head
    simp only [checkHead, Bool.and_eq_true] at hh
    exact paramFacts hh.1.1.1.1.1
  have hcop := hF.cop
  have hM := hF.M0
  have hb0 : (0 : ℝ) < P.b := by exact_mod_cast hF.b0
  have hp0 : (0 : ℝ) < P.p := by exact_mod_cast (show 0 < P.p by have := hF.pq; omega)
  have hΔ : ((P.p : ℝ) - P.q) ≠ 0 := by
    have : (P.q : ℝ) < P.p := by exact_mod_cast hF.pq
    linarith
  have hxs : (((((P.p : ℤ) - P.q : ℤ)) : ℝ) * P.b + ((P.p : ℝ) - P.q) * P.a) /
      (((P.p : ℝ) - P.q) * P.b) = 1 := by
    rw [ha]; simp only [Int.cast_zero, mul_zero, add_zero]; push_cast; field_simp
  refine not_checked_of_two_letters (s₀ := (P.p : ℤ) - P.q) (c := c) (r₀ := P.M - 1) (by omega)
    (by omega) ?_ ?_ (by rw [hxs]; norm_num) (by rw [hxs]) ?_ ?_ hc
  · intro l hl
    obtain ⟨hl2, hlcase⟩ := hPM l hl
    have hlM : (l : ℤ) ∣ P.M := by exact_mod_cast Nat.dvd_of_mod_eq_zero (hF.PM l hl)
    have hcast : (((P.M - 1 : ℕ)) : ℤ) = (P.M : ℤ) - 1 := by omega
    refine ⟨?_, ?_⟩
    · intro hd
      rw [hcast] at hd
      have : (l : ℤ) ∣ 1 := by
        have := dvd_sub hlM hd; simpa using this
      have := Int.le_of_dvd one_pos this
      omega
    rcases hlcase with ⟨hlp, hlc⟩ | hlr
    · left
      refine ⟨hlp, ?_, hlc⟩
      intro hd
      have hlq : (l : ℤ) ∣ P.q := by
        have := dvd_sub hlp hd; simpa using this
      have := Nat.dvd_gcd (Int.natCast_dvd_natCast.1 hlp) (Int.natCast_dvd_natCast.1 hlq)
      rw [hcop] at this
      have := Nat.le_of_dvd one_pos this
      omega
    · right
      constructor
      · rw [hcast]
        have : ((P.p : ℤ) - P.q) * ((P.M : ℤ) - 1) + ((P.p : ℤ) - P.q) =
            ((P.p : ℤ) - P.q) * P.M := by ring
        rw [this]
        exact dvd_mul_of_dvd_right hlM _
      · have := dvd_neg.2 hlr
        rwa [neg_sub] at this
  · intro l hl
    obtain ⟨hlq, hlp⟩ := hF.Pq l hl
    obtain ⟨hl2, hlc⟩ := hPq l hl
    have hlq' : (l : ℤ) ∣ P.q := Int.natCast_dvd_natCast.2 (Nat.dvd_of_mod_eq_zero hlq)
    refine ⟨?_, hlc⟩
    intro hd
    have : (l : ℤ) ∣ P.p := by
      have := dvd_add hd hlq'; simpa using this
    have := Nat.dvd_gcd (dvd_refl l) (Int.natCast_dvd_natCast.1 this)
    rw [hlp] at this
    have := Nat.le_of_dvd one_pos this
    omega
  · rw [hxs]
    have : ((P.p : ℤ) : ℝ) - ((P.p : ℤ) - P.q : ℤ) + c > 0 := by
      have : ((((P.p : ℤ) - P.q - c : ℤ)) : ℝ) < ((P.p : ℤ) : ℝ) := by exact_mod_cast hc1
      push_cast at this ⊢; linarith
    rw [show (1 : ℝ) + ((c : ℝ) - (((P.p : ℤ) - P.q : ℤ) : ℝ)) / P.p =
      (((P.p : ℤ) : ℝ) - ((P.p : ℤ) - P.q : ℤ) + c) / P.p by push_cast; field_simp; ring]
    exact div_pos this hp0
  · rw [hxs]
    have : (c : ℝ) < (((P.p : ℤ) - P.q : ℤ) : ℝ) := by exact_mod_cast hc0
    have : ((c : ℝ) - (((P.p : ℤ) - P.q : ℤ) : ℝ)) / P.p < 0 :=
      div_neg_of_neg_of_pos (by linarith) hp0
    linarith

/-- **[Oda26] Theorem 44, (29), with any window length.**  Let `T` contain the odd primes of `pq`,
`R ≥ 1` be prime to `T` with every `l ∈ PM` not dividing `p` dividing `2R`, and suppose every `J`
consecutive integers contain one divisible by no prime of `T`.  If a floor certificate is
checked, then `p ≤ 2R·J`. -/
@[category research solved, AMS 11 37, ref "Oda26", group "dubc2_obstruction"]
theorem p_le_of_window {P : Params} {C : Cert} (ha : P.a = 0) (hPM2 : ∀ l ∈ P.PM, 2 ≤ l)
    (hPq2 : ∀ l ∈ P.Pq, 2 ≤ l) {T : Finset ℕ} (hT : ∀ l ∈ T, l.Prime ∧ l ≠ 2)
    (hTpq : ∀ l, l.Prime → l ≠ 2 → l ∣ P.p * P.q → l ∈ T) {R : ℕ} (hR0 : 0 < R)
    (hRT : ∀ l ∈ T, ¬ l ∣ R) (hR : ∀ l ∈ P.PM, ¬ (l : ℤ) ∣ P.p → (l : ℤ) ∣ 2 * R) {J : ℕ}
    (hJ : ∀ s : ℤ, ∃ x ∈ Ico s (s + J), Oda.Avoids T x) (hc : Checked P C) : P.p ≤ 2 * R * J := by
  have hF : ParamFacts P := by
    have hh := hc.head
    simp only [checkHead, Bool.and_eq_true] at hh
    exact paramFacts hh.1.1.1.1.1
  have hcop := hF.cop
  have hq1 := hF.q1
  have hpq := hF.pq
  by_contra hlt
  push Not at hlt
  -- `l ∈ T` never divides `2R`
  have hT2R : ∀ l ∈ T, ¬ (l : ℤ) ∣ 2 * R := by
    intro l hl hd
    have hlP := (hT l hl).1
    rcases (Nat.prime_iff_prime_int.mp hlP).dvd_or_dvd hd with h | h
    · have := Int.le_of_dvd two_pos h
      have := hlP.two_le
      exact (hT l hl).2 (by omega)
    · exact hRT l hl (Int.natCast_dvd_natCast.1 h)
  -- `2R` is invertible modulo `N₀ = ∏ T`
  have hco : IsCoprime ((2 * R : ℕ) : ℤ) ((∏ l ∈ T, l : ℕ) : ℤ) := by
    rw [isCoprime_prod_iff (fun l hl => (hT l hl).1)]
    intro l hl hd
    exact hT2R l hl (by exact_mod_cast hd)
  obtain ⟨u, v, huv⟩ := hco
  set Δ : ℤ := (P.p : ℤ) - P.q with hΔ
  obtain ⟨x, hx, hav⟩ := hJ (1 - Δ * u)
  rw [mem_Ico] at hx
  set m : ℤ := x + Δ * u with hm
  have hm1 : 1 ≤ m := by omega
  have hmJ : m ≤ J := by omega
  set c : ℤ := Δ - 2 * R * m with hcdef
  have hcN : c = Δ * v * ((∏ l ∈ T, l : ℕ) : ℤ) - 2 * R * x := by
    rw [hcdef, hm]; push_cast at huv ⊢; linear_combination -Δ * huv
  -- `c` avoids `T`
  have hcT : ∀ l ∈ T, ¬ (l : ℤ) ∣ c := by
    intro l hl hd
    have hlN : (l : ℤ) ∣ ((∏ l ∈ T, l : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.2 (dvd_prod_of_mem _ hl)
    have h2 : (l : ℤ) ∣ 2 * R * x := by
      have := dvd_sub (dvd_mul_of_dvd_right hlN (Δ * v)) hd
      rw [hcN] at this; simpa using this
    rcases (Nat.prime_iff_prime_int.mp (hT l hl).1).dvd_or_dvd h2 with h | h
    · exact hT2R l hl h
    · exact hav l hl h
  -- hence no divisor `l ≥ 2` of `p` or `q` divides `c`
  have hpq2 : ¬ (2 ∣ P.p ∧ 2 ∣ P.q) := by
    rintro ⟨h1, h2⟩
    have := Nat.dvd_gcd h1 h2
    rw [hcop] at this
    omega
  have hnd : ∀ l : ℕ, 2 ≤ l → l ∣ P.p * P.q → ¬ (l : ℤ) ∣ c := by
    intro l hl hlpq hd
    have hr := Nat.minFac_prime (show l ≠ 1 by omega)
    have hrl : l.minFac ∣ l := Nat.minFac_dvd l
    have hrc : (l.minFac : ℤ) ∣ c := dvd_trans (Int.natCast_dvd_natCast.2 hrl) hd
    by_cases hr2 : l.minFac = 2
    · rw [hr2] at hrc hrl
      have h2pq : 2 ∣ P.p ∨ 2 ∣ P.q := (Nat.Prime.dvd_mul Nat.prime_two).1 (dvd_trans hrl hlpq)
      have hodd : Δ % 2 = 1 := by rw [hΔ]; omega
      have : c = Δ - 2 * (R * m) := by rw [hcdef]; ring
      generalize R * m = K at this
      push_cast at hrc
      omega
    · exact hcT _ (hTpq _ hr hr2 (dvd_trans hrl hlpq)) hrc
  have h2RmJ : 2 * (R : ℤ) * m ≤ 2 * R * J := by
    have : (0 : ℤ) ≤ 2 * R := by positivity
    exact mul_le_mul_of_nonneg_left hmJ this
  have hpJ : (2 * R * J : ℤ) < P.p := by exact_mod_cast hlt
  have hRpos : (0 : ℤ) < R := by exact_mod_cast hR0
  refine not_checked_floor_of_letter ha (c := c) (by rw [hcdef]; nlinarith)
    (by rw [hcdef]; linarith) ?_ ?_ hc
  · intro l hl
    refine ⟨hPM2 l hl, ?_⟩
    by_cases hlp : (l : ℤ) ∣ P.p
    · exact Or.inl ⟨hlp, hnd l (hPM2 l hl)
        (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.1 hlp) _)⟩
    · right
      rw [hcdef, show Δ - (Δ - 2 * R * m) = 2 * R * m by ring]
      exact dvd_mul_of_dvd_left (hR l hl hlp) _
  · intro l hl
    obtain ⟨hlq, _⟩ := hF.Pq l hl
    exact ⟨hPq2 l hl, hnd l (hPq2 l hl) (dvd_mul_of_dvd_right (Nat.dvd_of_mod_eq_zero hlq) _)⟩

/-- **[Oda26] Theorem 44, (29).**  `p ≤ 2R·J(N₀)` with `N₀ = ∏ T`. -/
@[category research solved, AMS 11 37, ref "Oda26", group "dubc2_obstruction"]
theorem p_le_jacobsthal {P : Params} {C : Cert} (ha : P.a = 0) (hPM2 : ∀ l ∈ P.PM, 2 ≤ l)
    (hPq2 : ∀ l ∈ P.Pq, 2 ≤ l) {T : Finset ℕ} (hT : ∀ l ∈ T, l.Prime ∧ l ≠ 2)
    (hTpq : ∀ l, l.Prime → l ≠ 2 → l ∣ P.p * P.q → l ∈ T) {R : ℕ} (hR0 : 0 < R)
    (hRT : ∀ l ∈ T, ¬ l ∣ R) (hR : ∀ l ∈ P.PM, ¬ (l : ℤ) ∣ P.p → (l : ℤ) ∣ 2 * R)
    (hc : Checked P C) : P.p ≤ 2 * R * jacobsthal (∏ l ∈ T, l) := by
  refine p_le_of_window ha hPM2 hPq2 hT hTpq hR0 hRT hR (fun s => ?_) hc
  have hpos : 0 < ∏ l ∈ T, l := prod_pos fun l hl => (hT l hl).1.pos
  obtain ⟨x, hx, hco⟩ := jacobsthal_spec hpos s
  exact ⟨x, hx, (isCoprime_prod_iff (fun l hl => (hT l hl).1) x).1 hco⟩

/-- **[Oda26] Theorem 44, (30).**  `p ≤ 2R·3^k` with `k = |T|`. -/
@[category research solved, AMS 11 37, ref "Oda26", group "dubc2_obstruction"]
theorem p_le_three_pow {P : Params} {C : Cert} (ha : P.a = 0) (hPM2 : ∀ l ∈ P.PM, 2 ≤ l)
    (hPq2 : ∀ l ∈ P.Pq, 2 ≤ l) {T : Finset ℕ} (hT : ∀ l ∈ T, l.Prime ∧ l ≠ 2)
    (hTpq : ∀ l, l.Prime → l ≠ 2 → l ∣ P.p * P.q → l ∈ T) {R : ℕ} (hR0 : 0 < R)
    (hRT : ∀ l ∈ T, ¬ l ∣ R) (hR : ∀ l ∈ P.PM, ¬ (l : ℤ) ∣ P.p → (l : ℤ) ∣ 2 * R)
    (hc : Checked P C) : P.p ≤ 2 * R * 3 ^ T.card :=
  p_le_of_window ha hPM2 hPq2 hT hTpq hR0 hRT hR (fun s => exists_avoids T hT s le_rfl) hc

/-- **[Oda26] Corollary 45(a).**  For an odd prime `p` and `q` a power of `2`: `p ≤ 4R`. -/
@[category research solved, AMS 11 37, ref "Oda26", group "dubc2_obstruction"]
theorem p_le_four_mul_R {P : Params} {C : Cert} (ha : P.a = 0) (hPM2 : ∀ l ∈ P.PM, 2 ≤ l)
    (hPq2 : ∀ l ∈ P.Pq, 2 ≤ l) (hp : P.p.Prime) (hp2 : P.p ≠ 2) {s : ℕ} (hq : P.q = 2 ^ s)
    {R : ℕ} (hR0 : 0 < R) (hRp : ¬ P.p ∣ R)
    (hR : ∀ l ∈ P.PM, ¬ (l : ℤ) ∣ P.p → (l : ℤ) ∣ 2 * R) (hc : Checked P C) :
    P.p ≤ 4 * R := by
  have hT : ∀ l ∈ ({P.p} : Finset ℕ), l.Prime ∧ l ≠ 2 := by
    intro l hl; rw [mem_singleton] at hl; subst hl; exact ⟨hp, hp2⟩
  have h := p_le_jacobsthal ha hPM2 hPq2 hT (fun l hl hl2 hd => by
      rw [mem_singleton]
      rcases (Nat.Prime.dvd_mul hl).1 hd with h | h
      · exact (Nat.prime_dvd_prime_iff_eq hl hp).1 h
      · rw [hq] at h
        exact absurd ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (hl.dvd_of_dvd_pow h)) hl2)
    hR0 (fun l hl => by rw [mem_singleton] at hl; subst hl; exact hRp) hR hc
  rw [prod_singleton, jacobsthal_prime hp] at h
  omega

/-- **[Oda26] Corollary 45(b).**  For distinct odd primes `p, q`: `p ≤ 6R`. -/
@[category research solved, AMS 11 37, ref "Oda26", group "dubc2_obstruction"]
theorem p_le_six_mul_R {P : Params} {C : Cert} (ha : P.a = 0) (hPM2 : ∀ l ∈ P.PM, 2 ≤ l)
    (hPq2 : ∀ l ∈ P.Pq, 2 ≤ l) (hp : P.p.Prime) (hq : P.q.Prime) (hp2 : P.p ≠ 2)
    (hq2 : P.q ≠ 2) {R : ℕ} (hR0 : 0 < R) (hRp : ¬ P.p ∣ R) (hRq : ¬ P.q ∣ R)
    (hR : ∀ l ∈ P.PM, ¬ (l : ℤ) ∣ P.p → (l : ℤ) ∣ 2 * R) (hc : Checked P C) :
    P.p ≤ 6 * R := by
  have hF : ParamFacts P := by
    have hh := hc.head
    simp only [checkHead, Bool.and_eq_true] at hh
    exact paramFacts hh.1.1.1.1.1
  have hne : P.p ≠ P.q := by have := hF.pq; omega
  have hT : ∀ l ∈ ({P.p, P.q} : Finset ℕ), l.Prime ∧ l ≠ 2 := by
    intro l hl
    rcases mem_insert.1 hl with rfl | hl
    · exact ⟨hp, hp2⟩
    · rw [mem_singleton] at hl; subst hl; exact ⟨hq, hq2⟩
  have h := p_le_jacobsthal ha hPM2 hPq2 hT (fun l hl hl2 hd => by
      rcases (Nat.Prime.dvd_mul hl).1 hd with h | h
      · rw [(Nat.prime_dvd_prime_iff_eq hl hp).1 h]; simp
      · rw [(Nat.prime_dvd_prime_iff_eq hl hq).1 h]; simp)
    hR0 (fun l hl => by
      rcases mem_insert.1 hl with rfl | hl
      · exact hRp
      · rw [mem_singleton] at hl; subst hl; exact hRq) hR hc
  rw [prod_pair hne, jacobsthal_mul_primes hp hq hp2 hq2 hne] at h
  omega

/-- The odd primes of `n`. -/
def oddPrimes (n : ℕ) : Finset ℕ := n.primeFactors.filter (· ≠ 2)

/-- **[Oda26] Theorem 44, effective part.**  If the external primes are confined to a fixed
product `R₀` (every prime of `M` outside `p` divides `2R₀`), only finitely many bases `p/q` admit a
checked floor certificate: `p` is bounded in terms of `R₀` alone. -/
@[category research solved, AMS 11 37, ref "Oda26", group "dubc2_obstruction"]
theorem exists_bound_of_R (R₀ : ℕ) (hR₀ : 0 < R₀) :
    ∃ B : ℕ, ∀ (P : Params) (C : Cert), P.a = 0 → (∀ l ∈ P.PM, 2 ≤ l) → (∀ l ∈ P.Pq, 2 ≤ l) →
      Nat.Coprime R₀ (P.p * P.q) → (∀ l ∈ P.PM, ¬ (l : ℤ) ∣ P.p → (l : ℤ) ∣ 2 * R₀) →
      Checked P C → P.p ≤ B := by
  -- eventually `4R₀²·9^k < 2^k·k!`
  have ht := FloorSemiring.tendsto_pow_div_factorial_atTop (9 / 2 : ℝ)
  have hε : (0 : ℝ) < 1 / (4 * (R₀ : ℝ) ^ 2) := by positivity
  obtain ⟨K, hK⟩ := eventually_atTop.1 ((tendsto_order.1 ht).2 _ hε)
  refine ⟨2 * R₀ * 3 ^ K, fun P C ha hPM2 hPq2 hcop hR hc => ?_⟩
  have hF : ParamFacts P := by
    have hh := hc.head
    simp only [checkHead, Bool.and_eq_true] at hh
    exact paramFacts hh.1.1.1.1.1
  have hq1 := hF.q1
  have hpq := hF.pq
  have hn0 : P.p * P.q ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  set T := oddPrimes (P.p * P.q) with hTdef
  have hT : ∀ l ∈ T, l.Prime ∧ l ≠ 2 := by
    intro l hl
    rw [hTdef, oddPrimes, mem_filter, Nat.mem_primeFactors] at hl
    exact ⟨hl.1.1, hl.2⟩
  have hTpq : ∀ l, l.Prime → l ≠ 2 → l ∣ P.p * P.q → l ∈ T := by
    intro l hl hl2 hd
    rw [hTdef, oddPrimes, mem_filter, Nat.mem_primeFactors]
    exact ⟨⟨hl, hd, hn0⟩, hl2⟩
  have hRT : ∀ l ∈ T, ¬ l ∣ R₀ := by
    intro l hl hd
    have hlpq : l ∣ P.p * P.q := by
      rw [hTdef, oddPrimes, mem_filter, Nat.mem_primeFactors] at hl; exact hl.1.2.1
    have := Nat.dvd_gcd hd hlpq
    rw [hcop] at this
    exact (hT l hl).1.one_lt.ne' (Nat.dvd_one.1 this)
  have hbound := p_le_three_pow ha hPM2 hPq2 hT hTpq hR₀ hRT hR hc
  -- `2^k·k! ≤ N₀ ≤ pq < p²`
  have hfac := two_pow_mul_factorial_le_prod T fun l hl =>
    ⟨Nat.odd_iff.1 ((hT l hl).1.odd_of_ne_two (hT l hl).2), by
      have := (hT l hl).1.two_le; have := (hT l hl).2; omega⟩
  have hdvd : ∏ l ∈ T, l ∣ P.p * P.q :=
    dvd_trans (prod_dvd_prod_of_subset _ _ _ (filter_subset _ _)) (Nat.prod_primeFactors_dvd _)
  have hle := Nat.le_of_dvd (by positivity) hdvd
  have hpp : P.p * P.q < P.p * P.p := Nat.mul_lt_mul_of_pos_left hpq (by omega)
  have hsq : P.p * P.p ≤ (2 * R₀ * 3 ^ T.card) * (2 * R₀ * 3 ^ T.card) :=
    Nat.mul_le_mul hbound hbound
  -- so `k < K`
  have hk : T.card < K := by
    by_contra hk
    push Not at hk
    have h1 := hK T.card hk
    have hf : (0 : ℝ) < (T.card.factorial : ℝ) := by exact_mod_cast T.card.factorial_pos
    rw [div_lt_div_iff₀ hf (by positivity), one_mul] at h1
    have h2 : ((2 ^ T.card * T.card.factorial : ℕ) : ℝ) <
        ((2 * R₀ * 3 ^ T.card) * (2 * R₀ * 3 ^ T.card) : ℕ) := by
      exact_mod_cast (lt_of_le_of_lt hfac (lt_of_le_of_lt hle (lt_of_lt_of_le hpp hsq)))
    push_cast at h2
    have h3 : (9 / 2 : ℝ) ^ T.card * 2 ^ T.card = 9 ^ T.card := by rw [← mul_pow]; norm_num
    have h4 : (3 : ℝ) ^ T.card * 3 ^ T.card = 9 ^ T.card := by rw [← mul_pow]; norm_num
    have h5 : (0 : ℝ) < 2 ^ T.card := by positivity
    nlinarith
  calc P.p ≤ 2 * R₀ * 3 ^ T.card := hbound
    _ ≤ 2 * R₀ * 3 ^ K := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hk.le)

end DubC2.Gen
