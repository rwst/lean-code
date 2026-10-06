/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.NumberTheory.Padics.PadicNorm
public import ForMathlib.NumberTheory.PadicFracPart

@[expose] public section

/-!
# The ring `ℤ[1/N_S]` of `S`-integers of `ℚ`, and its units

For a finite set of primes `S`, with `N_S = ∏_{p ∈ S} p`, the ring of `S`-integers is

`ℤ[1/N_S] = {m / N_Sᵏ} = {q ∈ ℚ : |q|_ℓ ≤ 1 for every prime ℓ ∉ S}`.

It is the lattice of the `S`-adic solenoid `Σ_S = (ℝ × ∏_{p ∈ S} ℚ_p) / ℤ[1/N_S]`, and its units
act on `Σ_S` by automorphisms.  This file is the arithmetic layer of that construction.

`S` is a `Finset Nat.Primes`, never an unchecked `Finset ℕ`: with typed primes every `ℚ_[p]` and
`padicNorm p` over `p ∈ S` elaborates without a `Fact p.Prime` side condition, through the global
instance `Nat.Primes.instFactPrime`.  An integer base `b` enters only through `Nat.primesOf b`, so
everything depends on the radical of `b` only.

## Main declarations

* `Nat.Primes.instFactPrime`, `Nat.primesOf` — typed primes, the primes of an integer.
* `Rat.sModulus S = N_S`, `Rat.sIntegers S : Subring ℚ` (concrete definition `{m / N_Sᵏ}`),
  `Rat.mem_sIntegers_iff_forall_padicNorm_le_one` (the valuation characterisation).
* `Rat.isInt_of_forall_padicNorm_le_one` — integral at every prime ⇒ integer.
* `Rat.exists_intCast_of_mem_sIntegers` — the *uniqueness engine*: an `S`-integer integral at
  every `p ∈ S` is an integer.
* `Rat.exists_sub_sum_principalPart_eq_intCast` — partial fractions: an `S`-integer minus the sum
  of its `p`-adic principal parts (`p ∈ S`) is an integer; no Bézout identity is used.
* `Rat.IsSUnit` with `one`, `mul`, `inv`, `div`, `neg`, `pow`, and `Rat.isSUnit_natCast` (every
  positive integer supported on `S`), `Rat.isSUnit_prime`.
* `Rat.prod_padicNorm_natCast` — if every prime factor of `d ≠ 0` lies in `S`, then
  `∏ l ∈ S, |d|_l = d⁻¹`.

## Implementation notes

The valuation characterisation, not the concrete definition, does the work: membership of
`b⁻¹`, of `m / pᵏ`, and of the partial-fraction remainder all reduce to "integral at every prime
outside `S`", so no coprimality bookkeeping over `S` is ever needed.

The declarations of this section are ported from `DiophantineApproximation/{RationalPlaces,
PrimeProducts}.lean` of the author's `Subspace-Theorems` repository (same author, there under
Apache-2.0).  Linking those files was tried first (gate G-2 of `plans/plan-udmf-O5.html`) and
failed on Mathlib API drift in their import closure (`PlacesOverFinite.lean`), so the five
declarations actually used are restated here.  `primesOf` is defined by `Finset.subtype` instead
of the original `attach.image`; the membership lemma is the same.

⚠ `decide` cannot evaluate `Nat.primeFactors`; compute `primesOf` through `Nat.mem_primesOf_iff_dvd`
or `simp` lemmas for `Nat.primeFactors`.

## Status

Everything in this file is standard; the contribution is the formalisation.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  Section 1.4.
-/

/-- Every typed prime is prime.  Global, and declared once in this repository: Mathlib's
`NumberTheory/Padics/HeightOneSpectrum.lean` keeps the same instance local. -/
instance Nat.Primes.instFactPrime (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

namespace Nat

/-- The primes dividing `n`, as a finite set of `Nat.Primes`.  It is empty for `n = 0` and for
`n = 1`. -/
def primesOf (n : ℕ) : Finset Nat.Primes :=
  n.primeFactors.subtype Nat.Prime

theorem mem_primesOf {n : ℕ} {l : Nat.Primes} : l ∈ n.primesOf ↔ (l : ℕ) ∈ n.primeFactors :=
  Finset.mem_subtype

/-- A prime belongs to `n.primesOf` exactly when it divides `n`, for `n ≠ 0`. -/
theorem mem_primesOf_iff_dvd {n : ℕ} (hn : n ≠ 0) {l : Nat.Primes} :
    l ∈ n.primesOf ↔ (l : ℕ) ∣ n := by
  rw [mem_primesOf, Nat.mem_primeFactors]
  exact ⟨fun h ↦ h.2.1, fun h ↦ ⟨l.2, h, hn⟩⟩

/-- A prime dividing a power of `n` belongs to `n.primesOf`. -/
theorem mem_primesOf_of_dvd_pow {n k : ℕ} (hn : n ≠ 0) {l : Nat.Primes} (h : (l : ℕ) ∣ n ^ k) :
    l ∈ n.primesOf :=
  (mem_primesOf_iff_dvd hn).mpr (l.2.dvd_of_dvd_pow h)

end Nat

namespace Rat

/-- **The finite part of the product formula, over the primes of the number itself.**  If every
prime factor of `d` lies in `S`, then `∏ l ∈ S, padicNorm l d = d⁻¹`: the factors `S` adds
beyond the prime factors of `d` are `1`, and none is missing. -/
theorem prod_padicNorm_natCast (S : Finset Nat.Primes) :
    ∀ d : ℕ, d ≠ 0 → (∀ l : Nat.Primes, (l : ℕ) ∣ d → l ∈ S) →
      ∏ l ∈ S, padicNorm (l : ℕ) ((d : ℕ) : ℚ) = ((d : ℕ) : ℚ)⁻¹ := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd hS
    rcases eq_or_ne d 1 with rfl | hd1
    · simp
    obtain ⟨l₀, hl₀p, e, rfl⟩ : ∃ l₀ : ℕ, l₀.Prime ∧ ∃ e : ℕ, d = l₀ * e := by
      obtain ⟨l₀, hl₀p, hl₀d⟩ := Nat.exists_prime_and_dvd hd1
      exact ⟨l₀, hl₀p, hl₀d⟩
    have he0 : e ≠ 0 := by rintro rfl; simp at hd
    have helt : e < l₀ * e :=
      lt_mul_of_one_lt_left (Nat.pos_of_ne_zero he0) hl₀p.one_lt
    have hSe : ∀ l : Nat.Primes, (l : ℕ) ∣ e → l ∈ S :=
      fun l hl ↦ hS l (hl.mul_left l₀)
    have hsingle : ∏ l ∈ S, padicNorm (l : ℕ) ((l₀ : ℕ) : ℚ) = ((l₀ : ℕ) : ℚ)⁻¹ := by
      have hmem : (⟨l₀, hl₀p⟩ : Nat.Primes) ∈ S := hS ⟨l₀, hl₀p⟩ ⟨e, rfl⟩
      refine Eq.trans (Finset.prod_eq_single (s := S)
        (f := fun l : Nat.Primes ↦ padicNorm (l : ℕ) ((l₀ : ℕ) : ℚ))
        (⟨l₀, hl₀p⟩ : Nat.Primes) (fun b _ hb ↦ ?_) (fun hcon ↦ absurd hmem hcon)) ?_
      · have hne : (b : ℕ) ≠ l₀ := fun hc ↦ hb (Subtype.ext hc)
        exact (padicNorm.nat_eq_one_iff _).mpr
          fun hdvd ↦ hne ((Nat.prime_dvd_prime_iff_eq b.2 hl₀p).mp hdvd)
      · change padicNorm l₀ ((l₀ : ℕ) : ℚ) = ((l₀ : ℕ) : ℚ)⁻¹
        exact padicNorm.padicNorm_p hl₀p.one_lt
    have hrec := ih e helt he0 hSe
    have hcast : ((l₀ * e : ℕ) : ℚ) = ((l₀ : ℕ) : ℚ) * ((e : ℕ) : ℚ) := by push_cast; ring
    calc ∏ l ∈ S, padicNorm (l : ℕ) ((l₀ * e : ℕ) : ℚ)
        = ∏ l ∈ S, padicNorm (l : ℕ) ((l₀ : ℕ) : ℚ) * padicNorm (l : ℕ) ((e : ℕ) : ℚ) := by
          refine Finset.prod_congr rfl fun l _ ↦ ?_
          rw [hcast, padicNorm.mul]
      _ = (∏ l ∈ S, padicNorm (l : ℕ) ((l₀ : ℕ) : ℚ))
            * ∏ l ∈ S, padicNorm (l : ℕ) ((e : ℕ) : ℚ) := Finset.prod_mul_distrib
      _ = ((l₀ : ℕ) : ℚ)⁻¹ * ((e : ℕ) : ℚ)⁻¹ := by rw [hsingle, hrec]
      _ = ((l₀ * e : ℕ) : ℚ)⁻¹ := by rw [hcast, mul_inv]

end Rat

/-! ### Divisibility helpers -/

namespace Nat

theorem primesOf_mono {m n : ℕ} (h : m ∣ n) (hn : n ≠ 0) : m.primesOf ⊆ n.primesOf :=
  fun _ hl ↦ mem_primesOf.mpr (Nat.primeFactors_mono h hn (mem_primesOf.mp hl))

/-- If every prime factor of `d` divides `N`, then `d ∣ N ^ d` (the exponent `d` is lazy but
always large enough: every `p`-adic valuation of `d` is `< d`). -/
theorem dvd_pow_self_of_forall_prime_dvd {d N : ℕ} (hd : d ≠ 0) (hN : N ≠ 0)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ d → ℓ ∣ N) : d ∣ N ^ d := by
  refine (Nat.factorization_le_iff_dvd hd (pow_ne_zero _ hN)).mp fun ℓ ↦ ?_
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  rcases Nat.eq_zero_or_pos (d.factorization ℓ) with h0 | hpos
  · rw [h0]; exact Nat.zero_le _
  have hℓ : ℓ.Prime := Nat.prime_of_mem_primeFactors (Finsupp.mem_support_iff.mpr hpos.ne')
  have hdvd : ℓ ∣ d := Nat.dvd_of_factorization_pos hpos.ne'
  have hN1 : 1 ≤ N.factorization ℓ := (hℓ.factorization_pos_of_dvd hN (h ℓ hℓ hdvd))
  calc d.factorization ℓ ≤ d := (Nat.factorization_lt ℓ hd).le
    _ = d * 1 := (mul_one d).symm
    _ ≤ d * N.factorization ℓ := Nat.mul_le_mul_left d hN1

end Nat

/-! ### Integrality at single primes -/

namespace padicNorm

/-- If `p` does not divide `q` then `m / qᵏ` is a `p`-adic integer: a principal part at one prime
is invisible at every other prime. -/
theorem intCast_div_pow_le_one_of_not_dvd {p q : ℕ} [Fact p.Prime] (hq : ¬ p ∣ q) (m : ℤ)
    (k : ℕ) : padicNorm p ((m : ℚ) / (q : ℚ) ^ k) ≤ 1 := by
  have h1 : padicNorm p ((q : ℚ) ^ k) = 1 := by
    rw [IsAbsoluteValue.abv_pow (padicNorm p), (padicNorm.nat_eq_one_iff q).mpr hq, one_pow]
  rw [padicNorm.div, h1, div_one]
  exact padicNorm.of_int m

/-- A prime dividing the denominator of `q` sees `q` as a non-integer. -/
theorem one_lt_of_dvd_den {p : ℕ} [hp : Fact p.Prime] {q : ℚ} (h : p ∣ q.den) :
    1 < padicNorm p q := by
  have hnum : ¬ (p : ℤ) ∣ q.num := by
    intro hn
    have : p = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left (Int.natCast_dvd.mp hn) q.reduced) h
    exact hp.out.one_lt.ne' this
  have hden0 : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  have hpos : 0 < padicNorm p (q.den : ℚ) :=
    lt_of_le_of_ne (padicNorm.nonneg _) (Ne.symm fun h0 ↦ hden0 (padicNorm.zero_of_padicNorm_eq_zero h0))
  rw [← Rat.num_div_den q, padicNorm.div, (padicNorm.int_eq_one_iff _).mpr hnum,
    one_lt_div hpos]
  exact (padicNorm.nat_lt_one_iff _).mpr h

end padicNorm

/-! ### The ring `ℤ[1/N_S]` of `S`-integers -/

namespace Rat

variable {S : Finset Nat.Primes}

/-- A rational number which is a `p`-adic integer at every prime is a rational integer. -/
theorem isInt_of_forall_padicNorm_le_one {q : ℚ} (h : ∀ ℓ : Nat.Primes, padicNorm ℓ q ≤ 1) :
    ∃ n : ℤ, q = n := by
  have hden : q.den = 1 := by
    by_contra hne
    obtain ⟨ℓ, hℓ, hdvd⟩ := Nat.exists_prime_and_dvd hne
    exact (h ⟨ℓ, hℓ⟩).not_gt (padicNorm.one_lt_of_dvd_den (p := ℓ) (hp := ⟨hℓ⟩) hdvd)
  exact ⟨q.num, (Rat.coe_int_num_of_den_eq_one hden).symm⟩

variable (S) in
/-- `N_S = ∏_{p ∈ S} p`, the squarefree modulus of `S`. -/
def sModulus : ℕ := ∏ p ∈ S, (p : ℕ)

theorem sModulus_pos : 0 < sModulus S := Finset.prod_pos fun p _ ↦ p.2.pos

theorem sModulus_ne_zero : sModulus S ≠ 0 := sModulus_pos.ne'

theorem dvd_sModulus {p : Nat.Primes} (hp : p ∈ S) : (p : ℕ) ∣ sModulus S :=
  Finset.dvd_prod_of_mem _ hp

/-- The primes dividing `N_S` are exactly the primes of `S`. -/
theorem dvd_sModulus_iff {p : Nat.Primes} : (p : ℕ) ∣ sModulus S ↔ p ∈ S := by
  refine ⟨fun h ↦ ?_, dvd_sModulus⟩
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff p.2.prime _).mp h
  rwa [show p = q from Subtype.ext ((Nat.prime_dvd_prime_iff_eq p.2 q.2).mp hpq)]

variable (S) in
/-- **The ring of `S`-integers** `ℤ[1/N_S] = {m / N_Sᵏ}` of `ℚ`, as a subring.  Its valuation
characterisation is `Rat.mem_sIntegers_iff_forall_padicNorm_le_one`. -/
def sIntegers : Subring ℚ where
  carrier := {q : ℚ | ∃ (m : ℤ) (k : ℕ), q = (m : ℚ) / (sModulus S : ℚ) ^ k}
  zero_mem' := ⟨0, 0, by simp⟩
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro a b ⟨m, k, rfl⟩ ⟨m', k', rfl⟩
    have h : (sModulus S : ℚ) ≠ 0 := by exact_mod_cast sModulus_ne_zero
    exact ⟨m * (sModulus S : ℤ) ^ k' + m' * (sModulus S : ℤ) ^ k, k + k', by
      push_cast; rw [pow_add]; field_simp⟩
  mul_mem' := by
    rintro a b ⟨m, k, rfl⟩ ⟨m', k', rfl⟩
    exact ⟨m * m', k + k', by push_cast; rw [pow_add]; ring⟩
  neg_mem' := by
    rintro a ⟨m, k, rfl⟩
    exact ⟨-m, k, by push_cast; ring⟩

theorem mem_sIntegers {q : ℚ} :
    q ∈ sIntegers S ↔ ∃ (m : ℤ) (k : ℕ), q = (m : ℚ) / (sModulus S : ℚ) ^ k := Iff.rfl

/-- An `S`-integer is a `ℓ`-adic integer at every prime `ℓ ∉ S`. -/
theorem padicNorm_le_one_of_mem_sIntegers {q : ℚ} (hq : q ∈ sIntegers S) {ℓ : Nat.Primes}
    (hℓ : ℓ ∉ S) : padicNorm ℓ q ≤ 1 := by
  obtain ⟨m, k, rfl⟩ := hq
  exact padicNorm.intCast_div_pow_le_one_of_not_dvd (fun h ↦ hℓ (dvd_sModulus_iff.mp h)) m k

/-- A rational which is integral at every prime outside `S` is an `S`-integer. -/
theorem mem_sIntegers_of_forall_padicNorm_le_one {q : ℚ}
    (h : ∀ ℓ : Nat.Primes, ℓ ∉ S → padicNorm ℓ q ≤ 1) : q ∈ sIntegers S := by
  have hS : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ q.den → ℓ ∣ sModulus S := by
    intro ℓ hℓ hdvd
    by_contra hn
    exact (h ⟨ℓ, hℓ⟩ fun hm ↦ hn (dvd_sModulus hm)).not_gt
      (padicNorm.one_lt_of_dvd_den (p := ℓ) (hp := ⟨hℓ⟩) hdvd)
  obtain ⟨c, hc⟩ := Nat.dvd_pow_self_of_forall_prime_dvd q.den_nz sModulus_ne_zero hS
  have hc' : (sModulus S : ℚ) ^ q.den = (q.den : ℚ) * c := by exact_mod_cast hc
  have hc0 : (c : ℚ) ≠ 0 := by
    rintro h0
    rw [h0, mul_zero] at hc'
    exact pow_ne_zero _ (by exact_mod_cast sModulus_ne_zero) hc'
  refine ⟨q.num * c, q.den, ?_⟩
  rw [hc']
  push_cast
  rw [mul_div_mul_right _ _ hc0, Rat.num_div_den]

/-- **The valuation characterisation of `ℤ[1/N_S]`.** -/
theorem mem_sIntegers_iff_forall_padicNorm_le_one {q : ℚ} :
    q ∈ sIntegers S ↔ ∀ ℓ : Nat.Primes, ℓ ∉ S → padicNorm ℓ q ≤ 1 :=
  ⟨fun hq _ hℓ ↦ padicNorm_le_one_of_mem_sIntegers hq hℓ,
    mem_sIntegers_of_forall_padicNorm_le_one⟩

/-- `m / pᵏ ∈ ℤ[1/N_S]` for `p ∈ S`: every `p`-adic principal part is an `S`-integer. -/
theorem div_pow_mem_sIntegers {p : Nat.Primes} (hp : p ∈ S) (m : ℤ) (k : ℕ) :
    (m : ℚ) / ((p : ℕ) : ℚ) ^ k ∈ sIntegers S :=
  mem_sIntegers_of_forall_padicNorm_le_one fun ℓ hℓ ↦
    padicNorm.intCast_div_pow_le_one_of_not_dvd (fun h ↦ hℓ
      ((Subtype.ext ((Nat.prime_dvd_prime_iff_eq ℓ.2 p.2).mp h) : ℓ = p) ▸ hp)) m k

/-- **Uniqueness engine.**  An `S`-integer which is integral at every prime of `S` is a rational
integer.  (For `S = {2, 3}` this is `2ᵏ ∣ m ∧ 3ᵏ ∣ m → 6ᵏ ∣ m`; here no coprimality bookkeeping
is needed.) -/
theorem exists_intCast_of_mem_sIntegers {q : ℚ} (hq : q ∈ sIntegers S)
    (h : ∀ p ∈ S, padicNorm (p : ℕ) q ≤ 1) : ∃ n : ℤ, q = n :=
  isInt_of_forall_padicNorm_le_one fun ℓ ↦
    if hℓ : ℓ ∈ S then h ℓ hℓ else padicNorm_le_one_of_mem_sIntegers hq hℓ

/-- **Partial fractions without Bézout.**  An `S`-integer differs from the sum of its `p`-adic
principal parts, `p ∈ S`, by a rational integer.  This is the well-definedness input of the
characters of the `S`-adic solenoid: the difference is integral at every prime (at `p ∈ S` by
the defining property of the principal part, which is invisible at the other primes; outside `S`
by the valuation characterisation), hence an integer. -/
theorem exists_sub_sum_principalPart_eq_intCast {q : ℚ} (hq : q ∈ sIntegers S) :
    ∃ n : ℤ, q - ∑ p ∈ S, Padic.principalPart (p : ℕ) (q : ℚ_[(p : ℕ)]) = n := by
  apply isInt_of_forall_padicNorm_le_one
  intro ℓ
  have hpart : ∀ p ∈ S, p ≠ ℓ →
      padicNorm ℓ (Padic.principalPart (p : ℕ) (q : ℚ_[(p : ℕ)])) ≤ 1 := by
    intro p _ hpℓ
    obtain ⟨m, k, hmk⟩ := Padic.exists_principalPart_eq (p := (p : ℕ)) (q : ℚ_[(p : ℕ)])
    rw [hmk]
    exact padicNorm.intCast_div_pow_le_one_of_not_dvd (fun h ↦ hpℓ
      (Subtype.ext ((Nat.prime_dvd_prime_iff_eq ℓ.2 p.2).mp h).symm)) m k
  by_cases hℓ : ℓ ∈ S
  · rw [← Finset.add_sum_erase S _ hℓ, ← sub_sub]
    refine (padicNorm.sub).trans (max_le ?_ ?_)
    · have hspec := Padic.principalPart_spec (p := (ℓ : ℕ)) (q : ℚ_[(ℓ : ℕ)])
      rw [← Rat.cast_sub, Padic.eq_padicNorm] at hspec
      exact_mod_cast hspec
    · exact padicNorm.sum_le' (fun p hp ↦ hpart p (Finset.mem_of_mem_erase hp)
        (Finset.ne_of_mem_erase hp)) zero_le_one
  · refine (padicNorm.sub).trans (max_le (padicNorm_le_one_of_mem_sIntegers hq hℓ) ?_)
    exact padicNorm.sum_le' (fun p hp ↦ hpart p hp fun h ↦ hℓ (h ▸ hp)) zero_le_one

/-! ### `S`-units -/

/-- `q` is an **`S`-unit**: a unit of `ℤ[1/N_S]`.  These are exactly `±∏_{p ∈ S} p^{e_p}`
(`e_p ∈ ℤ`); the constructors below cover every consumer (integers supported on `S`, and
quotients of those, such as `3/2` for `S ⊇ {2, 3}`). -/
structure IsSUnit (S : Finset Nat.Primes) (q : ℚ) : Prop where
  ne_zero : q ≠ 0
  mem : q ∈ sIntegers S
  inv_mem : q⁻¹ ∈ sIntegers S

namespace IsSUnit

theorem one : IsSUnit S 1 := ⟨one_ne_zero, Subring.one_mem _, by simp⟩

theorem mul {u v : ℚ} (hu : IsSUnit S u) (hv : IsSUnit S v) : IsSUnit S (u * v) :=
  ⟨mul_ne_zero hu.ne_zero hv.ne_zero, Subring.mul_mem _ hu.mem hv.mem, by
    rw [mul_inv]; exact Subring.mul_mem _ hu.inv_mem hv.inv_mem⟩

theorem inv {u : ℚ} (hu : IsSUnit S u) : IsSUnit S u⁻¹ :=
  ⟨inv_ne_zero hu.ne_zero, hu.inv_mem, by rw [inv_inv]; exact hu.mem⟩

theorem div {u v : ℚ} (hu : IsSUnit S u) (hv : IsSUnit S v) : IsSUnit S (u / v) := by
  rw [div_eq_mul_inv]; exact hu.mul hv.inv

theorem neg {u : ℚ} (hu : IsSUnit S u) : IsSUnit S (-u) :=
  ⟨neg_ne_zero.mpr hu.ne_zero, Subring.neg_mem _ hu.mem, by
    rw [inv_neg]; exact Subring.neg_mem _ hu.inv_mem⟩

theorem pow {u : ℚ} (hu : IsSUnit S u) (n : ℕ) : IsSUnit S (u ^ n) := by
  induction n with
  | zero => simpa using (one : IsSUnit S 1)
  | succ n ih => rw [pow_succ]; exact ih.mul hu

/-- Multiplication by an `S`-unit maps `ℤ[1/N_S]` onto itself. -/
theorem mul_mem_iff {u q : ℚ} (hu : IsSUnit S u) : u * q ∈ sIntegers S ↔ q ∈ sIntegers S :=
  ⟨fun h ↦ by simpa [← mul_assoc, inv_mul_cancel₀ hu.ne_zero] using
    Subring.mul_mem _ hu.inv_mem h, fun h ↦ Subring.mul_mem _ hu.mem h⟩

end IsSUnit

/-- A positive integer all of whose prime factors lie in `S` is an `S`-unit. -/
theorem isSUnit_natCast {b : ℕ} (hb : 0 < b) (h : Nat.primesOf b ⊆ S) : IsSUnit S b where
  ne_zero := by exact_mod_cast hb.ne'
  mem := natCast_mem (sIntegers S) b
  inv_mem := mem_sIntegers_of_forall_padicNorm_le_one fun ℓ hℓ ↦ by
    have hnd : ¬ (ℓ : ℕ) ∣ b := fun hdvd ↦ hℓ (h ((Nat.mem_primesOf_iff_dvd hb.ne').mpr hdvd))
    rw [← one_div, padicNorm.div, (padicNorm.nat_eq_one_iff b).mpr hnd, padicNorm.one, div_one]

/-- Every prime of `S` is an `S`-unit. -/
theorem isSUnit_prime {p : Nat.Primes} (hp : p ∈ S) : IsSUnit S ((p : ℕ) : ℚ) :=
  isSUnit_natCast p.2.pos fun ℓ hℓ ↦ by
    have := (Nat.mem_primesOf_iff_dvd p.2.ne_zero).mp hℓ
    rwa [show ℓ = p from Subtype.ext ((Nat.prime_dvd_prime_iff_eq ℓ.2 p.2).mp this)]

end Rat

/-! ### Examples -/

/-- `3/2` is a `{2,3}`-unit, the multiplier of the `(3/2)ⁿ` program. -/
example : Rat.IsSUnit (Nat.primesOf 6) (3 / 2) :=
  (Rat.isSUnit_natCast (by norm_num) (Nat.primesOf_mono (by norm_num) (by norm_num))).div
    (Rat.isSUnit_natCast (by norm_num) (Nat.primesOf_mono (by norm_num) (by norm_num)))

/-- `12` acts on the `6`-adic solenoid: only the radical of the base matters. -/
example : Rat.IsSUnit (Nat.primesOf 6) 12 := by
  have h : Nat.primesOf 12 ⊆ Nat.primesOf 6 := fun ℓ hℓ ↦ by
    rw [Nat.mem_primesOf_iff_dvd (by norm_num)] at hℓ ⊢
    have h3 : (ℓ : ℕ) ∣ 2 ^ 2 * 3 := hℓ
    rcases (Nat.Prime.dvd_mul ℓ.2).mp h3 with h2 | h3
    · exact (ℓ.2.dvd_of_dvd_pow h2).mul_right 3
    · exact h3.mul_left 2
  exact_mod_cast Rat.isSUnit_natCast (b := 12) (by norm_num) h

/-- `5 ∉ S` is visible: `1/5` is not a `{2,3}`-integer. -/
example : (1 / 5 : ℚ) ∉ Rat.sIntegers (Nat.primesOf 6) := by
  intro h
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h5 : (⟨5, Nat.prime_five⟩ : Nat.Primes) ∉ Nat.primesOf 6 := fun hm ↦ by
    have := (Nat.mem_primesOf_iff_dvd (n := 6) (by norm_num)).mp hm
    norm_num at this
  have := Rat.padicNorm_le_one_of_mem_sIntegers h h5
  have hval : padicNorm 5 (1 / 5 : ℚ) = 5 := by
    rw [padicNorm.div, padicNorm.one]
    have := padicNorm.padicNorm_p_of_prime (p := 5)
    push_cast at this ⊢
    rw [this]; norm_num
  change padicNorm 5 (1 / 5 : ℚ) ≤ 1 at this
  rw [hval] at this
  norm_num at this
