/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Int.Basic
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Tactic.LinearCombination
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The Jacobsthal function and the elementary sieve bound ([Oda26] §8.4)

For a finite set `S` of primes, the number of integers in a window `[a, b)` divisible by no prime
of `S` differs from `(b − a)·∏_{l∈S}(1 − 1/l)` by at most `2^{|S|} − 1`.  Hence a window of `3^k`
consecutive integers always contains one prime to `k` given odd primes.

* `Oda.sieveCount_bound` — the sieve bound (by induction on `S`, both sides at once).
* `Oda.exists_avoids` — every `3^k` consecutive integers contain one prime to `k` odd primes.
* `Oda.jacobsthal` — the Jacobsthal function `J(N)`: the least `J` such that every `J` consecutive
  integers contain one prime to `N`.
* `Oda.jacobsthal_prod_le` — **[Oda26] Theorem 44, second part:** `J(N) ≤ 3^{ω(N)}` for odd
  squarefree `N`.
* `Oda.jacobsthal_prime`, `Oda.jacobsthal_mul_primes` — `J(p) = 2`, and `J(pq) = 3` for distinct
  odd primes (used in [Oda26] Corollary 45).
* `Oda.two_pow_mul_factorial_le_prod` — `k` distinct odd numbers `≥ 3` have product `≥ 2^k k!`
  (the second inequality of (30)).

## References

* [Oda26] Y. Odagiri, *Finite graph certificates for composite terms in rational floor sequences*,
  Zenodo, doi:10.5281/zenodo.22997709 (2026).
-/

namespace Oda

open Finset

/-- `x` is divisible by no element of `S`. -/
def Avoids (S : Finset ℕ) (x : ℤ) : Prop := ∀ l ∈ S, ¬ (l : ℤ) ∣ x

instance (S : Finset ℕ) : DecidablePred (Avoids S) := fun x => by unfold Avoids; infer_instance

/-- The number of `x ∈ [a, b)` divisible by no element of `S`. -/
def sieveCount (S : Finset ℕ) (a b : ℤ) : ℕ := ((Ico a b).filter (Avoids S)).card

/-- The density `∏_{l ∈ S} (1 − 1/l)`. -/
noncomputable def sieveDensity (S : Finset ℕ) : ℝ := ∏ l ∈ S, (1 - 1 / (l : ℝ))

theorem sieveDensity_nonneg (S : Finset ℕ) (hS : ∀ l ∈ S, 1 ≤ l) : 0 ≤ sieveDensity S := by
  refine prod_nonneg fun l hl => ?_
  have : (1 : ℝ) ≤ l := by exact_mod_cast hS l hl
  have : 1 / (l : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact this
  linarith

theorem sieveDensity_le_one (S : Finset ℕ) (hS : ∀ l ∈ S, 1 ≤ l) : sieveDensity S ≤ 1 := by
  refine prod_le_one (fun l hl => ?_) fun l hl => ?_
  · have : (1 : ℝ) ≤ l := by exact_mod_cast hS l hl
    have : 1 / (l : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact this
    linarith
  · have : 0 ≤ 1 / (l : ℝ) := by positivity
    linarith

/-- The ceiling `⌈a/p⌉`. -/
def cdiv (a : ℤ) (p : ℕ) : ℤ := (a + p - 1) / p

theorem cdiv_le_iff {p : ℕ} (hp : 0 < p) (a y : ℤ) : cdiv a p ≤ y ↔ a ≤ p * y := by
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  unfold cdiv
  rw [← not_lt, Int.lt_iff_add_one_le, Int.le_ediv_iff_mul_le hp', not_le]
  constructor <;> intro h <;> nlinarith

theorem lt_cdiv_iff {p : ℕ} (hp : 0 < p) (a y : ℤ) : y < cdiv a p ↔ p * y < a := by
  rw [← not_le, cdiv_le_iff hp, not_le]

theorem le_mul_cdiv {p : ℕ} (hp : 0 < p) (a : ℤ) : a ≤ p * cdiv a p :=
  (cdiv_le_iff hp a _).1 le_rfl

theorem mul_cdiv_sub_lt {p : ℕ} (hp : 0 < p) (a : ℤ) : p * cdiv a p - p < a := by
  have := (lt_cdiv_iff hp a (cdiv a p - 1)).1 (by omega)
  linarith

/-- One sieving step: removing the multiples of a new prime `p`. -/
theorem sieveCount_insert {S : Finset ℕ} {p : ℕ} (hp : p.Prime) (hpS : p ∉ S)
    (hS : ∀ l ∈ S, l.Prime) (a b : ℤ) :
    sieveCount S a b = sieveCount (insert p S) a b + sieveCount S (cdiv a p) (cdiv b p) := by
  have hp0 : 0 < p := hp.pos
  have h := card_filter_add_card_filter_not (s := (Ico a b).filter (Avoids S))
    (fun x => (p : ℤ) ∣ x)
  have hneg : ((Ico a b).filter (Avoids S)).filter (fun x => ¬ (p : ℤ) ∣ x) =
      (Ico a b).filter (Avoids (insert p S)) := by
    ext x
    simp only [mem_filter, Avoids, forall_mem_insert]
    tauto
  have hpos : ((Ico a b).filter (Avoids S)).filter (fun x => (p : ℤ) ∣ x) =
      ((Ico (cdiv a p) (cdiv b p)).filter (Avoids S)).image (fun y => (p : ℤ) * y) := by
    ext x
    simp only [mem_filter, mem_Ico, mem_image, Avoids]
    constructor
    · rintro ⟨⟨⟨hax, hxb⟩, hav⟩, y, rfl⟩
      refine ⟨y, ⟨⟨(cdiv_le_iff hp0 _ _).2 hax, (lt_cdiv_iff hp0 _ _).2 hxb⟩, fun l hl hly => ?_⟩,
        rfl⟩
      exact hav l hl (dvd_mul_of_dvd_right hly _)
    · rintro ⟨y, ⟨⟨h1, h2⟩, hav⟩, rfl⟩
      refine ⟨⟨⟨(cdiv_le_iff hp0 _ _).1 h1, (lt_cdiv_iff hp0 _ _).1 h2⟩, fun l hl hly => ?_⟩,
        dvd_mul_right _ _⟩
      rcases (Nat.prime_iff_prime_int.mp (hS l hl)).dvd_or_dvd hly with h | h
      · have : l = p := (Nat.prime_dvd_prime_iff_eq (hS l hl) hp).1 (Int.natCast_dvd_natCast.1 h)
        exact hpS (this ▸ hl)
      · exact hav l hl h
  have hinj : Function.Injective (fun y : ℤ => (p : ℤ) * y) :=
    mul_right_injective₀ (by exact_mod_cast hp.ne_zero)
  rw [hneg, hpos, card_image_of_injective _ hinj] at h
  unfold sieveCount
  omega

/-- **The sieve bound.**  For a finite set `S` of primes and `a ≤ b`,
`|#{x ∈ [a,b) : no l ∈ S divides x} − (b−a)·∏_{l∈S}(1−1/l)| ≤ 2^{|S|} − 1`. -/
theorem sieveCount_bound (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime) :
    ∀ a b : ℤ, a ≤ b →
      |(sieveCount S a b : ℝ) - ((b - a : ℤ) : ℝ) * sieveDensity S| ≤ 2 ^ S.card - 1 := by
  induction S using Finset.induction_on with
  | empty =>
    intro a b hab
    have : sieveCount ∅ a b = (b - a).toNat := by
      unfold sieveCount
      rw [filter_true_of_mem (fun x _ => by simp [Avoids]), Int.card_Ico]
    rw [this, sieveDensity, prod_empty]
    have : (((b - a).toNat : ℕ) : ℝ) = ((b - a : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    rw [this]; simp
  | @insert p S hpS ih =>
    intro a b hab
    have hpP : p.Prime := hS p (mem_insert_self _ _)
    have hS' : ∀ l ∈ S, l.Prime := fun l hl => hS l (mem_insert_of_mem hl)
    have hp0 : 0 < p := hpP.pos
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
    set t := cdiv a p
    set u := cdiv b p
    have ht1 := le_mul_cdiv hp0 a
    have ht2 := mul_cdiv_sub_lt hp0 a
    have hu1 := le_mul_cdiv hp0 b
    have hu2 := mul_cdiv_sub_lt hp0 b
    have htu : t ≤ u := (cdiv_le_iff hp0 _ _).2 (by linarith)
    have hX := ih hS' a b hab
    have hY := ih hS' t u htu
    have hsplit := sieveCount_insert hpP hpS hS' a b
    have hδ0 := sieveDensity_nonneg S fun l hl => (hS' l hl).one_lt.le
    have hδ1 := sieveDensity_le_one S fun l hl => (hS' l hl).one_lt.le
    rw [sieveDensity, prod_insert hpS, ← sieveDensity, card_insert_of_notMem hpS, pow_succ]
    -- the error of the new window length
    set e : ℝ := ((u - t : ℤ) : ℝ) - ((b - a : ℤ) : ℝ) / p with he
    have he1 : -1 ≤ e ∧ e ≤ 1 := by
      have k1 : ((p * t - p : ℤ) : ℝ) < a := by exact_mod_cast ht2
      have k2 : (a : ℝ) ≤ ((p * t : ℤ) : ℝ) := by exact_mod_cast ht1
      have k3 : ((p * u - p : ℤ) : ℝ) < b := by exact_mod_cast hu2
      have k4 : (b : ℝ) ≤ ((p * u : ℤ) : ℝ) := by exact_mod_cast hu1
      push_cast at k1 k2 k3 k4 ⊢
      rw [he]; push_cast
      have m1 : ((b : ℝ) - a) / p ≤ (u - t) + 1 := by rw [div_le_iff₀ hpR]; nlinarith
      have m2 : (u : ℝ) - t - 1 ≤ ((b : ℝ) - a) / p := by rw [le_div_iff₀ hpR]; nlinarith
      constructor <;> linarith
    have hed : -1 ≤ e * sieveDensity S ∧ e * sieveDensity S ≤ 1 := by
      constructor <;> nlinarith
    have hcast : (sieveCount (insert p S) a b : ℝ) =
        (sieveCount S a b : ℝ) - (sieveCount S t u : ℝ) := by
      rw [hsplit]; push_cast; ring
    have hid : (sieveCount (insert p S) a b : ℝ) -
        ((b - a : ℤ) : ℝ) * ((1 - 1 / (p : ℝ)) * sieveDensity S) =
        ((sieveCount S a b : ℝ) - ((b - a : ℤ) : ℝ) * sieveDensity S) -
        ((sieveCount S t u : ℝ) - ((u - t : ℤ) : ℝ) * sieveDensity S) - e * sieveDensity S := by
      rw [hcast, he]; field_simp; ring
    rw [hid]
    rw [abs_le] at hX hY ⊢
    constructor <;> linarith [hX.1, hX.2, hY.1, hY.2, hed.1, hed.2]

/-- **Every `3^k` consecutive integers contain one prime to `k` given odd primes.** -/
theorem exists_avoids (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime ∧ l ≠ 2) (a : ℤ) {H : ℕ}
    (hH : 3 ^ S.card ≤ H) : ∃ x ∈ Ico a (a + H), Avoids S x := by
  have hb := sieveCount_bound S (fun l hl => (hS l hl).1) a (a + H) (by omega)
  have hδ : (2 / 3 : ℝ) ^ S.card ≤ sieveDensity S := by
    rw [sieveDensity, ← prod_const]
    refine prod_le_prod (fun _ _ => by norm_num) fun l hl => ?_
    have h3 : 3 ≤ l := by
      have := (hS l hl).1.two_le
      have := (hS l hl).2
      omega
    have : (3 : ℝ) ≤ l := by exact_mod_cast h3
    have : 1 / (l : ℝ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) this
    linarith
  have hH' : ((3 : ℝ)) ^ S.card ≤ H := by exact_mod_cast hH
  have hlen : ((a + H - a : ℤ) : ℝ) = H := by push_cast; ring
  rw [hlen, abs_le] at hb
  have h32 : (3 : ℝ) ^ S.card * (2 / 3) ^ S.card = 2 ^ S.card := by
    rw [← mul_pow]; norm_num
  have hpos : (0 : ℝ) < sieveCount S a (a + H) := by
    have h1 : (3 : ℝ) ^ S.card * (2 / 3) ^ S.card ≤ (H : ℝ) * sieveDensity S :=
      mul_le_mul hH' hδ (by positivity) (by positivity)
    linarith [hb.1]
  have : 0 < sieveCount S a (a + H) := by exact_mod_cast hpos
  obtain ⟨x, hx⟩ := card_pos.1 this
  rw [mem_filter] at hx
  exact ⟨x, hx.1, hx.2⟩

/-! ## The Jacobsthal function -/

/-- **The Jacobsthal function** `J(N)`: the least `J` such that every `J` consecutive integers
contain one prime to `N`. -/
noncomputable def jacobsthal (N : ℕ) : ℕ :=
  sInf {J : ℕ | ∀ s : ℤ, ∃ x ∈ Ico s (s + J), IsCoprime x (N : ℤ)}

theorem jacobsthal_set_nonempty {N : ℕ} (hN : 0 < N) :
    ∀ s : ℤ, ∃ x ∈ Ico s (s + N), IsCoprime x (N : ℤ) := by
  intro s
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  refine ⟨s + (1 - s) % N, ?_, ?_⟩
  · have := Int.emod_nonneg (1 - s) hN'.ne'
    have := Int.emod_lt_of_pos (1 - s) hN'
    rw [mem_Ico]; omega
  · refine ⟨1, (1 - s) / N, ?_⟩
    have := Int.emod_def (1 - s) N
    linear_combination this

theorem jacobsthal_spec {N : ℕ} (hN : 0 < N) (s : ℤ) :
    ∃ x ∈ Ico s (s + jacobsthal N), IsCoprime x (N : ℤ) :=
  Nat.sInf_mem (s := {J : ℕ | ∀ s : ℤ, ∃ x ∈ Ico s (s + J), IsCoprime x (N : ℤ)})
    ⟨N, jacobsthal_set_nonempty hN⟩ s

theorem jacobsthal_le {N J : ℕ} (h : ∀ s : ℤ, ∃ x ∈ Ico s (s + J), IsCoprime x (N : ℤ)) :
    jacobsthal N ≤ J :=
  Nat.sInf_le h

theorem lt_jacobsthal {N J : ℕ} (hN : 0 < N) (s : ℤ)
    (h : ∀ x ∈ Ico s (s + J), ¬ IsCoprime x (N : ℤ)) : J < jacobsthal N := by
  by_contra hle
  obtain ⟨x, hx, hco⟩ := jacobsthal_spec hN s
  rw [mem_Ico] at hx
  exact h x (by rw [mem_Ico]; omega) hco

/-- Coprimality to a product of primes is avoiding each of them. -/
theorem isCoprime_prod_iff {T : Finset ℕ} (hT : ∀ l ∈ T, l.Prime) (x : ℤ) :
    IsCoprime x ((∏ l ∈ T, l : ℕ) : ℤ) ↔ Avoids T x := by
  rw [Nat.cast_prod, IsCoprime.prod_right_iff]
  refine forall₂_congr fun l hl => ?_
  rw [isCoprime_comm]
  exact (Nat.prime_iff_prime_int.mp (hT l hl)).irreducible.coprime_iff_not_dvd

/-- **[Oda26] Theorem 44, Jacobsthal bound:** `J(N) ≤ 3^{ω(N)}` for odd squarefree `N`, written as
the product of a finite set of odd primes. -/
@[category research solved, AMS 11, ref "Oda26", group "oda26_budget"]
theorem jacobsthal_prod_le {T : Finset ℕ} (hT : ∀ l ∈ T, l.Prime ∧ l ≠ 2) :
    jacobsthal (∏ l ∈ T, l) ≤ 3 ^ T.card := by
  refine jacobsthal_le fun s => ?_
  obtain ⟨x, hx, hav⟩ := exists_avoids T hT s le_rfl
  exact ⟨x, hx, (isCoprime_prod_iff (fun l hl => (hT l hl).1) x).2 hav⟩

/-- `J(p) = 2` for a prime `p`. -/
@[category research solved, AMS 11, ref "Oda26", group "oda26_budget"]
theorem jacobsthal_prime {p : ℕ} (hp : p.Prime) : jacobsthal p = 2 := by
  have hirr := (Nat.prime_iff_prime_int.mp hp).irreducible
  refine le_antisymm (jacobsthal_le fun s => ?_) ?_
  · by_cases hs : (p : ℤ) ∣ s
    · refine ⟨s + 1, by rw [mem_Ico]; omega, ?_⟩
      rw [isCoprime_comm, hirr.coprime_iff_not_dvd]
      intro h
      have h1 : (p : ℤ) ∣ 1 := by have := dvd_sub h hs; simpa using this
      have := Int.le_of_dvd one_pos h1
      have := hp.two_le
      omega
    · exact ⟨s, by rw [mem_Ico]; omega, by rw [isCoprime_comm, hirr.coprime_iff_not_dvd]; exact hs⟩
  · refine Nat.succ_le_of_lt (lt_jacobsthal hp.pos 0 fun x hx => ?_)
    rw [mem_Ico] at hx
    obtain rfl : x = 0 := by omega
    rw [isCoprime_comm, hirr.coprime_iff_not_dvd]
    simp

/-- `J(pq) = 3` for distinct odd primes `p, q`. -/
@[category research solved, AMS 11, ref "Oda26", group "oda26_budget"]
theorem jacobsthal_mul_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hpq : p ≠ q) : jacobsthal (p * q) = 3 := by
  have hT : ∀ l ∈ ({p, q} : Finset ℕ), l.Prime ∧ l ≠ 2 := by
    intro l hl
    rcases mem_insert.1 hl with rfl | hl
    · exact ⟨hp, hp2⟩
    · rw [mem_singleton] at hl; subst hl; exact ⟨hq, hq2⟩
  have hprod : ∏ l ∈ ({p, q} : Finset ℕ), l = p * q := prod_pair hpq
  refine le_antisymm ?_ ?_
  · refine jacobsthal_le fun s => ?_
    have hge : ∀ l ∈ ({p, q} : Finset ℕ), 3 ≤ l := fun l hl => by
      have := (hT l hl).1.two_le; have := (hT l hl).2; omega
    have sep : ∀ l ∈ ({p, q} : Finset ℕ), ∀ x y : ℤ, (l : ℤ) ∣ x → (l : ℤ) ∣ y → x < y →
        y ≤ x + 2 → False := by
      intro l hl x y hx hy hxy hyx
      have h := Int.le_of_dvd (by omega) (dvd_sub hy hx)
      have := hge l hl
      omega
    have key : ∃ x ∈ Ico s (s + 3), Avoids {p, q} x := by
      by_contra h
      have hw : ∀ x : ℤ, s ≤ x → x < s + 3 → ∃ l ∈ ({p, q} : Finset ℕ), (l : ℤ) ∣ x := by
        intro x h1 h2
        by_contra h'
        exact h ⟨x, by rw [mem_Ico]; omega, fun l hl hd => h' ⟨l, hl, hd⟩⟩
      obtain ⟨l0, hl0, d0⟩ := hw s le_rfl (by omega)
      obtain ⟨l1, hl1, d1⟩ := hw (s + 1) (by omega) (by omega)
      obtain ⟨l2, hl2, d2⟩ := hw (s + 2) (by omega) (by omega)
      have e0 := mem_insert.1 hl0; have e1 := mem_insert.1 hl1; have e2 := mem_insert.1 hl2
      rw [mem_singleton] at e0 e1 e2
      rcases e0 with rfl | rfl <;> rcases e1 with h1 | h1 <;> rcases e2 with h2 | h2 <;>
        subst h1 <;> subst h2 <;>
        first
        | exact sep _ hl0 _ _ d0 d1 (by omega) (by omega)
        | exact sep _ hl0 _ _ d0 d2 (by omega) (by omega)
        | exact sep _ hl1 _ _ d1 d2 (by omega) (by omega)
    obtain ⟨x, hx, hav⟩ := key
    refine ⟨x, by simpa using hx, ?_⟩
    rw [← hprod]
    exact (isCoprime_prod_iff (fun l hl => (hT l hl).1) x).2 hav
  · -- `x ≡ 0 (mod p)`, `x ≡ 1 (mod q)`: the window `{x−1, x}` has no element prime to `pq`
    have hco : IsCoprime (p : ℤ) (q : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hpq)
    obtain ⟨u, v, huv⟩ := hco
    have hpos : 0 < p * q := Nat.mul_pos hp.pos hq.pos
    refine Nat.succ_le_of_lt (lt_jacobsthal hpos (u * p - 1) fun x hx => ?_)
    rw [← hprod, isCoprime_prod_iff (fun l hl => (hT l hl).1)]
    rw [mem_Ico] at hx
    intro hav
    rcases (show x = u * p - 1 ∨ x = u * p by omega) with rfl | rfl
    · exact hav q (by simp) ⟨-v, by linear_combination huv⟩
    · exact hav p (by simp) ⟨u, by ring⟩

/-- `k` distinct odd numbers `≥ 3` have product at least `2^k·k!`. -/
theorem two_pow_mul_factorial_le_prod (T : Finset ℕ) (hT : ∀ l ∈ T, l % 2 = 1 ∧ 3 ≤ l) :
    2 ^ T.card * T.card.factorial ≤ ∏ l ∈ T, l := by
  induction T using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have ha := hT a (mem_insert_self _ _)
    have ih' := ih fun l hl => hT l (mem_insert_of_mem hl)
    -- the elements of `s` are odd numbers in `[3, a)`
    have hcard : s.card ≤ (a - 3) / 2 := by
      have := card_le_card_of_injOn (fun x => (x - 3) / 2) (t := range ((a - 3) / 2))
        (fun x hx => by
          have := hT x (mem_insert_of_mem hx)
          have := hlt x hx
          simp only [coe_range, Set.mem_Iio]
          omega)
        (fun x hx y hy hxy => by
          have := hT x (mem_insert_of_mem hx)
          have := hT y (mem_insert_of_mem hy)
          simp only at hxy
          omega)
      simpa using this
    rw [prod_insert has, card_insert_of_notMem has, pow_succ, Nat.factorial_succ]
    have h2 : 2 * (s.card + 1) ≤ a := by omega
    calc 2 ^ s.card * 2 * ((s.card + 1) * s.card.factorial)
        = (2 * (s.card + 1)) * (2 ^ s.card * s.card.factorial) := by ring
      _ ≤ a * ∏ l ∈ s, l := Nat.mul_le_mul h2 ih'

end Oda
