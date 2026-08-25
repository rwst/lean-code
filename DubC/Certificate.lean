/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC.DigitRecurrence

/-!
# The zero-entropy certificate `C(𝒫)` and what it proves

This file formalises the **certificate route** of `plans/plan-dubC1.html` §0-ter, milestone
M1′: a single *finite, decidable* check on residues modulo `M = ∏_{p∈𝒫} p` that, if it
passes, settles the 1967 Forman–Shapiro problem for the base `a`.

## The subshift

If every term of `⌊ξaⁿ⌋` is prime and the terms exceed `M`, then every term is coprime to `M`,
so the residues `rₙ = ⌊ξaⁿ⌋ mod M` form an infinite path in the digraph on the units of
`ZMod M` with edges `r → a·r + d`, `d ∈ {0,…,a-1}`, target a unit (`DubC.Step`).

## The certificate

`DubC.CertOK a M rank` asks for a **rank function** `rank : ZMod M → ℕ` such that along every
admissible edge the rank does not increase, and every unit has at most **one** rank-preserving
admissible successor.

*This is exactly the combinatorial certificate `C(𝒫)` of the plan* — "no strongly connected
component contains two distinct cycles".  Taking `rank r` to be the height of `r`'s SCC in the
condensation DAG, the first condition is automatic (edges leave an SCC downwards, edges inside
an SCC preserve height) and the second says precisely that no state has two outgoing edges
*inside its own SCC*, i.e. that every cyclic SCC is a simple cycle, i.e. that the core has
spectral radius `1` and topological entropy `0`.  Conversely such a `rank` exists whenever
`C(𝒫)` holds, so nothing is lost by taking the rank form as the definition — and the rank form
is the one a proof assistant can check by `decide`, with no graph algorithms in the kernel.

## What it proves

`DubC.eventually_periodic_of_rank` — the abstract engine: rank non-increasing plus unique
rank-preserving successor forces every infinite path in a finite state space to be eventually
periodic.  (Non-increasing ℕ-valued potential ⇒ eventually constant ⇒ from there the path is
deterministic ⇒ a deterministic orbit of a finite set is eventually periodic.)

`DubC.infinite_composites_floorPow_of_certOK` — the payoff: if `CertOK a M rank` holds for one
finite `M` with `a ≤ M`, then for **every** real `ξ > 0` the sequence `⌊ξaⁿ⌋` contains
infinitely many composite terms.  The chain is

  all terms prime  ⇒  all residues are units  ⇒  the residue path is admissible
    ⇒  (certificate) the residue path is eventually periodic
    ⇒  the digit word is eventually periodic          (digits are read off mod `M`, and
                                                       `0 ≤ d < a ≤ M` pins them down)
    ⇒  a `d = 1` return recurrence along a progression  (`DigitRecurrence.lean`)
    ⇒  infinitely many composites                      ([Dub09] Thm 4, `ReturnEngine.lean`)

contradicting "all terms prime".  Note the chain never asserts that the avoiding `ξ` is
rational: eventual periodicity of the *digit word* is used directly, which is strictly less
than rationality-plus-conversion and avoids any series summation.

Instances live in `DubC/Verdict.lean`.

## References

* **[Dub09]** A. Dubickas, *Prime and composite integers close to powers of a number*,
  Monatsh. Math. **158** (2009) 271–284.
* **[DubOst06]** A. Dubickas, *Truncatable primes and unavoidable sets of divisors*,
  Acta Math. Univ. Ostrav. **14** (2006) 21–25.
-/

namespace DubC

open Filter

/-! ### The abstract certificate: rank ⇒ eventual periodicity -/

/-- **Zero-entropy certificate ⇒ every infinite path is eventually periodic.**

`rank` never increases along an admissible transition (`hle`) and each state has at most one
admissible rank-preserving successor (`huniq`).  Then along an infinite admissible path the
rank is non-increasing, hence eventually constant; beyond that point the path is *forced*, and
a deterministic orbit in a finite state space is eventually periodic. -/
@[category research solved, AMS 11 37, ref "Dub09" "DubOst06", group "dubc_certificate"]
theorem eventually_periodic_of_rank {S : Type*} [Finite S] {adm : S → S → Prop}
    (rank : S → ℕ)
    (hle : ∀ s t, adm s t → rank t ≤ rank s)
    (huniq : ∀ s t u, adm s t → adm s u → rank t = rank s → rank u = rank s → t = u)
    (s : ℕ → S) (hs : ∀ n, adm (s n) (s (n + 1))) :
    ∃ n₀ L, 0 < L ∧ ∀ m, n₀ ≤ m → s (m + L) = s m := by
  -- the potential is antitone along the path
  have hanti : ∀ p q : ℕ, p ≤ q → rank (s q) ≤ rank (s p) := by
    intro p q hpq
    induction q, hpq using Nat.le_induction with
    | base => exact le_refl _
    | succ q hpq ih => exact le_trans (hle _ _ (hs q)) ih
  -- hence eventually constant, namely at the infimum of its range
  obtain ⟨n₁, hn₁⟩ : ∃ n₁, ∀ m, n₁ ≤ m → rank (s m) = rank (s n₁) := by
    have hne : (Set.range fun n => rank (s n)).Nonempty := ⟨rank (s 0), 0, rfl⟩
    obtain ⟨n₁, hn₁⟩ := Nat.sInf_mem hne
    refine ⟨n₁, fun m hm => le_antisymm (hanti _ _ hm) ?_⟩
    have hinf : rank (s n₁) = sInf (Set.range fun n => rank (s n)) := hn₁
    rw [hinf]
    exact Nat.sInf_le ⟨m, rfl⟩
  -- beyond `n₁` the path is deterministic, so a repetition propagates forever
  have main : ∀ p q : ℕ, n₁ ≤ p → p < q → s p = s q →
      ∃ n₀ L, 0 < L ∧ ∀ m, n₀ ≤ m → s (m + L) = s m := by
    intro p q hnp hpq heq
    obtain ⟨L, hL, rfl⟩ : ∃ L, 0 < L ∧ q = p + L := ⟨q - p, by omega, by omega⟩
    refine ⟨p, L, hL, ?_⟩
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact heq.symm
    | succ m hpm ih =>
      have hadm2 : adm (s m) (s (m + L + 1)) := by rw [← ih]; exact hs (m + L)
      have hr1 : rank (s (m + 1)) = rank (s m) := by
        rw [hn₁ (m + 1) (by omega), hn₁ m (by omega)]
      have hr2 : rank (s (m + L + 1)) = rank (s m) := by
        rw [hn₁ (m + L + 1) (by omega), hn₁ m (by omega)]
      have huq := huniq (s m) (s (m + 1)) (s (m + L + 1)) (hs m) hadm2 hr1 hr2
      have hidx : m + 1 + L = m + L + 1 := by omega
      rw [hidx, ← huq]
  -- pigeonhole supplies the repetition
  obtain ⟨j₁, j₂, hjne, hjeq⟩ := Finite.exists_ne_map_eq_of_infinite fun j : ℕ => s (n₁ + j)
  rcases lt_trichotomy j₁ j₂ with h | h | h
  · exact main (n₁ + j₁) (n₁ + j₂) (by omega) (by omega) hjeq
  · exact absurd h hjne
  · exact main (n₁ + j₂) (n₁ + j₁) (by omega) (by omega) hjeq.symm

/-! ### The base-`a` coprimality subshift modulo `M` -/

/-- Being a unit of `ZMod M`, in the decidable `gcd` form that `decide` can run. -/
def Cop (M : ℕ) (r : ZMod M) : Prop := Nat.Coprime r.val M

instance (M : ℕ) (r : ZMod M) : Decidable (Cop M r) := by unfold Cop; infer_instance

@[category API, AMS 11 37, ref "Dub09", group "dubc_certificate"]
theorem cop_iff_isUnit {M : ℕ} [NeZero M] (r : ZMod M) : Cop M r ↔ IsUnit r := by
  have h : ((r.val : ℕ) : ZMod M) = r := by simp
  rw [Cop, ← ZMod.isUnit_iff_coprime r.val M, h]

/-- One step of the base-`a` coprimality subshift modulo `M`: append a digit `d < a` to a unit
and land on a unit. -/
def Step (a M : ℕ) (r t : ZMod M) : Prop :=
  Cop M r ∧ Cop M t ∧ ∃ d : ℕ, d < a ∧ t = (a : ZMod M) * r + (d : ZMod M)

/-- The certificate **`C(𝒫)`** in the shape `decide` can check: a rank function on residues
mod `M` that never increases along an admissible step, and leaves at most one rank-preserving
admissible successor at each unit.  (Quantifying over digits rather than over target states
keeps the check `O(M · a²)`.) -/
def CertOK (a M : ℕ) (rank : ZMod M → ℕ) : Prop :=
  ∀ r : ZMod M, Cop M r → ∀ d₁ < a, ∀ d₂ < a,
    (Cop M ((a : ZMod M) * r + (d₁ : ZMod M)) →
        rank ((a : ZMod M) * r + (d₁ : ZMod M)) ≤ rank r) ∧
      (Cop M ((a : ZMod M) * r + (d₁ : ZMod M)) → Cop M ((a : ZMod M) * r + (d₂ : ZMod M)) →
        rank ((a : ZMod M) * r + (d₁ : ZMod M)) = rank r →
        rank ((a : ZMod M) * r + (d₂ : ZMod M)) = rank r →
        (a : ZMod M) * r + (d₁ : ZMod M) = (a : ZMod M) * r + (d₂ : ZMod M))

-- The unfolded `CertOK` is a deep nest of bounded quantifiers; instance search needs room.
set_option synthInstance.maxSize 1000
set_option synthInstance.maxHeartbeats 1000000

/-- `CertOK` is a finite check, so `decide` can run it — this instance is what makes the
kernel-checked base instances of `DubC/Verdict.lean` possible. -/
instance (a M : ℕ) [NeZero M] (rank : ZMod M → ℕ) : Decidable (CertOK a M rank) := by
  unfold CertOK
  infer_instance

@[category API, AMS 11 37, ref "Dub09", group "dubc_certificate"]
theorem rank_le_of_certOK {a M : ℕ} {rank : ZMod M → ℕ} (hcert : CertOK a M rank) :
    ∀ r t : ZMod M, Step a M r t → rank t ≤ rank r := by
  rintro r t ⟨hr, ht, d, hd, rfl⟩
  exact ((hcert r hr d hd d hd).1) ht

@[category API, AMS 11 37, ref "Dub09", group "dubc_certificate"]
theorem unique_of_certOK {a M : ℕ} {rank : ZMod M → ℕ} (hcert : CertOK a M rank) :
    ∀ r t u : ZMod M, Step a M r t → Step a M r u →
      rank t = rank r → rank u = rank r → t = u := by
  rintro r t u ⟨hr, ht, d₁, hd₁, rfl⟩ ⟨-, hu, d₂, hd₂, rfl⟩ h1 h2
  exact ((hcert r hr d₁ hd₁ d₂ hd₂).2) ht hu h1 h2

/-! ### Plumbing shared by every certificate form

Three lemmas that mention no certificate at all: the residue path of a base-`a` expansion is
admissible, digits are pinned down by residues, and an eventually periodic digit word
contradicts "only finitely many composites".  A certificate form then has to supply only one
thing — eventual periodicity of the residue path.  `DubC/CoreCertificate.lean` supplies it a
second way. -/

/-- If the residues of `⌊ξaⁿ⌋` modulo `M` are units from `N` on, the shifted residue sequence
is an infinite admissible path of the base-`a` coprimality subshift. -/
@[category API, AMS 11 37, ref "Dub09", group "dubc_certificate"]
theorem step_floorPow {a M : ℕ} [NeZero M] (ha : 0 < a) {ξ : ℝ} {N : ℕ}
    (hunit : ∀ n, N ≤ n → Cop M ((floorPow ξ a n : ZMod M))) (j : ℕ) :
    Step a M ((floorPow ξ a (N + j) : ZMod M)) ((floorPow ξ a (N + (j + 1)) : ZMod M)) := by
  have hnn := floorDigit_nonneg ξ a (N + j)
  refine ⟨hunit _ (by omega), hunit _ (by omega), (floorDigit ξ a (N + j)).toNat, ?_, ?_⟩
  · have h2 := floorDigit_lt ξ ha (N + j)
    omega
  · have hcast : (((floorDigit ξ a (N + j)).toNat : ℕ) : ZMod M)
        = ((floorDigit ξ a (N + j) : ℤ) : ZMod M) := by
      rw [← Int.cast_natCast (R := ZMod M), Int.toNat_of_nonneg hnn]
    rw [hcast]
    have hidx : N + (j + 1) = (N + j) + 1 := by omega
    rw [hidx, floorPow_succ ξ a (N + j)]
    push_cast
    ring

/-- **Digits are determined by residues.**  If the residues of `⌊ξaⁿ⌋` modulo `M` are
`L`-periodic from `n₁` on and `a ≤ M`, then so is the digit word: two digits congruent mod `M`
and both in `[0, a) ⊆ [0, M)` are equal. -/
@[category API, AMS 11 37, ref "Dub09", group "dubc_certificate"]
theorem digits_periodic_of_residues_periodic {a M : ℕ} (ha : 2 ≤ a) (haM : a ≤ M) [NeZero M]
    {ξ : ℝ} {n₁ L : ℕ}
    (hres : ∀ p, n₁ ≤ p → ((floorPow ξ a (p + L) : ZMod M)) = ((floorPow ξ a p : ZMod M))) :
    ∀ m, n₁ ≤ m → floorDigit ξ a (m + L) = floorDigit ξ a m := by
  have key : ∀ p : ℕ, ((floorDigit ξ a p : ℤ) : ZMod M)
      = ((floorPow ξ a (p + 1) : ℤ) : ZMod M)
        - (a : ZMod M) * ((floorPow ξ a p : ℤ) : ZMod M) := by
    intro p
    have h : ((floorPow ξ a (p + 1) : ℤ) : ZMod M)
        = (a : ZMod M) * ((floorPow ξ a p : ℤ) : ZMod M)
          + ((floorDigit ξ a p : ℤ) : ZMod M) := by
      rw [floorPow_succ ξ a p]; push_cast; ring
    rw [h]; ring
  intro m hm
  have hd : ((floorDigit ξ a (m + L) : ℤ) : ZMod M) = ((floorDigit ξ a m : ℤ) : ZMod M) := by
    rw [key (m + L), key m]
    have e1 : m + L + 1 = (m + 1) + L := by omega
    rw [e1, hres (m + 1) (by omega), hres m (by omega)]
  have hdvd : ((M : ℤ)) ∣ (floorDigit ξ a (m + L) - floorDigit ξ a m) := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ?_
    push_cast
    rw [hd, sub_self]
  have hb1 := floorDigit_nonneg ξ a (m + L)
  have hb2 := floorDigit_lt ξ (show 0 < a by omega) (m + L)
  have hb3 := floorDigit_nonneg ξ a m
  have hb4 := floorDigit_lt ξ (show 0 < a by omega) m
  have haM' : (a : ℤ) ≤ (M : ℤ) := by exact_mod_cast haM
  have habs : |floorDigit ξ a (m + L) - floorDigit ξ a m| < (M : ℤ) := by
    rw [abs_lt]; omega
  have hzero := Int.eq_zero_of_abs_lt_dvd hdvd habs
  omega

/-- **From "periodic digits are forced" to the conclusion.**  Suppose that for the fixed real
`ξ > 0` some mechanism forces the base-`a` digit word to be eventually periodic as soon as the
residues of `⌊ξaⁿ⌋` mod `M` are eventually units.  Then `⌊ξaⁿ⌋` has infinitely many composite
terms.

Indeed, if not, then from some point on every term is a prime exceeding `M` (the terms tend to
infinity), hence a unit mod `M`; the mechanism fires, and [Dub09] Theorem 4 turns the periodic
digit word into infinitely many composites — a contradiction. -/
@[category API, AMS 11 37, ref "Dub09", group "dubc_certificate"]
theorem infinite_composites_floorPow_of_digits {a M : ℕ} (ha : 2 ≤ a) [NeZero M] {ξ : ℝ}
    (hξ : 0 < ξ)
    (H : ∀ N : ℕ, (∀ n, N ≤ n → Cop M ((floorPow ξ a n : ZMod M))) →
      ∃ n₀ L, 0 < L ∧ ∀ m, n₀ ≤ m → floorDigit ξ a (m + L) = floorDigit ξ a m) :
    {n | CompositeInt (floorPow ξ a n)}.Infinite := by
  have hMpos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  by_contra hfin
  rw [Set.not_infinite] at hfin
  obtain ⟨N₁, hN₁⟩ : ∃ N, ∀ n, N ≤ n → ¬ CompositeInt (floorPow ξ a n) := by
    obtain ⟨B, hB⟩ := hfin.bddAbove
    exact ⟨B + 1, fun n hn hns => by have := hB hns; omega⟩
  obtain ⟨N₂, hN₂⟩ :=
    Filter.tendsto_atTop_atTop.mp (tendsto_natAbs_floorPow ha hξ) (M + 1)
  -- beyond `max N₁ N₂` every term is a prime exceeding `M`, hence a unit mod `M`
  have hunit : ∀ n, max N₁ N₂ ≤ n → Cop M ((floorPow ξ a n : ZMod M)) := by
    intro n hn
    refine (cop_iff_isUnit _).mpr ?_
    have hbig : M + 1 ≤ (floorPow ξ a n).natAbs := hN₂ n (le_trans (le_max_right _ _) hn)
    have hnc := hN₁ n (le_trans (le_max_left _ _) hn)
    have hp : (floorPow ξ a n).natAbs.Prime := by
      by_contra h
      exact hnc ⟨by omega, h⟩
    refine isUnit_intCast_of_coprime ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => ?_)
    have := Nat.le_of_dvd hMpos hd
    omega
  obtain ⟨n₀, L, hL, hper⟩ := H _ hunit
  exact infinite_composites_of_periodic_digits (a := (a : ℤ)) (by positivity)
    (floorPow_succ ξ a) hL hper (tendsto_natAbs_floorPow ha hξ) hfin

/-! ### The certificate forces an eventually periodic digit word -/

/-- If the residues of `⌊ξaⁿ⌋` modulo `M` are units from `N` on, the certificate makes the
base-`a` digit word of `ξ` eventually periodic.  (The residue path is admissible, hence
eventually periodic; digits are then pinned down because `0 ≤ dₙ < a ≤ M`.) -/
@[category research solved, AMS 11 37, ref "Dub09", group "dubc_certificate"]
theorem digits_eventually_periodic_of_certOK {a M : ℕ} (ha : 2 ≤ a) (haM : a ≤ M) [NeZero M]
    (rank : ZMod M → ℕ) (hcert : CertOK a M rank)
    {ξ : ℝ} {N : ℕ} (hunit : ∀ n, N ≤ n → Cop M ((floorPow ξ a n : ZMod M))) :
    ∃ n₀ L, 0 < L ∧ ∀ m, n₀ ≤ m → floorDigit ξ a (m + L) = floorDigit ξ a m := by
  obtain ⟨j₀, L, hL, hjper⟩ := eventually_periodic_of_rank rank (rank_le_of_certOK hcert)
    (unique_of_certOK hcert) (fun j => ((floorPow ξ a (N + j) : ZMod M)))
    (step_floorPow (by omega) hunit)
  -- transport the period back to absolute indices, then read off the digits
  refine ⟨N + j₀, L, hL, digits_periodic_of_residues_periodic ha haM ?_⟩
  intro p hp
  have h1 := hjper (p - N) (by omega)
  have e1 : N + (p - N + L) = p + L := by omega
  have e2 : N + (p - N) = p := by omega
  rw [e1, e2] at h1
  exact h1

/-! ### The payoff -/

/-- **One finite certificate settles the base.**  If `CertOK a M rank` holds for a single
modulus `M ≥ a`, then for **every** real `ξ > 0` the sequence `⌊ξ·aⁿ⌋` contains infinitely
many composite terms — i.e. [DubOst06] Conjecture 2 holds for the base `a`, which for `a ≥ 7`
is the open case of the 1967 Forman–Shapiro problem.

Proof: if only finitely many terms were composite then, `⌊ξaⁿ⌋ → ∞` being unbounded, all
large terms would be primes exceeding `M`, hence units mod `M`; the certificate would make the
digit word eventually periodic, and [Dub09] Theorem 4 would then produce infinitely many
composites — a contradiction. -/
@[category research solved, AMS 11 37, ref "Dub09" "DubOst06", group "dubc_certificate"]
theorem infinite_composites_floorPow_of_certOK {a M : ℕ} (ha : 2 ≤ a) (haM : a ≤ M) [NeZero M]
    (rank : ZMod M → ℕ) (hcert : CertOK a M rank) {ξ : ℝ} (hξ : 0 < ξ) :
    {n | CompositeInt (floorPow ξ a n)}.Infinite :=
  infinite_composites_floorPow_of_digits ha hξ fun _ hunit =>
    digits_eventually_periodic_of_certOK ha haM rank hcert hunit

end DubC
