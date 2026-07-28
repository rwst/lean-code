/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TH.TwoAdic
import TH.RepetitionIdentity

/-!
# Window separation and anti-shadowing for the (3/2)ⁿ steering word (A5, T2)

Two exports of the exact 2-adic layer of `TH.TwoAdic`, in the sense of plan A5
(`plans/plan-A5.html`, T2/WP2).

## W1 — the bottom window is exactly periodic

`3^a ≡ 3^b (mod 2^N)` holds **iff** `2^(N-2) ∣ a − b` (`three_pow_modEq_iff`, `N ≥ 3`).
So the bottom `N`-bit word of `(3ⁿ)` is purely periodic with period exactly `2^(N-2)`
(`three_pow_modEq_period`), and two distinct positions can only agree on their bottom `N`
bits if their gap is at least `2^(N-2)` — agreement length `≤ 2 + log₂(gap)`
(`two_pow_le_of_three_pow_modEq`).  This is exact anti-clustering, with no estimate
anywhere.

## W3 — shadowing a periodic pattern is one residue class

If the steering word is `p`-periodic on a window of length `L` starting at `a`
(`IsPeriodicWindow`), then the circuit sum `W(a,p)` — a function of the `p` pattern
letters alone — pins the *value* `m_a` modulo `2^L`:

  `(3^p − 2^p)·m_a + W(a,p) ≡ 0  (mod 2^L)`   (`shadow_congruence`)

and `3^p − 2^p` is odd, hence invertible mod `2^L` (`isCoprime_two_pow_three_pow_sub_two_pow`), so
`m_a` lies in **one explicit residue class determined by the pattern**
(`shadow_residue`).  Consequences: any two starts of the same pattern satisfy
`2^L ∣ m_{a'} − m_a` (`shadow_pair`), which upgrades to the anti-clustering gap
`2^L ≤ m_{a'} − m_a` (`shadow_pair_gap`), and the length cap `shadow_length_cap`.

## Honest accounting (A5 risks R1–R3)

*What is new here is the residue-class reading, not the divisibility.*  The divisibility
input is TH's existing `two_pow_dvd_of_repetition`: a `p`-periodic window of length `L` at
`a` **is** a repetition of length `L − p` at the pair `(a, a+p)` (`IsRepetition_of_isPeriodicWindow`),
and `shadow_congruence` is that divisibility rewritten through `circuit_sum`.  What the
2-adic reading adds is *structure*: the residue class of `m_a` is computed from the pattern
alone, without reference to a second occurrence.

*The pincer does not beat either mechanism.*  Running the 2-adic cap and the archimedean
ceiling `repetition_pow_le` simultaneously (`shadow_length_cap`) yields the same
`2^(L+a+1) ≤ 3^(a+p+1)`, i.e. the same `L ≲ 0.585·a` slope, because both flow through the
one divisibility.  Plan A5 anticipated this (risk R3: "the pincer may improve nothing
outside narrow regimes — it is stated regardless"); it is recorded here as a fact rather
than advertised as a gain.

*The start-density count is stated pairwise, deliberately.*  `shadow_pair_gap` constrains
*values* `m_a`; converting it into a count of *positions* below `N` re-meets the
distribution problem itself, so no counting theorem is claimed ([A5] §2.3, risk R2).  The
pairwise constraint is the export, consumed pairwise.

## Contents

* `three_pow_modEq_iff`, `three_pow_modEq_period`, `two_pow_le_of_three_pow_modEq` — W1.
* `IsPeriodicWindow`, `IsRepetition_of_isPeriodicWindow` — the window predicate.
* `shadow_congruence`, `isCoprime_two_pow_three_pow_sub_two_pow`, `shadow_residue` — W3.
* `shadow_pair`, `shadow_pair_gap`, `shadow_length_cap` — the exports.

## References

* [A5] `plans/plan-A5.html`: §2.1, §2.3 (the congruence characterization), WP2, and §0.1
  Findings 2 and 4 (what was already proved, and what the exports may claim).
* [M4A3] `plans/plan-M4A3.html` §3.1–3.2: `circuit_sum`, Lemma R.
-/

namespace TH

/-! ## W1: exact periodicity of the bottom window -/

/-- **W1** ([A5] T2(i)): for `N ≥ 3` and `b ≤ a`, the bottom `N` bits of `3^a` and `3^b`
agree exactly when `2^(N-2)` divides the gap.  Since `3^b` is a unit mod `2^N`, this is
`two_pow_dvd_three_pow_sub_one_iff` transported along multiplication by `3^b`. -/
@[category research solved, AMS 11 68, ref "M4A3", group "three_halves_m4"]
theorem three_pow_modEq_iff {N a b : ℕ} (hN : 3 ≤ N) (hba : b ≤ a) :
    3 ^ a ≡ 3 ^ b [MOD 2 ^ N] ↔ 2 ^ (N - 2) ∣ a - b := by
  obtain ⟨e, rfl⟩ : ∃ e, a = b + e := ⟨a - b, by omega⟩
  simp only [show b + e - b = e by omega]
  rw [← two_pow_dvd_three_pow_sub_one_iff (e := e) hN]
  have hge : (3 : ℕ) ^ b ≤ 3 ^ (b + e) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h1e : (1 : ℕ) ≤ 3 ^ e := Nat.one_le_pow _ _ (by norm_num)
  rw [show (3 ^ (b + e) ≡ 3 ^ b [MOD 2 ^ N]) ↔ (3 ^ b ≡ 3 ^ (b + e) [MOD 2 ^ N]) from
      ⟨Nat.ModEq.symm, Nat.ModEq.symm⟩, Nat.modEq_iff_dvd' hge]
  have hfac : 3 ^ (b + e) - 3 ^ b = 3 ^ b * (3 ^ e - 1) := by
    rw [Nat.mul_sub, pow_add, mul_one]
  rw [hfac]
  -- `3^b` is coprime to `2^N`, so it can be cancelled
  have hcop : Nat.Coprime (2 ^ N) (3 ^ b) := Nat.Coprime.pow _ _ (by decide)
  exact ⟨fun h => (Nat.Coprime.dvd_of_dvd_mul_left hcop h), fun h => h.mul_left _⟩

/-- The bottom `N`-bit word of `(3ⁿ)` is purely periodic with period `2^(N-2)`
([A5] T2(i)). -/
@[category research solved, AMS 11 68, ref "M4A3", group "three_halves_m4"]
theorem three_pow_modEq_period {N : ℕ} (hN : 3 ≤ N) (n : ℕ) :
    3 ^ (n + 2 ^ (N - 2)) ≡ 3 ^ n [MOD 2 ^ N] :=
  (three_pow_modEq_iff hN (Nat.le_add_right n _)).mpr (by simp)

/-- **Agreement-length cap** ([A5] T2(i)): distinct positions whose bottom `N` bits agree
are at least `2^(N-2)` apart — equivalently, an `N`-bit agreement forces
`N ≤ 2 + log₂(gap)`. -/
@[category research solved, AMS 11 68, ref "M4A3", group "three_halves_m4"]
theorem two_pow_le_of_three_pow_modEq {N a b : ℕ} (hN : 3 ≤ N) (hba : b < a)
    (h : 3 ^ a ≡ 3 ^ b [MOD 2 ^ N]) : 2 ^ (N - 2) ≤ a - b :=
  Nat.le_of_dvd (by omega) ((three_pow_modEq_iff hN hba.le).mp h)

/-! ## W3: the shadow congruence -/

/-- The steering word is `p`-periodic on the length-`L` window starting at `a`: the letters
`t a, …, t (a+L-1)` satisfy `t (a+i) = t (a+i+p)` whenever both indices lie in the window. -/
@[category API, AMS 11 68, ref "M4A3", group "three_halves_m4"]
def IsPeriodicWindow (a p L : ℕ) : Prop := ∀ i, i + p < L → t (a + i) = t (a + i + p)

/-- A `p`-periodic window of length `L` at `a` **is** a repetition of length `L − p` at the
pair `(a, a+p)` — the bridge to TH's existing repetition layer. -/
@[category API, AMS 11 68, ref "M4A3", group "three_halves_m4"]
lemma IsRepetition_of_isPeriodicWindow {a p L : ℕ} (h : IsPeriodicWindow a p L) :
    IsRepetition a (a + p) (L - p) := by
  intro i hi
  have := h i (by omega)
  rw [this]
  ring_nf

/-- **The shadow congruence** ([A5] T2(ii), W3): a `p`-periodic window of length `L` at `a`
pins the value `m_a` modulo `2^L`,

  `(3^p − 2^p)·m_a + W(a,p) ≡ 0  (mod 2^L)`,

where `W(a,p)` depends only on the `p` letters of the pattern.  Proof: `circuit_sum` turns
the left side into `2^p·(m_{a+p} − m_a)`, and `two_pow_dvd_of_repetition` supplies
`2^(L-p) ∣ m_{a+p} − m_a`. -/
@[category research solved, AMS 11 68, ref "M4A3", group "three_halves_m4"]
theorem shadow_congruence {a p L : ℕ} (hpL : p ≤ L) (h : IsPeriodicWindow a p L) :
    (2 : ℤ) ^ L ∣ (3 ^ p - 2 ^ p) * m a + W a p := by
  have hcs := circuit_sum a p
  have hkey : ((3 : ℤ) ^ p - 2 ^ p) * m a + W a p = 2 ^ p * (m (a + p) - m a) := by
    linarith [hcs]
  obtain ⟨u, hu⟩ := two_pow_dvd_of_repetition (IsRepetition_of_isPeriodicWindow h)
  refine ⟨u, ?_⟩
  have hexp : p + (L - p) = L := by omega
  rw [hkey, hu, ← mul_assoc, ← pow_add, hexp]

/-- The multiplier `3^p − 2^p` is odd, hence a unit modulo `2^L` — this is what turns the
shadow congruence into a *residue class* for `m_a`. -/
@[category API, AMS 11 68, ref "M4A3", group "three_halves_m4"]
lemma isCoprime_two_pow_three_pow_sub_two_pow {p L : ℕ} (hp : 1 ≤ p) :
    IsCoprime ((2 : ℤ) ^ L) ((3 : ℤ) ^ p - 2 ^ p) := by
  refine IsCoprime.pow_left ?_
  obtain ⟨k, hk⟩ := odd_three_pow_sub_two_pow hp
  exact ⟨-k, 1, by rw [hk]; ring⟩

/-- **Residue form of the shadow congruence** ([A5] T2(ii)): stated in `ZMod (2^L)`, the
pattern determines the class of `m_a` outright.  The inverse-free `shadow_congruence` is
the primary statement (it avoids `ℤ₂` and the unit-group machinery); this is the readable
corollary. -/
@[category research solved, AMS 11 68, ref "M4A3", group "three_halves_m4"]
theorem shadow_residue {a p L : ℕ} (hpL : p ≤ L) (h : IsPeriodicWindow a p L) :
    ((3 : ZMod (2 ^ L)) ^ p - 2 ^ p) * ((m a : ℤ) : ZMod (2 ^ L))
      = -((W a p : ℤ) : ZMod (2 ^ L)) := by
  obtain ⟨u, hu⟩ := shadow_congruence hpL h
  have h0 : ((2 ^ L : ℤ) : ZMod (2 ^ L)) = 0 := by
    have h1 : ((2 ^ L : ℕ) : ZMod (2 ^ L)) = 0 := ZMod.natCast_self _
    exact_mod_cast h1
  have hz : ((((3 : ℤ) ^ p - 2 ^ p) * m a + W a p : ℤ) : ZMod (2 ^ L)) = 0 := by
    rw [hu, Int.cast_mul, h0, zero_mul]
  push_cast at hz
  linear_combination hz

/-- **Pairwise shadow constraint** ([A5] T2(ii)): two starts of the *same* `p`-periodic
pattern have `m`-values congruent mod `2^L`.  Invisible to archimedean arguments, which see
only the sizes of `m_a`, `m_{a'}`. -/
@[category research solved, AMS 11 68, ref "M4A3", group "three_halves_m4"]
theorem shadow_pair {a a' p L : ℕ} (hp : 1 ≤ p) (hpL : p ≤ L)
    (ha : IsPeriodicWindow a p L) (ha' : IsPeriodicWindow a' p L)
    (hpat : ∀ i < p, t (a + i) = t (a' + i)) :
    (2 : ℤ) ^ L ∣ m a' - m a := by
  have hW : W a p = W a' p := Finset.sum_congr rfl fun i hi => by
    rw [hpat i (Finset.mem_range.mp hi)]
  have h1 := shadow_congruence hpL ha
  have h2 := shadow_congruence hpL ha'
  rw [← hW] at h2
  have hsub : (2 : ℤ) ^ L ∣ ((3 : ℤ) ^ p - 2 ^ p) * (m a' - m a) := by
    have := dvd_sub h2 h1
    have heq : ((3 : ℤ) ^ p - 2 ^ p) * m a' + W a p - (((3 : ℤ) ^ p - 2 ^ p) * m a + W a p)
        = ((3 : ℤ) ^ p - 2 ^ p) * (m a' - m a) := by ring
    rwa [heq] at this
  exact (isCoprime_two_pow_three_pow_sub_two_pow (L := L) hp).dvd_of_dvd_mul_left hsub

/-- **Anti-clustering gap** ([A5] T2(ii), honest form): distinct starts `2 ≤ a < a'` of the
same `p`-periodic length-`L` pattern have `m`-values at least `2^L` apart.  Note this
constrains *values*; counting *positions* below `N` re-meets the distribution problem, so no
density theorem is claimed (risk R2). -/
@[category research solved, AMS 11 68, ref "M4A3", group "three_halves_m4"]
theorem shadow_pair_gap {a a' p L : ℕ} (hp : 1 ≤ p) (hpL : p ≤ L) (ha2 : 2 ≤ a)
    (haa' : a < a') (ha : IsPeriodicWindow a p L) (ha' : IsPeriodicWindow a' p L)
    (hpat : ∀ i < p, t (a + i) = t (a' + i)) :
    (2 : ℤ) ^ L ≤ m a' - m a :=
  Int.le_of_dvd (sub_pos.mpr (m_strictMono ha2 haa')) (shadow_pair hp hpL ha ha' hpat)

/-- **The pincer** ([A5] T2(iii)): the 2-adic cap and the archimedean growth ceiling
`repetition_pow_le`, run together on a `p`-periodic window of length `L` at `2 ≤ a`, give

  `2^(L + a + 1) ≤ 3^(a + p + 1)`,

i.e. the `L ≲ 0.585·a` slope.  Both mechanisms flow through the single divisibility
`2^(L-p) ∣ m_{a+p} − m_a`, so the joint constant is *not* better than either separately —
recorded, per [A5] risk R3, as a fact rather than a gain. -/
@[category research solved, AMS 11 68, ref "M4A3", group "three_halves_m4"]
theorem shadow_length_cap {a p L : ℕ} (ha2 : 2 ≤ a) (hp : 1 ≤ p) (hpL : p ≤ L)
    (h : IsPeriodicWindow a p L) : 2 ^ (L + a + 1) ≤ 3 ^ (a + p + 1) := by
  have hrep := repetition_pow_le_nat ha2 (by omega : a < a + p)
    (IsRepetition_of_isPeriodicWindow h)
  calc 2 ^ (L + a + 1) = 2 ^ ((L - p) + (a + p) + 1) := by congr 1; omega
    _ ≤ 3 ^ ((a + p) + 1) := hrep
    _ = 3 ^ (a + p + 1) := rfl

end TH
