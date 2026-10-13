/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.ObstructionKit

/-!
# Neither `{2}` nor `{3}` certifies at an integer shift

plan-dubC2-transform, conjecture N-4 (note-dubC2T-M0 §§7–8): at every base `p/q` and every
**integer** shift `ν = a/b` (`b ∣ a`), [Oda26] Theorem 42 kills the divisor sets `{2}`
(`not_checked_two_of_int`) and `{3}` (`not_checked_three_of_int`), so no certificate over these
primes exists, whatever the cell count `D` and modulus `M`.  (`{5}` is not always killed: it
survives Theorem 42 at `3/2` and `4/3`.)

The witness for `{2}`: put `t = p − q`, `k = t·(a/b)`, so that the fixed point of the letter `s₀` is
`x* = (s₀ + k)/t`.
* `t` odd: take `s₀ ∈ {−k, t − k}` odd (`x* ∈ {0, 1}`), `c = s₀ ± 2`, `R = 1`; then
  `2 ∣ t·R + s₀` and `2 ∣ c − s₀`, and `s₀`, `c` are odd (for `2 ∣ q`).
* `t` even (so `p`, `q` odd and `2 ∉ Pq`): take `s₀ = −k` (even, `x* = 0`), `c = s₀ + 2`, `R = 1`.
In both cases `x* + (c − s₀)/p ∈ {2/p, 1 − 2/p} ⊂ (0, 1)` since `p ≥ 3`.

## References

* [Oda26] Y. Odagiri, *Finite graph certificates for composite terms in rational floor sequences*,
  Zenodo, doi:10.5281/zenodo.22997709 (2026).
-/

namespace DubC2.Gen

/-- **N-4 for `{2}`.**  At an integer shift (`b ∣ a`), no certificate is checked for a parameter set
whose primes are all `2`: the two-letter obstruction of [Oda26] Theorem 42 always applies. -/
@[category research solved, AMS 11 37, ref "Oda26", group "dubc2_obstruction"]
theorem not_checked_two_of_int {P : Params} {C : Cert} (hab : (P.b : ℤ) ∣ P.a)
    (hPM : ∀ l ∈ P.PM, l = 2) (hPq : ∀ l ∈ P.Pq, l = 2) : ¬ Checked P C := by
  intro hc
  have hF : ParamFacts P := by
    have hh := hc.head
    simp only [checkHead, Bool.and_eq_true] at hh
    exact paramFacts hh.1.1.1.1.1
  obtain ⟨m, hm⟩ := hab
  have hq1 := hF.q1
  have hpq := hF.pq
  have hb0 : (0 : ℤ) < P.b := by exact_mod_cast hF.b0
  have ht0 : (0 : ℤ) < (P.p : ℤ) - P.q := by omega
  have hp2 : (0 : ℤ) < (P.p : ℤ) - 2 := by omega
  have hu0 : (0 : ℤ) < ((P.p : ℤ) - P.q) * P.b := mul_pos ht0 hb0
  have hv0 : (0 : ℤ) < ((P.p : ℤ) - 2) * (((P.p : ℤ) - P.q) * P.b) := mul_pos hp2 hu0
  have key : ((P.p : ℤ) - P.q) * P.a = ((P.p : ℤ) - P.q) * m * P.b := by rw [hm]; ring
  generalize hk : ((P.p : ℤ) - P.q) * m = k at key
  have hPM' : ∀ l ∈ P.PM, l ∈ [2] := fun l hl => by simp [hPM l hl]
  rcases Int.emod_two_eq_zero_or_one ((P.p : ℤ) - P.q) with htp | htp
  · -- `p − q` even: `p`, `q` odd, so no prime of `Pq`
    have hqodd : ¬ 2 ∣ P.q := by
      intro h2
      have hp2 : 2 ∣ P.p := by omega
      have := Nat.dvd_gcd hp2 h2
      rw [hF.cop] at this
      omega
    have hk2 : k % 2 = 0 := by
      rw [← hk, Int.mul_emod, htp]; simp
    refine not_checked_of_witnessOK (P := P) (C := C) ⟨[2], [], -k, -k + 2, 1⟩ ?_ hPM'
      (fun l hl => ?_) hc
    · simp only [witnessOK, Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
        Bool.or_eq_true, Bool.and_true, and_assoc, Nat.cast_ofNat, key]
      refine ⟨by omega, by omega, Or.inr ⟨by omega, by omega⟩, ?_, ?_, ?_, ?_⟩ <;>
        nlinarith
    · exfalso
      have h2 := hPq l hl
      have := (hF.Pq l hl).1
      subst h2
      exact hqodd (Nat.dvd_of_mod_eq_zero this)
  · rcases Int.emod_two_eq_zero_or_one k with hk2 | hk2
    · -- `s₀ = (p − q) − k` (odd), `x* = 1`, `c = s₀ − 2`
      refine not_checked_of_witnessOK (P := P) (C := C)
        ⟨[2], [2], ((P.p : ℤ) - P.q) - k, ((P.p : ℤ) - P.q) - k - 2, 1⟩ ?_ hPM'
        (fun l hl => by simp [hPq l hl]) hc
      simp only [witnessOK, Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
        Bool.or_eq_true, Bool.and_true, and_assoc, Nat.cast_ofNat, key]
      refine ⟨by omega, by omega, Or.inr ⟨by omega, by omega⟩, by omega, by omega, ?_, ?_, ?_,
        ?_⟩ <;> nlinarith
    · -- `s₀ = −k` (odd), `x* = 0`, `c = s₀ + 2`
      refine not_checked_of_witnessOK (P := P) (C := C) ⟨[2], [2], -k, -k + 2, 1⟩ ?_ hPM'
        (fun l hl => by simp [hPq l hl]) hc
      simp only [witnessOK, Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
        Bool.or_eq_true, Bool.and_true, and_assoc, Nat.cast_ofNat, key]
      refine ⟨by omega, by omega, Or.inr ⟨by omega, by omega⟩, by omega, by omega, ?_, ?_, ?_,
        ?_⟩ <;> nlinarith

/-- **N-4 for `{3}`.**  At an integer shift (`b ∣ a`), no certificate is checked for a parameter set
whose primes are all `3`.  Witnesses, with `t = p − q` and `k = t·(a/b)`:
* `3 ∣ q` or `3 ∣ p`: letters prime to `3` — `x* = 0` and `c = s₀ + 1, s₀ + 2`, or `x* = 1` and
  `c = s₀ − 1, s₀ − 2`, or, when `3 ∣ k` and `3 ∣ t`, `x* = 1/t` and `c = s₀ + 1` (`p + t < pt`);
* `3 ∤ pq` (so `p ≥ 4`): `c − s₀ = ±3` and a residue `R ∈ {1, 2}` with `3 ∣ tR + s₀`. -/
@[category research solved, AMS 11 37, ref "Oda26", group "dubc2_obstruction"]
theorem not_checked_three_of_int {P : Params} {C : Cert} (hab : (P.b : ℤ) ∣ P.a)
    (hPM : ∀ l ∈ P.PM, l = 3) (hPq : ∀ l ∈ P.Pq, l = 3) : ¬ Checked P C := by
  intro hc
  have hF : ParamFacts P := by
    have hh := hc.head
    simp only [checkHead, Bool.and_eq_true] at hh
    exact paramFacts hh.1.1.1.1.1
  obtain ⟨m, hm⟩ := hab
  have hq1 := hF.q1
  have hpq := hF.pq
  have hb0 : (0 : ℤ) < P.b := by exact_mod_cast hF.b0
  have ht0 : (0 : ℤ) < (P.p : ℤ) - P.q := by omega
  have hu0 : (0 : ℤ) < ((P.p : ℤ) - P.q) * P.b := mul_pos ht0 hb0
  have hp3 : (3 : ℤ) * (((P.p : ℤ) - P.q) * P.b) ≤ P.p * (((P.p : ℤ) - P.q) * P.b) := by
    have : (3 : ℤ) ≤ P.p := by omega
    nlinarith
  have hbt : (P.b : ℤ) ≤ ((P.p : ℤ) - P.q) * P.b := by nlinarith
  have hpb : (0 : ℤ) < (P.p : ℤ) * P.b := by
    have : (0 : ℤ) < P.p := by omega
    positivity
  have key : ((P.p : ℤ) - P.q) * P.a = ((P.p : ℤ) - P.q) * m * P.b := by rw [hm]; ring
  generalize hk : ((P.p : ℤ) - P.q) * m = k at key
  have hkt : (P.p - P.q : ℤ) % 3 = 0 → k % 3 = 0 := fun h => by
    rw [← hk, Int.mul_emod, h]; simp
  -- `x* = 1/t` needs `p + t < p t` once `t ≥ 3`
  have hsmall : (P.p - P.q : ℤ) % 3 = 0 →
      (P.p : ℤ) * P.b + ((P.p : ℤ) - P.q) * P.b < P.p * (((P.p : ℤ) - P.q) * P.b) := fun h => by
    have ht3 : (3 : ℤ) ≤ (P.p : ℤ) - P.q := by omega
    have hp3' : (3 : ℤ) ≤ P.p := by omega
    have : (0 : ℤ) < ((P.p : ℤ) - 1) * (((P.p : ℤ) - P.q) - 1) - 1 := by nlinarith
    nlinarith [mul_pos this hb0]
  have ht3 : (P.p - P.q : ℤ) % 3 = 0 ∨ (P.p - P.q : ℤ) % 3 = 1 ∨ (P.p - P.q : ℤ) % 3 = 2 := by
    omega
  have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  by_cases h3q : 3 ∣ P.q
  · -- `3 ∣ q`: `3 ∉ PM` since `q` is a unit mod `M`
    have hPM0 : ∀ l ∈ P.PM, l ∈ ([] : List ℕ) := fun l hl => by
      exfalso
      have h3 := hPM l hl
      have hM3 : 3 ∣ P.M := by
        have := hF.PM l hl; subst h3; exact Nat.dvd_of_mod_eq_zero this
      have hinv := congrArg (· % 3) hF.inv
      simp only [Nat.mod_mod_of_dvd _ hM3] at hinv
      obtain ⟨j, hj⟩ := h3q
      rw [hj, mul_assoc, Nat.mul_mod_right] at hinv
      omega
    have hPq3 : ∀ l ∈ P.Pq, l ∈ [3] := fun l hl => by simp [hPq l hl]
    rcases hk3 with hk3 | hk3 | hk3
    · rcases ht3 with ht3 | ht3 | ht3
      · refine not_checked_of_witnessOK (P := P) (C := C) ⟨[], [3], -k + 1, -k + 2, 1⟩ ?_ hPM0
          hPq3 hc
        simp only [witnessOK, Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
          Bool.and_true, and_assoc, Nat.cast_ofNat, key]
        have := hsmall ht3
        and_intros <;> first | omega | linarith
      · refine not_checked_of_witnessOK (P := P) (C := C)
          ⟨[], [3], ((P.p : ℤ) - P.q) - k, ((P.p : ℤ) - P.q) - k - 2, 1⟩ ?_ hPM0 hPq3 hc
        simp only [witnessOK, Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
          Bool.and_true, and_assoc, Nat.cast_ofNat, key]
        and_intros <;> first | omega | linarith
      · refine not_checked_of_witnessOK (P := P) (C := C)
          ⟨[], [3], ((P.p : ℤ) - P.q) - k, ((P.p : ℤ) - P.q) - k - 1, 1⟩ ?_ hPM0 hPq3 hc
        simp only [witnessOK, Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
          Bool.and_true, and_assoc, Nat.cast_ofNat, key]
        and_intros <;> first | omega | linarith
    · refine not_checked_of_witnessOK (P := P) (C := C) ⟨[], [3], -k, -k + 2, 1⟩ ?_ hPM0 hPq3 hc
      simp only [witnessOK, Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
        Bool.and_true, and_assoc, Nat.cast_ofNat, key]
      and_intros <;> first | omega | linarith
    · refine not_checked_of_witnessOK (P := P) (C := C) ⟨[], [3], -k, -k + 1, 1⟩ ?_ hPM0 hPq3 hc
      simp only [witnessOK, Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
        Bool.and_true, and_assoc, Nat.cast_ofNat, key]
      and_intros <;> first | omega | linarith
  by_cases h3p : 3 ∣ P.p
  · -- `3 ∣ p`: the same letters, through the alternative `3 ∣ p, 3 ∤ s₀, 3 ∤ c`
    have hp3i : (P.p : ℤ) % 3 = 0 := by omega
    have hPM3 : ∀ l ∈ P.PM, l ∈ [3] := fun l hl => by simp [hPM l hl]
    have hPq3 : ∀ l ∈ P.Pq, l ∈ [3] := fun l hl => by simp [hPq l hl]
    rcases hk3 with hk3 | hk3 | hk3
    · rcases ht3 with ht3 | ht3 | ht3
      · refine not_checked_of_witnessOK (P := P) (C := C) ⟨[3], [3], -k + 1, -k + 2, 1⟩ ?_ hPM3
          hPq3 hc
        simp only [witnessOK, Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
          Bool.or_eq_true, Bool.and_true, and_assoc, Nat.cast_ofNat, key]
        have := hsmall ht3
        and_intros <;> omega
      · refine not_checked_of_witnessOK (P := P) (C := C)
          ⟨[3], [3], ((P.p : ℤ) - P.q) - k, ((P.p : ℤ) - P.q) - k - 2, 1⟩ ?_ hPM3 hPq3 hc
        simp only [witnessOK, Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
          Bool.or_eq_true, Bool.and_true, and_assoc, Nat.cast_ofNat, key]
        and_intros <;> first | omega | linarith
      · refine not_checked_of_witnessOK (P := P) (C := C)
          ⟨[3], [3], ((P.p : ℤ) - P.q) - k, ((P.p : ℤ) - P.q) - k - 1, 1⟩ ?_ hPM3 hPq3 hc
        simp only [witnessOK, Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
          Bool.or_eq_true, Bool.and_true, and_assoc, Nat.cast_ofNat, key]
        and_intros <;> first | omega | linarith
    · refine not_checked_of_witnessOK (P := P) (C := C) ⟨[3], [3], -k, -k + 2, 1⟩ ?_ hPM3 hPq3 hc
      simp only [witnessOK, Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
        Bool.or_eq_true, Bool.and_true, and_assoc, Nat.cast_ofNat, key]
      and_intros <;> first | omega | linarith
    · refine not_checked_of_witnessOK (P := P) (C := C) ⟨[3], [3], -k, -k + 1, 1⟩ ?_ hPM3 hPq3 hc
      simp only [witnessOK, Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
        Bool.or_eq_true, Bool.and_true, and_assoc, Nat.cast_ofNat, key]
      and_intros <;> first | omega | linarith
  · -- `3 ∤ pq`: `c − s₀ = ±3`, `p ≥ 4`, and `3 ∉ Pq`
    have hp4 : (4 : ℤ) * (((P.p : ℤ) - P.q) * P.b) ≤ P.p * (((P.p : ℤ) - P.q) * P.b) := by
      have : (4 : ℤ) ≤ P.p := by omega
      nlinarith
    have hPM3 : ∀ l ∈ P.PM, l ∈ [3] := fun l hl => by simp [hPM l hl]
    have hPq0 : ∀ l ∈ P.Pq, l ∈ ([] : List ℕ) := fun l hl => by
      exfalso
      have h3 := hPq l hl
      have := (hF.Pq l hl).1
      subst h3
      exact h3q (Nat.dvd_of_mod_eq_zero this)
    rcases ht3 with ht3 | ht3 | ht3
    · have hk0 := hkt ht3
      refine not_checked_of_witnessOK (P := P) (C := C) ⟨[3], [], -k, -k + 3, 1⟩ ?_ hPM3 hPq0 hc
      simp only [witnessOK, Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
        Bool.or_eq_true, Bool.and_true, and_assoc, Nat.cast_ofNat, key]
      and_intros <;> first | omega | linarith
    all_goals
      rcases hk3 with hk3 | hk3 | hk3
      · -- `s₀ = t − k ≢ 0`, `x* = 1`, `R = 2`: `3 ∣ 2t + t − k`
        refine not_checked_of_witnessOK (P := P) (C := C)
          ⟨[3], [], ((P.p : ℤ) - P.q) - k, ((P.p : ℤ) - P.q) - k - 3, 2⟩ ?_ hPM3 hPq0 hc
        simp only [witnessOK, Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
          Bool.or_eq_true, Bool.and_true, and_assoc, Nat.cast_ofNat, key]
        and_intros <;> first | omega | linarith
      all_goals
        -- `s₀ = −k ≢ 0`, `x* = 0`, `R ∈ {1, 2}` with `3 ∣ tR − k`
        by_cases hR : ((P.p : ℤ) - P.q - k) % 3 = 0
        · refine not_checked_of_witnessOK (P := P) (C := C) ⟨[3], [], -k, -k + 3, 1⟩ ?_ hPM3
            hPq0 hc
          simp only [witnessOK, Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
            Bool.or_eq_true, Bool.and_true, and_assoc, Nat.cast_ofNat, key]
          and_intros <;> first | omega | linarith
        · refine not_checked_of_witnessOK (P := P) (C := C) ⟨[3], [], -k, -k + 3, 2⟩ ?_ hPM3
            hPq0 hc
          simp only [witnessOK, Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
            Bool.or_eq_true, Bool.and_true, and_assoc, Nat.cast_ofNat, key]
          and_intros <;> first | omega | linarith

end DubC2.Gen
