/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Oda26.WordArith
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.ZMod.Defs

/-!
# The family `(6t+3)/(6t+1)`: the integer map `T_t` ([Oda26] App. B.4, C.1–C.2)

For `t ≥ 1` put `a = 6t+3`, `b = 6t+1`, `δ = t mod 2`, `H = 3t−1−δ` and
`T_t(Q) = Q + 2⌊(Q+3t+1)/b⌋`, `F_t(z) = ⌈(az−δ)/b⌉`, `e = b·F_t(z) − az + δ`.

* `Oda.Fam.T_conj` … `Oda.Fam.F_add` — **Lemma 52** (a)–(d).
* `Oda.Fam.carries_eq_iff` — **Proposition 53**, carry-word form: two odd `T_t`-orbits share their
  first `L` carries iff their initial values agree mod `b^L`.

The rest of [Oda26] App. C (non-branching, the halting equivalence Theorem 58, prime forks) is
specific to this family and outside the scope kept here (user decision 2026-10-07: only results that
are general or bear on `DubC2/`).

## References

* [Oda26] Y. Odagiri, *Finite graph certificates for composite terms in rational floor sequences*,
  Zenodo, doi:10.5281/zenodo.22997709 (2026).
-/

namespace Oda.Fam

/-- `a = 6t+3`. -/
abbrev A (t : ℕ) : ℤ := 6 * t + 3
/-- `b = 6t+1`. -/
abbrev B (t : ℕ) : ℤ := 6 * t + 1
/-- `δ = t mod 2`. -/
abbrev δ (t : ℕ) : ℤ := (t : ℤ) % 2
/-- `H = 3t − 1 − δ` (odd). -/
abbrev H (t : ℕ) : ℤ := 3 * t - 1 - δ t

/-- The integer map `T_t(Q) = Q + 2⌊(Q+3t+1)/b⌋` of [Oda26] (32). -/
def T (t : ℕ) (Q : ℤ) : ℤ := Q + 2 * ((Q + 3 * t + 1) / B t)

/-- The ceiling map `F_t(z) = ⌈(az−δ)/b⌉`. -/
def F (t : ℕ) (z : ℤ) : ℤ := (A t * z - δ t + B t - 1) / B t

/-- The digit `e = b·F_t(z) − az + δ`. -/
def e (t : ℕ) (z : ℤ) : ℤ := B t * F t z - A t * z + δ t

/-- The `T_t`-orbit. -/
def orbit (t : ℕ) (Q : ℤ) (n : ℕ) : ℤ := (T t)^[n] Q

/-- Its carry word `cₙ = b·Q_{n+1} − a·Qₙ`. -/
def carry (t : ℕ) (Q : ℤ) (n : ℕ) : ℤ := B t * orbit t Q (n + 1) - A t * orbit t Q n

theorem H_odd (t : ℕ) : Odd (H t) := by
  refine ⟨(3 * t - 2 - δ t) / 2, ?_⟩
  simp only [H, δ]; omega

/-- **[Oda26] Lemma 52(a).**  `T_t(2z+H) = 2F_t(z) + H`. -/
@[category research solved, AMS 11, ref "Oda26", group "oda26_family"]
theorem T_conj (t : ℕ) (z : ℤ) : T t (2 * z + H t) = 2 * F t z + H t := by
  have hb : (0 : ℤ) < B t := by positivity
  have h2 : 2 * z + H t + 3 * t + 1 = 2 * z - δ t + B t - 1 := by simp only [H, B]; ring
  simp only [T, F]
  rw [h2, show A t * z - δ t + B t - 1 = (2 * z - δ t + B t - 1) + z * B t by simp only [A, B]; ring,
    Int.add_mul_ediv_right _ _ hb.ne']
  ring

/-- `T_t` preserves parity. -/
theorem T_parity (t : ℕ) (Q : ℤ) : T t Q % 2 = Q % 2 := by simp only [T]; omega

/-- **[Oda26] Lemma 52(b).**  `0 ≤ e ≤ b−1`. -/
@[category research solved, AMS 11, ref "Oda26", group "oda26_family"]
theorem e_bounds (t : ℕ) (z : ℤ) : 0 ≤ e t z ∧ e t z ≤ B t - 1 := by
  have hb : (0 : ℤ) < B t := by positivity
  have h1 := Int.emod_def (A t * z - δ t + B t - 1) (B t)
  have h2 := Int.emod_nonneg (A t * z - δ t + B t - 1) hb.ne'
  have h3 := Int.emod_lt_of_pos (A t * z - δ t + B t - 1) hb
  simp only [e, F]
  constructor <;> linarith

/-- **[Oda26] Lemma 52(b)**, congruence: `e ≡ δ − az (mod b)`. -/
@[category research solved, AMS 11, ref "Oda26", group "oda26_family"]
theorem e_modEq (t : ℕ) (z : ℤ) : e t z ≡ δ t - A t * z [ZMOD B t] := by
  refine Int.modEq_iff_dvd.2 ⟨-F t z, ?_⟩
  simp only [e]; ring

/-- **[Oda26] Lemma 52(c).**  The carry of `Q = 2z+H` is `2(e − (3t−1))`. -/
@[category research solved, AMS 11, ref "Oda26", group "oda26_family"]
theorem carry_conj (t : ℕ) (z : ℤ) :
    B t * T t (2 * z + H t) - A t * (2 * z + H t) = 2 * (e t z - (3 * t - 1)) := by
  rw [T_conj]; simp only [e, H, A, B]; ring

/-- **[Oda26] Lemma 52(d).**  `F_t(s + bv) = F_t(s) + av`. -/
@[category research solved, AMS 11, ref "Oda26", group "oda26_family"]
theorem F_add (t : ℕ) (s v : ℤ) : F t (s + B t * v) = F t s + A t * v := by
  have hb : (0 : ℤ) < B t := by positivity
  simp only [F]
  rw [show A t * (s + B t * v) - δ t + B t - 1 = (A t * s - δ t + B t - 1) + (A t * v) * B t by ring,
    Int.add_mul_ediv_right _ _ hb.ne']

/-- Lemma 52(d) in `T`-form: `T_t(Q + 2bw) = T_t(Q) + 2aw`. -/
theorem T_add (t : ℕ) (Q w : ℤ) : T t (Q + 2 * B t * w) = T t Q + 2 * A t * w := by
  have hb : (0 : ℤ) < B t := by positivity
  simp only [T]
  rw [show Q + 2 * B t * w + 3 * t + 1 = (Q + 3 * t + 1) + (2 * w) * B t by ring,
    Int.add_mul_ediv_right _ _ hb.ne']
  simp only [A, B]; ring

theorem orbit_succ (t : ℕ) (Q : ℤ) (n : ℕ) : orbit t Q (n + 1) = T t (orbit t Q n) := by
  simp only [orbit, Function.iterate_succ_apply']

theorem carry_rec (t : ℕ) (Q : ℤ) (n : ℕ) :
    ((6 * t + 1 : ℕ) : ℤ) * orbit t Q (n + 1) = ((6 * t + 3 : ℕ) : ℤ) * orbit t Q n + carry t Q n := by
  simp only [carry]; push_cast; ring

theorem B_coprime_A (t : ℕ) : Nat.Coprime (6 * t + 3) (6 * t + 1) := by
  have : 6 * t + 3 = 2 + (6 * t + 1) := by ring
  rw [this, Nat.coprime_add_self_left, Nat.coprime_two_left]
  exact ⟨3 * t, by ring⟩

/-- The orbit of `Q + 2b^L w`: `Q'_k = Q_k + 2aᵏb^{L−k}w` for `k ≤ L`. -/
theorem orbit_shift (t : ℕ) (Q w : ℤ) (L : ℕ) :
    ∀ k ≤ L, orbit t (Q + 2 * B t ^ L * w) k = orbit t Q k + 2 * A t ^ k * B t ^ (L - k) * w := by
  intro k
  induction k with
  | zero => intro _; simp [orbit]
  | succ k ih =>
    intro hk
    rw [orbit_succ, orbit_succ, ih (by omega)]
    obtain ⟨m, hm⟩ : ∃ m, L - k = m + 1 := ⟨L - k - 1, by omega⟩
    rw [hm, show L - (k + 1) = m by omega,
      show 2 * A t ^ k * B t ^ (m + 1) * w = 2 * B t * (A t ^ k * B t ^ m * w) by ring, T_add]
    ring

/-- **[Oda26] Proposition 53**, carry-word form.  For odd `Q₀, Q₀'`, the first `L` carries of
their `T_t`-orbits agree iff `Q₀ ≡ Q₀' (mod b^L)`. -/
@[category research solved, AMS 11, ref "Oda26", group "oda26_family"]
theorem carries_eq_iff (t : ℕ) {Q Q' : ℤ} (hQ : Odd Q) (hQ' : Odd Q') (L : ℕ) :
    (∀ k < L, carry t Q k = carry t Q' k) ↔ Q ≡ Q' [ZMOD B t ^ L] := by
  constructor
  · intro h
    have e1 := pow_mul_eq (carry_rec t Q) L
    have e2 := pow_mul_eq (carry_rec t Q') L
    have hC : Ccum (6 * t + 3) (6 * t + 1) (carry t Q) L =
        Ccum (6 * t + 3) (6 * t + 1) (carry t Q') L := by
      have : ∀ j ≤ L, Ccum (6 * t + 3) (6 * t + 1) (carry t Q) j =
          Ccum (6 * t + 3) (6 * t + 1) (carry t Q') j := by
        intro j
        induction j with
        | zero => intro _; rfl
        | succ j ih => intro hj; simp only [Ccum]; rw [ih (by omega), h j (by omega)]
      exact this L le_rfl
    have hdiv : ((6 * t + 1 : ℕ) : ℤ) ^ L ∣ ((6 * t + 3 : ℕ) : ℤ) ^ L * (Q' - Q) :=
      ⟨orbit t Q' L - orbit t Q L, by
        rw [show orbit t Q 0 = Q from rfl] at e1
        rw [show orbit t Q' 0 = Q' from rfl] at e2
        linear_combination e1 - e2 + hC⟩
    have hc : IsCoprime (((6 * t + 1 : ℕ) : ℤ) ^ L) (((6 * t + 3 : ℕ) : ℤ) ^ L) :=
      (Nat.isCoprime_iff_coprime.2 (B_coprime_A t).symm).pow
    have := Int.modEq_iff_dvd.2 (hc.dvd_of_dvd_mul_left hdiv)
    simpa using this
  · intro h k hk
    obtain ⟨m, hm⟩ := (Int.modEq_iff_dvd.1 h)
    -- `b^L m = Q' − Q` is even and `b` is odd, so `m = 2w`
    have hBodd : Odd (B t ^ L) := Odd.pow ⟨3 * t, by ring⟩
    have hmeven : Even m := by
      have hev : Even (B t ^ L * m) := by rw [← hm]; exact Odd.sub_odd hQ' hQ
      rcases Int.even_mul.1 hev with h' | h'
      · exact absurd h' (Int.not_even_iff_odd.2 hBodd)
      · exact h'
    obtain ⟨w, hw⟩ := hmeven
    have hQ'eq : Q' = Q + 2 * B t ^ L * w := by linear_combination hm + B t ^ L * hw
    subst hQ'eq
    simp only [carry]
    rw [orbit_shift t Q w L (k + 1) (by omega), orbit_shift t Q w L k (by omega)]
    obtain ⟨j, hj⟩ : ∃ j, L - k = j + 1 := ⟨L - k - 1, by omega⟩
    rw [hj, show L - (k + 1) = j by omega]
    simp only [A, B]; ring

end Oda.Fam
