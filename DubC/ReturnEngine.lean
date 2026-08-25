/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Set.Finite.Basic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The Dubickas return engine: [Dub09] Theorem 4

**[Dub09] Theorem 4** (Dubickas, *Prime and composite integers close to powers of a number*,
Monatsh. Math. **158** (2009) 271–284, §2).  Let `d = k + 1 ≥ 1`, let
`F ∈ ℤ[z₁,…,z_k]`, let `c ≠ 0` be an integer and let `x₀, x₁, x₂, …` be integers with

  `x_{n+d} = c · x_n + F(x_{n+1}, …, x_{n+d-1})`   for every `n`.        (1)

Then for every `q ≥ 1` with `gcd(c, q) = 1` the sequence is **purely** periodic modulo `q`
(`DubC.purely_periodic_mod`), and if moreover `|x_n| → ∞` the sequence contains infinitely
many composite terms (`DubC.infinite_composites`).

This single theorem is the *engine* of the plan `plans/plan-dubC1.html` (milestone M1′): it
disposes of the "eventually periodic digit word" regime of the 1967 Forman–Shapiro problem
for `⌊ξ aⁿ⌋` in one blow, uniformly in the base and in the shift.  Everything downstream in
`DubC/` (`DigitRecurrence.lean`, `Certificate.lean`, `Verdict.lean`) reduces to it.

## The two halves of the proof

*Ultimate* periodicity is pigeonhole on the window vectors `(x_n, …, x_{n+k}) mod q`: two
windows agree, and (1) propagates the agreement forwards (`hstep` below, read left to right).

*Pure* periodicity is where `gcd(c, q) = 1` enters: (1) also propagates agreement
**backwards** one step, because subtracting the two instances of (1) leaves
`c · (x_{ℓ} - x_{ℓ+t}) ≡ 0 (mod q)`, and `c` is invertible.  A downward induction then pushes
the period all the way to `n = 0`.  Both directions are packaged in the single identity

  `x_{n+k+1+t} - x_{n+k+1} ≡ c · (x_{n+t} - x_n)  (mod q)`   (`DubC.return_step`)

valid whenever the intermediate window entries already agree.

## Generality of `F`

The proof uses only that `F` **descends to `ZMod q`** — congruent inputs give congruent
outputs.  That is isolated as `DubC.CongrPreserving`, and
`DubC.congrPreserving_mvPolynomial` shows every `F ∈ ℤ[z₁,…,z_k]` qualifies, so the
polynomial hypothesis of the paper is recovered (`DubC.purely_periodic_mod_mvPolynomial`).
Stating it this way keeps the engine usable for the `d = 1` constant-`F` instances that
`DigitRecurrence.lean` actually feeds it.

## References

* **[Dub09]** A. Dubickas, *Prime and composite integers close to powers of a number*,
  Monatsh. Math. **158** (2009) 271–284.  Theorem 4 and its proof in §2.
-/

namespace DubC

open Filter

/-! ### Composite integers -/

/-- An integer is **composite** in the sense of [Dub09] if its absolute value is a composite
natural number ("a negative integer `a` is said to be composite if `|a|` is composite",
[Dub09] p. 273). -/
def CompositeInt (m : ℤ) : Prop := 2 ≤ m.natAbs ∧ ¬ m.natAbs.Prime

@[category API, AMS 11, ref "Dub09", group "dubc_return_engine"]
theorem compositeInt_of_prime_dvd {m : ℤ} {q : ℕ} (hq : q.Prime) (hdvd : (q : ℤ) ∣ m)
    (hlt : q < m.natAbs) : CompositeInt m := by
  refine ⟨le_trans hq.two_le hlt.le, fun hp => ?_⟩
  have hqd : q ∣ m.natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa using this
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp q hqd) with h | h
  · exact absurd h hq.one_lt.ne'
  · exact absurd h (by omega)

/-- An integer coprime to `q` casts to a unit of `ZMod q`. -/
@[category API, AMS 11, ref "Dub09", group "dubc_return_engine"]
theorem isUnit_intCast_of_coprime {q : ℕ} {m : ℤ} (h : Nat.Coprime m.natAbs q) :
    IsUnit ((m : ZMod q)) := by
  have hu : IsUnit ((m.natAbs : ZMod q)) := (ZMod.isUnit_iff_coprime _ _).mpr h
  rcases Int.natAbs_eq m with he | he
  · rw [he]; simpa using hu
  · rw [he]; simpa using hu.neg

/-! ### The recurrence and its `ZMod q` shadow -/

/-- The recurrence (1) of [Dub09] Theorem 4, with `d = k + 1`:
`x_{n+k+1} = c · x_n + F(x_{n+1}, …, x_{n+k})`. -/
def IsReturnRec (k : ℕ) (c : ℤ) (F : (Fin k → ℤ) → ℤ) (x : ℕ → ℤ) : Prop :=
  ∀ n, x (n + k + 1) = c * x n + F fun i => x (n + 1 + (i : ℕ))

/-- `F` descends to `ZMod q`: congruent arguments have congruent values.  Every integer
polynomial has this property (`congrPreserving_mvPolynomial`), and it is all that the proof
of [Dub09] Theorem 4 uses about `F`. -/
def CongrPreserving (q : ℕ) {k : ℕ} (F : (Fin k → ℤ) → ℤ) : Prop :=
  ∀ u v : Fin k → ℤ,
    (∀ i, ((u i : ZMod q)) = ((v i : ZMod q))) → ((F u : ZMod q)) = ((F v : ZMod q))

@[category API, AMS 11, ref "Dub09", group "dubc_return_engine"]
theorem congrPreserving_mvPolynomial {k : ℕ} (q : ℕ) (p : MvPolynomial (Fin k) ℤ) :
    CongrPreserving q (fun u => MvPolynomial.eval u p) := by
  intro u v h
  have hu := MvPolynomial.eval₂_comp_left (Int.castRingHom (ZMod q)) (RingHom.id ℤ) u p
  have hv := MvPolynomial.eval₂_comp_left (Int.castRingHom (ZMod q)) (RingHom.id ℤ) v p
  simp only [MvPolynomial.eval₂_id, RingHom.comp_id, eq_intCast] at hu hv
  simp only []
  rw [hu, hv]
  congr 1
  funext i
  exact h i

/-- A constant `F` (the `d = 1` case, `k = 0`) descends to every `ZMod q`. -/
@[category API, AMS 11, ref "Dub09", group "dubc_return_engine"]
theorem congrPreserving_const (q : ℕ) (b : ℤ) :
    CongrPreserving q (fun _ : Fin 0 → ℤ => b) := fun _ _ _ => rfl

/-- The single congruence carrying both halves of the [Dub09] Theorem 4 argument: if the
window entries `x_{n+1}, …, x_{n+k}` already agree with their `t`-shifts modulo `q`, then the
`(n+k+1)`-st difference is `c` times the `n`-th difference. -/
@[category API, AMS 11, ref "Dub09", group "dubc_return_engine"]
theorem return_step {k : ℕ} {c : ℤ} {F : (Fin k → ℤ) → ℤ} {x : ℕ → ℤ} {q : ℕ}
    (hF : CongrPreserving q F) (hrec : IsReturnRec k c F x) (n t : ℕ)
    (hi : ∀ i : Fin k, ((x (n + 1 + (i : ℕ) + t) : ZMod q)) = ((x (n + 1 + (i : ℕ)) : ZMod q))) :
    ((x (n + k + 1 + t) : ZMod q)) - ((x (n + k + 1) : ZMod q))
      = (c : ZMod q) * (((x (n + t) : ZMod q)) - ((x n : ZMod q))) := by
  have h1 : ((x (n + k + 1) : ZMod q))
      = (c : ZMod q) * ((x n : ZMod q)) + ((F fun i => x (n + 1 + (i : ℕ))) : ZMod q) := by
    rw [hrec n]; push_cast; ring
  have h2 : ((x (n + t + k + 1) : ZMod q))
      = (c : ZMod q) * ((x (n + t) : ZMod q))
        + ((F fun i => x (n + t + 1 + (i : ℕ))) : ZMod q) := by
    rw [hrec (n + t)]; push_cast; ring
  have hFeq : ((F fun i => x (n + t + 1 + (i : ℕ))) : ZMod q)
      = ((F fun i => x (n + 1 + (i : ℕ))) : ZMod q) := by
    refine hF _ _ fun i => ?_
    have hidx : n + t + 1 + (i : ℕ) = n + 1 + (i : ℕ) + t := by omega
    rw [hidx]
    exact hi i
  have hshift : n + k + 1 + t = n + t + k + 1 := by omega
  rw [hshift, h2, h1, hFeq]
  ring

/-! ### [Dub09] Theorem 4: pure periodicity -/

/-- **[Dub09] Theorem 4, first part.**  A solution of the return recurrence
`x_{n+k+1} = c x_n + F(x_{n+1},…,x_{n+k})` is *purely* periodic modulo every `q` for which
`c` is invertible mod `q` (i.e. `gcd(c, q) = 1`): there is a period `T > 0` with
`x_{n+T} ≡ x_n (mod q)` for **all** `n`, with no pre-period. -/
@[category research solved, AMS 11, ref "Dub09", group "dubc_return_engine"]
theorem purely_periodic_mod {k : ℕ} {c : ℤ} {F : (Fin k → ℤ) → ℤ} {x : ℕ → ℤ}
    (q : ℕ) [NeZero q] (hF : CongrPreserving q F) (hrec : IsReturnRec k c F x)
    (hc : IsUnit ((c : ZMod q))) :
    ∃ T, 0 < T ∧ ∀ n, ((x (n + T) : ZMod q)) = ((x n : ZMod q)) := by
  -- The backward step: `c` invertible turns a difference upstairs into one downstairs.
  have hback : ∀ (t ℓ : ℕ),
      (∀ m, ℓ + 1 ≤ m → ((x (m + t) : ZMod q)) = ((x m : ZMod q))) →
      ∀ m, ℓ ≤ m → ((x (m + t) : ZMod q)) = ((x m : ZMod q)) := by
    intro t ℓ h m hm
    rcases hm.lt_or_eq with hlt | heq
    · exact h m (by omega)
    · rw [← heq]
      have hi : ∀ i : Fin k,
          ((x (ℓ + 1 + (i : ℕ) + t) : ZMod q)) = ((x (ℓ + 1 + (i : ℕ)) : ZMod q)) :=
        fun i => h _ (by omega)
      have htop : ((x (ℓ + k + 1 + t) : ZMod q)) = ((x (ℓ + k + 1) : ZMod q)) := h _ (by omega)
      have hst := return_step hF hrec ℓ t hi
      have hz : (c : ZMod q) * (((x (ℓ + t) : ZMod q)) - ((x ℓ : ZMod q)))
          = (c : ZMod q) * 0 := by rw [mul_zero, ← hst, htop, sub_self]
      exact sub_eq_zero.mp (hc.mul_left_cancel hz)
  -- From a period valid beyond `j`, descend to a period valid everywhere.
  have hdown : ∀ (t j : ℕ),
      (∀ m, j ≤ m → ((x (m + t) : ZMod q)) = ((x m : ZMod q))) →
      ∀ m, ((x (m + t) : ZMod q)) = ((x m : ZMod q)) := by
    intro t j
    induction j with
    | zero => exact fun h m => h m (Nat.zero_le m)
    | succ j ih => exact fun h => ih (hback t j h)
  -- The main construction from a repeated window.
  have main : ∀ a b : ℕ, a < b →
      (∀ i : Fin (k + 1), ((x (a + (i : ℕ)) : ZMod q)) = ((x (b + (i : ℕ)) : ZMod q))) →
      ∃ T, 0 < T ∧ ∀ n, ((x (n + T) : ZMod q)) = ((x n : ZMod q)) := by
    intro a b hab hwin
    obtain ⟨t, ht, rfl⟩ : ∃ t, 0 < t ∧ b = a + t := ⟨b - a, by omega, by omega⟩
    refine ⟨t, ht, ?_⟩
    have hbase : ∀ i : ℕ, i ≤ k → ((x (a + i + t) : ZMod q)) = ((x (a + i) : ZMod q)) := by
      intro i hik
      have hw := hwin ⟨i, by omega⟩
      have hidx : a + t + i = a + i + t := by omega
      rw [hidx] at hw
      exact hw.symm
    have hfwd : ∀ m, a ≤ m → ((x (m + t) : ZMod q)) = ((x m : ZMod q)) := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro ham
        by_cases hsmall : m < a + k + 1
        · have hm : m = a + (m - a) := by omega
          rw [hm]
          exact hbase _ (by omega)
        · obtain ⟨n, rfl⟩ : ∃ n, m = n + k + 1 := ⟨m - (k + 1), by omega⟩
          have h0 : ((x (n + t) : ZMod q)) = ((x n : ZMod q)) := ih n (by omega) (by omega)
          have hi : ∀ i : Fin k,
              ((x (n + 1 + (i : ℕ) + t) : ZMod q)) = ((x (n + 1 + (i : ℕ)) : ZMod q)) := by
            intro i
            have hik := i.isLt
            exact ih _ (by omega) (by omega)
          have hst := return_step hF hrec n t hi
          rw [h0, sub_self, mul_zero] at hst
          exact sub_eq_zero.mp hst
    exact hdown t a hfwd
  -- Pigeonhole on the window vectors modulo `q`.
  obtain ⟨n₁, n₂, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ => fun i : Fin (k + 1) => ((x (n + (i : ℕ)) : ZMod q)))
  rcases lt_trichotomy n₁ n₂ with h | h | h
  · exact main n₁ n₂ h fun i => congrFun heq i
  · exact absurd h hne
  · exact main n₂ n₁ h fun i => (congrFun heq i).symm

/-- **[Dub09] Theorem 4, first part**, in the paper's `gcd` formulation. -/
@[category research solved, AMS 11, ref "Dub09", group "dubc_return_engine"]
theorem purely_periodic_mod_of_coprime {k : ℕ} {c : ℤ} {F : (Fin k → ℤ) → ℤ} {x : ℕ → ℤ}
    (q : ℕ) (hq : 0 < q) (hF : CongrPreserving q F) (hrec : IsReturnRec k c F x)
    (hcq : Nat.Coprime c.natAbs q) :
    ∃ T, 0 < T ∧ ∀ n, ((x (n + T) : ZMod q)) = ((x n : ZMod q)) := by
  have : NeZero q := ⟨by omega⟩
  exact purely_periodic_mod q hF hrec (isUnit_intCast_of_coprime hcq)

/-- **[Dub09] Theorem 4, second part.**  A solution of the return recurrence with
`c ≠ 0` and `|x_n| → ∞` contains infinitely many composite terms.

The proof is the paper's: beyond the point where `|x_n| > |c|`, either every term is already
composite, or some term has prime absolute value `q`; that `q` is coprime to `c`, so the
sequence is purely periodic mod `q`, hence `q` divides infinitely many terms — and those
terms eventually exceed `q`, so they are composite. -/
@[category research solved, AMS 11, ref "Dub09", group "dubc_return_engine"]
theorem infinite_composites {k : ℕ} {c : ℤ} {F : (Fin k → ℤ) → ℤ} {x : ℕ → ℤ}
    (hF : ∀ q : ℕ, CongrPreserving q F) (hrec : IsReturnRec k c F x) (hc : c ≠ 0)
    (hlim : Tendsto (fun n => (x n).natAbs) atTop atTop) :
    {n | CompositeInt (x n)}.Infinite := by
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp (hlim.eventually_ge_atTop (c.natAbs + 1))
  by_cases hall : ∀ n, k₀ ≤ n → CompositeInt (x n)
  · refine Set.infinite_of_injective_forall_mem (f := fun j : ℕ => k₀ + j) ?_
      (fun j => hall _ (by omega))
    intro a b hab
    have hab' : k₀ + a = k₀ + b := hab
    omega
  push Not at hall
  obtain ⟨m, hm, hmc⟩ := hall
  have hcabs : c.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hc
  have hbig : c.natAbs + 1 ≤ (x m).natAbs := hk₀ m hm
  set q := (x m).natAbs with hq
  have hq2 : 2 ≤ q := by omega
  have hqp : q.Prime := by
    by_contra h
    exact hmc ⟨hq2, h⟩
  have : NeZero q := ⟨by omega⟩
  -- `q > |c|` forces `q ∤ c`, so `c` is coprime to `q`.
  have hndvd : ¬ (q ∣ c.natAbs) := fun hdvd => by
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  obtain ⟨T, hT, hper⟩ :=
    purely_periodic_mod_of_coprime q (by omega) (hF q) hrec
      (hqp.coprime_iff_not_dvd.mpr hndvd).symm
  -- `q` divides `x m`, hence every term along the arithmetic progression `m + jT`.
  have hzero : ((x m : ZMod q)) = 0 := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ?_
    exact Int.natAbs_dvd.mpr dvd_rfl
  have hdvd : ∀ j : ℕ, (q : ℤ) ∣ x (m + j * T) := by
    intro j
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ?_
    induction j with
    | zero => simpa using hzero
    | succ j ih =>
      have : m + (j + 1) * T = (m + j * T) + T := by ring
      rw [this, hper]
      exact ih
  -- Beyond `J` the terms exceed `q`, so those in the progression are composite.
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (hlim.eventually_ge_atTop (q + 1))
  refine Set.infinite_of_injective_forall_mem (f := fun j : ℕ => m + (J + j) * T) ?_ ?_
  · intro a b hab
    have hab' : m + (J + a) * T = m + (J + b) * T := hab
    have h1 : (J + a) * T = (J + b) * T := by omega
    have := Nat.eq_of_mul_eq_mul_right hT h1
    omega
  · intro j
    refine compositeInt_of_prime_dvd hqp (hdvd (J + j)) ?_
    obtain ⟨T', rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
    have hle : J + j ≤ (J + j) * (T' + 1) := by
      have h1 : (J + j) * 1 ≤ (J + j) * (T' + 1) := Nat.mul_le_mul (le_refl _) (by omega)
      simpa using h1
    exact Nat.lt_of_succ_le (hJ (m + (J + j) * (T' + 1))
      (le_trans (le_trans (Nat.le_add_right J j) hle) (Nat.le_add_left _ m)))

end DubC
