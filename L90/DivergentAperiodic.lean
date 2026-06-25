/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import L90.RationalCycles
import Mathlib.Data.Rat.Lemmas
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Algebra.Order.Archimedean.Basic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Lagarias — Divergent trajectories are aperiodic (Lag90, §2, Corollary 2.1b)

Jeffrey C. Lagarias, *The set of rational cycles for the 3x+1 problem*, Acta Arithmetica **56**
(1990), 33–53, **Corollary 2.1b**.

**Corollary 2.1b.** *Any divergent trajectory must have an aperiodic parity sequence.*

Stated, as in [Lag90], for all `x ∈ Q[(2)] = ℚ ∩ ℤ₂` (the rationals with odd denominator, `L90.Q2`);
the `3x+1` integer trajectories are the special case `x = n ∈ ℕ` (`corollary_2_1b_nat`). The
contrapositive — *an eventually periodic parity sequence forces a non-divergent (finite) orbit* — is
what is actually proved (`not_divergent_of_eventuallyPeriodicParity`), and `corollary_2_1b` is its
restatement.

## The proof, and why it depends on `RationalCycles`

The crux is `periodic_of_periodicParity`: *a point `y ∈ Q[(2)]` whose parity sequence is **purely**
`n`-periodic is itself a period-`n` point of `T`* (`T^[n] y = y`). Its proof is the orbit-difference
form of Lagarias's argument, powered directly by the **affine recurrence**
`L90.two_pow_mul_iterate` (`2ⁿ·Tⁿ(x) = 3^{Σv}·x + S(v)`, the algebraic heart of Theorem 2.1):

* Let `zₖ = T^{nk}(y)`. Every `zₖ` has the same first-`n` parity bits `v`, so the recurrence gives
  `2ⁿ·z_{k+1} = 3^c·zₖ + S` (`c = Σv`, `S = cycleSum`). Subtracting consecutive instances,
  `2ⁿ·d_{k+1} = 3^c·dₖ` for `dₖ := z_{k+1} − zₖ`, hence `2^{nk}·dₖ = 3^{ck}·d₀`.
* Each `zₖ ∈ Q[(2)]` (`T` preserves odd denominators, `T_mem_Q2`), so `dₖ ∈ Q[(2)]` has **odd
  denominator**. Clearing denominators in `2^{nk}·dₖ = 3^{ck}·d₀` and using that `3^{ck}` and the
  denominators are odd forces `2^{nk} ∣ d₀.num` for **every** `k`. A fixed integer divisible by every
  power of `2` is `0`, so `d₀ = T^[n] y − y = 0`.

This is the `2`-adic *valuation trap* of Lagarias's `plan2`, now clean because `RationalCycles`
supplies the recurrence as a finished lemma. It uses **only** elementary integer divisibility — no
`padicValRat`, and crucially **not** the cited realization axiom `L90.xCycle_realizes`. The whole file
is therefore `sorry`-free and rests only on the standard `[propext, Classical.choice, Quot.sound]`.

## Relation to the `B3` capstone

The `2`-adic, integer-`n` form of this corollary is consumed directly inside the report §7.1 capstone
`B3.divergent_imp_not_automatic`, where the periodicity ⟹ non-divergence step is **inlined**:
`corollary_2_1b_nat` is its `ℚ`-side, reached from `B3.parityVector ∈ B3.RatInt` via the orbit bridge
`B3.l90Divergent_of_divergent` and the cited digit-periodicity axiom
`B3.ratInt_imp_eventuallyPeriodicParity`. See `B3/NoDivergence.lean` (and the route comparison in
`B3/plan3-proof.md`).

## References
* [Lag90] Lagarias, Jeffrey C. *The set of rational cycles for the `3x+1` problem.* Acta Arithmetica
  56 (1990), 33–53 (§2, **Corollary 2.1b**; built on Theorem 2.1).
* [BoS78] Böhm, Corrado, and Giovanni Sontacchi. *On the existence of cycles … like `xₙ₊₁ = xₙ/2` …*
  Atti Accad. Naz. Lincei (8) 64 (1978), 260–264 (the cycle formula behind the recurrence).
* [BL96] Bernstein, Daniel J., and Jeffrey C. Lagarias. *The 3x+1 conjugacy map.* Canadian J. Math.
  48 (1996), no. 6, 1154–1169 (parity sequences and divergent trajectories).
-/

namespace L90

open Finset Function

/-! ### Two elementary arithmetic facts -/

/-- A fixed integer divisible by **every** power of `2` is `0`. -/
@[category API, AMS 11, ref "Lag90"]
theorem eq_zero_of_forall_two_pow_dvd {a : ℤ} (h : ∀ k : ℕ, (2:ℤ) ^ k ∣ a) : a = 0 := by
  by_contra ha
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt |a| (by norm_num : (1:ℤ) < 2)
  have hdvd : (2:ℤ) ^ k ∣ |a| := (dvd_abs _ _).mpr (h k)
  have hle : (2:ℤ) ^ k ≤ |a| := Int.le_of_dvd (abs_pos.mpr ha) hdvd
  omega

/-- **Denominator-clearing / valuation step.** If `2ᴺ·u = c·w` with `c` and the denominator of `u`
both **odd**, then `2ᴺ ∣ w.num`. (The factor `2ᴺ` can only sit on `w`'s numerator.) -/
@[category API, AMS 11, ref "Lag90"]
theorem two_pow_dvd_num_of_eq {N : ℕ} {u w : ℚ} {c : ℤ} (hc : Odd c)
    (hu : Odd (u.den : ℤ))
    (heq : (2:ℚ) ^ N * u = (c : ℚ) * w) : (2:ℤ) ^ N ∣ w.num := by
  have hud : ((u.den : ℚ)) ≠ 0 := by exact_mod_cast u.den_nz
  have hwd : ((w.den : ℚ)) ≠ 0 := by exact_mod_cast w.den_nz
  have hun : (u.num : ℚ) = u * (u.den : ℚ) := (div_eq_iff hud).mp (Rat.num_div_den u)
  have hwn : (w.num : ℚ) = w * (w.den : ℚ) := (div_eq_iff hwd).mp (Rat.num_div_den w)
  have hint : (2:ℤ) ^ N * u.num * (w.den : ℤ) = c * w.num * (u.den : ℤ) := by
    have : ((2:ℤ) ^ N * u.num * (w.den : ℤ) : ℚ) = ((c * w.num * (u.den : ℤ) : ℤ) : ℚ) := by
      push_cast
      rw [hun, hwn]; linear_combination ((u.den : ℚ) * (w.den : ℚ)) * heq
    exact_mod_cast this
  have hdvd : (2:ℤ) ^ N ∣ c * w.num * (u.den : ℤ) := ⟨u.num * (w.den : ℤ), by linarith [hint]⟩
  have hcop : IsCoprime ((2:ℤ) ^ N) (c * (u.den : ℤ)) := by
    have ho : Odd (c * (u.den : ℤ)) := hc.mul hu
    have h2 : IsCoprime (2:ℤ) (c * (u.den : ℤ)) := by
      rw [Int.prime_two.coprime_iff_not_dvd, Int.two_dvd_ne_zero]; exact Int.odd_iff.mp ho
    exact h2.pow_left
  have hrw : c * w.num * (u.den : ℤ) = w.num * (c * (u.den : ℤ)) := by ring
  rw [hrw] at hdvd
  exact hcop.dvd_of_dvd_mul_right hdvd

/-! ### `T` preserves `Q[(2)]`; differences stay in `Q[(2)]` -/

/-- **`T` preserves `Q[(2)]`.** If `a` has odd denominator, so does `T a`: `2·T a = a·3^p + p`
(`two_mul_T`) has an **even** numerator (`p = parity a`, `a.den` odd), and dividing by `2` leaves the
odd denominator `a.den` intact. -/
@[category API, AMS 11 37, ref "Lag90" "BL96"]
theorem T_mem_Q2 {a : ℚ} (ha : a ∈ Q2) : T a ∈ Q2 := by
  rw [Q2, Set.mem_setOf_eq] at ha ⊢
  have hd0 : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_nz
  have h2 : (2:ℤ) ∣ a.num * 3 ^ (parity a) + (parity a : ℤ) * a.den := by
    rcases Int.even_or_odd a.num with he | ho
    · have hp0 : parity a = 0 := by unfold parity; rw [Int.even_iff.mp he]; rfl
      rw [hp0]; simp only [pow_zero, mul_one, Nat.cast_zero, zero_mul, add_zero]
      exact he.two_dvd
    · have hp1 : parity a = 1 := by unfold parity; rw [Int.odd_iff.mp ho]; rfl
      rw [hp1]; simp only [pow_one, Nat.cast_one, one_mul]
      have h1 : a.num % 2 = 1 := Int.odd_iff.mp ho
      have h2' : (a.den : ℤ) % 2 = 1 := Int.odd_iff.mp ((Int.odd_coe_nat a.den).mpr ha)
      omega
  obtain ⟨q, hq⟩ := h2
  have e2 := two_mul_T a
  have ea : (a.num : ℚ) = a * (a.den : ℚ) := (div_eq_iff hd0).mp (Rat.num_div_den a)
  have hqQ : (2:ℚ) * (q:ℚ) = (a.num:ℚ) * 3 ^ (parity a) + (parity a:ℚ) * (a.den:ℚ) := by
    exact_mod_cast hq.symm
  have hTaval : T a * (a.den:ℚ) = (q:ℚ) := by
    have hh : (2:ℚ) * (T a * (a.den:ℚ)) = 2 * (q:ℚ) := by
      rw [hqQ, ea]; linear_combination (a.den:ℚ) * e2
    linarith
  have hTeq : T a = Rat.divInt q (a.den:ℤ) := by
    rw [Rat.divInt_eq_div, Int.cast_natCast, eq_div_iff hd0]; exact hTaval
  have hdvd : ((T a).den : ℤ) ∣ (a.den : ℤ) := hTeq ▸ Rat.den_dvd q (a.den:ℤ)
  obtain ⟨t, ht⟩ := Int.natCast_dvd_natCast.mp hdvd
  rw [ht] at ha
  exact (Nat.odd_mul.mp ha).1

/-- Every iterate `T^[m] x` stays in `Q[(2)]`. -/
@[category API, AMS 11 37, ref "Lag90"]
theorem iterate_mem_Q2 {x : ℚ} (hx : x ∈ Q2) (m : ℕ) : T^[m] x ∈ Q2 := by
  induction m with
  | zero => simpa using hx
  | succ m ih => rw [Function.iterate_succ_apply']; exact T_mem_Q2 ih

/-- `Q[(2)]` is closed under subtraction: a difference of odd-denominator rationals has odd
denominator (`(a − b).den ∣ a.den · b.den`). -/
@[category API, AMS 11 37, ref "Lag90"]
theorem Q2_sub {a b : ℚ} (ha : Odd a.den) (hb : Odd b.den) : Odd (a - b).den := by
  obtain ⟨k, hk⟩ := Rat.sub_den_dvd a b
  exact (Nat.odd_mul.mp (hk ▸ ha.mul hb)).1

/-! ### Trajectories, divergence, and eventually periodic parity -/

/-- The **trajectory** (orbit) of `x` under the `3x+1` map `T`. -/
@[category API, AMS 11 37, ref "Lag90" "BL96"]
def orbit (x : ℚ) : Set ℚ := Set.range fun k => T^[k] x

/-- `x` has a **divergent trajectory**: its orbit under `T` is infinite. (For these maps an
unbounded orbit is exactly an infinite one.) -/
@[category API, AMS 11 37, ref "Lag90" "BL96"]
def Divergent (x : ℚ) : Prop := (orbit x).Infinite

/-- The parity sequence `bⱼ(x) = parity (Tʲ x)` of `x` is **eventually periodic**: it is periodic of
some period `n > 0` from some index `m` on. Its negation is "*aperiodic parity sequence*". -/
@[category API, AMS 11 37, ref "Lag90" "BL96"]
def EventuallyPeriodicParity (x : ℚ) : Prop :=
  ∃ m n, 0 < n ∧ ∀ j, m ≤ j → parity (T^[j + n] x) = parity (T^[j] x)

/-- A period-`n` point of `T` has a **finite** orbit (it is `{T^[i] y : i < n}`). -/
@[category API, AMS 11 37, ref "Lag90"]
theorem orbit_finite_of_periodic {y : ℚ} {n : ℕ} (hn : 0 < n) (hper : T^[n] y = y) :
    (orbit y).Finite := by
  apply Set.Finite.subset ((Finset.range n).image (fun i => T^[i] y)).finite_toSet
  rintro _ ⟨k, rfl⟩
  dsimp only
  have hpp : Function.IsPeriodicPt T n y := hper
  rw [← hpp.iterate_mod_apply k]
  exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨k % n, Finset.mem_range.mpr (Nat.mod_lt _ hn), rfl⟩)

/-! ### The crux: a purely periodic parity sequence forces a cycle -/

/-- **The crux of Corollary 2.1b.** A point `y ∈ Q[(2)]` whose parity sequence is **purely**
`n`-periodic (`parity (T^{j+n} y) = parity (Tʲ y)` for *all* `j`) is a period-`n` point: `T^[n] y = y`.

*Proof.* With `zₖ := T^{nk} y` and `v` the common parity block, the affine recurrence
`two_pow_mul_iterate` gives `2ⁿ·z_{k+1} = 3^{Σv}·zₖ + S(v)`; subtracting consecutive instances and
iterating yields `2^{nk}·(z_{k+1} − zₖ) = 3^{(Σv)k}·(T^[n] y − y)`. As each `zₖ ∈ Q[(2)]` has odd
denominator, clearing denominators forces `2^{nk} ∣ (T^[n] y − y).num` for all `k`, so the fixed
numerator is `0`. -/
@[category research solved, AMS 11 37, ref "Lag90" "BoS78", group "lag90_rational_cycles"]
theorem periodic_of_periodicParity {y : ℚ} {n : ℕ} (hy : y ∈ Q2) (hn : 0 < n)
    (hper : ∀ j, parity (T^[j + n] y) = parity (T^[j] y)) : T^[n] y = y := by
  set c := totalOdd n (fun j => parity (T^[j] y)) with hc_def
  set S := cycleSum n (fun j => parity (T^[j] y)) with hS_def
  have hodd : ∀ m, Odd (T^[m] y).den := fun m => iterate_mem_Q2 hy m
  -- the parity block repeats along the whole orbit
  have prop : ∀ k j, parity (T^[n * k + j] y) = parity (T^[j] y) := by
    intro k; induction k with
    | zero => intro j; simp only [Nat.mul_zero, Nat.zero_add]
    | succ k ih =>
      intro j
      rw [show n * (k + 1) + j = n * k + (n + j) from by ring, ih (n + j), add_comm n j]
      exact hper j
  -- the affine recurrence along the sub-orbit `zₖ = T^{nk} y`
  have R : ∀ k, (2:ℚ) ^ n * T^[n * (k + 1)] y = 3 ^ c * T^[n * k] y + S := by
    intro k
    have hpar : ∀ j < n, parity (T^[j] (T^[n * k] y)) = parity (T^[j] y) := by
      intro j _
      rw [← Function.iterate_add_apply, add_comm j (n * k)]; exact prop k j
    have key := two_pow_mul_iterate n (fun j => parity (T^[j] y)) (T^[n * k] y) hpar
    rw [← Function.iterate_add_apply, show n + n * k = n * (k + 1) from by ring] at key
    exact key
  -- iterate the recurrence on the differences
  have P : ∀ k, (2:ℚ) ^ (n * k) * (T^[n * (k + 1)] y - T^[n * k] y)
      = (3:ℚ) ^ (c * k) * (T^[n] y - y) := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
      linear_combination (2:ℚ) ^ (n * k) * R (k + 1) - (2:ℚ) ^ (n * k) * R k + (3:ℚ) ^ c * ih
  -- every power of two divides the (fixed) numerator of `T^[n] y - y`
  have hdvd : ∀ k, (2:ℤ) ^ (n * k) ∣ (T^[n] y - y).num := by
    intro k
    have hu : Odd ((T^[n * (k + 1)] y - T^[n * k] y).den) := Q2_sub (hodd (n * (k + 1))) (hodd (n * k))
    refine two_pow_dvd_num_of_eq (u := T^[n * (k + 1)] y - T^[n * k] y) (w := T^[n] y - y)
      (c := (3:ℤ) ^ (c * k)) ((by decide : Odd (3:ℤ)).pow)
      ((Int.odd_coe_nat _).mpr hu) ?_
    rw [P k]; push_cast; ring
  have hall : ∀ m, (2:ℤ) ^ m ∣ (T^[n] y - y).num :=
    fun m => dvd_trans (pow_dvd_pow 2 (Nat.le_mul_of_pos_left m hn)) (hdvd m)
  have h0 : T^[n] y - y = 0 := Rat.num_eq_zero.mp (eq_zero_of_forall_two_pow_dvd hall)
  linarith [sub_eq_zero.mp h0]

/-! ### Corollary 2.1b -/

/-- A period-`n` point is not divergent (its orbit is finite). -/
@[category research solved, AMS 11 37, ref "Lag90", group "lag90_rational_cycles"]
theorem not_divergent_of_periodic {y : ℚ} {n : ℕ} (hn : 0 < n) (hper : T^[n] y = y) :
    ¬ Divergent y := by
  rw [Divergent, Set.not_infinite]
  exact orbit_finite_of_periodic hn hper

/-- **Corollary 2.1b (contrapositive form).** A point `x ∈ Q[(2)]` with an **eventually periodic**
parity sequence has a non-divergent (finite) trajectory.

*Proof.* Shift to `y = T^[m] x`, whose parity is **purely** periodic; `periodic_of_periodicParity`
makes `y` a cycle, so its orbit is finite, and the orbit of `x` is the finite head
`{T^[k] x : k < m}` together with the orbit of `y`. -/
@[category research solved, AMS 11 37, ref "Lag90" "BL96", group "lag90_rational_cycles"]
theorem not_divergent_of_eventuallyPeriodicParity {x : ℚ} (hx : x ∈ Q2)
    (h : EventuallyPeriodicParity x) : ¬ Divergent x := by
  obtain ⟨m, n, hn, hperiod⟩ := h
  have hpure : ∀ j, parity (T^[j + n] (T^[m] x)) = parity (T^[j] (T^[m] x)) := by
    intro j
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply,
        show j + n + m = (j + m) + n from by ring]
    exact hperiod (j + m) (Nat.le_add_left m j)
  have hper : T^[n] (T^[m] x) = T^[m] x :=
    periodic_of_periodicParity (iterate_mem_Q2 hx m) hn hpure
  have hfiny : (orbit (T^[m] x)).Finite := orbit_finite_of_periodic hn hper
  rw [Divergent, Set.not_infinite]
  apply Set.Finite.subset
    (Set.Finite.union (Finset.finite_toSet ((Finset.range m).image (fun k => T^[k] x))) hfiny)
  rintro _ ⟨k, rfl⟩
  dsimp only
  rcases lt_or_ge k m with hk | hk
  · exact Or.inl (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩))
  · refine Or.inr ⟨k - m, ?_⟩
    show T^[k - m] (T^[m] x) = T^[k] x
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hk]

/-- **Corollary 2.1b (Lagarias 1990, §2).** *Any divergent trajectory must have an aperiodic parity
sequence.* For `x ∈ Q[(2)]`: if the orbit of `x` under `T` is infinite, its parity sequence is **not**
eventually periodic. -/
@[category research solved, AMS 11 37, ref "Lag90" "BL96", group "lag90_rational_cycles"]
theorem corollary_2_1b {x : ℚ} (hx : x ∈ Q2) (hdiv : Divergent x) :
    ¬ EventuallyPeriodicParity x :=
  fun h => not_divergent_of_eventuallyPeriodicParity hx h hdiv

/-- The `L90` trajectory of a natural number **is** the integer `3x+1` trajectory: `L90.Tᵏ(↑n) =
↑(Tᵏ n)` (iterating `T_natCast`). The bridge that turns an integer `3x+1` orbit into an `L90.T` orbit
on `ℚ` (used by `B3` to feed `corollary_2_1b_nat`). -/
@[category API, AMS 11 37, ref "Lag90" "BL96"]
theorem T_iterate_natCast (k n : ℕ) :
    T^[k] (n : ℚ) = ((CC.T^[k] n : ℕ) : ℚ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, T_natCast,
        Function.iterate_succ_apply' CC.T k n]

/-- **Corollary 2.1b for integer `3x+1` trajectories.** A divergent trajectory of a natural number
`n` (viewed in `Q[(2)]`) has an aperiodic parity sequence — the `ℚ`-side consumed by the report §7.1
capstone `B3.divergent_imp_not_automatic` (which inlines the periodicity ⟹ non-divergence step). -/
@[category research solved, AMS 11 37, ref "Lag90" "BL96", group "lag90_rational_cycles"]
theorem corollary_2_1b_nat (n : ℕ) (hdiv : Divergent (n : ℚ)) :
    ¬ EventuallyPeriodicParity (n : ℚ) := by
  refine corollary_2_1b ?_ hdiv
  rw [Q2, Set.mem_setOf_eq, Rat.den_natCast]
  exact odd_one

end L90
