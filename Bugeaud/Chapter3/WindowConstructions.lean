/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Bugeaud.Chapter3.ReverseCarry
import ForMathlib.Data.Real.NearestInt

/-!
# Bugeaud, Chapter 3, §3.6 — the window constructions of Dubickas

Yann Bugeaud, *Distribution Modulo One and Diophantine Approximation* (Cambridge Tracts in
Mathematics 193, 2012), **Theorem 3.18** and the second and third assertions of **Theorem
3.16**, both due to Dubickas [Dub06].

All three come from the same source, `Bugeaud.exists_window_orbit`: feeding the reverse carry
construction of `Bugeaud/Chapter3/ReverseCarry.lean` a window `A = {c, c+1, …, c+q-1}` of `q`
consecutive integers produces a real number `ξ > 0` whose *entire* orbit satisfies

  `ξ (p/q)ⁿ = xₙ + yₙ`,  `xₙ ∈ ℤ`,  `c/(p-q) < yₙ < (c+q-1)/(p-q)`.

Sliding the window then places the orbit where one wants it:

* `c = t` for `0 ≤ t ≤ p - 2q` traps `{ξ(p/q)ⁿ}` in `(t/(p-q), (t+q-1)/(p-q))` — **Theorem 3.18**;
* the window centred at `0` makes `‖ξ(p/q)ⁿ‖` *small* — Theorem 3.16, second assertion;
* the window centred at `1/2` makes `‖ξ(p/q)ⁿ‖` *large* — Theorem 3.16, third assertion
  (Exercise 3.7 in the book).

The first assertion of Theorem 3.16 (`‖ξ(p/2)ⁿ‖ < 1/p` for odd `p`) needs an alphabet of `q + 1`
letters and the *freedom* in the carry choice; it is proved in
`Bugeaud/Chapter3/AlternatingConstruction.lean`.

## Deviations from the book

* Bugeaud states the second and third assertions of Theorem 3.16 for arbitrary `p > 2q ≥ 4`.  The
  *strict* inequalities there rest on Lemma 3.17, which assumes `gcd(p, q) = 1`; we carry that
  hypothesis explicitly.  (It is harmless: the general case reduces to it by cancelling
  `gcd(p, q)`, which changes neither `p/q` nor the orbit.)
* Lemma 3.17 itself (only finitely many `n` with `{ξ(p/q)ⁿ} = t`, Exercise 3.6) is not needed:
  the extreme value of the window trap is attained only by a *constant* carry word, and a
  constant carry word forces `ξ = 0` by the `q`-adic descent
  `Bugeaud.carryXi_eq_zero_of_eventually_const`.
* Bugeaud writes the bounds with `δₘ = 1` for odd `m` and `δₘ = 0` for even `m`.  Here they read
  `⌊q/2⌋/(p-q)` and `⌊(p-2q+1)/2⌋/(p-q)`, which are the same numbers:
  `⌊q/2⌋ = (q - δ_q)/2` and `⌊(p-2q+1)/2⌋ = (p - 2q + δ_p)/2`.

## References

* [Bug12] Y. Bugeaud, *Distribution Modulo One and Diophantine Approximation*, Cambridge Tracts
  in Mathematics 193, Cambridge University Press, 2012, §3.6.
* [Dub06] A. Dubickas, *Arithmetical properties of powers of algebraic numbers*, Bull. London
  Math. Soc. **38** (2006), 70–80 — reference [248] of [Bug12].
-/

namespace Bugeaud

open ForMathlib

variable {p q : ℕ}

/-! ## The window trap -/

/-- **The window trap.**  For coprime `p > q ≥ 2` and any window `{c, …, c+q-1}` of `q`
consecutive integers that is short enough to keep the tail values inside `(-1, 1)`, the reverse
carry construction produces a real number `ξ > 0` together with integers `xₙ` such that
`ξ (p/q)ⁿ - xₙ` lies strictly between `c/(p-q)` and `(c+q-1)/(p-q)` for **every** `n`.

Strictness is where coprimality enters: an endpoint would force the carry word to be eventually
constant (`Bugeaud.eq_of_carryTail_eq_ge`), hence `ξ = 0`
(`Bugeaud.carryXi_eq_zero_of_eventually_const`). -/
@[category API, AMS 11, ref "Bug12", group "bug_3_16",
  formal_uses exists_carry, formal_uses carryXi_eq_zero_of_eventually_const]
theorem exists_window_orbit (hq : 2 ≤ q) (hqp : q < p) (hcop : Nat.Coprime p q) {c : ℤ}
    (hlo : -((p : ℤ) - q) < c) (hhi : c + q - 1 < (p : ℤ) - q) :
    ∃ (ξ : ℝ) (y : ℕ → ℝ) (x : ℕ → ℤ), 0 < ξ ∧
      (∀ n, ξ * ((p : ℝ) / q) ^ n = (x n : ℝ) + y n) ∧
      (∀ n, (c : ℝ) / ((p : ℝ) - q) < y n) ∧
      (∀ n, y n < ((c : ℝ) + q - 1) / ((p : ℝ) - q)) := by
  have hq0 : 0 < q := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hq0.trans hqp
  have hqR : (q : ℝ) < p := by exact_mod_cast hqp
  have hpq : (0 : ℝ) < (p : ℝ) - q := by linarith
  obtain ⟨x, s, hx0, hmem, hrec⟩ := exists_carry p hq0 c 1
  have hs : ∀ k, |s k| ≤ |c| + (q : ℤ) := abs_le_of_mem_Ico hmem
  have hlow : ∀ m, c ≤ s m := fun m => (Set.mem_Ico.mp (hmem m)).1
  have hhigh : ∀ m, s m ≤ c + q - 1 := fun m => by
    have := (Set.mem_Ico.mp (hmem m)).2; omega
  -- the two closed bounds
  have hb1 : ∀ n, (c : ℝ) / ((p : ℝ) - q) ≤ carryTail p q s n := fun n =>
    le_carryTail hq0 hqp hs fun m _ => hlow m
  have hb2 : ∀ n, carryTail p q s n ≤ ((c : ℝ) + q - 1) / ((p : ℝ) - q) := fun n => by
    have := carryTail_le (n := n) (c := c + q - 1) hq0 hqp hs fun m _ => hhigh m
    push_cast at this
    linarith
  -- the window is short enough that `|yₙ| < 1`
  have hgt : (-1 : ℝ) < (c : ℝ) / ((p : ℝ) - q) := by
    rw [lt_div_iff₀ hpq]
    have : ((-((p : ℤ) - q) : ℤ) : ℝ) < ((c : ℤ) : ℝ) := by exact_mod_cast hlo
    push_cast at this
    linarith
  have hlt : ((c : ℝ) + q - 1) / ((p : ℝ) - q) < 1 := by
    rw [div_lt_one hpq]
    have : ((c + q - 1 : ℤ) : ℝ) < (((p : ℤ) - q : ℤ) : ℝ) := by exact_mod_cast hhi
    push_cast at this
    linarith
  -- hence `ξ = 1 + y₀ > 0`
  have hpos : 0 < carryXi p q x s := by
    have h0 := hb1 0
    have h1 := hb2 0
    rw [carryXi, hx0]
    push_cast
    linarith
  refine ⟨carryXi p q x s, carryTail p q s, x, hpos,
    fun n => carryXi_mul_pow hq0 hqp hs hrec n, fun n => ?_, fun n => ?_⟩
  · rcases lt_or_eq_of_le (hb1 n) with h | h
    · exact h
    · exact absurd (carryXi_eq_zero_of_eventually_const hq hqp hcop hs hrec
        (eq_of_carryTail_eq_ge hq0 hqp hs (fun m _ => hlow m) h.symm)) (ne_of_gt hpos)
  · rcases lt_or_eq_of_le (hb2 n) with h | h
    · exact h
    · have heq : carryTail p q s n = ((c + q - 1 : ℤ) : ℝ) / ((p : ℝ) - q) := by
        rw [h]; push_cast; ring
      exact absurd (carryXi_eq_zero_of_eventually_const hq hqp hcop hs hrec
        (eq_of_carryTail_eq_le (n := n) hq0 hqp hs (fun m _ => hhigh m) heq)) (ne_of_gt hpos)

/-! ## Theorem 3.18 -/

/-- **Theorem 3.18** (Dubickas; essentially Flatto).  Let `p, q` be coprime with `q ≥ 2` and
`p > 2q`, and let `0 ≤ t ≤ p - 2q`.  Then some non-zero real `ξ` has

  `t/(p-q) < {ξ (p/q)ⁿ} < (t+q-1)/(p-q)`  for every `n ≥ 0`. -/
@[category research solved, AMS 11, ref "Bug12", group "bug_3_18",
  formal_uses exists_window_orbit]
theorem theorem_3_18 (hq : 2 ≤ q) (hp : 2 * q < p) (hcop : Nat.Coprime p q) {t : ℤ}
    (ht0 : 0 ≤ t) (ht : t ≤ (p : ℤ) - 2 * q) :
    ∃ ξ : ℝ, ξ ≠ 0 ∧ ∀ n : ℕ, Int.fract (ξ * ((p : ℝ) / q) ^ n) ∈
      Set.Ioo ((t : ℝ) / ((p : ℝ) - q)) (((t : ℝ) + q - 1) / ((p : ℝ) - q)) := by
  have hqp : q < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hqR : (q : ℝ) < p := by exact_mod_cast hqp
  have hpq : (0 : ℝ) < (p : ℝ) - q := by linarith
  obtain ⟨ξ, y, x, hξ, horb, hylo, hyhi⟩ :=
    exists_window_orbit hq hqp hcop (c := t) (by omega) (by omega)
  refine ⟨ξ, ne_of_gt hξ, fun n => ?_⟩
  have h0 : (0 : ℝ) ≤ (t : ℝ) / ((p : ℝ) - q) := by
    have : (0 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht0
    positivity
  have h1 : ((t : ℝ) + q - 1) / ((p : ℝ) - q) < 1 := by
    rw [div_lt_one hpq]
    have : ((t : ℤ) : ℝ) ≤ ((p : ℤ) : ℝ) - 2 * (q : ℤ) := by exact_mod_cast ht
    push_cast at this
    linarith
  have hfract : Int.fract (ξ * ((p : ℝ) / q) ^ n) = y n := by
    rw [horb n, Int.fract_intCast_add, Int.fract_eq_self]
    exact ⟨by linarith [hylo n], by linarith [hyhi n]⟩
  rw [hfract]
  exact ⟨hylo n, hyhi n⟩

/-- **Theorem 3.18**, last statement: for every odd `p ≥ 5` there is a non-zero real `ξ` with
`{ξ (p/2)ⁿ} < 1/(p-2)` for all `n ≥ 0`.  (Tijdeman had proved this with `≤`.) -/
@[category research solved, AMS 11, ref "Bug12", group "bug_3_18", formal_uses theorem_3_18]
theorem theorem_3_18_half {p : ℕ} (hp : 5 ≤ p) (hodd : Odd p) :
    ∃ ξ : ℝ, ξ ≠ 0 ∧ ∀ n : ℕ, 0 < Int.fract (ξ * ((p : ℝ) / 2) ^ n) ∧
      Int.fract (ξ * ((p : ℝ) / 2) ^ n) < 1 / ((p : ℝ) - 2) := by
  have hcop : Nat.Coprime p 2 := Nat.coprime_two_right.mpr hodd
  obtain ⟨ξ, hξ, hmem⟩ := theorem_3_18 (q := 2) (p := p) le_rfl (by omega) hcop
    (t := 0) le_rfl (by omega)
  refine ⟨ξ, hξ, fun n => ?_⟩
  have h := hmem n
  simp only [Set.mem_Ioo] at h
  push_cast at h
  constructor
  · simpa using h.1
  · have : ((0 : ℝ) + 2 - 1) / ((p : ℝ) - 2) = 1 / ((p : ℝ) - 2) := by ring_nf
    linarith [h.2, this.symm.le, this.le]

/-! ## Theorem 3.16, second and third assertions -/

/-- Bugeaud's `δ`-notation, made explicit: `⌊q/2⌋ = (q - δ_q)/2`, i.e. `2⌊q/2⌋` is `q` for even
`q` and `q - 1` for odd `q`. -/
@[category API, AMS 11, ref "Bug12", group "bug_3_16"]
theorem two_mul_half_eq (q : ℕ) : 2 * (q / 2) = q ∨ 2 * (q / 2) + 1 = q := by omega

/-- **Theorem 3.16**, second assertion (Dubickas).  For coprime `p > 2q ≥ 4` there is a non-zero
real `ξ` with `‖ξ (p/q)ⁿ‖ < ⌊q/2⌋/(p-q) = (q - δ_q)/(2(p-q))` for every `n ≥ 0`.

The window is `{⌊q/2⌋ - q + 1, …, ⌊q/2⌋}`, i.e. the `q` consecutive integers centred at `0`. -/
@[category research solved, AMS 11, ref "Bug12", group "bug_3_16",
  formal_uses exists_window_orbit]
theorem theorem_3_16_small (hq : 2 ≤ q) (hp : 2 * q < p) (hcop : Nat.Coprime p q) :
    ∃ ξ : ℝ, ξ ≠ 0 ∧ ∀ n : ℕ,
      distToNearestInt (ξ * ((p : ℝ) / q) ^ n) < ((q / 2 : ℕ) : ℝ) / ((p : ℝ) - q) := by
  have hqp : q < p := by omega
  have hqR : (q : ℝ) < p := by exact_mod_cast hqp
  have hpq : (0 : ℝ) < (p : ℝ) - q := by linarith
  set d : ℕ := q / 2 with hdd
  have hd1 : 2 * d ≤ q := by omega
  have hd2 : q ≤ 2 * d + 1 := by omega
  clear_value d
  obtain ⟨ξ, y, x, hξ, horb, hylo, hyhi⟩ :=
    exists_window_orbit hq hqp hcop (c := (d : ℤ) - q + 1)
      (by omega) (by omega)
  refine ⟨ξ, ne_of_gt hξ, fun n => ?_⟩
  -- `|yₙ| < ⌊q/2⌋/(p-q)`, and `‖xₙ + yₙ‖ ≤ |yₙ|`
  have hup : y n < (d : ℝ) / ((p : ℝ) - q) := by
    have h := hyhi n
    have heq : ((((d : ℤ) - q + 1 : ℤ) : ℝ)) + q - 1 = (d : ℝ) := by push_cast; ring
    rw [heq] at h
    exact h
  have hdown : -((d : ℝ) / ((p : ℝ) - q)) < y n := by
    refine lt_of_le_of_lt ?_ (hylo n)
    rw [← neg_div, div_le_div_iff_of_pos_right hpq]
    have hR : (q : ℝ) ≤ 2 * (d : ℝ) + 1 := by exact_mod_cast hd2
    push_cast
    linarith
  calc distToNearestInt (ξ * ((p : ℝ) / q) ^ n)
      ≤ |ξ * ((p : ℝ) / q) ^ n - (x n : ℝ)| := distToNearestInt_le_abs_sub_intCast _ _
    _ = |y n| := by rw [horb n]; congr 1; ring
    _ < (d : ℝ) / ((p : ℝ) - q) := abs_lt.mpr ⟨hdown, hup⟩

/-- **Theorem 3.16**, third assertion (Exercise 3.7 in the book).  For coprime `p > 2q ≥ 4`
there is a non-zero real `ξ` with
`‖ξ (p/q)ⁿ‖ > ⌊(p-2q+1)/2⌋/(p-q) = (p - 2q + δ_p)/(2(p-q))` for every `n ≥ 0`.

The window is `{a, …, a+q-1}` with `a = ⌊(p-2q+1)/2⌋`, i.e. the `q` consecutive integers whose
tail values straddle `1/2`. -/
@[category research solved, AMS 11, ref "Bug12", group "bug_3_16",
  formal_uses exists_window_orbit]
theorem theorem_3_16_large (hq : 2 ≤ q) (hp : 2 * q < p) (hcop : Nat.Coprime p q) :
    ∃ ξ : ℝ, ξ ≠ 0 ∧ ∀ n : ℕ,
      (((p - 2 * q + 1) / 2 : ℕ) : ℝ) / ((p : ℝ) - q)
        < distToNearestInt (ξ * ((p : ℝ) / q) ^ n) := by
  have hqp : q < p := by omega
  have hqR : (q : ℝ) < p := by exact_mod_cast hqp
  have hpq : (0 : ℝ) < (p : ℝ) - q := by linarith
  set a : ℕ := (p - 2 * q + 1) / 2 with ha
  have ha1 : 1 ≤ a := by omega
  have ha2 : 2 * a + 2 * q ≤ p + 1 := by omega
  have ha3 : a + 2 * q ≤ p := by omega
  clear_value a
  obtain ⟨ξ, y, x, hξ, horb, hylo, hyhi⟩ :=
    exists_window_orbit hq hqp hcop (c := (a : ℤ)) (by omega) (by omega)
  refine ⟨ξ, ne_of_gt hξ, fun n => ?_⟩
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha1
  have hlow : (a : ℝ) / ((p : ℝ) - q) < y n := by
    have h := hylo n; push_cast at h; exact h
  have hhigh : y n < ((a : ℝ) + q - 1) / ((p : ℝ) - q) := by
    have h := hyhi n; push_cast at h; exact h
  -- the window straddles `1/2`: `(a+q-1)/(p-q) ≤ 1 - a/(p-q)`
  have hmid : ((a : ℝ) + q - 1) / ((p : ℝ) - q) ≤ 1 - (a : ℝ) / ((p : ℝ) - q) := by
    rw [div_le_iff₀ hpq]
    have hR : 2 * (a : ℝ) + 2 * (q : ℝ) ≤ (p : ℝ) + 1 := by exact_mod_cast ha2
    have hne : ((p : ℝ) - q) ≠ 0 := ne_of_gt hpq
    field_simp
    linarith
  have hy0 : 0 < y n := lt_trans (by positivity) hlow
  have hy1 : y n < 1 := by
    have : (0 : ℝ) < (a : ℝ) / ((p : ℝ) - q) := by positivity
    linarith [hhigh, hmid]
  calc (a : ℝ) / ((p : ℝ) - q) < min (y n) (1 - y n) := by
        refine lt_min hlow ?_
        linarith [hhigh, hmid]
    _ ≤ distToNearestInt (y n) := min_le_distToNearestInt _
    _ = distToNearestInt (ξ * ((p : ℝ) / q) ^ n) := by
        rw [horb n, add_comm, distToNearestInt_add_intCast]

end Bugeaud
