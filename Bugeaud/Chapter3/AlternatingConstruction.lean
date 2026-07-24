/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Bugeaud.Chapter3.ReverseCarry
import ForMathlib.Data.Real.NearestInt

/-!
# Bugeaud, Chapter 3, §3.6 — Theorem 3.16, first assertion

Yann Bugeaud, *Distribution Modulo One and Diophantine Approximation* (Cambridge Tracts in
Mathematics 193, 2012), **Theorem 3.16**, first assertion (Dubickas [Dub06]):

> For every odd integer `p ≥ 3` there exists a non-zero real number `ξ` such that
> `‖ξ (p/2)ⁿ‖ < 1/p` for every `n ≥ 0`.

Unlike the window constructions of `Bugeaud/Chapter3/WindowConstructions.lean`, this one uses an
alphabet of **three** letters for `q = 2`, namely `A = {-1, 0, 1}`, and exploits the resulting
*freedom*: the congruence `2 ∣ p xₙ + sₙ` forces `sₙ = 0` when `xₙ` is even but leaves the choice
`sₙ = ±1` when `xₙ` is odd.  Making the non-zero letters **alternate in sign** — Bugeaud's
`0^{k₁} 1 0^{k₂} (-1) 0^{k₃} 1 …` — produces enough cancellation in

  `Tₙ := ∑_{j ≥ 0} s_{n+j} (2/p)ʲ`   (so that `yₙ = Tₙ/p`)

that `|Tₙ| ≤ 1`, i.e. `|yₙ| ≤ 1/p`, whereas the crude bound `∑ (2/p)ʲ = p/(p-2)` is useless.

## Proof of the bound

Let `σₙ = ±1` record the sign the next non-zero letter must carry.  The invariant

  `0 ≤ σₙ · ∑_{j < N} s_{n+j} (2/p)ʲ ≤ 1`   for all `N` and `n`

is proved by induction on the truncation length `N` (`Bugeaud.altSgn_mul_partialTail_mem_Icc`),
using `∑_{j<N+1} = sₙ + (2/p) ∑_{j<N}` from position `n+1`: if `sₙ = 0` the sign does not flip
and the value is `(2/p)·[0,1] ⊆ [0,1]`; if `sₙ = σₙ` the sign flips, so the tail contributes with
the *opposite* sign and the value is `1 + (2/p)·[-1,0] ⊆ [1-2/p, 1]`.  Since `[0,1]` is closed
the invariant passes to the limit (`ForMathlib.tailSeries_le_of_partialTail_le`).

This inductive-invariant-plus-limit route replaces the informal "it follows that all the `yₙ`
belong to `[-1/p, 1/p]`" of the book, which is an alternating-series estimate on the sub-word of
non-zero letters.

## Strictness

`|Tₙ| = 1` forces `σₙ Tₙ = 1`; the recursion then forces `T_{n+1} = 0`, and `Tₘ = 0` propagates
(`Bugeaud.altLetter_eq_zero_of_tail_eq_zero`) to `sₘ = 0` for all `m ≥ n+1`.  An eventually zero
carry word has `ξ = 0` by `Bugeaud.carryXi_eq_zero_of_eventually_const`, contradicting `ξ > 0`.
Bugeaud instead invokes Lemma 3.17; the descent is self-contained.

## References

* [Bug12] Y. Bugeaud, *Distribution Modulo One and Diophantine Approximation*, Cambridge Tracts
  in Mathematics 193, Cambridge University Press, 2012, §3.6, Theorem 3.16.
* [Dub06] A. Dubickas, *Arithmetical properties of powers of algebraic numbers*, Bull. London
  Math. Soc. **38** (2006), 70–80 — reference [248] of [Bug12].
* [AFS08] S. Akiyama, C. Frougny, J. Sakarovitch, *Powers of rationals modulo 1 and rational
  base number systems*, Israel J. Math. **168** (2008), 53–91 — reference [33] of [Bug12]:
  for `p = 3` the set of such `ξ > 0` is infinite and countable.
-/

namespace Bugeaud

open ForMathlib

variable {p : ℕ} {x₀ : ℤ}

/-! ## The sign-alternating carry construction (`q = 2`) -/

/-- One step of the alternating construction.  The state is `(xₙ, σₙ)`: when `xₙ` is even the
letter is `0` and the sign is kept, when `xₙ` is odd the letter is `σₙ` and the sign flips. -/
def altStep (p : ℕ) (v : ℤ × ℤ) : ℤ × ℤ :=
  if Even v.1 then ((p : ℤ) * v.1 / 2, v.2) else (((p : ℤ) * v.1 + v.2) / 2, -v.2)

/-- The state sequence of the alternating construction, started at `(x₀, 1)`. -/
def altSeq (p : ℕ) (x₀ : ℤ) (n : ℕ) : ℤ × ℤ := (altStep p)^[n] (x₀, 1)

/-- The integer sequence `xₙ` of the alternating construction. -/
def altX (p : ℕ) (x₀ : ℤ) (n : ℕ) : ℤ := (altSeq p x₀ n).1

/-- The sign `σₙ = ±1` carried along: the sign that the next non-zero letter must have. -/
def altSgn (p : ℕ) (x₀ : ℤ) (n : ℕ) : ℤ := (altSeq p x₀ n).2

/-- The carry word: `0` where `xₙ` is even, `σₙ` where it is odd. -/
def altLetter (p : ℕ) (x₀ : ℤ) (n : ℕ) : ℤ :=
  if Even (altX p x₀ n) then 0 else altSgn p x₀ n

@[category API, AMS 11, ref "Bug12", group "bug_3_16"]
theorem altX_succ (p : ℕ) (x₀ : ℤ) (n : ℕ) :
    altX p x₀ (n + 1) =
      if Even (altX p x₀ n) then (p : ℤ) * altX p x₀ n / 2
      else ((p : ℤ) * altX p x₀ n + altSgn p x₀ n) / 2 := by
  simp only [altX, altSgn, altSeq, Function.iterate_succ_apply', altStep]
  split <;> rfl

@[category API, AMS 11, ref "Bug12", group "bug_3_16"]
theorem altSgn_succ (p : ℕ) (x₀ : ℤ) (n : ℕ) :
    altSgn p x₀ (n + 1) =
      if Even (altX p x₀ n) then altSgn p x₀ n else -altSgn p x₀ n := by
  simp only [altX, altSgn, altSeq, Function.iterate_succ_apply', altStep]
  split <;> rfl

/-- The carried sign is always `±1`. -/
@[category API, AMS 11, ref "Bug12", group "bug_3_16"]
theorem altSgn_eq (p : ℕ) (x₀ : ℤ) (n : ℕ) : altSgn p x₀ n = 1 ∨ altSgn p x₀ n = -1 := by
  induction n with
  | zero => left; rfl
  | succ n ih =>
    rw [altSgn_succ]
    split
    · exact ih
    · rcases ih with h | h <;> rw [h] <;> simp

@[category API, AMS 11, ref "Bug12", group "bug_3_16"]
theorem abs_altLetter_le_one (p : ℕ) (x₀ : ℤ) (n : ℕ) : |altLetter p x₀ n| ≤ 1 := by
  rw [altLetter]
  split
  · simp
  · rcases altSgn_eq p x₀ n with h | h <;> rw [h] <;> norm_num

/-- Real form of `σₙ² = 1`. -/
@[category API, AMS 11, ref "Bug12", group "bug_3_16"]
theorem altSgn_mul_self (p : ℕ) (x₀ : ℤ) (n : ℕ) :
    (altSgn p x₀ n : ℝ) * (altSgn p x₀ n : ℝ) = 1 := by
  rcases altSgn_eq p x₀ n with h | h <;> rw [h] <;> norm_num

/-- The alternating construction is a reverse carry construction for `q = 2`. -/
@[category API, AMS 11, ref "Bug12", group "bug_3_16", formal_uses altX_succ]
theorem two_mul_altX_succ (hodd : Odd p) (x₀ : ℤ) (n : ℕ) :
    (2 : ℤ) * altX p x₀ (n + 1) = (p : ℤ) * altX p x₀ n + altLetter p x₀ n := by
  rw [altX_succ]
  by_cases hev : Even (altX p x₀ n)
  · rw [if_pos hev, Int.mul_ediv_cancel' (Dvd.dvd.mul_left hev.two_dvd _), altLetter,
      if_pos hev, add_zero]
  · have hoddx : Odd (altX p x₀ n) := Int.not_even_iff_odd.mp hev
    have hoddp : Odd ((p : ℤ)) := by exact_mod_cast hodd
    have hoddσ : Odd (altSgn p x₀ n) := by
      rcases altSgn_eq p x₀ n with h | h
      · exact ⟨0, by rw [h]; ring⟩
      · exact ⟨-1, by rw [h]; ring⟩
    rw [if_neg hev, Int.mul_ediv_cancel' ((hoddp.mul hoddx).add_odd hoddσ).two_dvd, altLetter,
      if_neg hev]

/-! ## The bound `|Tₙ| ≤ 1` -/

/-- The inductive invariant on truncations: `σₙ` times any partial sum of the tail from
position `n` lies in `[0, 1]`. -/
@[category API, AMS 11, ref "Bug12", group "bug_3_16",
  formal_uses altSgn_succ, formal_uses altSgn_mul_self]
theorem altSgn_mul_partialTail_mem_Icc (hp : 3 ≤ p) (x₀ : ℤ) :
    ∀ N n : ℕ,
      0 ≤ (altSgn p x₀ n : ℝ) *
            partialTail (2 / (p : ℝ)) (fun j => (altLetter p x₀ j : ℝ)) n N ∧
        (altSgn p x₀ n : ℝ) *
            partialTail (2 / (p : ℝ)) (fun j => (altLetter p x₀ j : ℝ)) n N ≤ 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hr0 : (0 : ℝ) ≤ 2 / (p : ℝ) := by positivity
  have hr1 : 2 / (p : ℝ) ≤ 1 := by
    rw [div_le_one hp0]
    exact_mod_cast (by omega : 2 ≤ p)
  intro N
  induction N with
  | zero => intro n; simp [partialTail]
  | succ N ih =>
    intro n
    obtain ⟨h1, h2⟩ := ih (n + 1)
    rw [partialTail_succ]
    set P := partialTail (2 / (p : ℝ)) (fun j => (altLetter p x₀ j : ℝ)) (n + 1) N with hP
    have hsq := altSgn_mul_self p x₀ n
    by_cases hev : Even (altX p x₀ n)
    · have hl : ((altLetter p x₀ n : ℤ) : ℝ) = 0 := by rw [altLetter, if_pos hev]; norm_num
      have hσ : altSgn p x₀ (n + 1) = altSgn p x₀ n := by rw [altSgn_succ, if_pos hev]
      rw [hσ] at h1 h2
      have hgoal : (altSgn p x₀ n : ℝ) * (((altLetter p x₀ n : ℤ) : ℝ) + 2 / (p : ℝ) * P)
          = 2 / (p : ℝ) * ((altSgn p x₀ n : ℝ) * P) := by rw [hl]; ring
      simp only [hgoal]
      exact ⟨mul_nonneg hr0 h1, mul_le_one₀ hr1 h1 h2⟩
    · have hl : ((altLetter p x₀ n : ℤ) : ℝ) = (altSgn p x₀ n : ℝ) := by
        rw [altLetter, if_neg hev]
      have hσ : altSgn p x₀ (n + 1) = -altSgn p x₀ n := by rw [altSgn_succ, if_neg hev]
      rw [hσ] at h1 h2
      push_cast at h1 h2
      have hgoal : (altSgn p x₀ n : ℝ) * (((altLetter p x₀ n : ℤ) : ℝ) + 2 / (p : ℝ) * P)
          = 1 + 2 / (p : ℝ) * ((altSgn p x₀ n : ℝ) * P) := by
        rw [hl]; linear_combination hsq
      have hA : (0 : ℝ) ≤ -((altSgn p x₀ n : ℝ) * P) := by linarith
      have hB : -((altSgn p x₀ n : ℝ) * P) ≤ 1 := by linarith
      have hC : (0 : ℝ) ≤ 2 / (p : ℝ) * -((altSgn p x₀ n : ℝ) * P) := mul_nonneg hr0 hA
      have hD : 2 / (p : ℝ) * -((altSgn p x₀ n : ℝ) * P) ≤ 1 := mul_le_one₀ hr1 hA hB
      simp only [hgoal]
      constructor <;> linarith

/-- The limit form of the invariant. -/
@[category API, AMS 11, ref "Bug12", group "bug_3_16",
  formal_uses altSgn_mul_partialTail_mem_Icc]
theorem altSgn_mul_tail_mem_Icc (hp : 3 ≤ p) (x₀ : ℤ) (n : ℕ) :
    0 ≤ (altSgn p x₀ n : ℝ) * tailSeries (2 / (p : ℝ)) (fun j => (altLetter p x₀ j : ℝ)) n ∧
      (altSgn p x₀ n : ℝ) *
        tailSeries (2 / (p : ℝ)) (fun j => (altLetter p x₀ j : ℝ)) n ≤ 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hr0 : (0 : ℝ) ≤ 2 / (p : ℝ) := by positivity
  have hr1 : 2 / (p : ℝ) < 1 := by
    rw [div_lt_one hp0]
    exact_mod_cast (by omega : 2 < p)
  have hbdd : ∀ k, |((altLetter p x₀ k : ℤ) : ℝ)| ≤ 1 := fun k => by
    rw [← Int.cast_abs]
    exact_mod_cast abs_altLetter_le_one p x₀ k
  have hsum := summable_tailSeries (M := (1 : ℝ)) hr0 hr1 hbdd n
  have hinv := altSgn_mul_partialTail_mem_Icc hp x₀
  rcases altSgn_eq p x₀ n with h | h
  · have hlo : ∀ N, (0 : ℝ) ≤ partialTail (2 / (p : ℝ))
        (fun j => (altLetter p x₀ j : ℝ)) n N := by
      intro N; have := (hinv N n).1; rw [h] at this; push_cast at this; linarith
    have hhi : ∀ N, partialTail (2 / (p : ℝ))
        (fun j => (altLetter p x₀ j : ℝ)) n N ≤ 1 := by
      intro N; have := (hinv N n).2; rw [h] at this; push_cast at this; linarith
    have hA := le_tailSeries_of_le_partialTail (r := 2 / (p : ℝ))
      (a := fun j => ((altLetter p x₀ j : ℤ) : ℝ)) (n := n) hsum hlo
    have hB := tailSeries_le_of_partialTail_le (r := 2 / (p : ℝ))
      (a := fun j => ((altLetter p x₀ j : ℤ) : ℝ)) (n := n) hsum hhi
    rw [h]
    push_cast
    constructor <;> linarith
  · have hlo : ∀ N, (-1 : ℝ) ≤ partialTail (2 / (p : ℝ))
        (fun j => (altLetter p x₀ j : ℝ)) n N := by
      intro N; have := (hinv N n).2; rw [h] at this; push_cast at this; linarith
    have hhi : ∀ N, partialTail (2 / (p : ℝ))
        (fun j => (altLetter p x₀ j : ℝ)) n N ≤ 0 := by
      intro N; have := (hinv N n).1; rw [h] at this; push_cast at this; linarith
    have hA := le_tailSeries_of_le_partialTail (r := 2 / (p : ℝ))
      (a := fun j => ((altLetter p x₀ j : ℤ) : ℝ)) (n := n) hsum hlo
    have hB := tailSeries_le_of_partialTail_le (r := 2 / (p : ℝ))
      (a := fun j => ((altLetter p x₀ j : ℤ) : ℝ)) (n := n) hsum hhi
    rw [h]
    push_cast
    constructor <;> linarith

/-! ## Strictness -/

/-- A vanishing tail propagates: it forces the letter to vanish and the next tail to vanish. -/
@[category API, AMS 11, ref "Bug12", group "bug_3_16", formal_uses altSgn_mul_tail_mem_Icc]
theorem altLetter_eq_zero_of_tail_eq_zero (hp : 3 ≤ p) (x₀ : ℤ) {n : ℕ}
    (h : tailSeries (2 / (p : ℝ)) (fun j => (altLetter p x₀ j : ℝ)) n = 0) :
    altLetter p x₀ n = 0 ∧
      tailSeries (2 / (p : ℝ)) (fun j => (altLetter p x₀ j : ℝ)) (n + 1) = 0 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hr0 : (0 : ℝ) < 2 / (p : ℝ) := by positivity
  have hr1 : 2 / (p : ℝ) < 1 := by
    rw [div_lt_one hp0]
    exact_mod_cast (by omega : 2 < p)
  have hbdd : ∀ k, |((altLetter p x₀ k : ℤ) : ℝ)| ≤ 1 := fun k => by
    rw [← Int.cast_abs]
    exact_mod_cast abs_altLetter_le_one p x₀ k
  have hrec := tailSeries_succ (M := (1 : ℝ)) hr0.le hr1 hbdd n
  have hsq := altSgn_mul_self p x₀ n
  by_cases hev : Even (altX p x₀ n)
  · have hl : ((altLetter p x₀ n : ℤ) : ℝ) = 0 := by rw [altLetter, if_pos hev]; norm_num
    refine ⟨by rw [altLetter, if_pos hev], ?_⟩
    rw [h, hl, zero_add] at hrec
    exact (mul_eq_zero.mp hrec.symm).resolve_left (ne_of_gt hr0)
  · exfalso
    have hl : ((altLetter p x₀ n : ℤ) : ℝ) = (altSgn p x₀ n : ℝ) := by
      rw [altLetter, if_neg hev]
    have hσ : altSgn p x₀ (n + 1) = -altSgn p x₀ n := by rw [altSgn_succ, if_neg hev]
    obtain ⟨h1, h2⟩ := altSgn_mul_tail_mem_Icc hp x₀ (n + 1)
    rw [hσ] at h1 h2
    push_cast at h1 h2
    rw [h, hl] at hrec
    -- `0 = σₙ + r·T_{n+1}`, but `σₙ · T_{n+1} ∈ [-1, 0]` gives `σₙ · 0 ≥ 1 - r > 0`
    have hmul : (altSgn p x₀ n : ℝ) * 0
        = 1 + 2 / (p : ℝ) *
            ((altSgn p x₀ n : ℝ) *
              tailSeries (2 / (p : ℝ)) (fun j => (altLetter p x₀ j : ℝ)) (n + 1)) := by
      rw [hrec]; linear_combination hsq
    have hA : (0 : ℝ) ≤ -((altSgn p x₀ n : ℝ) *
        tailSeries (2 / (p : ℝ)) (fun j => (altLetter p x₀ j : ℝ)) (n + 1)) := by linarith
    have hB : -((altSgn p x₀ n : ℝ) *
        tailSeries (2 / (p : ℝ)) (fun j => (altLetter p x₀ j : ℝ)) (n + 1)) ≤ 1 := by linarith
    have hD : 2 / (p : ℝ) * -((altSgn p x₀ n : ℝ) *
        tailSeries (2 / (p : ℝ)) (fun j => (altLetter p x₀ j : ℝ)) (n + 1)) ≤ 2 / (p : ℝ) := by
      nlinarith [hB, hr0.le]
    rw [mul_zero] at hmul
    linarith

/-- Once the tail vanishes it stays zero, so the carry word is eventually zero. -/
@[category API, AMS 11, ref "Bug12", group "bug_3_16",
  formal_uses altLetter_eq_zero_of_tail_eq_zero]
theorem altLetter_eventually_zero (hp : 3 ≤ p) (x₀ : ℤ) {n : ℕ}
    (h : tailSeries (2 / (p : ℝ)) (fun j => (altLetter p x₀ j : ℝ)) n = 0) :
    ∀ m, n ≤ m → altLetter p x₀ m = 0 := by
  have key : ∀ k, tailSeries (2 / (p : ℝ)) (fun j => (altLetter p x₀ j : ℝ)) (n + k) = 0 := by
    intro k
    induction k with
    | zero => exact h
    | succ k ih => exact (altLetter_eq_zero_of_tail_eq_zero hp x₀ ih).2
  intro m hm
  obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
  exact (altLetter_eq_zero_of_tail_eq_zero hp x₀ (key k)).1

/-! ## Theorem 3.16, first assertion -/

/-- Bridge to the general reverse carry machinery: `carryTail p 2 = (1/p)·tailSeries (2/p)`. -/
@[category API, AMS 11, ref "Bug12", group "bug_3_16"]
theorem carryTail_two (p : ℕ) (s : ℕ → ℤ) (n : ℕ) :
    carryTail p 2 s n = (1 / (p : ℝ)) * tailSeries (2 / (p : ℝ)) (fun j => (s j : ℝ)) n := by
  rw [carryTail]
  norm_num


/-- **Theorem 3.16**, first assertion (Dubickas).  For every odd integer `p ≥ 3` there is a
non-zero real number `ξ` with `‖ξ (p/2)ⁿ‖ < 1/p` for every `n ≥ 0`.

The bound is close to best possible for large `p`: by Theorem 3.14 it cannot be replaced by
`1/p - 4/p³`. -/
@[category research solved, AMS 11, ref "Bug12", group "bug_3_16",
  formal_uses two_mul_altX_succ, formal_uses altSgn_mul_tail_mem_Icc,
  formal_uses altLetter_eventually_zero, formal_uses carryXi_eq_zero_of_eventually_const]
theorem theorem_3_16_half (hp : 3 ≤ p) (hodd : Odd p) :
    ∃ ξ : ℝ, ξ ≠ 0 ∧ ∀ n : ℕ, distToNearestInt (ξ * ((p : ℝ) / 2) ^ n) < 1 / (p : ℝ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hpZ : (2 : ℕ) < p := by omega
  have hcop : Nat.Coprime p 2 := Nat.coprime_two_right.mpr hodd
  have hs : ∀ k, |altLetter p 1 k| ≤ 1 := abs_altLetter_le_one p 1
  have hrec : ∀ n, ((2 : ℕ) : ℤ) * altX p 1 (n + 1) = (p : ℤ) * altX p 1 n + altLetter p 1 n := by
    intro n
    have h := two_mul_altX_succ hodd 1 n
    push_cast
    exact h
  have hr0 : (0 : ℝ) < 2 / (p : ℝ) := by positivity
  have hr1 : 2 / (p : ℝ) < 1 := by
    rw [div_lt_one hp0]
    exact_mod_cast hpZ
  have hbdd : ∀ k, |((altLetter p 1 k : ℤ) : ℝ)| ≤ 1 := fun k => by
    rw [← Int.cast_abs]; exact_mod_cast hs k
  -- the invariant, in absolute-value form
  have hT : ∀ n, |tailSeries (2 / (p : ℝ)) (fun j => (altLetter p 1 j : ℝ)) n| ≤ 1 := by
    intro n
    obtain ⟨h1, h2⟩ := altSgn_mul_tail_mem_Icc hp 1 n
    rcases altSgn_eq p 1 n with h | h <;> rw [h] at h1 h2 <;> push_cast at h1 h2 <;>
      rw [abs_le] <;> constructor <;> linarith
  -- `ξ = 1 + T₀/p ≥ 1 - 1/p > 0`
  have hpos : 0 < carryXi p 2 (altX p 1) (altLetter p 1) := by
    have h0 := hT 0
    rw [abs_le] at h0
    have hx0 : altX p 1 0 = 1 := rfl
    have hple : 1 / (p : ℝ) < 1 := by
      rw [div_lt_one hp0]
      exact_mod_cast (by omega : 1 < p)
    have hinv : (0 : ℝ) < 1 / (p : ℝ) := by positivity
    rw [carryXi, hx0, carryTail_two]
    push_cast
    nlinarith [h0.1, h0.2]
  -- strictness of the invariant
  have hTlt : ∀ n, |tailSeries (2 / (p : ℝ)) (fun j => (altLetter p 1 j : ℝ)) n| < 1 := by
    intro n
    rcases lt_or_eq_of_le (hT n) with h | h
    · exact h
    exfalso
    obtain ⟨h1, h2⟩ := altSgn_mul_tail_mem_Icc hp 1 n
    have hsq := altSgn_mul_self p 1 n
    have hrecT := tailSeries_succ (M := (1 : ℝ)) hr0.le hr1 hbdd n
    -- `σₙ Tₙ = 1`
    have hone : (altSgn p 1 n : ℝ) *
        tailSeries (2 / (p : ℝ)) (fun j => (altLetter p 1 j : ℝ)) n = 1 := by
      rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp h with hT1 | hT1 <;>
        rcases altSgn_eq p 1 n with hσ | hσ <;>
        rw [hσ] at h1 h2 ⊢ <;> rw [hT1] at h1 h2 ⊢ <;> push_cast at h1 h2 ⊢ <;> linarith
    by_cases hev : Even (altX p 1 n)
    · -- letter `0`: then `σₙ Tₙ = r · σ_{n+1} T_{n+1} ≤ r < 1`
      have hl : ((altLetter p 1 n : ℤ) : ℝ) = 0 := by rw [altLetter, if_pos hev]; norm_num
      have hσ : altSgn p 1 (n + 1) = altSgn p 1 n := by rw [altSgn_succ, if_pos hev]
      obtain ⟨g1, g2⟩ := altSgn_mul_tail_mem_Icc hp 1 (n + 1)
      rw [hσ] at g1 g2
      rw [hl, zero_add] at hrecT
      have hmul : (altSgn p 1 n : ℝ) *
          tailSeries (2 / (p : ℝ)) (fun j => (altLetter p 1 j : ℝ)) n
          = 2 / (p : ℝ) * ((altSgn p 1 n : ℝ) *
              tailSeries (2 / (p : ℝ)) (fun j => (altLetter p 1 j : ℝ)) (n + 1)) := by
        rw [hrecT]; ring
      have hle : 2 / (p : ℝ) * ((altSgn p 1 n : ℝ) *
          tailSeries (2 / (p : ℝ)) (fun j => (altLetter p 1 j : ℝ)) (n + 1)) ≤ 2 / (p : ℝ) := by
        nlinarith [g2, hr0.le]
      rw [hone] at hmul
      linarith
    · -- letter `σₙ`: forces `T_{n+1} = 0`, hence an eventually zero word, hence `ξ = 0`
      have hl : ((altLetter p 1 n : ℤ) : ℝ) = (altSgn p 1 n : ℝ) := by
        rw [altLetter, if_neg hev]
      rw [hl] at hrecT
      have hmul : (altSgn p 1 n : ℝ) *
          tailSeries (2 / (p : ℝ)) (fun j => (altLetter p 1 j : ℝ)) n
          = 1 + 2 / (p : ℝ) * ((altSgn p 1 n : ℝ) *
              tailSeries (2 / (p : ℝ)) (fun j => (altLetter p 1 j : ℝ)) (n + 1)) := by
        rw [hrecT]; linear_combination hsq
      rw [hone] at hmul
      have hz2 : (altSgn p 1 n : ℝ) *
          tailSeries (2 / (p : ℝ)) (fun j => (altLetter p 1 j : ℝ)) (n + 1) = 0 := by
        have hz1 : 2 / (p : ℝ) * ((altSgn p 1 n : ℝ) *
            tailSeries (2 / (p : ℝ)) (fun j => (altLetter p 1 j : ℝ)) (n + 1)) = 0 := by
          linarith
        exact (mul_eq_zero.mp hz1).resolve_left (ne_of_gt hr0)
      have hzero : tailSeries (2 / (p : ℝ)) (fun j => (altLetter p 1 j : ℝ)) (n + 1) = 0 := by
        refine (mul_eq_zero.mp hz2).resolve_left ?_
        rcases altSgn_eq p 1 n with hσ | hσ <;> rw [hσ] <;> norm_num
      exact absurd (carryXi_eq_zero_of_eventually_const (q := 2) le_rfl hpZ hcop hs hrec
        (altLetter_eventually_zero hp 1 hzero)) (ne_of_gt hpos)
  refine ⟨carryXi p 2 (altX p 1) (altLetter p 1), ne_of_gt hpos, fun n => ?_⟩
  have hmain := carryXi_mul_pow (q := 2) (by norm_num) hpZ hs hrec n
  push_cast at hmain
  calc distToNearestInt (carryXi p 2 (altX p 1) (altLetter p 1) * ((p : ℝ) / 2) ^ n)
      ≤ |carryXi p 2 (altX p 1) (altLetter p 1) * ((p : ℝ) / 2) ^ n - (altX p 1 n : ℝ)| :=
        distToNearestInt_le_abs_sub_intCast _ _
    _ = |carryTail p 2 (altLetter p 1) n| := by rw [hmain]; congr 1; ring
    _ < 1 / (p : ℝ) := by
        rw [carryTail_two, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (p : ℝ))]
        have hinv : (0 : ℝ) < 1 / (p : ℝ) := by positivity
        calc (1 / (p : ℝ)) *
              |tailSeries (2 / (p : ℝ)) (fun j => (altLetter p 1 j : ℝ)) n|
            < (1 / (p : ℝ)) * 1 := mul_lt_mul_of_pos_left (hTlt n) hinv
          _ = 1 / (p : ℝ) := by ring

end Bugeaud
