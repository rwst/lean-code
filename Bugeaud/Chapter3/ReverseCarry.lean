/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import ForMathlib.Analysis.SpecificLimits.TailSeries
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Bugeaud, Chapter 3, §3.6 — the reverse carry construction

Yann Bugeaud, *Distribution Modulo One and Diophantine Approximation* (Cambridge Tracts in
Mathematics 193, 2012), §3.6, the engine behind the constructions of Dubickas quoted there as
Theorems 3.16 and 3.18.

Given integers `p > q ≥ 2` one builds *backwards* from a prescribed word.  Start from an integer
`x₀` and, at each step, pick a **carry letter** `sₙ` from a set `A` of `q` consecutive integers
so that `q ∣ p xₙ + sₙ` — always possible, and uniquely so if `A` has exactly `q` elements —
and put `x_{n+1} := (p xₙ + sₙ)/q`.  Then

  `ξ := x₀ + (1/p) ∑_{j ≥ 0} sⱼ (q/p)ʲ`  satisfies  `ξ (p/q)ⁿ = xₙ + yₙ`,
  `yₙ := (1/p) ∑_{j ≥ 0} s_{n+j} (q/p)ʲ`,

so the *whole* orbit of `ξ` is controlled by the letters: `yₙ` lies in the interval spanned by
`A/(p-q)`, uniformly in `n`.  Prescribing `A` therefore prescribes a trap for `({ξ (p/q)ⁿ})`.

This file isolates that engine; `Bugeaud/Chapter3/DubickasConstructions.lean` instantiates it.

## Main definitions

* `Bugeaud.carryTail p q s n` — the tail value `yₙ` above.
* `Bugeaud.carryXi p q x s` — the real number `ξ = x₀ + y₀`.
* `Bugeaud.carryDigit`, `Bugeaud.carryStep` — the greedy choice of letter in a window of `q`
  consecutive integers, and the resulting map `xₙ ↦ x_{n+1}`.

## Main results

* `Bugeaud.carryXi_mul_pow` — the identity `ξ (p/q)ⁿ = xₙ + yₙ`.
* `Bugeaud.carryTail_le`, `Bugeaud.le_carryTail` — the trap: letters in `[c₁, c₂]` confine `yₙ`
  to `[c₁/(p-q), c₂/(p-q)]`.
* `Bugeaud.exists_carry` — every window of `q` consecutive integers admits a carry word.
* `Bugeaud.carryXi_eq_zero_of_eventually_const` — **rigidity**: an eventually constant carry word
  forces `ξ = 0`.  This is what upgrades the closed trap of `carryTail_le`/`le_carryTail` to the
  open one, replacing the appeal to Lemma 3.17 (`{ξ(p/q)ⁿ} = t` for only finitely many `n`,
  Exercise 3.6) in the book: the extremal value of the trap is attained only by a constant word,
  and a constant word has `ξ = 0` by a `q`-adic descent on `(p-q)xₙ + c`.

## References

* [Bug12] Y. Bugeaud, *Distribution Modulo One and Diophantine Approximation*, Cambridge Tracts
  in Mathematics 193, Cambridge University Press, 2012, §3.6.
* [Dub06] A. Dubickas, *Arithmetical properties of powers of algebraic numbers*, Bull. London
  Math. Soc. **38** (2006), 70–80 — reference [248] of [Bug12].
-/

namespace Bugeaud

open ForMathlib

variable {p q : ℕ} {x s : ℕ → ℤ} {M c : ℤ} {n : ℕ}

/-! ## The tail value of a carry word -/

/-- The `n`-th tail value of a carry word, `yₙ = (1/p) ∑_{j ≥ 0} s_{n+j} (q/p)ʲ`. -/
noncomputable def carryTail (p q : ℕ) (s : ℕ → ℤ) (n : ℕ) : ℝ :=
  (1 / (p : ℝ)) * tailSeries ((q : ℝ) / p) (fun j => (s j : ℝ)) n

/-- The real number built from a carry word and its integer sequence, `ξ = x₀ + y₀`. -/
noncomputable def carryXi (p q : ℕ) (x s : ℕ → ℤ) : ℝ := (x 0 : ℝ) + carryTail p q s 0

/-! ### Elementary facts about the contraction ratio `q/p` -/

@[category API, AMS 11, ref "Bug12", group "bug_3_16"]
theorem carryRatio_pos (hq : 0 < q) (hqp : q < p) : (0 : ℝ) < (q : ℝ) / p := by
  have h1 : (0 : ℝ) < q := by exact_mod_cast hq
  have h2 : (0 : ℝ) < p := by exact_mod_cast hq.trans hqp
  positivity

@[category API, AMS 11, ref "Bug12", group "bug_3_16"]
theorem carryRatio_lt_one (hq : 0 < q) (hqp : q < p) : (q : ℝ) / p < 1 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast hq.trans hqp
  rw [div_lt_one hp]
  exact_mod_cast hqp

/-- `1 - q/p = (p - q)/p`, the denominator appearing in every bound below. -/
@[category API, AMS 11, ref "Bug12", group "bug_3_16"]
theorem one_sub_carryRatio (hq : 0 < q) (hqp : q < p) :
    1 - (q : ℝ) / p = ((p : ℝ) - q) / p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast hq.trans hqp
  field_simp

/-- Real form of an integer bound on the letters. -/
@[category API, AMS 11, ref "Bug12", group "bug_3_16"]
theorem abs_intCast_le_of_abs_le (hs : ∀ k, |s k| ≤ M) (k : ℕ) : |(s k : ℝ)| ≤ (M : ℝ) := by
  rw [← Int.cast_abs]
  exact_mod_cast hs k

/-! ## The orbit identity -/

/-- The backward recursion for the tail values: `yₙ = sₙ/p + (q/p) y_{n+1}`. -/
@[category API, AMS 11, ref "Bug12", group "bug_3_16"]
theorem carryTail_succ (hq : 0 < q) (hqp : q < p) (hs : ∀ k, |s k| ≤ M) (n : ℕ) :
    carryTail p q s n = (s n : ℝ) / p + ((q : ℝ) / p) * carryTail p q s (n + 1) := by
  rw [carryTail, carryTail,
    tailSeries_succ (M := (M : ℝ)) (carryRatio_pos hq hqp).le (carryRatio_lt_one hq hqp)
      (abs_intCast_le_of_abs_le hs) n]
  ring

/-- **The reverse carry identity.**  If `q x_{n+1} = p xₙ + sₙ` for every `n`, then the real
number `ξ = x₀ + y₀` satisfies `ξ (p/q)ⁿ = xₙ + yₙ` for every `n`. -/
@[category API, AMS 11, ref "Bug12", group "bug_3_16", formal_uses carryTail_succ]
theorem carryXi_mul_pow (hq : 0 < q) (hqp : q < p) (hs : ∀ k, |s k| ≤ M)
    (hrec : ∀ n, (q : ℤ) * x (n + 1) = (p : ℤ) * x n + s n) (n : ℕ) :
    carryXi p q x s * ((p : ℝ) / q) ^ n = (x n : ℝ) + carryTail p q s n := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hq.trans hqp
  induction n with
  | zero => simp [carryXi]
  | succ n ih =>
    have hrecR : (q : ℝ) * (x (n + 1) : ℝ) = (p : ℝ) * (x n : ℝ) + (s n : ℝ) := by
      exact_mod_cast hrec n
    rw [pow_succ, ← mul_assoc, ih, carryTail_succ hq hqp hs n]
    field_simp
    nlinarith [hrecR, carryTail p q s (n + 1)]

/-! ## The trap -/

/-- Letters bounded above by `c` from position `n` on trap `yₘ` below `c/(p-q)`. -/
@[category API, AMS 11, ref "Bug12", group "bug_3_16"]
theorem carryTail_le (hq : 0 < q) (hqp : q < p) (hs : ∀ k, |s k| ≤ M)
    (h : ∀ m, n ≤ m → s m ≤ c) : carryTail p q s n ≤ (c : ℝ) / ((p : ℝ) - q) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hq.trans hqp
  have hpq : (0 : ℝ) < (p : ℝ) - q := by
    have : (q : ℝ) < p := by exact_mod_cast hqp
    linarith
  have key := tailSeries_le (M := (M : ℝ)) (c := (c : ℝ)) (a := fun j => (s j : ℝ))
    (carryRatio_pos hq hqp).le (carryRatio_lt_one hq hqp) (abs_intCast_le_of_abs_le hs)
    (fun m hm => by exact_mod_cast h m hm)
  rw [one_sub_carryRatio hq hqp, div_div_eq_mul_div] at key
  rw [carryTail]
  calc (1 / (p : ℝ)) * tailSeries ((q : ℝ) / p) (fun j => (s j : ℝ)) n
      ≤ (1 / (p : ℝ)) * ((c : ℝ) * p / ((p : ℝ) - q)) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = (c : ℝ) / ((p : ℝ) - q) := by field_simp

/-- Letters bounded below by `c` from position `n` on trap `yₘ` above `c/(p-q)`. -/
@[category API, AMS 11, ref "Bug12", group "bug_3_16"]
theorem le_carryTail (hq : 0 < q) (hqp : q < p) (hs : ∀ k, |s k| ≤ M)
    (h : ∀ m, n ≤ m → c ≤ s m) : (c : ℝ) / ((p : ℝ) - q) ≤ carryTail p q s n := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hq.trans hqp
  have hpq : (0 : ℝ) < (p : ℝ) - q := by
    have : (q : ℝ) < p := by exact_mod_cast hqp
    linarith
  have key := le_tailSeries (M := (M : ℝ)) (c := (c : ℝ)) (a := fun j => (s j : ℝ))
    (carryRatio_pos hq hqp).le (carryRatio_lt_one hq hqp) (abs_intCast_le_of_abs_le hs)
    (fun m hm => by exact_mod_cast h m hm)
  rw [one_sub_carryRatio hq hqp, div_div_eq_mul_div] at key
  rw [carryTail]
  calc (c : ℝ) / ((p : ℝ) - q)
      = (1 / (p : ℝ)) * ((c : ℝ) * p / ((p : ℝ) - q)) := by field_simp
    _ ≤ (1 / (p : ℝ)) * tailSeries ((q : ℝ) / p) (fun j => (s j : ℝ)) n :=
        mul_le_mul_of_nonneg_left key (by positivity)

/-! ### Rigidity of the trap: the extremes are attained only by constant words -/

@[category API, AMS 11, ref "Bug12", group "bug_3_16"]
theorem eq_of_carryTail_eq_ge (hq : 0 < q) (hqp : q < p) (hs : ∀ k, |s k| ≤ M)
    (h : ∀ m, n ≤ m → c ≤ s m) (heq : carryTail p q s n = (c : ℝ) / ((p : ℝ) - q)) :
    ∀ m, n ≤ m → s m = c := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hq.trans hqp
  have hpq : (0 : ℝ) < (p : ℝ) - q := by
    have : (q : ℝ) < p := by exact_mod_cast hqp
    linarith
  have heq' : tailSeries ((q : ℝ) / p) (fun j => (s j : ℝ)) n = (c : ℝ) / (1 - (q : ℝ) / p) := by
    rw [one_sub_carryRatio hq hqp, div_div_eq_mul_div]
    rw [carryTail] at heq
    field_simp at heq ⊢
    linarith [heq]
  have := eq_of_tailSeries_eq_ge (M := (M : ℝ)) (carryRatio_pos hq hqp)
    (carryRatio_lt_one hq hqp) (abs_intCast_le_of_abs_le hs)
    (fun m hm => by exact_mod_cast h m hm) heq'
  intro m hm
  exact_mod_cast this m hm

@[category API, AMS 11, ref "Bug12", group "bug_3_16"]
theorem eq_of_carryTail_eq_le (hq : 0 < q) (hqp : q < p) (hs : ∀ k, |s k| ≤ M)
    (h : ∀ m, n ≤ m → s m ≤ c) (heq : carryTail p q s n = (c : ℝ) / ((p : ℝ) - q)) :
    ∀ m, n ≤ m → s m = c := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hq.trans hqp
  have hpq : (0 : ℝ) < (p : ℝ) - q := by
    have : (q : ℝ) < p := by exact_mod_cast hqp
    linarith
  have heq' : tailSeries ((q : ℝ) / p) (fun j => (s j : ℝ)) n = (c : ℝ) / (1 - (q : ℝ) / p) := by
    rw [one_sub_carryRatio hq hqp, div_div_eq_mul_div]
    rw [carryTail] at heq
    field_simp at heq ⊢
    linarith [heq]
  have := eq_of_tailSeries_eq_le (M := (M : ℝ)) (carryRatio_pos hq hqp)
    (carryRatio_lt_one hq hqp) (abs_intCast_le_of_abs_le hs)
    (fun m hm => by exact_mod_cast h m hm) heq'
  intro m hm
  exact_mod_cast this m hm

/-! ## Existence of carry words: the greedy choice in a window -/

/-- The greedy carry letter: the unique element of `[c, c+q)` congruent to `-p x` modulo `q`. -/
def carryDigit (p q c x : ℤ) : ℤ := c + (-(p * x) - c) % q

/-- The next integer of the reverse-carry sequence, `(p x + carryDigit)/q`. -/
def carryStep (p q c x : ℤ) : ℤ := -((-(p * x) - c) / q)

@[category API, AMS 11, ref "Bug12", group "bug_3_16"]
theorem carryStep_spec (p q c x : ℤ) : q * carryStep p q c x = p * x + carryDigit p q c x := by
  simp only [carryStep, carryDigit, Int.emod_def]
  ring

@[category API, AMS 11, ref "Bug12", group "bug_3_16"]
theorem carryDigit_mem_Ico {q : ℤ} (hq : 0 < q) (p c x : ℤ) :
    carryDigit p q c x ∈ Set.Ico c (c + q) := by
  constructor
  · have := Int.emod_nonneg (-(p * x) - c) hq.ne'
    simp only [carryDigit]
    omega
  · have := Int.emod_lt_of_pos (-(p * x) - c) hq
    simp only [carryDigit]
    omega

/-- **Every window of `q` consecutive integers carries a word.**  Given `q ≥ 1`, a starting
integer `x₀` and the left endpoint `c` of the window, there are sequences `x` and `s` with
`s` valued in `[c, c+q)` and `q x_{n+1} = p xₙ + sₙ`. -/
@[category API, AMS 11, ref "Bug12", group "bug_3_16", formal_uses carryStep_spec]
theorem exists_carry (p : ℕ) {q : ℕ} (hq : 0 < q) (c x₀ : ℤ) :
    ∃ x s : ℕ → ℤ, x 0 = x₀ ∧ (∀ n, s n ∈ Set.Ico c (c + q)) ∧
      ∀ n, (q : ℤ) * x (n + 1) = (p : ℤ) * x n + s n := by
  have hq' : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  refine ⟨fun n => (carryStep p q c)^[n] x₀,
    fun n => carryDigit p q c ((carryStep p q c)^[n] x₀), rfl, ?_, ?_⟩
  · intro n
    exact carryDigit_mem_Ico hq' _ _ _
  · intro n
    simp only [Function.iterate_succ_apply']
    exact carryStep_spec _ _ _ _

/-- Letters confined to a window of `q` consecutive integers are bounded. -/
@[category API, AMS 11, ref "Bug12", group "bug_3_16"]
theorem abs_le_of_mem_Ico {q : ℕ} (hmem : ∀ n, s n ∈ Set.Ico c (c + q)) (n : ℕ) :
    |s n| ≤ |c| + q := by
  have h := hmem n
  simp only [Set.mem_Ico] at h
  rcases abs_cases c with ⟨hc, _⟩ | ⟨hc, _⟩ <;> rcases abs_cases (s n) with ⟨hs, _⟩ | ⟨hs, _⟩ <;>
    omega

/-! ## Rigidity: a constant tail forces `ξ = 0` -/

/-- The auxiliary integer sequence `zₙ = (p-q) xₙ + c` of the descent. -/
@[category API, AMS 11, ref "Bug12", group "bug_3_16"]
theorem descent_rec (hrec : ∀ n, (q : ℤ) * x (n + 1) = (p : ℤ) * x n + s n)
    {N : ℕ} (hconst : ∀ m, N ≤ m → s m = c) (m : ℕ) (hm : N ≤ m) :
    (q : ℤ) * (((p : ℤ) - q) * x (m + 1) + c) = (p : ℤ) * (((p : ℤ) - q) * x m + c) := by
  have h1 := hrec m
  have h2 := hconst m hm
  rw [h2] at h1
  nlinarith [h1]

/-- `q`-adic descent: `q zₘ₊₁ = p zₘ` with `gcd(p, q) = 1` makes `z_N` divisible by every power
of `q`. -/
@[category API, AMS 11, ref "Bug12", group "bug_3_16"]
theorem dvd_pow_of_descent {z : ℕ → ℤ} {N : ℕ} (hcop : IsCoprime (p : ℤ) (q : ℤ))
    (hz : ∀ m, N ≤ m → (q : ℤ) * z (m + 1) = (p : ℤ) * z m) :
    ∀ k m, N ≤ m → ((q : ℤ) ^ k) ∣ z m := by
  intro k
  induction k with
  | zero => intro m _; simp
  | succ k ih =>
    intro m hm
    have h1 : ((q : ℤ) ^ (k + 1)) ∣ (q : ℤ) * z (m + 1) := by
      rw [pow_succ, mul_comm ((q : ℤ) ^ k) (q : ℤ)]
      exact mul_dvd_mul_left _ (ih (m + 1) (by omega))
    rw [hz m hm] at h1
    exact hcop.symm.pow_left.dvd_of_dvd_mul_left h1

/-- **Rigidity.**  If the carry word is eventually constant, then `ξ = 0`.  (In particular the
constructions below, which produce `ξ ≠ 0`, never realise the extreme values of their trap.) -/
@[category API, AMS 11, ref "Bug12", group "bug_3_16",
  formal_uses carryXi_mul_pow, formal_uses dvd_pow_of_descent]
theorem carryXi_eq_zero_of_eventually_const (hq : 2 ≤ q) (hqp : q < p)
    (hcop : Nat.Coprime p q) (hs : ∀ k, |s k| ≤ M)
    (hrec : ∀ n, (q : ℤ) * x (n + 1) = (p : ℤ) * x n + s n)
    {N : ℕ} (hconst : ∀ m, N ≤ m → s m = c) :
    carryXi p q x s = 0 := by
  have hq0 : 0 < q := by omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hq0.trans hqp
  have hq0R : (0 : ℝ) < q := by exact_mod_cast hq0
  have hpq : (0 : ℝ) < (p : ℝ) - q := by
    have : (q : ℝ) < p := by exact_mod_cast hqp
    linarith
  -- the descent sequence
  set z : ℕ → ℤ := fun m => ((p : ℤ) - q) * x m + c with hzdef
  have hcopZ : IsCoprime (p : ℤ) (q : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr (by simpa using hcop)
  have hdvd := dvd_pow_of_descent hcopZ (z := z)
    (fun m hm => descent_rec hrec hconst m hm)
  -- every power of `q` divides `z N`, hence `z N = 0`
  have hzN : z N = 0 := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, |z N| < (q : ℤ) ^ k := by
      obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (|z N| : ℤ) (by exact_mod_cast hq : (1 : ℤ) < q)
      exact ⟨k, hk⟩
    exact Int.eq_zero_of_abs_lt_dvd (hdvd k N le_rfl) hk
  -- hence `x N = -c/(p-q)` and `y N = c/(p-q)`
  have hxN : (x N : ℝ) = -(c : ℝ) / ((p : ℝ) - q) := by
    have : ((p : ℤ) - q) * x N + c = 0 := hzN
    have hR : ((p : ℝ) - q) * (x N : ℝ) + (c : ℝ) = 0 := by exact_mod_cast this
    field_simp
    linarith
  have hyN : carryTail p q s N = (c : ℝ) / ((p : ℝ) - q) :=
    le_antisymm (carryTail_le hq0 hqp hs fun m hm => (hconst m hm).le)
      (le_carryTail hq0 hqp hs fun m hm => (hconst m hm).ge)
  have hmain := carryXi_mul_pow hq0 hqp hs hrec N
  rw [hxN, hyN] at hmain
  have : carryXi p q x s * ((p : ℝ) / q) ^ N = 0 := by
    rw [hmain]
    ring
  have hpow : ((p : ℝ) / q) ^ N ≠ 0 := by positivity
  exact (mul_eq_zero.mp this).resolve_right hpow

end Bugeaud
