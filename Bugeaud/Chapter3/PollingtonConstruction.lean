/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Tactic
import ForMathlib.Data.Real.NearestInt
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Bugeaud, Chapter 3, §3.6 — Pollington's construction

Yann Bugeaud, *Distribution Modulo One and Diophantine Approximation* (Cambridge Tracts in
Mathematics 193, 2012), **Theorem 3.15** (Pollington [Pol81]): there is a real number `ξ` with

  `‖ξ (3/2)ⁿ‖ ≥ 4/65`  for every `n ≥ 1`.

This is the opposite extreme to `Bugeaud/Chapter3/WindowConstructions.lean`, where the orbit of
`ξ` is pushed *close* to `ℤ`; here it is kept *away* from `ℤ`.

## The method

Fix `ε ∈ (0, 1/2)`.  A **Pollington triple** `(n, ℓ, m)` (`Bugeaud.Pollington.Triple`) is good
(`Bugeaud.Pollington.IsGood`) when

* `(p/q)^m [n+ε, n+1-ε] ⊇ [ℓ+ε, ℓ+1-ε]`, and
* each of the `m+1` backward windows `(q/p)^i [ℓ+ε, ℓ+1-ε]`, `0 ≤ i ≤ m`, lies inside a gap
  between two consecutive integers, at distance `≥ δ` from both of them.

The second condition is exactly Bugeaud's "`[(q/p)^i(ℓ+ε), (q/p)^i(ℓ+1-ε)]` contains no integer"
together with his `δ(n) ≥ δ`; bundling the two (`IsGood.trap`) is what turns the whole
certificate into a single family of integer inequalities, see below.

A good triple is a **trap for `m` steps**: if `x (p/q)^m` lands in the target window — even after
an integer translation `ℓ ↦ ℓ + a pᵐ`, which is what the construction actually produces — then
`‖x (p/q)^i‖ ≥ δ` for `i = 0, 1, …, m` (`Bugeaud.Pollington.dist_ge_of_isGood`).  Traps are then
chained by a *covering system*: a finite list of triples whose residues `nⱼ mod q^{mⱼ}` cover
`ℕ`.  Starting from `n = 1` one always finds a triple to apply, and the resulting nested
intervals close in on the desired `ξ` (`Bugeaud.Pollington.exists_forall_dist_ge`).

## Certificate

Everything about a triple is decided by inequalities between *natural numbers*.  Writing
`ε = a/(a+a')`, `δ = c/d` and `b = a+a'`, the `i`-th backward window is `[U/D, V/D]` with
`U = qⁱ(ℓb+a)`, `V = qⁱ(ℓb+a')`, `D = pⁱ b`, and the trap condition reads

  `d·k·D + c·D ≤ d·U`  and  `d·V + c·D ≤ d·(k+1)·D`,  where `k = U / D`.

So `Bugeaud.Pollington.tripleOK` is a `Bool`-valued checker and
`Bugeaud.Pollington.exists_forall_dist_ge_of_cert` turns a `by decide` into a theorem about `ℝ`.
For `p/q = 3/2` the twelve triples of the book, with `ε = 9/65`, certify `δ = 4/65`.

## Deviations from the book

* Bugeaud's proof ends "the sequence `(Jⱼ)` is a decreasing sequence of nested closed intervals;
  its intersection is reduced to one point `ξ`".  The convergence is not needed: *any* point of
  the intersection works, and the supremum of the left endpoints is one, so no interval-length
  estimate appears here.
* `gcd(p, q) = 1` is never used; the construction works for all `p > q ≥ 1`.
* Bugeaud sets `δ(n) = min_{0≤i≤m} min{‖(ℓ+ε)(q/p)^i‖, ‖(ℓ+1-ε)(q/p)^i‖}` and separately demands
  that the backward windows contain no integer.  The two conditions are merged into
  `IsGood.trap`, which is both shorter to state and the form the certificate proves.
* The value `ε = 9/65` (the book only says "selecting `ε` suitably") is optimal for these twelve
  triples: no `ε` with denominator below 1200 gives a bound above `4/65`.

## References

* [Bug12] Y. Bugeaud, *Distribution Modulo One and Diophantine Approximation*, Cambridge Tracts
  in Mathematics 193, Cambridge University Press, 2012, Theorem 3.15.
* [Pol81] A. D. Pollington, *Progressions arithmétiques généralisées et le problème des `(3/2)ⁿ`*,
  C. R. Acad. Sci. Paris **292** (1981), 383–384, and *On the density of the sequence `{nₖξ}`*,
  Illinois J. Math. **23** (1979), 511–515 — references [572, 574] of [Bug12].
-/

namespace Bugeaud
namespace Pollington

/-- One congruence class of Pollington's construction: the residue `n`, the target integer `ℓ`
and the exponent `m` (so the modulus of the congruence is `qᵐ`).  Bugeaud writes these as
triples `(nⱼ, ℓⱼ, mⱼ)`. -/
structure Triple where
  /-- The residue class representative, `0 ≤ n < qᵐ`. -/
  n : ℕ
  /-- The integer part of the target window `[ℓ+ε, ℓ+1-ε]`. -/
  l : ℕ
  /-- The exponent: the modulus of the congruence is `qᵐ`, and the trap lasts `m` steps. -/
  m : ℕ
  deriving DecidableEq, Repr

variable {p q : ℕ} {ε δ : ℝ} {t : Triple}

/-- The conditions making a triple usable: `(p/q)^m` maps `[n+ε, n+1-ε]` over `[ℓ+ε, ℓ+1-ε]`,
and every backward window `(q/p)^i [ℓ+ε, ℓ+1-ε]`, `0 ≤ i ≤ m`, is trapped between two
consecutive integers, at distance `≥ δ` from both. -/
structure IsGood (p q : ℕ) (ε δ : ℝ) (t : Triple) : Prop where
  /-- `ℓ` is positive, so the recursion never leaves the positive integers. -/
  l_pos : 0 < t.l
  /-- The exponent is positive, so the cumulative exponents tend to infinity. -/
  m_pos : 0 < t.m
  /-- Lower endpoint of `[ℓ+ε, ℓ+1-ε] ⊆ (p/q)^m [n+ε, n+1-ε]`. -/
  lower : ((p : ℝ) / q) ^ t.m * (t.n + ε) ≤ (t.l : ℝ) + ε
  /-- Upper endpoint of `[ℓ+ε, ℓ+1-ε] ⊆ (p/q)^m [n+ε, n+1-ε]`. -/
  upper : (t.l : ℝ) + 1 - ε ≤ ((p : ℝ) / q) ^ t.m * (t.n + 1 - ε)
  /-- The `i`-th backward window lies in `[k+δ, k+1-δ]` for some integer `k`. -/
  trap : ∀ i ≤ t.m, ∃ k : ℤ,
    (k : ℝ) + δ ≤ ((q : ℝ) / p) ^ i * ((t.l : ℝ) + ε) ∧
      ((q : ℝ) / p) ^ i * ((t.l : ℝ) + 1 - ε) ≤ (k : ℝ) + 1 - δ

/-!
### A good triple traps the orbit for `m` steps
-/

/-- **The trap.**  If the `m`-th forward image of `x` lands in the target window of a good
triple — translated by an integer multiple `a·pᵐ`, which is what the covering system produces —
then the first `m` forward images of `x` all stay at distance `≥ δ` from `ℤ`.

This is Bugeaud's "for `x` in `[n+ε, n+1-ε] ∩ (q/p)^m [ℓ+ε, ℓ+1-ε]` we have
`‖x(p/q)^i‖ ≥ δ(n)` for `i = 1, …, m`". -/
@[category API, AMS 11, ref "Bug12", group "bug_3_15"]
theorem dist_ge_of_isGood (hp : 0 < p) (hq : 0 < q) (hgood : IsGood p q ε δ t) (a : ℕ) {x : ℝ}
    (hx1 : (t.l : ℝ) + a * (p : ℝ) ^ t.m + ε ≤ x * ((p : ℝ) / q) ^ t.m)
    (hx2 : x * ((p : ℝ) / q) ^ t.m ≤ (t.l : ℝ) + a * (p : ℝ) ^ t.m + 1 - ε) :
    ∀ i ≤ t.m, δ ≤ distToNearestInt (x * ((p : ℝ) / q) ^ i) := by
  have hpne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hqne : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  intro i hi
  obtain ⟨j, hj⟩ : ∃ j, t.m = i + j := ⟨t.m - i, by omega⟩
  set y : ℝ := x * ((p : ℝ) / q) ^ t.m - a * (p : ℝ) ^ t.m with hy
  have hy1 : (t.l : ℝ) + ε ≤ y := by rw [hy]; linarith
  have hy2 : y ≤ (t.l : ℝ) + 1 - ε := by rw [hy]; linarith
  have key : x * ((p : ℝ) / q) ^ i
      = ((q : ℝ) / p) ^ j * y + (a * (p : ℝ) ^ i * (q : ℝ) ^ j) := by
    rw [hy, hj, pow_add, pow_add, div_pow, div_pow, div_pow]
    field_simp
    ring
  have hposj : (0 : ℝ) < ((q : ℝ) / p) ^ j := by positivity
  obtain ⟨k, hk1, hk2⟩ := hgood.trap j (by omega)
  refine le_distToNearestInt_of_mem_Icc (k := k + (a * p ^ i * q ^ j : ℕ)) ?_ ?_
  · rw [key]
    push_cast
    linarith [mul_le_mul_of_nonneg_left hy1 hposj.le]
  · rw [key]
    push_cast
    linarith [mul_le_mul_of_nonneg_left hy2 hposj.le]

/-!
### The nested intervals
-/

/-- One step of the recursion: from the current integer `n`, the triple `f n` chosen for it
produces the next integer `ℓ + (n / q^m)·p^m`. -/
def nextN (p q : ℕ) (f : ℕ → Triple) (n : ℕ) : ℕ :=
  (f n).l + n / q ^ (f n).m * p ^ (f n).m

/-- The sequence of integer parts, starting from `1` (Bugeaud's `I₁ = [1, 2]`). -/
def orbitN (p q : ℕ) (f : ℕ → Triple) : ℕ → ℕ
  | 0 => 1
  | j + 1 => nextN p q f (orbitN p q f j)

/-- The cumulative exponent `m_{h(t₁)} + ⋯ + m_{h(t_j)}` of Bugeaud's proof. -/
def orbitM (p q : ℕ) (f : ℕ → Triple) : ℕ → ℕ
  | 0 => 0
  | j + 1 => orbitM p q f j + (f (orbitN p q f j)).m

/-- Left endpoint of the `j`-th nested interval `Jⱼ`. -/
noncomputable def leftEnd (p q : ℕ) (f : ℕ → Triple) (ε : ℝ) (j : ℕ) : ℝ :=
  ((q : ℝ) / p) ^ orbitM p q f j * (orbitN p q f j + ε)

/-- Right endpoint of the `j`-th nested interval `Jⱼ`. -/
noncomputable def rightEnd (p q : ℕ) (f : ℕ → Triple) (ε : ℝ) (j : ℕ) : ℝ :=
  ((q : ℝ) / p) ^ orbitM p q f j * (orbitN p q f j + 1 - ε)

variable {f : ℕ → Triple}

/-- The residue decomposition `n = nⱼ + a·q^{mⱼ}` supplied by the covering system. -/
theorem orbitN_decomp (hmod : ∀ n, n % q ^ (f n).m = (f n).n) (n : ℕ) :
    n = (f n).n + n / q ^ (f n).m * q ^ (f n).m := by
  conv_lhs => rw [← Nat.div_add_mod n (q ^ (f n).m), hmod n]
  ring

theorem leftEnd_le_succ (hp : 0 < p) (hq : 0 < q)
    (hgood : ∀ n, IsGood p q ε δ (f n)) (hmod : ∀ n, n % q ^ (f n).m = (f n).n) (j : ℕ) :
    leftEnd p q f ε j ≤ leftEnd p q f ε (j + 1) := by
  have hpne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hqne : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have hdecN := orbitN_decomp hmod (orbitN p q f j)
  have hNsucc : orbitN p q f (j + 1)
      = (f (orbitN p q f j)).l
        + orbitN p q f j / q ^ (f (orbitN p q f j)).m * p ^ (f (orbitN p q f j)).m := rfl
  have hMsucc : orbitM p q f (j + 1) = orbitM p q f j + (f (orbitN p q f j)).m := rfl
  simp only [leftEnd]
  rw [hNsucc, hMsucc]
  set n := orbitN p q f j with hn
  set M := orbitM p q f j with hM
  set t := f n with ht
  set a := n / q ^ t.m with ha
  have hdec : (n : ℝ) = (t.n : ℝ) + (a : ℝ) * (q : ℝ) ^ t.m := by exact_mod_cast hdecN
  have hinv : ((q : ℝ) / p) ^ t.m * ((p : ℝ) / q) ^ t.m = 1 := by
    rw [← mul_pow]; field_simp; exact one_pow _
  have hqp : ((q : ℝ) / p) ^ t.m * (p : ℝ) ^ t.m = (q : ℝ) ^ t.m := by rw [div_pow]; field_simp
  have hstep : (t.n : ℝ) + ε ≤ ((q : ℝ) / p) ^ t.m * ((t.l : ℝ) + ε) := by
    have h := mul_le_mul_of_nonneg_left (hgood n).lower
      (by positivity : (0 : ℝ) ≤ ((q : ℝ) / p) ^ t.m)
    calc (t.n : ℝ) + ε = ((q : ℝ) / p) ^ t.m * (((p : ℝ) / q) ^ t.m * ((t.n : ℝ) + ε)) := by
          rw [← mul_assoc, hinv, one_mul]
      _ ≤ _ := h
  rw [pow_add]
  push_cast
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hexp : ((q : ℝ) / p) ^ t.m * ((t.l : ℝ) + (a : ℝ) * (p : ℝ) ^ t.m + ε)
      = ((q : ℝ) / p) ^ t.m * ((t.l : ℝ) + ε) + (a : ℝ) * (q : ℝ) ^ t.m := by
    rw [← hqp]; ring
  rw [hexp, hdec]
  linarith

theorem rightEnd_succ_le (hp : 0 < p) (hq : 0 < q)
    (hgood : ∀ n, IsGood p q ε δ (f n)) (hmod : ∀ n, n % q ^ (f n).m = (f n).n) (j : ℕ) :
    rightEnd p q f ε (j + 1) ≤ rightEnd p q f ε j := by
  have hpne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hqne : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have hdecN := orbitN_decomp hmod (orbitN p q f j)
  have hNsucc : orbitN p q f (j + 1)
      = (f (orbitN p q f j)).l
        + orbitN p q f j / q ^ (f (orbitN p q f j)).m * p ^ (f (orbitN p q f j)).m := rfl
  have hMsucc : orbitM p q f (j + 1) = orbitM p q f j + (f (orbitN p q f j)).m := rfl
  simp only [rightEnd]
  rw [hNsucc, hMsucc]
  set n := orbitN p q f j with hn
  set M := orbitM p q f j with hM
  set t := f n with ht
  set a := n / q ^ t.m with ha
  have hdec : (n : ℝ) = (t.n : ℝ) + (a : ℝ) * (q : ℝ) ^ t.m := by exact_mod_cast hdecN
  have hinv : ((q : ℝ) / p) ^ t.m * ((p : ℝ) / q) ^ t.m = 1 := by
    rw [← mul_pow]; field_simp; exact one_pow _
  have hqp : ((q : ℝ) / p) ^ t.m * (p : ℝ) ^ t.m = (q : ℝ) ^ t.m := by rw [div_pow]; field_simp
  have hstep : ((q : ℝ) / p) ^ t.m * ((t.l : ℝ) + 1 - ε) ≤ (t.n : ℝ) + 1 - ε := by
    have h := mul_le_mul_of_nonneg_left (hgood n).upper
      (by positivity : (0 : ℝ) ≤ ((q : ℝ) / p) ^ t.m)
    calc ((q : ℝ) / p) ^ t.m * ((t.l : ℝ) + 1 - ε)
        ≤ ((q : ℝ) / p) ^ t.m * (((p : ℝ) / q) ^ t.m * ((t.n : ℝ) + 1 - ε)) := h
      _ = (t.n : ℝ) + 1 - ε := by rw [← mul_assoc, hinv, one_mul]
  rw [pow_add]
  push_cast
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hexp : ((q : ℝ) / p) ^ t.m * ((t.l : ℝ) + (a : ℝ) * (p : ℝ) ^ t.m + 1 - ε)
      = ((q : ℝ) / p) ^ t.m * ((t.l : ℝ) + 1 - ε) + (a : ℝ) * (q : ℝ) ^ t.m := by
    rw [← hqp]; ring
  rw [hexp, hdec]
  linarith

theorem leftEnd_le_rightEnd (hp : 0 < p) (hq : 0 < q) (hε : 2 * ε ≤ 1) (j : ℕ) :
    leftEnd p q f ε j ≤ rightEnd p q f ε j :=
  mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- Every exponent `i ≥ 1` falls in exactly one block `(M j, M (j+1)]` of the cumulative
exponent sequence. -/
theorem exists_block (hm : ∀ n, 0 < (f n).m) {i : ℕ} (hi : 1 ≤ i) :
    ∃ j, orbitM p q f j < i ∧ i ≤ orbitM p q f (j + 1) := by
  induction i, hi using Nat.le_induction with
  | base =>
      refine ⟨0, ?_, ?_⟩
      · show orbitM p q f 0 < 1
        simp [orbitM]
      · have h := hm (orbitN p q f 0)
        have e : orbitM p q f (0 + 1) = orbitM p q f 0 + (f (orbitN p q f 0)).m := rfl
        have e0 : orbitM p q f 0 = 0 := rfl
        omega
  | succ i _ ih =>
      obtain ⟨j, h1, h2⟩ := ih
      rcases le_or_gt (i + 1) (orbitM p q f (j + 1)) with h | h
      · exact ⟨j, by omega, h⟩
      · refine ⟨j + 1, by omega, ?_⟩
        have hpos := hm (orbitN p q f (j + 1))
        have e : orbitM p q f (j + 1 + 1)
            = orbitM p q f (j + 1) + (f (orbitN p q f (j + 1))).m := rfl
        omega

/-- The trap of one step, phrased in terms of a cumulative exponent `M`. -/
theorem step_trap (hp : 0 < p) (hq : 0 < q) {M a : ℕ} (hgood : IsGood p q ε δ t) {ξ : ℝ}
    (h1 : (t.l : ℝ) + a * (p : ℝ) ^ t.m + ε ≤ ξ * ((p : ℝ) / q) ^ (M + t.m))
    (h2 : ξ * ((p : ℝ) / q) ^ (M + t.m) ≤ (t.l : ℝ) + a * (p : ℝ) ^ t.m + 1 - ε) :
    ∀ i ≤ t.m, δ ≤ distToNearestInt (ξ * ((p : ℝ) / q) ^ (M + i)) := by
  have e : ∀ k : ℕ, ξ * ((p : ℝ) / q) ^ (M + k) = ξ * ((p : ℝ) / q) ^ M * ((p : ℝ) / q) ^ k := by
    intro k; rw [pow_add, mul_assoc]
  intro i hi
  rw [e]
  exact dist_ge_of_isGood hp hq hgood a (by rw [← e]; exact h1) (by rw [← e]; exact h2) i hi

/-!
### The main construction
-/

/-- **Pollington's construction.**  A covering system of good triples produces a positive real
number whose whole forward orbit under multiplication by `p/q` stays at distance `≥ δ` from the
integers. -/
@[category API, AMS 11, ref "Bug12", group "bug_3_15",
  formal_uses dist_ge_of_isGood, formal_uses exists_block, formal_uses step_trap]
theorem exists_forall_dist_ge (hp : 0 < p) (hq : 0 < q) (hε0 : 0 ≤ ε) (hε : 2 * ε ≤ 1)
    (T : List Triple) (hT : ∀ t ∈ T, IsGood p q ε δ t)
    (hcov : ∀ n : ℕ, ∃ t ∈ T, n % q ^ t.m = t.n) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ i : ℕ, 1 ≤ i → δ ≤ distToNearestInt (ξ * ((p : ℝ) / q) ^ i) := by
  classical
  have hpne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hqne : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  choose f hfT hfmod using hcov
  have hgood : ∀ n, IsGood p q ε δ (f n) := fun n => hT _ (hfT n)
  -- the endpoints of Bugeaud's intervals `Jⱼ` are monotone, resp. antitone
  have hL : Monotone (leftEnd p q f ε) :=
    monotone_nat_of_le_succ (leftEnd_le_succ hp hq hgood hfmod)
  have hR : Antitone (rightEnd p q f ε) :=
    antitone_nat_of_succ_le (rightEnd_succ_le hp hq hgood hfmod)
  have hLR : ∀ i j, leftEnd p q f ε i ≤ rightEnd p q f ε j := by
    intro i j
    rcases le_total i j with h | h
    · exact le_trans (hL h) (leftEnd_le_rightEnd hp hq hε j)
    · exact le_trans (leftEnd_le_rightEnd hp hq hε i) (hR h)
  -- any point of the intersection will do; the supremum of the left endpoints is one
  set ξ : ℝ := sSup (Set.range (leftEnd p q f ε)) with hξ
  have hbdd : BddAbove (Set.range (leftEnd p q f ε)) :=
    ⟨rightEnd p q f ε 0, by rintro _ ⟨i, rfl⟩; exact hLR i 0⟩
  have hmemL : ∀ j, leftEnd p q f ε j ≤ ξ := fun j => le_csSup hbdd ⟨j, rfl⟩
  have hmemR : ∀ j, ξ ≤ rightEnd p q f ε j := by
    intro j
    refine csSup_le ⟨leftEnd p q f ε 0, ⟨0, rfl⟩⟩ ?_
    rintro _ ⟨i, rfl⟩
    exact hLR i j
  have hξpos : 0 < ξ := by
    have h0 := hmemL 0
    have e : leftEnd p q f ε 0 = 1 + ε := by simp [leftEnd, orbitM, orbitN]
    rw [e] at h0
    linarith
  -- `ξ (p/q)^{M j}` lies in the `j`-th window
  have hinv : ∀ M : ℕ, ((q : ℝ) / p) ^ M * ((p : ℝ) / q) ^ M = 1 := by
    intro M; rw [← mul_pow]; field_simp; exact one_pow _
  have ekey : ∀ (z : ℝ) (M : ℕ), ((q : ℝ) / p) ^ M * z * ((p : ℝ) / q) ^ M = z := by
    intro z M
    rw [mul_comm (((q : ℝ) / p) ^ M) z, mul_assoc, hinv M, mul_one]
  have hwin : ∀ j : ℕ, (orbitN p q f j : ℝ) + ε ≤ ξ * ((p : ℝ) / q) ^ orbitM p q f j ∧
      ξ * ((p : ℝ) / q) ^ orbitM p q f j ≤ (orbitN p q f j : ℝ) + 1 - ε := by
    intro j
    have hposM : (0 : ℝ) < ((p : ℝ) / q) ^ orbitM p q f j := by positivity
    refine ⟨?_, ?_⟩
    · have h := mul_le_mul_of_nonneg_right (hmemL j) hposM.le
      simp only [leftEnd] at h
      rwa [ekey] at h
    · have h := mul_le_mul_of_nonneg_right (hmemR j) hposM.le
      simp only [rightEnd] at h
      rwa [ekey] at h
  refine ⟨ξ, hξpos, fun i hi => ?_⟩
  obtain ⟨j, hj1, hj2⟩ := exists_block (p := p) (q := q) (fun n => (hgood n).m_pos) hi
  have hNsucc : orbitN p q f (j + 1)
      = (f (orbitN p q f j)).l
        + orbitN p q f j / q ^ (f (orbitN p q f j)).m * p ^ (f (orbitN p q f j)).m := rfl
  have hMsucc : orbitM p q f (j + 1) = orbitM p q f j + (f (orbitN p q f j)).m := rfl
  have hx := hwin (j + 1)
  rw [hNsucc, hMsucc] at hx
  push_cast at hx
  have hmain := step_trap hp hq (hgood (orbitN p q f j))
    (a := orbitN p q f j / q ^ (f (orbitN p q f j)).m) hx.1 hx.2
    (i - orbitM p q f j) (by omega)
  rwa [show orbitM p q f j + (i - orbitM p q f j) = i from by omega] at hmain

/-!
### The certificate

Everything above is decided by inequalities between natural numbers.  Writing `ε = a/(a+a')`,
`δ = c/d` and `b = a+a'`, the `i`-th backward window of the triple `t` is `[U/D, V/D]` with
`U = qⁱ(ℓb+a)`, `V = qⁱ(ℓb+a')` and `D = pⁱ b`.
-/

/-- The integer just below the `i`-th backward window: `k = ⌊U/D⌋`. -/
def windowK (p q a a' : ℕ) (t : Triple) (i : ℕ) : ℕ :=
  q ^ i * (t.l * (a + a') + a) / (p ^ i * (a + a'))

/-- The `i`-th window check: `[U/D, V/D] ⊆ [k + c/d, k + 1 - c/d]`. -/
def stepOK (p q a a' c d : ℕ) (t : Triple) (i : ℕ) : Bool :=
  decide (d * (windowK p q a a' t i * (p ^ i * (a + a'))) + c * (p ^ i * (a + a'))
      ≤ d * (q ^ i * (t.l * (a + a') + a))) &&
  decide (d * (q ^ i * (t.l * (a + a') + a')) + c * (p ^ i * (a + a'))
      ≤ d * ((windowK p q a a' t i + 1) * (p ^ i * (a + a'))))

/-- The full check for one triple. -/
def tripleOK (p q a a' c d : ℕ) (t : Triple) : Bool :=
  decide (0 < t.l) && decide (0 < t.m) &&
    decide (p ^ t.m * (t.n * (a + a') + a) ≤ q ^ t.m * (t.l * (a + a') + a)) &&
    decide (q ^ t.m * (t.l * (a + a') + a') ≤ p ^ t.m * (t.n * (a + a') + a')) &&
    (List.range (t.m + 1)).all (stepOK p q a a' c d t)

@[category API, AMS 11, ref "Bug12", group "bug_3_15"]
theorem isGood_of_tripleOK {a a' c d : ℕ} (hp : 0 < p) (hq : 0 < q) (ha : 0 < a) (ha' : 0 < a')
    (hd : 0 < d) (h : tripleOK p q a a' c d t = true) :
    IsGood p q ((a : ℝ) / ((a : ℝ) + a')) ((c : ℝ) / d) t := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have haR' : (0 : ℝ) < (a' : ℝ) := by exact_mod_cast ha'
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  simp only [tripleOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hl, hm⟩, hlow⟩, hup⟩, hstep⟩ := h
  refine ⟨hl, hm, ?_, ?_, ?_⟩
  · have hcast : ((p ^ t.m * (t.n * (a + a') + a) : ℕ) : ℝ)
        ≤ ((q ^ t.m * (t.l * (a + a') + a) : ℕ) : ℝ) := by exact_mod_cast hlow
    push_cast at hcast
    rw [div_pow, ← sub_nonneg]
    have key : (t.l : ℝ) + (a : ℝ) / ((a : ℝ) + a')
          - (p : ℝ) ^ t.m / (q : ℝ) ^ t.m * ((t.n : ℝ) + (a : ℝ) / ((a : ℝ) + a'))
        = ((q : ℝ) ^ t.m * ((t.l : ℝ) * ((a : ℝ) + a') + a)
            - (p : ℝ) ^ t.m * ((t.n : ℝ) * ((a : ℝ) + a') + a))
          / ((q : ℝ) ^ t.m * ((a : ℝ) + a')) := by
      field_simp
      try ring
    rw [key]
    apply div_nonneg _ (by positivity)
    linarith
  · have hcast : ((q ^ t.m * (t.l * (a + a') + a') : ℕ) : ℝ)
        ≤ ((p ^ t.m * (t.n * (a + a') + a') : ℕ) : ℝ) := by exact_mod_cast hup
    push_cast at hcast
    rw [div_pow, ← sub_nonneg]
    have key : (p : ℝ) ^ t.m / (q : ℝ) ^ t.m * ((t.n : ℝ) + 1 - (a : ℝ) / ((a : ℝ) + a'))
          - ((t.l : ℝ) + 1 - (a : ℝ) / ((a : ℝ) + a'))
        = ((p : ℝ) ^ t.m * ((t.n : ℝ) * ((a : ℝ) + a') + a')
            - (q : ℝ) ^ t.m * ((t.l : ℝ) * ((a : ℝ) + a') + a'))
          / ((q : ℝ) ^ t.m * ((a : ℝ) + a')) := by
      field_simp
      try ring
    rw [key]
    apply div_nonneg _ (by positivity)
    linarith
  · intro i hi
    have hi' : i ∈ List.range (t.m + 1) := by simp; omega
    have hstepi := (List.all_eq_true.mp hstep) i hi'
    simp only [stepOK, Bool.and_eq_true, decide_eq_true_eq] at hstepi
    obtain ⟨hc1, hc2⟩ := hstepi
    refine ⟨(windowK p q a a' t i : ℤ), ?_, ?_⟩
    · have e1 : ((d * (windowK p q a a' t i * (p ^ i * (a + a'))) + c * (p ^ i * (a + a')) : ℕ) : ℝ)
          ≤ ((d * (q ^ i * (t.l * (a + a') + a)) : ℕ) : ℝ) := by exact_mod_cast hc1
      push_cast at e1
      rw [div_pow, ← sub_nonneg]
      have key : (q : ℝ) ^ i / (p : ℝ) ^ i * ((t.l : ℝ) + (a : ℝ) / ((a : ℝ) + a'))
            - (((windowK p q a a' t i : ℤ) : ℝ) + (c : ℝ) / (d : ℝ))
          = ((d : ℝ) * ((q : ℝ) ^ i * ((t.l : ℝ) * ((a : ℝ) + a') + a))
              - ((d : ℝ) * ((windowK p q a a' t i : ℝ) * ((p : ℝ) ^ i * ((a : ℝ) + a')))
                + (c : ℝ) * ((p : ℝ) ^ i * ((a : ℝ) + a'))))
            / ((d : ℝ) * ((p : ℝ) ^ i * ((a : ℝ) + a'))) := by
        push_cast
        field_simp
        try ring
      rw [key]
      apply div_nonneg _ (by positivity)
      linarith
    · have e2 : ((d * (q ^ i * (t.l * (a + a') + a')) + c * (p ^ i * (a + a')) : ℕ) : ℝ)
          ≤ ((d * ((windowK p q a a' t i + 1) * (p ^ i * (a + a'))) : ℕ) : ℝ) := by
        exact_mod_cast hc2
      push_cast at e2
      rw [div_pow, ← sub_nonneg]
      have key : ((windowK p q a a' t i : ℤ) : ℝ) + 1 - (c : ℝ) / (d : ℝ)
            - (q : ℝ) ^ i / (p : ℝ) ^ i * ((t.l : ℝ) + 1 - (a : ℝ) / ((a : ℝ) + a'))
          = ((d : ℝ) * (((windowK p q a a' t i : ℝ) + 1) * ((p : ℝ) ^ i * ((a : ℝ) + a')))
              - ((d : ℝ) * ((q : ℝ) ^ i * ((t.l : ℝ) * ((a : ℝ) + a') + a'))
                + (c : ℝ) * ((p : ℝ) ^ i * ((a : ℝ) + a'))))
            / ((d : ℝ) * ((p : ℝ) ^ i * ((a : ℝ) + a'))) := by
        push_cast
        field_simp
        try ring
      rw [key]
      apply div_nonneg _ (by positivity)
      linarith

/-- **Pollington's construction, certified form.**  A `by decide` on `tripleOK` and on the
covering property yields a real number keeping the whole orbit `ξ (p/q)ⁿ`, `n ≥ 1`, at distance
at least `c/d` from `ℤ`. -/
@[category API, AMS 11, ref "Bug12", group "bug_3_15",
  formal_uses exists_forall_dist_ge, formal_uses isGood_of_tripleOK]
theorem exists_forall_dist_ge_of_cert {a a' c d : ℕ} (hp : 0 < p) (hq : 0 < q) (ha : 0 < a)
    (ha' : a ≤ a') (hd : 0 < d) (T : List Triple)
    (hall : T.all (tripleOK p q a a' c d) = true)
    (hcov : ∀ n : ℕ, ∃ t ∈ T, n % q ^ t.m = t.n) :
    ∃ ξ : ℝ, 0 < ξ ∧
      ∀ i : ℕ, 1 ≤ i → (c : ℝ) / d ≤ distToNearestInt (ξ * ((p : ℝ) / q) ^ i) := by
  have haa' : (0 : ℕ) < a' := lt_of_lt_of_le ha ha'
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have haR' : (0 : ℝ) < (a' : ℝ) := by exact_mod_cast haa'
  refine exists_forall_dist_ge hp hq (by positivity) ?_ T
    (fun t ht => isGood_of_tripleOK hp hq ha haa' hd ((List.all_eq_true.mp hall) t ht)) hcov
  rw [mul_div_assoc', div_le_one (by positivity)]
  have : (a : ℝ) ≤ (a' : ℝ) := by exact_mod_cast ha'
  linarith

/-!
### Theorem 3.15
-/

/-- Bugeaud's twelve triples `(nⱼ, ℓⱼ, mⱼ)` for `p/q = 3/2`.  The residues
`1 (4), 2 (4), 3 (8), 4 (8), 7 (16), 8 (16), 15 (32), 16 (32), 31 (64), 32 (64), 0 (64),
63 (64)` are an exact cover of `ℤ/64ℤ`. -/
def triples12 : List Triple :=
  [⟨1, 3, 2⟩, ⟨2, 5, 2⟩, ⟨3, 12, 3⟩, ⟨4, 14, 3⟩, ⟨7, 36, 4⟩, ⟨8, 44, 4⟩,
   ⟨15, 117, 5⟩, ⟨16, 125, 5⟩, ⟨31, 360, 6⟩, ⟨32, 368, 6⟩, ⟨0, 8, 6⟩, ⟨63, 720, 6⟩]

@[category API, AMS 11, ref "Bug12", group "bug_3_15"]
theorem triples12_covering (n : ℕ) : ∃ t ∈ triples12, n % 2 ^ t.m = t.n := by
  have key : ∀ r < 64, ∃ t ∈ triples12, r % 2 ^ t.m = t.n := by decide
  have hm : ∀ t ∈ triples12, t.m ≤ 6 := by decide
  obtain ⟨t, ht, hr⟩ := key (n % 64) (Nat.mod_lt _ (by norm_num))
  refine ⟨t, ht, ?_⟩
  have hdvd : (2 : ℕ) ^ t.m ∣ 64 := by
    have h := pow_dvd_pow 2 (hm t ht)
    norm_num at h
    exact h
  rw [← Nat.mod_mod_of_dvd n hdvd]
  exact hr

@[category API, AMS 11, ref "Bug12", group "bug_3_15"]
theorem triples12_ok : triples12.all (tripleOK 3 2 9 56 4 65) = true := by decide

/-- **Theorem 3.15** (Pollington).  There is a real number `ξ` with `‖ξ (3/2)ⁿ‖ ≥ 4/65` for
every `n ≥ 1`.

The witness is the supremum of the left endpoints of Pollington's nested intervals, built from
the twelve covering triples `Bugeaud.Pollington.triples12` with `ε = 9/65`. -/
@[category research solved, AMS 11, ref "Bug12", group "bug_3_15",
  formal_uses exists_forall_dist_ge_of_cert, formal_uses triples12_ok,
  formal_uses triples12_covering]
theorem theorem_3_15 :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ n : ℕ, 1 ≤ n → (4 : ℝ) / 65 ≤ distToNearestInt (ξ * (3 / 2) ^ n) := by
  obtain ⟨ξ, hξ, h⟩ := exists_forall_dist_ge_of_cert (p := 3) (q := 2) (a := 9) (a' := 56)
    (c := 4) (d := 65) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    triples12 triples12_ok triples12_covering
  refine ⟨ξ, hξ, fun n hn => ?_⟩
  have h' := h n hn
  norm_num at h' ⊢
  exact h'

end Pollington
end Bugeaud
