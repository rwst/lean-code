/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import RB.OrbitKernel
import RB.ScaledKernel
import Mathlib.Data.Nat.Log
import Mathlib.Order.Interval.Set.Nat
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Chain rigidity for same-gap violators (plan-B2A2, WP5 — T1c part 1)

The **unconditional** half of [B2A2] §2.5: what can be said about the kernel violators of
the orbit word *without* knowing anything about the constant `K`.  Nothing here uses a
Diophantine theorem, and nothing here assumes `K ∈ ℚ` — the whole file is an elimination
argument between two violators, valid for an **arbitrary real multiplier**.

## The elimination

Fix a multiplier `δ` and write `v(a,c) := δ((3/2)^c − (3/2)^a)` (`RB.chainVal`).  Two
violators of the *same gap* `d = c − a` are exactly a pair `(a, c)`, `(a+e, c+e)`, and the
values are locked by one line of algebra (`two_pow_mul_chainVal_shift`):

  `2^e · v(a+e, c+e) = 3^e · v(a, c)`.

Write `Dᵢ` for the nearest integers and `ηᵢ` for the errors.  Then
`2^e·D₂ − 3^e·D₁ = 3^e e₁ − 2^e e₂` is an **integer** bounded by `3^e η₁ + 2^e η₂`, so as soon
as that is `< 1` — the pair is *clustered* — the integer vanishes:

  `2^e · D₂ = 3^e · D₁`   (`RB.exact_relation`),

whence `2^e ∣ D₁` (`RB.two_pow_dvd_of_exact_relation`).  [B2A2] §2.5 writes this with two
indices, `2^{Δc}D₂ = 3^{Δa}D₁`; for same-gap violators `Δa = Δc` necessarily, so the two
collapse to the single shift `e`.

The relation **composes** (`RB.exact_relation_trans`), so along a chain of consecutively
clustered same-gap violators the shifts *add*: total shift `E` ⇒ `2^E ∣ D₁`
(`RB.chain_exact_relation`, `RB.chain_two_pow_dvd`).  That is the plan's "2-valuation chain
cap", and it is where the counting bites: `2^E ≤ |D₁|`, so `E ≤ log₂|D₁|`
(`RB.le_log_of_two_pow_dvd`), and a chain has at most `log₂|D₁| + 1` members
(`RB.ncard_le_of_two_pow_dvd`) — the plan's "per-octave same-gap violator bound".

## The orbit instance: shift becomes repetition length

For the actual orbit (`δ = K x₀`, unconditional in `K`) the nearest integer is `x_c − x_a`
and the error is the defect difference `θ_c − θ_a`, bounded by `(2/3)^k` on a length-`k`
repetition.  So clustered same-gap *repetitions* are geometrically locked
(`RB.exact_relation_of_repetitions`), and the chain conclusion `2^E ∣ x_c − x_a` says — by
window rigidity (`RB.isRepetition_iff_dvd`) — that **the base windows already agree for `E`
letters** (`RB.isRepetition_of_chain`).  Chain rigidity converts *shift* into *repetition
length*; the existing ceiling then caps it for free:

  `2^{E+c} < 3^c(x₀+1)`, and at `x₀ = 1` the certified `41E ≤ 24c + 40` (`E ≤ 0.585c + 1`).

This is exactly [B2A2] §2.5's "the total 2-shift along any chain of clustered same-gap
violators is capped by `0.585 c₁`", now a theorem.

## Honest scope

These are **counterfactual** structure theorems.  WP6(i)'s numerics ([B2A2] §2.5's box:
repetition quality for `c ≥ 100` maxes at `0.1089` and decays) indicate that the clustered
same-gap families they cap are *empty* in the observable range, so nothing here yields a
complexity constant on its own; that was WP6's GO/NO-GO, and the data lean NO.  What the
file does deliver is the unconditional structure section the eventual T1c write-up needs,
and a cap that any future counting argument may quote.

## Relation to `BB13` (a correction to [B2A2] rev. 4)

Rev. 4 of the plan expects WP5 to be "largely a port" of `BB13/LineTower.lean` +
`BB13/MahlerCount.lean`.  It is **not**, and the reason is worth recording: BB13's per-line
theory (`collinear_scaling`, `sameLine_lt_div_fArch`) is *multiplier-free and single-index*
— it is about `mₙ = round((p/q)ⁿ)` — whereas WP5 is about *pairs* at a fixed gap with the
unknown multiplier `K`.  The shapes of the conclusions do agree (`collinear_scaling`'s
`p^{b−a}mₐ = q^{b−a}m_b` is this file's `2^e D₂ = 3^e D₁`), but the *hypotheses* are
disjoint: BB13 gets collinearity from a Diophantine input, whereas clustering is elementary.
Porting would have meant introducing the multiplier into BB13's frame; proving it here is
twenty lines and stays axiom-free.  The plan's Q2/Q3 (WP11) remain genuine ports — they are
about *counted* line covers, which this file does not attempt.

## Contents

* `RB.chainVal`, `RB.two_pow_mul_chainVal_shift` — the same-gap family and its scaling.
* **`RB.exact_relation`** — the clustered-pair exact-relation lemma (arbitrary real `δ`).
* `RB.two_pow_dvd_of_exact_relation`, `RB.exact_relation_trans`, `RB.chain_exact_relation`,
  **`RB.chain_two_pow_dvd`** — the 2-valuation chain cap.
* `RB.le_log_of_two_pow_dvd`, `RB.finite_of_two_pow_dvd`, **`RB.ncard_le_of_two_pow_dvd`** —
  the per-base counting bound.
* **`RB.exact_relation_of_repetitions`**, **`RB.isRepetition_of_chain`**,
  `RB.chain_pow_lt`, `RB.chain_linear_bound`, `RB.chain_length_linear_bound` — the orbit
  instance and the certified `0.585 c` cap.
* `RB.IsClustered`, **`RB.exact_relation_of_violators`**, `RB.clusteredShifts_ncard_le` —
  the `δ`-scaled violator instance (`RB.scaledViolators`).

## References

* [B2A2] `plans/plan-B2A2.html`: §2.5 (this file), WP5, T1c; §0-ter Q2 (the port claim).
* [Dub09] A. Dubickas, Glasgow Math. J. **51** (2009), 243–252 — Cor. 4, the standing record
  the T1c programme aims past.
* [M4A3] `plan-M4A3.html` / `TH/` — the template architecture.
-/

namespace RB

/-! ## The same-gap family and its scaling -/

/-- The **kernel value** `v(a,c) = δ·((3/2)^c − (3/2)^a)` over `ℝ`, for an *arbitrary* real
multiplier `δ`.  At `δ = K x₀` this is the orbit kernel of [B2A2] §2.1; at rational `δ` it is
the value measured by `RB.scaledViolators`. -/
@[category API, AMS 11 68, ref "B2A2", group "rb_rational_base"]
noncomputable def chainVal (δ : ℝ) (a c : ℕ) : ℝ := δ * ((3 / 2 : ℝ) ^ c - (3 / 2 : ℝ) ^ a)

/-- **Same-gap violators are shifts of one another, and their values scale**:
`2^e·v(a+e, c+e) = 3^e·v(a, c)`.  This one identity is the whole elimination — the unknown
multiplier `δ` cancels because it is a *common factor*, not because it is known. -/
@[category research solved, AMS 11 68, ref "B2A2", group "rb_rational_base"]
theorem two_pow_mul_chainVal_shift (δ : ℝ) (a c e : ℕ) :
    (2 : ℝ) ^ e * chainVal δ (a + e) (c + e) = 3 ^ e * chainVal δ a c := by
  have h : (2 : ℝ) ^ e * (3 / 2 : ℝ) ^ e = 3 ^ e := by
    rw [← mul_pow]; norm_num
  unfold chainVal
  rw [pow_add, pow_add]
  linear_combination (δ * ((3 / 2 : ℝ) ^ c - (3 / 2 : ℝ) ^ a)) * h

/-! ## The clustered-pair exact relation -/

private lemma coprime_two_three_pow (e : ℕ) : IsCoprime ((2 : ℤ) ^ e) ((3 : ℤ) ^ e) := by
  refine IsCoprime.pow ?_
  rw [Int.isCoprime_iff_gcd_eq_one]
  decide

/-- **The clustered-pair exact-relation lemma** ([B2A2] §2.5, "what works (unconditional)").

Two same-gap violators — a pair `(a,c)` and its `e`-shift `(a+e, c+e)` — with nearest
integers `D₁, D₂` and errors `η₁, η₂` satisfy the **exact** relation

  `2^e·D₂ = 3^e·D₁`

as soon as `3^e η₁ + 2^e η₂ < 1` (the pair is *clustered*).  The proof is the scaling
identity `two_pow_mul_chainVal_shift` plus the observation that `2^e D₂ − 3^e D₁` is an
integer of absolute value `≤ 3^e η₁ + 2^e η₂`.

Unconditional in every sense: `δ` is an arbitrary real, no Diophantine input is used, and
`D₁, D₂` are arbitrary integers (they need not be the *nearest* ones — only close). -/
@[category research solved, AMS 11 68, ref "B2A2", group "rb_rational_base"]
theorem exact_relation {δ η₁ η₂ : ℝ} {a c e : ℕ} {D₁ D₂ : ℤ}
    (h₁ : |chainVal δ a c - (D₁ : ℝ)| ≤ η₁)
    (h₂ : |chainVal δ (a + e) (c + e) - (D₂ : ℝ)| ≤ η₂)
    (hcl : (3 : ℝ) ^ e * η₁ + 2 ^ e * η₂ < 1) :
    (2 : ℤ) ^ e * D₂ = 3 ^ e * D₁ := by
  have hscale := two_pow_mul_chainVal_shift δ a c e
  have hreal : (((2 : ℤ) ^ e * D₂ - 3 ^ e * D₁ : ℤ) : ℝ)
      = 2 ^ e * ((D₂ : ℝ) - chainVal δ (a + e) (c + e))
        + 3 ^ e * (chainVal δ a c - (D₁ : ℝ)) := by
    push_cast
    linarith [hscale]
  have e1 : |(2 : ℝ) ^ e * ((D₂ : ℝ) - chainVal δ (a + e) (c + e))| ≤ 2 ^ e * η₂ := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ e), abs_sub_comm]
    exact mul_le_mul_of_nonneg_left h₂ (by positivity)
  have e2 : |(3 : ℝ) ^ e * (chainVal δ a c - (D₁ : ℝ))| ≤ 3 ^ e * η₁ := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ e)]
    exact mul_le_mul_of_nonneg_left h₁ (by positivity)
  have hb : |(((2 : ℤ) ^ e * D₂ - 3 ^ e * D₁ : ℤ) : ℝ)| < 1 := by
    rw [hreal]
    calc |(2 : ℝ) ^ e * ((D₂ : ℝ) - chainVal δ (a + e) (c + e))
            + 3 ^ e * (chainVal δ a c - (D₁ : ℝ))|
        ≤ |(2 : ℝ) ^ e * ((D₂ : ℝ) - chainVal δ (a + e) (c + e))|
            + |(3 : ℝ) ^ e * (chainVal δ a c - (D₁ : ℝ))| := abs_add_le _ _
      _ < 1 := by linarith
  have hcast : ((|(2 : ℤ) ^ e * D₂ - 3 ^ e * D₁| : ℤ) : ℝ) < ((1 : ℤ) : ℝ) := by
    push_cast
    rw [abs_lt] at hb ⊢
    push_cast at hb
    exact hb
  have hZ : |(2 : ℤ) ^ e * D₂ - 3 ^ e * D₁| < 1 := by exact_mod_cast hcast
  have h0 : (2 : ℤ) ^ e * D₂ - 3 ^ e * D₁ = 0 := by
    rcases abs_lt.mp hZ with ⟨hl, hr⟩
    omega
  linear_combination h0

/-- A convenient sufficient form of clustering, matching [B2A2] §2.5's `3^{Δa}η₁ < 1/2`: if
the *later* violator is at least as good as the base (`k ≤ k'`), a single inequality on the
base does it, because `2^e ≤ 3^e` absorbs the second term. -/
@[category API, AMS 11 68, ref "B2A2", group "rb_rational_base"]
theorem clustered_of_le {e k k' : ℕ} (hk : k ≤ k')
    (h : (3 : ℝ) ^ e * (2 / 3 : ℝ) ^ k < 1 / 2) :
    (3 : ℝ) ^ e * (2 / 3 : ℝ) ^ k + 2 ^ e * (2 / 3 : ℝ) ^ k' < 1 := by
  have h1 : (2 : ℝ) ^ e ≤ 3 ^ e := by gcongr; norm_num
  have h2 : (2 / 3 : ℝ) ^ k' ≤ (2 / 3 : ℝ) ^ k :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
  have key : (2 : ℝ) ^ e * (2 / 3 : ℝ) ^ k' ≤ 3 ^ e * (2 / 3 : ℝ) ^ k :=
    calc (2 : ℝ) ^ e * (2 / 3 : ℝ) ^ k' ≤ 3 ^ e * (2 / 3 : ℝ) ^ k' :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ 3 ^ e * (2 / 3 : ℝ) ^ k := mul_le_mul_of_nonneg_left h2 (by positivity)
  linarith

/-! ## Divisibility, composition, and the chain -/

/-- The exact relation is a **2-adic statement about the base**: `2^e ∣ D₁`.  (`2^e` and `3^e`
are coprime, so the `3^e` on the right cannot absorb the `2`-power.) -/
@[category research solved, AMS 11 68, ref "B2A2", group "rb_rational_base"]
theorem two_pow_dvd_of_exact_relation {D₁ D₂ : ℤ} {e : ℕ}
    (h : (2 : ℤ) ^ e * D₂ = 3 ^ e * D₁) : (2 : ℤ) ^ e ∣ D₁ := by
  have hdvd : (2 : ℤ) ^ e ∣ 3 ^ e * D₁ := ⟨D₂, h.symm⟩
  exact (coprime_two_three_pow e).dvd_of_dvd_mul_left hdvd

/-- **The relation composes**, and the shifts *add*.  This is why chains, not just pairs,
are constrained: a length-`r` chain of consecutively clustered same-gap violators behaves
like a single clustered pair of shift `e₁ + ⋯ + e_r`. -/
@[category research solved, AMS 11 68, ref "B2A2", group "rb_rational_base"]
theorem exact_relation_trans {D₁ D₂ D₃ : ℤ} {e f : ℕ}
    (h₁ : (2 : ℤ) ^ e * D₂ = 3 ^ e * D₁) (h₂ : (2 : ℤ) ^ f * D₃ = 3 ^ f * D₂) :
    (2 : ℤ) ^ (e + f) * D₃ = 3 ^ (e + f) * D₁ := by
  rw [pow_add, pow_add]
  linear_combination (2 : ℤ) ^ e * h₂ + (3 : ℤ) ^ f * h₁

/-- **The chain relation** ([B2A2] §2.5): a chain of same-gap violators at shifts
`A 0 ≤ A 1 ≤ ⋯ ≤ A r`, consecutive members clustered, satisfies the exact relation of its
*total* shift `A r − A 0`. -/
@[category research solved, AMS 11 68, ref "B2A2", group "rb_rational_base"]
theorem chain_exact_relation {A : ℕ → ℕ} {D : ℕ → ℤ} (hA : Monotone A) :
    ∀ r : ℕ, (∀ i < r, (2 : ℤ) ^ (A (i + 1) - A i) * D (i + 1)
        = 3 ^ (A (i + 1) - A i) * D i) →
      (2 : ℤ) ^ (A r - A 0) * D r = 3 ^ (A r - A 0) * D 0 := by
  intro r
  induction r with
  | zero => intro _; simp
  | succ r ih =>
    intro hstep
    have hprev := ih fun i hi => hstep i (by omega)
    have hlast := hstep r (by omega)
    have hcomp := exact_relation_trans hprev hlast
    have h1 : A 0 ≤ A r := hA (by omega)
    have h2 : A r ≤ A (r + 1) := hA (by omega)
    have he : A r - A 0 + (A (r + 1) - A r) = A (r + 1) - A 0 := by omega
    rwa [he] at hcomp

/-- **The 2-valuation chain cap** ([B2A2] §2.5's deliverable): the *total* shift of a chain of
consecutively clustered same-gap violators divides into the base integer,
`2^{A r − A 0} ∣ D₀`. -/
@[category research solved, AMS 11 68, ref "B2A2", group "rb_rational_base"]
theorem chain_two_pow_dvd {A : ℕ → ℕ} {D : ℕ → ℤ} (hA : Monotone A) (r : ℕ)
    (hstep : ∀ i < r, (2 : ℤ) ^ (A (i + 1) - A i) * D (i + 1)
      = 3 ^ (A (i + 1) - A i) * D i) :
    (2 : ℤ) ^ (A r - A 0) ∣ D 0 :=
  two_pow_dvd_of_exact_relation (chain_exact_relation hA r hstep)

/-! ## The counting bound -/

/-- `2^m ∣ D ≠ 0` ⇒ `2^m ≤ |D|`. -/
@[category API, AMS 11 68, ref "B2A2", group "rb_rational_base"]
theorem two_pow_le_abs_of_dvd {D : ℤ} {m : ℕ} (hD : D ≠ 0) (h : (2 : ℤ) ^ m ∣ D) :
    (2 : ℤ) ^ m ≤ |D| :=
  Int.le_of_dvd (abs_pos.mpr hD) ((dvd_abs _ _).mpr h)

/-- `2^m ∣ D ≠ 0` ⇒ `m ≤ log₂|D|` — the cap in counting form. -/
@[category research solved, AMS 11 68, ref "B2A2", group "rb_rational_base"]
theorem le_log_of_two_pow_dvd {D : ℤ} {m : ℕ} (hD : D ≠ 0) (h : (2 : ℤ) ^ m ∣ D) :
    m ≤ Nat.log 2 D.natAbs := by
  have h1 := two_pow_le_abs_of_dvd hD h
  rw [Int.abs_eq_natAbs] at h1
  have h2 : (2 : ℕ) ^ m ≤ D.natAbs := by exact_mod_cast h1
  exact Nat.le_log_of_pow_le (by norm_num) h2

private lemma subset_Iic_of_two_pow_dvd {S : Set ℕ} {D : ℤ} (hD : D ≠ 0)
    (hS : ∀ e ∈ S, (2 : ℤ) ^ e ∣ D) :
    S ⊆ Set.Iic (Nat.log 2 D.natAbs) := fun e he => le_log_of_two_pow_dvd hD (hS e he)

/-- Any set of shifts dividing a fixed nonzero integer is **finite**. -/
@[category research solved, AMS 11 68, ref "B2A2", group "rb_rational_base"]
theorem finite_of_two_pow_dvd {S : Set ℕ} {D : ℤ} (hD : D ≠ 0)
    (hS : ∀ e ∈ S, (2 : ℤ) ^ e ∣ D) : S.Finite :=
  Set.Finite.subset (Set.finite_Iic _) (subset_Iic_of_two_pow_dvd hD hS)

/-- **The per-base counting bound** ([B2A2] §2.5's "per-octave same-gap violator bounds"):
at most `log₂|D| + 1` shifts can be clustered against a base with nonzero integer `D`.
Linear in the position, since `|D| ≤ K(3/2)^c` for the orbit — see `chain_linear_bound`. -/
@[category research solved, AMS 11 68, ref "B2A2", group "rb_rational_base"]
theorem ncard_le_of_two_pow_dvd {S : Set ℕ} {D : ℤ} (hD : D ≠ 0)
    (hS : ∀ e ∈ S, (2 : ℤ) ^ e ∣ D) : S.ncard ≤ Nat.log 2 D.natAbs + 1 :=
  calc S.ncard ≤ (Set.Iic (Nat.log 2 D.natAbs)).ncard :=
        Set.ncard_le_ncard (subset_Iic_of_two_pow_dvd hD hS) (Set.finite_Iic _)
    _ = Nat.log 2 D.natAbs + 1 := Set.ncard_Iic_nat _

/-! ## The orbit instance -/

/-- For the orbit multiplier `δ = K x₀` the nearest integer is `x_c − x_a` and the error is
the defect difference `θ_c − θ_a`.  No hypothesis on `K` whatsoever. -/
@[category API, AMS 11 68, ref "B2A2", group "rb_rational_base"]
theorem chainVal_K_sub_intCast (x₀ a c : ℕ) :
    chainVal (K x₀) a c - (((x x₀ c : ℤ) - (x x₀ a : ℤ) : ℤ) : ℝ) = tail x₀ c - tail x₀ a := by
  unfold chainVal tail
  push_cast
  ring

/-- A length-`k` repetition bounds the orbit error by `(2/3)^k` (`RB.dist_le_of_repetition`
over `ℝ`, with the rationality hypothesis dropped — it was never needed for the bound). -/
@[category research solved, AMS 11 68, ref "B2A2", group "rb_rational_base"]
theorem abs_chainVal_sub_le_of_repetition {x₀ : ℕ} (hx₀ : 0 < x₀) {a c k : ℕ}
    (h : IsRepetition x₀ a c k) :
    |chainVal (K x₀) a c - (((x x₀ c : ℤ) - (x x₀ a : ℤ) : ℤ) : ℝ)| ≤ (2 / 3 : ℝ) ^ k := by
  rw [chainVal_K_sub_intCast]
  exact abs_tail_sub_le_of_repetition hx₀ h

/-- **Clustered same-gap repetitions are geometrically locked** — the orbit form of
`exact_relation`, unconditional in `K`:

  `2^e·(x_{c+e} − x_{a+e}) = 3^e·(x_c − x_a)`.

The hypothesis is [B2A2] §2.5's clustering; `clustered_of_le` supplies it from the plan's
`3^e(2/3)^k < 1/2` whenever the shifted repetition is at least as long. -/
@[category research solved, AMS 11 68, ref "B2A2" "Dub09", group "rb_rational_base"]
theorem exact_relation_of_repetitions {x₀ : ℕ} (hx₀ : 0 < x₀) {a c e k k' : ℕ}
    (h₁ : IsRepetition x₀ a c k) (h₂ : IsRepetition x₀ (a + e) (c + e) k')
    (hcl : (3 : ℝ) ^ e * (2 / 3 : ℝ) ^ k + 2 ^ e * (2 / 3 : ℝ) ^ k' < 1) :
    (2 : ℤ) ^ e * ((x x₀ (c + e) : ℤ) - x x₀ (a + e))
      = 3 ^ e * ((x x₀ c : ℤ) - x x₀ a) :=
  exact_relation (abs_chainVal_sub_le_of_repetition hx₀ h₁)
    (abs_chainVal_sub_le_of_repetition hx₀ h₂) hcl

/-- **Chain rigidity for the orbit, in one sentence**: a chain of consecutively clustered
same-gap repetitions of total shift `A r` forces the *base* windows to agree for `A r`
letters — the shift is converted into repetition length.

Everything downstream (`chain_pow_lt`, `chain_linear_bound`) is then the existing repetition
ceiling applied to this longer repetition. -/
@[category research solved, AMS 11 68, ref "B2A2", group "rb_rational_base"]
theorem isRepetition_of_chain {x₀ a c : ℕ} (hx₀ : 0 < x₀) {A k : ℕ → ℕ}
    (hA : Monotone A) (hA0 : A 0 = 0) (r : ℕ)
    (hrep : ∀ i ≤ r, IsRepetition x₀ (a + A i) (c + A i) (k i))
    (hcl : ∀ i < r, (3 : ℝ) ^ (A (i + 1) - A i) * (2 / 3 : ℝ) ^ k i
      + 2 ^ (A (i + 1) - A i) * (2 / 3 : ℝ) ^ k (i + 1) < 1) :
    IsRepetition x₀ a c (A r) := by
  have hstep : ∀ i < r,
      (2 : ℤ) ^ (A (i + 1) - A i) * ((x x₀ (c + A (i + 1)) : ℤ) - x x₀ (a + A (i + 1)))
        = 3 ^ (A (i + 1) - A i) * ((x x₀ (c + A i) : ℤ) - x x₀ (a + A i)) := by
    intro i hi
    have hmono : A i ≤ A (i + 1) := hA (by omega)
    have hEa : a + A i + (A (i + 1) - A i) = a + A (i + 1) := by omega
    have hEc : c + A i + (A (i + 1) - A i) = c + A (i + 1) := by omega
    have h2 := hrep (i + 1) (by omega)
    rw [← hEa, ← hEc] at h2
    have h3 := exact_relation_of_repetitions hx₀ (hrep i (by omega)) h2 (hcl i hi)
    rwa [hEa, hEc] at h3
  have hdvd := chain_two_pow_dvd (D := fun i => (x x₀ (c + A i) : ℤ) - x x₀ (a + A i))
    hA r hstep
  rw [hA0] at hdvd
  simp only [Nat.sub_zero, Nat.add_zero] at hdvd
  exact isRepetition_iff_dvd.mpr hdvd

/-- **The chain ceiling**: total shift `E` of a clustered same-gap chain obeys
`2^{E+c} < 3^c(x₀+1)` — the plan's `|D₁| ≤ K(3/2)^{c₁}` bound, via `RB.repetition_pow_lt`. -/
@[category research solved, AMS 11 68, ref "B2A2", group "rb_rational_base"]
theorem chain_pow_lt {x₀ a c : ℕ} (hx₀ : 0 < x₀) (hac : a < c) {A k : ℕ → ℕ}
    (hA : Monotone A) (hA0 : A 0 = 0) (r : ℕ)
    (hrep : ∀ i ≤ r, IsRepetition x₀ (a + A i) (c + A i) (k i))
    (hcl : ∀ i < r, (3 : ℝ) ^ (A (i + 1) - A i) * (2 / 3 : ℝ) ^ k i
      + 2 ^ (A (i + 1) - A i) * (2 / 3 : ℝ) ^ k (i + 1) < 1) :
    2 ^ (A r + c) < 3 ^ c * (x₀ + 1) :=
  repetition_pow_lt hx₀ hac (isRepetition_of_chain hx₀ hA hA0 r hrep hcl)

/-- **The certified chain cap** at `x₀ = 1`: `41·E ≤ 24c + 40`, i.e. `E ≤ 0.585·c + 1`.

This is [B2A2] §2.5's "the total 2-shift along any chain of clustered same-gap violators is
capped by `0.585 c₁`", with the same integer certificate `3^41 ≤ 2^65` (`RB.pow_cert`) that
carries the repetition ceiling — no reals, no logarithms. -/
@[category research solved, AMS 11 68, ref "B2A2" "Dub09", group "rb_rational_base"]
theorem chain_linear_bound {a c : ℕ} (hac : a < c) {A k : ℕ → ℕ}
    (hA : Monotone A) (hA0 : A 0 = 0) (r : ℕ)
    (hrep : ∀ i ≤ r, IsRepetition 1 (a + A i) (c + A i) (k i))
    (hcl : ∀ i < r, (3 : ℝ) ^ (A (i + 1) - A i) * (2 / 3 : ℝ) ^ k i
      + 2 ^ (A (i + 1) - A i) * (2 / 3 : ℝ) ^ k (i + 1) < 1) :
    41 * A r ≤ 24 * c + 40 :=
  repetition_linear_bound hac (isRepetition_of_chain (by norm_num) hA hA0 r hrep hcl)

private lemma le_of_strictMono_zero {A : ℕ → ℕ} (hA : StrictMono A) (hA0 : A 0 = 0) :
    ∀ r, r ≤ A r := by
  intro r
  induction r with
  | zero => omega
  | succ r ih =>
    have h : A r < A (r + 1) := hA (by omega)
    omega

/-- **The per-octave count for the orbit**: a chain of `r + 1` *distinct* clustered same-gap
repetitions based at `(a, c)` has `41·r ≤ 24c + 40`, i.e. at most `0.585·c + 2` members.

The clustered same-gap families [B2A2] §2.5 proposes to count are therefore **thin** — linear
in the position, not exponential.  (WP6(i)'s numerics suggest they are in fact empty in the
observable range; this is the counterfactual cap.) -/
@[category research solved, AMS 11 68, ref "B2A2" "Dub09", group "rb_rational_base"]
theorem chain_length_linear_bound {a c : ℕ} (hac : a < c) {A k : ℕ → ℕ}
    (hA : StrictMono A) (hA0 : A 0 = 0) (r : ℕ)
    (hrep : ∀ i ≤ r, IsRepetition 1 (a + A i) (c + A i) (k i))
    (hcl : ∀ i < r, (3 : ℝ) ^ (A (i + 1) - A i) * (2 / 3 : ℝ) ^ k i
      + 2 ^ (A (i + 1) - A i) * (2 / 3 : ℝ) ^ k (i + 1) < 1) :
    41 * r ≤ 24 * c + 40 := by
  have h1 := chain_linear_bound hac hA.monotone hA0 r hrep hcl
  have h2 := le_of_strictMono_zero hA hA0 r
  omega

/-! ## The `δ`-scaled violator instance -/

/-- **Clustering, in violator vocabulary** ([B2A2] §2.5): `3^e·θ^c < 1/2`.  With
`θ = (2/3)^{δ₀}` this is the plan's `Δa ≲ 0.37·δ₀c₁`. -/
@[category API, AMS 11, ref "B2A2", group "rb_rational_base"]
def IsClustered (θ : ℚ) (c e : ℕ) : Prop := (3 : ℚ) ^ e * θ ^ c < 1 / 2

private lemma chainVal_ratCast (δ : ℚ) (a c : ℕ) :
    chainVal (δ : ℝ) a c = ((δ * ((3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a) : ℚ) : ℝ) := by
  unfold chainVal
  push_cast
  ring

private lemma abs_chainVal_sub_round_le {δ θ : ℚ} {a c : ℕ}
    (h : (a, c) ∈ scaledViolators δ θ) :
    |chainVal (δ : ℝ) a c
        - ((round (δ * ((3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a)) : ℤ) : ℝ)| ≤ (θ : ℝ) ^ c := by
  obtain ⟨-, -, hd⟩ := h
  rw [Rat.distToNearestInt] at hd
  have hcast : ((|δ * ((3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a)
      - (round (δ * ((3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a)) : ℚ)| : ℚ) : ℝ)
      ≤ ((θ ^ c : ℚ) : ℝ) := by exact_mod_cast hd
  rw [chainVal_ratCast]
  push_cast at hcast ⊢
  exact hcast

/-- **The exact relation for `δ`-scaled violators** ([B2A2] §2.5, formalized on the plan's own
violator set `RB.scaledViolators`): a clustered pair of same-gap violators has

  `2^e·D₂ = 3^e·D₁`,   `Dᵢ` the nearest integers.

The clustering hypothesis is the plan's single inequality `3^e θ^c < 1/2`; the second error
term is absorbed because `2^e θ^{c+e} = (2θ)^e θ^c ≤ 3^e θ^c` for `θ < 1`. -/
@[category research solved, AMS 11, ref "B2A2", group "rb_rational_base"]
theorem exact_relation_of_violators {δ θ : ℚ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {a c e : ℕ}
    (h₁ : (a, c) ∈ scaledViolators δ θ)
    (h₂ : (a + e, c + e) ∈ scaledViolators δ θ)
    (hcl : IsClustered θ c e) :
    (2 : ℤ) ^ e * round (δ * ((3 / 2 : ℚ) ^ (c + e) - (3 / 2 : ℚ) ^ (a + e)))
      = 3 ^ e * round (δ * ((3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a)) := by
  have hθ0' : (0 : ℝ) < (θ : ℝ) := by exact_mod_cast hθ0
  have hθ1' : (θ : ℝ) < 1 := by exact_mod_cast hθ1
  have hclq : (3 : ℚ) ^ e * θ ^ c < 1 / 2 := hcl
  have hcl' : (3 : ℝ) ^ e * (θ : ℝ) ^ c < 1 / 2 := by
    have h : (((3 : ℚ) ^ e * θ ^ c : ℚ) : ℝ) < ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast hclq
    push_cast at h
    exact h
  have hkey : (2 : ℝ) ^ e * (θ : ℝ) ^ (c + e) ≤ 3 ^ e * (θ : ℝ) ^ c := by
    rw [pow_add]
    calc (2 : ℝ) ^ e * ((θ : ℝ) ^ c * (θ : ℝ) ^ e)
        = (2 * (θ : ℝ)) ^ e * (θ : ℝ) ^ c := by rw [mul_pow]; ring
      _ ≤ 3 ^ e * (θ : ℝ) ^ c := by
          have h1 : (2 * (θ : ℝ)) ^ e ≤ 3 ^ e := by gcongr; linarith
          exact mul_le_mul_of_nonneg_right h1 (by positivity)
  refine exact_relation (η₁ := (θ : ℝ) ^ c) (η₂ := (θ : ℝ) ^ (c + e))
    (abs_chainVal_sub_round_le h₁) ?_ (by linarith)
  exact abs_chainVal_sub_round_le h₂

/-- A base violator whose value exceeds `1` in absolute value has a nonzero nearest integer —
the side condition of the counting bound.  For the orbit it is automatic (`x_c > x_a`). -/
@[category API, AMS 11, ref "B2A2", group "rb_rational_base"]
theorem round_ne_zero_of_one_le_abs {v : ℚ} (h : 1 ≤ |v|) : round v ≠ 0 := by
  intro h0
  have hr := abs_sub_round v
  rw [h0] at hr
  simp only [Int.cast_zero, sub_zero] at hr
  linarith

/-- **The per-base same-gap violator bound** (the plan's "per-octave" deliverable), on
`RB.scaledViolators`: the shifts that keep a base violator a violator *and* stay clustered
against it form a finite set of size at most `log₂|D₁| + 1`. -/
@[category research solved, AMS 11, ref "B2A2" "Dub09", group "rb_rational_base"]
theorem clusteredShifts_ncard_le {δ θ : ℚ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {a c : ℕ}
    (h₀ : (a, c) ∈ scaledViolators δ θ)
    (hD : round (δ * ((3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a)) ≠ 0) :
    {e : ℕ | (a + e, c + e) ∈ scaledViolators δ θ ∧ IsClustered θ c e}.ncard
      ≤ Nat.log 2 (round (δ * ((3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a))).natAbs + 1 := by
  refine ncard_le_of_two_pow_dvd hD ?_
  rintro e ⟨hv, hc⟩
  exact two_pow_dvd_of_exact_relation (exact_relation_of_violators hθ0 hθ1 h₀ hv hc)

/-- Finiteness form of the same bound. -/
@[category research solved, AMS 11, ref "B2A2", group "rb_rational_base"]
theorem clusteredShifts_finite {δ θ : ℚ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {a c : ℕ}
    (h₀ : (a, c) ∈ scaledViolators δ θ)
    (hD : round (δ * ((3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a)) ≠ 0) :
    {e : ℕ | (a + e, c + e) ∈ scaledViolators δ θ ∧ IsClustered θ c e}.Finite := by
  refine finite_of_two_pow_dvd hD ?_
  rintro e ⟨hv, hc⟩
  exact two_pow_dvd_of_exact_relation (exact_relation_of_violators hθ0 hθ1 h₀ hv hc)

end RB
