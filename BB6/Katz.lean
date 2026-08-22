/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB6.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Katz's construction under the ratio-floor reading

[Kat16, Cor. 4.9] produces a universally densifying set of the shape
`A = {2ⁿ3ᵉ : n ∈ ℕ, e ∈ E}` with `E = {T(p₁ m) + T(p₂ k) : m, k ∈ ℕ}`, where `p₁, p₂` are
non-constant polynomials and `T` is a tower of threes.  The ported file
`DistributionModOne/Problem10_6.lean` hard-codes one instance of this, which is a fidelity
problem, since [Kat16] prints the tower with dots and the height comes out of the `p`-adic
substitution lemma of its §4.6–4.8.  This file therefore builds the family in general
(`BB6.threeTower`, `BB6.katzExponents`, `BB6.twoThreeSet`) and identifies the hard-coded set
inside it, so that nothing downstream depends on a height we cannot source.

That identification also corrects a misreading.  The ported set is written
`{2ⁿ · 3^(3^(3^m)) · 3^(3^(3^k))}`, whose three visible threes look like a height-three tower;
but the outermost one is the `3ᵉ` of the multiplicative set `A`, so the *exponent* tower has
height **two**: the port is `h = 2`, `p₁ = p₂ = id` (`BB6.twoThreeSet_katzExponents`).  Nothing
depends on this — it is exactly the ambiguity the parametrization exists to absorb — but a note
that named the height would have named the wrong one.

The mathematical content is **Theorem F**.  Two elements `2ⁿ3ᵉ < 2ⁿ'3ᵉ'` of `A` have log-ratio
`log 2 · ((n'-n) + (e'-e)θ)` with `θ = log₂3`, and that number is at least `log 2 · ‖(e'-e)θ‖`
where `‖·‖` is the distance to the nearest integer — the integer part `n'-n` is absorbed by
`round_le` and never has to be looked at.  So a Diophantine floor on `E - E` is exactly what
converts into a ratio floor on the increasing enumeration of `A`:

> **Theorem F.**  If `‖(e-e')θ‖ ≥ c / log max(e,e')` for all distinct `e, e' ∈ E`, then the
> increasing enumeration of `A` is R3-regular.

The index bookkeeping that turns `c / log max(e,e')` into `c' / log j` is one inequality: `A`
contains the geometric progression `2ⁿ3ᵉ⁰`, so its `j`-th element is at most `2ʲ3ᵉ⁰`, whence
`max(e,e') ≤ j + 1 + e₀` — a *lower* bound on the counting function, elementary, and in particular
[Kat16, Cor. 4.10] is **not** needed.  `BB6.theorem_F` is `std3`.

Applied to the hard-coded instance this gives a conditional resolution of the ratio-floor variant
`Bugeaud06.problem_10_6_variant_1`, which is recorded there with a `sorry`: the hypothesis of
Theorem F for Katz's own exponent set implies it, drawing only `Bugeaud06.katz_universal_density`
(`BB6.problem_10_6_variant_1_of_gap`).

## What the hypothesis costs

`BB6.exists_nearInt_lt_of_infinite` is the pigeonhole remark that replaces the withdrawn
Theorem E: for *every* infinite `E ⊆ ℕ` and *every* real `θ` the differences `E - E` come
arbitrarily close to the integers.  Irrationality of `θ` is not used, and neither is [Kat16] nor
[Pol79]/[Mat80]; the fact is recorded as trivial in [Kat01, §2.3].  Its consequence
(`BB6.not_const_gap_of_infinite`) is that the hypothesis of Theorem F cannot be strengthened to a
*constant* floor — the decay in `c / log max(e,e')` is not slack.  In the other direction the best
unconditional bound available is `‖dθ‖ ≥ 1.43·10⁻⁴ d^(-13.3)` ([Rhi87], `CITED/RhinLogForm.lean`),
so the hypothesis is out of reach of current transcendence methods.

## Contents

* `BB6.nearInt` — distance to the nearest integer, and `BB6.nearInt_le`;
* `BB6.threeTower`, `BB6.katzExponents`, `BB6.twoThreeSet`, `BB6.twoThreeSeq` — the family;
* `BB6.twoThreeSeq_le` — the `2ʲ3ᵉ⁰` ceiling on the enumeration;
* `BB6.twoThree_ratio_eq_exp`, `BB6.one_add_mul_le_ratio` — the ratio estimate, `round_le` doing the work;
* `BB6.theorem_F` — Theorem F, and `BB6.theorem_F_singleton` for its non-vacuity;
* `BB6.exists_nearInt_lt_of_infinite`, `BB6.not_const_gap_of_infinite` — the pigeonhole remark;
* `BB6.twoThreeSet_katzExponents`, `BB6.twoThreeSeq_katzExponents` — fidelity of the port;
* `BB6.problem_10_6_variant_1_of_gap` — the conditional resolution of the R3 variant.

*References:*
  - [Bug12] Bugeaud, Y. *Distribution modulo one and Diophantine approximation*, CUP 2012, Ch. 10.
  - [Kat01] Katznelson, Y. "Chromatic numbers of Cayley graphs on ℤ and recurrence."
    Combinatorica 21 (2001), §2.3.
  - [Kat16] Katz, A. "Generalizations of Furstenberg's Diophantine result." arXiv:1607.00670,
    Cor. 4.9 and Cor. 4.10.
  - [Rhi87] Rhin, G. "Approximants de Padé et mesures effectives d'irrationalité."
    Progr. Math. 71 (1987).
-/

namespace BB6

open Filter

/-! ## Distance to the nearest integer -/

/-- `nearInt x = ‖x‖` in the usual Diophantine sense: the distance from `x` to the nearest
integer.  Stated as `|x - round x|` rather than through `AddCircle` so that Mathlib's `round_le`
applies directly. -/
@[category API, AMS 11, group "bugeaud_10_6"]
noncomputable def nearInt (x : ℝ) : ℝ := |x - round x|

/-- The defining property: `‖x‖` is at most the distance from `x` to *any* integer.  This is the
one fact about `nearInt` the ratio estimate needs, and it is what lets the integer part of a
log-ratio be discarded without a case split. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem nearInt_le (x : ℝ) (z : ℤ) : nearInt x ≤ |x - (z : ℝ)| := round_le x z

/-- `‖x‖ ≥ 0`. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem nearInt_nonneg (x : ℝ) : 0 ≤ nearInt x := abs_nonneg _

/-! ## The generalized Katz family -/

/-- `threeTower h x` is the tower `3^3^⋯^x` of height `h`.  [Kat16, Cor. 4.9] prints the tower
with dots; the height is left as a parameter here rather than asserted. -/
@[category API, AMS 11, ref "Kat16", group "bugeaud_10_6"]
def threeTower : ℕ → ℕ → ℕ
  | 0, x => x
  | h + 1, x => 3 ^ threeTower h x

@[category API, AMS 11, group "bugeaud_10_6"]
theorem threeTower_zero (x : ℕ) : threeTower 0 x = x := rfl

@[category API, AMS 11, group "bugeaud_10_6"]
theorem threeTower_succ (h x : ℕ) : threeTower (h + 1) x = 3 ^ threeTower h x := rfl

/-- Towers of positive height are at least `1`. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem one_le_threeTower {h : ℕ} (hh : 1 ≤ h) (x : ℕ) : 1 ≤ threeTower h x := by
  obtain ⟨h, rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
  exact Nat.one_le_pow _ _ (by norm_num)

@[category API, AMS 11, group "bugeaud_10_6"]
theorem threeTower_strictMono (h : ℕ) : StrictMono (threeTower h) := by
  induction h with
  | zero => exact strictMono_id
  | succ h ih => exact fun a b hab => Nat.pow_lt_pow_right (by norm_num) (ih hab)

/-- Katz's exponent set `E = {T(p₁ m) + T(p₂ k)}` [Kat16, Cor. 4.9], with the tower height `h`
and the two polynomials left as parameters. -/
@[category API, AMS 11, ref "Kat16", group "bugeaud_10_6"]
def katzExponents (h : ℕ) (p₁ p₂ : ℕ → ℕ) : Set ℕ :=
  {e | ∃ m k : ℕ, e = threeTower h (p₁ m) + threeTower h (p₂ k)}

@[category API, AMS 11, group "bugeaud_10_6"]
theorem katzExponents_nonempty (h : ℕ) (p₁ p₂ : ℕ → ℕ) : (katzExponents h p₁ p₂).Nonempty :=
  ⟨_, 0, 0, rfl⟩

/-- Every exponent is at least `2` as soon as the tower has positive height, being a sum of two
towers.  This is the mild non-degeneracy Theorem F asks for: it rules out the pair `{0,1}`, on
which a bound of the form `c / log max(e,e')` says nothing because `log 1 = 0`. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem two_le_of_mem_katzExponents {h : ℕ} (hh : 1 ≤ h) {p₁ p₂ : ℕ → ℕ} {e : ℕ}
    (he : e ∈ katzExponents h p₁ p₂) : 2 ≤ e := by
  obtain ⟨m, k, rfl⟩ := he
  have := one_le_threeTower hh (p₁ m)
  have := one_le_threeTower hh (p₂ k)
  omega

/-- The exponent set is infinite as soon as one of the polynomials is unbounded — the
"non-constant" hypothesis of [Kat16, Cor. 4.9], in the form the pigeonhole remark needs. -/
@[category API, AMS 11, ref "Kat16", group "bugeaud_10_6"]
theorem katzExponents_infinite (h : ℕ) {p₁ : ℕ → ℕ} (hp : StrictMono p₁) (p₂ : ℕ → ℕ) :
    (katzExponents h p₁ p₂).Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun m : ℕ => threeTower h (p₁ m) + threeTower h (p₂ 0)) ?_ ?_
  · intro a b hab
    have hab' : threeTower h (p₁ a) + threeTower h (p₂ 0)
        = threeTower h (p₁ b) + threeTower h (p₂ 0) := hab
    exact hp.injective ((threeTower_strictMono h).injective (by omega))
  · exact fun m => ⟨m, 0, rfl⟩

/-- `A = {2ⁿ3ᵉ : n ∈ ℕ, e ∈ E}`, the multiplicative set of [Kat16, Cor. 4.9]. -/
@[category API, AMS 11, ref "Kat16", group "bugeaud_10_6"]
def twoThreeSet (E : Set ℕ) : Set ℕ := {N | ∃ n e : ℕ, e ∈ E ∧ N = 2 ^ n * 3 ^ e}

@[category API, AMS 11, group "bugeaud_10_6"]
theorem twoThreeSet_infinite {E : Set ℕ} (hE : E.Nonempty) : (twoThreeSet E).Infinite := by
  obtain ⟨e₀, he₀⟩ := hE
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => 2 ^ n * 3 ^ e₀) ?_ ?_
  · intro a b hab
    exact Nat.pow_right_injective (by norm_num)
      (Nat.eq_of_mul_eq_mul_right (by positivity) hab)
  · exact fun n => ⟨n, e₀, he₀, rfl⟩

/-- The increasing enumeration of `A`. -/
@[category API, AMS 11, ref "Kat16", group "bugeaud_10_6"]
noncomputable def twoThreeSeq (E : Set ℕ) : ℕ → ℕ := Nat.nth (· ∈ twoThreeSet E)

@[category API, AMS 11, group "bugeaud_10_6"]
theorem twoThreeSeq_mem {E : Set ℕ} (hE : E.Nonempty) (j : ℕ) : twoThreeSeq E j ∈ twoThreeSet E :=
  Nat.nth_mem_of_infinite (by simpa using twoThreeSet_infinite hE) j

@[category API, AMS 11, group "bugeaud_10_6"]
theorem twoThreeSeq_strictMono {E : Set ℕ} (hE : E.Nonempty) : StrictMono (twoThreeSeq E) :=
  Nat.nth_strictMono (by simpa using twoThreeSet_infinite hE)

/-- **The ceiling on the enumeration.**  `A` contains the geometric progression `2ⁿ3ᵉ⁰` for any
fixed `e₀ ∈ E`, and `Nat.nth` is the least strictly monotone enumeration, so the `j`-th element of
`A` is at most `2ʲ3ᵉ⁰`.  This is the only counting input Theorem F needs, and it is a *lower*
bound on `π_A` — the sparsity theorem [Kat16, Cor. 4.10] plays no part. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem twoThreeSeq_le {E : Set ℕ} {e₀ : ℕ} (he₀ : e₀ ∈ E) (j : ℕ) :
    twoThreeSeq E j ≤ 2 ^ j * 3 ^ e₀ := by
  refine Nat.nth_le_of_strictMonoOn_of_mapsTo (fun i : ℕ => 2 ^ i * 3 ^ e₀) ?_ ?_
  · exact fun i _ => ⟨i, e₀, he₀, rfl⟩
  · exact fun a _ b _ hab =>
      mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right (by norm_num) hab) (by positivity)

/-! ## The ratio of two elements of `A` -/

/-- The log-gap between two elements of `A`, in the coordinates that matter: `log 2` times an
integer plus `(e'-e)` times `θ = log₂3`. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem log_sub_log_two_three (n n' e e' : ℕ) :
    Real.log ((2 ^ n' * 3 ^ e' : ℕ) : ℝ) - Real.log ((2 ^ n * 3 ^ e : ℕ) : ℝ)
      = Real.log 2 * (((n' : ℝ) - n) + ((e' : ℝ) - e) * Real.logb 2 3) := by
  have hl2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hθ : Real.logb 2 3 * Real.log 2 = Real.log 3 := by
    rw [Real.logb]; field_simp
  have e1 : Real.log ((2 ^ n * 3 ^ e : ℕ) : ℝ) = n * Real.log 2 + e * Real.log 3 := by
    push_cast
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  have e2 : Real.log ((2 ^ n' * 3 ^ e' : ℕ) : ℝ) = n' * Real.log 2 + e' * Real.log 3 := by
    push_cast
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  rw [e1, e2, ← hθ]; ring

/-- The ratio of two elements of `A`, as an exponential of the log₂-gap.  Both the lower bound
Theorem F needs and the upper bound Theorem G needs (`BB6/FurstenbergGaps.lean`) go through this
one identity. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem twoThree_ratio_eq_exp (n n' e e' : ℕ) :
    ((2 ^ n' * 3 ^ e' : ℕ) : ℝ) / ((2 ^ n * 3 ^ e : ℕ) : ℝ)
      = Real.exp (Real.log 2 * (((n' : ℝ) - n) + ((e' : ℝ) - e) * Real.logb 2 3)) := by
  have haN : (0 : ℕ) < 2 ^ n * 3 ^ e := by positivity
  have hbN : (0 : ℕ) < 2 ^ n' * 3 ^ e' := by positivity
  have ha0 : (0 : ℝ) < ((2 ^ n * 3 ^ e : ℕ) : ℝ) := by exact_mod_cast haN
  have hb0 : (0 : ℝ) < ((2 ^ n' * 3 ^ e' : ℕ) : ℝ) := by exact_mod_cast hbN
  rw [← log_sub_log_two_three n n' e e', Real.exp_sub, Real.exp_log hb0, Real.exp_log ha0]

/-- The log-gap of an increasing pair is positive. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem logGap_pos {n n' e e' : ℕ} (h : (2 : ℕ) ^ n * 3 ^ e < 2 ^ n' * 3 ^ e') :
    0 < ((n' : ℝ) - n) + ((e' : ℝ) - e) * Real.logb 2 3 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hposN : (0 : ℕ) < 2 ^ n * 3 ^ e := by positivity
  have hpos : (0 : ℝ) < ((2 ^ n * 3 ^ e : ℕ) : ℝ) := by exact_mod_cast hposN
  have hlt : Real.log ((2 ^ n * 3 ^ e : ℕ) : ℝ) < Real.log ((2 ^ n' * 3 ^ e' : ℕ) : ℝ) :=
    Real.log_lt_log hpos (by exact_mod_cast h)
  have hid := log_sub_log_two_three n n' e e'
  by_contra hcon
  push Not at hcon
  nlinarith

/-- **The ratio estimate.**  If `D` is any lower bound for the log₂-gap of an increasing pair of
elements of `A`, then the ratio of the two elements is at least `1 + D log 2`.  Only `exp x ≥ 1+x`
is used, so the estimate is lossless where it matters (`D` small). -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem one_add_mul_le_ratio {n n' e e' : ℕ}
    {D : ℝ} (hD : D ≤ ((n' : ℝ) - n) + ((e' : ℝ) - e) * Real.logb 2 3) :
    1 + Real.log 2 * D ≤ ((2 ^ n' * 3 ^ e' : ℕ) : ℝ) / ((2 ^ n * 3 ^ e : ℕ) : ℝ) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [twoThree_ratio_eq_exp n n' e e']
  have hmul := mul_le_mul_of_nonneg_left hD hlog2.le
  linarith [Real.add_one_le_exp
    (Real.log 2 * (((n' : ℝ) - n) + ((e' : ℝ) - e) * Real.logb 2 3))]

/-- The log₂-gap of an increasing pair dominates `‖(e'-e)θ‖`: the integer part `n'-n` is absorbed
by `round_le`, which is why no case analysis on the sign or the size of `n'-n` is needed. -/
@[category API, AMS 11, group "bugeaud_10_6"]
theorem nearInt_le_logGap {n n' e e' : ℕ} (h : (2 : ℕ) ^ n * 3 ^ e < 2 ^ n' * 3 ^ e') :
    nearInt (((e' : ℝ) - e) * Real.logb 2 3)
      ≤ ((n' : ℝ) - n) + ((e' : ℝ) - e) * Real.logb 2 3 := by
  have hpos := logGap_pos h
  have hz := nearInt_le (((e' : ℝ) - e) * Real.logb 2 3) ((n : ℤ) - (n' : ℤ))
  have heq : |((e' : ℝ) - e) * Real.logb 2 3 - (((n : ℤ) - (n' : ℤ) : ℤ) : ℝ)|
      = ((n' : ℝ) - n) + ((e' : ℝ) - e) * Real.logb 2 3 := by
    rw [show ((e' : ℝ) - e) * Real.logb 2 3 - (((n : ℤ) - (n' : ℤ) : ℤ) : ℝ)
        = ((n' : ℝ) - n) + ((e' : ℝ) - e) * Real.logb 2 3 by push_cast; ring,
      abs_of_pos hpos]
  linarith [hz, heq.le, heq.ge]

/-! ## Theorem F -/

/-- **Theorem F (conditional resolution of R3).**  Let `E ⊆ ℕ` consist of integers `≥ 2`, let
`e₀ ∈ E`, and suppose the differences of `E` obey the Diophantine floor
`‖(e-e')θ‖ ≥ c / log max(e,e')`, `θ = log₂3`.  Then the increasing enumeration of
`A = {2ⁿ3ᵉ : e ∈ E}` is R3-regular, i.e. genuinely sublacunary in Bugeaud's sense.

Three ingredients, each one line of mathematics: the log-ratio of consecutive elements is
`log 2 · ((n'-n) + (e'-e)θ) ≥ log 2 · ‖(e'-e)θ‖` (`BB6.nearInt_le_logGap`); the exponents met at
index `j` satisfy `e ≤ j + 1 + e₀` because `A ⊇ {2ⁿ3ᵉ⁰}` forces `a_j ≤ 2ʲ3ᵉ⁰`
(`BB6.twoThreeSeq_le`); and `log(j+1+e₀) ≤ 2 log j` eventually.  The resulting constant is
`c log 2 / 2`.

This statement is `std3`: it uses no property of Katz's particular `E`, and in particular not
[Kat16] itself. -/
@[category research solved, AMS 11, ref "Bug12" "Kat16", group "bugeaud_10_6",
  formal_uses nearInt_le_logGap one_add_mul_le_ratio twoThreeSeq_le]
theorem theorem_F {E : Set ℕ} {e₀ : ℕ} (he₀ : e₀ ∈ E) (hE2 : ∀ e ∈ E, 2 ≤ e) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ e ∈ E, ∀ e' ∈ E, e ≠ e' →
      c / Real.log ((max e e' : ℕ) : ℝ) ≤ nearInt (((e : ℝ) - e') * Real.logb 2 3)) :
    Bugeaud06.IsGenuinelySublacunary (twoThreeSeq E) := by
  have hE : E.Nonempty := ⟨e₀, he₀⟩
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨c * Real.log 2 / 2, by positivity, ?_⟩
  have hclog : ∀ᶠ j : ℕ in atTop, c / 2 ≤ Real.log j :=
    tendsto_log_natCast.eventually_ge_atTop (c / 2)
  filter_upwards [Filter.eventually_ge_atTop (e₀ + 2), hclog] with j hj hjc
  -- the index is large: `j ≥ 2`, `j + 1 + e₀ ≤ j²`, and `log j > 0`
  have hj2 : 2 ≤ j := by omega
  have hjR : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj2
  have hlogj : (0 : ℝ) < Real.log j := Real.log_pos (by linarith)
  have hsq : j + 1 + e₀ ≤ j ^ 2 := by nlinarith
  have hlogsq : Real.log ((j + 1 + e₀ : ℕ) : ℝ) ≤ 2 * Real.log j := by
    have h1 : ((j + 1 + e₀ : ℕ) : ℝ) ≤ ((j : ℝ)) ^ 2 := by exact_mod_cast hsq
    calc Real.log ((j + 1 + e₀ : ℕ) : ℝ)
        ≤ Real.log (((j : ℝ)) ^ 2) := Real.log_le_log (by positivity) h1
      _ = 2 * Real.log j := by rw [Real.log_pow]; push_cast; ring
  -- the two elements
  obtain ⟨n, e, heE, hne⟩ := twoThreeSeq_mem hE j
  obtain ⟨n', e', he'E, hne'⟩ := twoThreeSeq_mem hE (j + 1)
  have hlt : twoThreeSeq E j < twoThreeSeq E (j + 1) :=
    twoThreeSeq_strictMono hE (Nat.lt_succ_self j)
  have hltN : (2 : ℕ) ^ n * 3 ^ e < 2 ^ n' * 3 ^ e' := by rw [← hne, ← hne']; exact hlt
  rw [hne, hne']
  -- the exponents are bounded by `j + 1 + e₀`
  have hceil : twoThreeSeq E (j + 1) ≤ 3 ^ (j + 1 + e₀) := by
    calc twoThreeSeq E (j + 1) ≤ 2 ^ (j + 1) * 3 ^ e₀ := twoThreeSeq_le he₀ (j + 1)
      _ ≤ 3 ^ (j + 1) * 3 ^ e₀ := by
          exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by norm_num) _)
      _ = 3 ^ (j + 1 + e₀) := (pow_add 3 (j + 1) e₀).symm
  have hpow : ∀ f : ℕ, twoThreeSeq E (j + 1) = 2 ^ n' * 3 ^ e' → 3 ^ f ≤ 3 ^ (j + 1 + e₀) →
      f ≤ j + 1 + e₀ := fun f _ hf => (Nat.pow_le_pow_iff_right (by norm_num)).1 hf
  have hebound : e ≤ j + 1 + e₀ := by
    refine hpow e hne' (le_trans (le_trans ?_ hlt.le) hceil)
    rw [hne]; exact Nat.le_mul_of_pos_left _ (by positivity)
  have he'bound : e' ≤ j + 1 + e₀ := by
    refine hpow e' hne' (le_trans ?_ hceil)
    rw [hne']; exact Nat.le_mul_of_pos_left _ (by positivity)
  -- the two cases
  by_cases hee : e = e'
  · -- equal exponents: the ratio is a power of two, hence at least `1 + log 2`
    have hD : (1 : ℝ) ≤ ((n' : ℝ) - n) + ((e' : ℝ) - e) * Real.logb 2 3 := by
      have hgapPos := logGap_pos hltN
      rw [hee] at hgapPos ⊢
      simp only [sub_self, zero_mul, add_zero] at hgapPos ⊢
      have hnn : (n : ℝ) < (n' : ℝ) := by linarith
      have hnn' : n < n' := by exact_mod_cast hnn
      have : (n : ℝ) + 1 ≤ (n' : ℝ) := by exact_mod_cast hnn'
      linarith
    have hmain := one_add_mul_le_ratio hD
    have hsmall : c * Real.log 2 / 2 / Real.log j ≤ Real.log 2 * 1 := by
      rw [div_le_iff₀ hlogj]
      nlinarith
    linarith
  · -- distinct exponents: the Diophantine floor
    have hmaxle : (max e' e : ℕ) ≤ j + 1 + e₀ := max_le he'bound hebound
    have hmax2 : 2 ≤ (max e' e : ℕ) := le_trans (hE2 e' he'E) (le_max_left _ _)
    have hmaxlogpos : (0 : ℝ) < Real.log ((max e' e : ℕ) : ℝ) := by
      refine Real.log_pos ?_
      have : (2 : ℝ) ≤ ((max e' e : ℕ) : ℝ) := by exact_mod_cast hmax2
      linarith
    have hmaxlog : Real.log ((max e' e : ℕ) : ℝ) ≤ 2 * Real.log j :=
      le_trans (Real.log_le_log (by positivity) (by exact_mod_cast hmaxle)) hlogsq
    have hfloor := hgap e' he'E e heE (fun hc' => hee hc'.symm)
    have hdiv : c / (2 * Real.log j) ≤ c / Real.log ((max e' e : ℕ) : ℝ) :=
      div_le_div_of_nonneg_left hc.le hmaxlogpos hmaxlog
    have hD : c / (2 * Real.log j) ≤ ((n' : ℝ) - n) + ((e' : ℝ) - e) * Real.logb 2 3 :=
      le_trans (le_trans hdiv hfloor) (nearInt_le_logGap hltN)
    have hmain := one_add_mul_le_ratio hD
    have hrw : c * Real.log 2 / 2 / Real.log j = Real.log 2 * (c / (2 * Real.log j)) := by
      field_simp
    rw [hrw]
    exact hmain

/-- Theorem F is not vacuous: a one-element exponent set has no distinct pairs, so its
hypothesis holds outright, and the conclusion is the true statement that `{2ⁿ·9}` has ratio `2`.
This checks the *shape* only.  Whether an **infinite** `E` can satisfy the `c/log max(e,e')`
floor is not settled here — a greedy or Borel–Cantelli construction makes it overwhelmingly
plausible, and `BB6.not_const_gap_of_infinite` shows the decay cannot be removed. -/
@[category test, AMS 11, group "bugeaud_10_6"]
theorem theorem_F_singleton : Bugeaud06.IsGenuinelySublacunary (twoThreeSeq {2}) :=
  theorem_F (E := {2}) rfl (fun _ he => le_of_eq he.symm) one_pos
    (fun _ he _ he' hne => absurd (he.trans he'.symm) hne)

/-! ## The pigeonhole remark (what replaces the withdrawn Theorem E) -/

/-- **Pigeonhole.**  For every infinite `E ⊆ ℕ`, every real `θ` and every `ε > 0` there are
distinct `e, e' ∈ E` with `‖(e-e')θ‖ < ε`.  Dirichlet's box principle on the `N+1` fractional
parts `{eθ}`, nothing more; irrationality of `θ` is not used, nor is any property of `E` beyond
being infinite.  Recorded as trivial in [Kat01, §2.3]. -/
@[category research solved, AMS 11, ref "Kat01", group "bugeaud_10_6"]
theorem exists_nearInt_lt_of_infinite {E : Set ℕ} (hE : E.Infinite) (θ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ e ∈ E, ∃ e' ∈ E, e ≠ e' ∧ nearInt (((e : ℝ) - e') * θ) < ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  have hNR : (0 : ℝ) < (N : ℝ) := lt_trans (by positivity) hN
  have hNε : 1 / (N : ℝ) < ε := by
    rw [div_lt_iff₀ hε] at hN
    rw [div_lt_iff₀ hNR]
    linarith
  -- the enumeration of `E`
  have hE' : (Set.ofPred (· ∈ E)).Infinite := hE
  set g : ℕ → ℕ := Nat.nth (· ∈ E) with hg
  have hginj : Function.Injective g := Nat.nth_injective hE'
  have hgmem : ∀ i, g i ∈ E := Nat.nth_mem_of_infinite hE'
  -- the boxes
  set f : ℕ → ℕ := fun i => ⌊(N : ℝ) * Int.fract ((g i : ℝ) * θ)⌋₊ with hf
  have hmaps : ∀ i ∈ Finset.range (N + 1), f i ∈ Finset.range N := by
    intro i _
    refine Finset.mem_range.2 ((Nat.floor_lt ?_).2 ?_)
    · exact mul_nonneg hNR.le (Int.fract_nonneg _)
    · have hfr := Int.fract_lt_one ((g i : ℝ) * θ)
      nlinarith
  obtain ⟨i, _, j, _, hij, hfij⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (by simp) hmaps
  refine ⟨g i, hgmem i, g j, hgmem j, fun hcon => hij (hginj hcon), ?_⟩
  -- the two fractional parts are within `1/N`
  set a : ℝ := (g i : ℝ) * θ with ha
  set b : ℝ := (g j : ℝ) * θ with hb
  have hfa : (0 : ℝ) ≤ (N : ℝ) * Int.fract a := mul_nonneg hNR.le (Int.fract_nonneg _)
  have hfb : (0 : ℝ) ≤ (N : ℝ) * Int.fract b := mul_nonneg hNR.le (Int.fract_nonneg _)
  have h1 : ((f i : ℕ) : ℝ) ≤ (N : ℝ) * Int.fract a := Nat.floor_le hfa
  have h2 : ((f j : ℕ) : ℝ) ≤ (N : ℝ) * Int.fract b := Nat.floor_le hfb
  have h3 : (N : ℝ) * Int.fract a < ((f i : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have h4 : (N : ℝ) * Int.fract b < ((f j : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hfe : ((f i : ℕ) : ℝ) = ((f j : ℕ) : ℝ) := by exact_mod_cast hfij
  have hclose : |Int.fract a - Int.fract b| < 1 / (N : ℝ) := by
    rw [abs_lt]
    constructor
    · rw [neg_lt, ← sub_neg_eq_add, lt_div_iff₀ hNR] at *
      nlinarith
    · rw [lt_div_iff₀ hNR]
      nlinarith
  -- and `‖(gi - gj)θ‖` is at most that
  have hsplit : ((g i : ℝ) - (g j : ℝ)) * θ - (((⌊a⌋ - ⌊b⌋ : ℤ)) : ℝ)
      = Int.fract a - Int.fract b := by
    rw [Int.fract, Int.fract, ha, hb]
    push_cast
    ring
  have hle := nearInt_le (((g i : ℝ) - (g j : ℝ)) * θ) (⌊a⌋ - ⌊b⌋)
  rw [hsplit] at hle
  have : ((g i : ℝ) - ((g j : ℕ) : ℝ)) * θ = ((g i : ℝ) - (g j : ℝ)) * θ := rfl
  linarith [hle, hclose, hNε]

/-- **The hypothesis of Theorem F cannot be strengthened to a constant floor.**  This is the one
job the withdrawn Theorem E did, and it needs neither [Kat16] nor [Pol79]/[Mat80]. -/
@[category research solved, AMS 11, ref "Kat01" "Kat16", group "bugeaud_10_6",
  formal_uses exists_nearInt_lt_of_infinite]
theorem not_const_gap_of_infinite {E : Set ℕ} (hE : E.Infinite) (θ : ℝ) {c : ℝ} (hc : 0 < c) :
    ¬ ∀ e ∈ E, ∀ e' ∈ E, e ≠ e' → c ≤ nearInt (((e : ℝ) - e') * θ) := by
  intro h
  obtain ⟨e, he, e', he', hne, hlt⟩ := exists_nearInt_lt_of_infinite hE θ hc
  exact absurd (h e he e' he' hne) (not_le.2 hlt)

/-! ## Fidelity: the ported set is one instance of the family -/

/-- The hard-coded `Bugeaud06.katzSet` is the instance of [Kat16, Cor. 4.9] with tower height
**two** and identity polynomials: its exponents are `3 ^ 3 ^ m + 3 ^ 3 ^ k`, since the outermost
three of the ported `3 ^ (3 ^ (3 ^ m))` belongs to the `3 ^ e` of the multiplicative set, not to
the tower.  Nothing in this root asserts which height [Kat16] intends; the general family above
is what the mathematics runs on. -/
@[category API, AMS 11, ref "Kat16", group "bugeaud_10_6"]
theorem twoThreeSet_katzExponents : twoThreeSet (katzExponents 2 id id) = Bugeaud06.katzSet := by
  ext N
  constructor
  · rintro ⟨n, e, ⟨m, k, rfl⟩, rfl⟩
    exact ⟨n, m, k, by simp only [threeTower_succ, threeTower_zero, id_eq, pow_add, mul_assoc]⟩
  · rintro ⟨n, m, k, rfl⟩
    refine ⟨n, threeTower 2 (id m) + threeTower 2 (id k), ⟨m, k, rfl⟩, ?_⟩
    simp only [threeTower_succ, threeTower_zero, id_eq, pow_add, mul_assoc]

@[category API, AMS 11, ref "Kat16", group "bugeaud_10_6"]
theorem twoThreeSeq_katzExponents : twoThreeSeq (katzExponents 2 id id) = Bugeaud06.katzSeq := by
  rw [twoThreeSeq, Bugeaud06.katzSeq, twoThreeSet_katzExponents]

/-! ## The conditional resolution of the R3 variant -/

/-- The Diophantine hypothesis of Theorem F, at Katz's own exponent set. -/
@[category API, AMS 11, ref "Kat16", group "bugeaud_10_6"]
def KatzGapHypothesis : Prop :=
  ∃ c > 0, ∀ e ∈ katzExponents 2 id id, ∀ e' ∈ katzExponents 2 id id, e ≠ e' →
    c / Real.log ((max e e' : ℕ) : ℝ) ≤ nearInt (((e : ℝ) - e') * Real.logb 2 3)

/-- Under the gap hypothesis, Katz's sequence is R3-regular. -/
@[category research solved, AMS 11, ref "Bug12" "Kat16", group "bugeaud_10_6",
  formal_uses theorem_F twoThreeSeq_katzExponents]
theorem katzSeq_isGenuinelySublacunary_of_gap (h : KatzGapHypothesis) :
    Bugeaud06.IsGenuinelySublacunary Bugeaud06.katzSeq := by
  obtain ⟨c, hc, hgap⟩ := h
  have := theorem_F (E := katzExponents 2 id id) (e₀ := threeTower 2 (id 0) + threeTower 2 (id 0))
    ⟨0, 0, rfl⟩ (fun _ he => two_le_of_mem_katzExponents (by norm_num) he) hc hgap
  rwa [twoThreeSeq_katzExponents] at this

/-- **Theorem F for Problem 10.6, conditional form.**  The Diophantine gap hypothesis, together
with Katz's density theorem taken as a hypothesis rather than as an axiom, gives the ratio-floor
variant of Problem 10.6 — the variant recorded as open (with a `sorry`) in
`Bugeaud06.problem_10_6_variant_1`.  `std3`. -/
@[category research solved, AMS 11, ref "Bug12" "Kat16", group "bugeaud_10_6",
  formal_uses katzSeq_isGenuinelySublacunary_of_gap]
theorem problem_10_6_variant_1_of_gap_of (hKatz : type_of% Bugeaud06.katz_universal_density)
    (h : KatzGapHypothesis) :
    ∃ m : ℕ → ℕ, StrictMono m ∧ Bugeaud06.IsGenuinelySublacunary m ∧
      ∀ ξ : ℝ, Irrational ξ →
        Dense (Set.range fun n => (↑(ξ * m n) : AddCircle (1 : ℝ))) :=
  ⟨Bugeaud06.katzSeq, Bugeaud06.katzSeq_strictMono,
    katzSeq_isGenuinelySublacunary_of_gap h, hKatz⟩

/-- **Theorem F for Problem 10.6.**  Same statement, drawing the cited axiom
`Bugeaud06.katz_universal_density` [Kat16, Cor. 4.9].  Note that the sparsity half of [Kat16]
(Cor. 4.10, `Bugeaud06.katzSeq_intermediateGrowth` in the ported file) is *not* used: the ceiling
`a_j ≤ 2ʲ3ᵉ⁰` that Theorem F needs is elementary. -/
@[category research open, AMS 11, ref "Bug12" "Kat16", group "bugeaud_10_6",
  formal_uses Bugeaud06.katz_universal_density problem_10_6_variant_1_of_gap_of]
theorem problem_10_6_variant_1_of_gap (h : KatzGapHypothesis) :
    ∃ m : ℕ → ℕ, StrictMono m ∧ Bugeaud06.IsGenuinelySublacunary m ∧
      ∀ ξ : ℝ, Irrational ξ →
        Dense (Set.range fun n => (↑(ξ * m n) : AddCircle (1 : ℝ))) :=
  problem_10_6_variant_1_of_gap_of Bugeaud06.katz_universal_density h

/-- The gap hypothesis is not vacuous for a *constant* floor only by accident: Katz's exponent set
is infinite, so by the pigeonhole remark no constant floor can hold, and the `1/log` decay in
`KatzGapHypothesis` is essential. -/
@[category research solved, AMS 11, ref "Kat01" "Kat16", group "bugeaud_10_6",
  formal_uses not_const_gap_of_infinite katzExponents_infinite]
theorem not_const_gap_katzExponents {c : ℝ} (hc : 0 < c) :
    ¬ ∀ e ∈ katzExponents 2 id id, ∀ e' ∈ katzExponents 2 id id, e ≠ e' →
        c ≤ nearInt (((e : ℝ) - e') * Real.logb 2 3) :=
  not_const_gap_of_infinite (katzExponents_infinite 2 strictMono_id id) _ hc

end BB6
