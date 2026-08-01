/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Round
import Mathlib.Tactic
import ForMathlib.Data.Real.NearestInt
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Bugeaud Problem 10.13, elementary layer: failures, residues, towers (Bug12, DD90)

Milestone **M2 / deliverable D1** of `plans/plan-1013.html`: the *elementary* gap-principle
layer under Bugeaud's Problem 10.13 — bound the number of `n` with `‖(3/2)ⁿ‖ < (3/4)ⁿ`.  This
file fixes the objects; `BB13.GapPrinciple` proves the §3 gap identity and linkage lemma, and
`BB13.TowerCount` proves the `O(log N)` tower count (T4).  Everything is stated for a general
rational base `p/q > 1` and rate `0 < c < 1` (the plan's general `(p/q, c)`); the headline case
is `(p, q, c) = (3, 2, 3/4)`.

The whole layer is *pure integer arithmetic + orders of magnitude* — no Diophantine input — so
it is fully formalizable and free of sorries and axioms (the plan's M6 remark).

## The failure predicate

For the nearest integer `m = round((p/q)ⁿ)` write the signed residue `kₙ = pⁿ - m·qⁿ ∈ ℤ`.
Since `‖(p/q)ⁿ‖ = |kₙ| / qⁿ`, a *failure* `‖(p/q)ⁿ‖ < cⁿ` is exactly the integer condition
`|kₙ| < (c·q)ⁿ` (`isFailure_iff`).  For `(3, 2, 3/4)` this is the exact-integer predicate of
`BB13/m0_failures.py`, whose failure set up to `n = 10⁶` is `{1, 2, 3, 4, 7}` (all on the
run-of-zeros side; the run-of-ones/Waring subset is empty).  The decidable `Nat`-level mirror
`failNat` reproduces `{1, 2, 3, 4, 7}` here (`failNat_initial_segment`), cross-checking the
Python numerics.

## Contents

* `BB13.Mnum`, `BB13.resid` — the nearest-integer numerator `m` and the signed residue `k`.
* `BB13.IsFailure` — `|kₙ| < (c·q)ⁿ`; `isFailure_iff` identifies it with `‖(p/q)ⁿ‖ < cⁿ`.
* `BB13.Linkable`, `BB13.IsTowerBase` — the §3 linkage relation `2·cᵃ·pᵇ⁻ᵃ ≤ 1` and the tower
  bases (failures not linked to any smaller failure).
* `BB13.epsilon` — the sharp gap exponent `ε = log(1/c)/log p` (`= log(4/3)/log 3 = 0.26186…`
  for `(3, 2, 3/4)`; M1 value).
* `residNat`, `failNat` — the decidable exact-integer failure predicate for `(3, 2, 3/4)`.

## References

* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, Cambridge Tracts
  in Mathematics **193**, 2012 (Problem 10.13).
* [DD90] F. Delmer, J.-M. Deshouillers, *The computation of `g(k)` in Waring's problem*, Math.
  Comp. **54** (1990), 885–893 (the exact-integer `(3/2)`-side recursion).
-/

namespace BB13

open scoped Real

/-- The **nearest-integer numerator** `m = round((p/q)ⁿ)`: the integer nearest to `(p/q)ⁿ`. -/
noncomputable def Mnum (p q n : ℕ) : ℤ := round (((p : ℝ) / q) ^ n)

/-- The **signed residue** `kₙ = pⁿ - m·qⁿ` of `(p/q)ⁿ` against its nearest integer.  One has
`‖(p/q)ⁿ‖ = |kₙ| / qⁿ`, so `kₙ` carries the whole failure test. -/
noncomputable def resid (p q n : ℕ) : ℤ := (p : ℤ) ^ n - Mnum p q n * (q : ℤ) ^ n

/-- A **failure** at `n`: `‖(p/q)ⁿ‖ < cⁿ`, in the exact-integer form `|kₙ| < (c·q)ⁿ`
(see `isFailure_iff`).  For `(3, 2, 3/4)` this is `|3ⁿ - m·2ⁿ| < (3/2)ⁿ`. -/
def IsFailure (p q : ℕ) (c : ℝ) (n : ℕ) : Prop := (|resid p q n| : ℝ) < (c * q) ^ n

/-- The **linkage relation** of §3: two failures at `a < b` are *linkable* when
`2·cᵃ·pᵇ⁻ᵃ ≤ 1`.  Under this bound the §3 gap identity forces `b` to be a `pᵇ⁻ᵃ`-scaling of the
base `a` (`BB13.GapPrinciple.linkage`); asymptotically it holds iff `b - a < ε·a`. -/
def Linkable (p : ℕ) (c : ℝ) (a b : ℕ) : Prop := 2 * c ^ a * (p : ℝ) ^ (b - a) ≤ 1

/-- A **tower base**: a failure not linked to any smaller failure.  Every failure sits in a
unique tower over such a base; the tower count `#{tower bases ≤ N}` is `O(log N)` (T4,
`BB13.TowerCount`). -/
def IsTowerBase (p q : ℕ) (c : ℝ) (b : ℕ) : Prop :=
  IsFailure p q c b ∧ ∀ a, a < b → IsFailure p q c a → ¬ Linkable p c a b

/-- The **sharp gap exponent** `ε = log(1/c)/log p` (M1).  Two failures within distance
`d < ε·n` of each other are linked, so tower bases grow by a factor `> 1 + ε`; for `(3, 2, 3/4)`,
`ε = log(4/3)/log 3 = 0.26186…` and the tower ratio is `1.26186…` (plan §3, `4.30 ln N` towers). -/
noncomputable def epsilon (p : ℕ) (c : ℝ) : ℝ := Real.log (1 / c) / Real.log p

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem epsilon_def (p : ℕ) (c : ℝ) :
    epsilon p c = Real.log (1 / c) / Real.log p := rfl

/-! ### The `(3, 2, 3/4)` exponents `ε*` and `θ`, and the subspace budget

The two reals the Diophantine layer runs on: the sharp gap exponent `ε* = log(4/3)/log 3` (the
`(3, 2, 3/4)` value of `epsilon`) and `θ = log 2/log 3`.  The single identity
`θ + θ + 1 = 2 + ε*` is what makes the frame of `BB13/LineCover.lean` exact: the reduction of a
failure to the Bugeaud–Evertse approximation system spends `θ` at the infinite place, `θ` at `2`
and `1` at `3`, and that budget is `2 + ε*` on the nose (both sides are `log 12/log 3`).  No
`ε` below `ε*` need be used, and none above `ε*` is available. -/

/-- The **sharp exponent** `ε* = log(4/3)/log 3 = 0.26186…` — the `(p, q, c) = (3, 2, 3/4)` value
of `BB13.epsilon`.  The `n`-th failure threshold is `(3/4)ⁿ = (3ⁿ)^{-ε*}` (`rpow_neg_epsStar`). -/
noncomputable def epsStar : ℝ := Real.log (4 / 3) / Real.log 3

/-- The exponent `θ = log 2/log 3 = 0.63093…`: `(3ⁿ)^{-θ} = 2⁻ⁿ` (`rpow_neg_theta`), so `θ` is
the exponent that the archimedean and the `2`-adic conditions of the frame each cost. -/
noncomputable def theta : ℝ := Real.log 2 / Real.log 3

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem epsStar_eq_epsilon : epsStar = epsilon 3 (3 / 4) := by
  rw [epsStar, epsilon]; norm_num

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem epsStar_pos : 0 < epsStar :=
  div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem theta_pos : 0 < theta :=
  div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))

/-- **The budget identity** `θ + θ + 1 = 2 + ε*` (both sides are `log 12/log 3`).  The exponent
sum of the Bugeaud–Evertse system (5.10) is met by the failure frame with `ε = ε*` exactly. -/
@[category research solved, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem theta_add_theta_add_one : theta + theta + 1 = 2 + epsStar := by
  have h3 : Real.log 3 ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  have hlog : Real.log (4 / 3) = 2 * Real.log 2 - Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  rw [theta, epsStar, hlog]
  field_simp
  ring

/-- `(3ⁿ)^{-ε*} = (3/4)ⁿ`: the failure threshold **is** the subspace threshold at `ε*`, with no
headroom to spare and none needed (`IsFailure` is a strict inequality). -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem rpow_neg_epsStar (n : ℕ) : ((3 : ℝ) ^ n) ^ (-epsStar) = (3 / 4 : ℝ) ^ n := by
  have h3 : Real.log 3 ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  rw [← Real.rpow_natCast (3 : ℝ) n, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
    ← Real.rpow_natCast (3 / 4 : ℝ) n, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3 / 4)]
  congr 1
  have e1 : Real.log (3 / 4) = -Real.log (4 / 3) := by rw [← Real.log_inv]; norm_num
  rw [e1, epsStar]; field_simp

/-- `(3ⁿ)^{-θ} = (1/2)ⁿ`: the archimedean and `2`-adic sides of the frame both read `2⁻ⁿ`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem rpow_neg_theta (n : ℕ) : ((3 : ℝ) ^ n) ^ (-theta) = (1 / 2 : ℝ) ^ n := by
  have h3 : Real.log 3 ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  rw [← Real.rpow_natCast (3 : ℝ) n, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
    ← Real.rpow_natCast (1 / 2 : ℝ) n, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  congr 1
  have e1 : Real.log (1 / 2) = -Real.log 2 := by rw [← Real.log_inv]; norm_num
  rw [e1, theta]; field_simp

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem epsStar_mul_log_three : epsStar * Real.log 3 = Real.log (4 / 3) := by
  rw [epsStar, div_mul_cancel₀]
  exact Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem theta_mul_log_three : theta * Real.log 3 = Real.log 2 := by
  rw [theta, div_mul_cancel₀]
  exact Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)

/-- `4·log 2 < 10·log(4/3)`, i.e. `16 < (4/3)¹⁰` — the one numeric fact behind every height
threshold below, and it needs no decimal logarithm bounds: `16·3¹⁰ = 944 784 < 1 048 576 = 4¹⁰`. -/
@[category API, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem four_log_two_lt : 4 * Real.log 2 < 10 * Real.log (4 / 3) := by
  have e16 : 4 * Real.log 2 = Real.log 16 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; push_cast; ring
  have e43 : 10 * Real.log (4 / 3) = Real.log ((4 / 3 : ℝ) ^ 10) := by
    rw [Real.log_pow]; push_cast; ring
  rw [e16, e43]
  exact Real.log_lt_log (by norm_num) (by norm_num)

/-- **The height threshold of (5.12), in the form the frames need**, over an arbitrary base
`P > 1`: `2^{4/ε} < Pⁿ` whenever `4·log 2 < n·ε·log P`.  The general `(p, q, c)` frames of
`BB13/MahlerFrame.lean` use it at `P = p`; the headline case is the `P = 3` corollary below. -/
@[category API, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem two_rpow_four_div_lt_base {P : ℕ} {ε : ℝ} {n : ℕ} (hP : 1 < P) (hε : 0 < ε)
    (h : 4 * Real.log 2 < (n : ℝ) * (ε * Real.log P)) :
    (2 : ℝ) ^ ((4 : ℝ) / ε) < (P : ℝ) ^ n := by
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hP
  rw [← Real.rpow_natCast (P : ℝ) n, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos hP0, Real.exp_lt_exp, mul_div_assoc', div_lt_iff₀ hε]
  nlinarith [h]

/-- `2^{4/ε} < 3ⁿ` whenever `4·log 2 < n·ε·log 3` — the `P = 3` case of
`two_rpow_four_div_lt_base`. -/
@[category API, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem two_rpow_four_div_lt {ε : ℝ} {n : ℕ} (hε : 0 < ε)
    (h : 4 * Real.log 2 < (n : ℝ) * (ε * Real.log 3)) :
    (2 : ℝ) ^ ((4 : ℝ) / ε) < (3 : ℝ) ^ n := by
  have := two_rpow_four_div_lt_base (P := 3) (by norm_num) hε (by push_cast; exact h)
  simpa using this

/-- **The height threshold is cleared from `n = 10` on**: `2^{4/ε*} < 3ⁿ` for `n ≥ 10`.  The
Bugeaud–Evertse condition (5.12) at `ξ = 1` reads `3ⁿ > max(2, 2^{4/ε*})`, and
`2^{4/ε*} = 39584.…` sits between `3⁹ = 19683` and `3¹⁰ = 59049`. -/
@[category API, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem two_rpow_four_div_epsStar_lt {n : ℕ} (hn : 10 ≤ n) :
    (2 : ℝ) ^ ((4 : ℝ) / epsStar) < (3 : ℝ) ^ n := by
  refine two_rpow_four_div_lt epsStar_pos ?_
  rw [epsStar_mul_log_three]
  have h10 : (10 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hl43 : 0 < Real.log (4 / 3) := Real.log_pos (by norm_num)
  nlinarith [four_log_two_lt]

/-- **`‖(p/q)ⁿ‖ = |kₙ|/qⁿ`**: the nearest-integer distance is the signed residue over `qⁿ`.  The
identity behind both `isFailure_iff` and the archimedean condition of the subspace frame
(`BB13.frame_arch_eq`). -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem distToNearestInt_eq_resid (p q n : ℕ) (hq : 0 < q) :
    distToNearestInt (((p : ℝ) / q) ^ n) = |(resid p q n : ℝ)| / (q : ℝ) ^ n := by
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqn : (0 : ℝ) < (q : ℝ) ^ n := by positivity
  have hkey : ((p : ℝ) / q) ^ n - (Mnum p q n : ℝ) = (resid p q n : ℝ) / (q : ℝ) ^ n := by
    rw [resid]; push_cast; rw [div_pow]; field_simp
  rw [distToNearestInt, show round (((p : ℝ) / q) ^ n) = Mnum p q n from rfl, hkey, abs_div,
    abs_of_pos hqn]

/-- **`IsFailure` is exactly `‖(p/q)ⁿ‖ < cⁿ`.**  The exact-integer predicate `|kₙ| < (c·q)ⁿ`
coincides with the distance-to-nearest-integer statement, justifying the definition. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem isFailure_iff (p q : ℕ) (c : ℝ) (n : ℕ) (hq : 0 < q) :
    IsFailure p q c n ↔ distToNearestInt (((p : ℝ) / q) ^ n) < c ^ n := by
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqn : (0 : ℝ) < (q : ℝ) ^ n := by positivity
  rw [IsFailure, distToNearestInt_eq_resid p q n hq, div_lt_iff₀ hqn, ← Int.cast_abs, mul_pow]

/-! ## Numeric cross-check for `(p, q, c) = (3, 2, 3/4)`

The decidable exact-integer failure predicate, mirroring `BB13/m0_failures.py`:
`D_n = min(3ⁿ mod 2ⁿ, 2ⁿ − 3ⁿ mod 2ⁿ) = |kₙ|` and a failure is `2ⁿ·D_n < 3ⁿ`. -/

/-- `D_n = 2ⁿ·‖(3/2)ⁿ‖ = |kₙ|`, computed by hand from `3ⁿ mod 2ⁿ` (`= 3` and `2` case). -/
def residNat (n : ℕ) : ℕ := min (3 ^ n % 2 ^ n) (2 ^ n - 3 ^ n % 2 ^ n)

/-- The exact-integer failure test `2ⁿ·D_n < 3ⁿ` for `‖(3/2)ⁿ‖ < (3/4)ⁿ`. -/
def failNat (n : ℕ) : Bool := decide (2 ^ n * residNat n < 3 ^ n)

/-- The failure set of `‖(3/2)ⁿ‖ < (3/4)ⁿ` on `n ≤ 19` is `{0, 1, 2, 3, 4, 7}` — i.e. the
genuine failures `{1, 2, 3, 4, 7}` plus the degenerate `n = 0` (`k₀ = 0`).  This reproduces, in
the kernel, the initial segment of the `n ≤ 10⁶` scan in `BB13/m0_failures.py` (whose full
failure set is `{1, 2, 3, 4, 7}`, correcting the plan's earlier `{1, 2, 3, 4}`). -/
@[category test, AMS 11, ref "DD90", group "bugeaud_10_13"]
theorem failNat_initial_segment :
    (List.range 20).filter failNat = [0, 1, 2, 3, 4, 7] := by decide

end BB13
