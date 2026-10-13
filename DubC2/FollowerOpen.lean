/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.FollowerLiteral

/-!
# Infinite follower automata, and the zero-entropy question

A cell fails to certify for one of two reasons (`checked_iff_finite`): a reachable **branching**
state (two letters from a state that both return to it), or an **infinite** follower automaton `F`.

**Infinite `F` occurs.**  The unconstrained cell `3/2` at `ν = 0` (`PM = Pq = []`) has infinite
`F` (`triv32_infinite`).  The states `[xₙ, 1)` follow the `3/2`-orbit of `1/2`, which never
leaves `(0, 1)` and has `2`-adic denominator `2ⁿ⁺¹`.  That cell also branches at the root (the
letters `0` and `−1` both return), so it is uncertified for both reasons.

**The open question** is whether infinite `F` can be the *only* reason, i.e. whether some cell has
no reachable branching state and infinite `F`.  By `checked_iff_finite` and the literal T5(iv)
(`T5iv_literal`) the conjecture `no_zero_entropy_obstruction` (no such cell) has two equivalent
forms (`no_zero_entropy_obstruction_iff`):

* every cell without a reachable branching state is certified for some `D`;
* every cell without a reachable branching state has only eventually periodic avoiding
  pseudo-orbits.

A counterexample needs an infinite injective path of `F`, i.e. an endpoint orbit `f_w(0)` or
`f_w(1)` that stays in `(0, 1)` forever along an aperiodic word `w`.  Along an eventually periodic
word this is impossible (the clipped expanding map has a repeating orbit, `exists_rep_of_clip`).
It also needs every side branch to die or close up in a simple cycle.  The frontier survey of
plan-dubC2-transform (`xfrontier.py`: 13 frontier cells, 7 atlas controls) found no such cell;
every finite automaton there is either certified or branching.

## Main results

* `DubC2.Gen.Follower.triv32_infinite` — an admissible cell with infinite `F`;
* `DubC2.Gen.Follower.no_zero_entropy_obstruction_iff` — the equivalent forms of the conjecture;
* `DubC2.Gen.Follower.no_zero_entropy_obstruction` — the conjecture, **open** (`sorry`).

## References

* [Oda26] Y. Odagiri, *Finite graph certificates for composite terms in rational floor sequences*,
  Zenodo, doi:10.5281/zenodo.22997709 (2026).
-/

namespace DubC2.Gen

namespace Follower

open Filter ForMathlib.SubwordComplexity Horse Branch

/-! ## An infinite follower automaton -/

/-- The unconstrained cell `3/2` at `ν = 0`. -/
def triv32 : Params where
  p := 3
  q := 2
  a := 0
  b := 1
  D := 1
  M := 1
  qinv := 1
  PM := []
  Pq := []
  sLo := -1
  nA := 4

theorem triv32_checkParams : checkParams triv32 = true := by decide

/-- The `3/2`-orbit of `1/2` kept inside `(0, 1)` by the letters `0` and `1`. -/
def x32 : ℕ → ℚ
  | 0 => 1 / 2
  | n + 1 => if 3 * x32 n < 2 then 3 * x32 n / 2 else (3 * x32 n - 1) / 2

/-- The letter used at time `n`. -/
def σ32 (n : ℕ) : ℤ := if 3 * x32 n < 2 then 0 else 1

theorem x32_mem : ∀ n, 0 < x32 n ∧ x32 n < 1
  | 0 => by norm_num [x32]
  | n + 1 => by
    obtain ⟨h0, h1⟩ := x32_mem n
    simp only [x32]
    split_ifs with h <;> constructor <;> linarith

/-- `2ⁿ⁺¹·xₙ` is an odd integer. -/
theorem x32_odd : ∀ n, ∃ k : ℤ, Odd k ∧ x32 n * 2 ^ (n + 1) = k
  | 0 => ⟨1, odd_one, by norm_num [x32]⟩
  | n + 1 => by
    obtain ⟨k, hk, he⟩ := x32_odd n
    simp only [x32]
    split_ifs with h
    · refine ⟨3 * k, Odd.mul (by decide) hk, ?_⟩
      push_cast
      rw [← he]
      ring
    · refine ⟨3 * k - 2 ^ (n + 1), ?_, ?_⟩
      · exact Odd.sub_even (Odd.mul (by decide) hk) ((even_two).pow_of_ne_zero (by omega))
      · push_cast
        rw [← he]
        ring

theorem x32_injective : Function.Injective x32 := by
  have key : ∀ m n, m < n → x32 m ≠ x32 n := by
    intro m n hmn he
    obtain ⟨k, hk, hke⟩ := x32_odd m
    obtain ⟨k', hk', hke'⟩ := x32_odd n
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hmn
    have : (k' : ℚ) = k * 2 ^ (j + 1) := by
      rw [← hke', ← hke, he]
      ring
    have hz : k' = k * 2 ^ (j + 1) := by exact_mod_cast this
    rw [hz, pow_succ, ← mul_assoc] at hk'
    exact Int.not_even_iff_odd.2 hk' (even_two.mul_left _)
  intro m n he
  rcases lt_trichotomy m n with h | h | h
  · exact absurd he (key m n h)
  · exact h
  · exact absurd he.symm (key n m h)

/-- The states `[xₙ, 1)`. -/
def X32 (n : ℕ) : FState := ⟨Finset.range 1, x32 n, 1⟩

theorem rstep_triv32 (s : ℤ) : rstep triv32 (Finset.range 1) s = Finset.range 1 := by
  ext r
  simp [rstep, rOK, Params.rnext, triv32]

theorem fw_triv32 (s : ℤ) (y : ℚ) : fw triv32.p triv32.q triv32.a triv32.b s y = (3 * y - s) / 2 := by
  simp [fw, triv32]

theorem step_X32 (n : ℕ) : step triv32 (X32 n) (σ32 n) = some (X32 (n + 1)) := by
  have hx := x32_mem (n + 1)
  have hlo : fw triv32.p triv32.q triv32.a triv32.b (σ32 n) (x32 n) = x32 (n + 1) := by
    rw [fw_triv32]
    simp only [σ32, x32]
    split_ifs <;> push_cast <;> ring
  have hhi : 1 ≤ fw triv32.p triv32.q triv32.a triv32.b (σ32 n) 1 := by
    rw [fw_triv32]
    simp only [σ32]
    split_ifs <;> norm_num
  have hI : istepX triv32 (X32 n) (σ32 n) = (x32 (n + 1), 1) := by
    simp only [istepX, istep, X32, hlo, min_eq_left hhi, max_eq_right hx.1.le]
  have hR : (X32 n).R = Finset.range 1 := rfl
  unfold step
  rw [hR, rstep_triv32, hI]
  split_ifs with h
  · rfl
  · exact absurd ⟨by simp [sOK, triv32], by simp, hx.2⟩ h

theorem step_root_triv32 : step triv32 (root triv32) (-1) = some (X32 0) := by
  have hI : istepX triv32 (root triv32) (-1) = (x32 0, 1) := by
    simp only [istepX, istep, root, fw_triv32]
    norm_num [x32]
  have hR : (root triv32).R = Finset.range 1 := rfl
  unfold step
  rw [hR, rstep_triv32, hI]
  split_ifs with h
  · rfl
  · exact absurd ⟨by simp [sOK, triv32], by simp, by norm_num [x32]⟩ h

theorem reach_X32 : ∀ n, Reach triv32 (root triv32) (X32 n)
  | 0 => Relation.ReflTransGen.single ⟨-1, step_root_triv32⟩
  | n + 1 => (reach_X32 n).tail ⟨σ32 n, step_X32 n⟩

/-- **An admissible cell with infinite follower automaton**: `3/2` at `ν = 0`, no avoidance. -/
@[category research solved, AMS 11 37, ref "Oda26", group "dubc2_obstruction"]
theorem triv32_infinite : {X | Reach triv32 (root triv32) X}.Infinite :=
  Set.infinite_of_injective_forall_mem (f := X32)
    (fun _ _ h => x32_injective (congrArg FState.lo h)) reach_X32

/-! ## The zero-entropy question -/

/-- A **zero-entropy obstruction**: an admissible cell with no reachable branching state whose
follower automaton is infinite. -/
def ZeroEntropyObstruction (P : Params) : Prop :=
  checkParams P = true ∧ (∀ X, Reach P (root P) X → ¬ Branching P X) ∧
    {X | Reach P (root P) X}.Infinite

/-- The two equivalent forms of `no_zero_entropy_obstruction`: without a reachable branching state,
`F` finite ⟺ certified ⟺ every avoiding pseudo-orbit eventually periodic. -/
@[category research solved, AMS 11 37, ref "Oda26", group "dubc2_obstruction"]
theorem no_zero_entropy_obstruction_iff {P : Params} (hP : checkParams P = true)
    (hnb : ∀ X, Reach P (root P) X → ¬ Branching P X) :
    List.TFAE [¬ ZeroEntropyObstruction P, ∃ D C, Checked { P with D := D } C,
      ∀ r y s, PseudoOrbit P r y s → IsEventuallyPeriodic s] := by
  tfae_have 1 ↔ 2 := by
    rw [checked_iff_finite hP]
    constructor
    · intro h
      have hfin : {X | Reach P (root P) X}.Finite := by
        by_contra hinf
        exact h ⟨hP, hnb, hinf⟩
      exact ⟨hfin, hnb, exists_checked_DF hP hfin hnb⟩
    · rintro ⟨hfin, -, -⟩ ⟨-, -, hinf⟩
      exact hinf hfin
  tfae_have 2 ↔ 3 := T5iv_literal hP
  tfae_finish

/-- **Conjecture (no zero-entropy obstruction).**  Every admissible cell without a reachable
branching state has a finite follower automaton; equivalently (`no_zero_entropy_obstruction_iff`)
it is certified, or all its avoiding pseudo-orbits are eventually periodic.  **Open**: a
counterexample needs an endpoint orbit that stays in `(0, 1)` forever along an aperiodic word
(a `Z`-number-type orbit).  No such cell is known, and the plan-dubC2-transform frontier has none. -/
@[category research open, AMS 11 37, ref "Oda26", group "dubc2_obstruction"]
theorem no_zero_entropy_obstruction : ∀ P, ¬ ZeroEntropyObstruction P := by
  sorry

end Follower

end DubC2.Gen
