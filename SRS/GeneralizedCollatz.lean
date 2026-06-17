/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Algebra.Ring.Rat
import Mathlib.Data.Int.ModEq
import Mathlib.Order.WithBot
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# Generalized Collatz functions (Yolcu–Aaronson–Heule)

[YAH] reduce the **Collatz conjecture** to a termination question about string rewriting. The
bridge is the notion of a *generalized Collatz function* (Definition 2.18): a piecewise-affine
self-map of `X⊥ = X ∪ {⊥}`, where the carrier `X` is one of `ℕ`, `ℕ⁺`, or `ℤ`. On each residue
class mod some fixed `d ≥ 2`, the map is either a single affine map `n ↦ qᵢ·n + rᵢ` with rational
coefficients (whose value must land back in `X`), or the *undefined* value `⊥`. The sentinel `⊥`,
fixed by the map (`f ⊥ = ⊥`), represents the undefined cases of a partial function — letting a
partial `f : X → X` be packaged as a total `f : X⊥ → X⊥`. Such an `f` is **convergent** when every
trajectory `n, f n, f² n, …` eventually reaches `⊥`.

The classical Collatz map fits this shape: over `d = 2`, even `n ≡ 0` go to `n/2`
(`q₀ = ½, r₀ = 0`) and odd `n ≡ 1` go to `3n + 1` (`q₁ = 3, r₁ = 1`); the conjecture that every
positive integer reaches `1` is the convergence of the variant that sends the orbit of `1` to `⊥`.

* `carrierInt` / `carrierNat` / `carrierPos` — the three admissible carriers `ℤ`, `ℕ`, `ℕ⁺`,
  realised as subsets of `ℤ` (so residues mod `d` and the affine values live in one ambient ring);
  `X⊥` is then `WithBot X`, with `⊥` the adjoined undefined element.
* `IsGeneralizedCollatzFunction X f` — **Definition 2.18**: `f : X⊥ → X⊥` fixes `⊥`, and there are
  an integer `d ≥ 2` and rationals `q r : Fin d → ℚ` such that on each residue class `i` mod `d`,
  *either* `f n = qᵢ·n + rᵢ` for all `n ≡ i` (the value lying in `X`), *or* `f n = ⊥` for all
  `n ≡ i`.
* `trajectory f x` / `Convergent f` — the trajectory `k ↦ fᵏ x` of a start point and convergence:
  every trajectory contains `⊥`.
* `iterate_eq_bot_of_map_bot` — once a trajectory reaches `⊥` it stays there (since `f ⊥ = ⊥`).
* `standardCollatz` / `isGeneralizedCollatzFunction_standardCollatz` — the standard Collatz map on
  `ℕ` (`even ↦ n/2`, `odd ↦ 3n+1`) as a generalized Collatz function (`d = 2`, `q = ![½, 3]`,
  `r = ![0, 1]`; both residue classes are affine, so it is *total* — no `⊥` branch).
* `isGeneralizedCollatzFunction_const_bot` / `convergent_const_bot` — non-vacuity: the totally
  undefined map `_ ↦ ⊥` is a (trivially convergent) generalized Collatz function.
-/

namespace StringRewriting.Collatz

open Function

/-- The carrier `X = ℤ`, as a subset of `ℤ`. -/
@[category API, AMS 68, ref "YAH", group "generalized_collatz"]
def carrierInt : Set ℤ := Set.univ

/-- The carrier `X = ℕ` (nonnegative integers), as a subset of `ℤ`. -/
@[category API, AMS 68, ref "YAH", group "generalized_collatz"]
def carrierNat : Set ℤ := {n | 0 ≤ n}

/-- The carrier `X = ℕ⁺` (positive integers), as a subset of `ℤ`. -/
@[category API, AMS 68, ref "YAH", group "generalized_collatz"]
def carrierPos : Set ℤ := {n | 0 < n}

/-- **Definition 2.18** (generalized Collatz function). Let `X` be one of `ℕ`, `ℕ⁺`, `ℤ` (here a
subset of `ℤ`) and `X⊥ = WithBot X`. A function `f : X⊥ → X⊥` is a *generalized Collatz function*
if `f ⊥ = ⊥` and there exist an integer `d ≥ 2` and rationals `q₀, …, q_{d-1}, r₀, …, r_{d-1}` such
that for every residue class `i` mod `d`, on all `n ≡ i (mod d)` the map has *either* the affine
form `f n = qᵢ·n + rᵢ` (the value being an element of `X`), *or* the undefined form `f n = ⊥`.

Mapping to `⊥` in the undefined cases is how a partially defined function is represented. -/
@[category API, AMS 68, ref "YAH", group "generalized_collatz"]
def IsGeneralizedCollatzFunction (X : Set ℤ) (f : WithBot X → WithBot X) : Prop :=
  f ⊥ = ⊥ ∧ ∃ d : ℕ, 2 ≤ d ∧ ∃ q r : Fin d → ℚ, ∀ i : Fin d,
    (∀ n : X, (n : ℤ) ≡ ((i : ℕ) : ℤ) [ZMOD (d : ℤ)] →
        ∃ m : X, f (↑n) = (↑m : WithBot X) ∧ ((m : ℤ) : ℚ) = q i * ((n : ℤ) : ℚ) + r i) ∨
    (∀ n : X, (n : ℤ) ≡ ((i : ℕ) : ℤ) [ZMOD (d : ℤ)] → f (↑n) = ⊥)

/-- The *trajectory* of a start point `x` under `f`: the orbit `k ↦ fᵏ x`. -/
@[category API, AMS 68, ref "YAH", group "generalized_collatz"]
def trajectory {α : Type*} (f : WithBot α → WithBot α) (x : WithBot α) : ℕ → WithBot α :=
  fun k => f^[k] x

/-- A partial map `f` is *convergent* when every `f`-trajectory contains `⊥`. -/
@[category API, AMS 68, ref "YAH", group "generalized_collatz"]
def Convergent {α : Type*} (f : WithBot α → WithBot α) : Prop :=
  ∀ x : WithBot α, ∃ k : ℕ, trajectory f x k = ⊥

/-- Once a trajectory reaches the undefined value it stays there: if `f ⊥ = ⊥` then `fᵏ ⊥ = ⊥`. -/
@[category API, AMS 68, ref "YAH", group "generalized_collatz"]
theorem iterate_eq_bot_of_map_bot {α : Type*} {f : WithBot α → WithBot α} (hf : f ⊥ = ⊥) :
    ∀ k : ℕ, f^[k] ⊥ = ⊥
  | 0 => rfl
  | k + 1 => by rw [Function.iterate_succ_apply', iterate_eq_bot_of_map_bot hf k, hf]

/-- The **standard Collatz map** on `ℕ` (`carrierNat`): an even `n` goes to `n/2`, an odd `n` goes
to `3n + 1`, and `⊥ ↦ ⊥`. Both residue classes mod `2` are affine, so this is a *total* generalized
Collatz function (it never takes the `⊥` branch); convergence to `⊥` would be a halting variant. -/
@[category API, AMS 68, ref "YAH", group "standard_collatz"]
def standardCollatz : WithBot carrierNat → WithBot carrierNat :=
  WithBot.map fun n =>
    if (n : ℤ) % 2 = 0 then
      ⟨(n : ℤ) / 2, by have := n.2; simp only [carrierNat, Set.mem_setOf_eq] at this ⊢; omega⟩
    else
      ⟨3 * (n : ℤ) + 1, by have := n.2; simp only [carrierNat, Set.mem_setOf_eq] at this ⊢; omega⟩

/-- The standard Collatz map is a generalized Collatz function (Definition 2.18): take `d = 2`,
`q = ![½, 3]`, `r = ![0, 1]`, with the even class `n ≡ 0` mapping by `½·n + 0 = n/2` and the odd
class `n ≡ 1` by `3·n + 1`. -/
@[category textbook, AMS 68, ref "YAH", group "standard_collatz"]
theorem isGeneralizedCollatzFunction_standardCollatz :
    IsGeneralizedCollatzFunction carrierNat standardCollatz := by
  refine ⟨rfl, 2, le_refl 2, ![1 / 2, 3], ![0, 1], ?_⟩
  intro i
  fin_cases i
  · left
    intro n hn
    have h2 : (n : ℤ) % 2 = 0 := by have h := hn; simp only [Int.ModEq] at h; omega
    obtain ⟨k, hk⟩ : ∃ k : ℤ, (n : ℤ) = 2 * k := ⟨(n : ℤ) / 2, by omega⟩
    refine ⟨⟨(n : ℤ) / 2, by
      have := n.2; simp only [carrierNat, Set.mem_setOf_eq] at this ⊢; omega⟩, ?_, ?_⟩
    · simp only [standardCollatz, WithBot.map_coe, h2, if_pos]
    · show (((n : ℤ) / 2 : ℤ) : ℚ) = 1 / 2 * ((n : ℤ) : ℚ) + 0
      have hk2 : (n : ℤ) / 2 = k := by omega
      rw [hk2, hk]; push_cast; ring
  · left
    intro n hn
    have h2 : (n : ℤ) % 2 = 1 := by have h := hn; simp only [Int.ModEq] at h; omega
    have hne : ¬ ((n : ℤ) % 2 = 0) := by omega
    refine ⟨⟨3 * (n : ℤ) + 1, by
      have := n.2; simp only [carrierNat, Set.mem_setOf_eq] at this ⊢; omega⟩, ?_, ?_⟩
    · simp only [standardCollatz, WithBot.map_coe, if_neg hne]
    · show ((3 * (n : ℤ) + 1 : ℤ) : ℚ) = 3 * ((n : ℤ) : ℚ) + 1
      push_cast; ring

/-- Non-vacuity: the totally undefined map `_ ↦ ⊥` is a generalized Collatz function (take `d = 2`
and let every residue class be the undefined branch). -/
@[category test, AMS 68, ref "YAH", group "generalized_collatz"]
theorem isGeneralizedCollatzFunction_const_bot (X : Set ℤ) :
    IsGeneralizedCollatzFunction X (fun _ => ⊥) := by
  refine ⟨rfl, 2, le_refl 2, 0, 0, ?_⟩
  intro i
  exact Or.inr fun n _ => rfl

/-- Non-vacuity: the totally undefined map is convergent (every trajectory is `⊥` already at
step `1`), so `Convergent` is satisfiable. -/
@[category test, AMS 68, ref "YAH", group "generalized_collatz"]
theorem convergent_const_bot {α : Type*} :
    Convergent (fun _ : WithBot α => (⊥ : WithBot α)) := by
  intro x
  exact ⟨1, rfl⟩

end StringRewriting.Collatz
