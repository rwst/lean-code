/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Dubickas's sets `𝒮` and `𝒵`: even integral parts of powers of a real number

The formal home that `plans/report-dubickas.html` §D.6 asks for, and the base of
`plans/plan-dubD1.html` (milestone M2).

> **Definition** ([Dub06EO] p. 331).  For `α > 1`, either for every real `ξ ≠ 0` the
> fractional parts `{ξ αⁿ}` are `≥ 1/2` for infinitely many `n`, or there is a real
> `ξ = ξ(α) ≠ 0` with `{ξ αⁿ} < 1/2` for every `n ∈ ℕ`.  The set of `α` for which the
> second possibility holds is `𝒵`; its complement in `(1, ∞)` is `𝒮`.  Equivalently,
> `α ∈ 𝒵` iff there is a real `ξ ≠ 0` such that the integral parts `⌊ξ αⁿ⌋`,
> `n = 1, 2, …`, are **all even**.

We take the *even integral part* form as the definition: it is the form Mahler's question
is about, the form `plans/report-dubickas.html` §D.1 states, and the form every
construction in this root produces.  The two are interchanged by `ξ ↦ 2ξ`.

## Conventions, checked against the primary text (plan gate G-4)

* `⌊·⌋` is the **floor** throughout [Dub06EO].
* `ξ` ranges over **all** nonzero reals, of either sign — Dubickas himself uses
  `ξ = -α^{n₀}` in the proof of Theorem 1(iii).
* the quantifier is `n ≥ 1`, not `n ≥ 0` ("`n = 1, 2, …`").  Every witness constructed in
  this root happens to work from `n = 0` as well, which is strictly stronger.
* `𝒵` is **tail-closed**: if `⌊ξ αⁿ⌋` is even for all `n ≥ N`, replace `ξ` by `ξ α^N`
  (`mem_MahlerZ_of_eventually` below).  Dubickas uses this twice, on pp. 333–334.

## Reference key

⚠️  This corpus already uses the key `[Dub06]` — in the docstrings of
`Bugeaud/Chapter3/*.lean` and `TShift/CriticalBox.lean` — for a *different* 2006 Dubickas
paper (*Arithmetical properties of powers of algebraic numbers*, Bull. London Math. Soc.
**38**).  The `SZ/` root therefore writes **`[Dub06EO]`** for the Glasgow paper below.
`plans/plan-dubD1.html` and `plans/report-dubickas.html` call it `[Dub06]`.

## References

* [Dub06EO] A. Dubickas, *Even and odd integral parts of powers of a real number*,
  Glasgow Math. J. **48** (2006), 331–336.
* [Mah68] K. Mahler, *An unsolved problem on the powers of 3/2*, J. Austral. Math. Soc.
  **8** (1968), 313–321.
-/

namespace SZ

open Int

/-- **Dubickas's set `𝒵`** ([Dub06EO] p. 331): the real numbers `α > 1` for which some
nonzero real `ξ` makes every integral part `⌊ξ αⁿ⌋`, `n ≥ 1`, even. -/
def MahlerZ : Set ℝ :=
  {α : ℝ | 1 < α ∧ ∃ ξ : ℝ, ξ ≠ 0 ∧ ∀ n : ℕ, 1 ≤ n → Even ⌊ξ * α ^ n⌋}

/-- **Dubickas's set `𝒮`** ([Dub06EO] p. 331): the complement of `𝒵` in `(1, ∞)`.  For
`α ∈ 𝒮`, *every* nonzero `ξ` produces infinitely many odd `⌊ξ αⁿ⌋`. -/
def S : Set ℝ := {α : ℝ | 1 < α} \ MahlerZ

@[category API, AMS 11, ref "Dub06EO", group "dub06_sz_defs"]
theorem mem_MahlerZ_iff {α : ℝ} :
    α ∈ MahlerZ ↔ 1 < α ∧ ∃ ξ : ℝ, ξ ≠ 0 ∧ ∀ n : ℕ, 1 ≤ n → Even ⌊ξ * α ^ n⌋ := Iff.rfl

@[category API, AMS 11, ref "Dub06EO", group "dub06_sz_defs"]
theorem mem_S_iff {α : ℝ} : α ∈ S ↔ 1 < α ∧ α ∉ MahlerZ := Iff.rfl

@[category API, AMS 11, ref "Dub06EO", group "dub06_sz_defs"]
theorem union_eq {α : ℝ} (hα : 1 < α) : α ∈ MahlerZ ∨ α ∈ S := by
  by_cases h : α ∈ MahlerZ
  · exact Or.inl h
  · exact Or.inr ⟨hα, h⟩

@[category API, AMS 11, ref "Dub06EO", group "dub06_sz_defs"]
theorem not_mem_both {α : ℝ} : ¬ (α ∈ MahlerZ ∧ α ∈ S) := fun h => h.2.2 h.1

/-! ## Tail closure

The one structural property of `𝒵` every construction below leans on: a witness only has
to work from some point on. -/

/-- **Tail closure.**  If `⌊ξ αⁿ⌋` is even for all `n ≥ N`, then `α ∈ 𝒵` — with the
witness `ξ α^N`. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_sz_defs"]
theorem mem_MahlerZ_of_eventually {α ξ : ℝ} (hα : 1 < α) (hξ : ξ ≠ 0) (N : ℕ)
    (h : ∀ n : ℕ, N ≤ n → Even ⌊ξ * α ^ n⌋) : α ∈ MahlerZ := by
  have hα0 : α ≠ 0 := ne_of_gt (lt_trans zero_lt_one hα)
  refine ⟨hα, ξ * α ^ N, mul_ne_zero hξ (pow_ne_zero N hα0), fun n hn => ?_⟩
  have e : ξ * α ^ N * α ^ n = ξ * α ^ (N + n) := by rw [pow_add]; ring
  rw [e]
  exact h _ (by omega)

/-- The workhorse: an explicit even integer sequence tracking the floors from `N` on. -/
@[category API, AMS 11, ref "Dub06EO", group "dub06_sz_defs"]
theorem mem_MahlerZ_of_floor_eq {α ξ : ℝ} (hα : 1 < α) (hξ : ξ ≠ 0) (N : ℕ) (x : ℕ → ℤ)
    (hx : ∀ n : ℕ, N ≤ n → Even (x n)) (hfl : ∀ n : ℕ, N ≤ n → ⌊ξ * α ^ n⌋ = x n) :
    α ∈ MahlerZ :=
  mem_MahlerZ_of_eventually hα hξ N fun n hn => (hfl n hn) ▸ hx n hn

/-! ## The trivial members, and Mahler's question -/

/-- Every integer `g ≥ 2` lies in `𝒵`: take `ξ = 2`, so that `⌊2 gⁿ⌋ = 2 gⁿ`
([Dub06EO] p. 331). -/
@[category research solved, AMS 11, ref "Dub06EO", group "dub06_sz_defs"]
theorem natCast_mem_MahlerZ {g : ℕ} (hg : 2 ≤ g) : (g : ℝ) ∈ MahlerZ := by
  refine ⟨by exact_mod_cast hg.trans_lt' one_lt_two, 2, two_ne_zero, fun n _ => ?_⟩
  have e : (2 : ℝ) * (g : ℝ) ^ n = ((2 * (g : ℤ) ^ n : ℤ) : ℝ) := by push_cast; ring
  rw [e, Int.floor_intCast]
  exact ⟨(g : ℤ) ^ n, by ring⟩

/-- **Mahler's question** (1968; [Dub06EO] abstract and p. 331).  *Is there a nonzero real
`ξ` for which every `⌊ξ (3/2)ⁿ⌋` is even?*  Stated, never assumed: this root proves
nothing about it, and `plans/report-dubickas.html` §C.5 prices the local approach out.
Formally, the question asks whether this `Prop` holds. -/
def MahlerQuestion : Prop := ((3 : ℝ) / 2) ∈ MahlerZ

/-- **[Dub06EO] Problem 5.**  *Is there an element of `𝒮` greater than `2`?*  Stated, not
assumed.  `SZ/Classification.lean` proves no quadratic Pisot number can be one. -/
def Problem5 : Prop := ∃ α ∈ S, 2 < α

end SZ
