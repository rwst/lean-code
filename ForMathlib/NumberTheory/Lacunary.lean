/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module


public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Rify

@[expose] public section

open Filter

/-- Say a sequence is lacunary if there exists some $\lambda > 1$ such that
$a_{n+1}/a_n > \lambda$ for all sufficiently large $n$. -/
def IsLacunary (n : ℕ → ℕ) : Prop := ∃ c > (1 : ℝ), ∀ᶠ k in atTop, c * n k < n (k + 1)

/-- Every lacunary sequence is eventually strictly increasing. -/
lemma IsLacunary.eventually_lt {n : ℕ → ℕ} (hn : IsLacunary n) : ∀ᶠ k in atTop, n k < n (k + 1) := by
  obtain ⟨c, hc, h⟩ := hn
  obtain ⟨N, h⟩ := eventually_atTop.1 h
  refine eventually_atTop.2 ⟨N, fun b hb ↦ ?_⟩
  grw [hc] at h
  simpa using h _ hb

/-- The real-valued analogue of `IsLacunary`. -/
def IsLacunaryReal (a : ℕ → ℝ) : Prop :=
  ∃ c > (1 : ℝ), ∀ᶠ k in atTop, c * a k < a (k + 1)

/-- An ℕ-valued sequence is lacunary iff its real cast is lacunary as a real sequence. -/
lemma isLacunary_iff_isLacunaryReal {n : ℕ → ℕ} :
    IsLacunary n ↔ IsLacunaryReal (fun k => (n k : ℝ)) := Iff.rfl

/-- A positive lacunary real-valued sequence is eventually strictly increasing. -/
lemma IsLacunaryReal.eventually_lt {a : ℕ → ℝ} (ha : IsLacunaryReal a)
    (hpos : ∀ᶠ k in atTop, 0 < a k) : ∀ᶠ k in atTop, a k < a (k + 1) := by
  obtain ⟨c, hc, hlac⟩ := ha
  filter_upwards [hlac, hpos] with k hk hp using by nlinarith
