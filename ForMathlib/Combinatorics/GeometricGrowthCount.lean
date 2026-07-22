/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-!
# Logarithmic counting for geometrically growing subsets of `ℕ`

A finite set `S ⊆ {1, …, N}` in which every element is at least `ρ` times any smaller
element (a *multiplicative gap* `ρ > 1`) can contain at most `1 + logᵨ N` elements: the
map `a ↦ ⌊logᵨ a⌋` is strictly monotone on `S`, so it injects `S` into the integer interval
`[0, ⌊logᵨ N⌋]`.

This is the abstract engine behind "geometric sparsity ⇒ `O(log N)` many objects" arguments
(gap principles, lacunary sequences, tower/ladder counts).  It is stated for `Finset ℕ` with
a real ratio `ρ`.

## Main results

* `card_le_logb_of_geomGap` — the clean bound `#S ≤ 1 + logᵨ N` under the gap `ρ·a ≤ b`
  for all `a < b` in `S`.
* `card_le_logb_of_geomGap_above` — the thresholded version: if the gap only holds for pairs
  with `t ≤ a`, then `#S ≤ t + (1 + logᵨ N)` (the `< t` part is counted trivially).  This is
  the form used when the multiplicative gap degrades near the bottom of the range.
-/

open scoped Real

/-- **Geometric-growth count.** If a finite set `S ⊆ {1, …, N}` of naturals has the
multiplicative-gap property that `ρ·a ≤ b` whenever `a < b` are both in `S` (with `ρ > 1`),
then `S` has at most `1 + logᵨ N` elements.

The proof sends `a ↦ ⌊logᵨ a⌋`; the gap makes this strictly increasing on `S`, hence injective,
and its image lies in the integer interval `[0, ⌊logᵨ N⌋]` of cardinality `⌊logᵨ N⌋ + 1`. -/
theorem card_le_logb_of_geomGap (ρ : ℝ) (hρ : 1 < ρ) (N : ℕ) (S : Finset ℕ)
    (h1 : ∀ a ∈ S, 1 ≤ a) (hN : ∀ a ∈ S, a ≤ N)
    (hgap : ∀ a ∈ S, ∀ b ∈ S, a < b → ρ * a ≤ b) :
    (S.card : ℝ) ≤ 1 + Real.logb ρ N := by
  have hlogρpos : 0 < Real.log ρ := Real.log_pos hρ
  have hlogN_nonneg : (0:ℝ) ≤ Real.logb ρ N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp [Real.logb]
    · exact Real.logb_nonneg hρ (by exact_mod_cast h)
  set g : ℕ → ℤ := fun a => ⌊Real.logb ρ a⌋ with hg
  -- the gap forces `g` to increase by at least one across a `<`-step
  have hstep : ∀ a ∈ S, ∀ b ∈ S, a < b → g a < g b := by
    intro a ha b hb hab
    have haR : (1:ℝ) ≤ a := by exact_mod_cast h1 a ha
    have hbge : ρ * a ≤ b := hgap a ha b hb hab
    have haRpos : (0:ℝ) < a := by linarith
    have hlog : Real.log (ρ * a) ≤ Real.log b := Real.log_le_log (by positivity) hbge
    have hmul : Real.log (ρ * a) = Real.log ρ + Real.log a :=
      Real.log_mul (by positivity) (by positivity)
    have keyl : Real.logb ρ a + 1 ≤ Real.logb ρ b := by
      rw [Real.logb, Real.logb, div_add_one (ne_of_gt hlogρpos),
        div_le_div_iff_of_pos_right hlogρpos]
      have : Real.log ρ + Real.log a ≤ Real.log b := by rw [← hmul]; exact hlog
      linarith
    have hfa : (⌊Real.logb ρ a⌋ : ℝ) ≤ Real.logb ρ a := Int.floor_le _
    have : (⌊Real.logb ρ a⌋ + 1 : ℤ) ≤ ⌊Real.logb ρ b⌋ := by
      apply Int.le_floor.mpr; push_cast; linarith
    simp only [hg]; omega
  have hinj : Set.InjOn g S := by
    intro a ha b hb hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact absurd hab (ne_of_lt (hstep a ha b hb h))
    · exact absurd hab.symm (ne_of_lt (hstep b hb a ha h))
  have hsub : S.image g ⊆ Finset.Icc 0 ⌊Real.logb ρ N⌋ := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    rw [Finset.mem_Icc]
    have haR : (1:ℝ) ≤ a := by exact_mod_cast h1 a ha
    have haRpos : (0:ℝ) < a := by linarith
    have haN : (a:ℝ) ≤ N := by exact_mod_cast hN a ha
    refine ⟨?_, ?_⟩
    · simp only [hg]; apply Int.le_floor.mpr; push_cast
      exact Real.logb_nonneg hρ haR
    · simp only [hg]; apply Int.floor_mono
      rw [Real.logb, Real.logb, div_le_div_iff_of_pos_right hlogρpos]
      exact Real.log_le_log haRpos haN
  have hcard : S.card = (S.image g).card := (Finset.card_image_of_injOn hinj).symm
  have hle : (S.image g).card ≤ (Finset.Icc (0:ℤ) ⌊Real.logb ρ N⌋).card :=
    Finset.card_le_card hsub
  rw [Int.card_Icc] at hle
  have hstep2 : (S.card : ℝ) ≤ ((⌊Real.logb ρ N⌋ + 1 - 0).toNat : ℝ) := by
    rw [hcard]; exact_mod_cast hle
  refine hstep2.trans ?_
  have hfloor_nonneg : 0 ≤ ⌊Real.logb ρ N⌋ := Int.le_floor.mpr (by push_cast; exact hlogN_nonneg)
  have heq : ((⌊Real.logb ρ N⌋ + 1 - 0).toNat : ℝ) = (⌊Real.logb ρ N⌋ : ℝ) + 1 := by
    have hz : ((⌊Real.logb ρ N⌋ + 1 - 0).toNat : ℤ) = ⌊Real.logb ρ N⌋ + 1 := by
      rw [sub_zero]; exact Int.toNat_of_nonneg (by omega)
    calc ((⌊Real.logb ρ N⌋ + 1 - 0).toNat : ℝ)
        = (((⌊Real.logb ρ N⌋ + 1 - 0).toNat : ℤ) : ℝ) := by push_cast; ring
      _ = ((⌊Real.logb ρ N⌋ + 1 : ℤ) : ℝ) := by rw [hz]
      _ = (⌊Real.logb ρ N⌋ : ℝ) + 1 := by push_cast; ring
  rw [heq]
  have := Int.floor_le (Real.logb ρ N)
  linarith

/-- **Thresholded geometric-growth count.** If the multiplicative gap `ρ·a ≤ b` only holds
for pairs `a < b` in `S` with `t ≤ a`, then `#S ≤ t + (1 + logᵨ N)`: elements below `t` are
counted trivially (there are at most `t` of them) and `card_le_logb_of_geomGap` handles the
rest.  This is the form needed when the gap comes from an inequality with a lower-order
additive defect that only dominates once `a` is large enough. -/
theorem card_le_logb_of_geomGap_above (ρ : ℝ) (hρ : 1 < ρ) (t N : ℕ) (S : Finset ℕ)
    (h1 : ∀ a ∈ S, 1 ≤ a) (hN : ∀ a ∈ S, a ≤ N)
    (hgap : ∀ a ∈ S, ∀ b ∈ S, t ≤ a → a < b → ρ * a ≤ b) :
    (S.card : ℝ) ≤ t + (1 + Real.logb ρ N) := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not (s := S) (p := fun a => t ≤ a)
  have hS1card : (S.filter (fun a => ¬ t ≤ a)).card ≤ t := by
    refine le_trans (Finset.card_le_card ?_) (le_of_eq (Finset.card_range t))
    intro a ha; rw [Finset.mem_filter] at ha; rw [Finset.mem_range]; omega
  have hS2card : ((S.filter (fun a => t ≤ a)).card : ℝ) ≤ 1 + Real.logb ρ N := by
    apply card_le_logb_of_geomGap ρ hρ N
    · intro a ha; rw [Finset.mem_filter] at ha; exact h1 a ha.1
    · intro a ha; rw [Finset.mem_filter] at ha; exact hN a ha.1
    · intro a ha b hb hab
      rw [Finset.mem_filter] at ha hb
      exact hgap a ha.1 b hb.1 ha.2 hab
  have hcast : (S.card : ℝ)
      = (S.filter (fun a => t ≤ a)).card + (S.filter (fun a => ¬ t ≤ a)).card := by
    rw [← hsplit]; push_cast; ring
  have hS1castR : ((S.filter (fun a => ¬ t ≤ a)).card : ℝ) ≤ t := by exact_mod_cast hS1card
  rw [hcast]; linarith
