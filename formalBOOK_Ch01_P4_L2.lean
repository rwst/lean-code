import Mathlib

set_option autoImplicit false

open Finset Nat BigOperators PNat
namespace PNat
variable {α M : Type*}
variable [PartialOrder α] [CommMonoid M] {f : α → M} {a b : α}
variable [LocallyFiniteOrder α]
variable {a b x: ℕ+}

/- merged 2024-04-28 not yet released -/
theorem one_lt_of_lt {a b : ℕ+} (hab : a < b) : 1 < b := bot_le.trans_lt hab

/- merged 2024-04-28 not yet released -/
theorem add_one (a : ℕ+) : a + 1 = succPNat a := rfl

/- merged 2024-04-28 not yet released -/
theorem lt_succ_self (a : ℕ+) : a < succPNat a := lt.base a

/- PR #12492, awaiting review -/
theorem PNat.sub_le : a - b ≤ a := by
  rw [← coe_le_coe, PNat.sub_coe]
  split_ifs with h
  · exact Nat.sub_le a b
  · exact a.2

/- PR #12492, awaiting review -/
theorem PNat.le_sub_one_of_lt (hab: a < b): a ≤ b - (1 : ℕ+) := by
  rw [← PNat.coe_le_coe, PNat.sub_coe]
  split_ifs with h
  · apply Nat.le_pred_of_lt hab
  · apply not_lt.mp at h
    simp_all only [PNat.le_one_iff, PNat.not_lt_one]

/- PR #12492, awaiting review -/
theorem PNat.le_of_le_sub_one (hx: x ≤ b - 1): x ≤ b := by
  apply LE.le.trans hx (a := x) (c := b) (b := b - 1)
  exact PNat.sub_le

theorem PNat.add_sub_cancel : (a + b) - b = a := by
  rw [←PNat.coe_inj, PNat.sub_coe]
  split_ifs with h
  · exact Nat.sub_eq_of_eq_add rfl
  · have : b < a + b := lt_add_left b a
    exact False.elim (h this)

theorem PNat.sub_one_lt_self: ∀ {b : ℕ+} (_: 1 < b), b - 1 < b := by
  intro b
  induction b using PNat.recOn with
  | p1 => trivial
  | hp n =>
      intro
      rw [add_sub_cancel, PNat.add_one]
      exact PNat.lt_succ_self n

theorem PNat.le_iff_eq_or_le_sub_one: x = b ∨ x ≤ b - 1 ↔ x ≤ b := by
  constructor
  · intro h
    rcases h with h | h
    · rw [le_iff_lt_or_eq]; exact Or.inr h
    · exact PNat.le_of_le_sub_one h
  · intro h'
    rw [le_iff_lt_or_eq, or_comm] at h'
    rcases h' with h₁ | h₂
    · exact Or.inl h₁
    · exact Or.inr (PNat.le_sub_one_of_lt h₂)

/- Interval manipulations with bounds in PNat, should go in PNat/Interval.lean -/
theorem PNat.mem_insert_Icc_sub_one (hab : a < b): x ∈ insert b (Icc a (b - 1))
    → a ≤ x ∧ x ≤ b := by
  rw [mem_insert, mem_Icc]
  apply le_of_lt at hab
  intro hh
  rcases hh with hh | hh
  · rw [hh] ; exact ⟨ hab, Eq.le rfl ⟩
  · exact ⟨ hh.1, PNat.le_of_le_sub_one hh.2 ⟩

theorem PNat.Icc_sub_one_right_not_mem (hb: 1 < b): b ∉ Icc a (b - 1) := by
  rw [mem_Icc]
  apply not_and_of_not_or_not
  exact Or.inr <| not_le.mpr <| PNat.sub_one_lt_self hb

theorem PNat.insert_Icc_sub_one_right (hab : a < b) : insert b (Icc a (b - 1)) = Icc a b := by
  ext x
  constructor
  · intro h
    apply PNat.mem_insert_Icc_sub_one hab at h
    rw [mem_Icc]
    exact h
  · intro hh
    rw [mem_insert, mem_Icc]
    rw [mem_Icc] at hh
    have hl: x = b ∨ a ≤ x ∧ x ≤ b - 1 ↔ (x = b ∨ a ≤ x) ∧ (x = b ∨ x ≤ b - 1) :=
      Iff.intro (Or.rec (fun ha => ⟨.inl ha, .inl ha⟩) (.imp .inr .inr))
            (And.rec <| .rec (fun _ => .inl ·) (.imp_right ∘ .intro))
    rw [hl]
    constructor
    · exact Or.inr hh.1
    · rw [PNat.le_iff_eq_or_le_sub_one]
      exact hh.2

/- Product manipulations, should go in PNat/BigOperators.lean -/
theorem PNat.prod_Icc_succ_top (f: ℕ+ → M) (hab: a < b):
    (∏ k in Icc a b, f k) = (∏ k in Icc a (b - 1), f k) * f b := by
  rw [← PNat.insert_Icc_sub_one_right hab,
    prod_insert <| PNat.Icc_sub_one_right_not_mem <| PNat.one_lt_of_lt hab,
    mul_comm]

theorem PNat.prod_Icc_id_eq_factorial: ∀ {n : ℕ+}, (∏ x in Icc 1 n, x) = n ! := by
  intro n
  induction n using PNat.recOn with
  | p1 => rfl
  | hp n ih =>
    rw [prod_Icc_succ_top, PNat.add_coe, PNat.one_coe, factorial_succ]
    rw [PNat.mul_coe, PNat.add_coe, PNat.one_coe, PNat.add_sub_cancel]
    rw [Nat.add_zero, ih, mul_comm]
    rw [PNat.lt_add_one_iff]
    exact PNat.one_le n
