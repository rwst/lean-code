import Mathlib

set_option autoImplicit false
open Nat PNat Set

variable {a b x: ℕ+}

example: x < b → x ≤ b := by exact fun a => LT.lt.le a

theorem PNat.le_succPNat: a ≤ succPNat a :=
    Nat.le.step Nat.le.refl

theorem PNat.sub_le : a - b ≤ a := by
  rw [← coe_le_coe, PNat.sub_coe]
  split_ifs with h
  · exact Nat.sub_le a b
  · exact a.2

theorem PNat.le_sub_one_of_lt (hab: a < b): a ≤ b - (1 : ℕ+) := by
  rw [← PNat.coe_le_coe, PNat.sub_coe]
  split_ifs with h
  · apply Nat.le_pred_of_lt hab
  · apply not_lt.mp at h
    simp_all only [PNat.le_one_iff, PNat.not_lt_one]

theorem PNat.le_of_le_sub_one (hx: x ≤ b - 1): x ≤ b := by
  apply LE.le.trans hx (a := x) (c := b) (b := b - 1)
  exact PNat.sub_le

theorem PNat.le_iff_eq_or_le_sub_one: x = b ∨ x ≤ b - 1 ↔ x ≤ b := by
  constructor
  · intro h
    rcases h with h | h
    · rw [le_iff_lt_or_eq] ; exact Or.inr h
    · apply PNat.le_of_le_sub_one at h ; exact h
  · intro h'
    rw [le_iff_lt_or_eq, or_comm] at h'
    rcases h' with h₁ | h₂
    left ; exact h₁
    right ; exact PNat.le_sub_one_of_lt h₂

theorem PNat.mem_insert_Icc_sub_one (hab : a < b): x ∈ insert b (Icc a (b - 1))
    → a ≤ x ∧ x ≤ b := by
  rw [mem_insert_iff, mem_Icc]
  apply le_of_lt at hab
  intro hh
  rcases hh with hh | hh
  · rw [hh] ; exact ⟨ hab, Eq.le rfl ⟩
  · exact ⟨ hh.1, PNat.le_of_le_sub_one hh.2 ⟩

theorem PNat.Icc_sub_one_right (hab : a < b) : insert b (Icc a (b - 1)) = Icc a b := by
  ext x
  constructor
  · intro h
    apply PNat.mem_insert_Icc_sub_one hab at h
    rw [mem_Icc]
    exact h
  · intro hh
    rw [mem_insert_iff, mem_Icc]
    rw [mem_Icc] at hh
    have hl: x = b ∨ a ≤ x ∧ x ≤ b - 1 ↔ (x = b ∨ a ≤ x) ∧ (x = b ∨ x ≤ b - 1) :=
      Iff.intro (Or.rec (fun ha => ⟨.inl ha, .inl ha⟩) (.imp .inr .inr))
            (And.rec <| .rec (fun _ => .inl ·) (.imp_right ∘ .intro))
    rw [hl]
    constructor
    · exact Or.inr hh.1
    · rw [PNat.le_iff_eq_or_le_sub_one]
      exact hh.2
