import Mathlib

set_option autoImplicit false

open Finset Nat BigOperators
namespace PNat
variable {α M : Type*}
variable [PartialOrder α] [CommMonoid M] {f : α → M} {a b : α}
variable [LocallyFiniteOrder α]
variable {a b x: ℕ+}

theorem PNat.one_lt_of_lt (hab: a < b): 1 < b := by
  by_contra! hle
  rw [le_one_iff] at hle
  subst hle
  have : ¬a < 1 := not_lt_one a
  contradiction

theorem PNat.add_one (a : ℕ+) : a + 1 = succPNat a := rfl

theorem PNat.lt_succ_self (a : ℕ+) : a < succPNat a := lt.base a

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

theorem PNat.Icc_sub_one_right_not_mem (hb: 1 < b): b ∉ Icc a (b - 1) := by
  rw [mem_Icc]
  apply not_and_of_not_or_not
  exact Or.inr <| not_le.mpr <| PNat.sub_one_lt_self hb

theorem insert_Icc_sub_one_right (hab : a < b) : insert b (Icc a (b - 1))
  = Icc a b := by sorry -- committed

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

