/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC.Rung
import DubC.Engine
import DubC.Verdict

/-!
# Climbing the ladder for `a = 7`

This file runs the ladder of `DubC/Ladder.lean` with the witnesses of `DubC/Engine.lean` and the
certificates of `DubC/Rung.lean`, from `M₀ = ∏_{p≤17} p` up to `∏_{p≤31} p`, and concludes

    DubC.Rungs.cc4 : CoreClosed 7 primorial31 (fun r => cnK4 r.val = true)

— the global half of the compressed-core certificate, at the *core* (`371 702` residues).  What
is still missing to reach `DubC.Y31.Kset` (the `365 761` cycle states, on which `CoreDet` was
verified) is one further rank certificate inside the core; that is `DubC/Cycles.lean`.

## The shape of a level

At level `j` a residue `y` is described by `infⱼ y = (g, c)`, where `g` is its **grid index**
and `c` says it lies in the candidate set — the core one level down, pulled back.  Both are
produced by a single downward pass (`liftInf`), which is what keeps the cost of a state linear
in the depth of the ladder: the level-`j` predicate mentions the level-`j-1` predicate, so
evaluating them separately would re-walk the chain once per level.

Three predicates per level, each the previous one conjoined with a survival test:

| | meaning |
|---|---|
| `cnCⱼ` | candidate: the level-`j-1` core, pulled back along `ZMod Mⱼ → ZMod Mⱼ₋₁` |
| `cnFⱼ` | survives forward peeling inside `cnCⱼ` |
| `cnKⱼ` | survives backward peeling inside `cnFⱼ` — the level-`j` core |

and correspondingly two certificates per level, `ccⱼF` (`DubC.coreClosed_of_rankNat`) and `ccⱼ`
(`DubC.coreClosed_of_rankRevNat`).

## The enumeration

`loopⱼ` is the nest of loops that visits exactly the level-`j` grid: the outer loop runs over
`M₀`, and each further level contributes a loop of length its prime, entered only at states that
survived.  `loopⱼ_spec` turns it into the quantifier `∀ y < Mⱼ, cnCⱼ y = true → …` by iterating
`DubC.forall_lift_nat`, so the modulus `2·10¹¹` is never enumerated.

## What is checked, and what is trusted

`chkAll` is one `Bool`: all ten stage checks, run in a single evaluation so the engine executes
once.  Nothing about the engine is assumed anywhere — the arrays `Dⱼ.F`, `Dⱼ.B`, `Dⱼ.RK` enter
only as opaque data, and every obligation is verified against them as written.

## References

* **[Dub09]** A. Dubickas, *Prime and composite integers close to powers of a number*,
  Monatsh. Math. **158** (2009) 271–284.
-/

namespace DubC
namespace Rungs

open Engine

/-! ### The moduli -/

def M0 : ℕ := 510510
def M1 : ℕ := M0 * 19
def M2 : ℕ := M1 * 23
def M3 : ℕ := M2 * 29
def M4 : ℕ := primorial31

/-- The top of the ladder is the modulus of `DubC.Y31`. -/
@[category API, AMS 11 37, ref "Dub09", group "dubc_rungs"]
theorem M4_eq : M4 = M3 * 31 := by norm_num [M4, M3, M2, M1, M0, primorial31]

instance : NeZero M0 := ⟨by norm_num [M0]⟩
instance : NeZero M1 := ⟨by norm_num [M1, M0]⟩
instance : NeZero M2 := ⟨by norm_num [M2, M1, M0]⟩
instance : NeZero M3 := ⟨by norm_num [M3, M2, M1, M0]⟩
instance : NeZero M4 := ⟨by norm_num [M4, primorial31]⟩

/-! ### The witnesses -/

def D0 : RungData := runRung (mkLevel0 M0)
def D1 : RungData := runRung (mkGrid D0.L 19)
def D2 : RungData := runRung (mkGrid D1.L 23)
def D3 : RungData := runRung (mkGrid D2.L 29)
def D4 : RungData := runRung (mkGrid D3.L 31)

/-! ### Grid index and candidate membership, in one downward pass -/

/-- One level of `inf`: from the level below, the grid index at this level and the membership of
the projection in the level-below core. -/
def liftInf (Mp p : ℕ) (F B RK : Array ℕ) (prev : ℕ → ℕ × Bool) (y : ℕ) : ℕ × Bool :=
  let i := prev (y % Mp)
  let core := (i.2 && (F.getD i.1 0 == CAP)) && (B.getD i.1 0 == CAP)
  (RK.getD i.1 0 * p + y / Mp, core && decide (y % p ≠ 0))

/-- At the bottom the grid index of a residue is the residue, and the candidate set is the
units. -/
def inf0 (x : ℕ) : ℕ × Bool := (x, decide (Nat.Coprime x M0))

def inf1 : ℕ → ℕ × Bool := liftInf M0 19 D0.F D0.B D0.RK inf0
def inf2 : ℕ → ℕ × Bool := liftInf M1 23 D1.F D1.B D1.RK inf1
def inf3 : ℕ → ℕ × Bool := liftInf M2 29 D2.F D2.B D2.RK inf2
def inf4 : ℕ → ℕ × Bool := liftInf M3 31 D3.F D3.B D3.RK inf3

/-! ### The three predicates at each level -/

def cnC0 (x : ℕ) : Bool := (inf0 x).2
def cnF0 (x : ℕ) : Bool := (inf0 x).2 && (D0.F.getD (inf0 x).1 0 == CAP)
def cnK0 (x : ℕ) : Bool := cnF0 x && (D0.B.getD (inf0 x).1 0 == CAP)

def cnC1 (y : ℕ) : Bool := (inf1 y).2
def cnF1 (y : ℕ) : Bool := (inf1 y).2 && (D1.F.getD (inf1 y).1 0 == CAP)
def cnK1 (y : ℕ) : Bool := cnF1 y && (D1.B.getD (inf1 y).1 0 == CAP)

def cnC2 (y : ℕ) : Bool := (inf2 y).2
def cnF2 (y : ℕ) : Bool := (inf2 y).2 && (D2.F.getD (inf2 y).1 0 == CAP)
def cnK2 (y : ℕ) : Bool := cnF2 y && (D2.B.getD (inf2 y).1 0 == CAP)

def cnC3 (y : ℕ) : Bool := (inf3 y).2
def cnF3 (y : ℕ) : Bool := (inf3 y).2 && (D3.F.getD (inf3 y).1 0 == CAP)
def cnK3 (y : ℕ) : Bool := cnF3 y && (D3.B.getD (inf3 y).1 0 == CAP)

def cnC4 (y : ℕ) : Bool := (inf4 y).2
def cnF4 (y : ℕ) : Bool := (inf4 y).2 && (D4.F.getD (inf4 y).1 0 == CAP)
def cnK4 (y : ℕ) : Bool := cnF4 y && (D4.B.getD (inf4 y).1 0 == CAP)

@[category API, AMS 11 37, ref "Dub09", group "dubc_rungs"]
theorem and_left {a b : Bool} (h : (a && b) = true) : a = true := by
  simp only [Bool.and_eq_true] at h
  exact h.1

@[category API, AMS 11 37, ref "Dub09", group "dubc_rungs"]
theorem of_ite_true {b t : Bool} (h : (if b = true then t else true) = true) (hb : b = true) :
    t = true := by
  rw [hb] at h
  simpa using h

/-! ### The enumeration nest -/

def loop0 (f : ℕ → Bool) : Bool := allLt M0 f
def loop1 (f : ℕ → Bool) : Bool :=
  loop0 fun z => if cnK0 z then allLt 19 fun k => f (z + k * M0) else true
def loop2 (f : ℕ → Bool) : Bool :=
  loop1 fun z => if cnK1 z then allLt 23 fun k => f (z + k * M1) else true
def loop3 (f : ℕ → Bool) : Bool :=
  loop2 fun z => if cnK2 z then allLt 29 fun k => f (z + k * M2) else true
def loop4 (f : ℕ → Bool) : Bool :=
  loop3 fun z => if cnK3 z then allLt 31 fun k => f (z + k * M3) else true

@[category API, AMS 11 37, ref "Dub09", group "dubc_rungs"]
theorem loop0_spec {f : ℕ → Bool} (h : loop0 f = true) : ∀ y < M0, cnC0 y = true → f y = true :=
  fun y hy _ => allLt_spec h y hy

@[category API, AMS 11 37, ref "Dub09", group "dubc_rungs"]
theorem loop1_spec {f : ℕ → Bool} (h : loop1 f = true) : ∀ y < M1, cnC1 y = true → f y = true := by
  refine forall_lift_nat rfl (by norm_num [M0]) cnK0 cnC1 (fun _ hy => and_left hy) ?_
  intro z hz hcz k hk _
  exact allLt_spec (of_ite_true (loop0_spec h z hz (and_left (and_left hcz))) hcz) k hk

@[category API, AMS 11 37, ref "Dub09", group "dubc_rungs"]
theorem loop2_spec {f : ℕ → Bool} (h : loop2 f = true) : ∀ y < M2, cnC2 y = true → f y = true := by
  refine forall_lift_nat rfl (by norm_num [M1, M0]) cnK1 cnC2 (fun _ hy => and_left hy) ?_
  intro z hz hcz k hk _
  exact allLt_spec (of_ite_true (loop1_spec h z hz (and_left (and_left hcz))) hcz) k hk

@[category API, AMS 11 37, ref "Dub09", group "dubc_rungs"]
theorem loop3_spec {f : ℕ → Bool} (h : loop3 f = true) : ∀ y < M3, cnC3 y = true → f y = true := by
  refine forall_lift_nat rfl (by norm_num [M2, M1, M0]) cnK2 cnC3 (fun _ hy => and_left hy) ?_
  intro z hz hcz k hk _
  exact allLt_spec (of_ite_true (loop2_spec h z hz (and_left (and_left hcz))) hcz) k hk

@[category API, AMS 11 37, ref "Dub09", group "dubc_rungs"]
theorem loop4_spec {f : ℕ → Bool} (h : loop4 f = true) : ∀ y < M4, cnC4 y = true → f y = true := by
  refine forall_lift_nat M4_eq (by norm_num [M3, M2, M1, M0]) cnK3 cnC4
    (fun _ hy => and_left hy) ?_
  intro z hz hcz k hk _
  exact allLt_spec (of_ite_true (loop3_spec h z hz (and_left (and_left hcz))) hcz) k hk

/-! ### The checks -/

def chk0F : Bool := loop0 fun x => rungChkF M0 CAP inf0 D0.F x
def chk0B : Bool := loop0 fun x => rungChkB M0 CAP inf0 D0.F D0.B x
def chk1F : Bool := loop1 fun x => rungChkF M1 CAP inf1 D1.F x
def chk1B : Bool := loop1 fun x => rungChkB M1 CAP inf1 D1.F D1.B x
def chk2F : Bool := loop2 fun x => rungChkF M2 CAP inf2 D2.F x
def chk2B : Bool := loop2 fun x => rungChkB M2 CAP inf2 D2.F D2.B x
def chk3F : Bool := loop3 fun x => rungChkF M3 CAP inf3 D3.F x
def chk3B : Bool := loop3 fun x => rungChkB M3 CAP inf3 D3.F D3.B x
def chk4F : Bool := loop4 fun x => rungChkF M4 CAP inf4 D4.F x
def chk4B : Bool := loop4 fun x => rungChkB M4 CAP inf4 D4.F D4.B x

/-- **The whole ladder, in one evaluation.**  Ten stage checks over about `10⁷` grid states,
sharing a single run of the engine. -/
def chkAll : Bool :=
  chk0F && chk0B && chk1F && chk1B && chk2F && chk2B && chk3F && chk3B && chk4F && chk4B

@[category API, AMS 11 37, ref "Dub09", group "dubc_rungs"]
theorem chkAll_true : chkAll = true := by native_decide

theorem chk0F_true : chk0F = true := by
  have h := chkAll_true; simp only [chkAll, Bool.and_eq_true] at h; exact h.1.1.1.1.1.1.1.1.1
theorem chk0B_true : chk0B = true := by
  have h := chkAll_true; simp only [chkAll, Bool.and_eq_true] at h; exact h.1.1.1.1.1.1.1.1.2
theorem chk1F_true : chk1F = true := by
  have h := chkAll_true; simp only [chkAll, Bool.and_eq_true] at h; exact h.1.1.1.1.1.1.1.2
theorem chk1B_true : chk1B = true := by
  have h := chkAll_true; simp only [chkAll, Bool.and_eq_true] at h; exact h.1.1.1.1.1.1.2
theorem chk2F_true : chk2F = true := by
  have h := chkAll_true; simp only [chkAll, Bool.and_eq_true] at h; exact h.1.1.1.1.1.2
theorem chk2B_true : chk2B = true := by
  have h := chkAll_true; simp only [chkAll, Bool.and_eq_true] at h; exact h.1.1.1.1.2
theorem chk3F_true : chk3F = true := by
  have h := chkAll_true; simp only [chkAll, Bool.and_eq_true] at h; exact h.1.1.1.2
theorem chk3B_true : chk3B = true := by
  have h := chkAll_true; simp only [chkAll, Bool.and_eq_true] at h; exact h.1.1.2
theorem chk4F_true : chk4F = true := by
  have h := chkAll_true; simp only [chkAll, Bool.and_eq_true] at h; exact h.1.2
theorem chk4B_true : chk4B = true := by
  have h := chkAll_true; simp only [chkAll, Bool.and_eq_true] at h; exact h.2

/-! ### The certificates -/

@[category research solved, AMS 11 37, ref "Dub09", group "dubc_rungs"]
theorem cc0F : CoreClosed 7 M0 (fun r => cnF0 r.val = true) := by
  refine coreClosed_of_rankNat (by norm_num [M0]) (by norm_num [M0]) cnC0 cnF0
    (fun y => D0.F.getD (inf0 y).1 0) (coreClosed_copN 7 M0) ?_
  intro x hx hcx d hd hd0 hpar hy
  exact rungChkF_spec (loop0_spec chk0F_true x hx hcx) hcx d hd hd0 hpar hy

@[category research solved, AMS 11 37, ref "Dub09", group "dubc_rungs"]
theorem cc0 : CoreClosed 7 M0 (fun r => cnK0 r.val = true) := by
  refine coreClosed_of_rankRevNat (by norm_num [M0]) (by norm_num [M0]) cnF0 cnK0
    (fun y => D0.B.getD (inf0 y).1 0) cc0F ?_
  intro x hx hcx d hd hd0 hpar hy
  exact rungChkB_spec (loop0_spec chk0B_true x hx (and_left hcx)) hcx d hd hd0 hpar hy

@[category research solved, AMS 11 37, ref "Dub09", group "dubc_rungs"]
theorem cc1F : CoreClosed 7 M1 (fun r => cnF1 r.val = true) := by
  refine coreClosed_of_rankNat (by norm_num [M1, M0]) (by norm_num [M1, M0]) cnC1 cnF1
    (fun y => D1.F.getD (inf1 y).1 0) (coreClosed_comapUnitN ⟨19, rfl⟩ ⟨M0, by norm_num [M1, M0]⟩ (by norm_num) cnK0 cc0) ?_
  intro x hx hcx d hd hd0 hpar hy
  exact rungChkF_spec (loop1_spec chk1F_true x hx hcx) hcx d hd hd0 hpar hy

@[category research solved, AMS 11 37, ref "Dub09", group "dubc_rungs"]
theorem cc1 : CoreClosed 7 M1 (fun r => cnK1 r.val = true) := by
  refine coreClosed_of_rankRevNat (by norm_num [M1, M0]) (by norm_num [M1, M0]) cnF1 cnK1
    (fun y => D1.B.getD (inf1 y).1 0) cc1F ?_
  intro x hx hcx d hd hd0 hpar hy
  exact rungChkB_spec (loop1_spec chk1B_true x hx (and_left hcx)) hcx d hd hd0 hpar hy

@[category research solved, AMS 11 37, ref "Dub09", group "dubc_rungs"]
theorem cc2F : CoreClosed 7 M2 (fun r => cnF2 r.val = true) := by
  refine coreClosed_of_rankNat (by norm_num [M2, M1, M0]) (by norm_num [M2, M1, M0]) cnC2 cnF2
    (fun y => D2.F.getD (inf2 y).1 0) (coreClosed_comapUnitN ⟨23, rfl⟩ ⟨M1, by norm_num [M2, M1, M0]⟩ (by norm_num) cnK1 cc1) ?_
  intro x hx hcx d hd hd0 hpar hy
  exact rungChkF_spec (loop2_spec chk2F_true x hx hcx) hcx d hd hd0 hpar hy

@[category research solved, AMS 11 37, ref "Dub09", group "dubc_rungs"]
theorem cc2 : CoreClosed 7 M2 (fun r => cnK2 r.val = true) := by
  refine coreClosed_of_rankRevNat (by norm_num [M2, M1, M0]) (by norm_num [M2, M1, M0]) cnF2 cnK2
    (fun y => D2.B.getD (inf2 y).1 0) cc2F ?_
  intro x hx hcx d hd hd0 hpar hy
  exact rungChkB_spec (loop2_spec chk2B_true x hx (and_left hcx)) hcx d hd hd0 hpar hy

@[category research solved, AMS 11 37, ref "Dub09", group "dubc_rungs"]
theorem cc3F : CoreClosed 7 M3 (fun r => cnF3 r.val = true) := by
  refine coreClosed_of_rankNat (by norm_num [M3, M2, M1, M0]) (by norm_num [M3, M2, M1, M0])
    cnC3 cnF3 (fun y => D3.F.getD (inf3 y).1 0)
    (coreClosed_comapUnitN ⟨29, rfl⟩ ⟨M2, by norm_num [M3, M2, M1, M0]⟩ (by norm_num) cnK2 cc2) ?_
  intro x hx hcx d hd hd0 hpar hy
  exact rungChkF_spec (loop3_spec chk3F_true x hx hcx) hcx d hd hd0 hpar hy

@[category research solved, AMS 11 37, ref "Dub09", group "dubc_rungs"]
theorem cc3 : CoreClosed 7 M3 (fun r => cnK3 r.val = true) := by
  refine coreClosed_of_rankRevNat (by norm_num [M3, M2, M1, M0]) (by norm_num [M3, M2, M1, M0])
    cnF3 cnK3 (fun y => D3.B.getD (inf3 y).1 0) cc3F ?_
  intro x hx hcx d hd hd0 hpar hy
  exact rungChkB_spec (loop3_spec chk3B_true x hx (and_left hcx)) hcx d hd hd0 hpar hy

@[category research solved, AMS 11 37, ref "Dub09", group "dubc_rungs"]
theorem cc4F : CoreClosed 7 M4 (fun r => cnF4 r.val = true) := by
  refine coreClosed_of_rankNat (by norm_num [M4, primorial31]) (by norm_num [M4, primorial31])
    cnC4 cnF4 (fun y => D4.F.getD (inf4 y).1 0)
    (coreClosed_comapUnitN ⟨31, M4_eq⟩ ⟨M3, by rw [M4_eq]; ring⟩ (by norm_num) cnK3 cc3) ?_
  intro x hx hcx d hd hd0 hpar hy
  exact rungChkF_spec (loop4_spec chk4F_true x hx hcx) hcx d hd hd0 hpar hy

/-- **The global half of the compressed-core certificate at `𝒫 = {p ≤ 31}`.**  Every residue
lying on a cycle of the base-`7` coprimality subshift modulo `∏_{p≤31} p` lies in the computed
core `cnK4` — the `371 702` residues that survive forward and backward peeling at every rung of
the ladder. -/
@[category research solved, AMS 11 37, ref "Dub09" "DubOst06", group "dubc_rungs"]
theorem cc4 : CoreClosed 7 M4 (fun r => cnK4 r.val = true) := by
  refine coreClosed_of_rankRevNat (by norm_num [M4, primorial31]) (by norm_num [M4, primorial31])
    cnF4 cnK4 (fun y => D4.B.getD (inf4 y).1 0) cc4F ?_
  intro x hx hcx d hd hd0 hpar hy
  exact rungChkB_spec (loop4_spec chk4B_true x hx (and_left hcx)) hcx d hd hd0 hpar hy

end Rungs
end DubC
