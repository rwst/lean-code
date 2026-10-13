/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.Follower
import Mathlib.Data.Nat.ChineseRemainder

/-!
# A kernel-checkable follower automaton

`DubC2.Gen.Follower.T5iv` needs the follower automaton `F` to be finite and decides certification
by its branching states.  This file turns both hypotheses into one Boolean check that the kernel
can evaluate on a concrete cell.

**Product states.**  The states of `F` carry a residue set mod `M`, which is too large to handle
directly.  When `PM` is pairwise coprime with product `M`, a residue set reachable from the root is
the product of one residue set per prime (Chinese remainder theorem), and the step acts prime by
prime (`rstep_prodR`).  So a state is encoded by one bitmask per prime of `PM`, the per-prime
automaton of `DubC2/xfrontier.py`.  The interval endpoints are stored as numerators over a fixed
denominator `Q`, and the interval step is done in integers (`istepX_gam`).

**The check** (`checkF`).  A binary search tree `T` lists encoded states with a label each.  For
every node and every letter the step is computed; the state must die or its successor must be
found in `T` with a label not larger.  At most one letter may keep the label.  The root must be
in `T`.  Then the reachable states are the decodings of nodes of `T`, so `F` is finite, every
endpoint lies on `(1/Q)ℤ`, and, since labels never increase along edges, a state reachable from its
own successor keeps its label, so no reachable state branches (`checkF_sound`).

## Main results

* `DubC2.Gen.Follower.rstep_prodR` — the residue step of a product set is the product of the
  per-prime steps (the correspondence with the per-prime automaton of `xfrontier.py`);
* `DubC2.Gen.Follower.checkF_sound` — a passed check gives the finiteness of `F`, the grid
  property at `D = Q` and the absence of reachable branching states;
* `DubC2.Gen.Follower.exists_checked_of_checkF` — a passed check with `D = Q` gives a checked
  certificate, hence the divisibility theorem `divisor_set_of_checked`;
* `DubC2.Gen.Follower.T5iv_of_checkF` — all four conditions of `T5iv` hold.

## References

* [Oda26] Y. Odagiri, *Finite graph certificates for composite terms in rational floor sequences*,
  Zenodo, doi:10.5281/zenodo.22997709 (2026).
-/

namespace DubC2.Gen

namespace Follower

open Horse

/-! ## Product residue sets -/

section Product

variable (P : Params)

/-- The mask of the prime `l` in a mask list aligned with `PM`. -/
def mk (ms : List ℕ) (l : ℕ) : ℕ := ms.getD (P.PM.idxOf l) 0

/-- The residues mod `M` whose reduction mod every `l ∈ PM` is in the mask of `l`. -/
def prodR (ms : List ℕ) : Finset ℕ :=
  (Finset.range P.M).filter fun r => P.PM.all fun l => (mk P ms l).testBit (r % l)

/-- One per-prime residue step on a bitmask, dropping the zero residue before and after. -/
def mstep (l m : ℕ) (s : ℤ) : ℕ :=
  orFold (List.range l)
    (fun r => m.testBit r && r != 0 && stepMod P.p l (invMod P.q l) r s != 0)
    (fun r => 2 ^ stepMod P.p l (invMod P.q l) r s)

/-- The per-prime step of a whole mask list. -/
def mstepAll (ms : List ℕ) (s : ℤ) : List ℕ := P.PM.map fun l => mstep P l (mk P ms l) s

/-- The Chinese-remainder side conditions: `PM` pairwise coprime, of primes `≥ 2`, product `M`. -/
def checkCRT : Bool :=
  decide (P.PM.Pairwise Nat.Coprime) && (P.PM.all fun l => decide (2 ≤ l)) && (P.M == P.PM.prod)

/-- The side conditions of `checkCRT`, unpacked. -/
structure CRTFacts : Prop where
  co : P.PM.Pairwise Nat.Coprime
  two : ∀ l ∈ P.PM, 2 ≤ l
  prod : P.M = P.PM.prod

variable {P}

theorem crtFacts (h : checkCRT P = true) : CRTFacts P := by
  simp only [checkCRT, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem mk_map (f : ℕ → ℕ) {l : ℕ} (hl : l ∈ P.PM) : mk P (P.PM.map f) l = f l := by
  have h := List.idxOf_lt_length_iff.2 hl
  simp only [mk, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem h, Option.map_some, Option.getD_some, List.getElem_idxOf h]

theorem testBit_mstep {l m j : ℕ} {s : ℤ} :
    (mstep P l m s).testBit j = true ↔ ∃ r < l, m.testBit r = true ∧ r ≠ 0 ∧
      stepMod P.p l (invMod P.q l) r s ≠ 0 ∧ stepMod P.p l (invMod P.q l) r s = j := by
  rw [mstep, testBit_orFold]
  simp only [List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq, Nat.testBit_two_pow,
    decide_eq_true_eq]
  constructor
  · rintro ⟨r, hr, ⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact ⟨r, hr, h1, h2, h3, h4⟩
  · rintro ⟨r, hr, h1, h2, h3, h4⟩
    exact ⟨r, hr, ⟨⟨h1, h2⟩, h3⟩, h4⟩

/-- The Chinese remainder theorem for `PM`: prescribed residues are met below `M`. -/
theorem exists_crt (hC : CRTFacts P) (ρ : ℕ → ℕ) :
    ∃ r < P.M, ∀ l ∈ P.PM, r % l = ρ l % l := by
  have co : P.PM.Pairwise (Function.onFun Nat.Coprime id) := hC.co
  refine ⟨Nat.chineseRemainderOfList ρ id P.PM co, ?_, fun l hl =>
    (Nat.chineseRemainderOfList ρ id P.PM co).2 l hl⟩
  have := Nat.chineseRemainderOfList_lt_prod ρ id P.PM co
    (fun l hl => by have := hC.two l hl; simp only [id]; omega)
  rwa [List.map_id, ← hC.prod] at this

/-- Uniqueness in the Chinese remainder theorem for `PM`. -/
theorem eq_of_mod_eq (hC : CRTFacts P) {r r' : ℕ} (hr : r < P.M) (hr' : r' < P.M)
    (h : ∀ l ∈ P.PM, r % l = r' % l) : r = r' := by
  have co : P.PM.Pairwise (Function.onFun Nat.Coprime id) := hC.co
  have hm : r ≡ r' [MOD (P.PM.map id).prod] := (Nat.modEq_list_map_prod_iff co).2 h
  rw [List.map_id, ← hC.prod] at hm
  rwa [Nat.ModEq, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hr'] at hm

/-- The residue step read mod a prime `l ∈ PM` is the per-prime step. -/
theorem rnext_mod (hF : ParamFacts P) (hC : CRTFacts P) {l : ℕ} (hl : l ∈ P.PM) (r : ℕ) (s : ℤ) :
    P.rnext r s % l = stepMod P.p l (invMod P.q l) (r % l) s := by
  have hl2 := hC.two l hl
  have hlM : l ∣ P.M := Nat.dvd_of_mod_eq_zero (hF.PM l hl)
  have hinv := invMod_spec hF hl2 hlM
  have h := rnext_modEq hF hl2 (by exact_mod_cast hlM) hinv (x := r) (ρ := r % l) s
    (by rw [Int.ModEq]; push_cast; rw [Int.emod_emod])
  have hlt := stepMod_lt (p := P.p) (l := l) (inv := invMod P.q l) (r := r % l) (by omega) s
  have : ((P.rnext r s % l : ℕ) : ℤ) = (stepMod P.p l (invMod P.q l) (r % l) s : ℕ) := by
    push_cast
    rw [h, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hlt)]
  exact_mod_cast this

/-- **The residue step of a product set is the product of the per-prime steps.** -/
theorem rstep_prodR (hF : ParamFacts P) (hC : CRTFacts P) (ms : List ℕ) (s : ℤ) :
    rstep P (prodR P ms) s = prodR P (mstepAll P ms s) := by
  ext r'
  simp only [rstep, prodR, Finset.mem_image, Finset.mem_filter, Finset.mem_range, rOK,
    Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨r, ⟨⟨hr, hm⟩, h0, h1⟩, rfl⟩
    refine ⟨rnext_lt hF r s, fun l hl => ?_⟩
    rw [mstepAll, mk_map _ hl, testBit_mstep]
    have hl2 := hC.two l hl
    refine ⟨r % l, Nat.mod_lt _ (by omega), hm l hl, h0 l hl, ?_, (rnext_mod hF hC hl r s).symm⟩
    rw [← rnext_mod hF hC hl]
    exact h1 l hl
  · rintro ⟨hr', hm⟩
    have hm' : ∀ l ∈ P.PM, ∃ ρ < l, (mk P ms l).testBit ρ = true ∧ ρ ≠ 0 ∧
        stepMod P.p l (invMod P.q l) ρ s ≠ 0 ∧ stepMod P.p l (invMod P.q l) ρ s = r' % l := by
      intro l hl
      have := hm l hl
      rwa [mstepAll, mk_map _ hl, testBit_mstep] at this
    choose! ρ hρ using hm'
    obtain ⟨r, hr, hrl⟩ := exists_crt hC ρ
    have hrl' : ∀ l ∈ P.PM, r % l = ρ l := fun l hl => by
      rw [hrl l hl, Nat.mod_eq_of_lt (hρ l hl).1]
    have hnext : ∀ l ∈ P.PM, P.rnext r s % l = r' % l := fun l hl => by
      rw [rnext_mod hF hC hl, hrl' l hl]
      exact (hρ l hl).2.2.2.2
    refine ⟨r, ⟨⟨hr, fun l hl => ?_⟩, fun l hl => ?_, fun l hl => ?_⟩,
      eq_of_mod_eq hC (rnext_lt hF r s) hr' hnext⟩
    · rw [hrl' l hl]; exact (hρ l hl).2.1
    · rw [hrl' l hl]; exact (hρ l hl).2.2.1
    · rw [hnext l hl, ← (hρ l hl).2.2.2.2]; exact (hρ l hl).2.2.2.1

/-- A product set with a residue in every mask is nonempty. -/
theorem prodR_nonempty (hC : CRTFacts P) {ms : List ℕ}
    (h : ∀ l ∈ P.PM, ∃ j < l, (mk P ms l).testBit j = true) : (prodR P ms).Nonempty := by
  choose! ρ hρ using h
  obtain ⟨r, hr, hrl⟩ := exists_crt hC ρ
  refine ⟨r, ?_⟩
  simp only [prodR, Finset.mem_filter, Finset.mem_range, List.all_eq_true]
  refine ⟨hr, fun l hl => ?_⟩
  rw [hrl l hl, Nat.mod_eq_of_lt (hρ l hl).1]
  exact (hρ l hl).2

/-- A nonempty product set has no zero mask. -/
theorem mk_ne_zero_of_nonempty {ms : List ℕ} (h : (prodR P ms).Nonempty) {l : ℕ}
    (hl : l ∈ P.PM) : mk P ms l ≠ 0 := by
  obtain ⟨r, hr⟩ := h
  simp only [prodR, Finset.mem_filter, List.all_eq_true] at hr
  intro h0
  have := hr.2 l hl
  rw [h0, Nat.zero_testBit] at this
  exact Bool.false_ne_true this

/-- The full masks give every residue. -/
theorem prodR_full (hC : CRTFacts P) :
    prodR P (P.PM.map fun l => 2 ^ l - 1) = Finset.range P.M := by
  ext r
  simp only [prodR, Finset.mem_filter, Finset.mem_range, List.all_eq_true, and_iff_left_iff_imp]
  intro _ l hl
  rw [mk_map _ hl, Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
  exact Nat.mod_lt _ (by have := hC.two l hl; omega)

end Product

/-! ## Intervals on a grid -/

section Grid

variable (P : Params)

/-- `q·b·Q·f_s(A/Q)`, an integer. -/
def ufw (Q A : ℕ) (s : ℤ) : ℤ :=
  (P.p : ℤ) * P.b * A - (s * P.b + ((P.p : ℤ) - P.q) * P.a) * Q

/-- An encoded follower state: the masks, and the endpoint numerators over `Q`. -/
abbrev Key := List ℕ × ℕ × ℕ

/-- The follower state encoded by a key. -/
def gam (Q : ℕ) (k : Key) : FState := ⟨prodR P k.1, (k.2.1 : ℚ) / Q, (k.2.2 : ℚ) / Q⟩

variable {P}

theorem fw_grid (hF : ParamFacts P) {Q : ℕ} (hQ : 0 < Q) (A : ℕ) (s : ℤ) :
    Branch.fw P.p P.q P.a P.b s ((A : ℚ) / Q) = (ufw P Q A s : ℚ) / ((P.q : ℚ) * P.b * Q) := by
  have hq : (P.q : ℚ) ≠ 0 := by have := hF.q1; positivity
  have hb : (P.b : ℚ) ≠ 0 := by have := hF.b0; positivity
  have hQ' : (Q : ℚ) ≠ 0 := by positivity
  simp only [Branch.fw, ufw]
  push_cast
  field_simp
  ring

/-- The interval step of an encoded state, in integers over `W = q·b·Q`. -/
theorem istepX_gam (hF : ParamFacts P) {Q : ℕ} (hQ : 0 < Q) (k : Key) (s : ℤ) :
    istepX P (gam P Q k) s =
      (((max 0 (ufw P Q k.2.1 s) : ℤ) : ℚ) / ((P.q : ℚ) * P.b * Q),
        ((min ((P.q : ℤ) * P.b * Q) (ufw P Q k.2.2 s) : ℤ) : ℚ) / ((P.q : ℚ) * P.b * Q)) := by
  have hW : (0 : ℚ) < (P.q : ℚ) * P.b * Q := by
    have := hF.q1; have := hF.b0; positivity
  simp only [istepX, Branch.istep, gam, fw_grid hF hQ]
  push_cast
  refine Prod.ext ?_ ?_
  · simp only
    rw [← max_div_div_right hW.le, zero_div]
  · simp only
    rw [← min_div_div_right hW.le, div_self hW.ne']

theorem grid_cast {w L : ℤ} (hw : 0 < w) (hL : 0 ≤ L) (hd : w ∣ L) (Q : ℕ) (hQ : 0 < Q) :
    (((L / w).toNat : ℕ) : ℚ) / Q = (L : ℚ) / ((w : ℚ) * Q) := by
  obtain ⟨m, rfl⟩ := hd
  have hm : 0 ≤ m := by
    by_contra h
    push Not at h
    nlinarith
  rw [Int.mul_ediv_cancel_left _ hw.ne']
  have hc : ((m.toNat : ℕ) : ℚ) = (m : ℚ) := by exact_mod_cast Int.toNat_of_nonneg hm
  rw [hc]
  have : (w : ℚ) ≠ 0 := by exact_mod_cast hw.ne'
  have : (Q : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp

end Grid

/-! ## A search tree of encoded states -/

/-- A binary search tree of encoded states, each with a label. -/
inductive LTree
  | leaf
  | node (l : LTree) (ms : List ℕ) (A B lab : ℕ) (r : LTree)

namespace LTree

/-- Lexicographic comparison of mask lists. -/
def cmpL : List ℕ → List ℕ → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => (compare a b).then (cmpL as bs)

/-- Comparison of keys. -/
def cmpK (k k' : Key) : Ordering :=
  (cmpL k.1 k'.1).then ((compare k.2.1 k'.2.1).then (compare k.2.2 k'.2.2))

/-- The label of a key, if the search finds it. -/
def find (k : Key) : LTree → Option ℕ
  | leaf => none
  | node l ms A B lab r =>
    match cmpK k (ms, A, B) with
    | .lt => find k l
    | .gt => find k r
    | .eq => if k = (ms, A, B) then some lab else none

/-- A predicate on every node. -/
def all (f : Key → ℕ → Bool) : LTree → Bool
  | leaf => true
  | node l ms A B lab r => f (ms, A, B) lab && all f l && all f r

/-- The keys of the nodes. -/
def keys : LTree → List Key
  | leaf => []
  | node l ms A B _ r => (ms, A, B) :: (keys l ++ keys r)

/-- A found key is a node: it is among the keys and passes every check on all nodes. -/
theorem find_spec : ∀ {T : LTree} {k : Key} {lab : ℕ}, T.find k = some lab →
    k ∈ T.keys ∧ ∀ f, T.all f = true → f k lab = true
  | leaf, _, _, h => by simp [find] at h
  | node l ms A B lab' r, k, lab, h => by
    simp only [find] at h
    split at h
    · obtain ⟨h1, h2⟩ := find_spec h
      refine ⟨by simp [keys, h1], fun f hf => ?_⟩
      simp only [all, Bool.and_eq_true] at hf
      exact h2 f hf.1.2
    · obtain ⟨h1, h2⟩ := find_spec h
      refine ⟨by simp [keys, h1], fun f hf => ?_⟩
      simp only [all, Bool.and_eq_true] at hf
      exact h2 f hf.2
    · split_ifs at h with he
      cases h
      subst he
      refine ⟨by simp [keys], fun f hf => ?_⟩
      simp only [all, Bool.and_eq_true] at hf
      exact hf.1.1

end LTree

/-! ## The check -/

theorem eq_of_length_le_one {α : Type*} {l : List α} (h : l.length ≤ 1) {a b : α} (ha : a ∈ l)
    (hb : b ∈ l) : a = b := by
  match l, h, ha, hb with
  | [_], _, ha, hb => simp only [List.mem_singleton] at ha hb; rw [ha, hb]

section Check

variable (P : Params)

/-- The encoded root: full masks, the interval `[0, Q/Q)`. -/
def rootKey (Q : ℕ) : Key := (P.PM.map fun l => 2 ^ l - 1, 0, Q)

/-- One encoded step, looked up in `T`: `some none` if the state dies, `some (some lab)` if the
successor is found with label `lab`, `none` if the check fails. -/
def aedge (Q : ℕ) (T : LTree) (k : Key) (s : ℤ) : Option (Option ℕ) :=
  if sOK P s = true then
    if max 0 (ufw P Q k.2.1 s) < min ((P.q : ℤ) * P.b * Q) (ufw P Q k.2.2 s) then
      if (mstepAll P k.1 s).all (· != 0) then
        if ((P.q : ℤ) * P.b ∣ max 0 (ufw P Q k.2.1 s)) ∧
            ((P.q : ℤ) * P.b ∣ min ((P.q : ℤ) * P.b * Q) (ufw P Q k.2.2 s)) then
          (T.find (mstepAll P k.1 s, (max 0 (ufw P Q k.2.1 s) / ((P.q : ℤ) * P.b)).toNat,
            (min ((P.q : ℤ) * P.b * Q) (ufw P Q k.2.2 s) / ((P.q : ℤ) * P.b)).toNat)).map some
        else none
      else some none
    else some none
  else some none

/-- The check at one node: every letter dies or leads to a found node with a label not larger,
and at most one letter keeps the label. -/
def nodeOK (Q : ℕ) (T : LTree) (k : Key) (lab : ℕ) : Bool :=
  ((List.range P.nA).all fun t => match aedge P Q T k (P.letter t) with
    | none => false
    | some none => true
    | some (some l') => decide (l' ≤ lab)) &&
  decide (((List.range P.nA).filter fun t =>
    aedge P Q T k (P.letter t) == some (some lab)).length ≤ 1)

/-- **The follower check**: side conditions, the root is found, every node passes `nodeOK`. -/
def checkF (Q : ℕ) (T : LTree) : Bool :=
  checkParams P && checkCRT P && decide (0 < Q) && (T.find (rootKey P Q)).isSome &&
    T.all (nodeOK P Q T)

variable {P}

theorem step_gam (hF : ParamFacts P) (hC : CRTFacts P) {Q : ℕ} (hQ : 0 < Q) (k : Key) (s : ℤ) :
    step P (gam P Q k) s =
      if sOK P s = true ∧ (prodR P (mstepAll P k.1 s)).Nonempty ∧
          max 0 (ufw P Q k.2.1 s) < min ((P.q : ℤ) * P.b * Q) (ufw P Q k.2.2 s) then
        some ⟨prodR P (mstepAll P k.1 s),
          ((max 0 (ufw P Q k.2.1 s) : ℤ) : ℚ) / ((P.q : ℚ) * P.b * Q),
          ((min ((P.q : ℤ) * P.b * Q) (ufw P Q k.2.2 s) : ℤ) : ℚ) / ((P.q : ℚ) * P.b * Q)⟩
      else none := by
  have hW : (0 : ℚ) < (P.q : ℚ) * P.b * Q := by
    have := hF.q1; have := hF.b0; positivity
  have hg : (gam P Q k).R = prodR P k.1 := rfl
  simp only [step, istepX_gam hF hQ, hg, rstep_prodR hF hC, div_lt_div_iff_of_pos_right hW,
    Int.cast_lt]

theorem aedge_none (hF : ParamFacts P) (hC : CRTFacts P) {Q : ℕ} (hQ : 0 < Q) {T : LTree}
    {k : Key} {s : ℤ} (h : aedge P Q T k s = some none) : step P (gam P Q k) s = none := by
  rw [step_gam hF hC hQ]
  simp only [aedge] at h
  split_ifs at h with h1 h2 h3 h4
  · simp [Option.map_eq_some_iff] at h
  · rw [ite_eq_right_iff]
    rintro ⟨-, hne, -⟩
    simp only [List.all_eq_true, bne_iff_ne, ne_eq, mstepAll, List.mem_map] at h3
    push Not at h3
    obtain ⟨_, ⟨l, hl, rfl⟩, h0⟩ := h3
    refine absurd ?_ (mk_ne_zero_of_nonempty hne hl)
    rw [mstepAll, mk_map _ hl]
    exact h0
  · rw [ite_eq_right_iff]
    exact fun h => absurd h.2.2 h2
  · rw [ite_eq_right_iff]
    exact fun h => absurd h.1 h1

theorem aedge_some (hF : ParamFacts P) (hC : CRTFacts P) {Q : ℕ} (hQ : 0 < Q) {T : LTree}
    {k : Key} {s : ℤ} {lab : ℕ} (h : aedge P Q T k s = some (some lab)) :
    ∃ k', T.find k' = some lab ∧ step P (gam P Q k) s = some (gam P Q k') := by
  simp only [aedge] at h
  split_ifs at h with h1 h2 h3 h4 <;> try (simp at h; done)
  have hf : T.find (mstepAll P k.1 s, (max 0 (ufw P Q k.2.1 s) / ((P.q : ℤ) * P.b)).toNat,
      (min ((P.q : ℤ) * P.b * Q) (ufw P Q k.2.2 s) / ((P.q : ℤ) * P.b)).toNat) = some lab := by
    simp only [Option.map_eq_some_iff, Option.some.injEq] at h
    obtain ⟨a, ha, rfl⟩ := h
    exact ha
  refine ⟨_, hf, ?_⟩
  have hne : (prodR P (mstepAll P k.1 s)).Nonempty := by
    apply prodR_nonempty hC
    intro l hl
    simp only [List.all_eq_true, bne_iff_ne, ne_eq, mstepAll, List.mem_map] at h3
    have h0 := h3 _ ⟨l, hl, rfl⟩
    obtain ⟨j, hj⟩ := Nat.exists_testBit_of_ne_zero h0
    refine ⟨j, ?_, by rw [mstepAll, mk_map _ hl]; exact hj⟩
    obtain ⟨r, -, -, -, -, rfl⟩ := testBit_mstep.1 hj
    exact stepMod_lt (by have := hC.two l hl; omega) s
  have hw : (0 : ℤ) < (P.q : ℤ) * P.b := by
    have := hF.q1; have := hF.b0; positivity
  have hL : (0 : ℤ) ≤ max 0 (ufw P Q k.2.1 s) := le_max_left _ _
  rw [step_gam hF hC hQ]
  split_ifs with hh
  swap
  · exact absurd ⟨h1, hne, h2⟩ hh
  simp only [gam, Option.some.injEq, FState.mk.injEq, true_and]
  rw [grid_cast hw hL h4.1 Q hQ, grid_cast hw (hL.trans h2.le) h4.2 Q hQ]
  push_cast
  exact ⟨rfl, rfl⟩

section Sound

variable {Q : ℕ} {T : LTree} (hc : checkF P Q T = true)
include hc

theorem checkF_facts : checkParams P = true ∧ CRTFacts P ∧ 0 < Q ∧
    (T.find (rootKey P Q)).isSome = true ∧ T.all (nodeOK P Q T) = true := by
  simp only [checkF, Bool.and_eq_true, decide_eq_true_eq] at hc
  exact ⟨hc.1.1.1.1, crtFacts hc.1.1.1.2, hc.1.1.2, hc.1.2, hc.2⟩

/-- A live letter at a found node leads to a found node with a label not larger. -/
theorem edge_rep {k : Key} {lab : ℕ} (hk : T.find k = some lab) {X Y : FState} (hX : gam P Q k = X)
    (hv : Valid X) {s : ℤ} (hs : step P X s = some Y) :
    ∃ t < P.nA, P.letter t = s ∧ ∃ k' lab', aedge P Q T k s = some (some lab') ∧
      T.find k' = some lab' ∧ gam P Q k' = Y ∧ lab' ≤ lab := by
  obtain ⟨hP, hC, hQ, -, hall⟩ := checkF_facts hc
  have hF := paramFacts hP
  have hn := (LTree.find_spec hk).2 _ hall
  have hsa := letter_mem hF hv hs
  simp only [alph, Finset.mem_image, Finset.mem_range] at hsa
  obtain ⟨t, ht, rfl⟩ := hsa
  refine ⟨t, ht, rfl, ?_⟩
  simp only [nodeOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hn
  have ht' := hn.1 t ht
  subst hX
  cases he : aedge P Q T k (P.letter t) with
  | none => simp [he] at ht'
  | some o =>
    cases o with
    | none => rw [aedge_none hF hC hQ he] at hs; cases hs
    | some lab' =>
      obtain ⟨k', hk', hst⟩ := aedge_some hF hC hQ he
      rw [hst] at hs
      cases hs
      simp only [he, decide_eq_true_eq] at ht'
      exact ⟨k', lab', rfl, hk', rfl, ht'⟩

/-- Every reachable state is encoded by a found node. -/
theorem reach_rep {X : FState} (h : Reach P (root P) X) :
    ∃ k lab, T.find k = some lab ∧ gam P Q k = X := by
  obtain ⟨hP, hC, hQ, hroot, -⟩ := checkF_facts hc
  induction h with
  | refl =>
    obtain ⟨lab, hlab⟩ := Option.isSome_iff_exists.1 hroot
    refine ⟨_, lab, hlab, ?_⟩
    simp only [gam, rootKey, root, prodR_full hC, FState.mk.injEq, true_and]
    have : (Q : ℚ) ≠ 0 := by positivity
    simp [this]
  | tail hr hbc ih =>
    obtain ⟨s, hs⟩ := hbc
    obtain ⟨k, lab, hk, hX⟩ := ih
    obtain ⟨-, -, -, k', lab', -, hk', hY, -⟩ := edge_rep hc hk hX (valid_of_reach hr) hs
    exact ⟨k', lab', hk', hY⟩

variable (P Q T) in
/-- The least label of a node encoding `X`. -/
noncomputable def labF (X : FState) : ℕ := sInf {l | ∃ k, T.find k = some l ∧ gam P Q k = X}

omit hc in
theorem labF_le {k : Key} {l : ℕ} (hk : T.find k = some l) {X : FState} (hX : gam P Q k = X) :
    labF P Q T X ≤ l :=
  Nat.sInf_le ⟨k, hk, hX⟩

theorem labF_mem {X : FState} (h : Reach P (root P) X) :
    ∃ k, T.find k = some (labF P Q T X) ∧ gam P Q k = X := by
  obtain ⟨k, l, hk, hX⟩ := reach_rep hc h
  exact Nat.sInf_mem (s := {l | ∃ k, T.find k = some l ∧ gam P Q k = X}) ⟨l, k, hk, hX⟩

theorem labF_step {X Y : FState} (h : Reach P (root P) X) {s : ℤ} (hs : step P X s = some Y) :
    labF P Q T Y ≤ labF P Q T X := by
  obtain ⟨k, hk, hX⟩ := labF_mem hc h
  obtain ⟨-, -, -, k', lab', -, hk', hY, hle⟩ := edge_rep hc hk hX (valid_of_reach h) hs
  exact (labF_le hk' hY).trans hle

theorem labF_reach {Y Z : FState} (hY : Reach P (root P) Y) (h : Reach P Y Z) :
    labF P Q T Z ≤ labF P Q T Y := by
  induction h with
  | refl => exact le_rfl
  | tail hr hbc ih =>
    obtain ⟨s, hs⟩ := hbc
    exact (labF_step hc (hY.trans hr) hs).trans ih

/-- **No reachable state branches.** -/
theorem not_branching_of_checkF {X : FState} (h : Reach P (root P) X) : ¬ Branching P X := by
  rintro ⟨s₁, s₂, Y₁, Y₂, hne, h₁, h₂, hr₁, hr₂⟩
  obtain ⟨-, -, -, -, hall⟩ := checkF_facts hc
  obtain ⟨k, hk, hX⟩ := labF_mem hc h
  have key : ∀ {s : ℤ} {Y : FState}, step P X s = some Y → Reach P Y X →
      ∃ t < P.nA, P.letter t = s ∧ aedge P Q T k s = some (some (labF P Q T X)) := by
    intro s Y hs hr
    obtain ⟨t, ht, hts, k', lab', he, hk', hY, hle⟩ := edge_rep hc hk hX (valid_of_reach h) hs
    have hYr : Reach P (root P) Y := h.tail ⟨s, hs⟩
    have h1 := labF_reach hc hYr hr
    have h2 := labF_le hk' hY
    exact ⟨t, ht, hts, by rw [he]; congr; omega⟩
  obtain ⟨t₁, ht₁, rfl, he₁⟩ := key h₁ hr₁
  obtain ⟨t₂, ht₂, rfl, he₂⟩ := key h₂ hr₂
  have hn := (LTree.find_spec hk).2 _ hall
  simp only [nodeOK, Bool.and_eq_true, decide_eq_true_eq] at hn
  have hm : ∀ t < P.nA, aedge P Q T k (P.letter t) = some (some (labF P Q T X)) →
      t ∈ (List.range P.nA).filter fun t =>
        aedge P Q T k (P.letter t) == some (some (labF P Q T X)) := fun t ht he => by
    simp [ht, he]
  have := eq_of_length_le_one hn.2 (hm t₁ ht₁ he₁) (hm t₂ ht₂ he₂)
  exact hne (by rw [this])

/-- **The follower check is sound**: `F` is finite, its endpoints lie on `(1/Q)ℤ`, and no
reachable state branches. -/
theorem checkF_sound :
    {X | Reach P (root P) X}.Finite ∧
      (∀ X, Reach P (root P) X → (∃ m : ℤ, X.lo * Q = m) ∧ ∃ m : ℤ, X.hi * Q = m) ∧
      ∀ X, Reach P (root P) X → ¬ Branching P X := by
  obtain ⟨-, -, hQ, -, -⟩ := checkF_facts hc
  have hQ' : (Q : ℚ) ≠ 0 := by positivity
  refine ⟨(((T.keys.map (gam P Q)).toFinset : Set FState).toFinite).subset fun X hX => ?_,
    fun X hX => ?_, fun X hX => not_branching_of_checkF hc hX⟩
  · obtain ⟨k, l, hk, rfl⟩ := reach_rep hc hX
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_coe]
    exact ⟨k, (LTree.find_spec hk).1, rfl⟩
  · obtain ⟨k, l, hk, rfl⟩ := reach_rep hc hX
    exact ⟨⟨k.2.1, by simp [gam, hQ']⟩, ⟨k.2.2, by simp [gam, hQ']⟩⟩

/-- **A passed check at `D = Q` gives a checked certificate.** -/
theorem exists_checked_of_checkF (hD : P.D = Q) : ∃ C, Checked P C := by
  obtain ⟨hP, -, -, -, -⟩ := checkF_facts hc
  obtain ⟨hfin, hgrid, hnb⟩ := checkF_sound hc
  exact exists_checked hP hfin (fun X hX => by rw [OnGrid, hD]; exact hgrid X hX) hnb

/-- **All four conditions of `T5iv` hold** for a cell passing the check. -/
theorem T5iv_of_checkF :
    ∃ hfin : {X | Reach P (root P) X}.Finite,
      (∃ D C, Checked { P with D := D } C) ∧ (∃ C, Checked { P with D := DF hfin } C) ∧
      (∀ X, Reach P (root P) X → ¬ Branching P X) ∧ PolyGrowth P := by
  obtain ⟨hP, -, -, -, -⟩ := checkF_facts hc
  obtain ⟨hfin, -, hnb⟩ := checkF_sound hc
  have h := T5iv hP hfin
  refine ⟨hfin, (h.out 1 3).2 hnb, (h.out 2 3).2 hnb, hnb, (h.out 4 3).2 hnb⟩

end Sound

end Check

end Follower

end DubC2.Gen
