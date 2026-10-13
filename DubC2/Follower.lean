/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.Branch
import Mathlib.Logic.Relation
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Tactic.TFAE
import Mathlib.Data.Set.Card

/-!
# The follower automaton: the sufficiency half of certificate completeness (T5(iv))

The **follower automaton** `F` of a cell (`DubC2/xfrontier.py`, note §§11–12 of
`plans/note-dubC2T-M0.html`) follows the set of all avoiding pseudo-orbits exactly: a state is a
residue set `R ⊆ ℤ/M` and an interval `[lo, hi) ⊆ [0, 1)`, and the letter `s` maps it to
`(q⁻¹(p·R + s) minus the residues ≡ 0 mod some l ∈ PM, f_s[lo, hi) ∩ [0, 1))`, with
`f_s(y) = (p·y − s − (p−q)·a/b)/q` (`DubC2.Gen.Branch.istep`); the state dies if either part
becomes empty or `s` is divisible by some `l ∈ Pq` (`DubC2.Gen.Follower.step`).  It does not
depend on the cell count `D`.  For `M = ∏ PM` (pairwise coprime) a residue set reachable from
the root is, by the Chinese remainder theorem, the product of one residue set per prime, so `F`
is the per-prime automaton of `xfrontier.py`.

A state is **branching** if two different letters lead from it to states from which it is
reachable again.  The necessity half of T5(iv) (`DubC2/Branch.lean`): a branching witness rules
out every certificate.  This file proves the **sufficiency half**:

> If `F` is finite and has no branching state reachable from the root, then a certificate is
> checked at every cell count `D` that is a common denominator of the interval endpoints of `F`
> (`DubC2.Gen.Follower.exists_checked`), in particular at their least common denominator `D_F`
> (`DubC2.Gen.Follower.exists_checked_DF`).

The certificate needs no peeling (`J = 0`, the core is every vertex).  Its det states are the
vertex sets `verts X = R × {cells c with [c/D, (c+1)/D) ⊆ [lo, hi)}` of the states `X` of `F`,
its transitions those of `F`, and its rank the number of states reachable from a state.  The
only geometric input is *soundness* (`succ_dead`, `succ_live`): the `s`-successors in the cell
graph of `verts X` lie in `verts (step X s)`, and there are none when `X` dies under `s`.  This
holds because on the grid `(1/D)ℤ` a cell meets the clipped image `f_s[lo, hi) ∩ [0, 1)` iff it
lies inside it.  A rank is kept exactly along an edge back into the strongly connected component,
so the `C_det` criterion "at most one rank-keeping letter per det state" is "no branching state".

## Main results

* `DubC2.Gen.Follower.checked_of_family` — a det family of over-approximating vertex sets with a
  rank satisfying the `C_det` criterion yields a checked certificate (no peeling);
* `DubC2.Gen.Follower.exists_checked` — **sufficiency** at every common denominator `D`;
* `DubC2.Gen.Follower.exists_checked_DF` — sufficiency at `D_F`;
* `DubC2.Gen.Follower.exists_branchOK` — a branching state of `F` yields a `BranchWitness`
  accepted by `branchOK`. Two loops `α, β` start with different letters. A loop permutes the
  state's residues (`exists_rep_fix`), so `A = α^k₁` and `B = β^k₂` fix them all. The
  witness is then `w₁ = AB`, `w₂ = BA`, a residue of the state, and the state's own interval,
  which every loop returns exactly;
* `DubC2.Gen.Follower.not_checked_of_branching` — necessity from `F` itself, at every `D`;
* `DubC2.Gen.Follower.checked_iff` — some `D` certifies ⟺ `D_F` certifies ⟺ no reachable
  state branches;
* `DubC2.Gen.Follower.polyGrowth_iff` — no reachable state branches ⟺ the admissible language
  `lang` grows polynomially (`PolyGrowth`). The language is the finite set `words`, since every
  live letter is in the alphabet (`letter_mem`). Two equal-length loops double the count per
  block. Without branching, at most `(nA+1)^N·(n+1)^N` words of length `n` exist, with `N`
  reachable states (`card_words_le`, by induction on the reachable-set rank);
* `DubC2.Gen.Follower.T5iv` — **T5(iv) for finite `F`**, all four conditions as a `TFAE`.

## References

* [Oda26] Y. Odagiri, *Finite graph certificates for composite terms in rational floor sequences*,
  Zenodo, doi:10.5281/zenodo.22997709 (2026).
-/

namespace DubC2.Gen

open Branch

/-! ## Bitmask lemmas -/

theorem testBit_of_mem_bitsScan : ∀ (fuel S i y : ℕ), y ∈ bitsScan fuel S i →
    i ≤ y ∧ S.testBit (y - i) = true
  | 0, S, i, y, h => by simp [bitsScan] at h
  | fuel + 1, S, i, y, h => by
    simp only [bitsScan] at h
    split_ifs at h with h0 h32 h2
    · simp at h
    · obtain ⟨h1, h2⟩ := testBit_of_mem_bitsScan fuel _ _ y h
      refine ⟨by omega, ?_⟩
      rw [Nat.testBit_shiftRight] at h2
      rwa [show 32 + (y - (i + 32)) = y - i by omega] at h2
    · rcases List.mem_cons.1 h with rfl | h
      · refine ⟨le_rfl, ?_⟩
        rw [Nat.sub_self, Nat.testBit_zero]
        simpa using h2
      · obtain ⟨h1, h3⟩ := testBit_of_mem_bitsScan fuel _ _ y h
        refine ⟨by omega, ?_⟩
        rw [Nat.testBit_div_two] at h3
        rwa [show y - (i + 1) + 1 = y - i by omega] at h3
    · obtain ⟨h1, h3⟩ := testBit_of_mem_bitsScan fuel _ _ y h
      refine ⟨by omega, ?_⟩
      rw [Nat.testBit_div_two] at h3
      rwa [show y - (i + 1) + 1 = y - i by omega] at h3

theorem testBit_of_mem_bits {S k : ℕ} (h : k ∈ bits S) : S.testBit k = true := by
  simpa using (testBit_of_mem_bitsScan S S 0 k h).2

namespace Follower

/-- The bitmask of a finite set of naturals. -/
noncomputable def enc (S : Finset ℕ) : ℕ := orFold S.toList (fun _ => true) (fun x => 2 ^ x)

theorem testBit_enc (S : Finset ℕ) (k : ℕ) : (enc S).testBit k = true ↔ k ∈ S := by
  rw [enc, testBit_orFold]
  simp [Nat.testBit_two_pow]

theorem length_le_one_of_nodup {l : List ℕ} (hl : l.Nodup) (h : ∀ a ∈ l, ∀ b ∈ l, a = b) :
    l.length ≤ 1 := by
  match l, hl, h with
  | [], _, _ => simp
  | [_], _, _ => simp
  | a :: b :: l, hl, h =>
    exact absurd (h a (by simp) b (by simp)) fun e => (List.nodup_cons.1 hl).1 (by simp [e])

/-! ## A det family is a certificate -/

section Family

variable {P : Params}

/-- **A det family yields a checked certificate.**  Vertex sets `V i` (`i < n`) with `V 0` every
vertex, transitions `δ` over-approximating the cell graph, and a rank non-increasing along `δ`
with at most one rank-keeping letter per state.  The certificate has no peeling rounds. -/
theorem checked_of_family (hP : checkParams P = true) (n : ℕ) (hn : 0 < n) (V : ℕ → Finset ℕ)
    (δ : ℕ → ℕ → Option ℕ) (rk : ℕ → ℕ)
    (hV : ∀ i < n, ∀ x ∈ V i, x < P.nV) (hV0 : ∀ x < P.nV, x ∈ V 0)
    (hnone : ∀ i < n, ∀ t < P.nA, δ i t = none → ∀ x ∈ V i, P.succList x (P.letter t) = [])
    (hsome : ∀ i < n, ∀ t < P.nA, ∀ j, δ i t = some j →
      j < n ∧ (∀ x ∈ V i, ∀ w ∈ P.succList x (P.letter t), w ∈ V j) ∧ rk j ≤ rk i)
    (hkeep : ∀ i < n, ∀ t₁ < P.nA, ∀ t₂ < P.nA, ∀ j₁ j₂, δ i t₁ = some j₁ → rk j₁ = rk i →
      δ i t₂ = some j₂ → rk j₂ = rk i → t₁ = t₂) :
    ∃ C, Checked P C := by
  have hF := paramFacts hP
  let C : Cert :=
    { J := 0, Z := P.nV, nB := 1, peels := [], imgs := [], core := List.range P.nV
      sets := (List.range n).map fun i => enc (V i)
      trans := (List.range n).map fun i => (List.range P.nA).map (δ i)
      rank := (List.range n).map rk }
  have hnV : 0 < P.nV := Nat.mul_pos hF.M0 hF.D0
  have hsets : ∀ i < n, C.sets.getD i 0 = enc (V i) := fun i hi => by
    simp [C, List.getD_eq_getElem?_getD, hi]
  have hslen : C.sets.length = n := by simp [C]
  have htrans : ∀ i < n, ∀ t < P.nA, (C.trans.getD i []).getD t none = δ i t := fun i hi t ht => by
    simp [C, List.getD_eq_getElem?_getD, hi, ht]
  have hrank : ∀ i < n, C.rank.getD i 0 = rk i := fun i hi => by
    simp [C, List.getD_eq_getElem?_getD, hi]
  have hcore : ∀ x < P.nV, C.core.getD x 0 = x := fun x hx => by
    simp [C, List.getD_eq_getElem?_getD, hx]
  -- a bit of a det successor set is a cell-graph successor of a member
  have hdet : ∀ i < n, ∀ s k, (detSucc P C (enc (V i)) s).testBit k = true →
      ∃ x ∈ V i, k ∈ P.succList x s := by
    intro i hi s k hk
    rw [detSucc, testBit_orFold] at hk
    obtain ⟨x, hx, -, hb⟩ := hk
    have hxV : x ∈ V i := (testBit_enc _ _).1 (testBit_of_mem_bits hx)
    rw [hcore x (hV i hi x hxV), Params.succIdx, testBit_orFold] at hb
    obtain ⟨w, hw, hwc, hb⟩ := hb
    rw [Nat.testBit_two_pow, decide_eq_true_eq] at hb
    have hwc' : w ∈ C.core := List.contains_iff_mem.1 hwc
    have hidx : C.core.idxOf w = w := by
      have h1 := getD_idxOf hwc'
      have h2 : C.core.idxOf w < P.nV := by
        have := List.idxOf_lt_length_of_mem hwc'
        simpa [C] using this
      rw [hcore _ h2] at h1
      exact h1
    refine ⟨x, hxV, ?_⟩
    rw [← hb, hidx]
    exact hw
  refine ⟨C, ⟨?_, ?_, ?_⟩⟩
  · -- the head
    simp only [checkHead, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
    refine ⟨⟨⟨⟨⟨hP, by rw [hslen]; exact hn⟩, hnV⟩, by simp [C]⟩, ?_⟩, ?_⟩
    · intro i _
      simp only [coreOK, List.all_eq_true]
      intro t _
      simp [C, Cert.memA]
    · rw [hsets 0 hn]
      refine subset_of_testBit fun k hk => ?_
      rw [Nat.testBit_two_pow_sub_one, decide_eq_true_eq] at hk
      exact (testBit_enc _ _).2 (hV0 k (by simpa [C] using hk))
  · -- no peeling rounds
    simp [C]
  · -- the det rows
    rw [List.all_eq_true]
    intro i hi
    rw [List.mem_range'_1, hslen] at hi
    have hi : i < n := by omega
    simp only [detOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq]
    refine ⟨fun t ht => ?_, ?_⟩
    · rw [htrans i hi t ht, hsets i hi]
      cases hδ : δ i t with
      | none =>
        simp only [beq_iff_eq]
        refine eq_zero_of_testBit fun k => ?_
        by_contra hk
        obtain ⟨x, hx, hkx⟩ := hdet i hi _ k (by simpa using hk)
        rw [hnone i hi t ht hδ x hx] at hkx
        simp at hkx
      | some j =>
        obtain ⟨hj, hsub, hrk⟩ := hsome i hi t ht j hδ
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨⟨by rw [hslen]; exact hj, ?_⟩, by rw [hrank j hj, hrank i hi]; exact hrk⟩
        rw [hsets j hj]
        refine subset_of_testBit fun k hk => ?_
        obtain ⟨x, hx, hkx⟩ := hdet i hi _ k hk
        exact (testBit_enc _ _).2 (hsub x hx k hkx)
    · -- at most one rank-keeping letter
      have hmem : ∀ t ∈ keep C P.nA i, t < P.nA ∧ ∃ j, δ i t = some j ∧ rk j = rk i := by
        intro t ht
        simp only [keep, List.mem_filter, List.mem_range] at ht
        obtain ⟨ht, hk⟩ := ht
        rw [htrans i hi t ht] at hk
        refine ⟨ht, ?_⟩
        cases hδ : δ i t with
        | none => rw [hδ] at hk; simp at hk
        | some j =>
          rw [hδ] at hk
          have hj := (hsome i hi t ht j hδ).1
          simp only [beq_iff_eq, hrank j hj, hrank i hi] at hk
          exact ⟨j, rfl, hk⟩
      refine length_le_one_of_nodup ((List.nodup_range).filter _) fun t₁ h₁ t₂ h₂ => ?_
      obtain ⟨ht₁, j₁, hδ₁, hr₁⟩ := hmem t₁ h₁
      obtain ⟨ht₂, j₂, hδ₂, hr₂⟩ := hmem t₂ h₂
      exact hkeep i hi t₁ ht₁ t₂ ht₂ j₁ j₂ hδ₁ hr₁ hδ₂ hr₂

end Family

/-! ## The follower automaton -/

/-- A follower state: a residue set mod `M` and an interval `[lo, hi)`. -/
structure FState where
  R : Finset ℕ
  lo : ℚ
  hi : ℚ
  deriving DecidableEq

variable (P : Params)

/-- The residue `r` survives the letter `s`: neither `r` nor its successor is `≡ 0 mod l ∈ PM`. -/
def rOK (r : ℕ) (s : ℤ) : Bool :=
  (P.PM.all fun l => r % l != 0) && (P.PM.all fun l => P.rnext r s % l != 0)

/-- The letter `s` is prime to every `l ∈ Pq`. -/
def sOK (s : ℤ) : Bool := P.Pq.all fun l => s % (l : ℤ) != 0

/-- The residue part of a follower step. -/
def rstep (R : Finset ℕ) (s : ℤ) : Finset ℕ :=
  (R.filter fun r => rOK P r s = true).image fun r => P.rnext r s

/-- The interval part of a follower step: `f_s[lo, hi) ∩ [0, 1)`. -/
def istepX (X : FState) (s : ℤ) : ℚ × ℚ := istep P.p P.q P.a P.b (X.lo, X.hi) s

/-- **One follower step**; `none` if the state dies. -/
def step (X : FState) (s : ℤ) : Option FState :=
  if sOK P s = true ∧ (rstep P X.R s).Nonempty ∧ (istepX P X s).1 < (istepX P X s).2 then
    some ⟨rstep P X.R s, (istepX P X s).1, (istepX P X s).2⟩
  else none

/-- An edge of the follower automaton. -/
def Edge (X Y : FState) : Prop := ∃ s, step P X s = some Y

/-- Reachability in the follower automaton. -/
abbrev Reach : FState → FState → Prop := Relation.ReflTransGen (Edge P)

/-- The root: every residue, the whole interval `[0, 1)`. -/
def root : FState := ⟨Finset.range P.M, 0, 1⟩

/-- A **branching state**: two different letters lead to states from which it is reachable. -/
def Branching (X : FState) : Prop :=
  ∃ s₁ s₂ Y₁ Y₂, s₁ ≠ s₂ ∧ step P X s₁ = some Y₁ ∧ step P X s₂ = some Y₂ ∧
    Reach P Y₁ X ∧ Reach P Y₂ X

/-- Both interval endpoints of `X` lie on the grid `(1/D)ℤ`. -/
def OnGrid (X : FState) : Prop := (∃ m : ℤ, X.lo * P.D = m) ∧ ∃ m : ℤ, X.hi * P.D = m

/-- The cells `c < D` with `[c/D, (c+1)/D) ⊆ [lo, hi)`. -/
def cells (X : FState) : Finset ℕ :=
  (Finset.range P.D).filter fun c => X.lo ≤ (c : ℚ) / P.D ∧ ((c : ℚ) + 1) / P.D ≤ X.hi

/-- The vertex set of a follower state. -/
def verts (X : FState) : Finset ℕ :=
  ((X.R.filter (· < P.M)) ×ˢ cells P X).image fun rc => rc.1 * P.D + rc.2

/-! ## Soundness of the follower step -/

variable {P}

theorem mem_succList {k w : ℕ} {s : ℤ} (h : w ∈ P.succList k s) :
    (P.PM.all fun l => k / P.D % l != 0) = true ∧ sOK P s = true ∧
      (P.PM.all fun l => P.rnext (k / P.D) s % l != 0) = true ∧
      ∃ c₂, c₂ < P.D ∧ (P.q : ℤ) * P.b * c₂ < P.hi (k % P.D) s ∧
        P.lo (k % P.D) s < (P.q : ℤ) * P.b * (c₂ + 1) ∧ w = P.rnext (k / P.D) s * P.D + c₂ := by
  unfold Params.succList at h
  split_ifs at h with hc
  · simp only [Bool.and_eq_true] at hc
    simp only [List.mem_map, List.mem_filter, List.mem_range'_1, Bool.and_eq_true,
      decide_eq_true_eq] at h
    obtain ⟨c₂, ⟨⟨h1, h2⟩, h3, h4⟩, rfl⟩ := h
    have : P.cHi (k % P.D) s ≤ P.D := min_le_left _ _
    exact ⟨hc.1.1, hc.1.2, hc.2, c₂, by omega, h3, h4, rfl⟩
  · simp at h

/-- **The interval arithmetic of one edge.**  If the cell `c` lies in `[lo, hi)` and the cell
graph has an edge `c → c₂` by the letter `s`, then the clipped image `f_s[lo, hi) ∩ [0, 1)` is
nonempty and meets the cell `c₂`. -/
theorem edge_interval (hF : ParamFacts P) {c c₂ : ℕ} {s : ℤ} (hc₂ : c₂ < P.D)
    (h1 : (P.q : ℤ) * P.b * c₂ < P.hi c s) (h2 : P.lo c s < (P.q : ℤ) * P.b * (c₂ + 1))
    {lo hi : ℚ} (hlo : lo ≤ (c : ℚ) / P.D) (hhi : ((c : ℚ) + 1) / P.D ≤ hi) :
    (istep P.p P.q P.a P.b (lo, hi) s).1 < (istep P.p P.q P.a P.b (lo, hi) s).2 ∧
      (istep P.p P.q P.a P.b (lo, hi) s).1 < ((c₂ : ℚ) + 1) / P.D ∧
      (c₂ : ℚ) / P.D < (istep P.p P.q P.a P.b (lo, hi) s).2 := by
  have hp : (0 : ℚ) < P.p := by exact_mod_cast (by have := hF.pq; omega : 0 < P.p)
  have hq : (0 : ℚ) < P.q := by exact_mod_cast (by have := hF.q1; omega : 0 < P.q)
  have hb : (0 : ℚ) < P.b := by exact_mod_cast hF.b0
  have hD : (0 : ℚ) < P.D := by exact_mod_cast hF.D0
  have e1 : fw P.p P.q P.a P.b s (((c : ℚ) + 1) / P.D) - (c₂ : ℚ) / P.D =
      ((P.hi c s - (P.q : ℤ) * P.b * c₂ : ℤ) : ℚ) / (P.q * P.b * P.D) := by
    simp only [fw, Params.hi, Params.shiftK]
    push_cast
    field_simp
    ring
  have e2 : ((c₂ : ℚ) + 1) / P.D - fw P.p P.q P.a P.b s ((c : ℚ) / P.D) =
      (((P.q : ℤ) * P.b * (c₂ + 1) - P.lo c s : ℤ) : ℚ) / (P.q * P.b * P.D) := by
    simp only [fw, Params.lo, Params.shiftK]
    push_cast
    field_simp
    ring
  have hA : (c₂ : ℚ) / P.D < fw P.p P.q P.a P.b s (((c : ℚ) + 1) / P.D) := by
    have : (0 : ℚ) < ((P.hi c s - (P.q : ℤ) * P.b * c₂ : ℤ) : ℚ) / (P.q * P.b * P.D) :=
      div_pos (by exact_mod_cast sub_pos.2 h1) (by positivity)
    linarith
  have hB : fw P.p P.q P.a P.b s ((c : ℚ) / P.D) < ((c₂ : ℚ) + 1) / P.D := by
    have : (0 : ℚ) < (((P.q : ℤ) * P.b * (c₂ + 1) - P.lo c s : ℤ) : ℚ) / (P.q * P.b * P.D) :=
      div_pos (by exact_mod_cast sub_pos.2 h2) (by positivity)
    linarith
  have m1 := fw_le (a := P.a) (b := P.b) hp.le hq s hlo
  have m2 := fw_le (a := P.a) (b := P.b) hp.le hq s hhi
  have m3 := fw_lt (a := P.a) (b := P.b) hp hq s
    (show (c : ℚ) / P.D < ((c : ℚ) + 1) / P.D from div_lt_div_of_pos_right (by linarith) hD)
  have c0 : (0 : ℚ) ≤ (c₂ : ℚ) / P.D := by positivity
  have c1 : (c₂ : ℚ) / P.D < 1 := (div_lt_one hD).2 (by exact_mod_cast hc₂)
  have c2 : ((c₂ : ℚ) + 1) / P.D ≤ 1 := (div_le_one hD).2 (by exact_mod_cast hc₂)
  simp only [istep]
  refine ⟨max_lt (lt_min one_pos (by linarith)) (lt_min (by linarith) (by linarith)),
    max_lt (by positivity) (by linarith), lt_min c1 (by linarith)⟩

theorem mem_verts {X : FState} {x : ℕ} (hx : x ∈ verts P X) (hD : 0 < P.D) :
    x / P.D ∈ X.R ∧ x / P.D < P.M ∧ x % P.D ∈ cells P X := by
  simp only [verts, Finset.mem_image, Finset.mem_product, Finset.mem_filter] at hx
  obtain ⟨⟨r, c⟩, ⟨⟨hr, hrM⟩, hc⟩, rfl⟩ := hx
  have hcD : c < P.D := Finset.mem_range.1 (Finset.mem_filter.1 hc).1
  have hdiv : (r * P.D + c) / P.D = r := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hD, Nat.div_eq_of_lt hcD, zero_add]
  have hmod : (r * P.D + c) % P.D = c := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hcD]
  rw [hdiv, hmod]
  exact ⟨hr, hrM, hc⟩

/-- **A dead follower step has no successors in the cell graph.** -/
theorem succ_dead (hF : ParamFacts P) {X : FState} {s : ℤ} (hX : step P X s = none) {x : ℕ}
    (hx : x ∈ verts P X) : P.succList x s = [] := by
  by_contra hne
  obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨hr0, hs, hr1, c₂, hc₂, h1, h2, -⟩ := mem_succList hw
  obtain ⟨hrR, -, hc⟩ := mem_verts hx hF.D0
  simp only [cells, Finset.mem_filter] at hc
  have hI := (edge_interval hF hc₂ h1 h2 hc.2.1 hc.2.2).1
  have hne : (rstep P X.R s).Nonempty :=
    ⟨_, Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hrR, by simp [rOK, hr0, hr1]⟩)⟩
  unfold step at hX
  split_ifs at hX with h
  exact h ⟨hs, hne, hI⟩

theorem grid_lo {lo : ℚ} {D c : ℕ} (hD : (0 : ℚ) < D) (hg : ∃ m : ℤ, lo * D = m)
    (h : lo < ((c : ℚ) + 1) / D) : lo ≤ (c : ℚ) / D := by
  obtain ⟨m, hm⟩ := hg
  rw [lt_div_iff₀ hD, hm] at h
  have h' : m < (c : ℤ) + 1 := by exact_mod_cast h
  rw [le_div_iff₀ hD, hm]
  exact_mod_cast (by omega : m ≤ (c : ℤ))

theorem grid_hi {hi : ℚ} {D c : ℕ} (hD : (0 : ℚ) < D) (hg : ∃ m : ℤ, hi * D = m)
    (h : (c : ℚ) / D < hi) : ((c : ℚ) + 1) / D ≤ hi := by
  obtain ⟨m, hm⟩ := hg
  rw [div_lt_iff₀ hD, hm] at h
  have h' : (c : ℤ) < m := by exact_mod_cast h
  rw [div_le_iff₀ hD, hm]
  exact_mod_cast (by omega : (c : ℤ) + 1 ≤ m)

/-- **A live follower step over-approximates the cell graph** when its target is on the grid. -/
theorem succ_live (hF : ParamFacts P) {X Y : FState} {s : ℤ} (hX : step P X s = some Y)
    (hY : OnGrid P Y) {x w : ℕ} (hx : x ∈ verts P X) (hw : w ∈ P.succList x s) :
    w ∈ verts P Y := by
  unfold step at hX
  split_ifs at hX with hc
  cases hX
  obtain ⟨hr0, hs, hr1, c₂, hc₂, h1, h2, rfl⟩ := mem_succList hw
  obtain ⟨hrR, -, hcX⟩ := mem_verts hx hF.D0
  simp only [cells, Finset.mem_filter] at hcX
  have hI := edge_interval hF hc₂ h1 h2 hcX.2.1 hcX.2.2
  have hD : (0 : ℚ) < P.D := by exact_mod_cast hF.D0
  have hrM : P.rnext (x / P.D) s < P.M := by
    have hM : (0 : ℤ) < P.M := by exact_mod_cast hF.M0
    have := Int.emod_lt_of_pos (((P.p : ℤ) * (x / P.D : ℕ) + s) * P.qinv) hM
    have h0 := Int.emod_nonneg (((P.p : ℤ) * (x / P.D : ℕ) + s) * P.qinv) hM.ne'
    simp only [Params.rnext]
    omega
  simp only [verts, Finset.mem_image, Finset.mem_product, Finset.mem_filter]
  refine ⟨(P.rnext (x / P.D) s, c₂), ⟨⟨Finset.mem_image_of_mem _ (Finset.mem_filter.2
    ⟨hrR, by simp [rOK, hr0, hr1]⟩), hrM⟩, ?_⟩, rfl⟩
  simp only [cells, Finset.mem_filter, Finset.mem_range]
  exact ⟨hc₂, grid_lo hD hY.1 hI.2.1, grid_hi hD hY.2 hI.2.2⟩

/-! ## Sufficiency -/

/-- **T5(iv), sufficiency.**  If the follower automaton is finite, all its interval endpoints lie
on `(1/D)ℤ`, and no reachable state is branching, then a certificate is checked at `D`. -/
@[category research solved, AMS 11 37, ref "Oda26", group "dubc2_obstruction"]
theorem exists_checked (hP : checkParams P = true) (hfin : {X | Reach P (root P) X}.Finite)
    (hgrid : ∀ X, Reach P (root P) X → OnGrid P X)
    (hnb : ∀ X, Reach P (root P) X → ¬ Branching P X) :
    ∃ C, Checked P C := by
  classical
  have hF := paramFacts hP
  set S := hfin.toFinset with hS
  set L : List FState := root P :: (S.erase (root P)).toList with hL
  have hmemL : ∀ X, Reach P (root P) X → X ∈ L := by
    intro X hX
    by_cases h : X = root P
    · simp [L, h]
    · simp [L, S, h, hX]
  have hLreach : ∀ X ∈ L, Reach P (root P) X := by
    intro X hX
    simp only [L, List.mem_cons, Finset.mem_toList, Finset.mem_erase, S,
      Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hX
    rcases hX with rfl | ⟨-, h⟩
    · exact Relation.ReflTransGen.refl
    · exact h
  set n := L.length with hn
  let X : ℕ → FState := fun i => L.getD i (root P)
  have hXmem : ∀ i < n, X i ∈ L := fun i hi => by
    simp only [X, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact List.getElem_mem hi
  have hXreach : ∀ i < n, Reach P (root P) (X i) := fun i hi => hLreach _ (hXmem i hi)
  have hidx : ∀ Y ∈ L, L.idxOf Y < n ∧ X (L.idxOf Y) = Y := fun Y hY => by
    refine ⟨List.idxOf_lt_length_of_mem hY, ?_⟩
    simp only [X, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hY), Option.getD_some,
      List.getElem_idxOf]
  let δ : ℕ → ℕ → Option ℕ := fun i t => (step P (X i) (P.letter t)).map L.idxOf
  let reachSet : ℕ → Finset ℕ := fun i => (Finset.range n).filter fun j => Reach P (X i) (X j)
  let rk : ℕ → ℕ := fun i => (reachSet i).card
  -- an edge shrinks the reachable set
  have hsub : ∀ i < n, ∀ t j, δ i t = some j → j < n ∧ reachSet j ⊆ reachSet i ∧
      ∃ Y, step P (X i) (P.letter t) = some Y ∧ X j = Y := by
    intro i hi t j hj
    obtain ⟨Y, hY, rfl⟩ := Option.map_eq_some_iff.1 hj
    have hYL := hmemL Y ((hXreach i hi).tail ⟨_, hY⟩)
    obtain ⟨hj, hXj⟩ := hidx Y hYL
    refine ⟨hj, fun k hk => ?_, Y, hY, hXj⟩
    simp only [reachSet, Finset.mem_filter] at hk ⊢
    rw [hXj] at hk
    exact ⟨hk.1, Relation.ReflTransGen.head ⟨_, hY⟩ hk.2⟩
  refine checked_of_family hP n (by simp [n, L]) (fun i => verts P (X i)) δ rk ?_ ?_ ?_ ?_ ?_
  · -- vertices are vertices
    intro i _ x hx
    simp only [verts, Finset.mem_image, Finset.mem_product, Finset.mem_filter, cells,
      Finset.mem_range] at hx
    obtain ⟨⟨r, c⟩, ⟨⟨-, hrM⟩, hc, -⟩, rfl⟩ := hx
    calc r * P.D + c < r * P.D + P.D := by omega
      _ = (r + 1) * P.D := by ring
      _ ≤ P.M * P.D := Nat.mul_le_mul_right _ hrM
  · -- state `0` is the root, every vertex
    intro x hx
    have hX0 : X 0 = root P := by simp [X, L]
    simp only [hX0, verts, root, Finset.mem_image, Finset.mem_product, Finset.mem_filter,
      Finset.mem_range, cells]
    have hD : (0 : ℚ) < P.D := by exact_mod_cast hF.D0
    have hxM : x / P.D < P.M := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hx)
    have hc : x % P.D < P.D := Nat.mod_lt _ hF.D0
    refine ⟨(x / P.D, x % P.D), ⟨⟨hxM, hxM⟩, hc, by positivity, ?_⟩, Nat.div_add_mod' x P.D⟩
    exact (div_le_one hD).2 (by exact_mod_cast hc)
  · -- dead transitions
    intro i _ t _ hδ x hx
    exact succ_dead hF (Option.map_eq_none_iff.1 hδ) hx
  · -- live transitions
    intro i hi t _ j hδ
    obtain ⟨hj, hss, Y, hY, hXj⟩ := hsub i hi t j hδ
    refine ⟨hj, fun x hx w hw => ?_, Finset.card_le_card hss⟩
    rw [hXj]
    exact succ_live hF hY (hgrid Y ((hXreach i hi).tail ⟨_, hY⟩)) hx hw
  · -- the keep condition is "no branching"
    intro i hi t₁ _ t₂ _ j₁ j₂ hδ₁ hr₁ hδ₂ hr₂
    have back : ∀ t j, δ i t = some j → rk j = rk i →
        ∃ Y, step P (X i) (P.letter t) = some Y ∧ Reach P Y (X i) := by
      intro t j hδ hr
      obtain ⟨hj, hss, Y, hY, hXj⟩ := hsub i hi t j hδ
      have heq : reachSet j = reachSet i := Finset.eq_of_subset_of_card_le hss (le_of_eq hr.symm)
      have hii : i ∈ reachSet j := by
        rw [heq]
        simp only [reachSet, Finset.mem_filter, Finset.mem_range]
        exact ⟨hi, Relation.ReflTransGen.refl⟩
      simp only [reachSet, Finset.mem_filter] at hii
      exact ⟨Y, hY, hXj ▸ hii.2⟩
    obtain ⟨Y₁, hY₁, hb₁⟩ := back t₁ j₁ hδ₁ hr₁
    obtain ⟨Y₂, hY₂, hb₂⟩ := back t₂ j₂ hδ₂ hr₂
    by_contra hne
    refine hnb (X i) (hXreach i hi) ⟨_, _, Y₁, Y₂, ?_, hY₁, hY₂, hb₁, hb₂⟩
    simp only [Params.letter, ne_eq, add_right_inj, Nat.cast_inj]
    exact hne

/-- The least common denominator `D_F` of the interval endpoints of a finite follower
automaton. -/
noncomputable def DF (hfin : {X | Reach P (root P) X}.Finite) : ℕ :=
  hfin.toFinset.lcm fun X => Nat.lcm X.lo.den X.hi.den

theorem DF_pos (hfin : {X | Reach P (root P) X}.Finite) : 0 < DF hfin := by
  refine Nat.pos_of_ne_zero fun h => ?_
  rw [DF, Finset.lcm_eq_zero_iff] at h
  obtain ⟨X, -, hX⟩ := h
  exact Nat.lcm_ne_zero X.lo.den_nz X.hi.den_nz hX

theorem onGrid_DF (hfin : {X | Reach P (root P) X}.Finite) {X : FState}
    (hX : Reach P (root P) X) : OnGrid { P with D := DF hfin } X := by
  have hdvd : Nat.lcm X.lo.den X.hi.den ∣ DF hfin :=
    Finset.dvd_lcm (hfin.mem_toFinset.2 hX)
  obtain ⟨k₁, hk₁⟩ := (Nat.dvd_lcm_left X.lo.den X.hi.den).trans hdvd
  obtain ⟨k₂, hk₂⟩ := (Nat.dvd_lcm_right X.lo.den X.hi.den).trans hdvd
  refine ⟨⟨X.lo.num * k₁, ?_⟩, ⟨X.hi.num * k₂, ?_⟩⟩
  · simp only
    rw [hk₁]
    push_cast
    rw [← mul_assoc, Rat.mul_den_eq_num]
  · simp only
    rw [hk₂]
    push_cast
    rw [← mul_assoc, Rat.mul_den_eq_num]

/-- **T5(iv), sufficiency at `D_F`.**  A finite follower automaton without reachable branching
state is certified at the least common denominator of its interval endpoints (which does not
depend on the cell count `D` of `P`). -/
@[category research solved, AMS 11 37, ref "Oda26", group "dubc2_obstruction"]
theorem exists_checked_DF (hP : checkParams P = true) (hfin : {X | Reach P (root P) X}.Finite)
    (hnb : ∀ X, Reach P (root P) X → ¬ Branching P X) :
    ∃ C, Checked { P with D := DF hfin } C := by
  have hP' : checkParams { P with D := DF hfin } = true := by
    have h := hP
    simp only [checkParams, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, DF_pos hfin⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩
  exact exists_checked hP' hfin (fun X hX => onGrid_DF hfin hX) hnb

/-! ## Necessity: a branching state yields a branching witness -/

section Witness

open Horse

/-- The residue walk mod `M` along a word; `none` once a residue or its successor is `≡ 0`. -/
def rpath (P : Params) (r : ℕ) : List ℤ → Option ℕ
  | [] => some r
  | s :: u => if rOK P r s = true then rpath P (P.rnext r s) u else none

/-- The follower state after a word. -/
def stepw (P : Params) (X : FState) : List ℤ → Option FState
  | [] => some X
  | s :: u => (step P X s).bind fun Y => stepw P Y u

/-- The `k`-th power of a word. -/
def rep (k : ℕ) (α : List ℤ) : List ℤ := (List.replicate k α).flatten

theorem rep_succ (k : ℕ) (α : List ℤ) : rep (k + 1) α = α ++ rep k α := by
  simp [rep, List.replicate_succ]

theorem stepw_append (X : FState) (u v : List ℤ) :
    stepw P X (u ++ v) = (stepw P X u).bind fun Y => stepw P Y v := by
  induction u generalizing X with
  | nil => simp [stepw]
  | cons s u ih =>
    simp only [List.cons_append, stepw]
    cases step P X s <;> simp [ih]

theorem rpath_append (r : ℕ) (u v : List ℤ) :
    rpath P r (u ++ v) = (rpath P r u).bind fun r' => rpath P r' v := by
  induction u generalizing r with
  | nil => simp [rpath]
  | cons s u ih =>
    simp only [List.cons_append, rpath]
    split_ifs <;> simp [ih]

theorem step_facts {X Y : FState} {s : ℤ} (h : step P X s = some Y) :
    sOK P s = true ∧ Y.R = rstep P X.R s ∧ (Y.lo, Y.hi) = istep P.p P.q P.a P.b (X.lo, X.hi) s ∧
      0 ≤ Y.lo ∧ Y.lo < Y.hi ∧ Y.hi ≤ 1 := by
  unfold step at h
  split_ifs at h with hc
  cases h
  exact ⟨hc.1, rfl, rfl, le_max_left _ _, hc.2.2, min_le_left _ _⟩

theorem stepw_interval : ∀ (u : List ℤ) {X Y : FState}, stepw P X u = some Y →
    ifold P.p P.q P.a P.b u (X.lo, X.hi) = (Y.lo, Y.hi)
  | [], X, Y, h => by simp only [stepw, Option.some.injEq] at h; subst h; rfl
  | s :: u, X, Y, h => by
    simp only [stepw, Option.bind_eq_some_iff] at h
    obtain ⟨Z, hZ, hu⟩ := h
    show ifold P.p P.q P.a P.b u (istep P.p P.q P.a P.b (X.lo, X.hi) s) = _
    rw [← (step_facts hZ).2.2.1]
    exact stepw_interval u hu

theorem stepw_bounds : ∀ (u : List ℤ) {X Y : FState}, u ≠ [] → stepw P X u = some Y →
    0 ≤ Y.lo ∧ Y.lo < Y.hi ∧ Y.hi ≤ 1
  | [], _, _, h, _ => absurd rfl h
  | s :: u, X, Y, _, h => by
    simp only [stepw, Option.bind_eq_some_iff] at h
    obtain ⟨Z, hZ, hu⟩ := h
    by_cases hu0 : u = []
    · subst hu0
      simp only [stepw, Option.some.injEq] at hu
      subst hu
      exact (step_facts hZ).2.2.2
    · exact stepw_bounds u hu0 hu

theorem stepw_sOK : ∀ (u : List ℤ) {X Y : FState}, stepw P X u = some Y → ∀ s ∈ u, sOK P s = true
  | [], _, _, _, s, hs => by simp at hs
  | t :: u, X, Y, h, s, hs => by
    simp only [stepw, Option.bind_eq_some_iff] at h
    obtain ⟨Z, hZ, hu⟩ := h
    rcases List.mem_cons.1 hs with rfl | hs
    · exact (step_facts hZ).1
    · exact stepw_sOK u hu s hs

theorem stepw_pre : ∀ (u : List ℤ) {X Y : FState} {r' : ℕ}, stepw P X u = some Y → r' ∈ Y.R →
    ∃ r ∈ X.R, rpath P r u = some r'
  | [], X, Y, r', h, hr' => by
    simp only [stepw, Option.some.injEq] at h
    subst h
    exact ⟨r', hr', rfl⟩
  | s :: u, X, Y, r', h, hr' => by
    simp only [stepw, Option.bind_eq_some_iff] at h
    obtain ⟨Z, hZ, hu⟩ := h
    obtain ⟨z, hz, hzr⟩ := stepw_pre u hu hr'
    rw [(step_facts hZ).2.1, rstep, Finset.mem_image] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    rw [Finset.mem_filter] at hr
    exact ⟨r, hr.1, by simp only [rpath, hr.2, ite_true]; exact hzr⟩

theorem stepw_of_reach {Y X : FState} (h : Reach P Y X) : ∃ u, stepw P Y u = some X := by
  induction h with
  | refl => exact ⟨[], rfl⟩
  | tail _ hbc ih =>
    obtain ⟨u, hu⟩ := ih
    obtain ⟨s, hs⟩ := hbc
    exact ⟨u ++ [s], by rw [stepw_append, hu]; simp [stepw, hs]⟩

theorem stepw_rep {X : FState} {α : List ℤ} (hα : stepw P X α = some X) :
    ∀ k, stepw P X (rep k α) = some X
  | 0 => by simp [rep, stepw]
  | k + 1 => by rw [rep_succ, stepw_append, hα]; exact stepw_rep hα k

/-- **A loop permutes the residues**, so a power of it fixes every residue of the state. -/
theorem exists_rep_fix {X : FState} {α : List ℤ} (hα : stepw P X α = some X) :
    ∃ k, 0 < k ∧ ∀ r ∈ X.R, rpath P r (rep k α) = some r := by
  classical
  have hp : ∀ y : X.R, ∃ x : X.R, rpath P x.1 α = some y.1 := fun y => by
    obtain ⟨r, hr, h⟩ := stepw_pre α hα y.2
    exact ⟨⟨r, hr⟩, h⟩
  choose g hg using hp
  have hinj : Function.Injective g := fun y₁ y₂ h => by
    have h1 := hg y₁
    have h2 := hg y₂
    rw [h, h2] at h1
    exact Subtype.ext (Option.some_injective _ h1).symm
  set σ : Equiv.Perm X.R := Equiv.ofBijective g (Finite.injective_iff_bijective.1 hinj)
  have hσ : ∀ k (x : X.R), rpath P ((σ ^ k) x).1 (rep k α) = some x.1 := by
    intro k
    induction k with
    | zero => intro x; simp [rep, rpath]
    | succ k ih =>
      intro x
      rw [pow_succ', Equiv.Perm.mul_apply, rep_succ, rpath_append,
        show σ ((σ ^ k) x) = g ((σ ^ k) x) from rfl, hg]
      exact ih x
  refine ⟨Fintype.card (Equiv.Perm X.R), Fintype.card_pos, fun r hr => ?_⟩
  have := hσ (Fintype.card (Equiv.Perm X.R)) ⟨r, hr⟩
  rwa [pow_card_eq_one, Equiv.Perm.one_apply] at this

theorem stepMod_lt {p l inv r : ℕ} (hl : 0 < l) (s : ℤ) : stepMod p l inv r s < l := by
  have hl' : (0 : ℤ) < l := by exact_mod_cast hl
  have h1 := Int.emod_nonneg (((p : ℤ) * r + s) * inv) hl'.ne'
  have h2 := Int.emod_lt_of_pos (((p : ℤ) * r + s) * inv) hl'
  simp only [stepMod]
  omega

/-- The candidate inverse `invMod q l` is an inverse of `q` mod every divisor `l ≥ 2` of `M`. -/
theorem invMod_spec (hF : ParamFacts P) {l : ℕ} (hl2 : 2 ≤ l) (hlM : l ∣ P.M) :
    P.q * invMod P.q l % l = 1 := by
  have h1 : P.q * (P.qinv % l) % l = 1 := by
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.mod_mod_of_dvd _ hlM, hF.inv,
      Nat.mod_mod_of_dvd _ hlM, Nat.one_mod_eq_one.2 (by omega)]
  unfold invMod
  cases hf : (List.range l).find? (fun i => P.q * i % l == 1) with
  | none =>
    have := List.find?_eq_none.1 hf (P.qinv % l) (List.mem_range.2 (Nat.mod_lt _ (by omega)))
    simp [h1] at this
  | some i =>
    have := List.find?_some hf
    simpa using this

/-- The residue walk mod `M` read mod a prime `l ∈ PM` is the witness walk `walk`. -/
theorem walk_of_rpath (hF : ParamFacts P) {l : ℕ} (hl : l ∈ P.PM) (hl2 : 2 ≤ l) :
    ∀ (w : List ℤ) (r r' : ℕ), rpath P r w = some r' →
      walk P.p l (invMod P.q l) (r % l) w w.length = r' % l ∧
        ∀ i < w.length, walk P.p l (invMod P.q l) (r % l) w i ≠ 0 := by
  have hlM : l ∣ P.M := Nat.dvd_of_mod_eq_zero (hF.PM l hl)
  have hinv := invMod_spec hF hl2 hlM
  have hstep : ∀ r s, stepMod P.p l (invMod P.q l) (r % l) s = P.rnext r s % l := by
    intro r s
    have h := rnext_modEq hF hl2 (by exact_mod_cast hlM) hinv (x := r) (ρ := r % l) s
      (by rw [Int.ModEq]; push_cast; rw [Int.emod_emod])
    have hlt := stepMod_lt (p := P.p) (l := l) (inv := invMod P.q l) (r := r % l) (by omega) s
    have : ((P.rnext r s % l : ℕ) : ℤ) = (stepMod P.p l (invMod P.q l) (r % l) s : ℕ) := by
      push_cast
      rw [h, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hlt)]
    exact_mod_cast this.symm
  intro w
  induction w with
  | nil =>
    intro r r' h
    simp only [rpath, Option.some.injEq] at h
    subst h
    simp [walk]
  | cons s u ih =>
    intro r r' h
    simp only [rpath] at h
    split_ifs at h with hok
    have hr0 : r % l ≠ 0 := by
      simp only [rOK, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at hok
      exact hok.1 l hl
    have hwalk : ∀ i, walk P.p l (invMod P.q l) (r % l) (s :: u) (i + 1) =
        walk P.p l (invMod P.q l) (P.rnext r s % l) u i := by
      intro i
      simp only [walk, List.take_succ_cons, List.foldl_cons, hstep]
    obtain ⟨h1, h2⟩ := ih _ _ h
    refine ⟨by rw [List.length_cons, hwalk]; exact h1, fun i hi => ?_⟩
    rcases i with _ | i
    · simpa [walk] using hr0
    · rw [hwalk]
      exact h2 i (by simp at hi; omega)

/-- **A branching follower state yields a checked branching witness** (with the same prime
lists).  Two loops `α, β` at the state start with different letters; powers `A = α^k₁`,
`B = β^k₂` fix every residue of the state; then `w₁ = AB` and `w₂ = BA` with any residue of the
state and the state's interval pass `branchOK`. -/
@[category research solved, AMS 11 37, ref "Oda26", group "dubc2_obstruction"]
theorem exists_branchOK (hF : ParamFacts P) {X : FState} (hX : Branching P X) :
    ∃ H : BranchWitness, H.PM = P.PM ∧ H.Pq = P.Pq ∧ branchOK P.p P.q P.a P.b H = true := by
  classical
  obtain ⟨s₁, s₂, Y₁, Y₂, hne, h₁, h₂, hb₁, hb₂⟩ := hX
  obtain ⟨u₁, hu₁⟩ := stepw_of_reach hb₁
  obtain ⟨u₂, hu₂⟩ := stepw_of_reach hb₂
  have hα : stepw P X (s₁ :: u₁) = some X := by simp [stepw, h₁, hu₁]
  have hβ : stepw P X (s₂ :: u₂) = some X := by simp [stepw, h₂, hu₂]
  obtain ⟨k₁, hk₁, hf₁⟩ := exists_rep_fix hα
  obtain ⟨k₂, hk₂, hf₂⟩ := exists_rep_fix hβ
  obtain ⟨k₁, rfl⟩ : ∃ k, k₁ = k + 1 := ⟨k₁ - 1, by omega⟩
  obtain ⟨k₂, rfl⟩ : ∃ k, k₂ = k + 1 := ⟨k₂ - 1, by omega⟩
  set A := rep (k₁ + 1) (s₁ :: u₁) with hAdef
  set B := rep (k₂ + 1) (s₂ :: u₂) with hBdef
  have hA : A = s₁ :: (u₁ ++ rep k₁ (s₁ :: u₁)) := by rw [hAdef, rep_succ]; rfl
  have hB : B = s₂ :: (u₂ ++ rep k₂ (s₂ :: u₂)) := by rw [hBdef, rep_succ]; rfl
  have hAX : stepw P X A = some X := stepw_rep hα _
  have hBX : stepw P X B = some X := stepw_rep hβ _
  -- a residue of the state
  obtain ⟨r₀, hr₀, hr₀ok⟩ : ∃ r ∈ X.R, rOK P r s₁ = true := by
    have hY := (step_facts h₁)
    have hne' : (rstep P X.R s₁).Nonempty := by
      unfold step at h₁
      split_ifs at h₁ with hc
      exact hc.2.1
    obtain ⟨z, hz⟩ := hne'
    rw [rstep, Finset.mem_image] at hz
    obtain ⟨r, hr, -⟩ := hz
    exact ⟨r, (Finset.mem_filter.1 hr).1, (Finset.mem_filter.1 hr).2⟩
  have hl2 : ∀ l ∈ P.PM, 2 ≤ l := by
    intro l hl
    have h0 : l ≠ 0 := by
      rintro rfl
      have := hF.PM 0 hl
      rw [Nat.mod_zero] at this
      exact absurd this hF.M0.ne'
    have h1 : l ≠ 1 := by
      rintro rfl
      simp only [rOK, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at hr₀ok
      exact hr₀ok.1 1 hl (Nat.mod_one _)
    omega
  have hres : ∀ w, stepw P X w = some X → rpath P r₀ w = some r₀ → w ≠ [] →
      bwordOK P.p P.q P.a P.b ⟨P.PM, P.Pq, (r₀ : ℤ), A ++ B, B ++ A, X.lo, X.hi⟩ w = true := by
    intro w hw hr hw0
    have hI := stepw_interval w hw
    have hR : ∀ l : ℕ, (((r₀ : ℤ) % (l : ℤ)).toNat) = r₀ % l := fun l => by
      rw [← Int.natCast_mod, Int.toNat_natCast]
    simp only [bwordOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      hR, hI]
    refine ⟨⟨⟨fun l hl => ?_, fun l hl s hs => ?_⟩, le_rfl⟩, le_rfl⟩
    · obtain ⟨h1, h2⟩ := walk_of_rpath hF hl (hl2 l hl) w r₀ r₀ hr
      exact ⟨h1, h2⟩
    · have := stepw_sOK w hw s hs
      simp only [sOK, List.all_eq_true, bne_iff_ne, ne_eq] at this
      exact this l hl
  have hrA : rpath P r₀ A = some r₀ := hf₁ r₀ hr₀
  have hrB : rpath P r₀ B = some r₀ := hf₂ r₀ hr₀
  have hb := stepw_bounds A (by rw [hA]; simp) hAX
  refine ⟨⟨P.PM, P.Pq, (r₀ : ℤ), A ++ B, B ++ A, X.lo, X.hi⟩, rfl, rfl, ?_⟩
  simp only [branchOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [hA]; simp
  · simp [Nat.add_comm]
  · rw [hA, hB]
    intro h
    exact hne (List.cons.inj h).1
  · exact fun l hl => ⟨hl2 l hl, invMod_spec hF (hl2 l hl) (Nat.dvd_of_mod_eq_zero (hF.PM l hl))⟩
  · exact hb.1
  · exact hb.2.1
  · exact hb.2.2
  · exact hres _ (by rw [stepw_append, hAX]; exact hBX) (by rw [rpath_append, hrA]; exact hrB)
      (by rw [hA]; simp)
  · exact hres _ (by rw [stepw_append, hBX]; exact hAX) (by rw [rpath_append, hrB]; exact hrA)
      (by rw [hB]; simp)

/-- **T5(iv), necessity from the follower automaton**: a branching state (reachable or not) rules
out every certificate, at every `D`. -/
@[category research solved, AMS 11 37, ref "Oda26", group "dubc2_obstruction"]
theorem not_checked_of_branching {C : Cert} {X : FState} (hX : Branching P X) :
    ¬ Checked P C := by
  intro hc
  have hF : ParamFacts P := by
    have hh := hc.head
    simp only [checkHead, Bool.and_eq_true] at hh
    exact paramFacts hh.1.1.1.1.1
  obtain ⟨H, hPM, hPq, h⟩ := exists_branchOK hF hX
  exact not_checked_of_branchOK H h (fun l hl => hPM ▸ hl) (fun l hl => hPq ▸ hl) hc

/-- **T5(iv) for a finite follower automaton, both halves.**  Some cell count `D` certifies iff
the least common denominator `D_F` of the endpoints certifies iff no reachable state branches. -/
@[category research solved, AMS 11 37, ref "Oda26", group "dubc2_obstruction"]
theorem checked_iff (hP : checkParams P = true) (hfin : {X | Reach P (root P) X}.Finite) :
    ((∃ D C, Checked { P with D := D } C) ↔ ∀ X, Reach P (root P) X → ¬ Branching P X) ∧
      ((∃ C, Checked { P with D := DF hfin } C) ↔ ∀ X, Reach P (root P) X → ¬ Branching P X) := by
  refine ⟨⟨?_, fun h => ⟨_, exists_checked_DF hP hfin h⟩⟩,
    ⟨?_, exists_checked_DF hP hfin⟩⟩
  · rintro ⟨D, C, hc⟩ X _ hX
    exact not_checked_of_branching (P := { P with D := D }) hX hc
  · rintro ⟨C, hc⟩ X _ hX
    exact not_checked_of_branching (P := { P with D := DF hfin }) hX hc

end Witness

/-! ## The growth of the admissible language -/

section Growth

/-- A state with `0 ≤ lo` and `hi ≤ 1` (the root, and every image of a step). -/
def Valid (X : FState) : Prop := 0 ≤ X.lo ∧ X.hi ≤ 1

/-- The alphabet `sLo, …, sLo + nA − 1`. -/
def alph (P : Params) : Finset ℤ := (Finset.range P.nA).image P.letter

/-- The admissible words of length `n` from `X`, as a finite set. -/
def words (P : Params) : ℕ → FState → Finset (List ℤ)
  | 0, _ => {[]}
  | n + 1, X => (alph P).biUnion fun s =>
      (step P X s).elim ∅ fun Y => (words P n Y).image (List.cons s)

/-- The admissible language of `F`: words of length `n` along which the root survives. -/
def lang (P : Params) (n : ℕ) : Set (List ℤ) :=
  {w | w.length = n ∧ (stepw P (root P) w).isSome}

/-- **Polynomial growth** of the admissible language. -/
def PolyGrowth (P : Params) : Prop :=
  ∃ C d : ℕ, ∀ n, (lang P n).ncard ≤ C * (n + 1) ^ d

theorem valid_root : Valid (root P) := ⟨le_rfl, le_rfl⟩

theorem valid_of_step {X Y : FState} {s : ℤ} (h : step P X s = some Y) : Valid Y :=
  ⟨(step_facts h).2.2.2.1, (step_facts h).2.2.2.2.2⟩

theorem valid_of_reach {X : FState} (h : Reach P (root P) X) : Valid X := by
  induction h with
  | refl => exact valid_root
  | tail _ hbc _ => obtain ⟨s, hs⟩ := hbc; exact valid_of_step hs

/-- **Every live letter is in the alphabet** (from the side conditions of `checkParams`). -/
theorem letter_mem (hF : ParamFacts P) {X Y : FState} {s : ℤ} (hX : Valid X)
    (h : step P X s = some Y) : s ∈ alph P := by
  obtain ⟨-, -, hI, -, hlt, -⟩ := step_facts h
  simp only [istep, Prod.mk.injEq] at hI
  rw [hI.1, hI.2] at hlt
  have hp : (0 : ℚ) < P.p := by exact_mod_cast (by have := hF.pq; omega : 0 < P.p)
  have hq : (0 : ℚ) < P.q := by exact_mod_cast (by have := hF.q1; omega : 0 < P.q)
  have hb : (0 : ℚ) < P.b := by exact_mod_cast hF.b0
  have A : 0 < fw P.p P.q P.a P.b s X.hi :=
    (le_max_left _ _).trans_lt (hlt.trans_le (min_le_right _ _))
  have B : fw P.p P.q P.a P.b s X.lo < 1 :=
    (le_max_right _ _).trans_lt (hlt.trans_le (min_le_left _ _))
  simp only [fw] at A B
  have A' := (div_pos_iff_of_pos_right hq).1 A
  have B' := (div_lt_one hq).1 B
  set c : ℚ := ((P.p : ℚ) - P.q) * P.a / P.b with hc
  have hcb : c * P.b = ((P.p : ℚ) - P.q) * P.a := div_mul_cancel₀ _ hb.ne'
  have hlo := hX.1
  have hhi := hX.2
  have hs1 : (s : ℚ) < P.p - c := by nlinarith
  have hs2 : -(s : ℚ) - c < P.q := by nlinarith
  have hHi : (P.p : ℚ) * P.b - ((P.p : ℚ) - P.q) * P.a ≤ P.b * (P.sLo + P.nA) := by
    exact_mod_cast hF.sHi
  have hLo : (P.b : ℚ) * (P.sLo - 1) ≤ -((P.q : ℚ) * P.b) - ((P.p : ℚ) - P.q) * P.a := by
    exact_mod_cast hF.sLo
  have m1 := mul_lt_mul_of_pos_right hs1 hb
  have m2 := mul_lt_mul_of_pos_right hs2 hb
  rw [sub_mul, hcb] at m1
  rw [sub_mul, hcb] at m2
  have u1 : (s : ℚ) < P.sLo + P.nA := by
    by_contra hc'
    push Not at hc'
    nlinarith
  have u2 : (P.sLo : ℚ) - 1 < s := by
    by_contra hc'
    push Not at hc'
    nlinarith
  have v1 : s < P.sLo + P.nA := by exact_mod_cast u1
  have v2 : P.sLo - 1 < s := by exact_mod_cast u2
  refine Finset.mem_image.2 ⟨(s - P.sLo).toNat, Finset.mem_range.2 (by omega), ?_⟩
  simp only [Params.letter]
  omega

theorem mem_words (hF : ParamFacts P) : ∀ (n : ℕ) (X : FState) (w : List ℤ), Valid X →
    (w ∈ words P n X ↔ w.length = n ∧ (stepw P X w).isSome)
  | 0, X, w, _ => by cases w <;> simp [words, stepw]
  | n + 1, X, w, hX => by
    constructor
    · intro h
      simp only [words, Finset.mem_biUnion] at h
      obtain ⟨s, -, hs⟩ := h
      cases hY : step P X s with
      | none => simp [hY] at hs
      | some Y =>
        simp only [hY, Option.elim, Finset.mem_image] at hs
        obtain ⟨v, hv, rfl⟩ := hs
        obtain ⟨h1, h2⟩ := (mem_words hF n Y v (valid_of_step hY)).1 hv
        simp [stepw, hY, h1, h2]
    · rintro ⟨hl, hs⟩
      cases w with
      | nil => simp at hl
      | cons s v =>
        simp only [stepw] at hs
        cases hY : step P X s with
        | none => simp [hY] at hs
        | some Y =>
          simp only [hY, Option.bind_some] at hs
          simp only [words, Finset.mem_biUnion]
          refine ⟨s, letter_mem hF hX hY, ?_⟩
          simp only [hY, Option.elim, Finset.mem_image]
          exact ⟨v, (mem_words hF n Y v (valid_of_step hY)).2 ⟨by simpa using hl, hs⟩, rfl⟩

theorem lang_eq (hF : ParamFacts P) (n : ℕ) : lang P n = ↑(words P n (root P)) := by
  ext w
  rw [Finset.mem_coe, mem_words hF n _ w valid_root]
  rfl

theorem ncard_lang (hF : ParamFacts P) (n : ℕ) : (lang P n).ncard = (words P n (root P)).card := by
  rw [lang_eq hF, Set.ncard_coe_finset]

theorem card_words_succ_le (n : ℕ) (X : FState) :
    (words P (n + 1) X).card ≤ ∑ s ∈ alph P, (step P X s).elim 0 fun Y => (words P n Y).card := by
  rw [words]
  refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun s _ => ?_)
  cases step P X s with
  | none => simp
  | some Y => exact Finset.card_image_le

/-- An exponential beats every polynomial. -/
theorem exists_pow_lt (C d a L : ℕ) (hL : 0 < L) : ∃ m, C * (a + m * L + 1) ^ d < 2 ^ m := by
  rcases Nat.eq_zero_or_pos C with rfl | hC
  · exact ⟨0, by simp⟩
  set E := a + (d + 1) * L + 1 with hE
  set j := C * E ^ d with hj
  have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by positivity))
  refine ⟨(d + 1) * j, ?_⟩
  have h1 : a + (d + 1) * j * L + 1 ≤ E * j := by
    have : a ≤ a * j := Nat.le_mul_of_pos_right _ hj1
    have : (d + 1) * j * L = (d + 1) * L * j := by ring
    nlinarith
  have hjlt : j < 2 ^ j := Nat.lt_two_pow_self
  calc C * (a + (d + 1) * j * L + 1) ^ d ≤ C * (E * j) ^ d :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _)
    _ = j * j ^ d := by rw [hj, mul_pow]; ring
    _ ≤ j * (2 ^ j) ^ d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hjlt.le _)
    _ < 2 ^ j * (2 ^ j) ^ d := mul_lt_mul_of_pos_right hjlt (by positivity)
    _ = 2 ^ ((d + 1) * j) := by rw [← pow_succ', ← pow_mul, Nat.mul_comm]

/-- Two distinct loops of one length at a branching state. -/
theorem branching_loops {X : FState} (hX : Branching P X) :
    ∃ w₁ w₂ : List ℤ, w₁ ≠ w₂ ∧ w₁.length = w₂.length ∧ 0 < w₁.length ∧
      stepw P X w₁ = some X ∧ stepw P X w₂ = some X := by
  obtain ⟨s₁, s₂, Y₁, Y₂, hne, h₁, h₂, hb₁, hb₂⟩ := hX
  obtain ⟨u₁, hu₁⟩ := stepw_of_reach hb₁
  obtain ⟨u₂, hu₂⟩ := stepw_of_reach hb₂
  have hα : stepw P X (s₁ :: u₁) = some X := by simp [stepw, h₁, hu₁]
  have hβ : stepw P X (s₂ :: u₂) = some X := by simp [stepw, h₂, hu₂]
  refine ⟨(s₁ :: u₁) ++ (s₂ :: u₂), (s₂ :: u₂) ++ (s₁ :: u₁), ?_, by simp; omega,
    by simp, by rw [stepw_append, hα]; exact hβ, by rw [stepw_append, hβ]; exact hα⟩
  intro h
  exact hne (List.cons.inj h).1

/-- **Branching ⇒ exponential growth.** -/
theorem not_polyGrowth_of_branching (hF : ParamFacts P) {X : FState} (hr : Reach P (root P) X)
    (hX : Branching P X) : ¬ PolyGrowth P := by
  classical
  obtain ⟨w₁, w₂, hne, hlen, hL, h₁, h₂⟩ := branching_loops hX
  obtain ⟨u, hu⟩ := stepw_of_reach hr
  have hXv := valid_of_reach hr
  set L := w₁.length with hLdef
  have hlow : ∀ m, 2 ^ m ≤ (words P (m * L) X).card := by
    intro m
    induction m with
    | zero => simp [words]
    | succ m ih =>
      have hmem : ∀ w, w ∈ words P (m * L) X → ∀ v, stepw P X v = some X → v.length = L →
          v ++ w ∈ words P ((m + 1) * L) X := by
        intro w hw v hv hvl
        obtain ⟨hl, hs⟩ := (mem_words hF _ _ _ hXv).1 hw
        rw [mem_words hF _ _ _ hXv]
        refine ⟨by rw [List.length_append, hl, hvl]; ring, ?_⟩
        rw [stepw_append, hv]
        exact hs
      have hsub : (words P (m * L) X).image (w₁ ++ ·) ∪ (words P (m * L) X).image (w₂ ++ ·) ⊆
          words P ((m + 1) * L) X := by
        intro w hw
        rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at hw
        rcases hw with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
        · exact hmem v hv w₁ h₁ rfl
        · exact hmem v hv w₂ h₂ hlen.symm
      have hdisj : Disjoint ((words P (m * L) X).image (w₁ ++ ·))
          ((words P (m * L) X).image (w₂ ++ ·)) := by
        rw [Finset.disjoint_left]
        intro w hw1 hw2
        obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hw1
        obtain ⟨v', -, h⟩ := Finset.mem_image.1 hw2
        exact hne (List.append_inj h.symm hlen).1
      have hinj : ∀ w₀ : List ℤ, Function.Injective (w₀ ++ · : List ℤ → List ℤ) :=
        fun w₀ a b h => List.append_cancel_left h
      calc 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
        _ ≤ (words P (m * L) X).card + (words P (m * L) X).card := Nat.add_le_add ih ih
        _ = ((words P (m * L) X).image (w₁ ++ ·) ∪ (words P (m * L) X).image (w₂ ++ ·)).card := by
          rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ (hinj w₁),
            Finset.card_image_of_injective _ (hinj w₂)]
        _ ≤ _ := Finset.card_le_card hsub
  have hroot : ∀ m, 2 ^ m ≤ (lang P (u.length + m * L)).ncard := by
    intro m
    rw [ncard_lang hF]
    refine (hlow m).trans ?_
    rw [← Finset.card_image_of_injective _ (fun a b h => List.append_cancel_left h :
      Function.Injective (u ++ · : List ℤ → List ℤ))]
    refine Finset.card_le_card fun w hw => ?_
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
    obtain ⟨hl, hs⟩ := (mem_words hF _ _ _ hXv).1 hv
    rw [mem_words hF _ _ _ valid_root]
    refine ⟨by rw [List.length_append, hl], ?_⟩
    rw [stepw_append, hu]
    exact hs
  rintro ⟨C, d, hCd⟩
  obtain ⟨m, hm⟩ := exists_pow_lt C d u.length L hL
  have := (hroot m).trans (hCd _)
  omega

theorem growth_arith {K nA r n k j : ℕ} (hK : nA ≤ K) (hk : k ≤ 1) (hj : j ≤ nA) :
    k * (K ^ (r + 1) * (n + 1) ^ (r + 1)) + j * (K ^ r * (n + 1) ^ r) ≤
      K ^ (r + 1) * (n + 1 + 1) ^ (r + 1) := by
  have e1 : k * (K ^ (r + 1) * (n + 1) ^ (r + 1)) ≤ K ^ (r + 1) * (n + 1) ^ (r + 1) := by
    calc _ ≤ 1 * (K ^ (r + 1) * (n + 1) ^ (r + 1)) := Nat.mul_le_mul_right _ hk
      _ = _ := one_mul _
  have e2 : j * (K ^ r * (n + 1) ^ r) ≤ K ^ (r + 1) * (n + 1) ^ r := by
    calc _ ≤ K * (K ^ r * (n + 1) ^ r) := Nat.mul_le_mul_right _ (hj.trans hK)
      _ = _ := by ring
  have e3 : K ^ (r + 1) * (n + 1) ^ (r + 1) + K ^ (r + 1) * (n + 1) ^ r =
      K ^ (r + 1) * ((n + 1) ^ r * (n + 1 + 1)) := by ring
  have e4 : (n + 1) ^ r * (n + 1 + 1) ≤ (n + 1 + 1) ^ (r + 1) := by
    rw [pow_succ]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) _)
  have e5 := Nat.mul_le_mul_left (K ^ (r + 1)) e4
  omega

/-- **No branching ⇒ polynomial growth**: with `N` reachable states, at most
`(nA + 1)^N · (n + 1)^N` admissible words of length `n`. -/
theorem card_words_le (hP : checkParams P = true) (hfin : {X | Reach P (root P) X}.Finite)
    (hnb : ∀ X, Reach P (root P) X → ¬ Branching P X) (n : ℕ) :
    (words P n (root P)).card ≤ (P.nA + 1) ^ hfin.toFinset.card * (n + 1) ^ hfin.toFinset.card := by
  classical
  have hF := paramFacts hP
  set S := hfin.toFinset with hS
  set K := P.nA + 1 with hK
  let rk : FState → ℕ := fun X => (S.filter fun Y => Reach P X Y).card
  have hrk_le : ∀ X Y s, step P X s = some Y → rk Y ≤ rk X := fun X Y s h =>
    Finset.card_le_card fun Z hZ => by
      simp only [Finset.mem_filter] at hZ ⊢
      exact ⟨hZ.1, Relation.ReflTransGen.head ⟨s, h⟩ hZ.2⟩
  have hrk_eq : ∀ X Y s, Reach P (root P) X → step P X s = some Y → rk Y = rk X →
      Reach P Y X := by
    intro X Y s hX h he
    have hsub : S.filter (fun Z => Reach P Y Z) ⊆ S.filter (fun Z => Reach P X Z) :=
      fun Z hZ => by
        simp only [Finset.mem_filter] at hZ ⊢
        exact ⟨hZ.1, Relation.ReflTransGen.head ⟨s, h⟩ hZ.2⟩
    have heq := Finset.eq_of_subset_of_card_le hsub (le_of_eq he.symm)
    have hXm : X ∈ S.filter (fun Z => Reach P X Z) :=
      Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 hX, Relation.ReflTransGen.refl⟩
    rw [← heq] at hXm
    exact (Finset.mem_filter.1 hXm).2
  have hrk_pos : ∀ X, Reach P (root P) X → 1 ≤ rk X := fun X hX =>
    Finset.card_pos.2 ⟨X, Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 hX, Relation.ReflTransGen.refl⟩⟩
  have halph : (alph P).card ≤ P.nA := Finset.card_image_le.trans (by simp)
  have key : ∀ r n X, Reach P (root P) X → rk X ≤ r → (words P n X).card ≤ K ^ r * (n + 1) ^ r := by
    intro r
    induction r with
    | zero => intro n X hX hr; have := hrk_pos X hX; omega
    | succ r ihr =>
      intro n
      induction n with
      | zero =>
        intro X _ _
        simp only [words, Finset.card_singleton, zero_add, one_pow, mul_one]
        exact Nat.one_le_pow _ _ (by omega)
      | succ n ihn =>
        intro X hX hr
        refine (card_words_succ_le n X).trans ?_
        rw [← Finset.sum_filter_add_sum_filter_not (alph P)
          (fun s => ∃ Y, step P X s = some Y ∧ Reach P Y X)]
        have hkeep : ((alph P).filter fun s => ∃ Y, step P X s = some Y ∧ Reach P Y X).card ≤ 1 :=
          Finset.card_le_one.2 fun a ha b hb => by
            by_contra hab
            obtain ⟨Y₁, h₁, r₁⟩ := (Finset.mem_filter.1 ha).2
            obtain ⟨Y₂, h₂, r₂⟩ := (Finset.mem_filter.1 hb).2
            exact hnb X hX ⟨a, b, Y₁, Y₂, hab, h₁, h₂, r₁, r₂⟩
        have h1 := Finset.sum_le_card_nsmul
          ((alph P).filter fun s => ∃ Y, step P X s = some Y ∧ Reach P Y X)
          (fun s => (step P X s).elim 0 fun Y => (words P n Y).card)
          (K ^ (r + 1) * (n + 1) ^ (r + 1)) (fun s hs => by
            obtain ⟨Y, hY, -⟩ := (Finset.mem_filter.1 hs).2
            simp only [hY, Option.elim]
            exact ihn Y (hX.tail ⟨s, hY⟩) ((hrk_le X Y s hY).trans hr))
        have h2 := Finset.sum_le_card_nsmul
          ((alph P).filter fun s => ¬ ∃ Y, step P X s = some Y ∧ Reach P Y X)
          (fun s => (step P X s).elim 0 fun Y => (words P n Y).card)
          (K ^ r * (n + 1) ^ r) (fun s hs => by
            cases hY : step P X s with
            | none => simp
            | some Y =>
              simp only [Option.elim]
              have hne : ¬ Reach P Y X := fun h => (Finset.mem_filter.1 hs).2 ⟨Y, hY, h⟩
              have : rk Y ≤ r := by
                have := hrk_le X Y s hY
                by_contra hc
                exact hne (hrk_eq X Y s hX hY (by omega))
              exact ihr n Y (hX.tail ⟨s, hY⟩) this)
        have hcard : ((alph P).filter fun s => ¬ ∃ Y, step P X s = some Y ∧ Reach P Y X).card
            ≤ P.nA := (Finset.card_filter_le _ _).trans halph
        rw [smul_eq_mul] at h1 h2
        exact (Nat.add_le_add h1 h2).trans (growth_arith (by omega) hkeep hcard)
  exact key _ n _ Relation.ReflTransGen.refl (Finset.card_filter_le _ _)

/-- **T5(iv), the growth link**: a finite follower automaton has no reachable branching state iff
its admissible language grows polynomially. -/
@[category research solved, AMS 11 37, ref "Oda26", group "dubc2_obstruction"]
theorem polyGrowth_iff (hP : checkParams P = true) (hfin : {X | Reach P (root P) X}.Finite) :
    PolyGrowth P ↔ ∀ X, Reach P (root P) X → ¬ Branching P X := by
  have hF := paramFacts hP
  refine ⟨fun h X hX hb => not_polyGrowth_of_branching hF hX hb h, fun hnb => ?_⟩
  refine ⟨(P.nA + 1) ^ hfin.toFinset.card, hfin.toFinset.card, fun n => ?_⟩
  rw [ncard_lang hF]
  exact card_words_le hP hfin hnb n

/-- **T5(iv) for a finite follower automaton**, all four conditions: some `D` certifies ⟺ `D_F`
certifies ⟺ no reachable state branches ⟺ the admissible language grows polynomially. -/
@[category research solved, AMS 11 37, ref "Oda26", group "dubc2_obstruction"]
theorem T5iv (hP : checkParams P = true) (hfin : {X | Reach P (root P) X}.Finite) :
    [∃ D C, Checked { P with D := D } C, ∃ C, Checked { P with D := DF hfin } C,
      ∀ X, Reach P (root P) X → ¬ Branching P X, PolyGrowth P].TFAE := by
  have h := checked_iff hP hfin
  have hg := polyGrowth_iff hP hfin
  tfae_have 1 ↔ 3 := h.1
  tfae_have 2 ↔ 3 := h.2
  tfae_have 4 ↔ 3 := hg
  tfae_finish

end Growth

end Follower

end DubC2.Gen
