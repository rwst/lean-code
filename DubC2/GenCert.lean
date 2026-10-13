/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Z32.DubickasWord
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.GCD
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# A generic, kernel-checkable divisor-set certificate for `⌊ξ(p/q)ⁿ + ν⌋`

Milestone M2 / experiment X3 of `plans/plan-dubC2.html`: the *emitted-certificate route*.
The hand proofs of `DubC2/Nearest.lean`, `Calibration53/75` and `FloorCore` follow the real
orbit by hand.  This file replaces the hand by Boolean checks, proved sound once
(`DubC2/GenSound.lean`), so that every cell of the `(p/q, ν, 𝒫)` atlas found by
`DubC2/gencert.py` becomes a theorem by `decide +kernel`.

## The graph

Fix coprime `p > q > 1`, `ν = a/b`, a cell count `D`, a modulus `M`, and a divisor set split as
`𝒫 = PM ++ Pq` with every `ℓ ∈ PM` dividing `M` and every `ℓ ∈ Pq` dividing `q` (and prime to
`p`).  Vertices are `k = r·D + c` with `r < M` (the residue `xₙ mod M`) and `c < D` (the cell
`⌊D·yₙ⌋` of `yₙ = {ξ(p/q)ⁿ + ν}`).  `Params.succList k s` lists the vertices reachable from
`k` by the letter `s`; it over-approximates, so an avoiding real orbit is a path
(`Gen.sound`).

## The certificate

* **peel** — a chain `A₀ = everything, A₁, …, A_J` of vertex sets, each stored as a list of
  `Z`-bit block masks, together with sets `I_j ⊇ image Aⱼ`.  The round checks `roundOK` say
  that `A_{j+1}` keeps every vertex of `Aⱼ` with a successor in `Aⱼ` and an `I_j`-bit; then an
  infinite path started at time `N` lies in `Aⱼ` from time `N + j` on (`Gen.mem_A`), and no
  fixpoint has to be proved.
* **det** — the core `A_J`, listed, and a determinized automaton whose states are subsets of
  the core (bitmasks over core *indices*), with a transition table and a rank.  Each state's
  `s`-successors lie in the state the table names, ranks never increase, and from each state at
  most one letter keeps the rank — the `C_det` criterion of the plan (§4.2).

Every kernel computation touches numbers of at most `max Z |core|` bits: an earlier version that
kept vertex sets as one bitmask over all `M·D` vertices spent its time and memory creating and
hashing `M·D`-bit literals, and took the machine down at `7/5`.

Under `Checked` every avoiding orbit has an eventually periodic carry word
(`Gen.isEventuallyPeriodic_of_path`), which [DN05] Lemma 2 (`Z32.not_isEventuallyPeriodic_carry`)
forbids: `Gen.divisor_set_of_checked`.
-/

namespace DubC2.Gen

open Filter ForMathlib.SubwordComplexity

/-! ## Data -/

/-- The fixed data of one atlas cell. -/
structure Params where
  p : ℕ
  q : ℕ
  a : ℤ
  b : ℕ
  D : ℕ
  M : ℕ
  qinv : ℕ
  PM : List ℕ
  Pq : List ℕ
  sLo : ℤ
  nA : ℕ

/-- The certificate. -/
structure Cert where
  /-- Number of peeling rounds. -/
  J : ℕ
  /-- Block size. -/
  Z : ℕ
  /-- Number of blocks. -/
  nB : ℕ
  /-- The peel chain `A₁, …, A_J`, each a list of `nB` block masks (`A₀` is everything). -/
  peels : List (List ℕ)
  /-- Over-approximations `I₀, …, I_{J−1}` of the images, as block masks. -/
  imgs : List (List ℕ)
  /-- The core `A_J`, listed. -/
  core : List ℕ
  /-- The det states, as bitmasks over core indices; state `0` is the whole core. -/
  sets : List ℕ
  /-- The det transitions, indexed by state and letter index. -/
  trans : List (List (Option ℕ))
  /-- A rank on det states. -/
  rank : List ℕ

/-- `⋃_{x ∈ l, g x} f x` for bitmasks. -/
def orFold {α : Type*} (l : List α) (g : α → Bool) (f : α → ℕ) : ℕ :=
  l.foldl (fun acc x => if g x then acc ||| f x else acc) 0

/-- The set bits of `S`, offset by `i`, scanning at most `fuel` steps (32 zero bits per step). -/
def bitsScan : ℕ → ℕ → ℕ → List ℕ
  | 0, _, _ => []
  | fuel + 1, S, i =>
    if S = 0 then [] else if S % 2 ^ 32 = 0 then bitsScan fuel (S >>> 32) (i + 32)
    else if S % 2 = 1 then i :: bitsScan fuel (S / 2) (i + 1)
    else bitsScan fuel (S / 2) (i + 1)

/-- The set bits of a bitmask. -/
def bits (S : ℕ) : List ℕ := bitsScan S S 0

/-- Membership in a block-mask list. -/
def memB (B : List ℕ) (Z k : ℕ) : Bool := (B.getD (k / Z) 0).testBit (k % Z)

/-- `A ⊆ B` for bitmasks. -/
def subset (A B : ℕ) : Bool := (A ||| B) == B

namespace Params

variable (P : Params)

/-- The `t`-th letter of the alphabet `sLo, …, sLo + nA − 1`. -/
def letter (t : ℕ) : ℤ := P.sLo + t

/-- The number of vertices. -/
def nV : ℕ := P.M * P.D

/-- `K(s) = (p−q)·a·D + s·b·D`: the shift of the integer-scaled step. -/
def shiftK (s : ℤ) : ℤ := ((P.p : ℤ) - P.q) * P.a * P.D + s * P.b * P.D

/-- Lower end of `p·b·[c, c+1) − K(s)`, which must meet `q·b·[c', c'+1)`. -/
def lo (c : ℕ) (s : ℤ) : ℤ := (P.p : ℤ) * P.b * c - P.shiftK s

/-- Upper end of `p·b·[c, c+1) − K(s)`. -/
def hi (c : ℕ) (s : ℤ) : ℤ := (P.p : ℤ) * P.b * (c + 1) - P.shiftK s

/-- The residue of `x_{n+1}` mod `M`: `(p·r + s)·q⁻¹`. -/
def rnext (r : ℕ) (s : ℤ) : ℕ := (((P.p : ℤ) * r + s) * P.qinv % P.M).toNat

/-- First candidate target cell. -/
def cLo (c : ℕ) (s : ℤ) : ℕ := (P.lo c s / ((P.q : ℤ) * P.b)).toNat

/-- One past the last candidate target cell. -/
def cHi (c : ℕ) (s : ℤ) : ℕ := min P.D ((P.hi c s - 1) / ((P.q : ℤ) * P.b) + 1).toNat

/-- The vertices reachable by the letter `s` from vertex `k`. -/
def succList (k : ℕ) (s : ℤ) : List ℕ :=
  if (P.PM.all fun l => k / P.D % l != 0) && (P.Pq.all fun l => s % (l : ℤ) != 0) &&
      (P.PM.all fun l => P.rnext (k / P.D) s % l != 0) then
    ((List.range' (P.cLo (k % P.D) s) (P.cHi (k % P.D) s - P.cLo (k % P.D) s)).filter
      (fun c₂ : ℕ => decide ((P.q : ℤ) * P.b * c₂ < P.hi (k % P.D) s) &&
        decide (P.lo (k % P.D) s < (P.q : ℤ) * P.b * (c₂ + 1)))).map
      (fun c₂ : ℕ => P.rnext (k / P.D) s * P.D + c₂)
  else []

/-- The `s`-successors of `k` inside `core`, as a bitmask over core indices. -/
def succIdx (core : List ℕ) (k : ℕ) (s : ℤ) : ℕ :=
  orFold (P.succList k s) (fun w => core.contains w) (fun w => 2 ^ core.idxOf w)

end Params

namespace Cert

variable (C : Cert) (P : Params)

/-- Membership in `Aⱼ`. -/
def memA (j k : ℕ) : Bool :=
  if j = 0 then decide (k < P.nV) else memB (C.peels.getD (j - 1) []) C.Z k

/-- Block `i` of `Aⱼ`. -/
def blk (j i : ℕ) : ℕ := if j = 0 then 2 ^ C.Z - 1 else (C.peels.getD (j - 1) []).getD i 0

end Cert

/-- Round check number `u`: round `j = u / nB` on block `i = u % nB`.  For every vertex `k` of
the block in `Aⱼ`: all successors of `k` are in `I_j`, and if `k` has a successor in `Aⱼ` and an
`I_j`-bit then `k ∈ A_{j+1}`. -/
def roundOK (P : Params) (C : Cert) (u : ℕ) : Bool :=
  (bitsScan C.Z (C.blk (u / C.nB) (u % C.nB)) 0).all fun t =>
    !(C.memA P (u / C.nB) (u % C.nB * C.Z + t)) ||
    (((List.range P.nA).all fun a => (P.succList (u % C.nB * C.Z + t) (P.letter a)).all
        fun w => memB (C.imgs.getD (u / C.nB) []) C.Z w) &&
      (!((List.range P.nA).any fun a => (P.succList (u % C.nB * C.Z + t) (P.letter a)).any
          fun w => C.memA P (u / C.nB) w) ||
        !(memB (C.imgs.getD (u / C.nB) []) C.Z (u % C.nB * C.Z + t)) ||
        C.memA P (u / C.nB + 1) (u % C.nB * C.Z + t)))

/-- The letters that keep the rank from det state `i`. -/
def keep (C : Cert) (nA i : ℕ) : List ℕ :=
  (List.range nA).filter fun t =>
    match (C.trans.getD i []).getD t none with
    | none => false
    | some j => C.rank.getD j 0 == C.rank.getD i 0

/-- The `s`-successors of det state `S`. -/
def detSucc (P : Params) (C : Cert) (S : ℕ) (s : ℤ) : ℕ :=
  orFold (bits S) (fun _ => true) (fun x => P.succIdx C.core (C.core.getD x 0) s)

/-- Row check for det state `i`. -/
def detOK (P : Params) (C : Cert) (i : ℕ) : Bool :=
  ((List.range P.nA).all fun t =>
    match (C.trans.getD i []).getD t none with
    | none => detSucc P C (C.sets.getD i 0) (P.letter t) == 0
    | some j => decide (j < C.sets.length) &&
        subset (detSucc P C (C.sets.getD i 0) (P.letter t)) (C.sets.getD j 0) &&
        decide (C.rank.getD j 0 ≤ C.rank.getD i 0)) &&
  decide ((keep C P.nA i).length ≤ 1)

/-- The arithmetic side conditions. -/
def checkParams (P : Params) : Bool :=
  decide (1 < P.q) && decide (P.q < P.p) && (Nat.gcd P.p P.q == 1) && decide (0 < P.b) &&
  decide (0 < P.D) && decide (0 < P.M) && (P.q * P.qinv % P.M == 1 % P.M) &&
  (P.PM.all fun l => P.M % l == 0) &&
  (P.Pq.all fun l => P.q % l == 0 && Nat.gcd l P.p == 1) &&
  decide ((P.b : ℤ) * (P.sLo - 1) ≤ -((P.q : ℤ) * P.b) - ((P.p : ℤ) - P.q) * P.a) &&
  decide ((P.p : ℤ) * P.b - ((P.p : ℤ) - P.q) * P.a ≤ (P.b : ℤ) * (P.sLo + P.nA))

/-- Every vertex of `A_J` (block `i`) is listed in the core. -/
def coreOK (P : Params) (C : Cert) (i : ℕ) : Bool :=
  (bitsScan C.Z (C.blk C.J i) 0).all fun t =>
    !(C.memA P C.J (i * C.Z + t)) || C.core.contains (i * C.Z + t)

/-- The head check: parameters, block cover, the core, and det state `0` = the whole core. -/
def checkHead (P : Params) (C : Cert) : Bool :=
  checkParams P && decide (0 < C.sets.length) && decide (0 < C.Z) &&
  decide (P.nV ≤ C.nB * C.Z) && ((List.range C.nB).all (coreOK P C)) &&
  subset (2 ^ C.core.length - 1) (C.sets.getD 0 0)

/-- **A checked certificate**: three Boolean facts, each decided by the kernel (the second and
third in as many separate pieces as the generator likes, glued by `all_range'_append`). -/
structure Checked (P : Params) (C : Cert) : Prop where
  head : checkHead P C = true
  rounds : (List.range' 0 (C.J * C.nB)).all (roundOK P C) = true
  det : (List.range' 0 C.sets.length).all (detOK P C) = true

/-- Gluing two consecutive range checks. -/
theorem all_range'_append {f : ℕ → Bool} {a n b m : ℕ} (h₁ : (List.range' a n).all f = true)
    (h₂ : (List.range' b m).all f = true) (hb : a + n = b) :
    (List.range' a (n + m)).all f = true := by
  subst hb
  rw [← List.range'_append_1, List.all_append, h₁, h₂, Bool.and_self]

/-- Gluing with every length explicit (the generator uses this form, so that elaboration only
ever compares numerals and never unfolds a check). -/
theorem all_glue (f : ℕ → Bool) (a n m N : ℕ) (h₁ : (List.range' a n).all f = true)
    (h₂ : (List.range' (a + n) m).all f = true) (hN : n + m = N) :
    (List.range' a N).all f = true := by
  subst hN
  exact all_range'_append h₁ h₂ rfl

/-! ## Bitmask lemmas -/

theorem testBit_foldl {α : Type*} (l : List α) (g : α → Bool) (f : α → ℕ) (init k : ℕ) :
    (l.foldl (fun acc x => if g x then acc ||| f x else acc) init).testBit k = true ↔
      init.testBit k = true ∨ ∃ x ∈ l, g x = true ∧ (f x).testBit k = true := by
  induction l generalizing init with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rw [ih]
    by_cases hg : g x = true
    · simp only [hg, ite_true, Nat.testBit_or, Bool.or_eq_true]
      constructor
      · rintro ((h | h) | ⟨y, hy, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨x, Or.inl rfl, hg, h⟩
        · exact Or.inr ⟨y, Or.inr hy, h⟩
      · rintro (h | ⟨y, rfl | hy, h⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h.2)
        · exact Or.inr ⟨y, hy, h⟩
    · simp only [hg, Bool.false_eq_true, ite_false]
      constructor
      · rintro (h | ⟨y, hy, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨y, Or.inr hy, h⟩
      · rintro (h | ⟨y, rfl | hy, h⟩)
        · exact Or.inl h
        · exact absurd h.1 hg
        · exact Or.inr ⟨y, hy, h⟩

theorem testBit_orFold {α : Type*} (l : List α) (g : α → Bool) (f : α → ℕ) (k : ℕ) :
    (orFold l g f).testBit k = true ↔ ∃ x ∈ l, g x = true ∧ (f x).testBit k = true := by
  rw [orFold, testBit_foldl]
  simp

theorem mem_bitsScan : ∀ (fuel S i k : ℕ), k < fuel → S.testBit k = true →
    i + k ∈ bitsScan fuel S i
  | 0, S, i, k, hk', hk => absurd hk' (Nat.not_lt_zero _)
  | fuel + 1, S, i, k, hk', hk => by
    have hS0 : S ≠ 0 := by rintro rfl; simp at hk
    simp only [bitsScan, hS0, ite_false]
    by_cases hw : S % 2 ^ 32 = 0
    · rw [if_pos hw]
      have hk32 : 32 ≤ k := by
        by_contra hlt
        have := Nat.testBit_mod_two_pow S 32 k
        rw [hw, Nat.zero_testBit, hk] at this
        simp at this; omega
      have := mem_bitsScan fuel (S >>> 32) (i + 32) (k - 32) (by omega)
        (by rw [Nat.testBit_shiftRight, show 32 + (k - 32) = k by omega]; exact hk)
      rwa [show i + 32 + (k - 32) = i + k by omega] at this
    rw [if_neg hw]
    rcases k with _ | k'
    · rw [Nat.testBit_zero] at hk
      simp only [decide_eq_true_eq] at hk
      simp [hk]
    · have hrec : i + (k' + 1) ∈ bitsScan fuel (S / 2) (i + 1) := by
        rw [show i + (k' + 1) = (i + 1) + k' by omega]
        exact mem_bitsScan fuel _ _ k' (by omega) (by rw [Nat.testBit_div_two]; exact hk)
      split_ifs
      · exact List.mem_cons_of_mem _ hrec
      · exact hrec

theorem mem_bits {S k : ℕ} (hk : S.testBit k = true) : k ∈ bits S := by
  have hlt : k < S := lt_of_lt_of_le Nat.lt_two_pow_self (Nat.ge_two_pow_of_testBit hk)
  simpa [bits] using mem_bitsScan S S 0 k hlt hk

theorem testBit_of_subset {A B k : ℕ} (h : subset A B = true) (hA : A.testBit k = true) :
    B.testBit k = true := by
  simp only [subset, beq_iff_eq] at h
  rw [← h, Nat.testBit_or, hA, Bool.true_or]

theorem ne_zero_of_testBit {A k : ℕ} (h : A.testBit k = true) : A ≠ 0 := by
  rintro rfl
  simp at h

theorem getD_idxOf {core : List ℕ} {w : ℕ} (h : w ∈ core) : core.getD (core.idxOf w) 0 = w := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem h),
    List.getElem_idxOf]

theorem testBit_succIdx {P : Params} {core : List ℕ} {k w : ℕ} {s : ℤ}
    (hw : w ∈ P.succList k s) (hc : w ∈ core) : (P.succIdx core k s).testBit (core.idxOf w) = true := by
  rw [Params.succIdx, testBit_orFold]
  exact ⟨w, hw, List.contains_iff_mem.2 hc, Nat.testBit_two_pow_self⟩

/-! ## Splitting one det row

A det state that is a large set of core vertices is too expensive for one kernel `decide`
(every member costs a successor list and linear scans of the core).  Its row is then checked
member by member and letter by letter (`detRowOK`, in as many pieces as the generator likes), plus
a cheap head check (`detHeadOK`), and reassembled by `detOK_of_rows`. -/

/-- Row `(i, t)` at the core vertex with index `x`: its successors lie in the target. -/
def detMemOK (P : Params) (C : Cert) (i t x : ℕ) : Bool :=
  match (C.trans.getD i []).getD t none with
  | none => P.succIdx C.core (C.core.getD x 0) (P.letter t) == 0
  | some j => subset (P.succIdx C.core (C.core.getD x 0) (P.letter t)) (C.sets.getD j 0)

/-- The member-free part of `detOK`: target indices, ranks, and the keep condition. -/
def detHeadOK (P : Params) (C : Cert) (i : ℕ) : Bool :=
  ((List.range P.nA).all fun t =>
    match (C.trans.getD i []).getD t none with
    | none => true
    | some j => decide (j < C.sets.length) && decide (C.rank.getD j 0 ≤ C.rank.getD i 0)) &&
  decide ((keep C P.nA i).length ≤ 1)

/-- Check number `u = t·L + k` of det row `i`: letter `t`, `k`-th member (`L` members). -/
def detRowOK (P : Params) (C : Cert) (i L u : ℕ) : Bool :=
  detMemOK P C i (u / L) ((bits (C.sets.getD i 0)).getD (u % L) 0)

theorem subset_of_testBit {A T : ℕ} (h : ∀ k, A.testBit k = true → T.testBit k = true) :
    subset A T = true := by
  simp only [subset, beq_iff_eq]
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_or]
  cases hA : A.testBit k
  · simp
  · simp [h k hA]

theorem eq_zero_of_testBit {A : ℕ} (h : ∀ k, A.testBit k = false) : A = 0 :=
  Nat.eq_of_testBit_eq fun k => by rw [h k, Nat.zero_testBit]

theorem all_range'_one {f : ℕ → Bool} {i : ℕ} (h : f i = true) : (List.range' i 1).all f = true := by
  simp [h]

/-- **Reassembling a split det row.** -/
theorem detOK_of_rows {P : Params} {C : Cert} {i L N : ℕ} (hh : detHeadOK P C i = true)
    (hL : (bits (C.sets.getD i 0)).length = L) (hN : P.nA * L = N)
    (hr : (List.range' 0 N).all (detRowOK P C i L) = true) : detOK P C i = true := by
  have hmem : ∀ t < P.nA, ∀ x ∈ bits (C.sets.getD i 0), detMemOK P C i t x = true := by
    intro t ht x hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    have hkL : k < L := hL ▸ hk
    have hu : t * L + k < N := by
      rw [← hN]
      have : t * L + k < t * L + L := by omega
      have : t * L + L ≤ P.nA * L := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ ht
      omega
    have h := List.all_eq_true.1 hr (t * L + k) (List.mem_range'_1.2 ⟨Nat.zero_le _, by omega⟩)
    have hL0 : 0 < L := by omega
    have hdiv : (t * L + k) / L = t := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hL0, Nat.div_eq_of_lt hkL, zero_add]
    have hmod : (t * L + k) % L = k := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hkL]
    simp only [detRowOK, hdiv, hmod] at h
    have e : (bits (C.sets.getD i 0)).getD k 0 = (bits (C.sets.getD i 0))[k] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    rwa [e] at h
  simp only [detHeadOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hh
  simp only [detOK, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨fun t ht => ?_, hh.2⟩
  have hht := hh.1 t ht
  have hm := hmem t ht
  revert hht hm
  unfold detMemOK
  cases (C.trans.getD i []).getD t none with
  | none =>
    intro _ hm
    simp only [beq_iff_eq] at hm ⊢
    refine eq_zero_of_testBit fun k => ?_
    by_contra hk
    rw [Bool.not_eq_false, detSucc, testBit_orFold] at hk
    obtain ⟨x, hx, -, hb⟩ := hk
    rw [hm x hx, Nat.zero_testBit] at hb
    exact Bool.false_ne_true hb
  | some j =>
    intro hht hm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hht ⊢
    refine ⟨⟨hht.1, subset_of_testBit fun k hk => ?_⟩, hht.2⟩
    rw [detSucc, testBit_orFold] at hk
    obtain ⟨x, hx, -, hb⟩ := hk
    exact testBit_of_subset (hm x hx) hb

/-! ## The combinatorial half: paths in the graph -/

/-- A path of the graph from time `N` on: `v n` is the vertex, `t n` the letter index. -/
structure IsPath (P : Params) (N : ℕ) (v t : ℕ → ℕ) : Prop where
  lt : ∀ n, N ≤ n → v n < P.nV
  letter_lt : ∀ n, N ≤ n → t n < P.nA
  edge : ∀ n, N ≤ n → v (n + 1) ∈ P.succList (v n) (P.letter (t n))

section Path

variable {P : Params} {N : ℕ} {v t : ℕ → ℕ}

theorem head_facts {C : Cert} (hc : Checked P C) :
    0 < C.sets.length ∧ 0 < C.Z ∧ P.nV ≤ C.nB * C.Z ∧ (∀ i < C.nB, coreOK P C i = true) ∧
      subset (2 ^ C.core.length - 1) (C.sets.getD 0 0) = true := by
  have hh := hc.head
  simp only [checkHead, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
    at hh
  exact ⟨hh.1.1.1.1.2, hh.1.1.1.2, hh.1.1.2, hh.1.2, hh.2⟩

/-- A vertex of `Aⱼ` is a bit of its own block. -/
theorem blk_testBit {C : Cert} (hZ : 0 < C.Z) {j k : ℕ} (hk : C.memA P j k = true) :
    (C.blk j (k / C.Z)).testBit (k % C.Z) = true := by
  unfold Cert.blk
  unfold Cert.memA at hk
  split_ifs with h
  · rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true (Nat.mod_lt _ hZ)
  · rw [if_neg h] at hk; exact hk

theorem mem_blk_scan {C : Cert} (hZ : 0 < C.Z) {j k : ℕ} (hk : C.memA P j k = true) :
    k % C.Z ∈ bitsScan C.Z (C.blk j (k / C.Z)) 0 := by
  simpa using mem_bitsScan C.Z _ 0 (k % C.Z) (Nat.mod_lt _ hZ) (blk_testBit hZ hk)

/-- The round facts at one vertex of `Aⱼ`. -/
theorem round_at {C : Cert} (hc : Checked P C) {j k : ℕ} (hj : j < C.J)
    (hk : C.memA P j k = true) (hkV : k < P.nV) :
    (∀ a < P.nA, ∀ w ∈ P.succList k (P.letter a), memB (C.imgs.getD j []) C.Z w = true) ∧
      ((∃ a < P.nA, ∃ w ∈ P.succList k (P.letter a), C.memA P j w = true) →
        memB (C.imgs.getD j []) C.Z k = true → C.memA P (j + 1) k = true) := by
  obtain ⟨-, hZ, hcov, -, -⟩ := head_facts hc
  have hi : k / C.Z < C.nB := (Nat.div_lt_iff_lt_mul hZ).2 (by linarith)
  have hu : j * C.nB + k / C.Z < C.J * C.nB := by nlinarith
  have hr := List.all_eq_true.1 hc.rounds (j * C.nB + k / C.Z)
    (List.mem_range'_1.2 ⟨Nat.zero_le _, by rw [zero_add]; exact hu⟩)
  have hnB : 0 < C.nB := lt_of_le_of_lt (Nat.zero_le _) hi
  have hdiv : (j * C.nB + k / C.Z) / C.nB = j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hnB, Nat.div_eq_of_lt hi, zero_add]
  have hmod : (j * C.nB + k / C.Z) % C.nB = k / C.Z := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  have hkk : k / C.Z * C.Z + k % C.Z = k := Nat.div_add_mod' k C.Z
  simp only [roundOK, hdiv, hmod] at hr
  have h := List.all_eq_true.1 hr (k % C.Z) (mem_blk_scan hZ hk)
  rw [hkk, hk] at h
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true'] at h
  refine ⟨h.1, fun ⟨a, ha, w, hw, hA⟩ hI => ?_⟩
  rcases h.2 with (h' | h') | h'
  · have hany : ((List.range P.nA).any fun a => (P.succList k (P.letter a)).any
        fun w => C.memA P j w) = true :=
      List.any_eq_true.2 ⟨a, List.mem_range.2 ha, List.any_eq_true.2 ⟨w, hw, hA⟩⟩
    rw [hany] at h'; exact absurd h' (by decide)
  · rw [hI] at h'; exact absurd h' (by decide)
  · exact h'

theorem mem_A {C : Cert} (hc : Checked P C) (hp : IsPath P N v t) :
    ∀ j, j ≤ C.J → ∀ n, N + j ≤ n → C.memA P j (v n) = true := by
  intro j
  induction j with
  | zero =>
    intro _ n hn
    simp only [Cert.memA, ite_true, decide_eq_true_eq]
    exact hp.lt n (by omega)
  | succ j ih =>
    intro hj n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    refine (round_at hc (by omega) (ih (by omega) _ (by omega)) (hp.lt _ (by omega))).2
      ⟨t (m + 1), hp.letter_lt _ (by omega), v (m + 1 + 1), hp.edge _ (by omega),
        ih (by omega) _ (by omega)⟩ ?_
    exact (round_at hc (by omega) (ih (by omega) m (by omega)) (hp.lt _ (by omega))).1
      (t m) (hp.letter_lt m (by omega)) _ (hp.edge m (by omega))

/-- From time `N + J` on the path runs in the core. -/
theorem mem_core {C : Cert} (hc : Checked P C) (hp : IsPath P N v t) {n : ℕ} (hn : N + C.J ≤ n) :
    v n ∈ C.core := by
  obtain ⟨-, hZ, hcov, hcore, -⟩ := head_facts hc
  have hA := mem_A hc hp C.J le_rfl n hn
  have hi : v n / C.Z < C.nB := (Nat.div_lt_iff_lt_mul hZ).2 (by have := hp.lt n (by omega); linarith)
  have h := List.all_eq_true.1 (hcore _ hi) (v n % C.Z) (mem_blk_scan hZ hA)
  rw [Nat.div_add_mod' (v n) C.Z, hA] at h
  simpa using h

/-- The next det state. -/
def next (C : Cert) (i t : ℕ) : ℕ := ((C.trans.getD i []).getD t none).getD 0

/-- The det path, started at time `N₀`. -/
def detPath (C : Cert) (t : ℕ → ℕ) (N₀ : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => next C (detPath C t N₀ i) (t (N₀ + i))

/-- One det step. -/
theorem step_entry {C : Cert} (hc : Checked P C) (hp : IsPath P N v t) {d n : ℕ}
    (hn : N + C.J ≤ n) (hd : d < C.sets.length)
    (hbit : (C.sets.getD d 0).testBit (C.core.idxOf (v n)) = true) :
    ∃ j, (C.trans.getD d []).getD (t n) none = some j ∧ j < C.sets.length ∧
      (C.sets.getD j 0).testBit (C.core.idxOf (v (n + 1))) = true ∧
        C.rank.getD j 0 ≤ C.rank.getD d 0 := by
  have hdet := List.all_eq_true.1 hc.det d (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  simp only [detOK, List.all_eq_true, List.mem_range, Bool.and_eq_true] at hdet
  have hrow := hdet.1 (t n) (hp.letter_lt n (by omega))
  have hT : (detSucc P C (C.sets.getD d 0) (P.letter (t n))).testBit (C.core.idxOf (v (n + 1)))
      = true := by
    rw [detSucc, testBit_orFold]
    refine ⟨C.core.idxOf (v n), mem_bits hbit, rfl, ?_⟩
    rw [getD_idxOf (mem_core hc hp hn)]
    exact testBit_succIdx (hp.edge n (by omega)) (mem_core hc hp (by omega))
  revert hrow
  cases (C.trans.getD d []).getD (t n) none with
  | none =>
    intro hrow
    simp only [beq_iff_eq] at hrow
    exact absurd hrow (ne_zero_of_testBit hT)
  | some j =>
    intro hrow
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hrow
    exact ⟨j, rfl, hrow.1.1, testBit_of_subset hrow.1.2 hT, hrow.2⟩

theorem detPath_spec {C : Cert} (hc : Checked P C) (hp : IsPath P N v t) (i : ℕ) :
    detPath C t (N + C.J) i < C.sets.length ∧
      (C.sets.getD (detPath C t (N + C.J) i) 0).testBit (C.core.idxOf (v (N + C.J + i))) = true := by
  induction i with
  | zero =>
    obtain ⟨hlen, -, -, -, h0⟩ := head_facts hc
    refine ⟨hlen, testBit_of_subset h0 ?_⟩
    rw [Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
    exact List.idxOf_lt_length_of_mem (mem_core hc hp (by omega))
  | succ i ih =>
    obtain ⟨j, he, hj, hb, -⟩ := step_entry hc hp (by omega) ih.1 ih.2
    have hdp : detPath C t (N + C.J) (i + 1) = next C (detPath C t (N + C.J) i)
        (t (N + C.J + i)) := rfl
    rw [hdp, show N + C.J + (i + 1) = N + C.J + i + 1 by omega]
    unfold next
    rw [he]
    exact ⟨hj, hb⟩

/-- The rank never increases along the det path, and keeping it forces the letter. -/
theorem detPath_rank {C : Cert} (hc : Checked P C) (hp : IsPath P N v t) (i : ℕ) :
    C.rank.getD (detPath C t (N + C.J) (i + 1)) 0 ≤ C.rank.getD (detPath C t (N + C.J) i) 0 ∧
      (C.rank.getD (detPath C t (N + C.J) (i + 1)) 0 = C.rank.getD (detPath C t (N + C.J) i) 0 →
        t (N + C.J + i) ∈ keep C P.nA (detPath C t (N + C.J) i)) := by
  obtain ⟨hi, hbit⟩ := detPath_spec hc hp i
  obtain ⟨j, he, -, -, hr⟩ := step_entry hc hp (by omega) hi hbit
  have hdp : detPath C t (N + C.J) (i + 1) = next C (detPath C t (N + C.J) i)
      (t (N + C.J + i)) := rfl
  rw [hdp]
  unfold next keep
  rw [he]
  refine ⟨hr, fun h => ?_⟩
  simp only [Option.getD_some] at h
  simp only [List.mem_filter, List.mem_range, he, h, beq_self_eq_true, and_true]
  exact hp.letter_lt _ (by omega)

theorem eq_headD_of_mem {l : List ℕ} (hl : l.length ≤ 1) {x : ℕ} (hx : x ∈ l) : x = l.headD 0 := by
  match l, hl, hx with
  | [_], _, hx => simpa using hx

/-- **The letter index of any path of a certified graph is eventually periodic.** -/
theorem isEventuallyPeriodic_of_path {C : Cert} (hc : Checked P C) (hp : IsPath P N v t) :
    IsEventuallyPeriodic t := by
  classical
  obtain ⟨d, hd⟩ : ∃ d, d = detPath C t (N + C.J) := ⟨_, rfl⟩
  have hspec : ∀ i, d i < C.sets.length := fun i => hd ▸ (detPath_spec hc hp i).1
  have hrank : ∀ i, C.rank.getD (d (i + 1)) 0 ≤ C.rank.getD (d i) 0 ∧
      (C.rank.getD (d (i + 1)) 0 = C.rank.getD (d i) 0 → t (N + C.J + i) ∈ keep C P.nA (d i)) :=
    fun i => hd ▸ detPath_rank hc hp i
  have hnext : ∀ i, d (i + 1) = next C (d i) (t (N + C.J + i)) := fun i => by rw [hd]; rfl
  have hanti : Antitone fun i => C.rank.getD (d i) 0 := antitone_nat_of_succ_le fun i => (hrank i).1
  -- the rank stabilizes
  have hex : ∃ k, ∃ i, C.rank.getD (d i) 0 = k := ⟨_, 0, rfl⟩
  obtain ⟨i₁, hi₁⟩ := Nat.find_spec hex
  have hconst : ∀ i, i₁ ≤ i → C.rank.getD (d i) 0 = C.rank.getD (d i₁) 0 := fun i hi =>
    le_antisymm (hanti hi) (hi₁ ▸ Nat.find_min' hex ⟨i, rfl⟩)
  -- from then on the det path is deterministic
  have hkeep : ∀ i, i < C.sets.length → (keep C P.nA i).length ≤ 1 := by
    intro i h
    have hdet := List.all_eq_true.1 hc.det i (List.mem_range'_1.2 ⟨by omega, by omega⟩)
    simp only [detOK, Bool.and_eq_true, decide_eq_true_eq] at hdet
    exact hdet.2
  have hstep : ∀ i, i₁ ≤ i → t (N + C.J + i) = (keep C P.nA (d i)).headD 0 ∧
      d (i + 1) = next C (d i) ((keep C P.nA (d i)).headD 0) := by
    intro i hi
    have hmem := (hrank i).2 (by rw [hconst (i + 1) (by omega), hconst i hi])
    have he := eq_headD_of_mem (hkeep _ (hspec i)) hmem
    exact ⟨he, by rw [← he, hnext]⟩
  -- pigeonhole
  have hpig := Fintype.exists_ne_map_eq_of_card_lt
    (fun m : Fin (C.sets.length + 1) => (⟨d (i₁ + m), hspec _⟩ : Fin C.sets.length)) (by simp)
  obtain ⟨m₁, m₂, hne, heq⟩ := hpig
  simp only [Fin.mk.injEq] at heq
  wlog hlt : (m₁ : ℕ) < m₂ generalizing m₁ m₂
  · exact this m₂ m₁ hne.symm heq.symm (by
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
      · exact absurd h hlt
      · exact h)
  have hshift : ∀ m, d (i₁ + m₁ + m) = d (i₁ + m₂ + m) := by
    intro m
    induction m with
    | zero => simpa using heq
    | succ m ih =>
      rw [show i₁ + m₁ + (m + 1) = (i₁ + m₁ + m) + 1 by omega,
        show i₁ + m₂ + (m + 1) = (i₁ + m₂ + m) + 1 by omega,
        (hstep _ (by omega)).2, (hstep _ (by omega)).2, ih]
  refine ⟨N + C.J + i₁ + m₁, m₂ - m₁, by omega, fun k hk => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, k = N + C.J + (i₁ + m₁ + m) := ⟨k - (N + C.J + i₁ + m₁), by omega⟩
  rw [show N + C.J + (i₁ + m₁ + m) + (m₂ - m₁) = N + C.J + (i₁ + m₂ + m) by omega,
    (hstep _ (by omega)).1, (hstep _ (by omega)).1, hshift]

end Path

end DubC2.Gen
