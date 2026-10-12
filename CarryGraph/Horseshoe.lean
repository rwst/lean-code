/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CarryGraph.Growth
import Mathlib.Data.Nat.Log

/-!
# Horseshoes ([LM95] §4.1, §4.4)

A **horseshoe** at a vertex `v` is a family of pairwise distinct closed labelled walks at `v`,
all of one length `L > 0` (a *rose* of `|ι|` petals).  Any choice of petals, one per block,
is an infinite labelled path (`Horseshoe.isIPath`), distinct choices give distinct paths
(`Horseshoe.block_injective`), so the full shift on `ι` embeds and

* `|ι|^k ≤ npaths v (k L)` (`Horseshoe.pow_le_npaths`), hence `log |ι| / L ≤ entropy`
  (`Horseshoe.log_card_div_le_entropy`);
* with two petals, choosing petal 1 exactly in the blocks numbered by a power of two gives an
  infinite path that is not eventually periodic (`Horseshoe.exists_not_evPer`).

Conversely, a vertex with two distinct arcs inside its strong component carries a two-petal
horseshoe (`exists_horseshoe_of_branch`): the two return loops, concatenated in both orders,
have one length.  This is the generic content of `Z32.Horse.card_modelLang_ge` and
`DubC2.Gen.Horse`.

## Contents

* `IsLWalk`, `IsLWalk.cons`, `IsLWalk.append`, `exists_lWalk_of_reach`.
* `card_le_npaths` — distinct labelled walks of length `n` from `v` number at most `npaths v n`.
* `Horseshoe`, `Horseshoe.blockS`, `Horseshoe.blockL`, `Horseshoe.isIPath`,
  `Horseshoe.block_injective`, `Horseshoe.pow_le_npaths`, `Horseshoe.log_card_div_le_entropy`,
  `Horseshoe.exists_not_evPer`.
* `exists_horseshoe_of_branch`.

## References

* [LM95] D. Lind, B. Marcus, *An Introduction to Symbolic Dynamics and Coding*, Cambridge UP,
  1995.
-/

namespace CarryGraph

variable {V A : Type*} {X : CarryGraph V A}

/-! ### Labelled walks -/

variable (X) in
/-- `g, ℓ` is a labelled walk of length `n`: `g 0 →[ℓ 0] g 1 → ⋯ → g n`. -/
def IsLWalk (g : ℕ → V) (ℓ : ℕ → A) (n : ℕ) : Prop := ∀ i < n, X.Adj (g i) (ℓ i) (g (i + 1))

/-- Prepend one arc to a labelled walk. -/
@[category API, AMS 05, group "carry_horseshoe"]
theorem IsLWalk.cons {g : ℕ → V} {ℓ : ℕ → A} {n : ℕ} (hg : X.IsLWalk g ℓ n) {x : V} {a : A}
    (hx : X.Adj x a (g 0)) :
    X.IsLWalk (fun i => if i = 0 then x else g (i - 1)) (fun i => if i = 0 then a else ℓ (i - 1))
      (n + 1) := by
  intro i hi
  rcases i with _ | i
  · simpa using hx
  · simpa using hg i (by omega)

/-- Concatenation of two labelled walks. -/
@[category API, AMS 05, group "carry_horseshoe"]
theorem IsLWalk.append {g h : ℕ → V} {ℓ ℓ' : ℕ → A} {m n : ℕ} (hg : X.IsLWalk g ℓ m)
    (hh : X.IsLWalk h ℓ' n) (hj : g m = h 0) :
    X.IsLWalk (fun i => if i ≤ m then g i else h (i - m))
      (fun i => if i < m then ℓ i else ℓ' (i - m)) (m + n) := by
  intro i hi
  by_cases h1 : i + 1 ≤ m
  · simpa [h1, show i ≤ m by omega, show i < m by omega] using hg i (by omega)
  · by_cases h2 : i = m
    · subst h2
      simpa [hj] using hh 0 (by omega)
    · have e : i + 1 - m = (i - m) + 1 := by omega
      simpa [h1, show ¬ i ≤ m by omega, show ¬ i < m by omega, e] using hh (i - m) (by omega)

/-- A path in the unlabelled graph lifts to a labelled walk (`a₀` is a dummy label for the
empty walk). -/
@[category API, AMS 05, group "carry_horseshoe"]
theorem exists_lWalk_of_reach (a₀ : A) {x y : V} (h : X.Reach x y) :
    ∃ n g ℓ, g 0 = x ∧ g n = y ∧ X.IsLWalk g ℓ n := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, fun _ => y, fun _ => a₀, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | head hxz _ ih =>
    obtain ⟨n, g, ℓ, hg0, hgn, hg⟩ := ih
    obtain ⟨a, ha⟩ := hxz
    exact ⟨n + 1, _, _, by simp, by simpa using hgn, hg.cons (hg0 ▸ ha)⟩

/-! ### Counting distinct walks -/

section count

variable [Fintype A]

/-- **Distinct walks are counted by `npaths`**: a family of labelled walks of length `n` from
`v`, pairwise distinct as arc sequences, has at most `npaths v n` members. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_horseshoe"]
theorem card_le_npaths {T : Type*} (F : Finset T) :
    ∀ (n : ℕ) (v : V) (s : T → ℕ → V) (ℓ : T → ℕ → A),
      (∀ t ∈ F, s t 0 = v ∧ X.IsLWalk (s t) (ℓ t) n) →
      (∀ t ∈ F, ∀ t' ∈ F, (∀ i < n, ℓ t i = ℓ t' i ∧ s t (i + 1) = s t' (i + 1)) → t = t') →
      F.card ≤ X.npaths v n
  | 0, v, s, ℓ, _, hinj => by
    rw [npaths_zero]
    exact Finset.card_le_one.2 fun t ht t' ht' =>
      hinj t ht t' ht' fun i hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, v, s, ℓ, hw, hinj => by
    classical
    let f : T → Σ _ : A, V := fun t => ⟨ℓ t 0, s t 1⟩
    have hf : ∀ t ∈ F, f t ∈ X.arcsFrom v := fun t ht => by
      have := (hw t ht).2 0 (by omega)
      rw [(hw t ht).1] at this
      exact mem_arcsFrom.2 this
    rw [Finset.card_eq_sum_card_fiberwise hf, npaths_succ']
    refine Finset.sum_le_sum fun x _ => ?_
    refine card_le_npaths _ n x.2 (fun t i => s t (i + 1)) (fun t i => ℓ t (i + 1)) ?_ ?_
    · intro t ht
      simp only [Finset.mem_filter] at ht
      refine ⟨?_, fun i hi => (hw t ht.1).2 (i + 1) (by omega)⟩
      rw [← ht.2]
    · intro t ht t' ht' hagree
      simp only [Finset.mem_filter] at ht ht'
      have h0 : f t = f t' := ht.2.trans ht'.2.symm
      simp only [f, Sigma.mk.inj_iff, heq_eq_eq] at h0
      refine hinj t ht.1 t' ht'.1 fun i hi => ?_
      rcases i with _ | i
      · exact h0
      · exact hagree i (by omega)

end count

/-! ### Horseshoes -/

variable (X) in
/-- A **horseshoe** at `v` with petals indexed by `ι`: closed labelled walks at `v` of one
length `L > 0`, pairwise distinct as arc sequences. -/
structure Horseshoe (v : V) (ι : Type*) where
  /-- The common length of the petals. -/
  L : ℕ
  pos : 0 < L
  /-- The vertices of the petals. -/
  g : ι → ℕ → V
  /-- The labels of the petals. -/
  ℓ : ι → ℕ → A
  start : ∀ i, g i 0 = v
  stop : ∀ i, g i L = v
  walk : ∀ i, X.IsLWalk (g i) (ℓ i) L
  distinct : ∀ i j, (∀ m < L, ℓ i m = ℓ j m ∧ g i (m + 1) = g j (m + 1)) → i = j

namespace Horseshoe

variable {v : V} {ι : Type*} (H : X.Horseshoe v ι)

/-- The vertex sequence of the block path reading petal `b k` in block `k`. -/
def blockS (b : ℕ → ι) (n : ℕ) : V := H.g (b (n / H.L)) (n % H.L)

/-- The label sequence of the block path. -/
def blockL (b : ℕ → ι) (n : ℕ) : A := H.ℓ (b (n / H.L)) (n % H.L)

@[category API, AMS 05, group "carry_horseshoe"]
theorem div_mod_block {q r : ℕ} (hr : r < H.L) :
    (H.L * q + r) / H.L = q ∧ (H.L * q + r) % H.L = r :=
  ⟨by rw [Nat.mul_add_div H.pos, Nat.div_eq_of_lt hr, add_zero],
    by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]⟩

@[category API, AMS 05, group "carry_horseshoe"]
theorem blockS_block (b : ℕ → ι) {q r : ℕ} (hr : r < H.L) :
    H.blockS b (H.L * q + r) = H.g (b q) r := by
  rw [blockS, (H.div_mod_block hr).1, (H.div_mod_block hr).2]

@[category API, AMS 05, group "carry_horseshoe"]
theorem blockL_block (b : ℕ → ι) {q r : ℕ} (hr : r < H.L) :
    H.blockL b (H.L * q + r) = H.ℓ (b q) r := by
  rw [blockL, (H.div_mod_block hr).1, (H.div_mod_block hr).2]

/-- The vertex after position `r` of block `q` is the petal's next vertex, also at the block
boundary (where both are `v`). -/
@[category API, AMS 05, group "carry_horseshoe"]
theorem blockS_block_succ (b : ℕ → ι) {q r : ℕ} (hr : r < H.L) :
    H.blockS b (H.L * q + r + 1) = H.g (b q) (r + 1) := by
  by_cases hlt : r + 1 < H.L
  · rw [add_assoc, H.blockS_block b hlt]
  · have hrL : r + 1 = H.L := by omega
    rw [hrL, H.stop, show H.L * q + r + 1 = H.L * (q + 1) + 0 by rw [add_assoc, hrL]; ring,
      H.blockS_block b H.pos, H.start]

/-- **Every choice of petals is an infinite labelled path.** -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_horseshoe"]
theorem isIPath (b : ℕ → ι) : X.IsIPath (H.blockS b) (H.blockL b) := by
  intro n
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < H.L ∧ n = H.L * q + r :=
    ⟨n / H.L, n % H.L, Nat.mod_lt _ H.pos, (Nat.div_add_mod n H.L).symm⟩
  rw [H.blockS_block b hr, H.blockL_block b hr, H.blockS_block_succ b hr]
  exact H.walk _ r hr

@[category API, AMS 05, group "carry_horseshoe"]
theorem blockS_zero (b : ℕ → ι) : H.blockS b 0 = v := by
  simp [blockS, Nat.zero_div, Nat.zero_mod, H.start]

/-- Agreement of two block paths on the first `k` blocks forces the same petals there. -/
@[category API, AMS 05, group "carry_horseshoe"]
theorem eq_of_agree {b b' : ℕ → ι} {k : ℕ}
    (h : ∀ i < k * H.L, H.blockL b i = H.blockL b' i ∧ H.blockS b (i + 1) = H.blockS b' (i + 1))
    {j : ℕ} (hj : j < k) : b j = b' j := by
  refine H.distinct _ _ fun m hm => ?_
  have hi : H.L * j + m < k * H.L := by nlinarith
  obtain ⟨h1, h2⟩ := h _ hi
  rw [H.blockL_block b hm, H.blockL_block b' hm] at h1
  rw [H.blockS_block_succ b hm, H.blockS_block_succ b' hm] at h2
  exact ⟨h1, h2⟩

/-- **The full shift on `ι` embeds**: distinct petal sequences give distinct paths. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_horseshoe"]
theorem block_injective {b b' : ℕ → ι}
    (h : ∀ n, H.blockL b n = H.blockL b' n ∧ H.blockS b n = H.blockS b' n) : b = b' :=
  funext fun j => H.eq_of_agree (k := j + 1) (fun i _ => ⟨(h i).1, (h (i + 1)).2⟩) (by omega)

/-- **A horseshoe with `|ι|` petals of length `L` gives `|ι|^k ≤ npaths v (k L)`.** -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_horseshoe"]
theorem pow_le_npaths [Fintype A] [Fintype ι] [Nonempty ι] (k : ℕ) :
    Fintype.card ι ^ k ≤ X.npaths v (k * H.L) := by
  classical
  let ext : (Fin k → ι) → ℕ → ι := fun b j =>
    if hj : j < k then b ⟨j, hj⟩ else Classical.arbitrary ι
  have := card_le_npaths (X := X) (Finset.univ : Finset (Fin k → ι)) (k * H.L) v
    (fun b => H.blockS (ext b)) (fun b => H.blockL (ext b))
    (fun b _ => ⟨H.blockS_zero _, fun i _ => H.isIPath _ i⟩)
    (fun b _ b' _ hagree => funext fun j => by
      have := H.eq_of_agree hagree j.2
      simpa [ext] using this)
  simpa [Fintype.card_fun] using this

/-- **Horseshoe entropy bound**: `log |ι| / L ≤ entropy`. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_horseshoe"]
theorem log_card_div_le_entropy [Fintype V] [Fintype A] [Fintype ι] [Nonempty ι] :
    ((Real.log (Fintype.card ι) / H.L : ℝ) : EReal) ≤ X.entropy :=
  log_div_le_entropy Fintype.card_pos H.pos H.pow_le_npaths

/-! ### An aperiodic path -/

/-- The indicator of the powers of two. -/
def isPow2 (k : ℕ) : Bool := decide (2 ^ Nat.log 2 k = k)

@[category API, AMS 05, group "carry_horseshoe"]
theorem isPow2_pow (j : ℕ) : isPow2 (2 ^ j) = true := by
  simp [isPow2, Nat.log_pow (by norm_num : 1 < 2)]

@[category API, AMS 05, group "carry_horseshoe"]
theorem isPow2_of_lt {j x : ℕ} (h1 : 2 ^ j < x) (h2 : x < 2 ^ (j + 1)) : isPow2 x = false := by
  have hl : Nat.log 2 x = j := Nat.log_eq_of_pow_le_of_lt_pow h1.le h2
  simp only [isPow2, hl, decide_eq_false_iff_not]
  omega

/-- The powers-of-two indicator is not eventually periodic. -/
@[category API, AMS 05, group "carry_horseshoe"]
theorem isPow2_not_evPer (n₀ P : ℕ) (hP : 0 < P) : ∃ k, n₀ ≤ k ∧ isPow2 (k + P) ≠ isPow2 k := by
  refine ⟨2 ^ (n₀ + P), ?_, ?_⟩
  · exact (Nat.lt_two_pow_self (n := n₀ + P)).le.trans' (by omega)
  · have hLt : P < 2 ^ (n₀ + P) := (Nat.lt_two_pow_self (n := P)).trans_le
      (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [isPow2_pow, isPow2_of_lt (j := n₀ + P) (by omega) (by rw [pow_succ]; omega)]
    simp

/-- Iterating a period. -/
@[category API, AMS 05, group "carry_horseshoe"]
theorem periodic_iter {α : Type*} {s : ℕ → α} {n₀ P : ℕ} (h : ∀ m, n₀ ≤ m → s (m + P) = s m)
    (m : ℕ) (hm : n₀ ≤ m) (k : ℕ) : s (m + k * P) = s m := by
  induction k with
  | zero => simp
  | succ k ih => rw [show m + (k + 1) * P = (m + k * P) + P by ring, h _ (by omega), ih]

include H in
/-- **Two petals give an infinite path that is not eventually periodic**: read petal `i` in
the blocks numbered by powers of two and petal `j` elsewhere. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_horseshoe"]
theorem exists_not_evPer {i j : ι} (hij : i ≠ j) :
    ∃ s ℓ, s 0 = v ∧ X.IsIPath s ℓ ∧
      ¬ ∃ n₀ P, 0 < P ∧ ∀ m, n₀ ≤ m → s (m + P) = s m ∧ ℓ (m + P) = ℓ m := by
  let b : ℕ → ι := fun k => if isPow2 k then i else j
  refine ⟨H.blockS b, H.blockL b, H.blockS_zero b, H.isIPath b, ?_⟩
  rintro ⟨n₀, P, hP, hper⟩
  obtain ⟨m, hm, hne⟩ : ∃ m < H.L, ¬ (H.ℓ i m = H.ℓ j m ∧ H.g i (m + 1) = H.g j (m + 1)) := by
    by_contra! hc
    exact hij (H.distinct i j hc)
  obtain ⟨k, hk, hkne⟩ := isPow2_not_evPer n₀ P hP
  have hx : n₀ ≤ H.L * k + m := le_trans hk (by nlinarith [H.pos])
  have hS := periodic_iter (s := H.blockS b) (fun m hm => (hper m hm).1) (H.L * k + m + 1)
    (by omega) H.L
  have hL := periodic_iter (s := H.blockL b) (fun m hm => (hper m hm).2) (H.L * k + m) hx H.L
  rw [show H.L * k + m + 1 + H.L * P = H.L * (k + P) + m + 1 by ring,
    H.blockS_block_succ b hm, H.blockS_block_succ b hm] at hS
  rw [show H.L * k + m + H.L * P = H.L * (k + P) + m by ring,
    H.blockL_block b hm, H.blockL_block b hm] at hL
  apply hne
  simp only [b] at hS hL
  revert hS hL hkne
  cases isPow2 (k + P) <;> cases isPow2 k <;> simp_all [eq_comm]

end Horseshoe

/-- **Branching gives a two-petal horseshoe**: if `v →[a] t` and `v →[b] u` are distinct arcs
whose targets return to `v`, the return loops through `t` and through `u`, concatenated in both
orders, are two distinct closed walks of one length. -/
@[category textbook, AMS 05 37, ref "LM95", group "carry_horseshoe"]
theorem exists_horseshoe_of_branch {v t u : V} {a b : A} (hvt : X.Adj v a t) (hvu : X.Adj v b u)
    (hne : ¬ (a = b ∧ t = u)) (htv : X.Reach t v) (huv : X.Reach u v) :
    Nonempty (X.Horseshoe v Bool) := by
  obtain ⟨n₁, g₁, ℓ₁, hg₁0, hg₁n, hg₁⟩ := exists_lWalk_of_reach a htv
  obtain ⟨n₂, g₂, ℓ₂, hg₂0, hg₂n, hg₂⟩ := exists_lWalk_of_reach a huv
  have hc₁ := hg₁.cons (x := v) (a := a) (hg₁0 ▸ hvt)
  have hc₂ := hg₂.cons (x := v) (a := b) (hg₂0 ▸ hvu)
  set c₁ : ℕ → V := fun i => if i = 0 then v else g₁ (i - 1)
  set c₂ : ℕ → V := fun i => if i = 0 then v else g₂ (i - 1)
  set d₁ : ℕ → A := fun i => if i = 0 then a else ℓ₁ (i - 1)
  set d₂ : ℕ → A := fun i => if i = 0 then b else ℓ₂ (i - 1)
  have e₁ : c₁ (n₁ + 1) = v := by simp [c₁, hg₁n]
  have e₂ : c₂ (n₂ + 1) = v := by simp [c₂, hg₂n]
  have hA := hc₁.append hc₂ (by rw [e₁]; simp [c₂])
  have hB := hc₂.append hc₁ (by rw [e₂]; simp [c₁])
  have hN : n₂ + 1 + (n₁ + 1) = n₁ + 1 + (n₂ + 1) := by ring
  rw [hN] at hB
  refine ⟨{
    L := n₁ + 1 + (n₂ + 1)
    pos := by omega
    g := fun c => if c then (fun i => if i ≤ n₁ + 1 then c₁ i else c₂ (i - (n₁ + 1)))
      else (fun i => if i ≤ n₂ + 1 then c₂ i else c₁ (i - (n₂ + 1)))
    ℓ := fun c => if c then (fun i => if i < n₁ + 1 then d₁ i else d₂ (i - (n₁ + 1)))
      else (fun i => if i < n₂ + 1 then d₂ i else d₁ (i - (n₂ + 1)))
    start := fun c => by cases c <;> simp [c₁, c₂]
    stop := fun c => by
      cases c
      · simp only [Bool.false_eq_true, ↓reduceIte]
        simp only [show ¬ (n₁ + 1 + (n₂ + 1) ≤ n₂ + 1) by omega, ↓reduceIte]
        rw [show n₁ + 1 + (n₂ + 1) - (n₂ + 1) = n₁ + 1 by omega, e₁]
      · simp only [↓reduceIte]
        simp only [show ¬ (n₁ + 1 + (n₂ + 1) ≤ n₁ + 1) by omega, ↓reduceIte]
        rw [show n₁ + 1 + (n₂ + 1) - (n₁ + 1) = n₂ + 1 by omega, e₂]
    walk := fun c => by
      cases c
      · simpa using hB
      · simpa using hA
    distinct := fun c c' h => by
      by_contra hcc
      obtain ⟨h1, h2⟩ := h 0 (by omega)
      apply hne
      cases c <;> cases c' <;> simp_all [c₁, c₂, d₁, d₂, eq_comm] }⟩

end CarryGraph
