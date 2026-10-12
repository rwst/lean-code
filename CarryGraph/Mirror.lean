/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CarryGraph.Affine
import Mathlib.Data.ZMod.Basic

/-!
# The mirror `ν ↦ 1 − ν`

Reflecting `[0, 1)` and negating carries maps the affine system at the shift `ν` to the one at
`1 − ν`: the arc condition of a block graph is invariant under
`(I, J, ν, s) ↦ (1 − I, 1 − J, 1 − ν, −s)` (`blockArc_mirror`).  So the cell graph at `1 − ν`,
with the cells reversed and the letter window reversed, has exactly the arcs of the cell graph
at `ν` (`adj_cellGraph_mirror`); the residue graph is symmetric under `r ↦ −r` when the primes
divide the modulus (`adj_residueGraph_mirror`); and the affine graphs at `ν` and `1 − ν` are
isomorphic up to relabelling (`adj_affine_mirror`).  Every relabelling-invariant property
transfers, in particular the label form (`allPer_affine_mirror_iff`).

The half-open cells reflect to cells open on the other side, so the *covers* at `ν` and
`1 − ν` are not mirror images at the endpoints.  The graphs are, and each is a cover of its own
system (`cover_affine`); that is all the divisor theorem needs.

## Main results

* `allPer_iff_of_adj_equiv` — the label form transfers along a vertex bijection and a label
  bijection that match the arcs.
* `blockArc_mirror`, `cells_rev`, `adj_cellGraph_mirror`, `adj_residueGraph_mirror`,
  `adj_affine_mirror`, `allPer_affine_mirror_iff`.

## References

* [LM95] D. Lind, B. Marcus, *An Introduction to Symbolic Dynamics and Coding*, 1995.
-/

namespace CarryGraph

/-! ### Relabelling -/

/-- **The label form transfers along an arc-matching relabelling.** -/
@[category API, AMS 05 37, ref "LM95", group "carry_mirror"]
theorem allPer_iff_of_adj_equiv {V W A B : Type*} {X : CarryGraph V A} {Y : CarryGraph W B}
    (e : V ≃ W) (g : A ≃ B) (h : ∀ v a w, Y.Adj (e v) (g a) (e w) ↔ X.Adj v a w) :
    Y.AllPer ↔ X.AllPer := by
  constructor
  · intro hY s ℓ hs
    obtain ⟨n₀, L, hL, hper⟩ := hY (fun n => e (s n)) (fun n => g (ℓ n))
      fun n => (h _ _ _).2 (hs n)
    exact ⟨n₀, L, hL, fun m hm => g.injective (hper m hm)⟩
  · intro hX s ℓ hs
    obtain ⟨n₀, L, hL, hper⟩ := hX (fun n => e.symm (s n)) (fun n => g.symm (ℓ n))
      fun n => (h _ _ _).1 (by simpa using hs n)
    exact ⟨n₀, L, hL, fun m hm => g.symm.injective (hper m hm)⟩

variable {p q : ℕ}

/-! ### Block and cell graphs -/

/-- **The arc condition is mirror-symmetric.** -/
@[category textbook, AMS 11 37 05, group "carry_mirror"]
theorem blockArc_mirror (ν : ℝ) (I J : ℚ × ℚ) (s : ℤ) :
    BlockArc p q (1 - ν) (1 - I.2, 1 - I.1) (1 - J.2, 1 - J.1) (-s) ↔
      BlockArc p q ν I J s := by
  simp only [BlockArc]
  push_cast
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith

/-- The reversed cell is the reflected cell. -/
@[category API, AMS 11, group "carry_mirror"]
theorem cells_rev {D : ℕ} (c : Fin D) :
    cells D c.rev = (1 - (cells D c).2, 1 - (cells D c).1) := by
  have hD : (D : ℚ) ≠ 0 := by
    have := c.pos; positivity
  have hc : ((c.rev : ℕ) : ℚ) = D - 1 - c := by
    rw [Fin.val_rev, Nat.cast_sub (by omega)]
    push_cast
    ring
  simp only [cells, hc, Prod.mk.injEq]
  constructor <;> field_simp <;> ring

/-- The reversed letter of the reversed window is the negated carry. -/
theorem letter_rev {s₀ : ℤ} {nA : ℕ} (t : Fin nA) :
    (-(s₀ + nA - 1) + ((t.rev : ℕ) : ℤ)) = -(s₀ + t) := by
  rw [Fin.val_rev]
  have := t.2
  omega

/-- **The mirror cell graph**: at `1 − ν`, with cells and letter window reversed, the cell graph
has the arcs of the cell graph at `ν`. -/
@[category textbook, AMS 11 37 05, group "carry_mirror"]
theorem adj_cellGraph_mirror {ν : ℚ} {s₀ : ℤ} {nA D : ℕ} {c d : Fin D} {t : Fin nA} :
    (cellGraph p q (1 - ν) (-(s₀ + nA - 1)) nA D).Adj c.rev t.rev d.rev ↔
      (cellGraph p q ν s₀ nA D).Adj c t d := by
  simp only [cellGraph, adj_blockGraph, cells_rev, letter_rev]
  push_cast
  exact blockArc_mirror (ν : ℝ) (cells D c) (cells D d) (s₀ + t)

/-! ### Residue graphs -/

/-- Residue avoidance is sign-blind when the primes divide the modulus. -/
@[category API, AMS 11, group "carry_mirror"]
theorem resOK_neg {M : ℕ} [NeZero M] {PM : List ℕ} (hPM : ∀ ℓ ∈ PM, ℓ ∣ M) (r : ZMod M) :
    ResOK PM (-r) ↔ ResOK PM r := by
  simp only [ResOK]
  refine forall₂_congr fun ℓ hℓ => not_congr ?_
  rw [ZMod.neg_val]
  split_ifs with h
  · subst h; simp
  · have hlt := ZMod.val_lt r
    have hdvd : (ℓ : ℤ) ∣ M := by exact_mod_cast hPM ℓ hℓ
    rw [Nat.cast_sub hlt.le]
    constructor
    · intro h'; simpa using (dvd_sub hdvd h')
    · intro h'; exact dvd_sub hdvd h'

/-- **The mirror residue graph**: `r ↦ −r`, carries negated. -/
@[category textbook, AMS 11 37 05, group "carry_mirror"]
theorem adj_residueGraph_mirror {M : ℕ} [NeZero M] {s₀ : ℤ} {nA : ℕ} {PM Pq : List ℕ}
    (hPM : ∀ ℓ ∈ PM, ℓ ∣ M) {r r' : ZMod M} {t : Fin nA} :
    (residueGraph p q M (-(s₀ + nA - 1)) nA PM Pq).Adj (-r) t.rev (-r') ↔
      (residueGraph p q M s₀ nA PM Pq).Adj r t r' := by
  simp only [adj_residueGraph, resOK_neg hPM, letter_rev, Avoid, dvd_neg]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_left fun _ => ?_
  push_cast
  constructor
  · intro h; linear_combination -h
  · intro h; linear_combination -h

/-! ### Affine graphs -/

/-- **The mirror affine graph**: at `1 − ν`, with residues negated, cells reversed and the letter
window reversed, the affine graph has the arcs of the affine graph at `ν`. -/
@[category textbook, AMS 11 37 05, group "carry_mirror"]
theorem adj_affine_mirror {ν : ℚ} {s₀ : ℤ} {nA M D : ℕ} [NeZero M] {PM Pq : List ℕ}
    (hPM : ∀ ℓ ∈ PM, ℓ ∣ M) {v w : ZMod M × Fin D} {t : Fin nA} :
    (affine p q (1 - ν) (-(s₀ + nA - 1)) nA M D PM Pq).Adj (-v.1, v.2.rev) t.rev
        (-w.1, w.2.rev) ↔
      (affine p q ν s₀ nA M D PM Pq).Adj v t w := by
  simp only [affine, adj_labelProduct]
  exact and_congr (adj_residueGraph_mirror hPM) adj_cellGraph_mirror

/-- **The label form is mirror-invariant**: the affine graph at `ν` has it iff the affine graph at
`1 − ν` (letter window reversed) has it. -/
@[category research solved, AMS 11 37 05, ref "LM95", group "carry_mirror"]
theorem allPer_affine_mirror_iff {ν : ℚ} {s₀ : ℤ} {nA M D : ℕ} [NeZero M] {PM Pq : List ℕ}
    (hPM : ∀ ℓ ∈ PM, ℓ ∣ M) :
    (affine p q (1 - ν) (-(s₀ + nA - 1)) nA M D PM Pq).AllPer ↔
      (affine p q ν s₀ nA M D PM Pq).AllPer :=
  allPer_iff_of_adj_equiv ((Equiv.neg _).prodCongr Fin.revPerm) Fin.revPerm
    fun _ _ _ => adj_affine_mirror hPM

end CarryGraph
