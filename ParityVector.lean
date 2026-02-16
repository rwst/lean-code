import Mathlib.Data.List.Basic
import Mathlib.Data.List.Infix
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

-- 1. Representation of Parity Vectors
-- Definition 2.1: Parity vectors are essentially binary words.
-- We represent 0 as `false` and 1 as `true`.
def ParityVector := List Bool

deriving instance DecidableEq for ParityVector

namespace ParityVector

-- Helper to interpret Bool as Nat (0 or 1) for summation contexts later
def toNat (b : Bool) : ℕ := if b then 1 else 0

-- 2. Definition 2.2: The Elementary Precedence Relation
-- "V = <w1 0 1 w2> and V' = <w1 1 0 w2> ... we say V strictly precedes V'"
-- This represents shifting a 1 to the left.
inductive ElementaryPrecedes : ParityVector → ParityVector → Prop
  | swap (w1 w2 : List Bool) :
      -- Replaces [false, true] (01) with [true, false] (10)
      ElementaryPrecedes (w1 ++ [false, true] ++ w2) (w1 ++ [true, false] ++ w2)

-- 3. Definition 2.2: The Partial Order (preceq)
-- "We extend this relation by adding transitivity... V preceq V' if V ≺ V' or V = V'"
-- In Lean, this is the Reflexive Transitive Closure of the elementary relation.
def Precedes (v1 v2 : ParityVector) : Prop :=
  Relation.ReflTransGen ElementaryPrecedes v1 v2

-- Notation for convenience
infix:50 " ≼ " => Precedes

/-- `q v` is the number of ones (true entries) in the parity vector `v`. -/
def q (v : ParityVector) : ℕ := v.count true

/-- The size (length) of a parity vector. -/
def size (v : ParityVector) : ℕ := v.length

/-- The ones-ratio `q / size` as a rational number. Returns 0 for the empty vector. -/
def onesRatio (v : ParityVector) : ℚ := (q v : ℚ) / (size v : ℚ)

/-- The partial sum `∑_{i=0}^{k} toNat(v[i])`, i.e., the number of ones
    among the first `k + 1` entries of `v`. -/
def partialSum (v : ParityVector) (k : ℕ) : ℕ :=
  ((v.take (k + 1)).map toNat).sum

/-- **Unordered majorization characterization.** For two parity vectors `v` and `v'` of the
    same length `j`, we have `v ≼ v'` if and only if:
    (i)  `∑_{i=0}^{k} vᵢ ≤ ∑_{i=0}^{k} v'ᵢ` for all `0 ≤ k ≤ j - 2`, and
    (ii) `∑_{i=0}^{j-1} vᵢ = ∑_{i=0}^{j-1} v'ᵢ` (equal total number of ones).
    See [10, §5.D, p. 198]. -/
theorem precedes_iff_majorization (v v' : ParityVector) (hlen : v.length = v'.length) :
    v ≼ v' ↔
      (∀ k, k + 2 ≤ v.length → partialSum v k ≤ partialSum v' k) ∧
      q v = q v' := by
  sorry

-- Weight metric: sum of indices where v[i] = true
-- W(v) = Σ {i | v[i] = true}
-- We define it via enumFrom for easier reasoning about appends.
def weightFrom (start : ℕ) : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then start else 0) + weightFrom (start + 1) bs

def weight (v : ParityVector) : ℕ := weightFrom 0 v

-- Key lemma: weightFrom distributes over append
theorem weightFrom_append (n : ℕ) (xs ys : List Bool) :
    weightFrom n (xs ++ ys) = weightFrom n xs + weightFrom (n + xs.length) ys := by
  induction xs generalizing n with
  | nil => simp [weightFrom]
  | cons x xs ih =>
    simp only [List.cons_append, weightFrom, List.length_cons]
    have : n + 1 + xs.length = n + (xs.length + 1) := by omega
    rw [ih, this]
    omega

-- Elementary swap strictly decreases weight
theorem elementary_weight_decrease {v1 v2 : ParityVector}
    (h : ElementaryPrecedes v1 v2) : weight v2 < weight v1 := by
  cases h with
  | swap w1 w2 =>
    simp only [weight, weightFrom_append]
    simp only [List.length_cons, List.length_nil, List.length_append]
    simp only [weightFrom, Bool.false_eq_true, ↓reduceIte]
    omega

-- Precedes implies weight is non-increasing
theorem precedes_weight_le {v1 v2 : ParityVector}
    (h : v1 ≼ v2) : weight v2 ≤ weight v1 := by
  induction h with
  | refl => exact le_refl _
  | tail _ hab ih =>
    have := elementary_weight_decrease hab
    omega

-- TransGen (at least one step) implies strictly less weight
theorem transGen_weight_lt {v1 v2 : ParityVector}
    (h : Relation.TransGen ElementaryPrecedes v1 v2) : weight v2 < weight v1 := by
  induction h with
  | single hab => exact elementary_weight_decrease hab
  | tail _ hab ih =>
    have := elementary_weight_decrease hab
    omega

-- If v1 ≼ v2 and weights are equal, then v1 = v2
theorem precedes_eq_of_weight_eq {v1 v2 : ParityVector}
    (h : v1 ≼ v2) (hw : weight v1 = weight v2) : v1 = v2 := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp h with rfl | htrans
  · rfl
  · exact absurd hw (Nat.ne_of_gt (transGen_weight_lt htrans))

-- 4. Proof that this forms a Partial Order
instance : PartialOrder ParityVector where
  le := Precedes
  le_refl := fun _ => Relation.ReflTransGen.refl
  le_trans := fun _ _ _ hab hbc => Relation.ReflTransGen.trans hab hbc
  le_antisymm := by
    intro v1 v2 h12 h21
    have hle1 := precedes_weight_le h12
    have hle2 := precedes_weight_le h21
    exact precedes_eq_of_weight_eq h12 (Nat.le_antisymm hle2 hle1)

-- 5. The associated directed graph of the partial order is acyclic (a DAG).
-- The vertices are parity vectors and the edges are given by `ElementaryPrecedes`.

/-- `ElementaryPrecedes` is irreflexive: no parity vector precedes itself. -/
theorem elementaryPrecedes_irrefl (v : ParityVector) : ¬ ElementaryPrecedes v v := by
  sorry

/-- `ElementaryPrecedes` is acyclic: there is no non-trivial cycle. -/
theorem elementaryPrecedes_acyclic (v : ParityVector) :
    ¬ Relation.TransGen ElementaryPrecedes v v := by
  sorry

/-- `ElementaryPrecedes` is well-founded, i.e., there are no infinite descending chains.
    Together with the directed edges of `ElementaryPrecedes`, this makes the associated
    graph a finite directed acyclic graph (DAG). -/
theorem elementaryPrecedes_wellFounded : WellFounded ElementaryPrecedes := by
  sorry

end ParityVector
