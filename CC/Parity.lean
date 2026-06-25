import CC.Terras

namespace CC

/-- Parity vectors are essentially binary words. We represent 0 as `false` and 1 as `true`. -/
def ParityVector := List Bool

deriving instance DecidableEq for ParityVector

instance : GetElem ParityVector ℕ Bool fun v i => i < v.length :=
  inferInstanceAs (GetElem (List Bool) ℕ Bool _)

def toNat (b : Bool) : ℕ := if b then 1 else 0

/-- `q v` is the number of ones (true entries) in the parity vector `v`. -/
def q (v : ParityVector) : ℕ := v.count true

/-- The size (length) of a parity vector. -/
def size (v : ParityVector) : ℕ := v.length

/-- The ones-ratio `q / size` as a rational number. Returns 0 for the empty vector. -/
def onesRatio (v : ParityVector) : ℚ := (q v : ℚ) / (size v : ℚ)

/-- `V j n` is the parity vector of length `j` for the Collatz sequence starting at `n`. -/
def V (j n : ℕ) : ParityVector :=
  (List.finRange j).map (fun i => decide (X (T_iter i.val n) = 1))

@[simp]
lemma V_length (j n : ℕ) : (V j n).length = j := by
  simp [V]

lemma V_get (j n : ℕ) (i : Fin j) :
    (V j n).get ⟨i.val, by simp [V_length]⟩ = decide (X (T_iter i.val n) = 1) := by
  simp [V]


/-- The elementary precedence relation (swapping 01 to 10). -/
inductive ElementaryPrecedes : ParityVector → ParityVector → Prop
  | swap (w1 w2 : List Bool) :
      ElementaryPrecedes (w1 ++ [false, true] ++ w2) (w1 ++ [true, false] ++ w2)

/-- reflexive transitive closure of the elementary relation. -/
def Precedes (v1 v2 : ParityVector) : Prop :=
  Relation.ReflTransGen ElementaryPrecedes v1 v2

infix:50 " ≼ " => Precedes

/-- `E_vec k n` is the parity vector `(X(n), X(T n), …, X(T^{k-1} n))` as a function `Fin k → ℕ`,
    where each entry is 0 or 1. -/
def E_vec (k : ℕ) (n : ℕ) : Fin k → ℕ :=
  fun i => X (T_iter i.val n)

@[simp]
lemma E_vec_apply (k n : ℕ) (i : Fin k) : E_vec k n i = X (T_iter i.val n) := rfl

lemma E_vec_le_one (k n : ℕ) (i : Fin k) : E_vec k n i ≤ 1 := by
  simp only [E_vec_apply, X_eq_mod]; omega

lemma num_odd_steps_eq_E_vec_sum (k n : ℕ) :
    num_odd_steps k n = Finset.sum Finset.univ (E_vec k n) := by
  simp [num_odd_steps, E_vec]; exact Finset.sum_range _

lemma E_vec_restrict (k m n : ℕ) (h : E_vec (k + 1) m = E_vec (k + 1) n) :
    E_vec k m = E_vec k n := by
  ext ⟨i, hi⟩
  have := congr_fun h ⟨i, by omega⟩
  simpa [E_vec_apply] using this

lemma num_odd_steps_eq_of_E_vec_eq (k m n : ℕ) (h : E_vec k m = E_vec k n) :
    num_odd_steps k m = num_odd_steps k n := by
  simp only [num_odd_steps]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have := congr_fun h ⟨i, hi⟩
  simpa [E_vec_apply] using this

end CC
