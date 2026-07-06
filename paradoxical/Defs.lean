import CC.Elementary
import CC.Terras

open CC

/-- One step of the integer-remainder recursion on a parity bit `x ∈ {0,1}`:
    state `(p2, s) ↦ (2·p2, 3^x·s + p2·x)`.  This is exactly the recursion defining
    `CC.decomposition_correction` (bit `x = X(T^k n)`, running weight `p2 = 2^k`). -/
def remStep (st : ℕ × ℕ) (x : ℕ) : ℕ × ℕ := (2 * st.1, 3 ^ x * st.2 + st.1 * x)

/-- The parity word of `n` of length `j`, as `[X(T^0 n), …, X(T^{j-1} n)]`. -/
def pbits (j n : ℕ) : List ℕ := (List.range j).map (fun k => X (T_iter k n))

/-- The burst/gap word `1^{a₁}0^{e₁} … 1^{a_R}0^{e_R}` of a shape `[(a₁,e₁),…]`. -/
def wordOfShape : List (ℕ × ℕ) → List ℕ
  | [] => []
  | (a, e) :: rest => List.replicate a 1 ++ List.replicate e 0 ++ wordOfShape rest

/-- Total number of odd steps `q = Σ aᵢ` of a shape. -/
def ones (S : List (ℕ × ℕ)) : ℕ := (S.map Prod.fst).sum

/-- Total length `j = Σ (aᵢ + eᵢ)` of a shape. -/
def wlen (S : List (ℕ × ℕ)) : ℕ := (S.map (fun p => p.1 + p.2)).sum

/-! ### `wordOfShape` / `wlen` structural lemmas -/

lemma wordOfShape_append (S₁ S₂ : List (ℕ × ℕ)) :
    wordOfShape (S₁ ++ S₂) = wordOfShape S₁ ++ wordOfShape S₂ := by
  induction S₁ with
  | nil => simp [wordOfShape]
  | cons ae rest ih => obtain ⟨a, e⟩ := ae; simp [wordOfShape, ih, List.append_assoc]

lemma wordOfShape_length (S : List (ℕ × ℕ)) : (wordOfShape S).length = wlen S := by
  induction S with
  | nil => simp [wordOfShape, wlen]
  | cons ae rest ih => obtain ⟨a, e⟩ := ae; simp [wordOfShape, wlen, ih]; ring

lemma wordOfShape_cons (p : ℕ × ℕ) (rest : List (ℕ × ℕ)) :
    wordOfShape (p :: rest) = List.replicate p.1 1 ++ List.replicate p.2 0 ++ wordOfShape rest := by
  obtain ⟨a, e⟩ := p; rfl

lemma wordOfShape_split (S : List (ℕ × ℕ)) (i : ℕ) (hi : i < S.length) :
    wordOfShape S = wordOfShape (S.take i) ++
      (List.replicate (S[i]'hi).1 1 ++ (List.replicate (S[i]'hi).2 0 ++ wordOfShape (S.drop (i + 1)))) := by
  conv_lhs => rw [← List.take_append_drop i S, List.drop_eq_getElem_cons hi]
  rw [wordOfShape_append]; simp only [wordOfShape_cons, List.append_assoc]

lemma wlen_append (A B : List (ℕ × ℕ)) : wlen (A ++ B) = wlen A + wlen B := by
  simp [wlen, List.map_append, List.sum_append]

lemma wlen_cons (p : ℕ × ℕ) (rest : List (ℕ × ℕ)) : wlen (p :: rest) = p.1 + p.2 + wlen rest := by
  simp [wlen]

/-! ### Bits of the parity word are orbit parities -/

lemma pbits_getElem? (j n m : ℕ) :
    (pbits j n)[m]? = if m < j then some (X (T_iter m n)) else none := by
  unfold pbits; rw [List.getElem?_map]
  by_cases h : m < j
  · rw [if_pos h, List.getElem?_eq_getElem (show m < (List.range j).length by simpa using h)]
    simp [List.getElem_range]
  · rw [if_neg h, List.getElem?_eq_none (show (List.range j).length ≤ m by simpa using Nat.le_of_not_lt h)]
    rfl

lemma odd_of_X_eq_one {n : ℕ} (h : X n = 1) : n % 2 = 1 := by
  rcases Nat.even_or_odd n with he | ho
  · rw [X_even (Nat.even_iff.mp he)] at h; omega
  · exact Nat.odd_iff.mp ho

lemma even_of_X_eq_zero {n : ℕ} (h : X n = 0) : n % 2 = 0 := by
  rcases Nat.even_or_odd n with he | ho
  · exact Nat.even_iff.mp he
  · rw [X_odd (Nat.odd_iff.mp ho)] at h; omega

lemma odd_of_word_bit_one (S : List (ℕ × ℕ)) (n m : ℕ) (hshape : pbits (wlen S) n = wordOfShape S)
    (hbit : (wordOfShape S)[m]? = some 1) : T_iter m n % 2 = 1 := by
  rw [← hshape, pbits_getElem?] at hbit; split at hbit
  · exact odd_of_X_eq_one (Option.some_injective _ hbit)
  · simp at hbit

lemma even_of_word_bit_zero (S : List (ℕ × ℕ)) (n m : ℕ) (hshape : pbits (wlen S) n = wordOfShape S)
    (hbit : (wordOfShape S)[m]? = some 0) : T_iter m n % 2 = 0 := by
  rw [← hshape, pbits_getElem?] at hbit; split at hbit
  · exact even_of_X_eq_zero (Option.some_injective _ hbit)
  · simp at hbit

