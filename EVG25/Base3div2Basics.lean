/-
Definitions and basic properties of the number system in rational base 3/2,
following Eliahou–Verger-Gaugry (arXiv:2504.13716v1) and Akiyama–Frougny–Sakarovitch.

Given n ∈ ℕ, its representation in base 3/2 is n = (1/2) Σ aᵢ (3/2)^i
with digits aᵢ ∈ {0,1,2}. The digit extraction follows Proposition 2.2:
  a₀ = (2n) mod 3,  parent = (2n) / 3,  and  ⟨n⟩ = ⟨parent⟩ a₀.
-/
import CollatzMapBasics.Terras

namespace CollatzMapBasics.Base3div2

open CollatzMapBasics

/-! ## Digit extraction -/

/-- The least-significant digit of `n` in rational base 3/2: `(2 * n) % 3`.
    This is `a₀` in the paper's Proposition 2.2. -/
def lsd (n : ℕ) : ℕ := (2 * n) % 3

/-- The parent of `n` in the base-3/2 digit tree: `(2 * n) / 3`.
    Removing the least-significant digit gives ⟨parent n⟩. -/
def parent (n : ℕ) : ℕ := (2 * n) / 3

/-- Fundamental identity: `2 * n = 3 * parent n + lsd n` (division algorithm for `2n` by 3). -/
theorem two_mul_eq (n : ℕ) : 2 * n = 3 * parent n + lsd n :=
  (Nat.div_add_mod (2 * n) 3).symm

/-- The least-significant digit is always in `{0, 1, 2}`. -/
theorem lsd_lt_three (n : ℕ) : lsd n < 3 := Nat.mod_lt _ (by omega)

/-- `parent n < n` for all `n ≥ 1`, ensuring termination of digit extraction. -/
theorem parent_lt (n : ℕ) (hn : n ≥ 1) : parent n < n := by
  simp only [parent]; omega

/-- The least-significant digit satisfies `lsd n ≡ parent n [MOD 2]` (Proposition 2.2). -/
theorem lsd_mod_two_eq_parent (n : ℕ) : lsd n % 2 = parent n % 2 := by
  simp only [lsd, parent]; omega

/-! ## Representation: digits in base 3/2 -/

/-- The representation of `n` in rational base 3/2, as a list of digits (least-significant first).
    `digits₃₂ 0 = []` and `digits₃₂ n = (lsd n) :: digits₃₂ (parent n)` for `n ≥ 1`. -/
def digits₃₂ (n : ℕ) : List ℕ :=
  if n = 0 then [] else lsd n :: digits₃₂ (parent n)
termination_by n
decreasing_by exact parent_lt n (by omega)

theorem digits₃₂_zero : digits₃₂ 0 = [] := by
  unfold digits₃₂; simp

theorem digits₃₂_pos (n : ℕ) (hn : n ≥ 1) :
    digits₃₂ n = lsd n :: digits₃₂ (parent n) := by
  conv_lhs => unfold digits₃₂
  simp [show n ≠ 0 by omega]

/-- Every digit in the representation is less than 3. -/
theorem mem_digits₃₂_lt_three (n : ℕ) : ∀ d ∈ digits₃₂ n, d < 3 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hn : n = 0
    · subst hn; simp [digits₃₂_zero]
    · rw [digits₃₂_pos n (by omega)]
      intro d hd
      simp only [List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact lsd_lt_three _
      · exact ih _ (parent_lt _ (by omega)) _ hd

/-- The length of `digits₃₂ n` is zero iff `n = 0`. -/
theorem digits₃₂_length_eq_zero_iff (n : ℕ) : (digits₃₂ n).length = 0 ↔ n = 0 := by
  constructor
  · intro h
    by_contra hn
    rw [digits₃₂_pos n (by omega)] at h
    simp at h
  · intro h; subst h; simp [digits₃₂_zero]

/-! ## Evaluation -/

/-- Evaluate a list of base-3/2 digits (least-significant first) to a natural number.
    Defined by: `eval₃₂ [] = 0` and `eval₃₂ (a :: rest) = (a + 3 * eval₃₂ rest) / 2`.
    For admissible digit lists (output of `digits₃₂`), the division is always exact. -/
def eval₃₂ : List ℕ → ℕ
  | [] => 0
  | a :: rest => (a + 3 * eval₃₂ rest) / 2

@[simp] theorem eval₃₂_nil : eval₃₂ [] = 0 := rfl

theorem eval₃₂_cons (a : ℕ) (rest : List ℕ) :
    eval₃₂ (a :: rest) = (a + 3 * eval₃₂ rest) / 2 := rfl

/-- Right inverse: `eval₃₂ (digits₃₂ n) = n` for all `n`. -/
theorem eval₃₂_digits₃₂ (n : ℕ) : eval₃₂ (digits₃₂ n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hn : n = 0
    · subst hn; simp [digits₃₂_zero]
    · rw [digits₃₂_pos n (by omega), eval₃₂_cons,
          ih _ (parent_lt _ (by omega))]
      have := two_mul_eq n
      omega

/-! ## The function U (Notation 3.7 of the paper) -/

/-- The function `U : ℕ → ℕ` from the paper (Notation 3.7):
    `U(n) = (3n + 2) / 2` if `n` is even, `U(n) = (3n + 1) / 2` if `n` is odd.
    Equivalently, `U(n) = (3n + 2 - n % 2) / 2`. -/
def U (n : ℕ) : ℕ :=
  if n % 2 = 0 then (3 * n + 2) / 2 else (3 * n + 1) / 2

theorem U_even {n : ℕ} (h : n % 2 = 0) : U n = (3 * n + 2) / 2 := by simp [U, h]
theorem U_odd {n : ℕ} (h : n % 2 = 1) : U n = (3 * n + 1) / 2 := by
  simp [U, show n % 2 ≠ 0 from by omega]

/-- When `n` is odd, `U n = T n`. -/
theorem U_odd_eq_T {n : ℕ} (h : n % 2 = 1) : U n = T n := by
  rw [U_odd h, T_odd h]

/-- `U n ≡ T n + n + 1 [MOD 2]` for all `n` (Remark 3.8). -/
theorem U_mod_two (n : ℕ) : U n % 2 = (T n + n + 1) % 2 := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [U_even (by omega), T_even (by omega)]
    omega
  · rw [U_odd (by omega), T_odd (by omega)]
    omega

/-- Proposition 3.9: `parent (U n) = n`. -/
theorem parent_U (n : ℕ) : parent (U n) = n := by
  simp only [parent, U]; split <;> omega

/-- When `n` is odd, the digit appended by `U` is `1`. -/
theorem lsd_U_odd {n : ℕ} (h : n % 2 = 1) : lsd (U n) = 1 := by
  simp only [lsd, U, show n % 2 ≠ 0 from by omega, ite_false]; omega

/-- When `n` is even, the digit appended by `U` is `2`. -/
theorem lsd_U_even {n : ℕ} (h : n % 2 = 0) : lsd (U n) = 2 := by
  simp only [lsd, U, h, ite_true]; omega

/-- `U n ≥ 1` for all `n`. -/
theorem U_pos (n : ℕ) : U n ≥ 1 := by
  simp only [U]; split <;> omega

/-- Proposition 3.9 combined: `digits₃₂ (U n)` equals `digits₃₂ n` with the
    appropriate digit (`1` if odd, `2` if even) prepended. -/
theorem digits₃₂_U (n : ℕ) :
    digits₃₂ (U n) = (if n % 2 = 1 then 1 else 2) :: digits₃₂ n := by
  rw [digits₃₂_pos _ (U_pos n), parent_U]
  congr 1
  split
  · exact lsd_U_odd ‹_›
  · exact lsd_U_even (by omega)

/-! ## Proposition 3.1: Extending admissible words -/

/-- For odd `n`, the Collatz value `T(n) = (3n+1)/2` has least-significant digit `1`
    in base 3/2. -/
theorem lsd_T_odd {n : ℕ} (h : n % 2 = 1) : lsd (T n) = 1 := by
  simp only [lsd, T_odd h]; omega

/-- For odd `n`, the parent of `T(n)` in the digit tree is `n` itself. -/
theorem parent_T_odd {n : ℕ} (h : n % 2 = 1) : parent (T n) = n := by
  simp only [parent, T_odd h]; omega

/-- Corollary 3.2: For odd `n`, `⟨T(n)⟩ = ⟨n⟩1`, i.e. the base-3/2 representation
    of `T(n)` is that of `n` with digit `1` prepended (least-significant first). -/
theorem digits₃₂_T_odd {n : ℕ} (hn : n % 2 = 1) :
    digits₃₂ (T n) = 1 :: digits₃₂ n := by
  rw [digits₃₂_pos _ (T_pos (show n ≥ 1 by omega)), lsd_T_odd hn, parent_T_odd hn]

/-- For even `n`, the number `3n/2` has least-significant digit `0` in base 3/2. -/
theorem lsd_extend_zero {n : ℕ} (h : n % 2 = 0) : lsd (3 * n / 2) = 0 := by
  simp only [lsd]; omega

/-- For even `n`, the parent of `3n/2` in the digit tree is `n`. -/
theorem parent_extend_zero {n : ℕ} (h : n % 2 = 0) : parent (3 * n / 2) = n := by
  simp only [parent]; omega

/-- Proposition 3.1 (even, digit 0): For even `n ≥ 1`, `⟨3n/2⟩ = ⟨n⟩0`. -/
theorem digits₃₂_extend_zero {n : ℕ} (hn : n % 2 = 0) (hn1 : n ≥ 1) :
    digits₃₂ (3 * n / 2) = 0 :: digits₃₂ n := by
  have : 3 * n / 2 ≥ 1 := by omega
  rw [digits₃₂_pos _ this, lsd_extend_zero hn, parent_extend_zero hn]

/-- For even `n`, the number `(3n+2)/2` has least-significant digit `2` in base 3/2. -/
theorem lsd_extend_two {n : ℕ} (h : n % 2 = 0) : lsd ((3 * n + 2) / 2) = 2 := by
  simp only [lsd]; omega

/-- For even `n`, the parent of `(3n+2)/2` in the digit tree is `n`. -/
theorem parent_extend_two {n : ℕ} (h : n % 2 = 0) : parent ((3 * n + 2) / 2) = n := by
  simp only [parent]; omega

/-- Proposition 3.1 (even, digit 2): For even `n`, `⟨(3n+2)/2⟩ = ⟨n⟩2`. -/
theorem digits₃₂_extend_two {n : ℕ} (hn : n % 2 = 0) :
    digits₃₂ ((3 * n + 2) / 2) = 2 :: digits₃₂ n := by
  have : (3 * n + 2) / 2 ≥ 1 := by omega
  rw [digits₃₂_pos _ this, lsd_extend_two hn, parent_extend_two hn]

/-- Proposition 3.1 (necessity): digit `1` requires an odd parent. -/
theorem odd_of_lsd_one {n : ℕ} (h : lsd n = 1) : parent n % 2 = 1 := by
  have := lsd_mod_two_eq_parent n; omega

/-- Proposition 3.1 (necessity): digit `0` requires an even parent. -/
theorem even_of_lsd_zero {n : ℕ} (h : lsd n = 0) : parent n % 2 = 0 := by
  have := lsd_mod_two_eq_parent n; omega

/-- Proposition 3.1 (necessity): digit `2` requires an even parent. -/
theorem even_of_lsd_two {n : ℕ} (h : lsd n = 2) : parent n % 2 = 0 := by
  have := lsd_mod_two_eq_parent n; omega

/-! ## Iterated U and saturated numbers -/

/-- `U_iter k n` applies `U` to `n` a total of `k` times. -/
def U_iter : ℕ → ℕ → ℕ
  | 0, n     => n
  | k + 1, n => U (U_iter k n)

@[simp] theorem U_iter_zero (n : ℕ) : U_iter 0 n = n := rfl
@[simp] theorem U_iter_succ (k n : ℕ) : U_iter (k + 1) n = U (U_iter k n) := rfl

/-- `sat k` is the largest natural number whose base-3/2 representation has length `k`.
    Equivalently, `sat k = U^k(0)` (Proposition 3.10). -/
def sat (k : ℕ) : ℕ := U_iter k 0

@[simp] theorem sat_zero : sat 0 = 0 := rfl
theorem sat_one : sat 1 = 1 := by native_decide
theorem sat_two : sat 2 = 2 := by native_decide
theorem sat_three : sat 3 = 4 := by native_decide
theorem sat_four : sat 4 = 7 := by native_decide
theorem sat_five : sat 5 = 11 := by native_decide
theorem sat_six : sat 6 = 17 := by native_decide
theorem sat_seven : sat 7 = 26 := by native_decide

/-- `sat (k + 1) = U (sat k)`. -/
theorem sat_succ (k : ℕ) : sat (k + 1) = U (sat k) := rfl

/-- The digits of `sat k` consist entirely of `1`s and `2`s (no `0`s) for `k ≥ 1`
    (Proposition 3.5 of the paper). -/
theorem digits₃₂_sat_no_zero {k : ℕ} (hk : k ≥ 1) {d : ℕ} (hd : d ∈ digits₃₂ (sat k)) :
    d = 1 ∨ d = 2 := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [sat_succ, digits₃₂_U] at hd
    simp only [List.mem_cons] at hd
    rcases hd with rfl | hd
    · split_ifs <;> simp_all
    · rcases k with _ | k
      · simp [sat, digits₃₂_zero] at hd
      · exact ih (by omega) hd

/-- Proposition 3.6: `⟨sat(k+1)⟩` is `⟨sat(k)⟩` extended by digit `1` or `2`
    according to the parity of `sat(k)`. -/
theorem sat_digits_prefix (k : ℕ) :
    digits₃₂ (sat (k + 1)) = (if sat k % 2 = 1 then 1 else 2) :: digits₃₂ (sat k) :=
  digits₃₂_U (sat k)

/-! ## The odometer (Proposition 2.3) -/

/-- The cyclic permutation σ = (2 1 0) on digits: 0 ↦ 2, 1 ↦ 0, 2 ↦ 1. -/
def σ (d : ℕ) : ℕ := (d + 2) % 3

@[simp] theorem σ_zero : σ 0 = 2 := by decide
@[simp] theorem σ_one : σ 1 = 0 := by decide
@[simp] theorem σ_two : σ 2 = 1 := by decide

/-- Successor always applies σ to the least-significant digit. -/
theorem lsd_succ (n : ℕ) (_hn : n ≥ 1) : lsd (n + 1) = σ (lsd n) := by
  simp only [lsd, σ]; omega

/-- When the least-significant digit is `0`, the parent is unchanged by successor. -/
theorem parent_succ_of_lsd_zero {n : ℕ} (_hn : n ≥ 1) (h : lsd n = 0) :
    parent (n + 1) = parent n := by
  simp only [parent, lsd] at *; omega

/-- When the least-significant digit is nonzero, the parent increments by 1 (carry). -/
theorem parent_succ_of_lsd_pos {n : ℕ} (_hn : n ≥ 1) (h : lsd n ≠ 0) :
    parent (n + 1) = parent n + 1 := by
  simp only [parent, lsd] at *; omega

/-- Split a digit list at its first `0` (LSB-first). Returns
    `(nonzero_prefix, suffix_after_zero)`. If no `0` is present, the suffix is `[]`. -/
def splitAtFirstZero : List ℕ → List ℕ × List ℕ
  | [] => ([], [])
  | d :: rest =>
    if d = 0 then ([], rest)
    else let p := splitAtFirstZero rest; (d :: p.1, p.2)

@[simp] theorem splitAtFirstZero_nil : splitAtFirstZero [] = ([], []) := rfl

@[simp] theorem splitAtFirstZero_zero (rest : List ℕ) :
    splitAtFirstZero (0 :: rest) = ([], rest) := by
  simp [splitAtFirstZero]

@[simp] theorem splitAtFirstZero_fst_cons_pos {d : ℕ} (hd : d ≠ 0) (rest : List ℕ) :
    (splitAtFirstZero (d :: rest)).1 = d :: (splitAtFirstZero rest).1 := by
  conv_lhs => unfold splitAtFirstZero; simp [hd]

@[simp] theorem splitAtFirstZero_snd_cons_pos {d : ℕ} (hd : d ≠ 0) (rest : List ℕ) :
    (splitAtFirstZero (d :: rest)).2 = (splitAtFirstZero rest).2 := by
  conv_lhs => unfold splitAtFirstZero; simp [hd]

/-- Proposition 2.3 (Odometer): If ⟨n⟩ = u0v with v ∈ {1,2}*, then ⟨n+1⟩ = u 2 vσ.
    In LSB-first digit lists, splitting at the first `0` and applying σ to the
    nonzero prefix gives the digits of `n + 1`. -/
theorem odometer (n : ℕ) :
    digits₃₂ (n + 1) =
      (splitAtFirstZero (digits₃₂ n)).1.map σ ++
        2 :: (splitAtFirstZero (digits₃₂ n)).2 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hn : n = 0
    · subst hn
      simp only [digits₃₂_zero, splitAtFirstZero_nil, List.map_nil, List.nil_append]
      rw [digits₃₂_pos 1 (by omega)]
      simp [lsd, parent, digits₃₂_zero]
    · rw [digits₃₂_pos n (by omega)]
      by_cases h0 : lsd n = 0
      · -- No carry: lsd = 0 becomes 2, parent unchanged
        simp only [h0, splitAtFirstZero_zero, List.map_nil, List.nil_append]
        rw [digits₃₂_pos (n + 1) (by omega), lsd_succ n (by omega), h0, σ_zero,
            parent_succ_of_lsd_zero (by omega) h0]
      · -- Carry: apply σ to lsd, increment parent
        simp only [splitAtFirstZero_fst_cons_pos h0, splitAtFirstZero_snd_cons_pos h0,
                    List.map_cons, List.cons_append]
        rw [digits₃₂_pos (n + 1) (by omega), lsd_succ n (by omega),
            parent_succ_of_lsd_pos (by omega) h0]
        congr 1
        exact ih (parent n) (parent_lt n (by omega))

/-! ## Scaled evaluation and parity criterion (Proposition 4.5) -/

/-- Scaled evaluation: `scaledEval [a₀, …, aₖ] = Σᵢ 2^(k−i) · 3^i · aᵢ`.
    This equals `2^(k+1) · n` when the digit list represents `n`. -/
def scaledEval : List ℕ → ℕ
  | [] => 0
  | a :: rest => 2 ^ rest.length * a + 3 * scaledEval rest

@[simp] theorem scaledEval_nil : scaledEval [] = 0 := rfl

theorem scaledEval_cons (a : ℕ) (rest : List ℕ) :
    scaledEval (a :: rest) = 2 ^ rest.length * a + 3 * scaledEval rest := rfl

/-- Key identity: `scaledEval (digits₃₂ n) = 2 ^ |digits₃₂ n| * n`. -/
theorem scaledEval_digits₃₂ (n : ℕ) :
    scaledEval (digits₃₂ n) = 2 ^ (digits₃₂ n).length * n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hn : n = 0
    · subst hn; simp [digits₃₂_zero]
    · rw [digits₃₂_pos n (by omega)]
      simp only [scaledEval_cons, List.length_cons]
      rw [ih (parent n) (parent_lt n (by omega))]
      have h := two_mul_eq n
      have hsum : lsd n + 3 * parent n = 2 * n := by omega
      calc 2 ^ (digits₃₂ (parent n)).length * lsd n +
              3 * (2 ^ (digits₃₂ (parent n)).length * parent n)
          = 2 ^ (digits₃₂ (parent n)).length * (lsd n + 3 * parent n) := by ring
        _ = 2 ^ (digits₃₂ (parent n)).length * (2 * n) := by rw [hsum]
        _ = 2 ^ ((digits₃₂ (parent n)).length + 1) * n := by ring

/-- Proposition 4.5: `n` is even iff `Σ 2^(k−i) 3^i aᵢ ≡ 0 (mod 2^(k+2))`,
    where `⟨n⟩ = aₖ…a₀` has `k + 1` digits. -/
theorem parity_criterion {n : ℕ} (_hn : n ≥ 1) :
    n % 2 = 0 ↔
      scaledEval (digits₃₂ n) % 2 ^ ((digits₃₂ n).length + 1) = 0 := by
  rw [scaledEval_digits₃₂, pow_succ]
  -- goal: n % 2 = 0 ↔ 2^L * n % (2^L * 2) = 0  where L = (digits₃₂ n).length
  rw [Nat.mul_mod_mul_left]
  -- goal: n % 2 = 0 ↔ 2^L * (n % 2) = 0
  constructor
  · intro h; simp [h]
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · exact absurd h1 (by positivity)
    · exact h2

end CollatzMapBasics.Base3div2
