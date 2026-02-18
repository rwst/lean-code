import Mathlib.Data.List.Basic
import Mathlib.Data.List.Infix
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

-- 1. Representation of Parity Vectors
-- Definition 2.1: Parity vectors are essentially binary words.
-- We represent 0 as `false` and 1 as `true`.
def ParityVector := List Bool

deriving instance DecidableEq for ParityVector

instance : GetElem ParityVector ℕ Bool fun v i => i < v.length :=
  inferInstanceAs (GetElem (List Bool) ℕ Bool _)

namespace ParityVector

-- Helper to interpret Bool as Nat (0 or 1) for summation contexts later
def toNat (b : Bool) : ℕ := if b then 1 else 0

/-- `q v` is the number of ones (true entries) in the parity vector `v`. -/
def q (v : ParityVector) : ℕ := v.count true

/-- The size (length) of a parity vector. -/
def size (v : ParityVector) : ℕ := v.length

/-- The ones-ratio `q / size` as a rational number. Returns 0 for the empty vector. -/
def onesRatio (v : ParityVector) : ℚ := (q v : ℚ) / (size v : ℚ)


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

/-
The elementary precedence relation (swapping 01 to 10) preserves the length of the vector.
-/
theorem ElementaryPrecedes_length_eq {v1 v2 : ParityVector} (h : ParityVector.ElementaryPrecedes v1 v2) :
    v1.length = v2.length := by
      cases h ; aesop

/-
The elementary precedence relation (swapping 01 to 10) preserves the number of ones (q).
-/
theorem ElementaryPrecedes_q_eq {v1 v2 : ParityVector} (h : ParityVector.ElementaryPrecedes v1 v2) :
    ParityVector.q v1 = ParityVector.q v2 := by
      obtain ⟨ w1, w2 ⟩ := h;
      unfold ParityVector.q; simp +arith +decide;

/-- The partial sum `∑_{i=0}^{k} toNat(v[i])`, i.e., the number of ones
    among the first `k + 1` entries of `v`. -/
def partialSum (v : ParityVector) (k : ℕ) : ℕ :=
  ((v.take (k + 1)).map toNat).sum

-- Helper: partialSum at k+1 decomposes as partialSum at k plus toNat(v[k+1])
private lemma partialSum_succ (v : ParityVector) (k : ℕ) (h : k + 1 < v.length) :
    partialSum v (k + 1) = partialSum v k + toNat (v[k + 1]'h) := by
  simp only [partialSum]
  rw [show k + 1 + 1 = (k + 1) + 1 from rfl, List.take_add_one (l := (v : List Bool))]
  simp only [List.map_append, List.sum_append, Option.toList, List.getElem?_eq_getElem h,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]; rfl

-- Helper: partialSum at 0 equals toNat(v[0])
private lemma partialSum_zero (v : ParityVector) (h : 0 < v.length) :
    partialSum v 0 = toNat (v[0]'h) := by
  simp [partialSum, List.take_add_one, List.getElem?_eq_getElem h, Option.toList, toNat]; rfl

private lemma toNat_false : toNat false = 0 := rfl
private lemma toNat_true : toNat true = 1 := rfl

-- Helper: partialSum is monotone non-decreasing
private lemma partialSum_mono (v : ParityVector) (a : ℕ) : ∀ b, a ≤ b → b < v.length →
    partialSum v a ≤ partialSum v b
  | 0, hab, _ => by
    obtain rfl : a = 0 := by omega
    exact le_refl _
  | n + 1, hab, hb => by
    rcases Nat.eq_or_lt_of_le hab with rfl | h
    · exact le_refl _
    · calc partialSum v a ≤ partialSum v n := partialSum_mono v a n (by omega) (by omega)
        _ ≤ partialSum v n + toNat (v[n + 1]'hb) := Nat.le_add_right _ _
        _ = partialSum v (n + 1) := (partialSum_succ v n hb).symm


/-
The elementary precedence relation (swapping 01 to 10) increases or maintains the partial sums.
Proof idea:
Let the swap happen at indices `i` and `i+1`.
The sequence changes from `... 0, 1 ...` to `... 1, 0 ...`.
For `k < i`, the prefix is unchanged, so partial sums are equal.
For `k = i`, the prefix of `v2` has a 1 where `v1` has a 0, so `partialSum v2 i = partialSum v1 i + 1`.
For `k >= i + 1`, the prefix includes both the swapped elements. Since 0+1 = 1+0, the total sum is unchanged.
Thus, for all `k`, `partialSum v1 k ≤ partialSum v2 k`.
-/
theorem ElementaryPrecedes_partialSum_le {v1 v2 : ParityVector} (h : ParityVector.ElementaryPrecedes v1 v2) :
    ∀ k, ParityVector.partialSum v1 k ≤ ParityVector.partialSum v2 k := by
      rcases h with ⟨ w1, w2 ⟩;
      unfold ParityVector.partialSum;
      intro k; rcases le_or_gt ( k + 1 ) w1.length with hk | hk <;> simp_all +decide [ List.take_append ] ;
      rcases n : k + 1 - w1.length with ( _ | _ | n ) <;> simp_all +arith +decide [ List.take ];

/-
If `v` is majorized by `v'` (and `v ≠ v'`), then the first index `i` where they differ must have `v[i] = 0` and `v'[i] = 1`.
Proof sketch:
1. Since `v ≠ v'`, there is a first index `i` where they differ.
2. Since `q v = q v'`, they cannot differ at only one position (the last one), so `i < v.length - 1`, i.e., `i + 2 ≤ v.length`.
3. For `k < i`, `v[k] = v'[k]`, so `partialSum v (i-1) = partialSum v' (i-1)`.
4. By `hsum` at `k=i`, `partialSum v i ≤ partialSum v' i`.
5. `partialSum v i = partialSum v (i-1) + v[i]`.
6. Thus `v[i] ≤ v'[i]`. Since they differ, `v[i]=0` and `v'[i]=1`.
-/
theorem exists_first_diff_zero_one {v v' : ParityVector}
    (hlen : v.length = v'.length)
    (hsum : ∀ k, k + 2 ≤ v.length → ParityVector.partialSum v k ≤ ParityVector.partialSum v' k)
    (hq : ParityVector.q v = ParityVector.q v')
    (hne : v ≠ v') :
    ∃ (i : ℕ) (hi : i + 2 ≤ v.length), v[i]'(by omega) = false ∧ v'[i]'(by omega) = true ∧
      ∀ (k : ℕ) (hk : k < i), v[k]'(by omega) = v'[k]'(by omega) := by
  -- Helper: v.take i = v'.take i when they agree on all indices < i
  have take_eq_of_agree : ∀ m, (∀ (k : ℕ) (_ : k < m) (_ : k < v.length), v[k]'(by omega) = v'[k]'(by omega)) →
      v.take m = v'.take m := by
    intro m hagree
    apply List.ext_getElem
    · simp [List.length_take, hlen]
    · intro k hk hk'
      simp only [List.getElem_take]
      have : k < m := by simp [List.length_take] at hk; omega
      have : k < v.length := by simp [List.length_take] at hk; omega
      exact hagree k ‹k < m› ‹k < v.length›
  -- Step 1: There exists some index where v and v' differ
  have hne_idx : ∃ i, ∃ _ : i < v.length, v[i] ≠ v'[i]'(hlen ▸ ‹i < v.length›) := by
    by_contra hall
    push_neg at hall
    apply hne
    apply List.ext_getElem (by exact hlen)
    intro i hi hi'
    have := hall i hi
    exact this
  -- Step 2: Find the minimum differing index
  obtain ⟨i₀, hi₀_lt, hi₀_diff⟩ := hne_idx
  -- Use well-ordering: take the minimum
  have hdiff_dec : ∀ n, Decidable (n < v.length ∧ v[n]? ≠ v'[n]?) := by
    intro n; exact inferInstance
  let S := {n : ℕ | n < v.length ∧ v[n]? ≠ v'[n]?}
  have hS : i₀ ∈ S := by
    refine ⟨hi₀_lt, ?_⟩
    simp [hi₀_lt, show i₀ < v'.length from hlen ▸ hi₀_lt]
    exact hi₀_diff
  obtain ⟨i, ⟨hi_lt, hi_diff_opt⟩, hi_min⟩ := Nat.lt_wfRel.2.has_min S ⟨i₀, hS⟩
  have hi_lt' : i < v'.length := hlen ▸ hi_lt
  have hi_diff : v[i]'hi_lt ≠ v'[i]'hi_lt' := by
    simp [hi_lt, hi_lt'] at hi_diff_opt
    exact hi_diff_opt
  -- hi_min : ∀ j ∈ S, ¬(j < i)
  have hi_agree : ∀ (k : ℕ) (_ : k < i), v[k]'(by omega) = v'[k]'(by omega) := by
    intro k hk
    by_contra h
    have hklt : k < v.length := by omega
    have hklt' : k < v'.length := by omega
    have : k ∈ S := by
      refine ⟨hklt, ?_⟩
      simp [hklt, hklt']
      exact h
    exact hi_min k this hk
  -- Step 3: Show i + 2 ≤ v.length (i is not the last index)
  have hi_not_last : i + 2 ≤ v.length := by
    by_contra h_last
    push_neg at h_last
    have hi_eq : i + 1 = v.length := by omega
    -- v and v' agree on all indices except i (the last one)
    -- So they differ only at i, which means q v ≠ q v'
    -- We show v.count true ≠ v'.count true
    -- Express v = v.take i ++ [v[i]] (since i is the last index)
    have hv_split : v = v.take i ++ v.drop i := (List.take_append_drop i v).symm
    have hv'_split : v' = v'.take i ++ v'.drop i := (List.take_append_drop i v').symm
    have hv_drop : v.drop i = [v[i]'(by omega)] := by
      apply List.ext_getElem
      · simp [List.length_drop]; omega
      · intro k hk hk'
        simp at hk'
        subst hk'
        simp only [List.getElem_drop, List.getElem_cons_zero]
        congr 1
    have hv'_drop : v'.drop i = [v'[i]'(by omega)] := by
      apply List.ext_getElem
      · simp [List.length_drop]; omega
      · intro k hk hk'
        simp at hk'
        subst hk'
        simp only [List.getElem_drop, List.getElem_cons_zero]
        congr 1
    have htake_eq : v.take i = v'.take i := by
      apply List.ext_getElem
      · simp [List.length_take, hlen]
      · intro k hk hk'
        simp only [List.getElem_take]
        exact hi_agree k (by simp [List.length_take] at hk; exact hk.1)
    unfold ParityVector.q at hq
    rw [hv_split, hv'_split, hv_drop, hv'_drop] at hq
    simp [List.count_append, List.count_singleton] at hq
    rw [htake_eq] at hq
    -- Now hq says: count in shared prefix + (if v[i]=true then 1 else 0) = same prefix + (if v'[i]=true then 1 else 0)
    -- So v[i] = true ↔ v'[i] = true, contradicting hi_diff
    have hilt : i < v.length := by omega
    have hilt' : i < v'.length := by omega
    cases hvi : v[i]'hilt <;> cases hvi' : v'[i]'hilt'
    · exact hi_diff (by simp [hvi, hvi'])
    · simp [hvi, hvi'] at hq
    · simp [hvi, hvi'] at hq
    · exact hi_diff (by simp [hvi, hvi'])
  -- Step 4: Show v[i] = false and v'[i] = true using hsum
  -- partialSum v i = sum of toNat over v.take (i+1) = sum over v.take i ++ [v[i]]
  have htake_eq : v.take i = v'.take i := by
    apply List.ext_getElem
    · simp [List.length_take, hlen]
    · intro k hk hk'
      simp only [List.getElem_take]
      exact hi_agree k (by simp [List.length_take] at hk; exact hk.1)
  have hv_take_succ : v.take (i + 1) = v.take i ++ [v[i]'(by omega)] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hi_lt]
    rfl
  have hv'_take_succ : v'.take (i + 1) = v'.take i ++ [v'[i]'(by omega)] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hi_lt']
    rfl
  have hsumi := hsum i hi_not_last
  unfold ParityVector.partialSum at hsumi
  rw [hv_take_succ, hv'_take_succ] at hsumi
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
             List.sum_nil, Nat.add_zero] at hsumi
  rw [htake_eq] at hsumi
  -- Now hsumi : ... + toNat v[i] ≤ ... + toNat v'[i]
  -- So toNat v[i] ≤ toNat v'[i]
  have htonat : toNat (v[i]'(by omega)) ≤ toNat (v'[i]'(by omega)) := by omega
  have hvi_false : v[i]'(by omega) = false := by
    cases hvi : v[i]'(by omega) with
    | false => rfl
    | true =>
      cases hvi' : v'[i]'(by omega) with
      | true => exact absurd (hvi.trans hvi'.symm) hi_diff
      | false => unfold toNat at htonat; simp [hvi, hvi'] at htonat
  have hvi'_true : v'[i]'(by omega) = true := by
    cases h : v'[i]'(by omega)
    · exact absurd (hvi_false.trans h.symm) hi_diff
    · rfl
  exact ⟨i, hi_not_last, hvi_false, hvi'_true, hi_agree⟩

-- Helper: partialSum stays constant when all entries in (a, b] are false
private lemma partialSum_eq_of_false_range (v : ParityVector) (a : ℕ) :
    ∀ b, a ≤ b → b < v.length →
    (∀ (x : ℕ), a < x → x ≤ b → (hx : x < v.length) → v[x]'hx = false) →
    partialSum v a = partialSum v b
  | 0, hab, _, _ => by
    obtain rfl : a = 0 := by omega
    rfl
  | n + 1, hab, hb, hf => by
    rcases Nat.eq_or_lt_of_le hab with rfl | h
    · rfl
    · have hvn1 : v[n + 1]'hb = false := hf (n + 1) (by omega) le_rfl hb
      have step := partialSum_succ v n hb
      have htn : toNat (v[n + 1]'hb) = 0 := by rw [hvn1]; rfl
      have ih := partialSum_eq_of_false_range v a n (by omega) (by omega)
        (fun x hx1 hx2 hx3 => hf x hx1 (by omega) hx3)
      linarith

-- Helper: count true = sum of toNat over the list
private lemma count_true_eq_map_toNat_sum : ∀ (l : List Bool), l.count true = (l.map toNat).sum
  | [] => by simp
  | b :: bs => by
    simp [List.count_cons, List.map, List.sum_cons, toNat]
    cases b <;> simp [count_true_eq_map_toNat_sum bs]; omega

-- Helper: q equals partialSum at the last index
private lemma q_eq_partialSum_last (v : ParityVector) (hne : v.length > 0) :
    q v = partialSum v (v.length - 1) := by
  unfold q partialSum
  rw [show v.length - 1 + 1 = v.length from by omega, List.take_length]
  exact count_true_eq_map_toNat_sum v

-- Helper: if v and v' agree on [0, k], their partial sums agree at k
private lemma partialSum_eq_of_prefix_agree (v v' : ParityVector) (k : ℕ)
    (hk : k < v.length) (hk' : k < v'.length)
    (hagree : ∀ (x : ℕ) (hxk : x ≤ k), v[x]'(by omega) = v'[x]'(by omega)) :
    partialSum v k = partialSum v' k := by
  unfold partialSum; congr 1; congr 1
  apply List.ext_getElem
  · simp [List.length_take]; omega
  · intro n hn hn'
    simp only [List.getElem_take]
    exact hagree n (by simp [List.length_take] at hn; omega)

/-
If `v` is majorized by `v'` and they first differ at `i` (where `v[i]=0, v'[i]=1`), then there exists an index `j > i` such that `v[j]=1` and `v[j-1]=0` (so we can swap at `j-1, j`).
Furthermore, for all `k` in `[i, j-1]`, the partial sum of `v` is strictly less than that of `v'`.
This strict inequality ensures that increasing `partialSum v (j-1)` by 1 (due to the swap) will not violate the majorization condition.
-/
theorem exists_swap_index_of_first_diff {v v' : ParityVector}
    (hlen : v.length = v'.length)
    (hq : ParityVector.q v = ParityVector.q v')
    (i : ℕ)
    (hi_le : i + 2 ≤ v.length)
    (hi_val : v[i]'(by omega) = false)
    (hi_val' : v'[i]'(by omega) = true)
    (hi_prev : ∀ (k : ℕ) (hk : k < i), v[k]'(by omega) = v'[k]'(by omega)) :
    ∃ (j : ℕ) (hj : j < v.length), i < j ∧ v[j] = true ∧ v[j - 1]'(by omega) = false ∧
         (∀ k, i ≤ k ∧ k < j → ParityVector.partialSum v k < ParityVector.partialSum v' k) := by
  -- Step 1: Strict inequality partialSum v i < partialSum v' i.
  -- When i = 0, this follows directly from v[0] = false, v'[0] = true.
  -- When i = n+1, the partial sums at n agree (prefix agreement), and then the
  -- differing values at i give the strict inequality.
  have hstrict_i : partialSum v i < partialSum v' i := by
    rcases i with _ | n
    · rw [partialSum_zero v (by omega), partialSum_zero v' (by omega : 0 < v'.length),
          hi_val, hi_val', toNat_false, toNat_true]; omega
    · rw [partialSum_succ v n (by omega), partialSum_succ v' n (by omega : n + 1 < v'.length),
          partialSum_eq_of_prefix_agree v v' n (by omega) (by omega : n < v'.length)
            (fun x hxn => hi_prev x (by omega)),
          hi_val, hi_val', toNat_false, toNat_true]; omega
  -- Step 2: There exists j > i with v[j] = true.
  -- If all entries after i were false, then q v = partialSum v i < partialSum v' i <= q v',
  -- contradicting hq.
  have hexists_true : ∃ (j : ℕ) (_ : j < v.length), i < j ∧ v[j] = true := by
    by_contra hall
    push_neg at hall
    have hall_false : ∀ (x : ℕ), i < x → (hx : x < v.length) → v[x]'hx = false := by
      intro x hx hxlt
      have := hall x hxlt
      cases hv : v[x]'hxlt <;> simp_all
    have hqv : q v = partialSum v (v.length - 1) := q_eq_partialSum_last v (by omega)
    have hqv' : q v' = partialSum v' (v'.length - 1) := q_eq_partialSum_last v' (by omega)
    have hps_const : partialSum v i = partialSum v (v.length - 1) :=
      partialSum_eq_of_false_range v i (v.length - 1) (by omega) (by omega)
        (fun x hx1 _ hx3 => hall_false x hx1 hx3)
    have hps_le : partialSum v' i ≤ partialSum v' (v'.length - 1) :=
      partialSum_mono v' i (v'.length - 1) (by omega) (by omega)
    linarith
  -- Step 3: Find the minimal j > i with v[j] = true, using well-founded minimum.
  obtain ⟨j₀, hj₀_lt, hj₀_gt, hj₀_true⟩ := hexists_true
  let S := fun n => i < n ∧ ∃ (h : n < v.length), v[n]'h = true
  obtain ⟨j, ⟨hj_gt, hj_lt, hj_true⟩, hj_min⟩ :=
    Nat.lt_wfRel.2.has_min (setOf S) ⟨j₀, (⟨hj₀_gt, hj₀_lt, hj₀_true⟩ : S j₀)⟩
  -- From minimality: all entries in (i, j) are false.
  have hj_min_false : ∀ (m : ℕ) (hm : m < v.length), i < m → m < j → v[m]'hm = false := by
    intro m hm hm1 hm2
    by_contra hmt
    have hvt : v[m]'hm = true := by cases hv : v[m]'hm <;> simp_all
    exact hj_min m (⟨hm1, hm, hvt⟩ : S m) hm2
  -- Step 4: v[j-1] = false.
  -- If j = i+1 then j-1 = i and v[i] = false.
  -- If j > i+1 then j-1 is in (i, j), so v[j-1] = false by minimality.
  have hj_pred_false : v[j - 1]'(by omega) = false := by
    rcases Nat.eq_or_lt_of_le (show i + 1 ≤ j by omega) with hji | hji
    · have : v[j - 1]'(by omega) = v[i]'(by omega) := by congr 1; omega
      rw [this]; exact hi_val
    · exact hj_min_false (j - 1) (by omega) (by omega) (by omega)
  -- Step 5: For all k in [i, j), partialSum v k < partialSum v' k.
  -- Since all entries in [i, k] of v are false (i ≤ k < j), partialSum v k = partialSum v i.
  -- Since partialSum v' is monotone, partialSum v' i ≤ partialSum v' k.
  -- Combining: partialSum v k = partialSum v i < partialSum v' i ≤ partialSum v' k.
  have hstrict_range : ∀ k, i ≤ k ∧ k < j → partialSum v k < partialSum v' k := by
    intro k ⟨hki, hkj⟩
    have hps_vk : partialSum v i = partialSum v k := by
      rcases Nat.eq_or_lt_of_le hki with rfl | hik
      · rfl
      · exact partialSum_eq_of_false_range v i k hki (by omega)
          (fun x hx1 hx2 hx3 => hj_min_false x hx3 (by omega) (by omega))
    have hps_v'k : partialSum v' i ≤ partialSum v' k :=
      partialSum_mono v' i k hki (by omega)
    linarith
  exact ⟨j, hj_lt, hj_gt, hj_true, hj_pred_false, hstrict_range⟩

/-
If `v` has a `0` at `j-1` and a `1` at `j`, we can perform an elementary swap to get `u`.
The partial sums of `u` are the same as `v` everywhere except at `j-1`, where it increases by 1.
Proof idea:
Construct `u` by decomposing `v` into `prefix ++ [0, 1] ++ suffix` and swapping to `prefix ++ [1, 0] ++ suffix`.
Then analyze the partial sums.
For `k < j-1`, the prefix is identical.
For `k = j-1`, `u` has a 1 where `v` has a 0, so sum increases by 1.
For `k = j`, `u` has `1, 0` and `v` has `0, 1`, so the sum up to `j` is the same.
For `k > j`, the prefix includes both swapped elements, so the sum is the same.
-/
theorem elementary_step_partialSum_change {v : ParityVector} {j : ℕ}
    (hj : j < v.length) (hj1 : 0 < j)
    (h0 : v[j - 1]'(by omega) = false) (h1 : v[j] = true) :
    ∃ u, ParityVector.ElementaryPrecedes v u ∧
         (∀ k, ParityVector.partialSum u k = if k = j - 1 then ParityVector.partialSum v k + 1 else ParityVector.partialSum v k) := by
  -- Decompose v into w1 ++ [false, true] ++ w2
  have hdrop1 : v.drop (j - 1) = v[j - 1]'(by omega) :: v.drop j := by
    have h_idx : j - 1 < v.length := by omega
    have : v.drop (j - 1) = v[j - 1] :: v.drop ((j - 1) + 1) := List.drop_eq_getElem_cons h_idx
    simpa [show (j - 1) + 1 = j by omega] using this
  have hdrop2 : v.drop j = v[j] :: v.drop (j + 1) := by
    exact List.drop_eq_getElem_cons hj
  have hv_eq : (v : List Bool) = v.take (j - 1) ++ [false, true] ++ v.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop (j - 1) v]
    rw [hdrop1, h0, hdrop2, h1]
    simp [List.append_assoc]
  -- Use w1, w2 as abbreviations (not set, to avoid simp recursion issues)
  -- We work directly with the existing proof idiom from ElementaryPrecedes_partialSum_le
  refine ⟨v.take (j - 1) ++ [true, false] ++ v.drop (j + 1), ?_, ?_⟩
  · conv_lhs => rw [hv_eq]
    exact ElementaryPrecedes.swap _ _
  · -- Partial sum analysis
    -- Abstract v.take/v.drop into w1/w2 to avoid simp recursion
    have hw1len : (v.take (j - 1)).length = j - 1 := by simp; omega
    -- Suffices to show a statement about abstract w1, w2
    suffices hsuff : ∀ (w1 w2 : List Bool), w1.length = j - 1 →
        ∀ k, partialSum (w1 ++ [true, false] ++ w2) k =
          if k = j - 1 then partialSum (w1 ++ [false, true] ++ w2) k + 1
          else partialSum (w1 ++ [false, true] ++ w2) k by
      intro k
      rw [hsuff (v.take (j - 1)) (v.drop (j + 1)) hw1len k, ← hv_eq]
    intro w1 w2 hw1 k
    unfold partialSum
    rcases le_or_gt (k + 1) w1.length with hk | hk
    · have hkne : k ≠ j - 1 := by omega
      simp only [hkne, if_false]
      congr 2
      rw [List.append_assoc, List.append_assoc,
          List.take_append_of_le_length hk, List.take_append_of_le_length hk]
    · rcases n : k + 1 - w1.length with _ | _ | n
      · omega
      · have hkeq : k = j - 1 := by omega
        subst hkeq
        simp only [if_true]
        rw [show j - 1 + 1 = w1.length + 1 from by omega]
        rw [List.append_assoc, List.append_assoc,
            List.take_append (l₁ := w1), List.take_append (l₁ := w1)]
        simp only [List.take_of_length_le (Nat.le_succ _),
                   List.map_append, List.sum_append]
        norm_num [toNat_true, toNat_false]
      · have hkne : k ≠ j - 1 := by omega
        simp only [hkne, if_false]
        have h2 : 2 ≤ k + 1 - w1.length := by omega
        have hw1le : w1.length ≤ k + 1 := by omega
        have h1_eq : List.take (k + 1) (w1 ++ [true, false] ++ w2) = w1 ++ [true, false] ++ List.take (k + 1 - w1.length - 2) w2 := by
          rw [List.append_assoc, List.append_assoc, List.take_append (l₁ := w1),
              List.take_of_length_le hw1le, List.take_append (l₁ := [true, false]),
              List.take_of_length_le h2]
          simp
        have h2_eq : List.take (k + 1) (w1 ++ [false, true] ++ w2) = w1 ++ [false, true] ++ List.take (k + 1 - w1.length - 2) w2 := by
          rw [List.append_assoc, List.append_assoc, List.take_append (l₁ := w1),
              List.take_of_length_le hw1le, List.take_append (l₁ := [false, true]),
              List.take_of_length_le h2]
          simp
        rw [h1_eq, h2_eq]
        simp [List.map_append, List.sum_append, toNat_true, toNat_false]

/-
If `v` is majorized by `v'` (and `v ≠ v'`), there exists a vector `u` such that `v ≺ u` (elementary step) and `u` is still majorized by `v'`.

Helper lemmas used (all proved above):
- `exists_first_diff_zero_one`: finds index i where v[i]=0, v'[i]=1 and agree before i
- `exists_swap_index_of_first_diff`: finds swap index j>i with v[j]=1, v[j-1]=0, strict ineq on [i,j)
- `elementary_step_partialSum_change`: constructs u via elementary swap at j-1,j; partialSum u k = partialSum v k + 1 at k=j-1, unchanged elsewhere
- `ElementaryPrecedes_length_eq`: swap preserves length (so u.length = v.length)
-/
theorem exists_elementary_step_of_majorized_ne {v v' : ParityVector}
    (hlen : v.length = v'.length)
    (hsum : ∀ k, k + 2 ≤ v.length → ParityVector.partialSum v k ≤ ParityVector.partialSum v' k)
    (hq : ParityVector.q v = ParityVector.q v')
    (hne : v ≠ v') :
    ∃ u, ParityVector.ElementaryPrecedes v u ∧ (∀ k, k + 2 ≤ u.length → ParityVector.partialSum u k ≤ ParityVector.partialSum v' k) := by
  -- Step 1: Find first differing index i where v[i]=0, v'[i]=1
  obtain ⟨i, hi_le, hi_val, hi_val', hi_prev⟩ := exists_first_diff_zero_one hlen hsum hq hne
  -- Step 2: Find swap index j>i with v[j]=1, v[j-1]=0, strict partial sum ineq on [i,j)
  obtain ⟨j, hj, hij, hjval, hj1val, hstrict⟩ :=
    exists_swap_index_of_first_diff hlen hq i hi_le hi_val hi_val' hi_prev
  -- Step 3: Construct u via elementary swap at positions j-1, j
  obtain ⟨u, hep, hpsum⟩ := elementary_step_partialSum_change hj (by omega) hj1val hjval
  -- Step 4: Verify majorization for u
  refine ⟨u, hep, ?_⟩
  have hlen_u : u.length = v.length := (ElementaryPrecedes_length_eq hep).symm
  intro k hk
  rw [hlen_u] at hk
  rw [hpsum k]
  split_ifs with heq
  · -- k = j-1: partialSum u (j-1) = partialSum v (j-1) + 1
    --   hstrict gives partialSum v (j-1) < partialSum v' (j-1), so +1 still fits
    subst heq
    have hstrict_at : partialSum v (j - 1) < partialSum v' (j - 1) :=
      hstrict (j - 1) ⟨by omega, by omega⟩
    omega
  · -- k ≠ j-1: partialSum u k = partialSum v k, apply hsum directly
    exact hsum k hk


-- The moment of a parity vector: sum of indices where the entry is true.
-- An elementary swap moves a 1 leftward by one position, so moment decreases by exactly 1.
private def moment (v : ParityVector) : ℕ :=
  (v.mapIdx fun i b => if b then i else 0).sum

-- An elementary swap moves a true entry one position left, strictly decreasing the moment
private lemma ElementaryPrecedes_moment_lt {v u : ParityVector}
    (h : ElementaryPrecedes v u) : moment u < moment v := by
  obtain ⟨w1, w2⟩ := h
  simp only [moment, List.mapIdx_append, List.sum_append, List.mapIdx_cons]
  simp only [List.mapIdx_nil, List.sum_nil, List.sum_cons]
  simp +arith

-- Forward direction: v ≼ v' implies majorization.
-- By induction on ReflTransGen: the refl case is trivial; for the tail case,
-- use ElementaryPrecedes_q_eq and ElementaryPrecedes_partialSum_le at each step,
-- then chain inequalities by transitivity.
private lemma precedes_implies_majorization {v v' : ParityVector}
    (h : v ≼ v') (hlen : v.length = v'.length) :
    (∀ k, k + 2 ≤ v.length → partialSum v k ≤ partialSum v' k) ∧ q v = q v' := by
  unfold Precedes at h
  induction h with
  | refl =>
    exact ⟨fun _ _ => le_refl _, rfl⟩
  | tail hab hstep ih =>
    have hlen_step := ElementaryPrecedes_length_eq hstep
    obtain ⟨ih_sum, ih_q⟩ := ih (by omega)
    refine ⟨fun k hk => ?_, ?_⟩
    · exact le_trans (ih_sum k hk) (ElementaryPrecedes_partialSum_le hstep k)
    · exact ih_q.trans (ElementaryPrecedes_q_eq hstep)

-- Backward direction: majorization implies v ≼ v'.
-- By well-founded induction on moment v: if v = v' use refl; otherwise
-- exists_elementary_step_of_majorized_ne gives u with v ≺ u and u still majorized by v';
-- ElementaryPrecedes_moment_lt gives moment u < moment v, so IH applies to u ≼ v';
-- transitivity then gives v ≼ v'.
private lemma majorization_implies_precedes {v v' : ParityVector}
    (hlen : v.length = v'.length)
    (hsum : ∀ k, k + 2 ≤ v.length → partialSum v k ≤ partialSum v' k)
    (hq : q v = q v') : v ≼ v' := by
  suffices ∀ n, ∀ w : ParityVector, moment w = n → w.length = v'.length →
      (∀ k, k + 2 ≤ w.length → partialSum w k ≤ partialSum v' k) →
      q w = q v' → w ≼ v' from
    this (moment v) v rfl hlen hsum hq
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w hwn hlen' hsum' hq'
    by_cases hne : w = v'
    · subst hne; exact Relation.ReflTransGen.refl
    · obtain ⟨u, hep, hu_sum⟩ := exists_elementary_step_of_majorized_ne hlen' hsum' hq' hne
      have hlen_u : u.length = v'.length :=
        (ElementaryPrecedes_length_eq hep).symm ▸ hlen'
      have hq_u : q u = q v' :=
        (ElementaryPrecedes_q_eq hep) ▸ hq'
      have hmom : moment u < moment w := ElementaryPrecedes_moment_lt hep
      have hu_prec : u ≼ v' :=
        ih (moment u) (hwn ▸ hmom) u rfl hlen_u hu_sum hq_u
      exact Relation.ReflTransGen.head hep hu_prec

/-- **Unordered majorization characterization.** For two parity vectors `v` and `v'` of the
    same length `j`, we have `v ≼ v'` if and only if:
    (i)  `∑_{i=0}^{k} vᵢ ≤ ∑_{i=0}^{k} v'ᵢ` for all `0 ≤ k ≤ j - 2`, and
    (ii) `∑_{i=0}^{j-1} vᵢ = ∑_{i=0}^{j-1} v'ᵢ` (equal total number of ones).
    See [10, §5.D, p. 198]. -/
theorem precedes_iff_majorization (v v' : ParityVector) (hlen : v.length = v'.length) :
    v ≼ v' ↔
      (∀ k, k + 2 ≤ v.length → partialSum v k ≤ partialSum v' k) ∧
      q v = q v' :=
  ⟨fun h => precedes_implies_majorization h hlen,
   fun ⟨hsum, hq⟩ => majorization_implies_precedes hlen hsum hq⟩

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
  intro h
  exact Nat.lt_irrefl _ (elementary_weight_decrease h)

/-- `ElementaryPrecedes` is acyclic: there is no non-trivial cycle. -/
theorem elementaryPrecedes_acyclic (v : ParityVector) :
    ¬ Relation.TransGen ElementaryPrecedes v v := by
  intro h
  exact Nat.lt_irrefl _ (transGen_weight_lt h)

/-- `ElementaryPrecedes` is well-founded, i.e., there are no infinite descending chains.
    Together with the directed edges of `ElementaryPrecedes`, this makes the associated
    graph a finite directed acyclic graph (DAG). -/
private theorem weightFrom_le (n : ℕ) (v : List Bool) :
    weightFrom n v ≤ (n + v.length) * v.length := by
  induction v generalizing n with
  | nil => simp [weightFrom]
  | cons b bs ih =>
    simp only [weightFrom, List.length_cons]
    have hih := ih (n + 1)
    split
    · -- b = true, contributes n
      calc n + weightFrom (n + 1) bs
          ≤ n + (n + 1 + bs.length) * bs.length := by omega
        _ ≤ (n + (bs.length + 1)) * (bs.length + 1) := by nlinarith
    · -- b = false, contributes 0
      calc 0 + weightFrom (n + 1) bs
          ≤ (n + 1 + bs.length) * bs.length := by omega
        _ ≤ (n + (bs.length + 1)) * (bs.length + 1) := by nlinarith

private theorem weight_le (v : ParityVector) : weight v ≤ v.length * v.length := by
  have := weightFrom_le 0 v
  simp [weight] at this ⊢
  linarith

theorem elementaryPrecedes_wellFounded : WellFounded ElementaryPrecedes := by
  apply Subrelation.wf (r := InvImage (· < ·) fun v => v.length * v.length - weight v)
  · intro a b hab
    have hlen := ElementaryPrecedes_length_eq hab
    have hwt := elementary_weight_decrease hab
    have ha_bound := weight_le a
    have hb_bound := weight_le b
    dsimp only [InvImage]
    rw [hlen]
    exact Nat.sub_lt_sub_left (Nat.lt_of_lt_of_le hwt (hlen ▸ ha_bound)) hwt
  · exact InvImage.wf _ Nat.lt_wfRel.wf

end ParityVector
