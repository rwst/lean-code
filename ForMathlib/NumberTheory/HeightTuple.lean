/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/

module

public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.NumberTheory.Height.MvPolynomial

@[expose] public section

/-!
# Heights of tuples: sums along index maps, products of matrices, polynomial values

Mathlib bounds the height of a sum of *field elements*,
`Height.mulHeight₁_sum_le : mulHeight₁ (∑ a ∈ s, x a) ≤ #s ^ totalWeight K * ∏ a ∈ s, mulHeight₁ (x a)`,
and its logarithmic twin `Height.logHeight₁_sum_le`.  Both are sharp, and both are the wrong tool
for a matrix recursion `Aₖ₊₁ = Aₖ * Bₖ`: applied entry by entry they multiply the bound by the
size `m` of the matrices at every step, so `k` steps cost a factor `mᵏ`.

The remedy is the *projective* height `Height.mulHeight` of the tuple of all entries, whose local
factor at a place `v` is a supremum `⨆ i, v (x i)` rather than a product.  A supremum absorbs a
sum of `n` terms at the cost of a single factor `n` — and at a nonarchimedean place at no cost at
all.  So a matrix product costs one *additive* `totalWeight K * log m` per step instead of a
*multiplicative* `m`, and `k` steps cost `k * totalWeight K * log m`.

Mathlib already has the case of a matrix acting on a *vector*,
`Height.mulHeight_linearMap_apply_le : mulHeight (fun j ↦ ∑ i, A (j, i) * x i)
  ≤ Nat.card ι ^ totalWeight K * mulHeight A * mulHeight x`.
That does not give the product of two matrices: applying it column by column bounds the height of
each column of `A * B` separately, and heights of columns cannot be recombined into the height of
the whole matrix, since each column carries its own scaling.  The right statement quantifies over
a single tuple from which all the summands are read off, which is what `mulHeight_sum_comp_le`
below does; the linear-map bound is its special case `κ = (ι' × ι) × ι` with a Segre tuple.

## Main results

* `Height.mulHeight_sum_comp_le` — the general bound.  For a single tuple `w : κ → K` and a family
  of index maps `f a : ι → κ` indexed by `a ∈ s`,
  `mulHeight (fun i ↦ ∑ a ∈ s, w (f a i)) ≤ #s ^ totalWeight K * mulHeight w`.
  Note that all the terms are read off from *one* tuple `w`; see the counterexample below for why
  no bound of this shape can hold for a sum of unrelated tuples.
* `Matrix.mulHeight_mul_le`, `Matrix.logHeight_mul_le` — the height of a matrix product, and
  `Matrix.logHeight_listProd_le` for a product of a list of square matrices.
* `Height.mulHeight₁_div_le_mulHeight` — the bridge back to the affine height: the height of a
  ratio of two coordinates is at most the projective height of the tuple.  This is what turns a
  projective bound into a Liouville-style inequality for a single field element.
* `Height.mulHeight_le_prod_mulHeight₁` — the bridge the other way: the projective height of a
  tuple is at most the product of the affine heights of its entries.  This is what feeds
  entry-by-entry information (say, from `Height.logHeight₁_eval_le_of_polynomial`) into the
  projective machinery.
* `Height.mulHeightAff` — the **affine** height of a tuple (the projective height of the tuple
  with a `1` appended).  It dominates the height of each single coordinate
  (`Height.mulHeight₁_le_mulHeightAff`), which the projective height does *not*, and it still
  obeys the matrix-product bound with an additive cost per multiplication
  (`Matrix.logHeightAff_mul_le`, `Matrix.logHeightAff_listProd_le`).  This is the notion needed
  when the *entries* of an iterated product have to stay of controlled height.
* `Height.mulHeight₁_eval_le_of_degreeOf` — the height of the value of a multivariate polynomial,
  in the sharp form in which the degree in each variable enters *once* ([Wal00] Lemma 3.7).  The
  naive bound (Mathlib-adjacent `Height.logHeight₁_eval_le`) sums the degrees once per monomial
  and so carries a factor `#support`, which is exponential in the degree.  The sharp form comes
  out of the machinery above: `Height.mulHeight_pow_le` bounds the height of the tuple of powers
  `(1, β, …, β^d)` by `mulHeight₁ β ^ d`, `Height.mulHeight_monomial_le` multiplies those tables
  together, and `Height.mulHeight_linearMap_apply_le` contracts against the coefficients.

## The naive tuple analogue is false

The transcription of `mulHeight₁_sum_le` obtained by replacing `mulHeight₁` with `mulHeight`,

  `mulHeight (∑ a ∈ s, x a) ≤ #s ^ totalWeight K * ∏ a ∈ s, mulHeight (x a)`,

is **false**, and not for a reason that better constants would fix: `mulHeight` is invariant under
scaling (`Height.mulHeight_smul_eq_mulHeight`), while the left-hand side above is not.  Over `ℚ`,
`mulHeight ![c, 0] = mulHeight ![0, 1] = 1` for every `c ≠ 0`, whereas
`mulHeight (![c, 0] + ![0, 1]) = mulHeight ![c, 1] = mulHeight₁ c` is unbounded.  See
`Height.not_mulHeight_add_le_of_lt_mulHeight₁` and `Height.exists_not_mulHeight_add_le`.

This is why the results below are stated for sums drawn from a single tuple: it is exactly the
situation of a matrix product, where the scaling ambiguity of `A` and of `B` is inherited
consistently by `A * B`.

## References

The elementary inequalities for the Weil height of a projective point are classical; see e.g.
[BG06] Ch. 1.  The use made of them here — an additive per-step cost in a matrix recursion — is
that of [AF22] App. A.2, which runs the argument over the `S`-integers of a number field, where
the local factor at a place is again a maximum rather than a sum.

* [BG06] E. Bombieri, W. Gubler, *Heights in Diophantine Geometry*, New Math. Monographs 4,
  Cambridge Univ. Press 2006.
* [AF22] B. Adamczewski, C. Faverjon, *Mahler's method in several variables and finite automata*,
  2022.
-/

namespace Height

open AdmissibleAbsValues Real Function Finset

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {α ι κ : Type*}

/-! ### The local bounds -/

section Local

variable [Nonempty ι] [Finite κ]

/-- The nonarchimedean places at which the supremum of `v` over the entries of a nonzero tuple
differs from `1` are finite in number.  (Mathlib has this fact, but only as a `private` lemma
inside `Mathlib/NumberTheory/Height/Basic.lean`.) -/
theorem hasFiniteMulSupport_iSup_nonarchAbsVal {ι : Type*} [Finite ι] {x : ι → K} (hx : x ≠ 0) :
    (fun v : nonarchAbsVal (K := K) ↦ ⨆ i, v.val (x i)).HasFiniteMulSupport := by
  have : Nonempty {j // x j ≠ 0} := nonempty_subtype.mpr <| ne_iff.mp hx
  suffices (fun v : nonarchAbsVal ↦ ⨆ i : {j // x j ≠ 0}, v.val (x i)).HasFiniteMulSupport by
    convert! this with v
    obtain ⟨i, hi⟩ : ∃ j, x j ≠ 0 := Function.ne_iff.mp hx
    have : Nonempty ι := .intro i
    refine le_antisymm (ciSup_le fun j ↦ ?_) (ciSup_le fun ⟨j, hj⟩ ↦ Finite.le_ciSup_of_le j le_rfl)
    rcases eq_or_ne (x j) 0 with h | h
    · rw [h, v.val.map_zero]
      exact Real.iSup_nonneg' ⟨⟨i, hi⟩, v.val.nonneg ..⟩
    · exact Finite.le_ciSup_of_le ⟨j, h⟩ le_rfl
  exact HasFiniteMulSupport.iSup fun i ↦ AdmissibleAbsValues.hasFiniteMulSupport i.2

omit [AdmissibleAbsValues K] in
/-- The local form of the sum bound at an arbitrary absolute value, with the index set of the sum
allowed to depend on the coordinate: if every sum has at most `n` terms, then the supremum of `v`
over the entries of `fun i ↦ ∑ a ∈ s i, w (f a i)` is at most `n` times the supremum of `v` over
the entries of `w`. -/
theorem iSup_apply_sum_le' (v : AbsoluteValue K ℝ) {n : ℕ} {s : ι → Finset α}
    (hs : ∀ i, #(s i) ≤ n) (f : α → ι → κ) (w : κ → K) :
    ⨆ i, v (∑ a ∈ s i, w (f a i)) ≤ n * ⨆ k, v (w k) := by
  have hw : (0 : ℝ) ≤ ⨆ k, v (w k) := Real.iSup_nonneg_of_nonnegHomClass v _
  refine ciSup_le fun i ↦ ?_
  calc v (∑ a ∈ s i, w (f a i))
      ≤ ∑ a ∈ s i, v (w (f a i)) := v.sum_le _ _
    _ ≤ ∑ _a ∈ s i, ⨆ k, v (w k) :=
        Finset.sum_le_sum fun a _ ↦ Finite.le_ciSup_of_le (f a i) le_rfl
    _ = #(s i) * ⨆ k, v (w k) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ n * ⨆ k, v (w k) := by gcongr; exact_mod_cast hs i

omit [AdmissibleAbsValues K] in
/-- The local form of the sum bound at a nonarchimedean absolute value: there the factor `n`
disappears, because a nonarchimedean absolute value of a sum is bounded by the maximum of the
absolute values of the terms. -/
theorem iSup_apply_sum_le_of_isNonarchimedean' {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v)
    (s : ι → Finset α) (f : α → ι → κ) (w : κ → K) :
    ⨆ i, v (∑ a ∈ s i, w (f a i)) ≤ ⨆ k, v (w k) := by
  have hw : (0 : ℝ) ≤ ⨆ k, v (w k) := Real.iSup_nonneg_of_nonnegHomClass v _
  refine ciSup_le fun i ↦ ?_
  rcases (s i).eq_empty_or_nonempty with h | h
  · simp [h, hw]
  · exact (hv.apply_sum_le_sup h).trans <|
      Finset.sup'_le h _ fun a _ ↦ Finite.le_ciSup_of_le (f a i) le_rfl

omit [AdmissibleAbsValues K] in
/-- The local form of the sum bound at an arbitrary absolute value. -/
theorem iSup_apply_sum_le (v : AbsoluteValue K ℝ) (s : Finset α) (f : α → ι → κ) (w : κ → K) :
    ⨆ i, v (∑ a ∈ s, w (f a i)) ≤ #s * ⨆ k, v (w k) :=
  iSup_apply_sum_le' v (s := fun _ ↦ s) (fun _ ↦ le_rfl) f w

omit [AdmissibleAbsValues K] in
/-- The local form of the sum bound at a nonarchimedean absolute value. -/
theorem iSup_apply_sum_le_of_isNonarchimedean {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v)
    (s : Finset α) (f : α → ι → κ) (w : κ → K) :
    ⨆ i, v (∑ a ∈ s, w (f a i)) ≤ ⨆ k, v (w k) :=
  iSup_apply_sum_le_of_isNonarchimedean' hv (fun _ ↦ s) f w

end Local

/-! ### The height of a sum of entries of a single tuple -/

/-- **The projective sum bound.**  If every term of the sum is an entry of one and the same tuple
`w : κ → K`, read off along index maps `f a : ι → κ`, then the height of the resulting tuple
exceeds that of `w` by at most `#s ^ totalWeight K`.

Contrast `Height.mulHeight₁_sum_le`, whose right-hand side is a *product* of the heights of the
terms; here a single `mulHeight w` suffices, which is what makes an iteration cost an additive
rather than a multiplicative constant per step. -/
theorem mulHeight_sum_comp_le' [Finite ι] [Finite κ] {n : ℕ} (hn : 0 < n) {s : ι → Finset α}
    (hs : ∀ i, #(s i) ≤ n) (f : α → ι → κ) (w : κ → K) :
    mulHeight (fun i ↦ ∑ a ∈ s i, w (f a i)) ≤ (n : ℝ) ^ totalWeight K * mulHeight w := by
  have hcard : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hs1 : (1 : ℝ) ≤ (n : ℝ) ^ totalWeight K := one_le_pow₀ hcard
  rcases eq_or_ne (fun i ↦ ∑ a ∈ s i, w (f a i)) (0 : ι → K) with h0 | h0
  · rw [h0, mulHeight_zero]
    exact hs1.trans <| le_mul_of_one_le_right (by positivity) (one_le_mulHeight w)
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp h0
  have hι : Nonempty ι := ⟨i₀⟩
  have hw : w ≠ 0 := by
    rintro rfl
    exact hi₀ (by simp)
  obtain ⟨k₀, _⟩ := Function.ne_iff.mp hw
  have hκ : Nonempty κ := ⟨k₀⟩
  rw [mulHeight_eq h0, mulHeight_eq hw]
  have hconst : ((n : ℝ)) ^ totalWeight K
      = (Multiset.map (fun _ : AbsoluteValue K ℝ ↦ (n : ℝ)) archAbsVal).prod := by
    rw [Multiset.map_const', Multiset.prod_replicate]
    rfl
  rw [hconst, ← mul_assoc, ← Multiset.prod_map_mul]
  refine mul_le_mul ?_ ?_ ?_ ?_
  · exact Multiset.prod_map_le_prod_map₀ _ _
      (fun v _ ↦ Real.iSup_nonneg_of_nonnegHomClass v _) fun v _ ↦ iSup_apply_sum_le' v hs f w
  · exact finprod_le_finprod (hasFiniteMulSupport_iSup_nonarchAbsVal h0)
      (fun v ↦ Real.iSup_nonneg_of_nonnegHomClass v.val _)
      (hasFiniteMulSupport_iSup_nonarchAbsVal hw) fun v ↦
        iSup_apply_sum_le_of_isNonarchimedean' (isNonarchimedean _ v.prop) s f w
  · exact finprod_nonneg fun v ↦ Real.iSup_nonneg_of_nonnegHomClass v.val _
  · exact Multiset.prod_map_nonneg fun v _ ↦
      mul_nonneg (by positivity) (Real.iSup_nonneg_of_nonnegHomClass v _)

/-- **The projective sum bound**, all the sums over the same index set. -/
theorem mulHeight_sum_comp_le [Finite ι] [Finite κ] {s : Finset α} (hs : s.Nonempty)
    (f : α → ι → κ) (w : κ → K) :
    mulHeight (fun i ↦ ∑ a ∈ s, w (f a i)) ≤ (#s : ℝ) ^ totalWeight K * mulHeight w :=
  mulHeight_sum_comp_le' hs.card_pos (s := fun _ ↦ s) (fun _ ↦ le_rfl) f w

/-- The logarithmic form of `Height.mulHeight_sum_comp_le`. -/
theorem logHeight_sum_comp_le [Finite ι] [Finite κ] {s : Finset α} (hs : s.Nonempty)
    (f : α → ι → κ) (w : κ → K) :
    logHeight (fun i ↦ ∑ a ∈ s, w (f a i)) ≤ totalWeight K * log #s + logHeight w := by
  have hcard : (0 : ℝ) < (#s : ℝ) := by exact_mod_cast hs.card_pos
  simp only [logHeight_eq_log_mulHeight]
  refine (log_le_log (mulHeight_pos _) (mulHeight_sum_comp_le hs f w)).trans_eq ?_
  rw [log_mul (by positivity) (mulHeight_ne_zero w), log_pow]

/-! ### Projective versus affine heights -/

/-- The projective height of a tuple is at most the product of the affine heights of its entries.

The proof is the Segre embedding: `z` is a slice of the multiplication table of the tuples
`![z i, 1]`, whose height is the product of their heights by `Height.mulHeight_fun_prod_eq`. -/
theorem mulHeight_le_prod_mulHeight₁ [Fintype ι] [DecidableEq ι] (z : ι → K) :
    mulHeight z ≤ ∏ i, mulHeight₁ (z i) := by
  have hne : ∀ i : ι, (![z i, 1] : Fin 2 → K) ≠ 0 := fun i h ↦ by
    simpa using congrFun h 1
  have hcomp : (fun I : ι → Fin 2 ↦ ∏ i, (![z i, 1] : Fin 2 → K) (I i)) ∘
      (fun (i j : ι) ↦ if j = i then (0 : Fin 2) else 1) = z := by
    ext i
    simp only [Function.comp_apply]
    refine (Finset.prod_eq_single i (fun j _ hj ↦ by simp [hj]) (by simp)).trans ?_
    simp
  calc mulHeight z
      = mulHeight ((fun I : ι → Fin 2 ↦ ∏ i, (![z i, 1] : Fin 2 → K) (I i)) ∘
          fun (i j : ι) ↦ if j = i then (0 : Fin 2) else 1) := by rw [hcomp]
    _ ≤ mulHeight fun I : ι → Fin 2 ↦ ∏ i, (![z i, 1] : Fin 2 → K) (I i) := mulHeight_comp_le _ _
    _ = ∏ i, mulHeight (![z i, 1] : Fin 2 → K) := mulHeight_fun_prod_eq hne
    _ = ∏ i, mulHeight₁ (z i) := Finset.prod_congr rfl fun i _ ↦ (mulHeight₁_eq_mulHeight (z i)).symm

/-- The logarithmic form of `Height.mulHeight_le_prod_mulHeight₁`. -/
theorem logHeight_le_sum_logHeight₁ [Fintype ι] [DecidableEq ι] (z : ι → K) :
    logHeight z ≤ ∑ i, logHeight₁ (z i) := by
  simp only [logHeight_eq_log_mulHeight, logHeight₁_eq_log_mulHeight₁]
  rw [← Real.log_prod fun i _ ↦ mulHeight₁_ne_zero (z i)]
  exact Real.log_le_log (mulHeight_pos z) (mulHeight_le_prod_mulHeight₁ z)

/-! ### From projective to affine heights -/

/-- The affine height of a ratio of two coordinates is at most the projective height of the
tuple.  This is the bridge that turns a bound on `mulHeight` into a statement about a single
field element. -/
theorem mulHeight₁_div_le_mulHeight [Finite ι] (z : ι → K) (i j : ι) :
    mulHeight₁ (z i / z j) ≤ mulHeight z := by
  have h : ![z i, z j] = z ∘ ![i, j] := by ext k; fin_cases k <;> rfl
  rw [mulHeight₁_div_eq_mulHeight, h]
  exact mulHeight_comp_le ![i, j] z

/-- The logarithmic form of `Height.mulHeight₁_div_le_mulHeight`. -/
theorem logHeight₁_div_le_logHeight [Finite ι] (z : ι → K) (i j : ι) :
    logHeight₁ (z i / z j) ≤ logHeight z :=
  log_le_log (mulHeight₁_pos _) (mulHeight₁_div_le_mulHeight z i j)

/-! ### The affine height of a tuple -/

/-- The **affine** height of a tuple: the projective height of the tuple with a coordinate `1`
appended.

Unlike the projective `mulHeight`, this dominates the height of each single coordinate
(`mulHeight₁_le_mulHeightAff`) — for `mulHeight` that is false, since it is invariant under
scaling.  It still obeys the matrix-product bound with an additive cost per multiplication
(`Matrix.logHeightAff_mul_le`), which is what makes it the right notion for a matrix recursion
whose *entries* have to stay of controlled height. -/
noncomputable def mulHeightAff (x : ι → K) : ℝ := mulHeight fun o : Option ι ↦ o.elim 1 x

/-- The affine logarithmic height of a tuple. -/
noncomputable def logHeightAff (x : ι → K) : ℝ := log (mulHeightAff x)

theorem logHeightAff_eq_log_mulHeightAff (x : ι → K) :
    logHeightAff x = log (mulHeightAff x) := rfl

section Aff

variable [Finite ι]

theorem one_le_mulHeightAff (x : ι → K) : 1 ≤ mulHeightAff x := one_le_mulHeight _

theorem mulHeightAff_pos (x : ι → K) : 0 < mulHeightAff x := mulHeight_pos _

theorem mulHeightAff_ne_zero (x : ι → K) : mulHeightAff x ≠ 0 := mulHeight_ne_zero _

theorem logHeightAff_nonneg (x : ι → K) : 0 ≤ logHeightAff x := logHeight_nonneg _

/-- The affine height of a tuple dominates the affine height of each of its coordinates. -/
theorem mulHeight₁_le_mulHeightAff (x : ι → K) (i : ι) : mulHeight₁ (x i) ≤ mulHeightAff x := by
  have h : (![x i, 1] : Fin 2 → K) = (fun o : Option ι ↦ o.elim 1 x) ∘ ![some i, none] := by
    ext j; fin_cases j <;> rfl
  rw [mulHeight₁_eq_mulHeight, h]
  exact mulHeight_comp_le _ _

/-- The logarithmic form of `Height.mulHeight₁_le_mulHeightAff`. -/
theorem logHeight₁_le_logHeightAff (x : ι → K) (i : ι) : logHeight₁ (x i) ≤ logHeightAff x :=
  log_le_log (mulHeight₁_pos _) (mulHeight₁_le_mulHeightAff x i)

/-- The projective height of a tuple is at most its affine height. -/
theorem mulHeight_le_mulHeightAff (x : ι → K) : mulHeight x ≤ mulHeightAff x :=
  mulHeight_comp_le some fun o : Option ι ↦ o.elim 1 x

omit [Finite ι] in
/-- The affine height of a tuple is at most the product of the heights of its coordinates. -/
theorem mulHeightAff_le_prod_mulHeight₁ [Fintype ι] [DecidableEq ι] (x : ι → K) :
    mulHeightAff x ≤ ∏ i, mulHeight₁ (x i) := by
  refine (mulHeight_le_prod_mulHeight₁ _).trans ?_
  rw [Fintype.prod_option]
  simp

/-- The logarithmic form of `Height.mulHeightAff_le_prod_mulHeight₁`. -/
theorem logHeightAff_le_sum_logHeight₁ [Fintype ι] [DecidableEq ι] (x : ι → K) :
    logHeightAff x ≤ ∑ i, logHeight₁ (x i) := by
  simp only [logHeightAff_eq_log_mulHeightAff, logHeight₁_eq_log_mulHeight₁]
  rw [← Real.log_prod fun i _ ↦ mulHeight₁_ne_zero (x i)]
  exact Real.log_le_log (mulHeightAff_pos x) (mulHeightAff_le_prod_mulHeight₁ x)

end Aff

/-! ### The height of a polynomial value -/

/-- The projective height of the tuple of powers `(1, β, …, β ^ d)` is at most `mulHeight₁ β ^ d`.

The tuple is a slice of the multiplication table of `d` copies of `![1, β]`, whose height is
`mulHeight₁ β ^ d` by `Height.mulHeight_fun_prod_eq`. -/
theorem mulHeight_pow_le (β : K) (d : ℕ) :
    mulHeight (fun e : Fin (d + 1) ↦ β ^ (e : ℕ)) ≤ mulHeight₁ β ^ d := by
  classical
  have hne : ∀ _ : Fin d, (![1, β] : Fin 2 → K) ≠ 0 := fun _ h ↦ by simpa using congrFun h 0
  have hval : ∀ e : Fin (d + 1),
      (∏ j : Fin d, (![1, β] : Fin 2 → K) (if (j : ℕ) < (e : ℕ) then 1 else 0)) = β ^ (e : ℕ) := by
    intro e
    have he : (e : ℕ) ≤ d := Nat.lt_succ_iff.mp e.isLt
    rw [Fin.prod_univ_eq_prod_range fun j ↦ (![1, β] : Fin 2 → K) (if j < (e : ℕ) then 1 else 0)]
    have hb : ∀ j : ℕ, (![1, β] : Fin 2 → K) (if j < (e : ℕ) then 1 else 0)
        = if j < (e : ℕ) then β else 1 := by
      intro j; by_cases h : j < (e : ℕ) <;> simp [h]
    simp_rw [hb]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    have hfil : (Finset.range d).filter (fun j ↦ j < (e : ℕ)) = Finset.range (e : ℕ) := by
      ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [hfil, Finset.card_range]
  have hcomp : (fun e : Fin (d + 1) ↦ β ^ (e : ℕ))
      = (fun I : Fin d → Fin 2 ↦ ∏ j, (![1, β] : Fin 2 → K) (I j)) ∘
        fun e : Fin (d + 1) ↦ fun j : Fin d ↦ if (j : ℕ) < (e : ℕ) then 1 else 0 := by
    ext e; exact (hval e).symm
  have hone : mulHeight (![1, β] : Fin 2 → K) = mulHeight₁ β := by
    rw [mulHeight_swap, ← mulHeight₁_eq_mulHeight]
  rw [hcomp]
  refine (mulHeight_comp_le _ _).trans ?_
  rw [mulHeight_fun_prod_eq hne, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hone]

/-- The projective height of the tuple of all monomials `∏ i, β i ^ (I i)` with `I i ≤ d i`. -/
theorem mulHeight_monomial_le {σ : Type*} [Fintype σ] (β : σ → K) (d : σ → ℕ) :
    mulHeight (fun I : (i : σ) → Fin (d i + 1) ↦ ∏ i, β i ^ (I i : ℕ))
      ≤ ∏ i, mulHeight₁ (β i) ^ d i := by
  have hne : ∀ i : σ, (fun e : Fin (d i + 1) ↦ β i ^ (e : ℕ)) ≠ 0 := fun i h ↦ by
    simpa using congrFun h 0
  rw [mulHeight_fun_prod_eq hne]
  exact Finset.prod_le_prod (fun i _ ↦ (mulHeight_pos _).le) fun i _ ↦ mulHeight_pow_le (β i) (d i)

/-- **The height of the value of a multivariate polynomial**, in the sharp form: the degree in
each variable enters *once*, not once per monomial.  This is [Wal00] Lemma 3.7 (used by [AF22] as
their (2.33)).

Contrast `Height.logHeight₁_eval_le`, which bounds the value by a sum over the monomials of
`∑ i, m i * logHeight₁ (x i)`; that bound carries a factor `#support` in front of the degrees,
which is exponential in the degree and therefore useless whenever the polynomial is allowed to
grow. -/
theorem mulHeight₁_eval_le_of_degreeOf {σ : Type*} [Fintype σ] [DecidableEq σ]
    (β : σ → K) (P : MvPolynomial σ K) {d : σ → ℕ} (hd : ∀ i, P.degreeOf i ≤ d i) :
    mulHeight₁ (MvPolynomial.eval β P)
      ≤ ((#P.support + 1 : ℕ) : ℝ) ^ totalWeight K
        * (∏ ν ∈ P.support, mulHeight₁ (P.coeff ν)) * ∏ i, mulHeight₁ (β i) ^ d i := by
  classical
  set x : Option P.support → K :=
    fun o ↦ o.elim 1 fun ν ↦ ∏ i, β i ^ ((ν : σ →₀ ℕ) i) with hxdef
  set Amat : Fin 2 × Option P.support → K :=
    fun p ↦ if p.1 = 0 then p.2.elim 0 (fun ν ↦ P.coeff ν) else p.2.elim 1 fun _ ↦ 0 with hAdef
  have h0 : ∑ o : Option P.support, Amat (0, o) * x o = MvPolynomial.eval β P := by
    rw [Fintype.sum_option]
    simp only [hAdef, hxdef, Option.elim_none, Option.elim_some, ite_eq_left rfl, zero_mul, zero_add]
    rw [MvPolynomial.eval_eq', ← Finset.sum_coe_sort P.support
      (fun ν ↦ P.coeff ν * ∏ i, β i ^ (ν : σ →₀ ℕ) i)]
  have h1 : ∑ o : Option P.support, Amat (1, o) * x o = 1 := by
    rw [Fintype.sum_option]
    simp [hAdef, hxdef]
  have hval : (fun j : Fin 2 ↦ ∑ o : Option P.support, Amat (j, o) * x o)
      = ![MvPolynomial.eval β P, 1] := by
    ext j
    fin_cases j
    · simpa using h0
    · simpa using h1
  have hlin := mulHeight_linearMap_apply_le Amat x
  rw [hval, ← mulHeight₁_eq_mulHeight] at hlin
  have hcard : (Nat.card (Option P.support) : ℝ) = ((#P.support + 1 : ℕ) : ℝ) := by
    congr 1
    rw [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_coe]
  have hA : mulHeight Amat ≤ ∏ ν ∈ P.support, mulHeight₁ (P.coeff ν) := by
    refine (mulHeight_le_prod_mulHeight₁ _).trans ?_
    rw [Fintype.prod_prod_type]
    refine le_of_eq ?_
    rw [Fin.prod_univ_two]
    simp only [hAdef, ite_eq_left rfl, Fintype.prod_option, Option.elim_none, Option.elim_some,
      mulHeight₁_zero, one_mul]
    rw [Finset.prod_coe_sort P.support fun ν ↦ mulHeight₁ (P.coeff ν)]
    simp
  have hx : mulHeight x ≤ ∏ i, mulHeight₁ (β i) ^ d i := by
    have hg : ∀ ν : P.support, ∀ i, (ν : σ →₀ ℕ) i < d i + 1 := by
      intro ν i
      exact Nat.lt_succ_of_le ((MvPolynomial.monomial_le_degreeOf i ν.2).trans (hd i))
    have hcomp : x = (fun I : (i : σ) → Fin (d i + 1) ↦ ∏ i, β i ^ (I i : ℕ)) ∘
        fun o : Option P.support ↦ o.elim (fun i ↦ (0 : Fin (d i + 1)))
          fun ν i ↦ (⟨(ν : σ →₀ ℕ) i, hg ν i⟩ : Fin (d i + 1)) := by
      ext o
      cases o with
      | none => simp [hxdef]
      | some ν => simp [hxdef]
    rw [hcomp]
    exact (mulHeight_comp_le _ _).trans (mulHeight_monomial_le β d)
  rw [hcard] at hlin
  have hpow : (0 : ℝ) ≤ ((#P.support + 1 : ℕ) : ℝ) ^ totalWeight K := by positivity
  exact hlin.trans <| mul_le_mul (mul_le_mul_of_nonneg_left hA hpow) hx (mulHeight_pos _).le
    (mul_nonneg hpow (Finset.prod_nonneg fun ν _ ↦ (mulHeight₁_pos _).le))

/-- The logarithmic form of `Height.mulHeight₁_eval_le_of_degreeOf`: [AF22]'s (2.33). -/
theorem logHeight₁_eval_le_of_degreeOf {σ : Type*} [Fintype σ] [DecidableEq σ]
    (β : σ → K) (P : MvPolynomial σ K) {d : σ → ℕ} (hd : ∀ i, P.degreeOf i ≤ d i) :
    logHeight₁ (MvPolynomial.eval β P)
      ≤ totalWeight K * log ((#P.support + 1 : ℕ) : ℝ)
        + (∑ ν ∈ P.support, logHeight₁ (P.coeff ν)) + ∑ i, d i * logHeight₁ (β i) := by
  have hpos : (0 : ℝ) < ((#P.support + 1 : ℕ) : ℝ) := by positivity
  simp only [logHeight₁_eq_log_mulHeight₁]
  refine (Real.log_le_log (mulHeight₁_pos _)
    (mulHeight₁_eval_le_of_degreeOf β P hd)).trans_eq ?_
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_prod fun ν _ ↦ (mulHeight₁_pos _).ne',
    Real.log_prod fun i _ ↦ by positivity]
  simp only [Real.log_pow]

/-! ### The naive tuple analogue of `mulHeight₁_sum_le` is false -/

/-- Any field element whose height exceeds `2 ^ totalWeight K` refutes the tuple analogue of
`Height.mulHeight₁_sum_le`: the two tuples `![x, 0]` and `![0, 1]` both have height `1`, while
their sum `![x, 1]` has height `mulHeight₁ x`.  The mechanism is scaling invariance
(`Height.mulHeight_smul_eq_mulHeight`), which the left-hand side of such a bound does not enjoy,
so no choice of constant can repair the statement. -/
theorem not_mulHeight_add_le_of_lt_mulHeight₁ {x : K} (hx : (2 : ℝ) ^ totalWeight K < mulHeight₁ x) :
    ¬ mulHeight ((![x, 0] : Fin 2 → K) + (![0, 1] : Fin 2 → K))
        ≤ (2 : ℝ) ^ totalWeight K
            * (mulHeight (![x, 0] : Fin 2 → K) * mulHeight (![0, 1] : Fin 2 → K)) := by
  have h1 : (![x, 0] : Fin 2 → K) + (![0, 1] : Fin 2 → K) = ![x, 1] := by
    ext i; fin_cases i <;> simp
  rw [h1, ← mulHeight₁_eq_mulHeight]
  simpa using not_le.2 hx

/-- The tuple analogue of `Height.mulHeight₁_sum_le` fails already over `ℚ`. -/
theorem exists_not_mulHeight_add_le :
    ∃ x : ℚ, ¬ mulHeight ((![x, 0] : Fin 2 → ℚ) + (![0, 1] : Fin 2 → ℚ))
      ≤ (2 : ℝ) ^ totalWeight ℚ
          * (mulHeight (![x, 0] : Fin 2 → ℚ) * mulHeight (![0, 1] : Fin 2 → ℚ)) := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((2 : ℝ) ^ totalWeight ℚ)
  have hpos : (0 : ℝ) ≤ 2 ^ totalWeight ℚ := by positivity
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [Nat.cast_zero] at hn
    exact hpos.not_gt hn
  have : NeZero n := ⟨hn0⟩
  exact ⟨(n : ℚ), not_mulHeight_add_le_of_lt_mulHeight₁ (by rwa [Rat.mulHeight₁_natCast])⟩

end Height

/-! ### Heights of matrices -/

namespace Matrix

open Height

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {ι ι' ι'' : Type*}

/-- The (projective) multiplicative height of a matrix: the height of the tuple of its entries. -/
noncomputable def mulHeight (A : Matrix ι ι' K) : ℝ :=
  Height.mulHeight fun p : ι × ι' ↦ A p.1 p.2

/-- The (projective) logarithmic height of a matrix. -/
noncomputable def logHeight (A : Matrix ι ι' K) : ℝ := Real.log (mulHeight A)

theorem logHeight_eq_log_mulHeight (A : Matrix ι ι' K) : logHeight A = Real.log (mulHeight A) :=
  rfl

theorem one_le_mulHeight [Finite ι] [Finite ι'] (A : Matrix ι ι' K) : 1 ≤ mulHeight A :=
  Height.one_le_mulHeight _

theorem mulHeight_pos [Finite ι] [Finite ι'] (A : Matrix ι ι' K) : 0 < mulHeight A :=
  Height.mulHeight_pos _

theorem mulHeight_ne_zero [Finite ι] [Finite ι'] (A : Matrix ι ι' K) : mulHeight A ≠ 0 :=
  Height.mulHeight_ne_zero _

theorem logHeight_nonneg [Finite ι] [Finite ι'] (A : Matrix ι ι' K) : 0 ≤ logHeight A :=
  Height.logHeight_nonneg _

/-- The identity matrix has height `1`. -/
@[simp]
theorem mulHeight_one [Finite ι] [DecidableEq ι] : mulHeight (1 : Matrix ι ι K) = 1 := by
  refine le_antisymm ?_ (one_le_mulHeight _)
  have h : (fun p : ι × ι ↦ (1 : Matrix ι ι K) p.1 p.2)
      = (![1, 0] : Fin 2 → K) ∘ fun p : ι × ι ↦ if p.1 = p.2 then 0 else 1 := by
    ext p
    by_cases hp : p.1 = p.2 <;> simp [Matrix.one_apply, hp]
  rw [mulHeight, h]
  exact (Height.mulHeight_comp_le _ _).trans (by simp)

@[simp]
theorem logHeight_one [Finite ι] [DecidableEq ι] : logHeight (1 : Matrix ι ι K) = 0 := by
  simp [logHeight_eq_log_mulHeight]

/-- **The height of a matrix product.**  The projective height of `A * B` exceeds the product of
the projective heights of `A` and `B` by at most `(card ι') ^ totalWeight K`, where `ι'` is the
contracted index.  Compare `Height.mulHeight₁_mul_le`, which is entry by entry and therefore
loses a factor `card ι'` *per entry*. -/
theorem mulHeight_mul_le [Finite ι] [Fintype ι'] [Nonempty ι'] [Finite ι'']
    (A : Matrix ι ι' K) (B : Matrix ι' ι'' K) :
    mulHeight (A * B)
      ≤ (Fintype.card ι' : ℝ) ^ totalWeight K * (mulHeight A * mulHeight B) := by
  classical
  set x : ι × ι' → K := fun p ↦ A p.1 p.2 with hx
  set y : ι' × ι'' → K := fun p ↦ B p.1 p.2 with hy
  set w : (ι × ι') × (ι' × ι'') → K := fun q ↦ x q.1 * y q.2 with hw
  set f : ι' → (ι × ι'') → (ι × ι') × (ι' × ι'') := fun l p ↦ ((p.1, l), (l, p.2)) with hf
  have key : (fun p : ι × ι'' ↦ (A * B) p.1 p.2)
      = fun p : ι × ι'' ↦ ∑ l ∈ Finset.univ, w (f l p) := by
    ext p
    simp [Matrix.mul_apply, hw, hf, hx, hy]
  have hmain : mulHeight (A * B) ≤ (Fintype.card ι' : ℝ) ^ totalWeight K * Height.mulHeight w := by
    rw [mulHeight, key]
    simpa using Height.mulHeight_sum_comp_le Finset.univ_nonempty f w
  refine hmain.trans ?_
  have hle : Height.mulHeight w ≤ mulHeight A * mulHeight B := by
    rcases eq_or_ne x 0 with h | h
    · have : w = 0 := by rw [hw, h]; ext q; simp
      rw [this, Height.mulHeight_zero]
      exact one_le_mul_of_one_le_of_one_le (one_le_mulHeight A) (one_le_mulHeight B)
    rcases eq_or_ne y 0 with h' | h'
    · have : w = 0 := by rw [hw, h']; ext q; simp
      rw [this, Height.mulHeight_zero]
      exact one_le_mul_of_one_le_of_one_le (one_le_mulHeight A) (one_le_mulHeight B)
    exact le_of_eq (Height.mulHeight_fun_mul_eq h h')
  exact mul_le_mul_of_nonneg_left hle (by positivity)

/-- The logarithmic form of `Matrix.mulHeight_mul_le`: the cost of one matrix multiplication is
the *additive* constant `totalWeight K * log (card ι')`. -/
theorem logHeight_mul_le [Finite ι] [Fintype ι'] [Nonempty ι'] [Finite ι'']
    (A : Matrix ι ι' K) (B : Matrix ι' ι'' K) :
    logHeight (A * B)
      ≤ totalWeight K * Real.log (Fintype.card ι') + (logHeight A + logHeight B) := by
  have hcard : (0 : ℝ) < (Fintype.card ι' : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty ι'›
  simp only [logHeight_eq_log_mulHeight]
  refine (Real.log_le_log (mulHeight_pos _) (mulHeight_mul_le A B)).trans_eq ?_
  rw [Real.log_mul (pow_ne_zero _ hcard.ne')
      (mul_ne_zero (mulHeight_ne_zero A) (mulHeight_ne_zero B)), Real.log_pow,
    Real.log_mul (mulHeight_ne_zero A) (mulHeight_ne_zero B)]

/-- The projective height of a matrix is at most the product of the affine heights of its
entries: the entry-by-entry input to the machinery above. -/
theorem mulHeight_le_prod_mulHeight₁ [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']
    (A : Matrix ι ι' K) :
    mulHeight A ≤ ∏ p : ι × ι', Height.mulHeight₁ (A p.1 p.2) :=
  Height.mulHeight_le_prod_mulHeight₁ _

/-- The logarithmic form of `Matrix.mulHeight_le_prod_mulHeight₁`. -/
theorem logHeight_le_sum_logHeight₁ [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']
    (A : Matrix ι ι' K) :
    logHeight A ≤ ∑ p : ι × ι', Height.logHeight₁ (A p.1 p.2) :=
  Height.logHeight_le_sum_logHeight₁ _

/-! ### The affine height of a matrix -/

/-- The **affine** height of a matrix: the affine height of the tuple of its entries.  This is the
notion the entries of an iterated matrix product must be measured in — see
`Matrix.mulHeight₁_le_mulHeightAff`. -/
noncomputable def mulHeightAff (A : Matrix ι ι' K) : ℝ :=
  Height.mulHeightAff fun p : ι × ι' ↦ A p.1 p.2

/-- The affine logarithmic height of a matrix. -/
noncomputable def logHeightAff (A : Matrix ι ι' K) : ℝ := Real.log (mulHeightAff A)

theorem logHeightAff_eq_log_mulHeightAff (A : Matrix ι ι' K) :
    logHeightAff A = Real.log (mulHeightAff A) := rfl

theorem one_le_mulHeightAff [Finite ι] [Finite ι'] (A : Matrix ι ι' K) : 1 ≤ mulHeightAff A :=
  Height.one_le_mulHeightAff _

theorem mulHeightAff_pos [Finite ι] [Finite ι'] (A : Matrix ι ι' K) : 0 < mulHeightAff A :=
  Height.mulHeightAff_pos _

theorem mulHeightAff_ne_zero [Finite ι] [Finite ι'] (A : Matrix ι ι' K) : mulHeightAff A ≠ 0 :=
  Height.mulHeightAff_ne_zero _

theorem logHeightAff_nonneg [Finite ι] [Finite ι'] (A : Matrix ι ι' K) : 0 ≤ logHeightAff A :=
  Height.logHeightAff_nonneg _

/-- **Every entry of a matrix has height at most the affine height of the matrix.** -/
theorem mulHeight₁_le_mulHeightAff [Finite ι] [Finite ι'] (A : Matrix ι ι' K) (i : ι) (j : ι') :
    Height.mulHeight₁ (A i j) ≤ mulHeightAff A :=
  Height.mulHeight₁_le_mulHeightAff (fun p : ι × ι' ↦ A p.1 p.2) (i, j)

/-- The logarithmic form of `Matrix.mulHeight₁_le_mulHeightAff`. -/
theorem logHeight₁_le_logHeightAff [Finite ι] [Finite ι'] (A : Matrix ι ι' K) (i : ι) (j : ι') :
    Height.logHeight₁ (A i j) ≤ logHeightAff A :=
  Height.logHeight₁_le_logHeightAff (fun p : ι × ι' ↦ A p.1 p.2) (i, j)

theorem mulHeightAff_le_prod_mulHeight₁ [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']
    (A : Matrix ι ι' K) :
    mulHeightAff A ≤ ∏ p : ι × ι', Height.mulHeight₁ (A p.1 p.2) :=
  Height.mulHeightAff_le_prod_mulHeight₁ _

theorem logHeightAff_le_sum_logHeight₁ [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']
    (A : Matrix ι ι' K) :
    logHeightAff A ≤ ∑ p : ι × ι', Height.logHeight₁ (A p.1 p.2) :=
  Height.logHeightAff_le_sum_logHeight₁ _

/-- The identity matrix has affine height `1`. -/
@[simp]
theorem mulHeightAff_one [Finite ι] [DecidableEq ι] : mulHeightAff (1 : Matrix ι ι K) = 1 := by
  refine le_antisymm ?_ (one_le_mulHeightAff _)
  have h : (fun o : Option (ι × ι) ↦ o.elim 1 fun p ↦ (1 : Matrix ι ι K) p.1 p.2)
      = (![1, 0] : Fin 2 → K) ∘ fun o : Option (ι × ι) ↦
          o.elim 0 fun p ↦ if p.1 = p.2 then 0 else 1 := by
    ext o
    cases o with
    | none => rfl
    | some p => by_cases hp : p.1 = p.2 <;> simp [Matrix.one_apply, hp]
  rw [mulHeightAff, Height.mulHeightAff, h]
  exact (Height.mulHeight_comp_le _ _).trans (by simp)

@[simp]
theorem logHeightAff_one [Finite ι] [DecidableEq ι] : logHeightAff (1 : Matrix ι ι K) = 0 := by
  simp [logHeightAff_eq_log_mulHeightAff]

/-- **The affine height of a matrix product.**  As for the projective height, the cost of one
multiplication is a single factor `(card ι') ^ totalWeight K`; unlike the projective height, the
conclusion bounds the height of every *entry* of the product. -/
theorem mulHeightAff_mul_le [Finite ι] [Fintype ι'] [Nonempty ι'] [Finite ι'']
    (A : Matrix ι ι' K) (B : Matrix ι' ι'' K) :
    mulHeightAff (A * B)
      ≤ (Fintype.card ι' : ℝ) ^ totalWeight K * (mulHeightAff A * mulHeightAff B) := by
  classical
  obtain ⟨l₀⟩ := ‹Nonempty ι'›
  set x : Option (ι × ι') → K := fun o ↦ o.elim 1 fun p ↦ A p.1 p.2 with hx
  set y : Option (ι' × ι'') → K := fun o ↦ o.elim 1 fun p ↦ B p.1 p.2 with hy
  set w : Option (ι × ι') × Option (ι' × ι'') → K := fun q ↦ x q.1 * y q.2 with hw
  set s : Option (ι × ι'') → Finset ι' := fun o ↦ o.elim {l₀} fun _ ↦ Finset.univ with hs
  set f : ι' → Option (ι × ι'') → Option (ι × ι') × Option (ι' × ι'') :=
    fun l o ↦ o.elim (none, none) fun p ↦ (some (p.1, l), some (l, p.2)) with hf
  have key : (fun o : Option (ι × ι'') ↦ o.elim 1 fun p ↦ (A * B) p.1 p.2)
      = fun o ↦ ∑ l ∈ s o, w (f l o) := by
    ext o
    cases o with
    | none => simp [hs, hf, hw, hx, hy]
    | some p => simp [hs, hf, hw, hx, hy, Matrix.mul_apply]
  have hcard : ∀ o, (s o).card ≤ Fintype.card ι' := by
    intro o
    cases o with
    | none => simpa [hs] using Fintype.card_pos.nat_succ_le
    | some p => simp [hs, Finset.card_univ]
  have hx0 : x ≠ 0 := fun h ↦ by simpa [hx] using congrFun h none
  have hy0 : y ≠ 0 := fun h ↦ by simpa [hy] using congrFun h none
  rw [mulHeightAff, Height.mulHeightAff, key]
  refine (Height.mulHeight_sum_comp_le' Fintype.card_pos hcard f w).trans ?_
  rw [Height.mulHeight_fun_mul_eq hx0 hy0]
  rfl

/-- The logarithmic form of `Matrix.mulHeightAff_mul_le`. -/
theorem logHeightAff_mul_le [Finite ι] [Fintype ι'] [Nonempty ι'] [Finite ι'']
    (A : Matrix ι ι' K) (B : Matrix ι' ι'' K) :
    logHeightAff (A * B)
      ≤ totalWeight K * Real.log (Fintype.card ι') + (logHeightAff A + logHeightAff B) := by
  have hcard : (0 : ℝ) < (Fintype.card ι' : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty ι'›
  simp only [logHeightAff_eq_log_mulHeightAff]
  refine (Real.log_le_log (mulHeightAff_pos _) (mulHeightAff_mul_le A B)).trans_eq ?_
  rw [Real.log_mul (pow_ne_zero _ hcard.ne')
      (mul_ne_zero (mulHeightAff_ne_zero A) (mulHeightAff_ne_zero B)), Real.log_pow,
    Real.log_mul (mulHeightAff_ne_zero A) (mulHeightAff_ne_zero B)]

/-- **The affine height of a product of a list of square matrices.**  Each factor costs its own
affine height plus one additive `totalWeight K * log (card ι)` — so `k` factors cost
`k * totalWeight K * log (card ι)` on top of the sum of their heights, never a factor
`(card ι) ^ k`. -/
theorem logHeightAff_listProd_le [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (l : List (Matrix ι ι K)) :
    logHeightAff l.prod
      ≤ l.length * (totalWeight K * Real.log (Fintype.card ι)) + (l.map logHeightAff).sum := by
  induction l with
  | nil => simp
  | cons A t ih =>
    rw [List.prod_cons]
    refine (logHeightAff_mul_le A t.prod).trans ?_
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_one]
    linarith

/-- The logarithmic height of a product of a list of square matrices: each factor of the product
costs its own height plus one additive `totalWeight K * log (card ι)`. -/
theorem logHeight_listProd_le [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (l : List (Matrix ι ι K)) :
    logHeight l.prod
      ≤ l.length * (totalWeight K * Real.log (Fintype.card ι)) + (l.map logHeight).sum := by
  induction l with
  | nil => simp
  | cons A t ih =>
    rw [List.prod_cons]
    refine (logHeight_mul_le A t.prod).trans ?_
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_one]
    linarith

end Matrix
