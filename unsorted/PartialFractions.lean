import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic

noncomputable section

open scoped Classical
open Polynomial

variable {K : Type*} [Field K]

/-~!
NOTE. This code would greatly benefit if RatFunc were an abbrev. Search Zulip for that.
-/

/-! This code bridges the gap between RatFunc (where partial fractions happen) and PowerSeries
(where you want the coefficients), and introduces the specific polynomials required for
the "coefficient formula."
-/

open RatFunc

/-!
### 1. Reverse Partial Fractions Structure
Mathlib has partial fractions, but not specifically optimized for the form
c / (1 - αX)^k, which is the "generating function friendly" format.
-/

/-- A single term in the partial fraction decomposition: c / (1 - αX)^k -/
structure GenFuncPartialFraction (L : Type*) [Field L] where
  c     : L  -- The numerator coefficient
  alpha : L  -- The reciprocal of the root (i.e., the base of the geometric series)
  k     : ℕ  -- The multiplicity/power (must be ≥ 1)

/-!
### 2. Standard Partial Fractions Structure

A term in the classical partial fraction decomposition: c / (X - r)^k
-/

/-- A single term in the standard partial fraction decomposition: c / (X - r)^k -/
structure StandardPartialFraction (L : Type*) [Field L] where
  c : L      -- The numerator coefficient
  root : L   -- The root r
  k : ℕ      -- The multiplicity/power (k ≥ 1)

/-!
### 3. Missing Infrastructure Lemmas

These lemmas bridge standard partial fractions to the generating function form.
-/

/-! ### Helper lemmas for the partial fraction proof -/

/-- Local helper: `X ≠ C r` in `RatFunc L`. -/
private lemma RatFunc_X_ne_C_aux (L : Type*) [Field L] (r : L) :
    (RatFunc.X : RatFunc L) ≠ RatFunc.C r := by
  intro heq
  have := congrArg RatFunc.num heq
  simp only [RatFunc.num_X, RatFunc.num_C] at this
  have hdeg : (Polynomial.X : L[X]).natDegree = (Polynomial.C r).natDegree := by rw [this]
  simp at hdeg

private lemma RatFunc_coe_X_sub_C_mul (L : Type*) [Field L] (r : L) (p : L[X]) :
    (((Polynomial.X - Polynomial.C r) * p : L[X]) : RatFunc L) =
      (RatFunc.X - RatFunc.C r) * (p : RatFunc L) := by
  rw [RatFunc.coePolynomial_eq_algebraMap, map_mul, map_sub,
    RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  rfl

/-- The key partial fraction identity in `RatFunc L`:
`C((r-s)^k) / ((X-Cr)(X-Cs)^k) = 1/(X-Cr) - ∑ᵢ C((r-s)^i)/(X-Cs)^(i+1)`. -/
private lemma rat_atomic_identity (L : Type*) [Field L] (r s : L) (k : ℕ) :
    (RatFunc.C ((r - s) ^ k) : RatFunc L) /
        ((RatFunc.X - RatFunc.C r) * (RatFunc.X - RatFunc.C s) ^ k) =
      1 / (RatFunc.X - RatFunc.C r) -
        ∑ i ∈ Finset.range k,
          RatFunc.C ((r - s) ^ i) / (RatFunc.X - RatFunc.C s) ^ (i + 1) := by
  have hXr_ne : (RatFunc.X - RatFunc.C r : RatFunc L) ≠ 0 := fun h =>
    RatFunc_X_ne_C_aux L r (sub_eq_zero.mp h)
  have hXs_ne : (RatFunc.X - RatFunc.C s : RatFunc L) ≠ 0 := fun h =>
    RatFunc_X_ne_C_aux L s (sub_eq_zero.mp h)
  have hgeom := geom_sum₂_mul (RatFunc.X - RatFunc.C s : RatFunc L) (RatFunc.C (r - s)) k
  have hsubst : (RatFunc.X - RatFunc.C s) - RatFunc.C (r - s) =
      (RatFunc.X - RatFunc.C r : RatFunc L) := by
    rw [show (RatFunc.C (r - s) : RatFunc L) = RatFunc.C r - RatFunc.C s from map_sub _ _ _]
    ring
  rw [hsubst] at hgeom
  have hCp : ∀ n, (RatFunc.C ((r - s)^n) : RatFunc L) = RatFunc.C (r - s) ^ n :=
    fun n => by rw [← map_pow]
  simp_rw [hCp]
  have hgeom2 : (∑ i ∈ Finset.range k, (RatFunc.X - RatFunc.C s : RatFunc L) ^ (k - 1 - i) *
        RatFunc.C (r - s) ^ i) * (RatFunc.X - RatFunc.C r) =
      (RatFunc.X - RatFunc.C s) ^ k - RatFunc.C (r - s) ^ k := by
    rw [← hgeom]
    congr 1
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    have : k - 1 - (k - 1 - i) = i := by omega
    rw [this]
  set S := ∑ i ∈ Finset.range k,
      (RatFunc.X - RatFunc.C s : RatFunc L) ^ (k - 1 - i) * RatFunc.C (r - s) ^ i with hS_def
  have hsum_id :
      ∑ i ∈ Finset.range k, (RatFunc.C (r - s) : RatFunc L) ^ i /
          (RatFunc.X - RatFunc.C s) ^ (i + 1) =
      S / (RatFunc.X - RatFunc.C s) ^ k := by
    rw [hS_def, Finset.sum_div]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [div_eq_div_iff (pow_ne_zero _ hXs_ne) (pow_ne_zero _ hXs_ne)]
    rw [show ((RatFunc.X - RatFunc.C s : RatFunc L) ^ k) =
        (RatFunc.X - RatFunc.C s) ^ (i + 1) * (RatFunc.X - RatFunc.C s) ^ (k - i - 1) from by
      rw [← pow_add]; congr 1; omega]
    rw [show ((RatFunc.X - RatFunc.C s : RatFunc L) ^ (k - 1 - i)) =
        (RatFunc.X - RatFunc.C s) ^ (k - i - 1) from by congr 1; omega]
    ring
  rw [hsum_id, div_sub_div _ _ hXr_ne (pow_ne_zero _ hXs_ne)]
  rw [div_eq_div_iff (mul_ne_zero hXr_ne (pow_ne_zero _ hXs_ne))
      (mul_ne_zero hXr_ne (pow_ne_zero _ hXs_ne))]
  linear_combination (RatFunc.X - RatFunc.C r) * (RatFunc.X - RatFunc.C s) ^ k * hgeom2

/-- Helper converting `List.range k` sums to `Finset.range k` sums. -/
private lemma list_range_sum_eq_finset_sum {M : Type*} [AddCommMonoid M]
    (k : ℕ) (g : ℕ → M) :
    ((List.range k).map g).sum = ∑ i ∈ Finset.range k, g i := by
  induction k with
  | zero => simp
  | succ n ihn =>
    rw [List.range_succ, List.map_append, List.sum_append, ihn, Finset.sum_range_succ]
    simp

/-- Helper: given one "atomic" term `c / ((X - C r) * (X - C s)^k)` in `RatFunc L`,
produce a list of standard partial fractions that sums to it. The produced list uses
only the roots `r` and `s`, with powers `≥ 1`. -/
private lemma pfd_step_atom (L : Type*) [Field L] (c : L) (r s : L) (k : ℕ) (hk : 1 ≤ k) :
    ∃ (ts : List (StandardPartialFraction L)),
      (∀ t ∈ ts, t.root = r ∨ t.root = s) ∧
      (∀ t ∈ ts, t.k ≥ 1) ∧
      (∀ t ∈ ts, t.root = s → t.k ≤ (if r = s then k + 1 else k)) ∧
      (∀ t ∈ ts, t.root ≠ s → t.k ≤ 1) ∧
      (RatFunc.C c : RatFunc L) /
          ((RatFunc.X - RatFunc.C r) * (RatFunc.X - RatFunc.C s) ^ k) =
      (ts.map fun t => RatFunc.C t.c / (RatFunc.X - RatFunc.C t.root) ^ t.k).sum := by
  have hXr_ne : (RatFunc.X - RatFunc.C r : RatFunc L) ≠ 0 := fun h =>
    RatFunc_X_ne_C_aux L r (sub_eq_zero.mp h)
  have hXs_ne : (RatFunc.X - RatFunc.C s : RatFunc L) ≠ 0 := fun h =>
    RatFunc_X_ne_C_aux L s (sub_eq_zero.mp h)
  by_cases hrs : r = s
  · -- (X - C r) * (X - C s)^k = (X - C s)^(k+1)
    refine ⟨[⟨c, s, k + 1⟩], ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht
      simp only [List.mem_singleton] at ht
      right; rw [ht]
    · intro t ht
      simp only [List.mem_singleton] at ht
      rw [ht]; dsimp; omega
    · intro t ht _ ; simp only [List.mem_singleton] at ht; rw [ht]; simp [hrs]
    · intro t ht hne; simp only [List.mem_singleton] at ht; rw [ht] at hne; simp at hne
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      subst hrs
      rw [show (RatFunc.X - RatFunc.C r : RatFunc L) * (RatFunc.X - RatFunc.C r) ^ k =
        (RatFunc.X - RatFunc.C r) ^ (k + 1) from by ring]
  · -- r ≠ s, so d = (r - s)^k ≠ 0; use rat_atomic_identity
    have hrs_ne : r - s ≠ 0 := sub_ne_zero.mpr hrs
    have hd_ne : (r - s) ^ k ≠ 0 := pow_ne_zero _ hrs_ne
    have hCd_ne : (RatFunc.C ((r - s) ^ k) : RatFunc L) ≠ 0 :=
      (map_ne_zero_iff RatFunc.C RatFunc.C_injective).2 hd_ne
    have hid := rat_atomic_identity L r s k
    -- Multiply both sides of hid by C c / C ((r - s)^k)
    have hmul : (RatFunc.C c : RatFunc L) /
          ((RatFunc.X - RatFunc.C r) * (RatFunc.X - RatFunc.C s) ^ k) =
        (RatFunc.C c / RatFunc.C ((r - s) ^ k)) * (1 / (RatFunc.X - RatFunc.C r)) -
        (RatFunc.C c / RatFunc.C ((r - s) ^ k)) *
          ∑ i ∈ Finset.range k,
            RatFunc.C ((r - s) ^ i) / (RatFunc.X - RatFunc.C s) ^ (i + 1) := by
      rw [← mul_sub, ← hid]
      field_simp
    -- Convert the coefficients into RatFunc.C form.
    -- The first main term: (c / (r-s)^k) * (1 / (X - C r)) = C (c / (r-s)^k) / (X - C r)^1
    -- The sum term: for each i, the contribution is
    --   - c * (r-s)^i / (r-s)^k * 1 / (X - C s)^(i+1) = C (-c*(r-s)^i/(r-s)^k) / (X - C s)^(i+1)
    -- Build the list: first term for r, then k terms for s (i = 0, ..., k-1).
    refine ⟨⟨c / (r - s) ^ k, r, 1⟩ :: (List.range k).map
        (fun i => (⟨-(c * (r - s) ^ i / (r - s) ^ k), s, i + 1⟩ :
          StandardPartialFraction L)), ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht
      rw [List.mem_cons] at ht
      rcases ht with ht | ht
      · left; rw [ht]
      · rw [List.mem_map] at ht
        obtain ⟨i, _, hti⟩ := ht
        right; rw [← hti]
    · intro t ht
      rw [List.mem_cons] at ht
      rcases ht with ht | ht
      · rw [ht]
      · rw [List.mem_map] at ht
        obtain ⟨i, _, hti⟩ := ht
        rw [← hti]; dsimp; omega
    · -- k-bound for root s
      intro t ht hts
      rw [List.mem_cons] at ht
      rcases ht with ht | ht
      · rw [ht] at hts; exact absurd hts hrs
      · rw [List.mem_map] at ht
        obtain ⟨i, hi, hti⟩ := ht
        rw [← hti]; dsimp; simp [hrs]
        rw [List.mem_range] at hi; omega
    · -- k-bound for root ≠ s
      intro t ht hne
      rw [List.mem_cons] at ht
      rcases ht with ht | ht
      · rw [ht]
      · rw [List.mem_map] at ht
        obtain ⟨i, _, hti⟩ := ht
        rw [← hti] at hne; simp at hne
    · -- Compute the list sum, using the identity.
      rw [hmul]
      simp only [List.map_cons, List.sum_cons, List.map_map, pow_one]
      -- The composite map over List.range k gives a function we can rewrite.
      have hcomp : ((fun t : StandardPartialFraction L =>
          RatFunc.C t.c / (RatFunc.X - RatFunc.C t.root) ^ t.k) ∘
          (fun i : ℕ => (⟨-(c * (r - s) ^ i / (r - s) ^ k), s, i + 1⟩ :
            StandardPartialFraction L))) =
          (fun i : ℕ => RatFunc.C (-(c * (r - s) ^ i / (r - s) ^ k)) /
            (RatFunc.X - RatFunc.C s) ^ (i + 1)) := by
        funext i; rfl
      rw [hcomp, list_range_sum_eq_finset_sum]
      -- Rewrite the C operations to pull out constants.
      have hCeach : ∀ i : ℕ,
          (RatFunc.C (-(c * (r - s) ^ i / (r - s) ^ k)) : RatFunc L) /
              (RatFunc.X - RatFunc.C s) ^ (i + 1) =
          -((RatFunc.C c / RatFunc.C ((r - s) ^ k)) *
            (RatFunc.C ((r - s) ^ i) / (RatFunc.X - RatFunc.C s) ^ (i + 1))) := by
        intro i
        rw [show (-(c * (r - s) ^ i / (r - s) ^ k) : L) =
            -(c * (r - s) ^ i) / (r - s) ^ k from by ring]
        rw [map_div₀, map_neg, map_mul, neg_div]
        field_simp
      simp_rw [hCeach]
      rw [show (RatFunc.C (c / (r - s) ^ k) : RatFunc L) =
          RatFunc.C c / RatFunc.C ((r - s) ^ k) from map_div₀ _ _ _]
      rw [show (∑ x ∈ Finset.range k,
          -(RatFunc.C c / RatFunc.C ((r - s) ^ k) *
            (RatFunc.C ((r - s) ^ x) / (RatFunc.X - RatFunc.C s) ^ (x + 1)))) =
          -(RatFunc.C c / RatFunc.C ((r - s) ^ k) *
            ∑ x ∈ Finset.range k,
              RatFunc.C ((r - s) ^ x) / (RatFunc.X - RatFunc.C s) ^ (x + 1)) from by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]]
      ring

/-- Helper: introducing a new factor `(X - C r)` to a partial-fraction decomposition.
Given a decomposition of some `F : RatFunc L` as a sum of terms `c_i / (X - C r_i)^{k_i}`,
produce a decomposition of `F / (X - C r)` as such a sum. -/
private lemma pfd_step_list (L : Type*) [Field L] (r : L)
    (ts : List (StandardPartialFraction L))
    (hts : ∀ t ∈ ts, t.k ≥ 1) :
    ∃ (ts' : List (StandardPartialFraction L)),
      (∀ t' ∈ ts', t'.root = r ∨ ∃ t ∈ ts, t'.root = t.root) ∧
      (∀ t' ∈ ts', t'.k ≥ 1) ∧
      (∀ (bound : L → ℕ), (∀ t ∈ ts, t.k ≤ bound t.root) →
        ∀ t' ∈ ts', t'.k ≤ if t'.root = r then bound r + 1 else bound t'.root) ∧
      (ts.map fun t => RatFunc.C t.c / (RatFunc.X - RatFunc.C t.root) ^ t.k).sum /
          (RatFunc.X - RatFunc.C r) =
      (ts'.map fun t => RatFunc.C t.c / (RatFunc.X - RatFunc.C t.root) ^ t.k).sum := by
  induction ts with
  | nil =>
    refine ⟨[], ?_, ?_, ?_, ?_⟩
    · intro t' ht'; simp at ht'
    · intro t' ht'; simp at ht'
    · intro _ _ t' ht'; simp at ht'
    · simp
  | cons t rest ih =>
    have hrest : ∀ t ∈ rest, t.k ≥ 1 := fun t ht => hts t (List.mem_cons_of_mem _ ht)
    obtain ⟨rest', hrest_root, hrest_k, hrest_bound, hrest_eq⟩ := ih hrest
    have ht_k : t.k ≥ 1 := hts t (List.mem_cons_self)
    obtain ⟨tterms, htterms_root, htterms_k, htterms_s_bound, htterms_ns_bound,
        htterms_eq⟩ :=
      pfd_step_atom L t.c r t.root t.k ht_k
    refine ⟨tterms ++ rest', ?_, ?_, ?_, ?_⟩
    · intro t' ht'
      rw [List.mem_append] at ht'
      rcases ht' with ht' | ht'
      · rcases htterms_root t' ht' with hr | hs
        · left; exact hr
        · right; exact ⟨t, List.mem_cons_self, hs⟩
      · rcases hrest_root t' ht' with hr | ⟨t0, ht0, ht0eq⟩
        · left; exact hr
        · right; exact ⟨t0, List.mem_cons_of_mem _ ht0, ht0eq⟩
    · intro t' ht'
      rw [List.mem_append] at ht'
      rcases ht' with ht' | ht'
      · exact htterms_k t' ht'
      · exact hrest_k t' ht'
    · -- k-bound propagation
      intro bound h_bound t' ht'
      rw [List.mem_append] at ht'
      have h_t_bound : t.k ≤ bound t.root := h_bound t (List.mem_cons_self)
      rcases ht' with ht' | ht'
      · -- t' comes from tterms (atom decomposition of t)
        by_cases h_eq : t'.root = r
        · -- t'.root = r
          rw [if_pos h_eq]
          by_cases hrs : r = t.root
          · -- r = t.root, so htterms_s_bound applies (t'.root = r = t.root)
            have h1 := htterms_s_bound t' ht' (h_eq.trans hrs)
            simp [hrs] at h1; rw [← hrs] at h_t_bound; omega
          · -- r ≠ t.root, so t'.root ≠ t.root, use htterms_ns_bound
            have hne : t'.root ≠ t.root := fun h => hrs (h_eq ▸ h ▸ rfl)
            have h1 := htterms_ns_bound t' ht' hne
            omega
        · -- t'.root ≠ r
          rw [if_neg h_eq]
          -- t' must have t'.root = t.root (the only other option from htterms_root)
          have hs : t'.root = t.root := by
            rcases htterms_root t' ht' with hr | hs
            · exact absurd hr h_eq
            · exact hs
          have h1 := htterms_s_bound t' ht' hs
          have hrs : r ≠ t.root := fun h => h_eq (hs ▸ h.symm ▸ rfl)
          simp [hrs] at h1
          rw [hs]; linarith
      · -- t' comes from rest' (recursive IH)
        have h_rest_bound : ∀ t_r ∈ rest, t_r.k ≤ bound t_r.root :=
          fun t_r ht_r => h_bound t_r (List.mem_cons_of_mem _ ht_r)
        exact hrest_bound bound h_rest_bound t' ht'
    · simp only [List.map_cons, List.sum_cons, List.map_append, List.sum_append]
      rw [add_div, ← hrest_eq]
      have hXr_ne : (RatFunc.X - RatFunc.C r : RatFunc L) ≠ 0 := fun h =>
        RatFunc_X_ne_C_aux L r (sub_eq_zero.mp h)
      have hXtroot_ne : (RatFunc.X - RatFunc.C t.root : RatFunc L) ≠ 0 := fun h =>
        RatFunc_X_ne_C_aux L t.root (sub_eq_zero.mp h)
      rw [← htterms_eq]
      congr 1
      rw [div_div, mul_comm]

/-- Core helper over `L[X]`: any polynomial that splits with `natDegree ≥ 1` has
a standard partial fraction decomposition. -/
private lemma pfd_aux (L : Type*) [Field L] :
    ∀ (n : ℕ) (f : L[X]), f.natDegree = n → f ≠ 0 → f.Splits →
      1 ≤ f.natDegree →
      ∃ (terms : List (StandardPartialFraction L)),
        (∀ t ∈ terms, f.IsRoot t.root) ∧
        (∀ t ∈ terms, t.k ≥ 1) ∧
        (∀ t ∈ terms, t.k ≤ Polynomial.rootMultiplicity t.root f) ∧
        (1 : RatFunc L) / (f : RatFunc L) =
        (terms.map fun t => RatFunc.C t.c / (RatFunc.X - RatFunc.C t.root) ^ t.k).sum := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro f hfn hf_ne hsplits hdeg
    -- Get a root of f
    have hdeg_pos : 0 < f.natDegree := hdeg
    have hdeg_ne_zero : f.natDegree ≠ 0 := Nat.pos_iff_ne_zero.mp hdeg_pos
    have hdeg_ne : f.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hf_ne]
      intro hcast
      have : f.natDegree = 0 := by exact_mod_cast hcast
      exact hdeg_ne_zero this
    obtain ⟨r, hr_root⟩ := hsplits.exists_eval_eq_zero hdeg_ne
    -- Factor f = (X - C r) * g with g = f /ₘ (X - C r)
    set g : L[X] := f /ₘ (Polynomial.X - Polynomial.C r) with hg_def
    have hroot : f.IsRoot r := hr_root
    have hfact : (Polynomial.X - Polynomial.C r) * g = f :=
      Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot
    have hXCr_monic : (Polynomial.X - Polynomial.C r : L[X]).Monic := Polynomial.monic_X_sub_C r
    have hXCr_ne : (Polynomial.X - Polynomial.C r : L[X]) ≠ 0 := hXCr_monic.ne_zero
    have hg_ne : g ≠ 0 := by
      intro hg0
      rw [hg0, mul_zero] at hfact
      exact hf_ne hfact.symm
    have hg_deg : g.natDegree = f.natDegree - 1 := by
      rw [hg_def, Polynomial.natDegree_divByMonic f hXCr_monic, Polynomial.natDegree_X_sub_C]
    have hg_splits : g.Splits := by
      apply Polynomial.Splits.of_dvd hsplits hf_ne
      exact ⟨Polynomial.X - Polynomial.C r, by rw [mul_comm]; exact hfact.symm⟩
    -- Case split on whether g is a constant or not.
    by_cases hg_const : g.natDegree = 0
    · -- g has degree 0, so f = (X - C r) * g where g is constant nonzero.
      -- Then 1/f = g⁻¹ * 1/(X - C r)
      obtain ⟨a, ha⟩ : ∃ a, g = Polynomial.C a := ⟨g.coeff 0,
        Polynomial.eq_C_of_natDegree_eq_zero hg_const⟩
      have ha_ne : a ≠ 0 := by
        intro h; rw [h, Polynomial.C_0] at ha; exact hg_ne ha
      refine ⟨[⟨a⁻¹, r, 1⟩], ?_, ?_, ?_, ?_⟩
      · intro t ht
        simp only [List.mem_singleton] at ht
        rw [ht]
        exact hroot
      · intro t ht
        simp only [List.mem_singleton] at ht
        rw [ht]
      · intro t ht
        simp only [List.mem_singleton] at ht
        rw [ht]; exact (Polynomial.rootMultiplicity_pos hf_ne).mpr hroot
      · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, pow_one]
        rw [← hfact, ha]
        rw [RatFunc_coe_X_sub_C_mul L r (Polynomial.C a)]
        have hXCr_rf_ne : (RatFunc.X - RatFunc.C r : RatFunc L) ≠ 0 := fun h =>
          RatFunc_X_ne_C_aux L r (sub_eq_zero.mp h)
        have hCa_rf_ne : (RatFunc.C a : RatFunc L) ≠ 0 :=
          (map_ne_zero_iff RatFunc.C RatFunc.C_injective).2 ha_ne
        rw [show ((Polynomial.C a : L[X]) : RatFunc L) = RatFunc.C a from rfl]
        rw [show (RatFunc.C a⁻¹ : RatFunc L) = (RatFunc.C a)⁻¹ from by
          rw [← map_inv₀]]
        field_simp
    · -- g has degree ≥ 1; apply IH to g.
      have hg_deg_pos : 1 ≤ g.natDegree := Nat.one_le_iff_ne_zero.mpr hg_const
      have hg_lt : g.natDegree < n := by
        rw [hg_deg, ← hfn]; omega
      obtain ⟨g_terms, g_roots, g_k, g_k_bound, g_eq⟩ :=
        ih g.natDegree hg_lt g rfl hg_ne hg_splits hg_deg_pos
      -- Now get a decomposition of 1/((X - C r) * g) by using pfd_step_list.
      obtain ⟨f_terms, f_roots, f_k, f_k_bound_fn, f_eq⟩ :=
        pfd_step_list L r g_terms g_k
      refine ⟨f_terms, ?_, f_k, ?_, ?_⟩
      · intro t ht
        rcases f_roots t ht with hr_eq | ⟨t0, ht0, ht0_eq⟩
        · -- t.root = r, which is a root of f
          rw [Polynomial.IsRoot, ← hfact, hr_eq]
          simp [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
        · -- t.root = some root of g, hence root of f since g divides f
          have : g.IsRoot t0.root := g_roots t0 ht0
          rw [← hfact]
          rw [Polynomial.IsRoot, ht0_eq]
          simp only [Polynomial.eval_mul]
          rw [this]
          ring
      · -- k-bound: ∀ t ∈ f_terms, t.k ≤ rootMultiplicity t.root f
        intro t ht
        -- Use the bound function from pfd_step_list with bound = rootMultiplicity _ g
        have h_step := f_k_bound_fn (fun s => Polynomial.rootMultiplicity s g) g_k_bound t ht
        -- h_step : t.k ≤ if t.root = r then rootMultiplicity r g + 1 else rootMultiplicity t.root g
        -- We need: t.k ≤ rootMultiplicity t.root f where f = (X - C r) * g
        rw [← hfact]
        have hprod_ne : (Polynomial.X - Polynomial.C r) * g ≠ 0 :=
          mul_ne_zero hXCr_ne hg_ne
        rw [Polynomial.rootMultiplicity_mul hprod_ne, Polynomial.rootMultiplicity_X_sub_C]
        simp only at h_step
        split_ifs at h_step ⊢ with h_eq
        · -- t.root = r
          rw [h_eq]; omega
        · -- t.root ≠ r
          omega
      · -- The decomposition equality.
        rw [← f_eq, ← hfact, RatFunc_coe_X_sub_C_mul L r g,
          show ((1 : RatFunc L) / ((RatFunc.X - RatFunc.C r) * (g : RatFunc L))) =
              ((1 : RatFunc L) / (g : RatFunc L)) / (RatFunc.X - RatFunc.C r) from by
            rw [div_div, mul_comm],
          g_eq]

/-- Standard partial fraction decomposition exists:
For any polynomial Q that splits completely over L, 1/Q can be written as
a sum of terms c / (X - r)^k. -/
theorem standard_partial_fractions_exists
    (Q : Polynomial K) (hQ_ne : Q ≠ 0) (_hQ_const : Q.coeff 0 ≠ 0)
    (hQ_deg : 1 ≤ Q.natDegree)
    (L : Type*) [Field L] [Algebra K L] [IsSplittingField K L Q] :
    ∃ (terms : List (StandardPartialFraction L)),
      (∀ t ∈ terms, (Q.map (algebraMap K L)).IsRoot t.root) ∧
      (∀ t ∈ terms, t.k ≥ 1) ∧
      (∀ t ∈ terms, t.k ≤ Polynomial.rootMultiplicity t.root (Q.map (algebraMap K L))) ∧
      (1 : RatFunc L) / (Q.map (algebraMap K L) : RatFunc L) =
      (terms.map fun (t : StandardPartialFraction L) =>
        RatFunc.C t.c / (RatFunc.X - RatFunc.C t.root) ^ t.k
      ).sum := by
  set f : L[X] := Q.map (algebraMap K L) with hf_def
  have hf_ne : f ≠ 0 := Polynomial.map_ne_zero hQ_ne
  have hf_splits : f.Splits := IsSplittingField.splits L Q
  have hf_deg : 1 ≤ f.natDegree := by
    rw [hf_def, Polynomial.natDegree_map_eq_of_injective (algebraMap K L).injective]
    exact hQ_deg
  exact pfd_aux L f.natDegree f rfl hf_ne hf_splits hf_deg

/-!
#### Helper lemmas for RatFunc algebra

TODO:   What would make this easier in mathlib/tactics:
  1. Better ring tactic integration with RatFunc.C - currently ring doesn't simplify
   expressions involving the embedding
  2. Direct simp lemmas like RatFunc.neg_C_eq without needing to use map_neg
  3. A unified approach for 1/r vs r⁻¹ - these are definitionally equal but don't always unify
   in rewrites
-/

/-- C(a) * C(b) = C(a * b) -/
lemma RatFunc.C_mul_C (L : Type*) [Field L] (a b : L) :
    RatFunc.C a * RatFunc.C b = RatFunc.C (a * b) := by
  rw [← map_mul]

/-- X ≠ C(r) for any r (X has degree 1, C(r) has degree 0) -/
lemma RatFunc.X_ne_C (L : Type*) [Field L] (r : L) : (RatFunc.X : RatFunc L) ≠ RatFunc.C r :=
  RatFunc_X_ne_C_aux L r

/-- (X - C(r))^k ≠ 0 -/
lemma RatFunc.X_sub_C_pow_ne_zero (L : Type*) [Field L] (r : L) (k : ℕ) :
    (RatFunc.X - RatFunc.C r) ^ k ≠ 0 := by
  apply pow_ne_zero
  intro h
  exact RatFunc.X_ne_C L r (sub_eq_zero.mp h)

/-- (1 - C(r⁻¹) * X)^k ≠ 0 when r ≠ 0 -/
lemma RatFunc.one_sub_C_inv_mul_X_pow_ne_zero (L : Type*) [Field L] (r : L) (hr : r ≠ 0) (k : ℕ) :
    (1 - RatFunc.C r⁻¹ * RatFunc.X) ^ k ≠ 0 := by
  apply pow_ne_zero
  intro h
  have h1 : (1 : RatFunc L) = RatFunc.C r⁻¹ * RatFunc.X := sub_eq_zero.mp h
  have : RatFunc.X = RatFunc.C r := by
    calc RatFunc.X = RatFunc.C r * (RatFunc.C r⁻¹ * RatFunc.X) := by
           rw [← mul_assoc, RatFunc.C_mul_C, mul_inv_cancel₀ hr, map_one, one_mul]
      _ = RatFunc.C r * 1 := by rw [← h1]
      _ = RatFunc.C r := mul_one _
  exact RatFunc.X_ne_C L r this

/-- Key factorization: X - C(r) = -C(r) * (1 - C(r⁻¹) * X) -/
lemma RatFunc.X_sub_C_factor (L : Type*) [Field L] (r : L) (hr : r ≠ 0) :
    RatFunc.X - RatFunc.C r = -RatFunc.C r * (1 - RatFunc.C r⁻¹ * RatFunc.X) := by
  have h1 : RatFunc.C r * RatFunc.C r⁻¹ = (1 : RatFunc L) := by
    rw [RatFunc.C_mul_C, mul_inv_cancel₀ hr, map_one]
  calc RatFunc.X - RatFunc.C r
      = RatFunc.X + (-RatFunc.C r) := sub_eq_add_neg _ _
    _ = 1 * RatFunc.X + (-RatFunc.C r) * 1 := by ring
    _ = (RatFunc.C r * RatFunc.C r⁻¹) * RatFunc.X + (-RatFunc.C r) * 1 := by rw [h1]
    _ = -RatFunc.C r * (1 - RatFunc.C r⁻¹ * RatFunc.X) := by ring

/--
Conversion from standard form to generating function form:
  1 / (X - r)^k = (-1/r)^k / (1 - (1/r)X)^k
for r ≠ 0.

Proof idea: Factor (X - r) = -r * (1 - r⁻¹ * X), raise to power k, invert.
-/
theorem inv_linear_pow_eq_geom_series_term (L : Type*) [Field L]
    (r : L) (hr : r ≠ 0) (k : ℕ) :
    (1 : RatFunc L) / (RatFunc.X - RatFunc.C r) ^ k =
    RatFunc.C ((-1 / r) ^ k) / (1 - RatFunc.C (1 / r) * RatFunc.X) ^ k := by
  have hXr_ne := RatFunc.X_sub_C_pow_ne_zero L r k
  have h1r_ne : (1 - RatFunc.C (1 / r) * RatFunc.X) ^ k ≠ 0 := by
    simpa [one_div] using RatFunc.one_sub_C_inv_mul_X_pow_ne_zero L r hr k
  have factor : RatFunc.X - RatFunc.C r = -RatFunc.C r * (1 - RatFunc.C (1/r) * RatFunc.X) := by
    simpa [one_div] using RatFunc.X_sub_C_factor L r hr
  have hcoef : ((-1 / r) ^ k : L) * (-r) ^ k = 1 := by
    rw [← mul_pow]
    have h_base : (-1 / r) * (-r) = (1 : L) := by field_simp
    rw [h_base, one_pow]
  have neg_C_pow : (-RatFunc.C r) ^ k = RatFunc.C ((-r) ^ k) := by
    have h1 : -RatFunc.C r = RatFunc.C (-r) := by simp [map_neg]
    rw [h1, ← map_pow]
  have inv_neg_pow : ((-r) ^ k)⁻¹ = ((-1 / r) ^ k : L) := by
    have h1 : -1 / r = (-r)⁻¹ := by field_simp
    rw [h1, ← inv_pow]
  calc (1 : RatFunc L) / (RatFunc.X - RatFunc.C r) ^ k
      = 1 / (-RatFunc.C r * (1 - RatFunc.C (1/r) * RatFunc.X)) ^ k := by rw [factor]
    _ = 1 / ((-RatFunc.C r) ^ k * (1 - RatFunc.C (1/r) * RatFunc.X) ^ k) := by rw [mul_pow]
    _ = 1 / (-RatFunc.C r) ^ k / (1 - RatFunc.C (1/r) * RatFunc.X) ^ k := by rw [div_div]
    _ = 1 / (RatFunc.C ((-r) ^ k)) / (1 - RatFunc.C (1/r) * RatFunc.X) ^ k := by rw [neg_C_pow]
    _ = RatFunc.C (((-r) ^ k)⁻¹) / (1 - RatFunc.C (1/r) * RatFunc.X) ^ k := by
        rw [one_div, map_inv₀]
    _ = RatFunc.C ((-1 / r) ^ k) / (1 - RatFunc.C (1/r) * RatFunc.X) ^ k := by rw [inv_neg_pow]

/--
Induction principle for rational functions of the form 1 / ∏(X - rᵢ):
If a property P holds for 1 (empty product) and is preserved when multiplying
the denominator by a new linear factor (X - r), then P holds for any such product.
-/
theorem inv_prod_linear_induction (L : Type*) [Field L]
    (P : RatFunc L → Prop)
    (h_one : P 1)
    (h_step : ∀ (f : RatFunc L) (r : L), P f → P (f / (RatFunc.X - RatFunc.C r))) :
    ∀ (roots : List L),
      P ((roots.map fun r => RatFunc.X - RatFunc.C r).prod⁻¹) := by
  intro roots
  induction roots with
  | nil =>
    simp only [List.map_nil, List.prod_nil, inv_one]
    exact h_one
  | cons r tail ih =>
    simp only [List.map_cons, List.prod_cons]
    have h_linear_ne : RatFunc.X - RatFunc.C r ≠ 0 := by
      intro h
      exact RatFunc.X_ne_C L r (sub_eq_zero.mp h)
    rw [mul_inv, mul_comm, ← div_eq_mul_inv]
    exact h_step _ r ih

/-!
### 4. Main Theorem

The missing existence theorem:
Any inverse of a polynomial Q (with Q(0) ≠ 0) decomposes into a sum of
terms of the form c / (1 - αX)^k in the splitting field.
-/
/-- Helper: if Q(0) ≠ 0, then 0 is not a root of Q -/
lemma root_ne_zero_of_coeff_zero_ne_zero (Q : Polynomial K) (hQ_const : Q.coeff 0 ≠ 0)
    (L : Type*) [Field L] [Algebra K L]
    (r : L) (hr : (Q.map (algebraMap K L)).IsRoot r) :
    r ≠ 0 := by
  intro h_r_zero
  rw [h_r_zero, Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_at_zero] at hr
  rw [map_eq_zero_iff _ (algebraMap K L).injective] at hr
  exact hQ_const hr

/-- Convert a standard partial fraction term to generating function form -/
def standardToGenFunc {L : Type*} [Field L] (t : StandardPartialFraction L) (_hr : t.root ≠ 0) :
    GenFuncPartialFraction L :=
  ⟨t.c * ((-1 / t.root) ^ t.k), 1 / t.root, t.k⟩

/-- The conversion preserves the rational function value -/
lemma standardToGenFunc_eq (L : Type*) [Field L] (t : StandardPartialFraction L) (hr : t.root ≠ 0) :
    RatFunc.C t.c / (RatFunc.X - RatFunc.C t.root) ^ t.k =
    (let g := standardToGenFunc t hr
     RatFunc.C g.c / (1 - RatFunc.C g.alpha * RatFunc.X) ^ g.k) := by
  unfold standardToGenFunc
  rw [div_eq_mul_one_div, inv_linear_pow_eq_geom_series_term L t.root hr t.k, ← mul_div_assoc,
    RatFunc.C_mul_C]

theorem exists_partial_fraction_form_inv_poly
    (Q : Polynomial K) (hQ_const : Q.coeff 0 ≠ 0)
    (L : Type*) [Field L] [Algebra K L] [IsSplittingField K L Q] :
    ∃ (terms : List (GenFuncPartialFraction L)),
      (1 : RatFunc L) / (Q.map (algebraMap K L) : RatFunc L) =
      (terms.map fun (t : GenFuncPartialFraction L) =>
        (RatFunc.C t.c) / ((1 : RatFunc L) - RatFunc.C t.alpha * RatFunc.X) ^ t.k
      ).sum := by
  have hQ_ne : Q ≠ 0 := fun h => hQ_const (by simp [h])
  -- Degenerate case: Q is a nonzero constant. Then 1/Q_L is itself a constant,
  -- which we represent as a single GenFuncPartialFraction term with k = 0.
  by_cases hdeg : Q.natDegree = 0
  · -- Q = C (Q.coeff 0) since natDegree = 0
    have hQ_eq : Q = Polynomial.C (Q.coeff 0) := (Polynomial.eq_C_of_natDegree_eq_zero hdeg)
    set a : K := Q.coeff 0
    set aL : L := algebraMap K L a
    have haL_ne : aL ≠ 0 := by
      simp only [aL]
      rw [Ne, map_eq_zero_iff _ (algebraMap K L).injective]
      exact hQ_const
    refine ⟨[⟨aL⁻¹, 0, 0⟩], ?_⟩
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
               pow_zero, div_one]
    have hmap : Q.map (algebraMap K L) = Polynomial.C aL := by
      rw [hQ_eq, Polynomial.map_C]
    rw [hmap]
    -- Goal: (1 : RatFunc L) / ↑(C aL) = RatFunc.C aL⁻¹
    rw [show (Polynomial.C aL : RatFunc L) = RatFunc.C aL from rfl]
    rw [one_div, ← map_inv₀]
  -- Nonconstant case
  have hQ_deg : 1 ≤ Q.natDegree := Nat.one_le_iff_ne_zero.mpr hdeg
  obtain ⟨std_terms, h_roots, _, _, h_decomp⟩ :=
    standard_partial_fractions_exists Q hQ_ne hQ_const hQ_deg L
  have h_roots_ne : ∀ t ∈ std_terms, t.root ≠ 0 := fun t ht =>
    root_ne_zero_of_coeff_zero_ne_zero Q hQ_const L t.root (h_roots t ht)
  let toGenFunc : StandardPartialFraction L → GenFuncPartialFraction L := fun t =>
    if hr : t.root ≠ 0 then standardToGenFunc t hr
    else ⟨0, 0, 0⟩
  use std_terms.map toGenFunc
  rw [h_decomp, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t ht
  have hr : t.root ≠ 0 := h_roots_ne t ht
  simp only [toGenFunc, dif_pos hr, Function.comp_apply]
  exact standardToGenFunc_eq L t hr

/-!
## Power Series Coefficient Theory

The following sections bridge the gap between `RatFunc` (where partial fractions happen) and
`PowerSeries` (where you want the coefficients), and introduces the specific polynomials
required for the "coefficient formula."
-/

open PowerSeries BigOperators

/-!
### 5. Binomial Coefficient Polynomials
We need to treat the binomial coefficient `(n + k - 1).choose (k - 1)`
as a polynomial in `n` over the field K.
-/

/--
Constructs the polynomial P_k(X) such that P_k(n) = (n + k - 1) choose (k - 1).
This is related to the Pochhammer symbol or rising factorial.
-/
def binomialCoefPoly (k : ℕ) : Polynomial K :=
  if k = 0 then 0 else
  Polynomial.C (((k - 1).factorial : K)⁻¹) * (ascPochhammer K (k - 1)).comp (Polynomial.X + 1)

/--
Lemma stating that this polynomial actually computes the integer binomial coefficient
when evaluated at a natural number n (cast to K).
-/
theorem binomialCoefPoly_eval_eq [CharZero K] (k : ℕ) (n : ℕ) (hk : k ≥ 1) :
    (binomialCoefPoly k).eval (n : K) = (Nat.choose (n + k - 1) (k - 1) : K) := by
  have hk' : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
  simp only [binomialCoefPoly, if_neg hk']
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
             Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  have cast_eq : (n : K) + 1 = ((n + 1 : ℕ) : K) := by push_cast; ring
  rw [cast_eq]
  rw [Nat.cast_choose_eq_ascPochhammer_div, div_eq_mul_inv, mul_comm]
  congr 1
  rcases k with _ | k'
  · omega
  · simp only [Nat.add_sub_cancel]
    cases k' with
    | zero => simp [ascPochhammer_zero]
    | succ k'' =>
      simp only [Nat.succ_sub_one]
      norm_cast
      congr 1
      omega

/-- The degree of `binomialCoefPoly k` is strictly less than `k` for `k ≥ 1`. -/
theorem binomialCoefPoly_degree_lt (k : ℕ) (hk : k ≥ 1) :
    (binomialCoefPoly (K := K) k).degree < (k : WithBot ℕ) := by
  have hk' : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
  have hnd_le : (binomialCoefPoly (K := K) k).natDegree ≤ k - 1 := by
    simp only [binomialCoefPoly, if_neg hk']
    have hnd : (Polynomial.X + 1 : K[X]).natDegree = 1 :=
      Polynomial.natDegree_X_add_C (1 : K)
    calc (Polynomial.C (((k - 1).factorial : K)⁻¹) *
          (ascPochhammer K (k - 1)).comp (Polynomial.X + 1)).natDegree
        ≤ ((ascPochhammer K (k - 1)).comp (Polynomial.X + 1)).natDegree :=
          Polynomial.natDegree_C_mul_le _ _
      _ ≤ (ascPochhammer K (k - 1)).natDegree * (Polynomial.X + 1 : K[X]).natDegree :=
          Polynomial.natDegree_comp_le
      _ = k - 1 := by rw [ascPochhammer_natDegree, hnd, mul_one]
  exact lt_of_le_of_lt Polynomial.degree_le_natDegree
    (by exact_mod_cast Nat.lt_of_le_of_lt hnd_le (Nat.sub_lt (by omega) (by omega)))

/-!
### 6. Expansion of Inverse Powers (Generalized Binomial Theorem)

The coefficient of x^n in the expansion of 1 / (1 - aX)^k is (n+k-1 choose k-1) * a^n.
This uses mathlib's `PowerSeries.invOneSubPow` and `PowerSeries.rescale`.
-/

private lemma constantCoeff_rescale (a : K) (f : K⟦X⟧) :
    PowerSeries.constantCoeff (PowerSeries.rescale a f) = PowerSeries.constantCoeff f := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff (R := K),
      PowerSeries.coeff_rescale, pow_zero, one_mul,
      PowerSeries.coeff_zero_eq_constantCoeff (R := K)]

private lemma rescale_inv (a : K) (f : K⟦X⟧) (hf : PowerSeries.constantCoeff f ≠ 0) :
    PowerSeries.rescale a f⁻¹ = (PowerSeries.rescale a f)⁻¹ := by
  have hrf : PowerSeries.constantCoeff (PowerSeries.rescale a f) ≠ 0 := by
    rw [constantCoeff_rescale]; exact hf
  have h : PowerSeries.rescale a f * PowerSeries.rescale a f⁻¹ = 1 := by
    rw [← map_mul, PowerSeries.mul_inv_cancel _ hf, map_one]
  have hne : PowerSeries.rescale a f ≠ 0 := by
    intro he; exact hrf (by simp [he])
  exact mul_left_cancel₀ hne (h.trans (PowerSeries.mul_inv_cancel _ hrf).symm)

private lemma invOneSubPow_val_eq_inv (d : ℕ) :
    ↑(PowerSeries.invOneSubPow K d) = ((1 - PowerSeries.X : K⟦X⟧) ^ d)⁻¹ := by
  have h1 : (1 - PowerSeries.X : K⟦X⟧) ^ d * ↑(PowerSeries.invOneSubPow K d) = 1 := by
    rw [← PowerSeries.invOneSubPow_inv_eq_one_sub_pow]
    exact (PowerSeries.invOneSubPow K d).inv_mul
  have hconst : PowerSeries.constantCoeff ((1 - PowerSeries.X : K⟦X⟧) ^ d) ≠ 0 := by
    simp [map_pow, map_sub, PowerSeries.constantCoeff_one, PowerSeries.constantCoeff_X]
  have hne : (1 - PowerSeries.X : K⟦X⟧) ^ d ≠ 0 := by
    intro h; exact hconst (by simp [h])
  exact mul_left_cancel₀ hne (h1.trans (PowerSeries.mul_inv_cancel _ hconst).symm)

private lemma inv_pow_eq_pow_inv (k : ℕ) :
    (1 - PowerSeries.X : K⟦X⟧)⁻¹ ^ k = ((1 - PowerSeries.X : K⟦X⟧) ^ k)⁻¹ := by
  have hconst : PowerSeries.constantCoeff ((1 - PowerSeries.X : K⟦X⟧) ^ k) ≠ 0 := by
    simp [map_pow, map_sub, PowerSeries.constantCoeff_one, PowerSeries.constantCoeff_X]
  have hconst1 : PowerSeries.constantCoeff (1 - PowerSeries.X : K⟦X⟧) ≠ 0 := by
    simp [PowerSeries.constantCoeff_one, PowerSeries.constantCoeff_X]
  have hne : (1 - PowerSeries.X : K⟦X⟧) ^ k ≠ 0 := by
    intro h; exact hconst (by simp [h])
  have h1 : (1 - PowerSeries.X : K⟦X⟧) ^ k * (1 - PowerSeries.X : K⟦X⟧)⁻¹ ^ k = 1 := by
    rw [← mul_pow, PowerSeries.mul_inv_cancel _ hconst1, one_pow]
  exact mul_left_cancel₀ hne (h1.trans (PowerSeries.mul_inv_cancel _ hconst).symm)

/--
The coefficient of x^n in the expansion of 1 / (1 - aX)^k is (n+k-1 choose k-1) * a^n.
-/
theorem coeff_inv_one_sub_smul_pow (a : K) (k : ℕ) (hk : k ≥ 1) (n : ℕ) :
    (PowerSeries.coeff n) ((1 - PowerSeries.C a * PowerSeries.X)⁻¹ ^ k : K⟦X⟧) =
    (Nat.choose (n + k - 1) (k - 1) : K) * a ^ n := by
  have hconst1 : PowerSeries.constantCoeff (1 - PowerSeries.X : K⟦X⟧) ≠ 0 := by
    simp [PowerSeries.constantCoeff_one, PowerSeries.constantCoeff_X]
  have rescale_eq : PowerSeries.rescale a (1 - PowerSeries.X : K⟦X⟧) =
      1 - PowerSeries.C a * PowerSeries.X := by
    ext n; simp [PowerSeries.coeff_one, PowerSeries.coeff_X]
  have hrw : (1 - PowerSeries.C a * PowerSeries.X : K⟦X⟧)⁻¹ ^ k =
      PowerSeries.rescale a ((1 - PowerSeries.X : K⟦X⟧)⁻¹ ^ k) := by
    rw [map_pow, rescale_inv a _ hconst1, rescale_eq]
  rw [hrw, PowerSeries.coeff_rescale, mul_comm]
  congr 1
  rw [inv_pow_eq_pow_inv, ← invOneSubPow_val_eq_inv]
  rw [PowerSeries.invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos K k hk]
  simp only [PowerSeries.coeff_mk]
  have : k - 1 + n = n + k - 1 := by omega
  rw [this]

/-!
### 7. The RatFunc to PowerSeries Bridge

We need to transport the equality from RatFunc (step 1) to PowerSeries (step 3).
-/

/--
A helper definition to coerce a valid Rational Function to a Power Series.
Valid means the denominator has a non-zero constant term (is a unit in PowerSeries).
-/
def ratFuncToPowerSeries (f : RatFunc K) (_h_denom : (RatFunc.denom f).coeff 0 ≠ 0) :
    PowerSeries K :=
  (RatFunc.denom f : PowerSeries K)⁻¹ * (RatFunc.num f : PowerSeries K)

-- Helper definitions for the common denominator approach
private def denomTermPoly (t : GenFuncPartialFraction K) : K[X] :=
  (1 - Polynomial.C t.alpha * Polynomial.X) ^ t.k

private def denomProdPoly : List (GenFuncPartialFraction K) → K[X]
  | [] => 1
  | t :: rest => denomTermPoly t * denomProdPoly rest

private def numerSumPoly : List (GenFuncPartialFraction K) → K[X]
  | [] => 0
  | t :: rest => Polynomial.C t.c * denomProdPoly rest + numerSumPoly rest * denomTermPoly t

private lemma denomTermPoly_ps_constantCoeff (t : GenFuncPartialFraction K) :
    PowerSeries.constantCoeff (↑(denomTermPoly t) : PowerSeries K) ≠ 0 := by
  have : (↑(denomTermPoly t) : PowerSeries K) =
      (1 - PowerSeries.C t.alpha * PowerSeries.X) ^ t.k := by
    rw [denomTermPoly]; push_cast; rfl
  simp only [this, map_pow, map_sub, PowerSeries.constantCoeff_one, map_mul,
    PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X, mul_zero, sub_zero,
    one_pow, ne_eq]; exact one_ne_zero

private lemma denomProdPoly_ps_constantCoeff :
    ∀ (l : List (GenFuncPartialFraction K)),
      PowerSeries.constantCoeff (↑(denomProdPoly l) : PowerSeries K) ≠ 0
  | [] => by simp [denomProdPoly, Polynomial.coe_one, PowerSeries.constantCoeff_one]
  | t :: rest => by
    simp only [denomProdPoly, Polynomial.coe_mul, map_mul]
    exact mul_ne_zero (denomTermPoly_ps_constantCoeff t) (denomProdPoly_ps_constantCoeff rest)

private lemma denomTermPoly_ne_zero (t : GenFuncPartialFraction K) : denomTermPoly t ≠ 0 :=
  fun h => denomTermPoly_ps_constantCoeff t (by rw [h]; simp [Polynomial.coe_zero])

private lemma denomProdPoly_ne_zero' (l : List (GenFuncPartialFraction K)) :
    denomProdPoly l ≠ 0 :=
  fun h => denomProdPoly_ps_constantCoeff l (by rw [h]; simp [Polynomial.coe_zero])

private lemma denomTermPoly_rf_ne (t : GenFuncPartialFraction K) :
    (algebraMap K[X] (RatFunc K)) (denomTermPoly t) ≠ 0 :=
  (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (denomTermPoly_ne_zero t)

private lemma denomProdPoly_rf_ne (l : List (GenFuncPartialFraction K)) :
    (algebraMap K[X] (RatFunc K)) (denomProdPoly l) ≠ 0 :=
  (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr (denomProdPoly_ne_zero' l)

private lemma rfSum_eq_frac : ∀ (terms : List (GenFuncPartialFraction K)),
    (terms.map fun t => RatFunc.C t.c /
      ((1 : RatFunc K) - RatFunc.C t.alpha * RatFunc.X) ^ t.k).sum =
    (algebraMap K[X] (RatFunc K)) (numerSumPoly terms) /
    (algebraMap K[X] (RatFunc K)) (denomProdPoly terms)
  | [] => by simp [numerSumPoly, denomProdPoly]
  | t :: rest => by
    simp only [List.map_cons, List.sum_cons]
    rw [show RatFunc.C t.c / ((1 : RatFunc K) - RatFunc.C t.alpha * RatFunc.X) ^ t.k =
      (algebraMap K[X] (RatFunc K)) (Polynomial.C t.c) /
      (algebraMap K[X] (RatFunc K)) (denomTermPoly t) from by
      rw [denomTermPoly, map_pow, map_sub, map_one, map_mul, RatFunc.algebraMap_C,
        RatFunc.algebraMap_X, RatFunc.algebraMap_C]]
    rw [rfSum_eq_frac rest,
      div_add_div _ _ (denomTermPoly_rf_ne t) (denomProdPoly_rf_ne rest),
      ← map_mul, ← map_mul, ← map_add]
    congr 1
    · simp [numerSumPoly, mul_comm]
    · simp [denomProdPoly]

private lemma ps_inv_pow_eq_pow_inv (f : PowerSeries K)
    (hf : PowerSeries.constantCoeff f ≠ 0) (k : ℕ) : f⁻¹ ^ k = (f ^ k)⁻¹ := by
  have hfk : PowerSeries.constantCoeff (f ^ k) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hf
  have hfne : f ^ k ≠ 0 := fun h => hfk (by simp [h])
  exact mul_left_cancel₀ hfne
    ((by rw [← mul_pow, PowerSeries.mul_inv_cancel _ hf, one_pow] :
        f ^ k * f⁻¹ ^ k = 1).trans (PowerSeries.mul_inv_cancel _ hfk).symm)

private lemma ps_denomProdPoly_mul_sum_eq_numerSumPoly :
    ∀ (terms : List (GenFuncPartialFraction K)),
    (↑(denomProdPoly terms) : PowerSeries K) *
      (terms.map fun t =>
        PowerSeries.C t.c *
          (1 - PowerSeries.C t.alpha * PowerSeries.X)⁻¹ ^ t.k).sum =
    (↑(numerSumPoly terms) : PowerSeries K)
  | [] => by simp [denomProdPoly, numerSumPoly, Polynomial.coe_one, Polynomial.coe_zero]
  | t :: rest => by
    simp only [List.map_cons, List.sum_cons, denomProdPoly, numerSumPoly]
    rw [Polynomial.coe_mul, mul_add]
    have hdtp_cc : PowerSeries.constantCoeff
        (1 - PowerSeries.C t.alpha * PowerSeries.X : PowerSeries K) ≠ 0 := by
      simp [PowerSeries.constantCoeff_one, PowerSeries.constantCoeff_X,
        PowerSeries.constantCoeff_C]
    have hdtp_eq : (↑(denomTermPoly t) : PowerSeries K) =
        (1 - PowerSeries.C t.alpha * PowerSeries.X) ^ t.k := by
      rw [denomTermPoly]; push_cast; rfl
    conv_lhs =>
      arg 1
      rw [show (↑(denomTermPoly t) : PowerSeries K) * ↑(denomProdPoly rest) *
          (PowerSeries.C t.c *
            (1 - PowerSeries.C t.alpha * PowerSeries.X)⁻¹ ^ t.k) =
        (↑(denomProdPoly rest) : PowerSeries K) * PowerSeries.C t.c *
          ((↑(denomTermPoly t) : PowerSeries K) *
            (↑(denomTermPoly t))⁻¹) from by
        rw [hdtp_eq, ps_inv_pow_eq_pow_inv _ hdtp_cc, ← hdtp_eq]; ring]
    rw [PowerSeries.mul_inv_cancel _ (denomTermPoly_ps_constantCoeff t), mul_one]
    conv_lhs =>
      arg 2
      rw [show (↑(denomTermPoly t) : PowerSeries K) * ↑(denomProdPoly rest) *
          (rest.map fun s => PowerSeries.C s.c *
            (1 - PowerSeries.C s.alpha * PowerSeries.X)⁻¹ ^ s.k).sum =
        (↑(denomTermPoly t) : PowerSeries K) *
          ((↑(denomProdPoly rest) : PowerSeries K) *
            (rest.map fun s => PowerSeries.C s.c *
              (1 - PowerSeries.C s.alpha * PowerSeries.X)⁻¹ ^ s.k).sum) from by ring]
    rw [ps_denomProdPoly_mul_sum_eq_numerSumPoly rest,
      Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_mul, Polynomial.coe_C]
    ring

/--
The Commutation Lemma:
If a RatFunc decomposition holds, the PowerSeries decomposition holds.
This allows us to sum the series of the parts to get the series of the whole.
-/
theorem ratFunc_decomposition_implies_series_sum
    (terms : List (GenFuncPartialFraction K))
    (Q : Polynomial K) (hQ : Q.coeff 0 ≠ 0) :
    (1 : RatFunc K) / (Q : RatFunc K) =
      (terms.map fun (t : GenFuncPartialFraction K) =>
        RatFunc.C t.c / ((1 : RatFunc K) - RatFunc.C t.alpha * RatFunc.X) ^ t.k).sum
    →
    (Q : PowerSeries K)⁻¹ =
      (terms.map fun (t : GenFuncPartialFraction K) =>
        PowerSeries.C t.c * ((1 - PowerSeries.C t.alpha * PowerSeries.X)⁻¹ ^ t.k)
      ).sum := by
  intro h
  set sum_ps := (terms.map fun t =>
    PowerSeries.C t.c *
      ((1 - PowerSeries.C t.alpha * PowerSeries.X)⁻¹ ^ t.k)).sum
  -- Extract polynomial identity from RatFunc hypothesis
  have hQ_ne : Q ≠ 0 := fun hh => hQ (by rw [hh]; simp)
  have hQrf : (algebraMap K[X] (RatFunc K)) Q ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).mpr hQ_ne
  rw [rfSum_eq_frac, RatFunc.coePolynomial_eq_algebraMap] at h
  have h' : (algebraMap K[X] (RatFunc K)) 1 / (algebraMap K[X] (RatFunc K)) Q =
    (algebraMap K[X] (RatFunc K)) (numerSumPoly terms) /
    (algebraMap K[X] (RatFunc K)) (denomProdPoly terms) := by rwa [map_one]
  rw [div_eq_div_iff hQrf (denomProdPoly_rf_ne terms)] at h'
  have h_poly := RatFunc.algebraMap_injective K
    (by rw [map_mul, map_mul]; exact h' :
      (algebraMap K[X] (RatFunc K)) (1 * denomProdPoly terms) =
      (algebraMap K[X] (RatFunc K)) (numerSumPoly terms * Q))
  simp only [one_mul] at h_poly
  -- h_poly : denomProdPoly terms = numerSumPoly terms * Q
  -- Map polynomial identity to PowerSeries
  have h_ps : (↑(denomProdPoly terms) : PowerSeries K) =
    (↑(numerSumPoly terms) : PowerSeries K) * (↑Q : PowerSeries K) := by
    exact_mod_cast h_poly
  -- Use inductive lemma: denomProdPoly * sum_ps = numerSumPoly
  have h_ps_sum := ps_denomProdPoly_mul_sum_eq_numerSumPoly terms
  -- Derive Q * sum_ps = 1 by cancelling denomProdPoly
  have hdPP_cc := denomProdPoly_ps_constantCoeff terms
  have hdPP_ne : (↑(denomProdPoly terms) : PowerSeries K) ≠ 0 :=
    fun hh => hdPP_cc (by rw [hh]; simp)
  have h_Q_sum : (↑Q : PowerSeries K) * sum_ps = 1 := by
    have key : (↑(denomProdPoly terms) : PowerSeries K) *
        ((↑Q : PowerSeries K) * sum_ps) =
        (↑(denomProdPoly terms) : PowerSeries K) * 1 := by
      rw [mul_one]; calc
        (↑(denomProdPoly terms) : PowerSeries K) *
            ((↑Q : PowerSeries K) * sum_ps)
          = (↑Q : PowerSeries K) *
            ((↑(denomProdPoly terms) : PowerSeries K) * sum_ps) := by ring
        _ = (↑Q : PowerSeries K) *
            ↑(numerSumPoly terms) := by rw [h_ps_sum]
        _ = ↑(numerSumPoly terms) * ↑Q := by ring
        _ = ↑(denomProdPoly terms) := h_ps.symm
    exact mul_left_cancel₀ hdPP_ne key
  -- Conclude: sum_ps = Q⁻¹
  have hQps_cc : PowerSeries.constantCoeff (↑Q : PowerSeries K) ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, Polynomial.coeff_coe]; exact hQ
  have hQps_ne : (↑Q : PowerSeries K) ≠ 0 := fun hh => hQps_cc (by rw [hh]; simp)
  exact (mul_left_cancel₀ hQps_ne
    (h_Q_sum.trans (PowerSeries.mul_inv_cancel _ hQps_cc).symm)).symm

/-!
### 8. The Main Coefficient Formula
-/

/-- Grouping a list sum by key into a finset sum of filtered sublists. -/
private lemma list_sum_eq_finset_sum_grouped {α β γ : Type*} [DecidableEq β] [AddCommMonoid γ]
    (l : List α) (g : α → β) (f : α → γ) (S : Finset β) (hS : ∀ a ∈ l, g a ∈ S) :
    (l.map f).sum = ∑ b ∈ S, ((l.filter (fun a => g a = b)).map f).sum := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    have hS_tl : ∀ a ∈ tl, g a ∈ S := fun a ha => hS a (List.mem_cons.mpr (Or.inr ha))
    have hhd : g hd ∈ S := hS hd (List.mem_cons.mpr (Or.inl rfl))
    simp only [List.map_cons, List.sum_cons, ih hS_tl]
    simp_rw [List.filter_cons]
    simp only [apply_ite (List.map f), apply_ite List.sum, List.map_cons, List.sum_cons]
    have key : ∀ x ∈ S, (if decide (g hd = x) = true then f hd +
        (List.map f (List.filter (fun a => decide (g a = x)) tl)).sum else
        (List.map f (List.filter (fun a => decide (g a = x)) tl)).sum) =
        (if x = g hd then f hd else 0) +
        (List.map f (List.filter (fun a => decide (g a = x)) tl)).sum := by
      intro x _; simp only [decide_eq_true_eq]
      split_ifs with h1 h2 h2
      · simp
      · exact absurd h1.symm h2
      · exact absurd h2.symm h1
      · simp
    rw [Finset.sum_congr rfl key, Finset.sum_add_distrib]
    congr 1
    exact ((Finset.sum_ite_eq' S (g hd) (fun _ => f hd)).trans (if_pos hhd)).symm

universe u in
theorem inverse_series_coefficient_repeated_roots
    {K : Type u} [Field K] [CharZero K]
    (Q : Polynomial K)
    (h_const : Q.coeff 0 ≠ 0)
    (h_deg : 1 ≤ Q.natDegree) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L),
    let Q_L := Q.map (algebraMap K L)
    let roots := Q_L.roots
    let unique_roots := roots.toFinset
    ∃ (poly_map : L → Polynomial L),
    (∀ r ∈ unique_roots, (poly_map r).degree < roots.count r)
    ∧
    ∀ (n : ℕ),
      (PowerSeries.coeff n) ((Polynomial.map (algebraMap K L) Q : PowerSeries L)⁻¹) =
      ∑ r ∈ unique_roots,
        ((poly_map r).eval (n : L)) * (1 / r) ^ n :=
by
  -- Step 1: Provide the splitting field
  refine ⟨Q.SplittingField, inferInstance, inferInstance, ?_⟩
  set L := Q.SplittingField
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  -- Step 2: Get standard PFD with explicit root info
  have hQ_ne : Q ≠ 0 := fun h => h_const (by simp [h])
  set Q_L := Q.map (algebraMap K L) with hQ_L_def
  have hQL_const : Q_L.coeff 0 ≠ 0 := by
    rw [hQ_L_def, Polynomial.coeff_map]
    exact (map_ne_zero_iff _ (algebraMap K L).injective).mpr h_const
  obtain ⟨std_terms, h_roots, h_k_ge, h_k_bound, h_std_rf⟩ :=
    standard_partial_fractions_exists Q hQ_ne h_const h_deg L
  -- Each root ≠ 0 (since Q(0) ≠ 0)
  have h_roots_ne : ∀ t ∈ std_terms, t.root ≠ 0 := fun t ht =>
    root_ne_zero_of_coeff_zero_ne_zero Q h_const L t.root (h_roots t ht)
  -- Convert to GenFunc form and bridge to PowerSeries
  let gfTerms : List (GenFuncPartialFraction L) := std_terms.map fun t =>
    if hr : t.root ≠ 0 then standardToGenFunc t hr else ⟨0, 0, 0⟩
  have h_gf_rf : (1 : RatFunc L) / (Q_L : RatFunc L) =
      (gfTerms.map fun t =>
        RatFunc.C t.c / ((1 : RatFunc L) - RatFunc.C t.alpha * RatFunc.X) ^ t.k).sum := by
    rw [h_std_rf, List.map_map]
    congr 1; apply List.map_congr_left; intro t ht
    have hr := h_roots_ne t ht
    simp only [gfTerms, Function.comp_apply, dif_pos hr]
    exact standardToGenFunc_eq L t hr
  have h_ps := ratFunc_decomposition_implies_series_sum gfTerms Q_L hQL_const h_gf_rf
  -- Step 3: Define poly_map using standard terms (which have explicit .root)
  let poly_map : L → Polynomial L := fun r =>
    ((std_terms.filter (fun t => t.root = r)).map
      (fun t => Polynomial.C (t.c * (-1 / t.root) ^ t.k) * binomialCoefPoly t.k)).sum
  refine ⟨poly_map, ?_, ?_⟩
  · -- Degree bound
    intro r hr
    -- poly_map r is a sum of C(a) * binomialCoefPoly t.k for filtered terms
    -- Each such polynomial has degree < t.k ≤ rootMultiplicity r Q_L = count r roots
    rw [Polynomial.count_roots]
    have hQL_ne : Q_L ≠ 0 := Polynomial.map_ne_zero hQ_ne
    set m := Polynomial.rootMultiplicity r Q_L with hm_def
    -- m > 0 since r is a root
    have hm_pos : 0 < m := by
      rw [hm_def]; exact (Polynomial.rootMultiplicity_pos hQL_ne).mpr
        ((Polynomial.mem_roots hQL_ne).mp (Multiset.mem_toFinset.mp hr))
    -- Each term in the mapped list has degree ≤ m - 1 < m
    have h_each : ∀ p ∈ ((std_terms.filter (fun t => decide (t.root = r))).map
        (fun t => Polynomial.C (t.c * (-1 / t.root) ^ t.k) * binomialCoefPoly t.k)),
        p.degree ≤ ((m - 1 : ℕ) : WithBot ℕ) := by
      intro p hp
      rw [List.mem_map] at hp
      obtain ⟨t, ht_mem, htp⟩ := hp
      rw [← htp]
      rw [List.mem_filter] at ht_mem
      obtain ⟨ht_std, ht_root⟩ := ht_mem
      simp only [decide_eq_true_eq] at ht_root
      have htk_le : t.k ≤ m := by rw [hm_def, ← ht_root]; exact h_k_bound t ht_std
      have htk_ge : t.k ≥ 1 := h_k_ge t ht_std
      calc (Polynomial.C (t.c * (-1 / t.root) ^ t.k) * binomialCoefPoly t.k).degree
          ≤ (binomialCoefPoly (K := L) t.k).degree := by
            rw [Polynomial.C_mul']; exact Polynomial.degree_smul_le _ _
        _ ≤ (binomialCoefPoly (K := L) t.k).natDegree := Polynomial.degree_le_natDegree
        _ ≤ ((t.k - 1 : ℕ) : WithBot ℕ) := by
            apply WithBot.coe_le_coe.mpr
            simp only [binomialCoefPoly, if_neg (Nat.one_le_iff_ne_zero.mp htk_ge)]
            have hnd : (Polynomial.X + 1 : L[X]).natDegree = 1 :=
              Polynomial.natDegree_X_add_C (1 : L)
            calc (Polynomial.C (((t.k - 1).factorial : L)⁻¹) *
                  (ascPochhammer L (t.k - 1)).comp (Polynomial.X + 1)).natDegree
                ≤ ((ascPochhammer L (t.k - 1)).comp (Polynomial.X + 1)).natDegree :=
                  Polynomial.natDegree_C_mul_le _ _
              _ ≤ (ascPochhammer L (t.k - 1)).natDegree *
                  (Polynomial.X + 1 : L[X]).natDegree := Polynomial.natDegree_comp_le
              _ = t.k - 1 := by rw [ascPochhammer_natDegree, hnd, mul_one]
        _ ≤ ((m - 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.sub_le_sub_right htk_le 1
    calc (poly_map r).degree
        ≤ ((m - 1 : ℕ) : WithBot ℕ) :=
          Polynomial.degree_list_sum_le_of_forall_degree_le _ _ h_each
      _ < (m : WithBot ℕ) := by exact_mod_cast Nat.sub_lt hm_pos Nat.one_pos
  · -- Coefficient formula
    intro n
    rw [h_ps]
    -- LHS: coeff n of the list sum over gfTerms
    rw [map_list_sum (PowerSeries.coeff n)]
    simp only [List.map_map, Function.comp_def]
    -- Each gfTerm's coeff: use coeff_C_mul and coeff_inv_one_sub_smul_pow
    -- gfTerms = std_terms.map (standardToGenFunc or default)
    -- For each std_term t with root r ≠ 0:
    --   gfTerm = ⟨t.c * (-1/r)^k, 1/r, k⟩
    --   coeff n (C(t.c*(-1/r)^k) * (1 - C(1/r)*X)⁻¹^k)
    --   = t.c * (-1/r)^k * C(n+k-1,k-1) * (1/r)^n
    -- Group by root → Σ_r (Σ_{t:root=r} ...) * (1/r)^n
    -- Step 1: Unfold gfTerms and simplify LHS to a sum over std_terms
    simp only [gfTerms, List.map_map, Function.comp_def]
    have hlhs_congr : ∀ t ∈ std_terms,
        (PowerSeries.coeff n)
          (PowerSeries.C (if hr : t.root ≠ 0 then (standardToGenFunc t hr) else ⟨0, 0, 0⟩).c *
            (1 - PowerSeries.C (if hr : t.root ≠ 0 then (standardToGenFunc t hr) else ⟨0, 0, 0⟩).alpha *
              PowerSeries.X)⁻¹ ^
            (if hr : t.root ≠ 0 then (standardToGenFunc t hr) else ⟨0, 0, 0⟩).k) =
        t.c * (-1 / t.root) ^ t.k * ((Nat.choose (n + t.k - 1) (t.k - 1) : ℕ) : L) *
          (1 / t.root) ^ n := by
      intro t ht
      simp only [dif_pos (h_roots_ne t ht), standardToGenFunc]
      rw [PowerSeries.coeff_C_mul, coeff_inv_one_sub_smul_pow _ _ (h_k_ge t ht)]
      ring
    rw [List.map_congr_left hlhs_congr]
    -- Step 2: Simplify RHS — eval poly_map and use binomialCoefPoly_eval_eq
    -- For each filtered term t with t.root = r, replace (1/r) by (1/t.root)
    have hrhs_congr : ∀ r ∈ Q_L.roots.toFinset,
        Polynomial.eval (↑n) (poly_map r) * (1 / r) ^ n =
        ((std_terms.filter (fun t => t.root = r)).map
          (fun t => t.c * (-1 / t.root) ^ t.k *
            ((Nat.choose (n + t.k - 1) (t.k - 1) : ℕ) : L) *
            (1 / t.root) ^ n)).sum := by
      intro r _hr
      simp only [poly_map, Polynomial.eval_listSum, List.map_map, Function.comp_def]
      rw [← List.sum_map_mul_right]
      congr 1
      apply List.map_congr_left
      intro t ht
      have ht_root : t.root = r := by
        have := (List.mem_filter.mp ht).2
        simpa using this
      simp only [Polynomial.eval_mul, Polynomial.eval_C]
      have htk : t.k ≥ 1 := h_k_ge t (List.mem_of_mem_filter ht)
      rw [binomialCoefPoly_eval_eq _ _ htk, ht_root]
    rw [Finset.sum_congr rfl hrhs_congr]
    -- Step 3: Both sides now have the same per-element function
    -- LHS: (std_terms.map f).sum
    -- RHS: ∑ r ∈ S, (std_terms.filter(root=r).map f).sum
    -- Use the grouping lemma
    have hQ_L_ne : Q_L ≠ 0 := by
      intro h; exact hQL_const (by rw [h]; simp)
    have h_roots_in_finset : ∀ t ∈ std_terms, t.root ∈ Q_L.roots.toFinset := by
      intro t ht
      rw [Multiset.mem_toFinset]
      exact (Polynomial.mem_roots hQ_L_ne).mpr (h_roots t ht)
    exact list_sum_eq_finset_sum_grouped std_terms
      (fun t => t.root)
      (fun t => t.c * (-1 / t.root) ^ t.k *
        ((Nat.choose (n + t.k - 1) (t.k - 1) : ℕ) : L) * (1 / t.root) ^ n)
      Q_L.roots.toFinset h_roots_in_finset

/-!
### 9. Applications and Examples
-/

/-- The coefficient of x^n in 1/(1-2x) is 2^n. -/
example (n : ℕ) :
    (PowerSeries.coeff n) ((1 - (PowerSeries.C (2 : ℚ)) * PowerSeries.X)⁻¹) = 2 ^ n := by
  have h := coeff_inv_one_sub_smul_pow (2 : ℚ) 1 (by omega) n
  simp at h
  exact h

/-- The Fibonacci Power Series: ∑ F_n * X^n -/
def fibSeries : PowerSeries ℚ := PowerSeries.mk (fun n => (Nat.fib n : ℚ))

/-- The Polynomial: 1 - X - X^2 -/
def fibDenom : PowerSeries ℚ := 1 - PowerSeries.X - PowerSeries.X ^ 2

private lemma fibDenom_mul_fibSeries : fibDenom * fibSeries = PowerSeries.X := by
  have hrw : fibDenom * fibSeries = fibSeries - PowerSeries.X * fibSeries -
      PowerSeries.X ^ 2 * fibSeries := by
    simp only [fibDenom]; ring
  rw [hrw]
  ext n
  match n with
  | 0 =>
    simp [fibSeries, PowerSeries.coeff_X, Nat.fib_zero, PowerSeries.constantCoeff_X, sq]
  | 1 =>
    simp only [map_sub, PowerSeries.coeff_X]
    rw [show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul]
    rw [show PowerSeries.X ^ 2 * fibSeries = PowerSeries.X * (PowerSeries.X * fibSeries) from by
      ring]
    rw [PowerSeries.coeff_succ_X_mul]
    simp [fibSeries, PowerSeries.coeff_mk, Nat.fib_zero, Nat.fib_one,
      PowerSeries.constantCoeff_X]
  | n + 2 =>
    simp only [map_sub, PowerSeries.coeff_X, show n + 2 ≠ 1 from by omega, if_false]
    rw [show n + 2 = (n + 1) + 1 from by ring]
    rw [PowerSeries.coeff_succ_X_mul]
    rw [show PowerSeries.X ^ 2 * fibSeries = PowerSeries.X * (PowerSeries.X * fibSeries) from by
      ring]
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul]
    simp only [fibSeries, PowerSeries.coeff_mk]
    rw [show Nat.fib (n + 1 + 1) = Nat.fib (n + 2) from rfl]
    rw [Nat.fib_add_two]; push_cast; ring

theorem fib_generating_function : fibSeries = PowerSeries.X * fibDenom⁻¹ := by
  have hconst : PowerSeries.constantCoeff fibDenom ≠ 0 := by
    simp [fibDenom, PowerSeries.constantCoeff_one, PowerSeries.constantCoeff_X, map_sub, map_pow]
  calc fibSeries = 1 * fibSeries := (one_mul _).symm
    _ = (fibDenom⁻¹ * fibDenom) * fibSeries := by
        rw [PowerSeries.inv_mul_cancel _ hconst]
    _ = fibDenom⁻¹ * (fibDenom * fibSeries) := by ring
    _ = fibDenom⁻¹ * PowerSeries.X := by rw [fibDenom_mul_fibSeries]
    _ = PowerSeries.X * fibDenom⁻¹ := by ring
