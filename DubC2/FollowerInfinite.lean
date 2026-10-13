/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.Follower

/-!
# An infinite follower automaton is never certified

`DubC2.Gen.Follower.T5iv` decides certification when the follower automaton `F` is finite.  This
file removes the finiteness hypothesis from the certification side: **a checked certificate, at
any cell count `D`, forces `F` to be finite** (`finite_of_checked`).  So for every cell

> some `D` certifies  ⟺  `F` is finite and no reachable state branches

(`checked_iff_finite`), and `D_F` certifies whenever some `D` does.

The proof has three steps.

* **Admissible words of a certified cell are eventually periodic**
  (`eventuallyPeriodic_of_checked`).  A word all of whose prefixes keep the root alive is, prefix
  by prefix, the label of a finite path of the cell graph at any `D` (backward realization
  `Branch.realize` and the residue walk); König's lemma on the finite graph
  (`Branch.exists_path_of_forall`) gives an infinite path, and a checked certificate makes its
  labels eventually periodic.
* **An infinite `F` has an infinite path of pairwise distinct states** (`exists_geodesic`): the
  states at every distance from the root exist, each distance level is finite, and a pigeonhole
  over the letters keeps a geodesic extendable at every step.
* **Along an eventually periodic word the states take finitely many values**
  (`finite_range_of_periodic`).  The residue set lies in a finite set, and over one period the
  endpoints follow `x ↦ max c (λx + β)` and `x ↦ min d (λx + β')` with `λ = (p/q)^per > 1`.  A
  bounded orbit of such a clipped expanding map repeats a value (`exists_rep_of_clip`), hence has
  finitely many values.

The growth side does not extend: an infinite `F` may still have polynomially many admissible
words (a zero-entropy aperiodic cell); such a cell is never certified.

## Main results

* `DubC2.Gen.Follower.eventuallyPeriodic_of_checked` — admissible words of a certified cell are
  eventually periodic;
* `DubC2.Gen.Follower.finite_of_checked` — a certified cell has a finite follower automaton;
* `DubC2.Gen.Follower.checked_iff_finite` — some `D` certifies ⟺ `D_F` certifies ⟺ `F` is finite
  and no reachable state branches.

## References

* [Oda26] Y. Odagiri, *Finite graph certificates for composite terms in rational floor sequences*,
  Zenodo, doi:10.5281/zenodo.22997709 (2026).
-/

namespace DubC2.Gen

namespace Follower

open Filter ForMathlib.SubwordComplexity Horse Branch

variable {P : Params}

/-! ## Words along a sequence -/

/-- The word of the first `n` letters of a sequence. -/
def pre (s : ℕ → ℤ) (n : ℕ) : List ℤ := (List.range n).map s

theorem pre_succ (s : ℕ → ℤ) (n : ℕ) : pre s (n + 1) = pre s n ++ [s n] := by
  simp [pre, List.range_succ]

theorem pre_length (s : ℕ → ℤ) (n : ℕ) : (pre s n).length = n := by simp [pre]

theorem pre_getD (s : ℕ → ℤ) {n i : ℕ} (h : i < n) : (pre s n).getD i 0 = s i := by
  rw [List.getD_eq_getElem _ _ (by rw [pre_length]; exact h)]
  simp [pre]

theorem rpath_pre (s : ℕ → ℤ) (r : ℕ) : ∀ n {r' : ℕ}, rpath P r (pre s n) = some r' →
    r' = rs P r s n ∧ ∀ i < n, rOK P (rs P r s i) (s i) = true
  | 0, r', h => by
    simp only [pre, List.range_zero, List.map_nil, rpath, Option.some.injEq] at h
    exact ⟨h.symm, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | n + 1, r', h => by
    rw [pre_succ, rpath_append] at h
    obtain ⟨r'', h1, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨e, hok⟩ := rpath_pre s r n h1
    simp only [rpath] at h2
    split_ifs at h2 with hr
    simp only [Option.some.injEq] at h2
    subst e
    refine ⟨by rw [← h2]; rfl, fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact hok i hi
    · exact hr

theorem step_R_nonempty {X Y : FState} {s : ℤ} (h : step P X s = some Y) : Y.R.Nonempty := by
  unfold step at h
  split_ifs at h with hc
  cases h
  exact hc.2.1

theorem stepw_pre_succ {X : FState} (s : ℕ → ℤ) (n : ℕ) :
    stepw P X (pre s (n + 1)) = (stepw P X (pre s n)).bind fun Y => step P Y (s n) := by
  rw [pre_succ, stepw_append]
  congr 1
  funext Y
  simp only [stepw]
  cases step P Y (s n) <;> rfl

/-! ## Admissible words of a certified cell are eventually periodic -/

/-- **Every admissible infinite word of a certified cell is eventually periodic**, at any `D`:
if every prefix of `s` keeps the root of `F` alive and a certificate is checked, then `s` is
eventually periodic. -/
@[category research solved, AMS 11 37, ref "Oda26", group "dubc2_obstruction"]
theorem eventuallyPeriodic_of_checked {C : Cert} (hc : Checked P C) (s : ℕ → ℤ)
    (hs : ∀ m, (stepw P (root P) (pre s m)).isSome) : IsEventuallyPeriodic s := by
  classical
  have hF : ParamFacts P := by
    have hh := hc.head
    simp only [checkHead, Bool.and_eq_true] at hh
    exact paramFacts hh.1.1.1.1.1
  have hp0 : (0 : ℚ) < P.p := by exact_mod_cast (by have := hF.pq; omega : 0 < P.p)
  have hq0 : (0 : ℚ) < P.q := by exact_mod_cast (by have := hF.q1; omega : 0 < P.q)
  have hb0 : (0 : ℚ) < P.b := by exact_mod_cast hF.b0
  -- finite paths of every length
  have hfin : ∀ m, ∃ v : ℕ → ℕ, (∀ i ≤ m, v i < P.nV) ∧ ∀ i < m,
      PseudoOrbit.ptix P s i < P.nA ∧ P.letter (PseudoOrbit.ptix P s i) = s i ∧
        v (i + 1) ∈ P.succList (v i) (P.letter (PseudoOrbit.ptix P s i)) := by
    intro m
    obtain ⟨X, hX⟩ := Option.isSome_iff_exists.1 (hs (m + 1))
    -- the interval
    have hI := stepw_interval (P := P) (pre s (m + 1)) hX
    have hb := stepw_bounds (P := P) (pre s (m + 1)) (by simp [pre]) hX
    obtain ⟨ys, -, -, -, hys, hrec⟩ := realize (a := P.a) (b := P.b) hp0 hq0 (pre s (m + 1))
      ((root P).lo, (root P).hi) le_rfl le_rfl X.lo (by rw [hI]) (by rw [hI]; exact hb.2.1)
    rw [pre_length] at hys hrec
    -- a residue
    have hne : X.R.Nonempty := by
      rw [stepw_pre_succ, Option.bind_eq_some_iff] at hX
      obtain ⟨Z, -, hZ⟩ := hX
      exact step_R_nonempty hZ
    obtain ⟨r', hr'⟩ := hne
    obtain ⟨r₀, hr₀, hpath⟩ := stepw_pre (P := P) (pre s (m + 1)) hX hr'
    have hr₀M : r₀ < P.M := by simpa [root] using hr₀
    obtain ⟨-, hok⟩ := rpath_pre s r₀ (m + 1) hpath
    set r := rs P r₀ s with hr
    have hrlt : ∀ n, r n < P.M := by
      intro n; cases n with
      | zero => exact hr₀M
      | succ n => exact rnext_lt hF _ _
    have hav : ∀ i < m + 1, (∀ l ∈ P.PM, r i % l ≠ 0) ∧ (∀ l ∈ P.PM, r (i + 1) % l ≠ 0) := by
      intro i hi
      have := hok i hi
      simp only [rOK, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at this
      exact ⟨this.1, this.2⟩
    have hsav : ∀ i < m + 1, ∀ l ∈ P.Pq, s i % (l : ℤ) ≠ 0 := by
      intro i hi l hl
      have := stepw_sOK (P := P) (pre s (m + 1)) hX (s i) (by simp only [pre, List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩)
      simp only [sOK, List.all_eq_true, bne_iff_ne, ne_eq] at this
      exact this l hl
    set y : ℕ → ℝ := fun i => (ys i : ℝ)
    have hst : ∀ i < m + 1, PseudoOrbit.pvtx P r y i < P.nV ∧ PseudoOrbit.ptix P s i < P.nA ∧
        P.letter (PseudoOrbit.ptix P s i) = s i ∧
          PseudoOrbit.pvtx P r y (i + 1) ∈ P.succList (PseudoOrbit.pvtx P r y i)
            (P.letter (PseudoOrbit.ptix P s i)) := by
      intro i hi
      obtain ⟨a0, a1⟩ := hys i hi.le
      obtain ⟨b0, b1⟩ := hys (i + 1) hi
      have e := hrec i hi
      rw [pre_getD s hi] at e
      refine PseudoOrbit.step_of hF i (hrlt i) (show (0 : ℝ) ≤ (ys i : ℝ) by exact_mod_cast a0)
        (show (ys i : ℝ) < 1 by exact_mod_cast a1)
        (show (0 : ℝ) ≤ (ys (i + 1) : ℝ) by exact_mod_cast b0)
        (show (ys (i + 1) : ℝ) < 1 by exact_mod_cast b1) ?_ rfl (hav i hi).1 (hav i hi).2
        (hsav i hi)
      have e' : ((ys (i + 1) : ℚ) : ℝ) = ((fw P.p P.q P.a P.b (s i) (ys i) : ℚ) : ℝ) := by rw [e]
      simp only [fw] at e'
      push_cast at e'
      simp only [y]
      have hq' : (P.q : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
      have hb' : (P.b : ℝ) ≠ 0 := by exact_mod_cast hb0.ne'
      rw [e']
      field_simp
      ring
    exact ⟨PseudoOrbit.pvtx P r y, fun i hi => (hst i (by omega)).1,
      fun i hi => (hst i (by omega)).2⟩
  have hlet : ∀ n, PseudoOrbit.ptix P s n < P.nA ∧ P.letter (PseudoOrbit.ptix P s n) = s n := by
    intro n
    obtain ⟨v, -, hv⟩ := hfin (n + 1)
    exact ⟨(hv n (by omega)).1, (hv n (by omega)).2.1⟩
  obtain ⟨v, hv⟩ := exists_path_of_forall (N := P.nV)
    (E := fun n x x' => x' ∈ P.succList x (P.letter (PseudoOrbit.ptix P s n)))
    (fun m => by
      obtain ⟨v, h1, h2⟩ := hfin m
      exact ⟨v, h1, fun i hi => (h2 i hi).2.2⟩)
  have hp : IsPath P 0 v (PseudoOrbit.ptix P s) :=
    ⟨fun n _ => (hv n).1, fun n _ => (hlet n).1, fun n _ => (hv n).2⟩
  obtain ⟨M₀, per, hper, hp'⟩ := isEventuallyPeriodic_of_path hc hp
  refine ⟨M₀, per, hper, fun k hk => ?_⟩
  rw [← (hlet k).2, ← (hlet (k + per)).2, hp' k hk]

/-! ## Clipped expanding maps -/

/-- A deterministic orbit that repeats a value has finitely many values. -/
theorem finite_range_of_rep {α : Type*} {g : α → α} {x : ℕ → α} (hx : ∀ j, x (j + 1) = g (x j))
    {i i' : ℕ} (hii : i < i') (he : x i = x i') : (Set.range x).Finite := by
  have hk : ∀ k, x (i + k) = x (i' + k) := by
    intro k
    induction k with
    | zero => simpa using he
    | succ k ih => rw [← add_assoc, ← add_assoc, hx, hx, ih]
  have hall : ∀ n, x n ∈ x '' Set.Iio i' := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      by_cases hn : n < i'
      · exact ⟨n, hn, rfl⟩
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hn)
        rw [← hk k]
        exact ih (i + k) (by omega)
  exact ((Set.finite_Iio i').image x).subset (by rintro _ ⟨n, rfl⟩; exact hall n)

/-- **A bounded orbit of a clipped expanding affine map repeats a value.**  Two clips give the
clip value twice; without a second clip the orbit is eventually affine and expanding, so bounded
only at the fixed point. -/
theorem exists_rep_of_clip {c l β B : ℚ} (hl : 1 < l) {x : ℕ → ℚ}
    (hx : ∀ j, x (j + 1) = max c (l * x j + β)) (hB : ∀ j, |x j| ≤ B) :
    ∃ i i', i < i' ∧ x i = x i' := by
  by_cases h2 : ∃ j₀ j₁, j₀ < j₁ ∧ l * x j₀ + β ≤ c ∧ l * x j₁ + β ≤ c
  · obtain ⟨j₀, j₁, hj, h0, h1⟩ := h2
    exact ⟨j₀ + 1, j₁ + 1, by omega, by rw [hx, hx, max_eq_left h0, max_eq_left h1]⟩
  · push Not at h2
    obtain ⟨i₀, hi₀⟩ : ∃ i₀, ∀ j, i₀ ≤ j → c < l * x j + β := by
      by_cases h1 : ∃ j₀, l * x j₀ + β ≤ c
      · obtain ⟨j₀, h0⟩ := h1
        exact ⟨j₀ + 1, fun j hj => h2 j₀ j (by omega) h0⟩
      · push Not at h1
        exact ⟨0, fun j _ => h1 j⟩
    set xs := β / (1 - l) with hxs
    have hfix : l * xs + β = xs := by
      have : (1 - l) ≠ 0 := by linarith
      rw [hxs]
      field_simp
      ring
    have hlin : ∀ k, x (i₀ + k) - xs = l ^ k * (x i₀ - xs) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [← add_assoc, hx, max_eq_right (hi₀ _ (by omega)).le, pow_succ]
        linear_combination l * ih + hfix
    have hx0 : x i₀ = xs := by
      by_contra hne
      have hd : 0 < |x i₀ - xs| := abs_pos.2 (sub_ne_zero.2 hne)
      obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((B + |xs|) / |x i₀ - xs|) hl
      have h1 : |x (i₀ + k) - xs| ≤ B + |xs| :=
        (abs_sub _ _).trans (by linarith [hB (i₀ + k)])
      rw [hlin, abs_mul, abs_of_pos (pow_pos (by linarith) k)] at h1
      rw [div_lt_iff₀ hd] at hk
      linarith
    refine ⟨i₀, i₀ + 1, by omega, ?_⟩
    rw [hx, max_eq_right (hi₀ i₀ le_rfl).le, hx0, hfix]

/-- The `min` form of `exists_rep_of_clip`. -/
theorem exists_rep_of_clip' {d l β B : ℚ} (hl : 1 < l) {x : ℕ → ℚ}
    (hx : ∀ j, x (j + 1) = min d (l * x j + β)) (hB : ∀ j, |x j| ≤ B) :
    ∃ i i', i < i' ∧ x i = x i' := by
  obtain ⟨i, i', hii, he⟩ := exists_rep_of_clip (c := -d) (β := -β) (B := B) hl (x := fun j => -x j)
    (fun j => by
      simp only [hx]
      rw [show l * -x j + -β = -(l * x j + β) by ring, max_neg_neg])
    (fun j => by simpa using hB j)
  exact ⟨i, i', hii, neg_injective he⟩

/-! ## The endpoints over a word -/

variable (P) in
/-- The lower endpoint after a word. -/
def gfold (u : List ℤ) (x : ℚ) : ℚ := u.foldl (fun y s => max 0 (fw P.p P.q P.a P.b s y)) x

variable (P) in
/-- The upper endpoint after a word. -/
def hfold (u : List ℤ) (x : ℚ) : ℚ := u.foldl (fun y s => min 1 (fw P.p P.q P.a P.b s y)) x

theorem ifold_eq (u : List ℤ) (I : ℚ × ℚ) :
    ifold P.p P.q P.a P.b u I = (gfold P u I.1, hfold P u I.2) := by
  induction u generalizing I with
  | nil => rfl
  | cons s u ih =>
    simp only [ifold, List.foldl_cons] at ih ⊢
    rw [ih]
    rfl

theorem fw_eq (hF : ParamFacts P) (s : ℤ) (y : ℚ) :
    fw P.p P.q P.a P.b s y = (P.p : ℚ) / P.q * y + (-(s : ℚ) - ((P.p : ℚ) - P.q) * P.a / P.b) / P.q := by
  have hq : (P.q : ℚ) ≠ 0 := by have := hF.q1; positivity
  simp only [fw]
  field_simp
  ring

/-- Over a word, the lower endpoint follows `x ↦ max c (λx + β)` with `λ = (p/q)^|u|`. -/
theorem gfold_affine (hF : ParamFacts P) : ∀ u : List ℤ, ∃ c β : ℚ, ∀ x, 0 ≤ x →
    gfold P u x = max c (((P.p : ℚ) / P.q) ^ u.length * x + β)
  | [] => ⟨0, 0, fun x hx => by simp [gfold, max_eq_right hx]⟩
  | s :: u => by
    obtain ⟨c, β, h⟩ := gfold_affine hF u
    set l := ((P.p : ℚ) / P.q) ^ u.length
    set κ := (-(s : ℚ) - ((P.p : ℚ) - P.q) * P.a / P.b) / P.q
    refine ⟨max c β, l * κ + β, fun x hx => ?_⟩
    show gfold P u (max 0 (fw P.p P.q P.a P.b s x)) = _
    have hl : 0 ≤ l := by have := hF.q1; positivity
    rw [h _ (le_max_left _ _), mul_max_of_nonneg _ _ hl, ← max_add_add_right, mul_zero, zero_add,
      ← max_assoc, fw_eq hF, List.length_cons, pow_succ]
    congr 1
    ring

/-- Over a word, the upper endpoint follows `x ↦ min d (λx + β)` with `λ = (p/q)^|u|`. -/
theorem hfold_affine (hF : ParamFacts P) : ∀ u : List ℤ, ∃ d β : ℚ, ∀ x, x ≤ 1 →
    hfold P u x = min d (((P.p : ℚ) / P.q) ^ u.length * x + β)
  | [] => ⟨1, 0, fun x hx => by simp [hfold, min_eq_right hx]⟩
  | s :: u => by
    obtain ⟨d, β, h⟩ := hfold_affine hF u
    set l := ((P.p : ℚ) / P.q) ^ u.length
    set κ := (-(s : ℚ) - ((P.p : ℚ) - P.q) * P.a / P.b) / P.q
    refine ⟨min d (l + β), l * κ + β, fun x hx => ?_⟩
    show hfold P u (min 1 (fw P.p P.q P.a P.b s x)) = _
    have hl : 0 ≤ l := by have := hF.q1; positivity
    rw [h _ (min_le_left _ _), mul_min_of_nonneg _ _ hl, ← min_add_add_right, mul_one,
      ← min_assoc, fw_eq hF, List.length_cons, pow_succ]
    congr 1
    ring

/-! ## Along an eventually periodic word the states repeat -/

/-- **Along an eventually periodic word, a path of `F` from the root repeats a state.** -/
theorem not_injective_of_periodic (hF : ParamFacts P) {s : ℕ → ℤ} {X : ℕ → FState}
    (h0 : X 0 = root P) (hX : ∀ n, step P (X n) (s n) = some (X (n + 1)))
    (hs : IsEventuallyPeriodic s) : ¬ Function.Injective X := by
  intro hinj
  obtain ⟨N, per, hper, hps⟩ := hs
  -- bounds and residues along the path
  have hbd : ∀ n, 0 ≤ (X n).lo ∧ (X n).lo ≤ (X n).hi ∧ (X n).hi ≤ 1 := by
    intro n
    cases n with
    | zero => rw [h0]; simp [root]
    | succ n =>
      obtain ⟨-, -, -, h1, h2, h3⟩ := step_facts (hX n)
      exact ⟨h1, h2.le, h3⟩
  have hR : ∀ n, (X n).R ⊆ Finset.range P.M := by
    intro n
    cases n with
    | zero => rw [h0]; exact subset_rfl
    | succ n =>
      rw [(step_facts (hX n)).2.1]
      intro r hr
      simp only [rstep, Finset.mem_image] at hr
      obtain ⟨r₀, -, rfl⟩ := hr
      exact Finset.mem_range.2 (rnext_lt hF _ _)
  -- one period
  have hseg : ∀ a k, stepw P (X a) ((List.range k).map fun i => s (a + i)) = some (X (a + k)) := by
    intro a k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.range_succ, List.map_append, stepw_append, ih]
      simp [stepw, hX (a + k), ← add_assoc]
  have hsp : ∀ j i, s (N + j * per + i) = s (N + i) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro i
      rw [show N + (j + 1) * per + i = N + j * per + i + per by ring, hps _ (by omega), ih]
  set u := (List.range per).map fun i => s (N + i) with hu
  set Y : ℕ → FState := fun j => X (N + j * per) with hYdef
  have hY : ∀ j, stepw P (Y j) u = some (Y (j + 1)) := by
    intro j
    have := hseg (N + j * per) per
    rw [show N + j * per + per = N + (j + 1) * per by ring] at this
    rw [← this]
    simp only [hYdef, hu]
    congr 2
    funext i
    exact (hsp j i).symm
  have hlen : u.length = per := by simp [hu]
  have hl : 1 < ((P.p : ℚ) / P.q) ^ u.length := by
    have hq : (0 : ℚ) < P.q := by exact_mod_cast (by have := hF.q1; omega : 0 < P.q)
    have : (1 : ℚ) < P.p / P.q := by
      rw [one_lt_div hq]; exact_mod_cast hF.pq
    exact one_lt_pow₀ this (by omega)
  -- the endpoints
  have hint : ∀ j, (Y (j + 1)).lo = gfold P u (Y j).lo ∧ (Y (j + 1)).hi = hfold P u (Y j).hi := by
    intro j
    have := stepw_interval (P := P) u (hY j)
    rw [ifold_eq] at this
    simp only [Prod.mk.injEq] at this
    exact ⟨this.1.symm, this.2.symm⟩
  obtain ⟨c, β, hc⟩ := gfold_affine hF u
  obtain ⟨d, β', hd⟩ := hfold_affine hF u
  have hlo : (Set.range fun j => (Y j).lo).Finite := by
    have hx : ∀ j, (Y (j + 1)).lo = max c (((P.p : ℚ) / P.q) ^ u.length * (Y j).lo + β) :=
      fun j => by rw [(hint j).1, hc _ (hbd _).1]
    obtain ⟨i, i', hii, he⟩ := exists_rep_of_clip (B := 1) (x := fun j => (Y j).lo) hl hx
      (fun j => abs_le.2 ⟨by linarith [(hbd (N + j * per)).1],
        by linarith [(hbd (N + j * per)).2.1, (hbd (N + j * per)).2.2]⟩)
    exact finite_range_of_rep (x := fun j => (Y j).lo)
      (g := fun x => max c (((P.p : ℚ) / P.q) ^ u.length * x + β)) hx hii he
  have hhi : (Set.range fun j => (Y j).hi).Finite := by
    have hx : ∀ j, (Y (j + 1)).hi = min d (((P.p : ℚ) / P.q) ^ u.length * (Y j).hi + β') :=
      fun j => by rw [(hint j).2, hd _ (hbd _).2.2]
    obtain ⟨i, i', hii, he⟩ := exists_rep_of_clip' (B := 1) (x := fun j => (Y j).hi) hl hx
      (fun j => abs_le.2 ⟨by linarith [(hbd (N + j * per)).1, (hbd (N + j * per)).2.1],
        by linarith [(hbd (N + j * per)).2.2]⟩)
    exact finite_range_of_rep (x := fun j => (Y j).hi)
      (g := fun x => min d (((P.p : ℚ) / P.q) ^ u.length * x + β')) hx hii he
  have hRf : {R : Finset ℕ | R ⊆ Finset.range P.M}.Finite :=
    ((Finset.range P.M).powerset.finite_toSet).subset fun R hR =>
      Finset.mem_coe.2 (Finset.mem_powerset.2 hR)
  have hfin : (Set.range Y).Finite :=
    ((hRf.prod (hlo.prod hhi)).image fun t => (⟨t.1, t.2.1, t.2.2⟩ : FState)).subset (by
      rintro _ ⟨j, rfl⟩
      exact ⟨((Y j).R, (Y j).lo, (Y j).hi), ⟨hR _, ⟨j, rfl⟩, ⟨j, rfl⟩⟩, rfl⟩)
  have hYinj : Function.Injective Y := fun j j' h => by
    have := hinj h
    have : j * per = j' * per := by omega
    exact Nat.eq_of_mul_eq_mul_right hper this
  exact Set.infinite_range_of_injective hYinj hfin

/-! ## An infinite follower automaton has an injective path -/

variable (P) in
/-- The states reached from the root by words of length exactly `n`. -/
def Lev (n : ℕ) : Set FState := {Y | ∃ u : List ℤ, u.length = n ∧ stepw P (root P) u = some Y}

variable (P) in
/-- The distance of a state from the root. -/
noncomputable def dist (Y : FState) : ℕ := sInf {n | Y ∈ Lev P n}

theorem reach_of_stepw : ∀ (u : List ℤ) {X Y : FState}, stepw P X u = some Y → Reach P X Y
  | [], X, Y, h => by simp only [stepw, Option.some.injEq] at h; subst h; exact .refl
  | s :: u, X, Y, h => by
    simp only [stepw, Option.bind_eq_some_iff] at h
    obtain ⟨Z, hZ, hu⟩ := h
    exact Relation.ReflTransGen.head ⟨s, hZ⟩ (reach_of_stepw u hu)

theorem Lev_finite (hF : ParamFacts P) (n : ℕ) : (Lev P n).Finite := by
  classical
  refine ((words P n (root P)).finite_toSet.image
    fun u => (stepw P (root P) u).getD (root P)).subset ?_
  rintro Y ⟨u, hu, hY⟩
  exact ⟨u, (mem_words hF n (root P) u valid_root).2 ⟨hu, by rw [hY]; rfl⟩, by simp [hY]⟩

theorem dist_le {Y : FState} {n : ℕ} (h : Y ∈ Lev P n) : dist P Y ≤ n := Nat.sInf_le h

theorem mem_Lev_dist {Y : FState} {n : ℕ} (h : Y ∈ Lev P n) : Y ∈ Lev P (dist P Y) :=
  Nat.sInf_mem (s := {n | Y ∈ Lev P n}) ⟨n, h⟩

theorem mem_Lev_dist_of_reach {Y : FState} (h : Reach P (root P) Y) : Y ∈ Lev P (dist P Y) := by
  obtain ⟨u, hu⟩ := stepw_of_reach h
  exact mem_Lev_dist ⟨u, rfl, hu⟩

theorem dist_root : dist P (root P) = 0 := Nat.le_zero.1 (dist_le ⟨[], rfl, rfl⟩)

theorem dist_stepw_le {X Z : FState} (hX : X ∈ Lev P (dist P X)) {u : List ℤ}
    (h : stepw P X u = some Z) : dist P Z ≤ dist P X + u.length := by
  obtain ⟨w, hw, hwX⟩ := hX
  refine dist_le ⟨w ++ u, by simp [hw], ?_⟩
  rw [stepw_append, hwX]
  exact h

/-- **A prefix of a geodesic is a geodesic.** -/
theorem geodesic_prefix {X Z : FState} (hX : X ∈ Lev P (dist P X)) {u v : List ℤ}
    (h : stepw P X (u ++ v) = some Z) (hd : dist P Z = dist P X + u.length + v.length) :
    ∃ W, stepw P X u = some W ∧ stepw P W v = some Z ∧ W ∈ Lev P (dist P W) ∧
      dist P W = dist P X + u.length := by
  rw [stepw_append, Option.bind_eq_some_iff] at h
  obtain ⟨W, hW, hWZ⟩ := h
  have hWl : W ∈ Lev P (dist P W) := by
    obtain ⟨w, hw, hwX⟩ := hX
    exact mem_Lev_dist ⟨w ++ u, rfl, by rw [stepw_append, hwX]; exact hW⟩
  have h1 := dist_stepw_le hX hW
  have h2 := dist_stepw_le hWl hWZ
  exact ⟨W, hW, hWZ, hWl, by omega⟩

variable (P) in
/-- From `X` a geodesic of length `m` leaves. -/
def Geo (X : FState) (m : ℕ) : Prop :=
  ∃ u Z, u.length = m ∧ stepw P X u = some Z ∧ dist P Z = dist P X + m

theorem geo_mono {X : FState} (hX : X ∈ Lev P (dist P X)) {m m' : ℕ} (hm : m' ≤ m)
    (h : Geo P X m) : Geo P X m' := by
  obtain ⟨u, Z, hu, hZ, hd⟩ := h
  rw [← List.take_append_drop m' u] at hZ
  obtain ⟨W, hW, -, -, hdW⟩ := geodesic_prefix hX hZ (by
    rw [hd, List.length_take, List.length_drop, hu]; omega)
  exact ⟨u.take m', W, by simp [hu, hm], hW, by rw [hdW]; simp [hu, hm]⟩

/-- **König's lemma for `F`**: an infinite follower automaton has an infinite path from the root
whose states are pairwise distinct (each at its own distance from the root). -/
theorem exists_injective_path (hF : ParamFacts P) (hinf : ¬ {X | Reach P (root P) X}.Finite) :
    ∃ (s : ℕ → ℤ) (X : ℕ → FState), X 0 = root P ∧
      (∀ n, step P (X n) (s n) = some (X (n + 1))) ∧ Function.Injective X := by
  classical
  -- invariant: reachable, at distance `n`, geodesics of every length leave
  let G : ℕ → FState → Prop := fun n X =>
    Reach P (root P) X ∧ X ∈ Lev P (dist P X) ∧ dist P X = n ∧ ∀ m, Geo P X m
  have hroot : G 0 (root P) := by
    refine ⟨.refl, ⟨[], rfl, rfl⟩ |> mem_Lev_dist, dist_root, fun m => ?_⟩
    -- a reachable state at distance `≥ m`
    obtain ⟨Z, hZr, hZm⟩ : ∃ Z, Reach P (root P) Z ∧ m ≤ dist P Z := by
      by_contra hc
      push Not at hc
      apply hinf
      refine ((Set.finite_Iio m).biUnion fun k _ => Lev_finite hF k).subset fun Z hZ => ?_
      exact Set.mem_biUnion (Set.mem_Iio.2 (hc Z hZ)) (mem_Lev_dist_of_reach hZ)
    obtain ⟨w, hw, hwZ⟩ := mem_Lev_dist_of_reach hZr
    rw [← List.take_append_drop m w] at hwZ
    obtain ⟨W, hW, -, -, hdW⟩ := geodesic_prefix (u := w.take m) (v := w.drop m)
      (⟨[], rfl, rfl⟩ |> mem_Lev_dist) hwZ (by rw [dist_root]; simp [hw]; omega)
    exact ⟨w.take m, W, by simp [hw, hZm], hW, by rw [hdW]; simp [hw, hZm]⟩
  have hnext : ∀ n X, G n X → ∃ s Y, step P X s = some Y ∧ G (n + 1) Y := by
    intro n X ⟨hXr, hXl, hXd, hXg⟩
    obtain ⟨t, -, ht⟩ := exists_forall_of_antitone (N := P.nA)
      (Q := fun t m => ∃ Y, step P X (P.letter t) = some Y ∧ Y ∈ Lev P (dist P Y) ∧
        dist P Y = dist P X + 1 ∧ Geo P Y m)
      (fun t m m' hm ⟨Y, h1, h2, h3, h4⟩ => ⟨Y, h1, h2, h3, geo_mono h2 hm h4⟩)
      (fun m => by
        obtain ⟨u, Z, hu, hZ, hd⟩ := hXg (m + 1)
        obtain ⟨s, u', rfl⟩ : ∃ s u', u = s :: u' := by
          cases u with
          | nil => simp at hu
          | cons s u' => exact ⟨s, u', rfl⟩
        obtain ⟨Y, hY, hYZ, hYl, hYd⟩ := geodesic_prefix (u := [s]) (v := u') hXl hZ
          (by simp at hu; simp [hd, hu]; omega)
        have hs1 : stepw P X [s] = some Y := hY
        have hstep : step P X s = some Y := by
          simp only [stepw, Option.bind_eq_some_iff] at hs1
          obtain ⟨Y', h1, h2⟩ := hs1
          simp only [Option.some.injEq] at h2
          rw [h1, h2]
        have hsa := letter_mem hF (valid_of_reach hXr) hstep
        simp only [alph, Finset.mem_image, Finset.mem_range] at hsa
        obtain ⟨t, ht, rfl⟩ := hsa
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hu
        exact ⟨t, ht, Y, hstep, hYl, by simpa using hYd,
          ⟨u', Z, hu, hYZ, by rw [hd, hYd]; simp; omega⟩⟩)
    obtain ⟨Y, hY, hYl, hYd, -⟩ := ht 0
    refine ⟨P.letter t, Y, hY, hXr.tail ⟨_, hY⟩, hYl, by omega, fun m => ?_⟩
    obtain ⟨Y', hY', -, -, hg⟩ := ht m
    rw [hY] at hY'
    cases hY'
    exact hg
  have hnext' : ∀ n X, ∃ p : ℤ × FState, G n X → step P X p.1 = some p.2 ∧ G (n + 1) p.2 := by
    intro n X
    by_cases hX : G n X
    · obtain ⟨s, Y, h1, h2⟩ := hnext n X hX
      exact ⟨(s, Y), fun _ => ⟨h1, h2⟩⟩
    · exact ⟨(0, X), fun h => absurd h hX⟩
  choose f hf using hnext'
  let X : ℕ → FState := fun n => Nat.rec (root P) (fun k Xk => (f k Xk).2) n
  have hG : ∀ n, G n (X n) := by
    intro n
    induction n with
    | zero => exact hroot
    | succ k ih => exact (hf k (X k) ih).2
  refine ⟨fun n => (f n (X n)).1, X, rfl, fun n => (hf n (X n) (hG n)).1, fun i j h => ?_⟩
  have hi := (hG i).2.2.1
  have hj := (hG j).2.2.1
  rw [h] at hi
  omega

/-! ## Certification forces a finite follower automaton -/

/-- **A certified cell has a finite follower automaton**, at any cell count `D`. -/
@[category research solved, AMS 11 37, ref "Oda26", group "dubc2_obstruction"]
theorem finite_of_checked {C : Cert} (hc : Checked P C) : {X | Reach P (root P) X}.Finite := by
  have hF : ParamFacts P := by
    have hh := hc.head
    simp only [checkHead, Bool.and_eq_true] at hh
    exact paramFacts hh.1.1.1.1.1
  by_contra hinf
  obtain ⟨s, X, h0, hX, hinj⟩ := exists_injective_path hF hinf
  have hs : ∀ m, stepw P (root P) (pre s m) = some (X m) := by
    intro m
    induction m with
    | zero => rw [h0]; rfl
    | succ m ih => rw [stepw_pre_succ, ih]; exact hX m
  exact not_injective_of_periodic hF h0 hX
    (eventuallyPeriodic_of_checked hc s fun m => by rw [hs]; rfl) hinj

/-- **T5(iv) for every cell.**  Some cell count `D` certifies iff the follower automaton is finite
and has no reachable branching state; then the common denominator `D_F` of its endpoints
certifies. -/
@[category research solved, AMS 11 37, ref "Oda26", group "dubc2_obstruction"]
theorem checked_iff_finite (hP : checkParams P = true) :
    (∃ D C, Checked { P with D := D } C) ↔
      ∃ hfin : {X | Reach P (root P) X}.Finite, (∀ X, Reach P (root P) X → ¬ Branching P X) ∧
        ∃ C, Checked { P with D := DF hfin } C := by
  constructor
  · rintro ⟨D, C, hc⟩
    have hfin : {X | Reach P (root P) X}.Finite := finite_of_checked (P := { P with D := D }) hc
    have hnb : ∀ X, Reach P (root P) X → ¬ Branching P X := fun X _ hX =>
      not_checked_of_branching (P := { P with D := D }) hX hc
    exact ⟨hfin, hnb, exists_checked_DF hP hfin hnb⟩
  · rintro ⟨hfin, -, C, hc⟩
    exact ⟨_, C, hc⟩

end Follower

end DubC2.Gen
