/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Data.Set.Countable
import EVG25.Question17
import EVG25.M0.Prefix

/-!
# Why counting stops at the horizon

Propositions 4 and 5 of plan EVGQ17-M0.  Write `X(n₀)` for `CC.U_orbit_density n₀`: the letters `1`
of the `U`-word of `n₀` have density `1/2`.

* `U_orbit_density_U_iff`, `U_orbit_density_U_iter_iff` — **Prop. 5(i)**: `X(n₀) ↔ X(U n₀)`;
* `U_orbit_density_add_mul_two_pow_iff` — **Prop. 5(ii)**:
  `X(n₀ + t·2^m) ↔ X(U^m(n₀) + t·3^m)`;
* `exists_U_orbit_density_of_ne_univ`, `exists_U_orbit_density_of_hasNatDensity_zero` —
  **Prop. 5(iii)**: if the failure set of `X` is not all of `ℕ` — in particular, if it has
  density `0` — then some seed satisfies `X`.  A density-`0` theorem for the failure set would
  therefore prove an open individual-orbit statement;
* `tailSaturated_not_wordDensityHalf` and `exists_tailSaturated_countable_superset` —
  **Prop. 4 (no-go)**: the set of words without letter density `1/2` is tail-saturated, and every
  set of seeds `S ⊆ ℕ` is contained in the preimage of a *countable* tail-saturated set of words
  (countable, hence null for the Bernoulli measure, which has no atoms).  So tail-saturation and
  measure zero — the two facts residue counting delivers about the failure set — are consistent
  with the failure set being all of `ℕ`.

Two words are *tail-equivalent* (`TailEq`) when they agree after shifting each by its own amount,
eventually; a set is *tail-saturated* when it is a union of tail classes.  This covers closure
under the shift, under its preimages and under changing finitely many letters at once.
-/

open Filter Topology Finset CC CC.Base3div2

namespace EVG25.M0

/-! ## Letter density of a word -/

/-- The number of letters `true` among the first `k` letters of `w`. -/
def cnt (w : ℕ → Bool) (k : ℕ) : ℕ := ((range k).filter fun i => w i = true).card

/-- The letters `1` of `w` have density `1/2`. -/
def WordDensityHalf (w : ℕ → Bool) : Prop :=
  Tendsto (fun k => (cnt w k : ℚ) / k) atTop (𝓝 (1 / 2 : ℚ))

theorem cnt_succ (w : ℕ → Bool) (k : ℕ) : cnt w (k + 1) = cnt w k + if w k then 1 else 0 := by
  unfold cnt
  rw [range_add_one, filter_insert]
  split
  · rw [card_insert_of_notMem (by simp)]
  · simp_all

theorem cnt_add (w : ℕ → Bool) (a k : ℕ) :
    cnt w (a + k) = cnt w a + cnt (fun i => w (i + a)) k := by
  induction k with
  | zero => simp [cnt]
  | succ k ih => rw [← add_assoc, cnt_succ, ih, cnt_succ, add_comm k a]; ring

/-- Letter density is invariant under the shift by `a`. -/
theorem wordDensityHalf_shift_iff (w : ℕ → Bool) (a : ℕ) :
    WordDensityHalf (fun i => w (i + a)) ↔ WordDensityHalf w := by
  unfold WordDensityHalf
  rw [← tendsto_add_atTop_iff_nat a (f := fun k => (cnt w k : ℚ) / k)]
  have h : (fun k => (cnt w (k + a) : ℚ) / ((k + a : ℕ) : ℚ))
      = fun k => ((cnt w a + cnt (fun i => w (i + a)) k : ℕ) : ℚ) / ((a + k : ℕ) : ℚ) := by
    funext k; rw [add_comm k a, cnt_add]
  simp only [Nat.cast_add] at h ⊢
  rw [h]
  have := tendsto_shift_ratio_iff (a := cnt fun i => w (i + a)) (c := cnt w a) (d := a)
    (L := 1 / 2)
  push_cast at this
  exact this.symm

/-! ## Tail equivalence -/

/-- `w` and `c` agree eventually, after shifting `w` by `a` and `c` by `b`. -/
def TailEq (w c : ℕ → Bool) : Prop := ∃ a b N : ℕ, ∀ i ≥ N, w (i + a) = c (i + b)

theorem TailEq.symm {w c : ℕ → Bool} (h : TailEq w c) : TailEq c w := by
  obtain ⟨a, b, N, h⟩ := h
  exact ⟨b, a, N, fun i hi => (h i hi).symm⟩

/-- A set of words is tail-saturated if it is a union of tail-equivalence classes. -/
def TailSaturated (E : Set (ℕ → Bool)) : Prop := ∀ w c, TailEq w c → c ∈ E → w ∈ E

theorem TailSaturated.shift {E : Set (ℕ → Bool)} (hE : TailSaturated E) {w : ℕ → Bool}
    (hw : w ∈ E) : (fun i => w (i + 1)) ∈ E :=
  hE _ w ⟨0, 1, 0, fun _ _ => rfl⟩ hw

theorem TailSaturated.of_shift {E : Set (ℕ → Bool)} (hE : TailSaturated E) {w : ℕ → Bool}
    (hw : (fun i => w (i + 1)) ∈ E) : w ∈ E :=
  hE w _ ⟨1, 0, 0, fun _ _ => rfl⟩ hw

theorem TailSaturated.of_finite_diff {E : Set (ℕ → Bool)} (hE : TailSaturated E)
    {w w' : ℕ → Bool} (hfin : {i | w i ≠ w' i}.Finite) (hw : w ∈ E) : w' ∈ E := by
  obtain ⟨N, hN⟩ := hfin.bddAbove
  refine hE w' w ⟨0, 0, N + 1, fun i hi => ?_⟩ hw
  by_contra h
  have := hN (show i + 0 ∈ {i | w i ≠ w' i} from Ne.symm h)
  omega

/-- Letter density `1/2` is a tail property. -/
theorem wordDensityHalf_of_tailEq {w c : ℕ → Bool} (h : TailEq w c) (hc : WordDensityHalf c) :
    WordDensityHalf w := by
  obtain ⟨a, b, N, h⟩ := h
  have heq : (fun i => w (i + (a + N))) = fun i => c (i + (b + N)) := by
    funext i; have := h (i + N) (by omega); rwa [show i + N + a = i + (a + N) by ring,
      show i + N + b = i + (b + N) by ring] at this
  rw [← wordDensityHalf_shift_iff w (a + N), heq, wordDensityHalf_shift_iff]
  exact hc

/-- **The failure set is tail-saturated.** -/
theorem tailSaturated_not_wordDensityHalf : TailSaturated {w | ¬ WordDensityHalf w} :=
  fun _ _ h hc hw => hc (wordDensityHalf_of_tailEq h.symm hw)

/-- The tail saturation of a countable set of words is countable. -/
theorem countable_tailSaturation {C : Set (ℕ → Bool)} (hC : C.Countable) :
    {w | ∃ c ∈ C, TailEq w c}.Countable := by
  have : {w | ∃ c ∈ C, TailEq w c}
      = ⋃ c ∈ C, ⋃ a : ℕ, ⋃ b : ℕ, ⋃ N : ℕ, {w | ∀ i ≥ N, w (i + a) = c (i + b)} := by
    ext w; simp [TailEq]
  rw [this]
  refine hC.biUnion fun c _ => Set.countable_iUnion fun a => Set.countable_iUnion fun b =>
    Set.countable_iUnion fun N => ?_
  -- a word in this set is determined by its first `N + a` letters
  refine Set.MapsTo.countable_of_injOn (f := fun w (j : Fin (N + a)) => w j)
    (Set.mapsTo_univ _ _) ?_ Set.countable_univ
  intro w hw w' hw' hww
  funext j
  by_cases hj : j < N + a
  · exact congr_fun hww ⟨j, hj⟩
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + a := ⟨j - a, by omega⟩
    rw [hw i (by omega), hw' i (by omega)]

theorem tailSaturated_tailSaturation (C : Set (ℕ → Bool)) :
    TailSaturated {w | ∃ c ∈ C, TailEq w c} := by
  rintro w c ⟨a, b, N, h⟩ ⟨c', hc', a', b', N', h'⟩
  -- compose: `w (i + a) = c (i + b)` and `c (i + a') = c' (i + b')`
  refine ⟨c', hc', a + a', b + b', N + N' + b + a', fun i hi => ?_⟩
  have h1 := h (i + a') (by omega)
  have h2 := h' (i + b) (by omega)
  rw [show i + (a + a') = i + a' + a by ring, h1, show i + a' + b = i + b + a' by ring, h2,
    show i + b + b' = i + (b + b') by ring]

/-! ## `U`-words -/

/-- The `U`-word of `n`. -/
def uWord (n : ℕ) : ℕ → Bool := uLetter n

theorem U_iter_add (i m n : ℕ) : U_iter i (U_iter m n) = U_iter (i + m) n := by
  induction i with
  | zero => simp
  | succ i ih => rw [U_iter_succ, ih, show i + 1 + m = (i + m) + 1 by ring, U_iter_succ]

theorem uWord_U_iter (m n : ℕ) : uWord (U_iter m n) = fun i => uWord n (i + m) := by
  funext i; simp [uWord, uLetter, U_iter_add]

theorem numOddU_eq_cnt (k n : ℕ) : numOddU k n = cnt (uWord n) k := by
  simp [numOddU, cnt, uWord, uLetter]

theorem U_orbit_density_iff_wordDensityHalf (n : ℕ) :
    U_orbit_density n ↔ WordDensityHalf (uWord n) := by
  simp only [U_orbit_density, WordDensityHalf, numOddU_eq_cnt]

/-! ## Proposition 5 -/

theorem U_orbit_density_U_iter_iff (m n : ℕ) :
    U_orbit_density (U_iter m n) ↔ U_orbit_density n := by
  rw [U_orbit_density_iff_wordDensityHalf, U_orbit_density_iff_wordDensityHalf, uWord_U_iter,
    wordDensityHalf_shift_iff]

/-- **Prop. 5(i).** `X(U n₀) ↔ X(n₀)`. -/
@[category API, AMS 11 37, group "evgq17_m0_nogo"]
theorem U_orbit_density_U_iff (n : ℕ) : U_orbit_density (U n) ↔ U_orbit_density n :=
  U_orbit_density_U_iter_iff 1 n

/-- **Prop. 5(ii).** `X(n₀ + t·2^m) ↔ X(U^m(n₀) + t·3^m)`: the word of `n₀ + t·2^m` is the first
`m` letters of the word of `n₀` followed by the word of `U^m(n₀) + t·3^m`. -/
@[category API, AMS 11 37, group "evgq17_m0_nogo"]
theorem U_orbit_density_add_mul_two_pow_iff (m n t : ℕ) :
    U_orbit_density (n + t * 2 ^ m) ↔ U_orbit_density (U_iter m n + t * 3 ^ m) := by
  rw [← U_orbit_density_U_iter_iff m, U_iter_add_mul_two_pow le_rfl, Nat.sub_self, pow_zero,
    mul_one]

/-- **Prop. 5(iii).** If the failure set of `X` is not all of `ℕ`, some seed satisfies `X`. -/
@[category API, AMS 11 37, group "evgq17_m0_nogo"]
theorem exists_U_orbit_density_of_ne_univ (h : {n | ¬ U_orbit_density n} ≠ Set.univ) :
    ∃ n, U_orbit_density n := by
  by_contra hn
  push Not at hn
  exact h (Set.eq_univ_of_forall hn)

/-- **Prop. 5(iii), density form.** A density-`0` theorem for the failure set of `X` would produce
a seed satisfying `X` — an individual-orbit statement nobody knows how to prove. -/
@[category API, AMS 11 37, group "evgq17_m0_nogo"]
theorem exists_U_orbit_density_of_hasNatDensity_zero
    [DecidablePred (· ∈ {n | ¬ U_orbit_density n})]
    (h : HasNatDensity {n | ¬ U_orbit_density n} 0) : ∃ n, U_orbit_density n := by
  refine exists_U_orbit_density_of_ne_univ fun hu => ?_
  have h1 : HasNatDensity {n | ¬ U_orbit_density n} 1 := by
    have hc : ∀ N, natDensityCount {n | ¬ U_orbit_density n} N = N := by
      intro N
      unfold natDensityCount
      rw [filter_true_of_mem fun x _ => by rw [hu]; trivial, card_range]
    unfold HasNatDensity
    simp only [hc]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [div_self (Nat.cast_ne_zero.2 hN.ne' : (N : ℝ) ≠ 0)]
  exact zero_ne_one (h.unique h1)

/-! ## Proposition 4 -/

/-- **Prop. 4 (no-go).** Every set of seeds lies in the preimage, under the word map, of a
countable tail-saturated set of words.  Since the failure set of `X` is itself tail-saturated
(`tailSaturated_not_wordDensityHalf`) and Bernoulli-null, those two properties alone cannot bound
its density: they are shared by a set containing all of `ℕ`. -/
@[category API, AMS 11 37, group "evgq17_m0_nogo"]
theorem exists_tailSaturated_countable_superset (S : Set ℕ) :
    ∃ E : Set (ℕ → Bool), TailSaturated E ∧ E.Countable ∧ S ⊆ uWord ⁻¹' E :=
  ⟨{w | ∃ c ∈ uWord '' S, TailEq w c}, tailSaturated_tailSaturation _,
    countable_tailSaturation (Set.countable_range uWord |>.mono (Set.image_subset_range _ _)),
    fun n hn => ⟨uWord n, ⟨n, hn, rfl⟩, 0, 0, 0, fun _ _ => rfl⟩⟩

end EVG25.M0
