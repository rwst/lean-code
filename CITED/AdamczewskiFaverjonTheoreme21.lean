/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CITED.AdamczewskiFaverjonBranchFull
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# [AF22] Théorème 2.1: the final assembly

plan-formalize-AF17's **WP20**, the second half of gap (6) of Stage 2.
-/

open Filter Metric Topology

open scoped Polynomial LaurentSeries RatFunc

namespace AF

/-! ## Small transport lemmas -/

section Transport

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- A matrix identity over a field may be checked after an embedding. -/
@[category API, AMS 12 15, ref "AF22", group "af_mahler_alternative"]
theorem matrix_map_injective {R S : Type*} [CommRing R] [CommRing S] {e : R →+* S}
    (he : Function.Injective e) {M N : Matrix ι ι R} (h : M.map e = N.map e) : M = N := by
  ext i j
  exact he (congrFun (congrFun (congrArg (fun P : Matrix ι ι S => (P : ι → ι → S)) h) i) j)

/-- The relation ideal depends on the points and the values only. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem relationIdeal_congr {K σ : Type*} [Field K] {pt pt' : ℕ → K} (h : pt = pt')
    (hpt : Function.Injective pt) (hpt' : Function.Injective pt') {Y Y' : ℕ → σ → K}
    (hY : Y = Y') : relationIdeal hpt Y = relationIdeal hpt' Y' := by
  subst h
  subst hY
  rfl

/-- Two successive coefficient maps on a matrix of polynomials. -/
@[category API, AMS 13 15, ref "AF22", group "af_mahler_alternative"]
theorem mapMat_mapMat {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] (g : S →+* T)
    (e : R →+* S) (M : Matrix ι ι R[X]) : mapMat g (mapMat e M) = mapMat (g.comp e) M :=
  Matrix.ext fun i j => by
    rw [mapMat_apply, mapMat_apply, mapMat_apply, Polynomial.map_map]

/-- A polynomial system over `L`, read over an intermediate field `K`. -/
@[category API, AMS 11 39, ref "AF17", group "af_mahler_alternative"]
theorem isMahlerSolution_mapMat {L K : Type*} [Field L] [Field K] [Algebra L K] [Algebra K ℂ]
    [Algebra L ℂ] [IsScalarTower L K ℂ] {q : ℕ} {A : Matrix ι ι L[X]} {F : ι → ℂ → ℂ} {S : Set ℂ}
    (h : IsMahlerSolution q A F S) : IsMahlerSolution q (mapMat (algebraMap L K) A) F S := by
  intro z hz i
  rw [h z hz i]
  exact Finset.sum_congr rfl fun j _ => by
    rw [mapMat_apply, Polynomial.aeval_map_algebraMap]

omit [DecidableEq ι] in
/-- A bound for finitely many complex polynomials on a closed disc — the hypothesis `hA` of
[AF22] Lemma 2.11, and there is nothing to it but compactness. -/
@[category research solved, AMS 30, ref "AF22", group "af_mahler_alternative"]
theorem exists_polynomial_bound (B : Matrix ι ι ℂ[X]) (t : ℝ) :
    ∃ Cb : ℝ, 1 ≤ Cb ∧ ∀ z : ℂ, ‖z‖ ≤ t → ∀ i j, ‖(B i j).eval z‖ ≤ Cb := by
  classical
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) t).exists_bound_of_continuousOn
    (f := fun z => fun p : ι × ι => (B p.1 p.2).eval z)
    (continuousOn_pi.2 fun p => (B p.1 p.2).continuous_aeval.continuousOn)
  refine ⟨max C 1, le_max_right _ _, fun z hz i j => ?_⟩
  refine le_trans (le_trans ?_ (hC z (by simpa using hz))) (le_max_left _ _)
  exact norm_le_pi_norm (fun p : ι × ι => (B p.1 p.2).eval z) (i, j)

end Transport

/-! ## The assembly over an algebraically closed field of algebraic numbers -/

section Ambient

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K] [Algebra K ℂ]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **[AF22] Théorème 2.1 over the big field.**  A linear relation over `K` between the values of
the solutions at a regular point `α` lifts to a relation over `K[z]` between the power series
themselves, specializing to the given one at `α`.

The ambient field `Ω` of [AF22] §2.2 is an explicit argument although the statement does not
mention it: it is where the whole proof takes place — the relation matrix, the solutions and the
lifted relation all live there — and it is discharged at
`Ω = AlgebraicClosure K⸨z⸩` by `AF.exists_lift_series`. -/
@[category research solved, AMS 11 12 30 39, ref "AF22", group "af_mahler_alternative"]
theorem exists_lift_series_ambient (Ω : Type*) [Field Ω] [Algebra (LaurentSeries K) Ω]
    [Algebra (RatFunc K) Ω] [IsScalarTower (RatFunc K) (LaurentSeries K) Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic (LaurentSeries K) Ω] (hKalg : ∀ x : K, IsIntegral ℚ x)
    {q : ℕ} (hq : 2 ≤ q) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    {A : Matrix ι ι K[X]} (hA : A.det ≠ 0)
    {F : ι → ℂ → ℂ} (hF : IsMahlerSolution q A F (ball 0 r))
    {f : ι → PowerSeries K} (hf : ∀ i, IsSumOnBall r (f i) (F i))
    {α : K} (hα0 : α ≠ 0) (hα : ‖algebraMap K ℂ α‖ < r) (hreg : IsRegularPoint q A α)
    {τ : ι → K} (hrel : ∑ i, algebraMap K ℂ (τ i) * F i (algebraMap K ℂ α) = 0) :
    ∃ w : ι → K[X], (∑ i, (w i : PowerSeries K) * f i = 0) ∧ ∀ i, (w i).eval α = τ i := by
  classical
  have hq0 : q ≠ 0 := by omega
  set φ : K →+* ℂ := algebraMap K ℂ with hφdef
  have hα1 : ‖φ α‖ < 1 := lt_of_lt_of_le hα hr1
  -- the formal system, and the regularity of its solution field
  have hFf : IsFormalMahlerSolution q A f :=
    isFormalMahlerSolution_of_isMahlerSolution hq0 hr0 hr1 hF hf
  have hregΩ : IsRegularSolField K (fun i => toAmbientSeries K Ω (f i)) :=
    isRegularSolField_of_formalMahler hq hA hFf
  -- the relation matrix of §2.2
  have hpt : Function.Injective fun k : ℕ => α ^ q ^ k := injective_iterPow φ hq hα0 hα1
  obtain ⟨Φalg, hΦ, hΦint⟩ := exists_relationMatrix_algebraic Ω hpt
    (fun (n : ℕ) (w : ι × ι) => (iterMatrix q A n w.1 w.2).eval α)
    (Filter.Eventually.of_forall fun n => by
      have hd := iterMatrix_det_eval_ne_zero hreg n
      rwa [show (Matrix.of fun i j => (iterMatrix q A n i j).eval α)
        = (iterMatrix q A n).map (Polynomial.evalRingHom α) from rfl, det_map_ringHom])
  -- the radii
  set t : ℝ := min r 1 / 2 with htdef
  have ht0 : 0 < t := by
    have : (0 : ℝ) < min r 1 := lt_min hr0 one_pos
    positivity
  have ht1 : t < 1 := by
    have : min r 1 ≤ 1 := min_le_right _ _
    simp only [htdef]; linarith
  have htr : t < r := by
    have : min r 1 ≤ r := min_le_left _ _
    simp only [htdef]; linarith
  -- the branch of Lemma 2.8, at a `k₀` large enough for the disc to sit inside `‖z‖ ≤ t`
  have hpow : Tendsto (fun k : ℕ => ‖φ α‖ ^ q ^ k) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hα1).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by omega))
  have hsmall : ∀ᶠ k in atTop, ‖φ α ^ q ^ k‖ < t / 2 := by
    refine (hpow.eventually_lt_const (show (0 : ℝ) < t / 2 by positivity)).mono fun k hk => ?_
    rwa [norm_pow]
  obtain ⟨k₀, hk₀branch, hk₀small⟩ :=
    ((lemma_2_8 (Ω := Ω) φ hα0 hα1 hq hΦint hΦ.2 hr0
      (fun i => isSeriesSumOn_of_isSumOnBall (hf i))).and hsmall).exists
  obtain ⟨U, R, real, Ψ, Φ₀, hb, hconn, hsol, han, hinj, htwist⟩ := hk₀branch
  -- the number field of the descent: `ℚ` adjoined the finitely many algebraic numbers in play
  set Sgen : Finset K :=
    ((Finset.univ : Finset (ι × ι)).biUnion fun w =>
        (Finset.range ((A w.1 w.2).natDegree + 1)).image fun n => (A w.1 w.2).coeff n)
      ∪ ((Finset.univ : Finset ι).image τ)
      ∪ ((Finset.univ : Finset (ι × ι)).image fun w => Φ₀ w.1 w.2)
      ∪ ((Finset.univ : Finset ι).image fun i => PowerSeries.coeff 0 (f i))
      ∪ {α} with hSgendef
  set L₀ : IntermediateField ℚ K := IntermediateField.adjoin ℚ (Sgen : Set K) with hL₀def
  haveI : NumberField L₀ := numberField_adjoin_finset Sgen fun x _ => hKalg x
  have hsub : ∀ x ∈ Sgen, x ∈ L₀ := fun x hx => IntermediateField.subset_adjoin ℚ _ hx
  have hrng : ∀ x : K, x ∈ L₀ → x ∈ Set.range (algebraMap L₀ K) := fun x hx => ⟨⟨x, hx⟩, rfl⟩
  have hmemA : ∀ i j n, n ≤ (A i j).natDegree → (A i j).coeff n ∈ Sgen := fun i j n hn =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_univ _,
        Finset.mem_image.2 ⟨n, Finset.mem_range.2 (Nat.lt_succ_of_le hn), rfl⟩⟩))))
  have hmemτ : ∀ i, τ i ∈ Sgen := fun i =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩))))
  have hmemΦ : ∀ i j, Φ₀ i j ∈ Sgen := fun i j =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)))
  have hmemf : ∀ i, PowerSeries.coeff 0 (f i) ∈ Sgen := fun i =>
    Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩))
  have hmemα : α ∈ Sgen := Finset.mem_union_right _ (Finset.mem_singleton_self α)
  -- and the data, read over it
  have hAc : ∀ i j n, (A i j).coeff n ∈ Set.range (algebraMap L₀ K) := by
    intro i j n
    by_cases hn : n ≤ (A i j).natDegree
    · exact hrng _ (hsub _ (hmemA i j n hn))
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      exact ⟨0, map_zero _⟩
  have hfc : ∀ i, PowerSeries.coeff 0 (f i) ∈ Set.range (algebraMap L₀ K) := fun i =>
    hrng _ (hsub _ (hmemf i))
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : Matrix ι ι L₀[X], mapMat (algebraMap L₀ K) A₀ = A := by
    choose p hp using fun i j => exists_polynomial_map_eq (algebraMap L₀ K) (hAc i j)
    exact ⟨Matrix.of p, Matrix.ext fun i j => by rw [mapMat_apply]; exact hp i j⟩
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : ι → PowerSeries L₀, ∀ i, (f₀ i).map (algebraMap L₀ K) = f i := by
    choose g hg using fun i =>
      exists_map_eq_of_isFormalMahlerSolution hq (algebraMap L₀ K) hFf hAc hfc i
    exact ⟨g, hg⟩
  obtain ⟨Φ₀₀, hΦ₀₀⟩ : ∃ N : Matrix ι ι L₀, N.map (algebraMap L₀ K) = Φ₀ :=
    exists_matrix_map_eq _ fun i j => hrng _ (hsub _ (hmemΦ i j))
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ₀ : ι → L₀, ∀ i, algebraMap L₀ K (τ₀ i) = τ i := by
    choose c hc using fun i => hrng _ (hsub _ (hmemτ i))
    exact ⟨c, hc⟩
  obtain ⟨α₀, hα₀⟩ : ∃ α₀ : L₀, algebraMap L₀ K α₀ = α := hrng _ (hsub _ hmemα)
  -- the ambient field as an `L₀(z)`-algebra
  letI : Algebra (RatFunc L₀) Ω := ((algebraMap (RatFunc K) Ω).comp (ratFuncMap L₀ K)).toAlgebra
  have htow : IsRatFuncTower L₀ K Ω := rfl
  set φL : L₀ →+* ℂ := φ.comp (algebraMap L₀ K) with hφLdef
  set ξ : ℂ := φ α ^ q ^ k₀ with hξdef
  have hφLα : φL α₀ = φ α := by rw [hφLdef, RingHom.comp_apply, hα₀]
  have hmapA : mapMat φL A₀ = mapMat φ A := by
    rw [hφLdef, ← mapMat_mapMat, hA₀]
  -- the branch, descended, and the normalizing matrix of Lemma 2.8(c)
  have hbL : IsAnalyticBranch φ Φalg ξ U R real Ψ (Φ₀₀.map (algebraMap L₀ K)) := by
    rw [hΦ₀₀]; exact hb
  obtain ⟨M₀, hM₀⟩ := (isAnalyticBranch_descend htow hbL).exists_normalization
    (evalMat α₀ (iterMatrix q A₀ k₀))
  have ha : M₀.map φL * Ψ ξ = evalMat (φL α₀) (iterMatrix q (mapMat φL A₀) k₀) := by
    rw [hM₀, ← evalMat_mapMat, mapMat_iterMatrix]
  have hMΦ : M₀.map (algebraMap L₀ K) * Φ₀ = evalMat α (iterMatrix q A k₀) := by
    refine matrix_map_injective φ.injective ?_
    rw [Matrix.map_mul, Matrix.map_map, ← RingHom.coe_comp, ← hφLdef, hb.map_value, ha, hφLα,
      hmapA, ← mapMat_iterMatrix, evalMat_mapMat]
  -- the hypotheses of Lemma 2.11, over the number field
  have hptL : Function.Injective fun k : ℕ => α₀ ^ q ^ k := by
    intro a b hab
    refine hpt ?_
    simpa only [map_pow, hα₀] using congrArg (algebraMap L₀ K) hab
  have hfunpt : (fun k : ℕ => algebraMap L₀ K (α₀ ^ q ^ k)) = fun k : ℕ => α ^ q ^ k := by
    funext k; rw [map_pow, hα₀]
  have hptK : Function.Injective fun k : ℕ => algebraMap L₀ K (α₀ ^ q ^ k) := by
    rw [hfunpt]; exact hpt
  have hYfun : (fun (n : ℕ) (w : ι × ι) => algebraMap L₀ K ((iterMatrix q A₀ n w.1 w.2).eval α₀))
      = fun (n : ℕ) (w : ι × ι) => (iterMatrix q A n w.1 w.2).eval α := by
    funext n w
    rw [algebraMap_iterMatrix_eval (algebraMap L₀ K) q n A₀ α₀ w.1 w.2, hA₀, hα₀]
  have hrelmat : IsRelationMatrix (relationIdeal hptK
      (fun (n : ℕ) (w : ι × ι) =>
        algebraMap L₀ K ((iterMatrix q A₀ n w.1 w.2).eval α₀))) Φalg := by
    rw [relationIdeal_congr hfunpt hptK hpt hYfun]
    exact hΦ
  obtain ⟨ρ, hρ0, hρt, hρU⟩ := hb.exists_radius (ρ₀ := t / 2) (by positivity)
  have hsph : ∀ z ∈ closedBall ξ ρ, ‖z‖ ≤ t := by
    intro z hz
    have hd : ‖z - ξ‖ ≤ ρ := by simpa [dist_eq_norm] using mem_closedBall.1 hz
    calc ‖z‖ = ‖z - ξ + ξ‖ := by ring_nf
      _ ≤ ‖z - ξ‖ + ‖ξ‖ := norm_add_le _ _
      _ ≤ t / 2 + t / 2 := add_le_add (le_trans hd hρt) (le_of_lt hk₀small)
      _ = t := by ring
  have hmapf : ∀ j, (f₀ j).map φL = (f j).map φ := by
    intro j
    ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_map, hφLdef, RingHom.comp_apply,
      ← PowerSeries.coeff_map, hf₀ j]
  have hrealL : ∀ j, IsSumOn r ((f₀ j).map φL) (F j) := fun j => by
    rw [hmapf j]
    exact isSeriesSumOn_iff_isSumOn_map.1 (isSeriesSumOn_of_isSumOnBall (hf j))
  have hstab : ∀ z : ℂ, ‖z‖ < r → ‖z ^ q‖ < r := by
    intro z hz
    rw [norm_pow]
    calc ‖z‖ ^ q ≤ ‖z‖ ^ 1 :=
          pow_le_pow_of_le_one (norm_nonneg z) (le_trans hz.le hr1) (by omega)
      _ = ‖z‖ := pow_one _
      _ < r := hz
  have hS : ∀ z ∈ ball (0 : ℂ) r, z ^ q ∈ ball (0 : ℂ) r := by
    intro z hz
    simp only [mem_ball, dist_zero_right] at hz ⊢
    exact hstab z hz
  have hmah : IsMahlerSolution q (mapMat φL A₀) F (ball 0 r) := by
    rw [hmapA]; exact isMahlerSolution_mapMat hF
  have hαS : φL α₀ ∈ ball (0 : ℂ) r := by
    simp only [mem_ball, dist_zero_right, hφLα]; exact hα
  have hLform : formVal (fun i => φL (τ₀ i)) F 1 (φL α₀) = 0 := by
    have hone : ∀ i, ∑ j, φL (τ₀ i) * (1 : Matrix ι ι ℂ) i j * F j (φL α₀)
        = φL (τ₀ i) * F i (φL α₀) := by
      intro i
      rw [Finset.sum_eq_single i]
      · rw [Matrix.one_apply_eq, mul_one]
      · intro j _ hj; rw [Matrix.one_apply_ne (Ne.symm hj), mul_zero, zero_mul]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [formVal, Finset.sum_congr rfl fun i _ => hone i]
    have hτK : ∀ i, φL (τ₀ i) = φ (τ i) := fun i => by
      rw [hφLdef, RingHom.comp_apply, hτ₀ i]
    simp only [hτK, hφLα]
    exact hrel
  have hSt : ∀ z : ℂ, ‖z‖ ≤ t → z ∈ ball (0 : ℂ) r := by
    intro z hz
    simp only [mem_ball, dist_zero_right]
    linarith
  obtain ⟨Cb, hC1, hCbd⟩ := exists_polynomial_bound (mapMat φ A) t
  have hCbd' : ∀ z : ℂ, ‖z‖ ≤ t → ∀ i j, ‖(mapMat φL A₀ i j).eval z‖ ≤ Cb := by
    rw [hmapA]; exact hCbd
  have h1C : 1 ≤ (Fintype.card ι : ℝ) * Cb := by
    have hc : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.2 ‹Nonempty ι›
    nlinarith
  -- [AF22] Lemma 2.11
  have hkl := key_lemma_descent htow hq (φ := φ) (φL := φL) rfl τ₀ hptL hptK hrelmat hbL
    hρU hρ0 hsph hrealL hr0 hS hmah hαS hLform hSt (by rw [hξdef, hφLα]) ha
    (s := r / 2) (by positivity) (by linarith) ht0 ht1 htr hC1 hCbd' h1C
  -- back to the big field, and §2.4
  have hτK : (fun i => φ (τ i)) = fun i => φL (τ₀ i) := by
    funext i; rw [hφLdef, RingHom.comp_apply, hτ₀ i]
  have hMmap : (M₀.map (algebraMap L₀ K)).map φ = M₀.map φL := by
    rw [Matrix.map_map, ← RingHom.coe_comp, ← hφLdef]
  have h0 : ∀ᶠ z in 𝓝 ξ, formVal (fun i => φ (τ i)) F
      ((M₀.map (algebraMap L₀ K)).map φ * Ψ z) z = 0 := by
    rw [hτK, hMmap]; exact hkl
  have hpos : 0 < q ^ k₀ := pow_pos (by omega) k₀
  obtain ⟨V, R', real', Ψ', hbtw⟩ :=
    htwist (ambientSubst K hpos.ne') fun hn c => ambientSubst_ratFunc hn c
  obtain ⟨w, hw0, hwev⟩ := exists_lift_of_eventually_formVal_eq_zero (K := K) (Ω := Ω)
    (q := q) (k₀ := k₀) (A := A) (α := α) hregΩ (ambientSubst K hpos.ne')
    (fun a => ambientSubst_ambC hpos a) (fun i => ambient_mahler_iter hq0 hFf k₀ i)
    hb.isBranch hsol han hinj hb.isOpen_dom hconn hb.mem_dom h0 hMΦ
    (iterMatrix_det_eval_ne_zero hreg k₀) hbtw
    (fun l j => isIntegral_ambientSubst hpos (hΦint l j))
  refine ⟨w, ?_, hwev⟩
  refine toAmbientSeries_injective (K := K) (Ω := Ω) ?_
  rw [map_zero, map_sum, ← hw0]
  exact Finset.sum_congr rfl fun i _ => by rw [map_mul, toAmbientSeries_poly]

/-- **[AF22] Théorème 2.1 over the field of algebraic numbers.**  `AF.exists_lift_series_ambient`
with the ambient field of §2.2 discharged: `Ω = AlgebraicClosure K⸨z⸩` carries every instance the
proof asks for. -/
@[category research solved, AMS 11 12 30 39, ref "AF22", group "af_mahler_alternative"]
theorem exists_lift_series (hKalg : ∀ x : K, IsIntegral ℚ x)
    {q : ℕ} (hq : 2 ≤ q) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    {A : Matrix ι ι K[X]} (hA : A.det ≠ 0)
    {F : ι → ℂ → ℂ} (hF : IsMahlerSolution q A F (ball 0 r))
    {f : ι → PowerSeries K} (hf : ∀ i, IsSumOnBall r (f i) (F i))
    {α : K} (hα0 : α ≠ 0) (hα : ‖algebraMap K ℂ α‖ < r) (hreg : IsRegularPoint q A α)
    {τ : ι → K} (hrel : ∑ i, algebraMap K ℂ (τ i) * F i (algebraMap K ℂ α) = 0) :
    ∃ w : ι → K[X], (∑ i, (w i : PowerSeries K) * f i = 0) ∧ ∀ i, (w i).eval α = τ i :=
  exists_lift_series_ambient (AlgebraicClosure (LaurentSeries K)) hKalg hq hr0 hr1 hA hF hf
    hα0 hα hreg hrel

end Ambient

/-! ## [AF22] Théorème 2.1, over an arbitrary field of algebraic numbers -/

section Final

variable {L : Type*} [Field L] [Algebra L ℂ] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **[AF22] Théorème 2.1 = [AF17] Théorème 1.4 in degree one, over a field embedded in an
algebraically closed field of algebraic numbers.**  The relation is lifted over `K`, where the whole
of §2 lives, and brought back to `L[z]` by [AF17] Lemme 4.3 in its prescribed-value form
(`AF.lemme_4_3_eval`) — which changes neither the relation nor its value at `α`, precisely because
the solutions have their coefficients in `L`. -/
@[category research solved, AMS 11 12 30 39, ref "AF22" "AF17", group "af_mahler_alternative"]
theorem lifting_regular_of_embedding {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    [Algebra K ℂ] [Algebra L K] [IsScalarTower L K ℂ] (hKalg : ∀ x : K, IsIntegral ℚ x)
    {q : ℕ} (hq : 2 ≤ q) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    {A : Matrix ι ι L[X]} (hA : A.det ≠ 0)
    {F : ι → ℂ → ℂ} (hF : IsMahlerSolution q A F (ball 0 r))
    {f : ι → PowerSeries L} (hf : ∀ i, IsSumOnBall r (f i) (F i))
    {α : L} (hα0 : α ≠ 0) (hα : ‖algebraMap L ℂ α‖ < r)
    (hreg : IsRegularPoint q A (algebraMap L ℂ α))
    {lam : ι → L} (hrel : ∑ i, algebraMap L ℂ (lam i) * F i (algebraMap L ℂ α) = 0) :
    ∃ w : ι → L[X], (∀ z : ℂ, ‖z‖ < r → ∑ i, Polynomial.aeval z (w i) * F i z = 0) ∧
      ∀ i, (w i).eval α = lam i := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨fun _ => 0, fun z _ => by simp, fun i => (hι.false i).elim⟩
  set e : L →+* K := algebraMap L K with hedef
  have hein : Function.Injective e := e.injective
  have hcomp : ∀ x : L, algebraMap K ℂ (e x) = algebraMap L ℂ x := fun x =>
    (IsScalarTower.algebraMap_apply L K ℂ x).symm
  -- the data, read over `K`
  have hdet : (mapMat e A).det = (A.det).map e := by
    rw [show mapMat e A = A.map (Polynomial.mapRingHom e) from
      Matrix.ext fun i j => mapMat_apply e A i j, det_map_ringHom]
    rfl
  have hA' : (mapMat e A).det ≠ 0 := by
    rw [hdet]
    exact fun h => hA ((Polynomial.map_eq_zero_iff hein).1 h)
  have hF' : IsMahlerSolution q (mapMat e A) F (ball 0 r) := isMahlerSolution_mapMat hF
  have hf' : ∀ i, IsSumOnBall r ((f i).map e) (F i) := fun i => (hf i).mapCoeff
  have hreg' : IsRegularPoint q (mapMat e A) (e α) := by
    intro l
    have hev : ∀ x : L, Polynomial.aeval (algebraMap L ℂ x) A.det
        = algebraMap L ℂ ((A.det).eval x) := fun x => aeval_algebraMap_eq x A.det
    have h1 : (A.det).eval (α ^ q ^ l) ≠ 0 := by
      intro h
      have := hreg l
      rw [← map_pow, hev, h, map_zero] at this
      exact this rfl
    have h2 : Polynomial.aeval (e α ^ q ^ l) (mapMat e A).det
        = e ((A.det).eval (α ^ q ^ l)) := by
      rw [hdet, ← map_pow, Polynomial.aeval_def, Polynomial.eval₂_map,
        show (algebraMap K K).comp e = e from RingHom.ext fun _ => rfl,
        Polynomial.eval₂_at_apply]
    rw [h2]
    exact fun h => h1 (hein (by rw [h, map_zero]))
  have hrel' : ∑ i, algebraMap K ℂ (e (lam i)) * F i (algebraMap K ℂ (e α)) = 0 := by
    simp only [hcomp]; exact hrel
  obtain ⟨w, hw0, hwev⟩ := exists_lift_series (K := K) hKalg hq hr0 hr1 hA' hF' hf'
    (fun h => hα0 (hein (by rw [h, map_zero]))) (by rw [hcomp]; exact hα) hreg' hrel'
  obtain ⟨w', hw'0, hw'ev⟩ := lemme_4_3_eval (k := L) (L := K) f α lam w hw0 hwev
  exact ⟨w', fun z hz => eval_of_relation_formal hf w' hw'0 hz, hw'ev⟩

/-- **[AF22] Théorème 2.1 = [AF17] Théorème 1.4 in degree one.**  A linear relation over a field
`L` of algebraic numbers between the values `f_i(α)` at a regular point lifts to a linear relation
over `L[z]` between the functions, specializing to the given one at `α`.

This is the statement `CITED/AdamczewskiFaverjonProof.lean` records as the axiom
`AF.lifting_regular`, now a theorem: its footprint is `std3` together with the two cited axioms of
Stage 2, `AF.lemme_2_2` ([AF17] Lemme 2.2) and `AF.lemma_2_8` ([AF22] Lemma 2.8). -/
@[category research solved, AMS 11 12 30 39, ref "AF22" "AF17", group "af_mahler_alternative"]
theorem theoreme_2_1 {q : ℕ} (hq : 2 ≤ q) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hLalg : ∀ x : L, IsAlgebraic ℚ (algebraMap L ℂ x))
    {A : Matrix ι ι L[X]} (hA : A.det ≠ 0)
    {F : ι → ℂ → ℂ} (hF : IsMahlerSolution q A F (ball 0 r))
    {f : ι → PowerSeries L} (hf : ∀ i, IsSumOnBall r (f i) (F i))
    {α : L} (hα0 : α ≠ 0) (hα : ‖algebraMap L ℂ α‖ < r)
    (hreg : IsRegularPoint q A (algebraMap L ℂ α))
    {lam : ι → L} (hrel : ∑ i, algebraMap L ℂ (lam i) * F i (algebraMap L ℂ α) = 0) :
    ∃ w : ι → L[X], (∀ z : ℂ, ‖z‖ < r → ∑ i, Polynomial.aeval z (w i) * F i z = 0) ∧
      ∀ i, (w i).eval α = lam i := by
  haveI : IsAlgClosure ℚ ↥(algebraicClosure ℚ ℂ) := algebraicClosure.isAlgClosure ℚ ℂ
  haveI : IsAlgClosed ↥(algebraicClosure ℚ ℂ) := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero ↥(algebraicClosure ℚ ℂ) :=
    charZero_of_injective_algebraMap
      (algebraMap ℚ ↥(algebraicClosure ℚ ℂ)).injective
  letI : Algebra L ↥(algebraicClosure ℚ ℂ) :=
    ((algebraMap L ℂ).codRestrict (algebraicClosure ℚ ℂ).toSubring
      fun x => mem_algebraicClosure_iff.2 (hLalg x)).toAlgebra
  haveI : IsScalarTower L ↥(algebraicClosure ℚ ℂ) ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine lifting_regular_of_embedding (K := ↥(algebraicClosure ℚ ℂ)) (fun x => ?_) hq hr0 hr1
    hA hF hf hα0 hα hreg hrel
  exact ((mem_algebraicClosure_iff.1 x.2).isIntegral).tower_bot
    (algebraMap ↥(algebraicClosure ℚ ℂ) ℂ).injective

end Final

end AF
