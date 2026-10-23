/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import QuantitativeSubspace.SubspaceCountTwo

/-!
# The large solutions of a system, as an interval result (WP A5 of plan-beyond-BB13)

Subspace-Theorems' assembly `NumberField.exists_finset_submodule_of_forall_interval` takes an
interval result for the domains (the levels `log Q ≥ X₀` not covered by `NS` subspaces lie in
`NI` intervals `[s, ρ s)`) and turns it into subspaces for the solutions of a normalized
system. It does so in two steps: it brings the solutions into the domain (raised exponents and
one scalar for the constants), and then it spends Layer 9.4's gap principle at ratio
`1 + δ / (2 n)` on each interval.

This file stops after the first step. Its result says that the large solutions lie in `NS`
proper subspaces, or have `log H(x)` in one of `NI` intervals `[s, ρ s)`. The intervals do not
depend on the solution, since the raised exponents are chosen once for the system. A system
with a better gap principle of its own can then count each interval itself; for the frame of
Problem 10.13 this is the elementary ratio `ρ₀ ≈ 1.2618` against `1 + δ/4 ≈ 1.065`
(`BB13/LineCoverRho.lean`).

## Main results

* `BB13.exists_interval_of_forall_interval`: the first step of the assembly, for any interval
  result of the conjugated forms.
* `BB13.exists_interval_of_isNormalizedSystem_two`: the same with the interval result in two
  variables (`NumberField.exists_forall_mem_interval_approxDomain_two`): at most two subspaces and
  `subspaceChainLength 1 s (2 ε) A` intervals of ratio `4 σ⁻¹`, above any
  `X₀ ≥ systemThresholdTwo`.

This is the shape of item M1 of `plans/plan-beyond-BB13.html` §7 (a two-variable count with a
user-supplied gap). It belongs in `DiophantineApproximation/SystemSubspaceCount.lean` upstream;
the proof is the first half of `exists_finset_submodule_of_forall_interval`.

## References

* J.-H. Evertse, *On the Quantitative Subspace Theorem*, Zap. Nauchn. Sem. POMI **377** (2010),
  proof of Theorem 2.1.
* `plans/plan-beyond-BB13.html`, §3.4, WP A5; §7, M1.
-/

open Finset Module NumberField IsDedekindDomain Height

universe u

namespace BB13

variable {K E : Type*} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
variable {ι : Type u} [Fintype ι]

open scoped Classical in
/-- **The large solutions of a system lie in `NS` subspaces or in `NI` height intervals**, from
any interval result above `X₀` for the conjugated forms (the hypothesis of
`NumberField.exists_finset_submodule_of_forall_interval`). The intervals `[s, ρ s)` of
`log H(x)` are the same for every solution. -/
theorem exists_interval_of_forall_interval [IsGalois K E]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (w : AbsoluteValue K ℝ → AbsoluteValue E ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) {X₀ ρ : ℝ} {NS NI : ℕ}
    (hX₀H : systemHeightThreshold (Fintype.card ι) (finrank ℚ E)
      (Fintype.card (InfinitePlace K) + #S) δ H (Real.log (scalarConst K S)) ≤ X₀)
    (hX₀n : finrank ℚ K * (2 * Fintype.card ι / δ) * Real.log (Fintype.card ι) ≤ X₀)
    (hint : ∀ c' : AbsoluteValue E ℝ → ι → ℝ,
      approxWeight (systemPlacesOver E S) c' ≤ -systemEps (finrank K E) δ →
      approxAbsWeight (systemPlacesOver E S) c' ≤ systemAbsBound (finrank K E) (Fintype.card ι) →
      approxWeight (systemPlacesOver E S) c' = -(finrank K E * δ / 2) →
      approxSupWeight (systemPlacesOver E S) c' ≤
        finrank K E * (1 + δ / (2 * Fintype.card ι)) →
      ∃ T : Finset (Submodule E (ι → E)), #T ≤ NS ∧ (∀ W ∈ T, W ≠ ⊤) ∧
        ∃ 𝒯 : Finset ℝ, #𝒯 ≤ NI ∧ (∀ s ∈ 𝒯, X₀ ≤ s) ∧
          ∀ Q : ℝ, 1 < Q → X₀ ≤ Real.log Q →
            (∃ W ∈ T, approxDomain (systemPlacesOver E S)
              (conjSystem univ (S.image FinitePlace.mk) w L) c' Q ⊆ W) ∨
              ∃ s ∈ 𝒯, s ≤ Real.log Q ∧ Real.log Q < ρ * s) :
    ∃ T : Finset (Submodule K (ι → K)), #T ≤ NS ∧ (∀ U ∈ T, U ≠ ⊤) ∧
      ∃ 𝒯 : Finset ℝ, #𝒯 ≤ NI ∧ (∀ s ∈ 𝒯, X₀ ≤ s) ∧
        ∀ x ∈ systemSet S w L C c, X₀ ≤ Real.log (mulHeightAff x) →
          (∃ U ∈ T, x ∈ U) ∨
            ∃ s ∈ 𝒯, s ≤ Real.log (mulHeightAff x) ∧ Real.log (mulHeightAff x) < ρ * s := by
  set n := Fintype.card ι with hn
  have hn2 : 2 ≤ n := hN.two_le_card
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hδ := hN.delta_pos
  have hδ1 := hN.delta_le_one
  have hH1 := hN.one_le_height
  set e := finrank K E with he
  set t := Fintype.card (InfinitePlace K) + #S with ht
  have hcardS : Fintype.card (InfinitePlace K ⊕ S) = t := by
    rw [Fintype.card_sum, Fintype.card_coe]
  have ht0 : (0 : ℝ) < t := by
    have := Fintype.card_pos (α := InfinitePlace K)
    exact_mod_cast (by omega : 0 < t)
  have he0 : (0 : ℝ) < e := by exact_mod_cast (finrank_pos : 0 < finrank K E)
  set Sfin' := systemPlacesOver E S with hSfin'
  set L' := conjSystem univ (S.image FinitePlace.mk) w L with hL'
  have hX₀pos : 0 < X₀ := by
    have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hK : (0 : ℝ) < finrank ℚ K := by exact_mod_cast finrank_pos
    exact (by positivity : (0 : ℝ) < finrank ℚ K * (2 * n / δ) * Real.log n).trans_le hX₀n
  -- the raised exponents
  obtain ⟨c', hcc', hc'w, hc'A, hc's⟩ := hN.exists_raise
  -- the scalar
  set Z : ℝ := (n.factorial : ℝ) * (H ^ finrank ℚ E) ^ n with hZ
  have hZ1 : 1 ≤ Z := one_le_mul_of_one_le_of_one_le
    (Nat.one_le_cast.2 (Nat.factorial_pos _)) (one_le_pow₀ (one_le_pow₀ hH1))
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ1
  have hlogZ : Real.log Z = Real.log n.factorial + n * (finrank ℚ E * Real.log H) := by
    rw [hZ, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  set μ := Real.log (scalarConst K S) with hμ
  set a : ℝ := (μ + 2 * t / n * Real.log Z) / t with ha
  set κ := Real.exp a with hκ
  have hC0 := hN.const_pos
  have hprodC : ∏ p, C p ≤ Z ^ (2 * (t : ℝ) / n) := by
    have h1 := hN.const_le
    rw [systemConst] at h1
    refine h1.trans ?_
    calc systemDet S w L ^ ((n : ℝ)⁻¹) ≤ (Z ^ (2 * t)) ^ ((n : ℝ)⁻¹) :=
          Real.rpow_le_rpow (systemDet_pos hN).le (hN.systemDet_le hwInf hwFin) (by positivity)
      _ = Z ^ (2 * (t : ℝ) / n) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hZ0.le]
          push_cast
          ring_nf
  have hκt : κ ^ t = scalarConst K S * Z ^ (2 * (t : ℝ) / n) := by
    rw [hκ, ← Real.exp_nat_mul, ha, mul_div_cancel₀ _ ht0.ne', Real.exp_add, hμ,
      Real.exp_log (scalarConst_pos S), Real.rpow_def_of_pos hZ0]
    ring_nf
  have hB : ∀ p, 0 < κ / C p := fun p ↦ div_pos (Real.exp_pos _) (hC0 p)
  have hBprod : scalarConst K S ≤ ∏ p, κ / C p := by
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, hcardS, hκt,
      le_div_iff₀ (Finset.prod_pos fun p _ ↦ hC0 p)]
    exact mul_le_mul_of_nonneg_left hprodC (scalarConst_pos S).le
  obtain ⟨β, hβ0, hβint, hβ⟩ := exists_ne_zero_systemAbs_le S hB hBprod
  -- the exponents of the domain
  set γ : ℝ := δ / (2 * n * t) with hγ
  have hγ0 : 0 ≤ γ := by positivity
  have htnγ : (t : ℝ) * n * γ = δ / 2 := by rw [hγ]; field_simp
  set e' : InfinitePlace K ⊕ S → ι → ℝ := fun p i ↦ c' p i + γ with he'
  have hsw : systemWeight e' = systemWeight c' + t * n * γ := by
    simp only [he', systemWeight, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      hcardS, nsmul_eq_mul]
    ring
  have hw' : approxWeight Sfin' (conjExponent S e') ≤ -systemEps e δ := by
    rw [approxWeight_conjExponent, systemEps, hsw, htnγ]
    nlinarith
  have hA' : approxAbsWeight Sfin' (conjExponent S e') ≤ systemAbsBound e n := by
    rw [approxAbsWeight_conjExponent, systemAbsBound]
    refine mul_le_mul_of_nonneg_left ?_ he0.le
    calc ∑ p, ∑ i, |e' p i| ≤ ∑ p, ∑ i, (|c' p i| + γ) :=
          Finset.sum_le_sum fun p _ ↦ Finset.sum_le_sum fun i _ ↦ by
            refine (abs_add_le _ _).trans_eq ?_
            rw [abs_of_nonneg hγ0]
      _ = ∑ p, ∑ i, |c' p i| + t * n * γ := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcardS,
            nsmul_eq_mul]
          ring
      _ ≤ 2 * n + 2 := by rw [htnγ]; linarith
  have hwe : approxWeight Sfin' (conjExponent S e') = -(e * δ / 2) := by
    rw [approxWeight_conjExponent, hsw, htnγ, hc'w]
    ring
  have hsup : approxSupWeight Sfin' (conjExponent S e') ≤ e * (1 + δ / (2 * n)) := by
    rw [approxSupWeight_conjExponent]
    refine mul_le_mul_of_nonneg_left ?_ he0.le
    calc ∑ p, ⨆ i, e' p i ≤ ∑ p, (systemExponent S p + γ) :=
          Finset.sum_le_sum fun p _ ↦ ciSup_le fun i ↦ by
            simp only [he']
            linarith [hc's p i]
      _ = 1 + δ / (2 * n) := by
          rw [Finset.sum_add_distrib, sum_systemExponent, Finset.sum_const, Finset.card_univ,
            hcardS, nsmul_eq_mul, hγ]
          field_simp
  obtain ⟨T, hTcard, hTtop, 𝒯, h𝒯card, h𝒯ge, hQint⟩ := hint _ hw' hA' hwe hsup
  -- `β x` lies in the domain
  have hdom : ∀ x ∈ systemSet S w L C c, X₀ ≤ Real.log (mulHeightAff x) →
      (fun j ↦ algebraMap K E (β * x j)) ∈ approxDomain Sfin' L' (conjExponent S e')
        (mulHeightAff x) := fun x hx hlogH ↦ by
    have hHx0 := mulHeightAff_pos x
    have hlH : 0 < Real.log (mulHeightAff x) := hX₀pos.trans_le hlogH
    have hHx1 : 1 ≤ mulHeightAff x := ((Real.log_pos_iff hHx0.le).1 hlH).le
    have hκx : κ ≤ mulHeightAff x ^ γ := by
      rw [hκ, Real.rpow_def_of_pos hHx0, Real.exp_le_exp]
      have h1 := hX₀H.trans hlogH
      rw [systemHeightThreshold, ← hlogZ, div_le_iff₀ hδ] at h1
      rw [ha, hγ, div_le_iff₀ ht0]
      have : Real.log (mulHeightAff x) * (δ / (2 * n * t)) * t =
          Real.log (mulHeightAff x) * δ / (2 * n) := by field_simp
      rw [this, le_div_iff₀ (by positivity)]
      have : (μ + 2 * t / n * Real.log Z) * (2 * n) = 2 * n * μ + 4 * t * Real.log Z := by
        field_simp
        ring
      rw [this]
      linarith
    refine mem_approxDomain_conjSystem hwInf hwFin L hHx0.le
      (fun j ↦ mul_mem hβint (hx.1 j)) fun p i ↦ ?_
    rw [systemValue_mul S w hwInf hwFin]
    calc systemPlace S p β ^ systemMult S p * systemValue S w L p i x
        ≤ κ / C p * (C p * mulHeightAff x ^ c p i) :=
          mul_le_mul (hβ p) (hx.2 p i) (systemValue_nonneg ..) (hB p).le
      _ = κ * mulHeightAff x ^ c p i := by field_simp [(hC0 p).ne']
      _ ≤ mulHeightAff x ^ γ * mulHeightAff x ^ c' p i :=
          mul_le_mul hκx (Real.rpow_le_rpow_of_exponent_le hHx1 (hcc' p i))
            (Real.rpow_nonneg hHx0.le _) (Real.rpow_nonneg hHx0.le _)
      _ = mulHeightAff x ^ e' p i := by rw [he', Real.rpow_add hHx0, mul_comm]
  refine ⟨T.image fun W ↦ (W.restrictScalars K).comap (algebraMapPi K E ι),
    Finset.card_image_le.trans hTcard, fun U hU ↦ ?_, 𝒯, h𝒯card, h𝒯ge, fun x hx hlogH ↦ ?_⟩
  · obtain ⟨W, hW, rfl⟩ := Finset.mem_image.1 hU
    exact comap_algebraMapPi_ne_top (hTtop W hW)
  have hy := hdom x hx hlogH
  have hH1 : 1 < mulHeightAff x := by
    rw [← Real.log_pos_iff (mulHeightAff_pos x).le]
    linarith
  rcases hQint (mulHeightAff x) hH1 hlogH with ⟨W, hW, hsub⟩ | hs
  · refine Or.inl ⟨_, Finset.mem_image_of_mem _ hW, ?_⟩
    have hβE : algebraMap K E β ≠ 0 := (map_ne_zero _).2 hβ0
    have hxW : (fun j ↦ algebraMap K E (x j)) ∈ W := by
      have h := W.smul_mem (algebraMap K E β)⁻¹ (hsub hy)
      convert h using 1
      funext j
      simp [map_mul, inv_mul_cancel_left₀ hβE]
    exact hxW
  · exact Or.inr hs

open scoped Classical in
/-- **The large solutions of a system in two variables lie in two subspaces or in `m` height
intervals**: for every `X₀ ≥ systemThresholdTwo`, at most two proper subspaces and at most
`m = subspaceChainLength 1 s (2 ε) A` intervals `[s, 4 σ⁻¹ s)`, `s ≥ X₀`, of `log H(x)`, with
`s = R [E : K]`, `ε = systemEps [E : K] δ`, `A = systemAbsBound [E : K] 2` and `σ` the ratio of
the Roth lemma. -/
theorem exists_interval_of_isNormalizedSystem_two [IsGalois K E] (RL : SubspaceRoth.{u} E)
    (hcard : Fintype.card ι = 2)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (w : AbsoluteValue K ℝ → AbsoluteValue E ℝ)
    (hwInf : ∀ v : InfinitePlace K, (w v.1).LiesOver v.1)
    (hwFin : ∀ v ∈ S, (w (FinitePlace.mk v).1).LiesOver (FinitePlace.mk v).1)
    {L : AbsoluteValue K ℝ → ι → Dual E (ι → E)} {C : InfinitePlace K ⊕ S → ℝ}
    {c : InfinitePlace K ⊕ S → ι → ℝ} {H : ℝ} {D R : ℕ} {δ : ℝ}
    (hN : IsNormalizedSystem S w L C c H D R δ) {X₀ : ℝ}
    (hX₀ : systemThresholdTwo E S w L RL.toRothParams R H δ ≤ X₀) :
    ∃ T : Finset (Submodule K (ι → K)), #T ≤ 2 ∧ (∀ U ∈ T, U ≠ ⊤) ∧
      ∃ 𝒯 : Finset ℝ,
        #𝒯 ≤ subspaceChainLength 1 (R * finrank K E) (2 * systemEps (finrank K E) δ)
          (systemAbsBound (finrank K E) 2) ∧ (∀ s ∈ 𝒯, X₀ ≤ s) ∧
        ∀ x ∈ systemSet S w L C c, X₀ ≤ Real.log (mulHeightAff x) →
          (∃ U ∈ T, x ∈ U) ∨
            ∃ s ∈ 𝒯, s ≤ Real.log (mulHeightAff x) ∧ Real.log (mulHeightAff x) <
              4 * (RL.ratio 1 (R * finrank K E) (2 * systemEps (finrank K E) δ)
                (systemAbsBound (finrank K E) 2))⁻¹ * s := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hLI : ∀ v : InfinitePlace K, LinearIndependent E (L v.1) := fun v ↦
    hN.linearIndependent (.inl v)
  have hLF : ∀ p ∈ S, LinearIndependent E (L (FinitePlace.mk p).1) := fun p hp ↦
    hN.linearIndependent (.inr ⟨p, hp⟩)
  have hε0 : 0 < systemEps (finrank K E) δ := by
    have := hN.delta_pos
    have he0 : (0 : ℝ) < finrank K E := by exact_mod_cast (finrank_pos : 0 < finrank K E)
    rw [systemEps]; positivity
  have hsE : formCount (systemPlacesOver E S) (conjSystem univ (S.image FinitePlace.mk) w L) ≤
      2 * (R * finrank K E) :=
    (formCount_conjSystem_le hwInf hwFin hN.ncard_le).trans (Nat.le_mul_of_pos_left _ two_pos)
  have hX₀T := (le_max_right _ _).trans hX₀
  have hX₀P : twoThreshold (systemPlacesOver E S) (conjSystem univ (S.image FinitePlace.mk) w L)
      RL.toRothParams (R * finrank K E) (systemEps (finrank K E) δ)
      (systemAbsBound (finrank K E) (Fintype.card ι)) ≤ X₀ := (le_max_left _ _).trans hX₀
  rw [hcard] at hX₀P
  have h := exists_interval_of_forall_interval S w hwInf hwFin hN (X₀ := X₀)
    (ρ := 4 * (RL.ratio 1 (R * finrank K E) (2 * systemEps (finrank K E) δ)
      (systemAbsBound (finrank K E) 2))⁻¹) (NS := 2)
    (NI := subspaceChainLength 1 (R * finrank K E) (2 * systemEps (finrank K E) δ)
      (systemAbsBound (finrank K E) 2))
    ((le_max_right _ _).trans hX₀T) ((le_max_left _ _).trans hX₀T) fun c' hcw hcA _ _ ↦ by
      rw [hcard] at hcA
      obtain ⟨T, hTcard, hTtop, hint⟩ :=
        exists_forall_mem_interval_approxDomain_two (K := E) RL hcard
          (linearIndependent_conjSystem_infinitePlace hwInf hLI)
          (fun V hV ↦ linearIndependent_conjSystem_systemPlacesOver hwFin hLF hV) hε0 hcw hcA hsE
      obtain ⟨𝒯, h𝒯card, h𝒯ge, hQint⟩ := hint X₀ hX₀P
      exact ⟨T, hTcard, hTtop, 𝒯, h𝒯card, h𝒯ge, hQint⟩
  exact h

end BB13
