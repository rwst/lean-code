/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CITED.AdamczewskiFaverjonTheoreme21
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# [AF17] Théorème 1.7 (i) and Corollaire 1.8, with the lifting theorem discharged

plan-formalize-AF17's **WP20**, the closing move of Stage 2.

Stage 1 ran §4 of [AF17] over the axiom `AF.lifting_regular` — Théorème 1.4 in degree one, the
lifting of a linear relation at a regular point.  Stage 2 proves it: `AF.theoreme_2_1`.  This file
is the join, and it exists only because of an import direction.

## Why these three theorems moved

`CITED/AdamczewskiFaverjonProof.lean` is at the *bottom* of the §2 chain — every file of Stage 2
imports it, for the dictionary `AF.IsSumOnBall` and for Lemme 4.2's doubling construction — so it
cannot see `AF.theoreme_2_1`, which is at the top.  The three theorems whose proofs use the lifting
theorem therefore live here instead: nothing about them changed except that the one step which was
an axiom is now a citation of Stage 2.

Their footprint is `std3` together with the **two** cited axioms of Stage 2, `AF.lemme_2_2`
([AF17] Lemme 2.2, the regularity of the solution field) and `AF.lemma_2_8` ([AF22] Lemma 2.8, the
existence of an analytic branch of the relation matrix).  Neither is [AF17] Théorème 1.4.

## Contents

* **`AF.theoreme_1_7_i`** — [AF17] Théorème 1.7 (i), by the paper's first proof (§4);
* **`AF.corollaire_1_8`** — the Mahler alternative at an algebraic point;
* **`AF.corollaire_1_8_rat`** — its rational specialization, the shape `RB/` consumes.

## References

* [AF17] B. Adamczewski, C. Faverjon. *Méthode de Mahler: relations linéaires, transcendance et
  applications aux nombres automatiques.* Proc. London Math. Soc. **115** (2017), 55–90
  (arXiv:1508.07158v2), Thm 1.7 and Cor 1.8 p. 5, §4 pp. 16–22.
* [AF22] B. Adamczewski, C. Faverjon. *A new proof of Nishioka's theorem in Mahler's method.*
  arXiv:2210.14528 (2022), §2.
* [AF17f] `plans/plan-formalize-AF17.html`: WP20, gap (6) of Stage 2, milestone M4.
-/

namespace AF

open Polynomial

/-! ## [AF17] Théorème 1.7 (i), by the route of §4 -/

section Main

variable {k L : Type*} [Field k] [Field L] [Algebra k L] [Algebra L ℂ] [Algebra k ℂ]
  [IsScalarTower k L ℂ] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **[AF17] Théorème 1.7 (i)** — *«si les nombres `f₁(α),…,fₙ(α)` sont linéairement dépendants sur
`ℚ̄`, alors ils sont linéairement dépendants sur `k`»* — by the paper's **first** proof (§4).

The relation is not merely reproduced over `k`: its *support shrinks or stays put*
(`∀ i, lam i = 0 → mu i = 0`) and the chosen index `i₀` still carries a nonzero coefficient.  That
is exactly what [AF17] prove — the descent of Lemme 4.3 is applied with `I = {i : λᵢ = 0}` — and it
is what makes Corollaire 1.8 a two-line consequence: a relation between `f(α)` and `1` alone stays
a relation between `f(α)` and `1` alone.

Reading the proof: Lemme 4.1 is invisible (`AF.lemme_4_1_of_polynomial`: the matrix is already
polynomial), `AF.lemme_4_2` doubles the system until `α` is regular, the axiom lifts the relation
to `L[z]` there, the bridge `AF.relation_formal_of_functional` turns the lifted identity of
functions into an identity of power series, `AF.lemme_4_3` descends its coefficients to `k[z]`, and
evaluating at `α` gives the relation over `k`.  [AF17] Théorème 1.10 — the analytic
desingularization of §5 — is never used.

Note that `k` is **not** required to be a number field: the descent uses one `k`-linear functional
and no finiteness. -/
@[category research solved, AMS 11 12 39, ref "AF17" "AF17f", group "af_mahler_alternative"]
theorem theoreme_1_7_i {q : ℕ} (hq : 2 ≤ q) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hLalg : ∀ x : L, IsAlgebraic ℚ (algebraMap L ℂ x))
    {A : Matrix ι ι (Polynomial L)} (hA : A.det ≠ 0)
    {F : ι → ℂ → ℂ} (hF : IsMahlerSolution q A F (Metric.ball 0 r))
    {f : ι → PowerSeries k} (hf : ∀ i, IsSumOnBall r (f i) (F i))
    {α : k} (hα0 : α ≠ 0) (hα : ‖algebraMap k ℂ α‖ < r)
    {lam : ι → L} {i₀ : ι} (hlam : lam i₀ ≠ 0)
    (hrel : ∑ i, algebraMap L ℂ (lam i) * F i (algebraMap k ℂ α) = 0) :
    ∃ mu : ι → k, mu i₀ ≠ 0 ∧ (∀ i, lam i = 0 → mu i = 0) ∧
      ∑ i, algebraMap k ℂ (mu i) * F i (algebraMap k ℂ α) = 0 := by
  classical
  set a : ℂ := algebraMap k ℂ α with ha
  have haL : a = algebraMap L ℂ (algebraMap k L α) := by
    rw [ha, IsScalarTower.algebraMap_apply k L ℂ]
  have ha0 : a ≠ 0 := by
    rw [ha]
    exact fun h => hα0 ((algebraMap k ℂ).injective (by simpa using h))
  have hstab : ∀ z : ℂ, ‖z‖ < r → ‖z ^ q‖ < r := by
    intro z hz
    rw [norm_pow]
    calc ‖z‖ ^ q ≤ ‖z‖ ^ 1 :=
          pow_le_pow_of_le_one (norm_nonneg z) (le_trans hz.le hr1) (by omega)
      _ = ‖z‖ := pow_one _
      _ < r := hz
  have hS : ∀ z ∈ Metric.ball (0 : ℂ) r, z ^ q ∈ Metric.ball (0 : ℂ) r := by
    intro z hz
    simp only [Metric.mem_ball, dist_zero_right] at hz ⊢
    exact hstab z hz
  have hinj : Function.Injective fun l : ℕ => a ^ q ^ l :=
    injective_pow_pow_of_norm_lt_one ha0 (lt_of_lt_of_le hα hr1) hq
  -- Lemme 4.2: double the system until `α` is a regular point
  obtain ⟨j, hFj, hregj, hembj⟩ := lemme_4_2 hS hF hA hinj
  have hserj : ∀ x, IsSumOnBall (𝕜 := ℂ) r (dblIterSer q f j x) (dblIterSol q F j x) :=
    isSumOnBall_dblIterSer (by omega) hstab hf j
  have hserjL : ∀ x, IsSumOnBall (𝕜 := ℂ) r
      ((dblIterSer q f j x).map (algebraMap k L)) (dblIterSol q F j x) :=
    fun x => (hserj x).mapCoeff
  have hdetj : (dblIterMat q A j).det ≠ 0 := fun h => hregj 0 (by rw [h]; simp)
  have hLamrel : ∑ x, algebraMap L ℂ (dblExt lam j x) * dblIterSol q F j x a = 0 := by
    rw [sum_dblIdx j _ fun x hx => by rw [dblExt_eq_zero lam j x hx]; simp]
    simpa only [dblExt_dblEmb, dblIterSol_dblEmb] using hrel
  -- the lifting theorem at the regular point
  obtain ⟨w, hwfun, hweval⟩ :=
    theoreme_2_1 hq hr0 hr1 hLalg hdetj hFj hserjL
      (α := algebraMap k L α)
      (fun h => hα0 ((algebraMap k L).injective (by simpa using h)))
      (by rw [← haL]; exact hα) (by rw [← haL]; exact hregj) (by rw [← haL]; exact hLamrel)
  -- the bridge, then Lemme 4.3
  have hformal : ∑ x, (w x : PowerSeries L) * ((dblIterSer q f j x).map (algebraMap k L)) = 0 :=
    relation_formal_of_functional hr0 hserjL w hwfun
  obtain ⟨w', hw'rel, hw'I, hw'0⟩ :=
    lemme_4_3 (fun x => dblIterSer q f j x) α w hformal {x | dblExt lam j x = 0}
      (fun x hx => by rw [hweval x]; exact hx)
      (i₀ := dblEmb ι j i₀) (by rw [hweval, dblExt_dblEmb]; exact hlam)
  -- evaluate at `α` and read off the original indices
  have heval : ∑ x, aeval a (w' x) * dblIterSol q F j x a = 0 :=
    eval_of_relation_formal hserj w' hw'rel hα
  have hvanish : ∀ x : dblIdx ι j, (∀ i, x ≠ dblEmb ι j i) →
      aeval a (w' x) * dblIterSol q F j x a = 0 := by
    intro x hx
    have hx0 : dblExt lam j x = 0 := dblExt_eq_zero lam j x hx
    rw [ha, aeval_algebraMap_eq, hw'I x hx0, map_zero, zero_mul]
  rw [sum_dblIdx j _ hvanish] at heval
  refine ⟨fun i => (w' (dblEmb ι j i)).eval α, hw'0, fun i hi => ?_, ?_⟩
  · refine hw'I _ ?_
    simp only [Set.mem_ofPred_eq, dblExt_dblEmb]
    exact hi
  · simpa only [ha, aeval_algebraMap_eq, dblIterSol_dblEmb] using heval

/-- **[AF17] Corollaire 1.8** — the Mahler alternative at an algebraic point: for `f` a coordinate
of a `q`-Mahler system and `α` a point of the disc of convergence with `0 < |α| < 1`, the value
`f(α)` is **transcendental over `k`, or lies in `k`**.

*«Soient `f(z)` une fonction `q`-mahlérienne et `α ∈ ℚ̄`, `0 < |α| < 1`, qui n'est pas un pôle de
`f`. Soit `k` un corps de nombres contenant `α` ainsi que les coefficients de `f`. On a
l'alternative suivante : soit `f(α)` est transcendant, soit `f(α) ∈ k`.»*

**Both branches are real** — [AF17] §8.1 exhibits a `3`-automatic series with `f` transcendental
over `ℚ(z)` and `f(φ) = −φ/2 ∈ ℚ(φ)` — so this must not be read as a transcendence statement; see
the module doc of `CITED/AdamczewskiFaverjon.lean`.

`hLfull` says that the field `L` of the lifting theorem is large enough to contain the value under
test; `AF.corollaire_1_8_rat` discharges it, and `hLalg`, by taking `L` to be the field of
algebraic numbers inside `ℂ`. -/
@[category research solved, AMS 11 12 39, ref "AF17" "AF17f", group "af_mahler_alternative"]
theorem corollaire_1_8 {q : ℕ} (hq : 2 ≤ q) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hLalg : ∀ x : L, IsAlgebraic ℚ (algebraMap L ℂ x))
    (hLfull : ∀ x : ℂ, IsAlgebraic k x → ∃ β : L, algebraMap L ℂ β = x)
    {A : Matrix ι ι (Polynomial L)} (hA : A.det ≠ 0)
    {F : ι → ℂ → ℂ} (hF : IsMahlerSolution q A F (Metric.ball 0 r))
    {f : ι → PowerSeries k} (hf : ∀ i, IsSumOnBall r (f i) (F i))
    {α : k} (hα0 : α ≠ 0) (hα : ‖algebraMap k ℂ α‖ < r) (i₀ : ι) :
    Transcendental k (F i₀ (algebraMap k ℂ α)) ∨
      ∃ c : k, F i₀ (algebraMap k ℂ α) = algebraMap k ℂ c := by
  classical
  by_cases hc : IsAlgebraic k (F i₀ (algebraMap k ℂ α))
  swap
  · exact Or.inl hc
  right
  obtain ⟨β, hβ⟩ := hLfull _ hc
  set a : ℂ := algebraMap k ℂ α with ha
  set F' : ι ⊕ Unit → ℂ → ℂ := Sum.elim F fun _ _ => 1 with hF'def
  set f' : ι ⊕ Unit → PowerSeries k := Sum.elim f fun _ => 1 with hf'def
  set lam : ι ⊕ Unit → L := Sum.elim (fun i => if i = i₀ then 1 else 0) fun _ => -β with hlamdef
  have hf' : ∀ x, IsSumOnBall r (f' x) (F' x) := by
    intro x
    cases x with
    | inl i => exact hf i
    | inr u => exact isSumOnBall_one r
  have hrel : ∑ x, algebraMap L ℂ (lam x) * F' x a = 0 := by
    rw [Fintype.sum_sum_type]
    have h1 : ∑ i, algebraMap L ℂ (lam (Sum.inl i)) * F' (Sum.inl i) a = F i₀ a := by
      rw [Finset.sum_eq_single i₀]
      · simp [hlamdef, hF'def]
      · intro i _ hi; simp [hlamdef, hi]
      · intro h; exact absurd (Finset.mem_univ i₀) h
    rw [h1]
    simp [hlamdef, hF'def, hβ]
  obtain ⟨mu, hmu0, hmusupp, hmurel⟩ :=
    theoreme_1_7_i (A := adjoinOne A) (F := F') (f := f') (lam := lam) (i₀ := Sum.inl i₀)
      hq hr0 hr1 hLalg (by rw [det_adjoinOne]; exact hA)
      (by rw [hF'def]; exact isMahlerSolution_adjoinOne hF) hf' hα0 hα (by simp [hlamdef]) hrel
  have hsum : algebraMap k ℂ (mu (Sum.inl i₀)) * F i₀ a + algebraMap k ℂ (mu (Sum.inr ())) = 0 := by
    rw [Fintype.sum_sum_type] at hmurel
    have h1 : ∑ i, algebraMap k ℂ (mu (Sum.inl i)) * F' (Sum.inl i) a
        = algebraMap k ℂ (mu (Sum.inl i₀)) * F i₀ a := by
      rw [Finset.sum_eq_single i₀]
      · simp [hF'def]
      · intro i _ hi
        rw [hmusupp (Sum.inl i) (by simp [hlamdef, hi]), map_zero, zero_mul]
      · intro h; exact absurd (Finset.mem_univ i₀) h
    rw [h1] at hmurel
    simpa [hF'def] using hmurel
  have hc1 : algebraMap k ℂ (mu (Sum.inl i₀)) ≠ 0 :=
    fun h => hmu0 ((algebraMap k ℂ).injective (by simpa using h))
  refine ⟨-mu (Sum.inr ()) / mu (Sum.inl i₀), ?_⟩
  rw [map_div₀, map_neg, eq_div_iff hc1]
  linear_combination hsum
end Main

/-! ## The rational specialization -/

/-- **[AF17] Corollaire 1.8 over `ℚ`**: for a Mahler system with **rational** matrix and rational
coefficient series, converging on a disc of radius `r ≤ 1`, the value at a nonzero rational point
of that disc is transcendental or rational.

This is the shape the corpus consumes (`AF.transcendental_or_rat_of_automatic`), with the field
`L` of `AF.theoreme_2_1` instantiated at the field `algebraicClosure ℚ ℂ` of algebraic numbers,
which discharges both side conditions of `AF.corollaire_1_8` by definition. -/
@[category research solved, AMS 11 12 39, ref "AF17" "AF17f", group "af_mahler_alternative"]
theorem corollaire_1_8_rat {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ} (hq : 2 ≤ q)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    {A : Matrix ι ι (Polynomial ℚ)} (hA : A.det ≠ 0)
    {F : ι → ℂ → ℂ} (hF : IsMahlerSolution q A F (Metric.ball 0 r))
    {f : ι → PowerSeries ℚ} (hf : ∀ i, IsSumOnBall r (f i) (F i))
    {α : ℚ} (hα0 : α ≠ 0) (hα : ‖(α : ℂ)‖ < r) (i₀ : ι) :
    Transcendental ℚ (F i₀ (α : ℂ)) ∨ ∃ c : ℚ, F i₀ (α : ℂ) = (c : ℂ) := by
  have hcast : ∀ x : ℚ, algebraMap ℚ ℂ x = (x : ℂ) := fun x => eq_ratCast (algebraMap ℚ ℂ) x
  have hmain := corollaire_1_8 (k := ℚ) (L := ↥(algebraicClosure ℚ ℂ)) (ι := ι) hq hr0 hr1
      (fun x => mem_algebraicClosure_iff.mp x.2)
      (fun x hx => ⟨⟨x, mem_algebraicClosure_iff.mpr hx⟩, rfl⟩)
      (A := A.map (Polynomial.map (algebraMap ℚ ↥(algebraicClosure ℚ ℂ))))
      (det_mapCoeff_ne_zero hA) hF.mapCoeff hf hα0 (by rw [hcast]; exact hα) i₀
  simpa only [hcast] using hmain

end AF
