/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import RB.MahlerAnalytic
import RB.MahlerNonsingular
import CITED.AdamczewskiFaverjonTheoreme17
import Mathlib.RingTheory.Algebraic.Basic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The value of an automatic power series at a rational point (plan-formalize-AF17, WP5)

The wiring that turns `AF.corollaire_1_8_rat` — [AF17] Corollaire 1.8, proved in
`CITED/AdamczewskiFaverjonTheoreme17.lean` over the two cited axioms of [AF22] §2 — into the
statement the corpus actually consumes.

## Contents

* `RB.self_mem_kKernel`, `RB.isKernelModel_kKernel` — the canonical kernel model.
* `RB.isSumOnBall_genSeries` — the series/function dictionary at the corpus's own objects.
* `RB.isMahlerSolution_of_formal` — the analytic system from the formal one.
* `RB.genFun_ofReal` — the real value, read in `ℂ`.
* **`RB.transcendental_or_rat_of_automatic`** — the theorem.

## References

* [AF17] B. Adamczewski, C. Faverjon. *Méthode de Mahler: relations linéaires, transcendance et
  applications aux nombres automatiques.* Proc. London Math. Soc. **115** (2017), 55–90.
* [Ran92] B. Randé. *Équations fonctionnelles de Mahler et applications aux suites
  `p`-régulières.* Thèse, Université Bordeaux I, 1992.
* [AS03] J.-P. Allouche, J. Shallit. *Automatic Sequences.* CUP 2003.
* [AF17f] `plans/plan-formalize-AF17.html`: WP5, milestone M2.
-/

namespace RB

open AS Polynomial

/-! ## The canonical kernel model -/

/-- A sequence lies in its own `k`-kernel, at `i = r = 0`. -/
@[category API, AMS 11 68, ref "AS03", group "rb_automatic_value"]
theorem self_mem_kKernel (k : ℕ) (a : ℕ → ℕ) : a ∈ kKernel k a :=
  ⟨0, 0, by simp, by funext n; simp⟩

/-- **The canonical kernel model** ([AS03] Thm 6.6.2): the `k`-kernel indexes itself, `φ` being
the inclusion and `σ` the decimation `RB.kernelMap`.

`RB/MahlerExamples.lean` builds kernel models by hand for Thue–Morse, the Cantor sequence and the
parity sequence; this is the one that exists for *every* sequence, and it is what makes the
hypothesis `AS.IsAutomatic a` — a bare finiteness statement — usable as input to the Mahler
machinery. -/
@[category research solved, AMS 11 68, ref "AS03" "AF17f", group "rb_automatic_value"]
theorem isKernelModel_kKernel (k : ℕ) (a : ℕ → ℕ) :
    IsKernelModel k a (Subtype.val : ↥(kKernel k a) → ℕ → ℕ) (kernelMap k a) :=
  ⟨Subtype.val_injective, Subtype.range_coe, fun _ _ _ => rfl⟩

/-! ## The corpus's objects in [AF17]'s vocabulary -/

section Wiring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The dictionary at the corpus's own objects** ([AF17f] WP5 step (iii)): the formal series
`RB.genSeries s` over `ℚ` sums, on the open unit disc of `ℂ`, to the generating function
`RB.genFun s`.

Both sides are the corpus's, not [AF17]'s: `genSeries` is the coefficient-wise object that
`RB/MahlerNonsingular.lean`'s repair theorem manipulates, `genFun` the analytic object that
`RB/MahlerAnalytic.lean` proves analytic on the disc.  `AF.IsSumOnBall` is the predicate that
ties them, and this lemma is the only place the tie is made. -/
@[category research solved, AMS 11 30 40, ref "AF17" "AF17f", group "rb_automatic_value"]
theorem isSumOnBall_genSeries {s : ℕ → ℕ} {B : ℕ} (hbdd : ∀ n, s n ≤ B) :
    AF.IsSumOnBall (K := ℚ) (𝕜 := ℂ) 1 (genSeries s) (genFun s) := by
  intro z hz
  have hcoef : (fun n => algebraMap ℚ ℂ (PowerSeries.coeff n (genSeries (K := ℚ) s)) * z ^ n)
      = fun n => (s n : ℂ) * z ^ n := by
    funext n
    rw [genSeries, PowerSeries.coeff_mk, map_natCast]
  rw [hcoef]
  exact (summable_natCast_mul_pow hbdd hz).hasSum

omit [Fintype ι] [DecidableEq ι] in
/-- The unit disc is stable under `z ↦ z ^ q`. -/
@[category API, AMS 30 40, ref "AF17", group "rb_automatic_value"]
theorem norm_pow_lt_one {z : ℂ} (hz : ‖z‖ < 1) {q : ℕ} (hq : q ≠ 0) : ‖z ^ q‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg z) hz hq

/-- **From the formal system to the analytic one** ([AF17f] WP5 step (iv)): a linear Mahler
system satisfied by the generating *series* over `ℚ` is satisfied by the generating *functions*
at every point of the open unit disc.

This is the transport the plan calls for, and it is bought by `AF.eval_of_relation_formal` alone:
each row of the system is a linear relation with polynomial coefficients among the series
`genSeries (φ j)` and their substitutions `z ↦ z^k`, and a formal relation may be evaluated
wherever the series converge.  In particular it applies verbatim to the **repaired** matrix of
`RB.exists_nonsingular_mahlerSystem`, whose rows differ from the kernel matrix's by exactly such
a relation — which is why gate G4's repair costs nothing on the analytic side. -/
@[category research solved, AMS 11 12 39, ref "AF17" "AF17f", group "rb_automatic_value"]
theorem isMahlerSolution_of_formal {k : ℕ} (hk0 : k ≠ 0) {φ : ι → ℕ → ℕ} {B : ℕ}
    (hbdd : ∀ i n, φ i n ≤ B) {A : Matrix ι ι (Polynomial ℚ)}
    (hsys : ∀ i, (genSeries (φ i) : PowerSeries ℚ)
      = ∑ j, ((A i j : Polynomial ℚ) : PowerSeries ℚ) *
          PowerSeries.expand k hk0 (genSeries (φ j))) :
    AF.IsMahlerSolution k A (fun i => (genFun (φ i) : ℂ → ℂ)) (Metric.ball 0 1) := by
  classical
  intro z hz i
  rw [Metric.mem_ball, dist_zero_right] at hz
  set f : ι ⊕ ι → PowerSeries ℚ :=
    Sum.elim (fun j => genSeries (φ j)) (fun j => AF.substPowSeries k (genSeries (φ j))) with hfdef
  set H : ι ⊕ ι → ℂ → ℂ :=
    Sum.elim (fun j => genFun (φ j)) (fun j y => genFun (φ j) (y ^ k)) with hHdef
  have hball : ∀ x, AF.IsSumOnBall (K := ℚ) (𝕜 := ℂ) 1 (f x) (H x) := by
    rintro (j | j)
    · exact isSumOnBall_genSeries (hbdd j)
    · exact (isSumOnBall_genSeries (hbdd j)).substPowSeries (Nat.pos_of_ne_zero hk0)
        fun y hy => norm_pow_lt_one hy hk0
  set w : ι ⊕ ι → Polynomial ℚ :=
    Sum.elim (fun j => if j = i then 1 else 0) (fun j => -(A i j)) with hwdef
  have hrel : ∑ x, ((w x : Polynomial ℚ) : PowerSeries ℚ) * f x = 0 := by
    rw [Fintype.sum_sum_type]
    have h1 : ∑ j : ι, ((w (Sum.inl j) : Polynomial ℚ) : PowerSeries ℚ) * f (Sum.inl j)
        = genSeries (φ i) := by
      rw [Finset.sum_eq_single i]
      · simp [hwdef, hfdef]
      · intro b _ hb
        simp [hwdef, hfdef, hb]
      · intro hcon
        exact absurd (Finset.mem_univ _) hcon
    have h2 : ∑ j : ι, ((w (Sum.inr j) : Polynomial ℚ) : PowerSeries ℚ) * f (Sum.inr j)
        = -∑ j : ι, ((A i j : Polynomial ℚ) : PowerSeries ℚ) *
            PowerSeries.expand k hk0 (genSeries (φ j)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hwdef, hfdef, Sum.elim_inr, Polynomial.coe_neg, neg_mul]
      rw [substPowSeries_eq_expand hk0]
    rw [h1, h2, ← sub_eq_add_neg, hsys i, sub_self]
  have heval := AF.eval_of_relation_formal hball w hrel (z := z) hz
  rw [Fintype.sum_sum_type] at heval
  have e1 : ∑ j : ι, aeval z (w (Sum.inl j)) * H (Sum.inl j) z = genFun (φ i) z := by
    rw [Finset.sum_eq_single i]
    · simp [hwdef, hHdef]
    · intro b _ hb
      simp [hwdef, hHdef, hb]
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  have e2 : ∑ j : ι, aeval z (w (Sum.inr j)) * H (Sum.inr j) z
      = -∑ j : ι, aeval z (A i j) * genFun (φ j) (z ^ k) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hwdef, hHdef, Sum.elim_inr, map_neg, neg_mul]
  rw [e1, e2, ← sub_eq_add_neg, sub_eq_zero] at heval
  exact heval

end Wiring

/-! ## The value at a rational point -/

/-- **The real value, read in `ℂ`** ([AF17f] WP5 step (i)): [AF17] Cor 1.8 is a statement about
`ℂ`, the corpus's consumers are statements about `ℝ`, and `RB.genFun` is defined over any normed
field — so the transport is the single cast identity `∑ (aₙ xⁿ : ℝ) = ∑ (aₙ xⁿ : ℂ)`. -/
@[category research solved, AMS 11 30 40, ref "AF17f", group "rb_automatic_value"]
theorem genFun_ofReal (s : ℕ → ℕ) (x : ℝ) :
    genFun s ((x : ℂ)) = ((genFun s x : ℝ) : ℂ) := by
  simp only [genFun]
  rw [Complex.ofReal_tsum]
  exact tsum_congr fun n => by push_cast; ring

set_option linter.unusedVariables false in
/-- **[AF17] Corollaire 1.8, at an automatic sequence** — the statement the corpus consumes, and
until now the cited axiom `AF.transcendental_or_rat_of_automatic`:

*for an automatic sequence `a` with bounded values and a rational `α` with `0 < |α| < 1`, the
value `f(α) = ∑ⱼ aⱼαʲ` is either transcendental over `ℚ`, or rational.*

This is [AF17]'s own named case — Cobham's 1968 conjecture.  **Both disjuncts are real**: [AF17]
§8.1 exhibits a `{0,1}`-valued `3`-automatic sequence with `f` transcendental over `ℚ(z)` and yet
`f₁(φ) = −φ/2 ∈ ℚ(φ)`, so a "collision" argument that reads the corollary as forcing degeneracy
from a *known rational value* is invalid.  The corollary has force only in the contrapositive
direction used by `RB.not_automatic_of_K_algebraic_irrational`: an *algebraic irrational* value is
excluded by **both** branches at once.

Footprint: `std3 + AF.lemme_2_2 + AF.lemma_2_8`.  The three facts that
`CITED/AdamczewskiFaverjon.lean` used to fold into the axiom are all discharged —

* *bounded coefficients ⇒ radius `≥ 1` ⇒ `α` is not a pole*: `RB.analyticAt_genFun` (WP2);
* *automatic ⇒ a `q`-Mahler system with `det A ≠ 0`*: `RB.exists_nonsingular_mahlerSystem`
  (gate G4), on the canonical kernel model `RB.isKernelModel_kKernel`;
* *`k = ℚ`*: `AF.corollaire_1_8_rat`.

`hbdd` is redundant — `AS.exists_bound_of_isAutomatic` derives it from `hauto` — and is kept
only so that the statement matches the retired axiom verbatim, which is what lets the two
consumer files compile unchanged. -/
@[category research solved, AMS 11 68, ref "AF17" "Cob68" "AF17f", group "rb_automatic_value"]
theorem transcendental_or_rat_of_automatic {a : ℕ → ℕ} {B : ℕ}
    (hbdd : ∀ j, a j ≤ B) (hauto : AS.IsAutomatic a)
    {α : ℚ} (hα0 : α ≠ 0) (hα1 : |α| < 1) :
    Transcendental ℚ (∑' j, (a j : ℝ) * (α : ℝ) ^ j) ∨
      ∃ r : ℚ, ∑' j, (a j : ℝ) * (α : ℝ) ^ j = (r : ℝ) := by
  classical
  obtain ⟨k, hk, hfin⟩ := id hauto
  have hk0 : k ≠ 0 := by omega
  have : Fintype ↥(kKernel k a) := hfin.fintype
  obtain ⟨B', hB'⟩ := exists_bound_kKernel (k := k) hauto
  have hbdd' : ∀ (i : ↥(kKernel k a)) (n : ℕ), (i : ℕ → ℕ) n ≤ B' := fun i n => hB' i.val i.2 n
  obtain ⟨A, hdet, hsys⟩ :=
    exists_nonsingular_mahlerSystem (K := ℚ) hk (isKernelModel_kKernel k a)
  have hF : AF.IsMahlerSolution k A
      (fun i : ↥(kKernel k a) => (genFun (i : ℕ → ℕ) : ℂ → ℂ)) (Metric.ball 0 1) :=
    isMahlerSolution_of_formal hk0 hbdd' hsys
  have hf : ∀ i : ↥(kKernel k a),
      AF.IsSumOnBall (K := ℚ) (𝕜 := ℂ) 1 (genSeries (i : ℕ → ℕ)) (genFun (i : ℕ → ℕ)) :=
    fun i => isSumOnBall_genSeries (hbdd' i)
  have hαnorm : ‖((α : ℚ) : ℂ)‖ < 1 := by
    rw [Complex.norm_ratCast]
    exact_mod_cast hα1
  have hmem : a ∈ kKernel k a := self_mem_kKernel k a
  have hval : genFun ((⟨a, hmem⟩ : ↥(kKernel k a)) : ℕ → ℕ) (((α : ℚ) : ℂ))
      = ((∑' j, (a j : ℝ) * ((α : ℚ) : ℝ) ^ j : ℝ) : ℂ) := by
    have hc : ((((α : ℚ) : ℝ)) : ℂ) = ((α : ℚ) : ℂ) := by push_cast; ring
    calc genFun ((⟨a, hmem⟩ : ↥(kKernel k a)) : ℕ → ℕ) (((α : ℚ) : ℂ))
        = genFun a (((((α : ℚ) : ℝ)) : ℂ)) := by rw [hc]
      _ = ((genFun a ((α : ℚ) : ℝ) : ℝ) : ℂ) := genFun_ofReal a _
      _ = _ := rfl
  rcases AF.corollaire_1_8_rat hk one_pos le_rfl hdet hF hf hα0 hαnorm ⟨a, hmem⟩ with h | ⟨c, hc⟩
  · left
    refine (transcendental_algebraMap_iff (R := ℚ) (S := ℝ) (A := ℂ)
      (algebraMap ℝ ℂ).injective).mp ?_
    have hcast : algebraMap ℝ ℂ (∑' j, (a j : ℝ) * ((α : ℚ) : ℝ) ^ j)
        = genFun ((⟨a, hmem⟩ : ↥(kKernel k a)) : ℕ → ℕ) (((α : ℚ) : ℂ)) := by
      rw [hval]
      rfl
    rw [hcast]
    exact h
  · right
    exact ⟨c, by exact_mod_cast hval.symm.trans hc⟩

end RB
