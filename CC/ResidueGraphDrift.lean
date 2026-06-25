/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CC.SRSBridge
import Mathlib.Data.Finset.Lattice.Fold
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The λ(G_R) drift dictionary (Report B3 item 6, step 2) (Ter76; YAH; Kar78)

**Report B3, item 6, concrete step 2:** the residue transition graph `G_R`, read in the two
semirings, gives two quantities that must agree in sign:

* **Tropical `(max, +)` side.** The **maximum cycle mean** `λ(G_R)` — the largest mean edge-weight
  over the cycles of `G_R` ([YAH], [Kar78]). A certificate (uniform contraction potential) exists iff
  `λ(G_R) < 0`.
* **Density / Markov `(+, ×)` side.** A **stationary distribution** on `G_R` and its **drift**, the
  expected weight per step. The Terras–Lagarias program shows the drift is negative for the natural
  stationary measure ([Ter76]).

The **dictionary theorem** is the max-plus / linear-programming duality between them:

> `λ(G_R) < 0  ⟺  every stationary distribution on G_R has negative drift`
> (`lam_neg_iff_drift_neg`),

because `λ(G_R) = max over stationary distributions of the drift` (`drift_le_lam` +
`exists_drift_eq_lam`): the drift is a convex average of cycle means, maximised at a single cycle.
We model the invariant measures of `G_R` by their **extreme points, the cycles** — flow
decomposition: every conservative non-negative edge-measure is a non-negative combination of cycle
measures, so a stationary distribution is a probability distribution over cycles (`StatDist`).

Specialised to the Collatz residue graph (edge weight `log 3 − (1+j)·log 2`, here per Terras step
`stepWeight u = log 3·[u odd] − log 2`), a cycle's mean is `oddFraction · log 3 − log 2`, so it is
negative iff the cycle's odd-step fraction is below the **critical ratio**
`log 2 / log 3 = SRSBridge.criticalRatio` (`cycleMean_residue_neg_iff`). Hence

> `(all stationary drifts < 0)  ⟺  (every cycle of G_R is sub-critical)` (`residue_drift_dictionary`),

the explicit density ↔ certificate dictionary on the same residue graph, joined to the per-orbit
threshold of [[cc-srsbridge-item6]].

## Contents
* `StatDist`, `lam`, `drift` — stationary distributions over a finite cycle family, the maximum cycle
  mean `λ`, and the drift.
* `drift_le_lam`, `exists_drift_eq_lam` — `λ = max stationary drift` (LP duality).
* **`lam_neg_iff_drift_neg`** — the abstract dictionary: `λ < 0 ⟺ all drifts < 0`.
* `Cycle`, `cycleMean`; `stepWeight`, `cycleMean_residue`, `cycleMean_residue_neg_iff` — the Collatz
  residue graph and its cycle means versus `criticalRatio`.
* **`residue_drift_dictionary`** — the dictionary on `G_R`: all stationary drifts negative iff every
  cycle is sub-critical.

## References
* [Ter76] Terras. *A stopping time problem on the positive integers.* Acta Arith. 30 (1976), 241–252.
* [YAH] Yolcu, Aaronson, Heule. *An Automated Approach to the Collatz Conjecture.* arXiv:2105.14697.
* [Kar78] Karp. *A characterization of the minimum cycle mean in a digraph.* Discrete Math. 23 (1978).
-/

namespace CC.ResidueGraphDrift

open CC
open scoped Classical

/-! ### Abstract duality: maximum cycle mean = maximum stationary drift -/

variable {ι : Type*}

/-- A **stationary distribution** supported on a finite cycle family `𝒞`: non-negative weights `p`,
supported on `𝒞`, summing to one. (By flow decomposition these are exactly the invariant
edge-measures of the graph, written in the cycle basis.) -/
@[category API, AMS 37 90, ref "Kar78", group "two_semiring_bridge"]
structure StatDist (𝒞 : Finset ι) where
  /-- The probability weight on each cycle. -/
  p : ι → ℝ
  /-- Weights are non-negative. -/
  nonneg : ∀ i, 0 ≤ p i
  /-- Weights are supported on `𝒞`. -/
  supported : ∀ i, p i ≠ 0 → i ∈ 𝒞
  /-- Weights sum to one. -/
  sum_one : ∑ i ∈ 𝒞, p i = 1

/-- The **maximum cycle mean** `λ(G_R) = max_{C} mean(C)` over the finite cycle family `𝒞`. -/
@[category API, AMS 37 90, ref "YAH" "Kar78", group "two_semiring_bridge"]
noncomputable def lam (𝒞 : Finset ι) (h : 𝒞.Nonempty) (mean : ι → ℝ) : ℝ := 𝒞.sup' h mean

/-- The **drift** of a stationary distribution: the expected cycle mean `∑_C p(C)·mean(C)`. -/
@[category API, AMS 37 90, ref "Ter76", group "two_semiring_bridge"]
noncomputable def drift (𝒞 : Finset ι) (mean : ι → ℝ) (μ : StatDist 𝒞) : ℝ :=
  ∑ i ∈ 𝒞, μ.p i * mean i

/-- The **point mass** on a single cycle `i₀ ∈ 𝒞`: a stationary distribution. -/
@[category API, AMS 37 90, ref "Kar78", group "two_semiring_bridge"]
noncomputable def pointMass {𝒞 : Finset ι} {i₀ : ι} (h : i₀ ∈ 𝒞) : StatDist 𝒞 where
  p := fun i => if i = i₀ then 1 else 0
  nonneg := fun i => by by_cases hi : i = i₀ <;> simp [hi]
  supported := fun i hi => by by_cases hi' : i = i₀ <;> simp_all
  sum_one := by simp [Finset.sum_ite_eq', h]

/-- The drift of the point mass on `i₀` is `mean i₀`. -/
@[category API, AMS 37 90, ref "Kar78", group "two_semiring_bridge"]
theorem drift_pointMass {𝒞 : Finset ι} {i₀ : ι} (h : i₀ ∈ 𝒞) (mean : ι → ℝ) :
    drift 𝒞 mean (pointMass h) = mean i₀ := by
  show ∑ i ∈ 𝒞, (if i = i₀ then (1 : ℝ) else 0) * mean i = mean i₀
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' 𝒞 i₀ mean, if_pos h]

/-- **Every stationary drift is at most `λ`**: the drift is a convex average of cycle means, so it
cannot exceed the maximum cycle mean (one half of the LP duality). -/
@[category research solved, AMS 37 90, ref "YAH" "Kar78", group "two_semiring_bridge",
  formal_uses lam drift]
theorem drift_le_lam (𝒞 : Finset ι) (h : 𝒞.Nonempty) (mean : ι → ℝ) (μ : StatDist 𝒞) :
    drift 𝒞 mean μ ≤ lam 𝒞 h mean := by
  calc drift 𝒞 mean μ
      = ∑ i ∈ 𝒞, μ.p i * mean i := rfl
    _ ≤ ∑ i ∈ 𝒞, μ.p i * lam 𝒞 h mean :=
        Finset.sum_le_sum fun i hi =>
          mul_le_mul_of_nonneg_left (Finset.le_sup' mean hi) (μ.nonneg i)
    _ = (∑ i ∈ 𝒞, μ.p i) * lam 𝒞 h mean := by rw [← Finset.sum_mul]
    _ = lam 𝒞 h mean := by rw [μ.sum_one, one_mul]

/-- **`λ` is attained by a stationary distribution** (the point mass on a maximising cycle): the other
half of the LP duality, `λ = max stationary drift`. -/
@[category research solved, AMS 37 90, ref "YAH" "Kar78", group "two_semiring_bridge",
  formal_uses drift_pointMass]
theorem exists_drift_eq_lam (𝒞 : Finset ι) (h : 𝒞.Nonempty) (mean : ι → ℝ) :
    ∃ μ : StatDist 𝒞, drift 𝒞 mean μ = lam 𝒞 h mean := by
  obtain ⟨i₀, hi₀, hsup⟩ := Finset.exists_mem_eq_sup' h mean
  exact ⟨pointMass hi₀, by rw [drift_pointMass hi₀, lam]; exact hsup.symm⟩

/-- **The drift dictionary.** The maximum cycle mean is negative iff *every* stationary distribution
has negative drift: `λ(G_R) < 0 ⟺ ∀ μ, drift μ < 0`. -/
@[category research solved, AMS 37 90, ref "Ter76" "YAH" "Kar78", group "two_semiring_bridge",
  formal_uses drift_le_lam exists_drift_eq_lam]
theorem lam_neg_iff_drift_neg (𝒞 : Finset ι) (h : 𝒞.Nonempty) (mean : ι → ℝ) :
    lam 𝒞 h mean < 0 ↔ ∀ μ : StatDist 𝒞, drift 𝒞 mean μ < 0 := by
  constructor
  · intro hlam μ
    exact lt_of_le_of_lt (drift_le_lam 𝒞 h mean μ) hlam
  · intro hdrift
    obtain ⟨μ, hμ⟩ := exists_drift_eq_lam 𝒞 h mean
    rw [← hμ]; exact hdrift μ

/-! ### The Collatz residue graph and its cycle means -/

/-- A **cycle** (closed walk) in a digraph on `V`: a positive length and a vertex at each position,
the successor taken cyclically. -/
@[category API, AMS 11 37, ref "YAH", group "two_semiring_bridge"]
structure Cycle (V : Type*) where
  /-- The length of the cycle. -/
  len : ℕ
  /-- The length is positive. -/
  pos : 0 < len
  /-- The vertex at each position. -/
  vert : Fin len → V

/-- The cyclic successor index. -/
@[category API, AMS 11 37, ref "YAH", group "two_semiring_bridge"]
def cycleNext {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n := ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩

/-- The total edge weight around a cycle. -/
@[category API, AMS 11 37, ref "YAH", group "two_semiring_bridge"]
noncomputable def cycleWeight {V : Type*} (w : V → V → ℝ) (c : Cycle V) : ℝ :=
  ∑ i : Fin c.len, w (c.vert i) (c.vert (cycleNext c.pos i))

/-- The **mean** edge weight around a cycle: total weight divided by length. -/
@[category API, AMS 11 37, ref "YAH" "Kar78", group "two_semiring_bridge"]
noncomputable def cycleMean {V : Type*} (w : V → V → ℝ) (c : Cycle V) : ℝ :=
  cycleWeight w c / c.len

/-- The **Terras per-step weight** at residue `u`: `log 3 − log 2` on an odd step (a tripling and a
halving) and `−log 2` on an even step (a halving). The `(max, +)` edge weight of `G_R`. -/
@[category API, AMS 11 37, ref "Ter76" "YAH", group "two_semiring_bridge"]
noncomputable def stepWeight (u : ℕ) : ℝ :=
  if u % 2 = 1 then Real.log 3 - Real.log 2 else -Real.log 2

/-- The step weight written with the parity indicator: `stepWeight u = [u odd]·log 3 − log 2`. -/
@[category API, AMS 11 37, ref "Ter76", group "two_semiring_bridge"]
theorem stepWeight_eq (u : ℕ) :
    stepWeight u = (if u % 2 = 1 then (1 : ℝ) else 0) * Real.log 3 - Real.log 2 := by
  unfold stepWeight; split <;> ring

/-- The residue-graph edge weight: depends only on the source residue's parity. -/
@[category API, AMS 11 37, ref "Ter76" "YAH", group "two_semiring_bridge"]
noncomputable def residueW (u _v : ℕ) : ℝ := stepWeight u

/-- The number of odd residues visited around a cycle (its odd-step count). -/
@[category API, AMS 11 37, ref "Ter76", group "two_semiring_bridge"]
noncomputable def oddCount (c : Cycle ℕ) : ℝ :=
  ∑ i : Fin c.len, (if (c.vert i) % 2 = 1 then (1 : ℝ) else 0)

/-- The total weight of a residue cycle is `oddCount·log 3 − len·log 2`. -/
@[category research solved, AMS 11 37, ref "Ter76" "YAH", group "two_semiring_bridge",
  formal_uses stepWeight_eq]
theorem cycleWeight_residue (c : Cycle ℕ) :
    cycleWeight residueW c = oddCount c * Real.log 3 - (c.len : ℝ) * Real.log 2 := by
  unfold cycleWeight residueW oddCount
  simp_rw [stepWeight_eq]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-- The mean of a residue cycle is `oddFraction·log 3 − log 2`. -/
@[category research solved, AMS 11 37, ref "Ter76" "YAH", group "two_semiring_bridge",
  formal_uses cycleWeight_residue]
theorem cycleMean_residue (c : Cycle ℕ) :
    cycleMean residueW c = oddCount c / (c.len : ℝ) * Real.log 3 - Real.log 2 := by
  have hlen : (c.len : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr c.pos.ne'
  unfold cycleMean
  rw [cycleWeight_residue]
  field_simp

/-- A real-number threshold lemma: `r·log 3 − log 2 < 0 ⟺ r < log 2 / log 3`. -/
@[category API, AMS 11 37, ref "Ter76", group "two_semiring_bridge"]
theorem ratio_threshold (r : ℝ) :
    r * Real.log 3 - Real.log 2 < 0 ↔ r < SRSBridge.criticalRatio := by
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  rw [SRSBridge.criticalRatio, sub_lt_zero, lt_div_iff₀ hlog3]

/-- A residue cycle is **contracting** (`cycleMean < 0`) iff its odd-step fraction is below the
critical ratio `log 2 / log 3` of the two-semiring bridge — the cycle-level analogue of
`SRSBridge.tropWeight_neg_iff_ratio`. -/
@[category research solved, AMS 11 37, ref "Ter76" "YAH", group "two_semiring_bridge",
  formal_uses cycleMean_residue ratio_threshold]
theorem cycleMean_residue_neg_iff (c : Cycle ℕ) :
    cycleMean residueW c < 0 ↔ oddCount c / (c.len : ℝ) < SRSBridge.criticalRatio := by
  rw [cycleMean_residue]; exact ratio_threshold _

/-- **The drift dictionary on the Collatz residue graph.** Every stationary distribution on `G_R`
has negative drift iff every cycle of `G_R` is sub-critical (odd-step fraction below `log 2/log 3`).
Both are equivalent to `λ(G_R) < 0`: the density program (negative drift everywhere) and the
certificate program (no non-contracting cycle) coincide on the residue graph. -/
@[category research solved, AMS 11 90, ref "Ter76" "YAH" "Kar78", group "two_semiring_bridge",
  formal_uses lam_neg_iff_drift_neg cycleMean_residue_neg_iff]
theorem residue_drift_dictionary {𝒞 : Finset (Cycle ℕ)} (h : 𝒞.Nonempty) :
    (∀ μ : StatDist 𝒞, drift 𝒞 (cycleMean residueW) μ < 0)
      ↔ ∀ c ∈ 𝒞, oddCount c / (c.len : ℝ) < SRSBridge.criticalRatio := by
  rw [← lam_neg_iff_drift_neg 𝒞 h (cycleMean residueW), lam, Finset.sup'_lt_iff]
  simp_rw [cycleMean_residue_neg_iff]

end CC.ResidueGraphDrift
