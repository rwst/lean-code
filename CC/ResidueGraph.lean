/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CC.ResidueGraphDrift
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The residue transition graph `G_R(R,k)` (Report B3 item 6, step 1) (Ter76; YAH; Kar78)

**Report B3, item 6, concrete step 1:** build the residue transition graph `G(R,k)` for modulus `2^k`
and avoidance set `R ⊆ ℤ/2^k`, with edge weights `log 3 − (1+j)·log 2`. This file gives that
constructor and connects it to the drift dictionary of [[cc-srsbridge-item6]] ([[corpus-annotation-conventions]]).

* **Vertices** (`GRVerts k R`): the odd residues of `ℤ/2^k`, written as canonical representatives in
  `[0, 2^k)`, that are not in `R`.
* **Edges**: `u → S(u) mod 2^k`, where `S` is the **Syracuse map** `S(u) = (3u+1)/2^{v₂(3u+1)}` (`syr`)
  — one accelerated odd step followed by `j = v₂(3u+1)` halvings down to the next odd value.
* **Weight** (`syrWeight u = log 3 − (1+j)·log 2`): the `(max, +)` weight of that segment — one
  tripling (`+log 3`) and `1+j` halvings (`−(1+j)·log 2`). It is the path weight of the corresponding
  per-`T`-step run, `syrWeight u = stepWeight u − j·log 2` for odd `u` (`syrWeight_odd`).

The graph is genuinely finite and closed on the residues: every edge target is again in `[0, 2^k)`
(`GR_next_lt`). A **cycle** of `G_R` (a `ResidueGraphDrift.Cycle ℕ` of `ResidueGraphDrift`) has total weight
`len·log 3 − (len + J)·log 2` where `J` is its total halving count (`cycleWeight_syr`), so it
**contracts** (`cycleMean < 0`) iff its triplings beat its halvings,
`len·log 3 < (len + J)·log 2` (`cycleMean_syr_neg_iff`) — equivalently the orbit's odd-step fraction
`len/(len+J)` is below `SRSBridge.criticalRatio`. Plugging the Syracuse cycle mean into the abstract
duality (`ResidueGraphDrift.lam_neg_iff_drift_neg`) gives the dictionary on `G_R`:

> `λ(G_R) < 0  ⟺  every cycle contracts  ⟺  every stationary distribution has negative drift`
> (`gr_lam_neg_iff`, `gr_drift_dictionary`).

## Contents
* `syrHalvings`, `syr`, `syrWeight` — the halving count `v₂(3u+1)`, the Syracuse map, the edge weight;
  `syr_spec` (`3u+1 = 2^j·S(u)`), `syr_odd` (`S(u)` is odd), `syrWeight_odd`.
* `WeightedDigraph`, `GRVerts`, **`GR`** — the constructor; `GR_w`, `GR_verts_odd`, `GR_next_lt`.
* `totalHalvings`, `cycleWeight_syr`, `cycleMean_syr`, `cycleMean_syr_neg_iff` — Syracuse cycle means.
* **`gr_lam_neg_iff`**, **`gr_drift_dictionary`** — the dictionary on the concrete `G_R`.
* `syr_example`, `grverts_example` — small verified instances (`k = 2`).

## References
* [Ter76] Terras. *A stopping time problem on the positive integers.* Acta Arith. 30 (1976), 241–252.
* [YAH] Yolcu, Aaronson, Heule. *An Automated Approach to the Collatz Conjecture.* arXiv:2105.14697.
* [Kar78] Karp. *A characterization of the minimum cycle mean in a digraph.* Discrete Math. 23 (1978).
-/

namespace CC.ResidueGraph

open CC CC.ResidueGraphDrift

/-! ### The Syracuse map and its edge weight -/

/-- The **halving count** `j = v₂(3u+1)`: how many times `3u+1` is halved before reaching the next
odd value. -/
@[category API, AMS 11 37, ref "Ter76" "YAH", group "two_semiring_bridge"]
def syrHalvings (u : ℕ) : ℕ := (3 * u + 1).factorization 2

/-- The **Syracuse map** `S(u) = (3u+1)/2^{v₂(3u+1)}` — the next odd value after one accelerated odd
step from the odd residue `u`. (The odd part of `3u+1`.) -/
@[category API, AMS 11 37, ref "Ter76" "YAH", group "two_semiring_bridge"]
def syr (u : ℕ) : ℕ := ordCompl[2] (3 * u + 1)

/-- The **edge weight** `log 3 − (1+j)·log 2` of `G_R`: one tripling and `1+j` halvings. -/
@[category API, AMS 11 37, ref "YAH" "Kar78", group "two_semiring_bridge"]
noncomputable def syrWeight (u : ℕ) : ℝ :=
  Real.log 3 - (1 + (syrHalvings u : ℝ)) * Real.log 2

/-- The Syracuse factorization: `3u+1 = 2^{v₂(3u+1)} · S(u)`. -/
@[category research solved, AMS 11, ref "Ter76", group "two_semiring_bridge"]
theorem syr_spec (u : ℕ) : 2 ^ syrHalvings u * syr u = 3 * u + 1 :=
  Nat.ordProj_mul_ordCompl_eq_self (3 * u + 1) 2

/-- The Syracuse value is odd (it is `3u+1` with all factors of `2` removed). -/
@[category research solved, AMS 11, ref "Ter76", group "two_semiring_bridge"]
theorem syr_odd (u : ℕ) : syr u % 2 = 1 := by
  have h : ¬ (2 ∣ syr u) := Nat.not_dvd_ordCompl Nat.prime_two (by omega)
  omega

/-- The edge weight as a per-`T`-step path weight: for odd `u`, `syrWeight u = stepWeight u − j·log 2`
(the one odd step `stepWeight u` plus `j` halvings, each `−log 2`). -/
@[category research solved, AMS 11 37, ref "Ter76" "YAH", group "two_semiring_bridge",
  formal_uses syrWeight stepWeight]
theorem syrWeight_odd {u : ℕ} (h : u % 2 = 1) :
    syrWeight u = stepWeight u - (syrHalvings u : ℝ) * Real.log 2 := by
  unfold syrWeight stepWeight
  rw [if_pos h]; ring

/-! ### The constructor -/

/-- A finite weighted digraph: an adjacency relation and an edge-weight function. -/
@[category API, AMS 5 90, ref "Kar78", group "two_semiring_bridge"]
structure WeightedDigraph (V : Type*) where
  /-- The adjacency relation. -/
  Adj : V → V → Prop
  /-- The edge-weight function. -/
  w : V → V → ℝ

/-- The **vertices of `G_R(R,k)`**: odd residues of `ℤ/2^k` (canonical representatives in `[0,2^k)`)
not in the avoidance set `R`. -/
@[category API, AMS 11 37, ref "YAH", group "two_semiring_bridge"]
def GRVerts (k : ℕ) (R : Finset ℕ) : Finset ℕ :=
  (Finset.range (2 ^ k)).filter (fun u => u % 2 = 1 ∧ u ∉ R)

/-- **The residue transition graph `G_R(R,k)`** ([YAH]): vertices the odd residues `∉ R`, an edge
`u → S(u) mod 2^k`, weight `log 3 − (1+j)·log 2`. -/
@[category API, AMS 11 37, ref "YAH" "Kar78", group "two_semiring_bridge"]
noncomputable def GR (k : ℕ) (R : Finset ℕ) : WeightedDigraph ℕ where
  Adj u v := u ∈ GRVerts k R ∧ v = syr u % 2 ^ k
  w u _ := syrWeight u

/-- The weight on an edge out of `u` is `syrWeight u`. -/
@[category API, AMS 11 37, ref "YAH", group "two_semiring_bridge"]
theorem GR_w (k : ℕ) (R : Finset ℕ) (u v : ℕ) : (GR k R).w u v = syrWeight u := rfl

/-- Vertices of `G_R` are odd. -/
@[category API, AMS 11, ref "YAH", group "two_semiring_bridge"]
theorem GR_verts_odd {k : ℕ} {R : Finset ℕ} {u : ℕ} (hu : u ∈ GRVerts k R) : u % 2 = 1 :=
  (Finset.mem_filter.mp hu).2.1

/-- **The graph is closed on the residues**: every edge target lands again in `[0, 2^k)`, so `G_R` is
a genuine finite digraph on `ℤ/2^k`. -/
@[category research solved, AMS 11 37, ref "YAH", group "two_semiring_bridge"]
theorem GR_next_lt (k u : ℕ) : syr u % 2 ^ k < 2 ^ k :=
  Nat.mod_lt _ (by positivity)

/-! ### Syracuse cycle means and the dictionary on `G_R` -/

/-- The **total halving count** around a cycle: `J = ∑ v₂(3·vᵢ+1)`. -/
@[category API, AMS 11 37, ref "Ter76", group "two_semiring_bridge"]
noncomputable def totalHalvings (c : ResidueGraphDrift.Cycle ℕ) : ℝ :=
  ∑ i : Fin c.len, (syrHalvings (c.vert i) : ℝ)

/-- The total Syracuse weight of a cycle is `len·log 3 − (len + J)·log 2`. -/
@[category research solved, AMS 11 37, ref "Ter76" "YAH" "Kar78", group "two_semiring_bridge",
  formal_uses syrWeight totalHalvings]
theorem cycleWeight_syr (c : ResidueGraphDrift.Cycle ℕ) :
    cycleWeight (fun u _ => syrWeight u) c
      = (c.len : ℝ) * Real.log 3 - ((c.len : ℝ) + totalHalvings c) * Real.log 2 := by
  have h1 : (∑ _i : Fin c.len, Real.log 3) = (c.len : ℝ) * Real.log 3 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h2 : (∑ i : Fin c.len, (1 + (syrHalvings (c.vert i) : ℝ)) * Real.log 2)
      = ((c.len : ℝ) + totalHalvings c) * Real.log 2 := by
    unfold totalHalvings
    rw [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  unfold cycleWeight
  simp_rw [syrWeight]
  rw [Finset.sum_sub_distrib, h1, h2]

/-- The Syracuse cycle mean is `log 3 − (1 + J/len)·log 2`. -/
@[category research solved, AMS 11 37, ref "Ter76" "YAH" "Kar78", group "two_semiring_bridge",
  formal_uses cycleWeight_syr]
theorem cycleMean_syr (c : ResidueGraphDrift.Cycle ℕ) :
    cycleMean (fun u _ => syrWeight u) c
      = Real.log 3 - (1 + totalHalvings c / (c.len : ℝ)) * Real.log 2 := by
  have hlen : (c.len : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr c.pos.ne'
  unfold cycleMean
  rw [cycleWeight_syr]
  field_simp

/-- A Syracuse cycle **contracts** (`cycleMean < 0`) iff its triplings beat its halvings:
`len·log 3 < (len + J)·log 2` — equivalently its odd-step fraction `len/(len+J)` is below the
critical ratio of the two-semiring bridge. -/
@[category research solved, AMS 11 37, ref "Ter76" "YAH", group "two_semiring_bridge",
  formal_uses cycleMean_syr]
theorem cycleMean_syr_neg_iff (c : ResidueGraphDrift.Cycle ℕ) :
    cycleMean (fun u _ => syrWeight u) c < 0
      ↔ (c.len : ℝ) * Real.log 3 < ((c.len : ℝ) + totalHalvings c) * Real.log 2 := by
  have hlen : (0 : ℝ) < (c.len : ℝ) := by exact_mod_cast c.pos
  have hlen' : (c.len : ℝ) ≠ 0 := ne_of_gt hlen
  rw [cycleMean_syr, sub_lt_zero,
    show (1 + totalHalvings c / (c.len : ℝ)) * Real.log 2
      = ((c.len : ℝ) + totalHalvings c) * Real.log 2 / (c.len : ℝ) from by field_simp,
    lt_div_iff₀ hlen, mul_comm (Real.log 3) (c.len : ℝ)]

/-- **The drift dictionary on `G_R`** (instantiating `ResidueGraphDrift.lam_neg_iff_drift_neg` at the
Syracuse weight): `λ(G_R) < 0` iff every stationary distribution on `G_R` has negative drift. -/
@[category research solved, AMS 11 90, ref "Ter76" "YAH" "Kar78", group "two_semiring_bridge",
  formal_uses lam_neg_iff_drift_neg]
theorem gr_drift_dictionary {𝒞 : Finset (ResidueGraphDrift.Cycle ℕ)} (h : 𝒞.Nonempty) :
    lam 𝒞 h (cycleMean fun u _ => syrWeight u) < 0
      ↔ ∀ μ : StatDist 𝒞, drift 𝒞 (cycleMean fun u _ => syrWeight u) μ < 0 :=
  lam_neg_iff_drift_neg 𝒞 h _

/-- `λ(G_R) < 0` iff **every cycle of `G_R` contracts** (triplings below halvings): the
certificate-existence criterion in terms of the residue cycles. -/
@[category research solved, AMS 11 90, ref "YAH" "Kar78", group "two_semiring_bridge",
  formal_uses cycleMean_syr_neg_iff]
theorem gr_lam_neg_iff {𝒞 : Finset (ResidueGraphDrift.Cycle ℕ)} (h : 𝒞.Nonempty) :
    lam 𝒞 h (cycleMean fun u _ => syrWeight u) < 0
      ↔ ∀ c ∈ 𝒞, (c.len : ℝ) * Real.log 3 < ((c.len : ℝ) + totalHalvings c) * Real.log 2 := by
  rw [lam, Finset.sup'_lt_iff]
  simp_rw [cycleMean_syr_neg_iff]

/-! ### Small verified instances (`k = 2`) -/

/-- `S(3) = 5` with `j = v₂(10) = 1`: `3·3+1 = 10 = 2·5`. -/
@[category test, AMS 11, ref "Ter76", group "two_semiring_bridge"]
theorem syr_example : syrHalvings 3 = 1 ∧ syr 3 = 5 := by
  constructor <;> native_decide

/-- The vertices of `G_∅(∅, 2)` are the odd residues mod `4`: `{1, 3}`. -/
@[category test, AMS 11, ref "YAH", group "two_semiring_bridge"]
theorem grverts_example : GRVerts 2 ∅ = {1, 3} := by decide

end CC.ResidueGraph
