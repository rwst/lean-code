/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.GenSound
import Oda26.RankFromCert

/-!
# Bridge: checked atlas certificates are [Oda26] certified graphs

A `DubC2.Gen.Checked` certificate is a statement about the residue × cell graph of
`DubC2/GenCert.lean`.  Read as a word-labelled graph of [Oda26] (`Gen.odaGraph`, one letter per
edge), it is a graph all of whose infinite walks have eventually periodic output
(`Gen.allPer_of_checked`), hence — by [Oda26] Theorem 21 in the form `Oda.WG.allCert_iff_allPer` —
a graph all of whose strongly connected components pass the phase test (`Gen.allCert_of_checked`).

So every atlas instance inherits the theory of [Oda26] for shifted sequences.  The first payoff is
quantitative (plan-dubC2 T4 in its honest form — a bound on the *first* hit, not on the gaps):

* `Gen.first_hit_of_checked` — for a checked `(p/q, ν = a/b, 𝒫)` there is a constant `D` such that
  for every `ξ` with `X = ⌊ξ + ν⌋ ≥ q/(p−q) + |ν|`, some `n ≤ T` has `xₙ = ⌊ξ(p/q)ⁿ + ν⌋` divisible
  by a member of `𝒫` as soon as `T > γ^V(V−1) + (A + γD)·∑_{j<V} γ^j`, where `V = M·D_cells` is the
  vertex count, `γ ≥ 1 + log_q(p/q)` and `A ≥ log_q(X + 2 + 2|ν|)` — so `n = O(log ξ)`.

(The constant is astronomically large — `γ^V` — but explicit in the graph; it is [Oda26] Theorem 27
with the rank certificate of `Oda.WG.rankCertOf`.)

## References

* [Oda26] Y. Odagiri, *Finite graph certificates for composite terms in rational floor sequences*,
  Zenodo, doi:10.5281/zenodo.22997709 (2026).
-/

namespace DubC2.Gen

open Oda Oda.WG ForMathlib.SubwordComplexity

/-- The certificate graph as an [Oda26] word-labelled graph: one letter per edge. -/
def odaGraph (P : Params) : Graph (Fin P.nV) ℤ := fun u w v =>
  ∃ t < P.nA, w = [P.letter t] ∧ (v : ℕ) ∈ P.succList u (P.letter t)

variable {P : Params} {C : Cert}

/-- **Every infinite walk of a checked graph has eventually periodic output.** -/
@[category API, AMS 11 37, ref "Oda26", group "dubc2_atlas"]
theorem allPer_of_checked (hc : Checked P C) : AllPer (odaGraph P) := by
  intro y v w tt hcov
  choose tl htl1 htl2 htl3 using fun i => hcov.edge i
  have hp : IsPath P 0 (fun n => (v n : ℕ)) tl :=
    ⟨fun n _ => (v n).isLt, fun n _ => htl1 n, fun n _ => htl3 n⟩
  obtain ⟨N, per, hper, hp'⟩ := isEventuallyPeriodic_of_path hc hp
  have hlen : ∀ i, (w i).length = 1 := fun i => by rw [htl2 i]; rfl
  have htt : ∀ i, tt i = tt 0 + i := fun i => by
    induction i with
    | zero => rfl
    | succ i ih => rw [hcov.time i, hlen i, ih]; ring
  have hy : ∀ i, y (tt 0 + i) = P.letter (tl i) := fun i => by
    have := hcov.letter i 0 (by rw [hlen i]; omega)
    rw [htt i, add_zero] at this
    rw [this]; simp [htl2 i]
  refine ⟨tt 0 + N, per, hper, fun k hk => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, k = tt 0 + i := ⟨k - tt 0, by omega⟩
  rw [add_assoc, hy, hy, hp' i (by omega)]

/-- **A checked graph is [Oda26]-certified**: every strongly connected component passes the
phase test (19). -/
@[category API, AMS 11 37, ref "Oda26", group "dubc2_atlas"]
theorem allCert_of_checked (hc : Checked P C) : AllCert (odaGraph P) :=
  (allCert_iff_allPer fun u w v ⟨t, _, hw, _⟩ => by rw [hw]; simp).2 (allPer_of_checked hc)

/-- **First-hit bound for a checked atlas cell** ([Oda26] Theorem 27 via `rankCertOf`). -/
@[category research solved, AMS 11 37, ref "Oda26", group "dubc2_atlas"]
theorem first_hit_of_checked (hc : Checked P C) :
    ∃ D : ℕ, ∀ {ξ : ℝ} {X : ℤ}, (X : ℝ) ≤ ξ + P.nu → ξ + P.nu < X + 1 →
      (P.q : ℝ) / (P.p - P.q) + |P.nu| ≤ X → ∀ {γ A : ℝ},
      1 + Real.logb P.q ((P.p : ℝ) / P.q) ≤ γ → Real.logb P.q (X + 2 + 2 * |P.nu|) ≤ A →
      ∀ T : ℕ, Gpot γ (A + γ * D) P.nV (P.nV - 1 : ℕ) + 1 < T →
      ∃ n ≤ T, ∃ ℓ ∈ P.PM ++ P.Pq, (ℓ : ℤ) ∣ Z32.xInt P.p P.q ξ P.nu n := by
  have hF : ParamFacts P := by
    have hh := hc.head
    simp only [checkHead, Bool.and_eq_true] at hh
    exact paramFacts hh.1.1.1.1.1
  obtain ⟨D, hD⟩ := waiting_time_of_allCert (allCert_of_checked hc)
  refine ⟨D, fun {ξ X} hξ0 hξ1 hX {γ A} hγ hA T hT => ?_⟩
  have hq1 : (1 : ℝ) < P.q := by exact_mod_cast hF.q1
  have hpq : (P.q : ℝ) < P.p := by exact_mod_cast hF.pq
  have hκ : 0 < Real.logb P.q ((P.p : ℝ) / P.q) :=
    Real.logb_pos hq1 (by rw [one_lt_div (by linarith)]; exact hpq)
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (by
    have := div_pos (by linarith : (0 : ℝ) < P.q) (by linarith : (0 : ℝ) < P.p - P.q)
    linarith [abs_nonneg P.nu]) hX
  have hA0 : 0 < A := lt_of_lt_of_le (Real.logb_pos hq1 (by linarith [abs_nonneg P.nu])) hA
  have hγ0 : (0 : ℝ) ≤ γ := by linarith
  have hG := Gpot_nonneg (γ := γ) (K := A + γ * D) (by linarith) (by positivity) P.nV
    (r := ((P.nV - 1 : ℕ) : ℝ)) (Nat.cast_nonneg _)
  have hT1 : 1 ≤ T := by
    have : (1 : ℝ) < T := by linarith
    exact_mod_cast this.le
  by_contra hcon
  push Not at hcon
  have hav : ∀ n, n ≤ T → Avoids P ξ n := fun n hn ℓ hℓ => hcon n hn ℓ hℓ
  have hs : ∀ n, n < T → _ := fun n hn => sound hF (hav n hn.le) (hav (n + 1) hn)
  have h0 := (hs 0 (by omega)).1
  let σ : ℕ → Fin P.nV := fun n =>
    if h : vtx P ξ n < P.nV then ⟨vtx P ξ n, h⟩ else ⟨vtx P ξ 0, h0⟩
  have hσ : ∀ n, n < T → (σ n : ℕ) = vtx P ξ n := fun n hn => by
    simp [σ, (hs n hn).1]
  have hwalk : ∀ n < T - 1, odaGraph P (σ n) [cf P.p P.q ξ P.nu n] (σ (n + 1)) := by
    intro n hn
    obtain ⟨_, ht, hlet, hmem⟩ := hs n (by omega)
    refine ⟨tix P ξ n, ht, ?_, ?_⟩
    · rw [hlet]; rfl
    · rw [hσ (n + 1) (by omega), hσ n (by omega)]; exact hmem
  have := hD hF.q1 hF.pq hF.cop hξ0 hξ1 hX hγ hA hwalk
  have hc' : ((T - 1 : ℕ) : ℝ) = T - 1 := by rw [Nat.cast_sub hT1]; simp
  rw [hc', Fintype.card_fin] at this
  linarith

end DubC2.Gen
