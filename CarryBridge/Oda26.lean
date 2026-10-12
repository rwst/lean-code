/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CarryGraph.Quotient
import Oda26.NFGraphs

/-!
# Bridge: `Oda26/` word graphs as carry graphs

[Oda26] works with *word graphs* `Oda.WG.Graph V α = V → List α → V → Prop`, whose edges carry
words.  A carry graph carries letters (plan-carry D-2).  The two meet on **one-letter** word
graphs, and every graph of [Oda26] §§3–7 that the corpus builds is one: the one-step graph
`oneStep` ((10) of [Oda26]), the complete graph `oneStepU = G(M, K)` and `gPrime = G′(R, K)`
(`isSingle_oneStep`, `isSingle_oneStepU`, `isSingle_gPrime`).  Only the contracted graphs of the
normal form (`Oda.WG.contract`, `Oda.WG.contractG`) carry longer words.  They enter through the
subdivision `CarryGraph.subdivide` of gate G-2 (M4): for a word graph `G` whose edges form a
finite set `F` of non-empty words, `Oda.WG.Covers G` is `CarryGraph.WCovers F`
(`covers_iff_wCovers`), so [Oda26]'s `AllPer` is the label form of the subdivision
(`odaAllPer_iff_subdivide`) and **Theorem 21 holds for every finite word graph as the
determinization theorem of its subdivision** (`allCert_iff_subdivide`).

Dictionary, for a one-letter word graph `E` and `X = ofWG E`:

| `Oda26/` | `CarryGraph/` |
|---|---|
| `E u [a] v` | `X.Adj u a v` (`adj_ofWG`; `toWG_ofWG` inverts) |
| `Oda.WG.Reach E` | `X.Reach` (`reach_ofWG`) |
| `Oda.WG.AllPer E` (Thm 21 (a)) | `X.AllPer` (`odaAllPer_iff`) |
| `Oda.WG.AllCert E` (Thm 21 (b), the phase test) | `X.det.LNoBranch` (`allCert_iff_det`) |
| Lemma 31 (`proj_edge`) | a carry-graph homomorphism `odaProjHom` |
| word graph with finite edge set `F` | `CarryGraph.subdivide F` (`odaAllPer_iff_subdivide`) |
| `Oda.WG.Covers` | `CarryGraph.WCovers` (`covers_iff_wCovers`) |
| Thm 21, any finite word graph | `allCert_iff_subdivide` |

So [Oda26] Theorem 21 for one-letter graphs is the determinization theorem of Chapter 5, and the
phase test of a component is the state form of the subset construction.  In particular an
[Oda26] certificate exists iff the label language grows polynomially (`allCert_iff_wordGrowth`).
Projection soundness (`allPer_of_proj`: periodic output on the coarse graph `G(m, k)` gives it on
`G(M, K)`) is `allPer_of_hom` along `odaProjHom`.

## References

* [Oda26] Y. Odagiri, *Finite graph certificates for composite terms in rational floor
  sequences*, Zenodo, doi:10.5281/zenodo.22997709 (2026).
* [LM95] D. Lind, B. Marcus, *An Introduction to Symbolic Dynamics and Coding*, 1995.
-/

namespace CarryBridge

open CarryGraph Oda.WG ForMathlib.SubwordComplexity

variable {V α : Type*}

/-! ### One-letter word graphs -/

/-- A carry graph as a word graph with one-letter edges. -/
def toWG (X : CarryGraph V α) : Oda.WG.Graph V α := fun u w v => ∃ a, w = [a] ∧ X.Adj u a v

/-- Every edge of `E` carries a one-letter word. -/
def IsSingle (E : Oda.WG.Graph V α) : Prop := ∀ u w v, E u w v → w.length = 1

open Classical in
/-- A word graph on a finite vertex set read as a carry graph: its one-letter edges. -/
noncomputable def ofWG [Fintype V] (E : Oda.WG.Graph V α) : CarryGraph V α :=
  ⟨fun v a => Finset.univ.filter fun w => E v [a] w⟩

@[category API, AMS 05 37, ref "Oda26", group "carry_bridge_oda26"]
theorem adj_ofWG [Fintype V] {E : Oda.WG.Graph V α} {u v : V} {a : α} :
    (ofWG E).Adj u a v ↔ E u [a] v := by
  classical
  simp [ofWG, Adj]

@[category API, AMS 05 37, ref "Oda26", group "carry_bridge_oda26"]
theorem toWG_ofWG [Fintype V] {E : Oda.WG.Graph V α} (hE : IsSingle E) : toWG (ofWG E) = E := by
  funext u w v
  apply propext
  constructor
  · rintro ⟨a, rfl, h⟩
    exact adj_ofWG.1 h
  · intro h
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 (hE u w v h)
    exact ⟨a, rfl, adj_ofWG.2 h⟩

@[category API, AMS 05 37, ref "Oda26", group "carry_bridge_oda26"]
theorem isSingle_toWG (X : CarryGraph V α) : IsSingle (toWG X) := by
  rintro u w v ⟨a, rfl, -⟩
  rfl

@[category API, AMS 05 37, ref "Oda26", group "carry_bridge_oda26"]
theorem reach_toWG {X : CarryGraph V α} {u v : V} : Oda.WG.Reach (toWG X) u v ↔ X.Reach u v := by
  have : (fun u v => ∃ w, toWG X u w v) = X.under := by
    funext u v
    exact propext ⟨fun ⟨_, a, _, h⟩ => ⟨a, h⟩, fun ⟨a, h⟩ => ⟨[a], a, rfl, h⟩⟩
  simp only [Oda.WG.Reach, CarryGraph.Reach, this]

@[category API, AMS 05 37, ref "Oda26", group "carry_bridge_oda26"]
theorem reach_ofWG [Fintype V] {E : Oda.WG.Graph V α} (hE : IsSingle E) {u v : V} :
    (ofWG E).Reach u v ↔ Oda.WG.Reach E u v := by
  rw [← reach_toWG, toWG_ofWG hE]

/-! ### Theorem 21 as the determinization theorem -/

/-- **[Oda26]'s `AllPer` on a carry graph is the label form `AllPer`.** -/
@[category API, AMS 05 37, ref "Oda26", group "carry_bridge_oda26"]
theorem odaAllPer_toWG_iff {X : CarryGraph V α} : Oda.WG.AllPer (toWG X) ↔ X.AllPer := by
  constructor
  · intro h s ℓ hs
    have hcov : Covers (toWG X) ℓ s (fun i => [ℓ i]) (fun i => i) :=
      ⟨fun i => ⟨ℓ i, rfl, hs i⟩, fun i => by simp, fun i => by simp, fun i => by simp⟩
    exact h _ _ _ _ hcov
  · intro h y v w t hcov
    choose a ha hE using hcov.edge
    have ht : ∀ i, t i = t 0 + i := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih => rw [hcov.time, ha, ih]; simp; ring
    have hy : ∀ i, a i = y (t 0 + i) := by
      intro i
      have := hcov.word i
      rw [ha i, ht i] at this
      simpa using this
    obtain ⟨n₀, L, hL, hper⟩ := h v a hE
    refine ⟨t 0 + n₀, L, hL, fun k hk => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, k = t 0 + m := ⟨k - t 0, by omega⟩
    have := hper m (by omega)
    rwa [hy, hy, ← add_assoc] at this

/-- **[Oda26]'s `AllPer` on a one-letter word graph is the label form of its carry graph.** -/
@[category API, AMS 05 37, ref "Oda26", group "carry_bridge_oda26"]
theorem odaAllPer_iff [Fintype V] {E : Oda.WG.Graph V α} (hE : IsSingle E) :
    Oda.WG.AllPer E ↔ (ofWG E).AllPer := by
  rw [← odaAllPer_toWG_iff, toWG_ofWG hE]

/-- **[Oda26] Theorem 21 for one-letter graphs is the determinization theorem**: every strong
component passes the phase test iff the subset construction passes the state form. -/
@[category research solved, AMS 05 37, ref "Oda26" "LM95", group "carry_bridge_oda26"]
theorem allCert_iff_det [Fintype V] [DecidableEq V] [Nonempty α] {E : Oda.WG.Graph V α}
    (hE : IsSingle E) : AllCert E ↔ (ofWG E).det.LNoBranch := by
  rw [allCert_iff_allPer fun u w v h => by rw [hE u w v h]; omega, odaAllPer_iff hE]
  exact determinization.out 1 3

/-- **An [Oda26] certificate exists iff the label language grows polynomially** (finite
alphabet). -/
@[category research solved, AMS 05 37, ref "Oda26" "LM95", group "carry_bridge_oda26"]
theorem allCert_iff_wordGrowth [Fintype V] [DecidableEq V] [Fintype α] [DecidableEq α]
    [Nonempty α] {E : Oda.WG.Graph V α} (hE : IsSingle E) :
    AllCert E ↔ ∃ C d : ℕ, ∀ v n, ((ofWG E).words v n).card ≤ C * (n + 1) ^ d := by
  rw [allCert_iff_allPer fun u w v h => by rw [hE u w v h]; omega, odaAllPer_iff hE]
  exact allPer_iff_wordGrowth

/-! ### The graphs of [Oda26] are one-letter graphs -/

variable {a b : ℕ} {ν : ℝ}

@[category API, AMS 05 37, ref "Oda26", group "carry_bridge_oda26"]
theorem isSingle_oneStep {M K : ℕ} {W : Fin M × Fin K → Prop} :
    IsSingle (oneStep a b ν M K W) := by
  rintro u w v ⟨-, -, e, rfl, -⟩
  rfl

@[category API, AMS 05 37, ref "Oda26", group "carry_bridge_oda26"]
theorem isSingle_oneStepU {M K : ℕ} : IsSingle (oneStepU a b ν M K) :=
  isSingle_oneStep

@[category API, AMS 05 37, ref "Oda26", group "carry_bridge_oda26"]
theorem isSingle_gPrime {R K : ℕ} : IsSingle (gPrime a b ν R K) :=
  fun u w v h => isSingle_oneStepU u w v h.1

/-- **[Oda26] Lemma 31 as a homomorphism**: `π(q, J) = (q mod m, ⌊J/f⌋)` maps `G(M, K)` to
`G(m, k)` with the same labels. -/
noncomputable def odaProjHom {m k M K : ℕ} (hm : m ∣ M) (hk : k ∣ K) :
    Hom (ofWG (oneStepU a b ν M K)) (ofWG (oneStepU a b ν m k)) where
  toFun := proj hm hk
  map_adj h := adj_ofWG.2 (proj_edge hm hk (adj_ofWG.1 h))

/-- **Projection soundness**: periodic output on the coarse complete graph `G(m, k)` gives
periodic output on the fine graph `G(M, K)` (`allPer_of_hom` along `odaProjHom`). -/
@[category research solved, AMS 05 11 37, ref "Oda26", group "carry_bridge_oda26"]
theorem allPer_of_proj {m k M K : ℕ} (hm : m ∣ M) (hk : k ∣ K)
    (h : Oda.WG.AllPer (oneStepU a b ν m k)) : Oda.WG.AllPer (oneStepU a b ν M K) := by
  rw [odaAllPer_iff isSingle_oneStepU] at h ⊢
  exact allPer_of_hom (odaProjHom hm hk) h

/-- **[Oda26] Theorem 21 on the complete one-step graph**: `G(M, K)` is certified iff the subset
construction of its carry graph has no branching inside a strong component. -/
@[category research solved, AMS 05 11 37, ref "Oda26" "LM95", group "carry_bridge_oda26"]
theorem allCert_oneStepU_iff {M K : ℕ} :
    AllCert (oneStepU a b ν M K) ↔ (ofWG (oneStepU a b ν M K)).det.LNoBranch := by
  classical
  exact allCert_iff_det isSingle_oneStepU

/-! ### Finite word graphs: subdivision (gate G-2) -/

section subdivide

variable [DecidableEq V] [DecidableEq α] {G : Oda.WG.Graph V α} {F : Finset (V × List α × V)}
  (hF : ∀ u w v, G u w v ↔ (u, w, v) ∈ F) (hpos : ∀ e ∈ F, e.2.1 ≠ [])
include hF hpos

omit [DecidableEq V] [DecidableEq α] in
/-- **[Oda26]'s covering walks are the word paths of the edge set.** -/
@[category API, AMS 05 37, ref "Oda26", group "carry_bridge_oda26"]
theorem covers_iff_wCovers {y : ℕ → α} {v : ℕ → V} {w : ℕ → List α} {t : ℕ → ℕ} :
    Covers G y v w t ↔ WCovers F y v w t := by
  constructor
  · intro h
    refine ⟨fun i => (hF _ _ _).1 (h.edge i), h.time, fun i k hk => ?_⟩
    rw [List.getElem?_eq_getElem hk, h.letter i k hk]
  · intro h
    refine ⟨fun i => (hF _ _ _).2 (h.edge i),
      fun i => List.length_pos_of_ne_nil (hpos _ (h.edge i)), h.time, fun i => ?_⟩
    refine List.ext_getElem (by simp) fun k hk _ => ?_
    have := h.word i k hk
    rw [List.getElem?_eq_getElem hk, Option.some_inj] at this
    simp [this]

/-- **[Oda26]'s `AllPer` of a finite word graph is the label form of its subdivision.** -/
@[category research solved, AMS 05 37, ref "Oda26" "LM95", group "carry_bridge_oda26"]
theorem odaAllPer_iff_subdivide : Oda.WG.AllPer G ↔ (subdivide F).AllPer := by
  rw [allPer_subdivide_iff hpos]
  exact ⟨fun h ℓ v w t hc => h ℓ v w t ((covers_iff_wCovers hF hpos).2 hc),
    fun h y v w t hc => h y v w t ((covers_iff_wCovers hF hpos).1 hc)⟩

/-- **[Oda26] Theorem 21 for every finite word graph** (gate G-2): every strong component passes
the phase test iff the subset construction of the subdivision has no branching inside a strong
component. -/
@[category research solved, AMS 05 37, ref "Oda26" "LM95", group "carry_bridge_oda26"]
theorem allCert_iff_subdivide [Fintype V] [Nonempty α] :
    AllCert G ↔ (subdivide F).det.LNoBranch := by
  rw [allCert_iff_allPer fun u w v h => List.length_pos_of_ne_nil (hpos _ ((hF u w v).1 h)),
    odaAllPer_iff_subdivide hF hpos]
  exact determinization.out 1 3

end subdivide

end CarryBridge
