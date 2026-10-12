/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Oda26.OrbitBasics
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.ZMod.Basic

/-!
# Word-labelled certificates ([Oda26] §§3.2, 4.1–4.5)

A *word-labelled graph* has edges `u —w→ v` labelled by nonempty words.  An infinite walk *covers*
a sequence `y` from time `n₀` (`G ⊨ n₀`) if its concatenated output is `y n₀, y (n₀+1), …`.
[Oda26] certifies `gcd(Qₙ, M) > 1` infinitely often by shrinking a graph covering the carry word
`cₙ` of `⌊ξ(a/b)ⁿ⌋` through three tail-preserving operations until no infinite walk is left.

* `Oda.WG.eventually_sameSCC` — **Lemma 6**: an infinite walk in a finite graph eventually stays in
  one strongly connected component.
* `Oda.WG.Covers.output_of_certified`, `Oda.WG.Covers.periodic_of_certified` —
  **Lemma 12(b)** (and Lemma 7): a walk inside a component passing the weighted phase test has
  output `y_{n₀+s} = λ((h(v₀) + s) mod d)`, hence period `d`.
* `Oda.WG.phase_telescope`, `Oda.WG.exists_delta_ne_zero` — **Lemma 12(a)**.
* `Oda.WG.models_removal` — **Proposition 13** (and Lemma 8): removal of every certified or
  acyclic component preserves coverings of a non-eventually-periodic word.
* `Oda.WG.visits_B` — **Lemma 15**; `Oda.WG.models_contract` — **Proposition 16** (forward
  direction): contraction of deterministic paths.
* `Oda.WG.models_lift` — **Proposition 17**: lifting by a prime `p ∤ b`.
* `Oda.WG.models_cellGraph` — **Proposition 5** for `M = 1`: the cell graph covers the carries.
* `Oda.WG.Exec`, `Oda.WG.finite_success` — **Theorem 19** (word-labelled finite success);
  `Oda.WG.composite_frequently` — **Corollary 20**.

## References

* [Oda26] Y. Odagiri, *Finite graph certificates for composite terms in rational floor sequences*,
  Zenodo, doi:10.5281/zenodo.22997709 (2026).
-/

namespace Oda.WG

open ForMathlib.SubwordComplexity

variable {V α : Type*}

/-- A word-labelled graph: `E u w v` is an edge `u —w→ v`. -/
abbrev Graph (V α : Type*) := V → List α → V → Prop

/-- An infinite walk `v` with words `w` and times `t` whose output is `y` from `t 0` on. -/
structure Covers (E : Graph V α) (y : ℕ → α) (v : ℕ → V) (w : ℕ → List α) (t : ℕ → ℕ) :
    Prop where
  edge : ∀ i, E (v i) (w i) (v (i + 1))
  pos : ∀ i, 0 < (w i).length
  time : ∀ i, t (i + 1) = t i + (w i).length
  word : ∀ i, w i = (List.range' (t i) (w i).length).map y

/-- `G ⊨ n₀`: some infinite walk of `G` outputs the tail of `y` from `n₀`. -/
def Models (E : Graph V α) (y : ℕ → α) (n₀ : ℕ) : Prop :=
  ∃ v w t, Covers E y v w t ∧ t 0 = n₀

namespace Covers

variable {E : Graph V α} {y : ℕ → α} {v : ℕ → V} {w : ℕ → List α} {t : ℕ → ℕ}

theorem shift (h : Covers E y v w t) (k : ℕ) :
    Covers E y (fun i => v (k + i)) (fun i => w (k + i)) (fun i => t (k + i)) :=
  ⟨fun i => h.edge (k + i), fun i => h.pos (k + i), fun i => h.time (k + i),
    fun i => h.word (k + i)⟩

theorem le_t (h : Covers E y v w t) (i : ℕ) : t 0 + i ≤ t i := by
  induction i with
  | zero => simp
  | succ i ih => have := h.time i; have := h.pos i; omega

theorem mono (h : Covers E y v w t) {i j : ℕ} (hij : i ≤ j) : t i ≤ t j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => have := h.time j; omega

theorem letter (h : Covers E y v w t) (i k : ℕ) (hk : k < (w i).length) :
    y (t i + k) = (w i)[k] := by
  have e : (w i)[k]? = some (y (t i + k)) := by
    rw [h.word i]; simp [hk]
  rw [List.getElem?_eq_getElem hk] at e
  exact (Option.some.inj e).symm

/-- Every time `t 0 + s` lies inside some word. -/
theorem exists_seg (h : Covers E y v w t) (s : ℕ) :
    ∃ i k, k < (w i).length ∧ t i + k = t 0 + s := by
  classical
  have hex : ∃ i, t 0 + s < t (i + 1) := ⟨s, by have := h.le_t (s + 1); omega⟩
  set i := Nat.find hex with hi
  have hspec := Nat.find_spec hex
  have hle : t i ≤ t 0 + s := by
    rcases Nat.eq_zero_or_eq_succ_pred i with h0 | h0
    · rw [h0]; omega
    · have := Nat.find_min hex (show i.pred < i by omega)
      rw [← Nat.succ_eq_add_one, ← h0] at this
      omega
  refine ⟨i, t 0 + s - t i, ?_, by omega⟩
  have := h.time i
  rw [← hi] at hspec
  omega

end Covers

/-! ## Lemma 6 -/

/-- Reachability along edges (paths of length `0` allowed). -/
def Reach (E : Graph V α) : V → V → Prop := Relation.ReflTransGen fun u v => ∃ w, E u w v

/-- Mutual reachability: same strongly connected component. -/
def SameSCC (E : Graph V α) (u v : V) : Prop := Reach E u v ∧ Reach E v u

theorem SameSCC.symm {E : Graph V α} {u v : V} (h : SameSCC E u v) : SameSCC E v u := ⟨h.2, h.1⟩

theorem SameSCC.trans {E : Graph V α} {u v x : V} (h : SameSCC E u v) (h' : SameSCC E v x) :
    SameSCC E u x := ⟨h.1.trans h'.1, h'.2.trans h.2⟩

theorem reach_walk {E : Graph V α} {v : ℕ → V} {w : ℕ → List α}
    (hedge : ∀ i, E (v i) (w i) (v (i + 1))) {i j : ℕ} (hij : i ≤ j) : Reach E (v i) (v j) := by
  induction j, hij using Nat.le_induction with
  | base => exact Relation.ReflTransGen.refl
  | succ j _ ih => exact ih.tail ⟨w j, hedge j⟩

/-- **[Oda26] Lemma 6.**  An infinite walk in a finite graph eventually stays in one strongly
connected component. -/
@[category research solved, AMS 05 37, ref "Oda26", group "oda26_wordgraph"]
theorem eventually_sameSCC [Finite V] {E : Graph V α} {v : ℕ → V} {w : ℕ → List α}
    (hedge : ∀ i, E (v i) (w i) (v (i + 1))) :
    ∃ i₁, ∀ i, i₁ ≤ i → SameSCC E (v i₁) (v i) := by
  obtain ⟨x, hx⟩ := Finite.exists_infinite_fiber v
  have hinf : (v ⁻¹' {x}).Infinite := Set.infinite_coe_iff.1 hx
  obtain ⟨i₁, hi₁⟩ := hinf.nonempty
  refine ⟨i₁, fun i hi => ⟨reach_walk hedge hi, ?_⟩⟩
  obtain ⟨j, hj, hij⟩ := hinf.exists_gt i
  have h1 : v j = v i₁ := by
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hj hi₁; rw [hj, hi₁]
  rw [← h1]
  exact reach_walk hedge hij.le

/-! ## Lemma 12 -/

/-- A set `S` of vertices passes the **weighted phase test**: a phase `h`, a modulus `d ≥ 1` and a
labelling `λ` with `h(v) ≡ h(u) + |w| (mod d)` and `wᵢ = λ((h(u) + i) mod d)` on every edge inside
`S` ([Oda26] (19)). -/
def Certified (E : Graph V α) (S : V → Prop) : Prop :=
  ∃ (h : V → ℤ) (d : ℕ) (lam : ℤ → α), 0 < d ∧ ∀ u w v, E u w v → S u → S v →
    h v ≡ h u + w.length [ZMOD d] ∧ ∀ i (hi : i < w.length), w[i] = lam ((h u + i) % d)

/-- **[Oda26] Lemma 12(b).**  A walk inside a set passing the phase test with `(h, d, λ)` has
output `y_{t₀+s} = λ((h(v₀) + s) mod d)`. -/
@[category research solved, AMS 05 37, ref "Oda26", group "oda26_wordgraph"]
theorem Covers.output_of_certified {E : Graph V α} {y : ℕ → α} {v : ℕ → V} {w : ℕ → List α}
    {t : ℕ → ℕ} (hc : Covers E y v w t) {S : V → Prop} {h : V → ℤ} {d : ℕ} {lam : ℤ → α}
    (hcert : ∀ u w v, E u w v → S u → S v →
      h v ≡ h u + w.length [ZMOD d] ∧ ∀ i (hi : i < w.length), w[i] = lam ((h u + i) % d))
    (hS : ∀ i, S (v i)) (s : ℕ) : y (t 0 + s) = lam ((h (v 0) + s) % d) := by
  have hph : ∀ i, h (v i) ≡ h (v 0) + ((t i - t 0 : ℕ) : ℤ) [ZMOD d] := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have h1 := (hcert _ _ _ (hc.edge i) (hS i) (hS (i + 1))).1
      have ht := hc.time i
      have hle := hc.le_t i
      have : ((t (i + 1) - t 0 : ℕ) : ℤ) = ((t i - t 0 : ℕ) : ℤ) + (w i).length := by omega
      rw [this, ← add_assoc]
      exact h1.trans (ih.add_right _)
  obtain ⟨i, k, hk, hik⟩ := hc.exists_seg s
  rw [← hik, hc.letter i k hk, (hcert _ _ _ (hc.edge i) (hS i) (hS (i + 1))).2 k hk]
  congr 1
  have hle := hc.le_t i
  have := (hph i).add_right (k : ℤ)
  rw [Int.ModEq] at this
  rw [this]
  congr 1
  omega

/-- **[Oda26] Lemma 7 / Lemma 12(b), periodicity.** -/
@[category research solved, AMS 05 37, ref "Oda26", group "oda26_wordgraph"]
theorem Covers.periodic_of_certified {E : Graph V α} {y : ℕ → α} {v : ℕ → V} {w : ℕ → List α}
    {t : ℕ → ℕ} (hc : Covers E y v w t) {S : V → Prop} (hcert : Certified E S)
    (hS : ∀ i, S (v i)) : IsEventuallyPeriodic y := by
  obtain ⟨h, d, lam, hd, hc'⟩ := hcert
  refine ⟨t 0, d, hd, fun k hk => ?_⟩
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [add_assoc, hc.output_of_certified hc' hS, hc.output_of_certified hc' hS]
  congr 1
  push_cast
  rw [← add_assoc, Int.add_emod_right]

/-- **[Oda26] Lemma 12(a), telescoping.**  Along a finite walk respecting the phase congruence
mod `d`, `h(v_m) ≡ h(v_0) + Σ|wᵢ| (mod d)`. -/
theorem phase_telescope {h : V → ℤ} {d : ℕ} (v : ℕ → V) (w : ℕ → List α) (m : ℕ)
    (hcong : ∀ i < m, h (v (i + 1)) ≡ h (v i) + (w i).length [ZMOD d]) :
    h (v m) ≡ h (v 0) + ∑ i ∈ Finset.range m, ((w i).length : ℤ) [ZMOD d] := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ← add_assoc]
    exact (hcong m (by omega)).trans ((ih fun i hi => hcong i (by omega)).add_right _)

/-- **[Oda26] Lemma 12(a).**  On a nonempty closed walk with nonempty words, some edge has
`δ(e) = h(u) + |w| − h(v) ≠ 0`; hence the gcd `d` of the `|δ(e)|` over a cyclic component is
positive, and (by `phase_telescope`) divides the length of every closed walk. -/
@[category research solved, AMS 05 37, ref "Oda26", group "oda26_wordgraph"]
theorem exists_delta_ne_zero (h : V → ℤ) (v : ℕ → V) (w : ℕ → List α) {m : ℕ} (hm : 0 < m)
    (hpos : ∀ i < m, 0 < (w i).length) (hclosed : v m = v 0) :
    ∃ i < m, h (v i) + (w i).length - h (v (i + 1)) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have := phase_telescope (h := h) (d := 0) v w m fun i hi => by
    rw [Int.ModEq, Nat.cast_zero, Int.emod_zero, Int.emod_zero]; linarith [hcon i hi]
  rw [hclosed, Int.ModEq, Nat.cast_zero, Int.emod_zero, Int.emod_zero] at this
  have h1 : 0 < ∑ i ∈ Finset.range m, ((w i).length : ℤ) :=
    Finset.sum_pos (fun i hi => by exact_mod_cast hpos i (Finset.mem_range.1 hi))
      ⟨0, Finset.mem_range.2 hm⟩
  omega

/-! ## Proposition 13: removal -/

/-- **Removal** `R(G)`: keep only the internal edges of components failing the phase test. -/
def removal (E : Graph V α) : Graph V α :=
  fun u w v => E u w v ∧ SameSCC E u v ∧ ¬ Certified E (SameSCC E u)

/-- **[Oda26] Proposition 13 (tail preservation under removal).**  If `G ⊨ n₀` for a word `y`
that is not eventually periodic, then `R(G) ⊨ n₁` for some `n₁ ≥ n₀`. -/
@[category research solved, AMS 05 37, ref "Oda26", group "oda26_wordgraph"]
theorem models_removal [Finite V] {E : Graph V α} {y : ℕ → α} (hy : ¬ IsEventuallyPeriodic y)
    {n₀ : ℕ} (h : Models E y n₀) : ∃ n₁, n₀ ≤ n₁ ∧ Models (removal E) y n₁ := by
  obtain ⟨v, w, t, hc, ht0⟩ := h
  obtain ⟨i₁, hi₁⟩ := eventually_sameSCC hc.edge
  set S := SameSCC E (v i₁)
  have hSeq : ∀ i, i₁ ≤ i → SameSCC E (v i) = S := by
    intro i hi
    funext x
    exact propext ⟨fun hx => (hi₁ i hi).trans hx, fun hx => (hi₁ i hi).symm.trans hx⟩
  have hnc : ¬ Certified E S := fun hcert =>
    hy ((hc.shift i₁).periodic_of_certified hcert fun i => hi₁ (i₁ + i) (by omega))
  refine ⟨t i₁, ht0 ▸ hc.mono (Nat.zero_le _), fun i => v (i₁ + i), fun i => w (i₁ + i),
    fun i => t (i₁ + i), ⟨fun i => ⟨hc.edge (i₁ + i), ?_, ?_⟩, fun i => hc.pos _,
    fun i => hc.time _, fun i => hc.word _⟩, by simp⟩
  · exact (hi₁ (i₁ + i) (by omega)).symm.trans (hi₁ (i₁ + i + 1) (by omega))
  · rw [hSeq (i₁ + i) (by omega)]; exact hnc

/-! ## Lemma 15 and Proposition 16: contraction -/

/-- A run from `u`: edges until the first vertex in `B`. -/
inductive Run (E : Graph V α) (B : V → Prop) : V → List α → V → Prop
  | last {u w v} : E u w v → B v → Run E B u w v
  | step {u w x W v} : E u w x → ¬ B x → Run E B x W v → Run E B u (w ++ W) v

/-- **The contraction** `P(G′)` on the macro vertices `B`: one edge per run between them. -/
def contract (E : Graph V α) (B : V → Prop) : Graph V α := fun u W v => B u ∧ Run E B u W v

/-- At most one out-edge (after merging identical triples). -/
def Det (E : Graph V α) (x : V) : Prop := ∀ w w' v v', E x w v → E x w' v' → w = w' ∧ v = v'

/-- **[Oda26] Lemma 15.**  If every vertex outside `B` has at most one out-edge and every
component all of whose vertices do contains a vertex of `B` (an anchor), then every infinite walk
visits `B` infinitely often. -/
@[category research solved, AMS 05 37, ref "Oda26", group "oda26_wordgraph"]
theorem visits_B {E : Graph V α} {B : V → Prop} (hdet : ∀ x, ¬ B x → Det E x)
    (hanchor : ∀ x, (∀ y, SameSCC E x y → Det E y) → ∃ y, SameSCC E x y ∧ B y)
    {v : ℕ → V} {w : ℕ → List α} (hedge : ∀ i, E (v i) (w i) (v (i + 1))) :
    ∀ N, ∃ i, N ≤ i ∧ B (v i) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨N, hN⟩ := hcon
  have follow : ∀ y, Reach E (v N) y → ∃ j, N ≤ j ∧ y = v j := by
    intro y hy
    induction hy with
    | refl => exact ⟨N, le_rfl, rfl⟩
    | tail _ hzy ih =>
      obtain ⟨j, hj, rfl⟩ := ih
      obtain ⟨w', hw'⟩ := hzy
      exact ⟨j + 1, by omega, (hdet _ (hN j hj) _ _ _ _ hw' (hedge j)).2⟩
  obtain ⟨y, hy, hBy⟩ := hanchor (v N) fun y hy => by
    obtain ⟨j, hj, rfl⟩ := follow y hy.1
    exact hdet _ (hN j hj)
  obtain ⟨j, hj, rfl⟩ := follow y hy.1
  exact hN j hj hBy

/-- `w i ++ w (i+1) ++ ⋯ ++ w (i+m−1)`. -/
def flat (w : ℕ → List α) : ℕ → ℕ → List α
  | _, 0 => []
  | i, m + 1 => w i ++ flat w (i + 1) m

theorem run_flat {E : Graph V α} {B : V → Prop} {v : ℕ → V} {w : ℕ → List α}
    (hedge : ∀ i, E (v i) (w i) (v (i + 1))) :
    ∀ m i, 0 < m → (∀ l, 0 < l → l < m → ¬ B (v (i + l))) → B (v (i + m)) →
      Run E B (v i) (flat w i m) (v (i + m)) := by
  intro m
  induction m with
  | zero => intro i h; omega
  | succ m ih =>
    intro i _ hgap hB
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [flat, List.append_nil]
      exact Run.last (hedge i) hB
    · simp only [flat]
      refine Run.step (hedge i) (by simpa using hgap 1 (by omega) (by omega)) ?_
      rw [show i + (m + 1) = i + 1 + m by ring] at hB ⊢
      exact ih (i + 1) hm (fun l hl1 hl2 => by
        rw [show i + 1 + l = i + (l + 1) by ring]; exact hgap (l + 1) (by omega) (by omega)) hB

theorem Covers.flat_spec {E : Graph V α} {y : ℕ → α} {v : ℕ → V} {w : ℕ → List α}
    {t : ℕ → ℕ} (hc : Covers E y v w t) :
    ∀ m i, t i + (flat w i m).length = t (i + m) ∧
      flat w i m = (List.range' (t i) (flat w i m).length).map y := by
  intro m
  induction m with
  | zero => intro i; simp [flat]
  | succ m ih =>
    intro i
    obtain ⟨h1, h2⟩ := ih (i + 1)
    have ht := hc.time i
    simp only [flat, List.length_append]
    refine ⟨by rw [show i + (m + 1) = i + 1 + m by ring]; omega, ?_⟩
    rw [← List.range'_append (step := 1), List.map_append, ← hc.word i, one_mul, ← ht, ← h2]

/-- **[Oda26] Proposition 16 (exactness of contraction), forward direction.**  If `G′ ⊨ n₁` by a
walk visiting `B` infinitely often, then `P(G′) ⊨ n₂` with `n₂` the first visit to `B`. -/
@[category research solved, AMS 05 37, ref "Oda26", group "oda26_wordgraph"]
theorem models_contract {E : Graph V α} {B : V → Prop} {y : ℕ → α} {v : ℕ → V}
    {w : ℕ → List α} {t : ℕ → ℕ} (hc : Covers E y v w t) (hB : ∀ N, ∃ i, N ≤ i ∧ B (v i)) :
    ∃ i₀, (∀ i < i₀, ¬ B (v i)) ∧ Models (contract E B) y (t i₀) := by
  classical
  let nxt : ℕ → ℕ := fun i => Nat.find (hB (i + 1))
  have hnxt : ∀ i, i + 1 ≤ nxt i ∧ B (v (nxt i)) := fun i => Nat.find_spec (hB (i + 1))
  have hgap : ∀ i l, i < l → l < nxt i → ¬ B (v l) := fun i l h1 h2 hl =>
    Nat.find_min (hB (i + 1)) h2 ⟨h1, hl⟩
  have hex0 : ∃ i, B (v i) := by obtain ⟨i, -, h⟩ := hB 0; exact ⟨i, h⟩
  let i₀ := Nat.find hex0
  let b : ℕ → ℕ := fun k => Nat.rec i₀ (fun _ j => nxt j) k
  have hb0 : b 0 = i₀ := rfl
  have hbs : ∀ k, b (k + 1) = nxt (b k) := fun k => rfl
  have hbB : ∀ k, B (v (b k)) := by
    intro k; cases k with
    | zero => exact Nat.find_spec hex0
    | succ k => rw [hbs]; exact (hnxt _).2
  refine ⟨i₀, fun i hi => Nat.find_min hex0 hi, fun k => v (b k),
    fun k => flat w (b k) (b (k + 1) - b k), fun k => t (b k), ⟨fun k => ?_, fun k => ?_,
    fun k => ?_, fun k => ?_⟩, rfl⟩
  · have hlt := (hnxt (b k)).1
    refine ⟨hbB k, ?_⟩
    have := run_flat (B := B) hc.edge (b (k + 1) - b k) (b k) (by rw [hbs]; omega)
      (fun l hl1 hl2 => hgap (b k) (b k + l) (by omega) (by rw [hbs] at hl2; omega))
      (by rw [show b k + (b (k + 1) - b k) = b (k + 1) by rw [hbs]; omega]; exact hbB (k + 1))
    rwa [show b k + (b (k + 1) - b k) = b (k + 1) by rw [hbs]; omega] at this
  · obtain ⟨m, hm⟩ : ∃ m, b (k + 1) - b k = m + 1 := ⟨b (k + 1) - b k - 1, by
      have := (hnxt (b k)).1; rw [hbs]; omega⟩
    rw [hm]; simp only [flat, List.length_append]
    have := hc.pos (b k); omega
  · have := (hc.flat_spec (b (k + 1) - b k) (b k)).1
    rwa [show b k + (b (k + 1) - b k) = b (k + 1) by
      have := (hnxt (b k)).1; rw [hbs]; omega, eq_comm] at this
  · exact (hc.flat_spec _ _).2

/-- **Contraction preserves coverings** (Lemma 15 + Proposition 16). -/
@[category research solved, AMS 05 37, ref "Oda26", group "oda26_wordgraph"]
theorem models_contract_of_anchor {E : Graph V α} {B : V → Prop} (hdet : ∀ x, ¬ B x → Det E x)
    (hanchor : ∀ x, (∀ y, SameSCC E x y → Det E y) → ∃ y, SameSCC E x y ∧ B y) {y : ℕ → α}
    {n₁ : ℕ} (h : Models E y n₁) : ∃ n₂, n₁ ≤ n₂ ∧ Models (contract E B) y n₂ := by
  obtain ⟨v, w, t, hc, ht0⟩ := h
  obtain ⟨i₀, -, hm⟩ := models_contract hc (visits_B hdet hanchor hc.edge)
  exact ⟨t i₀, ht0 ▸ hc.mono (Nat.zero_le _), hm⟩

/-! ## Proposition 17: lifting by a prime -/

/-- The residues `q₀ = q, q_{i+1} = b⁻¹(a qᵢ + cᵢ)` along a word, modulo `p`. -/
def liftRes (a b p : ℕ) (q : ZMod p) (w : List ℤ) : List (ZMod p) :=
  w.scanl (fun (r : ZMod p) (c : ℤ) => ((b : ZMod p))⁻¹ * (a * r + (c : ZMod p))) q

/-- **The lift** `Lift_p(G)`: vertices `(u, q)`, an edge when every residue along the word is
nonzero; the last residue is the residue of the target. -/
def lift (E : Graph V ℤ) (a b p : ℕ) : Graph (V × ZMod p) ℤ := fun x w x' =>
  E x.1 w x'.1 ∧ (∀ r ∈ liftRes a b p x.2 w, r ≠ 0) ∧ (liftRes a b p x.2 w).getLast? = some x'.2

theorem liftRes_orbit {a b p : ℕ} [Fact p.Prime] (hpb : ¬ (p : ℤ) ∣ b) {Q : ℕ → ℤ} {y : ℕ → ℤ}
    (hQ : ∀ n, (b : ℤ) * Q (n + 1) = a * Q n + y n) :
    ∀ ℓ n, liftRes a b p (Q n : ZMod p) ((List.range' n ℓ).map y) =
      (List.range' n (ℓ + 1)).map fun j => (Q j : ZMod p) := by
  have hb : ((b : ℤ) : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  intro ℓ
  induction ℓ with
  | zero => intro n; simp [liftRes]
  | succ ℓ ih =>
    intro n
    have hstep : ((b : ZMod p))⁻¹ * (a * (Q n : ZMod p) + y n) = (Q (n + 1) : ZMod p) := by
      have := congrArg (fun z : ℤ => (z : ZMod p)) (hQ n)
      push_cast at this hb
      rw [← this, ← mul_assoc, inv_mul_cancel₀ hb, one_mul]
    rw [List.range'_succ, List.map_cons, liftRes, List.scanl_cons, hstep, ← liftRes, ih,
      List.range'_succ (n := ℓ + 1), List.map_cons]

/-- **[Oda26] Proposition 17 (tail preservation under lifting).**  Let `p ∤ b` be prime, let
`b·Q_{n+1} = a·Qₙ + yₙ`, `G ⊨ n₀`, and `p ∤ Qₙ` for `n ≥ n'`.  Then `Lift_p(G) ⊨ n₁` for some
`n₁ ≥ max(n₀, n')`. -/
@[category research solved, AMS 05 11 37, ref "Oda26", group "oda26_wordgraph"]
theorem models_lift {E : Graph V ℤ} {a b p : ℕ} [Fact p.Prime] (hpb : ¬ (p : ℤ) ∣ b)
    {Q : ℕ → ℤ} {y : ℕ → ℤ} (hQ : ∀ n, (b : ℤ) * Q (n + 1) = a * Q n + y n) {n₀ n' : ℕ}
    (h : Models E y n₀) (hp : ∀ n, n' ≤ n → ¬ (p : ℤ) ∣ Q n) :
    ∃ n₁, n₀ ≤ n₁ ∧ n' ≤ n₁ ∧ Models (lift E a b p) y n₁ := by
  obtain ⟨v, w, t, hc, ht0⟩ := h
  have hle := hc.le_t n'
  refine ⟨t n', ht0 ▸ hc.mono (Nat.zero_le _), by omega, fun i => (v (n' + i), (Q (t (n' + i)))),
    fun i => w (n' + i), fun i => t (n' + i), ⟨fun i => ⟨hc.edge _, ?_, ?_⟩, fun i => hc.pos _,
    fun i => hc.time _, fun i => hc.word _⟩, rfl⟩
  · intro r hr
    rw [hc.word (n' + i), liftRes_orbit hpb hQ, List.mem_map] at hr
    obtain ⟨j, hj, rfl⟩ := hr
    rw [List.mem_range'_1] at hj
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have := hc.mono (show n' ≤ n' + i by omega)
    exact hp j (by omega)
  · rw [hc.word (n' + i), liftRes_orbit hpb hQ, List.getLast?_map, List.getLast?_range',
      if_neg (by omega), Option.map_some]
    show _ = some ((Q (t (n' + i + 1)) : ZMod p))
    rw [hc.time (n' + i)]
    congr 3

/-! ## Proposition 5 (`M = 1`): the cell graph -/

/-- **The cell graph** `G₀^in` on `K` cells with alphabet `C`, for the shift `ν`: an edge
`j —(c)→ k` iff `aj − b(k+1) < (c + (a−b)ν)K < a(j+1) − bk`.  [Oda26] is `ν = 0`
(`cellGraph_zero`). -/
def cellGraph (a b K : ℕ) (C : Set ℤ) (ν : ℝ) : Graph (Fin K) ℤ := fun j w k =>
  ∃ c ∈ C, w = [c] ∧ (a : ℝ) * (j : ℕ) - b * ((k : ℕ) + 1) < (c + ((a : ℝ) - b) * ν) * K ∧
    (c + ((a : ℝ) - b) * ν) * K < (a : ℝ) * ((j : ℕ) + 1) - b * (k : ℕ)

/-- At `ν = 0` the cell graph is [Oda26]'s integer one. -/
theorem cellGraph_zero (a b K : ℕ) (C : Set ℤ) (j k : Fin K) (w : List ℤ) :
    cellGraph a b K C 0 j w k ↔ ∃ c ∈ C, w = [c] ∧
      (a : ℤ) * (j : ℕ) - b * ((k : ℕ) + 1) < c * K ∧ c * K < (a : ℤ) * ((j : ℕ) + 1) - b * (k : ℕ) := by
  simp only [cellGraph, mul_zero, add_zero]
  constructor <;> rintro ⟨c, hc, rfl, h1, h2⟩ <;> exact ⟨c, hc, rfl, by exact_mod_cast h1, by exact_mod_cast h2⟩

variable {a b : ℕ} {ξ ν : ℝ}

/-- The cell `⌊Kθₙ⌋` of the orbit. -/
noncomputable def cell (a b K : ℕ) (hK : 0 < K) (ξ ν : ℝ) (n : ℕ) : Fin K :=
  ⟨(⌊(K : ℝ) * θf a b ξ ν n⌋).toNat, by
    have h1 := Int.fract_lt_one (Z32.orb a b ξ ν n)
    have h0 := Int.fract_nonneg (Z32.orb a b ξ ν n)
    have hK' : (0 : ℝ) < K := by exact_mod_cast hK
    have : ⌊(K : ℝ) * θf a b ξ ν n⌋ < K := by
      rw [Int.floor_lt]; push_cast
      exact mul_lt_of_lt_one_right hK' h1
    omega⟩

/-- **[Oda26] Proposition 5 for `M = 1`.**  If the carries lie in `C` from `n₀` on, the cell
graph covers them from `n₀`. -/
@[category research solved, AMS 11 37, ref "Oda26", group "oda26_wordgraph"]
theorem models_cellGraph (ha : 0 < a) (hb : 0 < b) {K : ℕ} (hK : 0 < K) {C : Set ℤ} {n₀ : ℕ}
    (hC : ∀ n, n₀ ≤ n → cf a b ξ ν n ∈ C) : Models (cellGraph a b K C ν) (cf a b ξ ν) n₀ := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hcell : ∀ n, ((cell a b K hK ξ ν n : ℕ) : ℝ) ≤ K * θf a b ξ ν n ∧
      K * θf a b ξ ν n < (cell a b K hK ξ ν n : ℕ) + 1 := by
    intro n
    have h0 := Int.fract_nonneg (Z32.orb a b ξ ν n)
    have hnn : 0 ≤ ⌊(K : ℝ) * θf a b ξ ν n⌋ := Int.floor_nonneg.2 (by positivity)
    have hcast : (((cell a b K hK ξ ν n : ℕ) : ℤ) : ℝ) = (⌊(K : ℝ) * θf a b ξ ν n⌋ : ℝ) := by
      simp only [cell]; rw [Int.toNat_of_nonneg hnn]
    push_cast at hcast
    rw [hcast]
    exact ⟨Int.floor_le _, Int.lt_floor_add_one _⟩
  refine ⟨fun i => cell a b K hK ξ ν (n₀ + i), fun i => [cf a b ξ ν (n₀ + i)], fun i => n₀ + i,
    ⟨fun i => ⟨_, hC _ (by omega), rfl, ?_, ?_⟩, fun i => by simp, fun i => by simp; ring,
    fun i => by simp [List.range'_succ]⟩, by simp⟩
  · have := cf_eq (a := a) (b := b) (ξ := ξ) (ν := ν) hb (n₀ + i)
    have h1 := hcell (n₀ + i); have h2 := hcell (n₀ + i + 1)
    have e : n₀ + (i + 1) = n₀ + i + 1 := rfl
    rw [e, this]
    have hb' : (0 : ℝ) < b := by exact_mod_cast hb
    have ha' : (0 : ℝ) ≤ a := by positivity
    nlinarith [mul_nonneg ha' (sub_nonneg.2 h1.1), mul_pos hb' (sub_pos.2 h2.2)]
  · have := cf_eq (a := a) (b := b) (ξ := ξ) (ν := ν) hb (n₀ + i)
    have h1 := hcell (n₀ + i); have h2 := hcell (n₀ + i + 1)
    have e : n₀ + (i + 1) = n₀ + i + 1 := rfl
    rw [e, this]
    have hb' : (0 : ℝ) < b := by exact_mod_cast hb
    have ha' : (0 : ℝ) ≤ a := by positivity
    nlinarith [mul_nonneg ha' (sub_nonneg.2 h1.2.le), mul_nonneg hb'.le (sub_nonneg.2 h2.1),
      mul_pos (show (0 : ℝ) < a by exact_mod_cast ha) (sub_pos.2 h1.2)]

end Oda.WG
