/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Oda26.NFGraphs

/-!
# The procedure `M₀` and the normal form of finite certificates ([Oda26] §7.2–7.4)

Everything is stated for an arbitrary shift `ν` (graphs of `⌊ξ(a/b)ⁿ + ν⌋`); [Oda26] is
`ν = 0`, so `Oda.WG.normal_form` at `ν = 0` is Theorem 37 and at other `ν` its shifted analogue.

A graph of an execution lives on the states `V(m, k) = Fin m × Fin k`; each edge `u —π→` records
its **expansion path** `π = [(e₀, u₁), …, (e_{L−1}, u_L)]` (labels and successive states), with word
`π.map fst` and target `u_L`.  The operations of [Oda26] §7.2:

* (I) `initG`: the complete one-step graph `G(M, K)`, or `G′(R, K)` (labels in `C(a, b)`; the
  modulus `N` of the conclusion must contain `R` and the primes of `2ab`);
* (P) `phaseG`: keep the edges internal to components of the word graph failing the phase test;
* (C) `contractG`: contraction on macro vertices `B` with the hypotheses of Lemma 15;
* (R), (L) `refineG`: all lifts of each expansion path whose steps are edges of `G(m', k')`;
* (A) `carryG`: labels restricted to `C(a, b)`, once all primes of `2ab` divide `N`.

`XExec a b ν full m k N Γ`: `Γ` is reachable; `full = false` is a *one-step execution* ((I) first form,
(P), (R), (L)).

* `Oda.WG.XExec.tracks` — **[Oda26] Lemma 30 (preservation)**, right-directed: a tail of every
  infinite walk of `G(M*, K*)` with non-eventually-periodic output becomes a walk of every graph of
  the execution, with expansion paths equal to the projected states.
* `Oda.WG.XExec.allCert` — **[Oda26] Theorem 33**: after a successful execution every cyclic SCC of
  the complete graph `G(M*, K*)` passes the phase test.
* `Oda.WG.normal_form` — **[Oda26] Theorem 37 (normal form)**: (1) some execution succeeds ⇔
  (2) some one-step execution succeeds ⇔ (3) every cyclic SCC of `G′(∏S, K)` passes the phase test,
  for some `K` and finite set `S` of primes not dividing `2ab` ⇔ (4) `a/b ∈ F_cert`.

Left-directed walks (the other half of Lemma 30) are not needed for Theorem 37 and are not
formalized.

## References

* [Oda26] Y. Odagiri, *Finite graph certificates for composite terms in rational floor sequences*,
  Zenodo, doi:10.5281/zenodo.22997709 (2026).
-/

namespace Oda.WG

open ForMathlib.SubwordComplexity

variable {a b : ℕ} {ν : ℝ}

/-- The states `V(m, k)`. -/
abbrev St (m k : ℕ) := Fin m × Fin k

/-- A word-labelled graph with expansion paths. -/
abbrev XGraph (m k : ℕ) := St m k → List (ℤ × St m k) → Prop

variable {m k : ℕ}

/-- The target of an expansion path from `u`. -/
def tgt (u : St m k) (π : List (ℤ × St m k)) : St m k := (π.getLast?.map Prod.snd).getD u

/-- The underlying word-labelled graph. -/
def wg (Γ : XGraph m k) : Graph (St m k) ℤ :=
  fun u w v => ∃ π, Γ u π ∧ w = π.map Prod.fst ∧ tgt u π = v

/-- (I) The initial graph `G(m, k)`, or `G′(m, k)` when `alph`. -/
def initG (a b : ℕ) (ν : ℝ) (m k : ℕ) (alph : Bool) : XGraph m k := fun u π =>
  ∃ e v, π = [(e, v)] ∧ oneStepU a b ν m k u [e] v ∧ (alph = true → carryAlphabet a b ν e)

/-- (P) Phase removal. -/
def phaseG (Γ : XGraph m k) : XGraph m k :=
  fun u π => Γ u π ∧ removal (wg Γ) u (π.map Prod.fst) (tgt u π)

/-- Runs of expansion paths until the first vertex of `B`. -/
inductive XRun (Γ : XGraph m k) (B : St m k → Prop) : St m k → List (ℤ × St m k) → Prop
  | last {u π} : Γ u π → B (tgt u π) → XRun Γ B u π
  | step {u π π'} : Γ u π → ¬ B (tgt u π) → XRun Γ B (tgt u π) π' → XRun Γ B u (π ++ π')

/-- (C) Contraction on the macro vertices `B`; expansion paths are concatenated. -/
def contractG (Γ : XGraph m k) (B : St m k → Prop) : XGraph m k := fun u π => B u ∧ XRun Γ B u π

/-- Every step of the path from `u` is an edge of `E`. -/
def Steps {V : Type*} (E : Graph V ℤ) : V → List (ℤ × V) → Prop
  | _, [] => True
  | u, (e, v) :: π => E u [e] v ∧ Steps E v π

/-- (R), (L) Refinement of cells and enlargement of the modulus: all paths of `G(m', k')` whose
projection is an expansion path of `Γ`. -/
def refineG (a b : ℕ) (ν : ℝ) {m' k' : ℕ} (hm : m ∣ m') (hk : k ∣ k') (Γ : XGraph m k) : XGraph m' k' :=
  fun u π => Γ (proj hm hk u) (π.map fun x => (x.1, proj hm hk x.2)) ∧
    Steps (oneStepU a b ν m' k') u π

/-- (A) Carry restriction. -/
def carryG (a b : ℕ) (ν : ℝ) (Γ : XGraph m k) : XGraph m k :=
  fun u π => Γ u π ∧ ∀ x ∈ π, carryAlphabet a b ν x.1

/-- **Executions of `M₀`** ([Oda26] §7.2).  `XExec a b ν full m k N Γ`: the graph `Γ` on `V(m, k)` is
reached, and its conclusion concerns the modulus `N`.  With `full = false`, only (I) first form,
(P), (R), (L) are allowed: a *one-step execution*. -/
inductive XExec (a b : ℕ) (ν : ℝ) (full : Bool) : (m k N : ℕ) → XGraph m k → Prop
  | init (M K : ℕ) (hM : 0 < M) (hK : 0 < K) : XExec a b ν full M K M (initG a b ν M K false)
  | init' (R K N : ℕ) (hfull : full = true) (hK : 0 < K) (hN : 0 < N) (hRN : R ∣ N)
      (h2ab : ∀ p, p.Prime → p ∣ 2 * a * b → p ∣ N) : XExec a b ν full R K N (initG a b ν R K true)
  | phase {m k N : ℕ} {Γ : XGraph m k} : XExec a b ν full m k N Γ → XExec a b ν full m k N (phaseG Γ)
  | contract {m k N : ℕ} {Γ : XGraph m k} (B : St m k → Prop) (hfull : full = true) :
      XExec a b ν full m k N Γ → (∀ x, ¬ B x → Det (wg Γ) x) →
      (∀ x, (∀ y, SameSCC (wg Γ) x y → Det (wg Γ) y) → ∃ y, SameSCC (wg Γ) x y ∧ B y) →
      XExec a b ν full m k N (contractG Γ B)
  | refine {m k N : ℕ} {Γ : XGraph m k} (f : ℕ) (hf : 0 < f) : XExec a b ν full m k N Γ →
      XExec a b ν full m (k * f) N (refineG a b ν (dvd_refl m) (Dvd.intro f rfl) Γ)
  | lift {m k N : ℕ} {Γ : XGraph m k} (h : ℕ) (hh : 0 < h) : XExec a b ν full m k N Γ →
      XExec a b ν full (h * m) k (h * N) (refineG a b ν (Dvd.intro_left h rfl) (dvd_refl k) Γ)
  | carry {m k N : ℕ} {Γ : XGraph m k} (hfull : full = true)
      (hN : ∀ p, p.Prime → p ∣ 2 * a * b → p ∣ N) :
      XExec a b ν full m k N Γ → XExec a b ν full m k N (carryG a b ν Γ)

theorem XExec.inv {full : Bool} {N : ℕ} {Γ : XGraph m k} (h : XExec a b ν full m k N Γ) :
    m ∣ N ∧ 0 < N ∧ 0 < k := by
  induction h with
  | init M K hM hK => exact ⟨dvd_refl M, hM, hK⟩
  | init' R K N _ hK hN hRN => exact ⟨hRN, hN, hK⟩
  | phase _ ih => exact ih
  | contract _ _ _ _ _ ih => exact ih
  | refine f hf _ ih => exact ⟨ih.1, ih.2.1, Nat.mul_pos ih.2.2 hf⟩
  | lift h hh _ ih => exact ⟨mul_dvd_mul_left h ih.1, Nat.mul_pos hh ih.2.1, ih.2.2⟩
  | carry _ _ _ ih => exact ih

/-- A one-step execution is an execution. -/
theorem XExec.mono {N : ℕ} {Γ : XGraph m k} (h : XExec a b ν false m k N Γ) :
    XExec a b ν true m k N Γ := by
  induction h with
  | init M K hM hK => exact .init M K hM hK
  | init' _ _ _ hfull => exact absurd hfull Bool.false_ne_true
  | phase _ ih => exact .phase ih
  | contract _ hfull => exact absurd hfull Bool.false_ne_true
  | refine f hf _ ih => exact .refine f hf ih
  | lift h hh _ ih => exact .lift h hh ih
  | carry hfull => exact absurd hfull Bool.false_ne_true

/-! ## Tracking a walk -/

/-- The expansion path of the times `n, …, n + L − 1`. -/
def seg (c : ℕ → ℤ) (p : ℕ → St m k) (n L : ℕ) : List (ℤ × St m k) :=
  (List.range' n L).map fun i => (c i, p (i + 1))

theorem tgt_seg (c : ℕ → ℤ) (p : ℕ → St m k) (n L : ℕ) (u : St m k) (hL : 0 < L) :
    tgt u (seg c p n L) = p (n + L) := by
  obtain ⟨L, rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  simp only [tgt, seg, List.range'_concat, List.map_append, List.map_cons, List.map_nil,
    List.getLast?_concat, Option.map_some, Option.getD_some]
  congr 1; omega

theorem seg_fst (c : ℕ → ℤ) (p : ℕ → St m k) (n L : ℕ) :
    (seg c p n L).map Prod.fst = (List.range' n L).map c := by
  simp [seg, Function.comp_def]

theorem seg_add (c : ℕ → ℤ) (p : ℕ → St m k) (n L₁ L₂ : ℕ) :
    seg c p n (L₁ + L₂) = seg c p n L₁ ++ seg c p (n + L₁) L₂ := by
  simp only [seg, ← List.map_append, List.range'_append_1]

theorem seg_map {m' k' : ℕ} (c : ℕ → ℤ) (p : ℕ → St m k) (f : St m k → St m' k') (n L : ℕ) :
    (seg c p n L).map (fun x => (x.1, f x.2)) = seg c (fun i => f (p i)) n L := by
  simp [seg, Function.comp_def]

theorem steps_seg {V : Type*} {E : Graph V ℤ} {c : ℕ → ℤ} {p : ℕ → V}
    (h : ∀ i, E (p i) [c i] (p (i + 1))) : ∀ L n,
      Steps E (p n) ((List.range' n L).map fun i => (c i, p (i + 1)))
  | 0, n => by simp [Steps]
  | L + 1, n => by
    rw [List.range'_succ, List.map_cons]
    exact ⟨h n, steps_seg h L (n + 1)⟩

/-- A tail of the walk `(p, c)` is a walk of `Γ` whose expansion paths are the segments of `p`. -/
def Tracks (Γ : XGraph m k) (c : ℕ → ℤ) (p : ℕ → St m k) : Prop :=
  ∃ τ : ℕ → ℕ, (∀ i, τ i < τ (i + 1)) ∧ ∀ i, Γ (p (τ i)) (seg c p (τ i) (τ (i + 1) - τ i))

theorem Tracks.covers {Γ : XGraph m k} {c : ℕ → ℤ} {p : ℕ → St m k} {τ : ℕ → ℕ}
    (hτ : ∀ i, τ i < τ (i + 1)) (hΓ : ∀ i, Γ (p (τ i)) (seg c p (τ i) (τ (i + 1) - τ i))) :
    Covers (wg Γ) c (fun i => p (τ i)) (fun i => (List.range' (τ i) (τ (i + 1) - τ i)).map c)
      τ := by
  refine ⟨fun i => ⟨_, hΓ i, (seg_fst _ _ _ _).symm, ?_⟩, fun i => ?_, fun i => ?_,
    fun i => by simp⟩
  · rw [tgt_seg _ _ _ _ _ (by have := hτ i; omega)]; congr 1; have := hτ i; omega
  · simp; have := hτ i; omega
  · simp; have := hτ i; omega

/-! ## Lemma 30: the operations are walk-sound (right-directed) -/

theorem tracks_init {M K : ℕ} (hm : m ∣ M) (hk : k ∣ K) {s : ℕ → St M K} {c : ℕ → ℤ}
    (hs : ∀ n, oneStepU a b ν M K (s n) [c n] (s (n + 1))) (alph : Bool)
    (hC : alph = true → ∀ j, carryAlphabet a b ν (c j)) :
    Tracks (initG a b ν m k alph) c (fun n => proj hm hk (s n)) :=
  ⟨fun i => i, fun i => Nat.lt_succ_self i, fun i => ⟨c i, proj hm hk (s (i + 1)),
    by simp [seg], proj_edge hm hk (hs i), fun h => hC h i⟩⟩

theorem tracks_phase {Γ : XGraph m k} {c : ℕ → ℤ} {p : ℕ → St m k}
    (hc : ¬ IsEventuallyPeriodic c) (h : Tracks Γ c p) : Tracks (phaseG Γ) c p := by
  obtain ⟨τ, hτ, hΓ⟩ := h
  have hcov := Tracks.covers hτ hΓ
  obtain ⟨i₁, hi₁⟩ := eventually_sameSCC (E := wg Γ) (v := fun i => p (τ i)) hcov.edge
  set S := SameSCC (wg Γ) (p (τ i₁))
  have hSeq : ∀ i, i₁ ≤ i → SameSCC (wg Γ) (p (τ i)) = S := by
    intro i hi
    funext x
    exact propext ⟨fun hx => (hi₁ i hi).trans hx, fun hx => (hi₁ i hi).symm.trans hx⟩
  have hnc : ¬ Certified (wg Γ) S := fun hcert =>
    hc ((hcov.shift i₁).periodic_of_certified hcert fun i => hi₁ (i₁ + i) (by omega))
  refine ⟨fun i => τ (i₁ + i), fun i => hτ _, fun i => ⟨hΓ (i₁ + i), ⟨_, hΓ (i₁ + i), rfl, rfl⟩,
    ?_, ?_⟩⟩
  · beta_reduce
    rw [show i₁ + (i + 1) = i₁ + i + 1 by ring]
    rw [tgt_seg _ _ _ _ _ (by have := hτ (i₁ + i); omega),
      show τ (i₁ + i) + (τ (i₁ + i + 1) - τ (i₁ + i)) = τ (i₁ + i + 1) by
        have := hτ (i₁ + i); omega]
    exact (hi₁ (i₁ + i) (by omega)).symm.trans (hi₁ (i₁ + i + 1) (by omega))
  · rw [hSeq (i₁ + i) (by omega)]; exact hnc

theorem xrun_seg {Γ : XGraph m k} {B : St m k → Prop} {c : ℕ → ℤ} {p : ℕ → St m k}
    {τ : ℕ → ℕ} (hτ : ∀ i, τ i < τ (i + 1))
    (hΓ : ∀ i, Γ (p (τ i)) (seg c p (τ i) (τ (i + 1) - τ i))) :
    ∀ m i, 0 < m → (∀ l, 0 < l → l < m → ¬ B (p (τ (i + l)))) → B (p (τ (i + m))) →
      XRun Γ B (p (τ i)) (seg c p (τ i) (τ (i + m) - τ i)) := by
  have hmono := strictMono_nat_of_lt_succ hτ
  have ht : ∀ i, tgt (p (τ i)) (seg c p (τ i) (τ (i + 1) - τ i)) = p (τ (i + 1)) := fun i => by
    rw [tgt_seg _ _ _ _ _ (by have := hτ i; omega)]; congr 1; have := hτ i; omega
  intro m
  induction m with
  | zero => intro i h; omega
  | succ m ih =>
    intro i _ hgap hB
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact XRun.last (hΓ i) (by rw [ht]; exact hB)
    · have hle := hmono.monotone (show i + 1 ≤ i + 1 + m by omega)
      have e : τ (i + (m + 1)) - τ i = (τ (i + 1) - τ i) + (τ (i + 1 + m) - τ (i + 1)) := by
        rw [show i + (m + 1) = i + 1 + m by ring]; have := hτ i; omega
      rw [e, seg_add, show τ i + (τ (i + 1) - τ i) = τ (i + 1) by have := hτ i; omega]
      refine XRun.step (hΓ i) (by rw [ht]; exact hgap 1 (by omega) (by omega)) ?_
      rw [ht]
      refine ih (i + 1) hm (fun l hl1 hl2 => ?_) ?_
      · rw [show i + 1 + l = i + (l + 1) by ring]; exact hgap (l + 1) (by omega) (by omega)
      · rw [show i + 1 + m = i + (m + 1) by ring]; exact hB

theorem tracks_contract {Γ : XGraph m k} {B : St m k → Prop} {c : ℕ → ℤ} {p : ℕ → St m k}
    (hdet : ∀ x, ¬ B x → Det (wg Γ) x)
    (hanchor : ∀ x, (∀ y, SameSCC (wg Γ) x y → Det (wg Γ) y) → ∃ y, SameSCC (wg Γ) x y ∧ B y)
    (h : Tracks Γ c p) : Tracks (contractG Γ B) c p := by
  classical
  obtain ⟨τ, hτ, hΓ⟩ := h
  have hmono := strictMono_nat_of_lt_succ hτ
  have hB := visits_B hdet hanchor (Tracks.covers hτ hΓ).edge
  let nxt : ℕ → ℕ := fun i => Nat.find (hB (i + 1))
  have hnxt : ∀ i, i + 1 ≤ nxt i ∧ B (p (τ (nxt i))) := fun i => Nat.find_spec (hB (i + 1))
  have hgap : ∀ i l, i < l → l < nxt i → ¬ B (p (τ l)) := fun i l h1 h2 hl =>
    Nat.find_min (hB (i + 1)) h2 ⟨h1, hl⟩
  obtain ⟨i₀, -, hi₀⟩ := hB 0
  let bs : ℕ → ℕ := fun j => Nat.rec i₀ (fun _ i => nxt i) j
  have hbs : ∀ j, bs (j + 1) = nxt (bs j) := fun j => rfl
  have hbB : ∀ j, B (p (τ (bs j))) := by
    intro j; cases j with
    | zero => exact hi₀
    | succ j => rw [hbs]; exact (hnxt _).2
  refine ⟨fun j => τ (bs j), fun j => hmono (by rw [hbs]; have := (hnxt (bs j)).1; omega),
    fun j => ⟨hbB j, ?_⟩⟩
  have hlt := (hnxt (bs j)).1
  have := xrun_seg (B := B) hτ hΓ (bs (j + 1) - bs j) (bs j) (by rw [hbs]; omega)
    (fun l hl1 hl2 => hgap (bs j) (bs j + l) (by omega) (by rw [hbs] at hl2; omega))
    (by rw [show bs j + (bs (j + 1) - bs j) = bs (j + 1) by rw [hbs]; omega]; exact hbB (j + 1))
  rwa [show bs j + (bs (j + 1) - bs j) = bs (j + 1) by rw [hbs]; omega] at this

theorem tracks_refine {m' k' M K : ℕ} (hm : m ∣ m') (hk : k ∣ k') (hm' : m' ∣ M) (hk' : k' ∣ K)
    {Γ : XGraph m k} {s : ℕ → St M K} {c : ℕ → ℤ}
    (hs : ∀ n, oneStepU a b ν M K (s n) [c n] (s (n + 1)))
    (h : Tracks Γ c (fun n => proj (hm.trans hm') (hk.trans hk') (s n))) :
    Tracks (refineG a b ν hm hk Γ) c (fun n => proj hm' hk' (s n)) := by
  obtain ⟨τ, hτ, hΓ⟩ := h
  refine ⟨τ, hτ, fun i => ⟨?_, steps_seg (c := c) (p := fun n => proj hm' hk' (s n))
    (fun n => proj_edge hm' hk' (hs n)) _ _⟩⟩
  rw [seg_map]
  simp only [proj_proj]
  exact hΓ i

theorem tracks_carry {Γ : XGraph m k} {c : ℕ → ℤ} {p : ℕ → St m k}
    (hC : ∀ j, carryAlphabet a b ν (c j)) (h : Tracks Γ c p) : Tracks (carryG a b ν Γ) c p := by
  obtain ⟨τ, hτ, hΓ⟩ := h
  refine ⟨τ, hτ, fun i => ⟨hΓ i, fun x hx => ?_⟩⟩
  simp only [seg, List.mem_map] at hx
  obtain ⟨j, -, rfl⟩ := hx
  exact hC j

/-- **[Oda26] Lemma 30 (preservation), right-directed walks.**  For an execution with final
parameters `(m, k, N)` and a walk of `G(M, K)` (`N ∣ M`, `k ∣ K`) with non-eventually-periodic
output, a tail of the projected walk is a walk of `Γ` with expansion paths equal to its segments. -/
@[category research solved, AMS 05 11, ref "Oda26", group "oda26_normalform"]
theorem XExec.tracks (hcop : Nat.Coprime a b) {full : Bool} {N : ℕ} {Γ : XGraph m k}
    (hE : XExec a b ν full m k N Γ) {M K : ℕ} {s : ℕ → St M K} {c : ℕ → ℤ}
    (hs : ∀ n, oneStepU a b ν M K (s n) [c n] (s (n + 1))) (hc : ¬ IsEventuallyPeriodic c) :
    ∀ (_ : N ∣ M) (hkK : k ∣ K) (hm : m ∣ M), Tracks Γ c (fun n => proj hm hkK (s n)) := by
  have hC : ∀ {N}, (∀ p, p.Prime → p ∣ 2 * a * b → p ∣ N) → N ∣ M →
      ∀ j, carryAlphabet a b ν (c j) := fun h2ab hNM j =>
    label_mem_alphabet hcop ((h2ab 2 Nat.prime_two (by rw [mul_assoc]; exact dvd_mul_right 2 _)).trans
      hNM) (fun p hp h => (h2ab p hp (by rw [mul_assoc]; exact dvd_mul_of_dvd_right h 2)).trans hNM)
      (hs j)
  induction hE with
  | init M' K' _ _ => intro _ hkK hm; exact tracks_init hm hkK hs false (by simp)
  | init' R K' N' _ _ _ _ h2ab =>
    intro hNM hkK hm; exact tracks_init hm hkK hs true fun _ => hC h2ab hNM
  | phase _ ih => intro hNM hkK hm; exact tracks_phase hc (ih hNM hkK hm)
  | contract B _ _ hdet hanch ih => intro hNM hkK hm; exact tracks_contract hdet hanch (ih hNM hkK hm)
  | refine f _ _ ih =>
    intro hNM hkK hm
    exact tracks_refine (dvd_refl _) (Dvd.intro f rfl) hm hkK hs
      (ih hNM ((Dvd.intro f rfl).trans hkK) hm)
  | lift h _ _ ih =>
    intro hNM hkK hm
    exact tracks_refine (Dvd.intro_left h rfl) (dvd_refl _) hm hkK hs
      (ih ((Dvd.intro_left h rfl).trans hNM) hkK ((Dvd.intro_left h rfl).trans hm))
  | carry _ hN _ ih =>
    intro hNM hkK hm; exact tracks_carry (hC hN hNM) (ih hNM hkK hm)

/-! ## Theorem 33 -/

/-- A walk of a one-step graph reads one letter per step. -/
theorem Covers.oneStep {M K : ℕ} {y : ℕ → ℤ} {v : ℕ → St M K} {w : ℕ → List ℤ} {t : ℕ → ℕ}
    (hcov : Covers (oneStepU a b ν M K) y v w t) : ∀ i, w i = [y (t 0 + i)] ∧ t i = t 0 + i := by
  have key : ∀ i, w i = [y (t i)] := fun i => by
    obtain ⟨-, -, e, he, -⟩ := hcov.edge i
    have := hcov.letter i 0 (by rw [he]; simp)
    simp only [he, add_zero, List.getElem_cons_zero] at this
    rw [he, this]
  have ht : ∀ i, t i = t 0 + i := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [hcov.time i, key i, ih]; simp; omega
  exact fun i => ⟨by rw [key, ht], ht i⟩

/-- **[Oda26] Theorem 33 (contraction does not enlarge the class), walk form.**  If an execution
with final parameters `(m, k, N)` succeeds (`Γ = ∅`), every infinite walk of `G(M, K)` with
`N ∣ M`, `k ∣ K` has eventually periodic output. -/
theorem XExec.allPer (hcop : Nat.Coprime a b) {full : Bool} {N : ℕ} {Γ : XGraph m k}
    (hE : XExec a b ν full m k N Γ) (hempty : ∀ u π, ¬ Γ u π) {M K : ℕ} (hNM : N ∣ M)
    (hkK : k ∣ K) : AllPer (oneStepU a b ν M K) := by
  intro y v w t hcov
  by_contra hy
  have hw := hcov.oneStep
  have hs : ∀ n, oneStepU a b ν M K (v n) [y (t 0 + n)] (v (n + 1)) := fun n =>
    (hw n).1 ▸ hcov.edge n
  have hc : ¬ IsEventuallyPeriodic fun n => y (t 0 + n) := fun ⟨N₀, p, hp, h⟩ =>
    hy ⟨t 0 + N₀, p, hp, fun j hj => by
      have := h (j - t 0) (by omega)
      simp only at this
      rwa [show t 0 + (j - t 0 + p) = j + p by omega, show t 0 + (j - t 0) = j by omega] at this⟩
  obtain ⟨τ, -, hΓ⟩ := hE.tracks hcop hs hc hNM hkK (hE.inv.1.trans hNM)
  exact hempty _ _ (hΓ 0)

/-- **[Oda26] Theorem 33.**  After a successful execution with final parameters `(m, k, N)`, every
cyclic SCC of the complete one-step graph `G(M, K)` (`N ∣ M`, `k ∣ K`) passes the phase test. -/
@[category research solved, AMS 05 11, ref "Oda26", group "oda26_normalform"]
theorem XExec.allCert (hcop : Nat.Coprime a b) {full : Bool} {N : ℕ} {Γ : XGraph m k}
    (hE : XExec a b ν full m k N Γ) (hempty : ∀ u π, ¬ Γ u π) {M K : ℕ} (hNM : N ∣ M)
    (hkK : k ∣ K) : AllCert (oneStepU a b ν M K) :=
  (allCert_iff_allPer oneStepU_pos).2 (hE.allPer hcop hempty hNM hkK)

/-! ## Theorem 37 -/

theorem wg_initG (M K : ℕ) : wg (initG a b ν M K false) = oneStepU a b ν M K := by
  funext u w v
  apply propext
  constructor
  · rintro ⟨π, ⟨e, v', rfl, hE, -⟩, rfl, rfl⟩
    simpa [tgt] using hE
  · intro h
    obtain ⟨-, -, e, rfl, -⟩ := id h
    exact ⟨[(e, v)], ⟨e, v, rfl, h, by simp⟩, rfl, by simp [tgt]⟩

/-- **The class `F_cert`** of finitely certifiable bases ([Oda26] §7.4): for some `K` and finite
set `S` of primes not dividing `2ab`, closed words commute in every cyclic SCC of `G′(∏S, K)`
(Theorem 21(c)); here for the shift `ν`. -/
def Fcert (a b : ℕ) (ν : ℝ) : Prop :=
  2 ≤ b ∧ b < a ∧ Nat.Coprime a b ∧ ∃ (K : ℕ) (S : Finset ℕ), 0 < K ∧
    (∀ p ∈ S, p.Prime ∧ ¬ p ∣ 2 * a * b) ∧
    ∀ x W W', PathIn (gPrime a b ν (∏ p ∈ S, p) K) (SameSCC (gPrime a b ν (∏ p ∈ S, p) K) x) x W x →
      PathIn (gPrime a b ν (∏ p ∈ S, p) K) (SameSCC (gPrime a b ν (∏ p ∈ S, p) K) x) x W' x →
      W ++ W' = W' ++ W

/-- **[Oda26] Theorem 37 (normal form).**  For a reduced base `a/b` (`a > b ≥ 2`) the following
are equivalent: (1) some execution of `M₀` succeeds; (2) some one-step execution succeeds;
(3) for some `K > 0` and finite set `S` of primes not dividing `2ab`, every cyclic SCC of
`G′(∏S, K)` passes the phase test; (4) `a/b ∈ F_cert`.  Stated for every shift `ν` (all graphs
those of `⌊ξ(a/b)ⁿ + ν⌋`); [Oda26] is `ν = 0`. -/
@[category research solved, AMS 05 11, ref "Oda26", group "oda26_normalform"]
theorem normal_form (hb : 2 ≤ b) (hab : b < a) (hcop : Nat.Coprime a b) :
    List.TFAE [∃ m k N, ∃ Γ : XGraph m k, XExec a b ν true m k N Γ ∧ ∀ u π, ¬ Γ u π,
      ∃ m k N, ∃ Γ : XGraph m k, XExec a b ν false m k N Γ ∧ ∀ u π, ¬ Γ u π,
      ∃ (K : ℕ) (S : Finset ℕ), 0 < K ∧ (∀ p ∈ S, p.Prime ∧ ¬ p ∣ 2 * a * b) ∧
        AllCert (gPrime a b ν (∏ p ∈ S, p) K),
      Fcert a b ν] := by
  have ha0 : 0 < a := by omega
  have hb0 : 0 < b := by omega
  have key : ∀ R K, AllCert (gPrime a b ν R K) ↔ ∀ x W W',
      PathIn (gPrime a b ν R K) (SameSCC (gPrime a b ν R K) x) x W x →
      PathIn (gPrime a b ν R K) (SameSCC (gPrime a b ν R K) x) x W' x → W ++ W' = W' ++ W :=
    fun R K => forall_congr' fun x => (all_edge_test gPrime_pos
      (fun u v hu hv => pathIn_of_reach (hu.2.trans hv.1) hu hv)
      ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩).out 1 3
  tfae_have 2 → 1 := fun ⟨m, k, N, Γ, hE, he⟩ => ⟨m, k, N, Γ, hE.mono, he⟩
  tfae_have 1 → 3 := by
    rintro ⟨m, k, N, Γ, hE, hemp⟩
    obtain ⟨-, hN, hk⟩ := hE.inv
    let S := N.primeFactors.filter fun p => ¬ p ∣ 2 * a * b
    have hSp : ∀ p ∈ S, p.Prime ∧ ¬ p ∣ 2 * a * b := fun p hp => by
      simp only [S, Finset.mem_filter, Nat.mem_primeFactors] at hp; exact ⟨hp.1.1, hp.2⟩
    have hRN : (∏ p ∈ S, p) ∣ N := (Finset.prod_dvd_prod_of_subset _ _ _
      (Finset.filter_subset _ _)).trans (Nat.prod_primeFactors_dvd N)
    have hRab : Nat.Coprime (∏ p ∈ S, p) (2 * a * b) :=
      Nat.Coprime.prod_left fun p hp => (hSp p hp).1.coprime_iff_not_dvd.2 (hSp p hp).2
    have hM : 0 < 2 * a * b * N := by positivity
    refine ⟨k, S, hk, hSp, (allCert_iff_allPer gPrime_pos).2 ?_⟩
    refine allPer_gPrime_of_allPer hcop (hRN.trans (dvd_mul_left _ _)) hM hRab ?_
      (hE.allPer hcop hemp (dvd_mul_left _ _) (dvd_refl k))
    intro p hp hpM
    rcases (Nat.Prime.dvd_mul hp).1 hpM with h | h
    · exact dvd_mul_of_dvd_left h _
    · by_cases h2 : p ∣ 2 * a * b
      · exact dvd_mul_of_dvd_left h2 _
      · exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _
          (by simp only [S, Finset.mem_filter, Nat.mem_primeFactors]; exact ⟨⟨hp, h, hN.ne'⟩, h2⟩))
          _
  tfae_have 3 → 2 := by
    rintro ⟨K, S, hK, hSp, hcert⟩
    have hR : 0 < ∏ p ∈ S, p := Finset.prod_pos fun p hp => (hSp p hp).1.pos
    have hM : 0 < 2 * a * b * ∏ p ∈ S, p := by positivity
    have hper : AllPer (oneStepU a b ν (2 * a * b * ∏ p ∈ S, p) K) :=
      allPer_of_allPer_gPrime hcop (dvd_mul_left _ _) ⟨a * b * ∏ p ∈ S, p, by ring⟩
        (fun p _ h => dvd_mul_of_dvd_left (by rw [mul_assoc]; exact dvd_mul_of_dvd_right h 2) _)
        ((allCert_iff_allPer gPrime_pos).1 hcert)
    have hc := (allCert_iff_allPer oneStepU_pos).2 hper
    refine ⟨_, K, _, _, XExec.phase (XExec.init _ K hM hK), ?_⟩
    rintro u π ⟨-, -, -, hnc⟩
    rw [wg_initG] at hnc
    exact hnc (hc u)
  tfae_have 3 ↔ 4 := by
    constructor
    · rintro ⟨K, S, hK, hSp, hc⟩
      exact ⟨hb, hab, hcop, K, S, hK, hSp, (key _ _).1 hc⟩
    · rintro ⟨-, -, -, K, S, hK, hSp, hc⟩
      exact ⟨K, S, hK, hSp, (key _ _).2 hc⟩
  tfae_finish

end Oda.WG
