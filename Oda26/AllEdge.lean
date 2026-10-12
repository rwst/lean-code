/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Oda26.WordGraph
import ForMathlib.Combinatorics.FineWilf
import Mathlib.Tactic.TFAE
import Mathlib.Data.List.GetD

/-!
# The all-edge test and commuting closed words ([Oda26] §4.6, Theorem 21, Corollary 22)

For a strongly connected set `C` of a word-labelled graph with root `ρ ∈ C`, the following are
equivalent ([Oda26] Theorem 21):

* (a) `C` passes the weighted phase test (19) — and then it passes it for the *root path lengths*
  `h(v) = |out(π_v)|` of any choice of paths `π_v : ρ → v` inside `C`;
* (b) every infinite walk inside `C` has eventually periodic output;
* (c) any two closed output words at `ρ` commute.

Hence the test with root path lengths is *complete*: a component failing it carries an internal
walk with non-eventually-periodic output.

* `Oda.WG.models_of_paths` — gluing infinitely many finite paths into one covering walk.
* `Oda.WG.models_of_contract` — **[Oda26] Proposition 16, converse**: every infinite walk of the
  contraction comes from one of the original graph with the same output.
* `Oda.WG.all_edge_test` — **[Oda26] Theorem 21** (as `List.TFAE`), with
  `Oda.WG.certified_rootPath` the "moreover" clause.
* `Oda.WG.dvd_delta_iff` — **[Oda26] Corollary 22**: for root path lengths, `n` divides every
  `δ(e)` iff `n` divides the length of every closed walk (so `d = g_C`), and
  `Oda.WG.certified_rootPath_iff` — the test does not depend on the root or the paths.

## References

* [Oda26] Y. Odagiri, *Finite graph certificates for composite terms in rational floor sequences*,
  Zenodo, doi:10.5281/zenodo.22997709 (2026).
-/

namespace Oda.WG

open ForMathlib.SubwordComplexity

variable {V α : Type*}

/-! ## List lemmas -/

theorem eq_map_range'_iff {l : List α} {y : ℕ → α} {s : ℕ} :
    l = (List.range' s l.length).map y ↔ ∀ k (hk : k < l.length), l[k] = y (s + k) := by
  constructor
  · intro h k hk
    have e : l[k]? = some (y (s + k)) := by rw [h]; simp [hk]
    rw [List.getElem?_eq_getElem hk] at e
    exact Option.some.inj e
  · intro h
    apply List.ext_getElem (by simp)
    intro k h1 h2
    simp [h k h1]

theorem flat_succ' (w : ℕ → List α) : ∀ m i, flat w i (m + 1) = flat w i m ++ w (i + m) := by
  intro m
  induction m with
  | zero => intro i; simp [flat]
  | succ m ih =>
    intro i
    rw [flat, ih (i + 1), flat, List.append_assoc, show i + 1 + m = i + (m + 1) by ring]

theorem flat_add (w : ℕ → List α) : ∀ a i b, flat w i (a + b) = flat w i a ++ flat w (i + a) b := by
  intro a
  induction a with
  | zero => intro i b; simp [flat]
  | succ a ih =>
    intro i b
    rw [show a + 1 + b = (a + b) + 1 by ring, flat, ih (i + 1), flat, List.append_assoc,
      show i + 1 + a = i + (a + 1) by ring]

theorem flat_shift {w w' : ℕ → List α} (h : ∀ j, w' (j + 1) = w j) :
    ∀ m i, flat w' (i + 1) m = flat w i m := by
  intro m
  induction m with
  | zero => intro i; simp [flat]
  | succ m ih => intro i; rw [flat, flat, h, ih]

theorem getElem?_flat (w : ℕ → List α) {m j : ℕ} (hj : j < m) (k : ℕ) (hk : k < (w j).length) :
    (flat w 0 m)[(flat w 0 j).length + k]? = (w j)[k]? := by
  obtain ⟨r, rfl⟩ : ∃ r, m = (j + 1) + r := ⟨m - (j + 1), by omega⟩
  rw [flat_add, flat_succ', zero_add, List.getElem?_append_left (by simp; omega),
    List.getElem?_append_right (by omega)]
  simp

/-- Two commuting words: `uv = vu`, `v ≠ []` ⇒ `u[j] = v[j mod |v|]`. -/
theorem getElem?_of_comm {u v : List α} (h : u ++ v = v ++ u) (hv : 0 < v.length) :
    ∀ j, j < u.length → u[j]? = v[j % v.length]? := by
  have key : ∀ j, j < u.length + v.length → (u ++ v)[j]? = v[j % v.length]? := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      by_cases hjv : j < v.length
      · rw [h, List.getElem?_append_left hjv, Nat.mod_eq_of_lt hjv]
      · have e1 : (u ++ v)[j]? = (u ++ v)[j - v.length]? := by
          conv_lhs => rw [h]
          rw [List.getElem?_append_right (by omega), List.getElem?_append_left (by omega)]
        rw [e1, ih (j - v.length) (by omega) (by omega)]
        congr 1
        conv_rhs => rw [show j = (j - v.length) + v.length by omega]
        rw [Nat.add_mod_right]
  intro j hj
  rw [← key j (by omega), List.getElem?_append_left hj]

/-- `W^n`. -/
def rep (W : List α) (n : ℕ) : List α := (List.replicate n W).flatten

theorem rep_comm (W : List α) (n : ℕ) : rep W n ++ W = W ++ rep W n := by
  calc rep W n ++ W = (List.replicate n W ++ [W]).flatten := by simp [rep]
    _ = (List.replicate (n + 1) W).flatten := by rw [List.replicate_succ']
    _ = W ++ rep W n := by simp [rep, List.replicate_succ]

theorem length_rep (W : List α) (n : ℕ) : (rep W n).length = n * W.length := by
  simp [rep]

/-- A sequence that is not eventually periodic: the indicator of the squares. -/
theorem not_eventuallyPeriodic_squares :
    ¬ IsEventuallyPeriodic fun k : ℕ => decide (Nat.sqrt k * Nat.sqrt k = k) := by
  rintro ⟨N, P, hP, hper⟩
  set s := N + P
  have h1 := hper (s * s) (le_trans (by omega : N ≤ s) (Nat.le_mul_self s))
  simp only at h1
  rw [Nat.sqrt_add_eq s (by omega), Nat.sqrt_eq] at h1
  simp at h1
  omega

/-! ## Gluing finite paths -/

/-- **Gluing.**  Infinitely many finite paths (`m k ≥ 1` edges each, consecutive ones linked) whose
outputs are consecutive blocks of `y` from `T 0` on form one walk covering `y` from `T 0`. -/
theorem models_of_paths {E : Graph V α} {y : ℕ → α} (m : ℕ → ℕ) (hm : ∀ k, 0 < m k)
    (pv : ℕ → ℕ → V) (pw : ℕ → ℕ → List α) (T : ℕ → ℕ)
    (hlink : ∀ k, pv k (m k) = pv (k + 1) 0)
    (hedge : ∀ k j, j < m k → E (pv k j) (pw k j) (pv k (j + 1)))
    (hpos : ∀ k j, j < m k → 0 < (pw k j).length)
    (hT : ∀ k, T (k + 1) = T k + (flat (pw k) 0 (m k)).length)
    (hy : ∀ k, flat (pw k) 0 (m k) = (List.range' (T k) (flat (pw k) 0 (m k)).length).map y) :
    ∃ v w t, Covers E y v w t ∧ t 0 = T 0 ∧ ∀ i, ∃ k, ∃ j ≤ m k, v i = pv k j := by
  classical
  obtain ⟨I, hI0, hI⟩ : ∃ I : ℕ → ℕ, I 0 = 0 ∧ ∀ k, I (k + 1) = I k + m k :=
    ⟨fun k => ∑ l ∈ Finset.range k, m l, by simp, fun k => Finset.sum_range_succ _ _⟩
  have hImono : StrictMono I := strictMono_nat_of_lt_succ fun k => by rw [hI]; have := hm k; omega
  have hIge : ∀ k, k ≤ I k := by
    intro k
    induction k with
    | zero => rw [hI0]
    | succ k ih => rw [hI]; have := hm k; omega
  have hex : ∀ i, ∃ k, i < I (k + 1) := fun i => ⟨i, by have := hIge (i + 1); omega⟩
  obtain ⟨blk, hblk⟩ : ∃ blk : ℕ → ℕ, ∀ i, I (blk i) ≤ i ∧ i < I (blk i + 1) := by
    refine ⟨fun i => Nat.find (hex i), fun i => ⟨?_, Nat.find_spec (hex i)⟩⟩
    show I (Nat.find (hex i)) ≤ i
    rcases Nat.eq_zero_or_eq_succ_pred (Nat.find (hex i)) with h0 | h0
    · rw [h0, hI0]; omega
    · have := Nat.find_min (hex i) (show (Nat.find (hex i)).pred < Nat.find (hex i) by omega)
      rw [← Nat.succ_eq_add_one, ← h0] at this
      omega
  have hblk_eq : ∀ i k, I k ≤ i → i < I (k + 1) → blk i = k := by
    intro i k h1 h2
    rcases lt_trichotomy (blk i) k with h | h | h
    · have := hImono.monotone (show blk i + 1 ≤ k by omega)
      have := (hblk i).2; omega
    · exact h
    · have := hImono.monotone (show k + 1 ≤ blk i by omega)
      have := (hblk i).1; omega
  have hoff : ∀ i, i - I (blk i) < m (blk i) := fun i => by
    have := hblk i; rw [hI] at this; omega
  have hkey : ∀ i, (i + 1 - I (blk (i + 1)) = (i - I (blk i)) + 1 ∧ blk (i + 1) = blk i ∧
      i - I (blk i) + 1 < m (blk i)) ∨
      (i + 1 - I (blk (i + 1)) = 0 ∧ blk (i + 1) = blk i + 1 ∧ i - I (blk i) + 1 = m (blk i)) := by
    intro i
    have h1 := hblk i
    rw [hI] at h1
    by_cases hlt : i + 1 < I (blk i) + m (blk i)
    · left
      have := hblk_eq (i + 1) (blk i) (by omega) (by rw [hI]; omega)
      rw [this]; omega
    · right
      have := hblk_eq (i + 1) (blk i + 1) (by rw [hI]; omega)
        (by rw [hI, hI]; have := hm (blk i + 1); omega)
      rw [this, hI]; omega
  have hlen : ∀ k j, j < m k → (flat (pw k) 0 (j + 1)).length =
      (flat (pw k) 0 j).length + (pw k j).length := by
    intro k j _; rw [flat_succ', zero_add, List.length_append]
  refine ⟨fun i => pv (blk i) (i - I (blk i)), fun i => pw (blk i) (i - I (blk i)),
    fun i => T (blk i) + (flat (pw (blk i)) 0 (i - I (blk i))).length,
    ⟨fun i => ?_, fun i => hpos _ _ (hoff i), fun i => ?_, fun i => ?_⟩, ?_,
    fun i => ⟨blk i, i - I (blk i), (hoff i).le, rfl⟩⟩
  · rcases hkey i with ⟨e1, e2, -⟩ | ⟨e1, e2, e3⟩
    · rw [e1, e2]; exact hedge _ _ (hoff i)
    · rw [e1, e2, ← hlink, ← e3]; exact hedge _ _ (hoff i)
  · rcases hkey i with ⟨e1, e2, -⟩ | ⟨e1, e2, e3⟩
    · rw [e1, e2, hlen _ _ (hoff i), add_assoc]
    · rw [e1, e2, hT, flat, List.length_nil, add_zero, ← e3, hlen _ _ (hoff i),
        add_assoc]
  · rw [eq_map_range'_iff]
    intro k hk
    have e := (eq_map_range'_iff.1 (hy (blk i)))
    have h2 := getElem?_flat (pw (blk i)) (hoff i) k hk
    have hb : (flat (pw (blk i)) 0 (i - I (blk i))).length + k <
        (flat (pw (blk i)) 0 (m (blk i))).length := by
      have := (List.getElem?_eq_some_iff.1 (h2.trans (List.getElem?_eq_getElem hk))).1
      exact this
    have h3 := e _ hb
    rw [List.getElem?_eq_getElem hb, List.getElem?_eq_getElem hk] at h2
    rw [add_assoc, ← h3, Option.some.inj h2]
  · have : blk 0 = 0 := hblk_eq 0 0 (by rw [hI0]) (by rw [hI, hI0]; have := hm 0; omega)
    show T (blk 0) + (flat (pw (blk 0)) 0 (0 - I (blk 0))).length = T 0
    rw [this, hI0]; simp [flat]

/-! ## Proposition 16, converse -/

theorem Run.toPath {E : Graph V α} {B : V → Prop} {u : V} {W : List α} {v : V}
    (h : Run E B u W v) : ∃ (m : ℕ) (pv : ℕ → V) (pw : ℕ → List α), 0 < m ∧ pv 0 = u ∧ pv m = v ∧
      (∀ j < m, E (pv j) (pw j) (pv (j + 1))) ∧ W = flat pw 0 m := by
  induction h with
  | @last u w v he _ =>
    refine ⟨1, fun j => if j = 0 then u else v, fun _ => w, one_pos, rfl, rfl, fun j hj => ?_,
      by simp [flat]⟩
    obtain rfl : j = 0 := by omega
    simpa using he
  | @step u w x W v he _ _ ih =>
    obtain ⟨m, pv, pw, hm, h0, hmv, hE, hW⟩ := ih
    refine ⟨m + 1, fun j => Nat.casesOn j u pv, fun j => Nat.casesOn j w pw, by omega, rfl,
      hmv, fun j hj => ?_, ?_⟩
    · cases j with
      | zero => simpa [h0] using he
      | succ j => exact hE j (by omega)
    · rw [flat, hW, flat_shift (w' := fun j => Nat.casesOn j w pw) (w := pw) (fun j => rfl)]
      rfl

/-- **[Oda26] Proposition 16, converse.**  Every infinite walk of the contraction `P(G′)`, with
nonempty words in `G′`, comes from an infinite walk of `G′` with the same output. -/
@[category research solved, AMS 05 37, ref "Oda26", group "oda26_wordgraph"]
theorem models_of_contract {E : Graph V α} {B : V → Prop} (hE : ∀ u w v, E u w v → 0 < w.length)
    {y : ℕ → α} {v : ℕ → V} {W : ℕ → List α} {t : ℕ → ℕ} (hc : Covers (contract E B) y v W t) :
    Models E y (t 0) := by
  choose m pv pw hm h0 hmv hedge hW using fun k => (hc.edge k).2.toPath
  obtain ⟨v', w', t', hc', ht', -⟩ := models_of_paths (E := E) (y := y) m hm pv pw t
    (fun k => by rw [hmv, h0]) hedge (fun k j hj => hE _ _ _ (hedge k j hj))
    (fun k => by rw [← hW, hc.time]) (fun k => by rw [← hW]; exact hc.word k)
  exact ⟨v', w', t', hc', ht'⟩

/-! ## Paths inside a set -/

/-- A finite path inside `C`. -/
inductive PathIn (E : Graph V α) (C : V → Prop) : V → List α → V → Prop
  | nil {u} : C u → PathIn E C u [] u
  | cons {u w x W v} : E u w x → C u → PathIn E C x W v → PathIn E C u (w ++ W) v

namespace PathIn

variable {E : Graph V α} {C : V → Prop}

theorem append {u x v : V} {W W' : List α} (h : PathIn E C u W x) (h' : PathIn E C x W' v) :
    PathIn E C u (W ++ W') v := by
  induction h with
  | nil _ => simpa using h'
  | cons he hu _ ih => rw [List.append_assoc]; exact cons he hu (ih h')

theorem rep {ρ : V} {W : List α} (h : PathIn E C ρ W ρ) (hρ : C ρ) :
    ∀ n, PathIn E C ρ (Oda.WG.rep W n) ρ := by
  intro n
  induction n with
  | zero => simpa [Oda.WG.rep] using nil hρ
  | succ n ih =>
    simp only [Oda.WG.rep, List.replicate_succ, List.flatten_cons]
    exact h.append ih

theorem toPath {u : V} {W : List α} {v : V} (h : PathIn E C u W v) :
    ∃ (m : ℕ) (pv : ℕ → V) (pw : ℕ → List α), pv 0 = u ∧ pv m = v ∧ (∀ j < m, E (pv j) (pw j) (pv (j + 1))) ∧
      (∀ j ≤ m, C (pv j)) ∧ W = flat pw 0 m := by
  induction h with
  | @nil u hu => exact ⟨0, fun _ => u, fun _ => [], rfl, rfl, fun j hj => by omega,
      fun _ _ => hu, rfl⟩
  | @cons u w x W v he hu _ ih =>
    obtain ⟨m, pv, pw, h0, hmv, hE, hC, hW⟩ := ih
    refine ⟨m + 1, fun j => Nat.casesOn j u pv, fun j => Nat.casesOn j w pw, rfl, hmv,
      fun j hj => ?_, fun j hj => ?_, ?_⟩
    · cases j with
      | zero => simpa [h0] using he
      | succ j => exact hE j (by omega)
    · cases j with
      | zero => exact hu
      | succ j => exact hC j (by omega)
    · rw [flat, hW, flat_shift (w' := fun j => Nat.casesOn j w pw) (w := pw) (fun j => rfl)]
      rfl

/-- Telescoping along a path: if `n ∣ δ(e)` on every edge inside `C`, then
`h(v) ≡ h(u) + |W| (mod n)`. -/
theorem telescope {h : V → ℤ} {n : ℤ}
    (hδ : ∀ u w v, E u w v → C u → C v → n ∣ h u + w.length - h v)
    {u : V} {W : List α} {v : V} (hp : PathIn E C u W v) : n ∣ h u + W.length - h v := by
  induction hp with
  | nil _ => simp
  | @cons u w x W v he hu hx ih =>
    have hxC : C x := by cases hx <;> assumption
    have := dvd_add (hδ _ _ _ he hu hxC) ih
    rw [List.length_append, Nat.cast_add]
    have e : h u + ((w.length : ℤ) + (W.length : ℤ)) - h v =
        (h u + w.length - h x) + (h x + W.length - h v) := by ring
    rw [e]; exact this

theorem start_mem {u : V} {W : List α} {v : V} (h : PathIn E C u W v) : C u := by
  cases h <;> assumption

end PathIn

/-! ## Theorem 21 -/

section Thm21

variable {E : Graph V α} {C : V → Prop} {ρ : V}

/-- (a) ⇒ (b): **Lemma 12(b)**. -/
theorem periodic_of_certified' (hcert : Certified E C) {y : ℕ → α} {v : ℕ → V}
    {w : ℕ → List α} {t : ℕ → ℕ} (hc : Covers E y v w t) (hC : ∀ i, C (v i)) :
    IsEventuallyPeriodic y :=
  hc.periodic_of_certified hcert hC

/-- (b) ⇒ (c): two non-commuting closed words at `ρ` code a non-eventually-periodic sequence into
the output of an internal infinite walk. -/
theorem comm_of_periodic (hEpos : ∀ u w v, E u w v → 0 < w.length)
    (hb : ∀ (y : ℕ → α) (v : ℕ → V) (w : ℕ → List α) (t : ℕ → ℕ), Covers E y v w t →
      (∀ i, C (v i)) → IsEventuallyPeriodic y)
    {W W' : List α} (hW : PathIn E C ρ W ρ) (hW' : PathIn E C ρ W' ρ) : W ++ W' = W' ++ W := by
  classical
  by_contra hne
  have hUU : (W ++ W').length = (W' ++ W).length := by simp [add_comm]
  have hL : 0 < (W ++ W').length := by
    rcases Nat.eq_zero_or_pos (W ++ W').length with h | h
    · rw [List.length_append] at h
      have h1 : W = [] := List.eq_nil_of_length_eq_zero (by omega)
      have h2 : W' = [] := List.eq_nil_of_length_eq_zero (by omega)
      exact absurd (by simp [h1, h2]) hne
    · exact h
  obtain ⟨L, hLdef⟩ : ∃ L, L = (W ++ W').length := ⟨_, rfl⟩
  obtain ⟨m0, pv0, pw0, h00, hm0, hE0, hC0, hW0⟩ := (hW.append hW').toPath
  obtain ⟨m1, pv1, pw1, h01, hm1, hE1, hC1, hW1⟩ := (hW'.append hW).toPath
  have hm0p : 0 < m0 := by
    rcases Nat.eq_zero_or_pos m0 with h | h
    · exfalso; rw [h] at hW0; rw [hW0] at hL; simp [flat] at hL
    · exact h
  have hm1p : 0 < m1 := by
    rcases Nat.eq_zero_or_pos m1 with h | h
    · exfalso; rw [h] at hW1; rw [hUU, hW1] at hL; simp [flat] at hL
    · exact h
  let ε : ℕ → Bool := fun k => decide (Nat.sqrt k * Nat.sqrt k = k)
  let word : ℕ → List α := fun k => if ε k then W' ++ W else W ++ W'
  have hεw : ∀ k, word k = if ε k then W' ++ W else W ++ W' := fun k => rfl
  have hwl : ∀ k, (word k).length = L := fun k => by
    rw [hεw]; split_ifs
    · rw [hLdef, hUU]
    · rw [hLdef]
  have hL' : 0 < L := hLdef ▸ hL
  let d₀ : α := (W ++ W')[0]'hL
  let z : ℕ → α := fun s => (word (s / L)).getD (s % L) d₀
  have hzw : ∀ k j (hj : j < L), z (k * L + j) = (word k)[j]'(by rw [hwl]; exact hj) := by
    intro k j hj
    have h1 : (k * L + j) / L = k := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hL', Nat.div_eq_of_lt hj, zero_add]
    have h2 : (k * L + j) % L = j := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    show (word ((k * L + j) / L)).getD ((k * L + j) % L) d₀ = _
    rw [h1, h2, List.getD_eq_getElem]
  have hflat : ∀ k, flat (if ε k then pw1 else pw0) 0 (if ε k then m1 else m0) = word k := by
    intro k; rw [hεw]; split_ifs
    · exact hW1.symm
    · exact hW0.symm
  have hend : ∀ k, (if ε k then pv1 else pv0) (if ε k then m1 else m0) = ρ := by
    intro k; split_ifs
    · exact hm1
    · exact hm0
  have hstart : ∀ k, (if ε k then pv1 else pv0) 0 = ρ := by
    intro k; split_ifs
    · exact h01
    · exact h00
  obtain ⟨v, w, t, hc, -, hvC⟩ := models_of_paths (E := E) (y := z)
    (fun k => if ε k then m1 else m0) (fun k => by split_ifs <;> assumption)
    (fun k => if ε k then pv1 else pv0) (fun k => if ε k then pw1 else pw0) (fun k => k * L)
    (fun k => (hend k).trans (hstart (k + 1)).symm)
    (fun k j hj => by
      split_ifs at hj ⊢
      · exact hE1 j hj
      · exact hE0 j hj)
    (fun k j hj => by
      split_ifs at hj ⊢
      · exact hEpos _ _ _ (hE1 j hj)
      · exact hEpos _ _ _ (hE0 j hj))
    (fun k => by rw [hflat, hwl]; ring)
    (fun k => by
      rw [hflat k, eq_map_range'_iff]
      intro j hj
      rw [hwl] at hj
      exact (hzw k j hj).symm)
  have hper := hb z v w t hc fun i => by
    obtain ⟨k, j, hj, hv⟩ := hvC i
    rw [hv]
    split_ifs at hj ⊢
    · exact hC1 j hj
    · exact hC0 j hj
  obtain ⟨N, P, hP, hz⟩ := hper
  have hzL : ∀ n s, N ≤ s → z (s + n * P) = z s := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro s hs
      rw [show s + (n + 1) * P = (s + n * P) + P by ring, hz _ (by nlinarith), ih s hs]
  apply not_eventuallyPeriodic_squares
  refine ⟨N, P, hP, fun k hk => ?_⟩
  have hword : word (k + P) = word k := by
    apply List.ext_getElem (by rw [hwl, hwl])
    intro j h1 h2
    have h1' : j < L := by rwa [hwl] at h1
    have e := hzL L (k * L + j) (le_trans hk (by nlinarith))
    rw [show k * L + j + L * P = (k + P) * L + j by ring, hzw _ _ h1', hzw _ _ h1'] at e
    exact e
  show ε (k + P) = ε k
  rw [hεw, hεw] at hword
  cases h1 : ε (k + P) <;> cases h2 : ε k
  · rfl
  · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte] at hword
    exact absurd hword hne
  · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte] at hword
    exact absurd hword.symm hne
  · rfl


/-- The phase test (19) with the phase `h(v) = |P v|` (root path lengths when `P v` is the output
of a path `ρ → v` inside `C`). -/
def RootCert (E : Graph V α) (C : V → Prop) (P : V → List α) : Prop :=
  ∃ (d : ℕ) (lam : ℤ → α), 0 < d ∧ ∀ u w v, E u w v → C u → C v →
    ((P v).length : ℤ) ≡ (P u).length + w.length [ZMOD d] ∧
    ∀ i (hi : i < w.length), w[i] = lam (((P u).length + i) % d)

theorem RootCert.certified {P : V → List α} (h : RootCert E C P) : Certified E C := by
  obtain ⟨d, lam, hd, h⟩ := h
  exact ⟨fun v => ((P v).length : ℤ), d, lam, hd, h⟩

/-- (c) ⇒ (a), **with root path lengths**: if closed words at `ρ` commute, the phase test holds for
`h(v) = |out(π_v)|`, for any choice of paths `π_v : ρ → v` inside `C`. -/
@[category research solved, AMS 05 68, ref "Oda26", group "oda26_wordgraph"]
theorem certified_rootPath [Nonempty α] (hEpos : ∀ u w v, E u w v → 0 < w.length)
    (hscc : ∀ u v, C u → C v → ∃ W, PathIn E C u W v) (hρ : C ρ)
    (hc : ∀ W W', PathIn E C ρ W ρ → PathIn E C ρ W' ρ → W ++ W' = W' ++ W)
    (P : V → List α) (hP : ∀ v, C v → PathIn E C ρ (P v) v) : RootCert E C P := by
  classical
  by_cases hint : ∃ u w v, E u w v ∧ C u ∧ C v
  swap
  · push Not at hint
    exact ⟨1, fun _ => Classical.arbitrary α, one_pos,
      fun u w v he hu hv => absurd hv (hint u w v he hu)⟩
  obtain ⟨u₀, w₀, v₀, he₀, hu₀, hv₀⟩ := hint
  obtain ⟨σ₀, hσ₀⟩ := hscc v₀ ρ hv₀ hρ
  have hz₀ : PathIn E C ρ (P u₀ ++ (w₀ ++ σ₀)) ρ := (hP u₀ hu₀).append (PathIn.cons he₀ hu₀ hσ₀)
  obtain ⟨z₀, hz₀def⟩ : ∃ z₀, z₀ = P u₀ ++ (w₀ ++ σ₀) := ⟨_, rfl⟩
  rw [← hz₀def] at hz₀
  have hz₀pos : 0 < z₀.length := by
    have := hEpos _ _ _ he₀; rw [hz₀def]; simp only [List.length_append]; omega
  let Z : ℕ → α := fun t => z₀.getD (t % z₀.length) (Classical.arbitrary α)
  -- every closed word at `ρ` reads `Z`
  have hZW : ∀ W, PathIn E C ρ W ρ → ∀ j, j < W.length → W[j]? = some (Z j) := by
    intro W hW j hj
    rw [getElem?_of_comm (hc W z₀ hW hz₀) hz₀pos j hj]
    show _ = some (z₀.getD (j % z₀.length) (Classical.arbitrary α))
    rw [List.getD_eq_getElem _ _ (Nat.mod_lt _ hz₀pos),
      List.getElem?_eq_getElem (Nat.mod_lt _ hz₀pos)]
  -- `Z` has every closed length as a period
  have hZper : ∀ W, PathIn E C ρ W ρ → Function.Periodic Z W.length := by
    intro W hW t
    rcases Nat.eq_zero_or_pos W.length with h0 | hpos
    · rw [h0, add_zero]
    have hR := hW.rep hρ (t + 2)
    have hlen : t + W.length < (rep W (t + 2)).length := by rw [length_rep]; nlinarith
    have e1 := hZW _ hR (t + W.length) hlen
    have e2 := hZW _ hR t (by omega)
    rw [getElem?_of_comm (rep_comm W (t + 2)) hpos _ hlen] at e1
    rw [getElem?_of_comm (rep_comm W (t + 2)) hpos _ (by omega)] at e2
    rw [Nat.add_mod_right] at e1
    exact Option.some.inj (e1.symm.trans e2)
  -- the least positive period `d` divides every closed length
  have hex : ∃ n, 0 < n ∧ Function.Periodic Z n := ⟨z₀.length, hz₀pos, hZper _ hz₀⟩
  have hd := Nat.find_spec hex
  have hdvd : ∀ W, PathIn E C ρ W ρ → Nat.find hex ∣ W.length := by
    intro W hW
    rcases Nat.eq_zero_or_pos W.length with h0 | hpos
    · rw [h0]; exact dvd_zero _
    have hg := periodic_gcd hd.2 (hZper W hW)
    have hgpos : 0 < Nat.gcd (Nat.find hex) W.length := Nat.gcd_pos_of_pos_left _ hd.1
    have hle : Nat.find hex ≤ Nat.gcd (Nat.find hex) W.length := Nat.find_min' hex ⟨hgpos, hg⟩
    have hge : Nat.gcd (Nat.find hex) W.length ≤ Nat.find hex :=
      Nat.le_of_dvd hd.1 (Nat.gcd_dvd_left _ _)
    have : Nat.gcd (Nat.find hex) W.length = Nat.find hex := le_antisymm hge hle
    rw [← this]; exact Nat.gcd_dvd_right _ _
  refine ⟨Nat.find hex, fun s => Z s.toNat, hd.1, fun u w v he hu hv => ?_⟩
  obtain ⟨σ, hσ⟩ := hscc v ρ hv hρ
  have hω1 : PathIn E C ρ (P u ++ (w ++ σ)) ρ := (hP u hu).append (PathIn.cons he hu hσ)
  have hω2 : PathIn E C ρ (P v ++ σ) ρ := (hP v hv).append hσ
  refine ⟨?_, fun i hi => ?_⟩
  · rw [Int.modEq_iff_dvd]
    have h1 := Int.natCast_dvd_natCast.2 (hdvd _ hω1)
    have h2 := Int.natCast_dvd_natCast.2 (hdvd _ hω2)
    have e : (((P u ++ (w ++ σ)).length : ℕ) : ℤ) - ((P v ++ σ).length : ℕ) =
        (P u).length + w.length - (P v).length := by
      simp only [List.length_append]; push_cast; ring
    rw [← e]
    exact dvd_sub h1 h2
  · have hj : (P u).length + i < (P u ++ (w ++ σ)).length := by
      simp only [List.length_append]; omega
    have e := hZW _ hω1 _ hj
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left hi, List.getElem?_eq_getElem hi] at e
    show w[i] = Z ((((P u).length : ℤ) + i) % (Nat.find hex : ℤ)).toNat
    rw [show ((P u).length : ℤ) + i = (((P u).length + i : ℕ) : ℤ) by push_cast; ring,
      ← Int.natCast_mod, Int.toNat_natCast, hd.2.map_mod_nat]
    exact Option.some.inj e

/-- **[Oda26] Theorem 21 (the all-edge test and commuting closed words).**  For a strongly
connected set `C` with root `ρ` (words nonempty), TFAE: (a) `C` passes the phase test (19);
(b) every infinite walk inside `C` has eventually periodic output; (c) closed words at `ρ`
commute.  (By `certified_rootPath`, (a) then holds for root path lengths.) -/
@[category research solved, AMS 05 68, ref "Oda26", group "oda26_wordgraph"]
theorem all_edge_test [Nonempty α] (hEpos : ∀ u w v, E u w v → 0 < w.length)
    (hscc : ∀ u v, C u → C v → ∃ W, PathIn E C u W v) (hρ : C ρ) :
    List.TFAE [Certified E C,
      ∀ (y : ℕ → α) (v : ℕ → V) (w : ℕ → List α) (t : ℕ → ℕ), Covers E y v w t →
        (∀ i, C (v i)) → IsEventuallyPeriodic y,
      ∀ W W', PathIn E C ρ W ρ → PathIn E C ρ W' ρ → W ++ W' = W' ++ W] := by
  classical
  tfae_have 1 → 2 := fun h y v w t hc hC => hc.periodic_of_certified h hC
  tfae_have 2 → 3 := fun h W W' hW hW' => comm_of_periodic hEpos h hW hW'
  tfae_have 3 → 1 := fun h => by
    let P : V → List α := fun v => if hv : C v then Classical.choose (hscc ρ v hρ hv) else []
    have hP : ∀ v, C v → PathIn E C ρ (P v) v := fun v hv => by
      simp only [P, hv, ↓reduceDIte]; exact Classical.choose_spec (hscc ρ v hρ hv)
    exact (certified_rootPath hEpos hscc hρ h P hP).certified
  tfae_finish

/-- **[Oda26] Corollary 22, independence.**  The root-path test does not depend on the root or on
the chosen paths. -/
@[category research solved, AMS 05 68, ref "Oda26", group "oda26_wordgraph"]
theorem rootCert_iff [Nonempty α] (hEpos : ∀ u w v, E u w v → 0 < w.length)
    (hscc : ∀ u v, C u → C v → ∃ W, PathIn E C u W v) {ρ ρ' : V} (hρ : C ρ) (hρ' : C ρ')
    {P P' : V → List α} (hP : ∀ v, C v → PathIn E C ρ (P v) v)
    (hP' : ∀ v, C v → PathIn E C ρ' (P' v) v) : RootCert E C P ↔ RootCert E C P' := by
  have t := all_edge_test hEpos hscc hρ
  have t' := all_edge_test hEpos hscc hρ'
  constructor
  · intro h
    exact certified_rootPath hEpos hscc hρ' ((t'.out 1 3).1 h.certified) P' hP'
  · intro h
    exact certified_rootPath hEpos hscc hρ ((t.out 1 3).1 h.certified) P hP

/-- **[Oda26] Corollary 22, `d = g_C`.**  For root path lengths, `n` divides every
`δ(e) = h(u) + |w| − h(v)` iff `n` divides the length of every closed walk in `C`. -/
@[category research solved, AMS 05 68, ref "Oda26", group "oda26_wordgraph"]
theorem dvd_delta_iff (hscc : ∀ u v, C u → C v → ∃ W, PathIn E C u W v) (hρ : C ρ)
    {P : V → List α} (hP : ∀ v, C v → PathIn E C ρ (P v) v) (n : ℕ) :
    (∀ u w v, E u w v → C u → C v → (n : ℤ) ∣ (P u).length + w.length - (P v).length) ↔
      ∀ x W, PathIn E C x W x → n ∣ W.length := by
  constructor
  · intro h x W hW
    have := hW.telescope (h := fun v => ((P v).length : ℤ)) h
    simp only [add_sub_cancel_left] at this
    exact Int.natCast_dvd_natCast.1 this
  · intro h u w v he hu hv
    obtain ⟨σ, hσ⟩ := hscc v ρ hv hρ
    have h1 := Int.natCast_dvd_natCast.2 (h ρ _ ((hP u hu).append (PathIn.cons he hu hσ)))
    have h2 := Int.natCast_dvd_natCast.2 (h ρ _ ((hP v hv).append hσ))
    have e : (((P u ++ (w ++ σ)).length : ℕ) : ℤ) - ((P v ++ σ).length : ℕ) =
        (P u).length + w.length - (P v).length := by
      simp only [List.length_append]; push_cast; ring
    rw [← e]
    exact dvd_sub h1 h2

/-! ## Lemma 14(b): deterministic components are certified -/

/-- Under determinism, of two paths from the same vertex one extends the other. -/
theorem PathIn.prefix {u x y : V} {W₁ W₂ : List α} (hdet : ∀ z, C z → Det E z)
    (h₁ : PathIn E C u W₁ x) (h₂ : PathIn E C u W₂ y) :
    (∃ R, W₂ = W₁ ++ R ∧ PathIn E C x R y) ∨ (∃ R, W₁ = W₂ ++ R ∧ PathIn E C y R x) := by
  induction h₁ generalizing W₂ with
  | nil _ => exact Or.inl ⟨W₂, rfl, h₂⟩
  | @cons u w x' W v he hu _ ih =>
    cases h₂ with
    | nil _ => exact Or.inr ⟨w ++ W, rfl, PathIn.cons he hu (by assumption)⟩
    | cons he' _ h₂' =>
      obtain ⟨rfl, rfl⟩ := hdet u hu _ _ _ _ he he'
      rcases ih h₂' with ⟨R, hR, hp⟩ | ⟨R, hR, hp⟩
      · exact Or.inl ⟨R, by rw [hR, List.append_assoc], hp⟩
      · exact Or.inr ⟨R, by rw [hR, List.append_assoc], hp⟩

theorem comm_of_det (hdet : ∀ z, C z → Det E z) :
    ∀ n (W₁ W₂ : List α), W₁.length + W₂.length ≤ n → PathIn E C ρ W₁ ρ → PathIn E C ρ W₂ ρ →
      W₁ ++ W₂ = W₂ ++ W₁ := by
  intro n
  induction n with
  | zero =>
    intro W₁ W₂ hn _ _
    rw [List.eq_nil_of_length_eq_zero (by omega : W₁.length = 0),
      List.eq_nil_of_length_eq_zero (by omega : W₂.length = 0)]
  | succ n ih =>
    intro W₁ W₂ hn h₁ h₂
    rcases Nat.eq_zero_or_pos W₁.length with h0 | h0
    · rw [List.eq_nil_of_length_eq_zero h0]; simp
    rcases Nat.eq_zero_or_pos W₂.length with h0' | h0'
    · rw [List.eq_nil_of_length_eq_zero h0']; simp
    rcases PathIn.prefix hdet h₁ h₂ with ⟨R, rfl, hR⟩ | ⟨R, rfl, hR⟩
    · have := ih W₁ R (by simp at hn; omega) h₁ hR
      calc W₁ ++ (W₁ ++ R) = W₁ ++ (R ++ W₁) := by rw [this]
        _ = W₁ ++ R ++ W₁ := by rw [List.append_assoc]
    · have := ih W₂ R (by simp at hn; omega) h₂ hR
      rw [List.append_assoc, ← this]

/-- **[Oda26] Lemma 14(b).**  A strongly connected set all of whose vertices have at most one
out-edge passes the phase test. -/
@[category research solved, AMS 05 68, ref "Oda26", group "oda26_wordgraph"]
theorem certified_of_det [Nonempty α] (hEpos : ∀ u w v, E u w v → 0 < w.length)
    (hscc : ∀ u v, C u → C v → ∃ W, PathIn E C u W v) (hdet : ∀ z, C z → Det E z) :
    Certified E C := by
  by_cases hne : ∃ ρ, C ρ
  · obtain ⟨ρ, hρ⟩ := hne
    exact ((all_edge_test hEpos hscc hρ).out 3 1).1 fun W₁ W₂ h₁ h₂ =>
      comm_of_det hdet _ W₁ W₂ le_rfl h₁ h₂
  · push Not at hne
    exact ⟨fun _ => 0, 1, fun _ => Classical.arbitrary α, one_pos,
      fun u _ _ _ hu _ => absurd hu (hne u)⟩

end Thm21

end Oda.WG
