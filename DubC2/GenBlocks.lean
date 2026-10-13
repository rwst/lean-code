/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.GenSound

/-!
# The surviving words of a checked certificate

Experiment X‑C of `plans/plan-dubC2-transform.html` (claims C‑3/C‑8, note §6) found that the det
cycles of every atlas certificate are exactly the periodic avoiding pseudo-orbits, up to grid
artefacts.  This file turns the half of that statement that matters into a theorem: **every
avoiding pseudo-orbit of a checked certificate eventually reads one of a listed set of words**.

* An avoiding **pseudo-orbit** (`Gen.Pseudo`) is what a real orbit looks like to the certificate:
  integers `xₙ`, residuals `yₙ ∈ [0,1)` and letters `sₙ` with `q x_{n+1} = p xₙ + sₙ`,
  `q y_{n+1} = p yₙ − sₙ − (p−q)a/b`, and every `xₙ` prime to `PM ++ Pq`.  No `ξ` — so, unlike a
  real orbit, a pseudo-orbit can exist at a certified cell (the census lists them).
* `Gen.pseudo_isPath`: its (residue, cell) sequence is a path of the certificate's graph — the
  soundness lemma `Gen.sound`, re-proved for abstract data.
* `Gen.eventually_word_of_path`: along any path, once the det rank stops dropping the det state
  follows the rank-keeping successor `fstep`.  A **cycle certificate** lists the `fstep` cycles
  with their words and a potential that strictly drops along `fstep` off the listed cycles; both
  are Boolean checks (`cycOK`, `potOK`).  Then the letter word is eventually a rotation of a
  listed word, read forever.

The per-cell instances, with the grid artefacts removed, are in `DubC2/Blocks.lean`.
-/

namespace DubC2.Gen

open Filter ForMathlib.SubwordComplexity

/-! ## Pseudo-orbits are paths -/

/-- An **avoiding pseudo-orbit** of the cell `P`. -/
structure Pseudo (P : Params) (x : ℕ → ℤ) (y : ℕ → ℝ) (s : ℕ → ℤ) : Prop where
  y0 : ∀ n, 0 ≤ y n
  y1 : ∀ n, y n < 1
  recx : ∀ n, (P.q : ℤ) * x (n + 1) = P.p * x n + s n
  recy : ∀ n, (P.q : ℝ) * y (n + 1) = P.p * y n - s n - ((P.p : ℝ) - P.q) * (P.a / P.b)
  avoid : ∀ n, ∀ ℓ ∈ P.PM ++ P.Pq, ¬ (ℓ : ℤ) ∣ x n

section PseudoPath

variable {P : Params} {x : ℕ → ℤ} {y : ℕ → ℝ} {s : ℕ → ℤ}

/-- The cell of `yₙ`. -/
noncomputable def pcell (P : Params) (y : ℕ → ℝ) (n : ℕ) : ℕ := (⌊(P.D : ℝ) * y n⌋).toNat

/-- The residue of `xₙ` mod `M`. -/
def pres (P : Params) (x : ℕ → ℤ) (n : ℕ) : ℕ := (x n % P.M).toNat

/-- The vertex of time `n`. -/
noncomputable def pvtx (P : Params) (x : ℕ → ℤ) (y : ℕ → ℝ) (n : ℕ) : ℕ :=
  pres P x n * P.D + pcell P y n

/-- The letter index of time `n`. -/
def ptix (P : Params) (s : ℕ → ℤ) (n : ℕ) : ℕ := (s n - P.sLo).toNat

variable (hF : ParamFacts P) (h : Pseudo P x y s)
include hF h

theorem Pseudo.scaled_b (n : ℕ) :
    (s n : ℝ) * P.b = P.p * P.b * y n - P.q * P.b * y (n + 1) - ((P.p : ℝ) - P.q) * P.a := by
  have hb : (P.b : ℝ) ≠ 0 := by have := hF.b0; positivity
  have e := h.recy n
  field_simp at e
  linear_combination e

theorem Pseudo.scaled (n : ℕ) :
    (P.q : ℝ) * P.b * (P.D * y (n + 1)) =
      P.p * P.b * (P.D * y n) - (((P.p : ℝ) - P.q) * P.a * P.D + s n * P.b * P.D) := by
  have e := h.scaled_b hF n
  linear_combination (P.D : ℝ) * e

omit h in
theorem pcell_spec (h0 : ∀ n, 0 ≤ y n) (h1 : ∀ n, y n < 1) (n : ℕ) :
    ((pcell P y n : ℕ) : ℝ) ≤ P.D * y n ∧ P.D * y n < (pcell P y n : ℕ) + 1 ∧
      pcell P y n < P.D := by
  have hy0 := h0 n
  have hy1 := h1 n
  have hD : (0 : ℝ) < P.D := by exact_mod_cast hF.D0
  have hfl : 0 ≤ ⌊(P.D : ℝ) * y n⌋ := Int.floor_nonneg.2 (by positivity)
  have hc : ((pcell P y n : ℕ) : ℤ) = ⌊(P.D : ℝ) * y n⌋ := Int.toNat_of_nonneg hfl
  have hcR : ((pcell P y n : ℕ) : ℝ) = (⌊(P.D : ℝ) * y n⌋ : ℝ) := by exact_mod_cast hc
  refine ⟨?_, ?_, ?_⟩
  · rw [hcR]; exact Int.floor_le _
  · rw [hcR]; exact Int.lt_floor_add_one _
  · have : ⌊(P.D : ℝ) * y n⌋ < P.D := by
      rw [Int.floor_lt]; push_cast; nlinarith
    omega

omit h in
theorem pres_cast (n : ℕ) : ((pres P x n : ℕ) : ℤ) = x n % P.M :=
  Int.toNat_of_nonneg (Int.emod_nonneg _ (by have := hF.M0; omega))

omit h in
theorem pres_lt (n : ℕ) : pres P x n < P.M := by
  have h1 := pres_cast hF (x := x) n
  have h2 := Int.emod_lt_of_pos (x n) (by have := hF.M0; omega : (0 : ℤ) < P.M)
  omega

omit h in
theorem pres_mod_ne {l : ℕ} (hl : l ∈ P.PM) {n : ℕ} (hn : ¬ (l : ℤ) ∣ x n) :
    pres P x n % l ≠ 0 := by
  intro h0
  apply hn
  have hlM : (l : ℤ) ∣ P.M := by
    exact_mod_cast Nat.dvd_of_mod_eq_zero (hF.PM l hl)
  have h1 : ((pres P x n % l : ℕ) : ℤ) = x n % l := by
    push_cast
    rw [pres_cast hF (x := x), Int.emod_emod_of_dvd _ hlM]
  rw [h0, Nat.cast_zero] at h1
  exact Int.dvd_of_emod_eq_zero h1.symm

theorem Pseudo.rnext_eq (n : ℕ) : P.rnext (pres P x n) (s n) = pres P x (n + 1) := by
  simp only [Params.rnext, pres]
  congr 1
  have hq : ((P.q : ℤ) * P.qinv) ≡ 1 [ZMOD P.M] := by
    have := congrArg (Nat.cast : ℕ → ℤ) hF.inv
    push_cast at this
    exact this
  have hr : ((pres P x n : ℕ) : ℤ) ≡ x n [ZMOD P.M] := by
    rw [pres_cast hF (x := x)]; exact Int.mod_modEq _ _
  calc ((P.p : ℤ) * ((x n % P.M).toNat : ℕ) + s n) * P.qinv
      ≡ ((P.p : ℤ) * x n + s n) * P.qinv [ZMOD P.M] :=
        ((hr.mul_left _).add_right _).mul_right _
    _ = x (n + 1) * ((P.q : ℤ) * P.qinv) := by rw [← h.recx]; ring
    _ ≡ x (n + 1) * 1 [ZMOD P.M] := hq.mul_left _
    _ = x (n + 1) := mul_one _

theorem Pseudo.s_mod_ne {l : ℕ} (hl : l ∈ P.Pq) {n : ℕ} (hn : ¬ (l : ℤ) ∣ x n) :
    s n % (l : ℤ) ≠ 0 := by
  intro h0
  apply hn
  obtain ⟨hlq, hlp⟩ := hF.Pq l hl
  have hdc : (l : ℤ) ∣ s n := Int.dvd_of_emod_eq_zero h0
  have hdq : (l : ℤ) ∣ P.q := by exact_mod_cast Nat.dvd_of_mod_eq_zero hlq
  have hdp : (l : ℤ) ∣ x n * P.p := by
    have : x n * P.p = P.q * x (n + 1) - s n := by rw [h.recx]; ring
    rw [this]
    exact dvd_sub (dvd_mul_of_dvd_left hdq _) hdc
  have hcop : IsCoprime (l : ℤ) (P.p : ℤ) := Nat.isCoprime_iff_coprime.2 hlp
  exact hcop.dvd_of_dvd_mul_right hdp

/-- **Soundness for pseudo-orbits** (`Gen.sound` without `ξ`). -/
theorem Pseudo.sound (n : ℕ) :
    pvtx P x y n < P.nV ∧ ptix P s n < P.nA ∧ P.letter (ptix P s n) = s n ∧
      pvtx P x y (n + 1) ∈ P.succList (pvtx P x y n) (P.letter (ptix P s n)) := by
  have hD := hF.D0
  obtain ⟨hc0, hc1, hcD⟩ := pcell_spec hF h.y0 h.y1 n
  obtain ⟨hd0, hd1, hdD⟩ := pcell_spec hF h.y0 h.y1 (n + 1)
  have hrM := pres_lt hF (x := x) n
  have hy0 := h.y0 n
  have hy1 := h.y1 n
  have hz0 := h.y0 (n + 1)
  have hz1 := h.y1 (n + 1)
  have hsb := h.scaled_b hF n
  have hpb : (0 : ℝ) ≤ P.p * P.b := by positivity
  have hqb : (0 : ℝ) < P.q * P.b := by
    have := hF.q1; have := hF.b0
    have : (0 : ℝ) < P.q := by exact_mod_cast (by omega : 0 < P.q)
    have : (0 : ℝ) < P.b := by exact_mod_cast hF.b0
    positivity
  have hlo : -((P.q : ℤ) * P.b) - ((P.p : ℤ) - P.q) * P.a < s n * P.b := by
    have : -((P.q : ℝ) * P.b) - ((P.p : ℝ) - P.q) * P.a < (s n : ℝ) * P.b := by
      nlinarith [mul_nonneg hpb hy0, mul_lt_mul_of_pos_left hz1 hqb]
    exact_mod_cast this
  have hhi : s n * P.b < (P.p : ℤ) * P.b - ((P.p : ℤ) - P.q) * P.a := by
    have : (s n : ℝ) * P.b < (P.p : ℝ) * P.b - ((P.p : ℝ) - P.q) * P.a := by
      nlinarith [mul_lt_mul_of_pos_left hy1 (by
        have : (0 : ℝ) < P.p := by exact_mod_cast (by have := hF.pq; omega : 0 < P.p)
        have : (0 : ℝ) < P.b := by exact_mod_cast hF.b0
        positivity : (0 : ℝ) < P.p * P.b), mul_nonneg hqb.le hz0]
    exact_mod_cast this
  have hb0 : (0 : ℤ) < P.b := by exact_mod_cast hF.b0
  have hs1 : P.sLo ≤ s n := by
    have := hF.sLo
    by_contra hc
    push Not at hc
    have : (P.b : ℤ) * s n ≤ P.b * (P.sLo - 1) := mul_le_mul_of_nonneg_left (by omega) hb0.le
    linarith
  have hs2 : s n < P.sLo + P.nA := by
    have := hF.sHi
    by_contra hc
    push Not at hc
    have : (P.b : ℤ) * (P.sLo + P.nA) ≤ P.b * s n := mul_le_mul_of_nonneg_left hc hb0.le
    linarith
  have htix : P.letter (ptix P s n) = s n := by
    simp only [Params.letter, ptix]; omega
  refine ⟨?_, by simp only [ptix]; omega, htix, ?_⟩
  · simp only [pvtx, Params.nV]
    calc pres P x n * P.D + pcell P y n < pres P x n * P.D + P.D := by omega
      _ = (pres P x n + 1) * P.D := by ring
      _ ≤ P.M * P.D := Nat.mul_le_mul_right _ hrM
  rw [htix]
  have hdiv : pvtx P x y n / P.D = pres P x n := by
    simp only [pvtx]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hD, Nat.div_eq_of_lt hcD, zero_add]
  have hmod : pvtx P x y n % P.D = pcell P y n := by
    simp only [pvtx]
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hcD]
  simp only [Params.succList, hdiv, hmod, h.rnext_eq hF]
  rw [if_pos]
  swap
  · simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq]
    refine ⟨⟨fun l hl => pres_mod_ne hF hl (h.avoid n l (List.mem_append_left _ hl)),
      fun l hl => h.s_mod_ne hF hl (h.avoid n l (List.mem_append_right _ hl))⟩,
      fun l hl => pres_mod_ne hF hl (h.avoid (n + 1) l (List.mem_append_left _ hl))⟩
  rw [List.mem_map]
  have hE := h.scaled hF n
  set c := pcell P y n
  set c' := pcell P y (n + 1)
  set w : ℤ := (P.q : ℤ) * P.b
  have hw : 0 < w := by
    have := hF.q1
    have : (0 : ℤ) < P.q := by omega
    positivity
  have hA : w * (c' : ℤ) < P.hi c (s n) := by
    simp only [Params.hi, Params.shiftK, w]
    have hq' : (0 : ℝ) ≤ P.q * P.b := hqb.le
    have hp' : (0 : ℝ) < P.p * P.b := by
      have : (0 : ℝ) < P.p := by exact_mod_cast (by have := hF.pq; omega : 0 < P.p)
      have : (0 : ℝ) < P.b := by exact_mod_cast hF.b0
      positivity
    have : ((P.q : ℝ) * P.b) * (c' : ℝ) < (P.p : ℝ) * P.b * ((c : ℝ) + 1) -
        (((P.p : ℝ) - P.q) * P.a * P.D + s n * P.b * P.D) := by
      nlinarith [mul_le_mul_of_nonneg_left hd0 hq', mul_lt_mul_of_pos_left hc1 hp']
    exact_mod_cast this
  have hB : P.lo c (s n) < w * ((c' : ℤ) + 1) := by
    simp only [Params.lo, Params.shiftK, w]
    have hp' : (0 : ℝ) ≤ P.p * P.b := hpb
    have : (P.p : ℝ) * P.b * (c : ℝ) -
        (((P.p : ℝ) - P.q) * P.a * P.D + s n * P.b * P.D) < ((P.q : ℝ) * P.b) * ((c' : ℝ) + 1) := by
      nlinarith [mul_le_mul_of_nonneg_left hc0 hp', mul_lt_mul_of_pos_left hd1 hqb]
    exact_mod_cast this
  refine ⟨c', List.mem_filter.2 ⟨?_, ?_⟩, ?_⟩
  · rw [List.mem_range'_1]
    have h1 : P.cLo c (s n) ≤ c' := by
      simp only [Params.cLo]
      rw [Int.toNat_le]
      have : P.lo c (s n) / w < (c' : ℤ) + 1 := by
        rw [Int.ediv_lt_iff_lt_mul hw]; linarith
      change P.lo c (s n) / w ≤ (c' : ℤ)
      omega
    have h2 : c' < P.cHi c (s n) := by
      simp only [Params.cHi]
      refine lt_min hdD ?_
      rw [Int.lt_toNat]
      have : (c' : ℤ) ≤ (P.hi c (s n) - 1) / w := by
        rw [Int.le_ediv_iff_mul_le hw]; linarith
      change (c' : ℤ) < (P.hi c (s n) - 1) / w + 1
      omega
    omega
  · simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hA, hB⟩
  · simp only [pvtx, c']

/-- An avoiding pseudo-orbit is a path of the graph. -/
theorem Pseudo.isPath : IsPath P 0 (pvtx P x y) (ptix P s) :=
  ⟨fun n _ => (h.sound hF n).1, fun n _ => (h.sound hF n).2.1, fun n _ => (h.sound hF n).2.2.2⟩

end PseudoPath

/-! ## The rank-keeping successor and the cycle certificate -/

/-- The rank-keeping letter of det state `i` (meaningful when `keep` is non-empty). -/
def kf (C : Cert) (nA i : ℕ) : ℕ := (keep C nA i).headD 0

/-- The rank-keeping successor of det state `i`. -/
def fstep (C : Cert) (nA i : ℕ) : ℕ := next C i (kf C nA i)

/-- `i` lies on a listed cycle. -/
def listed (cyc : List (List ℕ × ℕ × ℕ)) (i : ℕ) : Bool := cyc.any fun c => c.1.contains i

/-- A listed cycle `(states, word index, rotation)`: the states follow `fstep` around, each keeps
its rank, and the letters read are the word, rotated, `|w|` dividing the cycle length. -/
def cycOK (P : Params) (C : Cert) (W : List (List ℤ)) (c : List ℕ × ℕ × ℕ) : Bool :=
  decide (0 < c.1.length) && decide (c.2.1 < W.length) && decide (0 < (W.getD c.2.1 []).length) &&
  (c.1.length % (W.getD c.2.1 []).length == 0) &&
  (List.range c.1.length).all fun j =>
    !(keep C P.nA (c.1.getD j 0)).isEmpty &&
    (fstep C P.nA (c.1.getD j 0) == c.1.getD ((j + 1) % c.1.length) 0) &&
    (P.letter (kf C P.nA (c.1.getD j 0)) ==
      (W.getD c.2.1 []).getD ((c.2.2 + j) % (W.getD c.2.1 []).length) 0)

/-- Off the listed cycles, a rank-keeping step lowers the potential. -/
def potOK (P : Params) (C : Cert) (cyc : List (List ℕ × ℕ × ℕ)) (pot : List ℕ) (i : ℕ) : Bool :=
  listed cyc i || (keep C P.nA i).isEmpty ||
    (C.rank.getD (fstep C P.nA i) 0 != C.rank.getD i 0) || listed cyc (fstep C P.nA i) ||
    decide (pot.getD (fstep C P.nA i) 0 < pot.getD i 0)

/-- **A cycle certificate** for `C`: listed cycles with words `W`, and a potential. -/
structure CycChecked (P : Params) (C : Cert) (W : List (List ℤ)) (cyc : List (List ℕ × ℕ × ℕ))
    (pot : List ℕ) : Prop where
  cycles : cyc.all (cycOK P C W) = true
  pot : (List.range C.sets.length).all (potOK P C cyc pot) = true

theorem cycOK_spec {P : Params} {C : Cert} {W : List (List ℤ)} {c : List ℕ × ℕ × ℕ}
    (h : cycOK P C W c = true) :
    0 < c.1.length ∧ W.getD c.2.1 [] ∈ W ∧ 0 < (W.getD c.2.1 []).length ∧
      (W.getD c.2.1 []).length ∣ c.1.length ∧
      ∀ j < c.1.length, fstep C P.nA (c.1.getD j 0) = c.1.getD ((j + 1) % c.1.length) 0 ∧
        P.letter (kf C P.nA (c.1.getD j 0)) =
          (W.getD c.2.1 []).getD ((c.2.2 + j) % (W.getD c.2.1 []).length) 0 := by
  simp only [cycOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, ?_, h3, Nat.dvd_of_mod_eq_zero h4, fun j hj => ⟨(h5 j hj).1.2, (h5 j hj).2⟩⟩
  have e : W.getD c.2.1 [] = W[c.2.1] := by simp [List.getD_eq_getElem?_getD, h2]
  rw [e]
  exact List.getElem_mem h2

section Word

variable {P : Params} {N : ℕ} {v t : ℕ → ℕ}

/-- **Along any path of a checked certificate the letters are eventually a listed word, read
forever** (rotated by `r`). -/
theorem eventually_word_of_path {C : Cert} (hc : Checked P C) (hp : IsPath P N v t)
    {W : List (List ℤ)} {cyc : List (List ℕ × ℕ × ℕ)} {pot : List ℕ}
    (hcc : CycChecked P C W cyc pot) :
    ∃ n₀, ∃ w ∈ W, ∃ r, 0 < w.length ∧
      ∀ m, P.letter (t (n₀ + m)) = w.getD ((r + m) % w.length) 0 := by
  classical
  obtain ⟨d, hd⟩ : ∃ d, d = detPath C t (N + C.J) := ⟨_, rfl⟩
  have hspec : ∀ i, d i < C.sets.length := fun i => hd ▸ (detPath_spec hc hp i).1
  have hrank : ∀ i, C.rank.getD (d (i + 1)) 0 ≤ C.rank.getD (d i) 0 ∧
      (C.rank.getD (d (i + 1)) 0 = C.rank.getD (d i) 0 → t (N + C.J + i) ∈ keep C P.nA (d i)) :=
    fun i => hd ▸ detPath_rank hc hp i
  have hnext : ∀ i, d (i + 1) = next C (d i) (t (N + C.J + i)) := fun i => by rw [hd]; rfl
  have hanti : Antitone fun i => C.rank.getD (d i) 0 :=
    antitone_nat_of_succ_le fun i => (hrank i).1
  have hex : ∃ k, ∃ i, C.rank.getD (d i) 0 = k := ⟨_, 0, rfl⟩
  obtain ⟨i₁, hi₁⟩ := Nat.find_spec hex
  have hconst : ∀ i, i₁ ≤ i → C.rank.getD (d i) 0 = C.rank.getD (d i₁) 0 := fun i hi =>
    le_antisymm (hanti hi) (hi₁ ▸ Nat.find_min' hex ⟨i, rfl⟩)
  have hkeep : ∀ i, i < C.sets.length → (keep C P.nA i).length ≤ 1 := by
    intro i h
    have hdet := List.all_eq_true.1 hc.det i (List.mem_range'_1.2 ⟨by omega, by omega⟩)
    simp only [detOK, Bool.and_eq_true, decide_eq_true_eq] at hdet
    exact hdet.2
  -- from `i₁` on: the letter is `kf`, the state steps by `fstep`, and the rank is kept
  have hstep : ∀ i, i₁ ≤ i → t (N + C.J + i) = kf C P.nA (d i) ∧
      d (i + 1) = fstep C P.nA (d i) ∧ (keep C P.nA (d i)).isEmpty = false ∧
      C.rank.getD (fstep C P.nA (d i)) 0 = C.rank.getD (d i) 0 := by
    intro i hi
    have hmem := (hrank i).2 (by rw [hconst (i + 1) (by omega), hconst i hi])
    have he := eq_headD_of_mem (hkeep _ (hspec i)) hmem
    have hd1 : d (i + 1) = fstep C P.nA (d i) := by rw [hnext, he]; rfl
    refine ⟨he, hd1, ?_, ?_⟩
    · cases hk : keep C P.nA (d i) with
      | nil => rw [hk] at hmem; simp at hmem
      | cons _ _ => rfl
    · rw [← hd1, hconst (i + 1) (by omega), hconst i hi]
  have hpot := List.all_eq_true.1 hcc.pot
  -- some state from `i₁` on is listed
  have hlist : ∃ k, i₁ ≤ k ∧ listed cyc (d k) = true := by
    by_contra hno
    push Not at hno
    have hdrop : ∀ k, i₁ ≤ k → pot.getD (d (k + 1)) 0 < pot.getD (d k) 0 := by
      intro k hk
      have h := hpot (d k) (List.mem_range.2 (hspec k))
      obtain ⟨-, hd1, he, hr⟩ := hstep k hk
      have hl0 : listed cyc (d k) = false := by simpa using hno k hk
      have hl1 : listed cyc (fstep C P.nA (d k)) = false := by
        rw [← hd1]; simpa using hno (k + 1) (by omega)
      simp only [potOK, hl0, he, hr, hl1, bne_self_eq_false, Bool.or_false, Bool.false_or,
        decide_eq_true_eq] at h
      rwa [hd1]
    have hbound : ∀ m, pot.getD (d (i₁ + m)) 0 + m ≤ pot.getD (d i₁) 0 := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        have := hdrop (i₁ + m) (by omega)
        rw [show i₁ + (m + 1) = i₁ + m + 1 by omega]
        omega
    have := hbound (pot.getD (d i₁) 0 + 1)
    omega
  obtain ⟨k, hk, hlk⟩ := hlist
  simp only [listed, List.any_eq_true, List.contains_iff_mem] at hlk
  obtain ⟨c, hcm, hmem⟩ := hlk
  obtain ⟨hL, hwW, hwl, hdvd, hcyc⟩ := cycOK_spec (List.all_eq_true.1 hcc.cycles c hcm)
  set L := c.1.length
  set w := W.getD c.2.1 []
  set j₀ := c.1.idxOf (d k)
  have hj₀ : j₀ < L := List.idxOf_lt_length_of_mem hmem
  -- the det path runs around the listed cycle
  have hrun : ∀ m, d (k + m) = c.1.getD ((j₀ + m) % L) 0 := by
    intro m
    induction m with
    | zero => simpa [Nat.mod_eq_of_lt hj₀] using (getD_idxOf hmem).symm
    | succ m ih =>
      rw [show k + (m + 1) = k + m + 1 by omega, (hstep _ (by omega)).2.1, ih,
        (hcyc _ (Nat.mod_lt _ hL)).1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
        Nat.add_assoc]
  refine ⟨N + C.J + k, w, hwW, c.2.2 + j₀, hwl, fun m => ?_⟩
  rw [show N + C.J + k + m = N + C.J + (k + m) by omega, (hstep _ (by omega)).1, hrun,
    (hcyc _ (Nat.mod_lt _ hL)).2]
  congr 1
  obtain ⟨e, he⟩ := hdvd
  rw [Nat.add_mod (c.2.2) ((j₀ + m) % L), he, Nat.mod_mul_right_mod, ← Nat.add_mod,
    Nat.add_assoc]

/-- **Every avoiding pseudo-orbit of a checked certificate eventually reads a listed word.** -/
@[category API, AMS 11 37 68, ref "DN05", group "dubc2_atlas"]
theorem Pseudo.eventually_word {C : Cert} (hc : Checked P C) {W : List (List ℤ)}
    {cyc : List (List ℕ × ℕ × ℕ)} {pot : List ℕ} (hcc : CycChecked P C W cyc pot)
    {x : ℕ → ℤ} {y : ℕ → ℝ} {s : ℕ → ℤ} (h : Pseudo P x y s) :
    ∃ n₀, ∃ w ∈ W, ∃ r, 0 < w.length ∧ ∀ m, s (n₀ + m) = w.getD ((r + m) % w.length) 0 := by
  have hF : ParamFacts P := by
    have hh := hc.head
    simp only [checkHead, Bool.and_eq_true] at hh
    exact paramFacts hh.1.1.1.1.1
  obtain ⟨n₀, w, hw, r, hl, hm⟩ := eventually_word_of_path hc (h.isPath hF) hcc
  exact ⟨n₀, w, hw, r, hl, fun m => by rw [← hm, (h.sound hF _).2.2.1]⟩

/-- The exact orbit `Z` of a word `w` (`Z_{j+1} = (p Z_j − w_j − (p−q)a/b)/q` cyclically) leaves
`[0,1)` — the grid-artefact test, as a Boolean over `ℚ`. -/
def artefactOK (P : Params) (w : List ℤ) (Z : List ℚ) : Bool :=
  decide (0 < w.length) && (Z.length == w.length) &&
  ((List.range w.length).all fun j =>
    (P.q : ℚ) * Z.getD ((j + 1) % w.length) 0 ==
      P.p * Z.getD j 0 - w.getD j 0 - ((P.p : ℚ) - P.q) * (P.a / P.b)) &&
  ((List.range w.length).any fun j => decide (Z.getD j 0 < 0) || decide (1 ≤ Z.getD j 0))

/-- **Grid artefacts are not read by pseudo-orbits.**  If the letters of an avoiding pseudo-orbit
are eventually the word `w`, then `y` is eventually the exact orbit of `w` (any other orbit is
pushed away by `(p/q)^|w|` per period and leaves `[0,1)`); so a word whose exact orbit leaves
`[0,1)` is never read forever. -/
theorem Pseudo.not_artefact {P : Params} (hF : ParamFacts P) {x : ℕ → ℤ} {y : ℕ → ℝ}
    {s : ℕ → ℤ} (h : Pseudo P x y s) {w : List ℤ} {Z : List ℚ} (hA : artefactOK P w Z = true)
    {n₀ r : ℕ} (hs : ∀ m, s (n₀ + m) = w.getD ((r + m) % w.length) 0) : False := by
  simp only [artefactOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.any_eq_true, List.mem_range, Bool.or_eq_true] at hA
  obtain ⟨⟨⟨hL, -⟩, hrec⟩, j, hj, hout⟩ := hA
  set L := w.length
  set c : ℝ := ((P.p : ℝ) - P.q) * (P.a / P.b)
  set Y : ℕ → ℝ := fun m => ((Z.getD ((r + m) % L) 0 : ℚ) : ℝ)
  have hq : (0 : ℝ) < P.q := by exact_mod_cast (by have := hF.q1; omega : 0 < P.q)
  have hpq : (P.q : ℝ) < P.p := by exact_mod_cast hF.pq
  have hYrec : ∀ m, (P.q : ℝ) * Y (m + 1) = P.p * Y m - s (n₀ + m) - c := by
    intro m
    have e := hrec ((r + m) % L) (Nat.mod_lt _ hL)
    rw [Nat.mod_add_mod, show r + m + 1 = r + (m + 1) by omega] at e
    have e' := congrArg (fun z : ℚ => (z : ℝ)) e
    simp only [Rat.cast_mul, Rat.cast_sub, Rat.cast_natCast, Rat.cast_intCast, Rat.cast_div]
      at e'
    simp only [Y, c, hs]
    rw [e']
  have hYper : ∀ m, Y (m + L) = Y m := fun m => by
    simp only [Y]; rw [← Nat.add_assoc, Nat.add_mod_right]
  -- `u = y − Y` is multiplied by `p/q` at every step
  set u : ℕ → ℝ := fun m => y (n₀ + m) - Y m
  have hu : ∀ m, u (m + 1) = (P.p / P.q) * u m := by
    intro m
    have e1 := h.recy (n₀ + m)
    have e2 := hYrec m
    simp only [u]
    rw [show n₀ + (m + 1) = n₀ + m + 1 by omega]
    field_simp
    linear_combination e1 - e2
  have hupow : ∀ m, u m = (P.p / P.q) ^ m * u 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [hu, ih, pow_succ]; ring
  have hu0 : u 0 = 0 := by
    by_contra hne
    set lamL : ℝ := (P.p / P.q) ^ L
    have hlam : 1 < lamL := one_lt_pow₀ ((one_lt_div hq).2 hpq) hL.ne'
    have hk : ∀ k, y (n₀ + k * L) = Y 0 + lamL ^ k * u 0 := by
      intro k
      have hYk : Y (k * L) = Y 0 := by
        induction k with
        | zero => simp
        | succ k ih => rw [Nat.succ_mul, hYper, ih]
      have := hupow (k * L)
      have e : ((P.p : ℝ) / P.q) ^ (k * L) = lamL ^ k := by rw [mul_comm, pow_mul]
      rw [e] at this
      simp only [u, Nat.add_zero] at this ⊢
      linarith
    have hB : ∀ k, |lamL ^ k * u 0| ≤ 1 + |Y 0| := by
      intro k
      have := hk k
      have h0 := h.y0 (n₀ + k * L)
      have h1 := h.y1 (n₀ + k * L)
      rw [abs_le]
      constructor <;> cases abs_cases (Y 0) <;> linarith
    obtain ⟨k, hk'⟩ := pow_unbounded_of_one_lt ((1 + |Y 0|) / |u 0|) hlam
    have hpos : 0 < |u 0| := abs_pos.2 hne
    have := hB k
    rw [abs_mul, abs_of_pos (pow_pos (by linarith) k)] at this
    rw [div_lt_iff₀ hpos] at hk'
    linarith
  -- so `y` is the exact orbit, which leaves `[0,1)` at phase `j`
  set m := j + L - r % L
  have hm : (r + m) % L = j := by
    have hr := Nat.mod_lt r hL
    have : r + m = (j + L * (r / L + 1)) := by
      have := Nat.div_add_mod r L
      simp only [m]
      rw [Nat.mul_add, Nat.mul_one]
      omega
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  have hy : y (n₀ + m) = (Z.getD j 0 : ℝ) := by
    have := hupow m
    rw [hu0, mul_zero] at this
    simp only [u, Y, hm] at this
    linarith
  have h0 := h.y0 (n₀ + m)
  have h1 := h.y1 (n₀ + m)
  rw [hy] at h0 h1
  rcases hout with ho | ho
  · have : ((Z.getD j 0 : ℚ) : ℝ) < 0 := by exact_mod_cast ho
    linarith
  · have : (1 : ℝ) ≤ ((Z.getD j 0 : ℚ) : ℝ) := by exact_mod_cast ho
    linarith

end Word

/-- The parameter facts of a checked certificate. -/
theorem Checked.paramFacts {P : Params} {C : Cert} (hc : Checked P C) : ParamFacts P := by
  have hh := hc.head
  simp only [checkHead, Bool.and_eq_true] at hh
  exact DubC2.Gen.paramFacts hh.1.1.1.1.1

/-- **The surviving words, artefacts removed.**  If the cycle certificate's words are the
realized words `Wr` followed by grid artefacts `arts` (each with its exact orbit leaving
`[0,1)`), then every avoiding pseudo-orbit eventually reads a word of `Wr` forever. -/
@[category API, AMS 11 37 68, ref "DN05", group "dubc2_atlas"]
theorem Pseudo.eventually_realized_word {P : Params} {C : Cert} (hc : Checked P C)
    {Wr : List (List ℤ)} {arts : List (List ℤ × List ℚ)} {cyc : List (List ℕ × ℕ × ℕ)}
    {pot : List ℕ} (hcc : CycChecked P C (Wr ++ arts.map Prod.fst) cyc pot)
    (ha : arts.all (fun a => artefactOK P a.1 a.2) = true)
    {x : ℕ → ℤ} {y : ℕ → ℝ} {s : ℕ → ℤ} (h : Pseudo P x y s) :
    ∃ n₀, ∃ w ∈ Wr, ∃ r, ∀ m, s (n₀ + m) = w.getD ((r + m) % w.length) 0 := by
  obtain ⟨n₀, w, hw, r, -, hm⟩ := h.eventually_word hc hcc
  rcases List.mem_append.1 hw with hw | hw
  · exact ⟨n₀, w, hw, r, hm⟩
  · obtain ⟨a, ha', rfl⟩ := List.mem_map.1 hw
    exact (h.not_artefact hc.paramFacts (List.all_eq_true.1 ha a ha') hm).elim


end DubC2.Gen
