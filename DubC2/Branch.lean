/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.Horseshoe

/-!
# Branching witnesses: the necessity half of certificate completeness (T5(iv))

The **follower automaton** of a cell (`DubC2/xfrontier.py`, note §§11–12 of
`plans/note-dubC2T-M0.html`) has as states a residue set per prime and a half-open interval
`[lo, hi) ⊆ [0, 1)`; the letter `s` maps the interval to `f_s[lo, hi) ∩ [0, 1)` with
`f_s(y) = (p·y − s − (p−q)·a/b)/q` (`DubC2.Gen.Branch.istep`).  A **branching witness** is the
decidable trace of a follower state with two different loops: a residue `R`, two distinct words
`w₁ ≠ w₂` of one length returning `R mod l` to itself through nonzero residues, and an interval
`I = [lo, hi)` with `0 ≤ lo < hi ≤ 1` that each word's clipped image contains.

Then every finite concatenation of `w₁`, `w₂` is the label of a path of the certificate graph
of every cell count `D` (a finite pseudo-orbit segment, realized backwards from `lo`); a König
argument on the finite graph (`DubC2.Gen.Branch.exists_path_of_forall`) turns the coded infinite
concatenation into an infinite path; and a checked certificate makes the letters of every infinite
path eventually periodic (`DubC2.Gen.isEventuallyPeriodic_of_path`), which the squares coding is not.
So **no certificate is checked at any `D` and `M`** (`DubC2.Gen.not_checked_of_branchOK`).

Unlike a horseshoe (`DubC2.Gen.not_checked_of_horseOK`) no closed invariant interval and no infinite
pseudo-orbit is needed: the obstruction lives in the finite admissible words alone.  This is why it
is the exact converse of the sufficiency theorem of note §12 (a finite follower automaton without
branching state is certified at the common denominator `D` of its interval endpoints).

## Main results

* `DubC2.Gen.branchOK` — the Boolean witness check, on integers and rationals only;
* `DubC2.Gen.not_checked_of_branchOK` — soundness, for every `D`, every `M`, and every parameter
  set whose prime lists lie inside the witness's;
* `DubC2.Gen.Branch.exists_path_of_forall` — König's lemma for a finite vertex set.

## References

* [Oda26] Y. Odagiri, *Finite graph certificates for composite terms in rational floor sequences*,
  Zenodo, doi:10.5281/zenodo.22997709 (2026).
-/

namespace DubC2.Gen

open Filter ForMathlib.SubwordComplexity Horse

/-- A branching witness: prime lists, a residue, two words of one length, and an interval
`[lo, hi)`. -/
structure BranchWitness where
  PM : List ℕ
  Pq : List ℕ
  R : ℤ
  w₁ : List ℤ
  w₂ : List ℤ
  lo : ℚ
  hi : ℚ

namespace Branch

/-! ## The follower interval map -/

/-- The forward branch of the letter `s`: `f_s(y) = (p·y − s − (p−q)·a/b)/q`. -/
def fw (p q : ℕ) (a : ℤ) (b : ℕ) (s : ℤ) (y : ℚ) : ℚ :=
  ((p : ℚ) * y - s - ((p : ℚ) - q) * a / b) / q

/-- One follower step of an interval `[lo, hi)`: the image under `f_s`, clipped to `[0, 1)`. -/
def istep (p q : ℕ) (a : ℤ) (b : ℕ) (I : ℚ × ℚ) (s : ℤ) : ℚ × ℚ :=
  (max 0 (fw p q a b s I.1), min 1 (fw p q a b s I.2))

/-- The follower interval after a word. -/
def ifold (p q : ℕ) (a : ℤ) (b : ℕ) (w : List ℤ) (I : ℚ × ℚ) : ℚ × ℚ :=
  w.foldl (istep p q a b) I

/-- `[I.1, I.2) ⊆ [J.1, J.2)`, read on the endpoints. -/
def Within (I J : ℚ × ℚ) : Prop := J.1 ≤ I.1 ∧ I.2 ≤ J.2

theorem Within.trans {I J K : ℚ × ℚ} (h₁ : Within I J) (h₂ : Within J K) : Within I K :=
  ⟨h₂.1.trans h₁.1, h₁.2.trans h₂.2⟩

variable {p q : ℕ} {a : ℤ} {b : ℕ}

theorem fw_sub (hq : (q : ℚ) ≠ 0) (s : ℤ) (u v : ℚ) :
    fw p q a b s u - fw p q a b s v = ((p : ℚ) / q) * (u - v) := by
  simp only [fw]; field_simp; ring

theorem fw_le (hp : (0 : ℚ) ≤ p) (hq : (0 : ℚ) < q) (s : ℤ) {u v : ℚ} (h : u ≤ v) :
    fw p q a b s u ≤ fw p q a b s v := by
  have := fw_sub (p := p) (a := a) (b := b) hq.ne' s v u
  have : 0 ≤ ((p : ℚ) / q) * (v - u) := mul_nonneg (div_nonneg hp hq.le) (by linarith)
  linarith

theorem fw_lt (hp : (0 : ℚ) < p) (hq : (0 : ℚ) < q) (s : ℤ) {u v : ℚ} (h : u < v) :
    fw p q a b s u < fw p q a b s v := by
  have := fw_sub (p := p) (a := a) (b := b) hq.ne' s v u
  have : 0 < ((p : ℚ) / q) * (v - u) := mul_pos (div_pos hp hq) (by linarith)
  linarith

theorem fw_hb (hp : (p : ℚ) ≠ 0) (hq : (q : ℚ) ≠ 0) (s : ℤ) (y : ℚ) :
    fw p q a b s (hb p q a b s y) = y := by
  simp only [fw, hb]; field_simp; ring

theorem istep_mono (hp : (0 : ℚ) ≤ p) (hq : (0 : ℚ) < q) (s : ℤ) {I J : ℚ × ℚ}
    (h : Within I J) : Within (istep p q a b I s) (istep p q a b J s) :=
  ⟨max_le_max le_rfl (fw_le hp hq s h.1), min_le_min le_rfl (fw_le hp hq s h.2)⟩

theorem ifold_mono (hp : (0 : ℚ) ≤ p) (hq : (0 : ℚ) < q) :
    ∀ (w : List ℤ) {I J : ℚ × ℚ}, Within I J →
      Within (ifold p q a b w I) (ifold p q a b w J) := by
  intro w
  induction w with
  | nil => intro I J h; exact h
  | cons s w ih => intro I J h; exact ih (istep_mono hp hq s h)

theorem ifold_append (u v : List ℤ) (I : ℚ × ℚ) :
    ifold p q a b (u ++ v) I = ifold p q a b v (ifold p q a b u I) := by
  simp only [ifold, List.foldl_append]

/-- **Backward realization.**  Every point of the follower interval after `w` is the end of an
orbit segment along `w` that starts in `I` and stays in `[0, 1)`. -/
theorem realize (hp : (0 : ℚ) < p) (hq : (0 : ℚ) < q) :
    ∀ (w : List ℤ) (I : ℚ × ℚ), 0 ≤ I.1 → I.2 ≤ 1 → ∀ y : ℚ,
      (ifold p q a b w I).1 ≤ y → y < (ifold p q a b w I).2 →
      ∃ ys : ℕ → ℚ, ys w.length = y ∧ I.1 ≤ ys 0 ∧ ys 0 < I.2 ∧
        (∀ i ≤ w.length, 0 ≤ ys i ∧ ys i < 1) ∧
        ∀ i < w.length, ys (i + 1) = fw p q a b (w.getD i 0) (ys i) := by
  intro w
  induction w with
  | nil =>
    intro I h0 h1 y hy0 hy1
    refine ⟨fun _ => y, rfl, hy0, hy1, fun i _ => ⟨h0.trans hy0, hy1.trans_le h1⟩, ?_⟩
    intro i hi; simp at hi
  | cons s w ih =>
    intro I h0 h1 y hy0 hy1
    obtain ⟨ys, hyL, hy0', hy1', hys, hrec⟩ :=
      ih (istep p q a b I s) (le_max_left _ _) (min_le_left _ _) y hy0 hy1
    set z := hb p q a b s (ys 0) with hz
    have hfz : fw p q a b s z = ys 0 := fw_hb hp.ne' hq.ne' s _
    have hz0 : I.1 ≤ z := by
      by_contra hc
      push Not at hc
      have := fw_lt (a := a) (b := b) hp hq s hc
      have : fw p q a b s I.1 ≤ ys 0 := (le_max_right _ _).trans hy0'
      linarith
    have hz1 : z < I.2 := by
      by_contra hc
      push Not at hc
      have := fw_le (a := a) (b := b) hp.le hq s hc
      have : ys 0 < fw p q a b s I.2 := hy1'.trans_le (min_le_right _ _)
      linarith
    refine ⟨fun i => Nat.casesOn i z fun j => ys j, hyL, hz0, hz1, ?_, ?_⟩
    · intro i hi
      cases i with
      | zero => exact ⟨h0.trans hz0, hz1.trans_le h1⟩
      | succ j => exact hys j (by simp at hi; omega)
    · intro i hi
      cases i with
      | zero => simpa using hfz.symm
      | succ j =>
        simp only [List.getD_cons_succ]
        exact hrec j (by simp at hi; omega)

/-! ## König's lemma on a finite vertex set -/

/-- From "for every `m` some `x < N` satisfies `Q x m`", with `Q` antitone in `m`, one `x` that
works for every `m`. -/
theorem exists_forall_of_antitone {N : ℕ} {Q : ℕ → ℕ → Prop}
    (hmono : ∀ x m m', m' ≤ m → Q x m → Q x m') (h : ∀ m, ∃ x < N, Q x m) :
    ∃ x < N, ∀ m, Q x m := by
  classical
  by_contra hc
  push Not at hc
  choose f hf using hc
  set B := ∑ x ∈ Finset.range N, (if hx : x < N then f x hx else 0)
  obtain ⟨x, hx, hQ⟩ := h B
  have hle : f x hx ≤ B := by
    have := Finset.single_le_sum (f := fun x => if hx : x < N then f x hx else 0)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hx)
    simpa [hx] using this
  exact hf x hx (hmono x _ _ hle hQ)

/-- **König's lemma.**  If a time-dependent edge relation on the vertices `< N` has paths of every
finite length from time `0`, it has an infinite path from time `0`. -/
theorem exists_path_of_forall {N : ℕ} {E : ℕ → ℕ → ℕ → Prop}
    (h : ∀ m, ∃ v : ℕ → ℕ, (∀ i ≤ m, v i < N) ∧ ∀ i < m, E i (v i) (v (i + 1))) :
    ∃ v : ℕ → ℕ, ∀ n, v n < N ∧ E n (v n) (v (n + 1)) := by
  classical
  -- `G n x`: from vertex `x` at time `n` there are paths of every length
  let G : ℕ → ℕ → Prop := fun n x => x < N ∧ ∀ m, ∃ v : ℕ → ℕ, v 0 = x ∧
    (∀ i ≤ m, v i < N) ∧ ∀ i < m, E (n + i) (v i) (v (i + 1))
  have hstart : ∃ x, G 0 x := by
    obtain ⟨x, hx, hQ⟩ := exists_forall_of_antitone (N := N)
      (Q := fun x m => ∃ v : ℕ → ℕ, v 0 = x ∧ (∀ i ≤ m, v i < N) ∧
        ∀ i < m, E (0 + i) (v i) (v (i + 1)))
      (fun x m m' hm ⟨v, h0, h1, h2⟩ => ⟨v, h0, fun i hi => h1 i (by omega),
        fun i hi => h2 i (by omega)⟩)
      (fun m => by
        obtain ⟨v, h1, h2⟩ := h m
        exact ⟨v 0, h1 0 (Nat.zero_le _), v, rfl, h1, fun i hi => by rw [zero_add]; exact h2 i hi⟩)
    exact ⟨x, hx, hQ⟩
  have hnext : ∀ n x, G n x → ∃ x', E n x x' ∧ G (n + 1) x' := by
    intro n x ⟨_, hx⟩
    obtain ⟨x', hx', hQ⟩ := exists_forall_of_antitone (N := N)
      (Q := fun x' m => E n x x' ∧ ∃ v : ℕ → ℕ, v 0 = x' ∧ (∀ i ≤ m, v i < N) ∧
        ∀ i < m, E (n + 1 + i) (v i) (v (i + 1)))
      (fun x' m m' hm ⟨he, v, h0, h1, h2⟩ => ⟨he, v, h0, fun i hi => h1 i (by omega),
        fun i hi => h2 i (by omega)⟩)
      (fun m => by
        obtain ⟨v, h0, h1, h2⟩ := hx (m + 1)
        refine ⟨v 1, h1 1 (by omega), ?_, fun i => v (i + 1), rfl,
          fun i hi => h1 (i + 1) (by omega), fun i hi => ?_⟩
        · have := h2 0 (by omega); rwa [h0, add_zero] at this
        · have := h2 (i + 1) (by omega)
          rwa [show n + (i + 1) = n + 1 + i by omega] at this)
    exact ⟨x', hQ 0 |>.1, hx', fun m => (hQ m).2⟩
  have hnext' : ∀ n x, ∃ x', G n x → E n x x' ∧ G (n + 1) x' := by
    intro n x
    by_cases hx : G n x
    · obtain ⟨x', h1, h2⟩ := hnext n x hx
      exact ⟨x', fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose f hf using hnext'
  obtain ⟨x₀, hx₀⟩ := hstart
  let v : ℕ → ℕ := fun n => Nat.rec x₀ (fun k xk => f k xk) n
  have hG : ∀ n, G n (v n) := by
    intro n
    induction n with
    | zero => exact hx₀
    | succ k ih => exact (hf k (v k) ih).2
  exact ⟨v, fun n => ⟨(hG n).1, (hf n (v n) (hG n)).1⟩⟩

end Branch

open Branch

/-! ## The check -/

/-- The conditions on one word: residues (as in `wordOK`), letters, and `I ⊆ f_w(I)`. -/
def bwordOK (p q : ℕ) (a : ℤ) (b : ℕ) (H : BranchWitness) (w : List ℤ) : Bool :=
  H.PM.all (fun l =>
    decide (walk p l (invMod q l) (H.R % (l : ℤ)).toNat w w.length = (H.R % (l : ℤ)).toNat) &&
    (List.range w.length).all
      (fun i => decide (walk p l (invMod q l) (H.R % (l : ℤ)).toNat w i ≠ 0))) &&
  H.Pq.all (fun l => w.all (fun s => decide (s % (l : ℤ) ≠ 0))) &&
  decide ((ifold p q a b w (H.lo, H.hi)).1 ≤ H.lo) &&
  decide (H.hi ≤ (ifold p q a b w (H.lo, H.hi)).2)

/-- **The branching check.** -/
def branchOK (p q : ℕ) (a : ℤ) (b : ℕ) (H : BranchWitness) : Bool :=
  decide (0 < H.w₁.length) && decide (H.w₁.length = H.w₂.length) && decide (H.w₁ ≠ H.w₂) &&
  H.PM.all (fun l => decide (2 ≤ l) && decide (q * invMod q l % l = 1)) &&
  decide (0 ≤ H.lo) && decide (H.lo < H.hi) && decide (H.hi ≤ 1) &&
  bwordOK p q a b H H.w₁ && bwordOK p q a b H H.w₂

/-- The content of `bwordOK`. -/
structure BWordFacts (p q : ℕ) (a : ℤ) (b : ℕ) (H : BranchWitness) (w : List ℤ) : Prop where
  ret : ∀ l ∈ H.PM,
    walk p l (invMod q l) (H.R % (l : ℤ)).toNat w w.length = (H.R % (l : ℤ)).toNat
  av : ∀ l ∈ H.PM, ∀ i < w.length, walk p l (invMod q l) (H.R % (l : ℤ)).toNat w i ≠ 0
  sav : ∀ l ∈ H.Pq, ∀ s ∈ w, s % (l : ℤ) ≠ 0
  within : Within (H.lo, H.hi) (ifold p q a b w (H.lo, H.hi))

theorem bwordFacts {p q : ℕ} {a : ℤ} {b : ℕ} {H : BranchWitness} {w : List ℤ}
    (h : bwordOK p q a b H w = true) : BWordFacts p q a b H w := by
  simp only [bwordOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
    at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨fun l hl => (h1 l hl).1, fun l hl i hi => (h1 l hl).2 i hi, h2, h3, h4⟩

/-! ## Soundness -/

/-- **A checked branching witness rules out every certificate** for every parameter set with the
same base and shift whose prime lists are contained in the witness's — for every cell count `D`
and every modulus `M`. -/
@[category research solved, AMS 11 37, ref "Oda26", group "dubc2_obstruction"]
theorem not_checked_of_branchOK {P : Params} {C : Cert} (H : BranchWitness)
    (h : branchOK P.p P.q P.a P.b H = true) (hPM : ∀ l ∈ P.PM, l ∈ H.PM)
    (hPq : ∀ l ∈ P.Pq, l ∈ H.Pq) : ¬ Checked P C := by
  classical
  intro hc
  have hF : ParamFacts P := by
    have hh := hc.head
    simp only [checkHead, Bool.and_eq_true] at hh
    exact paramFacts hh.1.1.1.1.1
  simp only [branchOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hL, hlen⟩, hne⟩, hPMw⟩, hlo0⟩, hlohi⟩, hhi1⟩, hw₁⟩, hw₂⟩ := h
  have hW : ∀ k, BWordFacts P.p P.q P.a P.b H (hblk H.w₁ H.w₂ k) := fun k => by
    rcases hblk_cases (w₁ := H.w₁) (w₂ := H.w₂) k with e | e <;> rw [e]
    · exact bwordFacts hw₁
    · exact bwordFacts hw₂
  set L := H.w₁.length with hLdef
  have hbl : ∀ k, (hblk H.w₁ H.w₂ k).length = L := hblk_length hlen
  set s := hseq H.w₁ H.w₂ with hsdef
  have hsat : ∀ k i, i < L → s (k * L + i) = (hblk H.w₁ H.w₂ k).getD i 0 :=
    fun k i hi => hseq_at hL k hi
  have hp0 : (0 : ℚ) < P.p := by exact_mod_cast (by have := hF.pq; omega : 0 < P.p)
  have hq0 : (0 : ℚ) < P.q := by exact_mod_cast (by have := hF.q1; omega : 0 < P.q)
  have hb0 : (0 : ℚ) < P.b := by exact_mod_cast hF.b0
  set I : ℚ × ℚ := (H.lo, H.hi) with hI
  -- the word of the first `k` blocks keeps `I` inside its follower interval
  set W : ℕ → List ℤ := fun k => (List.range (k * L)).map s with hW'
  have hWsucc : ∀ k, W (k + 1) = W k ++ hblk H.w₁ H.w₂ k := by
    intro k
    simp only [hW', show (k + 1) * L = k * L + L by ring, List.range_add, List.map_append,
      List.map_map]
    congr 1
    refine List.ext_getElem (by simp [hbl k]) fun i h1 h2 => ?_
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range, Function.comp_apply]
    rw [hsat k i h1, List.getD_eq_getElem _ _ (by rw [hbl k]; exact h1)]
  have hWin : ∀ k, Within I (ifold P.p P.q P.a P.b (W k) I) := by
    intro k
    induction k with
    | zero =>
      simp only [hW', zero_mul, List.range_zero, List.map_nil]
      exact ⟨le_rfl, le_rfl⟩
    | succ k ih =>
      rw [hWsucc, ifold_append]
      exact (hW k).within.trans (ifold_mono hp0.le hq0 _ ih)
  have hWget : ∀ k i, i < k * L → (W k).getD i 0 = s i := by
    intro k i hi
    rw [List.getD_eq_getElem _ _ (by simp [hW']; exact hi)]
    simp [hW']
  have hWlen : ∀ k, (W k).length = k * L := fun k => by simp [hW']
  -- residues
  have hM0 : (0 : ℤ) < P.M := by exact_mod_cast hF.M0
  set r₀ : ℕ := (H.R % P.M).toNat with hr₀
  have hr₀M : r₀ < P.M := by
    have := Int.emod_lt_of_pos H.R hM0
    have := Int.emod_nonneg H.R hM0.ne'
    omega
  set r := rs P r₀ s with hr
  have hrlt : ∀ n, r n < P.M := by
    intro n; cases n with
    | zero => exact hr₀M
    | succ n => exact rnext_lt hF _ _
  have hrav : ∀ n, ∀ l ∈ P.PM, r n % l ≠ 0 :=
    rs_av_of_blocks hF hL hlen hPM hPMw
      (fun k l hl => by have h := (hW k).ret l hl; rw [hbl k] at h; exact h)
      (fun k l hl i hi => (hW k).av l hl i (by rw [hbl k]; exact hi))
  have hsav : ∀ n, ∀ l ∈ P.Pq, s n % (l : ℤ) ≠ 0 := by
    intro n l hl
    have hlH := hPq l hl
    rcases hseq_mem hL hlen n with hm | hm
    · exact (bwordFacts hw₁).sav l hlH _ hm
    · exact (bwordFacts hw₂).sav l hlH _ hm
  -- finite paths of every length
  have hfin : ∀ m, ∃ v : ℕ → ℕ, (∀ i ≤ m, v i < P.nV) ∧ ∀ i < m,
      PseudoOrbit.ptix P s i < P.nA ∧ P.letter (PseudoOrbit.ptix P s i) = s i ∧
        v (i + 1) ∈ P.succList (v i) (P.letter (PseudoOrbit.ptix P s i)) := by
    intro m
    have hmL : m + 1 ≤ (m + 1) * L := Nat.le_mul_of_pos_right _ hL
    obtain ⟨ys, -, -, -, hys, hrec⟩ := realize (a := P.a) (b := P.b) hp0 hq0 (W (m + 1)) I hlo0
      hhi1 H.lo (hWin (m + 1)).1 (hlohi.trans_le (hWin (m + 1)).2)
    rw [hWlen] at hys hrec
    set y : ℕ → ℝ := fun i => (ys i : ℝ)
    have hst : ∀ i, i < (m + 1) * L → PseudoOrbit.pvtx P r y i < P.nV ∧ PseudoOrbit.ptix P s i < P.nA ∧
        P.letter (PseudoOrbit.ptix P s i) = s i ∧
          PseudoOrbit.pvtx P r y (i + 1) ∈ P.succList (PseudoOrbit.pvtx P r y i)
            (P.letter (PseudoOrbit.ptix P s i)) := by
      intro i hi
      obtain ⟨a0, a1⟩ := hys i hi.le
      obtain ⟨b0, b1⟩ := hys (i + 1) hi
      have e := hrec i hi
      rw [hWget _ _ hi] at e
      refine PseudoOrbit.step_of hF i (hrlt i) (show (0 : ℝ) ≤ (ys i : ℝ) by exact_mod_cast a0)
        (show (ys i : ℝ) < 1 by exact_mod_cast a1) (show (0 : ℝ) ≤ (ys (i + 1) : ℝ) by exact_mod_cast b0)
        (show (ys (i + 1) : ℝ) < 1 by exact_mod_cast b1) ?_ rfl (hrav i) (hrav (i + 1)) (hsav i)
      have e' : ((ys (i + 1) : ℚ) : ℝ) = ((fw P.p P.q P.a P.b (s i) (ys i) : ℚ) : ℝ) := by rw [e]
      simp only [fw] at e'
      push_cast at e'
      simp only [y]
      have hq' : (P.q : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
      have hb' : (P.b : ℝ) ≠ 0 := by exact_mod_cast hb0.ne'
      rw [e']
      field_simp
      ring
    exact ⟨PseudoOrbit.pvtx P r y, fun i hi => (hst i (by omega)).1,
      fun i hi => (hst i (by omega)).2⟩
  have hlet : ∀ n, PseudoOrbit.ptix P s n < P.nA ∧ P.letter (PseudoOrbit.ptix P s n) = s n := by
    intro n
    obtain ⟨v, -, hv⟩ := hfin (n + 1)
    exact ⟨(hv n (by omega)).1, (hv n (by omega)).2.1⟩
  -- König: an infinite path labelled by the coded concatenation
  obtain ⟨v, hv⟩ := exists_path_of_forall (N := P.nV)
    (E := fun n x x' => x' ∈ P.succList x (P.letter (PseudoOrbit.ptix P s n)))
    (fun m => by
      obtain ⟨v, h1, h2⟩ := hfin m
      exact ⟨v, h1, fun i hi => (h2 i hi).2.2⟩)
  have hp : IsPath P 0 v (PseudoOrbit.ptix P s) :=
    ⟨fun n _ => (hv n).1, fun n _ => (hlet n).1, fun n _ => (hv n).2⟩
  obtain ⟨M₀, per, hper, hp'⟩ := isEventuallyPeriodic_of_path hc hp
  refine hseq_not_periodic hL hlen hne ⟨M₀, per, hper, fun k hk => ?_⟩
  show s (k + per) = s k
  rw [← (hlet k).2, ← (hlet (k + per)).2, hp' k hk]

/-- A whole row of branching witnesses at once (one `decide`). -/
theorem not_checked_of_branchRow {p q : ℕ} {a : ℤ} {b : ℕ} {ws : List BranchWitness}
    (h : ws.all (branchOK p q a b) = true) :
    ∀ w ∈ ws, ∀ (P : Params) (C : Cert), P.p = p → P.q = q → P.a = a → P.b = b →
      (∀ l ∈ P.PM, l ∈ w.PM) → (∀ l ∈ P.Pq, l ∈ w.Pq) → ¬ Checked P C := by
  intro w hw P C hp hq ha hb hPM hPq
  subst hp hq ha hb
  exact not_checked_of_branchOK w (List.all_eq_true.1 h w hw) hPM hPq

end DubC2.Gen
