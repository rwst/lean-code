/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.ObstructionKit
import Mathlib.Data.List.GetD

/-!
# Horseshoe witnesses: positive-entropy obstructions to certificates

[Oda26] Theorem 42 (`DubC2.Gen.not_checked_of_two_letters`) rules out certificates with a
zero-entropy pseudo-orbit built from two letters.  A **horseshoe witness** is the general two-word
version (the decidable form of [Oda26] Lemma 69): a residue `R`, two distinct letter words
`w₁ ≠ w₂` of one length `L`, and a rational interval `K = [lo, hi]` such that

* per prime `l` of the witness's `PM`, both words carry `R mod l` back to itself through nonzero
  residues (the residue map `r ↦ (p·r + s)·q⁻¹ mod l`);
* every letter avoids every prime of the witness's `Pq`;
* the inverse branches `h_s(y) = (q·y + s + (p−q)·a/b)/p` composed along either word map `K` into
  itself, and every intermediate image of `K` lies in `[0, 1)`.

Then every infinite concatenation of `w₁` and `w₂` is the letter sequence of an avoiding
pseudo-orbit (nested intervals, contraction `(q/p)^L`), and the concatenation coded by the squares
is not eventually periodic; by [Oda26] Lemma 38 (`DubC2.Gen.PseudoOrbit.eventuallyPeriodic`) no
certificate is checked, for any cell count `D`, any modulus `M`, and any parameter set whose prime
lists lie inside the witness's (`DubC2.Gen.not_checked_of_horseOK`).

This is a statement about the certificate method, never about the real orbit: a horseshoe
pseudo-orbit need not come from any `ξ`.

## Main results

* `DubC2.Gen.horseOK` — the Boolean witness check, on integers and rationals only;
* `DubC2.Gen.not_checked_of_horseOK` — soundness;
* `DubC2.Gen.not_checked_of_horseRow` — a row of witnesses in one `decide`.

## References

* [Oda26] Y. Odagiri, *Finite graph certificates for composite terms in rational floor sequences*,
  Zenodo, doi:10.5281/zenodo.22997709 (2026).
-/

namespace DubC2.Gen

open Filter ForMathlib.SubwordComplexity

/-- A horseshoe witness: prime lists, a residue, two words of one length, and an interval. -/
structure HorseWitness where
  PM : List ℕ
  Pq : List ℕ
  R : ℤ
  w₁ : List ℤ
  w₂ : List ℤ
  lo : ℚ
  hi : ℚ

namespace Horse

/-! ## The inverse branches and the residue walk -/

/-- The inverse branch of the letter `s`: `h_s(y) = (q·y + s + (p−q)·a/b)/p`. -/
def hb {K : Type*} [Field K] (p q : ℕ) (a : ℤ) (b : ℕ) (s : ℤ) (y : K) : K :=
  ((q : K) * y + s + ((p : K) - q) * a / b) / p

/-- The image of `y` under the inverse branches of a word, last letter first. -/
def back {K : Type*} [Field K] (p q : ℕ) (a : ℤ) (b : ℕ) : List ℤ → K → K
  | [], y => y
  | s :: w, y => hb p q a b s (back p q a b w y)

theorem cast_back (p q : ℕ) (a : ℤ) (b : ℕ) (w : List ℤ) (y : ℚ) :
    ((back p q a b w y : ℚ) : ℝ) = back p q a b w (y : ℝ) := by
  induction w with
  | nil => rfl
  | cons s w ih => simp only [back, hb, ← ih]; push_cast; ring

/-- A candidate inverse of `q` mod `l` (checked separately). -/
def invMod (q l : ℕ) : ℕ := ((List.range l).find? (fun i => q * i % l == 1)).getD 0

/-- One residue step mod `l`: `r ↦ (p·r + s)·inv mod l`. -/
def stepMod (p l inv : ℕ) (r : ℕ) (s : ℤ) : ℕ := ((((p : ℤ) * r + s) * inv) % l).toNat

/-- The residue mod `l` after the first `i` letters of `w`, from `r`. -/
def walk (p l inv r : ℕ) (w : List ℤ) (i : ℕ) : ℕ := (w.take i).foldl (stepMod p l inv) r

theorem walk_zero (p l inv r : ℕ) (w : List ℤ) : walk p l inv r w 0 = r := by
  simp [walk]

theorem walk_succ (p l inv r : ℕ) (w : List ℤ) {i : ℕ} (hi : i < w.length) :
    walk p l inv r w (i + 1) = stepMod p l inv (walk p l inv r w i) (w.getD i 0) := by
  rw [walk, walk, List.take_add_one, List.getElem?_eq_getElem hi, List.foldl_append,
    List.getD_eq_getElem _ _ hi]
  rfl

theorem foldl_stepMod_lt {p l inv : ℕ} (hl : 0 < l) :
    ∀ (w : List ℤ) (r : ℕ), r < l → w.foldl (stepMod p l inv) r < l := by
  intro w
  induction w with
  | nil => intro r hr; exact hr
  | cons s w ih =>
    intro r _
    refine ih _ ?_
    have hl' : (0 : ℤ) < l := by exact_mod_cast hl
    have h1 := Int.emod_nonneg (((p : ℤ) * r + s) * inv) hl'.ne'
    have h2 := Int.emod_lt_of_pos (((p : ℤ) * r + s) * inv) hl'
    simp only [stepMod]
    omega

theorem walk_lt {p l inv r : ℕ} (hl : 0 < l) (hr : r < l) (w : List ℤ) (i : ℕ) :
    walk p l inv r w i < l :=
  foldl_stepMod_lt hl _ _ hr

end Horse

open Horse

/-! ## The check -/

/-- The conditions on one word. -/
def wordOK (p q : ℕ) (a : ℤ) (b : ℕ) (H : HorseWitness) (w : List ℤ) : Bool :=
  H.PM.all (fun l =>
    decide (walk p l (invMod q l) (H.R % (l : ℤ)).toNat w w.length = (H.R % (l : ℤ)).toNat) &&
    (List.range w.length).all
      (fun i => decide (walk p l (invMod q l) (H.R % (l : ℤ)).toNat w i ≠ 0))) &&
  H.Pq.all (fun l => w.all (fun s => decide (s % (l : ℤ) ≠ 0))) &&
  decide (H.lo ≤ back p q a b w H.lo) && decide (back p q a b w H.hi ≤ H.hi) &&
  (List.range w.length).all (fun i =>
    decide (0 ≤ back p q a b (w.drop i) H.lo) && decide (back p q a b (w.drop i) H.hi < 1))

/-- **The horseshoe check.** -/
def horseOK (p q : ℕ) (a : ℤ) (b : ℕ) (H : HorseWitness) : Bool :=
  decide (0 < H.w₁.length) && decide (H.w₁.length = H.w₂.length) && decide (H.w₁ ≠ H.w₂) &&
  H.PM.all (fun l => decide (2 ≤ l) && decide (q * invMod q l % l = 1)) &&
  wordOK p q a b H H.w₁ && wordOK p q a b H H.w₂

/-- The content of `wordOK`. -/
structure WordFacts (p q : ℕ) (a : ℤ) (b : ℕ) (H : HorseWitness) (w : List ℤ) : Prop where
  ret : ∀ l ∈ H.PM,
    walk p l (invMod q l) (H.R % (l : ℤ)).toNat w w.length = (H.R % (l : ℤ)).toNat
  av : ∀ l ∈ H.PM, ∀ i < w.length, walk p l (invMod q l) (H.R % (l : ℤ)).toNat w i ≠ 0
  sav : ∀ l ∈ H.Pq, ∀ s ∈ w, s % (l : ℤ) ≠ 0
  lo : H.lo ≤ back p q a b w H.lo
  hi : back p q a b w H.hi ≤ H.hi
  img0 : ∀ i < w.length, 0 ≤ back p q a b (w.drop i) H.lo
  img1 : ∀ i < w.length, back p q a b (w.drop i) H.hi < 1

theorem wordFacts {p q : ℕ} {a : ℤ} {b : ℕ} {H : HorseWitness} {w : List ℤ}
    (h : wordOK p q a b H w = true) : WordFacts p q a b H w := by
  simp only [wordOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
    at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨fun l hl => (h1 l hl).1, fun l hl i hi => (h1 l hl).2 i hi, h2, h3, h4,
    fun i hi => (h5 i hi).1, fun i hi => (h5 i hi).2⟩

/-! ## The coded concatenation -/

section Coding

variable (w₁ w₂ : List ℤ)

open Classical in
/-- The `k`-th block: `w₁` at the squares, `w₂` elsewhere. -/
noncomputable def hblk (k : ℕ) : List ℤ := if InS 1 k then w₁ else w₂

/-- The concatenation `hblk 0 · hblk 1 · hblk 2 ⋯`. -/
noncomputable def hseq (n : ℕ) : ℤ := (hblk w₁ w₂ (n / w₁.length)).getD (n % w₁.length) 0

variable {w₁ w₂}

theorem hblk_cases (k : ℕ) : hblk w₁ w₂ k = w₁ ∨ hblk w₁ w₂ k = w₂ := by
  unfold hblk; split_ifs <;> simp

theorem hblk_length (hlen : w₁.length = w₂.length) (k : ℕ) :
    (hblk w₁ w₂ k).length = w₁.length := by
  rcases hblk_cases (w₁ := w₁) (w₂ := w₂) k with h | h <;> rw [h]; exact hlen.symm

theorem hseq_at (hL : 0 < w₁.length) (k : ℕ) {i : ℕ} (hi : i < w₁.length) :
    hseq w₁ w₂ (k * w₁.length + i) = (hblk w₁ w₂ k).getD i 0 := by
  have h1 : (k * w₁.length + i) / w₁.length = k := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hL, Nat.div_eq_of_lt hi, zero_add]
  have h2 : (k * w₁.length + i) % w₁.length = i := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  simp only [hseq, h1, h2]

theorem hseq_mem (hL : 0 < w₁.length) (hlen : w₁.length = w₂.length) (n : ℕ) :
    hseq w₁ w₂ n ∈ w₁ ∨ hseq w₁ w₂ n ∈ w₂ := by
  have hi : n % w₁.length < (hblk w₁ w₂ (n / w₁.length)).length := by
    rw [hblk_length hlen]; exact Nat.mod_lt _ hL
  have hm : hseq w₁ w₂ n ∈ hblk w₁ w₂ (n / w₁.length) := by
    simp only [hseq, List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  rcases hblk_cases (w₁ := w₁) (w₂ := w₂) (n / w₁.length) with h | h <;> rw [h] at hm
  · exact Or.inl hm
  · exact Or.inr hm

/-- The coded concatenation of two distinct words of one length is not eventually periodic. -/
theorem hseq_not_periodic (hL : 0 < w₁.length) (hlen : w₁.length = w₂.length) (hne : w₁ ≠ w₂) :
    ¬ IsEventuallyPeriodic (hseq w₁ w₂) := by
  rintro ⟨N, per, hper, hp⟩
  set L := w₁.length with hLdef
  have hmul : ∀ t k, N ≤ k → hseq w₁ w₂ (k + t * per) = hseq w₁ w₂ k := by
    intro t
    induction t with
    | zero => intro k _; simp
    | succ t ih =>
      intro k hk
      rw [show k + (t + 1) * per = k + t * per + per by ring, hp _ (by omega), ih k hk]
  have hext : ∀ u v : List ℤ, u.length = L → v.length = L →
      (∀ i < L, u.getD i 0 = v.getD i 0) → u = v := by
    intro u v hu hv h
    refine List.ext_getElem (hu.trans hv.symm) fun i h1 h2 => ?_
    have := h i (by omega)
    rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this
  have hblkeq : ∀ m, N ≤ m → hblk w₁ w₂ (m + per) = hblk w₁ w₂ m := by
    intro m hm
    refine hext _ _ (hblk_length hlen _) (hblk_length hlen _) fun i hi => ?_
    have hNm : N ≤ m * L + i := le_trans hm (le_trans (Nat.le_mul_of_pos_right m hL) (by omega))
    have := hmul L (m * L + i) hNm
    rw [show m * L + i + L * per = (m + per) * L + i by ring, hseq_at hL _ hi,
      hseq_at hL _ hi] at this
    exact this
  refine InS.not_periodic (le_refl 1) hper (N := N) fun m hm => ?_
  have h := hblkeq m hm
  unfold hblk at h
  constructor
  · intro h1
    by_contra h2
    simp only [h1, h2, ↓reduceIte] at h
    exact hne h
  · intro h1
    by_contra h2
    simp only [h1, h2, ↓reduceIte] at h
    exact hne h.symm

end Coding

/-! ## The series point -/

section Series

/-- `Σⱼ ρʲ·u(n+j)`. -/
noncomputable def gs (ρ : ℝ) (u : ℕ → ℝ) (n : ℕ) : ℝ := ∑' j : ℕ, ρ ^ j * u (n + j)

variable {ρ : ℝ} {u : ℕ → ℝ} {B : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hu : ∀ n, |u n| ≤ B)
include hρ0 hρ1 hu

theorem gs_summable (n : ℕ) : Summable fun j : ℕ => ρ ^ j * u (n + j) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hρ0 hρ1).mul_right B)
    fun j => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hρ0 _)]
  exact mul_le_mul_of_nonneg_left (hu _) (pow_nonneg hρ0 _)

theorem gs_rec (n : ℕ) : gs ρ u n = u n + ρ * gs ρ u (n + 1) := by
  simp only [gs]
  rw [(gs_summable hρ0 hρ1 hu n).tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, one_mul, add_zero]
  congr 1
  refine tsum_congr fun j => ?_
  rw [pow_succ, show n + (j + 1) = n + 1 + j by ring]; ring

theorem gs_abs_le (n : ℕ) : |gs ρ u n| ≤ B / (1 - ρ) := by
  rw [div_eq_mul_inv]
  show ‖∑' j : ℕ, ρ ^ j * u (n + j)‖ ≤ _
  refine tsum_of_norm_bounded ((hasSum_geometric_of_lt_one hρ0 hρ1).mul_left B) fun j => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hρ0 _), mul_comm B]
  exact mul_le_mul_of_nonneg_left (hu _) (pow_nonneg hρ0 _)

end Series

/-! ## Nested intervals along one block -/

section Block

variable {p q : ℕ} {a : ℤ} {b : ℕ} {y : ℕ → ℝ} {s : ℕ → ℤ}

theorem hb_sub (hp : (p : ℝ) ≠ 0) (c : ℤ) (u v : ℝ) :
    hb p q a b c u - hb p q a b c v = ((q : ℝ) / p) * (u - v) := by
  simp only [hb]; field_simp; ring

/-- Along a block `w` starting at `n₀`, an `ε`-enlargement of `[lo, hi]` at the block's end
pulls back to the images of `lo, hi`, enlarged by `(q/p)^(L−i)·ε`. -/
theorem block_bounds (hp : (0 : ℝ) < p) (hrec : ∀ n, y n = hb p q a b (s n) (y (n + 1)))
    {w : List ℤ} {n₀ : ℕ} (hs : ∀ i < w.length, s (n₀ + i) = w.getD i 0) {ε lo hi : ℝ}
    (hlo : lo - ε ≤ y (n₀ + w.length)) (hhi : y (n₀ + w.length) ≤ hi + ε) :
    ∀ i ≤ w.length,
      back p q a b (w.drop i) lo - ((q : ℝ) / p) ^ (w.length - i) * ε ≤ y (n₀ + i) ∧
      y (n₀ + i) ≤ back p q a b (w.drop i) hi + ((q : ℝ) / p) ^ (w.length - i) * ε := by
  have hρ : (0 : ℝ) ≤ (q : ℝ) / p := div_nonneg (Nat.cast_nonneg _) hp.le
  set ρ : ℝ := (q : ℝ) / p with hρdef
  have key : ∀ j, j ≤ w.length →
      back p q a b (w.drop (w.length - j)) lo - ρ ^ j * ε ≤ y (n₀ + (w.length - j)) ∧
      y (n₀ + (w.length - j)) ≤ back p q a b (w.drop (w.length - j)) hi + ρ ^ j * ε := by
    intro j
    induction j with
    | zero =>
      intro _
      simp only [Nat.sub_zero, List.drop_length, back, pow_zero, one_mul]
      exact ⟨hlo, hhi⟩
    | succ j ih =>
      intro hj
      obtain ⟨h1, h2⟩ := ih (by omega)
      have hiL : w.length - (j + 1) < w.length := by omega
      have hi1 : w.length - j = w.length - (j + 1) + 1 := by omega
      rw [hi1] at h1 h2
      set i := w.length - (j + 1)
      have hd : w.drop i = w.getD i 0 :: w.drop (i + 1) := by
        rw [List.getD_eq_getElem _ _ hiL]; exact List.drop_eq_getElem_cons hiL
      have hy := hrec (n₀ + i)
      rw [hs i hiL, show n₀ + i + 1 = n₀ + (i + 1) by ring] at hy
      rw [hd, back, back, hy, pow_succ]
      have e1 := hb_sub (q := q) (a := a) (b := b) hp.ne' (w.getD i 0) (y (n₀ + (i + 1)))
        (back p q a b (w.drop (i + 1)) lo)
      have e2 := hb_sub (q := q) (a := a) (b := b) hp.ne' (w.getD i 0) (y (n₀ + (i + 1)))
        (back p q a b (w.drop (i + 1)) hi)
      rw [← hρdef] at e1 e2
      constructor
      · have : ρ * (-(ρ ^ j * ε)) ≤ ρ * (y (n₀ + (i + 1)) - back p q a b (w.drop (i + 1)) lo) :=
          mul_le_mul_of_nonneg_left (by linarith) hρ
        nlinarith
      · have : ρ * (y (n₀ + (i + 1)) - back p q a b (w.drop (i + 1)) hi) ≤ ρ * (ρ ^ j * ε) :=
          mul_le_mul_of_nonneg_left (by linarith) hρ
        nlinarith
  intro i hi
  have := key (w.length - i) (by omega)
  rwa [show w.length - (w.length - i) = i by omega] at this

end Block

/-! ## Soundness -/

/-- One residue step, mod a divisor `l` of `M`. -/
theorem rnext_modEq {P : Params} (hF : ParamFacts P) {l inv : ℕ} (hl : 2 ≤ l)
    (hlM : (l : ℤ) ∣ P.M) (hinv : P.q * inv % l = 1) {x ρ : ℕ} (s : ℤ)
    (hx : (x : ℤ) ≡ ρ [ZMOD l]) :
    (P.rnext x s : ℤ) ≡ stepMod P.p l inv ρ s [ZMOD l] := by
  have hl0 : (0 : ℤ) < l := by exact_mod_cast (by omega : 0 < l)
  have hqi : (P.q : ℤ) * inv ≡ 1 [ZMOD l] := by
    have := congrArg (Nat.cast : ℕ → ℤ) hinv
    push_cast at this
    rw [Int.ModEq, this, Int.emod_eq_of_lt (by norm_num) (by exact_mod_cast (by omega : 1 < l))]
  have hstep : (P.q : ℤ) * P.rnext x s ≡ (P.p : ℤ) * ρ + s [ZMOD l] := by
    have h1 : (P.q : ℤ) * P.rnext x s ≡ (P.p : ℤ) * x + s [ZMOD l] :=
      (Int.modEq_of_dvd (hlM.trans (q_mul_rnext hF x s))).symm
    exact h1.trans ((hx.mul_left _).add_right _)
  have hcast : ((stepMod P.p l inv ρ s : ℕ) : ℤ) = (((P.p : ℤ) * ρ + s) * inv) % l :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hl0.ne')
  rw [hcast]
  calc (P.rnext x s : ℤ) = 1 * P.rnext x s := (one_mul _).symm
    _ ≡ ((P.q : ℤ) * inv) * P.rnext x s [ZMOD l] := hqi.symm.mul_right _
    _ = inv * ((P.q : ℤ) * P.rnext x s) := by ring
    _ ≡ inv * ((P.p : ℤ) * ρ + s) [ZMOD l] := hstep.mul_left _
    _ = ((P.p : ℤ) * ρ + s) * inv := by ring
    _ ≡ (((P.p : ℤ) * ρ + s) * inv) % l [ZMOD l] := (Int.mod_modEq _ _).symm

/-- **The residues of a block concatenation avoid `PM`**: if both words carry `R mod l` back to
itself through nonzero residues, for every prime `l` of `PMw ⊇ P.PM`, then so does the residue
sequence `rs` of the coded concatenation `hseq w₁ w₂`, started at `R mod M`. -/
theorem rs_av_of_blocks {P : Params} (hF : ParamFacts P) {PMw : List ℕ} {R : ℤ}
    {w₁ w₂ : List ℤ} (hL : 0 < w₁.length) (hlen : w₁.length = w₂.length)
    (hPM : ∀ l ∈ P.PM, l ∈ PMw) (hPMw : ∀ l ∈ PMw, 2 ≤ l ∧ P.q * invMod P.q l % l = 1)
    (hret : ∀ k, ∀ l ∈ PMw,
      walk P.p l (invMod P.q l) (R % (l : ℤ)).toNat (hblk w₁ w₂ k) w₁.length = (R % (l : ℤ)).toNat)
    (hav : ∀ k, ∀ l ∈ PMw, ∀ i < w₁.length,
      walk P.p l (invMod P.q l) (R % (l : ℤ)).toNat (hblk w₁ w₂ k) i ≠ 0) :
    ∀ n, ∀ l ∈ P.PM, rs P (R % P.M).toNat (hseq w₁ w₂) n % l ≠ 0 := by
  set L := w₁.length with hLdef
  have hbl : ∀ k, (hblk w₁ w₂ k).length = L := hblk_length hlen
  set s := hseq w₁ w₂ with hsdef
  have hsat : ∀ k i, i < L → s (k * L + i) = (hblk w₁ w₂ k).getD i 0 :=
    fun k i hi => hseq_at hL k hi
  have hM0 : (0 : ℤ) < P.M := by exact_mod_cast hF.M0
  set r₀ : ℕ := (R % P.M).toNat with hr₀
  have hr₀c : (r₀ : ℤ) = R % P.M := Int.toNat_of_nonneg (Int.emod_nonneg _ hM0.ne')
  set r := rs P r₀ s with hr
  intro n l hl
  have hlH := hPM l hl
  obtain ⟨hl2, hinv⟩ := hPMw l hlH
  have hlM : (l : ℤ) ∣ P.M := by exact_mod_cast Nat.dvd_of_mod_eq_zero (hF.PM l hl)
  have hl0 : (0 : ℤ) < l := by exact_mod_cast (by omega : 0 < l)
  set ρ₀ : ℕ := (R % (l : ℤ)).toNat with hρ₀
  have hρ₀c : (ρ₀ : ℤ) = R % l := Int.toNat_of_nonneg (Int.emod_nonneg _ hl0.ne')
  have hρ₀l : ρ₀ < l := by
    have := Int.emod_lt_of_pos R hl0
    omega
  have hmain : ∀ k, ∀ i ≤ L, (r (k * L + i) : ℤ) ≡
      walk P.p l (invMod P.q l) ρ₀ (hblk w₁ w₂ k) i [ZMOD l] := by
    intro k
    induction k with
    | zero =>
      intro i
      induction i with
      | zero =>
        intro _
        simp only [zero_mul, add_zero, walk_zero]
        change (r₀ : ℤ) ≡ ρ₀ [ZMOD l]
        rw [hr₀c, hρ₀c, Int.ModEq, Int.emod_emod_of_dvd _ hlM, Int.emod_emod]
      | succ i ih =>
        intro hi
        have hi' : i < (hblk w₁ w₂ 0).length := by rw [hbl]; omega
        rw [walk_succ _ _ _ _ _ hi', ← hsat 0 i (by omega)]
        exact rnext_modEq hF hl2 hlM hinv _ (ih (by omega))
    | succ k ihk =>
      intro i
      induction i with
      | zero =>
        intro _
        have h0 := ihk L le_rfl
        rw [show k * L + L = (k + 1) * L + 0 by ring] at h0
        rw [walk_zero]
        rwa [hret k l hlH] at h0
      | succ i ih =>
        intro hi
        have hi' : i < (hblk w₁ w₂ (k + 1)).length := by rw [hbl]; omega
        rw [walk_succ _ _ _ _ _ hi', ← hsat (k + 1) i (by omega)]
        exact rnext_modEq hF hl2 hlM hinv _ (ih (by omega))
  obtain ⟨k, i, hi, rfl⟩ : ∃ k i, i < L ∧ n = k * L + i :=
    ⟨n / L, n % L, Nat.mod_lt _ hL, by rw [Nat.div_add_mod']⟩
  have hm := hmain k i hi.le
  have hwl := walk_lt (p := P.p) (inv := invMod P.q l) (by omega) hρ₀l (hblk w₁ w₂ k) i
  have hw0 := hav k l hlH i hi
  intro h0
  have : ((r (k * L + i) % l : ℕ) : ℤ) = (walk P.p l (invMod P.q l) ρ₀ (hblk w₁ w₂ k) i : ℤ) := by
    push_cast
    rw [hm, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hwl)]
  rw [h0] at this
  exact hw0 (by exact_mod_cast this.symm)

/-- **A checked horseshoe witness rules out every certificate** for every parameter set with the
same base and shift whose prime lists are contained in the witness's — for every cell count `D`
and every modulus `M`. -/
@[category research solved, AMS 11 37, ref "Oda26", group "dubc2_obstruction"]
theorem not_checked_of_horseOK {P : Params} {C : Cert} (H : HorseWitness)
    (h : horseOK P.p P.q P.a P.b H = true) (hPM : ∀ l ∈ P.PM, l ∈ H.PM)
    (hPq : ∀ l ∈ P.Pq, l ∈ H.Pq) : ¬ Checked P C := by
  classical
  intro hc
  have hF : ParamFacts P := by
    have hh := hc.head
    simp only [checkHead, Bool.and_eq_true] at hh
    exact paramFacts hh.1.1.1.1.1
  simp only [horseOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hL, hlen⟩, hne⟩, hPMw⟩, hw₁⟩, hw₂⟩ := h
  have hW : ∀ k, WordFacts P.p P.q P.a P.b H (hblk H.w₁ H.w₂ k) := fun k => by
    rcases hblk_cases (w₁ := H.w₁) (w₂ := H.w₂) k with e | e <;> rw [e]
    · exact wordFacts hw₁
    · exact wordFacts hw₂
  set L := H.w₁.length with hLdef
  have hbl : ∀ k, (hblk H.w₁ H.w₂ k).length = L := hblk_length hlen
  set s := hseq H.w₁ H.w₂ with hsdef
  have hsat : ∀ k i, i < L → s (k * L + i) = (hblk H.w₁ H.w₂ k).getD i 0 :=
    fun k i hi => hseq_at hL k hi
  -- real parameters
  have hq0 : (0 : ℝ) < P.q := by exact_mod_cast (by have := hF.q1; omega : 0 < P.q)
  have hpq : (P.q : ℝ) < P.p := by exact_mod_cast hF.pq
  have hp0 : (0 : ℝ) < P.p := by linarith
  have hb0 : (0 : ℝ) < P.b := by exact_mod_cast hF.b0
  set ρ : ℝ := (P.q : ℝ) / P.p with hρ
  have hρ0 : 0 ≤ ρ := (div_pos hq0 hp0).le
  have hρ1 : ρ < 1 := (div_lt_one hp0).2 hpq
  -- the letter bound and the series point
  obtain ⟨S, hS⟩ : ∃ S : ℝ, ∀ n, |(s n : ℝ)| ≤ S := by
    refine ⟨((H.w₁ ++ H.w₂).map (fun x : ℤ => |(x : ℝ)|)).sum, fun n => ?_⟩
    refine List.single_le_sum (fun x hx => ?_) _ (List.mem_map_of_mem ?_)
    · obtain ⟨z, _, rfl⟩ := List.mem_map.1 hx; exact abs_nonneg _
    · rcases hseq_mem hL hlen n with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ h
  set c : ℝ := ((P.p : ℝ) - P.q) * P.a / P.b with hcdef
  set u : ℕ → ℝ := fun n => ((s n : ℝ) + c) / P.p with hu
  have hub : ∀ n, |u n| ≤ (S + |c|) / P.p := fun n => by
    simp only [hu, abs_div, abs_of_pos hp0]
    exact div_le_div_of_nonneg_right ((abs_add_le _ _).trans (by linarith [hS n])) hp0.le
  set y : ℕ → ℝ := gs ρ u with hy
  have hrec : ∀ n, y n = hb P.p P.q P.a P.b (s n) (y (n + 1)) := fun n => by
    simp only [hy]
    rw [gs_rec hρ0 hρ1 hub n]
    simp only [hu, hb, hρ, hcdef]
    field_simp
    ring
  have hyb : ∀ n, |y n| ≤ (S + |c|) / P.p / (1 - ρ) := gs_abs_le hρ0 hρ1 hub
  -- the boundary points lie in `K`
  set lo : ℝ := (H.lo : ℝ)
  set hi : ℝ := (H.hi : ℝ)
  set E : ℝ := (S + |c|) / P.p / (1 - ρ) + |lo| + |hi| with hE
  have hE0 : 0 ≤ E := by
    have := (abs_nonneg (y 0)).trans (hyb 0)
    simp only [hE]
    linarith [abs_nonneg lo, abs_nonneg hi]
  set lam : ℝ := ρ ^ L with hlam
  have hlam0 : 0 ≤ lam := pow_nonneg hρ0 _
  have hlam1 : lam < 1 := pow_lt_one₀ hρ0 hρ1 hL.ne'
  have hblock : ∀ k (ε : ℝ), lo - ε ≤ y (k * L + L) → y (k * L + L) ≤ hi + ε →
      ∀ i ≤ L, back P.p P.q P.a P.b ((hblk H.w₁ H.w₂ k).drop i) lo - ρ ^ (L - i) * ε ≤
          y (k * L + i) ∧
        y (k * L + i) ≤ back P.p P.q P.a P.b ((hblk H.w₁ H.w₂ k).drop i) hi + ρ ^ (L - i) * ε := by
    intro k ε h1 h2 i hi'
    have := block_bounds (w := hblk H.w₁ H.w₂ k) (n₀ := k * L) hp0 hrec
      (fun i hi => hsat k i (by rw [← hbl k]; exact hi)) (by rwa [hbl k]) (by rwa [hbl k]) i
      (by rw [hbl k]; exact hi')
    rwa [hbl k] at this
  have hbnd : ∀ m k, lo - lam ^ m * E ≤ y (k * L) ∧ y (k * L) ≤ hi + lam ^ m * E := by
    intro m
    induction m with
    | zero =>
      intro k
      obtain ⟨h1, h2⟩ := abs_le.1 (hyb (k * L))
      simp only [pow_zero, one_mul, hE]
      constructor <;> linarith [neg_abs_le lo, le_abs_self hi, le_abs_self lo, neg_abs_le hi]
    | succ m ih =>
      intro k
      obtain ⟨h1, h2⟩ := ih (k + 1)
      rw [show (k + 1) * L = k * L + L by ring] at h1 h2
      have := hblock k _ h1 h2 0 (Nat.zero_le _)
      simp only [List.drop_zero, Nat.sub_zero, Nat.add_zero] at this
      have hlo := (hW k).lo
      have hhi := (hW k).hi
      have hlo' : lo ≤ back P.p P.q P.a P.b (hblk H.w₁ H.w₂ k) lo := by
        have := (Rat.cast_le (K := ℝ)).2 hlo
        rwa [cast_back] at this
      have hhi' : back P.p P.q P.a P.b (hblk H.w₁ H.w₂ k) hi ≤ hi := by
        have := (Rat.cast_le (K := ℝ)).2 hhi
        rwa [cast_back] at this
      rw [pow_succ', mul_assoc]
      constructor <;> linarith [this.1, this.2]
  have hK : ∀ k, lo ≤ y (k * L) ∧ y (k * L) ≤ hi := by
    intro k
    constructor
    · by_contra hcon
      push Not at hcon
      obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show 0 < (lo - y (k * L)) / (E + 1) by
        apply div_pos <;> linarith) hlam1
      have h1 := (hbnd m k).1
      have : lam ^ m * E < lo - y (k * L) := by
        rw [lt_div_iff₀ (by linarith)] at hm
        nlinarith [pow_nonneg hlam0 m]
      linarith
    · by_contra hcon
      push Not at hcon
      obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show 0 < (y (k * L) - hi) / (E + 1) by
        apply div_pos <;> linarith) hlam1
      have h1 := (hbnd m k).2
      have : lam ^ m * E < y (k * L) - hi := by
        rw [lt_div_iff₀ (by linarith)] at hm
        nlinarith [pow_nonneg hlam0 m]
      linarith
  -- every point lies in `[0, 1)`
  have hy01 : ∀ n, 0 ≤ y n ∧ y n < 1 := by
    intro n
    obtain ⟨k, i, hi, rfl⟩ : ∃ k i, i < L ∧ n = k * L + i :=
      ⟨n / L, n % L, Nat.mod_lt _ hL, by rw [Nat.div_add_mod']⟩
    obtain ⟨h1, h2⟩ := hK (k + 1)
    rw [show (k + 1) * L = k * L + L by ring] at h1 h2
    have := hblock k 0 (by simpa using h1) (by simpa using h2) i hi.le
    simp only [mul_zero, sub_zero, add_zero] at this
    have hi' : i < (hblk H.w₁ H.w₂ k).length := by rw [hbl k]; exact hi
    have g0 := (Rat.cast_le (K := ℝ)).2 ((hW k).img0 i hi')
    have g1 := (Rat.cast_lt (K := ℝ)).2 ((hW k).img1 i hi')
    rw [cast_back] at g0 g1
    push_cast at g0 g1
    exact ⟨g0.trans this.1, this.2.trans_lt g1⟩
  -- the carry identity
  have hident : ∀ n, (s n : ℝ) * P.b =
      P.p * P.b * y n - P.q * P.b * y (n + 1) - ((P.p : ℝ) - P.q) * P.a := by
    intro n
    have e := hrec n
    simp only [hb] at e
    rw [eq_div_iff hp0.ne'] at e
    field_simp at e
    linear_combination -e
  -- residues
  have hM0 : (0 : ℤ) < P.M := by exact_mod_cast hF.M0
  set r₀ : ℕ := (H.R % P.M).toNat with hr₀
  have hr₀c : (r₀ : ℤ) = H.R % P.M := Int.toNat_of_nonneg (Int.emod_nonneg _ hM0.ne')
  have hr₀M : r₀ < P.M := by
    have := Int.emod_lt_of_pos H.R hM0
    omega
  set r := rs P r₀ s with hr
  have hrlt : ∀ n, r n < P.M := by
    intro n; cases n with
    | zero => exact hr₀M
    | succ n => exact rnext_lt hF _ _
  have hrav : ∀ n, ∀ l ∈ P.PM, r n % l ≠ 0 :=
    rs_av_of_blocks hF hL hlen hPM hPMw (fun k l hl => by have h := (hW k).ret l hl; rw [hbl k] at h; exact h)
      (fun k l hl i hi => (hW k).av l hl i (by rw [hbl k]; exact hi))
  have hpo : PseudoOrbit P r y s := by
    refine ⟨hrlt, fun n => (hy01 n).1, fun n => (hy01 n).2, hident, fun n => rfl, hrav, ?_⟩
    intro n l hl
    have hlH := hPq l hl
    rcases hseq_mem hL hlen n with hm | hm
    · exact (wordFacts hw₁).sav l hlH _ hm
    · exact (wordFacts hw₂).sav l hlH _ hm
  exact hseq_not_periodic hL hlen hne (PseudoOrbit.eventuallyPeriodic hc hpo)

/-- A whole row of horseshoe witnesses at once (one `decide`). -/
theorem not_checked_of_horseRow {p q : ℕ} {a : ℤ} {b : ℕ} {ws : List HorseWitness}
    (h : ws.all (horseOK p q a b) = true) :
    ∀ w ∈ ws, ∀ (P : Params) (C : Cert), P.p = p → P.q = q → P.a = a → P.b = b →
      (∀ l ∈ P.PM, l ∈ w.PM) → (∀ l ∈ P.Pq, l ∈ w.Pq) → ¬ Checked P C := by
  intro w hw P C hp hq ha hb hPM hPq
  subst hp hq ha hb
  exact not_checked_of_horseOK w (List.all_eq_true.1 h w hw) hPM hPq

end DubC2.Gen
