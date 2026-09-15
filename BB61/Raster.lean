/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.Covering
import BB61.Confinement
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# M2 Proposition 9: the X8 raster criterion is sound, and complete on Route A's range

Formal companion of `note-1061-M2.html` (milestone M2 of `plans/plan-1061.html`), §7, and of
`note-1061-M0.html` §6, which built the procedure.

M0's **X8 procedure** decides, per `α`, whether the confinement set `X(α) = (C(α) - K) mod 1`
misses an interval: over-approximate `C(α)` and `K` by their depth-`(M, M')` point sets fattened
by the tail bounds, rasterise the difference on `G` bins, dilate, and search for a run of empty
bins.  A reported run is a genuine gap, hence a proof of 10.61 at `α`.  Proposition 9 is the
*converse*: on Route A's range the procedure is guaranteed to find one, at a resolution that can
be named in advance —

`T := T(M, M') < 1/3` and `G ≥ 2^{M+M'+3}/(1 - 3T)`.

## What is formalised, and in what order

The note's proof is an accounting of lengths, and the accounting is what this file makes
precise.  The raster is modelled exactly: `bin G i = [i/G, (i+1)/G)`, so the bins are the
fibres of `binIdx G x = ⌊x·G⌋` and are automatically a partition of `ℝ`.

* `subset_occSet`, `occSet_dist` — the two halves of what a raster does to a set.  It only ever
  *grows* it (`S ⊆ occSet G S`, so nothing is lost), and it grows it by less than one bin
  (`x ∈ occSet G S → ∃ y ∈ S, |x - y| < 1/G`).  Everything below is these two facts and
  arithmetic.
* `runSet_inter_occSet_eq_empty` — **soundness**, M0's direction: a run of empty bins is an
  interval that misses the rasterised set, hence misses everything that set covers.
* `exists_zeroRun` — **completeness at a given resolution**: an interval of length `b - a`
  missing the occupied set contains a run of `ℓ ≥ (b-a)·G - 2` empty bins.  The `2` is the
  alignment loss, one bin at each end, and it is the only loss: no hypothesis on `a`, `b`, `G`.
* `inter_occSet_eq_empty_of_shrink` — the slack: if the implementation's set over-approximates
  the theoretical covering by `e`, a gap in the covering survives as a gap in the occupied set
  after shrinking by `e + 1/G` at each end.
* `exists_certified_gap` — the three composed, with no hypothesis on the numbers at all: this
  is the whole of the note's proof except the choice of `G`.
* `gap_pos_of_resolution` — the choice of `G`, i.e. the note's arithmetic
  `(1-3T)2^{-W} - 6/G > 0` for `G ≥ 2^{W+3}/(1-3T)`, which is `2^3 > 6`.
* `prop9` — **Proposition 9**.  Under `T < 1/3` and the stated `G` the procedure returns a run
  of `ℓ ≥ 1` empty bins whose length is at least *half* the note's guaranteed gap.

**The note's constant is generous.**  The note allows `O(1)` bins, "`≤ 3/G` on each side of each
arc", so `6/G` in total.  The accounting above spends `1/G` per side for the rasterisation and
one bin per side for the alignment, so `4/G` suffices and the surviving run is at least
`(1-3T)2^{-W}/2` rather than `/4`.  Both are recorded: `gap_pos_of_resolution` proves the note's
`6/G` form as well, so the displayed choice of `G` is verified as written.

## The engine

§5 instantiates all of this on the quadratic engine of `BB61/Covering.lean`.  `covSet M M' K`
is the set the procedure rasterises — the candidate points fattened by `delta M M'` — and
`orbitFract_mem_covSet` is `exists_cand_near`: it really does contain every `{ξ αⁿ}`.

* `X8Cert` — the certificate: a run of `ℓ ≥ 1` empty bins lying inside `[0, 1]`;
* `not_equidistributed_of_X8Cert` — **soundness of the criterion**: a certificate proves 10.61
  at `α`.  This is the step that makes X8 a proof method and not a heuristic;
* `exists_gap_in_covSet` — the Route A engine's own gap, stated against the covering rather than
  against the orbit (`BB61/Covering.lean`'s `exists_avoided_interval` throws that away, and the
  procedure needs it, since what it rasterises is the covering);
* `exists_X8Cert_of_cert` — **Route A ⊆ X8**: wherever the covering certificate of
  `BB61/Covering.lean` holds, the raster procedure reports a gap.  With `BB61/Criterion.lean`
  this covers every `α` with `A(α) < 1`, which is the containment half of the note's
  `Route A ⊊ X8`.

The *strict* half — an `α` where X8 fires and Route A does not — is `BB61/GapSqrtThree.lean`.

## What is taken as a hypothesis, and why

`prop9` takes the true gap `Ioo a b` and its length `(1-T)2^{-W}` as hypotheses, exactly as the
note's proof does ("By Theorem 2(ii) there is a true gap `J` with `|J| ≥ (1-T)2^{-W}`").
Theorem 2(i) is `BB61/RouteADepth.lean`; the *quantitative* form of 2(ii) — that `N` closed arcs
of total length `T < 1` leave an open arc of length `≥ (1-T)/N` — is a statement about the
interval structure of the complement and is not formalised here.  Its qualitative form is, and
suffices for the containment: `exists_gap_in_covSet` produces a gap with no length bound and
`exists_X8Cert_of_cert` then chooses `G` to fit it.  What is lost is only that `G` is chosen
*after* seeing the gap rather than in advance — which is precisely the distance the note's
closing paragraph measures, `2^{42}` guaranteed against `2^{21}` observed.

## References

* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, CUP 2012,
  Problem 10.61.
-/

noncomputable section

namespace BB61

open Set MeasureTheory

/-! ## 1. The raster

`G` bins per unit interval.  Bin `i` is `[i/G, (i+1)/G)`, and the bins are the fibres of
`binIdx`, so that they partition `ℝ` costs nothing. -/

namespace Raster

variable {G : ℕ}

/-- The index of the bin containing `x` in the `G`-bin raster. -/
def binIdx (G : ℕ) (x : ℝ) : ℤ := ⌊x * G⌋

/-- The `i`-th bin of the `G`-bin raster: `[i/G, (i+1)/G)`. -/
def bin (G : ℕ) (i : ℤ) : Set ℝ := Set.Ico ((i : ℝ) / G) (((i : ℝ) + 1) / G)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem mem_bin_iff (hG : 0 < G) (i : ℤ) (x : ℝ) : x ∈ bin G i ↔ binIdx G x = i := by
  have hG0 : (0 : ℝ) < G := by exact_mod_cast hG
  rw [binIdx, Int.floor_eq_iff, bin, Set.mem_Ico, div_le_iff₀ hG0, lt_div_iff₀ hG0]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem mem_bin_binIdx (hG : 0 < G) (x : ℝ) : x ∈ bin G (binIdx G x) :=
  (mem_bin_iff hG _ x).mpr rfl

/-! ## 2. The occupied set

The procedure marks a bin when the set it rasterises meets it.  Two facts are used, and only
two: the marked set contains the original — nothing is lost — and it exceeds it by less than one
bin — nothing much is gained. -/

/-- Bin `i` is occupied by `S` when some point of `S` falls in it. -/
def Occupied (G : ℕ) (S : Set ℝ) (i : ℤ) : Prop := ∃ y ∈ S, binIdx G y = i

/-- The occupied set: the union of the bins that `S` meets. -/
def occSet (G : ℕ) (S : Set ℝ) : Set ℝ := {x | Occupied G S (binIdx G x)}

/-- **The raster never loses a point.**  This is what makes a reported gap a true gap. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem subset_occSet (G : ℕ) (S : Set ℝ) : S ⊆ occSet G S := fun x hx => ⟨x, hx, rfl⟩

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem occSet_mono (G : ℕ) {S T : Set ℝ} (h : S ⊆ T) : occSet G S ⊆ occSet G T := by
  rintro x ⟨y, hy, hyx⟩; exact ⟨y, h hy, hyx⟩

/-- **The raster gains less than one bin.**  This is what makes a true gap survive
rasterisation. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem occSet_dist (hG : 0 < G) {S : Set ℝ} {x : ℝ} (hx : x ∈ occSet G S) :
    ∃ y ∈ S, |x - y| < 1 / G := by
  obtain ⟨y, hyS, hy⟩ := hx
  refine ⟨y, hyS, ?_⟩
  have hG0 : (0 : ℝ) < G := by exact_mod_cast hG
  have hxb : x ∈ bin G (binIdx G x) := mem_bin_binIdx hG x
  have hyb : y ∈ bin G (binIdx G x) := by rw [mem_bin_iff hG]; exact hy
  rw [bin, Set.mem_Ico] at hxb hyb
  have h1 : ((binIdx G x : ℝ) + 1) / G - (binIdx G x : ℝ) / G = 1 / G := by
    field_simp; ring
  rw [abs_lt]
  constructor <;> linarith [hxb.1, hxb.2, hyb.1, hyb.2]

/-! ## 3. Runs of empty bins

A *zero run* is a block of consecutive unoccupied bins.  It is what the procedure reports;
`runSet` is the interval it stands for. -/

/-- `ZeroRun G S i ℓ`: the `ℓ` bins `i, …, i+ℓ-1` are all unoccupied by `S`. -/
def ZeroRun (G : ℕ) (S : Set ℝ) (i : ℤ) (ℓ : ℕ) : Prop :=
  ∀ j : ℤ, i ≤ j → j < i + ℓ → ¬ Occupied G S j

/-- The interval covered by the run of `ℓ` bins starting at `i`. -/
def runSet (G : ℕ) (i : ℤ) (ℓ : ℕ) : Set ℝ := Set.Ico ((i : ℝ) / G) (((i : ℝ) + ℓ) / G)

/-- **Soundness of the procedure** (M0's direction): the interval of a zero run misses the
occupied set, hence misses everything the rasterised set covers. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem runSet_inter_occSet_eq_empty (hG : 0 < G) {S : Set ℝ} {i : ℤ} {ℓ : ℕ}
    (h : ZeroRun G S i ℓ) : runSet G i ℓ ∩ occSet G S = ∅ := by
  have hG0 : (0 : ℝ) < G := by exact_mod_cast hG
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hxr, hxo⟩
  rw [runSet, Set.mem_Ico, div_le_iff₀ hG0, lt_div_iff₀ hG0] at hxr
  refine h (binIdx G x) (Int.le_floor.mpr hxr.1) ?_ hxo
  exact_mod_cast lt_of_le_of_lt (Int.floor_le (x * G)) hxr.2

/-- **Completeness at a given resolution.**  An interval of length `b - a` that misses the
occupied set contains a run of at least `(b-a)·G - 2` empty bins, and the run's interval sits
inside it.  The `2` is the alignment loss — one bin at each end — and there is no other loss and
no hypothesis. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_zeroRun (hG : 0 < G) {S : Set ℝ} {a b : ℝ}
    (h : Set.Ioo a b ∩ occSet G S = ∅) :
    ∃ (i : ℤ) (ℓ : ℕ), (b - a) * G - 2 ≤ (ℓ : ℝ) ∧
      Set.Ioo ((i : ℝ) / G) (((i : ℝ) + ℓ) / G) ⊆ Set.Ioo a b ∧ ZeroRun G S i ℓ := by
  have hG0 : (0 : ℝ) < G := by exact_mod_cast hG
  set i : ℤ := ⌊a * G⌋ + 1 with hidef
  set k : ℤ := ⌈b * G⌉ - 1 with hkdef
  have hai : a * G < (i : ℝ) := by
    rw [hidef]; push_cast; linarith [Int.lt_floor_add_one (a * G)]
  have hkb : (k : ℝ) < b * G := by
    rw [hkdef]; push_cast; linarith [Int.ceil_lt_add_one (b * G)]
  have hi_le : (i : ℝ) ≤ a * G + 1 := by
    rw [hidef]; push_cast; linarith [Int.floor_le (a * G)]
  have hk_ge : b * G - 1 ≤ (k : ℝ) := by
    rw [hkdef]; push_cast; linarith [Int.le_ceil (b * G)]
  have halow : a < (i : ℝ) / G := (lt_div_iff₀ hG0).mpr hai
  have hbhigh : (k : ℝ) / G < b := (div_lt_iff₀ hG0).mpr hkb
  -- every bin of the run lies strictly inside `(a, b)`, hence is empty
  have hbins : ∀ ℓ : ℕ, ((ℓ : ℤ) ≤ k - i) → ZeroRun G S i ℓ := by
    intro ℓ hℓ j hji hjk hocc
    obtain ⟨y, hyS, hyj⟩ := hocc
    have hyb : y ∈ bin G j := by rw [mem_bin_iff hG]; exact hyj
    rw [bin, Set.mem_Ico, div_le_iff₀ hG0, lt_div_iff₀ hG0] at hyb
    have hjR : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hji
    have hj1 : (j : ℝ) + 1 ≤ (k : ℝ) := by
      have hz : (j : ℤ) + 1 ≤ k := by omega
      exact_mod_cast hz
    have hya : a * G < y * G := lt_of_lt_of_le hai (le_trans hjR hyb.1)
    have hyb2 : y * G < b * G := lt_of_lt_of_le hyb.2 (le_of_lt (lt_of_le_of_lt hj1 hkb))
    have hmem : y ∈ Set.Ioo a b :=
      ⟨lt_of_mul_lt_mul_right hya hG0.le, lt_of_mul_lt_mul_right hyb2 hG0.le⟩
    have hcontra : y ∈ Set.Ioo a b ∩ occSet G S := ⟨hmem, subset_occSet G S hyS⟩
    rw [h] at hcontra; exact hcontra
  rcases le_or_gt i k with hik | hik
  · have hc : (((k - i).toNat : ℕ) : ℝ) = (k : ℝ) - (i : ℝ) := by
      have h1 : ((k - i).toNat : ℤ) = k - i := Int.toNat_of_nonneg (by omega)
      calc (((k - i).toNat : ℕ) : ℝ) = ((((k - i).toNat : ℕ) : ℤ) : ℝ) := by push_cast; ring
      _ = ((k - i : ℤ) : ℝ) := by rw [h1]
      _ = (k : ℝ) - (i : ℝ) := by push_cast; ring
    refine ⟨i, (k - i).toNat, ?_, ?_, hbins _ (by omega)⟩
    · rw [hc]; linarith
    · rw [hc, show (i : ℝ) + ((k : ℝ) - (i : ℝ)) = (k : ℝ) by ring]
      exact Set.Ioo_subset_Ioo halow.le hbhigh.le
  · refine ⟨i, 0, ?_, ?_, ?_⟩
    · have hki : (k : ℝ) ≤ (i : ℝ) - 1 := by
        have hz : k ≤ i - 1 := by omega
        have : ((k : ℤ) : ℝ) ≤ ((i - 1 : ℤ) : ℝ) := by exact_mod_cast hz
        push_cast at this; linarith
      push_cast; nlinarith
    · simp
    · intro j hji hjk _; exact absurd hjk (by push_cast; omega)

/-! ## 4. Proposition 9

The implementation's set `Imp` over-approximates the theoretical covering `Cov` by `e`; the
covering contains the set `X` one cares about; a gap in `Cov` survives rasterisation shrunk by
`e + 1/G` at each end, and the alignment costs two more bins. -/

/-- The slack.  A gap in the covering survives as a gap in the occupied set, shrunk by
`e + 1/G` at each end. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem inter_occSet_eq_empty_of_shrink (hG : 0 < G) {Imp Cov : Set ℝ} {e : ℝ}
    (hIC : ∀ x ∈ Imp, ∃ y ∈ Cov, |x - y| ≤ e) {a b : ℝ}
    (h : Set.Ioo a b ∩ Cov = ∅) :
    Set.Ioo (a + (e + 1 / G)) (b - (e + 1 / G)) ∩ occSet G Imp = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hx, hxo⟩
  obtain ⟨z, hzI, hz⟩ := occSet_dist hG hxo
  obtain ⟨y, hyC, hy⟩ := hIC z hzI
  rw [abs_lt] at hz
  rw [abs_le] at hy
  have hcontra : y ∈ Set.Ioo a b ∩ Cov :=
    ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, hyC⟩
  rw [h] at hcontra; exact hcontra

/-- **Proposition 9, the length accounting.**  With no hypothesis on the numbers: a gap
`Ioo a b` in the covering yields a zero run of `(b - a - 2e)·G - 4` bins whose interval sits
inside the gap and misses `X`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_certified_gap (hG : 0 < G) {X Cov Imp : Set ℝ} {e : ℝ} (he : 0 ≤ e)
    (hXC : X ⊆ Cov) (hCI : Cov ⊆ Imp) (hIC : ∀ x ∈ Imp, ∃ y ∈ Cov, |x - y| ≤ e)
    {a b : ℝ} (hdisj : Set.Ioo a b ∩ Cov = ∅) :
    ∃ (i : ℤ) (ℓ : ℕ), (b - a - 2 * e) * G - 4 ≤ (ℓ : ℝ) ∧
      Set.Ioo ((i : ℝ) / G) (((i : ℝ) + ℓ) / G) ⊆ Set.Ioo a b ∧
      ZeroRun G Imp i ℓ ∧ runSet G i ℓ ∩ X = ∅ := by
  have hG0 : (0 : ℝ) < G := by exact_mod_cast hG
  have hGne : (G : ℝ) ≠ 0 := ne_of_gt hG0
  have hinv : (0 : ℝ) < 1 / G := by positivity
  obtain ⟨i, ℓ, hlen, hsub, hzero⟩ :=
    exists_zeroRun hG (inter_occSet_eq_empty_of_shrink hG hIC hdisj)
  refine ⟨i, ℓ, ?_, ?_, hzero, ?_⟩
  · have hexp : ((b - (e + 1 / (G : ℝ))) - (a + (e + 1 / (G : ℝ)))) * G - 2
        = (b - a - 2 * e) * G - 4 := by field_simp; ring
    linarith [hexp ▸ hlen]
  · exact hsub.trans (Set.Ioo_subset_Ioo (by linarith) (by linarith))
  · have hXo : X ⊆ occSet G Imp := hXC.trans (hCI.trans (subset_occSet G Imp))
    have hemp := runSet_inter_occSet_eq_empty hG hzero
    rw [Set.eq_empty_iff_forall_notMem] at hemp ⊢
    exact fun x hx => hemp x ⟨hx.1, hXo hx.2⟩

/-- The note's choice of resolution, and its arithmetic.  `G ≥ 2^{W+3}/(1-3T)` makes both the
note's own bound `(1-3T)2^{-W} - 6/G` and the sharper `- 4/G` of `exists_certified_gap`
positive; the first because `2^3 > 6`, the second with room to spare. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem gap_pos_of_resolution {Tn Gr : ℝ} {W : ℕ} (hT : 3 * Tn < 1)
    (hGr : (2 : ℝ) ^ (W + 3) / (1 - 3 * Tn) ≤ Gr) :
    0 < Gr ∧ (1 - 3 * Tn) / 2 ^ W / 2 ≤ (1 - 3 * Tn) / 2 ^ W - 4 / Gr ∧
      (1 - 3 * Tn) / 2 ^ W / 4 ≤ (1 - 3 * Tn) / 2 ^ W - 6 / Gr := by
  have hpos : (0 : ℝ) < 1 - 3 * Tn := by linarith
  have hW : (0 : ℝ) < 2 ^ W := by positivity
  have hpow : (2 : ℝ) ^ (W + 3) = 2 ^ W * 8 := by rw [pow_add]; norm_num
  rw [hpow] at hGr
  have hbase : (0 : ℝ) < 2 ^ W * 8 / (1 - 3 * Tn) := by positivity
  have hG0 : 0 < Gr := lt_of_lt_of_le hbase hGr
  have hmul : (2 : ℝ) ^ W * 8 ≤ Gr * (1 - 3 * Tn) := (div_le_iff₀ hpos).mp hGr
  have key : ∀ c : ℝ, 0 ≤ c → c / Gr ≤ c * (1 - 3 * Tn) / (2 ^ W * 8) := by
    intro c hc
    rw [div_le_div_iff₀ hG0 (by positivity)]
    nlinarith
  refine ⟨hG0, ?_, ?_⟩
  · have h4 := key 4 (by norm_num)
    have e4 : (4 : ℝ) * (1 - 3 * Tn) / (2 ^ W * 8) = (1 - 3 * Tn) / 2 ^ W / 2 := by
      field_simp; ring
    rw [e4] at h4; linarith
  · have h6 := key 6 (by norm_num)
    have e6 : (6 : ℝ) * (1 - 3 * Tn) / (2 ^ W * 8) = (1 - 3 * Tn) / 2 ^ W * (3 / 4) := by
      field_simp; ring
    rw [e6] at h6
    have e7 : (1 - 3 * Tn) / 2 ^ W / 4
        = (1 - 3 * Tn) / 2 ^ W - (1 - 3 * Tn) / 2 ^ W * (3 / 4) := by ring
    rw [e7]; linarith

/-- **Proposition 9.**  Let `T := T(M,M') < 1/3` and `W := M + M'`.  Suppose the covering `Cov`
contains `X`, the procedure's set `Imp` contains `Cov` and over-approximates it by at most
`T·2^{-W}`, and `Cov` misses an interval of length `≥ (1-T)2^{-W}` — the gap of Theorem 2(ii).
Then at any resolution `G ≥ 2^{W+3}/(1-3T)` the procedure reports a **nonempty** run of empty
bins, of length at least *half* the guaranteed gap, whose interval misses `X`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem prop9 {G : ℕ} (hG : 0 < G) {X Cov Imp : Set ℝ} {W : ℕ} {Tn : ℝ}
    (hT0 : 0 ≤ Tn) (hT : 3 * Tn < 1) (hXC : X ⊆ Cov) (hCI : Cov ⊆ Imp)
    (hIC : ∀ x ∈ Imp, ∃ y ∈ Cov, |x - y| ≤ Tn / 2 ^ W)
    {a b : ℝ} (hlen : (1 - Tn) / 2 ^ W ≤ b - a) (hdisj : Set.Ioo a b ∩ Cov = ∅)
    (hres : (2 : ℝ) ^ (W + 3) / (1 - 3 * Tn) ≤ (G : ℝ)) :
    ∃ (i : ℤ) (ℓ : ℕ), 0 < ℓ ∧ (1 - 3 * Tn) / 2 ^ W / 2 ≤ (ℓ : ℝ) / G ∧
      Set.Ioo ((i : ℝ) / G) (((i : ℝ) + ℓ) / G) ⊆ Set.Ioo a b ∧
      ZeroRun G Imp i ℓ ∧ runSet G i ℓ ∩ X = ∅ := by
  have hG0 : (0 : ℝ) < G := by exact_mod_cast hG
  have hW : (0 : ℝ) < 2 ^ W := by positivity
  obtain ⟨_, h4, _⟩ := gap_pos_of_resolution (W := W) hT hres
  obtain ⟨i, ℓ, hℓlen, hsub, hzero, hmiss⟩ :=
    exists_certified_gap hG (by positivity) hXC hCI hIC hdisj
  have hgapge : (1 - 3 * Tn) / 2 ^ W ≤ b - a - 2 * (Tn / 2 ^ W) := by
    have hid : (1 - Tn) / 2 ^ W - 2 * (Tn / 2 ^ W) = (1 - 3 * Tn) / 2 ^ W := by
      field_simp; ring
    linarith
  have h1 : ((1 - 3 * Tn) / 2 ^ W) * G - 4 ≤ (ℓ : ℝ) := by
    have hm := mul_le_mul_of_nonneg_right hgapge hG0.le
    linarith
  have hstep : (1 - 3 * Tn) / 2 ^ W - 4 / (G : ℝ) ≤ (ℓ : ℝ) / G := by
    rw [le_div_iff₀ hG0]
    have hid : ((1 - 3 * Tn) / 2 ^ W - 4 / (G : ℝ)) * G = ((1 - 3 * Tn) / 2 ^ W) * G - 4 := by
      field_simp
    rw [hid]; exact h1
  have hbound := h4.trans hstep
  have hposq : (0 : ℝ) < (ℓ : ℝ) / G := by
    have : (0 : ℝ) < (1 - 3 * Tn) / 2 ^ W / 2 := by
      have : (0 : ℝ) < 1 - 3 * Tn := by linarith
      positivity
    linarith
  have hℓpos : 0 < ℓ := by
    by_contra hc
    have : ℓ = 0 := by omega
    rw [this] at hposq; simp at hposq
  exact ⟨i, ℓ, hℓpos, hbound, hsub, hzero, hmiss⟩

end Raster

/-! ## 5. The X8 criterion on the quadratic engine

The accounting above, applied to the covering of `BB61/Covering.lean`. -/

namespace QuadSetup

open Raster

variable (P : QuadSetup)

/-- **The set the X8 procedure rasterises**: the depth-`(M, M')` candidate points fattened by
the truncation error `delta M M'`. -/
noncomputable def covSet (M M' K : ℕ) : Set ℝ :=
  ⋃ f ∈ P.cands M M' K, Set.Icc (f - P.delta M M') (f + P.delta M M')

/-- The covering really covers: every `{ξ αⁿ}` lies in `covSet`.  This is `exists_cand_near`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem orbitFract_mem_covSet (M M' K : ℕ)
    (hK : (1 + |P.β|) / (1 - |P.β|) + 1 ≤ (K : ℝ)) (ε : ℕ → Bool) (n : ℕ) :
    Int.fract (piVal P.α ε * P.α ^ n) ∈ P.covSet M M' K := by
  obtain ⟨f, hf, hnear⟩ := P.exists_cand_near M M' K hK ε n
  have habs := abs_le.mp hnear
  exact Set.mem_biUnion hf (Set.mem_Icc.mpr ⟨by linarith [habs.1], by linarith [habs.2]⟩)

/-- The set of orbit fractional parts. -/
noncomputable def orbitFractSet : Set ℝ :=
  {y | ∃ (ε : ℕ → Bool) (n : ℕ), y = Int.fract (piVal P.α ε * P.α ^ n)}

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem orbitFractSet_subset_covSet (M M' K : ℕ)
    (hK : (1 + |P.β|) / (1 - |P.β|) + 1 ≤ (K : ℝ)) :
    P.orbitFractSet ⊆ P.covSet M M' K := by
  rintro _ ⟨ε, n, rfl⟩; exact P.orbitFract_mem_covSet M M' K hK ε n

/-- **The X8 certificate at `α`**: at depths `(M, M')`, integer-part bound `K` and resolution
`G`, the raster reports a run of `ℓ ≥ 1` empty bins lying inside `[0, 1]`. -/
def X8Cert (M M' K G : ℕ) (i : ℤ) (ℓ : ℕ) : Prop :=
  0 < ℓ ∧ 0 ≤ i ∧ i + (ℓ : ℤ) ≤ (G : ℤ) ∧ ZeroRun G (P.covSet M M' K) i ℓ

/-- **Soundness of the X8 criterion.**  A certificate exhibits one open interval, uniform in
`ξ ∈ C(α)` and in `n`, that every orbit misses at every time. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem avoided_interval_of_X8Cert {M M' K G : ℕ} {i : ℤ} {ℓ : ℕ} (hG : 0 < G)
    (hK : (1 + |P.β|) / (1 - |P.β|) + 1 ≤ (K : ℝ)) (hc : P.X8Cert M M' K G i ℓ) :
    ∃ x r : ℝ, 0 < r ∧ Set.Ioo (x - r) (x + r) ⊆ Set.Ioo 0 1 ∧
      ∀ (ε : ℕ → Bool) (n : ℕ),
        Int.fract (piVal P.α ε * P.α ^ n) ∉ Set.Ioo (x - r) (x + r) := by
  obtain ⟨hℓ, hi0, hiG, hzero⟩ := hc
  have hG0 : (0 : ℝ) < G := by exact_mod_cast hG
  have hi0R : (0 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi0
  have hiGR : (i : ℝ) + (ℓ : ℝ) ≤ (G : ℝ) := by exact_mod_cast hiG
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  have h1 : ((i : ℝ) + (ℓ : ℝ) / 2) / G - (ℓ : ℝ) / 2 / G = (i : ℝ) / G := by ring
  have h2 : ((i : ℝ) + (ℓ : ℝ) / 2) / G + (ℓ : ℝ) / 2 / G = ((i : ℝ) + ℓ) / G := by ring
  refine ⟨((i : ℝ) + (ℓ : ℝ) / 2) / G, (ℓ : ℝ) / 2 / G, by positivity, ?_, ?_⟩
  · rw [h1, h2]
    exact Set.Ioo_subset_Ioo (div_nonneg hi0R hG0.le) ((div_le_one hG0).mpr hiGR)
  · intro ε n hy
    rw [h1, h2] at hy
    have hin : Int.fract (piVal P.α ε * P.α ^ n) ∈ runSet G i ℓ := Set.Ioo_subset_Ico_self hy
    have hocc : Int.fract (piVal P.α ε * P.α ^ n) ∈ occSet G (P.covSet M M' K) :=
      subset_occSet _ _ (P.orbitFract_mem_covSet M M' K hK ε n)
    have hemp := runSet_inter_occSet_eq_empty hG hzero
    rw [Set.eq_empty_iff_forall_notMem] at hemp
    exact hemp _ ⟨hin, hocc⟩

/-- **Problem 10.61 from an X8 certificate.**  This is what makes the raster sweep a proof
method: the certificate is a finite, decidable object, and it settles `α`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem not_equidistributed_of_X8Cert {M M' K G : ℕ} {i : ℤ} {ℓ : ℕ} (hG : 0 < G)
    (hK : (1 + |P.β|) / (1 - |P.β|) + 1 ≤ (K : ℝ)) (hc : P.X8Cert M M' K G i ℓ) :
    ∀ ξ ∈ cantorSet P.α, ¬ IsEquidistributedModuloOne fun n : ℕ => ξ * P.α ^ n := by
  obtain ⟨x, r, hr, hsub, havoid⟩ := P.avoided_interval_of_X8Cert hG hK hc
  rintro ξ ⟨ε, rfl⟩
  exact not_equidistributed_of_avoided hr hsub (havoid ε)

/-! ### Route A ⊆ X8 -/

/-- The Route A engine's gap, stated against the **covering** rather than against the orbit.
`BB61/Covering.lean`'s `exists_avoided_interval` proves this and then forgets it; the raster
procedure needs it, since what it rasterises is the covering. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_gap_in_covSet (M M' K : ℕ)
    (hcert : ((2 ^ M * 2 ^ M' * (2 * K + 1) : ℕ) : ℝ) * (2 * P.delta M M') < 1) :
    ∃ x r : ℝ, 0 < r ∧ Set.Ioo (x - r) (x + r) ⊆ Set.Ioo 0 1 ∧
      Set.Ioo (x - r) (x + r) ∩ P.covSet M M' K = ∅ := by
  have hδ0 := P.delta_nonneg M M'
  have hUclosed : IsClosed (P.covSet M M' K) :=
    Set.Finite.isClosed_biUnion (Finset.finite_toSet _) fun f _ => isClosed_Icc
  have hUvol : volume (P.covSet M M' K)
      ≤ ENNReal.ofReal (((2 ^ M * 2 ^ M' * (2 * K + 1) : ℕ) : ℝ) * (2 * P.delta M M')) := by
    calc volume (P.covSet M M' K)
        ≤ ∑ f ∈ P.cands M M' K,
            volume (Set.Icc (f - P.delta M M') (f + P.delta M M')) :=
          measure_biUnion_finset_le _ _
    _ = ∑ _f ∈ P.cands M M' K, ENNReal.ofReal (2 * P.delta M M') := by
          refine Finset.sum_congr rfl fun f _ => ?_
          rw [Real.volume_Icc]; congr 1; ring
    _ = ((P.cands M M' K).card : ENNReal) * ENNReal.ofReal (2 * P.delta M M') := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2 ^ M * 2 ^ M' * (2 * K + 1) : ℕ) : ENNReal)
          * ENNReal.ofReal (2 * P.delta M M') := by
          gcongr; exact_mod_cast P.card_cands_le M M' K
    _ = ENNReal.ofReal (((2 ^ M * 2 ^ M' * (2 * K + 1) : ℕ) : ℝ)
          * (2 * P.delta M M')) := by
          rw [ENNReal.ofReal_mul
              (show (0 : ℝ) ≤ ((2 ^ M * 2 ^ M' * (2 * K + 1) : ℕ) : ℝ) by positivity),
            ENNReal.ofReal_natCast]
  have hnotsub : ¬ Set.Ioo (0 : ℝ) 1 ⊆ P.covSet M M' K := by
    intro hsub
    have h1 : (1 : ENNReal) ≤ volume (P.covSet M M' K) := by
      calc (1 : ENNReal) = volume (Set.Ioo (0 : ℝ) 1) := by rw [Real.volume_Ioo]; norm_num
      _ ≤ _ := measure_mono hsub
    have h2 : volume (P.covSet M M' K) < 1 := by
      refine lt_of_le_of_lt hUvol ?_
      rw [show (1 : ENNReal) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
      exact (ENNReal.ofReal_lt_ofReal_iff one_pos).mpr hcert
    exact absurd h1 (not_le.mpr h2)
  obtain ⟨x₀, hx₀Ioo, hx₀U⟩ : ∃ x₀, x₀ ∈ Set.Ioo (0 : ℝ) 1 ∧ x₀ ∉ P.covSet M M' K := by
    by_contra hcon
    push Not at hcon
    exact hnotsub fun y hy => hcon y hy
  have hopen : IsOpen (Set.Ioo (0 : ℝ) 1 ∩ (P.covSet M M' K)ᶜ) :=
    isOpen_Ioo.inter hUclosed.isOpen_compl
  obtain ⟨r, hr0, hball⟩ := Metric.isOpen_iff.mp hopen x₀ ⟨hx₀Ioo, hx₀U⟩
  refine ⟨x₀, r, hr0, fun y hy => ?_, ?_⟩
  · exact (hball (by rw [Real.ball_eq_Ioo]; exact hy)).1
  · rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨hy, hyU⟩
    exact (hball (by rw [Real.ball_eq_Ioo]; exact hy)).2 hyU

/-- **Route A ⊆ X8.**  Wherever the covering certificate of `BB61/Covering.lean` holds — hence,
by `BB61/Criterion.lean`, at every `α` with `A(α) < 1` — the raster procedure reports a gap, at
an explicit resolution. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_X8Cert_of_cert (M M' K : ℕ)
    (hcert : ((2 ^ M * 2 ^ M' * (2 * K + 1) : ℕ) : ℝ) * (2 * P.delta M M') < 1) :
    ∃ (G : ℕ) (i : ℤ) (ℓ : ℕ), 0 < G ∧ P.X8Cert M M' K G i ℓ := by
  obtain ⟨x, r, hr, hsub, hdisj⟩ := P.exists_gap_in_covSet M M' K hcert
  obtain ⟨G, hG⟩ : ∃ G : ℕ, (4 : ℝ) / r < (G : ℝ) := exists_nat_gt (4 / r)
  have hG0R : (0 : ℝ) < G := lt_trans (by positivity) hG
  have hG0 : 0 < G := by exact_mod_cast hG0R
  have hinv : (0 : ℝ) < 1 / (G : ℝ) := by positivity
  have hzero : Set.Ioo (x - r + (0 + 1 / (G : ℝ))) (x + r - (0 + 1 / (G : ℝ)))
      ∩ occSet G (P.covSet M M' K) = ∅ :=
    inter_occSet_eq_empty_of_shrink hG0 (e := 0) (fun y hy => ⟨y, hy, by simp⟩) hdisj
  obtain ⟨i, ℓ, hlen, hrsub, hzr⟩ := exists_zeroRun hG0 hzero
  have hrG : (4 : ℝ) < r * G := by rw [mul_comm]; exact (div_lt_iff₀ hr).mp hG
  have hlenR : (0 : ℝ) < (ℓ : ℝ) := by
    have hexp : (x + r - (0 + 1 / (G : ℝ))) - (x - r + (0 + 1 / (G : ℝ)))
        = 2 * r - 2 / (G : ℝ) := by ring
    rw [hexp] at hlen
    have hid : (2 * r - 2 / (G : ℝ)) * G - 2 = 2 * (r * G) - 4 := by field_simp; ring
    rw [hid] at hlen; linarith
  have hℓ : 0 < ℓ := by exact_mod_cast hlenR
  have hIoo : Set.Ioo ((i : ℝ) / G) (((i : ℝ) + ℓ) / G) ⊆ Set.Ioo (0 : ℝ) 1 :=
    hrsub.trans ((Set.Ioo_subset_Ioo (by linarith) (by linarith)).trans hsub)
  have hne : (i : ℝ) / G < ((i : ℝ) + ℓ) / G := by
    rw [div_lt_div_iff₀ hG0R hG0R]; nlinarith
  obtain ⟨hlo, hhi⟩ := (Set.Ioo_subset_Ioo_iff hne).mp hIoo
  have hi0 : (0 : ℤ) ≤ i := by
    have hz : (0 : ℝ) ≤ (i : ℝ) := by
      have := (le_div_iff₀ hG0R).mp hlo; linarith
    exact_mod_cast hz
  have hiG : i + (ℓ : ℤ) ≤ (G : ℤ) := by
    have hz : (i : ℝ) + (ℓ : ℝ) ≤ (G : ℝ) := (div_le_one hG0R).mp hhi
    exact_mod_cast hz
  exact ⟨G, i, ℓ, hG0, hℓ, hi0, hiG, hzr⟩

end QuadSetup

end BB61
