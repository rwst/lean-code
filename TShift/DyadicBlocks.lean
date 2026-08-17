/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TShift.MahlerCountMul
import BB13.Constants
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Theorem A: the failures of `‖D(p/q)ⁿ‖ < cⁿ` meet boundedly many dyadic blocks

`TShift/MahlerCountMul.lean` proves the failure set finite at every admissible multiplier, but
*ineffectively*: `Set.Finite` names no threshold, because the number of failures on a single line
is the open per-line problem ([BE08] Rem. 7.4).  What **is** effective is the number of lines, and
this file turns that into an effective statement about the dates themselves — in the only currency
the line cover supports.

A line whose least above-threshold failure is `a` carries all its failures in `[a, a/f_∞)`
(`BB13.sameLineMul_lt_div_fArch`), and such an interval meets at most `t + 1` dyadic blocks
`[2ᵐ, 2ᵐ⁺¹)` whenever `2^t ≥ 1/f_∞`.  With at most `K(ε(p,c))` lines above the height threshold `N`
and at most `⌊log₂ N⌋ + 1` blocks below it,

`#{m : block m contains a failure} ≤ K(ε(p,c))·(t+1) + ⌊log₂ N⌋ + 1 =: B`   (`badBlocks_card_le`),

with every quantity explicit.  Equivalently — and this is the reading that matters — all but `B`
blocks are **entirely good**: every single date in them satisfies `‖D(p/q)ⁿ‖ ≥ cⁿ`
(`forall_good_of_block_good`).

## The showcase, and why `3/4`

At `(D, θ) = (5, 3/4)` every numeric input is already certified in this corpus:
`ε(3, 3/4) = ε*` is literally Problem 10.13's constant, so `K(ε*) ≤ 1.86·10¹²`
(`BB13.lineBound_epsStar_le`); the threshold `(3/4)ⁿ < 1/16` holds from `n = 10`
(`BB13.three_quarters_pow_lt`); and `1/f_∞ = log₂3 < 2` gives `t = 1`, i.e. two blocks per line.
Hence `badBlocks_card_le_five_decimal`: at most `3 720 000 000 004` bad blocks, with no new
numerics at all.  (The true value of `K(ε*)` is `1 856 360 182 227`, whence the plan's
`< 3.72·10¹²`; the *certified* decimal gives the figure above, four units over that round number.)

## The `κ` annotation (report §9)

The rate `3/4` clears the `2/3` barrier, so inside a spared block the sojourn cap runs at
`κ(3/4) = 0.70951 < 1` (`TShift.kappa_three_quarters_lt_one`,
`TShift.sojourn_cap_in_good_block`).  This is a **block** statement, not the sojourn cap: it says
nothing about which blocks are spared, and it is not a per-date bound valid at every date.  See
"What is not here".

## Contents

* `BB13.blockIdx`, `blockIdx_eq`, `blockIdx_le_of_le_mul`, `ncard_blockIdx_image_le`,
  `ncard_blockIdx_image_lt_le` — the block index `⌊log₂ n⌋ = Nat.log 2 n` and the two counting
  lemmas: a set confined to `[a, 2^t·a]` meets at most `t + 1` blocks; a set below `N` meets at
  most `⌊log₂ N⌋ + 1`.
* `BB13.badBlocks`, `BB13.blockBound` — the blocks met by the failure set, and `B(θ, D)` as a
  closed `ℕ`-expression in `BugeaudEvertse.lineBound`.
* `BB13.ncard_blockIdx_highFibreMul_le` — the per-line span: `t + 1` blocks per line.
* `BB13.badBlocks_card_le` — **Theorem A**.
* `BB13.forall_good_of_block_good` — the entirely-good reading of a spared block.
* `TShift.badBlocks_three_two_card_le` — Theorem A at base `3/2`, rate `3/4`, every odd multiplier.
* `TShift.badBlocks_card_le_five`, `badBlocks_card_le_five_decimal` — **Corollary A′** at
  `(D, θ) = (5, 3/4)`.
* `TShift.badBlocks_cycleDenom_card_le` — the cycle denominators `D_p = 3^p − 2^p`, with the
  threshold `max 10 (p+1)` explicit: `D` enters `B` only through `⌊log₂ ⌈log₃ 2D⌉⌋`.
* `TShift.le_distToNearestInt_of_block_good`, `sojourn_cap_in_good_block` — the T-shift reading of
  a spared block, and its `κ`.
* `TShift.failuresMul_cycleDenom_finite` — Theorem C at `D = D_p` (from `MahlerCountMul`).

## What is not here

* **No position is located.**  The bad blocks come from the Ridout cover's unlocated lines; nothing
  here exhibits a single good block, and `badBlocks` is not shown nonempty or empty.
* **No per-date bound** beyond what `TShift/HabsiegerTransfer.lean` already gives (`0.57434`, at
  every date).  The statement here is `θ = 3/4 > 2/3` *at every date of all but `B` blocks*.
* **No date count.**  `#{n : ‖D(3/2)ⁿ‖ < θⁿ} ≤ K(θ, D)` is *not* proved and is not provable by this
  route: it needs the uniform per-line height of [BE08] Rem. 7.4.  The conditional form is
  `BB13.mahler_failures_mul_card_le_of_heightBound`.
* **No escape payoff.**  The corpus already carries `TShift.dyadic_block_visit` unconditionally and
  with no Diophantine input (`TShift/FreeSojourn.lean`), which is strictly stronger than anything
  the block count buys here.

## Claim level

`badBlocks_card_le` is not claimed novel: gate G‑B (the novelty sweep) has not been run.  The
mathematics is the quantitative Ridout cover of [BE08] plus elementary bookkeeping; what is new
here is the formalization and the multiplier scope.

## Trust ledger

`std3 + BugeaudEvertse.ridout_line_cover`, entering through `BB13.mahler_line_cover` exactly as in
`TShift/MahlerCountMul.lean`.  The block machinery of §1 is `std3` alone.  No `sorry`, no
`native_decide`, no new cited axiom.

## References

* [Mah57] K. Mahler, *On the fractional parts of the powers of a rational number II*, Mathematika
  **4** (1957), 122–124.
* [BE08] Y. Bugeaud, J.-H. Evertse, *On two notions of complexity of algebraic numbers*, Acta
  Arith. **133** (2008), Cor. 5.2 and Rem. 7.4.
* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, Cambridge Tracts in
  Mathematics **193**, 2012 (Problem 10.13).
* `plans/plan-Tshift-S2.html` WP3 (this file), Theorem A / Corollary A′ / derivation D2;
  `plans/note-Tshift-S2-blocks.html` §2.2 (the counting convention) and §2.3 (F5, the showcase).
-/

namespace BB13

open scoped Real

/-! ## 1. Dyadic blocks

Block `m` is `[2ᵐ, 2ᵐ⁺¹)`, so the block of a date `n ≥ 1` is `⌊log₂ n⌋ = Nat.log 2 n`.  This is the
convention fixed by WP0 (note §2.2), used by both the note and the statements below. -/

/-- The **dyadic block index** of a date: `n ∈ [2ᵐ, 2ᵐ⁺¹) ↔ blockIdx n = m` for `n ≥ 1`. -/
def blockIdx (n : ℕ) : ℕ := Nat.log 2 n

/-- The defining property of the block index. -/
@[category API, AMS 11 37, ref "Bug12", group "tshift_s2"]
theorem blockIdx_eq {m n : ℕ} (h1 : 2 ^ m ≤ n) (h2 : n < 2 ^ (m + 1)) : blockIdx n = m :=
  Nat.log_eq_of_pow_le_of_lt_pow h1 h2

/-- **The span of a confined interval**: if `b ≤ 2^t·a` with `a ≥ 1`, then `b` lies at most `t`
blocks above `a`.  The `+1` in the block count `t + 1` below is the straddle case, and this is
where it is paid for: `a` itself need not sit at a block boundary. -/
@[category API, AMS 11 37, ref "Bug12", group "tshift_s2"]
theorem blockIdx_le_of_le_mul {a b t : ℕ} (h : b ≤ 2 ^ t * a) :
    blockIdx b ≤ blockIdx a + t := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp [blockIdx]
  · have h2 : a < 2 ^ (Nat.log 2 a + 1) := Nat.lt_pow_succ_log_self (by norm_num) a
    have hpow : (0 : ℕ) < 2 ^ t := pow_pos (by norm_num) t
    have h3 : b < 2 ^ (Nat.log 2 a + t + 1) := by
      calc b ≤ 2 ^ t * a := h
        _ < 2 ^ t * 2 ^ (Nat.log 2 a + 1) := by exact mul_lt_mul_of_pos_left h2 hpow
        _ = 2 ^ (Nat.log 2 a + t + 1) := by rw [← pow_add]; congr 1; omega
    have h4 := Nat.log_lt_of_lt_pow (by omega : b ≠ 0) h3
    simp only [blockIdx]
    omega

/-- **A line-fibre meets at most `t + 1` blocks.**  Everything in `S` lies in `[a, 2^t·a]`, so the
block indices of `S` lie in the `t + 1` values `⌊log₂ a⌋ … ⌊log₂ a⌋ + t`. -/
@[category research solved, AMS 11 37, ref "Bug12", group "tshift_s2"]
theorem ncard_blockIdx_image_le {S : Set ℕ} {a t : ℕ}
    (hS : ∀ b ∈ S, a ≤ b ∧ b ≤ 2 ^ t * a) : (blockIdx '' S).ncard ≤ t + 1 := by
  have hsub : blockIdx '' S ⊆ ↑(Finset.Icc (blockIdx a) (blockIdx a + t)) := by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨h1, h2⟩ := hS b hb
    simp only [Finset.coe_Icc, Set.mem_Icc]
    exact ⟨Nat.log_mono_right h1, blockIdx_le_of_le_mul h2⟩
  calc (blockIdx '' S).ncard
      ≤ (↑(Finset.Icc (blockIdx a) (blockIdx a + t)) : Set ℕ).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (Finset.Icc (blockIdx a) (blockIdx a + t)).card := Set.ncard_coe_finset _
    _ = t + 1 := by rw [Nat.card_Icc]; omega

/-- **The dates below the threshold occupy at most `⌊log₂ N⌋ + 1` blocks.** -/
@[category research solved, AMS 11 37, ref "Bug12", group "tshift_s2"]
theorem ncard_blockIdx_image_lt_le {S : Set ℕ} {N : ℕ} (hS : ∀ n ∈ S, n < N) :
    (blockIdx '' S).ncard ≤ Nat.log 2 N + 1 := by
  have hsub : blockIdx '' S ⊆ ↑(Finset.range (Nat.log 2 N + 1)) := by
    rintro _ ⟨n, hn, rfl⟩
    simp only [Finset.coe_range, Set.mem_Iio]
    exact Nat.lt_succ_of_le (Nat.log_mono_right (hS n hn).le)
  calc (blockIdx '' S).ncard ≤ (↑(Finset.range (Nat.log 2 N + 1)) : Set ℕ).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (Finset.range (Nat.log 2 N + 1)).card := Set.ncard_coe_finset _
    _ = Nat.log 2 N + 1 := Finset.card_range _

/-! ## 2. The bad blocks and the bound `B` -/

/-- The **bad blocks**: the dyadic blocks that contain at least one failure of
`‖D(p/q)ⁿ‖ < cⁿ`. -/
def badBlocks (D p q : ℕ) (c : ℝ) : Set ℕ := blockIdx '' failuresMul D p q c

/-- `B(θ, D) = K(ε(p,c))·(t+1) + ⌊log₂ N⌋ + 1` — a closed `ℕ`-expression in
`BugeaudEvertse.lineBound`, with `t` the block span per line (`2^t ≥ 1/f_∞`) and `N` the height
threshold.  The two real-analytic constants stay in the *hypotheses* of `badBlocks_card_le`, where
each instance discharges them by a rational comparison. -/
noncomputable def blockBound (p : ℕ) (c : ℝ) (t N : ℕ) : ℕ :=
  BugeaudEvertse.lineBound (epsilon p c) * (t + 1) + (Nat.log 2 N + 1)

/-- **A spared block is entirely good.**  If block `m` contains no failure, then *every* date in
`[2ᵐ, 2ᵐ⁺¹)` satisfies `‖D(p/q)ⁿ‖ ≥ cⁿ` — not merely one of them.  This is the reading Theorem A
is stated for. -/
@[category research solved, AMS 11 37, ref "Mah57" "BE08" "Bug12", group "tshift_s2"]
theorem forall_good_of_block_good {D p q : ℕ} {c : ℝ} {m : ℕ} (hgood : m ∉ badBlocks D p q c) :
    ∀ n, 2 ^ m ≤ n → n < 2 ^ (m + 1) →
      c ^ n ≤ distToNearestInt ((D : ℝ) * ((p : ℝ) / q) ^ n) := by
  intro n h1 h2
  have hn1 : 1 ≤ n := le_trans (Nat.one_le_pow m 2 (by norm_num)) h1
  have hnot : ¬ IsFailureMul (D : ℚ) p q c n := by
    intro hf
    exact hgood ⟨n, ⟨hn1, hf⟩, blockIdx_eq h1 h2⟩
  simp only [IsFailureMul, not_lt] at hnot
  simpa using hnot

/-! ## 3. The per-line block span -/

/-- **Each line of the cover meets at most `t + 1` blocks.**  The confinement
`b < a/f_∞` (`sameLineMul_lt_div_fArch`) with `a` the *least* above-threshold date of the line —
which need not itself be a failure, only `≥ 1`, since the proof runs on `|kₐ| ≥ 1` — puts the whole
fibre in `[a, 2^t·a]` as soon as `2^t·f_∞ ≥ 1`. -/
@[category research solved, AMS 11 37, ref "Mah57" "BE08" "Bug12", group "tshift_s2"]
theorem ncard_blockIdx_highFibreMul_le {D p q : ℕ} {c : ℝ} {N t : ℕ} (hp : 1 < p) (hq : 1 < q)
    (hqp : q < p) (hadm : AdmissibleMul D p q) (hc0 : 0 < c) (hc1 : c < 1) (hN : 1 ≤ N)
    (ht : (1 : ℝ) ≤ 2 ^ t * fArch p q c) (r : ℚ) :
    (blockIdx '' highFibreMul D p q c N r).ncard ≤ t + 1 := by
  rcases Set.eq_empty_or_nonempty (highFibreMul D p q c N r) with he | hne
  · rw [he, Set.image_empty, Set.ncard_empty]
    omega
  · obtain ⟨a, hamem, hamin⟩ :
        ∃ a, a ∈ highFibreMul D p q c N r ∧ ∀ b ∈ highFibreMul D p q c N r, a ≤ b :=
      ⟨sInf (highFibreMul D p q c N r), Nat.sInf_mem hne, fun b hb => Nat.sInf_le hb⟩
    have ha1 : 1 ≤ a := le_trans hN hamem.1
    have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hq
    have hqp' : (q : ℝ) ≤ (p : ℝ) := by exact_mod_cast hqp.le
    have hcq : c * (q : ℝ) < (p : ℝ) := by nlinarith
    have hF : 0 < fArch p q c := fArch_pos hp (by omega) hc0 hcq
    refine ncard_blockIdx_image_le (a := a) (fun b hb => ⟨hamin b hb, ?_⟩)
    rcases eq_or_lt_of_le (hamin b hb) with heq | hlt
    · rw [← heq]
      have h2 : 1 ≤ 2 ^ t := Nat.one_le_pow t 2 (by norm_num)
      nlinarith
    · have hconf := sameLineMul_lt_div_fArch hp hq hqp hadm hc0 hc1 ha1 hlt hb.2.1
        (hamem.2.2.trans hb.2.2.symm)
      have haR : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
      have hle : (a : ℝ) / fArch p q c ≤ 2 ^ t * (a : ℝ) := by
        rw [div_le_iff₀ hF]
        nlinarith [mul_le_mul_of_nonneg_left ht haR]
      have hbR : (b : ℝ) < ((2 ^ t * a : ℕ) : ℝ) := by push_cast; linarith
      have hbN : b < 2 ^ t * a := by exact_mod_cast hbR
      omega

/-! ## 4. Theorem A -/

/-- **Theorem A — block confinement, unconditional and effective.**  For every coprime `p > q ≥ 2`,
every admissible multiplier `D` and every rate `0 < c < 1`, the failures of `‖D(p/q)ⁿ‖ < cⁿ` meet
at most

`B = K(ε(p,c))·(t+1) + ⌊log₂ N⌋ + 1`

dyadic blocks `[2ᵐ, 2ᵐ⁺¹)`, where `N` is any height threshold for the line cover and `t` is any
natural with `2^t·f_∞ ≥ 1`.  Both hypotheses are discharged by explicit numerals at every instance
(§5), so `B` is fully effective.

By `forall_good_of_block_good`, the equivalent reading is: for all but `B` values of `m`, **every**
`n ∈ [2ᵐ, 2ᵐ⁺¹)` satisfies `‖D(p/q)ⁿ‖ ≥ cⁿ`.

What is *not* effective is *which* blocks are bad — the lines of `mahler_line_cover` are not
located — and the number of failing dates, which is the open per-line problem ([BE08] Rem. 7.4).
Footprint `std3 + BugeaudEvertse.ridout_line_cover`. -/
@[category research solved, AMS 11 37, ref "Mah57" "BE08" "Bug12", group "tshift_s2"]
theorem badBlocks_card_le {D p q : ℕ} {c : ℝ} {N t : ℕ} (hq : 1 < q) (hqp : q < p)
    (hcop : Nat.Coprime p q) (hadm : AdmissibleMul D p q) (hc0 : 0 < c) (hc1 : c < 1)
    (hN : 1 ≤ N)
    (hthr : ∀ n, N ≤ n →
      c ^ n < 1 / 16 ∧ 2 * (BugeaudEvertse.ratHeight (D : ℚ) : ℝ) < (p : ℝ) ^ n)
    (ht : (1 : ℝ) ≤ 2 ^ t * fArch p q c) :
    (badBlocks D p q c).ncard ≤ blockBound p c t N := by
  classical
  have hp : 1 < p := lt_trans hq hqp
  obtain ⟨R, hcard, hR⟩ := mahler_line_cover (D : ℚ) p q c (by omega) hqp hcop hc0 hc1
  have hfin : (failuresMulFrom D p q c N).Finite :=
    failuresMulFrom_finite hq hqp hcop hadm hc0 hc1 hthr hN
  have hlowfin : {n : ℕ | 1 ≤ n ∧ IsFailureMul (D : ℚ) p q c n ∧ n < N}.Finite :=
    Set.Finite.subset (Set.finite_Iio N) (fun n hn => hn.2.2)
  -- below the threshold: at most `⌊log₂ N⌋ + 1` blocks
  have hlow : (blockIdx '' {n : ℕ | 1 ≤ n ∧ IsFailureMul (D : ℚ) p q c n ∧ n < N}).ncard
      ≤ Nat.log 2 N + 1 :=
    ncard_blockIdx_image_lt_le (fun n hn => hn.2.2)
  -- above it: at most `K(ε)` lines, each meeting at most `t + 1` blocks
  have hhigh : (blockIdx '' failuresMulFrom D p q c N).ncard
      ≤ BugeaudEvertse.lineBound (epsilon p c) * (t + 1) := by
    set T := blockIdx '' failuresMulFrom D p q c N with hT
    have hTfin : T.Finite := hfin.image _
    set g : ℕ → ℕ := Function.invFunOn blockIdx (failuresMulFrom D p q c N) with hg
    have hgspec : ∀ m ∈ T, g m ∈ failuresMulFrom D p q c N ∧ blockIdx (g m) = m := by
      intro m hm
      obtain ⟨n, hn, hnm⟩ := hm
      exact ⟨Function.invFunOn_mem ⟨n, hn, hnm⟩, Function.invFunOn_eq ⟨n, hn, hnm⟩⟩
    have hfib : ∀ r : ℚ, {m ∈ T | linePointMul (D : ℚ) p q (g m) = r}.ncard ≤ t + 1 := by
      intro r
      refine le_trans (Set.ncard_le_ncard ?_ ?_)
        (ncard_blockIdx_highFibreMul_le hp hq hqp hadm hc0 hc1 hN ht r)
      · rintro m ⟨hm, hr⟩
        obtain ⟨hmem, hblk⟩ := hgspec m hm
        exact ⟨g m, ⟨hmem.1, hmem.2, hr⟩, hblk⟩
      · exact (hfin.subset (fun n hn => ⟨hn.1, hn.2.1⟩)).image _
    have hkey := Set.ncard_le_mul_ncard_image hTfin
      (fun m => linePointMul (D : ℚ) p q (g m)) (t + 1) hfib
    have himg : (fun m => linePointMul (D : ℚ) p q (g m)) '' T ⊆ ↑R := by
      rintro _ ⟨m, hm, rfl⟩
      obtain ⟨hmem, -⟩ := hgspec m hm
      exact hR _ (hthr _ hmem.1).1 (hthr _ hmem.1).2 hmem.2
    calc T.ncard
        ≤ (t + 1) * ((fun m => linePointMul (D : ℚ) p q (g m)) '' T).ncard := hkey
      _ ≤ (t + 1) * (↑R : Set ℚ).ncard :=
          Nat.mul_le_mul (le_refl (t + 1)) (Set.ncard_le_ncard himg R.finite_toSet)
      _ = (t + 1) * R.card := by rw [Set.ncard_coe_finset]
      _ ≤ (t + 1) * BugeaudEvertse.lineBound (epsilon p c) :=
          Nat.mul_le_mul (le_refl (t + 1)) hcard
      _ = BugeaudEvertse.lineBound (epsilon p c) * (t + 1) := Nat.mul_comm _ _
  have hsplit : badBlocks D p q c ⊆
      blockIdx '' {n : ℕ | 1 ≤ n ∧ IsFailureMul (D : ℚ) p q c n ∧ n < N}
        ∪ blockIdx '' failuresMulFrom D p q c N := by
    rintro m ⟨n, ⟨h1, hf⟩, rfl⟩
    rcases lt_or_ge n N with hlt | hge
    · exact Or.inl ⟨n, ⟨h1, hf, hlt⟩, rfl⟩
    · exact Or.inr ⟨n, ⟨hge, hf⟩, rfl⟩
  calc (badBlocks D p q c).ncard
      ≤ (blockIdx '' {n : ℕ | 1 ≤ n ∧ IsFailureMul (D : ℚ) p q c n ∧ n < N}
          ∪ blockIdx '' failuresMulFrom D p q c N).ncard :=
        Set.ncard_le_ncard hsplit ((hlowfin.image _).union (hfin.image _))
    _ ≤ (blockIdx '' {n : ℕ | 1 ≤ n ∧ IsFailureMul (D : ℚ) p q c n ∧ n < N}).ncard
        + (blockIdx '' failuresMulFrom D p q c N).ncard := Set.ncard_union_le _ _
    _ ≤ (Nat.log 2 N + 1) + BugeaudEvertse.lineBound (epsilon p c) * (t + 1) :=
        Nat.add_le_add hlow hhigh
    _ = blockBound p c t N := by simp only [blockBound]; ring

/-! ## 5. The constant at `(p, q, c) = (3, 2, 3/4)`

`f_∞ = θ = log 2/log 3 = 0.63093…`, so `1/f_∞ = log₂3 = 1.58496… < 2` and one doubling suffices:
`t = 1`, i.e. `b_ℓ = 2` blocks per line.  The only inequality needed is `log 3 ≤ 2·log 2`. -/

/-- `2·f_∞(3, 2, 3/4) ≥ 1`, i.e. `log₂3 ≤ 2`: the block span at the showcase is `t = 1`. -/
@[category API, AMS 11 37, ref "Bug12", group "tshift_s2"]
theorem one_le_two_pow_one_mul_fArch : (1 : ℝ) ≤ 2 ^ 1 * fArch 3 2 (3 / 4) := by
  have h3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hle : Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  rw [fArch_three_two, theta, pow_one, ← mul_div_assoc, le_div_iff₀ h3, one_mul]
  linarith

end BB13

/-! # The T-shift reading

At `(p, q) = (3, 2)` the cycle denominators `D_p = 3^p − 2^p` are odd, hence admissible, and the
rate `3/4` clears the `2/3` barrier.  So Theorem A says: for all but `B` dyadic blocks, **every**
date in the block satisfies `‖(3/2)ⁿ − A/D_p‖ ≥ (1/D_p)(3/4)ⁿ`, for every numerator `A` at once —
and inside such a block the sojourn cap runs at `κ(3/4) = 0.70951 < 1`.

This is the item's whole claim, and its limits are the ones listed in "What is not here": the
spared blocks are not located, and nothing improves the per-date rate `0.57434` of
`TShift/HabsiegerTransfer.lean` that holds at *every* date. -/

namespace TShift

open scoped Real

/-! ## 6. Theorem A at base `3/2` -/

/-- **Theorem A at base `3/2`, rate `3/4`, every odd multiplier.**  `N` is any date from which
`2D < 3^N` (the height threshold; `(3/4)ⁿ < 1/16` is free from `n = 10`), and the block span is
`t = 1`. -/
@[category research solved, AMS 11 37, ref "Mah57" "BE08" "Bug12", group "tshift_s2"]
theorem badBlocks_three_two_card_le {D N : ℕ} (hD : Odd D) (hN : 10 ≤ N) (hDN : 2 * D < 3 ^ N) :
    (BB13.badBlocks D 3 2 (3 / 4)).ncard
      ≤ BugeaudEvertse.lineBound BB13.epsStar * 2 + (Nat.log 2 N + 1) := by
  have hDpos : 0 < D := hD.pos
  have hthr : ∀ n, N ≤ n →
      (3 / 4 : ℝ) ^ n < 1 / 16 ∧
        2 * (BugeaudEvertse.ratHeight ((D : ℕ) : ℚ) : ℝ) < ((3 : ℕ) : ℝ) ^ n := by
    intro n hn
    refine ⟨BB13.three_quarters_pow_lt (by omega), ?_⟩
    rw [BB13.ratHeight_natCast, max_eq_left hDpos]
    have hnat : 2 * D < 3 ^ n := lt_of_lt_of_le hDN (Nat.pow_le_pow_right (by norm_num) hn)
    have hcast : ((2 * D : ℕ) : ℝ) < ((3 ^ n : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at hcast ⊢
    linarith
  have h := BB13.badBlocks_card_le (D := D) (p := 3) (q := 2) (c := 3 / 4) (N := N) (t := 1)
    (by norm_num) (by norm_num) (by decide) (admissibleMul_three_two hD) (by norm_num)
    (by norm_num) (by omega) hthr BB13.one_le_two_pow_one_mul_fArch
  have heq : BB13.blockBound 3 (3 / 4) 1 N
      = BugeaudEvertse.lineBound BB13.epsStar * 2 + (Nat.log 2 N + 1) := by
    simp only [BB13.blockBound, ← BB13.epsStar_eq_epsilon]
  exact heq ▸ h

/-- **Corollary A′ — the showcase.**  At `(D, θ) = (5, 3/4)`: the dates with `‖5(3/2)ⁿ‖ < (3/4)ⁿ`
meet at most `2·K(ε*) + 4` dyadic blocks.  Every constant is already certified in this corpus
(`BB13.lineBound_epsStar_le`, `BB13.three_quarters_pow_lt`); the height threshold is `N = 10`,
which contributes `⌊log₂ 10⌋ + 1 = 4`, and the span is `t = 1`.

`κ(3/4) = 0.70951 < 1` (`kappa_three_quarters_lt_one`), so in every spared block the statement is
genuinely below the `2/3` barrier — in the per-date currency, and only there. -/
@[category research solved, AMS 11 37, ref "Mah57" "BE08" "Bug12", group "tshift_s2"]
theorem badBlocks_card_le_five :
    (BB13.badBlocks 5 3 2 (3 / 4)).ncard ≤ 2 * BugeaudEvertse.lineBound BB13.epsStar + 4 := by
  have h := badBlocks_three_two_card_le (D := 5) (N := 10) (by decide) (le_refl 10) (by norm_num)
  have hlog : Nat.log 2 10 = 3 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  rw [hlog] at h
  omega

/-- **Corollary A′ in decimals**: at most `3 720 000 000 004` bad blocks.  The plan quotes
`< 3.72·10¹²`, which is the figure at the *true* value `K(ε*) = 1 856 360 182 227`; the certified
bound `K(ε*) ≤ 1.86·10¹²` gives four units more. -/
@[category research solved, AMS 11 37, ref "Mah57" "BE08" "Bug12", group "tshift_s2"]
theorem badBlocks_card_le_five_decimal :
    (BB13.badBlocks 5 3 2 (3 / 4)).ncard ≤ 3720000000004 := by
  have h1 := badBlocks_card_le_five
  have h2 := BB13.lineBound_epsStar_le
  omega

/-- **The cycle denominators.**  `D_p = 3^p − 2^p` is odd, and `2D_p < 3^{p+1}`, so the threshold
is `max 10 (p+1)`: the multiplier enters `B` only through `⌊log₂(p+1)⌋`, uniformly over all
periods.  Summing over `p ≤ P` gives `P·(2K(ε*) + log₂(P+1) + 1)`, entirely effective. -/
@[category research solved, AMS 11 37, ref "Mah57" "BE08" "A6plus", group "tshift_s2"]
theorem badBlocks_cycleDenom_card_le {p : ℕ} (hp : 1 ≤ p) :
    (BB13.badBlocks (Z32.cycleDenom p) 3 2 (3 / 4)).ncard
      ≤ BugeaudEvertse.lineBound BB13.epsStar * 2 + (Nat.log 2 (max 10 (p + 1)) + 1) := by
  refine badBlocks_three_two_card_le (Z32.cycleDenom_odd hp) (le_max_left _ _) ?_
  have h2 : (0 : ℕ) < 3 ^ p := pow_pos (by norm_num) p
  have h1 : Z32.cycleDenom p ≤ 3 ^ p := by
    simp only [Z32.cycleDenom]
    exact Nat.sub_le _ _
  calc 2 * Z32.cycleDenom p ≤ 2 * 3 ^ p := by omega
    _ < 3 ^ (p + 1) := by rw [pow_succ]; omega
    _ ≤ 3 ^ (max 10 (p + 1)) := Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)

/-! ## 7. What a spared block says about the cycle targets, and its `κ` -/

/-- **The T-shift reading of a spared block.**  If block `m` carries no failure of the multiplier
`D_p`, then at *every* date of that block the orbit stays `(1/D_p)(3/4)ⁿ` away from *every* cycle
target of period `p`.  The rate is `3/4 > 2/3`; the constant `1/D_p` and the block are explicit —
what is not explicit is which `m` qualify. -/
@[category research solved, AMS 11 37, ref "Mah57" "BE08" "A6plus", group "tshift_s2"]
theorem le_distToNearestInt_of_block_good {p : ℕ} (hp : 1 ≤ p) (A : ℤ) {m : ℕ}
    (hgood : m ∉ BB13.badBlocks (Z32.cycleDenom p) 3 2 (3 / 4)) {n : ℕ}
    (h1 : 2 ^ m ≤ n) (h2 : n < 2 ^ (m + 1)) :
    1 / (Z32.cycleDenom p : ℝ) * (3 / 4 : ℝ) ^ n
      ≤ distToNearestInt (((3 : ℝ) / 2) ^ n - (A : ℝ) / Z32.cycleDenom p) := by
  have hD : 0 < Z32.cycleDenom p := Z32.cycleDenom_pos hp
  have hDR : (0 : ℝ) < ((Z32.cycleDenom p : ℕ) : ℝ) := by exact_mod_cast hD
  have hmul := BB13.forall_good_of_block_good hgood n h1 h2
  push_cast at hmul
  have hred := distToNearestInt_mul_le hD (((3 : ℝ) / 2) ^ n) A
  rw [one_div, inv_mul_eq_div, div_le_iff₀ hDR]
  calc (3 / 4 : ℝ) ^ n
      ≤ distToNearestInt (((Z32.cycleDenom p : ℕ) : ℝ) * ((3 : ℝ) / 2) ^ n) := hmul
    _ ≤ ((Z32.cycleDenom p : ℕ) : ℝ)
        * distToNearestInt (((3 : ℝ) / 2) ^ n - (A : ℝ) / (Z32.cycleDenom p : ℕ)) := hred
    _ = distToNearestInt (((3 : ℝ) / 2) ^ n - (A : ℝ) / (Z32.cycleDenom p : ℕ))
        * ((Z32.cycleDenom p : ℕ) : ℝ) := by ring

/-- `κ(3/4) = log(4/3)/log(3/2) = 0.70951… < 1` — the showcase rate is below the `2/3` barrier
(report §9: every headline states its `κ`). -/
@[category API, AMS 11 37, ref "A6plus", group "tshift_s2"]
theorem kappa_three_quarters_lt_one : kappa (3 / 4 : ℝ) < 1 :=
  (kappa_lt_one_iff (by norm_num)).mpr (by norm_num)

/-- **The `κ` of Theorem A.**  Inside a spared block the sojourn cap runs at `κ(3/4) < 1`: a
sojourn beginning at a date `n` of such a block has length `L ≤ κ(3/4)·n + log D_p/log(3/2)`.

This is *not* the sojourn cap of `TShift/FreeSojourn.lean`, which holds at every date with
`κ_free = 0.585` and no Diophantine input; the point here is only that the block statement is a
per-date rate above `2/3`, which the free rung does not provide. -/
@[category research solved, AMS 11 37, ref "Mah57" "BE08" "A6plus", group "tshift_s2"]
theorem sojourn_cap_in_good_block {p : ℕ} (hp : 1 ≤ p) (A : ℤ) {m : ℕ}
    (hgood : m ∉ BB13.badBlocks (Z32.cycleDenom p) 3 2 (3 / 4)) {n L : ℕ}
    (h1 : 2 ^ m ≤ n) (h2 : n < 2 ^ (m + 1))
    (hshadow : distToNearestInt (((3 : ℝ) / 2) ^ n - (A : ℝ) / Z32.cycleDenom p)
      ≤ (2 / 3 : ℝ) ^ L) :
    (L : ℝ) ≤ kappa (3 / 4 : ℝ) * n
      + (-Real.log (1 / (Z32.cycleDenom p : ℝ))) / Real.log (3 / 2) := by
  have hD : 0 < Z32.cycleDenom p := Z32.cycleDenom_pos hp
  have hDR : (0 : ℝ) < ((Z32.cycleDenom p : ℕ) : ℝ) := by exact_mod_cast hD
  exact sojourn_cap_kappa (by positivity) (by norm_num)
    (le_distToNearestInt_of_block_good hp A hgood h1 h2) hshadow

/-- **Theorem C at the cycle denominators** — the instance the T-shift ladder consumes: for every
period `p` and every rate `θ < 1`, only finitely many dates fail `‖D_p(3/2)ⁿ‖ ≥ θⁿ`.  Ineffective
in the threshold; `badBlocks_cycleDenom_card_le` is the effective shadow of it. -/
@[category research solved, AMS 11 37, ref "Mah57" "BE08" "A6plus", group "tshift_s2"]
theorem failuresMul_cycleDenom_finite {p : ℕ} (hp : 1 ≤ p) {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) :
    (BB13.failuresMul (Z32.cycleDenom p) 3 2 θ).Finite :=
  failuresMul_three_two_finite (Z32.cycleDenom_odd hp) h0 h1

end TShift
