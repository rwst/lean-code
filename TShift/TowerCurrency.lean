/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.TowerCount
import TShift.DyadicBlocks
import ForMathlib.Data.Set.Card
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The second exception currency: towers at a multiplier, and why it cannot buy blocks

`TShift/DyadicBlocks.lean` (Theorem A) counts the dyadic blocks met by the failures of
`‖D(p/q)ⁿ‖ < cⁿ` in the currency of the Ridout **line cover**: at most `K(ε)` lines above the
height threshold, each meeting at most `t + 1` blocks.  `K(ε)` is bounded but astronomical
(`1.86·10¹²` at `ε*`), and it costs the cited axiom.

`BB13/GapPrinciple.lean` and `BB13/TowerCount.lean` carry a second, entirely elementary currency
at `δ = 1`: failures cluster into **towers**, and the number of tower bases below `N` is
`O(log N)` with tiny constants and no Diophantine input at all.  This file transports that layer
to an arbitrary multiplier `D` (WP5(a) of `plans/plan-Tshift-S2.html`) and then prices the swap
the plan proposed — replacing `b_ℓ·K(ε)` by the tower count.

## The transport

Everything in `BB13/GapPrinciple.lean` survives the multiplier verbatim, because `D` cancels out
of the gap identity: with `mₙ = round(D(p/q)ⁿ)` and `kₙ = D·pⁿ − mₙqⁿ`,

`qⁿ·(pᵈ·mₙ − qᵈ·mₙ₊ᵈ) = kₙ₊ᵈ − pᵈ·kₙ`   (`gap_identity_mul`),

an identity in which `D` does not occur.  Two failures within `d < ε·n` therefore link
(`linkage_mul`), with all four consequences (`link_resid_mul`, `link_dvd_mul`,
`link_scaling_mul`, `link_quality_mul`), and — the step this file needs and the `δ = 1` layer
never took — **linkage implies collinearity** (`sameLine_of_linkage`), so a linked pair is a pair
on one line of the cover and the confinement `b < a/f_∞` of `BB13.sameLineMul_lt_div_fArch`
applies to it.  Chaining down (`exists_isTowerBaseMul_sameLine`) puts every failure over a tower
base *on its own line*.

The tower count itself (`towerBasesMul_card_le`) needs even less than the linkage: the
non-linkage gap `gap_of_nonlink` mentions neither `q` nor `D`, so the `δ = 1` proof applies
unchanged, and the count holds at **every** multiplier with no admissibility and no parity
clause.  At `(p, q, c) = (3, 2, 3/4)` the threshold relation needs no decimal logarithm bounds
either: `ρ = 6/5` and `t = 11` reduce it to the integer inequality `3⁶⁶ ≤ 2¹⁰⁵`
(`towerBasesMul_card_le_three_halves`), where `BB13.towerBases_card_le_three_halves` still
carries `log 2 ≥ 0.6931` and `log 3 ≤ 1.0987` as hypotheses.

## The verdict: the tower currency cannot pay in block coin

Feeding the tower count into the block bookkeeping gives, unconditionally and with no cited
axiom, `#{bad blocks below N} ≤ (t+1)·(11 + 1 + log_ρ N)` (`ncard_badBlocksLe_le_tower`), which
at the showcase is `24 + 10.97·ln N`.  **This is vacuous**: there are only `⌊log₂N⌋ + 1 =
1.4427·ln N + 1` blocks below `N` in the first place (`badBlocksLe_card_le_log`), so the tower
bound is a factor `≈ 7.6` worse than counting *every* block as bad — and it is worse for every
`N`, not merely asymptotically (`tower_bound_not_below_trivial`).

The reason is structural, and it is the point of the file: blocks below `N` are themselves only
logarithmically many, so **only a line count bounded independently of `N` can show that most
blocks are good.**  That is exactly what the Ridout cover supplies and what no elementary gap
principle can, at any rate `c`.  Nor is it an artefact of the witness `ρ = 6/5`: at the sharp
ratio `1 + ε* = 1.26186…` the tower currency still spends `2/log(1+ε*) = 8.60` blocks per `ln N`
against the `1/log 2 = 1.44` that exist.  The swap WP5(a) proposed is therefore refuted rather
than performed, and outgoing angle O‑6's comparison question ("which currency gives the stronger
escape payoff at which `θ`") is answered: neither at any `θ` — they are not commensurable, the
tower currency counts *dates*, and its block shadow is dominated by the trivial bound.

Empirically the grouping is nearly vacuous too: over the census of the `s2` harness block
(`TShift/tshift_numerics.py`, section [G]; `D ∈ {1, 5, 19, 65}`, both rates, `n ≤ 1200`) there is
**one** linked pair among 79 failures, so towers and failures are all but the same count.  A link
needs two failures with `b ≤ 1.2619·a − 0.6309`, and failures are far too sparse for that.

What the transport does deliver on its own terms is a free sparsity statement about the failure
*dates* at every multiplier: below `N` they fall into at most `12 + 5.49·ln N` towers, each
confined to a single line, with footprint `std3`.

## The uniform-in-period package (WP5(b))

`TShift.badBlocks_cycleDenom_card_le` bounds the bad blocks of one cycle denominator
`D_p = 3^p − 2^p` with the threshold `max 10 (p+1)`.  Since the multiplier enters only through
`⌊log₂(p+1)⌋`, summing over `p ≤ P` is a summation and nothing more
(`badBlocks_cycleDenom_sum_card_le`); the form the escape accounting of the plan's D3 actually
consumes is the union `badBlocks_cycleDenom_biUnion_card_le`, the blocks bad for *some* period
`p ≤ P`, at most `P·(2K(ε*) + ⌊log₂ max(10, P+1)⌋ + 1)`, and in decimals
`badBlocks_cycleDenom_biUnion_card_le_decimal`.  Each set in the union is finite
(`badBlocks_cycleDenom_finite`), so the bound is not vacuous.

## Trust ledger

Sections 1–5 are `std3`: the whole tower layer, its transport and its block shadow are
elementary, and the no-go is arithmetic.  Only section 6 (the uniform-in-period package) carries
`BugeaudEvertse.ridout_line_cover`, inherited from Theorem A through
`TShift.badBlocks_cycleDenom_card_le`.  No `sorry`, no `native_decide`, no new cited axiom.

## References

* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, Cambridge Tracts
  in Mathematics **193**, 2012 (Problem 10.13 — the `δ = 1` gap principle and tower count).
* [Mah57] K. Mahler, *On the fractional parts of the powers of a rational number II*, Mathematika
  **4** (1957), 122–124 (Thm 1: the qualitative sparsity ancestor of the linkage lemma).
* [BE08] Y. Bugeaud, J.-H. Evertse, *On two notions of complexity of algebraic numbers*, Acta
  Arith. **133** (2008), Cor. 5.2 (the bounded line count the tower currency cannot replace).
* `plans/plan-Tshift-S2.html` WP5 (this file) and outgoing angle O‑6.
-/

namespace BB13

open scoped Real

/-! ## 1. The gap identity and the linkage lemma at a multiplier

The multiplier cancels out of the identity, so the `δ = 1` proofs of `BB13/GapPrinciple.lean`
transport line for line.  Only the failure test has to be converted through
`isFailureMul_iff_residMul`. -/

/-- **The gap identity at a multiplier** (exact, pure ring): `qⁿ·(pᵈ·m − qᵈ·m') = k' − pᵈ·k`
with `m = MnumMul`, `k = residMul`.  `D` occurs on neither side: it cancels between
`D·pⁿ⁺ᵈ` and `pᵈ·D·pⁿ`.  The `D = 1` case is `BB13.gap_identity`. -/
@[category API, AMS 11 37, ref "Bug12", group "tshift_s2"]
theorem gap_identity_mul (D p q n d : ℕ) :
    (q : ℤ) ^ n * ((p : ℤ) ^ d * MnumMul (D : ℚ) p q n
        - (q : ℤ) ^ d * MnumMul (D : ℚ) p q (n + d))
      = residMul D p q (n + d) - (p : ℤ) ^ d * residMul D p q n := by
  simp only [residMul, pow_add]; ring

/-- **Sharp linkage at a multiplier.**  If `n` and `n + d` are both failures of
`‖D(p/q)ⁿ‖ < cⁿ` and the sharp gap bound `cⁿ·((c·q)ᵈ + pᵈ) ≤ 1` holds, then `pᵈ·m = qᵈ·m'`:
the integer `pᵈ·m − qᵈ·m'` has absolute value `< 1`, hence vanishes.  The `D = 1` case is
`BB13.linkage`. -/
@[category research solved, AMS 11 37, ref "Mah57" "Bug12", group "tshift_s2"]
theorem linkage_mul {D p q : ℕ} {c : ℝ} (n d : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hn : IsFailureMul (D : ℚ) p q c n) (hnd : IsFailureMul (D : ℚ) p q c (n + d))
    (hthr : c ^ n * ((c * q) ^ d + (p : ℝ) ^ d) ≤ 1) :
    (p : ℤ) ^ d * MnumMul (D : ℚ) p q n = (q : ℤ) ^ d * MnumMul (D : ℚ) p q (n + d) := by
  have hn' : (|residMul D p q n| : ℝ) < (c * q) ^ n :=
    (isFailureMul_iff_residMul D p q c n hq).mp hn
  have hnd' : (|residMul D p q (n + d)| : ℝ) < (c * q) ^ (n + d) :=
    (isFailureMul_iff_residMul D p q c (n + d) hq).mp hnd
  set X : ℤ := (p : ℤ) ^ d * MnumMul (D : ℚ) p q n
    - (q : ℤ) ^ d * MnumMul (D : ℚ) p q (n + d) with hXdef
  have hid : (q : ℤ) ^ n * X = residMul D p q (n + d) - (p : ℤ) ^ d * residMul D p q n :=
    gap_identity_mul D p q n d
  have hqRpos : (0 : ℝ) < (q : ℝ) ^ n := by
    have : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    positivity
  have hpRpos : (0 : ℝ) < (p : ℝ) ^ d := by
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
    positivity
  have hidR : (q : ℝ) ^ n * |(X : ℝ)|
      = |(residMul D p q (n + d) : ℝ) - (p : ℝ) ^ d * (residMul D p q n : ℝ)| := by
    have hcast : ((q : ℝ)) ^ n * (X : ℝ)
        = (residMul D p q (n + d) : ℝ) - (p : ℝ) ^ d * (residMul D p q n : ℝ) := by
      exact_mod_cast hid
    rw [← hcast, abs_mul, abs_of_pos hqRpos]
  have hnR : |(residMul D p q n : ℝ)| < (c * q) ^ n := by
    rw [← Int.cast_abs]; exact_mod_cast hn'
  have hndR : |(residMul D p q (n + d) : ℝ)| < (c * q) ^ (n + d) := by
    rw [← Int.cast_abs]; exact_mod_cast hnd'
  have hkey : (q : ℝ) ^ n * |(X : ℝ)| < (c * q) ^ (n + d) + (p : ℝ) ^ d * (c * q) ^ n := by
    rw [hidR]
    calc |(residMul D p q (n + d) : ℝ) - (p : ℝ) ^ d * (residMul D p q n : ℝ)|
        ≤ |(residMul D p q (n + d) : ℝ)| + (p : ℝ) ^ d * |(residMul D p q n : ℝ)| := by
          calc |(residMul D p q (n + d) : ℝ) - (p : ℝ) ^ d * (residMul D p q n : ℝ)|
              ≤ |(residMul D p q (n + d) : ℝ)| + |(p : ℝ) ^ d * (residMul D p q n : ℝ)| :=
                abs_sub _ _
            _ = |(residMul D p q (n + d) : ℝ)| + (p : ℝ) ^ d * |(residMul D p q n : ℝ)| := by
                rw [abs_mul, abs_of_nonneg (le_of_lt hpRpos)]
      _ < (c * q) ^ (n + d) + (p : ℝ) ^ d * (c * q) ^ n := by
          have : (p : ℝ) ^ d * |(residMul D p q n : ℝ)| < (p : ℝ) ^ d * (c * q) ^ n :=
            mul_lt_mul_of_pos_left hnR hpRpos
          linarith
  have hrhs : (c * q) ^ (n + d) + (p : ℝ) ^ d * (c * q) ^ n
      = (q : ℝ) ^ n * (c ^ n * ((c * q) ^ d + (p : ℝ) ^ d)) := by
    rw [mul_pow, mul_pow, pow_add]; ring
  rw [hrhs] at hkey
  have hXlt1 : |(X : ℝ)| < 1 := by
    have h2 : (q : ℝ) ^ n * |(X : ℝ)| < (q : ℝ) ^ n * 1 := by
      calc (q : ℝ) ^ n * |(X : ℝ)| < (q : ℝ) ^ n * (c ^ n * ((c * q) ^ d + (p : ℝ) ^ d)) := hkey
        _ ≤ (q : ℝ) ^ n * 1 := mul_le_mul_of_nonneg_left hthr (le_of_lt hqRpos)
    exact lt_of_mul_lt_mul_left h2 (le_of_lt hqRpos)
  have hXint : |X| < 1 := by exact_mod_cast hXlt1
  have hX0 : X = 0 := Int.abs_lt_one_iff.mp hXint
  rw [hXdef] at hX0; linarith [hX0]

/-- **Linkage from the `Linkable` predicate**, at a multiplier.  `BB13.Linkable` mentions neither
`q` nor `D`, so it is reused unchanged. -/
@[category research solved, AMS 11 37, ref "Mah57" "Bug12", group "tshift_s2"]
theorem linkage_mul_of_linkable {D p q : ℕ} {c : ℝ} {n d : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hc0 : 0 ≤ c) (hcq : c * q ≤ (p : ℝ))
    (hn : IsFailureMul (D : ℚ) p q c n) (hnd : IsFailureMul (D : ℚ) p q c (n + d))
    (hlink : Linkable p c n (n + d)) :
    (p : ℤ) ^ d * MnumMul (D : ℚ) p q n = (q : ℤ) ^ d * MnumMul (D : ℚ) p q (n + d) := by
  have hcrude : 2 * c ^ n * (p : ℝ) ^ d ≤ 1 := by
    have h : Linkable p c n (n + d) = (2 * c ^ n * (p : ℝ) ^ (n + d - n) ≤ 1) := rfl
    rw [Nat.add_sub_cancel_left] at h
    rwa [h] at hlink
  exact linkage_mul n d hp hq hn hnd (crude_to_sharp p q c n d hc0 hcq hcrude)

/-! ## 2. Linkage implies collinearity

The step the `δ = 1` layer never needed: a linked pair sits on one line of the Bugeaud–Evertse
cover, so the archimedean confinement of `TShift/MahlerCountMul.lean` applies to it. -/

/-- **Linkage ⟹ collinearity.**  `pᵈ·mₐ = qᵈ·m_b` says exactly that the frame points
`(mₐqᵃ, pᵃ)` and `(m_b q^b, p^b)` are proportional, i.e. that `a` and `b` have the same
`linePointMul` slope. -/
@[category research solved, AMS 11 37, ref "BE08" "Bug12", group "tshift_s2"]
theorem sameLine_of_linkage {D p q : ℕ} {a d : ℕ} (hp : 0 < p)
    (hlink : (p : ℤ) ^ d * MnumMul (D : ℚ) p q a
      = (q : ℤ) ^ d * MnumMul (D : ℚ) p q (a + d)) :
    linePointMul (D : ℚ) p q a = linePointMul (D : ℚ) p q (a + d) := by
  have hp0 : ((p : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpa : ((p : ℚ)) ^ a ≠ 0 := pow_ne_zero _ hp0
  have hpb : ((p : ℚ)) ^ (a + d) ≠ 0 := pow_ne_zero _ hp0
  have hQ : ((p : ℚ)) ^ d * (MnumMul (D : ℚ) p q a : ℚ)
      = ((q : ℚ)) ^ d * (MnumMul (D : ℚ) p q (a + d) : ℚ) := by exact_mod_cast hlink
  rw [linePointMul, linePointMul, div_eq_div_iff hpa hpb, frameXMul, frameXMul]
  push_cast
  linear_combination ((q : ℚ) ^ a * (p : ℚ) ^ a) * hQ

/-- **Linkable failures are collinear** — the composite of `linkage_mul_of_linkable` and
`sameLine_of_linkage`, in the `a < b` form the descent below uses. -/
@[category research solved, AMS 11 37, ref "BE08" "Bug12", group "tshift_s2"]
theorem sameLine_of_linkable {D p q : ℕ} {c : ℝ} {a b : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hc0 : 0 ≤ c) (hcq : c * q ≤ (p : ℝ)) (hab : a < b)
    (hfa : IsFailureMul (D : ℚ) p q c a) (hfb : IsFailureMul (D : ℚ) p q c b)
    (hlink : Linkable p c a b) :
    linePointMul (D : ℚ) p q a = linePointMul (D : ℚ) p q b := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  exact sameLine_of_linkage hp (linkage_mul_of_linkable hp hq hc0 hcq hfa hfb hlink)

/-! ## 3. The four consequences of a link, at a multiplier -/

/-- **First consequence** `k' = pᵈ·k`: along a link the residues scale by `pᵈ`.  The `D = 1` case
is `BB13.link_resid`; here it is read off the collinearity through `BB13.sameLineMul_resid`. -/
@[category research solved, AMS 11 37, ref "Mah57" "Bug12", group "tshift_s2"]
theorem link_resid_mul {D p q : ℕ} {a d : ℕ} (hp : 0 < p)
    (hlink : (p : ℤ) ^ d * MnumMul (D : ℚ) p q a
      = (q : ℤ) ^ d * MnumMul (D : ℚ) p q (a + d)) :
    residMul D p q (a + d) = (p : ℤ) ^ d * residMul D p q a := by
  have h := sameLineMul_resid (D := D) hp (Nat.le_add_right a d) (sameLine_of_linkage hp hlink)
  simpa using h

/-- **Second consequence** `qᵈ ∣ m` (needs `gcd(p, q) = 1`): the `q`-adic surplus of the base of a
tower.  The `D = 1` case is `BB13.link_dvd`. -/
@[category research solved, AMS 11 37, ref "Mah57" "Bug12", group "tshift_s2"]
theorem link_dvd_mul {D p q : ℕ} {a d : ℕ} (hcop : Nat.Coprime p q)
    (hlink : (p : ℤ) ^ d * MnumMul (D : ℚ) p q a
      = (q : ℤ) ^ d * MnumMul (D : ℚ) p q (a + d)) :
    (q : ℤ) ^ d ∣ MnumMul (D : ℚ) p q a := by
  have hcopZ : IsCoprime (q : ℤ) (p : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]; exact (Nat.coprime_comm.mpr hcop)
  have hcopP : IsCoprime ((q : ℤ) ^ d) ((p : ℤ) ^ d) := hcopZ.pow
  have hdvd : (q : ℤ) ^ d ∣ (p : ℤ) ^ d * MnumMul (D : ℚ) p q a :=
    ⟨MnumMul (D : ℚ) p q (a + d), by rw [← hlink]⟩
  exact hcopP.dvd_of_dvd_mul_left hdvd

/-- **Third consequence** `m = qᵈ·μ`, `m' = pᵈ·μ`: the linked pair is the `pᵈ`-scaling of a single
reduced base `μ`.  The `D = 1` case is `BB13.link_scaling`. -/
@[category research solved, AMS 11 37, ref "Mah57" "Bug12", group "tshift_s2"]
theorem link_scaling_mul {D p q : ℕ} {a d : ℕ} (hq : 0 < q) (hcop : Nat.Coprime p q)
    (hlink : (p : ℤ) ^ d * MnumMul (D : ℚ) p q a
      = (q : ℤ) ^ d * MnumMul (D : ℚ) p q (a + d)) :
    ∃ μ : ℤ, MnumMul (D : ℚ) p q a = (q : ℤ) ^ d * μ
      ∧ MnumMul (D : ℚ) p q (a + d) = (p : ℤ) ^ d * μ := by
  obtain ⟨μ, hμ⟩ := link_dvd_mul hcop hlink
  refine ⟨μ, hμ, ?_⟩
  have hqd : (0 : ℤ) < (q : ℤ) ^ d := by
    have : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
    positivity
  have hcancel : (q : ℤ) ^ d * ((p : ℤ) ^ d * μ) = (q : ℤ) ^ d * MnumMul (D : ℚ) p q (a + d) := by
    rw [← hlink, hμ]; ring
  exact (mul_left_cancel₀ (ne_of_gt hqd) hcancel).symm

/-- **Fourth consequence: quality surplus.**  The base of a link has a residue a factor `pᵈ`
better than a generic failure: `pᵈ·|kₐ| < (c·q)ᵃ⁺ᵈ`.  The `D = 1` case is `BB13.link_quality`. -/
@[category research solved, AMS 11 37, ref "Mah57" "Bug12", group "tshift_s2"]
theorem link_quality_mul {D p q : ℕ} {c : ℝ} {a d : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hnd : IsFailureMul (D : ℚ) p q c (a + d))
    (hlink : (p : ℤ) ^ d * MnumMul (D : ℚ) p q a
      = (q : ℤ) ^ d * MnumMul (D : ℚ) p q (a + d)) :
    (p : ℝ) ^ d * |(residMul D p q a : ℝ)| < (c * q) ^ (a + d) := by
  have hk : residMul D p q (a + d) = (p : ℤ) ^ d * residMul D p q a := link_resid_mul hp hlink
  have h2 : (|residMul D p q (a + d)| : ℝ) < (c * (q : ℝ)) ^ (a + d) :=
    (isFailureMul_iff_residMul D p q c (a + d) hq).mp hnd
  have hcast : |(residMul D p q (a + d) : ℝ)| = (p : ℝ) ^ d * |(residMul D p q a : ℝ)| := by
    rw [hk]; push_cast
    rw [abs_mul, abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (p : ℝ))]
  rw [← hcast]
  rw [← Int.cast_abs]
  exact_mod_cast h2

/-! ## 4. Towers at a multiplier, and the free `O(log N)` count -/

/-- A **tower base at a multiplier**: a failure of `‖D(p/q)ⁿ‖ < cⁿ` not linked to any smaller
failure.  The `D = 1` case is `BB13.IsTowerBase`. -/
def IsTowerBaseMul (D p q : ℕ) (c : ℝ) (b : ℕ) : Prop :=
  IsFailureMul (D : ℚ) p q c b ∧ ∀ a, a < b → IsFailureMul (D : ℚ) p q c a → ¬ Linkable p c a b

/-- **The `O(log N)` tower count at a multiplier**, free of every Diophantine input — and free of
admissibility too: the non-linkage gap `BB13.gap_of_nonlink` mentions neither `q` nor `D`, so no
parity clause and no `AdmissibleMul` is needed.  Any finite set `S` of tower bases in `[1, N]`
has at most `t + (1 + logᵨ N)` elements, under the threshold relation
`log 2 ≤ t·(log(1/c) − (ρ−1)·log p)` (which forces `ρ < 1 + ε`, `ε = log(1/c)/log p`).

The `D = 1` case is `BB13.towerBases_card_le`. -/
@[category research solved, AMS 11 37, ref "Mah57" "Bug12", group "tshift_s2"]
theorem towerBasesMul_card_le {D : ℕ} (p q : ℕ) (c ρ : ℝ) (t N : ℕ)
    (hp1 : 1 < p) (hc0 : 0 < c) (ht1 : 1 ≤ t) (hρ1 : 1 < ρ)
    (hthr : Real.log 2 ≤ (t : ℝ) * (Real.log (1 / c) - (ρ - 1) * Real.log p))
    (S : Finset ℕ) (hbase : ∀ n ∈ S, IsTowerBaseMul D p q c n)
    (h1 : ∀ n ∈ S, 1 ≤ n) (hN : ∀ n ∈ S, n ≤ N) :
    (S.card : ℝ) ≤ t + (1 + Real.logb ρ N) := by
  refine card_le_logb_of_geomGap_above ρ hρ1 t N S h1 hN ?_
  intro a ha b hb hta hab
  have hfa : IsFailureMul (D : ℚ) p q c a := (hbase a ha).1
  have hnl : ¬ Linkable p c a b := (hbase b hb).2 a hab hfa
  rw [Linkable, not_le] at hnl
  exact gap_of_nonlink p c ρ a b t hp1 hc0 hab hta ht1 hnl hthr

/-- **Every failure sits over a tower base on its own line.**  Descending the linkage relation
from a failure `b` reaches a tower base `a ≤ b`, and — this is what `sameLine_of_linkage` buys —
every step of the descent stays on one line, so `a` and `b` are collinear.  The descent cannot
fall off the bottom: `0` is never linkable to anything (`2·p^b ≤ 1` fails). -/
@[category research solved, AMS 11 37, ref "Mah57" "Bug12", group "tshift_s2"]
theorem exists_isTowerBaseMul_sameLine {D p q : ℕ} {c : ℝ} (hp : 1 < p) (hq : 0 < q)
    (hc0 : 0 ≤ c) (hcq : c * q ≤ (p : ℝ)) :
    ∀ b, 1 ≤ b → IsFailureMul (D : ℚ) p q c b →
      ∃ a, 1 ≤ a ∧ a ≤ b ∧ IsTowerBaseMul D p q c a ∧
        linePointMul (D : ℚ) p q a = linePointMul (D : ℚ) p q b := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hb hfb
    by_cases hbase : IsTowerBaseMul D p q c b
    · exact ⟨b, hb, le_refl b, hbase, rfl⟩
    · have hex : ∃ a, a < b ∧ IsFailureMul (D : ℚ) p q c a ∧ Linkable p c a b := by
        by_contra hcon
        exact hbase ⟨hfb, fun a hab hfa hlink => hcon ⟨a, hab, hfa, hlink⟩⟩
      obtain ⟨a, hab, hfa, hlink⟩ := hex
      have ha1 : 1 ≤ a := by
        rcases Nat.eq_zero_or_pos a with rfl | hpos
        · exfalso
          have h0 : 2 * c ^ (0 : ℕ) * (p : ℝ) ^ (b - 0) ≤ 1 := hlink
          have hp1 : (1 : ℝ) ≤ (p : ℝ) ^ (b - 0) := by
            refine one_le_pow₀ ?_
            exact_mod_cast hp.le
          simp only [pow_zero, mul_one] at h0
          linarith
        · exact hpos
      have hcol := sameLine_of_linkable (Nat.zero_lt_of_lt hp) hq hc0 hcq hab hfa hfb hlink
      obtain ⟨a₀, h1, h2, h3, h4⟩ := ih a hab ha1 hfa
      exact ⟨a₀, h1, le_trans h2 hab.le, h3, h4.trans hcol⟩

/-! ## 5. The block shadow of the tower currency, and why it is vacuous -/

/-- The failures of `‖D(p/q)ⁿ‖ < cⁿ` at dates `≤ N`. -/
def failuresMulLe (D p q : ℕ) (c : ℝ) (N : ℕ) : Set ℕ :=
  {n : ℕ | n ∈ failuresMul D p q c ∧ n ≤ N}

/-- The dyadic blocks met by the failures at dates `≤ N` — the finite-range shadow of
`BB13.badBlocks`, which is the object an `O(log N)` currency can hope to bound. -/
def badBlocksLe (D p q : ℕ) (c : ℝ) (N : ℕ) : Set ℕ := blockIdx '' failuresMulLe D p q c N

@[category API, AMS 11 37, ref "Bug12", group "tshift_s2"]
theorem badBlocksLe_subset (D p q : ℕ) (c : ℝ) (N : ℕ) :
    badBlocksLe D p q c N ⊆ badBlocks D p q c := by
  rintro _ ⟨n, ⟨hn, -⟩, rfl⟩
  exact ⟨n, hn, rfl⟩

/-- **The trivial bound**: there are only `⌊log₂N⌋ + 1` dyadic blocks below `N` at all, bad or
good.  Any bound on `badBlocksLe` that exceeds this says nothing — which is the whole content of
the verdict below. -/
@[category API, AMS 11 37, ref "Bug12", group "tshift_s2"]
theorem badBlocksLe_card_le_log (D p q : ℕ) (c : ℝ) (N : ℕ) :
    (badBlocksLe D p q c N).ncard ≤ Nat.log 2 N + 1 := by
  have hsub : badBlocksLe D p q c N ⊆ ↑(Finset.range (Nat.log 2 N + 1)) := by
    rintro _ ⟨n, ⟨-, hnN⟩, rfl⟩
    simp only [Finset.coe_range, Set.mem_Iio, blockIdx]
    exact Nat.lt_succ_of_le (Nat.log_mono_right hnN)
  calc (badBlocksLe D p q c N).ncard
      ≤ (↑(Finset.range (Nat.log 2 N + 1)) : Set ℕ).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = Nat.log 2 N + 1 := by rw [Set.ncard_coe_finset, Finset.card_range]

/-- **The tower currency in block coin.**  Every failure `≤ N` lies on the line of a tower base
`≤ N`, and a line-fibre with least element `a` is confined to `[a, 2^t·a]` when `2^t·f_∞ ≥ 1`,
hence to `t + 1` blocks.  So the blocks met by the failures below `N` number at most
`(t + 1)·#{tower bases ≤ N}` — with **no cited axiom**, in exchange for a bound that grows with
`N`.

`S` is any finite set of dates containing every tower base in `[1, N]`. -/
@[category research solved, AMS 11 37, ref "Mah57" "Bug12", group "tshift_s2"]
theorem ncard_badBlocksLe_le_tower {D p q : ℕ} {c : ℝ} {N t : ℕ} (hq : 1 < q) (hqp : q < p)
    (hadm : AdmissibleMul D p q) (hc0 : 0 < c) (hc1 : c < 1)
    (ht : (1 : ℝ) ≤ 2 ^ t * fArch p q c)
    (S : Finset ℕ) (hS : ∀ a, 1 ≤ a → a ≤ N → IsTowerBaseMul D p q c a → a ∈ S) :
    (badBlocksLe D p q c N).ncard ≤ (t + 1) * S.card := by
  classical
  have hp : 1 < p := lt_trans hq hqp
  have hq0R : (0 : ℝ) < (q : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hq
  have hqpR : (q : ℝ) ≤ (p : ℝ) := by exact_mod_cast hqp.le
  have hcqlt : c * (q : ℝ) < (p : ℝ) := by nlinarith
  have hF : 0 < fArch p q c := fArch_pos hp (by omega) hc0 hcqlt
  have hsub : badBlocksLe D p q c N ⊆
      ↑(S.biUnion (fun a => Finset.Icc (blockIdx a) (blockIdx a + t))) := by
    rintro _ ⟨n, ⟨⟨hn1, hfn⟩, hnN⟩, rfl⟩
    obtain ⟨a, ha1, han, hbase, hline⟩ :=
      exists_isTowerBaseMul_sameLine (D := D) hp (by omega) hc0.le hcqlt.le n hn1 hfn
    have haS : a ∈ S := hS a ha1 (le_trans han hnN) hbase
    have hlo : blockIdx a ≤ blockIdx n := Nat.log_mono_right han
    have hhi : blockIdx n ≤ blockIdx a + t := by
      rcases eq_or_lt_of_le han with heq | hlt
      · rw [← heq]; omega
      · have hconf := sameLineMul_lt_div_fArch hp hq hqp hadm hc0 hc1 ha1 hlt hfn hline
        have haR : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
        have hle : (a : ℝ) / fArch p q c ≤ 2 ^ t * (a : ℝ) := by
          rw [div_le_iff₀ hF]
          nlinarith [mul_le_mul_of_nonneg_left ht haR]
        have hnR : (n : ℝ) < ((2 ^ t * a : ℕ) : ℝ) := by push_cast; linarith
        have hnN' : n ≤ 2 ^ t * a := by exact_mod_cast hnR.le
        exact blockIdx_le_of_le_mul hnN'
    exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨a, haS, Finset.mem_Icc.mpr ⟨hlo, hhi⟩⟩)
  calc (badBlocksLe D p q c N).ncard
      ≤ (↑(S.biUnion (fun a => Finset.Icc (blockIdx a) (blockIdx a + t))) : Set ℕ).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (S.biUnion (fun a => Finset.Icc (blockIdx a) (blockIdx a + t))).card :=
        Set.ncard_coe_finset _
    _ ≤ ∑ a ∈ S, (Finset.Icc (blockIdx a) (blockIdx a + t)).card := Finset.card_biUnion_le
    _ = ∑ _a ∈ S, (t + 1) := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Nat.card_Icc]; omega
    _ = S.card * (t + 1) := by rw [Finset.sum_const, smul_eq_mul]
    _ = (t + 1) * S.card := Nat.mul_comm _ _

end BB13

/-! # At base `3/2`, rate `3/4`: the free tower count and the verdict -/

namespace TShift

open scoped Real

/-! ## 6. The showcase instance, with no decimal logarithm bounds -/

/-- **The free tower count at `‖D(3/2)ⁿ‖ < (3/4)ⁿ`, every multiplier.**  Any finite set `S` of
tower bases in `[1, N]` has at most `11 + (1 + log_{6/5} N) ≈ 12 + 5.49·ln N` elements.

Unlike `BB13.towerBases_card_le_three_halves`, which carries `log 2 ≥ 0.6931` and
`log 3 ≤ 1.0987` as hypotheses, this instance needs no decimal logarithm bounds: at `ρ = 6/5` and
`t = 11` the threshold relation is `(66/5)·log 3 ≤ 21·log 2`, i.e. the integer inequality
`3⁶⁶ ≤ 2¹⁰⁵` (`3.09·10³¹ ≤ 4.06·10³¹`).  The sharp ratio is `1 + ε* = 1.26186…`, giving
`4.30·ln N` towers as `t → ∞`. -/
@[category research solved, AMS 11 37, ref "Mah57" "Bug12", group "tshift_s2"]
theorem towerBasesMul_card_le_three_halves {D : ℕ} (N : ℕ) (S : Finset ℕ)
    (hbase : ∀ n ∈ S, BB13.IsTowerBaseMul D 3 2 (3 / 4) n)
    (h1 : ∀ n ∈ S, 1 ≤ n) (hN : ∀ n ∈ S, n ≤ N) :
    (S.card : ℝ) ≤ 11 + (1 + Real.logb (6 / 5) N) := by
  refine BB13.towerBasesMul_card_le (D := D) 3 2 (3 / 4) (6 / 5) 11 N (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ?_ S hbase h1 hN
  have hlog43 : Real.log (1 / (3 / 4 : ℝ)) = 2 * Real.log 2 - Real.log 3 := by
    rw [show (1 / (3 / 4 : ℝ)) = 4 / 3 by norm_num, Real.log_div (by norm_num) (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  have hkey : (66 : ℝ) * Real.log 3 ≤ 105 * Real.log 2 := by
    have h1 : Real.log ((3 : ℝ) ^ (66 : ℕ)) ≤ Real.log ((2 : ℝ) ^ (105 : ℕ)) :=
      Real.log_le_log (by positivity) (by norm_num)
    rw [Real.log_pow, Real.log_pow] at h1
    push_cast at h1
    linarith
  rw [hlog43, show ((3 : ℕ) : ℝ) = 3 by norm_num]
  linarith

/-- **The tower currency in block coin, at the showcase.**  For every odd multiplier `D`, the
dyadic blocks met by the failures of `‖D(3/2)ⁿ‖ < (3/4)ⁿ` at dates `≤ N` number at most
`2·(12 + log_{6/5} N) = 24 + 10.97·ln N` — unconditionally, with footprint `std3`: no cited
axiom, no line cover, no height threshold.

Compare Theorem A (`TShift.badBlocks_card_le_five_decimal`): `3 720 000 000 004` blocks, for
*all* `N` at once, but on `BugeaudEvertse.ridout_line_cover`.  See
`tower_bound_not_below_trivial` for why the trade is a bad one. -/
@[category research solved, AMS 11 37, ref "Mah57" "Bug12", group "tshift_s2"]
theorem badBlocksLe_three_two_card_le_tower {D : ℕ} (hD : Odd D) (N : ℕ) :
    ((BB13.badBlocksLe D 3 2 (3 / 4) N).ncard : ℝ) ≤ 2 * (11 + (1 + Real.logb (6 / 5) N)) := by
  classical
  obtain ⟨S, hcomplete, hmem⟩ : ∃ S : Finset ℕ,
      (∀ a, 1 ≤ a → a ≤ N → BB13.IsTowerBaseMul D 3 2 (3 / 4) a → a ∈ S) ∧
      (∀ n ∈ S, (1 ≤ n ∧ n ≤ N) ∧ BB13.IsTowerBaseMul D 3 2 (3 / 4) n) := by
    refine ⟨(Finset.Icc 1 N).filter (fun a => BB13.IsTowerBaseMul D 3 2 (3 / 4) a), ?_, ?_⟩
    · intro a h1 h2 h3
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨h1, h2⟩, h3⟩
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn
      exact ⟨hn.1, hn.2⟩
  have hcard : (BB13.badBlocksLe D 3 2 (3 / 4) N).ncard ≤ 2 * S.card := by
    have h := BB13.ncard_badBlocksLe_le_tower (D := D) (p := 3) (q := 2) (c := 3 / 4) (N := N)
      (t := 1) (by norm_num) (by norm_num) (admissibleMul_three_two hD) (by norm_num)
      (by norm_num) BB13.one_le_two_pow_one_mul_fArch S hcomplete
    simpa using h
  have hS' : (S.card : ℝ) ≤ 11 + (1 + Real.logb (6 / 5) N) :=
    towerBasesMul_card_le_three_halves N S (fun n hn => (hmem n hn).2)
      (fun n hn => (hmem n hn).1.1) (fun n hn => (hmem n hn).1.2)
  calc ((BB13.badBlocksLe D 3 2 (3 / 4) N).ncard : ℝ) ≤ ((2 * S.card : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ = 2 * (S.card : ℝ) := by push_cast; ring
    _ ≤ 2 * (11 + (1 + Real.logb (6 / 5) N)) := by linarith

/-- **The verdict on the currency swap (WP5(a), outgoing angle O‑6).**  The tower-derived block
bound `2·(11 + 1 + log_{6/5} N)` is never smaller than `⌊log₂N⌋ + 1`, the number of dyadic blocks
below `N` *in total* (`BB13.badBlocksLe_card_le_log`).  So the free `O(log N)` tower currency
cannot establish that any block below `N` is good, at any rate `c` and any multiplier: blocks
below `N` are themselves only logarithmically many, and only a line count bounded independently
of `N` — the Ridout cover, i.e. the cited axiom — can beat that.

The elementary gap principle therefore *cannot* replace `b_ℓ·K(ε)` in Theorem A.  What it does
give on its own terms is a statement about dates, not blocks:
`towerBasesMul_card_le_three_halves`. -/
@[category research solved, AMS 11 37, ref "BE08" "Bug12", group "tshift_s2"]
theorem tower_bound_not_below_trivial (N : ℕ) :
    ((Nat.log 2 N : ℝ) + 1) ≤ 2 * (11 + (1 + Real.logb (6 / 5) N)) := by
  have hnat : (Nat.log 2 N : ℝ) ≤ Real.logb 2 N := Real.natLog_le_logb N 2
  have hlog65 : (0 : ℝ) < Real.log (6 / 5) := Real.log_pos (by norm_num)
  have hle : Real.log (6 / 5) ≤ Real.log 2 := Real.log_le_log (by norm_num) (by norm_num)
  have hlogN : (0 : ℝ) ≤ Real.log N := by
    rcases Nat.eq_zero_or_pos N with rfl | h
    · simp
    · exact Real.log_nonneg (by exact_mod_cast h)
  have hcmp : Real.logb 2 N ≤ Real.logb (6 / 5) N := by
    rw [Real.logb, Real.logb]
    gcongr
  have hpos : (0 : ℝ) ≤ Real.logb (6 / 5) N := by
    rw [Real.logb]; positivity
  linarith

/-! ## 7. WP5(b): the uniform-in-period package -/

/-- The bad blocks of one cycle denominator form a finite set — so the counts below are not
vacuous readings of `Set.ncard`. -/
@[category API, AMS 11 37, ref "Mah57" "BE08" "A6plus", group "tshift_s2"]
theorem badBlocks_cycleDenom_finite {p : ℕ} (hp : 1 ≤ p) :
    (BB13.badBlocks (Z32.cycleDenom p) 3 2 (3 / 4)).Finite :=
  (failuresMul_cycleDenom_finite hp (by norm_num) (by norm_num)).image _

/-- **The uniform-in-period package, as a sum.**  `D_p = 3^p − 2^p` enters `B(θ, D_p)` only
through the threshold `max 10 (p+1)`, so summing Theorem A over all periods `p ≤ P` is a
summation:

`∑_{p ≤ P} B(3/4, D_p) ≤ P·(2K(ε*) + ⌊log₂ max(10, P+1)⌋ + 1)`,

entirely effective.  This is D2's uniformity remark, machine-checked. -/
@[category research solved, AMS 11 37, ref "Mah57" "BE08" "A6plus", group "tshift_s2"]
theorem badBlocks_cycleDenom_sum_card_le (P : ℕ) :
    ∑ p ∈ Finset.Icc 1 P, (BB13.badBlocks (Z32.cycleDenom p) 3 2 (3 / 4)).ncard
      ≤ P * (BugeaudEvertse.lineBound BB13.epsStar * 2
          + (Nat.log 2 (max 10 (P + 1)) + 1)) := by
  have hterm : ∀ p ∈ Finset.Icc 1 P,
      (BB13.badBlocks (Z32.cycleDenom p) 3 2 (3 / 4)).ncard
        ≤ BugeaudEvertse.lineBound BB13.epsStar * 2 + (Nat.log 2 (max 10 (P + 1)) + 1) := by
    intro p hp
    rw [Finset.mem_Icc] at hp
    refine le_trans (badBlocks_cycleDenom_card_le hp.1) ?_
    have hmono : Nat.log 2 (max 10 (p + 1)) ≤ Nat.log 2 (max 10 (P + 1)) :=
      Nat.log_mono_right (max_le_max (le_refl 10) (by omega))
    omega
  calc ∑ p ∈ Finset.Icc 1 P, (BB13.badBlocks (Z32.cycleDenom p) 3 2 (3 / 4)).ncard
      ≤ ∑ _p ∈ Finset.Icc 1 P,
          (BugeaudEvertse.lineBound BB13.epsStar * 2 + (Nat.log 2 (max 10 (P + 1)) + 1)) :=
        Finset.sum_le_sum hterm
    _ = (Finset.Icc 1 P).card
          * (BugeaudEvertse.lineBound BB13.epsStar * 2 + (Nat.log 2 (max 10 (P + 1)) + 1)) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = P * (BugeaudEvertse.lineBound BB13.epsStar * 2
          + (Nat.log 2 (max 10 (P + 1)) + 1)) := by rw [Nat.card_Icc, Nat.add_sub_cancel]

/-- **The union form** — the one the escape accounting of the plan's D3 consumes: the dyadic
blocks that are bad for *some* period `p ≤ P` number at most
`P·(2K(ε*) + ⌊log₂ max(10, P+1)⌋ + 1)`. -/
@[category research solved, AMS 11 37, ref "Mah57" "BE08" "A6plus", group "tshift_s2"]
theorem badBlocks_cycleDenom_biUnion_card_le (P : ℕ) :
    (⋃ p ∈ Finset.Icc 1 P, BB13.badBlocks (Z32.cycleDenom p) 3 2 (3 / 4)).ncard
      ≤ P * (BugeaudEvertse.lineBound BB13.epsStar * 2
          + (Nat.log 2 (max 10 (P + 1)) + 1)) :=
  le_trans (Set.ncard_biUnion_le _ _) (badBlocks_cycleDenom_sum_card_le P)

/-- The union is finite, so the bound above is a genuine count. -/
@[category API, AMS 11 37, ref "Mah57" "BE08" "A6plus", group "tshift_s2"]
theorem badBlocks_cycleDenom_biUnion_finite (P : ℕ) :
    (⋃ p ∈ Finset.Icc 1 P, BB13.badBlocks (Z32.cycleDenom p) 3 2 (3 / 4)).Finite := by
  refine Set.Finite.biUnion (Finset.finite_toSet _) (fun p hp => ?_)
  rw [Finset.mem_coe, Finset.mem_Icc] at hp
  exact badBlocks_cycleDenom_finite hp.1

/-- **The uniform-in-period package in decimals**: at most
`P·(3 720 000 000 000 + ⌊log₂ max(10, P+1)⌋ + 1)` dyadic blocks are bad for some period `p ≤ P`,
on the certified `K(ε*) ≤ 1.86·10¹²` and nothing else new. -/
@[category research solved, AMS 11 37, ref "Mah57" "BE08" "A6plus", group "tshift_s2"]
theorem badBlocks_cycleDenom_biUnion_card_le_decimal (P : ℕ) :
    (⋃ p ∈ Finset.Icc 1 P, BB13.badBlocks (Z32.cycleDenom p) 3 2 (3 / 4)).ncard
      ≤ P * (3720000000000 + (Nat.log 2 (max 10 (P + 1)) + 1)) := by
  refine le_trans (badBlocks_cycleDenom_biUnion_card_le P) ?_
  have h := BB13.lineBound_epsStar_le
  exact Nat.mul_le_mul_left _ (by omega)

end TShift
