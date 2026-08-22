/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.TwoLogCap
import BB13.ValuationArm

/-!
# Digit blocks of `3ᵃ`: the Delmer–Deshouillers dictionary (strategy B7)

Strategy **B7** of `plans/report3-BB13.html` asks to

> formalize the window dynamics of `×3` as a finite transducer; **milestone 1: reprove a
> Delmer–Deshouillers run bound transducer-style**; milestone 2: run the transducer only in the
> window straddling bit `a`; milestone 3: a *repulsion* lemma at fibre tops.

This file executes the item.  Milestone 1 is delivered twice — [DD90] Prop. 1 with both of its
constants, and [DD90] Prop. 4, the unconditional `o(m)` run bound — and the programme is then
priced: the digit layer is an **exact dictionary** onto objects the root already has, and the one
place where it is strictly stronger than the rate layer is already spent by `BB13/ValuationArm`.

## 1. The block predicate

`cres N w` is the distance from `N` to the nearest multiple of `2^w` (the root's `residNat n` is
its diagonal, `cres (3ⁿ) n`), and

`IsBlock N lo hi  :=  2^hi ≤ 2N ∧ cres N hi < 2^lo`

says the binary digits of `N` are **constant on the positions `lo ≤ i < hi`**, with the block
inside the word.  Everything about digits is done through `cres`; no `testBit` bookkeeping is
needed, because the two facts that carry the whole subject are

* `cres_mul_le` :  `cres (cN) w ≤ c·cres N w`  — the transducer step, and
* `isBlock_mono` — sub-blocks of a block are blocks.

## 2. The transducer step is one line, and it is [DD90] Prop. 1

The `×3` transducer on binary words (state = previous digit and carry, four states) maps a
constant block to a constant block, losing `log₂3` positions at the bottom per multiplication.
Algebraically that is `|3(N − ν2^w)| = 3|N − ν2^w|`, i.e. `cres_mul_le`, and iterated
(`block_pow_mul`) it gives `dd_prop_one`: an exception at `k` puts a constant block of length
`2k − m·log₂3` into `3ᵐ` for every `m ≥ k`.  In integer form, through `3⁴¹ ≤ 2⁶⁵`,

`dd_prop_one_contra` :  no block of `h` equal digits in `3ᵐ` ⟹ no exception `k` with
`65m + 41h + 41 ≤ 82k ≤ 82m`,

which is [DD90] Prop. 1 — `k > m·log3/log4 + h/2 + 1/2` — with **both constants reproduced**
(`65/82 = 0.79268` against `log3/log4 = 0.79248`, and the `h/2` and the `1/2` exactly).  So
milestone 1's "reprove a DD run bound transducer-style" is achieved in the strict sense: their
criterion is a one-line consequence of the block calculus, with no analysis anywhere.

## 3. The dictionary, and why the run is `0.415a + D + v₂` and not `0.415a + 2d`

`block_of_arms`: the `D` arm (`2ᴰ|kₐ|2ᵃ ≤ 3ᵃ`) is the **bottom** end of the block at `a` and the
`v` arm (`2ᵛ ∣ mₐ`) is its **top** end.  The maximal constant block straddling bit `a` therefore
has length `0.4146a + D(a) + v₂(mₐ)` (`arms_block_length`, exact in the integer form
`41u + 41D ≤ 24a + 41`), where the report's §1.3 records only the guaranteed part `0.415a + 2(H−1)`
with `H − 1 = min(D, v₂)`.  Consequently

* a bound on the run **below** bit `a` — which is what every rate theorem is
  (`‖(3/2)ᵃ‖ ≥ cᵃ` says exactly "the block below bit `a` is no longer than `(1 − log₂2c)a`") —
  sees `D` alone;
* a bound on the run **straddling** bit `a` sees `D + v₂`, and `min ≤ (D+v₂)/2`: a factor `2`.

That factor is the `h/2` of [DD90] Prop. 1, and it is the entire quantitative content of
milestone 2.  It is also already spent: the only bound on `v₂` is `BB13.vTwo_isLittleO`
(`v₂ = o(a)`, ineffective), which caps `min` by `o(a)` on its own.

## 4. Pricing: what a run bound is worth (§5 below)

`sum_of_run_bound` converts *any* global run bound `length ≤ (P/Q)·a + C/Q` into

`17Qa + 41Q(D + v) ≤ 41Pa + 41Q + 41C`,  i.e.  `D + v₂ ≤ (c − 0.4146)a`,  `min ≤ (c − 0.4146)a/2`.

The calibrations are exact and they identify every row of the report's §1.4 table:

| run bound `c` | gives `min ≤` | status |
| --- | --- | --- |
| `log₂3 = 1.58496` (the word itself, `run_bound_trivial`) | `0.5854a` | = the elementary row |
| `1.1549` | `0.3701a` | = [Zud07]'s row — **any effective global run bound below `1.155` beats the 19-year record** |
| `0.4146` (`no_exception_of_run_bound`) | — | `ℰ` finite, effectively |
| `o(a)` ([DD90] Prop. 4, `longBlock_finite`) | — | `ℰ` finite, ineffectively |

There is no regime in between: the global run problem is not a softer neighbour of the rate
problem, it is a *harder* one, and the published digit results are its ineffective end.

## 5. [DD90] Prop. 4 formalized: `longBlock_finite`

For every `ε > 0`, only finitely many `n` have a constant block of length `≥ εn` anywhere in `3ⁿ`.
The proof is the source's: cover the word by `q ≈ 3/ε` overlapping windows `[pn/q, (p+2)n/q)`;
a block containing one of them is a Ridout solution at

`(f∞, f₂, f₃) = (1 − θp/q, θ(p+2)/q, 1)`,  budget `2 + 2θ/q` **exactly**,

and a fixed slope carries finitely many `n` because `|1 − x/y| < 2^{1−L} ≤ 2^{1−εn}` while
`x` is even and `y = 3ⁿ` is odd.  This is the same engine as `BB13.valuation_arm_finite`, run on
a different frame, and it is **ineffective for the same reason**.

Two consequences worth recording.  (i) `longBlock_finite` *implies* the finiteness of `ℰ`
(an exception has a block of length `≥ 0.4146a`), so [DD90] Prop. 4 is not a lever under
Problem 2 — it is Mahler's theorem in digit clothing.  (ii) It is uniform in the multiplier: a
block at `[u, m)` of `3ᵃ` with `m ≤ a` is `‖3^{a−m}(3/2)ᵐ‖ ≤ 2^{u−m}`, so Prop. 4 is the
`T`-shift statement of the `TShift/` root for **all** multipliers `3ʲ` at once — ineffectively,
and in print since 1990.

## 6. Milestone 3: there is no repulsion, there is persistence

`block_pow_mul` runs forwards (`exception_block_persists`): the block of an exception at `a`
survives in `3^{a+j}` for every `j`, eroding by `log₂3` positions per step, and the "failure bit"
at the top of a fibre destroys nothing.  Read on the other side, `dd_prop_one` says an exception at
`k` **contaminates every index up to `82k/65 = 1.2615k`** — the tower ratio `log4/log3 = 1.26186`
again — so indices carrying long blocks come in intervals; they do not repel.  The only repulsion
the block calculus can produce is the merge argument (two overlapping blocks are one block, and the
lower block cannot reach below the maximal one), and its conclusion `a' + D(a') ≥ a + D(a)` is the
line-scaling law `k_b = 3ᵈkₐ` — already in the root as `BB13.link_scaling` and
`BB13.corridor_candidate_unique` — which improves the inter-line gap `a' ≥ 1.2384a`
(`BB13.gap_of_nonlink`) only in the corner `D(a) − D(a') > 0.2384a`.  No `g(H) = 2^{cH}` repulsion
exists here, and nothing new is formalized for it.

## Trust ledger

Footprint `std3` for 26 of the 27 declarations; **exactly one**, `longBlock_finite`, carries the
root's cited Ridout axiom `BugeaudEvertse.ridout_line_cover` (via `ridout_line_cover_23`) — the
same and only cited input as `BB13/ValuationArm.lean`.  No `sorry`.  [DD90]'s propositions are *reproved*, not
axiomatized; [Zud07]'s and [Hab03]'s rates never appear, since the pricing theorems take the run
bound as an explicit hypothesis.

## Claim level

`cres_mul_le`, `block_pow_mul`, `isBlock_mono`, `block_of_arms`, `arms_block_length`,
`dd_prop_one`, `dd_prop_one_contra`, `exception_block_persists`, `run_bound_trivial`,
`elementary_row_from_runs` and `longBlock_finite` are unconditional.  `sum_of_run_bound`,
`fibre_of_run_bound`, `no_exception_of_run_bound` and `run_bound_beats_zudilin` are conditional on
their stated run-bound hypothesis, which no source supplies.

## References

* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, Cambridge Tracts
  in Mathematics **193**, 2012 (Problem 10.13).
* [DD90] F. Delmer, J.-M. Deshouillers, *On the computation of `g(k)` in Waring's problem*,
  Math. Comp. **54** (1990), 885–893 — §3.1 Prop. 1, §3.3 Prop. 4, and the closing remark that
  the longest block should be `O(log m)`.
* [BE08] Y. Bugeaud, J.-H. Evertse, *On two notions of complexity of algebraic numbers*, Acta
  Arith. **133** (2008), 221–250 (Cor. 5.2 — the cited axiom).
* [Hab03] L. Habsieger, *Explicit lower bounds for `‖(3/2)ᵏ‖`*, Acta Arith. **106** (2003).
* [Zud07] W. Zudilin, *A new lower bound for `‖(3/2)ᵏ‖`*, J. Théor. Nombres Bordeaux **19**
  (2007), 311–323.
-/

namespace BB13

open scoped Real

/-! ## 1. Blocks of equal binary digits

`cres N w` is the *centred* residue: the distance from `N` to the nearest multiple of `2^w`.  The
predicate `IsBlock N lo hi` says the digits of `N` on `[lo, hi)` are constant. -/

/-- The **centred residue** of `N` modulo `2^w`.  `BB13.residNat n = cres (3ⁿ) n`. -/
def cres (N w : ℕ) : ℕ := min (N % 2 ^ w) (2 ^ w - N % 2 ^ w)

@[category API, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem residNat_eq_cres (n : ℕ) : residNat n = cres (3 ^ n) n := rfl

/-- The centred residue, cast to `ℤ`. -/
@[category API, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem cres_cast (N w : ℕ) :
    ((cres N w : ℕ) : ℤ) = min ((N : ℤ) % 2 ^ w) (2 ^ w - (N : ℤ) % 2 ^ w) := by
  have hmodlt : N % 2 ^ w < 2 ^ w := Nat.mod_lt _ (by positivity)
  unfold cres
  rw [Nat.cast_min, Nat.cast_sub (le_of_lt hmodlt)]
  push_cast
  ring_nf

/-- `cres N w` is the minimum of `|N − ν2^w|` over integers `ν`: it is a lower bound for each. -/
@[category API, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem cres_le_abs (N w : ℕ) (ν : ℤ) : (cres N w : ℤ) ≤ |(N : ℤ) - ν * 2 ^ w| := by
  have hw : (0 : ℤ) < 2 ^ w := by positivity
  have hr0 : 0 ≤ (N : ℤ) % 2 ^ w := Int.emod_nonneg _ (by positivity)
  have hrlt : (N : ℤ) % 2 ^ w < 2 ^ w := Int.emod_lt_of_pos _ hw
  have hdm : (N : ℤ) = ((N : ℤ) / 2 ^ w) * 2 ^ w + (N : ℤ) % 2 ^ w := by
    rw [Int.emod_def]; ring
  have hval : (N : ℤ) - ν * 2 ^ w
      = (((N : ℤ) / 2 ^ w) - ν) * 2 ^ w + (N : ℤ) % 2 ^ w := by
    nth_rewrite 1 [hdm]; ring
  rw [hval, cres_cast]
  rcases lt_trichotomy ((N : ℤ) / 2 ^ w - ν) 0 with h | h | h
  · have ht1 : (N : ℤ) / 2 ^ w - ν ≤ -1 := by omega
    have h1 : ((N : ℤ) / 2 ^ w - ν) * 2 ^ w ≤ -1 * 2 ^ w :=
      mul_le_mul_of_nonneg_right ht1 (le_of_lt hw)
    rw [abs_of_nonpos (by linarith)]
    exact le_trans (min_le_right _ _) (by linarith)
  · rw [h, zero_mul, zero_add, abs_of_nonneg hr0]
    exact min_le_left _ _
  · have ht1 : 1 ≤ (N : ℤ) / 2 ^ w - ν := h
    have h1 : 1 * 2 ^ w ≤ ((N : ℤ) / 2 ^ w - ν) * 2 ^ w :=
      mul_le_mul_of_nonneg_right ht1 (le_of_lt hw)
    rw [abs_of_nonneg (by linarith)]
    exact le_trans (min_le_right _ _) (by linarith)

/-- ... and it is attained. -/
@[category API, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem cres_spec (N w : ℕ) : ∃ ν : ℤ, |(N : ℤ) - ν * 2 ^ w| = (cres N w : ℤ) := by
  have hw : (0 : ℤ) < 2 ^ w := by positivity
  have hr0 : 0 ≤ (N : ℤ) % 2 ^ w := Int.emod_nonneg _ (by positivity)
  have hrlt : (N : ℤ) % 2 ^ w < 2 ^ w := Int.emod_lt_of_pos _ hw
  have hdm : (N : ℤ) = ((N : ℤ) / 2 ^ w) * 2 ^ w + (N : ℤ) % 2 ^ w := by
    rw [Int.emod_def]; ring
  rcases le_total ((N : ℤ) % 2 ^ w) (2 ^ w - (N : ℤ) % 2 ^ w) with h | h
  · refine ⟨(N : ℤ) / 2 ^ w, ?_⟩
    rw [cres_cast, min_eq_left h,
      show (N : ℤ) - ((N : ℤ) / 2 ^ w) * 2 ^ w = (N : ℤ) % 2 ^ w by nth_rewrite 1 [hdm]; ring]
    exact abs_of_nonneg hr0
  · refine ⟨(N : ℤ) / 2 ^ w + 1, ?_⟩
    rw [cres_cast, min_eq_right h,
      show (N : ℤ) - ((N : ℤ) / 2 ^ w + 1) * 2 ^ w = (N : ℤ) % 2 ^ w - 2 ^ w by
        nth_rewrite 1 [hdm]; ring]
    rw [abs_of_nonpos (by linarith)]
    ring

/-- **The transducer step.**  Multiplying by `c` multiplies the distance to the nearest multiple
of `2^w` by at most `c`: `cres (cN) w ≤ c·cres N w`.  This one inequality is the whole carry
analysis — the four-state `×3` transducer maps a constant block to a constant block, and the
`log₂3` positions it eats at the bottom are the factor `3` here. -/
@[category research solved, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem cres_mul_le (c N w : ℕ) : cres (c * N) w ≤ c * cres N w := by
  obtain ⟨ν, hν⟩ := cres_spec N w
  have h := cres_le_abs (c * N) w ((c : ℤ) * ν)
  have heq : |((c * N : ℕ) : ℤ) - (c : ℤ) * ν * 2 ^ w| = (c : ℤ) * (cres N w : ℤ) := by
    have : ((c * N : ℕ) : ℤ) - (c : ℤ) * ν * 2 ^ w = (c : ℤ) * ((N : ℤ) - ν * 2 ^ w) := by
      push_cast; ring
    rw [this, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (c : ℤ)), hν]
  rw [heq] at h
  exact_mod_cast h

/-- `IsBlock N lo hi`: the binary digits of `N` are **constant on the positions `lo ≤ i < hi`**,
with the top of the block inside the word (`2^hi ≤ 2N`, i.e. `hi` is at most one position above
the leading bit).  Equivalently `N mod 2^hi < 2^lo` (a block of zeros) or
`N mod 2^hi > 2^hi − 2^lo` (a block of ones); the one residue `N mod 2^hi = 2^hi − 2^lo`, an
all-ones block with nothing below it, is excluded by the strict inequality, which only makes the
hypotheses of §5 weaker. -/
def IsBlock (N lo hi : ℕ) : Prop := 2 ^ hi ≤ 2 * N ∧ cres N hi < 2 ^ lo

/-- A sub-block of a block is a block. -/
@[category API, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem isBlock_mono {N lo hi lo' hi' : ℕ} (h : IsBlock N lo hi) (hlo : lo ≤ lo')
    (hhi : hi' ≤ hi) : IsBlock N lo' hi' := by
  obtain ⟨hword, hc⟩ := h
  refine ⟨le_trans (Nat.pow_le_pow_right (by norm_num) hhi) hword, ?_⟩
  obtain ⟨ν, hν⟩ := cres_spec N hi
  have hsplit : (2 : ℤ) ^ hi = 2 ^ hi' * 2 ^ (hi - hi') := by
    rw [← pow_add]
    congr 1
    omega
  have hle := cres_le_abs N hi' (ν * 2 ^ (hi - hi'))
  have heq : (N : ℤ) - ν * 2 ^ (hi - hi') * 2 ^ hi' = (N : ℤ) - ν * 2 ^ hi := by
    rw [hsplit]; ring
  rw [heq, hν] at hle
  have h1 : (cres N hi' : ℤ) < 2 ^ lo := lt_of_le_of_lt hle (by exact_mod_cast hc)
  have h2 : (cres N hi' : ℤ) < 2 ^ lo' :=
    lt_of_lt_of_le h1 (by exact_mod_cast Nat.pow_le_pow_right (by norm_num) hlo)
  exact_mod_cast h2

/-- **Persistence.**  A constant block of `N` on `[lo, hi)` gives a constant block of `3ʲN` on
`[lo + t, hi)` whenever `3ʲ ≤ 2ᵗ`: the block survives multiplication by `3ʲ`, eroding
`⌈j·log₂3⌉` positions at the bottom and none at the top. -/
@[category research solved, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem block_pow_mul {N lo hi j t : ℕ} (h : IsBlock N lo hi) (ht : 3 ^ j ≤ 2 ^ t) :
    IsBlock (3 ^ j * N) (lo + t) hi := by
  obtain ⟨hword, hc⟩ := h
  refine ⟨le_trans hword ?_, ?_⟩
  · exact Nat.mul_le_mul_left 2 (Nat.le_mul_of_pos_left _ (by positivity))
  · calc cres (3 ^ j * N) hi ≤ 3 ^ j * cres N hi := cres_mul_le _ _ _
      _ < 3 ^ j * 2 ^ lo := mul_lt_mul_of_pos_left hc (by positivity)
      _ ≤ 2 ^ t * 2 ^ lo := Nat.mul_le_mul_right _ ht
      _ = 2 ^ (lo + t) := by rw [← pow_add]; ring_nf

/-! ## 2. The dictionary: the two arms are the two ends of one block -/

/-- **The `D` arm caps the depth.**  From `2ᴰ|kₐ|2ᵃ ≤ 3ᵃ` and `kₐ ≠ 0`: `41(D + a) ≤ 65a`, i.e.
`D ≤ 0.5854a`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem depth_le_of_arm {a D : ℕ} (ha : 1 ≤ a)
    (hD : 2 ^ D * (resid 3 2 a).natAbs * 2 ^ a ≤ 3 ^ a) : 41 * D + 41 * a ≤ 65 * a := by
  have hk : 1 ≤ (resid 3 2 a).natAbs := resid_natAbs_pos ha
  have h1 : 2 ^ (D + a) ≤ 3 ^ a := by
    calc 2 ^ (D + a) = 2 ^ D * 1 * 2 ^ a := by rw [pow_add]; ring
      _ ≤ 2 ^ D * (resid 3 2 a).natAbs * 2 ^ a := by
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hk)
      _ ≤ 3 ^ a := hD
  have h2 : 2 ^ (41 * (D + a)) ≤ 2 ^ (65 * a) := by
    calc 2 ^ (41 * (D + a)) = (2 ^ (D + a)) ^ 41 := by rw [← pow_mul, Nat.mul_comm]
      _ ≤ (3 ^ a) ^ 41 := Nat.pow_le_pow_left h1 41
      _ = 3 ^ (41 * a) := by rw [← pow_mul, Nat.mul_comm]
      _ ≤ 2 ^ (65 * a) := three_pow_le_two_pow a
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2
  omega

/-- **The two arms are the two ends of one digit block.**  If `2ᵛ ∣ mₐ` (the `v` arm) and
`2ᴰ|kₐ|2ᵃ ≤ 3ᵃ` (the `D` arm), then `3ᵃ` has a constant digit block on `[u, a+v)` for every `u`
with `3ᵃ < 2^{u+D+a}`.  The top end `a + v` is the valuation arm, the bottom end `u ≈ 0.585a − D`
is the rate arm — the *sum* `D + v`, not their minimum, is what the block sees. -/
@[category research solved, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem block_of_arms {a D v u : ℕ} (hv : 2 ^ v ∣ mNat a)
    (hD : 2 ^ D * (resid 3 2 a).natAbs * 2 ^ a ≤ 3 ^ a) (hu : 3 ^ a < 2 ^ (u + D + a)) :
    IsBlock (3 ^ a) u (a + v) := by
  obtain ⟨M, hM⟩ := hv
  constructor
  · -- `2^{a+v} ≤ 2·3ᵃ` : `2ᵛ ≤ mₐ` and `mₐ2ᵃ ≤ 2·3ᵃ`
    have h1 : 2 ^ v ≤ mNat a := Nat.le_of_dvd (mNat_pos a) ⟨M, hM⟩
    calc 2 ^ (a + v) = 2 ^ v * 2 ^ a := by rw [pow_add]; ring
      _ ≤ mNat a * 2 ^ a := Nat.mul_le_mul_right _ h1
      _ ≤ 2 * 3 ^ a := mNat_mul_two_pow_le a
  · -- the centred residue at depth `a + v` is `|kₐ|`, and `|kₐ| < 2ᵘ`
    have hres : (3 ^ a : ℤ) - (M : ℤ) * 2 ^ (a + v) = resid 3 2 a := by
      have hm : Mnum 3 2 a = ((mNat a : ℕ) : ℤ) := Mnum_eq_mNat a
      rw [resid, hm, hM]
      push_cast
      rw [pow_add]
      ring
    have hle : (cres (3 ^ a) (a + v) : ℤ) ≤ |(resid 3 2 a : ℤ)| := by
      have := cres_le_abs (3 ^ a) (a + v) (M : ℤ)
      rw [show (((3 ^ a : ℕ) : ℤ)) = ((3 : ℤ) ^ a) by push_cast; ring] at this
      rwa [hres] at this
    -- `2ᴰ|kₐ|2ᵃ ≤ 3ᵃ < 2^{u+D+a}` forces `|kₐ| < 2ᵘ`
    have hlt : (resid 3 2 a).natAbs < 2 ^ u := by
      by_contra hcon
      push Not at hcon
      have hstep : 2 ^ D * 2 ^ u * 2 ^ a ≤ 2 ^ D * (resid 3 2 a).natAbs * 2 ^ a :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hcon)
      have h2 : 2 ^ (u + D + a) ≤ 3 ^ a := by
        calc 2 ^ (u + D + a) = 2 ^ D * 2 ^ u * 2 ^ a := by
              rw [pow_add, pow_add]; ring
          _ ≤ 2 ^ D * (resid 3 2 a).natAbs * 2 ^ a := hstep
          _ ≤ 3 ^ a := hD
      exact absurd hu (not_lt.mpr h2)
    rw [← Int.natCast_natAbs] at hle
    have hfin : (cres (3 ^ a) (a + v) : ℕ) ≤ (resid 3 2 a).natAbs := by exact_mod_cast hle
    exact lt_of_le_of_lt hfin hlt

/-- **The block of an exception, with its length.**  Under the two arms there is a `u` with
`IsBlock (3ᵃ) u (a+v)` and `41u + 41D ≤ 24a + 41`, i.e. the block has length
`≥ (17a + 41D + 41v − 41)/41 = 0.4146a + D + v − 1`. -/
@[category research solved, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem arms_block_length {a D v : ℕ} (ha : 1 ≤ a) (hv : 2 ^ v ∣ mNat a)
    (hD : 2 ^ D * (resid 3 2 a).natAbs * 2 ^ a ≤ 3 ^ a) :
    ∃ u : ℕ, IsBlock (3 ^ a) u (a + v) ∧ 41 * u + 41 * D ≤ 24 * a + 41 := by
  have hDa := depth_le_of_arm ha hD
  refine ⟨(24 * a - 41 * D) / 41 + 1, ?_, by omega⟩
  refine block_of_arms hv hD ?_
  -- `65a < 41(u + D + a)` gives `3ᵃ < 2^{u+D+a}` through `3⁴¹ ≤ 2⁶⁵`
  have hexp : 65 * a < 41 * ((24 * a - 41 * D) / 41 + 1 + D + a) := by omega
  have h1 : 3 ^ (41 * a) ≤ 2 ^ (65 * a) := three_pow_le_two_pow a
  have h2 : 2 ^ (65 * a) < 2 ^ (41 * ((24 * a - 41 * D) / 41 + 1 + D + a)) :=
    Nat.pow_lt_pow_right (by norm_num) hexp
  have h3 : (3 ^ a) ^ 41 < (2 ^ ((24 * a - 41 * D) / 41 + 1 + D + a)) ^ 41 := by
    calc (3 ^ a) ^ 41 = 3 ^ (41 * a) := by rw [← pow_mul, Nat.mul_comm]
      _ ≤ 2 ^ (65 * a) := h1
      _ < 2 ^ (41 * ((24 * a - 41 * D) / 41 + 1 + D + a)) := h2
      _ = (2 ^ ((24 * a - 41 * D) / 41 + 1 + D + a)) ^ 41 := by rw [← pow_mul, Nat.mul_comm]
  by_contra hcon
  push Not at hcon
  exact absurd h3 (not_lt.mpr (Nat.pow_le_pow_left hcon 41))

/-! ## 3. [DD90] Proposition 1, reproved

The persistence lemma, read at an exception, *is* Delmer–Deshouillers' criterion. -/

/-- **[DD90] Prop. 1** (the positive form).  If `k` is an exception and `k ≤ m`, then `3ᵐ` has a
constant digit block on `[u, k)` for every `u` with `65m < 41(u+k)` — i.e. a block of length
`2k − 65m/41` ending exactly at bit position `k`. -/
@[category research solved, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem dd_prop_one {k m u : ℕ} (hkm : k ≤ m) (hf : IsFailure 3 2 (3 / 4) k)
    (hu : 65 * m < 41 * (u + k)) : IsBlock (3 ^ m) u k := by
  have harm : 2 ^ 0 * (resid 3 2 k).natAbs * 2 ^ k ≤ 3 ^ k := exception_arm hf
  have harm' : (resid 3 2 k).natAbs * 2 ^ k ≤ 3 ^ k := by simpa using harm
  -- `3ᵐ < 2^{u+k}`
  have hlt : 3 ^ m < 2 ^ (u + k) := by
    have h1 : 3 ^ (41 * m) ≤ 2 ^ (65 * m) := three_pow_le_two_pow m
    have h2 : (3 ^ m) ^ 41 < (2 ^ (u + k)) ^ 41 := by
      calc (3 ^ m) ^ 41 = 3 ^ (41 * m) := by rw [← pow_mul, Nat.mul_comm]
        _ ≤ 2 ^ (65 * m) := h1
        _ < 2 ^ (41 * (u + k)) := Nat.pow_lt_pow_right (by norm_num) hu
        _ = (2 ^ (u + k)) ^ 41 := by rw [← pow_mul, Nat.mul_comm]
    by_contra hcon
    push Not at hcon
    exact absurd h2 (not_lt.mpr (Nat.pow_le_pow_left hcon 41))
  constructor
  · calc 2 ^ k ≤ 3 ^ k := Nat.pow_le_pow_left (by norm_num) k
      _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hkm
      _ ≤ 2 * 3 ^ m := Nat.le_mul_of_pos_left _ (by norm_num)
  · -- `cres (3ᵐ) k ≤ 3^{m−k}·cres (3ᵏ) k ≤ 3^{m−k}|k_k| < 2ᵘ`
    have hsplit : (3 : ℕ) ^ m = 3 ^ (m - k) * 3 ^ k := by
      rw [← pow_add]; congr 1; omega
    have hbase : cres (3 ^ k) k ≤ (resid 3 2 k).natAbs := by
      have hres : (3 ^ k : ℤ) - (mNat k : ℤ) * 2 ^ k = resid 3 2 k := by
        rw [resid, Mnum_eq_mNat]; push_cast; ring
      have hstep := cres_le_abs (3 ^ k) k ((mNat k : ℕ) : ℤ)
      rw [show (((3 ^ k : ℕ) : ℤ)) = ((3 : ℤ) ^ k) by push_cast; ring, hres,
        ← Int.natCast_natAbs] at hstep
      exact_mod_cast hstep
    have hchain : cres (3 ^ m) k ≤ 3 ^ (m - k) * (resid 3 2 k).natAbs := by
      rw [hsplit]
      exact le_trans (cres_mul_le _ _ _) (Nat.mul_le_mul_left _ hbase)
    have hfin : 3 ^ (m - k) * (resid 3 2 k).natAbs < 2 ^ u := by
      by_contra hcon
      push Not at hcon
      have h1 : 2 ^ u * 2 ^ k ≤ 3 ^ (m - k) * (resid 3 2 k).natAbs * 2 ^ k :=
        Nat.mul_le_mul_right _ hcon
      have h2 : 3 ^ (m - k) * (resid 3 2 k).natAbs * 2 ^ k ≤ 3 ^ m := by
        calc 3 ^ (m - k) * (resid 3 2 k).natAbs * 2 ^ k
            = 3 ^ (m - k) * ((resid 3 2 k).natAbs * 2 ^ k) := by ring
          _ ≤ 3 ^ (m - k) * 3 ^ k := Nat.mul_le_mul_left _ harm'
          _ = 3 ^ m := hsplit.symm
      have h3 : 2 ^ (u + k) ≤ 3 ^ m := by
        rw [pow_add]; exact le_trans h1 h2
      exact absurd hlt (not_lt.mpr h3)
    exact lt_of_le_of_lt hchain hfin

/-- **[DD90] Prop. 1**, in the source's own form: *if `3ᵐ` contains no block of `h` equal digits,
then the Diophantine condition holds for `m·log3/log4 + h/2 + 1/2 < k ≤ m`.*  The integer
hypothesis `65m + 41h + 41 ≤ 82k` is `k ≥ (65/82)m + h/2 + 1/2` with `65/82 = 0.792683` in place
of `log3/log4 = 0.792481` — the certificate `3⁴¹ ≤ 2⁶⁵`, and both of the source's constants. -/
@[category research solved, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem dd_prop_one_contra {m h k : ℕ} (hkm : k ≤ m)
    (hrange : 65 * m + 41 * h + 41 ≤ 82 * k)
    (hno : ∀ u : ℕ, ¬ IsBlock (3 ^ m) u (u + h)) : ¬ IsFailure 3 2 (3 / 4) k := by
  intro hf
  have hhk : h ≤ k := by
    have : 65 * k ≤ 65 * m := Nat.mul_le_mul_left _ hkm
    omega
  have hblock : IsBlock (3 ^ m) (k - h) k := by
    refine dd_prop_one hkm hf ?_
    have : k - h + k = 2 * k - h := by omega
    omega
  exact hno (k - h) (by rwa [show k - h + h = k by omega])

/-! ## 4. Milestone 3: persistence, and what happens at the next exception -/

/-- **The block of an exception persists.**  If `a` carries the two arms `(D, v)` then `3^{a+j}`
still has a constant block on `[u + t, a+v)` whenever `3ʲ ≤ 2ᵗ`: the run is not destroyed at the
top of the fibre, it erodes at the bottom by `log₂3` positions per step.  This is the exact
opposite of the repulsion milestone 3 asked for. -/
@[category research solved, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem exception_block_persists {a D v u j t : ℕ} (hv : 2 ^ v ∣ mNat a)
    (hD : 2 ^ D * (resid 3 2 a).natAbs * 2 ^ a ≤ 3 ^ a) (hu : 3 ^ a < 2 ^ (u + D + a))
    (ht : 3 ^ j ≤ 2 ^ t) : IsBlock (3 ^ (j + a)) (u + t) (a + v) := by
  have := block_pow_mul (block_of_arms hv hD hu) ht
  rwa [← pow_add] at this

/-! ## 5. Pricing: what a global run bound is worth

Everything here is integer arithmetic.  A run bound at rate `c = P/Q` (with slack `C`) enters as
`Q·hi ≤ Q·lo + P·a + C` for every block, and leaves as a cap on `D + v₂`. -/

/-- **The trivial global run bound**: a block of `3ⁿ` has length at most `65n/41 + 1`, because it
sits inside the word.  This is `c = log₂3 = 1.58496`, the top of the price list. -/
@[category research solved, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem run_bound_trivial {n lo hi : ℕ} (h : IsBlock (3 ^ n) lo hi) :
    41 * hi ≤ 41 * lo + 65 * n + 41 := by
  obtain ⟨hword, -⟩ := h
  have h1 : 2 ^ hi ≤ 2 * 3 ^ n := hword
  have h2 : (2 ^ hi) ^ 41 ≤ (2 * 3 ^ n) ^ 41 := Nat.pow_le_pow_left h1 41
  have h3 : (2 * 3 ^ n) ^ 41 = 2 ^ 41 * 3 ^ (41 * n) := by
    rw [Nat.mul_pow, ← pow_mul, Nat.mul_comm 41 n]
  have h4 : 2 ^ (41 * hi) ≤ 2 ^ (41 + 65 * n) := by
    calc 2 ^ (41 * hi) = (2 ^ hi) ^ 41 := by rw [← pow_mul, Nat.mul_comm]
      _ ≤ 2 ^ 41 * 3 ^ (41 * n) := by rw [← h3]; exact h2
      _ ≤ 2 ^ 41 * 2 ^ (65 * n) := Nat.mul_le_mul_left _ (three_pow_le_two_pow n)
      _ = 2 ^ (41 + 65 * n) := by rw [← pow_add]
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h4
  omega

/-- **The pricing theorem.**  A global run bound `length ≤ (P/Q)·a + C/Q` for the blocks of `3ᵃ`
caps the **sum** of the two arms:

`17Qa + 41Q(D + v) ≤ 41Pa + 41Q + 41C`,  i.e.  `D + v₂ ≤ (P/Q − 17/41)·a + O(1)`.

Since `min(D, v) ≤ (D+v)/2`, the fibre is capped at half the excess over `17/41 = 0.4146` — the
factor `2` that separates a run bound straddling bit `a` from a rate bound below it. -/
@[category research solved, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem sum_of_run_bound {a D v P Q C : ℕ} (ha : 1 ≤ a) (hv : 2 ^ v ∣ mNat a)
    (hD : 2 ^ D * (resid 3 2 a).natAbs * 2 ^ a ≤ 3 ^ a)
    (hrun : ∀ lo hi : ℕ, IsBlock (3 ^ a) lo hi → Q * hi ≤ Q * lo + P * a + C) :
    17 * Q * a + 41 * Q * (D + v) ≤ 41 * P * a + 41 * Q + 41 * C := by
  obtain ⟨u, hblock, hbot⟩ := arms_block_length ha hv hD
  have h := hrun u (a + v) hblock
  have h1 : (Q : ℤ) * (41 * u + 41 * D) ≤ (Q : ℤ) * (24 * a + 41) := by
    exact_mod_cast Nat.mul_le_mul_left Q hbot
  have h2 : (41 : ℤ) * ((Q : ℤ) * ((a : ℤ) + v)) ≤ 41 * ((Q : ℤ) * u + (P : ℤ) * a + C) := by
    exact_mod_cast Nat.mul_le_mul_left 41 h
  have hZ : (17 : ℤ) * Q * a + 41 * Q * ((D : ℤ) + v) ≤ 41 * (P : ℤ) * a + 41 * Q + 41 * C := by
    linarith [h1, h2]
  exact_mod_cast hZ

/-- The fibre form: at a tower of depth `d` both arms hold at `d`, so a run bound at `c = P/Q`
gives `17Qa + 82Qd ≤ 41Pa + 41Q + 41C`. -/
@[category research solved, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem fibre_of_run_bound {a d P Q C : ℕ} (ha : 1 ≤ a) (hv : 2 ^ d ∣ mNat a)
    (hD : 2 ^ d * (resid 3 2 a).natAbs * 2 ^ a ≤ 3 ^ a)
    (hrun : ∀ lo hi : ℕ, IsBlock (3 ^ a) lo hi → Q * hi ≤ Q * lo + P * a + C) :
    17 * Q * a + 82 * Q * d ≤ 41 * P * a + 41 * Q + 41 * C := by
  have h := sum_of_run_bound ha hv hD hrun
  rwa [show 41 * Q * (d + d) = 82 * Q * d by ring] at h

/-- **Calibration: the trivial run bound returns the elementary row.**  Feeding
`run_bound_trivial` (`c = log₂3`) into the pricing theorem gives `41(D + v) ≤ 48a + 82`, i.e.
`min(D, v₂) ≤ 0.5854a + 1` — the first row of the report's §1.4 table, on the nose. -/
@[category research solved, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem elementary_row_from_runs {a D v : ℕ} (ha : 1 ≤ a) (hv : 2 ^ v ∣ mNat a)
    (hD : 2 ^ D * (resid 3 2 a).natAbs * 2 ^ a ≤ 3 ^ a) : 41 * (D + v) ≤ 48 * a + 82 := by
  have h := sum_of_run_bound (P := 65) (Q := 41) (C := 41) ha hv hD
    (fun lo hi hb => by have := run_bound_trivial hb; omega)
  omega

/-- **Calibration: a global run bound at `c = 1.153` beats [Zud07].**  It gives
`82000·d ≤ 30273a + 82000`, i.e. `min ≤ 0.36918a + 1`, against `BB13.zudilin_slope`'s
`35d ≤ 13a` (`0.37143a`).  The crossover is `c = 1.1549`; every rate `c` below it — and the
whole word is only `1.58496` — would improve the best bound in print since 2007. -/
@[category research solved, AMS 11, ref "Bug12" "DD90" "Zud07", group "bugeaud_10_13"]
theorem run_bound_beats_zudilin {a d : ℕ} (ha : 1 ≤ a) (hv : 2 ^ d ∣ mNat a)
    (hD : 2 ^ d * (resid 3 2 a).natAbs * 2 ^ a ≤ 3 ^ a)
    (hrun : ∀ lo hi : ℕ, IsBlock (3 ^ a) lo hi → 1000 * hi ≤ 1000 * lo + 1153 * a) :
    82000 * d ≤ 30273 * a + 41000 := by
  have := fibre_of_run_bound (P := 1153) (Q := 1000) (C := 0) ha hv hD
    (fun lo hi hb => by have := hrun lo hi hb; omega)
  omega

/-- **Calibration: a global run bound below `17/41 = 0.4146` settles Problem 1 effectively.**  If
every block of `3ᵃ` is shorter than `(P/Q)a + C/Q` with `41P < 17Q`, then `a` is bounded — no
exception survives past `41(Q + C)/(17Q − 41P)`. -/
@[category research solved, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem no_exception_of_run_bound {a P Q C : ℕ} (ha : 1 ≤ a) (hPQ : 41 * P < 17 * Q)
    (hf : IsFailure 3 2 (3 / 4) a)
    (hrun : ∀ lo hi : ℕ, IsBlock (3 ^ a) lo hi → Q * hi ≤ Q * lo + P * a + C) :
    a ≤ 41 * Q + 41 * C := by
  have hv : 2 ^ 0 ∣ mNat a := by simp
  have hD : 2 ^ 0 * (resid 3 2 a).natAbs * 2 ^ a ≤ 3 ^ a := exception_arm hf
  have h := sum_of_run_bound (D := 0) (v := 0) ha hv hD hrun
  rw [show (0 : ℕ) + 0 = 0 from rfl, Nat.mul_zero, Nat.add_zero] at h
  have h1 : (41 * P + 1) * a ≤ 17 * Q * a := Nat.mul_le_mul_right a hPQ
  have hZ1 : ((41 * P + 1 : ℕ) : ℤ) * a ≤ ((17 * Q : ℕ) : ℤ) * a := by exact_mod_cast h1
  have hZ2 : ((17 * Q * a : ℕ) : ℤ) ≤ ((41 * P * a + 41 * Q + 41 * C : ℕ) : ℤ) := by
    exact_mod_cast h
  push_cast at hZ1 hZ2
  have : (a : ℤ) ≤ 41 * Q + 41 * C := by linarith only [hZ1, hZ2]
  exact_mod_cast this

/-! ## 6. [DD90] Proposition 4: the global run bound is `o(m)`, ineffectively

The source's proof, formalized: the block is a Ridout solution at the budget `2 + 2θ/q`, and one
slope carries finitely many indices.  Footprint `std3 + BugeaudEvertse.ridout_line_cover`. -/

/-- `5log3 < 8log2` (i.e. `3⁵ = 243 < 256 = 2⁸`), the numeral behind `1/θ < 8/5`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem five_log_three_lt_eight_log_two : 5 * Real.log 3 < 8 * Real.log 2 := by
  have h : Real.log ((3 : ℝ) ^ (5 : ℕ)) < Real.log ((2 : ℝ) ^ (8 : ℕ)) :=
    Real.log_lt_log (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h
  linarith

/-- `5/8 < θ`, i.e. `1/θ < 8/5 = 1.6`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem five_div_eight_lt_theta : (5 : ℝ) / 8 < theta := by
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  rw [theta, lt_div_iff₀ hl3]
  have := five_log_three_lt_eight_log_two
  linarith

/-- `(1/2)^w ≤ (3ⁿ)^{−θs}` when `s·n ≤ w`: the `2`-adic row of the frame, in the shape (5.11)
asks for. -/
@[category API, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem half_pow_le_rpow {n w : ℕ} {s : ℝ} (h : s * (n : ℝ) ≤ (w : ℝ)) :
    (1 / 2 : ℝ) ^ w ≤ ((3 : ℝ) ^ n) ^ (-(theta * s)) := by
  have h3a : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hlhs : (0 : ℝ) < (1 / 2 : ℝ) ^ w := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [Real.rpow_def_of_pos h3a, ← Real.exp_log hlhs, Real.exp_le_exp, Real.log_pow, Real.log_pow,
    show Real.log (1 / 2 : ℝ) = -Real.log 2 by rw [← Real.log_inv]; norm_num]
  have hrhs : (n : ℝ) * Real.log 3 * (-(theta * s)) = -((n : ℝ) * s * Real.log 2) := by
    rw [← theta_mul_log_three]; ring
  rw [hrhs]
  nlinarith [h, hl2]

/-- `2ᵘ/3ⁿ ≤ (3ⁿ)^{−(1 − θt)}` when `u ≤ t·n`: the archimedean row. -/
@[category API, AMS 11, ref "BE08" "Bug12", group "bugeaud_10_13"]
theorem two_div_three_le_rpow {n u : ℕ} {t : ℝ} (h : (u : ℝ) ≤ t * (n : ℝ)) :
    (2 : ℝ) ^ u / (3 : ℝ) ^ n ≤ ((3 : ℝ) ^ n) ^ (-(1 - theta * t)) := by
  have h3a : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hlhs : (0 : ℝ) < (2 : ℝ) ^ u / (3 : ℝ) ^ n := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [Real.rpow_def_of_pos h3a, ← Real.exp_log hlhs, Real.exp_le_exp, Real.log_div (by positivity)
    (by positivity), Real.log_pow, Real.log_pow]
  have hrhs : (n : ℝ) * Real.log 3 * (-(1 - theta * t))
      = -((n : ℝ) * Real.log 3) + (n : ℝ) * t * Real.log 2 := by
    rw [← theta_mul_log_three]; ring
  rw [hrhs]
  nlinarith [h, hl2]

/-- A single Ridout line carries only finitely many block indices: `|1 − r|` is a fixed positive
number while the frame point of a block of length `L` is within `2^{1−L}` of `1`. -/
@[category research solved, AMS 11, ref "BE08" "Bug12" "DD90", group "bugeaud_10_13"]
theorem blockLine_finite {ε : ℝ} (hε : 0 < ε) (r : ℚ) :
    {n : ℕ | r ≠ 1 ∧ ∃ L : ℕ, ε * (n : ℝ) ≤ (L : ℝ) ∧
      |(1 : ℝ) - (r : ℝ)| < 2 * (1 / 2 : ℝ) ^ L}.Finite := by
  by_cases hr : r = 1
  · convert Set.finite_empty
    ext n
    simp [hr]
  · have hpos : 0 < |(1 : ℝ) - (r : ℝ)| := by
      refine abs_pos.mpr (sub_ne_zero.mpr ?_)
      intro h
      exact hr (by exact_mod_cast h.symm)
    obtain ⟨L₀, hL₀⟩ := exists_pow_lt_of_lt_one (by linarith : 0 < |(1 : ℝ) - (r : ℝ)| / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    refine Set.Finite.subset (Set.finite_lt_nat ⌈(L₀ : ℝ) / ε⌉₊) ?_
    rintro n ⟨-, L, hLn, hlt⟩
    have hL : L < L₀ := by
      by_contra hcon
      push Not at hcon
      have hmono : (1 / 2 : ℝ) ^ L ≤ (1 / 2 : ℝ) ^ L₀ :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hcon
      linarith
    have hnlt : (n : ℝ) < (L₀ : ℝ) / ε := by
      rw [lt_div_iff₀ hε]
      have : (L : ℝ) < (L₀ : ℝ) := by exact_mod_cast hL
      nlinarith [hLn]
    exact Nat.lt_ceil.mpr hnlt

/-- **[DD90] Proposition 4.**  *The length of the longest block of equal digits in the binary
expansion of `3ⁿ` is `o(n)`*: for every `ε > 0` only finitely many `n` carry a constant digit
block of length `≥ εn` anywhere in the word.

The proof is the source's, on the corpus's Ridout axiom.  A block on `[u, u+L)` with `L ≥ εn`
contains one of the `q ≈ 3/ε` overlapping windows `[pn/q, (p+2)n/q)`, and then the frame point
`(x, y) = (ν2^{u+L}, 3ⁿ)` solves (5.11) at

`(f∞, f₂, f₃) = (1 − θp/q, θ(p+2)/q, 1)`,  sum `= 2 + 2θ/q`,

so all but finitely many such `n` lie on one of `lineBound (2θ/q)` slopes, each carrying finitely
many `n` (`blockLine_finite`).

**Ineffective**, exactly like `BB13.valuation_arm_finite`, and strictly stronger than it: an
exception `a` has a block of length `≥ 0.4146a` (`arms_block_length`), so this theorem *implies*
the finiteness of `ℰ`.  That is the price of the whole B7 programme: the only unconditional global
run bound in print is Mahler's theorem in digit clothing.  [DD90] themselves note that the truth
is expected to be `O(log n)`. -/
@[category research solved, AMS 11, ref "BE08" "DD90" "Mah57", group "bugeaud_10_13"]
theorem longBlock_finite {ε : ℝ} (hε : 0 < ε) :
    {n : ℕ | ∃ u L : ℕ, ε * (n : ℝ) ≤ (L : ℝ) ∧ IsBlock (3 ^ n) u (u + L)}.Finite := by
  have hth := theta_pos
  -- the window denominator `q ≥ max(3/ε, 5)`
  obtain ⟨q0, hq0⟩ := exists_nat_ge (3 / ε)
  set q : ℕ := max q0 5 with hqdef
  have hq5 : 5 ≤ q := le_max_right _ _
  have hqR : 3 / ε ≤ (q : ℝ) := le_trans hq0 (by exact_mod_cast le_max_left q0 5)
  have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
  have hq3 : 3 ≤ ε * q := by
    rw [div_le_iff₀ hε] at hqR
    linarith
  set ρ : ℝ := 2 * theta / q with hρdef
  have hρ : 0 < ρ := by rw [hρdef]; positivity
  -- one Ridout instance per window index `p`
  have key : ∀ p : ℕ, ∃ R : Finset ℚ, ∀ x y : ℤ, 0 < y →
      0 ≤ 1 - theta * p / q →
      max (2 * ((BugeaudEvertse.ratHeight 1 : ℕ) : ℝ)) ((2 : ℝ) ^ ((4 : ℝ) / ρ)) < (y : ℝ) →
      |(1 : ℝ) - (x : ℝ) / (y : ℝ)| ≤ (y : ℝ) ^ (-(1 - theta * p / q)) →
      ((padicNorm 2 (x : ℚ) : ℚ) : ℝ) ≤ (y : ℝ) ^ (-(theta * (p + 2) / q)) →
      ((padicNorm 3 (y : ℚ) : ℚ) : ℝ) ≤ (y : ℝ) ^ (-(1 : ℝ)) →
      (x : ℚ) / (y : ℚ) ∈ R := by
    intro p
    by_cases hf : 0 ≤ 1 - theta * p / q
    · obtain ⟨R, -, hR⟩ := BugeaudEvertse.ridout_line_cover_23 1 ρ (1 - theta * p / q)
        (theta * (p + 2) / q) 1 hρ hf (by positivity) zero_le_one
        (by rw [hρdef]; field_simp; ring)
      exact ⟨R, fun x y hy _ hht harch h2 h3 => hR x y hy (by simpa using hht)
        (by simpa using harch) h2 h3⟩
    · exact ⟨∅, fun x y _ hcon _ _ _ _ => absurd hcon hf⟩
  choose R hR using key
  -- the height threshold (5.12)
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt
    (max (2 * ((BugeaudEvertse.ratHeight 1 : ℕ) : ℝ)) ((2 : ℝ) ^ ((4 : ℝ) / ρ)))
    (by norm_num : (1 : ℝ) < 3)
  obtain ⟨M, hM⟩ := exists_nat_ge (3 / ε)
  refine Set.Finite.subset (Set.Finite.union (Set.finite_lt_nat (max (max N M) q))
    (((Finset.range (2 * q + 1)).finite_toSet).biUnion
      (fun p _ => ((R p).finite_toSet).biUnion (fun r _ => blockLine_finite hε r)))) ?_
  rintro n ⟨u, L, hLn, hblock⟩
  rcases lt_or_ge n (max (max N M) q) with hsmall | hbig
  · exact Or.inl hsmall
  -- the large indices
  have hnN : N ≤ n := le_trans (le_trans (le_max_left N M) (le_max_left _ _)) hbig
  have hnM : M ≤ n := le_trans (le_trans (le_max_right N M) (le_max_left _ _)) hbig
  have hnq : q ≤ n := le_trans (le_max_right _ _) hbig
  have hn1 : 1 ≤ n := le_trans (by omega) hnq
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hMn : (M : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnM
  have hεn : 3 ≤ ε * n := by
    rw [div_le_iff₀ hε] at hM
    nlinarith [hM, hMn, hε]
  obtain ⟨hword, hcres⟩ := hblock
  -- the frame point
  obtain ⟨ν, hν⟩ := cres_spec (3 ^ n) (u + L)
  set x : ℤ := ν * 2 ^ (u + L) with hxdef
  set y : ℤ := (3 : ℤ) ^ n with hydef
  have hypos : (0 : ℤ) < y := by rw [hydef]; positivity
  have hyR : (y : ℝ) = (3 : ℝ) ^ n := by rw [hydef]; push_cast; ring
  have hy3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hypos' : (0 : ℝ) < (y : ℝ) := by rw [hyR]; exact hy3
  have hdistZ : |(y : ℤ) - x| < 2 ^ u := by
    have h1 : |((3 ^ n : ℕ) : ℤ) - ν * 2 ^ (u + L)| = (cres (3 ^ n) (u + L) : ℤ) := hν
    have h2 : ((cres (3 ^ n) (u + L) : ℕ) : ℤ) < 2 ^ u := by exact_mod_cast hcres
    rw [hydef, hxdef, show ((3 : ℤ) ^ n) = ((3 ^ n : ℕ) : ℤ) by push_cast; ring, h1]
    exact h2
  have hdist : |(y : ℝ) - (x : ℝ)| < (2 : ℝ) ^ u := by
    have hcast : ((|(y : ℤ) - x| : ℤ) : ℝ) < (((2 : ℤ) ^ u : ℤ) : ℝ) := by exact_mod_cast hdistZ
    push_cast at hcast
    exact hcast
  have harch : |(1 : ℝ) - (x : ℝ) / (3 : ℝ) ^ n| < (2 : ℝ) ^ u / (3 : ℝ) ^ n := by
    rw [show (1 : ℝ) - (x : ℝ) / (3 : ℝ) ^ n = ((3 : ℝ) ^ n - (x : ℝ)) / (3 : ℝ) ^ n by
      field_simp, abs_div, abs_of_pos hy3]
    exact (div_lt_div_iff_of_pos_right hy3).mpr (by rw [← hyR]; exact hdist)
  -- the window index
  set p : ℕ := (u * q) / n + 1 with hpdef
  have hnpos' : 0 < n := hn1
  have hdm := Nat.div_add_mod (u * q) n
  have hmodlt : (u * q) % n < n := Nat.mod_lt _ hnpos'
  have hpn : u * q < p * n := by
    calc u * q = n * (u * q / n) + (u * q) % n := hdm.symm
      _ < n * (u * q / n) + n := Nat.add_lt_add_left hmodlt _
      _ = (u * q / n) * n + n := by rw [Nat.mul_comm]
      _ = p * n := by rw [hpdef]; ring
  have hpn' : p * n ≤ u * q + n := by
    calc p * n = (u * q / n) * n + n := by rw [hpdef]; ring
      _ ≤ u * q + n := Nat.add_le_add_right (Nat.div_mul_le_self _ _) n
  -- real bookkeeping
  have hqn : (0 : ℝ) < (q : ℝ) := hqpos
  have huq : (u : ℝ) * q ≤ (p : ℝ) * n := by exact_mod_cast le_of_lt hpn
  have hpq : (p : ℝ) * n ≤ (u : ℝ) * q + n := by exact_mod_cast hpn'
  have hLR : ε * n ≤ (L : ℝ) := hLn
  -- the word bound: `2^{u+L} ≤ 2·3ⁿ` gives `(u + L)·θ ≤ n + θ`
  have hwordR : ((u : ℝ) + L) * Real.log 2 ≤ (n : ℝ) * Real.log 3 + Real.log 2 := by
    have h1 : ((2 : ℝ) ^ (u + L)) ≤ 2 * (3 : ℝ) ^ n := by exact_mod_cast hword
    have h2 : Real.log ((2 : ℝ) ^ (u + L)) ≤ Real.log (2 * (3 : ℝ) ^ n) :=
      Real.log_le_log (by positivity) h1
    rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h2
    push_cast at h2
    linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hthlog : theta * Real.log 3 = Real.log 2 := theta_mul_log_three
  have hth1 : theta < 1 := theta_lt_one
  have hth58 : (5 : ℝ) / 8 < theta := five_div_eight_lt_theta
  -- `u·θ ≤ n + θ − L·θ`, hence `θ·p/q ≤ 1`
  have hu_bound : (u : ℝ) * theta ≤ (n : ℝ) + theta - (L : ℝ) * theta := by
    have hmul : (((u : ℝ) + L) * theta) * Real.log 3 ≤ ((n : ℝ) + theta) * Real.log 3 := by
      rw [show (((u : ℝ) + L) * theta) * Real.log 3 = ((u : ℝ) + L) * (theta * Real.log 3) by ring,
        hthlog, show ((n : ℝ) + theta) * Real.log 3
          = (n : ℝ) * Real.log 3 + theta * Real.log 3 by ring, hthlog]
      exact hwordR
    have hstep := le_of_mul_le_mul_right hmul hl3
    linarith only [hstep]
  have hnq' : (q : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnq
  have hq5' : (5 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq5
  have hn5 : (5 : ℝ) ≤ (n : ℝ) := le_trans hq5' hnq'
  have hu0 : (0 : ℝ) ≤ (u : ℝ) := by positivity
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := by positivity
  have hfInf : 0 ≤ 1 - theta * p / q := by
    rw [sub_nonneg, div_le_one hqn]
    -- `n + q ≤ Lq`, from `L ≥ εn`, `εq ≥ 3` and `n ≥ q`
    have hLq : (n : ℝ) + q ≤ (L : ℝ) * q := by
      have h1 : (ε * n) * q ≤ (L : ℝ) * q := mul_le_mul_of_nonneg_right hLR (le_of_lt hqn)
      have h2 : (3 : ℝ) * n ≤ (ε * q) * n := mul_le_mul_of_nonneg_right hq3 (le_of_lt hnpos)
      linarith only [h1, h2, hnq']
    have h1 : theta * ((p : ℝ) * n) ≤ theta * ((u : ℝ) * q + n) :=
      mul_le_mul_of_nonneg_left hpq (le_of_lt hth)
    have h2 : ((u : ℝ) * theta) * q ≤ ((n : ℝ) + theta - (L : ℝ) * theta) * q :=
      mul_le_mul_of_nonneg_right hu_bound (le_of_lt hqn)
    have h4 : theta * ((n : ℝ) + q) ≤ theta * ((L : ℝ) * q) :=
      mul_le_mul_of_nonneg_left hLq (le_of_lt hth)
    have h5 : theta * (p : ℝ) * (n : ℝ) ≤ (q : ℝ) * (n : ℝ) := by linarith only [h1, h2, h4]
    exact le_of_mul_le_mul_right h5 hnpos
  have hpsmall : p < 2 * q + 1 := by
    -- `u ≤ n/θ + 1 ≤ 1.6n + 1`, from `uθ ≤ n + θ` and `θ > 5/8`
    have hu58 : (u : ℝ) * (5 / 8) ≤ (u : ℝ) * theta :=
      mul_le_mul_of_nonneg_left (le_of_lt hth58) hu0
    have hLth : (0 : ℝ) ≤ (L : ℝ) * theta := mul_nonneg hL0 (le_of_lt hth)
    have hu5 : 5 * (u : ℝ) ≤ 8 * (n : ℝ) + 8 := by
      linarith only [hu58, hu_bound, hth1, hLth]
    have huq5 : 5 * ((u : ℝ) * q) ≤ (8 * (n : ℝ) + 8) * q := by
      have := mul_le_mul_of_nonneg_right hu5 (le_of_lt hqn)
      linarith only [this]
    have hnq5 : 5 * (q : ℝ) ≤ (n : ℝ) * q := mul_le_mul_of_nonneg_right hn5 (le_of_lt hqn)
    have hp5 : 5 * ((p : ℝ) * n) ≤ 5 * ((u : ℝ) * q + n) := by linarith only [hpq]
    have hgoal : (p : ℝ) * n < (2 * q + 1) * n := by
      linarith only [hp5, huq5, hnq5, hqn]
    have : (p : ℝ) < 2 * q + 1 := lt_of_mul_lt_mul_right hgoal (le_of_lt hnpos)
    exact_mod_cast this
  -- the three rows
  have hrow_arch : |(1 : ℝ) - (x : ℝ) / (y : ℝ)| ≤ (y : ℝ) ^ (-(1 - theta * p / q)) := by
    rw [hyR, show theta * (p : ℝ) / q = theta * ((p : ℝ) / q) by ring]
    refine le_trans (le_of_lt harch) (two_div_three_le_rpow ?_)
    rw [div_mul_eq_mul_div, le_div_iff₀ hqn]
    exact huq
  have hrow_two : ((padicNorm 2 (x : ℚ) : ℚ) : ℝ) ≤ (y : ℝ) ^ (-(theta * (p + 2) / q)) := by
    have hdvd : (2 : ℤ) ^ (u + L) ∣ x := ⟨ν, by rw [hxdef]; ring⟩
    have h1 := BugeaudEvertse.padicNorm_le_of_dvd_pow Nat.prime_two hdvd
    have h2 : ((2 : ℕ) : ℝ) ^ (-((u + L : ℕ) : ℝ)) = (1 / 2 : ℝ) ^ (u + L) := by
      rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num, Real.rpow_neg (by norm_num),
        Real.rpow_natCast, one_div, inv_pow]
    rw [h2] at h1
    refine le_trans h1 ?_
    rw [hyR, show theta * ((p : ℝ) + 2) / q = theta * (((p : ℝ) + 2) / q) by ring]
    refine half_pow_le_rpow ?_
    -- `((p+2)/q)·n ≤ u + L`, i.e. `(p+2)n ≤ (u+L)q`, from `pn ≤ uq + n` and `3n ≤ Lq`
    rw [div_mul_eq_mul_div, div_le_iff₀ hqn]
    have hLq3 : (ε * n) * q ≤ (L : ℝ) * q := mul_le_mul_of_nonneg_right hLR (le_of_lt hqn)
    have hLq4 : (3 : ℝ) * n ≤ (ε * q) * n := mul_le_mul_of_nonneg_right hq3 (le_of_lt hnpos)
    have h3n : 3 * (n : ℝ) ≤ (L : ℝ) * q := by linarith only [hLq3, hLq4]
    push_cast
    linarith only [hpq, h3n]
  have hrow_three : ((padicNorm 3 (y : ℚ) : ℚ) : ℝ) ≤ (y : ℝ) ^ (-(1 : ℝ)) :=
    frame_three_adic n
  have hthr : max (2 * ((BugeaudEvertse.ratHeight 1 : ℕ) : ℝ)) ((2 : ℝ) ^ ((4 : ℝ) / ρ))
      < (y : ℝ) := by
    rw [hyR]
    exact lt_of_lt_of_le hN (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hnN)
  have hmem := hR p x y hypos hfInf hthr hrow_arch hrow_two hrow_three
  -- the slope is not `1`, and it is within `2^{1−L}` of `1`
  have hL1 : 1 ≤ L := by
    have : (1 : ℝ) ≤ (L : ℝ) := by nlinarith [hLR, hεn]
    exact_mod_cast this
  have hne : (x : ℚ) / (y : ℚ) ≠ 1 := by
    intro h
    have hy0 : (y : ℚ) ≠ 0 := by exact_mod_cast hypos.ne'
    have hxy : (x : ℚ) = (y : ℚ) := by
      rwa [div_eq_one_iff_eq hy0] at h
    have hxyZ : x = y := by exact_mod_cast hxy
    obtain ⟨w, hw⟩ : ∃ w, u + L = w + 1 := ⟨u + L - 1, by omega⟩
    have h2x : (2 : ℤ) ∣ x := ⟨ν * 2 ^ w, by rw [hxdef, hw, pow_succ]; ring⟩
    have h2y : ¬ ((2 : ℤ) ∣ y) := by
      rw [hydef]
      intro hcon
      have hnat : (2 : ℕ) ∣ 3 ^ n := by
        have hz : ((2 : ℕ) : ℤ) ∣ ((3 ^ n : ℕ) : ℤ) := by push_cast; exact hcon
        exact_mod_cast hz
      have h23 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hnat
      norm_num at h23
    exact h2y (hxyZ ▸ h2x)
  have hclose : |(1 : ℝ) - (((x : ℚ) / (y : ℚ) : ℚ) : ℝ)| < 2 * (1 / 2 : ℝ) ^ L := by
    have hcast : (((x : ℚ) / (y : ℚ) : ℚ) : ℝ) = (x : ℝ) / (3 : ℝ) ^ n := by
      push_cast; rw [hyR]
    rw [hcast]
    refine lt_of_lt_of_le harch ?_
    -- `2ᵘ/3ⁿ ≤ 2·2^{−L}` because `2^{u+L} ≤ 2·3ⁿ`
    have h1 : ((2 : ℝ) ^ (u + L)) ≤ 2 * (3 : ℝ) ^ n := by exact_mod_cast hword
    have h2 : (2 : ℝ) ^ (u + L) = (2 : ℝ) ^ u * 2 ^ L := by rw [pow_add]
    rw [div_le_iff₀ hy3]
    have h3 : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
    have h4 : (2 : ℝ) * (1 / 2 : ℝ) ^ L * (3 : ℝ) ^ n = 2 * (3 : ℝ) ^ n / 2 ^ L := by
      rw [one_div, inv_pow]; field_simp
    rw [h4, le_div_iff₀ h3, ← h2]
    exact h1
  exact Or.inr (Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_range.mpr hpsmall))
    (Set.mem_biUnion (Finset.mem_coe.mpr hmem) ⟨hne, L, hLn, hclose⟩))

end BB13
