/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC.Ladder

/-!
# Verdicts: kernel-checked bases, controls, and the `a = 7` target

Instances of the certificate machinery of `DubC/Certificate.lean` (plan `plan-dubC1.html`,
milestone M1′).

## Kernel-checked bases

For `b = 3, 4` at `𝒫 = {2,3}` and `b = 5, 6` at `𝒫 = {2,3,5}` an explicit rank function passes
`CertOK`, checked by `decide`.  Each therefore yields, **sorry-free and axiom-free**, the full
statement of [DubOst06] Conjecture 2 for that base:

  `DubC.infinite_composites_three/four/five/six` — for every real `ξ > 0` the sequence
  `⌊ξbⁿ⌋` contains infinitely many composite terms.

These bases are known ( `b = 3,4,6` are [MPP+24] Lemma A.1; `b = 5` is [DN05] Theorem 2), so
nothing new is claimed — their role is to exercise the whole pipeline end to end in the kernel
and to show that the reduction is not vacuous.  Note `b = 4` and `b = 6` genuinely need a
non-constant rank: their cores contain surviving cycles (e.g. `x ↦ 4x+3` fixes `1 mod 6`), and
the certificate tolerates them precisely because a periodic word is harmless.

## Controls: the certificate does *not* fire spuriously

`DubC.not_certOK_seven_thirty` and `DubC.not_certOK_ten_thirty` prove that **no** rank function
exists at `𝒫 = {2,3,5}` for `b = 7` or for `b = 10`, by exhibiting a residue with two distinct
successors that both return to it (two distinct cycles in one SCC — the exact obstruction the
certificate rules out).  `b = 10` is the open base of [DubOst06] Conjecture 3 and the plan's
mandated sanity test: the machinery must not appear to settle it.

## Two certificate forms

The rank form (`DubC.CertOK`) and the compressed-core form (`DubC.CoreClosed` +
`DubC.CoreDet`) both feed the same pipeline, and neither hypothesis implies the other.
`DubC.not_coreDet_four_six` pins the difference down in the kernel: base `4` at `𝒫 = {2,3}`
passes the rank form and fails the core form, because its two cycles are joined by an edge.

## The `a = 7` target

`DubC.infinite_composites_seven_of_cert` and `DubC.infinite_composites_seven_of_coreCert` state
the 1967 Forman–Shapiro problem for `a = 7` as a *theorem conditional on a finite, explicitly
displayed certificate* at the modulus `DubC.primorial31 = ∏_{p ≤ 31} p` — the modulus at which
the C engines in this directory (`subshift.c`, `ladder.c`, `cycles.c`, cross-checked by
`subshift.py`, `verify_core.py`, `compress.py`) report that the pruned core is a disjoint union
of simple cycles with no edges between them.  Nothing here asserts that computation: it is a
hypothesis of the theorem, not an axiom of the development.

The core form is the one the computation actually produces, and it is the smaller obligation:
no rank function, just the cycle set `K` (365 761 residues in 849 cycles, emitted as
`core_y31_cycles.txt`) together with "the core has no cycles outside `K`" and "`K` is
deterministic".  Discharging either form in Lean means running a check over data of that size
in the kernel, which `decide` cannot reach on a `2·10¹¹`-element residue ring; the gap is
therefore stated, not hidden.

## References

* **[DN05]** A. Dubickas, A. Novikas, *Integer parts of powers of rational numbers*,
  Math. Z. **251** (2005) 635–648.
* **[Dub09]** A. Dubickas, *Prime and composite integers close to powers of a number*,
  Monatsh. Math. **158** (2009) 271–284.
* **[DubOst06]** A. Dubickas, *Truncatable primes and unavoidable sets of divisors*,
  Acta Math. Univ. Ostrav. **14** (2006) 21–25.
* **[MPP+24]** S. J. Miller et al., *Walking to infinity along some Zeckendorf
  representations*, Integers **24** (2024) #A78.  Lemma A.1.
-/

namespace DubC

/-! ### Sanity checks on the definitions -/

@[category test, AMS 11 37, ref "Dub09", group "dubc_verdict"]
theorem floorPow_half_three : floorPow (1 / 2 : ℝ) 3 2 = 4 := by
  norm_num [floorPow]

@[category test, AMS 11 37, ref "Dub09", group "dubc_verdict"]
theorem floorDigit_half_three : floorDigit (1 / 2 : ℝ) 3 0 = 1 := by
  norm_num [floorDigit, Int.fract]

@[category test, AMS 11 37, ref "Dub09", group "dubc_verdict"]
theorem compositeInt_four : CompositeInt 4 := by unfold CompositeInt; decide

@[category test, AMS 11 37, ref "Dub09", group "dubc_verdict"]
theorem not_compositeInt_seven : ¬ CompositeInt 7 := by unfold CompositeInt; decide

/-- Negative integers count as composite through their absolute value ([Dub09] p. 273). -/
@[category test, AMS 11 37, ref "Dub09", group "dubc_verdict"]
theorem compositeInt_neg_six : CompositeInt (-6) := by unfold CompositeInt; decide

/-! ### Kernel-checked bases -/

/-- `C({2,3})` for base 3: every unit mod 6 has a unique admissible successor, so the constant
rank works. -/
@[category test, AMS 11 37, ref "MPP+24", group "dubc_verdict"]
theorem certOK_three : CertOK 3 6 (fun _ => 0) := by decide

/-- `C({2,3})` for base 4.  Here `1 mod 6` is a genuine fixed point (`x ↦ 4x+3`), so the rank
must separate it from the recurrent state `5`. -/
@[category test, AMS 11 37, ref "MPP+24", group "dubc_verdict"]
theorem certOK_four : CertOK 4 6 (fun r => if r = 1 then 1 else 0) := by decide

/-- `C({2,3,5})` for base 5 — the modulus at which [DN05]'s own proof for `a = 5` collapses the
alphabet; every unit again has a unique admissible successor. -/
@[category test, AMS 11 37, ref "DN05", group "dubc_verdict"]
theorem certOK_five : CertOK 5 30 (fun _ => 0) := by decide

/-- `C({2,3,5})` for base 6.  The rank is the height in the condensation DAG: the digit `5`
loops inside a residue class mod 5 while the digit `1` advances it towards the forbidden
class, so the potential `2·(4 - r mod 5) + [r ≡ 1 mod 3]` strictly drops on every branch. -/
@[category test, AMS 11 37, ref "MPP+24", group "dubc_verdict"]
theorem certOK_six :
    CertOK 6 30 (fun r => 2 * (4 - r.val % 5) + (if r.val % 3 = 1 then 1 else 0)) := by decide

/-- **Base 3**: for every real `ξ > 0`, `⌊ξ·3ⁿ⌋` contains infinitely many composite terms. -/
@[category research solved, AMS 11 37, ref "MPP+24" "Dub09", group "dubc_verdict"]
theorem infinite_composites_three {ξ : ℝ} (hξ : 0 < ξ) :
    {n | CompositeInt (floorPow ξ 3 n)}.Infinite :=
  infinite_composites_floorPow_of_certOK (by norm_num) (by norm_num) _ certOK_three hξ

/-- **Base 4**: for every real `ξ > 0`, `⌊ξ·4ⁿ⌋` contains infinitely many composite terms. -/
@[category research solved, AMS 11 37, ref "MPP+24" "Dub09", group "dubc_verdict"]
theorem infinite_composites_four {ξ : ℝ} (hξ : 0 < ξ) :
    {n | CompositeInt (floorPow ξ 4 n)}.Infinite :=
  infinite_composites_floorPow_of_certOK (by norm_num) (by norm_num) _ certOK_four hξ

/-- **Base 5** ([DN05] Theorem 2): for every real `ξ > 0`, `⌊ξ·5ⁿ⌋` contains infinitely many
composite terms. -/
@[category research solved, AMS 11 37, ref "DN05" "Dub09", group "dubc_verdict"]
theorem infinite_composites_five {ξ : ℝ} (hξ : 0 < ξ) :
    {n | CompositeInt (floorPow ξ 5 n)}.Infinite :=
  infinite_composites_floorPow_of_certOK (by norm_num) (by norm_num) _ certOK_five hξ

/-- **Base 6**: for every real `ξ > 0`, `⌊ξ·6ⁿ⌋` contains infinitely many composite terms. -/
@[category research solved, AMS 11 37, ref "MPP+24" "Dub09", group "dubc_verdict"]
theorem infinite_composites_six {ξ : ℝ} (hξ : 0 < ξ) :
    {n | CompositeInt (floorPow ξ 6 n)}.Infinite :=
  infinite_composites_floorPow_of_certOK (by norm_num) (by norm_num) _ certOK_six hξ

/-! ### The same bases through the compressed-core certificate

`DubC/CoreCertificate.lean` replaces the rank function by a set `K` that catches every cycle and
is deterministic.  For bases `3` and `5` the constant rank above already says that every unit has
a unique unit successor, so `K` may be taken to be *all* units and the whole certificate is one
`decide`. -/

/-- Base 3 at `𝒫 = {2,3}`: every unit mod `6` has exactly one unit successor. -/
@[category test, AMS 11 37, ref "MPP+24", group "dubc_verdict"]
theorem coreDet_three : CoreDet 3 6 (Cop 6) := by decide

/-- Base 5 at `𝒫 = {2,3,5}`: every unit mod `30` has exactly one unit successor. -/
@[category test, AMS 11 37, ref "DN05", group "dubc_verdict"]
theorem coreDet_five : CoreDet 5 30 (Cop 30) := by decide

/-- **Base 3 again, this time with no rank data at all.** -/
@[category research solved, AMS 11 37, ref "MPP+24" "Dub09", group "dubc_verdict"]
theorem infinite_composites_three_via_core {ξ : ℝ} (hξ : 0 < ξ) :
    {n | CompositeInt (floorPow ξ 3 n)}.Infinite :=
  infinite_composites_floorPow_of_unitDet (by norm_num) (by norm_num) coreDet_three hξ

/-- **Base 5 again, with no rank data at all.** -/
@[category research solved, AMS 11 37, ref "DN05" "Dub09", group "dubc_verdict"]
theorem infinite_composites_five_via_core {ξ : ℝ} (hξ : 0 < ξ) :
    {n | CompositeInt (floorPow ξ 5 n)}.Infinite :=
  infinite_composites_floorPow_of_unitDet (by norm_num) (by norm_num) coreDet_five hξ

/-- **The two certificate forms are genuinely different.**  For base `4` at `𝒫 = {2,3}` both
units mod `6` are fixed points (`x ↦ 4x+3`), so the cycle set is all of the units — yet `1` also
steps to `5` with the digit `1`, an edge *between* the two cycles.  `CertOK` tolerates it
(`DubC.certOK_four`, with a rank that drops across the edge); `CoreDet` does not.

So the compressed-core form is a strictly stronger hypothesis, justified for `a = 7` only by the
measured fact that the core at `𝒫 = {p ≤ 31}` has no edges between distinct cycles. -/
@[category test, AMS 11 37, ref "DubOst06", group "dubc_verdict"]
theorem not_coreDet_four_six : ¬ CoreDet 4 6 (Cop 6) := by decide

/-! ### The ladder in miniature

`DubC/Ladder.lean` discharges `CoreClosed` by a **rank function** rather than by a strongly
connected component computation, and lets a certificate at a small modulus bound the work at a
larger one.  Base 3 at `𝒫 = {2,3}` exercises both: the subshift is `1 → 5 → 5`, so the cycle set
is the *single* residue `5` — strictly smaller than the unit group — and the rank `[r ≠ 5]`
certifies it in one `decide`. -/

/-- The exact cycle set at `𝒫 = {2,3}` for base 3 is `{5}`, certified by a rank function. -/
@[category test, AMS 11 37, ref "Dub09", group "dubc_verdict"]
theorem rankOK_three : RankOK 3 6 (fun r => r = 5) (fun r => if r = 5 then 0 else 1) := by decide

@[category test, AMS 11 37, ref "Dub09", group "dubc_verdict"]
theorem coreClosed_three : CoreClosed 3 6 (fun r => r = 5) :=
  coreClosed_of_rankOK _ _ rankOK_three

@[category test, AMS 11 37, ref "Dub09", group "dubc_verdict"]
theorem coreDet_three_exact : CoreDet 3 6 (fun r => r = 5) := by decide

/-- **Base 3 from the exact cycle set**, i.e. the compressed-core certificate run on a `K` that
really is the set of cycle states rather than the whole unit group.  This is the shape the
`a = 7` target has, in miniature. -/
@[category research solved, AMS 11 37, ref "MPP+24" "Dub09", group "dubc_verdict"]
theorem infinite_composites_three_via_cycles {ξ : ℝ} (hξ : 0 < ξ) :
    {n | CompositeInt (floorPow ξ 3 n)}.Infinite :=
  infinite_composites_floorPow_of_coreCert (by norm_num) (by norm_num) _ coreClosed_three
    coreDet_three_exact hξ

/-- `6 ∣ 30`: one rung of the ladder, from `𝒫 = {2,3}` to `𝒫 = {2,3,5}`. -/
theorem six_dvd_thirty : (6 : ℕ) ∣ 30 := by norm_num

/-- **The projection lemma in action.**  A cycle modulo `30` projects to a cycle modulo `6`, so
the base-3 certificate `{5}` at `𝒫 = {2,3}` already confines every cycle modulo `30` to the
preimage of `{5}` — five residues instead of thirty, without looking at the larger modulus at
all.  This is the step that makes the `a = 7` ladder finite. -/
@[category test, AMS 11 37, ref "Dub09", group "dubc_verdict"]
theorem coreClosed_three_thirty :
    CoreClosed 3 30 (fun r => ZMod.castHom six_dvd_thirty (ZMod 6) r = 5) :=
  coreClosed_comap six_dvd_thirty coreClosed_three

/-! ### Controls: where the certificate must fail -/

/-- A convenient constructor for a single admissible edge. -/
@[category API, AMS 11 37, ref "Dub09", group "dubc_verdict"]
theorem step_of {a M : ℕ} {r t : ZMod M} (d : ℕ) (hd : d < a) (hr : Cop M r) (ht : Cop M t)
    (h : t = (a : ZMod M) * r + (d : ZMod M)) : Step a M r t := ⟨hr, ht, d, hd, h⟩

/-- The rank cannot increase along a chain of admissible steps. -/
@[category API, AMS 11 37, ref "Dub09", group "dubc_verdict"]
theorem rank_le_of_reachable {a M : ℕ} {rank : ZMod M → ℕ} (hcert : CertOK a M rank)
    {r t : ZMod M} (h : Relation.ReflTransGen (Step a M) r t) : rank t ≤ rank r := by
  induction h with
  | refl => exact le_refl _
  | tail _ hbc ih => exact le_trans (rank_le_of_certOK hcert _ _ hbc) ih

/-- **Two distinct cycles through one state kill every certificate.**  If a residue `r` has two
distinct admissible successors `t ≠ u` that both return to `r`, then `rank t = rank r = rank u`
is forced, and the uniqueness clause of `CertOK` collapses `t = u`.  This is the converse
direction of the certificate: a branching strongly connected component is exactly what
`C(𝒫)` forbids. -/
@[category research solved, AMS 11 37, ref "DubOst06", group "dubc_verdict"]
theorem not_certOK_of_two_returning_successors {a M : ℕ} {r t u : ZMod M}
    (hst : Step a M r t) (hsu : Step a M r u) (htu : t ≠ u)
    (htr : Relation.ReflTransGen (Step a M) t r) (hur : Relation.ReflTransGen (Step a M) u r)
    (rank : ZMod M → ℕ) : ¬ CertOK a M rank := by
  intro hcert
  refine htu (unique_of_certOK hcert r t u hst hsu ?_ ?_)
  · exact le_antisymm (rank_le_of_certOK hcert _ _ hst) (rank_le_of_reachable hcert htr)
  · exact le_antisymm (rank_le_of_certOK hcert _ _ hsu) (rank_le_of_reachable hcert hur)

/-- **Control, base 7 at `𝒫 = {2,3,5}`.**  No rank function certifies this modulus: the residue
`1` has the two distinct successors `7` (digit `0`) and `11` (digit `4`), and both return,
along `7 → 19 → 13 → 1` (digits `0,0,0`) and `11 → 17 → 1` (digits `0,2`).

So the smallest open base of the 1967 problem is *not* settled at `y = 5` — consistent with the
`DubC/` ladder, which finds `C(𝒫)` for `b = 7` only at `y = 31`. -/
@[category research solved, AMS 11 37, ref "DubOst06", group "dubc_verdict"]
theorem not_certOK_seven_thirty (rank : ZMod 30 → ℕ) : ¬ CertOK 7 30 rank := by
  have e17 : Step 7 30 1 7 := step_of 0 (by norm_num) (by decide) (by decide) (by decide)
  have e1_11 : Step 7 30 1 11 := step_of 4 (by norm_num) (by decide) (by decide) (by decide)
  have e719 : Step 7 30 7 19 := step_of 0 (by norm_num) (by decide) (by decide) (by decide)
  have e1913 : Step 7 30 19 13 := step_of 0 (by norm_num) (by decide) (by decide) (by decide)
  have e131 : Step 7 30 13 1 := step_of 0 (by norm_num) (by decide) (by decide) (by decide)
  have e1117 : Step 7 30 11 17 := step_of 0 (by norm_num) (by decide) (by decide) (by decide)
  have e171 : Step 7 30 17 1 := step_of 2 (by norm_num) (by decide) (by decide) (by decide)
  exact not_certOK_of_two_returning_successors e17 e1_11 (by decide)
    (((Relation.ReflTransGen.single e719).tail e1913).tail e131)
    ((Relation.ReflTransGen.single e1117).tail e171) rank

/-- **Control, base 10 at `𝒫 = {2,3,5}` — the mandated sanity test.**  `b = 10` is *open*
([DubOst06] Conjecture 3 predicts no unavoidable set exists for it), and the machinery must not
appear to settle it.  It does not: the residue `13` has the two distinct successors `13`
(digit `3`, a fixed point) and `19` (digit `9`), and `19 → 13` (digit `3`) returns. -/
@[category research solved, AMS 11 37, ref "DubOst06", group "dubc_verdict"]
theorem not_certOK_ten_thirty (rank : ZMod 30 → ℕ) : ¬ CertOK 10 30 rank := by
  have e1313 : Step 10 30 13 13 := step_of 3 (by norm_num) (by decide) (by decide) (by decide)
  have e1319 : Step 10 30 13 19 := step_of 9 (by norm_num) (by decide) (by decide) (by decide)
  have e1913 : Step 10 30 19 13 := step_of 3 (by norm_num) (by decide) (by decide) (by decide)
  exact not_certOK_of_two_returning_successors e1313 e1319 (by decide)
    Relation.ReflTransGen.refl (Relation.ReflTransGen.single e1913) rank

/-! ### The `a = 7` target -/

/-- `∏_{p ≤ 31} p = 200560490130`, the modulus at which the `DubC/` C engines report that the
pruned base-7 core (371 555 states) is a disjoint union of simple cycles. -/
def primorial31 : ℕ := 2 * 3 * 5 * 7 * 11 * 13 * 17 * 19 * 23 * 29 * 31

@[category test, AMS 11 37, ref "Dub09", group "dubc_verdict"]
theorem primorial31_eq : primorial31 = 200560490130 := by norm_num [primorial31]

instance : NeZero primorial31 := ⟨by norm_num [primorial31]⟩

/-- **The `a = 7` case of the 1967 Forman–Shapiro problem, conditional on one finite
certificate.**  If some rank function passes `CertOK 7 primorial31`, then for every real
`ξ > 0` the sequence `⌊ξ·7ⁿ⌋` contains infinitely many composite terms — i.e. [DubOst06]
Conjecture 2 holds for `b = 7`, the smallest open base.

The hypothesis is exactly what the C engines in this directory compute (a zero-entropy core at
`𝒫 = {p ≤ 31}`); it is stated here as a hypothesis, never assumed.  Discharging it in Lean
needs a rank function on a residue ring of size `2·10¹¹`, which `decide` cannot reach — the
remaining gap of milestone M1′, stated in the open. -/
@[category research solved, AMS 11 37, ref "Dub09" "DubOst06", group "dubc_verdict"]
theorem infinite_composites_seven_of_cert (rank : ZMod primorial31 → ℕ)
    (hcert : CertOK 7 primorial31 rank) {ξ : ℝ} (hξ : 0 < ξ) :
    {n | CompositeInt (floorPow ξ 7 n)}.Infinite :=
  infinite_composites_floorPow_of_certOK (by norm_num)
    (by norm_num [primorial31]) rank hcert hξ

/-- **The `a = 7` case again, conditional on the compressed core.**  This is the same conclusion
as `DubC.infinite_composites_seven_of_cert` resting on a smaller and more sharply located
hypothesis, and it is the form the `DubC/` computation actually produces.

The set `K` is the **cycle set** of the base-7 core at `𝒫 = {p ≤ 31}`: `365 761` residues in
`849` cycles, emitted as `DubC/core_y31_cycles.txt` by `DubC/cycles.c` and re-derived
independently by `DubC/compress.py`.  The two hypotheses are exactly the two things that
computation reports:

* `hclosed` — pruning the subshift to its recurrent part leaves nothing outside `K`.  This is
  the one *global* fact, and the only one that needs the full state space;
* `hdet` — inside `K` each residue has a single successor in `K`.  This is local, and it is
  where the measured absence of edges between distinct cycles is used: with such edges present
  a rank function would be needed and `hdet` would be false, as base `4` shows
  (`DubC.not_coreDet_four_six`).

Neither is asserted here; both are hypotheses.  Discharging them in Lean means shipping `K` as
kernel data and re-running the walk on it, which is the remaining gap of milestone M1′. -/
@[category research solved, AMS 11 37, ref "Dub09" "DubOst06", group "dubc_verdict"]
theorem infinite_composites_seven_of_coreCert (K : ZMod primorial31 → Prop)
    (hclosed : CoreClosed 7 primorial31 K) (hdet : CoreDet 7 primorial31 K)
    {ξ : ℝ} (hξ : 0 < ξ) :
    {n | CompositeInt (floorPow ξ 7 n)}.Infinite :=
  infinite_composites_floorPow_of_coreCert (by norm_num)
    (by norm_num [primorial31]) K hclosed hdet hξ

end DubC
