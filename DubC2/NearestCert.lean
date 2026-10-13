/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.ProductState
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The certificate for `𝒫 = {2,5}`: the carry word of an avoiding orbit is `(AABB)^∞`

Milestone M3 of `plans/plan-dubC2.html`, third layer — the mathematical core.  Assume that from
some index `N` on the nearest integers `xₙ = [ξ(3/2)ⁿ + ½]` are divisible neither by `2` nor by
`5`.  Then the carry word is **forced**, up to a rotation, to `(−1,−1,+1,+1)^∞`, i.e. to
`(AABB)^∞` in the letters of `DubC2/NearestStep.lean`.

## Why this is a proof and not a `decide`

The plan budgeted a machine-emitted certificate here (`NearestCert` + `NearestData`, a subset
construction with SCC ranks, checked by `decide`).  M1 found the answer at `|𝒫| = 2` with a
paper proof short enough to check by hand, so this file carries that proof instead: the
certificate is a *theorem*, there is no emitted data, and `DubC2/NearestData.lean` is not
needed.  The information the engine's graph contained is here as three lemmas.

* `DubC2.funnel` — **the cell rule.**  From the block-start cell `yₙ ∈ [0,3/8)` at a residue of
  `{1,4}`, the only survivor is the sharp cell `yₙ ∈ [5/54, 1/6)`.  The two discarded pieces
  die because they would run the orbit into `A` at residue `2` or `B` at residue `3`, which are
  exactly the two edges into `0 mod 5` (`DubC2/ProductState.lean`).
* `DubC2.cycle` — **the block.**  From the sharp cell the next four letters are `A A B B`, the
  residue returns to where it started (`1 → 1 → 1 → 2 → 1`, resp. `4 → 3 → 4 → 4 → 4`) and
  `y` returns to the block-start cell `[0,3/8)`.
* `DubC2.seed` — **entry.**  Whatever `ξ` is, the orbit reaches the block-start cell within
  four steps of the first residue in `{1,4}`, and such a residue occurs within one step.

Together: `DubC2.isEventuallyPeriodic_sN`.  The carry word of an avoiding orbit is eventually
periodic with period `4`, which [DN05] Lemma 2 — proved, not cited, as
`Z32.not_isEventuallyPeriodic_carry` — forbids for every `ξ ≠ 0`.  Hence
`DubC2.exists_not_avoids`.

## The tube, and why it is absent here

The M1 engine had to determinize its graph before the "every cyclic component is a simple
cycle" test would fire: a grid over `[0,1)` carries every genuine periodic orbit as a *tube* of
`q/(p−q) = 2` cells, which branches, and refining the grid never narrows it (plan §4.2).  A
hand proof never meets the tube, because it tracks the real number `yₙ` and not a cell of it.
That is the whole difference between the two routes, and it is why the certificate here is
three lemmas rather than a 24-state automaton.

## References

* [DN05] A. Dubickas, A. Novikas, *Integer parts of powers of rational numbers*, Math. Z. **251**
  (2005), 635–648 — Lemma 2 and Theorem 4.
* [Dub09AA] A. Dubickas, *Powers of a rational number modulo 1 cannot lie in a small interval*,
  Acta Arith. **137** (2009), 233–239.
-/

namespace DubC2

open ForMathlib.SubwordComplexity

variable {ξ : ℝ} {N n : ℕ}

/-- **The block-start cell**: `yₙ ∈ [0, 3/8)` at a residue of `{1,4}` mod `5`.  Every completed
`AABB` block lands here. -/
def Base (ξ : ℝ) (n : ℕ) : Prop :=
  yN ξ n < 3 / 8 ∧ (xN ξ n % 5 = 1 ∨ xN ξ n % 5 = 4)

/-- **The sharp cell**: `yₙ ∈ [5/54, 1/6)` at a residue of `{1,4}` mod `5`.  This is the domain
of the block `AABB`, and `DubC2.funnel` says an avoiding orbit at a block start is already
here. -/
def Good (ξ : ℝ) (n : ℕ) : Prop :=
  5 / 54 ≤ yN ξ n ∧ yN ξ n < 1 / 6 ∧ (xN ξ n % 5 = 1 ∨ xN ξ n % 5 = 4)

/-! ## The cell rule -/

/-- **The funnel.**  At a block start of an avoiding orbit the residual is confined to
`[5/54, 1/6)`: the piece `[1/6, 3/8)` runs into a forbidden letter after two steps, and the
piece `[0, 5/54)` after three (residue `1`) or four (residue `4`). -/
@[category research solved, AMS 11 37, ref "DN05", group "dn05_nearest_32"]
theorem funnel (hav : ∀ m, N ≤ m → Avoids ξ m) (hn : N ≤ n) (hB : Base ξ n) : Good ξ n := by
  obtain ⟨hy38, hr⟩ := hB
  have a0 := hav n hn
  have a1 := hav (n + 1) (by omega)
  have a2 := hav (n + 2) (by omega)
  have a3 := hav (n + 3) (by omega)
  have a4 := hav (n + 4) (by omega)
  have a5 := hav (n + 5) (by omega)
  have hy0 := yN_nonneg ξ n
  have hlt6 : yN ξ n < 1 / 6 := by
    by_contra hc
    push Not at hc
    obtain ⟨-, hy1, hst1⟩ := stepA' a0 (by linarith)
    have hy1lo : 1 / 2 ≤ yN ξ (n + 1) := by linarith
    have hy1hi : yN ξ (n + 1) < 13 / 16 := by linarith
    obtain ⟨-, hy2, hst2⟩ := stepB' a1 hy1lo
    rcases hr with hr | hr
    · have r1 : xN ξ (n + 1) % 5 = 1 := res_A_one hst1 hr
      have r2 : xN ξ (n + 2) % 5 = 2 := res_B_one hst2 r1
      have := half_le_yN_of_res_two a2 a3 r2
      linarith
    · have r1 : xN ξ (n + 1) % 5 = 3 := res_A_four hst1 hr
      have := yN_lt_half_of_res_three a1 a2 r1
      linarith
  refine ⟨?_, hlt6, hr⟩
  by_contra hc
  push Not at hc
  obtain ⟨-, hy1, hst1⟩ := stepA' a0 (by linarith)
  have hy1lo : 1 / 4 ≤ yN ξ (n + 1) := by linarith
  have hy1hi : yN ξ (n + 1) < 7 / 18 := by linarith
  obtain ⟨-, hy2, hst2⟩ := stepA' a1 (by linarith)
  have hy2lo : 5 / 8 ≤ yN ξ (n + 2) := by linarith
  have hy2hi : yN ξ (n + 2) < 5 / 6 := by linarith
  obtain ⟨-, hy3, hst3⟩ := stepB' a2 (by linarith)
  have hy3lo : 3 / 16 ≤ yN ξ (n + 3) := by linarith
  have hy3hi : yN ξ (n + 3) < 1 / 2 := by linarith
  rcases hr with hr | hr
  · have r1 : xN ξ (n + 1) % 5 = 1 := res_A_one hst1 hr
    have r2 : xN ξ (n + 2) % 5 = 1 := res_A_one hst2 r1
    have r3 : xN ξ (n + 3) % 5 = 2 := res_B_one hst3 r2
    have := half_le_yN_of_res_two a3 a4 r3
    linarith
  · have r1 : xN ξ (n + 1) % 5 = 3 := res_A_four hst1 hr
    have r2 : xN ξ (n + 2) % 5 = 4 := res_A_three hst2 r1
    have r3 : xN ξ (n + 3) % 5 = 4 := res_B_four hst3 r2
    obtain ⟨-, hy4, hst4⟩ := stepA' a3 hy3hi
    have r4 : xN ξ (n + 4) % 5 = 3 := res_A_four hst4 r3
    have := yN_lt_half_of_res_three a4 a5 r4
    linarith

/-! ## The block -/

/-- **The `AABB` block.**  From the sharp cell the next four carries are `−1, −1, +1, +1`, and
the orbit returns to a block start. -/
@[category research solved, AMS 11 37, ref "DN05", group "dn05_nearest_32"]
theorem cycle (hav : ∀ m, N ≤ m → Avoids ξ m) (hn : N ≤ n) (hG : Good ξ n) :
    sN ξ n = -1 ∧ sN ξ (n + 1) = -1 ∧ sN ξ (n + 2) = 1 ∧ sN ξ (n + 3) = 1 ∧
      Base ξ (n + 4) := by
  obtain ⟨hylo, hyhi, hr⟩ := hG
  have a0 := hav n hn
  have a1 := hav (n + 1) (by omega)
  have a2 := hav (n + 2) (by omega)
  have a3 := hav (n + 3) (by omega)
  obtain ⟨s0, hy1, hst1⟩ := stepA' a0 (by linarith)
  have hy1lo : 7 / 18 ≤ yN ξ (n + 1) := by linarith
  have hy1hi : yN ξ (n + 1) < 1 / 2 := by linarith
  obtain ⟨s1, hy2, hst2⟩ := stepA' a1 hy1hi
  have hy2lo : 5 / 6 ≤ yN ξ (n + 2) := by linarith
  have hy2hi : yN ξ (n + 2) < 1 := yN_lt_one ξ (n + 2)
  obtain ⟨s2, hy3, hst3⟩ := stepB' a2 (by linarith)
  have hy3lo : 1 / 2 ≤ yN ξ (n + 3) := by linarith
  have hy3hi : yN ξ (n + 3) < 3 / 4 := by linarith
  obtain ⟨s3, hy4, hst4⟩ := stepB' a3 hy3lo
  refine ⟨s0, s1, s2, s3, by linarith, ?_⟩
  rcases hr with hr | hr
  · exact Or.inl (res_B_two hst4 (res_B_one hst3 (res_A_one hst2 (res_A_one hst1 hr))))
  · exact Or.inr (res_B_four hst4 (res_B_four hst3 (res_A_three hst2 (res_A_four hst1 hr))))

/-! ## Entry -/

/-- At residue `2` the orbit is one forced `B` away from a block start. -/
@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_32"]
theorem at_two (hav : ∀ m, N ≤ m → Avoids ξ m) (hn : N ≤ n) (hr : xN ξ n % 5 = 2)
    (hy : yN ξ n < 3 / 4) : xN ξ (n + 1) % 5 = 1 ∧ yN ξ (n + 1) < 3 / 8 := by
  have a0 := hav n hn
  have a1 := hav (n + 1) (by omega)
  obtain ⟨-, hy1, hst⟩ := stepB' a0 (half_le_yN_of_res_two a0 a1 hr)
  exact ⟨res_B_two hst hr, by linarith⟩

/-- At residue `4` with `yₙ ∈ [3/8, 3/4)` the orbit is one forced `B` away from a block start:
the letter `A` would put it at residue `3` with `y ≥ 13/16`, where `B` is forbidden. -/
@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_32"]
theorem at_four (hav : ∀ m, N ≤ m → Avoids ξ m) (hn : N ≤ n) (hr : xN ξ n % 5 = 4)
    (hlo : 3 / 8 ≤ yN ξ n) (hhi : yN ξ n < 3 / 4) :
    xN ξ (n + 1) % 5 = 4 ∧ yN ξ (n + 1) < 3 / 8 := by
  have a0 := hav n hn
  have a1 := hav (n + 1) (by omega)
  have a2 := hav (n + 2) (by omega)
  rcases lt_or_ge (yN ξ n) (1 / 2) with h | h
  · exfalso
    obtain ⟨-, hy1, hst⟩ := stepA' a0 h
    have := yN_lt_half_of_res_three a1 a2 (res_A_four hst hr)
    linarith
  · obtain ⟨-, hy1, hst⟩ := stepB' a0 h
    exact ⟨res_B_four hst hr, by linarith⟩

/-- Entry from residue `1` (the `{1,2}` component): at most four steps to a block start. -/
@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_32"]
theorem seed_one (hav : ∀ m, N ≤ m → Avoids ξ m) (hn : N ≤ n) (hr : xN ξ n % 5 = 1) :
    ∃ M, n ≤ M ∧ Base ξ M := by
  have a0 := hav n hn
  have a1 := hav (n + 1) (by omega)
  have a2 := hav (n + 2) (by omega)
  have hy0 := yN_nonneg ξ n
  have hy0' := yN_lt_one ξ n
  rcases le_or_gt (1 / 2) (yN ξ n) with h | h
  · obtain ⟨-, hy1, hst1⟩ := stepB' a0 h
    obtain ⟨r2, hy2⟩ := at_two hav (n := n + 1) (by omega) (res_B_one hst1 hr) (by linarith)
    exact ⟨n + 2, by omega, hy2, Or.inl r2⟩
  · obtain ⟨-, hy1, hst1⟩ := stepA' a0 h
    have r1 : xN ξ (n + 1) % 5 = 1 := res_A_one hst1 hr
    have hy1lo : 1 / 4 ≤ yN ξ (n + 1) := by linarith
    have hy1hi := yN_lt_one ξ (n + 1)
    rcases le_or_gt (1 / 2) (yN ξ (n + 1)) with h1 | h1
    · obtain ⟨-, hy2, hst2⟩ := stepB' a1 h1
      obtain ⟨r3, hy3⟩ := at_two hav (n := n + 2) (by omega) (res_B_one hst2 r1) (by linarith)
      exact ⟨n + 3, by omega, hy3, Or.inl r3⟩
    · obtain ⟨-, hy2, hst2⟩ := stepA' a1 h1
      have r2 : xN ξ (n + 2) % 5 = 1 := res_A_one hst2 r1
      have hy2lo : 5 / 8 ≤ yN ξ (n + 2) := by linarith
      have hy2hi := yN_lt_one ξ (n + 2)
      obtain ⟨-, hy3, hst3⟩ := stepB' a2 (by linarith)
      obtain ⟨r4, hy4⟩ := at_two hav (n := n + 3) (by omega) (res_B_one hst3 r2) (by linarith)
      exact ⟨n + 4, by omega, hy4, Or.inl r4⟩

/-- Entry from residue `4` (the `{3,4}` component): at most four steps to a block start. -/
@[category API, AMS 11 37, ref "DN05", group "dn05_nearest_32"]
theorem seed_four (hav : ∀ m, N ≤ m → Avoids ξ m) (hn : N ≤ n) (hr : xN ξ n % 5 = 4) :
    ∃ M, n ≤ M ∧ Base ξ M := by
  have a0 := hav n hn
  have a1 := hav (n + 1) (by omega)
  have a2 := hav (n + 2) (by omega)
  have hy0 := yN_nonneg ξ n
  have hy0' := yN_lt_one ξ n
  rcases le_or_gt (1 / 2) (yN ξ n) with h | h
  · obtain ⟨-, hy1, hst1⟩ := stepB' a0 h
    have r1 : xN ξ (n + 1) % 5 = 4 := res_B_four hst1 hr
    rcases lt_or_ge (yN ξ (n + 1)) (3 / 8) with h1 | h1
    · exact ⟨n + 1, by omega, h1, Or.inr r1⟩
    · obtain ⟨r2, hy2⟩ := at_four hav (n := n + 1) (by omega) r1 h1 (by linarith)
      exact ⟨n + 2, by omega, hy2, Or.inr r2⟩
  · obtain ⟨-, hy1, hst1⟩ := stepA' a0 h
    have r1 : xN ξ (n + 1) % 5 = 3 := res_A_four hst1 hr
    have h1 : yN ξ (n + 1) < 1 / 2 := yN_lt_half_of_res_three a1 a2 r1
    have hy1lo : 1 / 4 ≤ yN ξ (n + 1) := by linarith
    obtain ⟨-, hy2, hst2⟩ := stepA' a1 h1
    have r2 : xN ξ (n + 2) % 5 = 4 := res_A_three hst2 r1
    have hy2lo : 5 / 8 ≤ yN ξ (n + 2) := by linarith
    have hy2hi := yN_lt_one ξ (n + 2)
    obtain ⟨-, hy3, hst3⟩ := stepB' a2 (by linarith)
    have r3 : xN ξ (n + 3) % 5 = 4 := res_B_four hst3 r2
    rcases lt_or_ge (yN ξ (n + 3)) (3 / 8) with h3 | h3
    · exact ⟨n + 3, by omega, h3, Or.inr r3⟩
    · obtain ⟨r4, hy4⟩ := at_four hav (n := n + 3) (by omega) r3 h3 (by linarith)
      exact ⟨n + 4, by omega, hy4, Or.inr r4⟩

/-- **Entry.**  An avoiding orbit reaches a block start. -/
@[category research solved, AMS 11 37, ref "DN05", group "dn05_nearest_32"]
theorem seed (hav : ∀ m, N ≤ m → Avoids ξ m) : ∃ M, N ≤ M ∧ Base ξ M := by
  have a0 := hav N le_rfl
  have a1 := hav (N + 1) (by omega)
  have a2 := hav (N + 2) (by omega)
  rcases a0.res_mem with h | h | h | h
  · exact seed_one hav le_rfl h
  · obtain ⟨-, -, hst⟩ := stepB' a0 (half_le_yN_of_res_two a0 a1 h)
    obtain ⟨M, hM, hB⟩ := seed_one hav (n := N + 1) (by omega) (res_B_two hst h)
    exact ⟨M, by omega, hB⟩
  · obtain ⟨-, -, hst⟩ := stepA' a0 (yN_lt_half_of_res_three a0 a1 h)
    obtain ⟨M, hM, hB⟩ := seed_four hav (n := N + 1) (by omega) (res_A_three hst h)
    exact ⟨M, by omega, hB⟩
  · exact seed_four hav le_rfl h

/-! ## The carry word of an avoiding orbit -/

/-- **The certificate.**  If `xₙ` avoids `{2,5}` from `N` on, the carry word is eventually
periodic with period `4` — the word `(−1,−1,+1,+1)^∞`, i.e. `(AABB)^∞`. -/
@[category research solved, AMS 11 68, ref "DN05", group "dn05_nearest_32"]
theorem isEventuallyPeriodic_sN (hav : ∀ m, N ≤ m → Avoids ξ m) :
    IsEventuallyPeriodic (sN ξ) := by
  obtain ⟨M, hMN, hBM⟩ := seed hav
  have hbase : ∀ k, Base ξ (M + 4 * k) := by
    intro k
    induction k with
    | zero => simpa using hBM
    | succ k ih =>
      obtain ⟨-, -, -, -, hB'⟩ := cycle hav (N := N) (by omega) (funnel hav (by omega) ih)
      have he : M + 4 * (k + 1) = M + 4 * k + 4 := by ring
      rw [he]; exact hB'
  have hpat : ∀ k j, j < 4 → sN ξ (M + 4 * k + j) = (if j < 2 then (-1 : ℤ) else 1) := by
    intro k j hj
    obtain ⟨s0, s1, s2, s3, -⟩ := cycle hav (N := N) (by omega) (funnel hav (by omega) (hbase k))
    interval_cases j
    · simpa using s0
    · simpa using s1
    · simpa using s2
    · simpa using s3
  refine ⟨M, 4, by norm_num, ?_⟩
  intro m hm
  obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 4 ∧ m = M + 4 * k + j :=
    ⟨(m - M) / 4, (m - M) % 4, by omega, by omega⟩
  rw [show M + 4 * k + j + 4 = M + 4 * (k + 1) + j by ring, hpat (k + 1) j hj, hpat k j hj]

/-- **`{2,5}` is unavoidable.**  For every real `ξ ≠ 0` and every `N` there is an `n ≥ N` with
`xₙ = [ξ(3/2)ⁿ + ½]` divisible by `2` or by `5`.  Eventual avoidance would make the carry word
eventually periodic, which [DN05] Lemma 2 (`Z32.not_isEventuallyPeriodic_carry`) forbids. -/
@[category research solved, AMS 11 37, ref "DN05", group "dn05_nearest_32"]
theorem exists_not_avoids (hξ : ξ ≠ 0) (N : ℕ) : ∃ n, N ≤ n ∧ ¬ Avoids ξ n := by
  by_contra hc
  push Not at hc
  have hper : IsEventuallyPeriodic (Z32.carry 3 2 ξ (1 / 2)) := isEventuallyPeriodic_sN hc
  exact Z32.not_isEventuallyPeriodic_carry (p := 3) (q := 2) (ξ := ξ) (ν := 1 / 2)
    (by norm_num) (by norm_num) (by decide) hξ hper

end DubC2
