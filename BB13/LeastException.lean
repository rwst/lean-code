/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.TwoAdicRigidity

/-!
# The rounding recurrence and the least exception of a line (B8)

Item **B8** of `plans/report3-BB13.html` (§6 B8, §9): A2's strategies V and X — *everything
reduces to `v₂(mₐ)` at the least exception `a` of a line, where the rounding recurrence
`m_{n+1} = round(3mₙ/2)` constrains the bottom value* — together with A4's surviving residue-class
prong.  Rated 25% for a usable structural lemma.

## What the recurrence actually is

Write `mₙ = round((3/2)ⁿ)` (`BB13.Mnum 3 2 n`) and `kₙ = 3ⁿ − mₙ2ⁿ` (`BB13.resid 3 2 n`).  The
exact step is a *pair* identity,

`2m_{n+1} = 3mₙ + cₙ`,   `k_{n+1} = 3kₙ − cₙ2ⁿ`   (`BB13.carry`, `resid_succ`),

with a **carry** `cₙ` obeying `|cₙ| ≤ 2` and `cₙ ≡ mₙ (mod 2)` (`abs_carry_le_two`,
`carry_parity`), and all five values `−2, −1, 0, 1, 2` occur (`carry_alphabet`).

So the announced recurrence `m_{n+1} = round(3mₙ/2)` is **false** — it is the assertion `|cₙ| ≤ 1`,
and `cₙ = ±2` occurs (first at `n = 1`: `m₁ = 2` and `round(3·2/2) = 3`, but `m₂ = 2`).  The carry
is a function of `kₙ`, not of `mₙ`: for even `mₙ` it vanishes exactly when `3|kₙ| < 2ⁿ`
(`carry_eq_zero_of_even_of_small`), and otherwise it is `±2`.  **There is no autonomous recurrence
in the `m` variable**: the state is the pair `(mₙ, kₙ)`, and the `k` component is the problem
itself.  That is the first thing B8 settles, and it removes the lever strategy V was built on.

## The descent law, and the bottom lemma

What the carry does give is a complete description of how the `2`-adic arm moves:

* `cₙ = 0` ⟹ `k_{n+1} = 3kₙ` (so `n`, `n+1` lie on one line) and `v₂(m_{n+1}) + 1 = v₂(mₙ)`
  (`vTwo_succ_of_carry_zero`);
* `v₂(mₙ) ≥ 2` and `cₙ ≠ 0` ⟹ `v₂(m_{n+1}) = 0` — the **crash** (`vTwo_succ_eq_zero_of_carry_ne`).

Hence the dichotomy `vTwo_step_dichotomy` and its headline corollary

> **`vTwo_succ_lt`**: `v₂(mₙ) ≥ 2 ⟹ v₂(m_{n+1}) < v₂(mₙ)`.

The `2`-adic arm never rises except from height `≤ 1`; above height `1` it descends by exactly one
per step, and every descent is a walk down one line.  From this the least-exception statement is
two lines:

> **`vTwo_le_one_of_bottom`**: if `v₂(m_{a+1}) ≥ 1` and the carry at `a` does not vanish, then
> `v₂(mₐ) ≤ 1`.

A least exception `a+1` of a line with a nontrivial fibre satisfies both hypotheses
(`least_exception_vTwo_pred_le_one`), so **A2's strategy X is right up to one unit**: it claimed
`v₂(m_{a−1}) = 0`, the truth is `v₂(m_{a−1}) ≤ 1`, and both values occur (`bottom_pred_one`,
`bottom_pred_zero`).  The report's `CB4` — "*and then `v₂(m_{a−1})` is unconstrained*" — is
therefore wrong; see `CB16` in `plans/report3-BB13.html` §8.

## The fibre is exactly `1 + min(v₂(mₐ), D(a))`

`line_extends` runs the descent forward: `j ≤ v₂(mₐ)` plus archimedean room gives `k_{a+j} = 3ʲkₐ`
and `v₂(m_{a+j}) + j = v₂(mₐ)`.  Combined with the converse already in the root
(`BB13.sameTower_dvd`, `BB13.sameTower_resid`) this turns the report's §1.2 *computed* formula into
an equivalence:

> **`mem_lineFibre_add_iff`**: for `a ≥ 3`,
> `a + d ∈ lineFibre (linePoint a) ↔ d ≤ v₂(mₐ) ∧ 2ᵈ|kₐ|2ᵃ < 3ᵃ`.

The right-hand side is `d ≤ min(v₂(mₐ), D(a))` with `D(a)` the dyadic surplus, so the fibre over
its least element is the interval `[a, a + min(v₂(mₐ), D(a))]` (`lineFibre_eq_Icc`,
`lineFibre_ncard_eq`).  The two arms are its two ends — exactly the block dictionary of
`BB13/CarryTransducer.lean` §4, now proved on the fibre side as well.

## The residue-class prong, and where it stops

A4's surviving idea was to feed `a ≡ log₃ kₐ (mod 2^{w−2})` back as a stratification of the indices
that can carry long fibres.  The congruence is a theorem — the low-bit companion of
`BB13.selfRef_dvd_sub` — and it is sharp:

> **`resid_congr_index_congr`**: for `3 ≤ M ≤ a ≤ b`, `kₐ ≡ k_b (mod 2ᴹ)` forces `2^{M−2} ∣ b − a`,
> hence `b ≥ a + 2^{M−2}` (`resid_congr_gap`).

Prescribing `M` low-order bits of the residue costs a gap `2^{M−2}`: a genuine repulsion, doubly
exponential in the information prescribed.  But it stratifies by the **low** bits of `kₐ`, while a
fibre of height `H` prescribes the `2`-adic depth of `mₐ` — a condition on `3ᵃ` modulo `2^{a+H}`,
not modulo `2^H` — and the **high** bits of `kₐ` through `D(a)`.  The conversion A4 wanted, "fibre
`≥ H` forces `a` into explicit classes mod `2^{H−O(1)}`", needs a modulus that grows with `a` and
is vacuous at any fixed one: `BB13/b8_least_exception.py` [E] finds the indices with
`v₂(mₐ) ≥ H−1` spread over the classes mod `2^{H−2}` exactly as a random set of that size would be.
See `CB17`.

## What it costs, and what it buys

The bottom lemma constrains the *predecessor*, not the bottom.  The step from depth `≤ 1` upward is
the one step the carry does not control — `cₙ = ±1` for odd `mₙ`, and then `v₂(m_{n+1})` is
whatever `3mₙ ∓ 1` happens to give.  Concretely `v₂(m_{a+1}) = w` at a bottom is the congruence
`mₐ ≡ ±3⁻¹` or `±2·3⁻¹ (mod 2^{w+1})` — four classes out of `2^{w+1}` — which is a condition on the
binary window of `3ᵃ` at bit `a`, i.e. B7's milestone 2 again, priced at `0%` in
`plans/note-BB13-B7.html`.  So: **structural lemma delivered, route not opened**.  The tall bottoms
of the census all satisfy `v₂(m_{a−1}) ≤ 1` while `v₂(mₐ)` grows freely
(`tall_bottom_sixty_three`).

## Back-port

Everything through `vTwo_succ_lt` is `q`-adic and generic: for coprime `p > q ≥ 2` the carry
identity `q·m_{n+1} = p·mₙ + cₙ` with `|cₙ| ≤ q` gives the same descent law above depth
`⌈log_q(2q)⌉`.  Only the headline pair is formalized here.

Footprint: `std3` — no cited axiom, no `sorry`.

## References

* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*, Cambridge Tracts
  **193**, 2012 — Problem 10.13.
* [DD90] F. Delmer, J.-M. Deshouillers, *The computation of `g(k)` in Waring's problem*, Math.
  Comp. **54** (1990), 885–893 — the exact-integer `(3/2)`-recursion this file formalizes.
* `plans/report3-BB13.html` §6 B8 (the item), §8 `CB4` (corrected here by `CB16`), §9.
* `plans/note-BB13-B8.html` (the note), `BB13/b8_least_exception.py` (the evidence).
-/

namespace BB13

open scoped Real

/-! ### The carry of the rounding recurrence -/

/-- **The carry** `cₙ = 2m_{n+1} − 3mₙ` of the `(3/2)`-recursion: the exact defect of the naive
step `m_{n+1} = 3mₙ/2`.  It takes all five values `−2, −1, 0, 1, 2` (`carry_alphabet`). -/
noncomputable def carry (n : ℕ) : ℤ := 2 * Mnum 3 2 (n + 1) - 3 * Mnum 3 2 n

/-- The defining identity `2m_{n+1} = 3mₙ + cₙ`. -/
@[category API, AMS 11, ref "DD90", group "bugeaud_10_13"]
theorem two_mul_Mnum_succ (n : ℕ) : 2 * Mnum 3 2 (n + 1) = 3 * Mnum 3 2 n + carry n := by
  rw [carry]; ring

/-- **The residue recursion** `k_{n+1} = 3kₙ − cₙ2ⁿ` — the `k`-component of the exact step.  With
`two_mul_Mnum_succ` this is the whole rounding recurrence of [DD90]. -/
@[category research solved, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem resid_succ (n : ℕ) : resid 3 2 (n + 1) = 3 * resid 3 2 n - carry n * 2 ^ n := by
  simp only [resid, carry]
  push_cast
  ring

/-- **The parity law** `cₙ ≡ mₙ (mod 2)`: the carry is even exactly when `mₙ` is. -/
@[category API, AMS 11, ref "DD90", group "bugeaud_10_13"]
theorem carry_parity (n : ℕ) : (2 : ℤ) ∣ carry n - Mnum 3 2 n :=
  ⟨Mnum 3 2 (n + 1) - 2 * Mnum 3 2 n, by rw [carry]; ring⟩

/-- The carry inherits the parity of `mₙ`: if `mₙ` is even, so is `cₙ`. -/
@[category API, AMS 11, ref "DD90", group "bugeaud_10_13"]
theorem two_dvd_carry (n : ℕ) (he : (2 : ℤ) ∣ Mnum 3 2 n) : (2 : ℤ) ∣ carry n := by
  have h : carry n = (carry n - Mnum 3 2 n) + Mnum 3 2 n := by ring
  rw [h]
  exact dvd_add (carry_parity n) he

/-- The nearest-integer bound in integer form: `2|kₙ| ≤ 2ⁿ`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem two_mul_abs_resid_le (n : ℕ) : 2 * |resid 3 2 n| ≤ 2 ^ n := by
  have h := abs_resid_le n
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)] at h
  have hcast : ((2 * |resid 3 2 n| : ℤ) : ℝ) ≤ ((2 ^ n : ℤ) : ℝ) := by
    push_cast
    linarith [h]
  exact_mod_cast hcast

/-- **The carry alphabet is bounded**: `|cₙ| ≤ 2`.  Both residues obey the nearest-integer bound,
so `|cₙ|2ⁿ = |3kₙ − k_{n+1}| ≤ (3/2 + 1)·2ⁿ`, and `5/2 < 3`. -/
@[category research solved, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem abs_carry_le_two (n : ℕ) : |carry n| ≤ 2 := by
  have hP : (0 : ℤ) < 2 ^ n := by positivity
  have hid : carry n * 2 ^ n = 3 * resid 3 2 n - resid 3 2 (n + 1) := by
    have := resid_succ n; linarith
  have hx := two_mul_abs_resid_le n
  have hy := two_mul_abs_resid_le (n + 1)
  have hpow : (2 : ℤ) ^ (n + 1) = 2 * 2 ^ n := by ring
  rw [hpow] at hy
  have hx1 : resid 3 2 n ≤ |resid 3 2 n| := le_abs_self _
  have hx2 : -|resid 3 2 n| ≤ resid 3 2 n := neg_abs_le _
  have hy1 : resid 3 2 (n + 1) ≤ |resid 3 2 (n + 1)| := le_abs_self _
  have hy2 : -|resid 3 2 (n + 1)| ≤ resid 3 2 (n + 1) := neg_abs_le _
  refine abs_le.mpr ⟨?_, ?_⟩
  · by_contra hcon
    have h3 : carry n ≤ -3 := by omega
    have hmul : carry n * 2 ^ n ≤ -3 * 2 ^ n := mul_le_mul_of_nonneg_right h3 (le_of_lt hP)
    linarith
  · by_contra hcon
    have h3 : (3 : ℤ) ≤ carry n := by omega
    have hmul : (3 : ℤ) * 2 ^ n ≤ carry n * 2 ^ n :=
      mul_le_mul_of_nonneg_right h3 (le_of_lt hP)
    linarith

/-- **The carry vanishes when the numerator is even and the residue small**: if `2 ∣ mₙ` and
`3|kₙ| < 2ⁿ` then `cₙ = 0`, so `k_{n+1} = 3kₙ` and `2m_{n+1} = 3mₙ`.  A carry `±2` would push
`|k_{n+1}| = |3kₙ ∓ 2ⁿ⁺¹|` past the nearest-integer bound `2ⁿ`. -/
@[category research solved, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem carry_eq_zero_of_even_of_small {n : ℕ} (he : (2 : ℤ) ∣ Mnum 3 2 n)
    (hs : 3 * |resid 3 2 n| < 2 ^ n) : carry n = 0 := by
  have hP : (0 : ℤ) < 2 ^ n := by positivity
  obtain ⟨t, ht⟩ := two_dvd_carry n he
  have hbd := abs_carry_le_two n
  rw [ht, abs_mul, show |(2 : ℤ)| = 2 by decide] at hbd
  have htb : -1 ≤ t ∧ t ≤ 1 := by
    have := abs_le.mp (by omega : |t| ≤ 1)
    exact this
  have hid : resid 3 2 (n + 1) = 3 * resid 3 2 n - carry n * 2 ^ n := resid_succ n
  have hy : 2 * |resid 3 2 (n + 1)| ≤ 2 ^ (n + 1) := two_mul_abs_resid_le (n + 1)
  have hpow : (2 : ℤ) ^ (n + 1) = 2 * 2 ^ n := by ring
  have hy1 : 2 * resid 3 2 (n + 1) ≤ 2 * 2 ^ n := by
    have := le_abs_self (resid 3 2 (n + 1)); rw [hpow] at hy; linarith
  have hy2 : -(2 * 2 ^ n) ≤ 2 * resid 3 2 (n + 1) := by
    have := neg_abs_le (resid 3 2 (n + 1)); rw [hpow] at hy; linarith
  have hx1 : 3 * resid 3 2 n < 2 ^ n := by
    have := le_abs_self (resid 3 2 n); linarith
  have hx2 : -(2 ^ n) < 3 * resid 3 2 n := by
    have := neg_abs_le (resid 3 2 n); linarith
  rcases (by omega : t = -1 ∨ t = 0 ∨ t = 1) with h | h | h
  · exfalso
    have hc : carry n = -2 := by rw [ht, h]; ring
    rw [hc] at hid
    linarith
  · rw [ht, h]; ring
  · exfalso
    have hc : carry n = 2 := by rw [ht, h]; ring
    rw [hc] at hid
    linarith

/-- With `mₙ` even, a nonzero carry is `±2`. -/
@[category API, AMS 11, ref "DD90", group "bugeaud_10_13"]
theorem carry_eq_two_or_neg_two {n : ℕ} (he : (2 : ℤ) ∣ Mnum 3 2 n) (hne : carry n ≠ 0) :
    carry n = 2 ∨ carry n = -2 := by
  obtain ⟨t, ht⟩ := two_dvd_carry n he
  have hbd := abs_carry_le_two n
  rw [ht, abs_mul, show |(2 : ℤ)| = 2 by decide] at hbd
  have htb : -1 ≤ t ∧ t ≤ 1 := abs_le.mp (by omega : |t| ≤ 1)
  rcases (by omega : t = -1 ∨ t = 0 ∨ t = 1) with h | h | h
  · exact Or.inr (by rw [ht, h]; ring)
  · exact absurd (by rw [ht, h]; ring) hne
  · exact Or.inl (by rw [ht, h]; ring)

/-! ### The descent law of the `2`-adic arm -/

/-- `2ʲ ∣ 3x → 2ʲ ∣ x`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem two_pow_dvd_of_dvd_three_mul {j : ℕ} {x : ℤ} (h : (2 : ℤ) ^ j ∣ 3 * x) :
    (2 : ℤ) ^ j ∣ x :=
  (IsCoprime.pow_left (⟨-1, 1, by ring⟩ : IsCoprime (2 : ℤ) 3)).dvd_of_dvd_mul_left h

/-- **The line step costs one unit of `2`-adic depth**: a vanishing carry gives
`v₂(m_{n+1}) + 1 = v₂(mₙ)`. -/
@[category research solved, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem vTwo_succ_of_carry_zero {n : ℕ} (hv : 1 ≤ vTwo n) (h : carry n = 0) :
    vTwo (n + 1) + 1 = vTwo n := by
  have hm : 2 * Mnum 3 2 (n + 1) = 3 * Mnum 3 2 n := by rw [two_mul_Mnum_succ, h]; ring
  have hge : vTwo n - 1 ≤ vTwo (n + 1) := by
    refine le_vTwo_of_dvd (D := vTwo n - 1) ?_
    have hd : 2 * (2 : ℤ) ^ (vTwo n - 1) ∣ 2 * Mnum 3 2 (n + 1) := by
      rw [hm]
      refine dvd_trans ?_ (Dvd.dvd.mul_left (two_pow_vTwo_dvd n) 3)
      rw [show 2 * (2 : ℤ) ^ (vTwo n - 1) = 2 ^ (vTwo n - 1 + 1) by ring]
      exact pow_dvd_pow 2 (by omega)
    exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp hd
  have hle : vTwo (n + 1) + 1 ≤ vTwo n := by
    refine le_vTwo_of_dvd (D := vTwo (n + 1) + 1) (two_pow_dvd_of_dvd_three_mul ?_)
    rw [← hm, pow_succ, mul_comm ((2 : ℤ) ^ vTwo (n + 1)) 2]
    exact mul_dvd_mul_left 2 (two_pow_vTwo_dvd (n + 1))
  omega

/-- **The crash**: with `4 ∣ mₙ`, a nonzero carry makes `m_{n+1}` odd.  Indeed `2m_{n+1} = 3mₙ ± 2`
with `4 ∣ 3mₙ`, so `4 ∤ 2m_{n+1}`. -/
@[category research solved, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem vTwo_succ_eq_zero_of_carry_ne {n : ℕ} (hv : 2 ≤ vTwo n) (h : carry n ≠ 0) :
    vTwo (n + 1) = 0 := by
  have h4 : (4 : ℤ) ∣ Mnum 3 2 n := by
    have hd := dvd_trans (pow_dvd_pow (2 : ℤ) hv) (two_pow_vTwo_dvd n)
    norm_num at hd
    exact hd
  have he : (2 : ℤ) ∣ Mnum 3 2 n := dvd_trans (by norm_num) h4
  by_contra hne
  have hodd : (2 : ℤ) ∣ Mnum 3 2 (n + 1) := by
    have h1 : (1 : ℕ) ≤ vTwo (n + 1) := Nat.one_le_iff_ne_zero.mpr hne
    have := dvd_trans (pow_dvd_pow (2 : ℤ) h1) (two_pow_vTwo_dvd (n + 1))
    simpa using this
  obtain ⟨u, hu⟩ := hodd
  have h4' : (4 : ℤ) ∣ 3 * Mnum 3 2 n + carry n := by
    rw [← two_mul_Mnum_succ, hu]
    exact ⟨u, by ring⟩
  have hc4 : (4 : ℤ) ∣ carry n := by
    have hsplit : carry n = (3 * Mnum 3 2 n + carry n) - 3 * Mnum 3 2 n := by ring
    rw [hsplit]
    exact dvd_sub h4' (Dvd.dvd.mul_left h4 3)
  rcases carry_eq_two_or_neg_two he h with h2 | h2 <;> rw [h2] at hc4 <;> norm_num at hc4

/-- **The step dichotomy of the `2`-adic arm** (report §6 B8).  Above depth `1` the valuation
either drops by exactly one — and then `n`, `n+1` lie on one line — or crashes to `0`. -/
@[category research solved, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem vTwo_step_dichotomy {n : ℕ} (hv : 2 ≤ vTwo n) :
    vTwo (n + 1) + 1 = vTwo n ∨ vTwo (n + 1) = 0 := by
  by_cases h : carry n = 0
  · exact Or.inl (vTwo_succ_of_carry_zero (by omega) h)
  · exact Or.inr (vTwo_succ_eq_zero_of_carry_ne hv h)

/-- **The `2`-adic arm never rises except from depth `≤ 1`**: `v₂(mₙ) ≥ 2 ⟹ v₂(m_{n+1}) < v₂(mₙ)`.

This is the structural lemma B8 asks for: the sequence `v₂(mₙ)` is a disjoint union of strictly
descending runs, each begun at an index whose predecessor has depth `0` or `1`. -/
@[category research solved, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem vTwo_succ_lt {n : ℕ} (hv : 2 ≤ vTwo n) : vTwo (n + 1) < vTwo n := by
  rcases vTwo_step_dichotomy hv with h | h <;> omega

/-! ### The bottom lemma: A2's strategy X, corrected -/

/-- **The bottom lemma.**  If `m_{a+1}` is even and the carry at `a` does not vanish, then
`v₂(mₐ) ≤ 1`.  (Contrapositive of the dichotomy: depth `≥ 2` at `a` leaves only *descend along the
line* and *crash to `0`*, and both are excluded.) -/
@[category research solved, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem vTwo_le_one_of_bottom {a : ℕ} (hv : 1 ≤ vTwo (a + 1)) (hb : carry a ≠ 0) : vTwo a ≤ 1 := by
  by_contra hcon
  exact absurd (vTwo_succ_eq_zero_of_carry_ne (by omega) hb) (by omega)

/-- A vanishing carry is a step along a line. -/
@[category research solved, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem resid_succ_of_carry_zero {n : ℕ} (h : carry n = 0) :
    resid 3 2 (n + 1) = 3 * resid 3 2 n := by
  rw [resid_succ, h]; ring

/-- **A line is a chain of vanishing carries**: `k_b = 3^{b−a}kₐ` is the same thing as
`SameTower a b`.  The forward direction is `BB13.sameTower_resid`; this is the converse, which the
descent law needs in order to convert carries into fibre membership. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem sameTower_of_resid_eq {a b : ℕ} (hab : a ≤ b)
    (h : resid 3 2 b = (3 : ℤ) ^ (b - a) * resid 3 2 a) : SameTower a b := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  simp only [Nat.add_sub_cancel_left] at h
  have hx : ∀ n : ℕ, frameX n = 3 ^ n - resid 3 2 n := by
    intro n; simp only [frameX, resid]; push_cast; ring
  have key : frameX a * frameY (a + d) = frameX (a + d) * frameY a := by
    simp only [hx, frameY, h]
    ring
  have hya : ((frameY a : ℤ) : ℚ) ≠ 0 := by
    have := frameY_pos a; exact_mod_cast this.ne'
  have hyb : ((frameY (a + d) : ℤ) : ℚ) ≠ 0 := by
    have := frameY_pos (a + d); exact_mod_cast this.ne'
  rw [SameTower, linePoint, linePoint, div_eq_div_iff hya hyb]
  exact_mod_cast key

/-- Unfolding of the failure condition in exact-integer form: `a ∈ 𝓔 ↔ |kₐ|2ᵃ < 3ᵃ`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem isFailure_iff_int (a : ℕ) :
    IsFailure 3 2 (3 / 4) a ↔ |resid 3 2 a| * 2 ^ a < 3 ^ a := by
  rw [isFailure_iff_abs_resid_lt]
  have h2 : (0 : ℝ) < (2 : ℝ) ^ a := by positivity
  have hmul : (3 / 2 : ℝ) ^ a * 2 ^ a = 3 ^ a := by rw [← mul_pow]; norm_num
  constructor
  · intro h
    have key : |((resid 3 2 a : ℤ) : ℝ)| * 2 ^ a < 3 ^ a :=
      hmul ▸ mul_lt_mul_of_pos_right h h2
    exact_mod_cast key
  · intro h
    have key : |((resid 3 2 a : ℤ) : ℝ)| * 2 ^ a < 3 ^ a := by exact_mod_cast h
    rw [← hmul] at key
    exact lt_of_mul_lt_mul_right key (le_of_lt h2)

/-- **The least exception of a line has a shallow predecessor**: `v₂(m_{a−1}) ≤ 1`.

Stated at `a + 1`: if `a + 1` is a failure with `v₂(m_{a+1}) ≥ 1` and no smaller index lies on its
line, then `v₂(mₐ) ≤ 1`.  A2's strategy X asserted `= 0`; `CB4` asserted "unconstrained".  Both are
wrong, and this is what is true (`CB16`). -/
@[category research solved, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem least_exception_vTwo_pred_le_one {a : ℕ} (ha : 1 ≤ a)
    (hf : IsFailure 3 2 (3 / 4) (a + 1)) (hv : 1 ≤ vTwo (a + 1))
    (hmin : ∀ b ∈ lineFibre (linePoint (a + 1)), a + 1 ≤ b) : vTwo a ≤ 1 := by
  refine vTwo_le_one_of_bottom hv ?_
  intro hc
  -- a vanishing carry puts `a` on the line of `a+1`, and its residue is three times smaller
  have hk : resid 3 2 (a + 1) = 3 * resid 3 2 a := resid_succ_of_carry_zero hc
  have hsame : SameTower a (a + 1) :=
    sameTower_of_resid_eq (by omega) (by rw [hk, show a + 1 - a = 1 by omega]; ring)
  have hfint := (isFailure_iff_int (a + 1)).mp hf
  rw [hk, abs_mul, show |(3 : ℤ)| = 3 by decide] at hfint
  have hfa : IsFailure 3 2 (3 / 4) a := by
    rw [isFailure_iff_int]
    have hp : (0 : ℤ) < 2 ^ a := by positivity
    have h1 : (3 : ℤ) * (|resid 3 2 a| * 2 ^ (a + 1)) < 3 * 3 ^ a := by
      calc (3 : ℤ) * (|resid 3 2 a| * 2 ^ (a + 1)) = 3 * |resid 3 2 a| * 2 ^ (a + 1) := by ring
        _ < 3 ^ (a + 1) := hfint
        _ = 3 * 3 ^ a := by ring
    have h2 : |resid 3 2 a| * 2 ^ (a + 1) < 3 ^ a := by linarith
    have h3 : |resid 3 2 a| * 2 ^ a ≤ |resid 3 2 a| * 2 ^ (a + 1) := by
      have := abs_nonneg (resid 3 2 a)
      have hle : (2 : ℤ) ^ a ≤ 2 ^ (a + 1) := by
        have : (2 : ℤ) ^ (a + 1) = 2 * 2 ^ a := by ring
        linarith
      exact mul_le_mul_of_nonneg_left hle this
    linarith
  exact absurd (hmin a ⟨ha, hfa, hsame⟩) (by omega)

/-! ### Running the descent forward: the fibre is exactly `1 + min(v₂(mₐ), D(a))` -/

/-- `2·3ᵐ ≤ 4ᵐ` for `m ≥ 3` — the one numeric fact that converts a dyadic surplus into archimedean
room for the descent.  (`2·27 = 54 ≤ 64`, and `4/3 > 1` thereafter.) -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem two_mul_three_pow_le_four_pow {m : ℕ} (hm : 3 ≤ m) : 2 * (3 : ℤ) ^ m ≤ 4 ^ m := by
  induction m with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 3 with hk | hk
    · have hk2 : k = 2 := by omega
      subst hk2; norm_num
    · have h4 : (0 : ℤ) < 4 ^ k := by positivity
      calc 2 * (3 : ℤ) ^ (k + 1) = 3 * (2 * 3 ^ k) := by ring
        _ ≤ 3 * 4 ^ k := by linarith [ih (by omega)]
        _ ≤ 4 ^ (k + 1) := by rw [pow_succ]; linarith

/-- **The descent runs**: if `j ≤ v₂(mₐ)` and there is archimedean room `2·3ʲ|kₐ| < 2^{a+j}`, then
the line through `a` reaches `a + j`: `k_{a+j} = 3ʲkₐ` and `v₂(m_{a+j}) + j = v₂(mₐ)`. -/
@[category research solved, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem line_extends {a : ℕ} : ∀ j : ℕ, j ≤ vTwo a → 2 * 3 ^ j * |resid 3 2 a| < 2 ^ (a + j) →
    resid 3 2 (a + j) = 3 ^ j * resid 3 2 a ∧ vTwo (a + j) + j = vTwo a := by
  intro j
  induction j with
  | zero => intro _ _; simp
  | succ j ih =>
    intro hj harch
    have hY : (0 : ℤ) < 2 ^ (a + j) := by positivity
    have hpow2 : (2 : ℤ) ^ (a + (j + 1)) = 2 * 2 ^ (a + j) := by
      rw [show a + (j + 1) = (a + j) + 1 by omega]; ring
    have hpow3 : (3 : ℤ) ^ (j + 1) = 3 * 3 ^ j := by ring
    rw [hpow2, hpow3] at harch
    -- the binding condition at the last step, and the (weaker) one for the induction hypothesis
    have hstep : 3 * (3 ^ j * |resid 3 2 a|) < 2 ^ (a + j) := by linarith
    have harchj : 2 * 3 ^ j * |resid 3 2 a| < 2 ^ (a + j) := by
      have hnn : (0 : ℤ) ≤ 3 ^ j * |resid 3 2 a| := by positivity
      linarith
    obtain ⟨hk, hw⟩ := ih (by omega) harchj
    have hv1 : 1 ≤ vTwo (a + j) := by omega
    have he : (2 : ℤ) ∣ Mnum 3 2 (a + j) := by
      have := dvd_trans (pow_dvd_pow (2 : ℤ) hv1) (two_pow_vTwo_dvd (a + j))
      simpa using this
    have hsmall : 3 * |resid 3 2 (a + j)| < 2 ^ (a + j) := by
      rw [hk, abs_mul, abs_pow, show |(3 : ℤ)| = 3 by decide]
      linarith
    have hc := carry_eq_zero_of_even_of_small he hsmall
    have hnext : a + (j + 1) = (a + j) + 1 := by omega
    refine ⟨?_, ?_⟩
    · rw [hnext, resid_succ_of_carry_zero hc, hk, hpow3]; ring
    · rw [hnext]
      have := vTwo_succ_of_carry_zero hv1 hc
      omega

/-- **The fibre identity** (report §1.2, now an equivalence).  For `a ≥ 3`,

`a + d ∈ lineFibre (linePoint a) ↔ d ≤ v₂(mₐ) ∧ 2ᵈ|kₐ|2ᵃ < 3ᵃ`,

the right-hand side being `d ≤ min(v₂(mₐ), D(a))`.  Forward: `BB13.sameTower_dvd` gives the `v`
arm, `BB13.sameTower_resid` plus the failure condition the `D` arm.  Backward: `line_extends`. -/
@[category research solved, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem mem_lineFibre_add_iff {a : ℕ} (ha : 3 ≤ a) (d : ℕ) :
    a + d ∈ lineFibre (linePoint a) ↔
      d ≤ vTwo a ∧ 2 ^ d * |resid 3 2 a| * 2 ^ a < 3 ^ a := by
  have hd3 : (0 : ℤ) < 3 ^ d := by positivity
  have hcut : a + d - a = d := by omega
  constructor
  · rintro ⟨-, hfd, hslope⟩
    have hst : SameTower a (a + d) := hslope.symm
    have hdvd : (2 : ℤ) ^ d ∣ Mnum 3 2 a := by
      have := sameTower_dvd (by omega : a ≤ a + d) hst
      rwa [hcut] at this
    have hres : resid 3 2 (a + d) = 3 ^ d * resid 3 2 a := by
      have := sameTower_resid (by omega : a ≤ a + d) hst
      rwa [hcut] at this
    refine ⟨le_vTwo_of_dvd hdvd, ?_⟩
    have hint := (isFailure_iff_int (a + d)).mp hfd
    rw [hres, abs_mul, abs_pow, show |(3 : ℤ)| = 3 by decide] at hint
    have hsplit : (3 : ℤ) ^ d * (2 ^ d * |resid 3 2 a| * 2 ^ a) < 3 ^ d * 3 ^ a := by
      calc (3 : ℤ) ^ d * (2 ^ d * |resid 3 2 a| * 2 ^ a)
          = 3 ^ d * |resid 3 2 a| * 2 ^ (a + d) := by rw [pow_add]; ring
        _ < 3 ^ (a + d) := hint
        _ = 3 ^ d * 3 ^ a := by rw [pow_add]; ring
    exact lt_of_mul_lt_mul_left hsplit (le_of_lt hd3)
  · rintro ⟨hv, hD⟩
    have hpad : (0 : ℤ) < 2 ^ (a + d) := by positivity
    have hDD : |resid 3 2 a| * 2 ^ (a + d) < 3 ^ a := by
      calc |resid 3 2 a| * 2 ^ (a + d) = 2 ^ d * |resid 3 2 a| * 2 ^ a := by rw [pow_add]; ring
        _ < 3 ^ a := hD
    -- archimedean room for `line_extends`
    have harch : 2 * 3 ^ d * |resid 3 2 a| < 2 ^ (a + d) := by
      have hmul : (2 * 3 ^ d * |resid 3 2 a|) * 2 ^ (a + d) < 2 ^ (a + d) * 2 ^ (a + d) := by
        calc (2 * 3 ^ d * |resid 3 2 a|) * 2 ^ (a + d)
            = 2 * 3 ^ d * (|resid 3 2 a| * 2 ^ (a + d)) := by ring
          _ < 2 * 3 ^ d * 3 ^ a := by
              have : (0 : ℤ) < 2 * 3 ^ d := by positivity
              exact mul_lt_mul_of_pos_left hDD this
          _ = 2 * 3 ^ (a + d) := by rw [pow_add]; ring
          _ ≤ 4 ^ (a + d) := two_mul_three_pow_le_four_pow (by omega)
          _ = 2 ^ (a + d) * 2 ^ (a + d) := by
              rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
              congr 1
              omega
      exact lt_of_mul_lt_mul_right hmul (le_of_lt hpad)
    obtain ⟨hres, -⟩ := line_extends d hv harch
    refine ⟨by omega, ?_, ?_⟩
    · rw [isFailure_iff_int, hres, abs_mul, abs_pow, show |(3 : ℤ)| = 3 by decide]
      calc (3 : ℤ) ^ d * |resid 3 2 a| * 2 ^ (a + d)
          = 3 ^ d * (|resid 3 2 a| * 2 ^ (a + d)) := by ring
        _ < 3 ^ d * 3 ^ a := mul_lt_mul_of_pos_left hDD hd3
        _ = 3 ^ (a + d) := by rw [pow_add]; ring
    · exact (sameTower_of_resid_eq (by omega) (by rwa [hcut])).symm

/-- **The fibre over its least element is an interval.**  If `d` is the largest admissible step —
`d ≤ v₂(mₐ)` and `2ᵈ|kₐ|2ᵃ < 3ᵃ`, but not both at `d + 1` — then the whole line-fibre is
`[a, a + d]`. -/
@[category research solved, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem lineFibre_eq_Icc {a d : ℕ} (ha : 3 ≤ a)
    (hmin : ∀ b ∈ lineFibre (linePoint a), a ≤ b)
    (hin : d ≤ vTwo a ∧ 2 ^ d * |resid 3 2 a| * 2 ^ a < 3 ^ a)
    (hout : ¬ (d + 1 ≤ vTwo a ∧ 2 ^ (d + 1) * |resid 3 2 a| * 2 ^ a < 3 ^ a)) :
    lineFibre (linePoint a) = ↑(Finset.Icc a (a + d)) := by
  have hmono : ∀ e f : ℕ, e ≤ f → 2 ^ e * |resid 3 2 a| * 2 ^ a ≤ 2 ^ f * |resid 3 2 a| * 2 ^ a := by
    intro e f hef
    have h1 : (2 : ℤ) ^ e ≤ 2 ^ f := pow_le_pow_right₀ (by norm_num) hef
    have h2 : (0 : ℤ) ≤ |resid 3 2 a| * 2 ^ a := by positivity
    calc 2 ^ e * |resid 3 2 a| * 2 ^ a = 2 ^ e * (|resid 3 2 a| * 2 ^ a) := by ring
      _ ≤ 2 ^ f * (|resid 3 2 a| * 2 ^ a) := mul_le_mul_of_nonneg_right h1 h2
      _ = 2 ^ f * |resid 3 2 a| * 2 ^ a := by ring
  ext n
  simp only [Finset.coe_Icc, Set.mem_Icc]
  constructor
  · intro hn
    have han : a ≤ n := hmin n hn
    obtain ⟨e, rfl⟩ : ∃ e, n = a + e := ⟨n - a, by omega⟩
    obtain ⟨hv, hD⟩ := (mem_lineFibre_add_iff ha e).mp hn
    refine ⟨by omega, ?_⟩
    by_contra hcon
    exact hout ⟨by omega, lt_of_le_of_lt (hmono (d + 1) e (by omega)) hD⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨e, rfl⟩ : ∃ e, n = a + e := ⟨n - a, by omega⟩
    refine (mem_lineFibre_add_iff ha e).mpr ⟨by omega, ?_⟩
    exact lt_of_le_of_lt (hmono e d (by omega)) hin.2

/-- **The fibre count is exactly `1 + min(v₂(mₐ), D(a))`** — the report's §1.2 formula, proved. -/
@[category research solved, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem lineFibre_ncard_eq {a d : ℕ} (ha : 3 ≤ a)
    (hmin : ∀ b ∈ lineFibre (linePoint a), a ≤ b)
    (hin : d ≤ vTwo a ∧ 2 ^ d * |resid 3 2 a| * 2 ^ a < 3 ^ a)
    (hout : ¬ (d + 1 ≤ vTwo a ∧ 2 ^ (d + 1) * |resid 3 2 a| * 2 ^ a < 3 ^ a)) :
    (lineFibre (linePoint a)).ncard = d + 1 := by
  rw [lineFibre_eq_Icc ha hmin hin hout, Set.ncard_coe_finset, Nat.card_Icc]
  omega

/-! ### The residue-class stratification, and its gap -/

/-- `3ᵃ ≡ kₐ (mod 2ᴹ)` for every `M ≤ a` — the low-order half of `BB13.three_pow_sub_resid`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem two_pow_dvd_three_pow_sub_resid_of_le {M a : ℕ} (hMa : M ≤ a) :
    (2 : ℤ) ^ M ∣ 3 ^ a - resid 3 2 a := by
  rw [three_pow_sub_resid]
  exact Dvd.dvd.mul_left (pow_dvd_pow 2 hMa) _

/-- **The stratification**: for `3 ≤ M ≤ a ≤ b`, a congruence `kₐ ≡ k_b (mod 2ᴹ)` between the two
residues forces `2^{M−2} ∣ b − a`.  Prescribing `M` low-order bits of the residue prescribes the
index modulo `2^{M−2}` — the order of `3` in `(ℤ/2ᴹ)ˣ` (`BB13.two_pow_dvd_three_pow_sub_one_iff`).

This is the low-bit companion of `BB13.selfRef_dvd_sub`, which does the same for indices of high
`2`-adic depth against a common `k`. -/
@[category research solved, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem resid_congr_index_congr {M a b : ℕ} (hM : 3 ≤ M) (hMa : M ≤ a) (hab : a ≤ b)
    (h : (2 : ℤ) ^ M ∣ resid 3 2 b - resid 3 2 a) : 2 ^ (M - 2) ∣ b - a := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  have h1 := two_pow_dvd_three_pow_sub_resid_of_le (M := M) (a := a) hMa
  have h2 := two_pow_dvd_three_pow_sub_resid_of_le (M := M) (a := a + d) (by omega)
  have h3 : (2 : ℤ) ^ M ∣ 3 ^ a * (3 ^ d - 1) := by
    have hexp : (3 : ℤ) ^ a * (3 ^ d - 1)
        = ((3 : ℤ) ^ (a + d) - resid 3 2 (a + d)) - (3 ^ a - resid 3 2 a)
          + (resid 3 2 (a + d) - resid 3 2 a) := by
      rw [pow_add]; ring
    rw [hexp]
    exact dvd_add (dvd_sub h2 h1) h
  have hcop : IsCoprime ((2 : ℤ) ^ M) ((3 : ℤ) ^ a) :=
    IsCoprime.pow (⟨-1, 1, by ring⟩ : IsCoprime (2 : ℤ) 3)
  have h4 : (2 : ℤ) ^ M ∣ 3 ^ d - 1 := hcop.dvd_of_dvd_mul_left h3
  simpa using (two_pow_dvd_three_pow_sub_one_iff hM).mp h4

/-- **The repulsion this buys**: two distinct indices whose residues agree modulo `2ᴹ` are at least
`2^{M−2}` apart.  Doubly exponential in the information prescribed — and prescribed on the *low*
bits of `kₐ`, which is the wrong end for a fibre condition (see the module docstring, `CB17`). -/
@[category research solved, AMS 11, ref "Bug12" "DD90", group "bugeaud_10_13"]
theorem resid_congr_gap {M a b : ℕ} (hM : 3 ≤ M) (hMa : M ≤ a) (hab : a < b)
    (h : (2 : ℤ) ^ M ∣ resid 3 2 b - resid 3 2 a) : a + 2 ^ (M - 2) ≤ b := by
  have hdvd := resid_congr_index_congr hM hMa (le_of_lt hab) h
  have hpos : 0 < b - a := by omega
  have := Nat.le_of_dvd hpos hdvd
  omega

/-! ### The census witnesses

`BB13.mNat` is the decidable `ℕ`-mirror of `Mnum 3 2` (`BB13.Mnum_eq_mNat`), so the carry and the
valuations at small indices are kernel-checkable. -/

/-- The carry in decidable form. -/
@[category API, AMS 11, ref "DD90", group "bugeaud_10_13"]
theorem carry_eq_mNat (n : ℕ) : carry n = 2 * (mNat (n + 1) : ℤ) - 3 * (mNat n : ℤ) := by
  rw [carry, Mnum_eq_mNat, Mnum_eq_mNat]

/-- **All five carries occur** — so the naive recurrence `m_{n+1} = round(3mₙ/2)`, which asserts
`|cₙ| ≤ 1`, is false: `c₁ = −2` and `c₉ = 2`. -/
@[category test, AMS 11, ref "DD90", group "bugeaud_10_13"]
theorem carry_alphabet :
    carry 1 = -2 ∧ carry 2 = 0 ∧ carry 3 = 1 ∧ carry 9 = 2 ∧ carry 13 = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (rw [carry_eq_mNat]; decide)

/-- A bottom with `v₂(m_{a−1}) = 1`: at `a = 9`, `v₂(m₈) = v₂(m₉) = 1` and `c₈ = −2 ≠ 0`.
This refutes A2's strategy X in its original form (`v₂(m_{a−1}) = 0`). -/
@[category test, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem bottom_pred_one : vTwo 8 = 1 ∧ vTwo 9 = 1 ∧ carry 8 ≠ 0 :=
  ⟨vTwo_eq_of_mNat (by decide) (by decide), vTwo_eq_of_mNat (by decide) (by decide),
    by rw [carry_eq_mNat]; decide⟩

/-- A bottom with `v₂(m_{a−1}) = 0`: at `a = 5`, `v₂(m₄) = 0`, `v₂(m₅) = 3` and `c₄ = 1 ≠ 0`.  With
`bottom_pred_one` this shows `vTwo_le_one_of_bottom` is sharp: both values occur. -/
@[category test, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem bottom_pred_zero : vTwo 4 = 0 ∧ vTwo 5 = 3 ∧ carry 4 ≠ 0 :=
  ⟨vTwo_eq_of_mNat (by decide) (by decide), vTwo_eq_of_mNat (by decide) (by decide),
    by rw [carry_eq_mNat]; decide⟩

/-- **The price of the bottom lemma**, in one witness: at `a = 63` the predecessor obeys
`v₂(m₆₂) = 0` — as the lemma demands — while `v₂(m₆₃) = 5`.  The constraint sits on the
predecessor and does not propagate to the bottom, so it caps no fibre. -/
@[category test, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem tall_bottom_sixty_three : vTwo 62 = 0 ∧ vTwo 63 = 5 ∧ carry 62 ≠ 0 :=
  ⟨vTwo_eq_of_mNat (by decide) (by decide), vTwo_eq_of_mNat (by decide) (by decide),
    by rw [carry_eq_mNat]; decide⟩

end BB13
