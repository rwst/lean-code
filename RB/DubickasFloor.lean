/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import RB.Residues
import RB.CollatzDictionary
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The sharp Dubickas complexity floor (report-dubickas A.6): [Dub09] Thm 5 and Cor 4

**A machine-checked "divergent `3x+1` trajectories have parity complexity `> 1.70951129·n`"** —
[Dub09] Theorem 5 — together with its deterministic companion [Dub09] Corollary 4 for the
ceiling model `x_{n+1} = ⌈3x_n/2⌉`.  This is item **A.6** of `report-dubickas.html`.

## What is proved

The single engine `RB.sharp_complexity_floor` takes a `{0,1}`-word `w`, an integer sequence `y`
and three hypotheses — **window rigidity** (equal length-`m` factors of `w` force
`y a ≡ y b (mod 2^m)`), the **growth ceiling** `2^n(y_n + 1) ≤ 3^n(y_0 + 1)`, and
**injectivity** of `y` — and returns the floor

  `P(w, m) > m · log 2/log(3/2) − log(y₀ + 1)/log(3/2)`.

Three consequences are packaged for each instantiation: the sharp floor above, the paper's
numeric floor `> 1.70951129·m` beyond an explicit threshold (`RB.numeric_complexity_floor`,
threshold `RB.dubickasThreshold`), and the paper's `liminf` statement in `∀ᶠ m in atTop` form
(`RB.eventually_complexity_floor`: every `c < log 2/log(3/2)` is eventually beaten).

Two instantiations:

* **`RB.Collatz.dubickas_theorem_5`** ([Dub09] Thm 5): for `n₀ ≥ 1` whose accelerated Collatz
  orbit tends to `∞`, the parity word `𝒳ₙ = T^n n₀ mod 2` satisfies the displayed floor.
  Numeric form `RB.Collatz.dubickas_theorem_5_num`, `liminf` form
  `RB.Collatz.dubickas_theorem_5_liminf`.
* **`RB.dubickas_corollary_4`** ([Dub09] Cor 4): the same for the ceiling orbit
  `x_{n+1} = ⌈3x_n/2⌉` from any `x₀ ≥ 1` — unconditionally, since that orbit is strictly
  increasing.  Numeric form `RB.dubickas_corollary_4_num`, `liminf` form
  `RB.dubickas_corollary_4_liminf`.

`RB.complexity_floor_ten : 16 ≤ P(wmin 1, 10)` is a closed sanity instance of the certificate
form `RB.succ_le_complexity_of_pow_le`.

The constant is `RB.dubickasConst = log 2/log(3/2) = 1.70951129135…`, and
`RB.dubickasConst_gt : 1.70951129 < dubickasConst` is proved from the `log(1 − x)` Taylor
remainder at `x = 1/3` (`Real.abs_log_sub_add_sum_range_le`, 24 terms) plus
`Real.log_two_gt_d9`; the margin is `1.35 · 10⁻⁹`, so both bounds are needed to ten digits.

## What this sharpens in the corpus

Both existing floors are superseded (neither is deleted; both remain as certificate-only,
`Real`-free statements):

* `RB.complexity_lower_bound` — slope `41/24 = 1.7083…` at `x₀ = 1` only, from the integer
  certificate `3^41 ≤ 2^65`.  Here: the exact slope `log 2/log(3/2)`, every `x₀ ≥ 1`.
* `RB.Collatz.complexity_ge_of_injective` — slope `1`.  Its docstring derives that slope from the
  growth ceiling `T n ≤ 2n` and concludes that on the Collatz side "the guaranteed rate is `1` and
  the sharp constant is fixed by the orbit's odd-step density".  The *guaranteed* half of that is
  too pessimistic, and repairing it is the mathematical content of A.6: the accelerated map
  satisfies `2(T x + 1) ≤ 3(x + 1)` — with *equality* on odd `x` — hence
  `2^n(T^n n₀ + 1) ≤ 3^n(n₀ + 1)` (`RB.Collatz.T_iter_growth`) for **every** orbit, whatever its
  odd-step density.  So the guaranteed slope is already `log 2/log(3/2)`, uniformly, and no
  density hypothesis enters.  (What remains orbit-dependent is the *true* growth rate of
  `P(𝒳, ·)`, which this floor only bounds from below.)

## Relation to Dubickas's proof

[Dub09] §5 argues by contradiction: if `P(𝒳, m) ≤ m(log 2/log(3/2) − ε)` then two of the
`⌊m(log 2/log(3/2) − ε)⌋ + 1` windows starting at `0, 1, …` coincide, whence
`2^m ∣ x_n − x_s` while `|x_n − x_s| < (3/2)^n(x₀ + 1)`.  Read through the window/residue
dictionary of `RB/Residues.lean` and `RB/CollatzDictionary.lean` (windows of length `m` *are*
residues mod `2^m`) this is the direct count performed here: the orbit values
`y_0, …, y_N` with `(3/2)^N(y₀+1) ≤ 2^m` are distinct and `< 2^m`, hence occupy `N + 1` distinct
residues.  The direct form is *stronger* than the paper's: it gives the exact slope with an
additive constant, where [Dub09] gives `liminf P/n ≥ log 2/log(3/2)` and hence only
`c·n` for each `c` below the constant.

## The same ceiling in two other roots (cross-root note, 2026-08-11)

[Dub09]'s counting step — equal length-`m` windows force `q^m ∣ x_n − x_s`, which the growth
ceiling caps — is also the engine of the T-shift lane's *free rung*, in two other conventions
and about two other words:

* **round**: `TH.repetition_pow_le` (`TH/RepetitionIdentity.lean`), `2^(k+c+1) ≤ 3^(c+1)` for the
  nearest-integer steering word `TH.t n = 2·m(n+1) − 3·m n`, `m n = round ((3/2)^n)`;
* **floor**: `TShift.carry_repetition_pow_le` (`TShift/FreeSojourn.lean`), `2^(k+c) ≤ 3^c` for
  `TShift.carry`, one power sharper because `⌊·⌋ ≤ (3/2)^c` needs no rounding slack.

That file's headline `TShift.free_sojourn_cap` (`2^(L+n) ≤ 3^(n+p)`) has slope
`κ_free = log₂(3/2) = 0.5849625…`, and

  `κ_free = 1 / RB.dubickasConst`   (`0.5849625… = 1/1.70951129…`)

exactly — the complexity floor and the sojourn cap are one inequality read in two directions
(windows vs sojourns).  Different words, so no duplication and no refactor: this file's `y` is
the ceiling orbit `x_{n+1} = ⌈3x_n/2⌉` (and the accelerated Collatz orbit), which is neither of
the two above.  Found at plan-Tshift-S11's gate G-B, sweep #2
(`plans/note-Tshift-S11-WPE.html`), which also identifies the single-target form for *every*
real `ξ` and every rational base: [GY26] Thm 1.2 + Lemma 3.1.

## References

* [Dub09] A. Dubickas. *On integer sequences generated by linear maps.* Glasgow Math. J. **51**
  (2009), 243–252.  Theorem 3 (general `p/q`), Corollary 4 (`p/q = 3/2`, `> 1.70951129n`),
  Theorem 5 (divergent `3x+1` trajectories, same constant), proofs in §4–§5.
* [Ter76] R. Terras. *A stopping time problem on the positive integers.* Acta Arith. **30**
  (1976), 241–252.  (`CC.terras_periodicity`, the rigidity on the Collatz side.)
* [A6] `plans/report-dubickas.html`, item A.6 ("First formalization of Theorem 5 (and Cor 4)");
  the growth-ceiling repair is the correction of the "orbit-dependent constant" remark of
  [B2A2] §3.1.
* [GY26] X. Gao, C. H. Yip. *On the fractional parts of certain sequences of `ξαⁿ`.*
  arXiv:2408.02972v2 (2026).  Thm 1.2 + Lemma 3.1: the same ceiling at a single target, for
  every real `ξ` and every rational base, with a `⌊C log N⌋` escape count.
* [S11] `plans/note-Tshift-S11-WPE.html` — the cross-root identification above
  (`κ_free = 1/dubickasConst`), found at plan-Tshift-S11's gate G-B, sweep #2.
-/

namespace RB

open CC
open ForMathlib.SubwordComplexity

/-! ## The Dubickas constant -/

/-- **The Dubickas constant** `log 2/log(3/2) = 1.70951129135…` ([Dub09] Thm 3 at `p/q = 3/2`):
the complexity slope forced by the `3/2` growth rate against the `2`-adic modulus. -/
@[category API, AMS 11 68, ref "Dub09", group "rb_dubickas_floor"]
noncomputable def dubickasConst : ℝ := Real.log 2 / Real.log (3 / 2)

@[category API, AMS 11 68, ref "Dub09", group "rb_dubickas_floor"]
lemma log_three_halves_pos : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)

/-- `log(3/2) < 0.4054651082`, to ten digits (`log(3/2) = 0.40546510810816…`).

The `log(1 − x)` Taylor remainder at `x = 1/3`: `Real.abs_log_sub_add_sum_range_le` with 24 terms
bounds the tail by `(1/3)^25/(2/3) < 1.8 · 10⁻¹²`, and `log(2/3) = −log(3/2)`. -/
@[category API, AMS 11 68, ref "Dub09", group "rb_dubickas_floor"]
lemma log_three_halves_lt : Real.log (3 / 2 : ℝ) < 0.4054651082 := by
  have hx : |(1 / 3 : ℝ)| < 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 24
  rw [abs_of_pos (show (0 : ℝ) < 1 / 3 by norm_num)] at h
  have hlog : Real.log (1 - 1 / 3 : ℝ) = -Real.log (3 / 2 : ℝ) := by
    rw [show (1 - 1 / 3 : ℝ) = (3 / 2)⁻¹ by norm_num, Real.log_inv]
  rw [hlog] at h
  have h2 := (abs_le.mp h).1
  have hnum : (∑ i ∈ Finset.range 24, (1 / 3 : ℝ) ^ (i + 1) / (i + 1))
      + (1 / 3 : ℝ) ^ (24 + 1) / (1 - 1 / 3) < 0.4054651082 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  linarith

/-- **Dubickas's numeric constant is below the exact one**: `1.70951129 < log 2/log(3/2)`.

The margin is `1.35 · 10⁻⁹`, so this needs `log(3/2)` from above and `log 2` from below, both to
ten digits (`log_three_halves_lt`, `Real.log_two_gt_d9`). -/
@[category research solved, AMS 11 68, ref "Dub09", group "rb_dubickas_floor"]
theorem dubickasConst_gt : (1.70951129 : ℝ) < dubickasConst := by
  rw [dubickasConst, lt_div_iff₀ log_three_halves_pos]
  have h1 : (1.70951129 : ℝ) * Real.log (3 / 2) < 1.70951129 * 0.4054651082 := by
    nlinarith [log_three_halves_lt]
  have h2 : (1.70951129 : ℝ) * 0.4054651082 ≤ 0.6931471803 := by norm_num
  linarith [Real.log_two_gt_d9]

@[category API, AMS 11 68, ref "Dub09", group "rb_dubickas_floor"]
lemma dubickasConst_pos : 0 < dubickasConst := lt_trans (by norm_num) dubickasConst_gt

/-! ## The pigeonhole engine

Everything below is stated for an abstract pair (`{0,1}`-word `w`, integer sequence `y`) linked by
window rigidity, so that the Collatz map and the ceiling model are two instantiations of one
proof — exactly as [Dub09] proves Theorems 3 and 5 by the same computation.
-/

/-- The factors of a `{0,1}`-valued word form a finite set. -/
private lemma range_factor_finite {w : ℕ → ℕ} (hw : ∀ n, w n ≤ 1) (m : ℕ) :
    (Set.range fun a => factor w m a).Finite := by
  refine Set.Finite.subset (Set.Finite.pi fun _ : Fin m => Set.finite_Iic 1) ?_
  rintro v ⟨a, rfl⟩
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_Iic, forall_const]
  intro s
  exact hw (a + s)

/-- Every word has at least one factor of each length. -/
@[category API, AMS 11 68, ref "Dub09", group "rb_dubickas_floor"]
lemma one_le_complexity {w : ℕ → ℕ} (hw : ∀ n, w n ≤ 1) (m : ℕ) :
    1 ≤ AS.complexity w m :=
  (Set.ncard_pos (range_factor_finite hw m)).mpr ⟨factor w m 0, ⟨0, rfl⟩⟩

/-- **The covering pigeonhole**, abstract form: positions carrying pairwise distinct `y`-values
below the modulus `2^m` carry pairwise distinct length-`m` factors, so there are at most
`P(w, m)` of them. -/
@[category research solved, AMS 11 68, ref "Dub09", group "rb_dubickas_floor"]
theorem card_le_complexity {w y : ℕ → ℕ} (hw : ∀ n, w n ≤ 1) {m : ℕ}
    (hrig : ∀ a b, factor w m a = factor w m b → y a % 2 ^ m = y b % 2 ^ m)
    (S : Finset ℕ) (hbdd : ∀ a ∈ S, y a < 2 ^ m) (hinj : Set.InjOn y S) :
    S.card ≤ AS.complexity w m := by
  classical
  have hinj' : Set.InjOn (fun a => factor w m a) S := by
    intro a ha b hb hfac
    have hmod := hrig a b hfac
    rw [Nat.mod_eq_of_lt (hbdd a ha), Nat.mod_eq_of_lt (hbdd b hb)] at hmod
    exact hinj ha hb hmod
  have hsub : ((S.image fun a => factor w m a : Finset (Fin m → ℕ)) : Set (Fin m → ℕ))
      ⊆ Set.range fun a => factor w m a := by
    intro v hv
    simp only [Finset.coe_image, Set.mem_image] at hv
    obtain ⟨a, -, rfl⟩ := hv
    exact Set.mem_range_self a
  calc S.card = (S.image fun a => factor w m a).card :=
        (Finset.card_image_of_injOn hinj').symm
    _ = ((S.image fun a => factor w m a : Finset (Fin m → ℕ)) : Set (Fin m → ℕ)).ncard :=
        (Set.ncard_coe_finset _).symm
    _ ≤ (Set.range fun a => factor w m a).ncard :=
        Set.ncard_le_ncard hsub (range_factor_finite hw m)
    _ = AS.complexity w m := rfl

/-- **The floor, integer-certificate form**: if `3^N (y₀ + 1) ≤ 2^{m+N}` — i.e.
`(3/2)^N (y₀+1) ≤ 2^m`, so that the first `N + 1` orbit values stay below the modulus — then
`P(w, m) ≥ N + 1`.

This is the `Real`-free heart of [Dub09] Thm 3/5: the growth ceiling puts `y_0, …, y_N` inside
`[0, 2^m)`, injectivity makes them distinct, rigidity turns distinctness into `N + 1` distinct
windows. -/
@[category research solved, AMS 11 68, ref "Dub09", group "rb_dubickas_floor"]
theorem succ_le_complexity_of_pow_le {w y : ℕ → ℕ} (hw : ∀ n, w n ≤ 1)
    (hrig : ∀ m a b, factor w m a = factor w m b → y a % 2 ^ m = y b % 2 ^ m)
    (hgro : ∀ n, 2 ^ n * (y n + 1) ≤ 3 ^ n * (y 0 + 1))
    (hinj : Function.Injective y) {m N : ℕ} (hN : 3 ^ N * (y 0 + 1) ≤ 2 ^ (m + N)) :
    N + 1 ≤ AS.complexity w m := by
  have hsmall : ∀ j ∈ Finset.range (N + 1), y j < 2 ^ m := by
    intro j hj
    rw [Finset.mem_range] at hj
    -- transport the certificate from `N` down to `j ≤ N`, using `2 ≤ 3`
    have step : 3 ^ j * (y 0 + 1) ≤ 2 ^ (m + j) := by
      have hchain : 3 ^ j * (y 0 + 1) * 2 ^ (N - j) ≤ 2 ^ (m + j) * 2 ^ (N - j) := by
        calc 3 ^ j * (y 0 + 1) * 2 ^ (N - j)
            ≤ 3 ^ j * (y 0 + 1) * 3 ^ (N - j) :=
              Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by norm_num) _)
          _ = 3 ^ N * (y 0 + 1) := by
              rw [mul_comm (3 ^ j) (y 0 + 1), mul_assoc, ← pow_add]
              rw [show j + (N - j) = N by omega]; ring
          _ ≤ 2 ^ (m + N) := hN
          _ = 2 ^ (m + j) * 2 ^ (N - j) := by
              rw [← pow_add]; congr 1; omega
      exact Nat.le_of_mul_le_mul_right hchain (Nat.two_pow_pos _)
    have hgj := hgro j
    have : 2 ^ j * (y j + 1) ≤ 2 ^ j * 2 ^ m := by
      calc 2 ^ j * (y j + 1) ≤ 3 ^ j * (y 0 + 1) := hgj
        _ ≤ 2 ^ (m + j) := step
        _ = 2 ^ j * 2 ^ m := by rw [← pow_add]; congr 1; omega
    have := Nat.le_of_mul_le_mul_left this (Nat.two_pow_pos j)
    omega
  have := card_le_complexity hw (hrig m) (Finset.range (N + 1)) hsmall hinj.injOn
  simpa using this

/-- **The sharp Dubickas floor** ([Dub09] Thm 3/Thm 5, direct form):

  `P(w, m) > m · log 2/log(3/2) − log(y₀ + 1)/log(3/2)`.

Take `N = ⌊(m log 2 − log(y₀+1))/log(3/2)⌋`, the largest index with `(3/2)^N(y₀+1) ≤ 2^m`, and
apply `succ_le_complexity_of_pow_le`.  Unlike [Dub09]'s `liminf` statement this carries no `ε`:
the slope is exactly `log 2/log(3/2)`, with `log(y₀+1)/log(3/2)` as the only additive loss. -/
@[category research solved, AMS 11 68, ref "Dub09", group "rb_dubickas_floor"]
theorem sharp_complexity_floor {w y : ℕ → ℕ} (hw : ∀ n, w n ≤ 1)
    (hrig : ∀ m a b, factor w m a = factor w m b → y a % 2 ^ m = y b % 2 ^ m)
    (hgro : ∀ n, 2 ^ n * (y n + 1) ≤ 3 ^ n * (y 0 + 1))
    (hinj : Function.Injective y) (m : ℕ) :
    (m : ℝ) * dubickasConst - Real.log ((y 0 : ℝ) + 1) / Real.log (3 / 2)
      < AS.complexity w m := by
  have hL := log_three_halves_pos
  set t : ℝ := ((m : ℝ) * Real.log 2 - Real.log ((y 0 : ℝ) + 1)) / Real.log (3 / 2) with ht
  have htval : t = (m : ℝ) * dubickasConst - Real.log ((y 0 : ℝ) + 1) / Real.log (3 / 2) := by
    rw [ht, dubickasConst]; field_simp
  rw [← htval]
  rcases lt_or_ge t 0 with hneg | hpos
  · calc t < 0 := hneg
      _ < 1 := by norm_num
      _ ≤ (AS.complexity w m : ℝ) := by exact_mod_cast one_le_complexity hw m
  · have hNle : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le hpos
    have hNL : ((⌊t⌋₊ : ℕ) : ℝ) * Real.log (3 / 2)
        ≤ (m : ℝ) * Real.log 2 - Real.log ((y 0 : ℝ) + 1) := by
      rw [ht, le_div_iff₀ hL] at hNle; exact hNle
    have h32 : Real.log (3 / 2 : ℝ) = Real.log 3 - Real.log 2 :=
      Real.log_div (by norm_num) (by norm_num)
    rw [h32] at hNL
    have hlog : Real.log ((3 : ℝ) ^ (⌊t⌋₊ : ℕ) * ((y 0 : ℝ) + 1))
        ≤ Real.log ((2 : ℝ) ^ (m + (⌊t⌋₊ : ℕ))) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
      push_cast
      nlinarith [hNL]
    have hcast : ((3 : ℝ) ^ (⌊t⌋₊ : ℕ) * ((y 0 : ℝ) + 1)) ≤ ((2 : ℝ) ^ (m + (⌊t⌋₊ : ℕ))) :=
      (Real.log_le_log_iff (by positivity) (by positivity)).mp hlog
    have hnat : 3 ^ (⌊t⌋₊ : ℕ) * (y 0 + 1) ≤ 2 ^ (m + (⌊t⌋₊ : ℕ)) := by
      have : ((3 ^ (⌊t⌋₊ : ℕ) * (y 0 + 1) : ℕ) : ℝ) ≤ ((2 ^ (m + (⌊t⌋₊ : ℕ)) : ℕ) : ℝ) := by
        push_cast; exact hcast
      exact_mod_cast this
    have hfloor := succ_le_complexity_of_pow_le hw hrig hgro hinj hnat
    calc t < ((⌊t⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one t
      _ ≤ (AS.complexity w m : ℝ) := by exact_mod_cast hfloor

/-- The threshold above which the sharp floor implies the slope-`c` floor `P(w, m) > c·m`, for
`c < dubickasConst`: the additive loss `log(y₀+1)/log(3/2)` is absorbed once
`m (dubickasConst − c) ≥ log(y₀+1)/log(3/2)`. -/
@[category API, AMS 11 68, ref "Dub09", group "rb_dubickas_floor"]
noncomputable def floorThreshold (c : ℝ) (y₀ : ℕ) : ℕ :=
  ⌈Real.log ((y₀ : ℝ) + 1) / (Real.log (3 / 2) * (dubickasConst - c))⌉₊

/-- **The floor at any slope below the constant** — [Dub09]'s own conclusion
`liminf P(w, m)/m ≥ log 2/log(3/2)`, in its effective form: for every `c < dubickasConst`,
`P(w, m) > c·m` for every `m ≥ floorThreshold c y₀`. -/
@[category research solved, AMS 11 68, ref "Dub09", group "rb_dubickas_floor"]
theorem complexity_floor_of_lt {w y : ℕ → ℕ} (hw : ∀ n, w n ≤ 1)
    (hrig : ∀ m a b, factor w m a = factor w m b → y a % 2 ^ m = y b % 2 ^ m)
    (hgro : ∀ n, 2 ^ n * (y n + 1) ≤ 3 ^ n * (y 0 + 1))
    (hinj : Function.Injective y) {c : ℝ} (hc : c < dubickasConst)
    {m : ℕ} (hm : floorThreshold c (y 0) ≤ m) :
    c * m < AS.complexity w m := by
  have hL := log_three_halves_pos
  have hgap : (0 : ℝ) < dubickasConst - c := by linarith
  unfold floorThreshold at hm
  rw [Nat.ceil_le] at hm
  have habs : Real.log ((y 0 : ℝ) + 1) / Real.log (3 / 2)
      ≤ (m : ℝ) * (dubickasConst - c) := by
    rw [div_le_iff₀ hL]
    rw [div_le_iff₀ (mul_pos hL hgap)] at hm
    linarith [hm]
  have hsharp := sharp_complexity_floor hw hrig hgro hinj m
  linarith [hsharp, habs]

/-- The `liminf` form of [Dub09] Thm 3/5, as an `atTop` filter statement: every slope below
`log 2/log(3/2)` is eventually beaten. -/
@[category research solved, AMS 11 68, ref "Dub09", group "rb_dubickas_floor"]
theorem eventually_complexity_floor {w y : ℕ → ℕ} (hw : ∀ n, w n ≤ 1)
    (hrig : ∀ m a b, factor w m a = factor w m b → y a % 2 ^ m = y b % 2 ^ m)
    (hgro : ∀ n, 2 ^ n * (y n + 1) ≤ 3 ^ n * (y 0 + 1))
    (hinj : Function.Injective y) {c : ℝ} (hc : c < dubickasConst) :
    ∀ᶠ m in Filter.atTop, c * m < AS.complexity w m :=
  Filter.eventually_atTop.mpr
    ⟨floorThreshold c (y 0), fun _ hm => complexity_floor_of_lt hw hrig hgro hinj hc hm⟩

/-- The threshold for [Dub09]'s stated constant `1.70951129`. -/
@[category API, AMS 11 68, ref "Dub09", group "rb_dubickas_floor"]
noncomputable def dubickasThreshold (y₀ : ℕ) : ℕ := floorThreshold 1.70951129 y₀

/-- **The numeric floor** `P(w, m) > 1.70951129·m` ([Dub09]'s stated form of Thm 3/5), for every
`m ≥ dubickasThreshold y₀`. -/
@[category research solved, AMS 11 68, ref "Dub09", group "rb_dubickas_floor"]
theorem numeric_complexity_floor {w y : ℕ → ℕ} (hw : ∀ n, w n ≤ 1)
    (hrig : ∀ m a b, factor w m a = factor w m b → y a % 2 ^ m = y b % 2 ^ m)
    (hgro : ∀ n, 2 ^ n * (y n + 1) ≤ 3 ^ n * (y 0 + 1))
    (hinj : Function.Injective y) {m : ℕ} (hm : dubickasThreshold (y 0) ≤ m) :
    (1.70951129 : ℝ) * m < AS.complexity w m :=
  complexity_floor_of_lt hw hrig hgro hinj dubickasConst_gt hm

/-! ## [Dub09] Theorem 5: divergent `3x+1` trajectories -/

namespace Collatz

/-- **The sharp growth ceiling of the accelerated Collatz map**: `2(T x + 1) ≤ 3(x + 1)`, with
equality for odd `x`.  This — not the crude `T n ≤ 2n` of `RB.Collatz.T_le_two_mul` — is what
[Dub09] §5 uses (`x_n < (3/2)^n(x₀+1)`), and it is what makes the complexity slope
`log 2/log(3/2)` rather than `1`. -/
@[category API, AMS 11 68, ref "Dub09", group "rb_dubickas_floor"]
lemma two_mul_T_add_one_le (n : ℕ) : 2 * (T n + 1) ≤ 3 * (n + 1) := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [T_even (by omega)]; omega
  · rw [T_odd (by omega)]; omega

/-- **The iterated growth ceiling** `2^k (T^k n₀ + 1) ≤ 3^k (n₀ + 1)`, i.e.
`T^k n₀ < (3/2)^k (n₀ + 1)` ([Dub09] §5, p. 250).  Holds for *every* orbit — the odd-step
density is irrelevant, since each step obeys `two_mul_T_add_one_le`. -/
@[category research solved, AMS 11 68, ref "Dub09", group "rb_dubickas_floor"]
theorem T_iter_growth (n₀ k : ℕ) : 2 ^ k * (T_iter k n₀ + 1) ≤ 3 ^ k * (n₀ + 1) := by
  induction k with
  | zero => simp [T_iter]
  | succ k ih =>
    have hstep : 2 * (T_iter (k + 1) n₀ + 1) ≤ 3 * (T_iter k n₀ + 1) :=
      two_mul_T_add_one_le (T_iter k n₀)
    calc 2 ^ (k + 1) * (T_iter (k + 1) n₀ + 1)
        = 2 ^ k * (2 * (T_iter (k + 1) n₀ + 1)) := by rw [pow_succ]; ring
      _ ≤ 2 ^ k * (3 * (T_iter k n₀ + 1)) := Nat.mul_le_mul_left _ hstep
      _ = 3 * (2 ^ k * (T_iter k n₀ + 1)) := by ring
      _ ≤ 3 * (3 ^ k * (n₀ + 1)) := Nat.mul_le_mul_left _ ih
      _ = 3 ^ (k + 1) * (n₀ + 1) := by rw [pow_succ]; ring

/-- An orbit that revisits a value is eventually periodic, hence bounded: the [Dub09] §5 step
"if `x_n = x_s` the sequence is an infinite repetition of `x_s, …, x_{n−1}`, so it is bounded,
contrary to the condition of the theorem". -/
@[category API, AMS 11 68, ref "Dub09", group "rb_dubickas_floor"]
lemma bddAbove_of_T_iter_eq {n₀ a b : ℕ} (hab : a < b) (heq : T_iter a n₀ = T_iter b n₀) :
    ∀ k, T_iter k n₀ ≤ (Finset.range b).sup fun j => T_iter j n₀ := by
  have hper : ∀ k, a ≤ k → T_iter (k + (b - a)) n₀ = T_iter k n₀ := by
    intro k hk
    calc T_iter (k + (b - a)) n₀ = T_iter (k - a) (T_iter b n₀) := by
          rw [← T_iter_add]; congr 1; omega
      _ = T_iter (k - a) (T_iter a n₀) := by rw [heq]
      _ = T_iter k n₀ := by rw [← T_iter_add]; congr 1; omega
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    rcases Nat.lt_or_ge k b with hkb | hkb
    · exact Finset.le_sup (f := fun j => T_iter j n₀) (Finset.mem_range.mpr hkb)
    · have hk' : k - (b - a) < k := by omega
      have := IH (k - (b - a)) hk'
      rwa [← hper (k - (b - a)) (by omega), show k - (b - a) + (b - a) = k by omega] at this

/-- **Divergence ⇒ no repeat**: an unbounded Collatz orbit is injective as a function of time.
([Dub09] §5's `x_n ≠ x_s`.) -/
@[category research solved, AMS 11 68, ref "Dub09", group "rb_dubickas_floor"]
theorem injective_of_unbounded {n₀ : ℕ} (hub : ∀ B, ∃ n, B < T_iter n n₀) :
    Function.Injective fun n => T_iter n n₀ := by
  intro a b heq
  by_contra hne
  rcases Nat.lt_or_ge a b with hab | hba
  · obtain ⟨n, hn⟩ := hub ((Finset.range b).sup fun j => T_iter j n₀)
    exact absurd (bddAbove_of_T_iter_eq hab heq n) (by omega)
  · have hba' : b < a := by omega
    obtain ⟨n, hn⟩ := hub ((Finset.range a).sup fun j => T_iter j n₀)
    exact absurd (bddAbove_of_T_iter_eq hba' heq.symm n) (by omega)

/-- Window rigidity in the `%`-form the engine consumes: `CC.terras_periodicity` transported
across `RB.Collatz.factor_eq_iff_residue_eq`. -/
@[category API, AMS 11 68, ref "Ter76" "Dub09", group "rb_dubickas_floor"]
lemma factor_eq_imp_mod_eq {n₀ : ℕ} (hn₀ : 1 ≤ n₀) (m a b : ℕ)
    (hfac : factor (parityWord n₀) m a = factor (parityWord n₀) m b) :
    T_iter a n₀ % 2 ^ m = T_iter b n₀ % 2 ^ m := by
  have h := (factor_eq_iff_residue_eq hn₀ m a b).mp hfac
  rw [ZMod.natCast_eq_natCast_iff] at h
  exact h

/-- **[Dub09] Theorem 5** (sharp form).  If the accelerated Collatz orbit of `n₀ ≥ 1` is
unbounded, its parity word `𝒳ₙ = T^n n₀ mod 2` satisfies

  `P(𝒳, m) > m · log 2/log(3/2) − log(n₀ + 1)/log(3/2)`

for every `m`.  In particular `liminf P(𝒳, m)/m ≥ log 2/log(3/2) = 1.70951129135…`, which is
[Dub09] Thm 5; the paper's `> 1.70951129 m` for large `m` is `dubickas_theorem_5_num`. -/
@[category research solved, AMS 11 68, ref "Dub09" "Ter76", group "rb_dubickas_floor"]
theorem dubickas_theorem_5 {n₀ : ℕ} (hn₀ : 1 ≤ n₀) (hub : ∀ B, ∃ n, B < T_iter n n₀) (m : ℕ) :
    (m : ℝ) * dubickasConst - Real.log ((n₀ : ℝ) + 1) / Real.log (3 / 2)
      < AS.complexity (parityWord n₀) m :=
  sharp_complexity_floor (parityWord_le_one n₀) (fun m a b => factor_eq_imp_mod_eq hn₀ m a b)
    (fun k => T_iter_growth n₀ k) (injective_of_unbounded hub) m

/-- "`x_n → ∞`" in the `Filter.Tendsto` phrasing gives the unboundedness the proof uses. -/
@[category API, AMS 11 68, ref "Dub09", group "rb_dubickas_floor"]
lemma unbounded_of_tendsto {n₀ : ℕ}
    (hdiv : Filter.Tendsto (fun n => T_iter n n₀) Filter.atTop Filter.atTop) :
    ∀ B, ∃ n, B < T_iter n n₀ := by
  intro B
  obtain ⟨n, hn⟩ := (Filter.tendsto_atTop.mp hdiv (B + 1)).exists
  exact ⟨n, by omega⟩

/-- **[Dub09] Theorem 5**, the paper's numeric form: a divergent `3x+1` trajectory has parity
complexity `P(𝒳, m) > 1.70951129 m` for every `m ≥ dubickasThreshold n₀`.

Stated with `Filter.Tendsto … atTop atTop` — "`x_n → ∞` as `n → ∞`" — as in [Dub09]. -/
@[category research solved, AMS 11 68, ref "Dub09" "Ter76", group "rb_dubickas_floor"]
theorem dubickas_theorem_5_num {n₀ : ℕ} (hn₀ : 1 ≤ n₀)
    (hdiv : Filter.Tendsto (fun n => T_iter n n₀) Filter.atTop Filter.atTop)
    {m : ℕ} (hm : dubickasThreshold n₀ ≤ m) :
    (1.70951129 : ℝ) * m < AS.complexity (parityWord n₀) m :=
  numeric_complexity_floor (parityWord_le_one n₀)
    (fun m a b => factor_eq_imp_mod_eq hn₀ m a b) (fun k => T_iter_growth n₀ k)
    (injective_of_unbounded (unbounded_of_tendsto hdiv)) hm

/-- **[Dub09] Theorem 5**, the `liminf` form actually stated in the paper:
`liminf P(𝒳, m)/m ≥ log 2/log(3/2)`, i.e. every slope below the constant is eventually beaten. -/
@[category research solved, AMS 11 68, ref "Dub09" "Ter76", group "rb_dubickas_floor"]
theorem dubickas_theorem_5_liminf {n₀ : ℕ} (hn₀ : 1 ≤ n₀)
    (hdiv : Filter.Tendsto (fun n => T_iter n n₀) Filter.atTop Filter.atTop)
    {c : ℝ} (hc : c < dubickasConst) :
    ∀ᶠ m in Filter.atTop, c * m < AS.complexity (parityWord n₀) m :=
  eventually_complexity_floor (parityWord_le_one n₀)
    (fun m a b => factor_eq_imp_mod_eq hn₀ m a b) (fun k => T_iter_growth n₀ k)
    (injective_of_unbounded (unbounded_of_tendsto hdiv)) hc

end Collatz

/-! ## [Dub09] Corollary 4: the ceiling model `x ↦ ⌈3x/2⌉` -/

/-- Window rigidity for the ceiling model, in the `%`-form the engine consumes. -/
@[category API, AMS 11 68, ref "Dub09", group "rb_dubickas_floor"]
lemma factor_eq_imp_mod_eq (x₀ m a b : ℕ)
    (hfac : factor (wmin x₀) m a = factor (wmin x₀) m b) :
    x x₀ a % 2 ^ m = x x₀ b % 2 ^ m := by
  have h := (factor_eq_iff_residue_eq x₀ m a b).mp hfac
  rw [ZMod.natCast_eq_natCast_iff] at h
  exact h

/-- **[Dub09] Corollary 4** (sharp form, every seed).  For the ceiling orbit
`x_{n+1} = ⌈3x_n/2⌉` from any `x₀ ≥ 1`, the word `𝒳ₙ = x_n mod 2` satisfies

  `P(𝒳, m) > m · log 2/log(3/2) − log(x₀ + 1)/log(3/2)`.

Unconditional: the orbit is strictly increasing (`RB.x_strictMono`), so no divergence hypothesis
is needed — the contrast with `Collatz.dubickas_theorem_5` that [Dub09] p. 249 draws.

Sharpens `RB.complexity_lower_bound` (slope `41/24 = 1.7083…`, seed `x₀ = 1`) to the exact slope
`log 2/log(3/2) = 1.70951129135…` for every seed. -/
@[category research solved, AMS 11 68, ref "Dub09", group "rb_dubickas_floor"]
theorem dubickas_corollary_4 {x₀ : ℕ} (hx₀ : 0 < x₀) (m : ℕ) :
    (m : ℝ) * dubickasConst - Real.log ((x₀ : ℝ) + 1) / Real.log (3 / 2)
      < AS.complexity (wmin x₀) m :=
  sharp_complexity_floor (wmin_le_one x₀) (fun m a b => factor_eq_imp_mod_eq x₀ m a b)
    (fun n => by simpa using two_pow_mul_x_add_one_le x₀ n) (x_strictMono hx₀).injective m

/-- **[Dub09] Corollary 4**, the paper's numeric form: `P(𝒳, m) > 1.70951129 m` for every
`m ≥ dubickasThreshold x₀`.  For `x₀ = 1` the word is the parity word of **A061419** and the
threshold is `dubickasThreshold 1`. -/
@[category research solved, AMS 11 68, ref "Dub09", group "rb_dubickas_floor"]
theorem dubickas_corollary_4_num {x₀ : ℕ} (hx₀ : 0 < x₀) {m : ℕ}
    (hm : dubickasThreshold x₀ ≤ m) :
    (1.70951129 : ℝ) * m < AS.complexity (wmin x₀) m :=
  numeric_complexity_floor (wmin_le_one x₀) (fun m a b => factor_eq_imp_mod_eq x₀ m a b)
    (fun n => by simpa using two_pow_mul_x_add_one_le x₀ n)
    (x_strictMono hx₀).injective (by simpa using hm)

/-- **[Dub09] Corollary 4**, the `liminf` form: `liminf P(𝒳, m)/m ≥ log 2/log(3/2)` for the
ceiling orbit from any seed. -/
@[category research solved, AMS 11 68, ref "Dub09", group "rb_dubickas_floor"]
theorem dubickas_corollary_4_liminf {x₀ : ℕ} (hx₀ : 0 < x₀) {c : ℝ} (hc : c < dubickasConst) :
    ∀ᶠ m in Filter.atTop, c * m < AS.complexity (wmin x₀) m :=
  eventually_complexity_floor (wmin_le_one x₀) (fun m a b => factor_eq_imp_mod_eq x₀ m a b)
    (fun n => by simpa using two_pow_mul_x_add_one_le x₀ n) (x_strictMono hx₀).injective hc

/-- Sanity check of the certificate form (`succ_le_complexity_of_pow_le`): at `m = 10` and seed
`x₀ = 1` (the word of **A061419**) the certificate `3^15 · 2 ≤ 2^25` gives `P(𝒳, 10) ≥ 16`. -/
@[category test, AMS 11 68, ref "Dub09", group "rb_dubickas_floor"]
theorem complexity_floor_ten : 16 ≤ AS.complexity (wmin 1) 10 :=
  succ_le_complexity_of_pow_le (N := 15) (wmin_le_one 1)
    (fun m a b => factor_eq_imp_mod_eq 1 m a b)
    (fun n => by simpa using two_pow_mul_x_add_one_le 1 n) (x_strictMono one_pos).injective
    (by norm_num [x_zero])

end RB
