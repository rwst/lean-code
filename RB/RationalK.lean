/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import RB.OrbitKernel
import RB.ScaledKernel
import RB.NotAutomatic
import Mathlib.Data.Fintype.Pi
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The rational-`K` branch (plan-B2A2 T1a) and **T1b** (plan-B1E2 M4)

Two capstones, assembled from `RB.ScaledKernel`'s `δ`-general Diophantine core and
`RB.OrbitKernel`'s repetition contraction:

* **`RB.superlinear_of_K_notIrrational`** ([B2A2] **T1a**): `K(x₀) ∈ ℚ ⇒ p_w(m)/m → ∞`.
* **`RB.not_automatic_of_K_algebraic`** ([B1E2] **T1b = milestone M4**): `K(x₀)` algebraic
  ⇒ the carry word `RB.wmin x₀` is **not automatic**.

T1b is what M4 asked for, and it is exactly the composition the plan predicted: [B1E2]'s T1a
(`RB.not_automatic_of_K_algebraic_irrational`, refereed lane) kills the *algebraic irrational*
case, and B2A2's T1a kills the remaining `K ∈ ℚ` horn.  The glue
`RB.not_automatic_of_K_algebraic_of_superlinear` had already named the obligation precisely —
"deliver superlinearity for rational `K`, the Cobham step is discharged" — and
`superlinear_of_K_notIrrational` is that delivery, with no restatement needed.

## The reduction (Stage 1, mirroring [M4A3] §4)

Suppose `p_w(k) ≤ C·k`.  Pigeonhole among the `C·k + 1` windows at positions `2, …, C·k + 2`
gives a repetition `(a, c, k)` with `2 ≤ a < c ≤ (C+2)·k`.  `RB.dist_le_of_repetition`
contracts it to `‖δ((3/2)^c − (3/2)^a)‖ ≤ (2/3)^k ≤ θ^c` at the *fixed* rational scale
`θ = 1 − (1/3)/(C+2)`, and `RB.scaledViolators_finite` bounds `c`.  Meanwhile the growth
ceiling `RB.repetition_le_add` forces `k ≤ c + x₀`.  So `k := M + x₀ + 1` — one past what the
kernel permits — cannot satisfy `p_w(k) ≤ C·k`.

## Honest scope — read this before quoting either theorem

`K` is **expected transcendental**, so T1b's hypothesis is plausibly vacuous; it is *not* a
solution to the non-automaticity problem (report-dubickas B.1), whose generic case is untouched.
[B2A2] R1 flags this and so does [B1E2] §2.2. What the pair does deliver:

* `transcendental_of_automatic` — **unconditional** (mod axioms): *if the carry word is
  automatic then `K` is transcendental.*  This strictly strengthens
  `RB.transcendental_of_automatic_of_irrational`, which had to assume `K` irrational: that
  hypothesis was exactly the `K ∈ ℚ` horn, and B2A2's T1a removes it.  It is a transcendence
  criterion for a constant whose *irrationality* has been open since Wang–Washburn 1977.
* `superlinear_or_K_irrational` — [B2A2] §2.4's dichotomy, the honest headline: **either** the
  carry word's complexity is superlinear (beating [Dub09] Cor 4's `1.70951129n` record for the
  `3/2` orbit word), **or** `K ∉ ℚ`.  Both horns are worth having; neither is provable alone
  here.

## Axiom lanes — two refereed axioms, kept independent

Both plans call this file's results the "**preprint lane**", against [B1E2] T1b's "Axioms: AF
Cor 1.8 + CZ04 + NKR25 (preprint lane)".  **That label is stale and this file does not inherit
it.**  It predates the 2026-07-14 one-axiom refactor, which retired the bespoke `CZ04` and
`NKR25` axioms: both cited theorems are now *derived* from `Subspace.evertseSchlickewei`
(Evertse–Schlickewei — **refereed**).  Nothing here is assumed on an unrefereed preprint's
authority; [NKR25] survives as the *source of the argument* (and its Thm 1.3(i) is used only in
the repaired form, the published statement being false — `NKR.thm13i_unrepaired_false`).
[B2A2]'s meta line and its §2.3 rev. 2 note both record this; only [B1E2]'s T1b row was never
updated.

The lanes are still worth keeping apart — but for **axiom independence**, not refereeing:

* **AF lane** (`RB.NotAutomatic`, not imported here): T1a = std3 +
  `AF.transcendental_or_rat_of_automatic`, **no Subspace**.
* **Subspace lane** (this file): `superlinear_of_K_rat`, `superlinear_of_K_notIrrational`,
  `superlinear_or_K_irrational` = std3 + `Subspace.evertseSchlickewei`, **no AF**.
* **The composition**: only `not_automatic_of_K_algebraic` and `transcendental_of_automatic`
  carry both — they *are* the composition, so this is intended, and both axioms are refereed.

## Contents

* `RB.factorSet_finite`, `RB.exists_repetition_of_complexity_le` — the pigeonhole layer.
* **`RB.superlinear_of_K_rat`**, **`RB.superlinear_of_K_notIrrational`** — [B2A2] T1a.
* `RB.not_automatic_of_K_rat` — the `K ∈ ℚ` horn, as non-automaticity.
* **`RB.not_automatic_of_K_algebraic`** — [B1E2] **T1b / M4**.
* **`RB.transcendental_of_automatic`** — the unconditional transcendence criterion.
* **`RB.superlinear_or_K_irrational`** — [B2A2] §2.4's dichotomy.

## References

* [B1E2] `plans/plan-B1E2.html` (rev. 2, 2026-07): T1b, milestone M4, §2.2.
* [B2A2] `plans/plan-B2A2.html`: T1a (§2.3), T1b (§2.4), WP1/WP2/WP4.
* [M4A3] `plan-M4A3.html`: §4 — the Stage-1 reduction this mirrors (`TH.superlinear_of_kernel`).
* [Dub09] A. Dubickas. Glasgow Math. J. **51** (2009), 243–252.  (Cor 4 — the linear record.)
-/

namespace RB

open ForMathlib.SubwordComplexity

/-! ## The Bernoulli certificate -/

/-- Rational Bernoulli certificate: for `r ∈ (0,1)` and `N ≥ 1` there is a rational
`θ ∈ (0,1)` with `r ≤ θ^N` — take `θ = 1 − (1−r)/N`.  Trades the irrational `(2/3)^{1/N}` for a
rational kernel scale.

`private` on purpose: this is verbatim `TH.exists_pow_ge`, and re-exporting it would put a
second copy of the same API lemma in the corpus.  Kept local rather than importing `TH`, which
would couple two otherwise-independent roots for one Bernoulli inequality. -/
private lemma exists_pow_ge (r : ℚ) (hr0 : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N) :
    ∃ θ : ℚ, 0 < θ ∧ θ < 1 ∧ r ≤ θ ^ N := by
  have hN0 : (0 : ℚ) < N := by exact_mod_cast hN
  have hdivle : (1 - r) / N ≤ 1 - r := div_le_self (by linarith) (by exact_mod_cast hN)
  have hdivpos : 0 < (1 - r) / N := div_pos (by linarith) hN0
  refine ⟨1 - (1 - r) / N, by linarith, by linarith, ?_⟩
  have hb := one_add_mul_le_pow (a := -((1 - r) / N)) (by linarith) N
  calc r = 1 + (N : ℚ) * (-((1 - r) / N)) := by field_simp; ring
    _ ≤ (1 + -((1 - r) / N)) ^ N := hb
    _ = (1 - (1 - r) / N) ^ N := by rw [← sub_eq_add_neg]

/-! ## The pigeonhole layer -/

/-- The set of length-`k` factors of the carry word is finite — its letters are `0` or `1`
(`RB.wmin_le_one`). -/
@[category API, AMS 11 68, ref "B2A2", group "rb_rational_base"]
lemma factorSet_finite (x₀ k : ℕ) :
    (Set.range fun a : ℕ => factor (wmin x₀) k a).Finite := by
  refine Set.Finite.subset
    (Set.Finite.pi' (t := fun _ : Fin k => Set.Iic 1) fun _ => Set.finite_Iic _) ?_
  rintro w ⟨a, rfl⟩
  exact fun i => Set.mem_Iic.mpr (wmin_le_one _ _)

/-- **Pigeonhole**: if the carry word has at most `C·k` distinct length-`k` factors, two of the
`C·k + 1` windows at positions `2, …, C·k + 2` coincide — a repetition. -/
@[category research solved, AMS 11 68, ref "B2A2", group "rb_rational_base"]
lemma exists_repetition_of_complexity_le {x₀ C k : ℕ}
    (h : AS.complexity (wmin x₀) k ≤ C * k) :
    ∃ a c, 2 ≤ a ∧ a < c ∧ c ≤ C * k + 2 ∧ IsRepetition x₀ a c k := by
  have hncard : AS.complexity (wmin x₀) k = (factorSet_finite x₀ k).toFinset.card :=
    Set.ncard_eq_toFinset_card _ (factorSet_finite x₀ k)
  have hcard : ((factorSet_finite x₀ k).toFinset).card < (Finset.Icc 2 (C * k + 2)).card := by
    rw [Nat.card_Icc, ← hncard]
    have harith : C * k + 2 + 1 - 2 = C * k + 1 := by
      generalize C * k = P
      omega
    rw [harith]
    exact Nat.lt_succ_of_le h
  have hmaps : ∀ a ∈ Finset.Icc 2 (C * k + 2),
      factor (wmin x₀) k a ∈ (factorSet_finite x₀ k).toFinset := fun a _ => by
    rw [Set.Finite.mem_toFinset]
    exact ⟨a, rfl⟩
  obtain ⟨u, hu, v, hv, huv, hfeq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  rw [Finset.mem_Icc] at hu hv
  rcases Nat.lt_or_ge u v with h' | h'
  · exact ⟨u, v, hu.1, h', hv.2, (factor_eq_iff _ _ _ _).mp hfeq⟩
  · exact ⟨v, u, hv.1, by omega, hu.2, (factor_eq_iff _ _ _ _).mp hfeq.symm⟩

/-! ## T1a: the rational-`K` branch -/

/-- `1 ≤ K(x₀)` for `x₀ ≥ 1` — the orbit starts at `x₀` and `K` dominates it. -/
@[category API, AMS 11 68, ref "AFS08", group "rb_rational_base"]
lemma one_le_K {x₀ : ℕ} (hx₀ : 0 < x₀) : (1 : ℝ) ≤ K x₀ := by
  have h := le_K x₀ 0
  rw [x_zero, pow_zero, mul_one] at h
  have h1 : (1 : ℝ) ≤ (x₀ : ℝ) := by exact_mod_cast hx₀
  linarith

/-- **T1a of [B2A2]** (§2.3), with the rational value named: if `K(x₀) = δ ∈ ℚ`, the carry
word's subword complexity beats **every** linear function.

Stage 1 ([M4A3] §4) mirrored: pigeonhole ⇒ repetition ⇒ (`RB.dist_le_of_repetition`)
`δ`-scaled kernel violator at the Bernoulli scale `θ(C)` ⇒ (`RB.scaledViolators_finite`) `c`
bounded by some `M` ⇒ (`RB.repetition_le_add`) `k ≤ c + x₀ ≤ M + x₀`.  So the single length
`k = M + x₀ + 1` already refutes `p_w(k) ≤ C·k`.

Ineffective (Subspace).  Footprint: std3 + `Subspace.evertseSchlickewei` — **no AF**. -/
@[category research solved, AMS 11 68, ref "CZ04" "NKR25" "B2A2", group "rb_rational_base"]
theorem superlinear_of_K_rat {x₀ : ℕ} (hx₀ : 0 < x₀) {δ : ℚ} (hδK : (δ : ℝ) = K x₀) (C : ℕ) :
    ∃ m, 1 ≤ m ∧ C * m < AS.complexity (wmin x₀) m := by
  have hδ0 : δ ≠ 0 := by
    intro h
    rw [h, Rat.cast_zero] at hδK
    linarith [one_le_K hx₀, hδK]
  obtain ⟨θ, hθ0, hθ1, hθpow⟩ :=
    exists_pow_ge (2 / 3) (by norm_num) (by norm_num) (C + 2) (by omega)
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ p ∈ scaledViolators δ θ, p.2 ≤ M := by
    obtain ⟨M, hM⟩ := ((scaledViolators_finite δ hδ0 θ hθ0 hθ1).image Prod.snd).bddAbove
    exact ⟨M, fun p hp => hM (Set.mem_image_of_mem _ hp)⟩
  refine ⟨M + x₀ + 1, by omega, ?_⟩
  set k := M + x₀ + 1 with hkdef
  by_contra hle
  obtain ⟨a, c, ha, hac, hc, hrep⟩ := exists_repetition_of_complexity_le (Nat.not_lt.mp hle)
  have hck : c ≤ (C + 2) * k := by
    have h2k : 2 ≤ 2 * k := by omega
    calc c ≤ C * k + 2 := hc
      _ ≤ C * k + 2 * k := Nat.add_le_add_left h2k _
      _ = (C + 2) * k := by ring
  have hkv : (a, c) ∈ scaledViolators δ θ := by
    refine ⟨ha, hac, ?_⟩
    calc (δ * ((3 / 2 : ℚ) ^ c - (3 / 2 : ℚ) ^ a)).distToNearestInt
        ≤ (2 / 3 : ℚ) ^ k := dist_le_of_repetition hx₀ hδK hrep
      _ ≤ (θ ^ (C + 2)) ^ k := pow_le_pow_left₀ (by norm_num) hθpow k
      _ = θ ^ ((C + 2) * k) := (pow_mul θ (C + 2) k).symm
      _ ≤ θ ^ c := pow_le_pow_of_le_one hθ0.le hθ1.le hck
  have hcM : c ≤ M := hM (a, c) hkv
  have hbound := repetition_le_add hx₀ hac hrep
  omega

/-- **T1a of [B2A2]** (§2.3), in the shape [B1E2]'s T1b glue asks for: a **rational** `K(x₀)`
forces superlinear subword complexity of the carry word.

Note the shape — superlinearity, not a linear floor.  A linear lower bound, however large its
constant, is compatible with automaticity ([B1E2] §4), so [Dub09] Cor 4's `1.70951129n` could
never have served here. -/
@[category research solved, AMS 11 68, ref "CZ04" "NKR25" "B2A2", group "rb_rational_base"]
theorem superlinear_of_K_notIrrational {x₀ : ℕ} (hx₀ : 0 < x₀) (hrat : ¬ Irrational (K x₀)) :
    ∀ C, ∃ m, 1 ≤ m ∧ C * m < AS.complexity (wmin x₀) m := by
  have hmem : K x₀ ∈ Set.range ((↑) : ℚ → ℝ) := by
    by_contra hc
    exact hrat hc
  obtain ⟨δ, hδ⟩ := hmem
  exact superlinear_of_K_rat hx₀ hδ

/-- The `K ∈ ℚ` horn as non-automaticity: rational `K` ⇒ superlinear (T1a) ⇒ not automatic
(Cobham, `AS.not_automatic_of_complexity_superlinear`). -/
@[category research solved, AMS 11 68, ref "CZ04" "NKR25" "Cob72", group "rb_rational_base"]
theorem not_automatic_of_K_rat {x₀ : ℕ} (hx₀ : 0 < x₀) (hrat : ¬ Irrational (K x₀)) :
    ¬ AS.IsAutomatic (wmin x₀) :=
  AS.not_automatic_of_complexity_superlinear (superlinear_of_K_notIrrational hx₀ hrat)

/-! ## T1b — plan-B1E2's milestone M4 -/

/-- **T1b — [B1E2] milestone M4**: if `K(x₀) = ω_{3/2}` is **algebraic**, the carry word
`RB.wmin x₀` is **not automatic**.

The `K ∈ ℚ` horn of [B1E2]'s T1a is removed by [B2A2]'s T1a: the two branches partition the
algebraic case, and each is separately closed.

* `K` algebraic **irrational** ⇒ `RB.not_automatic_of_K_algebraic_irrational` ([AF17] Cor 1.8
  kills *both* of its own alternatives at once).
* `K` **rational** ⇒ `RB.not_automatic_of_K_rat` (superlinear complexity, then Cobham).

Assembled through `RB.not_automatic_of_K_algebraic_of_superlinear`, whose hypothesis was
written for exactly this discharge.

Honest scope ([B1E2] §2.2, [B2A2] R1): `K` is *expected transcendental*, so the hypothesis is
plausibly vacuous, and this is **not** a solution to report-dubickas B.1 — the generic
transcendental case is untouched.  Its value is `transcendental_of_automatic` below.

Footprint: std3 + `AF.transcendental_or_rat_of_automatic` + `Subspace.evertseSchlickewei` —
**both refereed** (see the module doc: [B1E2] T1b's "preprint lane" label predates the
2026-07-14 one-axiom refactor and no longer applies).  This is the one theorem in the program
that carries both axioms — it *is* the composition. -/
@[category research solved, AMS 11 68, ref "AF17" "CZ04" "NKR25" "B1E2", group "rb_rational_base"]
theorem not_automatic_of_K_algebraic {x₀ : ℕ} (hx₀ : 0 < x₀) (halg : IsAlgebraic ℚ (K x₀)) :
    ¬ AS.IsAutomatic (wmin x₀) :=
  not_automatic_of_K_algebraic_of_superlinear
    (fun hrat => superlinear_of_K_notIrrational hx₀ hrat) halg

/-- **The transcendence criterion, unconditionally**: *if the carry word of
`xₙ₊₁ = ⌈3xₙ/2⌉` is automatic, then `K(x₀)` is transcendental.*

This is T1b's contrapositive and the reading with actual content.  It strictly strengthens
`RB.transcendental_of_automatic_of_irrational`, which needed `K` irrational as a hypothesis —
precisely the `K ∈ ℚ` horn that [B2A2]'s T1a removes.  Worth stating plainly: `K = ω_{3/2} =
1.6222705028…` (A083286) is not known to be **irrational** (Wang–Washburn, *Problem E2604*,
Amer. Math. Monthly **84** (1977), 821–822), and this concludes its **transcendence** from a
combinatorial hypothesis on the word that generates it. -/
@[category research solved, AMS 11 68, ref "AF17" "CZ04" "NKR25" "B1E2", group "rb_rational_base"]
theorem transcendental_of_automatic {x₀ : ℕ} (hx₀ : 0 < x₀)
    (hauto : AS.IsAutomatic (wmin x₀)) : Transcendental ℚ (K x₀) :=
  fun halg => not_automatic_of_K_algebraic hx₀ halg hauto

/-- **[B2A2] §2.4's dichotomy** — the honest headline of the rational-`K` branch:

  **either** the carry word's subword complexity is superlinear, **or** `K(x₀) ∉ ℚ`.

Both horns are interesting and neither is provable alone here: the first would beat [Dub09]
Cor 4's refereed `1.70951129n` record for the `3/2` orbit word (superlinear vs. linear); the
second is a conditional irrationality statement about `K(3) = ω_{3/2}` (A083286), open since
Wang–Washburn 1977.

Consistency check ([B2A2] §2.4): an eventually periodic `w` would make `K` rational *and* the
complexity bounded — excluded by `RB.not_eventually_periodic`, so the dichotomy is sharp on
both sides.

Footprint: std3 + `Subspace.evertseSchlickewei`.  **No AF** — this statement stays out of the
refereed-lane theorem's way entirely. -/
@[category research solved, AMS 11 68, ref "CZ04" "NKR25" "B2A2", group "rb_rational_base"]
theorem superlinear_or_K_irrational {x₀ : ℕ} (hx₀ : 0 < x₀) :
    (∀ C, ∃ m, 1 ≤ m ∧ C * m < AS.complexity (wmin x₀) m) ∨ Irrational (K x₀) := by
  by_cases h : Irrational (K x₀)
  · exact Or.inr h
  · exact Or.inl (superlinear_of_K_notIrrational hx₀ h)

end RB
