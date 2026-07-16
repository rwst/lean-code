/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CITED.NairKumarRoutLemmas
import CITED.SubspaceTheorem
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Deriving the Nair–Kumar–Rout pair theorem from the Subspace Theorem

Final step of the one-axiom refactor (`report-formalize-subspace.html` §4/§6): the
`ℚ`-specialized [NKR25] Theorem 1.3(i) — **repaired** by the strict-positivity
hypothesis and **derived** as a theorem resting only on `Subspace.evertseSchlickewei`
at `n = 3`.  With `CZ.pseudoPisot_approx_of_subspace` (the `n = 2` half) this
completes the program's single-axiom end state: **M4's entire Diophantine footprint
is the Subspace Theorem**.

**Status: COMPLETE (2026-07-14).**  Both results below are **sorry-free** with
footprint `std3 + Subspace.evertseSchlickewei`.

## Why the repair (⚠ the unrepaired statement is false)

The cited axiom previously recorded here transcribed [NKR25] Theorem 1.3(i)
faithfully — and that statement is **false as printed**: inequality (1) of [NKR25]
does not require `‖α₁u₁ + α₂u₂‖ > 0` (their Theorem 1.1(iv) does!), so the family
`(u₁, u₂) = (3^m/2, 3^{2m}/2)` — whose sum is *exactly* an integer by parity, with
pairwise-distinct ratios `3^{-m}` — satisfies every hypothesis while no entry is ever
an algebraic integer.  The machine-checked refutation is
`NKR.thm13i_unrepaired_false` (`CITED/NairKumarRout.lean`); the proof gap in [NKR25]
§4.1 is the uniform-`ε` step (their `κ`, hence `ε`, depends on the tuple, while their
Lemma 2.2 needs one fixed `ε`).  Adding `0 < ‖α₁u₁ + α₂u₂‖` (per-member) repairs the
statement, and over `ℚ` the repaired theorem is *provable* — indeed the honest
content is **finiteness** (`pair_finite`, the analogue of [NKR25] Prop. 3.1 /
Remark 3.2 at `m = 2`, `q = 1`): no infinite family satisfies the hypotheses at all.

## The proof (`pair_finite`)

Assume an infinite family.  All but finitely many members have ratio height
`H(u₁/u₂) ≥ (|α₁|+|α₂|+1)²` (`finite_height23_le` + the pairwise-distinct-ratio
injectivity), and each such member's triple `(p₀, u₁, u₂)` (`p₀` the nearest integer)
solves the `S = {∞,2,3}` Subspace inequality `approxProduct ≤ mulHeight^{-3-ε₁/4}`
(`member_solves`: on the gcd-reduced integer representative the finite local norms
are `1`, the `S`-unit product formula collapses the numerator to `‖α₁u₁+α₂u₂‖`, and
`M ≤ CH²` with `C² ≤ M` gives `M ≤ H⁴`).  The Subspace Theorem confines these
triples to finitely many proper subspaces; a pigeonhole picks one subspace `W`
through infinitely many members, and a nonzero functional vanishing on `W` yields a
fixed relation `a₀p₀ + a₁u₁ + a₂u₂ = 0`.  If `a₀ = 0` the ratio `u₁/u₂` is constant —
against distinct ratios.  Otherwise `p₀ = λ₁u₁ + λ₂u₂` and, with `βᵢ = λᵢ − αᵢ`,
`‖α₁u₁+α₂u₂‖ = |β₁u₁ + β₂u₂|`: if `β = 0` this contradicts positivity; if the `βᵢ`
have equal signs (or one vanishes) the distance has a positive floor, bounding the
heights; and in the opposite-sign case the ratios `u₁/u₂` approximate `-β₂/β₁`, which
the derived Corvaja–Zannier theorem forbids (`sUnit_near_ratio_finite`, via
`CZ.pseudoPisot_approx_of_subspace` — Subspace at `n = 2`).  Every branch bounds the
family.  Ineffective throughout.

## Contents

* `NKR.pair_finite` — **the NKR pair theorem over `ℚ`, finiteness form** (primary).
* `NKR.sUnit_pair_integrality_of_subspace` — the repaired Theorem 1.3(i) shape the
  consumers use (same signature as the retired axiom plus strict positivity).

## References

* [NKR25] Nair, Parvathi S., Veekesh Kumar, and S. S. Rout. "Algebraic
  approximations to linear combinations of S-units." arXiv:2506.02898 (v3,
  18 Nov 2025).  **Unrefereed preprint**; Theorem 1.3(i) is false as stated and is
  repaired here — the reference now serves as statement template and attribution,
  not as authority.
* [S] W. M. Schmidt, LNM **1467**, Theorem 1D′ (`CITED/SubspaceTheorem.lean` — the
  single axiom everything rests on).
* [CZ04] Corvaja–Zannier, Acta Math. **193** (2004)
  (`CITED/CorvajaZannierProof.lean` — the `n = 2` ingredient).
* `report-formalize-subspace.html` §4, §6; `plan-M4A3.html` §6.3, §10.1.
-/

namespace NKR

open Subspace Rat.AbsoluteValue Height CZ

attribute [local instance] Classical.propDecidable

/-- **The Nair–Kumar–Rout pair theorem over `ℚ`, finiteness form** ([NKR25]
Prop. 3.1/Remark 3.2 analogue at `m = 2`, with the strict-positivity repair): a
family of exponent-encoded pairs from `Γ = ⟨2,3⟩` with entries `≥ 1`,
pairwise-distinct ratios, and `0 < ‖α₁u₁ + α₂u₂‖ < (H(u₁)H(u₂))^{-ε₁}` is
**finite**.  Sorry-free; rests only on `Subspace.evertseSchlickewei`. -/
@[category research solved, AMS 11, ref "NKR25", group "three_halves_m4"]
theorem pair_finite (α₁ α₂ : ℚ) (ε₁ : ℝ) (hε₁ : 0 < ε₁)
    (𝒩 : Set ((ℤ × ℤ) × (ℤ × ℤ)))
    (habs : ∀ q ∈ 𝒩, 1 ≤ |uval q.1.1 q.1.2| ∧ 1 ≤ |uval q.2.1 q.2.2|)
    (hratio : ∀ q ∈ 𝒩, ∀ q' ∈ 𝒩, q ≠ q' →
      uval q.1.1 q.1.2 / uval q.2.1 q.2.2 ≠ uval q'.1.1 q'.1.2 / uval q'.2.1 q'.2.2 ∧
      uval q.2.1 q.2.2 / uval q.1.1 q.1.2 ≠ uval q'.2.1 q'.2.2 / uval q'.1.1 q'.1.2)
    (hpos : ∀ q ∈ 𝒩,
      0 < (α₁ * uval q.1.1 q.1.2 + α₂ * uval q.2.1 q.2.2).distToNearestInt)
    (happrox : ∀ q ∈ 𝒩,
      ((α₁ * uval q.1.1 q.1.2 + α₂ * uval q.2.1 q.2.2).distToNearestInt : ℝ)
        < ((height23 q.1.1 q.1.2 * height23 q.2.1 q.2.2 : ℕ) : ℝ) ^ (-ε₁)) :
    𝒩.Finite := by
  by_contra hfin
  have hinf : 𝒩.Infinite := hfin
  -- entries are ≥ 1 (they are positive)
  have habs₁ : ∀ q ∈ 𝒩, 1 ≤ uval q.1.1 q.1.2 := fun q hq => by
    have h := (habs q hq).1
    rwa [abs_of_pos (uval_pos _ _)] at h
  have habs₂ : ∀ q ∈ 𝒩, 1 ≤ uval q.2.1 q.2.2 := fun q hq => by
    have h := (habs q hq).2
    rwa [abs_of_pos (uval_pos _ _)] at h
  -- the exponent-difference (ratio) maps and their injectivity
  have hrinj : Set.InjOn
      (fun q : (ℤ × ℤ) × (ℤ × ℤ) => (q.1.1 - q.2.1, q.1.2 - q.2.2)) 𝒩 := by
    intro q hq q' hq' heq
    by_contra hne
    apply (hratio q hq q' hq' hne).1
    rw [uval_div, uval_div,
      show q.1.1 - q.2.1 = q'.1.1 - q'.2.1 from congrArg Prod.fst heq,
      show q.1.2 - q.2.2 = q'.1.2 - q'.2.2 from congrArg Prod.snd heq]
  have hrinj₂ : Set.InjOn
      (fun q : (ℤ × ℤ) × (ℤ × ℤ) => (q.2.1 - q.1.1, q.2.2 - q.1.2)) 𝒩 := by
    intro q hq q' hq' heq
    by_contra hne
    apply (hratio q hq q' hq' hne).2
    rw [uval_div, uval_div,
      show q.2.1 - q.1.1 = q'.2.1 - q'.1.1 from congrArg Prod.fst heq,
      show q.2.2 - q.1.2 = q'.2.2 - q'.1.2 from congrArg Prod.snd heq]
  -- split off the small-ratio-height members
  set CQ : ℚ := |α₁| + |α₂| + 1 with hCQdef
  set small : Set ((ℤ × ℤ) × (ℤ × ℤ)) :=
    {q ∈ 𝒩 | ((height23 (q.1.1 - q.2.1) (q.1.2 - q.2.2) : ℕ) : ℝ) < ((CQ : ℚ) : ℝ) ^ 2}
    with hsmalldef
  have hsmall : small.Finite := by
    apply Set.Finite.of_finite_image
      (f := fun q : (ℤ × ℤ) × (ℤ × ℤ) => (q.1.1 - q.2.1, q.1.2 - q.2.2))
    swap
    · exact hrinj.mono (fun q hq => hq.1)
    apply Set.Finite.subset (finite_height23_le (((CQ : ℚ) : ℝ) ^ 2))
    rintro st ⟨q, ⟨-, hlt⟩, rfl⟩
    exact hlt.le
  have hbig : (𝒩 \ small).Infinite := hinf.sdiff hsmall
  -- the Subspace theorem at n = 3
  obtain ⟨T, hTproper, hTcover⟩ := evertseSchlickewei_rat (n := 3) (by norm_num)
    {Rat.AbsoluteValue.real, padic 2, padic 3} (Lforms3 α₁ α₂)
    (fun v _ => lforms3_linearIndependent α₁ α₂ v) (ε₁ / 4) (by positivity)
  set xv : (ℤ × ℤ) × (ℤ × ℤ) → (Fin 3 → ℚ) := fun q =>
    ![((round (α₁ * uval q.1.1 q.1.2 + α₂ * uval q.2.1 q.2.2) : ℤ) : ℚ),
      uval q.1.1 q.1.2, uval q.2.1 q.2.2] with hxvdef
  have hxvne : ∀ q, xv q ≠ 0 := by
    intro q h0
    have h1 := congrFun h0 1
    simp only [hxvdef, Matrix.cons_val_one, Pi.zero_apply] at h1
    exact (uval_pos q.1.1 q.1.2).ne' h1
  have hcover : ∀ q ∈ 𝒩 \ small, ∃ W ∈ T, xv q ∈ W := by
    intro q hq
    obtain ⟨hqN, hqns⟩ := hq
    have hqbig : ((CQ : ℚ) : ℝ) ^ 2
        ≤ ((height23 (q.1.1 - q.2.1) (q.1.2 - q.2.2) : ℕ) : ℝ) := by
      by_contra hlt
      exact hqns ⟨hqN, by linarith⟩
    apply hTcover (xv q) (hxvne q)
    have h := member_solves α₁ α₂ ε₁ hε₁ q.1.1 q.1.2 q.2.1 q.2.2
      (happrox q hqN) (by rw [hCQdef] at hqbig; exact_mod_cast hqbig)
    have hexp : (-(3 : ℝ) - ε₁ / 4) = (-((3 : ℕ) : ℝ) - ε₁ / 4) := by norm_num
    rw [hxvdef]
    rw [hexp] at h
    exact h
  -- pigeonhole: one subspace contains infinitely many member vectors
  have hWex : ∃ W ∈ T, {q ∈ 𝒩 \ small | xv q ∈ W}.Infinite := by
    by_contra hall
    push Not at hall
    apply hbig
    have hcov : (𝒩 \ small) ⊆ ⋃ W ∈ T, {q ∈ 𝒩 \ small | xv q ∈ W} := by
      intro q hq
      obtain ⟨W, hWT, hxW⟩ := hcover q hq
      exact Set.mem_biUnion hWT ⟨hq, hxW⟩
    exact Set.Finite.subset (T.finite_toSet.biUnion
      (fun W hW => hall W (Finset.mem_coe.mp hW))) hcov
  obtain ⟨W, hWT, hWinf⟩ := hWex
  set F : Set ((ℤ × ℤ) × (ℤ × ℤ)) := {q ∈ 𝒩 \ small | xv q ∈ W} with hFdef
  have hFsub : F ⊆ 𝒩 := fun q hq => hq.1.1
  -- a nonzero functional vanishing on W
  obtain ⟨f, hf0, hfW⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
    (lt_top_iff_ne_top.mpr (hTproper W hWT)) inferInstance
  set a₀ : ℚ := f (fun j => if (0 : Fin 3) = j then 1 else 0) with ha₀def
  set a₁ : ℚ := f (fun j => if (1 : Fin 3) = j then 1 else 0) with ha₁def
  set a₂ : ℚ := f (fun j => if (2 : Fin 3) = j then 1 else 0) with ha₂def
  have hfx : ∀ x : Fin 3 → ℚ, f x = x 0 * a₀ + x 1 * a₁ + x 2 * a₂ := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ f x, Fin.sum_univ_three]
    simp only [smul_eq_mul, ha₀def, ha₁def, ha₂def]
  have hrel : ∀ q ∈ F,
      ((round (α₁ * uval q.1.1 q.1.2 + α₂ * uval q.2.1 q.2.2) : ℤ) : ℚ) * a₀
        + uval q.1.1 q.1.2 * a₁ + uval q.2.1 q.2.2 * a₂ = 0 := by
    intro q hq
    have hfx0 : f (xv q) = 0 := by
      have h1 : f (xv q) ∈ W.map f := Submodule.mem_map_of_mem hq.2
      rwa [hfW, Submodule.mem_bot] at h1
    rw [hfx (xv q)] at hfx0
    simpa only [hxvdef, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] using hfx0
  have hFne : F.Nonempty := hWinf.nonempty
  have hane : ¬(a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0) := by
    rintro ⟨h0, h1, h2⟩
    apply hf0
    apply LinearMap.ext
    intro x
    rw [hfx x, h0, h1, h2]
    simp
  -- case split on a₀
  rcases eq_or_ne a₀ 0 with ha₀0 | ha₀0
  · -- the ratio is constant on F: two members contradict `hratio`
    obtain ⟨q, hqF, q', hq'F, hne⟩ := hWinf.nontrivial
    have ha₁0 : a₁ ≠ 0 := by
      intro h1
      obtain ⟨r, hrF⟩ := hFne
      have h := hrel r hrF
      rw [ha₀0, h1, mul_zero, mul_zero, zero_add, zero_add] at h
      have ha₂0 : a₂ = 0 :=
        (mul_eq_zero.mp h).resolve_left (uval_pos r.2.1 r.2.2).ne'
      exact hane ⟨ha₀0, h1, ha₂0⟩
    have hconst : ∀ r ∈ F, uval r.1.1 r.1.2 / uval r.2.1 r.2.2 = -a₂ / a₁ := by
      intro r hrF
      have h := hrel r hrF
      rw [ha₀0, mul_zero, zero_add] at h
      have hu₂ : uval r.2.1 r.2.2 ≠ 0 := (uval_pos r.2.1 r.2.2).ne'
      field_simp
      linarith
    have := (hratio q (hFsub hqF) q' (hFsub hq'F) hne).1
    rw [hconst q hqF, hconst q' hq'F] at this
    exact this rfl
  · -- a₀ ≠ 0: the relation gives `p₀ = λ₁u₁ + λ₂u₂`; set β = λ − α
    set β₁ : ℚ := -a₁ / a₀ - α₁ with hβ₁def
    set β₂ : ℚ := -a₂ / a₀ - α₂ with hβ₂def
    have hdisteq : ∀ q ∈ F,
        (α₁ * uval q.1.1 q.1.2 + α₂ * uval q.2.1 q.2.2).distToNearestInt
          = |β₁ * uval q.1.1 q.1.2 + β₂ * uval q.2.1 q.2.2| := by
      intro q hq
      have h := hrel q hq
      have hp₀ : ((round (α₁ * uval q.1.1 q.1.2 + α₂ * uval q.2.1 q.2.2) : ℤ) : ℚ)
          = (-a₁ / a₀) * uval q.1.1 q.1.2 + (-a₂ / a₀) * uval q.2.1 q.2.2 := by
        field_simp
        linarith
      show |α₁ * uval q.1.1 q.1.2 + α₂ * uval q.2.1 q.2.2
          - ((round (α₁ * uval q.1.1 q.1.2 + α₂ * uval q.2.1 q.2.2) : ℤ) : ℚ)|
        = |β₁ * uval q.1.1 q.1.2 + β₂ * uval q.2.1 q.2.2|
      rw [hp₀, show α₁ * uval q.1.1 q.1.2 + α₂ * uval q.2.1 q.2.2
          - ((-a₁ / a₀) * uval q.1.1 q.1.2 + (-a₂ / a₀) * uval q.2.1 q.2.2)
          = -(β₁ * uval q.1.1 q.1.2 + β₂ * uval q.2.1 q.2.2) by
        rw [hβ₁def, hβ₂def]; ring, abs_neg]
    -- a positive lower bound on the distance makes F finite — contradiction machine
    have hfloor : ∀ b : ℚ, 0 < b →
        (∀ q ∈ F, b ≤ (α₁ * uval q.1.1 q.1.2
          + α₂ * uval q.2.1 q.2.2).distToNearestInt) → False := by
      intro b hb hle
      apply hWinf
      have hbR : (0 : ℝ) < ((b : ℚ) : ℝ) := by exact_mod_cast hb
      set Bb : ℝ := (((b : ℚ) : ℝ)⁻¹) ^ (ε₁⁻¹) with hBbdef
      apply Set.Finite.subset
        (Set.Finite.prod (finite_height23_le Bb) (finite_height23_le Bb))
      intro q hqF
      have hHb : ((height23 q.1.1 q.1.2 * height23 q.2.1 q.2.2 : ℕ) : ℝ) ≤ Bb := by
        have h1 : ((b : ℚ) : ℝ)
            ≤ ((height23 q.1.1 q.1.2 * height23 q.2.1 q.2.2 : ℕ) : ℝ) ^ (-ε₁) := by
          have h2 : ((b : ℚ) : ℝ) ≤ (((α₁ * uval q.1.1 q.1.2
              + α₂ * uval q.2.1 q.2.2).distToNearestInt : ℚ) : ℝ) := by
            exact_mod_cast hle q hqF
          exact le_of_lt (lt_of_le_of_lt h2 (happrox q (hFsub hqF)))
        have hH0 : (0 : ℝ) < ((height23 q.1.1 q.1.2 * height23 q.2.1 q.2.2 : ℕ) : ℝ) := by
          have ha := one_le_height23 q.1.1 q.1.2
          have hbb := one_le_height23 q.2.1 q.2.2
          exact_mod_cast Nat.mul_pos ha hbb
        -- b ≤ H^{-ε₁}  ⟹  H^{ε₁} ≤ b⁻¹  ⟹  H ≤ (b⁻¹)^{1/ε₁}
        have h3 : ((height23 q.1.1 q.1.2 * height23 q.2.1 q.2.2 : ℕ) : ℝ) ^ ε₁
            ≤ ((b : ℚ) : ℝ)⁻¹ := by
          have h4 : ((height23 q.1.1 q.1.2 * height23 q.2.1 q.2.2 : ℕ) : ℝ) ^ ε₁
              * ((b : ℚ) : ℝ) ≤ 1 := by
            calc ((height23 q.1.1 q.1.2 * height23 q.2.1 q.2.2 : ℕ) : ℝ) ^ ε₁
                  * ((b : ℚ) : ℝ)
                ≤ ((height23 q.1.1 q.1.2 * height23 q.2.1 q.2.2 : ℕ) : ℝ) ^ ε₁
                  * ((height23 q.1.1 q.1.2 * height23 q.2.1 q.2.2 : ℕ) : ℝ) ^ (-ε₁) :=
                  mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hH0.le _)
              _ = 1 := by
                  rw [← Real.rpow_add hH0]
                  norm_num
          rw [← le_div_iff₀ hbR] at h4
          rwa [one_div] at h4
        calc ((height23 q.1.1 q.1.2 * height23 q.2.1 q.2.2 : ℕ) : ℝ)
            = (((height23 q.1.1 q.1.2 * height23 q.2.1 q.2.2 : ℕ) : ℝ) ^ ε₁) ^ ε₁⁻¹ := by
              rw [← Real.rpow_mul hH0.le, mul_inv_cancel₀ hε₁.ne', Real.rpow_one]
          _ ≤ (((b : ℚ) : ℝ)⁻¹) ^ ε₁⁻¹ :=
              Real.rpow_le_rpow (Real.rpow_pos_of_pos hH0 _).le h3 (by positivity)
      constructor
      · show ((height23 q.1.1 q.1.2 : ℕ) : ℝ) ≤ Bb
        have h1 : (height23 q.1.1 q.1.2 : ℕ) ≤ height23 q.1.1 q.1.2 * height23 q.2.1 q.2.2 :=
          Nat.le_mul_of_pos_right _ (one_le_height23 q.2.1 q.2.2)
        calc ((height23 q.1.1 q.1.2 : ℕ) : ℝ)
            ≤ ((height23 q.1.1 q.1.2 * height23 q.2.1 q.2.2 : ℕ) : ℝ) := by exact_mod_cast h1
          _ ≤ Bb := hHb
      · show ((height23 q.2.1 q.2.2 : ℕ) : ℝ) ≤ Bb
        have h1 : (height23 q.2.1 q.2.2 : ℕ) ≤ height23 q.1.1 q.1.2 * height23 q.2.1 q.2.2 :=
          Nat.le_mul_of_pos_left _ (one_le_height23 q.1.1 q.1.2)
        calc ((height23 q.2.1 q.2.2 : ℕ) : ℝ)
            ≤ ((height23 q.1.1 q.1.2 * height23 q.2.1 q.2.2 : ℕ) : ℝ) := by exact_mod_cast h1
          _ ≤ Bb := hHb
    -- sub-case analysis on the signs of β₁, β₂
    rcases lt_trichotomy β₁ 0 with hβ₁ | hβ₁ | hβ₁
    · rcases lt_trichotomy β₂ 0 with hβ₂ | hβ₂ | hβ₂
      · -- both negative: distance ≥ -β₁ > 0
        apply hfloor (-β₁) (by linarith)
        intro q hq
        rw [hdisteq q hq]
        have hu₁ := habs₁ q (hFsub hq)
        have hu₂0 := uval_pos q.2.1 q.2.2
        have h1 : β₁ * uval q.1.1 q.1.2 + β₂ * uval q.2.1 q.2.2 ≤ β₁ := by
          nlinarith
        calc -β₁ ≤ -(β₁ * uval q.1.1 q.1.2 + β₂ * uval q.2.1 q.2.2) := by linarith
          _ ≤ |β₁ * uval q.1.1 q.1.2 + β₂ * uval q.2.1 q.2.2| := neg_le_abs _
      · -- β₂ = 0: distance = |β₁|·u₁ ≥ -β₁ > 0
        apply hfloor (-β₁) (by linarith)
        intro q hq
        rw [hdisteq q hq, hβ₂, zero_mul, add_zero]
        have hu₁ := habs₁ q (hFsub hq)
        have h1 : β₁ * uval q.1.1 q.1.2 ≤ β₁ := by nlinarith
        calc -β₁ ≤ -(β₁ * uval q.1.1 q.1.2) := by linarith
          _ ≤ |β₁ * uval q.1.1 q.1.2| := neg_le_abs _
      · -- β₁ < 0 < β₂: the swapped opposite-sign case
        apply hWinf
        have hswap : F.Finite ↔ (Prod.swap '' F).Finite := by
          constructor
          · exact fun h => h.image _
          · intro h
            have := h.image Prod.swap
            rwa [Set.image_image, show (fun q : (ℤ × ℤ) × (ℤ × ℤ) =>
              Prod.swap (Prod.swap q)) = id from funext (fun q => Prod.swap_swap q),
              Set.image_id] at this
        rw [hswap]
        apply opposite_case_finite α₂ α₁ β₂ β₁ ε₁ hε₁ hβ₂ hβ₁ (Prod.swap '' F)
        · rintro q ⟨r, hrF, rfl⟩
          exact habs₁ r (hFsub hrF)
        · rintro q ⟨r, hrF, rfl⟩ q' ⟨r', hr'F, rfl⟩ heq
          simp only [Prod.swap] at heq ⊢
          have := hrinj₂ (hFsub hrF) (hFsub hr'F) heq
          rw [this]
        · rintro q ⟨r, hrF, rfl⟩
          have h := hdisteq r hrF
          simp only [Prod.swap]
          rw [show α₂ * uval r.2.1 r.2.2 + α₁ * uval r.1.1 r.1.2
              = α₁ * uval r.1.1 r.1.2 + α₂ * uval r.2.1 r.2.2 by ring, h,
            show β₂ * uval r.2.1 r.2.2 + β₁ * uval r.1.1 r.1.2
              = β₁ * uval r.1.1 r.1.2 + β₂ * uval r.2.1 r.2.2 by ring]
        · rintro q ⟨r, hrF, rfl⟩
          simp only [Prod.swap]
          rw [show α₂ * uval r.2.1 r.2.2 + α₁ * uval r.1.1 r.1.2
              = α₁ * uval r.1.1 r.1.2 + α₂ * uval r.2.1 r.2.2 by ring]
          exact hpos r (hFsub hrF)
        · rintro q ⟨r, hrF, rfl⟩
          simp only [Prod.swap]
          rw [show α₂ * uval r.2.1 r.2.2 + α₁ * uval r.1.1 r.1.2
              = α₁ * uval r.1.1 r.1.2 + α₂ * uval r.2.1 r.2.2 by ring,
            show height23 r.2.1 r.2.2 * height23 r.1.1 r.1.2
              = height23 r.1.1 r.1.2 * height23 r.2.1 r.2.2 from Nat.mul_comm _ _]
          exact happrox r (hFsub hrF)
    · -- β₁ = 0
      rcases lt_trichotomy β₂ 0 with hβ₂ | hβ₂ | hβ₂
      · -- distance = |β₂|·u₂ ≥ -β₂ > 0
        apply hfloor (-β₂) (by linarith)
        intro q hq
        rw [hdisteq q hq, hβ₁, zero_mul, zero_add]
        have hu₂ := habs₂ q (hFsub hq)
        have h1 : β₂ * uval q.2.1 q.2.2 ≤ β₂ := by nlinarith
        calc -β₂ ≤ -(β₂ * uval q.2.1 q.2.2) := by linarith
          _ ≤ |β₂ * uval q.2.1 q.2.2| := neg_le_abs _
      · -- β₁ = β₂ = 0: distance vanishes, contradicting positivity
        obtain ⟨q, hqF⟩ := hFne
        have h := hpos q (hFsub hqF)
        rw [hdisteq q hqF, hβ₁, hβ₂, zero_mul, zero_mul, add_zero, abs_zero] at h
        exact lt_irrefl 0 h
      · -- distance = β₂·u₂ ≥ β₂ > 0
        apply hfloor β₂ hβ₂
        intro q hq
        rw [hdisteq q hq, hβ₁, zero_mul, zero_add]
        have hu₂ := habs₂ q (hFsub hq)
        have h1 : β₂ ≤ β₂ * uval q.2.1 q.2.2 := by nlinarith
        calc β₂ ≤ β₂ * uval q.2.1 q.2.2 := h1
          _ ≤ |β₂ * uval q.2.1 q.2.2| := le_abs_self _
    · rcases lt_trichotomy β₂ 0 with hβ₂ | hβ₂ | hβ₂
      · -- β₁ > 0 > β₂: the direct opposite-sign case
        exact hWinf (opposite_case_finite α₁ α₂ β₁ β₂ ε₁ hε₁ hβ₁ hβ₂ F
          (fun q hq => habs₂ q (hFsub hq))
          (hrinj.mono hFsub) (fun q hq => hdisteq q hq)
          (fun q hq => hpos q (hFsub hq)) (fun q hq => happrox q (hFsub hq)))
      · -- β₂ = 0: distance = β₁·u₁ ≥ β₁ > 0
        apply hfloor β₁ hβ₁
        intro q hq
        rw [hdisteq q hq, hβ₂, zero_mul, add_zero]
        have hu₁ := habs₁ q (hFsub hq)
        have h1 : β₁ ≤ β₁ * uval q.1.1 q.1.2 := by nlinarith
        calc β₁ ≤ β₁ * uval q.1.1 q.1.2 := h1
          _ ≤ |β₁ * uval q.1.1 q.1.2| := le_abs_self _
      · -- both positive: distance ≥ β₁ > 0
        apply hfloor β₁ hβ₁
        intro q hq
        rw [hdisteq q hq]
        have hu₁ := habs₁ q (hFsub hq)
        have hu₂0 := uval_pos q.2.1 q.2.2
        have h1 : β₁ ≤ β₁ * uval q.1.1 q.1.2 + β₂ * uval q.2.1 q.2.2 := by
          nlinarith
        calc β₁ ≤ β₁ * uval q.1.1 q.1.2 + β₂ * uval q.2.1 q.2.2 := h1
          _ ≤ |β₁ * uval q.1.1 q.1.2 + β₂ * uval q.2.1 q.2.2| := le_abs_self _

/-- **Theorem 1.3(i) of [NKR25], repaired and derived** — the statement of the
retired cited axiom `NKR.sUnit_pair_integrality` with the strict-positivity
hypothesis `hpos` added (without it the statement is *false*:
`NKR.thm13i_unrepaired_false`), now a **theorem** resting only on
`Subspace.evertseSchlickewei`.  Since the (repaired) hypotheses already force the
family to be finite (`pair_finite`), the integrality conclusion holds vacuously;
consumers invoke this exactly as they would the axiom, deriving their contradiction
from `hinf`.  The hypotheses `hα₁`, `hα₂`, `hP2` are inherited from the source
statement (fidelity) but not needed. -/
@[category research solved, AMS 11, ref "NKR25", group "three_halves_m4"]
theorem sUnit_pair_integrality_of_subspace
    (α₁ α₂ : ℚ) (_hα₁ : α₁ ≠ 0) (_hα₂ : α₂ ≠ 0) (ε₁ : ℝ) (hε₁ : 0 < ε₁)
    (𝒩 : Set ((ℤ × ℤ) × (ℤ × ℤ))) (hinf : 𝒩.Infinite)
    (habs : ∀ q ∈ 𝒩, 1 ≤ |uval q.1.1 q.1.2| ∧ 1 ≤ |uval q.2.1 q.2.2|)
    (_hP2 : ∀ q ∈ 𝒩, uval q.1.1 q.1.2 ≠ -uval q.2.1 q.2.2)
    (hratio : ∀ q ∈ 𝒩, ∀ q' ∈ 𝒩, q ≠ q' →
      uval q.1.1 q.1.2 / uval q.2.1 q.2.2 ≠ uval q'.1.1 q'.1.2 / uval q'.2.1 q'.2.2 ∧
      uval q.2.1 q.2.2 / uval q.1.1 q.1.2 ≠ uval q'.2.1 q'.2.2 / uval q'.1.1 q'.1.2)
    (hpos : ∀ q ∈ 𝒩,
      0 < (α₁ * uval q.1.1 q.1.2 + α₂ * uval q.2.1 q.2.2).distToNearestInt)
    (happrox : ∀ q ∈ 𝒩,
      ((α₁ * uval q.1.1 q.1.2 + α₂ * uval q.2.1 q.2.2).distToNearestInt : ℝ)
        < ((CZ.height23 q.1.1 q.1.2 * CZ.height23 q.2.1 q.2.2 : ℕ) : ℝ) ^ (-ε₁)) :
    ∃ q ∈ 𝒩, (∃ n : ℤ, uval q.1.1 q.1.2 = n) ∧ (∃ n : ℤ, uval q.2.1 q.2.2 = n) :=
  absurd (pair_finite α₁ α₂ ε₁ hε₁ 𝒩 habs hratio hpos happrox) hinf.not_finite

end NKR
