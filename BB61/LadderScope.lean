/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.LadderReduction
import BB61.TraceLadder
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# M3 Corollary 6: which ladders may enter a proof

`note-1061-M3.html` Corollary 6 is the scope restriction that M3 attached to the trace-ladder
reduction of `BB61/LadderReduction.lean`:

> `τ̄_*λ = Leb` forces `λ̂(γ) = 0` **exactly** for `γ ∈ α^ℤ·(ℤ∖{0}) ∩ 𝔡⁻¹`.  For `γ ∈ 𝔡⁻¹`
> outside that set the hypothesis says nothing, so the corresponding ladder `Tr(γαᵏ)` cannot
> appear in a proof by contradiction.

It is aimed at M1.  M1 Proposition 15 (`BB61/TraceLadder.lean`) identified the ladders as the
whole codifferent `𝔡⁻¹ = f'(α)⁻¹ℤ[α]`, and M1's finding F8 then measured the difference: at
`α = 1 + √2` the **half-ladder** `1,1,3,7,17,41,…` (`γ = 1/2`) plateaus at `3.4511464·10⁻²`
against the trace ladder's `7.6370923·10⁻⁵`, a factor `452`, so M1 prescribed *maximise over*
`γ ∈ 𝔡⁻¹/α^ℤ`.  Corollary 6 says that prescription is a **detection** instruction and not a
proof instruction: a proof by contradiction may only use the ladders whose vanishing the
hypothesis actually supplies, and those are `h·Tr_m` with `h ∈ ℤ`, nothing else.

## What is proved here

The positive half is a corollary of Theorem 4 once the `α`-orbit is written out.  In ladder
coordinates the frequency `γ = n αʲ`, `j ∈ ℤ`, has `Tr(γαᵏ) = n·T_{k+j}` for the two-sided
trace ladder `T_n = αⁿ + βⁿ` (`traceSeqZ`, grounded by `traceSeqZ_cast` at a unit), and
`tendsto_futureCoeff_orbit` says every such ladder has the *same* limit `Φ_n(μ)`: **an
`α`-orbit of integer frequencies carries one constraint, not infinitely many**, no matter
where one enters it.

The negative half is a parity argument, and it is the reason the example in the note is
`α = 1 + √2`.  `Tr(u + vα) = 2u + av` (`trForm`), so

`1/2 ∈ 𝔡⁻¹  ⟺  Tr(ℤ[α]) ⊆ 2ℤ  ⟺  2 ∣ a`   (`two_dvd_trForm_iff`),

and exactly when the half-ladder exists it is *odd at the origin* while `T` is even
throughout, hence so is `n·T_{k+j}` for every `n` and every entry point `j ∈ ℤ`
(`two_dvd_traceSeqZ`).  So the half-ladder is not the ladder of any frequency in `α^ℤ·ℤ`
(`not_intOrbitLadder_halfLad`), and the hypothesis places nothing on it.  One divisibility
condition, `2 ∣ a`, does both halves of the corollary: it is what *creates* the competitor and
what *disqualifies* it.

`no_half_character` is the same fact in the analytic register, and is what "says nothing"
means for measures rather than for ladders: `e(x/2)` is not a function of `x mod 1`, so no
hypothesis about `τ̄_*λ` on `ℝ/ℤ` can constrain `λ̂(1/2)` at all.

## What is not proved here

* **The classification is not complete.**  Parity certifies `1/2 ∉ α^ℤ·ℤ`, which is the case
  the note argues and the only one M1's F8 needs.  It is not a decision procedure for
  membership in `α^ℤ·ℤ`: `lad 2 4` at `1+√2` is even throughout and is still not in the orbit
  (its frequency is `(1+α)/2`).  An all-even ladder need not be admissible; an odd one is
  certainly not.
* **`IntOrbitLadder` is the ladder-level definition** of `α^ℤ·(ℤ∖{0})`, justified by
  `traceSeqZ_cast` (`T_n = αⁿ + βⁿ` for `n ∈ ℤ`) plus linearity of the trace, not derived
  inside the number-field API of `BB61/TraceLadder.lean`.  `halfLad_isTraceLadder` is the
  bridge in the other direction: the half-ladder really is `Tr(γαᵏ)` for a genuine
  `γ ∈ 𝔡⁻¹`, by Proposition 15, so it is a competitor and not a spurious sequence.

## References

* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*,
  Cambridge Tracts in Math. 193, CUP 2012.  Problem 10.61.
* `note-1061-M3.html` §4, Corollary 6 and the paragraph after it; `note-1061-M1.html` §6
  (Proposition 15, finding F8 and the plateau table).  Numerics `BB61/m3_cor6_lean.py`.
-/

noncomputable section

namespace BB61

open Filter Topology MeasureTheory Polynomial TraceLadder

namespace QuadSetup

variable (P : QuadSetup)

/-! ## The trace form on `ℤ[α]`, and when `1/2` is a legal frequency -/

/-- The field trace on `ℤ[α]` in the basis `(1, α)`: `Tr(u + vα) = 2u + av`. -/
def trForm (u v : ℤ) : ℤ := 2 * u + P.a * v

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem trForm_cast (u v : ℤ) :
    ((P.trForm u v : ℤ) : ℝ) = ((u : ℝ) + v * P.α) + ((u : ℝ) + v * P.β) := by
  simp only [trForm]
  push_cast
  linear_combination (-(v : ℝ)) * P.alpha_add_beta

/-- **`γ = 1/2` lies in the codifferent exactly when `2 ∣ a`.**  `Tr(z/2) ∈ ℤ` for every
`z ∈ ℤ[α]` says `Tr(ℤ[α]) ⊆ 2ℤ`, and `Tr(u + vα) = 2u + av` makes that `2 ∣ a`.  This is M1's
own reason for `γ = 1/2` being legal at `1 + √2` ("every `Tr(αᵏ)` is even"), stated as an
iff so that it also disqualifies the odd-trace case. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem two_dvd_trForm_iff : (∀ u v : ℤ, (2 : ℤ) ∣ P.trForm u v) ↔ (2 : ℤ) ∣ P.a := by
  constructor
  · intro h
    have := h 0 1
    simpa [trForm] using this
  · rintro ⟨c, hc⟩ u v
    exact ⟨u + c * v, by simp only [trForm, hc]; ring⟩

/-- The concrete form of `1/2 ∈ 𝔡⁻¹`: when `a = 2c`, the real number `Tr(u + vα)/2` is the
integer `u + cv`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem half_trForm_eq {c : ℤ} (ha : P.a = 2 * c) (u v : ℤ) :
    (((u : ℝ) + v * P.α) + ((u : ℝ) + v * P.β)) / 2 = ((u + c * v : ℤ) : ℝ) := by
  rw [← P.trForm_cast u v]
  simp only [trForm, ha]
  push_cast
  ring

/-! ## The two-sided trace ladder `Tr(αⁿ)`, `n ∈ ℤ` -/

/-- `Tr(αⁿ)` for `n : ℤ`.  At a unit `αβ = ∓1`, so `α^{-m} + β^{-m} = (-b)^m(αᵐ + βᵐ)` and
the backwards half of the ladder is the forwards half up to sign. -/
def traceSeqZ (n : ℤ) : ℤ :=
  if 0 ≤ n then P.traceSeq n.toNat else (-P.b) ^ (-n).toNat * P.traceSeq (-n).toNat

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem traceSeqZ_natCast (k : ℕ) : P.traceSeqZ (k : ℤ) = P.traceSeq k := by
  simp [traceSeqZ]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem beta_ne_zero_of_unit (hb : P.b = 1 ∨ P.b = -1) : P.β ≠ 0 := by
  intro h
  have hab := P.alpha_mul_beta
  rw [h, mul_zero] at hab
  rcases hb with hb | hb <;> rw [hb] at hab <;> norm_num at hab

/-- **The grounding of `traceSeqZ`**: at a quadratic unit it really is `Tr(αⁿ) = αⁿ + βⁿ`
for every `n ∈ ℤ`, negative exponents included. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem traceSeqZ_cast (hb : P.b = 1 ∨ P.b = -1) (n : ℤ) :
    ((P.traceSeqZ n : ℤ) : ℝ) = P.α ^ n + P.β ^ n := by
  have hα0 : P.α ≠ 0 := ne_of_gt P.alpha_pos
  have hβ0 : P.β ≠ 0 := P.beta_ne_zero_of_unit hb
  rcases le_or_gt 0 n with hn | hn
  · lift n to ℕ using hn with m
    rw [P.traceSeqZ_natCast, zpow_natCast, zpow_natCast]
    exact_mod_cast P.traceSeq_cast m
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -(m : ℤ) := ⟨(-n).toNat, by omega⟩
    have hAne : P.α ^ m ≠ 0 := pow_ne_zero _ hα0
    have hBne : P.β ^ m ≠ 0 := pow_ne_zero _ hβ0
    have hAB : P.α ^ m * P.β ^ m = (-(P.b : ℝ)) ^ m := by
      rw [← mul_pow, P.alpha_mul_beta]
    have hu1 : (-(P.b : ℝ)) * (-(P.b : ℝ)) = 1 := by
      rcases hb with h | h <;> rw [h] <;> norm_num
    have huu : (-(P.b : ℝ)) ^ m * (-(P.b : ℝ)) ^ m = 1 := by
      rw [← mul_pow, hu1, one_pow]
    have hune : (-(P.b : ℝ)) ^ m ≠ 0 := by
      intro h; rw [h, mul_zero] at huu; norm_num at huu
    have hm0 : m ≠ 0 := by omega
    have hval : P.traceSeqZ (-(m : ℤ)) = (-P.b) ^ m * P.traceSeq m := by
      simp [traceSeqZ, hm0]
    rw [hval]
    push_cast
    rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, inv_add_inv hAne hBne, hAB,
      eq_div_iff hune]
    linear_combination ((P.traceSeq m : ℤ) : ℝ) * huu + P.traceSeq_cast m

/-! ## Evenness: the invariant that separates the ladders -/

/-- When `2 ∣ a` the trace ladder is even throughout: `T₀ = 2`, `T₁ = a`, and the recurrence
`T_{k+2} = a T_{k+1} + b T_k` propagates it. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem two_dvd_traceSeq (ha : (2 : ℤ) ∣ P.a) (k : ℕ) : (2 : ℤ) ∣ P.traceSeq k := by
  have key : ∀ k : ℕ, (2 : ℤ) ∣ P.traceSeq k ∧ (2 : ℤ) ∣ P.traceSeq (k + 1) := by
    intro k
    induction k with
    | zero => exact ⟨by rw [P.traceSeq_zero], by rw [P.traceSeq_one]; exact ha⟩
    | succ k ih =>
        refine ⟨ih.2, ?_⟩
        rw [P.traceSeq_add_two]
        exact dvd_add (ih.2.mul_left _) (ih.1.mul_left _)
  exact (key k).1

/-- Evenness survives the backwards half of the ladder too: `T_{-m} = (-b)^m T_m`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem two_dvd_traceSeqZ (ha : (2 : ℤ) ∣ P.a) (n : ℤ) : (2 : ℤ) ∣ P.traceSeqZ n := by
  rw [traceSeqZ]
  split
  · exact P.two_dvd_traceSeq ha _
  · exact (P.two_dvd_traceSeq ha _).mul_left _

/-! ## The half-ladder -/

/-- Ladders are `ℤ`-linear in their two initial terms. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem lad_smul (c h₀ h₁ : ℤ) (k : ℕ) : P.lad (c * h₀) (c * h₁) k = c * P.lad h₀ h₁ k := by
  have key : ∀ k : ℕ, P.lad (c * h₀) (c * h₁) k = c * P.lad h₀ h₁ k
      ∧ P.lad (c * h₀) (c * h₁) (k + 1) = c * P.lad h₀ h₁ (k + 1) := by
    intro k
    induction k with
    | zero => exact ⟨by rw [P.lad_zero, P.lad_zero], by rw [P.lad_one, P.lad_one]⟩
    | succ k ih =>
        refine ⟨ih.2, ?_⟩
        rw [P.lad_add_two, P.lad_add_two, ih.1, ih.2]
        ring
  exact (key k).1

/-- **The half-ladder** `Tr(αᵏ/2)`, available when `a = 2c`: the ladder started at `(1, c)`.
At `1 + √2` it is `1,1,3,7,17,41,…` and at `2 + √3` it is `1,2,7,26,97,…` — M1's F8 table. -/
def halfLad (c : ℤ) : ℕ → ℤ := P.lad 1 c

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem halfLad_zero (c : ℤ) : P.halfLad c 0 = 1 := rfl

/-- The half-ladder is what its name says: twice it is the trace ladder. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem two_mul_halfLad {c : ℤ} (ha : P.a = 2 * c) (k : ℕ) :
    2 * P.halfLad c k = P.traceSeq k := by
  have h : P.traceSeq k = P.lad (2 * 1) (2 * c) k := by
    rw [traceSeq, ha]
    norm_num
  rw [h, P.lad_smul, halfLad]

/-- **M1 Proposition 15 applied to the half-ladder**: it is `Tr(γαᵏ)` for a genuine element
`γ` of the codifferent, so it is a real competitor to the trace ladder and not a spurious
integer sequence.  This is `BB61/TraceLadder.lean`'s `lad_iff_trace_ladder` at `(h₀,h₁) =
(1,c)`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem halfLad_isTraceLadder {L : Type*} [Field L] [NumberField L] {α : L}
    (hgen : Algebra.adjoin ℚ ({α} : Set L) = ⊤) (hint : IsIntegral ℤ α)
    (hmin : minpoly ℤ α = P.charPoly) (c : ℤ) :
    ∃ lam ∈ codiff α, ∀ k, ladder α lam k = ((P.halfLad c k : ℤ) : ℚ) :=
  (P.lad_iff_trace_ladder hgen hint hmin _).mp ⟨1, c, rfl⟩

/-! ## Corollary 6 -/

/-- **The ladders a proof by contradiction may use.**  `γ ∈ α^ℤ·(ℤ∖{0})` means `γ = n αʲ`
with `n ≠ 0` and `j ∈ ℤ`, and then `Tr(γαᵏ) = n·Tr(α^{k+j}) = n·T_{k+j}` by linearity of the
trace; `traceSeqZ_cast` is the grounding of `T` at negative indices. -/
def IntOrbitLadder (h : ℕ → ℤ) : Prop :=
  ∃ n j : ℤ, n ≠ 0 ∧ ∀ k : ℕ, h k = n * P.traceSeqZ ((k : ℤ) + j)

/-- **Corollary 6, the positive half.**  Every ladder in the `α`-orbit of the integer
frequency `n` has the *same* limit `Φ_n(μ)`, whatever entry point `j ∈ ℤ` one chooses: an
orbit carries one constraint, not infinitely many. -/
@[category research solved, AMS 11 37, ref "Bug12", group "bugeaud_10_61"]
theorem tendsto_futureCoeff_orbit (hα : 1 < P.α) (μ : Measure Shift) [IsProbabilityMeasure μ]
    (hinv : Measure.map shiftZ μ = μ) (n j : ℤ) :
    Tendsto (fun m : ℕ => P.futureCoeff μ (n * P.traceSeqZ ((m : ℤ) + j))) atTop
      (𝓝 (P.phiCoeff μ n)) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (0 : ℤ) ≤ (N : ℤ) + j := ⟨j.natAbs, by omega⟩
  set t : ℕ := ((N : ℤ) + j).toNat with ht
  have hshift : Tendsto (fun m : ℕ => m - N + t) atTop atTop :=
    (tendsto_add_atTop_nat t).comp (tendsto_sub_atTop_nat N)
  have hbase := (P.tendsto_futureCoeff hα μ hinv n).comp hshift
  refine Filter.Tendsto.congr' ?_ hbase
  filter_upwards [eventually_ge_atTop N] with m hm
  have hkey : ((m : ℤ) + j) = ((m - N + t : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_sub hm, ht, Int.toNat_of_nonneg hN]
    ring
  simp only [Function.comp_apply, hkey, P.traceSeqZ_natCast]

/-- Every admissible ladder is even throughout, as soon as `2 ∣ a`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem two_dvd_of_intOrbitLadder (ha : (2 : ℤ) ∣ P.a) {h : ℕ → ℤ}
    (hh : P.IntOrbitLadder h) (k : ℕ) : (2 : ℤ) ∣ h k := by
  obtain ⟨n, j, -, hk⟩ := hh
  rw [hk]
  exact (P.two_dvd_traceSeqZ ha _).mul_left n

/-- **Corollary 6, the negative half.**  Exactly when the half-ladder exists — `2 ∣ a`, which
is M1's reason for `γ = 1/2` being legal — it is disqualified: it is odd at the origin, and
every ladder of a frequency in `α^ℤ·ℤ` is even everywhere.  So `1/2 ∉ α^ℤ·(ℤ∖{0})`, and the
hypothesis `τ̄_*λ = Leb` places no condition on `λ̂(1/2)`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem not_intOrbitLadder_halfLad {c : ℤ} (ha : P.a = 2 * c) :
    ¬ P.IntOrbitLadder (P.halfLad c) := by
  intro hh
  have h2 : (2 : ℤ) ∣ P.halfLad c 0 := P.two_dvd_of_intOrbitLadder ⟨c, ha⟩ hh 0
  rw [P.halfLad_zero] at h2
  norm_num at h2

/-- **M3 Corollary 6.**  Under the counterexample hypothesis `F_*μ = Leb`, *every* ladder in
the `α`-orbit of a nonzero integer frequency has vanishing limit — and the half-ladder is not
one of them.  The proof-relevant ladders are `h·Tr_m`, `h ∈ ℤ`, and nothing else: M1's
"maximise over `γ ∈ 𝔡⁻¹/α^ℤ`" is a detection instruction, not a proof instruction. -/
@[category research solved, AMS 11 37, ref "Bug12", group "bugeaud_10_61"]
theorem cor6 (hα : 1 < P.α) {c : ℤ} (ha : P.a = 2 * c) (μ : Measure Shift)
    [IsProbabilityMeasure μ] (hinv : Measure.map shiftZ μ = μ)
    (hmap : Measure.map P.fMap μ = (volume : Measure (AddCircle (1 : ℝ)))) :
    (∀ h : ℕ → ℤ, P.IntOrbitLadder h →
        Tendsto (fun m : ℕ => P.futureCoeff μ (h m)) atTop (𝓝 0))
      ∧ ¬ P.IntOrbitLadder (P.halfLad c) := by
  refine ⟨fun h hh => ?_, P.not_intOrbitLadder_halfLad ha⟩
  obtain ⟨n, j, hn, hk⟩ := hh
  have hlim := P.tendsto_futureCoeff_orbit hα μ hinv n j
  rw [P.phiCoeff_eq_zero μ hmap hn] at hlim
  exact hlim.congr fun m => by rw [hk m]

/-! ## What "says nothing" means for measures

The ladder statement above is about integer sequences.  Its analytic counterpart is that the
half-frequency character is not a function of the datum the hypothesis constrains: `τ̄_*λ` is a
measure on `ℝ/ℤ`, and `e(x/2)` does not descend to `ℝ/ℤ`.  No hypothesis about `τ̄` modulo one
can therefore say anything at all about `λ̂(1/2)`. -/

/-- **The half-frequency character does not descend to `ℝ/ℤ`.**  `e(x/2) = exp(πix)` changes
sign under `x ↦ x + 1`, so it is not a function on `AddCircle 1` — which is the reason
`τ̄_*λ = Leb` constrains `λ̂(h)` for `h ∈ ℤ` and nothing else. -/
@[category research solved, AMS 11 42, ref "Bug12", group "bugeaud_10_61"]
theorem no_half_character :
    ¬ ∃ g : AddCircle (1 : ℝ) → ℂ,
        ∀ x : ℝ, g ((x : ℝ) : AddCircle (1 : ℝ))
          = Complex.exp ((Real.pi : ℂ) * Complex.I * (x : ℂ)) := by
  rintro ⟨g, hg⟩
  have hpt : ((1 : ℝ) : AddCircle (1 : ℝ)) = ((0 : ℝ) : AddCircle (1 : ℝ)) := by
    rw [AddCircle.coe_period, QuotientAddGroup.mk_zero]
  have h0 := hg 0
  have h1 := hg 1
  rw [hpt, h0] at h1
  rw [show ((Real.pi : ℂ) * Complex.I * ((0 : ℝ) : ℂ)) = 0 by push_cast; ring,
    Complex.exp_zero, show ((Real.pi : ℂ) * Complex.I * ((1 : ℝ) : ℂ))
      = (Real.pi : ℂ) * Complex.I by push_cast; ring, Complex.exp_pi_mul_I] at h1
  norm_num at h1

end QuadSetup

/-! ## The two named cases -/

/-- At `α = 1 + √2` the trace is `2`, so `γ = 1/2` is legal and the half-ladder is
`1,1,3,7,17,41,…` — M1's F8 ladder, the one whose plateau beats the trace ladder's by `452`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem silver_halfLad_values :
    silver.halfLad 1 0 = 1 ∧ silver.halfLad 1 1 = 1 ∧ silver.halfLad 1 2 = 3
      ∧ silver.halfLad 1 3 = 7 ∧ silver.halfLad 1 4 = 17 ∧ silver.halfLad 1 5 = 41 := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **The `452` is unusable.**  At `1 + √2` the half-ladder is not the ladder of any frequency
in `α^ℤ·(ℤ∖{0})`, so no proof by contradiction may run along it. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem silver_not_intOrbitLadder : ¬ silver.IntOrbitLadder (silver.halfLad 1) :=
  silver.not_intOrbitLadder_halfLad (c := 1) rfl

/-- At `α = 2 + √3` the trace is `4`, so `γ = 1/2` is legal there too and the half-ladder is
`1,2,7,26,97,…`; M1's F8 found it *worse* than the trace ladder by `3.6`.  Either way it is
inadmissible. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem twoAddSqrt3_halfLad_values :
    twoAddSqrt3.halfLad 2 0 = 1 ∧ twoAddSqrt3.halfLad 2 1 = 2
      ∧ twoAddSqrt3.halfLad 2 2 = 7 ∧ twoAddSqrt3.halfLad 2 3 = 26
      ∧ twoAddSqrt3.halfLad 2 4 = 97 := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩ <;> decide

@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem twoAddSqrt3_not_intOrbitLadder : ¬ twoAddSqrt3.IntOrbitLadder (twoAddSqrt3.halfLad 2) :=
  twoAddSqrt3.not_intOrbitLadder_halfLad (c := 2) rfl

end BB61
