/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.RouteANormalForm
import BB61.Hausdorff
import BB61.Bernoulli
import BB61.FullSupport
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# M2 Proposition 8: block recoding is exactly neutral

Gate G-R of `plans/plan-1061.html` opened a degree of freedom: on the quadratic-unit class,
Problem 10.61 may be proved along a *single* arithmetic progression `n ≡ 0 (mod p)` — that
is, in base `α^p` ([BM86] Th. XIII licenses the reduction).  Proposition 8 of
`note-1061-M2.html` §6 says the freedom is worthless to Route A, and to every criterion of
its kind, and says so by an identity: the order-`p` **block recoding** of the system —
alphabet `{0,1}^p` of size `2^p`, base `α^p`, contraction `ρ^p` — leaves

`log 2^p / log α^p + log 2^p / log (1/ρ^p) = A(α)`

unchanged, and likewise `dim C(α) = log 2 / log α`, the entropy deficit `log 2 < log α` and
Mendès-France's `ρ < 1/2`.  The note's proof is one sentence, *every `p` cancels*.  This
file makes that sentence a theorem, and then makes it sharp.

## What is actually formalised

**The action, not the formula.**  A criterion of this kind sees three numbers,

`(log #alphabet, log base, log 1/contraction)`   (`RatioData`),

and block recoding multiplies all three by `p` (`RatioData.block`, an instance of
`RatioData.scale`).  Every quantity the note lists is a function of the two **ratios**

`L = log base / log #alphabet`,  `R = log (1/contraction) / log #alphabet`

(`RatioData.L`, `RatioData.R`; `A = 1/L + 1/R` is `RatioData.expo_eq_inv_add_inv` and
`dim = 1/L` is `RatioData.dim_eq_inv_L`), and the ratios are invariant under the action
(`RatioData.ratios_scale`).  So the no-go is not four separate cancellations but one:
`RatioData.apply_ratios_block` — *for every* `F`, `F` of the recoded ratios equals `F` of
the original ratios.  Route A, the entropy deficit, Mendès-France and the dimension are
then corollaries, not cases.

**The converse, which is what makes it a no-go.**  `RatioData.ratios_eq_iff` proves that
two ratio data have the same `(L, R)` *exactly when* one is a rescaling of the other: the
fibres of `ratios` are precisely the recoding orbits.  So factoring through the ratios is
not merely a sufficient condition for neutrality — by `RatioData.eq_of_ratios_eq` it is
what neutrality means.  A criterion can spend the progression freedom only by failing to be
a function of `(L, R)`, i.e. by seeing digit *positions*, exactly as the note says.

**The recoded contraction is earned, not assumed.**  This is the note's check P8: the
recoding's base and contraction must be `α^p` and `ρ^p` *of the actual power polynomial*.
`QuadSetup.power` builds that polynomial — `X² - t_p X + (-b)^p` with `t_p = α^p + β^p` the
integer trace ladder (`QuadSetup.traceSeq`, an instance of `BB61/Ladder.lean`'s `lad`) — and
`QuadSetup.power_beta` proves that its second root is `β^p`, so that `ρ^p` really is the
contraction one reads off it.  `QuadSetup.blockData` is then defined from *that* polynomial's
roots, and `QuadSetup.blockData_eq_block` is the theorem that it lands on `p •` the original
data.  Proposition 8's display is `QuadSetup.blockRecoding_expo`.

**Grounding.**  `QuadSetup.dimH_cantorSet_blockData` and
`QuadSetup.upperBoxDim_cantorSet_blockData` check that the recoded description computes the
dimension of the *same, unchanged* set `C(α)` — the recoding is a change of description, not
of object.

**The trap.**  Raising the base to the `p`-th power *without* enlarging the alphabet is a
different operation, and a seductive one: `QuadSetup.routeAExponent_power` shows it divides
`A` by `p`, so by `QuadSetup.exists_power_routeAExponent_lt_one` it eventually drives the
criterion below `1` at *every* `α` — including `α = 1 + √2`, where Route A provably does not
fire (`silver_not_routeAExponent_lt_one` against
`exists_silver_power_routeAExponent_lt_one`).  It proves nothing about 10.61 because the
binary system at base `α^p` is a *thinner* Cantor set, not a recoding of `C(α)`.  The pair
of theorems is the falsification test for any future attempt to spend the G-R freedom: an
argument that survives block recoding unchanged has not spent it, and an argument that
gains from `α ↦ α^p` has changed the set.

## References

* [Bug12] Y. Bugeaud, *Distribution modulo one and Diophantine approximation*,
  Cambridge Tracts in Math. 193, CUP 2012.  Problem 10.61.
* [BM86] A. Bertrand-Mathis, *Développement en base θ…*, Bull. SMF 114 (1986), Th. XIII —
  the progression licence.  It is what makes the freedom *available*; nothing here consumes
  it, because the statement proved is that the freedom is *neutral*.
* `note-1061-M2.html` §6 Proposition 8 and its check P8; `plans/plan-1061.html` §1 anchor
  (xvii)(b).  Numerics `BB61/m2_prop8_lean.py`.
-/

noncomputable section

namespace BB61

open Filter Topology Metric MeasureTheory

open scoped ENNReal

/-! ## The ratio data

The three logarithms a "ratio criterion" is allowed to look at, and the action under which
block recoding moves them.
-/

/-- **The data a ratio criterion sees**: the logarithms of the alphabet size, of the base,
and of the reciprocal contraction.  For Problem 10.61 as posed these are
`(log 2, log α, log (1/ρ))`; after an order-`p` block recoding they are
`(log 2^p, log α^p, log (1/ρ^p))`. -/
@[ext]
structure RatioData where
  /-- `log #alphabet` -/
  logAlphabet : ℝ
  /-- `log base` -/
  logBase : ℝ
  /-- `log (1 / contraction)` -/
  logInvContraction : ℝ

namespace RatioData

variable (D : RatioData) {c : ℝ}

/-- **Rescaling all three logarithms by `c`.**  Block recoding is exactly this action, at
`c = p`; nothing else about it enters any proof below. -/
def scale (c : ℝ) (D : RatioData) : RatioData :=
  ⟨c * D.logAlphabet, c * D.logBase, c * D.logInvContraction⟩

/-- **The order-`p` block recoding**: alphabet `2^p`, base `α^p`, contraction `ρ^p`, i.e.
every logarithm multiplied by `p`. -/
def block (p : ℕ) (D : RatioData) : RatioData := scale (p : ℝ) D

/-- `L`: the base measured in letters, `log base / log #alphabet`.  For 10.61 this is
`log₂ α`. -/
def L (D : RatioData) : ℝ := D.logBase / D.logAlphabet

/-- `R`: the reciprocal contraction measured in letters.  For 10.61 this is `log₂ (1/ρ)`. -/
def R (D : RatioData) : ℝ := D.logInvContraction / D.logAlphabet

/-- **The ratio data proper**, the pair `(L, R)`.  Everything a criterion of this kind can
depend on. -/
def ratios (D : RatioData) : ℝ × ℝ := (D.L, D.R)

/-- The Route A exponent `A = log#/log base + log#/log(1/contraction)`. -/
def expo (D : RatioData) : ℝ :=
  D.logAlphabet / D.logBase + D.logAlphabet / D.logInvContraction

/-- The similarity dimension `log #alphabet / log base`. -/
def dim (D : RatioData) : ℝ := D.logAlphabet / D.logBase

/-- **The entropy deficit** `log #alphabet < log base` — the note's `log 2 < log α`. -/
def EntropyDeficit (D : RatioData) : Prop := D.logAlphabet < D.logBase

/-- **Mendès-France's criterion** `contraction < 1/#alphabet`, i.e.
`log #alphabet < log (1/contraction)` — the note's `ρ < 1/2`. -/
def MFCriterion (D : RatioData) : Prop := D.logAlphabet < D.logInvContraction

/-- **Route A's criterion** `A < 1`. -/
def RouteACriterion (D : RatioData) : Prop := D.expo < 1

/-! ### `A` and the dimension are functions of the ratios -/

/-- `A = 1/L + 1/R`.  No hypothesis: `(a/b)⁻¹ = b/a` holds with Lean's junk convention. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem expo_eq_inv_add_inv : D.expo = D.L⁻¹ + D.R⁻¹ := by
  rw [expo, L, R, inv_div, inv_div]

/-- `dim = 1/L`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem dim_eq_inv_L : D.dim = D.L⁻¹ := by rw [dim, L, inv_div]

/-! ### The action -/

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem scale_one : scale 1 D = D := by
  ext <;> simp [scale]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem scale_scale (c d : ℝ) : scale c (scale d D) = scale (c * d) D := by
  ext <;> simp [scale, mul_assoc]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem block_one : block 1 D = D := by
  rw [block, Nat.cast_one, scale_one]

/-- `L` is invariant: this is the whole of "every `p` cancels", once. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem L_scale (hc : c ≠ 0) : (scale c D).L = D.L := by
  simp only [L, scale]
  exact mul_div_mul_left _ _ hc

/-- `R` is invariant. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem R_scale (hc : c ≠ 0) : (scale c D).R = D.R := by
  simp only [R, scale]
  exact mul_div_mul_left _ _ hc

/-- **The ratio pair is invariant under rescaling.** -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem ratios_scale (hc : c ≠ 0) : (scale c D).ratios = D.ratios := by
  simp only [ratios, L_scale D hc, R_scale D hc]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem expo_scale (hc : c ≠ 0) : (scale c D).expo = D.expo := by
  simp only [expo, scale]
  rw [mul_div_mul_left _ _ hc, mul_div_mul_left _ _ hc]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem dim_scale (hc : c ≠ 0) : (scale c D).dim = D.dim := by
  simp only [dim, scale]
  exact mul_div_mul_left _ _ hc

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem entropyDeficit_scale (hc : 0 < c) :
    (scale c D).EntropyDeficit ↔ D.EntropyDeficit := by
  simp only [EntropyDeficit, scale]
  constructor <;> intro h <;> nlinarith

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem mfCriterion_scale (hc : 0 < c) :
    (scale c D).MFCriterion ↔ D.MFCriterion := by
  simp only [MFCriterion, scale]
  constructor <;> intro h <;> nlinarith

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem routeACriterion_scale (hc : c ≠ 0) :
    (scale c D).RouteACriterion ↔ D.RouteACriterion := by
  simp only [RouteACriterion, expo_scale D hc]

/-! ### The same statements for the block recoding -/

variable {p : ℕ}

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cast_ne_zero (hp : 0 < p) : ((p : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem L_block (hp : 0 < p) : (D.block p).L = D.L := L_scale D (cast_ne_zero hp)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem R_block (hp : 0 < p) : (D.block p).R = D.R := R_scale D (cast_ne_zero hp)

/-- **Proposition 8, abstract form.**  Block recoding leaves the ratio pair unchanged. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem ratios_block (hp : 0 < p) : (D.block p).ratios = D.ratios :=
  ratios_scale D (cast_ne_zero hp)

@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem expo_block (hp : 0 < p) : (D.block p).expo = D.expo := expo_scale D (cast_ne_zero hp)

@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem dim_block (hp : 0 < p) : (D.block p).dim = D.dim := dim_scale D (cast_ne_zero hp)

@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem entropyDeficit_block (hp : 0 < p) :
    (D.block p).EntropyDeficit ↔ D.EntropyDeficit :=
  entropyDeficit_scale D (by exact_mod_cast hp)

@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem mfCriterion_block (hp : 0 < p) : (D.block p).MFCriterion ↔ D.MFCriterion :=
  mfCriterion_scale D (by exact_mod_cast hp)

@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem routeACriterion_block (hp : 0 < p) :
    (D.block p).RouteACriterion ↔ D.RouteACriterion :=
  routeACriterion_scale D (cast_ne_zero hp)

/-- **Proposition 8, the general no-go.**  Not four cancellations but one: *every* `F` of
the ratio pair — Route A, the entropy deficit, Mendès-France, the dimension, and anything
else anyone might write down — takes the same value before and after an order-`p` block
recoding.  There is nothing here for a ratio criterion to spend. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem apply_ratios_block {X : Sort*} (F : ℝ × ℝ → X) (hp : 0 < p) :
    F (D.block p).ratios = F D.ratios := by rw [ratios_block D hp]

/-! ### The converse: the ratios are a complete invariant of the recoding orbit -/

/-- **The fibres of `ratios` are exactly the rescaling orbits.**  Two ratio data have the
same `(L, R)` precisely when one is a rescaling of the other — the real interpolation of the
integer block recodings.  So "is a function of the ratio data" is not a convenient
sufficient condition for neutrality: it is what neutrality *is*. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem ratios_eq_iff (D D' : RatioData) (h : D.logAlphabet ≠ 0) (h' : D'.logAlphabet ≠ 0) :
    D.ratios = D'.ratios ↔ ∃ c, c ≠ 0 ∧ D' = scale c D := by
  constructor
  · intro hr
    have hL : D.logBase / D.logAlphabet = D'.logBase / D'.logAlphabet := by
      have := congrArg Prod.fst hr; simpa [ratios, L] using this
    have hR : D.logInvContraction / D.logAlphabet
        = D'.logInvContraction / D'.logAlphabet := by
      have := congrArg Prod.snd hr; simpa [ratios, R] using this
    refine ⟨D'.logAlphabet / D.logAlphabet, div_ne_zero h' h, ?_⟩
    ext
    · show D'.logAlphabet = D'.logAlphabet / D.logAlphabet * D.logAlphabet
      field_simp
    · show D'.logBase = D'.logAlphabet / D.logAlphabet * D.logBase
      field_simp at hL ⊢
      linarith [hL]
    · show D'.logInvContraction = D'.logAlphabet / D.logAlphabet * D.logInvContraction
      field_simp at hR ⊢
      linarith [hR]
  · rintro ⟨c, hc, rfl⟩
    exact (ratios_scale D hc).symm

/-- **Every rescaling-invariant quantity factors through the ratios.**  The converse
direction of the no-go, in the form it is used: if `F` cannot tell a system from its
recodings, then `F` cannot tell apart two systems with the same `(L, R)`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem eq_of_ratios_eq {X : Sort*} (F : RatioData → X)
    (hF : ∀ c : ℝ, c ≠ 0 → ∀ E : RatioData, F (scale c E) = F E)
    {D D' : RatioData} (h : D.logAlphabet ≠ 0) (h' : D'.logAlphabet ≠ 0)
    (hr : D.ratios = D'.ratios) : F D = F D' := by
  obtain ⟨c, hc, hEq⟩ := (ratios_eq_iff D D' h h').mp hr
  rw [hEq, hF c hc D]

end RatioData

/-! ## The ratio data of a `QuadSetup` -/

namespace QuadSetup

variable (P : QuadSetup)

/-- **The system as Problem 10.61 poses it**: alphabet `{0,1}`, base `α`, contraction
`ρ = |β|`. -/
def sysData : RatioData := ⟨Real.log 2, Real.log P.α, Real.log |P.β|⁻¹⟩

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem sysData_L : P.sysData.L = P.logAlpha := by
  simp [RatioData.L, sysData, logAlpha, Real.logb]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem sysData_R : P.sysData.R = P.logRhoInv := by
  simp [RatioData.R, sysData, logRhoInv, Real.logb]

/-- The abstract exponent of `sysData` is Route A's `A(α)`, on the nose. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem expo_sysData : P.sysData.expo = P.routeAExponent := rfl

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem dim_sysData : P.sysData.dim = Real.log 2 / Real.log P.α := rfl

/-- The entropy deficit of the note is `α > 2`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem entropyDeficit_sysData_iff : P.sysData.EntropyDeficit ↔ 2 < P.α := by
  simp only [RatioData.EntropyDeficit, sysData]
  exact Real.log_lt_log_iff (by norm_num) P.alpha_pos

/-- Mendès-France's criterion of the note is `ρ < 1/2`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem mfCriterion_sysData_iff (hβ : P.β ≠ 0) :
    P.sysData.MFCriterion ↔ |P.β| < 2⁻¹ := by
  have hb0 : (0 : ℝ) < |P.β| := abs_pos.mpr hβ
  simp only [RatioData.MFCriterion, sysData]
  rw [Real.log_lt_log_iff (by norm_num) (by positivity)]
  exact lt_inv_comm₀ (by norm_num) hb0

/-! ## The power polynomial

The recoded base and contraction have to be `α^p` and `ρ^p` *of the actual power
polynomial*; that polynomial is built here, and its second root is proved to be `β^p`.
-/

/-- **The trace ladder** `t_n = α^n + β^n`, an *integer* sequence: the `BB61/Ladder.lean`
recurrence `h_{k+2} = a h_{k+1} + b h_k` started at `(2, a)`. -/
def traceSeq (P : QuadSetup) : ℕ → ℤ := P.lad 2 P.a

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem traceSeq_zero : P.traceSeq 0 = 2 := rfl

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem traceSeq_one : P.traceSeq 1 = P.a := rfl

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem traceSeq_add_two (n : ℕ) :
    P.traceSeq (n + 2) = P.a * P.traceSeq (n + 1) + P.b * P.traceSeq n :=
  P.lad_add_two 2 P.a n

/-- **`t_n = α^n + β^n`.**  Both roots satisfy the same monic recurrence, so their sum is
the integer ladder from `(2, a)`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem traceSeq_cast (n : ℕ) : ((P.traceSeq n : ℤ) : ℝ) = P.α ^ n + P.β ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => rw [traceSeq_zero]; push_cast; ring
  | one =>
      rw [traceSeq_one, ← P.alpha_add_beta]
      ring
  | more n ih1 ih2 =>
      rw [traceSeq_add_two]
      push_cast
      rw [ih1, ih2]
      linear_combination (-(P.α ^ n)) * P.root + (-(P.β ^ n)) * P.beta_root

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem traceSeq_two : P.traceSeq 2 = P.a ^ 2 + 2 * P.b := by
  have h : P.traceSeq 2 = P.a * P.traceSeq 1 + P.b * P.traceSeq 0 := P.traceSeq_add_two 0
  rw [traceSeq_zero, traceSeq_one] at h
  rw [h]; ring

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem traceSeq_three : P.traceSeq 3 = P.a ^ 3 + 3 * P.a * P.b := by
  have h : P.traceSeq 3 = P.a * P.traceSeq 2 + P.b * P.traceSeq 1 := P.traceSeq_add_two 1
  rw [traceSeq_one, P.traceSeq_two] at h
  rw [h]; ring

/-- **The power system.**  `α^p` is again a quadratic integer: the root of
`X² - t_p X + (-b)^p`, `t_p = α^p + β^p`.  This is the "actual power polynomial" of the
note's check P8 — the recoding's base and contraction are read off *it*. -/
def power (P : QuadSetup) (p : ℕ) (hp : 0 < p) : QuadSetup where
  a := P.traceSeq p
  b := -(-P.b) ^ p
  α := P.α ^ p
  root := by
    have ht := P.traceSeq_cast p
    have hab := P.alpha_mul_beta
    show (P.α ^ p) ^ 2 = ((P.traceSeq p : ℤ) : ℝ) * P.α ^ p + ((-(-P.b) ^ p : ℤ) : ℝ)
    rw [ht]
    push_cast
    rw [← hab, mul_pow]
    ring
  one_lt := one_lt_pow₀ P.one_lt hp.ne'
  conj_lt := by
    have ht := P.traceSeq_cast p
    show |((P.traceSeq p : ℤ) : ℝ) - P.α ^ p| < 1
    rw [ht, add_sub_cancel_left, abs_pow]
    exact pow_lt_one₀ (abs_nonneg _) P.abs_beta_lt_one hp.ne'

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem power_a (p : ℕ) (hp : 0 < p) : (P.power p hp).a = P.traceSeq p := rfl

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem power_b (p : ℕ) (hp : 0 < p) : (P.power p hp).b = -(-P.b) ^ p := rfl

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem power_alpha (p : ℕ) (hp : 0 < p) : (P.power p hp).α = P.α ^ p := rfl

/-- **The second root of the power polynomial is `β^p`.**  This is what earns the recoded
contraction `ρ^p`: it is not a definition but a fact about `X² - t_p X + (-b)^p`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem power_beta (p : ℕ) (hp : 0 < p) : (P.power p hp).β = P.β ^ p := by
  show ((P.traceSeq p : ℤ) : ℝ) - P.α ^ p = P.β ^ p
  rw [P.traceSeq_cast p, add_sub_cancel_left]

/-! ## Proposition 8 -/

/-- **The order-`p` block recoding of the concrete system**: alphabet `{0,1}^p` of size
`2^p`, base and contraction read off the power polynomial's own roots. -/
def blockData (P : QuadSetup) (p : ℕ) (hp : 0 < p) : RatioData :=
  ⟨Real.log ((2 : ℝ) ^ p), Real.log (P.power p hp).α, Real.log |(P.power p hp).β|⁻¹⟩

/-- **Check P8, as a theorem.**  Reading base and contraction off the power polynomial
lands exactly on `p •` the original data.  Everything else in Proposition 8 is this plus
`RatioData.ratios_scale`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem blockData_eq_block (p : ℕ) (hp : 0 < p) :
    P.blockData p hp = P.sysData.block p := by
  have h1 : Real.log ((2 : ℝ) ^ p) = (p : ℝ) * Real.log 2 := Real.log_pow 2 p
  have h2 : Real.log (P.power p hp).α = (p : ℝ) * Real.log P.α := by
    rw [power_alpha]; exact Real.log_pow _ _
  have h3 : Real.log |(P.power p hp).β|⁻¹ = (p : ℝ) * Real.log |P.β|⁻¹ := by
    rw [P.power_beta p hp, abs_pow, ← inv_pow]; exact Real.log_pow _ _
  simp only [blockData, sysData, RatioData.block, RatioData.scale, h1, h2, h3]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem L_blockData (p : ℕ) (hp : 0 < p) : (P.blockData p hp).L = P.logAlpha := by
  rw [P.blockData_eq_block p hp, RatioData.L_block _ hp, P.sysData_L]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem R_blockData (p : ℕ) (hp : 0 < p) : (P.blockData p hp).R = P.logRhoInv := by
  rw [P.blockData_eq_block p hp, RatioData.R_block _ hp, P.sysData_R]

@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem ratios_blockData (p : ℕ) (hp : 0 < p) :
    (P.blockData p hp).ratios = P.sysData.ratios := by
  rw [P.blockData_eq_block p hp, RatioData.ratios_block _ hp]

/-- **Proposition 8, the display.**
`log 2^p / log α^p + log 2^p / log(1/ρ^p) = A(α)`, with the left-hand side computed from the
power polynomial's own roots. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem blockRecoding_expo (p : ℕ) (hp : 0 < p) :
    Real.log ((2 : ℝ) ^ p) / Real.log (P.power p hp).α
        + Real.log ((2 : ℝ) ^ p) / Real.log |(P.power p hp).β|⁻¹
      = P.routeAExponent := by
  have h : (P.blockData p hp).expo = P.sysData.expo := by
    rw [P.blockData_eq_block p hp, RatioData.expo_block _ hp]
  exact h

@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem expo_blockData (p : ℕ) (hp : 0 < p) :
    (P.blockData p hp).expo = P.routeAExponent := P.blockRecoding_expo p hp

/-- **The dimension is invariant.** -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem dim_blockData (p : ℕ) (hp : 0 < p) :
    (P.blockData p hp).dim = Real.log 2 / Real.log P.α := by
  rw [P.blockData_eq_block p hp, RatioData.dim_block _ hp]; rfl

/-- **The entropy deficit is invariant.** -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem entropyDeficit_blockData_iff (p : ℕ) (hp : 0 < p) :
    (P.blockData p hp).EntropyDeficit ↔ 2 < P.α := by
  rw [P.blockData_eq_block p hp, RatioData.entropyDeficit_block _ hp,
    P.entropyDeficit_sysData_iff]

/-- **Mendès-France's criterion is invariant.** -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem mfCriterion_blockData_iff (p : ℕ) (hp : 0 < p) (hβ : P.β ≠ 0) :
    (P.blockData p hp).MFCriterion ↔ |P.β| < 2⁻¹ := by
  rw [P.blockData_eq_block p hp, RatioData.mfCriterion_block _ hp,
    P.mfCriterion_sysData_iff hβ]

/-- **Route A's coverage is invariant.**  The recoded criterion fires at exactly the `α`
the original does — the G-R progression freedom buys Route A not one new `α`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem routeACriterion_blockData_iff (p : ℕ) (hp : 0 < p) :
    (P.blockData p hp).RouteACriterion ↔ P.routeAExponent < 1 := by
  rw [RatioData.RouteACriterion, P.expo_blockData p hp]

/-- **The coverage on quadratic units, after recoding at any order: still exactly
`(4, ∞)`.**  M2 Corollary 6 (`routeAExponent_lt_one_iff_four_lt`) transported through
Proposition 8. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem routeACriterion_blockData_iff_four_lt (p : ℕ) (hp : 0 < p) (hb : |P.b| = 1) :
    (P.blockData p hp).RouteACriterion ↔ 4 < P.α := by
  rw [P.routeACriterion_blockData_iff p hp, P.routeAExponent_lt_one_iff_four_lt hb]

/-- **Proposition 8's no-go at the concrete system.**  Every function of the ratio pair
takes the same value on the recoded system as on the original. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem apply_ratios_blockData {X : Sort*} (F : ℝ × ℝ → X) (p : ℕ) (hp : 0 < p) :
    F (P.blockData p hp).ratios = F P.sysData.ratios := by
  rw [P.ratios_blockData p hp]

/-! ## Grounding: the recoded description describes the same set -/

/-- The recoded data computes the box dimension of `C(α)` — the *same* set, unrecoded. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem upperBoxDim_cantorSet_blockData (p : ℕ) (hp : 0 < p) (h2 : 2 < P.α) :
    upperBoxDim (cantorSet P.α) = (((P.blockData p hp).dim : ℝ) : EReal) := by
  rw [P.dim_blockData p hp]
  exact upperBoxDim_cantorSet h2

/-- The same for the Hausdorff dimension, which is the form `plans/plan-1061.html` §1
anchor (xvii)(b) states. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem dimH_cantorSet_blockData (p : ℕ) (hp : 0 < p) (h2 : 2 < P.α) :
    dimH (cantorSet P.α) = ENNReal.ofReal ((P.blockData p hp).dim) := by
  rw [P.dim_blockData p hp]
  exact dimH_cantorSet h2

/-! ## The trap: powering the base is not recoding the alphabet -/

/-- **`A(α^p) = A(α)/p`.**  Raising the base without enlarging the alphabet divides the
exponent by `p` — it is a different operation from block recoding, and the difference is the
whole of Proposition 8. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem routeAExponent_power (p : ℕ) (hp : 0 < p) (hβ : P.β ≠ 0) :
    (P.power p hp).routeAExponent = P.routeAExponent / p := by
  have hla : 0 < Real.log P.α := Real.log_pos P.one_lt
  have hb0 : (0 : ℝ) < |P.β| := abs_pos.mpr hβ
  have hlb : 0 < Real.log |P.β|⁻¹ := by
    rw [Real.log_inv]
    exact neg_pos.mpr (Real.log_neg hb0 P.abs_beta_lt_one)
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have h1 : Real.log (P.power p hp).α = (p : ℝ) * Real.log P.α := by
    rw [power_alpha]; exact Real.log_pow _ _
  have h2 : Real.log |(P.power p hp).β|⁻¹ = (p : ℝ) * Real.log |P.β|⁻¹ := by
    rw [P.power_beta p hp, abs_pow, ← inv_pow]; exact Real.log_pow _ _
  simp only [routeAExponent, h1, h2]
  field_simp

/-- **The trap, sprung.**  Because `A(α^p) = A(α)/p`, the binary criterion at base `α^p`
eventually fires at *every* `α` — so it cannot be a proof of 10.61 at every `α`.  What it
proves is 10.61 on the base-`α^p` binary Cantor set, a proper sliver of `C(α)` (the words
constant on blocks of length `p`), which is not what 10.61 asks. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_power_routeAExponent_lt_one (hβ : P.β ≠ 0) :
    ∃ (p : ℕ) (hp : 0 < p), (P.power p hp).routeAExponent < 1 := by
  obtain ⟨p, hpgt⟩ := exists_nat_gt (max 1 P.routeAExponent)
  have hp1 : (1 : ℝ) < (p : ℝ) := lt_of_le_of_lt (le_max_left _ _) hpgt
  have hp0 : 0 < p := by exact_mod_cast lt_trans zero_lt_one hp1
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  refine ⟨p, hp0, ?_⟩
  rw [P.routeAExponent_power p hp0 hβ, div_lt_one hpR]
  exact lt_of_le_of_lt (le_max_right _ _) hpgt

end QuadSetup

/-! ## Check P8 at the note's three instances -/

section Instances

/-- `(2+√3)² = 7+4√3` is the root of `X² - 14X + 1`: the note's first P8 instance. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem twoAddSqrt3_power_two_a (hp : 0 < 2) : (twoAddSqrt3.power 2 hp).a = 14 := by
  show twoAddSqrt3.traceSeq 2 = 14
  rw [QuadSetup.traceSeq_two]
  norm_num [twoAddSqrt3]

@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem twoAddSqrt3_power_two_b (hp : 0 < 2) : (twoAddSqrt3.power 2 hp).b = -1 := by
  show -(-twoAddSqrt3.b) ^ 2 = -1
  norm_num [twoAddSqrt3]

@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem twoAddSqrt3_power_two_alpha (hp : 0 < 2) :
    (twoAddSqrt3.power 2 hp).α = 7 + 4 * Real.sqrt 3 := by
  have h : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  show (2 + Real.sqrt 3) ^ 2 = 7 + 4 * Real.sqrt 3
  nlinarith [h]

/-- `(1+√2)² = 3+2√2` is the root of `X² - 6X + 1`: the note's second P8 instance. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem silver_power_two_a (hp : 0 < 2) : (silver.power 2 hp).a = 6 := by
  show silver.traceSeq 2 = 6
  rw [QuadSetup.traceSeq_two]
  norm_num [silver]

@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem silver_power_two_b (hp : 0 < 2) : (silver.power 2 hp).b = -1 := by
  show -(-silver.b) ^ 2 = -1
  norm_num [silver]

@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem silver_power_two_alpha (hp : 0 < 2) :
    (silver.power 2 hp).α = 3 + 2 * Real.sqrt 2 := by
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  show (1 + Real.sqrt 2) ^ 2 = 3 + 2 * Real.sqrt 2
  nlinarith [h]

/-- `(1+√2)³ = 7+5√2` is the root of `X² - 14X - 1`: the note's third P8 instance, and the
one that shows the constant coefficient is not simply inherited. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem silver_power_three_a (hp : 0 < 3) : (silver.power 3 hp).a = 14 := by
  show silver.traceSeq 3 = 14
  rw [QuadSetup.traceSeq_three]
  norm_num [silver]

@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem silver_power_three_b (hp : 0 < 3) : (silver.power 3 hp).b = 1 := by
  show -(-silver.b) ^ 3 = 1
  norm_num [silver]

@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem silver_power_three_alpha (hp : 0 < 3) :
    (silver.power 3 hp).α = 7 + 5 * Real.sqrt 2 := by
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  show (1 + Real.sqrt 2) ^ 3 = 7 + 5 * Real.sqrt 2
  nlinarith [h, Real.sqrt_nonneg 2]

/-! ### The trap at the named open case -/

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem sqrt_two_lt_two : Real.sqrt 2 < 2 := by
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg 2]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem silver_abs_b : |silver.b| = 1 := by norm_num [silver]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem silver_beta_ne_zero : silver.β ≠ 0 := by
  rw [silver_beta]
  have := silver_rho_pos
  intro h
  linarith [neg_eq_zero.mp h]

/-- **Route A does not fire at `1 + √2`** — M2 Corollary 6, since `1 + √2 < 4`.  This is
Problem 10.61's named open case. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem silver_not_routeAExponent_lt_one : ¬ silver.routeAExponent < 1 := by
  rw [silver.routeAExponent_lt_one_iff_four_lt silver_abs_b, silver_alpha]
  push Not
  have := sqrt_two_lt_two
  linarith

/-- …and yet the binary criterion at base `(1+√2)^p` does fire, for suitable `p`.  Read
together with `silver_not_routeAExponent_lt_one` this is the falsification test: an
argument that gains from `α ↦ α^p` has silently changed the Cantor set, whereas the honest
block recoding gains nothing (`QuadSetup.routeACriterion_blockData_iff_four_lt`). -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem exists_silver_power_routeAExponent_lt_one :
    ∃ (p : ℕ) (hp : 0 < p), (silver.power p hp).routeAExponent < 1 :=
  silver.exists_power_routeAExponent_lt_one silver_beta_ne_zero

/-- **The block recoding of `1 + √2` at every order is still blind.**  Proposition 8 at the
one `α` the whole programme is about. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem silver_not_routeACriterion_blockData (p : ℕ) (hp : 0 < p) :
    ¬ (silver.blockData p hp).RouteACriterion := by
  rw [silver.routeACriterion_blockData_iff p hp]
  exact silver_not_routeAExponent_lt_one

end Instances

end BB61

end
