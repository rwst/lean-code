/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.Plateau
import BB61.Bernoulli
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# M1 Observation 16(i): the two one-sided Erdős products, and their common limit

Formal companion of `note-1061-M1.html` §6, Observation 16 **(i)**.  Part (ii) — the
mechanism, and why it is confined to quadratic units — is `BB61/Plateau.lean`; this file
supplies what (ii) left open, namely the infinite products themselves.

> **Observation 16(i).**  Along a ladder the future factor and the past factor of the
> Bernoulli(½) Weyl limit converge to the *same* value `L`, so the plateau is `L²`.

Writing `‖·‖` for `|cos(π ·)|` (`ncos`, the modulus of the Bernoulli(½) characteristic
function), the two one-sided factors of the Erdős product `G_{1/2}(h)` of M5 are

* `futProd h = ∏_{j≥1} ncos (h(α-1)/αʲ)` — the future factor,
* `pastProd h = ∏_{m≥0} ncos (h c_m)`, `c_m = (β-1)βᵐ` — the past factor,

and `weylProd h = futProd h * pastProd h` is `|G_{1/2}(h)|`.

## What is proved

1. **The products converge.**  `multipliable_futProd`, `multipliable_pastProd`: both are
   `Multipliable` for *every* real mode `h`, because the arguments decay geometrically and
   `|ncos x - 1| ≤ π|x - N|` for every integer `N`.  (Non-vanishing of the individual
   factors is `BB61/Bernoulli.lean`.)
2. **Each factor converges along a ladder, to an explicit limit.**  `tendsto_futProd` and
   `tendsto_pastProd`: with `A = shapeFut` and `B = shapePast` the two profiles of
   `BB61/Plateau.lean`,
   `futProd hₖ → biProd A`  and  `pastProd hₖ → biProd B`,
   where `biProd x = ∏_{n∈ℤ} ncos (x αⁿ)` is the **bi-infinite** Erdős product of amplitude
   `x`.  The future statement is unconditional — it holds at a non-unit too, which is the
   note's "the future factor still settles"; the past statement needs `|b| = 1`, and that
   is exactly where the plateau lives.
3. **The plateau.**  `tendsto_weylProd`: `G_{1/2}(hₖ) → biProd A * biProd B`.
4. **When the two limits agree.**  At norm `+1` (`b = -1`) they agree for a trivial and
   much stronger reason: `pastProd_eq_futProd` says the two products are *equal for every
   mode*, so `weylProd h = (futProd h)²` at every rung (`weylProd_eq_sq`) — this is
   correction (a) of the Plateau file, now at the level of the products themselves.
   At any quadratic unit, `biProd_shapePast_eq` gives `biProd B = biProd A` under
   `e₀ = -f₀`, so `weylProd hₖ → L²` with `L = biProd A` (`tendsto_weylProd_sq`).

## The correction: (i) is **false** for a general ladder

`e₀ = -f₀` says `2h₁ = a h₀`, i.e. the ladder is a rational multiple of the trace ladder
`hₖ = Tr(αᵏ)` — equivalently `λ' = λ` for the codifferent parameter `λ` of M1 Prop. 15
(`BB61/TraceLadder.lean`).  Both of the note's numerical witnesses (`λ = 1` and `λ = ½` at
`α = 1+√2`) satisfy it, and the general statement is not true without it:
`tendsto_futProd`/`tendsto_pastProd` identify the two limits as `biProd (λ(α-1))` and
`biProd (λ'(α-1))` (the second through `biProd_shapePast_eq_shapeFutC`), and these differ in
general.  Witness, at the norm `-1` unit `α = (3+√13)/2` with the ladder
`1, 4, 13, 43, 142, …` (`λ = (1+α)/√13`, so `λ'/λ = -0.16204…` is *not* `±αˢ`):
future factor `0.4004074010`, past factor `0.0126597907` — both settled to 16 digits by
`k = 36`, and not equal.  See `BB61/m1_obs16i.py`.

The sufficient condition is `λ' = ±αˢ λ`; `biProd_mul_alpha` and `biProd_neg` are the two
invariances that make it sufficient, and `e₀ = -f₀` is its `s = 0` case.
-/

noncomputable section

namespace BB61

open Filter Topology

/-! ## `ncos`: the modulus of the Bernoulli(½) characteristic function -/

/-- `ncos x = |cos (π x)| = |φ_{1/2}(x)|`, the modulus of the Bernoulli(½) characteristic
function.  It is even and `1`-periodic, so it depends only on the distance from `x` to
`ℤ`. -/
def ncos (x : ℝ) : ℝ := |Real.cos (Real.pi * x)|

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem ncos_nonneg (x : ℝ) : 0 ≤ ncos x := abs_nonneg _

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem ncos_le_one (x : ℝ) : ncos x ≤ 1 := Real.abs_cos_le_one _

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem ncos_neg (x : ℝ) : ncos (-x) = ncos x := by
  simp [ncos, mul_neg, Real.cos_neg]

/-- `ncos` is `1`-periodic and even, in the single form both facts are used in: reflecting
`x` in any integer leaves it unchanged. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem ncos_intCast_sub (N : ℤ) (x : ℝ) : ncos ((N : ℝ) - x) = ncos x := by
  have hexp : Real.pi * ((N : ℝ) - x) = (N : ℝ) * Real.pi - Real.pi * x := by ring
  rw [ncos, hexp, Real.cos_int_mul_pi_sub, abs_mul, ncos]
  have : |(-1 : ℝ) ^ (N : ℤ)| = 1 := by
    rw [abs_zpow, abs_neg, abs_one, one_zpow]
  rw [this, one_mul]

/-- Two reals whose **sum** is an integer have the same `ncos`.  This is the only way the
trace identities of `BB61/Plateau.lean` enter: a shape and its algebraic conjugate always
sum to an integer. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem ncos_eq_of_add_int {x y : ℝ} {N : ℤ} (h : x + y = (N : ℝ)) : ncos x = ncos y := by
  have hy : y = (N : ℝ) - x := by linarith
  rw [hy, ncos_intCast_sub]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem ncos_intCast (N : ℤ) : ncos (N : ℝ) = 1 := by
  have h := ncos_intCast_sub N 0
  rw [sub_zero] at h
  rw [h, ncos, mul_zero, Real.cos_zero, abs_one]

/-- Multiplying by a sign leaves `ncos` alone. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem ncos_mul_of_abs_eq_one {c : ℝ} (hc : |c| = 1) (x : ℝ) : ncos (c * x) = ncos x := by
  rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hc with h | h
  · rw [h, one_mul]
  · rw [h, neg_one_mul, ncos_neg]

/-- `ncos` is `π`-Lipschitz. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_ncos_sub_ncos_le (x y : ℝ) : |ncos x - ncos y| ≤ Real.pi * |x - y| := by
  have h1 := abs_abs_sub_abs_le_abs_sub (Real.cos (Real.pi * x)) (Real.cos (Real.pi * y))
  have h2 := Real.abs_cos_sub_cos_le (Real.pi * x) (Real.pi * y)
  have h3 : |Real.pi * x - Real.pi * y| = Real.pi * |x - y| := by
    rw [← mul_sub, abs_mul, abs_of_pos Real.pi_pos]
  calc |ncos x - ncos y| ≤ |Real.cos (Real.pi * x) - Real.cos (Real.pi * y)| := h1
    _ ≤ |Real.pi * x - Real.pi * y| := h2
    _ = Real.pi * |x - y| := h3

/-- A factor near an integer is near `1`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_ncos_sub_one_le (x : ℝ) (N : ℤ) : |ncos x - 1| ≤ Real.pi * |x - (N : ℝ)| := by
  calc |ncos x - 1| = |ncos x - ncos (N : ℝ)| := by rw [ncos_intCast]
    _ ≤ Real.pi * |x - (N : ℝ)| := abs_ncos_sub_ncos_le _ _

/-! ## Two generic facts about infinite products of factors in `[0,1]` -/

/-- Multipliability from summability of `f - 1`.  (`Multipliable` allows the value `0`, so
no non-vanishing hypothesis is needed; the factors here are `≤ 1`, so this is the only
criterion the file uses.) -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem multipliable_of_summable_sub_one {f : ℕ → ℝ} (h : Summable fun i => f i - 1) :
    Multipliable f := by
  have h2 := Real.multipliable_one_add_of_summable h
  have hfun : (fun i => 1 + (f i - 1)) = f := by funext i; ring
  rwa [hfun] at h2

/-- Finite products of factors in `[0,1]` differ by at most the sum of the differences. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_prod_sub_prod_le {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∀ i, f i ≤ 1) (hg0 : ∀ i, 0 ≤ g i) (hg1 : ∀ i, g i ≤ 1) :
    |∏ i ∈ s, f i - ∏ i ∈ s, g i| ≤ ∑ i ∈ s, |f i - g i| := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
  set F : ℝ := ∏ i ∈ s, f i with hF
  set G : ℝ := ∏ i ∈ s, g i with hG
  have hFnn : 0 ≤ F := Finset.prod_nonneg fun i _ => hf0 i
  have hF1 : F ≤ 1 := Finset.prod_le_one (fun i _ => hf0 i) fun i _ => hf1 i
  have hGnn : 0 ≤ G := Finset.prod_nonneg fun i _ => hg0 i
  have hG1 : G ≤ 1 := Finset.prod_le_one (fun i _ => hg0 i) fun i _ => hg1 i
  have hkey : f a * F - g a * G = (f a - g a) * F + g a * (F - G) := by ring
  have habsF : |F| ≤ 1 := by rw [abs_of_nonneg hFnn]; exact hF1
  have habsga : |g a| ≤ 1 := by rw [abs_of_nonneg (hg0 a)]; exact hg1 a
  calc |f a * F - g a * G| = |(f a - g a) * F + g a * (F - G)| := by rw [hkey]
    _ ≤ |(f a - g a) * F| + |g a * (F - G)| := abs_add_le _ _
    _ = |f a - g a| * |F| + |g a| * |F - G| := by rw [abs_mul, abs_mul]
    _ ≤ |f a - g a| * 1 + 1 * |F - G| :=
        add_le_add (mul_le_mul_of_nonneg_left habsF (abs_nonneg _))
          (mul_le_mul_of_nonneg_right habsga (abs_nonneg _))
    _ ≤ |f a - g a| + ∑ i ∈ s, |f i - g i| := by
        rw [mul_one, one_mul]; linarith [ih]

/-- The same bound for the infinite products. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_tprod_sub_tprod_le {f g : ℕ → ℝ}
    (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∀ i, f i ≤ 1) (hg0 : ∀ i, 0 ≤ g i) (hg1 : ∀ i, g i ≤ 1)
    (hfm : Multipliable f) (hgm : Multipliable g) (hs : Summable fun i => |f i - g i|) :
    |∏' i, f i - ∏' i, g i| ≤ ∑' i, |f i - g i| := by
  have hF := hfm.hasProd.tendsto_prod_nat
  have hG := hgm.hasProd.tendsto_prod_nat
  have hlim : Tendsto
      (fun n => |∏ i ∈ Finset.range n, f i - ∏ i ∈ Finset.range n, g i|) atTop
      (𝓝 |∏' i, f i - ∏' i, g i|) := (hF.sub hG).abs
  refine le_of_tendsto hlim (Filter.Eventually.of_forall fun n => ?_)
  calc |∏ i ∈ Finset.range n, f i - ∏ i ∈ Finset.range n, g i|
      ≤ ∑ i ∈ Finset.range n, |f i - g i| :=
        abs_prod_sub_prod_le _ f g hf0 hf1 hg0 hg1
    _ ≤ ∑' i, |f i - g i| := hs.sum_le_tsum _ fun i _ => abs_nonneg _

/-- Multipliability of `∏ ncos (u n)` when, from index `K` on, `u` sits within a geometric
distance of an integer.  Only the tail matters, which is what lets the same lemma serve the
products whose first `K` arguments are large. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem multipliable_ncos_of_geom_tail {u : ℕ → ℝ} {C r : ℝ} (K : ℕ) (hr : |r| < 1)
    (h : ∀ n : ℕ, ∃ N : ℤ, |u (n + K) - (N : ℝ)| ≤ C * |r| ^ n) :
    Multipliable fun n => ncos (u n) := by
  refine multipliable_of_summable_sub_one ?_
  rw [← summable_nat_add_iff K]
  choose N hN using h
  have hg : Summable fun n : ℕ => Real.pi * C * |r| ^ n :=
    (summable_geometric_of_lt_one (abs_nonneg r) hr).mul_left _
  refine hg.of_norm_bounded fun n => ?_
  have h1 : |ncos (u (n + K)) - 1| ≤ Real.pi * |u (n + K) - (N n : ℝ)| :=
    abs_ncos_sub_one_le _ _
  have h2 : Real.pi * |u (n + K) - (N n : ℝ)| ≤ Real.pi * (C * |r| ^ n) :=
    mul_le_mul_of_nonneg_left (hN n) Real.pi_pos.le
  calc ‖ncos (u (n + K)) - 1‖ = |ncos (u (n + K)) - 1| := Real.norm_eq_abs _
    _ ≤ Real.pi * (C * |r| ^ n) := h1.trans h2
    _ = Real.pi * C * |r| ^ n := by ring

/-- The `K = 0` case: arguments themselves geometrically small. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem multipliable_ncos_of_geom {u : ℕ → ℝ} {C r : ℝ} (hr : |r| < 1)
    (h : ∀ n : ℕ, |u n| ≤ C * |r| ^ n) : Multipliable fun n => ncos (u n) := by
  refine multipliable_ncos_of_geom_tail (C := C) (r := r) 0 hr fun n => ⟨(0 : ℤ), ?_⟩
  simpa using h n

end BB61

namespace BB61

open Filter Topology

namespace QuadSetup

variable (P : QuadSetup)

/-! ## The two one-sided Erdős products -/

/-- The **future factor** of the Bernoulli(½) Weyl limit at the mode `h`:
`∏_{j≥1} |cos(π h(α-1)α^{-j})|`. -/
def futProd (h : ℝ) : ℝ := ∏' j : ℕ, ncos (h * (P.α - 1) / P.α ^ (j + 1))

/-- The **past factor** at the mode `h`: `∏_{m≥0} |cos(π h c_m)|`, `c_m = (β-1)βᵐ`.
(`φ_p` is evaluated at `-h c_m` in the note; `ncos` is even, so the sign is immaterial.) -/
def pastProd (h : ℝ) : ℝ := ∏' m : ℕ, ncos (h * P.cCoef m)

/-- `|G_{1/2}(h)|`, the modulus of the Erdős product of M5. -/
def weylProd (h : ℝ) : ℝ := P.futProd h * P.pastProd h

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_inv_alpha_lt_one : |1 / P.α| < 1 := by
  have hα := P.alpha_pos
  rw [abs_of_pos (by positivity : (0:ℝ) < 1 / P.α), div_lt_one hα]
  exact P.one_lt

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_inv_alpha_eq : |1 / P.α| = 1 / P.α := by
  have := P.alpha_pos
  exact abs_of_pos (by positivity)

/-- **The future product converges** — for every real mode `h`, unit or not. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem multipliable_futProd (h : ℝ) :
    Multipliable fun j : ℕ => ncos (h * (P.α - 1) / P.α ^ (j + 1)) := by
  have hα : (0:ℝ) < P.α := P.alpha_pos
  refine multipliable_ncos_of_geom (C := |h * (P.α - 1)| / P.α) (r := 1 / P.α)
    P.abs_inv_alpha_lt_one fun n => le_of_eq ?_
  rw [abs_div, abs_pow, abs_of_pos hα, P.abs_inv_alpha_eq, div_pow, one_pow, pow_succ]
  field_simp

/-- **The past product converges** — for every real mode `h`, unit or not. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem multipliable_pastProd (h : ℝ) :
    Multipliable fun m : ℕ => ncos (h * P.cCoef m) := by
  refine multipliable_ncos_of_geom (C := |h| * (1 + |P.β|)) (r := P.β)
    P.abs_beta_lt_one fun m => ?_
  rw [abs_mul]
  calc |h| * |P.cCoef m| ≤ |h| * ((1 + |P.β|) * |P.β| ^ m) :=
        mul_le_mul_of_nonneg_left (P.abs_cCoef_le m) (abs_nonneg _)
    _ = |h| * (1 + |P.β|) * |P.β| ^ m := by ring

/-! ## The shape products, and the bi-infinite Erdős product -/

/-- The **shape product** at amplitude `x` and rung `k`: `∏_{j≥1} ncos (x α^{k-j})`, the
future product with the ladder mode replaced by its limit profile.  As `k` grows this is a
one-sided truncation of the bi-infinite product `biProd x`, taken further and further out. -/
def shapeProd (x : ℝ) (k : ℕ) : ℝ := ∏' j : ℕ, ncos (x * P.α ^ k / P.α ^ (j + 1))

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem multipliable_shapeProd (x : ℝ) (k : ℕ) :
    Multipliable fun j : ℕ => ncos (x * P.α ^ k / P.α ^ (j + 1)) := by
  have hα : (0:ℝ) < P.α := P.alpha_pos
  refine multipliable_ncos_of_geom_tail (C := |x| / P.α) (r := 1 / P.α) k
    P.abs_inv_alpha_lt_one fun n => ⟨(0 : ℤ), le_of_eq ?_⟩
  rw [Int.cast_zero, sub_zero, abs_div, abs_pow, abs_of_pos hα, abs_mul, abs_pow,
    abs_of_pos hα, P.abs_inv_alpha_eq, div_pow, one_pow]
  rw [show n + k + 1 = (n + 1) + k by ring, pow_add, pow_succ]
  field_simp

/-- Raising the rung by one peels off exactly one factor `ncos (x αᵏ)`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem shapeProd_succ (x : ℝ) (k : ℕ) :
    P.shapeProd x (k + 1) = ncos (x * P.α ^ k) * P.shapeProd x k := by
  have hα : (0:ℝ) < P.α := P.alpha_pos
  have hne : (P.α : ℝ) ≠ 0 := ne_of_gt hα
  have hcongr : ∀ j : ℕ, x * P.α ^ (k + 1) / P.α ^ (j + 1 + 1) = x * P.α ^ k / P.α ^ (j + 1) := by
    intro j
    rw [pow_succ, pow_succ (P.α) (j + 1)]
    field_simp
  have hmul : Multipliable fun j : ℕ => ncos (x * P.α ^ (k + 1) / P.α ^ (j + 1 + 1)) :=
    (P.multipliable_shapeProd x k).congr fun j => by rw [hcongr j]
  have main := tprod_eq_zero_mul'
    (f := fun j : ℕ => ncos (x * P.α ^ (k + 1) / P.α ^ (j + 1))) hmul
  have hzero : ncos (x * P.α ^ (k + 1) / P.α ^ (0 + 1)) = ncos (x * P.α ^ k) := by
    congr 1
    rw [zero_add, pow_one, pow_succ]
    field_simp
  have htail : (∏' j : ℕ, ncos (x * P.α ^ (k + 1) / P.α ^ (j + 1 + 1))) = P.shapeProd x k :=
    tprod_congr fun j => by rw [hcongr j]
  show (∏' j : ℕ, ncos (x * P.α ^ (k + 1) / P.α ^ (j + 1))) = ncos (x * P.α ^ k) * P.shapeProd x k
  rw [main, hzero, htail]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem shapeProd_eq_prod_range (x : ℝ) (k : ℕ) :
    P.shapeProd x k = (∏ n ∈ Finset.range k, ncos (x * P.α ^ n)) * P.shapeProd x 0 := by
  induction k with
  | zero => simp
  | succ k ih => rw [P.shapeProd_succ x k, ih, Finset.prod_range_succ]; ring

/-- The **bi-infinite Erdős product** of amplitude `x`, `∏_{n∈ℤ} ncos (x αⁿ)`, written as
the product of its two one-sided halves. -/
def biProd (x : ℝ) : ℝ := (∏' n : ℕ, ncos (x * P.α ^ n)) * P.shapeProd x 0

/-- The shape products converge to the bi-infinite product. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tendsto_shapeProd (x : ℝ) (hx : Multipliable fun n : ℕ => ncos (x * P.α ^ n)) :
    Tendsto (fun k => P.shapeProd x k) atTop (𝓝 (P.biProd x)) := by
  have h := hx.hasProd.tendsto_prod_nat.mul_const (P.shapeProd x 0)
  simpa only [← P.shapeProd_eq_prod_range x, biProd] using h

/-! ## Amplitudes whose forward orbit stays near `ℤ` -/

/-- `x` is a **good amplitude** when `x αⁿ` is within a geometric distance of an integer for
every `n`.  This is what makes the forward half of `biProd x` converge, and it holds for the
two profiles of `BB61/Plateau.lean` because a shape and its algebraic conjugate sum to an
integer (the trace identities below). -/
def GoodAmp (x : ℝ) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, ∃ N : ℤ, |x * P.α ^ n - (N : ℝ)| ≤ C * |P.β| ^ n

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem GoodAmp.multipliable {P : QuadSetup} {x : ℝ} (h : P.GoodAmp x) :
    Multipliable fun n : ℕ => ncos (x * P.α ^ n) := by
  obtain ⟨C, hC⟩ := h
  exact multipliable_ncos_of_geom_tail (C := C) (r := P.β) 0 P.abs_beta_lt_one
    (by simpa using hC)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem GoodAmp.mul_alpha {P : QuadSetup} {x : ℝ} (h : P.GoodAmp x) :
    P.GoodAmp (x * P.α) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C * |P.β|, fun n => ?_⟩
  obtain ⟨N, hN⟩ := hC (n + 1)
  refine ⟨N, ?_⟩
  have hx : x * P.α * P.α ^ n = x * P.α ^ (n + 1) := by rw [pow_succ]; ring
  rw [hx]
  calc |x * P.α ^ (n + 1) - (N : ℝ)| ≤ C * |P.β| ^ (n + 1) := hN
    _ = C * |P.β| * |P.β| ^ n := by rw [pow_succ]; ring

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem GoodAmp.multipliable_succ {P : QuadSetup} {x : ℝ} (h : P.GoodAmp x) :
    Multipliable fun j : ℕ => ncos (x * P.α ^ (j + 1)) :=
  h.mul_alpha.multipliable.congr fun j => by rw [pow_succ]; ring_nf

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem GoodAmp.neg {P : QuadSetup} {x : ℝ} (h : P.GoodAmp x) : P.GoodAmp (-x) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun n => ?_⟩
  obtain ⟨N, hN⟩ := hC n
  refine ⟨-N, ?_⟩
  have : -x * P.α ^ n - ((-N : ℤ) : ℝ) = -(x * P.α ^ n - (N : ℝ)) := by push_cast; ring
  rw [this, abs_neg]
  exact hN

/-! ## The conjugate profiles, and the trace identities they satisfy -/

variable (h₀ h₁ : ℤ)

/-- The **conjugate future profile** `A' = -e₀(α-1)/(α-β)`.  In the language of M1 Prop. 15
(`BB61/TraceLadder.lean`), `shapeFut = λ(α-1)` and `shapeFutC = λ'(α-1)`, where `λ` is the
codifferent parameter of the ladder and `λ'` its algebraic conjugate. -/
def shapeFutC : ℝ := -(P.ladE h₀ h₁) * (P.α - 1) / (P.α - P.β)

/-- The **conjugate past profile** `B' = -e₀(β-1)/(α-β) = λ'(β-1)`. -/
def shapePastC : ℝ := -(P.ladE h₀ h₁) * (P.β - 1) / (P.α - P.β)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem shapeFutC_mul : P.shapeFutC h₀ h₁ * (P.α - P.β) = -(P.ladE h₀ h₁) * (P.α - 1) := by
  rw [shapeFutC, div_mul_cancel₀ _ (ne_of_gt (alpha_sub_beta_pos (P := P)))]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem shapePastC_mul : P.shapePastC h₀ h₁ * (P.α - P.β) = -(P.ladE h₀ h₁) * (P.β - 1) := by
  rw [shapePastC, div_mul_cancel₀ _ (ne_of_gt (alpha_sub_beta_pos (P := P)))]

/-- Division-free Binet, read backwards: a pair `(u, v)` matching the Binet coefficients of
an integer ladder makes `u αⁿ + v βⁿ` that ladder — hence an **integer** at every `n`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem lad_eq_of_binet {u v : ℝ} {p q : ℤ}
    (hu : P.ladF p q = u * (P.α - P.β)) (hv : P.ladE p q = -(v * (P.α - P.β))) (n : ℕ) :
    u * P.α ^ n + v * P.β ^ n = (P.lad p q n : ℝ) := by
  have hne : P.α - P.β ≠ 0 := ne_of_gt (alpha_sub_beta_pos (P := P))
  have hb := P.lad_binet p q n
  rw [hu, hv] at hb
  apply mul_left_cancel₀ hne
  linear_combination -hb

/-- **Trace identity I.**  `A αⁿ + B' βⁿ` is an integer at every `n`: it is the rung `n` of
the integer ladder started at `h₁-h₀`, `a h₁ + b h₀ - h₁`.  (Conceptually
`Tr(λ(α-1)αⁿ) = h_{n+1} - h_n`; the ladder form avoids the number field.) -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem shapeFut_pow_add (n : ℕ) :
    P.shapeFut h₀ h₁ * P.α ^ n + P.shapePastC h₀ h₁ * P.β ^ n
      = (P.lad (h₁ - h₀) (P.a * h₁ + P.b * h₀ - h₁) n : ℝ) := by
  refine P.lad_eq_of_binet ?_ ?_ n
  · rw [P.shapeFut_mul h₀ h₁]
    simp only [ladF]
    push_cast
    linear_combination (-(h₁ : ℝ)) * P.alpha_add_beta + (h₀ : ℝ) * P.alpha_mul_beta
  · rw [P.shapePastC_mul h₀ h₁]
    simp only [ladE]
    push_cast
    linear_combination (-(h₁ : ℝ)) * P.alpha_add_beta + (h₀ : ℝ) * P.alpha_mul_beta

/-- **Trace identity II.**  `B αⁿ + A' βⁿ` is an integer at every `n` — the rung `n` of the
ladder started at `a h₀ - h₁ - h₀`, `-b h₀ - h₁`.  (Conceptually `Tr(λ(β-1)αⁿ)`; note that
`β - 1 ∈ ℤ[α]`, which is why this is an integer at all.) -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem shapePast_pow_add (n : ℕ) :
    P.shapePast h₀ h₁ * P.α ^ n + P.shapeFutC h₀ h₁ * P.β ^ n
      = (P.lad (P.a * h₀ - h₁ - h₀) (-P.b * h₀ - h₁) n : ℝ) := by
  refine P.lad_eq_of_binet ?_ ?_ n
  · rw [P.shapePast_mul h₀ h₁]
    simp only [ladF]
    push_cast
    linear_combination (h₀ : ℝ) * P.beta_root
  · rw [P.shapeFutC_mul h₀ h₁]
    simp only [ladE]
    push_cast
    linear_combination (h₀ : ℝ) * P.root

@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem goodAmp_shapeFut : P.GoodAmp (P.shapeFut h₀ h₁) := by
  refine ⟨|P.shapePastC h₀ h₁|,
    fun n => ⟨P.lad (h₁ - h₀) (P.a * h₁ + P.b * h₀ - h₁) n, ?_⟩⟩
  have h := P.shapeFut_pow_add h₀ h₁ n
  have hrw : P.shapeFut h₀ h₁ * P.α ^ n
      - ((P.lad (h₁ - h₀) (P.a * h₁ + P.b * h₀ - h₁) n : ℤ) : ℝ)
      = -(P.shapePastC h₀ h₁ * P.β ^ n) := by linarith
  rw [hrw, abs_neg, abs_mul, abs_pow]

@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem goodAmp_shapePast : P.GoodAmp (P.shapePast h₀ h₁) := by
  refine ⟨|P.shapeFutC h₀ h₁|,
    fun n => ⟨P.lad (P.a * h₀ - h₁ - h₀) (-P.b * h₀ - h₁) n, ?_⟩⟩
  have h := P.shapePast_pow_add h₀ h₁ n
  have hrw : P.shapePast h₀ h₁ * P.α ^ n
      - ((P.lad (P.a * h₀ - h₁ - h₀) (-P.b * h₀ - h₁) n : ℤ) : ℝ)
      = -(P.shapeFutC h₀ h₁ * P.β ^ n) := by linarith
  rw [hrw, abs_neg, abs_mul, abs_pow]

/-! ## Each one-sided factor converges along a ladder -/

/-- **The future factor of the rung `hₖ` is within `π|e₀|ρᵏ/(α-β)` of the shape product.**
Every factor of the two products differs by at most `π` times the profile error of
`BB61/Plateau.lean`, and those errors sum to a geometric series in `ρᵏ`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_futProd_sub_shapeProd_le (k : ℕ) :
    |P.futProd (P.lad h₀ h₁ k : ℝ) - P.shapeProd (P.shapeFut h₀ h₁) k|
      ≤ Real.pi * |P.ladE h₀ h₁| * |P.β| ^ k / (P.α - P.β) := by
  have hα : (0:ℝ) < P.α := P.alpha_pos
  have hu := alpha_sub_beta_pos (P := P)
  have hone : (0:ℝ) < P.α - 1 := by linarith [P.one_lt]
  have hr : (1:ℝ) / P.α < 1 := by rw [div_lt_one hα]; exact P.one_lt
  have hr0 : (0:ℝ) ≤ 1 / P.α := by positivity
  set E : ℝ := Real.pi * |P.ladE h₀ h₁| * (P.α - 1) * |P.β| ^ k / (P.α - P.β) with hEdef
  have hbd : ∀ j : ℕ,
      |ncos ((P.lad h₀ h₁ k : ℝ) * (P.α - 1) / P.α ^ (j + 1))
        - ncos (P.shapeFut h₀ h₁ * P.α ^ k / P.α ^ (j + 1))| ≤ E * (1 / P.α) ^ (j + 1) := by
    intro j
    have h1 := abs_ncos_sub_ncos_le ((P.lad h₀ h₁ k : ℝ) * (P.α - 1) / P.α ^ (j + 1))
      (P.shapeFut h₀ h₁ * P.α ^ k / P.α ^ (j + 1))
    rw [P.abs_future_sub_shape h₀ h₁ k (j + 1)] at h1
    refine h1.trans (le_of_eq ?_)
    rw [hEdef, div_pow, one_pow]
    field_simp
  have hgeo : Summable fun j : ℕ => E * (1 / P.α) ^ (j + 1) := by
    refine ((summable_geometric_of_lt_one hr0 hr).mul_left (E * (1 / P.α))).congr fun j => ?_
    rw [pow_succ]; ring
  have hsum : Summable fun j : ℕ =>
      |ncos ((P.lad h₀ h₁ k : ℝ) * (P.α - 1) / P.α ^ (j + 1))
        - ncos (P.shapeFut h₀ h₁ * P.α ^ k / P.α ^ (j + 1))| :=
    Summable.of_nonneg_of_le (fun j => abs_nonneg _) hbd hgeo
  have hgeoval : (∑' j : ℕ, E * (1 / P.α) ^ (j + 1)) = E / (P.α - 1) := by
    have hfun : (fun j : ℕ => E * (1 / P.α) ^ (j + 1))
        = fun j : ℕ => E * (1 / P.α) * (1 / P.α) ^ j := by
      funext j; rw [pow_succ]; ring
    have hne : (1:ℝ) - 1 / P.α ≠ 0 := by linarith
    rw [hfun, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr]
    field_simp
  simp only [futProd, shapeProd]
  calc |(∏' j : ℕ, ncos ((P.lad h₀ h₁ k : ℝ) * (P.α - 1) / P.α ^ (j + 1)))
          - ∏' j : ℕ, ncos (P.shapeFut h₀ h₁ * P.α ^ k / P.α ^ (j + 1))|
      ≤ ∑' j : ℕ, |ncos ((P.lad h₀ h₁ k : ℝ) * (P.α - 1) / P.α ^ (j + 1))
          - ncos (P.shapeFut h₀ h₁ * P.α ^ k / P.α ^ (j + 1))| :=
        abs_tprod_sub_tprod_le (fun _ => ncos_nonneg _) (fun _ => ncos_le_one _)
          (fun _ => ncos_nonneg _) (fun _ => ncos_le_one _)
          (P.multipliable_futProd _) (P.multipliable_shapeProd _ k) hsum
    _ ≤ ∑' j : ℕ, E * (1 / P.α) ^ (j + 1) := hsum.tsum_le_tsum hbd hgeo
    _ = E / (P.α - 1) := hgeoval
    _ = Real.pi * |P.ladE h₀ h₁| * |P.β| ^ k / (P.α - P.β) := by
        rw [hEdef]; field_simp

/-- **The past factor of the rung `hₖ` is within `π|e₀||β-1|ρᵏ/((α-β)(1-ρ))` of the shape
product one rung further out.**  `|b| = 1` is spent exactly once, to erase the sign
`(-b)ᵐ` from the past profile. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem abs_pastProd_sub_shapeProd_le (hb : |(P.b : ℝ)| = 1) (k : ℕ) :
    |P.pastProd (P.lad h₀ h₁ k : ℝ) - P.shapeProd (P.shapePast h₀ h₁) (k + 1)|
      ≤ Real.pi * |P.ladE h₀ h₁| * |P.β - 1| * |P.β| ^ k / ((P.α - P.β) * (1 - |P.β|)) := by
  have hα : (0:ℝ) < P.α := P.alpha_pos
  have hu := alpha_sub_beta_pos (P := P)
  have hb1 := P.abs_beta_lt_one
  have hb0 : (0:ℝ) ≤ |P.β| := abs_nonneg _
  set E : ℝ := Real.pi * |P.ladE h₀ h₁| * |P.β - 1| * |P.β| ^ k / (P.α - P.β) with hEdef
  have hgm : ∀ m : ℕ, ncos (P.shapePast h₀ h₁ * P.α ^ (k + 1) / P.α ^ (m + 1))
      = ncos (P.shapePast h₀ h₁ * ((-(P.b : ℝ)) ^ m * P.α ^ k / P.α ^ m)) := by
    intro m
    have habs : |(-(P.b : ℝ)) ^ m| = 1 := by rw [abs_pow, abs_neg, hb, one_pow]
    have hx : P.shapePast h₀ h₁ * ((-(P.b : ℝ)) ^ m * P.α ^ k / P.α ^ m)
        = (-(P.b : ℝ)) ^ m * (P.shapePast h₀ h₁ * P.α ^ (k + 1) / P.α ^ (m + 1)) := by
      rw [pow_succ, pow_succ]
      field_simp
    rw [hx, ncos_mul_of_abs_eq_one habs]
  have hbd : ∀ m : ℕ,
      |ncos ((P.lad h₀ h₁ k : ℝ) * P.cCoef m)
        - ncos (P.shapePast h₀ h₁ * P.α ^ (k + 1) / P.α ^ (m + 1))| ≤ E * |P.β| ^ m := by
    intro m
    rw [hgm m]
    have h1 := abs_ncos_sub_ncos_le ((P.lad h₀ h₁ k : ℝ) * P.cCoef m)
      (P.shapePast h₀ h₁ * ((-(P.b : ℝ)) ^ m * P.α ^ k / P.α ^ m))
    rw [P.abs_past_sub_shape h₀ h₁ k m] at h1
    refine h1.trans (le_of_eq ?_)
    rw [hEdef, pow_add]
    field_simp
  have hgeo : Summable fun m : ℕ => E * |P.β| ^ m :=
    (summable_geometric_of_lt_one hb0 hb1).mul_left _
  have hsum : Summable fun m : ℕ =>
      |ncos ((P.lad h₀ h₁ k : ℝ) * P.cCoef m)
        - ncos (P.shapePast h₀ h₁ * P.α ^ (k + 1) / P.α ^ (m + 1))| :=
    Summable.of_nonneg_of_le (fun m => abs_nonneg _) hbd hgeo
  simp only [pastProd, shapeProd]
  calc |(∏' m : ℕ, ncos ((P.lad h₀ h₁ k : ℝ) * P.cCoef m))
          - ∏' m : ℕ, ncos (P.shapePast h₀ h₁ * P.α ^ (k + 1) / P.α ^ (m + 1))|
      ≤ ∑' m : ℕ, |ncos ((P.lad h₀ h₁ k : ℝ) * P.cCoef m)
          - ncos (P.shapePast h₀ h₁ * P.α ^ (k + 1) / P.α ^ (m + 1))| :=
        abs_tprod_sub_tprod_le (fun _ => ncos_nonneg _) (fun _ => ncos_le_one _)
          (fun _ => ncos_nonneg _) (fun _ => ncos_le_one _)
          (P.multipliable_pastProd _) (P.multipliable_shapeProd _ (k + 1)) hsum
    _ ≤ ∑' m : ℕ, E * |P.β| ^ m := hsum.tsum_le_tsum hbd hgeo
    _ = E * (1 - |P.β|)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hb0 hb1]
    _ = Real.pi * |P.ladE h₀ h₁| * |P.β - 1| * |P.β| ^ k / ((P.α - P.β) * (1 - |P.β|)) := by
        rw [hEdef]
        have hne : (1:ℝ) - |P.β| ≠ 0 := by linarith
        field_simp

/-! ## The limits along a ladder -/

/-- **The future factor converges along every ladder**, at every quadratic `α` — unit or
not.  This is the note's "the future factor still settles". -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tendsto_futProd :
    Tendsto (fun k => P.futProd (P.lad h₀ h₁ k : ℝ)) atTop
      (𝓝 (P.biProd (P.shapeFut h₀ h₁))) := by
  have hshape := P.tendsto_shapeProd (P.shapeFut h₀ h₁) (P.goodAmp_shapeFut h₀ h₁).multipliable
  have hz : Tendsto (fun k : ℕ => Real.pi * |P.ladE h₀ h₁| * |P.β| ^ k / (P.α - P.β))
      atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg P.β) P.abs_beta_lt_one
    simpa using (h.const_mul (Real.pi * |P.ladE h₀ h₁|)).div_const (P.α - P.β)
  have hdiff : Tendsto
      (fun k => P.futProd (P.lad h₀ h₁ k : ℝ) - P.shapeProd (P.shapeFut h₀ h₁) k)
      atTop (𝓝 0) :=
    squeeze_zero_norm (fun k => by
      simpa [Real.norm_eq_abs] using P.abs_futProd_sub_shapeProd_le h₀ h₁ k) hz
  simpa using hdiff.add hshape

/-- **The past factor converges along every ladder at a quadratic unit.**  Off a unit the
sign `(-b)ᵐ` in the past profile is a genuine factor `|b|ᵐ` and the statement fails — that
is Observation 16(ii), and the note's "the past factor collapses". -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tendsto_pastProd (hb : |(P.b : ℝ)| = 1) :
    Tendsto (fun k => P.pastProd (P.lad h₀ h₁ k : ℝ)) atTop
      (𝓝 (P.biProd (P.shapePast h₀ h₁))) := by
  have hshape0 :=
    P.tendsto_shapeProd (P.shapePast h₀ h₁) (P.goodAmp_shapePast h₀ h₁).multipliable
  have hshape : Tendsto (fun k => P.shapeProd (P.shapePast h₀ h₁) (k + 1)) atTop
      (𝓝 (P.biProd (P.shapePast h₀ h₁))) := hshape0.comp (tendsto_add_atTop_nat 1)
  have hz : Tendsto (fun k : ℕ => Real.pi * |P.ladE h₀ h₁| * |P.β - 1| * |P.β| ^ k
      / ((P.α - P.β) * (1 - |P.β|))) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg P.β) P.abs_beta_lt_one
    simpa using (h.const_mul (Real.pi * |P.ladE h₀ h₁| * |P.β - 1|)).div_const
      ((P.α - P.β) * (1 - |P.β|))
  have hdiff : Tendsto
      (fun k => P.pastProd (P.lad h₀ h₁ k : ℝ) - P.shapeProd (P.shapePast h₀ h₁) (k + 1))
      atTop (𝓝 0) :=
    squeeze_zero_norm (fun k => by
      simpa [Real.norm_eq_abs] using P.abs_pastProd_sub_shapeProd_le h₀ h₁ hb k) hz
  simpa using hdiff.add hshape

/-- **The plateau.**  `|G_{1/2}(hₖ)|` converges to the product of the two bi-infinite
Erdős products, one for each profile. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tendsto_weylProd (hb : |(P.b : ℝ)| = 1) :
    Tendsto (fun k => P.weylProd (P.lad h₀ h₁ k : ℝ)) atTop
      (𝓝 (P.biProd (P.shapeFut h₀ h₁) * P.biProd (P.shapePast h₀ h₁))) :=
  (P.tendsto_futProd h₀ h₁).mul (P.tendsto_pastProd h₀ h₁ hb)

/-! ## Norm `+1`: the two factors are equal at every rung -/

/-- **At a quadratic unit of norm `+1` there is no limit to take.**  M5 Thm 7
(`past_eq_future`) makes the past ladder the future ladder shifted by one, so the two
one-sided products are equal factor by factor, for *every* mode `h` — not just along a
ladder, and not just asymptotically. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem pastProd_eq_futProd (hb : P.b = -1) (h : ℝ) : P.pastProd h = P.futProd h := by
  simp only [pastProd, futProd]
  refine tprod_congr fun m => ?_
  rw [cCoef, P.past_eq_future hb m,
    show h * -((P.α - 1) / P.α ^ (m + 1)) = -(h * (P.α - 1) / P.α ^ (m + 1)) by ring, ncos_neg]

/-- Hence the Erdős product is a perfect square at every mode. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem weylProd_eq_sq (hb : P.b = -1) (h : ℝ) : P.weylProd h = P.futProd h ^ 2 := by
  rw [weylProd, P.pastProd_eq_futProd hb h, sq]

/-! ## The reflection at a quadratic unit -/

/-- At a unit `βⁿ = ±α^{-n}`, so `ncos` does not see the difference. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem ncos_mul_beta_pow (hb : |(P.b : ℝ)| = 1) (x : ℝ) (n : ℕ) :
    ncos (x * P.β ^ n) = ncos (x / P.α ^ n) := by
  have hα : (0:ℝ) < P.α := P.alpha_pos
  have h1 : |P.β ^ n| = 1 / P.α ^ n := by rw [abs_pow, P.abs_beta_pow_unit hb n]
  have hpos : (0:ℝ) ≤ 1 / P.α ^ n := by positivity
  rcases (abs_eq hpos).mp h1 with h | h
  · rw [h, mul_one_div]
  · rw [h, show x * -(1 / P.α ^ n) = -(x / P.α ^ n) by ring, ncos_neg]

/-- **Trace identity III**, the mirror of II: `A' αⁿ + B βⁿ` is an integer at every `n`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem shapeFutC_pow_add (n : ℕ) :
    P.shapeFutC h₀ h₁ * P.α ^ n + P.shapePast h₀ h₁ * P.β ^ n
      = (P.lad (P.a * h₀ - h₁ - h₀)
          (P.a * (P.a * h₀ - h₁ - h₀) - (-P.b * h₀ - h₁)) n : ℝ) := by
  have ha : (P.a : ℝ) = P.α + P.β := P.alpha_add_beta.symm
  have hbb : (P.b : ℝ) = -(P.α * P.β) := by linarith [P.alpha_mul_beta]
  refine P.lad_eq_of_binet ?_ ?_ n
  · rw [P.shapeFutC_mul h₀ h₁]
    simp only [ladF, ladE]
    push_cast
    simp only [ha, hbb]
    ring
  · rw [P.shapePast_mul h₀ h₁]
    simp only [ladE, ladF]
    push_cast
    simp only [ha, hbb]
    ring

@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem goodAmp_shapeFutC : P.GoodAmp (P.shapeFutC h₀ h₁) := by
  refine ⟨|P.shapePast h₀ h₁|, fun n => ⟨P.lad (P.a * h₀ - h₁ - h₀)
    (P.a * (P.a * h₀ - h₁ - h₀) - (-P.b * h₀ - h₁)) n, ?_⟩⟩
  have h := P.shapeFutC_pow_add h₀ h₁ n
  have hrw : P.shapeFutC h₀ h₁ * P.α ^ n
      - ((P.lad (P.a * h₀ - h₁ - h₀)
          (P.a * (P.a * h₀ - h₁ - h₀) - (-P.b * h₀ - h₁)) n : ℤ) : ℝ)
      = -(P.shapePast h₀ h₁ * P.β ^ n) := by linarith
  rw [hrw, abs_neg, abs_mul, abs_pow]

/-- Two amplitudes each of which reflects onto the other's inverse orbit have the same
bi-infinite Erdős product.  This is the whole content of "the two one-sided factors share a
limit": the bi-infinite product does not care which way it is read. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem biProd_eq_of_reflect {x y : ℝ} (hy : P.GoodAmp y)
    (hxy : ∀ n : ℕ, ncos (x * P.α ^ n) = ncos (y / P.α ^ n))
    (hyx : ∀ n : ℕ, ncos (y * P.α ^ n) = ncos (x / P.α ^ n)) :
    P.biProd x = P.biProd y := by
  have hsp : ∀ z : ℝ, P.shapeProd z 0 = ∏' j : ℕ, ncos (z / P.α ^ (j + 1)) := by
    intro z
    rw [shapeProd]
    exact tprod_congr fun j => by rw [pow_zero, mul_one]
  have hmy0 : Multipliable fun j : ℕ => ncos (y / P.α ^ (j + 1)) :=
    (P.multipliable_shapeProd y 0).congr fun j => by rw [pow_zero, mul_one]
  have hmys : Multipliable fun j : ℕ => ncos (y * P.α ^ (j + 1)) := hy.multipliable_succ
  have hfwdx : (∏' n : ℕ, ncos (x * P.α ^ n)) = ncos y * P.shapeProd y 0 := by
    rw [tprod_congr hxy, tprod_eq_zero_mul' (f := fun n : ℕ => ncos (y / P.α ^ n)) hmy0,
      pow_zero, div_one, ← hsp]
  have hbackx : P.shapeProd x 0 = ∏' j : ℕ, ncos (y * P.α ^ (j + 1)) := by
    rw [hsp]
    exact tprod_congr fun j => (hyx (j + 1)).symm
  have hfwdy : (∏' n : ℕ, ncos (y * P.α ^ n))
      = ncos y * ∏' j : ℕ, ncos (y * P.α ^ (j + 1)) := by
    rw [tprod_eq_zero_mul' (f := fun n : ℕ => ncos (y * P.α ^ n)) hmys, pow_zero, mul_one]
  rw [biProd, biProd, hfwdx, hbackx, hfwdy]
  ring

/-- **The past limit is the future limit of the conjugate profile.**  At a quadratic unit,
`biProd B = biProd A'` — where `A = λ(α-1)` and `A' = λ'(α-1)`.  This is the exact form of
Observation 16(i): the two one-sided limits agree **iff** `biProd λ(α-1) = biProd λ'(α-1)`,
which is automatic when `λ' = ±αˢ λ` and false in general. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem biProd_shapePast_eq_shapeFutC (hb : |(P.b : ℝ)| = 1) :
    P.biProd (P.shapePast h₀ h₁) = P.biProd (P.shapeFutC h₀ h₁) := by
  refine P.biProd_eq_of_reflect (P.goodAmp_shapeFutC h₀ h₁) (fun n => ?_) fun n => ?_
  · rw [ncos_eq_of_add_int (P.shapePast_pow_add h₀ h₁ n), P.ncos_mul_beta_pow hb]
  · rw [ncos_eq_of_add_int (P.shapeFutC_pow_add h₀ h₁ n), P.ncos_mul_beta_pow hb]

/-! ## The two invariances of the bi-infinite product -/

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem biProd_neg (x : ℝ) : P.biProd (-x) = P.biProd x := by
  rw [biProd, biProd, shapeProd, shapeProd]
  congr 1
  · exact tprod_congr fun n => by rw [neg_mul, ncos_neg]
  · exact tprod_congr fun j => by rw [neg_mul, neg_div, ncos_neg]

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem GoodAmp.mul_pow {P : QuadSetup} {x : ℝ} (h : P.GoodAmp x) (s : ℕ) :
    P.GoodAmp (x * P.α ^ s) := by
  induction s with
  | zero => simpa using h
  | succ s ih =>
      have heq : x * P.α ^ (s + 1) = x * P.α ^ s * P.α := by ring
      rw [heq]
      exact ih.mul_alpha

/-- Multiplying the amplitude by `α` only shifts the index of the bi-infinite product. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem biProd_mul_alpha {x : ℝ} (hx : P.GoodAmp x) : P.biProd (x * P.α) = P.biProd x := by
  have hα : (0:ℝ) < P.α := P.alpha_pos
  have hne : (P.α : ℝ) ≠ 0 := ne_of_gt hα
  have hsp : P.shapeProd x 0 = ∏' j : ℕ, ncos (x / P.α ^ (j + 1)) := by
    rw [shapeProd]
    exact tprod_congr fun j => by rw [pow_zero, mul_one]
  have hm0 : Multipliable fun j : ℕ => ncos (x / P.α ^ (j + 1)) :=
    (P.multipliable_shapeProd x 0).congr fun j => by rw [pow_zero, mul_one]
  have hms : Multipliable fun j : ℕ => ncos (x * P.α ^ (j + 1)) := hx.multipliable_succ
  have hfwd : (∏' n : ℕ, ncos (x * P.α * P.α ^ n))
      = ∏' j : ℕ, ncos (x * P.α ^ (j + 1)) :=
    tprod_congr fun n => by rw [pow_succ]; ring_nf
  have hback : P.shapeProd (x * P.α) 0 = ncos x * P.shapeProd x 0 := by
    have h1 : P.shapeProd (x * P.α) 0 = ∏' j : ℕ, ncos (x / P.α ^ j) := by
      rw [shapeProd]
      refine tprod_congr fun j => ?_
      rw [pow_zero, mul_one, pow_succ]
      congr 1
      field_simp
    rw [h1, tprod_eq_zero_mul' (f := fun j : ℕ => ncos (x / P.α ^ j)) hm0, pow_zero, div_one,
      ← hsp]
  have hfwdx : (∏' n : ℕ, ncos (x * P.α ^ n))
      = ncos x * ∏' j : ℕ, ncos (x * P.α ^ (j + 1)) := by
    rw [tprod_eq_zero_mul' (f := fun n : ℕ => ncos (x * P.α ^ n)) hms, pow_zero, mul_one]
  rw [biProd, biProd, hfwd, hback, hfwdx]
  ring

@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem biProd_mul_pow {x : ℝ} (hx : P.GoodAmp x) (s : ℕ) :
    P.biProd (x * P.α ^ s) = P.biProd x := by
  induction s with
  | zero => rw [pow_zero, mul_one]
  | succ s ih =>
      have heq : x * P.α ^ (s + 1) = x * P.α ^ s * P.α := by ring
      rw [heq, P.biProd_mul_alpha (hx.mul_pow s), ih]

/-! ## Observation 16(i) -/

/-- `e₀ = -f₀` is the integer condition `2h₁ = a h₀`; in the language of M1 Prop. 15 it says
the codifferent parameter of the ladder is **rational**, `λ' = λ`, i.e. the ladder is a
rational multiple of the trace ladder `hₖ = Tr(αᵏ)`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem ladE_eq_neg_ladF_iff :
    P.ladE h₀ h₁ = -(P.ladF h₀ h₁) ↔ 2 * (h₁ : ℝ) = (P.a : ℝ) * h₀ := by
  simp only [ladE, ladF]
  constructor
  · intro h; linear_combination h + (h₀ : ℝ) * P.alpha_add_beta
  · intro h; linear_combination h - (h₀ : ℝ) * P.alpha_add_beta

/-- **The two limits agree when `λ' = ±αˢ λ`.**  The hypothesis is on the ladder, not on
`α`: it is what makes the conjugate profile `A'` a signed `α`-shift of `A`, and the
bi-infinite product is blind to both. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem biProd_shapePast_eq_of_pow (hb : |(P.b : ℝ)| = 1) (s : ℕ)
    (hs : P.ladE h₀ h₁ = -(P.ladF h₀ h₁ * P.α ^ s) ∨ P.ladE h₀ h₁ = P.ladF h₀ h₁ * P.α ^ s) :
    P.biProd (P.shapePast h₀ h₁) = P.biProd (P.shapeFut h₀ h₁) := by
  have hC : P.shapeFutC h₀ h₁ = P.shapeFut h₀ h₁ * P.α ^ s
      ∨ P.shapeFutC h₀ h₁ = -(P.shapeFut h₀ h₁ * P.α ^ s) := by
    rcases hs with h | h
    · left; rw [shapeFutC, h, neg_neg, shapeFut]; ring
    · right; rw [shapeFutC, h, shapeFut]; ring
  rw [P.biProd_shapePast_eq_shapeFutC h₀ h₁ hb]
  rcases hC with h | h
  · rw [h, P.biProd_mul_pow (P.goodAmp_shapeFut h₀ h₁) s]
  · rw [h, P.biProd_neg, P.biProd_mul_pow (P.goodAmp_shapeFut h₀ h₁) s]

/-- The `s = 0` case, `λ' = λ`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem biProd_shapePast_eq (hb : |(P.b : ℝ)| = 1) (hsym : P.ladE h₀ h₁ = -(P.ladF h₀ h₁)) :
    P.biProd (P.shapePast h₀ h₁) = P.biProd (P.shapeFut h₀ h₁) :=
  P.biProd_shapePast_eq_of_pow h₀ h₁ hb 0 (Or.inl (by simpa using hsym))

/-- **M1 Observation 16(i).**  At a quadratic unit, along a ladder with `2h₁ = a h₀`, the
past factor converges to the same limit `L = biProd A` as the future factor. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tendsto_pastProd_shapeFut (hb : |(P.b : ℝ)| = 1)
    (hsym : P.ladE h₀ h₁ = -(P.ladF h₀ h₁)) :
    Tendsto (fun k => P.pastProd (P.lad h₀ h₁ k : ℝ)) atTop
      (𝓝 (P.biProd (P.shapeFut h₀ h₁))) := by
  rw [← P.biProd_shapePast_eq h₀ h₁ hb hsym]
  exact P.tendsto_pastProd h₀ h₁ hb

/-- **M1 Observation 16(i), the plateau.**  The Erdős product along the ladder converges to
`L²`, the square of the one-sided Erdős constant. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tendsto_weylProd_sq (hb : |(P.b : ℝ)| = 1)
    (hsym : P.ladE h₀ h₁ = -(P.ladF h₀ h₁)) :
    Tendsto (fun k => P.weylProd (P.lad h₀ h₁ k : ℝ)) atTop
      (𝓝 (P.biProd (P.shapeFut h₀ h₁) ^ 2)) := by
  have h := (P.tendsto_futProd h₀ h₁).mul (P.tendsto_pastProd_shapeFut h₀ h₁ hb hsym)
  simpa [weylProd, sq] using h

/-! ## The trace ladder `hₖ = Tr(αᵏ)` -/

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem ladE_trace_eq_neg_ladF : P.ladE 2 P.a = -(P.ladF 2 P.a) := by
  rw [P.ladE_eq_neg_ladF_iff]
  push_cast
  ring

/-- **Observation 16(i) for the trace ladder** `2, a, a²+2b, …` — the ladder of the note's
own numerics.  Both one-sided factors converge to `L = biProd (α-1)`, and the plateau is
`L²`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem tendsto_weylProd_sq_trace (hb : |(P.b : ℝ)| = 1) :
    Tendsto (fun k => P.weylProd (P.lad 2 P.a k : ℝ)) atTop
      (𝓝 (P.biProd (P.shapeFut 2 P.a) ^ 2)) :=
  P.tendsto_weylProd_sq 2 P.a hb P.ladE_trace_eq_neg_ladF

end QuadSetup

/-! ## The instance `α = 2 + √3` -/

open QuadSetup

/-- At `α = 2 + √3` (norm `+1`) the Erdős product is a perfect square at **every** mode,
not merely in the limit. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem weylProd_eq_sq_twoAddSqrt3 (h : ℝ) :
    twoAddSqrt3.weylProd h = twoAddSqrt3.futProd h ^ 2 :=
  twoAddSqrt3.weylProd_eq_sq rfl h

end BB61
