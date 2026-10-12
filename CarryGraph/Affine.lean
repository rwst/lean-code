/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CarryGraph.Dimension
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.Star
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Affine carry graphs

The orbit `zₙ = ξ (p/q)ⁿ + ν` satisfies `z_{n+1} = (p/q)(zₙ − ν) + ν` (`affStep_orbit`).  Its
integer parts `xₙ = ⌊zₙ⌋` obey the **carry recurrence** `q x_{n+1} = p xₙ + sₙ`
(`q_mul_floor_affStep`), with the carry `sₙ = carry zₙ` in a window of `p + q + 1` integers
(`carry_window`), and the fractional parts `yₙ = {zₙ}` obey `q y_{n+1} = p yₙ − (p − q)ν − sₙ`
(`fract_affStep`).  The **affine system** is `(ℝ, affStep, affAdm)`: the step `t` is admissible at
`z` if the carry of `z` is the `t`-th letter `s₀ + t` and both `⌊z⌋` and `⌊affStep z⌋` avoid the
divisor set `P`.

Three carry graphs cover it, all with letters `Fin nA`:

* the **residue graph** `residueGraph p q M s₀ PM Pq` on `ZMod M`: `r →t r'` iff
  `q r' = p r + (s₀ + t)` and `r`, `r'` avoid `PM`, the letter avoids `Pq`
  (`cover_residueGraph`; `PM` divides `M`, `Pq` consists of primes dividing `q` but not `p`);
* the **block graph** `blockGraph p q ν s₀ I` on `Fin n`, for intervals `I i = [aᵢ, bᵢ)` that
  cover `[0, 1)`: `i →t j` iff the image of `I i` under `y ↦ (p y − (p − q)ν − s)/q` meets `I j`
  (`cover_blockGraph`, via the fractional system and `Cover.comap`).  The **cell graph**
  `cellGraph p q ν s₀ D` is the block graph of the `D` cells `[c/D, (c+1)/D)`;
* the **affine graph** `affine = residueGraph ⊗ cellGraph`, the label product
  (`cover_affine`, from `Cover.labelProduct`).

Gate G-4 of the plan checked on all 16 `DubC2/Atlas` cells that `DubC2.Gen.Params.succList` is
this label product, arc for arc.

## Main results

* `realizes_blockGraph`: a **Markov** block graph (every arc's target interval lies inside the
  image) realises its words in the fractional system (nested intervals);
* `blockGraph_hom` / `cellGraph_hom`: refining the intervals gives a homomorphism to the coarser
  graph, so certificates of the coarse graph hold for the fine one;
* `dimH_avoiders_le`: for **every** finite carry graph `X` covering the affine system,
  `dim_H {ξ | ⌊ξ(p/q)ⁿ + ν⌋ eventually avoids P} ≤ entropy X / log (p/q)`.  This is the generic
  form of `DubC2.Gen.dimH_eventually_avoids_le`.
-/

open Filter ENNReal ExpGrowth Metric
open scoped NNReal

namespace CarryGraph

/-! ### The affine step and its carry -/

/-- The affine step `z ↦ (p/q)(z − ν) + ν`. -/
noncomputable def affStep (p q : ℕ) (ν z : ℝ) : ℝ := p / q * (z - ν) + ν

/-- The carry of `z`: `q ⌊affStep z⌋ − p ⌊z⌋`. -/
noncomputable def carry (p q : ℕ) (ν z : ℝ) : ℤ := q * ⌊affStep p q ν z⌋ - p * ⌊z⌋

variable {p q : ℕ} {ν : ℝ}

@[category API, AMS 11 37, group "carry_affine"]
theorem affStep_orbit (ξ : ℝ) (n : ℕ) :
    affStep p q ν (ξ * ((p : ℝ) / q) ^ n + ν) = ξ * ((p : ℝ) / q) ^ (n + 1) + ν := by
  simp only [affStep, pow_succ]; ring

/-- **The carry recurrence** `q x_{n+1} = p xₙ + sₙ`. -/
@[category API, AMS 11 37, group "carry_affine"]
theorem q_mul_floor_affStep (z : ℝ) :
    (q : ℤ) * ⌊affStep p q ν z⌋ = p * ⌊z⌋ + carry p q ν z := by
  simp only [carry]; ring

@[category API, AMS 11 37, group "carry_affine"]
theorem q_mul_affStep (hq : q ≠ 0) (z : ℝ) :
    (q : ℝ) * affStep p q ν z = p * z - ((p : ℝ) - q) * ν := by
  have : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  simp only [affStep]; field_simp; ring

/-- **The fractional recurrence** `q y_{n+1} = p yₙ − (p − q)ν − sₙ`. -/
@[category API, AMS 11 37, group "carry_affine"]
theorem fract_affStep (hq : q ≠ 0) (z : ℝ) :
    (q : ℝ) * Int.fract (affStep p q ν z)
      = p * Int.fract z - ((p : ℝ) - q) * ν - carry p q ν z := by
  have h := q_mul_floor_affStep (p := p) (q := q) (ν := ν) z
  have h' : (q : ℝ) * ⌊affStep p q ν z⌋ = p * ⌊z⌋ + carry p q ν z := by exact_mod_cast h
  rw [Int.fract, Int.fract, mul_sub, q_mul_affStep hq, h']; ring

/-- **The carry window**: `⌊−(p − q)ν⌋ − q < carry z < ⌊−(p − q)ν⌋ − q + p + q + 1`. -/
@[category API, AMS 11 37, group "carry_affine"]
theorem carry_window (hq : q ≠ 0) (z : ℝ) :
    ⌊-((p : ℝ) - q) * ν⌋ - q ≤ carry p q ν z ∧
      carry p q ν z < ⌊-((p : ℝ) - q) * ν⌋ - q + (p + q + 1 : ℕ) := by
  have h := fract_affStep (p := p) (ν := ν) hq z
  have hy0 := Int.fract_nonneg z
  have hy1 := Int.fract_lt_one z
  have hz0 := Int.fract_nonneg (affStep p q ν z)
  have hz1 := Int.fract_lt_one (affStep p q ν z)
  have hq' : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  have hp' : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hf1 := Int.floor_le (-((p : ℝ) - q) * ν)
  have hf2 := Int.lt_floor_add_one (-((p : ℝ) - q) * ν)
  have hs : (carry p q ν z : ℝ) = p * Int.fract z - ((p : ℝ) - q) * ν
      - q * Int.fract (affStep p q ν z) := by linarith
  constructor
  · have : ((⌊-((p : ℝ) - q) * ν⌋ - q : ℤ) : ℝ) < carry p q ν z + 1 := by
      push_cast; nlinarith
    exact_mod_cast Int.lt_add_one_iff.1 (by exact_mod_cast this)
  · have : (carry p q ν z : ℝ) < ((⌊-((p : ℝ) - q) * ν⌋ - q + (p + q + 1 : ℕ) : ℤ) : ℝ) := by
      push_cast; nlinarith
    exact_mod_cast this

/-- **The carry bounds**: `−q − (p − q)ν < carry z < p − (p − q)ν`. -/
@[category API, AMS 11 37, group "carry_affine"]
theorem carry_bounds (hq : q ≠ 0) (hp : 0 < p) (z : ℝ) :
    -(q : ℝ) - ((p : ℝ) - q) * ν < carry p q ν z ∧ (carry p q ν z : ℝ) < p - ((p : ℝ) - q) * ν := by
  have h := fract_affStep (p := p) (ν := ν) hq z
  have hy0 := Int.fract_nonneg z
  have hy1 := Int.fract_lt_one z
  have hz0 := Int.fract_nonneg (affStep p q ν z)
  have hz1 := Int.fract_lt_one (affStep p q ν z)
  have hq' : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hs : (carry p q ν z : ℝ) = p * Int.fract z - ((p : ℝ) - q) * ν
      - q * Int.fract (affStep p q ν z) := by linarith
  have e1 : (p : ℝ) * Int.fract z < p := mul_lt_of_lt_one_right hp' hy1
  have e2 : (q : ℝ) * Int.fract (affStep p q ν z) < q := mul_lt_of_lt_one_right hq' hz1
  have e3 := mul_nonneg hp'.le hy0
  have e4 := mul_nonneg hq'.le hz0
  constructor <;> linarith

/-! ### The affine system -/

/-- `x` avoids the divisor set `P`. -/
def Avoid (P : List ℕ) (x : ℤ) : Prop := ∀ ℓ ∈ P, ¬ (ℓ : ℤ) ∣ x

instance (P : List ℕ) (x : ℤ) : Decidable (Avoid P x) :=
  inferInstanceAs (Decidable (∀ ℓ ∈ P, ¬ (ℓ : ℤ) ∣ x))

/-- Admissibility in the affine system: the carry is the letter `s₀ + t`, and the integer parts
before and after the step avoid `P`. -/
def affAdm (p q : ℕ) (ν : ℝ) (s₀ : ℤ) (P : List ℕ) {nA : ℕ} (z : ℝ) (t : Fin nA) : Prop :=
  carry p q ν z = s₀ + t ∧ Avoid P ⌊z⌋ ∧ Avoid P ⌊affStep p q ν z⌋

/-! ### The residue graph -/

/-- `r` avoids `PM` as a residue. -/
def ResOK {M : ℕ} (PM : List ℕ) (r : ZMod M) : Prop := ∀ ℓ ∈ PM, ¬ (ℓ : ℤ) ∣ (r.val : ℤ)

instance {M : ℕ} (PM : List ℕ) (r : ZMod M) : Decidable (ResOK PM r) :=
  inferInstanceAs (Decidable (∀ ℓ ∈ PM, ¬ (ℓ : ℤ) ∣ (r.val : ℤ)))

/-- **The residue graph**: `r →t r'` iff `q r' = p r + (s₀ + t)` in `ZMod M`, with `r`, `r'`
avoiding `PM` and the letter avoiding `Pq`. -/
def residueGraph (p q M : ℕ) [NeZero M] (s₀ : ℤ) (nA : ℕ) (PM Pq : List ℕ) :
    CarryGraph (ZMod M) (Fin nA) :=
  ⟨fun r t => Finset.univ.filter fun r' =>
    ResOK PM r ∧ Avoid Pq (s₀ + t) ∧ (q : ZMod M) * r' = p * r + ((s₀ + t : ℤ) : ZMod M) ∧
      ResOK PM r'⟩

@[category API, AMS 11 05, group "carry_affine"]
theorem adj_residueGraph {M : ℕ} [NeZero M] {s₀ : ℤ} {nA : ℕ} {PM Pq : List ℕ} {r r' : ZMod M}
    {t : Fin nA} :
    (residueGraph p q M s₀ nA PM Pq).Adj r t r' ↔
      ResOK PM r ∧ Avoid Pq (s₀ + t) ∧ (q : ZMod M) * r' = p * r + ((s₀ + t : ℤ) : ZMod M) ∧
        ResOK PM r' := by
  simp [residueGraph, Adj]

@[category API, AMS 11, group "carry_affine"]
theorem resOK_intCast {M : ℕ} [NeZero M] {PM : List ℕ} (hPM : ∀ ℓ ∈ PM, ℓ ∣ M) {x : ℤ}
    (hx : Avoid PM x) : ResOK PM (x : ZMod M) := by
  intro ℓ hℓ hdvd
  apply hx ℓ hℓ
  rw [ZMod.val_intCast] at hdvd
  have hM : (ℓ : ℤ) ∣ (M : ℤ) := by exact_mod_cast hPM ℓ hℓ
  have := Int.emod_add_mul_ediv x M
  rw [← this]
  exact dvd_add hdvd (dvd_mul_of_dvd_left hM _)

/-- **The residue cover**: the residue graph covers the affine system through
`ρ r = {z | ⌊z⌋ ≡ r (mod M)}`. -/
@[category textbook, AMS 11 37 05, group "carry_affine"]
theorem cover_residueGraph {M : ℕ} [NeZero M] {s₀ : ℤ} {nA : ℕ} {PM Pq P : List ℕ}
    (hPM : ∀ ℓ ∈ PM, ℓ ∣ M ∧ ℓ ∈ P) (hPq : ∀ ℓ ∈ Pq, ℓ ∣ q ∧ Nat.Coprime ℓ p ∧ ℓ ∈ P) :
    Cover (residueGraph p q M s₀ nA PM Pq) (fun _ => affStep p q ν) (affAdm p q ν s₀ P)
      (fun r => {z | ((⌊z⌋ : ℤ) : ZMod M) = r}) := by
  refine ⟨fun r t z hz ⟨hc, hav, hav'⟩ => ⟨((⌊affStep p q ν z⌋ : ℤ) : ZMod M), ?_, rfl⟩⟩
  have hsub : ∀ x, Avoid P x → Avoid PM x := fun x hx ℓ hℓ => hx ℓ (hPM ℓ hℓ).2
  have hPM' : ∀ ℓ ∈ PM, ℓ ∣ M := fun ℓ hℓ => (hPM ℓ hℓ).1
  simp only [Set.mem_ofPred_eq] at hz
  subst hz
  refine adj_residueGraph.2 ⟨resOK_intCast hPM' (hsub _ hav), ?_, ?_,
    resOK_intCast hPM' (hsub _ hav')⟩
  · intro ℓ hℓ hdvd
    obtain ⟨hlq, hlp, hlP⟩ := hPq ℓ hℓ
    rw [← hc] at hdvd
    have hqx : (ℓ : ℤ) ∣ (q : ℤ) * ⌊affStep p q ν z⌋ :=
      dvd_mul_of_dvd_left (by exact_mod_cast hlq) _
    have hpx : (ℓ : ℤ) ∣ (p : ℤ) * ⌊z⌋ := by
      have e : (p : ℤ) * ⌊z⌋ = q * ⌊affStep p q ν z⌋ - carry p q ν z := by simp only [carry]; ring
      rw [e]
      exact dvd_sub hqx hdvd
    exact hav ℓ hlP ((Nat.isCoprime_iff_coprime.2 hlp).dvd_of_dvd_mul_left hpx)
  · have h := q_mul_floor_affStep (p := p) (q := q) (ν := ν) z
    rw [hc] at h
    have := congrArg (fun x : ℤ => (x : ZMod M)) h
    push_cast at this ⊢
    exact this

/-! ### Block graphs and the fractional system -/

/-- The fractional step `y ↦ (p y − (p − q)ν − s)/q`. -/
noncomputable def fracStep (p q : ℕ) (ν : ℝ) (s : ℤ) (y : ℝ) : ℝ :=
  (p * y - ((p : ℝ) - q) * ν - s) / q

/-- Admissibility in the fractional system: the step stays in `[0, 1)`. -/
def fracAdm (p q : ℕ) (ν : ℝ) (s₀ : ℤ) {nA : ℕ} (y : ℝ) (t : Fin nA) : Prop :=
  0 ≤ fracStep p q ν (s₀ + t) y ∧ fracStep p q ν (s₀ + t) y < 1

/-- The arc condition of a block graph: the image of `[I.1, I.2)` under the letter `s` meets
`[J.1, J.2)`. -/
def BlockArc (p q : ℕ) (ν : ℝ) (I J : ℚ × ℚ) (s : ℤ) : Prop :=
  (q : ℝ) * J.1 < p * I.2 - ((p : ℝ) - q) * ν - s ∧ (p : ℝ) * I.1 - ((p : ℝ) - q) * ν - s < q * J.2

/-- The interval `[I.1, I.2)` as a set of reals. -/
def ival (I : ℚ × ℚ) : Set ℝ := {y | (I.1 : ℝ) ≤ y ∧ y < I.2}

/-- **The block graph** of a family of rational intervals. -/
def blockGraph (p q : ℕ) (ν : ℚ) (s₀ : ℤ) (nA : ℕ) {n : ℕ} (I : Fin n → ℚ × ℚ) :
    CarryGraph (Fin n) (Fin nA) :=
  ⟨fun i t => Finset.univ.filter fun j =>
    (q : ℚ) * (I j).1 < p * (I i).2 - ((p : ℚ) - q) * ν - (s₀ + t : ℤ) ∧
      (p : ℚ) * (I i).1 - ((p : ℚ) - q) * ν - (s₀ + t : ℤ) < q * (I j).2⟩

variable {s₀ : ℤ} {nA n : ℕ}

@[category API, AMS 11 05, group "carry_affine"]
theorem adj_blockGraph {νq : ℚ} {I : Fin n → ℚ × ℚ} {i j : Fin n} {t : Fin nA} :
    (blockGraph p q νq s₀ nA I).Adj i t j ↔ BlockArc p q νq (I i) (I j) (s₀ + t) := by
  simp only [blockGraph, Adj, Finset.mem_filter, Finset.mem_univ, true_and, BlockArc]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor
  · exact_mod_cast h1
  · exact_mod_cast h2
  · exact_mod_cast h1
  · exact_mod_cast h2

/-- **Block cover of the fractional system**: any graph containing the block arcs covers the
fractional system, provided the intervals cover `[0, 1)`. -/
@[category textbook, AMS 11 37 05, group "carry_affine"]
theorem cover_frac_of_blockArc (hq : q ≠ 0) (hp : 0 < p) {X : CarryGraph (Fin n) (Fin nA)}
    {I : Fin n → ℚ × ℚ}
    (hX : ∀ i (t : Fin nA) j, BlockArc p q ν (I i) (I j) (s₀ + t) → X.Adj i t j)
    (hI : ∀ y : ℝ, 0 ≤ y → y < 1 → ∃ j, y ∈ ival (I j)) :
    Cover X (fun t => fracStep p q ν (s₀ + t)) (fracAdm p q ν s₀) (fun i => ival (I i)) := by
  refine ⟨fun i t y hy ⟨h0, h1⟩ => ?_⟩
  obtain ⟨j, hj1, hj2⟩ := hI _ h0 h1
  refine ⟨j, hX i t j ⟨?_, ?_⟩, hj1, hj2⟩
  all_goals
    have hq' : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
    have hp' : (0 : ℝ) < p := by exact_mod_cast hp
    have hfs : (q : ℝ) * fracStep p q ν (s₀ + t) y
        = p * y - ((p : ℝ) - q) * ν - ((s₀ + t : ℤ) : ℝ) := by
      simp only [fracStep]; field_simp
    obtain ⟨hy1, hy2⟩ := hy
    have e1 := mul_le_mul_of_nonneg_left hj1 hq'.le
    have e2 := mul_lt_mul_of_pos_left hj2 hq'
    have e3 := mul_le_mul_of_nonneg_left hy1 hp'.le
    have e4 := mul_lt_mul_of_pos_left hy2 hp'
  · linarith
  · linarith

/-- The fractional parts of the affine system follow the fractional system. -/
@[category API, AMS 11 37, group "carry_affine"]
theorem fract_semiconj (hq : q ≠ 0) {P : List ℕ} (z : ℝ) (t : Fin nA)
    (h : affAdm p q ν s₀ P z t) :
    fracAdm p q ν s₀ (Int.fract z) t ∧
      Int.fract (affStep p q ν z) = fracStep p q ν (s₀ + t) (Int.fract z) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have he : Int.fract (affStep p q ν z) = fracStep p q ν (s₀ + t) (Int.fract z) := by
    have := fract_affStep (p := p) (ν := ν) hq z
    rw [h.1] at this
    simp only [fracStep]
    field_simp
    push_cast at this ⊢
    linarith
  exact ⟨⟨he ▸ Int.fract_nonneg _, he ▸ Int.fract_lt_one _⟩, he⟩

/-- **The block cover**: a block graph whose intervals cover `[0, 1)` covers the affine system
through the fractional parts. -/
@[category textbook, AMS 11 37 05, group "carry_affine"]
theorem cover_blockGraph (hq : q ≠ 0) (hp : 0 < p) {νq : ℚ} {P : List ℕ} {I : Fin n → ℚ × ℚ}
    (hI : ∀ y : ℝ, 0 ≤ y → y < 1 → ∃ j, y ∈ ival (I j)) :
    Cover (blockGraph p q νq s₀ nA I) (fun _ => affStep p q νq) (affAdm p q νq s₀ P)
      (fun i => Int.fract ⁻¹' ival (I i)) :=
  (cover_frac_of_blockArc hq hp (fun _ _ _ h => adj_blockGraph.2 h) hI).comap Int.fract
    fun t z h => fract_semiconj hq z t h

/-! ### Cells -/

/-- The `D` cells `[c/D, (c+1)/D)`. -/
def cells (D : ℕ) (c : Fin D) : ℚ × ℚ := ((c : ℚ) / D, ((c : ℚ) + 1) / D)

/-- **The cell graph**: the block graph of the `D` cells. -/
def cellGraph (p q : ℕ) (ν : ℚ) (s₀ : ℤ) (nA D : ℕ) : CarryGraph (Fin D) (Fin nA) :=
  blockGraph p q ν s₀ nA (cells D)

@[category API, AMS 11, group "carry_affine"]
theorem exists_cell {D : ℕ} (hD : 0 < D) (y : ℝ) (h0 : 0 ≤ y) (h1 : y < 1) :
    ∃ c : Fin D, y ∈ ival (cells D c) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hfl := Nat.floor_le (mul_nonneg hD'.le h0)
  have hlt := Nat.lt_floor_add_one ((D : ℝ) * y)
  have hc : ⌊(D : ℝ) * y⌋₊ < D := by
    have : (D : ℝ) * y < D := by nlinarith
    exact_mod_cast (Nat.floor_lt (mul_nonneg hD'.le h0)).2 this
  refine ⟨⟨_, hc⟩, ?_, ?_⟩
  · simp only [cells]; push_cast
    rw [div_le_iff₀ hD']; linarith
  · simp only [cells]; push_cast
    rw [lt_div_iff₀ hD']; linarith

/-- **The cell cover**. -/
@[category textbook, AMS 11 37 05, group "carry_affine"]
theorem cover_cellGraph (hq : q ≠ 0) (hp : 0 < p) {νq : ℚ} {P : List ℕ} {D : ℕ} (hD : 0 < D) :
    Cover (cellGraph p q νq s₀ nA D) (fun _ => affStep p q νq) (affAdm p q νq s₀ P)
      (fun c => Int.fract ⁻¹' ival (cells D c)) :=
  cover_blockGraph hq hp fun y h0 h1 => exists_cell hD y h0 h1

/-! ### The affine graph -/

/-- **The affine carry graph**: the label product of the residue and the cell graph. -/
def affine (p q : ℕ) (ν : ℚ) (s₀ : ℤ) (nA M D : ℕ) [NeZero M] (PM Pq : List ℕ) :
    CarryGraph (ZMod M × Fin D) (Fin nA) :=
  (residueGraph p q M s₀ nA PM Pq).labelProduct (cellGraph p q ν s₀ nA D)

/-- **The affine cover** (residue × cell). -/
@[category textbook, AMS 11 37 05, group "carry_affine"]
theorem cover_affine (hq : q ≠ 0) (hp : 0 < p) {νq : ℚ} {M D : ℕ} [NeZero M] (hD : 0 < D)
    {PM Pq P : List ℕ} (hPM : ∀ ℓ ∈ PM, ℓ ∣ M ∧ ℓ ∈ P)
    (hPq : ∀ ℓ ∈ Pq, ℓ ∣ q ∧ Nat.Coprime ℓ p ∧ ℓ ∈ P) :
    Cover (affine p q νq s₀ nA M D PM Pq) (fun _ => affStep p q νq) (affAdm p q νq s₀ P)
      (fun v => {z | ((⌊z⌋ : ℤ) : ZMod M) = v.1} ∩ Int.fract ⁻¹' ival (cells D v.2)) :=
  (cover_residueGraph hPM hPq).labelProduct (cover_cellGraph hq hp hD)

/-- Every real lies in some `ρ` of the affine cover. -/
@[category API, AMS 11, group "carry_affine"]
theorem affine_rho_cover {M D : ℕ} [NeZero M] (hD : 0 < D) (z : ℝ) :
    ∃ v : ZMod M × Fin D, z ∈ {z | ((⌊z⌋ : ℤ) : ZMod M) = v.1} ∩ Int.fract ⁻¹' ival (cells D v.2) :=
  let ⟨c, hc⟩ := exists_cell hD _ (Int.fract_nonneg z) (Int.fract_lt_one z)
  ⟨(_, c), rfl, hc⟩

/-! ### Realisability: Markov block graphs -/

/-- **Markov block graphs realise their words** in the fractional system: if every arc
`i →t j` has `I j` inside the image of `I i`, every word from `i` is the itinerary of a point of
`I i` (the set of such points contains a nonempty interval, by nested intervals). -/
@[category textbook, AMS 11 37 05, ref "LM95", group "carry_affine"]
theorem realizes_blockGraph (hq : q ≠ 0) (hp : 0 < p) {νq : ℚ} {I : Fin n → ℚ × ℚ}
    (hI : ∀ i, (I i).1 < (I i).2) (hI01 : ∀ i, 0 ≤ (I i).1 ∧ (I i).2 ≤ 1)
    (hM : ∀ i (t : Fin nA) j, (blockGraph p q νq s₀ nA I).Adj i t j →
      (p : ℝ) * (I i).1 - ((p : ℝ) - q) * νq - (s₀ + t : ℤ) ≤ q * (I j).1 ∧
        (q : ℝ) * (I j).2 ≤ p * (I i).2 - ((p : ℝ) - q) * νq - (s₀ + t : ℤ)) :
    Realizes (blockGraph p q νq s₀ nA I) (fun t => fracStep p q νq (s₀ + t))
      (fracAdm p q νq s₀) (fun i => ival (I i)) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have key : ∀ (w : List (Fin nA)) i, (blockGraph p q νq s₀ nA I).IsWord i w →
      ∃ α β : ℝ, α < β ∧ ((I i).1 : ℝ) ≤ α ∧ β ≤ (I i).2 ∧
        ∀ y, α ≤ y → y < β →
          Follows (fun t : Fin nA => fracStep p q νq (s₀ + t)) (fracAdm p q νq s₀) y w := by
    intro w
    induction w with
    | nil =>
      intro i _
      exact ⟨(I i).1, (I i).2, by exact_mod_cast hI i, le_rfl, le_rfl, fun _ _ _ => trivial⟩
    | cons t w ih =>
      intro i hw
      obtain ⟨j, hj, hwj⟩ := isWord_cons.1 hw
      obtain ⟨α, β, hαβ, hα, hβ, hf⟩ := ih j hwj
      obtain ⟨hM1, hM2⟩ := hM i t j hj
      have hj0 : (0 : ℝ) ≤ (I j).1 := by exact_mod_cast (hI01 j).1
      have hj1 : ((I j).2 : ℝ) ≤ 1 := by exact_mod_cast (hI01 j).2
      set K : ℝ := ((p : ℝ) - q) * νq + ((s₀ + t : ℤ) : ℝ)
      refine ⟨(q * α + K) / p, (q * β + K) / p, ?_, ?_, ?_, fun y hy1 hy2 => ?_⟩
      · exact div_lt_div_of_pos_right (by nlinarith) hp'
      · rw [le_div_iff₀ hp']; nlinarith
      · rw [div_le_iff₀ hp']; nlinarith
      · rw [div_le_iff₀ hp'] at hy1
        rw [lt_div_iff₀ hp'] at hy2
        have hfs : (q : ℝ) * fracStep p q νq (s₀ + t) y = p * y - K := by
          simp only [fracStep, K]; field_simp; ring
        have h1 : α ≤ fracStep p q νq (s₀ + t) y := by nlinarith
        have h2 : fracStep p q νq (s₀ + t) y < β := by nlinarith
        exact ⟨⟨by linarith, by linarith⟩, hf _ h1 h2⟩
  intro i w hw
  obtain ⟨α, β, hαβ, hα, hβ, hf⟩ := key w i hw
  exact ⟨α, ⟨hα, hαβ.trans_le hβ⟩, hf α le_rfl hαβ⟩

/-! ### Realisability forever

Nested half-open intervals can have empty intersection, and Markov block graphs need not realise
their infinite paths: for `y ↦ 2y − s` on the single block `[0, 1)` the constant path of the
letter `1` would need the fixed point `1` (`not_realizesInf_doubling`).  A strict Markov condition
at the right endpoints is enough (`realizesInf_blockGraph`): then the nested *closed* sets of
points following the path have a common point (compactness), and strictness keeps its orbit off
every right endpoint. -/

theorem continuous_orbit_fracStep (νq : ℚ) (ℓ : ℕ → Fin nA) :
    ∀ k, Continuous fun y : ℝ => orbit (fun t : Fin nA => fracStep p q νq (s₀ + t)) y ℓ k
  | 0 => continuous_id
  | k + 1 => by
    have h := continuous_orbit_fracStep νq ℓ k
    simp only [orbit, fracStep]
    fun_prop

/-- **Strictly Markov block graphs realise their infinite paths**: if every arc `i →t j` has
`I j` inside the image of `I i`, with the right endpoint of `I j` strictly inside, every infinite
path of the block graph is the itinerary of a point of its first interval, admissible forever. -/
@[category textbook, AMS 11 37 05, ref "LM95", group "carry_affine"]
theorem realizesInf_blockGraph (hq : q ≠ 0) (hp : 0 < p) {νq : ℚ} {I : Fin n → ℚ × ℚ}
    (hI : ∀ i, (I i).1 < (I i).2) (hI01 : ∀ i, 0 ≤ (I i).1 ∧ (I i).2 ≤ 1)
    (hM : ∀ i (t : Fin nA) j, (blockGraph p q νq s₀ nA I).Adj i t j →
      (p : ℝ) * (I i).1 - ((p : ℝ) - q) * νq - (s₀ + t : ℤ) ≤ q * (I j).1 ∧
        (q : ℝ) * (I j).2 < p * (I i).2 - ((p : ℝ) - q) * νq - (s₀ + t : ℤ)) :
    RealizesInf (blockGraph p q νq s₀ nA I) (fun t => fracStep p q νq (s₀ + t))
      (fracAdm p q νq s₀) (fun i => ival (I i)) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  set f : Fin nA → ℝ → ℝ := fun t => fracStep p q νq (s₀ + t) with hf
  have hfs : ∀ (t : Fin nA) y, (q : ℝ) * f t y = p * y - ((p : ℝ) - q) * νq - (s₀ + t : ℤ) := by
    intro t y
    simp only [hf, fracStep]
    field_simp
  -- the closed set of points whose first `m + 1` positions follow the path
  let T : (ℕ → Fin n) → (ℕ → Fin nA) → ℕ → Set ℝ := fun s ℓ m =>
    {y | ∀ k ≤ m, ((I (s k)).1 : ℝ) ≤ orbit f y ℓ k ∧ orbit f y ℓ k ≤ (I (s k)).2}
  have hne : ∀ m (s : ℕ → Fin n) (ℓ : ℕ → Fin nA), (blockGraph p q νq s₀ nA I).IsIPath s ℓ →
      (T s ℓ m).Nonempty := by
    intro m
    induction m with
    | zero =>
      intro s ℓ _
      exact ⟨(I (s 0)).1, fun k hk => by
        obtain rfl : k = 0 := by omega
        simp only [orbit]
        exact ⟨le_rfl, by exact_mod_cast (hI (s 0)).le⟩⟩
    | succ m ih =>
      intro s ℓ hs
      obtain ⟨z, hz⟩ := ih (fun k => s (k + 1)) (fun k => ℓ (k + 1)) fun k => hs (k + 1)
      obtain ⟨hz1, hz2⟩ := hz 0 (Nat.zero_le _)
      simp only [orbit] at hz1 hz2
      obtain ⟨hM1, hM2⟩ := hM _ _ _ (hs 0)
      set K : ℝ := ((p : ℝ) - q) * νq + ((s₀ + ℓ 0 : ℤ) : ℝ)
      set y : ℝ := (q * z + K) / p
      have hy : f (ℓ 0) y = z := by
        simp only [hf, fracStep, y, K]; field_simp; push_cast; ring
      refine ⟨y, fun k hk => ?_⟩
      cases k with
      | zero =>
        simp only [orbit]
        have e1 := mul_le_mul_of_nonneg_left hz1 hq'.le
        have e2 := mul_le_mul_of_nonneg_left hz2 hq'.le
        simp only [y, K]
        push_cast at hM1 hM2 ⊢
        constructor
        · rw [le_div_iff₀ hp']; linarith
        · rw [div_le_iff₀ hp']; linarith
      | succ k =>
        rw [orbit_succ', hy]
        exact hz k (by omega)
  intro s ℓ hs
  have hcl : ∀ m, IsClosed (T s ℓ m) := by
    intro m
    simp only [T, Set.ofPred_forall]
    refine isClosed_biInter fun k _ => IsClosed.inter ?_ ?_
    · exact isClosed_le continuous_const (continuous_orbit_fracStep νq ℓ k)
    · exact isClosed_le (continuous_orbit_fracStep νq ℓ k) continuous_const
  have hcpt : IsCompact (T s ℓ 0) := by
    refine (isCompact_Icc (a := ((I (s 0)).1 : ℝ)) (b := (I (s 0)).2)).of_isClosed_subset (hcl 0)
      fun y hy => ?_
    have := hy 0 le_rfl
    simpa [orbit] using this
  obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed (T s ℓ)
    (fun m y hy k hk => hy k (by omega)) (fun m => hne m s ℓ hs) hcpt hcl
  simp only [Set.mem_iInter] at hy
  have hin : ∀ k, ((I (s k)).1 : ℝ) ≤ orbit f y ℓ k ∧ orbit f y ℓ k ≤ (I (s k)).2 :=
    fun k => hy k k le_rfl
  have hlt : ∀ k, orbit f y ℓ k < (I (s k)).2 := by
    intro k
    have h1 := (hin (k + 1)).2
    have h2 := (hM _ _ _ (hs k)).2
    have h3 := hfs (ℓ k) (orbit f y ℓ k)
    have h4 : orbit f y ℓ (k + 1) = f (ℓ k) (orbit f y ℓ k) := rfl
    rw [← h4] at h3
    have : (p : ℝ) * orbit f y ℓ k < p * (I (s k)).2 := by nlinarith
    exact lt_of_mul_lt_mul_left this hp'.le
  refine ⟨y, ⟨(hin 0).1, hlt 0⟩, fun k => ?_⟩
  have h4 : orbit f y ℓ (k + 1) = f (ℓ k) (orbit f y ℓ k) := rfl
  refine ⟨?_, ?_⟩
  · show 0 ≤ orbit f y ℓ (k + 1)
    exact le_trans (by exact_mod_cast (hI01 _).1) (hin (k + 1)).1
  · show orbit f y ℓ (k + 1) < 1
    exact lt_of_lt_of_le (hlt (k + 1)) (by exact_mod_cast (hI01 _).2)

/-- **A Markov block graph that does not realise its infinite paths**: `y ↦ 2y − s` on the single
block `[0, 1)`, letters `0, 1`.  Every arc is Markov (with equality at the right endpoint for the
letter `1`), but the constant path of the letter `1` would need the fixed point `1`. -/
@[category test, AMS 11 37 05, group "carry_affine"]
theorem not_realizesInf_doubling :
    ¬ RealizesInf (blockGraph 2 1 (0 : ℚ) 0 2 fun _ : Fin 1 => ((0 : ℚ), (1 : ℚ)))
      (fun t => fracStep 2 1 ((0 : ℚ) : ℝ) (0 + t)) (fracAdm 2 1 ((0 : ℚ) : ℝ) 0)
      (fun i => ival ((fun _ : Fin 1 => ((0 : ℚ), (1 : ℚ))) i)) := by
  intro h
  have hpath : (blockGraph 2 1 (0 : ℚ) 0 2 fun _ : Fin 1 => ((0 : ℚ), (1 : ℚ))).IsIPath
      (fun _ => 0) (fun _ => 1) := fun _ => adj_blockGraph.2 (by
        simp only [BlockArc]; norm_num)
  obtain ⟨x, -, hx⟩ := h _ _ hpath
  set o := orbit (fun t : Fin 2 => fracStep 2 1 ((0 : ℚ) : ℝ) (0 + t)) x (fun _ => 1)
  have hstep : ∀ k, o (k + 1) = 2 * o k - 1 := fun k => by
    show fracStep 2 1 ((0 : ℚ) : ℝ) (0 + ((1 : Fin 2) : ℤ)) (o k) = _
    simp [fracStep]
  have hgap : ∀ k, 1 - o k = 2 ^ k * (1 - x) := by
    intro k
    induction k with
    | zero => simp [o, orbit]
    | succ k ih => rw [hstep, pow_succ]; linarith
  have h0 : ∀ k, 0 ≤ o (k + 1) := fun k => (hx k).1
  have hx1 : x < 1 := by
    have := (hx 0).2
    have e : o 1 = 2 * x - 1 := by rw [hstep]; rfl
    show x < 1
    have : o 1 < 1 := this
    linarith
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / (1 - x)) (by norm_num : (1 : ℝ) < 2)
  have := h0 k
  have hg := hgap (k + 1)
  have hpos : 0 < 1 - x := by linarith
  rw [div_lt_iff₀ hpos] at hk
  rw [pow_succ] at hg
  nlinarith

/-! ### Refinement -/

/-- **Refinement**: if each interval of `I` lies in the interval `J (π i)`, `π` is a
homomorphism from the fine block graph to the coarse one. -/
def blockGraph_hom (hpq : q ≤ p) {νq : ℚ} {m : ℕ} {I : Fin n → ℚ × ℚ} {J : Fin m → ℚ × ℚ}
    (π : Fin n → Fin m) (hπ : ∀ i, (J (π i)).1 ≤ (I i).1 ∧ (I i).2 ≤ (J (π i)).2) :
    Hom (blockGraph p q νq s₀ nA I) (blockGraph p q νq s₀ nA J) :=
  ⟨π, fun {i t j} h => by
    have hpq' : (q : ℚ) ≤ p := by exact_mod_cast hpq
    simp only [blockGraph, Adj, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
    obtain ⟨h1, h2⟩ := h
    have hq0 : (0 : ℚ) ≤ q := Nat.cast_nonneg q
    have hp0 : (0 : ℚ) ≤ p := Nat.cast_nonneg p
    obtain ⟨hi1, hi2⟩ := hπ i
    obtain ⟨hj1, hj2⟩ := hπ j
    constructor <;> nlinarith⟩

/-- **Cell refinement**: the cell graph with `k D` cells maps onto the one with `D` cells. -/
def cellGraph_hom (hpq : q ≤ p) {νq : ℚ} {k D : ℕ} (hk : 0 < k) (hD : 0 < D) :
    Hom (cellGraph p q νq s₀ nA (k * D)) (cellGraph p q νq s₀ nA D) :=
  blockGraph_hom hpq (fun c => ⟨c / k, Nat.div_lt_of_lt_mul c.2⟩)
    fun c => by
      have hk' : (0 : ℚ) < k := by exact_mod_cast hk
      have hD' : (0 : ℚ) < D := by exact_mod_cast hD
      have h1 : ((c / k : ℕ) : ℚ) * k ≤ c := by exact_mod_cast Nat.div_mul_le_self c k
      have h2 : (c : ℚ) + 1 ≤ ((c / k : ℕ) + 1 : ℚ) * k := by
        have : (c : ℕ) + 1 ≤ (c / k + 1) * k :=
          Nat.lt_mul_of_div_lt (a := (c : ℕ)) (Nat.lt_succ_self _) hk
        exact_mod_cast this
      simp only [cells, Nat.cast_mul]
      constructor
      · rw [div_le_div_iff₀ hD' (by positivity)]; nlinarith
      · rw [div_le_div_iff₀ (by positivity) hD']; nlinarith

/-! ### Dimension of the avoiders -/

section dimension

variable {P : List ℕ}

/-- Two runs that read the same word from the same integer part keep equal integer parts. -/
@[category API, AMS 11 37, group "carry_affine"]
theorem floor_run_eq (hq : q ≠ 0) :
    ∀ {x y : ℝ} {w : List (Fin nA)},
      Follows (fun _ => affStep p q ν) (affAdm p q ν s₀ P) x w →
      Follows (fun _ => affStep p q ν) (affAdm p q ν s₀ P) y w → ⌊x⌋ = ⌊y⌋ →
      ⌊run (fun _ => affStep p q ν) x w⌋ = ⌊run (fun _ => affStep p q ν) y w⌋
  | _, _, [], _, _, h => h
  | x, y, t :: w, ⟨hx, hxw⟩, ⟨hy, hyw⟩, h => by
    refine floor_run_eq hq (x := affStep p q ν x) (y := affStep p q ν y) hxw hyw ?_
    have h1 := q_mul_floor_affStep (p := p) (q := q) (ν := ν) x
    have h2 := q_mul_floor_affStep (p := p) (q := q) (ν := ν) y
    rw [hx.1, h] at h1
    rw [hy.1] at h2
    have hq' : (q : ℤ) ≠ 0 := by exact_mod_cast hq
    exact mul_left_cancel₀ hq' (h1.trans h2.symm)

variable {V : Type*} [Fintype V] {X : CarryGraph V (Fin nA)} {ρ : V → Set ℝ}

/-- The avoiders with integer part `x₀` that survive arbitrarily long. -/
def survivors (p q : ℕ) (ν : ℝ) (s₀ : ℤ) (nA : ℕ) (P : List ℕ) (x₀ : ℤ) : Set ℝ :=
  {z | ⌊z⌋ = x₀ ∧ ∀ n, ∃ w : List (Fin nA), w.length = n ∧
    Follows (fun _ => affStep p q ν) (affAdm p q ν s₀ P) z w}

/-- The survivors with one integer part have dimension at most `entropy X / log (p/q)`. -/
@[category research solved, AMS 11 28 37, ref "DN05", group "carry_affine"]
theorem dimH_survivors_le (hq : 0 < q) (hpq : q < p)
    (h : Cover X (fun _ => affStep p q ν) (affAdm p q ν s₀ P) ρ) (hρ : ∀ z, ∃ v, z ∈ ρ v)
    (x₀ : ℤ) :
    dimH (survivors p q ν s₀ nA P x₀)
      ≤ (X.entropy / ((Real.log ((p : ℝ) / q) : ℝ) : EReal)).toENNReal := by
  rcases (survivors p q ν s₀ nA P x₀).eq_empty_or_nonempty with he | hne
  · rw [he, dimH_empty]; exact zero_le
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hpq' : (q : ℝ) < p := by exact_mod_cast hpq
  have hp' : (0 : ℝ) < p := hq'.trans hpq'
  set r : ℝ≥0 := ⟨(q : ℝ) / p, by positivity⟩ with hr
  have hrR : (r : ℝ) = (q : ℝ) / p := rfl
  have hr0 : 0 < r := by rw [← NNReal.coe_pos, hrR]; positivity
  have hr1 : r < 1 := by rw [← NNReal.coe_lt_one, hrR, div_lt_one hp']; exact hpq'
  have hexp : ∀ (t : Fin nA) x y, affAdm p q ν s₀ P x t → affAdm p q ν s₀ P y t →
      edist x y ≤ r * edist (affStep p q ν x) (affStep p q ν y) := by
    intro t x y _ _
    rw [edist_dist, edist_dist, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity),
      hrR]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [Real.dist_eq, Real.dist_eq, show affStep p q ν x - affStep p q ν y = p / q * (x - y) by
      simp only [affStep]; ring, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < p / q)]
    field_simp
  have hU := h.upperBoxDim_le_of_expanding (K := survivors p q ν s₀ nA P x₀)
    (fun z hz => ⟨hρ z, hz.2⟩) hr0 hr1 one_pos hexp
    (fun v w x y hx hy _ _ hxf hyf => by
      have := floor_run_eq hq.ne' hxf hyf (hx.1.trans hy.1.symm)
      rw [edist_dist, ENNReal.coe_one, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by
        rw [Real.dist_eq]; exact (Int.abs_sub_lt_one_of_floor_eq_floor this).le))
  have hlog : Real.log (r : ℝ)⁻¹ = Real.log ((p : ℝ) / q) := by rw [hrR, inv_div]
  rw [hlog] at hU
  have h1 := (dimH_le_upperBoxDim hne).trans hU
  rw [← EReal.toENNReal_coe (x := dimH _)]
  exact EReal.toENNReal_le_toENNReal h1

/-- **Dimension of the avoiders** (generic form of `DubC2.Gen.dimH_eventually_avoids_le`): for
every finite carry graph covering the affine system, the real `ξ` with `⌊ξ(p/q)ⁿ + ν⌋`
eventually avoiding `P` form a set of Hausdorff dimension at most `entropy X / log (p/q)`
(read as `0` when negative).  The alphabet must contain the carry window. -/
@[category research solved, AMS 11 28 37, ref "DN05", group "carry_affine"]
theorem dimH_avoiders_le (hq : 0 < q) (hpq : q < p)
    (h : Cover X (fun _ => affStep p q ν) (affAdm p q ν s₀ P) ρ) (hρ : ∀ z, ∃ v, z ∈ ρ v)
    (hwin : ∀ z, s₀ ≤ carry p q ν z ∧ carry p q ν z < s₀ + nA) :
    dimH {ξ : ℝ | ∀ᶠ n in atTop, Avoid P ⌊ξ * ((p : ℝ) / q) ^ n + ν⌋}
      ≤ (X.entropy / ((Real.log ((p : ℝ) / q) : ℝ) : EReal)).toENNReal := by
  have hq0 : q ≠ 0 := hq.ne'
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hp' : (0 : ℝ) < p := hq'.trans (by exact_mod_cast hpq)
  set c : ℝ := (p : ℝ) / q
  have hc : 0 < c := by positivity
  let zs : ℝ → ℕ → ℝ := fun ξ n => ξ * c ^ n + ν
  let g : ℕ → ℝ → ℝ := fun N z => (z - ν) * c⁻¹ ^ N
  have hsub : {ξ : ℝ | ∀ᶠ n in atTop, Avoid P ⌊ξ * c ^ n + ν⌋}
      ⊆ ⋃ N : ℕ, ⋃ x₀ : ℤ, g N '' survivors p q ν s₀ nA P x₀ := by
    intro ξ hξ
    obtain ⟨N, hN⟩ := eventually_atTop.1 hξ
    let tl : ℕ → Fin nA := fun m =>
      ⟨(carry p q ν (zs ξ (N + m)) - s₀).toNat, by
        have := hwin (zs ξ (N + m)); omega⟩
    have htl : ∀ m, carry p q ν (zs ξ (N + m)) = s₀ + (tl m : ℕ) := fun m => by
      have := hwin (zs ξ (N + m)); simp only [tl]; omega
    have horb : ∀ m, orbit (fun _ => affStep p q ν) (zs ξ N) tl m = zs ξ (N + m) := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => rw [orbit, ih]; exact affStep_orbit ξ (N + m)
    have hadm : AdmForever (fun _ => affStep p q ν) (affAdm p q ν s₀ P) (zs ξ N) tl := by
      intro m
      rw [horb]
      refine ⟨by rw [htl], hN _ (by omega), ?_⟩
      rw [affStep_orbit]
      exact hN _ (by omega)
    simp only [Set.mem_iUnion, Set.mem_image]
    refine ⟨N, ⌊zs ξ N⌋, zs ξ N, ⟨rfl, fun n => ⟨pre tl n, length_pre tl n, hadm.follows n⟩⟩, ?_⟩
    simp only [g, zs]
    rw [add_sub_cancel_right, mul_assoc, ← mul_pow, mul_inv_cancel₀ hc.ne', one_pow, mul_one]
  have hlip : ∀ N, LipschitzWith ⟨c⁻¹ ^ N, by positivity⟩ (g N) := fun N =>
    LipschitzWith.of_dist_le_mul fun x y => by
      simp only [g, Real.dist_eq]
      rw [← sub_mul, sub_sub_sub_cancel_right, abs_mul, abs_of_pos (by positivity : 0 < c⁻¹ ^ N),
        mul_comm]
      exact le_of_eq rfl
  refine (dimH_mono hsub).trans ?_
  rw [dimH_iUnion]
  refine iSup_le fun N => ?_
  rw [dimH_iUnion]
  refine iSup_le fun x₀ => ?_
  exact ((hlip N).dimH_image_le _).trans (dimH_survivors_le hq hpq h hρ x₀)

end dimension

end CarryGraph
