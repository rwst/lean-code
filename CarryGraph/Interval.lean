/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CarryGraph.Affine

/-!
# Parameter intervals: hull graphs

The arc condition of a block graph (`BlockArc`) is linear in the shift `ν`: with
`α = p bᵢ − s − q aⱼ` and `β = p aᵢ − s − q bⱼ` it reads `β < (p − q)ν < α`.  For a parameter
interval `ν ∈ [ν₀, ν₁]` the **hull** `blockHull p q ν₀ ν₁ s₀ I` keeps the arcs present for some
`ν` in the interval.  It is decided by three rational comparisons.

* `cover_blockHull`, `cover_affineHull`: the hull covers the affine system for **every real**
  `ν ∈ [ν₀, ν₁]`, so one certificate on the hull settles a whole interval of real shifts (the
  `DubC2/NuAtlas` mechanism, `Params.hullOK`);
* `adj_blockHull_iff`: the hull is exactly the union of the rational block graphs over the
  interval (for `q < p`);
* `blockHull_mono`: a smaller interval gives a smaller hull; `residueGraph_hom`: a larger
  divisor set gives a smaller residue graph.  Both are homomorphisms, so certificates
  (`AllPer`, zero entropy, empty core) pass from the coarse graph to the fine one;
* `carry_window_of_interval`: one letter window serves the whole interval;
* `dimH_avoiders_le_hull`: the dimension bound of `CarryGraph/Affine.lean`, uniform in
  `ν ∈ [ν₀, ν₁]`.
-/

open Filter ENNReal ExpGrowth Metric

namespace CarryGraph

variable {p q : ℕ} {s₀ : ℤ} {nA n : ℕ}

/-- **The hull** of the block graphs over `ν ∈ [ν₀, ν₁]`. -/
def blockHull (p q : ℕ) (ν₀ ν₁ : ℚ) (s₀ : ℤ) (nA : ℕ) {n : ℕ} (I : Fin n → ℚ × ℚ) :
    CarryGraph (Fin n) (Fin nA) :=
  ⟨fun i t => Finset.univ.filter fun j =>
    ((p : ℚ) - q) * ν₀ < p * (I i).2 - (s₀ + t : ℤ) - q * (I j).1 ∧
      (p : ℚ) * (I i).1 - (s₀ + t : ℤ) - q * (I j).2 < ((p : ℚ) - q) * ν₁ ∧
      (p : ℚ) * (I i).1 - (s₀ + t : ℤ) - q * (I j).2 < p * (I i).2 - (s₀ + t : ℤ) - q * (I j).1⟩

@[category API, AMS 11 05, group "carry_interval"]
theorem adj_blockHull {ν₀ ν₁ : ℚ} {I : Fin n → ℚ × ℚ} {i j : Fin n} {t : Fin nA} :
    (blockHull p q ν₀ ν₁ s₀ nA I).Adj i t j ↔
      ((p : ℚ) - q) * ν₀ < p * (I i).2 - (s₀ + t : ℤ) - q * (I j).1 ∧
      (p : ℚ) * (I i).1 - (s₀ + t : ℤ) - q * (I j).2 < ((p : ℚ) - q) * ν₁ ∧
      (p : ℚ) * (I i).1 - (s₀ + t : ℤ) - q * (I j).2
        < p * (I i).2 - (s₀ + t : ℤ) - q * (I j).1 := by
  simp [blockHull, Adj]

/-- A block arc at a real `ν ∈ [ν₀, ν₁]` is a hull arc. -/
@[category API, AMS 11 05, group "carry_interval"]
theorem blockArc_hull (hpq : q ≤ p) {ν : ℝ} {ν₀ ν₁ : ℚ} (h₀ : (ν₀ : ℝ) ≤ ν) (h₁ : ν ≤ ν₁)
    {I : Fin n → ℚ × ℚ} {i j : Fin n} {t : Fin nA}
    (h : BlockArc p q ν (I i) (I j) (s₀ + t)) : (blockHull p q ν₀ ν₁ s₀ nA I).Adj i t j := by
  obtain ⟨h1, h2⟩ := h
  have hK : (0 : ℝ) ≤ (p : ℝ) - q := by
    have : (q : ℝ) ≤ p := by exact_mod_cast hpq
    linarith
  have e0 := mul_le_mul_of_nonneg_left h₀ hK
  have e1 := mul_le_mul_of_nonneg_left h₁ hK
  refine adj_blockHull.2 ⟨?_, ?_, ?_⟩
  · have : ((p : ℝ) - q) * (ν₀ : ℝ)
        < p * ((I i).2 : ℝ) - ((s₀ + t : ℤ) : ℝ) - q * ((I j).1 : ℝ) := by
      linarith
    exact_mod_cast this
  · have : (p : ℝ) * ((I i).1 : ℝ) - ((s₀ + t : ℤ) : ℝ) - q * ((I j).2 : ℝ)
        < ((p : ℝ) - q) * ν₁ := by
      linarith
    exact_mod_cast this
  · have : (p : ℝ) * ((I i).1 : ℝ) - ((s₀ + t : ℤ) : ℝ) - q * ((I j).2 : ℝ)
        < p * ((I i).2 : ℝ) - ((s₀ + t : ℤ) : ℝ) - q * ((I j).1 : ℝ) := by
      linarith
    exact_mod_cast this

/-- **The hull is the union** of the rational block graphs over the interval. -/
@[category textbook, AMS 11 05, group "carry_interval"]
theorem adj_blockHull_iff (hpq : q < p) {ν₀ ν₁ : ℚ} (hν : ν₀ ≤ ν₁) {I : Fin n → ℚ × ℚ}
    {i j : Fin n} {t : Fin nA} :
    (blockHull p q ν₀ ν₁ s₀ nA I).Adj i t j ↔
      ∃ ν : ℚ, ν₀ ≤ ν ∧ ν ≤ ν₁ ∧ (blockGraph p q ν s₀ nA I).Adj i t j := by
  constructor
  · intro h
    obtain ⟨h1, h2, h3⟩ := adj_blockHull.1 h
    set K : ℚ := (p : ℚ) - q
    have hK : 0 < K := by
      have : (q : ℚ) < p := by exact_mod_cast hpq
      simp only [K]; linarith
    set α : ℚ := p * (I i).2 - (s₀ + t : ℤ) - q * (I j).1
    set β : ℚ := p * (I i).1 - (s₀ + t : ℤ) - q * (I j).2
    set X : ℚ := (max (K * ν₀) β + min (K * ν₁) α) / 2
    have hKν : K * ν₀ ≤ K * ν₁ := mul_le_mul_of_nonneg_left hν hK.le
    have hX1 : K * ν₀ ≤ X ∧ X ≤ K * ν₁ ∧ β < X ∧ X < α := by
      simp only [X]
      rcases le_total (K * ν₀) β with ha | ha <;> rcases le_total (K * ν₁) α with hb | hb <;>
        simp only [max_eq_left, max_eq_right, min_eq_left, min_eq_right, ha, hb] <;>
        refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
    refine ⟨X / K, ?_, ?_, adj_blockGraph.2 ⟨?_, ?_⟩⟩
    · rw [le_div_iff₀ hK, mul_comm]; exact hX1.1
    · rw [div_le_iff₀ hK, mul_comm]; exact hX1.2.1
    · have : (q : ℚ) * (I j).1 < p * (I i).2 - ((p : ℚ) - q) * (X / K) - (s₀ + t : ℤ) := by
        have : ((p : ℚ) - q) * (X / K) = X := mul_div_cancel₀ X hK.ne'
        rw [this]; simp only [α] at hX1; linarith [hX1.2.2.2]
      exact_mod_cast this
    · have : (p : ℚ) * (I i).1 - ((p : ℚ) - q) * (X / K) - (s₀ + t : ℤ) < q * (I j).2 := by
        have : ((p : ℚ) - q) * (X / K) = X := mul_div_cancel₀ X hK.ne'
        rw [this]; simp only [β] at hX1; linarith [hX1.2.2.1]
      exact_mod_cast this
  · rintro ⟨ν, h₀, h₁, h⟩
    exact blockArc_hull hpq.le (by exact_mod_cast h₀) (by exact_mod_cast h₁) (adj_blockGraph.1 h)

/-- **The hull cover**: for every real `ν ∈ [ν₀, ν₁]` the hull covers the affine system at `ν`. -/
@[category textbook, AMS 11 37 05, group "carry_interval"]
theorem cover_blockHull (hq : q ≠ 0) (hpq : q ≤ p) (hp : 0 < p) {ν : ℝ} {ν₀ ν₁ : ℚ}
    (h₀ : (ν₀ : ℝ) ≤ ν) (h₁ : ν ≤ ν₁) {P : List ℕ} {I : Fin n → ℚ × ℚ}
    (hI : ∀ y : ℝ, 0 ≤ y → y < 1 → ∃ j, y ∈ ival (I j)) :
    Cover (blockHull p q ν₀ ν₁ s₀ nA I) (fun _ => affStep p q ν) (affAdm p q ν s₀ P)
      (fun i => Int.fract ⁻¹' ival (I i)) :=
  (cover_frac_of_blockArc hq hp (fun _ _ _ h => blockArc_hull hpq h₀ h₁ h) hI).comap Int.fract
    fun t z h => fract_semiconj hq z t h

/-- **Shrinking the interval shrinks the hull.** -/
@[category API, AMS 11 05, group "carry_interval"]
theorem blockHull_mono {ν₀ ν₁ μ₀ μ₁ : ℚ} (hpq : q ≤ p) (h₀ : μ₀ ≤ ν₀) (h₁ : ν₁ ≤ μ₁)
    {I : Fin n → ℚ × ℚ} (i : Fin n) (t : Fin nA) :
    (blockHull p q ν₀ ν₁ s₀ nA I).succ i t ⊆ (blockHull p q μ₀ μ₁ s₀ nA I).succ i t := by
  intro j hj
  obtain ⟨h1, h2, h3⟩ := adj_blockHull.1 hj
  have hK : (0 : ℚ) ≤ (p : ℚ) - q := by
    have : (q : ℚ) ≤ p := by exact_mod_cast hpq
    linarith
  have e0 := mul_le_mul_of_nonneg_left h₀ hK
  have e1 := mul_le_mul_of_nonneg_left h₁ hK
  exact adj_blockHull.2 ⟨by linarith, by linarith, h3⟩

/-- The identity is a homomorphism into the hull of a larger interval. -/
def blockHull_hom {ν₀ ν₁ μ₀ μ₁ : ℚ} (hpq : q ≤ p) (h₀ : μ₀ ≤ ν₀) (h₁ : ν₁ ≤ μ₁)
    {I : Fin n → ℚ × ℚ} :
    Hom (blockHull p q ν₀ ν₁ s₀ nA I) (blockHull p q μ₀ μ₁ s₀ nA I) :=
  ⟨id, fun h => blockHull_mono hpq h₀ h₁ _ _ h⟩

/-- The hull of the cells. -/
def cellHull (p q : ℕ) (ν₀ ν₁ : ℚ) (s₀ : ℤ) (nA D : ℕ) : CarryGraph (Fin D) (Fin nA) :=
  blockHull p q ν₀ ν₁ s₀ nA (cells D)

/-- The affine hull: residue graph ⊗ cell hull. -/
def affineHull (p q : ℕ) (ν₀ ν₁ : ℚ) (s₀ : ℤ) (nA M D : ℕ) [NeZero M] (PM Pq : List ℕ) :
    CarryGraph (ZMod M × Fin D) (Fin nA) :=
  (residueGraph p q M s₀ nA PM Pq).labelProduct (cellHull p q ν₀ ν₁ s₀ nA D)

/-- **The affine hull cover**, for every real `ν ∈ [ν₀, ν₁]`. -/
@[category textbook, AMS 11 37 05, group "carry_interval"]
theorem cover_affineHull (hq : q ≠ 0) (hpq : q ≤ p) (hp : 0 < p) {ν : ℝ} {ν₀ ν₁ : ℚ}
    (h₀ : (ν₀ : ℝ) ≤ ν) (h₁ : ν ≤ ν₁) {M D : ℕ} [NeZero M] (hD : 0 < D) {PM Pq P : List ℕ}
    (hPM : ∀ ℓ ∈ PM, ℓ ∣ M ∧ ℓ ∈ P) (hPq : ∀ ℓ ∈ Pq, ℓ ∣ q ∧ Nat.Coprime ℓ p ∧ ℓ ∈ P) :
    Cover (affineHull p q ν₀ ν₁ s₀ nA M D PM Pq) (fun _ => affStep p q ν) (affAdm p q ν s₀ P)
      (fun v => {z | ((⌊z⌋ : ℤ) : ZMod M) = v.1} ∩ Int.fract ⁻¹' ival (cells D v.2)) :=
  (cover_residueGraph hPM hPq).labelProduct
    (cover_blockHull hq hpq hp h₀ h₁ fun y h0 h1 => exists_cell hD y h0 h1)

/-! ### Monotonicity in the divisor set -/

/-- **A larger divisor set gives a smaller residue graph.** -/
def residueGraph_hom {M : ℕ} [NeZero M] {PM Pq PM' Pq' : List ℕ} (hM : PM ⊆ PM')
    (hq : Pq ⊆ Pq') :
    Hom (residueGraph p q M s₀ nA PM' Pq') (residueGraph p q M s₀ nA PM Pq) :=
  ⟨id, fun h => by
    obtain ⟨h1, h2, h3, h4⟩ := adj_residueGraph.1 h
    exact adj_residueGraph.2 ⟨fun ℓ hℓ => h1 ℓ (hM hℓ), fun ℓ hℓ => h2 ℓ (hq hℓ), h3,
      fun ℓ hℓ => h4 ℓ (hM hℓ)⟩⟩

/-- **Certificates survive a larger divisor set**: the label form of the affine graph for
`(PM, Pq)` gives it for `(PM', Pq') ⊇ (PM, Pq)` (the content of `avoidLang_mono`). -/
@[category textbook, AMS 11 05 37, group "carry_interval"]
theorem allPer_affine_mono {νq : ℚ} {M D : ℕ} [NeZero M] {PM Pq PM' Pq' : List ℕ}
    (hM : PM ⊆ PM') (hq : Pq ⊆ Pq') (h : (affine p q νq s₀ nA M D PM Pq).AllPer) :
    (affine p q νq s₀ nA M D PM' Pq').AllPer :=
  allPer_of_hom ((residueGraph_hom hM hq).prodMap (Hom.id _)) h

/-! ### One window for the interval -/

/-- **One letter window for the whole interval.** -/
@[category API, AMS 11, group "carry_interval"]
theorem carry_window_of_interval (hq : q ≠ 0) (hpq : q ≤ p) {ν : ℝ} {ν₀ ν₁ : ℝ}
    (h₀ : ν₀ ≤ ν) (h₁ : ν ≤ ν₁) (hs : s₀ ≤ ⌊-((p : ℝ) - q) * ν₁⌋ - q)
    (hn : ⌊-((p : ℝ) - q) * ν₀⌋ + p + 1 ≤ s₀ + nA) (z : ℝ) :
    s₀ ≤ carry p q ν z ∧ carry p q ν z < s₀ + nA := by
  obtain ⟨hlo, hhi⟩ := carry_window (p := p) (ν := ν) hq z
  have hK : (0 : ℝ) ≤ (p : ℝ) - q := by
    have : (q : ℝ) ≤ p := by exact_mod_cast hpq
    linarith
  have f1 : ⌊-((p : ℝ) - q) * ν₁⌋ ≤ ⌊-((p : ℝ) - q) * ν⌋ :=
    Int.floor_mono (by nlinarith)
  have f0 : ⌊-((p : ℝ) - q) * ν⌋ ≤ ⌊-((p : ℝ) - q) * ν₀⌋ :=
    Int.floor_mono (by nlinarith)
  push_cast at hhi
  constructor <;> omega

/-- **The dimension bound, uniform over a parameter interval**: for every real `ν ∈ [ν₀, ν₁]`,
the `ξ` with `⌊ξ(p/q)ⁿ + ν⌋` eventually avoiding `P` form a set of Hausdorff dimension at most
`entropy (affineHull …) / log (p/q)`. -/
@[category research solved, AMS 11 28 37, ref "DN05", group "carry_interval"]
theorem dimH_avoiders_le_hull (hq : 0 < q) (hpq : q < p) {ν₀ ν₁ : ℚ} {ν : ℝ}
    (h₀ : (ν₀ : ℝ) ≤ ν) (h₁ : ν ≤ ν₁) {M D : ℕ} [NeZero M] (hD : 0 < D) {PM Pq P : List ℕ}
    (hPM : ∀ ℓ ∈ PM, ℓ ∣ M ∧ ℓ ∈ P) (hPq : ∀ ℓ ∈ Pq, ℓ ∣ q ∧ Nat.Coprime ℓ p ∧ ℓ ∈ P)
    (hs : s₀ ≤ ⌊-((p : ℝ) - q) * ν₁⌋ - q) (hn : ⌊-((p : ℝ) - q) * ν₀⌋ + p + 1 ≤ s₀ + nA) :
    dimH {ξ : ℝ | ∀ᶠ n in atTop, Avoid P ⌊ξ * ((p : ℝ) / q) ^ n + ν⌋}
      ≤ ((affineHull p q ν₀ ν₁ s₀ nA M D PM Pq).entropy
          / ((Real.log ((p : ℝ) / q) : ℝ) : EReal)).toENNReal :=
  dimH_avoiders_le hq hpq
    (cover_affineHull hq.ne' hpq.le (hq.trans hpq) h₀ h₁ hD hPM hPq)
    (fun z => affine_rho_cover (M := M) hD z)
    (carry_window_of_interval hq.ne' hpq.le h₀ h₁ hs hn)

end CarryGraph
