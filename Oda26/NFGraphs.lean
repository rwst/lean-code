/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Oda26.OneStep
import Oda26.AllEdge
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Complete one-step graphs, projection and lifting ([Oda26] §7.1, §7.3, §7.4)

The complete one-step graph `G(M, K)` has the states `(q, j)` with `q` a unit mod `M`, and the
graph `G′(R, K)` of [Oda26] (I) restricts the labels to the general carry alphabet `C(a, b)`.
Everything is stated for an arbitrary shift `ν` (the graphs of `⌊ξ(a/b)ⁿ + ν⌋`, see
`Oda.WG.oneStep`); [Oda26] is the case `ν = 0`.  The arithmetic (Lemma 29, Propositions 35–36)
does not see the shift, which enters only the real cell condition (E3) and the label bounds.

* `Oda.WG.allCert_iff_allPer` — every cyclic SCC passes the phase test iff every infinite walk has
  eventually periodic output (Lemma 6 + Theorem 21).
* `Oda.WG.label_mem_alphabet` — **[Oda26] Lemma 29**: if `rad(2ab) ∣ M`, every edge of `G(M, K)` has
  its label in `C(a, b)`.
* `Oda.WG.proj_edge` — **[Oda26] Lemma 31 (projection)**: `π(q, J) = (q mod m, ⌊J/f⌋)` maps edges
  of `G(M, K)` to edges of `G(m, k)` (`m ∣ M`, `K = fk`) with the same label.
* `Oda.WG.exists_lift` — **[Oda26] Propositions 35 and 36 (merged)**: a walk of `G′(R, K)` lifts
  to `G(M, K)` with the same labels and cells, whenever `R ∣ M`, `gcd(R, 2ab) = 1` and every prime of
  `M` divides `2abR`.  Prime powers `p^e ∥ M` are treated one at a time: for `p ∤ b` by the recurrence
  `q_{n+1} = b⁻¹(aqₙ + cₙ)`, for `p ∣ b` by `qₙ = −Σ_{j<e} bʲa^{−j−1}c_{n+j}`; the factors are
  combined by the Chinese remainder theorem.
* `Oda.WG.allPer_gPrime_iff` — hence `G(M, K)` and `G′(R, K)` have the same infinite outputs.

## References

* [Oda26] Y. Odagiri, *Finite graph certificates for composite terms in rational floor sequences*,
  Zenodo, doi:10.5281/zenodo.22997709 (2026).
-/

namespace Oda.WG

open ForMathlib.SubwordComplexity

variable {V α : Type*}

/-! ## Cyclic SCCs versus infinite walks -/

/-- Every infinite walk of `E` has eventually periodic output. -/
def AllPer (E : Graph V α) : Prop :=
  ∀ y v w t, Covers E y v w t → IsEventuallyPeriodic y

/-- Every strongly connected component of `E` passes the phase test (19) (components without an
internal edge pass vacuously). -/
def AllCert (E : Graph V α) : Prop := ∀ x, Certified E (SameSCC E x)

/-- A path between two members of an SCC stays inside the SCC. -/
theorem pathIn_of_reach {E : Graph V α} {x u v : V} (h : Reach E u v) (hu : SameSCC E x u)
    (hv : SameSCC E x v) : ∃ W, PathIn E (SameSCC E x) u W v := by
  unfold Reach at h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], PathIn.nil hv⟩
  | @head u c hst hrest ih =>
    obtain ⟨w, hw⟩ := hst
    have hc : SameSCC E x c := ⟨hu.1.tail ⟨w, hw⟩, hrest.trans hv.2⟩
    obtain ⟨W, hW⟩ := ih hc
    exact ⟨w ++ W, PathIn.cons hw hu hW⟩

/-- **Phase test for all components ⇔ periodic output of all walks** (Lemma 6, Lemma 12(b),
Theorem 21 (b)⇒(a)). -/
@[category research solved, AMS 05 68, ref "Oda26", group "oda26_normalform"]
theorem allCert_iff_allPer [Finite V] [Nonempty α] {E : Graph V α}
    (hEpos : ∀ u w v, E u w v → 0 < w.length) : AllCert E ↔ AllPer E := by
  constructor
  · intro hc y v w t hcov
    obtain ⟨i₁, hi₁⟩ := eventually_sameSCC hcov.edge
    exact (hcov.shift i₁).periodic_of_certified (hc (v i₁)) fun i => hi₁ (i₁ + i) (by omega)
  · intro h x
    have t := all_edge_test (C := SameSCC E x) (ρ := x) hEpos
      (fun u v hu hv => pathIn_of_reach (hu.2.trans hv.1) hu hv)
      ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
    exact (t.out 1 2).2 fun y v w t hc _ => h y v w t hc

/-! ## The complete graphs `G(M, K)` and `G′(R, K)` -/

variable {a b : ℕ} {ν : ℝ}

/-- **The complete one-step graph** `G(M, K)`: all states with unit residue (shift `ν`). -/
def oneStepU (a b : ℕ) (ν : ℝ) (M K : ℕ) : Graph (Fin M × Fin K) ℤ :=
  oneStep a b ν M K fun x => Nat.Coprime x.1 M

/-- **The graph `G′(R, K)`** of [Oda26] (I), second form: `G(R, K)` with labels in `C(a, b)`. -/
def gPrime (a b : ℕ) (ν : ℝ) (R K : ℕ) : Graph (Fin R × Fin K) ℤ :=
  fun x w x' => oneStepU a b ν R K x w x' ∧ ∀ e ∈ w, carryAlphabet a b ν e

theorem oneStepU_pos {M K : ℕ} : ∀ u w v, oneStepU a b ν M K u w v → 0 < w.length := by
  rintro u w v ⟨-, -, e, rfl, -⟩; simp

theorem gPrime_pos {R K : ℕ} : ∀ u w v, gPrime a b ν R K u w v → 0 < w.length :=
  fun u w v h => oneStepU_pos u w v h.1

/-! ## Lemma 29 -/

/-- A prime dividing `ab` does not divide a letter of `C(a, b)`. -/
theorem not_dvd_of_alphabet {c : ℤ} (hc : carryAlphabet a b ν c) {p : ℕ} (hp : p.Prime)
    (hpab : p ∣ a * b) : ¬ (p : ℤ) ∣ c := by
  intro hpc
  have hco : IsCoprime c ((a : ℤ) * b) := Int.isCoprime_iff_gcd_eq_one.2 hc.2.2.2
  exact (Nat.prime_iff_prime_int.1 hp).not_isUnit
    (hco.isUnit_of_dvd' hpc (by exact_mod_cast hpab))

/-- **[Oda26] Lemma 29.**  If `2 ∣ M` and every prime of `ab` divides `M`, every edge of `G(M, K)` has
its label in `C(a, b)`. -/
@[category research solved, AMS 11 05, ref "Oda26", group "oda26_normalform"]
theorem label_mem_alphabet (hcop : Nat.Coprime a b) {M K : ℕ} (h2 : 2 ∣ M)
    (hab : ∀ p, p.Prime → p ∣ a * b → p ∣ M) {x x' : Fin M × Fin K} {e : ℤ}
    (h : oneStepU a b ν M K x [e] x') : carryAlphabet a b ν e := by
  obtain ⟨hu, hu', e', he', h1, h2', hE2, -⟩ := h
  obtain rfl : e = e' := by simpa using he'
  have hdvd : (M : ℤ) ∣ a * (x.1 : ℕ) + e - b * (x'.1 : ℕ) := hE2.dvd
  -- a prime of `M` divides neither residue
  have hres : ∀ p, p.Prime → p ∣ M → ¬ (p : ℤ) ∣ ((x.1 : ℕ) : ℤ) ∧ ¬ (p : ℤ) ∣ ((x'.1 : ℕ) : ℤ) := by
    intro p hp hpM
    constructor
    · intro h; exact (Nat.Prime.not_coprime_iff_dvd.2 ⟨p, hp, by exact_mod_cast h, hpM⟩) hu
    · intro h; exact (Nat.Prime.not_coprime_iff_dvd.2 ⟨p, hp, by exact_mod_cast h, hpM⟩) hu'
  have hg : Int.gcd e (a * b) = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
    have hpe : (p : ℤ) ∣ e := (Int.natCast_dvd_natCast.2 hpg).trans (Int.gcd_dvd_left _ _)
    have hpab : (p : ℤ) ∣ (a : ℤ) * b := (Int.natCast_dvd_natCast.2 hpg).trans (Int.gcd_dvd_right _ _)
    have hpZ := Nat.prime_iff_prime_int.1 hp
    have hpM : p ∣ M := hab p hp (by exact_mod_cast hpab)
    have hpd : (p : ℤ) ∣ a * (x.1 : ℕ) + e - b * (x'.1 : ℕ) :=
      (Int.natCast_dvd_natCast.2 hpM).trans hdvd
    rcases hpZ.dvd_or_dvd hpab with hpa | hpb
    · -- `p ∣ b z`
      have : (p : ℤ) ∣ b * (x'.1 : ℕ) := by
        have := dvd_sub (dvd_add (dvd_mul_of_dvd_left hpa ((x.1 : ℕ) : ℤ)) hpe) hpd
        rwa [show (a : ℤ) * (x.1 : ℕ) + e - (a * (x.1 : ℕ) + e - b * (x'.1 : ℕ)) =
          b * (x'.1 : ℕ) by ring] at this
      rcases hpZ.dvd_or_dvd this with hpb | hpz
      · exact hp.one_lt.ne' (Nat.dvd_one.1
          (hcop ▸ Nat.dvd_gcd (by exact_mod_cast hpa) (by exact_mod_cast hpb)))
      · exact (hres p hp hpM).2 hpz
    · have : (p : ℤ) ∣ a * (x.1 : ℕ) := by
        have := dvd_add (dvd_sub hpd hpe) (dvd_mul_of_dvd_left hpb ((x'.1 : ℕ) : ℤ))
        rwa [show (a : ℤ) * (x.1 : ℕ) + e - b * (x'.1 : ℕ) - e + b * (x'.1 : ℕ) =
          a * (x.1 : ℕ) by ring] at this
      rcases hpZ.dvd_or_dvd this with hpa | hpq
      · exact hp.one_lt.ne' (Nat.dvd_one.1
          (hcop ▸ Nat.dvd_gcd (by exact_mod_cast hpa) (by exact_mod_cast hpb)))
      · exact (hres p hp hpM).1 hpq
  refine ⟨h1, h2', ?_, hg⟩
  -- parity
  have hq := (hres 2 Nat.prime_two h2).1
  have hz := (hres 2 Nat.prime_two h2).2
  have hq2 : ((x.1 : ℕ) : ℤ) % 2 = 1 := by omega
  have hz2 : ((x'.1 : ℕ) : ℤ) % 2 = 1 := by omega
  have hd2 : (2 : ℤ) ∣ a * (x.1 : ℕ) + e - b * (x'.1 : ℕ) :=
    (Int.natCast_dvd_natCast.2 h2).trans hdvd
  have haq : ((a : ℤ) * (x.1 : ℕ)) % 2 = (a : ℤ) % 2 := by
    rw [Int.mul_emod, hq2, mul_one, Int.emod_emod_of_dvd _ (dvd_refl _)]
  have hbz : ((b : ℤ) * (x'.1 : ℕ)) % 2 = (b : ℤ) % 2 := by
    rw [Int.mul_emod, hz2, mul_one, Int.emod_emod_of_dvd _ (dvd_refl _)]
  have hodd : (2 : ℤ) ∣ (a : ℤ) * b → e % 2 = 1 := fun h => by
    have : ¬ (2 : ℤ) ∣ e := fun h2e => by
      have := Int.dvd_gcd h2e h
      rw [hg] at this; norm_num at this
    omega
  have hnot : ¬ (2 ∣ a ∧ 2 ∣ b) := fun ⟨h1, h2⟩ => by
    have := Nat.dvd_gcd h1 h2; rw [hcop] at this; omega
  generalize (a : ℤ) * ((x.1 : ℕ) : ℤ) = A at haq hd2
  generalize (b : ℤ) * ((x'.1 : ℕ) : ℤ) = B at hbz hd2
  have hd2' := Int.emod_emod_of_dvd (A + e - B) (dvd_refl 2)
  rcases Int.emod_two_eq (a : ℤ) with ha2 | ha2 <;> rcases Int.emod_two_eq (b : ℤ) with hb2 | hb2
  · exact absurd ⟨by omega, by omega⟩ hnot
  · have := hodd (Dvd.dvd.mul_right (Int.dvd_of_emod_eq_zero ha2) _); omega
  · have := hodd (Dvd.dvd.mul_left (Int.dvd_of_emod_eq_zero hb2) _); omega
  · omega

/-! ## Lemma 31 -/

theorem proj_aux {k K j : ℕ} (hk : k ∣ K) (hj : j < K) : j / (K / k) < k := by
  obtain ⟨f, rfl⟩ := hk
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hj)
  rw [Nat.mul_div_cancel_left f hk0]
  have hf : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; simp at hj)
  rw [Nat.div_lt_iff_lt_mul hf]; exact hj

theorem div_mul_div_aux {k k' K : ℕ} (hk : k ∣ k') (hk' : k' ∣ K) (hK : 0 < K) :
    K / k' * (k' / k) = K / k := by
  obtain ⟨v, rfl⟩ := hk
  obtain ⟨u, rfl⟩ := hk'
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hK)
  have hv0 : 0 < v := Nat.pos_of_ne_zero (by rintro rfl; simp at hK)
  rw [Nat.mul_div_cancel_left u (Nat.mul_pos hk0 hv0), Nat.mul_div_cancel_left v hk0, mul_assoc,
    Nat.mul_div_cancel_left _ hk0, mul_comm]

/-- **The projection** `π(q, J) = (q mod m, ⌊J/f⌋)`, `K = fk`. -/
def proj {m k M K : ℕ} (hm : m ∣ M) (hk : k ∣ K) (x : Fin M × Fin K) : Fin m × Fin k :=
  (⟨x.1 % m, Nat.mod_lt _ (Nat.pos_of_dvd_of_pos hm (Nat.zero_lt_of_lt x.1.2))⟩,
    ⟨x.2 / (K / k), proj_aux hk x.2.2⟩)

theorem proj_proj {m k m' k' M K : ℕ} (hm : m ∣ m') (hk : k ∣ k') (hm' : m' ∣ M) (hk' : k' ∣ K)
    (x : Fin M × Fin K) : proj hm hk (proj hm' hk' x) = proj (hm.trans hm') (hk.trans hk') x := by
  have hK : 0 < K := Nat.zero_lt_of_lt x.2.2
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
  · exact Nat.mod_mod_of_dvd _ hm
  · show x.2 / (K / k') / (k' / k) = x.2 / (K / k)
    rw [Nat.div_div_eq_div_mul, div_mul_div_aux hk hk' hK]

/-- **[Oda26] Lemma 31 (projection).** -/
@[category research solved, AMS 11 05, ref "Oda26", group "oda26_normalform"]
theorem proj_edge {m k M K : ℕ} (hm : m ∣ M) (hk : k ∣ K) {x x' : Fin M × Fin K} {w : List ℤ}
    (h : oneStepU a b ν M K x w x') : oneStepU a b ν m k (proj hm hk x) w (proj hm hk x') := by
  have hK : 0 < K := Nat.zero_lt_of_lt x.2.2
  obtain ⟨hu, hu', e, rfl, h1, h2, hE2, hl, hh⟩ := h
  have cop : ∀ y : Fin M, Nat.Coprime y M → Nat.Coprime (y % m) m := fun y hy => by
    have := Nat.Coprime.coprime_dvd_right hm hy
    rw [Nat.Coprime, ← Nat.gcd_rec, Nat.gcd_comm]; exact this
  refine ⟨cop _ hu, cop _ hu', e, rfl, h1, h2, ?_, ?_⟩
  · show (b : ℤ) * ((x'.1 % m : ℕ) : ℤ) ≡ a * ((x.1 % m : ℕ) : ℤ) + e [ZMOD m]
    push_cast
    have hm' := Int.ModEq.of_dvd (Int.natCast_dvd_natCast.2 hm) hE2
    exact ((Int.mod_modEq _ _).mul_left _).trans
      (hm'.trans (((Int.mod_modEq _ _).symm.mul_left _).add_right _))
  · obtain ⟨f, rfl⟩ := hk
    have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hK)
    have hf0 : 0 < f := Nat.pos_of_ne_zero (by rintro rfl; simp at hK)
    show (a : ℝ) * ((x.2 / (k * f / k) : ℕ) : ℝ) - b * (((x'.2 / (k * f / k) : ℕ) : ℝ) + 1) <
        (e + ((a : ℝ) - b) * ν) * (k : ℕ) ∧
      (e + ((a : ℝ) - b) * ν) * (k : ℕ) <
        (a : ℝ) * (((x.2 / (k * f / k) : ℕ) : ℝ) + 1) - b * ((x'.2 / (k * f / k) : ℕ) : ℝ)
    rw [Nat.mul_div_cancel_left f hk0]
    have hJ := Nat.div_add_mod (x.2 : ℕ) f
    have hH := Nat.div_add_mod (x'.2 : ℕ) f
    have hi := Nat.mod_lt (x.2 : ℕ) hf0
    have hℓ := Nat.mod_lt (x'.2 : ℕ) hf0
    set j := (x.2 : ℕ) / f
    set i := (x.2 : ℕ) % f
    set h' := (x'.2 : ℕ) / f
    set ℓ := (x'.2 : ℕ) % f
    have hJ' : ((x.2 : ℕ) : ℝ) = f * j + i := by exact_mod_cast hJ.symm
    have hH' : ((x'.2 : ℕ) : ℝ) = f * h' + ℓ := by exact_mod_cast hH.symm
    rw [hJ', hH'] at hl hh
    push_cast at hl hh ⊢
    set E : ℝ := (e : ℝ) + ((a : ℝ) - b) * ν
    have ha0 : (0 : ℝ) ≤ a := by positivity
    have hb0 : (0 : ℝ) ≤ b := by positivity
    have hi' : (i : ℝ) + 1 ≤ f := by exact_mod_cast hi
    have hℓ' : (ℓ : ℝ) + 1 ≤ f := by exact_mod_cast hℓ
    have P1 : 0 ≤ (a : ℝ) * i := mul_nonneg ha0 (by positivity)
    have P2 : 0 ≤ (b : ℝ) * (f - ℓ - 1) := mul_nonneg hb0 (by linarith)
    have P3 : 0 ≤ (a : ℝ) * (f - i - 1) := mul_nonneg ha0 (by linarith)
    have P4 : 0 ≤ (b : ℝ) * ℓ := mul_nonneg hb0 (by positivity)
    have hf' : (0 : ℝ) < f := by exact_mod_cast hf0
    constructor
    · refine lt_of_mul_lt_mul_left (a := (f : ℝ)) ?_ hf'.le
      nlinarith
    · refine lt_of_mul_lt_mul_left (a := (f : ℝ)) ?_ hf'.le
      nlinarith

/-! ## Propositions 35 and 36: lifting walks of `G′(R, K)` to `G(M, K)` -/

section Lift

variable (a b R : ℕ) (q c : ℕ → ℤ)

/-- Unit residues modulo `M` along the labels `c`, agreeing with `q` modulo `gcd(R, M)`. -/
def LiftAt (M : ℕ) : Prop :=
  ∃ Z : ℕ → ℤ, (∀ n, (M : ℤ) ∣ a * Z n + c n - b * Z (n + 1)) ∧ (∀ n, IsCoprime (Z n) M) ∧
    ∀ n, ((Nat.gcd R M : ℕ) : ℤ) ∣ Z n - q n

/-- `qₙ = −Σ_{j<e} bʲ a'^{j+1} c_{n+j}` (`a' = a⁻¹`), the residues at a prime power dividing `b`. -/
def bSum (b e : ℕ) (a' : ℤ) (c : ℕ → ℤ) (n : ℕ) : ℤ :=
  -∑ j ∈ Finset.range e, (b : ℤ) ^ j * a' ^ (j + 1) * c (n + j)

/-- `q_{n+1} = b'(aqₙ + cₙ)` (`b' = b⁻¹`), the residues at a prime power prime to `b`. -/
def bRec (a : ℕ) (b' z₀ : ℤ) (c : ℕ → ℤ) : ℕ → ℤ
  | 0 => z₀
  | n + 1 => b' * (a * bRec a b' z₀ c n + c n)

variable {a b R q c}

theorem liftAt_one : LiftAt a b R q c 1 :=
  ⟨fun _ => 1, fun _ => by simp, fun _ => by simp [isCoprime_one_left], fun _ => by simp⟩

/-- Chinese remainder step. -/
theorem liftAt_mul {M₁ M₂ : ℕ} (hco : Nat.Coprime M₁ M₂) (h₁ : LiftAt a b R q c M₁)
    (h₂ : LiftAt a b R q c M₂) : LiftAt a b R q c (M₁ * M₂) := by
  obtain ⟨Z₁, r₁, u₁, g₁⟩ := h₁
  obtain ⟨Z₂, r₂, u₂, g₂⟩ := h₂
  have hc : IsCoprime (M₁ : ℤ) M₂ := Nat.isCoprime_iff_coprime.2 hco
  obtain ⟨u, v, huv⟩ := hc
  let Z : ℕ → ℤ := fun n => Z₁ n * (v * M₂) + Z₂ n * (u * M₁)
  have e₁ : ∀ n, (M₁ : ℤ) ∣ Z n - Z₁ n := fun n =>
    ⟨(Z₂ n - Z₁ n) * u, by simp only [Z]; linear_combination (Z₁ n) * huv⟩
  have e₂ : ∀ n, (M₂ : ℤ) ∣ Z n - Z₂ n := fun n =>
    ⟨(Z₁ n - Z₂ n) * v, by simp only [Z]; linear_combination (Z₂ n) * huv⟩
  have hc : IsCoprime (M₁ : ℤ) M₂ := ⟨u, v, huv⟩
  refine ⟨Z, fun n => ?_, fun n => ?_, fun n => ?_⟩
  · push_cast
    refine hc.mul_dvd ?_ ?_
    · have := dvd_add (dvd_add (r₁ n) (dvd_mul_of_dvd_right (e₁ n) (a : ℤ)))
        (dvd_mul_of_dvd_right (e₁ (n + 1)) (-(b : ℤ)))
      convert this using 1; ring
    · have := dvd_add (dvd_add (r₂ n) (dvd_mul_of_dvd_right (e₂ n) (a : ℤ)))
        (dvd_mul_of_dvd_right (e₂ (n + 1)) (-(b : ℤ)))
      convert this using 1; ring
  · push_cast
    obtain ⟨t, ht⟩ := e₁ n
    obtain ⟨t', ht'⟩ := e₂ n
    refine IsCoprime.mul_right ?_ ?_
    · rw [show Z n = Z₁ n + M₁ * t by linarith]; exact (u₁ n).add_mul_left_left t
    · rw [show Z n = Z₂ n + M₂ * t' by linarith]; exact (u₂ n).add_mul_left_left t'
  · rw [Nat.Coprime.gcd_mul R hco]
    push_cast
    have hg : IsCoprime ((Nat.gcd R M₁ : ℕ) : ℤ) (Nat.gcd R M₂ : ℕ) :=
      Nat.isCoprime_iff_coprime.2 (Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _)
        (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _) hco))
    refine hg.mul_dvd ?_ ?_
    · have := dvd_add ((Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right R M₁)).trans (e₁ n)) (g₁ n)
      convert this using 1; ring
    · have := dvd_add ((Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right R M₂)).trans (e₂ n)) (g₂ n)
      convert this using 1; ring

/-- A prime power `p^e` with `p ∣ b` ([Oda26] Proposition 35, case `p ∣ b`). -/
theorem liftAt_dvd_b (hcop : Nat.Coprime a b) {p e : ℕ} (hp : p.Prime) (he : 0 < e)
    (hpb : p ∣ b) (hpR : ¬ p ∣ R) (hc : ∀ n, carryAlphabet a b ν (c n)) :
    LiftAt a b R q c (p ^ e) := by
  have hpa : ¬ p ∣ a := fun hpa => hp.one_lt.ne' (Nat.dvd_one.1 (hcop ▸ Nat.dvd_gcd hpa hpb))
  have hpZ := Nat.prime_iff_prime_int.1 hp
  obtain ⟨a', s, hs⟩ : IsCoprime (a : ℤ) ((p ^ e : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.2
    (Nat.Coprime.pow_right e (Nat.coprime_comm.1 (hp.coprime_iff_not_dvd.2 hpa)))
  refine ⟨bSum b e a' c, fun n => ?_, fun n => ?_, fun n => ?_⟩
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hA : (a : ZMod (p ^ e)) * (a' : ZMod (p ^ e)) = 1 := by
      have := congrArg (Int.cast : ℤ → ZMod (p ^ e)) hs
      simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero,
        add_zero, Int.cast_one] at this
      rw [mul_comm]; exact this
    have hB : (b : ZMod (p ^ e)) ^ e = 0 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((b : ℤ) ^ e) (p ^ e)).2
        (by exact_mod_cast pow_dvd_pow_of_dvd hpb e)
      exact_mod_cast this
    simp only [bSum]
    push_cast
    set F : ℕ → ZMod (p ^ e) := fun j => (b : ZMod (p ^ e)) ^ j * (a' : ZMod (p ^ e)) ^ j *
      (c (n + j) : ZMod (p ^ e)) with hF
    have h1 : (a : ZMod (p ^ e)) * ∑ j ∈ Finset.range e, (b : ZMod (p ^ e)) ^ j *
        (a' : ZMod (p ^ e)) ^ (j + 1) * (c (n + j) : ZMod (p ^ e)) = ∑ j ∈ Finset.range e, F j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hF]; rw [pow_succ]
      linear_combination ((b : ZMod (p ^ e)) ^ j * (a' : ZMod (p ^ e)) ^ j *
        (c (n + j) : ZMod (p ^ e))) * hA
    have h2 : (b : ZMod (p ^ e)) * ∑ j ∈ Finset.range e, (b : ZMod (p ^ e)) ^ j *
        (a' : ZMod (p ^ e)) ^ (j + 1) * (c (n + 1 + j) : ZMod (p ^ e)) =
        ∑ j ∈ Finset.range e, F (j + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hF]; rw [show n + 1 + j = n + (j + 1) by omega]; ring
    have h3 := Finset.sum_range_sub' F e
    rw [Finset.sum_sub_distrib] at h3
    have hF0 : F 0 = c n := by simp [hF]
    have hFe : F e = 0 := by simp only [hF]; rw [hB]; ring
    linear_combination (-1 : ZMod (p ^ e)) * h1 + h2 - h3 - hF0 + hFe
  · have hnd : ¬ (p : ℤ) ∣ bSum b e a' c n := by
      intro hd
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
      simp only [bSum, Finset.sum_range_succ', dvd_neg] at hd
      have hX : (p : ℤ) ∣ ∑ j ∈ Finset.range e', (b : ℤ) ^ (j + 1) * a' ^ (j + 1 + 1) *
          c (n + (j + 1)) :=
        Finset.dvd_sum fun j _ => Dvd.dvd.mul_right (Dvd.dvd.mul_right
          (dvd_pow (by exact_mod_cast hpb) (Nat.succ_ne_zero j)) _) _
      have h0 := (dvd_add_right hX).1 hd
      simp only [pow_zero, one_mul, zero_add, pow_one, add_zero] at h0
      rcases hpZ.dvd_or_dvd h0 with h | h
      · refine hpZ.not_dvd_one ?_
        rw [← hs]
        exact dvd_add (dvd_mul_of_dvd_left h _) (dvd_mul_of_dvd_right
          (by exact_mod_cast dvd_pow_self p (Nat.succ_ne_zero e')) _)
      · exact not_dvd_of_alphabet (hc n) hp (dvd_mul_of_dvd_right hpb a) h
    have := (Irreducible.coprime_iff_not_dvd hpZ.irreducible).2 hnd
    push_cast
    exact this.symm.pow_right
  · rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right e (hp.coprime_iff_not_dvd.2 hpR).symm)]
    simp

/-- A prime power `p^e` with `p ∤ b` and `p ∣ 2aR` ([Oda26] Propositions 35 and 36). -/
theorem liftAt_not_dvd_b {p e : ℕ} (hp : p.Prime) (he : 0 < e) (hpb : ¬ p ∣ b)
    (hpd : p ∣ 2 * a * b * R) (hq : ∀ n, IsCoprime (q n) R)
    (hrec : ∀ n, (R : ℤ) ∣ a * q n + c n - b * q (n + 1)) (hc : ∀ n, carryAlphabet a b ν (c n)) :
    LiftAt a b R q c (p ^ e) := by
  classical
  have hpZ := Nat.prime_iff_prime_int.1 hp
  obtain ⟨b', s, hs⟩ : IsCoprime (b : ℤ) ((p ^ e : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.2
    (Nat.Coprime.pow_right e (Nat.coprime_comm.1 (hp.coprime_iff_not_dvd.2 hpb)))
  set Z := bRec a b' (if p ∣ R then q 0 else 1) c with hZ
  have hZs : ∀ n, Z (n + 1) = b' * (a * Z n + c n) := fun n => rfl
  have hrecZ : ∀ n, ((p ^ e : ℕ) : ℤ) ∣ a * Z n + c n - b * Z (n + 1) := fun n =>
    ⟨s * (a * Z n + c n), by rw [hZs]; linear_combination (-(a * Z n + c n)) * hs⟩
  have hgb : IsCoprime ((Nat.gcd R (p ^ e) : ℕ) : ℤ) b :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _)
      (Nat.Coprime.pow_left e (hp.coprime_iff_not_dvd.2 hpb)))
  have hcong : ∀ n, ((Nat.gcd R (p ^ e) : ℕ) : ℤ) ∣ Z n - q n := by
    by_cases hpR : p ∣ R
    · intro n
      induction n with
      | zero => simp [hZ, bRec, hpR]
      | succ n ih =>
        have h1 := (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right R (p ^ e))).trans (hrecZ n)
        have h2 := (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left R (p ^ e))).trans (hrec n)
        have h3 : ((Nat.gcd R (p ^ e) : ℕ) : ℤ) ∣ (Z (n + 1) - q (n + 1)) * b := by
          have := dvd_add (dvd_sub h2 h1) (dvd_mul_of_dvd_right ih (a : ℤ))
          rwa [show (a : ℤ) * q n + c n - b * q (n + 1) - (a * Z n + c n - b * Z (n + 1)) +
            a * (Z n - q n) = (Z (n + 1) - q (n + 1)) * b by ring] at this
        exact hgb.dvd_of_dvd_mul_right h3
    · intro n
      rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right e (hp.coprime_iff_not_dvd.2 hpR).symm)]
      simp
  have hnd : ∀ n, ¬ (p : ℤ) ∣ Z n := by
    by_cases hpR : p ∣ R
    · intro n hd
      have hpg : (p : ℤ) ∣ ((Nat.gcd R (p ^ e) : ℕ) : ℤ) :=
        Int.natCast_dvd_natCast.2 (Nat.dvd_gcd hpR (dvd_pow_self p he.ne'))
      have : (p : ℤ) ∣ q n := by
        have := dvd_sub hd (hpg.trans (hcong n)); rwa [sub_sub_cancel] at this
      exact hpZ.not_isUnit ((hq n).isUnit_of_dvd' this (by exact_mod_cast hpR))
    · have hpb' : ¬ (p : ℤ) ∣ b' := fun h => by
        refine hpZ.not_dvd_one ?_
        rw [← hs]
        exact dvd_add (dvd_mul_of_dvd_left h _) (dvd_mul_of_dvd_right
          (by exact_mod_cast dvd_pow_self p he.ne') _)
      have hcase : p ∣ a ∨ (p = 2 ∧ ¬ p ∣ a) := by
        rcases (Nat.Prime.dvd_mul hp).1 hpd with h | h
        · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
          · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
            · by_cases hpa : p ∣ a
              · exact Or.inl hpa
              · exact Or.inr ⟨(Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h, hpa⟩
            · exact Or.inl h
          · exact absurd h hpb
        · exact absurd h hpR
      intro n
      induction n with
      | zero => simp only [hZ, bRec, hpR, ↓reduceIte]; exact hpZ.not_dvd_one
      | succ n ih =>
        rw [hZs]; intro hd
        rcases hpZ.dvd_or_dvd hd with h | h
        · exact hpb' h
        · rcases hcase with hpa | ⟨rfl, hpa⟩
          · exact not_dvd_of_alphabet (hc n) hp (dvd_mul_of_dvd_left hpa b)
              ((dvd_add_right (dvd_mul_of_dvd_left (by exact_mod_cast hpa) _)).1 h)
          · have ha2 : (a : ℤ) % 2 = 1 := by omega
            have hb2 : (b : ℤ) % 2 = 1 := by omega
            have hc2 : (2 : ℤ) ∣ c n :=
              Int.dvd_of_emod_eq_zero (by have := (hc n).2.2.1; omega)
            have h' : (2 : ℤ) ∣ a * Z n := (dvd_add_left hc2).1 (by exact_mod_cast h)
            rcases Int.prime_two.dvd_or_dvd h' with h'' | h''
            · omega
            · exact ih (by exact_mod_cast h'')
  refine ⟨Z, hrecZ, fun n => ?_, hcong⟩
  push_cast
  exact ((Irreducible.coprime_iff_not_dvd hpZ.irreducible).2 (hnd n)).symm.pow_right

/-- **[Oda26] Propositions 35 and 36 (lifting).**  Let `R ∣ M`, `gcd(R, 2ab) = 1`, and let every
prime of `M` divide `2abR`.  Residues `qₙ` mod `R` with `bq_{n+1} ≡ aqₙ + cₙ (mod R)`, units mod `R`,
along labels `cₙ ∈ C(a, b)`, lift to units `Zₙ` mod `M` with `bZ_{n+1} ≡ aZₙ + cₙ (mod M)` and
`Zₙ ≡ qₙ (mod R)`. -/
@[category research solved, AMS 11 05, ref "Oda26", group "oda26_normalform"]
theorem exists_lift (hcop : Nat.Coprime a b) {M : ℕ} (hRM : R ∣ M) (hM : 0 < M)
    (hRab : Nat.Coprime R (2 * a * b)) (hprimes : ∀ p, p.Prime → p ∣ M → p ∣ 2 * a * b * R)
    (hq : ∀ n, IsCoprime (q n) R) (hrec : ∀ n, (R : ℤ) ∣ a * q n + c n - b * q (n + 1))
    (hc : ∀ n, carryAlphabet a b ν (c n)) :
    ∃ Z : ℕ → ℤ, (∀ n, (M : ℤ) ∣ a * Z n + c n - b * Z (n + 1)) ∧ (∀ n, IsCoprime (Z n) M) ∧
      ∀ n, (R : ℤ) ∣ Z n - q n := by
  have key : ∀ M, 0 < M → (∀ p, p.Prime → p ∣ M → p ∣ 2 * a * b * R) → LiftAt a b R q c M := by
    intro M
    induction M using Nat.recOnPosPrimePosCoprime with
    | prime_pow p e hp he =>
      intro _ hpr
      have hpd := hpr p hp (dvd_pow_self p he.ne')
      by_cases hpb : p ∣ b
      · have hpR : ¬ p ∣ R := fun h => hp.one_lt.ne' (Nat.dvd_one.1
          (hRab ▸ Nat.dvd_gcd h (Dvd.dvd.mul_left hpb (2 * a))))
        exact liftAt_dvd_b hcop hp he hpb hpR hc
      · exact liftAt_not_dvd_b hp he hpb hpd hq hrec hc
    | zero => intro h; omega
    | one => intro _ _; exact liftAt_one
    | coprime m n hm hn hmn ihm ihn =>
      intro _ hpr
      exact liftAt_mul hmn (ihm (by omega) fun p hp h => hpr p hp (dvd_mul_of_dvd_left h n))
        (ihn (by omega) fun p hp h => hpr p hp (dvd_mul_of_dvd_right h m))
  obtain ⟨Z, h1, h2, h3⟩ := key M hM hprimes
  refine ⟨Z, h1, h2, fun n => ?_⟩
  have := h3 n
  rwa [Nat.gcd_eq_left hRM] at this

end Lift

/-- Walks of `G′(R, K)` lift to walks of `G(M, K)` with the same output. -/
theorem allPer_gPrime_of_allPer (hcop : Nat.Coprime a b) {R M K : ℕ} (hRM : R ∣ M) (hM : 0 < M)
    (hRab : Nat.Coprime R (2 * a * b)) (hprimes : ∀ p, p.Prime → p ∣ M → p ∣ 2 * a * b * R)
    (h : AllPer (oneStepU a b ν M K)) : AllPer (gPrime a b ν R K) := by
  intro y v w t hcov
  have hed := hcov.edge
  have hex : ∀ n, ∃ e, w n = [e] := fun n => by
    obtain ⟨⟨-, -, e, he, -⟩, -⟩ := hed n; exact ⟨e, he⟩
  choose e he using hex
  obtain ⟨Z, hZr, hZc, -⟩ := exists_lift (q := fun n => ((v n).1 : ℕ)) (c := e) hcop hRM hM
    hRab hprimes (fun n => Nat.isCoprime_iff_coprime.2 (hed n).1.1)
    (fun n => by
      obtain ⟨⟨-, -, e', he', -, -, hE2, -⟩, -⟩ := hed n
      rw [he n, List.singleton_inj] at he'
      rw [he']; exact hE2.dvd)
    (fun n => (hed n).2 _ (by rw [he n]; simp))
  refine h y (fun n => (res M hM (Z n), (v n).2)) w t ⟨fun n => ?_, hcov.pos, hcov.time,
    hcov.word⟩
  obtain ⟨⟨-, -, e', he', h1, h2, -, hl, hh⟩, -⟩ := hed n
  refine ⟨coprime_res hM (Int.isCoprime_iff_gcd_eq_one.1 (hZc n)),
    coprime_res hM (Int.isCoprime_iff_gcd_eq_one.1 (hZc (n + 1))), e', he', h1, h2, ?_, hl, hh⟩
  show (b : ℤ) * ((res M hM (Z (n + 1)) : ℕ) : ℤ) ≡ a * ((res M hM (Z n) : ℕ) : ℤ) + e' [ZMOD M]
  rw [res_val, res_val]
  rw [he n, List.singleton_inj] at he'
  rw [← he']
  exact ((Int.mod_modEq _ _).mul_left _).trans ((Int.modEq_of_dvd (hZr n)).trans
    (((Int.mod_modEq _ _).symm.mul_left _).add_right _))

/-- Walks of `G(M, K)` project to walks of `G′(R, K)` with the same output (Lemmas 29, 31). -/
theorem allPer_of_allPer_gPrime (hcop : Nat.Coprime a b) {R M K : ℕ} (hRM : R ∣ M) (h2 : 2 ∣ M)
    (hab : ∀ p, p.Prime → p ∣ a * b → p ∣ M) (h : AllPer (gPrime a b ν R K)) :
    AllPer (oneStepU a b ν M K) := by
  intro y v w t hcov
  refine h y (fun n => proj hRM (dvd_refl K) (v n)) w t ⟨fun n => ⟨proj_edge _ _ (hcov.edge n),
    ?_⟩, hcov.pos, hcov.time, hcov.word⟩
  obtain ⟨-, -, e, he, -⟩ := hcov.edge n
  intro x hx
  rw [he, List.mem_singleton] at hx
  subst hx
  exact label_mem_alphabet hcop h2 hab (he ▸ hcov.edge n)

/-- **[Oda26] Proposition 36, output form.**  For `M` with the same primes as `2abR`
(`gcd(R, 2ab) = 1`, `R ∣ M`), `G(M, K)` and `G′(R, K)` have the same infinite outputs; in
particular all walks of one are eventually periodic iff all walks of the other are. -/
@[category research solved, AMS 11 05, ref "Oda26", group "oda26_normalform"]
theorem allPer_gPrime_iff (hcop : Nat.Coprime a b) {R M K : ℕ} (hRM : R ∣ M) (hM : 0 < M)
    (h2 : 2 ∣ M) (hab : ∀ p, p.Prime → p ∣ a * b → p ∣ M) (hRab : Nat.Coprime R (2 * a * b))
    (hprimes : ∀ p, p.Prime → p ∣ M → p ∣ 2 * a * b * R) :
    AllPer (gPrime a b ν R K) ↔ AllPer (oneStepU a b ν M K) :=
  ⟨allPer_of_allPer_gPrime hcop hRM h2 hab, allPer_gPrime_of_allPer hcop hRM hM hRab hprimes⟩

end Oda.WG
