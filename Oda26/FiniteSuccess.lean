/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Oda26.WordGraph

/-!
# The word-labelled finite success theorem ([Oda26] §4.5, Theorem 19, Corollary 20)

An *execution* (for a shift `ν`; [Oda26] is `ν = 0`, where `Qₙ = ⌊ξ(a/b)ⁿ + ν⌋`) starts from the
cell graph `G₀^in` on `K` cells over an alphabet `C`, and applies
removal-then-contraction (`P ∘ R`) and lifts by primes `p ∤ b` in any order.  If the final graph has
no infinite walk, then `gcd(Qₙ, M₀·∏ pₖ) > 1` for infinitely many `n`, for every `ξ > 0`,
provided the alphabet hypothesis (H) holds for the primes `S₀` of `M₀`.

* `Oda.WG.Exec` — executions, indexed by the vertex type, the graph, and the lifted modulus.
* `Oda.WG.finite_success` — **[Oda26] Theorem 19**, (20).
* `Oda.WG.composite_frequently` — **[Oda26] Corollary 20**: `Qₙ` is composite infinitely often.

The contraction is admitted with any macro set `B` meeting the hypotheses of Lemma 15 (every
vertex outside `B` deterministic, an anchor in every all-deterministic component); the paper's
choice (all vertices of out-degree `≥ 2` plus one anchor per remaining component) is one instance.

## References

* [Oda26] Y. Odagiri, *Finite graph certificates for composite terms in rational floor sequences*,
  Zenodo, doi:10.5281/zenodo.22997709 (2026).
-/

namespace Oda.WG

open ForMathlib.SubwordComplexity Filter

/-- **An execution** of the word method for the base `a/b` with alphabet `C`: the graph reached and
the product `M` of the primes lifted so far. -/
inductive Exec (a b : ℕ) (ν : ℝ) (C : Set ℤ) : (V : Type) → Graph V ℤ → ℕ → Prop
  | init (K : ℕ) (hK : 0 < K) : Exec a b ν C (Fin K) (cellGraph a b K C ν) 1
  | reduce {V : Type} [Finite V] {G : Graph V ℤ} {M : ℕ} (B : V → Prop) :
      Exec a b ν C V G M → (∀ x, ¬ B x → Det (removal G) x) →
      (∀ x, (∀ y, SameSCC (removal G) x y → Det (removal G) y) →
        ∃ y, SameSCC (removal G) x y ∧ B y) →
      Exec a b ν C V (contract (removal G) B) M
  | lift {V : Type} {G : Graph V ℤ} {M : ℕ} (p : ℕ) [Fact p.Prime] :
      Exec a b ν C V G M → ¬ (p : ℤ) ∣ b → Exec a b ν C (V × ZMod p) (lift G a b p) (M * p)

variable {a b : ℕ} {ν : ℝ}

theorem Exec.M_pos {C : Set ℤ} {V : Type} {G : Graph V ℤ} {M : ℕ} (h : Exec a b ν C V G M) :
    0 < M := by
  induction h with
  | init => exact one_pos
  | reduce => assumption
  | lift p _ _ ih => exact Nat.mul_pos ih (Fact.out : p.Prime).pos

/-- Every graph of an execution covers the carries, as long as `Qₙ` stays prime to `M₀·M`. -/
theorem Exec.models {C : Set ℤ} {V : Type} {G : Graph V ℤ} {M : ℕ} (h : Exec a b ν C V G M)
    (hb : 2 ≤ b) (hab : b < a) (hcop : Nat.Coprime a b) {ξ : ℝ} (hξ : 0 < ξ) {M₀ L : ℕ}
    (hML : M ∣ L) {n₀ : ℕ} (hgcd : ∀ n, n₀ ≤ n → Int.gcd (Qf a b ξ ν n) (M₀ * L) = 1)
    (hH : ∀ n, n₀ ≤ n → cf a b ξ ν n ∈ C) : ∃ n, Models G (cf a b ξ ν) n := by
  induction h with
  | init K hK => exact ⟨n₀, models_cellGraph (by omega) (by omega) hK hH⟩
  | reduce B _ hdet hanchor ih =>
    obtain ⟨n, hn⟩ := ih hML
    have hy := Z32.not_isEventuallyPeriodic_carry (p := a) (q := b) (ν := ν) (by omega) hab hcop
      hξ.ne'
    obtain ⟨n₁, -, h₁⟩ := models_removal hy hn
    obtain ⟨n₂, -, h₂⟩ := models_contract_of_anchor hdet hanchor h₁
    exact ⟨n₂, h₂⟩
  | @lift V G M p _ _ hpb ih =>
    obtain ⟨n, hn⟩ := ih (dvd_trans (dvd_mul_right M p) hML)
    have hp : p.Prime := Fact.out
    have hpL : (p : ℤ) ∣ (M₀ : ℤ) * (L : ℤ) := by
      exact_mod_cast dvd_mul_of_dvd_right (dvd_trans (dvd_mul_left p M) hML) M₀
    obtain ⟨n₁, -, -, h₁⟩ := models_lift (E := G) hpb (Q := Qf a b ξ ν) (y := cf a b ξ ν)
      (fun n => b_mul_Qf_succ n) hn (n' := n₀) fun n hn hd => by
        have := Int.dvd_coe_gcd hd hpL
        rw [hgcd n hn] at this
        have := Int.le_of_dvd one_pos this
        have := hp.two_le
        omega
    exact ⟨n₁, h₁⟩

/-- **[Oda26] Theorem 19 (word-labelled finite success).**  Let `a > b ≥ 2` be coprime, let the
alphabet `C` satisfy (H) for `M₀` (`gcd(Qₙ, M₀) = gcd(Q_{n+1}, M₀) = 1 ⇒ cₙ ∈ C`), and let an
execution end in a graph with no infinite walk, having lifted primes of product `M`.  Then for
every `ξ > 0` and `N` (and `M₀ > 0`), some `n ≥ max(N, 1)` has `gcd(Qₙ, M₀·M) > 1`. -/
@[category research solved, AMS 11 37, ref "Oda26", group "oda26_wordgraph"]
theorem finite_success (hb : 2 ≤ b) (hab : b < a) (hcop : Nat.Coprime a b) {C : Set ℤ}
    {M₀ : ℕ} (hM₀ : 0 < M₀) (hH : ∀ ξ : ℝ, 0 < ξ → ∀ n, Int.gcd (Qf a b ξ ν n) M₀ = 1 →
      Int.gcd (Qf a b ξ ν (n + 1)) M₀ = 1 → cf a b ξ ν n ∈ C)
    {V : Type} {G : Graph V ℤ} {M : ℕ} (hex : Exec a b ν C V G M)
    (hnone : ∀ (v : ℕ → V) (w : ℕ → List ℤ), ¬ ∀ i, G (v i) (w i) (v (i + 1))) :
    ∀ ξ : ℝ, 0 < ξ → ∀ N : ℕ, ∃ n, max N 1 ≤ n ∧ 1 < Int.gcd (Qf a b ξ ν n) (M₀ * M) := by
  intro ξ hξ N
  by_contra hcon
  push Not at hcon
  have hgcd : ∀ n, max N 1 ≤ n → Int.gcd (Qf a b ξ ν n) (M₀ * M) = 1 := by
    intro n hn
    have h1 := hcon n hn
    have h0 : Int.gcd (Qf a b ξ ν n) (M₀ * M) ≠ 0 := by
      rw [Ne, Int.gcd_eq_zero_iff]
      have := hex.M_pos
      intro h
      have : (M₀ * M : ℤ) ≠ 0 := by positivity
      exact this h.2
    omega
  have hcop' : ∀ n, max N 1 ≤ n → Int.gcd (Qf a b ξ ν n) M₀ = 1 := by
    intro n hn
    have := Int.isCoprime_iff_gcd_eq_one.2 (hgcd n hn)
    push_cast at this
    exact Int.isCoprime_iff_gcd_eq_one.1 this.of_mul_right_left
  obtain ⟨n, hn⟩ := hex.models hb hab hcop hξ (M₀ := M₀) dvd_rfl hgcd fun n hn =>
    hH ξ hξ n (hcop' n hn) (hcop' (n + 1) (by omega))
  obtain ⟨v, w, t, hc, -⟩ := hn
  exact hnone v w hc.edge

/-- **[Oda26] Corollary 20.**  Under the hypotheses of Theorem 19 (with `M₀ > 0`), `Qₙ` is
composite for infinitely many `n`, for every `ξ > 0`. -/
@[category research solved, AMS 11 37, ref "Oda26", group "oda26_wordgraph"]
theorem composite_frequently (hb : 2 ≤ b) (hab : b < a) (hcop : Nat.Coprime a b) {C : Set ℤ}
    {M₀ : ℕ} (hM₀ : 0 < M₀) (hH : ∀ ξ : ℝ, 0 < ξ → ∀ n, Int.gcd (Qf a b ξ ν n) M₀ = 1 →
      Int.gcd (Qf a b ξ ν (n + 1)) M₀ = 1 → cf a b ξ ν n ∈ C)
    {V : Type} {G : Graph V ℤ} {M : ℕ} (hex : Exec a b ν C V G M)
    (hnone : ∀ (v : ℕ → V) (w : ℕ → List ℤ), ¬ ∀ i, G (v i) (w i) (v (i + 1))) {ξ : ℝ}
    (hξ : 0 < ξ) : ∃ᶠ n in atTop, 1 < Qf a b ξ ν n ∧ ¬ Prime (Qf a b ξ ν n) := by
  have hM := hex.M_pos
  have hT := tendsto_Qf (a := a) (b := b) (ξ := ξ) (ν := ν) (by omega) hab hξ
  rw [frequently_atTop]
  intro N
  obtain ⟨N', hN'⟩ := eventually_atTop.1 (tendsto_atTop.1 hT ((M₀ * M : ℕ) + 1))
  obtain ⟨n, hn, hg⟩ := finite_success hb hab hcop hM₀ hH hex hnone ξ hξ (max N N')
  have hQ := hN' n (by omega)
  have hpos : (0 : ℤ) < (M₀ : ℤ) * M := by positivity
  refine ⟨n, by omega, by omega, ?_⟩
  have hgd : (Int.gcd (Qf a b ξ ν n) ((M₀ : ℤ) * M) : ℤ) ∣ Qf a b ξ ν n := Int.gcd_dvd_left _ _
  have hgle : (Int.gcd (Qf a b ξ ν n) ((M₀ : ℤ) * M) : ℤ) ≤ (M₀ : ℤ) * M :=
    Int.le_of_dvd hpos (Int.gcd_dvd_right _ _)
  push_cast at hQ
  exact not_prime_of_dvd hgd (by exact_mod_cast hg) (by omega)

end Oda.WG
