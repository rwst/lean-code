/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Data.Matrix.Mul
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# ℕ-rational sequences (YAH §3; Berstel, Soittola)

A sequence of naturals is *ℕ-rational* when it is given by a linear-algebraic recurrence
`xₙ = vᵀ Mⁿ w` for a nonnegative matrix `M` and nonnegative vectors `v, w` (Definition 3.4). These
are exactly the coefficient sequences of ℕ-rational formal power series; in the YAH development they
arise as the values matrix interpretations take along powers, and their growth controls
termination/derivational complexity.

* `IsNRationalSequence x` — **Definition 3.4**: there are a dimension `d`, a matrix `M ∈ ℕ^{d×d}`
  and vectors `v, w ∈ ℕ^d` with `xₙ = vᵀ Mⁿ w` for all `n` (here `vᵀ Mⁿ w = v ⬝ᵥ (Mⁿ *ᵥ w)`).
* `theorem_3_5` — **Theorem 3.5**, a consequence of Berstel's theorem [RB10, Theorem 8.1.1] (cf. the
  remark of Soittola [Soi76, p. 318]): every ℕ-rational sequence splits, for some period `p > 0` and
  offset `m`, into `p` residue-class subsequences `k ↦ x_{m+kp+j}`, each either eventually zero or
  **asymptotically equivalent** to `P(k)·αᵏ` for a nonzero polynomial `P` and a constant `α > 0`
  (its `k`th element is `(1 + o(1)) P(k) αᵏ`), and in particular each eventually monotonically
  nondecreasing. Recorded as a **cited axiom** — the underlying Berstel/Soittola spectral analysis
  (Perron–Frobenius + Jordan structure) is not formalized.
* `theorem_3_5_geometric` — the elementary `d = 1` case, **proved**: a positive geometric sequence
  `xₙ = c·aⁿ` satisfies the conclusion (`p = 1`, `P = c`, `α = a`).
* `corollary_3_6` — **Corollary 3.6**, **fully proved from `theorem_3_5`** (no extra axiom): there is
  no ℕ-rational sequence with `x_{8n+1} > x_{9n+2}` for all `n ≥ 1`. Uses only the eventual-monotonicity
  half of Theorem 3.5 (via the helper `eventually_step`), so it needs none of the spectral input. (The
  hypothesis is the `n ≥ 1` form — the proof only inspects one large `n` — which is what the
  matrix-interpretation lower bound `theorem_3_8` consumes; it implies the literal `∀ n` reading.)
-/

namespace StringRewriting.NRational

open Matrix Asymptotics Filter

/-- **Definition 3.4** (ℕ-rational sequence). A sequence `x : ℕ → ℕ` is *ℕ-rational* if there are a
dimension `d`, a matrix `M ∈ ℕ^{d×d}` and vectors `v, w ∈ ℕ^d` such that `xₙ = vᵀ Mⁿ w` for all `n`,
where `vᵀ Mⁿ w` is the scalar `v ⬝ᵥ (Mⁿ *ᵥ w)`. -/
@[category API, AMS 68, ref "YAH", group "n_rational_sequence"]
def IsNRationalSequence (x : ℕ → ℕ) : Prop :=
  ∃ (d : ℕ) (M : Matrix (Fin d) (Fin d) ℕ) (v w : Fin d → ℕ),
    ∀ n, x n = v ⬝ᵥ (M ^ n *ᵥ w)

/- Registry node for the informal result that Theorem 3.5 rests on. -/
informal_result "berstel-theorem"
  latex "Berstel's theorem (Berstel–Reutenauer, *Noncommutative Rational Series with Applications*, Theorem 8.1.1): the asymptotic growth structure of ℕ-rational sequences. The coefficient sequence of an ℕ-rational series, split along arithmetic-progression subsequences k ↦ x_(m+kp+j), is governed by a dominant positive eigenvalue α > 0 together with a polynomial factor — each subsequence is (1 + o(1)) P(k) αᵏ for a nonzero polynomial P, hence eventually monotone. Closely tied to Soittola's theorem [Soi76], which characterizes the ℕ-rational series among the ℝ₊-rational ones."
  refs "RB10" "Soi76"

/-- **Theorem 3.5** (a consequence of Berstel's theorem [RB10, Theorem 8.1.1]; see also Soittola
[Soi76, p. 318]). For an ℕ-rational sequence `x` there are an offset `m` and a period `p > 0` such
that, for each residue `j < p`, the subsequence `k ↦ x_{m+kp+j}` is **either eventually zero, or**
asymptotically equivalent (as `k → ∞`) to `P(k)·αᵏ` for some nonzero polynomial `P : ℝ[X]` and
constant `α > 0` — i.e. its `k`th element is `(1 + o(1)) P(k) αᵏ` — and in either case is eventually
monotonically nondecreasing. (The eventually-zero alternative is the *sound* reading: the paper's
statement implicitly takes the subsequences nonvanishing, but without this disjunct the claim is
false for, e.g., the zero sequence — which is ℕ-rational.)

Recorded as a cited axiom: the Berstel/Soittola spectral analysis behind the asymptotics
(Perron–Frobenius dominant eigenvalue together with the Jordan/cyclic structure) is not formalized
here; only the elementary `d = 1` case is proved, in `theorem_3_5_geometric`. -/
@[category research solved, AMS 68 11, ref "RB10" "Soi76", group "n_rational_sequence",
  informal_uses "berstel-theorem"]
axiom theorem_3_5 (x : ℕ → ℕ) (hx : IsNRationalSequence x) :
    ∃ m p : ℕ, 0 < p ∧ ∀ j < p,
      ((∃ N : ℕ, ∀ k ≥ N, x (m + k * p + j) = 0) ∨
        ∃ (P : Polynomial ℝ) (α : ℝ), P ≠ 0 ∧ 0 < α ∧
          (fun k : ℕ => (x (m + k * p + j) : ℝ)) ~[atTop] (fun k : ℕ => P.eval (k : ℝ) * α ^ k)) ∧
      (∃ N : ℕ, ∀ k ≥ N, x (m + k * p + j) ≤ x (m + (k + 1) * p + j))

/-- The `d = 1` (geometric) case of Theorem 3.5, **proved directly**: a positive geometric sequence
`xₙ = c·aⁿ` (`c > 0`, `a ≥ 1`) — the simplest ℕ-rational sequence, from `M = (a)`, `v = (c)`,
`w = (1)` — satisfies the conclusion with period `p = 1`, constant polynomial `P = c` and `α = a`
(here the asymptotic equivalence is even an equality, so `o(1) = 0`). The general case rests on the
Berstel/Soittola spectral theory and is only cited (`theorem_3_5`). -/
@[category research solved, AMS 68 11, ref "YAH", group "n_rational_sequence"]
theorem theorem_3_5_geometric (c a : ℕ) (hc : 0 < c) (ha : 1 ≤ a) :
    ∃ m p : ℕ, 0 < p ∧ ∀ j < p,
      ((∃ N : ℕ, ∀ k ≥ N, (fun n => c * a ^ n) (m + k * p + j) = 0) ∨
        ∃ (P : Polynomial ℝ) (α : ℝ), P ≠ 0 ∧ 0 < α ∧
          (fun k : ℕ => ((fun n => c * a ^ n) (m + k * p + j) : ℝ)) ~[atTop]
            (fun k : ℕ => P.eval (k : ℝ) * α ^ k)) ∧
      (∃ N : ℕ, ∀ k ≥ N,
        (fun n => c * a ^ n) (m + k * p + j) ≤ (fun n => c * a ^ n) (m + (k + 1) * p + j)) := by
  refine ⟨0, 1, one_pos, fun j hj => ?_⟩
  obtain rfl : j = 0 := by omega
  simp only [Nat.zero_add, Nat.mul_one, Nat.add_zero]
  refine ⟨Or.inr ⟨Polynomial.C (c : ℝ), (a : ℝ), ?_, ?_, ?_⟩, 0, fun k _ => ?_⟩
  · exact Polynomial.C_ne_zero.mpr (by exact_mod_cast hc.ne')
  · exact_mod_cast (by omega : 0 < a)
  · have : (fun k : ℕ => ((c * a ^ k : ℕ) : ℝ))
        = (fun k : ℕ => (Polynomial.C (c : ℝ)).eval (k : ℝ) * (a : ℝ) ^ k) := by
      funext k; rw [Polynomial.eval_C]; push_cast; ring
    rw [this]
  · exact Nat.mul_le_mul le_rfl (Nat.pow_le_pow_right (by omega) (by omega))

/-- From the per-residue eventual monotonicity of Theorem 3.5, a *uniform* eventual step: for all
sufficiently large `i`, `x i ≤ x (i + p)` (any `i ≥ A` lies in some residue class `(i - m) % p`
beyond its threshold). -/
private theorem eventually_step {x : ℕ → ℕ} {m p : ℕ} (hp : 0 < p)
    (hmono : ∀ j, j < p → ∃ N, ∀ k, k ≥ N → x (m + k * p + j) ≤ x (m + (k + 1) * p + j)) :
    ∃ A, ∀ i, i ≥ A → x i ≤ x (i + p) := by
  choose! Nf hNf using hmono
  refine ⟨m + ((Finset.range p).sup Nf + 1) * p, fun i hi => ?_⟩
  set d := i - m with hd
  have hid : i = m + d := by omega
  have hjlt : d % p < p := Nat.mod_lt _ hp
  have hdge : ((Finset.range p).sup Nf + 1) * p ≤ d := by omega
  have hk : (Finset.range p).sup Nf + 1 ≤ d / p := (Nat.le_div_iff_mul_le hp).mpr hdge
  have hkN : Nf (d % p) ≤ d / p :=
    le_trans (Finset.le_sup (Finset.mem_range.mpr hjlt)) (by omega)
  have hdm : (d / p) * p + d % p = d := by rw [mul_comm]; exact Nat.div_add_mod d p
  have e1 : i = m + (d / p) * p + d % p := by omega
  rw [e1]
  have e3 : m + (d / p) * p + d % p + p = m + (d / p + 1) * p + d % p := by ring
  rw [e3]
  exact hNf (d % p) hjlt (d / p) hkN

/-- **Corollary 3.6** (proved from Theorem 3.5): there is **no** ℕ-rational sequence with
`x_{8n+1} > x_{9n+2}` for all `n ≥ 1`. Following the paper: take `n = qp − 1` with `p` the period of
Theorem 3.5; then `9n+2 = (8n+1) + qp`, so `8n+1` and `9n+2` lie in the same residue-class
subsequence, which is eventually nondecreasing — giving `x_{8n+1} ≤ x_{9n+2}` for large `q`, against
the strict inequality. (Rests on the cited `theorem_3_5`; everything else here is proved. The
hypothesis is stated for `n ≥ 1`, the form the lower bound `theorem_3_8` produces — the proof only
examines one large `n` (here `n ≥ 6`), so this is no weaker in substance than the `∀ n` reading.) -/
@[category research solved, AMS 68 11, ref "YAH", group "n_rational_sequence"]
theorem corollary_3_6 :
    ¬ ∃ x : ℕ → ℕ, IsNRationalSequence x ∧ ∀ n, 1 ≤ n → x (8 * n + 1) > x (9 * n + 2) := by
  rintro ⟨x, hx, hgt⟩
  obtain ⟨m, p, hp, hconc⟩ := theorem_3_5 x hx
  obtain ⟨A, hstep⟩ := eventually_step hp (fun j hj => (hconc j hj).2)
  have multi : ∀ t i, i ≥ A → x i ≤ x (i + t * p) := by
    intro t
    induction t with
    | zero => intro i _; simp
    | succ s ih =>
      intro i hi
      calc x i ≤ x (i + s * p) := ih i hi
        _ ≤ x (i + s * p + p) := hstep _ (by omega)
        _ = x (i + (s + 1) * p) := by ring_nf
  set t := A + 7 with ht
  have hQ : 1 ≤ t * p := Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos (by omega) hp).ne'
  have htp : t ≤ t * p := Nat.le_mul_of_pos_right t hp
  set n := t * p - 1 with hn
  have hn1 : 1 ≤ n := by omega
  have h81 : 8 * n + 1 ≥ A := by omega
  have key : 9 * n + 2 = (8 * n + 1) + t * p := by omega
  have hle := multi t (8 * n + 1) h81
  rw [← key] at hle
  exact absurd hle (not_le.mpr (hgt n hn1))

end StringRewriting.NRational
