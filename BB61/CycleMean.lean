/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB61.Pressure
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The max-plus certificate: an entropy-free growth bound

Formal companion of `note-1061-R2b.html` (work package R2b of
`plan-BB61-counterexample.html`).

`BB61/Pressure.lean` certifies the *pressure* of the window potential by exhibiting a
positive vector `vv` with

    bb * (w0 s * vv (t0 s) + w1 s * vv (t1 s))  ≤  aa * vv s      for every state `s`,

a Collatz–Wielandt bound: the weighted **path sum** grows no faster than `(aa/bb)^k`
(`BB61.TwoAddSqrt3.psum_le_pow`).  R2b needs the same data read in the max-plus semiring.
Replacing the sum by a maximum turns the hypothesis into

    bb * (w s c * vv (t s c))  ≤  aa * vv s                       for every `s` and `c`,

and the conclusion into a bound on the weight **product** along every cycle — an
ergodic-optimisation certificate, with no entropy term anywhere in it:

    bb^n * ∏_{i<n} w (s i) (c i)  ≤  aa^n      for every closed walk of length `n`.

That is exactly `max_μ ∫ ψ dμ ≤ log(aa/bb)` over shift-invariant `μ`, since for a
locally constant potential the maximum ergodic average is the maximum cycle mean
(note-1061-R2b.html, Theorem 2) — the *entropy-free* half of what
`BB61/PressureCriterion.lean` obtains with entropy.

Two things make this cheap.  The path argument is a two-line induction: the certificate
telescopes along the walk, and at a cycle the endpoint value cancels because `vv` is
positive.  And `max ≤ sum` for natural numbers means the max-plus hypothesis is *implied*
by the one `BB61/Pressure.lean` already discharges by `decide` — so the same
`certOK_true` carries both certificates, and no new numerical data enters this file.

## What is proved here

* `BB61.CycleMean.Cert` — the max-plus hypothesis, for an arbitrary state type.
* `cert_of_sum` — it follows from the summed hypothesis, since every term of a sum of
  naturals is at most the sum.
* `walk_le` — the telescoping bound along an arbitrary walk.
* `cycle_le`, `cycle_le_real` — the cycle bound, in `ℕ` and as `∏ w ≤ (aa/bb)^n`.
* `TwoAddSqrt3.cycle_prod_le` — the instance at `α = 2 + √3`, on the data of
  `BB61/Pressure.lean`.
-/

namespace BB61
namespace CycleMean

variable {S : Type*}

/-- The max-plus Collatz–Wielandt hypothesis: one inequality per state and letter.

`v` is a node potential, `a / b` the claimed bound on the growth rate.  Compare
`BB61.TwoAddSqrt3.cert`, which is the same statement with the two letters summed. -/
def Cert (t : S → Bool → S) (w : S → Bool → ℕ) (v : S → ℕ) (a b : ℕ) : Prop :=
  ∀ s c, b * (w s c * v (t s c)) ≤ a * v s

/-- `max ≤ sum`: the summed certificate implies the max-plus one, at the same potential
and the same ratio.  This is the whole of `β ≤ P` in this setting — the entropy the
pressure certificate pays for and this one does not. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cert_of_sum {t : S → Bool → S} {w : S → Bool → ℕ} {v : S → ℕ} {a b : ℕ}
    (h : ∀ s, b * (w s false * v (t s false) + w s true * v (t s true)) ≤ a * v s) :
    Cert t w v a b := by
  intro s c
  cases c
  · exact le_trans (Nat.mul_le_mul_left b (Nat.le_add_right _ _)) (h s)
  · exact le_trans (Nat.mul_le_mul_left b (Nat.le_add_left _ _)) (h s)

/-- **The telescoping bound.**  Along any walk `s 0 → s 1 → …` reading the letters `c`,
the weight product times the endpoint potential is at most `(a/b)^n` times the starting
potential. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem walk_le {t : S → Bool → S} {w : S → Bool → ℕ} {v : S → ℕ} {a b : ℕ}
    (hc : Cert t w v a b) (s : ℕ → S) (c : ℕ → Bool)
    (hs : ∀ i, s (i + 1) = t (s i) (c i)) (n : ℕ) :
    b ^ n * ((∏ i ∈ Finset.range n, w (s i) (c i)) * v (s n)) ≤ a ^ n * v (s 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : b * (w (s n) (c n) * v (s (n + 1))) ≤ a * v (s n) := by
      rw [hs n]; exact hc (s n) (c n)
    calc b ^ (n + 1) * ((∏ i ∈ Finset.range (n + 1), w (s i) (c i)) * v (s (n + 1)))
        = b ^ n * ((∏ i ∈ Finset.range n, w (s i) (c i))
            * (b * (w (s n) (c n) * v (s (n + 1))))) := by
          rw [Finset.prod_range_succ]; ring
      _ ≤ b ^ n * ((∏ i ∈ Finset.range n, w (s i) (c i)) * (a * v (s n))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hstep)
      _ = a * (b ^ n * ((∏ i ∈ Finset.range n, w (s i) (c i)) * v (s n))) := by ring
      _ ≤ a * (a ^ n * v (s 0)) := Nat.mul_le_mul_left _ ih
      _ = a ^ (n + 1) * v (s 0) := by ring

/-- **The cycle bound.**  On a closed walk the endpoint potential cancels, and what is
left is a statement about the walk alone: its weight product is at most `(a/b)^n`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cycle_le {t : S → Bool → S} {w : S → Bool → ℕ} {v : S → ℕ} {a b : ℕ}
    (hc : Cert t w v a b) (hv : ∀ s, 0 < v s) (s : ℕ → S) (c : ℕ → Bool)
    (hs : ∀ i, s (i + 1) = t (s i) (c i)) (n : ℕ) (hcyc : s n = s 0) :
    b ^ n * ∏ i ∈ Finset.range n, w (s i) (c i) ≤ a ^ n := by
  have h := walk_le hc s c hs n
  rw [hcyc] at h
  have h' : (b ^ n * ∏ i ∈ Finset.range n, w (s i) (c i)) * v (s 0) ≤ a ^ n * v (s 0) := by
    calc (b ^ n * ∏ i ∈ Finset.range n, w (s i) (c i)) * v (s 0)
        = b ^ n * ((∏ i ∈ Finset.range n, w (s i) (c i)) * v (s 0)) := by ring
      _ ≤ a ^ n * v (s 0) := h
  exact Nat.le_of_mul_le_mul_right h' (hv (s 0))

/-- The cycle bound as a growth rate: the mean weight along any cycle is at most `a/b`. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cycle_le_real {t : S → Bool → S} {w : S → Bool → ℕ} {v : S → ℕ} {a b : ℕ}
    (hb : 0 < b) (hc : Cert t w v a b) (hv : ∀ s, 0 < v s) (s : ℕ → S) (c : ℕ → Bool)
    (hs : ∀ i, s (i + 1) = t (s i) (c i)) (n : ℕ) (hcyc : s n = s 0) :
    ((∏ i ∈ Finset.range n, w (s i) (c i) : ℕ) : ℝ) ≤ ((a : ℝ) / b) ^ n := by
  have hbR : (0 : ℝ) < (b : ℝ) ^ n := by positivity
  have h := cycle_le hc hv s c hs n hcyc
  have hR : ((b : ℝ)) ^ n * ((∏ i ∈ Finset.range n, w (s i) (c i) : ℕ) : ℝ)
      ≤ ((a : ℝ)) ^ n := by
    exact_mod_cast (Nat.cast_le (α := ℝ)).mpr h
  rw [div_pow, le_div_iff₀ hbR, mul_comm]
  exact hR

end CycleMean

namespace TwoAddSqrt3

open CycleMean

/-- The max-plus certificate at `α = 2 + √3`, on the very data `BB61/Pressure.lean`
discharges by `decide`: no new numbers, only `max ≤ sum`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem certMax : Cert tgtB wB vv aa bb :=
  cert_of_sum fun s => by simpa [wB, tgtB] using cert s

/-- **The entropy-free growth bound at `α = 2 + √3`.**  Every cycle of the window digraph
has weight product at most `(aa/bb)^n`; equivalently `∫ ψ dμ ≤ log(aa/bb)` for every
shift-invariant `μ`, with no entropy term. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_61"]
theorem cycle_prod_le (s : ℕ → St) (c : ℕ → Bool)
    (hs : ∀ i, s (i + 1) = tgtB (s i) (c i)) (n : ℕ) (hcyc : s n = s 0) :
    ((∏ i ∈ Finset.range n, wB (s i) (c i) : ℕ) : ℝ) ≤ ((aa : ℝ) / bb) ^ n :=
  cycle_le_real (by norm_num [bb]) certMax one_le_vv s c hs n hcyc

end TwoAddSqrt3

end BB61
