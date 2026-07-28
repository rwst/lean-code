/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import TH.DigitBlocks.GapPrinciples
import ForMathlib.Combinatorics.SubwordComplexity
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Theorem B3: the Morse–Hedlund complexity floor for the binary expansion of `3^m`

Milestone **M-7 = Theorem B3** of the digit-block plan ([A4+] §3.3), the
**capstone**: the binary digit string of `3^m` eventually has full low-order
subword complexity `p_{3^m}(n) ≥ n + 1`.

The proof is a two-line contraposition of the two shipped pieces:

* if the window `[0, M)` (`M := ⌊log₂ 3^m⌋`) had `≤ n` distinct length-`n`
  factors, the **finite Morse–Hedlund floor** M-6
  (`ForMathlib.SubwordComplexity.finite_morse_hedlund`) would produce a
  `p`-periodic factor of length `M - 2n` with `1 ≤ p ≤ n`, deep in the
  expansion;
* but the **gap principle P** M-5 (`TH.gap_principle`) forbids any deep
  `p`-periodic window: it bounds `(M − x)·log 2` by `≈ p·(depth)·log m`, so a
  period-`p` run reaching depth `M − x ≈ M` is impossible once `M ≫ n² log m`.

Combining them:

* `log_le_of_lowComplexity` — the core contradiction, in effective form:
  low complexity forces `(M − (3n+2))·log 2 ≤ 4·C(4,1)·n²·log 3·max(log(2m+n),1)`.
* `three_pow_complexity_ge` — **Theorem B3**: for every `n ≥ 1`,
  `n + 1 ≤ p_{3^m}(n)` for all sufficiently large `m` (`∀ᶠ m in atTop`).  Since
  `M = ⌊log₂ 3^m⌋ ≥ m` grows linearly while the Baker bound grows like `log m`,
  the effective threshold `m₀(n)` is where `M` overtakes `4C(4,1)n²(log3/log2)
  log(2m+n)`.

Footprint std3 + [BW93] (via `gap_principle`); the complexity side is
axiom-free.  This is the exact analogue, for the finite digit string of a single
`3^m`, of the Morse–Hedlund rung the M4 program proved for the steering word of
`(3/2)^n` — the linear-forms optimum (see [A4+] §2.3 for the ceiling: superlinear
per-string complexity is a different, walled program).

## References

* [A4+] `plan-A4+.html` (this repository, 2026-07): §3.3 (B3), §2.3 (ceiling).
* [Ste80] C. L. Stewart, *On the representation of an integer in two different
  bases*, J. reine angew. Math. **319** (1980).  (The digit-program anchor.)
* [MH38] M. Morse, G. A. Hedlund, *Symbolic dynamics*, Amer. J. Math. **60**
  (1938).  (The complexity threshold; finite form in
  `ForMathlib/Combinatorics/SubwordComplexity.lean`.)
-/

open Filter Asymptotics ForMathlib.SubwordComplexity

namespace TH

/-- Linear-versus-logarithmic domination: the linear term `m·log 2` eventually
dominates `D·max(log(2m+n),1) + (3n+2)·log 2`.  Pure asymptotics
(`Real.log =o id`); consumed by `three_pow_complexity_ge`. -/
lemma linear_dominates_log (n : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    ∀ᶠ m : ℕ in atTop,
      D * max (Real.log ((2 * m + n : ℕ) : ℝ)) 1 + (3 * n + 2) * Real.log 2
        < (m : ℝ) * Real.log 2 := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have htend : Tendsto (fun m : ℕ => ((2 * m + n : ℕ) : ℝ)) atTop atTop := by
    apply tendsto_natCast_atTop_atTop.comp
    exact tendsto_atTop_mono (fun m => by omega : ∀ m : ℕ, m ≤ 2 * m + n) tendsto_id
  have hlogo : (fun m : ℕ => Real.log ((2 * m + n : ℕ) : ℝ)) =o[atTop] (fun m : ℕ => (m : ℝ)) := by
    have hbo : (fun m : ℕ => ((2 * m + n : ℕ) : ℝ)) =O[atTop] (fun m : ℕ => (m : ℝ)) := by
      rw [isBigO_iff]
      refine ⟨2 + (n : ℝ), ?_⟩
      filter_upwards [eventually_ge_atTop 1] with m hm1
      have hm1' : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ ((2*m+n:ℕ):ℝ)),
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (m:ℝ))]
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) n, hm1']
    have h2 := Real.isLittleO_log_id_atTop.comp_tendsto htend
    rw [Function.id_comp] at h2
    exact h2.trans_isBigO hbo
  have hDlogo : (fun m : ℕ => D * Real.log ((2 * m + n : ℕ) : ℝ)) =o[atTop] (fun m : ℕ => (m : ℝ)) :=
    hlogo.const_mul_left D
  have e1 : ∀ᶠ m : ℕ in atTop,
      D * Real.log ((2 * m + n : ℕ) : ℝ) ≤ (Real.log 2 / 8) * (m : ℝ) := by
    have hdef := hDlogo.def (show (0:ℝ) < Real.log 2 / 8 by positivity)
    filter_upwards [hdef] with m hm
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hm
    have hmabs : |(m:ℝ)| = (m:ℝ) := abs_of_nonneg (by positivity)
    rw [hmabs] at hm
    exact le_trans (le_abs_self _) hm
  have e2 : ∀ᶠ m : ℕ in atTop,
      D + (3 * n + 2) * Real.log 2 ≤ (Real.log 2 / 4) * (m : ℝ) := by
    have htlin : Tendsto (fun m : ℕ => (Real.log 2 / 4) * (m : ℝ)) atTop atTop :=
      Tendsto.const_mul_atTop (by positivity) tendsto_natCast_atTop_atTop
    exact htlin.eventually_ge_atTop _
  have e3 : ∀ᶠ m : ℕ in atTop,
      max (Real.log ((2 * m + n : ℕ) : ℝ)) 1 ≤ Real.log ((2 * m + n : ℕ) : ℝ) + 1 := by
    filter_upwards [eventually_ge_atTop 1] with m hm1
    have hm1' : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
    have hlognn : 0 ≤ Real.log ((2 * m + n : ℕ) : ℝ) :=
      Real.log_nonneg (by push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) n])
    exact max_le (by linarith) (by linarith)
  filter_upwards [e1, e2, e3, eventually_ge_atTop 1] with m hm1 hm2 hm3 hm0
  have hm0' : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm0
  calc D * max (Real.log ((2 * m + n : ℕ) : ℝ)) 1 + (3 * n + 2) * Real.log 2
      ≤ D * (Real.log ((2 * m + n : ℕ) : ℝ) + 1) + (3 * n + 2) * Real.log 2 := by
        have := mul_le_mul_of_nonneg_left hm3 hD; linarith
    _ = D * Real.log ((2 * m + n : ℕ) : ℝ) + (D + (3 * n + 2) * Real.log 2) := by ring
    _ ≤ (Real.log 2 / 8) * (m : ℝ) + (Real.log 2 / 4) * (m : ℝ) := by linarith [hm1, hm2]
    _ < (m : ℝ) * Real.log 2 := by nlinarith [hlog2, hm0']

/-- **The core contradiction (effective form).**  If the window `[0, M)` of the
binary expansion of `3^m` (`M := ⌊log₂ 3^m⌋`, `M ≥ 4n+1`) has at most `n`
distinct length-`n` factors, then `M` is bounded:
`(M − (3n+2))·log 2 ≤ 4·C(4,1)·n²·log 3·max(log(2m+n),1)`.  Proof: M-6 hands a
deep `p`-periodic factor (`p ≤ n`) to `gap_principle`, which caps its depth. -/
lemma log_le_of_lowComplexity {n m : ℕ} (hn : 1 ≤ n)
    (hM : 4 * n + 1 ≤ Nat.log 2 (3 ^ m))
    (hc : subwordComplexity (fun i => (3 ^ m).testBit i) (Nat.log 2 (3 ^ m)) n ≤ n) :
    ((Nat.log 2 (3 ^ m) : ℝ) - (3 * n + 2)) * Real.log 2
      ≤ 4 * BakerWustholz.C 4 1 * (n : ℝ) ^ 2 * Real.log 3
          * max (Real.log ((2 * m + n : ℕ) : ℝ)) 1 := by
  set M := Nat.log 2 (3 ^ m) with hMdef
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · exfalso; have : M = 0 := by rw [hMdef]; decide
      omega
    · exact h
  have h3n : 3 * n ≤ M := by omega
  obtain ⟨a, p, hp1, hpn, halen, hper0⟩ :=
    finite_morse_hedlund (fun i => (3 ^ m).testBit i) hn h3n hc
  -- halen : a + (M - 2 * n) ≤ M
  have ha2n : a ≤ 2 * n := by omega
  -- feed the periodic factor to the gap principle, with x = a + 1 (so x ≥ 1)
  have hgap := gap_principle (m := m) (x := a + 1) (y := a + (M - 2 * n)) (p := p)
    hm1 hp1 (by omega) (by omega) (by omega) (by omega)
    (by
      intro i hxi hiy
      exact hper0 i (by omega) (by omega))
  rw [← hMdef] at hgap
  -- normalise the "depth" factor  (M + 2p - y) = 2p + 2n - a
  have hMge : 2 * n ≤ M := by omega
  have hV : (M : ℝ) + 2 * (p : ℝ) - ((a + (M - 2 * n) : ℕ) : ℝ)
      = 2 * (p : ℝ) + 2 * (n : ℝ) - (a : ℝ) := by
    push_cast [Nat.cast_sub hMge]; ring
  rw [hV] at hgap
  -- constants
  have hC0 : (0:ℝ) ≤ BakerWustholz.C 4 1 := C_one_nonneg 4
  have hlog3nn : (0:ℝ) ≤ Real.log 3 := log_three_pos'.le
  have hlog2 : (0:ℝ) < Real.log 2 := log_two_pos'
  have hmaxp_nn : (0:ℝ) ≤ max (Real.log ((2 * m + p : ℕ) : ℝ)) 1 :=
    le_trans zero_le_one (le_max_right _ _)
  have hpn' : (p:ℝ) ≤ (n:ℝ) := by exact_mod_cast hpn
  have hp_nn : (0:ℝ) ≤ (p:ℝ) := by positivity
  have ha2n' : (a:ℝ) ≤ 2 * (n:ℝ) := by exact_mod_cast ha2n
  have hVle : 2 * (p:ℝ) + 2 * (n:ℝ) - (a:ℝ) ≤ 4 * (n:ℝ) := by nlinarith [hpn']
  have hV_nn : (0:ℝ) ≤ 2 * (p:ℝ) + 2 * (n:ℝ) - (a:ℝ) := by nlinarith [hp_nn, ha2n']
  have hmaxle : max (Real.log ((2 * m + p : ℕ) : ℝ)) 1
      ≤ max (Real.log ((2 * m + n : ℕ) : ℝ)) 1 := by
    apply max_le_max _ (le_refl 1)
    apply Real.log_le_log (by positivity)
    exact_mod_cast (by omega : 2 * m + p ≤ 2 * m + n)
  -- bound the product term
  have key : BakerWustholz.C 4 1 * (p:ℝ) * Real.log 3 * (2 * (p:ℝ) + 2 * (n:ℝ) - (a:ℝ))
        * max (Real.log ((2 * m + p : ℕ) : ℝ)) 1
      ≤ 4 * BakerWustholz.C 4 1 * (n:ℝ) ^ 2 * Real.log 3
        * max (Real.log ((2 * m + n : ℕ) : ℝ)) 1 := by
    have hClog3 : (0:ℝ) ≤ BakerWustholz.C 4 1 * Real.log 3 := mul_nonneg hC0 hlog3nn
    have hpV : (p:ℝ) * (2 * (p:ℝ) + 2 * (n:ℝ) - (a:ℝ)) ≤ (n:ℝ) * (4 * (n:ℝ)) :=
      mul_le_mul hpn' hVle hV_nn (by positivity)
    have hpV_nn : (0:ℝ) ≤ (p:ℝ) * (2 * (p:ℝ) + 2 * (n:ℝ) - (a:ℝ)) := mul_nonneg hp_nn hV_nn
    calc BakerWustholz.C 4 1 * (p:ℝ) * Real.log 3 * (2 * (p:ℝ) + 2 * (n:ℝ) - (a:ℝ))
            * max (Real.log ((2 * m + p : ℕ) : ℝ)) 1
        = (BakerWustholz.C 4 1 * Real.log 3) * ((p:ℝ) * (2 * (p:ℝ) + 2 * (n:ℝ) - (a:ℝ)))
            * max (Real.log ((2 * m + p : ℕ) : ℝ)) 1 := by ring
      _ ≤ (BakerWustholz.C 4 1 * Real.log 3) * ((n:ℝ) * (4 * (n:ℝ)))
            * max (Real.log ((2 * m + n : ℕ) : ℝ)) 1 := by
          apply mul_le_mul (mul_le_mul (le_refl _) hpV hpV_nn hClog3) hmaxle hmaxp_nn
          exact mul_nonneg hClog3 (by positivity)
      _ = 4 * BakerWustholz.C 4 1 * (n:ℝ) ^ 2 * Real.log 3
            * max (Real.log ((2 * m + n : ℕ) : ℝ)) 1 := by ring
  -- combine with the log2-linear front factor
  have hpa : (p:ℝ) + (a:ℝ) ≤ 3 * (n:ℝ) := by nlinarith [hpn', ha2n']
  have hslack : (0:ℝ) ≤ (3 * (n:ℝ) - (a:ℝ) - (p:ℝ)) * Real.log 2 :=
    mul_nonneg (by linarith [hpa]) hlog2.le
  -- combine hgap with the product bound, then expand the front factors
  have hstep : ((M:ℝ) - ((a + 1 : ℕ) : ℝ)) * Real.log 2
      ≤ 4 * BakerWustholz.C 4 1 * (n:ℝ) ^ 2 * Real.log 3
          * max (Real.log ((2 * m + n : ℕ) : ℝ)) 1 + ((p:ℝ) + 1) * Real.log 2 :=
    le_trans hgap (by linarith [key])
  have hgap' : (M:ℝ) * Real.log 2 - ((a:ℝ) + 1) * Real.log 2
      ≤ 4 * BakerWustholz.C 4 1 * (n:ℝ) ^ 2 * Real.log 3
          * max (Real.log ((2 * m + n : ℕ) : ℝ)) 1 + ((p:ℝ) + 1) * Real.log 2 := by
    calc (M:ℝ) * Real.log 2 - ((a:ℝ) + 1) * Real.log 2
        = ((M:ℝ) - ((a + 1 : ℕ) : ℝ)) * Real.log 2 := by push_cast; ring
      _ ≤ _ := hstep
  nlinarith [hgap', hslack]

/-- **Theorem B3 — the Morse–Hedlund complexity floor for `3^m`** ([A4+] §3.3).
For every `n ≥ 1`, the binary digit string of `3^m` has at least `n + 1`
distinct length-`n` factors in its low `M := ⌊log₂ 3^m⌋` bits, for all
sufficiently large `m`.  The effective `m₀(n)` is where the linear growth of `M`
overtakes the Baker bound `≈ 4·C(4,1)·n²·(log3/log2)·log(2m+n)`. -/
@[category research solved, AMS 11, ref "Ste80", group "three_pow_digit_blocks"]
theorem three_pow_complexity_ge (n : ℕ) (hn : 1 ≤ n) :
    ∀ᶠ m : ℕ in atTop,
      n + 1 ≤ subwordComplexity (fun i => (3 ^ m).testBit i) (Nat.log 2 (3 ^ m)) n := by
  have hMm : ∀ m : ℕ, m ≤ Nat.log 2 (3 ^ m) := by
    intro m
    calc m = Nat.log 2 (2 ^ m) := (Nat.log_pow (by norm_num) m).symm
      _ ≤ Nat.log 2 (3 ^ m) := Nat.log_mono_right (Nat.pow_le_pow_left (by norm_num) m)
  have hDnn : (0:ℝ) ≤ 4 * BakerWustholz.C 4 1 * (n:ℝ) ^ 2 * Real.log 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (C_one_nonneg 4)) (by positivity))
      log_three_pos'.le
  have haux := linear_dominates_log n hDnn
  filter_upwards [haux, eventually_ge_atTop (4 * n + 1)] with m haux_m hge
  by_contra hcon
  rw [not_le] at hcon
  have hle : subwordComplexity (fun i => (3 ^ m).testBit i) (Nat.log 2 (3 ^ m)) n ≤ n := by omega
  have hMbig : 4 * n + 1 ≤ Nat.log 2 (3 ^ m) := le_trans hge (hMm m)
  have hcore := log_le_of_lowComplexity hn hMbig hle
  have hmM : (m : ℝ) ≤ (Nat.log 2 (3 ^ m) : ℝ) := by exact_mod_cast hMm m
  have hlog2 : (0:ℝ) < Real.log 2 := log_two_pos'
  -- hcore : (M - (3n+2))log2 ≤ D·max ;  haux_m : D·max + (3n+2)log2 < m·log2 ≤ M·log2
  nlinarith [hcore, haux_m, hmM, hlog2, mul_le_mul_of_nonneg_right hmM hlog2.le]

end TH
