/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CC.SRSBridge
import SRS.CollatzSRS
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# The parity vector is the trace of 𝒯's dynamic-rule firings (Report B3 item 6, step 3) (Ter76; YAH)

**Report B3, item 6, concrete step 3:** *connect to existing code — show that the parity-vector
infrastructure of `Terras.lean` is exactly the syntactic trace of `𝒯`'s dynamic-rule firings.*

The mixed-base SRS `𝒯` (`SRS.CollatzSRS`) has exactly **two dynamic rules** `𝒟_T`
(`CollatzSRS.dynRules`):

* `f▷ → ▷`  — the **even** rule: a trailing binary `0`, value `2x`, is halved to `x`;
* `t▷ → 2▷` — the **odd** rule: a trailing binary `1`, value `2x+1`, becomes the accelerated odd
  step `3x+2`.

On a string of value `m` the *even* rule is the one that fires iff `m` is even (`dynFire_eq_firedT`);
either rule advances the value by one step of the accelerated Terras map `T` (`dynRules_applyT`,
re-packaged here as `dynFireR_eval`). Crucially `CollatzSRS.T` is the **same function** as
`CC.T` (`T_agree`), so the orbit driven by the dynamic firings is the Terras orbit
`T_iter · n` of `Terras.lean`.

Therefore the sequence of dynamic firings over the orbit — recorded as the bit `firedT` ("did the odd
`t`-rule fire?") at each step — is **exactly the parity vector** `V k n` of `Parity.lean`:

> **Step-3 theorem** (`dynTrace_eq_V`): `dynTrace k n = V k n`.

and, counting odd firings, the number of `t`-rule (tripling) firings equals the Terras odd-step count
(`q_dynTrace : q (dynTrace k n) = num_odd_steps k n`). This is the syntactic-trace ↔ density-datum
identification the two-semiring bridge ([[cc-srsbridge-item6]]) rests on.

*Scope.* This connects the dynamic firings **at the value level** (the `compFun`/`Γ` evaluation): each
firing is a genuine `dynRules` rewrite computing one `T`-step, and the firing bit is the parity bit.
The full *derivation-level* simulation — that the auxiliary rules `𝒳` normalise the representation so
the dynamic rules fire in this exact order along a `RewriteStep`-derivation to normal form — is
`CollatzSRS.theorem_3_17` territory (Report B3 item 8) and is not re-proved here.

## Contents
* `T_agree` — `CC.T = CollatzSRS.T` (the two `T`'s coincide).
* `dynFireL`, `dynFireR` — the left/right sides of the dynamic rule selected by a value's parity;
  `dynFiring_mem` (it is a genuine `dynRules` rule), `dynFireL_eval` / `dynFireR_eval` (it evaluates
  the value `m` and outputs `T m`), `dynFiring_advances` (it advances the Terras orbit).
* `firedT`, `dynFire_eq_firedT` — the trace bit, and that it genuinely selects the rule.
* `dynTrace`, **`dynTrace_eq_V`** — the dynamic-firing trace **is** the parity vector.
* `q_dynTrace` — odd (`t`-rule) firings `=` `num_odd_steps`.

## References
* [Ter76] Terras. *A stopping time problem on the positive integers.* Acta Arith. 30 (1976), 241–252.
* [YAH] Yolcu, Aaronson, Heule. *An Automated Approach to the Collatz Conjecture.* arXiv:2105.14697.
-/

namespace CC.SRSTrace

open CC CC.SRSBridge StringRewriting
open StringRewriting.CollatzSRS.TSym

/-! ### The two `T`'s coincide -/

/-- The accelerated Terras map of `Terras.lean` (`CC.T`) and the one the SRS `𝒯`
iterates (`CollatzSRS.T`) are the **same function**. -/
@[category research solved, AMS 11 68, ref "Ter76" "YAH", group "two_semiring_bridge"]
theorem T_agree (n : ℕ) : CC.T n = CollatzSRS.T n := by
  unfold CollatzSRS.T
  split
  · next h => exact CC.T_even h
  · next h => exact CC.T_odd (by omega)

/-! ### The dynamic rule selected by a value's parity -/

/-- The **left side** of the dynamic rule that fires on a value-`m` string: `f▷` (even) or `t▷`
(odd). -/
@[category API, AMS 68, ref "YAH", group "two_semiring_bridge"]
def dynFireL (m : ℕ) : List CollatzSRS.TSym := if m % 2 = 0 then [f, rhd] else [t, rhd]

/-- The **right side** of the dynamic rule that fires on a value-`m` string: `▷` (even) or `2▷`
(odd). -/
@[category API, AMS 68, ref "YAH", group "two_semiring_bridge"]
def dynFireR (m : ℕ) : List CollatzSRS.TSym := if m % 2 = 0 then [rhd] else [d2, rhd]

/-- The selected `dynFireL m → dynFireR m` is a genuine **dynamic rule** of `𝒯`. -/
@[category research solved, AMS 68, ref "YAH", group "two_semiring_bridge"]
theorem dynFiring_mem (m : ℕ) : CollatzSRS.dynRules (dynFireL m) (dynFireR m) := by
  unfold dynFireL dynFireR CollatzSRS.dynRules
  by_cases h : m % 2 = 0 <;> simp [h]

/-- The left side evaluates (at `x = m / 2`) to the value `m` itself: `f▷` reads an even `m = 2·(m/2)`,
`t▷` an odd `m = 2·(m/2)+1`. -/
@[category research solved, AMS 11 68, ref "YAH", group "two_semiring_bridge"]
theorem dynFireL_eval (m : ℕ) : CollatzSRS.compFun (dynFireL m) (m / 2) = m := by
  unfold dynFireL
  split <;>
    simp only [CollatzSRS.compFun, CollatzSRS.symFun, MixedBase.beta, List.foldl_cons,
      List.foldl_nil] <;>
    omega

/-- The right side outputs `T m`: the firing computes one Terras step. (This is `dynRules_applyT`
specialised to the parity-selected rule.) -/
@[category research solved, AMS 11 68, ref "YAH", group "two_semiring_bridge",
  formal_uses CollatzSRS.dynRules_applyT dynFiring_mem dynFireL_eval]
theorem dynFireR_eval (m : ℕ) : CollatzSRS.compFun (dynFireR m) (m / 2) = CollatzSRS.T m := by
  have h := CollatzSRS.dynRules_applyT (dynFireL m) (dynFireR m) (dynFiring_mem m) (m / 2)
  rw [dynFireL_eval m] at h
  exact h.symm

/-- The `i`-th dynamic firing advances the **Terras orbit**: from value `T_iter i n` it outputs
`T_iter (i+1) n`. -/
@[category research solved, AMS 11 68, ref "Ter76" "YAH", group "two_semiring_bridge",
  formal_uses dynFireR_eval T_agree]
theorem dynFiring_advances (n i : ℕ) :
    CollatzSRS.compFun (dynFireR (T_iter i n)) (T_iter i n / 2) = T_iter (i + 1) n := by
  have hstep : T_iter (i + 1) n = CollatzSRS.T (T_iter i n) := by
    show CC.T (T_iter i n) = CollatzSRS.T (T_iter i n)
    exact T_agree _
  rw [hstep]; exact dynFireR_eval _

/-! ### The firing trace is the parity vector -/

/-- The trace bit at value `m`: `true` iff the **odd** rule `t▷ → 2▷` fires (i.e. `m` is odd). -/
@[category API, AMS 11 68, ref "YAH", group "two_semiring_bridge"]
def firedT (m : ℕ) : Bool := decide (m % 2 = 1)

/-- The trace bit genuinely **selects the rule**: `firedT m` chooses the odd rule `t▷ → 2▷`, `¬ firedT m`
the even rule `f▷ → ▷`. -/
@[category research solved, AMS 11 68, ref "YAH", group "two_semiring_bridge"]
theorem dynFire_eq_firedT (m : ℕ) :
    (dynFireL m, dynFireR m)
      = (if firedT m then ([t, rhd], [d2, rhd]) else ([f, rhd], [rhd])) := by
  unfold dynFireL dynFireR firedT
  rcases Nat.mod_two_eq_zero_or_one m with h | h <;> simp [h]

/-- The **dynamic-firing trace** of the length-`k` orbit of `n`: the bit at step `i` records whether
the odd `t`-rule fired on the orbit value `T_iter i n`. -/
@[category API, AMS 11 68, ref "Ter76" "YAH", group "two_semiring_bridge"]
def dynTrace (k n : ℕ) : ParityVector := (List.range k).map (fun i => firedT (T_iter i n))

/-- **Step-3 theorem.** The dynamic-firing trace of the orbit **is** the parity vector `V k n` of
`Parity.lean`: the syntactic record of which dynamic rule of `𝒯` fires at each step coincides,
position by position, with Terras's parity vector. -/
@[category research solved, AMS 11 68, ref "Ter76" "YAH", group "two_semiring_bridge",
  formal_uses V_eq_range_map firedT]
theorem dynTrace_eq_V (k n : ℕ) : dynTrace k n = V k n := by
  rw [dynTrace, V_eq_range_map]
  refine List.map_congr_left ?_
  intro i _
  simp only [firedT, X_eq_mod]

/-- The number of **odd** (`t`-rule, tripling) firings in the trace equals the Terras odd-step count
`num_odd_steps k n`. -/
@[category research solved, AMS 11 68, ref "Ter76" "YAH", group "two_semiring_bridge",
  formal_uses dynTrace_eq_V q_V]
theorem q_dynTrace (k n : ℕ) : q (dynTrace k n) = num_odd_steps k n := by
  rw [dynTrace_eq_V, q_V]

end CC.SRSTrace
