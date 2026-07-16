/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Mathlib.Data.Nat.Basic
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Dimitrov–Howe: the powers of `3` with exactly three nonzero binary digits

Vassil S. Dimitrov and Everett W. Howe, *Powers of 3 with few nonzero bits and a
conjecture of Erdős* (arXiv:2105.06440, 2023).  The `n = 3` case of their
equation (1) — the worked example of their §1 — determines every power of `3`
that is a sum of three distinct powers of `2`:

  the only solution of `3^x = 2^{a₁} + 2^{a₂} + 2^{a₃}`
  (`0 ≤ a₁ < a₂ < a₃`) is `3^4 = 2^0 + 2^4 + 2^6`, i.e. `81 = 1 + 16 + 64`.

Since `3^x` is odd we always have `a₁ = 0` (an elementary reduction), so the
content is: `3^m = 1 + 2^b + 2^a` with `1 ≤ b < a` forces `(m, b, a) = (4, 4, 6)`.

## Method (not reproduced here)

DH23's proof is **completely elementary but computational**: reduce the equation
modulo a carefully chosen sequence of moduli, each dividing the next, so that
every solution modulo `M` lifts to at most one solution over `ℤ`.  For the
`n = 3` slice they use `M₁ = 5440 = 2^6·5·17` and
`M₂ = 2^7·5·17·257`, exploiting a *determinacy* property of the "tail" powers of
`2` in the multiplicative structure modulo these moduli, together with a
computer enumeration (Magma) of the finitely many residue patterns.  The
argument uses **no linear forms in logarithms** — the authors present it as a
reminder that elementary congruence methods can settle exponential Diophantine
problems out of reach of Baker's method for `n = 3` (though the perfect-power
form `2^a + 2^b + 1 = y^q` was also settled analytically by
Bennett–Bugeaud–Mignotte).

Recorded here as a **cited `axiom`** — the finite modular computation is not
re-executed inside Lean.  Status: `cited` (see the layered-QA policy for corpus
roots).  It supplies the Diophantine core of Theorem **B5a′/B5b** of the
digit-block program ([A4+] §3.4): `s₂(3^m) = 3 ⟺ m = 4`, formalized in
`TH/DigitBlocks/SparseSide.lean`.

## Contents

* `DH.three_pow_three_binary_digits` — **[DH23], `n = 3` case**: the equation
  `3^m = 2^a + 2^b + 1`, `1 ≤ b < a`, has the unique solution
  `(m, b, a) = (4, 4, 6)`.

## References

* [DH23] V. S. Dimitrov, E. W. Howe, *Powers of 3 with few nonzero bits and a
  conjecture of Erdős*, arXiv:2105.06440v4 (2023).  (Theorem 1.1 and the §1
  worked `n = 3` example; the general theorem covers `s₂(3^x) ≤ 22`,
  computationally.)
* [BBM] M. Bennett, Y. Bugeaud, M. Mignotte, *Perfect powers with few binary
  digits and related Diophantine problems, II*, Math. Proc. Cambridge Philos.
  Soc. **153** (2012), 525–540.  (Settles `2^a + 2^b + 1 = y^q`; the analytic
  two-log route to the same `y = 3` slice.)
* [A4+] `plan-A4+.html` (this repository, 2026-07): §3.4 (B5b), §4 gate G2.
-/

namespace DH

/-- **Dimitrov–Howe 2023, the `n = 3` case** ([DH23], §1): the only power of `3`
that is a sum of three distinct powers of `2` is `3^4 = 2^0 + 2^4 + 2^6 = 81`.
Equivalently (using `a₁ = 0` by oddness), the equation `3^m = 2^a + 2^b + 1`
with `1 ≤ b < a` has the unique solution `(m, b, a) = (4, 4, 6)`.

Recorded as a cited `axiom`: DH23 prove it by an elementary but *computational*
congruence argument (moduli `5440` and `2^7·5·17·257`, Magma enumeration), which
we do not re-execute.  Footprint: cited [DH23]. -/
@[category research solved, AMS 11, ref "DH23", group "three_pow_digit_blocks"]
axiom three_pow_three_binary_digits {m a b : ℕ}
    (h : 3 ^ m = 2 ^ a + 2 ^ b + 1) (hb : 1 ≤ b) (hab : b < a) :
    m = 4 ∧ b = 4 ∧ a = 6

end DH
