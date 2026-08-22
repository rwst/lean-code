/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.ValuationArm
import Mathlib.RingTheory.Radical.NatInt

/-!
# The `abc`-quality ledger (strategy B6(i))

Tier (i) of strategy **B6** of `plans/report3-BB13.html` is a *conditional benchmark*: under a cap
`q ≤ q_max` on the `abc` quality of the triples the frame produces, the two arms of Problem 2 obey

`v₂(mₐ) + D(a) ≤ (log₂3/log₂2 − …)·a`,  concretely  `w + D ≤ 1.17a − 1.585a/q_max`,

which at the empirical record `q_max = 1.63` gives `min(v₂(mₐ), D(a)) ≤ 0.0988a` — three and a half
times better than the best known unconditional row (`0.371a`, [Zud07]).  This file supplies the
ledger as a theorem, in both directions, and prices the whole range of `q_max`.

## The triple

At index `a` the frame identity `mₐ2ᵃ + kₐ = 3ᵃ` *is* an `abc` triple.  It is not primitive: `3`
may divide `mₐ` (and then it divides `kₐ` too), so the content is

`gₐ = gcd(mₐ, 3ᵃ) = 3^{v₃(mₐ)}`  (`frameGcd`),

and the primitive triple is `A = mₐ2ᵃ/gₐ`, `B = kₐ/gₐ`, `C = 3ᵃ/gₐ` (`frameC`).  Dividing by `gₐ`
does not change the radical (the prime `3` survives in `C`), so `frameRad a = rad(A·B·C)`, and the
quality of the primitive triple is `log C/log rad`.  **This distinction is not cosmetic**: read on
the *raw* triple, `a = 3` has "quality" `log 27/log 6 = 1.8393 > 1.63` and would refute the
report's own hypothesis; the primitive triple there is `8 + 1 = 9`, of quality `1.2263`.

"Quality at most `N/M`" is the integer inequality `C^M ≤ rad^N`, which is how every hypothesis
below is stated — no logarithms, no real exponents.

## The core inequality (§3)

`frameRad_core`: for `a ≥ 1`, `2^w ∣ mₐ` and `2^D|kₐ|2ᵃ ≤ 3ᵃ`,

`rad · 2^{w+D+2a} · gₐ² ≤ 12 · 3^{2a}`.

Every factor is accounted for: `rad ≤ 6·(mₐ/2^wgₐ)·(|kₐ|/gₐ)` because `2` and `3` each contribute
once (`radical_rigid_le`), and the two size bounds `mₐ2ᵃ ≤ 2·3ᵃ`, `2^D|kₐ|2ᵃ ≤ 3ᵃ` supply the rest.
Read logarithmically it says `log₂rad ≤ 1.16993a + 3.585 − (w + D) − 2log₂gₐ`.  Note that the
`D`-hypothesis at `D = 0` *is* the exception condition `|kₐ| ≤ (3/2)ᵃ`, so everything below is a
statement about `𝓔` — which is the ledger's intended scope.  Measured (`BB13/b6_ledger.py`, [E]):
no violation for `a ≤ 140`, equality of the radical half in `115` of `140` cases.

## The two directions

*Unconditional* (`tower_quality`, `exception_quality`): a tower of depth `d` over `a ≥ 74` forces

`rad^{13}·gₐ^{10}·2^{26d} ≤ 3^{10a}`,

i.e. the primitive triple has quality `≥ 13/10`, growing with the depth.  The asymptotic constant
is `q* = log3/(2log(3/2)) = 1.35476…`; `13/10` is what survives the explicit `O(1)` at `a = 74`.

*Conditional* (`record_ledger_cap`, `record_fibre_cap`): a quality cap `163/100` for the triple at
`a` gives `10(w + D) ≤ 2a + 35`, hence `10d ≤ a + 17` for a tower of depth `d` — the report's
`0.0988a` row, confirmed with an explicit constant.

These two are contrapositives of each other, which is the honest verdict on B6(i): **the ledger is
a benchmark, not a mechanism.**  Its slope `1.16993 − 1.58496/q` vanishes exactly at `q = q*`,
the quality the frame's own triples attain — so no cap that could be true produces a *sublinear*
bound by this route, and any unconditional input must come from counting quality-`>1.3` triples of
the rigid shape (tier (iii) of B6), not from the ledger.

Section 8 adds the structural reason: `frameC` and `frameRad` are **line invariants**
(`quality_line_invariant`), because on a line all three terms scale by `3ᵈ` at once.  The quality
cap is therefore a hypothesis about a *line*, whose only free data are `w` and `D` — the ledger
cannot see anything else, by construction.

## How safe is the `1.63` hypothesis?

Less safe than "the empirical record of all known `abc` triples" suggests.  The family produces
`3¹⁰ + 7³ = 2¹¹·29` at `a = 10`, of quality **`1.5463`** (`BB13/b6_ledger.py`, [B]) — within
`0.084` of the global record `1.6299`, and the mean quality over `a ≤ 140` is `1.036`.  The
conditional row should be read with that margin in view.

## Where the price list is interesting

* `q_max < q* = 1.35476…` bounds `a` itself.  `exception_le_of_quality` : a cap of `4/3` forces
  every exception below `196`, and with the kernel census `E ∩ [1,256] = {1,2,3,4,7}` this
  *resolves* Problem 1 and Problem 2 outright (`failures_of_quality_cap`).  This is the explicit
  form of "`abc` with a constant kills the Waring exceptions".
* `q* < q_max < 3.6879…` beats [Zud07]'s `0.371a` row conditionally; `1.63` is deep inside.
* `q_max ≥ 3.6879…` buys nothing.

## Trust ledger

`std3` (`propext`, `Classical.choice`, `Quot.sound`) throughout: no cited axiom, no `sorry`, no
`native_decide`.  Only `Nat`/`Int` arithmetic, Mathlib's `radical`, and — in the last theorem —
the kernel census `BB13.failures_up_to_256`.  The rational bound `3^41 ≤ 2^65`
(`three_pow_le_two_pow`) is the only numerical input; it is why the constants below (`0.19811a`
rather than `0.19756a`) are a hair weaker than the report's real-arithmetic figures.

## Claim level

Formalization of a conditional benchmark and of its unconditional contrapositive.  **No quality
cap is proved here** — `hqual` is a hypothesis of every statement in §5–§6.

## References

* `plans/report3-BB13.html` §6 (B6), §1.4 (the ledger row), §5 (Q2.4 — the quantified
  circularity), §8; `plans/note-BB13-B6.html`.
* [Mas85] D. W. Masser, *Open problems*, in: Proc. Symp. Analytic Number Th. (1985); [Oes88]
  J. Oesterlé, *Nouvelles approches du "théorème" de Fermat*, Sém. Bourbaki 694 (1988) — the
  `abc` conjecture and the quality convention.
* [SY01] C. L. Stewart, K. Yu, *On the `abc` conjecture, II*, Duke Math. J. **108** (2001) — the
  effective radical bounds audited (and found vacuous here) in the report's §6.12.
* [Zud07] W. Zudilin, *A new lower bound for `‖(3/2)ᵏ‖`*, J. Théor. Nombres Bordeaux **19**
  (2007) — the `0.371a` row the conditional ledger is measured against.
* `BB13/b6_ledger.py` — the numerical ledger (the family's own record is `1.2263`).
-/

namespace BB13

open UniqueFactorizationMonoid

/-! ## 1. Radicals of the rigid shape

The only radical fact needed is that a product `M·2ᵉ·K·3ᶠ` has radical at most `6MK`: the two
fixed primes contribute `2` and `3`, and each of `M`, `K` contributes at most itself. -/

/-- **The radical of the rigid shape.**  `rad(M·2ᵉ·K·3ᶠ) ≤ 6·M·K` for `e, f ≥ 1`.  This is the
only place where a factorisation is used; everything downstream is size bookkeeping. -/
@[category API, AMS 11, ref "Mas85" "Oes88", group "bugeaud_10_13"]
theorem radical_rigid_le {M K e f : ℕ} (hM : M ≠ 0) (hK : K ≠ 0) (he : e ≠ 0) (hf : f ≠ 0) :
    radical (M * 2 ^ e * K * 3 ^ f) ≤ 6 * (M * K) := by
  have h2 : radical ((2 : ℕ) ^ e) = 2 := by
    rw [radical_pow_of_prime Nat.prime_two.prime he]; simp
  have h3 : radical ((3 : ℕ) ^ f) = 3 := by
    rw [radical_pow_of_prime Nat.prime_three.prime hf]; simp
  have hdvd : radical (M * 2 ^ e * K * 3 ^ f)
      ∣ radical M * radical (2 ^ e) * radical K * radical (3 ^ f) := by
    refine dvd_trans radical_mul_dvd (mul_dvd_mul ?_ dvd_rfl)
    exact dvd_trans radical_mul_dvd (mul_dvd_mul radical_mul_dvd dvd_rfl)
  rw [h2, h3] at hdvd
  have hle : radical (M * 2 ^ e * K * 3 ^ f) ≤ radical M * 2 * radical K * 3 := by
    refine Nat.le_of_dvd ?_ hdvd
    have := Nat.radical_pos M
    have := Nat.radical_pos K
    positivity
  calc radical (M * 2 ^ e * K * 3 ^ f) ≤ radical M * 2 * radical K * 3 := hle
    _ ≤ M * 2 * K * 3 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul
          (Nat.mul_le_mul_right _ (Nat.radical_le_self_iff.mpr hM))
          (Nat.radical_le_self_iff.mpr hK))
    _ = 6 * (M * K) := by ring

/-! ## 2. The exponent arithmetic

Every inequality below ends in a comparison of `2`-powers with `3`-powers.  The single numerical
input is `3⁴¹ ≤ 2⁶⁵` — the smallest convergent bound `log₂3 < 65/41 = 1.58537` that is sharp
enough for the `1.63` row (`8/5` is not).  Raising to the `41`-st power turns every statement of
the form `2^{NE} ≤ 12^N·3^F` into a linear inequality between exponents. -/

/-- `3^{41k} ≤ 2^{65k}` — the rational bound `log₂3 < 65/41`, in the form used throughout. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem three_pow_le_two_pow (k : ℕ) : (3 : ℕ) ^ (41 * k) ≤ 2 ^ (65 * k) := by
  rw [pow_mul, pow_mul]
  exact Nat.pow_le_pow_left (by norm_num) k

/-- `(12^N·3^F)^{41} = 2^{82N}·3^{41(N+F)}` — `12 = 2²·3`, expanded once and for all. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem twelve_pow_pow (N F : ℕ) :
    ((12 : ℕ) ^ N * 3 ^ F) ^ 41 = 2 ^ (82 * N) * 3 ^ (41 * (N + F)) := by
  have h12 : (12 : ℕ) ^ N = 2 ^ (2 * N) * 3 ^ N := by
    rw [show (12 : ℕ) = 2 ^ 2 * 3 from by norm_num, mul_pow, ← pow_mul]
  rw [h12, mul_assoc, ← pow_add, mul_pow, ← pow_mul, ← pow_mul,
    show 2 * N * 41 = 82 * N from by ring, show (N + F) * 41 = 41 * (N + F) from by ring]

/-- `(12^N·3^F)^{41} ≤ 2^{82N + 65(N+F)}`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem twelve_pow_pow_le (N F : ℕ) :
    ((12 : ℕ) ^ N * 3 ^ F) ^ 41 ≤ 2 ^ (82 * N + 65 * (N + F)) := by
  rw [twelve_pow_pow, pow_add]
  exact Nat.mul_le_mul_left _ (three_pow_le_two_pow _)

/-- **The exponent ledger.**  `2^{N·E} ≤ 12^N·3^F` forces the linear inequality
`41·N·E ≤ 82N + 65(N + F)` between the exponents — the engine of every cap below. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem exponent_bound {N E F : ℕ} (h : (2 : ℕ) ^ (N * E) ≤ 12 ^ N * 3 ^ F) :
    41 * (N * E) ≤ 82 * N + 65 * (N + F) := by
  have h41 : (2 : ℕ) ^ (41 * (N * E)) ≤ 2 ^ (82 * N + 65 * (N + F)) := by
    calc (2 : ℕ) ^ (41 * (N * E)) = ((2 : ℕ) ^ (N * E)) ^ 41 := by rw [← pow_mul, Nat.mul_comm]
      _ ≤ ((12 : ℕ) ^ N * 3 ^ F) ^ 41 := Nat.pow_le_pow_left h 41
      _ ≤ 2 ^ (82 * N + 65 * (N + F)) := twelve_pow_pow_le N F
  exact (Nat.pow_le_pow_iff_right (a := 2) (by norm_num)).mp h41

/-- The converse bookkeeping: `12^N·3^F ≤ 2^G` as soon as the exponents allow it. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem twelve_pow_le {N F G : ℕ} (h : 82 * N + 65 * (N + F) ≤ 41 * G) :
    (12 : ℕ) ^ N * 3 ^ F ≤ 2 ^ G := by
  rw [← Nat.pow_le_pow_iff_left (n := 41) (by norm_num)]
  calc ((12 : ℕ) ^ N * 3 ^ F) ^ 41 ≤ 2 ^ (82 * N + 65 * (N + F)) := twelve_pow_pow_le N F
    _ ≤ 2 ^ (41 * G) := Nat.pow_le_pow_right (by norm_num) h
    _ = ((2 : ℕ) ^ G) ^ 41 := by rw [← pow_mul, Nat.mul_comm]

/-! ## 3. The frame's `abc` triple

`mₐ2ᵃ + kₐ = 3ᵃ` with the content `gₐ = gcd(mₐ, 3ᵃ)` divided out. -/

/-- **The content of the frame triple**: `gₐ = gcd(mₐ, 3ᵃ) = 3^{v₃(mₐ)}`.  It divides all three
terms, so the primitive triple is `(mₐ2ᵃ/gₐ, kₐ/gₐ, 3ᵃ/gₐ)`. -/
def frameGcd (a : ℕ) : ℕ := Nat.gcd (mNat a) (3 ^ a)

/-- **The product `A·B·C` of the frame triple at `a`**, `A = mₐ2ᵃ`, `B = |kₐ|`, `C = 3ᵃ`.
Dividing out the content does not change its radical, since `3` survives in `C`. -/
noncomputable def frameProd (a : ℕ) : ℕ := mNat a * 2 ^ a * (resid 3 2 a).natAbs * 3 ^ a

/-- **The radical of the frame triple** — the `rad(abc)` of the `abc` conjecture. -/
noncomputable def frameRad (a : ℕ) : ℕ := radical (frameProd a)

/-- **The `C` of the primitive frame triple**, `C = 3ᵃ/gₐ = 3^{a − v₃(mₐ)}`.  "Quality at most
`N/M`" is `frameC a ^ M ≤ frameRad a ^ N`. -/
def frameC (a : ℕ) : ℕ := 3 ^ a / frameGcd a

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem frameGcd_pos (a : ℕ) : 0 < frameGcd a :=
  Nat.gcd_pos_of_pos_right _ (by positivity)

@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem frameGcd_dvd_three_pow (a : ℕ) : frameGcd a ∣ 3 ^ a := Nat.gcd_dvd_right _ _

/-- `C·gₐ = 3ᵃ`: the content splits off exactly. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem frameC_mul_frameGcd (a : ℕ) : frameC a * frameGcd a = 3 ^ a :=
  Nat.div_mul_cancel (frameGcd_dvd_three_pow a)

/-- `mₐ > 0` in the computable mirror. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem mNat_pos (a : ℕ) : 0 < mNat a := by
  have h := Mnum_pos a
  rw [Mnum_eq_mNat] at h
  exact_mod_cast h

/-- **The content divides the residue** too: `gₐ ∣ 3ᵃ` and `gₐ ∣ mₐ` give `gₐ ∣ kₐ`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem frameGcd_dvd_resid (a : ℕ) : frameGcd a ∣ (resid 3 2 a).natAbs := by
  have h1 : ((frameGcd a : ℕ) : ℤ) ∣ (3 : ℤ) ^ a := by
    have h := Int.natCast_dvd_natCast.mpr (frameGcd_dvd_three_pow a)
    simpa using h
  have h2 : ((frameGcd a : ℕ) : ℤ) ∣ Mnum 3 2 a * 2 ^ a := by
    rw [Mnum_eq_mNat]
    exact Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)) _
  have h3 : ((frameGcd a : ℕ) : ℤ) ∣ resid 3 2 a := by
    rw [resid]
    exact dvd_sub h1 h2
  simpa using Int.natAbs_dvd_natAbs.mpr h3

/-- **The archimedean size of the numerator**: `mₐ2ᵃ ≤ 2·3ᵃ`, from `mₐ = ⌊(2·3ᵃ + 2ᵃ)/2ᵃ⁺¹⌋`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem mNat_mul_two_pow_le (a : ℕ) : mNat a * 2 ^ a ≤ 2 * 3 ^ a := by
  have h : mNat a * 2 ^ (a + 1) ≤ 2 * 3 ^ a + 2 ^ a := by
    rw [mNat]; exact Nat.div_mul_le_self _ _
  have h2 : (2 : ℕ) ^ a ≤ 3 ^ a := Nat.pow_le_pow_left (by norm_num) a
  refine Nat.le_of_mul_le_mul_left ?_ (show 0 < 2 by norm_num)
  have hrw : 2 * (mNat a * 2 ^ a) = mNat a * 2 ^ (a + 1) := by rw [pow_succ]; ring
  rw [hrw]
  omega

/-! ## 4. The core inequality

`rad · 2^{w+D+2a} · gₐ² ≤ 12 · 3^{2a}`: the whole ledger, before any hypothesis about quality. -/

/-- **The core inequality of the ledger.**  For `a ≥ 1`, `2^w ∣ mₐ` and `2^D|kₐ|2ᵃ ≤ 3ᵃ`:

`rad(A·B·C) · 2^{w+D+2a} · gₐ² ≤ 12·3^{2a}`.

The `2`-adic depth `w` of the numerator and the dyadic quality surplus `D` of the residue both
enter the radical as savings, once each; the content `gₐ` enters squared (it is divided out of
`A` and of `B`, while `rad` keeps the prime `3` only once). -/
@[category research solved, AMS 11, ref "Mas85" "Bug12", group "bugeaud_10_13"]
theorem frameRad_core {a w D : ℕ} (ha : 1 ≤ a) (hw : 2 ^ w ∣ mNat a)
    (hD : 2 ^ D * (resid 3 2 a).natAbs * 2 ^ a ≤ 3 ^ a) :
    frameRad a * (2 ^ (w + D + 2 * a) * frameGcd a ^ 2) ≤ 12 * 3 ^ (2 * a) := by
  obtain ⟨v, -, hgv⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (frameGcd_dvd_three_pow a)
  have hcop : Nat.Coprime (2 ^ w) (frameGcd a) := by
    rw [hgv]; exact Nat.Coprime.pow _ _ (by norm_num)
  obtain ⟨μ, hμ⟩ : 2 ^ w * frameGcd a ∣ mNat a :=
    hcop.mul_dvd_of_dvd_of_dvd hw (Nat.gcd_dvd_left _ _)
  obtain ⟨κ, hκ⟩ : frameGcd a ∣ (resid 3 2 a).natAbs := frameGcd_dvd_resid a
  have hμ0 : μ ≠ 0 := by
    intro h
    rw [h, Nat.mul_zero] at hμ
    exact (mNat_pos a).ne' hμ
  have hκ0 : κ ≠ 0 := by
    intro h
    rw [h, Nat.mul_zero] at hκ
    exact (Int.natAbs_ne_zero.mpr (resid_ne_zero ha)) hκ
  -- the radical: `2` and `3` once each, `μ` and `κ` at most themselves
  have hfac : frameProd a = μ * 2 ^ (a + w) * κ * 3 ^ (a + (v + v)) := by
    rw [frameProd, hμ, hκ, hgv]; ring
  have hrad : frameRad a ≤ 6 * (μ * κ) := by
    rw [frameRad, hfac]
    exact radical_rigid_le hμ0 hκ0 (by omega) (by omega)
  -- the two size bounds, multiplied
  have hS1 : 2 ^ w * frameGcd a * μ * 2 ^ a ≤ 2 * 3 ^ a := by
    rw [show 2 ^ w * frameGcd a * μ = mNat a from hμ.symm]
    exact mNat_mul_two_pow_le a
  have hS2 : 2 ^ D * (frameGcd a * κ) * 2 ^ a ≤ 3 ^ a := by
    rw [show frameGcd a * κ = (resid 3 2 a).natAbs from hκ.symm]
    exact hD
  have hprod : μ * κ * (2 ^ (w + D + 2 * a) * frameGcd a ^ 2) ≤ 2 * 3 ^ (2 * a) := by
    calc μ * κ * (2 ^ (w + D + 2 * a) * frameGcd a ^ 2)
        = (2 ^ w * frameGcd a * μ * 2 ^ a) * (2 ^ D * (frameGcd a * κ) * 2 ^ a) := by ring
      _ ≤ (2 * 3 ^ a) * 3 ^ a := Nat.mul_le_mul hS1 hS2
      _ = 2 * 3 ^ (2 * a) := by ring
  calc frameRad a * (2 ^ (w + D + 2 * a) * frameGcd a ^ 2)
      ≤ 6 * (μ * κ) * (2 ^ (w + D + 2 * a) * frameGcd a ^ 2) := Nat.mul_le_mul hrad le_rfl
    _ = 6 * (μ * κ * (2 ^ (w + D + 2 * a) * frameGcd a ^ 2)) := by ring
    _ ≤ 6 * (2 * 3 ^ (2 * a)) := Nat.mul_le_mul le_rfl hprod
    _ = 12 * 3 ^ (2 * a) := by ring

/-! ### The two arms, in the integer form the core consumes -/

/-- The `D` arm as an integer inequality: `2ᵈ‖(3/2)ᵃ‖ < (3/4)ᵃ` reads `2ᵈ|kₐ|2ᵃ ≤ 3ᵃ`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem resid_natAbs_le_of_lt {a d : ℕ}
    (h : (2 : ℝ) ^ d * |((resid 3 2 a : ℤ) : ℝ)| < (3 / 2 : ℝ) ^ a) :
    2 ^ d * (resid 3 2 a).natAbs * 2 ^ a ≤ 3 ^ a := by
  have habs : |((resid 3 2 a : ℤ) : ℝ)| = (((resid 3 2 a).natAbs : ℕ) : ℝ) := by
    rw [← Int.cast_abs]
    exact (Nat.cast_natAbs _).symm
  have h2a : (0 : ℝ) < (2 : ℝ) ^ a := by positivity
  have hmul := mul_lt_mul_of_pos_right h h2a
  rw [habs] at hmul
  have hR : (3 / 2 : ℝ) ^ a * 2 ^ a = 3 ^ a := by
    rw [div_pow]; field_simp
  rw [hR] at hmul
  have hcast : ((2 ^ d * (resid 3 2 a).natAbs * 2 ^ a : ℕ) : ℝ) < ((3 ^ a : ℕ) : ℝ) := by
    push_cast
    linarith [hmul]
  exact le_of_lt (by exact_mod_cast hcast)

/-- **The two arms of a tower**, in integer form: a tower of depth `d` over `a` gives both
`2ᵈ ∣ mₐ` (the `v` arm) and `2ᵈ|kₐ|2ᵃ ≤ 3ᵃ` (the `D` arm). -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem tower_arms {a d : ℕ} (hfail : IsFailure 3 2 (3 / 4) (a + d))
    (hlink : (3 : ℤ) ^ d * Mnum 3 2 a = (2 : ℤ) ^ d * Mnum 3 2 (a + d)) :
    2 ^ d ∣ mNat a ∧ 2 ^ d * (resid 3 2 a).natAbs * 2 ^ a ≤ 3 ^ a := by
  refine ⟨(two_pow_dvd_Mnum_iff a d).mp (link_dvd 3 2 (by norm_num) hlink), ?_⟩
  have hq := link_quality 3 2 (3 / 4) hfail hlink
  have hD : (2 : ℝ) ^ d * |((resid 3 2 a : ℤ) : ℝ)| < (3 / 2 : ℝ) ^ a := by
    have hstep : (3 : ℝ) ^ d * |((resid 3 2 a : ℤ) : ℝ)| < (3 / 2 : ℝ) ^ a * (3 / 2 : ℝ) ^ d := by
      have hcast : ((3 : ℝ) / 4 * ((2 : ℕ) : ℝ)) ^ (a + d) = (3 / 2 : ℝ) ^ a * (3 / 2 : ℝ) ^ d := by
        rw [← pow_add]; norm_num
      have h3 : (((3 : ℕ) : ℝ)) ^ d = (3 : ℝ) ^ d := by norm_num
      rw [hcast, h3] at hq
      exact hq
    have hpos : (0 : ℝ) < (3 / 2 : ℝ) ^ d := by positivity
    have hkey : (2 : ℝ) ^ d * ((3 / 2 : ℝ) ^ d * |((resid 3 2 a : ℤ) : ℝ)|)
        = (3 : ℝ) ^ d * |((resid 3 2 a : ℤ) : ℝ)| := by
      rw [div_pow]; field_simp
    nlinarith [hstep, hkey, hpos, abs_nonneg ((resid 3 2 a : ℤ) : ℝ)]
  exact resid_natAbs_le_of_lt hD

/-- An exception is the depth-`0` case: `|kₐ|2ᵃ ≤ 3ᵃ`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem exception_arm {a : ℕ} (hf : IsFailure 3 2 (3 / 4) a) :
    2 ^ 0 * (resid 3 2 a).natAbs * 2 ^ a ≤ 3 ^ a := by
  refine resid_natAbs_le_of_lt (d := 0) ?_
  have hcast : ((3 : ℝ) / 4 * ((2 : ℕ) : ℝ)) ^ a = (3 / 2 : ℝ) ^ a := by norm_num
  rw [IsFailure, hcast] at hf
  simpa using hf

/-! ## 5. The unconditional direction: deep fibres are high-quality `abc` triples

The core inequality, read as a lower bound for the quality.  `13/10` is the explicit constant the
`O(1)` allows from `a = 74` on; the asymptotic value is `q* = log3/(2log(3/2)) = 1.35476…`, and
each unit of tower depth adds a full factor `2` to the left-hand side. -/

/-- **A tower of depth `d` over `a ≥ 74` is an `abc` triple of quality `≥ 13/10`**, improving by a
factor `2^{26d/13} = 2²ᵈ` per unit of depth:

`rad^{13} · gₐ^{10} · 2^{26d} ≤ 3^{10a}` — i.e. `rad^{13} ≤ (3ᵃ/gₐ)^{10}·2^{−26d}`.

This is the contrapositive of the conditional ledger of §6, and the reason that ledger can never
be sublinear: the frame's own triples realise the quality its slope vanishes at. -/
@[category research solved, AMS 11, ref "Mas85" "Oes88" "Bug12", group "bugeaud_10_13"]
theorem tower_quality {a d : ℕ} (ha : 74 ≤ a) (hfail : IsFailure 3 2 (3 / 4) (a + d))
    (hlink : (3 : ℤ) ^ d * Mnum 3 2 a = (2 : ℤ) ^ d * Mnum 3 2 (a + d)) :
    frameRad a ^ 13 * frameGcd a ^ 10 * 2 ^ (26 * d) ≤ 3 ^ (10 * a) := by
  obtain ⟨hw, hDa⟩ := tower_arms hfail hlink
  have hcore := frameRad_core (by omega) hw hDa
  have h13 := Nat.pow_le_pow_left hcore 13
  have hL : (frameRad a * (2 ^ (d + d + 2 * a) * frameGcd a ^ 2)) ^ 13
      = frameRad a ^ 13 * (2 ^ (26 * d + 26 * a) * frameGcd a ^ 26) := by
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
    congr 2
    · congr 1; ring
  have hR : ((12 : ℕ) * 3 ^ (2 * a)) ^ 13 = 12 ^ 13 * 3 ^ (26 * a) := by
    rw [mul_pow, ← pow_mul]
    congr 2
    ring
  rw [hL, hR] at h13
  -- `12¹³·3^{26a} ≤ 2^{26a}·3^{10a}` for `a ≥ 74`
  have hnum : (12 : ℕ) ^ 13 * 3 ^ (16 * a) ≤ 2 ^ (26 * a) := twelve_pow_le (by omega)
  have hnum' : (12 : ℕ) ^ 13 * 3 ^ (26 * a) ≤ 2 ^ (26 * a) * 3 ^ (10 * a) := by
    calc (12 : ℕ) ^ 13 * 3 ^ (26 * a) = 12 ^ 13 * 3 ^ (16 * a) * 3 ^ (10 * a) := by
          rw [mul_assoc, ← pow_add]; congr 2; ring
      _ ≤ 2 ^ (26 * a) * 3 ^ (10 * a) := Nat.mul_le_mul hnum le_rfl
  -- move `g^{10} ≤ g^{26}` and cancel `2^{26a}`
  have hg : frameGcd a ^ 10 ≤ frameGcd a ^ 26 :=
    Nat.pow_le_pow_right (frameGcd_pos a) (by norm_num)
  have hmain : frameRad a ^ 13 * frameGcd a ^ 10 * 2 ^ (26 * d) * 2 ^ (26 * a)
      ≤ 3 ^ (10 * a) * 2 ^ (26 * a) := by
    calc frameRad a ^ 13 * frameGcd a ^ 10 * 2 ^ (26 * d) * 2 ^ (26 * a)
        ≤ frameRad a ^ 13 * frameGcd a ^ 26 * 2 ^ (26 * d) * 2 ^ (26 * a) := by
          exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul le_rfl hg) le_rfl) le_rfl
      _ = frameRad a ^ 13 * (2 ^ (26 * d + 26 * a) * frameGcd a ^ 26) := by rw [pow_add]; ring
      _ ≤ 12 ^ 13 * 3 ^ (26 * a) := h13
      _ ≤ 2 ^ (26 * a) * 3 ^ (10 * a) := hnum'
      _ = 3 ^ (10 * a) * 2 ^ (26 * a) := by ring
  exact Nat.le_of_mul_le_mul_right hmain (by positivity)

/-- **Every exception `a ≥ 74` is an `abc` triple of quality `≥ 13/10`** — the `d = 0` case.  The
five known exceptions are far below `74`, where the explicit `O(1)` still dominates; their
measured qualities are `0.61, 1.23, 1.23, 1.29, 1.10` (`BB13/b6_ledger.py`). -/
@[category research solved, AMS 11, ref "Mas85" "Oes88" "Bug12", group "bugeaud_10_13"]
theorem exception_quality {a : ℕ} (ha : 74 ≤ a) (hf : IsFailure 3 2 (3 / 4) a) :
    frameRad a ^ 13 * frameGcd a ^ 10 ≤ 3 ^ (10 * a) := by
  have h := tower_quality (d := 0) ha (by simpa using hf) (by simp)
  simpa using h

/-! ## 6. The conditional direction: the ledger

`hqual : frameC a ^ M ≤ frameRad a ^ N` is "the primitive triple at `a` has `abc` quality at most
`N/M`".  Nothing below proves such a bound; the point is the exchange rate. -/

/-- **The quality ledger.**  A quality cap `N/M` (with `M ≤ 2N`) at the index `a` converts the two
arms into the exponent inequality

`2^{N(w+D+2a)}·3^{Ma} ≤ 12^N·3^{2Na}`.

Logarithmically: `w + D ≤ log₂12 + (2log₂3 − 2)a − (M/N)·log₂3·a`, the report's
`w + D ≤ 1.17a − 1.585a/q_max + O(1)`. -/
@[category research solved, AMS 11, ref "Mas85" "Oes88" "Bug12", group "bugeaud_10_13"]
theorem quality_ledger {a w D M N : ℕ} (ha : 1 ≤ a) (hMN : M ≤ 2 * N)
    (hqual : frameC a ^ M ≤ frameRad a ^ N)
    (hw : 2 ^ w ∣ mNat a)
    (hD : 2 ^ D * (resid 3 2 a).natAbs * 2 ^ a ≤ 3 ^ a) :
    2 ^ (N * (w + D + 2 * a)) * 3 ^ (M * a) ≤ 12 ^ N * 3 ^ (2 * N * a) := by
  have hcore := frameRad_core ha hw hD
  have hcoreN := Nat.pow_le_pow_left hcore N
  have hL : (frameRad a * (2 ^ (w + D + 2 * a) * frameGcd a ^ 2)) ^ N
      = frameRad a ^ N * (2 ^ (N * (w + D + 2 * a)) * frameGcd a ^ (2 * N)) := by
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm (w + D + 2 * a) N]
  have hR : ((12 : ℕ) * 3 ^ (2 * a)) ^ N = 12 ^ N * 3 ^ (2 * N * a) := by
    rw [mul_pow, ← pow_mul]
    congr 2
    ring
  rw [hL, hR] at hcoreN
  have h3 : (3 : ℕ) ^ (M * a) = frameC a ^ M * frameGcd a ^ M := by
    rw [← mul_pow, frameC_mul_frameGcd, ← pow_mul, Nat.mul_comm]
  have hstep : (3 : ℕ) ^ (M * a) ≤ frameRad a ^ N * frameGcd a ^ (2 * N) := by
    rw [h3]
    exact Nat.mul_le_mul hqual (Nat.pow_le_pow_right (frameGcd_pos a) hMN)
  calc (2 : ℕ) ^ (N * (w + D + 2 * a)) * 3 ^ (M * a)
      ≤ 2 ^ (N * (w + D + 2 * a)) * (frameRad a ^ N * frameGcd a ^ (2 * N)) :=
        Nat.mul_le_mul le_rfl hstep
    _ = frameRad a ^ N * (2 ^ (N * (w + D + 2 * a)) * frameGcd a ^ (2 * N)) := by ring
    _ ≤ 12 ^ N * 3 ^ (2 * N * a) := hcoreN

/-- **The record row of the report's §1.4.**  Under the empirical `abc` record `q_max = 1.63` as a
cap for the frame triple at `a`:

`10·(v₂(mₐ) + D(a)) ≤ 2a + 35`,  i.e.  `w + D ≤ 0.2a + 3.5`.

Real arithmetic gives the slope `1.16993 − 1.58496/1.63 = 0.19756`; `1/5` is what the rational
bound `log₂3 < 65/41` of `three_pow_le_two_pow` leaves. -/
@[category research solved, AMS 11, ref "Mas85" "Oes88" "Zud07" "Bug12", group "bugeaud_10_13"]
theorem record_ledger_cap {a w D : ℕ} (ha : 1 ≤ a)
    (hqual : frameC a ^ 100 ≤ frameRad a ^ 163)
    (hw : 2 ^ w ∣ mNat a)
    (hD : 2 ^ D * (resid 3 2 a).natAbs * 2 ^ a ≤ 3 ^ a) :
    10 * (w + D) ≤ 2 * a + 35 := by
  have h := quality_ledger (M := 100) (N := 163) ha (by norm_num) hqual hw hD
  have hsplit : (3 : ℕ) ^ (2 * 163 * a) = 3 ^ (226 * a) * 3 ^ (100 * a) := by
    rw [← pow_add]; congr 1; ring
  rw [hsplit, ← mul_assoc] at h
  have h' : (2 : ℕ) ^ (163 * (w + D + 2 * a)) ≤ 12 ^ 163 * 3 ^ (226 * a) :=
    Nat.le_of_mul_le_mul_right h (by positivity)
  have := exponent_bound h'
  omega

/-- **The fibre form** — the report's `min(v₂(mₐ), D(a)) ≤ 0.0988a` row, with an explicit
constant: under the `1.63` cap, a tower of depth `d` over `a` obeys `10d ≤ a + 17`.  Against the
unconditional `d ≤ 0.371a` of [Zud07] this is a factor `3.7`. -/
@[category research solved, AMS 11, ref "Mas85" "Oes88" "Zud07" "Bug12", group "bugeaud_10_13"]
theorem record_fibre_cap {a d : ℕ} (ha : 1 ≤ a)
    (hqual : frameC a ^ 100 ≤ frameRad a ^ 163)
    (hfail : IsFailure 3 2 (3 / 4) (a + d))
    (hlink : (3 : ℤ) ^ d * Mnum 3 2 a = (2 : ℤ) ^ d * Mnum 3 2 (a + d)) :
    10 * d ≤ a + 17 := by
  obtain ⟨hw, hDa⟩ := tower_arms hfail hlink
  have h := record_ledger_cap ha hqual hw hDa
  omega

/-! ## 7. Below the threshold: a `4/3` cap resolves Problem 1

The slope `1.16993 − 1.58496/q` of the ledger is *negative* for `q < q* = 1.35476…`; there the
inequality bounds `a` itself rather than the fibre.  `4/3 = 1.333… < q*`, and the resulting
threshold `196` is inside the kernel-certified census range. -/

/-- **A quality cap of `4/3` bounds the exceptions.**  If the primitive frame triple at an
exception `a` has `abc` quality at most `4/3`, then `a ≤ 196`.

Real arithmetic gives `190`; `196` is the rational bound's version.  Note how little is being
assumed: the `abc` conjecture asserts quality `→ 1`, and even the *empirical* record for all known
triples is `1.6299`. -/
@[category research solved, AMS 11, ref "Mas85" "Oes88" "Mah57" "Bug12", group "bugeaud_10_13"]
theorem exception_le_of_quality {a : ℕ} (ha : 1 ≤ a)
    (hqual : frameC a ^ 3 ≤ frameRad a ^ 4) (hf : IsFailure 3 2 (3 / 4) a) : a ≤ 196 := by
  have h := quality_ledger (M := 3) (N := 4) (w := 0) (D := 0) ha (by norm_num) hqual
    (by simp) (exception_arm hf)
  have hsplit : (3 : ℕ) ^ (2 * 4 * a) = 3 ^ (5 * a) * 3 ^ (3 * a) := by
    rw [← pow_add]; congr 1; ring
  rw [hsplit, ← mul_assoc] at h
  have h' : (2 : ℕ) ^ (4 * (0 + 0 + 2 * a)) ≤ 12 ^ 4 * 3 ^ (5 * a) :=
    Nat.le_of_mul_le_mul_right h (by positivity)
  have := exponent_bound h'
  omega

/-- **The conditional resolution of Problem 1 (and hence of Problem 2).**  If every frame triple
has `abc` quality at most `4/3`, then the exceptions are exactly the five certified ones:

`‖(3/2)ⁿ‖ < (3/4)ⁿ ⟺ n ∈ {1, 2, 3, 4, 7}`.

The cap forces `a ≤ 196`, and `BB13.failures_up_to_256` decides the range in the kernel.  This is
the explicit shape of "`abc` with a constant settles the ideal Waring formula". -/
@[category research solved, AMS 11, ref "Mas85" "Oes88" "Mah57" "Bug12", group "bugeaud_10_13"]
theorem failures_of_quality_cap (hqual : ∀ b : ℕ, 1 ≤ b → frameC b ^ 3 ≤ frameRad b ^ 4)
    {a : ℕ} (ha : 1 ≤ a) :
    IsFailure 3 2 (3 / 4) a ↔ (a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 7) := by
  constructor
  · intro hf
    have hle := exception_le_of_quality ha (hqual a ha) hf
    exact (failures_up_to_256 a ha (by omega)).mp hf
  · intro h
    have h256 : a ≤ 256 := by rcases h with rfl | rfl | rfl | rfl | rfl <;> norm_num
    exact (failures_up_to_256 a ha h256).mpr h

/-! ## 8. The triple is a line invariant

On a line the frame points are exact `3ᵈ`-scalings of the least one (`mₐ = 2ᵈμ`,
`m_{a+d} = 3ᵈμ`, `k_{a+d} = 3ᵈkₐ`), so `A`, `B` and `C` all scale by `3ᵈ` — and the prime `3` is
already in `C`.  Hence the *primitive* triple, its radical and its quality are constant along a
line: measured, `a = 14, 15, 16` all give quality `1.170735` with radical `507642`
(`BB13/b6_ledger.py`, block [B]).

This is the report's scale-invariance wall (§6.12) seen from the `abc` side.  It says exactly what
the ledger is: a hypothesis about the *line*, whose only free data are `w` and `D`. -/

/-- The line data in `ℕ`: `mₐ = 2ᵈν`, `m_{a+d} = 3ᵈν`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem mNat_line {a d : ℕ} (hlink : (3 : ℤ) ^ d * Mnum 3 2 a = (2 : ℤ) ^ d * Mnum 3 2 (a + d)) :
    ∃ ν : ℕ, mNat a = 2 ^ d * ν ∧ mNat (a + d) = 3 ^ d * ν := by
  obtain ⟨ν, hν⟩ := (two_pow_dvd_Mnum_iff a d).mp (link_dvd 3 2 (by norm_num) hlink)
  refine ⟨ν, hν, ?_⟩
  have hN : (3 : ℕ) ^ d * mNat a = 2 ^ d * mNat (a + d) := by
    have h := hlink
    rw [Mnum_eq_mNat, Mnum_eq_mNat] at h
    exact_mod_cast h
  rw [hν] at hN
  have hcancel : 2 ^ d * (3 ^ d * ν) = 2 ^ d * mNat (a + d) := by rw [← hN]; ring
  exact (Nat.eq_of_mul_eq_mul_left (by positivity) hcancel).symm

/-- `rad(3ʲ·X) = rad(X)` whenever `3 ∣ X`: the scaling adds no new prime. -/
@[category API, AMS 11, ref "Mas85", group "bugeaud_10_13"]
theorem radical_three_pow_mul {j X : ℕ} (hX : X ≠ 0) (h3 : 3 ∣ X) :
    radical (3 ^ j * X) = radical X := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  have hmem : 3 ∈ X.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3, hX⟩
  have hpf : (3 ^ j * X).primeFactors = X.primeFactors := by
    rw [Nat.primeFactors_mul (by positivity) hX,
      Nat.primeFactors_prime_pow (by omega) Nat.prime_three]
    exact Finset.union_eq_right.mpr (Finset.singleton_subset_iff.mpr hmem)
  rw [Nat.radical_eq_prod_primeFactors, Nat.radical_eq_prod_primeFactors, hpf]

/-- **The product scales by `3^{3d}` along a line.** -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem frameProd_line {a d : ℕ}
    (hlink : (3 : ℤ) ^ d * Mnum 3 2 a = (2 : ℤ) ^ d * Mnum 3 2 (a + d)) :
    frameProd (a + d) = 3 ^ (3 * d) * frameProd a := by
  obtain ⟨ν, hνa, hνb⟩ := mNat_line hlink
  have hk : (resid 3 2 (a + d)).natAbs = 3 ^ d * (resid 3 2 a).natAbs := by
    rw [link_resid 3 2 hlink, Int.natAbs_mul, Int.natAbs_pow]
    norm_num
  rw [frameProd, frameProd, hνa, hνb, hk]
  rw [show 3 * d = d + (d + d) from by ring]
  rw [pow_add, pow_add, pow_add, pow_add]
  ring

/-- **The radical is a line invariant.** -/
@[category research solved, AMS 11, ref "Mas85" "Bug12", group "bugeaud_10_13"]
theorem frameRad_line {a d : ℕ} (ha : 1 ≤ a)
    (hlink : (3 : ℤ) ^ d * Mnum 3 2 a = (2 : ℤ) ^ d * Mnum 3 2 (a + d)) :
    frameRad (a + d) = frameRad a := by
  have hne : frameProd a ≠ 0 := by
    rw [frameProd]
    have h1 : mNat a ≠ 0 := (mNat_pos a).ne'
    have h2 : (resid 3 2 a).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (resid_ne_zero ha)
    positivity
  have h3 : 3 ∣ frameProd a := by
    rw [frameProd]
    exact Dvd.dvd.mul_left (dvd_pow_self 3 (by omega : a ≠ 0)) _
  rw [frameRad, frameRad, frameProd_line hlink, radical_three_pow_mul hne h3]

/-- **The content scales by `3ᵈ`, so `C` is a line invariant.** -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem frameGcd_line {a d : ℕ}
    (hlink : (3 : ℤ) ^ d * Mnum 3 2 a = (2 : ℤ) ^ d * Mnum 3 2 (a + d)) :
    frameGcd (a + d) = 3 ^ d * frameGcd a := by
  obtain ⟨ν, hνa, hνb⟩ := mNat_line hlink
  have hcop : Nat.Coprime (2 ^ d) (3 ^ a) := Nat.Coprime.pow _ _ (by norm_num)
  rw [frameGcd, frameGcd, hνa, hνb, pow_add, Nat.mul_comm (3 ^ a) (3 ^ d), Nat.gcd_mul_left,
    hcop.gcd_mul_left_cancel ν]

/-- **The quality cap is a hypothesis about the line, not about the index.** -/
@[category research solved, AMS 11, ref "Mas85" "Oes88" "Bug12", group "bugeaud_10_13"]
theorem quality_line_invariant {a d M N : ℕ} (ha : 1 ≤ a)
    (hlink : (3 : ℤ) ^ d * Mnum 3 2 a = (2 : ℤ) ^ d * Mnum 3 2 (a + d)) :
    (frameC (a + d) ^ M ≤ frameRad (a + d) ^ N) ↔ (frameC a ^ M ≤ frameRad a ^ N) := by
  have hC : frameC (a + d) = frameC a := by
    rw [frameC, frameC, frameGcd_line hlink, pow_add, Nat.mul_comm (3 ^ a) (3 ^ d),
      Nat.mul_div_mul_left _ _ (by positivity)]
  rw [hC, frameRad_line ha hlink]

end BB13
