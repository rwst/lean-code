/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CC.Terras
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Lagarias — Rational 3x+1 cycles and the explicit periodic point (Lag90, §2)

Jeffrey C. Lagarias, *The set of rational cycles for the 3x+1 problem*, Acta Arithmetica **56**
(1990), 33–53, **Section 2** ("Rational `3x+1` cycles").

The `3x+1` function `T` of `(1.1)` makes sense on the ring `Q[(2)]` of all rationals `p/q` with `q`
**odd** (the localization `ℤ_(2)`): for `x = p/q` one applies the half-or-`(3·+1)/2` step according to
the **parity of the numerator** `p`. To each `x` one associates its **parity sequence**
`b(x) = (b₀(x), b₁(x), …)` with `bⱼ(x) ≡ Tʲ(x) (mod 2) ∈ {0,1}`.

**Theorem 2.1.** *Given any `0`-`1` vector `v = (v₀, …, v_{n-1})` there is a unique `x ∈ Q[(2)]` which
is periodic of period `n` under `T` and whose parity sequence starts with `v`; it is*
```
  x = x(v) = (2ⁿ − 3^{v₀+⋯+v_{n-1}})⁻¹ · ∑_{j=0}^{n-1} vⱼ · 3^{v_{j+1}+⋯+v_{n-1}} · 2ʲ.      (2.1)
```
*(The proof follows Böhm–Sontacchi [BoS78], Thm 5.)*

## Reused notation (`CC`, `BL`, `B3`)

The map mirrors the corpus `3x+1` maps in the compact "`numerator / 2`" form
`2·T x = x·3^{parity x} + parity x` (cf. `BL.two_mul_T₂` on `ℤ₂` and `CC.T_expand` on
`ℕ`). On `ℕ ⊂ Q[(2)]` it restricts to the integer map `CC.T` (`T_natCast`,
`parity_natCast`). `Q[(2)] = {x : ℚ | Odd x.den}` is `ℚ ∩ ℤ₂` — Lagarias's `Q[(2)]` is exactly the
`BL`/`B3` set `RatInt` viewed inside `ℚ`. The denominator `2ⁿ − 3^{Σ vⱼ}` of `(2.1)` is (up to sign)
the `B3.subspaceDen 3^c − 2^p` and is the explicit periodic point underlying
`B3.blockVal`/`Φ_blockValue`.

## What is proved here, and what is cited

* **Proved.** The map and its defining identity (`two_mul_T`); the integer-restriction bridges
  (`parity_natCast`, `T_natCast`); the **affine recurrence** `two_pow_mul_iterate`
  (`2ⁿ·Tⁿ(x) = 3^{Σv}·x + S(v)` whenever the parity sequence of `x` starts with `v`) — the algebraic
  heart of `(2.1)`; that the denominator `2ⁿ − 3^{Σv}` is odd and nonzero (`cycleDen_*`), so
  `x(v) ∈ Q[(2)]` (`xCycle_mem_Q2`); and the **uniqueness + formula** direction
  (`eq_xCycle_of_periodic`: any rational periodic point with parity sequence `v` *equals* `x(v)`).
* **Cited (`xCycle_realizes`, a literature `axiom`).** The **realization** direction — that the
  explicit `x(v)` really is a period-`n` point whose parity sequence starts with `v` — is the
  Böhm–Sontacchi content; recorded as a cited `axiom`. The headline **Theorem 2.1** (`theorem_2_1`) is
  then *proved* (`∃!`) by combining this realization with the proved uniqueness.

## References
* [Lag90] Lagarias, Jeffrey C. *The set of rational cycles for the `3x+1` problem.* Acta Arithmetica
  56 (1990), 33–53 (§2, Theorem 2.1).
* [BoS78] Böhm, Corrado, and Giovanni Sontacchi. *On the existence of cycles of given length in
  integer sequences like `xₙ₊₁ = xₙ/2` if `xₙ` even, and `xₙ₊₁ = 3xₙ+1` otherwise.* Atti Accad. Naz.
  Lincei Rend. Cl. Sci. Fis. Mat. Natur. (8) 64 (1978), no. 3, 260–264 (Thm 5: the explicit cycle).
* [BL96] Bernstein, Daniel J., and Jeffrey C. Lagarias. *The 3x+1 conjugacy map.* Canadian J. Math.
  48 (1996), no. 6, 1154–1169 (the `2`-adic map `T₂` and parity sequences this restricts/extends).
-/

namespace L90

open Finset

/-! ### The ring `Q[(2)]`, the parity, and the `3x+1` map on `ℚ` -/

/-- **`Q[(2)]`**, Lagarias's ring of rationals with **odd denominator** (the localization `ℤ_(2)`).
As a subset of `ℚ` it is `ℚ ∩ ℤ₂`, i.e. the `BL`/`B3` set `RatInt` viewed inside `ℚ`. -/
@[category API, AMS 11 37, ref "Lag90"]
def Q2 : Set ℚ := {x : ℚ | Odd x.den}

/-- The **parity** of a rational: its numerator mod `2` (`∈ {0,1}`). For `x ∈ Q[(2)]` (odd
denominator) this is the residue of `x` in `ℤ_(2)/2 ≅ ℤ/2`, the analogue of `BL.parity` on `ℤ₂`. -/
@[category API, AMS 11 37, ref "Lag90" "BL96"]
def parity (x : ℚ) : ℕ := (x.num % 2).toNat

/-- The parity is a single bit: `parity x < 2`. -/
@[category API, AMS 11 37, ref "Lag90"]
theorem parity_lt_two (x : ℚ) : parity x < 2 := by
  unfold parity
  omega

/-- The **`3x+1` function on `ℚ`** in the compact numerator form
`T x = (x·3^{parity x} + parity x) / 2` — `x/2` when the numerator is even, `(3x+1)/2` when it is odd.
Mirrors `BL.T₂` on `ℤ₂` and `CC.T` on `ℕ`, and preserves `Q[(2)]`. -/
@[category API, AMS 11 37, ref "Lag90" "BL96"]
noncomputable def T (x : ℚ) : ℚ := (x * 3 ^ (parity x) + (parity x : ℚ)) / 2

/-- Defining identity of `T` (cf. `BL.two_mul_T₂`): `2·T x = x·3^{parity x} + parity x`. -/
@[category API, AMS 11 37, ref "Lag90" "BL96"]
theorem two_mul_T (x : ℚ) : 2 * T x = x * 3 ^ (parity x) + (parity x : ℚ) := by
  unfold T; ring

/-- On `ℕ ⊂ Q[(2)]` the parity is the Collatz parity `CC.X`: `parity ↑n = n % 2`. -/
@[category API, AMS 11 37, ref "Lag90"]
theorem parity_natCast (n : ℕ) : parity (n : ℚ) = CC.X n := by
  unfold parity
  rw [CC.X_eq_mod, Rat.num_natCast]
  omega

/-- On `ℕ ⊂ Q[(2)]` the rational map `T` restricts to the integer map `CC.T`:
`T ↑n = ↑(T n)`. So `(1.1)` is the restriction of this `T` to the integers. -/
@[category API, AMS 11 37, ref "Lag90" "BL96"]
theorem T_natCast (n : ℕ) : T (n : ℚ) = (CC.T n : ℚ) := by
  have hcancel : (2 : ℚ) * T (n : ℚ) = 2 * (CC.T n : ℚ) := by
    rw [two_mul_T, parity_natCast]
    have hexp := CC.T_expand n
    have : (2 : ℚ) * (CC.T n : ℚ)
        = ((3 ^ CC.X n * n + CC.X n : ℕ) : ℚ) := by
      rw [← hexp]; push_cast; ring
    rw [this]; push_cast; ring
  exact mul_left_cancel₀ (by norm_num) hcancel

/-- The **`j`-th bit** `bⱼ(x) ≡ Tʲ(x) (mod 2)` of the parity sequence of `x` (Lagarias's `bⱼ`). -/
@[category API, AMS 11 37, ref "Lag90"]
noncomputable def parityBit (x : ℚ) (j : ℕ) : ℕ := parity (T^[j] x)

/-! ### The explicit periodic point `x(v)` of `(2.1)` -/

/-- The total number of odd steps in one period, `v₀ + ⋯ + v_{n-1}` (the exponent of `3`). -/
@[category API, AMS 11 37, ref "Lag90"]
def totalOdd (n : ℕ) (v : ℕ → ℕ) : ℕ := ∑ k ∈ range n, v k

/-- The numerator `S(v) = ∑_{j<n} vⱼ · 2ʲ · 3^{v_{j+1}+⋯+v_{n-1}}` of `(2.1)`. -/
@[category API, AMS 11 37, ref "Lag90"]
noncomputable def cycleSum (n : ℕ) (v : ℕ → ℕ) : ℚ :=
  ∑ j ∈ range n, (v j : ℚ) * 2 ^ j * 3 ^ (∑ k ∈ Finset.Ico (j + 1) n, v k)

/-- The integer numerator `S(v)` of `(2.1)` (the `ℕ`-form of `cycleSum`, used for `Q[(2)]`-membership). -/
@[category API, AMS 11 37, ref "Lag90"]
def cycleSumNat (n : ℕ) (v : ℕ → ℕ) : ℕ :=
  ∑ j ∈ range n, v j * 2 ^ j * 3 ^ (∑ k ∈ Finset.Ico (j + 1) n, v k)

/-- The integer denominator `2ⁿ − 3^{Σ vⱼ}` of `(2.1)` (up to sign, `B3.subspaceDen`). -/
@[category API, AMS 11 37, ref "Lag90"]
def cycleDenInt (n : ℕ) (v : ℕ → ℕ) : ℤ := 2 ^ n - 3 ^ (totalOdd n v)

/-- The denominator `2ⁿ − 3^{Σ vⱼ}` of `(2.1)` as a rational. -/
@[category API, AMS 11 37, ref "Lag90"]
noncomputable def cycleDen (n : ℕ) (v : ℕ → ℕ) : ℚ := 2 ^ n - 3 ^ (totalOdd n v)

/-- **The explicit periodic point `x(v)` of `(2.1)`**:
`x(v) = (2ⁿ − 3^{Σ vⱼ})⁻¹ · ∑_{j<n} vⱼ · 2ʲ · 3^{v_{j+1}+⋯+v_{n-1}}`. -/
@[category API, AMS 11 37, ref "Lag90"]
noncomputable def xCycle (n : ℕ) (v : ℕ → ℕ) : ℚ := cycleSum n v / cycleDen n v

/-! ### The affine recurrence behind `(2.1)` -/

@[category API, AMS 11 37, ref "Lag90"]
theorem totalOdd_succ (n : ℕ) (v : ℕ → ℕ) : totalOdd (n + 1) v = totalOdd n v + v n := by
  unfold totalOdd; rw [Finset.sum_range_succ]

/-- One-step recurrence for the numerator: `S_{n+1}(v) = 3^{vₙ}·Sₙ(v) + vₙ·2ⁿ`. -/
@[category API, AMS 11 37, ref "Lag90"]
theorem cycleSum_succ (n : ℕ) (v : ℕ → ℕ) :
    cycleSum (n + 1) v = 3 ^ (v n) * cycleSum n v + (v n : ℚ) * 2 ^ n := by
  unfold cycleSum
  rw [Finset.sum_range_succ,
    show Finset.Ico (n + 1) (n + 1) = ∅ from Finset.Ico_self _, Finset.sum_empty, pow_zero,
    mul_one, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [Finset.sum_Ico_succ_top (by omega : j + 1 ≤ n), pow_add]
  ring

/-- **The affine recurrence (the algebraic heart of `(2.1)`).** If the parity sequence of `x` starts
with `v` (`parity (Tʲ x) = vⱼ` for `j < n`), then
```
  2ⁿ · Tⁿ(x) = 3^{v₀+⋯+v_{n-1}} · x + ∑_{j<n} vⱼ · 2ʲ · 3^{v_{j+1}+⋯+v_{n-1}}.
```
Iterating `2·T y = y·3^{parity y} + parity y` (`two_mul_T`) `n` times. Setting `Tⁿ(x) = x` and solving
the resulting affine equation for `x` gives exactly the formula `(2.1)` (`eq_xCycle_of_periodic`). -/
@[category research solved, AMS 11 37, ref "Lag90" "BoS78", group "lag90_rational_cycles"]
theorem two_pow_mul_iterate (n : ℕ) (v : ℕ → ℕ) (x : ℚ)
    (hpar : ∀ j < n, parity (T^[j] x) = v j) :
    2 ^ n * T^[n] x = 3 ^ (totalOdd n v) * x + cycleSum n v := by
  induction n with
  | zero => simp [totalOdd, cycleSum]
  | succ n ih =>
    have ihn := ih (fun j hj => hpar j (by omega))
    rw [Function.iterate_succ', Function.comp_apply, pow_succ, totalOdd_succ, cycleSum_succ, pow_add]
    have hp : parity (T^[n] x) = v n := hpar n (by omega)
    calc 2 ^ n * 2 * T (T^[n] x)
        = 2 ^ n * (2 * T (T^[n] x)) := by ring
      _ = 2 ^ n * (T^[n] x * 3 ^ (v n) + (v n : ℚ)) := by rw [two_mul_T, hp]
      _ = 3 ^ (v n) * (2 ^ n * T^[n] x) + (v n : ℚ) * 2 ^ n := by ring
      _ = 3 ^ (v n) * (3 ^ (totalOdd n v) * x + cycleSum n v) + (v n : ℚ) * 2 ^ n := by rw [ihn]
      _ = 3 ^ (totalOdd n v) * 3 ^ (v n) * x + (3 ^ (v n) * cycleSum n v + (v n : ℚ) * 2 ^ n) := by
          ring

/-! ### `x(v) ∈ Q[(2)]`: the denominator `2ⁿ − 3^{Σv}` is odd and nonzero -/

/-- The denominator `2ⁿ − 3^{Σ vⱼ}` is **odd** (for `n ≥ 1`): `2ⁿ` is even, `3^{Σv}` is odd. -/
@[category API, AMS 11 37, ref "Lag90"]
theorem cycleDenInt_odd (n : ℕ) (v : ℕ → ℕ) (hn : 0 < n) : Odd (cycleDenInt n v) := by
  unfold cycleDenInt
  have h2 : Even ((2 : ℤ) ^ n) := Int.even_pow.mpr ⟨even_two, hn.ne'⟩
  have h3 : Odd ((3 : ℤ) ^ (totalOdd n v)) := Odd.pow ⟨1, by ring⟩
  exact h2.sub_odd h3

/-- The denominator is **nonzero** (odd ⟹ `≠ 0`). -/
@[category API, AMS 11 37, ref "Lag90"]
theorem cycleDenInt_ne_zero (n : ℕ) (v : ℕ → ℕ) (hn : 0 < n) : cycleDenInt n v ≠ 0 := by
  have h := cycleDenInt_odd n v hn
  rintro h0
  rw [h0, Int.odd_iff] at h
  omega

/-- The rational denominator equals the integer one: `cycleDen = ↑(cycleDenInt)`. -/
@[category API, AMS 11 37, ref "Lag90"]
theorem cycleDen_eq_cast (n : ℕ) (v : ℕ → ℕ) : cycleDen n v = (cycleDenInt n v : ℚ) := by
  unfold cycleDen cycleDenInt; push_cast; ring

/-- The rational numerator equals the integer one: `cycleSum = ↑(cycleSumNat)`. -/
@[category API, AMS 11 37, ref "Lag90"]
theorem cycleSum_eq_cast (n : ℕ) (v : ℕ → ℕ) : cycleSum n v = (cycleSumNat n v : ℚ) := by
  unfold cycleSum cycleSumNat
  rw [Nat.cast_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  push_cast; ring

/-- The rational denominator is **nonzero** (for `n ≥ 1`). -/
@[category API, AMS 11 37, ref "Lag90"]
theorem cycleDen_ne_zero (n : ℕ) (v : ℕ → ℕ) (hn : 0 < n) : cycleDen n v ≠ 0 := by
  rw [cycleDen_eq_cast]
  exact_mod_cast cycleDenInt_ne_zero n v hn

/-- **`x(v) ∈ Q[(2)]`** (for `n ≥ 1`): `x(v) = S(v) / (2ⁿ − 3^{Σv})` is an integer over an odd integer,
so its reduced denominator is odd. -/
@[category research solved, AMS 11 37, ref "Lag90", group "lag90_rational_cycles"]
theorem xCycle_mem_Q2 (n : ℕ) (v : ℕ → ℕ) (hn : 0 < n) : xCycle n v ∈ Q2 := by
  rw [Q2, Set.mem_setOf_eq]
  have heq : xCycle n v = Rat.divInt (cycleSumNat n v : ℤ) (cycleDenInt n v) := by
    unfold xCycle
    rw [cycleSum_eq_cast, cycleDen_eq_cast, Rat.divInt_eq_div]
    push_cast; ring
  have hdvd : ((xCycle n v).den : ℤ) ∣ cycleDenInt n v := by rw [heq]; exact Rat.den_dvd _ _
  have hdvd' : (xCycle n v).den ∣ (cycleDenInt n v).natAbs := by
    have h := Int.natAbs_dvd_natAbs.mpr hdvd
    rwa [Int.natAbs_natCast] at h
  have hodd : Odd (cycleDenInt n v).natAbs := Int.natAbs_odd.mpr (cycleDenInt_odd n v hn)
  obtain ⟨t, ht⟩ := hdvd'
  rw [ht] at hodd
  exact (Nat.odd_mul.mp hodd).1

/-! ### Uniqueness, the cited realization, and Theorem 2.1 -/

/-- **Uniqueness + formula (proved).** Any rational `x` that is periodic of period `n` (`Tⁿ x = x`)
and whose parity sequence starts with `v` is **the** explicit point `x(v)` of `(2.1)`. *Proof:* the
affine recurrence `two_pow_mul_iterate` with `Tⁿ x = x` gives `(2ⁿ − 3^{Σv})·x = S(v)`, and the
denominator is nonzero, so `x = S(v)/(2ⁿ − 3^{Σv}) = x(v)`. -/
@[category research solved, AMS 11 37, ref "Lag90" "BoS78", group "lag90_rational_cycles"]
theorem eq_xCycle_of_periodic (n : ℕ) (v : ℕ → ℕ) (x : ℚ) (hn : 0 < n)
    (hper : T^[n] x = x) (hpar : ∀ j < n, parity (T^[j] x) = v j) :
    x = xCycle n v := by
  have hrec := two_pow_mul_iterate n v x hpar
  rw [hper] at hrec
  unfold xCycle
  rw [eq_div_iff (cycleDen_ne_zero n v hn)]
  unfold cycleDen
  linear_combination hrec

/-- **Realization (Böhm–Sontacchi; cited literature `axiom`).** The explicit point `x(v)` of `(2.1)`
really is a period-`n` point of `T` whose parity sequence starts with the `0`-`1` vector `v`. This is
the existence half of Theorem 2.1, proved in [Lag90] via Böhm–Sontacchi [BoS78, Thm 5]; recorded as a
cited `axiom`, from which `theorem_2_1` is assembled together with the proved uniqueness
`eq_xCycle_of_periodic`. -/
@[category research solved, AMS 11 37, ref "Lag90" "BoS78", group "lag90_rational_cycles"]
axiom xCycle_realizes (n : ℕ) (hn : 0 < n) (v : ℕ → ℕ) (hv : ∀ j < n, v j < 2) :
    T^[n] (xCycle n v) = xCycle n v ∧ ∀ j < n, parity (T^[j] (xCycle n v)) = v j

/-- **Theorem 2.1 (Lagarias 1990, §2).** *Given any `0`-`1` vector `v = (v₀, …, v_{n-1})` there is a
**unique** `x ∈ Q[(2)]` which is periodic of period `n` under `T` and whose parity sequence starts
with `v`* — and it is the explicit point `x(v)` of `(2.1)` (`xCycle`).

Assembled (`∃!`) from the cited realization `xCycle_realizes` (existence) and the proved
`eq_xCycle_of_periodic` (uniqueness + that the witness is `x(v) = (2.1)`); `xCycle_mem_Q2` gives
`x(v) ∈ Q[(2)]`. -/
@[category research solved, AMS 11 37, ref "Lag90" "BoS78", group "lag90_rational_cycles"]
theorem theorem_2_1 (n : ℕ) (hn : 0 < n) (v : ℕ → ℕ) (hv : ∀ j < n, v j < 2) :
    ∃! x : ℚ, x ∈ Q2 ∧ T^[n] x = x ∧ ∀ j < n, parity (T^[j] x) = v j := by
  obtain ⟨hper, hparv⟩ := xCycle_realizes n hn v hv
  refine ⟨xCycle n v, ⟨xCycle_mem_Q2 n v hn, hper, hparv⟩, ?_⟩
  rintro y ⟨-, hyper, hypar⟩
  exact eq_xCycle_of_periodic n v y hn hyper hypar

end L90
