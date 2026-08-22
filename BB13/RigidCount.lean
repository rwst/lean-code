/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BB13.QualityLedger
import BB13.CarryTransducer
import BB13.LeastException

/-!
# Counting the quality-`>1.3` triples of the rigid shape (strategy B6(iii))

Tier (iii) of strategy **B6** of `plans/report3-BB13.html` is the item's one *unconditional*
target:

> count the quality-`>1.3` triples `3ᵃ − μ2ᵐ = k`; Bennett's uniform `≤2` theorems are the
> nearest relatives, the exact gap being the *moving* small term `k`.

B6(i) pinned it as the statement "to which Problem 1 reduces".  This file proves the dictionary
that connects it to the rest of the corpus, and the dictionary prices the item.

## The rigid triple

`rigidK a m μ = 3ᵃ − μ2ᵐ` is the small term of the triple `μ2ᵐ + k = 3ᵃ`; the multiplier `μ` is
**free**, which is the only difference from the frame triple of `BB13/QualityLedger.lean` (that
one is the diagonal `m = a`, `μ = mₐ`, `rigidK_diag`).  Following B6(i), the quality is read on
the *primitive* triple and stated without logarithms:

`RigidQuality N M a m μ  :  rad(A·B·C)^N · g^M ≤ (3ᵃ)^M`,  `g = gcd(μ, |k|)`,

which is "quality `≥ N/M`" with `C = 3ᵃ/g`.  (Using `3ᵃ` rather than `max(3ᵃ, μ2ᵐ)` understates
the quality when `k < 0` — B6(i)'s convention, under which the family's record is `1.5463` at
`a = 10`; it costs one bit in the constants below and nothing else.)

## What the item's target actually is (§2–§3)

**Forward** (`rigid_quality_of_block`).  If the binary word of `3ᵃ` is constant on `[t, m)` — i.e.
`|k| ≤ 2ᵗ`, `t + L = m` — then

`41L ≥ 15a + 147  ⟹  quality ≥ 13/10`,

so a block of relative length `15/41 = 0.36585` manufactures the item's target.

**Backward** (`rigid_prod_of_quality`, `rigid_block_of_quality`).  Conversely quality `≥ 13/10`
forces `3^{3a}|k|¹³ ≤ 2^{13m+13}S¹³`, where `S = μ|k|/rad` is the **powerful surplus** of the
triple — and *only* the surplus stands between the quality and a block of relative length
`57/156 = 0.36538`.  The two constants bracket the true exchange rate `3log₂3/13 = 0.36576`, so
the dictionary is tight:

> a rigid triple of quality `≥ 13/10` is a constant digit block of `3ᵃ` of relative length
> `0.3658 ± 0.0005`, *unless* its multiplier or its small term is powerful.

## Consequences (§4–§6)

* **The approximation half is already a theorem, and it is Mahler's** (`rigidDelta_finite`).
  With the surplus bounded by `2^{a/8}` the block has relative length `≥ 1/7`, and [DD90] Prop. 4
  — `BB13.longBlock_finite`, Ridout — leaves finitely many `a`.  This is the file's only
  declaration that is not `std3`; it inherits the root's cited Ridout axiom.  It is ineffective,
  and since `0.36585 < 0.41504` it *implies* the finiteness of `𝓔`: the target's usable half is
  B7's global run bound in `abc` clothing, and B7 already priced that.
* **The target contains Problem 1** (`exception_rigid_quality`, `exceptions_finite_of_rigid_finite`):
  every exception `a ≥ 74` is a quality-`≥13/10` rigid triple (B6(i)'s `exception_quality` at the
  diagonal), so counting the target set is at least as hard as Problem 1 — *strictly* harder,
  because the threshold `0.36585` sits below the mandatory exception block `0.41463`.
* **The gap to Bennett is misidentified.**  Fixing the small term finitises nothing: `k = 1` has
  a solution at *every* index (`rigid_k_one`, `rigid_k_one_infinite` — take `2ᵐ` the exact power
  of `2` in `3ᵃ − 1`).  [Ben01] needs the multiplier *and* the small term fixed, and at index `a`
  the quality condition leaves `≥ 2^{1.219a}` admissible pairs (`bennett_pairs_ge`) against a
  truth of `≤ (65a+41)/41` corridor triples (`rigid_unique_per_m`, `rigid_m_le`).  The moving
  parameter that breaks the analogy is `μ`, not `k`.
* **A4's fibre tree is a path** (`fibre_downward_closed`).  After B8 the fibre over `a` is the
  interval `[a, a+min(v₂(mₐ), D(a))]`, so there is no branching to induct over and "bound the
  tree depth 2-adically" is Problem 2 verbatim.
* **Effectivity buys nothing new** (`effective_count_solves_problem_one`): an effective global run
  bound at the rate this target needs (`41P ≤ 15Q`) is below B7's `17/41` and therefore already
  settles Problem 1 effectively — far beyond anything in print.

## Trust ledger

`std3` (`propext`, `Classical.choice`, `Quot.sound`) everywhere except `rigidDelta_finite`, which
routes through `BB13.longBlock_finite` and hence the root's cited Ridout axiom.  No `sorry`, no
`native_decide`.  The numerical inputs are the root's `3⁴¹ ≤ 2⁶⁵` (upper) and `2¹⁹ ≤ 3¹²` (lower,
`two_pow_le_three_pow`); they are why the forward and backward slopes differ in the fifth decimal.

## Claim level

Formalisation of a dictionary and of a pricing argument.  **No count is proved here**, and none
can be: the unconditional statement the item asks for is an instance of the `abc` conjecture at
`ε = 0.3`, of which only the approximation half is a theorem.

## References

* `plans/report3-BB13.html` §6 (B6, tier (iii)), §5 (Q2.4), §1.4; `plans/note-BB13-B6iii.html`.
* [Ben01] M. A. Bennett, *Rational approximation to algebraic numbers of small height*, J. reine
  angew. Math. **535** (2001) — the uniform `≤2`-solution theorems the item names.
* [DD90] F. Delmer, J.-M. Deshouillers, *On the computation of `g(k)` in Waring's problem*, Math.
  Comp. **54** (1990), Prop. 4 — the `o(m)` global run bound, in the corpus as `longBlock_finite`.
* [Mas85] D. W. Masser, *Open problems* (1985); [Oes88] J. Oesterlé, Sém. Bourbaki 694 (1988) —
  the `abc` conjecture and the quality convention.
* [Mah57] K. Mahler, *On the fractional parts of the powers of a rational number II*, Mathematika
  **4** (1957) — what the approximation half of the target is.
* `BB13/b6iii_rigidcount.py` — the census: on the corridor and for `a ≤ 45`, *every* rigid triple
  of quality `≥ 13/10` is produced by a powerful part, not by an approximation.
-/

namespace BB13

open UniqueFactorizationMonoid

/-! ## 1. The rigid triple and its quality

`3ᵃ = μ2ᵐ + k`.  The frame triple of `BB13/QualityLedger.lean` is the diagonal `m = a`,
`μ = mₐ` (§5). -/

/-- **The small term of the rigid triple** `3ᵃ = μ2ᵐ + k`. -/
def rigidK (a m mu : ℕ) : ℤ := 3 ^ a - (mu : ℤ) * 2 ^ m

/-- The product `A·B·C` of the rigid triple: `A = μ2ᵐ`, `B = |k|`, `C = 3ᵃ`. -/
noncomputable def rigidProd (a m mu : ℕ) : ℕ := 3 ^ a * (mu * 2 ^ m) * (rigidK a m mu).natAbs

/-- Its radical.  Dividing out the content does not change it (the prime `3` survives in `C`). -/
noncomputable def rigidRad (a m mu : ℕ) : ℕ := radical (rigidProd a m mu)

/-- **The content** `g = gcd(μ, |k|)`; it is a power of `3` (`rigidGcd_dvd_three_pow`). -/
def rigidGcd (a m mu : ℕ) : ℕ := Nat.gcd mu (rigidK a m mu).natAbs

/-- **"The primitive triple at `(a, m, μ)` has `abc` quality at least `N/M`"**, in the integer
form of B6(i): `rad^N·g^M ≤ (3ᵃ)^M`, i.e. `rad^N ≤ C^M` with `C = 3ᵃ/g`. -/
def RigidQuality (N M a m mu : ℕ) : Prop :=
  rigidRad a m mu ^ N * rigidGcd a m mu ^ M ≤ (3 ^ a) ^ M

/-- `k ≠ 0`: an odd number is not `μ2ᵐ`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem rigidK_ne_zero {a m mu : ℕ} (hm : 1 ≤ m) : rigidK a m mu ≠ 0 := by
  intro h
  rw [rigidK, sub_eq_zero] at h
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have h3 : (3 : ℕ) ^ a = mu * 2 ^ (m' + 1) := by exact_mod_cast h
  have h2 : 2 ∣ (3 : ℕ) ^ a := ⟨mu * 2 ^ m', by rw [h3]; ring⟩
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
  norm_num at this

/-- The content divides `3ᵃ`, hence is a power of `3`: it divides `μ2ᵐ` and `k`, whose sum is
`3ᵃ`. -/
@[category API, AMS 11, ref "Mas85", group "bugeaud_10_13"]
theorem rigidGcd_dvd_three_pow (a m mu : ℕ) : rigidGcd a m mu ∣ 3 ^ a := by
  have h1 : (rigidGcd a m mu : ℤ) ∣ (mu : ℤ) := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)
  have h2 : (rigidGcd a m mu : ℤ) ∣ rigidK a m mu := by
    refine Int.dvd_natAbs.mp ?_
    exact_mod_cast Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right mu (rigidK a m mu).natAbs)
  have h3 : (rigidGcd a m mu : ℤ) ∣ (3 : ℤ) ^ a := by
    have : (3 : ℤ) ^ a = (mu : ℤ) * 2 ^ m + rigidK a m mu := by rw [rigidK]; ring
    rw [this]
    exact dvd_add (Dvd.dvd.mul_right h1 _) h2
  have h4 : (rigidGcd a m mu : ℤ) ∣ ((3 ^ a : ℕ) : ℤ) := by push_cast; exact h3
  exact_mod_cast h4

@[category API, AMS 11, ref "Mas85", group "bugeaud_10_13"]
theorem rigidGcd_pos (a m mu : ℕ) : 0 < rigidGcd a m mu :=
  Nat.pos_of_dvd_of_pos (rigidGcd_dvd_three_pow a m mu) (by positivity)

/-- `(bⁿ)ᵏ = b^{kn}` — the exponent bookkeeping used throughout. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem pow_pow_eq (b n k : ℕ) : (b ^ n) ^ k = b ^ (k * n) := by
  rw [← pow_mul, Nat.mul_comm]

/-- The arithmetic step of `rigid_rad_core`, with the content named: `R ≤ 6μ₁κ`, `μ = gμ₁`,
`K = gκ` give `R¹³g¹⁰ ≤ (6μK)¹³` (the content re-enters `26` times and is spent `10`). -/
@[category API, AMS 11, ref "Mas85", group "bugeaud_10_13"]
theorem rigid_rad_step {R g μ₁ κ mu K : ℕ} (hg : 0 < g) (hmu : mu = g * μ₁) (hK : K = g * κ)
    (hrad : R ≤ 6 * (μ₁ * κ)) : R ^ 13 * g ^ 10 ≤ (6 * (mu * K)) ^ 13 := by
  subst hmu; subst hK
  calc R ^ 13 * g ^ 10 ≤ (6 * (μ₁ * κ)) ^ 13 * g ^ 10 :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hrad 13)
    _ ≤ (6 * (μ₁ * κ)) ^ 13 * g ^ 26 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hg (by norm_num))
    _ = (6 * (g * μ₁ * (g * κ))) ^ 13 := by ring

/-- **The radical bookkeeping.**  `rad^13·g^10 ≤ (6μ|k|)^13`: the primes `2` and `3` contribute
once each, `μ/g` and `|k|/g` at most themselves, and the content — divided out of both — comes
back with room to spare.  This is `radical_rigid_le` of B6(i) at a free multiplier. -/
@[category research solved, AMS 11, ref "Mas85" "Oes88", group "bugeaud_10_13"]
theorem rigid_rad_core {a m mu : ℕ} (ha : 1 ≤ a) (hm : 1 ≤ m) (hmu : 1 ≤ mu) :
    rigidRad a m mu ^ 13 * rigidGcd a m mu ^ 10
      ≤ (6 * (mu * (rigidK a m mu).natAbs)) ^ 13 := by
  obtain ⟨v, -, hgv⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (rigidGcd_dvd_three_pow a m mu)
  obtain ⟨μ₁, hμ₁⟩ : rigidGcd a m mu ∣ mu := Nat.gcd_dvd_left _ _
  obtain ⟨κ, hκ⟩ : rigidGcd a m mu ∣ (rigidK a m mu).natAbs := Nat.gcd_dvd_right _ _
  have hK0 : (rigidK a m mu).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (rigidK_ne_zero hm)
  have hμ₁0 : μ₁ ≠ 0 := by
    intro h; rw [h, Nat.mul_zero] at hμ₁; omega
  have hκ0 : κ ≠ 0 := by
    intro h; rw [h, Nat.mul_zero] at hκ; exact hK0 hκ
  have hfac : rigidProd a m mu = μ₁ * 2 ^ m * κ * 3 ^ (a + (v + v)) := by
    rw [rigidProd]
    nth_rewrite 1 [hμ₁]
    rw [hκ, hgv]; ring
  have hrad : rigidRad a m mu ≤ 6 * (μ₁ * κ) := by
    rw [rigidRad, hfac]
    exact radical_rigid_le hμ₁0 hκ0 (by omega) (by omega)
  exact rigid_rad_step (rigidGcd_pos a m mu) hμ₁ hκ hrad

/-! ## 2. Forward: a digit block manufactures the quality

The engine is B6(i)'s exponent ledger `twelve_pow_le`, at `N = 13`, `F = 3a`, `G = 13L`. -/

/-- The size half of the forward direction: `(6μ|k|)¹³ ≤ (3ᵃ)¹⁰` already gives the quality. -/
@[category API, AMS 11, ref "Mas85" "Oes88", group "bugeaud_10_13"]
theorem rigid_quality_of_prod {a m mu : ℕ} (ha : 1 ≤ a) (hm : 1 ≤ m) (hmu : 1 ≤ mu)
    (h : (6 * (mu * (rigidK a m mu).natAbs)) ^ 13 ≤ (3 ^ a) ^ 10) :
    RigidQuality 13 10 a m mu :=
  le_trans (rigid_rad_core ha hm hmu) h

/-- **A constant digit block of `3ᵃ` of relative length `15/41` is a quality-`13/10` triple.**
If the word of `3ᵃ` is constant on `[t, m)` (`|k| ≤ 2ᵗ`, `t + L = m`) and `41L ≥ 15a + 147`, then
the rigid triple at `(a, m, μ)` has quality `≥ 13/10`.  `15/41 = 0.36585`, against the exchange
rate `3log₂3/13 = 0.36576` and B7's mandatory exception block `17/41 = 0.41463`. -/
@[category research solved, AMS 11, ref "Mas85" "Oes88" "DD90", group "bugeaud_10_13"]
theorem rigid_quality_of_block {a m mu t L : ℕ} (ha : 1 ≤ a) (hmu : 1 ≤ mu)
    (htL : t + L = m) (hk : (rigidK a m mu).natAbs ≤ 2 ^ t)
    (hword : mu * 2 ^ m ≤ 2 * 3 ^ a) (hL : 15 * a + 147 ≤ 41 * L) :
    RigidQuality 13 10 a m mu := by
  have hLpos : 1 ≤ L := by omega
  have hm : 1 ≤ m := by omega
  set K := (rigidK a m mu).natAbs with hKdef
  -- `6μ|k|·2^L ≤ 12·3ᵃ`
  have key : 6 * (mu * K) * 2 ^ L ≤ 12 * 3 ^ a := by
    calc 6 * (mu * K) * 2 ^ L ≤ 6 * (mu * 2 ^ t) * 2 ^ L := by
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hk))
      _ = 6 * (mu * 2 ^ m) := by rw [← htL, pow_add]; ring
      _ ≤ 12 * 3 ^ a := by omega
  have h13 : (6 * (mu * K)) ^ 13 * 2 ^ (13 * L) ≤ 12 ^ 13 * 3 ^ (13 * a) := by
    have hp := Nat.pow_le_pow_left key 13
    have e1 : (6 * (mu * K) * 2 ^ L) ^ 13 = (6 * (mu * K)) ^ 13 * 2 ^ (13 * L) := by
      rw [mul_pow, pow_pow_eq]
    have e2 : ((12 : ℕ) * 3 ^ a) ^ 13 = 12 ^ 13 * 3 ^ (13 * a) := by
      rw [mul_pow, pow_pow_eq]
    rw [e1, e2] at hp
    exact hp
  have hcert : (12 : ℕ) ^ 13 * 3 ^ (3 * a) ≤ 2 ^ (13 * L) := twelve_pow_le (by omega)
  have hfin : (6 * (mu * K)) ^ 13 * 2 ^ (13 * L) ≤ (3 ^ a) ^ 10 * 2 ^ (13 * L) := by
    calc (6 * (mu * K)) ^ 13 * 2 ^ (13 * L) ≤ 12 ^ 13 * 3 ^ (13 * a) := h13
      _ = 12 ^ 13 * 3 ^ (3 * a) * 3 ^ (10 * a) := by rw [mul_assoc, ← pow_add]; congr 2; ring
      _ ≤ 2 ^ (13 * L) * 3 ^ (10 * a) := Nat.mul_le_mul_right _ hcert
      _ = (3 ^ a) ^ 10 * 2 ^ (13 * L) := by rw [pow_pow_eq]; ring
  exact rigid_quality_of_prod ha hm hmu
    (Nat.le_of_mul_le_mul_right hfin (by positivity : 0 < (2 : ℕ) ^ (13 * L)))

/-! ## 3. Backward: the quality is a digit block, up to the powerful surplus

`S` is any bound for `μ|k|/rad`: the amount by which the multiplier and the small term fail to be
squarefree.  It is the *only* leak between the two directions. -/

/-- **The split.**  Quality `≥ 13/10` with surplus `S` forces `3^{3a}|k|¹³ ≤ 2^{13m+13}S¹³` —
i.e. `|k|/2ᵐ ≤ 4S·2^{−0.3658a}`.  With `S = 1` (squarefree parts) this is exactly the converse of
`rigid_quality_of_block`; with `S` large it is vacuous, and that is where `abc` lives. -/
@[category research solved, AMS 11, ref "Mas85" "Oes88", group "bugeaud_10_13"]
theorem rigid_prod_of_quality {a m mu S : ℕ} (hq : RigidQuality 13 10 a m mu)
    (hS : mu * (rigidK a m mu).natAbs ≤ S * rigidRad a m mu)
    (hlow : 3 ^ a ≤ 2 * (mu * 2 ^ m)) :
    3 ^ (3 * a) * (rigidK a m mu).natAbs ^ 13 ≤ 2 ^ (13 * m + 13) * S ^ 13 := by
  set K := (rigidK a m mu).natAbs with hKdef
  have hrad : rigidRad a m mu ^ 13 ≤ (3 ^ a) ^ 10 := by
    refine le_trans ?_ hq
    exact Nat.le_mul_of_pos_right _ (pow_pos (rigidGcd_pos a m mu) 10)
  have hprod : (mu * K) ^ 13 ≤ S ^ 13 * (3 ^ a) ^ 10 := by
    calc (mu * K) ^ 13 ≤ (S * rigidRad a m mu) ^ 13 := Nat.pow_le_pow_left hS 13
      _ = S ^ 13 * rigidRad a m mu ^ 13 := by rw [mul_pow]
      _ ≤ S ^ 13 * (3 ^ a) ^ 10 := Nat.mul_le_mul_left _ hrad
  have hexp : (2 * (mu * 2 ^ m) * K) ^ 13 = 2 ^ (13 * m + 13) * (mu * K) ^ 13 := by
    rw [pow_add, show (2 : ℕ) * (mu * 2 ^ m) * K = 2 ^ m * (2 * (mu * K)) from by ring,
      mul_pow, pow_pow_eq, mul_pow]
    ring
  have hbig : (3 ^ a) ^ 13 * K ^ 13 ≤ 2 ^ (13 * m + 13) * S ^ 13 * (3 ^ a) ^ 10 := by
    calc (3 ^ a) ^ 13 * K ^ 13 = (3 ^ a * K) ^ 13 := by rw [mul_pow]
      _ ≤ (2 * (mu * 2 ^ m) * K) ^ 13 := Nat.pow_le_pow_left (Nat.mul_le_mul_right _ hlow) 13
      _ = 2 ^ (13 * m + 13) * (mu * K) ^ 13 := hexp
      _ ≤ 2 ^ (13 * m + 13) * (S ^ 13 * (3 ^ a) ^ 10) := Nat.mul_le_mul_left _ hprod
      _ = 2 ^ (13 * m + 13) * S ^ 13 * (3 ^ a) ^ 10 := by ring
  have hsum : (3 : ℕ) ^ (3 * a) * (3 ^ a) ^ 10 = (3 ^ a) ^ 13 := by
    rw [pow_pow_eq, pow_pow_eq, ← pow_add]
    congr 1
    ring
  have hL : 3 ^ (3 * a) * K ^ 13 * (3 ^ a) ^ 10 ≤ 2 ^ (13 * m + 13) * S ^ 13 * (3 ^ a) ^ 10 := by
    calc 3 ^ (3 * a) * K ^ 13 * (3 ^ a) ^ 10 = 3 ^ (3 * a) * (3 ^ a) ^ 10 * K ^ 13 := by ring
      _ = (3 ^ a) ^ 13 * K ^ 13 := by rw [hsum]
      _ ≤ 2 ^ (13 * m + 13) * S ^ 13 * (3 ^ a) ^ 10 := hbig
  exact Nat.le_of_mul_le_mul_right hL (by positivity)

/-- `2¹⁹ ≤ 3¹²` — the *lower* rational bound `log₂3 > 19/12 = 1.58333`, the mirror of the root's
`three_pow_le_two_pow`.  It is what turns the split into a digit block. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem two_pow_le_three_pow (k : ℕ) : (2 : ℕ) ^ (19 * k) ≤ 3 ^ (12 * k) := by
  rw [pow_mul, pow_mul]
  exact Nat.pow_le_pow_left (by norm_num) k

/-- **The quality is a block.**  Quality `≥ 13/10`, surplus `≤ 2ˢ`, and `52(L+1+s) < 19a` give a
constant digit block of `3ᵃ` of length `L` ending at bit `m`.  The slope `19/52 = 0.36538` is the
backward companion of `rigid_quality_of_block`'s `15/41 = 0.36585`. -/
@[category research solved, AMS 11, ref "Mas85" "Oes88" "DD90", group "bugeaud_10_13"]
theorem rigid_block_of_quality {a m mu S s L : ℕ} (hm : 1 ≤ m) (hq : RigidQuality 13 10 a m mu)
    (hS : mu * (rigidK a m mu).natAbs ≤ S * rigidRad a m mu) (hSs : S ≤ 2 ^ s)
    (hlow : 3 ^ a ≤ 2 * (mu * 2 ^ m)) (hword : 2 ^ m ≤ 2 * 3 ^ a)
    (hLs : 52 * (L + 1 + s) < 19 * a) :
    ∃ t : ℕ, t + L = m ∧ IsBlock (3 ^ a) t m := by
  set K := (rigidK a m mu).natAbs with hKdef
  have hbase := rigid_prod_of_quality hq hS hlow
  have hK1 : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr (rigidK_ne_zero hm))
  -- the surplus, absorbed
  have hsplit : 3 ^ (3 * a) * K ^ 13 ≤ 2 ^ (13 * m + 13 + 13 * s) := by
    calc 3 ^ (3 * a) * K ^ 13 ≤ 2 ^ (13 * m + 13) * S ^ 13 := hbase
      _ ≤ 2 ^ (13 * m + 13) * (2 ^ s) ^ 13 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hSs 13)
      _ = 2 ^ (13 * m + 13 + 13 * s) := by rw [pow_pow_eq, ← pow_add]
  -- the certificate `2^{13(L+1+s)} < 3^{3a}`
  have hcert : (2 : ℕ) ^ (13 * (L + 1 + s)) < 3 ^ (3 * a) := by
    have h4 : ((2 : ℕ) ^ (13 * (L + 1 + s))) ^ 4 < (3 ^ (3 * a)) ^ 4 := by
      calc ((2 : ℕ) ^ (13 * (L + 1 + s))) ^ 4 = 2 ^ (52 * (L + 1 + s)) := by
            rw [pow_pow_eq]; congr 1; ring
        _ < 2 ^ (19 * a) := Nat.pow_lt_pow_right (by norm_num) hLs
        _ ≤ 3 ^ (12 * a) := two_pow_le_three_pow a
        _ = (3 ^ (3 * a)) ^ 4 := by rw [pow_pow_eq]; congr 1; ring
    exact lt_of_pow_lt_pow_left₀ 4 (by positivity) h4
  -- `L ≤ m`, else the certificate is contradicted outright
  have hLm : L ≤ m := by
    by_contra hcon
    have h1 : 3 ^ (3 * a) ≤ 3 ^ (3 * a) * K ^ 13 :=
      Nat.le_mul_of_pos_right _ (by positivity)
    have h2 : (2 : ℕ) ^ (13 * m + 13 + 13 * s) ≤ 2 ^ (13 * (L + 1 + s)) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    exact absurd (le_trans h1 (le_trans hsplit h2)) (not_le.mpr hcert)
  refine ⟨m - L, by omega, hword, ?_⟩
  -- `cres (3ᵃ) m ≤ |k| < 2^{m−L}`
  have hklt : K < 2 ^ (m - L) := by
    by_contra hcon
    have hge : (2 : ℕ) ^ (m - L) ≤ K := by omega
    have h1 : 3 ^ (3 * a) * 2 ^ (13 * (m - L)) ≤ 2 ^ (13 * (m - L)) * 2 ^ (13 * (L + 1 + s)) := by
      calc 3 ^ (3 * a) * 2 ^ (13 * (m - L)) = 3 ^ (3 * a) * (2 ^ (m - L)) ^ 13 := by
            rw [pow_pow_eq]
        _ ≤ 3 ^ (3 * a) * K ^ 13 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hge 13)
        _ ≤ 2 ^ (13 * m + 13 + 13 * s) := hsplit
        _ = 2 ^ (13 * (m - L)) * 2 ^ (13 * (L + 1 + s)) := by rw [← pow_add]; congr 1; omega
    have h4 : 3 ^ (3 * a) ≤ 2 ^ (13 * (L + 1 + s)) :=
      Nat.le_of_mul_le_mul_right (by rw [Nat.mul_comm (2 ^ (13 * (L + 1 + s)))]; exact h1)
        (by positivity)
    exact absurd h4 (not_le.mpr hcert)
  have hcres : (cres (3 ^ a) m : ℤ) ≤ (K : ℤ) := by
    have h := cres_le_abs (3 ^ a) m (mu : ℤ)
    have heq : |((3 ^ a : ℕ) : ℤ) - (mu : ℤ) * 2 ^ m| = (K : ℤ) := by
      rw [hKdef, rigidK, Int.abs_eq_natAbs]
      push_cast
      ring_nf
    rw [heq] at h
    exact h
  have hcn : cres (3 ^ a) m ≤ K := by exact_mod_cast hcres
  omega

/-! ## 4. The approximation half of the target set is finite — and it is Mahler's theorem

`RigidDelta` is the item's target set restricted to a *sub-exponential* powerful surplus
(`S ≤ 2^{a/8}`).  Its finiteness is [DD90] Prop. 4 with nothing added. -/

/-- **The approximation half of B6(iii)'s target set**: indices carrying a rigid triple of
quality `≥ 13/10` whose powerful surplus is at most `2^{a/8}`. -/
def RigidDelta (a : ℕ) : Prop :=
  ∃ m mu s : ℕ, 1 ≤ m ∧ 1 ≤ mu ∧ 8 * s ≤ a ∧ 2 ^ m ≤ 2 * 3 ^ a ∧ 3 ^ a ≤ 2 * (mu * 2 ^ m) ∧
    mu * (rigidK a m mu).natAbs ≤ 2 ^ s * rigidRad a m mu ∧ RigidQuality 13 10 a m mu

/-- **B6(iii)'s unconditional target, approximation half: already a theorem, and already
Mahler's.**  Only finitely many indices carry a rigid triple of quality `≥ 13/10` with surplus
`≤ 2^{a/8}` — because such a triple is a constant digit block of `3ᵃ` of relative length `≥ 1/7`,
and `BB13.longBlock_finite` ([DD90] Prop. 4, Ridout) leaves finitely many of those.

Two caveats keep this honest.  (a) The surplus bound is a *hypothesis*: the target set proper —
`exceptions_finite_of_rigid_finite`'s set — also contains the powerful accidents, and there
`abc` begins; measured, the frame's own surplus exceeds `2^{a/8}` at several small indices
(`BB13/b6iii_rigidcount.py`, [B]).  (b) The block produced here is *unanchored*, so this is B7's
global run problem, which B7 priced at twice the anchored one; and the corpus's unconditional
input is the same Ridout budget in both cases.  The item's "unconditional target" is therefore
B7's global run bound in `abc` clothing, at a rate (`15/41 = 0.36585`) even below the mandatory
exception block (`17/41 = 0.41463`).

The file's single non-`std3` declaration: it inherits the root's cited Ridout axiom through
`longBlock_finite`. -/
@[category research solved, AMS 11, ref "DD90" "Mah57" "Mas85" "Ben01", group "bugeaud_10_13"]
theorem rigidDelta_finite : {a : ℕ | RigidDelta a}.Finite := by
  have hfin := longBlock_finite (ε := 1 / 7) (by norm_num)
  refine Set.Finite.subset (Set.Finite.union (Set.finite_lt_nat 35) hfin) ?_
  rintro a ⟨m, mu, s, hm, hmu, hs, hword, hlow, hS, hq⟩
  by_cases hA : a < 35
  · exact Or.inl hA
  · refine Or.inr ?_
    have hLs : 52 * (a / 6 + 1 + s) < 19 * a := by omega
    obtain ⟨t, htL, hblk⟩ := rigid_block_of_quality hm hq hS le_rfl hlow hword hLs
    refine ⟨t, a / 6, ?_, by rwa [htL]⟩
    have h7 : a ≤ 7 * (a / 6) := by omega
    have h7R : (a : ℝ) ≤ 7 * ((a / 6 : ℕ) : ℝ) := by exact_mod_cast h7
    linarith

/-! ## 5. The diagonal: every exception is in the target set

The frame triple of `BB13/QualityLedger.lean` is `(a, a, mₐ)`. -/

/-- The frame's small term is the rigid one at `m = a`, `μ = mₐ`. -/
@[category API, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem rigidK_diag (a : ℕ) : rigidK a a (mNat a) = resid 3 2 a := by
  rw [rigidK, resid, Mnum_eq_mNat]
  push_cast
  ring

@[category API, AMS 11, ref "Mas85" "Bug12", group "bugeaud_10_13"]
theorem rigidProd_diag (a : ℕ) : rigidProd a a (mNat a) = frameProd a := by
  rw [rigidProd, frameProd, rigidK_diag]
  ring

@[category API, AMS 11, ref "Mas85" "Bug12", group "bugeaud_10_13"]
theorem rigidRad_diag (a : ℕ) : rigidRad a a (mNat a) = frameRad a := by
  rw [rigidRad, frameRad, rigidProd_diag]

/-- The two contents agree: `gcd(mₐ, |kₐ|) = gcd(mₐ, 3ᵃ)`, because `mₐ2ᵃ + kₐ = 3ᵃ`. -/
@[category API, AMS 11, ref "Mas85" "Bug12", group "bugeaud_10_13"]
theorem rigidGcd_diag (a : ℕ) : rigidGcd a a (mNat a) = frameGcd a := by
  refine Nat.dvd_antisymm ?_ ?_
  · exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _) (rigidGcd_dvd_three_pow a a (mNat a))
  · refine Nat.dvd_gcd (Nat.gcd_dvd_left _ _) ?_
    rw [rigidK_diag]
    exact frameGcd_dvd_resid a

/-- **Every exception `a ≥ 74` is one of the triples B6(iii) proposes to count.**  This is
B6(i)'s `exception_quality` read at the diagonal of the rigid family. -/
@[category research solved, AMS 11, ref "Mas85" "Oes88" "Bug12", group "bugeaud_10_13"]
theorem exception_rigid_quality {a : ℕ} (ha : 74 ≤ a) (hf : IsFailure 3 2 (3 / 4) a) :
    RigidQuality 13 10 a a (mNat a) := by
  have h := exception_quality ha hf
  rw [show (3 : ℕ) ^ (10 * a) = (3 ^ a) ^ 10 from by rw [← pow_mul, Nat.mul_comm]] at h
  rw [RigidQuality, rigidRad_diag, rigidGcd_diag]
  exact h

/-- **Counting the target set is at least Problem 1.**  If the quality-`≥13/10` rigid triples run
over finitely many indices then `𝓔` is finite — the reduction B6(i) announced, now a theorem.
It is a *strict* strengthening: the target set also contains the powerful accidents, which have
nothing to do with `‖(3/2)ᵃ‖`. -/
@[category research solved, AMS 11, ref "Mas85" "Oes88" "Mah57" "Bug12", group "bugeaud_10_13"]
theorem exceptions_finite_of_rigid_finite
    (h : {a : ℕ | ∃ m mu : ℕ, 1 ≤ m ∧ 1 ≤ mu ∧ RigidQuality 13 10 a m mu}.Finite) :
    {a : ℕ | IsFailure 3 2 (3 / 4) a}.Finite := by
  refine Set.Finite.subset (Set.Finite.union (Set.finite_lt_nat 74) h) ?_
  intro a hfa
  by_cases h74 : a < 74
  · exact Or.inl h74
  · exact Or.inr ⟨a, mNat a, by omega, mNat_pos a, exception_rigid_quality (by omega) hfa⟩

/-! ## 6. Why [Ben01] does not apply: the moving parameter is `μ`, not `k`

Fixing the small term leaves an infinite family; the count only becomes finite when the
*multiplier* is fixed too, and the quality condition leaves exponentially many multipliers. -/

/-- **`k = 1` has a solution at every index**: `3ᵃ − 1 = μ2ᵐ` with `2ᵐ` its exact `2`-part.  So
fixing the small term of the rigid shape finitises nothing — the item's stated gap to [Ben01] is
misidentified. -/
@[category research solved, AMS 11, ref "Ben01" "Bug12", group "bugeaud_10_13"]
theorem rigid_k_one {a : ℕ} (ha : 1 ≤ a) : ∃ m mu : ℕ, 1 ≤ m ∧ 1 ≤ mu ∧ rigidK a m mu = 1 := by
  have h3 : 3 ≤ 3 ^ a := by
    calc (3 : ℕ) = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have hmod : (3 : ℕ) ^ a % 2 = 1 := by
    rw [Nat.pow_mod]; norm_num
  refine ⟨1, (3 ^ a - 1) / 2, le_rfl, by omega, ?_⟩
  have hmul : 2 * ((3 ^ a - 1) / 2) = 3 ^ a - 1 := by omega
  have hZ : (2 : ℤ) * (((3 ^ a - 1) / 2 : ℕ) : ℤ) = (3 : ℤ) ^ a - 1 := by
    have h1 : ((2 * ((3 ^ a - 1) / 2) : ℕ) : ℤ) = ((3 ^ a - 1 : ℕ) : ℤ) := by exact_mod_cast hmul
    have h2 : ((3 ^ a - 1 : ℕ) : ℤ) = (3 : ℤ) ^ a - 1 := by
      have : ((3 ^ a : ℕ) : ℤ) = (3 : ℤ) ^ a := by push_cast; ring
      omega
    push_cast at h1
    omega
  rw [rigidK, pow_one]
  linarith [hZ]

/-- The `k = 1` family is infinite. -/
@[category research solved, AMS 11, ref "Ben01" "Bug12", group "bugeaud_10_13"]
theorem rigid_k_one_infinite :
    {a : ℕ | ∃ m mu : ℕ, 1 ≤ m ∧ 1 ≤ mu ∧ rigidK a m mu = 1}.Infinite := by
  refine Set.Infinite.mono (fun a (ha : a ∈ Set.Ici 1) => rigid_k_one ha) ?_
  exact Set.Ici_infinite 1

/-- **The corridor holds one multiplier per `(a, m)`**: `|k| < 2^{m−1}` determines `μ`.  This is
`pair_candidate_unique` of B6(ii) for the free-multiplier family. -/
@[category research solved, AMS 11, ref "Ben01" "Bug12", group "bugeaud_10_13"]
theorem rigid_unique_per_m {a m mu mu' : ℕ}
    (h : 2 * |rigidK a m mu| < 2 ^ m) (h' : 2 * |rigidK a m mu'| < 2 ^ m) :
    mu = mu' := by
  have hax : |2 * rigidK a m mu| < 2 ^ m := by rw [abs_mul]; simpa using h
  have hax' : |2 * rigidK a m mu'| < 2 ^ m := by rw [abs_mul]; simpa using h'
  obtain ⟨h1, h2⟩ := abs_lt.mp hax
  obtain ⟨h1', h2'⟩ := abs_lt.mp hax'
  have hdiff : 2 * rigidK a m mu - 2 * rigidK a m mu' = ((mu' : ℤ) - mu) * (2 * 2 ^ m) := by
    rw [rigidK, rigidK]; ring
  by_contra hne
  have hpos : (0 : ℤ) ≤ 2 * 2 ^ m := by positivity
  have hcase : (1 : ℤ) ≤ (mu' : ℤ) - mu ∨ (mu' : ℤ) - mu ≤ -1 := by omega
  rcases hcase with hc | hc
  · have := mul_le_mul_of_nonneg_right hc hpos
    rw [one_mul] at this
    linarith
  · have := mul_le_mul_of_nonneg_right hc hpos
    linarith

/-- The corridor is short: `μ ≥ 1` and `μ2ᵐ ≤ 2·3ᵃ` force `41m ≤ 65a + 41`.  With
`rigid_unique_per_m`: at most `(65a+41)/41 ≈ 1.585a + 1` rigid triples per index inside the
corridor. -/
@[category research solved, AMS 11, ref "Ben01" "Bug12", group "bugeaud_10_13"]
theorem rigid_m_le {a m mu : ℕ} (hmu : 1 ≤ mu) (hword : mu * 2 ^ m ≤ 2 * 3 ^ a) :
    41 * m ≤ 65 * a + 41 := by
  have h1 : (2 : ℕ) ^ m ≤ 2 * 3 ^ a := le_trans (Nat.le_mul_of_pos_left _ hmu) hword
  have h4 : (2 : ℕ) ^ (41 * m) ≤ 2 ^ (41 + 65 * a) := by
    calc (2 : ℕ) ^ (41 * m) = (2 ^ m) ^ 41 := by rw [← pow_mul, Nat.mul_comm]
      _ ≤ (2 * 3 ^ a) ^ 41 := Nat.pow_le_pow_left h1 41
      _ = 2 ^ 41 * 3 ^ (41 * a) := by rw [Nat.mul_pow, ← pow_mul, Nat.mul_comm 41 a]
      _ ≤ 2 ^ 41 * 2 ^ (65 * a) := Nat.mul_le_mul_left _ (three_pow_le_two_pow a)
      _ = 2 ^ (41 + 65 * a) := by rw [← pow_add]
  have := (Nat.pow_le_pow_iff_right (a := 2) (by norm_num)).mp h4
  omega

/-- **The Bennett ledger.**  At least `X` pairs `(μ, k)` satisfy the size condition `μ|k| ≤ X`
that the quality bound leaves open, and `X = 3^{10a/13} = 2^{1.219a}` at index `a`.  [Ben01]
bounds the solutions *per pair* by `2`; the resulting count is exponential, against a truth of
`≤ (65a+41)/41` (`rigid_m_le`, `rigid_unique_per_m`).  The uniformity is in the wrong variable. -/
@[category research solved, AMS 11, ref "Ben01", group "bugeaud_10_13"]
theorem bennett_pairs_ge (X : ℕ) :
    X ≤ (((Finset.Icc 1 X) ×ˢ (Finset.Icc 1 X)).filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ X)).card := by
  have hcard : (Finset.Icc 1 X).card = X := by rw [Nat.card_Icc]; omega
  calc X = (Finset.Icc 1 X).card := hcard.symm
    _ ≤ _ := by
        refine Finset.card_le_card_of_injOn (fun k => (1, k)) (fun k hk => ?_)
          (fun x _ y _ hxy => ?_)
        · have hk' : 1 ≤ k ∧ k ≤ X := by simpa using hk
          have hmem : ((1, k) : ℕ × ℕ) ∈ ((Finset.Icc 1 X) ×ˢ (Finset.Icc 1 X)).filter
              (fun p : ℕ × ℕ => p.1 * p.2 ≤ X) := by
            simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, one_mul]
            omega
          simpa using hmem
        · simpa using hxy

/-! ## 7. A4's fibre tree is a path

After B8 the fibre over `a` is an interval, so the "tree" whose depth A4's P2.4 proposed to bound
`2`-adically has exactly one child at each level, and its depth *is* `min(v₂(mₐ), D(a))`. -/

/-- **No branching.**  Membership in the fibre over `a` is downward closed in the offset: the
greedy ray of A4's fibre tree is the whole tree.  Bounding its depth is Problem 2 verbatim. -/
@[category research solved, AMS 11, ref "Bug12", group "bugeaud_10_13"]
theorem fibre_downward_closed {a d d' : ℕ} (ha : 3 ≤ a) (hdd : d' ≤ d)
    (h : a + d ∈ lineFibre (linePoint a)) : a + d' ∈ lineFibre (linePoint a) := by
  rw [mem_lineFibre_add_iff ha] at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨le_trans hdd h1, lt_of_le_of_lt ?_ h2⟩
  have hmono : (2 : ℤ) ^ d' ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) hdd
  have hpos : (0 : ℤ) ≤ |resid 3 2 a| * 2 ^ a := by positivity
  calc (2 : ℤ) ^ d' * |resid 3 2 a| * 2 ^ a = 2 ^ d' * (|resid 3 2 a| * 2 ^ a) := by ring
    _ ≤ 2 ^ d * (|resid 3 2 a| * 2 ^ a) := mul_le_mul_of_nonneg_right hmono hpos
    _ = 2 ^ d * |resid 3 2 a| * 2 ^ a := by ring

/-! ## 8. Effectivity, and the numerals -/

/-- **An effective count would settle Problem 1 effectively.**  The block rate the target needs is
`15/41`, below B7's `17/41`, so any effective global run bound strong enough to make B6(iii)'s
count effective already bounds the exceptions — which no method in print comes near. -/
@[category research solved, AMS 11, ref "DD90" "Ben01" "Bug12", group "bugeaud_10_13"]
theorem effective_count_solves_problem_one {a P Q C : ℕ} (ha : 1 ≤ a) (hQ : 1 ≤ Q)
    (hPQ : 41 * P ≤ 15 * Q) (hf : IsFailure 3 2 (3 / 4) a)
    (hrun : ∀ lo hi : ℕ, IsBlock (3 ^ a) lo hi → Q * hi ≤ Q * lo + P * a + C) :
    a ≤ 41 * Q + 41 * C :=
  no_exception_of_run_bound ha (by omega) hf hrun

/-- **The family's record, `a = 10`**: `3¹⁰ + 7³ = 29·2¹¹`, quality `1.5463` — and it is a
*powerful* accident, `|k| = 7³` with radical `7`.  Every quality-`≥13/10` triple found in the
census (`BB13/b6iii_rigidcount.py`, [C], `a ≤ 45`) is of this kind; none comes from an
approximation. -/
@[category test, AMS 11, ref "Mas85" "Bug12", group "bugeaud_10_13"]
theorem rigid_record_ten :
    rigidK 10 11 29 = -(7 ^ 3) ∧ rigidGcd 10 11 29 = 1 ∧ 29 * 2 ^ 11 = 3 ^ 10 + 7 ^ 3 := by
  refine ⟨by norm_num [rigidK], ?_, by norm_num⟩
  norm_num [rigidGcd, rigidK]

/-- The `k = 1` witness at `a = 5`: `3⁵ = 121·2 + 1`. -/
@[category test, AMS 11, ref "Ben01", group "bugeaud_10_13"]
theorem rigid_k_one_five : rigidK 5 1 121 = 1 := by norm_num [rigidK]

/-- **The slope order.**  `19/52 = 0.36538` (backward) `< 15/41 = 0.36585` (forward)
`< 17/41 = 0.41463` (B7's exception block): the dictionary is tight to `5·10⁻⁴`, and both of its
ends lie strictly below the block every exception is obliged to have. -/
@[category test, AMS 11, ref "DD90" "Bug12", group "bugeaud_10_13"]
theorem rigid_slope_order :
    19 * 41 < 15 * 52 ∧ 15 * 41 < 17 * 41 ∧ (2 : ℕ) ^ 19 ≤ 3 ^ 12 := by
  norm_num

/-- **The pricing, at `a = 100`**: the corridor holds at most `159` triples, while the pairs
`(μ, k)` that [Ben01] would have to be applied to number at least `3⁷⁶ > 8·10³⁶`. -/
@[category test, AMS 11, ref "Ben01", group "bugeaud_10_13"]
theorem rigid_pricing_hundred : 65 * 100 + 41 < 3 ^ 76 := by norm_num

end BB13
