/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import BertinPisot.SchurAlgorithm
import Corpus.Util.Attributes.Database
import Corpus.Util.Attributes.Basic

/-!
# The generalized Schur algorithm (Bertin §3.3) — Lemma 3.3.1

Bertin's **§3.3** (*Pisot and Salem Numbers*, [Ber92]) opens the *generalized Schur algorithm* with
**Lemma 3.3.1**, which "resembles Lemma 3.1.2 with `|a₀| = 1`". Let
`F = a₀ + a_k z^k + ⋯ ∈ ℂ⟦z⟧` with `|a₀| = 1` and `a_k ≠ 0` (so `ord(F − a₀) = k`). Form the Schur
quotient and its associated polynomials
`C = a₀ z^k / (F − a₀) = ∑ cᵢ zⁱ`,
`Q = c₀ + c₁z + ⋯ + c_{k-1} z^{k-1} − (c̄_{k-1} z^{k+1} + ⋯ + c̄₀ z^{2k})`  (an anti-reciprocal
degree-`2k` polynomial, the `z^k` coefficient absent), and `R` defined by `C = Q + z^k R`.

* `genSchurQ k cps`, `genSchurR k cps` — `Q` and `R` built from the coefficients of the Schur quotient
  `cps = C`. `genSchurNum k cps F = F(Q − z^k) − a₀Q` and
  `genSchurDen k cps F = ā₀FQ − (Q + z^k)` are the numerator and denominator that drive the algorithm.
* `genSchurQ_decomp` — the defining decomposition `C = Q + z^k R`.
* `genSchurNum_eq`, `genSchurDen_eq` — Bertin's "we easily establish that …" identities
  `F(Q − z^k) − a₀Q = z^k(a₀ − F)(1 + R)` and `ā₀FQ − (Q + z^k) = −ā₀ z^k(F − a₀)R`, each a
  `linear_combination` of the Schur relation `C(F − a₀) = a₀z^k` (the second also of `|a₀|² = 1`).

## Lemma 3.3.1

* `genSchur_order_ge` — **i)** (**proved**): `ord(F(Q − z^k) − a₀Q) ≥ 2k` and
  `ord(ā₀FQ − (Q + z^k)) ≥ 2k` — from the two identities above, `F − a₀ = z^k G` makes `z^{2k}` divide
  each side.
* `genSchur_delta_eq` — **ii)** (`cited` axiom): if `ord(ā₀FQ − (Q + z^k)) = 2k + s` (`s < ∞`) with `d`
  its first non-zero coefficient, then for all `n ≥ 2k + s`,
  `δₙ(F) = (−1)^{k+s} |a_k|^{2(k+s)} |d|^{2(n+1−2k−s)} δ_{n−2k−s}(H)`, where
  `H = z^s (F(Q − z^k) − a₀Q) / (ā₀FQ − (Q + z^k))`.
* `genSchur_delta_eq_of_den_zero` — **iii)** (`cited` axiom): if `ā₀FQ − (Q + z^k) ≡ 0`, then for all
  `n ≥ 2k`, `δₙ(F) = (−1)^{n+1−k} |a_k|^{2(n+1−k)}`.

## Remark — the explicit `H` (**proved**)

* `genSchur_H_eq` — Bertin's **Remark**: `H` simplifies to `H = z^s(1 + R)/(ā₀R)`, recorded as the
  cleared identity `ā₀ R H = z^s(1 + R)`.
* `genSchurDen_order_eq` — its companion `ord(ā₀FQ − (Q + z^k)) = 2k + ord R`, i.e. Bertin's
  "`s = ord R`".

Bertin prints the Remark as `H = −z^s(1 + R)/(ā₀R)`; the minus there propagates from the
`ā₀FQ − (Q + z^k) = +ā₀z^k(F − a₀)R` **misprint** in the part-i) denominator identity. The correct
denominator (machine-checked here via `linear_combination`) is `−ā₀z^k(F − a₀)R`, so the minus cancels
and `H = +z^s(1 + R)/(ā₀R)` (the sign convention forced by `genSchurDen`'s definition `ā₀FQ − (Q+z^k)`).

Bertin's `C = a₀z^k/(F − a₀)` is the unique power series with `C(F − a₀) = a₀z^k` (division by the
non-unit `F − a₀ = z^k · unit` is not a primitive `PowerSeries` operation); the Schur quotient is
therefore carried as a variable `cps` constrained by that **defining relation** `hrel`. Likewise the
order-`2k+s` denominator forces `H` to be a power series, recorded in ii) by its relation
`H · (ā₀FQ − (Q + z^k)) = z^s (F(Q − z^k) − a₀Q)`. `δₙ` is `schurDelta` of `BertinPisot.SchurAlgorithm`.

## Definition 3.3.1 — the algorithm

The **generalized Schur algorithm** builds a sequence `(Fⁿ)_{n∈J}` (`J ⊆ ℕ`) by `F⁰ = F` and, writing
`Fⁱ = γ₀ + γ_k z^k + ⋯` (`γ₀ = constantCoeff Fⁱ`, `γ_k` the first non-zero coefficient after `γ₀`):
1. `Fⁱ ≡ γ₀` with `|γ₀| = 1` — **stop**;
2. `Fⁱ ≡ γ₀` with `|γ₀| > 1` — **stop**;
3. `|γ₀| < 1` — `Fⁱ⁺¹ = (Fⁱ − γ₀)/(z(1 − γ̄₀Fⁱ)) = schurTransform Fⁱ` (the classical §3.1 Schur step);
4. `|γ₀| > 1`, `γ_k ≠ 0` — `Fⁱ⁺ᵏ = z^k(1 − γ̄₀Fⁱ)/(Fⁱ − γ₀) = genSchurReciprocalStep k Fⁱ`;
5. `|γ₀| = 1`, `γ_k ≠ 0` — with `Q = genSchurQ k cps` of Lemma 3.3.1 (`cps` the Schur quotient):
   a. `ord(γ̄₀FⁱQ − (Q + z^k)) = 2k + s` (`s < ∞`) —
      `Fˢ⁺²ᵏ⁺ⁱ = z^s(Fⁱ(Q − z^k) − γ₀Q)/(γ̄₀FⁱQ − (Q + z^k)) = genSchurUnimodularStep k s cps Fⁱ`
      (the `H` of Lemma 3.3.1 ii / the Remark, `genSchur_H_eq`);
   b. `γ̄₀FⁱQ − (Q + z^k) ≡ 0` — **stop**.

The index set `J` is non-contiguous: each step advances the index by `1` (case 3), `k` (case 4), or
`s + 2k` (case 5a). `genSchurReciprocalStep` and `genSchurUnimodularStep` are the two new transforms
(case 3 reuses `schurTransform`); `psDiv m num den` realizes the power-series quotient `num/den` when
`z^m ∣ num` and `den = z^m · unit`. The stopping cases (1, 2, 5b) and the index bookkeeping `J` are
recorded here only in prose; the formal content is the per-step transforms.

## Remark 3.3.1 — when the algorithm terminates

The sequence `(Fⁿ)` is **finite** (stops) iff it reaches either (a) a constant of modulus `≥ 1`
(cases 1–2 of the Definition), or (b) a series of the form `ε(Q + z^k)/Q` with `|ε| = 1` and
`Q = c₀ + ⋯ + c_{k-1}z^{k-1} − (c̄_{k-1}z^{k+1} + ⋯ + c̄₀z^{2k})`, `c₀ ≠ 0` (case 5b). Form (b) is the
case-5b stop `γ̄₀FⁱQ − (Q + z^k) ≡ 0`: `genSchurDen_eq_zero_iff` proves it equivalent to
`Fⁱ = γ₀(Q + z^k)/Q` (`ε = γ₀`, `|γ₀| = 1`). Case (a) is the constant stops by definition; the
"finite iff" wrapper over the whole sequence is recorded in prose (the sequence object itself is not
formalized).

## Remark 3.3.2 — the Schur determinants at the stopping cases

At the three stopping configurations of Definition 3.3.1 the determinants `δₙ(Fⁱ)` are:
1. (`Fⁱ ≡ γ₀`, `|γ₀| = 1`) `δₙ(Fⁱ) = 0` for all `n` (`schurDelta_C_eq_zero`);
2. (`Fⁱ ≡ γ₀`, `|γ₀| > 1`) `δₙ(Fⁱ) = (1 − γ₀γ̄₀)^{n+1}` (`schurDelta_C_eq`, which gives both 1 and 2);
5b. (`γ̄₀FⁱQ − (Q + z^k) ≡ 0`) `δₙ(Fⁱ) = (−1)^{n+1−k}|γ_k|^{2(n+1−k)}` for `n ≥ 2k` — this is exactly
   **Lemma 3.3.1 iii)** (`genSchur_delta_eq_of_den_zero`).

## References
* [Ber92] Bertin, Marie José. *Pisot and Salem Numbers.* Springer Science & Business Media, 1992.
* [Sch17] Schur, Issai. *Über Potenzreihen, die im Innern des Einheitskreises beschränkt sind.*
  J. Reine Angew. Math. **147** (1917), 205–232. (The Schur algorithm this section generalizes.)
-/

open PowerSeries

/-- Bertin's polynomial `Q` of **Lemma 3.3.1**, built from the coefficients `cᵢ = coeff i cps` of the
Schur quotient `cps = C = a₀z^k/(F − a₀)`:
`Q = c₀ + c₁z + ⋯ + c_{k-1} z^{k-1} − (c̄_{k-1} z^{k+1} + ⋯ + c̄₀ z^{2k})` —
an anti-reciprocal-type polynomial of degree `2k` whose `z^k` coefficient is absent
(`coeff j Q = cⱼ` for `j < k`, `= −c̄_{2k−j}` for `k < j ≤ 2k`, and `0` otherwise). -/
@[category API, AMS 30 13, ref "Ber92"]
noncomputable def genSchurQ (k : ℕ) (cps : PowerSeries ℂ) : PowerSeries ℂ :=
  mk fun j =>
    if j < k then coeff j cps
    else if k < j ∧ j ≤ 2 * k then -(starRingEnd ℂ) (coeff (2 * k - j) cps)
    else 0

/-- Bertin's remainder `R` of **Lemma 3.3.1**, defined by `C = Q + z^k R`: the series `C − Q`
divided by `z^k` (shifted down by `k`), `coeff i R = coeff (i + k) (C − Q)`. See `genSchurQ_decomp`. -/
@[category API, AMS 30 13, ref "Ber92", formal_uses genSchurQ]
noncomputable def genSchurR (k : ℕ) (cps : PowerSeries ℂ) : PowerSeries ℂ :=
  mk fun i => coeff (i + k) (cps - genSchurQ k cps)

/-- The **numerator** `F(Q − z^k) − a₀Q` of **Lemma 3.3.1** (`a₀ = constantCoeff F`). By
`genSchurNum_eq` it equals `z^k (a₀ − F)(1 + R)`, hence has order `≥ 2k`. -/
@[category API, AMS 30 13, ref "Ber92", formal_uses genSchurQ]
noncomputable def genSchurNum (k : ℕ) (cps F : PowerSeries ℂ) : PowerSeries ℂ :=
  F * (genSchurQ k cps - X ^ k) - PowerSeries.C (constantCoeff F) * genSchurQ k cps

/-- The **denominator** `ā₀FQ − (Q + z^k)` of **Lemma 3.3.1** (`ā₀ = conj (constantCoeff F)`). By
`genSchurDen_eq` it equals `−ā₀ z^k (F − a₀) R`, hence has order `≥ 2k`; its order `2k + s` and first
non-zero coefficient `d` drive part ii), and its vanishing is the hypothesis of part iii). -/
@[category API, AMS 30 13, ref "Ber92", formal_uses genSchurQ]
noncomputable def genSchurDen (k : ℕ) (cps F : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.C (starRingEnd ℂ (constantCoeff F)) * F * genSchurQ k cps - (genSchurQ k cps + X ^ k)

/-- The defining decomposition `C = Q + z^k R` of **Lemma 3.3.1** (`Q = genSchurQ`, `R = genSchurR`),
holding for every `cps`: the low `k` coefficients of `Q` reproduce those of `cps`, so `cps − Q` is
divisible by `z^k`. -/
@[category API, AMS 13, ref "Ber92", formal_uses genSchurQ genSchurR]
theorem genSchurQ_decomp (k : ℕ) (cps : PowerSeries ℂ) :
    cps = genSchurQ k cps + X ^ k * genSchurR k cps := by
  ext j
  rw [map_add, coeff_X_pow_mul']
  by_cases hj : k ≤ j
  · rw [if_pos hj, genSchurR, coeff_mk, Nat.sub_add_cancel hj, map_sub]; ring
  · rw [if_neg hj, add_zero, genSchurQ, coeff_mk, if_pos (not_le.mp hj)]

/-- Bertin's identity for the numerator (proof of **Lemma 3.3.1 i**):
`F(Q − z^k) − a₀Q = z^k(a₀ − F)(1 + R)`, i.e. `genSchurNum k cps F = −(z^k((F − a₀)(1 + R)))`. A
`linear_combination` of the Schur relation `C(F − a₀) = a₀z^k` (with `C = Q + z^k R`). -/
@[category API, AMS 30 13, ref "Ber92", formal_uses genSchurNum genSchurQ genSchurR genSchurQ_decomp]
theorem genSchurNum_eq {F cps : PowerSeries ℂ} {k : ℕ}
    (hrel : cps * (F - PowerSeries.C (constantCoeff F)) = PowerSeries.C (constantCoeff F) * X ^ k) :
    genSchurNum k cps F
      = -(X ^ k * ((F - PowerSeries.C (constantCoeff F)) * (1 + genSchurR k cps))) := by
  unfold genSchurNum
  have hdec := genSchurQ_decomp k cps
  set a₀ := constantCoeff F
  set Q := genSchurQ k cps
  set R := genSchurR k cps
  rw [hdec] at hrel
  linear_combination hrel

/-- Bertin's identity for the denominator (proof of **Lemma 3.3.1 i**):
`ā₀FQ − (Q + z^k) = −ā₀ z^k(F − a₀)R`. A `linear_combination` of the Schur relation
`C(F − a₀) = a₀z^k` and `a₀ā₀ = |a₀|² = 1`. (Bertin prints `+ā₀z^k(F − a₀)R`; the sign here is the
machine-checked one.) -/
@[category API, AMS 30 13, ref "Ber92", formal_uses genSchurDen genSchurQ genSchurR genSchurQ_decomp]
theorem genSchurDen_eq {F cps : PowerSeries ℂ} {k : ℕ}
    (ha₀ : Complex.normSq (constantCoeff F) = 1)
    (hrel : cps * (F - PowerSeries.C (constantCoeff F)) = PowerSeries.C (constantCoeff F) * X ^ k) :
    genSchurDen k cps F
      = -(PowerSeries.C (starRingEnd ℂ (constantCoeff F))
          * (X ^ k * ((F - PowerSeries.C (constantCoeff F)) * genSchurR k cps))) := by
  unfold genSchurDen
  have hdec := genSchurQ_decomp k cps
  set a₀ := constantCoeff F
  set Q := genSchurQ k cps
  set R := genSchurR k cps
  rw [hdec] at hrel
  have hconj : PowerSeries.C a₀ * PowerSeries.C (starRingEnd ℂ a₀) = 1 := by
    rw [← map_mul, Complex.mul_conj, ha₀, Complex.ofReal_one, map_one]
  linear_combination (PowerSeries.C (starRingEnd ℂ a₀)) * hrel + (X ^ k + Q) * hconj

/-- **Lemma 3.3.1 i)** (Bertin). For `F` with `|a₀| = 1` (`a₀ = constantCoeff F`), `z^k ∣ (F − a₀)`,
and the Schur quotient `cps` satisfying `cps (F − a₀) = a₀ z^k`, both Schur data have order at least
`2k`:
`ord(F(Q − z^k) − a₀Q) ≥ 2k`  and  `ord(ā₀FQ − (Q + z^k)) ≥ 2k`.

**Proof.** By `genSchurNum_eq` and `genSchurDen_eq` the two sides are `−z^k((F − a₀)(1 + R))` and
`−ā₀z^k((F − a₀)R)`; writing `F − a₀ = z^k G` (from `z^k ∣ (F − a₀)`), each is `z^{2k} · (·)`, so
`z^{2k}` divides it and the order is `≥ 2k`. -/
@[category research solved, AMS 30 13, ref "Ber92" "Sch17",
  formal_uses genSchurNum genSchurDen genSchurNum_eq genSchurDen_eq genSchurR]
theorem genSchur_order_ge {F cps : PowerSeries ℂ} {k : ℕ}
    (ha₀ : Complex.normSq (constantCoeff F) = 1)
    (hk : (X : PowerSeries ℂ) ^ k ∣ (F - PowerSeries.C (constantCoeff F)))
    (hrel : cps * (F - PowerSeries.C (constantCoeff F))
            = PowerSeries.C (constantCoeff F) * X ^ k) :
    (↑(2 * k) : ℕ∞) ≤ (genSchurNum k cps F).order ∧
      (↑(2 * k) : ℕ∞) ≤ (genSchurDen k cps F).order := by
  obtain ⟨G, hG⟩ := hk
  have key : ∀ e : PowerSeries ℂ,
      (X : PowerSeries ℂ) ^ (2 * k) ∣ e → (↑(2 * k) : ℕ∞) ≤ e.order := by
    rintro e ⟨H, rfl⟩
    rw [order_mul, order_X_pow]
    exact le_self_add
  refine ⟨key _ ?_, key _ ?_⟩
  · rw [genSchurNum_eq hrel, hG]
    exact dvd_neg.mpr ⟨G * (1 + genSchurR k cps), by ring⟩
  · rw [genSchurDen_eq ha₀ hrel, hG]
    exact dvd_neg.mpr ⟨PowerSeries.C (starRingEnd ℂ (constantCoeff F)) * G * genSchurR k cps, by ring⟩

/-- **Lemma 3.3.1 ii)** (Bertin). Under the §3.3 setup (`|a₀| = 1`, `k ≠ 0`, `a_k ≠ 0`,
`z^k ∣ (F − a₀)`, and the Schur quotient `cps` with `cps (F − a₀) = a₀z^k`), suppose
`ord(ā₀FQ − (Q + z^k)) = 2k + s` with `s < ∞`, and let `d = coeff (2k+s) (ā₀FQ − (Q + z^k))` be its
first non-zero coefficient, and `H` the power series with
`H · (ā₀FQ − (Q + z^k)) = z^s (F(Q − z^k) − a₀Q)` (i.e. Bertin's
`H = z^s (F(Q − z^k) − a₀Q)/(ā₀FQ − (Q + z^k))`). Then for all `n ≥ 2k + s`,
`δₙ(F) = (−1)^{k+s} |a_k|^{2(k+s)} |d|^{2(n+1−2k−s)} δ_{n−2k−s}(H)`
(with `|·|² = Complex.normSq`). A `cited` axiom (`ref "Ber92" "Sch17"`). -/
@[category research solved, AMS 30 13 15, ref "Ber92" "Sch17",
  formal_uses schurDelta genSchurDen genSchurNum genSchurQ]
axiom genSchur_delta_eq {F cps : PowerSeries ℂ} {k : ℕ}
    (ha₀ : Complex.normSq (constantCoeff F) = 1) (hk0 : k ≠ 0)
    (hk : (X : PowerSeries ℂ) ^ k ∣ (F - PowerSeries.C (constantCoeff F)))
    (hak : coeff k F ≠ 0)
    (hrel : cps * (F - PowerSeries.C (constantCoeff F)) = PowerSeries.C (constantCoeff F) * X ^ k)
    {s : ℕ} (hs : (genSchurDen k cps F).order = ↑(2 * k + s))
    {H : PowerSeries ℂ} (hH : H * genSchurDen k cps F = X ^ s * genSchurNum k cps F)
    {n : ℕ} (hn : 2 * k + s ≤ n) :
    schurDelta F n = (-1 : ℂ) ^ (k + s) * (Complex.normSq (coeff k F) : ℂ) ^ (k + s)
      * (Complex.normSq (coeff (2 * k + s) (genSchurDen k cps F)) : ℂ) ^ (n + 1 - 2 * k - s)
      * schurDelta H (n - 2 * k - s)

/-- **Lemma 3.3.1 iii)** (Bertin). Under the §3.3 setup (`|a₀| = 1`, `k ≠ 0`, `a_k ≠ 0`,
`z^k ∣ (F − a₀)`, and the Schur quotient `cps` with `cps (F − a₀) = a₀z^k`), if the denominator
vanishes, `ā₀FQ − (Q + z^k) ≡ 0`, then for all `n ≥ 2k`,
`δₙ(F) = (−1)^{n+1−k} |a_k|^{2(n+1−k)}`  (with `|·|² = Complex.normSq`).
A `cited` axiom (`ref "Ber92" "Sch17"`). -/
@[category research solved, AMS 30 13 15, ref "Ber92" "Sch17",
  formal_uses schurDelta genSchurDen genSchurQ]
axiom genSchur_delta_eq_of_den_zero {F cps : PowerSeries ℂ} {k : ℕ}
    (ha₀ : Complex.normSq (constantCoeff F) = 1) (hk0 : k ≠ 0)
    (hk : (X : PowerSeries ℂ) ^ k ∣ (F - PowerSeries.C (constantCoeff F)))
    (hak : coeff k F ≠ 0)
    (hrel : cps * (F - PowerSeries.C (constantCoeff F)) = PowerSeries.C (constantCoeff F) * X ^ k)
    (hden : genSchurDen k cps F = 0)
    {n : ℕ} (hn : 2 * k ≤ n) :
    schurDelta F n = (-1 : ℂ) ^ (n + 1 - k) * (Complex.normSq (coeff k F) : ℂ) ^ (n + 1 - k)

/-- **Remark** (Bertin), the explicit form of `H` from **Lemma 3.3.1 ii)**: in the factored form
`H = z^s(1 + R)/(ā₀R)`, recorded as the cleared identity `ā₀ R H = z^s(1 + R)`. **Proved** from
`genSchurNum_eq`, `genSchurDen_eq`, and cancellation of the non-zero `z^k(F − a₀)`.

(Bertin prints `H = −z^s(1 + R)/(ā₀R)`; the minus propagates from the `+ā₀z^k(F − a₀)R` misprint in
the part-i) denominator identity. With the correct `genSchurDen = −ā₀z^k(F − a₀)R`, the sign cancels
and `H = +z^s(1 + R)/(ā₀R)`.) -/
@[category research solved, AMS 30 13, ref "Ber92",
  formal_uses genSchurR genSchurDen genSchurNum genSchurDen_eq genSchurNum_eq]
theorem genSchur_H_eq {F cps : PowerSeries ℂ} {k : ℕ}
    (ha₀ : Complex.normSq (constantCoeff F) = 1) (hk0 : k ≠ 0) (hak : coeff k F ≠ 0)
    (hrel : cps * (F - PowerSeries.C (constantCoeff F)) = PowerSeries.C (constantCoeff F) * X ^ k)
    {s : ℕ} {H : PowerSeries ℂ}
    (hH : H * genSchurDen k cps F = X ^ s * genSchurNum k cps F) :
    PowerSeries.C (starRingEnd ℂ (constantCoeff F)) * genSchurR k cps * H
      = X ^ s * (1 + genSchurR k cps) := by
  rw [genSchurDen_eq ha₀ hrel, genSchurNum_eq hrel] at hH
  set a₀ := constantCoeff F with ha₀def
  set R := genSchurR k cps
  have hFa0 : F - PowerSeries.C a₀ ≠ 0 := by
    intro h
    apply hak
    have hc : coeff k (F - PowerSeries.C a₀) = 0 := by rw [h]; exact map_zero _
    rwa [map_sub, PowerSeries.coeff_C, if_neg hk0, sub_zero] at hc
  have hne : (X : PowerSeries ℂ) ^ k * (F - PowerSeries.C a₀) ≠ 0 :=
    mul_ne_zero (pow_ne_zero k PowerSeries.X_ne_zero) hFa0
  have key : (X ^ k * (F - PowerSeries.C a₀)) * (PowerSeries.C (starRingEnd ℂ a₀) * R * H)
           = (X ^ k * (F - PowerSeries.C a₀)) * (X ^ s * (1 + R)) := by
    linear_combination -hH
  exact mul_left_cancel₀ hne key

/-- **Remark** (Bertin), companion to `genSchur_H_eq`: the denominator order is `2k + ord R`, so the
threshold `s` of **Lemma 3.3.1 ii)** is `s = ord R`. **Proved** from `genSchurDen_eq`, using
`ord(F − a₀) = k` and `ord(ā₀) = 0`. -/
@[category research solved, AMS 30 13, ref "Ber92", formal_uses genSchurDen genSchurR genSchurDen_eq]
theorem genSchurDen_order_eq {F cps : PowerSeries ℂ} {k : ℕ}
    (ha₀ : Complex.normSq (constantCoeff F) = 1) (hk0 : k ≠ 0) (hak : coeff k F ≠ 0)
    (hk : (X : PowerSeries ℂ) ^ k ∣ (F - PowerSeries.C (constantCoeff F)))
    (hrel : cps * (F - PowerSeries.C (constantCoeff F)) = PowerSeries.C (constantCoeff F) * X ^ k) :
    (genSchurDen k cps F).order = (↑(2 * k) : ℕ∞) + (genSchurR k cps).order := by
  rw [genSchurDen_eq ha₀ hrel, order_neg]
  have ha0ne : constantCoeff F ≠ 0 := by
    intro h; rw [h, map_zero] at ha₀; norm_num at ha₀
  have hcord : (PowerSeries.C (starRingEnd ℂ (constantCoeff F)) : PowerSeries ℂ).order = 0 :=
    le_zero_iff.mp (order_le 0 (by rw [coeff_C]; simpa using ha0ne))
  have hge : (↑k : ℕ∞) ≤ (F - PowerSeries.C (constantCoeff F)).order := by
    obtain ⟨G, hG⟩ := hk; rw [hG, order_mul, order_X_pow]; exact le_self_add
  have hFord : (F - PowerSeries.C (constantCoeff F)).order = ↑k :=
    le_antisymm (order_le k (by rw [map_sub, coeff_C, if_neg hk0, sub_zero]; exact hak)) hge
  simp only [order_mul, order_X_pow, hcord, hFord]
  rw [zero_add, ← add_assoc, ← Nat.cast_add, ← two_mul]

/-- Power-series quotient `num / den`, valid when `den = z^m · unit` and `z^m ∣ num`: divide both by
`z^m` (drop the `m` lowest coefficients) and multiply by the inverse of the resulting unit. Realizes
the divisions of Bertin's generalized Schur algorithm (Definition 3.3.1). -/
@[category API, AMS 13]
noncomputable def psDiv (m : ℕ) (num den : PowerSeries ℂ) : PowerSeries ℂ :=
  (mk fun i => coeff (i + m) num) * (mk fun i => coeff (i + m) den)⁻¹

/-- **Definition 3.3.1, case 4** (Bertin): the `|γ₀| > 1` step of the generalized Schur algorithm.
For `Fⁱ = γ₀ + γ_k z^k + ⋯` with `|γ₀| > 1` and `γ_k ≠ 0` (`γ₀ = constantCoeff Fⁱ`), the next term
(at index `i + k`) is `Fⁱ⁺ᵏ = z^k(1 − γ̄₀Fⁱ)/(Fⁱ − γ₀)`. -/
@[category API, AMS 30 13, ref "Ber92" "Sch17", formal_uses psDiv]
noncomputable def genSchurReciprocalStep (k : ℕ) (F : PowerSeries ℂ) : PowerSeries ℂ :=
  psDiv k (X ^ k * (1 - PowerSeries.C (starRingEnd ℂ (constantCoeff F)) * F))
    (F - PowerSeries.C (constantCoeff F))

/-- **Definition 3.3.1, case 5a** (Bertin): the `|γ₀| = 1` step of the generalized Schur algorithm.
For `Fⁱ = γ₀ + γ_k z^k + ⋯` with `|γ₀| = 1`, `γ_k ≠ 0`, and `Q = genSchurQ k cps` (`cps` the Schur
quotient `γ₀z^k/(Fⁱ − γ₀)`), when `ord(γ̄₀FⁱQ − (Q + z^k)) = 2k + s` the next term (at index
`s + 2k + i`) is `Fˢ⁺²ᵏ⁺ⁱ = z^s(Fⁱ(Q − z^k) − γ₀Q)/(γ̄₀FⁱQ − (Q + z^k))` — the `H` of Lemma 3.3.1 ii)
(`genSchur_H_eq`: `H = z^s(1 + R)/(ā₀R)`). -/
@[category API, AMS 30 13, ref "Ber92" "Sch17", formal_uses psDiv genSchurNum genSchurDen]
noncomputable def genSchurUnimodularStep (k s : ℕ) (cps F : PowerSeries ℂ) : PowerSeries ℂ :=
  psDiv (2 * k + s) (X ^ s * genSchurNum k cps F) (genSchurDen k cps F)

/-- **Remark 3.3.1** (Bertin), case (b): the generalized Schur algorithm stops at `Fⁱ` via case 5b —
`γ̄₀FⁱQ − (Q + z^k) ≡ 0` (`genSchurDen k cps F = 0`) — **iff** `Fⁱ` has the form `ε(Q + z^k)/Q` with
`|ε| = 1`, explicitly `Fⁱ = γ₀(Q + z^k)Q⁻¹` (`ε = γ₀ = constantCoeff Fⁱ`, `Q = genSchurQ k cps`
invertible since `c₀ = coeff 0 cps ≠ 0`). **Proved** from `|γ₀|² = 1` and `Q · Q⁻¹ = 1`. (The other
finite case — a constant of modulus `≥ 1` — is cases 1–2 of Definition 3.3.1.) -/
@[category research solved, AMS 30 13, ref "Ber92" "Sch17", formal_uses genSchurDen genSchurQ]
theorem genSchurDen_eq_zero_iff {F cps : PowerSeries ℂ} {k : ℕ}
    (ha₀ : Complex.normSq (constantCoeff F) = 1) (hk0 : k ≠ 0) (hc0 : coeff 0 cps ≠ 0) :
    genSchurDen k cps F = 0 ↔
      F = PowerSeries.C (constantCoeff F) * (genSchurQ k cps + X ^ k) * (genSchurQ k cps)⁻¹ := by
  rw [genSchurDen, sub_eq_zero]
  set γ₀ := constantCoeff F with hγ₀def
  set Q := genSchurQ k cps with hQdef
  have hQ0 : constantCoeff Q ≠ 0 := by
    rw [hQdef, ← coeff_zero_eq_constantCoeff, genSchurQ, coeff_mk, if_pos (Nat.pos_of_ne_zero hk0)]
    exact hc0
  have hQinv : Q * Q⁻¹ = 1 := PowerSeries.mul_inv_cancel Q hQ0
  have hγ : PowerSeries.C γ₀ * PowerSeries.C (starRingEnd ℂ γ₀) = 1 := by
    rw [← map_mul, Complex.mul_conj, ha₀, Complex.ofReal_one, map_one]
  constructor
  · intro h
    rw [← h, show PowerSeries.C γ₀ * (PowerSeries.C (starRingEnd ℂ γ₀) * F * Q) * Q⁻¹
        = (PowerSeries.C γ₀ * PowerSeries.C (starRingEnd ℂ γ₀)) * F * (Q * Q⁻¹) from by ring,
      hγ, hQinv, one_mul, mul_one]
  · intro h
    rw [h, show PowerSeries.C (starRingEnd ℂ γ₀) * (PowerSeries.C γ₀ * (Q + X ^ k) * Q⁻¹) * Q
        = (PowerSeries.C γ₀ * PowerSeries.C (starRingEnd ℂ γ₀)) * (Q + X ^ k) * (Q * Q⁻¹) from by ring,
      hγ, hQinv, one_mul, mul_one]

/-- **Remark 3.3.2, cases 1–2** (Bertin): the Schur determinants of a **constant** series `Fⁱ ≡ γ₀`.
For every `n`, `δₙ(γ₀) = (1 − γ₀γ̄₀)^{n+1} = (1 − |γ₀|²)^{n+1}`. (Case 2, `|γ₀| > 1`, is this formula;
case 1, `|γ₀| = 1`, gives `δₙ = 0` — see `schurDelta_C_eq_zero`.) **Proved** from
`schurToeplitz (C γ₀) n = γ₀ • I` (a scalar matrix), whence `δₙ = det((1 − |γ₀|²) • I) = (1 − |γ₀|²)^{n+1}`. -/
@[category research solved, AMS 30 15 13, ref "Ber92" "Sch17",
  formal_uses schurDelta schurToeplitz schurToeplitzStar schurDelta_eq_det]
theorem schurDelta_C_eq (γ₀ : ℂ) (n : ℕ) :
    schurDelta (PowerSeries.C γ₀) n = (1 - (Complex.normSq γ₀ : ℂ)) ^ (n + 1) := by
  rw [(schurDelta_eq_det (PowerSeries.C γ₀) n).1]
  have hT : schurToeplitz (PowerSeries.C γ₀) n
      = γ₀ • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
    ext i j
    rw [schurToeplitz, Matrix.smul_apply, Matrix.one_apply, PowerSeries.coeff_C, smul_eq_mul]
    rcases eq_or_ne i j with h | h
    · subst h; simp
    · rw [if_neg h, mul_zero]
      split_ifs with ha hb
      · exact absurd (Fin.ext (by omega : (i : ℕ) = j)) h
      · rfl
      · rfl
  have hTs : schurToeplitzStar (PowerSeries.C γ₀) n
      = (starRingEnd ℂ γ₀) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
    ext i j
    rw [schurToeplitzStar, Matrix.smul_apply, Matrix.one_apply, PowerSeries.coeff_C, smul_eq_mul]
    rcases eq_or_ne i j with h | h
    · subst h; simp
    · rw [if_neg h, mul_zero]
      split_ifs with ha hb
      · exact absurd (Fin.ext (by omega : (i : ℕ) = j)) h
      · simp
      · rfl
  rw [hT, hTs, smul_mul_assoc, mul_smul_comm, smul_smul, mul_one,
      show (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) - (γ₀ * starRingEnd ℂ γ₀) • 1
        = (1 - γ₀ * starRingEnd ℂ γ₀) • 1 from by rw [sub_smul, one_smul],
      Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, Complex.mul_conj]

/-- **Remark 3.3.2, case 1** (Bertin): if the algorithm stops at a constant `Fⁱ ≡ γ₀` of modulus
`|γ₀| = 1`, then `δₙ(Fⁱ) = 0` for every `n`. A corollary of `schurDelta_C_eq` (`(1 − 1)^{n+1} = 0`). -/
@[category research solved, AMS 30 15, ref "Ber92" "Sch17", formal_uses schurDelta schurDelta_C_eq]
theorem schurDelta_C_eq_zero {γ₀ : ℂ} (h : Complex.normSq γ₀ = 1) (n : ℕ) :
    schurDelta (PowerSeries.C γ₀) n = 0 := by
  rw [schurDelta_C_eq, h]; simp
