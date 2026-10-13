/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.Obstruction

/-!
# Two-letter obstructions as decidable witnesses

`DubC2.Gen.not_checked_of_two_letters` ([Oda26] Theorem 42, for shifts) has real and
modulus-dependent hypotheses.  Here they are restated as one Boolean check `witnessOK` on integer
data — letters `s₀ ≠ c`, a residue `R` (any integer; the theorem uses `R mod M`), and the prime
lists — so that the obstructions found by `DubC2/obstruction_scan.py` become theorems by `decide`.

A witness for the lists `(PM, Pq)` kills every parameter set whose `PM` and `Pq` are *contained* in
them, whatever the cell count `D`, the modulus `M`, and the rest of the certificate data
(`Gen.not_checked_of_witnessOK`).

## References

* [Oda26] Y. Odagiri, *Finite graph certificates for composite terms in rational floor sequences*,
  Zenodo, doi:10.5281/zenodo.22997709 (2026).
-/

namespace DubC2.Gen

/-- A two-letter witness: prime lists, letters, and a residue. -/
structure Witness where
  PM : List ℕ
  Pq : List ℕ
  s₀ : ℤ
  c : ℤ
  R : ℤ

/-- The conditions of Theorem 42, in integers.  With `N = s₀b + (p−q)a` and `Δ = (p−q)b`,
`x* = N/Δ`, and the interval conditions read `0 ≤ N ≤ Δ`, `0 < pN + (c−s₀)Δ < pΔ`. -/
def witnessOK (p q : ℕ) (a : ℤ) (b : ℕ) (w : Witness) : Bool :=
  let N : ℤ := w.s₀ * b + ((p : ℤ) - q) * a
  let Δ : ℤ := ((p : ℤ) - q) * b
  decide (w.c ≠ w.s₀) &&
  w.PM.all (fun l => decide (w.R % (l : ℤ) ≠ 0) &&
    ((decide ((p : ℤ) % l = 0) && decide (w.s₀ % (l : ℤ) ≠ 0) && decide (w.c % (l : ℤ) ≠ 0)) ||
     (decide ((((p : ℤ) - q) * w.R + w.s₀) % l = 0) && decide ((w.c - w.s₀) % (l : ℤ) = 0)))) &&
  w.Pq.all (fun l => decide (w.s₀ % (l : ℤ) ≠ 0) && decide (w.c % (l : ℤ) ≠ 0)) &&
  decide (0 ≤ N) && decide (N ≤ Δ) && decide (0 < p * N + (w.c - w.s₀) * Δ) &&
  decide (p * N + (w.c - w.s₀) * Δ < p * Δ)

/-- **A checked witness rules out every certificate** for every parameter set with the same base
and shift whose prime lists are contained in the witness's. -/
@[category research solved, AMS 11 37, ref "Oda26", group "dubc2_obstruction"]
theorem not_checked_of_witnessOK {P : Params} {C : Cert} (w : Witness)
    (h : witnessOK P.p P.q P.a P.b w = true) (hPM : ∀ l ∈ P.PM, l ∈ w.PM)
    (hPq : ∀ l ∈ P.Pq, l ∈ w.Pq) : ¬ Checked P C := by
  intro hc
  have hF : ParamFacts P := by
    have hh := hc.head
    simp only [checkHead, Bool.and_eq_true] at hh
    exact paramFacts hh.1.1.1.1.1
  simp only [witnessOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true]
    at h
  obtain ⟨⟨⟨⟨⟨⟨hne, hM⟩, hq⟩, hN0⟩, hN1⟩, he0⟩, he1⟩ := h
  have hM0 : (0 : ℤ) < P.M := by exact_mod_cast hF.M0
  set r₀ : ℕ := (w.R % P.M).toNat with hr₀
  have hr₀c : (r₀ : ℤ) = w.R % P.M := Int.toNat_of_nonneg (Int.emod_nonneg _ hM0.ne')
  have hr₀M : r₀ < P.M := by
    have := Int.emod_lt_of_pos w.R hM0
    omega
  -- `r₀ ≡ R (mod l)` for `l ∣ M`
  have hmodl : ∀ l ∈ P.PM, (r₀ : ℤ) % l = w.R % l := fun l hl => by
    rw [hr₀c]
    exact Int.emod_emod_of_dvd _ (by
      have := hF.PM l hl
      exact_mod_cast Nat.dvd_of_mod_eq_zero this)
  have hpqR : (0 : ℝ) < ((P.p : ℝ) - P.q) * P.b := by
    have h1 : (P.q : ℝ) < P.p := by exact_mod_cast hF.pq
    have h2 : (0 : ℝ) < P.b := by exact_mod_cast hF.b0
    nlinarith
  have hp0 : (0 : ℝ) < P.p := by
    have : 0 < P.p := by have := hF.q1; have := hF.pq; omega
    exact_mod_cast this
  set N : ℤ := w.s₀ * P.b + ((P.p : ℤ) - P.q) * P.a with hNdef
  set Δ : ℤ := ((P.p : ℤ) - P.q) * P.b with hΔ
  have hNR : ((w.s₀ : ℝ) * P.b + ((P.p : ℝ) - P.q) * P.a) = (N : ℝ) := by
    simp only [hNdef]; push_cast; ring
  have hΔR : (((P.p : ℝ) - P.q) * P.b) = (Δ : ℝ) := by simp only [hΔ]; push_cast; ring
  have hΔ0 : (0 : ℝ) < Δ := by rw [← hΔR]; exact hpqR
  have hsum : (N : ℝ) / Δ + ((w.c : ℝ) - w.s₀) / P.p =
      ((P.p : ℝ) * N + ((w.c : ℝ) - w.s₀) * Δ) / ((P.p : ℝ) * Δ) := by
    field_simp
  refine not_checked_of_two_letters (s₀ := w.s₀) (c := w.c) hne hr₀M (fun l hl => ?_)
    (fun l hl => ?_) ?_ ?_ ?_ ?_ hc
  · obtain ⟨hR, hor⟩ := hM l (hPM l hl)
    have hml := hmodl l hl
    refine ⟨fun hd => hR (by rw [← hml]; exact Int.emod_eq_zero_of_dvd hd), ?_⟩
    rcases hor with ⟨⟨h1, h2⟩, h3⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨Int.dvd_of_emod_eq_zero h1, fun hd => h2 (Int.emod_eq_zero_of_dvd hd),
        fun hd => h3 (Int.emod_eq_zero_of_dvd hd)⟩
    · refine Or.inr ⟨Int.dvd_of_emod_eq_zero ?_, Int.dvd_of_emod_eq_zero h2⟩
      rw [Int.add_emod, Int.mul_emod, hml, ← Int.mul_emod, ← Int.add_emod]
      exact h1
  · obtain ⟨h1, h2⟩ := hq l (hPq l hl)
    exact ⟨fun hd => h1 (Int.emod_eq_zero_of_dvd hd), fun hd => h2 (Int.emod_eq_zero_of_dvd hd)⟩
  · rw [hNR, hΔR]
    exact div_nonneg (by exact_mod_cast hN0) hΔ0.le
  · rw [hNR, hΔR, div_le_one hΔ0]
    exact_mod_cast hN1
  · rw [hNR, hΔR, hsum]
    apply div_pos _ (by positivity)
    exact_mod_cast he0
  · rw [hNR, hΔR, hsum, div_lt_one (by positivity)]
    exact_mod_cast he1

/-- A whole row of witnesses at once (one `decide`). -/
theorem not_checked_of_row {p q : ℕ} {a : ℤ} {b : ℕ} {ws : List Witness}
    (h : ws.all (witnessOK p q a b) = true) :
    ∀ w ∈ ws, ∀ (P : Params) (C : Cert), P.p = p → P.q = q → P.a = a → P.b = b →
      (∀ l ∈ P.PM, l ∈ w.PM) → (∀ l ∈ P.Pq, l ∈ w.Pq) → ¬ Checked P C := by
  intro w hw P C hp hq ha hb hPM hPq
  subst hp hq ha hb
  exact not_checked_of_witnessOK w (List.all_eq_true.1 h w hw) hPM hPq

end DubC2.Gen
