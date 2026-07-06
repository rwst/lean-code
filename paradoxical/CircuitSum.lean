/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import paradoxical.Defs
import paradoxical.ClosureIdentity
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# The per-burst circuit sum for `s(V)`

The paper's boxed circuit-sum form of the integer remainder `s(V)` in the closure
identity (`length-bound.html` §1).  An odd start's parity word decomposes into `R`
bursts `aᵢ` (runs of `1`s) and gaps `eᵢ` (runs of `0`s), `cᵢ = aᵢ + eᵢ`.  Then

    s(V) = Σᵢ (3^{aᵢ} − 2^{aᵢ}) · 3^{a_{i+1}+…+a_R} · 2^{c₁+…+c_{i-1}} .

Here a shape is a `List (ℕ × ℕ)` of pairs `(aᵢ, eᵢ)`, and `circSum` is that sum in
the equivalent left-to-right recursive form
`circSum ((a,e)::rest) = 3^{ones rest}·(3^a − 2^a) + 2^{a+e}·circSum rest`
(the `(3^a − 2^a)` factor is the geometric sum `Σ_{t<a} 2^t 3^{a-1-t}` of one burst).

Two ingredients, both proved here from scratch:

* `foldl_pbits` — the integer-remainder recursion `remStep` folded over the parity
  word rebuilds `CC.decomposition_correction` (i.e. `s(V)`);
* `foldl_wordOfShape` — folding `remStep` over a shape's burst/gap word regroups
  into `circSum`, via the burst law `foldl_burst` and gap law `foldl_gap`.

Combined: `decomposition_correction_eq_circSum` (`s(V) = circSum S` when `n`'s word
is the shape word), and `closure_identity_circuit`, the closure identity of
`ClosureIdentity.lean` with `s(V)` in the explicit per-burst form.  This regrouping
is *not* in Rozier–Terracol; it refines `CC.decomposition_correction_eq_sum` (the
single-step sum) by collecting each burst's steps into one `(3^{aᵢ} − 2^{aᵢ})` term.

All results are `sorry`-free (`propext, Classical.choice, Quot.sound`).  The
numerical cross-check (`circSum` vs. `remainder_from_parity` on 130+ shapes) lives
in `bounded_circuit_search.py` in this directory.
-/

namespace Paradoxical

open CC

/-- The per-burst circuit sum `s(V)`, in left-to-right recursive form. -/
def circSum : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (a, e) :: rest => 3 ^ ones rest * (3 ^ a - 2 ^ a) + 2 ^ (a + e) * circSum rest

/-- **Bridge.** Folding `remStep` over the parity word rebuilds the pair
    `(2^j, decomposition_correction j n)`; the second component is `s(V)`. -/
lemma foldl_pbits (j n : ℕ) :
    (pbits j n).foldl remStep (1, 0) = (2 ^ j, decomposition_correction j n) := by
  induction j with
  | zero => simp [pbits, decomposition_correction]
  | succ j ih =>
      have hsplit : pbits (j + 1) n = pbits j n ++ [X (T_iter j n)] := by
        simp [pbits, List.range_succ]
      rw [hsplit, List.foldl_append, ih, List.foldl_cons, List.foldl_nil, Prod.ext_iff]
      refine ⟨?_, ?_⟩
      · simp only [remStep]; rw [pow_succ]; ring
      · simp only [remStep, decomposition_correction]

/-- **Burst law.** A burst of `a` ones multiplies the remainder by `3^a` and adds
    `p2 · (3^a − 2^a)` (the geometric sum `Σ_{t<a} 2^t 3^{a-1-t}`). -/
lemma foldl_burst (a p2 s : ℕ) :
    (List.replicate a 1).foldl remStep (p2, s)
      = (2 ^ a * p2, 3 ^ a * s + p2 * (3 ^ a - 2 ^ a)) := by
  induction a generalizing p2 s with
  | zero => simp
  | succ a ih =>
      rw [List.replicate_succ, List.foldl_cons]
      have hstep : remStep (p2, s) 1 = (2 * p2, 3 * s + p2) := by simp [remStep]
      rw [hstep, ih, Prod.ext_iff]
      have h1 : (2 : ℕ) ^ a ≤ 3 ^ a := Nat.pow_le_pow_left (by norm_num) a
      have h2 : (2 : ℕ) ^ (a + 1) ≤ 3 ^ (a + 1) := Nat.pow_le_pow_left (by norm_num) (a + 1)
      refine ⟨by rw [pow_succ]; ring, ?_⟩
      zify [h1, h2]; ring

/-- **Gap law.** A gap of `e` zeros leaves the remainder unchanged and scales the
    running weight `p2` by `2^e`. -/
lemma foldl_gap (e p2 s : ℕ) :
    (List.replicate e 0).foldl remStep (p2, s) = (2 ^ e * p2, s) := by
  induction e generalizing p2 with
  | zero => simp
  | succ e ih =>
      rw [List.replicate_succ, List.foldl_cons]
      have hstep : remStep (p2, s) 0 = (2 * p2, s) := by simp [remStep]
      rw [hstep, ih, Prod.ext_iff]
      exact ⟨by rw [pow_succ]; ring, rfl⟩

/-- **Regrouping by circuits.** Folding `remStep` over a shape's burst/gap word
    yields `(2^{wlen S}·p2, 3^{ones S}·s + p2·circSum S)`. -/
lemma foldl_wordOfShape (S : List (ℕ × ℕ)) (p2 s : ℕ) :
    (wordOfShape S).foldl remStep (p2, s)
      = (2 ^ wlen S * p2, 3 ^ ones S * s + p2 * circSum S) := by
  induction S generalizing p2 s with
  | nil => simp [wordOfShape, wlen, ones, circSum]
  | cons ae rest ih =>
      obtain ⟨a, e⟩ := ae
      rw [wordOfShape, List.foldl_append, List.foldl_append, foldl_burst, foldl_gap, ih,
        Prod.ext_iff]
      simp only [wlen, ones, circSum, List.map_cons, List.sum_cons]
      refine ⟨by ring, ?_⟩
      set D := (3 : ℕ) ^ a - 2 ^ a
      ring

/-- **Per-burst circuit sum.**  When `n`'s length-`j` parity word is the burst/gap
    word of a shape `S`, the integer remainder `s(V) = decomposition_correction j n`
    equals the paper's circuit sum `circSum S`. -/
theorem decomposition_correction_eq_circSum (S : List (ℕ × ℕ)) (j n : ℕ)
    (hshape : pbits j n = wordOfShape S) :
    decomposition_correction j n = circSum S := by
  have h1 := foldl_pbits j n
  rw [hshape, foldl_wordOfShape S 1 0] at h1
  have h2 := (Prod.ext_iff.mp h1).2
  simpa using h2.symm

/-- **Closure identity, circuit-sum form.**  The closure identity of
    `ClosureIdentity.lean` with `s(V)` written as the explicit per-burst sum:

    `(2^j − 3^q) · n = circSum S − 2^j · d`. -/
theorem closure_identity_circuit (S : List (ℕ × ℕ)) (j n : ℕ)
    (hshape : pbits j n = wordOfShape S) :
    ((2 : ℤ) ^ j - 3 ^ num_odd_steps j n) * (n : ℤ)
      = (circSum S : ℤ) - 2 ^ j * retDiff j n := by
  rw [closure_identity, decomposition_correction_eq_circSum S j n hshape]

end Paradoxical
