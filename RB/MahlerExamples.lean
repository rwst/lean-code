/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import RB.Regularity
import Mathlib.Data.Nat.Digits.Lemmas
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# Worked Mahler systems: Thue–Morse, Cantor, a collapsing example (plan-B1E2b WP9)

The regularity instrument of `RB/Regularity.lean` applied to actual automatic sequences, and the
two negative results that bound it: a kernel whose `0`-decimation collapses, and the proof that
passing from `k` to `k^t` can never repair a collapse.

## Kernel models

`RB.mahlerMatrix` is stated for an abstract decimation `σ : ι → Fin k → ι`, so a worked example
must say what ties `σ` to a sequence.  That is `RB.IsKernelModel k a φ σ`: an injective enumeration
`φ : ι → (ℕ → ℕ)` of the `k`-kernel of `a` intertwining `σ` with decimation,

  `φ (σ i r) n = φ i (k·n + r)`.

It is exactly the data of a DFAO for `a` written without automata, it makes the kernel finite
(`IsKernelModel.isAutomatic`), and it lets every row below be a concrete matrix over `ℤ[z]` rather
than a subtype of `Set (ℕ → ℕ)`.

## The rows

| sequence | `k` | kernel | `σ(·,0)` | `det M` | verdict at `2/3` |
|---|---|---|---|---|---|
| Thue–Morse `t` | 2 | `{t, 1-t}` | `id` | `1 - z²` | regular |
| Cantor `c` | 3 | `{c, 0}` | `id` | `(1+z²)(1+z+z²)` | regular |
| parity `n % 2` | 2 | `{n%2, 0, 1}` | **collapses** | `0` | *every* point singular |

The paper's fuller table (paperfolding, Rudin–Shapiro, Baum–Sweet) stays prose: the plan asks for
two or three formalized rows, and these three carry all three verdicts.

**Thue–Morse is not in Mathlib** (checked 2026-07-28) and not in the corpus; `ForMathlib/Data/Nat/
BinaryDigits.lean` has only `testBit` bridges.  It is defined here as the parity of the binary
digit sum, which makes the two recurrences `t(2n) = t(n)`, `t(2n+1) = 1 - t(n)` immediate from
`Nat.digits_def'` and gives `t ≤ 1` for free.  The Cantor sequence is `1` iff the base-`3`
expansion avoids the digit `1`.

## The collapsing example, and why it is degenerate

`n ↦ n % 2` is `2`-automatic with kernel `{n%2, 0, 1}`, and its `0`-decimation sends both `n%2` and
`0` to `0` — the permutation hypothesis of `regular_two_thirds` genuinely fails on a real sequence.
More is true: `n % 2` is not in the image of *any* decimation, so `det M` has a zero column and
**vanishes identically** (`det_mahlerMatrix_paritySigma`).  That is the same degeneracy the
exhaustive search of `RB/Regularity.lean` found in all 39130 of its vanishing systems, and it is
why WP8's test is stated against the lowest *nonzero* coefficient: for a collapsing system with
`det M ≠ 0` see `RB.nonPermSigma` there, which WP8 decides and WP7 cannot.

## No free lunch

The obvious repair — read the same sequence in base `k^t` — cannot help: decimation at residue `0`
in base `k^t` is the `t`-fold composite of decimation at residue `0` in base `k`
(`decZero_iterate`), and on a finite set a composite power is bijective iff the map is
(`bijective_iterate_iff`).  So `sigma_pow_zero_perm_iff`: the `k^t` system has a permutation
`0`-decimation iff the `k` system already did.

## The decision procedure

`Polynomial` is noncomputable in Mathlib — `mahlerMatrix` is a `noncomputable def` and
`#eval (mahlerMatrix 2 tmSigma).det.coeff 0` is rejected — so there is no `Bool`-valued
`decideRegular`.  What is decidable is the arithmetic, and that is enough.
`regular_of_certificate` takes the certificate `det M = z^e·g` — produced once by
`Matrix.det_fin_two`/`det_fin_three` and `simp` — and reduces regularity at a rational `α` to the
integer divisibility `α.num ∤ g(0)`.  That residue really is decidable (`¬ ((2:ℤ) ∣ 1)` is
`by decide`), but the step before it is not: kernel reduction cannot evaluate `(2/3 : ℚ).num`, so
the certified rows below discharge the whole side condition with `norm_num`.  No `native_decide`
anywhere, and none of these needs it.

## Contents

* **`RB.IsKernelModel`**, `RB.IsKernelModel.finite_kernel`, `RB.IsKernelModel.isAutomatic`.
* **`RB.thueMorse`**, its recurrences, `RB.thueMorse_pow_mul_add`, **`RB.thueMorse_kernel_eq`**,
  `RB.thueMorse_isKernelModel`, `RB.thueMorse_isAutomatic`,
  **`RB.thueMorse_sigma_zero_isPermutation`**, `RB.det_mahlerMatrix_tmSigma`,
  **`RB.thueMorse_regular_of_not_isIntegral_inv`**, `RB.thueMorse_regular_two_thirds`.
* **`RB.cantorSeq`** and the same chain, ending in `RB.cantor_regular_two_thirds`.
* **`RB.paritySeq`**, `RB.paritySeq_kernel_eq`, `RB.paritySigma_zero_not_injective`,
  `RB.det_mahlerMatrix_paritySigma`, **`RB.collapsing_example`**.
* `RB.decZero`, `RB.decZero_iterate`, `RB.bijective_iterate_iff`,
  **`RB.sigma_pow_zero_perm_iff`**.
* **`RB.regular_of_certificate`** and the two certified rows.

## References

* [AF17] Adamczewski, Faverjon. *Méthode de Mahler …* Proc. LMS **115** (2017), 55–90.
* [AS03] Allouche, Shallit. *Automatic Sequences.* CUP 2003.  (Thue–Morse §1.6, the Cantor
  sequence §5.1, the kernel characterization Thm 6.6.2.)
* [B1E2b] `plans/plan-B1E2b.html` (2026-07-28): WP9 = review items F4 (no examples) and B8
  (decidability module); WP10's negative lemma is `sigma_pow_zero_perm_iff`.
-/

namespace RB

open AS Polynomial

/-! ## Kernel models: what ties a matrix to a sequence -/

/-- **A kernel model** ([B1E2b] WP9): an injective enumeration `φ` of the `k`-kernel of `a` by a
type `ι`, intertwining an abstract decimation `σ : ι → Fin k → ι` with the actual decimation
`s ↦ (n ↦ s (k·n + r))`.

This is a DFAO for `a` with the automaton written as a function, and it is what makes
"`mahlerMatrix k σ` is *the* Mahler matrix of `a`" a theorem rather than a convention. -/
@[category API, AMS 11 68, ref "AS03" "AF17" "B1E2b", group "rb_mahler_examples"]
def IsKernelModel (k : ℕ) (a : ℕ → ℕ) {ι : Type*} (φ : ι → ℕ → ℕ) (σ : ι → Fin k → ι) : Prop :=
  Function.Injective φ ∧ Set.range φ = kKernel k a ∧ ∀ i r n, φ (σ i r) n = φ i (k * n + r)

/-- A kernel model on a finite index type exhibits the kernel as a finite set. -/
@[category research solved, AMS 11 68, ref "AS03" "B1E2b", group "rb_mahler_examples"]
lemma IsKernelModel.finite_kernel {k : ℕ} {a : ℕ → ℕ} {ι : Type*} [Finite ι] {φ : ι → ℕ → ℕ}
    {σ : ι → Fin k → ι} (h : IsKernelModel k a φ σ) : (kKernel k a).Finite :=
  h.2.1 ▸ Set.finite_range φ

/-- **A kernel model certifies automaticity** (Eilenberg's characterization, [AS03] Thm 6.6.2): a
finite model in base `k ≥ 2` makes `a` automatic. -/
@[category research solved, AMS 11 68, ref "AS03" "B1E2b", group "rb_mahler_examples"]
theorem IsKernelModel.isAutomatic {k : ℕ} {a : ℕ → ℕ} {ι : Type*} [Finite ι] {φ : ι → ℕ → ℕ}
    {σ : ι → Fin k → ι} (h : IsKernelModel k a φ σ) (hk : 2 ≤ k) : IsAutomatic a :=
  ⟨k, hk, h.finite_kernel⟩

/-! ## Row 1: Thue–Morse -/

/-- **The Thue–Morse sequence**: the parity of the binary digit sum.  Mathlib has no Thue–Morse
sequence (checked 2026-07-28), so it is defined here. -/
@[category API, AMS 11 68, ref "AS03", group "rb_mahler_examples"]
def thueMorse (n : ℕ) : ℕ := (Nat.digits 2 n).sum % 2

@[category API, AMS 11 68, ref "AS03", group "rb_mahler_examples"]
lemma thueMorse_le_one (n : ℕ) : thueMorse n ≤ 1 := by unfold thueMorse; omega

@[category API, AMS 11 68, ref "AS03", group "rb_mahler_examples"]
lemma thueMorse_zero : thueMorse 0 = 0 := by simp [thueMorse]

/-- `t(2n) = t(n)`: a trailing binary `0` contributes nothing to the digit sum. -/
@[category research solved, AMS 11 68, ref "AS03", group "rb_mahler_examples"]
lemma thueMorse_two_mul (n : ℕ) : thueMorse (2 * n) = thueMorse n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · unfold thueMorse
    rw [Nat.digits_def' (by norm_num : 1 < 2) (by omega : 0 < 2 * n)]
    simp [Nat.mul_div_cancel_left n (show 0 < 2 by norm_num)]

/-- `t(2n+1) = 1 - t(n)`: a trailing binary `1` flips the parity. -/
@[category research solved, AMS 11 68, ref "AS03", group "rb_mahler_examples"]
lemma thueMorse_two_mul_add_one (n : ℕ) : thueMorse (2 * n + 1) = 1 - thueMorse n := by
  unfold thueMorse
  rw [Nat.digits_def' (by norm_num : 1 < 2) (by omega : 0 < 2 * n + 1)]
  have h1 : (2 * n + 1) % 2 = 1 := by omega
  have h2 : (2 * n + 1) / 2 = n := by omega
  rw [h1, h2, List.sum_cons]
  omega

/-- **Digit-block additivity** ([B1E2b] WP9): for `j < 2^i` the binary expansion of `2^i·n + j` is
the expansion of `n` followed by the `i`-digit block of `j`, so the parities add:
`t(2^i·n + j) = (t n + t j) % 2`.

Proved from the two recurrences alone — no digit-list surgery. -/
@[category research solved, AMS 11 68, ref "AS03" "B1E2b", group "rb_mahler_examples"]
lemma thueMorse_pow_mul_add (i : ℕ) : ∀ j n, j < 2 ^ i →
    thueMorse (2 ^ i * n + j) = (thueMorse n + thueMorse j) % 2 := by
  induction i with
  | zero =>
    intro j n hj
    interval_cases j
    have := thueMorse_le_one n
    simp only [pow_zero, one_mul, add_zero, thueMorse_zero]
    omega
  | succ i ih =>
    intro j n hj
    rcases Nat.even_or_odd j with ⟨j', rfl⟩ | ⟨j', rfl⟩
    · have hj' : j' < 2 ^ i := by rw [pow_succ] at hj; omega
      rw [show 2 ^ (i + 1) * n + (j' + j') = 2 * (2 ^ i * n + j') by ring, thueMorse_two_mul,
        ih j' n hj', show j' + j' = 2 * j' by ring, thueMorse_two_mul]
    · have hj' : j' < 2 ^ i := by rw [pow_succ] at hj; omega
      rw [show 2 ^ (i + 1) * n + (2 * j' + 1) = 2 * (2 ^ i * n + j') + 1 by ring,
        thueMorse_two_mul_add_one, ih j' n hj', thueMorse_two_mul_add_one]
      have h1 := thueMorse_le_one n
      have h2 := thueMorse_le_one j'
      omega

@[category API, AMS 11 68, ref "AS03", group "rb_mahler_examples"]
lemma thueMorse_ne_compl : thueMorse ≠ fun n => 1 - thueMorse n := by
  intro hcon
  have h := congrFun hcon 0
  rw [thueMorse_zero] at h
  simp at h

/-- **The `2`-kernel of Thue–Morse is `{t, 1 - t}`** ([AS03] §6.8): every decimation is `t` or its
complement, according to the parity of the digit block that was decimated by. -/
@[category research solved, AMS 11 68, ref "AS03" "B1E2b", group "rb_mahler_examples"]
theorem thueMorse_kernel_eq :
    kKernel 2 thueMorse = {thueMorse, fun n => 1 - thueMorse n} := by
  ext s
  constructor
  · rintro ⟨i, r, hr, rfl⟩
    have hr1 := thueMorse_le_one r
    rcases (by omega : thueMorse r = 0 ∨ thueMorse r = 1) with h | h
    · left
      funext n
      rw [thueMorse_pow_mul_add i r n hr, h]
      have := thueMorse_le_one n
      omega
    · right
      funext n
      rw [thueMorse_pow_mul_add i r n hr, h]
      have := thueMorse_le_one n
      omega
  · rintro (rfl | rfl)
    · exact ⟨0, 0, by norm_num, by funext n; norm_num⟩
    · exact ⟨1, 1, by norm_num, by funext n; rw [pow_one]; exact (thueMorse_two_mul_add_one n).symm⟩

/-- The enumeration of the Thue–Morse kernel: `0 ↦ t`, `1 ↦ 1 - t`. -/
@[category API, AMS 11 68, ref "B1E2b", group "rb_mahler_examples"]
def tmPhi : Fin 2 → ℕ → ℕ := ![thueMorse, fun n => 1 - thueMorse n]

/-- The Thue–Morse decimation: `σ(t,0) = t`, `σ(t,1) = 1-t`, `σ(1-t,0) = 1-t`, `σ(1-t,1) = t`. -/
@[category API, AMS 11 68, ref "AF17" "B1E2b", group "rb_mahler_examples"]
def tmSigma : Fin 2 → Fin 2 → Fin 2 := ![![0, 1], ![1, 0]]

/-- **`tmSigma` is the Mahler system of Thue–Morse** ([B1E2b] WP9). -/
@[category research solved, AMS 11 68, ref "AS03" "AF17" "B1E2b", group "rb_mahler_examples"]
theorem thueMorse_isKernelModel : IsKernelModel 2 thueMorse tmPhi tmSigma := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp only [tmPhi] at h ⊢
    · exact absurd h thueMorse_ne_compl
    · exact absurd h.symm thueMorse_ne_compl
  · ext s
    rw [thueMorse_kernel_eq]
    simp [tmPhi, Set.range, Fin.exists_fin_two, eq_comm]
  · intro i r n
    have h := thueMorse_le_one n
    fin_cases i <;> fin_cases r
    all_goals simp only [tmPhi, tmSigma, Fin.isValue]
    all_goals simp [thueMorse_two_mul, thueMorse_two_mul_add_one]
    all_goals omega

/-- Thue–Morse is `2`-automatic. -/
@[category research solved, AMS 11 68, ref "AS03", group "rb_mahler_examples"]
theorem thueMorse_isAutomatic : IsAutomatic thueMorse :=
  thueMorse_isKernelModel.isAutomatic (by norm_num)

/-- **The permutation hypothesis holds for Thue–Morse** ([B1E2b] WP9, review item F4): `σ(·,0)` is
the identity, so Theorem C — `RB.regular_of_not_isIntegral_inv` — applies to it. -/
@[category research solved, AMS 11 68, ref "AF17" "B1E2b", group "rb_mahler_examples"]
theorem thueMorse_sigma_zero_isPermutation (i : Fin 2) :
    (Equiv.refl (Fin 2)) i = tmSigma i ⟨0, by norm_num⟩ := by
  revert i; decide

/-- `M(z) = ![![1, z], ![z, 1]]`, so `det M = 1 - z²`. -/
@[category research solved, AMS 11 68, ref "AF17" "B1E2b", group "rb_mahler_examples"]
theorem det_mahlerMatrix_tmSigma : (mahlerMatrix 2 tmSigma).det = 1 - X ^ 2 := by
  rw [Matrix.det_fin_two]
  simp [mahlerMatrix, tmSigma, Fin.sum_univ_two]
  ring

/-- **Worked instance of Theorem C** ([B1E2b] WP9): in the Thue–Morse system every point whose
inverse is not an algebraic integer is regular. -/
@[category research solved, AMS 11 68 12, ref "AF17" "B1E2b", group "rb_mahler_examples"]
theorem thueMorse_regular_of_not_isIntegral_inv {K : Type*} [Field K] {α : K} (hα : α ≠ 0)
    (hint : ¬ IsIntegral ℤ α⁻¹) : Polynomial.aeval α (mahlerMatrix 2 tmSigma).det ≠ 0 :=
  regular_of_not_isIntegral_inv 2 (by norm_num) tmSigma (Equiv.refl _)
    thueMorse_sigma_zero_isPermutation hα hint

/-- The iterates `(2/3)^{2^m}` are regular points of the Thue–Morse system. -/
@[category research solved, AMS 11 68, ref "AF17" "B1E2b", group "rb_mahler_examples"]
theorem thueMorse_regular_two_thirds (m : ℕ) :
    Polynomial.aeval ((2 / 3 : ℚ) ^ (2 ^ m)) (mahlerMatrix 2 tmSigma).det ≠ 0 :=
  regular_two_thirds 2 (by norm_num) tmSigma (Equiv.refl _) thueMorse_sigma_zero_isPermutation m

/-! ## Row 2: the Cantor sequence, base `3` -/

/-- **The Cantor sequence**: `1` exactly when the base-`3` expansion of `n` avoids the digit `1`,
i.e. the characteristic function of the Cantor set's endpoints. -/
@[category API, AMS 11 68, ref "AS03", group "rb_mahler_examples"]
def cantorSeq (n : ℕ) : ℕ := if 1 ∈ Nat.digits 3 n then 0 else 1

@[category API, AMS 11 68, ref "AS03", group "rb_mahler_examples"]
lemma cantorSeq_eq_zero_or_one (n : ℕ) : cantorSeq n = 0 ∨ cantorSeq n = 1 := by
  unfold cantorSeq; split <;> simp

@[category API, AMS 11 68, ref "AS03", group "rb_mahler_examples"]
lemma cantorSeq_zero : cantorSeq 0 = 1 := by simp [cantorSeq]

@[category research solved, AMS 11 68, ref "AS03", group "rb_mahler_examples"]
lemma cantorSeq_three_mul (n : ℕ) : cantorSeq (3 * n) = cantorSeq n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · unfold cantorSeq
    rw [Nat.digits_def' (by norm_num : 1 < 3) (by omega : 0 < 3 * n)]
    simp [Nat.mul_div_cancel_left n (show 0 < 3 by norm_num)]

@[category research solved, AMS 11 68, ref "AS03", group "rb_mahler_examples"]
lemma cantorSeq_three_mul_add_one (n : ℕ) : cantorSeq (3 * n + 1) = 0 := by
  unfold cantorSeq
  rw [Nat.digits_def' (by norm_num : 1 < 3) (by omega : 0 < 3 * n + 1),
    show (3 * n + 1) % 3 = 1 by omega]
  simp

@[category research solved, AMS 11 68, ref "AS03", group "rb_mahler_examples"]
lemma cantorSeq_three_mul_add_two (n : ℕ) : cantorSeq (3 * n + 2) = cantorSeq n := by
  unfold cantorSeq
  rw [Nat.digits_def' (by norm_num : 1 < 3) (by omega : 0 < 3 * n + 2),
    show (3 * n + 2) % 3 = 2 by omega, show (3 * n + 2) / 3 = n by omega]
  simp

/-- **Digit-block multiplicativity**: for `j < 3^i`, `c(3^i·n + j) = c(n)·c(j)` — the expansion
avoids `1` iff both blocks do. -/
@[category research solved, AMS 11 68, ref "AS03" "B1E2b", group "rb_mahler_examples"]
lemma cantorSeq_pow_mul_add (i : ℕ) : ∀ j n, j < 3 ^ i →
    cantorSeq (3 ^ i * n + j) = cantorSeq n * cantorSeq j := by
  induction i with
  | zero =>
    intro j n hj
    interval_cases j
    simp [cantorSeq_zero]
  | succ i ih =>
    intro j n hj
    obtain ⟨j', r, hr, rfl⟩ : ∃ j' r, r < 3 ∧ j = 3 * j' + r :=
      ⟨j / 3, j % 3, by omega, by omega⟩
    have hj' : j' < 3 ^ i := by rw [pow_succ] at hj; omega
    rw [show 3 ^ (i + 1) * n + (3 * j' + r) = 3 * (3 ^ i * n + j') + r by ring]
    interval_cases r
    · rw [add_zero, add_zero, cantorSeq_three_mul, ih j' n hj', cantorSeq_three_mul]
    · rw [cantorSeq_three_mul_add_one, cantorSeq_three_mul_add_one, mul_zero]
    · rw [cantorSeq_three_mul_add_two, ih j' n hj', cantorSeq_three_mul_add_two]

@[category API, AMS 11 68, ref "AS03", group "rb_mahler_examples"]
lemma cantorSeq_ne_zeroFun : cantorSeq ≠ fun _ => 0 := by
  intro hcon
  have h := congrFun hcon 0
  rw [cantorSeq_zero] at h
  simp at h

/-- **The `3`-kernel of the Cantor sequence is `{c, 0}`**: decimating by a block containing the
digit `1` kills the sequence, and every other decimation returns `c`. -/
@[category research solved, AMS 11 68, ref "AS03" "B1E2b", group "rb_mahler_examples"]
theorem cantorSeq_kernel_eq : kKernel 3 cantorSeq = {cantorSeq, fun _ => 0} := by
  ext s
  constructor
  · rintro ⟨i, r, hr, rfl⟩
    rcases cantorSeq_eq_zero_or_one r with h | h
    · right
      funext n
      rw [cantorSeq_pow_mul_add i r n hr, h, mul_zero]
    · left
      funext n
      rw [cantorSeq_pow_mul_add i r n hr, h, mul_one]
  · rintro (rfl | rfl)
    · exact ⟨0, 0, by norm_num, by funext n; norm_num⟩
    · refine ⟨1, 1, by norm_num, ?_⟩
      funext n
      rw [pow_one]
      exact (cantorSeq_three_mul_add_one n).symm

/-- The enumeration of the Cantor kernel: `0 ↦ c`, `1 ↦ 0`. -/
@[category API, AMS 11 68, ref "B1E2b", group "rb_mahler_examples"]
def cantorPhi : Fin 2 → ℕ → ℕ := ![cantorSeq, fun _ => 0]

/-- The Cantor decimation: `σ(c,·) = (c, 0, c)`, `σ(0,·) = (0,0,0)`. -/
@[category API, AMS 11 68, ref "AF17" "B1E2b", group "rb_mahler_examples"]
def cantorSigma : Fin 2 → Fin 3 → Fin 2 := ![![0, 1, 0], ![1, 1, 1]]

/-- **`cantorSigma` is the Mahler system of the Cantor sequence** ([B1E2b] WP9). -/
@[category research solved, AMS 11 68, ref "AS03" "AF17" "B1E2b", group "rb_mahler_examples"]
theorem cantorSeq_isKernelModel : IsKernelModel 3 cantorSeq cantorPhi cantorSigma := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp only [cantorPhi] at h ⊢
    · exact absurd h cantorSeq_ne_zeroFun
    · exact absurd h.symm cantorSeq_ne_zeroFun
  · ext s
    rw [cantorSeq_kernel_eq]
    simp [cantorPhi, Set.range, Fin.exists_fin_two, eq_comm]
  · intro i r n
    fin_cases i <;> fin_cases r
    all_goals simp only [cantorPhi, cantorSigma, Fin.isValue]
    all_goals simp [cantorSeq_three_mul, cantorSeq_three_mul_add_one, cantorSeq_three_mul_add_two]

/-- The Cantor sequence is `3`-automatic. -/
@[category research solved, AMS 11 68, ref "AS03", group "rb_mahler_examples"]
theorem cantorSeq_isAutomatic : IsAutomatic cantorSeq :=
  cantorSeq_isKernelModel.isAutomatic (by norm_num)

/-- `σ(·,0)` is the identity for the Cantor system as well. -/
@[category research solved, AMS 11 68, ref "AF17" "B1E2b", group "rb_mahler_examples"]
theorem cantor_sigma_zero_isPermutation (i : Fin 2) :
    (Equiv.refl (Fin 2)) i = cantorSigma i ⟨0, by norm_num⟩ := by
  revert i; decide

/-- `M(z) = ![![1 + z², z], ![0, 1 + z + z²]]`, so `det M = (1 + z²)(1 + z + z²)`.

The second factor is the row-sum factor of `RB.rowSum_dvd_det`, as it must be. -/
@[category research solved, AMS 11 68, ref "AF17" "B1E2b", group "rb_mahler_examples"]
theorem det_mahlerMatrix_cantorSigma :
    (mahlerMatrix 3 cantorSigma).det = (1 + X ^ 2) * (1 + X + X ^ 2) := by
  rw [Matrix.det_fin_two]
  simp [mahlerMatrix, cantorSigma, Fin.sum_univ_three]

/-- **Worked instance, base `3`** ([B1E2b] WP9): the iterates `(2/3)^{3^m}` are regular points of
the Cantor system. -/
@[category research solved, AMS 11 68, ref "AF17" "B1E2b", group "rb_mahler_examples"]
theorem cantor_regular_two_thirds (m : ℕ) :
    Polynomial.aeval ((2 / 3 : ℚ) ^ (3 ^ m)) (mahlerMatrix 3 cantorSigma).det ≠ 0 :=
  regular_two_thirds 3 (by norm_num) cantorSigma (Equiv.refl _)
    cantor_sigma_zero_isPermutation m

/-! ## Row 3: a collapsing example -/

/-- The parity sequence `n ↦ n % 2`. -/
@[category API, AMS 11 68, ref "B1E2b", group "rb_mahler_examples"]
def paritySeq (n : ℕ) : ℕ := n % 2

/-- **The `2`-kernel of the parity sequence is `{n%2, 0, 1}`**: every decimation of depth `≥ 1` is
constant, because `2^i·n` is even. -/
@[category research solved, AMS 11 68, ref "B1E2b", group "rb_mahler_examples"]
theorem paritySeq_kernel_eq :
    kKernel 2 paritySeq = {paritySeq, (fun _ => 0), (fun _ => 1)} := by
  ext s
  constructor
  · rintro ⟨i, r, hr, rfl⟩
    match i with
    | 0 =>
      left
      funext n
      simp [paritySeq]
      omega
    | (m + 1) =>
      have hconst : ∀ n, paritySeq (2 ^ (m + 1) * n + r) = r % 2 := by
        intro n
        show (2 ^ (m + 1) * n + r) % 2 = r % 2
        rw [show 2 ^ (m + 1) * n = 2 * (2 ^ m * n) by ring, Nat.mul_add_mod]
      rcases (by omega : r % 2 = 0 ∨ r % 2 = 1) with h | h
      · right; left; funext n; rw [hconst n, h]
      · right; right; funext n; rw [hconst n, h]
  · rintro (rfl | rfl | rfl)
    · refine ⟨0, 0, by norm_num, ?_⟩
      funext n
      show paritySeq n = paritySeq (2 ^ 0 * n + 0)
      norm_num
    · refine ⟨1, 0, by norm_num, ?_⟩
      funext n
      show (0 : ℕ) = paritySeq (2 ^ 1 * n + 0)
      simp [paritySeq]
    · refine ⟨1, 1, by norm_num, ?_⟩
      funext n
      show (1 : ℕ) = paritySeq (2 ^ 1 * n + 1)
      simp [paritySeq]

/-- The enumeration of the parity kernel: `0 ↦ n%2`, `1 ↦ 0`, `2 ↦ 1`. -/
@[category API, AMS 11 68, ref "B1E2b", group "rb_mahler_examples"]
def parityPhi : Fin 3 → ℕ → ℕ := ![paritySeq, (fun _ => 0), (fun _ => 1)]

/-- The parity decimation: `σ(p,0) = 0`, `σ(p,1) = 1`, and the constants are fixed. -/
@[category API, AMS 11 68, ref "B1E2b", group "rb_mahler_examples"]
def paritySigma : Fin 3 → Fin 2 → Fin 3 := ![![1, 2], ![1, 1], ![2, 2]]

/-- **`paritySigma` is the Mahler system of `n ↦ n % 2`** ([B1E2b] WP9). -/
@[category research solved, AMS 11 68, ref "AF17" "B1E2b", group "rb_mahler_examples"]
theorem paritySeq_isKernelModel : IsKernelModel 2 paritySeq parityPhi paritySigma := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    fin_cases i <;> fin_cases j <;> simp [parityPhi, paritySeq] at h0 h1 ⊢
  · ext s
    rw [paritySeq_kernel_eq]
    simp [parityPhi, Set.range, Fin.exists_fin_succ, eq_comm]
  · intro i r n
    fin_cases i <;> fin_cases r
    all_goals simp [parityPhi, paritySigma, paritySeq]

/-- The parity sequence is `2`-automatic. -/
@[category research solved, AMS 11 68, ref "B1E2b", group "rb_mahler_examples"]
theorem paritySeq_isAutomatic : IsAutomatic paritySeq :=
  paritySeq_isKernelModel.isAutomatic (by norm_num)

/-- **The permutation hypothesis fails on a real sequence** ([B1E2b] WP9, review item F4): the
`0`-decimation of the parity kernel sends both `n%2` and the constant `0` to the constant `0`. -/
@[category research solved, AMS 11 68, ref "AF17" "B1E2b", group "rb_mahler_examples"]
theorem paritySigma_zero_not_injective :
    ¬ Function.Injective fun i => paritySigma i ⟨0, by norm_num⟩ := by decide

/-- **And the system is degenerate**: `n%2` is in the image of no decimation, so `det M` has a zero
column and vanishes identically — *every* point is singular, `2/3` not specially so.

This is the shape of all 39130 vanishing systems found by the exhaustive search recorded in
`RB/Regularity.lean`.  For a collapsing system with `det M ≠ 0`, which WP8's lowest-coefficient
test decides, see `RB.nonPermSigma`. -/
@[category research solved, AMS 11 68, ref "AF17" "B1E2b", group "rb_mahler_examples"]
theorem det_mahlerMatrix_paritySigma : (mahlerMatrix 2 paritySigma).det = 0 := by
  rw [Matrix.det_fin_three]
  simp [mahlerMatrix, paritySigma, Fin.sum_univ_two]

/-- **The collapsing example, packaged** ([B1E2b] WP9): a genuine automatic sequence whose kernel
model has a non-injective `0`-decimation and identically vanishing determinant. -/
@[category research solved, AMS 11 68, ref "AF17" "B1E2b", group "rb_mahler_examples"]
theorem collapsing_example :
    ∃ (a : ℕ → ℕ) (φ : Fin 3 → ℕ → ℕ) (σ : Fin 3 → Fin 2 → Fin 3),
      IsKernelModel 2 a φ σ ∧ IsAutomatic a ∧
        ¬ Function.Injective (fun i => σ i ⟨0, by norm_num⟩) ∧
        (mahlerMatrix 2 σ).det = 0 :=
  ⟨paritySeq, parityPhi, paritySigma, paritySeq_isKernelModel, paritySeq_isAutomatic,
    paritySigma_zero_not_injective, det_mahlerMatrix_paritySigma⟩

/-! ## No free lunch: passing to base `k^t` ([B1E2b] WP9, WP10(i)) -/

/-- Decimation at residue `0`: `s ↦ (n ↦ s (k·n))`. -/
@[category API, AMS 11 68, ref "AF17" "B1E2b", group "rb_mahler_examples"]
def decZero (k : ℕ) (s : ℕ → ℕ) : ℕ → ℕ := fun n => s (k * n)

/-- **`σ_t(·,0) = σ(·,0)^t`** ([B1E2b] WP9): decimation at residue `0` in base `k^t` is the
`t`-fold composite of decimation at residue `0` in base `k`. -/
@[category research solved, AMS 11 68, ref "AF17" "B1E2b", group "rb_mahler_examples"]
theorem decZero_iterate (k : ℕ) (s : ℕ → ℕ) : ∀ t, (decZero k)^[t] s = decZero (k ^ t) s := by
  intro t
  induction t with
  | zero => funext n; simp [decZero]
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih]
    funext n
    show s (k ^ t * (k * n)) = s (k ^ (t + 1) * n)
    ring_nf

/-- On a finite type a composite power is bijective iff the map is. -/
@[category research solved, AMS 68, ref "B1E2b", group "rb_mahler_examples"]
theorem bijective_iterate_iff {ι : Type*} [Finite ι] (f : ι → ι) {t : ℕ} (ht : 0 < t) :
    Function.Bijective f^[t] ↔ Function.Bijective f := by
  constructor
  · intro h
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    rw [Function.iterate_succ] at h
    exact Finite.injective_iff_bijective.mp (h.injective.of_comp)
  · intro h
    exact h.iterate t

/-- **The obvious repair provably fails** ([B1E2b] WP9, and WP10(i)): reading a `k`-automatic
sequence in base `k^t` cannot turn a collapsing `0`-decimation into a permutation, because the new
`0`-decimation is the `t`-fold composite of the old one (`decZero_iterate`) and a power of a map on
a finite set is bijective exactly when the map is. -/
@[category research solved, AMS 11 68, ref "AF17" "B1E2b", group "rb_mahler_examples"]
theorem sigma_pow_zero_perm_iff {ι : Type*} [Finite ι] {k : ℕ} (hk : 0 < k) (σ : ι → Fin k → ι)
    {t : ℕ} (ht : 0 < t) :
    Function.Bijective (fun i => σ i ⟨0, hk⟩)^[t] ↔ Function.Bijective fun i => σ i ⟨0, hk⟩ :=
  bijective_iterate_iff _ ht

/-! ## The decision procedure ([B1E2b] WP9, review item B8) -/

/-- **The certificate form of the regularity test** ([B1E2b] WP9, review item B8): supply the
factorization `det M = z^e·g` — one `Matrix.det_fin_two`/`det_fin_three` plus `simp` — and
regularity at a rational point reduces to the integer divisibility `α.num ∤ g(0)`.

`Polynomial` is noncomputable in Mathlib, so a `Bool`-valued `decideRegular` cannot exist; this is
the decidable content of the plan's decision module, and it needs no `native_decide`.  Note the
certificate does *not* have to exhibit the trailing degree: any factorization `z^e·g` with
`α.num ∤ g(0)` works, and `e = 0` is the common case. -/
@[category research solved, AMS 11 68, ref "AF17" "B1E2b", group "rb_mahler_examples"]
theorem regular_of_certificate {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (σ : ι → Fin k → ι) (e : ℕ) (g : Polynomial ℤ)
    (hdet : (mahlerMatrix k σ).det = X ^ e * g) {α : ℚ} (hα : α ≠ 0)
    (hdvd : ¬ (α.num ∣ g.coeff 0)) : Polynomial.aeval α (mahlerMatrix k σ).det ≠ 0 := by
  intro h
  rw [hdet, map_mul, map_pow, Polynomial.aeval_X] at h
  refine hdvd (num_dvd_coeff_zero ?_)
  rcases mul_eq_zero.mp h with h' | h'
  · exact absurd (pow_eq_zero_iff' .. |>.mp h').1 hα
  · exact h'

/-- Certified row 1: `2/3` is a regular point of the Thue–Morse system, by the certificate
`det M = z⁰·(1 - z²)` and `2 ∤ 1`. -/
@[category research solved, AMS 11 68, ref "AF17" "B1E2b", group "rb_mahler_examples"]
theorem thueMorse_regular_two_thirds_cert :
    Polynomial.aeval (2 / 3 : ℚ) (mahlerMatrix 2 tmSigma).det ≠ 0 :=
  regular_of_certificate 2 tmSigma 0 (1 - X ^ 2)
    (by rw [det_mahlerMatrix_tmSigma]; ring) (by norm_num)
    (by norm_num)

/-- Certified row 2: `2/3` is a regular point of the Cantor system. -/
@[category research solved, AMS 11 68, ref "AF17" "B1E2b", group "rb_mahler_examples"]
theorem cantor_regular_two_thirds_cert :
    Polynomial.aeval (2 / 3 : ℚ) (mahlerMatrix 3 cantorSigma).det ≠ 0 :=
  regular_of_certificate 3 cantorSigma 0 ((1 + X ^ 2) * (1 + X + X ^ 2))
    (by rw [det_mahlerMatrix_cantorSigma]; ring) (by norm_num)
    (by norm_num)

end RB
