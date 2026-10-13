/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.GenSound
import ForMathlib.Topology.MetricSpace.BoxDimension

/-!
# The entropy ledger bounds the dimension of the real avoiders (plan-dubC2-transform T6(b))

For an atlas cell `P = (p/q, ν, 𝒫)` let `A` be the set of real `ξ` whose sequence
`xₙ = ⌊ξ(p/q)ⁿ + ν⌋` *eventually* avoids `𝒫`.  A certificate (`Gen.Checked`) says `A = ∅`; an
uncertified cell still has an entropy `λ_det`, the growth rate of its carry-word language, and
this file proves the honest dimension statement of the plan's §6.2:

  `dim_H A ≤ log λ / log (p/q)`   for every `λ ≥ λ_det` carried by an `EntCert`.

## The Lean meaning of `λ_det`

`λ_det` is the spectral radius of the determinized hull graph.  No eigentheory is used: an
`EntCert` is a subset automaton (`sets`, bitmasks over the hull vertices, state `0` = all of
them; `trans`, one `Option` target per state and letter) together with integer weights `w` and
a ratio `a / b` such that `b · ∑_letters w(target) ≤ a · w(state)` at every state — the
Collatz–Wielandt inequality, which bounds the spectral radius by `a / b`.  The kernel checks it
(`EntCert.check`), and `dcount_le` turns it into the word count `#words_L ≤ w₀ (a/b)^L`.

## The covering

Real orbits are hull paths (`Gen.sound`), hull paths are words of the subset automaton
(`cword_mem`), and the integer `x_{N+L}` is determined by `x_N` and the carry word through
`q·x_{n+1} = p·xₙ + sₙ` (`xs_add_eq_runX`).  Since `ξ` lies within `(q/p)^{N+L}/2` of a point
determined by `x_{N+L}`, the avoiders in a bounded interval are covered by
`#{x_N} · w₀ · (a/b)^L` balls of radius `(q/p)^L` (`upperBoxDim_avoiders_le`), and a countable
union gives the Hausdorff statement (`dimH_eventually_avoids_le`).

The bound concerns the *real* avoiders and is derived from the *model*: it is `1` (vacuous) at
`𝒫 = {2}`, where the model has `λ_det = 3/2`, as it must be — this is Mahler's problem.
-/

namespace DubC2.Gen

open Filter Metric Set
open scoped ENNReal NNReal

/-! ## The subset-automaton certificate -/

/-- An entropy certificate: a subset automaton over the hull vertices with Collatz–Wielandt
weights. -/
structure EntCert where
  /-- The states, as bitmasks over hull vertices; state `0` must be all of them. -/
  sets : List ℕ
  /-- The transitions, indexed by state and letter index. -/
  trans : List (List (Option ℕ))
  /-- The weights. -/
  w : List ℕ
  /-- Numerator of the ratio. -/
  a : ℕ
  /-- Denominator of the ratio. -/
  b : ℕ

namespace EntCert

variable (E : EntCert) (P : Params)

/-- The transition of state `i` on letter index `t`. -/
def tr (i t : ℕ) : Option ℕ := (E.trans.getD i []).getD t none

/-- The weight of state `i`. -/
def wt (i : ℕ) : ℕ := E.w.getD i 0

/-- Vertex `k` belongs to state `i`. -/
def mem (i k : ℕ) : Bool := (E.sets.getD i 0).testBit k

/-- The weight of an optional target. -/
def wopt (o : Option ℕ) : ℕ := o.elim 0 E.wt

/-- The weighted out-sum of state `i`. -/
def wsum (i : ℕ) : ℕ := ∑ t ∈ Finset.range P.nA, E.wopt (E.tr i t)

/-- State `i` is closed: every hull successor of every member lies in the target state. -/
def closeOK (i : ℕ) : Bool :=
  (List.range P.nA).all fun t => (List.range P.nV).all fun k =>
    !(E.mem i k) || (P.succList k (P.letter t)).all fun k' =>
      match E.tr i t with
      | some j => E.mem j k'
      | none => false

/-- The targets of state `i` are states. -/
def transOK (i : ℕ) : Bool :=
  (List.range P.nA).all fun t =>
    match E.tr i t with
    | some j => decide (j < E.sets.length)
    | none => true

/-- The full check. -/
def check : Bool :=
  checkParams P && decide (0 < E.sets.length) && decide (0 < E.b) && decide (E.b ≤ E.a) &&
    ((List.range P.nV).all fun k => E.mem 0 k) &&
    ((List.range E.sets.length).all fun i =>
      E.closeOK P i && E.transOK P i && decide (0 < E.wt i) &&
        decide (E.b * E.wsum P i ≤ E.a * E.wt i))

/-- The words of the automaton from state `i`. -/
def dwords : ℕ → ℕ → Finset (List ℤ)
  | _, 0 => {[]}
  | i, L + 1 => (Finset.range P.nA).biUnion fun t =>
      (E.tr i t).elim ∅ fun j => (dwords j L).image (P.letter t :: ·)

/-- The path count of the automaton from state `i`. -/
def dcount : ℕ → ℕ → ℕ
  | _, 0 => 1
  | i, L + 1 => ∑ t ∈ Finset.range P.nA, (E.tr i t).elim 0 fun j => dcount j L

theorem card_dwords_le : ∀ (L i : ℕ), (E.dwords P i L).card ≤ E.dcount P i L := by
  intro L
  induction L with
  | zero => intro i; simp [dwords, dcount]
  | succ L ih =>
    intro i
    simp only [dwords, dcount]
    refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun t _ => ?_)
    cases E.tr i t with
    | none => simp
    | some j => exact Finset.card_image_le.trans (ih j)

/-- The unpacked check. -/
structure Facts : Prop where
  par : checkParams P = true
  len : 0 < E.sets.length
  b0 : 0 < E.b
  ba : E.b ≤ E.a
  init : ∀ k < P.nV, E.mem 0 k = true
  close : ∀ i < E.sets.length, ∀ t < P.nA, ∀ k < P.nV, E.mem i k = true →
    ∀ k' ∈ P.succList k (P.letter t), ∃ j, E.tr i t = some j ∧ E.mem j k' = true
  trans : ∀ i < E.sets.length, ∀ t < P.nA, ∀ j, E.tr i t = some j → j < E.sets.length
  w0 : ∀ i < E.sets.length, 0 < E.wt i
  cw : ∀ i < E.sets.length, E.b * E.wsum P i ≤ E.a * E.wt i

theorem facts (h : E.check P = true) : E.Facts P := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
    at h
  obtain ⟨⟨⟨⟨⟨hpar, hlen⟩, hb⟩, hba⟩, hinit⟩, hall⟩ := h
  refine ⟨hpar, hlen, hb, hba, hinit, ?_, ?_, fun i hi => (hall i hi).1.2,
    fun i hi => (hall i hi).2⟩
  · intro i hi t ht k hk hm k' hk'
    have := (hall i hi).1.1.1
    simp only [closeOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true']
      at this
    rcases this t ht k hk with h0 | h1
    · simp [hm] at h0
    · have := h1 k' hk'
      revert this
      cases E.tr i t with
      | none => simp
      | some j => intro h; exact ⟨j, rfl, h⟩
  · intro i hi t ht j hj
    have := (hall i hi).1.1.2
    simp only [transOK, List.all_eq_true, List.mem_range] at this
    have := this t ht
    rw [hj] at this
    simpa using this

variable {E P}

/-- **The Collatz–Wielandt bound**: `b^L · #paths_L(i) ≤ a^L · w(i)`. -/
@[category API, AMS 11 37, ref "DN05", group "dubc2_entropy"]
theorem dcount_le (hE : E.Facts P) :
    ∀ (L i : ℕ), i < E.sets.length → E.b ^ L * E.dcount P i L ≤ E.a ^ L * E.wt i := by
  intro L
  induction L with
  | zero => intro i hi; simpa [dcount, Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero] using hE.w0 i hi
  | succ L ih =>
    intro i hi
    have hstep : ∀ t ∈ Finset.range P.nA,
        E.b ^ L * (E.tr i t).elim 0 (fun j => E.dcount P j L) ≤ E.a ^ L * E.wopt (E.tr i t) := by
      intro t ht
      rcases h : E.tr i t with _ | j
      · simp
      · simpa [wopt] using ih j (hE.trans i hi t (Finset.mem_range.1 ht) j h)
    calc E.b ^ (L + 1) * E.dcount P i (L + 1)
        = E.b * ∑ t ∈ Finset.range P.nA,
            E.b ^ L * (E.tr i t).elim 0 (fun j => E.dcount P j L) := by
          simp only [dcount, Finset.mul_sum]; ring_nf
      _ ≤ E.b * ∑ t ∈ Finset.range P.nA, E.a ^ L * E.wopt (E.tr i t) :=
          Nat.mul_le_mul_left _ (Finset.sum_le_sum hstep)
      _ = E.a ^ L * (E.b * E.wsum P i) := by
          simp only [wsum, Finset.mul_sum]; ring_nf
      _ ≤ E.a ^ L * (E.a * E.wt i) := Nat.mul_le_mul_left _ (hE.cw i hi)
      _ = E.a ^ (L + 1) * E.wt i := by ring

/-- The real form: `#words_L(0) ≤ w₀ · (a/b)^L`. -/
theorem card_dwords_zero_le (hE : E.Facts P) (L : ℕ) :
    ((E.dwords P 0 L).card : ℝ) ≤ E.wt 0 * ((E.a : ℝ) / E.b) ^ L := by
  have hb : (0 : ℝ) < E.b := by exact_mod_cast hE.b0
  have h1 : ((E.b ^ L * E.dcount P 0 L : ℕ) : ℝ) ≤ ((E.a ^ L * E.wt 0 : ℕ) : ℝ) := by
    exact_mod_cast dcount_le hE L 0 hE.len
  push_cast at h1
  have h2 : ((E.dwords P 0 L).card : ℝ) ≤ E.dcount P 0 L := by
    exact_mod_cast card_dwords_le E P L 0
  rw [div_pow, mul_div_assoc', le_div_iff₀ (by positivity)]
  nlinarith [pow_pos hb L]

end EntCert

/-! ## Real orbits are automaton words -/

section Orbit

variable {P : Params} {ξ : ℝ}

/-- The carry word `s_N, …, s_{N+L−1}`. -/
noncomputable def cword (P : Params) (ξ : ℝ) (N L : ℕ) : List ℤ :=
  (List.range L).map fun i => cs P ξ (N + i)

theorem cword_succ (N L : ℕ) : cword P ξ N (L + 1) = cs P ξ N :: cword P ξ (N + 1) L := by
  simp only [cword, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp, Nat.add_succ, Nat.succ_add]

/-- Running the recurrence `x ↦ (p·x + s)/q` along a carry word. -/
def runX (p q : ℕ) : ℤ → List ℤ → ℤ
  | x, [] => x
  | x, c :: w => runX p q (((p : ℤ) * x + c) / q) w

theorem xs_add_eq_runX (hF : ParamFacts P) :
    ∀ L N, xs P ξ (N + L) = runX P.p P.q (xs P ξ N) (cword P ξ N L) := by
  intro L
  induction L with
  | zero => intro N; simp [cword, runX]
  | succ L ih =>
    intro N
    have hq : (P.q : ℤ) ≠ 0 := by have := hF.q1; omega
    have hstep : ((P.p : ℤ) * xs P ξ N + cs P ξ N) / P.q = xs P ξ (N + 1) := by
      rw [← q_mul_xs_succ, Int.mul_ediv_cancel_left _ hq]
    rw [cword_succ, runX, hstep, ← ih (N + 1)]
    congr 1; omega

/-- **Real avoiders are words of the subset automaton.** -/
@[category API, AMS 11 37, ref "DN05", group "dubc2_entropy"]
theorem cword_mem {E : EntCert} (hE : E.Facts P) :
    ∀ L N i, (∀ n, N ≤ n → Avoids P ξ n) → i < E.sets.length →
      E.mem i (vtx P ξ N) = true → cword P ξ N L ∈ E.dwords P i L := by
  have hF : ParamFacts P := paramFacts hE.par
  intro L
  induction L with
  | zero => intro N i _ _ _; simp [cword, EntCert.dwords]
  | succ L ih =>
    intro N i hav hi hm
    obtain ⟨hv, ht, hlet, hsucc⟩ := sound hF (hav N le_rfl) (hav (N + 1) (by omega))
    obtain ⟨j, hj, hmj⟩ := hE.close i hi (tix P ξ N) ht (vtx P ξ N) hv hm _ hsucc
    have hjl := hE.trans i hi _ ht j hj
    rw [cword_succ, EntCert.dwords, Finset.mem_biUnion]
    refine ⟨tix P ξ N, Finset.mem_range.2 ht, ?_⟩
    rw [hj, Option.elim, Finset.mem_image]
    exact ⟨_, ih (N + 1) j (fun n hn => hav n (by omega)) hjl hmj, by rw [hlet]⟩

/-- `ξ` lies within `(q/p)^n / 2` of the point determined by `xₙ`. -/
theorem abs_sub_ctr_le (hF : ParamFacts P) (n : ℕ) :
    |ξ - ((xs P ξ n : ℝ) - P.nu + 1 / 2) * ((P.q : ℝ) / P.p) ^ n|
      ≤ ((P.q : ℝ) / P.p) ^ n / 2 := by
  have hq : (0 : ℝ) < P.q := by have := hF.q1; exact_mod_cast (by omega : 0 < P.q)
  have hp : (0 : ℝ) < P.p := by have := hF.q1; have := hF.pq; exact_mod_cast (by omega : 0 < P.p)
  have h0 : (xs P ξ n : ℝ) ≤ ξ * ((P.p : ℝ) / P.q) ^ n + P.nu := Int.floor_le _
  have h1 : ξ * ((P.p : ℝ) / P.q) ^ n + P.nu < xs P ξ n + 1 := Int.lt_floor_add_one _
  set σ : ℝ := ((P.q : ℝ) / P.p) ^ n with hσ
  have hσ0 : 0 < σ := by positivity
  have hρσ : ((P.p : ℝ) / P.q) ^ n * σ = 1 := by
    rw [hσ, ← mul_pow, div_mul_div_comm, mul_comm (P.p : ℝ), div_self (by positivity), one_pow]
  have hξ : ξ = (ξ * ((P.p : ℝ) / P.q) ^ n) * σ := by rw [mul_assoc, hρσ, mul_one]
  rw [abs_le]
  constructor <;> nlinarith [hξ]

end Orbit

/-! ## The dimension bounds -/

section Dimension

variable {P : Params} {E : EntCert}

/-- The avoiders from time `N` in `[lo, hi]`. -/
def avoidersFrom (P : Params) (N : ℕ) (lo hi : ℝ) : Set ℝ :=
  {ξ | ξ ∈ Icc lo hi ∧ ∀ n, N ≤ n → Avoids P ξ n}

/-- **The box-dimension bound.**  The avoiders from time `N` in a bounded interval have upper box
dimension at most `log (a/b) / log (p/q)`. -/
@[category research solved, AMS 11 28 37, ref "DN05", group "dubc2_entropy"]
theorem upperBoxDim_avoiders_le (hc : E.check P = true) (N : ℕ) (lo hi : ℝ) :
    upperBoxDim (avoidersFrom P N lo hi)
      ≤ ((Real.log ((E.a : ℝ) / E.b) / Real.log ((P.p : ℝ) / P.q) : ℝ) : EReal) := by
  have hE := E.facts P hc
  have hF : ParamFacts P := paramFacts hE.par
  have hq : (0 : ℝ) < P.q := by have := hF.q1; exact_mod_cast (by omega : 0 < P.q)
  have hpq : (P.q : ℝ) < P.p := by exact_mod_cast hF.pq
  have hp : (0 : ℝ) < P.p := hq.trans hpq
  have hb : (0 : ℝ) < E.b := by exact_mod_cast hE.b0
  have hab : (0 : ℝ) < (E.a : ℝ) / E.b := by
    have : (E.b : ℝ) ≤ E.a := by exact_mod_cast hE.ba
    exact div_pos (hb.trans_le this) hb
  set r : ℝ≥0 := ⟨(P.q : ℝ) / P.p, by positivity⟩ with hr
  have hrR : (r : ℝ) = (P.q : ℝ) / P.p := rfl
  have hr0 : 0 < r := by rw [← NNReal.coe_pos, hrR]; positivity
  have hr1 : r < 1 := by rw [← NNReal.coe_lt_one, hrR, div_lt_one hp]; exact hpq
  -- the range of `x_N`
  set ρN : ℝ := ((P.p : ℝ) / P.q) ^ N
  have hρN : 0 < ρN := by positivity
  set X : Finset ℤ := Finset.Icc ⌊lo * ρN + P.nu⌋ ⌊hi * ρN + P.nu⌋
  have hX : ∀ ξ ∈ avoidersFrom P N lo hi, xs P ξ N ∈ X := by
    intro ξ hξ
    simp only [X, Finset.mem_Icc]
    exact ⟨Int.floor_mono (by have := hξ.1.1; simp only [Z32.orb]; nlinarith),
      Int.floor_mono (by have := hξ.1.2; simp only [Z32.orb]; nlinarith)⟩
  -- the centres at depth `L`
  let ctr : ℕ → ℤ → ℝ := fun L x => ((x : ℝ) - P.nu + 1 / 2) * ((P.q : ℝ) / P.p) ^ (N + L)
  let T : ℕ → Finset ℝ := fun L =>
    (X.biUnion fun x => (E.dwords P 0 L).image (runX P.p P.q x)).image (ctr L)
  have hcover : ∀ L, IsCover (r ^ L) (avoidersFrom P N lo hi) (T L : Set ℝ) := by
    intro L ξ hξ
    refine ⟨ctr L (xs P ξ (N + L)), ?_, ?_⟩
    · simp only [T, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_biUnion,
        Finset.mem_image]
      refine ⟨xs P ξ (N + L), ⟨xs P ξ N, hX ξ hξ, cword P ξ N L,
        cword_mem hE L N 0 hξ.2 hE.len (hE.init _ (sound hF (hξ.2 N le_rfl)
          (hξ.2 (N + 1) (by omega))).1), (xs_add_eq_runX hF L N).symm⟩, rfl⟩
    · show edist ξ (ctr L (xs P ξ (N + L))) ≤ (r ^ L : ℝ≥0)
      rw [edist_dist, ← ENNReal.ofReal_coe_nnreal]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [Real.dist_eq, NNReal.coe_pow, hrR]
      refine (abs_sub_ctr_le hF (N + L)).trans ?_
      have h1 : ((P.q : ℝ) / P.p) ^ (N + L) ≤ ((P.q : ℝ) / P.p) ^ L :=
        pow_le_pow_of_le_one (by positivity) (by rw [div_le_one hp]; exact hpq.le) (by omega)
      have h2 : 0 ≤ ((P.q : ℝ) / P.p) ^ (N + L) := by positivity
      linarith
  have hcard : ∀ L, ((T L).card : ℝ) ≤ (X.card * E.wt 0 : ℝ) * ((E.a : ℝ) / E.b) ^ L := by
    intro L
    have h1 : (T L).card ≤ ∑ x ∈ X, (E.dwords P 0 L).card :=
      Finset.card_image_le.trans
        (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ => Finset.card_image_le))
    have h1' : ((T L).card : ℝ) ≤ X.card * ((E.dwords P 0 L).card : ℝ) := by
      rw [Finset.sum_const, smul_eq_mul] at h1; exact_mod_cast h1
    have h2 := EntCert.card_dwords_zero_le hE L
    have hXc : (0 : ℝ) ≤ X.card := Nat.cast_nonneg _
    calc ((T L).card : ℝ) ≤ X.card * ((E.dwords P 0 L).card : ℝ) := h1'
      _ ≤ X.card * (E.wt 0 * ((E.a : ℝ) / E.b) ^ L) := mul_le_mul_of_nonneg_left h2 hXc
      _ = (X.card * E.wt 0 : ℝ) * ((E.a : ℝ) / E.b) ^ L := by ring
  have hbound : ∀ L, (externalCoveringNumber (r ^ L) (avoidersFrom P N lo hi) : ℝ≥0∞)
      ≤ ENNReal.ofReal (X.card * E.wt 0 : ℝ) * ENNReal.ofReal ((E.a : ℝ) / E.b) ^ L := by
    intro L
    have h := (hcover L).externalCoveringNumber_le_encard
    rw [Set.encard_coe_eq_coe_finsetCard] at h
    refine (ENat.toENNReal_mono h).trans ?_
    rw [ENat.toENNReal_coe, ← ENNReal.ofReal_pow hab.le,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (hcard L)
  have := upperBoxDim_le_of_covering hr0 hr1 ENNReal.ofReal_ne_top hbound
  rw [ENNReal.log_ofReal_of_pos hab, hrR, inv_div, ← EReal.coe_div] at this
  exact this

/-- **The Hausdorff-dimension bound** (plan-dubC2-transform T6(b)): the real `ξ` for which
`⌊ξ(p/q)ⁿ + ν⌋` eventually avoids the divisor set form a set of Hausdorff dimension at most
`log (a/b) / log (p/q)`, for every checked entropy certificate. -/
@[category research solved, AMS 11 28 37, ref "DN05", group "dubc2_entropy"]
theorem dimH_eventually_avoids_le (hc : E.check P = true) :
    dimH {ξ : ℝ | ∀ᶠ n in atTop, Avoids P ξ n}
      ≤ ENNReal.ofReal (Real.log ((E.a : ℝ) / E.b) / Real.log ((P.p : ℝ) / P.q)) := by
  have hE := E.facts P hc
  have hF : ParamFacts P := paramFacts hE.par
  set t : ℝ := Real.log ((E.a : ℝ) / E.b) / Real.log ((P.p : ℝ) / P.q)
  have hq : (0 : ℝ) < P.q := by have := hF.q1; exact_mod_cast (by omega : 0 < P.q)
  have hpq : (P.q : ℝ) < P.p := by exact_mod_cast hF.pq
  have hb : (0 : ℝ) < E.b := by exact_mod_cast hE.b0
  have ht : 0 ≤ t := by
    refine div_nonneg (Real.log_nonneg ?_) (Real.log_nonneg ?_)
    · rw [le_div_iff₀ hb, one_mul]; exact_mod_cast hE.ba
    · rw [le_div_iff₀ hq, one_mul]; exact hpq.le
  have hsub : {ξ : ℝ | ∀ᶠ n in atTop, Avoids P ξ n}
      ⊆ ⋃ N : ℕ, ⋃ m : ℕ, avoidersFrom P N (-m) m := by
    intro ξ hξ
    obtain ⟨N, hN⟩ := eventually_atTop.1 hξ
    simp only [Set.mem_iUnion]
    refine ⟨N, ⌈|ξ|⌉₊, ⟨⟨?_, ?_⟩, hN⟩⟩
    · have := Nat.le_ceil |ξ|; have := neg_abs_le ξ; linarith
    · exact (le_abs_self ξ).trans (Nat.le_ceil _)
  refine (dimH_mono hsub).trans ?_
  rw [dimH_iUnion]
  refine iSup_le fun N => ?_
  rw [dimH_iUnion]
  refine iSup_le fun m => ?_
  rcases (avoidersFrom P N (-m) m).eq_empty_or_nonempty with h | h
  · rw [h, dimH_empty]; exact zero_le
  · have h1 := (dimH_le_upperBoxDim h).trans (upperBoxDim_avoiders_le hc N (-m) m)
    rw [← EReal.coe_ennreal_le_coe_ennreal_iff, EReal.coe_ennreal_ofReal, max_eq_left ht]
    exact h1

end Dimension

end DubC2.Gen
