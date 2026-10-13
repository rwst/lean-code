/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import DubC2.FollowerInfinite

/-!
# The literal completeness question (T5(iv))

The literal form of T5(iv) asks: **if every avoiding pseudo-orbit of a cell is eventually periodic,
is the cell certified?**  The converse is `DubC2.Gen.PseudoOrbit.eventuallyPeriodic`.  This file
proves the literal form for **every** cell (`T5iv_literal`):

> some `D` certifies  ⟺  every avoiding pseudo-orbit is eventually periodic.

**Why there is something to prove.**  If no `D` certifies, `F` is infinite or has a reachable
branching state (`checked_iff_finite`), so some infinite word keeps the root of `F` alive and is not
eventually periodic (`exists_aperiodic_adm`).  Its prefixes are realized by pseudo-orbit segments,
but the half-open intervals of `F` may shrink to an excluded right endpoint.  Then the limit orbit
`y*` hits the value `1`, where no pseudo-orbit lives.  This is the boundary-degenerate case.

**Why it cannot persist.**  The limit orbit is the supremum of backward realizations of the prefixes
(`ystar`), so after a hit of `1` every later value is approached strictly from below and is positive.
Between two hits the values `b·y*` are integers (a `q`-adic argument, `int_of_hits`).
* When `gcd(q, b) = 1` an integer value in `(0, b]` determines the next one (`det_step`), so
  infinitely many hits make the word eventually periodic (`hits_finite_cop`).
* Two hits force `gcd(q, b) ∣ a`: the value after a hit is an integer `w` with
  `q·w = p·b − b·s − (p−q)·a` (`gcd_dvd_of_two_hits`).  So when `gcd(q, b)` is prime to `a`, the
  case `gcd(q, b) > 1` has at most one hit.

Hence, when `gcd(q, b)` is prime to `a`, an aperiodic admissible word hits `1` only finitely often
(`hits_finite`), and a tail of its limit orbit is an aperiodic avoiding pseudo-orbit
(`exists_aperiodic_pseudoOrbit`).  That condition holds once `ν = a/b` is in lowest terms
(`coprime_red`), and both the follower automaton and the pseudo-orbits depend on `ν` only
(`step_red`, `pseudoOrbit_of_red`).  So no case remains.

## Main results

* `DubC2.Gen.Follower.exists_aperiodic_adm` — an uncertified cell has an aperiodic admissible word;
* `DubC2.Gen.Follower.hits_finite` — an aperiodic admissible word hits `1` only finitely often
  (`gcd(q, b)` prime to `a`);
* `DubC2.Gen.Follower.exists_aperiodic_pseudoOrbit` — then it yields an aperiodic avoiding
  pseudo-orbit;
* `DubC2.Gen.Follower.T5iv_literal` — the literal T5(iv), for every cell.

## References

* [Oda26] Y. Odagiri, *Finite graph certificates for composite terms in rational floor sequences*,
  Zenodo, doi:10.5281/zenodo.22997709 (2026).
-/

namespace DubC2.Gen

namespace Follower

open Filter ForMathlib.SubwordComplexity Horse Branch

variable {P : Params}

/-! ## Words -/

variable (P) in
/-- An admissible infinite word: every prefix keeps the root of `F` alive. -/
def Adm (s : ℕ → ℤ) : Prop := ∀ m, (stepw P (root P) (pre s m)).isSome

theorem pre_add (s : ℕ → ℤ) (m k : ℕ) :
    pre s (m + k) = pre s m ++ (List.range k).map fun i => s (m + i) := by
  simp only [pre, List.range_add, List.map_append, List.map_map]
  rfl

theorem isSome_of_append {X : FState} {u v : List ℤ} (h : (stepw P X (u ++ v)).isSome) :
    (stepw P X u).isSome := by
  rw [stepw_append] at h
  cases hu : stepw P X u <;> simp_all

theorem adm_mono {s : ℕ → ℤ} {m m' : ℕ} (hm : m' ≤ m)
    (h : (stepw P (root P) (pre s m)).isSome) : (stepw P (root P) (pre s m')).isSome := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [pre_add] at h
  exact isSome_of_append h

theorem periodic_of_shift {s : ℕ → ℤ} {k : ℕ} (h : IsEventuallyPeriodic fun n => s (n + k)) :
    IsEventuallyPeriodic s := by
  obtain ⟨N, per, hper, hp⟩ := h
  refine ⟨N + k, per, hper, fun n hn => ?_⟩
  have := hp (n - k) (by omega)
  simp only at this
  rwa [show n - k + per + k = n + per by omega, show n - k + k = n by omega] at this

theorem shift_of_periodic {s : ℕ → ℤ} (k : ℕ) (h : IsEventuallyPeriodic s) :
    IsEventuallyPeriodic fun n => s (n + k) := by
  obtain ⟨N, per, hper, hp⟩ := h
  exact ⟨N, per, hper, fun n hn => by
    show s (n + per + k) = s (n + k)
    rw [show n + per + k = n + k + per by ring]
    exact hp _ (by omega)⟩

/-- The word `u` followed by the sequence `t`. -/
def app (u : List ℤ) (t : ℕ → ℤ) (n : ℕ) : ℤ :=
  if n < u.length then u.getD n 0 else t (n - u.length)

theorem pre_app (u : List ℤ) (t : ℕ → ℤ) : ∀ n, pre (app u t) (u.length + n) = u ++ pre t n
  | 0 => by
    refine List.ext_getElem (by simp [pre_length]) fun i h1 h2 => ?_
    have hi : i < u.length := by simpa [pre_length] using h1
    simp [pre, app, hi]
  | n + 1 => by
    rw [← add_assoc, pre_succ, pre_app u t n, pre_succ, List.append_assoc]
    simp [app]

theorem rep_length (α : List ℤ) : ∀ k, (rep k α).length = k * α.length
  | 0 => by simp [rep]
  | k + 1 => by rw [rep_succ, List.length_append, rep_length α k]; ring

/-- **An uncertified cell has an admissible word that is not eventually periodic**: from an
injective path if `F` is infinite, from two loops at a branching state otherwise. -/
theorem exists_aperiodic_adm (hP : checkParams P = true)
    (h : ¬ ({X | Reach P (root P) X}.Finite ∧ ∀ X, Reach P (root P) X → ¬ Branching P X)) :
    ∃ s, Adm P s ∧ ¬ IsEventuallyPeriodic s := by
  have hF := paramFacts hP
  by_cases hfin : {X | Reach P (root P) X}.Finite
  · have hb : ∃ X, Reach P (root P) X ∧ Branching P X := by
      by_contra hc
      push Not at hc
      exact h ⟨hfin, fun X hX hb => hc X hX hb⟩
    obtain ⟨X₀, hX₀, s₁, s₂, Y₁, Y₂, hne, h₁, h₂, hr₁, hr₂⟩ := hb
    obtain ⟨u₁, hu₁⟩ := stepw_of_reach hr₁
    obtain ⟨u₂, hu₂⟩ := stepw_of_reach hr₂
    set α := s₁ :: u₁
    set β := s₂ :: u₂
    have hα : stepw P X₀ α = some X₀ := by simp only [α, stepw, h₁, Option.bind_some, hu₁]
    have hβ : stepw P X₀ β = some X₀ := by simp only [β, stepw, h₂, Option.bind_some, hu₂]
    set A := rep β.length α
    set B := rep α.length β
    have hA : stepw P X₀ A = some X₀ := stepw_rep hα _
    have hB : stepw P X₀ B = some X₀ := stepw_rep hβ _
    have hlen : A.length = B.length := by simp only [A, B, rep_length]; ring
    have hL : 0 < A.length := by simp [A, rep_length, α, β]
    have hAB : A ≠ B := by
      intro e
      have e' := congrArg List.head? e
      have hA' : A = α ++ rep u₂.length α := by
        simp only [A, β, List.length_cons]; exact rep_succ _ _
      have hB' : B = β ++ rep u₁.length β := by
        simp only [B, α, List.length_cons]; exact rep_succ _ _
      rw [hA', hB'] at e'
      simp [α, β] at e'
      exact hne e'
    set L := A.length
    obtain ⟨u₀, hu₀⟩ := stepw_of_reach hX₀
    set t := hseq A B
    have hblk : ∀ k, stepw P X₀ (pre t (k * L)) = some X₀ := by
      intro k
      induction k with
      | zero => simp [pre, stepw]
      | succ k ih =>
        have e : pre t ((k + 1) * L) = pre t (k * L) ++ hblk A B k := by
          rw [show (k + 1) * L = k * L + L by ring, pre_add]
          congr 1
          refine List.ext_getElem (by rw [List.length_map, List.length_range, hblk_length hlen])
            fun i h1 h2 => ?_
          simp only [List.length_map, List.length_range] at h1
          simp only [List.getElem_map, List.getElem_range]
          rw [show t (k * L + i) = (hblk A B k).getD i 0 from hseq_at hL k h1,
            List.getD_eq_getElem _ _ (by rw [hblk_length hlen]; exact h1)]
        rw [e, stepw_append, ih]
        rcases hblk_cases (w₁ := A) (w₂ := B) k with e | e <;> rw [e]
        · exact hA
        · exact hB
    refine ⟨app u₀ t, fun m => ?_, fun hp => ?_⟩
    · refine adm_mono (m := u₀.length + m * L) (by nlinarith) ?_
      rw [pre_app, stepw_append, hu₀]
      simp [hblk m]
    · refine hseq_not_periodic hL hlen hAB ?_
      have := shift_of_periodic u₀.length hp
      have e : (fun n => app u₀ t (n + u₀.length)) = t := funext fun n => by simp [app]
      rwa [e] at this
  · obtain ⟨s, X, h0, hX, hinj⟩ := exists_injective_path hF hfin
    have hs : ∀ m, stepw P (root P) (pre s m) = some (X m) := by
      intro m
      induction m with
      | zero => rw [h0]; rfl
      | succ m ih => rw [stepw_pre_succ, ih]; exact hX m
    exact ⟨s, fun m => by rw [hs]; rfl, fun hp => not_injective_of_periodic hF h0 hX hp hinj⟩

/-! ## The limit orbit -/

section Limit

variable {s : ℕ → ℤ}

theorem exists_state (hs : Adm P s) (N : ℕ) : ∃ X, stepw P (root P) (pre s N) = some X :=
  Option.isSome_iff_exists.1 (hs N)

/-- The lower endpoint of the state after the first `N` letters. -/
noncomputable def lof (hs : Adm P s) (N : ℕ) : ℚ := (Classical.choose (exists_state hs N)).lo

theorem lof_succ (hs : Adm P s) (N : ℕ) : fw P.p P.q P.a P.b (s N) (lof hs N) ≤ lof hs (N + 1) := by
  unfold lof
  have h1 := Classical.choose_spec (exists_state hs N)
  have h2 := Classical.choose_spec (exists_state hs (N + 1))
  set X := Classical.choose (exists_state hs N)
  set Y := Classical.choose (exists_state hs (N + 1))
  clear_value X Y
  rw [stepw_pre_succ, h1, Option.bind_some] at h2
  have := (step_facts h2).2.2.1
  simp only [istep, Prod.mk.injEq] at this
  rw [this.1]
  exact le_max_right _ _

/-- Backward realizations of the prefixes, ending at the lower endpoint. -/
theorem exists_back (hs : Adm P s) (hF : ParamFacts P) : ∃ ys : ℕ → ℕ → ℚ, ∀ N,
    ys N N = lof hs N ∧ (∀ i ≤ N, 0 ≤ ys N i ∧ ys N i < 1) ∧
    ∀ i < N, ys N (i + 1) = fw P.p P.q P.a P.b (s i) (ys N i) := by
  have hp0 : (0 : ℚ) < P.p := by exact_mod_cast (by have := hF.pq; omega : 0 < P.p)
  have hq0 : (0 : ℚ) < P.q := by exact_mod_cast (by have := hF.q1; omega : 0 < P.q)
  have h : ∀ N, ∃ ys : ℕ → ℚ, ys N = lof hs N ∧ (∀ i ≤ N, 0 ≤ ys i ∧ ys i < 1) ∧
      ∀ i < N, ys (i + 1) = fw P.p P.q P.a P.b (s i) (ys i) := by
    intro N
    set X := Classical.choose (exists_state hs N)
    have hX : stepw P (root P) (pre s N) = some X := Classical.choose_spec (exists_state hs N)
    have hI := stepw_interval (P := P) (pre s N) hX
    have hlt : X.lo < X.hi := by
      cases N with
      | zero =>
        simp only [pre, List.range_zero, List.map_nil, stepw, Option.some.injEq] at hX
        rw [← hX]; simp [root]
      | succ N => exact (stepw_bounds (P := P) (pre s (N + 1)) (by simp [pre]) hX).2.1
    obtain ⟨ys, hyL, -, -, hys, hrec⟩ := realize (a := P.a) (b := P.b) hp0 hq0 (pre s N)
      ((root P).lo, (root P).hi) le_rfl le_rfl X.lo (by rw [hI]) (by rw [hI]; exact hlt)
    rw [pre_length] at hyL hys hrec
    exact ⟨ys, hyL, hys, fun i hi => by rw [hrec i hi, pre_getD s hi]⟩
  choose ys hys using h
  exact ⟨ys, hys⟩

/-- The real affine branch `y ↦ (p·y − s − (p−q)·a/b)/q`. -/
noncomputable def fR (P : Params) (s : ℤ) (y : ℝ) : ℝ :=
  (P.p : ℝ) / P.q * y + (-(s : ℝ) - ((P.p : ℝ) - P.q) * P.a / P.b) / P.q

theorem fR_cast (hF : ParamFacts P) (s : ℤ) (y : ℚ) :
    ((fw P.p P.q P.a P.b s y : ℚ) : ℝ) = fR P s y := by
  rw [fw_eq hF]
  simp only [fR]
  push_cast
  ring

variable {hs : Adm P s} {ys : ℕ → ℕ → ℚ}
  (hys : ∀ N, ys N N = lof hs N ∧ (∀ i ≤ N, 0 ≤ ys N i ∧ ys N i < 1) ∧
    ∀ i < N, ys N (i + 1) = fw P.p P.q P.a P.b (s i) (ys N i))
include hys

/-- The backward realizations increase with the length of the prefix. -/
theorem back_mono (hF : ParamFacts P) : ∀ j i N, i + j = N → ys N i ≤ ys (N + 1) i := by
  have hp0 : (0 : ℚ) < P.p := by exact_mod_cast (by have := hF.pq; omega : 0 < P.p)
  have hq0 : (0 : ℚ) < P.q := by exact_mod_cast (by have := hF.q1; omega : 0 < P.q)
  intro j
  induction j with
  | zero =>
    intro i N h
    subst h
    rw [Nat.add_zero]
    by_contra hc
    push Not at hc
    have h1 := fw_lt (a := P.a) (b := P.b) hp0 hq0 (s i) hc
    rw [← (hys (i + 1)).2.2 i (by omega), (hys (i + 1)).1, (hys i).1] at h1
    have := lof_succ hs i
    linarith
  | succ j ih =>
    intro i N h
    by_contra hc
    push Not at hc
    have h1 := fw_lt (a := P.a) (b := P.b) hp0 hq0 (s i) hc
    rw [← (hys (N + 1)).2.2 i (by omega), ← (hys N).2.2 i (by omega)] at h1
    have := ih (i + 1) N (by omega)
    linarith

/-- `v i N`: the time-`i` value of the realization of the first `i + N` letters. -/
noncomputable def vv (ys : ℕ → ℕ → ℚ) (i N : ℕ) : ℝ := (ys (i + N) i : ℝ)

/-- **The limit orbit**: the supremum of the backward realizations. -/
noncomputable def ystar (ys : ℕ → ℕ → ℚ) (i : ℕ) : ℝ := ⨆ N, vv ys i N

omit hys in
theorem vv_bdd (hys : ∀ N, ys N N = lof hs N ∧ (∀ i ≤ N, 0 ≤ ys N i ∧ ys N i < 1) ∧
    ∀ i < N, ys N (i + 1) = fw P.p P.q P.a P.b (s i) (ys N i)) (i N : ℕ) :
    0 ≤ vv ys i N ∧ vv ys i N < 1 := by
  obtain ⟨h0, h1⟩ := (hys (i + N)).2.1 i (by omega)
  exact ⟨by simp only [vv]; exact_mod_cast h0, by simp only [vv]; exact_mod_cast h1⟩

theorem vv_mono (hF : ParamFacts P) (i N : ℕ) : vv ys i N ≤ vv ys i (N + 1) := by
  simp only [vv]
  exact_mod_cast (show ys (i + N) i ≤ ys (i + (N + 1)) i by
    rw [show i + (N + 1) = i + N + 1 by ring]; exact back_mono hys hF N i (i + N) rfl)

theorem bdd_vv (i : ℕ) : BddAbove (Set.range (vv ys i)) :=
  ⟨1, by rintro _ ⟨N, rfl⟩; exact (vv_bdd hys i N).2.le⟩

theorem le_ystar (i N : ℕ) : vv ys i N ≤ ystar ys i := le_ciSup (bdd_vv hys i) N

theorem ystar_nonneg (i : ℕ) : 0 ≤ ystar ys i := (vv_bdd hys i 0).1.trans (le_ystar hys i 0)

theorem ystar_le_one (i : ℕ) : ystar ys i ≤ 1 := ciSup_le fun N => (vv_bdd hys i N).2.le

theorem vv_succ (hF : ParamFacts P) (i N : ℕ) : vv ys (i + 1) N = fR P (s i) (vv ys i (N + 1)) := by
  simp only [vv]
  rw [show i + 1 + N = i + (N + 1) by ring, (hys (i + (N + 1))).2.2 i (by omega), fR_cast hF]

/-- The limit orbit follows the word. -/
theorem ystar_succ (hF : ParamFacts P) (i : ℕ) : ystar ys (i + 1) = fR P (s i) (ystar ys i) := by
  have hc : (0 : ℝ) ≤ (P.p : ℝ) / P.q := by positivity
  have hshift : ⨆ N, vv ys i (N + 1) = ystar ys i := le_antisymm
    (ciSup_le fun N => le_ystar hys i (N + 1))
    (ciSup_le fun N => (vv_mono hys hF i N).trans
      (le_ciSup (f := fun N => vv ys i (N + 1)) ⟨1, by
        rintro _ ⟨N, rfl⟩; exact (vv_bdd hys i (N + 1)).2.le⟩ N))
  have hcont : Continuous (fR P (s i)) := by
    unfold fR; fun_prop
  have hmono : Monotone (fR P (s i)) := fun a b h => by
    unfold fR; gcongr
  have := hmono.map_ciSup_of_continuousAt (g := fun N => vv ys i (N + 1)) hcont.continuousAt
    ⟨1, by rintro _ ⟨N, rfl⟩; exact (vv_bdd hys i (N + 1)).2.le⟩
  rw [hshift] at this
  rw [this]
  simp only [ystar, vv_succ hys hF]

/-- After a hit of `1`, the limit orbit is approached strictly from below. -/
theorem lt_ystar_of_hit (hF : ParamFacts P) {k : ℕ} (hk : ystar ys k = 1) :
    ∀ j N, vv ys (k + j) N < ystar ys (k + j) := by
  have hc : (0 : ℝ) < (P.p : ℝ) / P.q := by
    have := hF.q1; have := hF.pq
    have : (0 : ℝ) < P.p := by exact_mod_cast (by omega : 0 < P.p)
    positivity
  intro j
  induction j with
  | zero => intro N; rw [add_zero, hk]; exact (vv_bdd hys k N).2
  | succ j ih =>
    intro N
    rw [← add_assoc, vv_succ hys hF, ystar_succ hys hF]
    simp only [fR]
    have := ih (N + 1)
    nlinarith

theorem ystar_pos_of_hit (hF : ParamFacts P) {k : ℕ} (hk : ystar ys k = 1) (j : ℕ) :
    0 < ystar ys (k + j) :=
  (vv_bdd hys (k + j) 0).1.trans_lt (lt_ystar_of_hit hys hF hk j 0)

/-- The limit orbit in integer form: `q·(b·y') = p·(b·y) − b·s − (p−q)·a`. -/
theorem ystar_rec (hF : ParamFacts P) (n : ℕ) :
    (P.q : ℝ) * (P.b * ystar ys (n + 1)) =
      P.p * (P.b * ystar ys n) - (P.b * s n + ((P.p : ℝ) - P.q) * P.a) := by
  have hq : (P.q : ℝ) ≠ 0 := by have := hF.q1; positivity
  have hb : (P.b : ℝ) ≠ 0 := by have := hF.b0; positivity
  rw [ystar_succ hys hF]
  simp only [fR]
  field_simp
  ring

/-- **Between two hits of `1`, the values `b·y*` are integers** (a `q`-adic argument). -/
theorem int_of_hits (hF : ParamFacts P) {k k' : ℕ} (hk : ystar ys k = 1) (hk' : ystar ys k' = 1)
    (hkk : k ≤ k') : ∀ n, k ≤ n → n ≤ k' → ∃ m : ℤ, (P.b : ℝ) * ystar ys n = m := by
  -- `T j`: the integer shift at time `k + j`; `Nn j = q^j · b · y*(k + j)`
  set T : ℕ → ℤ := fun j => P.b * s (k + j) + ((P.p : ℤ) - P.q) * P.a
  let Nn : ℕ → ℤ := fun j => Nat.rec (P.b : ℤ) (fun j N => P.p * N - P.q ^ j * T j) j
  have hN : ∀ j, ((P.q : ℝ) ^ j * (P.b * ystar ys (k + j))) = Int.cast (Nn j) := by
    intro j
    induction j with
    | zero => simp [Nn, hk]
    | succ j ih =>
      have e := ystar_rec hys hF (k + j)
      show (P.q : ℝ) ^ (j + 1) * (P.b * ystar ys (k + j + 1)) =
        (((P.p : ℤ) * Nn j - (P.q : ℤ) ^ j * T j : ℤ) : ℝ)
      push_cast
      rw [← ih, pow_succ, mul_assoc, e]
      simp only [T]
      push_cast
      ring
  have hcong : ∀ j m, Nn (j + m) ≡ P.p ^ m * Nn j [ZMOD (P.q : ℤ) ^ j] := by
    intro j m
    induction m with
    | zero => simp
    | succ m ih =>
      show (P.p : ℤ) * Nn (j + m) - P.q ^ (j + m) * T (j + m) ≡ _ [ZMOD _]
      have hd : ((P.q : ℤ) ^ j) ∣ P.q ^ (j + m) * T (j + m) :=
        (pow_dvd_pow _ (by omega)).mul_right _
      calc (P.p : ℤ) * Nn (j + m) - P.q ^ (j + m) * T (j + m)
          ≡ P.p * Nn (j + m) - 0 [ZMOD (P.q : ℤ) ^ j] :=
            Int.ModEq.sub_left _ ((Int.modEq_zero_iff_dvd).2 hd)
        _ ≡ P.p * (P.p ^ m * Nn j) [ZMOD (P.q : ℤ) ^ j] := by
            rw [sub_zero]; exact ih.mul_left _
        _ = P.p ^ (m + 1) * Nn j := by ring
  intro n hn hn'
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (show j ≤ k' - k by omega)
  have hL : Nn (k' - k) = P.q ^ (k' - k) * P.b := by
    have := hN (k' - k)
    rw [show k + (k' - k) = k' by omega, hk', mul_one] at this
    exact_mod_cast this.symm
  have hdvd : ((P.q : ℤ) ^ j) ∣ Nn j := by
    have h1 := hcong j m
    rw [← hm, hL] at h1
    have h2 : ((P.q : ℤ) ^ j) ∣ P.p ^ m * Nn j := by
      have h3 : ((P.q : ℤ) ^ j) ∣ P.q ^ (k' - k) * P.b := (pow_dvd_pow _ (by omega)).mul_right _
      simpa using dvd_add h1.dvd h3
    have hcop : IsCoprime ((P.q : ℤ) ^ j) ((P.p : ℤ) ^ m) := by
      apply IsCoprime.pow
      rw [Int.isCoprime_iff_gcd_eq_one]
      exact_mod_cast Nat.Coprime.symm hF.cop
    exact hcop.dvd_of_dvd_mul_left h2
  obtain ⟨c, hc⟩ := hdvd
  refine ⟨c, ?_⟩
  have hq : (P.q : ℝ) ^ j ≠ 0 := by have := hF.q1; positivity
  have := hN j
  rw [hc] at this
  push_cast at this
  exact mul_left_cancel₀ hq this

/-- **With `gcd(q, b) = 1`, an integer value of `b·y*` determines the next one and the letter**
(among next values in `(0, b]`). -/
theorem det_step (hF : ParamFacts P) (hcop : Nat.Coprime P.q P.b) {n n' : ℕ} {z z' w w' : ℤ}
    (hz : (P.b : ℝ) * ystar ys n = z) (hz' : (P.b : ℝ) * ystar ys n' = z')
    (hw : (P.b : ℝ) * ystar ys (n + 1) = w) (hw' : (P.b : ℝ) * ystar ys (n' + 1) = w')
    (hw0 : 0 < w) (hwb : w ≤ P.b) (hw0' : 0 < w') (hwb' : w' ≤ P.b) (he : z = z') :
    w = w' ∧ s n = s n' := by
  have e1 := ystar_rec hys hF n
  have e2 := ystar_rec hys hF n'
  rw [hz, hw] at e1
  rw [hz', hw'] at e2
  have i1 : (P.q : ℤ) * w = P.p * z - (P.b * s n + ((P.p : ℤ) - P.q) * P.a) := by exact_mod_cast e1
  have i2 : (P.q : ℤ) * w' = P.p * z' - (P.b * s n' + ((P.p : ℤ) - P.q) * P.a) := by
    exact_mod_cast e2
  have hd : (P.b : ℤ) ∣ P.q * (w - w') := ⟨s n' - s n, by rw [mul_sub, i1, i2, he]; ring⟩
  have hcop' : IsCoprime (P.b : ℤ) P.q := by
    rw [Int.isCoprime_iff_gcd_eq_one]; exact_mod_cast hcop.symm
  obtain ⟨c, hc⟩ := hcop'.dvd_of_dvd_mul_left hd
  have hb : (0 : ℤ) < P.b := by exact_mod_cast hF.b0
  have hc0 : c = 0 := by
    by_contra hc0
    rcases lt_or_gt_of_ne hc0 with h | h
    · nlinarith
    · nlinarith
  rw [hc0, mul_zero, sub_eq_zero] at hc
  refine ⟨hc, ?_⟩
  rw [hc, he] at i1
  have : (P.b : ℤ) * s n = P.b * s n' := by linarith
  exact mul_left_cancel₀ hb.ne' this

/-- **An aperiodic admissible word hits `1` only finitely often**, case `gcd(q, b) = 1`. -/
theorem hits_finite_cop (hF : ParamFacts P) (hcop : Nat.Coprime P.q P.b)
    (hap : ¬ IsEventuallyPeriodic s) : ∃ N, ∀ n, N ≤ n → ystar ys n < 1 := by
  by_contra hc
  push Not at hc
  have hit : ∀ N, ∃ n, N ≤ n ∧ ystar ys n = 1 := fun N => by
    obtain ⟨n, hn, h1⟩ := hc N
    exact ⟨n, hn, le_antisymm (ystar_le_one hys n) h1⟩
  obtain ⟨k₀, -, hk₀⟩ := hit 0
  have hb : (0 : ℝ) < P.b := by exact_mod_cast hF.b0
  have hint : ∀ n, k₀ ≤ n → ∃ z : ℤ, (P.b : ℝ) * ystar ys n = z ∧ 0 < z ∧ z ≤ P.b := by
    intro n hn
    obtain ⟨k', hk'n, hk'⟩ := hit n
    obtain ⟨z, hz⟩ := int_of_hits hys hF hk₀ hk' (by omega) n hn hk'n
    refine ⟨z, hz, ?_, ?_⟩
    · have := ystar_pos_of_hit hys hF hk₀ (n - k₀)
      rw [show k₀ + (n - k₀) = n by omega] at this
      have : (0 : ℝ) < z := by rw [← hz]; positivity
      exact_mod_cast this
    · have := ystar_le_one hys n
      have : (z : ℝ) ≤ P.b := by rw [← hz]; nlinarith
      exact_mod_cast this
  choose! zi hzi using hint
  have key : ∀ a b, k₀ ≤ a → a < b → zi a = zi b → IsEventuallyPeriodic s := by
    intro a b ha hab he
    have hz : ∀ j, zi (a + j) = zi (b + j) := by
      intro j
      induction j with
      | zero => exact he
      | succ j ih =>
        obtain ⟨h1, -, -⟩ := hzi (a + j) (by omega)
        obtain ⟨h2, -, -⟩ := hzi (b + j) (by omega)
        obtain ⟨h3, h3a, h3b⟩ := hzi (a + j + 1) (by omega)
        obtain ⟨h4, h4a, h4b⟩ := hzi (b + j + 1) (by omega)
        exact (det_step hys hF hcop h1 h2 h3 h4 h3a h3b h4a h4b ih).1
    refine ⟨a, b - a, by omega, fun k hk => ?_⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    obtain ⟨h1, -, -⟩ := hzi (a + j) (by omega)
    obtain ⟨h2, -, -⟩ := hzi (b + j) (by omega)
    obtain ⟨h3, h3a, h3b⟩ := hzi (a + j + 1) (by omega)
    obtain ⟨h4, h4a, h4b⟩ := hzi (b + j + 1) (by omega)
    rw [show a + j + (b - a) = b + j by omega]
    exact (det_step hys hF hcop h1 h2 h3 h4 h3a h3b h4a h4b (hz j)).2.symm
  obtain ⟨n₁, hn₁, n₂, hn₂, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.Icc k₀ (k₀ + P.b)) (t := Finset.Icc (1 : ℤ) P.b) (by simp; omega) (f := zi) (by
      intro n hn
      obtain ⟨-, h0, hb'⟩ := hzi n (Finset.mem_Icc.1 hn).1
      exact Finset.mem_Icc.2 ⟨by omega, hb'⟩)
  have h1 := (Finset.mem_Icc.1 hn₁).1
  have h2 := (Finset.mem_Icc.1 hn₂).1
  rcases lt_or_gt_of_ne hne with h | h
  · exact hap (key n₁ n₂ h1 h heq)
  · exact hap (key n₂ n₁ h2 h heq.symm)

/-- **Two hits of `1` force `gcd(q, b) ∣ a`**: after a hit, `q·(b·y*) = p·b − b·s − (p−q)·a` with
`b·y*` an integer, and `gcd(p, q) = 1`. -/
theorem gcd_dvd_of_two_hits (hF : ParamFacts P) {k k' : ℕ} (hk : ystar ys k = 1)
    (hk' : ystar ys k' = 1) (hkk : k < k') : Nat.gcd P.q P.b ∣ P.a.natAbs := by
  obtain ⟨w, hw⟩ := int_of_hits hys hF hk hk' hkk.le (k + 1) (by omega) hkk
  have e := ystar_rec hys hF k
  rw [hk, hw, mul_one] at e
  have i : (P.q : ℤ) * w = P.p * P.b - (P.b * s k + ((P.p : ℤ) - P.q) * P.a) := by
    exact_mod_cast e
  set g := Nat.gcd P.q P.b
  have hgq : (g : ℤ) ∣ P.q := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left _ _)
  have hgb : (g : ℤ) ∣ P.b := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right _ _)
  have h1 : (g : ℤ) ∣ P.p * P.a := by
    have : (P.p : ℤ) * P.a = P.p * P.b - P.b * s k + P.q * P.a - P.q * w := by
      linear_combination i
    rw [this]
    exact dvd_sub (dvd_add (dvd_sub (hgb.mul_left _) (hgb.mul_right _)) (hgq.mul_right _))
      (hgq.mul_right _)
  have hgp : IsCoprime (g : ℤ) P.p := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact_mod_cast Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _) (Nat.Coprime.symm hF.cop)
  exact Int.natCast_dvd.1 (hgp.dvd_of_dvd_mul_left h1)

/-- **An aperiodic admissible word hits `1` only finitely often**, when `gcd(q, b)` is prime to
`a` (for instance when `gcd(q, b) = 1`, or when `ν = a/b` is in lowest terms).  If `gcd(q, b) > 1`
there is at most one hit (`gcd_dvd_of_two_hits`). -/
theorem hits_finite (hF : ParamFacts P) (hg : Nat.Coprime (Nat.gcd P.q P.b) P.a.natAbs)
    (hap : ¬ IsEventuallyPeriodic s) : ∃ N, ∀ n, N ≤ n → ystar ys n < 1 := by
  by_cases hcop : Nat.Coprime P.q P.b
  · exact hits_finite_cop hys hF hcop hap
  by_contra hc
  push Not at hc
  obtain ⟨k, -, hk⟩ := hc 0
  obtain ⟨k', hk'k, hk'⟩ := hc (k + 1)
  exact hcop (Nat.Coprime.eq_one_of_dvd hg (gcd_dvd_of_two_hits hys hF
    (le_antisymm (ystar_le_one hys k) hk) (le_antisymm (ystar_le_one hys k') hk') (by omega)))

end Limit

/-! ## From admissible words to pseudo-orbits -/

theorem rs_lt (hF : ParamFacts P) {r₀ : ℕ} (hr₀ : r₀ < P.M) (s : ℕ → ℤ) :
    ∀ m, rs P r₀ s m < P.M
  | 0 => hr₀
  | _ + 1 => rnext_lt hF _ _

/-- A residue that survives every prefix of an admissible word (König on the residues). -/
theorem exists_res (hF : ParamFacts P) {s : ℕ → ℤ} (hs : Adm P s) :
    ∃ r₀ < P.M, ∀ m, (rpath P r₀ (pre s m)).isSome := by
  obtain ⟨r, hr, h⟩ := exists_forall_of_antitone (N := P.M)
    (Q := fun r m => (rpath P r (pre s m)).isSome)
    (fun r m m' hm h => by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
      rw [pre_add, rpath_append] at h
      cases h' : rpath P r (pre s m') <;> simp_all)
    (fun m => by
      obtain ⟨X, hX⟩ := exists_state hs m
      have hne : X.R.Nonempty := by
        cases m with
        | zero =>
          simp only [pre, List.range_zero, List.map_nil, stepw, Option.some.injEq] at hX
          rw [← hX]
          exact ⟨0, by simp [root, hF.M0]⟩
        | succ m =>
          rw [stepw_pre_succ, Option.bind_eq_some_iff] at hX
          obtain ⟨Z, -, hZ⟩ := hX
          exact step_R_nonempty hZ
      obtain ⟨r', hr'⟩ := hne
      obtain ⟨r, hr, hp⟩ := stepw_pre (P := P) (pre s m) hX hr'
      exact ⟨r, by simpa [root] using hr, by rw [hp]; rfl⟩)
  exact ⟨r, hr, h⟩

/-- **An aperiodic admissible word yields an aperiodic avoiding pseudo-orbit** (`gcd(q, b)` prime
to `a`): a tail of its limit orbit, past the last hit of `1`. -/
theorem exists_aperiodic_pseudoOrbit (hF : ParamFacts P)
    (hg : Nat.Coprime (Nat.gcd P.q P.b) P.a.natAbs)
    {s : ℕ → ℤ} (hs : Adm P s) (hap : ¬ IsEventuallyPeriodic s) :
    ∃ r y s', PseudoOrbit P r y s' ∧ ¬ IsEventuallyPeriodic s' := by
  obtain ⟨ys, hys⟩ := exists_back hs hF
  obtain ⟨N₀, hN₀⟩ := hits_finite hys hF hg hap
  obtain ⟨r₀, hr₀, hres⟩ := exists_res hF hs
  have hok : ∀ i, rOK P (rs P r₀ s i) (s i) = true := fun i => by
    obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.1 (hres (i + 1))
    exact (rpath_pre s r₀ (i + 1) hr').2 i (by omega)
  have hsok : ∀ i, sOK P (s i) = true := fun i => by
    obtain ⟨X, hX⟩ := exists_state hs (i + 1)
    exact stepw_sOK (P := P) (pre s (i + 1)) hX (s i)
      (by simp only [pre, List.mem_map, List.mem_range]; exact ⟨i, by omega, rfl⟩)
  refine ⟨fun n => rs P r₀ s (N₀ + n), fun n => ystar ys (N₀ + n), fun n => s (N₀ + n),
    ⟨fun n => rs_lt hF hr₀ s _, fun n => ystar_nonneg hys _, fun n => hN₀ _ (by omega),
      fun n => ?_, fun n => rfl, fun n l hl => ?_, fun n l hl => ?_⟩, fun hp => ?_⟩
  · show (s (N₀ + n) : ℝ) * P.b = P.p * P.b * ystar ys (N₀ + n) -
      P.q * P.b * ystar ys (N₀ + n + 1) - ((P.p : ℝ) - P.q) * P.a
    linear_combination ystar_rec hys hF (N₀ + n)
  · have := hok (N₀ + n)
    simp only [rOK, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at this
    exact this.1 l hl
  · have := hsok (N₀ + n)
    simp only [sOK, List.all_eq_true, bne_iff_ne, ne_eq] at this
    exact this l hl
  · apply hap
    apply periodic_of_shift (k := N₀)
    simpa only [add_comm] using hp

/-! ## Lowest terms

The follower automaton and the pseudo-orbits see the shift only through `ν = a/b`, so `P` may be
replaced by `red P`, with `ν` in lowest terms; there `gcd(q, b)` is prime to `a`. -/

/-- The shift `ν = a/b` in lowest terms. -/
def red (P : Params) : Params :=
  { P with a := P.a / (Int.gcd P.a P.b : ℤ), b := P.b / Int.gcd P.a P.b }

theorem gcd_red_pos (hF : ParamFacts P) : 0 < Int.gcd P.a P.b :=
  Int.gcd_pos_of_ne_zero_right _ (by exact_mod_cast hF.b0.ne')

theorem red_a (P : Params) : (red P).a * (Int.gcd P.a P.b : ℤ) = P.a :=
  Int.ediv_mul_cancel (Int.gcd_dvd_left _ _)

theorem red_b (P : Params) : (red P).b * Int.gcd P.a P.b = P.b :=
  Nat.div_mul_cancel (by exact_mod_cast (Int.gcd_dvd_right P.a P.b : _ ∣ (P.b : ℤ)))

theorem red_b_pos (hF : ParamFacts P) : 0 < (red P).b := by
  have h := red_b P
  have := hF.b0
  rcases Nat.eq_zero_or_pos (red P).b with h0 | h0
  · rw [h0, zero_mul] at h; omega
  · exact h0

/-- `red P` has `gcd(q, b)` prime to `a`. -/
theorem coprime_red (hF : ParamFacts P) :
    Nat.Coprime (Nat.gcd (red P).q (red P).b) (red P).a.natAbs := by
  have h : Int.gcd (red P).a ((red P).b : ℤ) = 1 := by
    have := Int.gcd_div_gcd_div_gcd (gcd_red_pos (P := P) hF)
    simpa [red, Int.natCast_div] using this
  exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _) (Nat.Coprime.symm h)

theorem paramFacts_red (hF : ParamFacts P) : ParamFacts (red P) := by
  obtain ⟨d, hd, ha, hb⟩ : ∃ d : ℤ, 0 < d ∧ (red P).a * d = P.a ∧ ((red P).b : ℤ) * d = P.b :=
    ⟨_, by exact_mod_cast gcd_red_pos hF, red_a P, by exact_mod_cast red_b P⟩
  refine ⟨hF.q1, hF.pq, hF.cop, red_b_pos hF, hF.D0, hF.M0, hF.inv, hF.PM, hF.Pq, ?_, ?_⟩
  · have h := hF.sLo
    rw [← ha, ← hb] at h
    show ((red P).b : ℤ) * (P.sLo - 1) ≤ -((P.q : ℤ) * (red P).b) - ((P.p : ℤ) - P.q) * (red P).a
    by_contra hc
    push Not at hc
    nlinarith
  · have h := hF.sHi
    rw [← ha, ← hb] at h
    show (P.p : ℤ) * (red P).b - ((P.p : ℤ) - P.q) * (red P).a ≤ ((red P).b : ℤ) * (P.sLo + P.nA)
    by_contra hc
    push Not at hc
    nlinarith

theorem ratio_red (hF : ParamFacts P) : ((red P).a : ℚ) / (red P).b = (P.a : ℚ) / P.b := by
  have hd : (Int.gcd P.a P.b : ℚ) ≠ 0 := by exact_mod_cast (gcd_red_pos hF).ne'
  have ha : (P.a : ℚ) = (red P).a * Int.gcd P.a P.b := by exact_mod_cast (red_a P).symm
  have hb : (P.b : ℚ) = (red P).b * Int.gcd P.a P.b := by exact_mod_cast (red_b P).symm
  rw [ha, hb, mul_div_mul_right _ _ hd]

theorem step_red (hF : ParamFacts P) : step (red P) = step P := by
  have h : istep (red P).p (red P).q (red P).a (red P).b = istep P.p P.q P.a P.b := by
    funext I s
    simp only [istep, fw, mul_div_assoc, ratio_red hF]
    rfl
  funext X s
  simp only [step, istepX, h]
  rfl

theorem stepw_red (hF : ParamFacts P) : ∀ (u : List ℤ) X, stepw (red P) X u = stepw P X u
  | [], _ => rfl
  | s :: u, X => by simp only [stepw, step_red hF, stepw_red hF u]

theorem adm_red (hF : ParamFacts P) {s : ℕ → ℤ} (hs : Adm P s) : Adm (red P) s := fun m => by
  rw [show root (red P) = root P from rfl, stepw_red hF]
  exact hs m

/-- A pseudo-orbit of `red P` is one of `P`. -/
theorem pseudoOrbit_of_red {r : ℕ → ℕ} {y : ℕ → ℝ} {s : ℕ → ℤ}
    (h : PseudoOrbit (red P) r y s) : PseudoOrbit P r y s := by
  have ha : (P.a : ℝ) = (red P).a * Int.gcd P.a P.b := by exact_mod_cast (red_a P).symm
  have hb : (P.b : ℝ) = (red P).b * Int.gcd P.a P.b := by exact_mod_cast (red_b P).symm
  refine ⟨h.r_lt, h.y_nonneg, h.y_lt, fun n => ?_, h.rstep, h.r_av, h.s_av⟩
  have e : (s n : ℝ) * (red P).b = P.p * (red P).b * y n - P.q * (red P).b * y (n + 1) -
      ((P.p : ℝ) - P.q) * (red P).a := h.ident n
  rw [ha, hb]
  linear_combination (Int.gcd P.a P.b : ℝ) * e

/-! ## The literal T5(iv) -/

/-- **The literal T5(iv)**, for every cell: some cell count certifies iff every avoiding
pseudo-orbit is eventually periodic. -/
@[category research solved, AMS 11 37, ref "Oda26", group "dubc2_obstruction"]
theorem T5iv_literal (hP : checkParams P = true) :
    (∃ D C, Checked { P with D := D } C) ↔
      ∀ r y s, PseudoOrbit P r y s → IsEventuallyPeriodic s := by
  have hF := paramFacts hP
  constructor
  · rintro ⟨D, C, hc⟩ r y s h
    have h' : PseudoOrbit { P with D := D } r y s :=
      ⟨h.r_lt, h.y_nonneg, h.y_lt, h.ident, h.rstep, h.r_av, h.s_av⟩
    exact PseudoOrbit.eventuallyPeriodic hc h'
  · intro h
    by_contra hno
    have hnot : ¬ ({X | Reach P (root P) X}.Finite ∧ ∀ X, Reach P (root P) X → ¬ Branching P X) :=
      fun ⟨hfin, hnb⟩ => hno ⟨_, _, exists_checked_DF hP hfin hnb |>.choose_spec⟩
    obtain ⟨s, hs, hap⟩ := exists_aperiodic_adm hP hnot
    obtain ⟨r, y, s', hpo, hap'⟩ :=
      exists_aperiodic_pseudoOrbit (paramFacts_red hF) (coprime_red hF) (adm_red hF hs) hap
    exact hap' (h r y s' (pseudoOrbit_of_red hpo))

end Follower

end DubC2.Gen
