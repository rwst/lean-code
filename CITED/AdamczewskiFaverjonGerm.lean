/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import CITED.AdamczewskiFaverjonDictionary
import Corpus.Util.Attributes.Basic
import Corpus.Util.Attributes.Database

/-!
# [AF22] §2.3.1, the germ realization: from Lemma 2.7 to `hEp`

plan-formalize-AF17's **WP12(b)**, the second of the two realization maps that WP11 left as
hypotheses.  `CITED/AdamczewskiFaverjonDictionary` discharged `hreal`, `hsum`, `hmaj` and — granted
one hypothesis — `htail`, leaving Step (UB) with exactly one piece of mathematics outstanding:

  `hEp` :  `E_p(Θ_k(z), z^{q^{k-k₀}}) = 0`   for `k ≥ k₀` and `z` on the circle.

`E_p` is the truncation of the auxiliary series, `Θ_k(z) = a·Φ(z)·A_{k-k₀}(z)`, and the vanishing
is [AF22] Lemma 2.12 (`AF.exists_auxiliary`: `E_p(MY,z) ∈ 𝓘`) combined with [AF22] Lemma 2.7
(`AF.lemma_2_7`: a relation stays a relation under the twist `Y ↦ Y·A_k(z)`, `z ↦ z^{q^k}`).  Both
are already theorems of the corpus.  What separates them from `hEp` is that Lemma 2.7 is an
identity **in the abstract ambient field `Ω`**, while `hEp` is an identity **between complex
numbers**, one for each point `z` of the circle.  Bridging the two is what [AF22] call «reading
`φ(z)` as a matrix of analytic functions», and it is the last interface of Stage 2.

## What this file does

* `AF.IsBranchRealization` — the interface, and *only* the interface: a ring homomorphism
  `real : R →+* Germ l ℂ` out of a **subring** `R` of the ambient field into the germs of complex
  functions along a filter `l`, which realizes `K[z]` by the honest polynomial functions
  (transported by `φ : K →+* ℂ`) and the relation matrix `Φalg` by a given matrix `Ψ` of complex
  functions.  A homomorphism out of the ambient *field* cannot exist — `z - c` is a unit there and
  its realization vanishes — which is why the source is a subring; this is the same reason
  `AF.hspec_of_evalHom` is stated over a `Subring`.

* `AF.eventually_mvEvalC_branch_eq_zero` — **the transport**.  Given a branch realization and the
  two algebraic inputs, the auxiliary polynomial evaluated along the branch vanishes `l`-eventually.
  The proof is one chase through three ring homomorphisms: the twist of Lemma 2.7, the corestriction
  of `K[z] → Ω` to `R`, and `real` itself.  No analysis is used, and no property of `l`.

* `AF.mvEvalC_theta_eq_zero_of_branch` — the same statement with `l = 𝓟 U` and `Θ_k` spelled with
  `AF.theta`: this **is** `hEp`, for every `z` in `U`.

* `AF.eventually_norm_evalAt_le_exp_of_branch` — Step (UB) with `hEp` discharged: the capstone of
  `CITED/AdamczewskiFaverjonDictionary` with its last mathematical hypothesis replaced by the
  existence of a branch realization on a set containing the circle.

## The residue, stated exactly

What is **not** proved here is that a branch realization exists.  That is [AF22] Lemma 2.8 — «the
entries of `φ(z)` are algebraic functions, hence analytic at all but finitely many points, and
`det φ(ξ) ≠ 0` for `k₀ ≫ 1`» — and it is plan risk **R14**: Mathlib has no vanishing criterion for
the resultant, no convergent power series, and no analytic implicit function theorem for algebraic
function elements, so «an algebraic function element has an analytic branch on a small disc about a
non-critical point» is not available and is not cheap.  It is **not** axiomatized here: the
interface above is the precise statement that a future axiom, or a future proof, has to meet, and
every consumer *in this file* takes it as a hypothesis, so **this file adds no axiom to the AF
lane** — `#print axioms` shows `std3` on all of it.

It is axiomatized one layer up, in `CITED/AdamczewskiFaverjonBranchExistence`: `AF.lemma_2_8`
asserts the existence of an `AF.IsAnalyticBranch`, which is the interface below plus Lemma 2.8's
own two clauses (`Ψ` analytic on a disc, `Ψ(ξ)` the image of an invertible matrix over `K`).  That
file also derives from it Step (UB) with six further hypotheses gone.

The companion interface for §2.4 is unchanged: `AF.hspec_of_evalHom` still takes its evaluation
homomorphism `ev : R →+* K` — evaluation at the *algebraic* point `α`, with values in `K` — as a
hypothesis.  It is the same realization read at a point instead of along a branch.

## References

* [AF22] B. Adamczewski, C. Faverjon. *A new proof of Nishioka's theorem in Mahler's method.*
  arXiv:2210.14528 (2022), §2.2 (Lemma 2.7), §2.3.1 (Lemma 2.8, Remark 2.10), §2.3.2 ((2.9)).
* [AF17f] `plans/plan-formalize-AF17.html`: WP12(b), risk R14, milestone M4.
-/

open Filter Metric Topology MvPolynomial

open scoped Polynomial

namespace AF

/-! ## Matrices of functions, and their germs -/

section GermMat

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A function with matrix values, read as a matrix of functions. -/
@[category API, AMS 15, ref "AF22", group "af_mahler_alternative"]
noncomputable def funMat (f : ℂ → Matrix ι ι ℂ) : Matrix ι ι (ℂ → ℂ) :=
  Matrix.of fun i j z => f z i j

omit [DecidableEq ι] in
/-- Pointwise multiplication of matrices of functions is multiplication of the matrix values. -/
@[category API, AMS 15, ref "AF22", group "af_mahler_alternative"]
theorem funMat_mul (f g : ℂ → Matrix ι ι ℂ) :
    funMat (fun z => f z * g z) = funMat f * funMat g := by
  ext i j z
  simp [funMat, Matrix.mul_apply, Finset.sum_apply]

/-- **A matrix of complex functions, read as a matrix of germs along `l`.**  This is the target of
the branch realization: the ring in which the identity of [AF22] Lemma 2.7 is to be read. -/
@[category API, AMS 15 30, ref "AF22", group "af_mahler_alternative"]
noncomputable def germMat (l : Filter ℂ) (f : ℂ → Matrix ι ι ℂ) : Matrix ι ι (Germ l ℂ) :=
  (Germ.coeRingHom l).mapMatrix (funMat f)

@[category API, AMS 15 30, ref "AF22", group "af_mahler_alternative"]
theorem germMat_apply (l : Filter ℂ) (f : ℂ → Matrix ι ι ℂ) (i j : ι) :
    germMat l f i j = ((fun z : ℂ => f z i j : ℂ → ℂ) : Germ l ℂ) := rfl

@[category API, AMS 15 30, ref "AF22", group "af_mahler_alternative"]
theorem germMat_mul (l : Filter ℂ) (f g : ℂ → Matrix ι ι ℂ) :
    germMat l (fun z => f z * g z) = germMat l f * germMat l g := by
  rw [germMat, funMat_mul, map_mul, germMat, germMat]

end GermMat

/-! ## The coefficient homomorphism `K[z] → (ℂ → ℂ)` of the twist -/

section SubstFun

variable {K : Type*} [Field K]

/-- **The realization of the twisted coefficients**: `w ↦ (z ↦ φ(w)(z^n))`, as a ring homomorphism
into the ring of complex functions.  `n = q^k` is the Mahler substitution of [AF22] Lemma 2.7. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
noncomputable def substFun (φ : K →+* ℂ) (n : ℕ) : K[X] →+* (ℂ → ℂ) :=
  (Polynomial.eval₂RingHom (Pi.constRingHom ℂ ℂ) (fun z : ℂ => z ^ n)).comp
    (Polynomial.mapRingHom φ)

@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem evalRingHom_comp_substFun (φ : K →+* ℂ) (n : ℕ) (z : ℂ) :
    (Pi.evalRingHom (fun _ : ℂ => ℂ) z).comp (substFun φ n)
      = (Polynomial.evalRingHom (z ^ n)).comp (Polynomial.mapRingHom φ) := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · simp [substFun, Pi.constRingHom, Pi.evalRingHom]; rfl
  · simp [substFun, Pi.evalRingHom]; rfl

@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem substFun_apply (φ : K →+* ℂ) (n : ℕ) (w : K[X]) (z : ℂ) :
    substFun φ n w z = (w.map φ).eval (z ^ n) := by
  have h := DFunLike.congr_fun (evalRingHom_comp_substFun φ n z) w
  simpa using h

/-- The realization of a *polynomial* coefficient, i.e. the case `n = 1` read directly. -/
@[category API, AMS 11 13, ref "AF22", group "af_mahler_alternative"]
theorem substFun_eq_map_expand (φ : K →+* ℂ) (n : ℕ) (w : K[X]) :
    substFun φ n w = fun z : ℂ => ((substPow K n w).map φ).eval z := by
  funext z
  rw [substFun_apply, substPow_eq_expand, Polynomial.map_expand, Polynomial.expand_eval]

end SubstFun

/-! ## The substitution `Y ↦ MY`, evaluated through an arbitrary coefficient homomorphism -/

section SubMatEval

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **`AF.eval₂_subMat` with the coefficient map out of `K[z]` itself.**  The version in
`CITED/AdamczewskiFaverjonAuxiliary` needs a `K`-algebra structure on the target; the ambient field
`Ω` of [AF22] §2.2 carries one only through `K(z)`, so here the constant matrix `M` is transported
by the coefficient homomorphism directly. -/
@[category API, AMS 11 13 15, ref "AF22", group "af_mahler_alternative"]
theorem eval₂_subMat_polyHom {S : Type*} [CommRing S] (M : Matrix ι ι K) (f : K[X] →+* S)
    (x : Matrix ι ι S) (P : MvPolynomial (ι × ι) K[X]) :
    eval₂ f (fun s : ι × ι => x s.1 s.2) (subMat K[X] M P) =
      eval₂ f (fun s : ι × ι => ((M.map fun c => f (Polynomial.C c)) * x) s.1 s.2) P := by
  classical
  have h : (eval₂Hom f fun s : ι × ι => x s.1 s.2).comp (subMat K[X] M).toRingHom =
      eval₂Hom f fun s : ι × ι => ((M.map fun c => f (Polynomial.C c)) * x) s.1 s.2 := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun s => ?_)
    · simp
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, subMat_X, map_sum,
        map_mul, eval₂Hom_X', eval₂Hom_C]
      simp [Matrix.mul_apply, Matrix.map_apply, Polynomial.algebraMap_eq]
  exact DFunLike.congr_fun h P

end SubMatEval

/-! ## The branch realization -/

section BranchRealization

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra (RatFunc K) Ω]
variable {ι : Type*}

/-- **The germ realization of [AF22] §2.3.1, as an interface.**

`real` reads elements of a subring `R` of the ambient field as germs of complex functions along a
filter `l`, compatibly with the embedding `φ : K →+* ℂ` of the coefficients:

* every polynomial in `z` lies in `R` and is realized by the honest polynomial function;
* every entry of the relation matrix `Φalg` lies in `R` and is realized by the corresponding entry
  of a given matrix `Ψ` of complex functions.

That is all the transport of [AF22] Lemma 2.7 uses.  The source is a **subring**, not the field:
`z - c` is a unit of the ambient field, so no ring homomorphism out of the whole field can send it
to a function that vanishes somewhere — the same obstruction that `AF.hspec_of_evalHom` records
for evaluation at a point.

With `l = 𝓟 U` a germ is a function on `U` and the realization is a branch on `U`; with
`l = 𝓝 ξ` it is a germ at `ξ` in the usual sense.  Nothing below needs to know which. -/
@[category API, AMS 11 12 30, ref "AF22", group "af_mahler_alternative"]
structure IsBranchRealization (φ : K →+* ℂ) (l : Filter ℂ) (Φalg : Matrix ι ι Ω) (R : Subring Ω)
    (real : R →+* Germ l ℂ) (Ψ : ℂ → Matrix ι ι ℂ) : Prop where
  /-- Every polynomial in `z`, read in the ambient field, lies in the subring. -/
  poly_mem : ∀ w : K[X], toAmbient K Ω w ∈ R
  /-- …and is realized by the polynomial function with coefficients transported by `φ`. -/
  real_poly : ∀ w : K[X],
    real ⟨toAmbient K Ω w, poly_mem w⟩ = ((fun z : ℂ => (w.map φ).eval z : ℂ → ℂ) : Germ l ℂ)
  /-- Every entry of the relation matrix lies in the subring. -/
  mat_mem : ∀ i j, Φalg i j ∈ R
  /-- …and is realized by the corresponding entry of the analytic matrix `Ψ`. -/
  real_mat : ∀ i j,
    real ⟨Φalg i j, mat_mem i j⟩ = ((fun z : ℂ => Ψ z i j : ℂ → ℂ) : Germ l ℂ)

variable {φ : K →+* ℂ} {l : Filter ℂ} {Φalg : Matrix ι ι Ω} {R : Subring Ω}
  {real : R →+* Germ l ℂ} {Ψ : ℂ → Matrix ι ι ℂ}

/-- A matrix of polynomials, read inside the realization subring. -/
@[category API, AMS 11 15, ref "AF22", group "af_mahler_alternative"]
noncomputable def polyMatR (hmem : ∀ w : K[X], toAmbient K Ω w ∈ R) (B : Matrix ι ι K[X]) :
    Matrix ι ι R :=
  Matrix.of fun i j => ⟨toAmbient K Ω (B i j), hmem _⟩

/-- The relation matrix, read inside the realization subring. -/
@[category API, AMS 11 15, ref "AF22", group "af_mahler_alternative"]
noncomputable def relMatR (hmem : ∀ i j, Φalg i j ∈ R) : Matrix ι ι R :=
  Matrix.of fun i j => ⟨Φalg i j, hmem i j⟩

variable [Fintype ι] [DecidableEq ι]

@[category API, AMS 11 15, ref "AF22", group "af_mahler_alternative"]
theorem subtype_mapMatrix_polyMatR (hmem : ∀ w : K[X], toAmbient K Ω w ∈ R)
    (B : Matrix ι ι K[X]) :
    (Subring.subtype R).mapMatrix (polyMatR hmem B) = B.map (toAmbient K Ω) := by
  ext i j
  rfl

@[category API, AMS 11 15, ref "AF22", group "af_mahler_alternative"]
theorem subtype_mapMatrix_relMatR (hmem : ∀ i j, Φalg i j ∈ R) :
    (Subring.subtype R).mapMatrix (relMatR hmem) = Φalg := by
  ext i j
  rfl

@[category API, AMS 11 15 30, ref "AF22", group "af_mahler_alternative"]
theorem real_mapMatrix_polyMatR (h : IsBranchRealization φ l Φalg R real Ψ)
    (B : Matrix ι ι K[X]) :
    real.mapMatrix (polyMatR h.poly_mem B) = germMat l fun z => evalMat z (mapMat φ B) := by
  ext i j
  rw [germMat_apply]
  exact h.real_poly (B i j)

@[category API, AMS 11 15 30, ref "AF22", group "af_mahler_alternative"]
theorem real_mapMatrix_relMatR (h : IsBranchRealization φ l Φalg R real Ψ) :
    real.mapMatrix (relMatR h.mat_mem) = germMat l Ψ := by
  ext i j
  rw [germMat_apply]
  exact h.real_mat i j

/-- The realization of a matrix of *constants*: `Θ_k`'s normalizing factor `a = φ(M)`. -/
@[category API, AMS 11 15, ref "AF22", group "af_mahler_alternative"]
theorem evalMat_mapMat_map_C (M : Matrix ι ι K) (z : ℂ) :
    evalMat z (mapMat φ (M.map (Polynomial.C : K → K[X]))) = M.map φ := by
  ext i j
  simp [evalMat_apply, mapMat_apply, Matrix.map_apply]

end BranchRealization

/-! ## The transport: from [AF22] Lemma 2.7 to a vanishing of complex numbers -/

section Transport

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra (RatFunc K) Ω]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {φ : K →+* ℂ} {l : Filter ℂ} {Φalg : Matrix ι ι Ω} {R : Subring Ω}
  {real : R →+* Germ l ℂ} {Ψ : ℂ → Matrix ι ι ℂ}

/-- **WP12(b), the transport.**  A relation of the auxiliary kind — [AF22] Lemma 2.12's
`E_p(MY,z) ∈ 𝓘` — becomes, along a branch realization, the vanishing of a complex-valued function:

  `E_p(φ(M)·Ψ(z)·A_k(z), z^{q^k}) = 0`  for `l`-almost every `z`.

The proof composes three ring homomorphisms and uses no analysis:

1. [AF22] Lemma 2.7 (`AF.lemma_2_7`) twists the relation into
   `E_p(M·Φ(z)·A_k(z), z^{q^k}) = 0`, an identity **in `Ω`**, by `AF.aeval_twist` and
   `AF.eval₂_subMat_polyHom`;
2. everything in sight lies in the realization subring `R`, so the identity is one in `R`
   (`Subring.subtype` is injective);
3. `real` is a ring homomorphism, so it commutes with `MvPolynomial.eval₂`, and its values on the
   coefficients and on the matrix entries are exactly the germs of the intended functions. -/
@[category research solved, AMS 11 12 13 15 30, ref "AF22", group "af_mahler_alternative"]
theorem eventually_mvEvalC_branch_eq_zero {q : ℕ} (hq : 0 < q) {A : Matrix ι ι K[X]} {α : K}
    (hpt : Function.Injective fun k : ℕ => α ^ q ^ k)
    (hrel : IsRelationMatrix
      (relationIdeal hpt fun (n : ℕ) (s : ι × ι) => (iterMatrix q A n s.1 s.2).eval α) Φalg)
    (hbr : IsBranchRealization φ l Φalg R real Ψ) (M : Matrix ι ι K)
    (Ep : MvPolynomial (ι × ι) K[X])
    (hI : toRat K (ι × ι) (subMat K[X] M Ep) ∈
      relationIdeal hpt fun (n : ℕ) (s : ι × ι) => (iterMatrix q A n s.1 s.2).eval α)
    (k : ℕ) :
    ∀ᶠ z : ℂ in l, mvEvalC (z ^ q ^ k)
        (fun s : ι × ι => (M.map φ * Ψ z * evalMat z (iterMatrix q (mapMat φ A) k)) s.1 s.2)
        (MvPolynomial.map (Polynomial.mapRingHom φ) Ep) = 0 := by
  classical
  -- Step 1: [AF22] Lemma 2.7, unfolded to an `eval₂` over `Ω`
  have h27 := lemma_2_7 hq A hpt hrel k hI
  rw [aeval_twist] at h27
  rw [toRat_apply, MvPolynomial.eval₂_map] at h27
  -- the coefficient homomorphism `K[z] → Ω` of the twist
  set g₀ : K[X] →+* Ω := (toAmbient K Ω).comp (substPow K (q ^ k)) with hg₀
  have hcoeff : ((algebraMap (RatFunc K) Ω).comp (substPowRat K (pow_pos hq k))).comp
      (algebraMap K[X] (RatFunc K)) = g₀ := by
    refine RingHom.ext fun w => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, substPowRat_algebraMap, hg₀]
    rfl
  rw [hcoeff] at h27
  rw [eval₂_subMat_polyHom] at h27
  -- Step 2: the identity holds inside the realization subring
  set Mp : Matrix ι ι K[X] := M.map (Polynomial.C : K → K[X]) with hMp
  set Ak : Matrix ι ι K[X] := iterMatrix q A k with hAk
  have hg₀C : ∀ c : K, g₀ (Polynomial.C c) = toAmbient K Ω (Polynomial.C c) := by
    intro c
    rw [hg₀, RingHom.comp_apply, substPow_eq_expand, Polynomial.expand_C]
  have hMmap : (M.map fun c => g₀ (Polynomial.C c)) = Mp.map (toAmbient K Ω) := by
    ext i j
    simp [hMp, Matrix.map_apply, hg₀C]
  rw [hMmap] at h27
  set XR : Matrix ι ι R :=
    polyMatR hbr.poly_mem Mp * (relMatR hbr.mat_mem * polyMatR hbr.poly_mem Ak) with hXR
  have hsubX : (Subring.subtype R).mapMatrix XR
      = Mp.map (toAmbient K Ω) * (Φalg * Ak.map (toAmbient K Ω)) := by
    rw [hXR, map_mul, map_mul, subtype_mapMatrix_polyMatR, subtype_mapMatrix_relMatR,
      subtype_mapMatrix_polyMatR]
  have hg₀mem : ∀ w : K[X], g₀ w ∈ R := fun w => hbr.poly_mem _
  set g' : K[X] →+* R := g₀.codRestrict R hg₀mem with hg'
  have hsubg : (Subring.subtype R).comp g' = g₀ := by
    refine RingHom.ext fun w => ?_
    rfl
  have hR : eval₂ g' (fun s : ι × ι => XR s.1 s.2) Ep = 0 := by
    have hmap := MvPolynomial.eval₂_comp_left (Subring.subtype R) g'
      (fun s : ι × ι => XR s.1 s.2) Ep
    have hpt2 : ∀ s : ι × ι, (Subring.subtype R) (XR s.1 s.2)
        = (Mp.map (toAmbient K Ω) * (Φalg * Ak.map (toAmbient K Ω))) s.1 s.2 := by
      intro s
      rw [← hsubX]
      rfl
    rw [hsubg] at hmap
    have : (Subring.subtype R) (eval₂ g' (fun s : ι × ι => XR s.1 s.2) Ep) = 0 := by
      rw [hmap]
      simp only [Function.comp_def, hpt2]
      exact h27
    exact Subtype.coe_injective (by simpa using this)
  -- Step 3: apply the realization
  have hG : eval₂ (real.comp g') (fun s : ι × ι => real (XR s.1 s.2)) Ep = 0 := by
    have := congrArg real hR
    rw [MvPolynomial.eval₂_comp_left real g' (fun s : ι × ι => XR s.1 s.2) Ep, map_zero] at this
    simpa [Function.comp_def] using this
  -- identify the two homomorphisms with the germ of the intended complex data
  set Θ : ℂ → Matrix ι ι ℂ :=
    fun z => evalMat z (mapMat φ Mp) * (Ψ z * evalMat z (mapMat φ Ak)) with hΘ
  have hcoefH : real.comp g' = (Germ.coeRingHom l).comp (substFun φ (q ^ k)) := by
    refine RingHom.ext fun w => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply]
    have : g' w = ⟨toAmbient K Ω (substPow K (q ^ k) w), hbr.poly_mem _⟩ := rfl
    rw [this, hbr.real_poly]
    rw [Germ.coe_coeRingHom, substFun_eq_map_expand]
  have hptH : ∀ s : ι × ι,
      real (XR s.1 s.2) = (Germ.coeRingHom l) (fun z : ℂ => Θ z s.1 s.2) := by
    intro s
    have hmm : real.mapMatrix XR = germMat l Θ := by
      rw [hXR, map_mul, map_mul, real_mapMatrix_polyMatR hbr, real_mapMatrix_relMatR hbr,
        real_mapMatrix_polyMatR hbr, hΘ, germMat_mul, germMat_mul]
    have := congrFun (congrFun hmm s.1) s.2
    rw [germMat_apply] at this
    exact this
  rw [hcoefH] at hG
  simp only [hptH] at hG
  have hcomp := MvPolynomial.eval₂_comp_left (Germ.coeRingHom l) (substFun φ (q ^ k))
    (fun s : ι × ι => (fun z : ℂ => Θ z s.1 s.2)) Ep
  simp only [Function.comp_def] at hcomp
  rw [← hcomp] at hG
  -- read the germ identity pointwise
  have hfun : ∀ z : ℂ, eval₂ (substFun φ (q ^ k)) (fun s : ι × ι => fun w : ℂ => Θ w s.1 s.2) Ep z
      = mvEvalC (z ^ q ^ k) (fun s : ι × ι => Θ z s.1 s.2)
        (MvPolynomial.map (Polynomial.mapRingHom φ) Ep) := by
    intro z
    have h1 := MvPolynomial.eval₂_comp_left (Pi.evalRingHom (fun _ : ℂ => ℂ) z)
      (substFun φ (q ^ k)) (fun s : ι × ι => (fun w : ℂ => Θ w s.1 s.2)) Ep
    rw [evalRingHom_comp_substFun] at h1
    rw [mvEvalC, coe_eval₂Hom, MvPolynomial.eval₂_map]
    exact h1
  have hz : ((fun z : ℂ => mvEvalC (z ^ q ^ k) (fun s : ι × ι => Θ z s.1 s.2)
      (MvPolynomial.map (Polynomial.mapRingHom φ) Ep)) : ℂ → ℂ) =ᶠ[l] 0 := by
    have hfe : ((fun z : ℂ => mvEvalC (z ^ q ^ k) (fun s : ι × ι => Θ z s.1 s.2)
        (MvPolynomial.map (Polynomial.mapRingHom φ) Ep)) : ℂ → ℂ)
        = eval₂ (substFun φ (q ^ k)) (fun s : ι × ι => fun w : ℂ => Θ w s.1 s.2) Ep := by
      funext z
      exact (hfun z).symm
    rw [hfe, ← Germ.coe_eq, Germ.coe_zero]
    simpa using hG
  refine hz.mono fun z hz' => ?_
  have hΘz : Θ z = M.map φ * Ψ z * evalMat z (iterMatrix q (mapMat φ A) k) := by
    show evalMat z (mapMat φ Mp) * (Ψ z * evalMat z (mapMat φ Ak)) = _
    rw [hMp, evalMat_mapMat_map_C, hAk, mapMat_iterMatrix, Matrix.mul_assoc]
  rw [← hΘz]
  exact hz'

end Transport

/-! ## The interface is satisfiable -/

section NonVacuous

variable {K : Type*} [Field K] {ι : Type*} [DecidableEq ι]

/-- **`AF.IsBranchRealization` is not a vacuous hypothesis.**

The ambient field of [AF22] §2.2 is abstract, and a hypothesis about an abstract field is worth
nothing if nothing satisfies it.  Here is a witness: take the ambient field to be `K(z)` itself and
the relation matrix to be the identity.  The subring of *polynomials* then carries a realization
for **every** filter `l` and every embedding `φ : K →+* ℂ` — it is the tautological one, `w ↦ φ(w)`
read as a function — so the interface is satisfiable, and with `l = 𝓟 U` and `U` non-empty the
conclusion of `AF.eventually_mvEvalC_branch_eq_zero` is a genuine statement about functions on `U`.

What the corpus cannot yet produce is a witness for the *relation matrix* of [AF22] Lemma 2.5,
whose entries are algebraic over `K(z)` rather than polynomial; that is Lemma 2.8 and risk R14. -/
@[category research solved, AMS 11 12 30, ref "AF22", group "af_mahler_alternative"]
theorem exists_isBranchRealization_ratFunc (φ : K →+* ℂ) (l : Filter ℂ) :
    ∃ (R : Subring (RatFunc K)) (real : R →+* Germ l ℂ),
      IsBranchRealization φ l (1 : Matrix ι ι (RatFunc K)) R real (fun _ => 1) := by
  classical
  have hfa : ∀ w : K[X], toAmbient K (RatFunc K) w = algebraMap K[X] (RatFunc K) w := fun _ => rfl
  have hinj : Function.Injective (toAmbient K (RatFunc K)) := fun a b hab =>
    RatFunc.algebraMap_injective K (by rwa [← hfa, ← hfa])
  have hbij : Function.Bijective (toAmbient K (RatFunc K)).rangeRestrict :=
    ⟨fun a b hab => hinj (congrArg Subtype.val hab),
      (toAmbient K (RatFunc K)).rangeRestrict_surjective⟩
  set R : Subring (RatFunc K) := (toAmbient K (RatFunc K)).range with hR
  set e : K[X] ≃+* ↥R := RingEquiv.ofBijective (toAmbient K (RatFunc K)).rangeRestrict hbij with he
  have hmemP : ∀ w : K[X], toAmbient K (RatFunc K) w ∈ R := fun w => ⟨w, rfl⟩
  have hmemM : ∀ i j : ι, (1 : Matrix ι ι (RatFunc K)) i j ∈ R := by
    intro i j
    rcases eq_or_ne i j with rfl | hij
    · rw [Matrix.one_apply_eq]
      exact one_mem R
    · rw [Matrix.one_apply_ne hij]
      exact zero_mem R
  refine ⟨R, (Germ.coeRingHom l).comp ((substFun φ 1).comp e.symm.toRingHom),
    ⟨hmemP, fun w => ?_, hmemM, fun i j => ?_⟩⟩
  · have hew : e.symm ⟨toAmbient K (RatFunc K) w, hmemP w⟩ = w := by
      rw [show (⟨toAmbient K (RatFunc K) w, hmemP w⟩ : ↥R) = e w from Subtype.ext rfl,
        e.symm_apply_apply]
    have hs1 : substFun φ 1 w = fun z : ℂ => (w.map φ).eval z := by
      funext z
      rw [substFun_apply, pow_one]
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hew, hs1,
      Germ.coe_coeRingHom]
  · rcases eq_or_ne i j with rfl | hij
    · have h1 : (⟨(1 : Matrix ι ι (RatFunc K)) i i, hmemM i i⟩ : ↥R) = 1 := Subtype.ext (by simp)
      rw [h1, map_one, show ((fun z : ℂ => (1 : Matrix ι ι ℂ) i i) : ℂ → ℂ) = 1 by
        funext z; simp]
      exact Germ.coe_one.symm
    · have h0 : (⟨(1 : Matrix ι ι (RatFunc K)) i j, hmemM i j⟩ : ↥R) = 0 :=
        Subtype.ext (by simp [Matrix.one_apply_ne hij])
      rw [h0, map_zero, show ((fun z : ℂ => (1 : Matrix ι ι ℂ) i j) : ℂ → ℂ) = 0 by
        funext z; simp [Matrix.one_apply_ne hij]]
      exact Germ.coe_zero.symm

end NonVacuous

/-! ## `hEp`, and Step (UB) with it discharged -/

section HEp

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra (RatFunc K) Ω]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {φ : K →+* ℂ} {U : Set ℂ} {Φalg : Matrix ι ι Ω} {R : Subring Ω}
  {real : R →+* Germ (𝓟 U) ℂ} {Ψ : ℂ → Matrix ι ι ℂ}

/-- **`hEp`.**  With `l = 𝓟 U` a germ is a function on `U`, and the transport is exactly the
hypothesis that `CITED/AdamczewskiFaverjonDictionary`'s capstone carries: the truncated auxiliary
series vanishes along the branch `Θ_k`, at every point of `U`.

The normalizing matrix `a` of `AF.theta` is `φ(M)`, `M` being the matrix in which Step (AF)
substitutes `Y ↦ MY`; the relation `a·Ψ(ξ) = A_{k₀}(α)` that `AF.theta_center` needs is [AF22]
Lemma 2.8(c), and stays a hypothesis of the consumers, exactly as in WP11. -/
@[category research solved, AMS 11 12 13 15 30, ref "AF22", group "af_mahler_alternative"]
theorem mvEvalC_theta_eq_zero_of_branch {q : ℕ} (hq : 0 < q) {A : Matrix ι ι K[X]} {α : K}
    (hpt : Function.Injective fun k : ℕ => α ^ q ^ k)
    (hrel : IsRelationMatrix
      (relationIdeal hpt fun (n : ℕ) (s : ι × ι) => (iterMatrix q A n s.1 s.2).eval α) Φalg)
    (hbr : IsBranchRealization φ (𝓟 U) Φalg R real Ψ) (M : Matrix ι ι K)
    (Ep : MvPolynomial (ι × ι) K[X])
    (hI : toRat K (ι × ι) (subMat K[X] M Ep) ∈
      relationIdeal hpt fun (n : ℕ) (s : ι × ι) => (iterMatrix q A n s.1 s.2).eval α)
    (k₀ k : ℕ) :
    ∀ z ∈ U, mvEvalC (z ^ q ^ (k - k₀))
      (fun w : ι × ι => theta q k₀ (mapMat φ A) (M.map φ) Ψ k z w.1 w.2)
      (MvPolynomial.map (Polynomial.mapRingHom φ) Ep) = 0 := by
  have h := eventually_mvEvalC_branch_eq_zero hq hpt hrel hbr M Ep hI (k - k₀)
  rw [eventually_principal] at h
  intro z hz
  simpa [theta] using h z hz

/-- **Step (UB) with `hEp` discharged.**  `AF.eventually_norm_evalAt_le_exp_of_vanishing` is the
capstone of `CITED/AdamczewskiFaverjonDictionary`: Step (UB) with the dictionary's four hypotheses
gone and one mathematical hypothesis left, the vanishing `hEp`.  Here `hEp` is replaced by the
*existence of a branch realization* on a set containing the circle, together with the two algebraic
inputs it consumes — [AF22] Lemma 2.5 (`Φalg` is a relation matrix) and Lemma 2.12
(`AF.exists_auxiliary`: `E_p(MY,z)` is a relation).

What is left in the statement is therefore the analytic layer's own business — analyticity on the
closed disc, the geometry of the circle, Lemma 2.8(c) at one good `k₀` — plus the realization
itself, which is [AF22] Lemma 2.8(a,b) and plan risk R14.  All of those but the Mahler solutions'
own data and Step (NV) are discharged in `CITED/AdamczewskiFaverjonBranchExistence` by
`AF.eventually_norm_evalAt_le_exp_of_analyticBranch`, at the cost of the cited axiom
`AF.lemma_2_8`. -/
@[category research solved, AMS 11 12 13 15 30 40, ref "AF22", group "af_mahler_alternative"]
theorem eventually_norm_evalAt_le_exp_of_branch {q k₀ p v₀ N : ℕ} (hq : 2 ≤ q) (hvN : v₀ < N)
    {A : Matrix ι ι K[X]} {α : K} {P : ℕ → MvPolynomial (ι × ι) K[X]}
    (hP : ∀ j, j < v₀ → P j = 0) (τ : ι → K) {f : ι → PowerSeries K} {fs : ι → ℂ → ℂ}
    {M : Matrix ι ι K} {ξ : ℂ} {S : Set ℂ} {ρ r s t m γ Cb B₀ : ℝ}
    (hpt : Function.Injective fun k : ℕ => α ^ q ^ k)
    (hrel : IsRelationMatrix
      (relationIdeal hpt fun (n : ℕ) (w : ι × ι) => (iterMatrix q A n w.1 w.2).eval α) Φalg)
    (hbr : IsBranchRealization φ (𝓟 U) Φalg R real Ψ)
    (hI : toRat K (ι × ι) (subMat K[X] M
        (truncMv K (ι × ι) p (bigSeries P (linForm τ f) N))) ∈
      relationIdeal hpt fun (n : ℕ) (w : ι × ι) => (iterMatrix q A n w.1 w.2).eval α)
    (hUsph : sphere ξ ρ ⊆ U)
    (hreal : ∀ j, IsSumOn r ((f j).map φ) (fs j))
    (hS : ∀ z ∈ S, z ^ q ∈ S) (hmah : IsMahlerSolution q (mapMat φ A) fs S) (hα : φ α ∈ S)
    (hL : formVal (fun i => φ (τ i)) fs 1 (φ α) = 0) (hSsph : ∀ z ∈ sphere ξ ρ, z ∈ S)
    (hξ : ξ = φ α ^ q ^ k₀)
    (ha : M.map φ * Ψ ξ = evalMat (φ α) (iterMatrix q (mapMat φ A) k₀))
    (hρ : 0 < ρ) (hs0 : 0 < s) (hsr : s < r) (ht0 : 0 < t) (ht1 : t ≤ 1) (htr : t < r)
    (hsph : ∀ z ∈ sphere ξ ρ, ‖z‖ ≤ t) (hm : 0 < m)
    (hFf : ∀ z ∈ sphere ξ ρ, m ≤ ‖formVal (fun i => φ (τ i)) fs (M.map φ * Ψ z) z ^ v₀‖)
    (hC1 : 1 ≤ Cb) (hB₀ : 0 ≤ B₀)
    (hA : ∀ z : ℂ, ‖z‖ ≤ t → ∀ i j, ‖(mapMat φ A i j).eval z‖ ≤ Cb)
    (haΦ : ∀ z ∈ sphere ξ ρ, ∀ i j, ‖(M.map φ * Ψ z) i j‖ ≤ B₀)
    (h1B : 1 ≤ (Fintype.card ι : ℝ) * B₀) (h1C : 1 ≤ (Fintype.card ι : ℝ) * Cb)
    (hgan : ∀ k, k₀ ≤ k → DiffContOnCl ℂ
      (fun z => auxFun φ P (fun i => φ (τ i)) fs v₀ (N - v₀)
        (theta q k₀ (mapMat φ A) (M.map φ) Ψ k z) (z ^ q ^ (k - k₀))) (ball ξ ρ))
    (hγ0 : 0 < γ) (hγ : 2 * γ * (q : ℝ) ^ k₀ ≤ p * Real.log (1 / t)) :
    ∀ᶠ k in atTop, ‖φ (evalAt (fun k => α ^ q ^ k)
      (fun k w => (iterMatrix q A k w.1 w.2).eval α) k (P v₀))‖
      ≤ Real.exp (-(γ * (q : ℝ) ^ k)) :=
  eventually_norm_evalAt_le_exp_of_vanishing hq hvN φ hP τ hreal hS hmah hα hL hSsph hξ ha hρ hs0
    hsr ht0 ht1 htr hsph hm hFf hC1 hB₀ hA haΦ h1B h1C hgan
    (fun k _ z hz => mvEvalC_theta_eq_zero_of_branch (by omega) hpt hrel hbr M _ hI k₀ k z
      (hUsph hz))
    hγ0 hγ

end HEp

end AF
