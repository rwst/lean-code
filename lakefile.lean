/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
import Lake
open Lake DSL

package "lean-code" where
  version := v!"0.1.0"
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"


lean_lib Corpus where
  globs := #[.submodules `Corpus]

lean_lib DistributionModOne where
  globs := #[.submodules `DistributionModOne]

lean_lib ForMathlib where
  globs := #[.submodules `ForMathlib]

lean_lib BertinPisot where
  globs := #[.submodules `BertinPisot]

lean_lib Bugeaud where
  globs := #[.submodules `Bugeaud]

lean_lib WeylCriteria where
  globs := #[.submodules `WeylCriteria]

-- `SRS.AntihydraMachine` is deliberately NOT part of this library: it `import BusyLean`,
-- an external package this workspace does not depend on, so it can never be built here.
-- `SRS/AntihydraSRSaxiom.lean` is the in-repo stand-in.  Every other `SRS/` module is listed.
lean_lib SRS where
  globs := #[
    .one `SRS.AntihydraMahler,
    .one `SRS.AntihydraSRSaxiom,
    .one `SRS.AntihydraSRSForward,
    .one `SRS.AntihydraSRS,
    .one `SRS.AntihydraSRSObstruction,
    .one `SRS.AntihydraSRSSimulation,
    .one `SRS.ArcticInterpretation,
    .one `SRS.Basic,
    .one `SRS.CollatzSimulation,
    .one `SRS.CollatzSRS,
    .one `SRS.ComplexityBound,
    .one `SRS.GeneralizedCollatz,
    .one `SRS.Homogenization,
    .one `SRS.Interpretation,
    .one `SRS.MatrixInterpretation,
    .one `SRS.MixedBaseRepresentation,
    .one `SRS.NRationalSequence,
    .one `SRS.Zantema]

lean_lib CC where
  globs := #[.submodules `CC]

lean_lib CITED where
  globs := #[.submodules `CITED]

lean_lib AB where
  globs := #[.submodules `AB]

lean_lib BL where
  globs := #[.submodules `BL]

lean_lib B3 where
  globs := #[.submodules `B3]

lean_lib L90 where
  globs := #[.submodules `L90]

lean_lib RT where
  globs := #[.submodules `RT]

-- Author-original results for research-program.html Part I (paradoxical Collatz
-- sequences).  Files live in ./paradoxical/ (a research dir with PDFs/HTML/Python);
-- globbed like the other libs (module namespace = the lowercase dir name).
lean_lib Paradoxical where
  globs := #[.submodules `paradoxical]

-- "Three halves": M4/A3 program (plan-M4A3.html) — subword complexity of the
-- (3/2)^n steering word.  Extract.lean corpusRoots registration: user's call.
lean_lib TH where
  globs := #[.submodules `TH]

-- Flatto–Lagarias–Pollington ⅓-spread theorem (plan-FLT.html, ref "FLP95") —
-- milestone M3 of the (3/2)ⁿ equidistribution ladder.  Build-only registration;
-- Extract.lean corpusRoots registration + db regen: user's call.
lean_lib FLP where
  globs := #[.submodules `FLP]

-- Rational base number system 3/2 (plans plan-B1E2.html + plan-B2A2.html, refs
-- "AFS08"/"Dub09") — the orbit ⌈3x/2⌉, its minimal word g_{3/2}, and K = ω_{3/2}.
-- Shared root of both plans.  Build-only registration; Extract.lean corpusRoots
-- registration + db regen: user's call.
lean_lib RB where
  globs := #[.submodules `RB]

-- Forman–Shapiro 1967 / [DubOst06] Conjecture 2 for ⌊ξ·aⁿ⌋ (plan-dubC1.html, refs
-- "Dub09"/"DubOst06"/"DN05") — milestone M1′: the [Dub09] Thm 4 return engine, the digit
-- dynamics, and the C(𝒫) zero-entropy certificate.  Experimental C/Python engines live in
-- the same directory.  Build-only registration; Extract.lean corpusRoots registration + db
-- regen: user's call.
lean_lib DubC where
  globs := #[.submodules `DubC]

-- An unavoidable divisor set for the *nearest* integer ⌊ξ(3/2)ⁿ + 1/2⌋ (plans/plan-dubC2.html,
-- refs "DN05"/"Dub09AA"/"Dub08MN") — the case [DN05] Thm 4 conspicuously omits, its neighbours
-- 7, 5/3, 7/5 being done there.  The driven-carry product subshift (2-adic × odd residues ×
-- interval cells); survivors die to [DN05] Lemma 2, already proved ν-generally as
-- Z32.not_isEventuallyPeriodic_carry, so no Euler-return step is needed.  Imports Z32 (carry
-- formalism, BlockCert cell certificates, SmallInterval arc killer) and DubC's abstract
-- certificate layer only — never DubC.ReturnEngine.  Build-only registration; Extract.lean
-- corpusRoots registration + db regen: user's call.
lean_lib DubC2 where
  globs := #[.submodules `DubC2]

-- The (3/2)ⁿ confinement atlas (plans/plan-cert32.html, refs "FLP95"/"Dub09AA") — milestone M1:
-- the floor-residue ⟺ cell dictionary, the five FLP95 Cor 1.4a escape certificates, and T1
-- (residue non-capture mod m ≥ 3); milestone M1-bis: Dubickas 2009 (Acta Arith. 137), no
-- Z_{p/q}(s,s+1/p) is nonempty when 1 < q < p < q², for every real s.  Build-only registration;
-- Extract.lean corpusRoots registration + db regen: user's call.
lean_lib Z32 where
  globs := #[.submodules `Z32]

-- Bugeaud Problem 10.13 (plan-1013.html, refs "Bug12"/"DD90") — bound #{n : ‖(3/2)ⁿ‖<(3/4)ⁿ}.
-- M2/D1 elementary gap-principle layer: §3 gap identity, linkage lemma, O(log N) tower count.
-- Build-only registration; Extract.lean corpusRoots registration + db regen: user's call.
lean_lib BB13 where
  globs := #[.submodules `BB13]

-- Bugeaud Problem 10.6 (plans/plan-BB6-paper.html, refs "Bug12"/"Bos83"/"Kat16") — the
-- calibration: every reading of "very rapidly increasing" that constrains only the size or the
-- sparsity of the sequence is vacuous, because runs of consecutive integers answer all of them.
-- WP2 layer: Lemma R (runs ⟹ universally densifying), Theorem A(i)–(iii) on one dyadic-block
-- construction, and Corollary A′ — which proves `Bugeaud06.problem_10_6_variant_2` verbatim and
-- std3, de-axiomatizing the two Katz axioms in its recorded proof.  Build-only registration;
-- Extract.lean corpusRoots registration + db regen: user's call.
lean_lib BB6 where
  globs := #[.submodules `BB6]

-- Third-party port: reusable infrastructure lifted from `shaikidris/CET` v2.0.1
-- (Apache-2.0, © Idris Ali Shaik), adapted from Lean 4.15.0 to this toolchain.
-- Two independent groups: (a) the (C,D)-density / dyadic-shell API of Inselmann
-- arXiv:2402.03276 Def. 2.6, which this corpus lacked entirely; (b) the Syracuse
-- numerator on compositions with its fixed-length injectivity and the residue-fiber
-- spacing bound.  Deliberately NOT ported: their Terras parity bijection (we already
-- have `CC.terras_bijection`) and the whole endpoint-transport bootstrap, whose
-- headline claim is unverified here.  Build-only registration; Extract.lean
-- corpusRoots registration + db regen: user's call.
lean_lib CET where
  globs := #[.submodules `CET]


-- The T-shift problem (plan-A6+ C7, σ-ledger): exponential repulsion of (3/2)ⁿ from the cycle
-- targets A/(3^p−2^p).  Statement + the elementary layer around it (free bound, multiplier
-- reduction, shadowing, sojourn cap and its 2/3 threshold, diagonal-bit identity); plus
-- MultiplierTransfer.lean (plan-Tshift-S1 WP1), the content-refined rank-2 elimination step that
-- carries a multiplier D at the cost of one product |c|·Λ — engine-agnostic, so no Padé
-- construction enters; and HabsiegerTransfer.lean (WP3 + WP4), which feeds it the cited bundle of
-- CITED/HabsiegerPade.lean to get ‖D(3/2)^k‖ ≥ 0.57434^k for k ≥ 64440001, uniformly in the
-- multiplier (every D ≤ (1216/1215)^k at once), hence repulsion from every cycle target of every
-- period, and at a single date from all periods p ≤ k/1341 simultaneously.  0.57434 < 2/3, so the
-- effective problem is still open (see MahlerCountMul.lean below).  Plus FreeSojourn.lean
-- (plan-Tshift-S11 WP-C), which proves what *is* free: the floor-convention port of Lemma R
-- (from TH/RepetitionIdentity.lean, round convention) gives the unconditional sojourn cap
-- 2^(L+n) <= 3^(n+p) on p-periodic blocks of the carry word, i.e. L <= 0.585 n + 1.585 p, hence
-- the dyadic-block-visit payoff; it also carries the 1/5 parity cascade at a general multiplier.
-- No repulsion hypothesis and no per-n floor: it does not touch the open problem.  Plus
-- MahlerCountMul.lean (plan-Tshift-S2 WP1), which closes the multiplier gap BB13/MahlerCount.lean
-- flags — the residue D*p^n - m*q^n never vanishes for odd D at q = 2 (parity), so the delta = 1
-- per-line confinement runs at every multiplier — and gets Mahler's theorem for ‖D(p/q)^n‖ along
-- the quantitative Ridout route (std3 + BugeaudEvertse.ridout_line_cover).  That last statement is
-- a reproof, not a new result: Mahler 1957 has only D = 1, while Schlickewei 1975 Thm 1 (at n = 1)
-- and Philippon-Rath 2019 Thm 5/12 both print the multiplier form — qualitatively, discarding the
-- cover, which is exactly what DyadicBlocks.lean below needs kept.  At (3,2) that settles
-- the *existential* form of the problem, TShift.TShiftProblem, at every period and numerator, and
-- likewise T1Prime; so the file also carries the repair this forces, TShift.TShiftProblemAt, the
-- problem with its numerals exhibited, which is what is actually open.  Plus DyadicBlocks.lean
-- (plan-Tshift-S2 WP3), the effective shadow of that ineffective finiteness: a line of the Ridout
-- cover is confined to [a, a/f_inf), which meets at most t+1 dyadic blocks [2^m, 2^(m+1)) whenever
-- 2^t f_inf >= 1, so the failures meet at most K(eps)(t+1) + log_2 N_0 + 1 blocks -- Theorem A,
-- BB13.badBlocks_card_le, every quantity explicit -- and all the other blocks are ENTIRELY good.
-- At (D,theta) = (5,3/4) every constant is already certified (eps(3,3/4) = eps*), giving at most
-- 3 720 000 000 004 bad blocks with no new numerics, at kappa(3/4) = 0.70951 < 1: a per-date rate
-- above 2/3 at every date of all but boundedly many blocks.  Positions still ineffective, date
-- count still conditional, and the escape payoff still weaker than FreeSojourn's free one.
-- Plus TowerCurrency.lean (WP5), the second exception currency and its price: the gap principle,
-- the linkage lemma and its four consequences transport to every multiplier (D cancels out of the
-- gap identity, so neither admissibility nor a parity clause is needed), linkage is upgraded to
-- collinearity, and the free O(log N) tower count runs at every multiplier with no decimal log
-- bound (3^66 <= 2^105).  The swap the plan proposed -- replace b_l K(eps) by that count -- is
-- REFUTED, not performed: the block shadow 2(12 + log_{6/5} N) exceeds the floor(log2 N) + 1
-- blocks that exist below N, at every N and at every ratio up to the sharp 1+eps*, so only a line
-- count bounded independently of N (the cited axiom) can show that most blocks are good.  The
-- file also carries WP5(b), the uniform-in-period package: the blocks bad for SOME period p <= P
-- number at most P (2 K(eps*) + log2 max(10,P+1) + 1).  20 of its 25 decls are std3; only that
-- last package inherits the axiom.
-- Plus BlockScope.lean (WP7), which moves Theorem A along its two free parameters and prices each
-- move.  The rate: the line count is monotone in it, so the bound is CHEAPEST at theta -> 2/3 and
-- the plan's question was pointed the wrong way; the price of theta -> 1 is at least cubic,
-- K(eps(3,theta)) >= 1.27e9/(1-theta)^3, so no rate-uniform bound exists -- and it is the WHOLE
-- price, because one block span t = 2 serves every rate below 1 at base 3/2.  The base: the parity
-- clause never used q = 2, only 2 | q, so for D and p odd and q EVEN the residue is odd and
-- Theorem A runs at every coprime p/q of that shape, at every odd multiplier and every rate; the
-- span certificate reduces to the rational inequality (p/(cq))^(2^t) >= p, and the bases (5,2) and
-- (5,4) -- q even but not 2 -- are carried out in full.  Only the decimals are base-specific: they
-- would need log 5 enclosures.  15 of its 24 decls are std3.
-- Build-only registration; Extract.lean corpusRoots registration + db regen: user's call.
lean_lib TShift where
  globs := #[.submodules `TShift]

-- The Dubickas S/Z landscape (plans/plan-dubD1.html, ref "Dub06EO" = Dubickas, *Even and odd
-- integral parts of powers of a real number*, Glasgow Math. J. 48 (2006) 331-336; NOT the
-- [Dub06] of Bugeaud/Chapter3, which is the Bull. LMS paper of the same year).  Report
-- report-dubickas.html theme D: the sets Z = {alpha > 1 : some xi != 0 makes every floor(xi
-- alpha^n) even} and S = (1,infty) \ Z, the alpha-version of Mahler's 1968 question at 3/2.
-- Milestone M2/M3 of the plan: the sign-compensated trace-parity design settling
-- alpha = 1 + sqrt 2 (report section D.1's "best single open case", the P_alpha(1) = -2 boundary
-- that evades every engine of [Dub06EO]), its mod-m generalisation (report section D.4), a
-- constructive Tijdeman engine for [3, infinity) (report section D.6), the golden mean on the S
-- side, and the resulting complete classification of the quadratic Pisot numbers.  No cited
-- axiom anywhere.  Build-only registration; Extract.lean corpusRoots registration + db regen:
-- user's call.
lean_lib SZ where
  globs := #[.submodules `SZ]
