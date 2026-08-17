-- SCRATCH FILE — safe to delete.  Regenerate with:
--   python3 - <<'EOF'
--   import re
--   for fn in ["TShift/Basic.lean", "TShift/MultiplierTransfer.lean",
--              "TShift/HabsiegerTransfer.lean", "TShift/FreeSojourn.lean",
--              "TShift/ResidueClass.lean", "TShift/DeterminantCap.lean",
--              "TShift/CriticalBox.lean", "TShift/MahlerCountMul.lean",
--              "TShift/DyadicBlocks.lean", "TShift/TowerCurrency.lean",
--              "TShift/BlockScope.lean", "TShift/CarryGraph.lean",
--              "TShift/GeneralBase.lean", "TShift/FreeZone.lean",
--              "TShift/InitialRange.lean", "TShift/ZudilinTransfer.lean",
--              "TShift/WindowCap.lean", "TShift/PadicLogForm.lean",
--              "TShift/CycleNormForm.lean"]:
--       ns = []
--       for line in open(fn, encoding="utf-8"):
--           m = re.match(r'^namespace\s+([\w.]+)', line)
--           if m: ns.append(m.group(1)); continue
--           if re.match(r'^end\s+[\w.]+', line) and ns: ns.pop(); continue
--           m = re.match(r"^(?:noncomputable\s+)?(?:theorem|def|structure)\s+([\w.']+)", line)
--           if m: print("#print axioms " + ".".join(ns + [m.group(1)]))
--   EOF
-- The `namespace`/`end` tracking is needed: `MultiplierTransfer` nests `TwoForms`.
-- Expected ledger: Basic + MultiplierTransfer std3; HabsiegerTransfer std3 + Habsieger.padeData
-- (the transported bound and everything downstream of it); MahlerCountMul std3 up to
-- `lineFibreMul_finite` and std3 + BugeaudEvertse.ridout_line_cover from `failuresMulFrom_finite`
-- on (the cited axiom enters only through BB13.mahler_line_cover); DyadicBlocks std3 for the block
-- machinery and every conditional-on-a-spared-block statement (13 of its 19 decls, including
-- `ncard_blockIdx_highFibreMul_le`, `forall_good_of_block_good` and `sojourn_cap_in_good_block`),
-- std3 + BugeaudEvertse.ridout_line_cover for the six that actually invoke the line cover
-- (`badBlocks_card_le` and its five instances); TowerCurrency std3 for the whole tower layer, its
-- transport, its block shadow and the no-go (20 of its 25 decls), std3 + ridout_line_cover for the
-- five of section 7 that inherit Theorem A through `badBlocks_cycleDenom_card_le`; BlockScope std3
-- for the rate half (monotonicity, the cubic price, the span certificates) and the parity clause
-- (15 of its 24 decls), std3 + ridout_line_cover for the nine that count blocks or invoke
-- Theorem C; std3 for the rest.
-- CarryGraph and GeneralBase use anonymous `section`s only (CarryGraph for one `open Classical`,
-- GeneralBase for the explicit-`(p q : ℕ)` block of definitions): a NAMED section would pop
-- `TShift` off the tracker's stack and mis-name the tail of the file.  FreeZone uses none at all.
-- Last run 2026-08-15 (report-Tshift S9: CycleNormForm.lean, the norm form over a cycle, and
-- what the structure of `D_p` is worth.  30 decls, ZERO cited axioms: 26 std3, 2 propext +
-- Quot.sound (`tgtNum_odd`, `cycleProd_odd`), 2 propext alone (`tgtNum`, `tgtNum_modEq`).  The
-- file imports `TShift.Basic` and `TShift.MultiplierTransfer` only -- no engine, by design: it
-- prices a route rather than running one, so it must not inherit anyone's axiom.  The two
-- load-bearing statements are `route_rate_le_half` (a bound on the cycle product valid at every
-- odd numerator forces theta <= 1/2, so S9(ii) cannot exceed the free floor) and the pair
-- `TwoForms.scale` / `transfer_bound_scale` (the elimination ledger is homogeneous of degree 0
-- under the scaling S9(i)'s congruence performs).  613 `#print axioms` lines, 613 resolved
-- records: 511 exactly std3, 31 ridout_line_cover, 24 propext only, 18 propext + Quot.sound,
-- 10 axiom-free, 8 Habsieger.padeData, 6 BugeaudLaurent.padicDist_lt, 5 Zudilin.padeData.
-- Unchanged from the S3 run in every cited column -- four cited axioms, one per engine, no
-- declaration carrying two, the four lanes still `#print axioms`-disjoint.)
-- Before that 2026-08-14 (report-Tshift S3: PadicLogForm.lean, the 2-adic linear form in two
-- logarithms.  39 decls; the file's arithmetic layer -- the defect `N_n`, the 2-adic order of `3`,
-- the non-degeneracy of the pair `(3, N_n/D)`, the height bound, `v₂(Λ) ≥ n`, the numeric
-- self-improvement lemma and the burn-in -- is 33 decls of pure std3, and exactly SIX carry the
-- cited engine `BugeaudLaurent.padicDist_lt` ([BL96p] Cor. 1): `master`, `le_defectLogA`,
-- `dist_ge_subexp`, `dist_ge_theta`, `isRepelledMul_padic`, `repelledAt_padic`.  That axiom is
-- the FOURTH cited name in this root, and the second whose axiom predated the item consuming it
-- (after `BugeaudEvertse.ridout_line_cover`, which came from BB13): `CITED/BugeaudLaurent.lean`
-- predates this build (plan-formalize-logforms gap G-a, 2026-07-11), so
-- report §9's forecast "S3(i) needs one new cited axiom" is discharged with none written.  583
-- `#print axioms` lines, 583 resolved records: 485 exactly std3, 31 ridout_line_cover, 22 propext
-- only, 16 propext + Quot.sound, 10 axiom-free, 8 Habsieger.padeData, 6 BugeaudLaurent.padicDist_lt,
-- 5 Zudilin.padeData.  Four cited axioms in the root, one per engine, and no declaration carrying
-- two -- the four lanes (Padé-Habsieger, Padé-Zudilin, Ridout-counting, 2-adic-log) remain
-- `#print axioms`-disjoint.)
-- Before that 2026-08-14 (plan-Tshift-S5 WP6: WindowCap.lean, the three stretch variants of T1' --
-- the good-date abstraction and the composition with a bounded exceptional set, the general-base
-- window cap with its unconditional base-5/2 instance, and the single-target variant with report
-- N2's cycle-shift identity.  35 decls, ZERO cited axioms: 28 std3, 5 propext + Quot.sound (the
-- purely arithmetic `MeetsWindow` lemmas and the two `mod`-only F2 statements), 2 axiom-free
-- (`MeetsWindow` itself and `MeetsWindow.mono_start`).  The file imports `TShift.ResidueClass` and
-- `TShift.FreeZone` only, so the S5 lane stays `#print axioms`-disjoint from both engine lanes --
-- deliberately, since the one available instance of its composition lemma is plan-S2's bad blocks
-- and instantiating it would import `BugeaudEvertse.ridout_line_cover` to prove something the
-- corpus already has.  544 `#print axioms` lines, 544 resolved records: 452 exactly std3, 31
-- ridout_line_cover, 22 propext only, 16 propext + Quot.sound, 10 axiom-free, 8
-- Habsieger.padeData, 5 Zudilin.padeData.  Still exactly three cited axioms in the root, one per
-- engine, and no declaration carrying two.)
-- Before that 2026-08-14 (plan-Tshift-S1 WP7: ZudilinTransfer.lean + CITED/ZudilinPade.lean, the
-- record rate 0.5803 transported to every multiplier.  23 decls here, and only FIVE carry the new
-- cited axiom `Zudilin.padeData` -- `le_dist_zudilin_uniform`, `le_dist_zudilin`,
-- `isRepelledMul_zudilin`, `isRepelledMul_five_zudilin`, `isRepelled_cycle_zudilin` -- so the whole
-- apparatus (the master bound, the block ascent, the rate step, the three Bernoulli lemmas, both
-- rational inequalities and every honesty lemma) is std3, exactly as on the Habsieger lane.  The
-- fourteen declarations of `CITED/ZudilinPade.lean` are std3 too (checked separately: the axiom is
-- used by nothing in its own file, `det_ne_zero` included).  509 `#print axioms` lines, 509
-- resolved records: 424 exactly std3, 31 ridout_line_cover, 22 propext only, 11 propext +
-- Quot.sound, 8 Habsieger.padeData, 8 axiom-free, 5 Zudilin.padeData.  TShift now has exactly THREE
-- cited axioms, one per engine (BugeaudEvertse.ridout_line_cover, Habsieger.padeData,
-- Zudilin.padeData), and no declaration carries two of them.)
-- Before that 2026-08-14 (plan-Tshift-S1 WP5(b): InitialRange.lean, the kernel certificate for the
-- initial range of Theorem A.  30 decls, and only ONE of them carries a cited axiom --
-- `le_dist_five_two_ranges`, the assembly that also quotes Theorem A -- so the certificate proper
-- (`sweep_five`, `sweep_one`, `le_dist_five_initial`, `le_dist_one_initial`,
-- `thetaHab_pow_le_five_iff`, and the four `recSweep_*` record certificates) is std3 or less with
-- zero cited axioms: 12 std3, 13 propext only (the `Bool`-valued certificates and the `decide`
-- evaluations), 2 propext + Quot.sound, 2 axiom-free, 1 Habsieger.padeData.  486 `#print axioms`
-- lines, 486 resolved records: 406 exactly std3, 31 ridout_line_cover, 22 propext only, 11 propext
-- + Quot.sound, 8 Habsieger.padeData, 8 axiom-free.  The six kernel certificates -- two 20 000-date
-- sweeps and four record sweeps of 3 327 and 12 428 dates -- cost 19 s of build time in total and
-- introduce no `native_decide` and no `decide` on anything but `Nat`.)
-- Before that 2026-08-14 (plan-Tshift-S1314 WP7, milestone M4 and gate G-D: CarryGraph.lean §9, the
-- cycle-restricted region at `deltaB = 5/64`.  +19 decls, 45 -> 64 for that file, all of them free
-- of cited axioms -- 58 std3, 3 axiom-free, 2 propext only, 1 propext + Quot.sound.  456 `#print
-- axioms` lines, 456 resolved records: 394 exactly std3, 31 ridout_line_cover, 7
-- Habsieger.padeData, 6 axiom-free, 9 propext only, 9 propext + Quot.sound.  G-D refused the
-- certificate leg, so no `Z32/BlockCertSojourn.lean` and no new `decide` entered the ledger.)
-- Before that 2026-08-14 (plan-Tshift-S1314 WP5, milestone M2: FreeZone.lean, 45/45 decls carry no
-- cited axiom -- 44 std3 and 1 propext + Quot.sound (`IsBreakB`).  So Theorem C, both routes and
-- the all-bases corollary, is std3 with zero cited axioms, and the whole S13/S14 item has no
-- cited-axiom lane whatever.  437 `#print axioms` lines, 437 resolved records: 375 exactly std3,
-- 31 carrying ridout_line_cover and 7 Habsieger.padeData (both pre-existing and outside this
-- plan), 6 axiom-free, 9 propext only, 9 propext + Quot.sound.)
-- Before that 2026-08-14 (plan-Tshift-S1314 WP4: GeneralBase.lean, 60/60 decls carry no cited axiom
-- -- 54 std3, 3 propext only (`cycleDenomB` and its two evaluations), 3 propext + Quot.sound.
-- So the S14 arithmetic layer, like the S13(iii) half, has no cited-axiom lane; the general-base
-- cascade route (b) of finding F7 is std3 at every coprime base.  396 `#print axioms` lines, 392
-- resolved records (the 4-line gap is pre-existing), of which 31 carry ridout_line_cover and 7 the
-- pre-existing Habsieger.padeData; 6 need no axioms at all, 331 are exactly std3.)
-- Before that 2026-08-14 (plan-Tshift-S1314 WP2: CarryGraph.lean, 45/45 decls std3, 0 cited -- the
-- whole S13(iii) half lands with no cited-axiom lane at all, as WP0's F6 predicted when it dropped
-- Theorem A' and the [Hab03] file with it.  332 `#print axioms` lines checked (331 in TShift/ plus
-- the ForMathlib `Set.ncard_biUnion_le`), of which 31 carry ridout_line_cover and 7 the
-- pre-existing Habsieger.padeData; 6 need no axioms at all, 277 are exactly std3.
-- CarryGraph's own 45: 39 std3, 3 axiom-free, 2 propext only, 1 propext + Quot.sound.)
-- Before that 2026-08-14 (plan-Tshift-S2 WP7 gate G-C: BlockScope.lean, 24/24 decls, footprints
-- exactly std3 (15) or std3 + ridout_line_cover (9), no third name.  287 `#print axioms` lines
-- checked (286 in TShift/ plus the ForMathlib `Set.ncard_biUnion_le`), of which 31 carry
-- ridout_line_cover and 7 the pre-existing Habsieger.padeData; 3 need no axioms at all).
-- Before that 2026-08-13 (plan-Tshift-S2 WP5 gate G-C: TowerCurrency.lean, 25/25 decls, footprints
-- exactly std3 (20) or std3 + ridout_line_cover (5), no third name; the ForMathlib addition
-- `Set.ncard_biUnion_le` is std3.  263 `#print axioms` lines checked (262 in TShift/
-- plus that one), of which 22 carry
-- ridout_line_cover and 7 the pre-existing Habsieger.padeData; 3 need no axioms at all).
-- Before that 2026-08-13 (plan-Tshift-S2 WP3 gate G-C: DyadicBlocks.lean, 19/19 decls, footprints
-- exactly std3 or std3 + ridout_line_cover, no third name; 237 decls checked in total, of which 17
-- carry ridout_line_cover and 7 the pre-existing Habsieger.padeData).
-- Before that 2026-08-13 (plan-Tshift-S2 WP1 gate G-C: MahlerCountMul.lean, 31/31 decls, footprints
-- exactly std3 or std3 + ridout_line_cover, no third name; this is the first file in TShift/ that
-- carries a cited axiom, by design -- the import direction is MahlerCountMul -> {BB13, Basic,
-- ResidueClass} and never the reverse, so Basic/ResidueClass keep their 0-cited purity).
-- Before that 2026-08-13 (plan-Tshift-S10 WP-E: CriticalBox.lean, 22/22 decls std3, 0 cited; 173
-- decls checked in total, and the only non-std3 entries remain HabsiegerTransfer's expected
-- Habsieger.padeData ones).
-- Before that 2026-08-12 (plan-Tshift-S8 gate G-C: DeterminantCap.lean, 15/15 decls std3, 0 cited
-- -- two of them, `det_cramer` and `delta_det`, need only propext + Quot.sound).
-- Before that 2026-08-11 (plan-Tshift-S5 gate G-C: ResidueClass.lean complete, std3, 0 cited),
-- re-run the same day after plan-Tshift-S7's angle O-4 added ResidueClass §11 (the descent):
-- 25/25 ResidueClass decls std3, 0 cited, and `distToNearestInt_descent'` does not clash with
-- HabsiegerTransfer's `distToNearestInt_descent` (both are checked here, in one namespace).
import TShift.Basic
import TShift.MultiplierTransfer
import TShift.HabsiegerTransfer
import TShift.FreeSojourn
import TShift.ResidueClass
import TShift.DeterminantCap
import TShift.CriticalBox
import TShift.MahlerCountMul
import TShift.DyadicBlocks
import TShift.TowerCurrency
import TShift.BlockScope
import TShift.CarryGraph
import TShift.GeneralBase
import TShift.FreeZone
import TShift.InitialRange
import TShift.ZudilinTransfer
import TShift.WindowCap
import TShift.PadicLogForm
import TShift.CycleNormForm

-- TShift/Basic.lean
#print axioms TShift.distToNearestInt_pow_sub
#print axioms TShift.cycleDenom_values
#print axioms TShift.three_pow_modEq_two_pow
#print axioms TShift.numerator_periodic
#print axioms TShift.affine_fixedPoint
#print axioms TShift.distToNearestInt_mul_ge
#print axioms TShift.distToNearestInt_mul_le
#print axioms TShift.distToNearestInt_ge_of_odd_denom
#print axioms TShift.IsRepelled
#print axioms TShift.IsRepelledMul
#print axioms TShift.TShiftProblem
#print axioms TShift.half_not_gt_two_thirds
#print axioms TShift.isRepelled_half
#print axioms TShift.isRepelledMul_half
#print axioms TShift.IsRepelledMul.isRepelled
#print axioms TShift.tShiftProblem_of_isRepelledMul
#print axioms TShift.RepelledAt
#print axioms TShift.TShiftProblemAt
#print axioms TShift.TShiftProblemAt.tShiftProblem
#print axioms TShift.repelledAt_half
#print axioms TShift.not_tShiftProblemAt_half
#print axioms TShift.abs_sub_fixed_le
#print axioms TShift.sojourn_cap
#print axioms TShift.kappa
#print axioms TShift.log_three_halves_pos
#print axioms TShift.sojourn_cap_kappa
#print axioms TShift.kappa_lt_one_iff
#print axioms TShift.kappa_two_thirds
#print axioms TShift.one_lt_kappa_half
#print axioms TShift.geometric_bound
#print axioms TShift.lt_two_mul_of_lt_two
#print axioms TShift.intPart
#print axioms TShift.carry
#print axioms TShift.carry_cast
#print axioms TShift.carry_mem
#print axioms TShift.carry_emod_two
#print axioms TShift.intPart_eq
#print axioms TShift.testBit_iff_carry_odd

-- TShift/MultiplierTransfer.lean
#print axioms TShift.transfer_one_form
#print axioms TShift.exists_delta_ne_zero
#print axioms TShift.multiplier_transfer
#print axioms TShift.multiplier_transfer_div
#print axioms TShift.le_distToNearestInt_transfer
#print axioms TShift.multiplier_transfer_pow
#print axioms TShift.le_distToNearestInt_pow
#print axioms TShift.transfer_prop_one
#print axioms TShift.transfer_prop_one_sanity
#print axioms TShift.TwoForms
#print axioms TShift.TwoForms.transfer
#print axioms TShift.TwoForms.transfer_div
#print axioms TShift.TwoForms.le_distToNearestInt

-- TShift/HabsiegerTransfer.lean
#print axioms TShift.thetaHab
#print axioms TShift.kHab
#print axioms TShift.dHab
#print axioms TShift.thetaHab_pos
#print axioms TShift.thetaHab_lt_two_thirds
#print axioms TShift.half_lt_thetaHab
#print axioms TShift.eightPow_le
#print axioms TShift.le_eightPow
#print axioms TShift.qHab
#print axioms TShift.sHab
#print axioms TShift.bHab
#print axioms TShift.sHab_pos
#print axioms TShift.one_le_bHab
#print axioms TShift.one_add_le_qHab
#print axioms TShift.two_le_qHab_pow
#print axioms TShift.bHab_pow_six_le_sHab
#print axioms TShift.bHab_pow_le_sHab_pow
#print axioms TShift.habsieger_correction_le
#print axioms TShift.habsieger_main_le
#print axioms TShift.habsieger_endgame
#print axioms TShift.distToNearestInt_descent
#print axioms TShift.le_distToNearestInt_uniform
#print axioms TShift.three_le_bHab_pow
#print axioms TShift.le_bHab_pow_self
#print axioms TShift.le_bHab_pow_of_le_dHab
#print axioms TShift.le_distToNearestInt_habsieger
#print axioms TShift.isRepelledMul_habsieger
#print axioms TShift.isRepelledMul_five
#print axioms TShift.isRepelled_cycle
#print axioms TShift.repelledAt_habsieger
#print axioms TShift.le_dist_cycle_uniform
#print axioms TShift.period_range_at_kHab
#print axioms TShift.one_le_kappa_thetaHab

-- TShift/FreeSojourn.lean
#print axioms TShift.mD
#print axioms TShift.deltaD
#print axioms TShift.abs_deltaD_eq_dist
#print axioms TShift.abs_deltaD_le
#print axioms TShift.cascade_step
#print axioms TShift.cascade_dvd
#print axioms TShift.carrySum
#print axioms TShift.two_mul_intPart_succ
#print axioms TShift.carrySum_zero
#print axioms TShift.carrySum_succ
#print axioms TShift.carry_circuit_sum
#print axioms TShift.IsCarryRepetition
#print axioms TShift.carrySum_eq_of_repetition
#print axioms TShift.lemmaR_floor
#print axioms TShift.two_pow_dvd_of_carry_repetition
#print axioms TShift.intPart_pos
#print axioms TShift.two_pow_mul_intPart_le
#print axioms TShift.intPart_lt_succ
#print axioms TShift.intPart_strictMono
#print axioms TShift.carry_repetition_pow_le
#print axioms TShift.carry_repetition_pow_le_nat
#print axioms TShift.carry_not_eventually_periodic
#print axioms TShift.IsPeriodicBlock
#print axioms TShift.free_sojourn_cap
#print axioms TShift.free_sojourn_cap_logb
#print axioms TShift.free_kappa_lt_one
#print axioms TShift.thetaFree
#print axioms TShift.thetaFree_pos
#print axioms TShift.kappa_thetaFree
#print axioms TShift.two_thirds_lt_thetaFree
#print axioms TShift.escape_ratio
#print axioms TShift.escape_lt_two_mul
#print axioms TShift.dyadic_block_visit
#print axioms TShift.carry_sanity
#print axioms TShift.sojourn_sanity

-- TShift/ResidueClass.lean
#print axioms TShift.exists_mem_class_Ico
#print axioms TShift.IsRepelledMulClass
#print axioms TShift.IsRepelledClass
#print axioms TShift.T1Prime
#print axioms TShift.IsRepelledMul.isRepelledMulClass
#print axioms TShift.isRepelledMulClass_one_iff
#print axioms TShift.IsRepelledMulClass.subclass
#print axioms TShift.t1Prime_of_isRepelledMul
#print axioms TShift.IsRepelledMulClass.isRepelledClass
#print axioms TShift.isRepelledClass_of_t1Prime
#print axioms TShift.isRepelledMulClass_half
#print axioms TShift.isRepelledClass_half
#print axioms TShift.kappa_nonneg
#print axioms TShift.kappa_lt_kappa_iff
#print axioms TShift.kappa_lt_free_iff
#print axioms TShift.sojourn_cap_window
#print axioms TShift.sojourn_cap_window_short
#print axioms TShift.sojourn_cap_class
#print axioms TShift.dyadic_block_visit_window
#print axioms TShift.isRepelledMulClass_of_twoForms
#print axioms TShift.t1Prime_of_twoForms
#print axioms TShift.twoForms_socket_sanity
#print axioms TShift.distToNearestInt_descent'
#print axioms TShift.isRepelledMul_of_isRepelledMulClass_pow_two
#print axioms TShift.tShiftProblem_of_isRepelledMulClass_pow_two
-- TShift/DeterminantCap.lean
#print axioms TShift.det_cramer
#print axioms TShift.det_cap
#print axioms TShift.det_cap_size
#print axioms TShift.delta_det
#print axioms TShift.det_le_delta_sum
#print axioms TShift.mul_abs_delta_le
#print axioms TShift.multiplier_transfer_det
#print axioms TShift.det_gain_vacuous
#print axioms TShift.det_bad_case
#print axioms TShift.det_bad_case_ceiling
#print axioms TShift.det_bad_case_transfer
#print axioms TShift.TwoForms.determinant
#print axioms TShift.TwoForms.det_cap_size
#print axioms TShift.TwoForms.det_gain_vacuous
#print axioms TShift.det_gain_vacuous_sanity

-- TShift/CriticalBox.lean
#print axioms TShift.critical_box_exact
#print axioms TShift.critical_box_real
#print axioms TShift.critical_box_base
#print axioms TShift.critical_box_base_le_one
#print axioms TShift.exists_form_in_box
#print axioms TShift.floor_le_critical
#print axioms TShift.forms_of_floor
#print axioms TShift.TwoForms.mono
#print axioms TShift.UniformFloor
#print axioms TShift.TwoFormsInBox
#print axioms TShift.twoFormsInBox_of_uniformFloor
#print axioms TShift.uniformFloor_of_twoFormsInBox
#print axioms TShift.floor_iff_forms
#print axioms TShift.le_distToNearestInt_of_uniformFloor
#print axioms TShift.lambda_one_ge_half
#print axioms TShift.mD_pos
#print axioms TShift.escape_of_not_two_pow_dvd
#print axioms TShift.escape_in_window
#print axioms TShift.escape_in_window_logb
#print axioms TShift.escape_frequently
#print axioms TShift.no_all_dates_smallness
#print axioms TShift.escape_sanity

-- TShift/MahlerCountMul.lean
#print axioms BB13.residMul
#print axioms BB13.residMul_one
#print axioms BB13.distToNearestIntMul_eq_residMul
#print axioms BB13.isFailureMul_iff_residMul
#print axioms BB13.AdmissibleMul
#print axioms BB13.residMul_ne_zero_of_not_dvd
#print axioms BB13.residMul_odd
#print axioms BB13.admissibleMul_of_odd
#print axioms BB13.admissibleMul_of_lt
#print axioms BB13.one_le_abs_residMul
#print axioms BB13.sameLineMul_resid
#print axioms BB13.sameLineMul_gap
#print axioms BB13.sameLineMul_lt_div_fArch
#print axioms BB13.lineFibreMul
#print axioms BB13.lineFibreMul_finite
#print axioms BB13.failuresMul
#print axioms BB13.failuresMulFrom
#print axioms BB13.highFibreMul
#print axioms BB13.ratHeight_natCast
#print axioms BB13.exists_thresholdMul
#print axioms BB13.failuresMulFrom_finite
#print axioms BB13.mahler_failures_mul_finite
#print axioms BB13.mahler_failures_mul_card_le_of_heightBound
#print axioms BB13.residNatMul
#print axioms BB13.abs_residMul_eq_residNatMul
#print axioms BB13.failNatMul
#print axioms BB13.failNatMul_iff
#print axioms BB13.failNatMul_initial_segments
#print axioms TShift.admissibleMul_three_two
#print axioms TShift.failuresMul_three_two_finite
#print axioms TShift.exists_pow_le_distToNearestIntMul
#print axioms TShift.isRepelledMul_of_lt_one
#print axioms TShift.tShiftProblem_holds
#print axioms TShift.t1Prime_holds
#print axioms TShift.exists_const_forall_ge_one
#print axioms TShift.tShift_forall_ge_one
#print axioms TShift.exists_tShiftProblemAt

-- TShift/DyadicBlocks.lean
#print axioms BB13.blockIdx
#print axioms BB13.blockIdx_eq
#print axioms BB13.blockIdx_le_of_le_mul
#print axioms BB13.ncard_blockIdx_image_le
#print axioms BB13.ncard_blockIdx_image_lt_le
#print axioms BB13.badBlocks
#print axioms BB13.blockBound
#print axioms BB13.forall_good_of_block_good
#print axioms BB13.ncard_blockIdx_highFibreMul_le
#print axioms BB13.badBlocks_card_le
#print axioms BB13.one_le_two_pow_one_mul_fArch
#print axioms TShift.badBlocks_three_two_card_le
#print axioms TShift.badBlocks_card_le_five
#print axioms TShift.badBlocks_card_le_five_decimal
#print axioms TShift.badBlocks_cycleDenom_card_le
#print axioms TShift.le_distToNearestInt_of_block_good
#print axioms TShift.kappa_three_quarters_lt_one
#print axioms TShift.sojourn_cap_in_good_block
#print axioms TShift.failuresMul_cycleDenom_finite

-- TShift/TowerCurrency.lean
#print axioms BB13.gap_identity_mul
#print axioms BB13.linkage_mul
#print axioms BB13.linkage_mul_of_linkable
#print axioms BB13.sameLine_of_linkage
#print axioms BB13.sameLine_of_linkable
#print axioms BB13.link_resid_mul
#print axioms BB13.link_dvd_mul
#print axioms BB13.link_scaling_mul
#print axioms BB13.link_quality_mul
#print axioms BB13.IsTowerBaseMul
#print axioms BB13.towerBasesMul_card_le
#print axioms BB13.exists_isTowerBaseMul_sameLine
#print axioms BB13.failuresMulLe
#print axioms BB13.badBlocksLe
#print axioms BB13.badBlocksLe_subset
#print axioms BB13.badBlocksLe_card_le_log
#print axioms BB13.ncard_badBlocksLe_le_tower
#print axioms TShift.towerBasesMul_card_le_three_halves
#print axioms TShift.badBlocksLe_three_two_card_le_tower
#print axioms TShift.tower_bound_not_below_trivial
#print axioms TShift.badBlocks_cycleDenom_finite
#print axioms TShift.badBlocks_cycleDenom_sum_card_le
#print axioms TShift.badBlocks_cycleDenom_biUnion_card_le
#print axioms TShift.badBlocks_cycleDenom_biUnion_finite
#print axioms TShift.badBlocks_cycleDenom_biUnion_card_le_decimal
#print axioms Set.ncard_biUnion_le

-- TShift/BlockScope.lean
#print axioms BB13.log_six_ge
#print axioms BB13.lineBound_le_of_le
#print axioms BB13.epsilon_antitone
#print axioms BB13.lineBound_epsilon_mono
#print axioms BB13.blockBound_mono
#print axioms BB13.inv_cube_le_lineBound
#print axioms BB13.lineBound_price_cubic
#print axioms BB13.exists_rate_lineBound_ge
#print axioms BB13.one_le_two_pow_mul_fArch
#print axioms BB13.one_le_four_mul_fArch_three_two
#print axioms BB13.one_le_two_mul_fArch_three_two
#print axioms BB13.residMul_odd_of_even
#print axioms BB13.admissibleMul_of_odd_of_even
#print axioms BB13.exists_two_pow_mul_fArch
#print axioms BB13.threshold_of_two_mul_lt_pow
#print axioms BB13.badBlocks_finite
#print axioms BB13.exists_badBlocks_card_le
#print axioms BB13.exists_badBlocks_card_le_of_odd
#print axioms BB13.exists_badBlocks_card_le_of_lt
#print axioms TShift.badBlocks_three_two_card_le_rate
#print axioms TShift.exists_badBlocks_three_two_card_le
#print axioms TShift.badBlocks_five_two_card_le
#print axioms TShift.badBlocks_five_four_card_le
#print axioms TShift.mahler_failures_mul_finite_of_odd_of_even

-- TShift/CarryGraph.lean
#print axioms TShift.tgt
#print axioms TShift.nextNum
#print axioms TShift.cycleDigit
#print axioms TShift.delta
#print axioms TShift.InU
#print axioms TShift.delta_pos
#print axioms TShift.tgt_sep
#print axioms TShift.tenth_dist
#print axioms TShift.carry_window
#print axioms TShift.admissible_iff
#print axioms TShift.admissible_ncard
#print axioms TShift.abs_carry_sub_cycleDigit_le
#print axioms TShift.forcing
#print axioms TShift.idxAt
#print axioms TShift.idxAt_zero
#print axioms TShift.idxAt_succ
#print axioms TShift.idxAt_add_two
#print axioms TShift.idxAt_mem
#print axioms TShift.IsSojourn
#print axioms TShift.sojourn_entry
#print axioms TShift.sojourn_chain
#print axioms TShift.sojourn_carry
#print axioms TShift.sojourn_isPeriodicBlock
#print axioms TShift.sojourn_shadow
#print axioms TShift.sojourn_cap_free
#print axioms TShift.sojourn_cap_half
#print axioms TShift.x_ne_tgt
#print axioms TShift.IsEscape
#print axioms TShift.logb_three_eq
#print axioms TShift.free_kappa_lt_three_fifths
#print axioms TShift.free_kappa_nonneg
#print axioms TShift.exists_escape_ge
#print axioms TShift.escapes_infinite
#print axioms TShift.exists_escape_dyadic
#print axioms TShift.escape_card
#print axioms TShift.escapeSeq
#print axioms TShift.escapeSeq_spec
#print axioms TShift.escapeSeq_lt
#print axioms TShift.escapeSeq_strictMono
#print axioms TShift.escapeSeq_mem_gap
#print axioms TShift.escapeSeq_sojourn
#print axioms TShift.escapeConst
#print axioms TShift.escapeSeq_recursion
#print axioms TShift.escapeSeq_geometric
#print axioms TShift.forcing_sanity
-- §9, WP7: the cycle-restricted region at deltaB = 5/64
#print axioms TShift.deltaB
#print axioms TShift.InUB
#print axioms TShift.deltaB_pos
#print axioms TShift.ceiling_facts
#print axioms TShift.three_tenth_dist
#print axioms TShift.abs_carry_sub_cycleDigit_leB
#print axioms TShift.forcingB
#print axioms TShift.idxAtB_mem
#print axioms TShift.IsSojournB
#print axioms TShift.sojourn_entryB
#print axioms TShift.sojourn_chainB
#print axioms TShift.sojourn_carryB
#print axioms TShift.sojourn_isPeriodicBlockB
#print axioms TShift.sojourn_cap_freeB
#print axioms TShift.IsEscapeB
#print axioms TShift.exists_escape_geB
#print axioms TShift.exists_escape_dyadicB
#print axioms TShift.inUB_not_inU
#print axioms TShift.cycleB_sanity

-- TShift/GeneralBase.lean
#print axioms TShift.intPartB
#print axioms TShift.fracB
#print axioms TShift.carryB
#print axioms TShift.orbB
#print axioms TShift.intPartB_eq
#print axioms TShift.fracB_eq
#print axioms TShift.carryB_eq
#print axioms TShift.q_mul_intPartB_succ
#print axioms TShift.intPartB_add_fracB
#print axioms TShift.fracB_nonneg
#print axioms TShift.fracB_lt_one
#print axioms TShift.carryB_mem
#print axioms TShift.carryB_not_isEventuallyPeriodic
#print axioms TShift.intPartB_three_two
#print axioms TShift.fracB_three_two
#print axioms TShift.carryB_three_two
#print axioms TShift.pow_ratio_eq
#print axioms TShift.fracB_eq_mod_div
#print axioms TShift.coprime_pow_mod
#print axioms TShift.distToNearestInt_mul_ge_base
#print axioms TShift.distToNearestInt_ge_of_coprime_denom
#print axioms TShift.distToNearestInt_fracB_sub
#print axioms TShift.cycleDenomB
#print axioms TShift.cycleDenomB_three_two
#print axioms TShift.cycleDenomB_cast
#print axioms TShift.cycleDenomB_pos
#print axioms TShift.cycleDenomB_coprime
#print axioms TShift.affine_fixedPointB
#print axioms TShift.carrySumB
#print axioms TShift.carrySumB_zero
#print axioms TShift.carrySumB_succ
#print axioms TShift.carryB_circuit_sum
#print axioms TShift.IsCarryRepetitionB
#print axioms TShift.carrySumB_eq_of_repetition
#print axioms TShift.lemmaR_base
#print axioms TShift.q_pow_dvd_of_carryRepetitionB
#print axioms TShift.one_le_ratio
#print axioms TShift.intPartB_pos
#print axioms TShift.intPartB_mono
#print axioms TShift.intPartB_ge_iff
#print axioms TShift.intPartB_ge_of_pow_le
#print axioms TShift.intPartB_one_ge_iff
#print axioms TShift.intPartB_lt_succ
#print axioms TShift.intPartB_strictMono
#print axioms TShift.q_pow_mul_intPartB_le
#print axioms TShift.carryRepetitionB_pow_le
#print axioms TShift.IsPeriodicBlockB
#print axioms TShift.periodic_block_pow_le
#print axioms TShift.sub_fixed_pow_block
#print axioms TShift.abs_sub_fixed_le_block
#print axioms TShift.abs_sub_fixed_mul_le_block
#print axioms TShift.fracB_add
#print axioms TShift.carryB_block_shift
#print axioms TShift.carrySumB_shift_of_block
#print axioms TShift.fracB_block_step
#print axioms TShift.block_shadow
#print axioms TShift.intPartB_five_two
#print axioms TShift.carryB_five_two
#print axioms TShift.cycleDenomB_five_two
#print axioms TShift.growth_threshold_five_two_three_two

-- TShift/FreeZone.lean
#print axioms TShift.kappaB
#print axioms TShift.kappaB_three_halves
#print axioms TShift.kappaB_lt_one_iff
#print axioms TShift.sojourn_cap_base
#print axioms TShift.kappaFloor
#print axioms TShift.kappaCasc
#print axioms TShift.log_base_pos
#print axioms TShift.log_nat_pos
#print axioms TShift.kappaFloor_eq_kappaB
#print axioms TShift.kappaFloor_nonneg
#print axioms TShift.kappaCasc_pos
#print axioms TShift.kappaFloor_mul_kappaCasc
#print axioms TShift.freeZone_iff
#print axioms TShift.cascZone_iff
#print axioms TShift.ne_sq_of_coprime
#print axioms TShift.min_kappa_lt_one
#print axioms TShift.kappaFloor_three_two
#print axioms TShift.not_freeZone_three_two
#print axioms TShift.kappaCasc_three_two
#print axioms TShift.cascZone_three_two
#print axioms TShift.kappa_half_mul_free_kappa
#print axioms TShift.intPartB_ge_of_mul_le
#print axioms TShift.periodic_block_cap_casc
#print axioms TShift.free_zone_cap_pow
#print axioms TShift.free_zone_cap
#print axioms TShift.IsBreakB
#print axioms TShift.exists_break_ge
#print axioms TShift.breaks_infinite
#print axioms TShift.breakSeq
#print axioms TShift.breakSeq_spec
#print axioms TShift.breakSeq_lt
#print axioms TShift.breakSeq_strictMono
#print axioms TShift.breakSeq_ge
#print axioms TShift.breakSeq_gap
#print axioms TShift.breakSeq_isPeriodicBlock
#print axioms TShift.breakSeq_recursion
#print axioms TShift.exists_break_dyadic_of_cap
#print axioms TShift.exists_break_dyadic_free_zone
#print axioms TShift.exists_break_dyadic_casc
#print axioms TShift.exists_break_dyadic_all_bases
#print axioms TShift.freeZone_five_two
#print axioms TShift.free_zone_cap_five_two
#print axioms TShift.exists_break_dyadic_five_two
#print axioms TShift.growth_threshold_sanity
#print axioms TShift.kappa_grid_sanity

-- TShift/InitialRange.lean (plan-Tshift-S1 WP5(b))
#print axioms TShift.windowRem
#print axioms TShift.windowMin
#print axioms TShift.distToNearestInt_eq_windowMin
#print axioms TShift.windowMin_odd
#print axioms TShift.thetaHab_pow_five_le
#print axioms TShift.le_distToNearestInt_of_window
#print axioms TShift.windowOk
#print axioms TShift.sweepFrom
#print axioms TShift.windowOk_iff
#print axioms TShift.sweep_spec
#print axioms TShift.le_dist_of_sweep
#print axioms TShift.sweep_five
#print axioms TShift.sweep_one
#print axioms TShift.le_dist_five_initial
#print axioms TShift.le_dist_one_initial
#print axioms TShift.dist_lt_thetaHab_pow_five
#print axioms TShift.thetaHab_pow_le_five_iff
#print axioms TShift.le_dist_five_two_ranges
#print axioms TShift.recOk
#print axioms TShift.recSweep
#print axioms TShift.recOk_iff
#print axioms TShift.recSweep_spec
#print axioms TShift.dist_lt_dist_of_window
#print axioms TShift.isRecord_of_recSweep
#print axioms TShift.recSweep_one_3328
#print axioms TShift.recSweep_five_3328
#print axioms TShift.recSweep_one_12429
#print axioms TShift.recSweep_five_12429
#print axioms TShift.record_dates_simultaneous
#print axioms TShift.initial_range_sanity

-- TShift/ZudilinTransfer.lean (plan-Tshift-S1 WP7)
#print axioms TShift.thetaZud
#print axioms TShift.bZud
#print axioms TShift.thetaZud_pos
#print axioms TShift.one_le_bZud
#print axioms TShift.thetaZud_lt_two_thirds
#print axioms TShift.thetaHab_lt_thetaZud
#print axioms TShift.bHab_lt_bZud
#print axioms TShift.zud_validity
#print axioms TShift.zud_rate
#print axioms TShift.zud_validity_uniform
#print axioms TShift.zud_block_constant
#print axioms TShift.zud_const_absorb
#print axioms TShift.zud_error_small
#print axioms TShift.zud_error_small_uniform
#print axioms TShift.distToNearestInt_ascent
#print axioms TShift.le_dist_master
#print axioms TShift.zud_rate_step
#print axioms TShift.le_dist_zudilin_uniform
#print axioms TShift.le_dist_zudilin
#print axioms TShift.isRepelledMul_zudilin
#print axioms TShift.isRepelledMul_five_zudilin
#print axioms TShift.isRepelled_cycle_zudilin
#print axioms TShift.one_le_kappa_thetaZud

-- TShift/WindowCap.lean (plan-Tshift-S5 WP6)
#print axioms TShift.MeetsWindow
#print axioms TShift.meetsWindow_class
#print axioms TShift.MeetsWindow.mono_start
#print axioms TShift.MeetsWindow.gap_mono
#print axioms TShift.MeetsWindow.sdiff
#print axioms TShift.MeetsWindow.sdiff_finite
#print axioms TShift.MeetsWindow.sdiff_blocks
#print axioms TShift.IsRepelledMulOn
#print axioms TShift.isRepelledMulOn_class_iff
#print axioms TShift.IsRepelledMulOn.mono
#print axioms TShift.isRepelledMulClass_of_sdiff_bounded
#print axioms TShift.isRepelledMulClass_of_sdiff_finite
#print axioms TShift.sojourn_cap_on
#print axioms TShift.sojourn_cap_class_sdiff
#print axioms TShift.dyadic_block_visit_slope
#print axioms TShift.kappaB_nonneg
#print axioms TShift.sojourn_cap_window_base
#print axioms TShift.sojourn_cap_window_base_short
#print axioms TShift.IsRepelledMulClassB
#print axioms TShift.isRepelledMulClassB_three_halves_iff
#print axioms TShift.sojourn_cap_class_base
#print axioms TShift.isRepelledMulClassB_five_two_half
#print axioms TShift.kappaB_five_two_half_lt_one
#print axioms TShift.sojourn_cap_class_five_two
#print axioms TShift.dyadic_block_visit_five_two
#print axioms TShift.sub_cycle_pow
#print axioms TShift.abs_sub_cycle_le
#print axioms TShift.abs_sub_cycle_le_shift
#print axioms TShift.periodic_eq_of_mod
#print axioms TShift.shadow_at_phase
#print axioms TShift.exists_mem_biclass_Ico
#print axioms TShift.exists_mem_biclass_Ico_coprime
#print axioms TShift.not_biclass_of_not_modEq
#print axioms TShift.not_biclass_two_six
#print axioms TShift.sojourn_cap_single

-- TShift/PadicLogForm.lean (S3, the 2-adic two-log route)
#print axioms TShift.defect
#print axioms TShift.abs_defect_eq
#print axioms TShift.two_mul_abs_defect_le
#print axioms TShift.defect_odd
#print axioms TShift.defect_ne_zero
#print axioms TShift.two_pow_dvd_sub_defect
#print axioms TShift.abs_defect_lt
#print axioms TShift.three_pow_emod_eight
#print axioms TShift.two_pow_le_of_dvd_three_pow_sub_one
#print axioms TShift.two_pow_le_of_dvd_three_pow_add_one
#print axioms TShift.two_pow_le_of_dvd_three_pow_sub
#print axioms TShift.two_pow_dvd_of_dvd_mul_odd
#print axioms TShift.not_two_dvd_mul_three_pow
#print axioms TShift.one_le_of_burnin
#print axioms TShift.abs_defect_ne_mul_three_pow
#print axioms TShift.abs_defect_mul_three_pow_ne
#print axioms TShift.mulIndep_three_defect
#print axioms TShift.log_two_lt_one
#print axioms TShift.one_le_log_three
#print axioms TShift.log_three_le_two_log_two
#print axioms TShift.defectLogA
#print axioms TShift.log_two_le_defectLogA
#print axioms TShift.defectLogA_pos
#print axioms TShift.logA_two_three
#print axioms TShift.defectLogA_le
#print axioms TShift.le_padicValRat_form
#print axioms TShift.master
#print axioms TShift.log_sq_lt_self
#print axioms TShift.exp_eight_le
#print axioms TShift.le_defectLogA
#print axioms TShift.eight_mul_lt_two_pow
#print axioms TShift.burnin_of_le
#print axioms TShift.dist_ge_subexp
#print axioms TShift.dist_ge_theta
#print axioms TShift.theta_padic_gt_half
#print axioms TShift.theta_padic_lt_two_thirds
#print axioms TShift.isRepelledMul_padic
#print axioms TShift.repelledAt_padic
#print axioms TShift.not_tShiftProblemAt_padic


-- TShift/CycleNormForm.lean (S9, the norm form over a cycle)
#print axioms TShift.tgtNum
#print axioms TShift.tgtNum_odd
#print axioms TShift.tgtNum_modEq
#print axioms TShift.exists_odd_tgtNum_abs_le
#print axioms TShift.exists_odd_near_target
#print axioms TShift.cycleProd
#print axioms TShift.cycleProd_odd
#print axioms TShift.one_le_abs_cycleProd
#print axioms TShift.abs_cycleProd_eq
#print axioms TShift.abs_sub_le_one
#print axioms TShift.le_abs_sub_of_le_abs_cycleProd
#print axioms TShift.abs_cycleProd_le_of_near
#print axioms TShift.abs_sub_le_of_abs_cycleProd
#print axioms TShift.abs_tgtNum_le_of_abs_tgtNum_le
#print axioms TShift.exists_odd_abs_cycleProd_le
#print axioms TShift.exists_odd_cycleProd_rate_le
#print axioms TShift.route_rate_le_half
#print axioms TShift.trivial_input_lt_free
#print axioms TShift.route_not_two_thirds
#print axioms TShift.route_rate_le_half_cycleDenom
#print axioms TShift.cycleProd_sanity
#print axioms TShift.dvd_sub_of_dvd_tgtNum_two
#print axioms TShift.pow_dvd_cycleProd
#print axioms TShift.not_dvd_cycleProd
#print axioms TShift.forced_prime_le_card
#print axioms TShift.TwoForms.scale
#print axioms TShift.transfer_bound_scale
#print axioms TShift.content_le_size
#print axioms TShift.scale_sanity_five
#print axioms TShift.isRepelled_zero_of_isRepelledMul
