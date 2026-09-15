#!/bin/sh
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
#
# reproduce.sh -- plan-cert32 milestone M2: regenerate every number in
# Z32/README.md from scratch.  Deterministic: no timing, no randomness except
# the printed seed of the X3 greedy search.  Total runtime ~1 minute except
# where marked.
#
#   cd Z32 && sh reproduce.sh          # writes data/*.txt, prints checksums

set -e
cc=${CC:-gcc}
$cc -O2 -o hold     hold.c     -lm
$cc -O2 -o atlas    atlas.c    -lm
$cc -O2 -o gridcert gridcert.c -lm
mkdir -p data

echo "== X1 control: FLP95 Cor 1.4a escape orbits (expect N = 3,2,3,1) =="
for a in 1 2 3 4; do ./hold orbit $a 2 6 20; done  > data/x1_flp_orbits.txt
grep esc0 data/x1_flp_orbits.txt

echo "== X1 sweep: L = 1/3, s = i/G, theta-model =="
: > data/x1_sweep.txt
for G in 6 12 24 48 96 192 384 768 1536 3072 3888; do
  ./hold x1 $G 36 | tail -1 >> data/x1_sweep.txt
done
cat data/x1_sweep.txt

echo "== X1 cross-check: same five positions in the y-model =="
for a in 0 1 2 3 4; do ./atlas win 40 6 $a 2 | grep verdict; done | tee data/x1_ymodel.txt

echo "== X2: the (position,length) map, G = 360, lengths 1/3 .. 1/2 =="
ATLAS_CAP=20000 ./atlas x2 360 120 180 30 > data/x2_G360.txt 2>&1
grep '^# row' data/x2_G360.txt | head -30

echo "== X2 frontier: G = 3600 near L* (30 s) =="
ATLAS_CAP=20000 ATLAS_ILO=940 ATLAS_IHI=1240 ./atlas x2 3600 1455 1470 30 > data/x2_frontier.txt 2>&1
ATLAS_CAP=20000 ./atlas x2 3600 1467 1475 30 >> data/x2_frontier.txt 2>&1
grep '^# row' data/x2_frontier.txt

echo "== X2 no-go witnesses: cycle counts inside band entries =="
{ for w in "24 0 10" "360 0 150" "6 2 4" "24 4 13"; do
    set -- $w
    printf "U=[%s/%s,%s/%s) : " $2 $1 $3 $1
    ./atlas horse 12 $1 $2 $3 | grep 'cycles found'
  done; } | tee data/x2_cycles.txt

echo "== X3 literature controls =="
{ printf "[Dub08] Cor 1.2, U = [8/39,18/39) u [21/39,31/39), |U| = 20/39: "
  ./atlas cert 30 39 8 18 21 31 | grep verdict
  printf "[Dub06] complement, |U| = 0.476234: "
  ./atlas cert 30 1000000 0 238117 761883 1000000 | grep verdict
} | tee data/x3_controls.txt

echo "== X3 NEGATIVE controls: sets known NONEMPTY must come back undecided =="
{ printf "[KK18] Cor 4.8  X_{3,2}, |U|=2/3     : "; ./atlas cert 30 6 0 1 2 4 5 6 | grep -o "verdict [A-Z]*"
  printf "[Dub10] (1.1)   ||.||<1/3, |U|=2/3   : "; ./atlas cert 30 3 0 1 2 3 | grep -o "verdict [A-Z]*"
  printf "[Pol81]         [4/65,61/65)         : "; ./atlas cert 30 65 4 61 | grep -o "verdict [A-Z]*"
  printf "[Dub08] Thm 1.3 (5/48,43/48)         : "; ./atlas cert 30 48 5 43 | grep -o "verdict [A-Z]*"
  printf "[Cho80]         [1/19,18/19)         : "; ./atlas cert 30 19 1 18 | grep -o "verdict [A-Z]*"
} | tee data/x3_negative.txt

echo "== X3 exhaustive union search (records; N0 = 20 takes ~2 min) =="
for N in 12 16 18 20; do ./atlas x3exh $N 30 | tail -2; done | tee data/x3_exhaustive.txt

echo "== X3 randomized search + refinement climb =="
for N in 36 48 60; do ./atlas x3 $N 4000 28 | tail -2; done | tee data/x3_random.txt
echo "(the 120- and 240-cell records come from x3climb.py seeded by the 60-cell"
echo " winner; see README.  python3 x3climb.py 120 <cells>)"

echo "== record union, verified three ways =="
R240="0 8 12 32 36 48 52 88 100 104 108 128 132 152 161 184 190 191 192 208 216 224 228 237 238 239"
{ printf "C engine   : "; ./atlas cert 30 240 $R240 | grep verdict
  printf "falsify    : "; ./atlas horse 10 240 $R240 | tail -1
  printf "python lvls: "; python3 verify_atlas.py 18 240 $R240 --all --nocert |
      awk '$1=="level"&&$2+0>=15{printf "%s:%s ",$2,$4}'; echo
  printf "C lvls     : "; ATLAS_FULL=1 ./atlas cert 18 240 $R240 |
      awk 'NF==2&&$1+0>=15{printf "%s:%s ",$1,$2}'; echo
} | tee data/x3_record.txt

echo "== checksums =="
md5sum data/*.txt

# ---------------------------------------------------------------------------
# Milestone M3: the Lean bridge.  `gencert.py` re-runs the exact pruning and
# emits the funnel that `Z32/BlockCert.lean` hands to the kernel; these runs
# regenerate every certificate in that file byte for byte, and confirm that the
# generator refuses the five sets known NONEMPTY in print.
# ---------------------------------------------------------------------------

echo "== M3/M6 certificates (must match the defs in Z32/BlockCert.lean) =="
{ python3 gencert.py --closed --ranked 39 8 18 21 31          --lean certDub08
  python3 gencert.py 24 4 13                                  --lean certWindow38
  python3 gencert.py 12 0 2 3 4 5 8 9 10                      --lean certUnion712
  python3 gencert.py 18 0 2 3 8 9 10 11 14 15 16              --lean certUnion23
  python3 gencert.py 3600 961 2427                            --lean certFrontier
  python3 gencert.py 36 0 3 4 11 16 24 25 27 30 32 33 36      --lean certUnion2536
  python3 gencert.py 5 0 1 4 5                                --lean certTwoCellFifth
  python3 gencert.py --pq 4 3 24 8 15                         --lean certFourThree
  python3 gencert.py --pq 5 2 5 1 2                           --lean certFiveTwo
  # the p > q^2 table: six positions s = i/6 at each of five bases, all depth 1
  for i in 0 1 2 3 4 5; do
    python3 gencert.py --pq 5  2 30 $((i*5))  $((i*5+6))  --lean certGridFiveTwo$i
  done
  for i in 0 1 2 3 4 5; do
    python3 gencert.py --pq 7  2 42 $((i*7))  $((i*7+6))  --lean certGridSevenTwo$i
  done
  for i in 0 1 2 3 4 5; do
    python3 gencert.py --pq 9  2 18 $((i*3))  $((i*3+2))  --lean certGridNineTwo$i
  done
  for i in 0 1 2 3 4 5; do
    python3 gencert.py --pq 10 3 30 $((i*5))  $((i*5+3))  --lean certGridTenThree$i
  done
  for i in 0 1 2 3 4 5; do
    python3 gencert.py --pq 11 3 66 $((i*11)) $((i*11+6)) --lean certGridElevenThree$i
  done
} > data/m3_certs.txt
grep -E '^(def|# \(V2)' data/m3_certs.txt
diff <(grep -E '^\s+(D :=|p :=|q :=|closed :=|U :=|\[\()' data/m3_certs.txt) \
     <(grep -E '^\s+(D :=|p :=|q :=|closed :=|U :=|\[\()' BlockCert.lean) \
  && echo "certificates in BlockCert.lean are byte-identical to this run"

echo "== the union record (17/24), checked against Z32/UnionRecord.lean =="
echo "  (SLOW: the kernel check of this one costs ~100 s and ~12 GB; the"
echo "   generator run below is the cheap half)"
python3 gencert.py 48 0 2 3 9 10 11 12 16 17 18 20 21 23 34 36 37 38 40 41 45 46 47 \
  --lean certUnion7083 > data/m3_union_record.txt
diff <(grep -E '^\s+(D :=|U :=|\[\()' data/m3_union_record.txt) \
     <(grep -E '^\s+(D :=|U :=|\[\()' UnionRecord.lean) \
  && echo "certUnion7083 in UnionRecord.lean is byte-identical to this run"

echo "== the two-cell frontier: c = 1/5 certifies, c = 21/100 and closed do not =="
python3 gencert.py 100 0 21 79 100 | tail -1
python3 gencert.py --closed 5 0 1 4 5 | tail -1

echo "== M3 negative controls: no certificate for sets known NONEMPTY =="
{ for w in "65 4 61" "19 1 18" "48 5 43" "3 0 1 2 3" "6 0 1 2 4 5 6"; do
    printf "%-22s : " "[$w]"
    python3 gencert.py $w 2>&1 | grep -E "no certificate|V2\) and|KILL" | head -1
  done; } | tee data/m3_negative.txt

echo "== M4' P1 negative controls: same five refused in the STRONGEST mode too =="
{ for w in "65 4 61" "19 1 18" "48 5 43" "3 0 1 2 3" "6 0 1 2 4 5 6"; do
    printf "%-22s : " "[$w]"
    python3 gencert.py --closed --ranked $w 2>&1 |
      grep -E "no certificate|V2\) and|KILL" | head -1
  done; } | tee data/m4_negative_closed.txt

echo "== M6 base-independence: the (3,2) path must be BYTE-IDENTICAL to M3 =="
{ python3 gencert.py --pq 3 2 24 4 13 --lean certWindow38
} > data/m6_default.txt
diff <(grep -E '^\s+(D :=|U :=|\[\()' data/m6_default.txt) \
     <(sed -n '/^def certWindow38/,/^$/p' data/m3_certs.txt |
       grep -E '^\s+(D :=|U :=|\[\()') \
  && echo "--pq 3 2 reproduces the default (3,2) certificate exactly"

echo "== M6 controls: a second base, in both colors (SLOW: ~1 h, mostly part C) =="
python3 pqcontrols.py | tee data/m6_controls.txt

# ---------------------------------------------------------------------------
# Milestone M7 / experiment X4: the section-4.3 product refinement, states
# (cell, x mod q^j).  The engine is built so that its two no-go theorems can be
# measured, not asserted: Theorem A (the product KILLs no earlier than the
# archimedean engine, ever) and Theorem B (a certificate needs one block per
# periodic orbit of the hold set).  Applied to [Aki08] Conjecture 1.4 they
# close it out: no certificate of this family exists at any level.
# ---------------------------------------------------------------------------

echo "== M7/X4 controls: the product refinement, in both colors (~90 s) =="
python3 prodcert.py | tee data/m7_controls.txt

echo "== M7 cross-check: the C engine must agree on the cycle counts =="
{ for w in "24 0 10" "3600 961 2427" "3600 961 2428"; do
    printf "atlas horse P<=12  U=[%-14s] : " "$w"
    ./atlas horse 12 $w | grep -i 'cycles found'
  done; } | tee data/m7_horse.txt
grep -q 'cycles found: 1 ' data/m7_horse.txt \
  && echo "(the two frontier entries have ONE cycle each -- band and certified alike)"

# ---------------------------------------------------------------------------
# plan-M5A9 milestone N2(a): the phi_model ledger.  `horseshoe.py` re-checks the
# four certificates of Z32/ModelEntropy.lean in the exact integer form the Lean
# kernel uses, and validates each one independently by expanding every
# concatenation of up to two (or three) blocks and testing its periodic orbit.
# The searches print the frontier of what this certificate shape can reach, and
# the two certified windows are the negative controls: a set with phi_model = 0
# can carry no horseshoe (Z32.not_cert_and_horse), and none is found.
# ---------------------------------------------------------------------------

echo "== N2(a) phi_model: re-check the four horseshoe certificates =="
python3 horseshoe.py --check | tee data/n2_horseshoes.txt
grep -q "ALL ENTRIES RE-CHECKED" data/n2_horseshoes.txt

echo "== N2(a) searches: the band entry, the two-cell hole, and two controls =="
{ echo "--- band [0,5/12)";        python3 horseshoe.py --search band 8
  echo "--- two-cell ||.||<1/3";   python3 horseshoe.py --search twocell 6
  echo "--- control [1/6,13/24)";  python3 horseshoe.py --search window38 6
  echo "--- control frontier";     python3 horseshoe.py --search frontier 6
} | tee data/n2_search.txt
grep -c "no horseshoe" data/n2_search.txt

echo "== N2(a) why intervals: no point carries two return words of one length =="
{ for s in band twocell window38; do echo "--- $s"; python3 horseshoe.py --points $s 6; done
} | tee data/n2_points.txt
grep -q "1 carrying" data/n2_points.txt && echo "UNEXPECTED: a point with two words" || \
  echo "(the two-cell counts are 2^L-1: a full shift on points, none of them shared)"

# ---------------------------------------------------------------------------
# The three experiments opened by gate G-0 of plans/plan-z32-transform.html.
# X-KP is the negative control that MUST fail (its emptiness is Mahler's
# conjecture, by [KP18] Cor. 18); X-D19 tests the corpus against [Dub19]
# Thm 1.2; X-238 sweeps the two-cell family against [Dub06JNT]'s 0.238117...
# Write-up: plans/note-z32transform-X.html.  Kernel side: Z32/XG0Certs.lean.
# ---------------------------------------------------------------------------

echo "== X-KP: [KP18] Cor. 18's union -- must fail, and the manner of failure =="
python3 xg0.py kp | tee data/xg0_kp.txt
grep -q "prune(H,H) == H : True" data/xg0_kp.txt
grep -q "ranked : ('FAT'" data/xg0_kp.txt

echo "== X-D19: [Dub19] Thm 1.2's window, and the one-grid-unit shift =="
python3 xg0.py d19 | tee data/xg0_d19.txt
grep -q "\[217/1539, 805/1539) len 0.382066 : ('CYCLE'" data/xg0_d19.txt

echo "== X-238: the two-cell family, default vs rank-stratified =="
python3 xg0.py twocell | tee data/xg0_twocell.txt
grep -q "c=238/1000 = 0.238    : ('CYCLE', 7, 84, 18)" data/xg0_twocell.txt

echo "== the two block certificates of XG0Certs.lean, regenerated and diffed =="
python3 gencert.py --ranked --lean certTwoCell238 1000 0 238 762 1000 | sed -n '/^def cert/,/^$/p' > data/xg0_cert238.txt
python3 gencert.py          --lean certD19Shift  1539 217 805            | sed -n '/^def cert/,/^$/p' > data/xg0_certd19.txt
sed -n '/^def certTwoCell238/,/^$/p' XG0Certs.lean | diff - data/xg0_cert238.txt
sed -n '/^def certD19Shift/,/^$/p'   XG0Certs.lean | diff - data/xg0_certd19.txt

echo "== G-1: the depth-1 schema in (p,q,s), against two independent engines =="
python3 g1schema.py all | tee data/transform/g1_schema.txt
grep -q "schema == independent engine == gencert on all 30: YES" data/transform/g1_schema.txt
grep -q "12038 (base, position) pairs; 7989 predicted depth-1 valid (66.4%); 0 mismatches" data/transform/g1_schema.txt
grep -q "positions tested: 868; disagreements: 0" data/transform/g1_schema.txt
grep -q "wrapped positions tested: 51; disagreements: 0" data/transform/g1_schema.txt
grep -q "16153 (base, position) pairs; disagreements: 0" data/transform/g1_schema.txt

echo "== X-P re-aimed: the exact eps-cell decomposition of the two residual bands (~6 min) =="
python3 xp.py all | tee data/transform/xp_bands.txt
grep -q "1880 eps-pairs, 0 asymmetries" data/transform/xp_bands.txt
grep -q "at every grid point: YES" data/transform/xp_bands.txt
grep -q "bases disagreeing with the word: 0" data/transform/xp_bands.txt
grep -q "the HIGH word is the reversed LOW word at all 10 bases: YES" data/transform/xp_bands.txt
grep -q "rationals that resist: 0 and 0" data/transform/xp_bands.txt
grep -q "cells where ranking lowers the depth: 0 of 12" data/transform/xp_bands.txt
grep -q "plus every breakpoint as a rational instance); disagreements: 0" data/transform/xp_bands.txt
# the universality claim: the same 57-cell word at all ten bases
test "$(grep -c '57 cells   word identical to 5/2' data/transform/xp_bands.txt)" = 10
# the (5,2) growth row at cap 22, and the (4,3) caveat at cap 16
grep -q "  22    171             86   0.999999978092" data/transform/xp_bands.txt
grep -q "certified 0.964579931823" data/transform/xp_bands.txt

echo "== M3: the depth-K schema, and its identification with [Bug04] Lemma 3 (~3 s) =="
python3 m3schema.py | tee data/transform/depthk_schema.txt
grep -qF "1600 eps at 10 bases, mismatches: 0" data/transform/depthk_schema.txt
grep -qF "Escape holds on 800 of 800 band points; failures: 0" data/transform/depthk_schema.txt
grep -qF "LowBand endpoints+interior: 450 points, LowBand => Escape failures: 0" data/transform/depthk_schema.txt
grep -qF "LowBand K=1 == the G-1 closed band: True;  K=0 == q <= p*eps: True" data/transform/depthk_schema.txt
grep -qF "241524 checks (rotation + branch dichotomy), violations: 0" data/transform/depthk_schema.txt
# the literature cross-check: the certified eps are exactly [Bug04] Lemma 3's J_b^a(q/p)
grep -qF "840 interior points over the a/b with b <= 9, mismatches: 0" data/transform/depthk_schema.txt
grep -qF "Z32.LowBand ... K  ==  J_(K+1)^1(q/p)  at all bases, K <= 11: True" data/transform/depthk_schema.txt
grep -qF "escapes at K=2 throughout: True" data/transform/depthk_schema.txt
grep -qF "escapes at K=3 throughout: True" data/transform/depthk_schema.txt

echo "== M2: the quantitative escape bound (target T4) (~2 s) =="
python3 m2escape.py | tee data/transform/escape_bound.txt
grep -qF "shape mismatches: 0" data/transform/escape_bound.txt
grep -qF "ranked certificate excluded from M2: certDub08 (strata=4)" data/transform/escape_bound.txt
grep -qF "points tested: 11826, violations: 0" data/transform/escape_bound.txt
grep -qF "periodic runs found 8728; ladder checks 10937, divisibility 8728, dichotomy 8728" data/transform/escape_bound.txt
grep -qF "itineraries checked 42 (skipped 3193 as too short for the funnel), failures: 0" data/transform/escape_bound.txt
grep -qF "deepest confinement found at [1/6,13/24): 9 steps over 546 orbits" data/transform/escape_bound.txt
grep -qF "mismatches against the closed form: 0" data/transform/escape_bound.txt
grep -qF "points tested: 2400, violations: 0" data/transform/escape_bound.txt
grep -qF "VERDICT: all checks pass" data/transform/escape_bound.txt

echo "== M4: completeness and the obstruction (target T5) (~80 s) =="
python3 m4complete.py | tee data/transform/cert_complete.txt
grep -qF "certificates re-checked: 5, failures: 0; unranked controls wrongly passing: 0" data/transform/cert_complete.txt
grep -qF "more than one coprime successor in [0,1): 0" data/transform/cert_complete.txt
grep -qF "exactly one coprime successor: 6868" data/transform/cert_complete.txt
grep -qF "cycle points found: 26244; denominator not dividing p^P - q^P: 0; undefined successors: 0" data/transform/cert_complete.txt
grep -qF "recursion 2*y(n+1) = 3*y(n) - w(n) over 60 chains x 80 steps: failures 0" data/transform/cert_complete.txt
grep -qF "points outside the CLOSED [0,1/5] u [4/5,1]: 0" data/transform/cert_complete.txt
grep -qF "points outside the HALF-OPEN [0,1/5) u [4/5,1): 1530" data/transform/cert_complete.txt
grep -qF "closed-convention entries with a ranked certificate: 6 of 9" data/transform/cert_complete.txt
grep -qF "violations of |hold set| <= |blocks|: 0" data/transform/cert_complete.txt
grep -qF "VERDICT: all checks pass" data/transform/cert_complete.txt

echo "== X-U: the union-pattern autopsy (conjecture C-8, target T6) (~8 min) =="
python3 xu.py | tee data/transform/union_autopsy.txt
# A: the recurrent map is multiplication by p*q^{-1} mod D, and its two corollaries
grep -qF "successors that are not unique: 0;  disagreements with a |-> p*a*q^(-1) mod D: 0" \
  data/transform/union_autopsy.txt
grep -qF "non-periodic: 0" data/transform/union_autopsy.txt
grep -qF "that are not P-periodic: 0; P-periodic points of another denominator: 0" \
  data/transform/union_autopsy.txt
# B/C: the census, and the one-or-two orbits each record keeps
grep -qF "total points of period <= 14: 7138565, in 531292 orbits" data/transform/union_autopsy.txt
grep -qF "25/36   (N= 36): surviving orbits of period <= 14: 1" data/transform/union_autopsy.txt
grep -qF "89/120  (N=240): surviving orbits of period <= 14: 2" data/transform/union_autopsy.txt
grep -qF "period 3: 2/19 -> 3/19 -> 14/19" data/transform/union_autopsy.txt
# D: the funnel agrees with the census, and adds the backward tree
grep -qF "cycles 1+3, tree 56" data/transform/union_autopsy.txt
# E: C-8's own recipe, and that its refusals are final
grep -qF "NEVER (funnel converged d=21)" data/transform/union_autopsy.txt
grep -qF "the best measure C-8's recipe ever certifies is 1/4" data/transform/union_autopsy.txt
# F: the three new climb records
grep -qF "1440  181/240    0.754167" data/transform/union_autopsy.txt
# G: the two measure facts behind the depth-size bound
grep -qF "violations of (i): 0, of (ii): 0" data/transform/union_autopsy.txt
grep -qF "VERDICT: all structural checks pass" data/transform/union_autopsy.txt

echo "== M5(a): the depth-size bound, on the records (~2 s) =="
python3 depthsize_check.py | tee data/transform/depth_size.txt
# (i) the expansion half: the funnel loses at most delta per level
grep -qF "|f^-1(S)| >= |S| on the funnel, k = 0..22: 0 violations" data/transform/depth_size.txt
grep -qF "|T_k| >= 1 - (k+1) delta, k = 0..29: 0 violations" data/transform/depth_size.txt
# the certifier must reproduce the K and B the Lean file computes from the certificates
grep -qF "delta = 11/36, K = 11, B = 17" data/transform/depth_size.txt
grep -qF "delta = 7/24, K = 17, B = 100" data/transform/depth_size.txt
# (iii) the headline, and the slack it leaves at each record
grep -qF "2 delta (K+2+log_(3/2) 2B) = 13.2593 >= 1: ok" data/transform/depth_size.txt
grep -qF "floor on delta 0.023045 vs actual 0.305556, slack 13.26x" data/transform/depth_size.txt
grep -qF "89/120 (engine): K = 29, B = 2526" data/transform/depth_size.txt
grep -qF "VERDICT: depth-size bound holds on every record" data/transform/depth_size.txt

echo "== X-F: the frontier autopsy (conjectures C-6/C-7, target T7) (~8 min) =="
python3 xf.py | tee data/transform/frontier_autopsy.txt
# A: the recorded frontier row, reproduced by an independent exact-rational engine
grep -qF "i = 940..1240: 14 certified, 0 disagreements with the recorded row" \
  data/transform/frontier_autopsy.txt
grep -qF "reflection i <-> 2134-i maps the certified set to itself: True" \
  data/transform/frontier_autopsy.txt
grep -qF "0 certified, 0 disagreements with the recorded row" data/transform/frontier_autopsy.txt
# B: the survivor-cycle inventory, and C-6's verdict
grep -qF "8 windows, 0 mismatches" data/transform/frontier_autopsy.txt
grep -qF "of these, certified (hull): 14      refused: 2  [960, 1174]" \
  data/transform/frontier_autopsy.txt
# D: C-7 sharpened to an equality
grep -qF "213 ranked-certified positions; depth in {ker(s), ker(s+L)} at 213, elsewhere at 0" \
  data/transform/frontier_autopsy.txt
# E: the frontier belonged to the hull-merge search
grep -qF "the ranked-certified set is EXACTLY 961..1173: True" data/transform/frontier_autopsy.txt
grep -qF "|U| = 0.428571   ranked depth 15    blocks 166" data/transform/frontier_autopsy.txt
grep -qF "421 positions tested, 9 certified, all in [1030, 1070]" data/transform/frontier_autopsy.txt
grep -qF "centre 1029   certified in c+-25:   1   [1029, 1029]" data/transform/frontier_autopsy.txt
grep -qF "centre 1028   certified in c+-25:   0   empty" data/transform/frontier_autopsy.txt
# G: the Thue-Morse cascade and the two constants of [Dub06JNT] Cor. 1
grep -qF "   mismatches: 0" data/transform/frontier_autopsy.txt
grep -qF "(1 + T)/4  = 0.285647324744458851" data/transform/frontier_autopsy.txt
grep -qF "(3 - T)/12 = 0.238117558418513716" data/transform/frontier_autopsy.txt
grep -qF "so the ceiling lies in (0.2856472, 0.2856475]" data/transform/frontier_autopsy.txt
grep -qF "cascade mismatches: 0" data/transform/frontier_autopsy.txt
grep -qF "VERDICT: C-6 half true" data/transform/frontier_autopsy.txt

echo "== the block certificate of RankedFrontier.lean, regenerated and diffed (~2 min) =="
python3 gencert.py --closed --ranked --lean certTwoSeven 7 2 5 | sed -n '/^def cert/,/^$/p' \
  > data/transform/cert_twoseven.txt
sed -n '/^def certTwoSeven/,/^$/p' RankedFrontier.lean | diff - data/transform/cert_twoseven.txt

echo "== M3/M6/M7/N2/XG0 checksums =="
md5sum data/transform/*.txt data/m3_*.txt data/m6_*.txt data/m7_*.txt data/n2_*.txt data/xg0_*.txt 
