#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M2 -- one check per numbered statement of note-1061-M2.html.

T1  Theorem 1   the covering: minimal certified depth, effective gap bound, orbit avoidance
P3  Prop 3      normal form (L-1)(R-1)>1 and threshold rho < 2^{-L/(L-1)}, swept
P4  Prop 4      the ceiling rho >= alpha^{-1/(d-1)}; equality iff unit with equal moduli
T5  Theorem 5   the family X^d - aX^{d-1} - 1: irreducible Pisot unit, thresholds
C6  Cor 6       quadratic normal form (log2 a - 1)(log2(a/b) - 1) > 1, swept
P7  Prop 7      X7 vacuity: diam K >= d-1 > g, 2*Delta > g, swept
P8  Prop 8      exact invariance of A under (2,alpha,rho) -> (2^p,alpha^p,rho^p)
P9  Prop 9      X8 completeness: raster certificates at the first firings and at 2+sqrt3

Sweeps run over m0_coverage.json (9287 Pisot numbers).  Requires numpy, mpmath, sympy.
"""
import json, math, numpy as np, mpmath as mp
from m0_engine import Alpha, orbit, irreducible
from m0_gaps import support_gaps
from m0_words import CATALOG

mp.mp.dps = 60
RES = {}

def L2(x): return math.log2(x)

def report(key, ok, msg):
    RES[key] = dict(ok=bool(ok), msg=msg)
    print('%-4s %s  %s' % (key, 'PASS' if ok else 'FAIL', msg))

COV = json.load(open('m0_coverage.json'))

# ---------------- T1: Theorem 1, the covering ----------------
def min_cover(al, Wmax=200000):
    """smallest M+M' with 2^(M+M')(alpha^-M + C rho^M'/(1-rho)) < 1, and the gap bound there."""
    a, r = al.a, al.r
    C = float(sum(abs(complex(z) - 1) for z in al.conj)) / (1 - r)
    t = math.log(a) / math.log(1 / r)
    best = None
    for M in range(1, Wmax):
        for Mp in (int(M * t) + s for s in (-1, 0, 1, 2)):
            if Mp < 1: continue
            x, y = -M * L2(a), Mp * L2(r) + L2(C)
            hi, lo = max(x, y), min(x, y)
            lt = (M + Mp) + hi + L2(1 + 2 ** (lo - hi))
            if lt < 0:
                total = 2.0 ** lt
                gap_log2 = L2(1 - total) - (M + Mp)
                best = dict(M=M, Mp=Mp, W=M + Mp, log2_total=lt, log2_gap=gap_log2)
                return best
    return best

def t1_case(coeffs, name, Nw=20000):
    al = Alpha(coeffs, name)
    cov = min_cover(al)
    g, MK, pos = support_gaps(al)
    # orbit avoidance: 14 structured words + 20 random, all must miss (pos, pos+g)
    hits = 0; pts = 0
    rng = np.random.default_rng(2)
    words = [fn(Nw) for fn in CATALOG.values()] + \
            [(rng.random(Nw) < rng.uniform(.1, .9)).astype(np.int8) for _ in range(20)]
    for eps in words:
        x = orbit(al, eps)
        pts += len(x)
        hits += int(np.sum((x > pos) & (x < pos + g)))
    return al, cov, (g, pos), hits, pts

al2, cov2, (g2, p2), h2, n2 = t1_case([1, -4, -1], '2+sqrt5')
al3, cov3, (g3, p3), h3, n3 = t1_case([1, -8, 0, -1], 'X^3-8X^2-1')
report('T1a', cov2 and cov2['log2_total'] < 0,
       '2+sqrt5: cover < 1 first at (M,M\')=(%d,%d), gap >= 2^%.1f; raster gap %.5f at %.4f'
       % (cov2['M'], cov2['Mp'], cov2['log2_gap'], g2, p2))
report('T1b', cov3 and cov3['log2_total'] < 0,
       'X^3-8X^2-1: cover < 1 first at (M,M\')=(%d,%d) [W=%d], gap >= 2^%.1f; raster gap %.5f'
       % (cov3['M'], cov3['Mp'], cov3['W'], cov3['log2_gap'], g3))
report('T1c', h2 == 0 and h3 == 0,
       'orbit avoidance: %d+%d points from 34 words each, %d landed in the certified gap' % (n2, n3, h2 + h3))
RES['T1'] = dict(sqrt5=dict(cover=cov2, gap=g2, pos=p2), cubic=dict(cover=cov3, gap=g3, pos=p3))

# ---------------- P3: normal form and threshold ----------------
bad_nf = bad_th = 0; maxdev = 0.0
for r in COV:
    Lg, R = L2(r['a']), L2(1 / r['rho'])
    A = 1 / Lg + 1 / R
    maxdev = max(maxdev, abs(A - r['A']))
    if ((Lg - 1) * (R - 1) > 1) != (A < 1): bad_nf += 1
    if (r['rho'] < 2 ** (-Lg / (Lg - 1))) != (A < 1): bad_th += 1
report('P3', bad_nf == 0 and bad_th == 0 and maxdev < 1e-9,
       'normal form and threshold agree with A<1 on all %d Pisot (max |A| dev %.1e)' % (len(COV), maxdev))

# ---------------- P4: the ceiling and its equality case ----------------
viol = eq_bad = 0; eq_cases = []
minAL = {}
for r in COV:
    d = r['d']; ceil = r['a'] ** (-1 / (d - 1))
    if r['rho'] < ceil - 1e-9: viol += 1
    AL = r['A'] * L2(r['a'])
    minAL[d] = min(minAL.get(d, 9), AL)
    if abs(r['rho'] - ceil) < 1e-9:
        eq_cases.append(r)
        if not r['unit']: eq_bad += 1
        if abs(AL - d) > 1e-9: eq_bad += 1
# equality must be: unit and (d=2, or d=3 with a complex pair)
cplx_bad = 0
for r in eq_cases:
    if r['d'] == 2: continue
    rts = np.roots(np.array(r['coeffs'], dtype=float))
    small = sorted([z for z in rts if abs(z) < 1], key=lambda z: z.imag)
    if r['d'] == 3 and abs(small[0].imag) < 1e-9: cplx_bad += 1
    if r['d'] > 3: cplx_bad += 1
report('P4', viol == 0 and eq_bad == 0 and cplx_bad == 0,
       'ceiling holds on all %d; equality at %d numbers, every one a unit with equal-modulus '
       'conjugates (d=2 or d=3 complex pair); min A*log2(a) per degree: %s'
       % (len(COV), len(eq_cases), {d: round(v, 6) for d, v in sorted(minAL.items())}))
RES['P4'] = dict(equality_count=len(eq_cases), minAL=minAL)

# ---------------- T5: the family X^d - aX^{d-1} - 1 ----------------
def fam(d, a):
    c = [1, -a] + [0] * (d - 2) + [-1]
    rts = mp.polyroots([mp.mpf(x) for x in c], maxsteps=300, extraprec=300)
    rts = sorted(rts, key=lambda z: -abs(z))
    alv = mp.re(rts[0]); rho = max(abs(z) for z in rts[1:])
    A = float(mp.log(2) / mp.log(alv) + mp.log(2) / mp.log(1 / rho))
    return c, float(alv), float(rho), A, rts

fam_rows = []; t5_ok = True
for d in (2, 3, 4, 5, 6):
    for a in sorted({2 ** d - 1, 2 ** d, 2 ** d + 1, 2 ** (d + 1)}):
        c, alv, rho, A, rts = fam(d, a)
        irr = irreducible(c)
        pis = all(abs(z) < 1 for z in rts[1:]) and abs(mp.im(rts[0])) < 1e-30
        inab = a < alv < a + 1
        rbound = rho <= (2 / a) ** (1 / (d - 1)) + 1e-12
        t5_ok &= irr and pis and inab and rbound
        if a == 2 ** (d + 1): t5_ok &= (A < 1)                       # Theorem 5(iv)
        if d in (2, 3):
            t5_ok &= (abs(rho - alv ** (-1 / (d - 1))) < 1e-12)      # exactly on the ceiling
            t5_ok &= (A < 1) == (a >= 2 ** d)                        # exact threshold
        else:
            t5_ok &= (A < 1) == (a >= 2 ** d + 1)                    # observed threshold
        fam_rows.append(dict(d=d, a=a, alpha=alv, rho=rho, A=A, irr=irr, fires=A < 1))
report('T5', t5_ok, 'family checks at %d (d,a) pairs: irreducible Pisot unit in (a,a+1), '
       'rho <= (2/a)^{1/(d-1)}; thresholds a=2^d (d=2,3, on the ceiling), a=2^d+1 (d=4,5,6)'
       % len(fam_rows))
RES['T5'] = fam_rows

# ---------------- C6: quadratic normal form ----------------
bad = 0
quads = [r for r in COV if r['d'] == 2]
for r in quads:
    b = abs(r['coeffs'][2])
    lhs = (L2(r['a']) - 1) * (L2(r['a'] / b) - 1) > 1
    if lhs != (r['A'] < 1): bad += 1
units4 = [r for r in quads if r['unit'] and ((r['A'] < 1) != (r['a'] > 4))]
report('C6', bad == 0 and not units4,
       'quadratic normal form agrees on all %d quadratics; units fire iff alpha > 4' % len(quads))

# ---------------- P7: X7 vacuity ----------------
minD = {}; minDg = 9e9
for r in COV:
    minD[r['d']] = min(minD.get(r['d'], 9e9), r['D'] - (r['d'] - 1))
    minDg = min(minDg, 2 * r['Delta'] / r['g'])
report('P7', all(v > -1e-6 for v in minD.values()) and minDg > 1,
       'diam K - (d-1) >= %s; min 2*Delta/g = %.4f > 1: X7 never fires'
       % ({d: round(v, 6) for d, v in sorted(minD.items())}, minDg))

# ---------------- P8: recoding invariance ----------------
def Arec(coeffs, p):
    """A of the recoded system: alphabet 2^p, base alpha^p, from the power polynomial itself."""
    al = Alpha(coeffs)
    with mp.workdps(60):
        alp = al.alpha ** p; rhp = max(abs(z) ** p for z in al.conj)
        return float(mp.log(2 ** p) / mp.log(alp) + mp.log(2 ** p) / mp.log(1 / rhp)), al.routeA()

POWERS = [([1, -4, 1], 2, [1, -14, 1]), ([1, -2, -1], 2, [1, -6, 1]), ([1, -2, -1], 3, [1, -14, -1])]
dev = 0.0
for c, p, cp in POWERS:
    Ap, A = Arec(c, p)
    # independent route: alpha' from the power polynomial's own roots
    alp = Alpha(cp)
    Adir = float(mp.log(2 ** p) / mp.log(alp.alpha) + mp.log(2 ** p) / mp.log(1 / alp.rho))
    dev = max(dev, abs(Ap - A), abs(Adir - A))
report('P8', dev < 1e-12, 'A(2^p, alpha^p, rho^p) = A(2, alpha, rho) at three power cases, max dev %.1e' % dev)

# ---------------- P9: X8 completeness / comparison ----------------
al23 = Alpha([1, -4, 1], '2+sqrt3')
g23, MK23, p23 = support_gaps(al23)
A23 = al23.routeA()
need_G = 4.0 / 2.0 ** cov2['log2_gap']
report('P9', g23 and g23 > 0.05 and A23 > 1,
       '2+sqrt3: A=%.3f (Route A blind) yet raster gap %.6f at %.4f; Route A\'s own effective gap '
       'at 2+sqrt5 would need G ~ 2^%.0f bins to rasterise (used: 2^21 finds %.4f)'
       % (A23, g23, p23, L2(need_G), g2))
RES['P9'] = dict(sqrt3_gap=g23, sqrt3_pos=p23, A=A23)

# ---------------- d=1 sanity ----------------
al1 = Alpha([1, -3], 'alpha=3')
gA1 = math.log(2) / math.log(3)
g1, _, _ = support_gaps(al1)
report('D0', abs(g1 - 1 / 3) < 1e-4 and gA1 < 1,
       'd=1, alpha=3: A=log2/log3=%.4f<1, raster gap %.5f (=1/3)' % (gA1, g1))

json.dump(RES, open('m2_verify.json', 'w'), indent=1, default=float)
print('\nwrote m2_verify.json')
