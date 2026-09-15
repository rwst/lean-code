#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M2 Prop. 8 -- one check per GROUP OF DECLARATIONS of BB61/BlockRecoding.lean.

Proposition 8's proof in the note is one sentence ("every p cancels"), so the thing worth
verifying is not the conclusion but every step of the translation into Lean: that the block
recoding really is the scaling action on the triple (log #alphabet, log base,
log 1/contraction); that the recoded base and contraction are alpha^p and rho^p OF THE
ACTUAL POWER POLYNOMIAL and not by fiat; that the trace ladder giving that polynomial is an
integer sequence; and that the trap the file guards against -- alpha -> alpha^p without
enlarging the alphabet -- is genuinely a different operation.

P1  traceSeq_cast                     t_n = alpha^n + beta^n from the integer recurrence
P2  power (the QuadSetup fields)      X^2 - t_p X + (-b)^p: monic, integer, alpha^p > 1,
                                      |beta^p| < 1, and alpha^p IS a root
P3  power_beta                        its SECOND root is beta^p -- the recoded contraction
P4  blockData_eq_block                (log 2^p, log alpha^p, log rho^-p) = p * the original
P5  blockRecoding_expo                PROP. 8's DISPLAY: A recomputed after recoding = A
P6  dim/entropyDeficit/mfCriterion    the plan's other three invariants, and (L,R)
P7  ratios_eq_iff                     the fibres of `ratios` ARE the rescaling orbits
                                      (and a function of the RAW triple need not be neutral)
P8  the note's own check P8           (2+sqrt3)^2, (1+sqrt2)^2, (1+sqrt2)^3 by name
P9  routeACriterion_blockData_..._four_lt   units: still exactly (4, infinity), every p
P10 routeAExponent_power (the trap)   A(alpha^p) = A(alpha)/p, and the small system is the
                                      block-constant sliver of C(alpha), properly

Everything is computed at 60 decimal digits with mpmath from the integer coefficients,
independently of `m0_coverage.json`'s stored floats.  Requires mpmath.
"""
import json, mpmath as mp

mp.mp.dps = 60
RES = {}
FAILS = 0
PS = (1, 2, 3, 4, 5, 7, 11, 12)


def report(key, ok, msg):
    global FAILS
    RES[key] = dict(ok=bool(ok), msg=msg)
    if not ok:
        FAILS += 1
    print('%-4s %s  %s' % (key, 'PASS' if ok else 'FAIL', msg))


COV = json.load(open('m0_coverage.json'))
QUAD = [r for r in COV if r['d'] == 2]


def roots_hi(coeffs):
    """(alpha, conjugates) at 60 dps, from the integer coefficients."""
    r = mp.polyroots([mp.mpf(c) for c in coeffs], maxsteps=200, extraprec=200)
    big = [z for z in r if abs(z) > 1]
    assert len(big) == 1, coeffs
    return mp.re(big[0]), [z for z in r if abs(z) <= 1]


HI = {}
for row in COV:
    HI[tuple(row['coeffs'])] = roots_hi(row['coeffs'])


def rho_hi(conj):
    return max(abs(z) for z in conj)


def expo_hi(nletters, base, contraction):
    """The abstract A = log#/log base + log#/log(1/contraction)."""
    ln = mp.log(nletters)
    return ln / mp.log(base) + ln / (-mp.log(contraction))


def ab_of(row):
    """QuadSetup (a, b) from coeffs [1, -a, -b] of X^2 - aX - b."""
    return -row['coeffs'][1], -row['coeffs'][2]


def trace_seq(a, b, n):
    """The integer ladder h_{k+2} = a h_{k+1} + b h_k from (2, a)."""
    h0, h1 = 2, a
    if n == 0:
        return h0
    for _ in range(n - 1):
        h0, h1 = h1, a * h1 + b * h0
    return h1


# ---------------- P1: t_n = alpha^n + beta^n ----------------
dev = mp.mpf(0)
for row in QUAD:
    a, b = ab_of(row)
    alpha, conj = HI[tuple(row['coeffs'])]
    beta = mp.re(conj[0])
    for n in range(0, 21):
        t = trace_seq(a, b, n)
        assert isinstance(t, int)
        scale = max(mp.mpf(1), abs(alpha) ** n)
        dev = max(dev, abs(mp.mpf(t) - alpha ** n - beta ** n) / scale)
report('P1', dev < mp.mpf('1e-45'),
       'the integer ladder from (2, a) is t_n = alpha^n + beta^n on all %d quadratics for '
       'n = 0..20, and every t_n is an int (max RELATIVE deviation %.1e)'
       % (len(QUAD), float(dev)))

# ---------------- P2: the power polynomial is a QuadSetup ----------------
bad = []
maxroot = mp.mpf(0)
for row in QUAD:
    a, b = ab_of(row)
    alpha, conj = HI[tuple(row['coeffs'])]
    beta = mp.re(conj[0])
    for p in PS:
        tp = trace_seq(a, b, p)
        bp = -((-b) ** p)
        ap = alpha ** p
        bep = beta ** p
        # monic integer quadratic, alpha^p > 1, |beta^p| < 1, alpha^p a root
        val = (ap ** 2 - mp.mpf(tp) * ap - mp.mpf(bp)) / max(mp.mpf(1), ap ** 2)
        maxroot = max(maxroot, abs(val))
        if not (isinstance(tp, int) and isinstance(bp, int) and ap > 1
                and abs(bep) < 1 and abs(val) < mp.mpf('1e-45')):
            bad.append((row['coeffs'], p))
report('P2', not bad,
       'X^2 - t_p X - (-(-b)^p) is monic with INTEGER coefficients, alpha^p > 1, '
       '|beta^p| < 1 and alpha^p is a root, on all %d quadratics x %d exponents '
       '(max RELATIVE |poly(alpha^p)| = %.1e)'
       % (len(QUAD), len(PS), float(maxroot)))

# ---------------- P3: the second root is beta^p ----------------
dev = mp.mpf(0)
devnaive = mp.mpf(0)
for row in QUAD:
    a, b = ab_of(row)
    alpha, conj = HI[tuple(row['coeffs'])]
    beta = mp.re(conj[0])
    for p in PS:
        tp = trace_seq(a, b, p)
        bp = -((-b) ** p)
        r = mp.polyroots([mp.mpf(1), mp.mpf(-tp), mp.mpf(-bp)],
                         maxsteps=200, extraprec=200)
        small = min(r, key=lambda z: abs(z))
        dev = max(dev, abs(mp.re(small) - beta ** p))
        if p > 1:
            devnaive = max(devnaive, abs(abs(mp.re(small)) - abs(beta)))
report('P3', dev < mp.mpf('1e-40') and devnaive > mp.mpf('1e-3'),
       'the power polynomial recomputed from its integer coefficients has second root '
       'beta^p (max deviation %.1e) -- and it is NOT beta (the naive reading differs by up '
       'to %.3f), which is why the note recomputes rho^p from the actual polynomial'
       % (float(dev), float(devnaive)))

# ---------------- P4: the recoding is the scaling action ----------------
dev = mp.mpf(0)
for row in COV:
    alpha, conj = HI[tuple(row['coeffs'])]
    rho = rho_hi(conj)
    base = [mp.log(2), mp.log(alpha), -mp.log(rho)]
    for p in PS:
        rec = [mp.log(mp.mpf(2) ** p), mp.log(alpha ** p), -mp.log(rho ** p)]
        for u, v in zip(rec, base):
            dev = max(dev, abs(u - mp.mpf(p) * v))
report('P4', dev < mp.mpf('1e-40'),
       '(log 2^p, log alpha^p, log 1/rho^p) = p * (log 2, log alpha, log 1/rho) on all %d '
       'Pisot x %d exponents (max deviation %.1e) -- the recoding IS the scaling action'
       % (len(COV), len(PS), float(dev)))

# ---------------- P5: Proposition 8's display ----------------
dev = mp.mpf(0)
devA = mp.mpf(0)
for row in COV:
    alpha, conj = HI[tuple(row['coeffs'])]
    rho = rho_hi(conj)
    A = expo_hi(2, alpha, rho)
    devA = max(devA, abs(A - mp.mpf(row['A'])))
    for p in PS:
        Ap = expo_hi(mp.mpf(2) ** p, alpha ** p, rho ** p)
        dev = max(dev, abs(Ap - A))
report('P5', dev < mp.mpf('1e-40') and devA < mp.mpf('1e-7'),
       'log 2^p/log alpha^p + log 2^p/log(1/rho^p) = A(alpha) on all %d Pisot x %d '
       'exponents (max deviation %.1e); the recomputed A also matches the stored column '
       'to %.1e' % (len(COV), len(PS), float(dev), float(devA)))

# ---------------- P6: the plan's other three invariants ----------------
dev = mp.mpf(0)
flips = 0
for row in COV:
    alpha, conj = HI[tuple(row['coeffs'])]
    rho = rho_hi(conj)
    la, lb, lc = mp.log(2), mp.log(alpha), -mp.log(rho)
    L0, R0, dim0 = lb / la, lc / la, la / lb
    ed0, mf0 = la < lb, la < lc
    for p in PS:
        P = mp.mpf(p)
        la2, lb2, lc2 = P * la, P * lb, P * lc
        dev = max(dev, abs(lb2 / la2 - L0), abs(lc2 / la2 - R0), abs(la2 / lb2 - dim0))
        if (la2 < lb2) != ed0 or (la2 < lc2) != mf0:
            flips += 1
nED = sum(1 for r in COV if HI[tuple(r['coeffs'])][0] > 2)
nMF = sum(1 for r in COV if rho_hi(HI[tuple(r['coeffs'])][1]) < mp.mpf('0.5'))
report('P6', dev < mp.mpf('1e-40') and flips == 0,
       'L, R and dim = log2/log alpha are invariant (max deviation %.1e) and neither the '
       'entropy deficit (%d/%d rows) nor Mendes-France rho < 1/2 (%d/%d) flips at any of '
       'the %d exponents' % (float(dev), nED, len(COV), nMF, len(COV), len(PS)))

# ---------------- P7: the fibres of `ratios` are the scaling orbits ----------------
mp.mp.dps = 40
ok = True
sep = mp.mpf(1)
trips = [(mp.mpf(1), mp.mpf(2), mp.mpf(3)), (mp.mpf(7), mp.mpf(11), mp.mpf(2)),
         (mp.log(2), mp.log(3), mp.log(5)), (mp.mpf(-1), mp.mpf(4), mp.mpf(9))]
for D in trips:
    for c in (mp.mpf(2), mp.mpf('0.5'), mp.mpf(-3), mp.mpf('1.7')):
        E = tuple(c * x for x in D)
        if abs(E[1] / E[0] - D[1] / D[0]) > mp.mpf('1e-30') or \
           abs(E[2] / E[0] - D[2] / D[0]) > mp.mpf('1e-30'):
            ok = False
    for E in trips:
        if E is D:
            continue
        same = (abs(E[1] / E[0] - D[1] / D[0]) < mp.mpf('1e-30') and
                abs(E[2] / E[0] - D[2] / D[0]) < mp.mpf('1e-30'))
        prop = all(abs(E[i] * D[0] - D[i] * E[0]) < mp.mpf('1e-30') for i in (1, 2))
        if same != prop:
            ok = False
        if not same:
            sep = min(sep, max(abs(E[1] / E[0] - D[1] / D[0]),
                               abs(E[2] / E[0] - D[2] / D[0])))
mp.mp.dps = 60
# a function of the RAW TRIPLE need not be neutral: "log base > 1" flips at 1+sqrt2
alS0, cjS0 = HI[(1, -2, -1)]
flip = (mp.log(alS0) > 1) != (2 * mp.log(alS0) > 1)
report('P7', ok and sep > mp.mpf('1e-3') and flip,
       'same (L,R) iff proportional, on %d triples x 4 scalings: scaling never changes the '
       'pair, and non-proportional triples are separated in it (min separation %.3f) -- so '
       'the fibres are exactly the recoding orbits.  A function of the RAW triple need not '
       'be neutral: "log base > 1" is false at 1+sqrt2 (log alpha = %.4f) and true after '
       'recoding at p = 2' % (len(trips), float(sep), float(mp.log(alS0))))

# ---------------- P8: the note's three named instances ----------------
NAMED = [
    ('(2+sqrt3)^2', 4, -1, 2, 14, -1, mp.mpf(7) + 4 * mp.sqrt(3)),
    ('(1+sqrt2)^2', 2, 1, 2, 6, -1, mp.mpf(3) + 2 * mp.sqrt(2)),
    ('(1+sqrt2)^3', 2, 1, 3, 14, 1, mp.mpf(7) + 5 * mp.sqrt(2)),
]
dev = mp.mpf(0)
names_ok = True
for name, a, b, p, ta, ba, alpow in NAMED:
    alpha, conj = roots_hi([1, -a, -b])
    beta = mp.re(conj[0])
    tp, bp = trace_seq(a, b, p), -((-b) ** p)
    if (tp, bp) != (ta, ba):
        names_ok = False
    dev = max(dev, abs(alpha ** p - alpow))
    # A recomputed from the POWER polynomial's own roots, with alphabet 2^p
    al2, cj2 = roots_hi([1, -tp, -bp])
    Ap = expo_hi(mp.mpf(2) ** p, al2, rho_hi(cj2))
    dev = max(dev, abs(Ap - expo_hi(2, alpha, rho_hi(conj))))
report('P8', names_ok and dev < mp.mpf('1e-40'),
       'the three instances are exactly X^2-14X+1, X^2-6X+1, X^2-14X-1 with roots '
       '7+4sqrt3, 3+2sqrt2, 7+5sqrt2, and A recomputed from each power polynomial\'s OWN '
       'roots (alphabet 2^p) equals A(alpha) (max deviation %.1e)' % float(dev))

# ---------------- P9: units still fire exactly on (4, infinity) ----------------
units = [r for r in QUAD if abs(r['coeffs'][2]) == 1]
bad = []
for row in units:
    alpha, conj = HI[tuple(row['coeffs'])]
    rho = rho_hi(conj)
    for p in PS:
        fires = expo_hi(mp.mpf(2) ** p, alpha ** p, rho ** p) < 1
        if fires != (alpha > 4):
            bad.append((row['coeffs'], p))
nfire = sum(1 for r in units if HI[tuple(r['coeffs'])][0] > 4)
report('P9', not bad,
       'on the %d quadratic units the recoded criterion fires iff alpha > 4, at every one '
       'of the %d exponents (%d fire, %d do not -- 1+sqrt2 and 2+sqrt3 among them): the '
       'G-R freedom buys Route A not one new alpha' % (len(units), len(PS), nfire,
                                                       len(units) - nfire))

# ---------------- P10: the trap ----------------
dev = mp.mpf(0)
for row in QUAD:
    alpha, conj = HI[tuple(row['coeffs'])]
    rho = rho_hi(conj)
    A = expo_hi(2, alpha, rho)
    for p in PS:
        dev = max(dev, abs(expo_hi(2, alpha ** p, rho ** p) - A / p))
# at 1+sqrt2 the binary system at base alpha^p fires from p = 2 on, though Route A does not
alS, cjS = roots_hi([1, -2, -1])
rhoS = rho_hi(cjS)
AS = expo_hi(2, alS, rhoS)
pmin = min(p for p in range(1, 30) if expo_hi(2, alS ** p, rhoS ** p) < 1)


def pival(al, word, M=400):
    return (al - 1) * mp.fsum(mp.mpf(word[k]) * al ** (-(k + 1)) for k in range(M))


# the base-alpha^p binary Cantor set is the block-constant sliver of C(alpha)
import random
random.seed(11)
devc = mp.mpf(0)
for p in (2, 3, 5):
    for _ in range(12):
        eps = [random.randint(0, 1) for _ in range(120)]
        blk = [eps[j // p] for j in range(120 * p)]
        devc = max(devc, abs(pival(alS ** p, eps, 120) - pival(alS, blk, 120 * p)))
# and properly: the word 1,0,0,... of C(alpha) is far from every depth-14 point of C(alpha^2)
target = pival(alS, [1] + [0] * 200, 200)
tail = alS ** (-14)
best = min(abs(target - pival(alS, [w[j // 2] for j in range(28)] + [0] * 100, 128))
           for w in [[(k >> i) & 1 for i in range(14)] for k in range(1 << 14)])
report('P10', dev < mp.mpf('1e-40') and pmin == 2 and devc < mp.mpf('1e-30')
       and best > 10 * tail,
       'A(alpha^p) = A(alpha)/p exactly (max deviation %.1e); at 1+sqrt2, where Route A '
       'provably does not fire (A = %.4f), the binary system at base alpha^p fires from '
       'p = %d on -- because it is the BLOCK-CONSTANT sliver of C(alpha) (identity to '
       '%.1e) and a proper one (the word 10^inf sits %.1e away, tail bound %.1e)'
       % (float(dev), float(AS), pmin, float(devc), float(best), float(tail)))

print()
print('%d/%d checks OK at mp.dps = %d' % (len(RES) - FAILS, len(RES), mp.mp.dps))
json.dump(RES, open('m2_prop8_lean.json', 'w'), indent=1)
