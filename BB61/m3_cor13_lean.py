#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M3 Cor. 13 -- one check per GROUP OF DECLARATIONS of BB61/EntropyBudget.lean.

Corollary 13 says the Ledrappier-Young entropy floor decides no alpha that Route A does not
already decide.  In Lean it is an identity between two constants that had never met in the
repository: `QuadSetup.routeAExponent` (BB61/Criterion.lean) and `LY.hMin`
(CITED/LedrappierYoung.lean).  These checks recompute both from the polynomial, at 60 digits,
over the 42 candidates of m0_gapsweep.json -- the same sweep M3 sec 10 ran at 200 dps.

C1  routeAExponent_eq_log_two_mul     both constants, recomputed from the roots, against the
    hMin_eq_inv_add_inv               stored `routeA` column of the sweep
C2  routeAExponent_mul_hMin           the identity A(alpha) * h_min(alpha) = log 2
C3  routeAExponent_lt_one_iff_        Corollary 13 itself: A < 1 <=> log 2 < h_min, zero
    log_two_lt_hMin                   exceptions over all 42 (M3 Lemma 2's claim)
C4  zero_lt_entropyBudget_iff         the budget log 2 - h_min is > 0 exactly where Route A
                                      fails, and its size at the named alpha
C5  log_two_lt_hMin_iff_four_lt_      at a quadratic unit h_min = (1/2) log alpha, so the
    of_unit                           threshold is alpha > 4
C6  routeAExponent_lt_one_iff_        the two lanes cross at the same point: A(4) = 1 and
    four_lt_of_floor                  h_min(4) = log 2 on the unit family, to 50 digits

Requires mpmath.
"""
import json

import mpmath as mp

mp.mp.dps = 60

RES = {}
FAILS = 0


def report(key, ok, msg):
    global FAILS
    RES[key] = dict(ok=bool(ok), msg=msg)
    if not ok:
        FAILS += 1
    print('%-4s %s  %s' % (key, 'PASS' if ok else 'FAIL', msg))


LOG2 = mp.log(2)


def roots_of(coeffs):
    """alpha (the root > 1) and rho = max modulus of the other roots, at 60 digits."""
    rs = mp.polyroots([mp.mpf(c) for c in coeffs], maxsteps=200, extraprec=200)
    big = [r for r in rs if abs(mp.im(r)) < mp.mpf('1e-40') and mp.re(r) > 1]
    al = max(mp.re(r) for r in big)
    rest = [r for r in rs if abs(r - al) > mp.mpf('1e-40')]
    rho = max(abs(r) for r in rest)
    return al, rho


def routeA(al, rho):
    """QuadSetup.routeAExponent = log 2 / log alpha + log 2 / log (1/rho)."""
    return LOG2 / mp.log(al) + LOG2 / mp.log(1 / rho)


def hMin(al, rho):
    """LY.hMin = (1 / log alpha + 1 / log (1/rho))^-1."""
    return 1 / (1 / mp.log(al) + 1 / mp.log(1 / rho))


rows = json.load(open('m0_gapsweep.json'))
data = []
for rw in rows:
    al, rho = roots_of(rw['coeffs'])
    data.append(dict(row=rw, al=al, rho=rho, A=routeA(al, rho), h=hMin(al, rho)))

# C1: the two constants, recomputed from the roots
d1 = max(abs(e['al'] - mp.mpf(e['row']['alpha'])) for e in data)
d2 = max(abs(e['rho'] - mp.mpf(e['row']['rho'])) for e in data)
d3 = max(abs(e['A'] - mp.mpf(e['row']['routeA'])) for e in data)
report('C1', len(data) == 42 and d1 < mp.mpf('1e-12') and d2 < mp.mpf('1e-12')
       and d3 < mp.mpf('1e-12'),
       'both constants recomputed from the roots of all %d candidates at %d dps; agreement '
       'with the stored float64 columns: alpha %.2e, rho %.2e, routeA %.2e'
       % (len(data), mp.mp.dps, float(d1), float(d2), float(d3)))

# C2: the identity A * h_min = log 2
dev = max(abs(e['A'] * e['h'] - LOG2) for e in data)
report('C2', dev < mp.mpf('1e-50'),
       'A(alpha) * h_min(alpha) = log 2 on all %d candidates; worst deviation %.2e at %d dps '
       '-- an identity, not a coincidence: A is log 2 times the sum whose inverse is h_min'
       % (len(data), float(dev), mp.mp.dps))

# C3: Corollary 13
exc = [e for e in data if (e['A'] < 1) != (LOG2 < e['h'])]
fire = [e for e in data if e['A'] < 1]
report('C3', len(exc) == 0,
       'A < 1 <=> log 2 < h_min on all %d candidates, %d exceptions (Route A fires at %d of '
       'them, and the floor exceeds log 2 at exactly the same %d)'
       % (len(data), len(exc), len(fire), len(fire)))

# C4: the budget, and its size at the named alpha
excb = [e for e in data if (0 < LOG2 - e['h']) != (1 < e['A'])]
named = {}
for e in data:
    p = e['row']['poly']
    if p in ('X^2-2X-1', 'X^2-4X+1', 'X^2-3X+1'):
        named[p] = (float(e['al']), float(e['h']), float(LOG2 - e['h']), float(e['A']))
report('C4', len(excb) == 0 and all(v[2] > 0 for v in named.values()),
       'the budget log 2 - h_min is positive exactly where Route A fails, %d exceptions; '
       'at 1+sqrt2 (%s) budget %.6f, at 2+sqrt3 (%s) budget %.6f, at (3+sqrt5)/2 (%s) budget '
       '%.6f -- all three positive, so all three are out of Route A'
       % (len(excb),
          'X^2-2X-1', named['X^2-2X-1'][2],
          'X^2-4X+1', named['X^2-4X+1'][2],
          'X^2-3X+1', named['X^2-3X+1'][2]))

# C5: at a quadratic unit h_min = (1/2) log alpha, threshold alpha > 4
units = [e for e in data if e['row']['d'] == 2 and abs(e['row']['coeffs'][2]) == 1]
dhalf = max(abs(e['h'] - mp.log(e['al']) / 2) for e in units) if units else mp.mpf(0)
excu = [e for e in units if (LOG2 < e['h']) != (e['al'] > 4)]
above = sorted(float(e['al']) for e in units if e['al'] > 4)
report('C5', len(units) > 0 and dhalf < mp.mpf('1e-50') and len(excu) == 0,
       'on the %d quadratic units of the sweep h_min = (1/2) log alpha to %.2e, and '
       'log 2 < h_min <=> alpha > 4 with %d exceptions; the smallest unit above 4 is '
       '%.6f (2+sqrt5)' % (len(units), float(dhalf), len(excu),
                           above[0] if above else float('nan')))

# C6: both lanes cross at alpha = 4
al4 = mp.mpf(4)
rho4 = 1 / al4                      # a unit has rho = 1/alpha
A4 = routeA(al4, rho4)
h4 = hMin(al4, rho4)
report('C6', abs(A4 - 1) < mp.mpf('1e-50') and abs(h4 - LOG2) < mp.mpf('1e-50'),
       'on the unit locus rho = 1/alpha the two criteria cross at the same point: A(4) = %s '
       '(deviation %.2e) and h_min(4) = log 2 (deviation %.2e) -- the threshold of M2 Prop. 1 '
       'and the threshold of the entropy floor are one number'
       % (mp.nstr(A4, 12), float(abs(A4 - 1)), float(abs(h4 - LOG2))))

print()
print('%d/%d checks OK at mp.dps = %d' % (len(RES) - FAILS, len(RES), mp.mp.dps))
json.dump(RES, open('m3_cor13_lean.json', 'w'), indent=1)
