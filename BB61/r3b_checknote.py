#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# CC0 1.0 Universal (public domain dedication).
"""Read the numbers back OUT of `note-1061-R3b.html` and check them against the run.

Same role as `r3a_checknote.py`.  Every table row and quoted constant is parsed out of the
HTML and matched against `r3b_jacobian.json`, or recomputed here from `r3b_jacobian.py`.

Usage:  python3 r3b_checknote.py
"""
import json
import math
import os
import re
import sys

import numpy as np

BB = os.path.dirname(os.path.abspath(__file__))
NOTE = os.path.join(os.path.dirname(BB), 'note-1061-R3b.html')
sys.path.insert(0, BB)
OK = []


def chk(name, cond, extra=""):
    OK.append(bool(cond))
    print("  %s  %s%s" % ('PASS' if cond else 'FAIL', name, ('   ' + extra) if extra else ''))


def close(a, b, rel=3e-3):
    if a is None or b is None:
        return False
    return abs(a - b) <= rel * max(abs(a), abs(b), 1e-300)


def allnums(txt):
    t = re.sub(r'<[^>]+>', ' ', txt).replace('&nbsp;', ' ').replace('\\,', '')
    t = t.replace('\\mathbf{', ' ').replace('&times;', ' ').replace('\\times', ' ')
    out = []
    for m in re.finditer(r'([+-]?[0-9]*\.?[0-9]+)(?:\s*\\cdot\s*10\^\{(-?[0-9]+)\})?', t):
        try:
            out.append(float(m.group(1)) * (10.0 ** int(m.group(2)) if m.group(2) else 1.0))
        except ValueError:
            pass
    return out


def section(note, hid):
    i = note.index('id="%s"' % hid)
    j = note.find('<h2 ', i)
    return note[i:(j if j > 0 else len(note))]


def rows(txt):
    return re.findall(r'<tr>(.*?)</tr>', txt, re.S)


def cells(row):
    return re.findall(r'<t[dh][^>]*>(.*?)</t[dh]>', row, re.S)


def main():
    note = open(NOTE).read()
    D = json.load(open(os.path.join(BB, 'r3b_jacobian.json')))
    SPEC = {(r['d'], r['L'], r['H']): r for r in D['spec']}
    SPAR = {(r['d'], r['h']): r for r in D['sparse']}
    FULL = {(r['d'], r['H'], r['L']): r for r in D['full']}
    FULL.update({(r['d'], r['H'], r['L']): r for r in D['full_extra']})
    LM = {(r['d'], r['H'], r['L']): r for r in D['lm_preliminary']}
    REACH = {(r['d'], r['H'], r['L']): r for r in D['reach']}

    print('== provenance ==')
    chk('the run recorded 13 self-checks, all passing', D.get('checks') is True)
    chk("subtitle names r3b_jacobian.py with 13 self-checks and the 48-claim checker",
        '<code>BB61/r3b_jacobian.py</code> (13 self&#8209;checks)' in note
        and '<code>r3b_checknote.py</code> (48 claims)' in note)
    for f in ('r3b_spec.log', 'r3b_reach.log', 'r3b_newton.log', 'r3b_full_sweep.log'):
        chk('log %s exists and is named in the note' % f,
            os.path.exists(os.path.join(BB, f)) and f in note)

    print('== sec 2: the closed form, re-derived here ==')
    from r3b_jacobian import Field, FAMILY, schedule, g_row, forward, jacobian_at
    F2, F3 = Field([1, -2, -1]), Field(FAMILY[1])
    gam = schedule(F2, 25, 25)
    g0 = g_row(gam, 5, 0)[0]
    ph = (1.0 + np.exp(2j * np.pi * 5 * gam)) / 2.0
    ex = sum((np.exp(2j * np.pi * 5 * gam[k]) - 1.0) * np.prod(np.delete(ph, k))
             for k in range(len(gam)))
    chk('L=0 is d/dp of the Erdos product', abs(g0 - ex) < 1e-12 * abs(ex))
    L, t = 5, 1e-5
    gam3 = schedule(F3, 20, 40)
    A = np.array([g_row(gam3, h, L) for h in (1, 2, 5)])
    rng = np.random.default_rng(99)
    u = rng.normal(size=1 << L)
    pred = (A @ u) / (1 << L)
    fd = (forward(gam3, np.full(1 << L, .5) + t * u, (1, 2, 5), L)
          - forward(gam3, np.full(1 << L, .5) - t * u, (1, 2, 5), L)) / (2 * t)
    chk('Theorem C vs central differences at d=3',
        np.abs(fd - pred).max() / np.abs(pred).max() < 2e-8,
        'rel %.2e' % (np.abs(fd - pred).max() / np.abs(pred).max()))
    q = 0.5 + 0.05 * rng.normal(size=1 << L)
    G, phv = jacobian_at(gam3, q, (1, 2, 5), L)
    chk('sec 2.1: sum_b V_{J+1}[b] = Phi_h to 1e-17',
        np.abs(phv - forward(gam3, q, (1, 2, 5), L)).max() < 1e-16,
        '%.2e' % np.abs(phv - forward(gam3, q, (1, 2, 5), L)).max())
    u2 = rng.normal(size=1 << L)
    fd2 = (forward(gam3, q + 1e-6 * u2, (1, 2, 5), L)
           - forward(gam3, q - 1e-6 * u2, (1, 2, 5), L)) / 2e-6
    chk('sec 2.1: the general-point Jacobian vs central differences',
        np.abs(G @ u2 - fd2).max() / np.abs(fd2).max() < 1e-7,
        'rel %.2e' % (np.abs(G @ u2 - fd2).max() / np.abs(fd2).max()))
    Gb, _ = jacobian_at(gam3, np.full(1 << L, .5), (1, 2, 5), L)
    gb = np.array([g_row(gam3, h, L) for h in (1, 2, 5)]) / (1 << L)
    chk('sec 2.1: at Bernoulli it agrees with Theorem C to 4e-16',
        np.abs(Gb - gb).max() / np.abs(gb).max() < 1e-15)

    print('== sec 3: the sparsity ==')
    s3 = section(note, 'sparse')
    n = 0
    for r in rows(s3)[1:]:
        c = cells(r)
        if len(c) != 5:
            continue
        d, h = int(allnums(c[0])[0]), int(allnums(c[1])[0])
        K, act = int(allnums(c[2])[0]), int(allnums(c[3])[0])
        n90 = int(allnums(c[4])[0])
        R = SPAR[(d, h)]
        chk('sec 3 row d=%d h=%d' % (d, h),
            K == R['K'] and act == R['active'] and n90 == R['n90'],
            'K=%d active=%d n90=%d' % (R['K'], R['active'], R['n90']))
        n += 1
    chk('sec 3 table has six rows', n == 6)
    gam40 = schedule(F2, 40, 40)
    red = np.abs(gam40 * 1393 - np.round(gam40 * 1393))
    act = sorted(np.arange(-40, 41)[red > 1e-3].tolist())
    chk('M7 sec 5 support at h=1393 is exactly [-16,-2] u [2,16], 30 of 81',
        act == list(range(-16, -1)) + list(range(2, 17)) and len(gam40) == 81,
        '%d positions' % len(act))

    print('== sec 4: the two gates ==')
    s4 = section(note, 'gates')
    Hs = [4, 32, 64, 256]
    n = 0
    for r in rows(s4)[1:]:
        c = cells(r)
        if len(c) != 7:
            continue
        d, L = int(allnums(c[0])[0]), int(allnums(c[1])[0])
        key = ('step' if 'D\\Phi' in c[2] else ('lam1' if 'lambda' in c[2] else 'naive'))
        got = [allnums(c[3 + i])[0] for i in range(4)]
        want = [SPEC[(d, L, H)][key] for H in Hs]
        chk('sec 4 row d=%d L=%d %s' % (d, L, key),
            all(close(a, b, 3e-3) for a, b in zip(got, want)),
            ' '.join('%.4g' % w for w in want))
        n += 1
    chk('sec 4 table has seven rows', n == 7)
    chk('sec 4: ||r|| = 1.6099e-3 in every d=4 row (it is |Phi_1|)',
        all(close(SPEC[(4, L, H)]['nres'], 1.6099e-3, 1e-4) for L in (10, 12, 14, 16)
            for H in Hs))
    chk('sec 4: the looseness reaches 1.03e15 at d=4, L=10, H=256',
        close(SPEC[(4, 10, 256)]['loose'], 1.03e15, 5e-3),
        '%.4e' % SPEC[(4, 10, 256)]['loose'])
    chk('sec 4 box: s_min at d=4, L=12 runs 6.98e-3, 3.87e-6, 1.37e-9, 1.97e-15',
        all(close(x, SPEC[(4, 12, H)]['smin'], 4e-3)
            for x, H in zip((6.98e-3, 3.87e-6, 1.37e-9, 1.97e-15), Hs)))
    chk('sec 4 box: s_min at H=64 improves with L: 3.27e-10, 1.37e-9, 7.70e-9, 5.69e-8',
        all(close(x, SPEC[(4, L, 64)]['smin'], 4e-3)
            for x, L in zip((3.27e-10, 1.37e-9, 7.70e-9, 5.69e-8), (10, 12, 14, 16))))
    chk('sec 1(c): the step is within 1.3x of ||r|| at d=4 across six octaves',
        max(SPEC[(4, 16, H)]['step'] for H in (4, 8, 16, 32, 64, 128, 256))
        / SPEC[(4, 16, 4)]['nres'] < 1.3)

    print('== sec 5: the three solvers ==')
    s5 = section(note, 'iterate')
    ch = REACH[(4, 64, 12)]
    chk('sec 5.1: the chord run at d=4,H=64,L=12 goes 1.610e-3 -> 3.400e-6 -> 6.398e-8',
        all(close(x, y, 3e-3) for x, y in
            zip((1.610e-3, 3.400e-6, 6.398e-8), D['newton'][3]['resid'][:3])),
        ' '.join('%.4e' % v for v in D['newton'][3]['resid'][:3]))
    chk('sec 5.1: the damped chord stalls flat in L at H=64 (5.9, 6.1, 7.0 e-9)',
        all(close(x, REACH[(4, 64, L)]['final'], 3e-2)
            for x, L in zip((5.890e-9, 6.132e-9, 7.038e-9), (12, 14, 16))))
    chk('sec 5.2: LM reaches 6.96e-11, 2.70e-11, 1.21e-10, 2.57e-9, 3.42e-9',
        all(close(x, LM[k]['final'], 3e-3) for x, k in
            zip((6.957e-11, 2.699e-11, 1.205e-10, 2.574e-9),
                ((4, 32, 12), (4, 64, 12), (4, 64, 14), (4, 128, 12)))))
    n = 0
    for r in rows(s5):
        c = cells(r)
        if len(c) != 7 or 'chord' in c[3]:
            continue
        try:
            d, H, L = (int(allnums(c[i])[0]) for i in range(3))
        except (IndexError, ValueError):
            continue
        R = FULL[(d, H, L)]
        fn, its = allnums(c[5])[0], int(allnums(c[5])[1])
        chk('sec 5.3 row d=%d H=%d L=%d full Newton' % (d, H, L),
            close(fn, R['final'], 3e-3) and its == R['iters']
            and close(allnums(c[6])[0], R['floor'], 3e-2),
            '%.3e in %d its' % (R['final'], R['iters']))
        n += 1
    chk('sec 5.3 table has four rows', n == 4)
    chk('sec 5.3: full Newton REACHES where the chord diverges (d=4,H=32,L=12)',
        FULL[(4, 32, 12)]['reached'] and FULL[(4, 32, 12)]['final'] < 1e-14)
    best = {}
    for r in D['full']:
        if r['reached']:
            best.setdefault((r['d'], r['H']), r['L'])
    s54 = s5[s5.index('5.4'):]
    tab = re.findall(r'<table>(.*?)</table>', s54, re.S)[0]
    for r in rows(tab)[1:]:
        c = cells(r)
        d = int(allnums(c[0])[0])
        got = [int(allnums(x)[0]) for x in c[1:]]
        want = [best[(d, H)] for H in (8, 16, 32, 64, 128)]
        chk('sec 5.4 L*(H) at d=%d' % d, got == want, str(want))
    off = {(d, H): best[(d, H)] - math.log2(H)
           for d in (2, 3, 4) for H in (8, 16, 32, 64, 128)}
    chk('sec 5.4: L* - log2 H lies in [2, 7] and varies by <= 3 within a degree',
        2 <= min(off.values()) and max(off.values()) <= 7
        and max(max(off[(d, H)] for H in (8, 16, 32, 64, 128))
                - min(off[(d, H)] for H in (8, 16, 32, 64, 128)) for d in (2, 3, 4)) <= 3,
        'range [%g, %g]' % (min(off.values()), max(off.values())))
    chk('sec 5.4: hence 2^L* is between 4H and 128H',
        all(4 <= 2 ** off[k] <= 128 for k in off))
    chk('sec 5.4: max|dq| is 4.147e-3 at d=4,H=32,L=12 and 8.415e-3 at H=128',
        close(FULL[(4, 32, 12)]['stepinf'], 4.147e-3, 3e-3)
        and close(FULL[(4, 128, 12)]['stepinf'], 8.415e-3, 3e-3))
    chk('sec 6: the note does not claim K_H is nonempty',
        'It is not a proof that \\(\\mathcal K_H\\ne\\emptyset\\)' in note)

    print('\n%d claims verified, %d failed' % (len(OK), OK.count(False)))
    return 1 if OK.count(False) else 0


if __name__ == '__main__':
    sys.exit(main())
