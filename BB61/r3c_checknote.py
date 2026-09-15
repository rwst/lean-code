#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# CC0 1.0 Universal (public domain dedication).
"""Read the numbers back OUT of `note-1061-R3c.html` and check them against the run.

Same role as `r3a_checknote.py` and `r3b_checknote.py`.  Every table row and quoted
constant is parsed out of the HTML and matched against `r3c_kantorovich.json`, or
recomputed here from `r3c_kantorovich.py` / `r3a_degree.py`.

Usage:  python3 r3c_checknote.py
"""
import json
import math
import os
import re
import sys

BB = os.path.dirname(os.path.abspath(__file__))
NOTE = os.path.join(os.path.dirname(BB), 'note-1061-R3c.html')
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


def one(txt):
    v = allnums(txt)
    return v[0] if v else None


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
    run = json.load(open(os.path.join(BB, 'r3c_kantorovich.json')))
    grid = {(r['d'], r['H']): r for r in run['grid'] if r['certified']}

    import mpmath as mp
    from r3a_degree import Field, FAMILY
    import r3c_kantorovich as C

    F = {d: Field(FAMILY[d - 2]) for d in (2, 3, 4)}
    hmin = {}
    for d, f in F.items():
        la, lr = math.log(float(f.alpha)), math.log(1 / float(f.rho))
        hmin[d] = la * lr / (la + lr)

    print('== 4. the certified frontier ==')
    fr = rows(section(note, 'frontier'))[1:]
    chk('the frontier table has one row per certified rung',
        len(fr) == len(grid), '%d rows vs %d certified' % (len(fr), len(grid)))
    seen = set()
    for row in fr:
        c = cells(row)
        d, H, L, K = int(one(c[0])), int(one(c[2])), int(one(c[3])), int(one(c[5]))
        r = grid.get((d, H))
        seen.add((d, H))
        chk('d=%d H=%d is a certified row of the run' % (d, H), r is not None)
        if r is None:
            continue
        chk('  d=%d H=%d: alpha to ten digits' % (d, H),
            close(one(c[1]), float(F[d].alpha), 1e-10), c[1].strip())
        chk('  d=%d H=%d: L and the arithmetic' % (d, H),
            L == r['L'] and r.get('prec', 'ld') in c[4], '%s' % c[4].strip())
        chk('  d=%d H=%d: K is F.need at the 1e-30 window' % (d, H),
            K == r['K'] and K == sum(F[d].need(H, mp.mpf('1e-30'))) + 1, 'K=%d' % K)
        chk('  d=%d H=%d: ||Phi|| = residual + radius' % (d, H),
            close(one(c[6]), r['nres'] + r['nrad'], 2e-2))
        for j, key in ((7, 'smin'), (8, 'eta'), (9, 'rho'), (10, 'kappa')):
            chk('  d=%d H=%d: %s' % (d, H, key), close(one(c[j]), r[key], 2e-2),
                '%s vs %.4e' % (c[j].strip(), r[key]))
        chk('  d=%d H=%d: kappa is below 1/2, as Theorem D needs' % (d, H), r['kappa'] <= 0.5)
        chk('  d=%d H=%d: h(mu) lower bound' % (d, H),
            close(one(c[11]), r['entropy_lo'], 1e-6))
    chk('the frontier table lists every certified rung', seen == set(grid))

    print('== 5. E_H from one measure ==')
    en = rows(section(note, 'entropy'))[1:]
    prev = {16: 0.689054, 32: 0.687024, 64: 0.677794, 128: 0.605736, 256: 0.582936}
    upp = {16: 0.689241, 32: 0.687695, 128: 0.683077, 256: 0.683077}
    for row in en:
        c = cells(row)
        H = int(one(c[1]))
        poly = re.sub(r'<[^>]+>', '', c[0]).strip()
        d = {2: 'X^2-2X-1', 3: 'X^3-2X^2-1', 4: 'X^4-2X^3-1'}
        dd = [k for k, v in d.items() if v == poly]
        chk('entropy row polynomial %s is in the family' % poly, len(dd) == 1)
        if not dd:
            continue
        dd = dd[0]
        r = grid.get((dd, H))
        chk('  d=%d H=%d: the entropy matches the frontier' % (dd, H),
            r is not None and close(one(c[2]), r['entropy_lo'], 1e-6))
        chk('  d=%d H=%d: h_min is the Ledrappier-Young floor' % (dd, H),
            close(one(c[5]), hmin[dd], 1e-5), '%s vs %.9f' % (c[5].strip(), hmin[dd]))
        chk('  d=%d H=%d: the margin is the difference' % (dd, H),
            close(one(c[6]), one(c[2]) - one(c[5]), 1e-4))
        if dd == 2 and H in prev:
            chk('  H=%d: the previous lower bound is the folder\'s' % H,
                close(one(c[3]), prev[H], 1e-6), c[3].strip())
        if dd == 2 and H in upp:
            chk('  H=%d: the upper bound is R2c\'s' % H, close(one(c[4]), upp[H], 1e-6))
        if dd == 2 and H in prev and r:
            better = r['entropy_lo'] > prev[H]
            chk('  H=%d: the note\'s claim of who wins is right' % H,
                (H >= 64) == better, 'new %.6f vs old %.6f' % (r['entropy_lo'], prev[H]))

    print('== 6. what binds ==')
    sm = rows(section(note, 'binds'))
    hdr = cells(sm[0])
    Hs = [int(one(x)) for x in hdr[1:]]
    for row in sm[1:]:
        c = cells(row)
        d = int(one(c[0]))
        for j, H in enumerate(Hs):
            txt = c[j + 1]
            if '&mdash;' in txt:
                chk('  d=%d H=%d has no certified row, and the table says so' % (d, H),
                    (d, H) not in grid)
                continue
            v = allnums(txt)
            r = grid.get((d, H))
            chk('  d=%d H=%d: s_min and L' % (d, H),
                r is not None and close(v[0], r['smin'], 2e-2) and int(v[1]) == r['L'],
                txt.strip())

    print('== the verdict box and the prose ==')
    vd = section(note, 'verdict')
    r2 = grid.get((2, 128))
    if r2:
        chk('(b) the verdict quotes the certified entropy at d=2, H=128',
            ('%.6f' % r2['entropy_lo']) in vd, '%.6f' % r2['entropy_lo'])
        chk('(b) and the pool number it is measured against', '0.605736' in vd)
        w_old, w_new = 0.683077 - 0.605736, 0.683077 - r2['entropy_lo']
        nums = allnums(vd)
        chk('(b) the two bracket widths', any(close(x, w_old, 2e-3) for x in nums)
            and any(close(x, w_new, 2e-3) for x in nums),
            'old %.4e new %.4e' % (w_old, w_new))
        mf = re.search(r'a factor \\\(([0-9]+)\\\)', section(note, 'entropy'))
        chk('(b) the factor between them, as sec 5 states it',
            mf is not None and int(mf.group(1)) == round(w_old / w_new),
            'note %s, ratio %.2f' % (mf.group(1) if mf else '?', w_old / w_new))
    mq = re.search(r'floor \\\(h_\{\\min\}\\\) by \\\(([0-9.]+)\\\) and \\\(([0-9.]+)\\\)', vd)
    chk('(b) the verdict quotes two margins over h_min', mq is not None)
    for d, key in zip((3, 4), (float(x) for x in (mq.groups() if mq else ('0', '0')))):
        rr = [g for (dd, H), g in grid.items() if dd == d]
        best = max(g['entropy_lo'] - hmin[d] for g in rr) if rr else None
        worst = min(g['entropy_lo'] - hmin[d] for g in rr) if rr else None
        chk('(b) the d=%d margin is a valid bound for EVERY rung, and is not slack' % d,
            worst is not None and worst - 1e-3 <= key <= worst + 1e-9,
            'quoted %.4f, run [%.4f, %.4f]' % (key, worst or 0, best or 0))
    for d, kdeep, kfast in ((2, 175, 87), (3, 296, 148), (4, 486, 244)):
        got_deep = sum(F[d].need(128, mp.mpf('1e-30'))) + 1
        got_fast = sum(F[d].need(128, mp.mpf('1e-13'))) + 1
        chk('  d=%d: K = %d at 1e-30 and %d at 1e-13' % (d, kdeep, kfast),
            got_deep == kdeep and got_fast == kfast, '%d / %d' % (got_deep, got_fast))
    chk('3.3 the two kappa values quoted for the longdouble Jacobian at d=4, H=16',
        all(x in vd + section(note, 'inputs') for x in ('1.57\\cdot10^{-3}', '9.32\\cdot10^{-7}')))
    r416 = grid.get((4, 16))
    chk('  and the second is the run\'s kappa there',
        r416 is not None and close(r416['kappa'], 9.32e-7, 3e-3),
        '%.4e' % (r416['kappa'] if r416 else float('nan')))

    inp = section(note, 'inputs')
    chk('3.2 the crude Doeblin bound at L=14, m=0.2 is what the note quotes',
        any(close(x, 0.4 ** 14, 2e-2) for x in allnums(inp)), '%.3e' % 0.4 ** 14)
    import numpy as np
    dp = C.doeblin_const(0.5 + 0.15 * np.cos(np.arange(1 << 12)), 12)
    chk('3.2 the exact Doeblin DP beats the crude bound at a perturbed point',
        dp > 5 * 0.7 ** 12, 'DP %.4e vs crude %.4e, x%.1f' % (dp, 0.7 ** 12, dp / 0.7 ** 12))
    chk('3.4 the window is taken at 2 pi H eps <= 1e-30',
        all(2 * math.pi * r['H'] * r['eps'] <= 1e-30 for r in run['grid']),
        'worst %.2e' % max(2 * math.pi * r['H'] * r['eps'] for r in run['grid']))

    print('== structural claims ==')
    chk('h_min at d=2 is the folder\'s 0.440687', close(hmin[2], 0.440686794, 1e-8))
    chk('the family degenerates to 2 from above',
        float(F[2].alpha) > float(F[3].alpha) > float(F[4].alpha) > 2)
    chk('h_min falls with the degree', hmin[2] > hmin[3] > hmin[4])
    chk('every certified kappa is below 1/2 and every rho is tiny',
        all(g['kappa'] <= 0.5 and g['rho'] < 1e-8 for g in grid.values()))
    chk('every certified point is interior (positivity holds on the box)',
        all(g['positive'] for g in grid.values()))
    chk('every certified entropy clears its own Ledrappier-Young floor',
        all(g['entropy_lo'] > hmin[d] for (d, H), g in grid.items()))
    chk('the caps are the ones sec 3.2 quotes',
        all(close(g['cap'], 0.30 if d == 2 else 0.25, 1e-9) for (d, H), g in grid.items()))
    chk('Corollary D-prime is consistent with the run: 4 Lambda_1 Vinf ||Phi|| / s_min^2 <= 1',
        all(g['crit'] <= 1 for g in grid.values()),
        'worst %.3e' % max(g['crit'] for g in grid.values()))

    print('\n%d claims verified, %d failed' % (len(OK), OK.count(False)))
    return 0 if all(OK) else 1


if __name__ == '__main__':
    sys.exit(main())
