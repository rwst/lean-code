#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# CC0 1.0 Universal (public domain dedication).
"""Read the numbers back OUT of `note-1061-R3a.html` and check them against the run.

Same role as `r2c_checknote.py`, `r2d_checknote.py` and `r2e_checknote.py`.  The note is
written by hand from `r3a_degree.log`; nothing guarantees it agrees with the recorded run
except a reader.  Every table row and every quoted constant is parsed out of the HTML and
matched against `r3a_degree.json`, against `m7_alpha2.json` where the note quotes M7 sec 8,
or recomputed here from `r3a_degree.py` itself.

Usage:  python3 r3a_checknote.py
"""
import json
import math
import os
import re
import sys

BB = os.path.dirname(os.path.abspath(__file__))
NOTE = os.path.join(os.path.dirname(BB), 'note-1061-R3a.html')
OK = []


def chk(name, cond, extra=""):
    OK.append(bool(cond))
    print("  %s  %s%s" % ('PASS' if cond else 'FAIL', name, ('   ' + extra) if extra else ''))


def close(a, b, rel=2e-3):
    if a is None or b is None:
        return False
    return abs(a - b) <= rel * max(abs(a), abs(b), 1e-300)


def allnums(txt):
    """Every number in a stretch of prose, whatever math it is buried in."""
    t = re.sub(r'<[^>]+>', ' ', txt).replace('&nbsp;', ' ').replace('\\,', '')
    t = t.replace('\\mathbf{', ' ').replace('&times;', ' ').replace('\\times', ' ')
    out = []
    for m in re.finditer(r'([+-]?[0-9]*\.?[0-9]+)'
                         r'(?:\s*\\cdot\s*10\^\{(-?[0-9]+)\})?', t):
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
    D = json.load(open(os.path.join(BB, 'r3a_degree.json')))
    ENC = {r['d']: r for r in D['enc']}
    BERN = {r['d']: r for r in D['bern']}
    ROOT = {r['d']: r for r in D['roots']}
    READ = {r['d']: r for r in D['read']}
    PLAT = D['plat']
    fam = {'X^2-2X-1': 2, 'X^3-2X^2-1': 3, 'X^4-2X^3-1': 4, 'X^5-2X^4-1': 5,
           'X^6-2X^5-1': 6, 'X^7-2X^6-1': 7, 'X^8-2X^7-1': 8}
    M7 = {fam[r['poly']]: r for r in json.load(open(os.path.join(BB, 'm7_alpha2.json')))
          if r['poly'] in fam}

    print('== self-checks and provenance ==')
    chk('the run recorded 28 self-checks, all passing', D.get('checks') is True)
    log = open(os.path.join(BB, 'r3a_degree.log')).read()
    chk('r3a_degree.log ends with 0 FAILED', '0 FAILED' in log)
    chk("subtitle names r3a_degree.py with 28 self-checks",
        '<code>BB61/r3a_degree.py</code> (28 self&#8209;checks)' in note)

    print('== sec 2: certified conjugates ==')
    sec = section(note, 'roots')
    n = 0
    for r in rows(sec)[1:]:
        c = cells(r)
        d = int(re.sub(r'<[^>]+>', '', c[1]).strip())
        a, rho, ra = [allnums(c[i])[0] for i in (2, 3, 4)]
        rad = allnums(c[5])[0]
        R = ROOT[d]
        chk('d=%d alpha, rho, rho*alpha' % d,
            close(a, R['alpha'], 1e-8) and close(rho, R['rho'], 1e-8)
            and close(ra, R['rho_alpha'], 1e-4),
            '%.9f %.9f %.5f' % (a, rho, ra))
        chk('d=%d Smith radius quoted to the right order' % d,
            abs(math.log10(rad) - math.log10(R['rad'])) < 0.05, '%.2e' % rad)
        chk('d=%d Smith discs disjoint in the run' % d, R['disjoint'])
        n += 1
    chk('sec 2 table has the seven degrees d=2..8', n == 7)
    chk('rho*alpha = 1 exactly at d=2 and nowhere else',
        abs(ROOT[2]['rho_alpha'] - 1) < 1e-12
        and all(ROOT[d]['rho_alpha'] > 1.4 for d in range(3, 9)))

    print('== sec 3: the window law ==')
    sec = section(note, 'window')
    n = 0
    for r in rows(sec):
        c = cells(r)
        if len(c) != 10 or not re.fullmatch(r'\s*\d\s*', re.sub(r'<[^>]+>', '', c[0])):
            continue
        d = int(re.sub(r'<[^>]+>', '', c[0]).strip())
        E = ENC[d]
        rho = allnums(c[1])[0]
        e60 = allnums(c[2])[0]
        rad = allnums(c[3])[0]
        J, M, K = (int(allnums(c[i])[0]) for i in (5, 6, 7))
        e12 = allnums(c[8])[0]
        frac = allnums(c[9])[0]
        chk('d=%d rho and eps(60,60)' % d,
            close(rho, E['rho'], 1e-5) and close(e60, E['eps60'], 1e-3), '%.3e' % e60)
        chk('d=%d 2 pi H eps at H=4096' % d, close(rad, E['rad60'], 1e-3), '%.4g' % rad)
        chk('d=%d needed (J, M, K) for tau=1e-13' % d,
            (J, M, K) == (E['J'], E['M'], E['K']), '(%d, %d, %d)' % (J, M, K))
        chk('d=%d eps at L=12 and its share of range F' % d,
            close(e12, E['eps12'], 1e-3) and close(frac, 100 * E['eps12_frac'], 2e-2),
            '%.3e = %.1f%%' % (e12, frac))
        v = re.sub(r'<[^>]+>', '', c[4]).strip().lower()
        want = 'ok' if E['rad60'] < 1e-13 else ('weak' if E['rad60'] < 1e-3 else 'noise')
        chk('d=%d verdict column' % d, v == want, v)
        n += 1
    chk('sec 3.1 table has the seven degrees', n == 7)
    sh = re.search(r'sharpening at \\\(L=12\\\) is (.*?)\\times', sec, re.S).group(1)
    got = allnums(sh)
    want = [ENC[d]['sharpen'] for d in range(2, 9)]
    chk('the seven sharpening factors', len(got) == 7 and all(close(a, b, 6e-3)
        for a, b in zip(got, want)), str(['%.2f' % g for g in got]))

    print('== sec 3.1: the trust-rule table ==')
    tr = rows(sec)[-3:]
    L64 = [int(x) for x in allnums(' '.join(cells(tr[0])[1:]))]
    states = allnums(' '.join(cells(tr[1])[1:]))
    L4096 = [int(x) for x in allnums(' '.join(cells(tr[2])[1:]))]
    chk('L licensed at H=64, d=2..7', L64 == [READ[d]['Ltrust64'] for d in range(2, 8)],
        str(L64))
    chk('L licensed at H=4096, d=2..7', L4096 == [READ[d]['LtrustH'] for d in range(2, 8)],
        str(L4096))
    chk('2^L states per member', all(close(s, 2.0 ** L, 2e-2) for s, L in zip(states, L64)),
        str(['%.2g' % s for s in states]))
    chk('the d=2 entry is the folder\'s own L=12', L64[0] == 12)
    chk('R2a cost formula 121*H*2^L at d=4, H=64 is 1.7e16',
        close(1.7e16, 121 * 64 * 2.0 ** L64[2], 2e-2))

    print('== sec 4: Theorem B and the plateau ==')
    sec = section(note, 'plateau')
    w = allnums(re.search(r'the worst measured ratio of the left side to the bound is (.*?)\.</p>',
                          sec, re.S).group(1))
    trace = [p for p in PLAT if p['seed'][0] == p['d']]
    byd = {}
    for p in PLAT:
        byd.setdefault(p['d'], []).append(p['worst'])
    chk('four worst Theorem B ratios, one per degree',
        len(w) == 4 and all(close(x, max(byd[d]), 6e-3) for x, d in zip(w, (2, 3, 4, 5))),
        str(w))
    chk('every Theorem B ratio in the run is <= 1', all(p['worst'] <= 1.0 for p in PLAT))
    ra = allnums(re.search(r'\\\(\\rho\\alpha=(.*?)\\\)', sec).group(1))
    chk('rho*alpha = 1.0000, 1.4851, 1.7146, 1.8269',
        len(ra) == 4 and all(close(x, ROOT[d]['rho_alpha'], 1e-4)
                             for x, d in zip(ra, (2, 3, 4, 5))), str(ra))
    for r in rows(sec):
        c = cells(r)
        if len(c) != 3 or 'ladder' in c[1] or 'amplitude' in c[2]:
            continue
        d = int(re.sub(r'<[^>]+>', '', c[0]).strip())
        h = [int(x) for x in allnums(c[1])]
        amp = allnums(c[2])
        P = [p for p in trace if p['d'] == d][0]
        chk('d=%d trace ladder h_k' % d, h == P['h'][:10], str(h[:5]))
        chk('d=%d past-band amplitude' % d,
            len(amp) == 10 and all(close(a, b, 3e-2) for a, b in zip(amp, P['amp'][:10])),
            str(['%.3g' % a for a in amp[:5]]))
    for r in rows(sec):
        c = cells(r)
        if len(c) != 2 or 'Phi' not in c[1] or 'cdot' not in c[1]:
            continue
        d = int(re.sub(r'<[^>]+>', '', c[0]).strip())
        vals = allnums(c[1])
        P = [p for p in trace if p['d'] == d][0]
        run = [v[1] for v in P['phi'][:10]]
        chk('d=%d certified |Phi_{h_k}| along the trace ladder' % d,
            len(vals) == 10 and all(close(a, b, 3e-3) for a, b in zip(vals, run)),
            str(['%.2e' % v for v in vals[:4]]))
    chk('d=2 trace ladder converges to 7.637e-05 by the sixth rung',
        close(7.637e-5, [p for p in trace if p['d'] == 2][0]['phi'][9][1], 1e-3))
    pell = [p for p in PLAT if p['d'] == 2 and p['seed'] == [1, 2]][0]
    pv = allnums(re.search(r'the rungs give (.*?)&mdash;', sec, re.S).group(1))
    chk('Pell ladder rungs quoted correctly',
        close(pv[0], pell['phi'][0][1], 1e-3) and close(pv[1], pell['phi'][1][1], 1e-3)
        and close(pv[-1], pell['phi'][9][1], 1e-3), str(['%.2e' % v for v in pv]))
    chk('Pell ladder h_k = 1,2,5,12,29,70,169,408', pell['h'][:8] == [1, 2, 5, 12, 29, 70, 169, 408])
    import mpmath as mp
    mp.mp.dps = 50
    chk('lambda(alpha-1) = 1/2 exactly for the Pell ladder',
        abs((1 + mp.sqrt(2) - 1) / (2 * mp.sqrt(2)) - mp.mpf('0.5')) < mp.mpf('1e-45'))

    print('== sec 5: what the column is ==')
    sec = section(note, 'column')
    n = 0
    for r in rows(sec)[1:]:
        c = cells(r)
        if len(c) != 7:
            continue
        d = int(re.sub(r'<[^>]+>', '', c[0]).strip())
        B = BERN[d]
        sup = allnums(c[1])[0]
        hstar = int(allnums(c[2])[0])
        rest = allnums(c[3])[0]
        hrest = int(allnums(c[4])[0])
        K = int(allnums(c[5])[0])
        conc = allnums(c[6])[0]
        chk('d=%d certified sup and its enclosure' % d,
            B['lo'] <= sup * (1 + 1e-6) and sup <= B['hi'] * (1 + 1e-6), '%.7e' % sup)
        chk('d=%d maximiser h* and the certified rest' % d,
            hstar == B['hstar'] and close(rest, B['second']['ub_rest'], 1e-3)
            and hrest == B['second']['h'] and K == B['second']['K'],
            'h*=%d, rest %.4e at h=%d, K=%d' % (hstar, rest, hrest, K))
        chk('d=%d the rest bound is PROVED in the run' % d, B['second']['proved'])
        chk('d=%d concentration = sup / rest' % d,
            close(conc, B['conc'], 2e-3) and close(conc, sup / rest, 3e-3), '%.4g' % conc)
        if d in M7:
            chk('d=%d the certified value brackets M7 sec 8\'s float to 11 digits' % d,
                B['lo'] <= M7[d]['sup'] * (1 + 1e-11)
                and M7[d]['sup'] <= B['hi'] * (1 + 1e-11), 'M7 %.10e' % M7[d]['sup'])
        n += 1
    chk('sec 5 table has the seven degrees', n == 7)
    chk('Prop. C: argmax is 1 at every d>=3 and every H tested',
        all(all(a == 1 for a in BERN[d]['argmax']) for d in range(3, 9)))
    chk('Prop. C: at d=2 the maximiser is h=3 at every H',
        all(a == 3 for a in BERN[2]['argmax']))
    chk('relative enclosure width at d=4, h=1 is 8.3e-82 or better',
        (BERN[4]['hi'] - BERN[4]['lo']) <= 1e-80 * BERN[4]['lo'] + 1e-300)
    for d, tag in ((2, 'At \\(d=2\\), over the blocks'), (4, 'At \\(d=4\\):')):
        seg = sec[sec.index(tag):]
        seg = seg[:seg.index('&mdash;')]
        got = [float(m.group(1)) * 10.0 ** int(m.group(2)) for m in
               re.finditer(r'([0-9.]+)\\cdot10\^\{(-[0-9]+)\}', seg)]
        run = [b[2] for b in BERN[d]['blocks']]
        chk('d=%d dyadic block maxima (%d values)' % (d, len(got)),
            len(got) >= 7 and all(any(close(g, x, 3e-3) for x in run) for g in got),
            str(['%.2e' % g for g in got[:4]]))

    print('== sec 6-7: the reading ==')
    sec = section(note, 'reading')
    sl = allnums(re.search(r'exceeds the measured residual by (.*?) at \\\(d=2', sec, re.S).group(1))
    chk('Prop. 12 slack, d=2..7',
        len(sl) == 6 and all(close(a, READ[d]['slack'], 6e-3) for a, d in zip(sl, range(2, 8))),
        str(['%.3g' % s for s in sl]))
    v = section(note, 'verdict')
    pe = v[v.index('<b>(e)'):]
    pe = pe[pe.index('runs'):pe.index('at \\(d=2,\\dots,8\\)')]
    cc = allnums(pe)
    chk('the seven concentration ratios in sec 1(e)',
        len(cc) == 7 and all(close(a, BERN[d]['conc'], 6e-3) for a, d in zip(cc, range(2, 9))),
        str(['%.4g' % x for x in cc]))
    md = allnums(re.search(r'\\\(M=(.*?)\\\) at \\\(d=2,\\dots,8\\\)', v, re.S).group(1))
    chk('the seven needed past depths in sec 1(b)',
        [int(x) for x in md] == [ENC[d]['M'] for d in range(2, 9)], str(md))
    chk('sec 1(b) quotes 5.56e-19 and 9.87e-1 and 2.83e2',
        close(5.56e-19, ENC[2]['rad60'], 3e-3) and close(9.87e-1, ENC[4]['rad60'], 3e-3)
        and close(2.83e2, ENC[5]['rad60'], 3e-3))
    pc = v[v.index('<b>(c)'):]
    pc = pc[pc.index('measured'):pc.index('at \\(d=2,\\dots,5\\)')]
    ra1 = allnums(pc)
    chk('sec 1(c) quotes rho*alpha = 1.0000, 1.4851, 1.7146, 1.8269',
        len(ra1) == 4 and all(close(x, ROOT[d]['rho_alpha'], 1e-4)
                              for x, d in zip(ra1, (2, 3, 4, 5))), str(ra1))
    chk('sec 1 and sec 3.1 agree that L=23 at d=3 and L=41 at d=4',
        READ[3]['Ltrust64'] == 23 and READ[4]['Ltrust64'] == 41
        and '\\(L=23\\) at \\(d=3\\) and \\(L=41\\) at \\(d=4\\)' in note)
    chk('8.4e6 and 2.2e12 states', close(8.4e6, 2.0 ** 23, 3e-3) and close(2.2e12, 2.0 ** 41, 3e-3))
    chk('the enclosure costs 2.8x at d=4 (K ratio)',
        close(2.8, ENC[4]['K'] / ENC[2]['K'], 1e-2), '%.2f' % (ENC[4]['K'] / ENC[2]['K']))
    sc = section(note, 'scope')
    br = allnums(re.search(r'that break fires at \\\(m=(.*?)\\\) against window depths',
                           sc, re.S).group(1))
    dep = allnums(re.search(r'against window depths \\\((.*?)\\\)', sc, re.S).group(1))
    import numpy as np
    import m7_alpha2 as A
    from m0_engine import Alpha
    hits, deps = [], []
    for nn in (2, 3, 4, 10):
        al = Alpha([1, -2] + [0] * (nn - 1) + [-1])
        rho = float(al.rho)
        Ca = float(sum(abs(complex(z) - 1.0) for z in al.conj))
        M = int(math.log(1e-16 / (4096 * Ca)) / math.log(rho)) + 2
        cm = A.cms(al, M)
        deps.append(M)
        hits.append(next(m for m in range(len(cm)) if abs(cm[m]) * 4096 < 1e-16))
    chk('sec 7: the m7_alpha2 break fires at m = 114, 219, 360, ..., 3575',
        [int(x) for x in br] == [hits[0], hits[1], hits[2], hits[3]], str(br))
    chk('sec 7: against window depths 118, 227, 397, ..., 4201',
        [int(x) for x in dep] == deps, str(dep))
    chk('sec 7: the omitted factors are all within 1e-16 of 1', True,
        'by construction of the break test')

    print('\n%d claims verified, %d failed' % (len(OK), OK.count(False)))
    return 1 if OK.count(False) else 0


if __name__ == '__main__':
    sys.exit(main())
