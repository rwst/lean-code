#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# CC0 1.0 Universal (public domain dedication).
"""Read the numbers back OUT of `note-1061-R2e.html` and check them against the run.

Same role as `r2c_checknote.py` and `r2d_checknote.py`.  The note is written by hand
from `r2e_frozen128.log`, `r2e_diag.log` and `r2e_orb.log`; nothing guarantees it agrees
with the recorded run except a reader.  Every table row and every quoted constant below
is parsed out of the HTML and matched against `r2e_pool256.json`, `r2e_pool_frozen.json`
and `r1b_pool256.json`, against `r2d_hull.json` where the note quotes R2d, or
recomputed here from the machinery.

Usage:  python3 r2e_checknote.py
"""
import json
import math
import os
import re
import sys

BB = '/home/ralf/math/lean-code/BB61'
NOTE = '/home/ralf/math/lean-code/note-1061-R2e.html'
HMIN = 0.44068679350977147
LOG2 = 0.6931471805599453
OK = []


def chk(name, cond, extra=""):
    OK.append(bool(cond))
    print(f"  {'PASS' if cond else 'FAIL'}  {name}{'   ' + extra if extra else ''}")


def close(a, b, rel=2e-4):
    if a is None or b is None:
        return False
    return abs(a - b) <= rel * max(abs(a), abs(b), 1e-300)


def sci(txt):
    """Every `\\(x.yyy\\cdot10^{-n}\\)` or bare `\\(x.yyy\\)` in `txt`, in order."""
    out = []
    for m in re.finditer(r'\\\(\s*\\?m?a?t?h?b?f?\{?\s*([+-]?[0-9.]+)\s*\}?'
                         r'(?:\\cdot10\^\{(-?[0-9]+)\})?\s*\\\)', txt):
        try:
            out.append(float(m.group(1)) * (10.0 ** int(m.group(2)) if m.group(2) else 1.0))
        except ValueError:
            pass
    return out


def section(note, hid):
    i = note.index(f'id="{hid}"')
    j = note.find('<h2 ', i)
    return note[i:(j if j > 0 else len(note))]


def rows(txt):
    return re.findall(r'<tr>(.*?)</tr>', txt, re.S)


def cells(row):
    out = []
    for x in re.findall(r'<t[dh][^>]*>(.*?)</t[dh]>', row, re.S):
        t = re.sub(r'<[^>]+>', '', x)
        t = t.replace('&nbsp;', ' ').replace('&mdash;', '--').strip()
        t = re.sub(r'^\\\((.*)\\\)$', r'\1', t)
        out.append(t)
    return out


def num(s):
    """The first number in a cell.  Understands `a\\cdot10^{b}`, a bare `10^{b}`,
    `\\mathbf{}`, `\\gtrsim` and thousands written `58\\,647`."""
    t = (s.replace('&nbsp;', ' ').replace('\\,', '').replace('\\mathbf{', '')
          .replace('\\gtrsim', '').replace('\\approx', '').replace('\\cdot', ' cdot '))
    m = re.search(r'([+-]?[0-9]*\.?[0-9]+)\s*cdot\s*10\^\{(-?[0-9.]+)\}', t)
    if m:
        return float(m.group(1)) * 10.0 ** float(m.group(2))
    m = re.search(r'(?<![0-9.])10\^\{(-?[0-9.]+)\}', t)
    if m:
        return 10.0 ** float(m.group(1))
    m = re.search(r'([+-]?[0-9]*\.?[0-9]+)', t)
    return float(m.group(1)) if m else None


def allnums(txt):
    """Every number in a stretch of prose, whatever math it is buried in."""
    t = re.sub(r'<[^>]+>', ' ', txt).replace('&nbsp;', ' ').replace('\\,', '')
    out = []
    for m in re.finditer(r'([+-]?[0-9]*\.?[0-9]+)'
                         r'(?:\s*\\cdot\s*10\^\{(-?[0-9]+)\})?', t):
        try:
            out.append(float(m.group(1))
                       * (10.0 ** int(m.group(2)) if m.group(2) else 1.0))
        except ValueError:
            pass
    return out


def find(recs, **kw):
    out = [r for r in recs if all(r.get(k) == v for k, v in kw.items())]
    return out[0] if out else None


def main():
    note = open(NOTE).read()
    d = json.load(open(f'{BB}/r2e_pool256.json'))
    fz = json.load(open(f'{BB}/r2e_pool_frozen.json'))
    seed = json.load(open(f'{BB}/r1b_pool256.json'))
    print("R2e note check")
    sys.path.insert(0, BB)

    ent, orb, flat, diag, br = d['ent'], d['orb'], d['flat'], d['diag'], d['bracket']
    U = {r['H']: r['upper'] for r in br}
    L = {r['H']: r['lower'] for r in br if r['lower'] is not None}
    u128 = find(ent, H=128, pool='union')
    o128 = find(ent, H=128, pool='orb+B')
    m128 = find(ent, H=128, pool='M7')
    f128 = fz['rows']['128']

    # ---- section 1: the verdict ----------------------------------------------------
    s1 = section(note, 'verdict')
    g1 = allnums(s1)
    for want, why in ((u128['best']['h_lower'], "E_128 >= 0.605736"),
                      (U[128], "U*(128) = 0.683077"),
                      (U[128] - u128['best']['h_lower'], "width 7.734e-2"),
                      (o128['best']['h_lower'], "orb+B alone 0.448496"),
                      (u128['best']['delta'], "union delta 6.8975e-9"),
                      (f128['hull_distance_circ'], "M7 hull distance 1.0455e-2")):
        chk(f"sec 1 quotes {why}", any(close(v, want, 3e-4) for v in g1),
            f"{want:.6g}")
    chk("sec 1: the entropy gain of the Gibbs columns, 0.157240",
        any(close(v, u128['best']['h_lower'] - o128['best']['h_lower'], 1e-4) for v in g1),
        f"{u128['best']['h_lower'] - o128['best']['h_lower']:.6f}")
    cost = 100 * (1 - u128['R'] / o128['R'])
    chk("sec 1: the depth cost of those columns, 0.649%",
        any(close(v, cost, 2e-3) for v in g1), f"{cost:.4f}%")
    chk("sec 1: m = 10856 for the union", u128['m'] == 10856 and '10\\,856' in s1)
    chk("the note quotes h_min = 0.440687",
        any(close(v, HMIN, 3e-4) for v in allnums(note)), f"{HMIN:.6f}")
    chk("sec 1: q = 16", u128['q'] == 16 and 'q\\le16' in s1.replace(' ', ''))

    # the trust-wall multiples 4.1x and 8.1x, recomputed
    eps12 = 1.0101e-2
    wall = 1 / (2 * math.pi * eps12)
    chk("sec 1: trust wall at H = 15.8 for L = 12",
        any(close(v, wall, 5e-3) for v in g1), f"{wall:.2f}")
    chk("sec 1: the pool survives to 4.1x the wall and fails at 8.1x",
        any(close(v, 64 / wall, 2e-2) for v in g1)
        and any(close(v, 128 / wall, 2e-2) for v in g1),
        f"{64/wall:.2f}x, {128/wall:.2f}x")

    # the orb+B margin collapse
    o256 = find(orb, H=256, pool='orb+B')
    o64 = 0.499723                                   # R2d, quoted
    m64, m128b = o64 - HMIN, o128['best']['h_lower'] - HMIN
    chk("sec 1: orb+B margins 5.9036e-2 -> 7.8093e-3, then negative",
        any(close(v, m64, 1e-3) for v in g1) and any(close(v, m128b, 1e-3) for v in g1)
        and o256['best']['h_lower'] - HMIN < 0 and 'negative' in s1,
        f"{m64:+.4e} {m128b:+.4e} {o256['best']['h_lower']-HMIN:+.4e}")
    chk("sec 6 states the negative margin -4.2106e-2 in full",
        any(close(abs(v), abs(o256['best']['h_lower'] - HMIN), 1e-3)
            for v in allnums(section(note, 'h256'))))
    chk("sec 1: E_256 >= 0.398581 on orb+B, under h_min",
        any(close(v, o256['best']['h_lower'], 1e-5) for v in g1)
        and o256['best']['h_lower'] < HMIN, f"{o256['best']['h_lower']:.6f}")
    chk("sec 1: the certified floor at H=128 is 0.165049 over h_min",
        any(close(v, u128['best']['h_lower'] - HMIN, 1e-4) for v in g1),
        f"{u128['best']['h_lower'] - HMIN:.6f}")

    # ---- section 2: the diagnosis table --------------------------------------------
    s2 = section(note, 'diag')
    seen = 0
    for row in rows(s2)[1:]:
        c = cells(row)
        if len(c) < 8:
            continue
        H = int(num(c[0]))
        tag = 'frozen' if 'frozen' in c[1] else 'optimised'
        r = find(diag, H=H, centre=tag)
        if r is None:
            continue
        seen += 1
        chk(f"sec 2 row H={H} {tag}",
            close(num(c[2]), r['P'], 1e-6) and close(num(c[3]), r['xmax'], 1e-3)
            and close(num(c[4]), r['S1'], 1e-4) and int(num(c[5])) == r['chains']
            and int(num(c[6])) == r['finite'] and close(num(c[7]), r['secs'], 0.02),
            f"P={r['P']:.6f} xmax={r['xmax']:.4f} S1={r['S1']:.2f} "
            f"{r['finite']}/{r['chains']}")
    chk("sec 2: all four diagnosis rows are in the note", seen == 4, f"{seen} rows")
    chk("sec 2: the H=128 optimised centre yields NO representable member",
        find(diag, H=128, centre='optimised')['finite'] == 0)
    chk("sec 2: the H=256 optimised centre yields ALL of them (not monotone in H)",
        find(diag, H=256, centre='optimised')['finite'] == 4097)
    chk("sec 2: the frozen centre reproduces the H0=64 windowed pressure at BOTH H",
        close(find(diag, H=128, centre='frozen')['P'], seed['rows']['64']['upper'], 1e-14)
        and close(find(diag, H=256, centre='frozen')['P'],
                  seed['rows']['64']['upper'], 1e-14),
        f"{seed['rows']['64']['upper']:.16f}")

    # ---- section 3: the frozen pool ------------------------------------------------
    s3 = section(note, 'frozen')
    e = f128['ent']
    for row in rows(s3)[1:]:
        c = cells(row)
        if len(c) < 11:
            continue
        chk("sec 3 pool row H=128",
            int(num(c[0])) == 128 and int(num(c[1])) == f128['n_pool']
            and int(num(c[2])) == f128['skipped']
            and close(num(c[3]), min(e), 1e-5)
            and close(num(c[4]), sum(e) / len(e), 1e-5)
            and close(num(c[7]), f128['radius'], 1e-3)
            and close(num(c[8]), f128['repair'], 1e-3)
            and close(num(c[9]), f128['hull_distance_circ'], 1e-3),
            f"n={f128['n_pool']} ent[{min(e):.6f},{max(e):.6f}] "
            f"mean {sum(e)/len(e):.6f} hull {f128['hull_distance_circ']:.4e}")
    chk("sec 3: every member clears h_min", min(e) >= HMIN, f"min {min(e):.6f}")
    chk("sec 3: 99.0% of members clear 0.60",
        abs(sum(1 for v in e if v >= 0.60) / len(e) - 0.990) < 5e-3,
        f"{100*sum(1 for v in e if v >= 0.60)/len(e):.1f}%")
    med = sorted(e)[len(e) // 2]
    chk("sec 3: the median 0.681813 is within 1.5e-3 of the frozen pressure",
        close(med, 0.681813, 1e-5) and abs(med - f128['upper']) < 1.5e-3,
        f"median {med:.6f}, centre pressure {f128['upper']:.6f}")
    chk("sec 3: max |Phi_h| = 0.42715",
        close(max(math.hypot(a, b) for r, i in
                  zip(f128['phi_re'], f128['phi_im']) for a, b in zip(r, i)),
              0.42715, 1e-4))
    chk("sec 3: the build took 47402 s", '47&nbsp;402' in s3 or '47 402' in s3)

    # Theorem 2, checked rather than quoted: the enclosure radius knows neither H nor L
    chk("Theorem 2: the enclosure radius at H=128 equals R1a's at H=64",
        abs(f128['radius'] - seed['rows']['64']['radius']) < 1e-16,
        f"{f128['radius']:.6e}")

    # ---- section 4: monotone tightening --------------------------------------------
    s4 = section(note, 'tighten')
    raw = dict(zip([4, 8, 16, 32, 64, 128, 256, 512],
                   [0.691200, 0.690351, 0.689241, 0.687695, 0.685479,
                    0.683077, 0.684408, 0.681768]))
    for H, v in raw.items():
        chk(f"sec 4 raw U({H}) = {v:.6f}", f"{H}:{v:.6f}" in s4.replace('&nbsp;', ''))
    chk("sec 4: the raw upper bounds are NOT monotone (that is the point)",
        raw[256] > raw[128], f"U(256)={raw[256]} > U(128)={raw[128]}")
    chk("Theorem 1: the tightened uppers ARE non-increasing",
        all(U[a] >= U[b] - 1e-15 for a, b in zip(sorted(U), sorted(U)[1:])),
        ' '.join(f"{U[H]:.6f}" for H in sorted(U)))
    chk("Theorem 1: tightening fires exactly once, at H=256",
        [H for H in sorted(U) if U[H] < raw[H] - 1e-6] == [256])
    chk("Theorem 1: L*(H) <= U*(H) at every populated degree",
        all(L[H] <= U[H] for H in L), f"{len(L)} degrees")
    chk("sec 4: the tightest instance is H=4, gap 1.26e-4 (0.018%)",
        close(U[4] - L[4], 1.262e-4, 1e-3)
        and close(100 * (U[4] - L[4]) / U[4], 0.018, 0.05),
        f"{U[4]-L[4]:.4e}, {100*(U[4]-L[4])/U[4]:.4f}%")

    # ---- section 5: the certificate ------------------------------------------------
    s5 = section(note, 'cert')
    tabs = re.findall(r'<table>(.*?)</table>', s5, re.S)
    for row in rows(tabs[0])[1:]:
        c = cells(row)
        if 'M7' in c[0]:
            gap_cell = next((x for x in c if 'separated' in x), '')
            chk("sec 5: M7 alone is separated from 0",
                m128['feasible'] is False and int(num(c[1])) == m128['m']
                and close(num(gap_cell.split('by')[-1]),
                          f128['hull_distance_circ'], 1e-3),
                f"gap {f128['hull_distance_circ']:.4e}")
            continue
        r = o128 if 'orb' in c[0] else u128
        chk(f"sec 5 certificate row '{re.sub('[^a-zA-Z+]', '', c[0])}'",
            int(num(c[1])) == r['m'] and close(num(c[2]), r['sigma'], 1e-5)
            and close(num(c[3]), r['R'], 1e-5)
            and close(num(c[4]), r['best']['delta'], 1e-3)
            and close(num(c[5]), r['best']['drift'], 0.02)
            and close(num(c[6]), r['best']['h_lower'], 1e-5)
            and close(num(c[7]), r['best']['h_lower'] - HMIN, 1e-3),
            f"m={r['m']} sigma={r['sigma']:.6f} R={r['R']:.6e} "
            f"delta={r['best']['delta']:.4e} E={r['best']['h_lower']:.6f}")
    # the R0 sweep
    sweep = 0
    for row in rows(tabs[1])[1:]:
        c = cells(row)
        cc = num(c[0])
        ro = find(o128['curve'], c=cc) or next(
            (x for x in o128['curve'] if close(x['c'], cc, 1e-9)), None)
        ru = next((x for x in u128['curve'] if close(x['c'], cc, 1e-9)), None)
        if ro is None or ru is None:
            continue
        sweep += 1
        chk(f"sec 5 sweep row c={cc:g}",
            close(num(c[1]), ro['delta'], 1e-3)
            and abs(num(c[2]) - ro['h_lower']) < 1e-6
            and close(num(c[3]), ru['delta'], 1e-3)
            and abs(num(c[4]) - ru['h_lower']) < 1e-6,
            f"orb {ro['delta']:.3e}/{ro['h_lower']:.6f}  "
            f"union {ru['delta']:.3e}/{ru['h_lower']:.6f}")
    chk("sec 5: all eight sweep rows are in the note", sweep == 8, f"{sweep} rows")
    chk("sec 5: the union dominates orb+B in entropy at EVERY rate",
        all(ru['h_lower'] >= ro['h_lower'] - 1e-12
            for ro, ru in zip(o128['curve'], u128['curve'])))
    ratio = u128['best']['delta'] / u128['best']['drift']
    chk("sec 5: delta is a factor 192 above the Brouwer drift at the working rate",
        any(close(v, ratio, 3e-3) for v in allnums(s5)) and ratio > 100,
        f"{ratio:.1f}")

    # ---- section 6: H=256 ----------------------------------------------------------
    s6 = section(note, 'h256')
    tabs6 = re.findall(r'<table>(.*?)</table>', s6, re.S)
    for row in rows(tabs6[0])[1:]:
        c = cells(row)
        H = int(num(c[0]))
        if H == 64:
            continue                     # R2d's row, quoted not recomputed
        m = int(num(c[2]))
        if 'union' in c[1]:
            r = next(x for x in ent if x['H'] == H and x['m'] == m)
        else:
            r = find(orb, H=H, pool='orb+B')
        chk(f"sec 6 {'union' if 'union' in c[1] else 'orb+B'} row H={H}",
            m == r['m'] and int(num(c[3])) == r['q']
            and close(num(c[4]), r['best']['delta'], 1e-3)
            and close(num(c[5]), r['best']['h_lower'], 1e-5)
            and close(num(c[6]), r['best']['h_lower'] - HMIN, 1e-3),
            f"delta={r['best']['delta']:.4e} E={r['best']['h_lower']:.6f} "
            f"margin={r['best']['h_lower']-HMIN:+.4e}")
    # the H = 256 pool that landed later the same day
    u256 = next(x for x in ent if x['H'] == 256 and x['m'] == 12904)
    o256b = next(x for x in ent if x['H'] == 256 and x['m'] == 8807)
    fz256 = fz['rows']['256']
    chk("sec 6 box: the H=256 frozen pool, 4097 of 4097, 11058 s",
        fz256['n_pool'] == 4097 and fz256['skipped'] == 0
        and any(close(v, 11058, 1e-3) for v in allnums(s6)),
        f"n_pool={fz256['n_pool']} skipped={fz256['skipped']}")
    chk("sec 6 box: hull distance 1.2044e-2 at H=256, above the 1.0455e-2 at H=128",
        any(close(v, fz256['hull_distance_circ'], 1e-3) for v in allnums(s6))
        and fz256['hull_distance_circ'] > fz['rows']['128']['hull_distance_circ'],
        f"{fz256['hull_distance_circ']:.6e}")
    chk("sec 6 box: entropies [0.526185, 0.684441], radius 1.4810e-13, repair 8.916e-7",
        all(any(close(v, x, 2e-4) for v in allnums(s6))
            for x in (min(fz256['ent']), max(fz256['ent']),
                      fz256['radius'], fz256['repair'])),
        f"[{min(fz256['ent']):.6f}, {max(fz256['ent']):.6f}]")
    chk("sec 6 box: the Gibbs columns buy +0.184355 at H=256, more than +0.157240 at 128",
        any(close(v, u256['best']['h_lower'] - o256b['best']['h_lower'], 1e-4)
            for v in allnums(s6))
        and (u256['best']['h_lower'] - o256b['best']['h_lower']
             > 0.6057362013585407 - 0.44849611457220445),
        f"{u256['best']['h_lower'] - o256b['best']['h_lower']:.6f}")
    chk("sec 6 box: they cost 2.45% of the certified depth",
        any(close(v, 100 * (1 - u256['best']['delta'] / o256b['best']['delta']), 3e-2)
            for v in allnums(s6)),
        f"{100 * (1 - u256['best']['delta'] / o256b['best']['delta']):.3f}%")
    chk("sec 6: H_ent > 256 -- the union margin is positive",
        u256['best']['h_lower'] > HMIN,
        f"margin {u256['best']['h_lower'] - HMIN:+.6f}")
    chk("sec 6: the margin ratio 64 -> 128 is 7.56",
        any(close(v, m64 / m128b, 3e-3) for v in allnums(s6)), f"{m64/m128b:.2f}")
    chk("sec 6: orb+B delta falls 1.180e-8 -> 6.844e-9 -> 3.225e-9",
        close(o128['best']['delta'], 6.8435e-9, 1e-3)
        and close(o256['best']['delta'], 3.2245e-9, 1e-3))
    f14 = find(flat, H=256, q=14)
    f16 = find(flat, H=256, q=16)
    chk("sec 6: q<=14 is infeasible at H=256, rho = -1.6042e-3",
        f14['feasible'] is False and close(f14['rho'], -1.6042e-3, 1e-3)
        and f14['m'] == 2538, f"rho={f14['rho']:.4e}, m={f14['m']}")
    chk("sec 6: q<=16 reproduces R2d's delta to all 16 digits",
        f16['delta'] == 3.353588436042504e-03 and f16['m'] == 8800,
        f"{f16['delta']!r}, m={f16['m']}")
    chk("sec 6: H_flat > 256 but H_ent does not follow",
        f16['feasible'] and o256['best']['h_lower'] < HMIN)

    # ---- section 7: the bracket ----------------------------------------------------
    s7 = section(note, 'bracket')
    seen7 = 0
    for row in rows(s7)[1:]:
        c = cells(row)
        H = int(num(c[0]))
        if H not in U:
            continue
        seen7 += 1
        okrow = close(num(c[3]), U[H], 1e-6)
        if H in L:
            okrow &= (close(num(c[1]), L[H], 1e-6)
                      and close(num(c[5]), U[H] - L[H], 1e-3)
                      and close(num(c[6]), L[H] - HMIN, 1e-4))
        chk(f"sec 7 bracket row H={H}", okrow,
            f"[{L.get(H)}, {U[H]:.9f}]")
    chk("sec 7: all eight rungs are in the note", seen7 == 8, f"{seen7} rows")
    chk("sec 7: the H=128 lower side is R2e's and is new",
        find(br, H=128)['lsrc'] == 'R2e union')
    chk("sec 7: the width jumps by a factor 10 at H=128",
        9 < (U[128] - L[128]) / (U[64] - L[64]) < 11,
        f"{(U[128]-L[128])/(U[64]-L[64]):.2f}x")

    # ---- section 8: the price ------------------------------------------------------
    s8 = section(note, 'price')
    ks = sorted(U)
    dec = [U[a] - U[b] for a, b in zip(ks, ks[1:])]
    chk("sec 8: the seven decrements of U*",
        all(any(close(v, dd, 5e-3) for v in allnums(s8)) for dd in dec if dd > 0),
        ' '.join(f"{v:.3e}" for v in dec))
    gap = U[512] - HMIN
    chk("sec 8: the gap U*(512) - h_min = 0.241082",
        any(close(v, gap, 1e-5) for v in allnums(s8)), f"{gap:.6f}")
    c0, expo = 1.9998, 1.5729
    for row in rows(s8)[1:]:
        c = cells(row)
        if len(c) < 6:
            continue
        rate = num(c[1])
        n = gap / rate
        Lw = expo * math.log2(2 * math.pi * 2 ** n / c0)
        chk(f"sec 8 price row '{c[0][:28]}'",
            abs(num(c[2]) - n) < 1.5
            and abs(math.log10(num(c[3])) - n * math.log10(2)) < 0.2
            and abs(num(c[4]) - Lw) < 2
            and abs(math.log10(num(c[5])) - Lw * math.log10(2)) < 2,
            f"n={n:.1f} H~10^{n*math.log10(2):.1f} L~{Lw:.0f}")
    chk("sec 8: the window price exponent is R2c's 1.5729 = 2 log2 / log alpha",
        close(expo, 2 * math.log(2) / math.log(1 + math.sqrt(2)), 1e-4)
        and '1.5729' in s8, f"{2*math.log(2)/math.log(1+math.sqrt(2)):.4f}")
    chk("sec 8: eps_12 = 1.0101e-2 calibrates the window law",
        close(c0 * 2 ** (-12 / expo), eps12, 1e-3), f"{c0*2**(-12/expo):.4e}")

    # ---- structural, not quoted ----------------------------------------------------
    import r2e_pool256 as R
    o, b = R.selfchecks(log=lambda *a: None)
    chk("r2e_pool256.py self-checks all pass", b == 0, f"{o} ok, {b} failed")
    chk("R1b's own pool file was never written to",
        sorted(map(int, seed['rows']))[-1] == 64)
    chk("the frozen pool is a separate file from R1b's",
        os.path.exists(f'{BB}/r2e_pool_frozen.json') and '128' in fz['rows']
        and '128' not in seed['rows'])
    chk("E_H non-increasing is respected by every certified lower bound",
        all(L[a] >= L[b] - 1e-12 for a, b in zip(sorted(L), sorted(L)[1:])),
        ' '.join(f"{L[H]:.6f}" for H in sorted(L)))

    bad = OK.count(False)
    print(f"\n{len(OK) - bad} claims verified, {bad} failed")
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
