#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# CC0 1.0 Universal (public domain dedication).
"""Read the numbers back OUT of `note-1061-R2b.html` and check them against the runs.

The note is written by hand from the logs, so nothing guarantees the two agree except a
reader.  This is that reader: every claim below is parsed out of the HTML and recomputed
from `r2b_ergodic.json`, `r2b_fwflat.json`, `r2b_hybrid.json`, `r2b_orbits.json`, or from
the machinery itself.  Same role as `r2a_checknote.py` for R2a.

Usage:  python3 r2b_checknote.py
"""
import json
import math
import re
import sys

import numpy as np

BB = '/home/ralf/math/lean-code/BB61'
NOTE = '/home/ralf/math/lean-code/note-1061-R2b.html'
OK = []


def chk(name, cond, extra=""):
    OK.append(bool(cond))
    print(f"  {'PASS' if cond else 'FAIL'}  {name}{'   ' + extra if extra else ''}")


def num(s):
    return float(s.replace('e-', 'E-').replace('e+', 'E+'))


def close(a, b, rel=2e-3):
    return abs(a - b) <= rel * max(abs(a), abs(b), 1e-300)


def main():
    note = open(NOTE).read()
    erg = json.load(open(f'{BB}/r2b_ergodic.json'))
    fw = json.load(open(f'{BB}/r2b_fwflat.json'))
    hy = json.load(open(f'{BB}/r2b_hybrid.json'))
    orb = json.load(open(f'{BB}/r2b_orbits.json'))
    print("R2b note check")

    # --- sec 5: the reprice table --------------------------------------------------
    for row in erg['reprice']:
        L = row['L']
        pat = rf"<tr><td>{L}</td><td>\\\(([-0-9.]+)\\cdot10\^\{{([-0-9]+)\}}\\\)</td><td>\\\(([-+0-9.]+)\\\)</td>"
        m = re.search(pat, note)
        chk(f"sec 5 row L={L} present", m is not None)
        if m:
            eps = float(m.group(1)) * 10.0 ** int(m.group(2))
            chk(f"sec 5 L={L} eps", close(eps, row['eps'], 1e-3),
                f"note {eps:.4e}, json {row['eps']:.4e}")
            chk(f"sec 5 L={L} beta", close(float(m.group(3)), row['beta'], 1e-5),
                f"note {m.group(3)}, json {row['beta']:.6f}")
    r12 = [r for r in erg['reprice'] if r['L'] == 12][0]
    gain = r12['kappa'] / r12['kappa_press']
    chk("sec 1/5: the 17% the pressure pays", 1.16 <= gain <= 1.18, f"{gain:.3f}")
    b12 = [r for r in erg['reprice'] if r['L'] == 12][0]['beta']
    b18 = [r for r in erg['reprice'] if r['L'] == 18][0]['beta']
    chk("sec 5: the real truncation error is 0.85", close(abs(b18 - b12), 0.847, 5e-3),
        f"{abs(b18 - b12):.3f}")
    chk("sec 5: tau_12 / that error = 33", close(r12['tau'] / abs(b18 - b12), 32.9, 2e-2),
        f"{r12['tau'] / abs(b18 - b12):.1f}")

    # --- sec 6: the nu^(q) table ----------------------------------------------------
    tab = erg['nu_q']['tab']
    sec6 = note[note.index('id="above"'):]
    sec6 = sec6[:sec6.index('<h2 ')].replace('<b>', '').replace('</b>', '')
    for H in erg['nu_q']['Hs']:
        row = tab[str(H)]
        cells = re.search(rf"<tr><td>{H}</td>((?:<td>[^<]*</td>){{6}})</tr>", sec6)
        chk(f"sec 6 row H={H} present", cells is not None)
        if cells:
            got = [num(x) for x in re.findall(r'<td>([^<]*)</td>', cells.group(1))]
            chk(f"sec 6 row H={H} values", all(close(a, b, 1e-3) for a, b in zip(got, row)),
                f"note {got[-1]:.4e} vs json {row[-1]:.4e}")
    # nu^(q)_H is non-decreasing in H as a theorem; the table holds UPPER bounds from a
    # Frank-Wolfe run with a fixed budget, so a 1% inversion at the plateau is the solver
    inv = max((tab[str(a)][-1] - tab[str(b)][-1]) / max(tab[str(b)][-1], 1e-300)
              for a, b in zip(erg['nu_q']['Hs'], erg['nu_q']['Hs'][1:]))
    chk("sec 6: nu^(q) non-decreasing in H at q<=14, to the solver's 1%", inv <= 0.01,
        f"worst inversion {100 * inv:.2f}%")
    chk("sec 6: nu^(q) non-increasing in q at every H",
        all(all(tab[str(H)][i] >= tab[str(H)][i + 1] - 1e-12 for i in range(5))
            for H in erg['nu_q']['Hs']))
    chk("sec 1/6: nu^(14)_128 quoted as 2.70e-4",
        close(tab['128'][-1], 2.6959e-4, 1e-3) and '2.6959e-4' in note)
    chk("sec 6: H<=16 rows are zero to working precision",
        tab['8'][-1] < 1e-9 and tab['16'][-1] < 1e-9)

    # --- sec 7: the vetoes and the price --------------------------------------------
    sys.path.insert(0, BB)
    import r2b_ergodic as Z
    from m0_engine import Alpha
    al = Alpha([1, -2, -1], '1+sqrt2')
    bern = float(np.max(np.abs(Z.bern_phi_true(al, 512)) / np.arange(1, 513)))
    chk("sec 7.2: the Bernoulli constant 1.5321e-2", close(bern, 1.5321e-2, 1e-3)
        and '1.5321' in note, f"{bern:.5e}")
    argmax = int(np.argmax(np.abs(Z.bern_phi_true(al, 512)) / np.arange(1, 513))) + 1
    chk("sec 7.2: the maximum sits at h = 3", argmax == 3, f"h = {argmax}")
    for L, want in ((12, 6.3468e-2), (14, 2.6289e-2), (16, 1.0889e-2), (18, 4.5105e-3)):
        chk(f"sec 7.2/10: 2 pi eps_{L}", close(Z.LightWindow(al, L).r, want, 1e-3))
    chk("sec 7.2: L=14 is vetoed and L=16 is not",
        Z.LightWindow(al, 14).r > bern > Z.LightWindow(al, 16).r)
    expo = 2 * math.log(2) / math.log(float(al.alpha))
    chk("sec 7.4: the exponent 1.5729", close(expo, 1.5729, 1e-4) and '1.5729' in note,
        f"{expo:.4f}")
    for H in ('64', '128', '256', '512'):
        p = erg['price'][H]
        L2, st, _ = Z.price(al, p['nu'])
        chk(f"sec 7.4 H={H}: L = {p['L']:.1f}", close(L2, p['L'], 1e-6)
            and f"{p['L']:.1f}" in note)
    nf = erg['nofire']
    chk("sec 7.3: no-fire yes through L=22 at every H tried",
        all(all(v[:6]) for v in nf.values()))
    chk("sec 7.3: L=24 fails at H >= 64 and holds at H = 32",
        nf['32'][6] and not nf['64'][6] and not nf['128'][6] and not nf['256'][6])
    r1b = erg['r1b_price']['64']
    chk("sec 7.1: R1b's H0=64 gives nu <= 1/65", close(r1b['nu'], 1 / 65, 1e-9)
        and '1.5385e-2' in note)

    # --- sec 8: generator vs evaluator ------------------------------------------------
    for r in erg['flat12']:
        if r['H'] in (64, 96, 112, 116, 120, 128):
            chk(f"sec 8 flat12 H={r['H']} beta", f"{abs(r['beta']):.6f}" in note,
                f"{r['beta']:.6f}")
    chk("sec 8: the pressure certificate fails at H=128 where beta does not",
        [r for r in erg['flat12'] if r['H'] == 128][0]['ub'] > 0
        and [r for r in erg['flat12'] if r['H'] == 128][0]['beta'] < 0)
    chk("sec 8: the FW search never certifies below H=120",
        all(v['kappa'] < 0 for v in fw.values()))
    chk("sec 8: the hybrid certifies at 120 and 128 and not below",
        hy['120']['kappa1'] > 0 and hy['128']['kappa1'] > 0
        and hy['112']['kappa1'] < 0 and hy['116']['kappa1'] < 0)
    chk("sec 8: Frank-Wolfe improves the pressure direction at no rung",
        all(close(v['kappa0'], v['kappa1'], 1e-9) for v in hy.values()))
    best = max(r['ratio'] for r in erg['reprice'])
    chk("sec 8: the best kappa/tau is 9.50e-4, short of 1 by 1053",
        close(best, 9.50e-4, 2e-3) and close(1 / best, 1053, 2e-3)
        and '1053' in note, f"1/{best:.3e} = {1 / best:.0f}")

    # --- sec 9: the orbit pool --------------------------------------------------------
    def get(name, H, q):
        r = [x for x in orb if x['name'] == name and x['H'] == H and x['qmax'] == q]
        return r[0] if r else None
    for (nm, H, q, want) in (('1+sqrt2', 32, 14, 1.89332e-2), ('1+sqrt2', 64, 14, 1.18913e-2),
                             ('(3+sqrt5)/2', 64, 14, 2.30290e-3),
                             ('(3+sqrt5)/2', 32, 14, 5.60413e-3)):
        r = get(nm, H, q)
        chk(f"sec 9 {nm} H={H} q<={q} delta", r is not None and close(r['delta'], want, 1e-4),
            f"{r['delta']:.5e}" if r else "missing")
    chk("sec 9: the orbit hull beats the M7 pool 9.5x at H=32",
        close(get('1+sqrt2', 32, 14)['delta'] / 2.000092e-3, 9.47, 2e-2),
        f"{get('1+sqrt2', 32, 14)['delta'] / 2.000092e-3:.2f}")
    chk("sec 9: and 19.6x at H=64",
        close(get('1+sqrt2', 64, 14)['delta'] / 6.057009e-4, 19.63, 2e-2),
        f"{get('1+sqrt2', 64, 14)['delta'] / 6.057009e-4:.2f}")
    chk("sec 9: at (3+sqrt5)/2 H=64 the q<=10 and q<=12 hulls both fail",
        not get('(3+sqrt5)/2', 64, 10)['feasible']
        and not get('(3+sqrt5)/2', 64, 12)['feasible'])
    chk("sec 9: every enclosure is below 1.3e-12",
        max(x['eps'] for x in orb) < 1.3e-12, f"{max(x['eps'] for x in orb):.2e}")

    print(f"\n  {sum(OK)}/{len(OK)} claims verified, {len(OK) - sum(OK)} failed")
    return 0 if all(OK) else 1


if __name__ == '__main__':
    sys.exit(main())
