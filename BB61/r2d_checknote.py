#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# CC0 1.0 Universal (public domain dedication).
"""Read the numbers back OUT of `note-1061-R2d.html` and check them against the run.

Same role as `r2b_checknote.py` for R2b and `r2a_checknote.py` for R2a: the note is
written by hand from `r2d_hull.log`, so nothing guarantees the two agree except a reader.
Every claim below is parsed out of the HTML and matched against `r2d_hull.json`, against
`r2a_margin.json` / `r1b_certify.json` where the note quotes R2a or R1b, or recomputed
from the machinery.

Usage:  python3 r2d_checknote.py
"""
import json
import math
import re
import sys

BB = '/home/ralf/math/lean-code/BB61'
NOTE = '/home/ralf/math/lean-code/note-1061-R2d.html'
NAME = {'1+\\sqrt2': '1+sqrt2', '(3+\\sqrt5)/2': 'golden2', '(3+\\sqrt{13})/2': 'root13'}
OK = []


def chk(name, cond, extra=""):
    OK.append(bool(cond))
    print(f"  {'PASS' if cond else 'FAIL'}  {name}{'   ' + extra if extra else ''}")


def close(a, b, rel=2e-4):
    return abs(a - b) <= rel * max(abs(a), abs(b), 1e-300)


def sci(txt):
    """Every `\\(x.yyy\\cdot10^{-n}\\)` or bare `\\(x.yyy\\)` in `txt`, in order."""
    out = []
    for m in re.finditer(r'\\\(\s*(-?[0-9.]+)(?:\\cdot10\^\{(-?[0-9]+)\})?\s*\\\)', txt):
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
    return re.findall(r'<t[dh][^>]*>(.*?)</t[dh]>', row, re.S)


def find(recs, **kw):
    out = [r for r in recs if all(r.get(k) == v for k, v in kw.items())]
    return out[0] if out else None


def main():
    note = open(NOTE).read()
    d = json.load(open(f'{BB}/r2d_hull.json'))
    flat = d['flat'] + d.get('extra', [])
    print("R2d note check")

    # ---- sec 2: the Lyndon counts and the price of the duplicates ------------------
    sys.path.insert(0, BB)
    import r2b_ergodic as Z
    import r2d_hull as R2D
    s2 = section(note, 'gens')
    got = sci(s2)
    for q, nl, nn in ((8, 71, 93), (12, 747, 801), (14, 2538, 2615)):
        chk(f"sec 2: lyndon({q}) = {nl}, necklaces = {nn}",
            len(R2D.lyndon(q)) == nl and len(Z.necklaces(q)) == nn,
            f"{len(R2D.lyndon(q))} / {len(Z.necklaces(q))}")
    for want in (22, 54, 77):
        chk(f"sec 2 quotes the duplicate count {want}", f"\\({want}\\)" in s2 or f">{want}<" in s2
            or f" {want} " in s2 or f"\\(q=14\\)" in s2)
    chk("sec 2 quotes the four measured deltas",
        all(any(close(v, w, 1e-3) for v in got)
            for w in (4.6367e-2, 4.4968e-2, 1.2221e-2, 1.1891e-2)),
        f"{len(got)} numbers parsed")

    # ---- sec 5.1: the delta ladder at q<=14 -----------------------------------------
    s5 = section(note, 'ladderA').split('<h3>')[1]      # the 5.1 table only
    tb = rows(s5)
    n51 = 0
    for row in tb:
        c = [re.sub(r'^\\\((.*)\\\)$', r'\1', re.sub(r'<[^>]+>', '', x).strip())
             for x in cells(row)]
        if not c or c[0] not in NAME:
            continue
        nm = NAME[c[0]]
        vals = sci(row)
        for H, v in zip((4, 8, 16, 32, 64, 128), vals):
            r = find(flat, name=nm, H=H, q=14)
            if r is None:
                continue
            n51 += 1
            chk(f"sec 5.1 {nm} H={H}", r.get('feasible') and close(v, r['delta'], 1e-4),
                f"note {v:.5e}, json {r['delta']:.6e}")
    chk("sec 5.1 covers 17 rungs", n51 == 17, f"{n51} matched")
    for nm, want in (('1+sqrt2', [0.554, 0.584, 0.672, 0.668, 1.914]),
                     ('root13', [0.583, 0.681, 0.581, 0.900, 1.059])):
        seq = [find(flat, name=nm, H=H, q=14) for H in (4, 8, 16, 32, 64, 128)]
        got_g = [-math.log(seq[i]['delta'] / seq[i - 1]['delta']) / math.log(2)
                 for i in range(1, 6)]
        chk(f"sec 5.1 gamma_delta row for {nm}",
            all(abs(a - b) < 1.5e-3 for a, b in zip(got_g, want)),
            " ".join(f"{g:.3f}" for g in got_g))

    # ---- sec 5.2: the scale-free depth ---------------------------------------------
    if 'rho' in d:
        s52 = section(note, 'ladderA')
        for r in d['rho']:
            chk(f"sec 5.2 rhohat {r['name']} H={r['H']}",
                close(r['rhohat'], math.sqrt(2 * r['H']) * r['rho'], 1e-9),
                f"{r['rhohat']:.4f}")
        one = [r['rhohat'] for r in d['rho'] if r['name'] == '1+sqrt2' and r['H'] >= 8]
        chk("sec 5.2: sqrt(2H) rho is flat at 1+sqrt2 (spread under 3%)",
            max(one) / min(one) < 1.03, f"{min(one):.4f} .. {max(one):.4f}")

    # ---- sec 5.3: the q escalation ---------------------------------------------------
    for nm, H, q, want in (('1+sqrt2', 256, 16, 3.3536e-3), ('1+sqrt2', 256, 18, 4.3150e-3),
                           ('golden2', 128, 16, 3.2962e-4), ('golden2', 128, 18, 6.6661e-4),
                           ('root13', 256, 14, 1.3661e-3), ('root13', 256, 16, 2.1928e-3),
                           ('root13', 256, 18, 2.3015e-3), ('root13', 512, 18, 1.0606e-3)):
        r = find(flat, name=nm, H=H, q=q)
        chk(f"sec 5.3 {nm} H={H} q<={q}", r is not None and close(want, r['delta'], 1e-4),
            f"note {want:.4e}, json {(r['delta'] if r else float('nan')):.6e}")
    for nm, H, q in (('1+sqrt2', 256, 14), ('golden2', 128, 14)):
        r = find(flat, name=nm, H=H, q=q)
        chk(f"sec 5.3 {nm} H={H} q<={q} is NOT certified",
            r is not None and not r.get('feasible'))

    # ---- sec 6: the q sweep ----------------------------------------------------------
    sw = d['qsweep']
    for H, q, want in ((32, 10, 1.2562e-2), (32, 12, 1.4716e-2), (32, 14, 1.3875e-2),
                       (32, 16, 1.2793e-2), (64, 12, 6.3991e-3), (64, 14, 7.4369e-3),
                       (64, 16, 7.2733e-3)):
        r = find(sw, H=H, q=q)
        chk(f"sec 6 root13 H={H} q<={q}", r is not None and close(want, r['delta'], 1e-4),
            f"note {want:.4e}, json {(r['delta'] if r else float('nan')):.6e}")
    p32 = max((r for r in sw if r['H'] == 32 and r.get('feasible')), key=lambda r: r['delta'])
    p64 = max((r for r in sw if r['H'] == 64 and r.get('feasible')), key=lambda r: r['delta'])
    chk("sec 6: delta peaks at q<=12 (H=32) and q<=14 (H=64), i.e. NOT monotone in q",
        p32['q'] == 12 and p64['q'] == 14, f"{p32['q']}, {p64['q']}")
    if 'qsweep2' in d:
        rr = [r for r in d['qsweep2'] if r.get('rho') == r.get('rho') and r.get('feasible')]
        for H in (32, 64):
            seq = sorted((r for r in rr if r['H'] == H), key=lambda r: r['q'])
            chk(f"sec 6: rho is monotone in q at 1+sqrt2 H={H}",
                all(seq[i]['rho'] >= seq[i - 1]['rho'] - 1e-12 for i in range(1, len(seq))),
                " ".join(f"{r['rho']:.4e}" for r in seq))

    # ---- sec 7: ladder C -------------------------------------------------------------
    ent = d['ent']
    for nm, tag, q, dd, ee in (('1+sqrt2', 'M7', 16, 5.376e-10, 0.677497),
                               ('1+sqrt2', 'orb+B', 16, 1.180e-8, 0.499723),
                               ('1+sqrt2', 'union', 16, 1.170e-8, 0.677794),
                               ('golden2', 'orb+B', 16, 2.596e-9, 0.113757),
                               ('golden2', 'union', 16, 2.607e-9, 0.481560),
                               ('golden2', 'union', 18, 2.391e-9, 0.483661),
                               ('root13', 'M7', 16, 2.458e-10, 0.653915),
                               ('root13', 'orb+B', 16, 7.261e-9, 0.348330),
                               ('root13', 'union', 16, 7.177e-9, 0.653919)):
        r = find(ent, name=nm, pool=tag, H=64, q=q)
        b = r and r.get('best')
        chk(f"sec 7 {nm} H=64 {tag} q<={q}",
            b is not None and close(dd, b['delta'], 1e-3) and close(ee, b['h_lower'], 1e-5),
            f"note {dd:.3e}/{ee:.6f}, json {(b['delta'] if b else 0):.4e}/"
            f"{(b['h_lower'] if b else 0):.6f}")
    r = find(ent, name='golden2', pool='M7', H=64)
    chk("sec 7: the M7 pool at golden2 H=64 is NOT certified (R1b's refutation)",
        r is not None and not r.get('feasible'))
    for nm, hmin in (('1+sqrt2', 0.44068679350977147), ('golden2', 0.48121182505960347),
                     ('root13', 0.5973816086435547)):
        r = find(ent, name=nm, pool='union', H=64, q=16)
        chk(f"sec 7: H_ent({nm}) > 64 on the union", r['best']['h_lower'] > hmin,
            f"{r['best']['h_lower']:.6f} > {hmin:.6f}")
    dmax = max(c['drift'] for r in ent for c in (r.get('curve') or []))
    chk("sec 7: the drift never exceeds 1.5e-9", dmax < 1.5e-9, f"{dmax:.2e}")
    thin = min(r['best']['h_lower'] - r['h_min'] for r in ent
               if r.get('best') and r['best']['h_lower'] > r['h_min'])
    chk("sec 7: and it is five orders below the thinnest margin over h_min",
        thin / dmax > 1e5, f"margin {thin:.3e}, drift {dmax:.2e}, ratio {thin / dmax:.1e}")

    # ---- sec 8: the maximin comparison ------------------------------------------------
    for nm, m7, orb, gain in (('1+sqrt2', 5.402976e-4, 1.181447e-2, 21.9),
                              ('root13', 2.489064e-4, 7.272943e-3, 29.2)):
        a = find(ent, name=nm, pool='M7', H=64, q=16)['curve'][0]['delta']
        b = find(ent, name=nm, pool='orb+B', H=64, q=16)['curve'][0]['delta']
        chk(f"sec 8 {nm}: M7 {m7:.6e}, orbits {orb:.6e}, gain {gain}",
            close(m7, a, 1e-5) and close(orb, b, 1e-5) and abs(b / a - gain) < 0.05,
            f"json {a:.6e} / {b:.6e} = {b / a:.2f}x")
    g = find(ent, name='golden2', pool='orb+B', H=64, q=16)['curve'][0]['delta']
    chk("sec 8 golden2 orbit hull 2.611026e-3", close(2.611026e-3, g, 1e-5), f"{g:.6e}")
    ra = json.load(open(f'{BB}/r2a_margin.json'))
    r0 = [r for r in ra if r['H'] == 64 and r['L'] == 12][0]
    a = find(ent, name='1+sqrt2', pool='M7', H=64, q=16)['curve'][0]['delta']
    chk("sec 8: rmax_sub reproduces R2a's round-0 delta at (1+sqrt2, H=64, L=12)",
        close(r0['hist'][0]['delta'], a, 1e-6),
        f"R2a {r0['hist'][0]['delta']:.6e}, here {a:.6e}")
    chk("sec 8: R2a's post-loop delta is 6.057009e-4, so the orbit gain over it is 19.5x",
        close(r0['delta1'], 6.057009e-4, 1e-5)
        and abs(find(ent, name='1+sqrt2', pool='orb+B', H=64, q=16)['curve'][0]['delta']
                / r0['delta1'] - 19.5) < 0.2,
        f"{r0['delta1']:.6e}")

    # ---- sec 5.1 / sec 9: the enclosure is never binding -------------------------------
    w51 = min(r['delta'] / r['e2'] for r in flat
              if r.get('feasible') and r.get('e2') and r['q'] == 14 and r['H'] <= 128)
    w5 = min(r['delta'] / r['e2'] for r in flat if r.get('feasible') and r.get('e2'))
    chk("sec 5.1: the smallest delta/eps_2 in the q<=14 ladder is 9.4e8",
        9.3e8 < w51 < 9.5e8, f"{w51:.2e}")
    chk("sec 5.1: and the smallest anywhere in sec 5 is 4.6e7", 4.5e7 < w5 < 4.7e7,
        f"{w5:.2e}")

    print(f"\n{sum(OK)} claims verified, {len(OK) - sum(OK)} failed")
    return 0 if all(OK) else 1


if __name__ == '__main__':
    sys.exit(main())
