#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# CC0 1.0 Universal (public domain dedication).
"""Read the numbers back OUT of `note-1061-R2c.html` and check them against the run.

Same role as `r2d_checknote.py` for R2d: the note is written by hand from
`r2c_deep.log`, so nothing guarantees the two agree except a reader.  Every claim below
is parsed out of the HTML and matched against `r2c_deep.json` / `r2c_repro.json`,
against `m8_w4.json` / `m4_frontier.json` / `r1b_certify.json` / `r2d_hull.json` where
the note quotes an earlier run, or recomputed from the machinery.

Usage:  python3 r2c_checknote.py
"""
import json
import math
import re
import sys

BB = '/home/ralf/math/lean-code/BB61'
NOTE = '/home/ralf/math/lean-code/note-1061-R2c.html'
OK = []


def chk(name, cond, extra=""):
    OK.append(bool(cond))
    print(f"  {'PASS' if cond else 'FAIL'}  {name}{'   ' + extra if extra else ''}")


def close(a, b, rel=2e-4):
    return abs(a - b) <= rel * max(abs(a), abs(b), 1e-300)


def sci(txt):
    """Every `\\(x.yyy\\cdot10^{-n}\\)` or bare `\\(x.yyy\\)` in `txt`, in order."""
    out = []
    for m in re.finditer(r'\\\(\s*([+-]?[0-9.]+)(?:\\cdot10\^\{(-?[0-9]+)\})?\s*\\\)', txt):
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
        t = re.sub(r'<[^>]+>', '', x).strip()
        t = re.sub(r'^\\\((.*)\\\)$', r'\1', t)
        out.append(t)
    return out


def num(s):
    """The first number in a cell, sci notation understood."""
    m = re.search(r'([+-]?[0-9]*\.?[0-9]+)(?:\\cdot10\^\{(-?[0-9]+)\})?', s)
    if not m:
        return None
    return float(m.group(1)) * (10.0 ** int(m.group(2)) if m.group(2) else 1.0)


def find(recs, **kw):
    out = [r for r in recs if all(r.get(k) == v for k, v in kw.items())]
    return out[0] if out else None


def main():
    note = open(NOTE).read()
    d = json.load(open(f'{BB}/r2c_deep.json'))
    rp = json.load(open(f'{BB}/r2c_repro.json'))['repro']
    cert = d['cert']
    lad = d['ladder']
    meta = d['meta']
    print("R2c note check")
    sys.path.insert(0, BB)

    # ---- sec 2: kappa_ww off W4's stored certificates -----------------------------
    s2 = section(note, 'stall')
    w4 = json.load(open(f'{BB}/m8_w4.json'))
    got = sci(s2)
    chk("sec 2 quotes M4's saturated ladder value 0.689922",
        any(close(v, 0.689922, 1e-5) for v in got) or '0.689922' in s2)
    chk("sec 2 quotes M4's saturated multiplier norm 0.73",
        '0.73' in s2)

    # the kappa_ww range, recomputed here from W4's own file
    import r2c_deep as R
    rows_w4 = R.calib(log=lambda *a: None)
    ks = [r['k_ww'] for r in rows_w4 if r['src'] == 'W4']
    chk(f"sec 2/3: kappa_ww over W4's {len(ks)} certificates is in [{min(ks):.4f}, "
        f"{max(ks):.4f}]",
        len(ks) == 20 and 0.04 < min(ks) < 0.05 and 0.20 < max(ks) < 0.21,
        f"median {sorted(ks)[len(ks)//2]:.4f}")
    for want in (min(ks), max(ks)):
        chk(f"sec 2 quotes {want:.4f}",
            any(close(v, want, 5e-3) for v in got), f"{len(got)} numbers parsed")
    chk("sec 2 quotes the over-charge factors 4.8 and 22.6",
        any(close(v, 1 / max(ks), 5e-3) for v in got)
        and any(close(v, 1 / min(ks), 5e-3) for v in got))

    # ---- sec 4: the reproduction ---------------------------------------------------
    s4 = section(note, 'repro')
    pub = rp['published']
    for row in rows(s4)[1:]:
        c = cells(row)
        if len(c) < 4 or 'cert' not in c[0] and 'ladder' not in c[0]:
            continue
        m4, mine, dev = num(c[1]), num(c[2]), num(c[3])
        nums = re.findall(r'([0-9]+)', c[0])
        if 'cert' in c[0]:
            t = nums[0] + '/' + nums[1]
            if t not in pub:
                continue
            got_m4 = pub[t]
            got_mine = rp['cert'][t]['Lambda_ub']
        else:
            H = nums[0]
            if H not in rp['ladder']:
                continue
            got_m4 = rp['ladder'][H]['P'] - rp['ladder'][H]['dP']
            got_mine = rp['ladder'][H]['P']
        chk(f"sec 4 row '{c[0]}'",
            close(m4, got_m4, 1e-8) and close(mine, got_mine, 1e-8)
            and close(dev, got_mine - got_m4, 0.05),
            f"{got_m4:.9f} / {got_mine:.9f} / {got_mine - got_m4:+.1e}")
    chk("sec 4: worst certificate deviation is 5.0e-07",
        close(abs(rp['worst_cert']), 5.0e-07, 0.02), f"{rp['worst_cert']:+.1e}")
    chk("sec 4: the saturated multiplier norm reproduces as 0.7299",
        all(close(rp['ladder'][H]['sum_h_a'], 0.7299, 1e-3)
            for H in ('16', '24', '32', '48', '64')))

    # ---- sec 5: the ladder, every cell against the JSON ----------------------------
    s5 = section(note, 'ladder')
    allr = rows(s5)
    i0 = next(i for i, r in enumerate(allr)
              if r.count('kappa') >= 3 and '<th' in r)
    tb = allr[i0:i0 + 9]          # the ladder table only, not sec 5.2's
    hdr = cells(tb[0])
    kap = []
    for h in hdr[1:]:
        m = re.search(r'kappa=(?:1/)?([0-9.]+)', h.replace('\\', ''))
        if m:
            kap.append(1.0 / float(m.group(1)) if '1/' in h.replace('\\', '')
                       else float(m.group(1)))
    chk(f"sec 5 header lists {len(kap)} penalty rates",
        sorted(kap, reverse=True) == sorted({r['kappa'] for r in lad}, reverse=True),
        f"{kap}")
    n5 = 0
    for row in tb[1:]:
        c = cells(row)
        if num(c[0]) is None:
            continue
        H = int(num(c[0]))
        for j, k in enumerate(kap):
            r = find(lad, kappa=k, H=H)
            v = num(c[1 + j])
            if r is None or v is None:
                continue
            n5 += 1
            if not close(v, r['P'], 2e-6):
                chk(f"sec 5 cell kappa={k} H={H}", False, f"note {v} json {r['P']}")
    chk(f"sec 5: all {n5} ladder cells match r2c_deep.json", True)

    # ---- sec 6: the bracket ---------------------------------------------------------
    s6 = section(note, 'bracket')
    import r2c_deep as R
    lo = R._lower_bounds()
    up = {}
    for c in cert:
        b = up.get(c['H'])
        if b is None or c['Lambda_enc'] < b['Lambda_enc']:
            up[c['H']] = c
    n6 = 0
    for row in rows(s6)[1:]:
        c = cells(row)
        H = int(num(c[0])) if num(c[0]) else None
        if H not in up:
            continue
        n6 += 1
        if num(c[1]) is not None and H in lo:
            chk(f"sec 6 lower bound at H={H}", close(num(c[1]), lo[H][0], 1e-8),
                f"note {c[1]} json {lo[H][0]:.9f}")
        chk(f"sec 6 upper bound at H={H}",
            close(num(c[2]), up[H]['Lambda_enc'], 2e-6),
            f"note {c[2]} json {up[H]['Lambda_enc']:.6f}")
    chk(f"sec 6 reports {n6} degrees", n6 >= 5)

    # ---- sec 7: the price ------------------------------------------------------------
    s7 = section(note, 'price')
    got = sci(s7)
    for want in (1.5729, 1.4404, 1.1603):
        chk(f"sec 7 quotes the exponent {want}", any(close(v, want, 1e-3) for v in got))
    from m0_engine import Alpha
    from m3_entropy import best_split
    al = Alpha(R.COEFFS, R.POLY)
    for L, tgt, need in ((22, 3.490e-5, 26), (24, 1.333e-5, 28)):
        Lm = next(x for x in range(10, 60) if best_split(al, x)[2] <= tgt)
        chk(f"sec 7: matching (3+sqrt5)/2 at L={L} needs L={need} at 1+sqrt2", Lm == need,
            f"computed {Lm}")
    fac = [best_split(al, L + 1)[2] / best_split(al, L)[2] for L in range(16, 26)]
    chk("sec 7: the per-level factor is 0.6464",
        close(sum(fac) / len(fac), 0.6464, 1e-3), f"{sum(fac)/len(fac):.4f}")

    # ---- the certificate tables ------------------------------------------------------
    for hid in ('certs',):
        if f'id="{hid}"' not in note:
            continue
        sC = section(note, hid)
        nC = 0
        for row in rows(sC)[1:]:
            c = cells(row)
            H = int(num(c[0])) if num(c[0]) else None
            if H is None:
                continue
            for j, k in enumerate(kap):
                v = num(c[1 + j]) if 1 + j < len(c) else None
                if v is None:
                    continue
                r = [x for x in cert if x['kappa'] == k and x['H'] == H]
                if not r:
                    continue
                if not any(close(v, x['Lambda_enc'], 2e-6) for x in r):
                    chk(f"sec certs cell kappa={k} H={H}", False,
                        f"note {v} json {[round(x['Lambda_enc'],6) for x in r]}")
                nC += 1
        chk(f"sec certs: all {nC} certificate cells match", True)

    # ---- global ----------------------------------------------------------------------
    chk("the box is inactive at every ladder rung",
        not any(r['box_active'] for r in lad),
        f"max |x| = {max(r['xmax'] for r in lad):.4f}, cap {meta['cap']}")
    chk("every certificate encloses its own pressure",
        all(c['encloses'] for c in cert))
    chk("the word-wise enclosure never loses to the uniform one",
        all(c['Lambda_enc'] <= c['Lambda_cw'] + 1e-12 for c in cert))
    chk("Theorem 1's sandwich holds at every certificate",
        all(c['P_deep'] + c['err'] * c['mean_gp'] + 0.5 * c['err'] ** 2 * c['M2']
            <= c['Lambda_enc'] + 1e-9
            and c['Lambda_enc'] <= c['P_deep'] + c['err'] * c['sup_gp']
            + 0.5 * c['err'] ** 2 * c['M2'] + 1e-9 for c in cert),
        f"{len(cert)} certificates")
    chk("2 pi H eps < 1 at every certificate (R2b's trust rule)",
        all(c['trust'] < 1 for c in cert),
        f"worst {max(c['trust'] for c in cert):.4f}")
    chk("no certificate fires (Lambda_enc < h_min)",
        not any(c['fires'] for c in cert),
        f"best margin {max(c['margin_enc'] for c in cert):+.5f}")

    bad = OK.count(False)
    print(f"\n{len(OK) - bad} claims verified, {bad} failed")
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
