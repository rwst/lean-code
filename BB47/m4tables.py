#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code. Released under CC0 1.0 Universal.
"""M4 (plan-1047): turn BB47/data/*.tsv into the numbers quoted in BB47/M4.tex."""
import sys, glob, os, collections

def load(path):
    d = collections.defaultdict(dict); N = None
    for line in open(path):
        if line.startswith('#'):
            for tok in line.split():
                if tok.startswith('N='): N = int(tok[2:])
            continue
        f = line.rstrip('\n').split('\t')
        if f[0] in ('CERT', 'BAL', 'REP'):
            d[f[0]][int(f[2])] = [int(x) for x in f[3:]]
        elif f[0] == 'EXACT':
            d['EXACT'][int(f[2])] = [int(x) for x in f[3:]]
    return N, d

def main():
    tags = sys.argv[1:] or sorted(os.path.basename(p)[:-4] for p in glob.glob('BB47/data/*.tsv'))
    for tag in tags:
        p = 'BB47/data/%s.tsv' % tag
        if not os.path.exists(p): continue
        N, d = load(p)
        C, B, R, E = d['CERT'], d['BAL'], d['REP'], d['EXACT']
        ns = sorted(C)
        wreach = {n: N - C[n][0] for n in ns if C[n][0] > 0}
        breach = {n: N - B[n][0] for n in ns if B[n][0] > 0}
        zero_w = [n for n in ns if C[n][0] == 0]
        zero_b = [n for n in ns if B[n][0] == 0]
        full = [n for n in sorted(E) if E[n][0] == E[n][1]]
        print('=== %s  N=%d ===' % (tag, N))
        print('  C^W: fires for n in [%s..%s]; max reach %d (at n=%s); reach at n=2,8,16,32,63: %s'
              % (min(wreach) if wreach else '-', max(wreach) if wreach else '-',
                 max(wreach.values()) if wreach else 0,
                 max(wreach, key=wreach.get) if wreach else '-',
                 [wreach.get(k) for k in (2, 8, 16, 32, 63)]))
        print('  C^W: silent (=0) for n = %s' % (zero_w if len(zero_w) < 12 else '%d values %s..%s' % (len(zero_w), zero_w[0], zero_w[-1])))
        print('  C^B: max reach %d (at n=%s); silent for n = %s'
              % (max(breach.values()) if breach else 0, max(breach, key=breach.get) if breach else '-',
                 zero_b if len(zero_b) < 12 else '%d values' % len(zero_b)))
        print('  p(n)=b^n up to n=%s ; largest exact n=%d' % (max(full) if full else '-', max(E) if E else 0))
        for n in sorted(E):
            pn, bn, lmin, q01, q10, q50, revok, self_, a50, a90, a99, a999 = E[n]
            if n in (8, 16, 20, 24, 26, 27, max(E)) or n == max(full or [0]):
                print('    n=%-2d p=%-10d b^n=%-11d p/b^n=%.4f  C^F=%-10d  C_{.99p}=%-10d C_{.5p}=%-10d rev=%.4f  alive>0.999N=%d'
                      % (n, pn, bn, pn / bn, lmin, q01, q50, revok / pn, a999))
        rr = [(n, R[n][0]) for n in sorted(R) if R[n][0] > 0]
        print('  r(n): %s' % ' '.join('%d:%d' % t for t in rr[-10:]))
        print('  r(n)/n max over n>=2: %.1f at n=%d' % max(((v / n, n) for n, v in rr if n >= 2)))

main()
