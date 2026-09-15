#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code. Released under CC0 1.0 Universal.
"""M4 (plan-1047): the skew-branch (period) certificate and the lag-q break density.

For each lag q, T_q = {k : w_{k+q} != w_k}.  M3 Prop. 6.1 says that under hypothesis (H)
and branch (b) with least period q, every maximal run of consecutive integers in
T_q \\cap (s_n+n, oo) has exactly TWO elements, for every n > q+2.  Hence

    if {k, k+1, k+2} \\subseteq T_q  then  s_n >= k - n     (n > q+2).

We report  K(q) := max such k found in the scanned tail, and the density of T_q there.

Usage: m4period.py <digitfile> <tag> [qmax] [tail]
"""
import sys
import numpy as np


def main():
    fn, tag = sys.argv[1], sys.argv[2]
    qmax = int(sys.argv[3]) if len(sys.argv) > 3 else 4096
    tail = int(sys.argv[4]) if len(sys.argv) > 4 else 200000
    a = np.fromfile(fn, dtype=np.uint8)
    N = len(a)
    t = a[max(0, N - tail):]                    # scanned tail, offset off
    off = N - len(t)
    dens_tail = min(len(t), 2000000)
    best_k, best_q, worst_d, worst_dq = N, -1, 1.0, -1
    rows = []
    for q in range(1, qmax + 1):
        d = t[q:] != t[:-q]                     # d[i] <=> (off+i+1) in T_q, 1-based
        # last i with d[i] & d[i+1] & d[i+2]
        run3 = d[:-2] & d[1:-1] & d[2:]
        idx = np.flatnonzero(run3)
        k = int(off + idx[-1] + 1) if len(idx) else 0
        dq = float(d[-dens_tail:].mean())
        rows.append((q, k, dq))
        if k < best_k:
            best_k, best_q = k, q
        if dq < worst_d:
            worst_d, worst_dq = dq, q
    print("# PERIOD %s N=%d qmax=%d tail=%d" % (tag, N, qmax, tail))
    for q, k, dq in rows:
        if q <= 8 or q % 512 == 0 or q == best_q or q == worst_dq:
            print("PER\t%s\t%d\t%d\t%d\t%.6f" % (tag, q, k, N - k, dq))
    print("PERMIN\t%s\t%d\t%d\t%d\t%.6f\t%d" % (tag, best_q, best_k, N - best_k, worst_d, worst_dq))
    # the reach of the certificate is at least q+2 by construction; report the excess
    exc = max((N - k - q, q) for q, k, _ in rows if k > 0) if any(k > 0 for _, k, _ in rows) else (0, 0)
    nz = sum(1 for _, k, _ in rows if k == 0)
    print("PEREXCESS\t%s\t%d\t%d\t%d" % (tag, exc[0], exc[1], nz))


if __name__ == "__main__":
    main()
