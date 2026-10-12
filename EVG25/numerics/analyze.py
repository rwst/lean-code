# (C) 2026 Ralf Stephan, in collaboration with Claude Code. Released under CC0 1.0 Universal.
"""Summaries of the horizon.c runs in data/ for plan-EVGQ17-M0 M6 / gate G-1.
Usage: python3 analyze.py  (writes data/summary.json, prints tables)"""
import json, math, glob, os
from math import comb

def binom_tail(k, frac=0.15):
    # P(|S - k/2| > frac*k) for S ~ Bin(k,1/2), with the same integer test as horizon.c: 10|2S-k| > 3k
    return sum(comb(k, s) for s in range(k + 1) if 10 * abs(2 * s - k) > 3 * k) / 2 ** k

def load(tag):
    out = {}
    for f in glob.glob(f"data/j*_{tag}.json"):
        d = json.load(open(f)); out[d["j"]] = d
    return dict(sorted(out.items()))

summary = {}
for tag in ("0", "1e15", "sqrt2"):
    runs = load(tag); rows = []
    for j, d in runs.items():
        R = d["seeds"]; half = R // 2; sc = math.sqrt(R) / 2
        z = [(o - half) / sc for o in d["odd"]]          # z_{j,i}
        K = d["K"]
        var = [d["sD2"][k] / R / k if k else 0 for k in range(K + 1)]  # Var(D_k)/k, coin: 1
        mean = [d["sD"][k] / R / math.sqrt(k) if k else 0 for k in range(K + 1)]
        tail = [d["tail"][k] / R for k in range(K + 1)]
        bt = [binom_tail(k) for k in range(K + 1)]
        # tail z-score vs binomial (sampling sd of a proportion)
        tz = [(tail[k] - bt[k]) / math.sqrt(max(bt[k] * (1 - bt[k]), 1e-300) / R) if 0 < bt[k] < 1 else 0 for k in range(K + 1)]
        # pair correlations: z of (#unequal - R/2) for adjacent letters, i in [j, 3j-d)
        pc = {dd: [(d[f"xr{dd}"][i] - half) / sc for i in range(j, K - dd)] for dd in (1, 2, 3)}
        blk = d["blk"]; E = R / 256
        chi = sum((c - E) ** 2 / E for c in blk) / 255
        exact_ok = all(o == half for o in d["odd"][:j]) and all(abs(tail[k] - bt[k]) < 1e-12 for k in range(1, j + 1))
        rows.append(dict(j=j, beta=d["beta"], pair=d["pair"], beta_norm=d["beta"] / sc,
                         z_boundary=z[j:j + 14], z_far=z[j + 14:], zmax_far=max(map(abs, z[j + 14:]), default=0),
                         var=var, mean=mean, tail=tail, binom=bt, tail_z=tz,
                         tail_z_max=max(map(abs, tz[j + 1:])), var_dev=max(abs(v - 1) for v in var[j + 1:]),
                         pc_max={dd: max(map(abs, pc[dd])) for dd in pc}, pc_rms={dd: math.sqrt(sum(v * v for v in pc[dd]) / len(pc[dd])) for dd in pc},
                         chi2_df=chi, exact_below_horizon=exact_ok))
    summary[tag] = rows
json.dump(summary, open("data/summary.json", "w"))

for tag, rows in summary.items():
    print(f"\n== N0 tag {tag}")
    print(" j   beta  pair  beta/sd  max|z| j..j+13  rms z j..j+13  max|z| >j+13  chi2/df  var dev  max|tail z|  pc rms d=1,2,3  exact<=j")
    for r in rows:
        zb = r["z_boundary"]
        print(f"{r['j']:2d} {r['beta']:6d} {r['pair']:5d} {r['beta_norm']:8.3f} {max(map(abs,zb)):9.2f} {math.sqrt(sum(v*v for v in zb)/len(zb)):12.2f} "
              f"{r['zmax_far']:12.2f} {r['chi2_df']:8.3f} {r['var_dev']:8.4f} {r['tail_z_max']:10.2f}  "
              + " ".join(f"{r['pc_rms'][d]:.2f}" for d in (1,2,3)) + f"  {r['exact_below_horizon']}")
