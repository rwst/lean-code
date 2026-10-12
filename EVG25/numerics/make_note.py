# (C) 2026 Ralf Stephan, in collaboration with Claude Code. Released under CC0 1.0 Universal.
"""Writes plans/note-EVGQ17M0-XH.html from data/summary.json (plan-EVGQ17-M0, M6 / G-1).
Usage (from EVG25/numerics): python3 analyze.py && python3 make_note.py"""
import json, math
S = json.load(open("data/summary.json"))
style = open("../../plans/note-EVGQ17M0-G0.html").read()
head = style[:style.find("</head>")]
head = head.replace("plan-EVGQ17-M0 gate G&#8209;0 &mdash; prior-art memo", "plan-EVGQ17-M0 M6 &mdash; numerics past the horizon")
N0S = {"0": r"\(0\)", "1e15": r"\(10^{15}+12345\)", "sqrt2": r"\(\lfloor\sqrt2\cdot10^{37}\rfloor\)"}

def f(x, p=2): return f"{x:+.{p}f}".replace("-", "&minus;")
def i(x): return str(x).replace("-", "&minus;")

# --- table 1: beta_j
r0 = {r["j"]: r for r in S["0"]}
t1 = "<table><tr><th>\\(j\\)</th>" + "".join(f"<th>{j}</th>" for j in range(14, 33)) + "</tr>"
t1 += "<tr><th>\\(\\beta_j\\)</th>" + "".join(f"<td>{i(r0[j]['beta'])}</td>" for j in range(14, 33)) + "</tr>"
t1 += "<tr><th>\\(2^{j/2}/2\\)</th>" + "".join(f"<td>{round(2**(j/2)/2)}</td>" for j in range(14, 33)) + "</tr>"
t1 += "<tr><th>ratio</th>" + "".join(f"<td>{f(r0[j]['beta_norm'],3)}</td>" for j in range(14, 33)) + "</tr></table>"

# --- table 2: per-window summary
def rowfmt(tag, r):
    zb = r["z_boundary"]; w = next((t for t, v in enumerate(zb) if abs(v) > 0.25), 14)
    zf = r["z_far"]; m = sum(zf) / len(zf)
    ac = sum((a - m) * (b - m) for a, b in zip(zf, zf[1:])) / sum((a - m) ** 2 for a in zf)
    rms = math.sqrt(sum(v * v for v in zf) / len(zf))
    return (f"<tr><td>{N0S[tag]}</td><td>{r['j']}</td><td>{i(r['beta'])}</td><td>{f(r['beta_norm'],3)}</td>"
            f"<td>{w}</td><td>{max(map(abs, zb[:4])):.3f}</td><td>{r['chi2_df']:.3f}</td><td>{rms:.2f}</td><td>{f(ac)}</td>"
            f"<td>{r['tail_z_max']:.1f}</td><td>{r['var_dev']*1e4:.1f}</td><td>{'yes' if r['exact_below_horizon'] else 'NO'}</td></tr>")
t2 = ("<table><tr><th>\\(N_0\\)</th><th>\\(j\\)</th><th>\\(\\beta_j\\)</th><th>\\(\\beta_j/(2^{j/2}/2)\\)</th>"
      "<th>layer width</th><th>max \\(|z|\\), \\(t\\le3\\)</th><th>\\(\\chi^2/\\mathrm{df}\\), block at \\(j\\)</th>"
      "<th>rms \\(z\\), \\(t\\ge14\\)</th><th>lag-1 autocorr., \\(t\\ge14\\)</th><th>max \\(|z|\\) of tails, \\(k\\in(j,3j]\\)</th>"
      "<th>max \\(|\\mathrm{Var}/k-1|\\cdot10^4\\)</th><th>exact for \\(k\\le j\\)</th></tr>")
for tag in ("0", "1e15", "sqrt2"):
    for r in S[tag]:
        if r["j"] >= 20 and (tag != "0" or r["j"] % 2 == 0 or r["j"] >= 25):
            t2 += rowfmt(tag, r)
t2 += "</table>"

# --- table 3: boundary profiles
t3 = "<table><tr><th>\\(N_0\\)</th><th>\\(j\\)</th>" + "".join(f"<th>\\(t={t}\\)</th>" for t in range(14)) + "</tr>"
for tag in ("0", "sqrt2"):
    for r in S[tag]:
        if r["j"] >= 24:
            cells = "".join(
                f"<td style=\"background:{'#dcebdc' if abs(v)<=0.1 else ('#f3e2c8' if abs(v)>=1 else 'transparent')}\">{f(v)}</td>"
                for v in r["z_boundary"])
            t3 += f"<tr><td>{N0S[tag]}</td><td>{r['j']}</td>{cells}</tr>"
t3 += "</table>"

# --- figure: beta_j/(2^{j/2}/2), three windows
W, H, x0, x1, y0, y1 = 760, 300, 60, 740, 20, 260
def X(j): return x0 + (j - 8) / (32 - 8) * (x1 - x0)
def Y(v): return y0 + (2.5 - v) / 5 * (y1 - y0)
svg = [f'<svg viewBox="0 0 {W} {H+30}" width="100%" role="img" aria-label="beta_j normalized by coin scale, j=8..32, three seed windows">']
svg.append(f'<rect x="{x0}" y="{Y(2)}" width="{x1-x0}" height="{Y(-2)-Y(2)}" fill="#eef0f5"/>')
svg.append(f'<rect x="{x0}" y="{Y(1)}" width="{x1-x0}" height="{Y(-1)-Y(1)}" fill="#dce4f3"/>')
for v in (-2, -1, 0, 1, 2):
    svg.append(f'<line x1="{x0}" x2="{x1}" y1="{Y(v)}" y2="{Y(v)}" stroke="#bbb" stroke-width="{1 if v else 1.5}"/>')
    svg.append(f'<text x="{x0-8}" y="{Y(v)+4}" font-size="12" text-anchor="end">{i(v)}</text>')
for j in range(8, 33, 2):
    svg.append(f'<text x="{X(j)}" y="{y1+18}" font-size="12" text-anchor="middle">{j}</text>')
svg.append(f'<text x="{(x0+x1)/2}" y="{y1+36}" font-size="12" text-anchor="middle">j (seeds N0 + r, r &lt; 2^j)</text>')
cols = {"0": "#1f3a7a", "1e15": "#b5791f", "sqrt2": "#3a6b3a"}
for tag, c in cols.items():
    pts = [(X(r["j"]), Y(max(-2.5, min(2.5, r["beta_norm"])))) for r in S[tag]]
    svg.append(f'<polyline fill="none" stroke="{c}" stroke-width="1.2" points="' + " ".join(f"{a:.1f},{b:.1f}" for a, b in pts) + '"/>')
    for a, b in pts: svg.append(f'<circle cx="{a:.1f}" cy="{b:.1f}" r="3" fill="{c}"/>')
for k, (tag, c) in enumerate(cols.items()):
    svg.append(f'<circle cx="{x1-200}" cy="{y0+12+16*k}" r="4" fill="{c}"/><text x="{x1-190}" y="{y0+16+16*k}" font-size="12">N0 = {["0","10^15+12345","floor(sqrt2·10^37)"][k]}</text>')
svg.append("</svg>")
fig = "\n".join(svg)

body = open("note_body.html").read()
for k, v in {"@T1@": t1, "@T2@": t2, "@T3@": t3, "@FIG@": fig}.items(): body = body.replace(k, v)
open("../../plans/note-EVGQ17M0-XH.html", "w").write(head + "</head>\n<body>\n" + body + "\n</body>\n</html>\n")
print("wrote plans/note-EVGQ17M0-XH.html")
