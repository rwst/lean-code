#!/usr/bin/env python3
"""Item M3 of plans/plan-beyond-BB13.html §7: where the 449 of Subspace-Theorems' two-variable
count comes from, and what each piece of slack costs BB13's line count N_A = lineCountRho(13/50).

Transcribed from ~/math/Subspace-Theorems (eefd0e0 = 0925fc2 for these definitions):

  m   = subspaceChainLength 1 s ε A = ⌈4 log(2 (n+1) s) / ((n+1)(n+2) η²)⌉      (PenultimateMinimum)
  η   = subspaceEta 1 ε A = ε / (8 (n+1)² (A+1))                                 (PenultimateMinimum)
  ε   = 2 · systemEps 1 δ = δ/2,  A = systemAbsBound 1 2 = 6                     (SystemSubspaceCount)
  4σ⁻¹ = 16 (m+1) / η                                                            (SubspaceCount)
  log X₀ ≈ (m+1) log(2(m+1)/η) + O(log m)       (Evertse's height cost, ConstantsST.frame_threshold_le)
  N_A = 2 + m (1 + log(4σ⁻¹ (1+10⁻⁵)) / log ρ₀) + 1 + log(X₀ / (10⁵ log 3)) / log ρ₀   (LineCoverRho)

with n = 1 (projective dimension), s = 3 forms, δ = 13/50.  So η = δ/448 and
448 = 8 · (n+1)² · (A+1) · 2 = 8 · 4 · 7 · 2,  449/δ = 1 + 448/δ = evertseEtaInvBound.

Where η is consumed (PenultimateMinimum.exists_forall_not_chain): with w = −approxWeight,
  hmix:  (m+1)/(n+1) · (−w) + 2n (m+1) η AW ≤ −(m+1) ε/(4(n+1)),   w ≥ ε/2,
i.e. the deviation error 2nηAW gets HALF of the budget w/(n+1); the other half pays terms that
the free parameters D → ∞ and Qlow (threshold) make arbitrarily small (not_of_key_inequality).
Where m is consumed (SubspaceAuxiliary + MonomialDeviation): Siegel's lemma with conditions ≤ half
the unknowns, #forms ≤ (n+1)s, Chernoff exp(−(n+1)(n+2)η²(m+1)/4) from the RAW second moment
E[(j/N)²] = 2/((n+1)(n+2)) instead of the variance n/((n+1)²(n+2)) (factor 4 at n = 1).
"""
from mpmath import mp, mpf, log, ceil

mp.dps = 30

theta = log(2) / log(3)
eps_star = 2 * theta - 1
delta = mpf(13) / 50
eta_f = (eps_star - delta) / 2                     # FrameSystem's raise at 2 and 3
rho0 = mpf(6309) / 5000
n, n1 = 1, 2

# frame exponents (FrameSystem): ∞: (1−θ, 1); 2: (−θ+η_f, 0); 3: (0, −1+η_f); weight −δ
c = [(1 - theta, mpf(1)), (-theta + eta_f, mpf(0)), (mpf(0), -1 + eta_f)]
P = sum(max(x, 0) for row in c for x in row)       # positive part, 2 − θ
absw = sum(abs(x) for row in c for x in row)       # = 2P + δ (no raise needed: weight is −δ)
# refined deviation weight at n = 1: Σ_v (2|c₁−c₂| + |c_max|) instead of 2n Σ|c|
refined = sum(2 * abs(a - b) + abs(max(a, b)) for a, b in c)


def count(eta, logF, chern=mpf(1)):
    """(m, intervals term, threshold term, N_A) for a given η, log of the Siegel/form factor,
    and Chernoff improvement factor `chern` on the exponent."""
    m = int(ceil(4 * logF / (n1 * (n + 2) * eta ** 2 * chern)))
    inter = m * (1 + log(16 * (m + 1) / eta * (1 + mpf("1e-5"))) / log(rho0))
    logX0 = (m + 1) * log(2 * (m + 1) / eta) + log(m + 1) + 85 * log(2)
    thr = 1 + (logX0 - log(log(3) * 100001)) / log(rho0)
    return m, inter, thr, 2 + inter + thr


def eta_of(w, AW, f=mpf(1) / 2, dev=None):
    """η from the budget: f · w/(n+1) ≥ η · (deviation weight); deviation weight 2n·AW."""
    dw = 2 * n * AW if dev is None else dev
    return f * w / (n1 * dw)


tau = mpf("0.05")
base_eta = (delta / 2) / (8 * n1 ** 2 * 7)         # δ/448
steps = [
    ("baseline (ST eefd0e0)", base_eta, log(12), 1),
    ("(b) η lemma tight: ε/(8n(n+1)A)", eta_of(delta / 4, 6), log(12), 1),
    ("(a) + exact weight w = δ/2", eta_of(delta / 2, 6), log(12), 1),
    ("(c) + frame's |c|-weight", eta_of(delta / 2, absw + delta / 2), log(12), 1),
    ("(d) + budget f = 0.95", eta_of(delta / 2, absw + delta / 2, 1 - tau), log(12), 1),
    ("(e) + no scalar shift, w = δ", eta_of(delta, absw, 1 - tau), log(12), 1),
    ("(f) + #forms 3, Siegel 0.95", eta_of(delta, absw, 1 - tau), log(3 / (1 - tau)), 1),
    ("(g) + Chernoff by variance", eta_of(delta, absw, 1 - tau), log(3 / (1 - tau)), 4),
    ("(h) + refined deviation", eta_of(delta, absw, 1 - tau, refined), log(3 / (1 - tau)), 4),
]
single = [
    ("(b) alone", eta_of(delta / 4, 6), log(12), 1),
    ("(a) alone", base_eta * 2, log(12), 1),
    ("(c) alone", (delta / 2) / (8 * n1 ** 2 * (absw + delta / 2 + 1)), log(12), 1),
    ("(d) alone (f 1/2 → 0.95)", base_eta * 2 * (1 - tau), log(12), 1),
    ("(e) alone (shift γ → 0)", base_eta * 2, log(12), 1),
    ("(f) alone", base_eta, log(3 / (1 - tau)), 1),
    ("(g) alone", base_eta, log(12), 4),
]

if __name__ == "__main__":
    print(f"θ = {float(theta):.6f}  ε* = {float(eps_star):.6f}  δ = {float(delta)}  η_f = {float(eta_f):.6f}")
    print(f"frame: P = {float(P):.4f}  Σ|c| = {float(absw):.4f} (generic bound A = 6)"
          f"  refined dev weight = {float(refined):.4f} (vs 2Σ|c| = {float(2 * absw):.4f})\n")
    hdr = f"{'scenario':<38}{'δ/η':>9}{'m':>12}{'intervals':>12}{'below X₀':>12}{'N_A':>12}"
    for title, rows in (("cumulative", steps), ("one at a time", single)):
        print(title)
        print(hdr)
        for lab, eta, logF, ch in rows:
            m, i, t, N = count(eta, logF, ch)
            print(f"{lab:<38}{float(delta / eta):>9.1f}{m:>12}{float(i):>12.4e}"
                  f"{float(t):>12.4e}{float(N):>12.4e}")
        print()


def lane_at(delta, tau, s, P=None):
    """The certified lane of stages 1–2 (ST `exists_forall_mem_interval_systemSet_two_at`):
    W = (1−τ)δ, A₀ = 2P + (1+τ)δ, ε = 4W/(A₀+2), A = 0, η = subspaceEta 1 (2ε) 0 = ε/16,
    m = ⌈(2/3) log(4s)/η²⌉, X₀ ≤ ratThresholdCoeffTwoAt · (1 + log 2 + log 3) (H = 1, S = {2,3})."""
    P = 2 - theta if P is None else P
    W = (1 - tau) * delta
    A0 = 2 * P + (1 + tau) * delta
    eps = 4 * W / (A0 + 2)
    eta = 2 * eps / 32
    m = int(ceil(4 * log(4 * s) / (6 * eta ** 2)))
    inter = m * (1 + log(16 * (m + 1) / eta * (1 + mpf("1e-5"))) / log(rho0))
    t, beta = 2, 6
    F_log = (m + 1) * log(max(1, 2 * (m + 1) / eta))
    rest = log(8 * (1 + t) * (m + 1) ** 2 * (m + beta + 40 * (1 + t) + 5)
               + 2600 * (1 + t) ** 3 + 96 * (2 / eta + 2) ** 2)
    logX0 = F_log + rest - log(2 * eps) + log(1 + log(2) + log(3))
    thr = 1 + (logX0 - log(log(3) * 100001)) / log(rho0)
    return dict(eps=eps, eta=eta, m=m, inter=inter, thr=thr, N=2 + inter + thr, logX0=logX0)


if __name__ == "__main__":
    print("certified lane (stages 1–2), S = {2,3}, H = 1")
    for d, tau, s in [(delta, mpf(1) / 100, 2), (delta, mpf(1) / 100, 3), (delta, mpf(1) / 1000, 2)]:
        r = lane_at(d, tau, s)
        print(f"δ={float(d)} τ={float(tau)} s={s}: ε={float(r['eps']):.5f} δ/η={float(d / r['eta']):.2f}"
              f" m={r['m']} intervals={float(r['inter']):.4e} below X₀={float(r['thr']):.4e}"
              f" N_A={float(r['N']):.4e} (log X₀ ≈ {float(r['logX0']):.4e})")


def layer_rate_one(eta):
    """ST `Finset.layerRate 1 η` (stage S4): max of the book's 6η²/4 and the variance rate
    chernoffRate 1 η λ = λη − (λ²/2)(1 + 4λ/18)/12 at λ = min(2, 12η)."""
    lam = min(mpf(2), 12 * eta)
    return max(6 * eta ** 2 / 4, lam * eta - lam ** 2 / 2 * (1 + 4 * lam / 18) / 12)


def lane_explicit(delta, tau, eta, eps, f=3, chern=1, variance=False, q=1, dev=False):
    """The certified lane of stage S5 (ST `exists_forall_mem_interval_systemSet_two_of_rothLemmaAt`,
    Evertse's lemma at explicit m, η): budget −W/2 + 2ηA₀ ≤ −ε/4, m minimal with
    4 log(2f) < 6η²(m+1) / chern, f = 3 distinct forms; X₀ ≤ ratThresholdCoeffTwoAt · 3.
    With variance=True (stage S4), m is minimal with log(2f) < (m+1) · layerRate 1 η.
    With Siegel's exponent q (stage S3), 2f becomes (q+1)/q · f and the auxiliary polynomial's
    height constant 40(1+t)+3 is charged q times (ST `ratThresholdCoeffTwoExplicit`).
    With dev=True (item (h)), the budget charges the deviation weight of the pattern read with the
    sum of the ratios pinned, 2 (2 + δ) for the frame (every place has a nonnegative exponent),
    instead of 2 A₀ (ST `approxDevWeight`, `exists_forall_mem_interval_systemSet_two_of_rothLemmaAt`)."""
    P = 2 - theta
    W = (1 - tau) * delta
    A0 = 2 * P + (1 + tau) * delta
    charge = 2 * (2 + delta) if dev else 2 * A0
    assert -W / 2 + eta * charge <= -eps / 4, "budget"
    if variance:
        rate = layer_rate_one(eta)
    else:
        rate = 6 * eta ** 2 * chern / 4
    lf = log((q + 1) / mpf(q) * f)
    m = int(lf / rate)
    while not lf < (m + 1) * rate:
        m += 1
    inter = m * (1 + log(16 * (m + 1) / eta * (1 + mpf("1e-5"))) / log(rho0))
    t, beta = 2, 6
    F_log = (m + 1) * log(max(1, 2 * (m + 1) / eta))
    rest = log(8 * (1 + t) * (m + 1) ** 2 * (m + beta + q * (40 * (1 + t) + 3) + 2)
               + 2600 * (1 + t) ** 3 + 16 * (q - 1) * (3 + 40 * (1 + t)) + 96 * (2 / eta + 2) ** 2)
    logX0 = F_log + rest - log(2 * eps) + log(1 + log(2) + log(3))
    thr = 1 + (logX0 - log(log(3) * 100001)) / log(rho0)
    return dict(m=m, inter=inter, thr=thr, N=2 + inter + thr, logX0=logX0)


if __name__ == "__main__":
    print("\ncertified lane (stage S5, explicit m, η), δ = 13/50, τ = 1/1000, ε = 1/1000")
    r = lane_explicit(delta, mpf(1) / 1000, mpf(27) / 1250, mpf(1) / 1000)
    print(f"η = 27/1250, book rate: m={r['m']} intervals={float(r['inter']):.4e}"
          f" below X₀={float(r['thr']):.4e} N_A={float(r['N']):.4e}  (S5 only; was ≤ 300 000)")
    r = lane_explicit(delta, mpf(1) / 1000, mpf(27) / 1250, mpf(1) / 1000, chern=4)
    print(f"  exact variance (×4, no Bennett factor): m={r['m']} N_A={float(r['N']):.4e}")
    r = lane_explicit(delta, mpf(1) / 1000, mpf(27) / 1250, mpf(1) / 1000, variance=True)
    print(f"  + S4 (layerRate, certified): m={r['m']} intervals={float(r['inter']):.4e}"
          f" below X₀={float(r['thr']):.4e} N_A={float(r['N']):.4e}"
          f"  (Lean: ≤ 72 000, LineCoverSharp)")
    for q in (9, 99, 999):
        r = lane_explicit(delta, mpf(1) / 1000, mpf(27) / 1250, mpf(1) / 1000, variance=True, q=q)
        print(f"  + S3 (Siegel exponent q = {q}): m={r['m']} intervals={float(r['inter']):.4e}"
              f" below X₀={float(r['thr']):.4e} N_A={float(r['N']):.4e}"
              + ("  (Lean: ≤ 42 200, LineCoverSharp)" if q == 999 else ""))


if __name__ == "__main__":
    W = (1 - mpf(1) / 1000) * delta
    print(f"\n(h) deviation budget: η ≤ (W/2 − ε/4)/(2(2+δ)) = {float((W / 2 - mpf(1) / 4000) / (2 * (2 + delta))):.6f}"
          f"  (book: 2 A₀ = {float(2 * (2 * (2 - theta) + (1 + mpf(1) / 1000) * delta)):.4f}, dev: {float(2 * (2 + delta)):.4f})")
    for eta in (mpf(143) / 5000, mpf(1433) / 50000):
        r = lane_explicit(delta, mpf(1) / 1000, eta, mpf(1) / 1000, variance=True, q=999, dev=True)
        print(f"  + (h) η = {float(eta)}: m={r['m']} intervals={float(r['inter']):.4e}"
              f" below X₀={float(r['thr']):.4e} N_A={float(r['N']):.4e}")
