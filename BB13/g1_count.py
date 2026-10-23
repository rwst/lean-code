#!/usr/bin/env python3
"""Gate G-1 of plans/plan-beyond-BB13.html: the exact value of Subspace-Theorems'
two-variable count at BB13's frame.

Transcribes, from ~/math/Subspace-Theorems (pinned e443c24, same defs at 09835cb):
  systemEps e δ           = e δ / 4                       (SystemSubspaceCount.lean)
  systemAbsBound e n      = e (2n + 2)
  subspaceEta n ε A       = min 1 (ε / (8 (n+1)^2 (A+1)))  (PenultimateMinimum.lean)
  subspaceChainLength     = ⌈4 log(2(n+1)s) / ((n+1)(n+2) η²)⌉₊
  evertseRatio n s ε A    = η / (4 (m+1))                  (QuantitativeSubspace/SubspaceCount.lean)
  RothParams.evertse.factor = n · max(1, 2(m+1)/η)^(m+1) · (m+1)
  systemLargeCountTwo R e s δ
      = 2 + m · (1 + log(4 σ⁻¹) / log(1 + δ/4))  at (n, ε, A) = (1, 2·systemEps e δ, systemAbsBound e 2)
  exists_finset_submodule_of_isNormalizedSystem_two: total
      = δ⁻¹ ((10³·2)^2 + 8 log log 4H) + (1 + log(systemMiddleRatio)/log(1 + δ/4)) + large
  systemMiddleRatio d n H δ X = max 1 (X / (d log max(2H, n^(2n/δ))))

The frame (BB13): K = E = ℚ, ι = Fin 2, S = {2, 3}, x = (m_n 2^n, 3^n),
  ∞: forms (X₁ − X₂, X₂), exponents (1 − θ, 1)
  2: forms (X₁, X₂),      exponents (−θ + η₂, 0)
  3: forms (X₁, X₂),      exponents (0, −1 + η₃)
weight 1 − 2θ + η₂ + η₃ = −(ε* − η₂ − η₃); 3 distinct forms (s = 3), coefficient height H = 1.
The η's are forced (gate G-2): all three constants must be 1, and H(x) = max(m_n 2^n, 3^n)
exceeds 3^n by a factor ≤ 1 + 2^{-n}; any η > 0 works above a threshold n₁(η).
"""
from mpmath import mp, mpf, log, ceil, inf

mp.dps = 40

theta = log(2) / log(3)
eps_star = 2 * theta - 1
rho0 = 1 + eps_star - theta / 100001
RECORD = mpf(2) ** 36 + mpf(2) ** 34
K_eps_star = mpf("1.856e12")


def chain(delta, s, e=1):
    """(m, η, 4σ⁻¹) of systemLargeCountTwo at e, s, δ (Evertse's Roth lemma)."""
    eps = 2 * (e * delta / 4)            # 2 · systemEps
    A = e * (2 * 2 + 2)                  # systemAbsBound e 2
    n = 1
    eta = min(mpf(1), eps / (8 * (n + 1) ** 2 * (A + 1)))
    m = int(ceil(4 * log(2 * (n + 1) * s) / ((n + 1) * (n + 2) * eta ** 2)))
    sigma = eta / (4 * (m + 1))
    return m, eta, 4 / sigma


def large(delta, s, gap):
    """systemLargeCountTwo with the per-interval gap ratio `gap` in the log-height
    (generic: 1 + δ/4; BB13 elementary: ρ₀)."""
    m, eta, rho = chain(delta, s)
    return 2 + m * (1 + log(rho) / log(gap))


def closed_form(delta, s):
    """systemLargeCountTwo_evertse_le."""
    l = 1 + log(4 * s)
    Y = 449 / delta
    return 2 + 2 * l * Y ** 2 * (1 + 5 * log(32 * l * Y ** 3) / delta)


def log_threshold(delta, s, slack=mpf(30)):
    """Upper estimate of log X₀, X₀ = systemThresholdTwo.  X₀ is a max of terms each
    polynomial in m, 1/δ and the (tiny) form heights, except penultimateThreshold's
    chainThreshold term 8·3·factor·(m+1)·(aux + shift)/(δ/2), whose factor is
    max(1, 2(m+1)/η)^(m+1)·(m+1).  So log X₀ = (m+1) log(2(m+1)/η) + O(log m); `slack`
    covers the O(log m) (≈ 3 log m + 10 ≈ 60 would be generous; its effect on the count is
    slack/log(1+δ/4), i.e. ≈ 500 subspaces at slack 30)."""
    m, eta, _ = chain(delta, s)
    logfactor = (m + 1) * log(2 * (m + 1) / eta) + log(m + 1)
    shift = 6 + m + 2                     # max(b(m+1),0) + m + 2, b = h(P¹) ≤ 5.4
    return logfactor + log(24 * (m + 1) * (10 + shift) / (delta / 2)) + slack


def middle(delta, s, gap):
    logQ = log(max(mpf(2), mpf(2) ** (4 / delta)))  # d = 1, n = 2, H = 1
    return 1 + (log_threshold(delta, s) - log(logQ)) / log(gap)


def small(delta, H=1):
    return (mpf(2000) ** 2 + 8 * log(log(4 * H))) / delta


def row(label, delta, s):
    m, eta, rho = chain(delta, s)
    g = 1 + delta / 4
    Lg, Lr = large(delta, s, g), large(delta, s, rho0)
    Mg, Mr = middle(delta, s, g), middle(delta, s, rho0)
    Sm = small(delta)
    # BB13 middle range by census + ρ₀-gap: lines with least member n ∈ (10⁵, X₀/log 3]
    Mbb = 5 + 1 + (log_threshold(delta, s) - log(log(3) * 100001)) / log(rho0)
    tot_generic = Sm + Mg + Lg
    tot_A5 = Mbb + Lr
    print(f"{label:>12} δ={float(delta):.6f} s={s}  m={m:.4e}  η⁻¹={float(1/eta):.2f}"
          f"  log(4σ⁻¹)={float(log(rho)):.3f}")
    print(f"{'':>12} per interval: generic {float(1 + log(rho) / log(g)):.1f},"
          f" ρ₀ {float(1 + log(rho) / log(rho0)):.1f}")
    print(f"{'':>12} large: exact {float(Lg):.4e}  (closed form {float(closed_form(delta, s)):.4e})"
          f"  ρ₀ {float(Lr):.4e}")
    print(f"{'':>12} log X₀ ≈ {float(log_threshold(delta, s)):.4e}"
          f"  middle: generic {float(Mg):.4e}  ρ₀(BB13) {float(Mbb):.4e}")
    print(f"{'':>12} small {float(Sm):.4e}")
    print(f"{'':>12} TOTAL generic (A1–A4) {float(tot_generic):.4e}"
          f"   = record/{float(RECORD / tot_generic):.1f} = K(ε*)/{float(K_eps_star / tot_generic):.0f}")
    print(f"{'':>12} TOTAL A5 (ρ₀ everywhere)  {float(tot_A5):.4e}"
          f"   = record/{float(RECORD / tot_A5):.1f}")
    print()


if __name__ == "__main__":
    print(f"θ = {float(theta):.10f}, ε* = {float(eps_star):.10f}, ρ₀ = {float(rho0):.10f},"
          f" log ρ₀ = {float(log(rho0)):.6f}, log(1+ε*/4) = {float(log(1 + eps_star / 4)):.6f}")
    print(f"record 2^36+2^34 = {float(RECORD):.4e}, K(ε*) = {float(K_eps_star):.4e}\n")
    row("frame", eps_star - mpf("1e-6"), 3)
    row("δ = ε*", eps_star, 3)
    row("s = 4", eps_star - mpf("1e-6"), 4)
    row("δ = ε*/2", eps_star / 2, 3)
    # sensitivity to the G-2 slack η₂ + η₃
    for d in ["1e-4", "1e-3", "1e-2"]:
        dd = eps_star - mpf(d)
        print(f"η₂+η₃ = {d}: generic total {float(small(dd) + middle(dd, 3, 1 + dd / 4) + large(dd, 3, 1 + dd / 4)):.4e}")
