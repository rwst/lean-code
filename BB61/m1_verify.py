#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M1 of plans/plan-1061.html -- numerical verification of every statement of sec 2.

One check per numbered result of note-1061-M1.html, run at a quadratic unit, a
quadratic non-unit (so that Mbar is a proper endomorphism), a totally real cubic and a
cubic with a complex pair.  Writes m1_verify.json.
"""
from m0_engine import Alpha, orbit, orbit_direct_mp
from m1_field import Field, Fr, matpow, matvec, det, mattrace
from m1_torus import Torus
import numpy as np, math, json, itertools, mpmath as mp

CASES = [([1, -2, -1], '1+sqrt2',        'quadratic unit'),
         ([1, -4, 1],  '2+sqrt3',        'quadratic unit, certified gap'),
         ([1, -5, -2], 'X^2-5X-2',       'quadratic NON-unit, |N|=2'),
         ([1, -5, 1, -1], 'X^3-5X^2+X-1', 'cubic, complex pair'),
         ([1, -4, 0, 1],  'X^3-4X^2+1',    'cubic, totally real (r1=3)')]

R = {}


def rec(key, val, ok=None):
    R.setdefault(key, {})
    return val


def sect(t):
    print('\n' + '=' * 78 + '\n' + t + '\n' + '=' * 78)


# ---------------------------------------------------------------- Lemma 1
sect('Lemma 1 -- C(alpha) is a Cantor set; strong separation needs alpha > 2')
L1 = []
for c, n, tag in CASES:
    al = Alpha(c, n)
    a = al.a
    g = (a - 2) / a
    # min separation of the 2^K level-K cylinders
    K = 12
    v = np.zeros(1)
    for k in range(1, K + 1):
        v = np.concatenate([v, v + (a - 1) * a ** (-k)])
    v.sort()
    sep = np.diff(v).min()
    pred = g * a ** (-(K - 1))
    L1.append(dict(name=n, alpha=a, gap=g, minsep=float(sep), pred=float(pred),
                   dim=math.log(2) / math.log(a), ok=bool(sep >= pred * (1 - 1e-9))))
    print('%-16s alpha=%9.6f  g=(a-2)/a=%.6f  min cyl sep(K=12)=%.3e  >= g*a^-11=%.3e  %s  dim=%.5f'
          % (n, a, g, sep, pred, 'OK' if sep >= pred * (1 - 1e-9) else 'FAIL', math.log(2) / math.log(a)))
R['L1_cantor'] = L1

# ---------------------------------------------------------------- Lemma 2
sect('Lemma 2 -- trace splitting  {xi a^n} = {t_n - S_n},  c_m, sum c_m = -(d-1)')
L2 = []
for c, n, tag in CASES:
    al = Alpha(c, n)
    F = Field(c)
    d = al.d
    # (i) c_m three ways
    M = 40
    c_conj = al.c_m_mp(M)
    TR = F.traces(M + 2)
    c_trace = [TR[m + 1] - TR[m] for m in range(M)]            # Tr(a^{m+1}) - Tr(a^m)
    e1 = max(abs(float(c_conj[m] - (mp.mpf(int(c_trace[m])) - al.alpha ** m * (al.alpha - 1))))
             for m in range(M))
    # (ii) c_m obeys alpha's own linear recurrence
    co = [int(x) for x in c]
    e2 = max(abs(float(sum(co[i] * c_conj[m + d - i] for i in range(d + 1))))
             for m in range(M - d - 1))
    # (iii) sum_m c_m = -(d-1)
    tot = float(sum(al.c_m_mp(600)))
    # (iv) |c_m| <= C_alpha rho^m
    Ca = float(sum(abs(z - 1) for z in al.conj))
    e4 = max(float(abs(c_conj[m])) - Ca * al.r ** m for m in range(M))
    # (v) the splitting itself, at 200 dps
    rng = np.random.default_rng(7)
    eps = rng.integers(0, 2, 4000).astype(np.int8)
    N = 300
    dps = int(N * math.log10(al.a)) + 80        # {xi a^n} needs n log10(alpha) guard digits
    xd = orbit_direct_mp(al, eps, N, dps=dps)
    xe = orbit(al, eps)[:N]
    e5 = float(np.abs(((xd - xe + .5) % 1.0) - .5).max())
    L2.append(dict(name=n, d=d, dps=dps, c_formula_err=e1, c_recurrence_err=e2, sum_cm=tot,
                   sum_target=-(d - 1), tail_bound_slack=e4, splitting_err=e5, Calpha=Ca))
    print('%-16s d=%d  |c_m - (Tr diff)|<=%.2e  |recurrence|<=%.2e  sum c_m=%+.12f (target %+d)  '
          'max(|c_m|-C rho^m)=%.2e  |split-200dps|<=%.2e'
          % (n, d, e1, e2, tot, -(d - 1), e4, e5))
R['L2_splitting'] = L2

# ---------------------------------------------------------------- Prop 3
sect('Prop 3 -- exact confinement: S_n in K and t_n in C for every n (no O(rho^n))')
P3 = []
for c, n, tag in CASES:
    al = Alpha(c, n)
    Mdep = 400
    cm = np.array(al.c_m(Mdep))
    Kmin, Kmax = cm[cm < 0].sum(), cm[cm > 0].sum()
    rng = np.random.default_rng(11)
    eps = rng.integers(0, 2, 20000).astype(np.int8)
    # recompute S_n exactly as sum_{m<n} c_m eps_{n-m}
    worst = -np.inf
    Ns = 2000
    for nn in range(1, Ns):
        pass
    # vectorised: S_n = convolution
    S = np.convolve(eps[:Ns].astype(float), cm)[:Ns]
    # S_n uses eps_1..eps_n  -> shift
    inK = float(max((Kmin - S.min()), (S.max() - Kmax)))
    P3.append(dict(name=n, Kmin=float(Kmin), Kmax=float(Kmax), Smin=float(S.min()),
                   Smax=float(S.max()), excess=inK, diamK=float(Kmax - Kmin),
                   d_minus_1=al.d - 1))
    print('%-16s K=[%+.6f,%+.6f]  observed S_n in [%+.6f,%+.6f]  excess=%.2e  '
          'diam K=%.6f >= d-1=%d  %s'
          % (n, Kmin, Kmax, S.min(), S.max(), inK, Kmax - Kmin, al.d - 1,
             'OK' if inK <= 1e-12 and Kmax - Kmin >= al.d - 1 - 1e-12 else 'FAIL'))
R['P3_confinement'] = P3

# ---------------------------------------------------------------- Cor 4
sect('Cor 4 -- Route A can fire only above 2^d:  A(alpha) >= d log2 / log alpha')
C4 = []
for c, n, tag in CASES:
    al = Alpha(c, n)
    A = al.routeA()
    lb = al.d * math.log(2) / math.log(al.a)
    rhomin = al.a ** (-1.0 / (al.d - 1)) if al.d > 1 else 0.0
    C4.append(dict(name=n, A=A, lower=lb, rho=al.r, rho_min=rhomin, ok=bool(A >= lb - 1e-12)))
    print('%-16s A(alpha)=%.5f  >= d log2/log a = %.5f  %s   rho=%.5f >= a^{-1/(d-1)}=%.5f  %s'
          % (n, A, lb, 'OK' if A >= lb - 1e-12 else 'FAIL', al.r, rhomin,
             'OK' if al.r >= rhomin - 1e-12 else 'FAIL'))
R['C4_routeA'] = C4

# ---------------------------------------------------------------- Lemma 5
sect('Lemma 5 -- F(sigma^n omega~) = {xi alpha^n} for the zero-padded word')
L5 = []
for c, n, tag in CASES:
    al = Alpha(c, n)
    a = al.a
    cm = al.c_m(600)
    rng = np.random.default_rng(3)
    eps = rng.integers(0, 2, 3000).astype(np.int8)
    N = 200
    err = 0.0
    for nn in range(N):
        t = (a - 1) * sum(float(eps[nn + j - 1]) * a ** (-j) for j in range(1, 120))
        S = sum(cm[m] * (float(eps[nn - m - 1]) if m < nn else 0.0) for m in range(min(nn, 400)))
        Fv = (t - S) % 1.0
        xd = orbit_direct_mp(al, eps, nn + 1, dps=int(nn * math.log10(a)) + 80)[nn]
        err = max(err, abs(((Fv - xd + .5) % 1.0) - .5))
    L5.append(dict(name=n, max_err=float(err)))
    print('%-16s max_n<200 |F(sigma^n w~) - {xi a^n}| = %.3e' % (n, err))
R['L5_factor'] = L5

# ---------------------------------------------------------------- Thm 6 / Prop 7
sect('Thm 6 + Prop 7 -- empirical limits are F_* mu; realization of a Markov mu')
from m0_words import w_markov
from m0_markov import Fhat
T6 = []
NN = 1000000
p01, p10 = 0.30, 0.70
for c, n, tag in CASES:
    al = Alpha(c, n)
    eps = w_markov(NN + 4000, p01, p10, seed=5)
    x = orbit(al, eps)[:NN]
    row = dict(name=n, N=NN, p01=p01, p10=p10, modes=[])
    for h in (1, 2, 3, 5, 8):
        emp = complex(np.exp(2j * np.pi * h * x).mean())
        ex = Fhat(al, h, np.array([p01, 1 - p10]), 1)
        row['modes'].append(dict(h=h, emp_abs=abs(emp), exact_abs=abs(ex),
                                 diff=abs(emp - ex)))
    worst = max(m['diff'] for m in row['modes'])
    row['max_diff'] = worst
    row['noise_floor'] = NN ** -0.5
    T6.append(row)
    print('%-16s  ' % n + '  '.join('h=%d |emp|=%.5f |exact|=%.5f d=%.4f'
          % (m['h'], m['emp_abs'], m['exact_abs'], m['diff']) for m in row['modes'][:3]))
    print('%-16s  max|emp-exact| over h in {1,2,3,5,8} = %.4f   (MC floor 1/sqrt(N) = %.4f)'
          % ('', worst, NN ** -0.5))
R['T6_realization'] = T6

# ---------------------------------------------------------------- Prop 8-9
sect('Prop 8-9 -- the Minkowski torus: tau = Tr, Mbar has degree |N(alpha)|, Phi o sigma = Mbar o Phi')
P8 = []
for c, n, tag in CASES:
    al = Alpha(c, n)
    F = Field(c)
    T = Torus(al)
    d = al.d
    # (i) tau o iota = Tr  on 1, a, ..., a^{2d}
    TR = F.traces(2 * d + 1)
    e_tau = max(abs(T.tau(T.iota_pow(i)) - float(TR[i])) for i in range(2 * d + 1))
    e_int = max(abs(T.tau(T.iota_pow(i)) - round(T.tau(T.iota_pow(i)))) for i in range(2 * d + 1))
    # (ii) M in the lattice basis is the companion matrix (integer), det = N(alpha)
    Cmat = T.Binv @ T.M @ T.B
    comp = np.array([[float(x) for x in row] for row in F.C])
    e_comp = float(np.abs(Cmat - comp).max())
    Nal = int(F.norm([0, 1] + [0] * (d - 2)) if d > 1 else F.norm([0]))
    detM = float(np.linalg.det(T.M))
    # (iii) tau(Mbar^n p(xi)) = {xi a^n} for a random REAL xi (not in C(alpha)).
    #      (a) direct: Mbar^k p(xi) is the class of (xi a^k, 0, ..., 0); mpmath, k <= 40.
    rng = np.random.default_rng(19)
    xi = float(rng.random()) * 7.0
    e_orb = 0.0
    for k in range(1, 41):
        with mp.workdps(int(k * math.log10(al.a)) + 60):
            xk = mp.mpf(xi) * mp.mpf(al.alpha) ** k
            v = np.zeros(d); v[0] = float(mp.frac(xk))     # (xi a^k,0..0) - (floor,0..0), floor in Lambda
            v = T.reduce(v)
            e_orb = max(e_orb, abs(((T.tau(v) - float(mp.frac(xk)) + .5) % 1.0) - .5))
    #      (b) iterating Mbar in double precision: how far before the expansion eats the mantissa
    v = np.zeros(d); v[0] = xi
    k_stable = 0
    for k in range(1, 61):
        v = T.reduce(T.M @ v)
        with mp.workdps(int(k * math.log10(al.a)) + 60):
            ex = float(mp.frac(mp.mpf(xi) * mp.mpf(al.alpha) ** k))
        if abs(((T.tau(v) - ex + .5) % 1.0) - .5) > 1e-6:
            break
        k_stable = k
    # (iv) Phi o sigma = Mbar o Phi
    rng = np.random.default_rng(23)
    om = rng.integers(0, 2, 600).astype(int)      # om[0..299] = past, om[300..] = future
    P, Fu = list(om[:300]), list(om[300:])
    e_equi = 0.0
    for k in range(30):
        past = [Fu[k - 1 - i] if i < k else P[i - k] for i in range(300)]
        fut = Fu[k:]
        lhs = T.Phi(past, fut)
        past0 = [Fu[k - 2 - i] if i < k - 1 else P[i - k + 1] for i in range(300)] if k >= 1 else P
        rhs = T.reduce(T.M @ T.Phi(past0, Fu[k - 1:])) if k >= 1 else None
        if rhs is not None:
            e_equi = max(e_equi, T.dist(lhs, rhs))
    # (v) tau o Phi = F
    cm = al.c_m(400)
    e_tf = 0.0
    for k in range(20):
        past = [Fu[k - 1 - i] if i < k else P[i - k] for i in range(300)]
        fut = Fu[k:]
        Fv = ((al.a - 1) * sum(fut[j] * al.a ** (-(j + 1)) for j in range(120))
              - sum(cm[m] * past[m] for m in range(300))) % 1.0
        e_tf = max(e_tf, abs(((T.tau(T.Phi(past, fut)) - Fv + .5) % 1.0) - .5))
    P8.append(dict(name=n, d=d, r1=T.r1, r2=T.r2, tau_is_trace_err=e_tau,
                   tau_integrality_err=e_int, companion_err=e_comp, N_alpha=Nal,
                   det_M=detM, is_unit=bool(abs(Nal) == 1), degree_Mbar=abs(Nal),
                   toral_identity_err=e_orb, float_stable_steps=k_stable,
                   equivariance_err=e_equi, tau_Phi_eq_F_err=e_tf))
    print('%-16s r1=%d r2=%d  |tau o iota - Tr|=%.1e  |companion|=%.1e  N(a)=%+d  det M=%+.6f  '
          'Mbar %s  |tau(M^n p(xi))-{xi a^n}|=%.1e (n<=40)  float-iter stable to n=%d  '
          '|Phi.sigma - M.Phi|=%.1e  |tau.Phi - F|=%.1e'
          % (n, T.r1, T.r2, e_tau, e_comp, Nal, detM,
             ('AUTOMORPHISM' if abs(Nal) == 1 else '%d-to-1 ENDOmorphism' % abs(Nal)),
             e_orb, k_stable, e_equi, e_tf))
R['P8_torus'] = P8

# ---------------------------------------------------------------- Prop 10
sect('Prop 10 -- h_top(Mbar|Omega) = log 2:  2^n points, (n, eps_0)-separated, eps_0 = min(g, 3^{-1/(d-1)})')
P10 = []
for c, n, tag in CASES:
    al = Alpha(c, n)
    T = Torus(al)
    d = al.d
    g = (al.a - 2) / al.a
    eta = 3.0 ** (-1.0 / (d - 1))
    eps0 = min(g, eta)
    NW = 8
    words = list(itertools.product((0, 1), repeat=NW))
    # for each word: the reduced points Mbar^k Phi(omega^(a)), k = 0..NW-1
    pts = {}
    for a in words:
        seq = []
        for k in range(NW):
            past = list(a[:k][::-1]) + [0] * 60
            fut = list(a[k:]) + [0] * 120
            seq.append(T.Phi(past, fut))
        pts[a] = seq
    worst = np.inf
    for i in range(len(words)):
        for j in range(i + 1, len(words)):
            a, b = words[i], words[j]
            sep = max(T.dist(pts[a][k], pts[b][k]) for k in range(NW))
            worst = min(worst, sep)
    P10.append(dict(name=n, n_word=NW, npoints=len(words), eps0=eps0, g=g, eta=eta,
                    min_max_sep=float(worst), ok=bool(worst >= eps0 - 1e-9)))
    print('%-16s  2^%d points, min over pairs of max_{k<%d} dist = %.6f   >= eps_0 = min(g=%.4f, eta=%.4f) = %.4f   %s'
          % (n, NW, NW, worst, g, eta, eps0, 'OK' if worst >= eps0 - 1e-9 else 'FAIL'))
R['P10_entropy'] = P10

# ---------------------------------------------------------------- Prop 12
sect('Prop 12 -- for alpha > 2 every {0,1}-word is alpha-admissible: d(1,alpha) starts with floor(alpha) >= 2')
P12 = []
for c, n, tag in CASES:
    al = Alpha(c, n)
    a = mp.mpf(al.alpha)
    x = mp.mpf(1); dig = []
    for _ in range(12):
        y = x * a
        dd = int(mp.floor(y))
        dig.append(dd); x = y - dd
    P12.append(dict(name=n, alpha=al.a, d1alpha=dig, first=dig[0], floor=int(math.floor(al.a)),
                    ok=bool(dig[0] >= 2)))
    print('%-16s alpha=%9.6f  d(1,alpha) = %s ...  first digit %d >= 2  %s'
          % (n, al.a, dig[:8], dig[0], 'OK' if dig[0] >= 2 else 'FAIL'))
R['P12_admissible'] = P12

# ---------------------------------------------------------------- Prop 13
sect("Prop 13 -- integer solutions of alpha's recurrence = (Tr(lam a^k)), lam in d^-1 = f'(a)^-1 Z[a]")
P13 = []
for c, n, tag in CASES:
    al = Alpha(c, n)
    F = Field(c)
    d = al.d
    fp = F.fprime()
    fpi = F.inv(fp)
    rng = np.random.default_rng(31)
    # (i) lam = g(a)/f'(a) with g in Z[a]  =>  Tr(lam a^k) in Z for all k
    bad1 = 0
    for _ in range(60):
        gg = [Fr(int(v)) for v in rng.integers(-9, 10, d)]
        lam = F.mul(gg, fpi)
        ok = all(F.trace(matvec(matpow(F.C, k), lam)).denominator == 1 for k in range(3 * d))
        bad1 += (not ok)
    # (ii) conversely: random integer vector h -> lam, and lam*f'(a) must be in Z[a]
    bad2 = 0
    Bmat = [[F.trace(matvec(matpow(F.C, k), [Fr(1) if i == j else Fr(0) for i in range(d)]))
             for j in range(d)] for k in range(d)]
    for _ in range(60):
        h = [Fr(int(v)) for v in rng.integers(-40, 41, d)]
        from m1_field import solve as _solve
        lam = _solve(Bmat, h)
        bad2 += (not F.in_Zalpha(F.mul(lam, fp)))
    # (iii) a lam NOT in the codifferent fails
    notin = 0
    for q in (3, 5, 7):
        lam = [Fr(1, q)] + [Fr(0)] * (d - 1)
        if not F.in_codifferent(lam):
            notin += 1
    # (iv) the ladder itself
    lam_h = [Fr(1, 2)] + [Fr(0)] * (d - 1)
    ladder_half = [F.trace(matvec(matpow(F.C, k), lam_h)) for k in range(9)]
    half_ok = F.in_codifferent(lam_h)
    P13.append(dict(name=n, fprime=[str(x) for x in fp], bad_forward=bad1, bad_backward=bad2,
                    non_codiff_rejected=notin,
                    trace_ladder=[int(x) for x in F.traces(9)],
                    half_ladder=[str(x) for x in ladder_half], half_in_codiff=bool(half_ok)))
    print('%-16s  60/60 forward %s, 60/60 backward %s, 1/q rejected for q in {3,5,7}: %d/3'
          % (n, 'OK' if bad1 == 0 else 'FAIL(%d)' % bad1, 'OK' if bad2 == 0 else 'FAIL(%d)' % bad2, notin))
    print('%-16s  Tr(a^k) = %s ;  lam=1/2 %s codifferent, Tr(a^k/2) = %s'
          % ('', [int(x) for x in F.traces(7)], 'IN' if half_ok else 'NOT in',
             [str(x) for x in ladder_half[:7]]))
R['P13_ladder'] = P13

# ---------------------------------------------------------------- Prop 13b
sect('Prop 13b -- the ladder is per-lambda: |Fhat| along Tr(a^k) vs along Tr(a^k/2)  (Bernoulli 1/2)')
P13b = []
from m0_fourier import Phi_parts
for c, n, tag in CASES:
    al = Alpha(c, n)
    F = Field(c)
    row = dict(name=n, lambdas=[])
    for lam, lname in ((Fr(1), '1'), (Fr(1, 2), '1/2')):
        v = [lam] + [Fr(0)] * (al.d - 1)
        lad = [F.trace(matvec(matpow(F.C, k), v)) for k in range(21)]
        if any(x.denominator != 1 for x in lad):
            print('%-16s lambda=%-4s NOT in the codifferent -- no ladder' % (n, lname))
            row['lambdas'].append(dict(lam=lname, legal=False))
            continue
        lad = [int(x) for x in lad]
        pr = []
        for k in (8, 12, 16, 20):
            p1, p2 = Phi_parts(al, lad[k], 0.5, tol=1e-30)
            pr.append(dict(k=k, h=lad[k], fut=abs(p1), past=abs(p2), plateau=abs(p1 * p2)))
        row['lambdas'].append(dict(lam=lname, legal=True, ladder=lad[:9], probe=pr,
                                   L=pr[-1]['fut'], plateau=pr[-1]['plateau']))
        print('%-16s lambda=%-4s h = %s ...' % (n, lname, lad[1:7]))
        print('%-16s          L = %.10f  plateau = L^2 = %.10e   (|fut|-|past| = %.1e at k=20)'
              % ('', pr[-1]['fut'], pr[-1]['plateau'], abs(pr[-1]['fut'] - pr[-1]['past'])))
    P13b.append(row)
R['P13b_plateau'] = P13b

json.dump(R, open('m1_verify.json', 'w'), indent=1)
print('\n[results written to m1_verify.json]')
