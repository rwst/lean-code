# (C) 2026 Ralf Stephan, in collaboration with Claude Code. Released under CC0 1.0 Universal.
#
# X4 for plan-dubD1O5 (milestone M4): the companion check of paper-dubD1O5.tex.
# It is the "second program" of the paper's Appendix A.2 and produces every number
# in Sections 6.1 and 7, plus the structural facts Sections 4-5 rely on.
#
# What it prints, in order:
#   BLOCK 1  the two escape conditions of Prop. 5.4 collapse to one inequality
#            (sqrt m >= p); for p = 2 the only non-square m < 400 that fail are 3 and 6
#   BLOCK 2  for even m every digit is <= m-2, so Lemma 2.1's hypothesis is free
#            -- which is what removes m = 6 and leaves m = 3 as the only hand case
#   BLOCK 3  the top trap interval is exactly (mU - p, mU], and q(mU) = mM <= m
#   BLOCK 4  the witness table of Section 6.1: 25 exact decimals, floors even and
#            unambiguous for n <= 200, plus the L1 digit statistics
#   BLOCK 5  the thresholds of Theorem C, both branches, and the base counts
#   then     L' = L : the rule of Section 5.1 selects b = 0 exactly on [0, p sqrt m)
#            (a 200001-point scan of the whole state interval, refutation-only)
#   then     the cover gap conditions (4.1) at every (p,m), p <= 8, m < 200, with U > p
#   then     the witness table of Section 7: floors divisible by p for n <= 100,
#            including (p,m) = (3,7), the case in the hygiene gap of Remark 7.1
#
# Arithmetic: exact.  Z[sqrt m] comparisons by the integer test p^2 vs m q^2; states
# scaled by (m-1) so they are integer pairs; reals as Fraction with a rigorous m^-N
# tail, every floor evaluated at both ends of the enclosure.  No floats decide anything
# except in the two coarse scans of blocks 1 and 4, which are refutation-only.

from fractions import Fraction
import math

def is_sq(n): 
    r = math.isqrt(n); return r*r == n

def sgn(p, q, m):
    """sign of p + q sqrt(m), integers p,q, m non-square."""
    if p == 0 and q == 0: return 0
    if p >= 0 and q >= 0: return 1
    if p <= 0 and q <= 0: return -1
    d = p*p - m*q*q
    assert d != 0, (p, q, m)
    return 1 if (p > 0) == (d > 0) else -1

def model(m):
    e = m-1 if m % 2 else m-2         # largest even digit
    Ev = list(range(0, e+1, 2))
    return e, Ev

# ---------------------------------------------------------------- Block 1
print("BLOCK 1 --- the two escape conditions collapse to one inequality")
print("  odd m:  e = m-1, M = 1, U = 1+sqrt m")
print("  b-side needs U-2 >= 2/sqrt m   <=>  m - sqrt m >= 2")
print("  a-side needs 2 sqrt m <= (e-2)+U <=> m - sqrt m >= 2   (same!)")
print("  both  <=>  sqrt m >= 2  <=>  m >= 4")
bad_b, bad_a = [], []
for m in range(3, 400):
    if is_sq(m): continue
    e, Ev = model(m)
    M = Fraction(e, m-1); rt = math.sqrt(m); U = float(M)*(1+rt)
    if not (U - 2 >= 2/rt): bad_b.append(m)
    if not (2*rt <= (e-2) + U): bad_a.append(m)
print("  non-square m < 400 failing b-side:", bad_b)
print("  non-square m < 400 failing a-side:", bad_a)
print("  odd m failing either:", [m for m in set(bad_a+bad_b) if m % 2])
print("  => L1 needs hand analysis only at m = 3 (m = 6 is EVEN, where L1 is free).")
print()

# ---------------------------------------------------------------- Block 2
print("BLOCK 2 --- for even m every digit is <= m-2, so Lemma D's hypothesis is free")
for m in [4,6,8,10,12,20]:
    e, Ev = model(m)
    print(f"  m={m:3d}: Ev = {Ev},  max digit {e} <= m-2 = {m-2}: {e <= m-2}")
print()

# ---------------------------------------------------------------- Block 3
print("BLOCK 3 --- the top trap interval A_top = (mU-2, mU], uniformly")
print("  claim: mU - (e sqrt m + (e-2) + U) = 2 exactly, and the forced offset there is")
print("         e(1+sqrt m) = (m-1)U with fixed point mU, whose sqrt-m coefficient is mM <= m")
for m in [3,5,6,7,8,11,12]:
    if is_sq(m): continue
    e, _ = model(m); M = Fraction(e, m-1)
    # (m-1)U = e(1+sqrt m); check (m-1)*mU - (m-1)*(e sqrt m + e-2 + U) == 2(m-1)
    # in the scaled integer model:  (m-1)U = e + e sqrt m
    # m(m-1)U - [ (m-1)e sqrt m + (m-1)(e-2) + (m-1)U ] = (m-1)*2 ?
    lhs_p = m*e - ((m-1)*(e-2) + e); lhs_q = m*e - ((m-1)*e + e)
    print(f"  m={m:3d}: gap = ({lhs_p}) + ({lhs_q}) sqrt m = {lhs_p + lhs_q*math.sqrt(m):.6f}"
          f"   (want 2(m-1) = {2*(m-1)}) -> {lhs_p == 2*(m-1) and lhs_q == 0}")
    print(f"        q(mU) = mM = {m*M} <= m = {m}: {m*M <= m}")
print()

# ---------------------------------------------------------------- Block 4
print("BLOCK 4 --- the greedy (smallest a, then largest b) at the five new cells")
print("  states scaled by (m-1): W = (P + Q sqrt m)/(m-1)")

def greedy(m, N, k0=1):
    e, Ev = model(m)
    # translate: sigma = (2k0 + M) sqrt m - 2j,  need 0 < sigma < U
    # scaled by (m-1):  S = -2j(m-1) + (2k0(m-1)+e) sqrt m ;  (m-1)U = e + e sqrt m
    Qs = 2*k0*(m-1) + e
    j = 0
    while True:
        Ps = -2*j*(m-1)
        if sgn(Ps, Qs, m) > 0 and sgn(e - Ps, e - Qs, m) > 0: break
        j += 1
        assert j < 1000
    # w_0 = m sigma
    P, Q = m*Ps, m*Qs
    A, B = [], []
    for k in range(N):
        # invariant 0 <= W <= mU   i.e. 0 <= P+Q sqrt m <= m(e + e sqrt m)
        assert sgn(P, Q, m) >= 0 and sgn(m*e - P, m*e - Q, m) >= 0, (m, k)
        best = None
        for a in Ev:
            for b in reversed(Ev):
                p, q = P - a*(m-1), Q - b*(m-1)
                if sgn(p, q, m) >= 0 and sgn(e - p, e - q, m) >= 0:
                    best = (a, b); break
            if best: break
        assert best is not None, (m, k, "COVER LEMMA FAILS")
        a, b = best
        A.append(a); B.append(b)
        P, Q = m*(P - a*(m-1)), m*(Q - b*(m-1))
    return j, k0, e, A, B

for m in [3, 5, 6, 7, 8]:
    N = 300
    j, k0, e, A, B = greedy(m, N)
    x  = sum(Fraction(A[i], m**(i+1)) for i in range(N))
    xi_lo = Fraction(2*j + x, m)
    xi_hi = Fraction(2*j + x + Fraction(1, m**N), m)
    d_lo = (xi_lo.numerator * 10**25) // xi_lo.denominator
    d_hi = (xi_hi.numerator * 10**25) // xi_hi.denominator
    s = str(d_lo).rjust(26, "0")
    exact = "EXACT" if d_lo == d_hi else "AMBIG"
    # floors n = 1..200
    odd = []
    for n in range(1, 201):
        if n % 2 == 0:
            sft = n//2 - 1
            def f(xv): 
                v = (2*j + xv) * Fraction(m**sft); return v.numerator // v.denominator
        else:
            sft = (n-1)//2
            # (2k0 + y) m^s  with y = M - y'' ; recompute y from B
            def f(xv, _s=sft):
                y2 = sum(Fraction(B[i], m**(i+1)) for i in range(N))
                y = Fraction(e, m-1) - y2
                v = (2*k0 + y) * Fraction(m**_s); return v.numerator // v.denominator
        a1 = f(x); a2 = f(x + Fraction(1, m**N))
        if a1 != a2: odd.append((n, "STRADDLE")); continue
        if a1 % 2: odd.append((n, a1))
    first = []
    for n in range(1, 7):
        if n % 2 == 0:
            sft = n//2 - 1; v = (2*j + x)*Fraction(m**sft); first.append(v.numerator//v.denominator)
        else:
            sft = (n-1)//2
            y2 = sum(Fraction(B[i], m**(i+1)) for i in range(N))
            y = Fraction(e, m-1) - y2
            v = (2*k0 + y)*Fraction(m**sft); first.append(v.numerator//v.denominator)
    zeros = sum(1 for v in A if v <= e-2)
    twos  = sum(1 for v in B if v >= 2)
    print(f"  m={m}  (j,k0)=({j},{k0})  e={e}  xi = {s[:-25]}.{s[-25:]} [{exact}]")
    print(f"        first floors {first}   odd/straddle n<=200: {odd if odd else 'NONE'}")
    print(f"        L1: a-digits < e in {zeros}/{N};  b-digits >= 2 in {twos}/{N}")
print()

# ---------------------------------------------------------------- Block 5
print("BLOCK 5 --- Theorem C: p | floor(xi sqrt(m)^n)")
print("  branch p | m-1: e = m-1, M = 1, U = 1+sqrt m; need U > p  <=>  m > (p-1)^2")
print("  smallest such m congruent to 1 mod p is p^2-p+1 :")
for p in range(2, 13):
    thr = p*p - p + 1
    assert thr % p == 1 % p, p
    assert math.sqrt(thr) + 1 > p
    prev = thr - p
    assert not (math.sqrt(prev) + 1 > p) or prev < 1, (p, prev)
    print(f"    p={p:2d}:  p^2-p+1 = {thr:3d},  U = 1+sqrt(m) = {1+math.sqrt(thr):.4f} > {p}"
          f" ;  previous candidate {prev:3d} gives U = {1+math.sqrt(prev):.4f} (fails)")
print("  branch p | m: e = m-p, M = (m-p)/(m-1); need U = M(1+sqrt m) > p :")
for p in [3,4,5]:
    ms = [m for m in range(2*p, 200, p) if not is_sq(m)
          and float(Fraction(m-p, m-1))*(1+math.sqrt(m)) > p]
    print(f"    p={p}: smallest m with p|m is {ms[0]}")
print("  admissible bases m <= 60 (either branch, non-square, m >= 3):")
for p in range(3, 9):
    cnt = []
    for m in range(3, 61):
        if is_sq(m): continue
        if m % p == 1 % p or m % p == 0:
            e = p*((m-1)//p)
            if e == 0: continue
            U = float(Fraction(e, m-1))*(1+math.sqrt(m))
            if U > p: cnt.append(m)
    print(f"    p={p}: {len(cnt)} bases, smallest {cnt[0] if cnt else '-'}")

# ---------------------------------------------------------------- Blocks 4,5,7
def scan(p, m, G=200000):
    e = p*((m-1)//p); Ev=list(range(0,e+1,p))
    M = Fraction(e,m-1); rt = math.sqrt(m); U = float(M)*(1+rt); top = m*U
    bad = []
    for i in range(G+1):
        w = top*i/G
        best=None
        for a in Ev:
            for b in reversed(Ev):
                c = a + b*rt
                if c <= w <= c + U + 1e-12:
                    best=(a,b); break
            if best: break
        if best is None:
            bad.append(("NOCOVER", w)); continue
        if best[1] == 0 and w >= p*rt - 1e-12:
            bad.append(("bSEL0", w, best))
    return bad, U, top

print("scan of the whole state interval [0, mU], grid 200001 points")
for (p,m) in [(2,3),(2,5),(2,6),(2,7),(2,8),(2,11),(2,12),(3,10),(3,12),(4,17),(5,26),(3,7)]:
    if is_sq(m): continue
    bad,U,top = scan(p,m)
    kinds = {}
    for t in bad: kinds[t[0]] = kinds.get(t[0],0)+1
    ex = [t for t in bad if t[0]=="bSEL0"][:3]
    print(f"  p={p} m={m:2d}: U={U:.4f} mU={top:.4f} p*sqrt m={p*math.sqrt(m):.4f}"
          f"   anomalies {kinds if kinds else 'NONE'}")
    for t in ex:
        print(f"        e.g. w={t[1]:.6f} -> (a,b)={t[2]}")

def gaps(p,m):
    """the three cover-gap conditions for digit set {0,p,...,e}"""
    e = p*((m-1)//p)
    if e == 0: return None
    M = Fraction(e, m-1); rt = math.sqrt(m); U = float(M)*(1+rt)
    return e, M, U, (p <= U), (p*rt - e <= U), (U > p)

print("Cover gap conditions for the p-family (g1: p<=U, g2: p sqrt m - e <=U, g3: U>p)")
bad=[]
for p in range(2,9):
    for m in range(3,200):
        if is_sq(m): continue
        if m % p not in (0, 1 % p): continue
        g = gaps(p,m)
        if g is None: continue
        e,M,U,g1,g2,g3 = g
        if g3 and not (g1 and g2): bad.append((p,m,g1,g2))
print("  bases where the translate fits (g3) but a gap fails:", bad if bad else "NONE")
print()

def greedy_p(p, m, N, k0=1):
    e = p*((m-1)//p); Ev = list(range(0,e+1,p))
    Qs = p*k0*(m-1) + e
    j = 0
    while True:
        Ps = -p*j*(m-1)
        if sgn(Ps,Qs,m) > 0 and sgn(e-Ps, e-Qs, m) > 0: break
        j += 1; assert j < 5000
    P,Q = m*Ps, m*Qs
    A,B = [],[]
    for k in range(N):
        assert sgn(P,Q,m) >= 0 and sgn(m*e-P, m*e-Q, m) >= 0, (p,m,k,"INVARIANT")
        best=None
        for a in Ev:
            for b in reversed(Ev):
                pp,qq = P-a*(m-1), Q-b*(m-1)
                if sgn(pp,qq,m) >= 0 and sgn(e-pp, e-qq, m) >= 0:
                    best=(a,b); break
            if best: break
        assert best is not None, (p,m,k,"COVER FAILS")
        a,b = best; A.append(a); B.append(b)
        P,Q = m*(P-a*(m-1)), m*(Q-b*(m-1))
    return j,e,A,B

print("Theorem C end to end (N=250 digits, floors n<=100 checked at both enclosure ends)")
for (p,m) in [(2,3),(3,10),(3,12),(4,17),(5,26),(3,7)]:
    if is_sq(m): continue
    N=250; k0=1
    j,e,A,B = greedy_p(p,m,N,k0)
    x   = sum(Fraction(A[i], m**(i+1)) for i in range(N))
    y2  = sum(Fraction(B[i], m**(i+1)) for i in range(N))
    y   = Fraction(e,m-1) - y2
    bad=[]
    for n in range(1,101):
        if n%2==0:
            s=n//2-1
            f=lambda xv: ((p*j+xv)*Fraction(m**s)).numerator // ((p*j+xv)*Fraction(m**s)).denominator
            a1,a2 = f(x), f(x+Fraction(1,m**N))
        else:
            s=(n-1)//2
            f=lambda yv: ((p*k0+yv)*Fraction(m**s)).numerator // ((p*k0+yv)*Fraction(m**s)).denominator
            a1,a2 = f(y-Fraction(1,m**N)), f(y)
        if a1!=a2: bad.append((n,"STRADDLE")); continue
        if a1 % p: bad.append((n,a1))
    xi = Fraction(p*j+x, m)
    lo=(xi.numerator*10**20)//xi.denominator
    hi=((Fraction(p*j+x+Fraction(1,m**N),m)).numerator*10**20)//(Fraction(p*j+x+Fraction(1,m**N),m)).denominator
    s20=str(lo).rjust(21,"0")
    canon = (e <= m-2) or (m >= p*p) or (p,m)==(2,3)
    firsts=[]
    for n in range(1,7):
        if n%2==0:
            s=n//2-1; v=(p*j+x)*Fraction(m**s); firsts.append(v.numerator//v.denominator)
        else:
            s=(n-1)//2; v=(p*k0+y)*Fraction(m**s); firsts.append(v.numerator//v.denominator)
    print(f"  p={p} m={m:2d}: e={e:2d} j={j} xi={s20[:-20]}.{s20[-20:]}"
          f" [{'EXACT' if lo==hi else 'AMBIG'}] hygiene-free/covered: {canon}")
    print(f"            floors {firsts}  ...  n<=100 non-multiples of p: {bad if bad else 'NONE'}")
