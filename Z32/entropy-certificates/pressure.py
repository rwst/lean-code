#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
#
# pressure.py -- plan-B10 WP4' (angle B5 of report2-weyl.html): the pressure /
# Bowen-zero layer on top of the entropy certificates of `Z32/entcert.py`.
#
# WHAT IS COMPUTED, AND WHY IT NEEDS NO LOGARITHMS
#
# The branches of the model system are affine with slope 3/2, so the geometric
# potential -t log|T'| is CONSTANT and the pressure is affine in t:
#
#     P(t) = phi_model(U) - t log(3/2),
#
# whence the Bowen zero -- the unique t with P(t) = 0 -- is
#
#     t*(U) = phi_model(U) / log(3/2) = log(lambda) / log(3/2),
#
# lambda the growth rate of the carry language, which `entcert.py` brackets
# exactly.  The same quotient against log 2 instead of log(3/2) is Flatto's
# dyadic counting exponent s0(U) (= log_2(3/2) = 0.585... at the Z-cell).
#
# A bound on such a quotient is a PURE RATIONAL POWER COMPARISON:
#
#     n/d <= log(x)/log(r)   <==>   r^n <= x^d        (x, r > 1)
#
# so the kernel never sees a logarithm, a real number or a floating-point
# value -- only two integers to compare.  This script picks, for each shipped
# certificate, the exponent pair (n, d) that gives the tightest bracket subject
# to a digit budget, and verifies it in exact integer arithmetic.
#
# The digit budget matters: plan-B10's gate (j) asks the t-weighted layer to
# stay inside WP3's measured envelope.  Cost here is linear in d * log10(num),
# so the script reports the size of the largest integer the kernel will have to
# form, and `--budget` sweeps the trade-off.
#
#   ./pressure.py                 # the shipped grid, both bases
#   ./pressure.py <num> <den>     # one window
#   ./pressure.py --budget        # the width/size trade-off table
#   ./pressure.py --lean          # emit the Lean bracket theorems

import sys
from decimal import Decimal, getcontext
from fractions import Fraction as F

sys.path.insert(0, __file__.rsplit("/", 1)[0])
import entcert

getcontext().prec = 120

# the seven windows shipped as Lean terms in Z32/EntropyCert.lean, with the
# certificate name each one carries there
SHIPPED = [((2, 5), "cert25"), ((13, 32), "cert1332"), ((5, 12), "certBand"),
           ((7, 16), "cert716"), ((9, 20), "cert920"), ((11, 24), "cert1124"),
           ((23, 48), "cert2348")]

BASES = {"three_halves": F(3, 2), "two": F(2, 1)}


def dlog(x: F) -> Decimal:
    return (Decimal(x.numerator) / Decimal(x.denominator)).ln()


def approximants(tgt: Decimal, D: int):
    """Every best rational approximation to `tgt` with denominator <= D.

    These are the convergents and semiconvergents of the continued fraction, so
    the search below is logarithmic in `D` rather than linear -- which is what
    makes an eight-decimal bracket affordable to look for."""
    out, x = [], tgt
    hm1, km1, h, k = 1, 0, int(x.to_integral_value(rounding="ROUND_FLOOR")), 1
    out.append((h, k))
    for _ in range(80):
        frac = x - int(x.to_integral_value(rounding="ROUND_FLOOR"))
        if frac == 0:
            break
        x = 1 / frac
        a = int(x.to_integral_value(rounding="ROUND_FLOOR"))
        for j in range(1, a + 1):
            hj, kj = hm1 + j * h, km1 + j * k
            if kj > D:
                return out
            out.append((hj, kj))
        hm1, km1, h, k = h, k, hm1 + a * h, km1 + a * k
    return out


def below(x: F, r: F, D: int):
    """Largest n/d with d <= D, r^n <= x^d  (i.e. n/d <= log x / log r)."""
    tgt = dlog(x) / dlog(r)
    cands = sorted({(F(n, d), n, d) for (n, d) in approximants(tgt, D)
                    if n >= 0 and F(n, d) <= F(*Fdec(tgt))}, reverse=True)
    for f, n, d in cands:
        if pow_le(r, n, x, d):
            return (f, n, d)
    return None


def above(x: F, r: F, D: int):
    """Smallest n/d with d <= D, x^d <= r^n."""
    tgt = dlog(x) / dlog(r)
    cands = sorted({(F(n, d), n, d) for (n, d) in approximants(tgt, D)
                    if n >= 0 and F(n, d) >= F(*Fdec(tgt))})
    for f, n, d in cands:
        if pow_le(x, d, r, n):
            return (f, n, d)
    return None


def Fdec(x: Decimal):
    """`x` as an exact numerator/denominator pair (it is a finite decimal)."""
    f = F(x)
    return (f.numerator, f.denominator)


def pow_le(u: F, i: int, v: F, j: int) -> bool:
    """Exact test u^i <= v^j, cross-multiplied so only integers appear."""
    return u.numerator ** i * v.denominator ** j <= v.numerator ** j * u.denominator ** i


def digits(u: F, i: int, v: F, j: int) -> int:
    a = u.numerator ** i * v.denominator ** j
    b = v.numerator ** j * u.denominator ** i
    return int(max(a.bit_length(), b.bit_length()) * 0.30103) + 1


def simplify(x: F, Q: int, up: bool) -> F:
    """Best rational with denominator <= Q on the given side of x.

    Shrinking the certificate's 8-digit ratio to a 3-4 digit one before raising
    it to the d-th power is what keeps the kernel integers small; the precision
    lost is ~1/Q^2, far below the width the exponent pair can deliver anyway."""
    best = None
    for q in range(1, Q + 1):
        p = (x.numerator * q + (x.denominator - 1 if up else 0)) // x.denominator
        f = F(p, q)
        if (f >= x) if up else (f <= x):
            if best is None or ((f < best) if up else (f > best)):
                best = f
    return best


def bracket(lam_lo: F, lam_hi: F, r: F, D: int, Q: int):
    u = simplify(lam_lo, Q, up=False)
    v = simplify(lam_hi, Q, up=True)
    lo = below(u, r, D)
    hi = above(v, r, D)
    dig = max(digits(r, lo[1], u, lo[2]), digits(v, hi[2], r, hi[1]))
    return {"u": u, "v": v, "lo": lo, "hi": hi, "width": float(hi[0] - lo[0]),
            "digits": dig}


def row(name, ell, c, r, D, Q):
    b = bracket(c["lam_lo"], c["lam_up"], r, D, Q)
    print(f"  {name:9s} ell={str(ell):8s} "
          f"t in [{b['lo'][1]}/{b['lo'][2]}, {b['hi'][1]}/{b['hi'][2]}] "
          f"= [{float(b['lo'][0]):.7f}, {float(b['hi'][0]):.7f}] "
          f"w={b['width']:.2e} lam in [{b['u']}, {b['v']}] dig={b['digits']}")
    return b


def main_grid(D=10 ** 4, Q=10 ** 5):
    for bname, r in BASES.items():
        print(f"\n## base {r}  ({'Bowen zero' if r == F(3,2) else 'Flatto exponent'})"
              f"   D<={D}, Q<={Q}")
        for (n, d), cname in SHIPPED:
            c = entcert.build(n, d)
            row(cname, F(n, d), c, r, D, Q)


def main_budget():
    c = entcert.build(5, 12)
    print("window 5/12, base 3/2 -- width vs the largest kernel integer")
    print("   D     Q      bracket                width      digits")
    # The last row is past the point of usefulness: the certificate's own bracket
    # on lambda is 1.79e-08 wide, so no exponent pair can do better than that.
    for D, Q in [(40, 300), (200, 2000), (1600, 20000), (10 ** 4, 10 ** 5),
                 (10 ** 5, 10 ** 6)]:
        b = bracket(c["lam_lo"], c["lam_up"], F(3, 2), D, Q)
        print(f"  {D:5d} {Q:6d}  [{b['lo'][1]}/{b['lo'][2]}, "
              f"{b['hi'][1]}/{b['hi'][2]}]  {b['width']:.3e}  {b['digits']:6d}")


def main_lean(D=10 ** 4, Q=10 ** 5):
    for bname, r in BASES.items():
        print(f"-- base {r}")
        for (n, d), cname in SHIPPED:
            c = entcert.build(n, d)
            b = bracket(c["lam_lo"], c["lam_up"], r, D, Q)
            print(f"{cname} {bname} lo={b['lo'][1]}/{b['lo'][2]} "
                  f"hi={b['hi'][1]}/{b['hi'][2]} u={b['u']} v={b['v']} "
                  f"dig={b['digits']}")


if __name__ == "__main__":
    if "--budget" in sys.argv:
        main_budget()
    elif "--lean" in sys.argv:
        main_lean()
    elif len(sys.argv) >= 3:
        n, d = int(sys.argv[1]), int(sys.argv[2])
        c = entcert.build(n, d)
        for bname, r in BASES.items():
            row(bname, F(n, d), c, r, 400, 3000)
    else:
        main_grid()
