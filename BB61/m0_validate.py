#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M0 sec 3.1 -- Monte Carlo check of the closed form.

At N = 2e6 the simulated Weyl sums agree with the sec 3 product to the noise floor 7e-4,
at quadratic, cubic-unit and cubic-non-unit alpha.
"""
from m0_engine import *
from m0_fourier import Phi_parts
import numpy as np

def weyl(x, hs):
    return {h: abs(np.mean(np.exp(2j*np.pi*h*x))) for h in hs}

for coeffs, name, hs in [([1,-2,-1],'1+sqrt2',[1,2,3,7,17,41,99,239,577,1393]),
                         ([1,-4,1],'2+sqrt3',[1,3,15,56,209,780,2911]),
                         ([1,-3,2,-1],'X^3-3X^2+2X-1 (cubic, complex conj)',[1,2,3,12,114]),
                         ([1,-1,-2,-2],'X^3-X^2-2X-2 (cubic non-unit)',[1,2,3,7])]:
    al = Alpha(coeffs, name)
    rng = np.random.default_rng(7)
    L = 400
    N = 2*10**6
    eps = rng.integers(0,2,N+L)
    x = orbit(al, eps, L=L)
    W = weyl(x, hs)
    print('=== %-38s alpha=%.6f  N=%d  noise floor ~%.5f' % (name, al.a, len(x), 1/np.sqrt(len(x))))
    print('   %8s %12s %12s' % ('h','MC |Weyl|','closed form'))
    for h in hs:
        P1,P2 = Phi_parts(al,h)
        print('   %8d %12.6f %12.6f' % (h, W[h], P1*P2))
