#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code
# CC0 1.0 Universal (public domain dedication).
"""M0 sec 7 -- the structured digit-word catalogue.

iid, periodic, Thue-Morse, period-doubling, Rudin-Shapiro, Sturmian, binary Champernowne,
Markov, and one substitution word.
"""
import numpy as np

def w_iid(N, p=0.5, seed=0):
    return (np.random.default_rng(seed).random(N) < p).astype(np.int8)

def w_periodic(N, pat):
    pat = np.array([int(c) for c in pat], dtype=np.int8)
    return np.tile(pat, N // len(pat) + 1)[:N]

def w_thue_morse(N):
    n = np.arange(N, dtype=np.int64)
    return (np.array([bin(int(k)).count('1') for k in n]) % 2).astype(np.int8)

def w_period_doubling(N):
    # fixed point of 0->01, 1->00
    s = [0]
    while len(s) < N:
        s = [x for c in s for x in ((0, 1) if c == 0 else (0, 0))]
    return np.array(s[:N], dtype=np.int8)

def w_rudin_shapiro(N):
    out = np.empty(N, dtype=np.int8)
    for n in range(N):
        b = bin(n)[2:]
        out[n] = sum(1 for i in range(len(b) - 1) if b[i] == b[i+1] == '1') % 2
    return out

def w_sturmian(N, slope, rho=0.0):
    n = np.arange(1, N + 1)
    return (np.floor(n * slope + rho) - np.floor((n - 1) * slope + rho)).astype(np.int8)

def w_champernowne(N):
    out = []
    k = 1
    while len(out) < N:
        out += [int(c) for c in bin(k)[2:]]
        k += 1
    return np.array(out[:N], dtype=np.int8)

def w_markov(N, p01, p10, seed=0):
    rng = np.random.default_rng(seed)
    u = rng.random(N)
    out = np.empty(N, dtype=np.int8)
    s = 0
    for i in range(N):
        out[i] = s
        s = (1 if u[i] < p01 else 0) if s == 0 else (0 if u[i] < p10 else 1)
    return out

def w_substitution(N, rules, start=0):
    s = [start]
    while len(s) < N:
        s = [x for c in s for x in rules[c]]
        if len(s) > 40 * N: break
    return np.array(s[:N], dtype=np.int8)

CATALOG = {
    'iid p=1/2':        lambda N: w_iid(N, 0.5, 11),
    'iid p=0.3':        lambda N: w_iid(N, 0.3, 12),
    'iid p=0.1':        lambda N: w_iid(N, 0.1, 13),
    'periodic 01':      lambda N: w_periodic(N, '01'),
    'periodic 0011101': lambda N: w_periodic(N, '0011101'),
    'Thue-Morse':       w_thue_morse,
    'period-doubling':  w_period_doubling,
    'Rudin-Shapiro':    w_rudin_shapiro,
    'Sturmian 1/phi^2': lambda N: w_sturmian(N, (3 - 5 ** .5) / 2),
    'Sturmian sqrt2-1': lambda N: w_sturmian(N, 2 ** .5 - 1),
    'Champernowne':     w_champernowne,
    'Markov sticky .05':lambda N: w_markov(N, .05, .05, 5),
    'Markov altern .95':lambda N: w_markov(N, .95, .95, 6),
    'subst 0->011,1->0':lambda N: w_substitution(N, {0: (0, 1, 1), 1: (0,)}),
}
