import sys, math
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from gencert import LeanModel
from fractions import Fraction

def dfa(m, limit=200000):
    S0 = (1 << m.nV) - 1
    idx = {S0: 0}; sets = [S0]; trans = []
    i = 0
    while i < len(sets):
        S = sets[i]; row = []
        for t in range(m.nA):
            T = m.detSucc(S, m.letter(t))
            if T == 0:
                row.append(None); continue
            if T not in idx:
                idx[T] = len(sets); sets.append(T)
                if len(sets) > limit: return None
            row.append(idx[T])
        trans.append(row); i += 1
    return sets, trans

def lam(trans, it=3000):
    n = len(trans); v = [1.0]*n; r = 1.0
    for _ in range(it):
        w = [sum(v[j] for j in row if j is not None) for row in trans]
        r = max(w[i]/v[i] for i in range(n))
        s = max(w); v = [x/s + 1e-300 for x in w]
    # Collatz-Wielandt upper bound
    w = [sum(v[j] for j in row if j is not None) for row in trans]
    return max(w[i]/v[i] for i in range(n) if v[i] > 0)

def vcert(trans, a, b, maxit=100000):
    n = len(trans); v = [1]*n
    for _ in range(maxit):
        ch = False
        for i, row in enumerate(trans):
            s = sum(v[j] for j in row if j is not None)
            need = -(-b*s // a)
            if need > v[i]: v[i] = need; ch = True
        if not ch: return v
        if max(v) > 10**12: return None
    return None

if __name__ == '__main__':
    p, q, a, b = map(int, sys.argv[1:5]); P = list(map(int, sys.argv[5].split(','))); D = int(sys.argv[6])
    m = LeanModel(p, q, a, b, P, D)
    r = dfa(m)
    if r is None: print("too big"); sys.exit()
    sets, trans = r
    print("nV", m.nV, "nA", m.nA, "M", m.M, "PM", m.PM, "Pq", m.Pq, "dfa states", len(sets), "lam", lam(trans))

def lam_np(trans):
    import numpy as np
    n = len(trans); A = np.zeros((n, n))
    for i, row in enumerate(trans):
        for j in row:
            if j is not None: A[i, j] += 1
    return max(abs(np.linalg.eigvals(A)))
