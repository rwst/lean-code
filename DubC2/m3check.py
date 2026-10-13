#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
"""
Independent cross-check of the DubC2 Lean model (milestone M3).

Iterates x_n = [xi*(p/q)^n + nu] straight from the definition in exact Fractions --
nothing here goes through the Lean files -- and checks, at every avoiding consecutive
pair, every claim DubC2/NearestStep.lean and DubC2/Calibration53.lean make:

  * the carry identity   s_n = p*y_n - q*y_{n+1} - (p-q)*nu     (Z32.carry_eq)
  * the alphabet         3/2: s in {-1,+1};  5/3: s in {-2,+2}
  * letter <-> window    3/2: s = -1 iff y < 1/2
                         5/3: s = -2 iff y < 2/5, and y never lies in [2/5, 3/5)

and prints the longest avoiding run found, with its carry word and residues, so the
forced periodic word can be read off by eye.  Expected: 0 violations at both bases.

    python3 m3check.py
"""
from fractions import Fraction as F
import random

def orbit(p,q,nu,xi,n):
    """exact x_k, y_k, s_k for k<n"""
    X=[];Y=[]
    z=F(xi)
    for k in range(n+1):
        v=z+F(nu)
        x=v.numerator//v.denominator
        X.append(x); Y.append(v-x)
        z=z*F(p,q)
    S=[q*X[k+1]-p*X[k] for k in range(n)]
    return X,Y,S

def check(p,q,nu,P,label,trials=4000,n=60):
    """verify the Lean model's claims on avoidance runs"""
    random.seed(7)
    best=0; bestinfo=None
    viol=[]
    for _ in range(trials):
        num=random.randint(1,10**6); den=random.randint(1,10**6)
        xi=F(num,den)
        X,Y,S=orbit(p,q,nu,xi,n)
        # longest run of indices avoiding all of P
        run=0; start=0
        for k in range(n):
            if all(X[k]%m!=0 for m in P):
                if run==0: start=k
                run+=1
                if run>best: best=run; bestinfo=(xi,start,run,X[start:start+run],[S[j] for j in range(start,start+run-1)],[Y[j] for j in range(start,start+run)])
            else:
                run=0
        # model checks on every avoiding consecutive pair
        for k in range(n-1):
            if all(X[k]%m!=0 for m in P) and all(X[k+1]%m!=0 for m in P):
                s=S[k]
                # carry identity
                assert F(s)==p*Y[k]-q*Y[k+1]-(p-q)*F(nu), "carry identity"
                if (p,q)==(3,2):
                    if s not in (-1,1): viol.append(("alphabet",xi,k,s))
                    if (Y[k]<F(1,2)) != (s==-1): viol.append(("letter",xi,k,s,Y[k]))
                if (p,q)==(5,3):
                    if s not in (-2,2): viol.append(("alphabet",xi,k,s))
                    if F(2,5)<=Y[k]<F(3,5): viol.append(("gap",xi,k,Y[k]))
                    if (Y[k]<F(2,5)) != (s==-2): viol.append(("letter",xi,k,s,Y[k]))
    print(f"{label}: longest avoiding run over {trials} random xi = {best}")
    if bestinfo:
        xi,start,run,xs,ss,ys=bestinfo
        print(f"   xi={xi} start={start} carries={ss}")
        print(f"   x mod {P} = {[ [x%m for m in P] for x in xs]}")
    print(f"   model violations: {len(viol)}", viol[:3])

check(3,2,F(1,2),[2,5],"3/2 nu=1/2  P={2,5}")
check(5,3,F(1,2),[2,3],"5/3 nu=1/2  P={2,3}")

# the two claimed periodic y-orbits
def itin(p,q,nu,y0,n):
    y=F(y0); w=[]
    for _ in range(n):
        if (p,q)==(3,2):
            if y<F(1,2): w.append('A'); y=(6*y+1)/4
            else: w.append('B'); y=(6*y-3)/4
        else:
            if y<F(2,5): w.append('A'); y=(5*y+1)/3
            elif y>=F(3,5): w.append('B'); y=(5*y-3)/3
            else: w.append('?'); break
    return ''.join(w), y
print()
print("3/2 fixed point 3/26 :", itin(3,2,F(1,2),F(3,26),12), " in [5/54,1/6)?", F(5,54)<=F(3,26)<F(1,6))
print("5/3 y=1/4          :", itin(5,3,F(1,2),F(1,4),12), " in [1/9,2/5)?", F(1,9)<=F(1,4)<F(2,5))
print("5/3 y=1/34         :", itin(5,3,F(1,2),F(1,34),12), " < 1/9?", F(1,34)<F(1,9))
