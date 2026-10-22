# E7 — carry statistics of the square of √2 (2026-10-15)

Experiment E7 of `plans/report-sqrtnorm.html` (sources I1 §4.1/§6.2, I2 S69, I3 Rec. 3), the gate for
rank #4. Script: `BB47/e7carry.py` (numpy only, seed 20261015). Reproduce with
`python3 -I e7carry.py 100000 200` (8 s) and `python3 -I e7carry.py 1000000 20` (11 s, 240 MB).

## Objects

For digits `a_0 a_1 …` of `x = ∑ a_i 2^{-i}`, with `E = {i ≤ N : a_i = 1}`:

* `r(n) = #{(i,j) : i + j = n, a_i = a_j = 1}`, the carry-free square (I1's `c_k`, read from the top);
* `T(R) = ∑_{m ≥ 1} r(m + R) 2^{-m}`, the BBP tail, i.e. the carry into position `R` when the square
  is summed. For `√2` it is a positive integer, `T(R) = 2T(R−1) − r(R)`;
* `V(N) = ∑_{n ≤ N} r(n)`, the restricted sumset with multiplicity (`BB47/RestrictedSumset.lean`).

Rank #4 needs `V(N) ≥ (2+c)N` infinitely often. That follows if `T(R) ≥ 3` on a positive proportion
of `R`. The minimal configuration has `T(R) = 2`, which is what `V(N) ≈ 2N` and Dubickas' extremal
sets look like.

## Checks

* The `√2` tails were computed exactly (Python integers, forward recursion). They agree with the
  float backward recursion to `10⁻⁶`, and all are positive up to `N = 10⁶`, so the digits are right.
* Vandehey's parity rule ([Van18, §6]: `T(R)` is odd only if `R = 2i` with `a_i = 1`) holds for every
  `R ≤ 10⁶`.

## Result 1: the minimal tails occur only at the start

`T(R) ≤ 2` for `R ∈ {1, 2, 3, 5, 7, 8, 9, 10, 11, 12, 13}` and **never for `14 ≤ R ≤ 10⁶`**.
`T(10) = 1` (this is `R = 2·5`, `a_5 = 1`). On dyadic blocks `[2^j, 2^{j+1})`:

| j | 4 | 5 | 6 | 8 | 10 | 12 | 14 | 16 | 18 |
|---|---|---|---|---|---|---|---|---|---|
| min `T(R)` | 4 | 11 | 19 | 64 | 235 | 983 | 4095 | 16142 | 65242 |
| min `4T(R)/R` | 0.77 | 1.02 | 0.95 | 0.93 | 0.90 | 0.94 | 0.98 | 0.98 | 0.99 |

So `T(R) ≈ R/4` (the random-model value) from `R = 16` on. In truth `V(N) ≈ N²/8`, not `≈ 2N`. The
proof's input `T(R) ≥ 2` is off by a factor `≈ R/8` at every scale beyond the first 14 positions.

## Result 2: no statistic of √2 is away from random

z-scores against random digits (density ½, `a_0 = 1`): 200 samples at `N = 10⁵`, 20 at `N = 10⁶`.
`|z| ≥ 3` is in bold.

| statistic | random mean (10⁵) | √2 10⁵ | √2 10⁶ | 4−2√2 10⁶ | √3 10⁶ | √5/2 10⁶ | √7/2 10⁶ | Thue–Morse 10⁶ | Dubickas extremal 10⁶ |
|---|---|---|---|---|---|---|---|---|---|
| ones `/√N` | 158.1 | −1.26 | −0.03 | +0.43 | −0.29 | +0.81 | +0.43 | +0.20 | **−965** |
| `V(N)/N²` | 0.125 | −1.12 | −0.27 | +0.12 | −0.26 | +0.87 | +0.37 | −0.07 | **−414** |
| fraction `T ≤ 2` | 4.6e-5 | +1.48 | +0.92 | −0.12 | −0.82 | +0.23 | +0.58 | −0.30 | **+98868** |
| fraction `T ≤ 3` | 8.8e-5 | +0.88 | +0.51 | −0.69 | −1.29 | −0.24 | −0.09 | −0.09 | **+117844** |
| `min T/R`, `R ≥ N/2` | 0.246 | −1.48 | +0.21 | −0.12 | −0.09 | +1.28 | +0.42 | **−171.5** | **−446** |
| mean `4T/R`, `R ≥ N/2` | 1.000 | −1.35 | −0.10 | −0.03 | −0.24 | +1.05 | +0.18 | −0.07 | **−442** |
| sd `(T − R/4)/√R` | 0.259 | −0.79 | −0.50 | −0.50 | −0.33 | +0.09 | +0.47 | **+18.9** | **+440** |
| sd `(r − n/4)/√n` | 0.389 | −0.78 | −0.49 | −0.49 | −0.36 | +0.04 | +0.41 | **+73.8** | **+610** |
| `|(E+E) ∩ [0,N]|/N` | 1.000 | +0.36 | +0.42 | +0.20 | +0.86 | +0.20 | −0.24 | −1.79 | **−104285** |
| `|E+E|/2N` | 1.000 | +1.20 | −0.99 | +0.31 | +0.63 | +0.31 | −1.47 | −2.45 | **−205332** |
| additive energy `/k³` | 0.3333 | −1.53 | +0.30 | −0.12 | −0.26 | +0.99 | −0.29 | +0.27 | **−884** |
| lag-1 digit correlation | 0.000 | +0.08 | −0.80 | −0.80 | +1.04 | +0.18 | −2.04 | **−288** | −0.23 |
| even − odd ones `/√k` | 0.04 | −1.52 | −0.70 | −0.70 | +0.19 | +0.24 | +0.21 | −0.14 | **−7.5** |

The battery has power: Thue–Morse and the extremal set fail it at once. Every quadratic irrational
passes, with all `|z| < 3` at `10⁶` and no drift between `10⁵` and `10⁶`. The `4−2√2` column is the
zeros of `√2` (I1 §3.2).

## Verdict (gate for rank #4): negative

* **No statistic is forced away from random.** Carries, the sumset `|E+E|` (I1 §4.1's
  `(N−1)/(1+log₂N)` bound is attained with room to spare, since `|E+E| ≈ 2N`), the additive energy
  (I2 S18), local densities and parity (Vandehey §8) all match the random model: `√2` is within 1.6σ on every
  statistic at both scales.
* **The sufficient condition of 4.4 is true by a wide margin, but the data give no route to it.**
  `T(R) ≥ 3` holds for every `14 ≤ R ≤ 10⁶`, and in fact `T(R) ≈ R/4`. The configuration it must
  exclude is the sparse regime of Dubickas' extremal set, where `T ≈ 2` on half the positions. That
  regime is absent at every scale, so nothing in the data marks a mechanism (a forbidden pattern, a
  carry invariant) that a proof could use. The gap is between `T ≥ 2` and `T ≈ R/4`. Closing even
  a constant part of it is the same kind of statement as lower-bounding `V(N)` superlinearly. As
  I1 §4.2 warns, the carry recursion is the ×2 orbit again.
* Rank #4 stays "months; uncertain", with no experimental lead. E7 is spent; beyond-Dubickas
  effort on 4.4 is not justified by data.
