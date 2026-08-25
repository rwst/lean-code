/* (C) Ralf Stephan, in collaboration with Claude Code.  CC0 / public domain.
 *
 * X2' (plan-dubC1 §0-ter N1 / §8) — the certificate ladder for the
 * coprimality subshift of [xi 7^n].
 *
 * Model.  x_{n+1} = 7 x_n + d_{n+1}, d in {0,...,6}.  For P = {p <= y} put
 * M = prod P.  States: r in (Z/M)^*, transitions r --d--> 7r+d, admissible
 * iff gcd(7r+d, M) = 1.
 *
 * Reduction (verified against the literal model by subshift.py for y<=17):
 * coprimality to 2 forces d even, coprimality to 7 forces d != 0, so the
 * alphabet is {2,4,6}; then r mod 2 == 1 always and r mod 7 == d never
 * constrains anything.  So the state space is the product
 *       S = prod_{p in Q} (Z/p)^*,     Q = {p <= y} \ {2,7},
 * of size prod_{p in Q}(p-1) = phi(M)/6, with r_p --d--> (7 r_p + d) mod p,
 * admissible iff no coordinate hits 0.  Forward AND backward maps act
 * coordinatewise (7 is invertible mod every p in Q), so both are products.
 *
 * Implementation.  Mixed-radix index split in two halves,
 *      idx = i1 * N2 + i2,
 * with per-half transition tables fwdHi/fwdLo (and bwdHi/bwdLo) for each
 * digit; a successor is one table lookup per half.  Then:
 *   1. core pruning: alternately delete states with no live successor and
 *      states with no live predecessor, to a fixpoint (bitset, in place;
 *      monotone, so OpenMP-safe with atomic clears).
 *   2. compact the core, run iterative Tarjan.
 *   3. C(P) verdict: does some SCC contain two distinct cycles?  <=>
 *      some vertex has >= 2 successors inside its own SCC  <=>  rho > 1.
 *   4. lambda(y) by power iteration on the core + a Collatz-Wielandt
 *      bracket min_i (Av)_i/v_i <= rho <= max_i (Av)_i/v_i on the dominant
 *      SCC (a certified enclosure, [FKL10]-style).
 *   5. if C(P) fails, print two explicit distinct cycles through one state
 *      = an explicit eventually-periodic pair generating uncountably many
 *      aperiodic P-avoiding xi.
 *
 * Build:  gcc -O3 -march=native -fopenmp -o subshift subshift.c -lm
 * Run:    ./subshift <y> [maxpower]
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#ifdef _OPENMP
#include <omp.h>
#endif

#define BASE 7
#define NDIG 3
static const int DIG[NDIG] = {2, 4, 6};
#define MAXQ 20

static int Q[MAXQ], nq;
static long long rad[MAXQ], stride_[MAXQ];
static long long N, N1, N2;
static int split_k;                 /* number of low coordinates */

static int32_t *fwdLo[NDIG], *fwdHi[NDIG], *bwdLo[NDIG], *bwdHi[NDIG];

static uint64_t *alive;             /* N bits */
static long long nwords;

static inline int getbit(const uint64_t *b, long long i)
{ return (b[i >> 6] >> (i & 63)) & 1ULL; }
static inline void clrbit_atomic(uint64_t *b, long long i)
{ __atomic_fetch_and(&b[i >> 6], ~(1ULL << (i & 63)), __ATOMIC_RELAXED); }

static int isprime(int n){ for(int d=2;(long)d*d<=n;d++) if(n%d==0) return 0; return n>=2; }

static long long modinv(long long a, long long m)
{ long long g=m,x=0,x1=1,a1=a%m; while(a1){ long long q=g/a1,t;
    t=g-q*a1; g=a1; a1=t; t=x-q*x1; x=x1; x1=t; }
  return (x%m+m)%m; }

/* ---------------- table construction ---------------- */

/* Build per-half tables over coordinates [lo,hi) with local strides. */
static void build_half(int lo, int hi, long long n, int32_t *fwd[NDIG], int32_t *bwd[NDIG])
{
    long long ls[MAXQ]; long long s = 1;
    for (int j = lo; j < hi; j++) { ls[j] = s; s *= rad[j]; }
    for (int t = 0; t < NDIG; t++) {
        fwd[t] = malloc(sizeof(int32_t) * n);
        bwd[t] = malloc(sizeof(int32_t) * n);
        int d = DIG[t];
        for (long long i = 0; i < n; i++) {
            long long f = 0, b = 0; int okf = 1, okb = 1;
            for (int j = lo; j < hi; j++) {
                long long p = Q[j], r = (i / ls[j]) % rad[j] + 1;
                long long nr = (BASE * r + d) % p;          /* successor */
                if (nr == 0) okf = 0; else f += (nr - 1) * ls[j];
                long long pr = (modinv(BASE, p) * ((r - d) % p + p)) % p; /* predecessor */
                if (pr == 0) okb = 0; else b += (pr - 1) * ls[j];
            }
            fwd[t][i] = okf ? (int32_t)f : -1;
            bwd[t][i] = okb ? (int32_t)b : -1;
        }
    }
}

static void setup(int y)
{
    nq = 0;
    for (int p = 2; p <= y; p++)
        if (isprime(p) && p != 2 && p != BASE) Q[nq++] = p;
    N = 1;
    for (int j = 0; j < nq; j++) { rad[j] = Q[j] - 1; stride_[j] = N; N *= rad[j]; }

    /* choose the split: low half as large as possible under 20000 states */
    N2 = 1; split_k = 0;
    while (split_k < nq && N2 * rad[split_k] <= 20000) N2 *= rad[split_k++];
    N1 = N / N2;

    printf("y = %d   Q = {", y);
    for (int j = 0; j < nq; j++) printf("%d%s", Q[j], j + 1 < nq ? "," : "");
    printf("}\n");
    printf("  states N = %lld   (= phi(prod p<=y)/6)   split N1=%lld * N2=%lld\n", N, N1, N2);

    build_half(0, split_k, N2, fwdLo, bwdLo);
    build_half(split_k, nq, N1, fwdHi, bwdHi);
}

/* ---------------- pruning ---------------- */

static long long popcount_alive(void)
{
    long long c = 0;
#pragma omp parallel for reduction(+:c) schedule(static)
    for (long long w = 0; w < nwords; w++) c += __builtin_popcountll(alive[w]);
    return c;
}

/* one sweep; dir=0 forward (need a live successor), dir=1 backward. */
static long long sweep(int dir)
{
    long long removed = 0;
    int32_t **HI = dir ? bwdHi : fwdHi, **LO = dir ? bwdLo : fwdLo;
#pragma omp parallel for reduction(+:removed) schedule(dynamic, 64)
    for (long long i1 = 0; i1 < N1; i1++) {
        long long base = i1 * N2, hb[NDIG];
        for (int t = 0; t < NDIG; t++) {
            int32_t h = HI[t][i1];
            hb[t] = (h < 0) ? -1 : (long long)h * N2;
        }
        if (hb[0] < 0 && hb[1] < 0 && hb[2] < 0) {   /* whole block dies */
            for (long long i2 = 0; i2 < N2; i2++)
                if (getbit(alive, base + i2)) { clrbit_atomic(alive, base + i2); removed++; }
            continue;
        }
        for (long long i2 = 0; i2 < N2; i2++) {
            long long idx = base + i2;
            if (!getbit(alive, idx)) continue;
            int ok = 0;
            for (int t = 0; t < NDIG && !ok; t++) {
                if (hb[t] < 0) continue;
                int32_t l = LO[t][i2];
                if (l < 0) continue;
                if (getbit(alive, hb[t] + l)) ok = 1;
            }
            if (!ok) { clrbit_atomic(alive, idx); removed++; }
        }
    }
    return removed;
}

/* ---------------- compacted core ---------------- */

static long long ncore;
static long long *coreIdx;          /* compact -> global index */
static int32_t *succ;               /* NDIG per node, -1 if none */
static int8_t  *sdig;               /* digit of each successor slot */
static uint64_t *rankw;             /* prefix popcount per word */

static inline long long compact_of(long long idx)
{
    uint64_t w = alive[idx >> 6];
    uint64_t mask = (idx & 63) ? ((1ULL << (idx & 63)) - 1) : 0ULL;
    return (long long)rankw[idx >> 6] + __builtin_popcountll(w & mask);
}

static void compact_core(void)
{
    rankw = malloc(sizeof(uint64_t) * (nwords + 1));
    uint64_t acc = 0;
    for (long long w = 0; w < nwords; w++) { rankw[w] = acc; acc += __builtin_popcountll(alive[w]); }
    rankw[nwords] = acc;
    ncore = (long long)acc;

    coreIdx = malloc(sizeof(long long) * ncore);
#pragma omp parallel for schedule(static)
    for (long long w = 0; w < nwords; w++) {
        uint64_t x = alive[w]; long long c = (long long)rankw[w];
        while (x) { int b = __builtin_ctzll(x); coreIdx[c++] = (w << 6) + b; x &= x - 1; }
    }

    succ = malloc(sizeof(int32_t) * NDIG * ncore);
    sdig = malloc(sizeof(int8_t) * NDIG * ncore);
#pragma omp parallel for schedule(static)
    for (long long c = 0; c < ncore; c++) {
        long long idx = coreIdx[c], i1 = idx / N2, i2 = idx % N2;
        int k = 0;
        for (int t = 0; t < NDIG; t++) {
            int32_t h = fwdHi[t][i1], l = fwdLo[t][i2];
            if (h < 0 || l < 0) continue;
            long long j = (long long)h * N2 + l;
            if (!getbit(alive, j)) continue;
            succ[NDIG * c + k] = (int32_t)compact_of(j);
            sdig[NDIG * c + k] = (int8_t)DIG[t];
            k++;
        }
        for (; k < NDIG; k++) { succ[NDIG * c + k] = -1; sdig[NDIG * c + k] = 0; }
    }
}

/* CRT value of a core node modulo prod Q (for readable witnesses) */
static long long crt_label(long long c)
{
    long long idx = coreIdx[c], Mq = 1;
    for (int j = 0; j < nq; j++) Mq *= Q[j];
    __int128 v = 0;
    for (int j = 0; j < nq; j++) {
        long long p = Q[j], r = (idx / stride_[j]) % rad[j] + 1, co = Mq / p;
        v += (__int128)r * co * modinv(co % p, p);
    }
    return (long long)(v % Mq);
}

/* ---------------- Tarjan ---------------- */

static int32_t *comp;               /* SCC id per node */
static int32_t ncomp;

static void tarjan(void)
{
    int32_t *num = malloc(sizeof(int32_t) * ncore);
    int32_t *low = malloc(sizeof(int32_t) * ncore);
    int32_t *stk = malloc(sizeof(int32_t) * ncore);
    uint8_t *ons = calloc(ncore, 1);
    int32_t *dn = malloc(sizeof(int32_t) * ncore);   /* dfs stack: node */
    int8_t  *dc = malloc(sizeof(int8_t) * ncore);    /* dfs stack: child slot */
    comp = malloc(sizeof(int32_t) * ncore);
    for (long long i = 0; i < ncore; i++) { num[i] = -1; comp[i] = -1; }
    int32_t counter = 0, sp = 0; ncomp = 0;

    for (long long root = 0; root < ncore; root++) {
        if (num[root] >= 0) continue;
        int dsp = 0;
        dn[0] = (int32_t)root; dc[0] = 0;
        num[root] = low[root] = counter++;
        stk[sp++] = (int32_t)root; ons[root] = 1;
        while (dsp >= 0) {
            int32_t v = dn[dsp];
            if (dc[dsp] < NDIG) {
                int32_t w = succ[NDIG * (long long)v + dc[dsp]];
                dc[dsp]++;
                if (w < 0) continue;
                if (num[w] < 0) {
                    num[w] = low[w] = counter++;
                    stk[sp++] = w; ons[w] = 1;
                    dsp++; dn[dsp] = w; dc[dsp] = 0;
                } else if (ons[w]) {
                    if (num[w] < low[v]) low[v] = num[w];
                }
            } else {
                if (low[v] == num[v]) {
                    int32_t w;
                    do { w = stk[--sp]; ons[w] = 0; comp[w] = ncomp; } while (w != v);
                    ncomp++;
                }
                dsp--;
                if (dsp >= 0 && low[v] < low[dn[dsp]]) low[dn[dsp]] = low[v];
            }
        }
    }
    free(num); free(low); free(stk); free(ons); free(dn); free(dc);
}

/* ---------------- power iteration ---------------- */

static double power_iter(const int32_t *nodes, long long n, int iters,
                         double *lo_out, double *hi_out)
{
    /* nodes == NULL: whole core (compact ids 0..ncore-1).
       else: a subset; we build a local index via a scratch map. */
    double *v = malloc(sizeof(double) * ncore);
    double *w = malloc(sizeof(double) * ncore);
    uint8_t *in = NULL;
    if (nodes) { in = calloc(ncore, 1); for (long long i = 0; i < n; i++) in[nodes[i]] = 1; }
#pragma omp parallel for schedule(static)
    for (long long i = 0; i < ncore; i++) v[i] = (!nodes || in[i]) ? 1.0 : 0.0;

    double lam = 0.0, lo = 0, hi = 0;
    for (int it = 0; it < iters; it++) {
        double s = 0, sv = 0;
#pragma omp parallel for reduction(+:s,sv) schedule(static)
        for (long long i = 0; i < ncore; i++) {
            if (nodes && !in[i]) { w[i] = 0; continue; }
            double a = 0;
            for (int t = 0; t < NDIG; t++) {
                int32_t j = succ[NDIG * i + t];
                if (j >= 0 && (!nodes || in[j])) a += v[j];
            }
            w[i] = a; s += a; sv += v[i];
        }
        if (s == 0) { lam = 0; break; }
        lam = s / sv;
        /* Collatz-Wielandt bracket on the current iterate */
        lo = 1e300; hi = 0;
#pragma omp parallel for reduction(min:lo) reduction(max:hi) schedule(static)
        for (long long i = 0; i < ncore; i++) {
            if (nodes && !in[i]) continue;
            if (v[i] <= 0) continue;
            double q = w[i] / v[i];
            if (q < lo) lo = q;
            if (q > hi) hi = q;
        }
        double sc = (double)((nodes ? n : ncore)) / s;
#pragma omp parallel for schedule(static)
        for (long long i = 0; i < ncore; i++) v[i] = w[i] * sc;
    }
    if (lo_out) *lo_out = lo;
    if (hi_out) *hi_out = hi;
    free(v); free(w); if (in) free(in);
    return lam;
}

/* ---------------- witness cycles ---------------- */

static int32_t *bfs_parent, *bfs_pdig, *bfs_q;

/* shortest path from s to t inside SCC cid, first edge forced to (s,slot). */
static int path_in_scc(int32_t s, int slot, int32_t t, int32_t cid,
                       int32_t *out, int8_t *outd, int *len)
{
    int32_t first = succ[NDIG * (long long)s + slot];
    if (first < 0 || comp[first] != cid) return 0;
    for (long long i = 0; i < ncore; i++) bfs_parent[i] = -2;
    int head = 0, tail = 0;
    bfs_parent[first] = s; bfs_pdig[first] = sdig[NDIG * (long long)s + slot];
    bfs_q[tail++] = first;
    if (first == t) goto done;
    while (head < tail) {
        int32_t v = bfs_q[head++];
        for (int k = 0; k < NDIG; k++) {
            int32_t u = succ[NDIG * (long long)v + k];
            if (u < 0 || comp[u] != cid || bfs_parent[u] != -2) continue;
            bfs_parent[u] = v; bfs_pdig[u] = sdig[NDIG * (long long)v + k];
            if (u == t) goto done;
            bfs_q[tail++] = u;
        }
    }
    return 0;
done: {
        int32_t cur = t; int L = 0;
        int32_t tmp[4096]; int8_t tmpd[4096];
        while (1) {
            tmp[L] = cur; tmpd[L] = (int8_t)bfs_pdig[cur]; L++;
            if (cur == first) break;
            cur = bfs_parent[cur];
            if (L > 4000) return 0;
        }
        for (int i = 0; i < L; i++) { out[i] = tmp[L - 1 - i]; outd[i] = tmpd[L - 1 - i]; }
        *len = L;
        return 1;
    }
}

int main(int argc, char **argv)
{
    int y = (argc > 1) ? atoi(argv[1]) : 19;
    int iters = (argc > 2) ? atoi(argv[2]) : 3000;

    setup(y);
    nwords = (N + 63) / 64;
    alive = malloc(sizeof(uint64_t) * nwords);
    memset(alive, 0xFF, sizeof(uint64_t) * nwords);
    if (N & 63) alive[nwords - 1] = (1ULL << (N & 63)) - 1;

    long long before = N;
    int round = 0;
    for (;;) {
        long long r1 = sweep(0), r2 = sweep(1);
        round++;
        if (r1 + r2 == 0) break;
        if (round % 5 == 0 || r1 + r2 == 0)
            printf("  prune round %2d: alive %lld\n", round, popcount_alive());
    }
    long long ncore_bits = popcount_alive();
    printf("  core after pruning: %lld states  (%.4f%% of %lld), %d rounds\n",
           ncore_bits, 100.0 * ncore_bits / before, before, round);
    if (ncore_bits == 0) {
        printf("  CORE EMPTY -> lambda = 0: P is an UNAVOIDABLE divisor set for y=%d.\n", y);
        return 0;
    }

    compact_core();
    /* out-degree histogram inside the core */
    long long hist[NDIG + 1] = {0};
    for (long long c = 0; c < ncore; c++) {
        int k = 0; for (int t = 0; t < NDIG; t++) if (succ[NDIG * c + t] >= 0) k++;
        hist[k]++;
    }
    printf("  core out-degrees: ");
    for (int k = 0; k <= NDIG; k++) printf("%d:%lld  ", k, hist[k]);
    printf("\n");

    tarjan();
    long long *csize = calloc(ncomp, sizeof(long long));
    char *cbranch = calloc(ncomp, 1);
    char *ccyc = calloc(ncomp, 1);
    for (long long c = 0; c < ncore; c++) {
        csize[comp[c]]++;
        int inside = 0;
        for (int t = 0; t < NDIG; t++) {
            int32_t j = succ[NDIG * c + t];
            if (j >= 0 && comp[j] == comp[c]) inside++;
        }
        if (inside >= 1) ccyc[comp[c]] = 1;
        if (inside >= 2) cbranch[comp[c]] = 1;
    }
    long long ncyc = 0, nbr = 0, biggest = 0; int32_t argbig = -1, argbr = -1;
    for (int32_t k = 0; k < ncomp; k++) {
        if (ccyc[k]) ncyc++;
        if (cbranch[k]) { nbr++; if (argbr < 0) argbr = k; }
        if (ccyc[k] && csize[k] > biggest) { biggest = csize[k]; argbig = k; }
    }
    printf("  SCCs: %d total, %lld carry a cycle, %lld branching; largest cyclic SCC %lld\n",
           ncomp, ncyc, nbr, biggest);

    double lo = 0, hi = 0;
    double lam = power_iter(NULL, ncore, iters, &lo, &hi);
    printf("  lambda(y) = %.9f   (power iteration, %d its)\n", lam, iters);
    printf("  dim = log lambda / log 7 = %.9f\n", log(lam) / log((double)BASE));

    if (argbig >= 0) {
        int32_t *nodes = malloc(sizeof(int32_t) * biggest); long long m = 0;
        for (long long c = 0; c < ncore; c++) if (comp[c] == argbig) nodes[m++] = (int32_t)c;
        double l2, h2;
        double lamb = power_iter(nodes, m, iters, &l2, &h2);
        printf("  dominant SCC (%lld states): lambda = %.9f, "
               "Collatz-Wielandt bracket [%.9f, %.9f]\n", m, lamb, l2, h2);
        free(nodes);
    }

    double lbar = BASE;
    for (int p = 2; p <= y; p++) if (isprime(p)) lbar *= (1.0 - 1.0 / p);
    printf("  first moment lbar(y) = %.6f   ratio lambda/lbar = %.4f\n", lbar, lam / lbar);
    printf("  C(P) [no SCC contains two distinct cycles] : %s\n",
           nbr == 0 ? "HOLDS  ==>  a=7 SOLVED at this y" : "FAILS");

    if (nbr > 0) {
        /* explicit witness: a state with two in-SCC successors + two return paths */
        bfs_parent = malloc(sizeof(int32_t) * ncore);
        bfs_pdig = malloc(sizeof(int32_t) * ncore);
        bfs_q = malloc(sizeof(int32_t) * ncore);
        int32_t s = -1; int s1 = -1, s2 = -1;
        for (long long c = 0; c < ncore && s < 0; c++) {
            if (comp[c] != argbr) continue;
            int f = -1;
            for (int t = 0; t < NDIG; t++) {
                int32_t j = succ[NDIG * c + t];
                if (j >= 0 && comp[j] == comp[c]) { if (f < 0) f = t; else { s = (int32_t)c; s1 = f; s2 = t; } }
            }
        }
        if (s >= 0) {
            int32_t p1[4096], p2[4096]; int8_t d1[4096], d2[4096]; int L1 = 0, L2 = 0;
            int ok1 = path_in_scc(s, s1, s, argbr, p1, d1, &L1);
            int ok2 = path_in_scc(s, s2, s, argbr, p2, d2, &L2);
            printf("  witness: state r = %lld (mod prod Q) carries two distinct cycles\n", crt_label(s));
            if (ok1) { printf("    cycle A (len %d), digits:", L1);
                       for (int i = 0; i < L1 && i < 60; i++) printf(" %d", d1[i]); printf("\n"); }
            if (ok2) { printf("    cycle B (len %d), digits:", L2);
                       for (int i = 0; i < L2 && i < 60; i++) printf(" %d", d2[i]); printf("\n"); }
            if (ok1 && ok2)
                printf("    => the language contains {A,B}^* : uncountably many aperiodic "
                       "P-avoiding xi, h_top >= log 2 / %d\n", (L1 > L2 ? L1 : L2));
        }
    }
    return 0;
}
