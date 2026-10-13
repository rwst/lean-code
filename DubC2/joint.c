/* (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
 *
 * joint.c -- plan-dubC2 milestone M1, experiment X1: the INDEPENDENT
 * implementation of the joint (q-adic x odd-residue x interval-cell) subshift
 * G(P, K, D) for  x_n = [ xi (p/q)^n + nu ],  q x_{n+1} = p x_n + s_n.
 *
 * R-6 discipline: this file shares no code with the reference `joint.py`.
 * Where the reference uses fractions.Fraction, this uses int64 numerators over
 * one common denominator; where the reference peels with numpy bincounts and
 * decomposes with scipy's compiled Tarjan, this peels with a degree-counter
 * worklist over a CSR graph and runs its own iterative Tarjan; where the
 * reference determinizes with Python frozensets, this hashes sorted int32
 * arrays.  The two must agree on every field of the --summary line.
 *
 * Model, alphabet, edges and the two verdicts C(P) / C_det(P) are documented
 * in joint.py; see there.  In one line:
 *
 *     y_{n+1} = (p y_n - w - s)/q,   w = (p-q) nu,
 *     Dom(s)  = [ (s+w)/p, (s+q+w)/p ) n [0,1),
 *     s = -p x_n mod q,   x_{n+1} = q^{-1}(p x_n + s) mod l  (l in P, l !| q).
 *
 * Build:  gcc -O2 -o joint joint.c -lm
 * Run:    ./joint --pq 3 2 --nu 1/2 --P 2,5,7,11 --K 2 --k 6 [--det] [--summary]
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

/* ------------------------------------------------------------------ misc -- */

static long long ipow(long long b, int e)
{ long long r = 1; while (e--) r *= b; return r; }

static long long ffdiv(long long a, long long b)      /* floor division, b > 0 */
{ long long q = a / b; if ((a % b) && ((a < 0) != (b < 0))) q--; return q; }

static long long ccdiv(long long a, long long b)      /* ceil  division, b > 0 */
{ return -ffdiv(-a, b); }

static long long egcd_inv(long long a, long long m)
{ long long g = m, x = 0, x1 = 1, a1 = a % m;
  while (a1) { long long qq = g / a1, t;
    t = g - qq * a1; g = a1; a1 = t;
    t = x - qq * x1; x = x1; x1 = t; }
  return ((x % m) + m) % m; }

static void *xmalloc(size_t n)
{ void *p = malloc(n); if (!p) { fprintf(stderr, "oom %zu\n", n); exit(2); } return p; }

/* --------------------------------------------------------------- model --- */

static long long P_, Q_, NUN, NUD, W_;      /* base p/q, nu = NUN/NUD, w=(p-q)nu */
static int K_;                              /* q-adic depth */
static long long D_;                        /* number of cells */
static int PRIMES[16], NP;                  /* the candidate set P */
static int QL[16], NQ;                      /* primes of P not dividing q */
static int AVOID_Q;                         /* q in P ? */
static int SLO, SHI, NS;                    /* alphabet S(p/q,nu) = [SLO,SHI] */

/* Dom(s) n [0,1) as [loN, hiN) over the denominator D_.  Requires p*NUD | D_. */
static void dom_cells(int s, long long *loN, long long *hiN)
{
    long long F = D_ / (P_ * NUD);
    long long lo = (s * NUD + W_) * F;
    long long hi = (s * NUD + W_ + Q_ * NUD) * F;
    *loN = lo < 0 ? 0 : lo;
    *hiN = hi > D_ ? D_ : hi;
}

/* image of the point a/D_ under T_s, times D_, as an exact rational
 * numerator over the denominator Q_*NUD. */
static long long img_num(long long a, int s)
{ return P_ * a * NUD - W_ * D_ - (long long)s * NUD * D_; }

/* ------------------------------------------------------- coordinate tables */

static long long QK;                 /* q^K */
static int32_t *USTATE;              /* allowed u values      */
static int32_t *UPOS;                /* u -> index or -1      */
static int NU_;                      /* number of u states    */
static int32_t *UTAB;                /* [letter][uidx] -> up to Q_ successors */
static int8_t  *UCNT;
static int32_t *RTAB;                /* [letter][ridx] -> ridx or -1 */
static long long NR;                 /* number of residue states */
static int32_t *CLO, *CHI;           /* [letter][cell] -> [j0,j1) or j0=-1 */

static void build_tables(void)
{
    long long qK1 = QK * Q_;
    USTATE = xmalloc(QK * sizeof(int32_t));
    UPOS   = xmalloc(QK * sizeof(int32_t));
    NU_ = 0;
    for (long long u = 0; u < QK; u++) {
        UPOS[u] = -1;
        if (AVOID_Q && u % Q_ == 0) continue;
        UPOS[u] = NU_; USTATE[NU_++] = (int32_t)u;
    }
    UTAB = xmalloc((size_t)NS * NU_ * Q_ * sizeof(int32_t));
    UCNT = xmalloc((size_t)NS * NU_ * sizeof(int8_t));
    memset(UCNT, 0, (size_t)NS * NU_);
    for (int si = 0; si < NS; si++) {
        int s = SLO + si;
        for (int iu = 0; iu < NU_; iu++) {
            long long u = USTATE[iu];
            if (((P_ * u + s) % Q_ + Q_) % Q_ != 0) continue;
            int cnt = 0;
            for (long long j = 0; j < Q_; j++) {
                long long ut = u + j * QK;
                long long t = ((P_ * ut + s) % qK1 + qK1) % qK1;
                long long u2 = (t / Q_) % QK;
                if (AVOID_Q && u2 % Q_ == 0) continue;
                int dup = 0;
                for (int m = 0; m < cnt; m++)
                    if (UTAB[((size_t)si * NU_ + iu) * Q_ + m] == UPOS[u2]) dup = 1;
                if (dup) continue;
                UTAB[((size_t)si * NU_ + iu) * Q_ + cnt++] = UPOS[u2];
            }
            UCNT[(size_t)si * NU_ + iu] = (int8_t)cnt;
        }
    }
    /* residues: mixed radix over QL, digit l-1 (nonzero residues) */
    NR = 1;
    for (int i = 0; i < NQ; i++) NR *= (QL[i] - 1);
    RTAB = xmalloc((size_t)NS * NR * sizeof(int32_t));
    for (int si = 0; si < NS; si++) {
        int s = SLO + si;
        for (long long r = 0; r < NR; r++) {
            long long rest = r, out = 0, mul = 1;
            int ok = 1;
            for (int i = 0; i < NQ; i++) {
                long long l = QL[i];
                long long v = rest % (l - 1) + 1; rest /= (l - 1);
                long long qi = egcd_inv(Q_ % l, l);
                long long v2 = ((qi * ((P_ * v + s) % l + l)) % l + l) % l;
                if (v2 == 0) { ok = 0; break; }
                out += (v2 - 1) * mul; mul *= (l - 1);
            }
            RTAB[(size_t)si * NR + r] = ok ? (int32_t)out : -1;
        }
    }
    /* cells */
    CLO = xmalloc((size_t)NS * D_ * sizeof(int32_t));
    CHI = xmalloc((size_t)NS * D_ * sizeof(int32_t));
    for (int si = 0; si < NS; si++) {
        int s = SLO + si;
        long long lo, hi;
        dom_cells(s, &lo, &hi);
        for (long long c = 0; c < D_; c++) {
            int32_t *pl = &CLO[(size_t)si * D_ + c], *ph = &CHI[(size_t)si * D_ + c];
            *pl = -1; *ph = -1;
            long long a = c   > lo ? c   : lo;
            long long b = c+1 < hi ? c+1 : hi;
            if (a >= b) continue;
            long long den = Q_ * NUD;
            long long j0 = ffdiv(img_num(a, s), den);
            long long j1 = ccdiv(img_num(b, s), den);
            if (j0 < 0) j0 = 0;
            if (j1 > D_) j1 = D_;
            if (j0 >= j1) continue;
            *pl = (int32_t)j0; *ph = (int32_t)j1;
        }
    }
}

/* ------------------------------------------------------------ the graph --- */

static long long NV;                 /* NU_ * NR * D_ */
static long long NE;
static int64_t *ESRC, *EDST;
static int8_t  *ELAB;

#define SID(iu, r, c)  (((int64_t)(iu) * NR + (r)) * D_ + (c))

static void build_graph(void)
{
    NV = (long long)NU_ * NR * D_;
    /* pass 1: count */
    long long cnt = 0;
    for (int pass = 0; pass < 2; pass++) {
        if (pass == 1) {
            NE = cnt;
            ESRC = xmalloc((size_t)NE * sizeof(int64_t));
            EDST = xmalloc((size_t)NE * sizeof(int64_t));
            ELAB = xmalloc((size_t)NE * sizeof(int8_t));
            cnt = 0;
        }
        for (int si = 0; si < NS; si++) {
            int s = SLO + si;
            for (int iu = 0; iu < NU_; iu++) {
                int nu2 = UCNT[(size_t)si * NU_ + iu];
                if (!nu2) continue;
                for (long long r = 0; r < NR; r++) {
                    int32_t r2 = RTAB[(size_t)si * NR + r];
                    if (r2 < 0) continue;
                    for (long long c = 0; c < D_; c++) {
                        int32_t j0 = CLO[(size_t)si * D_ + c];
                        if (j0 < 0) continue;
                        int32_t j1 = CHI[(size_t)si * D_ + c];
                        for (int m = 0; m < nu2; m++) {
                            int iu2 = UTAB[((size_t)si * NU_ + iu) * Q_ + m];
                            for (int32_t j = j0; j < j1; j++) {
                                if (pass == 1) {
                                    ESRC[cnt] = SID(iu, r, c);
                                    EDST[cnt] = SID(iu2, r2, j);
                                    ELAB[cnt] = (int8_t)s;
                                }
                                cnt++;
                            }
                        }
                    }
                }
            }
        }
    }
}

/* ------------------------------------------------------------- the peel --- */

static uint8_t *ALIVE_V, *ALIVE_E;

static long long peel(long long *core_edges)
{
    ALIVE_V = xmalloc(NV); memset(ALIVE_V, 1, NV);
    ALIVE_E = xmalloc(NE); memset(ALIVE_E, 1, NE);
    int32_t *outd = xmalloc(NV * sizeof(int32_t));
    int32_t *ind  = xmalloc(NV * sizeof(int32_t));
    for (;;) {
        memset(outd, 0, NV * sizeof(int32_t));
        memset(ind,  0, NV * sizeof(int32_t));
        for (long long e = 0; e < NE; e++)
            if (ALIVE_E[e]) { outd[ESRC[e]]++; ind[EDST[e]]++; }
        long long killed = 0;
        for (long long v = 0; v < NV; v++)
            if (ALIVE_V[v] && (!outd[v] || !ind[v])) { ALIVE_V[v] = 0; killed++; }
        if (!killed) break;
        for (long long e = 0; e < NE; e++)
            if (ALIVE_E[e] && (!ALIVE_V[ESRC[e]] || !ALIVE_V[EDST[e]])) ALIVE_E[e] = 0;
    }
    free(outd); free(ind);
    long long n = 0, m = 0;
    for (long long v = 0; v < NV; v++) if (ALIVE_V[v]) n++;
    for (long long e = 0; e < NE; e++) if (ALIVE_E[e]) m++;
    *core_edges = m;
    return n;
}

/* ------------------------------------------------- compacted core + Tarjan */

static int32_t NC;                  /* core node count */
static int64_t *COREID;             /* core index -> global id */
static int32_t *CSR_OFF, *CSR_DST;  /* core adjacency */
static int8_t  *CSR_LAB;
static int32_t CM;                  /* core edge count */
static int32_t *COMP; static int32_t NCOMP;

static void compact(void)
{
    int32_t *remap = xmalloc(NV * sizeof(int32_t));
    NC = 0;
    for (long long v = 0; v < NV; v++) remap[v] = ALIVE_V[v] ? NC++ : -1;
    COREID = xmalloc((size_t)NC * sizeof(int64_t));
    for (long long v = 0; v < NV; v++) if (ALIVE_V[v]) COREID[remap[v]] = v;
    CM = 0;
    for (long long e = 0; e < NE; e++) if (ALIVE_E[e]) CM++;
    CSR_OFF = xmalloc(((size_t)NC + 1) * sizeof(int32_t));
    CSR_DST = xmalloc((size_t)CM * sizeof(int32_t));
    CSR_LAB = xmalloc((size_t)CM);
    memset(CSR_OFF, 0, ((size_t)NC + 1) * sizeof(int32_t));
    for (long long e = 0; e < NE; e++) if (ALIVE_E[e]) CSR_OFF[remap[ESRC[e]] + 1]++;
    for (int32_t i = 0; i < NC; i++) CSR_OFF[i + 1] += CSR_OFF[i];
    int32_t *fill = xmalloc((size_t)NC * sizeof(int32_t));
    memcpy(fill, CSR_OFF, (size_t)NC * sizeof(int32_t));
    for (long long e = 0; e < NE; e++) if (ALIVE_E[e]) {
        int32_t a = remap[ESRC[e]], k = fill[a]++;
        CSR_DST[k] = remap[EDST[e]]; CSR_LAB[k] = ELAB[e];
    }
    free(fill); free(remap);
}

static void tarjan(void)
{
    int32_t *idx = xmalloc((size_t)NC * sizeof(int32_t));
    int32_t *low = xmalloc((size_t)NC * sizeof(int32_t));
    int32_t *stk = xmalloc((size_t)NC * sizeof(int32_t));
    uint8_t *ons = xmalloc((size_t)NC);
    int32_t *cst = xmalloc((size_t)NC * sizeof(int32_t));   /* call stack: node */
    int32_t *cei = xmalloc((size_t)NC * sizeof(int32_t));   /* call stack: edge */
    COMP = xmalloc((size_t)NC * sizeof(int32_t));
    for (int32_t i = 0; i < NC; i++) { idx[i] = -1; COMP[i] = -1; ons[i] = 0; }
    int32_t counter = 0, sp = 0, csp;
    NCOMP = 0;
    for (int32_t root = 0; root < NC; root++) {
        if (idx[root] != -1) continue;
        csp = 0; cst[csp] = root; cei[csp] = CSR_OFF[root];
        idx[root] = low[root] = counter++; stk[sp++] = root; ons[root] = 1;
        while (csp >= 0) {
            int32_t v = cst[csp];
            if (cei[csp] < CSR_OFF[v + 1]) {
                int32_t w = CSR_DST[cei[csp]++];
                if (idx[w] == -1) {
                    idx[w] = low[w] = counter++; stk[sp++] = w; ons[w] = 1;
                    csp++; cst[csp] = w; cei[csp] = CSR_OFF[w];
                } else if (ons[w]) {
                    if (idx[w] < low[v]) low[v] = idx[w];
                }
            } else {
                if (low[v] == idx[v]) {
                    for (;;) { int32_t w = stk[--sp]; ons[w] = 0; COMP[w] = NCOMP;
                               if (w == v) break; }
                    NCOMP++;
                }
                csp--;
                if (csp >= 0 && low[v] < low[cst[csp]]) low[cst[csp]] = low[v];
            }
        }
    }
    free(idx); free(low); free(stk); free(ons); free(cst); free(cei);
}

static double perron(int32_t n, int32_t m, const int32_t *ea, const int32_t *eb);

/* ------------------------------------------------------- determinization -- */

typedef struct { int32_t n; int32_t *v; int32_t h; } Subset;
static Subset *SUB; static int32_t NSUB, CAPSUB;
static int32_t *HTAB; static int32_t HMASK;

static int32_t hash_of(const int32_t *v, int32_t n)
{ uint32_t h = 2166136261u;
  for (int32_t i = 0; i < n; i++) { h ^= (uint32_t)v[i]; h *= 16777619u; }
  return (int32_t)(h & 0x7fffffff); }

static int32_t sub_intern(int32_t *v, int32_t n)
{
    int32_t h = hash_of(v, n), i = h & HMASK;
    while (HTAB[i] != -1) {
        Subset *S = &SUB[HTAB[i]];
        if (S->h == h && S->n == n && !memcmp(S->v, v, (size_t)n * sizeof(int32_t)))
            return HTAB[i];
        i = (i + 1) & HMASK;
    }
    if (NSUB >= CAPSUB) return -2;
    SUB[NSUB].n = n; SUB[NSUB].h = h;
    SUB[NSUB].v = xmalloc((size_t)n * sizeof(int32_t));
    memcpy(SUB[NSUB].v, v, (size_t)n * sizeof(int32_t));
    HTAB[i] = NSUB;
    return NSUB++;
}

static int cmp32(const void *a, const void *b)
{ int32_t x = *(const int32_t *)a, y = *(const int32_t *)b; return x < y ? -1 : x > y; }

/* Determinize the induced labelled subgraph on component `c`, from S0 = c.
 * Returns 0 = every cyclic SCC of det() is a simple cycle, 1 = branching,
 * 2 = hit the cap.  Adds the det state count to *nstates. */
static int det_component(int32_t c, int32_t *members, int32_t nm,
                         long long *nstates, double *lam)
{
    CAPSUB = 400000; NSUB = 0;
    SUB = xmalloc((size_t)CAPSUB * sizeof(Subset));
    int32_t hsz = 1; while (hsz < 4 * CAPSUB) hsz <<= 1;
    HMASK = hsz - 1;
    HTAB = xmalloc((size_t)hsz * sizeof(int32_t));
    for (int32_t i = 0; i < hsz; i++) HTAB[i] = -1;

    int32_t *buf = xmalloc((size_t)nm * sizeof(int32_t));
    int32_t s0 = sub_intern(members, nm);
    /* det edges */
    int32_t decap = 4 * CAPSUB, den = 0;
    int32_t *da = xmalloc((size_t)decap * sizeof(int32_t));
    int32_t *db = xmalloc((size_t)decap * sizeof(int32_t));
    int8_t  *dl = xmalloc((size_t)decap);
    uint8_t *mark = xmalloc((size_t)NC); memset(mark, 0, (size_t)NC);
    int rc = 0;
    for (int32_t head = 0; head < NSUB; head++) {
        for (int si = 0; si < NS; si++) {
            int s = SLO + si;
            int32_t k = 0;
            Subset *S = &SUB[head];
            for (int32_t i = 0; i < S->n; i++) {
                int32_t v = S->v[i];
                for (int32_t e = CSR_OFF[v]; e < CSR_OFF[v + 1]; e++) {
                    int32_t w = CSR_DST[e];
                    if (CSR_LAB[e] != s || COMP[w] != c || mark[w]) continue;
                    mark[w] = 1; buf[k++] = w;
                }
            }
            if (!k) continue;
            for (int32_t i = 0; i < k; i++) mark[buf[i]] = 0;
            qsort(buf, k, sizeof(int32_t), cmp32);
            int32_t j = sub_intern(buf, k);
            if (j == -2) { rc = 2; goto done; }
            if (den >= decap) { rc = 2; goto done; }
            da[den] = head; db[den] = j; dl[den] = (int8_t)s; den++;
        }
    }
    {   /* peel + SCC on the det automaton (small): iterate to fixpoint */
        uint8_t *av = xmalloc((size_t)NSUB); memset(av, 1, (size_t)NSUB);
        uint8_t *ae = xmalloc((size_t)den); memset(ae, 1, (size_t)den);
        int32_t *od = xmalloc((size_t)NSUB * sizeof(int32_t));
        int32_t *id = xmalloc((size_t)NSUB * sizeof(int32_t));
        for (;;) {
            memset(od, 0, (size_t)NSUB * sizeof(int32_t));
            memset(id, 0, (size_t)NSUB * sizeof(int32_t));
            for (int32_t e = 0; e < den; e++) if (ae[e]) { od[da[e]]++; id[db[e]]++; }
            int32_t killed = 0;
            for (int32_t v = 0; v < NSUB; v++)
                if (av[v] && (!od[v] || !id[v])) { av[v] = 0; killed++; }
            if (!killed) break;
            for (int32_t e = 0; e < den; e++)
                if (ae[e] && (!av[da[e]] || !av[db[e]])) ae[e] = 0;
        }
        int32_t alive = 0;
        for (int32_t v = 0; v < NSUB; v++) if (av[v]) alive++;
        *nstates += alive;
        /* SCC by repeated reachability (small graphs; independent of Tarjan) */
        int32_t *comp = xmalloc((size_t)NSUB * sizeof(int32_t));
        for (int32_t v = 0; v < NSUB; v++) comp[v] = -1;
        uint8_t *fr = xmalloc((size_t)NSUB), *br = xmalloc((size_t)NSUB);
        int32_t nc2 = 0;
        for (int32_t v = 0; v < NSUB; v++) {
            if (!av[v] || comp[v] >= 0) continue;
            memset(fr, 0, (size_t)NSUB); memset(br, 0, (size_t)NSUB);
            fr[v] = br[v] = 1;
            for (int ch = 1; ch;) { ch = 0;
                for (int32_t e = 0; e < den; e++) if (ae[e]) {
                    if (fr[da[e]] && !fr[db[e]]) { fr[db[e]] = 1; ch = 1; }
                    if (br[db[e]] && !br[da[e]]) { br[da[e]] = 1; ch = 1; } } }
            for (int32_t w = 0; w < NSUB; w++)
                if (av[w] && fr[w] && br[w]) comp[w] = nc2;
            nc2++;
        }
        /* branching inside a component == two distinct cycles */
        int32_t *odin = xmalloc((size_t)NSUB * sizeof(int32_t));
        memset(odin, 0, (size_t)NSUB * sizeof(int32_t));
        int32_t inedges = 0;
        for (int32_t e = 0; e < den; e++)
            if (ae[e] && comp[da[e]] == comp[db[e]] && comp[da[e]] >= 0)
                { odin[da[e]]++; inedges++; }
        for (int32_t v = 0; v < NSUB; v++) if (odin[v] >= 2) rc = 1;
        if (inedges) {
            int32_t *loc2 = xmalloc((size_t)NSUB * sizeof(int32_t));
            int32_t *ea = xmalloc((size_t)inedges * sizeof(int32_t));
            int32_t *eb = xmalloc((size_t)inedges * sizeof(int32_t));
            for (int32_t cc = 0; cc < nc2; cc++) {
                int32_t n = 0;
                for (int32_t v = 0; v < NSUB; v++) if (comp[v] == cc) loc2[v] = n++;
                int32_t k = 0;
                for (int32_t e = 0; e < den; e++)
                    if (ae[e] && comp[da[e]] == cc && comp[db[e]] == cc)
                        { ea[k] = loc2[da[e]]; eb[k] = loc2[db[e]]; k++; }
                if (!k) continue;
                double r = perron(n, k, ea, eb);
                if (r > *lam) *lam = r;
            }
            free(loc2); free(ea); free(eb);
        }
        free(av); free(ae); free(od); free(id); free(comp); free(fr); free(br);
        free(odin);
    }
done:
    free(buf); free(da); free(db); free(dl); free(mark);
    for (int32_t i = 0; i < NSUB; i++) free(SUB[i].v);
    free(SUB); free(HTAB);
    return rc;
}

/* --------------------------------------------------------------- driver -- */

/* Perron root of ONE strongly connected 0-1-multigraph given as a local edge
 * list: power iteration on B = A + I (primitive, hence convergent) with a
 * Collatz-Wielandt bracket; rho(A) = rho(B) - 1.  Same recipe as joint.py's
 * perron(), independently coded. */
static double perron(int32_t n, int32_t m, const int32_t *ea, const int32_t *eb)
{
    if (!n || !m) return 0.0;
    double *v = xmalloc((size_t)n * sizeof(double));
    double *w = xmalloc((size_t)n * sizeof(double));
    for (int32_t i = 0; i < n; i++) v[i] = 1.0;
    double hi = n;
    for (int it = 0; it < 200000; it++) {
        for (int32_t i = 0; i < n; i++) w[i] = v[i];
        for (int32_t e = 0; e < m; e++) w[ea[e]] += v[eb[e]];
        double lo = 1e300, mx = 0;
        hi = 0;
        for (int32_t i = 0; i < n; i++) {
            double r = w[i] / v[i];
            if (r < lo) lo = r;
            if (r > hi) hi = r;
            if (w[i] > mx) mx = w[i];
        }
        for (int32_t i = 0; i < n; i++) v[i] = w[i] / mx;
        if (hi - lo <= 1e-13 * hi) break;
    }
    free(v); free(w);
    return hi - 1.0;
}

/* rho(core) = max over the cyclic SCCs of that SCC's Perron root. */
static double core_rho(const int32_t *sz, const int32_t *ei)
{
    double best = 0.0;
    int32_t *loc = xmalloc((size_t)NC * sizeof(int32_t));
    for (int32_t c = 0; c < NCOMP; c++) {
        if (!ei[c]) continue;
        int32_t n = 0;
        for (int32_t v = 0; v < NC; v++) if (COMP[v] == c) loc[v] = n++;
        int32_t m = ei[c];
        int32_t *ea = xmalloc((size_t)m * sizeof(int32_t));
        int32_t *eb = xmalloc((size_t)m * sizeof(int32_t));
        int32_t k = 0;
        for (int32_t v = 0; v < NC; v++) {
            if (COMP[v] != c) continue;
            for (int32_t e = CSR_OFF[v]; e < CSR_OFF[v + 1]; e++)
                if (COMP[CSR_DST[e]] == c) { ea[k] = loc[v]; eb[k] = loc[CSR_DST[e]]; k++; }
        }
        double r = perron(n, k, ea, eb);
        if (r > best) best = r;
        free(ea); free(eb);
    }
    free(loc);
    return best;
}

int main(int argc, char **argv)
{
    long long p = 3, q = 2, nun = 1, nud = 2, Dov = 0;
    int K = 2, k = 4, want_det = 0, summary = 0;
    char plist[128] = "2", pshow[128];
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--pq")) { p = atoll(argv[++i]); q = atoll(argv[++i]); }
        else if (!strcmp(argv[i], "--nu")) { char *t = argv[++i], *sl = strchr(t, '/');
            if (sl) { *sl = 0; nun = atoll(t); nud = atoll(sl + 1); }
            else { nun = atoll(t); nud = 1; } }
        else if (!strcmp(argv[i], "--P")) snprintf(plist, sizeof plist, "%s", argv[++i]);
        else if (!strcmp(argv[i], "--K")) K = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--k")) k = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--D")) Dov = atoll(argv[++i]);
        else if (!strcmp(argv[i], "--det")) want_det = 1;
        else if (!strcmp(argv[i], "--summary")) summary = 1;
        else { fprintf(stderr, "unknown arg %s\n", argv[i]); return 2; }
    }
    P_ = p; Q_ = q; NUN = nun; NUD = nud; K_ = K;
    { long long g = nun, b = nud; while (b) { long long t = g % b; g = b; b = t; }
      if (g > 1) { NUN /= g; NUD /= g; } if (NUN == 0) NUD = 1; }
    W_ = (P_ - Q_) * NUN;                    /* w = W_/NUD */
    NP = 0;
    snprintf(pshow, sizeof pshow, "%s", plist);
    { char *t = strtok(plist, ","); while (t) { PRIMES[NP++] = atoi(t); t = strtok(NULL, ","); } }
    AVOID_Q = 0; NQ = 0;
    for (int i = 0; i < NP; i++) {
        if (PRIMES[i] == Q_) AVOID_Q = 1;
        else if (Q_ % PRIMES[i] != 0) QL[NQ++] = PRIMES[i];
        else { fprintf(stderr, "prime %d divides q but != q\n", PRIMES[i]); return 2; }
    }
    /* alphabet: s such that Dom(s) n [0,1) is nonempty, i.e.
     *   -(p-q)nu - q < s < p - (p-q)nu   <=>  -W_ - q*NUD < s*NUD < p*NUD - W_ */
    SLO = 0; SHI = 0;
    { int found = 0;
      for (int s = -(int)(p + q + 4); s <= (int)(p + q + 4); s++) {
          long long lo = (long long)s * NUD + W_;
          long long hi = (long long)s * NUD + W_ + Q_ * NUD;
          long long dl = lo > 0 ? lo : 0, dh = hi < P_ * NUD ? hi : P_ * NUD;
          if (dl < dh) { if (!found) { SLO = s; found = 1; } SHI = s; } } }
    NS = SHI - SLO + 1;
    D_ = Dov ? Dov : P_ * NUD * ipow(Q_, k);
    if (D_ % (P_ * NUD)) { fprintf(stderr, "D must be a multiple of p*nud\n"); return 2; }
    QK = ipow(Q_, K);

    build_tables();
    build_graph();
    long long ce; long long cn = peel(&ce);
    compact();
    double lam = 0;
    int32_t sccs = 0, cyclic = 0, largest = 0, branch_nodes = 0, branch_sccs = 0;
    int all_simple = 1;
    long long det_states = 0; int det_rc = 0; double det_lam = 0;
    if (NC) {
        tarjan();
        sccs = NCOMP;
        int32_t *sz = xmalloc((size_t)NCOMP * sizeof(int32_t));
        int32_t *ei = xmalloc((size_t)NCOMP * sizeof(int32_t));
        memset(sz, 0, (size_t)NCOMP * sizeof(int32_t));
        memset(ei, 0, (size_t)NCOMP * sizeof(int32_t));
        for (int32_t v = 0; v < NC; v++) sz[COMP[v]]++;
        int32_t *odin = xmalloc((size_t)NC * sizeof(int32_t));
        memset(odin, 0, (size_t)NC * sizeof(int32_t));
        for (int32_t v = 0; v < NC; v++)
            for (int32_t e = CSR_OFF[v]; e < CSR_OFF[v + 1]; e++)
                if (COMP[CSR_DST[e]] == COMP[v]) { odin[v]++; ei[COMP[v]]++; }
        uint8_t *isb = xmalloc((size_t)NCOMP); memset(isb, 0, (size_t)NCOMP);
        for (int32_t v = 0; v < NC; v++) if (odin[v] >= 2) { branch_nodes++; isb[COMP[v]] = 1; }
        for (int32_t c = 0; c < NCOMP; c++) if (ei[c]) {
            cyclic++;
            if (sz[c] > largest) largest = sz[c];
            if (ei[c] != sz[c]) all_simple = 0;
            if (isb[c]) branch_sccs++;
        }
        lam = (branch_sccs == 0 && all_simple) ? 1.0 : core_rho(sz, ei);
        if (cyclic == 0) lam = 0.0;
        if (want_det) {
            int32_t *mem = xmalloc((size_t)NC * sizeof(int32_t));
            for (int32_t c = 0; c < NCOMP; c++) {
                if (!ei[c]) continue;
                int32_t nm = 0;
                for (int32_t v = 0; v < NC; v++) if (COMP[v] == c) mem[nm++] = v;
                int rc = det_component(c, mem, nm, &det_states, &det_lam);
                if (rc > det_rc) det_rc = rc;
            }
            free(mem);
        }
        free(sz); free(ei); free(odin); free(isb);
    }
    const char *verdict = !NC ? "EMPTY CORE"
                        : (branch_sccs == 0 && all_simple) ? "C(P) HOLDS" : "C(P) FAILS";
    const char *dv = !want_det ? "" : (!NC ? "EMPTY CORE"
                    : det_rc == 2 ? "CAP" : det_rc == 1 ? "C_det(P) FAILS" : "C_det(P) HOLDS");
    if (summary) {
        printf("{\"impl\": \"c\", \"p\": %lld, \"q\": %lld, \"nu\": \"%lld/%lld\", "
               "\"P\": \"%s\", \"K\": %d, \"k\": %d, \"D\": %lld, \"U\": %d, \"R\": %lld, "
               "\"nodes_total\": %lld, \"edges_total\": %lld, \"core_nodes\": %lld, "
               "\"core_edges\": %lld, \"sccs\": %d, \"cyclic_sccs\": %d, "
               "\"largest_cyclic\": %d, \"branch_nodes\": %d, \"branch_sccs\": %d, "
               "\"all_simple\": %s, \"lam\": %.12g, \"verdict\": \"%s\"",
               p, q, NUN, NUD, pshow, K, k, D_, NU_, NR, NV, NE, cn, ce, sccs, cyclic,
               largest, branch_nodes, branch_sccs, all_simple ? "true" : "false",
               lam, verdict);
        if (want_det) printf(", \"det_lam\": %.12g, \"det_states\": %lld, \"det_verdict\": \"%s\"",
                             det_lam, det_states, dv);
        printf("}\n");
    } else {
        printf("       p/q, nu : %lld/%lld, %lld/%lld\n", p, q, NUN, NUD);
        printf("        P, K, k : %s  K=%d k=%d  D=%lld\n", pshow, K, k, D_);
        printf("       alphabet : [%d..%d]   U=%d  R=%lld\n", SLO, SHI, NU_, NR);
        printf("    nodes/edges : %lld / %lld\n", NV, NE);
        printf("     core nodes : %lld   core edges: %lld\n", cn, ce);
        printf("           SCCs : %d   cyclic %d   largest cyclic %d\n", sccs, cyclic, largest);
        printf("       branding : nodes %d   SCCs %d   all_simple %d\n",
               branch_nodes, branch_sccs, all_simple);
        printf("         lambda : %.12g\n", lam);
        printf("        verdict : %s\n", verdict);
        if (want_det) printf("    det states/verdict : %lld  lam %.12g  %s\n", det_states, det_lam, dv);
    }
    return 0;
}
