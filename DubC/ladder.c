/* (C) Ralf Stephan, in collaboration with Claude Code.  CC0 / public domain.
 *
 * X2' (plan-dubC1 §0-ter N1) — incremental certificate ladder for the
 * coprimality subshift of [xi 7^n].  See subshift.c for the model; this file
 * computes the same objects but climbs the ladder y = 7, 11, 13, ... one
 * prime at a time, which is what makes y >= 29 cheap.
 *
 * Key observation.  Write core(Q) for the pruning fixpoint of the subshift
 * over Q = {p <= y} \ {2,7}, i.e. the set of states lying on a bi-infinite
 * admissible path.  Adjoining one more prime p gives the state space
 * S(Q u {p}) = S(Q) x (Z/p)^*, and admissibility is the CONJUNCTION of the
 * old condition and the new coordinate's.  Projecting a bi-infinite path
 * therefore gives a bi-infinite path, so
 *
 *          core(Q u {p})  subset  core(Q) x (Z/p)^* ,
 *
 * and moreover every edge used is an edge of the core(Q) subgraph.  So the
 * next rung can be built from the previous CORE rather than from the full
 * product: at y=23 that is 3.6e5 * 28 = 1.0e7 candidates instead of the
 * 1.7e8 states of the full y=29 space, and the saving compounds.
 *
 * Per rung: prune (two bitsets, no explicit predecessor table), compact,
 * Tarjan, C(P) verdict, power iteration + Collatz-Wielandt bracket,
 * explicit two-cycle witness.
 *
 * Build:  gcc -O3 -march=native -fopenmp -o ladder ladder.c -lm
 * Run:    ./ladder <ymax> [powerits]
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BASE 7
#define NDIG 3
static const int DIG[NDIG] = {2, 4, 6};

static int isprime(int n){ for(long d=2;d*d<=n;d++) if(n%d==0) return 0; return n>=2; }
static double wall(void){ struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t);
                          return t.tv_sec + 1e-9*t.tv_nsec; }

/* ------------------------------------------------------------------ */
/* a rung: n core states, succ[NDIG*c+t] = successor under digit DIG[t] */

static long long n_cur;
static int32_t *succ_cur;
static int32_t *par_c;      /* provenance: parent core id at previous rung  */
static int16_t *par_u;      /* provenance: residue mod the newly added prime */

static uint64_t *A, *B;     /* work bitsets over the product space          */
static long long mbits, mwords;

static inline int gb(const uint64_t *b, long long i){ return (b[i>>6]>>(i&63))&1ULL; }
static inline void sb(uint64_t *b, long long i){ b[i>>6] |= 1ULL<<(i&63); }
static inline void cb(uint64_t *b, long long i){ b[i>>6] &= ~(1ULL<<(i&63)); }
static inline void sb_at(uint64_t *b, long long i)
{ __atomic_fetch_or(&b[i>>6], 1ULL<<(i&63), __ATOMIC_RELAXED); }
static inline void cb_at(uint64_t *b, long long i)
{ __atomic_fetch_and(&b[i>>6], ~(1ULL<<(i&63)), __ATOMIC_RELAXED); }

static long long pop(const uint64_t *b)
{ long long c=0;
#pragma omp parallel for reduction(+:c) schedule(static)
  for (long long w=0; w<mwords; w++) c += __builtin_popcountll(b[w]);
  return c; }

/* ------------------------------------------------------------------ */
/* Tarjan (iterative), power iteration, witness — on the compacted rung  */

static int32_t *comp; static int32_t ncomp;

static void tarjan(long long n, const int32_t *succ)
{
    int32_t *num=malloc(4*n), *low=malloc(4*n), *stk=malloc(4*n);
    uint8_t *ons=calloc(n,1);
    int32_t *dn=malloc(4*n); int8_t *dc=malloc(n);
    comp=malloc(4*n);
    for (long long i=0;i<n;i++){ num[i]=-1; comp[i]=-1; }
    int32_t counter=0, sp=0; ncomp=0;
    for (long long root=0; root<n; root++) {
        if (num[root]>=0) continue;
        long long dsp=0; dn[0]=(int32_t)root; dc[0]=0;
        num[root]=low[root]=counter++; stk[sp++]=(int32_t)root; ons[root]=1;
        while (dsp>=0) {
            int32_t v=dn[dsp];
            if (dc[dsp]<NDIG) {
                int32_t w=succ[NDIG*(long long)v+dc[dsp]]; dc[dsp]++;
                if (w<0) continue;
                if (num[w]<0){ num[w]=low[w]=counter++; stk[sp++]=w; ons[w]=1;
                               dsp++; dn[dsp]=w; dc[dsp]=0; }
                else if (ons[w] && num[w]<low[v]) low[v]=num[w];
            } else {
                if (low[v]==num[v]) { int32_t w;
                    do { w=stk[--sp]; ons[w]=0; comp[w]=ncomp; } while (w!=v);
                    ncomp++; }
                dsp--;
                if (dsp>=0 && low[v]<low[dn[dsp]]) low[dn[dsp]]=low[v];
            }
        }
    }
    free(num);free(low);free(stk);free(ons);free(dn);free(dc);
}

static double power_iter(long long n, const int32_t *succ, const uint8_t *in,
                         long long nin, int iters, double *lo_o, double *hi_o)
{
    double *v=malloc(8*n), *w=malloc(8*n);
#pragma omp parallel for schedule(static)
    for (long long i=0;i<n;i++) v[i] = (!in || in[i]) ? 1.0 : 0.0;
    double lam=0, lo=0, hi=0;
    for (int it=0; it<iters; it++) {
        double s=0, sv=0;
#pragma omp parallel for reduction(+:s,sv) schedule(static)
        for (long long i=0;i<n;i++) {
            if (in && !in[i]) { w[i]=0; continue; }
            double a=0;
            for (int t=0;t<NDIG;t++){ int32_t j=succ[NDIG*i+t];
                if (j>=0 && (!in || in[j])) a+=v[j]; }
            w[i]=a; s+=a; sv+=v[i];
        }
        if (s==0){ lam=0; break; }
        lam=s/sv;
        lo=1e300; hi=0;
#pragma omp parallel for reduction(min:lo) reduction(max:hi) schedule(static)
        for (long long i=0;i<n;i++){ if ((in&&!in[i])||v[i]<=0) continue;
            double q=w[i]/v[i]; if(q<lo) lo=q; if(q>hi) hi=q; }
        double sc = (double)(in?nin:n)/s;
#pragma omp parallel for schedule(static)
        for (long long i=0;i<n;i++) v[i]=w[i]*sc;
    }
    if(lo_o)*lo_o=lo; if(hi_o)*hi_o=hi;
    free(v); free(w); return lam;
}

/* shortest cycle s -> s inside SCC cid whose first edge is slot `slot` */
static int cycle_via(long long n, const int32_t *succ, int32_t s, int slot,
                     int32_t cid, int8_t *outd, int *len)
{
    int32_t first = succ[NDIG*(long long)s+slot];
    if (first<0 || comp[first]!=cid) return 0;
    int32_t *par=malloc(4*n), *q=malloc(4*n); int8_t *pd=malloc(n);
    for (long long i=0;i<n;i++) par[i]=-2;
    long long head=0, tail=0;
    par[first]=s; pd[first]=(int8_t)DIG[slot]; q[tail++]=first;
    int found = (first==s);
    while (!found && head<tail) {
        int32_t v=q[head++];
        for (int k=0;k<NDIG;k++){ int32_t u=succ[NDIG*(long long)v+k];
            if (u<0||comp[u]!=cid||par[u]!=-2) continue;
            par[u]=v; pd[u]=(int8_t)DIG[k];
            if (u==s){ found=1; break; }
            q[tail++]=u; }
    }
    int ok=0;
    if (found) {
        int8_t tmp[8192]; int L=0; int32_t cur=s;
        while (1){ tmp[L++]=pd[cur]; if (cur==first) break; cur=par[cur];
                   if (L>8000) { L=0; break; } }
        if (L){ for(int i=0;i<L;i++) outd[i]=tmp[L-1-i]; *len=L; ok=1; }
    }
    free(par);free(q);free(pd);
    return ok;
}

/* ------------------------------------------------------------------ */

int main(int argc, char **argv)
{
    int ymax = (argc>1)?atoi(argv[1]):31;
    int iters = (argc>2)?atoi(argv[2]):4000;
    int dumpy = (argc>3)?atoi(argv[3]):-1;   /* dump core edge list at this y */

    /* rung 0: Q = {} — no constraints, one state, all three digits loop */
    n_cur = 1;
    succ_cur = malloc(4*NDIG);
    for (int t=0;t<NDIG;t++) succ_cur[t]=0;
    par_c = NULL; par_u = NULL;

    long long prodQ = 1;
    printf("# X2' ladder for [xi 7^n]; digits {2,4,6}; Q = primes <= y minus {2,7}\n");

    for (int p=3; p<=ymax; p++) {
        if (!isprime(p) || p==BASE) continue;
        double t0=wall();
        long long u_n = p-1;
        long long m = n_cur * u_n;
        prodQ *= p;
        /* P = {2,7} u Q; for p>=5 this is exactly {primes <= p} (p=5 -> y=7) */
        int y_eff = (p < 7) ? 7 : p;

        mbits = m; mwords = (m+63)/64;
        A = malloc(8*mwords); B = malloc(8*mwords);
        memset(A,0xFF,8*mwords);
        if (m&63) A[mwords-1] = (1ULL<<(m&63))-1;

        /* ---- prune to the bi-infinite-path fixpoint ---- */
        int rounds=0;
        for (;;) {
            long long killed=0;
            /* forward: need a live successor */
#pragma omp parallel for reduction(+:killed) schedule(dynamic,4096)
            for (long long c=0;c<n_cur;c++) {
                int32_t cs[NDIG];
                for (int t=0;t<NDIG;t++) cs[t]=succ_cur[NDIG*c+t];
                for (long long u=1;u<p;u++) {
                    long long idx=c*u_n+(u-1);
                    if (!gb(A,idx)) continue;
                    int ok=0;
                    for (int t=0;t<NDIG && !ok;t++) {
                        if (cs[t]<0) continue;
                        long long v=(BASE*u+DIG[t])%p;
                        if (v==0) continue;
                        if (gb(A,(long long)cs[t]*u_n+(v-1))) ok=1;
                    }
                    if (!ok){ cb_at(A,idx); killed++; }
                }
            }
            /* backward: need a live predecessor — computed by marking */
            memset(B,0,8*mwords);
#pragma omp parallel for schedule(dynamic,4096)
            for (long long c=0;c<n_cur;c++) {
                int32_t cs[NDIG];
                for (int t=0;t<NDIG;t++) cs[t]=succ_cur[NDIG*c+t];
                for (long long u=1;u<p;u++) {
                    long long idx=c*u_n+(u-1);
                    if (!gb(A,idx)) continue;
                    for (int t=0;t<NDIG;t++) {
                        if (cs[t]<0) continue;
                        long long v=(BASE*u+DIG[t])%p;
                        if (v==0) continue;
                        long long j=(long long)cs[t]*u_n+(v-1);
                        if (gb(A,j)) sb_at(B,j);
                    }
                }
            }
#pragma omp parallel for reduction(+:killed) schedule(static)
            for (long long w=0;w<mwords;w++) {
                uint64_t dead = A[w] & ~B[w];
                if (dead) { killed += __builtin_popcountll(dead); A[w] &= B[w]; }
            }
            rounds++;
            if (!killed) break;
        }
        long long ncore = pop(A);

        /* ---- compact ---- */
        uint64_t *rankw = malloc(8*(mwords+1));
        { uint64_t acc=0; for (long long w=0;w<mwords;w++){ rankw[w]=acc; acc+=__builtin_popcountll(A[w]); } rankw[mwords]=acc; }
        int32_t *ncc = malloc(4*(ncore?ncore:1));      /* new -> parent core id */
        int16_t *ncu = malloc(2*(ncore?ncore:1));      /* new -> residue mod p  */
#pragma omp parallel for schedule(static)
        for (long long w=0;w<mwords;w++) {
            uint64_t x=A[w]; long long k=(long long)rankw[w];
            while (x){ int b=__builtin_ctzll(x); long long idx=(w<<6)+b;
                       ncc[k]=(int32_t)(idx/u_n); ncu[k]=(int16_t)(idx%u_n+1); k++; x&=x-1; }
        }
        int32_t *nsucc = malloc(4*NDIG*(ncore?ncore:1));
#pragma omp parallel for schedule(static)
        for (long long k=0;k<ncore;k++) {
            long long c=ncc[k], u=ncu[k];
            for (int t=0;t<NDIG;t++) {
                int32_t cs=succ_cur[NDIG*c+t]; nsucc[NDIG*k+t]=-1;
                if (cs<0) continue;
                long long v=(BASE*u+DIG[t])%p;
                if (v==0) continue;
                long long j=(long long)cs*u_n+(v-1);
                if (!gb(A,j)) continue;
                uint64_t wd=A[j>>6]; uint64_t mk=(j&63)?((1ULL<<(j&63))-1):0ULL;
                nsucc[NDIG*k+t]=(int32_t)(rankw[j>>6]+__builtin_popcountll(wd&mk));
            }
        }
        free(rankw); free(A); free(B);

        /* ---- analyse the rung ---- */
        printf("\nP = {2,7} u Q, Q ends at %d  (y = %d)   product %lld  ->  core %lld"
               "  (%.4f%%, %d rounds, %.1fs)\n",
               p, y_eff, m, ncore, 100.0*ncore/m, rounds, wall()-t0);
        if (ncore==0) {
            printf("  CORE EMPTY: lambda = 0 -> {p<=%d} IS AN UNAVOIDABLE DIVISOR SET for a=7.\n", y_eff);
            free(succ_cur); succ_cur=nsucc; n_cur=0; break;
        }
        long long hist[NDIG+1]={0};
        for (long long k=0;k<ncore;k++){ int d=0;
            for(int t=0;t<NDIG;t++) if(nsucc[NDIG*k+t]>=0) d++; hist[d]++; }
        printf("  out-degrees: "); for(int d=0;d<=NDIG;d++) printf("%d:%lld ",d,hist[d]); printf("\n");

        if (y_eff == dumpy) {
            char fn[64]; snprintf(fn, sizeof fn, "core_y%d.txt", y_eff);
            FILE *f = fopen(fn, "w");
            fprintf(f, "%lld\n", ncore);
            for (long long k=0;k<ncore;k++)
                for (int t=0;t<NDIG;t++) if (nsucc[NDIG*k+t]>=0)
                    fprintf(f, "%lld %d\n", k, nsucc[NDIG*k+t]);
            fclose(f);
            printf("  [dumped core edge list to %s]\n", fn);
        }

        tarjan(ncore, nsucc);
        long long *csz=calloc(ncomp,8); char *cbr=calloc(ncomp,1), *ccy=calloc(ncomp,1);
        for (long long k=0;k<ncore;k++){
            csz[comp[k]]++; int ins=0;
            for(int t=0;t<NDIG;t++){ int32_t j=nsucc[NDIG*k+t];
                if (j>=0 && comp[j]==comp[k]) ins++; }
            if (ins>=1) ccy[comp[k]]=1;
            if (ins>=2) cbr[comp[k]]=1;
        }
        long long ncyc=0,nbr=0,big=0; int32_t argbig=-1,argbr=-1;
        for (int32_t k=0;k<ncomp;k++){ if(ccy[k]) ncyc++;
            if(cbr[k]){ nbr++; if(argbr<0) argbr=k; }
            if(ccy[k]&&csz[k]>big){ big=csz[k]; argbig=k; } }
        printf("  SCCs %d, cyclic %lld, branching %lld, largest cyclic %lld\n",
               ncomp, ncyc, nbr, big);

        double lo,hi;
        double lam = power_iter(ncore, nsucc, NULL, ncore, iters, &lo, &hi);
        /* first moment lbar = 7 * prod_{q in P}(1-1/q), P = {2,7} u Q */
        double lbar = BASE * 0.5 * (1.0 - 1.0/BASE);
        for (int q=3;q<=p;q++) if (isprime(q) && q!=BASE) lbar *= 1.0 - 1.0/q;
        printf("  lambda = %.9f   dim = %.9f   lbar = %.6f   ratio = %.4f\n",
               lam, lam>0?log(lam)/log((double)BASE):0.0, lbar, lam/lbar);
        if (argbig>=0) {
            uint8_t *in=calloc(ncore,1); long long nin=0;
            for (long long k=0;k<ncore;k++) if(comp[k]==argbig){ in[k]=1; nin++; }
            double l2,h2; double lb=power_iter(ncore,nsucc,in,nin,iters,&l2,&h2);
            printf("  dominant SCC %lld states: lambda = %.9f  CW bracket [%.9f, %.9f]\n",
                   nin, lb, l2, h2);
            free(in);
        }
        printf("  C(P): %s\n", nbr==0 ? "HOLDS  ==>  every P-avoiding xi is rational  ==>  a=7 SOLVED"
                                      : "FAILS (positive entropy survives)");
        if (nbr>0) {
            int32_t s=-1; int s1=-1,s2=-1;
            for (long long k=0;k<ncore && s<0;k++){
                if (comp[k]!=argbr) continue;
                int f=-1;
                for(int t=0;t<NDIG;t++){ int32_t j=nsucc[NDIG*k+t];
                    if (j>=0&&comp[j]==comp[k]) { if(f<0) f=t; else { s=(int32_t)k; s1=f; s2=t; } } }
            }
            if (s>=0) {
                int8_t d1[8192],d2[8192]; int L1=0,L2=0;
                int o1=cycle_via(ncore,nsucc,s,s1,argbr,d1,&L1);
                int o2=cycle_via(ncore,nsucc,s,s2,argbr,d2,&L2);
                if (o1&&o2) {
                    printf("  witness: two distinct cycles through one state, lengths %d and %d\n",L1,L2);
                    printf("    A:"); for(int i=0;i<L1&&i<40;i++) printf(" %d",d1[i]);
                    printf("%s\n", L1>40?" ...":"");
                    printf("    B:"); for(int i=0;i<L2&&i<40;i++) printf(" %d",d2[i]);
                    printf("%s\n", L2>40?" ...":"");
                    printf("    => {A,B}^infty gives uncountably many aperiodic avoiders, "
                           "h_top >= log2/%d\n", L1>L2?L1:L2);
                }
            }
        }
        free(csz);free(cbr);free(ccy);free(comp);

        free(succ_cur); free(par_c); free(par_u);
        succ_cur=nsucc; n_cur=ncore; par_c=ncc; par_u=ncu;
        fflush(stdout);
    }
    return 0;
}
