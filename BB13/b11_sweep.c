/* (C) 2026 Ralf Stephan, in collaboration with Claude Code.
 * CC0 1.0 Universal (public domain dedication).
 *
 * B11 of plans/report3-BB13.html -- the incremental shift-and-add census sweep.
 *
 * State: A = 3^n mod 2^M held as NL 64-bit limbs, M = 64*NL.  The step is
 *
 *     A <- 3*A, discarding the carry out of the top limb,
 *
 * which is exactly reduction mod 2^M (BB13.CensusSweep.window_step).  From A we
 * read, at each n:
 *
 *     r = A mod 2^n = 3^n mod 2^n            (BB13.CensusSweep.resid_of_window)
 *     q = (A >> n) mod 2^64 = (3^n / 2^n) mod 2^64
 *     z = the number of equal bits of r at positions n-1, n-2, ...
 *         (so 2^{n-z-1} <= |k_n| < 2^{n-z}, and n is an exception iff
 *          z >= 0.41504*n up to one unit -- BB13.CensusSweep.filter_sound)
 *     w = v_2(m_n), m_n = q + [r > 2^{n-1}]  (BB13.CensusSweep.mNat_of_window)
 *
 * Everything but the multiply is O(1) per index, so the whole sweep to N costs
 * Theta(N^2) bit operations -- the point of the exercise.
 *
 * Build:  cc -O2 -march=native -o b11_sweep b11_sweep.c
 * Usage:  ./b11_sweep N [TOPK]        (writes a plain-text report to stdout)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef unsigned __int128 u128;

#define MAXW 96            /* histogram width for z and v2 */
#define CAND 4096          /* max exception candidates reported */

static uint64_t *A;
static long NL;

/* leading-equal-bit count of a 64-bit word, counted from the top */
static inline int lead_run(uint64_t hi) {
  return (hi >> 63) ? __builtin_clzll(~hi) : (hi ? __builtin_clzll(hi) : 64);
}

/* bits [p, p+width) of A as a width-bit word, right aligned (width <= 64) */
static inline uint64_t window(long p, int width) {
  long wl = p >> 6; int bo = p & 63;
  uint64_t v = A[wl] >> bo;
  if (bo) v |= A[wl + 1] << (64 - bo);
  return (width == 64) ? v : (v & ((1ULL << width) - 1));
}

/* leading-equal-bit count inside a width-bit word whose "expected" fill is
 * all-zero or all-one; the word is known to differ from the fill somewhere */
static inline int lead_run_w(uint64_t v, int width, uint64_t fill) {
  v <<= (64 - width);
  if (fill) v = ~v;
  return __builtin_clzll(v);
}

typedef struct { long n; int z; int w; long score; } Rec;

static Rec *topD, *topB;
static int nD, nB, TOPK;

static void push(Rec *heap, int *cnt, Rec r) {
  /* keep the TOPK largest by .score, simple insertion (TOPK is small) */
  if (*cnt < TOPK) { heap[(*cnt)++] = r; }
  else {
    int worst = 0;
    for (int i = 1; i < *cnt; i++) if (heap[i].score < heap[worst].score) worst = i;
    if (heap[worst].score < r.score) heap[worst] = r;
  }
}

static int cmprec(const void *a, const void *b) {
  const Rec *x = a, *y = b;
  if (x->score != y->score) return x->score < y->score ? 1 : -1;
  return x->n < y->n ? -1 : 1;
}

int main(int argc, char **argv) {
  long N = (argc > 1) ? atol(argv[1]) : 100000;
  TOPK = (argc > 2) ? atoi(argv[2]) : 40;

  NL = N / 64 + 6;
  A = calloc(NL, sizeof(uint64_t));
  if (!A) { fprintf(stderr, "alloc failed\n"); return 1; }
  topD = malloc(sizeof(Rec) * (TOPK + 2));
  topB = malloc(sizeof(Rec) * (TOPK + 2));
  nD = nB = 0;

  long histz[MAXW + 1], histw[MAXW + 1];
  memset(histz, 0, sizeof histz);
  memset(histw, 0, sizeof histw);

  long cand[CAND]; int ncand = 0;
  long zmaxn = 0, wmaxn = 0, bmaxn = 0;
  int zmax = -1, wmax = -1, bmax = -1;
  long zrec[MAXW + 1];              /* first n attaining z >= t */
  long wrec[MAXW + 1];
  for (int i = 0; i <= MAXW; i++) { zrec[i] = -1; wrec[i] = -1; }
  long deep64 = 0, wide64 = 0;      /* windows that overflowed 64 bits */
  long histp[MAXW + 1];             /* peak heights: v2 rises only from <= 1 (B8) */
  long histrun[MAXW + 1];           /* descent-run lengths from a peak */
  long joint[13][13];               /* joint (z, v2) census, both capped at 12 */
  memset(histp, 0, sizeof histp);
  memset(histrun, 0, sizeof histrun);
  memset(joint, 0, sizeof joint);
  int prevw = -1, runlen = 0, runtop = 0, exact1 = 0, crashed = 0;

  A[0] = 1;                         /* n = 0 */
  long top = 0;

  for (long n = 1; n <= N; n++) {
    /* A <- 3*A mod 2^M */
    uint64_t carry = 0;
    for (long i = 0; i <= top; i++) {
      u128 v = (u128)A[i] * 3 + carry;
      A[i] = (uint64_t)v;
      carry = (uint64_t)(v >> 64);
    }
    if (carry) { if (top + 1 < NL) { A[++top] = carry; } }

    /* window reads */
    uint64_t hi, q64;
    if (n >= 64) {
      long p = n - 64, wl = p >> 6; int bo = p & 63;
      hi = A[wl] >> bo;
      if (bo) hi |= A[wl + 1] << (64 - bo);
    } else {
      hi = (A[0] & ((n == 64) ? ~0ULL : ((1ULL << n) - 1))) << (64 - n);
    }
    { long wq = n >> 6; int bq = n & 63;
      q64 = A[wq] >> bq;
      if (bq) q64 |= A[wq + 1] << (64 - bq); }

    int z = lead_run(hi);
    if (z >= 64 && n > 64) {                     /* rare: scan further down */
      wide64++;
      uint64_t fill = (hi >> 63) ? ~0ULL : 0ULL;
      long p = n - 64;
      while (z < n) {
        long q = p - 64; if (q < 0) q = 0;
        int width = (int)(p - q);
        uint64_t nxt = window(q, width);
        if (nxt != (fill >> (64 - width))) { z += lead_run_w(nxt, width, fill); break; }
        z += width; p = q;
        if (p == 0) break;
      }
    }
    if (z > n) z = (int)n;

    uint64_t mlow = q64 + (hi >> 63);            /* m_n mod 2^64 */
    int w = mlow ? __builtin_ctzll(mlow) : 64;
    if (!mlow) {                                 /* rare: read the next 64 bits */
      deep64++;
      uint64_t q2 = window(n + 64, 64);
      uint64_t m2 = q2 + 1;                      /* the carry out of mlow == 0 */
      w = m2 ? 64 + __builtin_ctzll(m2) : 128;
    }

    /* peaks and descent runs: by BB13.vTwo_succ_lt the valuation can only rise
     * from height <= 1, so every n with v2 >= 2 either starts a run or continues
     * a strictly descending one. */
    if (prevw >= 0) {
      if (w >= 2 && prevw <= 1) { histp[w > MAXW ? MAXW : w]++; runtop = w; runlen = 1; }
      else if (runlen > 0 && w >= 2) { runlen++; if (prevw - w == 1) exact1++; else crashed++; }
      else if (runlen > 0) { histrun[runlen > MAXW ? MAXW : runlen]++; runlen = 0; }
    }
    prevw = w;
    if (z <= 12 && w <= 12) joint[z][w]++;

    histz[z > MAXW ? MAXW : z]++;
    histw[w > MAXW ? MAXW : w]++;
    if (z > zmax) { zmax = z; zmaxn = n; }
    if (w > wmax) { wmax = w; wmaxn = n; }
    if (z + w > bmax) { bmax = z + w; bmaxn = n; }
    for (int t = z > MAXW ? MAXW : z; t >= 0 && zrec[t] < 0; t--) zrec[t] = n;
    for (int t = w > MAXW ? MAXW : w; t >= 0 && wrec[t] < 0; t--) wrec[t] = n;

    /* D-arm leaderboard: score 41*z - 17*n  (17/41 < log2(4/3) < z/n iff exception) */
    Rec r1 = { n, z, w, 41L * z - 17L * n };
    push(topD, &nD, r1);
    Rec r2 = { n, z, w, (long)(z + w) };
    push(topB, &nB, r2);

    if (n == 10000 || n == 100000 || n == 1000000 || n == 10000000 || n == N) {
      printf("CHK %ld zmax %d at %ld ; wmax %d at %ld ; blockmax %d at %ld\n",
             n, zmax, zmaxn, wmax, wmaxn, bmax, bmaxn);
      printf("CHKZ %ld", n);
      { long acc = 0; for (int i = MAXW; i >= 1; i--) { acc += histz[i]; if (i <= 24) printf(" %d:%ld", i, acc); } }
      printf("\nCHKW %ld", n);
      { long acc = 0; for (int i = MAXW; i >= 1; i--) { acc += histw[i]; if (i <= 24) printf(" %d:%ld", i, acc); } }
      printf("\n");
      fflush(stdout);
    }

    /* exception candidates.  2^{n-z-1} <= |k_n| < 2^{n-z}, so |k_n| < (3/2)^n
     * forces n-z-1 < n*log2(3/2) < 24n/41, i.e. 41*(z+1) > 17*n.  Sound. */
    if (41L * (z + 1L) > 17L * n && ncand < CAND) cand[ncand++] = n;
  }

  qsort(topD, nD, sizeof(Rec), cmprec);
  qsort(topB, nB, sizeof(Rec), cmprec);

  printf("# b11_sweep N=%ld limbs=%ld\n", N, NL);
  printf("SUMMARY zmax %d at %ld ; wmax %d at %ld ; blockmax %d at %ld\n",
         zmax, zmaxn, wmax, wmaxn, bmax, bmaxn);
  printf("OVERFLOW wide64 %ld deep64 %ld\n", wide64, deep64);
  printf("HISTZ");
  for (int i = 0; i <= MAXW; i++) if (histz[i]) printf(" %d:%ld", i, histz[i]);
  printf("\nHISTW");
  for (int i = 0; i <= MAXW; i++) if (histw[i]) printf(" %d:%ld", i, histw[i]);
  printf("\nZREC");
  for (int i = 0; i <= MAXW; i++) if (zrec[i] > 0) printf(" %d:%ld", i, zrec[i]);
  printf("\nWREC");
  for (int i = 0; i <= MAXW; i++) if (wrec[i] > 0) printf(" %d:%ld", i, wrec[i]);
  printf("\nHISTP");
  for (int i = 0; i <= MAXW; i++) if (histp[i]) printf(" %d:%ld", i, histp[i]);
  printf("\nHISTRUN");
  for (int i = 0; i <= MAXW; i++) if (histrun[i]) printf(" %d:%ld", i, histrun[i]);
  printf("\nSTEPS exact1 %d crashed %d lastruntop %d\n", exact1, crashed, runtop);
  for (int i = 0; i <= 12; i++) {
    printf("JOINT %d", i);
    for (int j = 0; j <= 12; j++) printf(" %ld", joint[i][j]);
    printf("\n");
  }
  printf("CAND %d", ncand);
  for (int i = 0; i < ncand; i++) printf(" %ld", cand[i]);
  printf("\n");
  for (int i = 0; i < nD; i++)
    printf("TOPD %ld z=%d w=%d score=%ld\n", topD[i].n, topD[i].z, topD[i].w, topD[i].score);
  for (int i = 0; i < nB; i++)
    printf("TOPB %ld z=%d w=%d block=%ld\n", topB[i].n, topB[i].z, topB[i].w, topB[i].score);
  return 0;
}
