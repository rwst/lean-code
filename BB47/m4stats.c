/* (C) 2026 Ralf Stephan, in collaboration with Claude Code. Released under CC0 1.0 Universal.
 *
 * M4 (plan-1047): recurrent-block statistics of b-ary expansions.
 *
 * Input : a file of N bytes, one base-b digit (raw value 0..b-1) per byte.
 * Output: TSV on stdout.  Row kinds
 *   CERT  n C g              horizon certificate: C = max i such that w[i..N] carries
 *                            >= n+2 distinct n-blocks; g = N-C = its "reach".
 *   BAL   n C v              balance certificate: C = max i such that the v-indicator of
 *                            w[i..N] has two n-windows of weight differing by >= 2,
 *                            minimised over the digit v (0 if no v qualifies).
 *   EXACT n p bn lmin q01 q10 q50 revok self a50 a90 a99 a999
 *                            exact last-occurrence statistics (only while b^n fits the cap):
 *                            p = #distinct n-blocks, bn = b^n, lmin = min over blocks of the
 *                            last-occurrence position (so ALL b^n blocks occur in w[lmin..N]),
 *                            qXX = the XX-th percentile of the last-occurrence distribution
 *                            (= the horizon certificate at level K = (1-XX/100)*p),
 *                            revok = #blocks whose reversal also occurs, self = #palindromes,
 *                            aXX = #blocks still occurring in the last (100-XX)% of w.
 *   REP   n r                r(n) = length of the shortest prefix carrying two occurrences
 *                            of some n-block  ([BK19] Thm. 10.4); -1 if not found in range.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <omp.h>

static const uint8_t *W;      /* w_1..w_N at W[0..N-1] */
static long long N;
static int B;                 /* base */

/* ---------- tiny open-addressing set for the certificate scans ---------- */
#define SCAP 1024
static inline int sins(uint64_t *t, uint64_t k) { /* returns 1 if newly inserted */
    uint64_t h = (k * 0x9E3779B97F4A7C15ull) >> 54, i = h & (SCAP - 1);
    for (;;) {
        if (t[i] == 0) { t[i] = k + 1; return 1; }
        if (t[i] == k + 1) return 0;
        i = (i + 1) & (SCAP - 1);
    }
}

/* max i in [1, N-n+1] such that positions i..N-n+1 carry >= K+1 distinct n-blocks; 0 if none */
static long long cert(int n, long long K)
{
    if (N < n) return 0;
    uint64_t pw = 1; for (int k = 1; k < n; k++) pw *= (uint64_t)B;   /* b^(n-1) */
    long long i0 = N - n + 1;
    uint64_t code = 0;
    for (int k = 0; k < n; k++) code = code * (uint64_t)B + W[i0 - 1 + k];
    uint64_t *t = calloc(SCAP, sizeof(uint64_t));
    long long cnt = sins(t, code), res = 0;
    if (cnt >= K + 1) { free(t); return i0; }
    for (long long i = i0 - 1; i >= 1; i--) {
        code = (uint64_t)W[i - 1] * pw + (code - W[i + n - 1]) / (uint64_t)B;
        cnt += sins(t, code);
        if (cnt >= K + 1) { res = i; break; }
        if (cnt >= SCAP / 2) break;                                   /* set full: give up */
    }
    free(t);
    return res;
}

/* max i such that the v-indicator of w[i..N] has two n-windows with weights differing by >=2 */
static long long balcert(int n, int v)
{
    if (N < n) return 0;
    long long i0 = N - n + 1, wt = 0;
    for (int k = 0; k < n; k++) wt += (W[i0 - 1 + k] == v);
    long long mx = wt, mn = wt;
    for (long long i = i0 - 1; i >= 1; i--) {
        wt += (W[i - 1] == v) - (W[i + n - 1] == v);
        if (wt > mx) mx = wt;
        if (wt < mn) mn = wt;
        if (mx - mn >= 2) return i;
    }
    return 0;
}

/* ---------- r(n) : shortest prefix with a repeated n-block ---------- */
#define RBITS 26
#define RCAP  (1ull << RBITS)
static long long repfun(int n, long long scancap, uint64_t *t)
{
    if (N < n) return -1;
    memset(t, 0, RCAP * sizeof(uint64_t));
    uint64_t mask_pw = 1; for (int k = 0; k < n; k++) mask_pw *= (uint64_t)B;  /* b^n */
    uint64_t code = 0;
    long long lim = N - n + 1; if (lim > scancap) lim = scancap;
    long long nin = 0;
    for (long long i = 1; i <= lim; i++) {
        if (i == 1) { for (int k = 0; k < n; k++) code = code * (uint64_t)B + W[k]; }
        else        { code = (code * (uint64_t)B + W[i + n - 2]) % mask_pw; }
        uint64_t h = (code * 0x9E3779B97F4A7C15ull) >> (64 - RBITS), j = h;
        for (;;) {
            if (t[j] == 0) { t[j] = code + 1; nin++; break; }
            if (t[j] == code + 1) return i + n - 1;        /* prefix length */
            j = (j + 1) & (RCAP - 1);
        }
        if (nin > (long long)(RCAP / 2)) return -1;
    }
    return -1;
}

/* ---------- exact last-occurrence table ---------- */
static uint64_t revcode(uint64_t u, int n, const uint64_t *pw)
{
    uint64_t r = 0;
    for (int k = 0; k < n; k++) { r += (u % B) * pw[n - 1 - k]; u /= B; }
    return r;
}

int main(int argc, char **argv)
{
    if (argc < 6) { fprintf(stderr, "usage: %s file base nexact ncert tag [threads]\n", argv[0]); return 1; }
    const char *fn = argv[1];
    B = atoi(argv[2]);
    int nexact = atoi(argv[3]), ncert = atoi(argv[4]);
    const char *tag = argv[5];
    int nth = argc > 6 ? atoi(argv[6]) : 6;

    int fd = open(fn, O_RDONLY);
    if (fd < 0) { perror(fn); return 1; }
    struct stat st; fstat(fd, &st); N = st.st_size;
    W = mmap(NULL, N, PROT_READ, MAP_SHARED, fd, 0);
    if (W == MAP_FAILED) { perror("mmap"); return 1; }
    madvise((void *)W, N, MADV_WILLNEED);
    printf("# %s file=%s base=%d N=%lld\n", tag, fn, B, N);

    /* --- certificates (cheap, all n) --- */
    #pragma omp parallel for schedule(dynamic) num_threads(nth)
    for (int n = 1; n <= ncert; n++) {
        long long c = cert(n, n + 1);
        long long bc = -1;
        for (int v = 0; v < B; v++) { long long x = balcert(n, v); if (bc < 0 || x < bc) bc = x; }
        #pragma omp critical
        { printf("CERT\t%s\t%d\t%lld\t%lld\n", tag, n, c, N - c);
          printf("BAL\t%s\t%d\t%lld\t%lld\n", tag, n, bc, N - bc); }
    }
    fflush(stdout);

    /* --- r(n) --- */
    #pragma omp parallel num_threads(nth < 4 ? nth : 4)
    {
        uint64_t *t = malloc(RCAP * sizeof(uint64_t));
        #pragma omp for schedule(dynamic)
        for (int n = 1; n <= ncert; n++) {
            long long r = repfun(n, 40000000LL, t);
            #pragma omp critical
            printf("REP\t%s\t%d\t%lld\n", tag, n, r);
        }
        free(t);
    }
    fflush(stdout);

    /* --- exact last-occurrence tables --- */
    #pragma omp parallel for schedule(dynamic) num_threads(nth)
    for (int n = nexact; n >= 1; n--) {
        uint64_t sz = 1; for (int k = 0; k < n; k++) sz *= (uint64_t)B;
        uint32_t *last = calloc(sz, sizeof(uint32_t));
        if (!last) { fprintf(stderr, "alloc fail n=%d\n", n); continue; }
        uint64_t code = 0, bn = sz;
        for (int k = 0; k < n - 1; k++) code = code * (uint64_t)B + W[k];
        for (long long i = 1; i <= N - n + 1; i++) {
            code = (code * (uint64_t)B + W[i + n - 2]) % bn;
            last[code] = (uint32_t)i;
        }
        uint64_t pw[64]; pw[0] = 1; for (int k = 1; k < n; k++) pw[k] = pw[k - 1] * (uint64_t)B;
        uint64_t p = 0, revok = 0, self = 0; uint32_t lmin = 0xFFFFFFFFu;
        /* histogram of last-occurrence, 1<<20 buckets */
        long long *hist = calloc(1 << 20, sizeof(long long));
        long long alive[4] = {0,0,0,0};
        long long thr[4] = { N/2, N-N/10, N-N/100, N-N/1000 };
        double scale = (double)(1 << 20) / (double)(N + 1);
        for (uint64_t u = 0; u < sz; u++) {
            if (!last[u]) continue;
            p++; if (last[u] < lmin) lmin = last[u];
            hist[(long long)(last[u] * scale)]++;
            uint64_t r = revcode(u, n, pw);
            if (r == u) self++;
            if (last[r]) revok++;
            for (int j = 0; j < 4; j++) if ((long long)last[u] >= thr[j]) alive[j]++;
        }
        /* quantiles of last-occurrence (bucket resolution) */
        long long want[3] = { (long long)(p / 100), (long long)(p / 10), (long long)(p / 2) };
        long long acc = 0, q[3] = { -1, -1, -1 };
        for (long long h = 0; h < (1 << 20); h++) {
            acc += hist[h];
            for (int j = 0; j < 3; j++) if (q[j] < 0 && acc > want[j]) q[j] = (long long)(h / scale);
        }
        free(hist);
        #pragma omp critical
        printf("EXACT\t%s\t%d\t%llu\t%llu\t%u\t%lld\t%lld\t%lld\t%llu\t%llu\t%lld\t%lld\t%lld\t%lld\n",
               tag, n, (unsigned long long)p, (unsigned long long)sz, p ? lmin : 0,
               q[0], q[1], q[2], (unsigned long long)revok, (unsigned long long)self,
               alive[0], alive[1], alive[2], alive[3]);
        free(last);
    }
    return 0;
}
