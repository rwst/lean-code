/*
 * (C) 2026 Ralf Stephan, in collaboration with Claude Code.
 * Released under CC0 1.0 Universal (public-domain dedication).
 *
 * horizon.c -- M6 numerics for plans/plan-EVGQ17-M0.html (gate G-1).
 *
 * Map U(x) = floor(3x/2) + 1 = x + (x >> 1) + 1.  Letter i of seed n is
 * U^i(n) mod 2.  For seeds n = N0 + r, 0 <= r < 2^j, and letters i < K,
 * the program accumulates exact integer statistics:
 *
 *   odd[i]      #{r : letter i odd}               -> beta_j = odd[j] - 2^(j-1)
 *   sD[k],sD2[k]  sum of D_k, D_k^2, D_k = 2 S_k - k, S_k = #odd letters < k
 *   tail[k]     #{r : |D_k| > 0.3 k}  (i.e. |S_k - k/2| > 0.15 k)
 *   xr[d][i]    #{r : letter i != letter i+d}, d = 1..3 (pair correlations)
 *   blk[w]      histogram of the 8-letter block at positions j..j+7
 *   pair        sum over r < 2^(j-1) with letter j-1 == [j odd] of (2 b_j - 1)
 *               (the pairing identity of plan section 3.2 predicts pair == beta_j)
 *
 * Arithmetic is mod 2^128 (unsigned __int128).  U(x) mod 2^(a-1) depends only on
 * x mod 2^a, so after i steps U^i(n) is correct mod 2^(128-i); letters are exact
 * for i < 128.  Hence K <= 120.
 *
 * Usage: horizon j K [N0] [threads]      (output: one JSON object on stdout)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <omp.h>

typedef unsigned __int128 u128;
#define KMAX 120

static u128 parse_u128(const char *s) {
  u128 v = 0;
  for (; *s; s++) v = v * 10 + (u128)(*s - '0');
  return v;
}

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: horizon j K [N0] [threads]\n"); return 1; }
  int j = atoi(argv[1]), K = atoi(argv[2]);
  const char *n0s = argc > 3 ? argv[3] : "0";
  u128 N0 = parse_u128(n0s);
  int th = argc > 4 ? atoi(argv[4]) : 4;
  if (j < 1 || j > 40 || K < 1 || K > KMAX || j + 8 > K) { fprintf(stderr, "bad j/K\n"); return 1; }
  omp_set_num_threads(th);
  uint64_t R = 1ULL << j, half = R >> 1;

  int64_t odd[KMAX] = {0}, sD[KMAX + 1] = {0}, tail[KMAX + 1] = {0}, xr[4][KMAX] = {{0}};
  double sD2[KMAX + 1] = {0};
  int64_t blk[256] = {0}, pair = 0;

#pragma omp parallel
  {
    int64_t l_odd[KMAX] = {0}, l_sD[KMAX + 1] = {0}, l_tail[KMAX + 1] = {0}, l_xr[4][KMAX] = {{0}};
    double l_sD2[KMAX + 1] = {0};
    int64_t l_blk[256] = {0}, l_pair = 0;
    unsigned char b[KMAX];
#pragma omp for schedule(static)
    for (uint64_t r = 0; r < R; r++) {
      u128 x = N0 + (u128)r;
      int S = 0;
      for (int i = 0; i < K; i++) {
        int bi = (int)(x & 1);
        b[i] = (unsigned char)bi;
        S += bi;
        x = x + (x >> 1) + 1;
        int k = i + 1, D = 2 * S - k;
        l_sD[k] += D;
        l_sD2[k] += (double)D * D;
        if (10 * (int64_t)(D < 0 ? -D : D) > 3 * k) l_tail[k]++;
      }
      for (int i = 0; i < K; i++) {
        l_odd[i] += b[i];
        for (int d = 1; d <= 3 && i + d < K; d++) l_xr[d][i] += b[i] ^ b[i + d];
      }
      int w = 0;
      for (int t = 0; t < 8; t++) w = (w << 1) | b[j + t];
      l_blk[w]++;
      if (r < half && b[j - 1] == (j & 1)) l_pair += 2 * b[j] - 1;
    }
#pragma omp critical
    {
      for (int i = 0; i < K; i++) { odd[i] += l_odd[i]; for (int d = 1; d <= 3; d++) xr[d][i] += l_xr[d][i]; }
      for (int k = 0; k <= K; k++) { sD[k] += l_sD[k]; sD2[k] += l_sD2[k]; tail[k] += l_tail[k]; }
      for (int w = 0; w < 256; w++) blk[w] += l_blk[w];
      pair += l_pair;
    }
  }

  printf("{\"j\":%d,\"K\":%d,\"N0\":\"%s\",\"seeds\":%llu,\n", j, K, n0s, (unsigned long long)R);
  printf("\"beta\":%lld,\"pair\":%lld,\n", (long long)(odd[j] - (int64_t)half), (long long)pair);
  printf("\"odd\":["); for (int i = 0; i < K; i++) printf("%s%lld", i ? "," : "", (long long)odd[i]); printf("],\n");
  printf("\"sD\":["); for (int k = 0; k <= K; k++) printf("%s%lld", k ? "," : "", (long long)sD[k]); printf("],\n");
  printf("\"sD2\":["); for (int k = 0; k <= K; k++) printf("%s%.0f", k ? "," : "", sD2[k]); printf("],\n");
  printf("\"tail\":["); for (int k = 0; k <= K; k++) printf("%s%lld", k ? "," : "", (long long)tail[k]); printf("],\n");
  for (int d = 1; d <= 3; d++) {
    printf("\"xr%d\":[", d); for (int i = 0; i + d < K; i++) printf("%s%lld", i ? "," : "", (long long)xr[d][i]); printf("],\n");
  }
  printf("\"blk\":["); for (int w = 0; w < 256; w++) printf("%s%lld", w ? "," : "", (long long)blk[w]); printf("]}\n");
  return 0;
}
