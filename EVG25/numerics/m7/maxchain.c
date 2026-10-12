/* (C) 2026 Ralf Stephan, in collaboration with Claude Code. Released under CC0 1.0 Universal.
 * M7: exact max over dyadic chains of prod_{s=2}^{n} |cos(pi theta_s)|,
 * theta_s = a_s / 2^s (a_s odd), a_{s+1} = 3 a_s + eps 2^s mod 2^{s+1}, theta_2 in {1/4, 3/4}.
 * Depth-first branch and bound (remaining factors <= 1).  Prints n, log2(max)/n for n <= NMAX.
 * Usage: maxchain NMAX   (NMAX <= 62) */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <stdint.h>
static int NMAX; static double best[64]; static int64_t nodes;
static void dfs(uint64_t a, int s, double lp) {   /* lp = log2 prod up to s inclusive */
  nodes++;
  if (lp > best[s]) best[s] = lp;
  if (s == NMAX) return;
  /* prune: best achievable at depth NMAX <= lp; but we want max at every depth n, so prune only
     if lp <= best[n] for all n > s */
  int useful = 0; for (int n = s + 1; n <= NMAX; n++) if (lp > best[n]) { useful = 1; break; }
  if (!useful) return;
  uint64_t M = 1ULL << (s + 1);
  for (int e = 0; e < 2; e++) {
    uint64_t b = (3 * a + (e ? (1ULL << s) : 0)) & (M - 1);
    double c = fabs(cos(M_PI * (double)b / (double)M));
    dfs(b, s + 1, lp + log2(c));
  }
}
int main(int argc, char **argv) {
  NMAX = atoi(argv[1]);
  for (int i = 0; i < 64; i++) best[i] = -1e300;
  /* seed incumbents greedily so pruning bites */
  dfs(1, 2, log2(cos(M_PI / 4)));
  dfs(3, 2, log2(fabs(cos(3 * M_PI / 4))));
  for (int n = 2; n <= NMAX; n++) printf("%d %.5f %.3f\n", n, best[n] / n, best[n]);
  fprintf(stderr, "nodes %lld\n", (long long)nodes);
  return 0;
}
