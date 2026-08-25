/* (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
 *
 * grid.c -- prototype of the *ladder grid* engine that DubC/Rung.lean has to
 * run inside `native_decide`.  Unlike subshift.c / ladder.c / cycles.c this one
 * is written to mirror the Lean checker exactly, so its numbers are the sizes
 * the Lean side will have to cope with.
 *
 * The point of the representation: a state at level M = M'*p is a pair
 * (i, k), i indexing the surviving set at level M', k < p, with residue
 * S'[i] + k*M'.  Its successor's index is  SU'[i][d]*p + k'  --  pure
 * arithmetic, no lookup.  So no binary search ever happens.
 *
 * Build:  gcc -O2 -o grid grid.c
 * Run:    ./grid
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef uint64_t u64;
typedef int32_t  i32;

#define AA 7                 /* the base */
#define NDIG 7               /* digits 0..6, exactly as the Lean statement */

static u64  M;               /* current modulus                  */
static u64  n;               /* number of states at this level   */
static u64 *S;               /* n residues                       */
static i32 *SU;              /* n*NDIG successor indices, -1 = none */
static unsigned char *alv;   /* n alive flags                    */

static u64 gcd_u(u64 a, u64 b){ while(b){ u64 t=a%b; a=b; b=t; } return a; }

/* ---------- peeling ---------------------------------------------------- */

/* forward round: kill every alive state with no alive successor.
   returns number killed. */
static u64 peel_fwd_round(void){
  u64 killed = 0;
  unsigned char *nk = malloc(n);
  memset(nk, 0, n);
  for(u64 i=0;i<n;i++){
    if(!alv[i]) continue;
    int ok = 0;
    for(int d=0;d<NDIG;d++){
      i32 j = SU[i*NDIG+d];
      if(j>=0 && alv[j]){ ok=1; break; }
    }
    if(!ok){ nk[i]=1; killed++; }
  }
  for(u64 i=0;i<n;i++) if(nk[i]) alv[i]=0;
  free(nk);
  return killed;
}

/* backward round: kill every alive state with no alive predecessor. */
static u64 peel_bwd_round(void){
  u64 killed = 0;
  unsigned char *hp = malloc(n);
  memset(hp, 0, n);
  for(u64 i=0;i<n;i++){
    if(!alv[i]) continue;
    for(int d=0;d<NDIG;d++){
      i32 j = SU[i*NDIG+d];
      if(j>=0 && alv[j]) hp[j]=1;
    }
  }
  for(u64 i=0;i<n;i++) if(alv[i] && !hp[i]){ alv[i]=0; killed++; }
  free(hp);
  return killed;
}

static void peel(const char *tag, int do_bwd, u64 *rounds_out, u64 *fwd_depth_out){
  u64 rounds=0, fwd_depth=0;
  for(;;){
    u64 k1 = peel_fwd_round();
    if(k1) fwd_depth++;
    u64 k2 = do_bwd ? peel_bwd_round() : 0;
    rounds++;
    if(k1==0 && k2==0) break;
  }
  u64 live=0; for(u64 i=0;i<n;i++) live+=alv[i];
  *rounds_out = rounds; *fwd_depth_out = fwd_depth;
  printf("    %s: %llu rounds -> %llu live\n",tag,
         (unsigned long long)rounds,(unsigned long long)live);
}

/* pure forward peel, recording the death depth of every state (capped). */
static u64 *fwd_depth_map(u64 cap, u64 *nlive){
  u64 *dep = malloc(n*sizeof(u64));
  unsigned char *a = malloc(n);
  memcpy(a, alv, n);
  for(u64 i=0;i<n;i++) dep[i]= a[i] ? cap : 0;
  for(u64 r=0;r<cap;r++){
    u64 killed=0;
    unsigned char *nk = malloc(n); memset(nk,0,n);
    for(u64 i=0;i<n;i++){
      if(!a[i]) continue;
      int ok=0;
      for(int d=0;d<NDIG;d++){ i32 j=SU[i*NDIG+d]; if(j>=0&&a[j]){ok=1;break;} }
      if(!ok){ nk[i]=1; killed++; }
    }
    if(!killed) break;
    for(u64 i=0;i<n;i++) if(nk[i]){ a[i]=0; dep[i]=r; }
    free(nk);
  }
  u64 lv=0; for(u64 i=0;i<n;i++) lv+=a[i];
  *nlive = lv;
  free(a);
  return dep;
}

/* ---------- compaction ------------------------------------------------- */

static void compact(void){
  i32 *map = malloc(n*sizeof(i32));
  u64 m=0;
  for(u64 i=0;i<n;i++) map[i] = alv[i] ? (i32)(m++) : -1;
  u64 *S2  = malloc(m*sizeof(u64));
  i32 *SU2 = malloc(m*NDIG*sizeof(i32));
  for(u64 i=0;i<n;i++){
    if(!alv[i]) continue;
    u64 t = map[i];
    S2[t] = S[i];
    for(int d=0;d<NDIG;d++){
      i32 j = SU[i*NDIG+d];
      SU2[t*NDIG+d] = (j>=0 && alv[j]) ? map[j] : -1;
    }
  }
  free(S); free(SU); free(alv); free(map);
  S=S2; SU=SU2; n=m;
  alv = malloc(n); memset(alv,1,n);
}

/* ---------- levels ----------------------------------------------------- */

static void level0(const int *pr, int np){
  M = 1; for(int i=0;i<np;i++) M *= pr[i];
  i32 *idx = malloc(M*sizeof(i32));
  u64 cnt=0;
  for(u64 x=0;x<M;x++) idx[x] = (gcd_u(x,M)==1) ? (i32)(cnt++) : -1;
  n = cnt;
  S  = malloc(n*sizeof(u64));
  SU = malloc(n*NDIG*sizeof(i32));
  alv= malloc(n); memset(alv,1,n);
  for(u64 x=0;x<M;x++) if(idx[x]>=0) S[idx[x]]=x;
  for(u64 i=0;i<n;i++)
    for(int d=0;d<NDIG;d++)
      SU[i*NDIG+d] = idx[(AA*S[i]+d)%M];
  free(idx);
  printf("  level0 M=%llu  units=%llu\n",(unsigned long long)M,(unsigned long long)n);
}

static void rung(int p){
  u64 Mn = M*(u64)p;
  u64 nn = n*(u64)p;
  u64 *S2  = malloc(nn*sizeof(u64));
  i32 *SU2 = malloc(nn*NDIG*sizeof(i32));
  unsigned char *a2 = malloc(nn);
  if(!S2||!SU2||!a2){ fprintf(stderr,"OOM at p=%d nn=%llu\n",p,(unsigned long long)nn); exit(1); }
  for(u64 i=0;i<n;i++){
    for(u64 k=0;k<(u64)p;k++){
      u64 t = i*(u64)p + k;
      u64 r = S[i] + k*M;
      S2[t] = r;
      a2[t] = (r % (u64)p) != 0;
      for(int d=0;d<NDIG;d++){
        i32 j = SU[i*NDIG+d];
        if(j<0){ SU2[t*NDIG+d] = -1; continue; }
        u64 y = (AA*r + (u64)d) % Mn;
        SU2[t*NDIG+d] = (y % (u64)p == 0) ? -1 : (i32)((u64)j*(u64)p + y/M);
      }
    }
  }
  free(S); free(SU); free(alv);
  S=S2; SU=SU2; alv=a2; n=nn; M=Mn;
  printf("  rung p=%2d: M=%llu  grid=%llu\n",p,(unsigned long long)M,(unsigned long long)n);
}

int main(void){
  const int pr0[] = {2,3,5,7,11,13,17};
  const int lad[] = {19,23,29,31};
  u64 rounds, fdep, nlive;

  level0(pr0,7);
  peel("peel(f+b)",1,&rounds,&fdep);
  {
    u64 *dep = fwd_depth_map(4000,&nlive);
    u64 mx=0; for(u64 i=0;i<n;i++) if(alv[i]&&dep[i]<4000&&dep[i]>mx) mx=dep[i];
    printf("    fwd-only depth max=%llu live=%llu\n",(unsigned long long)mx,(unsigned long long)nlive);
    free(dep);
  }
  compact();
  printf("  level0 core = %llu\n",(unsigned long long)n);

  for(int t=0;t<4;t++){
    rung(lad[t]);
    /* forward-only statistics first (what a forward-only Lean ladder would cost) */
    {
      u64 *dep = fwd_depth_map(4000,&nlive);
      u64 mx=0; for(u64 i=0;i<n;i++) if(dep[i]<4000&&dep[i]>mx) mx=dep[i];
      printf("    fwd-only: depth max=%llu -> live=%llu\n",
             (unsigned long long)mx,(unsigned long long)nlive);
      free(dep);
    }
    peel("peel(f+b)",1,&rounds,&fdep);
    compact();
    printf("  core after p=%2d : %llu states\n",lad[t],(unsigned long long)n);
    fflush(stdout);
  }
  return 0;
}
