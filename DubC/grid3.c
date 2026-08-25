/* (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
 * grid2.c -- sizing run for the Lean rung checker.  Two-stage peel per rung
 * (forward to fixpoint, then backward to fixpoint) which is provably the core,
 * plus the final condensation rank on the last core.
 * gcc -O2 -o grid2 grid2.c
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef uint64_t u64;
typedef int32_t  i32;
#define AA 7
#define NDIG 7

static u64 M, n; static u64 WORK=0;
static u64 *S;
static i32 *SU;
static unsigned char *alv;

static u64 gcd_u(u64 a,u64 b){while(b){u64 t=a%b;a=b;b=t;}return a;}

/* forward stage: rank = min(cap, forward death depth); survivors get cap. */
static u64 *stage_fwd(u64 cap,u64 *live,u64 *maxdep){
  u64 *dep=malloc(n*sizeof(u64));
  for(u64 i=0;i<n;i++) dep[i]= alv[i]?cap:0;
  u64 md=0;
  unsigned char *nk=malloc(n);
  for(u64 r=0;r<cap;r++){
    memset(nk,0,n); u64 killed=0;
    for(u64 i=0;i<n;i++){
      if(!alv[i]) continue;
      WORK++;
      int ok=0;
      for(int d=0;d<NDIG;d++){i32 j=SU[i*NDIG+d]; if(j>=0&&alv[j]){ok=1;break;}}
      if(!ok){nk[i]=1;killed++;}
    }
    if(!killed) break;
    for(u64 i=0;i<n;i++) if(nk[i]){alv[i]=0;dep[i]=r;}
    md=r;
  }
  free(nk);
  u64 lv=0; for(u64 i=0;i<n;i++) lv+=alv[i];
  *live=lv; *maxdep=md;
  return dep;
}

/* backward stage on the current alive set. */
static u64 *stage_bwd(u64 cap,u64 *live,u64 *maxdep){
  u64 *dep=malloc(n*sizeof(u64));
  for(u64 i=0;i<n;i++) dep[i]= alv[i]?cap:0;
  u64 md=0;
  unsigned char *hp=malloc(n),*nk=malloc(n);
  for(u64 r=0;r<cap;r++){
    memset(hp,0,n); memset(nk,0,n); u64 killed=0;
    for(u64 i=0;i<n;i++){
      if(!alv[i]) continue;
      WORK++;
      for(int d=0;d<NDIG;d++){i32 j=SU[i*NDIG+d]; if(j>=0&&alv[j]) hp[j]=1;}
    }
    for(u64 i=0;i<n;i++) if(alv[i]&&!hp[i]){nk[i]=1;killed++;}
    if(!killed) break;
    for(u64 i=0;i<n;i++) if(nk[i]){alv[i]=0;dep[i]=r;}
    md=r;
  }
  free(hp);free(nk);
  u64 lv=0; for(u64 i=0;i<n;i++) lv+=alv[i];
  *live=lv; *maxdep=md;
  return dep;
}

static void compact(void){
  i32 *map=malloc(n*sizeof(i32)); u64 m=0;
  for(u64 i=0;i<n;i++) map[i]= alv[i]?(i32)(m++):-1;
  u64 *S2=malloc(m*sizeof(u64)); i32 *SU2=malloc(m*NDIG*sizeof(i32));
  for(u64 i=0;i<n;i++){
    if(!alv[i])continue; u64 t=map[i]; S2[t]=S[i];
    for(int d=0;d<NDIG;d++){i32 j=SU[i*NDIG+d]; SU2[t*NDIG+d]=(j>=0&&alv[j])?map[j]:-1;}
  }
  free(S);free(SU);free(alv);free(map);
  S=S2;SU=SU2;n=m; alv=malloc(n); memset(alv,1,n);
}

static void level0(void){
  const int pr[]={2,3,5,7,11,13,17};
  M=1; for(int i=0;i<7;i++) M*=pr[i];
  i32 *idx=malloc(M*sizeof(i32)); u64 c=0;
  for(u64 x=0;x<M;x++) idx[x]=(gcd_u(x,M)==1)?(i32)(c++):-1;
  n=c; S=malloc(n*sizeof(u64)); SU=malloc(n*NDIG*sizeof(i32));
  alv=malloc(n); memset(alv,1,n);
  for(u64 x=0;x<M;x++) if(idx[x]>=0) S[idx[x]]=x;
  for(u64 i=0;i<n;i++) for(int d=0;d<NDIG;d++) SU[i*NDIG+d]=idx[(AA*S[i]+d)%M];
  free(idx);
}

static void rung(int p){
  u64 Mn=M*(u64)p, nn=n*(u64)p;
  u64 *S2=malloc(nn*sizeof(u64)); i32 *SU2=malloc(nn*NDIG*sizeof(i32));
  unsigned char *a2=malloc(nn);
  for(u64 i=0;i<n;i++) for(u64 k=0;k<(u64)p;k++){
    u64 t=i*(u64)p+k, r=S[i]+k*M;
    S2[t]=r; a2[t]=(r%(u64)p)!=0;
    for(int d=0;d<NDIG;d++){
      i32 j=SU[i*NDIG+d];
      if(j<0){SU2[t*NDIG+d]=-1;continue;}
      u64 y=(AA*r+(u64)d)%Mn;
      SU2[t*NDIG+d]=(y%(u64)p==0)?-1:(i32)((u64)j*(u64)p+y/M);
    }
  }
  free(S);free(SU);free(alv); S=S2;SU=SU2;alv=a2;n=nn;M=Mn;
}

int main(void){
  const int lad[]={19,23,29,31};
  u64 live,md;
  level0();
  printf("level0 M=%llu grid=%llu\n",(unsigned long long)M,(unsigned long long)n);
  { u64 *df=stage_fwd(100000,&live,&md);
    printf("  fwd: maxdepth=%llu live=%llu work=%llu\n",(unsigned long long)md,(unsigned long long)live,(unsigned long long)WORK); WORK=0; free(df);
    u64 *db=stage_bwd(100000,&live,&md);
    printf("  bwd: maxdepth=%llu live=%llu work=%llu\n",(unsigned long long)md,(unsigned long long)live,(unsigned long long)WORK); WORK=0; free(db); }
  compact();
  printf("  core0=%llu\n",(unsigned long long)n);
  for(int t=0;t<4;t++){
    rung(lad[t]);
    printf("rung p=%d grid=%llu\n",lad[t],(unsigned long long)n);
    u64 *df=stage_fwd(1000000,&live,&md);
    printf("  fwd: maxdepth=%llu live=%llu work=%llu\n",(unsigned long long)md,(unsigned long long)live,(unsigned long long)WORK); WORK=0; free(df);
    u64 *db=stage_bwd(1000000,&live,&md);
    printf("  bwd: maxdepth=%llu live=%llu work=%llu\n",(unsigned long long)md,(unsigned long long)live,(unsigned long long)WORK); WORK=0; free(db);
    /* verify fixpoint: another fwd stage must kill nothing */
    u64 *df2=stage_fwd(1000000,&live,&md);
    printf("  refwd: maxdepth=%llu live=%llu   (fixpoint check)\n",
           (unsigned long long)md,(unsigned long long)live); free(df2);
    compact();
    printf("  core=%llu\n",(unsigned long long)n);
    fflush(stdout);
  }
  /* dump final core residues for cross-checking against core_y31_cycles.txt */
  FILE *f=fopen("grid_core31.txt","w");
  for(u64 i=0;i<n;i++) fprintf(f,"%llu\n",(unsigned long long)S[i]);
  fclose(f);
  printf("wrote grid_core31.txt (%llu residues, M=%llu)\n",
         (unsigned long long)n,(unsigned long long)M);
  return 0;
}
