/* (C) 2026 Ralf Stephan, in collaboration with Claude Code.  CC0 1.0.
 * cond.c -- the last stage of the ladder: from the core to the cycle set.
 * Computes the condensation rank rho on the y=31 core with edge weight 0 iff
 * both ends lie in the cycle set K, and checks the two rank conditions that
 * DubC.coreClosed_of_rankNat asks for with C = core, K = cycles.
 * gcc -O2 -o cond cond.c
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint64_t u64;
static u64 M = 200560490130ULL;

static int cmp(const void*a,const void*b){
  u64 x=*(const u64*)a,y=*(const u64*)b; return x<y?-1:(x>y?1:0);
}
static long find(u64 *a,long n,u64 x){
  long lo=0,hi=n;
  while(lo<hi){ long mid=(lo+hi)/2; if(a[mid]==x) return mid; if(a[mid]<x) lo=mid+1; else hi=mid; }
  return -1;
}

int main(void){
  long cap=400000, n=0;
  u64 *core=malloc(cap*sizeof(u64));
  FILE*f=fopen("grid_core31.txt","r"); u64 v;
  while(fscanf(f,"%llu",(unsigned long long*)&v)==1){ if(n==cap){cap*=2;core=realloc(core,cap*sizeof(u64));} core[n++]=v; }
  fclose(f);
  qsort(core,n,sizeof(u64),cmp);
  printf("core %ld\n",n);

  unsigned char *inK=calloc(n,1);
  f=fopen("core_y31_cycles.txt","r");
  char line[8192]; long ncyc=0,nk=0;
  if(!fgets(line,sizeof line,f)){ fprintf(stderr,"bad file\n"); return 1; }
  while(fgets(line,sizeof line,f)){
    unsigned long long st; long dummy; char w[4096];
    if(sscanf(line,"%llu %ld %s",&st,&dummy,w)!=3) continue;
    ncyc++;
    u64 r=st;
    for(char*c=w;*c;c++){
      long i=find(core,n,r);
      if(i<0){ printf("CYCLE STATE NOT IN CORE: %llu\n",(unsigned long long)r); return 1; }
      if(!inK[i]){ inK[i]=1; nk++; }
      r=(7*r+(*c-'0'))%M;
    }
    if(r!=st){ printf("cycle does not close\n"); return 1; }
  }
  fclose(f);
  printf("cycles %ld  cycle states %ld  core-not-K %ld\n",ncyc,nk,n-nk);

  /* successors inside the core */
  int *deg=calloc(n,sizeof(int)); long *su=malloc(n*3*sizeof(long));
  for(long i=0;i<n;i++){
    for(int d=0;d<7;d++){
      u64 t=(7*core[i]+d)%M; long j=find(core,n,t);
      if(j>=0){ if(deg[i]<3) su[i*3+deg[i]]=j; deg[i]++; }
    }
  }
  long maxdeg=0,two=0; for(long i=0;i<n;i++){ if(deg[i]>maxdeg)maxdeg=deg[i]; if(deg[i]>1)two++; }
  printf("max core out-degree %ld ; states with >=2 core successors %ld\n",maxdeg,two);

  /* condensation rank: rho(r) = max over core successors t of rho(t) + w,
     w = 0 iff both r and t are cycle states. */
  int *rho=calloc(n,sizeof(int));
  long rounds=0;
  for(;;){
    rounds++; long ch=0;
    for(long i=0;i<n;i++){
      int best=0;
      for(int e=0;e<deg[i];e++){
        long j=su[i*3+e];
        int w=(inK[i]&&inK[j])?0:1;
        if(rho[j]+w>best) best=rho[j]+w;
      }
      if(best!=rho[i]){ rho[i]=best; ch++; }
    }
    if(!ch) break;
    if(rounds>200000){ printf("NO CONVERGENCE (a cycle avoids K)\n"); return 1; }
  }
  int mx=0; for(long i=0;i<n;i++) if(rho[i]>mx) mx=rho[i];
  printf("condensation rank converged in %ld rounds, max rho = %d\n",rounds,mx);

  long bad=0;
  for(long i=0;i<n;i++) for(int e=0;e<deg[i];e++){
    long j=su[i*3+e];
    if(rho[j]>rho[i]) bad++;
    if(!inK[i] && rho[j]>=rho[i]) bad++;
  }
  printf("rank-condition violations (C=core, K=cycles): %ld\n",bad);
  return 0;
}
