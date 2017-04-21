/************************************************************************************
Copyright (c) 2016, Jingchao Chen (chen-jc@dhu.edu.cn)
November 12, 2016

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include <math.h>
#include "mtl/Sort.h"
#include "core/checker.h"
#include "utils/System.h"

#define ABS(x) ((x)>0 ? (x) : (-x) )

#define    USEDFLAG   1
#define    VERIFIED   2
#define    SEG_SIZE  10000
#define    HASHSIZE  500000
 
int HASHBLOCK=2000000;

using namespace treeRat;

vec <int> learnt23;
int yes_learnt23=0;
vec <int> detachlist;
vec <int> tmpdetach;
vec <Lit> auxUnit;
int bintrn=0;
int auxPropSum=0;
int next_clsNo=0x3fffffff;
int traceflag=0;
int len_lim=3;
int watchmode=0;

#define SwapLit(a,b) { Lit t; t=a; a=b; b=t;}

inline Lit makeLit(int lit) { return (lit > 0) ? mkLit(lit-1) : ~mkLit(-lit-1);}

//=================================================================================================
static DoubleOption  opt_garbage_frac      ("CORE", "gc-frac",     "The fraction of wasted memory allowed before a garbage collection is triggered",  0.20, DoubleRange(0, false, HUGE_VAL, false));

//=================================================================================================
checker::checker() :
    ok                 (true)
  , garbage_frac     (opt_garbage_frac)
  , verbosity        (0)
  , qhead              (0)
{
   remNum=0;
   lastDel=-1;
   trueClause=0;
   Delq_active=0;
   occLit=0;
   verifyflag=0;
   detachlist.clear();
}

checker::~checker()
{
}

//=================================================================================================
// Minor methods:
Var checker::newVar()
{  int v = nVars();
    watches  .init(mkLit(v, false));
    watches  .init(mkLit(v, true ));
    watchesBin  .init(mkLit(v, false));
    watchesBin  .init(mkLit(v, true ));
    assigns  .push(l_Undef);
    trail    .capacity(v+12);
    LitBegin .capacity(2*v+2);
    LitEnd   .capacity(2*v+2);
    seen     .capacity(2*v+3);
    reason   .push(cNo_Undef);
    unitpos  .push(cNo_Undef);

    LitBegin[2*v]  = LitBegin[2*v+1]=0;
    LitEnd[2*v]    = LitEnd[2*v+1]  =0;
    seen  [2*v]    = seen[2*v+1]  = seen[2*v+2]=0;
    return v;
}

bool checker::addClause_(vec<Lit>& ps)
{
    sort(ps);
    vec<Lit>    oc;
    oc.clear();
    Lit p; int i, j;
    for (i = j = 0, p = lit_Undef; i < ps.size(); i++)
      if (value(ps[i]) == l_True || ps[i] == ~p) return true;
      else if (value(ps[i]) != l_False && ps[i] != p)
	ps[j++] = p = ps[i];
    ps.shrink(i - j);
   
    if (ps.size() == 0) return ok = false;
    if (ps.size() == 1){
        if (!ok) return false;
        uncheckedEnqueue(ps[0]);
        return ok = propagateMax(1);
    }
    if (ps.size() <= 3) bintrn++;
    CRef cr = ca.alloc(ps);
    attachClause(cr, -clauses.size());
    clauses.push(cr);
    return true;
}

struct watch_lt {
    OccLists<Lit, vec<WatcherL> >  & ws;
    watch_lt( OccLists<Lit, vec<WatcherL> >  & ws_):ws(ws_){} 
    bool operator () (Lit x, Lit y) { 
         return ws[~x].size() < ws[~y].size();
    }    
};

struct clause_lt {
    vec <CRef>        &  clist;
    ClauseAllocator   &  ca;

    clause_lt( vec <CRef> &  clist_, ClauseAllocator  &  ca_) : clist(clist_),ca(ca_){} 
    bool operator () (int x, int y) {
          Clause & c1 = ca[clist[x]];
          Clause & c2 = ca[clist[y]];
          if(c1.size() != c2.size()) return c1.size() < c2.size();
          for(int i=0; i<c1.size(); i++){
             if(c1[i] != c2[i]) return  toInt(c1[i]) < toInt(c2[i]);
          }  
          return x < y;
    }    
};

struct occLit_lt {
    int * & ocLit;
    occLit_lt(int * & ocLit_): ocLit(ocLit_){} 
    bool operator () (Lit x, Lit y) { 
       return ocLit[toInt(x)] < ocLit[toInt(y)];
    }    
};

void checker::attachClause(CRef cr, int clsNo) 
{   Clause & c = ca[cr];
    if(clsNo>0){
          attClauses++;
          if(winmode == 2 && c.size()>2 && occLit) for(int i=0; i<c.size(); i++) occLit[toInt(c[i])]++;
    }
    c.detach(0);
    if(c.size()==2 && watchmode==0) {
      watchesBin[~c[0]].push(Watcher(clsNo, c[1]));
      watchesBin[~c[1]].push(Watcher(clsNo, c[0]));
    } else {
      watches[~c[0]].push(WatcherL(clsNo,cr));
      watches[~c[1]].push(WatcherL(clsNo,cr));
    }
}

void checker::attachClause2(CRef cr, int clsNo)
{     if(clsNo>0) {
          attClauses++;
      }
      Clause& c = ca[cr];
      c.detach(0);
      if(c.size() !=2){
            if(winmode == 2){
               if(occLit==0 || clsNo<=0) sort((Lit *)c, c.size(), watch_lt(watches));
               else{
                      sort((Lit *)c, c.size(), occLit_lt(occLit));
                      for(int i=0; i<c.size(); i++) occLit[toInt(c[i])]++;
                }
                int j=0;
                for(int i=0; i<c.size(); i++) {
                    if(value(c[i]) == l_False) continue;
                    SwapLit(c[j],c[i]);j++;
                    if(j>=2) break;
                 }         
                 if(j==1 && value(c[0]) != l_True)  uncheckedEnqueue(c[0],clsNo);
            }
      }
      if(c.size()==2 && watchmode==0) {
           watchesBin[~c[0]].push(Watcher(clsNo, c[1]));
           watchesBin[~c[1]].push(Watcher(clsNo, c[0]));
      }
      else{
            watches[~c[0]].push(WatcherL(clsNo,cr));
            watches[~c[1]].push(WatcherL(clsNo,cr));
      }
}

inline void remove2(vec<Watcher> & wlist, int clsNo)
{   int sz=wlist.size()-1;
    int j = sz;
    for (; j > 0 && wlist[j].clsNo != clsNo; j--);
    wlist[j]=wlist[sz];
    wlist.pop();
}

inline void remove3(vec<WatcherL> & wlist, int clsNo)
{   int sz=wlist.size()-1;
    int j = sz;
    for (; j > 0 && wlist[j].clsNo != clsNo; j--);
    wlist[j]=wlist[sz];
    wlist.pop();
}

inline void checker::detachClause0(Clause& c, int clsNo) 
{
    if(clsNo>0){
        if(c.size()>2 && occLit) for(int i=0; i<c.size(); i++) occLit[toInt(c[i])]--;
        attClauses--;
    }
    if(c.size()==2 && watchmode==0) {
          remove2(watchesBin[~c[0]], clsNo);
          remove2(watchesBin[~c[1]], clsNo);
    } 
    else {
        remove3(watches[ ~c[0] ], clsNo);
        remove3(watches[ ~c[1] ], clsNo);
    }
}

CRef checker::detachClause(int clsNo) 
{
    CRef Cr=getCref(clsNo);
    detachClause0(ca[Cr],clsNo);
    return Cr;
}

void checker::removeClause(int clsNo) 
{
  if(++remNum > 100000){
       remNum=0;
       checkGarbage();
  } 
  CRef cr=detachClause(clsNo);
  ca.free(cr);
}

void checker::cancelUntil(int level) {
    if (trail_lim.size() > level){
        for (int c = trail.size()-1; c >= trail_lim[level]; c--){
            Var      x  = var(trail[c]);
            assigns [x] = l_Undef;
        }
        qhead = trail_lim[level];
        trail.shrink(trail.size() - qhead);
        trail_lim.shrink(trail_lim.size() - level);
    } 
}

void checker::uncheckedEnqueue(Lit p, int from)
{   assigns[var(p)] = lbool(!sign(p));
    reason[var(p)]  = from;
    trail.push_(p);
}
//------------------------------------------
bool checker::propagate()
{   unsigned int check=1;
    int i,start[2],pre_i=0;
    start[0]=start[1]=qhead;
    int lp=0, l23sz=learnt23.size();
    Lit pre_p=lit_Undef;
    int round=0;
loop:
    qhead=start[check];
    while (qhead < trail.size()){
       Lit  p=trail[qhead++];
       if(check==0) {
           if(pre_p == p) i=pre_i;
           else i=0;  
           goto longcls;
        }
        i=0;
longcls:
       vec<WatcherL> &  ws  = watches[ p ];
       Lit  false_lit = ~p;
       int wsize=ws.size();
       for (; i <wsize; i++){
           int cNo = ws[i].clsNo;
           if(check != (USEDFLAG & verifyflag[cNo])) continue;
            CRef   cr = ws[i].cr;
            Clause & c = ca[cr];
            if(value(c[0]) == l_True || value( c[1]) == l_True) continue;
	    if (c[0] == false_lit) c[0]=c[1];
            for (int m = 2; m < c.size(); m++) {
                  if (value(c[m]) != l_False){
                     c[1] = c[m]; c[m] = false_lit;
	 	     watches[ ~c[1] ].push(WatcherL(cNo,cr));
                     wsize--;
                     ws[i--]=ws[wsize];
                     goto NextClause; 
                }
	    }
            c[1] = false_lit;
            if (value(c[0]) == l_False){
                ws.shrink(ws.size() - wsize);
                learnt23.shrink(learnt23.size()-l23sz);
                analyze_used(cNo);
                return false;
             }
             else{
                 uncheckedEnqueue(c[0],cNo);
                 if(!check){
                      ws.shrink(ws.size() - wsize);
                      start[check]=qhead-1;
                      pre_i=i;
                      pre_p=p;
                      check=check^1; 
                      goto loop;
                 }
             }
        NextClause:
                     ;
        }
        ws.shrink(ws.size() - wsize);
    }
    start[check]=qhead;
    if(start[0] != start[1]){ check=check^1; goto loop;}
ltry:
     while(lp<l23sz){
          int n=learnt23[lp];
          CRef cr = learnts[n];
          if(cr == CRef_Undef){
                l23sz--;
                learnt23[lp]=learnt23[l23sz];
                continue;
          }
          Clause &  c = ca[cr];
          int m=0,j=0;
          for(int k=0; k<c.size(); k++) if (value(c[k]) != l_False) {j++;m=k;}
          if(j==0){
                analyze_used(n+1);
                learnt23.shrink(learnt23.size()-l23sz);
                return false;
          }
          if(j==1 && value(c[m]) != l_True ){
                uncheckedEnqueue(c[m],n+1);
                if(c.detach()) attachClause(cr, n+1);
                l23sz--;
                learnt23[lp]=learnt23[l23sz];
                auxPropSum++;
                goto loop;
          }
          lp++;
    }
    if(round==0){ round=1; lp=0; goto ltry;}
    learnt23.shrink(learnt23.size()-l23sz);
    return true;
}

bool checker::propagate2()
{   unsigned int check=1;
    int i,start[2],pre_i=0;
    start[0]=start[1]=qhead;
    Lit pre_p=lit_Undef;
loop:
    qhead=start[check];
    while (qhead < trail.size()){
        Lit            p   = trail[qhead++];
        if(check==0) {
           if(pre_p == p) i=pre_i;
           else i=0;  
           goto longcls;
        }
       {
         vec<Watcher> &  wbin  = watchesBin[p];
         for(int k = 0;k<wbin.size();k++) {
	      int cNo=wbin[k].clsNo;
              Lit imp = wbin[k].blocker;
              if(value(imp) == l_True) continue;
              if(value(imp) == l_False){
                  analyze_used(cNo);
                  return false;
              }
              uncheckedEnqueue(imp,cNo);
          }
        }
        i=0;
longcls:
        vec<WatcherL> &  ws  = watches[ p ];
        Lit  false_lit = ~p;
        int wsize=ws.size();
        for (; i <wsize; i++){
            int cNo = ws[i].clsNo;
            if(check != (USEDFLAG & verifyflag[cNo])) continue;
            CRef   cr = ws[i].cr;
            Clause & c = ca[cr];
            if(value(c[0]) == l_True || value( c[1]) == l_True) continue;
            if (c[0] == false_lit) c[0]=c[1];
            for (int m = 2; m < c.size(); m++) {
                  if (value(c[m]) != l_False){
		     c[1] = c[m]; c[m] = false_lit;
	 	     watches[ ~c[1]].push(WatcherL(cNo, cr));
                     wsize--;
                     ws[i--]=ws[wsize];
                     goto NextClause; 
                }
	    }
            c[1] = false_lit;
            if (value(c[0]) == l_False){
                 ws.shrink(ws.size() - wsize);
                 analyze_used(cNo);
                 return false;
           }
             else{
                 uncheckedEnqueue(c[0],cNo);
                 if(!check){
                      ws.shrink(ws.size() - wsize);
                      start[check]=qhead-1;
                      pre_i=i;
                      pre_p=p;
                      check=check^1; 
                      goto loop;
                 }
             }
        NextClause:
                     ;
        }
        ws.shrink(ws.size() - wsize);
    }
    start[check]=qhead;
    if(start[0] != start[1]){ check=check^1; goto loop;}
    return true;
}

bool checker::propagateMax(int maxCNo)
{   int i;
    while (qhead < trail.size()){
        Lit            p   = trail[qhead++];
        vec<Watcher> &  wbin  = watchesBin[p];
        for(int k = 0;k<wbin.size();k++) {
	      int cNo=wbin[k].clsNo;
              Lit imp = wbin[k].blocker;
              if(value(imp) == l_True) continue;
              if(value(imp) == l_False){
                  analyze_used(cNo);
                  return false;
              }
              uncheckedEnqueue(imp,cNo);
        }
        i=0;
        vec<WatcherL> &  ws  = watches[ p ];
        Lit  false_lit = ~p;
        int wsize=ws.size();
        for (; i <wsize; i++){
            int cNo = ws[i].clsNo;
            if(cNo >= maxCNo) continue;
            CRef   cr = ws[i].cr;
            Clause & c = ca[cr];
            if(value(c[0]) == l_True || value(c[1]) == l_True) continue;
            if (c[0] == false_lit) c[0]=c[1];
            int sz= c.size()-c.freesize();
            for (int m = 2; m < sz; m++) {
               if (value(c[m]) != l_False){
		     c[1] = c[m]; c[m] = false_lit;
	 	     watches[ ~c[1]].push(WatcherL(cNo,cr));
                     wsize--;
                     ws[i--]=ws[wsize];
                     goto NextClause; 
                }
	    }
            c[1] = false_lit;
            if (value(c[0]) == l_False){
                ws.shrink(ws.size() - wsize);
                analyze_used(cNo);
                return false;
             }
             else uncheckedEnqueue(c[0],cNo);
       NextClause:;
        }
        ws.shrink(ws.size() - wsize);
    }
    return true;
}

//=================================================================================================
// Garbage Collection methods:

void checker::relocAll(ClauseAllocator& to)
{
    // All learnt:
    for (int i = 0; i < learnts.size(); i++) 
               if( learnts[i] != CRef_Undef ) ca.reloc(learnts[i], to);
  // All original:

    for (int i = 0; i < clauses.size(); i++)
               if( clauses[i] != CRef_Undef ) ca.reloc(clauses[i], to);
}

void checker :: garbageCollect()
{
    ClauseAllocator to(ca.size() - ca.wasted()); 
    relocAll(to);
    if (verbosity)
        printf("c |  Garbage collection:   %12d bytes => %12d bytes             |\n", 
               ca.size()*ClauseAllocator::Unit_Size, to.size()*ClauseAllocator::Unit_Size);
   to.moveTo(ca);
//
    for (int v = 0; v < nVars(); v++)
        for (int s = 0; s < 2; s++){
            Lit p = mkLit(v, s);
            vec<WatcherL> &  ws = watches[p];
            for(int k = 0;k<ws.size();k++) ws[k].cr= getCref(ws[k].clsNo);
        }
}

void checker :: simplifylearnt(int CurNo)
{   vec <Lit> lits;
   
    for(int i=next_clsNo+1; i <= CurNo; i++){
          CRef cr=learnts[i];
          if(filePos[i] == -1 || cr == CRef_Undef) continue;
          Clause &  c = ca[cr];
          int No=i+1;
          lits.clear();
          for (int k = 0; k < c.size(); k++){
                   Lit lit=c[k];
                   if(value(lit) == l_False) continue;
                   if(value(lit) == l_True)  goto next;
                   lits.push(lit);
           }
           if(lits.size()>1){
                if(c.size() == lits.size()) continue;
                if(c.detach()) ca.free(cr);
                else removeClause(No);
                learnts[i] = cr = ca.alloc(lits);
                attachClause(cr, No);
           }        
           if(lits.size()==1) uncheckedEnqueue(lits[0], No);
           continue;
next:    
         if(c.detach()==0) detachClause0(c,No);
         learnts[i] = CRef_Undef;
         verifyflag[No]=0;
         ca.free(cr);
    }
    if (verbosity) printf("c nextNo=%d CurNo=%d learnt23#=%d \n",next_clsNo,CurNo,learnt23.size());
}
 
void checker :: readratOutput(char * rupfile) 
{       
#ifdef  __APPLE__
        rat_fp  = fopen(rupfile, "r");
#else
        rat_fp  = fopen64(rupfile, "r");
#endif
        if (rat_fp == NULL) {
		fprintf(stderr, "c Error: cannot open the drat file: %s\n", rupfile);
		exit(-1);
	}
        ori_fixed=trail.size();

 	printf("c %d unit clauses, %d binary,ternary clauses \n",ori_fixed,bintrn); 
        vec <int> ratLits, lits;
        filePos.clear();
        verifyMark.clear();
        off64_t curpos=0;
        int prelit=0;
        int curlit;
        origVars=nVars();
        while(1) {
		char c = fgetc(rat_fp);
                if (c == 'd'){
        	#ifdef  __APPLE__
        		curpos = ftello(rat_fp)+1;
                #else 
               	        curpos = ftello64(rat_fp)+1;
                #endif
        	         int m=filePos.size();
                        if(m){ 
                            off64_t base = filebase[(m-1)/SEG_SIZE];
                            Delqueue.push(DelInfo(m,int(curpos-base)));
                        }
                       	do { c = fgetc(rat_fp);
			} while ((c != '\n') && (c != EOF));
		        continue;
                 }
		 if(c == EOF) return;
                 if(c == '\n') continue;
                 #ifdef  __APPLE__
        	     fseeko(rat_fp, (off64_t)-1, SEEK_CUR);
                     curpos = ftello(rat_fp);
                #else 
                     fseeko64(rat_fp, (off64_t)-1, SEEK_CUR);
                     curpos = ftello64(rat_fp);
               	#endif
        	 lits.clear();
                 int newV=0; 
                 while(1){
                        int ilit;
                	int ret=fscanf(rat_fp, "%i", &ilit);
              		if(ret == EOF) goto done;
                        if(ilit==0) break;
                        lits.push(ilit);
		        int v = ABS(ilit);
                        if(v <= nVars()) continue;
                        newV=ilit;
                        while (v > nVars()) newVar();
          	 }
                 if(lits.size()==0) goto done;
                 Lit firstL=makeLit(lits[0]);
                 int curIdx=filePos.size();
                 if(lits.size()==1) r_unit.push(UnitIndex(curIdx,firstL));
                 int m=filePos.size();
               
                 if (verbosity) if(m%500000==0) printf(" f.s=%d \n",m);

                 if( m%SEG_SIZE == 0) filebase.push(curpos);
                 off64_t base = filebase[m/SEG_SIZE];
                 filePos.push(int(curpos-base));

                 curlit=toInt(firstL);
                 if(prelit != curlit){
                       LitBegin[curlit]=curIdx;
                       LitEnd[prelit]=curIdx;
                       prelit=curlit;
                 }
                 if(newV){
                        verifyMark.push(VERIFIED);
                        lits.copyTo(ratLits);
                        continue;
                 }
                 if(lits.size()>1){
                      if(ratLits.size() && ratLits[0] == -lits[0]){
                            for(int k=1; k<ratLits.size(); k++){
                                 if(ratLits[k] != -lits[1]) continue;
                                 verifyMark.push(VERIFIED);
                                 goto next;
                             }
                       }
                 }
                 verifyMark.push(0);
                 ratLits.clear();
next:            ;
                 
	}
done:
        LitEnd[prelit]=filePos.size();
        if (verbosity) printf("c fbase.size=%d curpos=%"PRIu64" fPos.sz=%d\n",filebase.size(),curpos,filePos.size());
}

int checker :: forwardCheck()
{
      printf("c forward Check RAT proof \n");
      return 1;
}

inline bool checker :: isconflict(vec<Lit> & lits)
{ 
    qhead=trail.size();
    newDecisionLevel();
    sort((Lit *)lits, lits.size(), watch_lt(watches));
    for (int i=0; i<lits.size(); i++){
        Lit p = ~lits[i];
        if (value(p) == l_True ) continue;
        if (value(p) == l_False) return true;
        uncheckedEnqueue(p);
   }
   if(watchmode) return !propagate();
   return !propagate2();
}

void checker :: readfile(int i,vec <Lit>  & lits)
{
     off64_t pos = filebase[i/SEG_SIZE]+filePos[i];
     #ifdef  __APPLE__
           fseeko(rat_fp, pos,SEEK_SET);
     #else 
           fseeko64(rat_fp, pos,SEEK_SET);
     #endif
        	
     lits.clear();
     while(1){
          int ilit;
          int ret=fscanf(rat_fp, "%i", &ilit);
          if(ret == EOF) break;
          if(ilit==0) return;
          lits.push(makeLit(ilit));
     }
}

inline void checker :: offtrueClause(vec <Lit> & lits,int No)
{
    int sz=lits.size();

    if(sz>cutLen) return;
    int minL=nVars()+100;
    int minV=-1;
    int j = 0;
    for (int k = 0; k < sz; k++) {
         Lit lit=lits[k];
         if(value(lit) == l_True){
                if(varLevel[var(lit)] < minL){
                      minV=var(lit);
                      minL=varLevel[minV];
                }
                continue;
         }
	 if(minV !=-1) continue;
         if (value(lit) == l_False) continue;
         lits[k]=lits[j]; lits[j]=lit;
         j++;
    }
    if(minV ==-1 && j==1 && value(lits[0]) != l_True) {
          uncheckedEnqueue(lits[0]);
          minV=var(lits[0]);
    }
    if(minV !=-1){
          trueClause[minV].push(No+1);
          learnts[No] = CRef_Undef;
          return;
    }
    CRef cr = ca.alloc(lits);
    attachClause2(cr,No+1);
    learnts[No]=cr;
}

inline void checker :: offtrueClause(CRef cr,int No, int maxLevel)
{
    Clause & c = ca[cr];
    int sz=c.size()-c.freesize();
    int minL=nVars()+100;
    int minV=-1;
    int j = 0;
    Lit u=c[0];
    for (int k = 0; k < sz; k++) {
         Lit lit=c[k];
         if(value(lit) == l_True){
                if(varLevel[var(lit)] < minL){
                      minV=var(lit);
                      minL=varLevel[minV];
                }
                continue;
         }
	 if(minV !=-1) continue;
         if (value(lit) == l_False) continue;
         u=lit; j++;
    }
    if(minV ==-1 && j==1 && value(u) != l_True) {
          uncheckedEnqueue(u,No+1);
          minV=var(u);
    }
    if(minV !=-1 && (minL <= maxLevel)){//
          trueClause[minV].push(No+1);
          if(c.detach()) ca.free(cr);
          else  removeClause(No+1);
          learnts[No] = CRef_Undef;
          return;
    }
}
       
void checker :: loadbegin(int m)
{   vec <Lit> lits;
    if(m>learnts.size()) m=learnts.size();
    for(int i= 0; i<m;  i++){
           if(learnts[i] != CRef_Undef ) continue;
           if(filePos[i] == -1) continue;
           readfile(i, lits);
           if(lits.size() < 2) continue;
           offtrueClause(lits, i);
    }
}

int checker :: loadblock(int begin, int end,int earlyEnd)
{   vec <Lit> lits;
    for(int i=begin; i<end; i++){
           if(learnts[i] != CRef_Undef ) continue;
           if(filePos[i] == -1) continue;
           readfile(i, lits);
           if(lits.size() < 2) continue;
           offtrueClause(lits, i);
   }
   return 0;
}

void checker :: removeProofunit( vec <UnitIndex> & punit)
{
    int j=0;
    for(int i=0; i<punit.size(); i++){
           if(value(punit[i].lit) == l_True) continue;
           punit[j++]=punit[i];
    }
    punit.shrink(punit.size()-j);
}  

bool checker :: extractUnit(int & proofn, int & unitproof)
{
    for(int i=cur_unit.size()-1; i>=0; i--){
           Lit lit=cur_unit[i].lit;
           if(assigns[var(lit)] != l_Undef) continue;
           newDecisionLevel();
           uncheckedEnqueue(~lit);
           bool cnf=propagate2();
           cancelUntil(0);
           if(cnf == false){
                 unitproof++;
                 uncheckedEnqueue(lit);
                 if(!propagate2()) return true;
           }
    }
    int propStart=trail.size();
    removeProofunit(cur_unit);
    if (verbosity)  printf("c unitproof=%d cur_unit.sz=%d \n",unitproof,cur_unit.size());
    vec <Lit> lits;
    int start_Idx=0,end_idx=0;
    int remUnit=0;
    vec <Lit> saveUnit;
    while(cur_unit.size()){
           cancelUntil(0);
           UnitIndex cUnit = cur_unit.last();
           int pre_idx=end_idx=cUnit.idx;
           start_Idx=0;
           for(int j=cur_unit.size()-2; j>=0; j--){
                  start_Idx = pre_idx-500;   
                  pre_idx = cur_unit[j].idx;
                  if(start_Idx > pre_idx) break;
           }
           if(start_Idx < 0) start_Idx=0;
           for(int j=0; j<cur_unit.size(); j++){
                   if(cur_unit[j].idx >= start_Idx){
                       for(int k=j; k<cur_unit.size(); k++){
                             Lit lit=cur_unit[k].lit;
                             if(assigns[var(lit)] != l_Undef) {cur_unit.pop(); goto Nextblock;}
                             newDecisionLevel();
                             uncheckedEnqueue(lit);
                       }
                       break;
                  }
           }
           if(propStart==trail.size()) break;
           if(end_idx-start_Idx>5000) {
                   cur_unit.pop();
                   continue;
           }
           for(int k=start_Idx; k<=end_idx; k++){
                  if(learnts[k]!= CRef_Undef) continue;
                  if(filePos[k] == -1) continue;
                  readfile(k, lits);
                  if(lits.size() <= 1) continue;
                   for (int j=0; j < lits.size(); j++) 
                           if(assigns[var(lits[j])] == l_Undef) {
                                Lit t=lits[j]; lits[j]=lits[0]; lits[0]=t;
                                break;
                            }
                  CRef cr = ca.alloc(lits);
                  learnts[k]=cr;
                  attachClause2(cr,k+1);
           }
           saveUnit.clear();
           for(int k=end_idx; k>=start_Idx; k--){
                   lits.clear();
                   if(cur_unit.size())  cUnit = cur_unit.last();
                   else cUnit.idx = -1;
                   if(cUnit.idx == k){
                          cur_unit.pop();
                          lits.push(cUnit.lit);
                          saveUnit.push(cUnit.lit);
                   }
                   else{
                          if(learnts[k] == CRef_Undef) continue;
                          if(filePos[k] == -1) continue;
                          CRef cr=learnts[k];
                          Clause & c = ca[cr];
                          if(c.disk()) readfile(k,lits);
                          else for (int j=0; j < c.size(); j++) lits.push(c[j]);
                          removeClause(k+1);
                          learnts[k] = CRef_Undef;
                          if(verifyflag[k+1] == 0 ) continue;
                   }
                   if(lits.size()==1)  removeTrailUnit(lits[0],k);
                   if(verifyflag[k+1] & VERIFIED) continue;
    
                   ok=isconflict(lits);
                   if(!ok){
                        cancelUntil(0);
                        for(int m=start_Idx; m<=end_idx; m++){
                                if(learnts[m] == CRef_Undef) continue;
                                if(filePos[m] == -1) continue;
                                CRef cr=learnts[m];
                                Clause & c = ca[cr];
                                if( c.size() > 1) removeClause(m+1);
                                learnts[m] = CRef_Undef;
                         }
                         unitproof += saveUnit.size();
                         if(lits.size()==1) {
                              unitproof--;
                              remUnit++;
                         }
                         goto Nextblock;
                   }
                   cancelUntil(decisionLevel()-1);
                   verifyflag[k+1] |= VERIFIED;
                   if(lits.size() !=1 ) proofn++;
            }
            cancelUntil(0);
            for(int j=0; j<saveUnit.size(); j++){
                     Lit lit= saveUnit[j];
                     if(value(lit) == l_True) continue;
                     if(value(lit) == l_False) return true;
                     unitproof++;
                     uncheckedEnqueue(lit);
                     if(!propagateMax(start_Idx+1)) return true;
            }
            CRef cr;
            for(int j=start_Idx; j<=end_idx; j++){
                   if(verifyflag[j+1] & VERIFIED){
                            cr=learnts[j];
                            if(cr == CRef_Undef){
                               if(filePos[j] == -1) continue;
                               if(clauses.size()>=maxCoreNo) continue;
                               readfile(j,lits);
                               if(lits.size()<2 || lits.size()>3) continue;
                               cr = ca.alloc(lits);
                          }
                          else {
                               if(ca[cr].size()>3 || clauses.size()>=maxCoreNo) continue;
                               detachClause0(ca[cr],j+1);
                          } 
                          attachClause(cr, -clauses.size());
                          clauses.push(cr);
                          learnts[j] = CRef_Undef;
                          filePos[j] = -1;
                   }
            }
            removeProofunit(cur_unit);
            propStart=trail.size();
Nextblock:  ;
    }
    cancelUntil(0);
    if (verbosity) printf("c extract verified inf #=%d verified unit#=%d deleted Unit=%d \n",proofn,unitproof,remUnit);
    return false;
}

void checker :: clearWatch( vec<Watcher>& ws)
{
      for (int j = 0; j < ws.size(); j++) {
              int  No=ws[j].clsNo;
              if(No>0){
                   CRef cr=learnts[No-1];
                   if(cr != CRef_Undef){
                        ca.free(cr);
                        learnts[No-1]=CRef_Undef;
                    }
              }
       }
       ws.clear();
}

void checker :: clearWatch( vec<WatcherL>& ws)
{
      for (int j = 0; j < ws.size(); j++) {
              int  No=ws[j].clsNo;
              if(No>0){
                   CRef cr=learnts[No-1];
                   if(cr != CRef_Undef){
                        ca.free(cr);
                        learnts[No-1]=CRef_Undef;
                    }
              }
       }
       ws.clear();
}

void checker :: RemoveTrueClause(int mode)
{   CRef cr;
    if(trueClause==0){
           trueClause = new vec<int>[nVars()];
           varLevel   = new int[nVars()];
    }
    for (int v = 0; v < nVars(); v++){
        trueClause[v].clear();
        varLevel[v]=nVars();
     	for (int s = 0; s < 2; s++){
             Lit p = mkLit(v, s);
             clearWatch(watches[p]);
             clearWatch(watchesBin[p]);
        }
    }
    for (int i = trail.size()-1; i>=0; i--) varLevel[var(trail[i])]=i;
    int j,minL,minV;      
    for (int i =0; i < clauses.size(); i++){
           cr = clauses[i];
           Clause &  c = ca[cr];
           j = 0; minV=-1;
           minL=trail.size();
           for (int k = 0; k < c.size(); k++) {
                 Lit lit=c[k];
	         if(value(lit) == l_True){
                      if(varLevel[var(lit)] < minL){
                           minV=var(lit);
                           minL=varLevel[minV];
                      }
                      continue;
                  }
	          if(minV !=-1) continue;
                  if (value(lit) == l_False) continue;
                  c[k]=c[j]; c[j]=lit;
                  j++;
           }
           if(minV != -1) {
                  trueClause[minV].push(-i);
                  c.detach(1); continue;
           }
           attachClause(cr, -i);
    }
}       

inline void checker :: swapEqTofront(Clause & c, int eqVal)
{
      int j=1;
      j=1;
      for(int n=1; n<c.size(); n++){
           if(seen[toInt(c[n])]!=eqVal) continue;
           SwapLit(c[j],c[n]);
           j++;
      }
}

inline void checker :: moveEqTofront(int preIdx, int curIdx, int ppIdx,int & PreEqLen)
{      CRef cr1 = learnts[preIdx];
       Clause &  c1 = ca[cr1];
       CRef cr2 = learnts[curIdx];
       Clause &  c2 = ca[cr2];
       for(int n=c1.size()-1; n>0; n--) seen[toInt(c1[n])]=1;
       int curLen=1;
       for(int n=c2.size()-1; n>0; n--) {
                if(seen[toInt(c2[n])]==0) continue;
                curLen++;
                seen[toInt(c2[n])]=2;
       }
       if(curLen > PreEqLen){
                swapEqTofront(c1,2);
                swapEqTofront(c2,2);
                for(int n=1; n<curLen; n++) c2[n]=c1[n];
        }
        else{
                if(ppIdx>0 && PreEqLen>0){
                       CRef cr3 = learnts[ppIdx];
                       Clause &  c3 = ca[cr3];
                       for(int n=1; n<c3.size(); n++){
                            if(seen[toInt(c3[n])]!=2) continue;
                            seen[toInt(c3[n])]=3;
                        }
                        swapEqTofront(c1,3);
                        swapEqTofront(c2,3);
                        swapEqTofront(c3,3);
                        for(int n=1; n<c3.size(); n++){
                            if(seen[toInt(c3[n])]!=3) break;
                            c2[n]=c1[n]=c3[n];
                        }
                }                  
      }
      for(int n=c1.size()-1; n>0; n--) seen[toInt(c1[n])]=0;
      PreEqLen=curLen;
}

inline void checker :: saveDetach(int level,int minNo)
{
    minClauseNo=minNo;
    vec <Lit> lits;
    detachClsNo.clear();
    if (trail_lim.size() <= level) return;
    for (int i = trail.size()-1; i >= trail_lim[level]; i--){
          Lit p = ~trail[i];
          vec<WatcherL> & ws = watches[p];
          for (int j = 0; j < ws.size(); j++){
                  if(ws[j].clsNo <= minClauseNo) detachClsNo.push(ws[j].clsNo);
          }
          vec<Watcher>& ws2 = watchesBin[p];
          for (int j = 0; j < ws2.size(); j++){
                  if(ws2[j].clsNo <= minClauseNo) detachClsNo.push(ws2[j].clsNo);
          }
    }
    int j=0;
    int dsz=detachClsNo.size();
    for (int i = 0; i < dsz; i++){
          int cNo=detachClsNo[i];
          CRef cr=getCref(cNo);
          if( cr == CRef_Undef) continue;
          Clause &  c = ca[cr];
          if(c.detach()) continue;
          detachClsNo[j++]=detachClsNo[i];
          detachClause0(c,cNo);
          c.detach(1);
    }
    detachClsNo.shrink(dsz-j);
}          

inline void checker :: restoreDetach()
{
    int dsz=detachClsNo.size();
    for (int i = 0; i < dsz; i++){
          int cNo=detachClsNo[i];
          CRef cr=getCref(cNo);
          if( cr == CRef_Undef) continue;
          if(ca[cr].detach()==0) continue;
          attachClause2(cr, cNo);
          ca[cr].detach(0);
    }
    detachClsNo.clear();
    minClauseNo=-1;
}

inline void checker :: eqvForwardcheck(Lit lit, int CurNo)
{  
     static int sumlocalProof=0;
     if(eqvForwardmode <=0) return;
    
     vec <Lit> lits;
     int i,begin,end=CurNo;
     int p=toInt(lit);
     if(LitEnd[p] -LitBegin[p]>2) begin= LitBegin[p];
     else  begin=LitEnd[p^1];
    
     if(p/2<origVars && (begin != LitBegin[p])) return;
    
     int bin_idx=-1;
     int ppIdx=-1,preIdx=-1;
     int preEqvLen=0;
     for(i=begin; i< CurNo; i++){
           if(filePos[i] == -1) break;
           CRef cr=learnts[i];
           if(cr != CRef_Undef){
                    if(ca[cr].size()==0 || ca[cr].detach()) ca.free(cr);
                    else removeClause(i+1);
                    learnts[i] = CRef_Undef;
           }
           readfile(i,lits);
           if(lits.size() < 2  || lits[0] != lit) break;
           if(bin_idx == -1 && lits.size() > 2) bin_idx=i;
          
           cr=learnts[i] = ca.alloc(lits);
           ca[cr].detach(1);
           if(preIdx !=-1) moveEqTofront(preIdx, i, ppIdx, preEqvLen);
           ppIdx=preIdx;
           preIdx=i;
    }
    end=i;
    if(end-begin<50){
           for(i=begin; i< end; i++) attachClause(learnts[i],i+1);
           return;
    }
    int m=0; 
    for(i=begin; i< bin_idx; i++){
            Clause & c=ca[learnts[i]];
            if (verbosity) printf("c <%d %d %d sz=%d>\n", ++m,toIntLit(c[0]),toIntLit(c[1]),c.size());
            attachClause(learnts[i],i+1);
    }

    restoreTrueClause(var(lit),CurNo);
 
    int j,ilev=decisionLevel();
    newDecisionLevel();
    uncheckedEnqueue(~lit);
    propagateMax(bin_idx+1);
    
    saveDetach(ilev,bin_idx);

    int localproof=0;
    int dis=end-bin_idx;
    int shift=20000;
    if(nVars()<origVars+10) shift=30000;
    if (verbosity) printf("c bin_idx=%d, dis=%d shift=%d\n", bin_idx,dis,shift);
    if (verbosity) printf("c p=%d qhead=%d attClause#=%d ilev=%d\n", toIntLit(~lit),qhead,attClauses,ilev);
    int localcut = (end-bin_idx)>300000? 4:6;
       
    for(i=bin_idx; i< end; i++){
          if(i-shift>=bin_idx){
                j=i-shift;
                CRef cr=learnts[j];
                if( cr != CRef_Undef){
                    if(ca[cr].size() > localcut){
                       if(ca[cr].detach()) ca.free(learnts[j]);
                       else   removeClause(j+1);
                       learnts[j] = CRef_Undef;
                    }      
                }
          }
          CRef pre_cr= (i==bin_idx)? CRef_Undef : learnts[i-1];
       
          if(verifyflag[i+1] & VERIFIED){
nextc: 
                 cancelUntil(ilev+1); 
                 if(pre_cr != CRef_Undef) attachClause(pre_cr,i);
                 continue;
          }

          CRef cr2 = learnts[i];
          Clause &  c2 = ca[cr2];
          if(pre_cr != CRef_Undef && decisionLevel() != (ilev+1)){
               Clause &  c1 = ca[pre_cr];
               int sz=c1.size();
               if(sz>c2.size()) sz=c2.size();
               for(j=1; j<sz; j++) if(c1[j]!=c2[j]) break;
               if(j>=sz && sz>=c1.size()){
                      verifyflag[i+1] |= VERIFIED;
                      ca.free(cr2);
                      learnts[i] = CRef_Undef;
                      goto nextc;
               }                 
               cancelUntil(ilev+j);
               sz=c1.size();
               int k;
               for(k=j; k<sz; k++) if(value(c1[k]) != l_False) break;
               if(k<sz) {SwapLit(c1[0],c1[k]);}
               if(k==sz-1 && assigns[var(c1[0])] == l_Undef) uncheckedEnqueue(c1[0]);
           }
           else {  cancelUntil(ilev+1);  j=1; }
           if(pre_cr != CRef_Undef) attachClause(pre_cr,i);
       
           int repeat=0;
           ok=true;
      loop:
           for(int k=j; k<c2.size(); k++){
                  newDecisionLevel();
                  Lit clit=~c2[k];
                  if(value(clit) == l_True) continue;
                  if(value(clit) == l_False) {
                         if(repeat==0){
                               cancelUntil(ilev+j);
                               repeat=1;
                               goto loop;
                         }
                         ok=false;
                         break;
                  }
                  uncheckedEnqueue(clit);
                  if(repeat) continue;
                  ok=propagateMax(i+1);
                  if(!ok)  break;
           }
        
           if(ok && repeat){ 
                   qhead=trail_lim[ilev];
                   ok=propagateMax(i+1);
            }
          if(!ok){ localproof++; verifyflag[i+1] |= VERIFIED;}
     }
//
     if(end != CurNo){
             cancelUntil(ilev);
             restoreDetach();
     }
     else {
            cancelUntil(ilev+1);
     }
  
     if(learnts[end-1] != CRef_Undef) attachClause(learnts[end-1], end);
     if(eqvForwardmode==1){
         for(i=end-100; i>=bin_idx; i--){
           if(learnts[i] != CRef_Undef){
                 if(ca[learnts[i]].size() > 2){
                           removeClause(i+1);
                           learnts[i] = CRef_Undef;
                   }      
            }
         }
     }         
  
     sumlocalProof += localproof;
     if (verbosity) printf("c localproof=%d attClauses=%d \n", localproof,attClauses);
     if (verbosity) printf("c curNo=%d sumlocalProof=%d\n", CurNo,sumlocalProof);
   
}    

void checker :: clearAllwatch()
{
   for (int v = 0; v < nVars(); v++){
   	for (int s = 0; s < 2; s++){
             Lit p = mkLit(v, s);
             watches[p].clear();
             watchesBin[p].clear();
        }
    }
}

void checker :: rebuildwatch(int CurNo)
{
    if (verbosity) printf("c rebuildwatch attClauses=%d CurNo=%d \n",attClauses,CurNo);
    clearAllwatch();
    for (int i =0; i < clauses.size(); i++){
           CRef cr = clauses[i];
           Clause &  c = ca[cr];
           if(c.detach()) continue;
           attachClause(cr,-i); 
    }
    attClauses=0;
    for(int i=0; i <= CurNo; i++){
          CRef cr=learnts[i];
          if(filePos[i] == -1 || cr == CRef_Undef) continue;
          Clause &  c = ca[cr];
          if(c.detach()) continue;
          if(c.size()<=3 && i>100000 && yes_learnt23 && watchmode){
                learnt23.push(i);
                c.detach(1);
          }
          else  attachClause2(cr,i+1);
    }
    if(watchmode==0) reducebufferlearnt();
} 

void checker :: deletewatch(int CurNo)
{
    if (verbosity) printf("c deletewatch attClauses=%d CurNo=%d watchmode=%d \n",attClauses,CurNo,watchmode);
    DetachWatch(0,CurNo);
    sort(tmpdetach);
    int mid=0;
    if(nVars() >= (origVars+200) && watchmode) mid=tmpdetach.size()-150000;
    if(mid < 0) mid=0;
    attClauses=0;
    for(int k=0; k < tmpdetach.size(); k++){
          int No=tmpdetach[k];
          if(k<mid){
                 if(No>1000000) { learnt23.push(No); continue;}
          }
         CRef cr=learnts[No];
         attachClause(cr,No+1);
    }
    tmpdetach.clear(true);
    if (verbosity) printf("c deleted attClauses=%d learnt23.size=%d\n",attClauses,learnt23.size());
} 
 
void checker :: removeTrailUnit(Lit uLit,int CurNo)
{   
     int lev=decisionLevel()-1;
     if(lev>=0 && trail[trail_lim[lev]]== uLit){
cancel:
           cancelloadtrueCls(lev, CurNo);
           if(trueClause){
                 if(winmode) eqvForwardcheck(uLit, CurNo);
                 restoreTrueClause(var(uLit),CurNo);
           }
     }
     else {
            if(lev>=0){
                 for (int c = trail.size()-1; c > trail_lim[lev]; c--)
                       if(trail[c]==uLit){
                           assigns[var(uLit)] = l_Undef;
                           trail[c]=trail.last();
                           trail.pop();
                           qhead=c;
                           restoreTrueClause(var(uLit),CurNo);
                           goto done;
                        }
                goto cancel;      
            }
            else printf("c error lev=%d uLit=%d CurNo=%d \n",lev,toIntLit(uLit),CurNo);
     }
done:  ;
}

inline void checker :: restoreTrueClause(int v, int MaxNo)
{    
     if(trueClause == 0) return;
     vec<Lit> lits;
     vec<int> & tc = trueClause[v];
     sort(tc);
     for(int i=0; i<tc.size(); i++){
           int No=tc[i];
           if(No<=0) {
                  CRef cr=clauses[-No];
                  if(ca[cr].detach()){
                         attachClause2(clauses[-No], No);
                         ca[cr].detach(0);
                  }
           }
           else{
                  if(No>MaxNo) continue;
                  No--;
                  if(learnts[No] != CRef_Undef) continue;
                  readfile(No, lits);
                  CRef cr = ca.alloc(lits);
                  learnts[No]=cr;
                  ca[cr].detach(1);
                  if(winmode==2 && lits.size() <= len_lim && watchmode) learnt23.push(No);
                  else    attachClause2(cr,No+1);
           }
      }
      tc.clear();
}

void checker :: cancelloadtrueCls(int lev,int MaxNo)
{    
     int first=trail_lim[lev];

     int end=trail.size()-1;
     vec <int> saveV;
     for (int c = end; c >= first; c--){
              int v=var(trail[c]);
              assigns [v] = l_Undef;
              saveV.push(v);
     }
     trail.shrink(trail.size() - first);
     trail_lim.shrink(trail_lim.size() - lev);
     if(trueClause){
         for (int i = saveV.size()-2; i>=0; i--) restoreTrueClause(saveV[i],MaxNo);
     }
     if(winmode !=2) qhead = first; 
     else {
          qhead=0;
          propagate2();
     }
  
}

inline void checker :: loadfalselitclause()
{
     vec <Lit> lits;
     for(int i=0; i<trail.size(); i++){
            int p=toInt(trail[i])^1;
            if(LitBegin[p]>=LitEnd[p]) continue;
            int k=LitBegin[p];
            if(filePos[k] == -1) continue;
            if(learnts[k] != CRef_Undef) continue;
            readfile(k,lits);
            if(lits.size() < 2) continue;
            CRef cr = ca.alloc(lits);
            learnts[k]=cr;
            attachClause2(cr,k+1);
    }
    for (int i=origVars; i<nVars(); i++){
            Lit p = mkLit(i);
            if( assigns[var(p)] != l_Undef) continue;
            int L=toInt(p);
            if(LitBegin[L]>LitBegin[L^1]) L=L^1;
            int k=LitBegin[L];
            if(filePos[k] == -1) continue;
            if(learnts[k] != CRef_Undef) continue;
            readfile(k,lits);
            if(lits.size() < 2) continue;
            CRef cr = ca.alloc(lits);
            learnts[k]=cr;
            attachClause2(cr,k+1);
    }         
}

bool checker :: simplifyUnit(vec <UnitIndex> & new_unit)
{
    bool non_empty = true;
    new_unit.clear();
    newDecisionLevel();
    for(int i=0; i<r_unit.size(); i++){
          Lit lit = r_unit[i].lit;
          int v=var(lit);
          if(value(lit) == l_True) continue;
          new_unit.push(r_unit[i]);
          if(value(lit) == l_False) non_empty=false;
          else {
               uncheckedEnqueue(lit);
               non_empty = propagateMax(1);
          }
          if(!non_empty){
               filePos.shrink(filePos.size()-r_unit[i].idx-1);
               verifyflag[r_unit[i].idx+1] |= USEDFLAG;
               break;
          }
          if(unitpos[v] == cNo_Undef){
                unitpos[v]=r_unit[i].idx+1;
                if(nVars()<500) verifyflag[unitpos[v]] |= USEDFLAG;
          }
    }
    if (verbosity) printf("c new unit size=%d  r_size=%d trail.size=%d \n",new_unit.size(),r_unit.size(),trail.size());
    return non_empty;
}               

bool checker :: double_propagate(int maxNo)
{       bool ret=propagateMax(maxNo);
        if(ret) {
            qhead=0;
            ret=propagateMax(maxNo);
        }
        return ret;
}

bool checker :: getcurUnit(vec <UnitIndex> & c_unit, int mode)
{
     if(mode==2){
          trail_lim.clear();
          trail_lim.push(ori_fixed);
     }
     cancelUntil(0);
     qhead=0;
     propagate2();
     c_unit.clear();
     ok=true;
     for(int i=0; i<r_unit.size(); i++){
           Lit lit=r_unit[i].lit;
           int No=r_unit[i].idx+1;
           if(value(lit) == l_True){
                  verifyflag[No] |= VERIFIED;
                  continue;
           }
           c_unit.push(r_unit[i]);
           if(value(lit) == l_False) {
                  newDecisionLevel();
                  ok=false;
                  goto done;
           } 
           if(winmode==2){
                 if ( (verifyflag[No] & VERIFIED) != VERIFIED){
                      newDecisionLevel();
                      uncheckedEnqueue(~lit);
                      ok=propagate2();
                      cancelUntil(decisionLevel()-1);
                      if(!ok){
                          verifyflag[No] |= VERIFIED;
                          c_unit.pop();
                          goto preunit;
                      }
                 }
                 verifyflag[No] |= USEDFLAG;
           }
           newDecisionLevel();
preunit:
           uncheckedEnqueue(lit);
           ok=propagate2();
           if(!ok)  goto done;
     }
 done:
     return ok;
}

void checker :: reducebufferlearnt()
{ 
    int newsize=0;
    if(learnt23.size()>10000 && yes_learnt23 && watchmode){
             newsize=trail.size();;
             if(newsize>=learnt23.size()) return;
    }
    sort(learnt23);
    for(int i=newsize; i<learnt23.size(); i++){
          int n=learnt23[i];
          CRef cr = learnts[n];
          if(cr == CRef_Undef) continue;
          if(ca[cr].detach()) attachClause(cr, n+1);
    }
    learnt23.shrink(learnt23.size()-newsize);
    if (verbosity) printf("c detached bin, tetrnary learnt #=%d \n",learnt23.size());
}

bool checker :: finddetachUnit()
{    bool ret=false;
     int dp,dsz=detachlist.size();
     for(dp=dsz-1; dp>=0; dp--){
           int n=detachlist[dp];
           CRef cr = learnts[n];
           if(cr == CRef_Undef){
                  dsz--;
                  detachlist[dp]=detachlist[dsz];
                  continue;
           }
           Clause &  c = ca[cr];
           int m=0,j=0;
           for(int k=0; k<c.size(); k++) if (value(c[k]) != l_False) {j++;m=k;}
           if(j==1 && value(c[m]) != l_True ) {
                   uncheckedEnqueue(c[m],n+1);
                   if(c.detach()) attachClause(cr, n+1);
                   dsz--;
                   detachlist[dp]=detachlist[dsz];
                   break;
            }
            if(j==0) { ret=true; analyze_used(n+1);break;}
     }
     if (verbosity) printf("c <dsz=%d dp=%d ret=%d trail.size=%d qhead=%d end >\n",dsz,dp,ret,trail.size(),qhead);
     detachlist.shrink(detachlist.size()-dsz);
     return ret;
}
                           
int checker :: backwardCheck()
{
    attClauses=0;
    eqvForwardmode=-1;
    printf("c backward check\n");
    printf("c %d inferences \n",filePos.size());
    if(verbosity) printf("c r_unit #=%d \n",r_unit.size());
 
    int maxNo=filePos.size();
    filePos.min_memory(maxNo);
    maxCoreNo=clauses.size()+100000;
    verifyflag = (unsigned char * ) calloc (maxCoreNo+maxNo+4, sizeof(unsigned char));
  
    if(clauses.size()<10000 || (nVars()!=origVars && clauses.size()<500000))
          for(int i=0; i <= maxCoreNo; i++) verifyflag[i]=USEDFLAG;
    verifyflag += maxCoreNo;
    for(int i=0; i<maxNo; i++) verifyflag[i+1]=verifyMark[i];
    verifyMark.clear(true);
 
    Delqueue.min_memory(Delqueue.size());

    if(!double_propagate(1)){
            printf("c proof is trivally verified \n");
            return 1;
    }
    cancelUntil(0);
    bool non_empty = simplifyUnit(cur_unit);
    learnts.clear();
    for(int i=0; i<filePos.size(); i++) learnts.push(CRef_Undef);
    learnts.min_memory(maxNo);
   
    vec <Lit> lits;
    if (verbosity) printf("c non_empty=%d \n",(int)non_empty);
    if(non_empty){
          qhead=0;
          non_empty = double_propagate(1);
    }
    cancelUntil(0);
 
    int unproofn=1, proofn=0, unitproof=0;
    if(nVars() < 100000 && clauses.size()<1500000) winmode=1;
    else winmode=2;
    int first=1;
    cutLen=0x5fffffff;
    if(winmode <=1 ){
        ok=extractUnit(proofn, unitproof);
        printf("c %d inferences and %d units are verified in 1st step.\n",proofn,unitproof);
        if(ok) goto done;
    }
    if(!non_empty) printf("c empty clause is detected \n");
    for(int i=0; i<trail.size(); i++) unitpos[var(trail[i])]=0; 
    if(nVars()<500000) occLit = (int * ) calloc (2*nVars()+1, sizeof(int));
    while(unproofn || non_empty){
       unproofn=0;
       int ccnt=0,pre_Sum=0;
       learnt23.clear();
     
       int  end = filePos.size()-1;
       for(int i=0; i<r_unit.size(); i++){
              if(r_unit[i].idx > end) { r_unit.shrink(r_unit.size()-i); break;}
       }
       if (verbosity) printf("c end = %d var#=%d cur_unit#=%d \n", end,nVars(),cur_unit.size());
    
       int initblock=end/100;
       if(initblock>5000) initblock=5000;
       int begin=0;
       int winSize=10000;

     ok=getcurUnit(cur_unit,winmode);
     if(!ok && non_empty){
            non_empty=false;
            printf("c empty clause  is found \n");
     }
     RemoveTrueClause(winmode);
     if(winmode==0){
              if(end<=winSize) begin=0;
              else begin=end-winSize;
              if(begin<=initblock) begin=0;
              cutLen=7;
              eqvForwardmode=0;
              if(initblock<begin) loadbegin(initblock);
              loadblock(begin, end,0);
       }
       else{
          if(winmode==1){
             if(end>10000000) cutLen=4;
             else cutLen=6;
             eqvForwardmode=1;
             initblock=0;
             winSize=40000;
             int init_end=1000000;
             if(end<init_end) init_end=end;
             loadblock(0,init_end,0);
             begin=end;
          }
          if(winmode==2){
              cutLen=0x5fffffff;
              eqvForwardmode=0;
              begin=0;
              ok=activateDelinfo(end,cur_unit);
              if(!ok && non_empty){
                 non_empty=false;
                 printf("c empty clause  is detected.\n");
              }
          }
       }
       if (verbosity) printf("c end=%d begin=%d attClause#=%d winmode=%d\n", end,begin,attClauses,winmode);
     
       if(nVars()>origVars) loadfalselitclause();
       minClauseNo=-1;
       if(non_empty){
            int pre_qhead;
            do{
                pre_qhead=qhead; qhead=0;
                if(watchmode) non_empty =propagate();
                else non_empty = propagate2();
            } while (non_empty && pre_qhead != qhead);
            if(!non_empty) printf("c empty clause is found!\n");
       }
       int  auxUnitmode=0;
       for(int i=end; i>=0; i--){
          if (verbosity) if(i%100000==0)  
                printf("c i=%d proofn=%d auxPropSum=%d ccnt=%d at#=%d \n",i,proofn,auxPropSum,ccnt,attClauses);
           if(ccnt%40000 == 39999){
                  int lsz=learnt23.size();
                  if(lsz && (auxPropSum-pre_Sum >50000 || (!yes_learnt23 && lsz<5000))) reducebufferlearnt();
                  pre_Sum=auxPropSum;
           }
   
           if(i == minClauseNo){
                    cancelUntil(decisionLevel()-1);
                    restoreDetach();
           }

           if(lastDel>=0 && i<=Delqueue[lastDel].timeNo) restoreDelClause(i);
           if(filePos[i] == -1) continue;
        
           if(learnts[i] == CRef_Undef){
              lits.clear();
              if(cur_unit.size()){
                    UnitIndex cUnit = cur_unit.last();
                    if(cUnit.idx == i){
                          cur_unit.pop();
                          lits.push(cUnit.lit);
           if (verbosity) printf("c !! i=%d u=%d unpf=%d pf=%d att#=%d\n", i,toIntLit(lits[0]),unproofn,proofn,attClauses);
                          removeTrailUnit(lits[0],i);
                          while(auxUnit.size()){
                               Lit lit=auxUnit.last();
                               auxUnit.pop();
                               if(lit == lit_Undef) break;
                               if( assigns[var(lit)] == l_Undef) uncheckedEnqueue(lit);  
                          }
                          if(auxUnitmode) restoreAuxUnit();
                          if(cur_unit.size()){
                              UnitIndex nextUnit = cur_unit.last();
                              next_clsNo=nextUnit.idx;
                          }
                          else next_clsNo=0;
                          if(winmode==2) {
                             simplifylearnt(i);
                             if(i-next_clsNo > 50000){
                                  deletewatch(i);
                                  if( nVars() == origVars && clauses.size()>30000){
                                         sort(learnt23);
                                         for(int k=0; k < clauses.size(); k++) verifyflag[-k]=0;
                                 }
                             }
                         }
                  }
              }
              if((verifyflag[i+1] & VERIFIED) || verifyflag[i+1]==0) continue;
              if(lits.size() == 0){
                   readfile(i,lits);
                   if(lits.size()==1) continue;
              }
           }
           else{
               CRef cr=learnts[i];
               Clause & c = ca[cr];
               lits.clear();
               if(c.disk()) readfile(i,lits);
               else  for (int j=0; j < c.size(); j++) lits.push(c[j]);
               if( c.size() > 1){
                     if(c.detach()) ca.free(cr);
                     else removeClause(i+1);
               }
               learnts[i] = CRef_Undef;
               if((verifyflag[i+1] & VERIFIED) || verifyflag[i+1]==0) continue;
          }
          first= winmode>1 || i>end-5;
repeat:
         ok=isconflict(lits);
         ccnt++;
         cancelUntil(decisionLevel()-1);
         if(!ok && first) {
                if(i < end-5 && winmode !=2 ) first=0;
                qhead=0;
                if(watchmode) propagate();
                else propagate2();
                int pre_qhead=qhead;
                ok=isconflict(lits);
         retry:     
                while (!ok && pre_qhead != qhead){
                    pre_qhead=qhead;
                    qhead=0;
                    if(watchmode) ok=!propagate();
                    else ok=!propagate2();
                }
                if(!ok && auxUnitmode==0){
                      auxUnitmode=1;
                      ok=restoreAuxUnit();
                      if(!ok){ pre_qhead=0;  goto retry;}
                }
                if(!ok){
                       ok=finddetachUnit();
                       if(!ok && qhead != trail.size()){ pre_qhead=0; goto retry;}
                }
                cancelUntil(decisionLevel()-1);
                if(auxUnitmode==1){ auxUnitmode=2; restoreAuxUnit();}
          }
          if(!ok) {
                if( begin >=i ) begin=i;
                if( begin > initblock && (i-begin < winSize-100) && minClauseNo <0){
                        int newbegin=i-winSize;
                        if(newbegin<0) newbegin=0;
                        cutLen=0x5fffffff; 
                        loadblock(newbegin,begin,0);
                        begin=newbegin;
                        goto repeat;
                }
                if(unproofn==0) {
                        if(!non_empty) filePos.shrink_(filePos.size()-1-i);
                }
                unproofn++;
                if(lits.size()==1){
                     if (verbosity) printf("c %d unit is not verified \n",toIntLit(lits[0]));
                }
          }
          else {
                verifyflag[i+1] = VERIFIED;
                if(lits.size()==1) unitproof++;
                else proofn++;
          }
       }
       if(unproofn)
        printf("c so far %d inferences %d units are verified, %d inferences not verified\n",proofn,unitproof,unproofn);
       winmode++;
       if(winmode>2) break;
    }
    if(unproofn){
         auxUnit.clear();
         return RATCheck();
    }
    printf("c %d inferences, %d units are verified\n",proofn,unitproof);
    printf("c %d deleted inferences \n",Delqueue.size());
    if(non_empty) {
           printf("c there is no empty clause \n");
           return 0;
    }
done:
    if(verbosity) printf("c clause # =%d \n", clauses.size());
    printf("c proof is verified\n");
    fclose(rat_fp);
    return 1;
}

//-----------------------------------------RAT check
void checker :: setRATvar()
{
    vec<Lit> lits;
    CRef cr;
    RATvar = (char  * ) calloc (nVars()+1, sizeof(char));
    for(int  i=0; i<filePos.size(); i++){
           if(verifyflag[i+1] & VERIFIED) continue;
           if(verifyflag[i+1]==0) continue;
           if(filePos[i] == -1) continue;
           readfile(i,lits);
           RATvar[var(lits[0])]=1;
           if(lits.size()>1 && learnts[i] == CRef_Undef){
                  cr = ca.alloc(lits);
                  learnts[i]=cr;
                  attachClause(cr,i+1);
           }
   }
}

inline void checker :: setRATindex (Clause & c, int clsNo)
{
    for(int j=0; j<c.size(); j++) {
          if(RATvar[var(c[j])]){
              RATindex[toInt(c[j])].push(clsNo);
          }
    }
}

inline int checker :: removeRATindex (vec<Lit> & lits, int clsNo)
{  
    int delno=0;
    for(int j=0; j<lits.size(); j++) {
          if(RATvar[var(lits[j])]){
               delno++;
               remove(RATindex[toInt(lits[j])], clsNo);
          }
     }
     return delno;
}

void checker :: buildRATindex ()
{   CRef cr;
    RATindex = new vec<int>[2*nVars()+1];
    for (int i =0; i <= 2*nVars(); i++) RATindex[i].clear();
    for (int i =0; i < clauses.size(); i++){
        cr = clauses[i];
        if( cr == CRef_Undef) continue;
        setRATindex(ca[cr],-i);
    }
    vec<Lit> lits;
    for(int  i=0; i<filePos.size(); i++){
           if(filePos[i] == -1) continue;
           if(learnts[i] == CRef_Undef){
                  readfile(i,lits);
                  int flag=0;
                  for(int j=0; j<lits.size(); j++) {
                       if(RATvar[var(lits[j])]) {
                            flag=1;
                            RATindex[toInt(lits[j])].push(i+1);
                       }
                  }
                  if(flag && lits.size()>1){
                        cr = ca.alloc(lits);
                        learnts[i]=cr;
                        attachClause(cr,i+1);
                  }
           }
           else {
                 cr=learnts[i];
                 setRATindex(ca[cr],i+1);
          }
    }
}       

bool checker :: conflictCheck(int No, vec<Lit> & lits,int & begin,int end)
{
     int first=1;
     while(1){
          ok=isconflict(lits);
          cancelUntil(decisionLevel()-1);
          if(!ok && first) {
                qhead=first=0;
                ok=propagate2();
                if(ok) {
                     ok=isconflict(lits);
                     cancelUntil(decisionLevel()-1);
                }
                else return true;
          }
          if(ok) return true;
          if(begin >= No) begin=No;
          if(begin <= 0) return false;
          int newbegin=begin-end/3000-50;
          if(newbegin<0) newbegin=0;
          loadblock(newbegin,begin,0);
          begin=newbegin;
     }
     return false;
}
   
int checker :: RATCheck()
{
    cancelUntil(0);
    printf("c RAT check... \n");
    setRATvar();
    buildRATindex();
    int end= filePos.size()-1;
   
    learnt23.clear(true);   
    getcurUnit(cur_unit,2);
    cutLen=0x5fffffff;
    int begin=0;
    if(Delq_active){
           RemoveTrueClause(0);
           DetachDelClause();
           loadblock(begin, end,0);
     }
     else {
           RemoveTrueClause(2);
           winmode=3;
           activateDelinfo(end, cur_unit);
     }
     if(verbosity) printf("c cur_unit.size=%d \n", cur_unit.size());
     CRef cr;
     vec<Lit> lits,lits2,lits3;
     int pivot;
     int proofn=0,unitproof=0;
     vec<int> *ridx;
     eqvForwardmode=-1;
     for(int i=end; i>=0; i--){
           if(lastDel>=0 && i<=Delqueue[lastDel].timeNo) restoreDelClause(i);
           if(filePos[i] == -1) continue;
           if(learnts[i] == CRef_Undef){
              lits.clear();
              if(cur_unit.size()){
                    UnitIndex cUnit = cur_unit.last();
                    if(cUnit.idx == i){
                          cur_unit.pop();
                          lits.push(cUnit.lit);
                     }
              }
              if(verifyflag[i+1] & VERIFIED) {
                     if(lits.size()==1) removeTrailUnit(lits[0],i);
                     continue;
              }
              if(lits.size() == 0 ){
                    if(verifyflag[i+1] == 0)  continue;
                    readfile(i,lits);
                    if(lits.size()==1) continue;
              }
           }
           else{
               removeClause(i+1);
               learnts[i] = CRef_Undef;
               if(verifyflag[i+1] == 0) continue;
               if(verifyflag[i+1] & VERIFIED) continue;
               readfile(i,lits);
          }

          if(lits.size() == 1) removeTrailUnit(lits[0],i);
          int curLevel=decisionLevel();
          int rno=removeRATindex (lits, i+1);
          if(rno==0) {
                 if(!conflictCheck(i, lits,begin,end)){
                     printf("c RAT check fail !\n");
                     return 0;
                 }
                 goto nextclase;
          }
//
          pivot=toInt(~lits[0]);
          ridx = & RATindex[pivot];
          for(int j=0; j < ridx->size(); j++){
                 newDecisionLevel();
                 int cno=(*ridx)[j];
                 int maxCno=1;
                 if(cno <= 0) cr=clauses[-cno];
                 else{
                         if(cno>i) continue;
                         cr=learnts[cno-1];
                         maxCno=cno;
                 }
                 if(cr == CRef_Undef) readfile(maxCno-1,lits2);
                 else{
                      lits2.clear();
                      Clause & c = ca[cr];
                      if(c.disk()) readfile(cno-1,lits2);
                      else   for(int k=0; k<c.size(); k++) lits2.push(c[k]);
                 }
                 lits3.clear();
                 for(int k=0; k<lits.size(); k++) lits3.push(lits[k]);
                 for(int k=0; k<lits2.size(); k++){
                       if(pivot== toInt(lits2[k])) continue;
                       lits3.push(lits2[k]);
                 }
                
                 if(!conflictCheck(i,lits3,begin,end)){
                     printf("c RAT check fail \n");
                     return 0;
                 }
          }
nextclase: 
          cancelUntil(curLevel);
          verifyflag[i+1] = VERIFIED;
          if(lits.size()==1) unitproof++;
          else proofn++;
     }
     printf("c %d verified inferences in RAT check\n",proofn);
     printf("c proof is verified \n");
     delete []RATindex;
     free(RATvar);
     return 1;
}

int checker :: clauseUnfixed(Lit *lits, int sz)
{
     int j = 0;
     for (int k = 0; k < sz; k++) {
            Lit lit=lits[k];
            if (value(lit) == l_True) return 100;
	    if (value(lit) == l_False) continue;
            j++;
     }
     return j;
}
/*
void checker :: printclause(Lit *lits, int sz)
{
     for (int k = 0; k < sz && k<100; k++) {
            Lit lit=lits[k];
            printf("%7d ",toIntLit(lit));
            if (value(lit) == l_True) {printf("T "); continue;}
	    if (value(lit) == l_False) printf("F ");
   	    else printf("U ");
     }
}
*/
//------------------------------------------------

unsigned int sxhash (Lit * lits,int len) 
{
    unsigned int sum = 0,Xor = 0;
    if(len<=8) sort(lits,len);
    for(int i=0; i<len; i++) {
        int lv= toInt(lits[i]);
        int  w=(len<=8)? lv*(i+1) : lv;
        sum += w;
        Xor ^= lv; 
    }
    return (63* sum + len + (31 * Xor)) % HASHSIZE;
}

void checker :: readdelclause(int i,vec <Lit>  & lits)
{
     int offset=Delqueue[i].target.diskoffset;
     int m=Delqueue[i].timeNo-1;
     off64_t pos = filebase[m/SEG_SIZE]+offset;
     #ifdef  __APPLE__
           fseeko(rat_fp, pos,SEEK_SET);
     #else 
           fseeko64(rat_fp, pos,SEEK_SET);
     #endif
     lits.clear();
     while(1){
          int ilit;
          int ret=fscanf(rat_fp, "%i", &ilit);
          if(ret == EOF) break;
          if(ilit==0) break;
          lits.push(makeLit(ilit));
     }
}

void checker :: detachWatch( vec<Watcher>& ws)
{     int j=0;
      for (int i = 0; i < ws.size(); i++) {
              int  No=ws[i].clsNo;
              if(No>0){
                   CRef cr=learnts[No-1];
                   ca[cr].detach(1);
               }
               else ws[j++]=ws[i];
       }
       ws.shrink(ws.size()-j);
}

void checker :: detachWatch( vec<WatcherL>& ws)
{     int j=0;
      for (int i = 0; i < ws.size(); i++) {
              int  No=ws[i].clsNo;
              if(No>0){
                   CRef cr=learnts[No-1];
                   ca[cr].detach(1);
               }
               else ws[j++]=ws[i];
       }
       ws.shrink(ws.size()-j);
}

void checker :: removeRepeatedCls(int end,int maxlevel)
{
   for (int v = 0; v < nVars(); v++){
   	for (int s = 0; s < 2; s++){
             Lit p = mkLit(v, s);
             watches[p].clear();
             watchesBin[p].clear();
        }
    }
    int core=0;
    for (int i =0; i < clauses.size(); i++){
           CRef cr = clauses[i];
           Clause &  c = ca[cr];
           if(c.detach()) continue;
           attachClause(cr,-i);
           core++;
    }
    vec <int> clsno;
    for(int i=0; i<=end; i++){
          if(filePos[i] == -1) continue;
          CRef cr=learnts[i];
          if(cr == CRef_Undef) continue;
          sort((Lit *)ca[cr], ca[cr].size());
          clsno.push(i);
    }
    sort((int *)clsno, clsno.size(), clause_lt(learnts,ca));
    int repeat=0;
    int btn=0;
    for(int i=0; i<clsno.size()-1; i++){
          int n1=clsno[i];
          CRef cr1=learnts[n1];
          if( cr1 == CRef_Undef ) continue;
          Clause & c1 = ca[cr1];//bug 2017.4.11
          if(c1.size() <4) btn++;
          int n2=clsno[i+1];
          CRef cr2=learnts[n2];
          if( cr2 == CRef_Undef ) continue;
          Clause &  c2 = ca[cr2];
          if( c1.size() != c2.size() ) continue;
          if( c1.detach() && !c2.detach()) c1.detach(0);
          for(int j=0; j<c1.size(); j++) if(c1[j] != c2[j]) goto nextc;
          ca.free(cr2);
          learnts[n2]=CRef_Undef;
          filePos[n2]=-1;
          verifyflag[n1+1] |= verifyflag[n2+1]; 
          repeat++;
 nextc: ;
    }
    printf("c remove %d repeated inferences.\nc %d binary,ternary inferences\n",repeat,btn);
    clsno.clear(true);
    learnt23.clear();
  yes_learnt23 = ((btn>500000) && (nVars()>120000) && (winmode==2)) ||  (nVars() !=origVars) || 10*bintrn>9*clauses.size();
    
    int buff_lim= (nVars()<250000) ? 2*nVars() : 3*nVars(); 
    attClauses=0;
    detachlist.clear();
    for(int i=0; i<=end; i++){
          if(filePos[i] == -1) continue;
          CRef cr=learnts[i];
          if(cr == CRef_Undef) continue;
          if(learnts[i] == CRef_Undef) continue;
          Clause &  c = ca[cr];
          if(c.detach()) {
                detachlist.push(i);
                continue;
          }
          c.detach(1);
          if(i < end-500){
                offtrueClause(cr, i, maxlevel);
                if(learnts[i] == CRef_Undef) continue;
          }
          if(yes_learnt23 && c.size()<=len_lim && learnt23.size() < buff_lim && i < end-5000){
                 learnt23.push(i);
                 continue;
          }
//
          if(c.detach()) attachClause(cr, i+1);
    }
    if(verbosity) printf("c detach # =%d \n",detachlist.size());
} 

inline void checker :: DelRedundancyLit(vec <Lit> & lits,int No)
{
    int newsz = 0;
    for (int k = 0; k < lits.size(); k++) {
         Lit lit=lits[k];
         if (value(lit) == l_False) continue;
         lits[k]=lits[newsz]; lits[newsz++]=lit;
    }
    if(newsz==1 && value(lits[0]) != l_True) uncheckedEnqueue(lits[0],No+1);
    int minL=0x3fffffff;
    int minV=-1;
    for (int k = 0; k < newsz; k++) {
         Lit lit=lits[k];
         if(value(lit) == l_True){
             if(varLevel[var(lit)] < minL){
                      minV=var(lit);
                      minL=varLevel[minV];
              }
         }
    }
    if(minV !=-1){
          trueClause[minV].push(No+1);
          learnts[No] = CRef_Undef;
          return;
    }
    CRef cr=learnts[No]=ca.alloc(lits);
    attachClause(cr,No+1);
    if(newsz<2) newsz=2;
    unsigned delta=lits.size()-newsz;
    if (delta>7) delta=7;
    ca[cr].freesize(delta);
}

void checker :: detachWatch( vec<Watcher>& ws, int begin, int end)
{     int j=0;
      for (int i = 0; i < ws.size(); i++) {
              int  No=ws[i].clsNo-1;
              if(No>=begin && No<=end){
                  CRef cr=learnts[No];
                  if(ca[cr].detach()==0){
                     ca[cr].detach(1);
                     tmpdetach.push(No);
                  }
              }
              else ws[j++]=ws[i];
       }
       ws.shrink_(ws.size()-j);
}

void checker :: detachWatch( vec<WatcherL>& ws, int begin, int end)
{     int j=0;
      for (int i = 0; i < ws.size(); i++) {
              int  No=ws[i].clsNo-1;
              if(No>=begin && No<=end){
                  CRef cr=learnts[No];
                  if(ca[cr].detach()==0){
                       ca[cr].detach(1);
                       tmpdetach.push(No);
                  }
              }
              else ws[j++]=ws[i];
       }
       ws.shrink_(ws.size()-j);
}

void checker :: DetachWatch(int begin, int end)
{   tmpdetach.clear();  
    for (int v = 0; v < nVars(); v++){
        for (int s = 0; s < 2; s++){
             Lit p = mkLit(v, s);
             detachWatch(watches[p],begin,end);
             detachWatch(watchesBin[p],begin,end);
        }
    }
}

bool checker :: restoreAuxUnit()
{
      for(int k=0; k<auxUnit.size(); k++){
              Lit lit=auxUnit[k];
              if(lit == lit_Undef) continue;
              if( assigns[var(lit)] == l_Undef) uncheckedEnqueue(lit); 
              else if( value(lit) == l_False) return true;
      }
      return false;
}
                      
bool checker :: activateDelinfo(int & end, vec <UnitIndex> & c_unit)
{
   if(verbosity) printf("c deleted inf #=%d \n", Delqueue.size());
  
   int maxhsize=0;
   auxUnit.clear();
   hashtbl = new vec<int>[HASHSIZE];
   for(int i=0; i<HASHSIZE; i++) hashtbl[i].clear();
   vec <Lit> lits;
   ok = true;
   int k=0,t=0;
   int matchN=0,nomatch=0;
   vec <Lit> saveU;
   for(int i=0; i<trail.size(); i++) {
           saveU.push(trail[i]);
           reason[var(trail[i])]=cNo_Undef;
   }
   vec <int> olevel;
   int i;
   for(i=0; i<c_unit.size()-1; i++) olevel.push(varLevel[var(c_unit[i].lit)]);
   Lit lt=c_unit[i].lit; 
   int lastl= (value(lt)==l_False) ? trail.size() : varLevel[var(lt)];
   olevel.push(lastl);
   olevel.push(trail.size());
   cancelUntil(0);

   if( origVars != nVars()) HASHBLOCK=600000;

   for (int i =0; i < clauses.size(); i++){
           CRef cr = clauses[i];
           Clause &  c = ca[cr];
           if(c.detach()) {
                  attachClause(cr,-i);
                  c.detach(1);
           } 
   }

   for(int i=0; i<=end; i++){
         while (k<Delqueue.size() && i==Delqueue[k].timeNo){
               readdelclause(k,lits);
               int sz=lits.size();
               int h=sxhash((Lit *)lits, sz);
               if(!match(h, (Lit *)lits,sz,k)){
                      nomatch++;
                      Delqueue[k].timeNo=-i;
               }
               else  matchN++;
               k++;
               checkGarbage();
         }
         if(i>=1200000 && (i%100000==0)) {
                int begin=i-1200000;
                int end=begin+100000;
                DetachWatch(begin, end);
                attClauses -= tmpdetach.size();

                for(int k=begin; k <=end; k++){
                    if(filePos[k] == -1) continue;
                    CRef cr=learnts[k];
                    if(cr == CRef_Undef) continue;
                    if(ca[cr].freesize()) continue;
                    offtrueClause(cr, k,trail.size());
                }

                for(int k=0; k < tmpdetach.size(); k++){
                   int No=tmpdetach[k];
                    CRef cr=learnts[No];
                    if(cr == CRef_Undef) continue;
                    attachClause(cr,No+1);
                }
                tmpdetach.clear();
                checkGarbage();
         }

         if(i>=1000000 && (i%200000==0)) {
                  if(verbosity)  printf("c i=%d \n",i);
                  clearHashtbl(i);
                  if(i>=end-1000000) garbageCollect(); 
         }  
         if(filePos[i] == -1) continue;
         CRef cr=learnts[i];
         if(cr != CRef_Undef) {
                removeClause(i+1); 
                learnts[i] = CRef_Undef;
         }
         readfile(i, lits);
         int sz=lits.size();
         if(sz == 1){
                if(t < c_unit.size() && c_unit[t].idx == i){
                      int curLevel= olevel[t];
                      if(t>0){
                             cancelUntil(decisionLevel()-1);
                             newDecisionLevel();
                             for(int k=olevel[t-1]; k<curLevel; k++) uncheckedEnqueue(saveU[k]);
                      }         
                      int nextLevel= olevel[t+1];
                      newDecisionLevel();
                      t++;
                      qhead=trail.size();
                      for(int k=curLevel; k<nextLevel; k++) uncheckedEnqueue(saveU[k]);
                      restoreAuxUnit();
                      int oldt=trail.size(); 
                      if(var(lits[0]) < origVars){
                            ok=propagateMax(i+1);                      
                            if(!ok) {
                                 end=i; 
                                 goto nexstep;
                            }
                     }
                     if(t < c_unit.size()){
                           auxUnit.push(lit_Undef);
                           for (int c = oldt; c<trail.size();c++) auxUnit.push(trail[c]);
                      }
                 }
                continue;
         }
         DelRedundancyLit(lits,i);
         if(learnts[i] != CRef_Undef){
             if(k<Delqueue.size()){
                  int h=sxhash((Lit *)lits, sz);
                  if(sz == 3){
                        if(match3(h, lits)){
                             removeClause(i+1);
                             learnts[i] = CRef_Undef;
                             goto nextc;
                        }
                  }
         
                  hashtbl[h].push(i+1);
                  if(verbosity && maxhsize<hashtbl[h].size()){
                     maxhsize=hashtbl[h].size();
                  }
              }
         }
         nextc: ;
    }
nexstep:
   for (int i =0; i < learnts.size(); i++){
           CRef cr = learnts[i];
           if(cr == CRef_Undef) continue;
           Clause &  c = ca[cr];
           unsigned int newsize=c.size()-c.freesize();
           c.size(newsize);
           c.freesize(0);
    }
    for(int v=0; v<nVars(); v++){
          if(assigns[v] == l_Undef) restoreTrueClause(v,end);
    }
    c_unit.shrink(c_unit.size()-t);
    int maxlevel=0;
    t=t-1-t/50;
    if(t>0) maxlevel=varLevel[var(c_unit[t].lit)];
    removeRepeatedCls(end,maxlevel);
    garbageCollect(); 

    for(int i=0; i<HASHSIZE; i++) hashtbl[i].clear();
    if(matchN != Delqueue.size()){
      //     for(int i=0; i<HASHSIZE; i++) hashtbl[i].clear();
           clearAllwatch();
           for (int i =0; i < clauses.size(); i++){
                  CRef cr = clauses[i];
                  Clause &  c = ca[cr];
                  if(c.detach()) continue;
                  int h=sxhash((Lit *)c, c.size());
                  hashtbl[h].push(-i);
           }
    }
      
    int j=0;
    for(int i=0; i <Delqueue.size() && i<k; i++){
          if(Delqueue[i].timeNo<0){
                  Delqueue[i].timeNo=-Delqueue[i].timeNo;
                  readdelclause(i,lits);
                  int sz=lits.size();
                  int h=sxhash((Lit *)lits, sz);
                  if(!match(h, (Lit *)lits,sz,i)) continue;
          }
          Delqueue[i].timeNo = Delqueue[i].timeNo-1;
          Delqueue[j++]=Delqueue[i];
    }
    if(c_unit.size()<50 && clauses.size()<200000) watchmode=0;
    else  watchmode=1;
    rebuildwatch(end);

    if(verbosity) printf("c actually deleted inf # =%d \n",j);
    
    Delqueue.shrink(Delqueue.size()-j);
    lastDel=Delqueue.size()-1;
    delete []hashtbl;
    Delq_active=1;

    for(int i=0; i<trail.size(); i++) reason[var(trail[i])]=cNo_Undef;
    return ok;
} 

void checker :: clearHashtbl(int cur_delno)
{  
    for(int h=0; h<HASHSIZE; h++){
          vec<int> & ht=hashtbl[h];
          int sz=ht.size();
          if(sz<16) continue;
          int j=0;
          for(int i=0; i<sz; i++){
               int No=ht[i];
               if(No+HASHBLOCK < cur_delno) continue;
               ht[j++]=ht[i];  
          }
          ht.shrink(sz-j);
     }
}

int checker :: match(int h, Lit * lits, int len, int cur_delp)
{   int eqv=0;
    int reasonNo=cNo_Undef;
    for(int i=0; i<len; i++){
          if(cNo_Undef != reason[var(lits[i])]) reasonNo=reason[var(lits[i])];
          seen[toInt(lits[i])]++;
    }
    if(reasonNo <=0 ) reasonNo=cNo_Undef;
    vec<int> & ht=hashtbl[h];
    int sz=ht.size();
    int j=0;
    for(int i=0; i<sz; i++){
           int No=ht[i];
           if(No == reasonNo) continue;
           CRef cr=getCref(No);
           if(cr == CRef_Undef) continue;
           Clause &  c = ca[cr];
   	   if(c.size() == 0) continue;
   	   if(c.size() == len){
                int m=0;
                for ( m= 0; m < len; m++) {
                       int lt=toInt(c[m]);
          	       if (seen[lt]==0) break;
                }
                if(m>=len){
                    for (i++; i<sz ; i++) ht[j++]=ht[i];
                    Delqueue[cur_delp].target.deletedNo=No;
                    eqv=1;
                    if(No>0){
                           if(c.detach()==0) { detachClause0(c,No); c.detach(1);}
                           if(c.freesize()==0) {
                                  ca.free(cr);
                                  learnts[No-1] = CRef_Undef;
                           }
                    }              
                    else {
                         c.detach(1);
                    }
                    break;
               }
          }
          ht[j++]=ht[i];  
    }
    ht.shrink(sz-j);
    for(int i=0; i<len; i++) seen[toInt(lits[i])]=0;
    return eqv;
}

int checker :: match3(int h, Lit * lits)
{
    vec<int> & ht=hashtbl[h];
    int sz=ht.size();
    if(sz==0) return 0;
    int eqv=0;
    for(int i=0; i<3; i++) seen[toInt(lits[i])]++;
    int j=0;
    for(int i=0; i<sz; i++){
           int No=ht[i]-1;
           if(No > 0) {
                CRef cr = learnts[No];
                if(cr == CRef_Undef) continue;
                Clause &  c = ca[cr];
   	        if(c.size() == 3) {
                    for (int m= 0; m < 3; m++) if(seen[toInt(c[m])]==0) goto next;
                    for (i++; i<sz; i++) ht[j++]=ht[i];
                    eqv=1;
                    break;
                }
            }
    next: 
           ht[j++]=ht[i];  
    }
    for(int i=0; i<3; i++) seen[toInt(lits[i])]=0;
    ht.shrink(sz-j);
    return eqv;
}

void checker :: DetachDelClause()
{ 
    if(Delq_active=0) {lastDel=-1; return;}
    vec <Lit> lits;
    lastDel=Delqueue.size()-1;
    for(int i=0; i<=lastDel; i++){
           DelInfo DI=Delqueue[i];
           int No=DI.target.deletedNo;
           if(No>0){
                   No--;
                   CRef & cr=learnts[No];
                   if( cr != CRef_Undef) {
                           if(ca[cr].size()<2) continue;
                           removeClause(No+1);
                   }
                   lits.clear();
                   learnts[No] = ca.alloc(lits);
           }
           else{
                  CRef cr = clauses[-No];
                  Clause &  c = ca[cr];
                  if(c.detach()==0){
                      c.detach(1);
                      detachClause0(c,No);
                  }
           }
      }
}

struct delInfo_lt {
    delInfo_lt() {} 
    bool operator () (DelInfo x, DelInfo y) { 
       return x.target.deletedNo < y.target.deletedNo;
    }    
};

void checker :: restoreDelClause(int CurNo)
{ 
    int end=lastDel;
    for(; lastDel>=0; lastDel--){
           DelInfo DI=Delqueue[lastDel];
           if(DI.timeNo<CurNo-10) break;
    }
    int begin=lastDel+1;
    sort((DelInfo *)Delqueue+begin, end-lastDel, delInfo_lt());
 
    vec <Lit> lits;
    for(int i=begin; i<=end; i++){
           DelInfo DI=Delqueue[i];
           int No=DI.target.deletedNo;
           if(No>0){
                   No--;
                   CRef cr=learnts[No];
                   if(cr != CRef_Undef){
                          if(ca[cr].detach()) attachClause(cr,No+1);
                          continue;
                   }
                   if(No>=CurNo){
                          learnts[No]=CRef_Undef;
                          continue;
                   }
                   readfile(No, lits);
                   cr = ca.alloc(lits);
                   learnts[No]=cr;
                   if(lits.size() <= len_lim && watchmode){
                          learnt23.push(No);//3
                          ca[cr].detach(1);
                   }
                   else    attachClause2(cr,No+1);
            }
           else{
                  CRef cr = clauses[-No];
                  Clause &  c = ca[cr];
                  if(c.detach()){
                       attachClause2(cr,No);
                       c.detach(0);
                  }
           }
      }
}

void checker:: analyze_used(int confl)
{
    if(verifyflag==0) return;
    vec<Var> scan;
    if(nVars()<500){
          verifyflag[confl] |= USEDFLAG;
simp:
          for (int c = trail.size()-1; c >=0; c--){
               Var  pv  = var(trail[c]);
               int No=reason [pv];
               if (No == cNo_Undef) continue;
               verifyflag[No] |= USEDFLAG;
           }
           return;
    }
    int k=0;
    while(1){
         verifyflag[confl] |= USEDFLAG;
         CRef cr=getCref(confl);
         if(cr == CRef_Undef) break;
         Clause & c = ca[cr];
         for (int i =0; i < c.size(); i++){
               Var pv= var(c[i]);
               if (seen[pv]) continue;
               if (reason [pv] == cNo_Undef) continue;
               scan.push(pv);
               seen[pv]=1;
         }
         if(k>=scan.size()) break;
         Var cv = scan[k++];    
         confl = reason [cv];
    }
    for (int i =0; i < scan.size(); i++) seen[scan[i]]=0;
    if(k<scan.size()) goto simp;
}

