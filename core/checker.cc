/************************************************************************************
Copyright (c) 2017, Jingchao Chen (chen-jc@dhu.edu.cn)
November 18, 2017

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

#define    USEDFLAG       1
#define    VERIFIED       2
#define    TMP_VERIFIED   4

#define    SEG_SIZE  10000
#define    HASHSIZE  500000
 
int HASHBLOCK=2000000;
int display=0;

using namespace treeRat;
  
vec <int> learnt23,savelearnt23;
int yes_learnt23=0;
vec <int> detachlist;
vec <int> tmpdetach;
vec <Lit> auxUnit;
int bintrn=0;
int auxPropSum=0;
int next_clsNo=0x3fffffff;
int len_lim=3;
int watchmode=0;

extern FILE*  traceOutput;
extern bool   tracecheck; 

#define SwapLit(a,b) { Lit t; t=a; a=b; b=t;}

inline Lit makeLit(int lit) { return (lit > 0) ? mkLit(lit-1) : ~mkLit(-lit-1);}

//=================================================================================================
static DoubleOption  opt_garbage_frac      ("CORE", "gc-frac",     "The fraction of wasted memory allowed before a garbage collection is triggered",  0.20, DoubleRange(0, false, HUGE_VAL, false));

//=================================================================================================
inline void checker:: analyze_used(int confl)
{ 
   if(shiftmode){
        if(tracecheck) analyze_used_tmp_trace(confl);
        else analyze_used_tmp_notrace(confl);
        return;
   }
   if(tracecheck) analyze_used_trace(confl);
   else analyze_used_notrace(confl);
}

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
   maxdisFirstvar=0;
   detachlist.clear();
   shiftproof=0;
   shiftmode=false;
   seen.push(0);
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
    seen     .push(0);
    seen     .push(0);
    reason   .push(cNo_Undef);
    varLevel.push(0);
    unitClauseID.push(0);
    return v;
}

bool checker::addClause_(vec<Lit>& ps)
{
    if (!ok) return false;
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
        uncheckedEnqueue(ps[0]);
        return true;
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
{
      Clause& c = ca[cr];
      if(clsNo>0) {
          attClauses++;
      }
      c.detach(0);
      if(c.size() !=2){
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
{   int v=var(p);
    assigns[v] = lbool(!sign(p));
    reason[v]  = from;
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
              if(cNo >= maxCNo) continue;
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

bool checker::propagate3()
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

inline void checker :: printEqRat1(int RatNo, vec <int> & lits)
{
   fprintf(traceOutput, "%i ", getClauseID(RatNo));
   for (int i =0; i < lits.size(); i++) fprintf(traceOutput, "%i ", lits[i]);
   fprintf(traceOutput, "0 0\n");
}         

inline void checker :: printEqRat2(int clsNo, int RatNo, vec <int> & lits)
{
   fprintf(traceOutput, "%i ", getClauseID(clsNo));
   for (int i =0; i < lits.size(); i++) fprintf(traceOutput, "%i ", lits[i]);
   fprintf(traceOutput, "0 -%i 0\n",getClauseID(RatNo));
}         

void checker :: readratOutput(char * rupfile) 
{
      if (!ok) return;
      origIDSize = clauses.size();
      if(tracecheck) TraceOrigClause();
      unitpropagate();
      lit_begin_end.clear();

#ifdef  __APPLE__
        rat_fp  = fopen(rupfile, "r");
#else
        rat_fp  = fopen64(rupfile, "r");
#endif
        if (rat_fp == NULL) {
		fprintf(stderr, "c Error: cannot open the drat file: %s\n", rupfile);
		exit(-1);
	}
        int unitsz=trail.size();
 	printf("c %d units, %d bin-ternary clauses\n",unitsz,bintrn); 

        vec <int> ratLits, lits;
        filePos.clear();
        verifyMark.clear();
        off64_t curpos=0;
        int prelit=0, RatNo=0;
        int curlit;
        origVars=nVars();
        int new_b=0,pre_size=-1;
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
                 if(lits.size()==1) {
                       cur_unit.push(UnitIndex(curIdx,firstL));
                       if(unitClauseID[var(firstL)]==0) unitClauseID[var(firstL)]=curIdx+origIDSize+1;
                 }
                 int m=filePos.size();
               
                 if (verbosity) if(m%500000==0) printf(" f.s=%d \n",m);

                 if( m%SEG_SIZE == 0) filebase.push(curpos);
                 off64_t base = filebase[m/SEG_SIZE];
                 filePos.push(int(curpos-base));
                 curlit=toInt(firstL);
                 if(prelit != curlit){
                       int cur_sz = curIdx-new_b;
                       if(maxdisFirstvar < cur_sz ) maxdisFirstvar = cur_sz;
                       if(cur_sz>100){
                           lit_begin_end.push(prelit);
                           lit_begin_end.push(new_b);
                           if(pre_size==1) lit_begin_end.push(curIdx-1);          
                           else lit_begin_end.push(curIdx);         
                       }
                       prelit=curlit;
                       new_b=curIdx;
                 }
                 pre_size=lits.size();
                 if(newV){
                        verifyMark.push(VERIFIED);
                        RatNo=verifyMark.size();
                        if(tracecheck) printEqRat1(RatNo, lits);
                        lits.copyTo(ratLits);
                        continue;
                 }
                 if(lits.size()>1){
                      if(ratLits.size() && ratLits[0] == -lits[0]){
                            for(int k=1; k<ratLits.size(); k++){
                                 if(ratLits[k] != -lits[1]) continue;
                                 verifyMark.push(VERIFIED);
                                 if(tracecheck) printEqRat2(verifyMark.size(), RatNo,lits);
                                 goto next;
                             }
                       }
                 }
                 verifyMark.push(0);
                 ratLits.clear();
next:            ;
                 
	}
done:
       int curIdx=filePos.size()-1;
       if(curIdx-new_b>100){
             lit_begin_end.push(prelit);
             lit_begin_end.push(new_b);
             lit_begin_end.push(curIdx);
       }
       printf("c %d inferences\n",filePos.size());
       if (verbosity) printf("c fbase.size=%d curpos=%"PRIu64" \n",filebase.size(),curpos);
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
    if(lits.size()>2) sort((Lit *)lits, lits.size(), watch_lt(watches));
    for (int i=0; i<lits.size(); i++){
        Lit p = ~lits[i];
        if (value(p) == l_True ) continue;
        if (value(p) == l_False) {
                 int cv = var(p);
                 int confl=reason [cv];
                 if(confl != cNo_Undef){
                         reason [cv]=cNo_Undef;
                         analyze_used(confl);
                         reason [cv]=confl;
                         return true;
                 }
                 if(tracecheck && unitClauseID[cv]){
                         antecedents.clear();
                         antecedents.push(unitClauseID[cv]);
                 }
                 return true;
        }
        uncheckedEnqueue(p);
   }
   if(watchmode){
      return !propagate();
   }
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
    if(minV !=-1 && (minL <= maxLevel)){
          trueClause[minV].push(No+1);
          if(c.detach()) ca.free(cr);
          else  removeClause(No+1);
          learnts[No] = CRef_Undef;
          return;
    }
}

void checker :: removeProofunit( vec <UnitIndex> & punit)
{
    int j=0;
    int  end = filePos.size()-1;
    for(int i=0; i<punit.size(); i++){
           if(value(punit[i].lit) == l_True) continue;
           if(punit[i].idx > end) break;
           punit[j++]=punit[i];
    }
    punit.shrink(punit.size()-j);
}

void checker :: extractUnit(int & unitproof)
{
    newDecisionLevel();
  //  for(int i=cur_unit.size()-1; i>=0; i--){
    for(int i=0; i<cur_unit.size(); i++){
           Lit lit=cur_unit[i].lit;
           int clsNo=cur_unit[i].idx+1;
           int cv=var(lit);
           if (value(lit) == l_True ){
                 if(verifyflag[clsNo]== VERIFIED) continue;
                 int confl=reason [cv];
                 if(confl != cNo_Undef){
                      reason [cv]=cNo_Undef;
                      analyze_used(confl);
                      reason [cv]=confl;
                      if(tracecheck) traceUnit(clsNo, toIntLit(lit));
                      unitproof++;
                      verifyflag[clsNo] = VERIFIED;
                 }
                 continue;
           }
           if(assigns[cv] != l_Undef) continue;
           newDecisionLevel();
           uncheckedEnqueue(~lit);
           int saveID=unitClauseID[cv];// -lit and lit have different ID
           unitClauseID[cv]=0;
           bool cnf=propagate2();
           unitClauseID[cv]=saveID;
           cancelUntil(1);
           if(cnf == false){
                 if(tracecheck){
                       traceUnit(clsNo, toIntLit(lit));
                 }
                 unitproof++;
                 uncheckedEnqueue(lit);
                 propagate2();
                 verifyflag[clsNo] = VERIFIED;
           }
    }
    cancelUntil(0);
    removeProofunit(cur_unit);
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

void checker :: setvarLevel(vec <UnitIndex> & c_unit)
{  
    if(trueClause==0) trueClause = new vec<int>[nVars()];
    for (int v = 0; v < nVars(); v++){
        trueClause[v].clear();
        varLevel[v]=nVars();
    }
    for(int i=0; i<c_unit.size(); i++){
           Lit lit=c_unit[i].lit;
           varLevel[var(lit)]=i+1;
    }
    for (int i = trail.size()-1; i>=0; i--) varLevel[var(trail[i])]=0;
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

inline void checker :: moveEqTofront(int preIdx, int curIdx, int ppIdx,int & PreEqLen, int c_start)
{      CRef cr1 = learnts[preIdx];
       Clause &  c1 = ca[cr1];
       CRef cr2 = learnts[curIdx];
       Clause &  c2 = ca[cr2];
       for(int n=c1.size()-1; n>=c_start; n--) seen[toInt(c1[n])]=1;
       int curLen=1;
       for(int n=c2.size()-1; n>=c_start; n--) {
                if(seen[toInt(c2[n])]==0) continue;
                curLen++;
                seen[toInt(c2[n])]=2;
       }
       if(curLen > PreEqLen){
                swapEqTofront(c1,2);
                swapEqTofront(c2,2);
                for(int n=c_start; n<curLen; n++) c2[n]=c1[n];
        }
        else{
                if(ppIdx>0 && PreEqLen>0){
                       CRef cr3 = learnts[ppIdx];
                       Clause &  c3 = ca[cr3];
                       for(int n=c_start; n<c3.size(); n++){
                            if(seen[toInt(c3[n])]!=2) continue;
                            seen[toInt(c3[n])]=3;
                        }
                        swapEqTofront(c1,3);
                        swapEqTofront(c2,3);
                        swapEqTofront(c3,3);
                        for(int n=c_start; n<c3.size(); n++){
                            if(seen[toInt(c3[n])]!=3) break;
                            c2[n]=c1[n]=c3[n];
                        }
                }                  
      }
      for(int n=c1.size()-1; n>=c_start; n--) seen[toInt(c1[n])]=0;
      PreEqLen=curLen;
}

inline void checker :: saveDetach(int level,int minNo)
{
    saveDetach(level, minNo, minClauseNo1, detachClsNo1);
}

inline void checker :: saveDetach(int level,int minNo,int & MinClauseNo, vec<int>  & DetachClsNo)
{
    MinClauseNo=minNo;
    vec <Lit> lits;
    DetachClsNo.clear();
    if (trail_lim.size() <= level) return;
    for (int i = trail.size()-1; i >= trail_lim[level]; i--){
          Lit p = ~trail[i];
          vec<WatcherL> & ws = watches[p];
          for (int j = 0; j < ws.size(); j++){
                  if(ws[j].clsNo <= minNo) DetachClsNo.push(ws[j].clsNo);
          }
          vec<Watcher>& ws2 = watchesBin[p];
          for (int j = 0; j < ws2.size(); j++){
                  if(ws2[j].clsNo <= minNo) DetachClsNo.push(ws2[j].clsNo);
          }
    }
    int j=0;
    int dsz=DetachClsNo.size();
    for (int i = 0; i < dsz; i++){
          int cNo=DetachClsNo[i];
          CRef cr=getCref(cNo);
          if( cr == CRef_Undef) continue;
          Clause &  c = ca[cr];
          if(c.detach()) continue;
          DetachClsNo[j++] = DetachClsNo[i];
          detachClause0(c,cNo);
          c.detach(1);
    }
    DetachClsNo.shrink(dsz-j);
}          

inline void checker :: restoreDetach()
{
   restoreDetach(minClauseNo1, detachClsNo1);
}

inline void checker :: restoreDetach(int & MinClauseNo, vec<int>  & DetachClsNo)
{
    int dsz=DetachClsNo.size();
    for (int i = 0; i < dsz; i++){
          int cNo=DetachClsNo[i];
          CRef cr=getCref(cNo);
          if( cr == CRef_Undef) continue;
          if(ca[cr].detach()==0) continue;
          attachClause2(cr, cNo);
    }
    DetachClsNo.clear();
    MinClauseNo=-1;
}
  
inline void checker :: prePropagate(int CurNo)
{
   int MaxLimt=0;
   if(cur_unit.size()) {
         UnitIndex cUnit = cur_unit.last();
         MaxLimt=cUnit.idx+1;
   }
   if(MaxLimt<minClauseNo1  ) MaxLimt=minClauseNo1;
 
   int blocksz=10000;
   if(CurNo-MaxLimt < blocksz) return;
   int start=MaxLimt;
   if(CurNo-MaxLimt >= 2*blocksz) start=CurNo-2*blocksz;
   int mid=(CurNo+start)/2;
   newDecisionLevel();

   clearlearnt23(mid, true);
  
   vec <Lit> lits;
   for(int i=start; i< mid; i++){
           if(filePos[i] == -1) continue;
           CRef cr=learnts[i];
           if(cr != CRef_Undef){
                Clause &  c = ca[cr];
                if(c.size()==0) ca.free(cr);
                else{
                     if(c.detach()) attachClause(cr,i+1);
                     goto unt;
                }
                learnts[i] = CRef_Undef;
           }
           readfile(i,lits);
           if(lits.size() < 2) break;
           cr=learnts[i] = ca.alloc(lits);
           attachClause(cr,i+1);
           ca[cr].canDel(1);
  unt:      
           Clause &  c = ca[cr];
           if(c.size()>8) continue;
           int m=0;
           Lit lit;
           for(int k=0; k<c.size(); k++) {
               if(value(c[k]) == l_False) continue;
               lit=c[k];
               m++;
               if(m>1) break;
           }
           if(m==1){
               if( value(lit) != l_True ) uncheckedEnqueue(lit,i+1);
           }             
   }
 
   qhead=0;
   propagateMax(mid+1);
   saveDetach(decisionLevel()-1,mid, minClauseNo2, detachClsNo2);

   for(int i=start; i< mid; i++){
         CRef cr = learnts[i];
         if(cr == CRef_Undef) continue;
         Clause &  c = ca[cr];
         if(c.canDel()){
               if( c.detach()==0){
                    detachClause0(c, i+1);
                    c.detach(1);
               }
         }
     }
}   

void checker :: clearlearnt23(int maxLimit, bool attachflag)
{   int j=0;
    int sz=learnt23.size();
    for(int i=0; i<sz; i++){
          int n=learnt23[i];
          CRef cr = learnts[n];
          if(cr == CRef_Undef) continue;
          Clause &  c = ca[cr];
          if(n>=maxLimit){
                if(attachflag && c.detach()) attachClause(cr, n+1);
          }
          else{
                learnt23[j++]=n;
                int m=0;
                Lit lit;
                for(int k=0; k<c.size(); k++) {
                     if(value(c[k]) == l_False) continue;
                     if(value(c[k]) == l_True) goto done; 
                     lit=c[k];
                     m++;
                }
                if(m==1) uncheckedEnqueue(lit,n+1);
                done: ;
          }
    }
    learnt23.shrink(sz-j);
}

void checker :: clearlearnt23()
{ 
    for(int i=0; i<learnt23.size(); i++){
          int n=learnt23[i];
          CRef cr = learnts[n];
          if(cr == CRef_Undef) continue;
          if(ca[cr].detach()) attachClause(cr, n+1);
    }
    learnt23.clear();
}

void checker :: restorelearnt23(int maxNo)
{
    for (int v = 0; v < nVars(); v++){
        for (int s = 0; s < 2; s++){
             Lit p = mkLit(v, s);
             detachWatch23(watches[p],   maxNo);
             detachWatch23(watchesBin[p],maxNo);
        }
    }
}

void checker :: blockbackward(int curNo, int begin)
{   vec <Lit> lits;
    if(begin > 800000){
           int dbegin=50000;
           DetachWatch(dbegin, begin-50000);
           reAttachlearnt(dbegin);
    } 
    int localproofn=0, fail=0;
    int old_lastDel=lastDel;
    for(int i=curNo; i>begin; i--){
       if(lastDel>=0 && i<=Delqueue[lastDel].timeNo) restoreDelClause(i);
       if(filePos[i] == -1) continue;
       if(learnts[i] == CRef_Undef){
           if(verifyflag[i+1] != USEDFLAG) continue;
           readfile(i,lits);
           if(lits.size()==1) break;
       }
       else{
           CRef cr=learnts[i];
           Clause & c = ca[cr];
           lits.clear();
           for (int j=0; j < c.size(); j++) lits.push(c[j]);
           if(c.reuse()){
                 if( c.detach()==0) detachClause0(c, i+1);
                 c.detach(1);
           }
           else{
                 if(c.detach()) ca.free(cr);
                 else removeClause(i+1);
                 learnts[i] = CRef_Undef;
           }
           if(verifyflag[i+1] != USEDFLAG) continue;
       }
  
       int orglevel=decisionLevel();
       ok=isconflict(lits);
       if(!ok) {
             qhead=0;
             if(watchmode) ok=!propagate();
             else ok=!propagate2();
       }
       if(!ok) fail++;
       else {
             verifyflag[i+1] = VERIFIED;
             if(tracecheck) printrace(i+1);
             localproofn++;
       }
       cancelUntil(orglevel);
   }
   lastDel=old_lastDel;
   restoreTmpdetach( );
   for(int i=curNo; i>begin; i--){
       if(filePos[i] == -1) continue;
       CRef cr=learnts[i];
       if( cr == CRef_Undef) continue;
       Clause & c = ca[cr];
       if(c.detach()) attachClause(cr,i+1);
   }
   shiftproof += localproofn;
 //  printf(" localproofn=%d fail=%d\n",localproofn,fail);
}

void checker :: restoreTmpdetach( )
{
    for(int k=0; k < tmpdetach.size(); k++){
          int No=tmpdetach[k];
          CRef cr=learnts[No];
          if(cr == CRef_Undef) continue;
          if(ca[cr].detach()) attachClause(cr,No+1);
     }
     tmpdetach.clear();
}

void checker :: reAttachlearnt(int end)
{
   for(int n=0; n< end; n++){
      CRef cr=learnts[n];
      if( cr == CRef_Undef) continue;
      Clause & c=ca[cr];
      if(c.detach() || c.size()<3) continue;
      if(assigns[var(c[0])] == l_Undef && assigns[var(c[1])]==l_Undef) continue;
      detachClause0(c, n+1);
      int m=0;
      for(int k=0; k<c.size(); k++) {
            if(value(c[k]) == l_False) continue;
            SwapLit(c[m],c[k]);m++;
            if(value(c[m]) == l_True) break;
            if(m>=2) break;
      }         
      attachClause(cr,n+1);
   }
}

void checker :: eqvForwardshift(int ulit, int begin, int CurNo)
{    Lit plit=toLit(ulit);
   
     if( begin >= CurNo || begin < 1000 || CurNo-begin<400) return;
    
     if(minClauseNo2 != -1){
           cancelUntil(decisionLevel()-1);
           restoreDetach(minClauseNo2, detachClsNo2);
     }

     if(CurNo-begin>30000) clearlearnt23();

     vec <Lit> lits,prelits;
     int i, j, k;
     int ppIdx=-1,preIdx=-1,preEqvLen=0;
     int bin_idx=-1;
     for(i=begin; i<= CurNo; i++){
           if(filePos[i] == -1){
                learnts[i] = CRef_Undef;
                continue;
           }
           CRef cr=learnts[i];
           if(cr != CRef_Undef){
                Clause &  c = ca[cr];
                if(c.size()==0) ca.free(cr);
                else{
                     if(c.detach()==0) detachClause0(c, i+1);
                     ca[cr].canDel(0);
                     goto det;
                }
                learnts[i] = CRef_Undef;
           }
           readfile(i,lits);
           if(lits.size() < 2) break;
           cr=learnts[i] = ca.alloc(lits);
           ca[cr].canDel(1);
  det:      
           Clause &  c = ca[cr];
           c.detach(1);
           if(bin_idx < 0 && c.size() > 2) bin_idx=i;
           for(j=0; j<c.size(); j++) if(c[j] == plit) break;
           if(j>=c.size()) break;
           if(j>0) { c[j]=c[0]; c[0]=plit;} 
           if(preIdx !=-1) {
                 moveEqTofront(preIdx, i, ppIdx, preEqvLen,1);
           }
           ppIdx=preIdx;
           preIdx=i;
    }
    int end=i-1;
    if(bin_idx < 0 ) bin_idx=begin;
        
 //   printf(" end=%d i=%d bin_idx=%d block size=%d \n", end,i,bin_idx, i-begin);
    
    if(end-begin<400){
           for(i=begin; i< CurNo; i++){
                CRef cr=learnts[i];
                if(cr != CRef_Undef){
                    Clause &  c = ca[cr];
                    if(c.detach()) attachClause(cr,i+1);
                }
           }
           return;
    }
    for (i=end+1; i<=CurNo; i++){
          if(learnts[i] == CRef_Undef) continue;
          Clause & c=ca[learnts[i]];
          if(c.detach()) continue;
          detachClause0(c, i+1);
          c.detach(1);
    }
    for(i=begin; i< bin_idx; i++){
            if(learnts[i] == CRef_Undef) continue;
            Clause & c=ca[learnts[i]];
            if(c.detach()) attachClause(learnts[i],i+1);
    }
   
    newDecisionLevel();
    qhead=0;
    propagateMax(begin);
    int qhead0=trail.size();
    int ilev=decisionLevel();
    int initlev=ilev;
    newDecisionLevel();
    if(value(plit) == l_True){
          antecedents.clear();
          antecedents.push(getClauseID(reason[var(plit)]));
          for(i=begin; i<= end; i++){
               verifyflag[i+1] = VERIFIED;
               if(tracecheck) printrace(i+1);
          }        
    }
    else if(value(plit) != l_False){
           uncheckedEnqueue(~plit);
           propagateMax(bin_idx+1);
           saveDetach(ilev,bin_idx);
         }
         else detachClsNo1.clear();
  
   clearlearnt23(bin_idx, false);
   qhead=0;
   propagateMax(bin_idx+1);
          
   tmp_antecedent.clear();
   tmp_unitID.clear();
   int shift=10000;
   if(bin_idx<=begin+1) shift=200;
   int bsize=end-bin_idx;
   if(bsize<280000) shiftmode=true;
   else  shiftmode=false;
   int localproof=0,fail;
   int localcut = 4; 
   int preNo=0;
   static int dbig=0;

   tmpdetach.clear();
   if(begin>400000){
        int dbegin=1000;
        if(learnts.size()>40000000) dbegin=100000;
        else if(dbig) dbegin=50000;
        DetachWatch(dbegin, begin-5000);
        reAttachlearnt(dbegin);
   }
   int loopNo = (end-bin_idx < 2*shift)? 1 : 0;
   int start=bin_idx;
loop:
    ok=true;
    fail=0;
    for(i=start; i<= end; i++){
       if(i-shift>=bin_idx){
                int m=i-shift;
                CRef cr=learnts[m];
                if( cr != CRef_Undef){
                    Clause & c=ca[cr];
                    if(c.size() > localcut){
                        if(c.detach()==0){
                             detachClause0(c, m+1);
                             c.detach(1);
                        }
                    }      
                }
         }
         int cNo=i+1;
         CRef cr2 = learnts[i];
         if(cr2 == CRef_Undef){
nextc: 
               if(i > start){
                     if(learnts[i-1] != CRef_Undef) attachClause(learnts[i-1],i);
               }
               continue;

         }
         Clause &  c2 = ca[cr2];
         if(verifyflag[cNo] & (VERIFIED | TMP_VERIFIED)){
                if(c2.size()==2){
                    cancelUntil(ilev+1);
                    if(assigns[var(c2[1])] == l_Undef){
                        uncheckedEnqueue(c2[1],cNo);
                        qhead=0; 
                        propagate3();
                    }
                }
                goto nextc;
         }
      
         int dlevel=decisionLevel();
         if( dlevel > ilev+1){
                 int sz=prelits.size();
                 if(sz>c2.size()) sz=c2.size();
                 for(j=1; j<sz; j++) if(prelits[j]!=c2[j]) break;
                 if(j>=sz && sz>=prelits.size()){
                        ca.free(cr2);
                        learnts[i] = CRef_Undef;
                        goto nextc;
                 }
                 if(ilev+j>=dlevel){
                       if(!ok) goto sucess;
                       j=dlevel-ilev;
                 }
                 cancelUntil(ilev+j);
                 sz=prelits.size();
                 int n=0;
                 Lit lit;
                 for(k=j; k<sz; k++){
                      if(value(prelits[k]) == l_False) continue;
                      n++;
                      lit=prelits[k];
                      if(n>1) break;
                 }
                 if(n==1 && assigns[var(lit)] == l_Undef){
                        uncheckedEnqueue(lit,preNo);
                        ok=propagate3();
                   //     ok=propagate2();
                     //   if(watchmode) ok=propagate();
                     //   else ok = propagate2();
                 }
                 else ok=true;
          } 
          else {  cancelUntil(ilev+1);  j=1; ok=true;}
sucess:
          if(i>start){
              if(learnts[i-1] != CRef_Undef) attachClause(learnts[i-1],i);
          }
          if(!ok) goto testok;
          for(k=j; k<c2.size(); k++){
                  newDecisionLevel();
                  Lit clit=~c2[k];
                  if(value(clit) == l_True) continue;
                  if(value(clit) == l_False) {
                       int cv = var(clit);
                       int confl=reason [cv];
                       if(confl != cNo_Undef){
                             reason [cv]=cNo_Undef;
                             analyze_used(confl);
                             reason [cv]=confl;
                             ok=false;
                       }
                       break;
                  }
                  uncheckedEnqueue(clit);
                  ok=propagate3();
                  if(!ok)  break;
           }
testok:
           if(ok) { 
                   qhead=qhead0; 
                   ok = propagate2();
           }
           if(!ok){
                if(shiftmode){
                    tmp_antecedent.push(i);
                    tmp_antecedent.push(cNo_Undef);
                    if(tracecheck) tmp_unitID.push(0);
                    if(loopNo == 0) verifyflag[cNo] |= TMP_VERIFIED;
                 }
                 else{
                    if(tracecheck) printrace(cNo);
                    verifyflag[cNo] |= VERIFIED;
                 }
                 localproof++; 
           }
           else fail++;
           preNo=cNo;
           prelits.clear();
           for(k=0; k<c2.size(); k++) prelits.push(c2[k]);
     }

    // printf(" loop=%d %d verified inferences %d fails\n",loopNo,localproof,fail);
    
    restoreTmpdetach( );
    restoreDetach();
    if(learnts.size()>20000000 && fail>40000) dbig=1;

     if(loopNo == 0 && filePos.size()>35000000 && fail>5000) {
         loopNo = 1;
         ppIdx=-1,preIdx=-1,preEqvLen=0;
         start=bin_idx+100;
         for(i=bin_idx; i<=CurNo; i++){
             CRef cr = learnts[i];
             if(cr == CRef_Undef) continue;
             Clause &  c = ca[cr];
             if(i<start){
                     if(c.detach()) attachClause(cr, i+1);
             }
             else{
                   if(c.detach()==0){
                         detachClause0(c,i+1);
                         c.detach(1);
                   }
                   for(j=0; j<c.size(); j++) if(c[j] == plit) break;
                   if(j>0) { c[j]=c[0]; c[0]=plit;} 
                   if(verifyflag[i+1] & (VERIFIED | TMP_VERIFIED)) continue;
                   if(preIdx !=-1) moveEqTofront(preIdx, i, ppIdx, preEqvLen,1);
                   ppIdx=preIdx;
                   preIdx=i;
             }
         }

         shift=(end-bin_idx)/2;
         if(shift<15000) shift=15000;
         if(shift>50000) shift=50000;
         
         shiftmode=false;
         cancelUntil(ilev);
         newDecisionLevel();
         if(assigns[var(plit)] == l_Undef) uncheckedEnqueue(~plit);
         qhead=0; 
         propagateMax(start+1);
         saveDetach(ilev, start);
         localcut = 6;
         if(begin>800000){
                int dbegin=100000;
                DetachWatch(dbegin, begin-10000);
                reAttachlearnt(dbegin);
         }
         goto loop;
     }

     for(i=bin_idx; i<=CurNo; i++){
         CRef cr = learnts[i];
         int No=i+1;
         if (verifyflag[No] & TMP_VERIFIED) verifyflag[No] = verifyflag[No] & USEDFLAG;
         if(cr == CRef_Undef) continue;
         Clause &  c = ca[cr];
         if(c.canDel()){
                 if( c.detach()==0){
                    detachClause0(c, No);
                    c.detach(1);
                 }
                 continue;
         }
         if(c.detach()) attachClause(cr, No);
         c.reuse(1);
     }

     cancelUntil(initlev-1);

 //printf(" %d localproofs %d fails, tmp_ant=%d \n",localproof,fail,tmp_antecedent.size());

    if(fail>10000 && tmp_antecedent.size()==0) blockbackward(CurNo, bin_idx);

    if(bin_idx+100<CurNo){
        newDecisionLevel();
        if(end == CurNo){
           if(assigns[var(plit)] == l_Undef) uncheckedEnqueue(~plit);
        }
        qhead=0;
        propagateMax(bin_idx+1);
        saveDetach(initlev-1,bin_idx);
     }      
     else minClauseNo1=-1;
   
     shiftproof += localproof;

     shiftmode=false;
     if(tmp_antecedent.size()){
           tmp_antecedent.pop();
           shift_i=tmp_antecedent.pop_();
           if(tracecheck) tmp_unitID.pop();
    }
    else shift_i=-1;
}    

void checker :: moveBlockEqTofront(int begin,int end)
{     vec <Lit> lits;
     int ppIdx=-1,preIdx=-1;
     int preEqvLen=0;
     if(end > learnts.size()) end = learnts.size();
     for(int i=begin; i< end; i++){
           if(filePos[i] == -1) continue;
           CRef cr=learnts[i];
           if(cr != CRef_Undef){
                   if(ca[cr].size()==0) {ca.free(cr); goto readcls;}
                   if(ca[cr].detach()==0) detachClause0(ca[cr], i+1);
                   ca[cr].canDel(0);
                   goto det;
           }
readcls:
           readfile(i,lits);
           cr=learnts[i] = ca.alloc(lits);
           ca[cr].canDel(1);
det:
           ca[cr].detach(1);
           if(preIdx !=-1) moveEqTofront(preIdx, i, ppIdx, preEqvLen,0);
           ppIdx=preIdx;
           preIdx=i;
    }
}

void checker :: moveBlockUsedTofront(int begin,int end)
{     vec <Lit> lits;
     int ppIdx=-1,preIdx=-1;
     int preEqvLen=0;
     if(end > learnts.size()) end = learnts.size();
     for(int i=begin; i< end; i++){
           if(filePos[i] == -1) continue;
           CRef cr=learnts[i];
           if(cr != CRef_Undef){
                   if(ca[cr].size()==0) {ca.free(cr); goto readcls;}
                   if(ca[cr].detach()==0) detachClause0(ca[cr], i+1);
                   ca[cr].canDel(0);
                   goto det;
           }
readcls:
           readfile(i,lits);
           cr=learnts[i] = ca.alloc(lits);
           ca[cr].canDel(1);
det:
           ca[cr].detach(1);
           if(verifyflag[i+1] & VERIFIED) continue;
           if( verifyflag[i+1] != USEDFLAG ) continue;
           if(preIdx != -1) moveEqTofront(preIdx, i, ppIdx, preEqvLen,0);
           ppIdx=preIdx;
           preIdx=i;
    }
}

void checker :: Localbackwardshift(int begin, int end)
{   if(end<begin+10000 || begin<60000) return;
    static bool nofind=false;   
   
//    printf("\n back B=%d E=%d ",begin, end);
//    fflush(stdout);

    int csz=clauses.size();  
    if(end<begin+15000 || csz>3000000 || nofind || (10*bintrn>9*csz && nVars()>150000) ){
        prePropagate((begin+end)/2); // no win shift
        return;
    }
      
    tmpdetach.clear();
    int winsize=30000;
    int mid=begin-winsize;
    DetachWatch(0,begin-50000);
 
    int  cNo,fail=0;
    int k,localproof=0;
    int clevel=decisionLevel ();
    int shiftb=end-winsize+1;
   
    vec <Lit> lits;
    for(int i=mid+1; i < shiftb; i++){
          if(filePos[i] == -1) continue;
          CRef cr=learnts[i];
          if(cr != CRef_Undef){
                   if(ca[cr].size()==0) {ca.free(cr); learnts[i]=CRef_Undef; goto readcls;}
                   if(ca[cr].detach()==0) detachClause0(ca[cr], i+1);
                   ca[cr].canDel(0);
                   goto det;
           }
readcls:
           if(i<begin) continue;
           readfile(i,lits);
           if(lits.size() <=1 ) continue;
           cr=learnts[i] = ca.alloc(lits);
           ca[cr].canDel(1);
det:
           ca[cr].detach(1);
    }
    for(int i=end-1; i>=begin; i--){
         shiftb--;
         CRef cr=learnts[shiftb];
         if( cr != CRef_Undef){
               Clause &  c = ca[cr];
               if(c.detach()){
                     int j=0;
                     for(int k=0; k<c.size(); k++) 
                         if (value(c[k]) != l_False) {
                             SwapLit(c[j],c[k]);
                             j++; 
                             if(j>1)break;
                         }
                     attachClause(cr, shiftb+1);
               }
         }
         if(filePos[i] == -1) continue;
         cNo=i+1;
         if(verifyflag[cNo] != USEDFLAG ) continue;
         cr = learnts[i];
         if(cr == CRef_Undef) continue;
         Clause &  c = ca[cr];
         cancelUntil(clevel);
         if(c.detach()==0){
               detachClause0(c, cNo);
               c.detach(1);
         }
         ok=true;
         for(k=0; k<c.size(); k++){
                 newDecisionLevel();
                 Lit clit=~c[k];
                 if(value(clit) == l_True) continue;
                 if(value(clit) == l_False) {
                       int cv = var(clit); 
                       int confl=reason [cv];
                       if( confl !=cNo_Undef){
                             reason [cv]=cNo_Undef;
                             analyze_used(confl);
                             reason [cv]=confl;
                             ok=false;
                       }
                       break;
                 }
                 uncheckedEnqueue(clit);
               //  if(watchmode) ok=propagate();
               //  else ok=propagate2();
                 ok=propagate2();
                 if(!ok)  break;
         }
         if(!ok){ localproof++; 
                  verifyflag[cNo] |= VERIFIED;
                  if(tracecheck) printrace(cNo);
         }
         else fail++;
    }
    cancelUntil(clevel);
    restoreTmpdetach( );
   int delstart=end-2000;
   for(int i=mid+1; i<end; i++){
         CRef cr = learnts[i];
         if(cr == CRef_Undef) continue;
         int No=i+1;
         Clause &  c = ca[cr];
         if(i>=delstart) c.canDel(0);
         else{
             if(c.canDel()){
                 if( c.detach()==0){
                    detachClause0(c, No);
                    c.detach(1);
                 }
                 continue;
             }
         }
         if(c.detach()) attachClause(cr, No);
    }

    prePropagate((begin+end)/2);
 
 //   printf(" %d verified inferences, %d fails ",localproof,fail);

    if(fail>2000 && fail>3*localproof) nofind=true;
    shiftproof += localproof;
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
    clearAllwatch();
    for (int i =0; i < clauses.size(); i++){
           CRef cr = clauses[i];
           Clause &  c = ca[cr];
           int j = 0, minV=-1;
           int minL=trail.size();
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
                  c.detach(1); 
                  continue;
           }
           attachClause(cr, -i);
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
    DetachWatch(0,CurNo);
    sort(tmpdetach);
    int mid=0;
    if(nVars() >= (origVars+200) && watchmode) mid=tmpdetach.size()-150000;
    if(mid < 0) mid=0;
    attClauses=0;
    for(int k=0; k < tmpdetach.size(); k++){
          int No=tmpdetach[k];
          CRef cr=learnts[No];
          if(k<mid){
                 if(No>1000000 && ca[cr].size()<4) { learnt23.push(No); continue;}
          }
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
                           cancelloadtrueCls(lev, CurNo);
                           return;
                     }
                goto cancel;      
            }
            else printf("c error lev=%d uLit=%d CurNo=%d \n",lev,toIntLit(uLit),CurNo);
     }
}

inline void checker :: restoreTrueClause(int v, int MaxNo)
{    
     if(trueClause == 0) return;
     vec<Lit> lits;
     vec<int> & tc = trueClause[v];
     if(tc.size()==0) return;
     if(tc.size()>2) sort(tc);
     for(int i=0; i<tc.size(); i++){
           int No=tc[i];
           if(No<=0) {
                  CRef cr=clauses[-No];
                  if(ca[cr].detach()){
                         attachClause2(cr, No);
                  }
           }
           else{
                  if(No>MaxNo) continue;
                  No--;
                  CRef cr=learnts[No];
                  if( cr != CRef_Undef) {
                        if(ca[cr].canDel()){
                             ca[cr].canDel(0);
                             if(ca[cr].detach()) attachClause2(cr, No+1);
                        }
                        continue;
                  }
                  readfile(No, lits);
                  cr = ca.alloc(lits);
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
              if(unitClauseID[v]<=maxClauseID) unitClauseID[v]=0;//bug 
              saveV.push(v);
     }
     trail.shrink(trail.size() - first);
     trail_lim.shrink(trail_lim.size() - lev);
     if(trueClause){
         for (int i = saveV.size()-2; i>=0; i--) restoreTrueClause(saveV[i],MaxNo);
     }
     if(first>40000) qhead = first; 
     else {
          int MaxNo=1;
          if(cur_unit.size()) {
               UnitIndex cUnit = cur_unit.last();
               MaxNo=cUnit.idx+1;
          }
          if(verifyflag[MaxNo] != USEDFLAG) qhead = first;
          else {
               qhead=0;
               propagateMax(MaxNo);
          }
     }
}

void checker :: simplifyUnit()
{
    cancelUntil(0);
    newDecisionLevel();
    for(int i=0; i<cur_unit.size(); i++){
          Lit lit = cur_unit[i].lit;
          int v=var(lit);
          if(value(lit) == l_True) continue;
          int clsNo=cur_unit[i].idx+1;
          if(value(lit) == l_False){
                 printEmptyclause1(origIDSize+clsNo, var(lit));
                 ok=false;
          }
          else {
               int saveID=unitClauseID[v];
               unitClauseID[v]=0;
               uncheckedEnqueue(lit);
               ok = propagateMax(1);
               if(!ok) printEmptyclause2();
               unitClauseID[v]=saveID;
          }
          if(!ok){
               filePos.shrink(filePos.size()-clsNo);
               verifyflag[clsNo] |= USEDFLAG;
               break;
          }
          verifyflag[clsNo] |= USEDFLAG;
     }
     if(non_empty){
          qhead=0;
          ok = double_propagate(1);
          if(!ok) printEmptyclause2();
     }
     cancelUntil(0);
}               

bool checker :: double_propagate(int maxNo)
{       bool ret=propagateMax(maxNo);
        if(ret) {
            qhead=0;
            ret=propagateMax(maxNo);
        }
        return ret;
}

void checker :: setAuxUnit(Lit lit,int t)
{

     int cv = var(lit);
     int confl=reason [cv];
     reason [cv]=cNo_Undef;
     if(confl != cNo_Undef){
           int pre_No=-1;
           for(int k=t; k<cur_unit.size(); k++){
                 int No=cur_unit[k].idx;
                 if(pre_No>0 && pre_No != No) break;
                 No++;
                 if(cur_unit[k].lit==lit){
                      analyze_used(confl);
                      if(tracecheck) {
                          traceUnit(No, toIntLit(lit));
                      }
                      verifyflag[No]=VERIFIED;
                      return;
                 }
                 pre_No=No;
           } 
           if(unitClauseID[cv] == 0){
                   analyze_used(confl);
                   unitClauseID[cv]= ++auxClauseID;
                   if(tracecheck) {
                       traceUnit(auxClauseID-origIDSize, toIntLit(lit));
                   }
            }
     }
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
}

bool checker :: finddetachUnit(vec <int> & detachNo)
{    bool ret=false;
     int dp,dsz=detachNo.size();
     for(dp=dsz-1; dp>=0; dp--){
           int n=detachNo[dp];
           CRef cr = learnts[n];
           if(cr == CRef_Undef){
                  dsz--;
                  detachNo[dp]=detachNo[dsz];
                  continue;
           }
           Clause &  c = ca[cr];
           int m=0,j=0;
           for(int k=0; k<c.size(); k++) if (value(c[k]) != l_False) {j++;m=k;}
           if(j==1 && value(c[m]) != l_True ) {
                   uncheckedEnqueue(c[m],n+1);
                   if(c.detach()) attachClause(cr, n+1);
                   dsz--;
                   detachNo[dp]=detachNo[dsz];
                   break;
            }
            if(j==0) { ret=true; analyze_used(n+1);break;}
     }
     detachNo.shrink(detachNo.size()-dsz);
     return ret;
}

bool checker :: checkClauseSAT(int & cls_i)
{    
     for(cls_i--; cls_i>=0; cls_i--){
           CRef cr = clauses[cls_i];
           if(cr == CRef_Undef) continue;
           int j=0;
           Clause &  c = ca[cr];
           if(!c.detach()) continue;
           for(int k=0; k<c.size(); k++) 
               if (value(c[k]) != l_False) {
                      SwapLit(c[j],c[k]);
                      j++; 
                      if(j>1)break;
               }
           if(c.detach()) attachClause(cr, -cls_i);
           if(j==1 && value(c[0]) != l_True ) {
                   uncheckedEnqueue(c[0],-cls_i);
                   if(watchmode) ok=propagate();
                   else ok=propagate2();
                   if(!ok) return true;
                   continue;
            }
            if(j==0) { 
                 analyze_used(-cls_i);
                 return true;
            }
     }
     return false;
}

bool checker :: checklearntSAT(int lrn_i)
{    vec <Lit> lits;
     for(lrn_i--; lrn_i>=0; lrn_i--){
           CRef cr = learnts[lrn_i];
           int j=0;
           if(cr == CRef_Undef) {
                 lits.clear();
                 readfile(lrn_i,lits);
                 for(int k=0; k<lits.size(); k++) 
                    if (value(lits[k]) != l_False) {
                        SwapLit(lits[j],lits[k]);
                        j++; 
                        if(j>1)break;
                    }
                 if(j==1 && value(lits[0]) != l_True ) {
                     uncheckedEnqueue(lits[0],lrn_i+1);
                     if(watchmode) ok=propagate();
                     else ok=propagate2();
                     if(!ok) return true;
                     continue;
                  }
                  if(j==0) { 
                      analyze_used(lrn_i+1);
                      return true;
                  }
                  continue;
           }
           if(!ca[cr].detach()) continue;
           Clause &  c = ca[cr];
           for(int k=0; k<c.size(); k++) 
               if (value(c[k]) != l_False) {
                      SwapLit(c[j],c[k]);
                      j++; 
                      if(j>1)break;
               }
           if(c.detach()) attachClause(cr, lrn_i+1);
           if(j==1 && value(c[0]) != l_True ) {
                   uncheckedEnqueue(c[0],lrn_i+1);
                   if(watchmode) ok=propagate();
                   else ok=propagate2();
                   if(!ok) return true;
                   continue;
            }
            if(j==0) { 
                 analyze_used(lrn_i+1);
                 return true;
            }
     }
     return false;
}

inline void checker :: use_pre_antecedent()
{    int i;
     int m=0;
     for(i=tmp_antecedent.size()-1; i>=0; i -= 2){
           if(tmp_antecedent[i] != cNo_Undef) break;
           m++;
     }
     if(m==0) return;

     if(tracecheck){//unit
         for(int j=tmp_unitID.size()-m; j>=0; j--){
             int ID=tmp_unitID[j];
             if(ID==0) break;
             fprintf(traceOutput, "%i ", ID);
         }
     }
     for(; i>=0; i--){// non-uint
         int No=tmp_antecedent[i];
         if( No == cNo_Undef) return;
         verifyflag[No] |= USEDFLAG;
         if(tracecheck) {
             fprintf(traceOutput, "%i ", getClauseID(No));
         }                  
     }
}

bool checker :: refind(int & cls_i, int lrn_i)
{
    bool  unsat=checkClauseSAT(cls_i);
    if(unsat) return true;
    unsat=checklearntSAT(lrn_i);
    return unsat;
}

extern double initial_time;
                                                    
int checker :: backwardCheck()
{   int shiftusedproof=0;
    attClauses=0;
    printf("c backward check\n");
  
    int maxNo=filePos.size();
    filePos.min_memory(maxNo);
    maxCoreNo=origIDSize;
    verifyflag = (unsigned char * ) calloc (maxCoreNo+maxNo+4, sizeof(unsigned char));
    varusemark = (char * ) calloc (nVars()+1, sizeof(char));

    int csz=clauses.size();  
    if(csz<10000 || (nVars()!=origVars && csz<500000) || (10*bintrn>9*csz && nVars()>450000 && csz<2500000))
          for(int i=0; i <= maxCoreNo; i++) verifyflag[i]=USEDFLAG;
  
    verifyflag += maxCoreNo;
    for(int i=0; i<maxNo; i++) verifyflag[i+1]=verifyMark[i];
    verifyMark.clear(true);
 
    Delqueue.min_memory(Delqueue.size());
    non_empty = true;
    maxClauseID=auxClauseID=origIDSize+maxNo;
    simplifyUnit();
    learnts.clear();
    for(int i=0; i<filePos.size(); i++) learnts.push(CRef_Undef);
    learnts.min_memory(maxNo);
   
    vec <Lit> lits;
    int unproofn=0, proofn=0, unitproof=0;
    cutLen=0x5fffffff;
    extractUnit(unitproof);
    printf("c %d out of %d units are verified in initial step\n",unitproof,cur_unit.size());
    if(nVars()<300000) occLit = (int * ) calloc (2*nVars()+1, sizeof(int));
//    
    if(maxdisFirstvar<5000 || lit_begin_end.size()<=180 || nVars()<=origVars+50){
         lit_begin_end.clear();
         eqvForwardmode=0;
    }
    else eqvForwardmode=1;
    winmode=2;
    int ccnt=0,pre_Sum=0;
    learnt23.clear();
     
    int  end = filePos.size()-1;
    activateDelinfo(end,cur_unit);
 
    save_unit.clear();
    int usz=cur_unit.size();
    for(int i=0; i<usz; i++){
          save_unit.push(cur_unit[i]);
          if(i>=usz-3) varusemark[var(cur_unit[i].lit)]=1;
    }
     
    minClauseNo1=minClauseNo2=-1;
    int clause_i=clauses.size();
    int learnt_i=learnts.size();
    if(non_empty){
        int pre_qhead;
        do{
              pre_qhead=qhead; qhead=0;
              if(watchmode) ok=propagate();
              else ok = propagate2();
        } while (ok && pre_qhead != qhead);
        if(ok){
              ok=!refind(clause_i,learnt_i);
              pre_qhead=0;
              while (ok && pre_qhead != qhead){
                  pre_qhead=qhead;
                  ok=!checklearntSAT(learnt_i);
              }
              if(ok){
                  printf("c there is no empty clause \n");
                  return 0;
              }
        }         
        if(!ok) printEmptyclause2();
    }
    vec <int> varUnitID;
    int  auxUnitmode=0, backshiftbegin=-1, shiftmode=false;
    int  refound=0;
    shift_i=-1;
    for(int i=end; i>=0; i--){
       if(i%1000==0){
            double check_time = cpuTime();
            if(check_time-initial_time>25000) {
                   printf("c time out \n");
                   return 0;
           }
       }
       if(ccnt%40000 == 39999){
           int lsz=learnt23.size();
           if(lsz && (auxPropSum-pre_Sum >50000 || (!yes_learnt23 && lsz<5000))) reducebufferlearnt();
           pre_Sum=auxPropSum;
       }
//
       bool shift_again=false;
       if(shift_i == i){
 shift_done:     
           int cNo=i+1;
           if( verifyflag[cNo] == USEDFLAG ){
                shiftusedproof++;
                verifyflag[cNo]=VERIFIED;
                if(tracecheck) printrace2(cNo);
                else{
                     use_pre_antecedent();
                     while(tmp_antecedent.size()){
                         int No=tmp_antecedent.pop_();
                         if(No==cNo_Undef) break;
                         verifyflag[No] |= USEDFLAG;
                     }
                }
           }
           else{
                while(tmp_antecedent.size()){
                      int No=tmp_antecedent.pop_();
                      if(No==cNo_Undef) break;
                }
                if(tracecheck){
                      while(tmp_unitID.size()){
                          if(0==tmp_unitID.pop_()) break;
                      }
                 }
           }
           if(tmp_antecedent.size()) shift_i=tmp_antecedent.pop_();
           else shift_i=-1;
           if(shift_again) continue;
       }
   
       if(i == minClauseNo2){
           cancelUntil(decisionLevel()-1);
           restoreDetach(minClauseNo2, detachClsNo2);
           if(auxUnitmode) restoreAuxUnit();
       }

       if(i == minClauseNo1){
           cancelUntil(decisionLevel()-1);
           restoreDetach();
       }

       if(lastDel>=0 && i<=Delqueue[lastDel].timeNo) restoreDelClause(i);
       if(i == backshiftbegin) shiftmode=true;
       if(minClauseNo2==-1 && eqvForwardmode==0 && shiftmode){
            shiftmode=false;
            if(cur_unit.size()) {
                UnitIndex beginU = cur_unit.last();
                backshiftbegin=beginU.idx+1;
            }
            else backshiftbegin=0;
            if(backshiftbegin < i-40000) backshiftbegin = i-40000;
            Localbackwardshift(backshiftbegin, i+1);
            backshiftbegin = i-40000;
       }
       if(filePos[i] == -1) continue;
       if(learnts[i] == CRef_Undef){
           lits.clear();
           if(cur_unit.size()){
                UnitIndex cUnit = cur_unit.last();
                if(cUnit.idx == i){
                     if(cur_unit.size()>10000) auxUnitmode=0;
                     cur_unit.pop();
                     lits.push(cUnit.lit);
                     removeTrailUnit(lits[0],i);
                     while(varUnitID.size()) unitClauseID[varUnitID.pop_()]=0;
                     while(auxUnit.size()){
                          Lit lit=auxUnit.last();
                          auxUnit.pop();
                          if(lit == lits[0]) continue;
                          if(lit == lit_Undef) break;
                          varUnitID.push(var(lit));
                          if(unitClauseID[var(lit)]<=maxClauseID){// new Unit must be bigger than it
                              continue;
                          }
                          if( assigns[var(lit)] == l_Undef) uncheckedEnqueue(lit);  
                     }
                     if(auxUnitmode) restoreAuxUnit();
                     if(cur_unit.size()){
                          UnitIndex nextUnit = cur_unit.last();
                          next_clsNo=nextUnit.idx;
                     }
                     else next_clsNo=0;
                     if(i-next_clsNo > 50000){
                           deletewatch(i);
                           if( nVars() == origVars && clauses.size()>30000 && origVars<100000){
                                 sort(learnt23);
                           }
                     }
               }
           }
         
            if(lits.size()==1){
                if(varusemark[var(lits[0])]==0){
                    shiftmode=false;
                    backshiftbegin=-1;
                    continue;
                }
                verifyflag[i+1] |= USEDFLAG;
                shiftmode=true;
           }
           if(verifyflag[i+1] != USEDFLAG) continue;
           if(lits.size() == 0){
                   readfile(i,lits);
                   if(lits.size()==1) continue;
           }
       }
       else{
           CRef cr=learnts[i];
           Clause & c = ca[cr];
           lits.clear();
           for (int j=0; j < c.size(); j++) lits.push(c[j]);
       }
     
       if(verifyflag[i+1] == USEDFLAG && lits.size()>1){
           if(eqvForwardmode && lit_begin_end.size()>2){
               int last=lit_begin_end.last();
               if(i<last){
                  lit_begin_end.pop();
                  int lbegin=lit_begin_end.pop_();
                  int uLit=lit_begin_end.pop_();
                  eqvForwardshift(uLit, lbegin, i);
               }
           }
       }

       if(learnts[i] != CRef_Undef){
           CRef cr=learnts[i];
           Clause & c = ca[cr];
           if(c.detach()) ca.free(cr);
           else removeClause(i+1);
           learnts[i] = CRef_Undef;
       }

       if(verifyflag[i+1] != USEDFLAG) continue;
       if(shift_i == i){
             shift_again=true;
             goto shift_done;
       } 
       if(minClauseNo2 == -1 && eqvForwardmode && (minClauseNo1>0 || lit_begin_end.size()< 2))
             prePropagate(i);
  
       int orglevel=decisionLevel();
       if(refound){
             qhead=0;
             newDecisionLevel();
             if(watchmode) propagate();
             else propagate2();
             refound=0;
       }    
       int v0=var(lits[0]);
       int saveID=unitClauseID[v0];
       unitClauseID[v0] = 0;
       ok=isconflict(lits);
       ccnt++;
       if(!ok) {
             refound=1;
             int pre_qhead=qhead;
             qhead=0;
             if(watchmode) ok=!propagate();
             else ok=!propagate2();
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
                   ok=finddetachUnit(detachlist);
                   if(!ok && qhead != trail.size()){ pre_qhead=0; goto retry;}
             }

           //  if(!ok && unproofn==0){
           //      ok=refind(clause_i,i);
           //  }

             cancelUntil(orglevel);
             if(auxUnitmode==1){ auxUnitmode=2; restoreAuxUnit();}
       }
       if(!ok) {
            if(unproofn==0) filePos.shrink_(filePos.size()-1-i);
            unproofn++;
       }
       else {
             verifyflag[i+1] = VERIFIED;
             if(tracecheck) printrace(i+1);
             if(lits.size()==1) unitproof++;
             else proofn++;
       }
       cancelUntil(orglevel);
       unitClauseID[v0]=saveID;
   }
   printf("\nc %d inferences, %d units are verified\n",proofn,unitproof);
   if(shiftusedproof) 
         printf("c %d out of %d verified inferences is useful in shift step\n",shiftusedproof,shiftproof);
   else  printf("c %d inferences are verified in shift step\n",shiftproof);
   printf("c %d deleted inferences\n",Delqueue.size());
   if(unproofn){
         printf("\nc so far %d inferences are not verified\n",unproofn);
         auxUnit.clear();
         return RATCheck();
   }

   printf("c proof is verified\n");
   fclose(rat_fp);
   if(tracecheck) fclose(traceOutput);
   return 1;
}

//-----------------------------------------RAT check
void checker :: setRATvar()
{
    clearAllwatch();
    for(int  i=0; i<filePos.size(); i++){
           if(filePos[i] == -1) continue;
           if(learnts[i] != CRef_Undef){
               ca.free(learnts[i]);
               learnts[i] = CRef_Undef;
          }
    }
    garbageCollect();
 
    vec<Lit> lits;
    RATvar = (char  * ) calloc (nVars()+1, sizeof(char));
    for(int  i=0; i<filePos.size(); i++){
           if(filePos[i] == -1) continue;
           if(verifyflag[i+1] != USEDFLAG) continue;
           readfile(i,lits);
           RATvar[var(lits[0])]=1;
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
        attachClause(cr,-i); 
        setRATindex(ca[cr],-i);
    }
    vec<Lit> lits;
    for(int  i=0; i<filePos.size(); i++){
         if(filePos[i] == -1) continue;
         readfile(i,lits);
         for(int j=0; j<lits.size(); j++) {
               if(RATvar[var(lits[j])]) RATindex[toInt(lits[j])].push(i+1);
         }
    }
}       

bool checker :: conflictCheck(int No, vec<Lit> & lits,int & begin,int end)
{
     int first=1;
     int clause_i=clauses.size();
     ok=isconflict(lits);
     while(!ok){
          if(first) {
                qhead=first=0;
                if(watchmode) ok=propagate();
                else ok = propagate2();
          }
          if(ok) break;
          int old_qhead=qhead;
          ok=refind(clause_i,No);
          if(ok) break;
          if(old_qhead==qhead) break;
     }
     cancelUntil(decisionLevel()-1);
     return ok;
}
   
int checker :: RATCheck()
{
    cancelUntil(0);
    setRATvar();
    buildRATindex();
    cutLen=0x5fffffff;
    int begin=0;
    learnt23.clear(true);   
    int end= filePos.size()-1;
    winmode=3;
//
    cur_unit.clear();
    for(int i=0; i<save_unit.size(); i++){
            cur_unit.push(save_unit[i]);
            unitClauseID[var(save_unit[i].lit)]=save_unit[i].idx+origIDSize+1;
    }
    activateDelinfo(end, cur_unit);
     
    CRef cr;
    vec<Lit> lits,lits2,lits3;
    int pivot;
    int proofn=0,unitproof=0;
    vec<int> *ridx;
    eqvForwardmode=0;
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
          if(tracecheck) printracHead(i+1,lits);

          if(lits.size() == 1) removeTrailUnit(lits[0],i);
          int curLevel=decisionLevel();
          int rno=removeRATindex (lits, i+1);
          if(rno==0) {
                 if(!conflictCheck(i, lits,begin,end)){
                     printf("c the %d-th inference RAT check fails!\n",i);
                     return 0;
                 }
                 goto nextclase;
          }
//
          if(tracecheck) printracHead(i+1, lits);
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
                     // if(c.disk()) readfile(cno-1,lits2);
                     // else
                      for(int k=0; k<c.size(); k++) lits2.push(c[k]);
                 }
                 lits3.clear();
                 for(int k=0; k<lits.size(); k++) lits3.push(lits[k]);
                 for(int k=0; k<lits2.size(); k++){
                       if(pivot== toInt(lits2[k])) continue;
                       lits3.push(lits2[k]);
                 }
                
                 if(!conflictCheck(i,lits3,begin,end)){
                     printf("c The %d-th inference RAT check fails \n",i);
                     return 0;
                 }
                 if(tracecheck) printRatBody(cno);
          }
nextclase: 
          cancelUntil(curLevel);
          verifyflag[i+1] = VERIFIED;
          if(tracecheck) printraceEnd();
          if(lits.size()==1) unitproof++;
          else proofn++;
     }
     printf("c %d verified inferences in RAT check\n",proofn);
     printf("c proof is verified \n");
     delete []RATindex;
     free(RATvar);
     return 1;
}

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
          Clause & c1 = ca[cr1];
          if(c1.size() <4) btn++;
          int n2=clsno[i+1];
          if( verifyflag[n2+1] ) continue;
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
    printf("c remove %d repeated inferences\nc %d binary,ternary inferences\n",repeat,btn);
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
    //if(verbosity) printf("c detach # =%d \n",detachlist.size());
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

void checker :: detachWatch23( vec<Watcher>& ws, int end)
{     int j=0;
      for (int i = 0; i < ws.size(); i++) {
              int  No=ws[i].clsNo-1;
              if(No>=0 && No<=end){
                 CRef cr=learnts[No];
                 int sz=ca[cr].size();
                 if(sz==2 || sz==3){
                     if(ca[cr].detach()==0){
                         ca[cr].detach(1);
                         learnt23.push(No);
                     }
                     continue;
                 }
              }
              ws[j++]=ws[i];
       }
       ws.shrink_(ws.size()-j);
}

void checker :: detachWatch23( vec<WatcherL>& ws, int end)
{     int j=0;
      for (int i = 0; i < ws.size(); i++) {
              int  No=ws[i].clsNo-1;
              if(No>=0 && No<=end){
                  CRef cr=learnts[No];
                  int sz=ca[cr].size();
                  if(sz==2 || sz==3){
                     if(ca[cr].detach()==0){
                         ca[cr].detach(1);
                         learnt23.push(No);
                     }
                     continue;
                  }
              }   
              ws[j++]=ws[i];
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

void checker :: DetachWatch2(int begin, int end)
{   tmpdetach.clear();  
    for (int v = 0; v < nVars(); v++){
        for (int s = 0; s < 2; s++){
             Lit p = mkLit(v, s);
             detachWatch(watches[p],begin,end);
         //    detachWatch(watchesBin[p],begin,end);
        }
    }
}

bool checker :: restoreAuxUnit()
{
      for(int k=0; k<auxUnit.size(); k++){
              Lit lit=auxUnit[k];
              if(lit == lit_Undef) continue;
              if( assigns[var(lit)] == l_Undef) uncheckedEnqueue(lit); 
              else 
                  if( value(lit) == l_False ){
                       int cv = var(lit);
                       int confl=reason [cv];
                       if(confl != cNo_Undef){
                             reason [cv]=cNo_Undef;
                             analyze_used(confl);
                             reason [cv]=confl;
                       }
                       return true;
                  }
      }
      return false;
}

void checker :: activateDelinfo(int & end, vec <UnitIndex> & c_unit)
{
   for(int i=c_unit.size()-1; i>=0; i--){
         if(c_unit[i].idx <= end) { c_unit.shrink(cur_unit.size()-i-1); break;}
   }
   setvarLevel(c_unit);
 
   int maxhsize=0;
   auxUnit.clear();
   hashtbl = new vec<int>[HASHSIZE];
   for(int i=0; i<HASHSIZE; i++) hashtbl[i].clear();
   vec <Lit> lits;
   int k=0,t=0;
   int matchN=0,nomatch=0;
   cancelUntil(0);
   if( origVars != nVars()) HASHBLOCK=600000;
   for(int i=0; i<=end; i++){
        while (k<Delqueue.size() && i==Delqueue[k].timeNo){
               readdelclause(k,lits);
               int sz=lits.size();
               int h=sxhash((Lit *)lits, sz);
               if(!match(h, (Lit *)lits,sz,k)){
                      nomatch++;
                      Delqueue[k].timeNo=-i;
               }
               else matchN++;
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
                    offtrueClause(cr, k, t+1);
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
                      int not_next=1;
                      if(t>0){
                             cancelUntil(decisionLevel()-1);
                             newDecisionLevel();
                             Lit lit=c_unit[t-1].lit;
                             int v=var(lit);
                             if(assigns[v] == l_Undef) uncheckedEnqueue(lit);
                      }         
                      newDecisionLevel();
                      qhead=trail.size();
                      int v=var(lits[0]);
                      if(assigns[v] == l_Undef) uncheckedEnqueue(c_unit[t].lit);
                      t++;
                      for(int k=0; k<auxUnit.size(); k++){
                            if(lits[0]==auxUnit[k]){ 
                               not_next=0;
                               break;
                            }
                      }                      
                      if(not_next) restoreAuxUnit();
                      int oldt=trail.size(); 
                      if(var(lits[0]) < origVars && not_next){
                            ok=propagateMax(i+1);                      
                            if(!ok) {
                                 end=i;
                                 printEmptyclause2(); 
                                 goto nexstep;
                            }
                     }
                     if(t < c_unit.size()){
                           auxUnit.push(lit_Undef);
                           for (int c = oldt; c<trail.size();c++){
                                   Lit lit=trail[c];
                                   setAuxUnit(lit,t-1);
                                   auxUnit.push(lit);
                           }
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
           c.freesize(0);
          // if(tracecheck) continue;
          // unsigned int newsize=c.size()-c.freesize();
          // c.size(newsize);
    }
    for(int v=0; v<nVars(); v++){
          if(assigns[v] == l_Undef) restoreTrueClause(v,end);
    }
    c_unit.shrink(c_unit.size()-t);
    removeRepeatedCls(end,t);
    garbageCollect(); 
    for(int i=0; i<HASHSIZE; i++) hashtbl[i].clear();
    if(matchN != Delqueue.size()){
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
    if(c_unit.size()<100 && clauses.size()<2000000 || origVars != nVars() || nVars()>350000) watchmode=0;
    else  watchmode=1;
    rebuildwatch(end);

    if(verbosity) printf("c actually deleted inf # =%d \n",j);
    
    Delqueue.shrink(Delqueue.size()-j);
    lastDel=Delqueue.size()-1;
    delete []hashtbl;
    Delq_active=1;
    for(int i=0; i<trail.size(); i++) reason[var(trail[i])]=cNo_Undef;
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
                          ca[cr].canDel(0);
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
                   else   attachClause2(cr,No+1);
            }
           else{
                  CRef cr = clauses[-No];
                  Clause &  c = ca[cr];
                  if(c.detach()){
                       attachClause2(cr,No);
                  }
           }
      }
}

void checker:: analyze_used_notrace(int confl)
{
    if(verifyflag==0) return;
    vec<Var> scan;
    if(nVars()<500){
          verifyflag[confl] |= USEDFLAG;
simp:
          for (int c = trail.size()-1; c >=0; c--){
               Var  pv  = var(trail[c]);
               int No=reason [pv];
               if (No == cNo_Undef) {
                      if(unitClauseID[pv]) varusemark[pv]=1;
                      continue;
               }
               verifyflag[No] |= USEDFLAG;
          }
           return;
    }
    int k=0;
    while(1){
         verifyflag[confl] |= USEDFLAG;
         CRef cr=getCref(confl);
         if(cr == CRef_Undef){
               if(confl<=0) break;
               detachClsNo1.push(confl);
               vec <Lit> lits;
               readfile(confl-1,lits);
               cr=learnts[confl-1] = ca.alloc(lits);
               ca[cr].detach(1);
         }
         Clause & c = ca[cr];
         for (int i =0; i < c.size(); i++){
               Var pv= var(c[i]);
               if (seen[pv]) continue;
               if (reason [pv] == cNo_Undef){
                   if(unitClauseID[pv]) varusemark[pv]=1;
                   continue;
               }
               scan.push(pv);
               seen[pv]=97;
         }
         if(k>=scan.size()) break;
         Var cv = scan[k++];    
         confl = reason [cv];
    }
    for (int i =0; i < scan.size(); i++) seen[scan[i]]=0;
    if(k<scan.size()) goto simp;
}

void checker:: analyze_used_trace(int confl)
{   
    int i=trail.size()-1;
    antecedents.clear();
    antecedents.push(getClauseID(confl));
    int pre_v=-1;
    while(i>=0){
         verifyflag[confl] |= USEDFLAG;
         CRef cr=getCref(confl);
         if(cr == CRef_Undef) {
              if(confl<=0) break;
              detachClsNo1.push(confl);
              vec <Lit> lits;
              readfile(confl-1,lits);
              cr=learnts[confl-1] = ca.alloc(lits);
              ca[cr].detach(1);
         }
         Clause & c = ca[cr];
         for (int k =0; k < c.size(); k++) seen[var(c[k])]=98;
         if(pre_v>=0)  seen[pre_v]=0;
         for(; i>=0; i--){
              Var  pv  = var(trail[i]);
              if (seen[pv]==0) continue;
              seen[pv]=0;
              confl=reason [pv];
              if (confl == cNo_Undef){
                   if(unitClauseID[pv]){
                        varusemark[pv]=1;
                        antecedents.push(unitClauseID[pv]);
                   }
                   continue;
              }
              antecedents.push(getClauseID(confl));
              i--; pre_v=pv;
              break;
         }
    }
    if(pre_v>=0) seen[pre_v]=0;
    for(; i>=0; i--){
          Var  pv  = var(trail[i]);
          seen[pv]=0;
          confl=reason [pv];
          if (confl == cNo_Undef){
                 if(unitClauseID[pv]){
                        varusemark[pv]=1;
                        antecedents.push(unitClauseID[pv]);
                 }
          }
          else  {
              verifyflag[confl] |= USEDFLAG;
              antecedents.push(getClauseID(confl));
          }
    }
}

void checker:: analyze_used_tmp_trace(int confl)
{   
    int i=trail.size()-1;
    tmp_antecedent.push(confl);
    int pre_v=-1;
    while(i>=0){
         CRef cr=getCref(confl);
         if(cr == CRef_Undef) {
              vec <Lit> lits;
              readfile(confl-1,lits);
              cr=learnts[confl-1] = ca.alloc(lits);
              ca[cr].detach(1);
         }
         Clause & c = ca[cr];
         for (int k =0; k < c.size(); k++) seen[var(c[k])]=99;
         if(pre_v>=0)  seen[pre_v]=0;
         for(; i>=0; i--){
              Var  pv  = var(trail[i]);
              if (seen[pv]==0) continue;
              seen[pv]=0;
              confl=reason [pv];
              if (confl == cNo_Undef){
                   if(unitClauseID[pv]){
                      varusemark[pv]=1;
                      tmp_unitID.push(unitClauseID[pv]);
                   }
                   continue;
              }
              tmp_antecedent.push(confl);
              i--; pre_v=pv;
              break;
         }
    }
    if(pre_v>=0)  seen[pre_v]=0;
}

void checker:: analyze_used_tmp_notrace(int confl)
{   
    int i=trail.size()-1;
    if(confl>0) tmp_antecedent.push(confl);
    int pre_v=-1;
    while(i>=0){
         CRef cr=getCref(confl);
         if(cr == CRef_Undef) {
              vec <Lit> lits;
              readfile(confl-1,lits);
              cr=learnts[confl-1] = ca.alloc(lits);
              ca[cr].detach(1);
         }
         Clause & c = ca[cr];
         for (int k =0; k < c.size(); k++) seen[var(c[k])]=100;
         if(pre_v>=0)  seen[pre_v]=0;
         for(; i>=0; i--){
              Var  pv  = var(trail[i]);
              if (seen[pv]==0) continue;
              seen[pv]=0;
              confl=reason [pv];
              if (confl == cNo_Undef){
                    if(unitClauseID[pv]) varusemark[pv]=1;
                    continue;
              }
              tmp_antecedent.push(confl);
              i--; pre_v=pv;
              break;
         }
    }
    if(pre_v>=0)  seen[pre_v]=0;
}

//tracecheck ===============================================
void checker :: printracHead(int clsNo, vec <Lit> & lits)
{
   fprintf(traceOutput, "%i ", getClauseID(clsNo));
   if(lits.size()==0){
        CRef cr=getCref(clsNo);
        if( cr != CRef_Undef){
              Clause & c = ca[cr];
              for (int i =0; i < c.size(); i++) fprintf(traceOutput, "%i ", toIntLit(c[i]));
              return;
        }
        readfile(clsNo-1, lits);
    }
    for (int i =0; i < lits.size(); i++) fprintf(traceOutput, "%i ", toIntLit(lits[i]));
}         

void checker:: printrace(int clsNo)
{
   vec <Lit> lits;
   printracHead(clsNo, lits);
   fprintf(traceOutput, "0 ");
   int sz=antecedents.size()-1;
   for (int i=sz; i>=0; i--) fprintf(traceOutput, "%i ", antecedents[i]);
   fprintf(traceOutput, "0\n");
}         

void checker:: printrace2(int clsNo)
{
   vec <Lit> lits;
   printracHead(clsNo, lits);
   fprintf(traceOutput, "0 ");
   while(tmp_unitID.size()){
         int ID=tmp_unitID.pop_();
         if(ID==0) break;
         fprintf(traceOutput, "%i ", ID);
   }
 
   use_pre_antecedent();
   while(tmp_antecedent.size()){
         int No=tmp_antecedent.pop_();
         if(No==cNo_Undef) break;
         verifyflag[No] |= USEDFLAG;
         fprintf(traceOutput, "%i ", getClauseID(No));
   }   
   fprintf(traceOutput, "0\n");
}         

void checker:: printRatBody(int clsNo)
{
   fprintf(traceOutput, "0 -%i",getClauseID(clsNo));
   for (int i=antecedents.size()-1; i>=0; i--) fprintf(traceOutput, "%i ", antecedents[i]);
}         

void checker:: printraceEnd()
{
   fprintf(traceOutput, "0\n");
}

void checker:: traceUnit(int clsNo,int lit)
{  int ID=getClauseID(clsNo);
   fprintf(traceOutput, "%i %i 0 ", ID,lit);

   int sz=antecedents.size()-1;
   for (int i=sz; i>=0; i--)
           if(antecedents[i] != ID) fprintf(traceOutput, "%i ", antecedents[i]);
   fprintf(traceOutput, "0\n");
}         

void checker:: TraceOrigClause()
{   antecedents.clear();
    for(int i=0; i<clauses.size(); i++) printrace(-i);
    for(int i=0; i<trail.size(); i++){//unit
          unitClauseID[var(trail[i])] = ++origIDSize;
          fprintf(traceOutput, "%i %i 0 0\n",origIDSize, toIntLit(trail[i]));
    }
}

void checker:: unitpropagate()
{
    int ori_fixed=trail.size();
    ok= propagateMax(1);
    for(int i=ori_fixed; i<trail.size(); i++){
          Var cv = var(trail[i]);    
          if(tracecheck) {
              unitClauseID[cv] = ++origIDSize;
              fprintf(traceOutput, "%i ",origIDSize);
              int cNo = reason [cv];
              CRef cr=getCref(cNo);
              Clause & c = ca[cr];
              for (int j =0; j < c.size();j++) fprintf(traceOutput, "%i ",toIntLit(c[j]));
              fprintf(traceOutput, "0 ");
              for (int j =0; j < c.size();j++)
                  if(cv != var(c[j])) fprintf(traceOutput, "%i ",unitClauseID[var(c[j])]);
              fprintf(traceOutput, "0\n");
           }
           reason [cv]=cNo_Undef;
    }
}

void checker:: printEmptyclause1(int clsID, int cv)
{
     if(!non_empty) return;
     if(!tracecheck || unitClauseID[cv]){
           non_empty=false;
           printf("c Empty clause is detected\n");
           if(tracecheck) fprintf(traceOutput, "%i 0 %i %i 0\n", ++auxClauseID, clsID, unitClauseID[cv]);
           return;
     }
     int confl=reason [cv];
     reason [cv]=cNo_Undef;
     analyze_used_trace(confl);
     reason [cv]=confl;
     antecedents.push(clsID);
     printEmptyclause2();
}

void checker:: printEmptyclause2()
{
   if(!non_empty) return;
   non_empty=false;
   printf("c empty clause is detected\n");
   if(tracecheck) {
       fprintf(traceOutput, "%i 0 ", ++auxClauseID);
       for (int i=antecedents.size()-1; i>=0; i--) fprintf(traceOutput, "%i ", antecedents[i]);
       fprintf(traceOutput, "0\n");
   }
}

