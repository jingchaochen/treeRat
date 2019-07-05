/************************************************************************************
Copyright (c) 2019, Jingchao Chen (chen-jc@dhu.edu.cn)
June 5, 2019

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
#include <cstdio>
#include "mtl/Sort.h"
#include "utils/System.h"
#include "core/checker.h"

#define ABS(x) ((x)>0 ? (x) : (-x) )

#define    USEDFLAG       1
#define    VERIFIED       2
#define    TMP_VERIFIED   4

#define    SEG_SIZE  10000
#define    HASHSIZE  500000
 
int HASHBLOCK=2000000;
int coreMode=0;
int coreNum=0;
  
using namespace treeRat;
  
vec <int> detachlist;

vec <int> tmpdetach;
vec <Lit> auxUnit;
int bintrn=0;
bool movetoFront=false;

extern FILE*  traceOutput;
extern bool   tracecheck; 
extern const char * Trace_file;

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

inline void checker::uncheckedEnqueue(Lit p, int from)
{   int v=var(p);
    assigns[v] = lbool(!sign(p));
    reason[v]  = from;
    trail.push_(p);
}

checker::checker() :
    ok                 (true)
  , garbage_frac     (opt_garbage_frac)
  , verbosity        (0)
  , qhead            (0)
{
   remNum=0;
   lastDel=-1;
   trueClause=0;
   Delq_active=0;
   verifyflag=0;
   maxdisFirstvar=0;
   detachlist.clear();
   shiftproof=0;
   shiftmode=false;
   seen.push(0);
   unitID_idx=-1;
}

checker::~checker()
{
}

//=================================================================================================
// Minor methods:
Var checker::newVar()
{  int v = nVars();
    corewatch .init(mkLit(v, false));
    corewatch .init(mkLit(v, true ));
    watches   .init(mkLit(v, false));
    watches   .init(mkLit(v, true ));
    watchesBin.init(mkLit(v, false));
    watchesBin.init(mkLit(v, true ));
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

struct watch_lts {
    OccLists<Lit, vec<WatcherL> >  & ws;
    watch_lts( OccLists<Lit, vec<WatcherL> >  & ws_):ws(ws_){} 
    bool operator () (Lit x, Lit y) { 
         return ws[~x].size() < ws[~y].size();
    }    
};

struct watch_lt {
    OccLists<Lit, vec<WatcherL> >  & ws;
    OccLists<Lit, vec<Watcher>  >  & wsB;
    watch_lt( OccLists<Lit, vec<WatcherL> >  & ws_, OccLists<Lit, vec<Watcher>  >  & wsB_):ws(ws_),wsB(wsB_){} 
    bool operator () (Lit x, Lit y) { 
         return ws[~x].size() + wsB[~x].size() < ws[~y].size()+wsB[~y].size();
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

void checker::attachClause(CRef cr, int clsNo) 
{   Clause & c = ca[cr];
    c.detach(0);
    if(c.coreC()){
        corewatch[~c[0]].push(WatcherL(clsNo,cr));
        corewatch[~c[1]].push(WatcherL(clsNo,cr));
        return;
    }
    if(c.size()==2) {
      watchesBin[~c[0]].push(Watcher(clsNo, c[1]));
      watchesBin[~c[1]].push(Watcher(clsNo, c[0]));
    } else {
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
   if(c.coreC()){
        remove3(corewatch[ ~c[0] ], clsNo);
        remove3(corewatch[ ~c[1] ], clsNo);
        return;
   }
   if(c.size()==2) {
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

//------------------------------------------
bool checker::propagateMax(int maxCNo)
{   
    while (qhead < trail.size()){
        Lit            p   = trail[qhead++];
        vec<Watcher> &  wbin  = watchesBin[p];
        for(int k = wbin.size()-1; k>=0; k--) {
	      Watcher & wk= wbin[k];
	      Lit imp = wk.blocker;
              if(value(imp) == l_True) continue;
              int cNo=wk.clsNo;
              if(cNo >= maxCNo) continue;
              int v=var(imp);
              if(assigns[v] == l_Undef){
                   assigns[v] = lbool(!sign(imp));
                   reason[v]  = cNo;
                   trail.push_(imp);
                   continue;
              }
              analyze_used(cNo);
              return false;
        }
        vec<WatcherL> &  ws  = watches[ p ];
        Lit  false_lit = ~p;
        int wsize=ws.size();
        for (int i=0; i <wsize; i++){
 	    WatcherL & wi= ws[i];
            int cNo = wi.clsNo;
            if(cNo >= maxCNo) continue;
            CRef    cr = wi.cr;
            Clause & c = ca[cr];
            if(value(c[0]) == l_True || value(c[1]) == l_True) continue;
            if (c[0] == false_lit) c[0]=c[1];
            int sz= c.size();
            for (int m = 2; m < sz; m++) {
               if (value(c[m]) != l_False){
		     c[1] = c[m]; c[m] = false_lit;
	 	     watches[ ~c[1]].push(wi);
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

inline bool checker::propagateCore()
{   if(!coreMode) return true;
    while (qhead < trail.size()){
        Lit   p = trail[qhead++];
        vec<WatcherL> &  cws  = corewatch[p];
        Lit  false_lit = ~p;
        int cwsize=cws.size();
        for (int i=0; i <cwsize; i++){
            WatcherL & cwi=cws[i];
            CRef &  cr = cwi.cr;
            Clause & c = ca[cr];
            Lit & w0=c[0], & w1=c[1];
            if(value(w0) == l_True || value(w1) == l_True) continue;
            if (w0 == false_lit) w0=w1;
            int sz= c.size();
            for (int m = 2; m < sz; m++) {
                Lit & Lm=c[m];
               if (value(Lm) != l_False){
                     corewatch[~Lm].push(cwi);
                     w1 = Lm; Lm = false_lit;
	             cwsize--;
                     cws[i--]=cws[cwsize];
                     goto NextC; 
                }
	    }
            w1 = false_lit;
            if (value(w0) == l_False){
                cws.shrink(cws.size() - cwsize);
                analyze_used(cwi.clsNo);
                return false;
             }
             else uncheckedEnqueue(w0,cwi.clsNo);
         NextC:;
        }
        cws.shrink(cws.size() - cwsize);
     }
     return true;
  
}

bool checker::propagate3()
{  
    int qhead2=qhead;

    if(!propagateCore()) return false;
    while (qhead2 < trail.size()){
        Lit   p = trail[qhead2++];
        vec<Watcher> &  wbin  = watchesBin[p];
        for(int k = wbin.size()-1; k>=0; k--) {
    //    for(int k =0; k< wbin.size(); k++) {
             Watcher & wk= wbin[k];
	     Lit imp = wk.blocker;
             int v=var(imp);
             if(value(imp) == l_True) continue;
             if(assigns[v] == l_Undef){
                   assigns[v] = lbool(!sign(imp));
                   reason[v]  = wk.clsNo;
                   trail.push_(imp);
                   if(!propagateCore()) return false;
                   continue;
              }
              analyze_used(wk.clsNo);
              return false;
        }

        vec<WatcherL> &  ws  = watches[ p ];
        Lit  false_lit = ~p;
        int wsize=ws.size();
        for (int i=0; i <wsize; i++){
            WatcherL & wi=ws[i];
            CRef & cr = wi.cr;
            Clause & c = ca[cr];
            Lit & w0=c[0], & w1=c[1];
            if(value(w0) == l_True || value(w1) == l_True) continue;
            if (w0 == false_lit) w0=w1;
            int sz= c.size();
            for (int m = 2; m < sz; m++) {
               Lit & Lm=c[m];
               if (value(Lm) != l_False){
                     watches[ ~Lm].push(wi);
                     w1 = Lm; Lm = false_lit;
	             wsize--;
                     ws[i--]=ws[wsize];
                     goto NextClause; 
                }
	    }
            w1 = false_lit;
            if (value(w0) == l_False){
                ws.shrink(ws.size() - wsize);
                analyze_used(wi.clsNo);
                return false;
             }
             else{
                 uncheckedEnqueue(w0,wi.clsNo);
                 ws.shrink(ws.size() - wsize);
                 if(!propagateCore()) return false;
            }
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
    for (int i = 0; i < learnts.size(); i++) 
               if( learnts[i] != CRef_Undef ) ca.reloc(learnts[i], to);
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
            vec<WatcherL> &  cws = corewatch[p];
            for(int k = 0;k<cws.size();k++) cws[k].cr= getCref(cws[k].clsNo);
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
		 if(c == EOF) goto done;
         if(c == '\n' || c == ' ') continue;
         if(c != '-' && (c <'0' || c>'9') && c != '+') continue;
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
    if(lits.size()>2){
          if(nVars()>100000) sort((Lit *)lits, lits.size(), watch_lt(watches,watchesBin));
          else sort((Lit *)lits, lits.size(), watch_lts(watches));
    }
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
    return !propagate3();
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

inline void checker :: offtrueClause(CRef cr,int No, int maxLevel)
{
    Clause & c = ca[cr];
    int sz=c.size();
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
           bool cnf=propagate3();
           unitClauseID[cv]=saveID;
           cancelUntil(1);
           if(cnf == false){
                 if(tracecheck){
                       traceUnit(clsNo, toIntLit(lit));
                 }
                 unitproof++;
                 uncheckedEnqueue(lit);
                 propagate3();
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
          attachClause(cr, cNo);
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


void checker :: restoreTmpdetach( )
{
    for(int k=0; k < tmpdetach.size(); k++){
          int No=tmpdetach[k];
          CRef cr=learnts[No];
          if(cr == CRef_Undef) continue;
          if(ca[cr].detach()) attachClause(cr,No+1);
          ca[cr].canDel(0);
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

inline void checker :: swapEqTofront(Lit * lits, int sz, int eqVal)
{     int j=0,k;
      for(int i=0; i<sz; i++){
           Lit lt=lits[i];
           if(seen[toInt(lt)]!=eqVal) continue;
           lits[i]=lits[j]; lits[j++]=lt;
      }
      if(j>11){
          sort(lits, j);
          return;
      }
      for(int i=1; i<j; i++){
           Lit lt=lits[i];
           int m=toInt(lt);
           for(k=i-1; k>=0; k--){
               if(m>toInt(lits[k])) break;
               lits[k+1]=lits[k];
           }
           lits[k+1]=lt;
     }
}

inline int checker :: moveEqTofront(vec <Lit> & preLit,vec <Lit> & curLit,vec <Lit> & nxtLit)
{      
      for(int i=preLit.size()-1; i>=0; i--) seen[toInt(preLit[i])]  =1;
      for(int i=nxtLit.size()-1; i>=0; i--) seen[toInt(nxtLit[i])] +=2;
      int en1=0,en2=0,en3=0;
      for(int i=curLit.size()-1; i>=0; i--){
             int lit=toInt(curLit[i]);
             if(seen[lit]==1) en1++;
             else if(seen[lit]==2) en2++;
                  else if(seen[lit]==3) en3++;
      }
      swapEqTofront((Lit *)curLit, curLit.size(),3);
      swapEqTofront((Lit *)curLit+en3, curLit.size()-en3,1);
      swapEqTofront((Lit *)curLit+en1+en3, curLit.size()-en1-en3,2);
      for(int i=preLit.size()-1; i>=0; i--) seen[toInt(preLit[i])]=0;
      for(int i=nxtLit.size()-1; i>=0; i--) seen[toInt(nxtLit[i])]=0;
      return en1+en2+en3;
}

inline void checker :: detachpartClause(int m,int localcut)
{
    CRef cr=learnts[m];
    if( cr == CRef_Undef) return;
    Clause & c=ca[cr];
    if(c.size() > localcut){
         if(c.detach()==0){
             detachClause0(c, m+1);
             c.detach(1);
         }
    }
}      

void checker :: DelInference(int & Delidx,int low)
{ 
    int ctime=Delqueue[Delidx].timeNo;
    for(; Delidx<Delqueue.size() && ctime==Delqueue[Delidx].timeNo; Delidx++){
         DelInfo DI=Delqueue[Delidx];
         int No=DI.target.deletedNo;
         if(No<=low) continue;
         CRef cr=learnts[No-1];
         if(cr != CRef_Undef){
              Clause &  c = ca[cr];
              if(c.detach()==0){
                  detachClause0(c, No);
                  c.detach(1);
              }
         }
    }
}

int checker :: finddelstart(int begin, int end,int timeNo)
{
     if(begin >= end) {
            if( timeNo > Delqueue[begin].timeNo) begin++;
            return begin;
     }
     int mid= (begin + end)/2;
     if( timeNo > Delqueue[mid].timeNo) return finddelstart(mid+1, end,timeNo);
     return finddelstart(begin, mid-1,timeNo);    
}     

void checker :: eqvForwardshift(int ulit, int begin, int CurNo)
{    Lit plit=toLit(ulit);
   
     if( begin >= CurNo || begin < 1000 || CurNo-begin<400) return;
 
     coreMode=0;
     clearCoreflag(CurNo+1);

     if(minClauseNo2 != -1){
           cancelUntil(decisionLevel()-1);
           restoreDetach(minClauseNo2, detachClsNo2);
     }

     vec <Lit> lits;
     int i, bin_idx=-1;
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
           int j;
           for(j=0; j<c.size(); j++) if(c[j] == plit) break;
           if(j>=c.size()) break;
    }
    int end=i-1;
    if(bin_idx < 0 ) bin_idx=begin;
        
  //  printf(" end=%d i=%d bin_idx=%d block size=%d \n", end,i,bin_idx, i-begin);
    
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
  
   qhead=0;
   propagateMax(bin_idx+1);
          
   tmp_antecedent.clear();
   tmp_unitID.clear();
   int shift=10000;
   int bsize=end-bin_idx;
 //  if(bsize<280000) shiftmode=true;
//   else  shiftmode=false;
   shiftmode=true;
   int localproof=0,fail;
//   int localcut = 20; 
   int localcut = 8; //10
 //  if(bsize>200000) { shift = 100000; localcut = 40;}
   if(bsize>200000) shift = 30000;
   static int dbig=0;

   tmpdetach.clear();
   if(begin>400000){
        int dbegin=1000;
        if(learnts.size()>40000000) dbegin=100000;
        else if(dbig) dbegin=50000;
        if(bsize>200000) DetachWatch(dbegin, begin-250000);
        else DetachWatch(dbegin, begin-5000);
        reAttachlearnt(dbegin);
   }
  // int loopNo = (end-bin_idx < 2*shift)? 1 : 0;
   int start=bin_idx;
   vec <Lit> litg[3];
   int delstart=finddelstart(0, Delqueue.size()-1,start);

   int Delidx=delstart;
   ok=true;
   fail=0;
   int sz,nx=2, cu_i=-1;
   for(i=0; i<3; i++) litg[i].clear();
   for(i=start; i<= end+1; i++){
        int cu=(nx+2)%3;
        int pr=(nx+1)%3;
        vec <Lit> & prLits=litg[pr];
        vec <Lit> & cuLits=litg[cu];
        vec <Lit> & nxLits=litg[nx];
        nxLits.clear();
        while (i<= end){
              {if(Delqueue[Delidx].timeNo == i && i<end) DelInference(Delidx, bin_idx);}
              if(i-shift>=bin_idx) detachpartClause(i-shift,localcut);
              CRef cr=learnts[i];
              if(  cr == CRef_Undef) {
nextc:
                    i++;
                    continue;
              }
              if(verifyflag[i+1] & (VERIFIED | TMP_VERIFIED)) {
                    Clause &  c2 = ca[cr];  
                    if(c2.size()==2){
                         Lit lt= (c2[0]==plit) ? c2[1] : c2[0];
                        if(assigns[var(lt)] == l_Undef){
                            cancelUntil(ilev+1);
                            uncheckedEnqueue(lt,i+1);
                            qhead=0; 
                            ok=propagate3();
                        }
                    }
                    attachClause(cr,i+1);
                    goto nextc;
              }
              Clause & c =ca[cr];
              for(int j=0; j<c.size(); j++) 
                     if(plit !=c[j]) nxLits.push(c[j]);
              break;
        }
//
        while(cuLits.size()){
              int cNo=cu_i+1;
              moveEqTofront(prLits,cuLits,nxLits);
              lits.clear();
              for(int j=0; j<cuLits.size(); j++) seen[toInt(cuLits[j])]=2;
              int eqvn=sz=prLits.size();
              for(int j=0; j < sz; j++){
                  Lit lt=prLits[j];
                  if(seen[toInt(lt)]==2){
                      lits.push(lt);
                      seen[toInt(lt)]=0;
                  }
                  else if(eqvn == sz ) eqvn=j;
              }
              for(int j=0; j<cuLits.size(); j++){
                   Lit lt=cuLits[j];
                   if(seen[toInt(lt)]){
                         lits.push(lt);
                         seen[toInt(lt)]=0;
                   }
                   cuLits[j]=lits[j];
              }
              if(eqvn >= prLits.size() && eqvn>0 ){//subsume current clause
                   ca.free(learnts[cu_i]);
                   learnts[cu_i] = CRef_Undef;
                   cuLits.shrink(cuLits.size()-eqvn);
                   goto nextcls;
              }
              int dlevel=decisionLevel();
              if( dlevel <= ilev+eqvn+1){
                    if(!ok) goto sucess;
                    eqvn=decisionLevel()-ilev-1;
              }
              cancelUntil(ilev+eqvn+1);
              ok=true;
              for(int k = eqvn; k <cuLits.size(); k++){
                  newDecisionLevel();
                  Lit clit= ~cuLits[k];
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
              if(ok) { 
                   qhead=qhead0; 
                   ok = propagate3();
              }
 sucess:
              if(!ok){
                   if(shiftmode){
                        tmp_antecedent.push(cu_i);
                        tmp_antecedent.push(cNo_Undef);
                        if(tracecheck) tmp_unitID.push(0);
                   //     if(loopNo == 0) verifyflag[cNo] |= TMP_VERIFIED;
                   }
                   else{
                        if(tracecheck) printrace(cNo);
                        verifyflag[cNo] |= VERIFIED;
                   }
                   localproof++; 
              }
              else fail++;
              break;
          }
          if(cu_i >= 0 && cu_i <= end){
              if(learnts[cu_i] != CRef_Undef) attachClause(learnts[cu_i],cu_i+1);
          }
nextcls:
          cu_i=i;
          nx = (nx+1)%3;
    } 
 
    //printf(" %d verified inferences %d fails\n",localproof,fail);
  
    restoreTmpdetach( );
    restoreDetach();
    if(learnts.size()>20000000 && fail>40000) dbig=1;

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

  //  printf(" %d localproofs %d fails, tmp_ant=%d \n",localproof,fail,tmp_antecedent.size());

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

    coreMode=1;
}    

void checker :: Localbackwardshift(int begin, int end)
{  
   if(end<begin+5000 || begin<500000) return;
   static bool nofind=false;   
   
  //  printf("\n back B=%d E=%d ",begin, end);

   int csz=clauses.size();  

   if(end<begin+15000 || csz>1000000 || nofind || (10*bintrn>9*csz && nVars()>150000) ){

        if(nVars()<350000) prePropagate((begin+end)/2);
        return;
    }
  
   
    tmpdetach.clear();
    int winsize=30000;
    int mid=begin-winsize;
    DetachWatch(0,begin-50000);
  
    int  cNo,fail=0;
    int k,localproof=0;
    int clevel=decisionLevel ();
    int trail0=trail.size();
    int shiftb=end-winsize+1;
   
    vec <Lit> lits;

    for(int i=mid+1; i < shiftb; i++){
          if(filePos[i] == -1) continue;
          CRef cr=learnts[i];
          if(cr != CRef_Undef){
                   if(ca[cr].size()==0) {ca.free(cr); learnts[i]=CRef_Undef; goto readcls;}
                   ca[cr].canDel(0);
                   goto det;
           }
readcls:
           if(i<begin) continue;
           readfile(i,lits);
           if(lits.size() <=1 ) continue;
           cr=learnts[i] = ca.alloc(lits);
           ca[cr].canDel(1);
           ca[cr].detach(1);
det:       ;
    }

    vec <Lit> litg[2];
    int cu=1,saveDel=lastDel;

    for(int i=end-1; i>=begin; i--){
         if(lastDel>=0 && i<=Delqueue[lastDel].timeNo) restoreDelClause(i-1,mid,1);
         if(filePos[i] == -1) continue;
         CRef cr = learnts[i];
         if(cr == CRef_Undef) continue;
         cNo=i+1;
         Clause &  c = ca[cr];
         if(c.detach()==0){
               detachClause0(c, cNo);
               c.detach(1);
         }
         if(verifyflag[cNo] != USEDFLAG ) continue;
     
         int sz,pr=(cu+1)%2;
         vec <Lit> & prLits=litg[pr];
         vec <Lit> & cuLits=litg[cu];
         cuLits.clear();
         for(k=0; k<c.size(); k++) cuLits.push(c[k]);
         lits.clear();
         for(int j=0; j<cuLits.size(); j++) seen[toInt(cuLits[j])]=2;
         int eqvn=sz=prLits.size();
         for(int j=0; j < sz; j++){
              Lit lt=prLits[j];
              if(seen[toInt(lt)]==2){
                    lits.push(lt);
                    seen[toInt(lt)]=0;
              }
              else if(eqvn == sz ) eqvn=j;
         }
         for(int j=0; j<cuLits.size(); j++){
              Lit lt=cuLits[j];
              if(seen[toInt(lt)]){
                   lits.push(lt);
                   seen[toInt(lt)]=0;
              }
              cuLits[j]=lits[j];
         }
         int dlevel=decisionLevel();
         if( dlevel < clevel+eqvn) eqvn=dlevel-clevel;
         cancelUntil(clevel+eqvn);
         for(k=trail0; k<trail.size(); k++){
              int confl=reason [var(trail[k])];
              if(confl == cNo_Undef || confl <= i) continue;
              cancelUntil(clevel);
              eqvn=0;
              break;
         }
        
         ok=true;
         for(k=eqvn; k<cuLits.size(); k++){
                 newDecisionLevel();
                 Lit clit=~cuLits[k];
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
                 ok=propagate3();
                 if(!ok)  break;
         }
         if(!ok){ localproof++; 
                  verifyflag[cNo] |= VERIFIED;
                  if(tracecheck) printrace(cNo);
         }
         else fail++;
    }
    lastDel = saveDel;

    cancelUntil(clevel);
    restoreTmpdetach( );
   int delbegin=end-2000;
   for(int i=mid+1; i<end; i++){
         CRef cr = learnts[i];
         if(cr == CRef_Undef) continue;
         int No=i+1;
         Clause &  c = ca[cr];
         if(i>=delbegin) c.canDel(0);
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
 
  //  printf(" %d verified inferences, %d fails ",localproof,fail);

    if(fail>2000 && fail>3*localproof) nofind=true;
    shiftproof += localproof;
}    

void checker :: clearAllwatch()
{
   for (int v = 0; v < nVars(); v++){
   	for (int s = 0; s < 2; s++){
             Lit p = mkLit(v, s);
             watches[p].clear();
             corewatch[p].clear();
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
           if(c.detach()) continue;
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
    for(int i=0; i <= CurNo; i++){
          CRef cr=learnts[i];
          if(filePos[i] == -1 || cr == CRef_Undef) continue;
          Clause &  c = ca[cr];
          if(c.detach()) continue;
          attachClause(cr,i+1);
    }
} 
 
void checker :: removeTrailUnit(Lit uLit,int CurNo)
{   
     unitClauseID[var(uLit)]=0;
     int lev=decisionLevel()-1;
     if(lev>=0 && trail[trail_lim[lev]]== uLit){
//cancel:
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
  //              goto cancel;      
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
                         attachClause(cr, No);
                       //  movelit_att(ca[cr], No,cr);
                  }
           }
           else{
                  if(No>MaxNo) continue;
                  No--;
                  CRef cr=learnts[No];
                  if( cr != CRef_Undef) {
                        if(ca[cr].canDel()){
                             ca[cr].canDel(0);
                             if(ca[cr].detach()) attachClause(cr, No+1);
                       //      if(ca[cr].detach()) movelit_att(ca[cr], No+1,cr);
                        }
                        continue;
                  }
                  readfile(No, lits);
                  cr = ca.alloc(lits);
                  learnts[No]=cr;
                  ca[cr].detach(1);
                  attachClause(cr,No+1);
                //  movelit_att(ca[cr], No+1,cr);
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
          if(value(lit) == l_True) continue;
          int clsNo=cur_unit[i].idx+1;
          if(value(lit) == l_False){
                 printEmptyclause1(origIDSize+clsNo, var(lit));
                 ok=false;
          }
          else {
               uncheckedEnqueue(lit);
               ok = propagateMax(1);
               if(!ok) printEmptyclause2();
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
					  if(verifyflag[No] & VERIFIED) return;//bug 2019
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
			       if(unitID_idx>=0){
	                    if(unitID_idx < saveUnitID.size()){
						    if(saveUnitID[unitID_idx].v==cv){
							    unitClauseID[cv]= saveUnitID[unitID_idx++].ID;
                           	}
                        }
                        return;
                   }
				   analyze_used(confl);
                   unitClauseID[cv]= ++auxClauseID;
				   saveUnitID.push(UnitID(cv,auxClauseID));
                   if(tracecheck) {
                       traceUnit(auxClauseID-origIDSize, toIntLit(lit));
                   }
            }
     }
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
                   ok=!propagate3();
                   if(ok) return true;
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
                     ok=!propagate3();
                     if(ok) return true;
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
                   ok=!propagate3();
                   if(ok) return true;
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
bool checker :: checkRup(int LerantNo, vec <Lit> & lits)
{
    int orglevel=decisionLevel();
    if(refound){
        qhead=t_sz0;
        newDecisionLevel();
        propagate3();
        refound=0;
    }
  	int v0=var(lits[0]);
    int saveID=unitClauseID[v0];
    unitClauseID[v0] = 0;
    ok=isconflict(lits);
    if(!ok) {
        refound=1;
        int pre_qhead=-1;
  retry:     
        while (!ok && pre_qhead != trail.size()){
            pre_qhead=trail.size();
            qhead=0;
            ok=!propagate3();
        }

        if(!ok && auxUnitmode==0){
            auxUnitmode=1;
            ok=restoreAuxUnit();
            if(!ok){ pre_qhead=-1;  goto retry;}
        }
	
        if(!ok && detachlist.size()){
            pre_qhead=qhead = trail.size();
            ok=finddetachUnit(detachlist);
            if(!ok && pre_qhead != trail.size()) goto retry;
        }

    //      if(!ok) { unproofn++; break;}
    //  if(!ok && unproofn==0){
    //      ok=refind(clause_i,iLerantNo);
    //  }

        cancelUntil(orglevel);
        if(auxUnitmode==1){ 
            auxUnitmode=2; 
            restoreAuxUnit();
        }
    }
    cancelUntil(orglevel);
    unitClauseID[v0]=saveID;
	return ok;
}
                                                    
int checker :: backwardCheck()
{   
    printf("c backward check\n");
    movetoFront=nVars()<350000;
    int shiftusedproof=0;
    int maxNo=filePos.size();
    filePos.min_memory(maxNo);
    maxCoreNo=origIDSize;
    verifyflag = (unsigned char * ) calloc (maxCoreNo+maxNo+4, sizeof(unsigned char));
    varusemark = (char * ) calloc (nVars()+1, sizeof(char));

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
    unproofn=proofn=unitproof=0;

    cutLen=0x5fffffff;
    extractUnit(unitproof);
    t_sz0=trail.size();
    printf("c %d out of %d units are verified in initial step\n",unitproof,cur_unit.size());
 
    if(maxdisFirstvar<5000 || lit_begin_end.size()<=180 || nVars()<=origVars+50){
         lit_begin_end.clear();
         eqvForwardmode=0;
    }
    else eqvForwardmode=1;
    winmode=2;

    saveDelqueue.clear();
    for(int i=0; i<Delqueue.size(); i++) saveDelqueue.push(Delqueue[i]);
     
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
              ok = propagate3();
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
    int  backshiftbegin=-1, shiftmode=false;
    auxUnitmode=refound=0;
    shift_i=-1;
    for(int i=end; i>=0; i--){
       if(i%1000==0){
            double check_time = cpuTime()-initial_time;
            if(check_time>45000) {
                   printf("c time out \n");
                   return 0;
           }
       }
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
                    //
                         if(!coreMode) continue;
                         CRef cr=getCref(No);
                         if(cr == CRef_Undef) continue;
                         Clause & c = ca[cr];
                         if(c.coreC()) continue;
                         if(c.detach()) continue;
                         detachClause0(c,No);
                         c.coreC(1);
                         attachClause(cr, No);
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
                    else  auxUnitmode=2;
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
//
        ok=checkRup(i, lits);
        if(!ok) {
//            if(unproofn==0) filePos.shrink_(filePos.size()-1-i); //note delete info need to display, clear tail Unit ID 
            unproofn++;
			RatcheckCls.push(i);
        }
        else {
             verifyflag[i+1] = VERIFIED;
             if(tracecheck) printrace(i+1);
             if(lits.size()==1) unitproof++;
             else proofn++;
             coreNum--;
             if(coreNum>70000) clearCoreflag(i);
        }
   }
   if(tracecheck){
	    LRAT_map.growTo(auxClauseID+1);
        for(int j=0; j <=auxClauseID; j++) LRAT_map[j].delbegin=-1;
   }
   if(unproofn){
         printf("\nc %d inferences are not verified in RUP check step\n",unproofn);
         auxUnit.clear();
         coreMode=0;
         clearCoreflag(0);
		 unitID_idx=0;
         return RATCheck();
   }
	
   printf("\nc %d inferences, %d units are verified\n",proofn,unitproof);
   if(shiftusedproof) 
         printf("c %d out of %d verified inferences is useful in win shift step\n",shiftusedproof,shiftproof);
   else  printf("c %d inferences are verified in win shift step\n",shiftproof);
   printf("c %d deleted inferences\n",Delqueue.size());
   sort_LRAT();
 
   printf("c proof is verified\n");
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
           if(verifyflag[i+1] & VERIFIED) continue;
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

inline void checker :: removeRATindex (vec<Lit> & lits, int clsNo)
{  
    for(int j=0; j<lits.size(); j++) {
          if(RATvar[var(lits[j])]){
               remove(RATindex[toInt(lits[j])], clsNo);
          }
     }
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

bool checker :: conflictCheck(int lrn_No, vec<Lit> & lits)
{
     int clause_i=clauses.size();
     ok=isconflict(lits);
     while(!ok){
          qhead=0;
          ok = !propagate3();//bug
          if(ok) break;
          int old_tsz=trail.size();
          ok=refind(clause_i,lrn_No);
          if(ok) break;
          if(old_tsz==trail.size()) break;
     }
     cancelUntil(decisionLevel()-1);
     return ok;
}
    
int checker :: RATCheck()
{
    cancelUntil(0);
    t_sz0=trail.size();
    auxUnitmode=refound=0;
 
    setRATvar();
    buildRATindex();
    cutLen=0x5fffffff;
    int end=filePos.size()-1;
    winmode=3;
//
    cur_unit.clear();
    for(int i=0; i<save_unit.size(); i++){
            cur_unit.push(save_unit[i]);
            unitClauseID[var(save_unit[i].lit)]=save_unit[i].idx+origIDSize+1;
    }
	Delqueue.clear();
    for(int i=0; i<saveDelqueue.size(); i++) Delqueue.push(saveDelqueue[i]);
    saveDelqueue.clear(true);
	
    activateDelinfo(end, cur_unit);
      
    CRef cr;
    vec<Lit> lits,lits2,lits3;
    int pivot,RatProofn=0,RatUnitProof=0,Ratk=0;
    vec<int> *ridx;
    eqvForwardmode=0;
    vec <int> varUnitID;
	
    int preDelID=-1;
	learntDel.growTo(end+1);
	clauseDel.growTo(clauses.size());
    for(int i=0; i<=end; i++) learntDel[i]=0;
    for(int i=0; i<=clauses.size(); i++) clauseDel[i]=0;
  
    for(int i=0; i<Delqueue.size(); i++){
        int No=Delqueue[i].target.deletedNo;
        if(No<=0) clauseDel[-No]=1;
        else if(No<=end) learntDel[No]=1;
        if(tracecheck){
			int ID=getClauseID(Delqueue[i].timeNo+1);
         	if(ID != preDelID){
               // if(preDelID==-1) fprintf(traceOutput, "%i d ", ID);
				//else 	         fprintf(traceOutput, "0\n%i d ", ID);
				
		        if(preDelID != -1 ) LRAT_map[preDelID].delend = delID.size();
    			LRAT_map[ID].delbegin = delID.size();
	        }
			delID.push(getClauseID(No));
			//fprintf(traceOutput, "%i ", getClauseID(No));
			preDelID=ID;
		}	
    }
	
    //if(tracecheck && preDelID != -1) fprintf(traceOutput, "0\n");
    if(tracecheck && preDelID != -1) LRAT_map[preDelID].delend = delID.size();

    for(int i=end; i>=0; i--){
           if(lastDel>=0 && i<=Delqueue[lastDel].timeNo) restoreDelClause(i, 0,0);
           if(filePos[i] == -1) continue;
           if(learnts[i] == CRef_Undef){
              lits.clear();
              if(cur_unit.size()){
                UnitIndex cUnit = cur_unit.last();
                if(cUnit.idx == i){
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
                     restoreAuxUnit();
                     qhead=t_sz0;
                     propagate3();
                }
                if(verifyflag[i+1] != USEDFLAG) continue;
              }
              if(lits.size() == 0){
                    if(verifyflag[i+1] != USEDFLAG) continue;
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
		  
		  pivot=toInt(~lits[0]);
 	  	  int curLevel=decisionLevel();
		  if(tracecheck) printracHead(i+1, lits);
          while(Ratk<RatcheckCls.size()){
			  if(RatcheckCls[Ratk]<=i) break;
			  Ratk++;
		  }
		  if(Ratk>=RatcheckCls.size() || RatcheckCls[Ratk]<i){ // RUP check
               if(checkRup(i, lits)){
                     if(tracecheck) printbody();
                     if(lits.size()==1) unitproof++;
                     else proofn++;
                     goto nextclase;
			   }
		  }
    	  removeRATindex (lits, i+1);
          ridx = & RATindex[pivot];
          for(int j=0; j < ridx->size(); j++){
                 newDecisionLevel();
                 int cno=(*ridx)[j];
                 int maxCno=1;
                 if(cno <= 0){
					 cr=clauses[-cno];
					 if(clauseDel[-cno]) continue;
				 }
                 else{
                     if(cno>i) continue;
					 if(learntDel[cno]) continue;
                     verifyflag[cno] |= USEDFLAG;
                     cr=learnts[cno-1];
                     maxCno=cno;
                 }
                 if(cr == CRef_Undef) readfile(maxCno-1,lits2);
                 else{
                      lits2.clear();
                      Clause & c = ca[cr];
                      for(int k=0; k<c.size(); k++) lits2.push(c[k]);
                 }
                 lits3.clear();
                 for(int k=0; k<lits.size(); k++) lits3.push(lits[k]);
                 for(int k=0; k<lits2.size(); k++){
                       if(pivot== toInt(lits2[k])) continue;
                       lits3.push(lits2[k]);
                 }
                
                 if(!checkRup(i, lits3))
                    if(!conflictCheck(i,lits3)){
                        printf("c The %d-th inference RAT check fails \n",i);
                        return 0;
                    }
                 if(tracecheck) printRatBody(cno);
          }
          if(lits.size()==1) RatUnitProof++;
          else RatProofn++;
nextclase: 
          cancelUntil(curLevel);
          verifyflag[i+1] = VERIFIED;
          if(tracecheck) printraceEnd();
     }
     printf("\nc %d inferences, %d units are verified\n",proofn,unitproof);
     printf("c %d units and %d inferences are verified in RAT check\n",RatUnitProof,RatProofn);
     delete []RATindex;
     free(RATvar);
	 sort_LRAT();
     printf("c proof is verified \n");
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
    int binterN=0;
    for(int i=0; i<clsno.size()-1; i++){
          int n1=clsno[i];
          CRef cr1=learnts[n1];
          if( cr1 == CRef_Undef ) continue;
          Clause & c1 = ca[cr1];
          if(c1.size() <4) binterN++;
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
	static int dis=1;
	if(dis) {
		printf("c remove %d repeated inferences\nc %d binary,ternary inferences\n",repeat,binterN);
        dis=0;
	}
	clsno.clear(true);
    
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
          if(c.detach()) attachClause(cr, i+1);
    }
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

void checker :: DetachWatch(int begin, int end)
{   tmpdetach.clear();  
    for (int v = 0; v < nVars(); v++){
        for (int s = 0; s < 2; s++){
             Lit p = mkLit(v, s);
             detachWatch(watches[p],  begin,end);
             detachWatch(corewatch[p],begin,end);
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
 
   auxUnit.clear();
   hashtbl = new vec<int>[HASHSIZE];
   for(int i=0; i<HASHSIZE; i++) hashtbl[i].clear();
   vec <Lit> lits;
   int k=0,t=0;
   int matchN=0,nomatch=0;
   cancelUntil(0);
   if( origVars != nVars()) HASHBLOCK=600000;
   bool clauseDel=true;

   if(end<6000000){
       for (int i =0; i < clauses.size(); i++){
           CRef cr = clauses[i];
           Clause &  c = ca[cr];
           if(c.detach()) continue;
           int h=sxhash((Lit *)c, c.size());
           hashtbl[h].push(-i);
       }
       clauseDel=false;
       rebuildwatch(-1);
   }

   for(int i=0; i<=end; i++){
        while (k<Delqueue.size() && i==Delqueue[k].timeNo){
               readdelclause(k,lits);
               int sz=lits.size();
               int h=sxhash((Lit *)lits, sz);
               if(!match(h, (Lit *)lits,sz,k,true)){
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
     
                for(int k=begin; k <=end; k++){
                    if(filePos[k] == -1) continue;
                    CRef cr=learnts[k];
                    if(cr == CRef_Undef) continue;
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
              }
         }
         nextc: ;
    }
nexstep:
    for(int v=0; v<nVars(); v++){
          if(assigns[v] == l_Undef) restoreTrueClause(v,end);
    }
    c_unit.shrink(c_unit.size()-t);
    removeRepeatedCls(end,t);
    garbageCollect(); 
    for(int i=0; i<HASHSIZE; i++) hashtbl[i].clear();
 
    if(clauseDel && matchN != Delqueue.size()){
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
    coreMode=end>100000 && eqvForwardmode==0;

    rebuildwatch(end);
    
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

int checker :: match(int h, Lit * lits, int len, int cur_delp, bool detachflag)
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
                           ca.free(cr);
                           learnts[No-1] = CRef_Undef;
                    }              
                    else{
                           if(c.detach()==0 && detachflag) detachClause0(c,No); 
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

inline void checker :: movelit_att( Clause &  c, int cno, CRef cr)
{
    if(movetoFront){
      int j=0;
      for(int k=0; k<c.size(); k++){
        Lit lit=c[k]; 
        if (value(lit) == l_False) continue;
        c[k]=c[j]; c[j++]=lit;
      }
    }
    attachClause(cr,cno);
}

void checker :: restoreDelClause(int CurNo,int low, int candel_flag)
{   
    int delta=clauseDel.size()? 1 : 10;
    int end=lastDel;
    for(; lastDel>=0; lastDel--){
           DelInfo DI=Delqueue[lastDel];
           //if(DI.timeNo<CurNo-10) break;
           if(DI.timeNo<CurNo-delta) break;
    }
    vec <int> cNo;
    int begin=lastDel+1;
    for(int i=begin; i<=end; i++){
           int No=Delqueue[i].target.deletedNo;
           cNo.push(No);
    }
    sort(cNo);

    vec <Lit> lits;
    for(int i=0; i<cNo.size(); i++){
           int No = cNo[i];
           if(No>0){
			      if(No<learntDel.size()) learntDel[No]=0;
                  No--;;
                  CRef cr=learnts[No];
                  if(cr != CRef_Undef){
                          if(ca[cr].detach()) //attachClause(cr,No+1);
                          movelit_att(ca[cr], No+1,cr);
                          if(candel_flag==0) ca[cr].canDel(0);
                          continue;
                  }
                  if(No>=CurNo || candel_flag) continue;
                  readfile(No, lits);
                  cr = ca.alloc(lits);
                  learnts[No]=cr;
                // attachClause2(cr,No+1);
                  movelit_att(ca[cr], No+1,cr);
                  if(No>low) ca[cr].canDel(candel_flag);
           }
           else{
			      if(clauseDel.size()) clauseDel[-No]=0;
                  CRef cr = clauses[-No];
                  Clause &  c = ca[cr];
                  if(c.detach()) movelit_att(c, No,cr);
           }
      }
}

void checker:: clearCoreflag(int lastlearnt)
{
    coreNum=0;
    clearAllwatch();
    for (int i =0; i < clauses.size(); i++){
           CRef cr = clauses[i];
           Clause &  c = ca[cr];
           c.coreC(0);
           if(c.detach()) continue;
           attachClause(cr, -i);
    }
    for(int i=0; i < lastlearnt; i++){
          CRef cr=learnts[i];
          if(filePos[i] == -1 || cr == CRef_Undef) continue;
          Clause &  c = ca[cr];
          if(!coreMode) c.coreC(0);
          if(c.detach()) continue;
          attachClause(cr,i+1);
    }
}

void checker:: analyze_used_notrace(int confl)
{
    if(verifyflag==0) return;
    vec<Var> scan;
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
               if(coreMode) ca[cr].coreC(1);
          }
         Clause & c = ca[cr];
         if(coreMode){
              if(!c.coreC()){
                   coreNum++;
                   if(!c.detach()){
                        detachClause0(c,confl);
                        c.coreC(1);
                        attachClause(cr, confl);
                   }
              }
         }
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
   // if(k<scan.size()) goto simp;
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
              if(coreMode) ca[cr].coreC(1);
         }
         Clause & c = ca[cr];
         if(coreMode){
              if(!c.coreC()){
                   coreNum++;
                   if(!c.detach()){
                        detachClause0(c,confl);
                        c.coreC(1);
                        attachClause(cr, confl);
                   }
              }
         }
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
              fprintf(traceOutput, "0 ");
              return;
        }
        readfile(clsNo-1, lits);
    }
    for (int i =0; i < lits.size(); i++) fprintf(traceOutput, "%i ", toIntLit(lits[i]));
    fprintf(traceOutput, "0 ");
}         

void checker:: printbody()
{
   for (int i=antecedents.size()-1; i>=0; i--) fprintf(traceOutput, "%i ", antecedents[i]);
}	

void checker:: printrace(int clsNo)
{
   vec <Lit> lits;
   printracHead(clsNo, lits);
   if(clsNo>0) printbody();
   fprintf(traceOutput, "0\n");
}         

void checker:: printrace2(int clsNo)
{
   vec <Lit> lits;
   printracHead(clsNo, lits);

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
    fprintf(traceOutput, "-%i ",getClauseID(clsNo));
    printbody();
}         

void checker:: printraceEnd()
{
   fprintf(traceOutput, "0\n");
}

void checker:: traceUnit(int clsNo,int lit)
{  int ID=getClauseID(clsNo);
   fprintf(traceOutput, "%i %i 0 ", ID,lit);

   int sz=antecedents.size()-1;
   int maxID=origIDSize;
   for (int i=sz; i>=0; i--){
	   int AntID = antecedents[i];
	   if( AntID != ID){
  		    fprintf(traceOutput, "%i ", AntID);
            if(ID>maxClauseID){
           		if(AntID> maxClauseID){
					for(int k=auxUnitRely.size()-1; k>=0; k--)
                        if(auxUnitRely[k].ID == AntID) {
           					if(maxID < auxUnitRely[k].maxAntID) maxID = auxUnitRely[k].maxAntID;
							break;
						}
		        }				
                else if(maxID < AntID) maxID = AntID;
			}
	   }
   }
   if(ID>maxClauseID) auxUnitRely.push(AuxUnitRely(ID,maxID));
	   
   fprintf(traceOutput, "0\n");
}         

void checker:: TraceOrigClause()
{   antecedents.clear();
    for(int i=0; i<clauses.size(); i++)	printrace(-i);
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

struct IDrely_lt { 
    bool operator () (struct AuxUnitRely x, struct AuxUnitRely y) const {
		if(x.maxAntID < y.maxAntID) return 1;
		return x.ID < y.ID; 
	}
};
void checker:: sort_LRAT()
{
    fclose(rat_fp);
	if( (!tracecheck) || traceOutput == stdout) return;
	fclose(traceOutput);
    sort(auxUnitRely, IDrely_lt());
	
    int m=origIDSize+1;	
    for(int j=m; j <=auxClauseID; j++) LRAT_map[j].toID=-1;
	int k=0;
    for(int j=m; j <=auxClauseID; ){
		if(LRAT_map[j].toID>0) {j++; continue;}
		if(k>=auxUnitRely.size() || j<=auxUnitRely[k].maxAntID) {
			LRAT_map[j++].toID=m++;
			continue;
		}
        LRAT_map[auxUnitRely[k++].ID].toID=m++;
    }
    for(int j=0; j <=auxClauseID; j++) LRAT_map[j].pos=0;
	readtracefile(); 
    savetracefile();
}

void checker :: readtracefile() 
{
#ifdef  __APPLE__
        traceOutput  = fopen(Trace_file, "r");
#else
        traceOutput  = fopen64(Trace_file, "r");
#endif
        int ID;
        while(1) {
            int ret=fscanf(traceOutput, "%i", &ID);
            if( ret == EOF) return;
            #ifdef  __APPLE__
        	    LRAT_map[ID].pos = ftello(traceOutput);
            #else 
                LRAT_map[ID].pos = ftello64(traceOutput);
            #endif
            while(1){
                char c = fgetc(traceOutput);
                if(c == EOF) return;
                if(c == '\n') break;
            }
 	    }
}

void checker :: savetracefile() 
{
        int n=strlen(Trace_file);
    	char *tmp_file = new char[n+10];
		stpcpy(tmp_file,Trace_file);
	    tmp_file[n]='t';
	    tmp_file[n+1]=0;
		
#ifdef  __APPLE__
        FILE* tmpOutput  = fopen(tmp_file, "w");
#else
        FILE* tmpOutput  = fopen64(tmp_file, "w");
#endif
     
	    for(int i=origIDSize; i>=0; i--) LRAT_map[i].toID=i;
 //    
        vec <int> oldID(auxClauseID+2);
        for(int i=0; i <= auxClauseID; i++) oldID[i]=i;
        for(int i=origIDSize+1; i <= auxClauseID; i++) oldID[LRAT_map[i].toID]=i;
        
		int m;
     	for(int cID=1; cID <=auxClauseID; cID++){
			int orgID=oldID[cID];
	        if(LRAT_map[orgID].pos <=0) goto putdel;
            readLRATline(LRAT_map[orgID].pos);
            if(LRATrow.size() == 0) goto putdel;
		    fprintf(tmpOutput, "%i", cID);
            m=0;
  		    for(; m < LRATrow.size(); m++) {// lit
				 fprintf(tmpOutput, " %i", LRATrow[m]);
				 if(LRATrow[m]==0) break;
			}
			for(m++; m < LRATrow.size(); m++) {// ant ID
				 int oldid = LRATrow[m];
        		 int newID = 0;
		         if( oldid > 0 ) newID = LRAT_map[oldid].toID;
                 else if( oldid < 0 ) newID = -LRAT_map[-oldid].toID;
         		 fprintf(tmpOutput, " %i", newID);
			}
			
			fprintf(tmpOutput, "\n");
putdel:     
            if(LRAT_map[orgID].delbegin<0 || LRAT_map[orgID].delbegin>=LRAT_map[orgID].delend) continue;
		    fprintf(tmpOutput, "%i d ", cID);
		    for(int i=LRAT_map[orgID].delbegin; i < LRAT_map[orgID].delend; i++){
				 fprintf(tmpOutput, "%i ", LRAT_map[delID[i]].toID);
			}
			fprintf(tmpOutput, "0\n");
		}
        fclose(tmpOutput);
        fclose(traceOutput);
		rename(tmp_file,Trace_file);
}

void checker :: readLRATline(off64_t pos)
{
     #ifdef  __APPLE__
           fseeko(traceOutput, pos,SEEK_SET);
     #else 
           fseeko64(traceOutput, pos,SEEK_SET);
     #endif
     LRATrow.clear();
     int cnt=0;
     while(1){
          int No;
          int ret=fscanf(traceOutput, "%i", &No);
          if(ret == EOF) break;
          LRATrow.push(No);
          if(No==0){
               cnt++;
               if(cnt==2) return;
          }
     }
 }

