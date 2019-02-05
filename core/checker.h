
#ifndef treeRat_checker_h
#define treeRat_checker_h

#include "mtl/Vec.h"
#include "mtl/Alg.h"
#include "utils/Options.h"
#include "core/checkerTypes.h"

#define _FILE_OFFSET_BITS 64
#define _LARGE_FILES

#define cNo_Undef 0x7fffffff

#ifdef  __APPLE__
   typedef  off_t  off64_t;
#endif

namespace treeRat {

   struct DelInfo {
        DelInfo(){}
        int  timeNo;
        union {int  deletedNo; int diskoffset;} target; 
        DelInfo(int t, int d) {timeNo=t, target.diskoffset=d;}
    };
 
    struct Watcher {
        int  clsNo;
        Lit  blocker;
        Watcher(int No, Lit p) : clsNo(No), blocker(p){}
        bool operator==(const Watcher& w) const { return clsNo == w.clsNo; }
        bool operator!=(const Watcher& w) const { return clsNo != w.clsNo; }
    };

    struct WatcherL {
        int  clsNo;
        CRef cr;
        WatcherL(int No, CRef _cr) : clsNo(No),cr(_cr){}
        bool operator==(const WatcherL & w) const { return clsNo == w.clsNo; }
        bool operator!=(const WatcherL & w) const { return clsNo != w.clsNo; }
    };

//=================================================================================================
class checker {
public:

    checker();
    ~checker();

    bool                ok;        // If FALSE, the constraints are already unsatisfiable
    Var     newVar (); // Add a new variable 
    bool    addClause (const vec<Lit>& ps);                     // Add a clause to the checker. 
    bool    addClause_(vec<Lit>& ps);    // Add a clause to the checker without making superflous internal copy. 

    vec <off64_t> filebase;                                     // base position of clauses in the rup file
    vec <int> filePos;                                          // the position of clauses in the rup file
    vec <unsigned char> verifyMark;
    unsigned char *verifyflag;
     
    struct UnitIndex {
        int  idx;
        Lit  lit;
        UnitIndex(int i, Lit l) {idx=i, lit=l;}
    };
    vec <UnitIndex> cur_unit, save_unit;
   
    vec <DelInfo> Delqueue,saveDelqueue;
    int lastDel,Delq_active;
    void  readdelclause(int i,vec <Lit>  & lits);
   
    void DelRedundancyLit(vec <Lit> & lits,int No);
    void activateDelinfo(int & end, vec <UnitIndex> & c_unit);
    int  match(int h, Lit * lits, int len,int curNo,bool detachflag=false);
    int  match3(int h, Lit * lits);
    vec<int> * hashtbl;
    void clearHashtbl(int cur_delno);
    void movelit_att( Clause &  c, int cno, CRef cr);
    void restoreDelClause(int CurNo, int low=0, int candel_flag=0);
    void DetachWatch(int begin, int end);
    void detachWatch( vec<Watcher> & ws, int begin, int end);
    void detachWatch( vec<WatcherL>& ws, int begin, int end);
  
    FILE *rat_fp;
    void  readratOutput(char * rupfile);
    int   forwardCheck();
    bool  finddetachUnit(vec <int> & detachNo);

    void  readfile(int i,vec <Lit>  & lits);
    bool  isconflict(vec<Lit> & lits);
  
    int   backwardCheck();
    void  simplifyUnit();
    void  setAuxUnit(Lit lit,int t);
                                 
    int   maxCoreNo;
    void  removeTrailUnit(Lit uLit,int MaxNo);
    void  cancelloadtrueCls(int lev,int MaxNo);
    void  restoreTrueClause(int v, int MaxNo);
    void  rebuildwatch(int CurNo);
    bool  restoreAuxUnit();
   
    void extractUnit(int & unitproof);
    void removeProofunit( vec <UnitIndex> & unit);
    int  decisionLevel () {return trail_lim.size();}
    int  origVars,cutLen;
    void reAttachlearnt(int end);
    void eqvForwardshift (int ulit, int begin, int CurNo);
    void restoreTmpdetach( );
    void swapEqTofront(Lit * lits, int sz, int eqVal);
    int  moveEqTofront(vec <Lit> & preLit,vec <Lit> & curLit,vec <Lit> & nxtLit);
    void Localbackwardshift(int begin, int end);
    void detachpartClause(int m,int localcut);
    void DelInference(int & Delidx,int low);
    int  finddelstart(int begin, int end,int timeNo);
    int  eqvForwardmode, winmode;
   
    lbool   value      (Lit p) const;       // The current value of a literal.
    int     nClauses   ()      const { return clauses.size(); }       // number of original clauses.
    int     nVars      ()      const { return assigns.size(); }     // number of variables.

    double  garbage_frac;  // The fraction of wasted memory allowed 
    void garbageCollect();
    void checkGarbage(){
          if (ca.wasted() > ca.size() * garbage_frac)  garbageCollect(); 
    }
    int       verbosity;
 
  protected:
    OccLists<Lit, vec<WatcherL> >  watches, corewatch; 
    OccLists<Lit, vec<Watcher> >   watchesBin;    
 
    CRef getCref(int clsNo){
          if(clsNo<=0) return clauses[-clsNo];
          else         return learnts[clsNo-1];
    }
   
    vec<CRef>           clauses;          // List of problem clauses.
    vec<CRef>           learnts;          // List of learnt clauses.
    vec<lbool>          assigns;          // The current assignments.
    vec<Lit>            trail;            // Assignment stack; 
    vec<int>            trail_lim;        // Separator indices for different decision levels in 'trail'.
    int                 qhead;            // Head of queue (as index into the trail) 

    ClauseAllocator     ca;
    vec<Lit>            add_tmp;
 
    void     newDecisionLevel ();                // Begins a new decision level.
    void     uncheckedEnqueue (Lit p, int from=cNo_Undef); // Enqueue a literal. 
    bool     propagateMax      (int maxCNo);     // Perform unit propagation. Returns conflict clause.
    bool     propagate3        ();
    bool     propagateCore     ();
    void     clearCoreflag     (int last);

    bool     double_propagate (int maxCNo);
    void     cancelUntil      (int level);      // Backtrack until a certain level.
    void     analyze_used_notrace(int confl);
    void     analyze_used_trace(int confl);
    void     analyze_used_tmp_notrace(int confl);
    void     analyze_used_tmp_trace(int confl);
    bool     shiftmode;
    void     analyze_used(int confl);
  
    void     attachClause (CRef cr, int clsNo);    // Attach a clause to watcher lists.
    void     detachClause0(Clause & c, int clsNo);
    CRef     detachClause     (int clsNo);        // Detach a clause to watcher lists.
    int      remNum;
    void     removeClause     (int clsNo);        // Detach and free a clause.
    void     rebuildwatch();
    void     prePropagate(int CurNo);
    vec<int> *trueClause;
  
    void     saveDetach(int level,int minNo);
    void     saveDetach       (int level, int minNo, int & minClauseNo,vec<int>  & detachClsNo);
    void     restoreDetach    ();
    void     restoreDetach    (int & minClauseNo, vec<int>  & detachClsNo);
    vec<int> detachClsNo1,detachClsNo2;
    int      minClauseNo1,minClauseNo2;

    vec<int> lit_begin_end;
    vec<char> seen;
    char *varusemark;
    vec<int> reason;
    vec<int> varLevel;
    
    int      maxdisFirstvar;
    int      shiftproof;

    void     clearWatch( vec<Watcher> &  ws);
    void     clearAllwatch();
    void     clearWatch( vec<WatcherL> & wsL);
    void     setvarLevel(vec <UnitIndex> & c_unit);
    void     removeRepeatedCls(int end,int maxlevel);
   
    void     offtrueClause(CRef cr,int No,int maxlevel);
   
    void     relocAll (ClauseAllocator& to);

    int      auxUnitmode;
	bool     checkRup(int LerantNo,vec <Lit> & lits);
    int      unitproof, proofn, unproofn,refound,t_sz0;
	vec<bool> clauseDel,learntDel;
     
//rat check
    vec<int> RatcheckCls;
    bool  conflictCheck(int lrn_No, vec<Lit> & lits);
    char *RATvar;
    vec<int> *RATindex;
    void  setRATvar();
    void  setRATindex (Clause & c, int clsNo);
    void  removeRATindex (vec<Lit> & lits, int clsNo);
    void  buildRATindex ();
    int   RATCheck();
    bool  refind(int & cls_i, int lrn_i);
//tracecheck
    vec<int> antecedents;
    vec<int> tmp_antecedent;
    vec<int> tmp_unitID;
    int      shift_i;
    void     use_pre_antecedent();

    vec<int> unitClauseID;
    vec<Lit> unitzeroID;
    vec<int> unitID;
  
   void printracHead(int clsNo, vec <Lit> & lits);
    void printrace(int clsNo);
    void printrace2(int clsNo);
    void printRatBody(int clsNo);
    void printraceEnd();
    void TraceOrigClause();
    void printbody();

    void printEqRat1(int RatNo, vec <int> & lits);
    void printEqRat2(int clsNo, int RatNo, vec <int> & lits);
    int  origIDSize;
    int  getClauseID(int clsNo){
         return (clsNo<=0) ? -clsNo+1 : clsNo+origIDSize;
    }
    void unitpropagate();
    void traceUnit(int clsNo,int lit);
    void printEmptyclause1(int clsID, int cv);
    void printEmptyclause2();
    bool non_empty;
    int  maxClauseID, auxClauseID;
//
    bool  checkClauseSAT(int & cls_i);
    bool  checklearntSAT(int lrn_i);
};
//=================================================================================================

inline bool checker::addClause (const vec<Lit>& ps) { ps.copyTo(add_tmp); return addClause_(add_tmp); }
inline void     checker::newDecisionLevel()                      { trail_lim.push(trail.size()); }
inline lbool    checker::value         (Lit p) const   { return assigns[var(p)] ^ sign(p); }

}

#endif
