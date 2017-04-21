
#ifndef treeRat_checker_h
#define treeRat_checker_h

#include "mtl/Vec.h"
#include "mtl/Alg.h"
#include "utils/Options.h"
#include "core/checkerTypes.h"

#define _FILE_OFFSET_BITS 64
#define _LARGE_FILES

#define cNo_Undef 0x3fffffff

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
    vec <UnitIndex> r_unit;
    vec <UnitIndex> cur_unit;
    int *occLit;
   
    vec <DelInfo> Delqueue;
    int lastDel,Delq_active;
    void  readdelclause(int i,vec <Lit>  & lits);
   
    void DelRedundancyLit(vec <Lit> & lits,int No);
    bool activateDelinfo(int & end, vec <UnitIndex> & c_unit);
    int  match(int h, Lit * lits, int len,int curNo);
    int  match3(int h, Lit * lits);
    vec<int> * hashtbl;
    void clearHashtbl(int cur_delno);
    void restoreDelClause(int CurNo);
    void DetachDelClause();
    void DetachWatch(int begin, int end);
    void detachWatch( vec<Watcher>& ws, int begin, int end);
    void detachWatch( vec<WatcherL>& ws, int begin, int end);
    void deletewatch(int CurNo);

    FILE *rat_fp;
    void  readratOutput(char * rupfile);
    int   forwardCheck();
    void  simplifylearnt(int CurNo);
    void  reducebufferlearnt();
    bool  finddetachUnit();

    void  readfile(int i,vec <Lit>  & lits);
    bool  isconflict(vec<Lit> & lits);
  
    int   backwardCheck();
    bool  simplifyUnit(vec <UnitIndex> & new_unit);
    bool  getcurUnit(vec <UnitIndex> & c_unit,int mode);

    void  printwatchsize();
    int   maxCoreNo;
    void  removeTrailUnit(Lit uLit,int MaxNo);
    void  cancelloadtrueCls(int lev,int MaxNo);
    void  restoreTrueClause(int v, int MaxNo);
    void  rebuildwatch(int CurNo);
    bool  restoreAuxUnit();

    bool extractUnit(int & proofn, int & unitproof);
    void removeProofunit( vec <UnitIndex> & unit);
    int  decisionLevel () {return trail_lim.size();}
    int  attClauses, origVars,cutLen;
    void swapEqTofront(Clause & c, int eqVal);
    void moveEqTofront(int preIdx, int curIdx, int ppIdx,int & eqvLen);
    void eqvForwardcheck(Lit lit, int CurNo);
    int  eqvForwardmode, winmode;

    void loadfalselitclause();
  
    lbool   value      (Lit p) const;       // The current value of a literal.
    int     nClauses   ()      const { return clauses.size(); }       // The current number of original clauses.
    int     nVars      ()      const { return assigns.size(); }     // The current number of variables.

    double  garbage_frac;  // The fraction of wasted memory allowed before a garbage collection is triggered.
    void garbageCollect();
    void checkGarbage(){
          if (ca.wasted() > ca.size() * garbage_frac)  garbageCollect(); 
    }
    int       verbosity;
 
  protected:
    OccLists<Lit, vec<WatcherL> >  watches; 
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
    int                 qhead,ori_fixed;            // Head of queue (as index into the trail 

    ClauseAllocator     ca;
    vec<Lit>            add_tmp;
 
    void     newDecisionLevel ();                // Begins a new decision level.
    void     uncheckedEnqueue (Lit p, int from=cNo_Undef); // Enqueue a literal. 
    bool     propagateMax      (int maxCNo);     // Perform unit propagation. Returns conflict clause.
    bool     propagate         ();
    bool     propagate2        ();
    bool     double_propagate (int maxCNo);
    void     cancelUntil      (int level);      // Backtrack until a certain level.
    void     analyze_used(int confl);
    
    void     attachClause (CRef cr, int clsNo);    // Attach a clause to watcher lists.
    void     attachClause2(CRef cr, int clsNo);
    void     detachClause0(Clause & c, int clsNo);
    CRef     detachClause     (int clsNo);        // Detach a clause to watcher lists.
    int      remNum;
    void     removeClause     (int clsNo);        // Detach and free a clause.
    void     rebuildwatch();

    void     saveDetach       (int level, int minNo);
    void     restoreDetach    ();

    void     loadbegin(int m);
    int      loadblock(int begin, int end, int earlyflag);
    vec<int> *trueClause;
    vec<int> detachClsNo;
    int      minClauseNo;

    vec<int> LitBegin;
    vec<int> LitEnd;
    vec<char> seen;
    vec<int> reason;
    vec<int> unitpos;
    
    int      *varLevel;
    void     clearWatch( vec<Watcher> &  ws);
    void     clearAllwatch();
    void     clearWatch( vec<WatcherL> & wsL);
    void     RemoveTrueClause(int extractMode);
    void     removeRepeatedCls(int end,int maxlevel);
    void     detachWatch( vec<Watcher>& ws);
    void     detachWatch( vec<WatcherL>& ws);

    void     offtrueClause(vec <Lit> & lits,int No);
    void     offtrueClause(CRef cr,int No,int maxlevel);
   
    void   relocAll (ClauseAllocator& to);

//rat check
    bool  conflictCheck(int No, vec<Lit> & lits,int & begin,int end);
    char *RATvar;
    vec<int> *RATindex;
    void  setRATvar();
    void  setRATindex (Clause & c, int clsNo);
    int   removeRATindex (vec<Lit> & lits, int clsNo);
    void  buildRATindex ();
    int   RATCheck();

    void  printwatch();
    void  printclause(Lit *lits, int sz);
  
    int   clauseUnfixed(Lit *lits, int sz);
    void  checkClauseSAT(vec<CRef> & cs,int n, int begin);
    void  checkClauseSAT(int curNo,int begin);
};
//=================================================================================================

inline bool checker::addClause (const vec<Lit>& ps) { ps.copyTo(add_tmp); return addClause_(add_tmp); }
inline void     checker::newDecisionLevel()                      { trail_lim.push(trail.size()); }
inline lbool    checker::value         (Lit p) const   { return assigns[var(p)] ^ sign(p); }

}

#endif
