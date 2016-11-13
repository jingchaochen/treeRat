
#ifndef treeRat_SolverTypes_h
#define treeRat_SolverTypes_h

#include <assert.h>

#include "mtl/IntTypes.h"
#include "mtl/Alg.h"
#include "mtl/Vec.h"
#include "mtl/Map.h"
#include "mtl/Alloc.h"

namespace treeRat {

//=================================================================================================
// Variables, literals, lifted booleans, clauses:


// NOTE! Variables are just integers. No abstraction here. They should be chosen from 0..N,
// so that they can be used as array indices.

typedef int Var;
#define var_Undef (-1)

//#define INT32_MIN (-2147483647L-1)

#define clsNo_Undef  INT32_MIN 

struct Lit {
    int     x;
    // Use this as a constructor:
    friend Lit mkLit(Var var, bool sign = false);
    bool operator == (Lit p) const { return x == p.x; }
    bool operator != (Lit p) const { return x != p.x; }
    bool operator <  (Lit p) const { return x < p.x;  } // '<' makes p, ~p adjacent in the ordering.
};

inline  Lit  mkLit     (Var var, bool sign) { Lit p; p.x = var + var + (int)sign; return p; }
inline  Lit  operator ~(Lit p)              { Lit q; q.x = p.x ^ 1; return q; }
inline  Lit  operator ^(Lit p, bool b)      { Lit q; q.x = p.x ^ (unsigned int)b; return q; }
inline  bool sign      (Lit p)              { return p.x & 1; }
inline  int  var       (Lit p)              { return p.x >> 1; }

// Mapping Literals to and from compact integers suitable for array indexing:
inline  int  toInt     (Var v)              { return v; } 
inline  int  toInt     (Lit p)              { return p.x; } 
inline  Lit  toLit     (int i)              { Lit p; p.x = i; return p; } 
inline  int  toIntLit  (Lit p)              { return sign(p) ? -(var(p)+1) : var(p)+1;} 

const Lit lit_Undef = { -2 };  // }- Useful special constants.
const Lit lit_Error = { -1 };  // }


//=================================================================================================
// Lifted booleans:
//
// NOTE: this implementation is optimized for the case when comparisons between values are mostly
//       between one variable and one constant. Some care had to be taken to make sure that gcc 
//       does enough constant propagation to produce sensible code, and this appears to be somewhat
//       fragile unfortunately.

#define l_True  (treeRat::lbool((uint8_t)0)) // gcc does not do constant propagation if these are real constants.
#define l_False (treeRat::lbool((uint8_t)1))
#define l_Undef (treeRat::lbool((uint8_t)2))

class lbool {
    uint8_t value;

public:
    explicit lbool(uint8_t v) : value(v) { }

    lbool()       : value(0) { }
    explicit lbool(bool x) : value(!x) { }

  //  bool  operator == (lbool b) const { return ((b.value&2) & (value&2)) | (!(b.value&2)&(value == b.value)); }
    bool  operator == (lbool b) const { return value == b.value;}
    bool  operator != (lbool b) const { return !(*this == b); }
    lbool operator ^  (bool  b) const { return lbool((uint8_t)(value^(uint8_t)b)); }

    lbool operator && (lbool b) const { 
        uint8_t sel = (this->value << 1) | (b.value << 3);
        uint8_t v   = (0xF7F755F4 >> sel) & 3;
        return lbool(v); }

    lbool operator || (lbool b) const {
        uint8_t sel = (this->value << 1) | (b.value << 3);
        uint8_t v   = (0xFCFCF400 >> sel) & 3;
        return lbool(v); }

    friend int   toInt  (lbool l);
    friend lbool toLbool(int   v);
};
inline int   toInt  (lbool l) { return l.value; }
inline lbool toLbool(int   v) { return lbool((uint8_t)v);  }

//=================================================================================================
// Clause -- a simple class for representing a clause:

class Clause;
typedef RegionAllocator<uint32_t>::Ref CRef;

class Clause {
    struct {
      unsigned freesize  : 3;
      unsigned detach    : 1;
      unsigned disk      : 1;
      unsigned size      : 26;
    }  header;
    union { Lit lit; CRef rel;} data[0];
    friend class ClauseAllocator;
    template<class V>
    Clause(const V & ps, bool learnt) {
        header.freesize  = 0;
        header.detach    = 0;
        header.disk      = 0;
        header.size      = ps.size();
        for (int i = 0; i < ps.size(); i++) data[i].lit = ps[i];
   }
public:
    int          size        ()      const   { return header.size; }
    void         size        (uint32_t sz)   { header.size=sz;  }
    uint32_t     freesize    ()      const   { return header.freesize;}
    void         freesize    (uint32_t m)    { header.freesize = m; }
    uint32_t     detach      ()      const   { return header.detach;}
    void         detach      (uint32_t df)   { header.detach = df;}
    uint32_t     disk        ()      const   { return header.disk;}
    void         disk        (uint32_t df)   { header.disk = df;}
    Lit&         operator [] (int i)         { return data[i].lit; }
    Lit          operator [] (int i) const   { return data[i].lit; }
    operator const Lit* (void) const         { return (Lit*)data; }
    operator Lit *       (void)              { return (Lit*)data; }

};

//=================================================================================================
// ClauseAllocator -- a simple class for allocating memory for clauses:

const CRef CRef_Undef = RegionAllocator<uint32_t>::Ref_Undef;
class ClauseAllocator : public RegionAllocator<uint32_t>
{
    static int clauseWord32Size(int size){
        return (sizeof(Clause) + (sizeof(Lit) * size)) / sizeof(uint32_t); }
 public:
    ClauseAllocator(uint32_t start_cap) : RegionAllocator<uint32_t>(start_cap){}
    ClauseAllocator(){}

    void moveTo(ClauseAllocator& to){ RegionAllocator<uint32_t>::moveTo(to); }

    template<class Lits>
    CRef alloc(const Lits & ps)
    {
        CRef cid = RegionAllocator<uint32_t>::alloc(clauseWord32Size(ps.size()));
        new (lea(cid)) Clause(ps, false);
        return cid;
    }
    // Deref, Load Effective Address (LEA), Inverse of LEA (AEL):
    Clause&       operator[](Ref r)       { return (Clause&)RegionAllocator<uint32_t>::operator[](r); }
    const Clause& operator[](Ref r) const { return (Clause&)RegionAllocator<uint32_t>::operator[](r); }
    Clause*       lea       (Ref r)       { return (Clause*)RegionAllocator<uint32_t>::lea(r); }
    const Clause* lea       (Ref r) const { return (Clause*)RegionAllocator<uint32_t>::lea(r); }
    Ref           ael       (const Clause* t){ return RegionAllocator<uint32_t>::ael((uint32_t*)t); }

    void free(CRef cid)
    {   Clause& c = operator[](cid);
        RegionAllocator<uint32_t>::free(clauseWord32Size(c.size()));
    }

    void reloc(CRef& cr, ClauseAllocator& to)
    {
        Clause& c = operator[](cr);
        cr = to.alloc(c);
        to[cr].freesize(c.freesize());
        to[cr].detach(c.detach());
        to[cr].disk(c.disk());
    }
};

//=================================================================================================
template<class Idx, class Vec>
class OccLists
{
    vec<Vec>  occs;
 public:
    void  init      (const Idx& idx){ occs.growTo(toInt(idx)+1);}
    Vec&  operator[](const Idx& idx){ return occs[toInt(idx)];}
    void  clear(bool free = true){ occs.clear(free);}
};

//=================================================================================================
}

 
#endif
