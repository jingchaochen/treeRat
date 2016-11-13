
#ifndef treeRat_System_h
#define treeRat_System_h

#if defined(__linux__)
#include <fpu_control.h>
#endif

#include "mtl/IntTypes.h"

//-------------------------------------------------------------------------------------------------

namespace treeRat {

static inline double cpuTime(void); // CPU-time in seconds.
extern double memUsed();            // Memory in mega bytes (returns 0 for unsupported architectures).
extern double memUsedPeak();        // Peak-memory in mega bytes (returns 0 for unsupported architectures).

}

//-------------------------------------------------------------------------------------------------
// Implementation of inline functions:

#if defined(_MSC_VER) || defined(__MINGW32__)
#include <time.h>

static inline double treeRat::cpuTime(void) { return (double)clock() / CLOCKS_PER_SEC; }

#else
#include <sys/time.h>
#include <sys/resource.h>
#include <unistd.h>

static inline double treeRat::cpuTime(void) {
    struct rusage ru;
    getrusage(RUSAGE_SELF, &ru);
    return (double)ru.ru_utime.tv_sec + (double)ru.ru_utime.tv_usec / 1000000; }

#endif

#endif
