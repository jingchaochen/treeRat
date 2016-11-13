
#ifndef treeRat_IntTypes_h
#define treeRat_IntTypes_h

#ifdef __sun
    // Not sure if there are newer versions that support C99 headers. The
    // needed features are implemented in the headers below though:

#   include <sys/int_types.h>
#   include <sys/int_fmtio.h>
#   include <sys/int_limits.h>

#else

#   include <stdint.h>
#   include <inttypes.h>

#endif

#include <limits.h>

#ifndef PRIu64
#define PRIu64 "lu"
#define PRIi64 "ld"
#endif
//=================================================================================================

#endif
