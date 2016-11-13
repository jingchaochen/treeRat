
#ifndef treeRat_XAlloc_h
#define treeRat_XAlloc_h

#include <errno.h>
#include <stdlib.h>
#include <stdio.h>

namespace treeRat {

//=================================================================================================
// Simple layer on top of malloc/realloc to catch out-of-memory situtaions and provide some typing:

class OutOfMemoryException{};
static inline void* xrealloc(void *ptr, size_t size)
{
    void* mem = realloc(ptr, size);
    if (mem == NULL && errno == ENOMEM){
        throw OutOfMemoryException();
    }else {
        return mem;
	}
}

//=================================================================================================
}

#endif
