/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.2 $ */

#ifndef SAFE_MALLOC_H
#define SAFE_MALLOC_H

#ifdef THINK_C
#include "size_t.h"
#else
#include <stdlib.h>  /* To get size_t */
#endif

/* If this counter is 0 at the end of the program, then the total
   number of malloc()'s equals the total number of free()'s. */

#ifdef DEBUG
extern long malloc_counter;
#endif

void fatal_error( char * );

void *safe_malloc( size_t );

void safe_free( void * );

#endif
