/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.2 $ */

#ifndef SUNOS
#ifndef THINK_C
#include <malloc.h>
#endif /* THINK_C */
#endif /* SUNOS */
#include <memory.h>
#include <stdio.h>
#include "safemall.h"
#include "poly.h"

#ifdef THINK_C
void *memcpy(void *s1, const void *s2, size_t n);
#endif

#ifdef SUNOS
void *realloc( void *, size_t );
#endif

void append_to_array( char **base, size_t width, long *nelm,
                      long *size, char *next )
{
  char *destination;

  if( *nelm == *size ) {
    long new_size;
    char *new_base;

    new_size = 2 * (*size);
    new_base = realloc( *base, width * (size_t)new_size );
    if( new_base == NULL )
      fatal_error( "append_to_array:  realloc() returned NULL" );
    *base = new_base;
    *size = new_size;
  }
  destination = (*base) + (*nelm) * width;
  (void)memcpy( destination, next, width );
  (*nelm)++;
}
