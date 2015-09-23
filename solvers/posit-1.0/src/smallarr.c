/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.2 $ */

#include <limits.h>
#include <stdio.h>
#include "safemall.h"
#include "smallarr.h"


small_array sarray_empty( long range )
{
  small_array result;

  result = (small_array)safe_malloc( sizeof(small_array_object) );
  result->real_members =
    (long *)safe_malloc( (size_t)(2 * range) * sizeof(long) );
  result->real_costs =
    (long *)safe_malloc( (size_t)(2 * range) * sizeof(long) );
  result->offset = range;
  result->members = result->real_members + range;
  result->costs = result->real_costs + range;
  result->length = 0;
  result->size = range;

  return result;
}

void sarray_print( small_array sa )
{
  long i;

  fprintf( stderr, "[%ld %ld [%ld %ld] ",
           sa->length,
           sa->size,
           sa->max_cost,
           sa->min_cost );
  for( i=0; i<sa->length; i++ )
    fprintf( stderr, "(%ld %ld) ", sa->members[i], sa->costs[i] );
  fprintf( stderr, "\n" );
}

void sarray_free( small_array sa )
{
  safe_free( sa->real_members );
  safe_free( sa->real_costs );
  safe_free( sa );
}
