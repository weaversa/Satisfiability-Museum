/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.2 $ */

#include <memory.h>
#include <stdio.h>
#include <math.h>
#include "good-rnd.h"
#include "misc.h"
#include "safemall.h"
#include "timeiset.h"

#ifdef THINK_C
#include <size_t.h>
void *memcpy(void *s1, const void *s2, size_t n);
#endif

time_index_set tiset_emptyset( long limit )
{
  long i;
  time_index_set result;
  
#ifdef DEBUG
  if( limit <= 0 )
    fatal_error( "tiset_emptyset:  Invalid range" );
#endif
  result = (time_index_set)safe_malloc( sizeof(time_index_set_object) );
  result->length = 0;
  result->limit = limit;
  result->dense_array =
    (long *)safe_malloc( sizeof(long) * (size_t)limit );
  result->sparse_array =
    (long *)safe_malloc( sizeof(long) * (size_t)limit );
  for( i=0; i<limit; i++ )
    result->sparse_array[i] = TISET_NOVALUE;
  return result;
}

/* Assumption:  tiset_to->limit >= tiset_from->limit. */

void tiset_copy( time_index_set tiset_to, time_index_set tiset_from )
{
  long i, from_length, *from_members;

  from_length = tiset_cardinality( tiset_from );
  from_members = tiset_members( tiset_from );

  tiset_delete_all( tiset_to );
  for( i=0; i<from_length; i++ )
    tiset_unsafe_adjoin( tiset_to, from_members[i] );
}

void tiset_adjoin( time_index_set tiset, long elt )
{
  if( tiset->sparse_array[elt] == TISET_NOVALUE ) {
    long tiset_length = tiset->length;

    tiset->sparse_array[elt] = tiset_length;
    tiset->dense_array[tiset_length] = elt;
    tiset->length++;
  }
}

void tiset_delete( time_index_set tiset, long elt )
{
  long dense_index = tiset->sparse_array[elt];

  if( dense_index != TISET_NOVALUE ) {
    long tiset_length = tiset->length;

    if( dense_index + 1 < tiset_length ) {
      long copied_index = tiset->dense_array[tiset_length - 1];

      tiset->sparse_array[copied_index] = dense_index;
      tiset->dense_array[dense_index] = copied_index;
    }
    tiset->sparse_array[elt] = TISET_NOVALUE;
    tiset->length--;
  }
}

/* Add all of the elements in the second set to the first set.
   Assumption:  tiset1->limit >= tiset2->limit. */

void tiset_union( time_index_set tiset1, time_index_set tiset2 )
{
  long i, cardinality2, *members2;

  cardinality2 = tiset_cardinality( tiset2 );
  members2 = tiset_members( tiset2 );
  for( i=0; i<cardinality2; i++ )
    tiset_adjoin( tiset1, members2[i] );
}

/* Delete all of the members of tiset2 from tiset1. */

void tiset_difference( time_index_set tiset1, time_index_set tiset2 )
{
  long i, cardinality2, *members2;

  cardinality2 = tiset_cardinality( tiset2 );
  members2 = tiset_members( tiset2 );
  for( i=0; i<cardinality2; i++ )
    tiset_delete( tiset1, members2[i] );
}

void tiset_print( time_index_set tiset )
{
  long i, tiset_length;

  tiset_length = tiset->length;
  fprintf( stderr, "There are %ld elements in the set:\n[", tiset_length );
  if( tiset_length ) {
    for( i=0; i<tiset_length - 1; i++ )
      fprintf( stderr, "%ld, ", tiset->dense_array[i] );
    fprintf( stderr, "%ld", tiset->dense_array[tiset_length - 1] );
  }
  fprintf( stderr, "]\n" );
}

void tiset_delete_all( time_index_set tiset )
{
  long i, tiset_length;

  tiset_length = tiset->length;
  for( i=0; i<tiset_length; i++ )
    tiset->sparse_array[tiset->dense_array[i]] = TISET_NOVALUE;
  tiset->length = 0;
}

void tiset_double_size( time_index_set tiset )
{
  long i, old_limit, new_limit;
  long *new_array;

  old_limit = tiset->limit;
  new_limit = old_limit * 2;
  tiset->limit = new_limit;

  new_array = (long *)safe_malloc( sizeof(long) * (size_t)new_limit );
  (void)memcpy( (char *)new_array,
                (char *)tiset->dense_array,
                sizeof(long) * (size_t)old_limit );
  /* There's no need to initialize the rest of the array. */
  safe_free( tiset->dense_array );
  tiset->dense_array = new_array;

  new_array = (long *)safe_malloc( sizeof(long) * (size_t)new_limit );
  (void)memcpy( (char *)new_array,
                (char *)tiset->sparse_array,
                sizeof(long) * (size_t)old_limit );
  for( i=old_limit; i<new_limit; i++ )
    new_array[i] = TISET_NOVALUE;
  safe_free( tiset->sparse_array );
  tiset->sparse_array = new_array;
}

void tiset_free( time_index_set tiset )
{
  safe_free( tiset->dense_array );
  safe_free( tiset->sparse_array );
  safe_free( tiset );
}
