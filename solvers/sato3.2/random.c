#include "main.h"
#include "random.h"

/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.2 $ */

/* Generate an instance of a random K-SAT problem. */
void random_ksat_init( prop_count, clause_count, clause_length )
     int prop_count, clause_count, clause_length;
{
  /* 1. Error-checking. */
  if( prop_count >= MAX_ATOM )
    fatal_error( "random_ksat:  Number of propositions is too big" );
  if( prop_count < 2 )
    fatal_error( "random_ksat:  Number of propositions is too small" );
  if( clause_count < prop_count )
    fatal_error( "random_ksat:  Number of clauses is too small" );
  if( clause_length < 2 )
    fatal_error( "random_ksat:  Clause length is too small" );
  if( clause_length > prop_count )
    fatal_error( "random_ksat:  Clause length is too large" );

  /* 2.  Initialize */
  random_seed -= LINE;
  Max_clause = QGROUP;
  Max_atom = prop_count;
  existing_props = tiset_emptyset( prop_count );
}

/* Generate an instance of a random K-SAT problem. */
int random_ksat_cls(clause_count, clause_length )
     int clause_count, clause_length;
{
  int i;

  for( i=0; i<clause_count; i++ ) {
    if (ksat_make_mitchell( Max_atom, clause_length )) return 1;
  }

  /*tiset_free( existing_props );*/
  return 0;
}

/* Generate a clause for random K-SAT (Mitchell et al.'s version). */
int ksat_make_mitchell( pcount, clength )
     int pcount, clength;
{
  long guess;
  int i;
  int cl_arr[MAX_ATOM], sign_arr[MAX_ATOM];

  for( i=0; i<clength; i++ ) {
    do {
      guess = random_long( pcount );
    } while ( tiset_member(existing_props, guess) );
    tiset_adjoin( existing_props, guess );
    insert_one_key(++guess, random_long(2), cl_arr, sign_arr, i);
  }
  tiset_delete_all( existing_props );

  Clause_num++;
  return (insert_clause(cl_arr, sign_arr, clength));
}


/* Finite sets with indexed elements, where the range of the possible
   indices is known in advance. */
/* This implementation is faster but consumes more space. */

time_index_set tiset_emptyset( limit )
     long limit;
{
  int i;
  time_index_set result;
  
  result = (time_index_set)tp_alloc( sizeof(time_index_set_object) );
  result->length = 0;
  result->limit = limit;
  result->dense_array =
    (long *)tp_alloc( sizeof(long) * (size_t)limit );
  result->sparse_array =
    (long *)tp_alloc( sizeof(long) * (size_t)limit );
  for( i=0; i<limit; i++ )
    result->sparse_array[i] = TISET_NOVALUE;
  return result;
}

void tiset_adjoin( tiset, elt )
     time_index_set tiset;
     long elt;
{
  if( tiset->sparse_array[elt] == TISET_NOVALUE ) {
    long tiset_length = tiset->length;

    tiset->sparse_array[elt] = tiset_length;
    tiset->dense_array[tiset_length] = elt;
    tiset->length++;
  }
}

void tiset_delete_all( tiset )
     time_index_set tiset;
{
  long i, tiset_length;

  tiset_length = tiset->length;
  for( i=0; i<tiset_length; i++ )
    tiset->sparse_array[tiset->dense_array[i]] = TISET_NOVALUE;
  tiset->length = 0;
}
