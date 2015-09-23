/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.2 $ */

#include <limits.h>
#include <math.h>
#include <stdio.h>
#include "safemall.h"
#include "cnfforms.h"
#include "timeiset.h"
#include "good-rnd.h"
#include "rnd-ksat.h"

/* For ensuring that no clause contains more than one literal
   associated with the same proposition. */

static time_index_set existing_props;

/* Generate a clause for random K-SAT (Mitchell et al.'s version). */

static void ksat_make_mitchell( literal_object *lobjs,
                                long pcount, long clength )
{
  long i, guess;

  for( i=0; i<clength; i++ ) {
    do {
      guess = random_long( pcount );
    } while ( tiset_member(existing_props, guess) );
    tiset_adjoin( existing_props, guess );
    lobjs[i].p_index = guess;
    lobjs[i].sign = (random_long(2) ? Pos : Neg);
  }
  tiset_delete_all( existing_props );
}

/* Generate an instance of a random K-SAT problem. */

void random_ksat( long prop_count, long clause_count,
                  long clause_length, int long_clause )
{
  size_t max_prop_length;
  long i;

  /* 1. Error-checking. */
  if( prop_count < 2 )
    fatal_error( "random_ksat:  Number of propositions is too small" );
  if( clause_count < prop_count )
    fatal_error( "random_ksat:  Number of clauses is too small" );
  if( clause_length < 2 )
    fatal_error( "random_ksat:  Clause length is too small" );
  if( clause_length > prop_count ||
      clause_length > SCHAR_MAX )
    fatal_error( "random_ksat:  Clause length is too large" );

  /* 2.  Initialize the_prop_count, the_clause_count, etc. */
  the_prop_count = prop_count;
  the_clause_count = clause_count;
  the_longest_clause_length = clause_length;
  max_prop_length = 3 + digits_in_long( prop_count - 1 );

  /* 3.  Initialize existing_props. */
  existing_props = tiset_emptyset( prop_count );

  /* 4.  Initialize the_prop_list. */
  the_prop_list = proplist_empty( prop_count );
  the_prop_list->length = prop_count;
  for( i=0; i<prop_count; i++ ) {
    the_prop_list->props[i] =
      (proposition)safe_malloc( sizeof(char) * max_prop_length );
    (void)sprintf( the_prop_list->props[i], "p_%ld", i );
  }

  /* 5.  Initialize the_formula. */

  the_formula = formula_empty( clause_count );
  the_formula->length = clause_count;
  for( i=0; i<clause_count; i++ ) {
    the_formula->clauses[i].length = clause_length;
    the_formula->clauses[i].members = 
      (literal_object *)
        safe_malloc( sizeof(literal_object) * (size_t)clause_length );
    ksat_make_mitchell( the_formula->clauses[i].members,
                        prop_count,
                        clause_length );
  }

  /* 6.  Clean up. */

  tiset_free( existing_props );
}
