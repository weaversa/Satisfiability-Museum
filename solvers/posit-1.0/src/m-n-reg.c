/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.2 $ */

#include <limits.h>
#include <math.h>
#include <stdio.h>
#include "cnfforms.h"
#include "timeiset.h"
#include "good-rnd.h"
#include "safemall.h"
#include "m-n-reg.h"

/* For keeping track of the clauses that still have room for
   an additional literal. */

static time_index_set unexhausted_clauses;

/* For keeping track of the propositions that have not yet been
   distributed. */

static time_index_set unexhausted_props;

/* For each proposition p_i, "sprinkle" posct occurrences of Pos p_i
   and negct occurrences of Neg p_i among the clauses in the formula.
   To avoid painting yourself into a corner, sprinkle the literals
   in waves, where each clause gains exactly one new literal in each
   wave. */

void mnreg_make_clauses( long posct, long negct, long propct,
                         long clength, long ccount )
{
  clause curr_clause;
  literal curr_literal;
  long prop_guess, clause_guess;
  long totalct, pos_remaining, neg_remaining;
  long i, j, k;

  totalct = posct + negct;

  for( i=0; i<propct; i++ ) {
    prop_guess = tiset_choose( unexhausted_props );
    tiset_delete( unexhausted_props, prop_guess );
    pos_remaining = posct;
    neg_remaining = negct;

    for( j=0; j<totalct; j++ ) {
      if( tiset_isempty(unexhausted_clauses) )
        for( k=0; k<ccount; k++ )
          tiset_adjoin( unexhausted_clauses, k);
      clause_guess = tiset_choose( unexhausted_clauses );
      tiset_delete( unexhausted_clauses, clause_guess );
      curr_clause = &(the_formula->clauses[clause_guess]);
      curr_literal = &(curr_clause->members[curr_clause->length]);
      curr_literal->p_index = prop_guess;
      if( pos_remaining && !neg_remaining ) {
        curr_literal->sign = Pos;
        pos_remaining--;
      }
      else if( neg_remaining && !pos_remaining ) {
        curr_literal->sign = Neg;
        neg_remaining--;
      }
      else if( random_long(totalct - j) < pos_remaining ) {
        curr_literal->sign = Pos;
        pos_remaining--;
      }
      else {
        curr_literal->sign = Neg;
        neg_remaining--;
      }
      curr_clause->length++;
    }
  }
}

/* Generate an instance of an m-n-regular problem. */

void m_n_regular( long pos_count, long neg_count,
                  long prop_count, long clause_length )
{
  size_t max_prop_length;
  long i, clause_count;

  /* 1.  Error checking. */
  if( pos_count < 1 )
    fatal_error( "m_n_regular:  pos_count is too small" );
  if( neg_count < 1 )
    fatal_error( "m_n_regular:  neg_count is too small" );
  if( prop_count < 2 )
    fatal_error( "m_n_regular:  Number of propositions is too small" );
  if( clause_length < 2 )
    fatal_error( "m_n_regular:  Clause length is too small" );
  if( clause_length > prop_count ||
      clause_length > SCHAR_MAX )
    fatal_error( "m_n_regular:  Clause length is too large" );
  if( ((pos_count + neg_count) * prop_count) % clause_length )
    fatal_error( "m_n_regular:  Invalid formula" );

  /* 2.  Calculate the_prop_count, the_clause_count, etc. */
  the_longest_clause_length = clause_length;
  max_prop_length = 3 + digits_in_long( prop_count - 1 );
  clause_count = ((pos_count + neg_count) * prop_count) / clause_length;
  if( (pos_count + neg_count) > clause_count )
    fatal_error( "m_n_regular:  Number of clauses is too small" );
  the_prop_count = prop_count;
  the_clause_count = clause_count;

  /* 3.  Initialize the auxiliary data structures. */
  unexhausted_clauses = tiset_emptyset( clause_count );
  for( i=0; i<clause_count; i++ )
    tiset_adjoin( unexhausted_clauses, i );
  unexhausted_props = tiset_emptyset( prop_count );
  for( i=0; i<prop_count; i++ )
    tiset_adjoin( unexhausted_props, i );

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
    the_formula->clauses[i].length = 0;  /* Not clause_length!! */
    the_formula->clauses[i].members =
      (literal_object *)
        safe_malloc( sizeof(literal_object) * (size_t)clause_length );
  }

  /* 6.  Construct the clauses in the_formula. */
  mnreg_make_clauses( pos_count, neg_count, prop_count,
                      clause_length, clause_count );

  /* 7.  Clean up. */
  tiset_free( unexhausted_clauses );
  tiset_free( unexhausted_props );
}
