/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.2 $ */

#include <limits.h>
#include <math.h>
#include <stdio.h>
#include "cnfforms.h"
#include "good-rnd.h"
#include "safemall.h"
#include "ballbin.h"

void balls_in_bins( long ball_count, long bin_count )
{
  size_t max_prop_length;
  long i, j, k, prop_count, clause_count, counter;
  literal current_lit;

  /* 1.  Error-checking. */
  if( ball_count < 1 )
    fatal_error( "balls_in_bins:  Number of balls is too small" );
  if( bin_count < 1 )
    fatal_error( "balls_in_bins:  Number of bins is too small" );
  if( bin_count > SCHAR_MAX )
    fatal_error( "balls_in_bins:  Number of bins is too large" );
  /* There is no relationship that has to hold between the number
     of balls and the number of bins. */

  /* 2.  Basic initialization. */
  prop_count = ball_count * bin_count;
  /* This formula is taken from [Jeroslow and Wang, 1990]. */
  clause_count =
    ball_count *
      (2 + bin_count * bin_count - 2 * bin_count + ball_count * bin_count)
        / 2;
  the_prop_count = prop_count;
  the_clause_count = clause_count;
  the_longest_clause_length = bin_count;
  max_prop_length =
    4 + digits_in_long( ball_count - 1 )
      + digits_in_long( bin_count - 1 );

  /* 3.  Initialize the_prop_list. */
  the_prop_list = proplist_empty( prop_count );
  the_prop_list->length = prop_count;

  counter = 0;
  for( i=0; i<ball_count; i++ )
    for( j=0; j<bin_count; j++ ) {
      the_prop_list->props[counter] =
        (proposition)safe_malloc( max_prop_length );
      (void)sprintf( the_prop_list->props[counter],
                     "p_%ld_%ld", i, j );
      counter++;
    }

  /* 4.  Initialize the_formula. */
  the_formula = formula_empty( clause_count );
  the_formula->length = clause_count;

  /* 5.  Construct the clauses and add them to the_formula. */
  counter = 0;

  /* 5.a.  Construct the clauses stipulating that every ball must
     be placed in at least one bin. */
  for( i=0; i<ball_count; i++ ) {
    the_formula->clauses[counter].length = bin_count;
    current_lit =
      the_formula->clauses[counter].members =
        (literal_object *)
          safe_malloc( sizeof(literal_object) * (size_t)bin_count );
    for( j=0; j<bin_count; j++, current_lit++ ) {
      current_lit->sign = Pos;
      current_lit->p_index = bin_count * i + j;
    }
    counter++;
  }

  /* 5.b.  Construct the clauses stipulating that no ball can
     occur in two different bins. */
  for( i=0; i<ball_count; i++ )
    for( j=0; j<bin_count; j++ )
      for( k=j+1; k<bin_count; k++ ) {
        the_formula->clauses[counter].length = 2;
        current_lit =
          the_formula->clauses[counter].members =
            (literal_object *)
              safe_malloc( sizeof(literal_object) * 2 );
        current_lit->sign = Neg;
        current_lit->p_index = bin_count * i + j;
        current_lit++;
        current_lit->sign = Neg;
        current_lit->p_index = bin_count * i + k;
        counter++;
      }

  /* 5.c.  Construct the clauses stipulating that no bin can hold
     two different balls.  This is symmetric to 5.b. */
  for( i=0; i<bin_count; i++ )
    for( j=0; j<ball_count; j++ )
      for( k=j+1; k<ball_count; k++ ) {
        the_formula->clauses[counter].length = 2;
        current_lit =
          the_formula->clauses[counter].members =
            (literal_object *)
              safe_malloc( sizeof(literal_object) * 2 );
        current_lit->sign = Neg;
        current_lit->p_index = bin_count * j + i;
        current_lit++;
        current_lit->sign = Neg;
        current_lit->p_index = bin_count * k + i;
        counter++;
      }
}
