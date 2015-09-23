/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.2 $ */

#include <limits.h>
#include <math.h>
#include <stdio.h>
#include "cnfforms.h"
#include "safemall.h"
#include "n-queens.h"

void n_queens( long n, int for_gsat )
{
  size_t max_prop_length;
  long i, j, k;
  long prop_count, clause_count;
  long counter;
  literal current_lit;

  /* 1.  Error-checking. */
  if( n < 4 )
    fatal_error( "n_queens:  Number of queens is too small" );
  if( n > SCHAR_MAX )
    fatal_error( "n_queens:  Number of queens is too large" );
  
  /* 2.  Basic initialization. */
  prop_count = n * n;
  if( for_gsat )
    clause_count = n * ((5 * n * n) - (6 * n) + 4) / 3;
  else
    clause_count = n * ((5 * n * n) - (6 * n) + 7) / 3;
  the_prop_count = prop_count;
  the_clause_count = clause_count;
  the_longest_clause_length = n;
  max_prop_length = 4 + 2 * digits_in_long( prop_count - 1 );

  /* 3.  Initialize the_prop_list. */
  the_prop_list = proplist_empty( prop_count );
  the_prop_list->length = prop_count;

  counter = 0;
  for( i=0; i<n; i++ )
    for( j=0; j<n; j++ ) {
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

  /* 5.a.  Construct the n positive row clauses. */
  for( i=0; i<n; i++ ) {
    the_formula->clauses[counter].length = n;
    current_lit =
      the_formula->clauses[counter].members =
        (literal_object *)
          safe_malloc( sizeof(literal_object) * (size_t)n );
    for( j=0; j<n; j++, current_lit++ ) {
      current_lit->sign = Pos;
      current_lit->p_index = n * i + j;
    }
    counter++;
  }

  /* 5.b.  Construct the n positive column clauses, but only if
     we're not using GSAT to solve this problem. */
  if( !for_gsat )
    for( i=0; i<n; i++ ) {
      the_formula->clauses[counter].length = n;
      current_lit =
        the_formula->clauses[counter].members =
          (literal_object *)
            safe_malloc( sizeof(literal_object) * (size_t)n );
      for( j=0; j<n; j++, current_lit++ ) {
        current_lit->sign = Pos;
        current_lit->p_index = n * j + i;
      }
      counter++;
    }

  /* 5.c.  Construct the n * (n choose 2) negative row clauses. */
  for( i=0; i<n; i++ )
    for( j=0; j<n; j++ )
      for( k=j+1; k<n; k++ ) {
        the_formula->clauses[counter].length = 2;
        current_lit =
          the_formula->clauses[counter].members =
            (literal_object *)
              safe_malloc( sizeof(literal_object) * 2 );
        current_lit->sign = Neg;
        current_lit->p_index = n * i + j;
        current_lit++;
        current_lit->sign = Neg;
        current_lit->p_index = n * i + k;
        counter++;
      }

  /* 5.d.  Construct the n * (n choose 2) negative column clauses. */
  for( i=0; i<n; i++ )
    for( j=0; j<n; j++ )
      for( k=j+1; k<n; k++ ) {
        the_formula->clauses[counter].length = 2;
        current_lit =
          the_formula->clauses[counter].members =
            (literal_object *)
              safe_malloc( sizeof(literal_object) * 2 );
        current_lit->sign = Neg;
        current_lit->p_index = n * j + i;
        current_lit++;
        current_lit->sign = Neg;
        current_lit->p_index = n * k + i;
        counter++;
      }

  /* 5.e.  Construct the negative left-to-right diagonal clauses. */

  /* 5.e.i.  Construct the clauses for the main diagonal. */
  for( i=0; i<n; i++ )
    for( j=i+1; j<n; j++ ) {
      the_formula->clauses[counter].length = 2;
      current_lit =
        the_formula->clauses[counter].members =
          (literal_object *)
            safe_malloc( sizeof(literal_object) * 2 );
      current_lit->sign = Neg;
      current_lit->p_index = n * i + i;
      current_lit++;
      current_lit->sign = Neg;
      current_lit->p_index = n * j + j;
      counter++;
    }

  /* 5.e.ii.  Construct the clauses for the n-2 diagonals on its left.
     Symmetric to 5.e.iii. */
  for( i=1; i<n-1; i++ )
    for( j=i; j<n-1; j++ )
      for( k=j+1; k<n; k++ ) {
        the_formula->clauses[counter].length = 2;
        current_lit =
          the_formula->clauses[counter].members =
            (literal_object *)
              safe_malloc( sizeof(literal_object) * 2 );
        current_lit->sign = Neg;
        current_lit->p_index = n * j + (j - i);
        current_lit++;
        current_lit->sign = Neg;
        current_lit->p_index = n * k + (k - i);
        counter++;
      }

  /* 5.e.iii.  Construct the clauses for the n-2 diagonals on its right.
     Symmetric to 5.e.ii. */
  for( i=1; i<n-1; i++ )
    for( j=i; j<n-1; j++ )
      for( k=j+1; k<n; k++ ) {
        the_formula->clauses[counter].length = 2;
        current_lit =
          the_formula->clauses[counter].members =
            (literal_object *)
              safe_malloc( sizeof(literal_object) * 2 );
        current_lit->sign = Neg;
        current_lit->p_index = n * (j - i) + j;
        current_lit++;
        current_lit->sign = Neg;
        current_lit->p_index = n * (k - i) + k;
        counter++;
      }

  /* 5.f.  Construct the negative right-to-left diagonal clauses. */

  /* 5.f.i.  Construct the clauses for the main diagonal. */
  for( i=0; i<n; i++ )
    for( j=i+1; j<n; j++ ) {
      the_formula->clauses[counter].length = 2;
      current_lit =
        the_formula->clauses[counter].members =
          (literal_object *)
            safe_malloc( sizeof(literal_object) * 2 );
      current_lit->sign = Neg;
      current_lit->p_index = n * i + (n - 1) - i;
      current_lit++;
      current_lit->sign = Neg;
      current_lit->p_index = n * j + (n - 1) - j;
      counter++;
    }

  /* 5.f.ii.  Construct the clauses for the n-2 diagonals on its left. */
  for( i=1; i<n-1; i++ )
    for( j=i; j<n-1; j++ )
      for( k=j+1; k<n; k++ ) {
        the_formula->clauses[counter].length = 2;
        current_lit =
          the_formula->clauses[counter].members =
            (literal_object *)
              safe_malloc( sizeof(literal_object) * 2 );
        current_lit->sign = Neg;
        current_lit->p_index = n * ((n - 1) - j) + (j - i);
        current_lit++;
        current_lit->sign = Neg;
        current_lit->p_index = n * ((n - 1) - k) + (k - i);
        counter++;
      }

  /* 5.f.iii.  Construct the clauses for the n-2 diagonals on its right. */
  for( i=1; i<n-1; i++ )
    for( j=i; j<n-1; j++ )
      for( k=j+1; k<n; k++ ) {
        the_formula->clauses[counter].length = 2;
        current_lit =
          the_formula->clauses[counter].members =
            (literal_object *)
              safe_malloc( sizeof(literal_object) * 2 );
        current_lit->sign = Neg;
        current_lit->p_index = n * ((n - 1) + i - j) + j;
        current_lit++;
        current_lit->sign = Neg;
        current_lit->p_index = n * ((n - 1) + i - k) + k;
        counter++;
      }
}
