/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.2 $ */

#include <limits.h>
#include <math.h>
#include <stdio.h>
#include "cnfforms.h"
#include "good-rnd.h"
#include "safemall.h"
#include "graphclr.h"

void graph_coloring( long vertex_count, double edge_prob, long color_count )
{
  size_t max_prop_length;
  long i, j, k, prop_count, counter;
  clause_object current_clause_object;
  literal current_lit;

  /* 1.  Error-checking. */
  if( vertex_count < 1 )
    fatal_error( "graph_coloring:  Number of vertices is too small" );
  if( edge_prob < 0.0 )
    fatal_error( "graph_coloring:  Edge probability is too small" );
  if( edge_prob > 1.0 )
    fatal_error( "graph_coloring:  Edge probability is too large" );
  if( color_count < 1 )
    fatal_error( "graph_coloring:  Number of colors is too small" );
  if( color_count > SCHAR_MAX )
    fatal_error( "graph_coloring:  Number of colors is too large" );

  /* 2.  Basic initialization. */
  prop_count = vertex_count * color_count;
  the_prop_count = prop_count;
  the_longest_clause_length = color_count;
  max_prop_length =
    4 + digits_in_long( vertex_count - 1 )
      + digits_in_long( color_count - 1 );

  /* 3.  Initialize the_prop_list. */
  the_prop_list = proplist_empty( prop_count );
  the_prop_list->length = prop_count;

  counter = 0;
  for( i=0; i<vertex_count; i++ )
    for( j=0; j<color_count; j++ ) {
      the_prop_list->props[counter] =
        (proposition)safe_malloc( max_prop_length );
      (void)sprintf( the_prop_list->props[counter],
                     "p_%ld_%ld", i, j );
      counter++;
    }

  /* 4.  Initialize the_formula. */
  the_formula = formula_empty( 2 * vertex_count );   /* An estimate */
  the_formula->length = vertex_count;   /* The # of clauses in 5.a. */

  /* 5.  Construct the clauses and add them to the_formula. */

  /* 5.a.  Construct the clauses stipulating that each vertex
     must have at least one color. */
  counter = 0;
  for( i=0; i<vertex_count; i++ ) {
    the_formula->clauses[i].length = color_count;
    current_lit =
      the_formula->clauses[i].members =
        (literal_object *)
          safe_malloc( sizeof(literal_object) * (size_t)color_count );
    for( j=0; j<color_count; j++, current_lit++ ) {
      current_lit->sign = Pos;
      current_lit->p_index = counter;
      counter++;
    }
  }

  /* 5.b.  Construct the clauses stipulating that each vertex
     must have at most one color. */
  current_clause_object.length = 2;
  for( i=0; i<vertex_count; i++ )
    for( j=0; j<color_count; j++ )
      for( k=j+1; k<color_count; k++ ) {
        current_lit =
          current_clause_object.members =
            (literal_object *)
              safe_malloc( sizeof(literal_object) * 2 );
        current_lit->sign = Neg;
        current_lit->p_index = color_count * i + j;
        current_lit++;
        current_lit->sign = Neg;
        current_lit->p_index = color_count * i + k;
        formula_append_clause( the_formula, &current_clause_object );
      }
     
  /* 5.c.  Construct the clauses associated with the edges between
     the vertices. */
  for( i=0; i<vertex_count; i++ )
    for( j=i+1; j<vertex_count; j++ )
      if( good_random() < edge_prob )
        for( k=0; k<color_count; k++ ) {
          current_lit =
            current_clause_object.members =
              (literal_object *)
                safe_malloc( sizeof(literal_object) * 2 );
          current_lit->sign = Neg;
          current_lit->p_index = color_count * i + k;
          current_lit++;
          current_lit->sign = Neg;
          current_lit->p_index = color_count * j + k;
          formula_append_clause( the_formula, &current_clause_object );
        }

  /* 6.  Construct the_clause_count. */

  the_clause_count = the_formula->length;

  /* 7.  Resize the_formula->clauses to avoid the wasted space
     due to repeatedly doubling the size of this array. */

  formula_delete_wasted_space( the_formula );
}
