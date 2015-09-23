/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.3 $ */

/* The top-level algorithm. */

#include <stdio.h>
#include "bt-stack.h"
#include "cnfforms.h"
#include "defines.h"
#include "dynstats.h"
#include "cmn-carr.h"
#include "gbl-carr.h"
#include "gbl-parr.h"
#include "gbl-sv.h"
#include "good-rnd.h"
#include "heur1.h"
#include "heur2.h"
#include "heurs.h"
#include "safemall.h"
#include "dynamic.h"

#ifdef GRAND_STATS
extern double *grand_avgs;
extern unsigned long *grand_counts;
#endif /* GRAND_STATS */

literal dynamic_current_literal;
long dynamic_current_lindex;
long dynamic_current_pindex;
long dynamic_valued_props;


#ifndef USE_HEURISTICS

static literal choose_random_literal( void )
{
  long i, starting_pindex;
  literal pos_lit, neg_lit;

  pos_lit = NULL;    /* To avoid the stupid compiler warning. */
  neg_lit = NULL;    /* Ditto. */

  i = starting_pindex = random_long( the_prop_count );
  while( i < the_prop_count ) {
    if( global_truth_prop(i) == Indeterminate ) {
      pos_lit = lindex_to_literal( 2 * i );
      neg_lit = lindex_to_literal( 2 * i + 1 );
      if( pos_lit || neg_lit )
        break;
    }
    i++;
  }
  if( i == the_prop_count ) {
    i = starting_pindex - 1;
    while( i > -1 ) {
      if( global_truth_prop(i) == Indeterminate ) {
        pos_lit = lindex_to_literal( 2 * i );
        neg_lit = lindex_to_literal( 2 * i + 1 );
        if( pos_lit || neg_lit )
          break;
      }
      i--;
    }
  }
  if( i == -1 )
    /* The formula has a truth value. */
    return NULL;
  if( pos_lit && neg_lit )
    return( random_long(2) ? pos_lit : neg_lit );
  return( pos_lit ? pos_lit : neg_lit );
}

#endif /* !USE_HEURISTICS */

void satisfy_dynamic( void )
{

  /* Initialization code. */
  dynamic_valued_props = 0;

 forwards:

#ifdef PROGRESS_REPORT
  if( btstack_isempty() && the_dynamic_stats->nodes )
    fprintf( stderr, "Half! " );
#endif /* PROGRESS_REPORT */

#ifdef USE_HEURISTICS

  dynamic_current_lindex = apply_heuristic();
  switch( dynamic_current_lindex ) {
  case AHFalseFormula:
    goto backwards;
  case AHTrueFormula:
    /* The formula is true, and we are done. */
    the_dynamic_stats->solution_count = 1;
    return;
  default:
#ifdef DEBUG
    if( dynamic_current_lindex < 0 )
      fatal_error( "satisfy_dynamic:  dynamic_current_lindex < 0" );
#endif /* DEBUG */
    break;
  }
  dynamic_current_pindex = lindex_to_pindex( dynamic_current_lindex );

#else /* USE_HEURISTICS */

  dynamic_current_literal = choose_random_literal();
  if( dynamic_current_literal == NULL ) {
    /* The formula is True. */
    the_dynamic_stats->solution_count = 1;
    return;
  }
  dynamic_current_lindex = dynamic_current_literal->l_index;
  dynamic_current_pindex = dynamic_current_literal->p_index;

#endif /* USE_HEURISTICS */

  the_dynamic_stats->nodes++;
  btstack_push();

#ifdef GRAND_STATS
  /* Formula:  X_{n+1} = X_n + (x_{n+1} - X_n) / n+1. */
  grand_counts[top_of_bt_stack]++;
  grand_avgs[top_of_bt_stack] +=
    ((the_prop_count - dynamic_valued_props) - grand_avgs[top_of_bt_stack]) /
      grand_counts[top_of_bt_stack];
#endif /* GRAND_STATS */

  if( extend_prop_la(dynamic_current_pindex,
                     lindex_is_positive(dynamic_current_lindex) ?
                     True :
                     False) )
    goto backwards;
  goto forwards;

 backwards:

  if( btstack_isempty() )
    return;
  btstack_restore();    /* Restores dynamic_current_lindex. */
  btstack_pop();
  dynamic_current_pindex = lindex_to_pindex( dynamic_current_lindex );
  if( extend_prop_la(dynamic_current_pindex,
                     lindex_is_positive(dynamic_current_lindex) ?
                     False :
                     True) )
    goto backwards;
  goto forwards;

}
