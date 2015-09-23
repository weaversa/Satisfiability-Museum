/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.3 $ */

#include <stdio.h>
#include "cnfforms.h"
#include "cmn-carr.h"
#include "cmn-parr.h"
#include "defines.h"
#include "gbl-parr.h"
#include "main.h"
#include "dynstats.h"

#ifdef SIMPLIFY_FIRST
#define is_eliminated(PI) (common_p_array[(PI)].occurinfo[Pos].length == 0 \
                           && common_p_array[(PI)].occurinfo[Neg].length == 0)
#endif /* SIMPLIFY_FIRST */

dynamic_stats the_dynamic_stats;


static void dimacs_truthassign_print( dynamic_stats dstats )
{
  long i;

  /* 1.  Print a comment line. */

  printf( "c POSIT generated this solution file.\nc\n" );

  /* 2.  Print the solution line. */

  printf( "s cnf %ld %ld %ld\n",
          dstats->solution_count,
          the_prop_count,
          the_clause_count );

  /* 3.  Print the statistics line. */

  printf( "t cnf %ld %ld %ld %.3f %.3f\n",
          dstats->solution_count,
          the_prop_count,
          the_clause_count,
          dstats->cpu_time,
          (double)dstats->nodes );

  /* 4.  Print the variable lines if there is a solution. */

  if( dstats->solution_count == 0 )
    return;

  for( i=0; i<the_prop_count; i++ )
    switch( global_truth_prop(i) ) {
    case True:
      printf( "v %ld\n", i+1 );     /* 1-indexed. */
      break;
    case False:
      printf( "v -%ld\n", i+1 );    /* 1-indexed. */
      break;
    case Indeterminate:
      break;
    }
}

static void posit_truthassign_print( dynamic_stats dstats )
{
  long i;
  long true_prop_count, false_prop_count, ind_prop_count;
  long eliminated;

  if( dstats->solution_count == 0 ) {
    printf( "There is no satisfying truth assignment.\n" );
    printf( "Number of nodes:  %ld\n", dstats->nodes );
    printf( "CPU time:  %.3f seconds.\n", dstats->cpu_time );
    return;
  }

  printf( "There is a satisfying truth assignment.\n" );

  true_prop_count = false_prop_count = ind_prop_count = 0;
  eliminated = 0;
  for( i=0; i<the_prop_count; i++ )
#ifdef SIMPLIFY_FIRST
    if( is_eliminated(i) )
      eliminated++;
    else
#endif /* SIMPLIFY_FIRST */
      switch( global_truth_prop(i) ) {
      case True:
        true_prop_count++;
        break;
      case False:
        false_prop_count++;
        break;
      case Indeterminate:
        ind_prop_count++;
        break;
      }

  if( true_prop_count == 1 )
    printf( "There is 1 true variable:\n[" );
  else
    printf( "There are %ld true variables:\n[", true_prop_count );
  for( i=0; i<the_prop_count; i++ ) {
    if( global_truth_prop(i) == True
#ifdef SIMPLIFY_FIRST
        /* The pure literal rule always marks eliminated variables
           as True. */
        && !is_eliminated(i)
#endif /* SIMPLIFY_FIRST */
       ) {
      printf( "%s", common_p_array[i].prop );
      true_prop_count--;
      if( true_prop_count )
        printf( ", " );
    }
  }
  printf( "]\n" );

  if( false_prop_count == 1 )
    printf( "There is 1 false variable:\n[" );
  else
    printf( "There are %ld false variables:\n[", false_prop_count );
  for( i=0; i<the_prop_count; i++ ) {
    if( global_truth_prop(i) == False ) {
      printf( "%s", common_p_array[i].prop );
      false_prop_count--;
      if( false_prop_count )
        printf( ", " );
    }
  }
  printf( "]\n" );

  if( ind_prop_count == 1 )
    printf( "There is 1 open variable:\n[" );
  else
    printf( "There are %ld open variables:\n[",
            ind_prop_count );
  for( i=0; i<the_prop_count; i++ )
    if( global_truth_prop(i) == Indeterminate ) {
      printf( "%s", common_p_array[i].prop );
      ind_prop_count--;
      if( ind_prop_count )
        printf( ", " );
    }
  printf( "]\n" );

#ifdef SIMPLIFY_FIRST
  if( eliminated ) {
    printf( "%ld variables were eliminated before the search began:\n[",
            eliminated );
    for( i=0; i<the_prop_count; i++ )
      if( is_eliminated(i) ) {
        printf( "%s", common_p_array[i].prop );
        eliminated--;
        if( eliminated )
          printf( ", " );
      }
    printf( "]\n" );
  }
#endif /* SIMPLIFY_FIRST */

  printf( "Number of nodes:  %ld\n", dstats->nodes );
  printf( "CPU time:  %.3f seconds.\n", dstats->cpu_time );
}

static void global_verify_solution( void )
{
  common_carray_element ccarrelt;
  long i, j, ccarrelt_length;
  literal current_lit;
  truth_value current_tval;

  for( i = 0, ccarrelt = common_c_array;
       i < the_clause_count;
       i++, ccarrelt++ ) {
    ccarrelt_length = ccarrelt->length;
    for( j = 0, current_lit = ccarrelt->cset;
         j < ccarrelt_length;
         j++, current_lit++ ) {
      current_tval = global_truth_prop( current_lit->p_index );
      if( (current_lit->sign == Pos && current_tval == True) ||
          (current_lit->sign == Neg && current_tval == False) )
        break;
    }
    if( j == ccarrelt_length )
      fprintf( stderr,
               "Bug alert:  This model does not satisfy clause %ld!\n",
               i + 1 );
  }
}

void global_status_report( dynamic_stats dstats )
{
  if( machine_readable )
    dimacs_truthassign_print( dstats );
  else
    posit_truthassign_print( dstats );

  if( dstats->solution_count )
    global_verify_solution();
}
