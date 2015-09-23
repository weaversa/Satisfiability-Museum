/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.5 $ */

#include <stdio.h>
#include "cnfforms.h"
#include "cmn-carr.h"
#include "cmn-flgs.h"
#include "cmn-parr.h"
#include "cmn-sv.h"
#include "defines.h"
#include "dmcs-cnf.h"
#include "gbl-carr.h"
#include "gbl-parr.h"
#include "gbl-sv.h"
#include "la-stack.h"
#include "main.h"
#include "safemall.h"
#include "statevec.h"

/* Construct all of the parts of the state vector that are not
   strictly necessary, but make the code faster.  This function
   must be called after global_sv_make() and common_sv_make(). */

static void construct_redundant_info( void )
{
  long i, j;
  common_carray_element ccarrelt;
  long ccarrelt_length;
  common_parray_element cparrelt;
  c_indices ci;
  long ci_length;
  literal current_lit;
  long current_pindex;
  literal_sign current_sign;

  /* 1.  Construct the redundant information in literals. */

  for( i = 0, ccarrelt = common_c_array;
       i < the_clause_count;
       i++, ccarrelt++ ) {
    ccarrelt_length = ccarrelt->length;
    for( j = 0, current_lit = ccarrelt->cset;
         j < ccarrelt_length;
         j++, current_lit++ ) {
      current_pindex = current_lit->p_index;
      current_sign = current_lit->sign;
      current_lit->l_index =
        litinfo_to_lindex( current_sign, current_pindex );
      current_lit->l_index2 = lindex_complement( current_lit->l_index );
      current_lit->c_index = i;
      current_lit->common_pointer = common_p_array + current_pindex;
    }
  }

  /* 2.  Construct the redundant information in common_p_array. */

  for( i = 0, cparrelt = common_p_array;
       i < the_prop_count;
       i++, cparrelt++ ) {

    /* 2.a.  Construct the redundant information in cparrelt->occurinfo[Pos]
       from cparrelt->occurinfo[Pos].members. */

    ci = &(cparrelt->occurinfo[Pos]);
    ci_length = ci->length;
    /* On some platforms, calling malloc(0) is a bad thing. */
    if( ci_length ) {
      ci->common_pointers =
        (common_carray_element *)
          safe_malloc( (size_t)ci_length * sizeof(common_carray_element) );
      for( j=0; j<ci_length; j++ )
        ci->common_pointers[j] = common_c_array + ci->members[j];
    }
    else
      ci->common_pointers = NULL;

    /* 2.b.  Construct the redundant information in cparrelt->occurinfo[Neg]
       from cparrelt->occurinfo[Neg].members. */

    ci = &(cparrelt->occurinfo[Neg]);
    ci_length = ci->length;
    if( ci_length ) {
      ci->common_pointers =
        (common_carray_element *)
          safe_malloc( (size_t)ci_length * sizeof(common_carray_element) );
      for( j=0; j<ci_length; j++ )
        ci->common_pointers[j] = common_c_array + ci->members[j];
    }
    else
      ci->common_pointers = NULL;
  }

  /* 3.  Construct common_l_members from common_p_array. */

  common_l_members =
    (common_literal_members)
      safe_malloc( 2 * the_prop_count * sizeof(long *) );
  for( i=0; i<the_prop_count; i++ ) {
    common_l_members[2*i] = common_p_array[i].occurinfo[Pos].members;
    common_l_members[2*i + 1] = common_p_array[i].occurinfo[Neg].members;
  }
}

static truth_value preprocess_state_vector( void )
{
  volatile_carray_element vcarrelt;
  common_parray_element cparrelt;
  long i;

  /* 1.  Check for an empty clause. */

  if( empty_clause )
    return (truth_value)False;

  /* 2.  Check for unary clauses and propagate constraints
     if necessary. */

  for( i = 0, vcarrelt = global_c_array;
       i < the_clause_count;
       i++, vcarrelt++ ) {
    if( vcarrelt->data == 1 )
      lastack_push_bcp( i );
  }
  if( lastack_notempty() ) {
    if( extend_lit_la(common_c_array[lastack_top()].cset, True) )
      return (truth_value)False;
    if( global_truth_formula() == True )
      return (truth_value)True;
  }

  /* 3.  Check for pure literals.  Even more pure literals could
     arise as a result of satisfying the initial ones, but we're
     ignoring this possibility. */

  for( i = 0, cparrelt = common_p_array;
       i < the_prop_count;
       i++, cparrelt++ ) {
    if( cparrelt->occurinfo[Neg].length == 0 )
      (void)extend_prop_la( i, True );
    else if( cparrelt->occurinfo[Pos].length == 0 )
      (void)extend_prop_la( i, False );
  }

  return( global_truth_formula() );
}

truth_value sv_make_and_preprocess( void )
{
  truth_value result = (truth_value)Indeterminate;

  common_sv_make();
  global_sv_make();
  construct_redundant_info();

#ifndef SIMPLIFY_FORMULA
  switch( problem_choice ) {
  case NQueens:
  case BallsInBins:
    /* These are the only classes of problems that need not be
       preprocessed. */
    break;
  default:
    /* External formulas may contain empty or unary clauses, and
       the other internal formulas may contain pure literals. */
    result = preprocess_state_vector();
    break;
  }
#endif /* SIMPLIFY_FORMULA */
  return result;
}

void sv_free( void )
{
  proplist_free( the_prop_list );
  formula_free( the_formula );
  common_sv_free();
  global_sv_free();
  safe_free( common_l_members );
}
