/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.4 $ */

#include <limits.h>
#include <memory.h>
#include <stdio.h>
#include "bt-stack.h"
#include "cnfforms.h"
#include "cmn-carr.h"
#include "cmn-parr.h"
#include "defines.h"
#include "gbl-carr.h"
#include "gbl-sv.h"
#include "heurs.h"
#include "misc.h"
#include "safemall.h"
#include "heur2.h"

#ifdef THINK_C
#include <size_t.h>
void *memcpy(void *s1, const void *s2, size_t n);
#endif

volatile_prop_array backup_p_array;


long heuristic2a( long lindex )
{
  register long pos_cost = 0;
  register long neg_cost = 0;
  int pos_first = lindex_is_positive( lindex );
  long pindex = lindex_to_pindex( lindex );
  long total_cost;

  if( binary_clause_info[lindex_complement(lindex)] == 0 )
    /* lindex' does not occur in any open binary clauses,
       so lindex has 0 descendants. */
    goto compute_next_cost;

  /* Save global_p_array (and global_c_array) to a scratch array. */
  save_state( (char *)backup_p_array,
              (char *)global_p_array,
              (size_t)total_array_size );

  /* Don't bother finding an actual occurrence of this literal. */
  pos_cost = extend_prop_la_for_failure( pindex,
                                         pos_first ? True : False );

  /* Undo the changes we made by restoring the old global_p_array
     and global_c_array. */
  temp_p_array = global_p_array;
  global_p_array = backup_p_array;
  backup_p_array = temp_p_array;

  global_c_array =
    (volatile_clause_array)((char *)global_p_array + prop_array_size);

  if( pos_cost < 0 ) {
    /* lindex is a failed literal.  We have to add one because the
       proposition indices are 0-based. */
#ifdef FAILED_LITS
    return -lindex - 1;
#else
    /* We certainly want to branch on this literal immediately. */
    return LONG_MAX;
#endif /* FAILED_LITS */
  }

 compute_next_cost:

  if( binary_clause_info[lindex] == 0 )
    /* lindex does not occur in any open binary clauses,
       so lindex' has 0 descendants. */
    goto compute_total_cost;

  /* Save global_p_array (and global_c_array) to a scratch array. */
  save_state( (char *)backup_p_array,
              (char *)global_p_array,
              (size_t)total_array_size );

  /* Don't bother finding an actual occurrence of this literal. */
  neg_cost = extend_prop_la_for_failure( pindex,
                                         pos_first ? False : True );

  /* Undo the changes we made by restoring the old global_p_array
     and global_c_array. */
  temp_p_array = global_p_array;
  global_p_array = backup_p_array;
  backup_p_array = temp_p_array;

  global_c_array =
    (volatile_clause_array)((char *)global_p_array + prop_array_size);

  if( neg_cost < 0 ) {
    /* lindex' is a failed literal.  We have to add one because the
       proposition indices are 0-based. */
#ifdef FAILED_LITS
    return -(lindex_complement(lindex)) - 1;
#else
    /* We certainly want to branch on this literal immediately. */
    return LONG_MAX;
#endif /* FAILED_LITS */
  }

 compute_total_cost:

  /* Reduce the number of calls to .umul. */
  if( pos_cost == 0 ) {
    total_cost = neg_cost;
  }
  else if( neg_cost == 0 ) {
    total_cost = pos_cost;
  }
  else {
    total_cost = ((pos_cost * neg_cost) << shift_value)
                 + pos_cost + neg_cost;
  }

  /* shift_value should be as large as possible, but no larger. */
  if( total_cost < 0 ) {
    /* An overflow has occurred.  No problem. */
    if( shift_value > 0 ) {
      shift_value--;
      goto compute_total_cost;
    }
    /* Otherwise, shift_value is already 0; return the largest
       possible positive cost. */
    total_cost = LONG_MAX;
  }

  /* The quantity that we return here must not be negative. */
  return total_cost;
}
