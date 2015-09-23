/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.9 $ */

#include <limits.h>
#include <math.h>
#include <memory.h>
#include <stdio.h>
#include "bt-stack.h"
#include "cnfforms.h"
#include "cmn-carr.h"
#include "cmn-parr.h"
#include "dynamic.h"
#include "gbl-carr.h"
#include "gbl-parr.h"
#include "heur2.h"
#include "heurs.h"
#include "la-stack.h"
#include "safemall.h"
#include "gbl-sv.h"

#ifdef THINK_C
#include <size_t.h>
void *memset(void *s, int c, size_t n);
#endif

/* Contains the occurrences of the literals that have become true. */
static long **satisfied_lits;

/* Points to the literals in clauses that have become open binary. */
static literal *open_binaries;

/* Indicates whether a clause has become open binary. */
static unsigned long *binary_timestamps;
static unsigned long binary_main_timestamp;


void global_sv_make( void )
{
  long i;
  long ccarrelt_length;
  volatile_carray_element vcarrelt;
  volatile_parray_element vparrelt;
  common_carray_element ccarrelt;
  literal current_lit;
  long lindex;

  /* 1.  Initialize the global backtracking stack. */

  prop_array_size = the_prop_count * sizeof(volatile_parrelt_object);
  clause_array_size = the_clause_count * sizeof(volatile_carrelt_object);
  total_array_size = prop_array_size + clause_array_size;
  /* Adjust for alignment considerations. */
  total_array_size +=
    8 * sizeof(double) -
      (total_array_size & (8 * sizeof(double) - 1));
  lit_array_size = 2 * the_prop_count;
  /* Adjust for alignment considerations. */
  lit_array_size += 
    8 * sizeof(double) -
      (lit_array_size & (8 * sizeof(double) - 1));

  btstack_emptystack();

  /* 2.  Initialize the global lookahead stack. */

  lastack_emptystack();

  /* 3.  Initialize global_p_array and global_pcount_array. */

  vparrelt =
    global_p_array =
      (volatile_prop_array)safe_malloc( (size_t)total_array_size );
  for( i=0; i<the_prop_count; i++, vparrelt++ )
    vparrelt->tval = (truth_value)Indeterminate;

  global_pcount_array =
    (volatile_pcount_array)
      safe_malloc( (size_t)the_prop_count *
                   sizeof(volatile_pcountelt_object) );

  /* 4.  Initialize global_c_array. */

  vcarrelt =
    global_c_array =
      (volatile_clause_array)((char *)global_p_array + prop_array_size);
  for( i = 0, ccarrelt = common_c_array;
       i < the_clause_count;
       i++, vcarrelt++, ccarrelt++ ) {
    ccarrelt_length = ccarrelt->length;
    if( ccarrelt_length > SCHAR_MAX )
      fprintf( stderr, "Warning:  Clause too long!\n" );
    vcarrelt->data = (char)ccarrelt_length;
  }

  /* 5.  Initialize the heuristic-specific data structures. */

  gapplyh_literals1 = sarray_empty( the_prop_count );
  gapplyh_literals2 = tiset_emptyset( 2 * the_prop_count );

  backup_p_array =
    (volatile_prop_array)safe_malloc( (size_t)total_array_size );

  /* 6.  Initialize binary_clause_info. */

  binary_clause_info =
    (unsigned char *)safe_malloc( (size_t)lit_array_size );
  (void)memset( (char *)binary_clause_info,
                '\0',
                (size_t)(2 * the_prop_count) );
  for( i = 0, ccarrelt = common_c_array;
       i < the_clause_count;
       i++, ccarrelt++ )
    if( ccarrelt->length == 2 ) {
      /* The l_index fields are uninitialized at this point. */
      current_lit = ccarrelt->cset;
      lindex = litinfo_to_lindex(current_lit->sign, current_lit->p_index);
      if( binary_clause_info[lindex] == UCHAR_MAX )
        fprintf( stderr, "Warning:  Too many literal occurrences!\n" );
      else
        binary_clause_info[lindex]++;
      current_lit++;
      lindex = litinfo_to_lindex(current_lit->sign, current_lit->p_index);
      if( binary_clause_info[lindex] == UCHAR_MAX )
        fprintf( stderr, "Warning:  Too many literal occurrences!\n" );
      else
        binary_clause_info[lindex]++;
    }

  /* 7.  An upper bound on shift_value.  It's decremented dynamically
     as needed inside heuristic2a(). */

  shift_value = 10;

  /* 8.  Initialize satisfied_lits. */

  satisfied_lits =
    (long **)safe_malloc( (size_t)the_prop_count * sizeof(long *) );

  /* 9.  Initialize open_binaries. */

  open_binaries =
    (literal *)safe_malloc( (size_t)the_clause_count * sizeof(literal) );

  /* 10.  Initialize binary_timestamps and binary_main_timestamp. */

  binary_timestamps =
    (unsigned long *)
      safe_malloc( (size_t)the_clause_count * sizeof(unsigned long) );
  (void)memset( (char *)binary_timestamps,
                '\0',
                (size_t)the_clause_count * sizeof(unsigned long) );
  binary_main_timestamp = 0;
}

void global_sv_free( void )
{
  btstack_free();
  lastack_free();
  global_parray_free();
  global_carray_free();

  sarray_free( gapplyh_literals1 );
  tiset_free( gapplyh_literals2 );

  safe_free( backup_p_array );
  safe_free( binary_clause_info );
  safe_free( satisfied_lits );
  safe_free( open_binaries );
  safe_free( binary_timestamps );
}

int extend_prop_la( long pindex, int tv )
{
  /* Local variables for the initial extension. */

  register long *cindex_ptr;
  register long cindex;
  register literal current_lit;
  register volatile_carray_element vcarrelt;
  register int vcarrelt_data;

  /* Local variables for propagating constraints. */

  register long *local_tos_ptr;
  register long **satisfied_lit_ptr;
  register literal *open_binary_ptr;
  register unsigned long local_binary_timestamp;
  register long local_valued_props;
  register truth_value original_tval;

  /* Local copies of all the global variables.
     Yes, it's really worth it. */

  common_literal_members l_common_l_members = common_l_members;
  volatile_prop_array l_global_p_array = global_p_array;
  common_clause_array l_common_c_array = common_c_array;
  volatile_clause_array l_global_c_array = global_c_array;
  unsigned char *l_binary_clause_info = binary_clause_info;
  long **l_satisfied_lits = satisfied_lits;
  literal *l_open_binaries = open_binaries;
  unsigned long *l_binary_timestamps = binary_timestamps;
  lookahead_stack l_global_la_stack = global_la_stack;

#ifdef DEBUG
  if( tv == Indeterminate ) {
    fprintf( stderr,
             "extend_prop_la: Warning: Truth value is indeterminate.\n" );
    return 0;
  }
  if( l_global_p_array[pindex].tval != Indeterminate ) {
    fprintf( stderr,
             "extend_prop_la: Warning: Truth value already exists.\n" );
    return 0;
  }
#endif /* DEBUG */

  satisfied_lit_ptr = l_satisfied_lits;
  binary_main_timestamp++;
  local_binary_timestamp = binary_main_timestamp;
  local_valued_props = dynamic_valued_props;

  local_tos_ptr = l_global_la_stack;
  local_valued_props++;
  /* This must be done first! */  
  l_global_p_array[pindex].tval = (truth_value)tv;

  /* These statements assume that True == Pos and False == Neg. */
  cindex_ptr = l_common_l_members[litinfo_to_lindex2(tv,pindex)];
  *satisfied_lit_ptr = l_common_l_members[litinfo_to_lindex(tv,pindex)];

  satisfied_lit_ptr++;

  /* 1.  Falsify the false literals. */

  open_binary_ptr = l_open_binaries;

  while( (cindex = *cindex_ptr) != -99 ) {
    vcarrelt = l_global_c_array + cindex;
    /* This instruction forces gcc to use ldsb instead of ldub. */
    vcarrelt_data = (int)vcarrelt->data;
    vcarrelt_data--;
    if( vcarrelt_data < 0 )
      ;
    else if( vcarrelt_data == 2 ) {      /* Open ternary to open binary. */
      /* Note that for formulas with a large proportion of
         binary clauses, this case will not occur very often. */
      l_binary_timestamps[cindex] = local_binary_timestamp;
      *open_binary_ptr = l_common_c_array[cindex].cset;
      open_binary_ptr++;
    }
    else if( vcarrelt_data == 1 ) {      /* Open binary to open unary. */
      *local_tos_ptr = cindex;
      local_tos_ptr++;
    }
    else if( vcarrelt_data == 0 ) {      /* Open unary to False. */
      /* Highly unlikely at this point. */
      return 1;
    }
    vcarrelt->data = (signed char)vcarrelt_data;
    cindex_ptr++;
  }

  /* 2.  Next, propagate constraints.  All the local variables can be
     reused below this point. */

  while( local_tos_ptr != l_global_la_stack ) {
    local_tos_ptr--;
    current_lit = l_common_c_array[*local_tos_ptr].cset;

    /* Invariant:  Either this clause is really open unary,
       or it contains exactly one true literal and n - 1 false
       literals. */

    while( (pindex = current_lit->p_index) != -99 ) {
      original_tval = l_global_p_array[pindex].tval;

      /* This test assumes that True == Pos and False == Neg. */
      if( original_tval == current_lit->sign ) {
        /* This clause is actually True.  It has no open literals,
           so we'll never examine it again in this loop.  We do
           not want to set the data field to -1 here, because
           the formula might end up false. */
        goto examine_next_clause;
      }
      if( original_tval == Indeterminate ) {    /* Less likely. */
        local_valued_props++;

        /* This must be done first! */
        /* These statements assume that True == Pos and False == Neg. */
        l_global_p_array[pindex].tval = (truth_value)current_lit->sign;
        cindex_ptr = l_common_l_members[current_lit->l_index2];
        *satisfied_lit_ptr = l_common_l_members[current_lit->l_index];

        satisfied_lit_ptr++;

        /* Falsify the false literals associated with pindex. */

        while( (cindex = *cindex_ptr) != -99 ) {
          vcarrelt = l_global_c_array + cindex;
          /* This instruction forces gcc to use ldsb instead of ldub. */
          vcarrelt_data = (int)vcarrelt->data;
          vcarrelt_data--;
          if( vcarrelt_data == 0 ) {      /* Open unary to False. */
            /* Fairly likely at this point. */
            return 1;
          }
          if( vcarrelt_data < 0 )
            ;
          else if( vcarrelt_data == 2 ) {   /* Open ternary to open binary. */
            /* Note that for formulas with a large proportion of
               binary clauses, this case will not occur very often. */
            l_binary_timestamps[cindex] = local_binary_timestamp;
            *open_binary_ptr = l_common_c_array[cindex].cset;
            open_binary_ptr++;
          }
          else if( vcarrelt_data == 1 ) {      /* Open binary to open unary. */
            *local_tos_ptr = cindex;
            local_tos_ptr++;
          }
          vcarrelt->data = (signed char)vcarrelt_data;
          cindex_ptr++;
        }
        goto examine_next_clause;
      }

      /* Otherwise, this literal is false; keep looking. */
      current_lit++;
    }

  examine_next_clause:
    ;
  }

  /* The stack is empty when we get to this point. */

  /* 3.  Satisfy the true literals associated with the literals
     in satisfied_lits. */

  *satisfied_lit_ptr = NULL;     /* A sentinel. */
  satisfied_lit_ptr = l_satisfied_lits;

  while( (cindex_ptr = *satisfied_lit_ptr) != NULL ) {

    while( (cindex = *cindex_ptr) != -99 ) {
      vcarrelt = l_global_c_array + cindex;
      vcarrelt_data = (int)vcarrelt->data;
      if( vcarrelt_data > 0 ) {
        if( vcarrelt_data == 2 &&
            l_binary_timestamps[cindex] != local_binary_timestamp ) {

          /* This clause was open binary when we called this
             function, i.e., it did not become open binary
             because of this function.  It now contains either
             one True literal and one open literal or two True
             literals and no open literals. */

          current_lit = l_common_c_array[cindex].cset;
          while( (pindex = current_lit->p_index) != -99 ) {
            if( l_global_p_array[pindex].tval == Indeterminate ) {
              l_binary_clause_info[current_lit->l_index]--;
              break;
            }
            current_lit++;
          }
        }
        /* We can set data to any value less than 0. */
        vcarrelt->data = (signed char)-1;
      }
      cindex_ptr++;
    }

    satisfied_lit_ptr++;
  }

  /* All the information in global_c_array is correct when we
     get to this point. */

  /* 4.  Update binary_clause_info[] for the clauses that became
     open binary and are still open binary. */

  *open_binary_ptr = NULL;     /* A sentinel. */
  open_binary_ptr = l_open_binaries;
  while( (current_lit = *open_binary_ptr) != NULL ) {

    if( l_global_c_array[current_lit->c_index].data == 2 ) {
      while( 1 ) {
        if( l_global_p_array[current_lit->p_index].tval == Indeterminate )
          break;
        current_lit++;
      }
#ifdef DEBUG
      if( l_binary_clause_info[current_lit->l_index] == UCHAR_MAX )
        fprintf( stderr, "Warning:  Too many literal occurrences!\n" );
#endif /* DEBUG */
      l_binary_clause_info[current_lit->l_index]++;
      current_lit++;
      while( 1 ) {
        if( l_global_p_array[current_lit->p_index].tval == Indeterminate )
          break;
        current_lit++;
      }
#ifdef DEBUG
      if( l_binary_clause_info[current_lit->l_index] == UCHAR_MAX )
        fprintf( stderr, "Warning:  Too many literal occurrences!\n" );
#endif /* DEBUG */
      l_binary_clause_info[current_lit->l_index]++;
    }

    /* Otherwise, this clause is True, and there's nothing to update. */

    open_binary_ptr++;
  }

  dynamic_valued_props = local_valued_props;
  return 0;
}

/* Don't increment dynamic_valued_props. */

/* Do not increment the appropriate information in binary_clause_info.
   This is important, since we do not save binary_clause_info in the
   call to heuristic2a(). */

long extend_prop_la_for_failure( long pindex, int tv )
{
  /* Local variables for the initial extension. */

  register long cindex;
  register long *cindex_ptr;
  register volatile_carray_element vcarrelt;
  register int vcarrelt_data;

  /* Local variables for the subsequent constraint propagation. */

  register long *local_tos_ptr;
  register literal chosen_lit;
  register long extend_count;
  register truth_value original_tval;

  /* Local copies of global variables.  Yes, it's really worth it. */

  register common_literal_members l_common_l_members = common_l_members;
  register volatile_prop_array l_global_p_array = global_p_array;
  register common_clause_array l_common_c_array = common_c_array;
  register volatile_clause_array l_global_c_array = global_c_array;
  register lookahead_stack l_global_la_stack = global_la_stack;

  /* 1.  Perform the initial extension. */

#ifdef DEBUG
  if( tv == Indeterminate ) {
    fprintf
      ( stderr,
        "extend_prop_la_ff: Warning: Truth value is indeterminate.\n" );
    return 0;
  }
  if( l_global_p_array[pindex].tval != Indeterminate ) {
    fprintf
      ( stderr,
        "extend_prop_la_ff: Warning: Truth value already exists.\n" );
    return 0;
  }
#endif /* DEBUG */

  local_tos_ptr = l_global_la_stack;
  l_global_p_array[pindex].tval = (truth_value)tv;

  /* This statement assumes that True == Pos and False == Neg. */
  cindex_ptr = l_common_l_members[litinfo_to_lindex2(tv,pindex)];

  extend_count = 0;
  while( (cindex = *cindex_ptr) != -99 ) {
    vcarrelt = l_global_c_array + cindex;
    /* This instruction forces gcc to use ldsb instead of ldub. */
    vcarrelt_data = (int)vcarrelt->data;

    if( vcarrelt_data < 0 )
      ;
    else if( vcarrelt_data == 3 ) {
      /* Open ternary to open binary. */
      extend_count++;
      vcarrelt->data = (signed char)2;
    }
    else if( vcarrelt_data == 2 ) {
      /* Open binary to open unary. */
      *local_tos_ptr = cindex;
      local_tos_ptr++;
      vcarrelt->data = (signed char)1;
    }
    else if( vcarrelt_data == 1 ) {
      /* Open unary to false. */
      return -1;    /* Any negative quantity will do. */
    }
    else {
      vcarrelt->data = (signed char)(vcarrelt_data - 1);
    }
    cindex_ptr++;
  }

  /* 2.  Propagate constraints. */

  while( local_tos_ptr != l_global_la_stack ) {
    local_tos_ptr--;
    chosen_lit = l_common_c_array[*local_tos_ptr].cset;

    /* Find chosen_lit and satisfy it if it exists. */

    /* We can use cindex and cindex_ptr for a different purpose
       in the following loop. */

    while( (pindex = chosen_lit->p_index) != -99 ) {
      original_tval = l_global_p_array[pindex].tval;

      /* This test assumes that True == Pos and False == Neg. */
      if( original_tval == chosen_lit->sign ) {
        /* This clause is True.  It contains no open literals, so
           it will not be examined again in this function. */
        goto examine_next_clause;
      }
      if( original_tval == Indeterminate ) {    /* Less likely. */
        extend_count += 2;

        /* Do not increment dynamic_valued_props. */

        /* These statements assume that True == Pos and False == Neg. */
        l_global_p_array[pindex].tval = (truth_value)chosen_lit->sign;
        cindex_ptr = l_common_l_members[chosen_lit->l_index2];

        /* Modify the appropriate information in global_c_array. */
        while( (cindex = *cindex_ptr) != -99 ) {
          vcarrelt = l_global_c_array + cindex;
          /* This instruction forces gcc to use ldsb instead of ldub. */
          vcarrelt_data = (int)vcarrelt->data;

          if( vcarrelt_data < 0 )
            ;
          else if( vcarrelt_data == 3 ) {
            /* Open ternary to open binary. */
            extend_count++;
            vcarrelt->data = (signed char)2;
          }
          else if( vcarrelt_data == 2 ) {
            /* Open binary to open unary. */
            *local_tos_ptr = cindex;
            local_tos_ptr++;
            vcarrelt->data = (signed char)1;
          }
          else if( vcarrelt_data == 1 ) {
            /* Open unary to false. */
            return -1;    /* Any negative quantity will do. */
          }
          else {
            vcarrelt->data = (signed char)(vcarrelt_data - 1);
          }
          cindex_ptr++;
        }
        goto examine_next_clause;
      }

      /* Otherwise, this literal is false; keep looking. */
      chosen_lit++;
    }

  examine_next_clause:
    ;
  }

  /* The stack is empty when we get to this point. */
  return extend_count;
}

truth_value global_truth_formula( void )
{
  volatile_carray_element vcarrelt;
  long i;
  int open_clause_exists;

  open_clause_exists = 0;
  for( i = 0, vcarrelt = global_c_array;
       i < the_clause_count;
       i++, vcarrelt++ ) {
    if( vcarrelt->data == 0 )    /* False clause. */
      return (truth_value)False;
    if( vcarrelt->data > 0 )     /* Open clause. */
      open_clause_exists = 1;
  }
  if( open_clause_exists )
    return (truth_value)Indeterminate;
  return (truth_value)True;
}
