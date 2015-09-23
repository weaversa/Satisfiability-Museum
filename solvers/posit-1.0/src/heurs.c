/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.11 $ */

#include <memory.h>
#include <limits.h>
#include <stdio.h>
#include "bt-stack.h"
#include "cnfforms.h"
#include "cmn-carr.h"
#include "dynstats.h"
#include "dynamic.h"
#include "gbl-carr.h"
#include "gbl-parr.h"
#include "gbl-sv.h"
#include "good-rnd.h"
#include "heur1.h"
#include "heur2.h"
#include "misc.h"
#include "heurs.h"

#ifdef THINK_C
#include <size_t.h>
void *memcpy(void *s1, const void *s2, size_t n);
#endif


small_array gapplyh_literals1;
time_index_set gapplyh_literals2;

long gapplyh_pure_lindex;

long shift_value;

unsigned char *binary_clause_info;

/* The maximum number of times to run heuristic2a() at each node
   and NOT find a failed literal. */
static long unfailed_lit_limit;

static long scratch_long;


literal lindex_to_literal( long lindex )
{
  literal current_literal;
  c_indices ci;

  if( lindex_is_negative(lindex) )
    ci = &(common_p_array[lindex_to_pindex(lindex)].occurinfo[Neg]);
  else
    ci = &(common_p_array[lindex_to_pindex(lindex)].occurinfo[Pos]);
  /* In some randomly generated problems, a literal may not appear
     anywhere in the formula. */
  if( ci->length == 0 )
    return NULL;
  current_literal = (ci->common_pointers[0])->cset;
  while( 1 ) {
    if( current_literal->l_index == lindex )
      break;
    current_literal++;
  }
  return current_literal;
}

static long compute_new_size( void )
{
  /* linear_result = - dynamic_valued_props / 0.05 + the_prop_count. */

  long linear_result =
    the_prop_count -
      ((dynamic_valued_props << 4) +
       (dynamic_valued_props << 2));

  if( linear_result < 10 ||
      /* The cutoff value here is very important, especially for
         hard random K-SAT problems where K > 3. */
      top_of_bt_stack > 5 ) {
    /* 3 is really the best value.  4 creates too much overhead. */
    unfailed_lit_limit = 3;
    return 10;
  }
  unfailed_lit_limit = linear_result;
  return linear_result;
}

/* Simply check whether assigning tv to pindex and running BCP
   falsifies the formula. */

static int check_for_failed_lit( long pindex, int tv )
{
  int status;

  /* Save global_p_array (and global_c_array) to a scratch array. */
  save_state( (char *)backup_p_array,
              (char *)global_p_array,
              (size_t)total_array_size );

  /* Don't bother finding an actual occurrence of this literal. */
  status = extend_prop_la_for_failure( pindex, tv );

  /* Undo the changes we made by restoring the old global_p_array
     and global_c_array. */
  temp_p_array = global_p_array;
  global_p_array = backup_p_array;
  backup_p_array = temp_p_array;

  global_c_array =
    (volatile_clause_array)((char *)global_p_array + prop_array_size);

  return status;
}

/* Assumption:  There are no false clauses in the formula. */

long apply_heuristic( void )
{
  register long unfailed_lit_count;
  register long candidate_count;
  register long *candidates;
  register long pos_cost;
  register long neg_cost;
  register long lindex;
  register long pindex;
  register long current_cost;
  register long aux_long_1;
  register long aux_long_2;
  register long sa_cost;
  long max_occurrences;

  long main_counter;
  long i;
  long i_limit;
  long i_delta;
  long i_reset;
  volatile_prop_array gbl_parray_ptr;
  long failed_lit_check_counter;
  long failed_lit_cutoff;

  /* Local copies of global variables. */

  register small_array sa = gapplyh_literals1;
  register time_index_set tiset = gapplyh_literals2;
  register long local_shift_value = shift_value;

#ifdef DEBUG
  /* It's OK if the formula is true at this point, but it's not OK
     if the formula is false. */
  if( global_truth_formula() == False ) {
    fprintf( stderr, "apply_heuristic:  The formula is false!\n" );
    return AHFalseFormula;
  }
#endif /* DEBUG */

  /* A.  Initialize. */

 the_beginning:

  sarray_delete_all( sa );
  sarray_resize( sa, compute_new_size() );
  sa->max_cost = -99;
  gapplyh_pure_lindex = -99;

  /* tiset is cleared below. */
  unfailed_lit_count = 0;
  max_occurrences = 0;    /* By far the best value! */
  failed_lit_check_counter = 0;
  failed_lit_cutoff = unfailed_lit_limit;
  if( failed_lit_cutoff > 10 )
    failed_lit_cutoff = 10;
  else if( failed_lit_cutoff == 3 )    /* The usual case. */
    failed_lit_cutoff = 2;


  /* Check for failed literals first. */
#ifdef FAILED_LITS
#ifdef RANDOMIZE
  i = fast_random_long( the_prop_count );
#else
  i = (the_prop_count >> 3) * (the_dynamic_stats->nodes & 7);
#endif
  if( the_dynamic_stats->nodes & 1 ) {
    i_limit = the_prop_count;
    i_delta = 1;
    i_reset = 0;
  }
  else {
    i_limit = -1;
    i_delta = -1;
    i_reset = the_prop_count - 1;
  }
  /* Do not use gbl_parray_ptr in this loop, because check_for_failed_lit
     changes global_p_array. */
  for( main_counter = the_prop_count;
       main_counter > 0;
       main_counter--,
       i += i_delta ) {
    if( i == i_limit ) {
      i = i_reset;
    }

    if( global_p_array[i].tval == Indeterminate ) {
      pos_cost = binary_clause_info[2 * i];
      neg_cost = binary_clause_info[2 * i + 1];

      current_cost = pos_cost + neg_cost;
      if( current_cost < max_occurrences )
        continue;
      if( current_cost > max_occurrences )    /* Important. */
        max_occurrences = current_cost;

      if( check_for_failed_lit(i,
                               (pos_cost > neg_cost ? False : True)) < 0 ) {
        if( extend_prop_la(i,
                           (pos_cost > neg_cost ? True : False)) ) {
          return AHFalseFormula;
        }
        failed_lit_check_counter = 0;
        /* failed_lit_cutoff doesn't need to be adjusted. */
        continue;
      }
      failed_lit_check_counter++;
      if( failed_lit_check_counter >= failed_lit_cutoff )
        break;
    }
  }
#endif /* FAILED_LITS */


  /* B. Begin by assuming that there is at least one open binary
     clause in the formula. */

  /* Set the starting point randomly. */
#ifdef RANDOMIZE
  i = fast_random_long( the_prop_count );
#else
  i = (the_prop_count >> 3) * (the_dynamic_stats->nodes & 7);
#endif
  if( the_dynamic_stats->nodes & 1 ) {
    i_limit = the_prop_count;
    i_delta = 1;
    i_reset = 0;
  }
  else {
    i_limit = -1;
    i_delta = -1;
    i_reset = the_prop_count - 1;
  }
  for( main_counter = the_prop_count,
       gbl_parray_ptr = global_p_array + i;
       main_counter > 0;
       main_counter--,
       i += i_delta,
       gbl_parray_ptr += i_delta ) {
    if( i == i_limit ) {
      i = i_reset;
      gbl_parray_ptr = global_p_array + i;
    }

    if( gbl_parray_ptr->tval == Indeterminate ) {

      lindex = 2 * i;    /* Assume it's a positive literal. */
      pos_cost = binary_clause_info[lindex];
      neg_cost = binary_clause_info[lindex + 1];
#ifdef DEBUG
      if( pos_cost < 0 ||
          neg_cost < 0 )
        fprintf( stderr,
                 "apply_heuristic:  Negative binary clause occurrences!\n" );
#endif /* DEBUG */
      current_cost = pos_cost + neg_cost;

      if( current_cost == 0 )
        continue;

      if( pos_cost > neg_cost ) {
        /* Branch on Neg i first. */

        /* Calculate lindex. */
        lindex++;

        /* Avoid unnecessary calls to .umul. */
        sa_cost = current_cost;
        if( neg_cost < 4 )
          switch( neg_cost ) {
          case 1:
            sa_cost += (pos_cost << local_shift_value);
            break;
          case 2:
            sa_cost += (pos_cost << (local_shift_value + 1));
            break;
          case 3:
            sa_cost += (((pos_cost << 1) + pos_cost) << local_shift_value);
            break;
          default:
            break;
          }
        else
          sa_cost += ((pos_cost * neg_cost) << local_shift_value);
      }
      else {
        /* Branch on Pos i first. */

        /* Calculate lindex. */
        /* lindex = 2 * i; */

        /* Avoid unnecessary calls to .umul. */
        sa_cost = current_cost;
        if( pos_cost < 4 )
          switch( pos_cost ) {
          case 1:
            sa_cost += (neg_cost << local_shift_value);
            break;
          case 2:
            sa_cost += (neg_cost << (local_shift_value + 1));
            break;
          case 3:
            sa_cost += (((neg_cost << 1) + neg_cost) << local_shift_value);
            break;
          default:
            break;
          }
        else
          sa_cost += ((pos_cost * neg_cost) << local_shift_value);
      }

      /* Insert the pair (lindex, sa_cost) into sa. */
      while( 1 ) {
        if( sa->length < sa->size ) {
          if( sa_cost >= sa->max_cost ) {
            sa->members--;
            sa->costs--;
            sa->members[0] = lindex;
            sa->costs[0] = sa_cost;
            sa->length++;
            /* sa->max_cost may have increased. */
            if( sa_cost > sa->max_cost ) {
              sa->max_cost = sa_cost;
              if( sa->length == 1 )
                sa->min_cost = sa_cost;
            }
            break;
          }
          if( sa_cost <= sa->min_cost ) {
            sa->members[sa->length] = lindex;
            sa->costs[sa->length] = sa_cost;
            sa->length++;
            /* sa->min_cost may have decreased. */
            if( sa_cost < sa->min_cost )
              sa->min_cost = sa_cost;
            break;
          }
          /* Otherwise, sa_cost < sa->max_cost and
             sa_cost > sa->min_cost. */
          aux_long_1 = 0;
          while( 1 ) {
            if( sa->costs[aux_long_1] <= sa_cost )
              break;
            aux_long_1++;
          }
          sa->length++;
          for( aux_long_2 = sa->length - 1;
               aux_long_2 > aux_long_1;
               aux_long_2-- ) {
            sa->members[aux_long_2] = sa->members[aux_long_2 - 1];
            sa->costs[aux_long_2] = sa->costs[aux_long_2 - 1];
          }
          sa->members[aux_long_1] = lindex;
          sa->costs[aux_long_1] = sa_cost;
          /* Neither sa->min_cost nor sa->max_cost has changed. */
          break;
        }
        /* Otherwise, sa->length == sa->size. */
        if( sa_cost < sa->min_cost )
          /* There's no room for this element. */
          break;
        if( sa_cost == sa->min_cost ) {
          /* Unconditionally replace the last element in the array. */
          sa->members[sa->size - 1] = lindex;
          sa->costs[sa->size - 1] = sa_cost;
          break;
        }
        if( sa_cost >= sa->max_cost ) {
          sa->members--;
          sa->costs--;
          sa->members[0] = lindex;
          sa->costs[0] = sa_cost;
          /* Either sa->min_cost or sa->max_cost may have increased. */
          if( sa_cost > sa->max_cost )
            sa->max_cost = sa_cost;
          if( sa->costs[sa->size - 1] > sa->min_cost )
            sa->min_cost = sa->costs[sa->size - 1];
          break;
        }
        /* Otherwise, sa_cost < sa->max_cost and sa_cost > sa->min_cost. */
        aux_long_1 = 0;
        while( 1 ) {
          if( sa->costs[aux_long_1] <= sa_cost )
            break;
          aux_long_1++;
        }
        for( aux_long_2 = sa->size - 1;
             aux_long_2 > aux_long_1;
             aux_long_2-- ) {
          sa->members[aux_long_2] = sa->members[aux_long_2 - 1];
          sa->costs[aux_long_2] = sa->costs[aux_long_2 - 1];
        }
        sa->members[aux_long_1] = lindex;
        sa->costs[aux_long_1] = sa_cost;
        /* sa->min_cost may have increased. */
        if( sa->costs[sa->size - 1] > sa->min_cost )
          sa->min_cost = sa->costs[sa->size - 1];
        break;
      }
    }
  }

  if( sarray_isempty(sa) ) {
    /* Either the formula is true, or there are no open binary
       clauses. */

    for( i=0; i<the_clause_count; i++ )
      if( global_c_array[i].data > 0 )
        break;

    if( i == the_clause_count ) {
      /* The formula is true. */
      return AHTrueFormula;
    }

    /* Otherwise, there are no open binary clauses. */
    unfailed_lit_count = LONG_MAX;

    for( i=0; i<the_prop_count; i++ )
      if( global_p_array[i].tval == Indeterminate ) {
        current_cost = heuristic1_nonbinary( i, &scratch_long );

        /* This heuristic checks for pure literals. */
        if( gapplyh_pure_lindex != -99 ) {
          (void)extend_prop_la( i,
                                (lindex_is_negative(gapplyh_pure_lindex) ?
                                 False : True) );
          gapplyh_pure_lindex = -99;
          continue;
        }

        if( current_cost == 0 )
          continue;

        pos_cost = scratch_long;
        neg_cost = current_cost - pos_cost;

        if( pos_cost > neg_cost ) {
          /* Branch on Neg i first. */
          lindex = 2 * i + 1;
          sa_cost = current_cost +
            ((pos_cost * neg_cost) << local_shift_value);
        }
        else {
          /* Branch on Pos i first. */
          lindex = 2 * i;
          sa_cost = current_cost +
            ((pos_cost * neg_cost) << local_shift_value);
        }

        /* Insert the pair (lindex, sa_cost) into sa. */
        while( 1 ) {
          if( sa->length < sa->size ) {
            if( sa_cost >= sa->max_cost ) {
              sa->members--;
              sa->costs--;
              sa->members[0] = lindex;
              sa->costs[0] = sa_cost;
              sa->length++;
              /* sa->max_cost may have increased. */
              if( sa_cost > sa->max_cost ) {
                sa->max_cost = sa_cost;
                if( sa->length == 1 )
                  sa->min_cost = sa_cost;
              }
              break;
            }
            if( sa_cost <= sa->min_cost ) {
              sa->members[sa->length] = lindex;
              sa->costs[sa->length] = sa_cost;
              sa->length++;
              /* sa->min_cost may have decreased. */
              if( sa_cost < sa->min_cost )
                sa->min_cost = sa_cost;
              break;
            }
            /* Otherwise, sa_cost < sa->max_cost and
               sa_cost > sa->min_cost. */
            aux_long_1 = 0;
            while( 1 ) {
              if( sa->costs[aux_long_1] <= sa_cost )
                break;
              aux_long_1++;
            }
            sa->length++;
            for( aux_long_2 = sa->length - 1;
                 aux_long_2 > aux_long_1;
                 aux_long_2-- ) {
              sa->members[aux_long_2] = sa->members[aux_long_2 - 1];
              sa->costs[aux_long_2] = sa->costs[aux_long_2 - 1];
            }
            sa->members[aux_long_1] = lindex;
            sa->costs[aux_long_1] = sa_cost;
            /* Neither sa->min_cost nor sa->max_cost has changed. */
            break;
          }
          /* Otherwise, sa->length == sa->size. */
          if( sa_cost < sa->min_cost )
            /* There's no room for this element. */
            break;
          if( sa_cost == sa->min_cost ) {
            /* Unconditionally replace the last element in the array. */
            sa->members[sa->size - 1] = lindex;
            sa->costs[sa->size - 1] = sa_cost;
            break;
          }
          if( sa_cost >= sa->max_cost ) {
            sa->members--;
            sa->costs--;
            sa->members[0] = lindex;
            sa->costs[0] = sa_cost;
            /* Either sa->min_cost or sa->max_cost may have increased. */
            if( sa_cost > sa->max_cost )
              sa->max_cost = sa_cost;
            if( sa->costs[sa->size - 1] > sa->min_cost )
              sa->min_cost = sa->costs[sa->size - 1];
            break;
          }
          /* Otherwise, sa_cost < sa->max_cost and sa_cost > sa->min_cost. */
          aux_long_1 = 0;
          while( 1 ) {
            if( sa->costs[aux_long_1] <= sa_cost )
              break;
            aux_long_1++;
          }
          for( aux_long_2 = sa->size - 1;
               aux_long_2 > aux_long_1;
               aux_long_2-- ) {
            sa->members[aux_long_2] = sa->members[aux_long_2 - 1];
            sa->costs[aux_long_2] = sa->costs[aux_long_2 - 1];
          }
          sa->members[aux_long_1] = lindex;
          sa->costs[aux_long_1] = sa_cost;
          /* sa->min_cost may have increased. */
          if( sa->costs[sa->size - 1] > sa->min_cost )
            sa->min_cost = sa->costs[sa->size - 1];
          break;
        }    /* while( 1 ) */
      }    /* if( i is Indeterminate ) */
  }

  candidate_count = sarray_cardinality( sa );
  candidates = sarray_members( sa );

  /* C.  Run a series of slower heuristics on the remaining candidates. */

  aux_long_1 = LONG_MIN;
  aux_long_2 = LONG_MIN;
  /* We do not need to clear out tiset here. */

  for( i=0; i<candidate_count; i++ ) {
    lindex = candidates[i];
    pindex = lindex_to_pindex( lindex );

    if( global_p_array[pindex].tval != Indeterminate )
      continue;

    if( unfailed_lit_count > unfailed_lit_limit )
      /* We cannot simply break when this happens; otherwise, we
         won't filter out the candidates at all when there are
         no open binary clauses. */
      current_cost = LONG_MIN;
    else {
      current_cost = heuristic2a( lindex );
      if( current_cost < 0 ) {
        /* The index of the failed literal is -current_cost - 1. */
        unfailed_lit_count = 0;         /* A big performance win. */
        if( unfailed_lit_limit < 4 )    /* Bump it up slightly. */
          unfailed_lit_limit = 4;
        if( extend_prop_la(pindex,
                           (lindex_is_negative(-current_cost - 1) ?
                            True : False)) ) {
          return AHFalseFormula;
        }

        /* Skip this candidate. */
        continue;
      }
    }

    if( unfailed_lit_count != LONG_MAX )
      unfailed_lit_count++;

    if( current_cost > aux_long_1 ||
        current_cost == LONG_MAX ) {   /* Needed when FAILED_LITS is off. */
      aux_long_1 = current_cost;
      tiset_delete_all( tiset );
      tiset_unsafe_adjoin( tiset, lindex );
    }
    else if( current_cost == aux_long_1 ) {

      if( unfailed_lit_count == LONG_MAX ) {
        /* We called heuristic1_nonbinary().  If we multiply
           global_poscount() and global_negcount() together, etc.,
           then this heuristic will be identical to the output of
           heuristic1_nonbinary(), which certainly won't accomplish
           anything. */
        current_cost =
          global_poscount(pindex) + global_negcount(pindex);
      }
      else {
        /* Call heuristic1_nonbinary(), but without the overhead
           of the function call, updating global_pcount_array, etc. */

        register long *cindex_ptr;
        register signed char vcarrelt_data;
        register volatile_clause_array l_global_c_array = global_c_array;

        pos_cost = 0;
        cindex_ptr = common_l_members[litinfo_to_lindex(Pos,pindex)];
        while( *cindex_ptr != -99 ) {
          vcarrelt_data = l_global_c_array[*cindex_ptr].data;
          if( vcarrelt_data > 0 )
            pos_cost +=
              (1 << (6 < vcarrelt_data ? 0 : 6 - vcarrelt_data));
          cindex_ptr++;
        }

        if( pos_cost == 0 ) {
          (void)extend_prop_la( pindex, False );
          continue;
        }

        neg_cost = 0;
        cindex_ptr = common_l_members[litinfo_to_lindex(Neg,pindex)];
        while( *cindex_ptr != -99 ) {
          vcarrelt_data = l_global_c_array[*cindex_ptr].data;
          if( vcarrelt_data > 0 )
            neg_cost +=
              (1 << (6 < vcarrelt_data ? 0 : 6 - vcarrelt_data));
          cindex_ptr++;
        }

        if( neg_cost == 0 ) {
          (void)extend_prop_la( pindex, True );
          continue;
        }

        current_cost =
          ((pos_cost * neg_cost) << local_shift_value)
            + pos_cost + neg_cost;
      }

      if( current_cost > aux_long_2 ) {
        aux_long_2 = current_cost;
        tiset_delete_all( tiset );
        tiset_unsafe_adjoin( tiset, lindex );
      }
      else if( current_cost == aux_long_2 ) {
        /* lindex came from sa, which has no duplicates. */
        tiset_unsafe_adjoin( tiset, lindex );
      }
    }
  }

  if( aux_long_1 == LONG_MIN &&
      aux_long_2 == LONG_MIN )
    /* We did not modify tiset at all. */
    goto the_beginning;

  /* D.  If there are still two or more candidates left, simply
     pick the first one. */

  /* Note that some of the literals in tiset may have gained a
     truth value as a result of detecting failed literals in the
     above loop. */

#ifdef RANDOMIZE
  /* Assume that all of the remaining candidates are equally good,
     and pick one at random. */
  while( tiset_notempty(tiset) ) {
    lindex = tiset_fast_choose( tiset );
    if( global_p_array[lindex_to_pindex(lindex)].tval ==
        Indeterminate ) {
      return lindex;
    }
    tiset_delete( tiset, lindex );
  }
#else
  candidates = tiset_members( tiset );
  candidate_count = tiset_cardinality( tiset );
  for( i=0; i<candidate_count; i++ ) {
    lindex = candidates[i];
    if( global_p_array[lindex_to_pindex(lindex)].tval ==
        Indeterminate ) {
      return lindex;
    }
  }
#endif /* RANDOMIZE */

  /* If we reach this point, then all the candidates have a truth
     value. */
  goto the_beginning;
}
