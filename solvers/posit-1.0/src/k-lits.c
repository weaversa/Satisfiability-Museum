/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.6 $ */

#include <limits.h>
#include <memory.h>
#include <stdio.h>
#include "cnfforms.h"
#include "dmcs-cnf.h"
#include "safemall.h"
#include "timeiset.h"
#include "k-lits.h"

#ifdef THINK_C
#include <size_t.h>
void *memset(void *s, int c, size_t n);
#endif

static time_index_set key_literals;
static time_index_set t_l;
static time_index_set t_l2;
static time_index_set vanished_clauses;
static long *occurrence_array;
static long *key_cindices1;
static long *other_cindices;
static long *backup_occurrences;

/* For doubleton deletion only: */

static time_index_set t_l_other;
static time_index_set t_l_other2;
static long *key_cindices2;



/* Create a new clause from a tiset and append it to the end
   of the formula. */

static void create_and_append_clause( time_index_set tiset )
{
  clause_object current_clause_obj;
  long cardinality, *members;
  literal current_lit;
  long j, sub_lindex;

  cardinality = tiset_cardinality( tiset );
  members = tiset_members( tiset );

  if( cardinality > SCHAR_MAX )
    fatal_error( "create_and_append_clause:  New clause is too long" );

  current_clause_obj.length = cardinality;
  current_lit =
    current_clause_obj.members =
      (literal_object *)
        safe_malloc( (size_t)cardinality * sizeof(literal_object) );

  for( j=0; j<cardinality; j++, current_lit++ ) {
    sub_lindex = members[j];
    current_lit->l_index = sub_lindex;
    current_lit->p_index = lindex_to_pindex( sub_lindex );
    current_lit->sign = lindex_to_sign( sub_lindex );
    current_lit->l_index2 = lindex_complement( sub_lindex );
  }

  formula_append_clause( the_formula, &current_clause_obj );
  if( the_clause_count == tiset_size(vanished_clauses) )
    tiset_double_size( vanished_clauses );
  the_clause_count++;
  if( cardinality > the_longest_clause_length )
    the_longest_clause_length = cardinality;
}

/* Delete all of the clauses whose indices are in vanished_clauses
   by replacing them with the clauses at the end of the formula.
   Make sure you replace the vanished clauses in *decreasing*
   order with respect to cindex to avoid the bug of replacing
   a vanished clause by another vanished clause.  Keep in mind
   that the elements of vanished_clauses are NOT necessarily
   sorted in increasing order. */

static void delete_vanished_clauses( void )
{
  long cindex;
  clause current_clause;

  /* Note that the initial value of cindex is correct, even though
     the_clause_count decreases inside the loop. */

  for( cindex = the_clause_count - 1; cindex > -1; cindex-- )
    if( tiset_member(vanished_clauses, cindex) ) {
      if( cindex == the_clause_count - 1 ) {
        /* We're deleting the last clause in the formula, so
           we cannot replace it with anything. */
        safe_free( the_formula->clauses[cindex].members );
      }
      else {
        current_clause = the_formula->clauses + cindex;
        safe_free( current_clause->members );
        current_clause->length =
          the_formula->clauses[the_clause_count - 1].length;
        current_clause->members =
          the_formula->clauses[the_clause_count - 1].members;
      }
      the_clause_count--;
    }

  the_formula->length = the_clause_count;
}

/* For convenience, we have to do this first. */

static void construct_lindex_info( void )
{
  clause c, upper_c_limit;
  literal lit, upper_l_limit;

  c = the_formula->clauses;
  upper_c_limit = c + the_formula->length;
  for( ;
       c < upper_c_limit;
       c++ ) {
    lit = c->members;
    upper_l_limit = lit + c->length;
    for( ;
         lit < upper_l_limit;
         lit++ ) {
      lit->l_index = litinfo_to_lindex( lit->sign, lit->p_index );
      lit->l_index2 = lindex_complement( lit->l_index );
    }
  }
}

/* Apply BCP to the raw formula. */

truth_value formula_bcp( void )
{
  time_index_set current_unit_lits;
  time_index_set new_unit_lits;
  time_index_set remaining_lits;
  time_index_set temp_tiset;
  long i, lindex;
  clause c, upper_c_limit;
  literal lit, upper_l_limit;
  truth_value result;

  current_unit_lits = tiset_emptyset( 2 * the_prop_count );

  /* Loop through the clauses and collect the literals in the
     unit clauses. */
  c = the_formula->clauses;
  upper_c_limit = c + the_formula->length;
  for( ; c < upper_c_limit; c++ )
    if( c->length == 1 )
      tiset_adjoin( current_unit_lits, c->members[0].l_index );

  if( tiset_isempty(current_unit_lits) ) {
    tiset_free( current_unit_lits );
    return (truth_value)Indeterminate;
  }

  new_unit_lits = tiset_emptyset( 2 * the_prop_count );
  remaining_lits = tiset_emptyset( 2 * the_prop_count );
  result = (truth_value)Indeterminate;

  while( tiset_notempty(current_unit_lits) ) {
    tiset_delete_all( vanished_clauses );
    tiset_delete_all( new_unit_lits );

    /* Loop through the clauses. */
    for( i=0; i<the_clause_count; i++ ) {

      /* We can't use pointer arithmetic, because we may modify
         the_formula inside this loop. */
      c = the_formula->clauses + i;

      tiset_delete_all( remaining_lits );

      /* Loop through the literals in c. */
      lit = c->members;
      upper_l_limit = lit + c->length;
      for( ;
           lit < upper_l_limit;
           lit++ ) {
        if( tiset_member(current_unit_lits, lit->l_index) ) {
          tiset_unsafe_adjoin( vanished_clauses, i );
          goto next_clause;
        }
        if( tiset_nonmember(current_unit_lits, lit->l_index2) )
          tiset_unsafe_adjoin( remaining_lits, lit->l_index );
      }

      if( tiset_isempty(remaining_lits) ) {
        result = (truth_value)False;
        goto clean_up;
      }
      if( tiset_cardinality(remaining_lits) < c->length ) {
        if( tiset_cardinality(remaining_lits) == 1 ) {
          lindex = tiset_members(remaining_lits)[0];
          if( tiset_member(new_unit_lits, lindex_complement(lindex)) ) {
            result = (truth_value)False;
            goto clean_up;
          }
          tiset_adjoin( new_unit_lits, lindex );
        }
        /* Replace c with a new, smaller clause.  It's cleaner if we
           do this for new unit clauses as well. */
        tiset_unsafe_adjoin( vanished_clauses, i );
        create_and_append_clause( remaining_lits );
      }

    next_clause:

      ;
    }    /* for( i ) */

    delete_vanished_clauses();
    if( the_clause_count == 0 ) {
      result = (truth_value)True;
      goto clean_up;
    }

    /* Swap current_unit_lits and new_unit_lits. */
    temp_tiset = current_unit_lits;
    current_unit_lits = new_unit_lits;
    new_unit_lits = temp_tiset;

  }    /* while( current_unit_lits is not empty ) */

 clean_up:

  tiset_free( current_unit_lits );
  tiset_free( new_unit_lits );
  tiset_free( remaining_lits );
  return result;
}

static void pure_literal_rule( time_index_set pure_lits )
{
  clause c;
  literal lit, upper_l_limit;
  long i;

  tiset_delete_all( vanished_clauses );
  for( i=0; i<the_clause_count; i++ ) {
    c = the_formula->clauses + i;
    lit = c->members;
    upper_l_limit = lit + c->length;
    for( ;
         lit < upper_l_limit;
         lit++ )
      if( tiset_member(pure_lits, lit->l_index) ) {
        tiset_unsafe_adjoin( vanished_clauses, i );
        break;
      }
  }
  delete_vanished_clauses();
}

int simplify_helper( void )
{
  long lindex, lindex2;
  long pindex, sub_pindex;
  long sub_lindex, sub_lindex2;
  long sub_sub_lindex;
  long lit_count;
  long i, i_limit, j, j_limit;
  clause c_l, c_l2, c_l_other;
  long c_l_cindex, c_l2_cindex, c_other_cindex;
  long cardinality, *members;
  clause current_clause, upper_c_limit;
  literal current_lit, upper_l_limit;
  long current_length;
  long max_occurrences, max_max, maxoccur_cap;
  long best_so_far, tie_breaker;
  int have_singleton_space;
  int is_member, is_member2;
  long score;
  int found_unit_clause = 0;

  /* For doubleton deletion only: */

  int have_doubleton_space;


  /* 0.  Initialize.  Calculate l_index, l_index2, etc. */

  max_max = LONG_MIN;      /* Important. */
  have_singleton_space = 0;
  have_doubleton_space = 0;
  lit_count = 2 * the_prop_count;
  maxoccur_cap = (500 < the_prop_count ? 500 : the_prop_count);

  /* 1.  Allocate space for key_literals. */

  key_literals = tiset_emptyset( lit_count );

  /* Main loop: */

  while( 1 ) {

    /* 2.  Collect a list of candidate 1-literals. */

    /* 2.a.  Initialize the occurrence array to all zeros. */

    (void)memset( (char *)occurrence_array,
                  '\0',
                  (size_t)lit_count * sizeof(long) );

    /* 2.b.  Clear out key_literals.  Initialize max_occurrences.
       Loop through the entire formula, incrementing the values in
       occurrence_array and modifying key_literals: When a literal's
       count goes from 0 to 1, adjoin its lindex to key_literals.
       When a literal's count goes from 1 to 2, delete its lindex
       from key_literals. */

    tiset_delete_all( key_literals );
    max_occurrences = 4;

    current_clause = the_formula->clauses;
    upper_c_limit = current_clause + the_clause_count;
    for( ;
         current_clause < upper_c_limit;
         current_clause++ ) {
      if( current_clause->length == 1 ) {
        found_unit_clause = 1;
        goto almost_done;
      }
      current_lit = current_clause->members;
      upper_l_limit = current_lit + current_clause->length;
      for( ;
           current_lit < upper_l_limit;
           current_lit++ ) {
        lindex = current_lit->l_index;
        occurrence_array[lindex]++;
        switch( occurrence_array[lindex] ) {
        case 1:
          tiset_unsafe_adjoin( key_literals, lindex );
          break;
        case 2:
          tiset_delete( key_literals, lindex );
          break;
        default:
          if( occurrence_array[lindex] > max_occurrences )
            max_occurrences = occurrence_array[lindex];
          break;
        }
      }
    }

    if( tiset_isempty(key_literals) )
      break;

    if( max_occurrences > maxoccur_cap )
      max_occurrences = maxoccur_cap;

    /* 3.  Delete the pure singletons and the singletons whose
       complements occur pathologically often. */

    for( i=0; i<the_prop_count; i++ ) {
      lindex = 2 * i;
      lindex2 = 2 * i + 1;
      if( occurrence_array[lindex] == 0 ||
          occurrence_array[lindex] > maxoccur_cap )
        tiset_delete( key_literals, lindex2 );
      if( occurrence_array[lindex2] == 0 ||
          occurrence_array[lindex2] > maxoccur_cap )
        tiset_delete( key_literals, lindex );
    }

    if( tiset_isempty(key_literals) )
      break;

    /* Allocate the space for the remaining data structures
       if you haven't already done so. */

    if( !have_singleton_space ) {
      have_singleton_space = 1;
      max_max = max_occurrences;
      t_l = tiset_emptyset( lit_count );
      t_l2 = tiset_emptyset( lit_count );
      key_cindices1 =
        (long *)safe_malloc( (size_t)the_prop_count * sizeof(long) );
      /* I'm treating this as a 2-dimensional array, even though
         it's technically a 1-dimensional array. */
      other_cindices =
        (long *)
          safe_malloc( (size_t)(the_prop_count * max_max) * sizeof(long) );
      backup_occurrences =
        (long *)safe_malloc( (size_t)lit_count * sizeof(long) );
    }
    else if( max_occurrences > max_max ) {
      max_max = max_occurrences;
      safe_free( other_cindices );
      other_cindices =
        (long *)
          safe_malloc( (size_t)(the_prop_count * max_max) * sizeof(long) );
    }

    /* 4.  Loop through the formula again and store clause indices. */

    (void)memcpy( (char *)backup_occurrences,
                  (char *)occurrence_array,
                  (size_t)lit_count * sizeof(long) );

    for( i = 0, current_clause = the_formula->clauses;
         i < the_clause_count;
         i++, current_clause++ ) {
      current_length = current_clause->length;
      current_lit = current_clause->members;
      upper_l_limit = current_lit + current_length;
      for( ;
           current_lit < upper_l_limit;
           current_lit++ ) {
        lindex = current_lit->l_index;
        lindex2 = current_lit->l_index2;
        pindex = current_lit->p_index;
        is_member = tiset_member( key_literals, lindex );
        is_member2 = tiset_member( key_literals, lindex2 );

        if( is_member && is_member2 ) {
          /* Delete lindex2 from key_literals. */
          tiset_delete( key_literals, lindex2 );
          key_cindices1[pindex] = i;
        }
        else if( is_member )
          key_cindices1[pindex] = i;
        else if( is_member2 ) {
          backup_occurrences[lindex]--;
          other_cindices
            [pindex * max_max + backup_occurrences[lindex]] = i;
        }
      }
    }

    if( tiset_isempty(key_literals) )
      break;

    /* 5.  Choose just one of the remaining singletons in key_literals,
       namely the one that, when deleted, would increase the overall
       length of the formula by the smallest amount. */

    best_so_far = LONG_MAX;
    tie_breaker = LONG_MAX;
    lindex = LONG_MAX;
    cardinality = tiset_cardinality( key_literals );
    members = tiset_members( key_literals );
    for( i=0; i<cardinality; i++ ) {
      sub_lindex = members[i];
      sub_pindex = lindex_to_pindex( sub_lindex );
      score =
        j_limit = occurrence_array[lindex_complement(sub_lindex)];

      /* Prefer singletons that occur in clauses free of other
         singletons and doubletons. */
      c_l_cindex = key_cindices1[sub_pindex];
      c_l = the_formula->clauses + c_l_cindex;
      current_lit = c_l->members;
      upper_l_limit = current_lit + c_l->length;
      for( ;
           current_lit < upper_l_limit;
           current_lit++ ) {
        sub_sub_lindex = current_lit->l_index;
        if( sub_sub_lindex != sub_lindex )
          switch( occurrence_array[sub_sub_lindex] ) {
            case 1:
              score += 64;
              break;
            case 2:
              score += 32;
              break;
            default:
              break;
          }
      }

      if( score < best_so_far ) {
        lindex = sub_lindex;
        best_so_far = score;
      }
      else if( score == best_so_far ) {
        score = 0;
        for( j=0; j<j_limit; j++ ) {
          c_other_cindex = other_cindices[sub_pindex * max_max + j];
          score += the_formula->clauses[c_other_cindex].length - 1;
        }
        score *= c_l->length - 1;

        if( score < tie_breaker ) {
          lindex = sub_lindex;
          tie_breaker = score;
        }
      }
    }

    lindex2 = lindex_complement( lindex );
    pindex = lindex_to_pindex( lindex );

    /* 6.  Delete pindex from the formula. */

    /* 6.a.  First, find the clause containing lindex and delete
       lindex from it. */

    c_l_cindex = key_cindices1[pindex];
    c_l = the_formula->clauses + c_l_cindex;

    tiset_delete_all( t_l );

    current_lit = c_l->members;
    upper_l_limit = current_lit + c_l->length;
    for( ;
         current_lit < upper_l_limit;
         current_lit++ ) {
      sub_lindex = current_lit->l_index;
      if( sub_lindex != lindex )
        tiset_unsafe_adjoin( t_l, sub_lindex );
    }

    tiset_delete_all( vanished_clauses );
    tiset_unsafe_adjoin( vanished_clauses, c_l_cindex );

    /* 6.b.  Then, find the clauses c_l2 containing lindex' and
       replace each of them with (c_l - lindex) v (c_l2 - lindex'). */

    i_limit = occurrence_array[lindex2];

    for( i=0; i<i_limit; i++ ) {
      c_l2_cindex = other_cindices[pindex * max_max + i];
      c_l2 = the_formula->clauses + c_l2_cindex;

      /* Unconditionally make c_l2 disappear. */
      tiset_unsafe_adjoin( vanished_clauses, c_l2_cindex );

      tiset_delete_all( t_l2 );

      current_lit = c_l2->members;
      upper_l_limit = current_lit + c_l2->length;
      for( ;
           current_lit < upper_l_limit;
           current_lit++ ) {
        sub_lindex = current_lit->l_index;
        if( sub_lindex != lindex2 )
          tiset_unsafe_adjoin( t_l2, sub_lindex );
      }

      cardinality = tiset_cardinality( t_l );
      members = tiset_members( t_l );
      for( j=0; j<cardinality; j++ ) {
        sub_lindex = members[j];
        if( tiset_member(t_l2, lindex_complement(sub_lindex)) )
          break;
        /* We cannot use tiset_unsafe_adjoin() here. */
        tiset_adjoin( t_l2, sub_lindex );
      }
      if( j == cardinality )
        create_and_append_clause( t_l2 );
    }    /* for( i ) */

    /* 6.c.  Delete all of the vanished clauses from the formula. */

    delete_vanished_clauses();

  }    /* while( 1 ) */


  /****** Next, perform doubleton deletion. ******/

  /* Main loop: */

  while( 1 ) {

    /* 2.  Collect a list of candidate doubletons. */

    /* 2.a.  Initialize the occurrence array to all zeros. */

    (void)memset( (char *)occurrence_array,
                  '\0',
                  (size_t)lit_count * sizeof(long) );

    /* 2.b.  Clear out key_literals.  Initialize max_occurrences.
       Loop through the entire formula, incrementing the values in
       occurrence_array and modifying key_literals: When a literal's
       count goes from 1 to 2, adjoin its lindex to key_literals.
       When a literal's count goes from 2 to 3, delete its lindex
       from key_literals. */

    tiset_delete_all( key_literals );
    max_occurrences = 4;
    /* Do not reset max_max; we need its current value in order to
       know if we should enlarge other_cindices. */

    current_clause = the_formula->clauses;
    upper_c_limit = current_clause + the_clause_count;
    for( ;
         current_clause < upper_c_limit;
         current_clause++ ) {
      if( current_clause->length == 1 ) {
        found_unit_clause = 1;
        goto almost_done;
      }
      current_lit = current_clause->members;
      upper_l_limit = current_lit + current_clause->length;
      for( ;
           current_lit < upper_l_limit;
           current_lit++ ) {
        lindex = current_lit->l_index;
        occurrence_array[lindex]++;
        switch( occurrence_array[lindex] ) {
        case 1:
          /* Don't compare to max_occurrences. */
          break;
        case 2:
          tiset_unsafe_adjoin( key_literals, lindex );
          break;
        case 3:
          tiset_delete( key_literals, lindex );
          break;
        default:
          if( occurrence_array[lindex] > max_occurrences )
            max_occurrences = occurrence_array[lindex];
          break;
        }
      }
    }

    if( tiset_isempty(key_literals) )
      break;

    if( max_occurrences > maxoccur_cap )
      max_occurrences = maxoccur_cap;

    /* 3.  Delete the pure doubletons and the doubletons whose
       complements occur pathologically often. */

    for( i=0; i<the_prop_count; i++ ) {
      lindex = 2 * i;
      lindex2 = 2 * i + 1;
      if( occurrence_array[lindex] == 0 ||
          occurrence_array[lindex] > maxoccur_cap )
        tiset_delete( key_literals, lindex2 );
      if( occurrence_array[lindex2] == 0 ||
          occurrence_array[lindex2] > maxoccur_cap )
        tiset_delete( key_literals, lindex );
    }

    if( tiset_isempty(key_literals) )
      break;

    /* Allocate the space for the remaining data structures
       if you haven't already done so. */

    if( !have_doubleton_space ) {

      /* Note that we have not necessarily allocated the space
         for the singleton data structures. */
      if( !have_singleton_space ) {
        have_singleton_space = 1;
        max_max = max_occurrences;    /* Used below. */
        t_l = tiset_emptyset( lit_count );
        t_l2 = tiset_emptyset( lit_count );
        key_cindices1 =
          (long *)safe_malloc( (size_t)the_prop_count * sizeof(long) );
        /* I'm treating this as a 2-dimensional array, even though
           it's technically a 1-dimensional array. */
        other_cindices =
          (long *)
            safe_malloc( (size_t)(the_prop_count * max_max) * sizeof(long) );
        backup_occurrences =
          (long *)safe_malloc( (size_t)lit_count * sizeof(long) );
      }

      have_doubleton_space = 1;
      t_l_other = tiset_emptyset( lit_count );
      t_l_other2 = tiset_emptyset( lit_count );
      key_cindices2 =
        (long *)safe_malloc( (size_t)the_prop_count * sizeof(long) );
    }

    if( max_occurrences > max_max ) {
      max_max = max_occurrences;
      safe_free( other_cindices );
      other_cindices =
        (long *)
          safe_malloc( (size_t)(the_prop_count * max_max) * sizeof(long) );
    }

    /* 4.  Loop through the formula again and store clause indices
       in key_cindices1, key_cindices2, and other_cindices. */

    (void)memcpy( (char *)backup_occurrences,
                  (char *)occurrence_array,
                  (size_t)lit_count * sizeof(long) );

    for( i=0; i<the_prop_count; i++ )
      key_cindices1[i] = -99;

    for( i = 0, current_clause = the_formula->clauses;
         i < the_clause_count;
         i++, current_clause++ ) {
      current_length = current_clause->length;
      current_lit = current_clause->members;
      upper_l_limit = current_lit + current_length;
      for( ;
           current_lit < upper_l_limit;
           current_lit++ ) {
        lindex = current_lit->l_index;
        lindex2 = current_lit->l_index2;
        pindex = current_lit->p_index;
        is_member = tiset_member( key_literals, lindex );
        is_member2 = tiset_member( key_literals, lindex2 );

        if( is_member && is_member2 ) {
          /* Delete lindex2 from key_literals.  This is the first
             time we've seen either lindex or lindex2, so i belongs
             in key_cindices1. */
          tiset_delete( key_literals, lindex2 );
          key_cindices1[pindex] = i;
        }
        else if( is_member ) {
          if( key_cindices1[pindex] == -99 )
            key_cindices1[pindex] = i;
          else
            key_cindices2[pindex] = i;
        }
        else if( is_member2 ) {
          backup_occurrences[lindex]--;
          other_cindices
            [pindex * max_max + backup_occurrences[lindex]] = i;
        }
      }
    }

    if( tiset_isempty(key_literals) )
      break;

    /* 5.  Choose just one of the remaining doubletons in key_literals,
       namely the one such that deleting it will increase the overall
       length of the formula by the smallest amount.  Note that we may
       end up choosing a doubleton whose complement is also a doubleton;
       this is certainly not a problem. */

    best_so_far = LONG_MAX;
    lindex = LONG_MAX;
    cardinality = tiset_cardinality( key_literals );
    members = tiset_members( key_literals );
    for( i=0; i<cardinality; i++ ) {
      sub_lindex = members[i];
      sub_lindex2 = lindex_complement( sub_lindex );
      sub_pindex = lindex_to_pindex( sub_lindex );
      j_limit = occurrence_array[sub_lindex2];
      score = 0;

      /* Prefer doubletons that occur in clauses free of other
         doubletons. */
      c_l_cindex = key_cindices1[sub_pindex];
      c_l = the_formula->clauses + c_l_cindex;
      current_lit = c_l->members;
      upper_l_limit = current_lit + c_l->length;
      for( ;
           current_lit < upper_l_limit;
           current_lit++ ) {
        sub_sub_lindex = current_lit->l_index;
        if( sub_sub_lindex != sub_lindex ) {
          if( occurrence_array[sub_sub_lindex] == 2 )
            score += 64;
          else
            score += j_limit;
        }
      }
      c_l2_cindex = key_cindices2[sub_pindex];
      c_l2 = the_formula->clauses + c_l2_cindex;
      current_lit = c_l2->members;
      upper_l_limit = current_lit + c_l2->length;
      for( ;
           current_lit < upper_l_limit;
           current_lit++ ) {
        sub_sub_lindex = current_lit->l_index;
        if( sub_sub_lindex != sub_lindex ) {
          if( occurrence_array[sub_sub_lindex] == 2 )
            score += 64;
          else
            score += j_limit;
        }
      }
      /* Do the same thing for the clauses containing the complement
         of sub_lindex. */
      for( j=0; j<j_limit; j++ ) {
        c_other_cindex = other_cindices[sub_pindex * max_max + j];
        c_l_other = the_formula->clauses + c_other_cindex;
        current_lit = c_l_other->members;
        upper_l_limit = current_lit + c_l_other->length;
        for( ;
             current_lit < upper_l_limit;
             current_lit++ ) {
          sub_sub_lindex = current_lit->l_index;
          if( sub_sub_lindex != sub_lindex2 ) {
            if( occurrence_array[sub_sub_lindex] == 2 )
              score += 64;
            else
              score += 2;
          }
        }
      }

      if( score < best_so_far ) {
        lindex = sub_lindex;
        best_so_far = score;
      }
      /* No tie-breaking should be necessary. */
    }

    lindex2 = lindex_complement( lindex );
    pindex = lindex_to_pindex( lindex );

    /* 6.  Find the two clauses c_l and c_l2 containing l. */

    c_l_cindex = key_cindices1[pindex];
    c_l2_cindex = key_cindices2[pindex];
    c_l = the_formula->clauses + c_l_cindex;
    c_l2 = the_formula->clauses + c_l2_cindex;

    /* 7.  Mark c_l and c_l2 as vanished. */

    tiset_delete_all( vanished_clauses );
    tiset_unsafe_adjoin( vanished_clauses, c_l_cindex );
    tiset_unsafe_adjoin( vanished_clauses, c_l2_cindex );

    /* 8.  Construct the sets t_l and t_l2 from c_l and c_l2,
       respectively, by deleting l from both clauses. */

    tiset_delete_all( t_l );
    current_lit = c_l->members;
    upper_l_limit = current_lit + c_l->length;
    for( ;
         current_lit < upper_l_limit;
         current_lit++ ) {
      sub_lindex = current_lit->l_index;
      if( sub_lindex != lindex )
        tiset_unsafe_adjoin( t_l, sub_lindex );
    }

    tiset_delete_all( t_l2 );
    current_lit = c_l2->members;
    upper_l_limit = current_lit + c_l2->length;
    for( ;
         current_lit < upper_l_limit;
         current_lit++ ) {
      sub_lindex = current_lit->l_index;
      if( sub_lindex != lindex )
        tiset_unsafe_adjoin( t_l2, sub_lindex );
    }

    /* 9.  For each clause c_l_other containing l': */

    i_limit = occurrence_array[lindex2];

    for( i=0; i<i_limit; i++ ) {
      c_other_cindex = other_cindices[pindex * max_max + i];
      c_l_other = the_formula->clauses + c_other_cindex;

      /* 9.a.  Unconditionally mark c_l_other as vanished. */

      tiset_unsafe_adjoin( vanished_clauses, c_other_cindex );

      /* 9.b.  Construct the sets t_l_other and t_l_other2 from
         c_l_other by deleting l' from the clause. */

      tiset_delete_all( t_l_other );
      tiset_delete_all( t_l_other2 );
      current_lit = c_l_other->members;
      upper_l_limit = current_lit + c_l_other->length;
      for( ;
           current_lit < upper_l_limit;
           current_lit++ ) {
        sub_lindex = current_lit->l_index;
        if( sub_lindex != lindex2 ) {        /* Not lindex. */
          tiset_unsafe_adjoin( t_l_other, sub_lindex );
          tiset_unsafe_adjoin( t_l_other2, sub_lindex );
        }
      }

      /* 9.c.  Add the contents of t_l to t_l_other.  If the
         resulting clause is not a tautology, create it and append
         it to the end of the formula. */

      cardinality = tiset_cardinality( t_l );
      members = tiset_members( t_l );
      for( j=0; j<cardinality; j++ ) {
        sub_lindex = members[j];
        if( tiset_member(t_l_other, lindex_complement(sub_lindex)) )
          break;
        /* We cannot use tiset_unsafe_adjoin() here. */
        tiset_adjoin( t_l_other, sub_lindex );
      }
      if( j == cardinality )
        create_and_append_clause( t_l_other );

      /* 9.d.  Add the contents of t_l2 to t_l_other2.  If the
         resulting clause is not a tautology, create it and append
         it to the end of the formula. */

      cardinality = tiset_cardinality( t_l2 );
      members = tiset_members( t_l2 );
      for( j=0; j<cardinality; j++ ) {
        sub_lindex = members[j];
        if( tiset_member(t_l_other2, lindex_complement(sub_lindex)) )
          break;
        /* We cannot use tiset_unsafe_adjoin() here. */
        tiset_adjoin( t_l_other2, sub_lindex );
      }
      if( j == cardinality )
        create_and_append_clause( t_l_other2 );

    }    /* for( i ) */

    /* 10.  Vanish the vanished clauses. */

    delete_vanished_clauses();

  }    /* while( 1 ) */

 almost_done:

  tiset_free( key_literals );

  if( have_singleton_space ) {
    tiset_free( t_l );
    tiset_free( t_l2 );
    safe_free( key_cindices1 );
    safe_free( other_cindices );
    safe_free( backup_occurrences );
  }

  if( have_doubleton_space ) {
    tiset_free( t_l_other );
    tiset_free( t_l_other2 );
    safe_free( key_cindices2 );
  }

  return found_unit_clause;
}

/* Objectives of this function:
   1.  Scan through the formula as few times as possible.
   2.  Apply unit clause resolution first.
   3.  Apply the pure literal rule second.
   4.  Apply singleton and doubleton deletion last. */

truth_value simplify_formula( void )
{
  time_index_set pure_literals;
  int found_unit_clause;
  long singleton_count, doubleton_count;
  truth_value result;
  long lit_count;
  clause c, upper_c_limit;
  literal lit, upper_l_limit;
  long i, lindex, lindex2;

  if( empty_clause )
    return (truth_value)False;

  result = (truth_value)Indeterminate;
  vanished_clauses = tiset_emptyset( the_clause_count );
  lit_count = 2 * the_prop_count;
  occurrence_array =
    (long *)safe_malloc( (size_t)lit_count * sizeof(long) );
  construct_lindex_info();

  found_unit_clause = 0;
  pure_literals = tiset_emptyset( lit_count );
  singleton_count = 0;
  doubleton_count = 0;

  /* Loop through the entire formula once.  Break if there is
     a unit clause. */
  (void)memset( (char *)occurrence_array,
                '\0',
                (size_t)lit_count * sizeof(long) );
  c = the_formula->clauses;
  upper_c_limit = c + the_formula->length;
  for( ;
       c < upper_c_limit;
       c++ ) {
    if( c->length == 1 ) {
      found_unit_clause = 1;
      break;
    }
    lit = c->members;
    upper_l_limit = lit + c->length;
    for( ;
         lit < upper_l_limit;
         lit++ ) {
      lindex = lit->l_index;
      occurrence_array[lindex]++;
      switch( occurrence_array[lindex] ) {
      case 1:
        singleton_count++;
        break;
      case 2:
        singleton_count--;
        doubleton_count++;
        break;
      case 3:
        doubleton_count--;
        break;
      default:
        break;
      }
    }
  }

  /* Loop through and fill up pure_literals if possible. */
  for( i=0; i<the_prop_count; i++ ) {
    lindex = 2 * i;
    lindex2 = 2 * i + 1;
    if( occurrence_array[lindex] &&
        occurrence_array[lindex2] == 0 )
      tiset_unsafe_adjoin( pure_literals, lindex );
    else if( occurrence_array[lindex2] &&
             occurrence_array[lindex] == 0 )
      tiset_unsafe_adjoin( pure_literals, lindex2 );
  }

  if( found_unit_clause == 0 &&
      tiset_isempty(pure_literals) &&
      singleton_count == 0 &&
      doubleton_count == 0 )
    /* result = Indeterminate; */
    goto almost_done;

  if( found_unit_clause ) {
    switch( formula_bcp() ) {
    case True:
      result = (truth_value)True;
      goto almost_done;
    case False:
      result = (truth_value)False;
      goto almost_done;
    case Indeterminate:
      break;
    }
    /* Loop through the formula again to find pure literals;
       existing ones may have disappeared, and new ones may
       have appeared. */
    tiset_delete_all( pure_literals );
    (void)memset( (char *)occurrence_array,
                  '\0',
                  (size_t)lit_count * sizeof(long) );
    c = the_formula->clauses;
    upper_c_limit = c + the_formula->length;
    for( ;
         c < upper_c_limit;
         c++ ) {
      lit = c->members;
      upper_l_limit = lit + c->length;
      for( ;
           lit < upper_l_limit;
           lit++ )
        occurrence_array[lit->l_index]++;
    }
    for( i=0; i<the_prop_count; i++ ) {
      lindex = 2 * i;
      lindex2 = 2 * i + 1;
      if( occurrence_array[lindex] &&
          occurrence_array[lindex2] == 0 )
        tiset_unsafe_adjoin( pure_literals, lindex );
      else if( occurrence_array[lindex2] &&
               occurrence_array[lindex] == 0 )
        tiset_unsafe_adjoin( pure_literals, lindex2 );
    }
  }

  if( tiset_notempty(pure_literals) ) {
    pure_literal_rule( pure_literals );
    if( the_clause_count == 0 ) {
      result = (truth_value)True;
      goto almost_done;
    }
  }

  found_unit_clause = simplify_helper();
  if( the_clause_count == 0 ) {
    result = (truth_value)True;
    goto almost_done;
  }

  while( found_unit_clause ) {
    switch( formula_bcp() ) {
    case True:
      result = (truth_value)True;
      goto almost_done;
    case False:
      result = (truth_value)False;
      goto almost_done;
    case Indeterminate:
      break;
    }
    found_unit_clause = simplify_helper();
    if( the_clause_count == 0 ) {
      result = (truth_value)True;
      goto almost_done;
    }
  }

 almost_done:

  tiset_free( vanished_clauses );
  safe_free( occurrence_array );
  tiset_free( pure_literals );
  return result;
}

