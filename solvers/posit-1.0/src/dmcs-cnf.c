/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.2 $ */

#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "cnfforms.h"
#include "safemall.h"
#include "timeiset.h"
#include "dmcs-cnf.h"

int empty_clause;

static long current_clause_number;
static long static_prop_count;
static long current_lindex;
static time_index_set literals_in_clause;

static int get_cnf_literal( void )
{
  return( scanf("%ld", &current_lindex) );
}

static void get_cnf_literals( void )
{
  clause_object current_clause_object;
  long current_clause_size;
  int literal_code;
  literal_object lobj;
  long lindex, lindex2;
  int keep_clause = 1;

  current_clause_object.length = 0;
  current_clause_size = 4;
  current_clause_object.members =
    (literal_object *)safe_malloc( sizeof(literal_object) * 4 );

  while( 1 ) {
    if( (literal_code = get_cnf_literal()) == 0 ) {
      fprintf( stderr, "Parse error:  Bad data in clause %ld",
               current_clause_number );
      exit( 1 );
    }
    if( literal_code == EOF || current_lindex == 0 )
      break;

    if( current_lindex < 0 ) {
      lobj.sign = Neg;
      lobj.p_index = -1 - current_lindex;    /* 0-indexed */
      lindex = 2 * lobj.p_index + 1;
      lindex2 = 2 * lobj.p_index;
    }
    else {
      lobj.sign = Pos;
      lobj.p_index = current_lindex - 1;     /* 0-indexed */
      lindex = 2 * lobj.p_index;
      lindex2 = 2 * lobj.p_index + 1;
    }

    if( lobj.p_index >= static_prop_count ) {
      fprintf( stderr, "Literal %ld in clause %ld is out of range.\n",
               current_lindex, current_clause_number );
      exit( 1 );
    }

    if( !tiset_member(literals_in_clause, lindex) &&
        !tiset_member(literals_in_clause, lindex2) ) {
      tiset_adjoin( literals_in_clause, lindex );
      clause_append_literal( &current_clause_object, &lobj,
                             &current_clause_size );
    }
    else {
      if( tiset_member(literals_in_clause, lindex2) ) {
        fprintf( stderr, "Warning:  Clause %ld contains literal %ld \
and its complement.\nI'm discarding the entire clause.\n",
                 current_clause_number,
                 current_lindex );
        keep_clause = 0;
        /* We still have to swallow up the rest of the clause, so
           we cannot break out of the loop here. */
      }
      /* A clause may contain lindex twice AND lindex2. */
      if( tiset_member(literals_in_clause, lindex) )
        fprintf( stderr, "Warning:  Literal %ld appears more than once \
in clause %ld.\nI'm discarding the extra occurrence.\n",
                 current_lindex, current_clause_number );
    }
  }   /* while( 1 ) */

  if( current_clause_object.length == 0 )
    if( literal_code == EOF ) {
      fprintf( stderr, "Parse error:  Unexpected EOF in clause %ld.\n",
               current_clause_number );
      exit( 1 );
    }
    else {      /* current_lindex == 0 */
      fprintf( stderr, "Warning:  Clause %ld is empty.\n",
               current_clause_number );
      empty_clause = 1;
      keep_clause = 0;
    }

  if( keep_clause ) {
    if( current_clause_object.length > the_longest_clause_length ) {
      if( current_clause_object.length > SCHAR_MAX ) {
        fprintf( stderr, "Error:  Clause %ld is too long.\n",
                 current_clause_number );
        exit( 1 );
      }
      the_longest_clause_length = current_clause_object.length;
    }
    clause_delete_wasted_space( &current_clause_object,
                                current_clause_size );
    formula_append_clause( the_formula, &current_clause_object );
  }
  else
    safe_free( current_clause_object.members );
  current_clause_number++;
}

static void get_cnf_clause( void )
{
  get_cnf_literals();
  tiset_delete_all( literals_in_clause );
}

void get_cnf_formula( long prop_count, long clause_count )
{
  long i;
  size_t max_prop_length;

  empty_clause = 0;
  static_prop_count = prop_count;
  current_clause_number = 1;
  the_prop_count = prop_count;
  the_longest_clause_length = -99;
  the_formula = formula_empty( clause_count );
  the_prop_list = proplist_empty( prop_count );
  the_prop_list->length = prop_count;
  /* In this format, propositions range from 1 to prop_count. */
  max_prop_length = 1 + digits_in_long( prop_count );
  for( i=0; i<prop_count; i++ ) {
    the_prop_list->props[i] =
      (proposition)safe_malloc( max_prop_length );
    (void)sprintf( the_prop_list->props[i], "%ld", i+1 );
  }
  literals_in_clause = tiset_emptyset( 2 * prop_count );
  for( i=0; i<clause_count; i++ )
    get_cnf_clause();
  if( the_formula->length < clause_count )
    fprintf( stderr, "Warning:  I only found %ld valid clauses.\n",
             the_formula->length );
  the_clause_count = the_formula->length;
  tiset_free( literals_in_clause );
}

static void literal_print_cnf( literal lit, int detailed )
{
  if( detailed )
    fprintf( stderr, "(%s %s, pi=%ld, li=%ld, li2=%ld)",
             (lit->sign == Pos ? "Pos" : "Neg"),
             the_prop_list->props[lit->p_index],
             lit->p_index,
             lit->l_index,
             lit->l_index2 );
  else
    fprintf( stderr, "%ld",
             (lit->sign == Pos ? lit->p_index + 1 : -1 - lit->p_index) );
}

void clause_print_cnf( clause c, int detailed )
{
  long i;
  long c_length;

  c_length = c->length;
  for( i=0; i<c_length; i++ ) {
    literal_print_cnf( c->members + i, detailed );
    fprintf( stderr, " " );
  }
  fprintf( stderr, "0\n" );
}

void formula_print_cnf( int detailed )
{
  long i;

  fprintf( stderr, "c POSIT generated this problem file.\nc\n" );
  fprintf( stderr, "p cnf %ld %ld\n", the_prop_count, the_clause_count );
  for( i=0; i<the_clause_count; i++ )
    clause_print_cnf( the_formula->clauses + i, detailed );
}
