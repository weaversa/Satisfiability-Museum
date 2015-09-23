/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.2 $ */

#include <ctype.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include "cnfforms.h"
#include "safemall.h"
#include "timeiset.h"
#include "dmcs-sat.h"

/* This code assumes that every formula contains at least one clause
   and every clause contains at least one literal. */

typedef enum { EMPTY, LPAREN, RPAREN, AND, OR, NOT, PROP } sat_token_type;

static long current_clause_number;
static literal_object current_lobj;
static long static_prop_count;
static long static_line_number;
static time_index_set literals_in_clause;

static char lparen_error[] = "Expecting a left parenthesis";
static char rparen_error[] = "Expecting a right parenthesis";

static void sat_parse_error( char *s )
{
  fprintf( stderr, "Input line %ld: %s\n", static_line_number, s );
  exit( 1 );
}

/* I only need one character of lookahead, so it suffices to use
   getchar() and ungetc(). */

static sat_token_type get_sat_token( void )
{
  int c;

  do {
    if( (c = getchar()) == '\n' )
      static_line_number++;
  } while( isspace(c) );

  if( c == '(' )
    return LPAREN;
  if( c == ')' )
    return RPAREN;
  if( c == '*' )
    return AND;
  if( c == '+' )
    return OR;
  if( c == '-' )
    return NOT;
  if( c == EOF )
    return EMPTY;

  if( isdigit(c) ) {
    if( ungetc(c, stdin) == EOF )
      fatal_error( "ungetc() failed" );
    if( scanf("%ld", &(current_lobj.p_index)) == 0 )
      sat_parse_error( "Bad proposition" );
    return PROP;
  }
  sat_parse_error( "Unrecognized token" );
  return PROP;   /* To avoid the stupid compiler warning. */
}

static sat_token_type peek_sat_token( void )
{
  int c;

  do {
    if( (c = getchar()) == '\n' )
      static_line_number++;
  } while( isspace(c) );
  if( ungetc(c, stdin) == EOF )
    fatal_error( "ungetc() failed" );

  switch( c ) {
  case '(':
    return LPAREN;
  case ')':
    return RPAREN;
  case '*':
    return AND;
  case '+':
    return OR;
  case '-':
    return NOT;
  case EOF:
    return EMPTY;
  }

  if( isdigit(c) )
    return PROP;
  sat_parse_error( "Unrecognized token" );
  return PROP;   /* To avoid the stupid compiler warning. */
}

static void get_sat_literal( void )
{
  switch( get_sat_token() ) {
  case PROP:   /* Base case */
    current_lobj.sign = Pos;
    break;
  case NOT:
    get_sat_literal();
    current_lobj.sign = lsign_complement( current_lobj.sign );
    break;
  case LPAREN:
    get_sat_literal();
    if( get_sat_token() != RPAREN )
      sat_parse_error( rparen_error );
    break;
  default:
    sat_parse_error( "Expecting a literal" );
    break;
  }
}

/* Most of the semantics are buried in here. */

static void get_sat_literals( void )
{
  sat_token_type next_token;
  clause_object current_clause_object;
  long current_clause_size;
  long lindex, lindex2;
  int keep_clause = 1;

  current_clause_object.length = 0;
  current_clause_size = 4;
  current_clause_object.members =
    (literal_object *)safe_malloc( sizeof(literal_object) * 4 );

  do {
    get_sat_literal();
    if( current_lobj.p_index < 1 ||
        current_lobj.p_index > static_prop_count )
      sat_parse_error( "Proposition out of range" );
    current_lobj.p_index--;      /* Must be 0-indexed. */
    lindex = 2 * current_lobj.p_index + (current_lobj.sign == Neg);
    lindex2 = 2 * current_lobj.p_index + (current_lobj.sign == Pos);

    if( !tiset_member(literals_in_clause, lindex) &&
        !tiset_member(literals_in_clause, lindex2) ) {
      tiset_adjoin( literals_in_clause, lindex );
      clause_append_literal( &current_clause_object, &current_lobj,
                             &current_clause_size );
    }
    else {
      /* Note that by failing to increment current_clause_number
         here, you're making the diagnostics more confusing. */
      if( tiset_member(literals_in_clause, lindex2) ) {
        fprintf( stderr, "Warning:  Clause %ld contains a literal \
and its complement.\nI'm discarding the entire clause.\n",
                 current_clause_number );
        keep_clause = 0;
        next_token = peek_sat_token();
        break;
      }
      /* A clause may contain lindex twice AND lindex2.  This case
         should be second, since discarding a literal is irrelevant
         if we're discarding the entire clause. */
      if( tiset_member(literals_in_clause, lindex) )
        fprintf( stderr, "Warning:  A literal appears more than once \
in clause %ld.\nI'm discarding the extra occurrence.\n",
                 current_clause_number );
    }

    next_token = peek_sat_token();
  } while( next_token == NOT || next_token == PROP ||
           next_token == LPAREN );

  if( next_token != RPAREN )    /* End of the clause */
    sat_parse_error( "Unrecognized input following a literal" );
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
    current_clause_number++;
  }
  else
    safe_free( current_clause_object.members );
}

static void get_sat_clause( void )
{
  switch( get_sat_token() ) {
  case OR:
    if( get_sat_token() != LPAREN )
      sat_parse_error( lparen_error );
    get_sat_literals();
    if( get_sat_token() != RPAREN )
      sat_parse_error( rparen_error );
    break;
  case LPAREN:
    get_sat_clause();
    if( get_sat_token() != RPAREN )
      sat_parse_error( rparen_error );
    break;
  default:
    sat_parse_error( "Expecting a clause" );
    break;
  }
  tiset_delete_all( literals_in_clause );
}

static void get_sat_clauses( void )
{
  sat_token_type next_token;

  do {
    get_sat_clause();
    next_token = peek_sat_token();
  } while( next_token == OR || next_token == LPAREN );

  if( next_token != RPAREN )    /* End of the formula */
    sat_parse_error( "Unrecognized input following a clause" );
}

static void get_sat_inner_formula( void )
{
  switch( get_sat_token() ) {
  case AND:
    if( get_sat_token() != LPAREN )
      sat_parse_error( lparen_error );
    get_sat_clauses();
    if( get_sat_token() != RPAREN )
      sat_parse_error( rparen_error );
    break;
  case LPAREN:
    get_sat_inner_formula();
    if( get_sat_token() != RPAREN )
      sat_parse_error( rparen_error );
    break;
  default:
    sat_parse_error( "Expecting a formula" );
    break;
  }
}

void get_sat_formula( long prop_count, long line_number )
{
  long i;
  size_t max_prop_length;

  /* 1.  Initialize. */

  static_prop_count = prop_count;
  static_line_number = line_number;
  current_clause_number = 1;
  the_prop_count = prop_count;
  the_longest_clause_length = -99;
  the_formula = formula_empty( 16 );
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

  /* 2.  Parse the formula. */

  if( get_sat_token() != LPAREN )
    sat_parse_error( lparen_error );
  get_sat_inner_formula();
  if( get_sat_token() != RPAREN )
    sat_parse_error( rparen_error );

  /* 3.  Initialize the_clause_count. */

  the_clause_count = the_formula->length;

  /* 4.  Resize the_formula->clauses to avoid the wasted space
     due to repeatedly doubling the size of this array. */

  formula_delete_wasted_space( the_formula );

  /* 5.  Clean up. */

  tiset_free( literals_in_clause );
}
