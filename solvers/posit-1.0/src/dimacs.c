/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.2 $ */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "dmcs-cnf.h"
#include "dmcs-sat.h"
#include "safemall.h"
#include "dimacs.h"

#define CNF_FORMAT 0
#define SAT_FORMAT 1
#define LINELENGTH 80
#define SEPCHARS " \t\n"

static char current_line[LINELENGTH];
static char *current_word;

/* We do not want to reinitialize this variable when parsing multiple
   formulas from the same file. */

static long current_line_number = 1;

static void parse_comment_lines( void )
{
  do {
    /* If this call to fgets() fails, it's very likely that no problem
       was supplied in the first place, or the user asked to solve 10
       problems but supplied only 9, etc. */
    if( fgets(current_line, LINELENGTH, stdin) == NULL )
      fatal_error( "Bailing out:  No problem supplied" );
    current_line_number++;
  } while( *current_line == 'c' || *current_line == '\n' );
}

static int parse_problem_line( long *prop_cnt, long *clause_cnt )
{
  int result = CNF_FORMAT;    /* To eliminate the compiler warning. */
  static char short_problem_line[] =
    "Parse error:  Unexpected end of problem line";

  if( (current_word = strtok(current_line, SEPCHARS)) == NULL )
    fatal_error( short_problem_line );
  if( strcmp(current_word, "p") != 0 )
    fatal_error( "Parse error:  Unknown line type in preamble" );

  if( (current_word = strtok(NULL, SEPCHARS)) == NULL )
    fatal_error( short_problem_line );
  if( strcmp(current_word, "cnf") == 0 )
    result = CNF_FORMAT;
  /* "satx", "sate", and "satex" are valid problem types. */
  else if( strncmp(current_word, "sat", 3) == 0 )
    result = SAT_FORMAT;
  else {
    fprintf( stderr,
             "Parse error:  Unknown problem format \"%s\"\n",
             current_word );
    exit( 1 );
  }

  if( (current_word = strtok(NULL, SEPCHARS)) == NULL )
    fatal_error( short_problem_line );
  if( (*prop_cnt = atol(current_word)) <= 0 )
    fatal_error( "Parse error:  Invalid number of propositions" );

  if( result == CNF_FORMAT ) {
    if( (current_word = strtok(NULL, SEPCHARS)) == NULL )
      fatal_error( short_problem_line );
    if( (*clause_cnt = atol(current_word)) <= 0 )
      fatal_error( "Parse error:  Invalid number of clauses" );
  }

  return result;
}

/* Branch, depending on whether the problem in question is a CNF
   problem or a SAT problem. */

void get_dimacs_formula( void )
{
  long prop_count, clause_count;

  parse_comment_lines();
  if( parse_problem_line(&prop_count, &clause_count) == CNF_FORMAT )
    /* Due to the nature of cnf format, keeping track of line
       numbers is too difficult. */
    get_cnf_formula( prop_count, clause_count );
  else
    get_sat_formula( prop_count, current_line_number );
}
