/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.2 $ */

#ifndef CNF_FORMULAS_H
#define CNF_FORMULAS_H

/* Data structures for CNF formulas. */

#ifdef THINK_C
#include <size_t.h>  
#else
#include <stdlib.h>  /* To get size_t */
#endif
#include "statebas.h"

/* The total number of propositions in the formula. */
extern long the_prop_count;

/* The total number of clauses in the formula. */
extern long the_clause_count;

/* The length of the longest clause in the formula. */
extern long the_longest_clause_length;

/* The global list of propositions.  This list must not be modified
   in any way during the execution of the program, because other
   data structures in the program point to these propositions.
   The propositions may appear in any order. */

typedef struct {
  proposition *props;
  long length;          /* The number of actual props. in the array */
  long size;            /* The number of possible props. in the array */
} prop_list_object, *prop_list;

extern prop_list the_prop_list;

/* The global formula.  The literals are stored here. */

typedef struct {
  clause_object *clauses;
  long length;          /* The number of actual clauses in the array */
  long size;            /* The number of possible clauses in the array */
} formula_object, *formula;

/* The formula itself. */

extern formula the_formula;


/* Macros and function prototypes. */

size_t digits_in_long( long );

prop_list proplist_empty( long );

void proplist_append_prop( prop_list, proposition );

void proplist_free( prop_list );

formula formula_empty( long );

void formula_append_clause( formula, clause );

void formula_delete_wasted_space( formula );

void formula_free( formula );

#endif
