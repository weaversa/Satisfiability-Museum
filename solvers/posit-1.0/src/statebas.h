/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.3 $ */

#ifndef STATE_BASICS_H
#define STATE_BASICS_H

#include "prims.h"

/* Basic types for state vectors. */

#include "cmn-parr.h"

/* A literal is a literal sign and the index of its associated
   proposition in the_prop_list and/or the prop-array. */

/* All the literal_object's are actually stored in the_formula. */

typedef struct literal_object {
  long p_index;
  literal_sign sign;
  /* The following components are not strictly necessary, but
     make the code faster. */
  long l_index;
  long l_index2;
  long c_index;
  common_parray_element common_pointer;
} literal_object, *literal;

/* Clauses. */

typedef struct {
  literal_object *members;
  long length;
} clause_object, *clause;

/* Boolean constraint propagation and the positive-negative rule. */

typedef enum { BCP, PosNeg } lookahead_type;


/* Macros and function prototypes. */

/* A quick and dirty macro for truth values. */
#define tval_quick_complement(x) (1 - (x))

/* Lots of macros for literals and literal indices. */
#define lsign_complement(x) (1 - (x))
#define lindex_is_positive(x) ((x) % 2 == 0)
#define lindex_is_negative(x) ((x) % 2)
#define lindex_to_pindex(x) ((x) / 2)
#define lindex_to_sign(x) ((literal_sign)((x) % 2))
#define lindex_complement(x) (((x) % 2) ? ((x) - 1) : ((x) + 1))
#define litinfo_to_lindex(x,y) (2 * (y) + (x))
#define litinfo_to_lindex2(x,y) (2 * (y) + (1 - (x)))

void clause_append_literal( clause, literal, long * );

void clause_delete_wasted_space( clause, long );

void litsign_print( literal_sign );

void tval_print( truth_value );

void literal_print( literal );

#endif
