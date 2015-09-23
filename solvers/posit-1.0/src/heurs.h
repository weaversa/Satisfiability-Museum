/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.3 $ */

#ifndef HEURISTICS_H
#define HEURISTICS_H

#include "cmn-carr.h"
#include "smallarr.h"
#include "statebas.h"
#include "timeiset.h"

/* For communicating with satisfy_dynamic().  Must be negative. */
#define AHFalseFormula -1
#define AHTrueFormula  -2

/* For keeping track of the winning literals. */
extern small_array gapplyh_literals1;
extern time_index_set gapplyh_literals2;

/* For recording a pure literal. */
extern long gapplyh_pure_lindex;

/* For calculating the cost of a proposition. */
extern long shift_value;

extern unsigned char *binary_clause_info;


/* Macros and function prototypes. */

literal lindex_to_literal( long );

long apply_heuristic( void );

#endif
