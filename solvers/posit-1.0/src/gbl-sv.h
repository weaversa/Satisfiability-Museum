/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.2 $ */

#ifndef GLOBAL_SV_H
#define GLOBAL_SV_H

#include "statebas.h"

/* The global state vectors.  I mean "global" in the sense of
   global (i.e., exhaustive) search, not in the sense of
   global variable. */


/* Macros and function prototypes. */

/* log2() is not widely available. */
#define log_base_2(X) (log(X) / log(2.0))

void global_sv_make( void );

void global_sv_free( void );

int extend_prop_la( long, int );

#define extend_lit_la( LIT, TVAL ) ( (LIT)->sign == Pos ? \
   ( (TVAL) == True ? \
     extend_prop_la((LIT)->p_index, True) : \
     extend_prop_la((LIT)->p_index, False) ) : \
   ( (TVAL) == True ? \
     extend_prop_la((LIT)->p_index, False) : \
     extend_prop_la((LIT)->p_index, True) ) )

/* Returns a negative quantity if failure occurs, otherwise returns
   the cost as a positive quantity. */
long extend_prop_la_for_failure( long, int );

truth_value global_truth_formula( void );

#endif

