/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.3 $ */

#ifndef BT_STACK_H
#define BT_STACK_H

/* The backtracking stack used in the main search algorithm.
   It's actually a collection of several stacks. */

#include "statebas.h"
#include "gbl-parr.h"

extern long *lindex_stack;
extern volatile_prop_array *prop_array_stack;
extern long *valued_prop_stack;
extern unsigned char **binary_info_stack;

extern long top_of_bt_stack;

extern long prop_array_size;
extern long lit_array_size;
extern long clause_array_size;
extern long total_array_size;
extern volatile_prop_array temp_p_array;


/* Macros and function prototypes. */

void btstack_emptystack( void );

#define btstack_isempty() (top_of_bt_stack == -1)

void btstack_push( void );

void btstack_restore( void );

#define btstack_pop() (top_of_bt_stack--)

void btstack_free( void );

#endif
