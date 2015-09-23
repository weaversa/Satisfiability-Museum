/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.2 $ */

#ifndef LA_STACK_H
#define LA_STACK_H

/* The LookAhead stack. */

#include "statebas.h"

typedef long *lookahead_stack;

extern lookahead_stack global_la_stack;

extern long top_of_la_stack;


/* Macros and function prototypes. */

void lastack_emptystack( void );

#define lastack_isempty() (top_of_la_stack == -1)

#define lastack_notempty() (top_of_la_stack != -1)

#define lastack_delete_all() (top_of_la_stack = -1)

#define lastack_push_bcp(CI) do { \
    top_of_la_stack++; \
    global_la_stack[top_of_la_stack] = (CI); \
  } while( 0 )

#define lastack_top() (global_la_stack[top_of_la_stack])

#define lastack_pop() (top_of_la_stack--)

void lastack_free( void );

#endif
