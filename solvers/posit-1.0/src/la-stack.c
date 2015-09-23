/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.2 $ */

#include "cnfforms.h"
#include "safemall.h"
#include "la-stack.h"

lookahead_stack global_la_stack;

long top_of_la_stack;


void lastack_emptystack( void )
{
  top_of_la_stack = -1;

  /* Theoretically, the depth of the stack is bounded by the number
     of clauses, but in practice it doesn't usually get very deep. */
  global_la_stack =
    (lookahead_stack)
      safe_malloc( sizeof(long) *
                   (size_t)(the_clause_count < 500 ?
                            the_clause_count : 500) );
}

void lastack_free( void )
{
  safe_free( global_la_stack );
}
