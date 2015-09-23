/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.2 $ */

#ifndef HEURISTIC2_H
#define HEURISTIC2_H

/* Heuristic 2:  Run the full-blown constraint propagation algorithm,
   then undo all the changes.  Return the total number of calls to
   extend_lit_la(). */

#include "gbl-parr.h"

extern volatile_prop_array backup_p_array;


/* Macros and function prototypes. */

long heuristic2a( long );

#endif
