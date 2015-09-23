/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.2 $ */

#include "safemall.h"
#include "gbl-parr.h"

volatile_prop_array global_p_array;

volatile_pcount_array global_pcount_array;


void global_parray_free( void )
{
  safe_free( global_p_array );
  safe_free( global_pcount_array );
}
