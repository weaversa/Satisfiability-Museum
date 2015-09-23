/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.2 $ */

#include "cnfforms.h"
#include "safemall.h"
#include "cmn-carr.h"

common_clause_array common_c_array;


void common_carray_free( void )
{
  safe_free( common_c_array[0].cset );
  safe_free( common_c_array );
}

