/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.4 $ */

#include <memory.h>
#include "cnfforms.h"
#include "poly.h"
#include "safemall.h"
#include "cmn-parr.h"

#ifdef THINK_C
#include <size_t.h>
void *memcpy(void *s1, const void *s2, size_t n);
#endif

common_prop_array common_p_array;
common_literal_members common_l_members;


void cindices_append_cindex( c_indices cis, long ci )
{
  append_to_array( (char **)&(cis->members),
                   sizeof(long),
                   &(cis->length),
                   &(cis->size),
                   (char *)&ci );
}

/* Repeatedly doubling the size of c_indices can waste a lot
   of space for very large formulas. */

void cindices_delete_wasted_space( c_indices cis )
{
  long cis_length = cis->length;

  if( cis_length < cis->size ) {
    long *old_members, *new_members;

    old_members = cis->members;
    new_members = (long *)safe_malloc( sizeof(long) * (size_t)cis_length );
    (void)memcpy( (char *)new_members,
                  (char *)old_members,
                  sizeof(long) * (size_t)cis_length );
    safe_free( old_members );
    cis->members = new_members;
    cis->size = cis_length;
  }
}

void cindices_free( c_indices cis )
{
  safe_free( cis->members );
  if( cis->length )
    safe_free( cis->common_pointers );
}

void common_parray_free( void )
{
  long i;

  for( i=0; i<the_prop_count; i++ ) {
    cindices_free( &(common_p_array[i].occurinfo[Pos]) );
    cindices_free( &(common_p_array[i].occurinfo[Neg]) );
  }
  safe_free( common_p_array );
}
