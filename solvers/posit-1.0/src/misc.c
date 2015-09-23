/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.2 $ */

#include <stdio.h>
#include "misc.h"

/* This function only works when dest and src are aligned
   on an 8-byte boundary, otherwise it causes a bus error. */

void save_state( char *dest, char *src, long n )
{
  double *dbl_dest, *dbl_src;

#ifdef DEBUG
  if( sizeof(double) < 8 )
    fprintf( stderr, "save_state:  double's are too small!\n" );
  if( n & (8 * sizeof(double) - 1) )
    fprintf( stderr, "save_state:  Wrong number of bytes!\n" );
#endif

  dbl_dest = (double *)dest;
  dbl_src = (double *)src;

  while( n ) {
    *dbl_dest = *dbl_src;
    dbl_src++;
    dbl_dest++;

    *dbl_dest = *dbl_src;
    dbl_src++;
    dbl_dest++;

    *dbl_dest = *dbl_src;
    dbl_src++;
    dbl_dest++;

    *dbl_dest = *dbl_src;
    dbl_src++;
    dbl_dest++;

    *dbl_dest = *dbl_src;
    dbl_src++;
    dbl_dest++;

    *dbl_dest = *dbl_src;
    dbl_src++;
    dbl_dest++;

    *dbl_dest = *dbl_src;
    dbl_src++;
    dbl_dest++;

    *dbl_dest = *dbl_src;
    dbl_src++;
    dbl_dest++;

    n -= 8 * sizeof(double);
  }
}
