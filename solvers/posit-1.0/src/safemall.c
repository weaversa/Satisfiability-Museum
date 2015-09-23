/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.2 $ */

#ifndef SUNOS
#ifndef THINK_C
#include <malloc.h>
#endif  /* THINK_C */
#endif /* SUNOS */
#include <stdio.h>
#include <errno.h>
#include "safemall.h"

#ifdef DEBUG
long malloc_counter;
#endif

void fatal_error( char *message )
{
  if( errno )
    perror( message );
  else
    fprintf( stderr, "%s.\n", message );
  exit( 1 );
}

void *safe_malloc( size_t size )
{
  void *result;

  if( (result = malloc(size)) == NULL )
    fatal_error( "Unable to allocate enough memory" );
#ifdef DEBUG
  malloc_counter++;
#endif
  return result;
}

void safe_free( void *ptr )
{
  if( ptr )
    (void)free( ptr );
#ifdef DEBUG
  else
    fprintf( stderr, "Warning:  attempt to free a NULL pointer" );
  malloc_counter--;
#endif
}
