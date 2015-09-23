/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.2 $ */

#include <memory.h>
#include <stdlib.h>
#include <stdio.h>
#include "safemall.h"
#include "readdata.h"

#ifdef THINK_C
#include <size_t.h>
void *memset(void *s, int c, size_t n);
#endif

/* Read a number from stdin in a robust fashion and return it.
   These functions work pretty well.  The key idea is to scan for a
   string before scanning for a number. */

long read_long( char *prompt, long dfault, int flag )
{
  int failure = 1;
  long result;
  char buf[LINEMAX], temp[LINEMAX];

  do {
    (void)memset( buf, '\0', LINEMAX );
    (void)memset( temp, 'x', LINEMAX );
    if( flag )
      printf( "%s [%ld]: ", prompt, dfault );
    else
      printf( "%s: ", prompt );
    (void)fflush( stdout );
    if( (fgets( buf, LINEMAX, stdin ) != NULL) &&
        sscanf( buf, "%s", temp ) ) {
      if( feof( stdin ) )  /* The user typed <stuff>^D^D. */
        exit( 0 );
      failure = !sscanf( temp, "%ld", &result );
      if( failure && flag )
        return dfault;
    }
    if( feof( stdin ) )  /* The user typed ^D. */
      exit( 0 );
  } while( failure );
  return result;
}

double read_double( char *prompt, double dfault, int flag )
{
  int failure = 1;
  double result;
  char buf[LINEMAX], temp[LINEMAX];

  do {
    (void)memset( buf, '\0', LINEMAX );
    (void)memset( temp, 'x', LINEMAX );
    if( flag )
      printf( "%s [%.3f]: ", prompt, dfault );
    else
      printf( "%s: ", prompt );
    (void)fflush( stdout );
    if( (fgets( buf, LINEMAX, stdin ) != NULL) &&
        sscanf( buf, "%s", temp ) ) {
      if( feof( stdin ) )  /* The user typed <stuff>^D^D. */
        exit( 0 );
      failure = !sscanf( temp, "%lf", &result );
      if( failure && flag )
        return dfault;
    }
    if( feof( stdin ) )  /* The user typed ^D. */
      exit( 0 );
  } while( failure );
  return result;
}

char *read_string( char *prompt )
{
  char buf[LINEMAX], *result;

  result = (char *)safe_malloc( sizeof(char) * LINEMAX );
  (void)memset( result, '\0', LINEMAX );
  printf( "%s: ", prompt );
  (void)fflush( stdout );
  (void)fgets( buf, LINEMAX, stdin );
  if( feof(stdin) )   /* The user typed ^D. */
    exit( 0 );
  (void)sscanf( buf, "%s", result );
  return result;
}
