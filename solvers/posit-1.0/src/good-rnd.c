/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.7 $ */

/* A good (uniform) random number generator for platforms with (at
   least) 32-bit long integers.  From Numerical Recipes in C, Second
   Edition, Section 7.1 (page 282). */

#include <stdio.h>
#include "good-rnd.h"

#if defined(THINK_C)
#include "time.h"
#define getpid() 27449  /* The 3,000th prime. */
#else
#include <sys/time.h>
#include <unistd.h>     /* For getpid(). */
#endif

#define IM1   2147483563
#define IM2   2147483399
#define AM    (1.0/IM1)
#define IMM1  (IM1-1)
#define IA1   40014
#define IA2   40692
#define IQ1   53668
#define IQ2   52774
#define IR1   12211
#define IR2   3791
#define NTAB  32
#define NDIV  (1+IMM1/NTAB)
#define EPS   1.2e-7
#define RNMX  (1.0-EPS)

long random_seed;


void reset_seed( void )
{
  if( random_seed == 0 ) {
    /* Choose a seed for the user. */
    /* getpid() is necessary when we're solving more than one problem
       per second. */
    random_seed = -((long)time(NULL) + (long)getpid());
    return;
  }
  if( random_seed > 0 )
    random_seed = -random_seed;
}

/* Long period (> 2 x 10^18) random number generator of L'Ecuyer with
   Bays-Durham shuffle and added safeguards.  Returns a uniformly
   distributed random number between 0.0 and 1.0, exclusive. */

double good_random( void )
{
  int    j;
  long   k;
  static long seed2 = 123456789;
  static long iy = 0;
  static long iv[NTAB];
  double temp;

  if( random_seed <= 0 ) {
    if( -random_seed < 1 )
      random_seed = 1;
    else
      random_seed = -random_seed;
    seed2 = random_seed;
    for( j=NTAB+7; j>=0; j--) {
      k = random_seed / IQ1;
      random_seed = IA1 * (random_seed - k * IQ1) - k * IR1;
      if( random_seed < 0 )
        random_seed += IM1;
      if( j < NTAB )
        iv[j] = random_seed;
    }
    iy = iv[0];
  }
  k = random_seed / IQ1;
  random_seed = IA1 * (random_seed - k * IQ1) - k * IR1;
  if( random_seed < 0 )
    random_seed += IM1;
  k = seed2 / IQ2;
  seed2 = IA2 * (seed2 - k * IQ2) - k * IR2;
  if( seed2 < 0 )
    seed2 += IM2;
  j = (int)(iy / NDIV);
  iy = iv[j] - seed2;
  iv[j] = random_seed;
  if( iy < 1 )
    iy += IMM1;
  if( (temp = AM * iy) > RNMX )
    return RNMX;
  return temp;
}

/* A faster but still portable random number generator for those
   occasions when speed is critical.  From the same section of the
   same book.  Note that the version in the book contains two bugs
   which I have fixed below. */

#define MBIG 1000000000
#define MSEED 161803398
#define MZ 0
#define FAC (1.0 / MBIG)

double fast_random( void )
{
  static int inext, inextp;
  static long ma[56];
  static int iff=0;
  long mj, mk;
  int i, ii, k;

  if( random_seed < 0 ||
      iff == 0 ) {
    iff = 1;
    /* This fixes a bug in the Second Edition. */
    mj = MSEED - (random_seed < 0 ? -random_seed : random_seed) % MSEED;
    ma[55] = mj;
    mk = 1;
    for( i=1; i<=54; i++ ) {
      ii = (21 * i) % 55;
      ma[ii] = mk;
      mk = mj - mk;
      if( mk < MZ )
        mk += MBIG;
      mj = ma[ii];
    }
    for( k=1; k<=4; k++ )
      for( i=1; i<=55; i++ ) {
        ma[i] -= ma[1 + (i+30) % 55];
        if( ma[i] < MZ )
          ma[i] += MBIG;
      }
    inext = 0;
    inextp = 31;
    /* This logic is also better than what appears in the book. */
    if( random_seed < 0 )
      random_seed = 1;
  }
  /* Here is where we start, except on initialization. */
  if( ++inext == 56 )
    inext = 1;
  if( ++inextp == 56 )
    inextp = 1;
  mj = ma[inext] - ma[inextp];
  if( mj < MZ )
    mj += MBIG;
  ma[inext] = mj;

#ifdef DEBUG
  if( mj < 0 ||
      mj > MBIG ) {
    fprintf( stderr, "fast_random:  Output is < 0 or > 1!\n" );
  }
#endif
  return (double)(mj * FAC);
}
