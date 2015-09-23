/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.3 $ */

#ifndef GOOD_RANDOM_H
#define GOOD_RANDOM_H

/* A good random number generator. */

extern long random_seed;

void reset_seed( void );

double good_random( void );

double fast_random( void );

/* Returns a long integer in the range [0, x-1]. */
#define random_long(x) ((long)(good_random() * (double)(x)))

#define fast_random_long(x) ((long)(fast_random() * (double)(x)))

#endif
