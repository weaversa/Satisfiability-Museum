/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.3 $ */

#ifndef PRIMITIVES_H
#define PRIMITIVES_H

/* The most primitive declarations. */

/* A three-valued logic. */

#ifdef True
#undef True
#endif

#ifdef False
#undef False
#endif

#define True 0                        /* Corresponds to Pos below. */
#define False 1                       /* Corresponds to Neg below. */
#define Indeterminate 2

typedef unsigned char truth_value;    /* Saves space! */

/* A proposition is just a string. */

typedef char *proposition;

/* The sign of a literal.  The values of Pos and Neg matter. */

typedef enum { Pos=0, Neg=1 } literal_sign;

#endif
