/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.2 $ */

#ifndef GLOBAL_PARRAY_H
#define GLOBAL_PARRAY_H

/* Proposition arrays. */

#include "prims.h"

/* The volatile components of the proposition array. */

typedef struct {
  truth_value tval;
} volatile_parrelt_object, *volatile_parray_element;

typedef volatile_parrelt_object *volatile_prop_array;

extern volatile_prop_array global_p_array;


typedef struct {
  long poscount;
  long negcount;
} volatile_pcountelt_object, *volatile_pcount_element;

typedef volatile_pcountelt_object *volatile_pcount_array;

extern volatile_pcount_array global_pcount_array;


/* Macros and function prototypes. */

#define global_truth_prop(x) (global_p_array[(x)].tval)

#define global_poscount(x) (global_pcount_array[(x)].poscount)

#define global_negcount(x) (global_pcount_array[(x)].negcount)

void global_parray_free( void );

#endif
