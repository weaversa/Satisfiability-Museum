/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.2 $ */

#ifndef GLOBAL_CARRAY_H
#define GLOBAL_CARRAY_H

/* Clause arrays. */

/* The components of the clause array for global search. */

/* data > 0 => Indeterminate; the exact value is the number of
   Indeterminate literals.  data == 0 => False, and data < 0
   => True. */

typedef struct {
  signed char data;
} volatile_carrelt_object, *volatile_carray_element;

typedef volatile_carrelt_object *volatile_clause_array;

extern volatile_clause_array global_c_array;


/* Macros and function prototypes. */

void global_carray_free( void );

#endif
