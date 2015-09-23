/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.2 $ */

#ifndef COMMON_CARRAY_H
#define COMMON_CARRAY_H

/* The common components of the clause array. */

struct literal_object;      /* To avoid recursive #include's. */

typedef struct {
  struct literal_object *cset;
  long length;
} common_carrelt_object, *common_carray_element;

typedef common_carrelt_object *common_clause_array;

extern common_clause_array common_c_array;


/* Macros and function prototypes. */

void common_carray_free( void );

#endif
