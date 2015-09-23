/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.2 $ */

#ifndef SMALL_ARRAY_H
#define SMALL_ARRAY_H

/* Small arrays that hold entries sorted in decreasing order
   with respect to a given cost. */

typedef struct {
  long *members;
  long *costs;
  long length;
  long size;
  long max_cost;
  long min_cost;
  long *real_members;
  long *real_costs;
  long offset;
} small_array_object, *small_array;


/* Macros and function prototypes. */

small_array sarray_empty( long );

#define sarray_cardinality(x) ((x)->length)

#define sarray_isempty(x) ((x)->length == 0)

#define sarray_members(x) ((x)->members)

#define sarray_resize(x, y) ((x)->size = (y))

#define sarray_delete_all(x) do { \
    (x)->length = 0; \
    (x)->members = (x)->real_members + (x)->offset; \
    (x)->costs = (x)->real_costs + (x)->offset; \
  } while( 0 )

void sarray_print( small_array );

void sarray_free( small_array );

#endif
