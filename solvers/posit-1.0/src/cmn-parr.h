/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.4 $ */

#ifndef COMMON_PARRAY_H
#define COMMON_PARRAY_H

#include "prims.h"
#include "cmn-carr.h"

/* Expandable arrays of clause indices. */

typedef struct {
  long *members;
  long length;
  long size;
  /* This component is not strictly necessary, but it makes
     the code slightly faster. */
  common_carray_element *common_pointers;
} c_indices_object, *c_indices;

/* The common components of the proposition array. */

typedef struct {
  /* Occurrence information for positive and negative literals is
     stored in occurinfo[0] and occurinfo[1], respectively. */
  c_indices_object occurinfo[2];
  proposition prop;
} common_parrelt_object, *common_parray_element;

typedef common_parrelt_object *common_prop_array;


/* The positive and negative occurrences of each proposition.
   A redundant array, used for efficiency in the search algorithm. */
typedef long **common_literal_members;


extern common_prop_array common_p_array;
extern common_literal_members common_l_members;


/* Macros and function prototypes. */

void cindices_append_cindex( c_indices, long );

void cindices_delete_wasted_space( c_indices );

void cindices_free( c_indices );

void common_parray_free( void );

#endif
