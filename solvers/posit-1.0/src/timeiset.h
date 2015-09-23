/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.3 $ */

#ifndef TIME_ISET_H
#define TIME_ISET_H

/* Finite sets with indexed elements, where the range of the possible
   indices is known in advance. */

/* This implementation is faster but consumes more space. */

#define TISET_NOVALUE -99

typedef struct {
  long *dense_array;    /* The index in sparse_array, i.e., the element */
  long *sparse_array;   /* The index in dense_array, or TISET_NOVALUE */
  long length;          /* The actual number of elements in the set */
  long limit;           /* The elements can range from 0 to limit - 1 */
} time_index_set_object, *time_index_set;


/* Macros and function prototypes. */

time_index_set tiset_emptyset( long );

#define tiset_cardinality(x) ((x)->length)

#define tiset_size(x) ((x)->limit)

#define tiset_isempty(x) ((x)->length == 0)

#define tiset_notempty(x) ((x)->length)

#define tiset_members(x) ((x)->dense_array)

#define tiset_member(x,y) ((x)->sparse_array[(y)] != TISET_NOVALUE)

#define tiset_nonmember(x,y) ((x)->sparse_array[(y)] == TISET_NOVALUE)

/* This will cause a segmentation fault if the set is empty. */
#define tiset_choose(x) ((x)->dense_array[random_long((x)->length)])
#define tiset_fast_choose(x) ((x)->dense_array[fast_random_long((x)->length)])

void tiset_copy( time_index_set, time_index_set );

void tiset_adjoin( time_index_set, long );

/* Assumption:  elt is not already in the set. */

#define tiset_unsafe_adjoin( TISET, ELT ) do { \
    (TISET)->sparse_array[(ELT)] = (TISET)->length; \
    (TISET)->dense_array[(TISET)->length] = (ELT); \
    (TISET)->length++; \
  } while( 0 )

void tiset_delete( time_index_set, long );

void tiset_union( time_index_set, time_index_set );

void tiset_difference( time_index_set, time_index_set );

void tiset_print( time_index_set );

void tiset_delete_all( time_index_set );

void tiset_double_size( time_index_set );

void tiset_free( time_index_set );

#endif
