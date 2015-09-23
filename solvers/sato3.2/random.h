#include <limits.h>

#define TISET_NOVALUE -99

typedef struct {
  long *dense_array;    /* The index in sparse_array, i.e., the element */
  long *sparse_array;   /* The index in dense_array, or TISET_NOVALUE */
  long length;          /* The actual number of elements in the set */
  long limit;           /* The elements can range from 0 to limit - 1 */
} time_index_set_object, *time_index_set;

/* Returns a long integer in the range [0, x-1]. */
#define random_long(x) ((long)(good_random() % x))

/* For ensuring that no clause contains more than one literal
   associated with the same proposition. */
time_index_set existing_props;

/* Macros and function prototypes. */
time_index_set tiset_emptyset();

#define tiset_cardinality(x) ((x)->length)

#define tiset_size(x) ((x)->limit)

#define tiset_isempty(x) ((x)->length == 0)

#define tiset_notempty(x) ((x)->length)

#define tiset_members(x) ((x)->dense_array)

#define tiset_member(x,y) ((x)->sparse_array[(y)] != TISET_NOVALUE)

#define tiset_nonmember(x,y) ((x)->sparse_array[(y)] == TISET_NOVALUE)

/* This will cause a segmentation fault if the set is empty. */
#define tiset_choose(x) ((x)->dense_array[random_long((x)->length)])

/* Assumption:  elt is not already in the set. */

#define tiset_unsafe_adjoin( TISET, ELT ) do { \
    (TISET)->sparse_array[(ELT)] = (TISET)->length; \
    (TISET)->dense_array[(TISET)->length] = (ELT); \
    (TISET)->length++; \
  } while( 0 )

