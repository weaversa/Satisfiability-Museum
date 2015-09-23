/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.3 $ */

#include <stdio.h>
#include <memory.h>
#include "cnfforms.h"
#include "dynamic.h"
#include "gbl-carr.h"
#include "heurs.h"
#include "misc.h"
#include "safemall.h"
#include "bt-stack.h"

#ifdef THINK_C
#include <size_t.h>
void *memcpy(void *s1, const void *s2, size_t n);
#endif

long *lindex_stack;
volatile_prop_array *prop_array_stack;
long *valued_prop_stack;
unsigned char **binary_info_stack;

long top_of_bt_stack;

long prop_array_size;
long lit_array_size;
long clause_array_size;
long total_array_size;
volatile_prop_array temp_p_array;

static unsigned char *temp_binary_info;


void btstack_emptystack( void )
{
  long i;

  top_of_bt_stack = -1;

  lindex_stack =
    (long *)safe_malloc( (size_t)the_prop_count * sizeof(long) );
  prop_array_stack =
    (volatile_prop_array *)
      safe_malloc( (size_t)the_prop_count * sizeof(volatile_prop_array) );
  valued_prop_stack =
    (long *)safe_malloc( (size_t)the_prop_count * sizeof(long) );
  binary_info_stack =
    (unsigned char **)
      safe_malloc( (size_t)the_prop_count * sizeof(unsigned char *) );

  for( i=0; i<the_prop_count; i++ )
    prop_array_stack[i] = NULL;
}

void btstack_push( void )
{
  top_of_bt_stack++;

  lindex_stack[top_of_bt_stack] = dynamic_current_lindex;
  valued_prop_stack[top_of_bt_stack] = dynamic_valued_props;

  if( prop_array_stack[top_of_bt_stack] == NULL ) {
#ifdef MAX_DEPTH
    fprintf( stderr, "%ld ", top_of_bt_stack + 1 );
#endif /* MAX_DEPTH */
    prop_array_stack[top_of_bt_stack] =
      (volatile_prop_array)safe_malloc( (size_t)total_array_size );
    binary_info_stack[top_of_bt_stack] =
      (unsigned char *)safe_malloc( (size_t)lit_array_size );
  }

  save_state( (char *)prop_array_stack[top_of_bt_stack],
              (char *)global_p_array,
              (size_t)total_array_size );
  save_state( (char *)binary_info_stack[top_of_bt_stack],
              (char *)binary_clause_info,
              (size_t)lit_array_size );
}

void btstack_restore( void )
{
  dynamic_current_lindex = lindex_stack[top_of_bt_stack];
  dynamic_valued_props = valued_prop_stack[top_of_bt_stack];

  /* Swap global_p_array and prop_array_stack[top_of_bt_stack]. */
  temp_p_array = global_p_array;
  global_p_array = prop_array_stack[top_of_bt_stack];
  prop_array_stack[top_of_bt_stack] = temp_p_array;

  /* Restore global_c_array. */
  global_c_array =
    (volatile_clause_array)((char *)global_p_array + prop_array_size);

  /* Swap binary_clause_info and binary_info_stack[top_of_bt_stack]. */
  temp_binary_info = binary_clause_info;
  binary_clause_info = binary_info_stack[top_of_bt_stack];
  binary_info_stack[top_of_bt_stack] = temp_binary_info;
}

void btstack_free( void )
{
  long i;

  i = 0;
  while( i < the_prop_count ) {
    if( prop_array_stack[i] == NULL )
      break;
    safe_free( prop_array_stack[i] );
    safe_free( binary_info_stack[i] );
    i++;
  }
  safe_free( lindex_stack );
  safe_free( prop_array_stack );
  safe_free( valued_prop_stack );
  safe_free( binary_info_stack );
}
