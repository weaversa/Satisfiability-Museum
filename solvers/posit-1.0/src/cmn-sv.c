/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.3 $ */

#include <stdlib.h>
#include <memory.h>
#include <stdio.h>
#include "cnfforms.h"
#include "cmn-carr.h"
#include "cmn-parr.h"
#include "safemall.h"
#include "cmn-sv.h"

#ifdef THINK_C
#include <size_t.h>
void *memcpy(void *s1, const void *s2, size_t n);
#endif


/* To reduce memory fragmentation, recopy all of the clauses into a
   single block of memory.  Add sentinels at the end of each clause,
   too. */

static void construct_ccarrelt_csets( void )
{
  long i, total_length, current_length;
  literal current_lit;

  total_length = 0;
  for( i=0; i<the_clause_count; i++ )
    total_length += the_formula->clauses[i].length;

  current_lit =
    (literal_object *)
      safe_malloc
        ( (size_t)(total_length + the_clause_count) *
          sizeof(literal_object) );

  for( i=0; i<the_clause_count; i++ ) {
    current_length = the_formula->clauses[i].length;
    common_c_array[i].length = current_length;
    common_c_array[i].cset = current_lit;
    (void)memcpy( (char *)current_lit,
                  (char *)(the_formula->clauses[i].members),
                  (size_t)current_length * sizeof(literal_object) );
    current_lit += current_length;
    current_lit->p_index = -99;
    current_lit++;
    safe_free( the_formula->clauses[i].members );
  }
}

void common_sv_make( void )
{
  long i, j;
  common_carray_element ccarrelt;
  long ccarrelt_length;
  common_parray_element cparrelt;
  literal current_lit;

  /* 1. Initialize common_p_array. */

  cparrelt =
    common_p_array =
      (common_prop_array)
        safe_malloc( (size_t)the_prop_count *
                     sizeof(common_parrelt_object) );

  for( i=0; i<the_prop_count; i++, cparrelt++ ) {
    cparrelt->prop = the_prop_list->props[i];

    cparrelt->occurinfo[Pos].length = 0;
    cparrelt->occurinfo[Pos].size = 4;
    cparrelt->occurinfo[Pos].members =
      (long *)safe_malloc( 4 * sizeof(long) );

    cparrelt->occurinfo[Neg].length = 0;
    cparrelt->occurinfo[Neg].size = 4;
    cparrelt->occurinfo[Neg].members =
      (long *)safe_malloc( 4 * sizeof(long) );
  }

  /* 2.  Initialize common_c_array and construct
     common_p_array[*].occurinfo[{Pos,Neg}]. */

  ccarrelt =
    common_c_array =
      (common_clause_array)
        safe_malloc( (size_t)the_clause_count *
                     sizeof(common_carrelt_object) );

  construct_ccarrelt_csets();

  for( i=0; i<the_clause_count; i++, ccarrelt++ ) {
    ccarrelt_length = the_formula->clauses[i].length;

    for( j = 0, current_lit = ccarrelt->cset;
         j < ccarrelt_length;
         j++, current_lit++ )
      cindices_append_cindex
        ( &(common_p_array[current_lit->p_index].
            occurinfo[current_lit->sign]),
          i );
  }

  safe_free( the_formula->clauses );
  safe_free( the_formula );

  /* 3.  Delete wasted space in common_p_array[*].occurinfo[{Pos,Neg}]. */

  for( i = 0, cparrelt = common_p_array;
       i < the_prop_count;
       i++, cparrelt++ ) {

    /* Add sentinels at the end of cparrelt->occurinfo[{Pos,Neg}]. */

    cindices_append_cindex( &(cparrelt->occurinfo[Pos]), -99 );
    cparrelt->occurinfo[Pos].length--;
    cindices_append_cindex( &(cparrelt->occurinfo[Neg]), -99 );
    cparrelt->occurinfo[Neg].length--;

    /* cindices_delete_wasted_space( &(cparrelt->occurinfo[Pos]) ); */
    /* cindices_delete_wasted_space( &(cparrelt->occurinfo[Neg]) ); */
  }
}

void common_sv_free( void )
{
  common_carray_free();
  common_parray_free();
}
