/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.2 $ */

#include <memory.h>
#include <stdio.h>
#include "cnfforms.h"
#include "poly.h"
#include "safemall.h"
#include "statebas.h"

#ifdef THINK_C
#include <size_t.h>
void *memcpy(void *s1, const void *s2, size_t n);
#endif

void clause_append_literal( clause c, literal l, long *sizeptr )
{
  append_to_array( (char **)&(c->members),
                   sizeof(literal_object),
                   &(c->length),
                   sizeptr,
                   (char *)l );     /* Not (char *)&l */
}

/* For very large external formulas, repeatedly doubling the size of
   c->members can lead to an enormous waste of space. */

void clause_delete_wasted_space( clause c, long clause_size )
{
  long c_length = c->length;

  if( c_length < clause_size ) {
    literal_object *old_members, *new_members;

    old_members = c->members;
    new_members =
      (literal_object *)
        safe_malloc( sizeof(literal_object) * (size_t)c_length );
    (void)memcpy( (char *)new_members,
                  (char *)old_members,
                  sizeof(literal_object) * (size_t)c_length );
    safe_free( old_members );
    c->members = new_members;
    /* Clauses do not have a size field. */
  }
}

void litsign_print( literal_sign lsign )
{
  fprintf( stderr, "%s", ((lsign == Pos) ? "Pos" : "Neg") );
}

void tval_print( truth_value tval )
{
  fprintf( stderr,
           "%s",
           ((tval == True) ? "T" : ((tval == False) ? "F" : "I")) );
}

void literal_print( literal l )
{
  if( l->sign == Pos )
    fprintf( stderr, "Pos " );
  else
    fprintf( stderr, "Neg " );
  fprintf( stderr, "%s", the_prop_list->props[l->p_index] );
}
