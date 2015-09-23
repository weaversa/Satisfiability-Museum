/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.2 $ */

#include <math.h>
#include <memory.h>
#include <stdio.h>
#include <string.h>
#include "poly.h"
#include "safemall.h"
#include "cnfforms.h"

#ifdef THINK_C
void *memcpy(void *s1, const void *s2, size_t n);
#endif

long the_prop_count;
long the_clause_count;
long the_longest_clause_length;

prop_list the_prop_list;

formula the_formula;


/* Calculate the number of digits in a non-negative integer.  I've
   seen people get this wrong in commercial code; the answer is NOT
   the ceiling of the log! */

/* Casting the result of log10() implicitly computes its floor. */

size_t digits_in_long( long l )
{
  return( 1 + (size_t)log10(l ? (double)l : 1.0) );
}

prop_list proplist_empty( long limit )
{
  prop_list result;

  result = (prop_list)safe_malloc( sizeof(prop_list_object) );
  result->length = 0;
  result->size = limit;
  result->props =
    (proposition *)
      safe_malloc( sizeof(proposition) * (size_t)limit );
  return result;
}

void proplist_append_prop( prop_list pl, proposition prop )
{
  append_to_array( (char **)&(pl->props),
                   sizeof(proposition),
                   &(pl->length),
                   &(pl->size),
                   (char *)&prop );
}

void proplist_free( prop_list pl )
{
  long i, pl_length;

  pl_length = pl->length;
  for( i=0; i<pl_length; i++ )
    safe_free( pl->props[i] );
  safe_free( pl->props );
  safe_free( pl );
}

formula formula_empty( long limit )
{
  formula result;

  result = (formula)safe_malloc( sizeof(formula_object) );
  result->length = 0;
  result->size = limit;
  result->clauses =
    (clause_object *)
      safe_malloc( sizeof(clause_object) * (size_t)limit );
  return result;
}

void formula_append_clause( formula f, clause c )
{
  append_to_array( (char **)&(f->clauses),
                   sizeof(clause_object),
                   &(f->length),
                   &(f->size),
                   (char *)c );      /* Not (char *)&c */
}

/* Repeatedly doubling the size of f->clauses can lead to an
   enormous waste of space for very large formulas. */

void formula_delete_wasted_space( formula f )
{
  long f_length = f->length;

  if( (double)f_length / f->size < 0.95 ) {
    clause_object *old_clauses, *new_clauses;

    old_clauses = f->clauses;
    new_clauses =
      (clause_object *)
        safe_malloc( sizeof(clause_object) * (size_t)f_length );
    (void)memcpy( (char *)new_clauses,
                  (char *)old_clauses,
                  sizeof(clause_object) * (size_t)f_length );
    safe_free( old_clauses );
    f->clauses = new_clauses;
    f->size = f_length;
  }
}

void formula_free( formula f )
{
  return;
}
