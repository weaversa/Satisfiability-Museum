/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.2 $ */

#ifndef DIMACS_CNF_H
#define DIMACS_CNF_H

#include "statebas.h"

extern int empty_clause;

void get_cnf_formula( long, long );

void clause_print_cnf( clause, int );

void formula_print_cnf( int );

#endif
