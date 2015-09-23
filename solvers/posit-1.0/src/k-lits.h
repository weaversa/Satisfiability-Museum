/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.2 $ */

#ifndef K_LITERALS_H
#define K_LITERALS_H

/* Apply a restricted form of the Davis-Putnam variable elimination
   rule to the raw formula:  eliminate all propositions p such that
   one of the literals associated with p occurs exactly once or
   exactly twice. */

#include "statebas.h"

truth_value simplify_formula( void );

#endif
