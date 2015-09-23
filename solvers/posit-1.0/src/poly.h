/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.2 $ */

#ifndef POLYMORPHIC_H
#define POLYMORPHIC_H

#ifdef THINK_C
#include "size_t.h"
#else
#include <stdlib.h>  /* To get size_t */
#endif

/* Let's hear it for polymorphism in C.  Yay. */

void append_to_array( char **,     /* Base of array */
                      size_t,      /* Width of each element */
                      long *,      /* Number of actual elements */
                      long *,      /* Number of possible elements */
                      char * );    /* Element to append */

#endif
