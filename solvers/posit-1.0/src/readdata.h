/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.2 $ */

#ifndef READ_DATA_H
#define READ_DATA_H

#define LINEMAX 80

/* Reading in numbers from stdin in a very robust fashion. */

long read_long( char *, long, int );

double read_double( char *, double, int );

char *read_string( char * );

#endif
