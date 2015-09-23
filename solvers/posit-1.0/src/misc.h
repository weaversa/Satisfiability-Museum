/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.2 $ */

#ifndef MISC_H
#define MISC_H

/* This function is faster than either memcpy() or bcopy(),
   mainly because it assumes that the memory in question is
   properly aligned. */
void save_state( char *, char *, long );

#endif
