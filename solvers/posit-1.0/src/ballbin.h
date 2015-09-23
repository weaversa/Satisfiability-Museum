/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.2 $ */

#ifndef BALLS_IN_BINS_H
#define BALLS_IN_BINS_H

/* Is it possible to put x balls in y bins, where each bin holds
   exactly one ball?  When x = y + 1, the search tree always
   contains O(y!) dead ends, which is obviously not good. */

void balls_in_bins( long, long );

#endif
