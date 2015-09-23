/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.2 $ */

#ifndef DYNAMIC_STATS_H
#define DYNAMIC_STATS_H

/* Accumulating statistics about the search process, and printing
   those statistics out. */

typedef struct {
  long nodes;              /* # of non-leaf nodes in the search tree */
  long solution_count;     /* Number of solutions (0 or 1) */
  double cpu_time;         /* CPU time in seconds */
} dynamic_stats_object, *dynamic_stats;

extern dynamic_stats the_dynamic_stats;


/* Macros and function prototypes. */

void global_status_report( dynamic_stats );

#endif
