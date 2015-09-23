/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.2 $ */

#ifndef MAIN_H
#define MAIN_H

typedef enum { None=0, MitchellKSAT=1, MNRegular=2,
               GraphColoring=3, NQueens=4, BallsInBins=5,
               FromStdin=6, FromFile=7 }
problem_type;

/* The type of problem to solve. */

extern problem_type problem_choice;

/* Whether or not the output should be machine-readable. */

extern int machine_readable;

#endif
