# Environment variables for POSIT.

# Which problem to solve.  Choose one of the following:  "nqueens",
# "mitchellksat", "graphcoloring", "mnregular", "ballsinbins",
# "stdin", or "file".  No default.

# setenv POSIT_PROBLEM_CHOICE nqueens

# Whether to echo internally generated problems to stderr.
# The default is not to echo them.

# setenv POSIT_ECHO_INTERNAL_PROBLEMS

# Whether to generate machine-readable output.  The default is
# not to.

# setenv POSIT_MACHINE_READABLE_OUTPUT

# The initial seed for the random number generator, which can be
# any number other than zero.  Zero or no value sets it to the sum
# of the process's ID number and the number of seconds since
# January 1, 1970.

# setenv POSIT_RANDOM_SEED 123456

# The number of trials to run (useful for randomly generated problems).
# The default is 1.

# setenv POSIT_NUMBER_OF_TRIALS 5

# The following environment variables are problem-specific.  None
# of them have default values.

# 1.  Environment variables for random K-SAT problems (Mitchell et al.).

# setenv POSIT_RANDOMKSAT_PROPCOUNT 10
# setenv POSIT_RANDOMKSAT_CLAUSECOUNT 49
# setenv POSIT_RANDOMKSAT_CLAUSELENGTH 3

# 2.  Environment variables for M-N-regular random K-SAT problems
# (Pehoushek).  The sum of the first two numbers, times the third,
# must be evenly divisible by the fourth.

# setenv POSIT_MNREGULAR_POSOCCURRENCES 5
# setenv POSIT_MNREGULAR_NEGOCCURRENCES 5
# setenv POSIT_MNREGULAR_PROPCOUNT 9
# setenv POSIT_MNREGULAR_CLAUSELENGTH 3

# 3.  Environment variables for random graph-coloring problems.

# setenv POSIT_GRAPHCOLOR_VERTEXCOUNT 10
# setenv POSIT_GRAPHCOLOR_EDGE_PROB 0.5
# setenv POSIT_GRAPHCOLOR_COLORCOUNT 4

# 4.  Environment variables for N-queens problems.

# setenv POSIT_NQUEENS_QUEENCOUNT 8

# 5.  Environment variables for balls in bins problems, a.k.a.
# pigeonhole problems.

# setenv POSIT_BALLSINBINS_BALLCOUNT 7
# setenv POSIT_BALLSINBINS_BINCOUNT 8
