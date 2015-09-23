# The Makefile for POSIT.

# On a Sun, clcc generates faster code than gcc, which generates faster
# code than acc.  Note that clcc requires the -ansi flag in order to
# recognize "signed char".
CC = gcc # clcc # acc
CFLAGS = -O3 -Wall # -O3 -ansi # -g -pg

# On an RS6000, cc generates faster code than gcc.
# CC = cc
# CFLAGS = -O3 # -g -pg

# Purify and Quantify.  Choose at most one.
ANALYZE = # quantify # purify
STATIC = # -static   # For Quantify only.

# Where should the executable be placed?
POSIT = ./posit

# Choose one or more of the following "-D" symbols:
#
# USE_HEURISTICS turns on whatever heuristic(s) I'm currently
#    using.  Turning this off is only useful for debugging.
# FAILED_LITS makes the heuristics check for failed literals when it
#    is possible to do so.  It implies USE_HEURISTICS.
# SIMPLIFY_FIRST performs singleton and doubleton deletion before
#    the backtracking search begins.
# RANDOMIZE makes POSIT's behavior non-deterministic.  It's needed
#    for running multiple copies of POSIT on the same problem.
#
# MAX_DEPTH prints out the maximum depth of the backtracking stack.
#    This is useful for estimating the amount of time you will
#    probably need to solve the current problem.
# PROGRESS_REPORT prints out a little message when the size of
#    the remaining (sub)problem has decreased by half.  This is
#    useful for estimating the total running time of a very hard
#    problem, i.e., "It isn't even halfway done yet!".
# DEBUG turns on little sanity checks throughout the code that
#    increase the running time somewhat.
# SUNOS is needed for compiling on SunOS, the OS with non-ANSI include
#    files.
# THINK_C is needed for compiling with Think C (on the Macintosh).
#
# I recommend that the first three symbols be defined.

SYMBOLS = -DUSE_HEURISTICS \
          -DFAILED_LITS \
          -DSIMPLIFY_FIRST \
          -DRANDOMIZE
          # -DDEBUG
          # -DGRAND_STATS
          # -DMAX_DEPTH
          # -DSUNOS
          # -DPROGRESS_REPORT
          # -DTHINK_C

# Nothing below this line needs to be modified.

VERSION = 1.0
LIBS = -lm
RM = rm -f
LINT = /opt/bin/lclint
LINTFLAGS = $(SYMBOLS) +boolname truth_value

OFILES = bt-stack.o \
         dynamic.o \
         gbl-sv.o \
         heur2.o \
         heurs.o \
         misc.o \
         timeiset.o \
         ballbin.o \
         cnfforms.o \
         cmn-carr.o \
         cmn-flgs.o \
         cmn-parr.o \
         cmn-sv.o \
         dmcs-cnf.o \
         dmcs-sat.o \
         dimacs.o \
         dynstats.o \
         gbl-carr.o \
         gbl-parr.o \
         good-rnd.o \
         graphclr.o \
         heur1.o \
         k-lits.o \
         la-stack.o \
         m-n-reg.o \
         main.o \
         n-queens.o \
         poly.o \
         rnd-ksat.o \
         readdata.o \
         safemall.o \
         smallarr.o \
         statebas.o \
         statevec.o

SFILES = $(OFILES:%.o=%.c)


.c.o:
	$(CC) $(CFLAGS) $(SYMBOLS) -c $<

all: posit

posit: $(OFILES)
	$(RM) $(POSIT)
	$(ANALYZE) $(CC) $(CFLAGS) -o $(POSIT) $(STATIC) $(OFILES) $(LIBS)

dist:
	(cd ..; \
    tar cvf /tmp/posit-$(VERSION).tar README src/ROAD_MAP src/Makefile \
            src/*.h src/*.c \
            doc/posit.1 doc/posit.cshrc doc/sample.cnf doc/sample.sat \
            doc/satformat.tex doc/zebra.c doc/zebra.cnf \
            scripts/Makefile scripts/analyze-stats.c scripts/batch-posit3 \
            scripts/batch-posit4 scripts/batch-posit5 scripts/compare-posits)

lint:
	$(RM) pass1_errs
	$(LINT) $(LINTFLAGS) $(SFILES) 2> pass1_errs

clean:
	$(RM) $(OFILES) pass1_errs

realclean: clean
	$(RM) $(POSIT)
