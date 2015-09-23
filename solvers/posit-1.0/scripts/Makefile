# The Makefile for analyze-stats, which takes a text file of tree sizes
# and CPU times from POSIT and computes mean, standard deviation, etc.

CC = gcc
LIBS = -lm
RM = rm -f

CFLAGS = -O2 # -Wall
OFILES = analyze-stats.o

.c.o:
	$(CC) $(CFLAGS) -c $<

all: analyze-stats

analyze-stats: $(OFILES)
	$(CC) $(CFLAGS) -o $@ $(OFILES) $(LIBS)

clean:
	$(RM) $(OFILES)

realclean: clean
	$(RM) analyze-stats
