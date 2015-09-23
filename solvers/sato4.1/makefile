# CFLAGS for "make":
# -pg can be used by gprof
# -g can be used by gdb
CFLAGS = -O3 -DQUASICLAUSE

# choose your C compiler.
CC = cc
CC = gcc

.SUFFIXES:	.o .c .f .h

#---------------------- user defined files
SATONFIL = main.c sato.c util.c

SATONOBJ = main.o sato.o util.o

#---------------------- make binary code
lean: $(SATONOBJ)
	$(CC) $(CFLAGS) $(SATONOBJ) -lc -o sato
	chmod a+x sato

$(SATONOBJ): main.h

sato.o: sato.h weight.h tape.h weight.h stack.h select.h santo.h

util.o main.o: clocks.h

