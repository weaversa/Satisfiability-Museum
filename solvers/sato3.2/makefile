# Cflag for HPs: 
CFLAGS = -O -DHP_UX -DMORETRACE -DBENCHMARK

# CFLAGS for "make lean":
CFLAGS = -g -DMORETRACE
CFLAGS = -O 
CFLAGS = -O3

# CFLAGS for "make full":
CFLAGS = -g -DMORETRACE -DBENCHMARK
CFLAGS = -O -DBENCHMARK -DMORETRACE

CFLAGS = -O3 -DMORETRACE -DBENCHMARK -m32
# choose your C compiler.
CC = cc
CC = gcc

.SUFFIXES:	.o .c .f .h

#---------------------- user defined files
SATOFIL = main.c sato.c trie.c list.c clocks.c clause.c greedy.c

SATOOBJ = main.o sato.o trie.o list.o clocks.o clause.o greedy.o

BENCHFIL = bench.c qgroup.c cgroup.c ngroup.c square.c oarray.c pmd.c random.c

BENCHOBJ = bench.o qgroup.o cgroup.o ngroup.o square.o oarray.o pmd.o random.o

#---------------------- make binary code
full: $(SATOOBJ) $(BENCHOBJ)
	$(CC) $(CFLAGS) $(SATOOBJ) $(BENCHOBJ) -lc -o sato
	chmod a+x sato

lean: $(SATOOBJ)
	$(CC) $(CFLAGS) $(SATOOBJ) -lc -o sato
	chmod a+x sato

$(BENCHOBJ) $(SATOOBJ): main.h

$(BENCHOBJ) $(SATOOBJ): sato.h

list.o: list.h

trie.o: trie.h trie0.h trie2.h trie3.h trie4.h slot.h weight.h stack.h

random.o: random.h

clocks.o sato.o: clocks.h
