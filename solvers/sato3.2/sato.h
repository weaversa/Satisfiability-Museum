/***************************************************
 *
 *  CONSTANT Declaration
 *
 ***************************************************/

#define MAX_INT  2147483647             /* 32 bit integer */
#define MAX_SHORT     32767             /* 16 bit integer */
#define MAX_CHAR        255             /*  8 bit integer */
#define MAX_ATOM      60000             /* no bigger than MAX_SHORT */
#define MAX_LIST      25000             /* maximal elements in a list */
#define MAX_LENGTH      250             /* maximal literals in a clause */
#define MAX_STACK     10000             /* maximal elements in a stack */
#define MAX_ABG_SIZE    200

#define MAX_TRIES       100

#define FF                0             /* false */
#define TT                1             /* true */
#define DC                2             /* Don't-Care value */
#define SAT               3
#define UNSAT             MAX_ATOM
#define NEG(v)           (v == TT? FF : TT)

#define BUILD_TIME          0
#define SEARCH_TIME         1

#define MAX_SQUARE1 100
#define MAX_SQUARE2 20
#define MAX_SQUARE3 1

#define time_in_second time((long *) NULL)

/****************************************************
 *
 *  MACRO Declaration
 *
 ****************************************************/

#ifdef IN_MAIN
#define GLOB         /* empty string if included by main program */
#else
#define GLOB extern  /* extern if included by anything else */
#endif

#define print_let_x_have \
    if (TRACE == 2) fprintf(Sato_fp, "B%ld.", Branch_num); \
    else if (TRACE > 8 || TRACE == 3 || TRACE == 4)  \
      fprintf(Sato_fp, "[%d]  let x%d have value %d.\n", Branch_open, i, Value[i])

#define print_now_let_x_have \
    if (TRACE == 2) fprintf(Sato_fp, "B%ld.", Branch_num); \
    else if (TRACE > 8 || TRACE == 3 || TRACE == 4)  \
      fprintf(Sato_fp, "    now x%d takes value %d.\n", i, Value[i])

#define print_x_has_to \
    if (TRACE == 2) fprintf(Sato_fp, "."); \
      else if (TRACE > 8 || TRACE == 4)  \
	fprintf(Sato_fp, "      x%d has value %d.\n", i, Value[i])

#define print_x_contradictory \
     if (TRACE > 8 || TRACE == 4) \
	fprintf(Sato_fp, "      x%d has contradictory values.\n", i)

#define print_up_to_x \
    if (TRACE > 8 || TRACE == 4) \
        fprintf(Sato_fp, "      reset x%d's value %d.\n", i, Value[i])

#define print_x_pure \
    if (TRACE > 8 || TRACE == 4) \
      fprintf (Sato_fp, "    x%d is set to %d by pure-literal deletion.\n", \
		 i, Value[i])

#define print_x_subsume \
	  if (TRACE > 6) \
	    fprintf(Sato_fp, "      [C%d] is subsumed by another clause.\n", \
		    Clause_num)

#define print_x_skip \
	if (TRACE > 6) \
	  fprintf(Sato_fp, "    %d in [C%d] is skipped by resolution.\n", \
		  key, Clause_num)

/****************************************
 *
 * Function prototype
 *
 ****************************************/

#include "proto.h"

/***************************************************
 *
 *  VARIBALE Declaration 
 *
 **************************************************/

/* The initials of names of global variables are capitalized. */
GLOB SATOINT Value[ MAX_ATOM ];
GLOB int Old_value[ MAX_LIST ], Old_choice[ MAX_LIST ], OLDV;
GLOB int Max_atom;
GLOB long Max_clause;
GLOB long Printed_clause;
GLOB long Act_max_atom;
GLOB long Clause_num, Subsume_num, NH_num, Unit_num, Bicl_num, Trcl_num;
GLOB int Tmp[MAX_ATOM], Tmp_idx, Tmp_idx_end; 

/* Without this "if", a bug was found when running on SGI:
      sato -Q3 -I4 -C39 -t1 -m10000 -H7
      */
#ifdef IN_MAIN
#define Sato_fp stdout
#else
#ifdef UseP4
GLOB FILE *Sato_fp;  /* Each slave has its own output file. */
#else
#define Sato_fp stdout
#endif
#endif

#ifdef IN_MAIN
FILE *Input_sqs = NULL;
#else 
GLOB FILE *Input_sqs;
#endif

GLOB unsigned long Branch_num;
GLOB unsigned long Branch_fail;
GLOB unsigned int Branch_jump, Branch_skip, Branch_succ, Branch_open, Clause_extra_num;
/* During the search:
   Branch_num = 1 + Branch_succ + Branch_fail + Branch_open + Branch_skip
   At the end of the search:
   Branch_num = Branch_succ + Branch_fail + Branch_open + Branch_skip
   */
GLOB SATOINT Backup[MAX_LIST];
GLOB int Backup_idx;

/* Default Values */
GLOB int CREATE;     /* creating and printing clauses only */
GLOB int TRACE;
GLOB int MODEL;
GLOB int SELECT;
GLOB int DATA;
GLOB int FORMAT;
GLOB int PREP;
GLOB int LINE;
GLOB int IDEMPOTENT;
GLOB int HOURS; 
GLOB int MINUTES; 
GLOB int JUMP;
GLOB int FLAG;
GLOB int GREEDY;
GLOB int RENAME;
GLOB int GROW;
GLOB int OUTPUT;
GLOB int CHOICE1;
GLOB int CHOICE2;
GLOB int INPUT;
GLOB int UIP;
GLOB long random_seed;
GLOB long Memory_count;   
GLOB int Stop;

#ifdef BENCHMARK
GLOB int ZOOM;
GLOB int RAMSEY;
GLOB int NHOLE;
GLOB int OARRAY;
GLOB int PMD;
GLOB int QGROUP;
GLOB int INCOMPLETE;
GLOB int PIGEON;
GLOB int QUEEN;
GLOB int RANDOM;
GLOB int SQUARE2;
GLOB int CYCLIC;
GLOB int MOD;
GLOB int RESTRICT;
GLOB int TEAM;
#endif

#define assign_value(i, val)\
  Value[i] = val;\
  Tmp[Tmp_idx++] = i
