#ifdef IN_MAIN
#define GLOB         /* empty string if included by main program */
#else
#define GLOB extern  /* extern if included by anything else */
#endif

#ifdef BENCHMARK
#define PRIVATE
#endif

#include <stdio.h>
#include <sys/time.h>
#include <sys/resource.h>  

/***************************************************
 *
 *  CONSTANT Declaration
 *
 ***************************************************/

#define BSD /* for SUN and RS6000 */
#define SATO_VERSION "4.1"
#define VERSION_DATE "06/04/2003"
#define MAX_INT  2147483647             /* 32 bit integer */
#define MAX_ATOM (1+Max_atom)           /* can be anything under MAX_INT */
#define MAX_SHORT     65536             /* 16 bit integer */
#define MAX_CHAR        255             /*  8 bit integer */
#define MAX_STACK     40000             /* maximal elements in a stack */
#define MAX_LIST  MAX_STACK             /* maximal elements in a list */
#define MAX_LENGTH     1000             /* maximal literals in a clause */
#define MAX_TRIES       100
#define FF                0             /* false */
#define TT                1             /* true */
#define DC                2             /* Don't-Care value */
#define SAT               3
#define UNSAT             0
#define NPSTOP            0
#define STOP_SUCC         1
#define STOP_PART         2
#define STOP_TIME         3
#define STOP_MEMO         4
#define STOP_ERR          5
#define NEG(v)            ((v)^1)
#define UNDEF             -1

/* the following are clause types */
#define NORM              0
#define EQUL              1
#define LESS              2
#define LSEQ              3
#define GRTR              4
#define GTEQ              5
#define UNEQ              6
#define WEIG              7

#define BUILD_TIME          0
#define SEARCH_TIME         1

#define time_in_second time((long *) NULL)

/****************************************************
 *
 *  MACRO Declaration
 *
 ****************************************************/

#ifdef MORETRACE
#define trace(x,y) if (TRACE>=x) y
#define trace1(x,y) if (TRACE==x || x>8) y
#define check(x,y) if (x) y
#else
#define trace(x,y) 
#define trace1(x,y) 
#define check(x,y) 
#endif

#define get_lit(v,s) ((v)<<1)+(s)
#define lit_var(i) ((i)>>1) 
#define lit_sign(i) ((i)&1) 

#define memory_count_set(x) Memory_count = x
#define memory_count_get() Memory_count/1024.0
/* #define memory_count(x,y) printf("Memory: %d for %s\n", x, y);  Memory_count += (x) */
#define memory_count(x,y) Memory_count += (x)

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
GLOB int *Unit_cls, Unit_cls_idx, Unit_cls_idx_end;
GLOB int Max_atom;
GLOB unsigned int Clause_num0, Clause_num, Subsume_num, NH_num, POS_num, Delete_num, Pure_num;
GLOB unsigned int Unit_num, Bicl_num, Trcl_num;
GLOB int *Value;

GLOB unsigned long Branch_num;
GLOB unsigned long Branch_fail;
GLOB unsigned int Branch_skip, Branch_succ, Branch_open, Branch_jump;
/* During the search:
   Branch_num = 1 + Branch_succ + Branch_fail + Branch_open + Branch_skip + Branch_jump
   At the end of the search:
   Branch_num = Branch_succ + Branch_fail + Branch_open + Branch_skip + Branch_jump
   */

GLOB long Memory_count;   
GLOB long random_seed;
GLOB int Backjumping_down;
GLOB int Stop;

/* Parameters and Flags */
GLOB int ANT;
GLOB int ANTTRACE;
GLOB int BINARY;
GLOB int CHOICE;
GLOB int CHOICE2;
GLOB int DLENGTH;
GLOB int FLAG;
GLOB int GREEDY;
GLOB int GROW;
GLOB int HOURS; 
GLOB int INPUT;
GLOB int INSEARCH;
GLOB int JUMP;
GLOB int LINE;
GLOB int MAX_TAPE;
GLOB int MINVAR; 
GLOB int MINUTES; 
GLOB int Miss_num;
GLOB int MODEL;
GLOB int QCLAUSE;
GLOB int RANJUM;
GLOB int RENAME;
GLOB int RESTART;
GLOB int SELECT;
GLOB int TRACE;
GLOB int Max_cand;
GLOB int RESTRICT;
GLOB int VarOrderFirst;
GLOB int Conflict_cl_level;

/* Application related variables */
GLOB int STAGE;  /* STAGE = 1, 2, 3 */
GLOB int TEAM;   /* number of teams */
GLOB int QAP;    /* actual size of QAP problem */
GLOB int Current_best;  /* The best weight obtained so far */
GLOB int SYMMETRY;  /* 1 if the QAP matrices are symmetric */
GLOB int GROUP;     /* Quasigroup size */

GLOB char *Input_file;
GLOB char *line;

#ifndef TEST
#ifdef MORETRACE
/* debugging data */
GLOB int Model[MAX_LIST];
#endif
GLOB int Old_value[MAX_LIST], OLDV;
#endif
