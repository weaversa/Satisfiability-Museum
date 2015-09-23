/*********************************************************************
; Copyright 1992-2000, The University of Iowa (UI).  All rights reserved. 
; By using this software the USER indicates that he or she has read, 
; understood and will comply with the following:
;
; --- UI hereby grants USER nonexclusive permission to use, copy and/or
; modify this software for internal, noncommercial, research purposes only.
; Any distribution, including commercial sale or license, of this software,
; copies of the software, its associated documentation and/or modifications
; of either is strictly prohibited without the prior consent of UI.  Title
; to copyright to this software and its associated documentation shall at
; all times remain with UI.  Appropriate copyright notice shall be placed
; on all software copies, and a complete copy of this notice shall be
; included in all copies of the associated documentation.  No right is
; granted to use in advertising, publicity or otherwise any trademark,
; service mark, or the name of UI.  Software and/or its associated
; documentation identified as "confidential," if any, will be protected
; from unauthorized use/disclosure with the same degree of care USER
; regularly employs to safeguard its own such information.
;
; --- This software and any associated documentation is provided "as is," and
; UI MAKES NO REPRESENTATIONS OR WARRANTIES, EXPRESS OR IMPLIED, INCLUDING
; THOSE OF MERCHANTABILITY OR FITNESS FOR A PARTICULAR PURPOSE, OR THAT
; USE OF THE SOFTWARE, MODIFICATIONS, OR ASSOCIATED DOCUMENTATION WILL
; NOT INFRINGE ANY PATENTS, COPYRIGHTS, TRADEMARKS OR OTHER INTELLECTUAL
; PROPERTY RIGHTS OF A THIRD PARTY.  UI, the University of Iowa,
; its Regents, officers, and employees shall not be liable under any
; circumstances for any direct, indirect, special, incidental, or
; consequential damages with respect to any claim by USER or any third
; party on account of or arising from the use, or inability to use, this
; software or its associated documentation, even if UI has been advised
; of the possibility of those damages.
*********************************************************************/
#define IN_MAIN
#define SATO_VERSION "3.2.1"
#define VERSION_DATE "04/2000"
#include "main.h"

/* Global variables */
char *fname_out = NULL;

FILE *command_line_check ();

/*************
 *
 *   main()
 *
 *************/

main(argc, argv)
     int argc;
     char **argv;
{
  FILE *fin;
  FILE *efile;
  int res;

  if ( argc == 1 ) print_menu();

  fin = command_line_check( argc, argv, &efile );

  if (DATA == 1)
    list_init_once_forall();
  else
    trie_init_once_forall();

  read_one_problem(1, efile);
  res = sato(fin); 
  if (efile != NULL || res == 2) {
    read_one_problem(0, efile);
    if (HOURS || MINUTES) append_cmd_line(argc, argv);
  }
  if (OUTPUT < 2) print_command(Sato_fp, 1, argc, argv);
  return (Branch_succ > 0)? 1 : 0;
}

void p_banner(argc, argv)
     int argc;
     char *argv[];
{
  char host[64];

  if (gethostname(host, 64) != 0) str_copy("???", host);
  printf("------- SATO %s, %s on %s ------\n", 
	 SATO_VERSION, VERSION_DATE, host);
  print_command(stdout, 0, argc, argv);
  printf("\n");
}  /* print_banner */

void print_menu()
{
  printf("Usage: sato [<Options>] <Input_file>\n\n");
  printf("Options are:\n");
  printf("   -e fname : give the file name of unfinished jobs\n\n");
  printf("   -f<n>    : use the DIMACS or Lisp format\n");
  printf("   -g<n>    : set the length of created clauses to be saved\n");
  printf("   -h<n>    : set the number of hours to be run (default: 23)\n");
  printf("   -m<n>    : set the number of minutes to be run (default: 0)\n");
  printf("   +m<n>    : set the number of expected models (default: 1)\n");
  printf("   -n       : rename variable names to make name space compact\n");
  printf("   -o<n>    : print out clauses (0 <= n <= 5)\n");
  printf("   -p       : do not preprocess (i.e., sort) input clauses\n");

/*
  printf("   -s<n>    : select an atom in clauses for branching:\n");
  printf("               n = 0: the atom with the minimal index;\n");
  printf("               n = 1: an atom in a shortest positive clause (default);\n");
  printf("               n = 2: a variant of n = 1;\n");
  printf("               n = 3: an atom with most occurrences;\n");
  printf("               n = 4: an atom with most occurrences in binary clauses;\n");
  printf("               n = 5: an atom with most Jeroslow-Wang weight.\n");
*/

#ifdef MORETRACE
  printf("   -t<n>    : set the trace level (2-4: search; 5-8: build; 9: all)\n\n");
#else
  printf("   -t  >    : do not print models\n\n");
#endif

#ifdef BENCHMARK
  printf("For the full version, the following benchmark problems are provided:\n");
  printf("   -A<n>    : Random k-sat problems (-K<k>, n atoms, -C<c> clauses)\n");
  printf("   -P<n>    : Pigeonhole problems (n holes, n+1 pigeons)\n");
  printf("   -Q<n>    : Queen problems (n queens on n by n board)\n");
  printf("   -R<n>    : Ramsey numbers r(p, q) = n with -P<p> and -Q<q>\n");
  printf("   -G<n>    : Quasigroup problems: QGm(n), m from -Q<m>\n");
  printf("   -B<n>    : Cyclic method for quasigroups QGm(h^g, i), where:\n");
  printf("   -C<n>    :   n=hg+k, m from -Q<m>, h from -H<h>, i from -I<i>\n");
  printf("   -K<k>    : k-PMD(h^g, i) problems, h, g, i, as above\n");
  printf("   -O<k>    : k-MOLS(h^g, i) problems, h, g, i, as above\n\n");
#endif

  printf("Input_file is either `-' (denotes the standard input) or a \n");
  printf("    file name. The input consists of a list of clauses, each of\n");
  printf("    which is a list of nonzero integers separated 0 (DIMACS Format,\n");
  printf("    default), or surrounded by parentheses (Lisp Format, -f1).\n\n");
  printf("    Example: To input clauses p1|p2, -p1|p3|p4, and p2|-p3|p4 in\n");
  printf("       DIMACS Format              Lisp Format\n");
  printf("       1 2 0                      (1 2)\n");
  printf("       -1 3 4 0                   (-1 3 4)\n");
  printf("       2 -3 4 0                   (2 -3 4)\n\n");
  printf("    Tautologies and duplicated literals are always removed.\n");
  printf("    E.g., (1 1 -2 -4) is the same as (1 -2 -4).\n\n");
  printf("    `-f' for the DIMACS format and `-f1' for the lisp format.\n\n");

  printf("The option -o<n> is useful if you use sato as a propositional clause\n");
  printf("generator, or as a preprocessor and can be combined with -n.\n");
  printf("The six cases of n are: \n\n");

  printf("   -o:   print out all, excluding simplifed by trie, in Lisp Format\n");
  printf("   -o1:  print out all, excluding subsumed, in Lisp Format\n");
  printf("   -o2:  print out all the clauses in Lisp Format\n");
  printf("   -o3:  print out all, excluding simplifed by trie, in DIMACS Format\n");
  printf("   -o4:  print out all, excluding subsumed, in DIMCS Format\n");
  printf("   -o5:  print out all the clauses in DIMCS Format\n\n");

  printf("The option -g<n> was new in sato3.x.  This option affects\n");
  printf("the performance of sato dramatically.  At each failed branch\n");
  printf("in the Davis-Putnam algorithm, sato tries to identify the source\n");
  printf("of the failure and create a new clause.  The number `n' is\n");
  printf("the maximal length of the created clauses to be saved.\n");
  printf("For the current release, the default value is 20.\n");
  printf("For certain problems, a large `n' improves the performance;\n");
  printf("for other problems, a large `n' deteriorates the performance\n");
  printf("(because it consumes too much memory). In fact, 20 is too big for \n");
  printf("many problems.\n");

  exit ( 0 );
}

FILE *open_fname_out (mode)
     char *mode;
{
  FILE *fout;
  char s[100];

  if (fname_out == NULL) {
#ifdef BENCHMARK
    sprintf(s, "un%d.%d%d.%dj", QGROUP, RAMSEY, INCOMPLETE, QUEEN);
#else
    sprintf(s, "unfinish.job");
#endif
    fname_out = (char *) strdup(s);
  } else if (mode[0] == 'w') {
    sprintf(s, "mv %s %s~", fname_out, fname_out);
    system (s);
  }
  fout = fopen(fname_out, mode);
  if (fout == NULL) fout = stdout;
  return (fout);
}

void save_untouched (efile, fout)
     FILE *efile, *fout;
{
  int i;

  while ((i = getc ( efile )) != EOF && i != '(' && i != 'T')
    skip_chars_until( efile, '\n' ); 
  if (i != EOF) {
    fprintf(fout, "Untouched jobs:\n"); putc( i, fout );
    while ((i = getc( efile )) != EOF) putc( i, fout );
  }
}

void append_cmd_line(argc, argv)
     int argc;
     char *argv[];
{
  FILE *fout;

  fout = fopen(fname_out, "a");
  if (OUTPUT < 2) print_command(fout, 1, argc, argv);
  fclose(fout);
}

void print_command (fout, flag, argc, argv)
     FILE *fout; int flag, argc; char *argv[];
{
  int i;
  fprintf(fout, "The job \"%s", argv[0]);
  for (i = 1; i < argc; i++) fprintf(fout, " %s", argv[i]);
  fprintf(fout, "\", (pid: %d)", getpid());
  if (flag)
    fprintf(fout, " ended at %s", get_time());
  else 
    fprintf(fout, " started at %s", get_time());
}

FILE *command_line_check (argc, argv, efile)
     int argc;
     char **argv;
     FILE **efile;
{
  int i, temp;
  FILE *fin;

  /* Default */
  *efile = fin = NULL;

  Memory_count = 0;
  Max_atom = MAX_ATOM-1;
  Max_clause = 100000;
  Printed_clause = 0;

#ifdef PRIVATE
  GROW = 0;
  DATA = 3;
  FORMAT = 0;
#else
  GROW = 10;
  DATA = 2;
  FORMAT = 0;
#endif 

  Stop = 0;
  GREEDY = MAX_ATOM;
  RENAME = 0;
  CREATE = 0;
  TRACE = 1;
  MODEL = 1;
  SELECT = 0;
  PREP = 1;
  LINE = 20;
  JUMP = 1;
  OUTPUT = 0;
  OLDV = 0;
  UIP = 1;
  HOURS = 23; /* default: 23 hours */
  MINUTES = 0;
  CHOICE1 = FF;
  CHOICE2 = TT;
  IDEMPOTENT = 1;
  random_seed = -(time_in_second);

#ifdef BENCHMARK
  ZOOM = 0;
  FLAG = 0;
  RAMSEY = 0;
  NHOLE = 0;
  QGROUP = 0;
  PIGEON = 0;
  QUEEN = 0;
  INCOMPLETE = 0;
  CYCLIC = 0;
  RESTRICT = 0;
  TEAM = 0;
  SQUARE2 = 0;
#endif

  for(i = 1; i < argc; i++) 
    if (argv[i][0] == '+')  {
      temp = str_int(argv[i], 2);

      if (argv[i][1] == '?') {
	print_menu();
      } else if (argv[i][1] == 'j') {
	JUMP = 1000+temp;
	FLAG = 6;
      } else if (argv[i][1] == 'm') {
	MODEL = temp;
      } 
    } else if (argv[i][0] == '-')  {
      temp = str_int(argv[i], 2);

      if (argv[i][1] == '?') {
	print_menu();
      } else if (argv[i][1] == 'c') {
	CREATE = temp;
      } else if (argv[i][1] == 'd') {
	DATA = temp;
 	if (DATA&1) GROW = 0;
      } else if (argv[i][1] == 'e') {
	i++;
	fname_out = (char *) strdup(argv[i]);
	if ((*efile = fopen (fname_out, "r")) == NULL) 
	  fprintf(stderr, "%s ignores invalid parameter : %s\n",
		  argv [0], fname_out );
      } else if (argv[i][1] == 'f') {
	FORMAT = temp;
      } else if (argv[i][1] == 'g') {
	GROW = temp;
      } else if (argv[i][1] == 'h') {
	HOURS = temp;
      } else if (argv[i][1] == 'j') {
	JUMP = temp;

#ifdef BENCHMARK
      } else if (argv[i][1] == 'a') {
	set_addk(temp);
      } else if (argv[i][1] == 'i') {
	open_input_sqs(argv[++i]);
      } else if (argv[i][1] == 'k') {
	set_k_flag(temp);
      } else if (argv[i][1] == 'r') {
	RESTRICT = temp;
#endif

      } else if (argv[i][1] == 'l') {
	LINE = temp;
      } else if (argv[i][1] == 'm') {
	MINUTES = temp;
      } else if (argv[i][1] == 'n') {
	RENAME = temp+1;
      } else if (argv[i][1] == 'o') {
	/* OUTPUT = 5+2: print every clause in dimacs format 
	   OUTPUT = 4+2: print nontrivial clause in dimacs format 
	   OUTPUT = 3+2: print clause in trie dimacs format 
	   OUTPUT = 2+2: print every clause in lisp format 
	   OUTPUT = 1+2: print nontrival clause in lisp format 
	   OUTPUT = 0+2: print clause in trie lisp format */
	OUTPUT = temp+2;
	if (OUTPUT < 8) { DATA = 2; GROW = 0; }
      } else if (argv[i][1] == 'p') {
	PREP = temp;
      } else if (argv[i][1] == 's') {
	if (temp > 0) SELECT = temp;
	else IDEMPOTENT = 0;
      } else if (argv[i][1] == 't') {
	TRACE = temp;
	if (!OUTPUT && TRACE > 5) OUTPUT = 1;
      } else if (argv[i][1] == 'u') {
	UIP = temp;
      } else if (argv[i][1] == 'v') {
	CHOICE1 = TT;
	CHOICE2 = FF;
      } else if (argv[i][1] == 'y') {
	GREEDY = temp;
#ifdef BENCHMARK
      } else if (argv[i][1] == 'z') {
	ZOOM = temp;
      } else if (argv[i][1] == 'A') {
	RANDOM = temp;
      } else if (argv[i][1] == 'B') {
	QGROUP = temp;
	CYCLIC = 'B';
      } else if (argv[i][1] == 'C') {
	QGROUP = temp;
	CYCLIC = 'C';
      } else if (argv[i][1] == 'D') {
	QGROUP = temp;
	CYCLIC = 'D';
      } else if (argv[i][1] == 'G') {
	QGROUP = temp;
      } else if (argv[i][1] == 'H') {
	RAMSEY = temp;
      } else if (argv[i][1] == 'I') {
	INCOMPLETE = temp;
      } else if (argv[i][1] == 'K') {
	PMD = temp;
	if (PMD > 20) { PMD -= 20; IDEMPOTENT = 3; }
	if (PMD > 10) { PMD -= 10; IDEMPOTENT = 2; }
      } else if (argv[i][1] == 'M') {
	MOD = temp;
      } else if (argv[i][1] == 'N') {
	set_num_of_hole(temp);
      } else if (argv[i][1] == 'O') {
	OARRAY = temp;
      } else if (argv[i][1] == 'P') {
	PIGEON = temp;
      } else if (argv[i][1] == 'Q') {
	QUEEN = temp;
      } else if (argv[i][1] == 'R') {
	RAMSEY = temp;
      } else if (argv[i][1] == 'S') {
	TEAM = temp;
#endif

      } else if (argv[i][1] == '\0' && (i+1 == argc)) {
	fin = stdin;
      } else {
	fprintf(stderr, "%s ignores invalid parameter : %s\n",
		argv[0], argv[i] );
      }
    } else if (i+1 < argc) {
      fprintf ( stderr, "%s ignores invalid parameter : %s\n",
	       argv [0], argv [i] );
    }

  if (OUTPUT < 2) {
    p_banner(argc, argv);
    if (fname_out != NULL) 
      printf( "File \"%s\" is open for the extra clauses.\n", fname_out );
  } else {
    printf("c ");
    print_command(stdout, 0, argc, argv);
  }

#ifdef BENCHMARK
  if (QGROUP || RAMSEY || PIGEON || QUEEN || TEAM || INCOMPLETE) {
    fin = NULL; PREP = 0;
  } else 
#endif

  if (fin != stdin && ((fin = fopen ( argv [argc-1], "r" ) ) == NULL)) {
    fprintf ( stderr, "%s can't open file : %s\n",
	      argv [0], argv [argc-1] );
    Stop = 1;
  } else {
    printf( "c Input file \"%s\" is open.\n", argv [argc-1] );

    if (FORMAT == 0) {
      /* fix Max_atom and Max_clause if possible */
      int ch;
      printf( "c Reading clauses in DIMACS's format.\n");
      ch = getc ( fin );  
      while (ch != EOF) {
	if (ch != 'p') { skip_chars_until( fin, '\n' ); ch = getc ( fin ); }
	if (ch == EOF) { printf("c The file is empty.\n"); exit(0); }
	if (ch == 'p' &&
	    getc(fin) == ' ' &&
	    getc(fin) == 'c' &&
	    getc(fin) == 'n' &&
	    getc(fin) == 'f' ) {
	  fscanf(fin, "%d", &Max_atom);
	  fscanf(fin, "%d", &Max_clause);
	  printf("c Max_atom = %d, Max_clause = %d\n", Max_atom, Max_clause);
	  ch = EOF;
	}
      }
    }
  }

#ifdef BENCHMARK
  /* some initiation following the parameters */
  if (RANDOM) 
    random_ksat_init(RANDOM, QGROUP, PMD);
  else if (PMD > 0) 
    init_pmd();
  else if (OARRAY > 0) 
    init_oarray();
  else if (QGROUP > 0) 
    init_qgroups();
  else if (RAMSEY > 0) 
    Max_atom = (RAMSEY-1) * RAMSEY / 2;
  else if (TEAM) 
    Max_atom = init_team();
  else if (QUEEN > 0)
    Max_atom = QUEEN * QUEEN;
  else if (PIGEON > 0)
    Max_atom = PIGEON * (PIGEON+1);

  if (Max_atom >= MAX_ATOM) {
    if (RENAME == 0) {
      fprintf(stderr, "Max_atom(=%d) >= MAX_ATOM(=%d) (check sato.h).\n",
	      Max_atom, MAX_ATOM);
      exit(1);
    } else {
      Max_atom = MAX_ATOM-1;
    }
  }
#endif

  return fin;
}
