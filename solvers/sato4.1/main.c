/*********************************************************************
; Copyright 2002-2003, Hantao Zhang (HZ).  All rights reserved. 
; By using this software the USER indicates that he or she has read, 
; understood and will comply with the following:
;
; --- HZ hereby grants USER nonexclusive permission to use, copy and/or
; modify this software for internal, noncommercial, research purposes only.
; Any distribution, including commercial sale or license, of this software,
; copies of the software, its associated documentation and/or modifications
; of either is strictly prohibited without the prior consent of HZ.  Title
; to copyright to this software and its associated documentation shall at
; all times remain with HZ.  Appropriate copyright notice shall be placed
; on all software copies, and a complete copy of this notice shall be
; included in all copies of the associated documentation.  No right is
; granted to use in advertising, publicity or otherwise any trademark,
; service mark, or the name of HZ.  Software and/or its associated
; documentation identified as "confidential," if any, will be protected
; from unauthorized use/disclosure with the same degree of care USER
; regularly employs to safeguard its own such information.
;
; --- This software and any associated documentation is provided "as is," and
; HZ MAKES NO REPRESENTATIONS OR WARRANTIES, EXPRESS OR IMPLIED, INCLUDING
; THOSE OF MERCHANTABILITY OR FITNESS FOR A PARTICULAR PURPOSE, OR THAT
; USE OF THE SOFTWARE, MODIFICATIONS, OR ASSOCIATED DOCUMENTATION WILL
; NOT INFRINGE ANY PATENTS, COPYRIGHTS, TRADEMARKS OR OTHER INTELLECTUAL
; PROPERTY RIGHTS OF A THIRD PARTY.  HZ, the University of Iowa,
; its Regents, officers, and employees shall not be liable under any
; circumstances for any direct, indirect, special, incidental, or
; consequential damages with respect to any claim by USER or any third
; party on account of or arising from the use, or inability to use, this
; software or its associated documentation, even if HZ has been advised
; of the possibility of those damages.
*********************************************************************/
#define IN_MAIN
#include "main.h"
#include "clocks.h" 
extern struct clock Clocks[ MAX_CLOCKS ];

/* Global variables */
char *fname_out = NULL;
FILE *command_line_check ();
FILE *open_fname_out();

/* #define TP_ALLOC_SIZE 32700 */
#define TP_ALLOC_SIZE MAX_SHORT
#define ARG_TYPE unsigned

static unsigned long Branch_mark = 1;

/*************
 *
 *   main()
 *
 *************/

main (argc, argv)
     int argc;
     char **argv;
{
  FILE *fin;
  FILE *efile;
  int res,i;

  if ( argc == 1 ) print_menu();

  fin = command_line_check( argc, argv, &efile );
  init_once_forall();
#ifndef TEST
  handle_guide_path(1, efile);
#endif
  res = saton(fin); 
  if (res) {
#ifndef TEST
    handle_guide_path(0, efile);
    if (HOURS || MINUTES) append_cmd_line(argc, argv);
#endif
  }

  if (TRACE >= 0) print_command(stdout, 1, argc, argv);
  return (Branch_succ > 0)? 1 : 0;
}

void p_banner (argc, argv)
     int argc;
     char *argv[];
{
  char host[64];

  if (gethostname(host, 64) != 0) str_copy("???", host);
  printf("c ------- SATO %s, %s on %s ------\n", 
	 SATO_VERSION, VERSION_DATE, host);
  print_command(stdout, 0, argc, argv);
  printf("\n");
}  /* print_banner */

void print_menu()
{
  printf("Usage: sato <Input_file> [<Options>]\n\n");
  printf("Options are:\n");
  printf("   -e fname : give the file name of unfinished jobs (default: unfinish)\n");
  printf("   -g<n>    : set the amount of space for lemmas (default: 5)\n");
  printf("   -h<n>    : set the number of hours to be run (default: 47)\n");
  printf("   -m<n>    : set the number of minutes to be run (default: 0)\n");
  printf("   +m<n>    : set the number of expected models (default: 1)\n");
  printf("   -n       : rename variable names to make name space compact\n");

/*
  printf("   -s<n>    : select an atom in clauses for branching:\n");
  printf("               n = 0: the system will pick a strategy for you;\n"
  printf("               n = 1: the atom with the minimal index;\n");
  printf("               n = 2: a variable in a shortest positive clause;\n");
  printf("               n = 3: a variant of n = 3;\n");
  printf("               n = 4: a variable with most occurrences;\n");
  printf("               n = 5: a variable with most occurrences in binary clauses;\n");
  printf("               n = 6: a variable with most Jeroslow-Wang weight.\n");
*/

#ifdef MORETRACE
  printf("   -t<n>    : set the trace level (1: default; 2-4: search; 5-8: build; 9: all)\n\n");
#else
  printf("   -t       : do not print models\n\n");
#endif

  printf("Input_file is a file name. The input consists of a list of clauses, each of\n");
  printf("    which is a list of nonzero integers separated by 0 (DIMACS Format).\n\n");
  printf("    Example: To input clauses p1|p2, -p1|p3|p4, and p2|-p3|p4 in\n");
  printf("       DIMACS Format\n");
  printf("       1 2 0   \n");
  printf("       -1 3 4 0\n");
  printf("       2 -3 4 0\n\n");
  printf("    Tautologies and duplicated literals are always removed.\n");
  printf("    E.g., (1 1 -2 -4) is the same as (1 -2 -4).\n\n");

  exit ( 0 );
}

FILE *open_fname_out (mode)
     char *mode;
{
  FILE *fout;
  char s[100];

  if (fname_out == NULL) {
    sprintf(s, "unfinish");
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
  print_command(fout, 1, argc, argv);
  fclose(fout);
}

void print_command (fout, flag, argc, argv)
     FILE *fout; int flag, argc; char *argv[];
{
  int i;
  fprintf(fout, "c The job \"%s", argv[0]);
  for (i = 1; i < argc; i++) fprintf(fout, " %s", argv[i]);
  fprintf(fout, "\", (pid: %d) %s at %s", 
	  getpid(), (flag)? "ended" : "started", get_time());
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

  memory_count_set(0);
  random_seed = -(time_in_second);
  Stop = -1;  /* Inputing clauses */

  ANT = 0;
  BINARY = 0;
  CHOICE = 0;
  CHOICE2 = 0;
  DLENGTH = 10;  /* Lemmas longer will be deleted */
  HOURS = 47;    /* default: 47 hours */
  GREEDY = MAX_INT;
  GROW = 9;
  INSEARCH = 0;
  JUMP = 1;
  LINE = 20;
  MINVAR = 0;
  MINUTES = 0;
  MODEL = 1;
  QCLAUSE = 0;
  RANJUM = 0;
  RENAME = 0;
  RESTART = 0;
  RESTRICT = 0;
  OLDV = 0;
  SELECT = 0;

  Current_best=MAX_INT;

#ifdef TEST
  TRACE = -1;
#else
  TRACE = 1;
#endif

#ifdef APPLICATION
  /* Applications related */
  QAP = 0;
#endif

  for(i = 1; i < argc; i++) 
    if (argv[i][0] == '?') {
	print_menu();
    } else if (argv[i][0] == '+')  {
      temp = str_int(argv[i], 2);
      if (argv[i][1] == 'j') {
	RANJUM = temp+1;
      } else if (argv[i][1] == 'm') {
	MODEL = temp;
      } 
    } else if (argv[i][0] == '-')  {
      temp = str_int(argv[i], 2);

      if (argv[i][1] == 'e') {
	i++;
	fname_out = (char *) strdup(argv[i]);
	if ((*efile = fopen (fname_out, "r")) == NULL) 
	  fprintf(stderr, "c %s ignores invalid parameter : %s\n",
		  argv [0], fname_out );
      } else if (argv[i][1] == 'a') {
	if (temp) ANT=temp;
	else ANTTRACE = 1;
      } else if (argv[i][1] == 'b') {
	BINARY = temp;
      } else if (argv[i][1] == 'd') {
	DLENGTH = temp;
	if (DLENGTH && (DLENGTH < 5)) DLENGTH = 5;
      } else if (argv[i][1] == 'g') {
	GROW = temp;
      } else if (argv[i][1] == 'h') {
	HOURS = temp;
#ifdef MINONE
      } else if (argv[i][1] == 'I') {
	MINVAR = temp;
#endif
      } else if (argv[i][1] == 'j') {
	JUMP = temp;
      } else if (argv[i][1] == 'l') {
	LINE = temp;
      } else if (argv[i][1] == 'm') {
	HOURS = 0;
	MINUTES = temp;
      } else if (argv[i][1] == 'n') {
	RENAME = temp+1;
      } else if (argv[i][1] == 'r') {
	RESTRICT = temp;
      } else if (argv[i][1] == 's') {
	SELECT = temp;
#ifdef APPLICATION
      } else if (argv[i][1] == 'q'  || argv[i][1] == 'Q') {
	QAP = 1;
      } else if (argv[i][1] == 'G') {
	GROUP = temp;
      } else if (argv[i][1] == 'S' || argv[i][1] == 'H') {
	STAGE = temp;
      } else if (argv[i][1] == 'T' || argv[i][1] == 'I') {
	TEAM = temp;
      } else if (argv[i][1] == 'w') {
	Current_best = temp+1;
#endif
      } else if (argv[i][1] == 't') {
	TRACE = temp;
      } else if (argv[i][1] == 'v') {
	if (temp) CHOICE2 = 1;
	else CHOICE = 1^CHOICE;
      } else {
	fprintf(stderr, "c %s ignores invalid parameter : %s\n",
		argv[0], argv[i] );
      }
    } else if (i > 1) {
      fprintf ( stderr, "c %s ignores invalid parameter : %s\n",
	       argv[0], argv[i] );
    }

  if (TRACE >= 0) {
    p_banner(argc, argv);
    if (fname_out != NULL) 
      printf( "File \"%s\" is open for the extra clauses.\n", fname_out );
  }

#ifdef APPLICATION
  if (GROUP) {
    Max_atom = init_group();
  } else if (TEAM) {
    Max_atom = init_wht();
  } else if (STAGE) {
    Max_atom = init_team();
  } else
#endif

  {
    if ((fin = fopen ( Input_file=argv[1], "r" ) ) == NULL) {
      fprintf ( stderr, "c %s can't open file : %s\n",
		argv [0], Input_file );
      exit(1);
    } 

#ifdef APPLICATION
    else if (QAP) {
      Max_atom = init_qap(fin);
    }
#endif

    else {
      int ch;

      if (TRACE >= 0) 
	printf( "c Reading clauses in DIMACS format from file \"%s\".\n", argv[1] );

      /* fix Max_atom and Clause_num if possible */
      ch = getc ( fin );  
      while (ch != EOF) {
      if (ch != 'p') { skip_chars_until( fin, '\n' ); ch = getc ( fin ); }
      if (ch == EOF) {     
	if (TRACE >= 0) printf("c The input file is empty.\n"); exit(0); 
      }
      if (ch == 'p' &&
	  getc(fin) == ' ' &&
	  getc(fin) == 'c' &&
	  getc(fin) == 'n' &&
	  getc(fin) == 'f' ) {
	fscanf(fin, "%d", &Max_atom);
	fscanf(fin, "%d", &Clause_num);
	if (TRACE >= 0) 
	  printf("c Max_atom = %d, Clause_num = %d\n", Max_atom, Clause_num);
	if (Max_atom >= MAX_LIST) 
	  { fprintf(stderr, "c Variable Number (%d) >= MAX_LIST (%d)\n", 
		    Max_atom, MAX_LIST); exit(1); }
	ch = EOF;
      }
      }
    }
  }

  return fin;
}

/* the main function of saton: return 1 if satisfiable; 0 otherwise.  */
int saton (file)
     FILE *file;
{
  int i = 0, j;

  check_stop(0);
  clock_init();

  CLOCK_START(BUILD_TIME)
  i = build(file);
  CLOCK_STOP(BUILD_TIME)

  if (i != 0) {
    Branch_num = Branch_fail = 1;
    printf("c An empty clause is found!\n");
    printf("s UNSATISFIABLE\n");
    return 0;
  } else {
    CLOCK_START(SEARCH_TIME)
    Branch_skip = 0;
    trace(2, printf("c Starting the search ...\n")); 
    INSEARCH = 1;
    i = search();
    CLOCK_STOP(SEARCH_TIME)
  } 
 
  j=p_stats(stdout);
  if (TRACE>0 && Branch_succ) print_guide_path(stdout);
  print_times(stdout);
  if (TRACE == -1) exit(j);
  return i;
}

int build (file)
     FILE *file;
{
  int j;

  Clause_num0 = Clause_num;
  init_var5_table();
  Clause_num = Subsume_num = Trcl_num = Bicl_num = 0;
  Unit_num = POS_num = NH_num = Delete_num = 0;

  /* read input file */
#ifdef APPLICATION
  if (GROUP) j = group_clauses();
  else if (TEAM) j = wht_clauses();
  else if (STAGE) j = team_clauses();
  else if (QAP) j = input_qap_clauses(file);
  else 
#endif
    j = input_clauses(file);

  if (file && file != stdin) fclose(file);
  if (TRACE >= 0) p_input_stats(stdout);
  fflush(stdout);
  record_keeping();
  Stop = 0;
  return j;
}

init_once_forall ()
{
  int i;
  FILE *f;

  if (Max_atom == 0) { printf("Warning: Max_atom = 0\n"); exit(0); }
  Value = (int *) malloc(MAX_ATOM * (sizeof(int)));
  Unit_cls = (int *) malloc(Max_atom * (sizeof(int))); 
  memory_count(sizeof(int *) * (MAX_ATOM << 1), "Unit_cls");
  for (i = 0; i <= Max_atom; i++) Value[i] = DC;

#ifdef MORETRACE
  if ((LINE == 4000 || LINE == 4001) && (f = fopen("model", "r"))) {
    int i, k;
    for (i = 1; i <= Max_atom; i++) {
      fscanf(f, "%d", &k);
      if (i == k || -i == k) 
	Model[i] = (k > 0)? 1 : 0;
      else printf("warning: %d != |%d|\n", i, k);
    }
    fclose(f);
  }
#endif

}

search ()
{
  int res = 0, i;
  Branch_num = 1;
  Branch_fail = 0;
  Branch_jump = Branch_open = Branch_succ = 0;
  Max_cand = (RENAME>1)? RENAME : Max_atom;

  res = saton_search(1);
  if (RESTART) while (res == STOP_PART) { 
    adjust_record(); 
    res = saton_search(0); 
  }
  return res;
}

void p_input_stats ()
{
  if (Clause_num == 0) {
    printf("c There are no input clauses (the format may be wrong).\n\n");
    exit(0);
   } else if ((Clause_num - Subsume_num) == 1) {
    printf("c Only one input clause is read.\n\n");
    /* exit(0);*/
  } else if (Subsume_num > 0)
    printf("c There are %d input clauses (%d unit, %d subsumed, %d retained).\n", 
	    Clause_num, Unit_num, Subsume_num, Clause_num+Unit_num-Subsume_num);

  printf("c The mallocated memory is %10.2f Kbytes.\n", memory_count_get());
}

void p_paras ( )
{
  if (MODEL == 0) 
    printf ( "Search for all models.\n" );
  else if (MODEL == 1)    
    printf ( "Search only one model.\n" );
  else
    printf ( "Search for %d models.\n", MODEL );

  if (SELECT == 1) 
    printf ( "Branch on a variable with the minimal indices.\n" );
  else if (SELECT == 2) 
    printf ( "Branch on a variable of the shortest positive clauses.\n" );

  printf ( "Set the trace level to %d.\n", TRACE );

  printf("\n");
}

int p_stats ()
{
  if (Branch_succ > 0) {
    printf("c The number of found models is %ld.\n", Branch_succ);
    if (TRACE == -1) { return 10; }
  } else if (Stop == 0 && Branch_skip == 0) {
    printf("c The clause set is unsatisfiable.\n");
    if (TRACE == -1) { printf("s UNSATISFIABLE\n"); return 20; }
  } else {
    printf("c The search for unsatisfiability is incomplete.\n");
    if (TRACE == -1) { printf("s UNKNOWN\n"); return 0; }
  } 

  if (Branch_num == 1) {
    printf("c There is only one branch (%ld succeeded, %ld failed).\n", 
	    Branch_succ, Branch_fail);
  } else if (Branch_skip > 0) {
    printf("c There are %d branches (%d succeeded, %ld failed, %d skipped, %d jumped).\n", 
	    Branch_num, Branch_succ, Branch_fail, Branch_skip, Branch_jump);
  } else {
    printf("c There are %d branches (%d succeeded, %ld failed, %d jumped).\n", 
	    Branch_num, Branch_succ, Branch_fail, Branch_jump);
  }
  return 0;
  /* if (TRACE > 2 && DATA != 1) p_trie_info(f); */
}

void skip_guide_path (r)
     float r;
{
  int i, j, k;

  Branch_skip++;
  if (r < 0.95 && r > 0.2) {
    k = (Branch_open >= RANJUM)? RANJUM : Branch_open;
    if (k) Conflict_cl_level = rand()%k; else Conflict_cl_level = 0;
  } else if (r == 1) {
    Conflict_cl_level = 1;
  }    
}

int check_stop (flag)
     int flag;
{
#ifndef TEST
  static long initial;
  static long previous;
  static long total_time;
#endif

  static long checkpoint;

  if (!flag) {

#ifndef TEST
    total_time = getSATlimit("SATTIMEOUT");
    if (total_time == 0) { 
      total_time = 3600*HOURS+60*MINUTES; 
    }
    printf("c Timeout set after %d seconds\n", total_time);

    initial = time_in_second;
    previous = 0;
#endif

    checkpoint = (RANJUM)? (1 << RANJUM) - 1 : (1 << 12) - 1;
    /* checkpoint = (RANJUM)? (1 << RANJUM) - 1 : (1 << 14) - 1;*/
    /* printf("checkpoint = %ld\n", checkpoint);*/
    return 0;
  } else if (!(Branch_num & checkpoint)) {

#ifndef TEST
    long used_time = time_in_second-initial;

    if (used_time < 0) return STOP_TIME;
    if (used_time >= total_time) {
      /*printf("total time = %ld, used time = %ld\n", 
	total_time, used_time);*/
      return STOP_TIME;
    }

    if (RESTART && (used_time > (RESTART << 3))) {
      if (RESTART < 4) { skip_guide_path(1.0); return STOP_PART; }
      else if ((used_time << 2) > total_time*3) {
	RANJUM = 10;
	total_time -= used_time;
	initial += used_time;
      }
    }

    /* print out the guiding path every 6 hours */ 
    if ((used_time - previous) > 21600) {
      previous = used_time;
      /* print_guide_path(stdout);*/
      handle_guide_path(2, stdin);
      trace(1, {
	printf("branches = %d     %s", Branch_num, get_time());
	fflush(stdout);});
    }

    /* skip some points in the guiding path */ 
    if (RANJUM) {
      /*printf("checkpoint = %d, Branch_num = %ld, the AND of two = %d\n", 
	checkpoint, Branch_num, checkpoint & Branch_num);*/
      skip_guide_path(1.0-((float) used_time)/total_time);
      checkpoint = (1 << (good_random() % RANJUM + 4)) - 1;
    }
#endif

    if (DLENGTH) {
      delete_clauses_on_tape();
    }
  }
  return 0;
}

void bug (i)
     int i;
{
#ifdef PRIVATE
  printf("<<<<<<<<<<<<< BUG%d >>>>>>>>>>>>>\n", i);
#else
  i = 1;
#endif
}

#ifndef TEST
void handle_guide_path (flag, efile)
     int flag;
     FILE *efile;
{
  static int msgout[MAX_LENGTH];
  int MSIZE, i;
  FILE *fout;

  if (flag == 2) {

    FILE *fout;

    fout = open_fname_out("w");
    fprintf(fout, "Under search:\n((");

    MSIZE = msgout[0];
    if (MSIZE > 1) for (i = MSIZE-1; i > 0; i--)
      fprintf(fout, " %s%d", (lit_sign(msgout[i]))? "" : "-", lit_var(msgout[i]));
    fprintf(fout, " 0 )\n ");
    print_guide_path(fout);
    fprintf(fout, ")\n");
    fclose(fout);

  } else if (flag == 1) {
    int cl_arr [MAX_LENGTH];
    int total, ch, j;
    int old_format;

    j = 0;
    msgout[0] = 1;
    msgout[1] = 0;

    if (efile == NULL) return;

    ch = getc ( efile );  
    while (ch != EOF && (ch != '(' || (ch = getc ( efile )) != '(')) {
      skip_chars_until( efile, '\n' ); 
      ch = getc ( efile );                /* skip it */
    }

    /* read the extra unit clauses */
    if (ch != EOF) {
      char buffer[MAX_LENGTH];
      fgets(buffer, MAX_LENGTH, efile); line = buffer;
      total = read_one_clause( buffer, efile, cl_arr, &j, &ch);
      MSIZE = 1;

      if (total > 0) {
	printf("One set of extra unit clauses is read:\n    ");
	print_input_clause(cl_arr, total, NORM);

	reverse(cl_arr, total);
	for (i = 0; i < total; i++) {
	  msgout[MSIZE++] = ch = NEG(cl_arr[i]);
	  Value[lit_var(ch)] = lit_sign(ch);
	}
      }
	
      /* read in the old values */
      ch = getc ( efile );  
      while ( ch != EOF && ch != '(') ch = getc ( efile );  
      if (ch != EOF) {
	total = read_guide_path(efile, Old_value);
	if (total > 0) {
	  printf("\nA guiding path is read:\n    ");
	  print_read_guide_path(Old_value, total);
	  reverse(Old_value, total);
	  i = total;
	  while (i-- && !OLDV) {
	    if (Old_value[i]&1) {
	      OLDV = i+1;
	    } else {
	      msgout[MSIZE++] = ch = Old_value[i]>>1;
	      Value[lit_var(ch)] = lit_sign(ch);
	    }
	  }
	}
      }
      msgout[0] = MSIZE;
      printf("\n");
    }
    fclose(efile);
  } else if (HOURS == 0 && MINUTES == 0) {

    FILE *fout;
    int max=8;
    int j, k, x, y, backup[MAX_STACK], idx=0;
    j = 0;
    fout = open_fname_out("w");

    idx = vstack_collect_selected(backup);

    x = idx;
    for (y = 0; y < x && j <= max; y++) {
      k = backup[y];
      if (k > 0 || j == max) {
	if (j == max)
	  idx = x;
	else {
	  idx = y+1;
	  backup[y] = -k; 
	  set_var_value(k, NEG(get_var_value(k))); 
	}
	fprintf(fout, "((");
	MSIZE = msgout[0];
	if (MSIZE > 1) for (i = 1; i < MSIZE; i++)
	  fprintf(fout, " %s%d", (lit_sign(msgout[i]))? "" : "-", lit_var(msgout[i]));

	fprintf(fout, " 0 ) ");
	output_guide_path(fout, idx, backup);
	fprintf(fout, ")\n");
	set_var_value(k, NEG(get_var_value(k))); 
	j++;
      }
    }
    fclose(fout);
  } else {
    fout = open_fname_out("w");
    fprintf(fout, "Unfinished job is:\n((");

    MSIZE = msgout[0];
    if (MSIZE > 1) for (i = MSIZE-1; i > 0; i--) 
      fprintf(fout, " %s%d", (lit_sign(msgout[i]))? "" : "-", lit_var(msgout[i]));
    fprintf(fout, " 0 )\n ");
    print_guide_path(fout);
    fprintf(fout, ")\n");
    /* if (efile != NULL) save_untouched(efile, fout);*/
    fclose(fout);
  }
}
#endif

void print_guide_path (fout)
     FILE *fout;
{
  int backup[MAX_STACK], idx;
  
  idx = vstack_collect_selected(backup);
  output_guide_path(fout, idx, backup);
  fflush(fout);
}

void output_guide_path (f, idx, backup)
     FILE *f;
     int idx, backup[];
{
  int i, k;

  fprintf(f, "( ");

  for (i = 0; i < idx; i++) {
    k = backup[i];
    if (k > 0) { fprintf(f, "f"); }
    else { fprintf(f, "s"); k = -k; }

    if (get_var_value(k) == FF) 
      fprintf(f, "-%d ", k);
    else 
      fprintf(f, "%d ", k);
  }
  fprintf(f, ")");
}

int read_guide_path ( f, keys )
     FILE *f;
     int keys[];
{
  int total, key;
  int ch;
  
  total = 0;
  while (1) {
    ch = getc ( f );  

    while (ch != EOF && ch != 'f' && ch != 's' && ch != ')') 
      ch = getc ( f );  
    if (ch == EOF) return 0;
    if (ch == ')') {
      skip_chars_until( f, '\n' ); 
      return total;
    }
    fscanf(f, "%d", &key);
    key = (key>0)? (key<<1)+1 : (-key)<<1;
    keys[total++] = (ch == 'f')? (key << 1)+1 : key<<1;
  }
}

void print_read_guide_path (keys, total)
     int keys[], total;
{
  int i, k;
  printf("( ");
  for (i = 0; i < total; i++) {
    if (keys[i]&1) 
      printf("f"); 
    else
      printf("s");
    k = keys[i]>>1;
    printf("%s%d ", lit_sign(k)? "" : "-", lit_var(k));
  }
  printf(")\n");
}

/* To be used with "SATRAM" or "SATTIMEOUT" */
/* Return the limit or:
   0  if the variable is not set or
      if there was a problem in atoi (variable isn't a number) */
int getSATlimit (char *name) {
  char * value = (char *) getenv(name);
  if (value == NULL) return(0);
  return atoi(value);
}

void adjust_record ()
{
  Stop = 0;
  Branch_skip = 0;

  RESTART++;
  if (RESTART == 3) { SELECT = 6; }
  else if (RESTART > 3) { 
    SELECT = 8; 
  }
#ifdef MORETRACE
  printf("Restart #%d (-s%d, -g%d)\n", 
	 RESTART-1, SELECT, GROW);
#endif
}

int stop () {  if (TRACE++ > 11) exit(1);}
int stop1 () { return 1; }

