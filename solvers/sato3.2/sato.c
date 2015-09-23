/*********************************************************************
; Copyright 1992-2002, The University of Iowa (UI).  All rights reserved. 
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
#include "main.h"
#include "clocks.h" 
FILE *open_fname_out();
GLOB struct clock Clocks[ MAX_CLOCKS ];

/* #define TP_ALLOC_SIZE 32700 */
#define TP_ALLOC_SIZE MAX_SHORT
#define ARG_TYPE unsigned
#define two14 16383   /* 2^14-1 */
#define two15 32767   /* 2^15-1 */

static char *Alloc_block;    /* location returned by most recent malloc */
static char *Alloc_pos;      /* current position in block */
static unsigned long Branch_mark = 1;

/* the main function of sato: return 1 if satisfiable; 0 otherwise.  */
int sato (file)
     FILE *file;
{
  int i = 0;

  check_stop(0);
  clock_init();

  CLOCK_START(BUILD_TIME)
  i = build(file);
  CLOCK_STOP(BUILD_TIME)

  if (i != 0) {
    i = 0;
    Branch_num = Branch_fail = 1;
    if (OUTPUT > 1) fprintf(stderr, "An empty clause is found!\n");
    exit(0);
  } else if (OUTPUT > 1) 
    exit(0);
  else {
    CLOCK_START(SEARCH_TIME)
#ifdef MORETRACE
    if (TRACE > 1)  fprintf(Sato_fp, "\nStarting the search ...\n"); 
#endif

    Branch_skip = 0;

    if (DATA == 1) {
      if (TRACE > 1) printf("Using the list structure for clauses.\n");
      i = list_search();
    } else {
      if (TRACE > 1) printf("Using the trie structure for clauses.\n");
      i = trie_search();
    }
    CLOCK_STOP(SEARCH_TIME)
  } 
 
  if (OUTPUT < 2) p_stats(Sato_fp);
  if (Branch_succ && Backup_idx > 0) print_guide_path(stdout);
  print_times(Sato_fp);
  return i;
}

int build (file)
     FILE *file;
{
  int j;

  Alloc_block = NULL;
  Alloc_pos = NULL;
  Clause_num = Subsume_num = Trcl_num = Bicl_num = Unit_num = NH_num = 0;
  Tmp_idx = 0;
  if (TRACE > 5) fprintf(Sato_fp, "\nInput clauses are:\n\n");

  if (OUTPUT > 4 && OUTPUT < 8) 
    printf("p cnf %d %ld\n", Max_atom, Max_clause);

  if (DATA == 1) init_list(Max_atom); else init_trie();

  /* read input file and build tree */
  j = 0;
  Act_max_atom = Max_atom;

#ifdef BENCHMARK
  if (RANDOM) {
    j = random_ksat_cls(QGROUP, PMD);
  } else if (PMD) {
    j = pmd_clauses();
  } else if (OARRAY) {
    j = oarray_clauses();
  } else if (QGROUP > 0) {
    if ((QUEEN == 4 || QUEEN == 14) && 
	(((QGROUP-INCOMPLETE)*(QGROUP-3*INCOMPLETE-1)) % 4 != 0)) {
      printf("Warning: (v-n)(v-3n-1) mod 4 = %d != 0\n",
	     ((QGROUP-INCOMPLETE)*(QGROUP-3*INCOMPLETE-1)) % 4);
    }
    if (CYCLIC)
      j = cyclic_qgroup_clauses();
    else
      j = qgroup_clauses();
  } else if (RAMSEY > 0) 
    j = ramsey_clauses();
  else if (TEAM)
    j = team_clauses();
  else if (PIGEON > 0)
    j = pigeonhole_clauses();
  else if (QUEEN > 0)
    j = queen_clauses();
  else if (INCOMPLETE > 0)
    j = isomo_clauses();
  else 
#endif 
  {
    Act_max_atom = 0;
    j = input_clauses ( file );
    if (file != stdin) fclose ( file );
  }

  if (OUTPUT == 2 || OUTPUT == 5) {
    print_clauses_in_trie();
  }

  if (OUTPUT > 4 && OUTPUT < 8) {
    int flag = 0;
    if (Act_max_atom != Max_atom) {
      fprintf(stderr, "\nThe number of variables should be %ld instead of %ld, i.e,\n", 
	      Act_max_atom, Max_atom);
      flag = 1;
    } else if (Printed_clause != Max_clause) {
      fprintf(stderr, "\nThe number of clauses should be %ld instead of %ld, i.e,\n", 
	      Printed_clause, Max_clause);
      flag = 1;
    }
    if (flag == 1) {
      FILE *f;

      fprintf(stderr, "p cnf %d %ld\n", Act_max_atom, Printed_clause);
      f = fopen("fixnum", "w");
      if (f != NULL) {
	fprintf(stderr, "Please run fixnum with the output file name, i.e.,\n");
	fprintf(stderr, "  fixnum <output-file>\n");
	fprintf(f, "/bin/mv $1 $1.old\nsed 's/^p cnf %d %ld/p cnf %d %ld/' $1.old > $1\n/bin/rm $1.old\n", 
		Max_atom, Max_clause, Act_max_atom, Printed_clause);
	fclose(f);
	system("chmod a+rx fixnum");
      }
    }
  } else if (OUTPUT < 2) p_input_stats(Sato_fp);
  fflush(Sato_fp);
  record_keeping();
  return j;
}

void p_input_stats (f)
     FILE *f;
{
  fprintf(f, "\n");
  if (Clause_num == 0) {
    fprintf(f, "There are no input clauses (the format may be wrong).\n\n");
    exit(0);
   } else if ((Clause_num - Subsume_num) == 1) {
    fprintf(f, "Only one input clause is read.\n\n");
    /* exit(0);*/
  } else if (Subsume_num > 0)
    fprintf(f, "There are %ld input clauses (%ld unit, %ld subsumed, %ld retained).\n", 
	    Clause_num, Unit_num, Subsume_num, Clause_num+Unit_num-Subsume_num);
  else 
    fprintf(f, "There are %d input clauses.\n", Clause_num );

  fprintf(f, "The maximal index of propositional variables is %d.\n",
	  Max_atom);
  fprintf(f, "The mallocated memory is %10.2f Kbytes.\n", Memory_count / 1024.0);
}

void p_paras ( )
{
  if (MODEL == 0) 
    printf ( "Search for all models.\n" );
  else if (MODEL == 1)    
    printf ( "Search only one model.\n" );
  else
    printf ( "Search for %d models.\n", MODEL );

  if (SELECT == 0) 
    printf ( "Branch on the atom with the minimal indices.\n" );
  else if (SELECT == 1) 
    printf ( "Branch on an atom of the shortest positive clauses.\n" );
  else if (SELECT == 2) 
    printf ( "Branch on an atom of the shortest negative clauses.\n" );

  printf ( "Set the trace level to %d.\n", TRACE );

  if (TRACE > 0)
    printf ( "Print at most %d atoms per line in a model.\n",
	    LINE );
  printf("\n");
}

void p_stats (f)
     FILE *f;
{
  if (Branch_succ > 0) 
    fprintf(f, "\nThe number of found models is %ld.\n", Branch_succ);
  else if (Branch_num == Branch_fail+Branch_jump) 
    fprintf(f, "\nThe clause set is unsatisfiable.\n");
  else
    fprintf(f, "\nThe search for unsatisfiability is incomplete.\n");

  if (Branch_num == 1)
    fprintf(f, "\nThere is only one branch (%ld succeeded, %ld failed).\n", 
	   Branch_succ, Branch_fail);
  else if (Branch_skip > 0)
    fprintf(f, "\nThere are %ld branches (%ld succeeded, %ld failed, %ld skipped).\n", 
	   Branch_num, Branch_succ, Branch_fail, Branch_skip);
  else
    fprintf(f, "\nThere are %d branches (%ld succeeded, %ld failed, %d jumped).\n", 
	   Branch_num, Branch_succ, Branch_fail, Branch_jump);

  /* if (TRACE > 2 && DATA != 1) p_trie_info(f); */
}

void skip_guide_path (r)
     float r;
{
  int i, j, k;

#ifdef TRY
  if (r == 2) {
    for (i = 0; i < Backup_idx; i++) 
      if ((k = Backup[i]) > 0) {
	Backup[i] = -k; 
	Branch_skip++;
	Branch_open--;
	if (TRACE >= 2) 
	  fprintf(Sato_fp, "close the second branch of B[%d]=x%d\n", i, k);
      }
  } 
#endif

  if (r < 0.95 && r > 0.05) {
    float x=0.0;
    int done=0;
    k = (Backup_idx >= FLAG+FLAG)? FLAG+FLAG : Backup_idx;

    j=1;
    for (i = 0; (done==0) && (i < k); i++) {
      j = (j << 1);
      if (Backup[i] > 0) {
	x += 1.0/j;
	/*printf("%d: x=%f, j=%d\n", i, x, j);*/
	if (x >= r) done=1;
      }
    }
#ifdef MORETRACE
    if (TRACE >= 2) printf("r=%f, x=%f\n", r, x);
#endif
  
    if (done==1) 
      for (i = i+1; i < Backup_idx; i++) {
	if ((k = Backup[i]) > 0) {
	  Backup[i] = -k; 
	  Branch_skip++;
	  Branch_open--;
#ifdef MORETRACE
	  if (TRACE >= 2) 
	    fprintf(Sato_fp, "close the second branch of B[%d]=x%d\n", i, k);
#endif
	}
      }
  }
}

int check_stop (flag)
     int flag;
{
  static long initial;
  static long previous;
  static long total_time;
  static long checkpoint;

  if (flag == 0) {
    initial = time_in_second;
    total_time = 3600*HOURS+60*MINUTES;
    previous = 0;
    checkpoint = (1 << (FLAG + FLAG + 4)) - 1;
    /* printf("checkpoint = %ld\n", checkpoint);*/
    return 0;
  } else {

    if (HOURS == 0 && MINUTES == 0) return 1;

    if ((Branch_fail & checkpoint) == 0) {
      long used_time = time_in_second-initial;
      if (used_time < 0) return 1;
      if (used_time >= total_time) {
	/*printf("total time = %ld, used time = %ld\n", 
	  total_time, used_time);*/
	return 1;
      }

      /* print out the guiding path every 6 hours */ 
      if ((used_time - previous) > 21600) {
	previous = used_time;
	/* print_guide_path(stdout);*/
	read_one_problem(2, stdin);
	printf("branches = %d     %s", Branch_fail, get_time());
	fflush(stdout);
      }

      /* skip some points in the guiding path */ 
      if (JUMP>=1000 && DATA>=2) {
	/*printf("checkpoint = %d, Branch_fail = %ld, their and = %d\n", 
	  checkpoint, Branch_fail, checkpoint & Branch_fail);*/
	skip_guide_path(1.0-((float) used_time)/total_time);
	checkpoint = (1 << (good_random() % FLAG + FLAG + FLAG)) - 1;
	/*printf("checkpoint = %ld\n", checkpoint);*/
      }


      /* restart? */
      if (SELECT == 20) {
	skip_guide_path(1.0);
      }
    }
    return 0;
  }
}

int handle_succ_end ()
{
#ifdef BENCHMARK
  if (QUEEN == 32) {
    int i, j;
    j = 0;
    for (i=0;i<9;i++) if (Value[Max_atom-i] == TT) j++;
    if (j < 3) 
      return ((DATA == 1)? list_prev_key(1) : 
	      (DATA == 2)? trie2_prev_key(2) : trie_prev_key());
    for (i=0;i<9;i++) printf("X%d=%d\n", Max_atom-i, Value[Max_atom-i]);
  }
#endif

  Branch_succ++;

#ifdef MORETRACE
  if (TRACE == 2) fprintf(Sato_fp, "S%d\n", Branch_succ);
#endif
  if (TRACE) print_model(Sato_fp);
  else if (MODEL == 0 && Branch_succ == Branch_mark) {
    fprintf(Sato_fp, "\nThe %dth model is found!\n", Branch_succ);
    Branch_mark *= 10;
  }
  return ((MODEL && Branch_succ >= MODEL)? 0 : 
	  ((DATA == 1)? list_prev_key(1) : 
	   (DATA == 2)? trie2_prev_key(3) : trie_prev_key()));
}

int handle_fail_end ()
{
  Branch_fail++;

#ifdef MORETRACE
  if (TRACE == 2) fprintf(Sato_fp, "F%ld\n", Branch_fail);
  else if (TRACE > 8 || TRACE == 3 || TRACE == 4)  
    fprintf(Sato_fp, "      an empty clause is found.\n"); 
#endif

  if (Stop = check_stop(1)) {
    /*
    int i, last;
    last = Backup_idx-1;
    while (last >= 0 && Backup[last] < 0) last--;
    if (last >= 0) { 
      i = Backup[last]; 
      Backup[last] = -i; 
      Value[i] = NEG(Value[i]);
    }
    Backup_idx = last+1;
    */

    fprintf(Sato_fp, "\nThe search is aborted and the current search tree path is:\n");
    output_guide_path(Sato_fp);
    fprintf(Sato_fp, "\n");
  }

  return UNSAT;
}

void bug (i)
     int i;
{
#ifdef PRIVATE
  printf("<<<<<<<<<<<<<<<<<<< BUG%d >>>>>>>>>>>>>>>>>>>>\n", i);
#else
  i = 1;
#endif
}

int strategy0 ()
     /* the least unsigned variable */
{
  int i; 
  
  if (JUMP > 1 && JUMP < 1000) {
    i = (int) (good_random() % Max_atom);
    while (++i <= Max_atom) if (Value[i] == DC) {
      Value[i] = CHOICE1;
      return i;
    }
  } 

  for (i = 1; (i <= Max_atom); i++) 
    if (Value[i] == DC) {
      Value[i] = CHOICE1;
      return i;
    }

  return 0;
}

/*************
 *    OTTER's Function:
 *
 *    Allocate n contiguous bytes, aligned on pointer boundry.
 *
 *************/

#define scale sizeof(int *)

char *tp_alloc(n)
     int n;
{
  char *return_block;

  /* if n is not a multiple of sizeof(int *), then round up so that it is */
  /*if (n % scale != 0)	n += (scale - (n % scale));*/

  if (Alloc_block == NULL || Alloc_block + TP_ALLOC_SIZE - Alloc_pos < n) {
    /* try to malloc a new block */
    if (n > TP_ALLOC_SIZE) {
      fprintf(stderr, "tp_alloc, request too big: %d\n", n);
      exit(0);
    } else {
      Alloc_pos = Alloc_block = (char *) malloc((ARG_TYPE) TP_ALLOC_SIZE);
      if (Alloc_pos == NULL) {
	fprintf(stderr, "ABEND, malloc returns NULL (out of memory).\007\n");
	fprintf(stderr, "%ld K has been mallocated.\007\n", Memory_count/1042);
	exit(0);
      }
      Memory_count += TP_ALLOC_SIZE;
    }
  }

  return_block = Alloc_pos;
  Alloc_pos += n;
  return(return_block);
}  /* tp_alloc */


void read_one_problem (flag, efile)
     int flag;
     FILE *efile;
{
  static int msgout[MAX_ATOM];
  int MSIZE, i;

  if (flag == 2) {

    FILE *fout;

    fout = open_fname_out("w");
    fprintf(fout, "Under search:\n((");

    MSIZE = msgout[0];
    if (MSIZE > 1)
      for (i = MSIZE-1; i > 0; i--) fprintf(fout, " %d", msgout[i]);
    else 
      fprintf(fout, " 0");

    fprintf(fout, " ) ");
    output_guide_path(fout);
    fprintf(fout, ")\n");
    fclose(fout);

  } else if (flag == 1) {
    int sign_arr [MAX_ATOM];
    int cl_arr [MAX_ATOM];
    int total, ch, j;
    int old_format;

    OLDV = j = 0;
    if (Max_atom == 0) printf("Warning: Max_atom = 0\n");
    for (i = 1; i <= Max_atom; i++) Value[i] = DC;
    msgout[0] = 2;
    msgout[1] = 0;

    if (efile == NULL) return;
    ch = getc ( efile );  
    while (ch != EOF && (ch != '(' || (ch = getc ( efile )) != '(')) {
      skip_chars_until( efile, '\n' ); 
      ch = getc ( efile );                /* skip it */
    }

    /* read the extra unit clauses */
    if (ch != EOF) {
      old_format = FORMAT;
      FORMAT = 1;
      total = read_one_clause( efile, cl_arr, sign_arr, &j, NULL );
      FORMAT = old_format;
      MSIZE = 1;

      if (total > 0) {
	reverse(cl_arr, total);
	printf("One set of extra unit clauses is read:\n    ");
	print_clause(cl_arr, sign_arr, total);

	for (i = 0; i < total; i++) {
	  ch = cl_arr[i];
	  Value[ch] = sign_arr[ch];
	  msgout[MSIZE++] = (sign_arr[ch])? ch : -ch;
	}
      }
	
      /* read in the old values */
      ch = getc ( efile );  
      while ( ch != EOF && ch != '(') ch = getc ( efile );  
      if (ch != EOF) {
	total = read_guide_path( efile, Old_value, Old_choice );
	if (total > 0) {
	  printf("\nA guiding path is read:\n    ");
	  print_read_guide_path(Old_value, Old_choice, total);
	  reverse(Old_value, total);
	  reverse(Old_choice, total);
	  i = total;
	  while (i-- && OLDV == 0) {
	    if (Old_choice[i] == FF) {
	      if (Old_value[i] > 0) {
		Value[Old_value[i]] = TT;
	      } else {
		Value[-Old_value[i]] = FF;
	      }
	      msgout[MSIZE++] = Old_value[i];
	    } else {
	      OLDV = i+1;
	    }
	  }
	}
      }
      msgout[0] = MSIZE;
      printf("\n");
    }
  } else if (HOURS == 0 && MINUTES == 0) {

    FILE *fout;
    int max=8;
    int j, k, x, y;
    j = 0;
    fout = open_fname_out("w");
    x = Backup_idx;

    for (y = 0; y < x && j <= max; y++) {
      k = Backup[y];
      if (k > 0 || j == max) { 
	if (j == max)
	  Backup_idx = x;
	else {
	  Backup_idx = y+1;
	  Backup[y] = -k; 
	  Value[k] = NEG(Value[k]); 
	}
	fprintf(fout, "((");
	MSIZE = msgout[0];
	if (MSIZE > 1)
	  for (i = 1; i < MSIZE; i++) fprintf(fout, " %d", msgout[i]);
	else 
	  fprintf(fout, " 0");

	fprintf(fout, " ) ");
	output_guide_path(fout);
	fprintf(fout, ")\n");
	Value[k] = NEG(Value[k]); 
	j++;
      }
    }
    fclose(fout);
  } else {

    FILE *fout;

    fout = open_fname_out("w");
    fprintf(fout, "Unfinished job is:\n((");

    MSIZE = msgout[0];
    if (MSIZE > 1)
      for (i = MSIZE-1; i > 0; i--) fprintf(fout, " %d", msgout[i]);
    else 
      fprintf(fout, " 0");

    fprintf(fout, " ) ");
    output_guide_path(fout);
    fprintf(fout, ")\n");

    if (efile != NULL) save_untouched(efile, fout);
    fclose(fout);
  }
}

void print_guide_path (f)
     FILE *f;
{
  if (!Backup_idx) 
    fprintf(f, "\nThe search tree path is empty.\n");
  else {
    fprintf(f, "\nThe search tree path is:\n ");
    output_guide_path(f);
    fprintf(f, "\n");
    fflush(f);
  }
}

void output_guide_path (f)
     FILE *f;
{
  int i, k;

  fprintf(f, "( ");

  for (i = 0; i < Backup_idx; i++) {
    k = Backup[i];
    if (k > 0) { fprintf(f, "f"); }
    else { fprintf(f, "s"); k = -k; }

    if (Value[k] == FF) 
      fprintf(f, "-%d ", k);
    else 
      fprintf(f, "%d ", k);
  }
  fprintf(f, ")");
}

int read_guide_path ( f, keys, choices )
     FILE *f;
     int keys[], choices[];
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
    keys[total] = key;
    choices[total++] = (ch == 'f')? TT : FF;
  }
}

void print_read_guide_path (keys, choices, total)
     int keys[], choices[], total;
{
  int i;
  printf("( ");
  for (i = 0; i < total; i++) {
    if (choices[i] == TT) 
      printf("f"); 
    else
      printf("s");
    printf("%d ", keys[i]);
  }
  printf(")\n");
}

