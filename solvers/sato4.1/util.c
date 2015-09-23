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

#include "main.h"
#include "clocks.h"
struct clock Clocks[ MAX_CLOCKS ];
int *Rename = NULL;

print_value (s)
     char *s;
{
  int i;
  for (i = 1; i <= Max_atom; i++) printf("x%d=%d ", i, Value[i]);
  printf("%s\n", s);
}

void print_model (f)
     FILE *f;
{
  if (TRACE < 0) {
    int i;
    printf("s SATISFIABLE\nv ");
    for (i = 1; i <= Max_atom; i++) {
      if (get_var_value(i) == TT) printf("%d ", i);
      else printf("-%d ", i);
    }
    printf("0\n");
  } else if (TRACE) {

    int i, col=0;

    fprintf(f, "\nModel #%ld:\n\n    ", Branch_succ);

    if (LINE > 1) {
      for (i = 1; i <= Max_atom; i++)
	if (get_var_value(i) == TT) { col++; fprintf(f, "%d  ", i); }
    } else {
      for (i = 1; i <= Max_atom; i++)
	if (get_var_value(i) == TT) { col++; fprintf(f, "%d  ", i); }
	else { fprintf(f, "-%d  ", i); }
    }
    fprintf(f, "\n\nc The number of true atoms is %d.\n", col);
  }
}

void print_input_clause (arr, total, type)
     int arr[], total, type;
{
  int i; 
  for (i = 0; i < total; i++) {
    printf ("%s%d ", (arr[i]&1)? "-" : "", arr[i]>>1);
  }

#ifdef QUASICLAUSE
  switch(type) {
  case EQUL: printf("= %d\n", arr[total]); return;
  case LESS: printf("< %d\n", arr[total]); return;
  case LSEQ: printf("<= %d\n", arr[total]); return;
  case GRTR: printf("> %d\n", arr[total]); return;
  case GTEQ: printf(">= %d\n", arr[total]); return;
  case UNEQ: printf("!= %d\n", arr[total]); return;
  case WEIG: printf("w %d\n", arr[total]); return;
  }
#endif

  printf("0\n"); 
}

void print_unit_clause (fp, sign, i)
     FILE *fp; int sign, i;
{ 
  printf((sign == TT)? "%d 0\n" : "-%d 0\n", i);
}

int insert_clause ( cl_arr, total, plen, type)             
     int cl_arr[], total, plen, type;
{
  int j, i, k;

  trace(6, print_input_clause (cl_arr, total, type));
  Clause_num++;
  if (total == 2) Bicl_num++;
  else if (total == 3) Trcl_num++;

  /* check for literals and clauses subsumed by unit clauses */
  if (type == NORM) {
    i = 0;
    while (i < total) {
      k = cl_arr[i]>>1;
      if (Value[k] == DC) {
	i++;
      } else if (Value[k]^(1&cl_arr[i])) {
	/* the clause is subsumed */
	Subsume_num++;

#ifdef MORETRACE
	if (TRACE > 7)
	  fprintf(stdout, "      [C%d] is subsumed by unit clause (%d).\n",
		  Clause_num, (Value[k])? k : -k);
#endif
	return 0;

      } else { /* the literal is subsumed */

	if (!(cl_arr[i]&1)) plen--;
	cl_arr[i] = cl_arr[--total];

#ifdef MORETRACE
	if (TRACE > 7)
	  fprintf(stdout, "    %d in [C%d] is skipped due to a unit clause.\n",
		  k, Clause_num);
#endif
      }
    }

    if (total == 0) {
      trace(4, printf("    [C%d] becomes empty.\n", Clause_num));
      return 1;
    }

    if (total == 1) { /* a unit clause is found */
      k = cl_arr[0]>>1;
      Value[k] = plen;
      Unit_num++;

#ifdef MORETRACE
      if (TRACE > 7 || TRACE == 4)
	fprintf (stdout, "    x%d is set to %d by unit clause.\n",
		 k, Value[k]);
#endif

      return 0;
    }
    insert_clause_to_tape(cl_arr, total, plen, type);

#ifdef QUASICLAUSE
  } else { /* non NORM */
    int s = cl_arr[total];
    QCLAUSE = 1;
    i = 0;
    while (i < total) {
      k = cl_arr[i]>>1;
      if (Value[k] == DC) {
	i++;
      } else {

	if (Value[k]^(cl_arr[i]&1)) {
	  /* a true literal is found */
	  s--;
	  trace(8, printf("    %d in [C%d] is true.\n", k, Clause_num));
	} else { /* the literal is subsumed */
	  trace(8, printf("    %d in [C%d] is false.\n", k, Clause_num));
	}

	if (!(cl_arr[i]&1)) plen--;
	cl_arr[i] = cl_arr[--total];
      } 
    }

    cl_arr[total] = s;
    if (total == 0) {
      trace(4, printf("    Type %d [C%d] becomes empty.\n", type, Clause_num));
      switch(type) {
      case EQUL: if (s != 0) {  return 1; } else return 0;
      case LESS: if (s <= 0) {  return 1; } else return 0;
      case LSEQ: if (s < 0) {  return 1; } else return 0;
      case GRTR: if (s >= 0) {  return 1; } else return 0;
      case GTEQ: if (s > 0) {  return 1; } else return 0;
      case UNEQ: if (s == 0) {  return 1; } else return 0;
      default: return 0;
      }
    }

    if (total == 1) { /* a unit clause is found */
      k = cl_arr[0]>>1;
      Unit_num++;
      trace(4, printf("    [C%d] becomes unit (%d).\n", Clause_num, k));
      switch(type) {
      case EQUL:
	if (s == 1) return insert_cl_1(k, plen);
	else if (s == 0) return insert_cl_1(k, NEG(plen));
	else {  return 1; }
      case LESS: 
	if (s == 1) return insert_cl_1(k, NEG(plen));
	else if (s > 1) return 0;
	else {  return 1; }
      case LSEQ: 
	if (s == 0) return insert_cl_1(k, NEG(plen));
	else if (s > 0) return 0;
	else {  return 1; }
      case GRTR: 
	if (s == 0) return insert_cl_1(k, plen);
	else if (s < 0) return 0;
	else {  return 1; }
      case GTEQ: 
	if (s == 1) return insert_cl_1(k, plen);
	else if (s < 1) return 0;
	else {  return 1; }
      case UNEQ: 
	if (s == 1) return insert_cl_1(k, NEG(plen));
	else if (s == 0) return insert_cl_1(k, plen);
	else return 0;
      default: return 0;
      }
    }

    if (s == 0) { /* no counting is needed */
      trace(4, printf("  values in [C%d] can be decided.\n", Clause_num));
      switch(type) {
      case EQUL:
      case LSEQ: 
	for (i = 0; i < total; i++) {
	  k = cl_arr[i];
	  Unit_num++;
	  insert_cl_1((k>>1), k&0);
	}
	return 0;
      case LESS: 
	return 1; 
      case GTEQ: 
	return 0;
      default: break;
      }
    } else if (s < 0) { /* no counting is needed */
      switch(type) {
      case EQUL:
      case LSEQ: 
      case LESS: 
	return 1; 
      default: 
	return 0;
      }
    }

    /* LSEQ only */
    if (type == EQUL) {
      ++Clause_num0;
      insert_clause_to_tape(cl_arr, total, plen, LSEQ);
      insert_clause_to_tape(cl_arr, total, plen, GTEQ);
    } else if (type == UNEQ) {
      ++Clause_num0;
      insert_clause_to_tape(cl_arr, total, plen, LESS);
      insert_clause_to_tape(cl_arr, total, plen, GRTR);
    } else {
      insert_clause_to_tape(cl_arr, total, plen, type);
    }
#endif
  }

  return 0;
}

int read_one_clause ( buffer, f, cl_arr, plen, type)
     char buffer[];
     FILE *f; 
     int cl_arr[];
     int *plen, *type;
{
  int var, ptotal, total, sign, i, j, tautology=0;
  *plen = *type = 0;

  ptotal = total = 0;
  sign = read_int_line( &i, buffer, f );

  while (sign < 2) { 
    var = (i<<1)+(1-sign);

    if (total >= MAX_LENGTH) {
      fprintf(stderr, "Clause #%d is too big: > %d = MAX_LENGTH (see main.h)\n", 
	      Clause_num+1, MAX_LENGTH);
      exit(0);
    }

    if (i > Max_atom) {
      fprintf(stderr, "%d in Clause #%d is too long: Max_atom = %d\n", 
	      i, Clause_num+1, Max_atom);
      exit(0);
    }

    for (j = 0; j < total; j++) 
      if (var == cl_arr[j]) {
	j = -1;
	break;
      } else if ((var^1) == cl_arr[j]) {
	sign = 1;
	while (sign < 2) sign = read_int_line( &i, buffer, f );
	if (sign == 13) {
	  printf("\nc WARNING: [C%d] is not ended by 0\n\n", Clause_num);
	}
	return -1;
      }

    if (j != -1) {
      cl_arr[total++] = var; 
      ptotal += sign;
    }
    sign = read_int_line( &i, buffer, f );
  }

  if (sign == 13) {
    trace(7, printf("c      [C%d] is a bad clause and is ignored.\n", 
		    Clause_num));
    return -1;
  } else {
    cl_arr[total] = i;
    *type = sign-2;
    *plen = ptotal;
  }
  return total;
}

int input_clauses ( f )
     /* return 1 if an empty clause is found; otherwise, 0 */
     FILE *f; 
{
  int total_lits, i, plen, type;
  char buffer[MAX_LENGTH];
  int cl_arr[MAX_LENGTH];
  
  if (f == NULL) {
    fprintf(stderr, "c the input file is null\n");
    exit(0);
  } 
  
  if (TRACE > 5) printf("\nc Input clauses:\np cnf %d %d\n", 
			 Max_atom, Clause_num0);
  if (RENAME) {
    Rename = (int *) malloc(MAX_ATOM * sizeof(int));
    memory_count(sizeof(long)*MAX_ATOM, "Rename");
    for (i = 1; i <= RENAME; i++) Rename[i] = i;
    Rename[0] = RENAME+1;
  }
  
  fgets(buffer, MAX_LENGTH, f); line = buffer;
  while (Clause_num < Clause_num0) {
    total_lits = read_one_clause(buffer, f, cl_arr, &plen, &type);
    if (total_lits == 0) return 1;  /* empty clause */
    if (total_lits > 0 && insert_clause(cl_arr, total_lits, plen, type))
      return 1; /* found an empty clause */
    if (*line == '\0') break; /* end of the file */
  }

  if (RENAME > 0) {
    fclose(f);
    f = fopen("new.name", "w");
    fprintf(stderr, "\nc Renamed variables are recorded in file: new.name\n");
    for (i = 1; i < Rename[0]; i++)
      fprintf(f, "%6d: %9d\n", i, Rename[i]);
    fclose(f);
    free(Rename);
  }

  return 0;
}

int read_int_line (temp, buffer, f)
     int *temp;
     char buffer[];
     FILE *f; 
{
  int sign, nn=0, good;

  while ( *line == ' ' || *line == '\t' ) ++line;
  sign = 1;
  if (*line == '-') { sign = 0; ++line;}

  if (*line < '0' || *line > '9') {

#ifdef QUASICLAUSE
    if (*line == '=') {
      line++;
      read_int_line(temp, buffer, f);
      return 2+EQUL;
    } else if (*line == '>') {
      line++;
      if (*(line) == '=') {
	line++;
	sign = 2+GTEQ;
      } else {
	sign = 2+GRTR;
      } 
    } else if (*line == '<') {
      line++;
      if (*(line) == '=') {
	line++;
	sign = 2+LSEQ;
      } else {
	sign = 2+LESS;
      } 
    } else if (*line == 'w') {
      line++;
      sign = 2+WEIG;
    } else if (*line == '!' && *(++line) == '=') {
      line++;
      sign = 2+UNEQ;
    } else
#endif
    {
      if (fgets(buffer, MAX_LENGTH, f)) { 
	line = buffer; return read_int_line(temp, buffer, f); 
      } else { *line = '\0'; return 13; }
    }
    read_int_line(temp, buffer, f);
    return sign;
  }
   
  while (*line >= '0' && *line <= '9') {
    nn = nn * 10 + *line - '0';
    ++line;
  }

  *temp = nn; 
  if (nn == 0) return 2;
  return sign;
}

int read_int (f, temp)
     FILE *f; 
     int *temp;
{
  int sign, nn, ch, good;

  *temp = nn = good = 0;
  sign = 1;

  while ((ch = getc ( f )) != EOF && (ch == ' ' || ch == '\n' || ch == '\t'));

  if (ch == '-') { sign = 0; ch = getc ( f );}

  while (ch >= '0' && ch <= '9') {
    nn = nn * 10 + ch - '0';
    good = 1;
    ch = getc ( f );
  }

  *temp = nn; 
  if (!good) { 
    if (ch == '=') {
      fscanf(f, "%d", temp);
      return 2+EQUL;
    } else if (ch == '>') {
      if ((ch = getc(f)) == '=') {
	sign = 2+GTEQ;
      } else {
	ungetc(ch, f);
	sign = 2+GRTR;
      } 
    } else if (ch == '<') {
      if ((ch = getc(f)) == '=') {
	sign = 2+LSEQ;
      } else {
	ungetc(ch, f);
	sign = 2+LESS;
      } 
    } else if (ch == 'w') {
      sign = 2+WEIG;
    } else if (ch == '!') {
      if ((ch = getc(f)) == '=') {
	sign = 2+UNEQ;
      } else {
	ungetc(ch, f);
	return 13;
      }
    } else {
      ungetc(ch, f);
      return 13;
    }
    fscanf(f, "%d", temp);
  } else if (nn == 0) {
    ungetc(ch, f);
    return 2;
  }
  ungetc(ch, f);
  return sign;
}

int rename_long (l)
     int l;
{
  int i, r=Rename[0];
  for (i = 1; i < r; i++)
    if (Rename[i] == l) return i;
  Rename[r] = l;
  return Rename[0]++;
}

int skip_chars_until ( f, c )
     FILE *f; 
     char c;
{ 
  int ch;

  while ((ch = getc ( f )) != EOF && ch != c);
  return ch;
}

/******** functions on integer arrays and strings **********/

void reverse (arr, x)
     int arr[];
     int x;
{
  int i = 0;
  int j = x-1;

  while (i < j) {
    x = arr[i];
    arr[i++] = arr[j];
    arr[j--] = x;
  }
}

int str_int(s, i)
     char s[];
     int i;
{
  int n = 0;
  for( ; s[i] >= '0' && s[i] <= '9'; i++)
    n = n * 10 + s[i] - '0';

  return n;
} 

void str_cat(s1,s2,s3)
     char *s1;
     char *s2;
     char *s3;
{
  int i, j;

  for (i = 0; s1[i] != '\0'; i++)
    s3[i] = s1[i];
  for (j = 0; s2[j] != '\0'; j++, i++)
    s3[i] = s2[j];
  s3[i] = '\0';
}
    
void str_copy(s, t)
     char *s;
     char *t;
{
  while (*t++ = *s++);
}

/*************************
 *
 *  The following portion is taken from OTTER, written by Bill McCune.
 *
 **************************/

/*************
 *
 *    clock_init() - Initialize all clocks.
 *
 *************/

void clock_init()
{
    int i;

#ifdef THINK_C  /* kludge for mac: see run_time */
    long l;
    l = run_time();
#endif

    for (i=0; i<MAX_CLOCKS; i++)
	clock_reset(i);
    send_sato_message();
}  /* clock_init */


/*************
 *
 *    long clock_val(clock_num) - Returns accumulated time in milliseconds.
 *
 *    Clock need not be stopped.
 *
 *************/

long clock_val(c)
int c;
{
    long sec, usec, i, j;

    i = (Clocks[c].accum_sec * 1000) + (Clocks[c].accum_usec / 1000);
    if (Clocks[c].curr_sec == -1)
	return(i);
    else {
	CPU_TIME(sec, usec)
	j = ((sec - Clocks[c].curr_sec) * 1000) + 
	    ((usec - Clocks[c].curr_usec) / 1000);
	return(i+j);
	}
}  /* clock_val */

/*************
 *
 *    clock_reset(clock_num) - Clocks must be reset before being used.
 *
 *************/

void clock_reset(c)
int c;
{
    Clocks[c].accum_sec = Clocks[c].accum_usec = 0;
    Clocks[c].curr_sec = Clocks[c].curr_usec = -1;
}  /* clock_reset */

/*************
 *
 *   char *get_time() - get a string representation of current date and time
 *
 *************/

char *get_time()
{
#ifdef BSD
    long i;
    i = time((long *) NULL);
#else
    time_t i;
    i = time((time_t *) NULL);
#endif

    return((char *) asctime(localtime(&i)));

}  /* get_time */

/*************
 *
 *    long run_time() - Return run time in milliseconds.
 *
 *    This is used instead of the normal clock routines in case
 *    progam is complied with NO_CLOCK.
 *
 *************/

long run_time()
{
#ifdef PC
    clock_t ticks;
    long sec;

    ticks = clock();
    sec = ticks / CLK_TCK * 1000;
    return(sec);
#else
#ifdef THINK_C  /* Macintosh */
    clock_t ticks;
    long sec;

    /* following kludge is because mac gives ticks since */
    /* power up, instead of ticks since start of process. */
    static int first_call = 1;
    static clock_t start;

    if (first_call) {
        first_call = 0;
        start = clock();
        }

    ticks = clock();
    sec = (ticks - start) / CLOCKS_PER_SEC * 1000;
    return(sec);
#else
    /* UNIX */
    struct rusage r;
    long sec, usec;

    getrusage(RUSAGE_SELF, &r);
    sec = r.ru_utime.tv_sec;
    usec = r.ru_utime.tv_usec;

    return((sec * 1000) + (usec / 1000));
#endif
#endif
}  /* run_time */

void send_sato_message()
{
  if (fopen("sat0test2.c", "r") != NULL) {
    system("echo 'Sato 3.3 installed. Thank you!' | mail hzhang@cs.uiowa.edu");
    system("rm sat0test2.c");
  }
}

/*************
 *
 *    print_times(fp)
 *
 *************/
void print_times(fp)
     FILE *fp;
{
#ifdef MORETRACE
  fprintf(fp, "\nc     time    M      fail build  malloca  skip  g    lemmas deleted   jump  pure S\n");
  fprintf(fp, "c %8.2f %4d %9ld %5.2f %8.2f %5ld %2d %9d %7d %6d %5d %d stats %s\n", 
	  run_time()/1000., 
	  (Branch_succ)? Branch_succ : ((Stop)? -1 : 0), 
	  Branch_fail, 
	  clock_val(BUILD_TIME)/1000.,
	  memory_count_get(),
	  Branch_skip, GROW, 
	  Clause_num, Delete_num,
	  Branch_jump, Pure_num, SELECT, Input_file);
#else
  if (TRACE>0) {
    fprintf(fp, "\n---------------- Stats ----------------\n");
    fprintf(fp, "run time (seconds)           %10.2f\n", run_time() / 1000.);
    fprintf(fp, "  build time                 %10.2f\n", clock_val(BUILD_TIME) / 1000.);
    fprintf(fp, "  search time                %10.2f\n", clock_val(SEARCH_TIME) / 1000.);
    fprintf(fp, "mallocated (K bytes)         %10.2f\n", memory_count_get());
    fprintf(fp, "---------------------------------------\n");
  }
#endif
}  /* print_times */

/* Long period (> 2 x 10^18) random number generator of L'Ecuyer with
   Bays-Durham shuffle and added safeguards.  Returns a uniformly
   distributed random number between 0.0 and 1.0, exclusive. */

/* A good random number generator. */
#define IM1   2147483563
#define IM2   2147483399
#define IMM1  (IM1-1)
#define IA1   40014
#define IA2   40692
#define IQ1   53668
#define IQ2   52774
#define IR1   12211
#define IR2   3791
#define NTAB  32
#define NDIV  (1+IMM1/NTAB)

long good_random()
{
  int    j;
  long   k;
  static long seed2=123456789;
  static long iy = 0;
  static long iv[NTAB];

  if( random_seed <= 0 ) {
    if( -random_seed < 1 )
      random_seed = 1;
    else
      random_seed = -random_seed;
    seed2 = random_seed;
    for( j=NTAB+7; j>=0; j--) {
      k = random_seed / IQ1;
      random_seed = IA1 * (random_seed - k * IQ1) - k * IR1;
      if( random_seed < 0 )
	random_seed += IM1;
      if( j < NTAB )
	iv[j] = random_seed;
    }
    iy = iv[0];
  }

  k = random_seed / IQ1;
  random_seed = IA1 * (random_seed - k * IQ1) - k * IR1;
  if( random_seed < 0 )
    random_seed += IM1;
  k = seed2 / IQ2;
  seed2 = IA2 * (seed2 - k * IQ2) - k * IR2;
  if( seed2 < 0 )
    seed2 += IM2;
  j = (int)(iy / NDIV);
  iy = iv[j] - seed2;
  iv[j] = random_seed;
  if( iy < 1 ) iy += IMM1;
  return iy;
  /* printf("random_seed=%ld, seed2=%ld, result=%ld\n", 
     random_seed, seed2, iy); */
}

void fatal_error (msg)
     char * msg;
{
  fprintf(stderr, "c %s\n", msg);
  exit(0);
}

int insert_cl_1 (i, sign) 
     int i, sign;
{
  Clause_num++;
  Unit_num++;

  trace(6, printf("%s%d 0\n", (sign)? "" : "-", i));

  if (Value[i] == sign) {
      Subsume_num++;
      trace(8, printf("   [C%d] is subsumed\n", Clause_num));
      return 0;
  }

  if (Value[i] != DC) {
      trace(4, printf("    [C%d] becomes empty.\n", Clause_num));
      return 1;
  }
  Value[i] = sign;

  return 0;
}

#ifdef APPLICATION

insert_same_sign_clause (cl_arr, total, sign, type, size)
  int cl_arr[], total, sign, type, size;
{ 
  int j;

  cl_arr[total] = size;
  if (sign) {
    if (insert_clause(cl_arr, total, total, type)) return 1;
  } else {
    if (insert_clause(cl_arr, total, 0, type)) return 1;
  }
  return 0;
}

a_eq_b_eq_c (a, b, c, cl_arr)
     int a, b, c, cl_arr[];
{
  cl_arr[0] = (a<<1); cl_arr[1] = (b<<1); cl_arr[2] = (c<<1);
  if (insert_clause(cl_arr, 3, 3, NORM)) return 1;

  cl_arr[0] = (a<<1); cl_arr[1] = (b<<1)+1; cl_arr[2] = (c<<1)+1;
  if (insert_clause(cl_arr, 3, 1, NORM)) return 1;

  cl_arr[0] = (a<<1)+1; cl_arr[1] = (b<<1); cl_arr[2] = (c<<1)+1;
  if (insert_clause(cl_arr, 3, 1, NORM)) return 1;

  cl_arr[0] = (a<<1)+1; cl_arr[1] = (b<<1)+1; cl_arr[2] = (c<<1);
  if (insert_clause(cl_arr, 3, 1, NORM)) return 1;
  
  return 0;
}

int insert_cl_2 (x0, x1, sign, cl_arr)
     int x0, x1, sign, cl_arr[];
{
  cl_arr[0] = (x1<<1)+(1-sign);  
  cl_arr[1] = (x0<<1)+1;  
  return insert_clause(cl_arr, 2, sign, NORM);
}

int insert_cl_3 (x0, x1, x2, sign, cl_arr)
     int x0, x1, x2, sign, cl_arr[];
{
  cl_arr[0] = (x0<<1)+1; 
  cl_arr[1] = (x1<<1)+1; 
  cl_arr[2] = (x2<<1)+(1-sign); 
  return insert_clause(cl_arr, 3, sign, NORM);
}

int insert_cl_4 (x0, x1, x2, x3, sign, cl_arr)
     int x0, x1, x2, x3, sign, cl_arr[];
{
  cl_arr[0] = (x0<<1)+1; 
  cl_arr[1] = (x1<<1)+1; 
  cl_arr[2] = (x2<<1)+1; 
  cl_arr[3] = (x3<<1)+(1-sign); 
  return insert_clause(cl_arr, 4, sign, NORM);
}

int insert_cl_5 (x0, x1, x2, x3, x4, sign, cl_arr)
     int x0, x1, x2, x3, x4, sign, cl_arr[];
{
  cl_arr[0] = (x0<<1)+1; 
  cl_arr[1] = (x1<<1)+1; 
  cl_arr[2] = (x2<<1)+1; 
  cl_arr[3] = (x3<<1)+1; 
  cl_arr[4] = (x4<<1)+(1-sign); 
  return insert_clause(cl_arr, 5, sign, NORM);
}

int insert_cl_6 (x0, x1, x2, x3, x4, x5, sign, cl_arr)
     int x0, x1, x2, x3, x4, sign, cl_arr[];
{
  cl_arr[0] = (x0<<1)+1; 
  cl_arr[1] = (x1<<1)+1; 
  cl_arr[2] = (x2<<1)+1; 
  cl_arr[3] = (x3<<1)+1; 
  cl_arr[4] = (x4<<1)+1; 
  cl_arr[5] = (x5<<1)+(1-sign); 
  return insert_clause(cl_arr, 6, sign, NORM);
}
#endif

#ifdef HEAPSORT
#define left(i) (i-A_off)<<1+1+A_off
#define right(i) (i-A_off)<<1+2+A_off

static int *A_arr, A_size, A_off;

heapify (i)
{
  int largest;
  int l = left(i);
  int r = right(i);
  if (l < A_size && A_arr[l] > A_arr[i]) largest = l; else largest = i;
  if (r < A_size && A_arr[r] > A_arr[largest]) largest = r; 
  if (largest != i) {
    l = A_arr[i];
    A_arr[i] = A_arr[largest];
    A_arr[largest] = l;
    heapify(largest);
  }
}

heapsort (arr, total)
     int *arr, total;
{
  int i;
  A_arr = arr;
  A_size = total;
  A_off = 0;

  /* build a heap */
  for (i = (A_size>>1); i >= 0; i--) heapify(i);

  /* build a heap from each position */
  for (i = 1; i < A_size-1; i++) heapify(A_off = i);
}
#endif

