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

long *Rename = NULL;
int Rename_idx = 0;

void print_model (f)
     FILE *f;
{
  int i, col, row;

#ifdef BENCHMARK
  if (!RANDOM && PMD) {
    print_pmd_model(f);
  } else if (TEAM) {
    print_bigten_schedule();
  } else if (OARRAY) {
    print_oarray_model(f);
  } else if (!RANDOM && QGROUP) {
    if (CYCLIC)
      print_cyclic_model(f); 
    else 
      print_qgroup_model(f); 
  } else if (!RAMSEY && (QUEEN || INCOMPLETE)) {
    fprintf(f, "\nModel #%ld:", Branch_succ);
    col = QUEEN; row = 0;
    if (col == 0) col = INCOMPLETE;
    for (i = 1; i <= Max_atom; i++) if (Value[i] == TT) { 
      fprintf(f, "  %2d", (i-1) % col);
      if ( ++row == 50 ) { 
	row = 0; 
	fprintf(f, "\n    " ); 
      }
    }
  } else 
#endif
  {

    fprintf(f, "\nModel #%ld:", Branch_succ);
    if (TRACE < 5) 
      fprintf(f, " (indices of true atoms)\n\n    " );
    else 
      fprintf(f, "\n\n    " );

    if (LINE <= 1) {
      for (i = 1; i <= Max_atom; i++)
	if (TRACE < 5) {
	  if (Value[i] == TT) {
	    fprintf(f, "%d  ", i);
	  }
	} else
	  fprintf(f, "%s%d  ",  (Value[i] == TT)? "" : "-", i); 
    } else {
      col = row = 0;
      for (i = 1; i <= Max_atom; i++) {
	if (TRACE < 5) {
	  if (Value[i] == TT) { 
	    fprintf(f, "%d  ", i);
	    ++col; 
	  }
	} else { 
	  fprintf(f, "%s%d  ",  (Value[i] == TT)? "" : "-", i); 
	  ++col; 
	}

	if ( col == LINE ) {
	  col = 0;  fprintf(f, "\n    " );
	  if ( ++row == LINE ) { 
	    row = 0; 
	    if (i < Max_atom) fprintf(f, "\n    " ); 
	  }
	}
      }
    }
    fprintf(f, "\n");
  }
}

void print_clause (arr, sign, total)
     int arr[], sign[];
     int total;
{
  fprint_clause (Sato_fp, arr, sign, total);
}

void fprint_clause (f, arr, sign, total)
     FILE *f;
     int arr[], sign[];
     int total;
{
  Printed_clause++;
  if (OUTPUT == 8) {
    fprintf (f, "( " );
    total--;
    while ( total >= 0 ) {
      if (sign[arr[total]] == 0) fprintf(f, "~");
      fprintf (f, "%d ", arr[total] );
      if (total--) fprintf(f, " | ");
    }
    fprintf(f, ")&\n"); 
  } else {

    if (OUTPUT < 5) fprintf (f, "( " );
    total--;
    while ( total >= 0 ) {
      if (sign[arr[total]] == 0) fprintf(f, "-");
      fprintf (f, "%d ", arr[total--] );
    }
    if (OUTPUT < 5) fprintf(f, ")\n"); else fprintf(f, "0\n");
  }
}

void print_unit_clause (fp, sign, i)
     FILE *fp; int sign, i;
{ 
  Printed_clause++;
  if (OUTPUT < 5)
    fprintf(fp, (sign == TT)? "( %d )\n" : "( -%d )\n", i);
  else if (OUTPUT < 8) 
    fprintf(fp, (sign == TT)? "%d 0\n" : "-%d 0\n", i);
  else 
    fprintf(fp, (sign == TT)? "( %d )&\n" : "( ~%d )&\n", i);
}

int insert_cl_1 (i, sign) 
     int i, sign;
{
  if (OUTPUT) print_unit_clause(Sato_fp, sign, i);

  Clause_num++;
  Unit_num++;

  if (Value[i] == sign) {
    Subsume_num++;

#ifdef MORETRACE
    if (TRACE > 7) printf("   [C%d] is subsumed\n", Clause_num);
#endif

    return 0;
  }

  if (Value[i] != DC) {

#ifdef MORETRACE
    if (TRACE > 4) printf("   [C%d] becomes empty!\n", Clause_num);
#endif
    bug(4);
    return 1;
  }

  assign_value(i, sign);

  return 0;
}

#ifdef BENCHMARK

int insert_cl_2 (a, b, sign, cl_arr, sign_arr) 
     int a, b, sign, cl_arr[], sign_arr[];
{
  int total;

  Clause_num++;
  cl_arr[0] = a; sign_arr[cl_arr[0]] = 0;
  if ((total = insert_one_key(b, sign, cl_arr, sign_arr, 1)) == 0)
    Subsume_num++;
  else if (qg_insert_clause( cl_arr, sign_arr, total) == 1)
    return 1;
  return 0;
}

int insert_cl_all_3 (a, b, c, all, cl_arr, sign_arr) 
     int a, b, c, all, cl_arr[], sign_arr[];
{
  int total;

  total = 0;
  if (total) {
    if (all == 0) return 0;
    Clause_num++;
    cl_arr[0] = a; sign_arr[cl_arr[0]] = 0;
    if ((total = insert_one_key(b, 0, cl_arr, sign_arr, 1)) == 0)
      Subsume_num++;
    else if (qg_insert_clause( cl_arr, sign_arr, total) == 1)
      return 1;
    return 0;
  }

  Clause_num++;
  cl_arr[0] = c;
  sign_arr[cl_arr[0]] = (all)? 1: 0;
  if ((total = insert_one_key(a, 0, cl_arr, sign_arr, 1)) == 0)
    Subsume_num++;
  else if ((total = insert_one_key(b, 0, cl_arr, sign_arr, total)) == 0)
    Subsume_num++;
  else if (qg_insert_clause( cl_arr, sign_arr, total) == 1)
    return 1;

  if (all < 2 || PIGEON == 1) return 0;

  Clause_num++;
  cl_arr[0] = a;
  sign_arr[cl_arr[0]] = 0;
  if ((total = insert_one_key(b, 1, cl_arr, sign_arr, 1)) == 0)
    Subsume_num++;
  else if ((total = insert_one_key(c, 0, cl_arr, sign_arr, total)) == 0)
    Subsume_num++;
  else if (qg_insert_clause( cl_arr, sign_arr, total) == 1)
    return 1;

  Clause_num++;
  cl_arr[0] = a;
  sign_arr[cl_arr[0]] = 1;
  if ((total = insert_one_key(b, 0, cl_arr, sign_arr, 1)) == 0)
    Subsume_num++;
  else if ((total = insert_one_key(c, 0, cl_arr, sign_arr, total)) == 0)
    Subsume_num++;
  else if (qg_insert_clause( cl_arr, sign_arr, total) == 1)
    return 1;

  return 0;
}

int insert_cl_4 (a, b, c, d, all, cl_arr, sign_arr) 
     int a, b, c, d, all, cl_arr[], sign_arr[];
{
  int total;

  total = 0;
  
  if (total) {
    if (all == 0) return 0;
    Clause_num++;
    cl_arr[0] = a; sign_arr[cl_arr[0]] = 0;
    if ((total = insert_one_key(b, 0, cl_arr, sign_arr, 1)) == 0)
      Subsume_num++;
    else if ((total = insert_one_key(c, 0, cl_arr, sign_arr, total)) == 0)
      Subsume_num++;
    else if (qg_insert_clause( cl_arr, sign_arr, total)) return 1;
    return 0;
  }

  Clause_num++;
  cl_arr[0] = d;
  sign_arr[cl_arr[0]] = (all)? 1 : 0;
  if ((total = insert_one_key(a, 0, cl_arr, sign_arr, 1)) == 0)
    Subsume_num++;
  else if ((total = insert_one_key(b, 0, cl_arr, sign_arr, total)) == 0)
    Subsume_num++;
  else if ((total = insert_one_key(c, 0, cl_arr, sign_arr, total)) == 0)
    Subsume_num++;
  else if (qg_insert_clause( cl_arr, sign_arr, total) == 1) return 1;

  if (all < 2) return 0;

  Clause_num++;
  cl_arr[0] = a;
  sign_arr[cl_arr[0]] = 0;
  if ((total = insert_one_key(b, 0, cl_arr, sign_arr, 1)) == 0)
    Subsume_num++;
  else if ((total = insert_one_key(c, 1, cl_arr, sign_arr, total)) == 0)
    Subsume_num++;
  else if ((total = insert_one_key(d, 0, cl_arr, sign_arr, total)) == 0)
    Subsume_num++;
  else if (qg_insert_clause( cl_arr, sign_arr, total) == 1)
    return 1;

  Clause_num++;
  cl_arr[0] = a;
  sign_arr[cl_arr[0]] = 0;
  if ((total = insert_one_key(b, 1, cl_arr, sign_arr, 1)) == 0)
    Subsume_num++;
  else if ((total = insert_one_key(c, 0, cl_arr, sign_arr, total)) == 0)
    Subsume_num++;
  else if ((total = insert_one_key(d, 0, cl_arr, sign_arr, total)) == 0)
    Subsume_num++;
  else if (qg_insert_clause( cl_arr, sign_arr, total) == 1)
    return 1;

  Clause_num++;
  cl_arr[0] = a;
  sign_arr[cl_arr[0]] = 1;
  if ((total = insert_one_key(b, 0, cl_arr, sign_arr, 1)) == 0)
    Subsume_num++;
  else if ((total = insert_one_key(c, 0, cl_arr, sign_arr, total)) == 0)
    Subsume_num++;
  else if ((total = insert_one_key(d, 0, cl_arr, sign_arr, total)) == 0)
    Subsume_num++;
  else if (qg_insert_clause( cl_arr, sign_arr, total) == 1)
    return 1;

  return 0;
}

int insert_cl_5 (a, b, c, d, e, sign, cl_arr, sign_arr) 
     int a, b, c, d, e, sign, cl_arr[], sign_arr[];
{
  int total;

  total = 0;

  Clause_num++;
  cl_arr[0] = a;
  sign_arr[cl_arr[0]] = 0; 
  if ((total = insert_one_key(b, 0, cl_arr, sign_arr, 1)) == 0)
    Subsume_num++;
  else if ((total = insert_one_key(c, 0, cl_arr, sign_arr, total)) == 0)
    Subsume_num++;
  else if ((total = insert_one_key(d, 0, cl_arr, sign_arr, total)) == 0)
    Subsume_num++;
  else if ((total = insert_one_key(e, (sign)? 1: 0, 
				   cl_arr, sign_arr, total)) == 0)
    Subsume_num++;
  else if (qg_insert_clause( cl_arr, sign_arr, total) == 1) return 1;

  return 0;
}

int insert_cl_6 (a, b, c, d, e, f, sign, cl_arr, sign_arr) 
     int a, b, c, d, e, f, sign, cl_arr[], sign_arr[];
{
  int total;

  total = 0;

  Clause_num++;
  cl_arr[0] = a;
  sign_arr[cl_arr[0]] = 0;
  if ((total = insert_one_key(b, 0, cl_arr, sign_arr, 1)) == 0)
    Subsume_num++;
  else if ((total = insert_one_key(c, 0, cl_arr, sign_arr, total)) == 0)
    Subsume_num++;
  else if ((total = insert_one_key(d, 0, cl_arr, sign_arr, total)) == 0)
    Subsume_num++;
  else if ((total = insert_one_key(e, 0, cl_arr, sign_arr, total)) == 0)
    Subsume_num++;
  else if ((total = insert_one_key(f, (sign)? 1 : 0, 
				   cl_arr, sign_arr, total)) == 0)
    Subsume_num++;
  else if (qg_insert_clause( cl_arr, sign_arr, total) == 1) return 1;

  return 0;
}
#endif

int insert_clause ( cl_arr, sign_arr, total )             
     int cl_arr[], sign_arr[];
     int total;
{
  int j, i, k, p = 0;
  
  if (cl_arr[0] > Max_atom) bug(11);
  if (OUTPUT == 1 || OUTPUT == 4 || OUTPUT == 7) 
    print_clause(cl_arr, sign_arr, total);

  /* check for literals and clauses subsumed by unit clauses */
  j = 0;
  for (i = 0; i < total; i++) {
    k = cl_arr[i];
    if (Value[k] == DC) {
      cl_arr[j] = k;
      if (sign_arr[cl_arr[j++]] == TT) p++;
    } else if (Value[k] == sign_arr[k]) { /* the clause is subsumed */
      Subsume_num++;

#ifdef MORETRACE
      if (TRACE > 7)
	fprintf(Sato_fp, "      [C%ld] is subsumed by unit clause (%d).\n",
		Clause_num, (Value[k])? k : -k);
#endif
      return 0;

    } else { /* the literal is subsumed */

#ifdef MORETRACE
      if (TRACE > 7)
	fprintf(Sato_fp, "    %d in [C%ld] is skipped due to a unit clause.\n",
		k, Clause_num);
#endif
    }
  }
  total = j;

  if (total == 0) {

#ifdef MORETRACE
    if (TRACE > 6)
      fprintf(Sato_fp, "    [C%ld] becomes empty.\n", Clause_num);
#endif

    bug(4);
    return 1;
  }

  if (total == 1) { /* a unit clause is found */

    j = cl_arr[0];
    assign_value(j, sign_arr[j]);
    Unit_num++;
    if (OUTPUT) print_unit_clause(Sato_fp, Value[j], j);

#ifdef MORETRACE
    if (TRACE > 7 || TRACE == 4)
      fprintf (Sato_fp, "    x%d is set to %d by unit clause.\n",
	       j, Value[j]);
#endif

    return 0;
  }

  if (total == 3) Trcl_num++;
  else if (total == 2) Bicl_num++;
  if (p > 1) NH_num++;

  if (OUTPUT == 3 || OUTPUT == 6 || OUTPUT == 8) 
    print_clause(cl_arr, sign_arr, total);

  if (DATA == 1) 
    return list_insert_clause(cl_arr, sign_arr, total);
  else 
    return trie_insert_clause(cl_arr, sign_arr, total);
}

int read_one_clause ( f, cl_arr, sign_arr, tautology, mark )
     FILE *f; 
     int cl_arr[], sign_arr[];
     int *tautology;
     long mark[];
{
  int total, sign, i;
  *tautology = 0;

  total = 0;
  sign = (RENAME > 0)? read_long( f, &i ) : read_int( f, &i );

  while ( sign != 2 && sign != 3 ) { 

    if (i > Act_max_atom && (Act_max_atom = i) > Max_atom) {
      fprintf ( stderr, "Atom %d > Max_atom(=%d).\n",
	       i, Max_atom);
      exit(0);
    } 

    if (mark == NULL) {
      cl_arr [ total++ ] = i;
      sign_arr [ i ] = sign;
      sign = (RENAME > 0)? read_long( f, &i ) : read_int( f, &i );
    } else if (PREP == 1) {
      if ((total = insert_one_key(i, sign, cl_arr, sign_arr, total)) == 0) {
	*tautology = 1;
	sign = 2;
      } else {
	sign = (RENAME > 0)? read_long( f, &i ) : read_int( f, &i );
      }
    } else if (mark[i] == Clause_num) { /* duplicate atoms */
      if (sign_arr[i] != sign) { /* a tautology is found */
	*tautology = 1;
	sign = 2;
      } else { /* skip the same literal */
	sign = (RENAME > 0)? read_long( f, &i ) : read_int( f, &i );
      }
    } else { /* new atom */
      cl_arr [ total++ ] = i;
      sign_arr [ i ] = sign;
      mark[i] = Clause_num;
      sign = (RENAME > 0)? read_long( f, &i ) : read_int( f, &i );
    }
  }

  if (*tautology) {
    if (FORMAT == 1) {
      skip_chars_until(f, ')');
    } else {
      sign = 1;
      while (sign != 2 && sign != 3)
	sign = (RENAME > 0)? read_long( f, &i ) : read_int( f, &i );
      if (sign == 3) {
	printf("\nWARNING: Clause %ld is not ended by 0\n\n", Clause_num);
      } 
    }
    return 0;
  } else if (FORMAT == 1) {
    if (sign == 2 || getc(f) != ')') {
      skip_chars_until(f, ')');
#ifdef MORETRACE
      if (TRACE > 6) 
	fprintf(Sato_fp, "      [C%ld] is a bad clause and is ignored.\n", Clause_num);
#endif
      return -1;
    }
  } else if (sign != 2) {
#ifdef MORETRACE
      if (TRACE > 6) 
	fprintf(Sato_fp, "      [C%ld] is a bad clause and is ignored.\n", Clause_num);
#endif
      return -1;
  }

  return total;
}

int input_clauses ( f )
     /* return 1 if an empty clause is found; otherwise, 0 */
     FILE *f; 
{
  if (f == NULL) {
    fprintf(stderr, "the input file is null\n");
  } else {
    int total_lits, ch, i, tautology;
    long mark[MAX_ATOM];
  
    if (RENAME > 0) {
      Rename = (long *) malloc((MAX_ATOM) * (sizeof(long)));
      for (i = 0; i < RENAME; i++) Rename[i] = i;
      Rename_idx = RENAME;
    }
      
    for (i = 0; i <= Max_atom; i++) mark[i] = MAX_ATOM;
    ch = getc ( f );  

    while ( ch != EOF ) {
      int cl_arr [ MAX_ATOM ], sign_arr [ MAX_ATOM ];

      if (FORMAT == 0 && (ch <= 'z' && ch >= 'a')) 
	ch = skip_chars_until( f, '\n' ); 

      if ( FORMAT == 0 || ch == '(' ) {
	tautology = 0;
	Clause_num++;
	total_lits = read_one_clause( f, cl_arr, sign_arr, &tautology, mark );

	if (tautology == 1) {
	  Subsume_num++;
#ifdef MORETRACE
	  if (TRACE > 6) 
	    fprintf(Sato_fp, "      [C%ld] is a tautology.\n", Clause_num);
#endif
	} else if (total_lits > 0) {

	  if (PREP != 1) reverse(cl_arr, total_lits);
	  if (insert_clause ( cl_arr, sign_arr, total_lits)) {
	    if (OUTPUT < 5) Max_atom = Act_max_atom;
	    return 1;
	  }
	} else if (total_lits == 0) {
	  return 1;   /* empty clause */
	} else
	  Clause_num--; /* bad clause */
      }

      ch = getc ( f );                /* skip it */
    }

    if (RENAME > 0) {
      fclose(f);
      f = fopen("new.name", "w");
      fprintf(stderr, "\nRenamed variables are recorded in file: new.name\n");
      for (i = 1; i < Rename_idx; i++)
	fprintf(f, "%7d: %10ld\n", i, Rename[i]);
      fclose(f);
      free(Rename);
    }

  }
  if (OUTPUT < 5) Max_atom = Act_max_atom;
  return 0;
}

int insert_one_key (key, sign, cl_arr, sign_arr, total)
     int key, sign, total;
     int cl_arr[], sign_arr[];
     /* insert a literal into the current clause.
	return 0 if a tautology is found.
	ignore duplicate literals.
	return the length of the current clause. */
{
  int i, j;

  for (j = 0; j < total; j++)
    if (key > cl_arr[j]) {
      for (i = total; i > j; i--)
	cl_arr[i] = cl_arr[i-1];
      cl_arr[j] = key;
      sign_arr[key] = sign;
      return total+1;
    } else if (key == cl_arr[j]) {
      if (sign == sign_arr[key])
	return total;
      else 
	return 0;
    }
  
  cl_arr[total] = key;
  sign_arr[key] = sign;
  return total+1;
}

int read_long (f, i)
     FILE *f; 
     int *i;
{
  int sign, ch, good;
  long nn;

  *i = nn = good = 0;
  sign = 1;

  while ((ch = getc ( f )) != EOF && (ch == ' ' || ch == '\n' || ch == '\t'));

  if (ch == '-') { sign = 0; ch = getc ( f );}

  while (ch >= '0' && ch <= '9') {
    nn = nn * 10 + ch - '0';
    good = 1;
    ch = getc ( f );
  }

  ungetc(ch, f);
  *i = rename_long(nn); 
  if (good == 0) { /* printf("!!!%c!!!", ch); */ return 3; }
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

  ungetc(ch, f);
  *temp = nn; 
  if (good == 0) { /* printf("!!!%c!!!", ch); */ return 3; }
  if (nn == 0) return 2;
  return sign;
}

int rename_long (l)
     long l;
{
  int i;
  for (i = 0; i < Rename_idx; i++)
    if (Rename[i] == l) return i;
  Rename[Rename_idx] = l;
  return Rename_idx++;
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

int insert_sorter (arr, last)
     int arr[];
     int last;
{
  int x, y, i, j;

  for (i = 1; i < last; i++) {
    x = arr[i];
    y = arr[i-1];
    j = i;
    while (y < x) {
      arr[j--] = y;
      y = (j)? arr[j-1] : MAX_SHORT;
    }
    if (x == y) {
      for (x = j; x < last-1; x++) arr[x] = arr[x+1];
      i--; last--;
    } else
      arr[j] = x;
  }
  return last;
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
