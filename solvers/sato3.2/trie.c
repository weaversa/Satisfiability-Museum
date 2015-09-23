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
#include "trie.h"
#include "weight.h"
#include "stack.h"
#include "slot.h"
#include "trie2.h"
#include "trie3.h"
#include "trie4.h"

void trie_init_once_forall ()
{
  /*
  if (sizeof(struct trie) % sizeof(int *)) 
    printf("\nWARNING: sizeof(struct trie) = %d\n", sizeof(struct trie));
  if (sizeof(struct var2) % sizeof(int *)) 
    printf("\nWARNING: sizeof(struct var2) = %d\n", sizeof(struct var2));
  if (sizeof(struct var3) % sizeof(int *)) 
    printf("\nWARNING: sizeof(struct var3) = %d\n", sizeof(struct var3));
  if (sizeof(struct cap) % sizeof(int *)) 
    printf("\nWARNING: sizeof(struct cap) = %d\n", sizeof(struct cap));
  */

  V2 = NULL;
  V3 = NULL;
  CLtrie = NHtrie = Newtrie = Root = NULL;
  /* Trie_news = Trie_frees = Trie_gets = Trie_avails = 0; */
  Trie_avail = NULL;
  BItrie = CLAUSE_MARK = get_trie();
  Unit_avail = NULL;

  V4 = NULL;
  Gclause_New = NULL;
  Gclause_New_idx = 0;
}

void init_trie ()
{
  free_trie(Root); 
  free_trie(NHtrie); 
  free_trie(Newtrie); 
  free_trie(CLtrie);  
  Old_cls = NULL;
  Root = CLtrie = Newtrie = NHtrie = NULL;
  Backup_idx = 0;
  Top_var2 = NULL;
  Top_var3 = NULL;
  NH_num = Jump_num = Pure_num = Clause_extra_num = 0;
  Miss_num = 0;
}

int trie_in_path (i, no)
     int i;
     struct trie *no;
{
  while (no && key_of(no) > i) no = no->par;
  if (no && key_of(no) == i) return 1;
  return 0;
}

struct trie *trie_create_one_path (arr, signs, count)
     int arr[], signs[], count;
{
  int sign;
  struct trie *first, *pre, *no;

  first = no = get_trie(); 
  set_key(no, arr[count]); 
  sign = signs[key_of(no)];
  while (--count >= 0) {
    pre = no;
    no = get_trie();
    if (sign) pre->pos = no;
    else pre->neg = no;
    set_key(no, arr[count]); 
    sign = signs[key_of(no)];
  }
  if (sign)
    no->pos = CLAUSE_MARK;
  else
    no->neg = CLAUSE_MARK;
  return first;
}

int trie_insert_clause ( cl_arr, sign_arr, total )             
     int cl_arr[], sign_arr[], total;
{
  if (Root == CLAUSE_MARK) return 1;

  if (total > 0) 
    Root = trie_insert_clause2(Root, cl_arr, sign_arr, total-1);

  if (total == 0 || Root == CLAUSE_MARK) { /* an empty clause is found */

#ifdef MORETRACE
    if (TRACE > 6)
      fprintf(Sato_fp, "    [C%ld] becomes empty.\n", Clause_num);
#endif

    bug(4);
    free_trie(Root);
    Root = CLAUSE_MARK;
    return 1;
  }
  /*print_trie(Root);*/
  return 0;
}

struct trie *trie_insert_clause2 (root, arr, signs, count)
     struct trie *root; /* current root of the tree */
     int arr[], signs[]; /* current clause */
     int count; /* the length of the current clause */
{
  int key;
  int sign, dep;
  struct trie *no, *bro1, *bro2, *pars[MAX_LENGTH];
  static struct trie *roots[MAX_ATOM];

  if (root == NULL)
    for (dep = 0; dep <= Max_atom; dep++) roots[dep] = NULL;

  key = arr[count];

  if (roots[key] == NULL) {

    if (INSEARCH) {
      for (dep = key-1; dep >= 0; dep--) {
	if (roots[dep] != NULL) {
	  return trie_insert_clause_end(roots[dep], arr, signs, count);
	}
      }
      return trie_insert_clause_end(root, arr, signs, count);
    }


    roots[key] = no = trie_create_one_path (arr, signs, count);
    for (dep = key-1; dep >= 0; dep--) {
      if (roots[dep] != NULL) {
	no->bro = roots[dep]->bro;
	roots[dep]->bro = no;
	return root;
      }
    }
    no->bro = root;
    return no;
  }

  no = roots[key];

  if (INSEARCH) return trie_insert_clause_end(no, arr, signs, count);

  dep = 0;
  bro1 = bro2 = NULL;

  while (no != NULL && count >= 0) {
    key = arr[count];
    sign = signs[key]; 
    
    if (key == key_of(no)) {
      if (sign == 1) {

	if HAS_POS_CL(no) {
#ifdef MORETRACE
	  print_x_subsume;
#endif
	  Subsume_num++;
	  return root; /* skip this clause */

	} else if (trie_subsume_clause(no->neg, arr, signs, count)) {
#ifdef MORETRACE
	  print_x_skip;
#endif
	  count--;
	  bro1 = no;
	  no = no->bro; 
	} else {
	  count--;
	  pars[dep++] = no;
	  bro1 = NULL;
	  if (sign) no = no->pos; else no = no->neg;
	}
      } else { /* sign == 0 */

	if HAS_NEG_CL(no) {
#ifdef MORETRACE
	  print_x_subsume;
#endif
	  Subsume_num++;
	  return root; /* skip this clause */

	} else if (trie_subsume_clause(no->pos, arr, signs, count)) {
#ifdef MORETRACE
	  print_x_skip;
#endif
	  count--;
	  bro1 = no;
	  no = no->bro; 
	} else {
	  count--;
	  pars[dep++] = no;
	  bro1 = NULL;
	  if (sign) no = no->pos; else no = no->neg;
	}
      }
    } else if (key < key_of(no)) {
      bro2 = no;
      no = NULL;
    } else { /* (key > key_of(no)) */
      bro1 = no;
      no = bro1->bro;
      while ((no != NULL) && (key_of(no) < key)) {
	bro1 = no;
	no = bro1->bro;
      }
    }
  }

  if (count >= 0) {

    if (count == 0 && dep == 0) { /* a unit clause is found */ 
      key = arr[0];
      assign_value(key, signs[key]);
      Unit_num++;
      if (OUTPUT) print_unit_clause(Sato_fp, Value[key], key);

#ifdef MORETRACE
      if (TRACE > 7 || TRACE == 4)
	fprintf (Sato_fp, "    x%d is set to %d by unit clause.\n",
		 key, Value[key]);
#endif
      return root;
    }

    no = trie_create_one_path (arr, signs, count);
    no->bro = bro2;
    if (bro1 == NULL) {
      if (dep--) {
	if (signs[key_of(pars[dep])])
	  pars[dep]->pos = no;
	else 
	  pars[dep]->neg = no;
	return root;
      } else {
	return no;
      }
    } else {
      bro1->bro = no;
      if (dep == 0) roots[key_of(no)] = no;
      return root;
    }
  }

  /* count < 0 */
  while (dep--) {
    no = pars[dep];
    sign = signs[key_of(no)];

    if (dep == 0) { /* if at depth 0, no is unit clause */
      key = key_of(no);
      assign_value(key, sign);
      Unit_num++;

#ifdef MORETRACE
      if (TRACE > 7 || TRACE == 4)
	fprintf (Sato_fp, "    %sx%d is found be a unit clause.\n",
		 (sign)? "" : "-", key);
#endif
    }

    if (sign) {
      free_trie(no->pos);
      no->pos = CLAUSE_MARK;
    
      if (no->neg != NULL) {
	no->bro = merge_tries(no->bro, no->neg);
	no->neg = NULL;
      }
    } else {
      free_trie(no->neg);
      no->neg = CLAUSE_MARK;    
    
      if (no->pos != NULL) {
	no->bro = merge_tries(no->bro, no->pos);
	no->pos = NULL;
      }
    }
    
    if (no->bro != CLAUSE_MARK) return root;
  }
  return CLAUSE_MARK;
}

struct trie *trie_insert_clause_end (root, arr, signs, count)
     /* return the end of the clause */
     struct trie *root;
     int arr[], signs[], count;
{
  int total=count;
  int key;
  int sign;
  struct trie *no, *bro1, *bro2, *parent;

  parent = NULL;
  bro1 = bro2 = NULL;
  no = root;
  key = arr[count];
  sign = signs[key]; 

  while (no != NULL && count >= 0) {
    
    if (key == key_of(no)) {
      if HAS_POS_CL(no) {
	
	if (sign == 1) {

#ifdef MORETRACE
	  print_x_subsume;
#endif

	  return NULL; /* skip this clause */
	} /* otherwise sign = 0 */

#ifdef MORETRACE
	print_x_skip;
#endif

	bro1 = no;
	no = no->bro; 
      } else if HAS_NEG_CL(no) {
      
	if (sign == 0) {

#ifdef MORETRACE
	  print_x_subsume;
#endif

	  return NULL; /* skip this clause */
	} /* otherwise sign == 1 */

#ifdef MORETRACE
	print_x_skip;
#endif

	bro1 = no;
	no = no->bro; 
      } else {
	parent = no;
	bro1 = NULL;
	if (sign) no = no->pos; else no = no->neg;
      }

      if (count-->0) {
	key = arr[count];
	sign = signs[key]; 
      }

    } else if (key < key_of(no)) {
      bro2 = no;
      no = NULL;
    } else {
      bro1 = no;
      no = bro1->bro;
      while ((no != NULL) && (key_of(no) < key)) {
	bro1 = no;
	no = bro1->bro;
      }
    }
  }

  if (count >= 0) {
    no = get_trie(); 
    set_key(no, arr[count]); 
    no->par = parent;
    if (parent != NULL)
      set_psign(no, signs[key_of(no->par)]);
    no->bro = bro2;
    if (bro1 == NULL) {
      if (parent != NULL) {
	if (signs[key_of(no->par)])
	  no->par->pos = no;
	else 
	  no->par->neg = no;
      }
    } else {
      bro1->bro = no;
    }
    sign = signs[key_of(no)];
    while (--count >= 0) {
      bro1 = no;
      no = get_trie();
      if (sign) bro1->pos = no;
      else bro1->neg = no;
      no->par = bro1;
      set_key_psign(no, arr[count], sign);
      sign = signs[key_of(no)];
    }
  } else if (parent == NULL) {
    /* an empty clause is found */

#ifdef MORETRACE
    if (TRACE == 9) {
      printf("While inserting the clause:");
      print_clause(arr, signs, total);
    }
#endif

    return CLAUSE_MARK;
  } else {
    no = parent;
  }

  if (signs[key_of(no)]) {
    no->pos = CLAUSE_MARK;
    no->neg = NULL;
  } else {
    no->neg = CLAUSE_MARK;
    no->pos = NULL;
  }
  return no;
}

int trie_subsume_clause (no, arr, signs, count)
     struct trie *no;
     int arr[], signs[]; /* current clause */
     int count; /* the length of the current clause */
{
  int key;
  while (no != NULL) {
    if (no == CLAUSE_MARK) return 1;
    if (count > 0) key = arr[--count]; else return 0;
    if (key == key_of(no)) {
      if (signs[key] == 1) no = no->pos;
      else no = no->neg;
    } else if (key > key_of(no)) {
      no = no->bro;
      while ((no != NULL) && (key > key_of(no))) {
	no = no->bro;
      }
    }
  }
  return 0;
} /* trie_subsume_clause */


struct trie *merge_tries (n1, n2)
     struct trie *n1, *n2;  
     /* do lazy clean and complete merge */
{
    if (n2 == NULL) return n1;  
    if (n2 == CLAUSE_MARK) { free_trie(n1); return n2;}
    if (n1 == NULL) return n2;
    if (n1 == CLAUSE_MARK) { free_trie(n2); return n1;}
    
    if (key_of(n2) < key_of(n1)) {
    n2->bro = merge_tries(n1, n2->bro);
    if (n2->bro == CLAUSE_MARK) { free_trie(n2); return CLAUSE_MARK; }
    return n2;
  }

  if (key_of(n1) < key_of(n2)) {
    n1->bro = merge_tries(n1->bro, n2);
    if (n1->bro == CLAUSE_MARK) { free_trie(n1); return CLAUSE_MARK; }
    return n1;
  }

  /* now, key_of(n1) == key_of(n2) */
  n1->bro = merge_tries(n1->bro, n2->bro);
  n2->bro = NULL;
  if (n1->bro == CLAUSE_MARK) {
    free_trie(n1);
    free_trie(n2);
    return CLAUSE_MARK;
  }

  n1->pos = merge_tries(n1->pos, n2->pos);
  n1->neg = merge_tries(n1->neg, n2->neg);
  free_trie_cell(n2);

  if (n1->pos == CLAUSE_MARK) {
    n1->bro = merge_tries(n1->bro, n1->neg);
    n1->neg = NULL;
  }
  if (n1->neg == CLAUSE_MARK) {
    n1->bro = merge_tries(n1->bro, n1->pos);
    n1->pos = NULL;
  }

  if (n1->bro == CLAUSE_MARK) { free_trie(n1); return CLAUSE_MARK; }
  return n1;
}

struct unit *get_unit ()
{
  struct unit *p;
  if (Unit_avail == NULL) {
    p = ( struct unit * ) tp_alloc (sizeof (struct unit ));
    if (p == NULL) {
      fprintf ( stderr, "get_unit return NULL.\n");
      exit(1);
    }
  } else {
    p = Unit_avail;
    Unit_avail = Unit_avail->next;
  }
  return(p);
} 
 
struct trie *get_trie ()
{
  struct trie *p;
  struct links *l;

  if (Trie_avail == NULL) {
    p = ( struct trie * ) tp_alloc ( sizeof ( struct trie ) );
    if (p == NULL) {
      fprintf ( stderr, "get_trie return NULL.\n");
      exit(1);
    }
    p->link = NULL;
    /* Trie_news++; */
  } else {
    /* Trie_avails--; */
    p = Trie_avail;
    Trie_avail = Trie_avail->bro;
  }

  /* Trie_gets++; */
  p->pos = p->neg = p->bro = p->par = NULL;
  set_esign(p,DC);

  return(p);
} 
 
void free_trie (no)
     struct trie *no;
{
  struct trie *no2;
  while (no && no != CLAUSE_MARK) {
    /* if (no->pos && no->pos != CLAUSE_MARK) free_trie( no->pos );
       if (no->neg && no->neg != CLAUSE_MARK) free_trie( no->neg ); */
    free_trie(no->pos); 
    free_trie(no->neg);
    no2 = no;
    no = no->bro;
    free_trie_cell(no2);
  }
}

void print_trie (no)
     struct trie *no;
{
  /*
  printf("\nUnit Clauses: ");
  for (i = 1; i <= Max_atom; i++) 
    if (Value[i] != DC) {
      if (Value[i] == TT)
	fprintf(Sato_fp, "(%d) ", i);
      else
	fprintf(Sato_fp, "(-%d) ", i);
    }
    */
  fprintf(Sato_fp, "\nClause Tree:\n");
  if (no == NULL)
    fprintf(Sato_fp, "   nil");
  else if (no == CLAUSE_MARK)
    fprintf(Sato_fp, "   [C]");
  else 
    print_trie_aux(no, 0, "", "", "");
  fprintf(Sato_fp, "\n");
}

void print_trie_aux (no, sign, leader, addition, arrow)
     /* assume no != NULL */
     struct trie *no;
     int sign;
     char *leader, *addition, *arrow;
{
  char leader2[MAX_ATOM];
  int i;
  i = 0;

  fprintf(Sato_fp, "\n%s%s", leader, arrow);

  if (sign == 1 || sign == 2)
    if (no == CLAUSE_MARK)
      fprintf(Sato_fp, "->[C]");
    else 
      fprintf(Sato_fp, "-x%d[%d,%d]", key_of(no), esign_of(no), psign_of(no));
  else 
    fprintf(Sato_fp, " x%d[%d,%d]", key_of(no), esign_of(no), psign_of(no));

  if (no->pos != NULL) i++;
  if (no->neg != NULL) i++;
  if (no->bro != NULL) i++;

  str_cat(leader, addition, leader2);

  if (no->pos != NULL) {
    if (i == 1)
      print_trie_aux(no->pos, 1, leader2, "     ", " `-P-");
    else
      print_trie_aux(no->pos, 1, leader2, " |   ", " |-P-");
    i--;
  }

  if (no->neg != NULL) {
    if (i == 1)
      print_trie_aux(no->neg, 2, leader2, "     ", " `-N-");
    else
      print_trie_aux(no->neg, 2, leader2, " |   ", " |-N-");
    i--;
  }

  if (no->bro != NULL) {
      print_trie_aux(no->bro, 3, leader2, "", "");
    }
}

void print_clauses_in_trie ()
{
  int cl_arr[MAX_LIST], sign_arr[MAX_ATOM];

  if (Root == CLAUSE_MARK) {
    print_clause(cl_arr, sign_arr, 0);
    fprintf(stderr, "\nAn empty clause is found.\n");
  } else if (Root != NULL) 
    print_cl_in_trie_aux(Root, 0, cl_arr, sign_arr);
}

void print_cl_in_trie_aux (no, size, cl_arr, sign_arr)
     /* assume no != NULL */
     struct trie *no;
     int size, cl_arr[], sign_arr[];
{
  if (no == CLAUSE_MARK) {
    print_clause(cl_arr, sign_arr, size);
    return;
  } else {
    cl_arr[size] = key_of(no);
  }

  if (no->pos != NULL) {
    sign_arr[key_of(no)] = TT;
    print_cl_in_trie_aux(no->pos, size+1, cl_arr, sign_arr);
  }

  if (no->neg != NULL) {
    sign_arr[key_of(no)] = FF;
    print_cl_in_trie_aux(no->neg, size+1, cl_arr, sign_arr);
  }

  if (no->bro != NULL) {
    print_cl_in_trie_aux(no->bro, size, cl_arr, sign_arr);
  }
}

/***********************************************************/
/** search for a model **/
/***********************************************************/

trie_search ()
{
  int res = 0;
  INSEARCH = SHARED_BITS;

#ifdef MORETRACE
  if (TRACE == 6) print_trie(Root);
#endif

  if (Root == NULL) {
    Branch_num = Branch_succ = 1;
    fprintf(Sato_fp, "\nEvery atom has a fixed truth value.\n");
    if (TRACE > 0) print_model(Sato_fp);
    res = 1;
  } else if (Root == CLAUSE_MARK || trie_create_var_table() == UNSAT) {
    Branch_num = Branch_fail = 1;
    fprintf(Sato_fp, "\nAn empty clause is found from the first %d clauses.\n",
	   Clause_num);
    res = 0;
  } else {
    Branch_num = 1;
    Branch_fail = Branch_succ = 0;
    if (DATA == 4) res = trie4_search(1);
    else if (DATA == 2) res = trie2_search2();
    else res = trie3_search2(); 
  }
  return res;
}

int trie_list_len (no)
     struct trie *no;
{ 
  int i = 0;
  while (no != CLAUSE_MARK) { no = no->link->lin; i++; }
  return i;
}

void pv(n) int n; { printf("Value[%d] = %d", n, Value[n]); }


/*
void p_trie_info (f)
     FILE *f;
{
  fprintf(f, "\nThere are %d nodes in use and %d nodes available.\n",
	 Trie_gets - Trie_frees, Trie_avails);
  fprintf(f, "There are %d calls to get_node and %d calls to new_node.\n",
	 Trie_gets, Trie_news);
}
*/

int trie_create_var_table()
{
  int pos, neg, i;
  int extra_space = 0;
  if (GROW) extra_space = EXTRA_SPACE;

  if (Root == CLAUSE_MARK) return UNSAT;
  if (Root == NULL) return SAT;

  if (DATA != 2) {
    if (DATA == 4) { 
      init_var4_table();
      Clause_num = visit_trie4(Root, NULL, 0, 0, 0);
    } else {
      init_var3_table();
      Clause_num = visit_trie(Root, NULL, 0, 0, 0);
    }
    printf("There are %ld clauses in the trie (%d binary, %d non-Horn).\n", 
	   Clause_num, Bicl_num, NH_num);
    if (Root == CLAUSE_MARK) return UNSAT;

  } else {

    Stack2 = (int *) malloc((Max_atom+1) * (sizeof(int)));
    Stack2_idx = 0;

    init_var2_table ();
    Clause_num = visit_trie2(Root, NULL, 0, 0, 0);
    printf("There are %ld clauses in the trie (%d binary, %d non-Horn).\n", 
	   Clause_num, Bicl_num, NH_num);

    for (i = 1; i <= Max_atom; i++) {
      struct var2 *el = V2[i];
      pos = el->pos_count;
      neg = el->neg_count;
      el->pos_count = el->neg_count = 0;

      if (Value[i] == DC) {
	if (pos == 0) {
	  trie2_assign_value(i, FF);
#ifdef MORETRACE
	  print_x_pure;
#endif
	  Pure_num++;
	  level_of(el) = 0;
	  el->neg = get_trie2_array(neg);
	} else if (neg == 0) { 
	  trie2_assign_value(i, TT);
#ifdef MORETRACE
	  print_x_pure;
#endif
	  Pure_num++;
	  level_of(el) = 0;
	  el->pos = get_trie2_array(pos);
	} else {
	  el->pos_extra = el->neg_extra = extra_space;
	  el->pos = get_trie2_array(pos+extra_space);
	  el->neg = get_trie2_array(neg+extra_space);
	}
      } else {
	level_of(el) = 0;
	if (pos) el->pos = get_trie2_array(pos);
	if (neg) el->neg = get_trie2_array(neg);
      }
    }

    trie2_fill_in_clauses(NHtrie);
    trie2_fill_in_clauses(CLtrie);
  }

  return SAT;
}

void var_clauses (i, f)
     int i;
     /* f = 1: positive clauses only
	f = 2: negative clauses only
	f = 3: all clauses */
{
  int j, l;

  if (f != 2 && (l = V2[i]->pos_count) > 0) {
    printf("Here are the positive clauses for var %d.\n", i);
    for (j=0; j<l; j++) 
      print_clause_from_leaf(V2[i]->pos[j]);
  }

  if (f > 1 && (l = V2[i]->neg_count) > 0) {
    printf("Here are the negative clauses for var %d.\n", i);
    for (j=0; j<l; j++) 
      print_clause_from_leaf(V2[i]->neg[j]);
  }
}

void print_clause_from_leaf (tr)
     struct trie *tr;
{
  struct trie *son;

  if (DATA == 2)
    printf("%s c=%d ( ", 
	   (active_clause(tr))? " " : "m", count_of_clause(tr));
  else
    printf(" c=%d ( ", key_of(tr));

  tr = tr->par;
  printf("%s%d[%d] ",  HAS_POS_CL(tr)? "" : "-", key_of(tr), Value[key_of(tr)]);

  son = tr;
  tr = tr->par;
  while (tr != NULL) {
    printf("%s%d[%d] ",  (psign_of(son))? "" : "-", key_of(tr), Value[key_of(tr)]);
    son = tr; 
    tr = tr->par;
  }
  printf(")\n");
}

#ifdef MORETRACE
check_cl (total, arr, sign)
     int total, arr[], sign[];
{
  int pos[201];
  static int model[201];
  int i, j;

  if (total == 0) {
    j = 0;
    for (i = 1; i <= 200; i++) model[i] = FF;
    for (i = 1; i <= 200; i++) {
      if (pos[j] == i) { model[i] = TT; j++; }
    }
    return 0;
  } else {
    for (i = 0; i < total; i++) 
      if (sign[arr[i]] == model[arr[i]]) return 0;
    return 1;
  }
}
#endif

void trie_stats ()
{
  printf("\n");
  if (Clause_extra_num) 
    printf("The number of created clauses is %d (%d array updates).\n",
	   Clause_extra_num, Miss_num);
  if (Jump_num)
    printf("The number of backjumping is %d.\n",
	   Jump_num);
  if (Pure_num)
    printf("The number of pure deletions is %d.\n",
	   Pure_num);
}

void print_all_clauses (cl)
     struct trie *cl;
{
  while (cl != NULL) {
    print_clause_from_leaf(cl);
    cl = cl->bro;
  }
}

int trie_insert_one_key (key, key_arr, total)
     int key, key_arr[], total;
     /* insert a literal into the current clause.
	return 0 if the key is in key_arr.
	otherwise, return the length of the current clause. */
{
  int j;

  for (j = 0; j < total; j++)
    if (key == key_arr[j]) j = MAX_ATOM;

  if (j >= MAX_ATOM) return 0;
  key_arr[total++] = key;
  return total;
}

int weight_of_clauses ()
     /* return the number of false clauses under the current 
	interpretation */
{
  return count_false_cl_trie(Root);
}

int count_false_cl_trie (tr)
     struct trie *tr;
{
  if (tr == CLAUSE_MARK) {
    return 1;
  } else {
    int num_f_cl = 0;
    while (tr != NULL) {
      if (Value[key_of(tr)] == FF) {
	if (tr->pos != NULL)
	  num_f_cl += count_false_cl_trie(tr->pos);
      } else if (tr->neg != NULL) {
	  num_f_cl += count_false_cl_trie(tr->neg);
      }
      tr = tr->bro;
    }
    return num_f_cl;
  } 
}


/*
check_unit_implacants(i, val)
     int i, val;
{
  int j = Backup_idx-1;
  struct unit *u, *v;

  if (Backup[j] > 0) {
    u = get_unit(); 
    u->lit = (val == TT)? i : -i; 
    u->next = Top_var3->units; 
    Top_var3->units = u;  
  } else {
    u = Top_var3->units;
    j = (val == TT)? i : -i; 
    while (u != NULL) {
      if (u->lit == j) printf("unit %d\n", j);
      u = u->next;
    }
  }
  return 0;
}
*/

print_trie_info (tr)
     struct trie *tr;
{
  printf("info = %d, key = %d, psign = %d, shared = %d\n", 
	 tr->info, key_of(tr), psign_of(tr), shared_trie(tr));
}
