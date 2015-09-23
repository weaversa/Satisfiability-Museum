/*********************************************************************
; Copyright 2002, Hantao Zhang (HZ).  All rights reserved. 
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
#include "sato.h"
#include "weight.h"
#include "stack.h"
#include "tape.h"
#include "select.h"
#include "santo.h"

get_var_value (i) { return L5[(i)<<1]->value; }
set_var_value (i, s) { L5[(i)<<1]->value = s; }

#ifdef QUASICLAUSE
struct nlink *get_nlink ()
{
  struct nlink *p = (struct nlink *) malloc(sizeof(struct nlink));
  memory_count(sizeof(struct nlink), "nlink");

  if (p == NULL) {
    fprintf(stderr, "get_nlink return NULL.\n");
    exit(1);
  }
  p->next = NULL;
  return(p);
} 
#endif

void init_var5_table ()
{
  int i, s;
  struct lit5 *xl;

  tape_init();
  L5 = (struct lit5 **) malloc (sizeof(struct lit5 *)*(MAX_ATOM<<1));
  memory_count((sizeof(int *)*4+sizeof(struct lit5))*(MAX_ATOM<<1), "L5");

  for (i=2; i < (MAX_ATOM<<1); i++)  {
    int *arr;
    int **ptrs;

    L5[i] = xl = (struct lit5 *) malloc(sizeof(struct lit5));

    ptrs = (int **) malloc((sizeof(int *) << 2));
    xl->hts = ptrs; 
    hts_set_max(ptrs,4);
    hts_set_count(ptrs,2);

    arr = (int *) malloc((sizeof(int) << 2));
    xl->bicls = arr; 
    bicls_set_max(arr,4);
    bicls_set_count(arr,2);

#ifdef QUASICLAUSE
    xl->ncls = NULL;
#endif
    xl->deleted = 0;
    xl->weight_new = 0;
    xl->weight = 0;
    xl->stamp = 0;
    xl->level = 0;
    xl->info2 = 0;

    if (Value[lit_var(i)] == DC) xl->value = DC;
    else if (Value[lit_var(i)] == lit_sign(i)) xl->value = FF;
    else xl->value = TT;
  }

  Empty_binary[0] = -5;
  Empty_binary[1] = 3;
  Empty_binary[2] = 4;
}

insert_binary_clause (v1, v2)
     int v1, v2;
{
  int vs1[MAX_STACK];
  int vs2[MAX_STACK];
  int *bcs, i, nv, num=2, s;

  vs1[0] = vs2[1] = v1;
  vs2[0] = vs1[1] = v2;

  while (num) {
    v1 = vs1[--num];
    v2 = vs2[num];
    nv = NEG(v2);

    bcs = L5[v1]->bicls;
    weight_add1(v1);

    check((v1 == v2), printf("OOOPS! "));

    trace(9, printf(" binary ( %s%d %s%d )\n",
		    (lit_sign(v1))? "-" : "", lit_var(v1), 
		    (lit_sign(v2))? "-" : "", lit_var(v2)));

    /* check duplicates or unit clause */
    for (i = bicls_count(bcs)-1; i >= bicls_begin(); i--) {
      if (bcs[i] == v2) goto label;
      if (bcs[i] == nv) {
	if (vstack_nonempty()) {
	  trace(3, printf(" Unit ( %s%d )\n", (lit_sign(v1))? "-" : "", lit_var(v1)));
	  New_unit = NEG(v1);
	  New_unit_clause = NULL;
	  Conflict_cl_level = Backjumping_down = 1;
	  return 0;
	} else 
	  Clause_num--;
	  return insert_cl_1(lit_var(v1), NEG(lit_sign(v1))); 
      }
    }

    /* check space before insert */
    if (bicls_count(bcs) == bicls_max(bcs)) {
      int *bcs2 = (int *) malloc((bicls_max(bcs)<<1) * (sizeof(int)));
      memory_count((sizeof(int) * bicls_max(bcs)), "BCS");
      if (bcs2 == NULL) { 
	if (vstack_nonempty()) return 0;
	fprintf(stderr, "insert_bicl_key failed.\n"); exit(1); 
      }
      for (i = bicls_max(bcs)-1; i >= 0; i--) bcs2[i] = bcs[i];
      bicls_max(bcs2) += bicls_max(bcs);
      free(bcs);
      bcs = L5[v1]->bicls = bcs2;
    }
    bcs[bicls_count_inc(bcs)] = v2;

    if (BINARY) {
      bcs = L5[NEG(v1)]->bicls;
      for (i = bicls_count(bcs)-1; i >= bicls_begin(); i--) {
	v1 = bcs[i];
	if (v1 == v2) {
	  if (vstack_nonempty()) {
	    trace(3, printf(" Unit ( %s%d )\n", lit_sign(v1)? "-" : "", lit_var(v1)));
	    New_unit = nv; /* nv = NEG(v1) = NEG(v2) */
	    New_unit_clause = NULL;
	    Conflict_cl_level = Backjumping_down = 1;
	    return 0;
	  } else 
	    return insert_cl_1(lit_var(v1), NEG(lit_sign(v1))); 
	} else if (v1 != nv) {
	  vs1[num] = v1;
	  vs2[num++] = v2;
	  vs1[num] = v2;
	  vs2[num++] = v1;
	}
      }
    label: ;
    }
  }
}

int *insert_clause_to_tape (cl_arr, total, plen, type)
     int cl_arr[], total, plen, type;
{
  int i, value=cl_arr[total], *cl, *p;

  if (type == NORM) { 
    if (total == 1) { 
      i = cl_arr[0];
      assign_value1(i);
      return NULL; 
    }
    if (total == 2) { 
      insert_binary_clause(cl_arr[0], cl_arr[1]); 
      return NULL; 
    }
  } else if (type == GTEQ || type == GRTR) { 
    if (type == GRTR) value++;
    if (value == 0) return NULL; 
    if (value == 1) type = NORM; 
    else {
      /* changing GTEQ to LSEQ */
      for (i=0; i < total; i++) cl_arr[i] = NEG(cl_arr[i]);
      value = total-value;
      type = LSEQ;
    }
  } else if (type == LESS) { 
    type = LSEQ; value--; 
  } 

  if (Branch_open) {
    cl = get_tape_head(total, Lemma_tape);
  } else if (type) { /* type != NORM */
    NH_num++;
    POS_num++;
    cl = get_tape_head(total, 0);
  } else if (plen > 1) {
    NH_num++;
    if (plen == total) {
      POS_num++;
      cl = get_tape_head(total, 0);
    } else
      cl = get_tape_head(total, Input_tape);
  } else {   
    cl = get_tape_head(total, Input_tape);
  }

  if (cl == NULL) {
    fprintf(stderr, "No space for input clauses (because of -g%d)\n", GROW);
    exit(1);
  } 
  set_clause_size(cl, total);
  p = cl;

#ifdef QUASICLAUSE
  if (type) { 
    *(++p) = -value;  /* original value */
    *(++p) = value;   /* current value */
    for (i = 0; i < total; i++) {
      int j;
      struct nlink *nl = get_nlink();
      set_lit(++p, cl_arr[i]);
      nl->cl = cl;
      j = (*p)^1;
      nl->next = L5[j]->ncls;
      L5[j]->ncls = nl;
      weight_add(*p,value); 
      weight_add(j,value); 
    }
  } else 
#endif
  { 
    /* set the head */
    set_head_tail(++p, 3); 
    insert_head_tail(p,cl_arr[0]);
    /* set the tail */
    set_head_tail(++p, total+2); 
    insert_head_tail(p,cl_arr[total-1]);
    for (i=0; i < total; i++) {
      set_lit(++p, cl_arr[i]);
      weight_add1(*p); 
    }
  }

  trace(9, { printf("IN(%d): ", type); print_clause(cl);});
  return cl;
}

int *insert_lemma_to_tape (cl_arr, total, p1, p2)
     int cl_arr[], total, p1, p2;
{
  int i, sig, *cl, *p;

  if (p1 > p2) { i = p1; p1 = p2; p2 = i; }
  if (total == 3) {
    if (p1 != 0) {
      i = cl_arr[0]; cl_arr[0] = cl_arr[p1]; cl_arr[p1] = i; p1 = 0;
    } else if (p2 != 2) {
      i = cl_arr[2]; cl_arr[2] = cl_arr[p2]; cl_arr[p2] = i; p2 = 2;
    }
  }

  check((p1 == p2),  printf("p1 = %d = p2\n", p1));

  cl = get_tape_head(total, (total>4)? Lemma_tape : Input_tape);
  if (cl == NULL) {
    printf("c no space for new clauses (-g%d)\n", GROW);
    GROW = 0;
    return NULL;
  }
  set_clause_size(cl, total);
  p = cl;

  /* set the head */
  set_head_tail(++p, p1+3);
  insert_head_tail(p,cl_arr[p1]);

  /* set the tail */
  set_head_tail(++p, p2+3);
  insert_head_tail(p,cl_arr[p2]);

  for (i=0; i < total; i++) {
    set_lit(++p, cl_arr[i]); 
    weight_add1(*p); 
  }

  trace(3, { printf("NEW(%d): ", Level); print_clause(cl);});
  return cl;
}

init_saton_search ()
{ 
  int i;
  int fixed=0;

  adjust_max_tape();
  vstack_init(); 

  for (i = 1; i <= Max_atom; i++) {
    int x0 = get_lit(i,0);
    int x1 = get_lit(i,1);

    if (Value[i] != DC) {
      fixed++;
      trace(6, printf("%s%d 0\n", (Value[i] == TT)? "" : "-", i));
      x1 = get_lit(i,Value[i]);
      uqueue_add(x1);
      assign_value2(x1);
    } else if (!weight_new_val(x0)) {
      fixed++;
      uqueue_add(x0);
      print_x_pure(x0);
      assign_value0(x0);
      Pure_num++; 
    } else if (!weight_new_val(x1)) { 
      fixed++;
      uqueue_add(x1);
      print_x_pure(x1);
      assign_value0(x1);
      Pure_num++;
    }
  }

  VarOrderFirst = 0;
  if (SELECT > 3) {
    VarOrder = (int *) malloc(sizeof(int)*Max_atom);
    VarOrderSize = 0;
    for (i = 1; i <= Max_atom; i++)
      if (Value[i] == DC) VarOrder[VarOrderSize++] = i;
  } else
    VarOrderSize = Max_atom+1;

  trace(1, if (fixed) printf("c %d variables have fixed value\n", fixed));
  return handle_unit_clauses();
}

int saton_search (first)
     int first;
{
  int i;    

  uqueue_init();
  if (first) {
    if (TRACE >= 0) 
      printf("c There are %d clauses on %d variables (%d binary, %d non-Horn).\n", 
	     Clause_num, Max_atom, Bicl_num, NH_num);
    Clause_num = 0;
    if (init_saton_search() == UNSAT) return UNSAT;
    if (100*Bicl_num >= 98*Clause_num && binsat_scc1() == UNSAT) return UNSAT;
  }

  /* ANT SEARCH 
  if (ANT) return santo_search();
  */

  var5_next_key();
  /* the major loop goes here. */
  while (!Stop && (New_unit || uqueue_nonempty())) {
    if (handle_unit_clauses() == UNSAT) {
      var5_prev_key();
    } else {	
      var5_next_key();
    }
  } /* while */

  return ((Branch_succ > 0)? 1 : Stop);
}

int var5_next_key ()
{
  int i, s;

#ifndef TEST
  if (OLDV) {
    int flag;

    while (OLDV) {
      i = Old_value[--OLDV];
      flag = i&1;
      s = i>>1;
      i = lit_var(s);

      if (var_value(i) == DC) {
	if (flag) {
	  print_let_x_have(s);
	  vstack_push1(s);
	  assign_value2(s);
	  Branch_num++;
	  Branch_open++; 
	  var_level(i) = Level;
	} else {
	  print_now_let_x_have(s);
	  vstack_push2(s);
	  assign_value2(s);
	  var_level(i) = Level;
	}

	return s;
      } else if (flag) OLDV = 0;
    }
  }
#endif

  if (GROW) {
    if (SELECT < 3 || SELECT > 8) ;
    else if (CHOICE2) { weight_update1(); }
    else { weight_update0(); }
  }

#ifdef APPLICATION
  /* ------------------ added by shen ---------------------*/
  if (QAP)
    s = qap_best_key();
  else if (STAGE == 4)
    s = mlb_best_key();
  else
  /* ------------------------------------------------------*/
#endif

  var5_best_key(s);

  if (s < 0) return var5_prev_key();
  if (!s) return var5_succ_end();
  s = s^CHOICE;

  ++Branch_open;
  ++Branch_num;
  Conflict_cl_level = Level;
  i = s >> 1;
  var_level(i) = Level;
  trace(6, printf("#%d ", var_order(i)));
  print_let_x_have(s);
  vstack_push1(s);
  assign_value2(s);
  check(var_gmark(i), printf("var_gmark(%d) != NULL\n", i));
}

int var5_prev_key ()
{
  int i, s;

  trace(4, printf("a %d branches (%d open, %ld failed, %d jumped, l=%d).\n", 
		  Branch_num, Branch_open, Branch_fail, Branch_jump, 
		  Conflict_cl_level));

  if (!Branch_open) return UNSAT;

  if (JUMP && Conflict_cl_level < Level) {
    trace(4, printf("    Backjumping from level %d to %d\n", Level, Conflict_cl_level));
    Branch_jump += Level-Conflict_cl_level;
    i = vstack_backup(Conflict_cl_level);
    if (Backjumping_down) i = 0;
  } else
    i = vstack_backup(Level);

  if (i && L5[i]->value == DC) {
    check((var_level(i>>1) != Level+1), 
	  printf("why changed level of %d: %d %d\n", 
		 i>>1, var_level(i>>1), Level));
    i = NEG(i);
    uqueue_add(i); 
    /* Hope that clauses imply i later */
  }

  trace(4, printf("b %d branches (%d open, %ld failed, %d jumped)\n", 
		  Branch_num, Level, Branch_fail, Branch_jump)); 
}

int adjust_conflict_level (cl_arr, total, down, gcl)
     int cl_arr[], total, *down;
     TAPE gcl;
{
  int l, i, c=0, hl=0, highest=0, second_high=0, u;

  for (i = 0; i < total; i++) {
    l = var_level(cl_arr[i]);
    if (l > highest) { 
      second_high = highest; 
      u = hl;
      highest = l; 
      hl = cl_arr[i];
      c = 1; 
    }
    else if (l == highest) c++;
    else if (l > second_high) { second_high = l; u = cl_arr[i]; }
  }

  if (!gcl || c > 1 || ++second_high == highest) { *down = 0; return highest; }

  /* if only one variable is the highest */
  trace1(5,  printf("New level %d, %d, %d\n", second_high, highest, Level));

  *down = 1;
  return (second_high);
}

void var5_record_conflict (gcl)
     TAPE gcl;
{
  int num;
  int cl_arr[MAX_LENGTH];

  trace(3, { printf(" Empty cl: "); print_clause(gcl);});

  if ((num = var5_collect_parents(gcl, cl_arr)) > 0) {
    var5_insert_lemma(num, cl_arr);
  }
}

var5_insert_lemma (num, cl_arr)
     int num, cl_arr[];
{
  int i, j, l, p1=1, p2=0, second_high=0, c=0;
  TAPE gcl = NULL;

  Clause_num++;
  trace(4, {
    printf("Fresh [%d]: (", Level);
    for (i = 0; i < num; i++) {
      j = cl_arr[i];
      printf(" %d(%d,%d)", j, var_value(j), var_level(j));
    }
    printf(" )\n");
  });

  /* remove level 0 variables */
  /* find the max level of clause and set it to Conflict_cl_level */
  /* fix the sign of literals in the new clause */
  i = Backjumping_down = Conflict_cl_level = 0;
  while (i < num) {
    j = cl_arr[i];
    if ((l=var_level(j)) == 0) {
      cl_arr[i] = cl_arr[--num];
    } else {
      if (l > Conflict_cl_level) { 
	second_high = Conflict_cl_level; 
	p2 = p1;
	Conflict_cl_level = l; 
	p1 = i;
	c = 1; 
      } else if (l == Conflict_cl_level) c++;
      else if (l > second_high) {
	second_high = l; p2 = i;
      }
      cl_arr[i++] = (j<<1)+var_value(j);
    }
  }

  if (c == 1) { 
    New_unit = NEG(cl_arr[p1]);
    if (++second_high < Conflict_cl_level) { 
      Conflict_cl_level = second_high; 
      Backjumping_down = 1;
      /* if only one variable is the highest, then take the second_high */
      trace1(5,  printf("New level %d, %d, %d\n", second_high, 
			Conflict_cl_level, Level));
    }
  }

  trace(3, {
    printf("NC [%d]: (", Level);
    for (i = 0; i < num; i++) {
      j = cl_arr[i];
      printf(" %s%d", (lit_sign(j))? "-" : "", lit_var(j));
    }
    printf(" )\n");
  });

#ifdef MORETRACE
  if (LINE == 4000) {
    for (i = 0; i < num; i++) {
      j = cl_arr[i];
      if ((lit_sign(j))^Model[j]) i = MAX_LIST;
    }
    if (i < MAX_LIST) { printf("c FALSE CLAUSE CREATED\n"); exit(0); }
  }
#endif

  if (num == 2) { 
    New_unit_clause = (int *) -cl_arr[p2];
    insert_binary_clause(cl_arr[0], cl_arr[1]); 
  } else if (num > 2) {
    if (gcl = insert_lemma_to_tape(cl_arr, num, p1, p2)) {
      trace(3, { printf("Gnc "); print_clause(gcl); });
      Conflict_gcl = gcl; 
    } 
  }
  New_unit_clause = gcl;
}

var5_collect_parents (gcl0, cl_arr)
     TAPE gcl0;
     int cl_arr[];
{
  int key, i, j, k, var_num=0, total=0, first=1, offset;
  int max_level=Level;
  TAPE gcl=gcl0;
  int this_trace=4;

  if (++stamp >= MAX_SHORT) stamp = 1;

  /*
  for (j = 3; j < size_of_clause(gcl); j++) 
    if ((i=var_level(lit_var(gcl[j]))) > max_level) max_level = i;
  */

#ifdef QUASICLAUSE
  if (is_quasi_cl(gcl)) 
    for (j = 3; j < size_of_clause(gcl); j++) {
      if (lit_value(gcl[j]) == TT) {
	key = lit_var(gcl[j]);
	if (var_level(key) < max_level) {
	  cl_arr[total++] = key;  
	} else {
	  var_num++;
	  trace(this_trace, printf("queue %d (%d)\n", key, var_level(key)));
	}
	weight_add1(gcl[j]);
	var_stamp(key) = stamp; 
      } 
    }
  else 
#endif
    for (j = 3; j < size_of_clause(gcl); j++) {
      key = lit_var(gcl[j]);
      if (var_level(key) < max_level) {
	cl_arr[total++] = key;  
      } else {
	var_num++;
	trace(this_trace, printf("queue %d (%d)\n", key, var_level(key)));
      }
      weight_add1(gcl[j]);
      var_stamp(key) = stamp; 
    }

  for (k = vstack_size()-1; k >= 0 && var_num; k--) {
    key = vs_var(vstack_of(k));
    if (var_level(key) < max_level) break;
    if (var_stamp(key) == stamp) {
      trace(this_trace, printf("unqueue %d\n", key));
      if (--var_num == 0 && !first) { cl_arr[total++] = key; return total; }

      if (gcl=(int*)var_gmark(key)) {
	if (is_from_binary(gcl)) {
	  i = key_from_binary(gcl);
	  collect_one_key(i);
	} else {
	  trace(this_trace, print_clause(gcl));

#ifdef QUASICLAUSE
	  if (is_quasi_cl(gcl)) {
	    /* collect only true literals for LSEQ clauses */
	    for (j = 3; j < size_of_clause(gcl); j++) if (lit_value(gcl[j]) == TT) { 
	      i = lit_var(gcl[j]);
	      collect_one_key(i);
	    }
	  }
	  else
#endif
	    for (j = 3; j < size_of_clause(gcl); j++) {
	      i = lit_var(gcl[j]);
	      collect_one_key(i);
	    }
	}

	first = 0;
	weight_add1(vs_literal(vstack_of(k)));
	if (!var_num) return total; 
      } else { 
	cl_arr[total++] = key;
	if (total >= MAX_LENGTH) return 0;
      }
    } else
      var_stamp(key) = stamp;
  }
 
  check(var_num, 
	{ if (TRACE == 9) { stop1(); exit(0); } TRACE=9; 
	printf("failed %d %ld\n", var_num, Branch_fail); 
	vstack_print(); 
	var5_record_conflict(gcl0);}); 

  return 0;
}

int grow_propagate (ks0)
     int ks0;
{
  /* more than 95% of total time is consumed by this function for 
     most hard examples */
  int **pts = L5[ks0]->hts;
  int *p = L5[ks0]->bicls;
  int i, j, ks, num, sig, step;
  int head, tail, tail_lit, endcl, *cl;

#ifdef APPLICATION
  if (QAP && lit_sign(ks0) && (qap_branch_and_bound(lit_var(ks0)) == UNSAT)) {
    return var5_fail_end(NULL);
  }
#endif

  /* propagate binary clauses first */
  for (j = bicls_count(p)-1; j >= bicls_begin(); j--) {
    ks = NEG(p[j]);
    if ((i = L5[ks]->value) == DC) { /* a unit clause is found */
      i = lit_var(ks);
      var_gmark(i) = -lit_var(ks0);
      var_level(i) = Level;
      trace(6, printf("unit cl %s%d at %d from (%s%d %s%d)\n", 
		      (lit_sign(ks))? "" : "-", i, Level,
		      (lit_sign(ks))? "" : "-", i,  
		      (lit_sign(ks0))? "-" : "", lit_var(ks0)));
      print_x_has_to(ks);
      vstack_push0(ks);
      assign_value2(ks);
#ifdef APPLICATION
      if (ANTTRACE) weight_add1(ks);
#endif
    } else if (i == TT) {
      Empty_binary[3] = ks0;
      Empty_binary[4] = p[j];
      return var5_fail_end(Empty_binary);
    }
    /* use a shorter clause: lit_var(ks0) must be assigned before i */
    /* else if (var_gmark(i=lit_var(ks))) { 
      trace(8, printf("replace %d->gmarkd by binary (%s%d)\n", 
		      i, (lit_sign(ks0))? "-" : "", lit_var(ks0)));
      var_gmark(i) = -lit_var(ks0);
      var_level(i) = Level;
      } */
  }

  /* propagate long clauses */
  j = hts_begin();
  num = hts_count(pts);
  while (j < num) {
    p = pts[j];
    if (is_head(p)) { /* p is a real head */
      /* head moves from left to right and tail moves from right to left */
      step = 1;
      cl = p-1;
      head = cl[1];
      tail = cl[2];
    } else { /* p is actually tail */
      step = -1;
      cl = p-2;
      tail = cl[1];
      head = cl[2];
    }
    endcl = size_of_clause(cl);

    /* check tail first */
    if (i=L5[tail_lit = cl[tail]]->value) {
      if (i != DC) {
	j++;
	continue; /* cl[tail] is true */
      }
    } else {
      tail_lit = 0;  /* cl[tail] is false */
    }

    if (endcl == 6) { /* clause length == 3 */
      /* check the middle literal */
      if (L5[ks = cl[4]]->value) {
	/* cl[4] is either true or unsigned */
	/* switch cl[4] with cl[head] */
	i = cl[4];
	cl[4] = cl[head];
	cl[head] = i;
	pts[j] = pts[--num];
	insert_head_tail(p,ks);
	continue;

	/* Now cl[4] is false */
      } else if (tail_lit) {
	/* a unit clause is found */
	ks = NEG(tail_lit);
	i = lit_var(ks);
	trace(6, {
	  printf("unit cl %s%d at %d from ", (lit_sign(ks))? "" : "-", i, Level);
	  print_clause(cl);});
	var_gmark(i) = (int) cl;
	var_level(i) = Level;
	print_x_has_to(ks);
	vstack_push0(ks);
	assign_value0(ks);

#ifdef APPLICATION
	if (ANTTRACE) weight_add1(ks);
#endif
	j++;
	continue;
      } else {
	hts_set_count(pts,num);
	return var5_fail_end(cl);
      }
    } else {

      /* work on long clause */
      i = head+step;
    while (1) {
      /* printf("i=%d, h=%d, t=%d, e=%d s=%d\n", i, head, tail, endcl, step);*/
      if (i == endcl) { /* the end of the clause; step must be 1 */
	i = 3; /* beginning */
	continue;
      } 
      if (i == 2) { /* the beginning of the clause; step must be -1 */
	i = endcl-1;
	continue;
      } 
      if (i == tail) { i += step; continue; /* skip the tail */ }

      if (i == head) {
	/* Now the whole clause has been scanned. */
	if (tail_lit) {
	  /* a unit clause is found */
	  ks = NEG(tail_lit);
	  i = lit_var(ks);
	  sig = lit_sign(ks);
	  trace(6, {
	    printf("unit cl %s%d at %d from ", (sig)? "" : "-", i, Level);
	    print_clause(cl);});
	  var_gmark(i) = (int) cl;
	  var_level(i) = Level;
	  print_x_has_to(ks);
	  vstack_push0(ks);
	  assign_value0(ks);

#ifdef APPLICATION
	  if (ANTTRACE) weight_add1(ks);
#endif
	  j++;
	  break; /* look for next clause  */
	} else {
	  hts_set_count(pts,num);
	  return var5_fail_end(cl);
	} 
      }

      /* cl[i] is a literal */
      if (L5[ks = cl[i]]->value) {
	/* cl[i] is either true or unsigned */
	pts[j] = pts[--num];
	set_head_tail(p, i);
	insert_head_tail(p,ks);
	/*
	  printf("change head-tail from %d to %d in ", 
		 lit_var(cl[head]), lit_var(ks));
	  print_clause(cl);
	  print_var5_clause(k, 3);
	*/
	break;
      }
      i += step;
    }}
  }
  hts_set_count(pts,num);

#ifdef QUASICLAUSE
  if (QCLAUSE) {
    /* these for the new types of clauses with numbers */
    struct nlink *nl = L5[ks0]->ncls;
    /*printf("Q%d ", ks0);*/
    while (nl) {
      cl = nl->cl;
      if ((dec_cvalue(cl) <= 0) &&
	  double_check_nclause(cl) == UNSAT) {
	return var5_fail_end(cl);
      }
      nl = nl->next;
    }
  }
#endif

  return SAT;
}

#ifdef QUASICLAUSE

int double_check_nclause (cl)
     TAPE cl;
{
  int tt = 0;
  int value = value_of(cl);
  int i, j, v, nc, s, ks;

  for (j = 3; j < size_of_clause(cl); j++) 
    if ((i=L5[cl[j]]->value) == DC) nc++;
    else if (i) tt++;

  tt = value-tt;
  /* printf("nc=%d, tt=%d ", nc, tt); print_clause(cl);*/
  if (tt > 0) { set_ncl_val(cl,tt); return SAT; }

  /* LSEQ only */
  if (tt < 0) { set_ncl_val(cl,0); return UNSAT; }

  /* tt = 0, all the remaining literals should be false */
  for (j = 3; nc && j < size_of_clause(cl); j++) 
    if (L5[ks=cl[j]]->value == DC) {
      i = lit_var(ks);
      var_gmark(i) = (int) cl;
      var_level(i) = Level;
      trace(6, {
	printf("set x%d = %d at %d by LSEQ: ", i, lit_sign(ks), Level);
	print_clause(cl);
      });
      print_x_has_to(ks);
      vstack_push0(ks);
      assign_value0(ks);
#ifdef APPLICATION
      if (ANTTRACE) weight_add1(ks);
#endif
      nc--;
    }
  
  return SAT;
}
#endif

int handle_unit_clauses ()
     /* handle each unit clause one by one ... */
{
  int i, s;

  /* see if there is a unit clause from lemma */
  check_new_unit();

  /* now handle clauses */
  while (uqueue_nonempty()) {
    uqueue_pop(s);
    i = lit_var(s);
    if (L5[s]->value == DC) {
      /* this is the case of the second choice of a selected lit */
      if (1) {
	var_level(i) = Level;
	check(var_gmark(i), printf("var_gmark(%d) != NULL\n"));
	print_now_let_x_have(s);
	vstack_push2(s);
	assign_value2(s);
      }
    } else if (L5[s]->value) {
      trace(3, printf("    x%d = %d is a conflict\n", i, lit_sign(s)));
      if (var5_fail_end(NULL) == UNSAT) return UNSAT;
    } else if (grow_propagate(s) == UNSAT) return UNSAT;
  }

#ifdef APPLICATION
  if (QAP) return qap_check_low_bound();
  else if (STAGE == 4 && (RESTRICT&1)) return mlb_check_low_bound(); 
#endif

  return SAT;
}

check_true_atoms (num)
     int num;
{
  int i, j=0;
  for (i = 2; i <= (Max_atom<<1); i += 2) if (L5[i]->value == TT) j++;
  if (num>0 && j != num) {
    printf("Warning: true variables = %d != %d\n", j, num);
    stop1();
    return -1;
  }
  return j;
}

int var5_succ_end ()
{
  Conflict_cl_level = Level;
  uqueue_init();

  if (var5_check_model()) return var5_prev_key();
  Branch_succ++;

#ifdef APPLICATION
  if (GROUP) print_oarray_model();
  else if (QAP) qap_record_soln(); 
  else if (TEAM) print_wht_model();
  else if (STAGE) print_team_model();
  else 
#endif
    print_model(stdout);
stop1();
  return ((MODEL && Branch_succ >= MODEL)? 0 : var5_prev_key());
}

int var5_fail_end (cl)
     TAPE cl;
{
  int i;

  Conflict_cl_level = Level;
  uqueue_init();

  trace(3, if (cl) { printf(" empty cl: "); print_clause(cl);});

  if (GROW && cl && Branch_open) {
    int num;
    int cl_arr[MAX_LENGTH];

    if ((num = var5_collect_parents(cl, cl_arr)) > 0) {
      var5_insert_lemma(num, cl_arr);
    }
  }

  if (Stop = check_stop(1)) {
    if (!RESTART && TRACE >= 0) {
      printf("\nc The search is aborted with search tree path:\n");
      print_guide_path(stdout);
      printf("\n");
    }
  }
  
  Branch_fail++;
  return UNSAT;
}

print_weight ()
{
  int i;
  for (i = 1; i <= Max_atom; i++) {
    printf("V%d: %d %d\n", i, L5[(i<<1)]->weight, L5[(i<<1)+1]->weight);
  }
}

var5_assign (i, sign)
     int i, sign;
{
  var_level(i) = Level;
  i = get_lit(i,sign);
  print_x_has_to(i);
  vstack_push0(i);
  assign_value2(i);
#ifdef APPLICATION
  if (ANTTRACE) weight_add1(i);
#endif
}


void print_var5_clause (i, flag)
     int i, flag;
{
  int j, m, *cl;

  if ((flag&1) &&(m=hts_count(L5[get_lit(i,0)]->hts))>hts_begin()) {
    printf("/******* Positive clauses for variable %d.*******/\n",i);
    for (j = hts_begin(); j < m; j++) {
      cl = L5[get_lit(i,0)]->hts[j];
      set_clause_address(cl);
      print_clause(cl);
    }
  }

  if ((flag>1) &&(m=hts_count(L5[get_lit(i,1)]->hts))>hts_begin()) {
    printf("/******* Negative clauses for variable %d.*******/\n",i);
    for (j = hts_begin(); j < m; j++) {
      cl = L5[get_lit(i,1)]->hts[j];
      set_clause_address(cl);
      print_clause(cl);
    }
  }
}

#ifdef QUASICLAUSE
void print_var5_nclause (i, flag)
     int i, flag;
{
  int j, l;
  struct nlink *gl;

  if (L5[get_lit(i,1)]->ncls && (flag & 1)) {
    printf("/******* Positive clauses for variable %d.*******/\n",i);
    gl = L5[get_lit(i,1)]->ncls;
    while (gl) {
      print_clause(gl->cl);
      gl = gl->next;
    }
  }
  
  if (L5[get_lit(i,0)]->ncls && flag > 1) {
    printf("/******* Negative clauses for variable %d.*******/\n",i);
    gl = L5[get_lit(i,0)]->ncls;
    while (gl) {
      print_clause(gl->cl);
      gl = gl->next;
    }
  }
}
#endif

int variable_value (v) int v; { return var_value(v); }

int binsat_scc1 ()
{
  int i, j, k; 
  if (++stamp >= MAX_SHORT) stamp = 1;  
  timer = 0;
  trace(6, printf("Pre-2-SAT\n"));
  for (k = 1; k <= Max_atom; k++) {
    i = (k<<1)+CHOICE;
    if (lit_value(i) == DC && unassigned_lit10(i)) {
      lit_stamp(i) = stamp;
      trace(6, printf("  Pre-2-SAT:  %s%d be 1\n", 
		      (lit_sign(i))? "-" : "", lit_var(i)));
      if (binary_scc(i^1) == UNSAT) {
	trace(3, printf("End Pre-2-SAT\n"));
	return UNSAT;
      }
    }
  }
  trace(3, printf("End Pre-2-SAT\n"));
  return SAT;
}

int binary_scc (ks0)
     int ks0;
{
  int *p, *cl;
  int i, j, ks, num;

  timer++;
  dfs_time(ks0) = dfs_lowlink(ks0) = timer;

  p = L5[ks0]->bicls;

  for (j = bicls_count(p)-1; j >= bicls_begin(); j--) {
    if (lit_value(ks0) != DC) return SAT;
    if (lit_value(ks=p[j]) == DC) { 
      if (unassigned_lit10(ks)) {
	/* a unit clause is found */
	trace(6, printf("  Pre-2-SAT:  %s%d from (%s%d %s%d)\n", 
			(lit_sign(ks))? "-" : "", lit_var(ks), 
			(lit_sign(ks))? "-" : "", lit_var(ks), 
			(lit_sign(ks0))? "-" : "", lit_var(ks0)));
	lit_stamp(ks) = stamp;
	if (binary_scc(ks^1) == UNSAT) return UNSAT;
	if (dfs_lowlink(ks0) > dfs_lowlink(ks)) dfs_lowlink(ks0) = dfs_lowlink(ks);
      } else if (assigned_false10(ks)) {
	/* a conflict and ks has to be true */
	uqueue_init();
	var_level(ks>>1) = Level;
	trace(2, printf("  Pre-2-SAT:  %s%d be 1 by (%s%d %s%d)\n", 
			(lit_sign(ks))? "-" : "", lit_var(ks), 
			(lit_sign(ks))? "-" : "", lit_var(ks), 
			(lit_sign(ks0))? "-" : "", lit_var(ks0)));
	ks = ks^1;
	vstack_push0(ks);
	assign_value2(ks);
	if (handle_unit_clauses() == UNSAT) return UNSAT;
      } else if (dfs_done(ks) != stamp) {
	if (dfs_lowlink(ks0) > dfs_time(ks)) dfs_lowlink(ks0) = dfs_time(ks);
      }
    }
  }

  if (lit_value(ks0) == DC) {
    if (dfs_lowlink(ks0) != dfs_time(ks0)) { 
      trace(2, printf("push %d\n", ks0)); 
    } else {
      trace(2, printf("root %d\n", ks0));
      dfs_done(ks0) = stamp;
    }
  }

  return SAT;
}
