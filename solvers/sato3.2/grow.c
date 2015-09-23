/*********************************************************************
; Copyright 2002-2009, Hantao Zhang (HZ).  All rights reserved. 
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
#include "grow.h"

fill_var4_table ()
{
  int i;

  if (TRACE >= 0) 
    printf("c There are %d clauses (%d binary, %d non-Horn).\n", 
	   Slot_total-Slot_avail, Bicl_num, NH_num);

  for (i=1; i <= Max_atom; i++) {
    struct var4 *el = V4[i];
    el->input_pos = el->pos;
    el->input_neg = el->neg;
    if (Value[i] == DC) {
			 
      if (!el->pos) {
	assign_value(i, FF);
#ifdef MORETRACE
	print_x_pure;
#endif
	Pure_num++;
      } else if (!el->neg) {
	assign_value(i, TT);
#ifdef MORETRACE
	print_x_pure;
#endif
	Pure_num++;
      }
    } 
  }
}

struct gclause *get_gclause (size)
     int size;
{
  struct gclause *p;

  if (Slot_avail) {
    p = (struct gclause *) tp_alloc(sizeof(struct gclause));
    p->osize = size;
    p->lits = (int *) malloc(size * sizeof(int));
    Gclauses[--Slot_avail] = p;
  } else {
    if (!Slot_full) {
      int i = (Gcl_size) >> 1;
      while (i) heapify_gclause(--i);
      Slot_full = 1;
    }
    p = Gclauses[0];
    if (Value[p->watch1] != DC || Value[p->watch2] != DC || p->osize < size) return NULL;
    delete_gclause(p);
    p->osize = size;
    heapify_gclause(0);
  }
  p->unit = 0;
  return(p);
} 

struct gclause *get_gclause0 (size)
     int size;
{
  struct gclause *p = (struct gclause *) tp_alloc(sizeof(struct gclause));
  p->osize = size;
  p->lits = (int *) tp_alloc(size * sizeof(int));
  p->unit = 0;
  return(p);
}

void heapify_gclause (i)
     int i;
{
  int m, l = left(i);
  int r = right(i);
  
  if (l < Gcl_size && Value[Gclauses[l]->watch1] == DC && Value[Gclauses[l]->watch2] == DC &&
      Gclauses[l]->osize >= Gclauses[i]->osize) m = l;
  else m = i;

  if (r < Gcl_size && Value[Gclauses[r]->watch1] == DC && Value[Gclauses[r]->watch2] == DC &&
      Gclauses[r]->osize >= Gclauses[m]->osize) m = r;

  if (m != i) {
    struct gclause *cl = Gclauses[i];
    Gclauses[i] = Gclauses[m];
    Gclauses[m] = cl;
    heapify_gclause(m);
  }
}

struct glink *get_glink ()
{
  struct glink *p;

  if (Glink_avail) {
    /* Glink_avails--; */
    p = Glink_avail;
    Glink_avail = Glink_avail->next;
  } else {
    p = (struct glink *) tp_alloc(sizeof(struct glink));
    if (p == NULL) {
      fprintf ( stderr, "get_glink retudrn NULL.\n");
      exit(1);
    }
    /* Glink_news++; */
  }
  p->next = NULL;
  return(p);
} 

struct glink *delete_glink (gl, cl)
  struct glink *gl;
  struct gclause *cl;
{
  struct glink *gl1, *gl2;
  gl2 = gl->next;
  if (gl->cl == cl) { free_glink(gl); return gl2; }
  else {
    gl1 = gl;
    while (gl2->cl != cl) { 
      gl1 = gl2; gl2 = gl2->next;
      if (gl2 == NULL) { printf("delete_glink failed\n"); return gl; }
    }
    gl1->next = gl2->next;
    free_glink(gl2);
    return gl;
  }
}

void init_var4_table ()
{
  int i;
  struct var4 *el;

  Glink_avail = NULL;
  NHcls = NULL;
  V4 = (struct var4 **) malloc (sizeof(struct var4 *)*MAX_ATOM);
  Memory_count += (sizeof(struct var4 *)+sizeof(struct var4))*MAX_ATOM;

  Gcl_size = (1 << GROW);
  Slot_total = Slot_avail = Gcl_size + Clause_num;
  Gclauses = (struct gclause **) malloc(sizeof(struct gclause *)*Slot_avail);
  if (Gclauses == NULL) { fprintf(stderr, "run out of memory\n"); exit(1); }
  Memory_count += sizeof(struct gclause *)*(Slot_avail);

  for (i=0; i <= Max_atom; i++)  {
    el = (struct var4 *) tp_alloc(sizeof(struct var4));
    el->pos = el->neg = NULL;
    el->key = i;
    el->next = NULL;
    el->neg_count = el->pos_count = 0;

    /* GROW techniques */
    el->gmark = NULL;
    el->level = 0;
    el->dfs = 0; 
    V4[i] = el;
  }

  Ucl_queue = get_gclause_array(MAX_STACK);
  Gclause_New = get_gclause_array(MAX_STACK);
}

struct gclause * insert_gclause (cl_arr, sign_arr, total)
     int cl_arr[], sign_arr[];
     int total;
{
  int key, i, j=0;
  struct gclause *cl;
  struct glink *gl;

  if (total == 1) { 
    Unit_cls[Unit_cls_idx++] = (sign_arr[cl_arr[0]])? cl_arr[0] : -cl_arr[0];
    Clause_num++;
    return NULL;
  }

  if ((cl= get_gclause(total)) == NULL) {
#ifdef MORETRACE
    if (TRACE == 4 || TRACE > 8) printf("the slot is full\n");
#endif
    return NULL;
  }

  /* at first, insert positive literals */
  for (i=0; i < total; i++) {
    key = cl_arr[i];
    if (sign_arr[key] == 1) {
      cl->lits[j++] = key;
      gl = get_glink();
      gl->cl = cl;
      gl->next = V4[key]->pos;
      V4[key]->pos = gl;
      V4[key]->pos_count++;
    }
  }
  cl->psize = j;

  /* now, insert negative literals */
  for (i=0; i < total; i++) {
    key = cl_arr[i];
    if (sign_arr[key] == 0) {
      cl->lits[j++] = key;
      gl = get_glink();
      gl->cl = cl;
      gl->next = V4[key]->neg;
      V4[key]->neg = gl;
      V4[key]->neg_count++;
    }
  }

#ifdef MORETRACE
  if (TRACE > 9) { printf("New: "); print_gclause(cl); }
#endif

  cl->watch1 = 0;
  cl->watch2 = 1;
  Clause_num++;
  return cl;
}

int delete_gclause (cl)
     struct gclause *cl;
{
  int j, k;
  for (j = 0; j < cl->psize; j++) {
    k = cl->lits[j];
    V4[k]->pos = delete_glink(V4[k]->pos, cl);
  }
  for (j = cl->psize; j < cl->osize; j++) {
    k = cl->lits[j];
    V4[k]->neg = delete_glink(V4[k]->neg, cl);
  }
}

void print_all_gclauses ()
{
  int i;

  printf("all clauses\n");
  for (i = Slot_avail; i < Slot_total; i++) print_gclause(Gclauses[i]);
}

void print_gclause (cl)
     struct gclause *cl;
{
  int j;

  printf("size=%d w1=%d w2=%d ( ", 
	 cl->osize, cl->watch1, cl->watch2);
  for (j = 0; j < cl->psize; j++) 
    printf("%d[%d] ", cl->lits[j], Value[cl->lits[j]]);
  for (j = cl->psize; j < cl->osize; j++) 
    printf("-%d[%d] ", cl->lits[j], Value[cl->lits[j]]);
  printf(")\n");
}

void print_var4_gclause (i, flag)
     int i, flag;
{
  int j, l;
  struct glink *gl;

  if (V4[i]->pos && flag % 2) {
    printf("/******* Positive clauses for variable %d.*******/\n",i);
    gl = V4[i]->pos;
    while (gl != NULL) {
      print_gclause(gl->cl);
      gl = gl->next;
    }
  }
  
  if (V4[i]->neg && flag > 1) {
    printf("/******* Negative clauses for variable %d.*******/\n",i);
    gl = V4[i]->neg;
    while (gl != NULL) {
      print_gclause(gl->cl);
      gl = gl->next;
    }
  }
}

check_gclause (cl)
     struct gclause *cl;
{
  int j, s=0, c=0;

  for (j = 0; j < cl->psize; j++) 
    if (Value[cl->lits[j]] == TT) s = 1;
    else if (Value[cl->lits[j]] == DC) c++;
  for (j = cl->psize; j < cl->osize; j++) 
    if (Value[cl->lits[j]] == FF) s = 1;
    else if (Value[cl->lits[j]] == DC) c++;
  if (!s && !c) {
    printf("W: ");
    print_gclause(cl);
    return 1;
  }
  return 0;
}

check_all_gclauses ()
{
  int i, j;
  for (i = Slot_avail; i < Slot_total; i++)
    if (check_gclause(Gclauses[i])) {
      for (j = 0; j < Gclauses[i]->psize; j++)
	 print_var4_gclause(Gclauses[i]->lits[j], 1); 
      for (j = Gclauses[i]->psize; j < Gclauses[i]->osize; j++)
	 print_var4_gclause(Gclauses[i]->lits[j], 2); 
    }
}

struct gclause **get_gclause_array (size)
     int size;
{
  struct gclause **p;

  p = (struct gclause **) malloc(sizeof(struct gclause *)*size);
  if (p == NULL) { fprintf(stderr, "get_gclause_array return NULL.\n"); exit(1); }
  Memory_count += sizeof(struct gclause *)*size;
  return p;
}

int saton_search ()
{
  int i;    
  Top_var4 = V4[0];
  Unit_cls_idx = Clause_num = 0;

  for (i = 1; i <= Max_atom; i++) {
    if (Value[i] != DC) Unit_cls[Unit_cls_idx++] = i;
    if (SELECT == 6) {
      Weight1[i] = V4[i]->pos_count;
      Weight2[i] = V4[i]->neg_count;
    } else {
      Weight1[i] = V4[i]->pos_count + V4[i]->neg_count;
    }
    V4[i]->pos_count = V4[i]->neg_count = 0;
  }
  if (handle_known_values() == UNSAT) return 0;

  if (SELECT == 2 && !NHcls)
    for (i = Slot_avail; i < Slot_total; i++) if (Gclauses[i]->psize > 1) {
      struct glink *gl = get_glink();
      gl->cl = Gclauses[i];
      gl->next = NHcls;
      NHcls = gl;
    }
  
  i = var4_next_key();
  /* the major loop goes here. */
  while (!Stop && i) {
    if (propagate_all(i>>1, i & 1) != UNSAT) {
      i = var4_next_key();
    } else {	
      i = var4_prev_key();
    }
  } /* while */

  return ((Branch_succ > 0)? 1 : Stop);
}

int var4_next_key ()
{
  int i, s;
  
  if (OLDV) {
    int flag = TT;

    while (OLDV && flag) {
      i = Old_value[--OLDV];
      if (i < 0) { i = -i; flag = FF; }

      if (Value[i] != DC) flag = TT;
      else {
	Value[i] = flag;

	if (Old_choice[OLDV] == TT) {
	  Backup[Backup_idx++] = i;
	  Top_var4 = V4[i];
	  Top_var4->level = ++Branch_open;
	  Branch_num++;
	} else
	  Backup[Backup_idx++] = -i;

#ifdef MORETRACE
	print_let_x_have;
#endif
	if (grow_propagate(i, flag, 0) == UNSAT) {
	  return var4_prev_key();
	}
	return (i << 1)+flag;
      }
    }
  }

  s = var4_best_key();
  if (!s) return var4_succ_end();

  Branch_open++;
  Branch_num++;
  
  if (Backup_idx >= MAX_STACK) {
    fprintf ( stderr, "MAX_STACK(%d) is too small in var4_next_key().\n", 
	      MAX_STACK);
    Stop = STOP_MEMO;
  }

  i = s >> 1;
  Backup[Backup_idx++] = i;
  Top_var4 = V4[i];
  Top_var4->level = Branch_open;
  Top_var4->gmark = NULL;
  Value[i] = s & 1;

#ifdef MORETRACE
  print_let_x_have;
#endif

  if (grow_propagate(i, s & 1, 0) == UNSAT) return var4_prev_key();
  return s;
}

void var4_clean_dependents (act)
     struct var4 *act; 
{
  struct var4 *it, *next;
  int i;
  
  it = act->next;
  while (it != NULL) {
    if (Value[i=it->key] != DC) {
#ifdef MORETRACE
      print_up_to_x;
#endif
      Value[i] = DC;
      V4[i]->gmark = NULL;
    }
    next = it->next;
    it->next = NULL;
    it = next;
  }
  if (Value[i=act->key] != DC) {
#ifdef MORETRACE
      print_up_to_x;
#endif
      Value[i] = DC;
  }
  V4[i]->gmark = NULL;
  act->next = NULL;
}

struct gclause * locate_gmark (key, sign)
     int key, sign;
{
  struct glink *gl = (sign)? V4[key]->pos : V4[key]->neg;
  int n=3;

  while (gl && n) {
    int i, k;
    struct gclause *cl = gl->cl;
    for (i = 0; i < cl->psize; i++) if ((k = cl->lits[i]) != key) {
      if (Value[k] != FF) goto endl;
    }
    for (i = cl->psize; i < cl->osize; i++) if ((k = cl->lits[i]) != key) {
      if (Value[k] != TT) goto endl;
    }
    return cl;

  endl: 
    n--;
    gl = gl->next;
  } 
  return NULL;
}

struct var4 * set_top_var4 ()
{
  int i=Backup_idx;
  while (i) { if (Backup[--i]>0) return V4[Backup[i]]; }
  return V4[0];
}

int var4_prev_key ()
{
  int i, s;
  
  /* printf("a There are %d branches (%d open, %ld failed, %d jumped, l=%d).\n", 
     Branch_num, Branch_open, Branch_fail, Branch_jump, Conflict_cl_level); */

  if (!Branch_open) return 0;
  OLDV = 0; 
  Ucl_queue_idx = Ucl_queue_idx_end = 0;

  if (JUMP && Conflict_cl_level < Branch_open) {

#ifdef MORETRACE
    if (TRACE > 2)
      printf("    Backjumping from level %d to %d\n", 
	     Branch_open, Conflict_cl_level);
#endif

    while (Backup_idx && Branch_open >= Conflict_cl_level) {
      if ((i = Backup[--Backup_idx]) < 0) { i = -i;  }
      else if (Branch_open) { Branch_jump++;  Branch_open--; }
      var4_clean_dependents(V4[i]);
    }
    Branch_jump--;
  }

  if (Backjumping_down) {
    Backjumping_down = 0;
    if (!Backup_idx) {
      if (propagate_gcl() == UNSAT) {
	return 0;
      }
      return var4_next_key();
    }
    i = Backup[Backup_idx-1];
    Top_var4 = set_top_var4();
    if (i < 0) i = -i;

#ifdef MORETRACE
    if (TRACE > 2)
      printf("    Back to x%d=%d, [%d,%d,%d]\n",
	     i, Value[i], V4[i]->level, Branch_open, Conflict_cl_level);
#endif
    /*
     printf("b There are %d branches (%d open, %ld failed, %d jumped).\n", 
     Branch_num, Branch_open, Branch_fail, Branch_jump); */
    return (i << 1)+Value[i];
  } else {
    s = 1;
    while (s && Backup_idx) {
      if ((i = Backup[--Backup_idx]) < 0) {
	var4_clean_dependents(V4[-i]);
      } else { 
	s = 0;
	Backup_idx++;
      }
    }
    Branch_open--;

    if (!Backup_idx) {
      /* printf("e There are %d branches (%d open, %ld failed, %d jumped, l=%d).\n", 
	 Branch_num, Branch_open, Branch_fail, Branch_jump, Conflict_cl_level); */
      return 0;
    }
    s = NEG(Value[i]);
    var4_clean_dependents(V4[i]);
    Backup[Backup_idx-1] = -i;
    V4[i]->level = Branch_open;
    Top_var4 = set_top_var4();
    /* Hope that gclauses imply i later */
    /* printf("c There are %d branches (%d open, %ld failed, %d jumped) return %d at %d.\n", 
       Branch_num, Branch_open, Branch_fail, Branch_jump, i, Backup_idx); */
    return (i << 1)+s;
  }
}

int var4_best_key()
{
  /* switch (SELECT) */
  if (SELECT == 6) return var4_strategy6();
  else if (SELECT == 7) return var4_strategy7();
  else if (SELECT == 8) return var4_strategy8();
  else if (SELECT == 2) return var4_strategy2();
  else if (SELECT == 1) return var4_strategy1();
  else if (SELECT == 5) return var4_strategy5();
  else if (SELECT == 4) return var4_strategy4();
  else if (SELECT == 3) return var4_strategy3();
  else if (SELECT == 9) return var4_strategy9();
  else if (SELECT == 10) return var4_strategy0();
  return var4_strategy7();
}

int var4_strategy0 ()
     /* the least unsigned variable */
{
  int i; 
  
  for (i = 1; (i <= Max_atom); i++) if (Value[i] == DC) 
    return (i << 1)+ CHOICE1;
  return 0;
}

int p_times_n (i, sign, flag)
     int i, *sign, flag;
{
  int n=0, p=0;
  struct glink *gl;
  
  gl = (flag)? V4[i]->input_pos : V4[i]->pos;
  while (gl) {
    struct gclause *cl = gl->cl;
    if (Value[cl->lits[cl->watch1]] == DC && Value[cl->lits[cl->watch2]] == DC) p++;
    gl = gl->next;
  }
  if (!p) { 
    save_assign_value(i, FF);
#ifdef MORETRACE
    print_x_pure;
#endif
    Pure_num++;
    return 0;
  }

  gl = (flag)? V4[i]->input_neg : V4[i]->neg;
  while (gl) {
    struct gclause *cl = gl->cl;
    if (Value[cl->lits[cl->watch1]] == DC && Value[cl->lits[cl->watch2]] == DC) n++;
    gl = gl->next;
  }
  if (!n) { 
    save_assign_value(i, TT);
#ifdef MORETRACE
    print_x_pure;
#endif
    Pure_num++;
    return 0;
  }
  *sign = (flag)? ((p > n)? FF : TT) : ((p > n)? TT : FF); 
  return (p+n);
}

select_best_p_n (n, best_keys)
     int n, best_keys[];
{
  int i, s, best=0, best_v, best_i;
    
  for (i = n-1; i >= 0; i--) {
    n = p_mom_n(best_keys[i], &s); 
    if (n > best) { best = n; best_i = i; best_v = s; }
  }
  if (best) {
    Value[best_keys[best_i]] = best_v;
    return best_keys[best_i];
  } else return 0;
} 

p_mom_n (i, sign)
     int i, *sign;
{
  int n=0, p=0;
  struct glink *gl;
  
  gl = V4[i]->pos;
  while (gl) {
    struct gclause *cl = gl->cl;
    if (cl->lits[cl->watch1] == i) {
      if (Value[cl->lits[cl->watch2]] == DC) p++;
    } else if (cl->lits[cl->watch2] == i) {
      if (Value[cl->lits[cl->watch1]] == DC) p++;
    } 
    gl = gl->next;
  }

  gl = V4[i]->neg;
  while (gl) {
    struct gclause *cl = gl->cl;
    if (cl->lits[cl->watch1] == i) {
      if (Value[cl->lits[cl->watch2]] == DC) n++;
    } else if (cl->lits[cl->watch2] == i) {
      if (Value[cl->lits[cl->watch1]] == DC) n++;
    } 
    gl = gl->next;
  }
  *sign = (p > n)? TT : FF;
  return (p+n);
}

int var4_strategy1 ()
     /* MOM */
{
  int i, j, best_i = 0, best = 0, best_w, best_v=0, s;

  for (i = 1; i <= Max_cand; i++) if (Value[i] == DC) {
    j = p_mom_n(i, &s); 
    /*printf("key %d has weight %d and w1w2=%d\n", i, Weight1[i], j);*/
    if (j > best) { best = j; best_i = i; best_w = Weight1[i]; best_v = s; }
    else if (j == best && Weight1[i] > best_w) 
      { best_i = i; best_w = Weight1[i]; }
  }
  return (best_i << 1)+best_v;
}

int var4_strategy2 ()
     /* the heaviest unsigned variable in non-horn clause */
{
  int key=0, i, j;
  int min = MAX_LIST;
  struct gclause *cl;
  struct glink *gl = NHcls;

  while (gl) {
    cl = gl->cl;
    j = 0;
    if (Value[cl->lits[cl->watch1]] == DC && Value[cl->lits[cl->watch2]] == DC) {
      for (i = 0; i < cl->psize; i++) if (Value[cl->lits[i]] == DC) {
	key = cl->lits[i];
	if (++j >= min) goto label;
      }
    }
    min = j;
    
  label: 
    gl = gl->next;
  }

  if (key) return (key << 1)+CHOICE1;
  return 0;
}

int var4_strategy3 ()
     /* pick one with most active clauses; use Weight1 to break tie */
{
  int i, j, best_i = 0, best = 0, best_w, best_v=0, s;

  for (i = 1; i <= Max_cand; i++) if (Value[i] == DC) {
    j = p_times_n(i, &s, 0); 
    /*printf("key %d has weight %d and w1w2=%d\n", i, Weight1[i], j);*/
    if (j > best) { best = j; best_i = i; best_w = Weight1[i]; best_v = s; }
    else if (j == best && Weight1[i] > best_w) 
      { best_i = i; best_w = Weight1[i]; }
  }
  if (best_i) return (best_i << 1)+best_v;
  return 0;
}

int var4_strategy4 ()
     /* the same as var4_strategy3, but look at input clauses only */
{
  int i, j, best_i = 0, best = 0, best_w, best_v=0, s;

  for (i = 1; i <= Max_cand; i++) if (Value[i] == DC) {
    j = p_times_n(i, &s, 1); 
    /*printf("key %d has weight %d and w1w2=%d\n", i, Weight1[i], j);*/
    if (j > best) { best = j; best_i = i; best_w = Weight1[i]; best_v = s; }
    else if (j == best && Weight1[i] > best_w) 
      { best_i = i; best_w = Weight1[i]; }
  }
  if (best_i) return (best_i << 1)+best_v;
  return 0;
}

int var4_strategy5 ()
     /* same as var4_strategy6 but use p_time_n to break tie */
{
  int i, x, best_keys[1000];
  int best = -1, j = 0;

  for (i = 1; i <= Max_atom; i++) if (Value[i] == DC) {
    if ((x=Weight1[i]) > best)
      { best_keys[0] = i; j = 1; best = x; }
    else if (x == best) 
      { best_keys[j++] = i; }
  }

  if (j) {
    i = select_best_p_n(j, best_keys);
    return (i)? (i<<1)+CHOICE1 : var4_strategy6();
  }
  return 0;
}

int var4_strategy6 ()
     /* the least heavest literal */
{
  int i, best_i = 0, best = -10, best_v = 0;

  if (Branch_num & 255 == 0) {
    for (i = 1; i <= Max_atom; i++) {
      Weight1[i] = (Weight1[i] >> 1) + V4[i]->pos_count;
      Weight2[i] = (Weight2[i] >> 1) + V4[i]->neg_count;
      V4[i]->pos_count = V4[i]->neg_count = 0;
    }}

  /*
  for (i = 1; i <= Max_atom; i++) if (Value[i] == DC) {
    if (Weight2[i] > best) {
      best_i = i; best = Weight2[i]; best_v = FF; 
    } else if (Weight1[i] > best) { 
      best_i = i; best = Weight1[i]; best_v = TT; 
    } else if (Weight2[i] == best) {
      if (best_v == TT && Weight1[i] > Weight2[best_i])
	  { best_i = i; best = Weight2[i]; best_v = FF; }
      else if (best_v == FF && Weight1[i] > Weight1[best_i])
	  { best_i = i; best = Weight2[i]; best_v = FF; }
    } else if (Weight1[i] == best) {
      if (best_v == TT && Weight2[i] > Weight2[best_i])
	  { best_i = i; best = Weight1[i]; best_v = TT; }
      else if (best_v == FF && Weight2[i] > Weight1[best_i])
	  { best_i = i; best = Weight1[i]; best_v = TT; }
    }
  } 
  */

  for (i = 1; i <= Max_atom; i++) if (Value[i] == DC) {
    if (Weight2[i] > best) {
      best_i = i; best = Weight2[i]; best_v = FF; 
    } else if (Weight1[i] > best) { 
      best_i = i; best = Weight1[i]; best_v = TT; 
    } 
  } 

  if (best_i) return (best_i << 1)+best_v;
  return 0;
}

int var4_strategy7 ()
     /* the least heavest literal */
{
  int i, x, best_i = 0;
  int best = -1;

  if (Branch_num & 255 == 0) {
    for (i = 1; i <= Max_atom; i++) {
      Weight1[i] = (Weight1[i] >> 1) + V4[i]->pos_count + V4[i]->neg_count;
      V4[i]->pos_count = V4[i]->neg_count = 0;
    }}

  for (i = 1; i <= Max_atom; i++) 
    if (Value[i] == DC && (x=(Weight1[i])) > best)
      { best_i = i; best = x; }
  if (best_i) return (best_i << 1)+CHOICE1;
  return 0;
}

int var4_strategy8 ()
     /* an random heavest literal */
{
  int i, x, best_keys[1000];
  int best = -1, j = 0;

  for (i = 1; i <= Max_atom; i++) if (Value[i] == DC) {
    if ((x=(Weight1[i])) > best)
      { best_keys[0] = i; j = 1; best = x; }
    else if (x == best) 
      { best_keys[j++] = i; }
  }
  if (j) {
    i = best_keys[rand() % j];
    return (i << 1)+(rand() % 2);
  } 
  return 0;
}

int var4_strategy9 ()
     /* same as var4_strategy8 but use p_time_n to break tie */
{
  int i, x, best_keys[1000];
  int best = -1, j = 0;

  for (i = 1; i <= Max_atom; i++) if (Value[i] == DC) {
    if ((x=(Weight1[i])) > best)
      { best_keys[0] = i; j = 1; best = x; }
    else if (x == best) 
      { best_keys[j++] = i; }
  }

  if (j) {
    i = select_best_p_n(j, best_keys);
    return (i)? (i << 1)+CHOICE1 : var4_strategy8();
  } 
  return 0;
}

int adjust_conflict_level (cl_arr, sign_arr, total, down)
     int cl_arr[], sign_arr[], total, *down;
{
  int l, i, c=0, hl=0, highest=0, second_high=0, u;

  for (i = 0; i < total; i++) {
    l = V4[cl_arr[i]]->level;
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

  if (c > 1 || ++second_high == highest) { *down = 0; return highest; }

  /* if only one variable is the highest */
#ifdef MORETRACE
  if (TRACE > 8 || TRACE == 5) {
    printf("New level %d, %d, %d\n", second_high, highest, Branch_open);
  }
#endif

  /* Remember this unit literal */
  if (second_high) { /* u << 1 + sign_arr[u] */ 
    Unit_cls[--Unit_cls_idx_end] = (sign_arr[u])? u : -u;
  }
  *down = 1;
  return (second_high);
}

void var4_record_conflict (gcl0)
     struct gclause *gcl0;
{
  int i, j, num;
  int sign_arr[MAX_LIST], cl_arr[MAX_LENGTH];
  struct gclause *gcl=gcl0;

  Conflict_cl_level = Branch_open;

  num = var4_collect_parents(gcl, cl_arr);
  if (num > 0) {

#ifdef MORETRACE
    if (TRACE == 4 || TRACE > 8) {
      printf("Fresh [%d]: (", Branch_open);
      for (i = 0; i < num; i++) {
	j = cl_arr[i];
	printf(" %d(%d,%d)", j, Value[j], V4[j]->level);
      }
      printf(" )\n");
    }
#endif

    /* remove level 0 variables */
    /* fix the sign of literals in the new clause */
    for (i = 0; i < num; i++) {
      j = cl_arr[i];
      V4[j]->dfs = 0;
      if (V4[j]->level == 0) {
	cl_arr[i--] = cl_arr[--num];
      } else {
	sign_arr[j] = NEG(Value[j]);
      }
    }

#ifdef MORETRACE
    if (TRACE >= 3) {
      printf("NC [%d]: (", Branch_open);
      for (i = 0; i < num; i++) {
	j = cl_arr[i];
	printf(" %s%d", ((sign_arr[j])? "" : "-"), j);
      }
      printf(" )\n");
    }
    if (LINE == 4000) {
      for (i = 0; i < num; i++) {
	j = cl_arr[i];
	if (sign_arr[j] == Model[j]) i = MAX_LIST;
      }
      if (i < MAX_LIST) { printf("c WARNING\n"); exit(0); }
    }
#endif

    gcl = insert_gclause(cl_arr, sign_arr, num);
    if (gcl) {
      Gclause_New[Gclause_New_idx++] = gcl;
      if (Gclause_New_idx >= MAX_STACK) {
	fprintf(stderr, "MAX_STACK(%d) is too small in var4_record_conflict().\n", 
		MAX_STACK);
	Stop = STOP_MEMO;
      }
    }
    if ((num = adjust_conflict_level(cl_arr, sign_arr, num, &i)) < Conflict_cl_level) {
      Conflict_cl_level = num;
      Backjumping_down = i;
    }
  }
}

var4_collect_parents (gcl0, cl_arr)
     struct gclause *gcl0;
     int cl_arr[];
{
  int key, i, j, var_num=0, total=0, first=1, max_level=0;
  int stamp = 1;
  struct gclause *gcl=gcl0;
  struct var4 *el, *el0;

#ifdef MORETRACE
  if (TRACE>1) { printf("conflict: "); print_gclause(gcl); }
#endif

  for (j = 0; j < gcl->osize; j++) 
    if ((i=V4[gcl->lits[j]]->level) > max_level) max_level = i;

  for (j = 0; j < gcl->osize; j++) {
    if (V4[key=gcl->lits[j]]->level < max_level) {
      cl_arr[total++] = key;
    } else {
      var_num++;
#ifdef MORETRACE
      if (TRACE>3) printf("queue %d\n", key);
#endif
    }
    V4[key]->dfs = stamp; 
  }

  if (Top_var4->level > max_level) {
    i = Backup_idx;
    while (i && (Backup[--i] < 0 || V4[Backup[i]]->level > max_level));
    el0 = V4[i];
  } else { el0 = Top_var4; }

  el = el0->next;
  while (el) {
    if (V4[key=el->key]->dfs == stamp && V4[key]->level == max_level) {
#ifdef MORETRACE
      if (TRACE>3) printf("unqueue %d\n", key);
#endif
      if (--var_num == 0) {
	if (!first) { cl_arr[total++] = key; return total; }
      }
      if (gcl=el->gmark) {
#ifdef MORETRACE
	if (TRACE>3) print_gclause(gcl);
#endif
	for (j = 0; j < gcl->osize; j++) 
	  if (V4[i = gcl->lits[j]]->dfs != stamp) { 
	    if (V4[i]->level < max_level) {
	      cl_arr[total++] = i;
	    } else {
	      var_num++;
	      if (TRACE>3) printf("queue %d\n", i);
	    }
	    V4[i]->dfs = stamp; 
	  }
	first = 0;
      } else cl_arr[total++] = key;
      V4[key]->dfs = 0;
    }
    el = el->next;
  }

  if (V4[key=el0->key]->dfs == stamp) {
#ifdef MORETRACE
    if (TRACE>3) printf("unqueue %d\n", key);
#endif
    if (var_num == 1) {
      if (!first) { cl_arr[total++] = key; return total; }
    }
  }
 
#ifdef MORETRACE
  if (TRACE>1) {
    if (gcl=el0->gmark) { printf("Where from: "); print_gclause(gcl); }
    printf("failed %d\n", var_num); fflush(stdout); 
  }
#endif

  for (i = 0; i < total; i++) V4[cl_arr[i]]->dfs = 0;
  return 0;
}

int grow_propagate (key, sign, save)
     int key, sign, save;
{
  struct var4 *el = V4[key];
  struct gclause *cl;
  struct glink *gl;

  /* remember the vars for backtracking */
  if (save && el != Top_var4) {
    el->next = Top_var4->next;
    Top_var4->next = el;
  }

  gl = (sign)? el->neg : el->pos;
  while (gl) {
    cl = gl->cl; 
    if (cl->lits[cl->watch1] == key) {
      if (check_gcl_watch1(cl) == UNSAT) {
#ifdef MORETRACE
	if (TRACE > 8 || TRACE == 4) {
	  printf("EMPTY: ");
	  print_gclause(cl);
	}
#endif
	if (SELECT > 6) add_weight1(key);
	return var4_fail_end(cl);
      }
    } else if (cl->lits[cl->watch2] == key) {
      if (check_gcl_watch2(cl) == UNSAT) {
	if (SELECT > 6) add_weight1(key);
	return var4_fail_end(cl);
      }
    }
    gl = gl->next;
  }

  return SAT;
}

int check_gcl_key (cl, k, sign)
     struct gclause *cl;
     int k, sign;
{
  if (Value[k] == DC) {
    cl->unit = (sign)? k : -k;
    Ucl_queue[Ucl_queue_idx_end++] = cl;
    /* Ucl_queue[Ucl_queue_idx++] = cl;*/
#ifdef MORETRACE
    if (TRACE > 8 || TRACE == 6) {
      printf("unit cl %d from ", cl->unit);
      print_gclause(cl);
    }
#endif
    return 0;
  } else if (Value[k] != sign) {
#ifdef MORETRACE
    if (TRACE == 4 || TRACE > 8) {
      printf("EmpTy: ");
      print_gclause(cl);
    }
#endif
    if (SELECT > 6) add_weight1(k);
    return UNSAT;
  } else 
    return 0;
}

int check_gcl_watch1 (cl)
     struct gclause *cl;
{
  if (cl->osize < 2) return UNSAT;
  if (cl->osize == 2) {
    return check_gcl_key(cl, cl->lits[1], (cl->psize > 1)? 1 : 0);
    /*
  } else if (cl->osize == 3) {
    int s1, s2, k1, k2;

    if (cl->watch1) {
      k1 = cl->lits[0], s1 = (cl->psize)? 1 : 0;
    } else {
      k1 = cl->lits[1], s1 = (cl->psize > 1)? 1 : 0;
    }
    k2 = cl->lits[2]; s2 = (cl->psize > 2)? 1 : 0;

    if (Value[k1] == DC) {
      if (Value[k2] == DC) { 
	cl->watch1 = 1 - cl->watch1; 
	cl->watch2 = 2; 
	return 0; 
      } else if (Value[k2] == TT) {
	if (s2) return 0;
	return check_gcl_key(cl, k1, s1);
      } else {
	if (s2 == FF) return 0;
	return check_gcl_key(cl, k1, s1);
      }
    } else if (Value[k1] == TT) {
      if (s1) return 0;
      return check_gcl_key(cl, k2, s2);
    } else {
      if (s1 == FF) return 0;
      return check_gcl_key(cl, k2, s2);
    }
    */
  } else {
    int i, w2_false=0;

    if (Value[i=cl->lits[cl->watch2]] != DC) { 
      if (Value[i] == TT) {
	if (cl->watch2 < cl->psize) return 0;
      } else if (cl->watch2 >= cl->psize) return 0;
      w2_false = 1;
    }

    /* looking at the left of watch1 */
    for (i = 0; i < cl->watch1; i++) {
      if (Value[cl->lits[i]] == DC) { 
	cl->watch1 = i; 
	if (w2_false) return check_gcl_watch2(cl);
	return 0; 
      }
      if (Value[cl->lits[i]] == TT) { 
	if (i < cl->psize) return 0;
      } else if (i >= cl->psize) return 0;
    }
    /* at this point, the left of watch1 is empty. */

    /* looking between watch1 and watch2 */
    for (i = cl->watch1+1; i < cl->watch2; i++) {
      if (Value[cl->lits[i]] == DC) { 
	cl->watch1 = i; 
	if (w2_false) return check_gcl_watch2(cl);
	return 0; 
      }
      if (Value[cl->lits[i]] == TT) { 
	if (i < cl->psize) return 0;
      } else if (i >= cl->psize) return 0;
    }

    /* at this point, the left of watch2 is empty. */
    for (i = cl->watch2+1; i < cl->osize; i++) {
      if (Value[cl->lits[i]] == DC) { 
	if (w2_false) {
	  cl->watch2 = i;
	  w2_false = 0;
	} else {
	  cl->watch1 = cl->watch2;
	  cl->watch2 = i;
	  return 0; 
	}
      } else if (Value[cl->lits[i]] == TT) { 
	if (i < cl->psize) return 0;
      } else if (i >= cl->psize) return 0;
    }

    /* at this point, the right of watch2 is empty. */
    return check_gcl_key(cl, cl->lits[cl->watch2],
			 (cl->watch2 < cl->psize)? 1 : 0);
  }
}

int check_gcl_watch2 (cl)
     struct gclause *cl;
{
  if (cl->osize < 2) return UNSAT;
  if (cl->osize == 2) {
    return check_gcl_key(cl, cl->lits[0], (cl->psize)? 1 : 0); 
    /*
  } else if (cl->osize == 3) {
    int s1, s2, k1, k2;

    if (cl->watch2 == 2) {
      k2 = cl->lits[1], s2 = (cl->psize > 1)? 1 : 0;
    } else {
      k2 = cl->lits[2]; s2 = (cl->psize > 2)? 1 : 0;
    }
    k1 = cl->lits[0], s1 = (cl->psize)? 1 : 0;

    if (Value[k1] == DC) {
      if (Value[k2] == DC) { 
	cl->watch1 = 0; 
	cl->watch2 = 3 - cl->watch2; 
	return 0; 
      } else if (Value[k2] == TT) {
	if (s2) return 0;
	return check_gcl_key(cl, k1, s1);
      } else {
	if (s2 == FF) return 0;
	return check_gcl_key(cl, k1, s1);
      }
    } else if (Value[k1] == TT) {
      if (s1) return 0;
      return check_gcl_key(cl, k2, s2);
    } else {
      if (s1 == FF) return 0;
      return check_gcl_key(cl, k2, s2);
    }
    */
  } else {
    int i, w1_false = 0;

    if (Value[i=cl->lits[cl->watch1]] != DC) { 
      if (Value[i] == TT) {
	if (cl->watch1 < cl->psize) return 0;
      } else if (cl->watch1 >= cl->psize) return 0;
      w1_false = 1;
    }

    /* looking at the right of watch2 */
    for (i = cl->watch2+1; i < cl->osize; i++) {
      if (Value[cl->lits[i]] == DC) { 
	cl->watch2 = i; 
	if (w1_false) return check_gcl_watch1(cl);
	return 0; 
      }
      if (Value[cl->lits[i]] == TT) { 
	if (i < cl->psize) return 0;
      } else if (i >= cl->psize) return 0;
    }
    /* at this point, the right of watch2 is empty. */

    /* looking between watch1 and watch2 */
    for (i = cl->watch1+1; i < cl->watch2; i++) {
      if (Value[cl->lits[i]] == DC) {
	cl->watch2 = i; 
	if (w1_false) return check_gcl_watch1(cl);
	return 0; 
      }
      if (Value[cl->lits[i]] == TT) { 
	if (i < cl->psize) return 0;
      } else if (i >= cl->psize) return 0;
    }

    /* at this point, the left of watch2 is also empty. */
    for (i = cl->watch1-1; i >= 0; i--) {
      if (Value[cl->lits[i]] == DC) { 
	if (w1_false) {
	  cl->watch1 = i;
	  w1_false = 0;
	} else {
	  cl->watch2 = cl->watch1;
	  cl->watch1 = i;
	  return 0; 
	}
      }
      if (Value[cl->lits[i]] == TT) { 
	if (i < cl->psize) return 0;
      } else if (i >= cl->psize) return 0;
    }

    /* at this point, the left of watch1 is empty. */
    return check_gcl_key(cl, cl->lits[cl->watch1], 
			 (cl->watch1 < cl->psize)? 1 : 0);
  }
}

int propagate_gcl ()
{
  int i, s;

  /* check newly generated unit clauses */
  while (Unit_cls_idx) {
    i = Unit_cls[--Unit_cls_idx];
    if (i > 0) s = 1; else { s = 0; i = -i; }
    if (Value[i] == DC) { 
      V4[i]->level = 0;
      V4[i]->gmark = NULL;
      Value[i] = s;

#ifdef MORETRACE
      if (TRACE > 8) printf("unit");
      print_x_has_to;
#endif
      if (grow_propagate(i, s, 0) == UNSAT) {
#ifdef MORETRACE
	print_up_to_x;
#endif
	Value[i] = DC;
	return UNSAT;
      }
    } else if (Value[i] != s) {
      if (TRACE > 1) printf("F1 ");
      return var4_fail_end(NULL);
    }
  }

  /* check newly generated clauses for unit or empty clauses */
  for (s = Gclause_New_idx-1; s >= 0; s--) {
    int l, j, k;
    struct gclause *gcl = Gclause_New[s];
    i=-1, l = 0;
    for (j = 0; j < gcl->osize; j++) {
      if (Value[k=gcl->lits[j]] == DC) {
	if (i > -1) { gcl->watch1 = i; gcl->watch2 = j; j = MAX_LIST; }
	else { i = j; }
      } else if (Value[k] == TT) {
	if (j < gcl->psize) j = MAX_SHORT;
	else if (V4[k]->level > l) {
	  l = V4[k]->level;
	}
      } else if (j >= gcl->psize) {
	j = MAX_SHORT;
      } else if (V4[k]->level > l) {
	l = V4[k]->level;
      }
    }

    if (j < MAX_SHORT) { /* clause is either empty or unit */
      if (i == -1) {
	if (TRACE > 1) { printf("F2 at %d ", Branch_open); print_gclause(gcl); }
	return var4_fail_end(NULL);
      } else { 
	int s = (i < gcl->psize)? 1 : 0;
	i = gcl->lits[i];
	V4[i]->gmark = gcl;
	V4[i]->level = l;
	Value[i] = s;

#ifdef MORETRACE
	if (TRACE > 2) {
	  printf("\nforced x%d(%d,%d) at %d,%d: (", 
		 i, s, l, Branch_open, Top_var4->level);
	  for (j = 0; j < gcl->psize; j++) {
	    printf(" %d[%d,%d]", gcl->lits[j], 
		   Value[gcl->lits[j]], V4[gcl->lits[j]]->level);
	  }
	  for (j = gcl->psize; j < gcl->osize; j++) {
	    printf(" -%d[%d,%d]", gcl->lits[j], 
		   Value[gcl->lits[j]], V4[gcl->lits[j]]->level);
	  }
	  printf(")\n\n");
	}
	print_x_has_to;
#endif
	if (grow_propagate(i, s, 1) == UNSAT) {
	  return UNSAT;
	}
      }
    } else if (j >= MAX_LIST) { /* now delete this gcl from the pool */
      /* printf("deleted "); print_gclause(gcl); */
      if (s < --Gclause_New_idx) Gclause_New[s] = Gclause_New[Gclause_New_idx];
    }
  }

  /*printf("top=%d ", Top_var4->key);*/
  return handle_unit_clauses();
}

int propagate_all (i, sign)
     int i, sign;
{
  if (propagate_gcl() == UNSAT) return UNSAT;
  if (Value[i] == DC) {
    Value[i] = sign; 
    V4[i]->gmark = NULL;
    V4[i]->level = Branch_open;
#ifdef MORETRACE
    if (GROW && (TRACE > 8 || TRACE == 4))  printf("  (%d)", V4[i]->level);
    print_now_let_x_have;
#endif
    if (grow_propagate(i, sign, 1) == UNSAT) return UNSAT;
  } else if (Value[i] != sign) {
    /* struct gclause *cl = V4[i]->gmark;
       printf("F2: x%d=%d, %d ", i, sign, Value[i]); 
       if (V4[i]->gmark) print_gclause(V4[i]->gmark);
       Value[i] = sign;
       V4[i]->gmark = NULL; */
    return var4_fail_end(NULL);
  } else if (Value[i] != sign) return UNSAT;

  return handle_unit_clauses();
}

handle_known_values ()
{
  while (Unit_cls_idx) {
    int k = Unit_cls[--Unit_cls_idx];
    if (grow_propagate(k, Value[k], 0) == UNSAT) return UNSAT;
  }
  return (handle_unit_clauses());
}

int handle_unit_clauses ()
     /* handle each unit clause one by one ... */
{
  /* now handle gclauses */
  while (Ucl_queue_idx < Ucl_queue_idx_end) {
    /* while (Ucl_queue_idx) */
    int i, sign;
    struct var4 *el;
    struct gclause *cl = Ucl_queue[Ucl_queue_idx++];
    /* struct gclause *cl = Ucl_queue[--Ucl_queue_idx];*/
    i = cl->unit;
    sign = 1; 

    if (i < 0) { i = -i; sign = 0; }
    if (Value[i] == DC) {
      Value[i] = sign;

#ifdef MORETRACE
      if (TRACE > 8) printf("gcl");
      print_x_has_to;
#endif

      if (GROW) {
	el = V4[i];
	el->gmark = cl; 
	el->level = Branch_open;
      }
      if (grow_propagate(i, sign, 1) == UNSAT) return UNSAT;
    } if (Value[i] != sign) {
      if (SELECT > 6) add_weight1(i);
      return var4_fail_end(cl);
    }
  }
  return SAT;
}

int var4_succ_end ()
{
  Branch_succ++;

#ifdef MORETRACE
  if (TRACE == 2) printf("S%d\n", Branch_succ);
#endif

  print_model(stdout);
  return ((MODEL && Branch_succ >= MODEL)? 0 : var4_prev_key());
}

int var4_fail_end (cl)
     struct gclause *cl;
{
  Branch_fail++;
  Unit_cls_idx_end = MAX_STACK;

  if (GROW && cl && Branch_open) var4_record_conflict(cl);

#ifdef MORETRACE
  if (TRACE > 8 || TRACE == 3 || TRACE == 4) {
    printf(" empty cl: "); 
    if (cl) print_gclause(cl);
  }
#endif

  if (Stop = check_stop(1)) {
    if (TRACE >= 0) {
      printf("\nThe search is aborted with search tree path:\n");
      output_guide_path(stdout);
      printf("\n");
    }
  }
  return UNSAT;
}
