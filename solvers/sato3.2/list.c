/*********************************************************************
; Copyright 1992-97, The University of Iowa (UI).  All rights reserved. 
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
; This software and any associated documentation is provided "as is," and
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
#include "list.h"

void list_init_once_forall()
{
  int i;

  if (sizeof(struct elem) % sizeof(int *)) 
    printf("\nWARNING: sizeof(struct elem) = %d\n", sizeof(struct elem));
  if (sizeof(struct clause) % sizeof(int *)) 
    printf("\nWARNING: sizeof(struct clause) = %d\n", sizeof(struct clause));

  Tape_space = (int **) malloc ( sizeof(int *) * MAX_TAPE);
  Memory_count += ( sizeof(int *) * MAX_TAPE);

  for (i = 0; i < MAX_TAPE; i++) Tape_space[i] = NULL;
  L = NULL;
  Clause = NULL;
  NHClause = NULL;
  EMPTY = get_clause();
}

int get_tape ()
{
  int *temp;
  
  /* Tape_limit[Tape_count] = Tape_offset-1; */
  if (++Tape_count < MAX_TAPE) {
    Tape_offset = 0;
    if (Tape_space[Tape_count] == NULL) {
      temp = (int *) malloc((TAPE_BLOCK) * (sizeof(int)));
      if (temp == NULL) {
	fprintf(stderr, "ABEND, malloc returns NULL (out of memory).\007\n");
	fprintf(stderr, "%ld K has been mallocated.\007\n", Memory_count/1042);
	exit(0);
      }
      Memory_count += ( sizeof(int *) * TAPE_BLOCK);
      Tape_space[Tape_count] = temp;
    }
    return 1;
  } else  {
    return 0;
  }
}

void init_list (max_atom)
     int max_atom;
{
  int i;
  struct elem *el;

  printf("Storing clauses as lists of integers.\n");
  if (Clause != NULL && Clause != EMPTY) free_clause(Clause);
  if (NHClause != NULL) free_clause(NHClause);
  NHClause = Clause = NULL;
  
  if (L != NULL) free(L);
  L = (struct elem **) malloc ( sizeof ( struct elem *) * (1+max_atom ));
  if (L == NULL) {
    fprintf ( stderr, "init_list returns NULL.\n");
    exit(1);
  }
  Memory_count += ( sizeof ( struct elem *) * (1+max_atom ));

  for (i=0; i <= max_atom; i++)  {
    el = (struct elem *) tp_alloc ( sizeof ( struct elem ) );
    el->pos_address = 0;
    el->neg_address = 0;
    el->pos_count = 0;
    el->neg_count = 0;
    el->key = i;
    el->idx = 0;
    el->depen[1] = 0;
    el->depen[0] = 0;
    L[i] = el;
  }

  Tape_offset = 0;
  Tape_count = 0;
  if (Tape_space[0] == NULL) {
    Tape_space[0] = (int *) malloc((TAPE_BLOCK) * (sizeof(int)));
    Memory_count += (TAPE_BLOCK) * (sizeof(int));
  }
}

int list_insert_clause (cl_arr, sign_arr, total)
     int cl_arr[], sign_arr[];
     int total;
{
  int key, i, j;
  int cl_add, pcount;
  struct clause *cl;

  if (Clause == EMPTY) return 1;

  if (total == 0) { /* an empty clause is found */
    
#ifdef MORETRACE
    if (TRACE > 6)
      fprintf(Sato_fp, "    [C%d] becomes empty.\n", Clause_num);
#endif
    if (Clause != NULL) free_clause(Clause);
    Clause = EMPTY;
    return 1;
  }

  if ((Tape_offset+total+4) > TAPE_BLOCK) {
    if (!get_tape()) {
      printf("The clause list is too big to handle.\n");
      return 2;
    }
  }

  cl = get_clause();
  cl_add = cl->address = address_of(Tape_count, Tape_offset);
  j = 0;

  /* at first, insert positive literals */
  for (i=0; i < total; i++) {
    key = cl_arr[i];
    if (sign_arr[key] == 1) {
      nth_lit_of_clause(cl_add, j++) = key;
      L[key]->pos_count++;
    }
  }
  pcount = j;

  for (i=0; i < total; i++) {
    key = cl_arr[i];
    if (sign_arr[key] == 0) {
      nth_lit_of_clause(cl_add, j++) = -key;
      L[key]->neg_count++;
    }
  }

  size_of_clause(cl_add) = total;
  stamp_of_clause(cl_add) = 0;
  count_of_clause(cl_add) = total;
  pcount_of_clause(cl_add) = pcount;
  Tape_offset += 4 + total;
  
  if (pcount > 1) {
    cl->next = NHClause;
    NHClause = cl;
  } else {
    cl->next = Clause;
    Clause = cl;
  }
  return 0;
}

int create_variable_table ()
{
  int i;
  int pos, neg;
  struct elem *el;

  if (Clause != EMPTY) {
  for (i = 1; i <= Max_atom; i++) {
    el = L[i];

    pos = el->pos_count;
    neg = el->neg_count;
    if ((Tape_offset + pos + neg) > TAPE_BLOCK) {
      if (!get_tape()) {
	printf("The size of the problem is too big to handle.\n");
	return 1;
      }
    }

    if ((pos == 0 || neg == 0) && Value[i] == DC) {
      assign_value(i, (pos == 0)? FF : TT);
      print_x_pure;
    }

    if (pos > 0) {
      el->pos_address = address_of(Tape_count, Tape_offset);
      Tape_offset += pos;
    } 

    if (neg > 0) {
      el->neg_address = address_of(Tape_count, Tape_offset);
      Tape_offset += neg;
    }
  }

  fill_in_clauses(NHClause);
  fill_in_clauses(Clause);
}
  return 0;
}

void fill_in_clauses (temp)
     struct clause *temp;
{
  int cl_add, k, i, pcount;

  while (temp != NULL) {
    cl_add = temp->address;

    /* scan the positive literals first */
    pcount = pcount_of_clause(cl_add);
    for (i = pcount-1; i >= 0; i--) {
      k = nth_lit_of_clause(cl_add, i);
      content_of(L[k]->pos_address, (L[k]->depen[1])++) = cl_add;
    }

    /* then, scan the negative literals */
    for (i = count_of_clause(cl_add)-1; i >= pcount; i--) {
      k = -nth_lit_of_clause(cl_add, i);
      content_of(L[k]->neg_address, (L[k]->depen[0])++) = cl_add;
    }
    temp = temp->next;
  }
}

void print_variable_clause( i )
     int i;
{
  int j, l;
  int cl_add;
  if (L[i]->pos_count > 0) {
    printf("/******* here is the positive clauses for variable %d.*******/\n",i);
    for (j=0; j<L[i]->pos_count; j++) {
      cl_add = content_of(L[i]->pos_address, j);
      printf("( ");
      for (l=0; l<size_of_clause(cl_add); l++) {
	printf("%d ", content_of(cl_add, 4+l));
      }
      printf(")\n");
    }
  }
  
  if (L[i]->neg_count > 0) {
    printf("/******* here is the negative clauses for variable %d.*******/\n",i);
    for (j=0; j<L[i]->neg_count; j++) {
      cl_add = content_of(L[i]->neg_address, j);
      printf("( ");
      for (l=0; l<size_of_clause(cl_add); l++) {
	printf("%d ", content_of(cl_add, 4+l));
      }
      printf(")\n");
    }
  }
}

struct clause *get_clause()
{
  struct clause *p;
  
  Clause_gets++;

  if (Clause_avail == NULL) {
    p = ( struct clause * ) tp_alloc ( sizeof ( struct clause ) );
    Clause_news++;
  } else {
    Clause_avails--;
    p = Clause_avail;
    Clause_avail = Clause_avail->next;
  }
  
  p->next = NULL;
  return(p);
} 

void free_clause (cl)
     struct clause *cl;
{
  struct clause *no;

  while (cl != NULL) {
    no = cl;
    cl = cl->next;
    free_clause_cell(no);
  }
}


/***********************************************************/
/** search for a model **/
/***********************************************************/

list_search ()
{
  int res = 0;

  if (Clause == NULL) {
    Branch_num = Branch_succ = 1;
    fprintf(Sato_fp, "\nEvery atom has a fixed truth value.\n");
    if (TRACE > 0) print_model(Sato_fp);
    res = 1;
  } else if (Clause == EMPTY) {
    Branch_num = Branch_fail = 1;
    fprintf(Sato_fp, "\nAn empty clause is found from the first %ld clauses.\n",
	   Clause_num);
    res = 0;
  } else {
    
    Branch_num = 1;
    Branch_fail = Branch_succ = 0;
    
    res = list_search2();
  }
  return res;
}

int list_search2 ()
{
  struct elem *it;
  int i;    
  
  if (create_variable_table()) return 2;
  list_collect_unit_clauses();
  
  Top_elem = L[0];
  i = list_next_key(0);

  /* the major loop goes here. */
  while (!Stop && i > 0) {
    
    Top_elem = it = L[i];
    
    if (Value[i] == TT) {
      
      if (propagate_true(it) != UNSAT)
	i = list_next_key(i);
      else {
	i = list_prev_key(0);
      }
      
    } else { /* Value[i] == FF */
      
      if (propagate_false(it) != UNSAT) {
	i = list_next_key(i);
      } else {
	i = list_prev_key(0);
      }
      
    }
  } /* while */

  return ((Branch_succ > 0)? 1 : (Stop)? 2 : 0);
}

int list_next_key (i)
     int i;
{
  if (list_handle_unit_clauses() == UNSAT) return list_prev_key(1);

  if ((i = list_best_key()) == 0) return handle_succ_end();
  
  if (OLDV && i < 10000 && Old_value[i] == CHOICE2) { 
    Value[i] = CHOICE2;
    Backup[Backup_idx++] = -i;

#ifdef MORETRACE
    print_let_x_have;
#endif

  } else {
    int first_try;

    if (i > 10000) {
      i -= 10000;
      first_try = CHOICE2;
    } else
      first_try = CHOICE1;

    Branch_open++;
    Branch_num++;
  
    Value[i] = first_try;
    if (Backup_idx >= MAX_LIST) {
      fprintf ( stderr, "MAX_LIST(%d) is too small in next_key(%d).\n", 
	       MAX_LIST, i);
      Stop = 1;
    }
    Backup[Backup_idx++] = i;

#ifdef MORETRACE
    print_let_x_have;
#endif
  
  }

  return i;
}

int list_best_key()
{
  if (SELECT == 0) { 
    return list_strategy2();
  } else if (SELECT == 10) {
    return strategy0();
  } else if (SELECT == 1) {
    return list_strategy1();
  } else if (SELECT == 2) { 
    return list_strategy2();
  } else if (SELECT == 3) {
    return list_strategy3();
  }else if (SELECT == 4) {
    return list_strategy4();
  } else if (SELECT >= 6 && SELECT <= 9) {
    return list_strategy6_9();
  } else {
    fprintf ( stderr, "Unknown option: -s%d\n", SELECT);
    return (Stop = 1);
  }
}

int list_strategy1()
     /* return an open variable in a shortest positive clause */
{
  int i, k, min_clause_add;
  int min_pos_clause = TAPE_BLOCK;
  struct clause *cl = NHClause;

  while (cl != NULL) {
    if (active_clause(k = cl->address))
      if ((i = count_of_clause(k)) == pcount_of_clause(k)) 
	if (min_pos_clause > i) {
	  min_pos_clause = i;
	  min_clause_add = k;
	  if (i <= 2) goto end;
	}
    cl = cl->next;
  }
  
  if (min_pos_clause == TAPE_BLOCK) return 0;

 end:
  for (i = size_of_clause(min_clause_add)-1; i >= 0; i--) {
    k = nth_lit_of_clause(min_clause_add, i);
    if ((k > 0) && Value[k] == DC) return k;
  }
  return 0;
}

int list_strategy2()
     /* return an open variable with the maximal 
	binary occurrences, then any occurrences */
{
  int i,j,k = 0;
  int clist_address, clist_count, cl_add;
  int actural_occurrences, most_occurrences;
  int most_binary_occurrences = -1;
  int actural_binary_occurrences;
  
  for (i=1; i<= Max_atom; i++) {
    if (Value[i] == DC) {
      actural_binary_occurrences = actural_occurrences = 0;
      clist_address = L[i]->pos_address;
      clist_count = L[i]->pos_count;
      j = 0;
      while (j < clist_count) {
	cl_add = content_of(clist_address,j);
	if (active_clause(cl_add)) {
	  actural_occurrences++;
	  if (count_of_clause(cl_add) == 2)
	    actural_binary_occurrences++;
	}
	j++;
      }
      
      clist_address = L[i]->neg_address;
      clist_count = L[i]->neg_count;
      j = 0;
      while (j < clist_count) {
	cl_add = content_of(clist_address,j);
	if (active_clause(cl_add)) {
	  actural_occurrences++;
	  if (count_of_clause(cl_add) == 2)
	    actural_binary_occurrences++;
	}
	j++;
      }
      
      if (actural_binary_occurrences > most_binary_occurrences) {
	most_binary_occurrences = actural_binary_occurrences;
	most_occurrences = actural_occurrences;
	k = i;
      } else if (actural_binary_occurrences == most_binary_occurrences &&
		 actural_occurrences > most_occurrences) {
	most_occurrences = actural_occurrences;
	k = i;
      }
      
    }
  }	
  return k;
}

int list_strategy3()
     /* return an open variable with the maximal occurrences */
{
  int i,j,k = 0;
  int clist_address, clist_count, cl_add;
  int most_occurrences = -1;
  int actural_occurrences;
  
  for (i=1; i<= Max_atom; i++) {
    if (Value[i] == DC) {
      actural_occurrences = 0;
      clist_address = L[i]->pos_address;
      clist_count = L[i]->pos_count;
      j = 0;
      while (j < clist_count) {
	cl_add = content_of(clist_address,j);
	if (active_clause(cl_add)) actural_occurrences++;
	j++;
      }
      
      clist_address = L[i]->neg_address;
      clist_count = L[i]->neg_count;
      j = 0;
      while (j < clist_count) {
	cl_add = content_of(clist_address,j);
	if (active_clause(cl_add)) actural_occurrences++;
	j++;
      }
      
      if (actural_occurrences > most_occurrences) {
	most_occurrences = actural_occurrences;
	k = i;
      }
      
    }
  }	
  return k;
}

int list_strategy4()
     /* return an open variable with the maximal binary occurrences */
{
  int i,j;
  int k= 0;
  int clist_address, clist_count, cl_add;
  int most_binary_occurrences;
  int actural_binary_occurrences;
  
  most_binary_occurrences = -1;
  for (i=1; i<= Max_atom; i++) {
    if (Value[i] == DC) {
      actural_binary_occurrences = 0;
      clist_address = L[i]->pos_address;
      clist_count = L[i]->pos_count;
      j = 0;
      while (j < clist_count) {
	cl_add = content_of(clist_address, j);
	if (active_clause(cl_add) &&
	    count_of_clause(cl_add) == 2)
	  actural_binary_occurrences++;
	j++;
      }
      clist_address = L[i]->neg_address;
      clist_count = L[i]->neg_count;
      j = 0;
      while (j < clist_count) {
	cl_add = content_of(clist_address, j);
	if (active_clause(cl_add) &&
	    count_of_clause(cl_add) == 2)
	  actural_binary_occurrences++;
	j++;
      }
      if (actural_binary_occurrences > most_binary_occurrences) {
	most_binary_occurrences = actural_binary_occurrences;
	k = i;
      }
    }
  }
  return k;
} 


int list_strategy6_9()
{
  return list_strategy1();
}  


int list_prev_key (first)
     int first;
{
  int i, sign, second_try;
  
  OLDV = Tmp_idx = 0;
  
  while (Backup_idx > 0) {
    i = Backup[--Backup_idx];
    if (i < 0) {
      sign = 0; 
      i = -i; 
    } else {
      sign = 1; 
      second_try = NEG(Value[i]);
      Branch_open--;
    }
    
#ifdef MORETRACE
    print_up_to_x;
#endif
    if (first) list_clean_dependents(L[i]);
    
    if (sign == 1) {
      Backup[Backup_idx++] = -i;
      Value[i] = second_try;

#ifdef MORETRACE
      print_x_has_to;
#endif
      
      return i;
    } else {
      Value[i] = DC;
      first = 1;
    }
  }
  return Stop = 0;
}

int propagate_true (el)
     struct elem *el;
{
  int cl_add, cl_add_2;
  int clist_1_address, clist_2_address;
  int clist_1_count, count, ii, jj;
  int key = el->key;
  int old_ucl_idx = Tmp_idx;

  /* decrement the count of clauses in which key appears negatively. */
  clist_1_address = el->neg_address;
  clist_1_count = el->neg_count;
  ii = 0;
  while (ii < clist_1_count) {
    cl_add = content_of(clist_1_address, ii);
    if (active_clause(cl_add)) {
      count = --count_of_clause(cl_add);
      if (count == 0) { 	
	/* restore what is done so far and then backtrack */
	clist_2_address = el->neg_address;
	jj = 0;	
	while ( ii != jj ) { 
	  cl_add_2 = content_of(clist_2_address,jj);
	  if (active_clause(cl_add_2)) {
	    count_of_clause(cl_add_2)++;
	  }
	  jj++;
	}
	count_of_clause(cl_add)++;
	Tmp_idx = old_ucl_idx;
	return handle_fail_end();
      } else if (count == 1) {
	/* store unit clauses in an array */
	Tmp[Tmp_idx++] = cl_add;
      }
    }
    ii++;
  }
  
  /* freeze clauses in which key appears positively. */
  clist_1_address = el->pos_address;
  clist_1_count = el->pos_count;
  ii = 0;
  while ( ii < clist_1_count ) {
    cl_add = content_of(clist_1_address, ii);
    if (active_clause(cl_add)) {
      stamp_of_clause(cl_add) = key;
    }
    ii++;
  }
    
  /* remember the element for backtracking */
  Top_elem->depen[Top_elem->idx++] = key;
  if (Top_elem->idx == MAX_STACK) {
    Top_elem = el;
    Top_elem->depen[Top_elem->idx++] = key;
  }
  return SAT;
}

int propagate_false (el)
     struct elem *el;
{
  int cl_add, cl_add_2;
  int clist_1_address, clist_2_address;
  int clist_1_count, count, ii, jj;
  int key = el->key;
  int old_ucl_idx = Tmp_idx;
  
  /* decrement the count of clauses in which key appears negatively. */
  clist_1_address = el->pos_address;
  clist_1_count = el->pos_count;
  ii = 0;
  while (ii < clist_1_count) {
    cl_add = content_of(clist_1_address, ii);
    if (active_clause(cl_add)) {
      --pcount_of_clause(cl_add);
      count = --count_of_clause(cl_add);
      if (count == 0) { 	
	/* restore what is done so far and then backtrack */
	clist_2_address = el->pos_address;
	jj = 0;	
	while ( ii != jj ) { 
	  cl_add_2 = content_of(clist_2_address,jj);
	  if (active_clause(cl_add_2)) {
	    pcount_of_clause(cl_add_2)++;
	    count_of_clause(cl_add_2)++;
	  }
	  jj++;
	}
	pcount_of_clause(cl_add)++;
	count_of_clause(cl_add)++;
	Tmp_idx = old_ucl_idx;
	return handle_fail_end();
      } else if ( count == 1 ) {
	/* store unit clauses in an array */
	Tmp[Tmp_idx++] = cl_add;
      }
    }
    ii++;
  }
  
  /* freeze clauses in which key appears positively. */
  clist_1_address = el->neg_address;
  clist_1_count = el->neg_count;
  ii = 0;
  while ( ii < clist_1_count ) {
    cl_add = content_of(clist_1_address, ii);
    if (active_clause(cl_add)) {
      stamp_of_clause(cl_add) = key;
    }
    ii++;
  }
  
  /* remember the element for backtracking */
  Top_elem->depen[Top_elem->idx++] = key;
  if (Top_elem->idx == MAX_STACK) {
    Top_elem = el;
    Top_elem->depen[Top_elem->idx++] = key;
  }
  return SAT;
}

void list_clean_dependents (act)
     struct elem *act;
{
  int s, i, idx, sign;
  struct elem *it, *depens[MAX_LIST];
  int clist_1_address;
  int clist_1_count, ii;
  int cl_add;
  
  /* at first, collect all the dependents */
  idx = 0;
  while (act != NULL) {
    depens[idx++] = act;
    if (act->idx == MAX_STACK)
      act = L[act->depen[--act->idx]];
    else 
      act = NULL;
  }
  
  while (idx > 0) {
    act = depens[--idx];
    for (s = act->idx-1; s >= 0; s--) {
      i = act->depen[s];
      it = L[i];
      
#ifdef MORETRACE
      print_up_to_x;
#endif
      
      sign = Value[i];
      Value[i] = DC;
      
      /* defreeze clauses */
      clist_1_address = (sign)? it->pos_address : it->neg_address;
      clist_1_count = (sign)? it->pos_count : it->neg_count;
      ii = 0;
      while ( ii < clist_1_count ) {
	cl_add = content_of(clist_1_address, ii);
	if (stamp_of_clause(cl_add) == i)
	  stamp_of_clause(cl_add) = 0;
	ii++;
      }
      
      /* increment the counter of clauses */
      if (sign) {
	clist_1_address = it->neg_address;
	clist_1_count = it->neg_count;
	ii = 0;
	while ( ii < clist_1_count ) {
	  cl_add = content_of(clist_1_address, ii);
	  if (active_clause(cl_add)) {
	    count_of_clause(cl_add)++ ;
	  }
	  ii++;
	}
      } else {
	clist_1_address = it->pos_address;
	clist_1_count = it->pos_count;
	ii = 0;
	while ( ii < clist_1_count ) {
	  cl_add = content_of(clist_1_address, ii);
	  if (active_clause(cl_add)) {
	    pcount_of_clause(cl_add)++;
	    count_of_clause(cl_add) ++ ;
	  }
	  ii++;
	}
      }
    }
    act->idx = 0;
  }
}

int list_collect_unit_clauses ()
     /* search through Clause and collect all the unit clauses 
	into Tmp. */
{
  int i;
  
  /* at first, handle known unit clauses */
  if (Tmp_idx > MAX_ATOM) {
    fprintf ( stderr, "Tmp_idx (%d) > MAX_ATOM (%d).\n", Tmp_idx, MAX_ATOM);
    exit(1);
  }

  i = MAX_ATOM;
  while (Tmp_idx > 0) {
    Tmp[--i] = Tmp[--Tmp_idx];
    if (Tmp[i] > Max_atom) bug(Tmp[i]);
  }

  Top_elem = L[0];
  while (i < MAX_ATOM) {
    if (propagate(L[Tmp[i]], Value[Tmp[i]]) == UNSAT) 
      return UNSAT;
    i++;
  }
  
  return SAT;
}

int list_handle_unit_clauses ()
     /* handle each unit clause one by one ... */
{
  int i, cl_add, cl_size4, ii;

  while (Tmp_idx > 0) {
    
    cl_add = Tmp[--Tmp_idx];
    
    if (active_clause(cl_add)) {
      if (count_of_clause(cl_add) == 0) {
	return handle_fail_end();
      }
      
      /* at first locate the literal which has no value */
      cl_size4 = size_of_clause(cl_add) + 4;

      if (pcount_of_clause(cl_add)) {
	/* the atom is poitive */
	ii = 4;
	while ( ii < cl_size4 ) {
	  i = content_of(cl_add,ii);
	  if (i < 0) { bug(i); i = -i; }
	  if (Value[i] == DC) {
	    Value[i] = TT;
	    ii = cl_size4;
	  } else
	    ii++;
	}
      } else {
	/* the atom is negative */
	ii = cl_size4 - 1;
	while ( ii >= 0 ) {
	  i = -content_of(cl_add,ii);
	  if (i < 0) { bug(i); i = -i; }
	  if (Value[i] == DC) {
	    Value[i] = FF;
	    ii = -1;
	  } else 
	    ii--;
	}
      }
      
#ifdef MORETRACE
      print_x_has_to;
#endif

      if (propagate(L[i], Value[i]) == UNSAT) {
	
#ifdef MORETRACE
	print_up_to_x;
#endif
	
	Value[i] = DC;
	return UNSAT;
      }
    }
  }
  return SAT;
}

void print_a_clause (cl_add)
     int cl_add;
{
  int clause_size, ii;
  int cl_size4;
  
  printf("( ");
  
  clause_size = size_of_clause(cl_add);
  cl_size4 = clause_size+4;
  ii = 4;
  while ( ii < cl_size4 ) {
    printf("%d ", content_of(cl_add, ii));
    ii++;
  }
  printf(")\n");
}

void print_clause_address(a, b)
     int a, b;
{
  printf("The clause address is : %d.\n", content_of(a, b));
}

