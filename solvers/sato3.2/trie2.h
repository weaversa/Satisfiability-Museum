/********************************************************
  Code for a different search algorithm: DATA = 2
********************************************************/

#define trie2_propagate(a,b,c) \
  ((b)? trie2_propagate_true(a,c) : trie2_propagate_false(a,c))

void init_var2_table ()
{
  static int old_Max_atom;
  int i;
  struct var2 *el;

  if (V2 != NULL) {
    for (i=1; i <= old_Max_atom; i++)  {
      free(V2[i]);
    }
    free(V2);
  }

  old_Max_atom = Max_atom;
  i = sizeof ( struct var2 *) * (1+Max_atom );
  V2 = (struct var2 **) malloc ( i );
  Memory_count += i;

  if (V2 == NULL) {
    fprintf ( stderr, "var_table returns NULL.\n");
    exit(1);
  }

  for (i=0; i <= Max_atom; i++)  {
    V2[i] = el = (struct var2 *) tp_alloc ( sizeof ( struct var2 ) );

    /* basic stuff */
    set_id(el, i);
    el->next = NULL;
    el->pos = el->neg = NULL;
    el->neg_count = el->pos_count = 0;

    /* related to unit-propagations. */
    el->frozen = CLAUSE_MARK;                  /* frozen clauses */
    el->pure = 0; 

    /* GROW techniques */
    el->mark = NULL;
    el->level = 0;
    el->pos_extra = el->neg_extra = 0;
  }

  /*check_cl(0, NULL, NULL); */
  Trie2_Ucl = get_trie2_array(MAX_LIST);
  Trie2_Ucl_idx = 0;
}

struct trie **get_trie2_array (size)
     int size;
{
  struct trie **p;

  p = (struct trie **) malloc ( sizeof ( struct trie *) * size );
  if (p == NULL) {
    fprintf ( stderr, "get_trie2_array return NULL.\n");
    exit(1);
  }
  Memory_count += sizeof ( struct trie *) * size;
  return p;
}

long visit_trie2 (tr, par, pflag, count, pcount)
     struct trie *tr, *par;
     int count, pcount;
     /* Visit the whole trie.
	When go down, (a) assign the parent; (b) count the numbers
	of literals and positive literals; (d) if a CLAUSE_MARK is found, 
	create a clause node.
	When go up, return the number of clauses in the trie.
	*/
{
  if (tr == CLAUSE_MARK) {
    if (count == 2) Bicl_num++;

    tr = get_trie();
    tr->par = par;
    count_of_clause(tr) = count;

    if (pcount > 1) {
      tr->bro = NHtrie;
      NHtrie = tr;
      NH_num++;
    } else {
      tr->bro = CLtrie;
      CLtrie = tr;
    }
      /* print_clause_from_leaf(tr);*/

    return 1;

  } else {

    long y, x = 0;
    count++;

    while (tr != NULL) {
      int key = key_of(tr);
      tr->par = par;
      set_psign(tr, pflag);

      if (tr->pos != NULL) {
	y = visit_trie2(tr->pos, tr, 1, count, 1+pcount);
	V2[key]->pos_count += y;
	x += y;
      }

      if (tr->neg != NULL) {
	y = visit_trie2(tr->neg, tr, 0, count, pcount);
	V2[key]->neg_count += y;
	x += y;
      }
      tr = tr->bro;
    }
    return (x);
  }
}

void trie2_fill_in_clauses (cl)
     struct trie *cl;
{
  struct trie *tr, *son;
  struct var2 *el;

  while (cl != NULL) {
    tr = cl->par;
    el = V2[key_of(tr)];
    if (HAS_POS_CL(tr)) {
      el->pos[el->pos_count++] = cl;
    } else {
      el->neg[el->neg_count++] = cl;
    }

    son = tr;
    tr = tr->par;
    while (tr != NULL) {
      el = V2[key_of(tr)];
      if (psign_of(son)) {
	el->pos[el->pos_count++] = cl;
      } else {
	el->neg[el->neg_count++] = cl;
      }
      son = tr;
      tr = tr->par;
    }

    cl = cl->bro;
  }
}


int trie2_search2 ()
{
  struct var2 *it;
  int i;    
  
  Max_cand = (RENAME>1)? RENAME : Max_atom+1;
  Tmp_idx_end = MAX_ATOM;
  Top_var2 = V2[0];
  if (trie2_handle_known_values(0) == UNSAT) return 0;

  Nonunit_cls = NULL;
  i = trie2_next_key();
  
  /* the major loop goes here. */
  while (!Stop && i > 0) {
    Top_var2 = it = V2[i];

    if (Value[i] == TT) {
      if (trie2_propagate_true(it,0) != UNSAT)
	i = trie2_next_key();
      else {
	i = trie2_prev_key(0);
      }
    } else { /* Value[i] == FF */
      if (trie2_propagate_false(it,0) != UNSAT) {
	i = trie2_next_key();
      } else {
	i = trie2_prev_key(0);
      }
    }
  } /* while */

  return ((Branch_succ > 0)? 1 : (Stop)? 2 : 0);
}

int trie2_next_key ()
{
  int i;
  
  if (trie2_handle_unit_clauses(1) == UNSAT)
    return trie2_prev_key(1);
  
  if (OLDV) {
    int flag = TT;

    while (OLDV && flag) {
      i = Old_value[--OLDV];
      if (i < 0) { i = -i; flag = FF; }

      if (Value[i] != DC) flag = TT;
      else {
	Top_var2 = V2[i];
	Value[i] = flag;
	Stack2[Stack2_idx++] = i;
	level_of(Top_var2) = Branch_open;
	mark_of(Top_var2) = NULL;

	if (Old_choice[OLDV] == TT) {
	  Branch_open++;
	  Branch_num++;
	  Backup[Backup_idx++] = i;
	} else
	  Backup[Backup_idx++] = -i;

#ifdef MORETRACE
	print_let_x_have;
#endif

	return i;
      }
    }
  }

  i = trie2_best_key();
  if (i == 0) return handle_succ_end();

  Branch_open++;
  Branch_num++;
  
  if (Backup_idx >= MAX_LIST) {
    fprintf ( stderr, "MAX_LIST(%d) is too small in trie2_next_key().\n", 
	      MAX_LIST);
    Stop = 1;
  }

  Backup[Backup_idx++] = i;
  level_of(V2[i]) = Branch_open;
  mark_of(V2[i]) = NULL;
  Stack2[Stack2_idx++] = i;

#ifdef MORETRACE
  print_let_x_have;
#endif

  return i;
}

int trie2_prev_key (clean)
     int clean;
{
  int i;
  
  OLDV = Trie2_Ucl_idx = Tmp_idx = 0;
  Tmp_idx_end = MAX_ATOM;

  if (clean == 3) { clean--; Conflict_cl_level = Branch_open; }

  while (Backup_idx-- > 0) {
    if ((i = Backup[Backup_idx]) < 0) {
      int j;
      
      i = -i; 
      Conflict_cl = NULL;
      j = Conflict_cl_level;

      if (clean) trie2_clean_dependents(V2[i], clean-1);
      else {
#ifdef MORETRACE
	print_up_to_x;
#endif
	Stack2_idx--;
	Value[i] = DC;
      }
      clean = 2;

      if (GROW) {
	if (JUMP && j < Branch_open) {
	  int good = 1;
	  Jump_num++;

#ifdef MORETRACE
	  if (TRACE > 2)
	    printf("    Backjumping from level %d to %d\n", Branch_open, j);
#endif

	  while (good && Backup_idx) {
	    if ((i = Backup[--Backup_idx]) < 0) {
	      trie2_clean_dependents(V2[-i], clean);
	    } else if (level_of(V2[i]) > j) {
	      Branch_num--;
	      Branch_open--;
	      trie2_clean_dependents(V2[i], clean);
	    } else { 
	      Backup_idx++;
	      good = 0;
	    }
	  }
	}
      }
      clean = 2;
    } else {
      int NEXT_VALUE = NEG(Value[i]);

      Branch_open--;

      if (clean) {
	trie2_clean_dependents(V2[i], clean-1);
	Stack2[Stack2_idx++] = i;
      }
#ifdef MORETRACE
      else print_up_to_x;
#endif
      Value[i] = DC;

      if (GROW) {
	if (Conflict_cl == NULL || !trie_in_path(i, Conflict_cl->par)) {
	  mark_of(V2[i]) = NULL;
	} else {
	  mark_of(V2[i]) = Conflict_cl;
	}
	Conflict_cl = NULL;
	if (Conflict_cl_level > Branch_open) Conflict_cl_level = Branch_open;
	level_of(V2[i]) = Conflict_cl_level;
      }
  
      if (Old_cls != NULL) {
	struct trie *cl = Newtrie;
	while (cl != Old_cls) {
	  trie2_adjust_counts(cl);
	  cl = cl->bro;
	}
	Old_cls = NULL;
      }
      Backup[Backup_idx++] = -i;
      Value[i] = NEXT_VALUE;

#ifdef MORETRACE
      if (GROW && (TRACE > 8 || TRACE == 3 || TRACE == 4))
	  printf("  [%d]", level_of(V2[i]));
      print_now_let_x_have;
#endif

      return i;
    }
  }
  return Stop = 0;
}

int trie2_best_key()
{
  static int first = -1;
  if (first == -1 && JUMP > 1 && JUMP < 1000) { first = JUMP; }

  if (first > 0) {
    first--;
    return strategy0();
  }

  if (SELECT == 0) {
    return trie2_strategy1();
  } else if (SELECT == 1) {
    return trie2_strategy1();
  } else if (SELECT == 2) {
    return trie2_strategy2();
  } else if (SELECT == 3) {
    return trie2_strategy3();
  } else if (SELECT == 4) {
    return trie2_strategy4();
  } else if (SELECT == 5) {
    return trie2_strategy5();
  } else if (SELECT == 6 || SELECT == 7) {
    return trie2_strategy6();
  } else if (SELECT == 10) { 
    return strategy0();
  } else {
    fprintf ( stderr, "Unknown option(2): -s%d\n", SELECT);
    Stop = 1;
    return 0;
  }
}

int trie2_mom (total, keys)
     int total, keys[];
{
  int s, best_key, best_sign, sign, new, max_weight;
  best_sign = best_key = max_weight = 0;

#ifdef MORETRACE
  if (total && TRACE >= 4) 
    printf("There are %d MOM candidates.\n", total);
#endif

  for (s = 0; s < total; s++) {
    new = trie2_compute_mom(keys[s], &sign);
    if (new > max_weight) {
      best_key = keys[s];
      best_sign = sign;
      max_weight = new;
    }
  }

#ifdef MORETRACE
  if (total && TRACE >= 4) 
    printf("The winner is x%d.\n", best_key);
#endif

  Value[best_key] = best_sign;
  return best_key;
}

int trie2_compute_mom (i, sign)
     int i, *sign;
{
  int j, k, num_cls, pos_count, neg_count;
  struct trie *cl, **cls;

    pos_count = neg_count = 1;

    j = 0;
    cls = V2[i]->neg;
    num_cls = V2[i]->neg_count;
  
    for (k = 0; k < num_cls; k++) if (active_clause((cl=cls[k]))) { 
      j = 1; 
      if (count_of_clause(cl) == 2) {
	neg_count++;
      }
    }

    if (j == 0) {
      trie2_pure_delete(i, TT);
      return -1;
    }    

    j = 0;
    cls = V2[i]->pos;
    num_cls = V2[i]->pos_count;
  
    for (k = 0; k < num_cls; k++) if (active_clause((cl=cls[k]))) { 
      j = 1; 
      if (count_of_clause(cl) == 2) {
	pos_count++;
      }
    }
    
    if (j == 0) {
      trie2_pure_delete(i, FF);
      return -1;
    }    

#ifdef MORETRACE
  if (TRACE > 4) 
    printf("   key %d:  neg = %d, pos = %d\n", i, neg_count, pos_count);
#endif

  *sign = (neg_count > pos_count)? CHOICE2 : CHOICE1;
  return (neg_count * pos_count);
}

int trie2_strategy1 ()
     /* apply MOM to all active variables appearing
      in shortest non-Horn clauses */
{
  int i, x, y, min_len, total, keys[12];
  struct trie *cl = NHtrie;
  struct trie *cls[12];
  min_len = MAX_ATOM;
  total = 0;

  /* at first, collect all the shortnest clauses */
  while (cl != NULL) {
    if (active_clause(cl)) {
      if (count_of_clause(cl) < min_len) {
	min_len = count_of_clause(cl);
	cls[0] = cl;
	total = 1;
      } else if (total < MAGIC && count_of_clause(cl) == min_len) {
	cls[total++] = cl;
      }
    }
    cl = cl->bro;
  }

  if (total == 0) {
    return strategy0();
  }    

  /* then, colect active keys in the shortest clauses */
  i = total;
  y = 0;
  while  (i && y < MAGIC) {
    cl = cls[--i];
    cl = cl->par;
    while (cl != NULL && y < MAGIC) {
      x = key_of(cl);
      if (x < Max_cand && Value[x] == DC &&
	  V2[x]->pure != MAX_ATOM) {
	V2[x]->pure = MAX_ATOM;
	keys[y++] = x;
      }
      cl = cl->par;
    }
  }

  for (i = 0; i < y; i++) V2[keys[i]]->pure = 0;
  i = trie2_mom(y, keys);
  if (i == 0)  /* purecheck blocked the keys */
    return (trie2_strategy2());
  else 
    return i;
}

int trie2_strategy2 ()
{
  int i, total, keys[MAX_ATOM];

  total = 0;
  for (i = 1; i < Max_cand; i++)
    if (Value[i] == DC) keys[total++] = i;

  if (i = trie2_mom(total, keys)) return i;
  else {
    return strategy0();
  }
}

int trie2_strategy3 ()
     /* choose the min variable in the first shortest clause */
{
  int i;
  int min_clause_count = MAX_ATOM;
  struct trie *min_clause = NULL;
  struct trie *cl = NHtrie;

  while (cl != NULL) {
    if (active_clause(cl)) {
      i = count_of_clause(cl);
      if (i == psign_of(cl))
	if (min_clause_count > i) {
	  min_clause_count = i;
	  min_clause = cl;
	  if (i <= 2) cl = CLAUSE_MARK;
	}
    }
    cl = cl->bro;
  }
  
  if (min_clause == NULL) return strategy0();

#ifdef MORETRACE
  if (TRACE == 4) print_clause_from_leaf(min_clause);
#endif

  i = 0;
  cl = min_clause->par;
  while (cl != NULL) {
    if (key_of(cl) < Max_cand && Value[key_of(cl)] == DC) i = key_of(cl);
    cl = cl->par;
  }
  if (i == 0) i = strategy0();
  Value[i] = CHOICE1;
  return i;
}

int trie2_strategy4 ()
  /* choose a variable in a shortest clause;
     using the occurrence as the second criterion */
{
  int i, min_idx;
  int min_clause_count = MAX_ATOM;
  struct trie *min_clauses[50], *no;
  struct trie *cl = NHtrie;

  for (i = 1; i <= Max_atom; i++) V2[i]->pos2 = 0;
  min_idx = 0;

  while (cl != NULL) {
    if (active_clause(cl)) {

      if (min_clause_count > i) {
	min_clause_count = i;
	min_idx = 1;
	min_clauses[0] = cl;
      } else if (min_idx < 50 && min_clause_count == i) {
	min_clauses[min_idx++] = cl;
      }

      no = cl->par;
      while (no != NULL) {
	V2[key_of(no)]->pos2++;
	no = no->par;
      }
    }
    cl = cl->bro;
  }

  if (min_clause_count == MAX_ATOM) return 0;

  min_clause_count = 0;
  while (min_idx) {
    cl = min_clauses[--min_idx]->par;
    while (cl != NULL) {
      if (Value[key_of(cl)] == DC && 
	  min_clause_count <  V2[key_of(cl)]->pos2) {
	min_clause_count = V2[key_of(cl)]->pos2;
	i = key_of(cl);
	/*printf("key = %d, occ = %d\n", i, min_clause_count); */
      }
      cl = cl->par;
    }
  }

  Value[i] = CHOICE1;
  return i;
}

int trie2_strategy5 ()
  /* choose a variable with the highest occurrence */
{
  int i, min_idx, min_key;
  struct trie *no;
  struct trie *cl = (Newtrie)? Newtrie : NHtrie;

  for (i = 1; i <= Max_atom; i++) V2[i]->pos2 = 0;

  while (cl != NULL) {
    if (active_clause(cl)) {
      no = cl->par;
      while (no != NULL) {
	V2[key_of(no)]->pos2++;
	no = no->par;
      }
    }
    cl = cl->bro;
  }
  
  min_key = min_idx = 0;
  for (i = 1; i < Max_cand; i++) 
    if (Value[i] == DC && V2[i]->pos2 > min_idx) {
      min_idx = V2[i]->pos2;
      min_key = i;
    }

  if (min_key) {
    Value[min_key] = CHOICE1;
    return min_key;
  } else {
    return trie2_strategy2();
  }
}

int trie2_strategy6 ()
  /* choose a variable with the highest occurrence */
{
  int i, min_wei, min_key, pos_wei;
  struct trie *no;
  struct trie *cl = (Newtrie)? Newtrie : NHtrie;

  for (i = 1; i <= Max_atom; i++) V2[i]->pos2 = 0;
  min_wei = 0;

  while (cl != NULL) {
    if (active_clause(cl)) {
      no = cl->par;
      while (no != NULL) {
	V2[key_of(no)]->pos2 += 1;
	no = no->par;
      }
    }
    cl = cl->bro;
  }
  
  min_key = min_wei = 0;
  for (i = 1; i < Max_cand; i++) 
    if (Value[i] == DC && V2[i]->pos2 > min_wei) {
      min_wei = V2[i]->pos2;
      min_key = i;
    }

  if (min_key == 0) return trie2_strategy1();

  /* plus some weights for being positive */
  pos_wei = 0;
  for (i = V2[min_key]->pos_count-1; i >= 0; i--) 
    if (active_clause(V2[min_key]->pos[i])) pos_wei++;
  min_wei -= pos_wei;
  Value[min_key] = (min_wei >= pos_wei)? TT : FF; 
  return min_key;
}

int trie2_strategy7 ()
{
  struct trie *cl = (Newtrie)? Newtrie : NHtrie;
  int sign, key;

  while (innactive_clause(cl)) {
    cl = cl->bro;
    if (!cl) return trie2_strategy1();
  }
  cl = cl->par;
  sign = (HAS_POS_CL(cl))? 1 : 0;
  while (cl) {
    if (Value[key = key_of(cl)] == DC) {
      Value[key] = sign;
      return key;
    }
    sign = psign_of(cl);
    cl = cl->par;
  }
  return trie2_strategy1();
}

void trie2_pure_delete (i, sign)
     int i, sign;
{
  int j, num_cls;
  struct trie **cls, *frozens, *cl;
  struct var2 *el;

  Value[i] = sign;
  Stack2[Stack2_idx++] = i;
  el = V2[i];
  el->level = PURECHECK;
  mark_of(el) = NULL;
  Pure_num++;

#ifdef MORETRACE
  print_x_pure;
#endif

  el->next = Top_var2->next;
  Top_var2->next = el;

  if (sign == TT) {
    cls = el->pos;
    num_cls = el->pos_count;
  } else {
    cls = el->neg;
    num_cls = el->neg_count;
  }

  frozens = CLAUSE_MARK;
  for (j = 0; j < num_cls; j++) if (active_clause((cl=cls[j]))) {
    frozen_lin(cl) = frozens;
    frozens = cl;
  }
  frozen_cls(el) = frozens;
}

void trie2_pure_check ()
     /* implementing pure deletion */
{
  int i, j, k, num_cls;
  struct trie **cls;
  struct var2 *el;

  for (i = 1; i <= Max_atom; i++) if (Value[i] == DC) {

    j = 0;
    el = V2[i];
    cls = el->neg;
    num_cls = el->neg_count;
    for (k = 0; k < num_cls; k++) 
      if (active_clause(cls[k])) { k = num_cls; j = 1; }

    if (j == 0) trie2_pure_delete(i, TT);
    else {

      j = 0;
      cls = el->pos;
      num_cls = el->pos_count;
      for (k = 0; k < num_cls; k++) 
	if (active_clause(cls[k])) { k = num_cls; j = 1; }

      if (j == 0) trie2_pure_delete(i, FF);
    }
  }
}

trie2_handle_unit_lit (i, sign, save)
     int i, sign, save;
{ 
  if (Value[i] == DC) {
    trie2_assign_value(i, sign);
#ifdef MORETRACE
    print_x_has_to;
#endif
    if (save && trie2_propagate(V2[i], sign, save) == UNSAT) 
      return UNSAT;

  } else if (Value[i] != sign) {
    return UNSAT;
  }
  return SAT;
}

int trie2_propagate_true (el, save)
     struct var2 *el;
     int save;
{
  int key = id_of(el);
  int i, j, count, num_cls;
  struct trie **cls, *cl;

  /* decrement the count of clauses in which key appears negatively. */
  cls = el->neg;
  num_cls = el->neg_count;

  for (i = 0; i < num_cls; i++) {
    cl = cls[i];
    if (active_clause(cl)) {
      count = --count_of_clause(cl);
      if (count == 0) { 	
	/* restore what is done so far and then backtrack */
	count_of_clause(cl)++;

	for (j = 0; j < i; j++) {
	  if (active_clause(cls[j])) {
	    count_of_clause(cls[j])++;
	  }
	}
	if (save && GROW && Branch_open) trie2_record_conflict(cl);
	return handle_fail_end();
      } else if (count == 1) {
	/* store unit clauses in an array */
	Trie2_Ucl[Trie2_Ucl_idx++] = cl;
      }
    }
  }

  /* remember the key for freezing its positive clauses */
  Tmp[--Tmp_idx_end] = key;

  /* remember the vars for backtracking */
  if (save) {
    el->next = Top_var2->next;
    Top_var2->next = el;
  }
  return SAT;
}

int trie2_propagate_false (el, save)
     struct var2 *el;
     int save;
{
  int key = id_of(el);
  int i, j, count, num_cls;
  struct trie **cls, *cl;

  /* decrement the count of clauses in which key appears positively. */
  cls = el->pos;
  num_cls = el->pos_count;

  for (i = 0; i < num_cls; i++) {
    cl = cls[i];
    if (active_clause(cl)) {
      count = --count_of_clause(cl);
      if (count == 0) { 	
	/* restore what is done so far and then backtrack */
	count_of_clause(cl)++;
	for (j = 0; j < i; j++) 
	  if (active_clause(cls[j])) {
	    count_of_clause(cls[j])++;
	  }
	if (save && GROW && Branch_open) trie2_record_conflict(cl);
	return handle_fail_end();
      } else if (count == 1) {
	/* store unit clauses in an array */
	Trie2_Ucl[Trie2_Ucl_idx++] = cl;
      }
    }
  }

  /* remember the key for freezing its negative clauses */
  Tmp[--Tmp_idx_end] = key;
    
  /* remember the vars for backtracking */
  if (save) {
    el->next = Top_var2->next;
    Top_var2->next = el;
  }
  return SAT;
}

void trie2_clean_dependents (act, defreeze)
     struct var2 *act; int defreeze;
{
  struct var2 *it, *next;
  struct trie *cl, *cl2;
  
  /* at first, defreeze the clauses */
  if (defreeze) {
    it = act;
    while (it != NULL) {
      cl = frozen_cls(it);
      while (cl != CLAUSE_MARK) {
	cl2 = frozen_lin(cl);
	frozen_lin(cl) = NULL;
	cl = cl2;
      }
      frozen_cls(it) = CLAUSE_MARK;
      it = it->next;
    }
  }

  /* next, increase the counters */
  it = act->next;
  while (it != NULL) {
    trie2_clean_one_var(it);
    next = it->next;
    it->next = NULL;
    it = next;
  }
  trie2_clean_one_var(act);
  act->next = NULL;
}

void trie2_clean_one_var (it)
     struct var2 *it; 
{
  int i, j, sign, num_cls;
  struct trie **cls, *cl;

  i = id_of(it);

#ifdef MORETRACE
  print_up_to_x;
#endif

  sign = Value[i];

  if (it->level == PURECHECK) {
    it->level = 0;
  } else if (sign) {  

    /* increment the counter of clauses */
    cls = it->neg;
    num_cls = it->neg_count;
    for (j = 0; j < num_cls; j++) 
      if (active_clause((cl=cls[j]))) {
#ifdef PRIVATE
	if (TRACE > 3 && trie2_cl_count(cl) < count_of_clause(cl)) {
	  print_clause_from_leaf(cl);
	  bug(2000);
	}
#endif
	count_of_clause(cl)++;
      }
  } else {
    cls = it->pos;
    num_cls = it->pos_count;
    for (j = 0; j < num_cls; j++) 
      if (active_clause((cl=cls[j]))) {
#ifdef PRIVATE
	if (TRACE > 3 && trie2_cl_count(cl) < count_of_clause(cl)) {
	  print_clause_from_leaf(cl);
	  bug(1000);
	}
#endif
	count_of_clause(cl)++;
      }
  }
  Stack2_idx--;
  Value[i] = DC;
}

trie2_handle_known_values (save)
     /* search through Clause and collect all the unit clauses 
	into Trie2_Ucl. */
     int save;
{
  if (Tmp_idx > Tmp_idx_end) {
    fprintf ( stderr, "Tmp_idx (%d) > Tmp_idx_end (%d).\n", 
	      Tmp_idx, Tmp_idx_end);
    exit(1);
  }

  while (Tmp_idx--) {
    if (trie2_propagate(V2[Tmp[Tmp_idx]], Value[Tmp[Tmp_idx]], save) == UNSAT) 
      return UNSAT;
  }
  Tmp_idx = 0;

  return (trie2_handle_unit_clauses(0));
}

void trie2_freeze_clauses()
{
  int i, j, key, num_cls;
  struct var2 *el;
  struct trie **cls, *frozens, *cl;

  if (Tmp_idx_end < 0) {
    fprintf ( stderr, "Tmp is overflow (Tmp_idx_end = %d).\n", Tmp_idx_end);
    exit(1);
  }

  /* freeze clauses in which key appears as its value. */
  for (i = Tmp_idx_end; i < MAX_ATOM; i++) {
    el = V2[Tmp[i]];
    key = id_of(el);
    if (Value[key] == TT) {
      cls = el->pos;
      num_cls = el->pos_count;
    } else {
      cls = el->neg;
      num_cls = el->neg_count;
    }

    frozens = CLAUSE_MARK;
    for (j = 0; j < num_cls; j++) if (active_clause((cl=cls[j]))) {
      frozen_lin(cl) = frozens;
      frozens = cl;
    }
    frozen_cls(el) = frozens;
  }
  Tmp_idx_end = MAX_ATOM;
}

int trie2_handle_unit_clauses (save)
     int save;
     /* handle each unit clause one by one ... */
{
  int i, sign;
  struct trie *cl, *tr;

  /* At first, collect unit clauses from new clauses */
  if (Nonunit_cls != Newtrie) {
    cl = Newtrie; i = 0;
    while (cl != Nonunit_cls) {
      if (count_of_clause(cl) < 2) {
	i++;
	if (active_clause(cl)) {
	  /*print_clause_from_leaf(cl);*/
	  Trie2_Ucl[Trie2_Ucl_idx++] = cl;
	}
      }
      cl = cl->bro;
    }
    if (i == 0) Nonunit_cls = Newtrie;
  }

  if (Trie2_Ucl_idx >= MAX_LIST) {
    printf("Trie1_Ucl (%d) overflow!\n", MAX_LIST);
    exit(1);
  }

  while (Trie2_Ucl_idx > 0) {
    
    cl = Trie2_Ucl[--Trie2_Ucl_idx];
    /*printf("-");    print_clause_from_leaf(cl);*/
    
    if (active_clause(cl)) {
      if (count_of_clause(cl) == 0) {
	if (GROW) trie2_record_conflict(cl);
	return handle_fail_end();
      } else {

	/* at first locate the literal which has no value */
	tr = cl->par; 
	i = 0;
	sign = (HAS_POS_CL(tr))? 1 : 0;
	while (tr != NULL && i == 0) {
	  if (Value[key_of(tr)] == DC) i = key_of(tr);
	  else { sign = psign_of(tr); tr = tr->par; }
	}

	if (i) {
	  struct var2 *el = V2[i];

	  Value[i] = sign;
	  Stack2[Stack2_idx++] = i;

#ifdef MORETRACE
	  print_x_has_to;
#endif

	  if (GROW) {
	    mark_of(el) = cl;
	    level_of(el) = Branch_open;
	  }
	  if (trie2_propagate(el, Value[i], save) == UNSAT) {
	
#ifdef MORETRACE
	    print_up_to_x;
#endif
	
	    Stack2_idx--;
	    Value[i] = DC;
	    return UNSAT;
	  }
	}
      }
    }
  }

  trie2_freeze_clauses();

  return SAT;
}

void trie2_record_conflict (cl)
     struct trie *cl;
{
  int i, j, total, uip=0, uip2, newlevel;
  int sign_arr[MAX_ATOM], cl_arr[MAX_LENGTH];
  int flag = trie2_max_level(cl, 0);
  Old_cls = Newtrie;
  Conflict_cl_level = Branch_open;

  while (total = trie2_collect_parents(cl, cl_arr, &flag)) {

    /* remove level 0 variables */
    /* fix the sign of literals in the new clause */
    newlevel = 0;
    for (i = 0; i < total; i++) {
      j = cl_arr[i];
      if (level_of(V2[j]) == 0) {
	cl_arr[i--] = cl_arr[--total];
      } else {
	V2[j]->pure = 0;
	if (level_of(V2[j]) > newlevel) newlevel = level_of(V2[j]);
	sign_arr[j] = NEG(Value[j]);
      }
    }
    /* printf("newlevel = %d, C_levle=%d\n", newlevel, Conflict_cl_level);*/
    if (newlevel < Conflict_cl_level) Conflict_cl_level = newlevel;

    uip2 = cl_arr[total-1]; 
    /* printf("uip = %d\n", uip2);*/

    if (uip) { 
      cl_arr[total++] = uip; 
      sign_arr[uip] = Value[uip]; 
    } 

#ifdef MORETRACE
    if (TRACE == 2 || TRACE > 8) {
      printf("\nNC [%d]: (", 
	     Branch_open);
      for (i = 0; i < total; i++) {
	j = cl_arr[i];
	printf(" %s%d", ((sign_arr[j])? "" : "-"), j);
      }
      printf(")\n\n");
    }
#endif

    if (total <= GROW) {
      total = insert_sorter(cl_arr, total);

      /* integrating the new clause into the database */
      for (i = 0; i < total; i++) {
	j = cl_arr[i];
	if (sign_arr[j]) {
	  if (V2[j]->pos_extra <= 0) { 

#ifdef MORETRACE
	    if (TRACE > 2) 
	      printf("  x%d has %d occurrences.\n", j, V2[j]->pos_count);
#endif

	    if (trie2_add_extra_space(V2[j], TT) == 0) return; 
	  }
	} else {
	  if (V2[j]->neg_extra <= 0) { 

#ifdef MORETRACE
	    if (TRACE > 2) 
	      printf(" -x%d has %d occurrences.\n", j, V2[j]->neg_count);
#endif

	    if (trie2_add_extra_space(V2[j], FF) == 0) {
	      printf("WARNING: No space is available\n");
	      return; 
	    }
	  }
	}
      }

      if (total) {
#ifdef MORETRACE
	if (TRACE == 2 || TRACE >= 8) {
	  printf("\n[open: %d]: (", 
		 Branch_open);
	  for (i = 0; i < total; i++) {
	    j = cl_arr[i];
	    printf(" %s%d[%d]", ((sign_arr[j])? "" : "-"), 
		   j, level_of(V2[j]));
	  }
	  printf(")\n\n");
	}
#endif

	cl = trie_insert_clause2(Root, cl_arr, sign_arr, total-1);
	if (cl && cl != CLAUSE_MARK) {
	  trie2_integrate_clause(cl, uip);
	}
      } 
    }

    if (!flag || UIP<2) return;
    V2[uip]->pure = Branch_num; /* used as stamp in collect_parents */
    cl = NULL; 
    uip = uip2;
  }
}

trie2_add_extra_space (it, sign)
     struct var2 *it;
     int sign;
{
  int i, old_space;
  struct trie **old_arr, **new_arr;

  if (sign) {
    old_space = it->pos_count;
    old_arr = it->pos;
  } else {
    old_space = it->neg_count;
    old_arr = it->neg;
  }

  /* new_arr = get_trie2_array(old_space+EXTRA_SPACE);*/
  new_arr = (struct trie **) malloc 
    ( sizeof ( struct trie *) * (old_space+EXTRA_SPACE));
  if (new_arr == NULL) {
    printf("Warning: ran out space; no more new clauses\n");
    return (GROW = 0);
  }
  Memory_count += (EXTRA_SPACE) * sizeof ( struct trie *);

  for (i = 0; i < old_space; i++) new_arr[i] = old_arr[i];
  free(old_arr);

  if (sign) {
    it->pos_extra = EXTRA_SPACE;
    it->pos = new_arr;
  } else {
    it->neg_extra = EXTRA_SPACE;
    it->neg = new_arr;
  }
  return 1;
}

void trie2_integrate_clause (no, uip)
     struct trie *no;
{
  int psign, i;
  struct trie *cl;
  struct var2 *el;

  cl = get_trie();
  cl->par = no;
  if (uip) {
    count_of_clause(cl) = 1;
    /* printf("You need to mark this clause!"); */
  } else {
    count_of_clause(cl) = 0;
    Conflict_cl = cl;
  }

  cl->bro = Newtrie;
  Newtrie = cl;
  Clause_extra_num++;

  i = key_of(no);
  el = V2[i];
  if HAS_POS_CL(no) {
    el->pos_extra--;
    el->pos[el->pos_count++] = cl;
  } else {
    el->neg_extra--;
    el->neg[el->neg_count++] = cl;
  }
  
  psign = psign_of(no);
  no = no->par;
  while (no != NULL) {
    i = key_of(no);
    el = V2[i];
    if (psign) {
      el->pos_extra--;
      el->pos[el->pos_count++] = cl;
    } else {
      el->neg_extra--;
      el->neg[el->neg_count++] = cl;
    }
    psign = psign_of(no);
    no = no->par;
  }
}

trie2_collect_parents (cl, cl_arr, flag)
     struct trie *cl;
     int cl_arr[], *flag;
     /* flag passed the max_level and takes back if there is a uip */
{
  int key, i, j, var_num=0, total=0, cl_num=0, max_level=*flag;
  int stamp = Branch_num;
  struct trie *no;

  if (cl) {
    cl_num = 1;

#ifdef MORETRACE
    if (TRACE>1) { printf("conflict: "); print_clause_from_leaf(cl); }
#endif

    no = cl->par;
    while (no) {
      if (V2[key=key_of(no)]->level < max_level || mark_of(V2[key]) == NULL) {
	cl_arr[total++] = key;
      } else {
	var_num++;
#ifdef MORETRACE
	if (TRACE>3) printf("queue %d\n", key);
#endif
      }
      V2[key]->pure = stamp; 
      no = no->par;
    }
  } else var_num=1;

  for (j = Stack2_idx-1; j >= 0; j--) 
    if (V2[key=Stack2[j]]->pure == stamp && V2[key]->level == max_level) {
      if (cl=mark_of(V2[key])) {
#ifdef MORETRACE
	if (TRACE>3) printf("unqueue %d\n", key);
#endif
	--var_num;
	if (UIP && !var_num && cl_num>1) { 
	  cl_arr[total++] = key; 
	  return total; 
	}

#ifdef MORETRACE
	if (TRACE>3) print_clause_from_leaf(cl);
#endif
	no = cl->par;
	while (no) {
	  if (V2[i = key_of(no)]->pure != stamp) { 
	    if (V2[i]->level < max_level || mark_of(V2[i]) == NULL) {
	      cl_arr[total++] = i;
	      if (total >= MAX_LENGTH) {
		for (i = 0; i < total; i++) V2[cl_arr[i]]->pure = 0;
		return *flag=0;
	      }
	    } else {
	      var_num++;
	      if (TRACE>3) printf("queue %d\n", i);
	    }
	    V2[i]->pure = stamp; 
	  }
	  no = no->par;
	}
	cl_num++;
	if (!var_num && cl_num>1) { V2[key]->pure = 0; *flag = 0; return total; }
      } else {
	cl_arr[total++] = key;
      }
      V2[key]->pure = 0;
    }

#ifdef MORETRACE
  if (TRACE>1) {
    printf("failed %d\n", var_num); fflush(stdout); 
  }
#endif

  for (i = 0; i < total; i++) V2[cl_arr[i]]->pure = 0;
  return *flag=0;
}

int trie2_max_level (cl, key)
     struct trie *cl;
     int key;
{
  int max = 0;
  cl = cl->par;
  while (cl != NULL) {
    if (key_of(cl) != key &&
	level_of(V2[key_of(cl)]) > max)
      max = level_of(V2[key_of(cl)]);
    cl = cl->par;
 }
  return max;
}

void trie2_adjust_counts (cl)
     struct trie *cl;
{
  struct trie *tr;
  struct trie *son;
  int count = 0;

  tr = cl->par;

  if (Value[key_of(tr)] == DC) count++;

  son = tr; 
  tr = tr->par;
  while (tr != NULL) {
    if (Value[key_of(tr)] == DC) count++;
    son = tr;
    tr = tr->par;
  }

  count_of_clause(cl) = count;
#ifdef MORETRACE
  if (TRACE >= 9) {
    printf("Adjusted: ");
    print_clause_from_leaf(cl);
  }
#endif
}

int trie2_cl_count (cl)
     struct trie *cl;
{
  struct trie *tr;
  struct trie *son;
  int count;

  count = 0;

  tr = cl->par;
  if (Value[key_of(tr)] == DC) {
    count++;
  }
  if (HAS_POS_CL(tr) && Value[key_of(tr)] != FF) return 100;
  if (HAS_NEG_CL(tr) && Value[key_of(tr)] == FF) return 100;

  son = tr; 
  tr = tr->par;
  while (tr != NULL) {
    if (Value[key_of(tr)] == DC) {
      count++;
    } else if (psign_of(son) == 0 && Value[key_of(tr)] == FF) return 100;
    else if (psign_of(son) == 1 && Value[key_of(tr)] != FF) return 100;
    son = tr;
    tr = tr->par;
  }

  return count;
}

void trie2_empty (cl)
     struct trie *cl;
{
  while (cl != NULL) {
    if (trie2_is_empty(cl)) print_clause_from_leaf(cl);
    cl = cl->bro;
  }
}

int trie2_is_empty (tr)
     struct trie *tr;
{
  struct trie *son;

  tr = tr->par;
  if (HAS_POS_CL(tr) && Value[key_of(tr)] != FF) return 0;
  if (HAS_NEG_CL(tr) && Value[key_of(tr)] == FF) return 0;

  son = tr;
  tr = tr->par;
  while (tr != NULL) {
    if (psign_of(son) && Value[key_of(tr)] != FF) return 0;
    if (psign_of(son) == 0 && Value[key_of(tr)] == FF) return 0;
    son = tr; 
    tr = tr->par;
  }
  return 1;
}
