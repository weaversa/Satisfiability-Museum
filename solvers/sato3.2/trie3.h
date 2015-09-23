/********************************************************
  Code for a different search algorithm: DATA = 3
********************************************************/

void init_var3_table ()
{
  static int old_Max_atom;
  int i;
  struct var3 *el;

  if (V3 != NULL) {
    for (i=1; i <= old_Max_atom; i++)  {
      el = V3[i];
      free(el->poss);
      free(el->negs);
      free(el->both);
      free(el->pnegs);
      free(el->pposs);
    }
    free(V3);
  }

  old_Max_atom = Max_atom;
  i = sizeof ( struct var3 *) * (1+Max_atom );
  V3 = (struct var3 **) malloc ( i );
  Memory_count += i;

  if (V3 == NULL) {
    fprintf ( stderr, "var_table returns NULL.\n");
    exit(1);
  }

  for (i=0; i <= Max_atom; i++)  {
    V3[i] = el = (struct var3 *) tp_alloc ( sizeof ( struct var3 ) );
    el->poss = (struct cap *) tp_alloc( sizeof ( struct cap ));
    el->negs = (struct cap *) tp_alloc( sizeof ( struct cap ));
    el->both = (struct cap *) tp_alloc( sizeof ( struct cap ));
    el->pnegs = (struct cap *) tp_alloc( sizeof ( struct cap ));
    el->pposs = (struct cap *) tp_alloc( sizeof ( struct cap ));
    el->both->tr = el->poss->tr = el->negs->tr = 
      el->pposs->tr = el->pnegs->tr = CLAUSE_MARK;

    el->push = el->pull = NULL;
    set_id(el, i);
    /* el->units = NULL; */
    el->next = NULL;
  }

  if (SELECT == 7) {
    Weight = (long *) malloc((Max_atom+1) * (sizeof(long)));
    Memory_count += ( sizeof(long *) * (Max_atom+1));
    for (i=0; i <= Max_atom; i++) Weight[i] = 0;
  }
}

long visit_trie (no, par, pflag, len, pos)
     struct trie *no, *par;
     int pflag, len, pos;
{
  struct trie *tr;

  if (Stop) {
    return 0;
  } else if (no == CLAUSE_MARK) {
    if (trie_pull_par_up_init(par, pflag, len) == UNSAT) {
      /* free_trie(Root);*/
      Root = CLAUSE_MARK; 
      return 0; 
    }

    if (pos > 1) {
      tr = get_trie();
      tr->par = par;
      set_key_psign(tr, 0, pflag);
      tr->bro = NHtrie;
      NHtrie = tr;
      NH_num++;
    }
    return 1;
  } else {
    long z = 0;
    len++;
    tr = no;
    while (tr != NULL) {
      if (tr->link == NULL) {
	tr->link = (struct links *) tp_alloc(sizeof(struct links));
	tr->link->lin = tr->link->back = NULL;
	tr->link->stamp = NULL;
      }
      tr->par = par;
      set_psign(tr, pflag);
      set_esign(tr,DC);
      if (tr->pos != NULL)
	z += visit_trie(tr->pos, tr, 1, len, pos+1);
      if (tr->neg != NULL) 
	z += visit_trie(tr->neg, tr, 0, len, pos);
      tr = tr->bro;
    }
    if (SELECT == 7) { 
      Weight[key_of(no)] += z;
    }
    return z;
  } 
}

int trie3_search2 ()
{
  int i;

  /* there is a BUG appearing in trie_push_brothers
     when the file BUG is input 
     */

  Max_cand = (RENAME>1)? RENAME : Max_atom+1;
  Tmp_idx = 0;
  i = (trie_push_brothers(Root) != UNSAT);

  /* the major loop goes here. */
  while (i && !Stop) {
    if (trie_propagate_values() != UNSAT)
      i = trie_next_key();
    else {
      i = trie_prev_key();
    }
  } /* while */

  return ((Branch_succ)? 1 : (Stop)? 2 : 0);
}

int trie_next_key ()
{
  int i;

  if (OLDV) {
    int flag = TT;

    while (OLDV && flag) {
      i = Old_value[--OLDV];
      if (i < 0) { i = -i; flag = FF; }

      if (Value[i] != DC) flag = TT;
      else {
	Top_var3 = V3[i];
	assign_value(i, flag); 

	if (Old_choice[OLDV] == TT) {
	  Backup[Backup_idx++] = i;
	  Branch_open++;
	  Branch_num++;
	} else {
	  Backup[Backup_idx++] = -i;
	}

#ifdef MORETRACE
	print_let_x_have;
	/*if (QGROUP && TRACE >= 2) print_cell(i);*/
#endif

	return i;
      }
    }
  }

  if (GREEDY <= Branch_open) {
    if (greedy_search()) {
      printf("Found a model by the Greedy Search.\n");
      return handle_succ_end(); 
    }
    return trie_prev_key();
  }

  if ((i = trie_best_key()) == 0) return handle_succ_end();

  Branch_open++;
  Branch_num++;
  
  Top_var3 = V3[i];
  if (SELECT == 9) {
    /* random value */
    int sign = rand() % 2;
    assign_value(i, sign);
  } else if (SELECT != 6) {
    assign_value(i, CHOICE1); 
  }

#ifdef MORETRACE
  print_let_x_have;
  /*if (QGROUP && TRACE >= 2) print_cell(i);*/
#endif

  if (Backup_idx >= MAX_LIST) {
    fprintf ( stderr, "MAX_LIST(%d) is too small in next_key(%d).\n", 
	      MAX_LIST, i);
    Stop = 1;
  }
  Backup[Backup_idx++] = i;

  return i;
}

int trie_best_key ()
{
  static int first = -1;
  if (first == -1 && JUMP > 1 && JUMP < 1000) { first = JUMP; }
  if (first > 0) { first--;  return strategy0();}

  if (SELECT == 0) { 
    return trie_strategy1();
  } else if (SELECT == 10) {
    return strategy0();
  } else if (SELECT == 1) {
    return trie_strategy1();
  } else if (SELECT == 2) { 
    return trie_strategy1();
  } else if (SELECT == 12) { 
    return trie_strategy20();
  } else if (SELECT == 20) { 
    return trie_strategy20();
  } else if (SELECT == 3) {
    return trie_strategy3();
  } else if (SELECT == 4) {
    return trie_strategy4();
  } else if (SELECT == 5) {
    return trie_strategy5();
  } else if (SELECT == 6) {
    return trie_strategy6();
  } else if (SELECT == 7) {
    return trie_strategy7();
  } else if (SELECT < 10) {
    return trie_strategy1();
  } else {
    fprintf ( stderr, "Unknown option(1): -s%d\n", SELECT);
    return (Stop = 1);
  }
}


int trie_strategy1 ()
     /* the least unsigned variable in a shortest 
	non-horn clause */
{
  int key, i;
  int min_key = 0;
  int min = MAX_ATOM;
  struct trie *cl = NHtrie;
  struct trie *son, *no, *min_clause;

  while (cl != NULL) {
    i = 0;
    key = 0;
    son = cl;
    no = son->par;
    while (no != NULL) {
      if (Value[key_of(no)] == DC) {
	if (++i >= min) goto end; 
	if (key_of(no) < Max_cand) {
	  key = key_of(no);
	}
      } else if (Value[key_of(no)] == psign_of(son)) 
	goto end;

      son = no; 
      no = son->par;
    }	

    if (key) {
      if (i <= 2) { 
#ifdef MORETRACE
	if (TRACE == 4) print_clause_from_leaf(cl);
#endif
	return key;
      }
      min = i;
      min_key = key;
      min_clause = cl;
    }

  end:
    cl = cl->bro;
  }

#ifdef MORETRACE
  if (min_key && TRACE == 4) print_clause_from_leaf(min_clause);
#endif

  if (min_key || RENAME==0) return min_key;
  else return strategy0();
}

int trie_strategy20 ()
     /* a random key in shortest non-horn clauses */
{
  int key[30], i, min_key[1000];
  int min_key_idx = 0;
  int min = MAX_ATOM;
  struct trie *cl = NHtrie;
  struct trie *son, *no;

  while (cl != NULL) {
    i = 0;
    son = cl;
    no = son->par;
    while (no != NULL) {
      if (Value[key_of(no)] == DC) {
	if (i+1 > min) goto end; 
	if (key_of(no) < Max_cand) {
	  key[i++] = key_of(no);
	}
      } else if (Value[key_of(no)] == psign_of(son)) 
	goto end;

      son = no; 
      no = son->par;
    }	

    if (i < min) {
      min_key_idx = min = i;
      for (i=0; i<min; i++) min_key[i] = key[i];
    } else if (i == min) 
      for (i=0; i<min; i++) min_key[min_key_idx++] = key[i];

  end:
    cl = cl->bro;
  }

  if (min_key_idx)
    return min_key[good_random() % min_key_idx];
  else return strategy0();
}

int trie_strategy3 ()
     /* the most frequent variable in shortest non-horn clauses */
{
  int key, i, j;
  int tmp_keys[200], best_keys[200], best_occurs[200];
  int best_num = 0;
  int min = MAX_ATOM-1;
  struct trie *son, *no;
  struct trie *cl = NHtrie;

  while (cl != NULL) {
    son = cl;
    no = son->par;
    i = key = 0;
    while (i < min && no != NULL) {
      if (Value[key_of(no)] == DC) {
	tmp_keys[i++] = key = key_of(no);
	son = no; 
	no = son->par;
      } else if (Value[key_of(no)] == psign_of(son)) {
	i = MAX_ATOM;
      } else {
	son = no; 
	no = son->par;
      }
    }	

    if (min > i) {
      best_num = min = i;
      for (i = 0; i < min; i++) {
	best_keys[i] = tmp_keys[i];
	best_occurs[i] = 1;
      }
    } else if (min == i) {
      for (i = 0; i < min; i++) {
	key = tmp_keys[i];
	for (j = 0; j < best_num; j++) 
	  if (best_keys[j] == key) { best_occurs[j]++; j = MAX_ATOM; }
	if (j < MAX_ATOM) {
	  best_keys[best_num] = key;
	  best_occurs[best_num++] = 1;
	}
      }
    }
    cl = cl->bro;
  }

  if (!best_num) return 0;

  j = 0;
  for (i = 1; i < best_num; i++) {
    if ((best_occurs[i] > best_occurs[j])) {
      j = i;
    }
  }

  return best_keys[j];
}

int trie_strategy4 ()
     /* the most frequent variable in shortest non-horn clauses */
{
  int key, i, j;
  int tmp_keys[200], best_keys[MAX_ATOM], best_occurs[200];
  int best_num = 0;
  int min = MAX_ATOM-1;
  struct trie *son, *no;
  struct trie *cl = NHtrie;

  while (cl != NULL) {
    son = cl;
    no = son->par;
    i = 0;
    while (i < min && no != NULL) {
      if (Value[key_of(no)] == DC) {
	tmp_keys[i++] = key = key_of(no);
	son = no; 
	no = son->par;
      } else if (Value[key_of(no)] == psign_of(son)) {
	i = MAX_ATOM;
      } else {
	son = no; 
	no = son->par;
      }
    }	

    if (min > i) {
      best_num = min = i;
      for (i = 0; i < min; i++) {
	key = best_keys[i] = tmp_keys[i];
      }
    } else if (min == i) {
      for (i = 0; i < min; i++) {
	key = tmp_keys[i];
	for (j = 0; j < best_num && (best_keys[j] != key); j++);
	if (j >= min) {
	  best_keys[best_num++] = key;
	}
      }
    }
    cl = cl->bro;
  }

  if (!best_num) return 0;

  for (i = 0; i < best_num; i++) {
    struct var3 *el = V3[best_keys[i]];
    best_occurs[i] = 
      trie_list_len(el->both->tr) +
      trie_list_len(el->pnegs->tr) +
      trie_list_len(el->pposs->tr) +
      trie_list_len(el->negs->tr) +
      trie_list_len(el->poss->tr);
  }
  j = 0;
  for (i = 1; i < best_num; i++) {
    if ((best_occurs[i] > best_occurs[j])) {
/*      printf("length = %d, key = %d, best occ = %d\n",
	     min, best_keys[j], best_occurs[j]);
*/
      j = i;
    }
  }

/*  printf("LENGTH = %d, key = %d, best occ = %d\n",
	 min, best_keys[j], best_occurs[j]);
*/
  return best_keys[j];
}

int trie_strategy5 ()
     /* the most frequent variable in shortest non-horn clauses */
{
  int key, i, j;
  int tmp[500], best_keys[500];
  int best_num = 0;
  int min = MAX_ATOM-1;
  struct trie *son, *no;
  struct trie *cl = NHtrie;

  while (cl != NULL) {
    i = 0;
    son = cl;
    no = son->par;
    while (no != NULL) {
      if (Value[key_of(no)] == DC) {
	if (++i > min) goto end; 
	tmp[i] = key = key_of(no);
      } else if (Value[key_of(no)] == psign_of(son)) 
	goto end;

      son = no; 
      no = son->par;
    }	

    if (min > i) {
      best_num = min = i;
      for (i = 0; i < min; i++) {
	best_keys[i] = tmp[i+1];
      }
    } else { /* (min == i) */
      for (i = 1; i <= min; i++) {
	key = tmp[i];
	for (j = 0; j < best_num; j++) 
	  if (best_keys[j] == key) goto exist;
	best_keys[best_num++] = key;
      exist: ;
      }
    }

  end:
    cl = cl->bro;
  }

  if (!best_num) return 0;
  return best_keys[good_random() % best_num];
}

int trie_strategy6 ()
     /* same as trie_strategy2 except the new clauses are considered. */
{
  static int best_clause[10], signs[10], best_num;
  int i, key, best_i = 0;
  int min = MAX_ATOM;
  struct trie *cl = NHtrie;
  struct trie *son, *no, *min_clause = NULL;

  if (Backup_idx) {
    for (i = best_num-1; i >= 0; i--) {
      key = best_clause[i]; 
      if (Value[key] == DC) { best_num--; best_i = i; }
      else if (Value[key] == signs[i]) { i = -1; best_i = 0; }
    }
    if (best_i) {
      assign_value(best_clause[best_i], NEG(signs[best_i]));
      return best_clause[best_i];
    }
  }

  while (cl != NULL) {
    i = 0;
    son = cl;
    no = son->par;
    while (no != NULL) {
      if (Value[key_of(no)] == DC) {
	if (++i >= min) goto end; 
      } else if (Value[key_of(no)] == psign_of(son)) 
	goto end;

      son = no; 
      no = son->par;
    }	

    if (key) {
      min_clause = cl;
      if (i <= 2) cl = CLAUSE_MARK;
      min = i;
    }

  end:
    cl = cl->bro;
  }

#ifdef MORETRACE
  if (min_clause && TRACE == 4) print_clause_from_leaf(min_clause);
#endif

  if (min_clause) {
    best_num = 0;
    son = min_clause;
    no = son->par;
    while (no != NULL) {
      if (Value[key_of(no)] == DC) {
	if (best_num < 10 && key_of(no) < Max_cand) {
	  best_clause[best_num] = key_of(no);
	  signs[best_num++] = psign_of(son);
	} 
      }
      son = no; 
      no = son->par;
    }	

    best_num--;
    assign_value(best_clause[best_num], NEG(signs[best_num]));
    return best_clause[best_num];
    
  } else return strategy0();
}

int trie_strategy7 ()
     /* the least unsigned variable in a shortest clause;
      except the first literal, the rest literals are positive. */
{
  int i, best_i = 0;
  long best = 0;

  for (i = 1; i < Max_cand; i++) 
    if (Value[i] == DC && Weight[i] > best)
      { best_i = i; best = Weight[i]; }
  return best_i;
}

int trie_prev_key ()
{
  int i, j;
  int jump=1;
  if (JUMP < 1000) jump=JUMP; 

  OLDV = Tmp_idx = 0;
  j = Branch_fail & two15;

  while (Backup_idx-- > 0) {
    if ((i = Backup[Backup_idx]) < 0) {
      trie_clean_dependents(V3[-i]);
      --jump;
    } else {
      int sign = Value[i];
      trie_clean_dependents(V3[i]);
      Branch_open--;

      if (j || --jump < 1) {
	Backup[Backup_idx++] *= -1;
	Top_var3 = V3[i];
	assign_value(i, NEG(sign));

#ifdef MORETRACE
	print_now_let_x_have;
#endif
	return i;
      } else
	Branch_skip++;
    }
  }

  if (SELECT == 20) {
    Clause_extra_num++;
    return trie_next_key();
  }

  if (GREEDY < MAX_ATOM) printf("\nThe greedy search for models has failed.\n");
  if (JUMP > 1 && JUMP < 1000) 
    printf("\nThe jumpy search for models has failed.\n");

  return Stop = 0;
}

int trie_strategy9 ()
     /* the least unsigned variable in a shortest clause;
      except the first literal, the rest literals are positive. */
{
  struct trie *no;
  int i, first_i, best_i, best;
  unsigned int k;
  best = Max_atom;
  first_i = best_i = 0;

  for (i = 1; i < Max_cand; i++) 
    if (Value[i] == DC) {
      if (first_i == 0) first_i = i;
      no = V3[i]->both->tr;
      while (no != CLAUSE_MARK) {
	if ((k = trie_short_clause_all(no, best)) < best) 
	  if (k == 1) {
	    return i;
	  } else {
	    best = k;
	    best_i = i;
	  }
	no = no->link->lin;
      }
      no = V3[i]->poss->tr;
      while (no != NULL) {
	if ((k = trie_short_clause_all(no, best)) < best) 
	  if (k == 1) {
	    return i;
	  } else {
	    best = k;
	    best_i = i;
	  }
	no = no->link->lin;
      }
    }
  return (best_i == 0)? first_i : best_i;
}

#ifdef RESEARCH
int trie_look_ahead (total, p_arr, sign_arr)
     int total, p_arr[], sign_arr[];
     /* return UNSAT if it results in inconsistency
	when P[i] is assigned SIGN[i] */
{
  struct var3 *old_top_var;
  int res, i, p, p_sign;

  for (i = 0; i < total; i++) if (Value[p = p_arr[i]] == DC) {
    old_top_var = Top_var3;
    Top_var3 = V3[p];

    assign_value(p, p_sign = sign_arr[i]);

#ifdef MORETRACE
    if (TRACE > 3) printf("     Looking ahead on %s%d\n", 
			  (p_sign == TT)? "x" : "-x", p);
#endif

    res = trie_propagate_values();
    if (res == UNSAT) {
      Tmp_idx = 0;
      trie_clean_dependents(V3[p]);
      Top_var3 = old_top_var;

      trie_assign_value(p, NEG(p_sign));

#ifdef MORETRACE
      if (TRACE > 3) printf("        %s%d is set to false by lookahead\n", 
			    (p_sign == TT)? "x" : "-x", p);
#endif

      if (trie_propagate_values() == UNSAT) {
	return UNSAT;
      }
    } else {
      int j;
      res = 0;
      for (j = 1; j <= Max_atom; j++) if (Value[j] != DC) res++;
      sign_arr[i] = res;

      trie_clean_dependents(V3[p]);
      Top_var3 = old_top_var;
    }
  }
  return SAT;
}
#endif

int trie_propagate_values ()
{
  struct var3 *el;
  int i;

  while (Tmp_idx > 0) {
    el = V3[i = Tmp[--Tmp_idx]];
    if (Value[i] == TT) {
      if (trie_push_list_neg(el->both->tr) == UNSAT) return UNSAT;
      if (trie_push_list_neg(el->negs->tr) == UNSAT) return UNSAT;
      if (trie_pull_list(el->pnegs->tr) == UNSAT) return UNSAT;
    } else if (Value[i] == FF) {
      if (trie_push_list_pos(el->both->tr) == UNSAT) return UNSAT;
      if (trie_push_list_pos(el->poss->tr) == UNSAT) return UNSAT;
      if (trie_pull_list(el->pposs->tr) == UNSAT) return UNSAT;
    } else {
      printf("value[x%d] = %d\n", i, Value[i]);
    }
  }
  return SAT;
}

int trie_pull_list (topno)
     struct trie *topno;
{
  struct trie *no;
  int i, sign;

  while (topno != CLAUSE_MARK) {
    no = topno->par;
    sign = psign_of(topno);

    while (1) {
      while (Value[key_of(no)] != DC) {
	if (Value[key_of(no)] == sign) { goto end; } 
	else {
	  sign = psign_of(no);
	  if ((no = no->par) == NULL) {
	    if (SELECT == 7) Weight[key_of(no)] += WPLUS;
	    return handle_fail_end();
	  }
	}
      }

      if (esign_of(no) == DC) {
	if (end_mark(no) != NULL) {
	  i = key_of(no);
	  trie_assign_value(i, sign);
#ifdef MORETRACE
	  print_x_has_to;
#endif

	} else {
	  struct cap *cp;
	  set_esign(no, sign);
	  cp = (sign)? V3[key_of(no)]->pposs : V3[key_of(no)]->pnegs;
	  end_mark(no) = cp->tr;
	  cp->tr = no;
	  if (Backup_idx) {
	    no->link->stamp = cp;
	    no->link->back = Top_var3->pull;
	    Top_var3->pull = no;
	  }
	}
	goto end;
      } else if (esign_of(no) == sign) {
	goto end;
      } else {
	sign = psign_of(no);
	if ((no = no->par) == NULL) {
	  if (SELECT == 7) Weight[key_of(no)] += WPLUS;
	  return handle_fail_end();
	}
      }
    }
  end: 
    topno = topno->link->lin;
  }    
  return SAT;
}

int trie_pull_par_up_init (no, sign, len)
     struct trie *no;
     int sign, len;
{
  while (1) {
    while (Value[key_of(no)] != DC) {
      if (Value[key_of(no)] == sign) return SAT;
      sign = psign_of(no);
      if ((no = no->par) == NULL) {
	if (SELECT == 7) Weight[key_of(no)] += WPLUS;
	return handle_fail_end();
      }
    }
   
    if (esign_of(no) == DC) {
      struct cap *cp;

      if (len == 1) {
	fprintf(stderr, "%d unit %d ", key_of(no), sign);
      } else if (len == 2) {
	Bicl_num++;
      } 
      set_esign(no,sign);
      cp = (sign)? V3[key_of(no)]->pposs : V3[key_of(no)]->pnegs;
      end_mark(no) = cp->tr;
      cp->tr = no;
      return SAT;
    } else if (esign_of(no) == sign) {
      return SAT;
    } else {
      sign = psign_of(no);
      if ((no = no->par) == NULL) {
	if (SELECT == 7) Weight[key_of(no)] += WPLUS;
	return handle_fail_end();
      }
    }
  }
}

int trie_pull_par_up (no, sign)
     struct trie *no;
     int sign;
{
  int i;

  while (1) {
    while (Value[key_of(no)] != DC) {
      if (Value[key_of(no)] == sign) return SAT;
      sign = psign_of(no);
      if ((no = no->par) == NULL) {
	if (SELECT == 7) Weight[key_of(no)] += WPLUS;
	return handle_fail_end();
      }
    }
   
    if (esign_of(no) == DC) {
      if (end_mark(no) != NULL) {
	i = key_of(no);
	trie_assign_value(i, sign);
#ifdef MORETRACE
	print_x_has_to;
#endif

      } else {
	struct cap *cp;
	set_esign(no, sign);
	cp = (sign)? V3[key_of(no)]->pposs : V3[key_of(no)]->pnegs;
	end_mark(no) = cp->tr;
	cp->tr = no;
	if (Backup_idx) {
	  no->link->stamp = cp;
	  no->link->back = Top_var3->pull;
	  Top_var3->pull = no;
	}
      }
      return SAT;
    } else if (esign_of(no) == sign) {
      return SAT;
    } else {
      sign = psign_of(no);
      if ((no = no->par) == NULL) {
	if (SELECT == 7) Weight[key_of(no)] += WPLUS;
	return handle_fail_end();
      }
    }
  }
}

int trie_push_list_pos (top_cl)
     struct trie *top_cl;
{
  while (top_cl != CLAUSE_MARK) {
#ifdef MORETRACE
    if (trie_push_brothers(top_cl->pos) == UNSAT) return UNSAT;
#else
    struct trie *tr = top_cl->pos;
    TRIE_PUSH_BROTHERS 
#endif
    top_cl = top_cl->link->lin;
  }    
  return SAT;
}

int trie_push_list_neg (top_cl)
     struct trie *top_cl;
{
  while (top_cl != CLAUSE_MARK) {
#ifdef MORETRACE
    if (trie_push_brothers(top_cl->neg) == UNSAT) return UNSAT;
#else
    struct trie *tr = top_cl->neg;
    TRIE_PUSH_BROTHERS
#endif
    top_cl = top_cl->link->lin;
  }    
  return SAT;
}

int trie_push_brothers (tr)
     struct trie *tr;
{
  struct trie *bros[MAX_SHORT];
  struct trie *no;
  int i;
  int idx;
  struct var3 *it;


  idx = 1;
  bros[0] = tr;
  while (idx > 0) {
    tr = bros[--idx];
    while (tr != NULL) {
      no = tr;
      i = key_of(no);
      it = V3[i];

      if (esign_of(no) == TT) {

	if (Value[i] == DC) {
	  trie_assign_value(i, TT);
#ifdef MORETRACE
	  print_x_has_to;
#endif
	} else if (Value[i] == FF) {
#ifdef MORETRACE
	  print_x_contradictory;
#endif
	  if (SELECT == 7) Weight[i] += WPLUS;
	  return handle_fail_end();
	}

	if (tr->bro != NULL) bros[idx++] = tr->bro;
	tr = no->neg;

      } else if (esign_of(no) == FF) {

	if (Value[i] == DC) {
	  trie_assign_value(i, FF);
#ifdef MORETRACE
	  print_x_has_to;
#endif
	} else if (Value[i] == TT) {
#ifdef MORETRACE
	  print_x_contradictory;
#endif
	  if (SELECT == 7) Weight[i] += WPLUS;
	  return handle_fail_end();
	}

	if (tr->bro != NULL) bros[idx++] = tr->bro;
	tr = no->pos;

      } else { /* esign_of(no) == DC */

	if (Value[i] == TT) {
	  if (tr->bro != NULL) bros[idx++] = tr->bro;
	  tr = no->neg;
	} else if (Value[i] == FF) {
	  if (tr->bro != NULL) bros[idx++] = tr->bro;
	  tr = no->pos;
	} else {  /* Value[i] == DC */ 
	  struct cap *cp;
	  if (no->neg == NULL) {
	    if (no->pos != NULL) {
	      cp = it->poss;
	      end_mark(no) = cp->tr;
	      cp->tr = no;
	      if (Backup_idx) {
		no->link->stamp = cp;
		no->link->back = Top_var3->push;
		Top_var3->push = no;
	      }
	    }
	  } else if (no->pos == NULL) {
	    cp = it->negs;
	    end_mark(no) = cp->tr;
	    cp->tr = no;
	    if (Backup_idx) {
	      no->link->stamp = cp;
	      no->link->back = Top_var3->push;
	      Top_var3->push = no;
	    }
	  } else {
	    cp = it->both;
	    end_mark(no) = cp->tr;
	    cp->tr = no;
	    if (Backup_idx) {
	      no->link->stamp = cp;
	      no->link->back = Top_var3->push;
	      Top_var3->push = no;
	    }
	  }
	  tr = tr->bro;
	}
      }
    }
  }
  return SAT;
}

void trie_clean_dependents (top)
     struct var3 *top;
{
  int i;
  struct trie *no;
  struct var3 *it, *next;

  it = top;

  /*
  if (top->units) {
    struct unit *u, *v;
    u = top->units;
    top->units = NULL;
    while (u != NULL) {
      v = u->next;
      free_unit(u);
      u = v;
    }
    } */

  while (it != NULL) {
    i = id_of(it);
#ifdef MORETRACE
    print_up_to_x;
#endif
    Value[i] = DC;
    next = it->next;
    it->next = NULL;
    it = next;
  }

  no = top->pull;
  top->pull = NULL;
  while (no != NULL) {
    /* pop off stack */
    no->link->stamp->tr = no->link->lin;
    end_mark(no) = NULL;
    set_esign(no,DC);
    no = no->link->back;
  }

  no = top->push;
  top->push = NULL;
  while (no != NULL) {
    /* pop off stack */
    no->link->stamp->tr = no->link->lin;
    end_mark(no) = NULL;
    no = no->link->back;
  }
}

int trie_short_clause_all (no0, min)
     /* count the length of the shortest clauses in no0, top-down,
	positive side only. */
     struct trie *no0;
     int min;
{
  struct trie *no;
  int key = key_of(no0);

  if (min == 1) return 1;
  if (Value[key] == DC) {

    no = no0->pos;
    if (no != NULL) {
      if (esign_of(no) == TT) return 1;
      if (esign_of(no) == FF) return min;
      while (no != NULL && no->pos != NULL) {
	min = trie_short_clause_all(no, min);
	if (min == 1) return 2;
	no = no->bro;
      }
    }
    return ++min;

  } else {

    if (Value[key] == FF) 
      no = no0->pos;
    else no = no0->neg;

    if (no != NULL) {
      if (esign_of(no) == TT) return 1;
      if (esign_of(no) == FF) return min;
      while (no != NULL && no->pos != NULL) {
	min = trie_short_clause_all(no, min);
	if (min == 1) return 1;
	no = no->bro;
      }
    }
    return min;
  }
}
