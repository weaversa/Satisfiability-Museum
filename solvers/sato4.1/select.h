/* Functions for literal-selection strategies */

min_weight_key (cl)
     TAPE cl;
{
  int i, j, best_key=0, best_w=MAX_INT;

  for (i = 3; i < size_of_clause(cl); i++) {
    j = lit_var(cl[i]);
    if (L5[cl[i]]->value == DC && weight(j) < best_w) {
      best_key = j; best_w = weight(j);
    }
  }
  if (best_key) return (best_key << 1)+FF;
  return 0;
}

first_key (cl)
     TAPE cl;
{
  int i;

  for (i = 3; i < size_of_clause(cl); i++) {
    if (L5[cl[i]]->value == DC) return cl[i];
  }
  return 0;
}


int *shortest_clause () 
{
  int *cl, *cl2, *best_cl=NULL;
  int i, j, l;
  int min = MAX_LIST;

  cl = Tape_space[0]; 
  cl2 = cl+Tape_limit[0]; 
  while (cl < cl2) {
    l = size_of_clause(cl);

    if (is_normal(cl) && 
	(L5[get_head(cl)]->value == TT || L5[get_tail(cl)]->value == TT))
      goto label;

    j = 0;
    for (i = 3; i < l; i++) {
      if (L5[cl[i]]->value == DC) {
	if (++j >= min) { goto label; }
      } else if (is_normal(cl) && L5[cl[i]]->value == TT) {
	goto label;
      }
    }

    if (j) {
      best_cl = cl;
      if ((min=j) <= 2) break; 
    }

  label: 
    cl += l;
  }
  /* if (best_cl) { printf("best cl "); print_clause(best_cl);  }*/
  return best_cl;
}

/*
int *shortest_clause () 
{
  int *cl, *cl2, *best_cl=NULL;
  int i, j, l;
  int min = MAX_LIST;

  cl = Tape_space[0]; 
  cl2 = cl+Tape_limit[0]; 
  while (cl < cl2) {
    if (is_normal(cl) && 
	(L5[get_head(cl)]->value == TT || L5[get_tail(cl)]->value == TT))
      goto label;

    j = 0;
    l = size_of_clause(cl);
    for (i = 3; i < l; i++) {
      if (L5[cl[i]]->value == DC) {
	if (++j >= min) { goto label; }
      } else if (is_normal(cl) && L5[cl[i]]->value == TT) {
	goto label;
      }
    }
    printf("best cl "); print_clause(cl); 
    best_cl = cl;
    if ((min=j) <= 2) break; 

  label: 
    cl += l;
  }
  return best_cl;
}
*/

int collect_best_keys (best_keys, max)
     int best_keys[], max;
{
  int i, k, x=0, num=0;

  if (max > 100) max = 100;

  for (i = VarOrderFirst; i < VarOrderSize; i++) {
    k = VarOrder[i];
    if (var_value(k) == DC) {
      if (!num) VarOrderFirst = i;
      best_keys[num++] = k;
      if (num >= max) break;
    }
  }

  if (!num) {
    for (i = 0; i < VarOrderSize; i++) {
      k = VarOrder[i];
      if (var_value(k) == DC) {
	if (!x) x = VarOrderFirst = i;
	best_keys[num++] = k;
	if (num >= max) break;
      }
    } 
  }
  return num;
}

int collect_best_keys_9 (best_keys, max)
     int best_keys[], max;
{
  int i, j, k, x=0, num=0;
  int *cl, *cl2;

  if (max > 100) max = 100;

  for (i = (Max_atom<<1)+1; i > 1; i--) lit_weight(i) = weight_value(i) = 0;
  
  /* scan the input clauses to compute weight_value */
  for (i = 0; i <= Input_tape; i++) {
    cl = Tape_space[i];
    cl2 = cl+Tape_limit[i];
    while (cl < cl2) {
      /* work only for 3-SAT */
      if (L5[cl[3]]->value == DC &&
	  L5[cl[4]]->value != TT &&
	  L5[cl[5]]->value == DC) {
	if (L5[cl[4]]->value == DC) {
	  weight_value(cl[3])++;
	  weight_value(cl[4])++;
	  weight_value(cl[5])++;
	} else {
	  weight_value(cl[3]) += 4;
	  weight_value(cl[5]) += 4;
	}
      }
      cl += size_of_clause(cl);
    }
  }

  /* scan the input clauses to compute lit_weight */
  for (i = 0; i <= Input_tape; i++) {
    cl = Tape_space[i];
    cl2 = cl+Tape_limit[i];
    while (cl < cl2) {
      /* work only for 3-SAT */
      if (L5[cl[3]]->value == DC &&
	  L5[cl[4]]->value == DC &&
	  L5[cl[5]]->value == DC) {
	lit_weight(cl[3]) += weight_value(cl[4]^1)*weight_value(cl[5]^1);
	lit_weight(cl[4]) += weight_value(cl[5]^1)*weight_value(cl[3]^1);
	lit_weight(cl[5]) += weight_value(cl[3]^1)*weight_value(cl[4]^1);
      }
      cl += size_of_clause(cl);
    }
  }

#ifdef TRYAGAIN
  for (i = (Max_atom<<1)+1; i > 1; i--) {
    weight_value(i) = (lit_weight(i))>>1;
    lit_weight(i) = 0;
  }

  /* scan the input clauses to compute lit_weight again */
  for (i = 0; i <= Input_tape; i++) {
    cl = Tape_space[i];
    cl2 = cl+Tape_limit[i];
    while (cl < cl2) {
      /* work only for 3-SAT */
      if (L5[cl[3]]->value == DC &&
	  L5[cl[4]]->value == DC &&
	  L5[cl[5]]->value == DC) {
	lit_weight(cl[3]) += weight_value(cl[4]^1)*weight_value(cl[5]^1);
	lit_weight(cl[4]) += weight_value(cl[5]^1)*weight_value(cl[3]^1);
	lit_weight(cl[5]) += weight_value(cl[3]^1)*weight_value(cl[4]^1);
      }
      cl += size_of_clause(cl);
    }
  }
#endif

  /* use lit_weight to select best keys */
  for (i = 1; i <= Max_atom; i++) if (var_value(i) == DC) 
    weight(i) = lit_weight((i<<1))*lit_weight((i<<1)+1);

  for (i = 1; i <= Max_atom; i++) if (var_value(i) == DC) {
    if (num < max) best_keys[num++] = i;
    else {
      j = x;
      while (1) {
	if (weight(i) > weight(best_keys[j])) {
	  best_keys[x=j] = i; break;
	} else {
	  if (++j == max) j = 0;
	  if (j == x) break;
	}
      }
    }
  }
  return num;
}

int var5_strategy1 ()
     /* the least unsigned variable */
{
  int i; 

  for (i = 1; i <= Max_atom; i++) if (var_value(i) == DC) {
    return (i << 1)+ CHOICE;
  }
  return 0;
}

int var5_strategy2 ()
     /* the heaviest unsigned variable in a shortest non-horn clause */
{
  static TAPE best_cl;
  static int prev_level;
  int i;

  if (!vstack_nonempty()) { prev_level = Level; }
  if ((prev_level < Level) && best_cl && (i = first_key(best_cl))) return i;
  best_cl = NULL;
  prev_level = Level;
  if (best_cl = shortest_clause()) {
    return first_key(best_cl);
  }
  return var5_strategy1();
}

int var5_strategy3 ()
     /* strategy2 plus weight */
{
  static TAPE best_cl;
  static int prev_level;
  int i;

  if (!vstack_nonempty()) { prev_level = Level; }
  if ((prev_level < Level) && best_cl && (i = min_weight_key(best_cl))) return i;
  best_cl = NULL;
  prev_level = Level;
  if (best_cl = shortest_clause()) return min_weight_key(best_cl); 
  return var5_strategy1();
}

int var5_strategy4 ()
     /* Use weight, look at Conflict_gcl first */
{
  int k, i, best = -1, best_s = FF, best_k = 0;

  if (Conflict_gcl && undeleted_clause(Conflict_gcl)) {
    for (k = 3; k < size_of_clause(Conflict_gcl); k++) 
      if (L5[Conflict_gcl[k]]->value == DC) {
	i = lit_var(Conflict_gcl[k]);
	if (weight(i) > best) {
	  best_k = i; best = weight(i); best_s = FF; 
	} 
      }
  } 

  if (best_k) return (best_k << 1)+best_s;

  return var5_strategy6();
}

int var5_strategy5 ()
     /* Use weight, look at Lemma_tape first */
{
  int *cl, *cl2;
  static int *cl0;

  cl = Tape_space[Lemma_tape];
  cl2 = cl+Tape_limit[Lemma_tape];

  if (cl == cl2) cl0 = NULL;
  else if (!(cl0 && undeleted_clause(cl0))) {
    cl0 = NULL;
    while (cl < cl2) {
      if (undeleted_clause(cl) &&
	  L5[get_head(cl)]->value == DC &&
	  L5[get_tail(cl)]->value == DC) {
	cl0 = cl;
	return get_head(cl);
      }
      cl += size_of_clause(cl);
    }
  }

  return var5_strategy6();
}

int var5_strategy6 ()
{
  int i,k;

  for (i = VarOrderFirst; i < VarOrderSize; i++) {
    k = VarOrder[i];
    if (var_value(k) == DC) {
      VarOrderFirst = i+1;
      return (weight_value(get_lit(k,0)) > weight_value(get_lit(k,1)))? 
	get_lit(k,0) : get_lit(k,1);
    } 
  }
  for (i = 0; i < VarOrderSize; i++) {
    k = VarOrder[i];
    if (var_value(k) == DC) {
      VarOrderFirst = i+1;
      return (weight_value(get_lit(k,0)) > weight_value(get_lit(k,1)))? 
	get_lit(k,0) : get_lit(k,1);
    } 
  } 
  return 0;
}

int var5_strategy7 ()
     /* a random heavy literal using weight */
{
  int i, num, best_keys[100];
  
  num = collect_best_keys(best_keys, Max_atom>>3);
  if (num) {
    i = best_keys[rand() % num];
    return (i << 1)+(rand() & 1);
  } 
  return 0;
}

unsigned long branch_fail;
int var5_strategy8 ()
     /* using lookahead */
{
  int i, k, num, best_keys[100];
  int best_weight=0, best_lit=0;
  branch_fail = Branch_fail;

  trace(3, printf("Begin lookahead\n"));
  if (SELECT == 8) {
    num = collect_best_keys(best_keys, Max_atom>>2);
    for (i = (Max_atom<<1)+1; i > 1; i--) lit_weight(i) = weight_value(i);
  } else 
    num = collect_best_keys_9(best_keys, Max_atom>>2);
  

  Conflict_cl_level = Level+1;
  while (num) {
    if (var_value(k=best_keys[--num]) == DC) {
      if (lookahead(k, num, best_keys, &best_lit, &best_weight, 1) == UNSAT) break;
    }
  }

  trace(3, printf("End lookahead\n"));
  Branch_fail = branch_fail;
  if (best_lit < 1 || L5[best_lit]->value == DC) return best_lit;
  return var5_strategy8();
}

lookahead (k, num, best_keys, best_lit, best_weight, depth)
     int k, num, best_keys[], *best_lit, *best_weight, depth;
{
  int i, j;
  int w0, w1;
  int stack_size = vstack_size();
  int ulit=0, units8[100];
  
  ++Branch_open;
  var_level(k) = Level;
  k = (k<<1);
  print_let_x_have(k);
  vstack_push1(k);
  assign_value2(k);
  if (handle_unit_clauses() == SAT) {
    w0 = (vstack_size()-stack_size)<<1;
    /* lookahead 2 steps
    if (depth && (LINE&1)) {
      int dummy, best_weight2;
      for (i = 0; i < num; i++) if (var_value(j=best_keys[i]) == DC) {
	best_weight2=0;
	if (lookahead(j, num, best_keys, &dummy, &best_weight2, 0) == UNSAT)
	  goto unsat;
	w0 += best_weight2;
      }
    }
    */
    if (++stamp >= MAX_SHORT) stamp = 1;
    for (j = stack_size; j < vstack_size(); j++) {
      i = vs_literal(vstack_of(j));
      lit_umark(i) = -stamp;
      w0 += lit_weight(i);
    }
    vstack_backup(Level);
    uqueue_init();
    k = k^1;
    ++Branch_open;
    print_now_let_x_have(k);
    vstack_push1(k);
    assign_value2(k);
    if (handle_unit_clauses() == SAT) {
      w1 = (vstack_size()-stack_size)<<1;
      /*
      if (depth && (LINE&1)) {
	int dummy, best_weight2=0;
	for (i = 0; i < num; i++) if (var_value(j=best_keys[i]) == DC) {
	  best_weight2=0;
	  if (lookahead(j, num, best_keys, &dummy, &best_weight2, 0) == UNSAT)
	    goto unsat;
	  w1 += best_weight2;
	}
      }
      */
      for (j = stack_size; j < vstack_size(); j++) {
	i = vs_literal(vstack_of(j));
	w1 += lit_weight(i);
	if (lit_umark(i) == -stamp) {
	  if (ulit < 100) units8[ulit++] = i;
	}
      }
      vstack_backup(Level);
      uqueue_init();

      while (ulit) {
	j = units8[--ulit];
	var_level((j>>1)) = Level;
	print_x_has_to(j);
	vstack_push0(j);
	assign_value2(j);
      }
      if (uqueue_nonempty()) {
	if (handle_unit_clauses() == UNSAT) {
	  *best_lit = -1;
	  branch_fail++;
	  return UNSAT;
	}
      }

      j = w1*w0;
      if (j > *best_weight) {
	*best_weight = j;
	*best_lit = (w1 > w0)? k : k^1;
	trace(8, printf("  weight_of(%d) = %d, %d, %d\n", (k>>1), j, w0, w1));
      }
    } else { /* UNSAT */
      goto unsat;
    }
  } else { /* UNSAT */
    goto unsat;
  }

  return SAT;

 unsat:
  if (Conflict_cl_level < Level) {
    *best_lit = -1;
    branch_fail++;
    return UNSAT;
  }

  vstack_backup(Level);
  uqueue_init();
  k = k^1;
  var_level((k>>1)) = Level;
  print_x_has_to(k);
  vstack_push0(k);
  assign_value2(k);
  if (handle_unit_clauses() == UNSAT) {
    *best_lit = -1;
    branch_fail++;
    return UNSAT;
  }
  return SAT;
}

int unit_num=0;
#define unassigned_lit10(i) (lit_stamp(i) != stamp && lit_stamp(i^1) != stamp) 
#define assigned_false10(i) (lit_stamp(i^1) == stamp) 

int var5_strategy10 ()
     /* using decision procedure for 2SAT */
{
  int i, k; 
  int best_weight=0, best_lit=0;

  if (++stamp >= MAX_SHORT) stamp = 1;  
  trace(3, printf("Begin 2-SAT\n"));
  for (k = 1; k <= Max_atom; k++) {
    i = (k<<1)+CHOICE;
    if (lit_value(i) == DC && unassigned_lit10(i)) {
      unit_num = 1;
      lit_stamp(i) = stamp;
      trace(6, printf("  2-SAT:  %s%d be 1\n", 
		      (lit_sign(i))? "-" : "", lit_var(i)));
      if (binary_propagate(i^1) == UNSAT) {
	trace(3, printf("End 2-SAT\n"));
	return -1;
      }
      if (lit_value(i) == DC && unit_num > best_weight) {
	best_weight = unit_num;
	best_lit = i^1;
      }
    }
  }
  trace(3, printf("End 2-SAT\n"));
  if (best_lit < 1 || L5[best_lit]->value == DC) return best_lit;
  return var5_strategy10();
}

int binary_propagate (ks0)
     int ks0;
{
  int **pts;
  int *p, *cl;
  int i, j, ks, num;

  pts = L5[ks0]->hts;
  p = L5[ks0]->bicls;

  /* propagate binary clauses first */
  for (j = bicls_count(p)-1; j >= bicls_begin(); j--) {
    if (lit_value(ks0) != DC) return SAT;
    if (lit_value(ks=p[j]) == DC) { 
      if (unassigned_lit10(ks)) {
	/* a unit clause is found */
	trace(6, printf("  2-SAT:  %s%d from (%s%d %s%d)\n", 
			(lit_sign(ks))? "-" : "", lit_var(ks), 
			(lit_sign(ks))? "-" : "", lit_var(ks), 
			(lit_sign(ks0))? "-" : "", lit_var(ks0)));
	lit_stamp(ks) = stamp;
	if (binary_propagate(ks^1) == UNSAT) return UNSAT;
      } else if (assigned_false10(ks)) {
	/* a conflict and ks has to be true */
	if (++stamp >= MAX_SHORT) stamp = 1;  
	uqueue_init();
	var_level(ks>>1) = Level;
	trace(6, printf("  2-SAT:  %s%d be 1 by (%s%d %s%d)\n", 
			(lit_sign(ks))? "-" : "", lit_var(ks), 
			(lit_sign(ks))? "-" : "", lit_var(ks), 
			(lit_sign(ks0))? "-" : "", lit_var(ks0)));
	ks = ks^1;
	vstack_push0(ks);
	assign_value2(ks);
	if (handle_unit_clauses() == UNSAT) return UNSAT;
      }
    }
  }

  /* propagate 3-SAT clauses */
  j = hts_begin();
  num = hts_count(pts);
  while (j < num) {
    if (lit_value(ks0) != DC) return SAT;
    p = pts[j];
    if (is_head(p)) { /* p is a real head */
      cl = p-1;
      ks = cl[cl[2]];
    } else { /* p is actually tail */
      cl = p-2;
      ks = cl[cl[1]];
    }

    if (size_of_clause(cl) == 6 && lit_value(cl[4]) == FF && lit_value(ks) == DC) { 
      if (unassigned_lit10(ks)) {
	/* a unit clause is found */
	trace(6, { printf("  2-SAT:  %s%d from ", 
			  (lit_sign(ks))? "-" : "", lit_var(ks));
	             print_clause(cl);});
	lit_stamp(ks) = stamp;
	if (binary_propagate(ks^1) == UNSAT) return UNSAT;
      } else if (assigned_false10(ks)) {
	/* a conflict and ks has to be true */
	/* this is buggy: a depth-first search procedure is needed */
	if (++stamp >= MAX_SHORT) stamp = 1;  
	uqueue_init();
	var_level(ks>>1) = Level;
	trace(6, { printf("  2-SAT:  %s%d be 1 by ", 
			  (lit_sign(ks))? "-" : "", lit_var(ks));
	             print_clause(cl);});
	ks = ks^1;
	vstack_push0(ks);
	assign_value2(ks);
	if (handle_unit_clauses() == UNSAT) return UNSAT;
      }
    }
    j++;
  }
  return SAT;
}

int var5_strategy11 ()
     /* the first unassigned clause and make it true */
{

  int *cl, *cl2, *best_cl=NULL;
  int i, j, l;

  cl = Tape_space[0]; 
  cl2 = cl+Tape_limit[0]; 
  while (cl < cl2) {
    if (is_normal(cl) &&
	L5[get_head(cl)]->value != TT && 
	L5[get_tail(cl)]->value != TT) {
      if (L5[get_head(cl)]->value == DC) 
	return NEG(get_head(cl));
      else
	return NEG(get_tail(cl));
    } 
    cl += size_of_clause(cl);
  }

  return var5_strategy1();
}


int var5_strategy20 ()
     /* an experimental one */
{
  int i, j, num;
  int *cl, *cl2;

  /* reset weight_value */
  /* scan the binary clauses to compute weight_value */
  for (i = 1; i <= Max_atom; i++) if (var_value(i) == DC) {
    num = 0;
    cl2 = L5[i<<1]->bicls;
    for (j = bicls_count(cl2)-1; j >= bicls_begin(); j--) 
      if (L5[cl2[j]]->value == DC) num++;
    weight_value((i<<1)+1) = (num<<2);
    num = 0;
    cl2 = L5[(i<<1)+1]->bicls;
    for (j = bicls_count(cl2)-1; j >= bicls_begin(); j--) 
      if (L5[cl2[j]]->value == DC) num++;
    weight_value(i<<1) = (num<<2);
  }
  
  /* scan the input clauses to compute weight_value */
  for (i = 0; i <= Input_tape; i++) {
    cl = Tape_space[i];
    cl2 = cl+Tape_limit[i];
    while (cl < cl2) {
      /* work only for 2-SAT + 3-SAT */
      if (L5[cl[3]]->value == DC &&
	  L5[cl[4]]->value != TT &&
	  L5[cl[5]]->value == DC) {
	if (L5[cl[4]]->value == DC) {
	  weight_value(cl[3])++;
	  weight_value(cl[4])++;
	  weight_value(cl[5])++;
	} else {
	  weight_value(cl[3]) += 4;
	  weight_value(cl[5]) += 4;
	}
      }
      cl += size_of_clause(cl);
    }
  }

#ifndef QUASICLAUSE
  /* check for pure literals: works only for 3-SAT */
  for (i = 1; i <= Max_atom; i++) if (var_value(i) == DC) {
    int x1 = (i<<1)+1;
    int x0 = (i<<1);
    if (!MINVAR && !weight_value(x1)) { 
      print_x_pure(x1);
      assign_value0(x1);
      vstack_push0(x1);
      var_level(i) = Level;
      Pure_num++;
    } else if (!weight_value(x0)) {
      print_x_pure(x0);
      assign_value0(x0);
      vstack_push0(x0);
      var_level(i) = Level;
      Pure_num++; 
    }
  }
#endif

  /* now compute the second weight */
  j = num = 0;
  for (i = 1; i <= Max_atom; i++) if (var_value(i) == DC) {
    int w0 = second_weight((i<<1));
    int w1 = second_weight((i<<1)+1);
    int x;
    x = ((w0*w1)<<10)+w0+w1+1;
    if (x > num) { 
      num = x; 
      if (w0 > w1) j = (i<<1)+1; else j = (i<<1); 
    }
  }

  trace(5, printf("pick %d: %d=%d, w=%d\n", j, lit_var(j), lit_sign(j), num));
  if (j) return j;
  return var5_strategy1();
}

second_weight (ks)
     int ks;
{
  int **pts = L5[ks]->hts;
  int *bcs = L5[ks]->bicls;
  int i, j, num, total = 0;
  int *p, *cl;

  /* consider binary clauses first */
  for (j = bicls_count(bcs)-1; j >= bicls_begin(); j--) {
    if (L5[ks = bcs[j]]->value == DC) total += weight_value(NEG(ks));
  }

  num = hts_count(pts);
  for (j = hts_begin(); j < num; j++) {
    p = pts[j];
    if (is_head(p)) { /* p is a real head */
      cl = p-1;
      i = cl[4];
      ks = cl[5];
    } else { /* p is actually tail */
      cl = p-2;
      ks = cl[2];
      i = cl[4];
    }
    if (size_of_clause(cl) == 6 && L5[ks]->value == DC) {
      if (L5[i]->value == FF) 
	total += (weight_value(NEG(ks)));
      else if (L5[i]->value == DC) 
	total += (weight_value(NEG(ks))+weight_value(NEG(i)))>>1;
    }
  }
  
  return total;
}

#define var5_best_key(i)\
  if ((Branch_num & 128) == 0) i=var5_strategy1(); \
  else \
  switch (SELECT) {\
  case 2: i=var5_strategy2(); break;\
  case 3: i=var5_strategy3(); break;\
  case 4: i=var5_strategy4(); break;\
  case 5: i=var5_strategy5(); break;\
  case 6: i=var5_strategy6(); break;\
  case 7: i=var5_strategy7(); break;\
  case 8: i=var5_strategy8(); break;\
  case 9: i=var5_strategy8(); break;\
  case 10: i=var5_strategy10(); break;\
  case 11: i=var5_strategy11(); break;\
  default: i=var5_strategy1(); \
  }

void record_keeping ()
{
  int h, t, b, p;

  b = (100*Bicl_num)/Clause_num;
  t = (100*Trcl_num)/Clause_num;
  h = (1000*NH_num)/Clause_num;
  p = (1000*POS_num)/Clause_num;

  /* adjust splitting strategies */
  if (SELECT == 0) {
    if (QCLAUSE && b < 50) 
      SELECT = 2;
    else {
      SELECT = 4; CHOICE = CHOICE^1;
    }

    /* if NH < 5% select 2. */    
    if (p && (h < 50 || p < 20)) {
      SELECT = 2; CHOICE = CHOICE^1;
    } else if (t > 95 && Max_atom*4 <= Clause_num && Clause_num*2 <= Max_atom*9) { 
      SELECT = 9; 
    } else if (b > 75) { 
      SELECT = 6; 
    } else if (b > 5 && b < 10 && t+b > 95) {
      SELECT = 6; 
    }
  }

  trace(1, {
    printf("c Bin = %ld, %d ", Bicl_num, b);
    printf("NH = %d, %2.1f ", NH_num, h/10.0);
    printf("Pos = %d, %2.1f ", POS_num, p/10.0);
    printf("Tri = %ld, %d S = %d data\n", Trcl_num, t, SELECT);
  });
}

