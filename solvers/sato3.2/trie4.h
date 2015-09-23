/********************************************************
  Code for a different search algorithm: DATA = 4
********************************************************/

/* Local Micros */

#define save_assign_value(i, val)  Value[i] = val;

#define print_gclause(gcl) print_clause_from_leaf(gcl->body);
  
/* functions */

struct gclause **get_gclause_array (size)
     int size;
{
  struct gclause **p;

  p = (struct gclause **) malloc(sizeof(struct gclause *)*size);
  if (p == NULL) { fprintf(stderr, "get_gclause_array return NULL.\n"); exit(1); }
  Memory_count += sizeof(struct gclause *)*size;
  return p;
}

struct glink *get_glink ()
{
  struct glink *p = (struct glink *) tp_alloc(sizeof(struct glink));
  if (p == NULL) {
    fprintf(stderr, "get_glink return NULL.\n");
    exit(1);
  }
  p->next = p->prev = NULL;
  return(p);
} 

struct gclause *get_gclause ()
{
  struct gclause *p = NULL;
  struct glink *g;

  if (slot_full()) {
    if (INSEARCH) {
      slot_cleanup(); 
    } else {
      double_slots();
    }
    if (slot_full()) return NULL;
  }
  
  if ((p = slot_next()) == NULL) {
    p = (struct gclause *) tp_alloc(sizeof(struct gclause));
    if (p == NULL) {
      fprintf(stderr, "Out of memory: get_gclause return NULL.\n");
      exit(1);
    }
    g = p->head_glink = get_glink();
    g->cl = p;
    g = p->tail_glink = get_glink();
    g->cl = p;
  }
  slot_add(p);
  return(p);
} 

void init_var4_table ()
{
  static int old_Max_atom;
  int i, s;
  struct var4 *el;

  old_Max_atom = Max_atom;
  Glink_avail = NULL;
  slot_init();
  weight_init();
  Gclause_New = get_gclause_array(MAX_STACK);

  if (V4 != NULL) {
    for (i=1; i <= old_Max_atom; i++) { free(V4[i]); }
    free(V4);
  }

  i = sizeof ( struct var4 *) * (1+Max_atom );
  Memory_count += i;
  V4 = (struct var4 **) malloc ( i );
  if (V4 == NULL) {
    fprintf ( stderr, "init_var4_table returns NULL.\n");
    exit(1);
  }

  for (i=0; i <= Max_atom; i++)  {
    V4[i] = el = (struct var4 *) tp_alloc ( sizeof ( struct var4 ) );

    /* basic stuff */
    for (s = 0; s < 2; s++) {
      struct glink *gl = el->cls[s] = get_glink();
      gl->next = gl->prev = gl;
    }

    /* GROW techniques */
    el->mark = NULL;
    el->level = 0;
    el->dfs = 0; 
    V4[i] = el;
  }
}

long visit_trie4 (tr, par, pflag, count, pcount)
     struct trie *tr, *par;
     int count, pcount;
     /* Visit the whole trie.
	When go down, (a) assign the parent; (b) count the numbers
	of literals and positive literals; (d) if a CLAUSE_MARK is found, 
	create a clause node.
	When go up, return the number of clauses in the trie.
	*/
{
  struct gclause *gcl;

  if (tr == CLAUSE_MARK) {

    if (count == 1) { return 0; }
    else if (count == 2) Bicl_num++;

    gcl = get_gclause();
    if (pcount > 1) slot_nh_swap();

    tr = get_trie();
    tr->par = par;
    set_key_psign(tr, count, pflag);

    gcl->body = tr;
    trie_head(tr) = tr;
    var4_insert_glink_end(gcl, tr, gcl->head_glink); 
    trie_tail(tr) = par;
    var4_insert_glink_end(gcl, par, gcl->tail_glink);
    return 1;

  } else {

    long x = 0;
    int y;
    count++;

    while (tr != NULL) {
      int key = key_of(tr);
      tr->par = par;
      set_psign(tr, pflag);

      if (tr->pos != NULL) {
	y = visit_trie4(tr->pos, tr, 1, count, 1+pcount);
	weight_add(key,1,y);
	x += y;
      }

      if (tr->neg != NULL) {
	y = visit_trie4(tr->neg, tr, 0, count, pcount);
	weight_add(key,0,y);
	x += y;
      }
      tr = tr->bro;
    }
    return (x);
  }
}

var4_insert_glink (cl, end, new)
  struct gclause *cl;
  struct trie *end;
  struct glink *new;
{
  struct glink *gl;
  int k = key_of(end->par);
  int s = psign_of(end);
  gl = V4[k]->cls[s];
  if (new->next) { delete_glink(new); }
  new->next = gl->next;
  new->prev = gl;
  gl->next->prev = new;
  gl->next = new;
}

var4_insert_glink_end (cl, end, new)
  struct gclause *cl;
  struct trie *end;
  struct glink *new;
{
  struct glink *gl;
  int k = key_of(end->par);
  int s = psign_of(end);
  gl = V4[k]->cls[s];
  if (new->next) { delete_glink(new); }
  new->prev = gl->prev;
  new->next = gl;
  gl->prev->next = new;
  gl->prev = new;
}

init_trie4_search (first)
     int first;
{ 
  int i;
  for (i = 1; i <= Max_atom; i++) {
    struct var4 *el = V4[i];
    
    if (Value[i] != DC) {
      trace(6, printf("%s%d 0\n", (Value[i] == TT)? "" : "-", i));
      uqueue_add((i<<1)+Value[i]);
    } else if (first) {
      if (!weight_val1(i)) {
	uqueue_add((i<<1));
	Value[i] = FF;
#ifdef MORETRACE
	print_x_pure;
#endif
	Pure_num++;
      } else if (!weight_val0(i)) {
	uqueue_add((i<<1)+1);
	Value[i] = TT;
#ifdef MORETRACE
	print_x_pure;
#endif
	Pure_num++; 
      } else {
	if (SELECT & 1) {
	  weight_set(i,0,weight_val0(i)+weight_val1(i));
	  weight_set(i,1,0);
	} else {
	  weight_set(i,0,weight_val0(i));
	  weight_set(i,1,weight_val1(i));
	}
      }
    }
  }
}

int trie4_search (first)
     int first;
{
  int i;    

  if (TRACE >= 0) 
    printf("c There are %d clauses (%d binary, %d non-Horn).\n", 
	   slot_size(), Bicl_num, NH_num);

  Clause_num = New_unit = 0;
  uqueue_init();
  vstack_init();
  slot_set_kept(slot_size());
  init_trie4_search(first);
  if (handle_unit_clauses() == UNSAT) return 0;

  var4_next_key();
  /* the major loop goes here. */
  while (!Stop && uqueue_nonempty()) {
    if (handle_unit_clauses() == UNSAT) {
      var4_prev_key();
    } else {	
      var4_next_key();
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
	s = (i<<1)+flag;
	if (Old_choice[OLDV] == TT) {
	  vstack_push1(s);
	  Branch_num++;
	  Branch_open++; 
	} else {
	  vstack_push2(s);
	}
	Value[i] = flag;
	V4[i]->level = Level;

#ifdef MORETRACE
	print_let_x_have;
#endif
	return s;
      }
    }
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
    s = var4_best_key();

  if (!s) return var4_succ_end();
  
  vstack_push1(s);
  ++Branch_open;
  ++Branch_num;
  Conflict_cl_level = Level;
  i = s >> 1;
  Value[i] = s & 1;
  V4[i]->level = Level;
  check(V4[i]->mark, printf("V4[%d]->mark != NULL", i));

#ifdef MORETRACE
  print_let_x_have;
#endif
}

int var4_prev_key ()
{
  int i, s;
  uqueue_init();

  trace(3, printf("a There are %d branches (%d open, %ld failed, %d jumped, l=%d).\n", 
		  Branch_num, Branch_open, Branch_fail, Branch_jump, Conflict_cl_level));

  if (!Branch_open) return 0;

  if (JUMP && Conflict_cl_level < Level) {
    trace(3, printf("    Backjumping from level %d to %d\n", Level, Conflict_cl_level));
    i = vstack_backup(Conflict_cl_level);
  } else
    i = vstack_backup(Level);
  Branch_jump--;

  if (collect_units_from_new_gcl() == UNSAT) {
    uqueue_init();
    trace(3, printf("c There are %d branches (%d open, %ld failed, %d jumped)\n", 
		  Branch_num, Branch_open, Branch_fail, Branch_jump)); 
    return var4_fail_end(NULL);
  }

  if (Backjumping_down) {
    Backjumping_down = 0;
  } else if (i && Value[i>>1] == DC) {
    check((V4[i>>1]->level != Level+1), 
	  { printf("why changed level of %d: %d %d\n", 
		 i>>1, V4[i>>1]->level, Level); bug(); exit(0);});
    i = i^1;
    uqueue_add(i); 
    /* Hope that gclauses imply i later */
  }

  trace(3, printf("b There are %d branches (%d open, %ld failed, %d jumped)\n", 
		  Branch_num, Level, Branch_fail, Branch_jump)); 

}

int var4_best_key()
{
  int i;

  if (SELECT & 1) { weight_update7(); }
  else { weight_update6(); }

  /* switch (SELECT) */
  /* 
  else if (SELECT == 6) return var4_strategy6();
  else if (SELECT == 5) return var4_strategy5();
  else if (SELECT == 7) return var4_strategy7();
  else if (SELECT == 8) return var4_strategy8();
  else if (SELECT == 2) return var4_strategy2();
  else if (SELECT == 1) return var4_strategy1();
  else if (SELECT == 3) return var4_strategy3();
  else if (SELECT == 9) return var4_strategy9(); 
  */
  if (SELECT == 4) return var4_strategy4();
  else if (SELECT == 2) return var4_strategy2();
  else if (SELECT == 10) return var4_strategy0(); 
  return var4_strategy4();
}

int var4_strategy0 ()
     /* the least unsigned variable */
{
  int i; 
  
  for (i = 1; (i <= Max_atom); i++) if (Value[i] == DC) 
    return (i << 1)+ CHOICE1;
  return 0;
}

int var4_strategy2 ()
     /* the heaviest unsigned variable in non-horn clause */
{
  int best_key=0, i, j, h;
  int min = MAX_LIST;
  static struct trie *best_gy2;
  static int prev_level;
  struct trie *cl;

  if (!vstack_nonempty()) { prev_level = Level; }

  if ((prev_level < Level) && (cl=best_gy2)) {
    if (Value[head_key(cl)] == DC && Value[tail_key(cl)] == DC) {
      best_key = head_key(cl);
      return (best_key << 1)+CHOICE1;
    }
  } else best_gy2 = NULL;

  for (h = 0; h < NH_num; h++) {
    cl = slot_of(h)->body;
    j = 0;
    if (Value[head_key(cl)] == DC && Value[tail_key(cl)] == DC) {
      struct trie *no = cl->par;
      while (no) {
	if (Value[key_of(no)] == DC) {	if (++j >= min) goto label; }
	no = no->par;
      }
      best_key = head_key(cl);
      /* printf("best %d in ", best_key); print_gclause(cl); */
      best_gy2 = cl;
      prev_level = Level;
      if ((min=j) <= 2) return (best_key << 1)+CHOICE1;
    }
  label: ;
  }

  if (best_key) {
    /* printf("pick %d in ", best_key); print_gclause(best_gy2); */
    return (best_key << 1)+CHOICE1;
  }
  return var4_strategy0();
}

int var4_strategy4 ()
     /* the same as var4_strategy6, but look at Conflict_gcl first */
{
  struct trie *cl;
  int k, i, best_i = 0, best = -10, best_v = 0;

  if (cl=Conflict_cl) {
    best_v = psign_of(cl);
    cl = cl->par;
    while (cl) {
      if (Value[i=key_of(cl)] == DC) {
	if (weight0(i) > best) {
	  best_i = i; best = weight0(i); best_v = FF; 
	} else if (weight1(i) > best) { 
	  best_i = i; best = weight1(i); best_v = TT; 
	} 
      }
      best_v = psign_of(cl);
      cl = cl->par;
    }
  } 
  
  if (!best_i)
    for (i = 1; i <= Max_atom; i++) if (Value[i] == DC) {
      if (weight0(i) > best) {
	best_i = i; best = weight0(i); best_v = FF; 
      } else if (weight1(i) > best) { 
	best_i = i; best = weight1(i); best_v = TT; 
      } 
    } 

  if (best_i) return (best_i << 1)+best_v;

  return 0;
}

int adjust_conflict_level (cl, down)
     struct trie *cl;
     int *down;
{
  int l, i, c=0, hl=0, highest=0, second_high=0, u;
  
  cl = cl->par;
  while (cl) {
    l = V4[i=key_of(cl)]->level;
    if (l > highest) { 
      second_high = highest; 
      u = hl;
      highest = l; 
      hl = i;
      c = 1; 
    } else if (l == highest) c++;
    else if (l > second_high) { second_high = l; u = i; }
    cl = cl->par;
  }

  if (c > 1 || ++second_high == highest) { *down = 0; return highest; }

  /* if only one variable is the highest */
#ifdef MORETRACE
  if (TRACE > 8 || TRACE == 5) {
    printf("New level %d, %d, %d\n", second_high, highest, Level);
  }
#endif

  *down = 1;
  return (second_high);
}


int handle_unit_clauses ()
     /* handle each unit clause one by one ... */
{
  int i, s;

  /* now handle gclauses */
  while (uqueue_nonempty()) {
    uqueue_pop(s);
    i = s>>1;
    if (Value[i] == DC) {
      /* this is the case of the second choice of a selected lit */
      V4[i]->level = Level;
      check(V4[i]->mark, printf("V4[%d]->mark != NULL\n"));
      Value[i] = s&1;
      vstack_push2(s);


#ifdef MORETRACE
      print_now_let_x_have;
#endif

    } else if (Value[i] != (s&1)) return var4_fail_end(NULL);
    else if (var4_propagate(i, (s&1)) == UNSAT) return UNSAT;
  }

#ifdef APPLICATION
  if (QAP) return qap_check_low_bound();
  else if (STAGE == 4 && (RESTRICT&1)) return mlb_check_low_bound(); 
#endif

  return SAT;
}

int var4_succ_end ()
{
  if (var4_check_model()) return var4_prev_key();
  Branch_succ++;

#ifdef MORETRACE
  if (TRACE == 2) printf("S%d\n", Branch_succ);
#endif

#ifdef APPLICATION
  if (GROUP) print_oarray_model();
  else if (QAP) qap_record_soln(); 
  else if (TEAM) print_team_model();
  else 
#endif
    print_model(stdout);

  return ((MODEL && Branch_succ >= MODEL)? 0 : var4_prev_key());
}

int var4_fail_end (cl)
     struct trie *cl;
{
  Branch_fail++;

  if (GROW && cl && Branch_open>1) {
    var4_record_conflict(cl);
  }

  if (Stop = check_stop(1)) {
    if (TRACE >= 0) {
      printf("\nThe search is aborted with search tree path:\n");
      print_guide_path(stdout);
      printf("\n");
    }
  }
  return UNSAT;
}

vstack_print () 
{
  int i; 
  printf("value stack: ");
  for (i = 0; i < vstack_size(); i++) {
    int info = vstack_of(i);
    int k = vs_var(info);
    if (vs_selected(info)) printf("\n");
    printf("var %d, val %d=%d, lvl %d ", k, 
	   vs_value(info), Value[k], V4[k]->level);
    if (V4[k]->mark) print_clause_from_leaf(V4[k]->mark); else printf("\n");
  }
}

int vstack_backup (level)
     /* back up to level level; return the last item of level level */
     int level; 
{
  int vv=0, i, k, info;

  for (k = vstack_size()-1; k >= 0; k--) {
    info = vstack_of(k);
    if (V4[i = vs_var(info)]->level < level) {
      vstack_resize(k+1);
      return vv;
    }
#ifdef MORETRACE
    print_up_to_x;
#endif

    if (vs_selected(info)) { Branch_jump++;  Branch_open--; }
    vv = vs_var_and_value(info);
    V4[i]->mark = NULL;
    V4[i]->dfs = 0;
    Value[i] = DC;
#ifdef APPLICATION
    if (QAP && (vv & 1)) qappair_pop(vv>>1);
#endif
  }
  vstack_resize(0);
  return vv;
}

var4_assign (i, sign)
     int i, sign;
{
  V4[i]->level = Level;
  vstack_push0((i<<1)+sign);
  Value[i] = sign;
#ifdef MORETRACE
  print_x_has_to;
#endif
}

collect_units_from_new_gcl()
{
  int i, j, s;

  /* check the newly generated unit clause */
  if (New_unit) {
    i = New_unit >> 1;
    s = New_unit & 1;
    New_unit = 0;

    if (Value[i] == DC) { 
      V4[i]->level = 0;
      Value[i] = s;

#ifdef MORETRACE
      if (TRACE>8) printf("unit");
      print_x_has_to;
#endif
      uqueue_add((i<<1)+s);
    } else if (Value[i] != s) {
      if (TRACE > 1) printf("F1 ");
      return var4_fail_end(NULL);
    }
  }

  /* check newly generated clauses for unit or empty clauses */
  for (j = Gclause_New_idx-1; j >= 0; j--) {
    int l, lj, v, k, saved=0;
    struct gclause *gcl = Gclause_New[j];
    struct trie *body, *no, *high, *head = NULL;

    i=-1, l = 0;
    no = body = gcl->body; 
    while (no->par) {
      v = Value[k=key_of(no->par)];
      s = psign_of(no);
      if ((s && v != FF) || (!s && v != TT)) {
	if (head) { 
	  trie_head(body) = head; 
	  var4_insert_glink(gcl, head, gcl->head_glink);
	  trie_tail(body) = no; 
	  var4_insert_glink(gcl, no, gcl->tail_glink);
	  saved = 1; 
	  break;
	} else { head = no; }
      } else if (v != DC && V4[k]->level > l) {
	l = V4[k]->level; high = no;
      }
      no = no->par;
    }

    if (!saved) { /* clause is either empty or unit or true */
      if (!head) {
	trace(2, { printf("F2 at %d ", Branch_open); print_gclause(gcl); });
	return var4_fail_end(NULL);
      } else if (Value[k=key_of(head->par)] == DC) { 
	int ks, s = psign_of(head);
	V4[k]->mark = gcl->body;
	V4[k]->level = l;
	Value[k] = s;
	ks = (k << 1)+s;
	vstack_push2(ks);

	if (head == body) {
	  trie_head(body) = head; 
	  var4_insert_glink(gcl, head, gcl->head_glink);
	  trie_tail(body) = high; 
	  var4_insert_glink(gcl, high, gcl->tail_glink);
	} else {
	  trie_head(body) = high; 
	  var4_insert_glink(gcl, high, gcl->head_glink);
	  trie_tail(body) = head; 
	  var4_insert_glink(gcl, head, gcl->tail_glink);
	}

#ifdef MORETRACE
	i = k;
	if (TRACE > 2) {
	  printf("  Forced x%d(%d,%d) at %d: (", i, s, l, Level);
	  print_gclause(gcl);
	}
	print_x_has_to;
#endif
	saved = 1;
      }
    }
    
    if (saved) { /* now delete this gcl from the pool */
      trace(3, { printf("Moved at %d ", Branch_open); print_gclause(gcl); });
      if (j < --Gclause_New_idx) 
	Gclause_New[j] = Gclause_New[Gclause_New_idx];
    } else {
      trace(3, { printf("Kept at %d ", Branch_open); print_gclause(gcl); });
    }
  }
}

var4_check_model ()
{
  int i, s, good;

#ifndef APPLICATION
  printf("c Checking model ...\n");
#endif

  for (i = 0; i < slot_size(); i++) {
    struct trie *cl = slot_of(i)->body;
    good = 0; 
    s = psign_of(cl);
    cl = cl->par;
    while (cl && !good) {
      if (s && Value[key_of(cl)] == TT) good = 1;
      else if (!s && Value[key_of(cl)] == FF) good = 1;
      else { s = psign_of(cl); cl = cl->par; }
    }
    if (!good) return 1;
  }
  return 0;
}

int var4_propagate (key, sign)
     int key, sign;
{
  struct var4 *el = V4[key];
  struct gclause *gcl;
  struct trie *cl;
  struct glink *gl0, *gl;
  struct nlink *nl;
  int r;
  /* print_var4_gclause(key, sign+1); */

  gl0 = el->cls[sign^1];
  gl = gl0->next;
  while (gl != gl0) {
    gcl = gl->cl; 
    cl = gcl->body;
    gl = gl->next;

    if (head_key(cl) == key) {
      r = check_gcl_head(gcl);
    } else if (tail_key(cl) == key) {
      r = check_gcl_tail(gcl);
    } else {
      /* check(1, { printf("Why here %d: ", key); print_gclause(cl);}); 
	 clauses in Gclause_New may appear here */
      r = 0;
    }

    if (r == UNSAT) {
      trace1(4, { printf("EMPTY: "); print_clause_from_leaf(cl);});
      return var4_fail_end(cl); 
    }
  }

  /* print_var4_gclause(key, sign+1); */
  return 0;
}

int check_cl_key (cl, i, sign)
     struct trie *cl;
     int i, sign;
{
  if (Value[i] == DC) {
    int ks = (i<<1)+sign;
    trace(8, {
      printf("unit cl %s%d at %d from ", (sign)? "" : "-", i, Level);
      print_clause_from_leaf(cl);
    });
    V4[i]->mark = cl;
    V4[i]->level = Level;
    vstack_push0(ks);
    Value[i] = sign;
#ifdef MORETRACE
    print_x_has_to;
#endif
    return 0;
  } else if (Value[i] != sign) {
    trace1(4, { printf("EmpTy: "); print_clause_from_leaf(cl);});
    return UNSAT;
  } else 
    return 0;
}

int locate_head_tail (gcl)
     struct gclause *gcl;
{
  int v, s;
  struct glink *gl;
  struct trie *cl=gcl->body, *xi, *xj=NULL;

  xi = cl;
  while (xi->par) {
    if ((v=Value[key_of(xi->par)]) == DC) {
      if (!xj) { xj = xi; }
      else { 
	trie_head(cl) = xj; 
	var4_insert_glink(gcl, xj, gcl->head_glink);
	trie_tail(cl) = xi; 
	var4_insert_glink(gcl, xi, gcl->tail_glink);
	return 0; 
      }
    } else if (v) { if (psign_of(xi)) return 0; }
    else { if (!psign_of(xi)) return 0; }
    xi = xi->par;
  }

  if (xj) return check_cl_key(cl, key_of(xj->par), psign_of(xj));

#ifdef MORETRACE
  if (TRACE == 4 || TRACE > 8) {
    printf("EMpty: "); print_gclause(gcl);
  }
#endif
  return UNSAT;
}

int check_gcl_head (gcl)
     struct gclause *gcl;
{
  struct trie *cl = gcl->body;

  if (key_of(cl) == 2) {
    return check_cl_key(cl, key_of(cl->par->par), psign_of(cl->par));
  } else {
    int l, v;
    struct trie *xi, *focus, *other; 
    focus = trie_head(cl); 
    other = trie_tail(cl);

    if ((v=Value[key_of(other->par)]) != DC) { 
      if (v) {
	if (psign_of(other)) return 0;
      } else if (!psign_of(other)) return 0;
      return locate_head_tail(gcl);
    }
    l = V4[key_of(focus->par)]->level;
    xi = focus->par;

    /* printf("size=%d, focus=%d, other=%d i=%d\n", cl->osize, focus, other, i);*/
    while (xi != focus) {
      if (xi->par == NULL) { xi = cl; continue; }
      if (xi == other) { xi = xi->par; continue; }
      if ((v=Value[key_of(xi->par)]) == DC) { 
	trie_head(cl) = xi; 
	var4_insert_glink(gcl, xi, gcl->head_glink);
	return 0; 
      }
      if ((v == TT && psign_of(xi)) || 
	  (v == FF && !psign_of(xi))) {
	if (V4[key_of(xi->par)]->level < l) {
	  trie_head(cl) = xi; 
	  var4_insert_glink(gcl, xi, gcl->head_glink);
	}
	return 0;
      }
      xi = xi->par;
    }
    return check_cl_key(cl, key_of(other->par), psign_of(other));
  }
}

int check_gcl_tail (gcl)
     struct gclause *gcl;
{
  struct trie *cl = gcl->body;

  if (key_of(cl) == 2) {
    return check_cl_key(cl, key_of(cl->par), psign_of(cl));
  } else {
    int l, v;
    struct trie *xi, *focus, *other; 
    focus = trie_tail(cl); 
    other = trie_head(cl);

    if ((v=Value[key_of(other->par)]) != DC) { 
      if (v) {
	if (psign_of(other)) return 0;
      } else if (!psign_of(other)) return 0;
      return locate_head_tail(gcl);
    }
    l = V4[key_of(focus->par)]->level;
    xi = focus->par;

    /* printf("size=%d, focus=%d, other=%d i=%d\n", cl->osize, focus, other, i);*/
    while (xi != focus) {
      if (xi->par == NULL) { xi = cl; continue; }
      if (xi == other) { xi = xi->par; continue; }
      if ((v=Value[key_of(xi->par)]) == DC) { 
	trie_tail(cl) = xi; 
	var4_insert_glink(gcl, xi, gcl->tail_glink);
	return 0; 
      }
      if ((v == TT && psign_of(xi)) || 
	  (v == FF && !psign_of(xi))) {
	if (V4[key_of(xi->par)]->level < l) {
	  trie_tail(cl) = xi; 
	  var4_insert_glink(gcl, xi, gcl->tail_glink);
	}
	return 0;
      }
      xi = xi->par;
    }
    return check_cl_key(cl, key_of(other->par), psign_of(other));
  }
}

var4_record_conflict (cl)
     struct trie *cl;
{
  int i, j, k, total, uip=0, uip2, newlevel;
  int sign_arr[MAX_ATOM], cl_arr[MAX_LENGTH];
  int flag = trie4_max_level(cl, 0);

  trace(3, { printf(" empty cl: "); print_clause_from_leaf(cl);});

  while ((total = var4_collect_parents(cl, cl_arr, &flag)) > 0) {
    var4_insert_lemma(total, cl_arr, flag);
    return 0;
  }
}

var4_collect_parents (cl, cl_arr, flag)
     struct trie *cl;
     int cl_arr[], *flag;
     /* flag passed the max_level and takes back if there is a uip */
{
  int k, key, i, j, var_num=0, total=0, cl_num=0, max_level=*flag;
  int stamp = Branch_num;
  struct trie *no;

  if (cl) {
    cl_num = 1;

#ifdef MORETRACE
    if (TRACE>1) { printf("conflict: "); print_clause_from_leaf(cl); }
#endif

    no = cl->par;
    while (no) {
      if (V4[key=key_of(no)]->level < max_level || mark_of(V4[key]) == NULL) {
	cl_arr[total++] = key;
      } else {
	var_num++;
#ifdef MORETRACE
	if (TRACE>3) printf("queue %d (%d)\n", key, V4[key]->level);
#endif
      }
      weight_add1(key,Value[key]);
      V4[key]->dfs = stamp; 
      no = no->par;
    }
  } else var_num=1;

  for (k = vstack_size()-1; k >= 0 && var_num; k--) {
    key = vs_var(vstack_of(k));
    if (V4[key]->level < max_level) break;
    if (V4[key]->dfs == stamp && V4[key]->level == max_level) {
      if (cl=mark_of(V4[key])) {
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
	  if (V4[i = key_of(no)]->dfs != stamp) { 
	    if (V4[i]->level < max_level || mark_of(V4[i]) == NULL) {
	      cl_arr[total++] = i;
	      if (total >= MAX_LENGTH) {
		for (i = 0; i < total; i++) V4[cl_arr[i]]->dfs = 0;
		return *flag=0;
	      }
	    } else {
	      var_num++;
#ifdef MORETRACE
	      if (TRACE>3) printf("queue %d (%d)\n", i, V4[i]->level);
#endif
	    }
	    weight_add1(i,Value[i]);
	    V4[i]->dfs = stamp; 
	  }
	  no = no->par;
	}
	cl_num++;
	if (!var_num && cl_num>1) { V4[key]->dfs = 0; *flag = 0; return total; }
      } else {
	cl_arr[total++] = key;
      }
      V4[key]->dfs = 0;
    }
  }

#ifdef MORETRACE
  if (TRACE>1) {
    printf("failed %d\n", var_num); fflush(stdout); 
  }
#endif

  for (i = 0; i < total; i++) V4[cl_arr[i]]->dfs = 0;
  return *flag=0;
}

int trie4_max_level (cl, key)
     struct trie *cl;
     int key;
{
  int max = 0;
  cl = cl->par;
  while (cl != NULL) {
    if (key_of(cl) != key &&
	level_of(V4[key_of(cl)]) > max)
      max = level_of(V4[key_of(cl)]);
    cl = cl->par;
  }
  return max;
}

struct gclause * insert_gclause (cl_arr, sign_arr, total)
     int cl_arr[], sign_arr[], total;
{
  int key, i, j=0;
  struct gclause *gcl;
  struct glink *gl; 
  struct trie *cl, *tr = trie_insert_clause2(Root, cl_arr, sign_arr, total-1);

  if (!tr || tr == CLAUSE_MARK) {
    Conflict_cl_level = Backjumping_down = 0;
    return NULL;
  }

  if (!tr->par) {
    Conflict_cl_level = Backjumping_down = 1;
    check(New_unit, printf("New_unit = %d\n", New_unit)); 
    New_unit = ((i=key_of(tr)) << 1) + sign_arr[i];
    return NULL;
  }

  if ((gcl = get_gclause()) == NULL) {
    trace1(4, printf("the slot is full\n"));
    return NULL;
  }

  cl = get_trie();
  cl->par = tr;

  set_key_psign(cl, total, HAS_POS_CL(tr));
  gcl->body = cl;
  /*
  trie_head(cl) = cl;
  var4_insert_glink_end(gcl, cl, gcl->head_glink); 
  trie_tail(cl) = tr;
  var4_insert_glink_end(gcl, tr, gcl->tail_glink);
  */
  return gcl;
}

var4_insert_lemma (num, cl_arr)
     int num, cl_arr[];
{
  int i, j;
  int sign_arr[MAX_LIST];

#ifdef MORETRACE
  if (TRACE == 4 || TRACE > 8) {
    printf("Fresh [%d]: (", Level);
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
    if (V4[j = cl_arr[i]]->level == 0) {
      cl_arr[i--] = cl_arr[--num];
    } else {
      sign_arr[j] = NEG(Value[j]);
    }
    V4[j]->dfs = 0;
  }

#ifdef MORETRACE
  if (TRACE >= 3) {
    printf("NC [%d]: (", Level);
    for (i = 0; i < num; i++) {
      j = cl_arr[i];
      printf(" %s%d", ((sign_arr[j])? "" : "-"), j);
    }
    printf(" )\n");
  }
#endif

  if (num <= GROW) {
    num = insert_sorter(cl_arr, num);

    if (num == 0) {
      Conflict_cl_level = Backjumping_down = 0;
    } else if (num == 1) {
      Conflict_cl_level = Backjumping_down = 1;
      check(New_unit, printf("New_unit = %d\n", New_unit)); 
      New_unit = (cl_arr[0] << 1) + sign_arr[cl_arr[0]];
    } else {
      struct gclause *gcl;

      Clause_num++;
      if (gcl = insert_gclause(cl_arr, sign_arr, num)) {

#ifdef MORETRACE
	if (TRACE >= 3) { printf("Gnc "); print_gclause(gcl); }
#endif

	Conflict_cl = gcl->body;
	Gclause_New[Gclause_New_idx++] = gcl;
	if (Gclause_New_idx >= MAX_STACK) {
	  fprintf(stderr, "Gclause_New (%d) overflow\n", MAX_STACK);
	  exit(1);
	}

	if ((num = adjust_conflict_level(Conflict_cl, &i))
	    < Conflict_cl_level) {
	  Conflict_cl_level = num;
	  Backjumping_down = i;
	}
      } else {
	int max=0;
	for (i = 0; i < num; i++) if ((j=V4[cl_arr[i]]->level) > max) { 
	  max = j; 
	}
	Conflict_cl_level = max;
      }
    }
  } else {
    int max=0;
    for (i = 0; i < num; i++) if ((j=V4[cl_arr[i]]->level) > max) { 
      max = j; 
    }
    Conflict_cl_level = max;
  }
}

int stop () { return 1; }
