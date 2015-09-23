/* 

  Literal: 
     A literal is a variable with a sign. A variable is represented
     by a positive integer.
     One bit is used to denote the sign of a literal: 
              0 == positive, 1 == negative.

  Clause:
     Unit clauses are stored in Value[] or L5[x]->value.
     Binary clauses are stored in Bcs[].
     Other clauses are stored on tapes:
     A list of literals precedenced by its size (in negated form), head and
        tail indices.
     Two literals indicated by head/tail are head/tail literals. 
     Each literal is represented by a 32 bit integer, with one bit 
	representing its sign.

  Tape: 
     All non-unit, non-binary clauses are saved in an integerd array called Tape.
     An element in a tape can be (i) a literal, (ii) size of a clause,
        (iii) head/tail indices, (iv) zero, unused space, (v) values of quasi-clause.
 */

/***************************************************
 *
 *  TYPE Declaration
 *
 ***************************************************/

#define TAPE            int*

/***************************************************
 *
 *  MACRO Declaration
 *
 ***************************************************/

/* Macros for literals */
#define set_lit(p,ks) *(p) = ks

/* Macros for the special head/tail literals */
#define is_head(p) (*(p-1)<0)
#define get_head(cl) cl[cl[1]]
#define get_tail(cl) cl[cl[2]]
#define set_head_tail(p,i) *(p) = i
#define is_head_tail(cl,i) (i == cl[1] || i == cl[2])
#define is_literal(p) (*(p) > 0)
#define not_literal(p) (*(p) <= 0)

/* Macros for clauses */
#define set_clause_size(p,size) *p = -(size+3)
#define size_of_clause(p) (-*p)  
/* acutual size plus 3 */
#define set_clause_address(p) while (*p > 0) --p

#define is_from_binary(p) ((int) p) < 0
#define key_from_binary(p) -((int) p)

/* Macros for nclauses */
#define value_of(cl) -cl[1] 
#define cvalue(cl) cl[2]
#define dec_cvalue(cl) --cl[2]
#define set_ncl_val(cl,tt) cl[2]=tt

#define undeleted_clause(cl) cl[1] 
#define undeleted_head_tail(p) *p 
#define is_normal(cl) (cl[1] > 0) 
#define is_quasi_cl(cl) (cl[1] < 0) 

/***************************************************
 *
 *  VARIABLE Declaration
 *
 ***************************************************/

int TAPE_BLOCK;
TAPE *Tape_space;            /* a large storage space */
TAPE Tape_limit;             /* limit of each tape */
int Input_tape;
int Lemma_tape;
int last_Delete_num=0;

unsigned long Deleted_cells, Half_total_cells;

/* Total memory for variables: 6x4 bytes */


/***************************************************
 *
 *  FUN Declaration
 *
 ***************************************************/

void tape_init ()
{
  int i;

  Deleted_cells = 0;

  if (Max_atom <= 100) MAX_TAPE = 64;
  else if (Max_atom <= 1000) MAX_TAPE = 128;
  else if (Max_atom <= 10000) MAX_TAPE = 256;
  else if (Max_atom <= 100000) MAX_TAPE = 512;
  else MAX_TAPE = 1024;
  TAPE_BLOCK = MAX_TAPE << (GROW+3);

  Tape_space = (TAPE *) malloc((MAX_TAPE) * (sizeof(TAPE)));
  memory_count((sizeof(TAPE *)*MAX_TAPE), "Tape_space");
  Tape_limit = (TAPE) malloc((MAX_TAPE) * (sizeof(int)));
  memory_count((sizeof(TAPE)*MAX_TAPE), "Tape_limit");

  for (i = 0; i < MAX_TAPE; i++) {
    Tape_space[i] = NULL;
    Tape_limit[i] = 0; 
  }
  Tape_space[0] = (TAPE) malloc((TAPE_BLOCK) * (sizeof(int)));
  if (!Tape_space[0]) { fprintf(stderr, "out of memory\n"); exit(0); }
  memory_count((sizeof(TAPE) * TAPE_BLOCK), "Tape");
  Input_tape = 0;
  Lemma_tape = MAX_TAPE-1;
  if (SELECT <= 3) { /* Tape[0] for Non-horn clauses */
    Input_tape = 1;
    Tape_space[1] = (TAPE) malloc((TAPE_BLOCK) * (sizeof(int)));
    if (!Tape_space[1]) { fprintf(stderr, "Out of memory\n"); exit(0); }
    memory_count((sizeof(TAPE) * TAPE_BLOCK), "Tape");
  }
  Half_total_cells = (TAPE_BLOCK*MAX_TAPE)>>1;
}

adjust_max_tape ()
{
  int i0 = Input_tape+((SELECT < 4)? 1 : 2);
  int i;
  
  i = i0*(GROW+1); 
  if (i < MAX_TAPE) {
    trace(1, printf("c MAX_TAPE is set to %d (%d, %d)\n", 
		    i, MAX_TAPE, i0));
    MAX_TAPE = i;
    Lemma_tape = MAX_TAPE-1;
  } else {
    trace(1, printf("c MAX_TAPE (%d) is not as big as %d\n", MAX_TAPE, i));
  }
}

int *get_tape (s, i)
     int s, i;
{
  if (Tape_space[i] == NULL) {
    if ((Tape_space[i] = (TAPE) malloc((TAPE_BLOCK) * (sizeof(int)))) == NULL) {
      fprintf(stderr, "ABEND, malloc returns NULL (out of memory).\n");
      fprintf(stderr, "%10.2f K has been mallocated.\n", memory_count_get());
      return NULL;
    }
    memory_count((sizeof(TAPE) * TAPE_BLOCK), "tape");
    /* printf("tape[%d] is ready (%d)\n", i, Input_tape);*/
  }
  Tape_limit[i] = s;
  return Tape_space[i];
}

int *get_tape_head0 (s, t)
     int s, t;
{
  int i, *p;

  if (Tape_limit[t]+s < TAPE_BLOCK) {
    p = Tape_space[t]+Tape_limit[t];
    Tape_limit[t] += s;
    return p;
  }

  if (Lemma_tape <= Input_tape+1) return NULL;
  t = --Lemma_tape;
  Tape_limit[t] = s;
  return Tape_space[t];
}

int *get_tape_head (s, t)
     int s, t;
{
  int i, *p;
  s += 3;

  if (!Tape_space[t]) return get_tape(s, t);

  if (Tape_limit[t]+s < TAPE_BLOCK) {
    p = Tape_space[t]+Tape_limit[t];
    Tape_limit[t] += s;
    return p;
  }
  if (t == 0) { 
    t = Input_tape;
    if (Tape_limit[t]+s < TAPE_BLOCK) {
      p = Tape_space[t]+Tape_limit[t];
      Tape_limit[t] += s;
      return p;
    }
  }
  if (Lemma_tape <= Input_tape+1) {
    if (last_Delete_num < Delete_num) {
      clean_tapes();
      return get_tape_head0(s, Lemma_tape);
    } else {
      return NULL;
    }
  }
  if (t == Input_tape) t = ++Input_tape;
  else t = --Lemma_tape;
  return get_tape(s, t);
}

delete_clauses_on_tape ()
{
  int i, j, k, len, *cl, *cl2;

  trace(3, printf("Begin deleting clauses ...\n"));

  i = MAX_TAPE-1;
  while (i >= Lemma_tape) {
    cl = Tape_space[i];
    cl2 = cl+Tape_limit[i];
    while (cl < cl2) {
      len = size_of_clause(cl);
      if (undeleted_clause(cl) && len > DLENGTH+2 &&
	  L5[j=get_head(cl)]->value != FF &&
	  L5[k=get_tail(cl)]->value != FF) {
	L5[j]->deleted = L5[k]->deleted = 1;
	Deleted_cells += len;
	Delete_num++;
	cl[1] = cl[2] = 0; /* mark as deleted */
      }
      cl += len;
    }
    i--;
  }

  /* clean the tapes? */
  if (Deleted_cells >= Half_total_cells)
    clean_tapes();
  else {
    if (DLENGTH > 5 && (Lemma_tape<<1) < (MAX_TAPE-Input_tape))
      DLENGTH--;

    /* we need to remove hts of deleted clauses */
    /* this operation can be done lazily */
    for (k = get_lit(Max_atom,1); k >= 2; k--) if (L5[k]->deleted) {
      int **pts = L5[k]->hts;
      L5[k]->deleted = 0;
      j = hts_count(pts);
      i = hts_begin(); 
      while (i < j) {
	if (undeleted_head_tail(pts[i])) i++;
	else pts[i] = pts[--j];
      }
      hts_set_count(pts,i);
    }
  }
}

clean_tapes ()
{
  int ck, i, j, j2, k, t2, *cl, *cl2, *tape, *tape2;
  int **ptrs; 

  trace(4, printf("c Begin tape cleaning ...\n"));

  i = t2 = MAX_TAPE-1;
  tape2 = Tape_space[t2];
  j2 = 0;

  while (i >= Lemma_tape) {
    int limit = Tape_limit[i];
    tape = Tape_space[i--];
    for (j=0; j < limit; ++j){ 
      if ((k=tape[j]) < 0) {
	/* beginning of clause */
	if (tape[j+1] == 0) {
	  j = j-k-1;  /* ++j later */
	} else {
	  if (j2-k >= TAPE_BLOCK) {
	    Tape_limit[t2] = j2;
	    tape2 = Tape_space[--t2];
	    tape2[0] = k;
	    j2 = 1;
	    cl = &tape[j];
	    cl2 = tape2;
	  } else {
	    cl = &tape[j];
	    cl2 = &tape2[j2];
	    tape2[j2++] = k;
	  }

	  /* cl, cl2 are needed to update gmark */
	  if (L5[get_head(cl)]->value == FF) {
	    ck = lit_var(get_tail(cl));
	    if (var_gmark(ck) == (int) cl) var_gmark(ck) = (int) cl2;
	  } else if (L5[get_tail(cl)]->value == FF) {
	    ck = lit_var(get_head(cl));
	    if (var_gmark(ck) == (int) cl) var_gmark(ck) = (int) cl2;
	  }
	}
      } else {
	tape2[j2++] = k;
      }
    }
  }
  Tape_limit[t2] = j2;
  for (j = Lemma_tape; j < t2; j++) Tape_limit[j] = 0;
  trace(2, printf("c %ld clauses deleted (total=%d), avg len = %d, %d tapes released\n",
		  Delete_num-last_Delete_num, Delete_num,
		  Deleted_cells/(Delete_num-last_Delete_num), 
		  t2-Lemma_tape));
  Lemma_tape = t2;
  Deleted_cells = 0;
  last_Delete_num = Delete_num;

  /* clean up the head_tail pointers from variables */
  for (i= get_lit(Max_atom,1); i >= 2; i--) {
    hts_set_count(L5[i]->hts,hts_begin());
  }

  /* re-insert the head_tail_pointers */
  /* how to avoid repeating this work for input clauses? */
  i = 0; 
  while (i < MAX_TAPE) {
    cl = Tape_space[i];
    cl2 = cl+Tape_limit[i];
    while (cl < cl2) {
      if (is_normal(cl)) {
	/* insert head */
	ptrs = L5[get_head(cl)]->hts;
	push_head_tail(ptrs, cl+1);
	/* insert tail */
	ptrs = L5[get_tail(cl)]->hts;
	push_head_tail(ptrs, cl+2);
      }
      cl += size_of_clause(cl);
    }
    if (i == Input_tape) i = Lemma_tape;
    else i++;
  }
}

void print_clause (cl)
     TAPE cl;
{
  int i, j, k, v;

  if (is_from_binary(cl)) {
    i = key_from_binary(cl);
    printf("from binary %s%d\n", (i&1)? "" : "-", i>>1);
    return;
  }
  j=size_of_clause(cl);
  if (is_normal(cl)) {
    printf("size=%d ( ", j-3); 
  } else {
    printf("size=%d cval=%d ( ", j-3, cl[2]);
  }

  for (i = 3; i < j; i++) {
    v = cl[i];
    k = lit_var(v);
    if (is_head_tail(cl,i)) printf("^");
    if (lit_sign(v)) printf("-");
    printf("%d%s ", k, (var_value(k) == TT)? "+" : ((var_value(k) == FF)? "-" : "")); 
  }
  if (is_normal(cl)) printf(") h=%d t=%d\n", cl[1]-2, cl[2]-2);
  else printf(")\n");
}

void print_clauses_on_tape (tape1, tape2)
     int tape1, tape2;
{
  int i;

  printf("all clauses on tapes %d-%d\n", tape1, tape2);
  for (i = tape1; i <= tape2; i++) {
    int *cl2, *cl = Tape_space[i];
    cl2 = cl+Tape_limit[i];
    while (cl < cl2) {
      if (size_of_clause(cl) < 5) {
	break;
      } else { 
	print_clause(cl);
	cl += size_of_clause(cl);
      }
    }
  }
}

check_clause (cl)
     TAPE cl;
{
  int j;
  for (j = 3; j < size_of_clause(cl); j++) if (L5[cl[j]]->value == TT) return 0;
  trace(2, { printf("False cl: "); print_clause(cl);});
  return 1;
}

#ifdef QUASICLAUSE
check_nclause (cl)
     TAPE cl;
{
  int j, s=0;
  for (j = 3; j < size_of_clause(cl); j++) if (L5[cl[j]]->value) s++;
  s = s+cl[1];
  if (s > 0) { 
    trace(2, { printf("False cl: "); print_clause(cl); }); return 1;
  }
  return 0;
}
#endif

var5_check_model ()
{
  int i, j, *cl;

  trace(2, printf("c Checking model ...\n"));

  for (i = 0; i <= Input_tape; i++) {
    TAPE cl = Tape_space[i];
    int limit = Tape_limit[i];

    while (limit>0) {
      if (is_normal(cl)) {
	if (check_clause(cl)) return 1;
#ifdef QUASICLAUSE
      } else {
	if (check_nclause(cl)) { return 1; }
#endif
      }
      j = size_of_clause(cl);
      limit -= j;
      cl += j;
    }
  }
  return 0;
}
