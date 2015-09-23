/***************************************************
 *
 *  TYPE Declaration
 *
 ***************************************************/

/* Literal table element */
struct lit5 {
  unsigned char deleted, value;
  unsigned short stamp;
  unsigned short weight_new;
  unsigned short level; /* 2i for level */
  int info2; /* 2i for gmark and 2i+1 for order */
  int info3; /* for SELECT=8 */
  int weight;
  int **hts;
  int *bicls;
#ifdef QUASICLAUSE
  struct nlink *ncls;
#endif
};

struct nlink {
  int * cl;
  struct nlink *next;
};

/* Micros */
#define MAX_CONFLICT 1
#define Level Branch_open

/* if Value[i] = TT, then L5[2i] = TT and L5[2i+1] = FF
   if Value[i] = FF, then L5[2i] = FF and L5[2i+1] = TT 
   if Value[i] = DC, then L5[2i] = DC and L5[2i+1] = DC */

#define assign_value0(k)\
  L5[k]->value = FF;\
  L5[NEG((k))]->value = TT
#define assign_value1(k)\
  L5[k]->value = TT;\
  L5[NEG((k))]->value = FF

#ifdef MINONE

#define assign_value2(k)\
  L5[NEG((k))]->value = TT;\
  if (MINVAR && (lit_sign(k)) && (++Current_best > MINVAR)) { return var5_fail_end(NULL); }\
  L5[k]->value = FF
#define unassign_value(i) \
  if (MINVAR && L5[(i<<1)]->value == TT) --Current_best;\
  L5[get_lit(i,TT)]->value = L5[(i<<1)]->value = DC

#else

#define assign_value2(k) assign_value0(k)
#define unassign_value(i) L5[get_lit(i,TT)]->value = L5[get_lit(i,FF)]->value = DC

#endif

#define var_value(i) L5[(i)<<1]->value
#define var_stamp(i) L5[(i)<<1]->stamp
#define var_level(i) L5[(i)<<1]->level
#define var_gmark(i) L5[(i)<<1]->info2
#define var_order(i) L5[((i)<<1)+1]->info2

#define lit_value(i) L5[i]->value
#define lit_stamp(i) L5[i]->stamp
#define lit_umark(i) L5[i]->stamp
#define lit_gmark(i) L5[(i)&(~1)]->info2
#define lit_order(i) L5[(i)|1]->info2
#define lit_level(i) L5[(i)&(~1)]->level
#define dfs_done(i) L5[(i)|1]->level
#define dfs_time(i) L5[(i)&(~1)]->info3
#define dfs_lowlink(i) L5[(i)|1]->info3
#define lit_weight(i) L5[i]->info3

#define hts_count_inc(ptrs) ((int) ptrs[0])++
#define hts_count_dec(ptrs) --((int) ptrs[0])
#define hts_count(ptrs) (int) *ptrs
#define hts_max(ptrs) (int) ptrs[1]
#define hts_set_count(ptrs,c) ptrs[0]=(int*)c

#define hts_set_max(ptrs,c) (int) ptrs[1]=(int*)c
#define hts_begin() 2

#define bicls_count_inc(ptrs) ptrs[0]++
#define bicls_count_dec(ptrs) --ptrs[0]
#define bicls_count(ptrs) *ptrs
#define bicls_max(ptrs) ptrs[1]
#define bicls_set_count(ptrs,c) ptrs[0]=c
#define bicls_set_max(ptrs,c) ptrs[1]=c
#define bicls_begin() 2

#define delete_head_tail(ptrs,i)\
   ptrs[i] = ptrs[hts_count_dec(ptrs)]

#define push_head_tail(ptrs,ptr)\
   ptrs[hts_count_inc(ptrs)] = ptr

#define insert_head_tail(ptr,ks)\
{ \
  int **ptrs1 = L5[ks]->hts;\
  if (hts_count(ptrs1) == hts_max(ptrs1)) {\
    int **ptrs2 = (int **) malloc((hts_max(ptrs1)<<1) * (sizeof(int *)));\
    memory_count(sizeof(int *) * hts_max(ptrs1), "HTS");\
    if (ptrs2 == NULL) { fprintf(stderr, "insert_head_tail failed.\n"); exit(1); }\
    for (i = hts_max(ptrs1)-1; i >= 0; i--) ptrs2[i] = ptrs1[i];\
    hts_max(ptrs2) += hts_max(ptrs1);\
    free(ptrs1);\
    ptrs1 = L5[ks]->hts = ptrs2;\
  }\
  push_head_tail(ptrs1, ptr);\
}

#define check_new_unit()\
  if (New_unit) { \
      i = New_unit; \
      New_unit = 0;\
      if ((s=L5[i]->value) == DC) { \
      var_level(lit_var(i)) = Level; \
      var_gmark(lit_var(i)) = (int) New_unit_clause; \
      if (New_unit_clause) { trace(6, { printf("unit x%d at level %d by ", i, Level); \
                             print_clause(New_unit_clause);});} \
      print_x_has_to(i); \
      assign_value2(i); \
      vstack_push2(i);\
      if (grow_propagate(i) == UNSAT) return UNSAT; \
    } else if (s == TT) { \
      return var5_fail_end(New_unit_clause);\
  }}

#define collect_one_key(i) \
  if (var_stamp(i) != stamp) { \
    if (var_level(i) < max_level) {\
       cl_arr[total++] = i;\
       if (total >= MAX_LENGTH) { \
 	 trace(4, printf("new clause too big\n")); return 0; }\
    } else { \
       var_num++;\
       trace(4, printf("queue %d (%d)\n", i, var_level(i)));\
    }\
    var_stamp(i) = stamp; \
  }

#ifdef MORETRACE

#define print_let_x_have(k) \
  if (TRACE > 5 || TRACE == 3)  \
     printf("[%d]  let x%d = %d.\n", Branch_open, lit_var(k), lit_sign(k))

#define print_now_let_x_have(k) \
  if (TRACE > 5 || TRACE == 3)  \
     printf(" [%d]  now x%d = %d.\n", Branch_open, lit_var(k), lit_sign(k))

#define print_x_has_to(k) \
  if (TRACE > 5 || TRACE == 3)  \
     printf("      x%d has to be %d [%d].\n", lit_var(k), lit_sign(k), vstack_size())

#define print_x_contradictory(k) \
  if (TRACE > 5 || TRACE == 3)  \
     printf("      x%d has contradictory values.\n", lit_var(k))

#define print_up_to_x \
  if (TRACE > 5 || TRACE == 3)  \
     printf("      reset x%d's value %d.\n", i, var_value(i))

#define print_x_pure(k) \
  if (TRACE > 5 || TRACE == 3)  \
     printf("    x%d is set to %d by pure-literal deletion.\n", lit_var(k), lit_sign(k))

#define print_x_subsume(k) \
  if (TRACE > 6) printf("    [C%d] is subsumed by x%d.\n", Clause_num, lit_var(k))

#define print_x_skip(k) \
  if (TRACE > 6) printf("    %d in [C%d] is skipped.\n", lit_var(k), Clause_num)

#else

#define print_let_x_have(k)
#define print_now_let_x_have(k)
#define print_x_has_to(k)
#define print_x_contradictory(k)
#define print_up_to_x
#define print_x_pure(k)
#define print_x_subsume(k)
#define print_x_skip(k)

#endif

struct lit5 **L5;
struct var5 **V5;
int STAMPSIZE = (1<<15)-1;
int New_unit = 0;
int *New_unit_clause = NULL;
int *Conflict_gcl;
int *VarOrder, VarOrderSize;
int Empty_binary[5];
int stamp, timer;
