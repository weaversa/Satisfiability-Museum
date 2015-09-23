/***************************************************
 *
 *  TYPE Declaration
 *
 ***************************************************/

struct trie { /* trie of clauses */
  /* char psign, esign; int key; */
  int info;   /* info = (key<<1 + psign)<<10 + esign */
  struct trie *bro;
  struct trie *pos, *neg;
  struct trie *par;
  struct links *link;
};

struct links {
  struct trie *lin;
  struct trie *back;
  struct cap *stamp;
};

struct cap { 
  struct trie *tr;
};

struct unit { 
  int lit;
  struct unit *next;
};

struct gclause {
  struct trie *body;
  struct glink *head_glink, *tail_glink;
};

struct glink { 
  struct gclause *cl;
  struct glink *next;
  struct glink *prev;
};

struct var4 { 
  short level, dfs;
  struct trie *mark;
  struct glink *cls[2];
};

struct var3 { 
  int id;
  struct trie *push, *pull;
  struct trie **pos, **neg;
  struct cap *both, *poss, *negs;
  struct cap *pposs, *pnegs;
  struct var3 *next;
  /* struct unit *units; unit clauses */
  /* binary clauses: a=first_literal; b=second_literal 
  struct trie *pos2b, *neg2b, *pos2a, *neg2a; 
  struct trie **pos3a, **neg3a, **pos3b, **neg3b, **pos3c, **neg3c; */
};

struct var2 { 
  int id;
  int pos_extra;
  int neg_extra;
  int level;
  int pos2;
  int pure;
  int pos_count;
  int neg_count;
  struct trie *frozen, *mark;
  struct trie **pos, **neg;
  struct var2 *next;
};

/**********************
  MACROS
***********************/
#define MAX_CONFLICT 1
#define Level Branch_open

#define HAS_POS_CL(no) (no->pos == CLAUSE_MARK)
#define HAS_NEG_CL(no) (no->neg == CLAUSE_MARK)

#define count_of_clause(cl) cl->info
#define active_clause(cl) cl->neg == NULL
#define innactive_clause(cl) cl->neg
#define frozen_lin(cl) cl->neg

#define set_id(it,k) it->id = k
#define id_of(it) it->id

#define SHARED_BITS 1023
int INSEARCH = 0;

#define set_key_psign(cl,k,s) cl->info = (((k<<1)+s)<<10)+INSEARCH
#define set_key(cl,k) cl->info = (k<<11)+INSEARCH
#define key_of(cl) (cl->info>>11)
#define set_psign(cl,s) cl->info = cl->info+(s<<10)
#define psign_of(cl) ((cl->info>>10)&1)
#define set_esign(cl,s) cl->info = ((cl->info>>2)<<2)+s
#define esign_of(cl) (cl->info&3)
#define shared_trie(cl) (cl->info&SHARED_BITS)
#define shared_inc(cl) cl->info--
#define shared_dec(cl) cl->info++

#define binary_lin(cl) cl->pos
#define unit_lin(cl) cl->link->back

#define level_of(it) it->level
#define mark_of(it) it->mark
#define frozen_cls(it) it->frozen

#define free_trie_cell(no) \
    no->bro = Trie_avail; \
    Trie_avail = no

#define free_unit(no) \
    no->next = Unit_avail; \
    Unit_avail = no

#include "trie0.h"
	 

#define EXTRA_SPACE (GROW<<2)
#define PURECHECK -MAX_ATOM
#define MAGIC 7 /* at most 12*/
#define two14 16383   /* 2^14-1 */
#define two15 32767   /* 2^15-1 */
#define BINARY 0
#define WPLUS LINE

#define end_mark(no) no->link->lin

#define trie_assign_value(i, val)\
  if (Backup_idx) { \
     /* check_unit_implacants(i, val); */ \
     V3[i]->next = Top_var3->next; \
     Top_var3->next = V3[i]; \
  }\
  assign_value(i, val)

#define trie2_assign_value(i, val)\
  if (Backup_idx) { V2[i]->next = Top_var2->next; Top_var2->next = V2[i]; }\
  assign_value(i, val)

/* Micros for DATA = 4 */

#define trie_head(no) no->pos
#define trie_tail(no) no->neg
#define trie_end_sign(no) psign_of(no)
#define trie_end_key(no) key_of(no->par)
#define head_sign(cl) trie_end_sign(trie_head(cl))
#define tail_sign(cl) trie_end_sign(trie_tail(cl))
#define head_key(cl) trie_end_key(trie_head(cl))
#define tail_key(cl) trie_end_key(trie_tail(cl))

#define free_glink(no) \
    no->next = Glink_avail; \
    Glink_avail = no

#define delete_glink(gl)\
  gl->next->prev = gl->prev;\
  gl->prev->next = gl->next

#define idle_gcl(cl) \
    (((head_sign(cl))? (Value[head_key(cl)] != FF) : (Value[head_key(cl)] != TT)) && \
    ((tail_sign(cl))? (Value[tail_key(cl)] != FF) : (Value[tail_key(cl)] != TT)))


/**********************
  VARIABLES
***********************/

/* long unsigned Trie_frees, Trie_avails, Trie_gets, Trie_news; */
struct unit *Unit_avail;
struct trie *Trie_avail;

struct trie *CLAUSE_MARK;
struct trie *Root;
struct trie *NHtrie;
struct trie *Newtrie;
struct trie *CLtrie;

struct var3 **V3;
struct var3 *Top_var3;

struct var2 **V2;
struct var2 *Top_var2;

struct trie **Trie2_Ucl;
int Trie2_Ucl_idx;

/* memory of variables in this file: 8x4+4x11 = 76 bytes */
struct trie *Conflict_cl, *Old_cls, *BItrie;
struct trie *Nonunit_cls = NULL;
int Conflict_cl_level;
long Pure_num, *Weight;
int Jump_num, Miss_num;
int Max_cand;
int *Stack2, Stack2_idx;

/* Variables for DATA = 4 */
struct var4 **V4;
struct glink *Glink_avail;
int Time_stamp;
int Backjumping_down = 0;
int New_unit = 0;
int debug=1;
int STAMPSIZE = (1<<15)-1;
struct gclause **Gclause_New;
int Gclause_New_idx;
