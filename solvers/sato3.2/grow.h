/***************************************************
 *
 *  TYPE Declaration
 *
 ***************************************************/

struct gclause {
  int osize, unit;
  int psize;
  int watch1;
  int watch2;
  int *lits;
};

struct var4 { 
  int key;
  int level;
  int dfs;
  struct gclause *gmark;
  struct glink *pos, *neg;
  struct glink *input_pos, *input_neg;
  int neg_count, pos_count;
  struct var4 *next;
};

struct glink {
  struct gclause *cl;
  struct glink *next;
};

/* Micros */
#define WPLUS 1

#define free_glink(no) \
    no->next = Glink_avail; \
    Glink_avail = no

#define assert(i) if (!(i)) { printf("assert failed\n"); stop(); }
#define add_weight1(i) V4[i]->pos_count++
#define left(i) (((i) << 1)+1)
#define right(i) ((((i)+1) << 1))
#define parent(i) ((((i)-1) >> 1))

#define save_assign_value(i, val)\
  if (Backup_idx) { V4[i]->next = Top_var4->next; Top_var4->next = V4[i]; }\
  assign_value(i, val)

struct gclause **Gclauses;
struct var4 **V4;
struct var4 *Top_var4;
struct glink *Glink_avail;
int Slot_total;
int Slot_full = 0;
struct glink *NHcls = NULL;
struct gclause **Ucl_queue = NULL;
struct gclause **Gclause_New = NULL;
int Gclause_New_idx = 0;
int Ucl_queue_idx = 0;
int Ucl_queue_idx_end = 0;
int Time_stamp;
int Wait_and_see = 0;
int Gcl_size;
int Slot_avail;
