#define TAPE            int*
#define TAPE_BLOCK      16*MAX_SHORT
#define MAX_TAPE        100

#define content_of(a,b) (*((int*)(a)+(b)))
#define count_of_clause(a) (*((int*)(a)))
#define pcount_of_clause(a) (*((int*)(a)+1))
#define ncount_of_clause(a) (count_of_clause(a)-pcount_of_clause(a))
#define stamp_of_clause(a) (*((int*)(a)+2))
#define active_clause(a) (*((int*)(a)+2) == 0)
#define size_of_clause(a) (*((int*)(a)+3))
#define nth_lit_of_clause(a,b) (*((int*)(a)+4+b))
#define Tape(a, b) = Tape_space[a][b]
#define address_of(a,b) (int)(&(Tape_space[a][b]))
#define propagate(a,b) ((b)? propagate_true(a) : propagate_false(a))

#define free_clause_cell(no) \
  Clause_frees++; \
  Clause_avails++; \
  no->next = Clause_avail; \
  Clause_avail = no

/***************************************************
 *
 *  TYPE Declaration
 *
 ***************************************************/

struct clause {
  int  address;
  struct clause *next;
};

struct elem { 
  int pos_address, neg_address;
  int pos_count, neg_count;
  SATOINT key;
  SATOINT idx;
  SATOINT depen[10];
};

struct clause *Clause;
struct clause *NHClause;

int **Tape_space;            /* a large storage space */
int  Tape_offset;            /* offset in the current tape */
int  Tape_count;             /* # of Tapes been used */

struct elem **L;
struct elem *Top_elem;

long unsigned Clause_frees, Clause_avails, Clause_gets, Clause_news;
struct clause *Clause_avail;
struct clause *EMPTY;

/* Total memory for variables: 13*4 = 52 bytes */
