/* All the clauses are kept in the Slots from 0 to Slot_total-1 */
struct gclause **Slots;
int Slot_total, Slot_kept, Slot_used, Slot_once_full;
int Expand_slot=0;

#define slot_init()\
  Slot_used = Slot_kept = Slot_once_full = 0;\
  if (GROW) Slot_total = (GROW*100) + Clause_num + (Clause_num>>1);\
  else Slot_total = Clause_num;\
  trace(1, printf("c Variables %d, Clauses %d, Slots allocated: %d\n", \
     Max_atom, Clause_num, Slot_total));\
  Slots = (struct gclause **) malloc(sizeof(struct gclause *)*Slot_total);\
  if (Slots == NULL) { fprintf(stderr, "run out of memory\n"); exit(1); }\
  for (i = 0; i < Slot_total; i++) Slots[i] = NULL;\
  Memory_count += sizeof(struct gclause *)*(Slot_total)

#define slot_size() Slot_used
#define slot_of(i) Slots[i]
#define slot_full() (Slot_used == Slot_total)
#define slot_add(p) Slots[Slot_used++] = p
#define slot_next() Slots[Slot_used]
#define slot_set_kept(k) Slot_kept = k

#define slot_nh_swap() \
   if (NH_num+1 < Slot_used) { \
     Slots[Slot_used-1] = Slots[NH_num];\
     Slots[NH_num++] = gcl; \
   } else NH_num++

double_slots ()
{
  struct gclause **slots;
  int i = Slot_total;
  Expand_slot++;
  Slot_total = Slot_total<<1;
  slots = (struct gclause **) malloc(sizeof(struct gclause *)*Slot_total);
  if (slots == NULL) { Expand_slot = GROW; return 0; }
  Memory_count += sizeof(struct gclause *)*(i);
  while (i--) slots[i] = Slots[i];
  free(Slots);
  Slots = slots;
  for (i = (Slot_total<<1); i < Slot_total; i++) Slots[i] = NULL;
  return 1;
}

slot_cleanup ()
     /* remove old/idle/long clauses from the first half of generated clauses */
{
  struct gclause *gcl;
  struct trie *cl;
  int h, j, i = Slot_kept, t = 4, c = 1;
  h = (slot_size()-i)>>1;
  j = h + i;
  
  while (h--) {
    gcl = slot_of(i);
    cl = gcl->body;
    if (key_of(cl) <= 4) { 
      slot_of(i++) = slot_of(Slot_kept);
      slot_of(Slot_kept++) = gcl;
    } else if (key_of(cl) > t && idle_gcl(cl)) {
      struct glink *g;
      trace(3, { printf("Destroy at %d ", Level); print_clause_from_leaf(cl); }); 
      g = gcl->head_glink;
      delete_glink(g);
      g->next = g->prev = NULL;
      g = gcl->tail_glink;
      delete_glink(g);
      g->next = g->prev = NULL;
      slot_of(i++) = slot_of(j);
      slot_of(j++) = gcl;
      /* more trie nodes need to be freed */
      free_trie_cell(gcl->body);
      t = 4 + (++c >> 8);
    } else {
      i++;
    }
  }

  while (j < Slot_total) {
    gcl = slot_of(i);
    slot_of(i++) = slot_of(j);
    slot_of(j++) = gcl;
  }
  Slot_used = i;
  trace(1, printf("c slots: %d used, %d kept, %d released\n", 
		  Slot_used, Slot_kept, Slot_total-Slot_used));
  if (Expand_slot < GROW && (Slot_used > Slot_total*0.75)) double_slots();
} 
