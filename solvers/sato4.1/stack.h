/* Unit clause queue */

#define uqueue_init() Unit_cls_idx = Unit_cls_idx_end = 0

#define uqueue_nonempty() (Unit_cls_idx != Unit_cls_idx_end)

#define uqueue_add(i) \
   Unit_cls[Unit_cls_idx_end++] = i;\
   if (Unit_cls_idx_end == MAX_STACK) Unit_cls_idx_end = 0;

#define uqueue_pop(i) \
   i=Unit_cls[Unit_cls_idx++];\
   if (Unit_cls_idx == MAX_STACK) Unit_cls_idx = 0


/* value stack */

/* A value stack is an unsigned int array of length Max_atom.
   Each entry in the stack contains the following info:
      the variable  -- the high 30 bits.
      the value assiged to the variable -- the third bit
      the second choice of the selected variable -- the second bit
      the assignment due to selection -- the first bit
  That is, the last two bits:
     01: selected, first choice
     10: selected, second choice
     00: forced by unit clause
     11: forced by unit clause from a masked clause (related to MAXSAT).
*/

#define SELECT_BIT 1
#define SECOND_BIT 2
#define MASK_BIT   3
#define VALUE_BIT  4

unsigned int *Vstack, Vstack_idx;

#define vstack_init() \
   Vstack = (int *) malloc((Max_atom+1) * (sizeof(int)));\
   Vstack_idx = 0

#define vstack_push(k,s,c,p)\
   uqueue_add((k<<1)+s); \
   Vstack[Vstack_idx++] = (((k<<1)+s)<<2)+(c<<1)+p;\
   check(Vstack_idx>Max_atom, { printf("Vstack overflow\n"); vstack_print();})

#define vstack_push0(ks)\
   uqueue_add(ks); \
   Vstack[Vstack_idx++] = (ks<<2);\
   check(Vstack_idx>Max_atom, { printf("Vstack overflow\n"); vstack_print(); exit(1);})

#define vstack_push1(ks)\
   uqueue_add(ks); \
   Vstack[Vstack_idx++] = (ks<<2)+1;\
   check(Vstack_idx>Max_atom, { printf("Vstack overflow\n"); vstack_print(); exit(1);})

#define vstack_push2(ks)\
   uqueue_add(ks); \
   Vstack[Vstack_idx++] = (ks<<2)+2;\
   check(Vstack_idx>Max_atom, { printf("Vstack overflow\n"); vstack_print(); exit(1);})

#define vstack_push3(ks)\
   uqueue_add(ks); \
   Vstack[Vstack_idx++] = (ks<<2)+3;\
   check(Vstack_idx>Max_atom, { printf("Vstack overflow\n"); vstack_print(); exit(1);})

#define vstack_pop() Vstack[--Vstack_idx]
#define vstack_of(k) Vstack[k]
#define vstack_nonempty() Vstack_idx
#define vstack_size() Vstack_idx
#define vstack_resize(k) Vstack_idx = k
#define vs_literal(i) (i>>2)
#define vs_var(i) (i>>3)
#define vs_value(i) ((i&VALUE_BIT)>>2)
#define vs_selected(i) ((i&MASK_BIT)==SELECT_BIT)
#define vs_second(i) ((i&MASK_BIT)==SECOND_BIT)
#define vs_mask(i) ((i&MASK_BIT)==MASK_BIT)

vstack_collect_selected (backup)
     int backup[];
{
  int i, idx=0; 
  for (i = 0; i < vstack_size(); i++) 
    if (vs_selected(vstack_of(i))) 
      backup[idx++] = vs_var(vstack_of(i));
    else if (vs_second(vstack_of(i))) 
      backup[idx++] = -vs_var(vstack_of(i));
  return idx;
}

vstack_reinit ()
{
  int i, k;

  for (i = 0; i < vstack_size(); i++) {
    k = vs_var(vstack_of(i));
    unassign_value(k);
    var_gmark(k) = 0;
  }
  vstack_size() = 0;
  uqueue_init();
}

vstack_print () 
{
  int i; 
  printf("value stack:\n");
  for (i = 0; i < vstack_size(); i++) {
    int info = vstack_of(i);
    int k = vs_var(info);
    if (vs_selected(info)) printf("\n");
    printf("%d: x%d, val %d=%d, lvl %d ", i, k, 
	   vs_value(info), var_value(k), var_level(k));
    if (var_gmark(k)) print_clause((int*)var_gmark(k)); else printf("\n");
  }
}

int vstack_backup (level)
     /* back up to Level level; return the last item of Level level */
     int level; 
{
  int vv=0, i, k, info, end_pos=0, hold_pos, flipped=0;
  struct clause *cl;

  for (k = vstack_size()-1; k >= 0; k--) {
    info = vstack_of(k);
    i = vs_var(info);

    if (var_level(i) < level) {
      vstack_resize(k+1);
      trace(8, printf("  touch x%d, level = %d\n", i, var_level(i)));
      return vv;
    }
    vv = vs_literal(info);

#ifdef APPLICATION
    if (QAP && (vv & 1)) qappair_pop(vv>>1);
#endif

    trace(6, printf(" [%d,%d,%d]: ", k, var_level(i), var_order(i)));
    print_up_to_x;
    var_gmark(i) = 0;
    var_stamp(i) = 0;
    unassign_value(i);

    if (vs_selected(info)) { 
      Branch_open--; 
      if (SELECT > 3 && VarOrderFirst > var_order(i))
	VarOrderFirst = var_order(i);
    }
    else vv = 0;
  }
  vstack_resize(0);
  return vv;
}
