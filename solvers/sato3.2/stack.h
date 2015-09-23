/* Unit clause queue */
#define Unit_cls Tmp
#define Unit_cls_idx Tmp_idx
#define Unit_cls_idx_end Tmp_idx_end

#define uqueue_init() Unit_cls_idx = Unit_cls_idx_end = 0

#define uqueue_nonempty() (Unit_cls_idx != Unit_cls_idx_end)

#define uqueue_add(i) \
   Unit_cls[Unit_cls_idx_end++] = i;\
   if (Unit_cls_idx_end == MAX_STACK) Unit_cls_idx_end = 0;\
   if (Unit_cls_idx_end == Unit_cls_idx) \
      { fprintf(stderr, "Unit clause queue overflow\n"); exit(1); }

#define uqueue_pop(i) \
   i=Unit_cls[Unit_cls_idx++];\
   if (Unit_cls_idx == MAX_STACK) Unit_cls_idx = 0

/* Value stack */

/* A value stack is an unsigned int array of length Max_atom.
   Each entry in the stack contains the following info:
      the variable  -- the high 30 bits.
      the value assiged to the variable -- the third bit
      the second choice of the selected variable -- the second bit
      the value assiged due to selection -- the first bit
*/

unsigned int *Vstack, Vstack_idx, VALUE_BIT, SELECT_BIT, SECOND_BIT;

#define vstack_init() \
   VALUE_BIT = 4;\
   SECOND_BIT = 2;\
   SELECT_BIT = 1;\
   Vstack = (int *) malloc((Max_atom) * (sizeof(int)));\
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

#define vstack_pop() Vstack[--Vstack_idx]
#define vstack_of(k) Vstack[k]
#define vstack_nonempty() Vstack_idx
#define vstack_size() Vstack_idx
#define vstack_resize(k) Vstack_idx = k
#define vs_var_and_value(i) (i>>2)
#define vs_var(i) (i>>3)
#define vs_value(i) ((i&VALUE_BIT)>2)
#define vs_second(i) (i&SECOND_BIT)
#define vs_selected(i) (i&SELECT_BIT)

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
