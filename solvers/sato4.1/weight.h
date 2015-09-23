/* Variable weights for selecting literals */

#define weight_set(ks) L5[ks]->weight = L5[ks]->weight_new; L5[ks]->weight_new = 0
#define weight_add(ks,x) L5[ks]->weight_new += x
#define weight_add1(ks)  L5[ks]->weight_new++
#define weight_new_val(ks) L5[ks]->weight_new
#define weight_value(ks) L5[ks]->weight
#define weight(k) Value[k]

/* weight(i) = max{weight(x0), weight(x1)} */
#define weight_update0()\
  if (((Branch_num) & 511)==1) {\
    for (i = 1; i <= Max_atom; i++) {\
      int x0 = i<<1;\
      int x1 = get_lit(i,1);\
      L5[x0]->weight = (L5[x0]->weight >> 1) + L5[x0]->weight_new;\
      L5[x1]->weight = (L5[x1]->weight >> 1) + L5[x1]->weight_new;\
      L5[x0]->weight_new = L5[x1]->weight_new = 0;\
      if (L5[x0]->weight >= L5[x1]->weight)\
          { weight(i) = L5[x0]->weight; }\
      else \
          { weight(i) = L5[x1]->weight; }\
    }\
    if (SELECT > 3) { mergesort_var_order();  VarOrderFirst = 0;} \
  }

/* weight(i) = weight(x0)+weight(x1) */
#define weight_update1()\
  if ((Branch_num & 511) == 1) {\
    for (i = 1; i <= Max_atom; i++) {\
      int x0 = i<<1;\
      int x1 = get_lit(i,1); \
      L5[x0]->weight = (L5[x0]->weight >> 1) + L5[x0]->weight_new;\
      L5[x1]->weight = (L5[x1]->weight >> 1) + L5[x1]->weight_new;\
      L5[x0]->weight_new = L5[x1]->weight_new = 0;\
      weight(i) = L5[x0]->weight+L5[x1]->weight;\
    }\
    if (SELECT > 3) { mergesort_var_order();  VarOrderFirst = 0;} \
  }

/* weight(i) = second-order(weight(x0), weight(x1)) */
#define weight_update7() if (!(Branch_fail & 15)) weight_update7_aux()

weight_update7_aux ()
{
  int i;

  for (i = 1; i <= Max_atom; i++) {
    int x0 = i<<1;
    int x1 = (i<<1)+1;
    if (GROW) {
      L5[x0]->weight = (L5[x0]->weight >> 1) + L5[x0]->weight_new;
      L5[x1]->weight = (L5[x1]->weight >> 1) + L5[x1]->weight_new;
      L5[x0]->weight_new = L5[x1]->weight_new = 0;
    }
    if (var_value(i) == DC) {
      int w0 = second_weight(x0);
      int w1 = second_weight(x1);
      if (CHOICE2) 
	weight(i) = w0+w1;
      else if (w0 > w1) 
	weight(i) = w0;
      else weight(i) = w1;
      printf("W2[%d] = %d\n", i, weight(i));
    }
  }
  mergesort_var_order();  
  VarOrderFirst = 0;
}

mergesort_var_order ()
{
  int i, s=1;
  FILE *f;
  
  /*
  f = fopen("array", "a");
  fprintf(f, "%d", VarOrderSize);
  for (i = 0; i < VarOrderSize; i++) {
    fprintf(f, " %d %d", VarOrder[i], weight(VarOrder[i]));
  }
  fprintf(f, "\n");
  fclose(f);
  */

  while (s < VarOrderSize) {
    s = s<<1;
    for (i = 0; i < VarOrderSize; i += s) {
      mergesorted(i, s);
    }
  }

  /*
  if (not_sorted(0, VarOrderSize)) { printf("not sorted\n"); }
  else printf("sorted\n");
  */

  VarOrderFirst = 0;
  for (i = 0; i < VarOrderSize; i++) {
    var_order(VarOrder[i]) = i;    
    /* printf("W%d = %d %d\n", VarOrder[i], L5[VarOrder[i]<<1]->weight,
       L5[(VarOrder[i]<<1)+1]->weight); */
  }
}

int B[MAX_SHORT];
mergesorted (p, s)
     int p, s;
{
  int r, x, y;

  if (s == 2) {
    r = p+1;
    if (r >= VarOrderSize) return 0;
    x = VarOrder[p];
    y = VarOrder[r];
    if (weight(x) < weight(y)) {
      VarOrder[p] = y;
      VarOrder[r] = x;
    }
  } else {
    int q = p+(s>>1);
    int i;
    r = p+s;

    if (r >= VarOrderSize) {
      r = VarOrderSize; 
      if (r <= q) return 0;
    }

    x = VarOrder[--q]; y = VarOrder[--r];
    while (q < r && weight(x) >= weight(y)) { y = VarOrder[--r]; }
    if (q < r) {
      s = 0; i = q+1;
      while (i < r) B[s++] = VarOrder[i++];
      while (1) {
	if (weight(x) < weight(y)) {
	  VarOrder[r--] = x;
	  if (q == p) { B[s++] = y; break; }
	  x = VarOrder[--q];
	} else {
	  VarOrder[r--] = y;
	  if (s == 0) break;
	  y = B[--s];
	}
      }
      while (s) VarOrder[r--] = B[--s];
    }
  }
}

#ifdef NONDISCARD
mergesorted (p, s)
     int p, s;
{
  int r = p+s;
  int x, y;

  /*printf("%d, %d\n", p, r);*/

  if (s == 2) {
    if (r > VarOrderSize) return 0;
    x = VarOrder[p];
    y = VarOrder[r=p+1];
    if (weight(x) < weight(y)) {
      VarOrder[r] = x;
      VarOrder[p] = y;
    }
  } else {
    int m = p+(s>>1);
    int q = 0, i, j;

    if (m >= VarOrderSize) return 0;
    if (r > VarOrderSize) r = VarOrderSize; 

    x = VarOrder[p]; y = VarOrder[m];
    while (weight(x) >= weight(y) && p < m) { x = VarOrder[++p]; }

    i = p; j = m;
    while (i < m && j < r) {
      if (weight(x) < weight(y)) {
	A[q++] = y;
	y = VarOrder[++j];
      } else {
	A[q++] = x;
	x = VarOrder[++i];
      }
    }
    while (i < m) A[q++] = VarOrder[i++];
    for (i = 0; i < q; i++) VarOrder[p+i] = A[i];
  }
}

not_sorted (p, r)
     int p, r;
{
  int i;
  for (i = p+1; i < r; i++) if (weight(VarOrder[i-1]) < weight(VarOrder[i])) {
    printf("W%d = %d, W%d = %d\n", 
	   VarOrder[i-1], weight(VarOrder[i-1]),
	   VarOrder[i], weight(VarOrder[i]));
    return 1;
  }
  return 0;
}

bubblesort_var_order ()
{
  int i0=0, i, bubble=1, k=VarOrderSize-1, x, y;

  /* bubble sort */
  while (bubble < VarOrderSize) {
    bubble = VarOrderSize;
    x = VarOrder[i0];
    for (i = i0; i < k; i++) {
      y = VarOrder[i+1];
      if (weight(x) < weight(y)) {
	if (bubble > i) { bubble = i; }
	VarOrder[i] = y;
	VarOrder[i+1] = x;
      } else {
	x = y;
      }
    }
    k--;
    i0 = (bubble)? bubble-1 : bubble;
  }

  VarOrderFirst = 0;
  for (i = 0; i < VarOrderSize; i++) {
    var_order(VarOrder[i]) = i;    
    /* printf("W(x%d) = %d\n", VarOrder[i], weight(VarOrder[i]));*/
  }
}

quicksort (p, r)
     int p, r;
{
  int q = partition(p, r);
  /* printf("[%d %d]", p, r); */
  if (p < q) quicksort(p, q);
  if (q+1 < r) quicksort(q+1, r);
}

partition (p, r)
     int p, r;
{
  int i = p;
  int j = r;
  int x = weight(VarOrder[(p+r)>>1]);

  while (1) {
    while (weight(VarOrder[i]) > x) i++;
    while (weight(VarOrder[j]) < x) j--;
    if (i < j) {
      int y = VarOrder[i];
      VarOrder[i++] = VarOrder[j];
      VarOrder[j--] = y;
    } else
      return j;
  }
}
#endif

