/*********************************************************************
; Copyright 1992-99, The University of Iowa (UI).  All rights reserved. 
; By using this software the USER indicates that he or she has read, 
; understood and will comply with the following:
;
; --- UI hereby grants USER nonexclusive permission to use, copy and/or
; modify this software for internal, noncommercial, research purposes only.
; Any distribution, including commercial sale or license, of this software,
; copies of the software, its associated documentation and/or modifications
; of either is strictly prohibited without the prior consent of UI.  Title
; to copyright to this software and its associated documentation shall at
; all times remain with UI.  Appropriate copyright notice shall be placed
; on all software copies, and a complete copy of this notice shall be
; included in all copies of the associated documentation.  No right is
; granted to use in advertising, publicity or otherwise any trademark,
; service mark, or the name of UI.  Software and/or its associated
; documentation identified as "confidential," if any, will be protected
; from unauthorized use/disclosure with the same degree of care USER
; regularly employs to safeguard its own such information.
;
; --- This software and any associated documentation is provided "as is," and
; UI MAKES NO REPRESENTATIONS OR WARRANTIES, EXPRESS OR IMPLIED, INCLUDING
; THOSE OF MERCHANTABILITY OR FITNESS FOR A PARTICULAR PURPOSE, OR THAT
; USE OF THE SOFTWARE, MODIFICATIONS, OR ASSOCIATED DOCUMENTATION WILL
; NOT INFRINGE ANY PATENTS, COPYRIGHTS, TRADEMARKS OR OTHER INTELLECTUAL
; PROPERTY RIGHTS OF A THIRD PARTY.  UI, the University of Iowa,
; its Regents, officers, and employees shall not be liable under any
; circumstances for any direct, indirect, special, incidental, or
; consequential damages with respect to any claim by USER or any third
; party on account of or arising from the use, or inability to use, this
; software or its associated documentation, even if UI has been advised
; of the possibility of those damages.
*********************************************************************/
#include "main.h"

GLOB SATOINT ABG_f[MAX_ABG_SIZE][MAX_ABG_SIZE];
GLOB SATOINT ABG_g[MAX_ABG_SIZE];
GLOB int Lsquare[MAX_SQUARE1][MAX_SQUARE1];

/* SIGMA(x,y,z) means the entry at row x and column y is z */
#define SIGMA2(i,j,k) (((((i-row_offset) * c) + (j)) * QGROUP) + k + 3)
#define SIGMA(i,j,k) ((Oarray[i][j] == UNKNOW)? \
		      SIGMA2(i,j,k) : \
		      (Oarray[i][j] == k)? 1 : 2)
#define set_entry0(i,j,k) Oarray[i][j] = k
#define set_entry(i,j,k) if (insert_cl_1(SIGMA(i, j, k), 1)) { bug(1); return 1; } \
                         Oarray[i][j] = k
/* DELTA(r1,r2,c1,z,a), where r1 > r2,  means z is covered at column c1 */
#define DELTA(r1,r2,c1,z,a) (((((((r1-alpha) * (r-1)) + (r2-beta)) * c) + (c1)) * (max_seed+1) + (z)) * Addk + (a) + rcn)

#define MULTI ZOOM
#define MAX_ROW 9
#define MAX_COL 50
#define DIFF(x,y) (ABG_f[ABG_g[y]][x])
#define HOLE -2
#define UNKNOW -1
#define Major_cols Oarray[MAX_ROW-1]

int Seed[MAX_ABG_SIZE];
int Mext[MAX_ABG_SIZE];
int Reps[MAX_ABG_SIZE];
int We[MAX_ROW];

int Oarray[MAX_ROW][MAX_COL];
#define expanding Oarray[MAX_ROW-2]
int expand_col, EXPAND = 0;
int row_offset = 2; /* either 1 or 2 */

extern int m;
int r, c, rcn, max_seed, shift30;
int free_infinity = 0;

int alpha = 2;
int beta = 0;
int Addk = 1;
void set_addk(x) int x; { Addk  = x; }
int get_addk() { return Addk; }

void init_oarray()
{
  m = QGROUP-INCOMPLETE;
  gen_abg_table();
  init_same_hole();
  if (RAMSEY>0) cqg_locate_holes();

  if (RAMSEY) {
    NHOLE = m/RAMSEY;
    if (m % RAMSEY != 0) {
      printf("Hole size %d does not divide %d - %d.\n", 
	     RAMSEY, QGROUP, INCOMPLETE);
      exit(0);
    }
  } else if (IDEMPOTENT) { RAMSEY = 1;
  } else RAMSEY = 0;

  if (m % Addk) {
    printf("Group size %d is not divisiable by %d.\n", 
	   m, Addk);
    exit(0);
  }

  printf("m = %d, MULTI = %d, INCOMPLETE = %d\n",
	  m, MULTI, INCOMPLETE);


  if (QUEEN == 30) {
    MULTI = 2;
    fix_seed_minus1();
    print_mext_reps();
    max_seed = m-1;
    if (QUEEN == 30 && RESTRICT > 79 && RESTRICT < 200) {
      row_offset = 1;
      RESTRICT %= 100;
    }
  } else if (MULTI == 0) { 
    fix_seed_zero();
  } else {

    if (INCOMPLETE % MULTI != 0) {
      printf("Multiplier %d does not divide %d.\n", MULTI, INCOMPLETE);
      exit(0);
    }
    if ((QGROUP - RAMSEY) % MULTI != 0) {
      printf("Multiplier %d does not divide %d - %d.\n", 
	     MULTI, QGROUP-INCOMPLETE, RAMSEY);
      exit(0);
    }

    if (fopen("oa.spe", "r") != NULL) 
      max_seed = read_special_seed();
    else {
      max_seed = fix_seed();
      if (max_seed == 0) exit(0);
    }
    print_mext_reps();
  }

  if (QUEEN == 31) {
    MULTI *= 2;
    beta = 1;
  }

  r = OARRAY+2;
  if (r > MAX_ROW) {
    printf("MAX_ROW (%d) is too small (< %d).\n", 
	   MAX_ROW, r);
    exit(0);
  }

  c = (QGROUP + INCOMPLETE - RAMSEY) / MULTI;

  if (QUEEN == 30 && (!IDEMPOTENT || INCOMPLETE % 2)) c++;

  if ((r * (INCOMPLETE / MULTI)) > c) {
    printf("Not enough cells for infinities: %d * (%d / %d) > %d.\n", 
	   r, INCOMPLETE, MULTI, c);
    exit(0);
  }

  if (QUEEN == 40) { row_offset = 1; c = c >> 1; }

  if (FLAG >= 3000 && FLAG < 10000) set_expanding(FLAG/1000);

  if (Addk < 1 || Addk > 9) { printf("Addk = %d ?\n", Addk); exit(0); }
  c *= Addk;
  if (c > MAX_COL) {
    printf("MAX_COL (%d) is too small (< %d).\n", 
	   MAX_COL, c);
    exit(0);
  }

  rcn = (r-row_offset) * c * QGROUP + 3;
  if (QUEEN == 40)
    Max_atom = DELTA(4,2,1,max_seed, Addk-1);
  else
    Max_atom = DELTA(r-1,r-2,c-1,max_seed, Addk-1);

  if (TRACE == 5) print_oa_encoding();
}

cgroup_find_seed ()
{
  if (MULTI > 0) { 
    printf("m = %d, MULTI = %d, INCOMPLETE = %d\n",
	   m, MULTI, INCOMPLETE);
    if (RAMSEY==0 && IDEMPOTENT) { RAMSEY = 1; }
    if (RAMSEY) { NHOLE=m/RAMSEY; }

    if (INCOMPLETE % MULTI != 0) {
      printf("Multiplier %d does not divide %d.\n", MULTI, INCOMPLETE);
      exit(0);
    }
    if ((QGROUP - RAMSEY) % MULTI != 0) {
      printf("Multiplier %d does not divide %d - %d.\nI set it to 2\n", 
	     MULTI, QGROUP-INCOMPLETE, RAMSEY);
      MULTI = 2;
      fix_seed_minus1();
      Seed[m/2] = HOLE;
      print_mext_reps();
      max_seed = m-1;
      return (0);
    }

    if (fopen("oa.spe", "r") != NULL) 
      max_seed = read_special_seed();
    else {
      max_seed = fix_seed();
      if (max_seed == 0) exit(0);
    }
    print_mext_reps();
    printf("max_seed = %d\n", max_seed);
  }
  return 1;
}

cgroup_seed_cls (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
{
  if (MULTI > 0) { 
    int x, y, z;
    int u = 1;
    if (LINE != 20) u = LINE;

    for (x = m-u; x >= 0; x--) if (Seed[x] >= 0)
      for (y = m-u; y >= 0; y--) if (Seed[y] >= 0)
	for (z = m-u; z >= 0; z--) if (Seed[z] >= 0) {
	  if (insert_cl_2(TRIPLE2KEY(x, y, z), 
			  TRIPLE2KEY(Mext[x], Mext[y], Mext[z]), 
			  TT, cl_arr, sign_arr))
	    return 1;
	}
  }
  return 0;
}

void print_oa_encoding ()
{
  int i, j, k, i2, a;

  for (i = row_offset; i < r; i++)
    for (j = 0; j < c; j++)
      for (k = 0; k < QGROUP; k++)
	printf("SIGMA(%d, %d, %d) = %d\n", i, j, k, SIGMA2(i,j,k));

  for (i = 2; i < r; i++) 
    for (i2 = 0; i2 < i; i2++)
      for (j = 0; j < c; j++)
	for (k = 0; k <= max_seed; k++)
	  for (a = 0; a < Addk; a++) {
	    printf("DELTA(%d, %d, %d, %d, %d) = %d\n", 
		   i, i2, j, k, a,
		   DELTA(i, i2, j, k, a));
	  }
}

void set_expanding(k)
     int k;
{
  int i, j;
  
  EXPAND = k;
  row_offset = 1;
  fix_remainder(k);
  for (i = 0; i < EXPAND; i++) printf("We[%d] = %d  ", i, We[i]);
  printf("\n");

  k = INCOMPLETE/MULTI;
  if (k % EXPAND) { printf("%d doesn't divide %d\n", k, EXPAND); exit(0); }
  i = k/EXPAND;
  expand_col = i * r;
  j = r*i*(EXPAND - 1); /* saved columns from infinities */
  i = (c - k * r)/EXPAND;
  expand_col += i;
  j += i*(EXPAND - 1); /* plus those saved from noninfinities */
  printf("Expanding the first %d columns by %d with multiplier %d\n", 
	 expand_col, EXPAND, We[1]);
  printf("Reducing the original %d columns to %d\n", c, c-j);
  if ((EXPAND-1) * expand_col != j) bug();
  c -= j;
}


void print_mext_reps ()
{ 
  int i, j;

  printf("M_next and Representives:\n  ");

  for (j = 0; j < m; j += 20) {
    printf("\n  x : ");
    for (i = j; i < m && i < j+20; i++) printf(" %2d", i);
    printf("\nn(x): ");
    for (i = j; i < m && i < j+20; i++) printf(" %2d", Mext[i]);
    printf("\ns(x): ");
    for (i = j; i < m && i < j+20; i++) printf(" %2d", Seed[i]);
    printf("\nr(x): ");
    for (i = j; i < m && i < j+20; i++) printf(" %2d", Reps[i]);
    printf("\n");
  }

  printf("\nsubgroup H = { 0");
  for (i = 1; i < m; i++) if (Seed[i] == HOLE) printf(", %d", i);
  printf(" }\ninfinity elements X = { ");
  if (QUEEN == 30) 
    for (i = 1; i <= INCOMPLETE/2; i++) printf("x%d, y%d, ", i, i);
  else
    for (i = 1; i <= INCOMPLETE; i++) printf("x%d, ", i);
  printf("}\n\n");
}

void fix_seed_minus1()
{ 
  int i;
  max_seed = m/2;  
  Seed[m] = m-1;
  for (i = m/2; i >= 0; i--) {
    Reps[m-i] = Reps[i] = i;
    Mext[i] = m-i;
    Mext[m-i] = i;
    if (NHOLE == 0 || i % NHOLE != 0) Seed[m-i] = Seed[i] = i;
    else Seed[i] = Seed[m-i] = HOLE;
  }
  if (IDEMPOTENT) Seed[0] = HOLE;
}

void fix_seed_zero()
{ 
  int i;
  max_seed = m-1;  
  MULTI = 1; Seed[m] = 1;
  for (i = 0; i < m; i++) {
    Mext[i] = Reps[i] = i;
    if (NHOLE == 0 || i % NHOLE != 0) Seed[i] = i;
    else Seed[i] = HOLE;
  }
  if (IDEMPOTENT) Seed[0] = HOLE;
}

int fix_seed ()
{
  int s,i,j;

  if (NHOLE) for (i = 0; i < m; i += NHOLE) Seed[i] = HOLE;
  else if (IDEMPOTENT) Seed[0] = HOLE;

  for (s = (FORMAT > 22 && FORMAT < 200)? FORMAT-21 : 2; s < m; s++) 
    if (Seed[s] != HOLE) {
      j = s; 
      for (i = 1; i < MULTI; i++) { j *= s; j = j % m; }
      if (j == 1) {
	if ((j = fill_seed(s, MULTI)) > 0) return j;
      }
    }
  
  printf("No more solution for x^%d = 1 mod %d\n", MULTI, m);
  exit(1);
  return 0;
}

void fix_remainder (times)
     int times;
{
  int j, i, s;
  int seed[MAX_ABG_SIZE];

  if (NHOLE) for (i = 0; i < m; i += NHOLE) seed[i] = HOLE;
  else if (IDEMPOTENT) Seed[0] = HOLE;
  We[0] = 1;

  for (s = (FORMAT > 19 && FORMAT < 200)? FORMAT-10 : 2; s < m; s++) 
    if (seed[s] != HOLE) {
      j = s; 
      for (i = 1; i < times; i++) { We[i] = (j % m); j *= s; }
      if (j % m == 1) {
	printf("%d^%d = 1 mod %d\n", s, times, m);
	if (EXPAND) return;
	if (CREATE < 5 && RESTRICT >= 4000) { if (pmd_fill_seed(s)) return; }
	else if (pmd_fill_remainder(s, seed)) return;
      }
    }
  
  printf("No more solution for x^%d = 1 modulo %d\n", times, m);
  exit(0);
}

int fill_seed(s, times)
     int s;
{
  int i, j, max, bad = 0;

  Seed[m] = s;
  printf("%d^%d = 1 mod %d\n", s, times, m);
  for (i = 0; i < m; i++) if (Seed[i] != HOLE) Seed[i] = UNKNOW;

  max = Reps[0] = Mext[0] = 0;
  for (i = 1; i < m; i++) if (Seed[i] == UNKNOW) {
    int x = i;
    int y = i;
    Seed[x] = i;
    Reps[x] = ++max;
    if (TRACE > 1) printf("%d ", x);
    for (j = 1; j < times; j++) {
      x *= s;
      x %= m;
      if (x == i) {
	if (!bad || TRACE > 1) 
	  printf("bad number: %d*(%d^%d) = %d\n\n", x, s, j, x);
	bad++;
      } else if (Seed[x] != UNKNOW) {
	if (!bad || TRACE > 1) 
	  printf("bad number: Seed[%d] = %d != %d\n\n", x, Seed[x], i);
	bad++;
      }
      Mext[y] = x;
      y = x;
      Seed[x] = i;
      Reps[x] = max;
      if (TRACE > 1) printf("%d ", x); 
    }
    Mext[y] = i;
    if (TRACE > 1) printf("at %d\n", max); 
  }

  if (bad) { if (TRACE > 1) print_mext_reps(); return 0; }
  return (max);
}

int read_special_seed()
{
  FILE *f = fopen("oa.spe", "r");
  int i, j, max;

/* 
   Format of File oa.spe:
 
Groupsize  Subgroupsize  Parameter_of_-f  Num_of_multiplier
<Subgroup Elements>
<multiplier_table>
*/

  if (f == NULL) { printf("Cannot open oa.spe\n"); exit(0); }
  printf("Opening FILE 'oa.spe' for a special multiplier function\n");
  fscanf(f, "%d", &i);
  if (i != m) { printf("Abelian Group size %d is not %d\n", m, i); exit(0); }
  fscanf(f, "%d", &i);
  if (i != RAMSEY)
    { printf("Abelian Subgroup size %d is not %d\n", RAMSEY, i); exit(0); }
  fscanf(f, "%d", &i);
  if (i != get_num_of_hole()) 
    { printf("Abelian Group generator %d is not %d\n", get_num_of_hole(), i); exit(0); }
  fscanf(f, "%d", &i);
  if (i != MULTI) 
    { printf("Abelian Group multiple %d is not %d\n", MULTI, i); exit(0); }

  for (j = 0; j < RAMSEY; j++) {
    fscanf(f, "%d", &i);
    Seed[i] = HOLE;
  }

  for (j = 0; j < m; j++) {
    fscanf(f, "%d", &i);
    Mext[j] = i;
  }

  for (j = 0; j < m; j++) if (Seed[j] != HOLE) Seed[j] = UNKNOW;

  max = Reps[0] = Mext[0] = 0;
  for (i = 1; i < m; i++) if (Seed[i] == UNKNOW) {
    int x;
    Seed[i] = i;
    Reps[i] = ++max;
    printf("\n%d ", i);
    x = Mext[i];
    while (x != i) {
      Seed[x] = i;
      Reps[x] = max;
      printf("%d ", x);
      x = Mext[x];
    }
  }
  printf("\n");

  return (max);
}

int oarray_clauses()
{
  int cl_arr [ MAX_ATOM ], sign_arr [ MAX_ATOM ];

  Value[1] = TT;
  Value[2] = FF;
  if (OUTPUT) { 
    print_unit_clause(stdout, TT, 1);
    print_unit_clause(stdout, FF, 2);
  }

  free_infinity = RANDOM;
  /* set the first two rows and infinity elements */
  if (oarray_unit_cls()) return 1;
  print_oarray2(stdout);
  /*oarray_extra_cls(); */

  /* additional constraints on row 2. */
  if (oarray_row2_cls(cl_arr, sign_arr)) return 1;

  /* automorphism 
  if (FLAG > 1 && oarray_auto_cls(cl_arr, sign_arr)) return 1;
  */

  /* unique values */
  if (oarray_unique_cls(cl_arr, sign_arr)) return 1;

  /* difference conditions */
  if (EXPAND) {
    if (oarray_expand_cls(cl_arr, sign_arr)) return 1;
  } else if (QUEEN == 30) {
    if (oarray_diff_cls_30(cl_arr, sign_arr)) return 1;
    if (oarray_qg30(cl_arr, sign_arr)) return 1;
  } else if (QUEEN == 31) {
    if (oarray_diff_cls_31(cl_arr, sign_arr)) return 1;
  } else if (QUEEN == 40 && r == 5) {
    if (oarray_diff_cls_40(cl_arr, sign_arr)) return 1;
  } else {
    if (oarray_diff_cls(cl_arr, sign_arr)) return 1;
  }

  /* additional constraints */
  if (QUEEN) {
    if (QUEEN == 10) {
      if (oarray_trans(2, 3, cl_arr, sign_arr)) return 1;
    } else if (QUEEN == 11) {
      if (oarray_qg1(2, 3, cl_arr, sign_arr)) return 1;
    } else if (QUEEN == 12) {
      if (oarray_qg2(2, 3, cl_arr, sign_arr)) return 1;
    } else if (QUEEN == 20) {
      if (oarray_trans(2, 3, cl_arr, sign_arr)) return 1;
      if (oarray_trans(4, 4, cl_arr, sign_arr)) return 1;
      if (oarray_qg20(cl_arr, sign_arr)) return 1;
    } else if (QUEEN == 21) {
      if (oarray_trans(2, 3, cl_arr, sign_arr)) return 1;
      if (oarray_qg1(2, 4, cl_arr, sign_arr)) return 1;
    } else if (QUEEN == 22) {
      if (oarray_trans(2, 3, cl_arr, sign_arr)) return 1;
      if (oarray_qg2(2, 4, cl_arr, sign_arr)) return 1;
    } else if (QUEEN == 32) {
      if (oarray_qg1(2, 3, cl_arr, sign_arr)) return 1;
      if (oarray_qg2(2, 4, cl_arr, sign_arr)) return 1;
    }
  }

  /* available values */
  if (oarray_posi_cls(cl_arr, sign_arr)) return 1;

  return 0;
}

int oarray_unique_cls (cl_arr, sign_arr)
     int cl_arr[], sign_arr[];
     /* every cell has at most one value */
{
  int x, y, u, v, r1, r2, a;

  if (Addk > 1) {
    int ack = c/Addk;
    int k = INCOMPLETE/MULTI;
    for (a = 0; a < k+k; a++) 
      for (x = a; x < c-ack; x += ack)
	for (y = x+ack; y < c; y += ack)
	  for (r1 = 2; r1 < r; r1++) 
	    for (u = 0; u < m; u++) 
	      for (v = 0; v < m; v++) if (u % Addk == v % Addk) {
		if (insert_cl_2(SIGMA(r1, y, u), 
				SIGMA(r1, x, v), 
				FF, cl_arr, sign_arr)) return 1;
	      }

    for (a = k+k; a < ack; a++) 
      for (x = a; x < c-ack; x += ack) 
	for (y = x+ack-Addk; y < c; y++) if (Oarray[1][x] == Oarray[1][y])
	  for (r1 = 2; r1 < r; r1++) 
	    for (v = m; v < QGROUP; v++) {
	      if (insert_cl_2(SIGMA(r1, y, v), 
			      SIGMA(r1, x, v), 
			      FF, cl_arr, sign_arr)) return 1;
	    }
  }

  for (x = 0; x < r; x++) 
    for (y = 0; y < c; y++) 
      for (u = QGROUP-1; u >= 0; u--) 
	for (v = u-1; v >= 0; v--) {
	  /* x * y = u and x * y = v imply u = v. */
	  if (insert_cl_2(SIGMA(x, y, u), 
			  SIGMA(x, y, v), 
			  FF, cl_arr, sign_arr)) return 1;
	}

  /* r1 * x = u and r2 * x = v and u-v = 0 imply r1 = r2. */
  for (r1 = 2; r1 < r; r1++) 
    for (r2 = r1-1; r2 >= 0; r2--) 
      for (x = 0; x < c; x++) 
	for (u = 0; u < m; u++)
	  for (v = 0; v < m; v++) {
	    /* DIFF(u, v) is in H. */
	    y = DIFF(u, v);
	    if (Seed[y] == HOLE) {
	      if (insert_cl_2(SIGMA(r1, x, u), 
			      SIGMA(r2, x, v), 
			      FF, cl_arr, sign_arr)) return 1;
	    }
	  }

  /* r1 * x = u and r2 * x = v imply r1 = r2 for u, v >= m. */
  for (r1 = 2; r1 < r; r1++) 
    for (r2 = r1-1; r2 >= 0; r2--) 
      for (x = 0; x < c; x++) 
	for (u = m; u < m+INCOMPLETE/MULTI; u++) 
	  for (v = m; v < m+INCOMPLETE/MULTI; v++) {
	    if (insert_cl_2(SIGMA(r1, x, u), 
			    SIGMA(r2, x, v), 
			    FF, cl_arr, sign_arr)) return 1;
	  }

  for (a = 0; a < Addk; a++) {
    int cak = a*c/Addk+shift30;
    /* r1 * x = u and r1 * y = u imply x = y. */
    for (x = INCOMPLETE/MULTI; x < c/Addk; x++) 
      for (y = x+1; y < c/Addk; y++) 
      for (r1 = row_offset; r1 < r; r1++) 
	for (u = 1; u < QGROUP; u++) {
	  if (insert_cl_2(SIGMA(r1, x+cak, u), 
			  SIGMA(r1, y+cak, u), 
			  FF, cl_arr, sign_arr)) return 1;
	}
  }

  return 0;
}

int oarray_row2_cls (cl_arr, sign_arr)
     int cl_arr[], sign_arr[];
{
  int i, j, k, u, v, x, y;
  k = INCOMPLETE/MULTI;

  for (i = 0; i < k-1; i++)
    for (j = i+1; j < k; j++) 
      for (u = 2; u < m; u++)
	for (v = u-1; v > 0; v--) if (QUEEN < 20) {
	  if (insert_cl_2(SIGMA(2, i, u), 
			  SIGMA(2, j, v), 
			  FF, cl_arr, sign_arr)) return 1;

	  if (insert_cl_2(SIGMA(2, i+k, u), 
			  SIGMA(2, j+k, v), 
			  FF, cl_arr, sign_arr)) return 1;
	}

  if (INCOMPLETE && free_infinity && QUEEN < 20) {
    for (x = 2; x < r; x++)
      for (i = 2*k; i < c-1; i++)
	for (j = i+1; j < c; j++) 
	  for (u = m+1; u < m+k; u++)
	    for (v = u-1; v >= m; v--) {
	      if (insert_cl_2(SIGMA(x, i, u), 
			      SIGMA(x, j, v), 
			      FF, cl_arr, sign_arr)) return 1;
	    }
  }

  if (LINE >= 200 && LINE < 1000 && (LINE % 100 == 0)) {
    i = x = 0;
    u = LINE/100;
    v = (c - k)/u;
    for (j = 0; j < c; j++) if (Oarray[3][j] == UNKNOW) {
      printf("<3,%d> = ", j);
      for (y = 1; y < m; y++) if (y % u != x) {
	if (insert_cl_1(SIGMA(3, j, y), FF)) return 1;
      }
      if (++i == v) { 
	i = 0; 
	printf("%d mod %d\n", x, u);
	if (++x == u) x = 0; 
      }
    }
    if ((c-k)%u) printf("%d mod %d\n\n", x, u);
    else printf("\n");
  }

#ifdef MORE
  if (free_infinity && QUEEN < 20) {
    for (x = 2; x < r; x++)
      for (i = 2*k; i < c-1; i++)
	for (j = i+1; j < c; j++) 
	  for (u = m+1; u < m+k; u++)
	    for (v = u-1; v >= m; v--) {
	      if (insert_cl_2(SIGMA(x, i, u), 
			      SIGMA(x, j, v), 
			      FF, cl_arr, sign_arr)) return 1;
	    }

    if (INCOMPLETE)
      for (i = 2*k; i < c-1; i++)
	for (j = i+1; j < c; j++) 
	  for (u = 2; u < r-1; u++) {
	    if (insert_cl_2(SIGMA(u, j, m), 
			    SIGMA(u+1, i, m), 
			    FF, cl_arr, sign_arr)) return 1;
	  }
  }
#endif

  return 0;
}

int oarray_posi_cls (cl_arr, sign_arr)
     int cl_arr[], sign_arr[];
  /* every cell must have a value */
{
  int i, j, k, u, v;
  k = INCOMPLETE/MULTI;

  for (i = row_offset; i < r; i++) 
    for (j = 0; j < c; j++) 
      if (Oarray[i][j] < 0) {
	v = 0;
	if (j < k+k+shift30) {
	  for (u = m-1; u >= 0; u--) {
	    cl_arr[v] = SIGMA2(i, j, u);
	    sign_arr[cl_arr[v++]] = 1;
	  }
	} else if (free_infinity == 0) {
	  if (QUEEN == 30 && shift30 && IDEMPOTENT  && (i == 2 || i == 4)) {
	    cl_arr[v] = SIGMA2(i, j, QGROUP-1);
	    sign_arr[cl_arr[v++]] = 1;
	  }
	  for (u = m-1; u >= 0; u--) {
	    cl_arr[v] = SIGMA2(i, j, u);
	    sign_arr[cl_arr[v++]] = 1;
	  }
	} else {
	  if (QUEEN == 30 && shift30 && IDEMPOTENT  && (i == 2 || i == 4)) {
	    cl_arr[v] = SIGMA2(i, j, QGROUP-1);
	    sign_arr[cl_arr[v++]] = 1;
	  }
	  for (u = m+k-1; u >= 0; u--) {
	    cl_arr[v] = SIGMA2(i, j, u);
	    sign_arr[cl_arr[v++]] = 1;
	  }
	}
	Clause_num++;
	if (insert_clause ( cl_arr, sign_arr, v) == 1)	return 1;
      }
  return 0;
}

int oarray_diff_cls (cl_arr, sign_arr)
     int cl_arr[], sign_arr[];
{
  int a, x, y, u, v, r1, r2;

  for (r1 = 2; r1 < r; r1++) 
    for (r2 = 0; r2 < r1; r2++) 
      for (x = 0; x < c; x++) 
	for (u = 0; u < m; u++)
	  for (v = 0; v < m; v++) {

	    y = DIFF(u, v);

	    if (Seed[y] != HOLE) {

	      /* DIFF(u, v) is not in H. */
	      if (insert_cl_all_3(SIGMA(r1, x, u), 
				  SIGMA(r2, x, v), 
				  DELTA(r1, r2, x, Reps[y], u%Addk),
				  TT, cl_arr, sign_arr)) return 1;
	    }
	  }

  /* unique covering */
  for (r1 = 2; r1 < r; r1++) 
    for (r2 = r1-1; r2 >= 0; r2--) 
      for (x = 0; x <= max_seed; x++) 
	for (u = 1; u < c; u++) 
	  for (v = u-1; v >= 0; v--) 
	    for (a = 0; a < Addk; a++) {
	    /* delta(r1, r2, u, x, a) and delta(r1, r2, v, x, a) => u = v */
	    if (insert_cl_2(DELTA(r1, r2, u, x, a), 
			    DELTA(r1, r2, v, x, a), 
			    FF, cl_arr, sign_arr)) return 1;
	  }

  return 0;
}

int oarray_diff_cls_40 (cl_arr, sign_arr)
     int cl_arr[], sign_arr[];
{
  int a, x, y, u, v, r1, r2;

  if (LINE >= 5000) {
    oa_read_square();
    for (x = 0; x < QGROUP; x++)
      for (y = 0; y < QGROUP; y++) 
	for (u = 0; u < c; u++) {
	  if ((Lsquare[x][y] >= 0) &&
	      insert_cl_all_3(SIGMA(1, u, x), 
			      SIGMA(2, u, y), 
			      SIGMA(3, u, Lsquare[x][y]), 
			      TT, cl_arr, sign_arr)) return 1;

	  if ((Lsquare[y][x] >= 0) &&
	      insert_cl_all_3(SIGMA(1, u, x), 
			      SIGMA(2, u, y), 
			      SIGMA(4, u, Lsquare[y][x]), 
			      TT, cl_arr, sign_arr)) return 1;

	}
  }

  for (x = 0; x < INCOMPLETE/2; x++)
    for (u = 0; u < m; u++) 
      for (v = 0; v < m; v++) {
	y = DIFF(u, v);
	if ((y & 1) == 0) {
	  if (insert_cl_2(SIGMA(4, x, u), 
			  SIGMA(3, x, v), 
			  FF, cl_arr, sign_arr)) return 1;
	}
      }

  for (x = 0; x < c; x++) 
    for (u = 0; u < m; u++)
      for (v = 0; v < m; v++) {
	y = DIFF(u, v);
	if (Seed[y] != HOLE) { /* DIFF(u, v) is not in H. */

	  /* <2, 0> takes <a, b> and <a, c> in (a, b, c, d, e) */
	  if (insert_cl_all_3(SIGMA(1, x, u), 
			      SIGMA(0, x, v), 
			      DELTA(2, 0, x, Reps[y], u%Addk),
			      TT, cl_arr, sign_arr)) return 1;
	  if (insert_cl_all_3(SIGMA(2, x, u), 
			      SIGMA(0, x, v), 
			      DELTA(2, 0, x, Reps[y], u%Addk),
			      TT, cl_arr, sign_arr)) return 1;

	  /* <2, 1> takes <a, d> and <a, e> in (a, b, c, d, e) */
	  if (insert_cl_all_3(SIGMA(3, x, u), 
			      SIGMA(0, x, v), 
			      DELTA(2, 1, x, Reps[y], u%Addk),
			      TT, cl_arr, sign_arr)) return 1;
	  if (insert_cl_all_3(SIGMA(4, x, u), 
			      SIGMA(0, x, v), 
			      DELTA(2, 1, x, Reps[y], u%Addk),
			      TT, cl_arr, sign_arr)) return 1;

	  /* <3, 0> takes <b, c> and <c, b> in (a, b, c, d, e) */
	  if (insert_cl_all_3(SIGMA(2, x, u), 
			      SIGMA(1, x, v), 
			      DELTA(3, 0, x, Reps[y], u%Addk),
			      TT, cl_arr, sign_arr)) return 1;
	  if (insert_cl_all_3(SIGMA(1, x, u), 
			      SIGMA(2, x, v), 
			      DELTA(3, 0, x, Reps[y], u%Addk),
			      TT, cl_arr, sign_arr)) return 1;

	  /* <3, 2> takes <d, e> and <e, d> in (a, b, c, d, e) */
	  if (insert_cl_all_3(SIGMA(4, x, u), 
			      SIGMA(3, x, v), 
			      DELTA(3, 2, x, Reps[y], u%Addk),
			      TT, cl_arr, sign_arr)) return 1;
	  if (insert_cl_all_3(SIGMA(3, x, u), 
			      SIGMA(4, x, v), 
			      DELTA(3, 2, x, Reps[y], u%Addk),
			      TT, cl_arr, sign_arr)) return 1;

	  /* <3, 1> takes <b, d> and <c, e> in (a, b, c, d, e) */
	  if (insert_cl_all_3(SIGMA(1, x, u), 
			      SIGMA(3, x, v), 
			      DELTA(3, 1, x, Reps[y], u%Addk),
			      TT, cl_arr, sign_arr)) return 1;
	  if (insert_cl_all_3(SIGMA(1, x, u), 
			      SIGMA(3, x, v), 
			      DELTA(4, 1, 0, Reps[y], u%Addk),
			      TT, cl_arr, sign_arr)) return 1;

	  if (insert_cl_all_3(SIGMA(2, x, u), 
			      SIGMA(4, x, v), 
			      DELTA(3, 1, x, Reps[y], u%Addk),
			      TT, cl_arr, sign_arr)) return 1;
	  if (insert_cl_all_3(SIGMA(2, x, u), 
			      SIGMA(4, x, v), 
			      DELTA(4, 1, 1, Reps[y], u%Addk),
			      TT, cl_arr, sign_arr)) return 1;

	  /* <4, 0> takes <b, e> and <c, d> in (a, b, c, d, e) */
	  if (insert_cl_all_3(SIGMA(1, x, u), 
			      SIGMA(4, x, v), 
			      DELTA(4, 0, x, Reps[y], u%Addk),
			      TT, cl_arr, sign_arr)) return 1;
	  if (insert_cl_all_3(SIGMA(1, x, u), 
			      SIGMA(4, x, v), 
			      DELTA(4, 2, 0, Reps[y], u%Addk),
			      TT, cl_arr, sign_arr)) return 1;

	  if (insert_cl_all_3(SIGMA(2, x, u), 
			      SIGMA(3, x, v), 
			      DELTA(4, 0, x, Reps[y], u%Addk),
			      TT, cl_arr, sign_arr)) return 1;
	  if (insert_cl_all_3(SIGMA(2, x, u), 
			      SIGMA(3, x, v), 
			      DELTA(4, 2, 1, Reps[y], u%Addk),
			      TT, cl_arr, sign_arr)) return 1;

	} else {
	  /* <a, b> and <a, c> in (a, b, c, d, e) */
	  if (insert_cl_2(SIGMA(1, x, u), 
			  SIGMA(2, x, v), 
			  FF, cl_arr, sign_arr)) return 1;

	  /* <a, d> and <a, e> in (a, b, c, d, e) */
	  if (insert_cl_2(SIGMA(3, x, u), 
			  SIGMA(4, x, v), 
			  FF, cl_arr, sign_arr)) return 1;
	}
      }

  /* unique covering */
  for (r1 = r-1; r1 >= 2; r1--) 
    for (r2 = 0; r2 < r1; r2++) {
      for (x = 0; x <= max_seed; x++) 
	for (u = 1; u < c; u++) {
	  for (v = u-1; v >= 0; v--) 
	    for (a = 0; a < Addk; a++) {
	      /* delta(r1, r2, u, x, a) and delta(r1, r2, v, x, a) => u = v */
	      if (insert_cl_2(DELTA(r1, r2, u, x, a), 
			      DELTA(r1, r2, v, x, a), 
			      FF, cl_arr, sign_arr)) return 1;
	    }
	  if (r1 == 4 && r2) u = c;
	}
      if (r1 == 4 && r2 == 2) r2 = r1;
    }

  return 0;
}

int oarray_diff_cls_30 (cl_arr, sign_arr)
     int cl_arr[], sign_arr[];
{
  int a, x, y, u, v, r1, r2;
  int k = INCOMPLETE/2;

  /* handle <0, 1> = <0, 2>, <0, 3> = <0, 4> */
  for (r1 = 2; r1 < 5; r1 += 2) 
    for (x = 0; x < c; x++) 
      for (u = 0; u < m; u++) {

	if (!IDEMPOTENT && x >= k &&
	    insert_cl_2(SIGMA(r1, x, u), 
			SIGMA(r1-1, x, u), 
			FF, cl_arr, sign_arr)) return 1;

	for (v = 0; v < m; v++) {

	  y = DIFF(u, v);

	  if (Seed[y] != HOLE) { /* DIFF(u, v) is not in H. */

	    if (insert_cl_all_3(SIGMA(r1, x, u), 
				SIGMA(0, x, v), 
				DELTA(r1, 0, x, y, u%Addk),
				TT, cl_arr, sign_arr)) return 1;

	    if (insert_cl_all_3(SIGMA(r1-1, x, u), 
				SIGMA(0, x, v), 
				DELTA(r1, 0, x, y, u%Addk),
				TT, cl_arr, sign_arr)) return 1;

	  }
	}
      }

  /* handle <1, 2>, <3, 4> */
  for (r2 = 1; r2 < 4; r2 += 2) {
    r1 = r2+1;
    for (x = 0; x < c; x++) 
      for (u = 0; u < m; u++)
	for (v = 0; v < m; v++) {

	  y = DIFF(u, v);

	  if (Seed[y] != HOLE) { /* DIFF(u, v) is not in H. */
	    if (insert_cl_all_3(SIGMA(r1, x, u), 
				SIGMA(r2, x, v), 
				DELTA(r1, r2, x, Reps[y], u%Addk),
				TT, cl_arr, sign_arr)) return 1;
	  }
	}
  }

  /* handle <1, 3> = <2, 4>, <1, 4> = <2, 3> */
  r1 = 3; r2 = 1;
  for (x = 0; x < c; x++) 
    for (u = 0; u < m; u++) 
      for (v = 0; v < m; v++) {

	y = DIFF(u, v);

	if (Seed[y] != HOLE) { /* DIFF(u, v) is not in H. */
	  if (insert_cl_all_3(SIGMA(3, x, u), 
			      SIGMA(1, x, v), 
			      DELTA(3, 1, x, y, u%Addk),
			      TT, cl_arr, sign_arr)) return 1;

	  if (insert_cl_all_3(SIGMA(4, x, u), 
			      SIGMA(2, x, v), 
			      DELTA(3, 1, x, y, u%Addk),
			      TT, cl_arr, sign_arr)) return 1;

	  if (insert_cl_all_3(SIGMA(4, x, u), 
			      SIGMA(2, x, v), 
			      DELTA(4, 2, x, y, u%Addk),
			      TT, cl_arr, sign_arr)) return 1;

	  if ((x >= shift30) &&
	      (x > shift30 || Oarray[2][shift30] != m/2) &&
	      insert_cl_all_3(SIGMA(3, x, u), 
			      SIGMA(1, x, v), 
			      DELTA(4, 2, x, y, u%Addk),
			      FF, cl_arr, sign_arr)) return 1;

	  if (insert_cl_all_3(SIGMA(3, x, u), 
			      SIGMA(2, x, v), 
			      DELTA(4, 1, x, y, u%Addk),
			      TT, cl_arr, sign_arr)) return 1;

	  if (insert_cl_all_3(SIGMA(4, x, u), 
			      SIGMA(1, x, v), 
			      DELTA(4, 1, x, y, u%Addk),
			      TT, cl_arr, sign_arr)) return 1;

	  if (insert_cl_all_3(SIGMA(3, x, u), 
			      SIGMA(2, x, v), 
			      DELTA(3, 2, x, y, u%Addk),
			      TT, cl_arr, sign_arr)) return 1;

	  if ((x >= shift30) && 
	      (x > shift30 || Oarray[2][shift30] != m/2) &&
	      insert_cl_all_3(SIGMA(4, x, u), 
			      SIGMA(1, x, v), 
			      DELTA(3, 2, x, y, u%Addk),
			      FF, cl_arr, sign_arr)) return 1;
	}
      }

  /* unique covering */
  for (r1 = 2; r1 < r; r1++) 
    for (r2 = r1-1; r2 >= 0; r2--) if (r1 == 2 || (r1 == 3 && r2 == 1) ||
				       (r1 == 4 && r2 != 2))
      for (x = 0; x < m; x++) 
	for (u = 1; u < c; u++) 
	  for (v = u-1; v >= 0; v--) 
	    for (a = 0; a < Addk; a++) {
	    /* delta(r1, r2, u, x, a) and delta(r1, r2, v, x, a) => u = v */
	    if (insert_cl_2(DELTA(r1, r2, u, x, a), 
			    DELTA(r1, r2, v, x, a), 
			    FF, cl_arr, sign_arr)) return 1;
	  }

  return 0;
}

int oarray_diff_cls_31 (cl_arr, sign_arr)
     int cl_arr[], sign_arr[];
{
  int a, x, y, u, v, r1, r2;
  int k = INCOMPLETE/2;

  /* handle <0, 4> = <1, 4>, <2, 4> = <3, 4> */
  for (r1 = 1; r1 < 4; r1 += 2) 
    for (x = 0; x < c; x++) 
      for (u = 0; u < m; u++) {

	if (!IDEMPOTENT && x >= k &&
	    insert_cl_2(SIGMA(r1, x, u), 
			SIGMA(r1-1, x, u), 
			FF, cl_arr, sign_arr)) return 1;

	for (v = 0; v < m; v++) {

	  y = DIFF(u, v);

	  if (Seed[y] != HOLE) { /* DIFF(u, v) is not in H. */

	    if (insert_cl_all_3(SIGMA(4, x, u), 
				SIGMA(r1, x, v), 
				DELTA(4, r1, x, y, u%Addk),
				TT, cl_arr, sign_arr)) return 1;

	    if (insert_cl_all_3(SIGMA(4, x, u), 
				SIGMA(r1-1, x, v), 
				DELTA(4, r1, x, y, u%Addk),
				TT, cl_arr, sign_arr)) return 1;

	  }
	}
      }

  /* handle <0, 1> (done), <2, 3> */
  for (x = 0; x < c; x++) 
    for (u = 0; u < m; u++)
      for (v = 0; v < m; v++) {

	y = DIFF(u, v);

	if (Seed[y] != HOLE) { /* DIFF(u, v) is not in H. */
	  if (insert_cl_all_3(SIGMA(3, x, u), 
			      SIGMA(2, x, v), 
			      DELTA(3, 2, x, (y > m/2)? m-y : y, u%Addk),
			      TT, cl_arr, sign_arr)) return 1;
	}
      }

  /* handle <1, 3> = <0, 2>, <0, 3> = <1, 2> */
  for (x = 0; x < c; x++) 
    for (u = 0; u < m; u++) 
      for (v = 0; v < m; v++) {

	y = DIFF(u, v);

	if (Seed[y] != HOLE) { /* DIFF(u, v) is not in H. */
	  if (insert_cl_all_3(SIGMA(2, x, u), 
			      SIGMA(0, x, v), 
			      DELTA(3, 1, x, y, u%Addk),
			      TT, cl_arr, sign_arr)) return 1;
	  if (insert_cl_all_3(SIGMA(2, x, u), 
			      SIGMA(0, x, v), 
			      DELTA(2, 1, 2, y, u%Addk),
			      TT, cl_arr, sign_arr)) return 1;

	  if (insert_cl_all_3(SIGMA(3, x, u), 
			      SIGMA(1, x, v), 
			      DELTA(3, 1, x, y, u%Addk),
			      TT, cl_arr, sign_arr)) return 1;
	  if (insert_cl_all_3(SIGMA(3, x, u), 
			      SIGMA(1, x, v), 
			      DELTA(2, 1, 3, y, u%Addk),
			      TT, cl_arr, sign_arr)) return 1;

	  if (insert_cl_all_3(SIGMA(3, x, u), 
			      SIGMA(0, x, v), 
			      DELTA(4, 2, x, y, u%Addk),
			      TT, cl_arr, sign_arr)) return 1;
	  if (insert_cl_all_3(SIGMA(3, x, u), 
			      SIGMA(0, x, v), 
			      DELTA(2, 1, 0, y, u%Addk),
			      TT, cl_arr, sign_arr)) return 1;

	  if (insert_cl_all_3(SIGMA(2, x, u), 
			      SIGMA(1, x, v), 
			      DELTA(4, 2, x, y, u%Addk),
			      TT, cl_arr, sign_arr)) return 1;
	  if (insert_cl_all_3(SIGMA(2, x, u), 
			      SIGMA(1, x, v), 
			      DELTA(2, 1, 1, y, u%Addk),
			      TT, cl_arr, sign_arr)) return 1;

	  /*
	  for (r1 = 0; r1 < m; r1++) {
	      if (insert_cl_4(SIGMA(2, x, u), 
			      SIGMA(0, x, v), 
			      SIGMA(3, x, r1), 
			      SIGMA(1, x, DIFF(r1, y)), 
			      FF, cl_arr, sign_arr)) return 1;

	      if (insert_cl_4(SIGMA(3, x, u), 
			      SIGMA(0, x, v), 
			      SIGMA(2, x, r1), 
			      SIGMA(1, x, DIFF(r1, y)), 
			      FF, cl_arr, sign_arr)) return 1;
	  } */
	}
      }

  /* For <a b c d x>, if x >= m, then DIFF(a, b) and DIFF(c, d) are odd */
  for (y = 0; y < c; y++) 
    for (x = m; x < QGROUP; x++) 
      for (u = 0; u < m; u++)
	for (v = 0; v < m; v++) if ((u+v) % 2 == 0) {
	  if (insert_cl_all_3(SIGMA(4, y, x), 
			      SIGMA(3, y, u), 
			      SIGMA(2, y, v),
			      FF, cl_arr, sign_arr)) return 1;
	  if (insert_cl_all_3(SIGMA(4, y, x), 
			      SIGMA(1, y, u), 
			      SIGMA(0, y, v),
			      FF, cl_arr, sign_arr)) return 1;
	}

  /* unique covering */
  for (r1 = 3; r1 < r; r1++) 
    for (r2 = r1-1; r2 > 0; r2--)
      for (x = 0; x < m; x++) 
	for (u = 1; u < c; u++) 
	  for (v = u-1; v >= 0; v--) 
	    for (a = 0; a < Addk; a++) {
	    /* delta(r1, r2, u, x, a) and delta(r1, r2, v, x, a) => u = v */
	    if (insert_cl_2(DELTA(r1, r2, u, x, a), 
			    DELTA(r1, r2, v, x, a), 
			    FF, cl_arr, sign_arr)) return 1;
	  }

  for (x = 0; x < m; x++) 
    for (a = 0; a < Addk; a++) {
      if (insert_cl_2(DELTA(2, 1, 3, x, a), 
		      DELTA(2, 1, 2, x, a), 
		      FF, cl_arr, sign_arr)) return 1;
      if (insert_cl_2(DELTA(2, 1, 1, x, a), 
		      DELTA(2, 1, 0, x, a), 
		      FF, cl_arr, sign_arr)) return 1;
    }

  return 0;
}

int oarray_expand_cls (cl_arr, sign_arr)
     int cl_arr[], sign_arr[];
{
  int i, k, x, y, u, v, r1, r2;

  /* constraints for expanding columns */
  for (x = 0; x < expand_col; x++) {

    /* row [0 .. EXPAND-1] x [0 .. EXPAND-1] */
    for (k = EXPAND/2; k > 0; k--) 
      for (r2 = 0; r2 < EXPAND; r2++) { 
	r1 = (r2 + k) % EXPAND;
	for (u = 0; u < m; u++)
	  for (v = 0; v < m; v++) {
	    y = (We[(r2)? (EXPAND-r2) : 0] * DIFF(u, v)) % m;
	    if (Seed[y] != HOLE) {
	      /* DIFF(u, v) is not in H. */
	      if (insert_cl_all_3(SIGMA(r1, x, u), 
				  SIGMA(r2, x, v), 
				  DELTA(EXPAND-1, k-1, x, Reps[y], u%Addk),
				  TT, cl_arr, sign_arr)) return 1;
	    }
	  }
      }

    for (u = 0; u < m; u++)
      for (v = 1; v < m; v++) {
	int uv = (We[1] * DIFF(u, v)) % m;
	for (y = 1; y < m; y++) if (uv == DIFF(v, y)) {
	  for (r1 = 0; r1 < EXPAND; r1++) 
	    if (insert_cl_all_3(SIGMA(r1, x, u), 
				SIGMA((r1+1)%EXPAND, x, v), 
				SIGMA((r1+2)%EXPAND, x, y), 
				FF, cl_arr, sign_arr)) return 1;
	}
      }

    for (u = 1; u < m; u++)
      for (v = 0; v < m; v++) {
	int w1uv = (We[1] * DIFF(u, v)) % m;
	int w2uv = (We[1] * w1uv) % m;
	for (y = 1; y < m; y++) if (w1uv == DIFF(u, y) || w2uv == DIFF(u, y)) {
	  for (r1 = EXPAND; r1 < r; r1++) 
	    for (r2 = 0; r2 < EXPAND-1; r2++)
	      for (i = r2+1; i < EXPAND; i++) {

	      if (insert_cl_all_3(SIGMA(r1, x, u), 
				  SIGMA(r2, x, v), 
				  SIGMA(i, x, y), 
				  FF, cl_arr, sign_arr)) return 1;
	      /*
	      if (insert_cl_all_3(SIGMA(r1, x, u), 
				  SIGMA(r2, x, y), 
				  SIGMA(i, x, v), 
				  FF, cl_arr, sign_arr)) return 1;
				  */
	    }
	}
      }

    /* row [0 ..EXPAND-1] x [EXPAND..r-1] */
    for (r1 = EXPAND; r1 < r; r1++) 
      for (r2 = 0; r2 < EXPAND; r2++) 
	for (u = 1; u < m; u++) 
	  for (v = 0; v < m; v++) {
	    y = (We[(r2 == 0)? 0 : (EXPAND-r2)] * DIFF(u, v)) % m;
	    if (Seed[y] != HOLE) {
	      if (insert_cl_all_3(SIGMA(r1, x, u), 
				  SIGMA(r2, x, v), 
				  DELTA(r1, 0, x, Reps[y], u%Addk),
				  TT, cl_arr, sign_arr)) return 1;
	    }
	  }
    
    
    /* row [EXPAND, r-1] x [EXPAND, r-1] */
    for (r1 = EXPAND+1; r1 < r; r1++) 
      for (r2 = EXPAND; r2 < r1; r2++) 
	for (u = 0; u < m; u++) {

	  for (v = 0; v < m; v++) {
	    y = DIFF(u, v);
	    if (Seed[y] != HOLE) {
	      /* DIFF(u, v) is not in H. */
	      if (insert_cl_all_3(SIGMA(r1, x, u), 
				  SIGMA(r2, x, v), 
				  DELTA(r1, r2, x, Reps[y], u%Addk),
				  TT, cl_arr, sign_arr)) return 1;
	    }
	  }

	  if (Seed[u] == HOLE || u == (We[1]*u)%m) {
	    if (insert_cl_1(DELTA(r1, r2, x, Reps[u], u%Addk), FF)) return 1;
	  } else {
	    for (i = 1; i < EXPAND; i++) 
	      if (insert_cl_2(DELTA(r1, r2, x, Reps[u], u%Addk),
			      DELTA(r1, r2, x, Reps[(We[i]*u)%m], u%Addk),
			      TT, cl_arr, sign_arr)) return 1;
	  }
	}
  }

  /* constraints for non-expanding columns */
  for (x = expand_col; x < c; x++) {

    /* row [0 .. EXPAND-1] x [0 .. EXPAND-1] */
    for (u = 0; u < m; u++) {
      if (Seed[u] == HOLE) {
	if (insert_cl_1(SIGMA(1, x, u), FF)) return 1;
      } else {
	if (insert_cl_2(SIGMA(1, x, u),
			DELTA(EXPAND-1, 0, x, u, u%Addk),
			TT, cl_arr, sign_arr)) return 1;

	if (EXPAND > 3 &&
	    insert_cl_2(SIGMA(1, x, u),
			DELTA(EXPAND-1, 1, x, ((We[1]+1)*u)%m, u%Addk),
			TT, cl_arr, sign_arr)) return 1;

      }
    }

    /* row [0 .. EXPAND-1] x [EXPAND .. r-1] */
    for (r1 = EXPAND; r1 < r; r1++) 
      for (u = 0; u < m; u++) if (Seed[u] != HOLE) {
	if (insert_cl_2(SIGMA(r1, x, u), 
			DELTA(r1, 0, x, Reps[u], u%Addk),
			TT, cl_arr, sign_arr)) return 1;
      }


    /* row [EXPAND .. r-1] x [EXPAND .. r-1] */
    for (r1 = EXPAND+1; r1 < r; r1++) 
      for (r2 = EXPAND; r2 < r1; r2++)
	for (u = 0; u < m; u++)
	  for (v = 0; v < m; v++) {
	    y = DIFF(u, v);
	    if (Seed[y] != HOLE) {
	      /* DIFF(u, v) is not in H. */
	      if (insert_cl_all_3(SIGMA(r1, x, u), 
				  SIGMA(r2, x, v), 
				  DELTA(r1, r2, x, Reps[y], u%Addk),
				  TT, cl_arr, sign_arr)) return 1;
	    }
	  }
  }


  return 0;
}

int oarray_trans (r1, r2, cl_arr, sign_arr)
     int r1, r2, cl_arr[], sign_arr[];
     /* Trans constraints on r1 and r2 */
{
  int a, b, j1, j2, i, j, k, x, x1, y;
  int cak = c/Addk;
  k = INCOMPLETE/MULTI;

  for (a = 0; a < Addk; a++) {
    /* if 0*x = a, 1*x = j, r1*x = i, 0*y = b, 1*y = a-j+b then r2*y = i-j+b,
       where b = j % Addk */

    for (x1 = 2*k; x1 < cak; x1++) {
      x = x1+a*cak;
      j = Oarray[1][x];
      b = j % Addk;
      j1 = ABG_f[ABG_f[a][b]][ABG_g[j]];
      y = 2*k+b*cak;
      while (Oarray[1][y] != j1) y++;

      /* 2 * x = i imply 3 * y = i-j+b. */
      for (i = 1; i < m; i++) {
	if (insert_cl_2(j2=SIGMA(r1, x, i), 
			j1=SIGMA(r2, y, ABG_f[ABG_f[i][b]][ABG_g[j]]), 
			TT, cl_arr, sign_arr)) return 1;
	if (insert_cl_2(j1,
			j2,
			TT, cl_arr, sign_arr)) return 1;
      }
    
      /* 2 * x = i imply 3 * y  \= j for j < m. */
      for (i = m; i < k+m; i++) 
	for (j = 0; j < m; j++) {
	  if (insert_cl_2(j1=SIGMA(r1, x, i), 
			  j2=SIGMA(r2, y, j), 
			  FF, cl_arr, sign_arr)) return 1;
	  if (insert_cl_2(j2,
			  j1,
			  FF, cl_arr, sign_arr)) return 1;
	}
    }

    for (x = 0; x < k; x++) 
      for (i = 1; i < m; i++) {
	/* r1 * x = i imply r2 * (x+k) = i. */
	if (insert_cl_2(j2=SIGMA(r1, x+a*cak, i), 
			j1=SIGMA(r2, k+x+a*cak, i), 
			TT, cl_arr, sign_arr)) return 1;
	if (insert_cl_2(j1,
			j2,
			TT, cl_arr, sign_arr)) return 1;
    }
  }

  return 0;
}    

int oarray_qg1 (r1, r2, cl_arr, sign_arr)
     int cl_arr[], sign_arr[];
     /* QG1 constraints on r1 and r2 */
{
  int a, b, j1, j2, i, j, k, x, x1, y;
  int cak = c/Addk;
  k = INCOMPLETE/MULTI;

  for (a = 0; a < Addk; a++) {
    /* if 0*x = a, 1*x = j, r1*x = i, 0*y = b, 1*y = j-i+b, then r2*y = a-i+b 
       where b = i % Addk */

    for (x1 = 2*k; x1 < cak; x1++) {
      x = x1+a*cak;
      j = Oarray[1][x];

      /* r1 * x = i imply r2 * y = a-i+b. */
      for (i = 1; i < m; i++) {
	b = i % Addk;
	j1 = ABG_f[ABG_f[j][b]][ABG_g[i]];
	y = 2*k+b*cak;
	while (y < c && Oarray[1][y] != j1) y++;

	if (y < c) {
	  if (insert_cl_2(j1=SIGMA(r1, x, i), 
			  j2=SIGMA(r2, y, ABG_f[ABG_f[a][b]][ABG_g[i]]),
			  TT, cl_arr, sign_arr)) return 1;
	  if (insert_cl_2(j2,
			  j1,
			  TT, cl_arr, sign_arr)) return 1;
	}
      }

      /* r1 * x = i imply r2 * y  = a-j+b, where 0*y = i, 1*y = b, b = j % Addk */
      for (i = m; i < k+m; i++) {
	b = j % Addk;
	if (insert_cl_2(j2=SIGMA(r1, x, i), 
			j1=SIGMA(r2, i-m+b*cak, ABG_f[ABG_f[a][b]][ABG_g[j]]),
			TT, cl_arr, sign_arr)) return 1;
	if (insert_cl_2(j1,
			j2,
			TT, cl_arr, sign_arr)) return 1;
      }
    }

    for (x = 0; x < k; x++) 
      for (i = 1; i < m; i++) {
	b = i % Addk;
	/* r1 * x = i imply r2 * x = a. */
	if (insert_cl_2(j2=SIGMA(r1, k+x+a*cak, i), 
			j1=SIGMA(r2, k+x+b*cak, ABG_f[ABG_f[a][b]][ABG_g[i]]),
			TT, cl_arr, sign_arr)) return 1;
	if (insert_cl_2(j1,
			j2,
			TT, cl_arr, sign_arr)) return 1;
    }
  }

  return 0;
}    

int oarray_qg2 (r1, r2, cl_arr, sign_arr)
     int cl_arr[], sign_arr[];
     /* QG1 constraints on r1 and r2 */
{
  int a, b, j1, j2, i, j, k, x, x1, y;
  int cak = c/Addk;
  k = INCOMPLETE/MULTI;

  for (a = 0; a < Addk; a++) {
    /* if 0*x = a, 1*x = j, r1*x = i, 0*y = b, 1*y = a-i+b, then r2*y = j-i+b 
       where b = i % Addk */

    for (x1 = 2*k; x1 < cak; x1++) {
      x = x1+a*cak;
      j = Oarray[1][x];

      /* r1 * x = i imply r2 * y = a-i+b. */
      for (i = 1; i < m; i++) {
	b = i % Addk;
	j1 = ABG_f[ABG_f[a][b]][ABG_g[i]];
	y = 2*k+b*cak;
	while (y < c && Oarray[1][y] != j1) y++;

	if (y < c) {
	  if (insert_cl_2(j1=SIGMA(r1, x, i), 
			  j2=SIGMA(r2, y, ABG_f[ABG_f[j][b]][ABG_g[i]]),
			  TT, cl_arr, sign_arr)) return 1;
	  if (insert_cl_2(j2,
			  j1,
			  TT, cl_arr, sign_arr)) return 1;
	}
      }

      /* r1 * x = i imply r2 * y  = a-j+b, where 0*y = i, 1*y = b, b = j % Addk */
      for (i = m; i < k+m; i++) {
	if (insert_cl_2(j2=SIGMA(r1, x, i), 
			j1=SIGMA(r2, i-m+a*cak, j),
			TT, cl_arr, sign_arr)) return 1;
	if (insert_cl_2(j1,
			j2,
			TT, cl_arr, sign_arr)) return 1;
      }
    }

    for (x = 0; x < k; x++) 
      for (i = 1; i < m; i++) {
	b = i % Addk;
	/* r1 * x = i imply r2 * x = a. */
	if (insert_cl_2(j2=SIGMA(r1, x+a*cak, i), 
			j1=SIGMA(r2, k+x+b*cak, ABG_f[ABG_f[a][b]][ABG_g[i]]),
			TT, cl_arr, sign_arr)) return 1;
	if (insert_cl_2(j1,
			j2,
			TT, cl_arr, sign_arr)) return 1;
    }
  }

  return 0;
}    

int oarray_qg20 (cl_arr, sign_arr)
     int cl_arr[], sign_arr[];
{
  int a, b, i, j, x;
  int k = INCOMPLETE/MULTI;

  if (!IDEMPOTENT && INCOMPLETE && INCOMPLETE % 2 == 0) {
    if (insert_cl_1(SIGMA(2, 2*INCOMPLETE, 0), TT)) return 1;
  }

  if (INCOMPLETE) {
    for (i = 2*k; i < c; i++) {
      j = Oarray[1][i];
      if (j < m && j != 0 && j != m/2) 
	for (x = m; x < QGROUP; x++) {
	  if (j % 2 == 0) {
	    if (insert_cl_1(SIGMA(4, i, x), FF)) return 1;
	  }
	  for (a = 0; a < m; a++)
	    for (b = 0; b < m; b++) if ((a+b) % 2 == 0) {
	      if (insert_cl_all_3(SIGMA(2, i, a),
				  SIGMA(3, i, b),
				  SIGMA(4, i, x),
				  0, cl_arr, sign_arr)) return 1;
	    }
	}
    }
  }

  return 0;
}

int oarray_qg30 (cl_arr, sign_arr)
     int cl_arr[], sign_arr[];
     /* QG1 constraints on r1 and r2 */
{
  int x, y, z, w;

  if (INCOMPLETE) 
    for (z = shift30; z-shift30 < INCOMPLETE/2; z++) 
      if (z > shift30 || Oarray[2][shift30] != m/2)
      for (x = 0; x < m; x++)
	for (y = 0; y < m; y++) if ((x+y) % 2 == 0) {
	  if (insert_cl_2(SIGMA(1, z, x),
			  SIGMA(2, z, y),
			  FF, cl_arr, sign_arr)) return 1;
	  if (insert_cl_2(SIGMA(3, z, x),
			  SIGMA(4, z, y),
			  FF, cl_arr, sign_arr)) return 1;
	}

  if (row_offset == 1) 
    for (z = INCOMPLETE; z < c; z++)
      for (y = z+1; y < c; y++)
	for (x = 1; x < m; x++)
	  for (w = 0; w < x; w++) {
	    if (insert_cl_2(SIGMA(1, z, x),
			    SIGMA(1, y, w),
			    FF, cl_arr, sign_arr)) return 1;
	  }

  return 0;
}

int oarray_auto_cls(cl_arr, sign_arr)
     int cl_arr[], sign_arr[];
{
  int i, j, u, k;

  if ((k = FLAG) < r) {
  for (i = 0; i < r; i++) We[i] = 1;
  if (MULTI > 1) 
    for (i = 1; i < r; i++) 
      We[i] = (We[i-1] * Seed[m]) % m;

  for (i = 3; i < r; i++) 
    for (j = 1; j < c; j++) if (j % k) {
      int i2 = i-1;
      int j2 = j-1;
      if (Oarray[i][j] == UNKNOW && Oarray[i2][j2] == UNKNOW) 
	for (u = 1; u < m; u++) {
	  if (insert_cl_2(SIGMA(i2, j2, u), 
			  SIGMA(i, j, u*We[j%k]),
			  TT, cl_arr, sign_arr)) return 1;
	  if (insert_cl_2(SIGMA(i, j, u*We[j%k]),
			  SIGMA(i2, j2, u), 
			  TT, cl_arr, sign_arr)) return 1;
	}
    }
  }
  return 0;
}

int oarray_unit_cls ()
{
  int a, cak, i, j, k;
  k = INCOMPLETE/MULTI;

  for (i = 0; i < r; i++) 
    for (j = 0; j < c; j++)  
      Oarray[i][j] = UNKNOW;

  /* pre-set the places of infinity elements at first and second rows */
  if (EXPAND)
    pre_set_infinity(k/EXPAND);
  else 
    pre_set_infinity(k);

  if (IDEMPOTENT) 
    for (a = 0; a < Addk; a++) {
      cak = a*c/Addk+shift30;

      /* no entry after the second will be 0 */
      for (i = row_offset; i < r; i++) 
	for (j = cak; j < c/Addk; j++) if (i >= 2 || j >= k+shift30) {
	  if (insert_cl_1(SIGMA(i, j, a), FF)) return 1;

	  if (NHOLE) {
	    int y;
	    for (y = 1; y < m; y++) if (Seed[y] == HOLE) {
	      if (insert_cl_1(SIGMA(i, j, ABG_f[y][a]), FF)) return 1;
	    }
	  }
	}
    }
  
  if (LINE < 5000 && LINE >= 3000) oa_read_partial();
  else if (((LINE / 1000) & 1) && LINE >= 2000) oa_read_bool();
  
  /* restriction on the first few columns */
  if (RESTRICT < 80 && RESTRICT % 10 != 0) {
    int v1 = Oarray[1][0] + 1;
    int c1 = RESTRICT%10 + 2*k;
    int r1 = (row_offset == 1)? 1 : 3;
    int r2 = RESTRICT/10;
    r2 += r1;
    if (r2 > r) r2 = r;
    if (c1 > c) c1 = c;

    while (Seed[v1] != v1) v1++;
    v1 -= 2*k+3*row_offset;
    for (j = 2*k+shift30; j < c1; j++)
      for (i = r1; i < r2; i++) {
	int y;
	for (y = v1+3*i+2*j; y < m; y++) {
	  /*printf("A[%d, %d] != %d\n", i, j, y); */
	  if (insert_cl_1(SIGMA(i, j, y), FF)) return 1;
	}
      }
  }

  if (RESTRICT > 1000 && RESTRICT < 4000 && MULTI == 2 && (m % 2 == 0 || INCOMPLETE % 2)) {
    int r1, r2, wrong[5][10], avoid;
    j = RESTRICT % 1000;
    if (j > m) { printf("bad: RESTRICT = %d\n", RESTRICT); exit(0); }
    k = m/2;
    printf("special code = %d\n", j);
    if (j > k) j = m-j;

    avoid = 5;
    wrong[0][0] = m;
    wrong[1][0] = 0;
    wrong[2][0] = j;
    wrong[3][0] = j+k;
    wrong[4][0] = k;
    for (j = 1; j < 5; j++)
      for (i = 0; i < 5; i++)
	wrong[(i+1)%5][j] = wrong[i][j-1];

    if (INCOMPLETE % 2 == 0) {
      avoid = 10;
      i = FLAG/100;
      wrong[0][5] = m;
      wrong[1][5] = 0;
      wrong[2][5] = i;
      wrong[3][5] = i;
      wrong[4][5] = 0;
      for (j = 6; j < 10; j++)
	for (i = 0; i < 5; i++)
	  wrong[(i+1)%5][j] = wrong[i][j-1];
    }

    printf("Avoiding:\n     ");
    for (i = 0; i < 5; i++) {
      for (j = 0; j < avoid; j++)
	if (wrong[i][j] < m)
	  printf("%2d ", wrong[i][j]);
	else
	  printf("x%d ", (j < 5)? INCOMPLETE+1 : INCOMPLETE+2);
      printf("\n     ");
    }

    if (TRACE > 1) printf("\n     ");
    for (r1 = 2; r1 < r; r1++) 
      for (r2 = 0; r2 < r1; r2++) {
	if (TRACE > 1) printf("<%d, %d> miss ", r1, r2);
	for (j = 0; j < avoid; j++) if (wrong[r1][j] < m && wrong[r2][j] < m) {
	  int y = DIFF(wrong[r1][j], wrong[r2][j]);
	  if (TRACE > 1) printf(" %d", y);
	  for (i = 0; i < c; i++) {
	    if (insert_cl_1(DELTA(r1, r2, i, Reps[y], wrong[r1][j]%Addk), FF)) return 1;
	  }
	}
	if (TRACE > 1) printf("\n     ");
      }
    printf("\n");
  }

  return 0;
}

int pre_set_infinity (k)
     int k;
{
  int i, j, avoid, a, c_by_addk, big;
  shift30 = 0;

  avoid = -1;
  if (RESTRICT > 1000 && RESTRICT < 4000 &&
      MULTI == 2 && (m % 2 == 0 || INCOMPLETE % 2)) {
    avoid = RESTRICT % 1000;
    if (avoid > m/2) avoid = m-avoid;
  }

  if (QUEEN == 30 && (!IDEMPOTENT || INCOMPLETE % 2)) {
    set_entry0(0, 0, QGROUP-1);
    set_entry0(1, 0, 0);
    shift30 = 1;

    if (!IDEMPOTENT) {
      set_entry0(2, 0, 0);
      set_entry0(3, 0, 0);
      set_entry0(4, 0, 0);
      if (INCOMPLETE%2 == 0) {
	set_entry0(1, 1, 0);
	set_entry0(2, 1, m/2);
      }
    } else
      set_entry0(2, 0, m/2);
  }

  if (QUEEN == 40 && r == 5) {
    /* infinities on the first row */
    for (i = 0; i < k/2; i++) {
      set_entry0(0,i,m+i);
      set_entry0(1,i,0);
      for (j = 0; j < m; j += 2) {
	if (insert_cl_1(SIGMA(2,i,j), FF)) return 1;
      }
    }
    for (i = k/2; i < c; i++) {
      set_entry0(0,i,0);
    }
    /* infinities on the second row */
    for (i = k/2; i < k+k/2; i++) {
      set_entry0(1,i,m+i-k/2);
    }
    /* infinities on the fifth row */
    for (i = k/2+k; i < k+k+k/2; i++) {
      set_entry0(4,i,m+i-k/2-k);
    }

    if (RESTRICT) {
      /* restriction on second row */
      j = 1;
      for (i = (RESTRICT == 1)? k+k+k/2 : k/2+k; i <= c-RESTRICT; i++) {
	if (Seed[j] == HOLE) j++;
	set_entry0(1,i,j++);
      }
    }
  } else 

  for (a = 0; a < Addk; a++) {
    c_by_addk = a*c/Addk+shift30;

    /* infinities on the first two rows */
    for (i = 0; i < k; i++) {
      set_entry0(0,i+c_by_addk,m+i);
      set_entry0(1,i+k+c_by_addk,m+i);
      set_entry0(0,i+k+c_by_addk,a);
      set_entry0(1,i+c_by_addk,a);
    }

    if (IDEMPOTENT) j = 1; else j = 0;
    if (row_offset == 2) big = m;
    else if (RESTRICT < 100 && RESTRICT > 79) big = RESTRICT-79;
    else big = 0;

    for (i = 2*k; i < c/Addk; i++) {
      set_entry0(0,i+c_by_addk,a);

      while (j < big && (Seed[j] != j || j == avoid)) j++;
      if (j < big) set_entry0(1,i+c_by_addk,ABG_f[j][a]);
      j++;
    }
      
    /* pre-set the places of infinity elements in rows after the second*/
    for (j = 2; j < r-free_infinity; j++)
	for (i = 0; i < k; i++) {
	  set_entry(j, j*k+i+c_by_addk, m+i);
	}
  }
  return 0;
}

/*
#ifndef HP_UX
#ifdef PRIVATE
oarray_extra_cls ()
{
  int i, j, s, x;
  int sol[] = {
14, 12,  0, 0, 0, 0, 0, 0, 0, 
 0,  0, 12, 1, 2, 4, 5, 6,14,
 6,  5,  7,11, 3,12, 8,10, 9,
 5,  3, 10, 7,14, 1,12, 5, 2,
11,  6,  9, 3,11, 8, 6,12, 4,
-1};
  printf("\nnew unit clauses\n");
  
  s = 0;
  for (i = 0; i < r; i++)
    for (j = 0; j < c; j++) {
      x = sol[s++];
      if (x == -1) {
	printf("\nI'm there:\n");
	print_oarray(stdout);
	return 1;
      }
      set_entry(i, j, x);
    }

  print_oarray(stdout);
  return 0;
}
#endif
#endif
*/

void print_oarray_portrait (file)
     FILE *file;
{
  int i, j, x, y, k;
  
  for (k = 0; k < MULTI; k++) {

    for (j = 0; j < c; j++) {
      fprintf(file, "\n ");
      for (i = 0; i < r; i++) {
	if (Oarray[i][j] < m) {
	  y = Oarray[i][j];
	  for (x = 0; x < k; x++) y = Mext[y];
	  fprintf(file, " %2d", y);
	} else {
	  y = Oarray[i][j]-m+1+k*INCOMPLETE/MULTI;
	  if (i && QUEEN == 30 && i % 2 == 0)
	    fprintf(file, " y%d", y);
	  else
	    fprintf(file, " x%d", y);
	}
      }
    }
    fprintf(file, "\n ");
  }
}

void print_oarray (file)
     FILE *file;
{
  int i, j, r1, r2, x, y, k;
  int diffs[100];

  for (k = 0; k < MULTI; k++) {

    for (i = 0; i < r; i++) {
      fprintf(file, "\n    ");
      for (j = 0; j < c; j++) 
	if (Oarray[i][j] < m) {
	  y = Oarray[i][j];
	  for (x = 0; x < k; x++) y = Mext[y];
	  fprintf(file, " %2d", y);
	} else {
	  y = Oarray[i][j]-m+1+k*INCOMPLETE/MULTI;
	  if (i && QUEEN == 30 && i % 2 == 0)
	    fprintf(file, " y%d", y);
	  else
	    fprintf(file, "  -", y);
	}
    }
    
    fprintf(file, "\n\nDifference Conditions:\n");
    if (QUEEN == 40) {
      for (r2 = 0; r2 < r; r2++) 
	if (r2 == 0) {
	  for (r1 = 1; r1 < 4; r1 += 2) {
	    for (j = 0; j < m; j++) diffs[j] = -1;
	    fprintf(file, "\nr%d - r%d: ", r1, r2);
	    for (j = 0; j < c; j++) {
	      if (Oarray[r1][j] < m && Oarray[r2][j] < m) {
		y = DIFF(Oarray[r1][j], Oarray[r2][j]);
		fprintf(file, " %2d", y);
		if (diffs[y] != -1) printf("WOW "); else diffs[y] = 1;
	      }
	      if (Oarray[r1+1][j] < m && Oarray[r2][j] < m) {
		y = DIFF(Oarray[r1+1][j], Oarray[r2][j]);
		fprintf(file, " %2d", y);
		if (diffs[y] != -1) printf("WOW "); else diffs[y] = 1;
	      }
	    }
	  }
	} else if (r2 == 1 || r2 == 3) {
	  for (j = 0; j < m; j++) diffs[j] = -1;
	  fprintf(file, "\nr%d - r%d: ", r1=r2+1, r2);
	  for (j = 0; j < c; j++) {
	    if (Oarray[r1][j] < m && Oarray[r2][j] < m) {
	      y = DIFF(Oarray[r1][j], Oarray[r2][j]);
	      for (x = 0; x < k; x++) y = Mext[y];
	      fprintf(file, " %2d", y);
	      if (diffs[y] != -1) printf("WOW "); else diffs[y] = 1;

	      y = ABG_g[y];
	      fprintf(file, " %2d", y);
	      if (diffs[y] != -1) printf("WOW "); else diffs[y] = 1;
	    }
	  }
	} else if (r2 == 2) {
	  for (j = 0; j < m; j++) diffs[j] = -1;
	  fprintf(file, "\nr3 - r1: ");
	  for (j = 0; j < c; j++) {
	    if (Oarray[3][j] < m && Oarray[1][j] < m) {
	      y = DIFF(Oarray[3][j], Oarray[1][j]);
	      fprintf(file, " %2d", y);
	      if (diffs[y] != -1) printf("WOW "); else diffs[y] = 1;
	    }
	    if (Oarray[4][j] < m && Oarray[2][j] < m) {
	      y = DIFF(Oarray[4][j], Oarray[2][j]);
	      fprintf(file, " %2d", y);
	      if (diffs[y] != -1) printf("WOW "); else diffs[y] = 1;
	    }
	  }

	  for (j = 0; j < m; j++) diffs[j] = -1;
	  fprintf(file, "\nr4 - r1: ");
	  for (j = 0; j < c; j++) {
	    if (Oarray[4][j] < m && Oarray[1][j] < m) {
	      y = DIFF(Oarray[4][j], Oarray[1][j]);
	      fprintf(file, " %2d", y);
	      if (diffs[y] != -1) printf("WOW "); else diffs[y] = 1;
	    }
	    if (Oarray[3][j] < m && Oarray[2][j] < m) {
	      y = DIFF(Oarray[3][j], Oarray[2][j]);
	      fprintf(file, " %2d", y);
	      if (diffs[y] != -1) printf("WOW "); else diffs[y] = 1;
	    }
	  }
	}
    } else 
      for (r2 = 0; r2 < r; r2++)
	for (r1 = r2+1; r1 < r; r1++) {
	  for (j = 0; j < m; j++) diffs[j] = -1;
	  fprintf(file, "\nr%d - r%d: ", r1, r2);
	  for (j = 0; j < c; j++) if (Oarray[r1][j] < m && Oarray[r2][j] < m) {
	    y = DIFF(Oarray[r1][j], Oarray[r2][j]);
	    for (x = 0; x < k; x++) y = Mext[y];
	    fprintf(file, " %2d", y);
	    if (diffs[y] != -1) {
	      printf("W ");
	    } else 
	      diffs[y] = 1;
	  }
	}
    fprintf(file, "\n\n");
  }
   
  if (QUEEN != 40) {
    j = RESTRICT % 1000;
    if (RESTRICT > 1000 && RESTRICT < 4000 && j < m) {
      printf("And append the %d cyclic shitfs of\n", r);
      printf("       ( x%d  0 %2d %2d %2d )\n\n", INCOMPLETE, j, j+m/2, m/2);
    }
    print_oarray_portrait(file);
  }
}

void print_oarray20 (file)
     FILE *file;
{
  int i, j, r1, x, y, k;
  k = 0;

  for (j = 0; j < c; j++) if ((x=Oarray[4][j]) < m) {
    for (i = 0; i < 4; i++) if ((y=Oarray[i][j]) < m) {
      Oarray[i][j] = (y>=x)? (y-x) : (y+m-x);
    }
    Oarray[4][j] = 0;
  }
  
  for (j = 1; j < c; j++) {
    for (i = 0; i < j; i++) {
      x = 0;
      for (r1 = 0; r1 < 4; r1++) if (x == 0)
	if (Oarray[r1][i] < m &&
	    Oarray[r1][i] != Oarray[r1][j])
	  x  =1;
      if (x == 0) Oarray[0][j] = -1000;
    }
  }

    for (i = 0; i < r; i++) {
      fprintf(file, "\n    ");
      for (j = 0; j < c; j++) if (Oarray[0][j] != -1000) {
	if (Oarray[i][j] < m) {
	  y = Oarray[i][j];
	  for (x = 0; x < k; x++) y = Mext[y];
	  fprintf(file, " %2d ", y);
	} else {
	  y = Oarray[i][j]-m+1+k*INCOMPLETE/MULTI;
	  if (i && i % 2 == 0)
	    fprintf(file, " y%d ", y);
	  else
	    fprintf(file, " x%d ", y);
	}
      }}
    
}

void print_oarray2(file)
     FILE *file;
{
  int i, j;
  
  fprintf(file, "First two rows of the array:");
  for (i = 0; i < 2; i++) {
    fprintf(file, "\n    ");
    for (j = 0; j < c; j++) 
      if (Oarray[i][j] < m)
	fprintf(file, " %2d", Oarray[i][j]);
      else
	fprintf(file, " x%d", Oarray[i][j]-m+1);
  }
  fprintf(file, "\n\n");
}

void print_oarray_model (file)
     FILE *file;
{
  int i, x, y, z;

  for (i = rcn; i > 0; i--) if (Value[i] == TT) {
    z = (i-3) % QGROUP;
    x = (i-3) / QGROUP;
    y = x % c;
    x = row_offset + x / c;
    if (Oarray[x][y] < 0) Oarray[x][y] = z;
  }
  
  if (EXPAND) {
    for (i = 0; i < r; i++) Oarray[i][c] = 0;
    c++;
    for (i = 0; i < expand_col; i++) 
      for (x = 1; x < EXPAND; x++) {
	for (y = 0; y < EXPAND; y++) {
	  Oarray[(y+x)%EXPAND][c] = (Oarray[y][i] < m)? (We[x]*Oarray[y][i])%m : m;
	}
	for (y = EXPAND; y < r; y++)
	  Oarray[y][c] = (Oarray[y][i] < m)? (We[x]*Oarray[y][i])%m : m;
	c++; 
	if (c >= MAX_COL) { printf("MAX_COL overflow!\n"); c--; }
      }
  }

  fprintf(file, "\n%d-HMOLS(%d^%d, %d^1):\n", 
	  OARRAY, RAMSEY, m/((RAMSEY)? RAMSEY : 1), INCOMPLETE);
  print_oarray(file);

  /* print the corresponding squares */
  if (QUEEN == 20) { print_oarray20(file); /*oa_print_squares(2, 4); */}

  if (MODEL != 1) oarray_unit_cls();
}


GLOB SATOINT Lsquare[MAX_SQUARE1][MAX_SQUARE1];
GLOB int n;

void oa_print_squares (s1, s2)
     int s1, s2;
{
  int i, j;

  n = QGROUP;

  for (i = 0; i < Addk; i++)
    for (j = 0; j < QGROUP; j++) Lsquare[i][j] = 0;
  if (RAMSEY > 1) 
    for (i = 0; i < Addk; i++)
      for (j = i; j < QGROUP; j += m/RAMSEY) Lsquare[i][j] = -1;

  for (j = 0; j < c; j++) {
    Lsquare[Oarray[0][j]][Oarray[1][j]] = Oarray[s1][j];
  }
  fill_table(Addk);
  print_square(0); 

  if (s1 != 3 && s2 != 3) {
    s1 = 3;
    for (j = 0; j < c; j++) {
      Lsquare[Oarray[0][j]][Oarray[1][j]] = Oarray[s1][j];
    }
    fill_table(Addk);
    print_square(0); 
  }

  for (j = 0; j < c; j++) {
    Lsquare[Oarray[0][j]][Oarray[1][j]] = Oarray[s2][j];
  }
  fill_table(Addk);
  print_square(0); 
}

int oarray_rem (mo, col, j, i1, i2)
     int mo, col[], j, i1, i2;
{
  if (Oarray[i1][j] >= m || Oarray[i2][j] >= m) return mo;
  return ((col[i2]-col[i1] + m) % mo);
}

int oa_type (j, mo)
     int j, mo;
{
  int i;
  static int max_type;
  static int types[MAX_COL];

  i = oa_type2(j, mo);
  for (j = 0; j < max_type; j++) if (i == types[j]) return j;
  types[max_type++] = i;
  return (max_type-1);
}

int oa_type2 (j, mo)
     int j, mo;
{
  int i;

  for (i = 0; i < r; i++) 
    if (Oarray[i][j] >= m) 
      return ((i > 1)? ((i)*mo+Oarray[1][j] % mo) : i+mo+1);
  if (Oarray[1][j] >= 0)
    return (Oarray[1][j] % mo + 1);
  else
    return 0;
}

oa_read_matrix40 ()
{
  int i, j, k;
  char name[20];
  int oarray2[MAX_ROW][MAX_COL];
  int k0 = INCOMPLETE/2;
  int k1 = k0 + INCOMPLETE;
  int k2 = k1 + INCOMPLETE;

  printf("Read in a matrix:\n");
  for (i = 0; i < r; i++) {
    for (j = 0; j < c; j++) {
      if (fscanf(Input_sqs, "%d", &k) == EOF) { printf("\n"); return 0; }
      printf("%2d ", k);
      oarray2[i][j] = k;
    }
    printf("\n");
  }
  printf("\n");

  /* Copy to Oarray */
  for (i = 0; i < 4; i++) 
    for (j = 0; j < c; j++) if (oarray2[i][j] > 0) {
      if (j < INCOMPLETE) {
	set_entry(i+1, j+k1, oarray2[i][j]);
      } else if (j < INCOMPLETE+INCOMPLETE) {
	set_entry(i+1, j-k0, oarray2[i][j]);
      } else if (j < k2) {
	set_entry(i+1, j-INCOMPLETE-INCOMPLETE, oarray2[i][j]);
      } else {
	set_entry(i+1, j, oarray2[i][j]);
      }
    }

  if (TRACE > 1) {
    for (i = 0; i < 5; i++) {
      for (j = 0; j < c; j++) printf(" %2d", Oarray[i][j]);
      printf("\n");
    }
    printf("\n");
  }

  /* generate clauses */
  for (i = 1; i < 5; i++) 
    for (j = 0; j < c; j++) {
      k = Oarray[i][j];
      if (k >= 0 && k < m) set_entry(i,j,k);
    }

  return 0;
}

oa_read_partial ()
{
  int i, j, k;
  char name[20];

  sprintf(name, "c%d.in", LINE % 1000);
  if (Input_sqs == NULL) { open_input_sqs(name); }
  if (fscanf(Input_sqs, "%d", &i) == EOF) {
    printf("No more blocks.\n"); 
    fclose(Input_sqs);
    Input_sqs = NULL;
    return 1;
  }

  if (QUEEN == 40) return oa_read_matrix40();

  printf("Read in an array:\n");
  for (i = 0; i < r; i++) {
    for (j = 0; j < c; j++) {
      if (fscanf(Input_sqs, "%d", &k) == EOF) { printf("\n"); return 0; }
      if (Oarray[i][j] >= m) {
	printf("- ");
	if (k != -1 && k != Oarray[i][j]) 
	  { printf("Bad input (-1 expected): %d\n", k); exit(0); }
      } else if (k < 0) {
	printf("X ");
      } else {
	printf("%d ", k);
	set_entry(i,j,k);
      }
    }
    printf("\n");
  }
  printf("\n");

  return 0;
}

oa_read_bool ()
{
  int i, j, k;
  char name[20];

  sprintf(name, "b%d.in", LINE % 1000);
  Input_sqs = fopen(name, "r");
  if (Input_sqs == NULL) {
    printf("File %s doesn't exist!\n", name);
    exit(1);
  }

  for (i = 1; i < r; i++) 
    for (j = 0; j < c; j++) {
      fscanf(Input_sqs, "%d", &k);
      if (Oarray[i][j] < m && (k == 0 || k == 1)) {
	k++;
	while (k < m) {
	  if (insert_cl_1(SIGMA(i, j, k), FF)) return 1;
	  k += 2;
	}
      }
    }
  return 0;
}

oa_read_square ()
{
  int i, j, k, col[4];
  char name[20];

  sprintf(name, "c%d.in", LINE % 1000);
  Input_sqs = fopen(name, "r");
  if (Input_sqs == NULL) {
    printf("File %s doesn't exist!\n", name);
    exit(1);
  }

  c = (QGROUP + INCOMPLETE - RAMSEY) / 2;
  for (i = 0; i < m; i += m/RAMSEY) Lsquare[0][i] = i;

  for (i = 0; i < c; i++) {
    int z1, z2, z3;
    int a1, a2, a3;
    for (j = 0; j < 4; j++) {
      fscanf(Input_sqs, "%d", &k);
      col[j] = k;
    }
    if (col[1] >= m) {
      z1 = 0; z2 = col[1]; z3 = DIFF(col[2], col[0]);
      a1 = col[1]; a2 = 0; a3 = DIFF(col[3], col[0]);
    } else {
      z1 = 0; z2 = DIFF(col[1],col[0]); 
      z3 = (col[2] >= m)? col[2] : DIFF(col[2],col[0]); 
      a1 = 0; a2 = DIFF(col[0],col[1]); 
      a3 = (col[3] >= m)? col[3] : DIFF(col[3],col[1]); 
    }
    Lsquare[z1][z2] = z3;
    Lsquare[a1][a2] = a3;

    printf("[%d, %d, %d, %d] %d * %d = %d    %d * %d = %d\n", 
	   col[0], col[1], col[2], col[3], z1, z2, z3, a1, a2, a3); 

    /* fix the value of the infinities */
    if ((i<<1) < INCOMPLETE) {
      if (insert_cl_1(TRIPLE2KEY(z1, z2, m+i), 1)) return 1;
      /* if (insert_cl_1(TRIPLE2KEY(z2, z1, m+i+INCOMPLETE/2), 1)) return 1;*/
    } /* else {
      if (insert_cl_1(TRIPLE2KEY(col[0], col[1], 0), 1)) return 1;
      if (insert_cl_1(TRIPLE2KEY(col[1], col[0], 0), 1)) return 1;
      } */

    if (i < c-2*INCOMPLETE) {
      if (((col[0]+col[1])&1==0) || ((col[2]+col[3])&1==0)) {
	for (j = m; j < n; j++) {
	  /* printf("%d * %d != %d\n", col[0], col[1], j);*/
	  if (insert_cl_1(TRIPLE2KEY(col[0], col[1], j), 0)) return 1;
	}
      }
    } else if (col[1] < m) {
      for (j = m; j < n; j++) {
	if (insert_cl_1(TRIPLE2KEY(col[0], col[1], j), 0)) return 1;
      }
    }
  }
  fill_table(1);

  if (TRACE > 1) 
    for (i = 0; i < QGROUP; i++) {
      for (j = 0; j < QGROUP; j++) 
	printf("%2d ", Lsquare[i][j]);
      printf("\n");
    }

  return 0;
}

