/*********************************************************************
; Copyright 1992-2002, The University of Iowa (UI).  All rights reserved. 
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

#define DIFF(x,y) (ABG_f[ABG_g[y]][x])
#define neg(x) DIFF(n1,x)
#define ALPHA(k,x,y) (((k) * Kmax) + ((y) * m) + (x) + 1)
#define BETA(k,x,y) (((k) * Kmax) + ((x+INCOMPLETE) * m) + (y) + 1)
#define GAMMA(k,x,y) (((k) * Kmax) + ((x+INCOMPLETE+INCOMPLETE) * m) + (y) + 1)
#define THETA(k,x,y) (((k) * Kmax) + nk2m + ((x) * m) + (y) + 1)
#define DELTA(k,x,y) (((k) * Kmax) + (nk2m<<1) + ((x) * m) + (y) + 1)

/**** Abelian groups ****/
SATOINT ABG_f[MAX_ABG_SIZE][MAX_ABG_SIZE];
SATOINT ABG_g[MAX_ABG_SIZE];
extern int m, n, n1, n_sqt, n_cube, n_four, n_offset, max_seed;
extern FILE *Input_sqs;
GLOB int Lsquare[MAX_SQUARE1][MAX_SQUARE1];
int Kmax, addk_num, nk2m;

int OMEGA(x,y,z) 
     int x, y, z;
{
  int k;

  if (CYCLIC == 0) 
    return (x*n_sqt + y*n + z + 1 + n_offset);
  else if (x>=m) {
    k = y % addk_num;
    return ((GAMMA(k,x,DIFF(z,y-k))) + n_cube);
  } else {
    k = x % addk_num;
    if (y>=m) 
      return ((BETA(k,y,DIFF(z,x-k))) + n_cube);
    else {
      return ((ALPHA(k, DIFF(y,x-k), ((z<m)? DIFF(z,x-k) : z))) + n_cube);
    }
  } 
}

int TRIPLE2KEY (x,y,z) 
     int x, y, z;
{
  int k, w;

  if (CYCLIC == 0) {
    if (63 <= QUEEN && QUEEN <= 68) {
      if (x == y || x == z || y == z) {
	if (66 <= QUEEN && QUEEN <= 67) {
	  w = (QUEEN == 66)? get_k_flag() : 0;
	  if (x == y && z == w) return 1;
	  else if (x == z && y == w) return 1;
	  else if (y == z && x == w) return 1;
	  else return 2;
	} else if (x == y && y == z) return 1;
	else return 2;
      }
      if (z < x && z < y) {
	k = x; x = z; z = y; y = k;
      } else if (y < x) {
	k = x; x = y; y = z; z = k;
      }
      if (x >= (n+1)/2) {
	x = n1-x; y = n1-y; z = n1-z;
      }
    }
    return ((x * n_sqt) + (y * n) + z + 1);
  }

  /*if (CYCLIC == 'B' || CYCLIC == 'D') */
  if (x>=m) {
    k = y % addk_num;
    return (GAMMA(k,x,DIFF(z,y-k)));
  } else {
    k = x % addk_num;
    if (y>=m) 
      return (BETA(k,y,DIFF(z,x-k)));
    else 
      return (ALPHA(k,DIFF(y,x-k), ((z<m)? DIFF(z,x-k) : z)));
  } 
}

void print_qp_coding (p, q)
     int p, q;
{
  int ab[100][2], i, j, k;

  for (i = 0; i < p; i++)
    for (j = 0; j < q; j++) {
      k = ABG_f[j][i*q];
      ab[k][0] = j; ab[k][1] = i;
    }

  printf("Each element of G is encoded as follows:\n");
  for (i = 0; i < p; i++)
    for (j = 0; j < q; j++) {
      k = i*q+j;
      printf(" %2d: b^%da^%d = a^%db^%d\n", k, i, j, ab[k][0], ab[k][1]);
    }
  printf("\n");
}

void gen_gp_table (p, q)
     int p, q;
{
  int i, j, r;

  if (p > q) { i = p; p = q; q = i; }
  printf("Working with p = %d and q = %d\n", p, q);

  if (CYCLIC == 'D') {
    if ((p*p != q) && (q - 1) % p != 0) {
      printf("Error:  p doesn't divide (q-1).\n");
      exit(1);
    }

    /* looking for r */
    if (p*p == q) {
      r = p+1;
    } else {
      r = 0;
      for (j = 2; j < q; j++) {
	int x = j;
	for (i = 1; i < p; i++) x *= j;
	if (x % q == 1) { r = j; break; }
      }
    }
  } else {
    if (p != 2) exit(0);
    r = q-1;
  }

  CYCLIC = 'B';
  if (r == 0) {
    printf("Error:  no good r was found such that r^p = 1 mod q.\n");
    exit(1);
  }

  printf("group G = { b^ia^j | 0 <= i < %d, 0 <= j < %d, \n", p, q);
  printf("            b^%d = b^0 = 1 = a^0 = a^%d, ab = ba^%d }\n\n", p, q, r);

  /* start to fill in the table */
  fill_qp_table(p, q, r);
  fix_abg_g();
  if (TRACE>1) prn_abg_table();
  print_qp_coding(p, q);

  if (RESTRICT == 99) { print_short_blocks(q); }
}

#define encode_pair(a, b) (a)*q+(b)
void decode_pair (i, ap, bp, q)
     int i, *ap, *bp, q;
{
  *ap = i/q;
  *bp = i % q;
}

void fill_qp_table (p, q, r)
     int p, q, r;
{
  int i, j;

  /* initialization */
  for (i = 1; i < m; i++)
    for (j = 1; j < m; j++) 
      ABG_f[i][j] = -1;

  for (i = 1; i < m; i++)
    for (j = 1; j < m; j++) {
      if (ABG_f[i][j] != -1) { 
	printf("strange entry: %d * %d = %d\n", i, j, ABG_f[i][j]); 
      }
      ABG_f[i][j] = gp_one_product(i, j, p, q, r);
      /*printf("%d * %d = %d\n", i, j, ABG_f[i][j]); */
    }
}

int gp_one_product(i, j, p, q, r)
     int i, j, p, q, r;
{
  int stacka[100], stackb[100], stack_idx;
  int a1, b1, a0, b0;
  int loaded = 1;

  /*printf("i, j, p, q, r = %d, %d, %d, %d, %d\n",  i, j, p, q, r);*/


  /* compute (a0,b0)*(a1,b1) */
  decode_pair(j, &a1, &b1, q);
  decode_pair(i, &a0, &b0, q);
  stack_idx = 0;

  while (loaded || stack_idx) {
    if (loaded == 0) {
      stack_idx--;
      a0 = stacka[stack_idx];
      b0 = stackb[stack_idx];
      i = encode_pair(a0, b0);
    } else {
      loaded = 0;
    }
    /*printf("(a0 b0) = (%d %d), (a1 b1) = (%d %d)\n", a0, b0, a1, b1);*/

    if (ABG_f[i][j] != -1) {
      j = ABG_f[i][j];
      decode_pair(j, &a1, &b1, q);
    } else if (a1 == 0) {
      a1 = a0;
      b1 = (b1+b0) % q;
      j = encode_pair(a1, b1);
    } else if (b0 == 0) {
      a1 = (a1+a0) % p;
      j = encode_pair(a1, b1);
    } else {
      a1--;
      b0--;
      j = encode_pair(a1, b1);
      stacka[stack_idx] = a0;
      stackb[stack_idx] = b0;
      stack_idx++;
      loaded = 1;
      a0 = 1;
      b0 = r;
      i = encode_pair(a0, b0);
    }
  }
  return j;
}

void gen_abg_table()
  /* Generate the Abelian group Z_k1 x Z_k2 x ... x Z_ky. */
{
  int ci[10], cj[10], k[10], i, j, s, x, y;

  if (m >= MAX_ABG_SIZE) {
    printf("The size of group, %d, is out of bound (%d)\n", m, MAX_ABG_SIZE);
    exit(0);
  }
  x = FORMAT;
  if (x == 100) {
    FILE *f;
    printf("Reading a group from group.in\n");
    /* open_input_sqs("group.in");*/
    f = fopen("group.in", "r");
    if (f == NULL) {
      printf("File group.in doesn't exist!\n");
      exit(0);
    }
    fscanf(f, "%d", &i);
    if (i != m) {
      printf("the group size is not right (m=%d, %d).\n", m, i); 
      exit(0);
    }
    for (i = 0; i < m; i++) 
      for (j = 0; j < m; j++) {
	fscanf(f, "%d", &s);
	ABG_f[i][j] = s;
      }
    fix_abg_g();
    printf("Finish reading group.in\n");
    if (TRACE == 5) prn_abg_table();
    fclose(f);
    return;
  } else if (x < 2) { k[0] = m; y = s = 1; }
  else {
    s = m; y = 0; 
    while (s > 1 && x > 1) {
      i = x % 10; 
      x = x/10;
      if (i > 1 && s % i == 0) {
	k[y++] = i; s = s/i;
      } else {
	printf("Warning: %d is not a nontrivial factor of (%d - %d)\n",
	       i, QGROUP, INCOMPLETE);
	k[0] = m; y = s = 1; 
	break;
      }
      if (x <= 1 && s > 1) k[y++] = s;
    }

    if (RAMSEY > 0) {
      NHOLE = (QGROUP-INCOMPLETE) / RAMSEY;
      i = 1;
      while (i < y) {
	if (k[i] == NHOLE) { k[i] = k[0]; k[0] = NHOLE; i = y; }
	else i++;
      }
    }  
  }

  if (OUTPUT < 2 && CYCLIC != 'D') {
    printf("Group G = Z%d", k[0]);
    for (i = 1; i < y; i++) printf(" x Z%d", k[i]);
    if (RAMSEY > 1 && y > 1 && k[0] != NHOLE)
      printf("\nWarning: the holes may not match!");
    printf("\n\n");
  }

  /* 0 is the unit */
  for (i = 0; i < m; i++) ABG_f[0][i] = ABG_f[i][0] = i;

  if (CYCLIC == 'D') {
    if (y != 2) {
      printf("\nError: what are p and q?!\n\n");
      exit(1);
    }
    gen_gp_table(k[0], k[1]);
    return;
  } 

  for (i = 1; i < m; i++) {
    abg_encode(y, k, i, ci);
    for(j = i; j < m; j++) {
      abg_encode(y, k, j, cj);
      for (x = 0; x < y; x++) cj[x] = (ci[x] + cj[x]) % k[x];
      s = abg_decode(y, k, cj);
      ABG_f[i][j] = ABG_f[j][i] = s;
    }
  }

  fix_abg_g();
  if (TRACE == 5) {
    prn_abg_table();

    /* print the code of Abelian group */
    if (y > 1) {
      for (i = 0; i < m; i++) {
	abg_encode(y, k, i, ci);
	printf("%2d = <", i);
	for (j = 0; j < y; j++) printf(" %d", ci[j]);
	printf(" >\n");
      }  
      printf("\n");
    }
  }
}

void abg_encode (size, base, j, res)
     int size, base[], j, res[];
{
  int i;
  
  while (size-- > 0) {
    i = base[size];
    res[size] = j % i;
    j = j/i;
  }
}

int abg_decode (size, base, vec)
     int size, base[], vec[];
{
  int i, j;
  j = 0;
  for (i = 0; i < size; i++) j = j * base[i] + vec[i];
  return j;
}

void fix_abg_g ()
{
  int i, j;

  /** Suppose the identity element of the group is 0. **/
  ABG_g[0] = 0;
  for( i = 1; i < m; i++ ) ABG_g[i] = (-1);
  for( i = 1; i < m; i++ )
    if ( ABG_g[i] < 0 ) {
      for( j = 1; j < m; j++ )
	if (ABG_f[i][j] == 0) {
	  ABG_g[i] = j;
	  ABG_g[j] = i;
	}
    }
}

void prn_abg_table ()
{
  int   i, j;

  printf("The Group found:\n\n");
  for(i = 0; i < m; i++) {
    for(j = 0; j < m; j++)
	printf(" %2d", ABG_f[i][j]);
    printf("\n");
  }
  printf("\nthe inverse function:\n");
  for(i = 0; i < m; i++)
	printf(" %2d",ABG_g[i]);
  printf("\n\n");
}

/*** the following function is called from init_qgroups in qgroup.c */
void init_cgroups ()
{
  if (get_addk()) { 
    addk_num = get_addk();
    if ((QGROUP-INCOMPLETE) % addk_num) {
      printf("%d does not divide %d\n", addk_num, QGROUP-INCOMPLETE);
      exit(0);
    }
  } else addk_num = 1;

  if (CYCLIC == 'C') {
    nk2m = (QGROUP + INCOMPLETE + INCOMPLETE)*(QGROUP - INCOMPLETE);
    Kmax = nk2m + nk2m + addk_num*(QGROUP - INCOMPLETE);
    Max_atom = addk_num * Kmax;
  } else {
    Kmax = ((QGROUP + 2 * INCOMPLETE) * (QGROUP - INCOMPLETE));
    Max_atom = addk_num * Kmax;
  }

  if (PIGEON == 2 && QUEEN <= 38) {
    n_cube = Max_atom;
    Max_atom += n_cube;  
  } 

  init_same_hole();
  if (RAMSEY>0) cqg_locate_holes();
  cgroup_find_seed();
  gen_abg_table();
}

void print_encoding ()
{
  int k, x, y, z, u, v;

  prn_abg_table ();

  u = (QUEEN == 30)? 3 : 1;

  for (v = 0; v <= u; v++) 
  for (k = 0; k < addk_num; k++) {
      for (y = 0; y < n; y++) 
    for (x = 0; x < m; x++)
	printf("ALPHA(%d, %d, %d) = %d\n", k, x, y, ALPHA(k, x, y)+v*SQUARE2);
    printf("\n");

    for (x = m; x < n; x++)
      for (y = 0; y < m; y++) 
	printf("BETA(%d, %d, %d) = %d\n", k, x, y, BETA(k, x, y)+v*SQUARE2);
    printf("\n");

    for (x = m; x < n; x++)
      for (y = 0; y < m; y++) 
	printf("GAMMA(%d, %d, %d) = %d\n", k, x, y, GAMMA(k, x, y)+v*SQUARE2);
    printf("\n");

    if (CYCLIC == 'C') {
      for (x = 0; x < n+INCOMPLETE; x++)
	for (y = 0; y < m; y++) 
	  printf("THETA(%d, %d, %d) = %d\n", k, x, y, THETA(k, x, y)+v*SQUARE2);
      printf("\n");
      for (x = 0; x < addk_num; x++)
	for (y = 0; y < m; y++) 
	  printf("DELTA(%d, %d, %d) = %d\n", k, x, y, DELTA(k, x, y)+v*SQUARE2);
      printf("\n");
    }
  }

  if (PIGEON == 2) {
    for (z = 0; z < n; z++) 
      for (x = 0; x < n; x++)
	for (y = 0; y < n; y++) 
	  printf("OMEGA(%d, %d, %d) = %d\n", x, y, z, OMEGA(x, y, z));
    printf("\n");
  }
}


/**** The following function generates the input clauses for
  cyclic quaisgroup problems. ****/

int cyclic_qgroup_clauses ()
     /* return 1 if an empty clause is found; otherwise, 0 */
{
  int cl_arr [ MAX_ATOM ], sign_arr [ MAX_ATOM ];
  int i, x, y, u, v, k;

  /* cqg_extra_unit_cls();*/

  if (cqg_unit_clauses()) return 1;

  if (extra_cyclic_cls(cl_arr, sign_arr)) return 1;
  
  if (cgroup_seed_cls(cl_arr, sign_arr)) return 1;

  if (FLAG == 200 && cqg_multi2_cls(cl_arr, sign_arr)) return 1;

  /* isomorphism cutting */
  if (LINE < 10) {
    if (cqg_iso_cls(cl_arr, sign_arr)) return 1; 
  } else 
    /* 0 * u = x, 0 * v = y, x < y => u < v  for x,y >= m */
    /*
    for (y = n1; y > m; y--)
      for (x = y-1; x >= m; x--) 
	for (u = m-1; u > 1; u--) 
	  for (v = u-1; v > 0; v--) 
	    for (k = 0; k < addk_num; k++) {
	      if (insert_cl_2(ALPHA(k, v, y), ALPHA(k, u, x), 0,
			      cl_arr, sign_arr) == 1)
		return 1;
	    }
	    */

  /* 0 * x = y, 0 * u = v => x - y != u - v */
  for (k = 0; k < addk_num; k++)
    for (x = m-1; x > 0; x--) if (is_same_hole(x, k) == 0)
      for (u = x-addk_num; u >= 0; u -= addk_num) if (is_same_hole(u, k) == 0) 
	for (y = 0; y < m; y++) 
	  if (is_same_hole(y, k) == 0 && is_same_hole(x, y) == 0) {
	    v = ABG_f[DIFF(y, x)][u];
	    if (is_same_hole(v, k) == 0 &&
		insert_cl_2(ALPHA(k, x, y), ALPHA(k, u, v),
			    0, cl_arr, sign_arr))
	      return 1;
	  }

  for (k = 0; k < addk_num; k++) 
    for (x = n1; x >= 0; x--) if (is_same_hole(x, k) == 0)
      for (y = (x >= m)? m-1 : n1; y > 0; y--) 
	if ((is_same_hole(y, k) == 0) && (is_same_hole(y, x) == 0))
	for (v = y-1; v >= 0; v--) 
	if ((is_same_hole(v, k) == 0) && (is_same_hole(v, x) == 0)) {

	  /* 0 * x = y and 0 * x = v imply y = v. */
	  if (insert_cl_2(TRIPLE2KEY(k, x, y),
			  TRIPLE2KEY(k, x, v),
			  FF, cl_arr, sign_arr) == 1)
	    return 1;

	  /* 0 * y = x and 0 * v = x imply y = v. */
	  if (insert_cl_2(TRIPLE2KEY(k, y, x),
			  TRIPLE2KEY(k, v, x),
			  FF, cl_arr, sign_arr) == 1)
	    return 1;

	  if (x >= m) {
	    /* x * 0 = y and x * 0 = v imply y = v. */
	    if (insert_cl_2(GAMMA(k, x, y), GAMMA(k, x, v), 
			    FF, cl_arr, sign_arr) == 1)
	      return 1;
	  } else {
	    /* y * 0 = x and v * 0 = x imply y = v. */
	    if (insert_cl_2(TRIPLE2KEY(y, k, x),
			    TRIPLE2KEY(v, k, x),
			    FF, cl_arr, sign_arr) == 1)
	      return 1;

	  /* y * x = 0 and v * x = 0 imply y = v. */
	    if (insert_cl_2(TRIPLE2KEY(y, x, k),
			    TRIPLE2KEY(v, x, k),
			    FF, cl_arr, sign_arr) == 1)
	      return 1;
	  }
	}

  for (k = 1; k < addk_num; k++) 
    for (v = 0; v < k; v++) 
      for (y = m; y < n; y++) 
	for (x = 0; x < m; x++) 
	  for (u = 0; u < m; u++) if (x % addk_num == u % addk_num) {
  
	    /* v * y = x and k * y = u imply k = v. */
	    if (insert_cl_2(TRIPLE2KEY(k, y, x),
			    TRIPLE2KEY(v, y, u),
			    FF, cl_arr, sign_arr) == 1)
	      return 1;

	    /* v * x = y and k * u = y imply k = v. */
	    if (insert_cl_2(TRIPLE2KEY(k, u, y),
			    TRIPLE2KEY(v, x, y),
			    FF, cl_arr, sign_arr) == 1)
	      return 1;

	    /* y * v = x and y * k = u imply k = v. */
	    if (insert_cl_2(TRIPLE2KEY(y, k, x),
			    TRIPLE2KEY(y, v, u),
			    FF, cl_arr, sign_arr) == 1)
	      return 1;
	  }
  
  if (cqg_cls(cl_arr, sign_arr)) { return 1; }
  
  if (multi_squares() == 1) { 
    set_double_cl(0); 
    if (corthogonal_cls(1, cl_arr, sign_arr)) return 1; 
    set_double_cl(1);
  } else if (multi_squares() == 2) { 
    set_double_cl(0); 
    if (corthogonal_cls(3, cl_arr, sign_arr)) return 1; 
    set_double_cl(2);
  }

  /*  * is closed.
  (0*j=1) v ... v (0*j=n)     (1<=j<=n)  value of product
  (0*1=j) v ... v (0*n=j)     (1<=j<=n)  right solution
  */

  for (k = 0; k < addk_num; k++)
  for (x = n1; x >= 0; x--) {
    if (x >= m) {

      i = 0;
      for (v = m-1; v >= 0; v--) 
	if (is_same_hole(k, v) == 0) {
	  cl_arr[i] = TRIPLE2KEY(x, k, v); 
	  sign_arr[cl_arr[i]] = 1;
	  i++;
	}

      if (qg_insert_clause( cl_arr, sign_arr, i) == 1)	
	return 1;
      
      i = 0;
      for (v = m-1; v >= 0; v--) 
	if (is_same_hole(k, v) == 0) {
	  cl_arr[i] = TRIPLE2KEY(k, x, v);
	  sign_arr[cl_arr[i]] = 1;
	  i++;
	}

      if (qg_insert_clause( cl_arr, sign_arr, i) == 1)	
	return 1;
      
      i = 0;
      for (v = m-1; v >= 0; v--) 
	if (is_same_hole(k, v) == 0) {
	  cl_arr[i] = TRIPLE2KEY(k, v, x);
	  sign_arr[cl_arr[i]] = 1;
	  i++;
	}

      if (qg_insert_clause( cl_arr, sign_arr, i) == 1)	
	return 1;

    } else if (is_same_hole(k, x) == 0) {

      i = 0;
      for (v = n1; v >= 0; v--) 
	if (v >= m || 
	    (is_same_hole(k, v) == 0 &&
	     is_same_hole(x, v) == 0)) {
	  cl_arr[i] = TRIPLE2KEY(k, x, v);
	  sign_arr[cl_arr[i]] = 1;
	  i++;
	}
      if (qg_insert_clause( cl_arr, sign_arr, i) == 1)	
	return 1;

      i = 0;
      for (v = n1; v >= 0; v--) 
	if (v >= m || 
	    (is_same_hole(k, v) == 0 &&
	     is_same_hole(x, v) == 0)) {
	  cl_arr[i] = TRIPLE2KEY(k, v, x);
	  sign_arr[cl_arr[i]] = 1;
	  i++;
	}
      if (qg_insert_clause( cl_arr, sign_arr, i) == 1)	
	return 1;
    }
  }

  return 0;
}

corthogonal_cls (num, cl_arr, sign_arr)
     int num, cl_arr [], sign_arr [];
     /* x * y = u, z * w = u, x # y = v, z # w = v -> x = z OR y = w */
{
  int k, x, y, z, u, v, w, a, b, c;

  /* no symmtry between square 2 and square 3 
  if (num == 3) {
    for (y = 2; y < n; y++) 
      for (z = 1; z < y; z++) 
	if (insert_cl_2(SQUARE2+TRIPLE2KEY(0, 1, y), 
			SQUARE2+SQUARE2+TRIPLE2KEY(0, 1, z), 
			0, cl_arr, sign_arr))
	  return 1;
  }
  */

  while (num-- > 0) {
    if (num == 1) { a = 0; b = c = SQUARE2+SQUARE2; }
    else if (num == 2) { a = c = SQUARE2; b = SQUARE2+SQUARE2; }
    else { a = c = 0; b = SQUARE2; }

    for (k = 0; k < addk_num; k++) for (u = 1; u < m; u++) 
      for (x = m; x < n; x++) {

	for (y = m; y < n; y++) {
	  /* (0 * u = x ==> u * 0 != y for x, y >= m */
	  if (insert_cl_2(a+TRIPLE2KEY(k, u, x),
			  b+TRIPLE2KEY(k, u, y),
			  FF, cl_arr, sign_arr)) 
	    return 1;
	}

	/* (0 * x = u ==> x * 0 != u for x >= m */
	if (insert_cl_2(a+TRIPLE2KEY(k, x, u),
			b+TRIPLE2KEY(k, x, u),
			FF, cl_arr, sign_arr)) 
	  return 1;
      }

    for (u = 1; u < m; u++) {
      if (NHOLE) 
	/* difference conditions:
	   (0 * x = u) => (0 *213 x) != v for u == v mod h */
	for (x = n1; x >= 0; x--) 
	  for (v = u % NHOLE; v < m; v += NHOLE) {
	    if (insert_cl_2(a+TRIPLE2KEY(k, x, u),
			    b+TRIPLE2KEY(k, x, v),
			    0, cl_arr, sign_arr))
	      return 1;
	  }
      else
	for (w = m-1; w > 0; w--) if (w != u)
	  if (insert_cl_2(a+TRIPLE2KEY(k, w, u), 
			  b+TRIPLE2KEY(k, w, u),
			  0, cl_arr, sign_arr))
	    return 1;
    }

    if (CYCLIC == 'C') {

      for (k = 0; k < addk_num; k++)
	for (u = m-1; u >= 0; u--) {
	  int uk = u%addk_num;
	  for (v = m-1; v >= 0; v--) {
	    int uv = DIFF(u,v);
	    for (x = n1; x >= m; x--) {
	      if (insert_cl_all_3(a+BETA(k, x, u), 
				  b+BETA(k, x, v), 
				  c+DELTA(uk, k, uv),
				  1, cl_arr, sign_arr))
		return 1;

	      if (insert_cl_all_3(a+BETA(k, x, u), 
				  b+BETA(k, x, v), 
				  c+THETA(uk, x, uv),
				  1, cl_arr, sign_arr))
		return 1;

	      if (insert_cl_all_3(a+GAMMA(k, x, u),
				  b+GAMMA(k, x, v), 
				  c+THETA(uk, x+INCOMPLETE, uv),
				  1, cl_arr, sign_arr))
		return 1;

	      if (insert_cl_all_3(a+GAMMA(k, x, u),
				  b+GAMMA(k, x, v), 
				  c+DELTA(uk, k, uv),
				  1, cl_arr, sign_arr))
		return 1;
	    }
	    
	    for (x = m-1; x >= 0; x--) {
	      if (insert_cl_all_3(a+TRIPLE2KEY(k, x, u), 
				  b+TRIPLE2KEY(k, x, v), 
				  c+THETA(uk, x, uv),
				  1, cl_arr, sign_arr))
		return 1;

	      if (insert_cl_all_3(a+TRIPLE2KEY(k, x, u), 
				  b+TRIPLE2KEY(k, x, v), 
				  c+DELTA(uk, k, uv),
				  1, cl_arr, sign_arr))
		return 1;

	      /*
	      if (x == 9 && uv == 5 && uk) {
		if ((k == 0 && u == 7) || (k == 1 && u == 1))
		  printf("WWW <%d %d %d>+%d vs <%d %d %d>+%d => (%d %d %d)+%d\n",
			 k, x, u, a, k, x, v, b, uk, k, uv, c);
	      }
	      */
	    }
	  }
	}

      if (unique_cover_clauses(c, cl_arr, sign_arr)) return 1;

    } else {

      for (x = n1; x > 0; x--)
	for (y = (x >= m)? m-1 : n1; y >= 0; y--) if (x != y) {
	  
	  for (z = (x < m && y < m)? n1 : m-1; z >= 0; z--) 
	    if (z != x && z != y && 
		insert_cl_2(b+TRIPLE2KEY(x, z, y), 
			    a+TRIPLE2KEY(x, z, y), 
			    0, cl_arr, sign_arr))
	      return 1;

	  for (z = x-1; z >= 0; z--) 
	    for (w = (z >= m)? m-1 : n1; w >= 0; w--) if (y != w && z != w) 
	      for (u = (x < m && y < m && z < m && w < m)? n1 : m-1;
		   u >= 0; u--) 
		for (v = (x < m && y < m && z < m && w < m)? n1 : m-1;
		     v >= 0; v--) if (v != x && v != y && v != z && v != w)
		       if (insert_cl_4(b+TRIPLE2KEY(x, y, u),
				       b+TRIPLE2KEY(z, w, u), 
				       a+TRIPLE2KEY(x, y, v), 
				       a+TRIPLE2KEY(z, w, v), 
				       0, cl_arr, sign_arr))
			 return 1;
	}
    }
  }
  return 0;
}

int cqg_iso_cls (cl_arr, sign_arr)
     int cl_arr[], sign_arr[];
{
  int x, y, u, v, k;
  
  /* 0 * u = x, 0 * v = y, x < y => u < v  for x,y >= m */
  if (LINE == 3 || LINE == 5 || LINE > 6)
  for (y = n1; y > m; y--)
    for (x = y-1; x >= m; x--) 
      for (u = m-1; u > 1; u--) 
	for (v = u-1; v > 0; v--) 
	  for (k = 0; k < addk_num; k++) {
	    if (insert_cl_2(ALPHA(k, v, y), ALPHA(k, u, x), 0,
			    cl_arr, sign_arr) == 1)
	      return 1;
	  }

  /* 0 * x = u, 0 * y = v, x < y => u < v  for x,y >= m */
  if (LINE == 2 || LINE == 3 || LINE > 5)
  for (y = n1; y > m; y--)
    for (x = y-1; x >= m; x--) 
      for (u = m-1; u > 1; u--) 
	for (v = u-1; v > 0; v--) 
	  for (k = 0; k < addk_num; k++) {
	    if (insert_cl_2(BETA(k, y, v), BETA(k, x, u), 0,
			    cl_arr, sign_arr) == 1)
	      return 1;
	  }

  /* x * 0 = u, y * 0 = v, x < y => u < v  for x,y >= m */
  if (LINE > 3)
  for (y = n1; y > m; y--)
    for (x = y-1; x >= m; x--) 
      for (u = m-1; u > 1; u--) 
	for (v = u-1; v > 0; v--) 
	  for (k = 0; k < addk_num; k++) {
	    if (insert_cl_2(GAMMA(k, y, v), GAMMA(k, x, u), 0,
			    cl_arr, sign_arr) == 1)
	      return 1;
	  }

  return 0;
}

int cqg_multi2_cls (cl_arr, sign_arr)
     int cl_arr[], sign_arr[];
{
  int x, y, k;
  
  if (m % 2) { printf("The order of the group is not even\n"); return 0; }

  /* k * x = y => -k * -x = -y */
  for (k = 0; k < addk_num; k++) 
    for (x = 1; x < m/2; x++) 
      for (y = 1; y < m/2; y++) {
	if (insert_cl_2(TRIPLE2KEY(k, x, y), 
			TRIPLE2KEY(m-k, m-x, m-y), 
			TT, cl_arr, sign_arr) == 1)
	  return 1;
      }
  return 0;
}

int cqg_cls (cl_arr, sign_arr)
     int cl_arr[], sign_arr[];
{
  if (QUEEN == 0) { if (cqg0(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 1) { if (cqg1(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 2) { if (cqg2(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 3) { if (cqg3(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 4) { if (cqg4(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 5) { if (cqg5(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 6) { if (cqg6(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 7) { if (cqg7(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 8) { if (cqg8(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 9) { if (cqg9(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 10) { if (qg11(cl_arr, sign_arr)) return 1;
           if (PIGEON == 2 && rpmd_cls(cl_arr, sign_arr)) return 1;
                          if (qg12(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 12) { if (cqg12(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 13) { if (cqg13(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 14) { if (cqg14(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 16) { if (cqg16(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 17) { if (cqg0(cl_arr, sign_arr)) return 1; 
			  if (cdiagonal_cls(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 18) { if (cqg2(cl_arr, sign_arr)) return 1; 
			  if (cdiagonal_cls(cl_arr, sign_arr)) return 1; }
  /*
  else if (QUEEN == 88) { if (cqg1(cl_arr, sign_arr)) return 1; 
			  if (cdiagonal_cls2(cl_arr, sign_arr)) return 1; }
  */
  else if (QUEEN == 21) { set_double_cl(0);
			  if (cqg0(cl_arr, sign_arr, 1)) return 1; 
			  set_double_cl(1);
			}
  else if (QUEEN == 22) { set_double_cl(0);
                          if (qg14_resolve(cl_arr, sign_arr)) return 1;
			  if (qg14(cl_arr, sign_arr)) return 1;
			  set_double_cl(1);
			}
  else if (QUEEN == 23) { if (cqg13(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 24) { if (cqg24(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 31) { if (cqg13(cl_arr, sign_arr)) return 1;
                          if (cqg0(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 33) { if (cqg3(cl_arr, sign_arr)) return 1; 
			  if (cdiagonal_cls(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 37) { if (qg37(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 38) { if (qg38(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 44) { if (qg44(cl_arr, sign_arr)) return 1; }
  /* if (cdiagonal_cls(cl_arr, sign_arr)) return 1; } */
  else if (QUEEN == 45) { if (cqg0(cl_arr, sign_arr)) return 1; 
			  if (csymm_trasversal(cl_arr, sign_arr)) return 1; } 
  else if (QUEEN == 46) { if (cqg1(cl_arr, sign_arr)) return 1; 
			  if (cdiagonal_cls321(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 50) { if (cqg50(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 63) { if (cqg13(cl_arr, sign_arr)) return 1; 
			  if (cqg63(cl_arr, sign_arr)) return 1; } 
  else if (QUEEN == 66) { if (qg66(cl_arr, sign_arr)) return 1; 
			  if (qg13(cl_arr, sign_arr)) return 1; 
			  if (qg63(cl_arr, sign_arr)) return 1; } 
  else if (QUEEN == 69) { if (qg69(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 78) { if (qg78(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 79) { if (qg79(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 83) { if (symmetric_cls(0, cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 88) { if (qg88(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 89) { if (qg89(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 91) { if (cqg91(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 92) { if (cqg91(cl_arr, sign_arr)) return 1;
			  if (cqg0(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 95) { if (cqg0(cl_arr, sign_arr)) return 1;
			  if (cqg102(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 99) { if (cqg9(cl_arr, sign_arr)) return 1;
			  if (cdiagonal_cls321(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 100) { gen_abg_table();
                           if (qg100(cl_arr, sign_arr)) return 1; 
                           if (cqg0(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 101) { if (cqg101(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 102) { if (cqg102(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 103) { if (cqg0(cl_arr, sign_arr)) return 1;
			   if (cqg101(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 104) { if (qg104(cl_arr, sign_arr)) return 1; }
  else if (QUEEN > 110) { if (co_cycle_cls(cl_arr, sign_arr)) return 1; }
 
  return 0;
}

cqg0 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* x * y = u, z * w = u, y * x = v, w * z = v -> x = z, y = w */
{
  int x, y, z, u, v, w, k;

  for (k = 0; k < addk_num; k++) {

    for (x = m; x < n; x++) {
      if (!IDEMPOTENT)
	if (insert_cl_1(ALPHA(k, k, x), FF)) return 1;

      for (u = 1; u < m; u++) {
	/* (0 * x = u ==> x * 0 != u for x >= m */
	if (insert_cl_2(TRIPLE2KEY(k, x, u),
			TRIPLE2KEY(x, k, u),
			FF, cl_arr, sign_arr)) 
	  return 1;

	for (y = m; y < n; y++) {
	  /* (0 * u = x ==> u * 0 != y for x, y >= m */
	  if (insert_cl_2(TRIPLE2KEY(k, u, x),
			  TRIPLE2KEY(u, k, y),
			  FF, cl_arr, sign_arr)) 
	    return 1;
	}
      }
    }

    for (u = 1; u < m; u++) {
      if (NHOLE) 
	/* difference conditions:
	   (0 * x = u) => (0 *213 x) != v for u == v mod h */
	for (x = n1; x >= 0; x--) 
	  for (v = u % NHOLE; v < m; v += NHOLE) {
	    if (insert_cl_2(TRIPLE2KEY(k, x, u),
			    TRIPLE2KEY(x, k, v),
			    0, cl_arr, sign_arr))
	      return 1;
	  }
      else
	for (w = m-1; w > 0; w--) if (w != u && w != k)
	  if (insert_cl_2(TRIPLE2KEY(k, w, u), 
			  TRIPLE2KEY(w, k, u),
			  0, cl_arr, sign_arr))
	    return 1;
    }
  }

  if (CYCLIC == 'B') {
    for (k = 0; k < addk_num; k++) for (x = n1; x > 0; x--) 
      for (y = (x >= m)? m-1 : n1; y >= 0; y--) 
	if (x != y && is_same_hole(x, y) == 0) 
	  for (z = x-1; z >= 0; z--) 
	    for (w = (z >= m)? m-1 : n1; w >= 0; w--) 
	      if (y != w && w != z && is_same_hole(w, z) == 0)
		for (u = (x < m && y < m && z < m && w < m)? n1 : m-1;
		     u >= 0; u--) 
		  if (u != x && u != y && u != z && u != w &&
		      is_same_hole(u, x) == 0 &&
		      is_same_hole(u, y) == 0 &&
		      is_same_hole(u, z) == 0 &&
		      is_same_hole(u, w) == 0)
		    for (v = (x < m && y < m && z < m && w < m)? n1 : m-1;
			 v >= 0; v--) 
		      if (v != x && v != y && v != z && v != w && 
			  is_same_hole(v, x) == 0 &&
			  is_same_hole(v, y) == 0 &&
			  is_same_hole(v, z) == 0 &&
			  is_same_hole(v, w) == 0) {
			if (insert_cl_4(TRIPLE2KEY(x, y, u),
					TRIPLE2KEY(z, w, u),
					TRIPLE2KEY(y, x, v),
					TRIPLE2KEY(w, z, v),
					0, cl_arr, sign_arr))
			  return 1;
		      }

    for (k = 0; k < addk_num; k++) for (w = k+1; w < addk_num; w++)
      for (y = 0; y < m; y++) if (y != k)
	for (z = 0; z < m; z++) if (z != w) {

	  for (u = m; u < n; u++) 
	    for (x = m; x < n; x++) {
	      if (insert_cl_all_3(TRIPLE2KEY(k, y, x),
				  TRIPLE2KEY(w, z, x),
				  TRIPLE2KEY(y, k, u),
				  0, cl_arr, sign_arr))
		return 1;
	      if (insert_cl_all_3(TRIPLE2KEY(y, k, x),
				  TRIPLE2KEY(z, w, x),
				  TRIPLE2KEY(k, y, u),
				  0, cl_arr, sign_arr))
		return 1;
	    }

	  for (x = m; x < n; x++) for (u = 0; u < m; u++) 
	    if (is_same_hole(u, k) == 0 &&
		is_same_hole(u, y) == 0) 
	      for (v = u%addk_num; v < m; v += addk_num)
		if (is_same_hole(v, w) == 0 &&
		    is_same_hole(v, z) == 0) {

		  if (insert_cl_4(TRIPLE2KEY(k, y, x),
				  TRIPLE2KEY(w, z, x),
				  TRIPLE2KEY(y, k, u),
				  TRIPLE2KEY(z, w, v),
				  0, cl_arr, sign_arr))
		    return 1;

		  if (insert_cl_4(TRIPLE2KEY(y, k, x),
				  TRIPLE2KEY(z, w, x),
				  TRIPLE2KEY(k, y, u),
				  TRIPLE2KEY(w, z, v),
				  0, cl_arr, sign_arr))
		    return 1;
		}

	  for (x = 0; x < m; x++) 
	    if (is_same_hole(k, x) == 0 &&
		is_same_hole(w, x) == 0 &&
		is_same_hole(y, x) == 0 &&
		is_same_hole(z, x) == 0)
	      for (u = 0; u < m; u++) 
		if (is_same_hole(u, k) == 0 &&
		    is_same_hole(u, y) == 0 &&
		    is_same_hole(u, w) == 0 &&
		    is_same_hole(u, z) == 0) {

		  if (insert_cl_4(TRIPLE2KEY(k, y, x),
				  TRIPLE2KEY(w, z, x),
				  TRIPLE2KEY(y, k, u),
				  TRIPLE2KEY(z, w, u),
				  0, cl_arr, sign_arr))
		    return 1;
		}
	}
    
  } else { /* CYCLIC == 'C' */ 
    
    for (k = 0; k < addk_num; k++) for (u = 0; u < m; u++) {
      int uk = u%addk_num;
      for (v = 0; v < m; v++) {
	int uv = DIFF(u,v);
	for (x = n1; x >= m; x--) {

	  if (insert_cl_all_3(GAMMA(k, x, u), 
			      BETA(k, x, v), 
			      THETA(uk, x+INCOMPLETE, uv),
			      1, cl_arr, sign_arr))
	    return 1;

	  if (insert_cl_all_3(GAMMA(k, x, u), 
			      BETA(k, x, v), 
			      DELTA(uk, k, uv),
			      1, cl_arr, sign_arr))
	    return 1;

	  if (insert_cl_all_3(GAMMA(k, x, v), 
			      BETA(k, x, u), 
			      THETA(uk, x, uv),
			      1, cl_arr, sign_arr))
	    return 1;

	  if (insert_cl_all_3(GAMMA(k, x, v), 
			      BETA(k, x, u), 
			      DELTA(uk, k, uv),
			      1, cl_arr, sign_arr))
	    return 1;
	}

	for (w = 0; w < m; w++) {

	  if (insert_cl_all_3(TRIPLE2KEY(k, w, u), 
			      TRIPLE2KEY(w, k, v), 
			      THETA(uk, w, uv),
			      1, cl_arr, sign_arr))
	    return 1;
	
	  if (insert_cl_all_3(TRIPLE2KEY(k, w, u), 
			      TRIPLE2KEY(w, k, v), 
			      DELTA(uk, k, uv),
			      1, cl_arr, sign_arr))
	    return 1;
	}
      }
    }

    if (unique_cover_clauses(0, cl_arr, sign_arr)) return 1;
  }

  return 0;
}

cqg10 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* x * y = u, z * w = u, y * x = v, w * z = v -> x = z, y = w */
{
  int x, y, z, u, v, w;

  if (cqg0(cl_arr, sign_arr)) return 1;

  for (x = n1; x > 0; x--)
    for (y = (x >= m)? m-1 : n1; y >= 0; y--) 
      for (z = x-1; z >= 0; z--) 
	for (w = (z >= m)? m-1 : n1; w >= 0; w--) if (y != w)
	  for (u = (x < m && y < m && z < m && w < m)? n1 : m-1;
	       u >= 0; u--) 
	    for (v = (x < m && y < m && z < m && w < m)? n1 : m-1;
		 v >= 0; v--) 
	      if (insert_cl_4(TRIPLE2KEY(x, y, u),
			      TRIPLE2KEY(z, w, u), 
			      TRIPLE2KEY(neg(y), neg(x), v), 
			      TRIPLE2KEY(neg(w), neg(z), v), 
			      0, cl_arr, sign_arr))
		return 1;
  return 0;
}
	
cqg1 (cl_arr, sign_arr)
  int cl_arr [], sign_arr [];
	/* x * y = u, z * w = u, v * y = x, v * w = z -> x = z, y = w */
{
  if (CYCLIC == 'B') {
    return (qg1_2000(cl_arr, sign_arr));
  } else { /* CYCLIC == 'C' */ 
    return (qg1_3000(cl_arr, sign_arr));
  }
}

int qg1_2000 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* x * y = u, z * w = u, v * y = x, v * w = z -> x = z, y = w */
{
  int x, y, z, u, v, w;
 
  for (x = n1; x >= 0; x--)
    for (y = (x >= m)? m-1 : n1; y >= 0; y--) if (x != y) {

      for (z = (x < m && y < m)? n1 : m-1; z >= 0; z--) 
	if (z != x && z != y)
	  if (RAMSEY) {
	    for (u = n1; u >= 0; u--) 
	      if (is_same_hole(y, u) &&
		  insert_cl_2(TRIPLE2KEY(x, z, u), 
			      TRIPLE2KEY(y, z, x), 
			      0, cl_arr, sign_arr))
		return 1; 
	  } else {
	    if (insert_cl_all_3(TRIPLE2KEY(y, y, y),
				TRIPLE2KEY(x, z, y), 
				TRIPLE2KEY(y, z, x), 
				0, cl_arr, sign_arr))
	      return 1; 
	  }
      
      for (z = x-1; z >= 0; z--) 
	for (w = (z >= m)? m-1 : n1; w >= 0; w--) if (y != w)
	  for (u = (x < m && y < m && z < m && w < m)? n1 : m-1;
	       u >= 0; u--) 
            for (v = (x < m && y < m && z < m && w < m)? n1 : m-1;
		 v >= 0; v--)
	      if (insert_cl_4(TRIPLE2KEY(x, y, u),
			      TRIPLE2KEY(z, w, u),
			      TRIPLE2KEY(v, y, x), 
			      TRIPLE2KEY(v, w, z), 
			      0, cl_arr, sign_arr))
		return 1;
    }
  return 0;
}

qg1_3000 (cl_arr, sign_arr)
     int cl_arr[], sign_arr[];
{
 int x, y, u, v, w, k;

 for (k = 0; k < addk_num; k++) {
   for (u = 0; u < m; u++) {

     /*
       for (x = m; x < n; x++) 
       for (y = m; y < n; y++) {
       if (insert_cl_2(TRIPLE2KEY(y, u, k),
       TRIPLE2KEY(k, u, x),
       FF, cl_arr, sign_arr)) 
       return 1;
       
       if (insert_cl_2(TRIPLE2KEY(k, x, u), 
       TRIPLE2KEY(u, y, k), 
       FF, cl_arr, sign_arr))
       return 1;
       }*/
     for (y = m; y < n; y++) {
       if (insert_cl_2(TRIPLE2KEY(y, u, k),
		       TRIPLE2KEY(k, u, y),
		       FF, cl_arr, sign_arr)) 
	 return 1;
       
       if (insert_cl_2(TRIPLE2KEY(k, y, u), 
		       TRIPLE2KEY(u, y, k), 
		       FF, cl_arr, sign_arr))
	 return 1;
     }
     
     if (NHOLE) {
       /* difference conditions:
	  (0 * x = u) => (0 *321 x) != v for u == v mod h */
       for (v = u % NHOLE; v < m; v += NHOLE) 
	 for (x = n1; x >= 0; x--) {
	   if (insert_cl_2(TRIPLE2KEY(k, x, u),
			   TRIPLE2KEY(v, x, k), 
			   0, cl_arr, sign_arr))
	     return 1;
	   if ((x >= m) &&
	       insert_cl_2(TRIPLE2KEY(x, k, u),
			   TRIPLE2KEY(v, k, x), 
			   0, cl_arr, sign_arr))
	     return 1;
	 }
     } else if (IDEMPOTENT)
       for (w = m-1; w > k; w--) 
	 if (insert_cl_2(TRIPLE2KEY(k, w, u), 
			 TRIPLE2KEY(u, w, k),
			 0, cl_arr, sign_arr))
	   return 1;
   }
 }

 for (k = 0; k < addk_num; k++) for (u = m-1; u >= 0; u--) 
   for (v = m-1; v >= 0; v--) {
     int uv = DIFF(u,v);
     
     for (x = n1; x >= m; x--) {
       if (insert_cl_all_3(TRIPLE2KEY(k, x, u), 
			   TRIPLE2KEY(v, x, k),
			   THETA(u%addk_num, x, uv),
			   1, cl_arr, sign_arr))
	 return 1;

       if (insert_cl_all_3(TRIPLE2KEY(x, k, u), 
			   TRIPLE2KEY(v, k, x),
			   THETA(u%addk_num, x+INCOMPLETE, uv),
			   1, cl_arr, sign_arr))
	 return 1;
     }

     /* bug: for m = 12, addk = 2:
	0.3=11, 0*3=4, 7.9=11, 7*9=4 */
     for (w = m-1; w >= 0; w--)
       if (insert_cl_all_3(TRIPLE2KEY(k, w, u), 
			   TRIPLE2KEY(v, w, k), 
			   THETA(u%addk_num, w, uv),
			   1, cl_arr, sign_arr))
	 return 1;
   }

 if (unique_cover_clauses(0, cl_arr, sign_arr)) return 1;

 /* this set of clauses is heavy */
 if (addk_num > 1)
 for (k = 0; k < addk_num; k++) 
   for (u = 0; u < m; u++) 
     for (y = k+1; y < m; y++)
       for (x = m; x < n; x++)
	 for (v = 0; v < m; v++)
	   for (w = 0; w < n; w++) {
	     if (insert_cl_4(TRIPLE2KEY(k, u, x), 
			     TRIPLE2KEY(y, v, x), 
			     TRIPLE2KEY(w, u, k),
			     TRIPLE2KEY(w, v, y),
			     0, cl_arr, sign_arr))
	       return 1;
	   }

 return 0;
}

cqg2 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* x * y = u, z * w = u, y * v = x, w * v = z -> x = z, y = w */
{
  int k, x, y, z, u, v, w;

  for (k = 0; k < addk_num; k++)
  for (u = 1; u < m; u++) {

    for (x = m; x < n; x++)
      for (y = m; y < n; y++) {
	if (insert_cl_2(TRIPLE2KEY(u, y, k),
			TRIPLE2KEY(k, u, x),
			FF, cl_arr, sign_arr)) 
	  return 1;
      }

    for (x = n1; x >= m; x--) {
      if (insert_cl_2(TRIPLE2KEY(k, x, u), 
		      TRIPLE2KEY(x, u, k), 
		      0, cl_arr, sign_arr))
	return 1;
      if (insert_cl_2(TRIPLE2KEY(x, u, k), 
		      TRIPLE2KEY(u, k, x), 
		      0, cl_arr, sign_arr))
	return 1;
    }

    if (NHOLE) 
      /* difference conditions:
	 (k * x = u) => (k *312 x) != v for u == v mod h */
      for (v = u % NHOLE; v < m; v += NHOLE) 
	for (x = n1; x >= 0; x--) {
	  if (insert_cl_2(TRIPLE2KEY(k, x, u),
			  TRIPLE2KEY(x, v, k),
			  0, cl_arr, sign_arr))
	    return 1;
	  if ((x >= m) &&
	      insert_cl_2(TRIPLE2KEY(x, k, u),
			  TRIPLE2KEY(k, v, x),
			  0, cl_arr, sign_arr))
	    return 1;
	}
    else
      for (w = n1; w > 0; w--) if (w != u)
	if (insert_cl_2(TRIPLE2KEY(k, u, w), 
			TRIPLE2KEY(u, w, k),
			0, cl_arr, sign_arr))
	  return 1;
  }

  if (CYCLIC == 'B') {
    for (x = n1; x > 0; x--) 
      for (y = (x >= m)? m-1 : n1; y >= 0; y--) 
	if (x != y && is_same_hole(x, y) == 0) 
      for (z = x-1; z >= 0; z--) 
	for (w = (z >= m)? m-1 : n1; w >= 0; w--) 
	  if (y != w && w != z && is_same_hole(w, z) == 0)
	    for (u = (x < m && y < m && z < m && w < m)? n1 : m-1;
		 u >= 0; u--) 
	      if (u != x && u != y && u != z && u != w &&
		  is_same_hole(u, x) == 0 &&
		  is_same_hole(u, y) == 0 &&
		  is_same_hole(u, z) == 0 &&
		  is_same_hole(u, w) == 0)
	    for (v = (x < m && y < m && z < m && w < m)? n1 : m-1;
		 v >= 0; v--) 
	      if (v != x && v != y && v != z && v != w && 
		  is_same_hole(v, x) == 0 &&
		  is_same_hole(v, y) == 0 &&
		  is_same_hole(v, z) == 0 &&
		  is_same_hole(v, w) == 0) {
	      if ((x == 1 || y == 1 || z <= 1 || w == 1 || u == 1 || v == 1) &&
		  insert_cl_4(TRIPLE2KEY(x, y, u),
			      TRIPLE2KEY(z, w, u),
			      TRIPLE2KEY(y, v, x),
			      TRIPLE2KEY(w, v, z),
			      0, cl_arr, sign_arr))
		return 1;
	    }

  } else { /* CYCLIC == 'C' */ 
    
  for (k = 0; k < addk_num; k++)
    for (u = m-1; u >= 0; u--) 
      for (v = m-1; v >= 0; v--) if (u != v) {
	int uv = DIFF(u,v);
	int uaddk_num = u%addk_num;

	for (x = n1; x >= m; x--) {
	  if (insert_cl_all_3(TRIPLE2KEY(k, x, u), 
			      TRIPLE2KEY(x, v, k),
			      THETA(uaddk_num, x, uv),
			      1, cl_arr, sign_arr))
	    return 1;

	  if (insert_cl_all_3(TRIPLE2KEY(x, k, u), 
			      TRIPLE2KEY(k, v, x),
			      THETA(uaddk_num, x+INCOMPLETE, uv),
			      1, cl_arr, sign_arr))
	    return 1;
	}

	for (w = m-1; w >= 0; w--) 
	  if (insert_cl_all_3(TRIPLE2KEY(k, w, u), 
			      TRIPLE2KEY(w, v, k),
			      THETA(uaddk_num, w, uv),
			      1, cl_arr, sign_arr))
	    return 1;
      }
    
  if (unique_cover_clauses(0, cl_arr, sign_arr)) return 1;

 /* this set of clauses is heavy */
 if (addk_num > 1)
 for (k = 0; k < addk_num; k++) 
   for (u = 0; u < m; u++) 
     for (y = k+1; y < m; y++)
       for (x = m; x < n; x++)
	 for (v = 0; v < m; v++)
	   for (w = 0; w < n; w++) {
	     if (insert_cl_4(TRIPLE2KEY(k, u, x), 
			     TRIPLE2KEY(y, v, x), 
			     TRIPLE2KEY(u, w, k),
			     TRIPLE2KEY(v, w, y),
			     0, cl_arr, sign_arr))
	       return 1;
	   }
  }

  return 0;
}

int cqg3 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* (x * y) * (y * x) = x, and its two variants */
{
  int x, y, u, v;

  /* x * y = u, y * x = v => u * v = x */
  for (x = n1; x >= 0; x--) 
    for (y = (x >= m)? m-1 : n1; y >= 0; y--) 
      for (u = (x < m && y < m)? n1 : m-1; u >= 0; u--)
	for (v = (x < m && y < m && u < m)? n1 : m-1; v >= 0; v--) 
	  if (insert_cl_all_3(TRIPLE2KEY(x, y, u),
			      TRIPLE2KEY(y, x, v), 
			      TRIPLE2KEY(u, v, x), 
			      3, cl_arr, sign_arr))
	    return 1;

  return 0;
}

cqg4 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* (x * y) * (y * x) = y, and its two variants */
{
  int x, y, u, v;

  /* x * y = u, y * x = v => u * v = y */
  for (x = n1; x >= 0; x--) 
    for (y = (x >= m)? m-1 : n1; y >= 0; y--) 
      for (u = (x < m && y < m)? n1 : m-1; u >= 0; u--) 
	for (v = (x < m && y < m && u < m)? n1 : m-1; v >= 0; v--) 
	  if (insert_cl_all_3(TRIPLE2KEY(x, y, u),
			      TRIPLE2KEY(y, x, v),
			      TRIPLE2KEY(u, v, y), 
			      3, cl_arr, sign_arr))
	    return 1;

  return 0;
}

cqg5 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* ((x * y) * x) * x = y, plus its two variants */
{
  int x, y, u, v;
  
  /* x * y = u, u * x = v => v * x = y */
  for (x = n1; x >= 0; x--) 
    for (y = (x >= m)? m-1 : n1; y >= 0; y--) 
      for (u = (x < m && y < m)? n1 : m-1; u >= 0; u--) 
	for (v = (x < m && y < m && u < m)? n1 : m-1; v >= 0; v--) {

	  /* u * x = y, y * u = v imply v * u = x */
	  if (insert_cl_all_3(TRIPLE2KEY(u, x, y), 
			      TRIPLE2KEY(y, u, v),
			      TRIPLE2KEY(v, u, x), 
			      3, cl_arr, sign_arr))
	    return 1;
	}

  return 0;
}

cqg6 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* (x * y) * y = x * (x * y) and its two variants */
{
  int x, y, u, v;

  /* x * y = u, x * u = v => u * y = v */
  for (x = n1; x >= 0; x--) 
    for (y = (x >= m)? m-1 : n1; y >= 0; y--) 
      for (u = (x < m && y < m)? n1 : m-1; u >= 0; u--) 
	for (v = (x < m && y < m && u < m)? n1 : m-1; v >= 0; v--) 
	  if (insert_cl_all_3(TRIPLE2KEY(x, y, u),
			      TRIPLE2KEY(u, y, v), 
			      TRIPLE2KEY(x, u, v), 
			      3, cl_arr, sign_arr))
	    return 1;
  return 0;
}

cqg7 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* (x * y) * x = y * (x * y) and its two variants */
{
  int x, y, u, v;

  /* x * y = u, u * x = v => y * u = v */
  for (x = n1; x >= 0; x--) 
    for (y = (x >= m)? m-1 : n1; y >= 0; y--) 
      for (u = (x < m && y < m)? n1 : m-1; u >= 0; u--) 
	for (v = (x < m && y < m && u < m)? n1 : m-1; v >= 0; v--) 
	  /* x * y = u, u * x = v imply y * u = v */
	  if (insert_cl_all_3(TRIPLE2KEY(x, y, u), 
			      TRIPLE2KEY(u, x, v),
			      TRIPLE2KEY(y, u, v), 
			      3, cl_arr, sign_arr))
	    return 1;
  return 0;
}

cqg8 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* x * (x * y) = (y * x) and its two variants */
{
  int x, y, u, v;

  for (x = n1; x >= 0; x--) 
    for (y = (x >= m)? m-1 : n1; y >= 0; y--) 
      for (u = (x < m && y < m)? n1 : m-1; u >= 0; u--) 
	for (v = (x < m && y < m && u < m)? n1 : m-1; v >= 0; v--) 
	  /* x * y = u, y * x = v => x * u = v */
	  if (insert_cl_all_3(TRIPLE2KEY(x, y, u),
			      TRIPLE2KEY(y, x, v),
			      TRIPLE2KEY(x, u, v),
			      3, cl_arr, sign_arr))
	    return 1;
  return 0;
}

int cqg9 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* ((x * y) * y) * y ==  x */
{
  int x, y, u, v;
  
  /* x * y = u, u * y = v => v * y = x */
  for (x = n1; x >= 0; x--) 
    for (y = (x >= m)? m-1 : n1; y >= 0; y--) 
      for (u = (x < m && y < m)? n1 : m-1; u >= 0; u--) 
	for (v = (x < m && y < m && u < m)? n1 : m-1; v >= 0; v--) 
	  if (insert_cl_all_3(TRIPLE2KEY(x, y, u), 
			      TRIPLE2KEY(u, y, v),
			      TRIPLE2KEY(v, y, x), 
			      1, cl_arr, sign_arr))
	    return 1;
  return 0;
}

cqg91 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* (x * y) * x = y */
{
  int x, y, z;

  for (x = n1; x >= 0; x--) 
    for (y = (x >= m)? m-1 : n1; y >= 0; y--) 
      for (z = ((x < m && y < m)? n1 : m-1); z >= 0; z--) {
	/* (x * y) = z => z * x = y */
	if (insert_cl_2(TRIPLE2KEY(x, y, z), 
			TRIPLE2KEY(z, x, y), 
			TT, cl_arr, sign_arr))
	  return 1;
      }
  return 0;
}

cqg101 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* 10.1: (x * y) * y = x */
{
  int x, y, z;

  /* (x * y) = z => z * y = x */
  for (x = n1; x >= 0; x--) 
    for (y = n1; y >= 0; y--) 
      for (z = ((x < m && y < m)? n1 :
		((x < m || y < m)? m-1 : -1)); 
	   z >= 0; z--) {

	/* x * y = z -> z * y = x */
	cl_arr[0] = TRIPLE2KEY(x, y, z);
	sign_arr[cl_arr[0]] = 0;
	if (insert_one_key(TRIPLE2KEY(z, y, x), 1,
			   cl_arr, sign_arr, 1) == 0)
	    Subsume_num++;
	else if (qg_insert_clause( cl_arr, sign_arr, 2) == 1)
	  return 1;
      }
  return 0;
}

cqg102 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* 10.2: x * (y * x) = y * (x * y) */
{
  int x, y, u, v, z;
  
  for (x = n1; x >= 0; x--) 
    for (y = (x >= m)? m-1 : n1; y >= 0; y--) 
      for (u = (x < m && y < m)? n1 : m-1; u >= 0; u--) 
	for (v = (x < m && y < m && u < m)? n1 : m-1; v >= 0; v--) 
	  for (z = (x < m && y < m && u < m && v < m)? n1 : m-1; z >= 0; z--) {

	    /* x * y = v, y * x = u, x * u = z imply y * v = z */
	    if (insert_cl_4(TRIPLE2KEY(x, y, v), 
				TRIPLE2KEY(y, x, u),
				TRIPLE2KEY(x, u, z), 
				TRIPLE2KEY(y, v, z), 
				4, cl_arr, sign_arr))
	      return 1;
	  }
  return 0;
}

cqg12 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* f(f(f(f(y, x),x),y),y) == x */
{
  int x, y, z, u, v;

  for (x = n1; x >= 0; x--) 
    for (y = (x >= m)? m-1 : n1; y >= 0; y--) 
      for (z = (x >= m || y >= m)? m-1 : n1; z >= 0; z--) 
	for (u = (z >= m || y >= m || x >= m)? m-1 : n1; u >= 0; u--) 
	  for (v = (z >= m || u >= m || y >= m || x >= m)? m-1 : n1;
	       v >= 0; v--) 
	    /* y * x = z, z * x = u, u * y = v, v * y = x */
	    if (insert_cl_4(TRIPLE2KEY(y, x, z),
			    TRIPLE2KEY(z, x, u),
			    TRIPLE2KEY(u, y, v),
			    TRIPLE2KEY(v, y, x),
			    1, cl_arr, sign_arr))
	      return 1;
  return 0;
}


int cqg13 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* y * (x * y) = x */
{
  int x, y, z;
 
  for (x = n1; x >= 0; x--) 
    for (y = n1; y >= 0; y--) 
      for (z = ((x < m && y < m)? n1 :
		((x < m || y < m)? m-1 : -1)); 
	   z >= 0; z--) {

	if (insert_cl_2(TRIPLE2KEY(x, y, z),
			TRIPLE2KEY(y, z, x), 
			1, cl_arr, sign_arr))
	  return 1;

	if (insert_cl_2(TRIPLE2KEY(x, y, z),
			TRIPLE2KEY(z, x, y), 
			1, cl_arr, sign_arr))
	  return 1;
      }
  return 0;
}

cqg24 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* Find two squares: one is a (213)-COILS and the other is symmetric */
{
  int x, y, z, u, k;

  set_double_cl(0);

  for (x = m; x < n; x++) 
    for (u = 2; u < m; u++) if (2*u != m && u % 2 == 0) {
      if (insert_cl_1(SQUARE2+TRIPLE2KEY(0, u, x), 
		      0, cl_arr, sign_arr))
	return 1;
    }

  for (u = n1; u >= 0; u--) {

    if (!IDEMPOTENT && PIGEON == 0 && QGROUP % 2 == 0) {
      if (u == 0) printf("Assume x . x = %d\n\n", n1);
      if (insert_cl_1(SQUARE2+TRIPLE2KEY(u, u, n1), TT)) return 1;
    }

    for (x = n1; x > 0; x--)
      for (y = (x >= m)? m-1 : x-1; y >= 0; y--) {

	if (QGROUP % 2 == 0 && (PIGEON == 1) && (x < m)) {
	  if (insert_cl_2(SQUARE2+TRIPLE2KEY(x, x, u),
			  SQUARE2+TRIPLE2KEY(y, y, u),
			  1, cl_arr, sign_arr)) 
	    return 1;

	  if (insert_cl_2(SQUARE2+TRIPLE2KEY(y, y, u),
			  SQUARE2+TRIPLE2KEY(x, x, u),
			  1, cl_arr, sign_arr)) 
	    return 1;
	}

	if (u < m) {
	  if (insert_cl_2(SQUARE2+TRIPLE2KEY(x, y, u),
			  SQUARE2+TRIPLE2KEY(y, x, u),
			  1, cl_arr, sign_arr)) 
	    return 1;
	  if (insert_cl_2(SQUARE2+TRIPLE2KEY(y, x, u),
			  SQUARE2+TRIPLE2KEY(x, y, u),
			  1, cl_arr, sign_arr)) 
	    return 1;
	}
      }
  }

  for (k = 0; k < addk_num; k++) 
    for (u = k+1; u < m; u++) 
      for (x = m; x < n; x++) 
	if ((k+u)%2 == 0) {
	  if (m%2 || (u-k) != m/2)
	    if (insert_cl_1(SQUARE2+TRIPLE2KEY(k, u, x), 0)) return 1;
	} else {
	  for (y = 0; y < m; y++) 
	    for (z = 0; z < m; z++) if ((y+z)%2 == 0) {
	      if (insert_cl_all_3(TRIPLE2KEY(k, u, y), 
				  TRIPLE2KEY(u, k, z),
				  SQUARE2+TRIPLE2KEY(k, u, x), 
				  0, cl_arr, sign_arr))
		return 1;
	    }
	}

  if (cqg0( cl_arr, sign_arr )) return 1;
  set_double_cl(1);
  return 0;
}

cqg14 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* 4-ipmd: x * y = u, y * u = v => u * v = x */
{
  int x, y, u, v;

  for (x = n1; x >= 0; x--) 
    for (y = (x >= m)? m-1 : n1; y >= 0; y--) 
      for (v = (x >= m || y >= m)? m-1 : n1; v >= 0; v--) {

	if (x >= m) 
	  /* x * v = y => v * y != u for x >= m and u >= m */
	  for (u = n1; u >= m; u--) {
	    cl_arr[0] = TRIPLE2KEY(x, v, y);
	    sign_arr[cl_arr[0]] = 0;
	    cl_arr[1] = TRIPLE2KEY(v, y, u);
	    sign_arr[cl_arr[1]] = 0;
	    if (qg_insert_clause( cl_arr, sign_arr, 2) == 1)
	      return 1;
	  }

	for (u = (v >= m || y >= m || x >= m)? m-1 : n1; u >= 0; u--) 
	  if (insert_cl_all_3(TRIPLE2KEY(x, y, u),
			      TRIPLE2KEY(y, u, v),
			      TRIPLE2KEY(u, v, x),
			      1, cl_arr, sign_arr))
	    return 1;
      }
  return 0;
}

cqg16 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* Read a (213)-COLS and find its symmetric mate */
{
  int x, u, v, k;

  for (x = m; x < n; x++) 
    for (u = 2; u < m; u++) if (2*u != m && u % 2 == 0) {
      if (insert_cl_1(TRIPLE2KEY(0, u, x), 0)) return 1;
    }

  for (k = 0; k < addk_num; k++)
    for (u = n1; u >= 0; u--) {
      for (x = (u >= m)? m-1 : n1; x > 0; x--) if (is_same_hole(k, x) == 0) {
	if (u >= m) {
	  if (((k+x) & 1) == 0 ||
	      ((Lsquare[k][x] + Lsquare[x][k]) & 1) == 0) {
	    if (insert_cl_1(TRIPLE2KEY(k, x, u), FF)) return 1;
	  }
	} else {
	  if (insert_cl_2(TRIPLE2KEY(k, x, u),
			  TRIPLE2KEY(x, k, u),
			  1, cl_arr, sign_arr)) 
	    return 1;
	} 
      }
  }

  /* The symmetric square is orthogonal to the SOLS */
  for (k = 0; k < addk_num; k++)
    for (u = m-1; u >= 0; u--) {
      int uk = u%addk_num;
      for (v = m-1; v >= 0; v--) {
	int uv = DIFF(u,v);
	for (x = n1; x >= m; x--) {
	  if ((Lsquare[k][x] == u) &&
	      insert_cl_2(BETA(k, x, v), 
			  THETA(uk, x, uv),
			  1, cl_arr, sign_arr))
	    return 1;

	  if ((Lsquare[k][x] == u) &&
	      insert_cl_2(BETA(k, x, v), 
			  DELTA(uk, k, uv),
			  1, cl_arr, sign_arr))
	    return 1;

	  if ((Lsquare[x][k] == u) &&
	      insert_cl_2(GAMMA(k, x, v), 
			  THETA(uk, x+INCOMPLETE, uv),
			  1, cl_arr, sign_arr))
	    return 1;

	  /*
	  if ((Lsquare[x][k] == u) &&
	      insert_cl_2(GAMMA(k, x, v), 
			  DELTA(uk, k, uv),
			  1, cl_arr, sign_arr))
	    return 1;
	  */
	}
	    
	for (x = m-1; x >= 0; x--) {
	  if ((Lsquare[k][x] == u) &&
	      insert_cl_2(TRIPLE2KEY(k, x, v), 
			  THETA(uk, x, uv),
			  1, cl_arr, sign_arr))
	    return 1;

	  if ((Lsquare[k][x] == u) &&
	      insert_cl_2(TRIPLE2KEY(k, x, v), 
			  DELTA(uk, k, uv),
			  1, cl_arr, sign_arr))
	    return 1;
	}
      }
    }

  if (unique_cover_clauses(0, cl_arr, sign_arr)) return 1;

  return 0;
}

cqg50 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* 5-ipmd: x * y = z, y * z = u, z * u = v => u * v = x */
{
  int x, y, z, u, v;

  for (x = n1; x >= 0; x--) 
    for (y = (x >= m)? m-1 : n1; y >= 0; y--) 
      for (z = (x >= m || y >= m)? m-1 : n1; z >= 0; z--) {

	if (x >= m) {
	  /* x * z = y => z * y != u for x >= m and u >= m */
	  for (u = n1; u >= m; u--) {
	    cl_arr[0] = TRIPLE2KEY(x, z, y);
	    sign_arr[cl_arr[0]] = 0;
	    cl_arr[1] = TRIPLE2KEY(z, y, u);
	    sign_arr[cl_arr[1]] = 0;
	    if (qg_insert_clause( cl_arr, sign_arr, 2) == 1)
	      return 1;
	  }

	  /* x * z = y, z * y = u => y * u != x for x >= m */
	  for (u = m-1; u >= 0; u--) {
	    if (insert_cl_all_3(TRIPLE2KEY(x, z, y),
				TRIPLE2KEY(z, y, u),
				TRIPLE2KEY(y, u, x),
				0, cl_arr, sign_arr))
	      return 1;
	  }

	  /* v * x = y, x * y = z, y * z != u for x >=m and u >= m */
	  for (v = m-1; v > y; v--)
	    for (u = n1; u >= m; u--) {
	      if (insert_cl_all_3(TRIPLE2KEY(x, y, z),
				  TRIPLE2KEY(v, x, y),
				  TRIPLE2KEY(y, z, u),
				  0, cl_arr, sign_arr))
		return 1;
	    }
	}

	for (u = (z >= m || y >= m || x >= m)? m-1 : n1; u >= 0; u--) 
	  for (v = (z >= m || u >= m || y >= m || x >= m)? m-1 : n1;
	       v >= 0; v--) 
	    if (insert_cl_4(TRIPLE2KEY(x, y, z),
			    TRIPLE2KEY(y, z, u),
			    TRIPLE2KEY(z, u, v),
			    TRIPLE2KEY(u, v, x),
			    1, cl_arr, sign_arr))
	      return 1;
      }

  return 0;
}

int cqg63 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* if (x * y = z) then  (x * z) != y -- pure MTS */
{
  int x, y, z;

  if (m % 6 == 3) {
    x = m/3;
    if (PIGEON == 9) {
      if (insert_cl_1(TRIPLE2KEY(0, x, x+x), TT)) return 1;
    } else if (PIGEON == 10) {
      if (insert_cl_1(TRIPLE2KEY(0, x+x, x), TT)) return 1;
    }
  }
 
  for (x = n1; x >= 0; x--) 
    for (y = n1; y >= 0; y--) if (x != y)
      for (z = n1; z >= 0; z--) {

	if (insert_cl_2(TRIPLE2KEY(x, y, z),
			TRIPLE2KEY(x, z, y), 
			0, cl_arr, sign_arr))
	  return 1;
      }

  return 0;
}

csymm_trasversal(cl_arr, sign_arr)
     int cl_arr[], sign_arr[];
{
  int u, x, y, first, second;

  /* first position */
  first = 0;

  /* second position */
  second = first+1;

  for (u = 0; u < n; u++) {
    for (x = 1; x <= first; x++) 
      for (y = 0; y < x; y++) {
	if (insert_cl_2(TRIPLE2KEY(x, first-x, u), 
			TRIPLE2KEY(y, first-y, u), 
			0, cl_arr, sign_arr))
	  return 1;  
      }

    for (x = second+1; x <= n1; x++)
	for (y = second; y < x; y++) {
	  if (insert_cl_2(TRIPLE2KEY(x, n1-x+second, u), 
			  TRIPLE2KEY(y, n1-y+second, u), 
			  0, cl_arr, sign_arr))
	    return 1;
	}

    for (x = 0; x <= first; x++) 
      for (y = second; y <= n1; y++) {
	if (insert_cl_2(
			TRIPLE2KEY(y, n1-y+second, u), 
			TRIPLE2KEY(x, first-x, u), 
			0, cl_arr, sign_arr))
	  return 1;  
      }
  }
  return 0;
}

cdiagonal_cls2 ()
{
  int u;

  if (m % 2) {
    printf("Warning: v-n = %d is not even.\n", m);
    fprintf(stderr, "Warning: v-n = %d is not even.\n", m);
  }

  for (u = m; u < n; u++) {
    if (insert_cl_1(TRIPLE2KEY(0, m/2, u), FF)) {
      printf("<0, %d, %d> cannot be false\n", m/2, u);
      return 1;
    }
    if (insert_cl_1(TRIPLE2KEY(u, 0, 0), FF)) {
      printf("<%d, 0, 0> cannot be false\n", u);
      return 1;
    }
    if (insert_cl_1(TRIPLE2KEY(u, 0, m/2), FF)) {
      printf("<%d, 0, %d> cannot be false\n", u, m/2);
      return 1;
    }
  }
  return 0;
}

cdiagonal_cls (cl_arr, sign_arr)
     int cl_arr[], sign_arr[];
{
  int x, y, u;

  for (u = m; u < n; u++)
    for (x = 0; x < m; x++)
      if (insert_cl_1(TRIPLE2KEY(x, m-1-x, u), 0)) return 1;

  for (u = 0; u < n; u++) 
    for (x = m-1; x > 0; x--)
      for (y = x-1; y >= 0; y--) {
	if (insert_cl_2(TRIPLE2KEY(x, m-1-x, u), 
			TRIPLE2KEY(y, m-1-y, u), 
			0, cl_arr, sign_arr))
	  return 1;
      }

  if (!IDEMPOTENT) {

    for (u = m; u < n; u++)
      for (x = 0; x < m; x++)
      if (insert_cl_1(TRIPLE2KEY(x, x, u), 0)) return 1; 

    for (u = 0; u < m; u++) 
      for (x = m-1; x > 0; x--)
	for (y = x-1; y >= 0; y--) {
	  if (insert_cl_2(TRIPLE2KEY(x, x, u), 
			  TRIPLE2KEY(y, y, u), 
			  0, cl_arr, sign_arr))
	    return 1;
	}
  }

  return 0;
}

cdiagonal_cls321(cl_arr, sign_arr)
     int cl_arr[], sign_arr[];
{
  int x, y, u;

  if (cdiagonal_cls(cl_arr, sign_arr)) return 1;

  for (u = 0; u < n; u++) 
    for (x = n1; x > 0; x--)
      for (y = x-1; y >= 0; y--) {
	if (insert_cl_2(TRIPLE2KEY(u, x, n1-x), 
			TRIPLE2KEY(u, y, n1-y), 
			0, cl_arr, sign_arr))
	  return 1;
      }

  if (!IDEMPOTENT) 
    for (u = 0; u < n; u++) 
      for (x = n1; x > 0; x--)
	for (y = x-1; y >= 0; y--) {
	  if (insert_cl_2(TRIPLE2KEY(u, x, x), 
			  TRIPLE2KEY(u, y, y), 
			  0, cl_arr, sign_arr))
	    return 1;
	}

  return 0;
}

cqg_unit_clauses()
{
  int j, x, num, step[3], k;

  step[0] = 0; step[1] = SQUARE2; step[2] = SQUARE2+SQUARE2;
  num = 1 + multi_squares();

  if (LINE < 5000 && LINE >= 3000) cqg_read_square();
  if (LINE < 4000 && LINE >= 2000) qg_read_square_mod2();

  if (QUEEN == 16) oa_read_square();

  if (IDEMPOTENT) {
    if (OUTPUT < 2) {
      if (NHOLE > 1) 
	printf("Looking for HQG%d(%d^%d, %d^1).\n\n",
	       QUEEN, RAMSEY, NHOLE, INCOMPLETE);
      else if (INCOMPLETE)
	printf("Looking for idempotent IQG%d(%d, %d).\n\n",
	       QUEEN, m, INCOMPLETE);
      else
	printf("Looking for idempotent QG%d(%d).\n\n", QUEEN, m);
    }

    for (k = 0; k < addk_num; k++) 
      for (j = 0; j < num; j++) {

	/* 0 * 0 = 0 */
	if (NHOLE == 0) 
	  if (insert_cl_1(step[j]+TRIPLE2KEY(k,k,k), TT)) return 1;

	/* 0 * x != x */
	for (x = k+1; x < m; x++) if (is_same_hole(x, k) == 0) {
	  if (insert_cl_1(step[j]+ALPHA(k, x, x), FF)) return 1;
	}

	/* 0 * x != 0 and x * 0 != 0 */
	for (x = k+1; x < n; x++) {
	  if (insert_cl_1(step[j]+TRIPLE2KEY(k, x, k), FF)) return 1;
	  if (insert_cl_1(step[j]+TRIPLE2KEY(x, k, k), FF)) return 1;
	}
      }
  }

  return 0;
}

void cqg_locate_holes ()
{
  int i, v, u;

  if ((QGROUP-INCOMPLETE) % RAMSEY == 0) {
    NHOLE = (QGROUP-INCOMPLETE) / RAMSEY;

    for (u = m; u < QGROUP; u++)
      for (v = m; v < QGROUP; v++) 
	set_same_hole(u, v);

    for (i = 0; i < NHOLE; i++) 
      for (u = i; u < m; u += NHOLE)
	for (v = i; v < m; v += NHOLE) {
	  set_same_hole(u, v);
	}
  } else {
    printf("why do you set -q and -r at the same time?\n");
    exit(0);
  }
}

int unique_cover_clauses (step, cl_arr, sign_arr)
     int step, cl_arr [], sign_arr [];
{
  int i, x, y, v, k;

  for (k = 0; k < addk_num; k++) {
    if (IDEMPOTENT) 
      /* no one can cover 0, c(x, 0) = false */
      for (y = n1+INCOMPLETE; y > k; y--) {
	if (insert_cl_1(step+THETA(k, y, 0),  FF)) return 1;
	
	if (NHOLE) 
	  for (x = NHOLE; x < m; x += NHOLE) {
	    if (insert_cl_1(step+THETA(k, y, x), FF)) return 1;
	  }
      }
 
    /* c(k, x, y) and c(i, x, y) => k = i */
    /*
    for (i = 0; i < k; i++) 
      for (x = 0; x < m; x++)
	for (v = 0; v < m; v++) {
	  if (insert_cl_2(step+THETA(k, x, v),
			  step+THETA(i, x, v),
			  FF, cl_arr, sign_arr)) return 1;
	}

    for (i = 0; i < k; i++) 
      for (x = 0; x < addk_num; x++)
	for (v = 0; v < m; v++) {
	  if (insert_cl_2(step+DELTA(k, x, v),
			  step+DELTA(i, x, v),
			  FF, cl_arr, sign_arr)) return 1;
	}
    */

    for (x = m-1; x >= 0; x--) if (NHOLE == 0 || (x % NHOLE != 0)) {
      for (y = n1+INCOMPLETE; y > 0; y--) 
	for (v = y-1; v >= 0; v--) {
	  /* c(y, x) and c(v, x) => y = v */
	  if (insert_cl_2(step+THETA(k, y, x),
			  step+THETA(k, v, x),
			  FF, cl_arr, sign_arr)) return 1;
	}
    }

    for (x = m-1; x >= 0; x--) if (NHOLE == 0 || (x % NHOLE != 0)) {
      for (y = addk_num-1; y > 0; y--) 
	for (v = y-1; v >= 0; v--) {
	  /* c(y, x) and c(v, x) => y = v */
	  if (insert_cl_2(step+DELTA(k, y, x),
			  step+DELTA(k, v, x),
			  FF, cl_arr, sign_arr)) return 1;
	  /*
	  if (x == 5 && k) {
	    printf("WWW %d: (%d %d %d) vs (%d %d %d)\n",
		   step, k, y, x, k, v, x);
	  }
	  */
	}
    }
  }
  return 0;
}

/*
int test_omts ()
{
  int t;
  char s1[10];
  omts++;

  for (t = 1; t <= Max_atom; t++) if (Value[t]) 
    fprintf(omt_f, "%d ", (t-1) % QGROUP);
  fprintf(omt_f, "\n");

  if (omts == 1000) {
    omts = 0;
    fclose(omt_f);
    sprintf(s1,"omt_f%d", ++omt_fn);
    omt_f = fopen(s1, "w");
  }

  return 0;
}
*/

extra_cyclic_cls(cl_arr, sign_arr)
     int cl_arr[], sign_arr[];
{
  int x, y, u, v;

  if (PIGEON >= 200 && (PIGEON % 100 == 0)) {
    int i, j, k;
    x = 0;
    u = PIGEON/100;
    v = m/u-2;
    i = 0;

    for (j = 1; j < m; j++) if (is_same_hole(0, j) == 0) {
      printf("0 * %d = ", j);
      for (k = 1; k < m; k++) if (is_same_hole(k, j) == 0 && k % u != x) {
	if (insert_cl_1(ALPHA(0, j, k), FF)) return 1;
      }

      if (++i == v) { 
	i = 0; 
	printf("%d mod %d\n", x, u);
	if (++x == u) j = m;
      }
    }
    if (i) printf("%d mod %d\n", x, u);
    printf("\n");
  }

  if (RESTRICT >= 10) {

    if (OUTPUT < 2) printf("n = %d, m = %d, RESTRICT = %d\n", n, m, RESTRICT);

    if (RESTRICT >= 80) {

      if (RESTRICT == 88 && (addk_num > 1)) {
	/* complete highest consecutive numbers in GAMMA. */
	for (x = m; x < n; x++) {
	  insert_cl_1(GAMMA(1, x, x-INCOMPLETE), TT);
	  if (x % 2 == m % 2) 
	    insert_cl_1(GAMMA(0, x, x-INCOMPLETE+1), TT);
	  else
	    insert_cl_1(GAMMA(0, x, x-INCOMPLETE-1), TT);
	}

      } else {
	/* complete low consecutive numbers in BETA. */
	for (x = m; x < n; x++) {
	  insert_cl_1(BETA(0, x, x-m+1+RESTRICT-80), TT);
	  printf("0 * %d = %d\n", x, x-m+1+RESTRICT-80);
	}

	/* complete highest consecutive numbers in GAMMA. */
	for (x = m; x < n; x++) {
	  insert_cl_1(GAMMA(0, x, x-INCOMPLETE), TT);
	  printf("%d * 0 = %d\n", x, x-INCOMPLETE);
	}
      }

    } else if (RESTRICT >= 70) {

      /* complete high consecutive numbers in BETA. */
      for (x = m; x < n; x++) {
	insert_cl_1(BETA(0, x, x-INCOMPLETE+70-RESTRICT), TT);
	printf("0 * %d = %d\n", x, x-INCOMPLETE+70-RESTRICT);
      }
      /* partial highest consecutive numbers in GAMMA. */
      for (x = m+RESTRICT-70; x < n; x++) {
	insert_cl_1(GAMMA(0, x, x-INCOMPLETE), TT);
	printf("%d * 0 = %d\n", x, x-INCOMPLETE);
      }
    } else if (RESTRICT >= 60) {

      /* complete high consecutive numbers in GAMMA. */
      for (x = m; x < n; x++) 
	insert_cl_1(GAMMA(0, x, x-INCOMPLETE+60-RESTRICT), TT);

    } else if (RESTRICT >= 50) {

      /* partial highest consecutive numbers in GAMMA. */
      for (x = m+RESTRICT-50; x < n; x++) 
	insert_cl_1(GAMMA(0, x, x-INCOMPLETE), TT);

    } else if (RESTRICT >= 40) {

      /* complete high consecutive numbers in BETA. */
      for (x = m; x < n; x++) 
	insert_cl_1(BETA(0, x, x-INCOMPLETE+40-RESTRICT), TT);

    } else if (RESTRICT >= 30) {

      /* partial highest consecutive numbers in BETA. */
      for (x = m+RESTRICT-30; x < n; x++) 
	insert_cl_1(BETA(0, x, x-INCOMPLETE), TT);

    } else if (RESTRICT >= 20) {

      /* some consecutive numbers in BETA. */
      for (y = m+1; (y < n) && (y <= m+RESTRICT-10); y++) 
	for (x = 2; x < m; x++) {
	  sign_arr[cl_arr[0] = BETA(0, y, x)] = 0;
	  sign_arr[cl_arr[1] = BETA(0, y-1, x-1)] = 1;
	  if (qg_insert_clause( cl_arr, sign_arr, 2) == 1)
	    return 1;
	  
	  sign_arr[cl_arr[0] = BETA(0, y, x)] = 1;
	  sign_arr[cl_arr[1] = BETA(0, y-1, x-1)] = 0;
	  if (qg_insert_clause( cl_arr, sign_arr, 2) == 1)
	    return 1;
	}
    } else {
      /* some restriction on BETA and GAMMA */
      for (x = m; x < n; x++) 
	for (y = 3*(x-m)+21-RESTRICT; y < m; y++) if (is_same_hole(0, y) == 0) {
	  if (insert_cl_1(BETA(0, x, y), FF)) return 1;
	  if (insert_cl_1(GAMMA(0, x, y), FF)) return 1;
	}
    }
  }   

  return 0;
}

cqg_read_square ()
{
  int i, j, k;
  char name[20];

  sprintf(name, "l%d.in", LINE%1000);
  if (Input_sqs == NULL) { open_input_sqs(name); }
  if (fscanf(Input_sqs, "%d", &i) == EOF) {
    printf("No more blocks.\n"); 
    fclose(Input_sqs);
    Input_sqs = NULL;
    return 1;
  }

  printf("Read in a square:\n");
  for (i = 0; i < n; i++) {
    printf("\n  ");
    for (j = 0; j < n; j++) {
      if (fscanf(Input_sqs, "%d", &k) == EOF) { printf("\n"); return 0; }
      if (is_same_hole(i, j)) {
	if (k >= 0) { 
	  printf("Bad input: %d (-1 expected)\n", k); exit(0); 
	} 
	printf("-1 ");
      } else if (k >= 0) {
	printf("%d ", k);
	if (insert_cl_1(TRIPLE2KEY(i, j, k), TT)) bug(9);
      } else
	printf("-%d ", QGROUP);
    }
  }
  printf("\n\n");

  return 0;
}

void cqg_extra_unit_cls()
{
  printf("Extra unit clauses\n");

  if (insert_cl_1(TRIPLE2KEY(0, 1, 9), TT)) bug(99);
  if (insert_cl_1(TRIPLE2KEY(0, 2, 4), TT)) bug(99);
  if (insert_cl_1(TRIPLE2KEY(0, 3, 1), TT)) bug(99);
  if (insert_cl_1(TRIPLE2KEY(0, 4, 3), TT)) bug(99);
  if (insert_cl_1(TRIPLE2KEY(0, 5, 13), TT)) bug(99);
  /* if (insert_cl_1(TRIPLE2KEY(0, 6, 7), TT)) bug(99);*/
  if (insert_cl_1(TRIPLE2KEY(0, 7, 12), TT)) bug(99);
  if (insert_cl_1(TRIPLE2KEY(0, 8, 11), TT)) bug(99);
  if (insert_cl_1(TRIPLE2KEY(0, 9, 10), TT)) bug(99);
  if (insert_cl_1(TRIPLE2KEY(0, 10, 2), TT)) bug(99);
  if (insert_cl_1(TRIPLE2KEY(0, 11, 8), TT)) bug(99);
  if (insert_cl_1(TRIPLE2KEY(0, 12, 7), TT)) bug(99);
  if (insert_cl_1(TRIPLE2KEY(0, 13, 5), TT)) bug(99);

  /*
  if (insert_cl_1(TRIPLE2KEY(1, 0, 10), TT)) bug(99);
  if (insert_cl_1(TRIPLE2KEY(1, 1, 1), TT)) bug(99);
  if (insert_cl_1(TRIPLE2KEY(1, 2, 5), TT)) bug(99);
  if (insert_cl_1(TRIPLE2KEY(1, 3, 2), TT)) bug(99);
  if (insert_cl_1(TRIPLE2KEY(1, 4, 6), TT)) bug(99);
  if (insert_cl_1(TRIPLE2KEY(1, 5, 0), TT)) bug(99);
  if (insert_cl_1(TRIPLE2KEY(1, 6, 3), TT)) bug(99);
  if (insert_cl_1(TRIPLE2KEY(1, 7, 8), TT)) bug(99);
  if (insert_cl_1(TRIPLE2KEY(1, 8, 4), TT)) bug(99);
  if (insert_cl_1(TRIPLE2KEY(1, 9, 7), TT)) bug(99);
  if (insert_cl_1(TRIPLE2KEY(1, 10, 9), TT)) bug(99);

  if (insert_cl_1(TRIPLE2KEY(10, 0, 4), TT)) bug(99);
  if (insert_cl_1(TRIPLE2KEY(10, 1, 5), TT)) bug(99);

  if (insert_cl_1(SQUARE2+TRIPLE2KEY(0, 0, 4), TT)) bug(99);
  if (insert_cl_1(SQUARE2+TRIPLE2KEY(0, 1, 8), TT)) bug(99);
  if (insert_cl_1(SQUARE2+TRIPLE2KEY(0, 2, 0), TT)) bug(99);
  if (insert_cl_1(SQUARE2+TRIPLE2KEY(0, 3, 6), TT)) bug(99);
  if (insert_cl_1(SQUARE2+TRIPLE2KEY(0, 4, 5), TT)) bug(99);
  if (insert_cl_1(SQUARE2+TRIPLE2KEY(0, 5, 2), TT)) bug(99);
  if (insert_cl_1(SQUARE2+TRIPLE2KEY(0, 6, 12), TT)) bug(99);
  if (insert_cl_1(SQUARE2+TRIPLE2KEY(0, 7, 9), TT)) bug(99);
  if (insert_cl_1(SQUARE2+TRIPLE2KEY(0, 8, 1), TT)) bug(99);
  if (insert_cl_1(SQUARE2+TRIPLE2KEY(0, 9, 3), TT)) bug(99);
  if (insert_cl_1(SQUARE2+TRIPLE2KEY(0, 10, 10), TT)) bug(99);
  if (insert_cl_1(SQUARE2+TRIPLE2KEY(0, 11, 7), TT)) bug(99);
  if (insert_cl_1(SQUARE2+TRIPLE2KEY(0, 12, 11), TT)) bug(99);

  if (insert_cl_1(SQUARE2+TRIPLE2KEY(1, 0, 8), TT)) bug(99);
  if (insert_cl_1(SQUARE2+TRIPLE2KEY(1, 1, 5), TT)) bug(99);
  if (insert_cl_1(SQUARE2+TRIPLE2KEY(1, 2, 9), TT)) bug(99);
  if (insert_cl_1(SQUARE2+TRIPLE2KEY(1, 3, 1), TT)) bug(99);
  if (insert_cl_1(SQUARE2+TRIPLE2KEY(1, 4, 7), TT)) bug(99);
  if (insert_cl_1(SQUARE2+TRIPLE2KEY(1, 5, 6), TT)) bug(99);
  if (insert_cl_1(SQUARE2+TRIPLE2KEY(1, 6, 3), TT)) bug(99);
  if (insert_cl_1(SQUARE2+TRIPLE2KEY(1, 7, 12), TT)) bug(99);
  if (insert_cl_1(SQUARE2+TRIPLE2KEY(1, 8, 10), TT)) bug(99);
  if (insert_cl_1(SQUARE2+TRIPLE2KEY(1, 9, 2), TT)) bug(99);
  if (insert_cl_1(SQUARE2+TRIPLE2KEY(1, 10, 4), TT)) bug(99);
  if (insert_cl_1(SQUARE2+TRIPLE2KEY(1, 11, 11), TT)) bug(99);
  if (insert_cl_1(SQUARE2+TRIPLE2KEY(1, 12, 0), TT)) bug(99);

  if (insert_cl_1(SQUARE2+TRIPLE2KEY(12, 0, 11), TT)) bug(99);
  if (insert_cl_1(SQUARE2+TRIPLE2KEY(12, 1, 0), TT)) bug(99);
  */
}

qg100 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* x * y = u, z * w = v, (x+y) == (z+w) mod n -> u != v */
{
  int x, y, z, u, w;
  
  for (x = n1; x > 0; x--)
    for (y = (x >= m)? m-1 : n1; y >= 0; y--) 
      if (x != y && is_same_hole(x, y) == 0) 
      for (z = x-1; z >= 0; z--) 
	for (w = (z >= m)? m-1 : n1; w >= 0; w--) 
	  if (z != w && is_same_hole(w, z) == 0 &&
	      ABG_f[x][y] == ABG_f[z][w]) 
	  for (u = (x < m && y < m && z < m && w < m)? n1 : m-1; u >= 0; u--)
		if (insert_cl_2(TRIPLE2KEY(x, y, u),
				TRIPLE2KEY(z, w, u), 
				0, cl_arr, sign_arr))
		  return 1;
  
  return 0;
}
