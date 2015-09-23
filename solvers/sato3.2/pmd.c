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

/* We search for SFS when PMD == 2. */

GLOB SATOINT ABG_f[MAX_ABG_SIZE][MAX_ABG_SIZE];
GLOB SATOINT ABG_g[MAX_ABG_SIZE];
int Multi_blocks=0;
int rowoffset=1;

/* SIG(x,y,z) means the entry at row x and column y is z */
#define SIG2(i,j,k) ((((((i)-rowoffset) * c) + (j)) * m) + (k) + 3)
#define SIG(i,j,k) ((Oarray[i][j] == UNKNOW)? \
		      SIG2(i,j,k) : \
		      (Oarray[i][j] == k)? 1 : 2)
#define set_entry0(i,j,k) if (Oarray[i][j] == UNKNOW) Oarray[i][j] = k; \
                          else if (Oarray[i][j] != k) { bug(7); return 1;} 
#define set_entry(i,j,k) if (insert_cl_1(SIG(i, j, k), 1)) { bug(8); return 1;} \
                         Oarray[i][j] = k; 
#define set_entry1(i,j,k) if (Oarray[0][j] == UNKNOW) Oarray[i][j] = k; 
#define set_entry2(i,j,k) if (Oarray[0][j] == UNKNOW) \
 { if (insert_cl_1(SIG(i, j, k), 1)) { bug(8); return 1;} Oarray[i][j] = k; }

/* PHI(k,c1,z,a) means z is (k+1)-apart-covered at column c1 under a */
#define PHI(k,c1,z,a) ((((k) * c + (c1)) * (m) + (z))*Addk + a + rcm)
/* THI(k,r1,z, a) means z is (k+1)-apart-covered at row r1 under a */
#define THI(k,r1,z,a) ((((k) * r + (r1)) * (m) + (z))*Addk + a + rcm + kcm) 
/* TAO(k,r1c1,z,a) means z is (k+1)-apart-covered at row r1 and column c1 under a */
#define TAO(k,r1c1,z,a) ((((k) * r * c + (r1c1)) * (m) + (z))*Addk + a + rcm + kcm)
/* YOYO(k,x,a,b) means the pair (a,b) appears k-apart in column x */
#define YOYO(k,x,a,b) ((((k) * c + (x)) * (QGROUP) + (a))*(QGROUP) + b + rcm)

#define SPCD OARRAY
#define MULTI ZOOM
#define MAX_ROW 9
#define MAX_COL 50
#define DIFF(x,y) (ABG_f[ABG_g[y]][x])
#define HOLE -2
#define UNKNOW -1

#define Min_diff Addk

GLOB SATOINT Oarray[MAX_ROW][MAX_COL];
GLOB SATOINT Seed[MAX_ABG_SIZE];
GLOB SATOINT Mext[MAX_ABG_SIZE];
GLOB SATOINT W[MAX_ROW];
GLOB int m, r, c, Addk;

int DOUBLE = 0;
int Diffs[2][MAX_ABG_SIZE][MAX_ABG_SIZE];
int Num1 = 0;
int Add1 = 1;
int K_apart, rcm, kcm, newaddk;
int remainder[31], num_rem = 0;
int k_flag = 0;
void set_k_flag(k) int k; { k_flag = k; }
int get_k_flag() { return k_flag; }

void init_pmd()
{
  int i, j;

  m = QGROUP-INCOMPLETE;
  Addk = get_addk();
  if (Addk > 100) {
    Num1 = Addk/100;
    Addk = Addk%100;
    if (Num1 > 10) {
      Add1 = Num1/10;
      Num1 = Num1%10;
    }
    if (Addk%Add1) {
      printf("Bad parameters: Add1=%d, Num1=%d\n", Add1, Num1);
      exit(0);
    }
  }
  newaddk = (MOD > 0 && MOD < 7)? MOD * Addk : Addk;
  gen_abg_table();
  remainder[30] =0;

  if (k_flag >= 1000) { 
    if (FLAG == 0) { printf("please set # of blocks by -Q\n"); exit(0); }
    c = FLAG; 
    FLAG = 0;
    K_apart = PMD/2;
    r = PMD;
    num_rem = 0;
    rcm = (r-1) * c * m + 3;
    kcm = m * c * K_apart * Addk + 1;
    Max_atom = SIG2(r-1, c-1, QGROUP-1);
    for (i = 0; i < PMD; i++) W[i] = 1;
    fix_seed_zero();
    MULTI = 1;
    RAMSEY = 1;
    if (TRACE > 8) pmd_print_code(); 
    return; 
  } else if (FLAG >= 100) {
    K_apart = PMD/2;
    c = QGROUP*(QGROUP-1)/PMD;
    if (FLAG > 100) c = FLAG-100;
    FLAG = 0;
    r = PMD;
    m = QGROUP;
    rcm = r * c * m + 3;
    Max_atom = YOYO(K_apart-1, c-1, QGROUP-1, QGROUP-1);
    MULTI = 1;
    RAMSEY = 1;
    if (TRACE > 2) pmd_print_code(); 
    return; 
  }

  K_apart = PMD/2;
  r = PMD;
  if (RAMSEY) {
    if (m % RAMSEY != 0) {
      printf("Hole size %d does not divide %d - %d.\n", 
	     RAMSEY, QGROUP, INCOMPLETE);
      exit(0);
    }
    NHOLE = m/RAMSEY;
  } else RAMSEY = 1;

  if (SPCD==0 && (QGROUP + INCOMPLETE - RAMSEY) < (PMD * INCOMPLETE)) {
    printf("Too many infinitity elements:  %d+%d-%d < %d*%d.\n", 
	   QGROUP, INCOMPLETE, RAMSEY, PMD, INCOMPLETE);
    exit(0);
  }

  if ((QGROUP - INCOMPLETE) % Addk != 0) {
    printf("Additor %d does not divide %d - %d.\n", 
	   Addk, QGROUP, INCOMPLETE);
    exit(0);
  }

  if (MULTI == 0) fix_seed_zero();
  else {

    if (INCOMPLETE % MULTI != 0) {
      printf("Multiplier %d does not divide %d.\n", MULTI, INCOMPLETE);
    }

    if ((QGROUP - INCOMPLETE - RAMSEY) % MULTI != 0) {
      printf("Multiplier %d does not divide %d - %d.\n", 
	     MULTI, QGROUP-INCOMPLETE, RAMSEY);
      exit(0);
    }

    if (fopen("oa.spe", "r") != NULL) 
      i = read_special_seed();
    else 
      i = fix_seed();

    print_mext_reps();
  }

  for (i = 0; i < PMD; i++) W[i] = 1;

  if (k_flag >= 100 && k_flag < 120) {
    num_rem = k_flag-100;
    k_flag = 100;
    if (FLAG == 0) { printf("please set # of blocks by -Q\n"); exit(0); }
    c = FLAG; 
    FLAG = 0;
    if (num_rem > 0) {
      printf("Type in %d numbers to avoid: ", num_rem);
      i = 0; 
      while (i < num_rem) { scanf("%d", &j); remainder[i++] = j; }
      if (Addk > 1) {
	printf("How many multiples w.r.t Addk=%d: ", Addk);
	scanf("%d", &j);
	remainder[30] = j-1;
      }
    }
  } else if ((i = (((QGROUP + INCOMPLETE - RAMSEY)*newaddk) % PMD)) != 0 ||
	     k_flag >= 6) {
    if (k_flag >= 6) { k_flag -= 4; i += PMD; }
    else 
      printf("Block size %d does not divide %d = (%d + %d - %d)*%d.\n", 
	     PMD, (QGROUP + INCOMPLETE - RAMSEY)*newaddk, 
	     QGROUP, INCOMPLETE, RAMSEY, newaddk);

    if (k_flag == 0) exit(0);
    num_rem = i;

    if (k_flag == 1) {
      fix_remainder(PMD); 
      c = ((QGROUP + INCOMPLETE - RAMSEY)*newaddk - num_rem) / PMD;

    } else if (k_flag == 2) {
      printf("Type in %d numbers: ", num_rem);
      i = 0; 
      while (i < num_rem) { scanf("%d", &j); remainder[i++] = j; }
      c = ((QGROUP + INCOMPLETE - RAMSEY)*newaddk - num_rem) / PMD;
    } else if (k_flag == 3) {
      printf("Type in %d numbers: ", K_apart*num_rem);
      i = 0; 
      while (i < K_apart*num_rem) { scanf("%d", &j); remainder[i++] = j; }
      c = ((QGROUP + INCOMPLETE - RAMSEY)*newaddk - num_rem) / PMD;
    } else if (k_flag == 4) {
      if (num_rem % Addk == 0) num_rem = num_rem/Addk;
      else if ((num_rem+PMD)%Addk == 0) {
	num_rem = (num_rem+PMD)/Addk;
      }	
      printf("Type in %d numbers: ", num_rem);
      i = 0; 
      while (i < num_rem) { scanf("%d", &j); remainder[i++] = j; }
      c = ((QGROUP + INCOMPLETE - RAMSEY)*newaddk - num_rem*Addk) / PMD;
    } else if (k_flag > 4) exit(0);

  } else {
    num_rem = 0;
    if (k_flag == 1) {
      fix_remainder(PMD);
    } else if (k_flag < 10 && gcd(k_flag, m) == 1) {
      for (i = 0; i < r; i++) W[i] = k_flag;
    } else if (k_flag > 10 && k_flag < 20) {
      int j;
      num_rem = k_flag-10;
      printf("Type in %d numbers: ", num_rem);
      i = 0; 
      while (i < num_rem) { scanf("%d", &j); remainder[i++] = j; }
    }
    c = ((QGROUP + INCOMPLETE - RAMSEY)*newaddk - num_rem) / PMD;
  }

  /* decide Multi_blocks */
  if (MULTI > 1) {
    Multi_blocks = (c-INCOMPLETE)/MULTI+INCOMPLETE/MULTI;
    c -= Multi_blocks*(MULTI-1);
  }

  if (IDEMPOTENT == 1) {
    if (Multi_blocks)
      printf("Looking for %d %d-blocks (+ %d mod %d), the first %d are multi.\n\n", 
	     c, PMD, Addk, m, Multi_blocks);
    else
      printf("Looking for %d %d-tuples (+ %d mod %d).\n\n", c, PMD, Addk, m);
  } else {
    if (IDEMPOTENT == 3) {
      DOUBLE = (c) >> 1;
      Multi_blocks = Multi_blocks >> 1;
    } else 
      DOUBLE = (c-Addk*INCOMPLETE) >> 1;

    if (Addk <= 1 && 2*DOUBLE == c && INCOMPLETE % 2) --DOUBLE;
    c -= (DOUBLE);


    printf("Looking for %d %d-blocks (+ %d mod %d), of which the first %d are doubles.\n",
	   c, PMD, Addk, m, DOUBLE);
  }

  if (Num1) {
    /* decide Num1 blocks mod Add1 */
    c -= Num1*(Addk/Add1-1);
    if (c < 2) { printf("Less than one block is searched\n"); exit(0); }
    if (DOUBLE>0) DOUBLE -= Num1*(Addk/Add1-1);
    printf("Looking for %d %d-blocks of which the first %d are + %d mod %d, the rest are + %d mod %d.\n",
	   c, PMD, Num1, Add1, m, Addk, m);
  }

  if (r > MAX_ROW) {
    printf("MAX_ROW (%d) is too small (< %d).\n", 
	   MAX_ROW, r);
    exit(0);
  }
  if (c > MAX_COL) {
    printf("MAX_COL (%d) is too small (< %d).\n", 
	   MAX_COL, c);
    exit(0);
  }

  if (PMD == 2) { 
    rowoffset = 0; 
    kcm = m * c * 2 * Addk + 1;
  } else 
    kcm = m * c * K_apart * Addk + 1;

  rcm = (r-rowoffset) * c * m + 3;
  Max_atom = THI(K_apart-1, r-1, m-1, Addk-1);
  if (Addk != newaddk) Max_atom = TAO(K_apart-1, r*c-1, m-1, Addk-1);

  if (TRACE > 2) pmd_print_code(); 

  if (num_rem) {
    printf("The numbers that should be taken care specially:");
    for (i = 0; i < num_rem; i++) printf(" %d", remainder[i]);
    printf("\n\n");
  }
}

int pmd_fill_remainder (s, seed)
     int s, seed[];
{
  int k, i, j, y, good;
  int w = W[1]-1;

  /*
  printf("Give me the first nubmer to try: ");
  scanf("%d", &j);
  printf("You entered %d, a golden number!\n", j);
  */

  y = 0;
  for (i = 1; i < m; i++) if (seed[i] != HOLE) seed[i] = UNKNOW;
  i = 1;
  while (y < num_rem) {
    while (i < m && seed[i] != UNKNOW) i++;
    if (i >= m) { 
      i = m-1;
      while (i && seed[i] != UNKNOW) i--;
    }
    if (i == 0) return 0;

    good = 1;
    seed[i] = i;
    for (k = PMD/2-1; k >= 0; k--) if (good) {
      j = ((k+1)*i*w) % m;
      if (seed[j] == HOLE) good = 0;
      if (k == 0) {
	printf("j = %d\n", j);
	if (seed[Seed[j]] == -Seed[j]) good = 0;
	else seed[Seed[j]] = -Seed[j];
      }
    }
    if (good) { remainder[y++] = i; i = m-i; }
  }
  return 1;
}

void pmd_clause_init ()
{
  int i, j;

  Value[1] = TT;
  Value[2] = FF;
  if (OUTPUT) {
    print_unit_clause(stdout, TT, 1);
    print_unit_clause(stdout, FF, 2);
  }

  for (i = 0; i < r; i++) 
    for (j = 0; j < c; j++)  
      Oarray[i][j] = UNKNOW;
}

int pmd_clauses()
{
  int cl_arr [ MAX_ATOM ], sign_arr [ MAX_ATOM ];

  pmd_clause_init();

  if (FLAG >= 100) { FLAG = 0; return q100_clauses(); }
  if (k_flag >= 1000) { return blocks_clauses(); }
  if (PMD == 2) { return sfs_clauses(); }

  /* set the first row */
  if (pmd_unit_cls()) return 1;
  print_pmd(stdout);

  if (LINE >= 1000 && LINE <= 4000) {
    if (LINE == 4000) {
      if (CREATE < 5) pmd_gene_partials();
    } else if ((m % 2 == 0) || (m % 3 == 0)) {
      /* mod 2 or 3 unit blocks or clauses */
      if (LINE >= 2000) {
	if (pmd_mod23_blocks()) return 2;
      } else if (pmd_mod23_cls()) return 1;
    } else {
      printf("%d cannot be divided by 2 or 3\n", m);
      exit(0);
    }
  }

  /* additional constraints on row 2. */
  if (pmd_row2_cls(cl_arr, sign_arr)) return 1;

  if (num_rem && pmd_avoid_nums()) return 1;

  /* additional constraints */
  if (1 <= QUEEN && QUEEN <= 3 && pmd_resolve(cl_arr, sign_arr)) return 1;
  /*if (QUEEN == 3 && PMD == 4 && pmd_qg3_cls(cl_arr, sign_arr)) return 1;*/

  /* difference conditions */
  if (pmd_diff_cls(cl_arr, sign_arr)) return 1;

  /* unique values */
  if (pmd_unique_cls(cl_arr, sign_arr)) return 1;

  /* available values */
  if (pmd_posi_cls(cl_arr, sign_arr)) return 1;

  return 0;
}

int pmd_avoid_nums ()
{
  int i, j, k, u, w;

  printf("k_flag = %d, MULTI = %d, r = %d\n", k_flag, MULTI, r);

  if (k_flag == 4 && MULTI == r) 
    for (j = 0; j < num_rem; j++) {
      for (i = 1; i < m; i++) 
	if (((Seed[m]-1)*i) % m == remainder[j]) {
	  printf("replace %d by %d\n", remainder[j], i);
	  remainder[j] = i;
	  i = m;
	}
    }

  else if (k_flag == 2 || k_flag == 4 || k_flag == 100) {

    w = 1; 
    for (k = 1; k <= K_apart; k++) {
      w = (W[k] == 1)? k+1 : W[k];
      for (i = 0; i < num_rem; i++) {
	/*j = (remainder[i]*(w-1)) % m;*/
	int a, A;
	int y;
	int x = remainder[i]; 
	j = x;
	for (y = 2; y < w; y++) j = ABG_f[j][x];

	printf(">>>>>>>> avoiding %d in %d-apart\n", j, k);
	if (k_flag == 4) A = Addk; else A = 1;
	for (a = 0; a < A; a++) 
	  for (y = remainder[30]; y >= 0; y--) {
	    for (u = 0; u < c; u++) 
	      if (insert_cl_1(PHI(k-1, u, Seed[j], (a+y)), FF)) return 1;
	    for (u = 0; u < r; u++) 
	      if (insert_cl_1(THI(k-1, u, Seed[j], (a+y)), FF)) return 1;
	  }
      }
    }
  } else if (k_flag == 3) {
    for (k = 0; k < K_apart; k++) {
      for (i = 0; i < num_rem; i++) {
	j = remainder[i+k*num_rem]; 

	printf(">>>>>>>> avoiding %d in %d-apart\n", j, k+1);
	for (u = 0; u < c; u++) 
	    if (insert_cl_1(PHI(k, u, Seed[j], 0), FF)) return 1;
	for (u = 0; u < r; u++) 
	    if (insert_cl_1(THI(k, u, Seed[j], 0), FF)) return 1;
      }
    }
  }
  return 0;
}

int pmd_unique_cls (cl_arr, sign_arr)
     int cl_arr[], sign_arr[];
     /* every cell has at most one value */
{
  int x, y, u, v, r1, r2, a, k;

  for (x = 0; x < r; x++) 
    for (y = 0; y < c; y++) 
      for (u = m-1; u >= 0; u--) 
	for (v = u-1; v >= 0; v--) {
	  /* x * y = u and x * y = v imply u = v. */
	  if (insert_cl_2(SIG(x, y, u), 
			  SIG(x, y, v), 
			  FF, cl_arr, sign_arr)) return 1;
	}

  /* r1 * x = u and r2 * x = v and u-v = 0 imply r1 = r2. */
  for (r1 = 1; r1 < r; r1++) 
    for (r2 = r1-1; r2 >= 0; r2--) 
      for (x = 0; x < c; x++) 
	for (u = 0; u < m; u++)
	  for (v = 0; v < m; v++) {
	    y = DIFF(u, v);
	    if (Seed[y] == HOLE) {
	      if (insert_cl_2(SIG(r1, x, u), 
			      SIG(r2, x, v), 
			      FF, cl_arr, sign_arr)) return 1;
	    }
	  }

  /* 0 * x = 0 * y, x,y >= m, r2 * x = v and r2 * y = u imply v = u. */
  for (x = 0; x < c; x++)
    for (y = x+1; y < c; y++) 
      if (newaddk == Addk &&
	  Oarray[0][x] >= m && Oarray[0][x] == Oarray[0][y]) {
	for (r1 = 2; r1 < r; r1++) 
	  for (u = 0; u < m; u++) {
	    if (insert_cl_2(SIG(r1, x, u), 
			    SIG(r1, y, u), 
			    FF, cl_arr, sign_arr)) return 1;
	  }
      }

  for (a = 0; a < Addk; a++) {

    /* r1 * x = u and r1 * y = u imply x = y. */
    /*
    for (r1 = 1; r1 < r; r1++) 
      for (x = 1; x < a1; x++)
	for (y = 0; y < x; y++) 
	  for (u = 1; u < m; u++) {
	    if (insert_cl_2(SIG(r1, x+a*a1, u), 
			    SIG(r1, y+a*a1, u), 
			    FF, cl_arr, sign_arr)) return 1;
	  }

    for (r1 = 2; r1 < r; r1++) 
      for (x = 1; x < k1; x++) 
	for (y = 0; y < x; y++) 
	  for (u = 1; u < m; u++) {
	    if (insert_cl_2(SIG(r1, a1*newaddk+a*k1+x, u), 
			    SIG(r1, a1*newaddk+a*k1+y, u), 
			    FF, cl_arr, sign_arr)) return 1;
	  }
    */

    /* unique covering */
    if (0 < MOD && MOD < 7) {
      if (multi_cover_cls(a, cl_arr, sign_arr)) return 1;
    } else {

      for (k = K_apart-1; k >= 0; k--) if (PMD != 4 || QUEEN != 1 || k)
	for (x = 1; x < m; x++) {

	  for (u = 1; u < c; u++) 
	    for (v = u-1; v >= 0; v--) {
	      int x1, x2;
	      if (u < Multi_blocks) {
		x1 = x2 = Seed[x];
	      } else if (v >= Multi_blocks) {
		x1 = x2 = x;
	      } else {
		x1 = Seed[x];
		x2 = x;
	      }

	      /* PHI(k, u, x, a) and PHI(k, v, x, a) => u = v */
	      if (insert_cl_2(PHI(k, u, x2, a), 
			      PHI(k, v, x1, a), 
			      FF, cl_arr, sign_arr)) return 1;
	    }
	    
	  for (u = 1; u < r; u++) 
	    for (v = u-1; v >= 0; v--) {
	      /* THI(k, u, x, a) and THI(k, v, x, a) => u = v */
	      if (insert_cl_2(THI(k, u, x, a), 
			      THI(k, v, x, a), 
			      FF, cl_arr, sign_arr)) return 1;
	    }
	}

      if (PMD == 4 && QUEEN == 1)
	for (x = 1; x < m; x++) {
	  for (u = 2; u < c; u++) 
	    for (v = u-1; v >= 0; v--) 
	      for (k = v-1; k >= 0; k--) {
		/* PHI(0, u, x, a) and PHI(0, v, x, a) and 
		   PHI(0, k, x, a) => u = v | u = k | v = k */
		if (insert_cl_all_3(PHI(0, u, x, a), 
				    PHI(0, v, x, a), 
				    PHI(0, k, x, a), 
				    FF, cl_arr, sign_arr)) return 1;
	      }
	    
	  for (u = 2; u < r; u++) 
	    for (v = u-1; v >= 0; v--) {
		/* THI(0, u, x, a) and THI(0, v, x, a) and
		   THI(0, k, x, a) => u = v  u = v */
		if (insert_cl_2(THI(0, u, x, a), 
				THI(0, v, x, a), 
				FF, cl_arr, sign_arr)) return 1;
	      }
	}
    }
  }

  return 0;
}

multi_cover_cls (a, cl_arr, sign_arr)
     int a, cl_arr[], sign_arr[];
{
  int k, x, u, v, i, g;
  int comb[8];
  int h = MOD;
  
  for (k = K_apart-1; k >= 0; k--)
    for (x = 1; x < m; x++) {

      for (u = 0; u <= h; u++) comb[u] = u;
      g = c*r-1;
      while (comb[0] != g) {
	u = 0;
	for (i = h; i >= 0; i--) {
	  /* TAO(k, u, x, a) and TAO(k, v, x, a) => u = v */
	  v = cl_arr[u++] = TAO(k, comb[i], x, a);
	  sign_arr[v] = FF;
	}
	Clause_num++;
	if (insert_clause ( cl_arr, sign_arr, u)) return 1;

	if ((comb[0] + h) == g)
	  comb[0] = g;
	else 
	  next_combination(h, g, comb);
      }
    }

  return 0;
}

int pmd_row2_cls (cl_arr, sign_arr)
     int cl_arr[], sign_arr[];
{
  int i, j, u, v;

  if (RESTRICT) {
    /* increasing third column for (x 0 . . . .) */
    for (j = 0; j < c; j++) if (Oarray[0][j] >= m) {
      for (i = j+1; i < c; i++) 
	if (Oarray[0][i] >= m && Oarray[1][j] == Oarray[1][i])
	  for (u = 2; u < m; u++)
	    for (v = u-1; v > 0; v--) {
	      if (insert_cl_2(SIG(2, i, v), 
			      SIG(2, j, u), 
			      FF, cl_arr, sign_arr)) return 1;
	    }
    }

    /* increasing second column for (0 . . . .) */
    for (j = 0; j < c; j++) if (Oarray[0][j] < m) {
      for (i = j+1; i < c; i++) 
	if (Oarray[0][j] == Oarray[0][i])
	  for (u = 2; u < m; u++)
	    for (v = u-1; v > 0; v--) {
	      if (insert_cl_2(SIG(1, i, v), 
			      SIG(1, j, u), 
			      FF, cl_arr, sign_arr)) return 1;
	    }
    }
  }

  return 0;
}

int pmd_posi_cls (cl_arr, sign_arr)
     int cl_arr[], sign_arr[];
  /* every cell must have a value */
{
  int i, j, u, v;

  for (i = 0; i < r; i++) 
    for (j = 0; j < c; j++) 
      if (Oarray[i][j] < 0) {
	v = 0;
	for (u = m-1; u >= 0; u--) {
	  cl_arr[v] = SIG(i, j, u);
	  sign_arr[cl_arr[v++]] = 1;
	}
	Clause_num++;
	if (insert_clause ( cl_arr, sign_arr, v) == 1)	return 1;
      }
  return 0;
}

int pmd_diff_cls (cl_arr, sign_arr)
     int cl_arr[], sign_arr[];
{
  int x, y0, y, y2, u, v, r1, r2, k;

  if (IDEMPOTENT == 3 && PMD == 5) {
    for (x = 0; x < c; x++) if (Oarray[0][x] >= m) {
      r2 = (x < Num1)? Add1 : (Addk < 2)? 2 : Addk;
      for (y = 0; y < c; y++) if (Oarray[0][x] == Oarray[0][y]) 
	for (u = 0; u < m; u++) {

	  /* In <-, 0, c, d, e>, c and d have different oddity. */
	  for (v = 0; v < m; v++) if (v % r2 == u % r2) {
	    if (x < y) {
	      if (insert_cl_2(SIG(1, x, v), 
			      SIG(1, y, u), 
			      FF, cl_arr, sign_arr)) return 1;
	      if (insert_cl_2(SIG(2, x, v), 
			      SIG(2, y, u), 
			      FF, cl_arr, sign_arr)) return 1;
	      if (insert_cl_2(SIG(3, x, v), 
			      SIG(3, y, u), 
			      FF, cl_arr, sign_arr)) return 1;
	      if (insert_cl_2(SIG(4, x, v), 
			      SIG(4, y, u), 
			      FF, cl_arr, sign_arr)) return 1;
	    }
	    if (insert_cl_2(SIG(1, x, v), 
			    SIG(4, y, u), 
			    FF, cl_arr, sign_arr)) return 1;
	    if (insert_cl_2(SIG(2, x, v), 
			    SIG(3, y, u), 
			    FF, cl_arr, sign_arr)) return 1;
	  }
	}
    }
  }

  for (k = 0; k < K_apart; k++) 
    for (x = 0; x < c; x++) {
      int delta = (x < Num1)? Add1 : Addk;
      for (u = 0; u < m; u++)
	for (v = 0; v < m; v++) {
	  y0 = DIFF(u, v);
	  for (r1 = 0; r1 < r; r1++) {
	    y = y0; /* (y0 * W[(r1)? (r-r1) : 0]) % m;*/
	    r2 = (r1 + 1 + k) % r;
	    if (y && Seed[y] != HOLE) {
	      /* DIFF(u, v) is not in H. */

	      if (x < DOUBLE && (SPCD == 0) && 
		  Seed[y] == Seed[ABG_g[y]] &&
		  u % delta == v % delta) {

		if (insert_cl_2(SIG(r1, x, v), 
				SIG(r2, x, u), 
				FF, cl_arr, sign_arr)) return 1;

	      } else if (Addk != newaddk) {
		if (insert_cl_all_3(SIG(r1, x, v), 
				    SIG(r2, x, u), 
				    TAO(k, r1*c+x, Seed[y], u%Addk),
				    TT, cl_arr, sign_arr)) return 1;
	      } else {
		int d;
		for (d = 0; d < Addk; d += delta) {
		  y2 = (x < Multi_blocks)? Seed[y] : y;

		  if (SPCD == 0 || QGROUP > 14 ||
		      k != 1 || (y != SPCD && ABG_g[y] != SPCD)) {

		    if ((PMD != 4 || QUEEN != 1 || k) &&
			insert_cl_all_3(SIG(r1, x, v), 
					SIG(r2, x, u), 
					PHI(k, x, y2, (u+d)%Addk),
					TT, cl_arr, sign_arr)) return 1;

		    if (insert_cl_all_3(SIG(r1, x, v), 
					SIG(r2, x, u), 
					THI(k, r1, y2, (u+d)%Addk),
					TT, cl_arr, sign_arr)) return 1;
		  }

		  if (x < DOUBLE) {
		    y2 = (x < Multi_blocks)? Seed[ABG_g[y]] : ABG_g[y];
		    if (SPCD == 0 || (y != m/2 && v > 5)
			/* || (y != m/2 &&
			   y != SPCD && y2 != SPCD)*/) {
		      if (insert_cl_all_3(SIG(r1, x, v), 
					  SIG(r2, x, u), 
					  PHI(k, x, y2, (v+d)%Addk),
					  TT, cl_arr, sign_arr)) return 1;
		      if (insert_cl_all_3(SIG(r1, x, v), 
					  SIG(r2, x, u), 
					  THI(k, r1, y2, (v+d)%Addk),
					  TT, cl_arr, sign_arr)) return 1;
		    }
		  }
		}
	      }
	    } 
	  }
	}
    }

  if (PMD == 4 && QUEEN == 1)
    for (x = 0; x < c; x++) 
      for (u = 0; u < m; u++)
	for (v = 0; v < m; v++) {
	  y = DIFF(u, v);
	  if (y > m/2) y = m-y;
	  for (r1 = 0; r1 < r; r1++) {
	    r2 = (r1 + 1 + k) % r;
	    if (y && Seed[y] != HOLE) {
	      /* DIFF(u, v) is not in H. */
	      if (insert_cl_all_3(SIG(r1, x, v), 
				  SIG(r2, x, u), 
				  PHI(0, x, y, u%Addk),
				  TT, cl_arr, sign_arr)) return 1;
	    }
	  }
	}

  return 0;
}

int pmd_resolve (cl_arr, sign_arr)
     int cl_arr[], sign_arr[];
     /* every cell has a unique value */
{
  int x, y, u, v, r1, r2, a, step;

  step = m;
  if (DOUBLE) step = step >> 1;

  if (QUEEN == 2) {
    for (a = 0; a < Addk; a++) 
      for (r1 = 0; r1 < r; r1++) 
	for (x = a; x < c; x += Addk) 
	  for (u = 0; u < m; u += NHOLE) 
		if (insert_cl_1(SIG(r1, x, u), FF)) return 1;
  }

  if (QUEEN == 3) { /* frame construction */
    for (r1 = 1; r1 < r; r1++) 
      for (x = 0; x < c; x++) 
	for (u = 0; u < m; u += NHOLE) 
	  if (insert_cl_1(SIG(r1, x, u), FF)) return 1;
  }
	
  for (a = 0; a < Addk; a++) 
    for (r1 = 0; r1 < r; r1++) 
      for (r2 = 0; r2 < r; r2++) 
	for (x = a; x < c; x += Addk) 
	  for (y = a; y < c; y += Addk) if (r1 != r2 || x != y)
	    for (u = m-1; u >= 0; u--) 
	      for (v = u; v < m; v += step) {
		/* r1 * x = u and r2 * y = v imply u = v. */
		if (insert_cl_2(SIG(r1, x, u), 
				SIG(r2, y, v), 
				FF, cl_arr, sign_arr)) return 1;
	      }

  return 0;
}

int avoid_entry_in_col (r1, c1, num)
  int r1, c1, num;
{
  int i, j;

  for (i = r1; i < r; i++) {
    if (NHOLE) {
      for (j = 0; j < m; j++) {
	int y = DIFF(num,j);
	if ((Seed[y] == HOLE) && 
	    (insert_cl_1(SIG(i, c1, j), FF))) { bug(8); return 1; }
      }
    } else 
      if (insert_cl_1(SIG(r1, c1, num), FF)) { bug(8); return 1; }
  }
  return 0;
}

int pmd_unit_cls ()
{
  int i, j, k, k1, a, x;

  k = INCOMPLETE/MULTI;

  if (LINE >= 4000) pmd_read_partial();

  if (IDEMPOTENT == 3) {

    /*if (insert_cl_1(SIG(4, 1, 1), FF)) { bug(8); return 1; }*/

    /* in case the number of colums is not even */
    for (a = 0;  a < Addk; a++) {
      if (k % 2 && Addk != 2) {
	set_entry2(1,c-Addk+a, a); 
	set_entry1(0,c-Addk+a,m+k-1); 
	
	if (c > DOUBLE+1) {
	  if (NHOLE) for (j = 1; j < m; j++) 
	    if ((Seed[j] == HOLE) && 
		insert_cl_1(SIG(1, c-2*Addk+a, j), FF)) { bug(8); return 1; }
	}
      } else if (c > DOUBLE) {
	set_entry1(0,c-Addk+a,0);
	if (insert_cl_1(SIG(1, c-Addk+a, 0), FF)) { bug(8); return 1; }
	if (NHOLE) for (j = 1; j < m; j++) 
	  if ((Seed[j] == HOLE) && 
	      insert_cl_1(SIG(1, c-Addk+a, j), FF)) { bug(8); return 1; }
      }
    }
    
    k = k/2;
    x = 0;
    /* pre-set the places of infinity elements at the first row */
    for (i = DOUBLE-k*Addk; i < DOUBLE; i++) {
      set_entry2(1,i,0);
      set_entry1(0,i,m+(x++));
    }

    x = (m-RAMSEY)/2;
    for (i = DOUBLE-k*Addk-1; i >= 0; i--) {
      int x11 = (i >= x)? i-x+1 : 0;
      if (Oarray[0][i] == UNKNOW) 
	if (insert_cl_1(SIG(1, i, x11), FF)) { bug(8); return 1; }
      set_entry1(0,i,x11);
      if (NHOLE) 
	for (j = 1; j < m; j++) 
	  if ((Seed[j] == HOLE) && 
	      insert_cl_1(SIG(1, i, j+x11), FF)) { bug(8); return 1; }
    }

  } /* end of if (IDEMPOTENT == 3) */
  else {

    /* pre-set the places of infinity elements at the first row */
    if (Multi_blocks) {
      x = Multi_blocks-k*newaddk;
      for (a = 0; a < newaddk; a++) 
	for (i = 0; i < k; i++) {
	  set_entry2(1,x+i+newaddk*a,a%Addk);
	  set_entry1(0,x+i+newaddk*a,m+i);
	  if (avoid_entry_in_col(2, x+i+newaddk*a, a%Addk)) return 1;
	}

      k1=INCOMPLETE-k*MULTI;
    } else {
      k1=INCOMPLETE;
    }

    j = (QUEEN > 0)? 1 : 0;
    x=c-k1*newaddk;
    for (a = 0; a < newaddk; a++) 
      for (i = 0; i < k1; i++) {
	int y = x+a+i*newaddk;
	set_entry1(0,y,m+i%k1);
	set_entry2(1,y,(j+a%Addk+(x+i)/Addk)%m);
	if (avoid_entry_in_col(2, y, (j+a%Addk+(i+x)/Addk)%m)) return 1;
	/*
	  set_entry2(1,y,a%Addk);
	  set_entry1(0,y,m+k*MULTI+a);
	  if (avoid_entry_in_col(2, y, a%Addk)) return 1;
	*/
      }

    /* pre-set the places of 0 elements at the first row */
    for (i = 0; i < c; i++) if (Oarray[0][i] < m) { 
      if (QUEEN == 3) {
	j += 1-rand()%2;
	if ((j+i/Addk) % NHOLE == 0) ++j;
      }
      set_entry1(0,i,j+i/Addk);
      if (avoid_entry_in_col(1, i, j+i/Addk)) return 1;
    }
  }

  /* restriction on the first few columns */
  if (RESTRICT < 50 && RESTRICT % 10 != 0) {
    int v1 = (Oarray[1][0] < 0)? 1 : Oarray[1][0]+1;
    int m1 = 5-RESTRICT/10;
    int x1 = RESTRICT%10;
    if (m1 < 1) m1 = 1;

    while (Seed[v1] != v1) v1++;
    for (j = x1-1; j >= 0; j--) {
      int y;
      for (y = v1+(j)*m1+1; y < m; y++) {
	if (Oarray[0][j] == 0) {
	  /*printf("A[1, %d] != %d\n", j, y);*/
	  if (insert_cl_1(SIG(1, j, y), FF)) { bug(8); return 1; }
	} else {
	  /*printf("A[2, %d] != %d\n", j, y);*/
	  if (insert_cl_1(SIG(2, j, y), FF)) { bug(8); return 1; }
	}
      }
    }
  } else if (RESTRICT >= 200 && RESTRICT < 1000 && (RESTRICT % 100 == 0)) {
    int u = RESTRICT/100;
    int v = c/u;
    x = i = 0;
    for (j = 0; j < c; j++) if (Oarray[3][j] == UNKNOW) {
      printf("<3,%d> = ", j);
      for (k = 1; k < m; k++) if (k % u != x) {
	if (insert_cl_1(SIG(3, j, k), FF)) { bug(8); return 1; }
      }
      if (++i == v) { 
	i = 0; 
	printf("%d mod %d\n", x, u);
	if (++x == u) x = 0; 
      }
    }
    printf("\n");
  } else if (RESTRICT>0)  {
    i = j = 0;
    while (j < 3) { if (Seed[++i] != HOLE) j++; }
    for (j = i; j < m; j++) {
      if (insert_cl_1(SIG(1, 0, j), FF)) { bug(8); return 1; }
    }
  }

  return 0;
}

void print_one_pmd_block (file, j, k)
  FILE *file;
  int j, k;
{
  int x, y, i; 

  fprintf(file, "\n ");
  for (x = 0; x < k; x++) fprintf(file, " ");
  fprintf(file, "( ");

  for (i = 0; i < r; i++) {
    if (Oarray[i][j] < m) {
      y = Oarray[i][j];
      for (x = 0; x < k; x++) y = Mext[y];
      fprintf(file, "%2d ", y);
    } else {
      y = Oarray[i][j]-m+1+k*INCOMPLETE/MULTI;
      fprintf(file, "x%d ", y);
    }
  }
  fprintf(file, ")   ");

  for (y = 1; y <= K_apart; y++) {
    fprintf(file, "    ");
    if (y > 1 && Oarray[0][j] >= m) fprintf(file, "      "); 
    for (i = 0; i < r; i++) {
      int i1 = (i + y) % r;
      if (Oarray[i][j] < m && Oarray[i1][j] < m) {
	int x2 = (W[(i)? r-i : 0] * DIFF(Oarray[i1][j], Oarray[i][j])) % m;
	for (x = 0; x < k; x++) x2 = Mext[x2];
	if (PMD == 5) { 
	  int a = Oarray[i][j];
	  int b = Oarray[i1][j];
	  int x; 
	  for (x = 0; x < m; x += (j < Num1)? Add1 : Addk) 
	    Diffs[y-1][ABG_f[a][x]][ABG_f[b][x]] = 1;
	}
	fprintf(file, " %2d", x2);
      }
    }
  }

  if (PMD == 2) {
    fprintf(file, "    ");
    if (Oarray[0][j] < m && Oarray[1][j] < m) {
      int x2 = (W[(i)? r-i : 0] * ABG_f[Oarray[1][j]][Oarray[0][j]]) % m;
      for (x = 0; x < k; x++) x2 = Mext[x2];
      fprintf(file, " %2d %2d", x2, m-x2);
    }
  }

  if (j < DOUBLE) {
    fprintf(file, "\n  ");
    for (x = 0; x < k; x++) fprintf(file, " ");
    fprintf(file, "  (");

    for (i = r-1; i >= 0; i--) {
      if (Oarray[i][j] < m) {
	y = Oarray[i][j];
	for (x = 0; x < k; x++) y = Mext[y];
	fprintf(file, "%2d ", y);
      } else {
	y = Oarray[i][j]-m+1+k*INCOMPLETE/MULTI;
	fprintf(file, "x%d ", y);
      }
    }
    fprintf(file, ")   ");

    for (y = 1; y <= K_apart; y++) {
      fprintf(file, "    ");
      if (y > 1 && Oarray[0][j] >= m) fprintf(file, "      "); 
      for (i = r-1; i >= 0; i--) {
	int i1 = (i + r - y) % r;
	if (Oarray[i][j] < m && Oarray[i1][j] < m) {
	  /* W[i] or W[i1]? */
	  int x2 = (W[(i)? r-i : 0] * DIFF(Oarray[i1][j], Oarray[i][j])) % m;
	  for (x = 0; x < k; x++) x2 = Mext[x2];
	  if (PMD == 5) { 
	    int a = Oarray[i][j];
	    int b = Oarray[i1][j];
	    int x; 
	    for (x = 0; x < m; x += (j < Num1)? Add1 : Addk) 
	      Diffs[y-1][ABG_f[a][x]][ABG_f[b][x]] = 1;
	    fprintf(file, " %2d", x2);
	  }
	}
      }
    }
  }
}

void print_pmd (file)
     FILE *file;
{
  int i, j, y, k;

  if (PMD == 5) {
    for (i = 0; i < 2; i++) 
      for (j = 0; j < m; j++) 
	for (y = 0; y < m; y++) 
	  Diffs[i][j][y] = 0;
  }

  fprintf(file, "\n     Base Blocks    ");
  for (y = 1; y <= K_apart; y++) {
    for (i = 0; i < PMD; i++) fprintf(file, "  ");
    fprintf(file, " %d-apart", y);
  }

  for (j = 0; j < Multi_blocks; j++) {
    for (k = 0; k < MULTI; k++) {
      print_one_pmd_block(file, j, k);
    }
  } 

  for (j = Multi_blocks; j < c; j++) {
    print_one_pmd_block(file, j, 0);
  }

  fprintf(file, "\n\n");

  if (num_rem > 0 && k_flag != 3 && k_flag != 100) {
    if (k_flag == 4 && MULTI == r) {
      W[0] = 1; 
      i = Seed[m]; j = 1;
      while (i != 1) { W[j++] = i; i = (i*Seed[m])%m; }
    } else if (W[1] == 1)
      for (i = 0; i < r; i++) W[i] = i+1;

    printf("Additional blocks:\n");
    for (i = 0; i < num_rem; i++) {
      fprintf(file, "   (");
      for (j = 0; j < PMD; j++) 
	fprintf(file, "%2d ", (remainder[i]*(W[j]-1))%m);
      fprintf(file, ")\n");
    }
    fprintf(file, "\n");

    fprintf(file, "For non-Abelian group:\n");
    for (i = 0; i < num_rem; i++) {
      int i2;
      fprintf(file, "   (");
      i2 = 0;
      for (j = 0; j < PMD; j++) {
	fprintf(file, "%2d ", i2);
	i2 = ABG_f[i2][remainder[i]];
      }
      fprintf(file, ")\n");
    }
    fprintf(file, "\n");
  }

  if (SPCD && PMD != 2) {
    fprintf(file, "Checking diffs: ");
    for (i = 0; i < 2; i++) 
      for (j = 0; j < m; j++) 
	for (y = 0; y < m; y++) 
	  if (j != y && Diffs[i][j][y] == 0) {
	    fprintf(file, "pair <%d, %d> missing in %d-diff\n",
		    j, y, i+1);
	    Branch_succ--;  Branch_fail++; 
	    return;
	  }
    fprintf(file, "every pair is there.\n");
  }
}

void print_pmd_model2 (file)
     FILE *file;
{
  int i, x, y, z;

  for (i = rcm; i > 2; i--) if (Value[i] == TT) {
    z = (i-3) % m;
    x = (i-3) / m;
    y = x % c;
    x = rowoffset + x / c;
    Oarray[x][y] = z;
  }
  
  if (INCOMPLETE == 0 || INCOMPLETE == RAMSEY)
    fprintf(file, "\n%d-HPMD(%d^%d) #%d:\n", 
	    PMD, RAMSEY, ((INCOMPLETE)?1:0)+m/RAMSEY, Branch_succ);
  else 
    fprintf(file, "\n%d-HPMD(%d^%d, %d^1) #%d:\n", 
	    PMD, RAMSEY, m/RAMSEY, INCOMPLETE, Branch_succ);
  print_pmd(file);

  if (MODEL != 1) pmd_unit_cls();
}

void print_pmd_model (file)
     FILE *file;
{
  if (SPCD && PMD != 2) {
    FILE *file2;
    char s[20];
    sprintf(s, "pmd.%d%d%d", QGROUP, SPCD, m);
    file2 = fopen(s, "w");
    print_pmd_model2(file2);
    fclose(file2);
  }

  if (SPCD == 0 || Branch_succ)
    print_pmd_model2(file);
}

void pmd_print_code()
{
  int i, j, x, y, a;

  printf("rcm = %d, kcm = %d, Max_atom = %d, Addk = %d\n\n", 
	 rcm, kcm, Max_atom, Addk);

  for (i = 1; i < r; i++)
    for (j = 0; j < c; j++)
      for (x = 0; x < m; x++) {
	printf("SIG(%d, %d, %d) = %d\n", i, j, x,SIG2(i,j,x));
      }    

  if (Addk != newaddk) {
    for (i = 0; i < K_apart; i++)
      for (j = 0; j < c*r; j++)
	for (x = 1; x < m; x++) 
	  for (a = 0; a < Addk; a++) {
	    printf("TAO(%d, %d, %d, %d) = %d\n", i, j, x, a, TAO(i,j,x,a));
	  }    
  } else {
    for (i = 0; i < K_apart; i++)
      for (j = 0; j < c; j++)
	for (x = 1; x < m; x++) 
	  for (a = 0; a < Addk; a++) {
	    printf("PHI(%d, %d, %d, %d) = %d\n", i, j, x, a, PHI(i,j,x,a));
	  }    

    for (i = 0; i < K_apart; i++)
      for (y = 0; y < r; y++) 
	for (x = 1; x < m; x++) 
	  for (a = 0; a < Addk; a++) {
	    printf("THI(%d, %d, %d, %d) = %d\n", i, y, x, a, THI(i,y,x,a));
	  }
  }
} 

pmd_read_partial ()
{
  int i, j, k;
  char name[20];

  sprintf(name, "c%d.in", OARRAY);
  if (Input_sqs == NULL) { open_input_sqs(name); }
  if (fscanf(Input_sqs, "%d", &i) == EOF) {
    printf("No more blocks.\n"); 
    fclose(Input_sqs);
    Input_sqs = NULL;
    return 1;
  }

  printf("Read in a partial set of blocks:\n");
  for (j = 0; j < c; j++) {
    printf("\n ( ");
    for (i = 0; i < r; i++) {
      if (fscanf(Input_sqs, "%d", &k) == EOF) { printf("\n"); return 0; }
      if (k < 0) {
	printf("X ");
      } else {
	if (k >= m) 
	  printf("x%d ", k-m+1);
	else
	  printf("%d ", k);
	if (i) set_entry(i,j,k);
      }
    }
    printf(")");
  }
  printf("\n\n");

  return 0;
}

void pmd_gene_partials ()
{
  printf("Getting there ...\n");
  fix_remainder(PMD);
  printf("Jessus Chris!\n");
  exit (0);
}

int pmd_fill_seed(s)
     int s;
{
  int i, j, k, reps[50], comb[50], w[10];
  int x, y, z, z0, good;
  int oarray[MAX_ROW][MAX_COL];

  k = 0;
  printf("working on %d ...\n", s);
  i = fill_seed(s, PMD);
  for (j = 1; j < m; j++) if (Seed[j] == j) {
    printf("[ %d", y = j);
    for (x = 1; x < PMD; x++) {
      y = Mext[y];
      if (y == j) x = m;
      else printf(", %d", y);
    }
    printf(" ]\n");
    if (x < m) reps[k++] = j;
  }

  printf("\nGenerating tables ...\n");
  Input_sqs = (FILE *) open_fname_out("w");
  x = s; w[0] = 0; w[1] = 1;
  for (y = 2; y < PMD; y++) { w[y] = ABG_f[x][w[y-1]]; x = (x * s)%m; }

  x = RESTRICT % 100;
  if (x > k) { printf("Warning: impossible to pick %d out of %d\n", x, k);
	       exit(0); }
  if (x >= c || Oarray[0][x-1] >= m) {
    printf("Warning: not enough number of blocks to fill (c = %d, n = %d)\n",
	   c, x);
    exit(0); 
  }
  
  z = 0; z0 = (RESTRICT%1000)+100;
  for (y = 0; (y <= x); y++) comb[y] = y;
  while (comb[0] != k && z < z0) {
    good = 1;
    for (j = 0; j < c; j++) {
      /*int h = reps[comb[j]];*/
      int h = (s-1)*reps[comb[j]];

      for (i = 0; i < PMD; i++) {
	if (Oarray[i][j] >= m)
	  oarray[i][j] = -1;
	else if (Oarray[i][j] >= 0)
	  oarray[i][j] = Oarray[i][j];
	else if (j < x) {
	  if (Seed[oarray[i][j] = (w[i]*h)%m] == HOLE) good = 0;;
	} else  oarray[i][j] = -2;
      }
    }

    printf("Finding a %s one:\n", (good)? "good" : "bad");
    if (good) fprintf(Input_sqs, "%d %d\n", ++z, x);
    for (j = 0; j < c; j++) {
      for (i = 0; i < PMD; i++) {
	printf("%d ", oarray[i][j]);
	if (good) fprintf(Input_sqs, "%d ", oarray[i][j]);
      }
      printf("\n");
      if (good) fprintf(Input_sqs, "\n");
    }

    printf("\n");
    if (good) fprintf(Input_sqs, "\n");

    if ((comb[0] + x) == k)
      comb[0] = k;
    else 
      next_combination(x, k, comb);
  }

  fclose(Input_sqs); 
  printf("Finding %d good tables.\n", z);
  return (s);
}

pmd_mod23_cls ()
{
  int array[MAX_COL][MAX_ROW];
  int mo, i, j, k;
  char name[20];

  sprintf(name, "b%d.in", LINE%1000);
  if (Input_sqs == NULL) { open_input_sqs(name); }
  if (fscanf(Input_sqs, "%d", &mo) == EOF) {
    printf("No more blocks.\n"); 
    fclose(Input_sqs);
    Input_sqs = NULL;
    return 1;
  }

  printf("Read in blocks mod %d:\n", mo);
  for (j = 0; j < c; j++) {
    printf("\n ( ");
    for (i = 0; i < r; i++) {
      if (Oarray[i][j] >= m) {
	printf("- ");
	fscanf(Input_sqs, "%d", &k);
	if (k != -1) { printf("Bad input (-1 expected): %d\n", k); exit(0); }
      } else {
	fscanf(Input_sqs, "%d", &k);
	printf("%d ", array[j][i] = k);
      }
    }
    printf(")");
  }
  printf("\n\n");

  /* generate unit clauses */
  for (i = 1; i < r; i++)
    for (j = 0; j < c; j++) if (Oarray[i][j] == UNKNOW)
      for (k = 1; k < m; k++) if (k % mo != array[j][i])
	if (insert_cl_1(SIG(i, j, k), FF)) return 1;

  return 0;
}

int pmd_mod23_blocks ()
{
  if (m % 3 == 0 && RESTRICT / 1000 == 3) {
    if (pmd_mod_blocks(3)) return 1; 
  } else if (m % 2 == 0) {
    if (pmd_mod_blocks(2)) return 1; 
  }

  return 0;
}

#define MAX_K_MOD 3
pmd_mod_blocks (mo)
     int mo;
     /* this function is very, very long, because it uses
	several 2 or 3 dimension arrays that cannot be easily past 
	as parameters. */
{
  int tuples[MAX_COL][21][MAX_ROW];
  int load[MAX_COL];
  int code[MAX_COL][201];
  int array[MAX_COL][MAX_ROW];
  int apar[MAX_COL][MAX_K_MOD][MAX_K_MOD];
  int goal[MAX_K_MOD][MAX_K_MOD], apar_sum[MAX_K_MOD][MAX_K_MOD];
  int c0, i, j, k, good;
  int x[MAX_K_MOD];

  /* initialize */
  for (k = 0; k < K_apart; k++) 
    for (i = 0; i < mo; i++) {
      goal[k][i] = apar_sum[k][i] = 0;
      for (j = 0; j < c; j++) apar[j][k][i] = 0;
    }
  for (j = 0; j < c; j++) code[j][0] = 0;
  for (j = 1; j < m; j++) if (Seed[j] != HOLE) 
    for (k = 0; k < K_apart; k++) goal[k][j % mo]++;

  if (MULTI > 1) {
    for (j = 1; j < m; j++) 
      if (Seed[j] != HOLE && (j % mo != Mext[j] % mo)) {
	printf("Multipliers in trouble: %d != %d mo %d\n", 
	       j, Mext[j], mo);
	exit(0);
      }

    for (i = 0; i < mo; i++)
      for (k = 0; k < K_apart; k++) 
	goal[k][i] /= MULTI;
  }
  for (i = 0; i < num_rem; i++) goal[0][remainder[i] % mo]--; 

  printf("Number of remainders by %d: ", mo);
  for (i = 0; i < mo; i++) printf(" %d of %d's,", goal[0][i], i); 
  printf("\n\n");

  /* skip the first few cases */
  j = 0;
  if (FLAG > 1000) { 
    c0 = 0;
    mod_init_col(mo, array[j], j);
    while (FLAG != c0) {
      mod_inc_col(mo, array[j], j);
      c0 = (Oarray[0][j] >= m) ? 1 : 0;
      for (k = 0; k < K_apart; k++) {
	mod_apart_count(mo, array[j], j, k, x);
	for (i = 0; i < mo-1; i++) {
	  c0 = (c0 << 3) + x[i];
	}
      }
      c0 += 1000;
      mod_insert_code(code[j], c0);
      printf("c0 = %d\n", c0);
    }
    good = 0; 
  } else {
    good = 1; 
  }

  /* fill the array */
  printf("Searching for blocks mod %d ...\n", mo);
  while (j < c) {

    if (good) {
      mod_init_col(mo, array[j], j);
    } else {
      good = 1;
      while (j >= 0 && good) {
	if (good = mod_inc_col(mo, array[j], j)) {
	  code[j][0] = 0;
	  if (j--) {
	    for (k = 0; k < K_apart; k++) 
	      for (i = 0; i < mo; i++) {
		apar_sum[k][i] -= apar[j][k][i];
		apar[j][k][i] = 0;
	      }
	  }
	}
      }
      if (good) { printf("\nNo table mod %d!!!\n\n", mo); return 1; }
      good = 1;
    }

    if (TRACE > 2) {
      printf("col %d: ( ", j);
      for (i = 0; i < r; i++) 
	if (Oarray[i][j] >= m) {
	  printf("- ");
	} else {
	  printf("%d ", array[j][i]);
	}
      printf(")\n");
    }

    for (k = 0; good && k < K_apart; k++) {
      mod_apart_count(mo, array[j], j, k, x);
      for (i = 0; i < mo; i++) 
	if ((apar_sum[k][i] + x[i]) > goal[k][i]) good = 0;

      if (good) {

	for (i = 0; i < mo; i++) {
	  apar[j][k][i] = x[i];
	  apar_sum[k][i] += x[i];

	  if (TRACE > 2)
	    printf("For %d-apart, remainder %d: %d in col %d, and %d in total (<= %d)\n", 
		   k+1, i, x[i], j, apar_sum[k][i], goal[k][i]);

	  }
      } else {
	/* backtracking */
	good = k;
	for (k = 0; k < good; k++) 
	  for (i = 0; i < mo; i++) {
	    apar_sum[k][i] -= apar[j][k][i];
	    apar[j][k][i] = 0;
	  }
	good = 0;
      }
    }

    if (good) {
      c0 = (Oarray[0][j] >= m) ? 1 : 0;
      for (k = 0; k < K_apart; k++) 
	for (i = 0; i < mo-1; i++) {
	  c0 = (c0 << 3) + apar[j][k][i];
	}

      c0 += 1000;
      if (TRACE > 2) printf("code of col %d = %d\n", j, c0);

      if ((j && c0 < code[j-1][200]) || mod_insert_code(code[j], c0)) {
	good = 0;
	/* backtracking */
	for (k = 0; k < K_apart; k++) 
	  for (i = 0; i < mo; i++) {
	    apar_sum[k][i] -= apar[j][k][i];
	    apar[j][k][i] = 0;
	  }
      } else 
	j++;
    } 
  }

  printf("The first set of blocks mod %d (initial code: %d):\n", 
	 mo, CREATE = code[0][200]);
  for (j = 0; j < c; j++) {
    printf("\n ( ");
    for (i = 0; i < r; i++) {
      if (Oarray[i][j] >= m) {
	printf("- ");
      } else {
	printf("%d ", array[j][i]);
      }
    }
    printf(")");
  }
  printf("\n\n");

  /* generate more sets of blocks */
  for (j = 0; j < c; j++) load[j] = 0;
  for (j = 0; j < c; j++) {
    code[j][0] = 0;
    mod_init_col(mo, array[j], j);
    good = 1;
    while (good) {
      for (k = 0; good && k < K_apart; k++) {
	mod_apart_count(mo, array[j], j, k, x);
	for (i = 1; i < mo; i++) if (apar[j][k][i] != x[i]) good = 0;
      }

      if (good && (j || Oarray[0][0] >= m || array[0][1] == 1)) {
	printf("col %d: ", j);
	for (i = 0; i < r; i++) {
	  if (Oarray[i][j] >= m) {
	    printf("- ");
	  } else {
	    printf("%d ", array[j][i]);
	  }
	}
	c0 = mod_encode(mo, array[j], j);
	printf(" (code = %d)\n", c0);

	/*
	for (k = 0; k < K_apart; k++) 
	  for (i = 0; i < mod; i++) 
	    printf("apar[%d][%d][%d] = %d != %d = x[%d]\n", j, k, i, apar[j][k][i], x[i], i);
	*/

	if (!mod_insert_code(code[j], c0)) {
	  if (load[j] < 20) {
	    k = load[j]++;
	    for (i = 0; i < r; i++) tuples[j][k][i] = array[j][i];
	  } else 
	    printf("overflow in 21\n");
	}

      }
      good = !mod_inc_col(mo, array[j], j);
    } 
  }

  for (j = 0; j < c; j++) {
    i = load[j];
    printf("%d col%d, ", i, j);
    code[j][200] = i-1;
    for (k = 0; k < i; k++) code[j][k] = mod_encode(mo, tuples[j][k], j);
  }
  printf("\n");

  Input_sqs = (FILE *) open_fname_out("w");
  good = 0;
  for (j = 0; j < c; j++) {
    load[j] = 0; 
    if (good < code[j][200]) good = code[j][200];
  }
  good++;

  while ( good ) {
    good--;
    fprintf(Input_sqs, "%d %d ", CREATE, mo);
    for (j = 0; j < c; j++) {
      for (i = 0; i < r; i++) {
	if (Oarray[i][j] >= m) {
	  fprintf(Input_sqs, "-1 ");
	} else {
	  fprintf(Input_sqs, "%d ", tuples[j][load[j]][i]);
	}
      }
    }
    fprintf(Input_sqs, "\n");

    for (j = 0; j < c; j++) {
      if (++load[j] >= code[j][200]) load[j] = 0;
    }
  }

  fclose(Input_sqs); 
  return 2;
}

void mod_init_col (mo, col, j)
     int mo, col[], j;
{
  int i;
  for (i = 0; i < r; i++) 
    if (Oarray[i][j] == UNKNOW) col[i] = 0;
    else if (Oarray[i][j] < m) col[i] = Oarray[i][j] % mo;
}

int mod_inc_col (mo, col, j)
     int mo, col[], j;
{
  int i;

  for (i = 0; i < r; i++) if (Oarray[i][j] == UNKNOW) {
    if (col[i] == mo-1) col[i] = 0;
    else { col[i]++; return 0; }
  }
  return 1;
}

void mod_apart_count(mo, col, j, k, x)
     int mo, col[], j, k, x[];
{
  int i;

  /*
  printf("col %d: ( ", j);
  for (i = 0; i < r; i++) 
    if (Oarray[i][j] >= m) {
      printf("- ");
    } else {
      printf("%d ", col[i]);
    }
  printf(")\n");
  */

  k++;
  for (i = 0; i < mo; i++) x[i] = 0;
  for (i = 0; i < r; i++) 
    if (Oarray[i][j] < m && Oarray[(i+k)%r][j] < m) {
      /*
      printf("c[%d] = %d, c[%d] = %d, c[%d] - c[%d] = %d\n",
	     (i+k)%r, col[(i+k)%r], i, col[i],
	     (i+k)%r, i, (mo + col[(i+k)%r] - col[i])%mo);
	     */
      if (k)
	x[(mo + col[(i+k)%r] - col[i])%mo]++;
      else
	x[col[i]%mo]++;
    }

  if (j < DOUBLE) {
    int col2[10];
    for (i = 1; i <= r; i++) col2[i-1] = col[r-i];
    for (i = 0; i < r; i++) 
      if (Oarray[i][j] < m && Oarray[(i+k)%r][j] < m) {
	if (k)
	  x[(mo + col2[(i+k)%r] - col2[i])%mo]++;
	else
	  x[col2[i]%mo]++;
      }
  }
}

int mod_insert_code (list, c)
     int list[], c;
     /* insert c into the list and keep the list sorted */
{
  int l, rr, mm;
  list[MAX_COL-1] = c;
  l = 1; rr = list[0]; 
  while (l <= rr) {
    mm = (l+rr)/2;
    if (list[mm] == c) { return 1; }
    /* c is already in the list */

    if (list[mm] > c) rr = mm-1;
    else l = mm+1;
  }

  /* c is not in the list */
  if (list[0] == MAX_COL-1) {
    printf("WARNING: Overflow in mo_insert_code: %d\n\n", MAX_COL); 
  } else {
    l = list[0]++;
    while (l > rr) { list[l+1] = list[l]; l--; }
    list[rr+1] = c;
  }

  /*
  printf("\nC: ");
  for (l = list[0]; l > 0; l--) printf("%d ", list[l]);
  printf("\n");
  */

  return 0;
}

mod_encode(mo, col, j)
     int mo, col[], j;
{
  int i, c0;
  
  c0 = (Oarray[0][j] >= m) ? 1 : 0;
  if (c0) 
    for (i = 1; i < r; i++)
      c0 = (c0 << mo) + col[i];
  else {
    int m1, m2, good;

    m1 = 0;
    for (m2 = 1; m2 < r; m2++) {
      good = 1;
      for (i = 0; (good > 0) && i < r; i++) 
	if (col[(m1+i)%r] > col[(m2+i)%r]) good = 0;
	else if (col[(m1+i)%r] != col[(m2+i)%r]) good = -1;
      if (!good) m1 = m2;
    }
    for (i = 1; i < r; i++) 
      c0 = (c0 << mo) + col[(i+m1)%r];
  }
  return c0;
}

void p_pmd() { print_pmd(stdout); }

/***************************/
int q100_clauses ()
{
  int cl_arr [ MAX_ATOM ], sign_arr [ MAX_ATOM ];

  if (q100_unit_cls()) return 1;

  if (q100_unique_cls(cl_arr, sign_arr)) return 1;

  if (q100_pair_cls(cl_arr, sign_arr)) return 1;

  if (pmd_posi_cls(cl_arr, sign_arr)) return 1;

  return 0;
}

int q100_unit_cls ()
{
  int x, y, i, j;
  int addk = get_addk();
  if (addk < 2) addk = QGROUP-1;

  for (i = addk-1; i >= 0; i--) if (i < c) {
    set_entry0(0,i,0);
    set_entry(1,i,i+1);
  }

  if (RESTRICT > 20) y = RESTRICT-20; else y = 2;
  x = 1; j = 0; 
  for (i = addk; i < c; i++) {
    set_entry0(0, i, x);
    j++;
    if (j == y) { x++; j = 0; }
  }

  for (i = 1; i < r; i++)
    for (x = 0; x < c; x++) 
      if (insert_cl_1(SIG(i, x, 0), FF)) { bug(9); return 1; }

  if (RESTRICT > 20) {
    /* restriction on the first column. */
    for (i = 2; i < r; i++)
      for (x = i+3; x < QGROUP; x++) 
	if (insert_cl_1(SIG(i, 0, x), FF)) { bug(10); return 1; }
  }

  return 0;
}

int q100_unique_cls (cl_arr, sign_arr)
     int cl_arr[], sign_arr[];
{
  int i, j, u, v;
  int addk = get_addk();
  if (addk < 2) addk = QGROUP-1;

  /* each entry has at most one value */
  /* i * j = u and i * j = v imply u = v. */
  for (i = 0; i < r; i++) 
    for (j = 0; j < c; j++) 
      for (u = QGROUP-1; u >= 0; u--) 
	for (v = u-1; v >= 0; v--) {
	  if (insert_cl_2(SIG(i, j, u), 
			  SIG(i, j, v), 
			  FF, cl_arr, sign_arr)) return 1;
	}

  /* no two elements are the same in the same column */
  /* i * v = u and j * v = u imply i = j. */
  for (i = 1; i < r; i++) 
    for (j = i-1; j >= 0; j--) 
      for (v = 0; v < c; v++) 
	for (u = 0; u < m; u++) {
	  if (insert_cl_2(SIG(i, v, u), 
			  SIG(j, v, u), 
			  FF, cl_arr, sign_arr)) return 1;
	}

  /* no two elements are the same in the same row */
  /* v * i = u and v * j = u imply i = j. */
  for (i = addk-1; i > 0; i--) if (i < c)
    for (j = i-1; j >= 0; j--) 
      for (v = 1; v < r; v++) 
	for (u = 0; u < QGROUP; u++) {
	  if (insert_cl_2(SIG(v, i, u), 
			  SIG(v, j, u), 
			  FF, cl_arr, sign_arr)) return 1;
	}

  /* last part of the second row is in increasing order */
  for (i = addk; i < c; i++) 
    for (j = 1; j < QGROUP; j++)
      for (u = 1; u < j; u++) {

	for (v = i+1; v < c; v++) 
	  if (insert_cl_2(SIG(1, i, j), 
			  SIG(1, v, u), 
			  FF, cl_arr, sign_arr)) return 1;

	if (insert_cl_2(SIG(0, i, j), 
			SIG(1, i, u), 
			FF, cl_arr, sign_arr)) return 1;
      }	

  return 0;
}

int q100_pair_cls (cl_arr, sign_arr)
     int cl_arr[], sign_arr[];
{
  int k, i, j, u, v;

  for (k = 0; k < K_apart; k++) 
    for (u = 0; u < m; u++)
      for (v = 0; v < m; v++) 
	for (i = c-1; i >= 0; i--) {

	  for (j = 0; j < r; j++) {
	    if (insert_cl_all_3(SIG(j, i, u),
				SIG((j+k+1)%r, i, v),
				YOYO(k, i, u, v),
				1, cl_arr, sign_arr))
	      return 1;
	  }

	  for (j = i+1; j < c; j++) {
	    if (insert_cl_2(YOYO(k, j, u, v),
			    YOYO(k, i, u, v),
			    0, cl_arr, sign_arr))
	      return 1;
	  }
	}

  return 0;
}

int sfs_clauses ()
{
  int cl_arr [ MAX_ATOM ], sign_arr [ MAX_ATOM ];

  if (OARRAY) pmd_read_partial();

  if (sfs_unit_cls()) return 1;

  if (sfs_unique_cls(cl_arr, sign_arr)) return 1;

  if (sfs_diff_cls(cl_arr, sign_arr)) return 1;

  if (pmd_posi_cls(cl_arr, sign_arr)) return 1;

  return 0;
}

int sfs_unit_cls ()
{
  int i, k;

  set_entry0(0,0,1);

  for (i = 0; i < c; i++) {

    for (k = 0; k < m; k++) 
      if (Seed[k] < 0) {
	if (insert_cl_1(SIG(0, i, k), FF)) { bug(8); return 1; }
	if (insert_cl_1(SIG(1, i, k), FF)) { bug(8); return 1; }
      } else if (Seed[k] != k || k > i+i+1) {
	if (insert_cl_1(SIG(0, i, k), FF)) { bug(8); return 1; }
	/* if (insert_cl_1(SIG(1, i, k), FF)) { bug(8); return 1; } */
      }

    if (i) {
      if (insert_cl_1(SIG(0, i, 1), FF)) { bug(8); return 1; }
      if (insert_cl_1(SIG(1, i, 1), FF)) { bug(8); return 1; }
    }
  }

  return 0;
}

int sfs_unique_cls (cl_arr, sign_arr)
     int cl_arr[], sign_arr[];
{
  int x, i, j, u, v, k;

  /* each entry has at most one value */
  /* i * j = u and i * j = v imply u = v. */
  for (i = 0; i < r; i++) 
    for (j = 0; j < c; j++) 
      for (u = m-1; u >= 0; u--) 
	for (v = u-1; v >= 0; v--) {
	  if (insert_cl_2(SIG(i, j, u), 
			  SIG(i, j, v), 
			  FF, cl_arr, sign_arr)) return 1;
	}

  /* each column is in increasing order */
  for (i = 0; i < c; i++) 
    for (u = 0; u < m; u++) 
      for (v = u; v < m; v++) {
	if (insert_cl_2(SIG(0, i, v), 
			SIG(1, i, u), 
			FF, cl_arr, sign_arr)) return 1;
      }

  /* the first row is in increasing order */
  for (i = 0; i < c; i++)
    for (j = i+1; j < c; j++) 
      for (u = 2; u < m; u++)
	for (v = u-1; v > 0; v--) {
	  if (insert_cl_2(SIG(0, i, u), 
			  SIG(0, j, v), 
			  FF, cl_arr, sign_arr)) return 1;

	  if (insert_cl_2(SIG(0, i, u), 
			  SIG(0, j, ABG_g[u]), 
			  FF, cl_arr, sign_arr)) return 1;

	  if (insert_cl_2(SIG(1, i, u), 
			  SIG(1, j, ABG_g[u]), 
			  FF, cl_arr, sign_arr)) return 1;
	}

  /* no two elements are the same in the table */
  for (i = 0; i < c; i++) 
    for (j = 0; j < c; j++) 
      for (u = 0; u < m; u++) {
	v = u;
	for (k = 0; k < MULTI; k++) {
	  v = Mext[v];
	  if (insert_cl_2(SIG(0, i, u), 
			  SIG(1, j, v), 
			  FF, cl_arr, sign_arr)) return 1;

	  if (i > j) {
	    if (insert_cl_2(SIG(0, i, u), 
			    SIG(0, j, v), 
			    FF, cl_arr, sign_arr)) return 1;
	    if (insert_cl_2(SIG(1, i, u), 
			    SIG(1, j, v), 
			    FF, cl_arr, sign_arr)) return 1;
	  }
	}
      }

  for (k = 0; k < 2; k++) 
    for (x = 1; x < m; x++) {
      int y1;
      int x1 = Seed[x];
      y1=Seed[ABG_g[x1]];

      for (i = 0; i < c; i++) {

	/* PHI(k, i, x, a) => PHI(k, i, -x, a) */
	if (insert_cl_2(PHI(k, i, x1, 0), 
			PHI(k, i, y1, 0), 
			TT, cl_arr, sign_arr)) return 1;

	for (v = 1; v < m; v++) if (Seed[v] != y1 && Seed[v] != x1) {
	  /* PHI(k, i, x, a) and PHI(k, i, v, a) => v = x */
	  if (insert_cl_2(PHI(k, i, x1, 0), 
			  PHI(k, i, v, 0), 
			  FF, cl_arr, sign_arr)) return 1;
	}

	for (j = i-1; j >= 0; j--) {
	  /* PHI(k, i, x, a) and PHI(k, j, x, a) => i = j */
	  if (insert_cl_2(PHI(k, i, x1, 0), 
			  PHI(k, j, x1, 0), 
			  FF, cl_arr, sign_arr)) return 1;
	}
      }
    }

  return 0;
}

int sfs_diff_cls (cl_arr, sign_arr)
     int cl_arr[], sign_arr[];
{
  int x, y, u, v, d;

  for (x = 0; x < c; x++) {
    int delta = (x < Num1)? Add1 : Addk;
    for (u = 0; u < m; u++)
      for (v = 0; v < m; v++) {

	y = DIFF(u, v);
	if (y && Seed[y] != HOLE) {
	  /* DIFF(u, v) is not in H. */
	  for (d = 0; d < Addk; d += delta) 
	    if (insert_cl_all_3(SIG(0, x, v), 
				SIG(1, x, u), 
				PHI(0, x, Seed[y], (u+d)%Addk),
				TT, cl_arr, sign_arr)) return 1;
	} else if (insert_cl_2(SIG(0, x, v), 
			       SIG(1, x, u), 
			       FF, cl_arr, sign_arr)) return 1;

	y = ABG_f[u][v];
	if (y && Seed[y] != HOLE) {
	  /* (u + v) is not in H. */
	  for (d = 0; d < Addk; d += delta) 
	    if (insert_cl_all_3(SIG(0, x, v), 
				SIG(1, x, u), 
				PHI(1, x, Seed[y], (u+d)%Addk),
				TT, cl_arr, sign_arr)) return 1;
	} else if (insert_cl_2(SIG(0, x, v), 
			       SIG(1, x, u), 
			       FF, cl_arr, sign_arr)) return 1;
      }
  }
  return 0;
}

int blocks_clauses ()
{
  int cl_arr [ MAX_ATOM ], sign_arr [ MAX_ATOM ];

  if (blocks_unit_cls()) return 1;

  /*pmd_extra_cls(); print_pmd(stdout); */

  if (blocks_unique_cls(cl_arr, sign_arr)) return 1;

  if (blocks_pair_cls(cl_arr, sign_arr)) return 1;

  if (pmd_posi_cls(cl_arr, sign_arr)) return 1;

  return 0;
}

int blocks_unit_cls ()
{
  int i, j;

  for (i = c-(k_flag % 100)-1; i >= 0; i--) set_entry0(0,i,0);
  for (i = c-(k_flag % 100); i < c; i++) set_entry0(0,i,1);
  for (i = c-((k_flag/100) % 10); i < c; i++) set_entry0(0,i,2);

  if (RESTRICT < 50 && RESTRICT % 10) {
    set_entry(1,0,1);
    for (j = 1; j < RESTRICT && j < c; j++) 
      for (i = m/2; i < m; i += j) {
	if (insert_cl_1(SIG(3, j, i), FF)) { bug(8); return 1; }
      }
  }

  return 0;
}

int blocks_unique_cls (cl_arr, sign_arr)
     int cl_arr[], sign_arr[];
{
  int x, i, j, u, v;

  /* each entry has at most one value */
  /* i * j = u and i * j = v imply u = v. */
  for (i = 0; i < r; i++) 
    for (j = 0; j < c; j++) 
      for (u = m-1; u >= 0; u--) 
	for (v = u-1; v >= 0; v--) {
	  if (insert_cl_2(SIG(i, j, u), 
			  SIG(i, j, v), 
			  FF, cl_arr, sign_arr)) return 1;
	}

  /* no two elements are the same in the same column */
  /* i * v = u and j * v = u imply i = j. */
  for (i = 1; i < r; i++) 
    for (j = i-1; j >= 0; j--) 
      for (v = 0; v < c; v++) 
	for (u = 0; u < m; u++) {
	  if (insert_cl_2(SIG(i, v, u), 
			  SIG(j, v, u), 
			  FF, cl_arr, sign_arr)) return 1;
	}


  /* the second row is in increasing order */
  x = c-(k_flag % 100);
  for (i = 0; i < x; i++)
    for (j = i+1; j < x; j++) 
      for (u = 2; u < m; u++)
	for (v = u-1; v > 0; v--) {
	  if (insert_cl_2(SIG(1, i, u), 
			  SIG(1, j, v), 
			  FF, cl_arr, sign_arr)) return 1;
	}
  for (i = x; i < c; i++)
    for (j = i+1; j < c; j++) 
      for (u = 2; u < m; u++)
	for (v = u-1; v > 0; v--) {
	  if (insert_cl_2(SIG(1, i, u), 
			  SIG(1, j, v), 
			  FF, cl_arr, sign_arr)) return 1;
	}

  return 0;
}

int blocks_pair_cls (cl_arr, sign_arr)
     int cl_arr[], sign_arr[];
{
  int k, i, j, i1, j1, u, v;

  for (i = 0; i < c; i++)
    for (i1 = i+1; i1 < c; i1++) 
      for (j = 0; j < r; j++)
	for (j1 = 0; j1 < r; j1++)
	  for (u = 0; u < m; u++)
	    for (v = 0; v < m; v++) 
	      for (k = 1; k <= K_apart; k++) {
		if (insert_cl_4(SIG(j, i, u),
				SIG((j+k)%r, i, v),
				SIG(j1, i1, u),
				SIG((j1+k)%r, i1, v),
				0, cl_arr, sign_arr))
		  return 1;
	      }
  return 0;
}

void print_short_blocks (q)
     int q;
{
  int x, y, z;
  int q2 = q+q;
  int i = 0;
  int badnums[20], badcount=0;
  int a[10];
  
  if (RAMSEY>1) {
    x = m/RAMSEY;
    for (y = 0; y < m; y += x) 
      badnums[badcount++] = y;
  }

  printf("Short blocks                1-apart  2-apart  3-apart\n");

  if (q2 == m) {
  for (x = 0; x < q; x++)
    for (y = x+1; y < m; y++) if (y % q > x) 
      for (z = y+1; z < m; z++) if (z % q > y) {
	a[1] = DIFF(y, x); 
	a[2] = DIFF(z, y);
	a[3] = DIFF(x+q, z);
	a[4] = DIFF(z, x);
	a[5] = DIFF(x+q, y);
	a[6] = DIFF((y+q)%m, z);
	a[7] = DIFF(x+q, x);
	a[8] = DIFF((y+q)%m, y);
	a[9] = DIFF((z+q)%m, z);

	if (good_short_block(a, 9, badnums, badcount)) {
	  printf("\n%2d: (%2d %2d %2d %2d %2d %2d )\n\t\t\t",
		 ++i, x, y, z, (x+q), (y+q)%m, (z+q)%m);
	  printf("    %2d %2d %2d", a[1], a[2], a[3]);
	  printf("    %2d %2d %2d", a[4], a[5], a[6]); 
	  printf("    %2d %2d %2d", a[7], a[8], a[9]);
	}

	a[1] = DIFF(z, x);
	a[2] = DIFF(y, z); 
	a[3] = DIFF(x+q, y);
	a[4] = DIFF(y, x);
	a[5] = DIFF(x+q, z);
	a[6] = DIFF((z+q)%m, y);
	a[7] = DIFF(x+q, x);
	a[8] = DIFF((z+q)%m, z);
	a[9] = DIFF((y+q)%m, y);

	if (good_short_block(a, 9, badnums, badcount)) {
	  printf("\n%2d: (%2d %2d %2d %2d %2d %2d )\n\t\t\t",
		 ++i, x, z, y, (x+q), (z+q)%m, (y+q)%m);
	  printf("    %2d %2d %2d", a[1], a[2], a[3]);
	  printf("    %2d %2d %2d", a[4], a[5], a[6]);
	  printf("    %2d %2d %2d", a[7], a[8], a[9]);
	}
      }
  } else
  for (x = 0; x < q; x++)
    for (y = x+1; y < m; y++) if (y % q > x) {
      a[1] = DIFF(y, x);
      a[2] = DIFF(x+q, y);
      a[3] = DIFF(x+q, x);
      a[4] = DIFF((y+q)%m, y);
      a[5] = DIFF((y+q)%m, x);
      a[6] = DIFF(x+q2, y);

      if (good_short_block(a, 6, badnums, badcount)) {
	printf("\n%2d: (%2d %2d %2d %2d %2d %2d )\n\t\t\t",
	       ++i, x, y, (x+q), (y+q)%m, (x+q2), (y+q2)%m);
	printf("    %2d %2d", a[1], a[2]);
	printf("    %2d %2d", a[3], a[4]);
	printf("    %2d %2d", a[5], a[6]);
      }

      a[1] = DIFF(y, x);
      a[2] = DIFF(x+q2, y);
      a[3] = DIFF(x+q2, x);
      a[4] = DIFF((y+q2)%m, y);
      a[5] = DIFF((y+q2)%m, x);
      a[6] = DIFF(x+q, y);

      if (good_short_block(a, 6, badnums, badcount)) {
	printf("\n%2d: (%2d %2d %2d %2d %2d %2d )\n\t\t\t",
	       ++i, x, y, (x+q2), (y+q2)%m, (x+q), (y+q)%m);
	printf("    %2d %2d", a[1], a[2]);
	printf("    %2d %2d", a[3], a[4]);
	printf("    %2d %2d", a[5], a[6]);
      }
    }
  printf("\n\n");
  exit(0);
}

int good_short_block (a, num, badnums, count)
     int a[], num, badnums[], count;
{
  int i;
  for (i = 1; i <= num; i++) {
    if (bad_short_num(a[i], badnums, count)) return 0;
    count++;
  }
  return 1;
}

int bad_short_num (i, badnums, c)
     int i, badnums[], c;
{
  int j;

  for (j = 0; j < c; j++) if (badnums[j] == i) return 1;
  badnums[c] = i;
  return 0;
}
