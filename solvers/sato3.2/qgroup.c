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

#define PHI(i,j,k) (((i) * n_sqt) + ((j) * n) + (k) + 1 + n_offset)
#define P2(i,j,k,l) ((((i) * n_sqt) + ((j) * n) + k) * n + l + 1 + n_offset)
#define P3(i,j,k,l) ((((i) * n_sqt) + ((j) * n) + k) * n + l + n_four)
#define neg(x) (n1-x)
#define C3(x,y) (Max_atom-((x)*3+y))
#define conj_TRIPLE2KEY(conj,x,y,z) TRIPLE2KEY(x, y, z)
/*
#define conj_TRIPLE2KEY(conj,x,y,z) (conj == 0)? TRIPLE2KEY(x, y, z) :\
			      (conj == 1)? TRIPLE2KEY(y, x, z) :\
			      (conj == 2)? TRIPLE2KEY(z, y, x) :\
			      (conj == 3)? TRIPLE2KEY(y, z, x) :\
			      TRIPLE2KEY(x, y, z)
*/

#define special_call(x,y,z,w,u,v) insert_cl_4(TRIPLE2KEY(x,y,u),TRIPLE2KEY(z,w,u),TRIPLE2KEY(y,x,v),TRIPLE2KEY(w,z,v),0,cl_arr,sign_arr)

int limit_of_hole = 0;
int double_cl = 0;
int m = 0;
int n = 0;
int n1 = 0;
int n_sqt, n_cube, n_four, n_offset;

GLOB int Lsquare2[MAX_SQUARE2][MAX_SQUARE2];

void locate_holes();

int get_num_of_hole () { return limit_of_hole; }
void set_num_of_hole (x) int x; { limit_of_hole = x; }

int multi_squares () { return double_cl; }
void set_double_cl (x) int x; { double_cl = x; }

void init_qgroups()
{
  if (CREATE == 4) system("mv outputsqs outputsqs~");

  m = QGROUP - INCOMPLETE;
  n = QGROUP;
  n1 = n-1;
  n_sqt = QGROUP * QGROUP;
  SQUARE2 = n_offset = n_cube = QGROUP * n_sqt;
  n_four = QGROUP*n_cube+1;

  if (LINE == 222) { read_two(); exit(1); }
  if ((QUEEN == 39) || (QUEEN == 40) || 
      (22 <= QUEEN && QUEEN <= 29) ||
      (50 <= QUEEN && QUEEN <= 54) ||
      (66 <= QUEEN && QUEEN <= 68))
    { IDEMPOTENT = 0; }

  if (CYCLIC) init_cgroups();
  else {
    Max_atom = n_cube;
    /*if (PREP == 1) Max_atom = P3(QGROUP-2, QGROUP-1, QGROUP-1, QGROUP-1);*/
    if (63 <= QUEEN && QUEEN <= 68) Max_atom = (n+1)*n_sqt/2;
    if (PIGEON == 2 && QUEEN <= 38) Max_atom += n_cube;
    if (PIGEON == 2 && (QUEEN == 69 || QUEEN == 79 || QUEEN == 89))
      Max_atom = 4*n_cube;
    if (PIGEON == 2 && (QUEEN == 78 || QUEEN == 88))
      Max_atom = 3*n_cube;
    if (QUEEN == 39 || QUEEN == 40) Max_atom += 9+n_cube;
  }

  if (QUEEN == 44 || QUEEN == 47) {
    if (QGROUP % 4 > 1) { printf("%d % 4 != 0, 1\n", QGROUP); exit(1); }
    Max_atom += n_cube;
  } else if (20 <= QUEEN && QUEEN <= 29 || QUEEN == 53) {
    set_double_cl(1); 
    SQUARE2 = Max_atom;
    Max_atom += SQUARE2;
    if (QUEEN == 29) Max_atom += 9;
  } else if (QUEEN == 30) {
    set_double_cl(2); 
    SQUARE2 = Max_atom;
    Max_atom *= 3;
  }
  Max_clause = Max_atom*Max_atom;
  if (QUEEN < 3) Max_clause *= n_sqt;
  if (TRACE > 7 && CYCLIC == 0) print_qg_encoding();
  else if (TRACE > 8) print_encoding();
}

void print_qg_encoding()
{
  int x, y, z;

  for (x = 0; x < n; x++)
    for (y = 0; y < n; y++) 
      for (z = 0; z < n; z++) 
	printf("TRIPLE(%d, %d, %d) = %d\n", x, y, z, TRIPLE2KEY(x, y, z));
  printf("\n");


  if (PIGEON == 2 || (QUEEN == 39) || QUEEN == 40) {
    for (x = 0; x < n; x++)
      for (y = 0; y < n; y++) 
	for (z = 0; z < n; z++) 
	  printf("OMEGA(%d, %d, %d) = %d\n", x, y, z, OMEGA(x, y, z));
    printf("\n");
  }
}

/**** The following function generates the input clauses for
  quaisgroup problems. ****/

int qgroup_clauses ()
     /* return 1 if an empty clause is found; otherwise, 0 */
{
  int cl_arr [ MAX_ATOM ], sign_arr [ MAX_ATOM ];
  int x, y, u, v, h;

  init_same_hole();
  if (RAMSEY > 0) locate_holes();

  if (qgroup_unit_clauses()) return 1;

  if (50 <= RESTRICT && RESTRICT <= 90) cyclic_cls( cl_arr, sign_arr );

  for (x = n1; x >= 0; x--) 
    for (y = n1; y >= 0; y--) if (is_same_hole(x, y) == 0)
      for (u = n1; u >= 0; u--) 
	if (is_same_hole(u, x) == 0 && is_same_hole(u, y) == 0)
	for (v = u-1; v >= 0; v--) 
	if (is_same_hole(v, x) == 0 && is_same_hole(v, y) == 0) {

	    /* x * y = u and x * y = v imply u = v. */
	    cl_arr[0] = TRIPLE2KEY(x, y, u);
	    sign_arr[cl_arr[0]] = 0;
	    cl_arr[1] = TRIPLE2KEY(x, y, v);
	    sign_arr[cl_arr[1]] = 0;
	    if (qg_insert_clause( cl_arr, sign_arr, 2) == 1)
	      return 1;

	    /* x * u = y and x * v = y imply u = v. */
	    cl_arr[0] = TRIPLE2KEY(x, u, y);
	    sign_arr[cl_arr[0]] = 0;
	    cl_arr[1] = TRIPLE2KEY(x, v, y);
	    sign_arr[cl_arr[1]] = 0;
	    if (qg_insert_clause( cl_arr, sign_arr, 2) == 1)
	      return 1;
	}

  for (x = n1; x >= 0; x--) 
    for (y = n1; y >= 0; y--) if (is_same_hole(x, y) == 0)
      for (u = n1; u >= 0; u--) 
	if (is_same_hole(u, x) == 0 && is_same_hole(u, y) == 0)
	for (v = u-1; v >= 0; v--) 
	if (is_same_hole(v, x) == 0 && is_same_hole(v, y) == 0) {
	  
	    /* u * x = y and v * x = y imply u = v. */
	    cl_arr[0] = TRIPLE2KEY(u, x, y);
	    sign_arr[cl_arr[0]] = 0;
	    cl_arr[1] = TRIPLE2KEY(v, x, y);
	    sign_arr[cl_arr[1]] = 0;
	    if (qg_insert_clause( cl_arr, sign_arr, 2) == 1)
	      return 1;
	}

       if (QUEEN == 0) { if (qg0(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 1) { if (qg1(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 2) { if (qg2(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 3) { if (qg3(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 4) { if (qg4(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 5) { if (qg5(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 6) { if (qg6(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 7) { if (qg7(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 8) { if (qg8(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 9) { if (qg9(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 10) { if (qg11(cl_arr, sign_arr)) return 1;
           if (PIGEON == 2 && rpmd_cls(cl_arr, sign_arr)) return 1;
			  if (qg12(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 11) { if (qg11(cl_arr, sign_arr)) return 1; } 
  else if (QUEEN == 12) { if (qg12(cl_arr, sign_arr)) return 1; } 
  else if (QUEEN == 13) { if (qg13(cl_arr, sign_arr)) return 1; } 
  else if (QUEEN == 14) { if (qg14(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 15) { if (qg15(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 16) { if (qg16(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 17) { if (qg0(cl_arr, sign_arr)) return 1; 
			  if (diagonal_cls(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 18) { if (qg2(cl_arr, sign_arr)) return 1; 
			  if (diagonal_cls(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 19) { if (qg1(cl_arr, sign_arr)) return 1; 
			  if (diagonal_cls321(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 20) { /* set_double_cl(0);
                          if (qg0(cl_arr, sign_arr, 1)) return 1; 
			  if (orthogonal_cls(1, cl_arr, sign_arr, 0)) return 1;
			  set_double_cl(1); */
			}
  else if (QUEEN == 21) { set_double_cl(0);
			  if (orthogonal_cls(1, cl_arr, sign_arr, 2)) return 1;
			  set_double_cl(1);
			}
  else if (QUEEN == 22) { set_double_cl(0);
                          if (qg14_resolve(cl_arr, sign_arr)) return 1;
			  if (qg14(cl_arr, sign_arr)) return 1;
			  set_double_cl(1);
			}
  else if (QUEEN == 23) { /* if (qg13(cl_arr, sign_arr)) return 1; */
                        }
  else if (QUEEN == 24) { set_double_cl(0);
			  if (symmetric_cls(SQUARE2, cl_arr, sign_arr)) return 1;
			  if (qg0(cl_arr, sign_arr)) return 1; 
			  set_double_cl(1);
			}
  else if (QUEEN == 25) { if (qg25(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 26) { if (qg26(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 28) { set_double_cl(0);
                          if (symmetric_cls(0, cl_arr, sign_arr)) return 1; 
                          if (symmetric_cls(SQUARE2, cl_arr, sign_arr)) return 1;
			  if (PIGEON != 2) { printf("-P2 is not set\n");
			  exit(0); }
			  if (ortho_P2_symm(cl_arr, sign_arr)) return 1;
			  set_double_cl(1);
			}
  else if (QUEEN == 29) { set_double_cl(0);
			  if (orthogonal_cls_3(1, 0, cl_arr, sign_arr)) return 1;
			  for (u = 0; u < n; u++)
			    for (x = 0; x < n; x++)
			      for (y = 0; y < n; y++) {
				if (insert_cl_2(SQUARE2+TRIPLE2KEY(x, y, u),
						TRIPLE2KEY(y, x, u),
						TT, cl_arr, sign_arr))
				  return 1;
			      }
			  if (only_3_non_orth(3, cl_arr, sign_arr)) return 1;
			  set_double_cl(1);
			}
  /*else if (QUEEN == 30) { if (qg30(4, cl_arr, sign_arr)) return 1; }*/
  else if (QUEEN == 31) { if (qg13(cl_arr, sign_arr)) return 1;
			  if (qg0(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 32) { if (qg13(cl_arr, sign_arr)) return 1;
			  if (qg1(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 33) { if (qg3(cl_arr, sign_arr)) return 1; 
			  if (diagonal_cls(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 34) { set_double_cl(0);
                          if (qg14_resolve(cl_arr, sign_arr)) return 1;
			  if (qg3(cl_arr, sign_arr)) return 1;
			  if (qg14(cl_arr, sign_arr)) return 1;
			  set_double_cl(1);
			}
  else if (QUEEN == 35) { if (qg30(5, cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 36) { if (qg30(1, cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 37) { if (qg37(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 38) { if (qg38(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 39) { if (qg39(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 40) { if (qg40(cl_arr, sign_arr)) return 1; }
       /*
  else if (QUEEN == 39) { if (qg3(cl_arr, sign_arr)) return 1; 
			  if (qg12(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 40) { if (LINE < 5000) {
                            printf("An input square is needed by -l5xxx\n");
			    exit(1);
                          }
                          if (ortho_Lsquare2(0, cl_arr, sign_arr)) return 1; 
                          transpose_Lsquare2(0);
                          if (ortho_Lsquare2(0, cl_arr, sign_arr)) return 1; }
       */
  else if (QUEEN == 41) { if (LINE < 5000) {
                            printf("An input square is needed by -l5xxx\n");
			    exit(1);
                          }
                          if (ortho_Lsquare2(0, cl_arr, sign_arr)) return 1; 
                          transpose_Lsquare2(1);
                          if (ortho_Lsquare2(0, cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 42) { if (LINE < 6000) {
                            printf("Two input squares needed by -l6xxx\n");
			    exit(1);
                          }
                          /* read two squares and find one
			     which is orthogonal to both */
                          if (ortho_Lsquare2(0, cl_arr, sign_arr)) return 1; 
			  qg_read_square();
                          if (ortho_Lsquare2(0, cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 43) { if (LINE < 5000) {
                            printf("An input square is needed by -l5xxx\n");
			    exit(1);
                          }
  /* read one square and find all squares which orthogonal to the first */
                          if (ortho_Lsquare2(0, cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 44) { if (qg44(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 47) { if (qg47(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 48) { if (qg4(cl_arr, sign_arr)) return 1; 
			  if (diagonal_cls(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 49) { if (qg4(cl_arr, sign_arr)) return 1; 
			  if (qg12(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 50) { if (qg50(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 51) { if (qg51(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 52) { if (qg52(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 53) { set_double_cl(0);
                          if (qg52(cl_arr, sign_arr)) return 1; 
			  if (qg53(cl_arr, sign_arr)) return 1;
			  set_double_cl(1); 
			}
  else if (QUEEN == 60) { if (qg60(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 61) { if (qg0(cl_arr, sign_arr)) return 1; 
			  if (symm_trasversal(cl_arr, sign_arr)) return 1; } 
  else if (QUEEN == 63) { if (qg13(cl_arr, sign_arr)) return 1; 
			  if (qg63(cl_arr, sign_arr)) return 1; } 
  else if (QUEEN == 64) { if (qg13(cl_arr, sign_arr)) return 1; 
			  if (qg63(cl_arr, sign_arr)) return 1; 
			  if (qg64(cl_arr, sign_arr)) return 1; } 
  else if (QUEEN == 65) { if (qg13(cl_arr, sign_arr)) return 1; 
			  if (qg00(cl_arr, sign_arr, 1)) return 1; } 
  else if (QUEEN == 66) { if (qg66(cl_arr, sign_arr)) return 1; 
			  if (qg13(cl_arr, sign_arr)) return 1; 
			  if (qg63(cl_arr, sign_arr)) return 1; } 
  else if (QUEEN == 67) { if (qg67(cl_arr, sign_arr)) return 1; 
			  if (qg13(cl_arr, sign_arr)) return 1; 
			  if (qg63(cl_arr, sign_arr)) return 1; } 
  else if (QUEEN == 68) { if (qg68(cl_arr, sign_arr)) return 1; 
			  if (qg13(cl_arr, sign_arr)) return 1; } 
  else if (QUEEN == 69) { if (qg69(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 78) { if (qg78(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 79) { if (qg79(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 88) { if (qg88(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 89) { if (qg89(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 71) { if (qg71(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 81) { if (qg81(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 82) { if (qg0(cl_arr, sign_arr)) return 1;
			  if (qg12(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 83) { if (symmetric_cls(0, cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 84) { if (symmetric_cls(0, cl_arr, sign_arr)) return 1;
			  if (ortho_Lsquare2(0, cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 90) { if (qg00(cl_arr, sign_arr, 1)) return 1; }
  else if (QUEEN == 93) { if (qg00(cl_arr, sign_arr, 1)) return 1; 
			  if (qg13(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 98) { if (qg9(cl_arr, sign_arr)) return 1;
			  if (diagonal_cls(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 99) { if (qg9(cl_arr, sign_arr)) return 1;
			  if (diagonal_cls321(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 100) { gen_abg_table();
                           if (qg100(cl_arr, sign_arr)) return 1; 
                           if (qg0(cl_arr, sign_arr)) return 1; }
  else if (QUEEN == 101) { if (qg101(cl_arr, sign_arr)) return 1; } 
  else if (QUEEN == 102) { if (qg102(cl_arr, sign_arr)) return 1; } 
  else if (QUEEN == 104) { if (qg104(cl_arr, sign_arr)) return 1; } 
  else if (QUEEN == 105) { if (qg00(cl_arr, sign_arr, 1)) return 1; 
			   transpose_square2();
			   if (qg00(cl_arr, sign_arr, 0)) return 1; }
  else if (QUEEN == 106) { if (qg00(cl_arr, sign_arr, 1)) return 1; 
			   conjugate321_square();
			   if (qg00(cl_arr, sign_arr, 0)) return 1; }
  else if (QUEEN > 110) { if (co_cycle_cls(cl_arr, sign_arr)) return 1; }

  if (QUEEN != 22 && QUEEN != 29 && QUEEN != 34 && multi_squares() == 1) { 
    set_double_cl(0); 
    if (orthogonal_cls(1, cl_arr, sign_arr, 0)) return 1; 
    set_double_cl(1);
  } else if (multi_squares() == 2) {
    set_double_cl(0); 
    if (orthogonal_cls(3, cl_arr, sign_arr, 0)) return 1; 
    set_double_cl(2);
  }

  /*  * is closed.
  (i*j=1) v ... v (i*j=n)     (1<=i,j<=n)  value of product
  (i*1=j) v ... v (i*n=j)     (1<=i,j<=n)  right solution
  (1*i=j) v ... v (n*i=j)     (1<=i,j<=n)  left solution
  */
  for (x = n1; x >= 0; x--) 
    for (y = n1; y >= 0; y--) if (is_same_hole(x, y) == 0) {

      if (QUEEN != 37 && QUEEN != 38) {
	h = 0;
	for (u = n1; u >= 0; u--) 
	  if (is_same_hole(u, x) == 0 && is_same_hole(u, y) == 0) {
	    cl_arr[h] = TRIPLE2KEY(u, x, y);
	    sign_arr[cl_arr[h++]] = 1;
	  }
	if (qg_insert_clause( cl_arr, sign_arr, h) == 1) return 1;
      }

      if (x <= n1) {
	h = 0;
	for (u = n1; u >= 0; u--) 
	  if (is_same_hole(u, x) == 0 && is_same_hole(u, y) == 0) {
	    cl_arr[h] = TRIPLE2KEY(x, u, y);
	    sign_arr[cl_arr[h++]] = 1;
	  }
	if (qg_insert_clause( cl_arr, sign_arr, h) == 1) return 1;
      }

      if (x <= n1) {
	h = 0;
	for (u = n1; u >= 0; u--) 
	  if (is_same_hole(u, x) == 0 && is_same_hole(u, y) == 0) {
	    cl_arr[h] = TRIPLE2KEY(x, y, u);
	    sign_arr[cl_arr[h++]] = 1;
	  }
	if (qg_insert_clause( cl_arr, sign_arr, h) == 1) return 1;
      }
    }

  return 0;
}

double_holes ()
{
  int i, j, x, y, z=get_addk();

  RESTRICT = 99;
  for (x = 0; x+z <= m; x+=z) 
    for (i = 0; i < QGROUP; i++) if (i < x || i >= (x+z))
      for (j = x; j < (x+z); j++) 
	for (y = x; y < (x+z); y++) {
	  /* printf("x=%d (%d %d %d) = %d\n", x, i, j, y, TRIPLE2KEY(i,j,y));*/
	  if (insert_cl_1(TRIPLE2KEY(i, j, y), FF)) return 1;
	  if (insert_cl_1(TRIPLE2KEY(j, i, y), FF)) return 1;
	}
  return 0;
}


void locate_holes () 
{
  int i, v, u, x;
  int low_right_hole = 1;

  if (RAMSEY >= QGROUP) {
    if (RAMSEY > 2000) {
      low_right_hole = RAMSEY/1000;
      RAMSEY = RAMSEY % 1000;
    }
    NHOLE = RAMSEY / 10;
    RAMSEY = RAMSEY % 10;
  } else
    NHOLE = (n-INCOMPLETE) / RAMSEY;

  limit_of_hole = RAMSEY * NHOLE;

  if ((n-limit_of_hole) % low_right_hole) {
    printf("IMPOSSIBLE: You try to search for (%d^%d, %d^?)\n",
	   RAMSEY, NHOLE, low_right_hole);
    exit(1);
  }

  for (i = 0; i < NHOLE; i++) 
    for (u = i; u < limit_of_hole; u += NHOLE)
      for (v = i; v < limit_of_hole; v += NHOLE) {
	set_same_hole(u, v);
      }
 
  if (low_right_hole > 1) {
    int nhole = (n-limit_of_hole)/low_right_hole;
    for (i = 0; i < nhole; i++) 
      for (u = i+limit_of_hole; u < n; u += nhole)
	for (v = i+limit_of_hole; v < n; v += nhole) {
	  printf("same hole: (%d, %d)\n", u, v);
	  set_same_hole(u, v);
	}
  } else if (IDEMPOTENT) 
    for (i = limit_of_hole; i < m; i++) {
      set_same_hole(i, i);
    }

  for (u = 0; u < n; u++)
    for (v = 0; v < n; v++) if (is_same_hole(u, v))
      for (x = 0; x < n; x++)
	if (is_same_hole(u, x)) {
	  if (u == v && u == x)
	    insert_cl_1(TRIPLE2KEY(u, v, x), TT);
	} else {
	  insert_cl_1(TRIPLE2KEY(u, v, x), FF);
	  insert_cl_1(TRIPLE2KEY(u, x, v), FF);
	  insert_cl_1(TRIPLE2KEY(x, u, v), FF);
	}
}

qgroup_unit_clauses ()
{
  int i, x, y;
 
  if (LINE >= 3000) qg_read_square();
  if (LINE < 4000 && LINE >= 2000) qg_read_square_mod2();

  /* Removing symmetries */
  if (RESTRICT > 1000) {
    int element[20], party[20];
    int min = 1, num=0, last=1;
    int current=0;

    /* initiation */
    if (IDEMPOTENT) min = 2;
    for (i = min-1; i < n; i++) if (!(is_same_hole(0, i))) element[num++] = i;
    party[0] = num;
    while (party[0] >= (min<<1)) {
      party[last++] = min;
      party[0] -= min;
    }
    
    /* main loop */
    for (i = 1001; i < RESTRICT; i++) {
      
      if (TRACE > 1) {
	for (y = 0; y < last; y++) printf( " %d", party[y]);
	printf(" <- partition %d\n", i-1000);
      }

      while (current && party[current-1] <= party[current]+1) --current;
      if (current == 0) {
	if (last > 1) { 
	  party[0] += party[--last]; 
	  if (last > 1) current = 1; 
	  for (x = 1; x < last; x++) {
	    party[0] += party[x]-min; party[x] = min;
	  }
	} else { printf("no partition available\n"); exit(0); }
      } else {
	party[current]++; party[current-1]--;
	if (current < last-1) current++;
      }
    }

    if (TRACE > 1) {
      for (y = 0; y < last; y++) printf( " %d", party[y]);
      printf(" <- partition %d\n", i-1000);
    }

    /* output unit clauses */
    current = 0;
    for (i = 0; i < last; i++) {
      for (x = party[i]-1; x>0; x--) {
	if (TRACE > 1)
	  printf("0 * %d = %d\n", element[x+current-1], element[x+current]); 
	insert_cl_1(TRIPLE2KEY(0, element[x+current-1], element[x+current]), TT);
      }
      if (TRACE > 1)
	printf("0 * %d = %d\n", element[party[i]+current-1], element[current]); 
      insert_cl_1(TRIPLE2KEY(0, element[party[i]+current-1], element[current]), TT); 
      current += party[i];
    }
  }

  if (IDEMPOTENT) { /* x * x = x; */
    if ((QUEEN != 84 && QUEEN != 83) || QGROUP % 2) {
      if (OUTPUT < 2) {
	if (NHOLE > 1) 
	  printf("Looking for HQG%d(%d^%d, %d^1)\n",
		 QUEEN, RAMSEY, NHOLE, INCOMPLETE);
	else if (INCOMPLETE)
	  printf("Looking for idempotent IQG%d(%d, %d)\n",
		 QUEEN, m, INCOMPLETE);
	else
	  printf("Looking for idempotent QG%d(%d)\n", QUEEN, m);
      }

      for (x = 0; x < m; x++) {
	if (insert_cl_1(i = TRIPLE2KEY(x, x, x), TT)) return 1;
	if ((QUEEN != 24 || (QGROUP % 2)) && double_cl) {
	  if (insert_cl_1(i+SQUARE2, TT)) return 1;
	  if (double_cl > 1 && insert_cl_1(i+SQUARE2+SQUARE2, TT)) return 1;
	}
      }
    } 
    /*
  } else if (QUEEN == 39) {
    if (qg39_unit_cls()) return 1;
    */
  }
  
  if (get_addk() > 2 && double_holes()) return 1;

  if (RESTRICT <= 10 || (100 <= RESTRICT && RESTRICT < 1000)) {
    int step = 1;
    int x0 = 0;

    if (RESTRICT >= 300) { step = 2; RESTRICT -= 200; }
    else if (RAMSEY > 1) step = 2;
    else if (RESTRICT > 1 && RESTRICT < 10) step = RESTRICT;

    if (RESTRICT < 10) {
      /* choose the best for each problem */
      if (RAMSEY > 1) RESTRICT = 100;
      else if (QUEEN == 2 || QUEEN == 6 || QUEEN == 7) RESTRICT = 102;
      else if (QUEEN == 3 || QUEEN == 4) RESTRICT = 105;
      else if (QUEEN != 100) RESTRICT = 103;
    } 

    if (QUEEN == 50 || QUEEN == 51) { x0 = 1; }

    /* additional clauses, i.e., a good heuristic.
       FC1: x < y-step implies x * 1 != y.  RESTRICT=100
       FC2: x < y-step implies y * 1 != x.  RESTRICT=200
       FR1: x < y-step implies 1 * x != y.  RESTRICT=101
       FR2: x < y-step implies 1 * y != x.  RESTRICT=201
       FV1: x < y-step implies x * y != 1.  RESTRICT=102
       FV2: x < y-step implies y * x != 1.  RESTRICT=202
       LC1: x < y-step implies x * n != y.  RESTRICT=103
       LC2: x < y-step implies y * n != x.  RESTRICT=203 -- by McCune
       LR1: x < y-step implies n * x != y.  RESTRICT=104
       LR2: x < y-step implies n * y != x.  RESTRICT=204
       LV1: x < y-step implies x * y != n.  RESTRICT=105
       LV2: x < y-step implies y * x != n.  RESTRICT=205
       */
    if (RESTRICT > 0)
    for (y = 2; y < m; y++) if (is_same_hole(n1, y) == 0)
      for (x = x0; x < y-step; x++) 
	if (is_same_hole(x, y) == 0 && is_same_hole(n1, x) == 0 &&
	    is_same_hole(x, 0) == 0 && is_same_hole(y, 0) == 0) {
	  if (RESTRICT == 100) i = TRIPLE2KEY(x, 0, y);
	  else if (RESTRICT == 200) i = TRIPLE2KEY(y, 0, x);
	  else if (RESTRICT == 101) i = TRIPLE2KEY(0, x, y);
	  else if (RESTRICT == 201) i = TRIPLE2KEY(0, y, x);
	  else if (RESTRICT == 102) i = TRIPLE2KEY(x, y, 0);
	  else if (RESTRICT == 202) i = TRIPLE2KEY(y, x, 0);
	  else if (RESTRICT == 103) i = TRIPLE2KEY(x, n1, y);
	  else if (RESTRICT == 203) i = TRIPLE2KEY(y, n1, x);
	  else if (RESTRICT == 104) i = TRIPLE2KEY(n1, x, y);
	  else if (RESTRICT == 204) i = TRIPLE2KEY(n1, y, x);
	  else if (RESTRICT == 105) i = TRIPLE2KEY(x, y, n1);
	  else if (RESTRICT == 205) i = TRIPLE2KEY(y, x, n1);
	  else i = 2;
	  
	  if (insert_cl_1(i, FF)) return 1;
	}
    
    if (IDEMPOTENT && RESTRICT == 10) {
      for (x = m/2; x < m-2; x++) 
	if (insert_cl_1(TRIPLE2KEY(x, n1, x+1), TT)) return 1;
    }
  }
  
  return 0;
}

qg0 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* x * y = u, z * w = u, y * x = v, w * z = v -> x = z, y = w */
{
  int x, y, z, u, v, w;
  
  if (PIGEON == 2) return (qg0_P2(cl_arr, sign_arr));
  
  for (x = n1; x > 0; x--)
    for (y = (x >= m)? m-1 : n1; y >= 0; y--) 
      if (x != y && is_same_hole(x, y) == 0) {

	for (z = n1; z >= 0; z--) 
	  if (z != x && z != y &&
	      insert_cl_all_3(TRIPLE2KEY(y, y, y),
			      TRIPLE2KEY(x, z, y), 
			      TRIPLE2KEY(z, x, y), 
			      0, cl_arr, sign_arr))
	    return 1;
      
	for (z = x-1; z >= 0; z--)
	  for (w = (z >= m)? m-1 : n1; w >= 0; w--) if (z != w) 
	    for (u = (x < m && y < m && z < m && w < m)? n1 : m-1;
		 u >= 0; u--)
	      for (v = (x < m && y < m && z < m && w < m)? n1 : m-1;
		   v >= 0; v--) 
		if (insert_cl_4(TRIPLE2KEY(x, y, u),
				TRIPLE2KEY(z, w, u), 
				TRIPLE2KEY(y, x, v), 
				TRIPLE2KEY(w, z, v), 
				0, cl_arr, sign_arr))
		  return 1;
      }
  
  return 0;
}

qg0_P2 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* x * y = u, z * w = u, y * x = v, w * z = v -> x = z, y = w */
{
  int x, y, z, w;
  
  if (omega_cls(cl_arr, sign_arr)) return 1;

  for (x = n1; x >= 0; x--)
    for (y = n1; y >= 0; y--) if (is_same_hole(x, y) == 0)
      for (z = n1; z >= 0; z--) 
	for (w = n1; w >= 0; w--) {

	  if (is_same_hole(z, w) == 0) {
	    if (insert_cl_all_3(TRIPLE2KEY(x, y, w),
				TRIPLE2KEY(y, x, z), 
				OMEGA(x, w, z), 
				1, cl_arr, sign_arr))
	      return 1;
	  } else if (insert_cl_2(TRIPLE2KEY(x, y, w),
				 TRIPLE2KEY(y, x, z), 
				 0, cl_arr, sign_arr))
	    return 1;
	}

  return 0;
}

qg10 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* x * y = u, z * w = u, y * x = v, w * z = v -> x = z, y = w */
{
  int x, y, z, u, v, w;

  if (qg0(cl_arr, sign_arr)) return 1;

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

int qg1 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* x * y = u, z * w = u, v * y = x, v * w = z -> x = z, y = w */
{
  int x, y, z, u, v, w;
 
  if (PIGEON == 2) return (qg1_P2(cl_arr, sign_arr));
  if (PREP == 1) P2_vs_P3(cl_arr, sign_arr);

  for (x = n1; x >= 0; x--)
    for (y = (x >= m)? m-1 : n1; y >= 0; y--) if (x != y) {

      for (z = (x < m && y < m)? n1 : m-1; z >= 0; z--) 
	if (is_same_hole(x,z) == 0 && is_same_hole(y,z) == 0) {
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
	}

      if (is_same_hole(x, y) == 0) 
	for (z = x-1; z >= 0; z--) 
	  for (w = (z >= m)? m-1 : n1; w >= 0; w--) 
	    if (is_same_hole(z, w) == 0) 
	    for (u = (x < m && y < m && z < m && w < m)? n1 : m-1;
		 u >= 0; u--) if (is_same_hole(x, u) == 0 &&
				  is_same_hole(y, u) == 0) 
	      for (v = (x < m && y < m && z < m && w < m)? n1 : m-1;
		   v >= 0; v--) if (is_same_hole(x, v) == 0 &&
				  is_same_hole(y, v) == 0) 
		if (insert_cl_4(TRIPLE2KEY(x, y, u),
				TRIPLE2KEY(z, w, u),
				TRIPLE2KEY(v, y, x), 
				TRIPLE2KEY(v, w, z), 
				0, cl_arr, sign_arr))
		  return 1;
    }
  return 0;
}

qg1_P2 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* x * y = u, z * w = u, v * y = x, v * w = z -> x = z, y = w */
{
  int x, y, z, w;

  if (omega_cls(cl_arr, sign_arr)) return 1;

  for (x = n1; x >= 0; x--)
    for (y = n1; y >= 0; y--) if (is_same_hole(x, y) == 0)
      for (z = n1; z >= 0; z--) 
	for (w = n1; w >= 0; w--) {

	  if (is_same_hole(z, w) == 0) {
	    if (insert_cl_all_3(TRIPLE2KEY(x, y, w),
				TRIPLE2KEY(z, y, x), 
				OMEGA(x, w, z), 
				1, cl_arr, sign_arr))
	    return 1;
	  } else if (insert_cl_2(TRIPLE2KEY(x, y, w),
				 TRIPLE2KEY(z, y, x), 
				 0, cl_arr, sign_arr))
	    return 1;
	}

  return 0;
}

int qg2 (cl_arr, sign_arr)
     int cl_arr [], sign_arr []; 
     /* Looking for (231)-COLS:
        x * y = u, z * w = u, y * v = x, w * v = z -> x = z, y = w */
     /* If looking for (312)-COLS, use:
	x * y = u, z * w = u, v * x = y, v * z = w -> x = z, y = w */
{
  int x, y, z, u, v, w;

  if (PIGEON == 2) return (qg2_P2(cl_arr, sign_arr));

  for (x = n1; x >= 0; x--)
    for (y = (x >= m)? m-1 : n1; y >= 0; y--) if (is_same_hole(x,y) == 0) {
      for (z = (x < m && y < m)? n1 : m-1; z >= 0; z--) 
	if (is_same_hole(x,z) == 0 && is_same_hole(y,z) == 0 &&
	    insert_cl_all_3(TRIPLE2KEY(y, y, y),
			    TRIPLE2KEY(x, z, y), 
			    TRIPLE2KEY(z, y, x), 
			    0, cl_arr, sign_arr))
	  return 1;

      for (z = x-1; z >= 0; z--) 
	for (w = (z >= m)? m-1 : n1; w >= 0; w--) if (y != w && z != w) 
	  for (u = (x < m && y < m && z < m && w < m)? n1 : m-1;
	       u >= 0; u--)
	    for (v = (x < m && y < m && z < m && w < m)? n1 : m-1;
		 v >= 0; v--)
	      if (insert_cl_4(TRIPLE2KEY(x, y, u),
			      TRIPLE2KEY(z, w, u),
			      TRIPLE2KEY(y, v, x),
			      TRIPLE2KEY(w, v, z),
			      0, cl_arr, sign_arr))
		return 1;
      }
  return 0;
}

qg2_P2 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* (231) x * y = u, z * w = u, y * v = x, w * v = z -> x = z, y = w */
     /* (312) x * y = u, z * w = u, v * x = y, v * z = w -> x = z, y = w */
{
  int x, y, z, w;

  if (omega_cls(cl_arr, sign_arr)) return 1;

  for (x = n1; x >= 0; x--)
    for (y = n1; y >= 0; y--) if (is_same_hole(x, y) == 0)
      for (z = n1; z >= 0; z--) 
	for (w = n1; w >= 0; w--) {

	  if (is_same_hole(z, w) == 0) {
	    if (insert_cl_all_3(TRIPLE2KEY(x, y, w),
				TRIPLE2KEY(y, z, x), 
				OMEGA(x, w, z), 
				1, cl_arr, sign_arr))
	      return 1;
	  } else if (insert_cl_2(TRIPLE2KEY(x, y, w),
				 TRIPLE2KEY(y, z, x), 
				 0, cl_arr, sign_arr))
	    return 1;
	}

  return 0;
}

int qg3 (cl_arr, sign_arr)
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

int qg4 (cl_arr, sign_arr)
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

int qg5 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* ((y * x) * y) * y = x, plus its two variants */
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

int qg6 (cl_arr, sign_arr)
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

int qg7 (cl_arr, sign_arr)
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

int qg71 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* ((x * y) * x) * y = x, and its two variants */
{
  int x, y, u, v;

  for (x = n1; x >= 0; x--) 
    for (y = (x >= m)? m-1 : n1; y >= 0; y--) 
      for (u = (x < m && y < m)? n1 : m-1; u >= 0; u--) 
	for (v = (x < m && y < m && u < m)? n1 : m-1; v >= 0; v--) 
	  /* x * y = u, u * x = v imply v * y = x */
	  if (insert_cl_all_3(TRIPLE2KEY(x, y, u), 
			      TRIPLE2KEY(u, x, v),
			      TRIPLE2KEY(v, y, x),
			      3, cl_arr, sign_arr))
	    return 1;
  return 0;
}

int qg8 (cl_arr, sign_arr)
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

int qg81 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* (x * (x * y)) * y = x and its two variants */
{
  int x, y, u, v;

  for (x = n1; x >= 0; x--) 
    for (y = (x >= m)? m-1 : n1; y >= 0; y--) 
      for (u = (x < m && y < m)? n1 : m-1; u >= 0; u--) 
	for (v = (x < m && y < m && u < m)? n1 : m-1; v >= 0; v--) 
	  /* x * y = u, x * u = v => v * y = x */
	  if (insert_cl_all_3(TRIPLE2KEY(x, y, u),
			      TRIPLE2KEY(x, u, v),
			      TRIPLE2KEY(v, y, x),
			      3, cl_arr, sign_arr))
	    return 1;
  return 0;
}

int qg9 (cl_arr, sign_arr)
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

int qg11 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* (x * y) * y = x */
{
  int x, y, z;
 
  for (x = n1; x >= 0; x--) 
    for (y = (x < m)? n1 : m-1; y >= 0; y--) 
      for (z = ((x < m && y < m)? n1 :
		((x < m || y < m)? m-1 : -1)); 
	   z >= 0; z--) {

	/* x * y = z -> z * y = x */
	if (insert_cl_2(TRIPLE2KEY(x, y, z),
			TRIPLE2KEY(z, y, x), 
			1, cl_arr, sign_arr, 1)) return 1;
      }
  return 0;
}

int qg12 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* x * (y * x) = y * (x * y) */
{
  int x, y, u, v, z;
  
  /* x * y = u, u * x = v => v * x = y */
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

int qg13 (cl_arr, sign_arr)
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

qg14 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* x * y = z, y * z = u, z * u = v => u * v = x */
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

	for (u = (v >= m || y >= m || x >= m)? m-1 : n1; u >= 0; u--) {
	  if (insert_cl_all_3(TRIPLE2KEY(x, y, u),
			      TRIPLE2KEY(y, u, v),
			      TRIPLE2KEY(u, v, x),
			      1, cl_arr, sign_arr))
	    return 1;

	  if (insert_cl_all_3(TRIPLE2KEY(x, y, u),
			      TRIPLE2KEY(y, u, v),
			      TRIPLE2KEY(v, x, y),
			      1, cl_arr, sign_arr))
	    return 1;

	  if (insert_cl_all_3(TRIPLE2KEY(x, y, u),
			      TRIPLE2KEY(u, v, x),
			      TRIPLE2KEY(y, u, v),
			      1, cl_arr, sign_arr))
	    return 1;
	}	
      }
  return 0;
}

qg15 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* x * y = z, y * z = u, z * u = v => u * v = x */
{
  int x, y, z, u, v;
 
  if (PIGEON == 2 && rpmd_cls(cl_arr, sign_arr)) return 1;

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
	       v >= 0; v--) {

	    if (insert_cl_4(TRIPLE2KEY(x, y, z),
			    TRIPLE2KEY(y, z, u),
			    TRIPLE2KEY(z, u, v),
			    TRIPLE2KEY(u, v, x),
			    1, cl_arr, sign_arr))
	      return 1;

	    if (insert_cl_4(TRIPLE2KEY(x, y, z),
			    TRIPLE2KEY(z, u, v),
			    TRIPLE2KEY(u, v, x),
			    TRIPLE2KEY(y, z, u),
			    1, cl_arr, sign_arr))
	      return 1;

	    if (insert_cl_4(TRIPLE2KEY(x, y, z),
			    TRIPLE2KEY(y, z, u),
			    TRIPLE2KEY(u, v, x),
			    TRIPLE2KEY(z, u, v),
			    1, cl_arr, sign_arr))
	      return 1;

	    if (insert_cl_4(TRIPLE2KEY(x, y, z),
			    TRIPLE2KEY(y, z, u),
			    TRIPLE2KEY(z, u, v),
			    TRIPLE2KEY(v, x, y),
			    1, cl_arr, sign_arr))
	      return 1;
	  }
      }
  return 0;
}

qg16 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* x * y = z, y * z = u, z * u = v, u * v = w => v * w = x */
{
  int x, y, z, u, v, w;
 
  for (x = n1; x >= 0; x--) 
    for (y = (x >= m)? m-1 : n1; y >= 0; y--) 
      for (z = (x >= m || y >= m)? m-1 : n1; z >= 0; z--) {

	if (x >= m) {
	  /* x * z = y => z * y != u for x >= m and u >= m */
	  for (u = n1; u >= m; u--) {
	    if (insert_cl_2(TRIPLE2KEY(x, z, y),
			    TRIPLE2KEY(z, y, u),
			    0, cl_arr, sign_arr))
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

	if (x != y || x != z || y != z) 
	for (u = (z >= m || y >= m || x >= m)? m-1 : n1; u >= 0; u--) {

	  if (insert_cl_all_3(TRIPLE2KEY(x, y, z),
			      TRIPLE2KEY(y, z, u),
			      TRIPLE2KEY(z, u, x),
			      0, cl_arr, sign_arr))
	    return 1;

	  for (v = (z >= m || u >= m || y >= m || x >= m)? m-1 : n1;
	       v >= 0; v--) {

	    for (w = (z >= m || u >= m || y >= m || x >= m || v >= m)? m-1 : n1;
		 w >= 0; w--) {

	      if (insert_cl_5(TRIPLE2KEY(x, y, z),
			      TRIPLE2KEY(y, z, u),
			      TRIPLE2KEY(z, u, v),
			      TRIPLE2KEY(u, v, w),
			      TRIPLE2KEY(v, w, x),
			      1, cl_arr, sign_arr))
		return 1;

	      if (insert_cl_5(TRIPLE2KEY(x, y, z),
			      TRIPLE2KEY(y, z, u),
			      TRIPLE2KEY(u, v, w),
			      TRIPLE2KEY(v, w, x),
			      TRIPLE2KEY(z, u, v),
			      1, cl_arr, sign_arr))
		return 1;

	    }
	  }
	}
      }
  return 0;
}

qg17 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* (yx)x = y */
     /* (xy)(y(xy)) = x * y */
     /* x * y = y * x */
{
  int x, y, z, u;
 
  for (x = n1; x >= 0; x--) 
    for (y = (x >= m)? m-1 : n1; y >= 0; y--) 
      for (z = (x >= m || y >= m)? m-1 : n1; z >= 0; z--) {

	if (insert_cl_2(TRIPLE2KEY(y, x, z),
			TRIPLE2KEY(z, x, y),
			1, cl_arr, sign_arr))
	  return 1;
	
	/* x * z = y, z * y = u => y * u != x for x >= m */
	for (u = m-1; u >= 0; u--) {
	    if (insert_cl_all_3(TRIPLE2KEY(x, z, y),
				TRIPLE2KEY(z, y, u),
				TRIPLE2KEY(y, u, x),
				0, cl_arr, sign_arr))
	      return 1;
	  }
      }

  return 0;
}

qg14_resolve (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* x * y = z, x + y = u => y + z = u */
{
  int x, y, z, u;

  /* initial parallel classes */
  for (x = n1; x >= 0; x--) {
    insert_cl_1(SQUARE2+TRIPLE2KEY(0, x, x), TT);
    insert_cl_1(SQUARE2+TRIPLE2KEY(x, x, 0), TT);
    insert_cl_1(TRIPLE2KEY(x, x, x), TT);
  }

  /* 3P Property: No three common elments in two blocks. */
  for (x = n1; x >= 0; x--) 
    for (y = n1; y >= 0; y--) if (x != y && is_same_hole(x, y) == 0)
      for (z = n1; z >= 0; z--) 
	if (is_same_hole(x, z) == 0 && is_same_hole(y, z) == 0) {
	  if (insert_cl_2(TRIPLE2KEY(x, y, z),
			  TRIPLE2KEY(x, z, y),
			  FF, cl_arr, sign_arr)) return 1;
	  if (insert_cl_2(TRIPLE2KEY(x, y, z),
			  TRIPLE2KEY(y, x, z),
			  FF, cl_arr, sign_arr)) return 1;
	}

  /* subsequent parallel classes */
  for (x = n1; x >= 0; x--) 
    for (y = n1; y >= 0; y--) if (is_same_hole(x, y) == 0)
      for (z = n1; z >= 0; z--) 
	if (is_same_hole(x, z) == 0 && is_same_hole(y, z) == 0)
	  for (u = n1; u >= 0; u--) 
	    if (insert_cl_all_3(TRIPLE2KEY(x, y, z),
				SQUARE2+TRIPLE2KEY(x, y, u),
				SQUARE2+TRIPLE2KEY(y, z, u),
				1, cl_arr, sign_arr))
	      return 1;

  return 0;
}

qg25 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* x * y = z, y * z = u, z * u = v => u * v = x */
{
  int x, y, z, u;

  if (phi_clauses_miss(cl_arr, sign_arr)) return 1;

  for (x = n1; x >= 0; x--) 
    for (y = (x >= m)? m-1 : n1; y >= 0; y--) if (is_same_hole(x, y) == 0)
      for (z = (x >= m || y >= m)? m-1 : n1; z >= 0; z--) 
	if (is_same_hole(x, z) == 0 &&  is_same_hole(y, z) == 0)
	for (u = (x >= m || y >= m)? m-1 : n1; u >= 0; u--) 
	  if (is_same_hole(u, z) == 0 &&  is_same_hole(u, y) == 0)
	  if (insert_cl_all_3(TRIPLE2KEY(x, y, z),
			      TRIPLE2KEY(y, z, u),
			      PHI(z, u, x),
			      1, cl_arr, sign_arr))
	    return 1;
  return 0;
}

qg26 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* x * y = z, y * z = u, z * u = v, u * v = w => v * w = x */
{
  int x, y, z, u, v;
 
  if (phi_clauses_miss(cl_arr, sign_arr)) return 1;

  for (x = n1; x >= 0; x--) 
    for (y = (x >= m)? m-1 : n1; y >= 0; y--) 
      for (z = (x >= m || y >= m)? m-1 : n1; z >= 0; z--) {
	if (x != z && insert_cl_2(PHI(x, y, z),
				  PHI(z, y, x),
				  0, cl_arr, sign_arr))
	  return 1;
      }

  for (x = n1; x >= 0; x--) 
    for (y = (x >= m)? m-1 : n1; y >= 0; y--) 
      for (z = (x >= m || y >= m)? m-1 : n1; z >= 0; z--) 
	for (u = (x >= m || y >= m)? m-1 : n1; u >= 0; u--) 
	  for (v = (x >= m || y >= m || z >= m || u >= m)? m-1 : n1; 
	       v >= 0; v--) 
	    if (insert_cl_4(
			    TRIPLE2KEY(x, y, z),
			    TRIPLE2KEY(y, z, u),
			    TRIPLE2KEY(z, u, v),
			    PHI(u, v, x),
			    1, cl_arr, sign_arr))
	      return 1;
  return 0;
}

qg37 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* Round Robin Tournament Scheduling */
{
  int x, y, z, u, v, w;
  int n2 = m/2;

  if (m % 2) {
    printf("Warning: the group size %d must be even\n", m);
    exit(0);
  }

  if (PIGEON == 2) return (qg37_P2(cl_arr, sign_arr));

  for (x = n-2; x > 0; x--) 
    for (u = n2-1; u >= 0; u--) 
      for (z = 0; z < n; z++)
	for (w = 0; w < n; w++) {
	
	  for (v = n2-1; v >= 0; v--) 
	    for (y = x-1; y >= 0; y--) {
	      if (insert_cl_4(TRIPLE2KEY(x, u, z),
			      TRIPLE2KEY(x, u+n2, w),
			      TRIPLE2KEY(y, v, w),
			      TRIPLE2KEY(y, v+n2, z),
			      0, cl_arr, sign_arr))
		return 1;

	      if (insert_cl_4(TRIPLE2KEY(x, u, z),
			      TRIPLE2KEY(x, u+n2, w),
			      TRIPLE2KEY(y, v, z),
			      TRIPLE2KEY(y, v+n2, w),
			      0, cl_arr, sign_arr))
		return 1;
	    }

	  for (y = n-2; y >= 0; y--) 
	    for (v = n-2; v >= m; v-=2) {
	      if (insert_cl_4(TRIPLE2KEY(x, u, z),
			      TRIPLE2KEY(x, u+n2, w),
			      TRIPLE2KEY(y, v, w),
			      TRIPLE2KEY(y, v+1, z),
			      0, cl_arr, sign_arr))
		return 1;

	      if (insert_cl_4(TRIPLE2KEY(x, u, z),
			      TRIPLE2KEY(x, u+n2, w),
			      TRIPLE2KEY(y, v, z),
			      TRIPLE2KEY(y, v+1, w),
			      0, cl_arr, sign_arr))
		return 1;
	    }
	}

  return 0;
}

qg37_P2 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
{
  int x, u, z, w, y, v;
  int n2 = m/2;

  for (z = 0; z < n; z++)
    for (w = z; w < n; w++) {

      for (x = n-2; x >= 0; x--) 
	for (u = n2-1; u >= 0; u--) {
	    if (insert_cl_all_3(TRIPLE2KEY(x, u, z),
				TRIPLE2KEY(x, u+n2, w), 
				OMEGA(x, z, w), 
				1, cl_arr, sign_arr))
	      return 1;
	    if (insert_cl_all_3(TRIPLE2KEY(x, u, w),
				TRIPLE2KEY(x, u+n2, z), 
				OMEGA(x, z, w), 
				1, cl_arr, sign_arr))
	      return 1;
	  }

      for (y = 0; y < m; y++) 
	for (v = n-2; v >= m; v-=2) {
	  if (insert_cl_all_3(TRIPLE2KEY(y, v, w),
			      TRIPLE2KEY(y, v+1, z),
			      OMEGA(y, z, w), 
			      1, cl_arr, sign_arr))
	    return 1;
	  if (insert_cl_all_3(TRIPLE2KEY(y, v, z),
			      TRIPLE2KEY(y, v+1, w),
			      OMEGA(y, z, w), 
			      1, cl_arr, sign_arr))
	    return 1;
	}
    }

  if (omega_cls(cl_arr, sign_arr)) return 1;
  return 0;
}

qg38 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* Round Robin Tournament Scheduling */
{
  int x, y, z, u, v, w;

  if (PIGEON == 2) return (qg38_P2(cl_arr, sign_arr));

  for (x = n-2; x > 0; x--) 
    for (y = x-1; y >= 0; y--) 
      for (u = n1-1; u >= 0; u-=2) 
	for (v = n1-1; v >= 0; v-=2) 
	  for (z = 0; z < n; z++)
	    for (w = 0; w < n; w++) {
	      /*
	      if (x == 4 && y == 0 && u == 0 &&
	      v == 2 && z == 7 && w == 4) bug(37); */

	      if (insert_cl_4(TRIPLE2KEY(x, u, z),
			      TRIPLE2KEY(x, u+1, w),
			      TRIPLE2KEY(y, v, w),
			      TRIPLE2KEY(y, v+1, z),
			      0, cl_arr, sign_arr))
		return 1;

	      if (insert_cl_4(TRIPLE2KEY(x, u, z),
			      TRIPLE2KEY(x, u+1, w),
			      TRIPLE2KEY(y, v, z),
			      TRIPLE2KEY(y, v+1, w),
			      0, cl_arr, sign_arr))
		return 1;
	    }

  return 0;
}

qg38_P2 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
{
  int x, u, z, w;

  for (x = n-2; x >= 0; x--) 
    for (u = n-2; u >= 0; u-=2) if (is_same_hole(x, u) == 0)
      for (z = 0; z < n; z++) 
	if (is_same_hole(x, z) == 0 && is_same_hole(u, z) == 0)
	for (w = (z>m)? m-1 : n1; w >= 0; w--) 
	  if (is_same_hole(x, w) == 0 && is_same_hole(u, w) == 0) {

	    if (z < w) {
	      if (insert_cl_all_3(TRIPLE2KEY(x, u, z),
				  TRIPLE2KEY(x, u+1, w), 
				  OMEGA(x, w, z), 
				  1, cl_arr, sign_arr))
	      return 1;
	    } else {
	      if (insert_cl_all_3(TRIPLE2KEY(x, u, w),
				  TRIPLE2KEY(x, u+1, z), 
				  OMEGA(x, w, z), 
				  1, cl_arr, sign_arr))
		return 1;
	    }
	}

  if (omega_cls(cl_arr, sign_arr)) return 1;

  return 0;
}

qg39(cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* r-sols */
{
  int x, y, z, w;
  int b = (PIGEON%100)-10;

  if (omega_cls(cl_arr, sign_arr)) return 1;

  for (x = n1; x >= 0; x--)
    for (y = n1; y >= 0; y--) if ((is_same_hole(x, y) == 0) &&
				  (x >= b || y >= b))
      for (z = n1; z >= 0; z--) 
	for (w = n1; w >= 0; w--) {

	  if (is_same_hole(z, w) == 0) {
	    if (insert_cl_all_3(TRIPLE2KEY(x, y, w),
				TRIPLE2KEY(y, x, z), 
				OMEGA(x, w, z), 
				1, cl_arr, sign_arr))
	      return 1;
	  } else if (insert_cl_2(TRIPLE2KEY(x, y, w),
				 TRIPLE2KEY(y, x, z), 
				 0, cl_arr, sign_arr))
	    return 1;
	}

  return 0;
}

qg40 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* r-sols */
{
  int x, y, z, w;
  
  for (x = 0; x < n; x++)
    for (y = 0; y < n; y++) if (is_same_hole(x, y) == 0)
      for (z = 0; z < n; z++) 
	if (is_same_hole(x, z) == 0 && is_same_hole(y, z) == 0)
	  for (w = z+1; w < n; w++) 
	    if (is_same_hole(x, w) == 0 && is_same_hole(y, w) == 0) {
	      if (x < 3 && y < 3) {
		if (insert_cl_all_3(OMEGA(w, x, y), 
				    OMEGA(z, x, y), 
				    C3(x, y), 
				    1, cl_arr, sign_arr)) return 1;
	      } else if (insert_cl_2(OMEGA(w, x, y), 
				     OMEGA(z, x, y), 
				     FF, cl_arr, sign_arr)) return 1;
	    }

  for (x = n1; x >= 0; x--)
    for (y = n1; y >= 0; y--) if (is_same_hole(x, y) == 0)
      for (z = n1; z >= 0; z--) 
	for (w = n1; w >= 0; w--) {
	  if (is_same_hole(z, w) == 0) {
	    if (insert_cl_all_3(TRIPLE2KEY(x, y, w),
				  TRIPLE2KEY(y, x, z), 
				  OMEGA(x, w, z), 
				  1, cl_arr, sign_arr))
	      return 1;
	  } else if (insert_cl_2(TRIPLE2KEY(x, y, w),
				 TRIPLE2KEY(y, x, z), 
				 0, cl_arr, sign_arr))
	    return 1;
	}

  return only_3_non_orth(3, cl_arr, sign_arr); 
}

int qg44 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* Triple Whist Tournament */
{
  int u, w, x, y, z, n2 = n/2;
  n_offset = SQUARE2;

  for (x = 0; x < n1; x++)
    for (y = 0; y < n2; y += 2)
      for (z = n1; z > 0; z--) 
	for (w = z-1; w >= 0; w--) {

	  /* (a c) or (c a) */
	  if (insert_cl_all_3(TRIPLE2KEY(x, y, w),
			      TRIPLE2KEY(x, y+n2, z), 
			      OMEGA(w, z, x),  /* w < z */
			      1, cl_arr, sign_arr))
	    return 1;
	  if (insert_cl_all_3(TRIPLE2KEY(x, y+n2, w),
			      TRIPLE2KEY(x, y, z), 
			      OMEGA(w, z, x), 	  /* w < z */
			      1, cl_arr, sign_arr))
	    return 1;

	  /* (b d) or (b d) */
	  if (insert_cl_all_3(TRIPLE2KEY(x, y+1, w),
			      TRIPLE2KEY(x, y+n2+1, z), 
			      OMEGA(w, z, x),  /* w < z */
			      1, cl_arr, sign_arr))
	    return 1;
	  if (insert_cl_all_3(TRIPLE2KEY(x, y+n2+1, w),
			      TRIPLE2KEY(x, y+1, z), 
			      OMEGA(w, z, x), 	  /* w < z */
			      1, cl_arr, sign_arr))
	    return 1;

	  /* (a b), (b a), (c d), or (d c) */
	  if (insert_cl_all_3(TRIPLE2KEY(x, y, w),
			      TRIPLE2KEY(x, y+1, z), 
			      OMEGA(z, w, x), 	  /* w < z */
			      1, cl_arr, sign_arr))
	    return 1;
	  if (insert_cl_all_3(TRIPLE2KEY(x, y+1, w),
			      TRIPLE2KEY(x, y, z), 
			      OMEGA(z, w, x),   /* w < z */
			      1, cl_arr, sign_arr))
	    return 1;
	  if (insert_cl_all_3(TRIPLE2KEY(x, y+n2, w),
			      TRIPLE2KEY(x, y+n2+1, z), 
			      OMEGA(z, w, x),   /* w < z */
			      1, cl_arr, sign_arr))
	    return 1;
	  if (insert_cl_all_3(TRIPLE2KEY(x, y+n2+1, w),
			      TRIPLE2KEY(x, y+n2, z), 
			      OMEGA(z, w, x),   /* w < z */
			      1, cl_arr, sign_arr))
	    return 1;

	  /* (a d), (d a), (b c), or (c b) */
	  if (insert_cl_all_3(TRIPLE2KEY(x, y, w),
			      TRIPLE2KEY(x, y+n2+1, z), 
			      OMEGA(z, w, x),   /* w < z */
			      1, cl_arr, sign_arr))
	    return 1;
	  if (insert_cl_all_3(TRIPLE2KEY(x, y+n2+1, w),
			      TRIPLE2KEY(x, y, z), 
			      OMEGA(z, w, x),   /* w < z */
			      1, cl_arr, sign_arr))
	    return 1;
	  if (insert_cl_all_3(TRIPLE2KEY(x, y+1, w),
			      TRIPLE2KEY(x, y+n2, z), 
			      OMEGA(z, w, x),   /* w < z */
			      1, cl_arr, sign_arr))
	    return 1;
	  if (insert_cl_all_3(TRIPLE2KEY(x, y+n2, w),
			      TRIPLE2KEY(x, y+1, z), 
			      OMEGA(z, w, x),   /* w < z */
			      1, cl_arr, sign_arr))
	    return 1;
	}

  for (w = 0; w < n; w++) 
    for (z = w+1; z < n; z++) 
      for (x = 0; x < n; x++)
	for (y = x+1; y < n; y++) {
	  if (insert_cl_2(OMEGA(x, y, w), /* x < y */
			  OMEGA(x, y, z), 
			  FF, cl_arr, sign_arr)) return 1;

	  for (u = z+1; u < n; u++) {
	    if (insert_cl_all_3(OMEGA(y, x, u),  /* x < y */
				OMEGA(y, x, w), 
				OMEGA(y, x, z), 
				FF, cl_arr, sign_arr)) return 1;
	  }

	}

  return 0;
}

int qg47 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* Triple Whist Tournament */
{
  int w, x, y, z;

  for (x = 0; x <= n1; x++)
    for (y = 0; y < n1; y += 4)
      for (z = n1; z > 0; z--) 
	for (w = z-1; w >= 0; w--) {
	  /* (a c) or (c a) */
	  n_offset = SQUARE2;
	  if (insert_cl_all_3(TRIPLE2KEY(x, y, w),
			      TRIPLE2KEY(x, y+2, z), 
			      OMEGA(w, z, x), 
			      1, cl_arr, sign_arr))
	    return 1;

	  if (insert_cl_all_3(TRIPLE2KEY(x, y+2, w),
			      TRIPLE2KEY(x, y, z), 
			      OMEGA(w, z, x), 
			      1, cl_arr, sign_arr))
	    return 1;

	  /* (a b), (b a), (c d), or (d c) */
	  n_offset = SQUARE2+SQUARE2;
	  if (insert_cl_all_3(TRIPLE2KEY(x, y, w),
			      TRIPLE2KEY(x, y+1, z), 
			      OMEGA(w, z, x), 
			      1, cl_arr, sign_arr))
	    return 1;

	  if (insert_cl_all_3(TRIPLE2KEY(x, y+1, w),
			      TRIPLE2KEY(x, y, z), 
			      OMEGA(w, z, x), 
			      1, cl_arr, sign_arr))
	    return 1;

	  if (insert_cl_all_3(TRIPLE2KEY(x, y+2, w),
			      TRIPLE2KEY(x, y+3, z), 
			      OMEGA(w, z, x), 
			      1, cl_arr, sign_arr))
	    return 1;

	  if (insert_cl_all_3(TRIPLE2KEY(x, y+3, w),
			      TRIPLE2KEY(x, y+2, z), 
			      OMEGA(w, z, x), 
			      1, cl_arr, sign_arr))
	    return 1;

	  /* (a d), (d a), (b c), or (c b) */
	  n_offset = SQUARE2+SQUARE2+SQUARE2;
	  if (insert_cl_all_3(TRIPLE2KEY(x, y, w),
			      TRIPLE2KEY(x, y+3, z), 
			      OMEGA(w, z, x), 
			      1, cl_arr, sign_arr))
	    return 1;

	  if (insert_cl_all_3(TRIPLE2KEY(x, y+3, w),
			      TRIPLE2KEY(x, y, z), 
			      OMEGA(w, z, x), 
			      1, cl_arr, sign_arr))
	    return 1;

	  if (insert_cl_all_3(TRIPLE2KEY(x, y+1, w),
			      TRIPLE2KEY(x, y+2, z), 
			      OMEGA(w, z, x), 
			      1, cl_arr, sign_arr))
	    return 1;

	  if (insert_cl_all_3(TRIPLE2KEY(x, y+2, w),
			      TRIPLE2KEY(x, y+1, z), 
			      OMEGA(w, z, x), 
			      1, cl_arr, sign_arr))
	    return 1;
	}

  for (n_offset = 3*SQUARE2; n_offset; n_offset -= SQUARE2)
    for (w = 0; w < n; w++) 
      for (z = w+1; z < n; z++) 
	for (x = 0; x < n; x++)
	  for (y = x+1; y < n; y++)
	    if (insert_cl_2(OMEGA(x, y, w), 
			    OMEGA(x, y, z), 
			    FF, cl_arr, sign_arr)) return 1;
  
  return 0;
}

int qg52 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* Round-Robin Tournament:
         P(i, j, k) iff i playes j in week k. */
{
  int x, y, z;

  if (n % 2) {
    printf("The number of teams must be even (now is %d)\n", n);
    return 1;
  }
 
  for (x = n1; x >= 0; x--) {
    insert_cl_1(TRIPLE2KEY(x, x, 0), TT);
    insert_cl_1(TRIPLE2KEY(0, x, x), TT);
    insert_cl_1(TRIPLE2KEY(x, 0, x), TT);

    for (y = n1; y > 0; y--) if (x != y)
      for (z = n1; z > 0; z--) {
	if (insert_cl_2(TRIPLE2KEY(x, y, z),
			TRIPLE2KEY(y, x, z), 
			1, cl_arr, sign_arr))
	  return 1;
      }
  }

  return 0;
}

int qg53 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* Round-Robin Tournament with Periods:
         Q(i, k, x) iff i playes in week k at period x. */
{
  int x, y, z, u;
 
  for (x = n1; x >= 0; x--) {
    /*insert_cl_1(SQUARE2+TRIPLE2KEY(x, x, x), TT);*/

    for (y = x-1; y >= 0; y--)
      for (z = n1; z > 0; z--)
	for (u = n1; u > 0; u--) {
	  if (insert_cl_all_3(TRIPLE2KEY(x, y, z),
			      SQUARE2+TRIPLE2KEY(x, z, u), 
			      SQUARE2+TRIPLE2KEY(y, z, u-1), 
			      1, cl_arr, sign_arr))
	    return 1;
	  if (insert_cl_all_3(TRIPLE2KEY(x, y, z),
			      SQUARE2+TRIPLE2KEY(y, z, u-1), 
			      SQUARE2+TRIPLE2KEY(x, z, u), 
			      1, cl_arr, sign_arr))
	    return 1;
	}
  }

  return 0;
}

int qg63 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* if (x * y = z) then  (x * z) != y -- pure MTS */
{
  int x, y, z;

  if (QUEEN == 63 && m % 6 == 3) {
    x = m/3;
    if (PIGEON == 9) {
      if (insert_cl_1(TRIPLE2KEY(0, x, x+x), TT)) return 1;
    } else if (PIGEON == 10) {
      if (insert_cl_1(TRIPLE2KEY(0, x+x, x), TT)) return 1;
    }
  }
 
  for (x = m-1; x >= 0; x--) 
    for (y = m-1; y >= 0; y--) if (x != y)
      for (z = n1; z >= 0; z--) if (z != x && z != y) {

	if (insert_cl_2(TRIPLE2KEY(x, y, z),
			TRIPLE2KEY(x, z, y), 
			0, cl_arr, sign_arr))
	  return 1;
      }

  return 0;
}

int qg64 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
{
  int u, x, y, z, k, n2;
  k = get_k_flag();
  if (k < 2) k = 2;
  n2 = n-k;

  if (n2 % 6 == 3) {
    /*    for (x = 0; x < n2; x++)
      for (y = x+a; y < n2; y += a)
	for (z = n1; z >= 0; z--) if (z >= n2 || z%a != x%a) {
printf("%d * %d != %d\n", x, y, z);
	  if (insert_cl_1(TRIPLE2KEY(x, y, z), FF)) return 1;
	  if (insert_cl_1(TRIPLE2KEY(y, x, z), FF)) return 1;
	}
    if (insert_cl_1(TRIPLE2KEY(0, a, a+a), TT)) return 1;
	*/
  }

  for (x = n2; x < n; x++)
    for (y = n2; y < n; y++) if (x != y)
      for (z = n2; z < n; z++)
	if (insert_cl_1(TRIPLE2KEY(x, y, z), FF)) return 1;

  for (u = n1-k; u > 0; u--) 
    for (x = n1-k; x >= 0; x--) 
      for (y = n1-k; y >= 0; y--) if (x != y)
	for (z = n1; z >= 0; z--) {
	  if (z < n2) {
	    if (insert_cl_2(TRIPLE2KEY(x, y, z),
			    TRIPLE2KEY((x+u)%n2, (y+u)%n2, (z+u)%n2), 
			    0, cl_arr, sign_arr))
	      return 1;
	  } else {
	    if (insert_cl_2(TRIPLE2KEY(x, y, z),
			    TRIPLE2KEY((x+u)%n2, (y+u)%n2, z), 
			    0, cl_arr, sign_arr))
	      return 1;
	  }
      }
  
  return 0;
}

int qg66 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
{
  int  x, k;
  k = get_k_flag();

  if (m < n && k < m) {
    printf("k_flag = %d should be greater than %d\n", k, m);
  }

  for (x = 0; x < m; x++) {
    if (insert_cl_1(TRIPLE2KEY(k, x, x), TT)) return 1;
    if (insert_cl_1(TRIPLE2KEY(x, k, x), TT)) return 1;
    if (insert_cl_1(TRIPLE2KEY(x, x, k), TT)) return 1;
  }
  return 0;
}

int qg67 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
{
  int u, x, y, z;
  int n2 = n - get_k_flag();
  printf("n2 = %d\n", n2);

  for (x = 0; x < n; x++) {
    if (insert_cl_1(TRIPLE2KEY(0, x, x), TT)) return 1;
    if (insert_cl_1(TRIPLE2KEY(x, 0, x), TT)) return 1;
    if (insert_cl_1(TRIPLE2KEY(x, x, 0), TT)) return 1;
  }

  for (x = n2; x < n; x++)
    for (y = n2; y < n; y++) if (x != y)
      for (z = n2; z < n; z++)
	if (insert_cl_1(TRIPLE2KEY(x, y, z), FF)) return 1;

  for (u = n2-1; u > 0; u--) 
    for (x = n2-1; x > 0; x--) 
      for (y = n2-1; y > 0; y--) if (x != y) 
	for (z = n1; z >= 0; z--) {
	  if (z < n2) {
	    if (insert_cl_2(TRIPLE2KEY(x, y, z),
			    TRIPLE2KEY((x+u)%n2, (y+u)%n2, (z+u)%n2), 
			    0, cl_arr, sign_arr))
	      return 1;
	  } else {
	    if (insert_cl_2(TRIPLE2KEY(x, y, z),
			    TRIPLE2KEY((x+u)%n2, (y+u)%n2, z), 
			    0, cl_arr, sign_arr))
	      return 1;
	  }
      }
  return 0;
}

int qg68 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
{
  int u, x, y, z, k, n2;
  k = 2;
  n2 = n-k;

  if (insert_cl_1(TRIPLE2KEY(n2, n1, 0), TT)) return 1; 
  if (insert_cl_1(TRIPLE2KEY(n1, n2, 0), TT)) return 1; 

  for (u = 1; u < n2; u++) 
    for (z = 1; z < n2; z++) if (u != z) {
      if (insert_cl_2(TRIPLE2KEY(n2, z, u), 
		      TRIPLE2KEY(n1, u, z), 
		      TT, cl_arr, sign_arr))
	return 1;
      if (insert_cl_2(TRIPLE2KEY(n1, z, u), 
		      TRIPLE2KEY(n2, u, z), 
		      TT, cl_arr, sign_arr))
	return 1;
    }

  for (x = n2-3; x >= 0; x--) 
    for (y = n2-2; y > x; y--) 
      for (z = n2-1; z > y; z--) {
	if (insert_cl_2(TRIPLE2KEY(x, y, z), 
			TRIPLE2KEY(y, x, z),
			TT, cl_arr, sign_arr))
	  return 1;
      }

  for (u = n1-k; u > 0; u--) 
    for (x = n1-k; x >= 0; x--) 
      for (y = n1-k; y >= 0; y--) if (x != y)
	for (z = n1; z >= 0; z--) {
	  if (z < n2) {
	    if (insert_cl_2(TRIPLE2KEY(x, y, z),
			    TRIPLE2KEY((x+u)%n2, (y+u)%n2, (z+u)%n2), 
			    0, cl_arr, sign_arr))
	      return 1;
	  } else {
	    if (insert_cl_2(TRIPLE2KEY(x, y, z),
			    TRIPLE2KEY((x+u)%n2, (y+u)%n2, z), 
			    0, cl_arr, sign_arr))
	      return 1;
	  }
      }
  
  return 0;
}

int qg69 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* look for one-regular conjugate orthogonal Latin-square graph*/
{
  fill_triple();
  if (co_cls(SQUARE2, 0, 5, cl_arr, sign_arr)) return 1;
  if (co_cls(2*SQUARE2, 1, 4, cl_arr, sign_arr)) return 1;
  if (co_cls(3*SQUARE2, 2, 3, cl_arr, sign_arr)) return 1;
  return 0;
}

int qg78 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* look for 6-cycle conjugate orthogonal Latin-square graph */
{
  fill_triple();
  if (co_cls(SQUARE2, 0, 5, cl_arr, sign_arr)) return 1;
  if (co_cls(2*SQUARE2, 3, 1, cl_arr, sign_arr)) return 1;
  return 0;
}

int qg88 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* look for two 3-cycle conjugate orthogonal Latin-square graph */
{
  fill_triple();
  if (co_cls(SQUARE2, 0, 5, cl_arr, sign_arr)) return 1;
  if (co_cls(2*SQUARE2, 1, 2, cl_arr, sign_arr)) return 1;
  return 0;
}

int qg79 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* look for 6-cycle conjugate orthogonal Latin-square graph */
{
  fill_triple();
  if (co_cls(SQUARE2, 0, 3, cl_arr, sign_arr)) return 1;
  if (co_cls(2*SQUARE2, 0, 4, cl_arr, sign_arr)) return 1;
  if (co_cls(3*SQUARE2, 3, 1, cl_arr, sign_arr)) return 1;
  return 0;
}

int qg89 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* look for two 3-cycle conjugate orthogonal Latin-square graph */
{
  fill_triple();
  if (co_cls(SQUARE2, 0, 1, cl_arr, sign_arr)) return 1;
  if (co_cls(2*SQUARE2, 0, 2, cl_arr, sign_arr)) return 1;
  if (co_cls(3*SQUARE2, 1, 2, cl_arr, sign_arr)) return 1;
  return 0;
}

int qg101 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* *(y, *(y, *(y, x))) ==  x */
{
  int x, y, u, v;
  
  /* y * x = u, y * u = v => y * v = x */
  for (x = n1; x >= 0; x--) 
    for (y = (x >= m)? m-1 : n1; y >= 0; y--) 
      for (u = (x < m && y < m)? n1 : m-1; u >= 0; u--) 
	for (v = (x < m && y < m && u < m)? n1 : m-1; v >= 0; v--) 
	  if (insert_cl_all_3(TRIPLE2KEY(y, x, u), 
			      TRIPLE2KEY(y, u, v),
			      TRIPLE2KEY(y, v, x), 
			      1, cl_arr, sign_arr))
	    return 1;
  return 0;
}

int qg102 (cl_arr, sign_arr)
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

phi_clauses_miss (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
{
  int x, y, z, u;

  for (x = n1; x >= 0; x--) {
    if (insert_cl_1(PHI(x, x, x), 1)) return 1;
    
    for (y = (x >= m)? m-1 : n1; y >= 0; y--) if (x != y) {
      if (insert_cl_1(PHI(x, y, x), 0)) return 1;
      if (insert_cl_1(PHI(x, y, y), 0)) return 1;
    }
  }

  for (x = n1; x >= 0; x--) 
    for (y = (x >= m)? m-1 : n1; y >= 0; y--) if (is_same_hole(x, y) == 0) {
      for (z = (x >= m || y >= m)? m-1 : n1; z >= 0; z--) 
	if (is_same_hole(x, z) == 0 && is_same_hole(y, z) == 0) {

	if (x >= m) {
	  /* x * z = y => z * y != u for x >= m and u >= m */
	  for (u = n1; u >= m; u--) {
	    if (insert_cl_2(TRIPLE2KEY(x, y, z),
			    TRIPLE2KEY(y, z, u),
			    0, cl_arr, sign_arr))
	      return 1;
	  }
	}

	for (u = (z >= m || y >= m)? m-1 : n1; u >= 0; u--) {
	  /* define PI */
	  if (insert_cl_all_3(TRIPLE2KEY(x, y, z),
			      TRIPLE2KEY(y, z, u),
			      PHI(x, y, u),
			      1, cl_arr, sign_arr))
	    return 1;
	}
      }
    }

  for (x = n1; x >= 0; x--) 
    for (y = (x >= m)? m-1 : n1; y >= 0; y--) 
      for (z = (x >= m || y >= m)? m-1 : n1; z >= 0; z--) {

	if (x != z) 
	  for (u = (x >= m || y >= m)? m-1 : n1; u >= 0; u--) {

	    if (insert_cl_2(PHI(u, z, y),
			    PHI(u, x, y),
			    0, cl_arr, sign_arr))
	      return 1;

	    if (insert_cl_2(PHI(u, y, z),
			    PHI(u, y, x),
			    0, cl_arr, sign_arr))
	      return 1;

	    if (insert_cl_2(PHI(z, u, y),
			    PHI(x, u, y),
			    0, cl_arr, sign_arr))
	      return 1;
	  }
      }

  return 0;
}

cyclic_cls (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
{
  int x, y, v, k;
  int m1 = m-1;
  
  if (RESTRICT == 50) {
    for (x = m-3; x >= 0; x--) {
      insert_cl_2(TRIPLE2KEY(x, n-1, 0), 
		  TRIPLE2KEY(m-2, 0, n-1), 
		  TT, cl_arr, sign_arr);
    }
  } else if (RESTRICT == 51) {
    for (x = m-3; x >= 0; x--) {
      insert_cl_2(TRIPLE2KEY(x, n-1, 0), 
		  TRIPLE2KEY(x-1, 0, n-1), 
		  TT, cl_arr, sign_arr);
    }
  } else if (RESTRICT == 70) {
    /*  x * y = v => (m1-y) * (m1-x) = ((v + m1 - (x+y)) mod m) */
    for (x = m1; x >= 0; x--)
      for (y = x-1; y >= 0; y--) 
	for (v = m1; v >= 0; v--) {
	  int newv = m + m1 + v - (x+y); newv = newv % m; 
	  /* int newv = m1 - v; */
	  cl_arr[0] = TRIPLE2KEY(x, y, v);
	  sign_arr[cl_arr[0]] = 1;
	  if (insert_one_key(TRIPLE2KEY(m1-y, m1-x, newv), 0,
			     cl_arr, sign_arr, 1) &&
	      qg_insert_clause( cl_arr, sign_arr, 2))
	    return 1;
	  
	  /*
	  cl_arr[0] = TRIPLE2KEY(x, y, v);
	  sign_arr[cl_arr[0]] = 0;
	  if (insert_one_key(TRIPLE2KEY(m1-y, m1-x, m1-v), 1,
			     cl_arr, sign_arr, 1) &&
	      qg_insert_clause( cl_arr, sign_arr, 2))
	    return 1;
	    */
	}
  } else {
    /* RESTRICT == 55--60:
       x * y = v => (x-k) * (y-k) = (v-k) */
    k = get_k_flag();
    if (k < 1) k = 1;

    for (v = m1; v >= k; v--)
      for (x = m1; x >= k; x--) {

	if (RESTRICT >= 58) {
	  for (y = m; y < n; y++) {
	    if (insert_cl_2(TRIPLE2KEY(v, x, y),
			    TRIPLE2KEY(v-k, x-k, y),
			    TT, cl_arr, sign_arr)) return 1;
	    if (RESTRICT >= 59) {
	      if (insert_cl_2(TRIPLE2KEY(v-k, x-k, y),
			      TRIPLE2KEY(v, x, y),
			    TT, cl_arr, sign_arr)) return 1;
	    }
	  }
	}

	for (y = (RESTRICT == 55)? x-1 : m1; y >= k; y--) {
	  if (insert_cl_2(TRIPLE2KEY(v, x, y),
			  TRIPLE2KEY(v-k, x-k, y-k),
			  TT, cl_arr, sign_arr)) return 1;
	  
	  if (RESTRICT > 56) {
	    if (insert_cl_2(TRIPLE2KEY(v-k, x-k, y-k),
			    TRIPLE2KEY(v, x, y),
			    TT, cl_arr, sign_arr)) return 1;
	  }
	}
      }
  }
  return 0;
}

int P2_vs_P3(cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* P2(x, y, z, w) xor P3(x, y, z, w) */
{
  int x, y, z, w;
 
  for (z = n-2; z >= 0; z--) 
    for (x = n1; x > z; x--)
      for (y = (x >= m)? m-1 : n1; y >= 0; y--) if (x != y) 
	for (w = (z >= m)? m-1 : n1; w >= 0; w--) if (y != w && z != w) {

	  /* printf("P3(%d, %d, %d, %d) = %d\n", z, x, y, w, P3(z, x, y, w));*/

	  if (insert_cl_2(P2(z, x, y, w), 
			  P3(z, x, y, w), 
			  0, cl_arr, sign_arr))
	    return 1;
        }
  return 0;
}

symmetric_cls (num, cl_arr, sign_arr)
     int num, cl_arr[], sign_arr[];
{
  int x, y, u;

  if (IDEMPOTENT && QGROUP % 2 == 0) {
    if (get_addk() == 1) {
      /* x * x = 0 for all x */
      printf("assuming x . x = 0\n");
      for (u = QGROUP-INCOMPLETE-1; u >= 0; u--) {
	if (insert_cl_1(x = num+TRIPLE2KEY(u, u, 0), TT)) return 1;
      }
    } else if (get_addk() == 2) {
      /* x * x = n for all x */
      printf("assuming x . x = %d\n", QGROUP-1);
      for (u = n1-INCOMPLETE; u >= 0; u--) 
	if (insert_cl_1(x = num+TRIPLE2KEY(u, u, n1), TT)) return 1;
    } else if (get_addk() == 3) {
      printf("assuming x . x = a for some a\n");
      for (u = n1-INCOMPLETE; u >= 0; u--) 
	for (x = m-1; x > 0; x--)
	  for (y = x-1; y >= 0; y--) {
	    /* there exists y for all x . x * x = y. */
	    cl_arr[0] = num+TRIPLE2KEY(x, x, u);
	    cl_arr[1] = num+TRIPLE2KEY(y, y, u);

	    Clause_num++;
	    sign_arr[cl_arr[0]] = 0;
	    sign_arr[cl_arr[1]] = 1;
	    if (insert_clause ( cl_arr, sign_arr, 2)) return 1;

	    Clause_num++;
	    sign_arr[cl_arr[0]] = 1;
	    sign_arr[cl_arr[1]] = 0;
	    if (insert_clause ( cl_arr, sign_arr, 2)) return 1;
	  }
    }
  }

  for (u = n1; u >= 0; u--) 
    for (x = (u >= m)? m-1 : n1; x > 0; x--)
      for (y = (x >= m)? m-1 : x-1; y >= 0; y--) {
	cl_arr[0] = num+TRIPLE2KEY(x, y, u);
	cl_arr[1] = num+TRIPLE2KEY(y, x, u);
      
	Clause_num++;
	sign_arr[cl_arr[0]] = 0;
	sign_arr[cl_arr[1]] = 1;
	if (insert_clause ( cl_arr, sign_arr, 2)) return 1;

	Clause_num++;
	sign_arr[cl_arr[0]] = 1;
	sign_arr[cl_arr[1]] = 0;
	if (insert_clause ( cl_arr, sign_arr, 2)) return 1;
      }

  return 0;
}

symm_trasversal(cl_arr, sign_arr)
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

diagonal_cls (cl_arr, sign_arr)
     int cl_arr[], sign_arr[];
{
  int x, y, u, w;
  w = m-1;

  for (u = m; u < n; u++)
    for (x = 0; x < m; x++)
      if (insert_cl_1(TRIPLE2KEY(x, w-x, u), 0)) return 1;

  for (u = 0; u < m; u++) 
    for (x = m-1; x > 0; x--)
      for (y = x-1; y >= 0; y--) {
	if (insert_cl_2(TRIPLE2KEY(x, w-x, u), 
			TRIPLE2KEY(y, w-y, u), 
			0, cl_arr, sign_arr))
	  return 1;
      }

  if (!IDEMPOTENT) 

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

  return 0;
}

diagonal_cls321 (cl_arr, sign_arr)
     int cl_arr[], sign_arr[];
{
  int x, y, u, w;
  w = m-1;

  if (diagonal_cls(cl_arr, sign_arr)) return 1;

  for (u = m; u < n; u++)
    for (x = 0; x < m; x++)
      if (insert_cl_1(TRIPLE2KEY(u, x, w-x), 0)) return 1;

  for (u = 0; u < m; u++) 
    for (x = m-1; x > 0; x--)
      for (y = x-1; y >= 0; y--) {
	if (insert_cl_2(TRIPLE2KEY(u, x, w-x), 
			TRIPLE2KEY(u, y, w-y), 
			0, cl_arr, sign_arr))
	  return 1;
      }

  if (!IDEMPOTENT) 

    for (u = m; u < n; u++)
      for (x = 0; x < m; x++)
	if (insert_cl_1(TRIPLE2KEY(u, x, x), 0)) return 1;

    for (u = 0; u < m; u++) 
      for (x = m-1; x > 0; x--)
	for (y = x-1; y >= 0; y--) {
	  if (insert_cl_2(TRIPLE2KEY(u, x, x), 
			  TRIPLE2KEY(u, y, y), 
			  0, cl_arr, sign_arr))
	    return 1;
	}
  
  return 0;
}

orthogonal_cls (num, cl_arr, sign_arr, conj)
     int num, cl_arr [], sign_arr [], conj;
     /* x * y = u, z * w = u, x # y = v, z # w = v -> x = z OR y = w */
{
  int x, y, z, u, v, w, a, b, c;

  if (num == 3) {
    /* no symmtry between square 2 and square 3 */
    for (y = 2; y < n; y++) 
      for (z = 1; z < y; z++) 
	if (insert_cl_2(SQUARE2+TRIPLE2KEY(0, 1, y), 
			SQUARE2+SQUARE2+TRIPLE2KEY(0, 1, z), 
			0, cl_arr, sign_arr))
	  return 1;
  }

  while (num-- > 0) {
    if (num == 1) { a = c = 0; b = SQUARE2+SQUARE2; }
    else if (num == 2) { a = SQUARE2; b = c = SQUARE2+SQUARE2; }
    else { a = 0; b = c = SQUARE2; }

    if (PIGEON == 2) {
      if (ortho_P2(a, b, c, cl_arr, sign_arr, conj)) return 1;
    } else {
      for (x = n1; x > 0; x--)
	for (y = (x >= m)? m-1 : n1; y >= 0; y--) if (x != y) {

	  for (z = (x < m && y < m)? n1 : m-1; z >= 0; z--) 
	    if (z != x && z != y && 
		insert_cl_4(b+TRIPLE2KEY(y, y, y),
			    b+TRIPLE2KEY(x, z, y), 
			    a+TRIPLE2KEY(y, y, y),
			    a+TRIPLE2KEY(x, z, y), 
			    0, cl_arr, sign_arr))
	      return 1;

	  for (z = x-1; z >= 0; z--) 
	    for (w = (z >= m)? m-1 : n1; w >= 0; w--) if (y != w) 
	      for (u = (x < m && y < m && z < m && w < m)? n1 : m-1; u >= 0; u--) 
		for (v = (x < m && y < m && z < m && w < m)? n1 : m-1; v >= 0; v--) 
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

void transpose_Lsquare2 (flag)
     int flag;
{
  int x, y, z;

  if (flag == 0) 
    for (x = n1; x > 0; x--)
      for (y = x-1; y >= 0; y--) {
	z = Lsquare2[x][y];
	Lsquare2[x][y] = Lsquare2[y][x];
	Lsquare2[y][x] = z;
      }
  else {
    int sq[11][11];
    for (x = n1; x > 0; x--)
      for (y = n1; y >= 0; y--) sq[x][y] = Lsquare2[x][y];
    for (x = n1; x > 0; x--)
      for (y = n1; y >= 0; y--) Lsquare2[sq[x][y]][y] = x;
  }
}

ortho_Lsquare2 (num, cl_arr, sign_arr)
     int num, cl_arr [], sign_arr [];
     /* x * y = u, z * w = u, x # y = v, z # w = v -> x = z OR y = w */
{
  int x, y, z, u, v, w;

  for (x = n1; x > 0; x--)
    for (y = (x >= m)? m-1 : n1; y >= 0; y--) if (x != y) {

      for (z = (x < m && y < m)? n1 : m-1; z >= 0; z--) 
	if (z != x && z != y && 
	    Lsquare2[y][y] == y &&
	    Lsquare2[x][z] == y &&
	    insert_cl_2(num+TRIPLE2KEY(y, y, y),
			num+TRIPLE2KEY(x, z, y), 
			0, cl_arr, sign_arr))
	  return 1;

      for (z = x-1; z >= 0; z--) 
	for (w = (z >= m)? m-1 : n1; w >= 0; w--) if (y != w && z != w) 
	  for (u = (x < m && y < m && z < m && w < m)? n1 : m-1; u >= 0; u--) 
	    for (v = (x < m && y < m && z < m && w < m)? n1 : m-1; v >= 0; v--) 
	      if (Lsquare2[x][y] == u &&
		  Lsquare2[z][w] == u &&
		  insert_cl_2(num+TRIPLE2KEY(x, y, v), 
			      num+TRIPLE2KEY(z, w, v), 
			      0, cl_arr, sign_arr))
		return 1;
    }
  return 0;
}

ortho_P2_symm (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* x * y = u, z * w = u, x . y = v, z . w = v -> x = z, y = w */
{
  int x, y, z, w;

  if (phi_cls_P2(0, cl_arr, sign_arr)) return 1;

  for (x = n1; x >= MINUTES; x--)
    for (y = x; y >= 0; y--) if (is_same_hole(x, y) == 0)
      for (z = n1; z >= 0; z--) 
	for (w = n1; w >= 0; w--) {

	  if (insert_cl_all_3(SQUARE2+TRIPLE2KEY(x, y, w),
			      TRIPLE2KEY(x, y, z),
			      PHI(x, w, z), 
			      1, cl_arr, sign_arr))
	    return 1;
	}

  return 0;
}

ortho_P2 (a, b, c, cl_arr, sign_arr, conj)
     int a, b, c, cl_arr [], sign_arr [], conj;
     /* x * y = u, z * w = u, x . y = v, z . w = v -> x = z, y = w */
{
  int x, y, z, w;

  if (phi_cls_P2(c, cl_arr, sign_arr)) return 1;

  for (x = n1; x >= 0; x--)
    for (y = n1; y >= 0; y--) if (is_same_hole(x, y) == 0)
      for (z = n1; z >= 0; z--) if (is_same_hole(x, z) == 0 && is_same_hole(y, z) == 0)
	for (w = n1; w >= 0; w--) if (is_same_hole(x, w) == 0 && is_same_hole(y, w) == 0) {

	  if (insert_cl_all_3(a+TRIPLE2KEY(x, y, w),
			      b+((conj == 0)? TRIPLE2KEY(x, y, z) :
				 (conj == 1)? TRIPLE2KEY(y, x, z) :
				 (conj == 2)? TRIPLE2KEY(z, y, x) :
				 (conj == 3)? TRIPLE2KEY(y, z, x) :
				 TRIPLE2KEY(x, y, z)),
			      c+PHI(x, w, z), 
			      1, cl_arr, sign_arr))
	    return 1;
	}

  return 0;
}

int qg_insert_clause ( cl_arr, sign_arr, total )
     int cl_arr[], sign_arr[], total;
{ 
  if (double_cl) {
    int i, j, cl_arr2[100];

    if (double_cl > 1) {
      int cl_arr3[100];
      int line2 = SQUARE2+SQUARE2;

      for (i = 0; i < total; i++) {
	j = cl_arr[i];
	cl_arr3[i] = j+line2;
	sign_arr[j+line2] = sign_arr[j];
      }
      Clause_num++;
      if (insert_clause ( cl_arr3, sign_arr, total )) return 1;
    }

    for (i = 0; i < total; i++) {
      j = cl_arr[i];
      cl_arr2[i] = j+SQUARE2;
      sign_arr[j+SQUARE2] = sign_arr[j];
    }
    Clause_num++;
    if (insert_clause ( cl_arr2, sign_arr, total )) return 1;
  }

  Clause_num++;
  if (insert_clause ( cl_arr, sign_arr, total )) { return 1; }
  return 0;
}

qg_read_square ()
{
  int i, j, k;
  int save = 0;
  char name[20];

  if (LINE > 5000) save = 1;
  if (Input_sqs == NULL) {
    if (LINE > 5000) {
      sprintf(name, "i%d.in", LINE%1000);
      for (i = 0; i < n; i++)
	for (j = 0; j < n; j++)
	  Lsquare2[i][j] = -2;
    } else 
      sprintf(name, "l%d.in", LINE%1000);
    open_input_sqs(name); 
  } else   /* skip the first number */
    read_int(Input_sqs, &i);

  if (fscanf(Input_sqs, "%d", &i) == EOF) {
    printf("No more inputs.\n"); 
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
	  printf("Bad input: %d (-1 expected)\n", k); exit(1); 
	} 
	printf("-1 ");
      } else if (k >= 0) {
	printf("%2d ", k);
	if (save) {
	  Lsquare2[i][j] = k;
	} else
	  if (insert_cl_1(TRIPLE2KEY(i, j, k), TT)) bug(9);
      } else
	printf("%2d ", k);
    }
  }
  printf("\n\n");

  /* if (LINE > 9000) {  shuffle_square2(); exit(1); } */

  if (QUEEN == 30) {
    /* read in two more squares */
    for (save = SQUARE2; save <= SQUARE2+SQUARE2; save += SQUARE2) 
      for (i = 0; i < n; i++) 
	for (j = 0; j < n; j++) {
	  if (fscanf(Input_sqs, "%d", &k) == EOF) { return 0; }
	  if (is_same_hole(i, j) == 0 && k >= 0) {
	    if (insert_cl_1(save+TRIPLE2KEY(i, j, k), TT)) bug(9);
	  }
	}
  }

  return 0;
}

qg_read_square_mod2 ()
{
  int i, j, k, x;
  char name[20];

  sprintf(name, "b%d.in", LINE%1000);
  Input_sqs = fopen(name, "r"); 
  if (Input_sqs == NULL) { printf("%s: cannot open\n", name); exit(1); }
  for (i = 0; i < n; i++) 
    for (j = 0; j < n; j++) {
      if (fscanf(Input_sqs, "%d", &k) == EOF) { 
	  fclose(Input_sqs); Input_sqs = NULL;
	  return 0; 
      }
      if (is_same_hole(i, j) == 0 && (k == 0 || k == 1)) {
	k++;
	while (k < m) {
	  if (insert_cl_1(TRIPLE2KEY(i, j, k), FF)) bug(7);
	  k += 2;
	}
      }
    }

  if (QUEEN == 30) {
    for (x = 1; x < 3; x++) {
      printf("reading matrix #%d\n", x+1);
      for (i = 0; i < n; i++) 
	for (j = 0; j < n; j++) {
	  if (fscanf(Input_sqs, "%d", &k) == EOF) { 
	    fclose(Input_sqs); Input_sqs = NULL;
	    return 0; 
	  }
	  if (is_same_hole(i, j) == 0 && (k == 0 || k == 1)) {
	    k++;
	    while (k < m) {
	      if (insert_cl_1(x*SQUARE2+TRIPLE2KEY(i, j, k), FF)) bug(7);
	      /* printf("%d * %d != %d\n", i, j, k); */
	      k += 2;
	    }
	  }
	}
    }
  }

  printf("finished reading matrix\n");
  fclose(Input_sqs);
  Input_sqs = NULL;
  return 0;
}

int rpmd_cls (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
{
  int x, y, u, v;

  for (x = 0; x < n; x++) 
    if (is_same_hole(0, x)) {
      for (u = 0; u < n; u++) 
	for (v = 1; v < n; v++) 
	  if (insert_cl_1(OMEGA(u, v, x), FF)) return 1;
    }
    else if (insert_cl_1(OMEGA(0, x, x), TT)) return 1;

  for (x = 0; x < n; x++) 
    for (y = 0; y < n; y++) if (is_same_hole(x, y) == 0) {
      for (u = 0; u < n; u++) {

	for (v = u+1; v < n; v++) {
	  if (insert_cl_2(OMEGA(x, y, v), 
			  OMEGA(x, y, u), 
			  FF, cl_arr, sign_arr)) return 1;
	  if (insert_cl_2(OMEGA(x, v, y), 
			  OMEGA(x, u, y), 
			  FF, cl_arr, sign_arr)) return 1;
	  if (insert_cl_2(OMEGA(v, x, y), 
			  OMEGA(u, x, y), 
			  FF, cl_arr, sign_arr)) return 1;
	}

	for (v = 1; v < n; v++) 
	  if (is_same_hole(y, u) == 0) {
	    if (insert_cl_all_3(TRIPLE2KEY(x, y, u), 
				OMEGA(x, y, v), 
				OMEGA(y, u, v), 
				TT, cl_arr, sign_arr)) return 1;
	  }
      }

      /* if (x > 0 && y > x) {
	v = 0;
	for (u = n1; u > 0; u--) {
	  cl_arr[v] = OMEGA(x, y, u);
	  sign_arr[cl_arr[v++]] = 1;
	}
	if (qg_insert_clause( cl_arr, sign_arr, v) == 1) return 1;
      }*/
    }

  return 0;
}

int omega_cls (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
{
  int x, y, u, v;
  int q37offset=0;
  if (QUEEN == 37 || QUEEN == 38) q37offset = 1;

  for (x = 0; x < n; x++)
    for (y = 0; y < n; y++) if (is_same_hole(x, y) == 0)
      for (u = 0; u < n; u++) 
	if (is_same_hole(x, u) == 0 && is_same_hole(y, u) == 0)
	  for (v = u+1; v < n-q37offset; v++) 
	    if (is_same_hole(x, v) == 0 && is_same_hole(y, v) == 0) {
	      if (insert_cl_2(OMEGA(v, x, y), 
			      OMEGA(u, x, y), 
			      FF, cl_arr, sign_arr)) return 1;
	    }
  return 0;
}

int phi_cls_P2 (offset, cl_arr, sign_arr)
     int offset, cl_arr [], sign_arr [];
{
  int x, y, u, v;

  for (x = 0; x < n; x++)
    for (y = 0; y < n; y++)
      for (u = 0; u < n; u++)
	for (v = u+1; v < n; v++) {
	  if (insert_cl_2(offset+PHI(v, x, y), 
			  offset+PHI(u, x, y), 
			  FF, cl_arr, sign_arr)) return 1;
	}
  return 0;
}

qg39_unit_cls ()
{
  if (insert_cl_1(OMEGA(0, 1, 1), TT)) return 1;
  if (insert_cl_1(OMEGA(0, 0, 2), TT)) return 1;
  if (insert_cl_1(OMEGA(1, 2, 2), TT)) return 1;
  if (insert_cl_1(OMEGA(1, 1, 0), TT)) return 1;
  if (insert_cl_1(OMEGA(2, 0, 0), TT)) return 1;
  if (insert_cl_1(OMEGA(2, 2, 1), TT)) return 1;
  if (insert_cl_1(OMEGA(3, 2, 0), TT)) return 1;
  if (insert_cl_1(OMEGA(3, 0, 1), TT)) return 1;
  if (insert_cl_1(OMEGA(3, 1, 2), TT)) return 1;
  return 0;
}

qg23_unit_cls ()
{
  int i, j, k;
  char name[20];

  sprintf(name, "qg%d.sqs.%d", QUEEN, LINE);
  Input_sqs = fopen(name, "r");
  if (Input_sqs != NULL) {
    for (i = 0; i < n; i++) {
      for (j = 0; j < n; j++) {
	fscanf(Input_sqs, "%d", &k);
	printf(" %2d", k);
	if (k >= 0) {
	  if (insert_cl_1(TRIPLE2KEY(i, j, k), TT)) return 1;
	}
      }
      printf("\n");
    }
    printf("\n");

    for (i = 0; i < n; i++) {
      for (j = 0; j < n; j++) {
	fscanf(Input_sqs, "%d", &k);
	printf(" %2d", k);
	if (k >= 0) {
	  if (insert_cl_1(SQUARE2+TRIPLE2KEY(i, j, k), TT)) return 1;
	}
      }
      printf("\n");
    }
  }

  return 0;
}

orthogonal_cls_3 (num, conj, cl_arr, sign_arr)
     int num, conj, cl_arr [], sign_arr [];
     /* otherthan the {0,1,2}x{0,1,2},
	x * y = u, z * w = u, x # y = v, z # w = v -> x = z OR y = w */
{
  int x, y, z, u, v, w, b;
  
  if (num == 1) b = SQUARE2; else b = 0;

  for (x = n1; x >= 0; x--)
    for (y = (x >= m)? m-1 : n1; y >= 0; y--) {

      if (y < 3) {
	for (z = (x < m && y < m)? n1 : m-1; z >= 0; z--) 
	  if (z != x && z != y) {
	    if (insert_cl_5(b+TRIPLE2KEY(y, y, y),
			    b+TRIPLE2KEY(x, z, y), 
			    TRIPLE2KEY(y, y, y),
			    conj_TRIPLE2KEY(conj, x, z, y), 
			    C3(y, y),
			    1, cl_arr, sign_arr))
	      return 1;
	    if (TRACE > 1) 
	      printf ("C(%d, %d) from (%d, %d) on (%d, %d)\n", y, y, x, z, y, y); 
	  }
      } else {
	for (z = (x < m && y < m)? n1 : m-1; z >= 0; z--) 
	  if (z != x && z != y) {
	    if (x < 3 && z < 3) {
	      if (insert_cl_5(b+TRIPLE2KEY(y, y, y),
			      b+TRIPLE2KEY(x, z, y), 
			      TRIPLE2KEY(y, y, y),
			      conj_TRIPLE2KEY(conj, x, z, y), 
			      C3(x, z),
			      1, cl_arr, sign_arr))
		return 1;
	      if (TRACE > 1) 
		printf ("C(%d, %d) from (%d, %d) on (%d, %d)\n", x, z, y, y, y, y); 
	    } else {
	      if (insert_cl_4(b+TRIPLE2KEY(y, y, y),
			      b+TRIPLE2KEY(x, z, y), 
			      TRIPLE2KEY(y, y, y),
			      conj_TRIPLE2KEY(conj, x, z, y), 
			      0, cl_arr, sign_arr))
		return 1;
	    }
	  }
      }

      if (x < 3 && y < 3) {
	for (z = 0; z < n; z++) if (x != z)
	  for (w = (z >= m)? m-1 : n1; w >= 0; w--) if (y != w) 
	    for (u = (x < m && y < m && z < m && w < m)? n1 : m-1; u >= 0; u--) 
	      for (v = (x < m && y < m && z < m && w < m)? n1 : m-1; v >= 0; v--) {
		if (insert_cl_5(b+TRIPLE2KEY(x, y, u),
				b+TRIPLE2KEY(z, w, u), 
				conj_TRIPLE2KEY(conj, x, y, v), 
				conj_TRIPLE2KEY(conj, z, w, v), 
				C3(x, y),
				1, cl_arr, sign_arr))
		return 1; 
		if (TRACE > 1)
		  printf ("C(%d, %d) from (%d, %d) on (%d, %d)\n", x, y, z, w, u, v); 
	      }
      } else {
	for (z = n1; z >= 0; z--) if (x != z)
	  for (w = (z >= m)? m-1 : n1; w >= 0; w--) 
	    if (y != w && (z >= 3 || w >= 3))
	    for (u = (x < m && y < m && z < m && w < m)? n1 : m-1; u >= 0; u--) 
	      for (v = (x < m && y < m && z < m && w < m)? n1 : m-1; v >= 0; v--) 
		if (insert_cl_4(b+TRIPLE2KEY(x, y, u),
				b+TRIPLE2KEY(z, w, u), 
				conj_TRIPLE2KEY(conj, x, y, v), 
				conj_TRIPLE2KEY(conj, z, w, v), 
				0, cl_arr, sign_arr))
		  return 1;
      }
    }
  return 0;
}

only_3_non_orth (h, cl_arr, sign_arr)
     int h, cl_arr [], sign_arr [];
     /* x * y = u, z * w = u, x # y = v, z # w = v -> x = z OR y = w */
{
  int x, y, u, v;
  int comb[10];
  int g=8;

  if (TRACE > 1)
    for (x=0; x<3; x++) for (y=0; y<3; y++) 
      printf("C(%d, %d) = %d\n", x, y, C3(x,y));

  for (u = 0; u <= h; u++) comb[u] = u;
  while (comb[0] != 100) {
    for (u=0; u<= h; u++) {
      v = cl_arr[u] = Max_atom-comb[u];
      sign_arr[v] = FF;
    }
    Clause_num++;
    if (insert_clause ( cl_arr, sign_arr, h+1)) return 1;

    if ((comb[0] + h) == g)
      comb[0] = 100;
    else 
      next_combination(h, g, comb);  
  }

  /*
  h = 6;
  for (u = 0; u <= h; u++) comb[u] = u;
  while (comb[0] != 100) {
    for (u=0; u<= h; u++) {
      v = cl_arr[u] = Max_atom-comb[u];
      sign_arr[v] = TT;
    }
    Clause_num++;
    if (insert_clause ( cl_arr, sign_arr, h+1)) return 1;

    if ((comb[0] + h) == g)
      comb[0] = 100;
    else 
      next_combination(h, g, comb);  
  }
  */

  return 0;
}
