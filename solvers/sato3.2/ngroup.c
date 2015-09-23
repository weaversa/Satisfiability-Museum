/*********************************************************************
; Copyright 1992-97, The University of Iowa (UI).  All rights reserved. 
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
#define ALPHA(x,y) (((y) * m) + x + 1)
#define BETA(x,y) ((((n - m) + (x)) * m) + y + 1)
#define GAMMA(x,y) (((((n - m) << 1) + (x)) * m) + y + 1)
#define THETA(x,y) (((((n - m) << 1) + n + (x)) * m) + y + 1)
#define TRIPLEtKEY(i,j,k) (((i) * n_sqt) + ((j) * n) + k + 1)
#define TRIPLEcKEY(x,y,z) ((x<m)? ((y<m)? ALPHA(DIFF(y,x),((z<m)? DIFF(z,x) : z)) : \
				   BETA(y,DIFF(z,x))) : GAMMA(x,DIFF(z,y)))
#define TRIPLE2KEY(x,y,z) ((CYCLIC)? \
			   (TRIPLEcKEY(x,y,z)) : (TRIPLEtKEY(x,y,z)))

/**** Abelian groups ****/
GLOB SATOINT ABG_f[MAX_ABG_SIZE][MAX_ABG_SIZE];
GLOB SATOINT ABG_g[MAX_ABG_SIZE];

extern int m, n, n1, n_sqt, n_cube, n_four, n_offset;

int co_cls (step, op1, op2, cl_arr, sign_arr)
  /* co = conjugate orthogonal */
     int step, op1, op2, cl_arr [], sign_arr [];
     /* x *ijk y = u, z *ijk w = u, x *abc y = v, z *abc w = v ->
	x = z OR y = w */
{
  int x, y, z, u, v, w;

  if (OUTPUT < 2) printf("     orthogonality between (%d)- and (%d)-conjugates\n",
			  conjugate_num(op1), conjugate_num(op2));

  if (PIGEON == 2) return(co_cls_P2(step, op1, op2, cl_arr, sign_arr));

  /*
  for (x = n1; x >= 0; x--)
    for (y = (x >= m)? m-1 : n1; y >= 0; y--) 
      if (x != y && is_same_hole(x, y) == 0) {

	for (z = n1; z >= 0; z--) 
	  if (z != x && z != y &&
	      insert_cl_all_3(TRIPLE2KEY(y, y, y),
			      co_key(op1, x, z, y), 
			      co_key(op2, x, z, y), 
			      0, cl_arr, sign_arr))
	    return 1;
      }

      if (NHOLE) {
	for (u = 0; u < m; u++) 
	  for (v = u % NHOLE; v < m; v += NHOLE)
	    if (insert_cl_2(co_key(op1, x, y, u), 
			    co_key(op2, x, y, v), 
			    0, cl_arr, sign_arr))
	      return 1;
      } else if (IDEMPOTENT == 1) {
	for (z = m-1; z >= 0; z--) {
	  if (z != x && z != y &&
	      insert_cl_2(co_key(op1, x, y, z), 
			  co_key(op2, x, y, z), 
			  0, cl_arr, sign_arr))
	    return 1;
	}
      }
  */

  if (CYCLIC == 'C') {
    for (x = n1; x >= 0; x--)
      for (y = (x >= m)? m-1 : n1; y >= 0; y--) if (x != y) {

	if (y < m) { 

	  for (z = m-1; z > 0; z--) if (y != z) {
	    int yz = DIFF(y,z);

	    /* 0 *1 x = y, 0 *2 x = z => <x, y-z> */
	    if (insert_cl_all_3(co_key(op1, 0, x, y),
				co_key(op2, 0, x, z),
				THETA(x, yz),
				1, cl_arr, sign_arr))
	      return 1;

	    if (x >= m) {

	      /* x *1 0 = y, x *2 0 = z, 0 * u = x => <u, y-z> */
	      if (insert_cl_all_3(co_key(op1, x, 0, y),
				  co_key(op2, x, 0, z),
				  THETA(x, yz),
				  1, cl_arr, sign_arr))
		return 1; 

	      for (u = 1; u < m; u++)
		for (v = 1; v < m; v++) if (yz == DIFF(u,v)) 
		  if (insert_cl_4(co_key(op1, x, 0, y),
				  co_key(op2, x, 0, z),
				  co_key(op1, 0, x, u),
				  co_key(op2, 0, x, v),
				  0, cl_arr, sign_arr))
		    return 1; 
	    }
	  }
	}
      }

  } else { 

    for (x = n1; x >= 0; x--)
      for (y = (x >= m)? m-1 : n1; y >= 0; y--) 
	if (x != y && is_same_hole(x, y) == 0) {

	for (z = n1; z >= 0; z--) 
	  if (is_same_hole(x, z) == 0 && 
	      is_same_hole(y, z) == 0 &&
	      insert_cl_all_3(co_key(op1, y, y, y),
			      co_key(op1, x, z, y), 
			      co_key(op2, x, z, y), 
			      0, cl_arr, sign_arr))
	    return 1;

	for (z = x-1; z >= 0; z--)
	  for (w = (z >= m)? m-1 : n1; w >= 0; w--) if (z != w) 
	    for (u = (x < m && y < m && z < m && w < m)? n1 : m-1;
		 u >= 0; u--)
	      for (v = (x < m && y < m && z < m && w < m)? n1 : m-1;
		   v >= 0; v--) 
		if (insert_cl_4(co_key(op1, x, y, u),
				co_key(op1, z, w, u),
				co_key(op2, x, y, v),
				co_key(op2, z, w, v),
				0, cl_arr, sign_arr))
		  return 1;
	}
  }
  return 0;
}

co_cls_P2 (step, op1, op2, cl_arr, sign_arr)
     int step, op1, op2, cl_arr [], sign_arr [];
     /* x * y = u, z * w = u, y * x = v, w * z = v -> x = z, y = w */
{
  int x, y, z, w;
  
  n_offset = step;
  if (omega_cls(cl_arr, sign_arr)) return 1;

  for (x = n1; x >= 0; x--)
    for (y = n1; y >= 0; y--) if (is_same_hole(x, y) == 0)
      for (z = n1; z >= 0; z--) 
	for (w = n1; w >= 0; w--) {

	  if (is_same_hole(z, w) == 0) {
	    if (insert_cl_all_3(co_key(op1, x, y, w),
				co_key(op2, x, y, z),
				OMEGA(x, w, z), 
				1, cl_arr, sign_arr))
	      return 1;
	  } else if (insert_cl_2(co_key(op1, x, y, w),
				 co_key(op2, x, y, z), 
				 0, cl_arr, sign_arr))
	    return 1;
	}

  return 0;
}

int how_many_co (edge)
     int edge[];
{
  int i, j, many;

  /* decompose QUEEN into a list of digits */
  for (i = 1; i < 10; i++) edge[i] = 0;
  i = QUEEN;
  while (i) {
    j = i % 10;
    if (j == 0) { printf("Unknown option: -Q%d\n", QGROUP); exit(0); }
    i = (i - j)/10;
    edge[j] = 1;
  }

  many = 0;
  for (i = 1; i < 10; i++) if (edge[i] == 1) many++;

  return many;
}

int co_cycle_cls(cl_arr, sign_arr)
     int cl_arr[], sign_arr[];
{
  int edge[10], i, many;

  many = how_many_co(edge);
  fill_triple();

  if (OUTPUT < 2) printf("Looking for squares satisfying\n");

  if (CYCLIC == 'C') {

    if (unique_cover_clauses(many, cl_arr, sign_arr)) return 1;

    for (i = 9; i > 0; i--) if (edge[i] == 1) {
      many--;
      if (i < 6) { 
	if (co_cls(many, 0, i, cl_arr, sign_arr)) return 1;
      } else if (i < 9) {
	if (co_cls(many, 1, i-4, cl_arr, sign_arr)) return 1;
      } else {
	if (co_cls(many, 2, 3, cl_arr, sign_arr)) return 1;
      }
    }

  } else { 

    for (i = 1; i < 10; i++) if (edge[i] == 1) {
      if (i < 6) co_cls(0, 0, i, cl_arr, sign_arr);
      else if (i < 9) co_cls(0, 1, i-4, cl_arr, sign_arr);
      else co_cls(0, 2, 3, cl_arr, sign_arr);
    }
  }
  printf("\n");
  return 0;
}

/**********************************************************/

qg50 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* looking for invertible loops */
{
  int x, y;

  /* 0 is the unity */
  for (x = n1; x >= 0; x--)
    if (!is_same_hole(0, x)) {
      insert_cl_1(TRIPLE2KEY(x, 0, x), TT);
      insert_cl_1(TRIPLE2KEY(0, x, x), TT);
    }

  /* the inverse is unique */
  for (x = n1; x >= 0; x--)
    for (y = x; y >= 0; y--) {
      if (insert_cl_2(TRIPLE2KEY(x, y, 0),
		      TRIPLE2KEY(y, x, 0),
		      1, cl_arr, sign_arr)) return 1;
    }
  return 0;
}

qg51 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* looking for invertible loops */
{
  int x, y, z;
  if (qg50(cl_arr, sign_arr)) return 1;
  
  /* commutative */
  for (x = n1; x >= 1; x--)
    for (y = x; y >= 1; y--) 
      for (z = n1; z >= 1; z--) 
	if (insert_cl_2(TRIPLE2KEY(x, y, z),
			TRIPLE2KEY(y, x, z),
			1, cl_arr, sign_arr)) return 1;
  return 0;
}
/**********************************************************/

qg60 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* Read in the first square and find the second square
	whose every conjugate is orthogonal to each conjugate of 
	the first square */
{
  int x, y, z, w, u, k;

  read_in_square("firstsqs", 0);
  fill_triple2();

  for (k = 0; k < 6; k++) {

    if (NHOLE) 
      for (x = n1; x >= 0; x--)
	for (y = (x >= m)? m-1 : n1; y >= 0; y--) {
	  for (u = 0; u < m; u++) 
	    for (w = u % NHOLE; w < m; w += NHOLE) 
	      if (getxyz(x, y, k) == w) {
		if (insert_cl_1(TRIPLE2KEY(x, y, u), 0)) return 1;
		if (insert_cl_1(TRIPLE2KEY(x, u, y), 0)) return 1;
		if (insert_cl_1(TRIPLE2KEY(u, x, y), 0)) return 1;
	      }
	}
  
    for (x = n1; x >= 0; x--)
      for (z = n1; z >= 0; z--) if (x != z)
	for (y = (x >= m)? m-1 : n1; y >= 0; y--)
	  for (w = (z >= m)? m-1 : n1; w >= 0; w--) if (y != w)
	    if (getxyz(x, y, k) == getxyz(z, w, k))
	      for (u = (x < m && y < m && z < m && w < m)? n1 : m-1; u >= 0; u--) {
		if (insert_cl_2(TRIPLE2KEY(x, y, u),
				TRIPLE2KEY(z, w, u),
				0, cl_arr, sign_arr)) return 1;
		if (insert_cl_2(TRIPLE2KEY(x, u, y),
				TRIPLE2KEY(z, u, w),
				0, cl_arr, sign_arr)) return 1;
		if (insert_cl_2(TRIPLE2KEY(u, x, y),
				TRIPLE2KEY(u, z, w),
				0, cl_arr, sign_arr)) return 1; 
	      }
  }
  return 0;
}

int orthogonal_to_first(k, cl_arr, sign_arr)
     int k, cl_arr [], sign_arr [];
     /* generate clauses for orthogonal to k-conjugate of 
	the first square */
{
  int x, y, z, w, u;

  if (NHOLE) 
    for (x = n1; x >= 0; x--)
      for (y = (x >= m)? m-1 : n1; y >= 0; y--) 
	for (u = 0; u < m; u++) 
	  for (w = u % NHOLE; w < m; w += NHOLE) {
	    if (getxyz(x, y, k) == w &&
		insert_cl_1(TRIPLE2KEY(x, y, u), 0)) {
	      return 1;
	    }
	  }

  for (x = n1; x >= 0; x--)
    for (z = n1; z >= 0; z--) if (x != z)
      for (y = (x >= m)? m-1 : n1; y >= 0; y--)
	for (w = (z >= m)? m-1 : n1; w >= 0; w--) {
	  if (y != w && getxyz(x, y, k) == getxyz(z, w, k))
	    for (u = (x < m && y < m && z < m && w < m)? n1 : m-1;
		 u >= 0; u--) {
	      if (insert_cl_2(TRIPLE2KEY(x, y, u),
			      TRIPLE2KEY(z, w, u),
			      0, cl_arr, sign_arr)) return 1;
	    }
	}
  return 0;
}
  
int qg30 (k, cl_arr, sign_arr)
     int k, cl_arr [], sign_arr [];
     /* Read in the first square and find the second square
	which is orthogonal to (123)- and (213)- conjugates of 
	the first square */
{
  read_in_square("outputsqs", 0);
  fill_triple2();
  
  if (orthogonal_to_first(0, cl_arr, sign_arr)) return 1;
  if (orthogonal_to_first(k, cl_arr, sign_arr)) return 1;
  return 0;
}

int qg104 (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* Read in the first square and find the second square
	which is symmetric and orthogonal to the first square */
{
  read_in_square("outputsqs", 0);
  fill_triple2();
  if (orthogonal_to_first(0, cl_arr, sign_arr)) return 1;
  if (qg_symmetric(cl_arr, sign_arr)) return 1;
  return 0;
}

int qg_symmetric (cl_arr, sign_arr)
     int cl_arr [], sign_arr [];
     /* (x * y) = z => (y * x) = z */
{
  int x, y, z;

  for (x = n1; x >= 0; x--) 
    for (y = n1; y >= 0; y--) 
      for (z = ((x < m && y < m)? n1 :
		((x < m || y < m)? m-1 : -1)); 
	   z >= 0; z--) {

	Clause_num++;
	cl_arr[0] = TRIPLE2KEY(x, y, z);
	sign_arr[cl_arr[0]] = 0;
	if (insert_one_key(TRIPLE2KEY(y, x, z), 1,
			   cl_arr, sign_arr, 1) == 0)
	    Subsume_num++;
	else if (qg_insert_clause ( cl_arr, sign_arr, 2) == 1)
	  return 1;
      }
  return 0;
}
