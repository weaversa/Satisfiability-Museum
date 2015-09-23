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

#define MAX_RAMSEY        50
#define PAIR2KEY(i,j) ((i * n) + j + 1)

/* Team Schedule */

/* BIGTEN schools */
#define Ill 0
#define Ind 1
#define Iow 2
#define Mic 3
#define MiS 4
#define Min 5
#define Nor 6
#define Ohi 7
#define Pen 8
#define Pur 9
#define Wis 10

/* ACC schools */
#define Clem 0
#define Duke 1
#define FSU 2
#define GT 3
#define UMD 4
#define UNC 5
#define NCS 6
#define UVA 7
#define Wake 8

#define PATTERNSIZE 1000 
#define ELEVEN 11
#define NINE 9

#define GAME(i,j,t) ((i*TEAM + j) * DAY + t + 1)
#define PI(i,j) (i * TEAM + SIZE + j + 1)
#define HOME(i,t) ((i + TEAM) * DAY + SIZE + t + 1)
#define AWAY(j,t) (j * DAY + SIZE + t + 1)
#define A(i) (i+1)
#define H(i) (i+DAY+1)
#define B(i) (i+DAY+DAY+1)
#define X(i) (i+1)

int mirror[22];
int pat[PATTERNSIZE][22];
int DAY;

int SIZE;
int init_team () { 
  if (TEAM == 1 || TEAM == 3 || TEAM == 9) DAY = 18;
  else DAY = 22;
  if (TEAM == 1 || TEAM == 2) return 3*DAY;
  if (TEAM == 3 || TEAM == 4) return PATTERNSIZE;
  if (TEAM == 9 || TEAM == 11) return TEAM * TEAM * (1 + DAY); 
  return (TEAM + 2) * TEAM * DAY; 
}

/**** The following function generates the input clauses for
  generating a basketball schedule ****/

int team_clauses ()
{
  if (TEAM == 1 || TEAM == 3 || TEAM == 9) {
    /* (0 7) (1 8) (2 11) (3 12) (4 13) (5 14) (6 15) (9 16) (10 17) */
    mirror[0] = 7; mirror[7] = 0;
    mirror[1] = 8; mirror[8] = 1;
    mirror[2] = 11; mirror[11] = 2;
    mirror[3] = 12; mirror[12] = 3;
    mirror[4] = 13; mirror[13] = 4;
    mirror[5] = 14; mirror[14] = 5;
    mirror[6] = 15; mirror[15] = 6;
    mirror[9] = 16; mirror[16] = 9;
    mirror[10] =17; mirror[17] = 10;
    mirror[18] =21; mirror[21] = 18;
    mirror[19] =20; mirror[20] = 19;
  } else {
    /* (0 11) (1 12) (2 13) (3 14) (4 15) (5 18) (6 19) (7 16) (8 17) (9 20) */
    mirror[0] = 11; mirror[11] = 0;
    mirror[1] = 12; mirror[12] = 1;
    mirror[2] = 13; mirror[13] = 2;
    mirror[3] = 14; mirror[14] = 3;
    mirror[4] = 15; mirror[15] = 4;
    mirror[5] = 16; mirror[16] = 5;
    mirror[6] = 17; mirror[17] = 6;
    mirror[7] = 18; mirror[18] = 7;
    mirror[8] = 19; mirror[19] = 8;
    mirror[9] = 20; mirror[20] = 9;
    mirror[10] = 21; mirror[21] = 10;
  }

  if (TEAM == 1 || TEAM == 2) return team_pattern_clauses();
  else if (TEAM == 3 || TEAM == 4) return pattern_set_clauses();
  else if (TEAM == 9) return acc_match_clauses();
  else if (TEAM == 11) return bigten_match_clauses();
  else if (TEAM == 10) return acc_clauses();
  else return bigten_clauses();
}

int pattern_set_clauses ()
     /* return 1 if an empty clause is found; otherwise, 0 */
{
  int cl_arr [ MAX_ATOM ], sign_arr [ MAX_ATOM ];
  int i, j, k, x, y, z, u;
  int pattern = PATTERNSIZE;

  char *name = "patterns";
  Input_sqs = fopen(name, "r");
  if (Input_sqs == NULL) {
    printf("File %s doesn't exist!\n", name);
    exit(0);
  }

  for (i = 0; i < pattern; i++)
    for (j = 0; j < DAY; j++) {
      if (fscanf(Input_sqs, "%d", &x) == EOF) pattern = i;
      else pat[i][j] = x;
    }
  printf("Read in %d patterns\n", pattern);
  Max_atom = pattern;

  for (i = 0; i < pattern; i++)
    for (j = i+1; j < pattern; j++) {
      int nogame = 0;
      for (x = 0; (nogame == 0) && x < DAY; x++) {
	y = pat[i][x] + pat[j][x];
	if (y == 0) nogame = 1;
	else if (y == 3) nogame = 2;
      }
      if (nogame < 2) {
	if (insert_cl_2(X(j),
			X(i),
			0, cl_arr, sign_arr)) return 1;
      }
    }
  
  /* subsumed by the above; only one bye in each set.
  for (u = 0; u < DAY; u++) 
    for (i = 0; i < pattern; i++) if (pat[i][u] == 0) {
      for (j = i+1; j < pattern; j++) if (pat[j][u] == 0) {
	if (insert_cl_2(X(j),
			X(i),
			0, cl_arr, sign_arr)) return 1;
      }	
      i = pattern;
    }
  */

  if (QUEEN == 0) {

  if (TEAM == 3) {
    for (u = 0; u < DAY; u++) {
      /* no more than 4 home games */
      for (i = 0; i < pattern-4; i++) if (pat[i][u] == 2)
	for (j = i+1; j < pattern-3; j++) if (pat[j][u] == 2)
	  for (x = j+1; x < pattern-2; x++) if (pat[x][u] == 2)
	    for (y = x+1; y < pattern-1; y++) if (pat[y][u] == 2)
	      for (z = y+1; z < pattern; z++) if (pat[z][u] == 2) {
		if (insert_cl_5(
				X(z),
				X(y),
				X(x),
				X(j),
				X(i),
				0, cl_arr, sign_arr))
		  return 1;
	      }
    
      /* no more than 4 away games */
      for (i = 0; i < pattern-4; i++) if (pat[i][u] == 1)
	for (j = i+1; j < pattern-3; j++) if (pat[j][u] == 1)
	  for (x = j+1; x < pattern-2; x++) if (pat[x][u] == 1)
	    for (y = x+1; y < pattern-1; y++) if (pat[y][u] == 1)
	      for (z = y+1; z < pattern; z++) if (pat[z][u] == 1) {
		if (insert_cl_5(
				X(z),
				X(y),
				X(x),
				X(j),
				X(i),
				0, cl_arr, sign_arr))
		  return 1;
	      }
    }
  } else { /* TEAM == 4 */

    for (u = 0; u < DAY; u++) {
      /* no more than 5 home games */
      for (k = 0; k < pattern-5; k++) if (pat[k][u] == 2) 
	for (i = k+1; i < pattern-4; i++) if (pat[i][u] == 2)
	  for (j = i+1; j < pattern-3; j++) if (pat[j][u] == 2)
	    for (x = j+1; x < pattern-2; x++) if (pat[x][u] == 2)
	      for (y = x+1; y < pattern-1; y++) if (pat[y][u] == 2)
		for (z = y+1; z < pattern; z++) if (pat[z][u] == 2) {
		  if (insert_cl_6(
				  X(z),
				  X(y),
				  X(x),
				  X(j),
				  X(i),
				  X(k),
				  0, cl_arr, sign_arr))
		    return 1;
		}
    
      /* no more than 5 away games */
      for (k = 0; k < pattern-5; k++) if (pat[k][u] == 1) 
	for (i = k+1; i < pattern-4; i++) if (pat[i][u] == 1)
	  for (j = i+1; j < pattern-3; j++) if (pat[j][u] == 1)
	    for (x = j+1; x < pattern-2; x++) if (pat[x][u] == 1)
	      for (y = x+1; y < pattern-1; y++) if (pat[y][u] == 1)
		for (z = y+1; z < pattern; z++) if (pat[z][u] == 1) {
		  if (insert_cl_6(
				  X(z),
				  X(y),
				  X(x),
				  X(j),
				  X(i),
				  X(k),
				  0, cl_arr, sign_arr))
		    return 1;
		}
    }
  }
  } /* QUEEN */
      
  /* how to specify exactly TEAM of variables are true? */
  for (x = 0; x < DAY; x++) {
    i = 0;
    for (y = pattern-1; y >= 0; y--) if (pat[y][x] == 0) {
      cl_arr[i] = X(y);
      sign_arr[cl_arr[i++]] = 1;
    }
    Clause_num++;
    if (insert_clause ( cl_arr, sign_arr, i) == 1)	
      return 1;
  }
  return 0;
}

int team_pattern_clauses ()
     /* return 1 if an empty clause is found; otherwise, 0 */
{
  int cl_arr [ MAX_ATOM ], sign_arr [ MAX_ATOM ];
  int m, x, y, u, v, w, z;

  if (TRACE > 2) 
    for (x = 0; x < DAY; x++) {
      printf("A(%d) = %d, H(%d) = %d, B(%d) = %d\n", 
	     x, A(x), x, H(x), x, B(x));
    }

  /* A(x) or H(x) or B(x), but not both */
  for (x = 0; x < DAY; x++) {
    if (insert_cl_2(H(x), A(x), 0, cl_arr, sign_arr)) return 1;
    if (insert_cl_2(B(x), A(x), 0, cl_arr, sign_arr)) return 1;
    if (insert_cl_2(B(x), H(x), 0, cl_arr, sign_arr)) return 1;
  }

  /* Only one bye in weekday and one in weekend */
  for (x = 0; x < DAY; x++) 
    for (y = x+2; y < DAY; y +=2) 
      if (insert_cl_2(B(y), B(x), 0, cl_arr, sign_arr)) return 1;

  /* 1. Mirroring */
  for (x = 0; x < DAY; x++) {
    if (insert_cl_2(H(x), A(mirror[x]), 1, cl_arr, sign_arr)) return 1;
    if (insert_cl_2(H(mirror[x]), A(x), 1, cl_arr, sign_arr)) return 1;
    if (insert_cl_2(B(mirror[x]), B(x), 1, cl_arr, sign_arr)) return 1;
  }

  /* No two final away games */
  if (insert_cl_2(A(17), A(16), 0, cl_arr, sign_arr)) return 1;

  if (RESTRICT % 2) {
    /* b0+a17 < 2 or -a0 & -h0 => -a17 */
    if (insert_cl_2(B(0), A(17), 0, cl_arr, sign_arr)) return 1;

    /* b15+a17 < 2 or -a15 & -h15 => -a17 */
    if (insert_cl_2(B(15), A(17), 0, cl_arr, sign_arr)) return 1;

    /* b0+h16 < 2 or -a0 & -h0 => -a16 */
    if (insert_cl_2(B(0), H(16), 0, cl_arr, sign_arr)) return 1;
  }

  /* patterns of the last four games */
  if (DAY == 22) {
    /* b + + - */
    if (insert_cl_2(B(18), H(19), 1, cl_arr, sign_arr)) return 1;
    if (insert_cl_2(B(18), H(20), 1, cl_arr, sign_arr)) return 1;
    if (insert_cl_2(B(18), A(21), 1, cl_arr, sign_arr)) return 1;
       
    /* + b - + */
    if (insert_cl_2(B(19), H(18), 1, cl_arr, sign_arr)) return 1;
    if (insert_cl_2(B(19), A(20), 1, cl_arr, sign_arr)) return 1;
    if (insert_cl_2(B(19), H(21), 1, cl_arr, sign_arr)) return 1;

    /* - + b - */
    if (insert_cl_2(B(20), A(18), 1, cl_arr, sign_arr)) return 1;
    if (insert_cl_2(B(20), H(19), 1, cl_arr, sign_arr)) return 1;
    if (insert_cl_2(B(20), A(21), 1, cl_arr, sign_arr)) return 1;

    /* + - - b */
    if (insert_cl_2(B(21), H(18), 1, cl_arr, sign_arr)) return 1;
    if (insert_cl_2(B(21), A(19), 1, cl_arr, sign_arr)) return 1;
    if (insert_cl_2(B(21), A(20), 1, cl_arr, sign_arr)) return 1;

    /* a18+a20 < 2, h18+h20 < 2, a19+a21 < 2, h19+h21 < 2 */
    if (insert_cl_2(A(20), A(18), 0, cl_arr, sign_arr)) return 1;
    if (insert_cl_2(H(20), H(18), 0, cl_arr, sign_arr)) return 1;
    if (insert_cl_2(A(21), A(19), 0, cl_arr, sign_arr)) return 1;
    if (insert_cl_2(H(21), H(19), 0, cl_arr, sign_arr)) return 1;
  }

  /* H(x) or A(x) or B(x) */
  for (x = 0; x < DAY; x++) {
    cl_arr[0] = B(x);
    sign_arr[cl_arr[0]] = 1;
    cl_arr[1] = H(x);
    sign_arr[cl_arr[1]] = 1;
    cl_arr[2] = A(x);
    sign_arr[cl_arr[2]] = 1;
    Clause_num++;
    if (insert_clause ( cl_arr, sign_arr, 3) == 1)	
      return 1;
  }
  
  if (RESTRICT < 100) {
    /* h0+h1+h2 >= 1 */
    cl_arr[0] = H(2);
    sign_arr[cl_arr[0]] = 1;
    cl_arr[1] = H(1);
    sign_arr[cl_arr[1]] = 1;
    cl_arr[2] = H(0);
    sign_arr[cl_arr[2]] = 1;
    Clause_num++;
    if (insert_clause ( cl_arr, sign_arr, 3) == 1)	
      return 1;

    /* h15+h16+h17 >= 1 */
    cl_arr[0] = H(17);
    sign_arr[cl_arr[0]] = 1;
    cl_arr[1] = H(16);
    sign_arr[cl_arr[1]] = 1;
    cl_arr[2] = H(15);
    sign_arr[cl_arr[2]] = 1;
    Clause_num++;
    if (insert_clause ( cl_arr, sign_arr, 3) == 1)	
      return 1;
  }

  if (RESTRICT/10 > 0) {
    /* no three games without a home/road game */
    for (x = 0; x < DAY-2; x++) {
      if (insert_cl_all_3(H(x+2), H(x), A(x+1), 1, cl_arr, sign_arr)) return 1;
      if (insert_cl_all_3(A(x+2), A(x), H(x+1), 1, cl_arr, sign_arr)) return 1;
    }
  } else 
    /* no three consecutive  home/away games */
    for (x = 0; x < DAY-2; x++) {
      if (insert_cl_all_3(H(x+2), H(x+1), H(x), 0, cl_arr, sign_arr)) return 1;
      if (insert_cl_all_3(A(x+2), A(x+1), A(x), 0, cl_arr, sign_arr)) return 1;
    }

  /* no four consecutive days without a home game */
  for (x = 0; x < 15; x++) {
    cl_arr[0] = H(x+3);
    sign_arr[cl_arr[0]] = 1;
    cl_arr[1] = H(x+2);
    sign_arr[cl_arr[1]] = 1;
    cl_arr[2] = H(x+1);
    sign_arr[cl_arr[2]] = 1;
    cl_arr[3] = H(x);
    sign_arr[cl_arr[3]] = 1;
    Clause_num++;
    if (insert_clause(cl_arr, sign_arr, 4) == 1) return 1;
  }

  if (RESTRICT > 1 && RESTRICT < 4) {
    /* no four consecutive days without an away game */
    for (x = 0; x < 15; x++) {
      cl_arr[0] = A(x+3);
      sign_arr[cl_arr[0]] = 1;
      cl_arr[1] = A(x+2);
      sign_arr[cl_arr[1]] = 1;
      cl_arr[2] = A(x+1);
      sign_arr[cl_arr[2]] = 1;
      cl_arr[3] = A(x);
      sign_arr[cl_arr[3]] = 1;
      Clause_num++;
      if (insert_clause(cl_arr, sign_arr, 4) == 1) return 1;
    }
  } else if (RESTRICT > 3) {
    /* no four away games in five days */
    for (x = 0; x < DAY-4; x++) {
      if (insert_cl_4(A(x+4), A(x+3), A(x+1), A(x), 0, cl_arr, sign_arr)) 
	return 1;
    }

    /* no four home games in five days */
    for (x = 0; x < DAY-3; x++) {
      if (insert_cl_4(H(x+4), H(x+3), H(x+1), H(x), 0, cl_arr, sign_arr)) 
	return 1;
    }

    if (RESTRICT%10 > 5) 
      /* no four consecutive days without an away game */
      for (x = 0; x < 15; x++) {
	cl_arr[0] = A(x+3);
	sign_arr[cl_arr[0]] = 1;
	cl_arr[1] = A(x+2);
	sign_arr[cl_arr[1]] = 1;
	cl_arr[2] = A(x+1);
	sign_arr[cl_arr[2]] = 1;
	cl_arr[3] = A(x);
	sign_arr[cl_arr[3]] = 1;
	Clause_num++;
	if (insert_clause(cl_arr, sign_arr, 4) == 1) return 1;
      }

  } else {
    /* no five consecutive days without an away game */
    for (x = 0; x < 14; x++) {
      cl_arr[0] = A(x+4);
      sign_arr[cl_arr[0]] = 1;
      cl_arr[1] = A(x+3);
      sign_arr[cl_arr[1]] = 1;
      cl_arr[2] = A(x+2);
      sign_arr[cl_arr[2]] = 1;
      cl_arr[3] = A(x+1);
      sign_arr[cl_arr[3]] = 1;
      cl_arr[4] = A(x);
      sign_arr[cl_arr[4]] = 1;
      Clause_num++;
      if (insert_clause(cl_arr, sign_arr, 5) == 1) return 1;
    }
  }

  /* 5. First Weekends.
     No more than three away games in the first five weekends */
  for (z = 1; z < 4; z += 2) 
    for (y = z+2; y < 6; y += 2)
      for (w = y+2; w < 8; w += 2)
	for (v = w+2; v < 10; v += 2) {
	  if (insert_cl_4(
			  A(v),
			  A(w), 
			  A(y),
			  A(z),
			  0, cl_arr, sign_arr))
	    return 1;
	}

  /* same number of home/away games on weekdays and weekends */
  if (DAY == 22) {
  for (m = 0; m < 2; m++)
  for (x = m; x < DAY-10; x+=2)
    for (z = x+2; z < DAY-8; z += 2) 
      for (y = z+2; y < DAY-6; y += 2)
	for (w = y+2; w < DAY-4; w += 2)
	  for (v = w+2; v < DAY-2; v += 2)
	    for (u = v+2; u < DAY; u += 2) {
	      if (insert_cl_6(
			      H(u),
			      H(v),
			      H(w), 
			      H(y),
			      H(z),
			      H(x),
			      0, cl_arr, sign_arr))
		return 1;
	      if (insert_cl_6(
			      A(u),
			      A(v),
			      A(w), 
			      A(y),
			      A(z),
			      A(x),
			      0, cl_arr, sign_arr))
		return 1;
	    }
  } else if (DAY == 18) {
    for (m = 0; m < 2; m++)
    for (z = m; z < DAY-8; z += 2) 
      for (y = z+2; y < DAY-6; y += 2)
	for (w = y+2; w < DAY-4; w += 2)
	  for (v = w+2; v < DAY-2; v += 2)
	    for (u = v+2; u < DAY; u += 2) {
	      if (insert_cl_5(
			      H(u),
			      H(v),
			      H(w), 
			      H(y),
			      H(z),
			      0, cl_arr, sign_arr))
		return 1;
	      if (insert_cl_5(
			      A(u),
			      A(v),
			      A(w), 
			      A(y),
			      A(z),
			      0, cl_arr, sign_arr))
		return 1;
	    }
  }
  return 0;
}

int acc_match_clauses ()
     /* return 1 if an empty clause is found; otherwise, 0 */
{
  int cl_arr [ MAX_ATOM ], sign_arr [ MAX_ATOM ];
  int i, j, x, y, z, u, v;
  int set[NINE];
  char *name;
  SIZE = TEAM * TEAM * DAY; 

  name = "patset";
  Input_sqs = fopen(name, "r");
  if (Input_sqs == NULL) {
    printf("File %s doesn't exist!\n", name);
    exit(0);
  }
  for (i = 1; i <= QUEEN; i++)
    for (j = 0; j < TEAM; j++) {
      if (fscanf(Input_sqs, "%d", &x) == EOF) 
	{ printf("Data incomplete in %s\n", name); exit(0); }
      if (i == QUEEN) set[j] = x;
    }

  name = "patterns";
  Input_sqs = fopen(name, "r");
  if (Input_sqs == NULL) {
    printf("File %s doesn't exist!\n", name);
    exit(0);
  }
  y = 0;
  for (i = 0; y < TEAM; i++)
    if (i == set[y]) {
      for (j = 0; j < DAY; j++) {
	if (fscanf(Input_sqs, "%d", &x) == EOF) 
	  { printf("Data incomplete in %s\n", name); exit(0); }
	pat[y][j] = x;
      }
      y++;
    } else
      for (j = 0; j < DAY; j++) {
	if (fscanf(Input_sqs, "%d", &x) == EOF) 
	  { printf("Data incomplete in %s\n", name); exit(0); }
      }

  printf("\nPattern set:\n");
  for (j = 0; j < TEAM; j++) {
    printf("\n %d: ", j);
    for (i = 0; i < DAY; i++) printf(" %d ", pat[j][i]);
  }     
  printf("\n\n");

  /* 6. Rivaries in the last day */
  for (x = 0; x < TEAM; x++) if (x != FSU) {
    if (x != Clem) {
      if (insert_cl_1(GAME(GT, x, 17), FF)) return 1; 
      if (insert_cl_1(GAME(x, GT, 17), FF)) return 1; 
    }
    if (x != GT) {
      if (insert_cl_1(GAME(Clem, x, 17), FF)) return 1; 
      if (insert_cl_1(GAME(x, Clem, 17), FF)) return 1; 
    }
    if (x != UMD) {
      if (insert_cl_1(GAME(UVA, x, 17), FF)) return 1; 
      if (insert_cl_1(GAME(x, UVA, 17), FF)) return 1; 
    }
    if (x != UVA) {
      if (insert_cl_1(GAME(UMD, x, 17), FF)) return 1; 
      if (insert_cl_1(GAME(x, UMD, 17), FF)) return 1; 
    }
    if (x != NCS) {
      if (insert_cl_1(GAME(Wake, x, 17), FF)) return 1; 
      if (insert_cl_1(GAME(x, Wake, 17), FF)) return 1; 
    }
    if (x != Wake) {
      if (insert_cl_1(GAME(NCS, x, 17), FF)) return 1; 
      if (insert_cl_1(GAME(x, NCS, 17), FF)) return 1; 
    }
  }

  /* 9. Idiosyncratic criteria */
  /* UNC plays Duke in the last day at Duke */
  if (insert_cl_1(GAME(Duke, UNC, 17), TT)) return 1;
  for (i = 0; i < TEAM; i++) {
    /* Duke has a bye on day 16 */
    if (pat[i][15] == 0) {
      if (insert_cl_1(PI(Duke, i), TT)) return 1;
    }
    /* Wake has a bye on day 1 */
    if (pat[i][0] == 0) {
      if (insert_cl_1(PI(Wake, i), TT)) return 1;  
    }
    /* Wake doesn't have a home game on day 17 */
    if (pat[i][16] == 2) {
      if (insert_cl_1(PI(Wake, i), FF)) return 1;  
    }

    /* UNC plays Duke in the last day and day 11 */
    if (pat[i][17] != 2) {
      if (insert_cl_1(PI(Duke, i), FF)) return 1;  
    }
    if (pat[i][17] != 1) {
      if (insert_cl_1(PI(UNC, i), FF)) return 1;  
    }

    /* Clem, UMD, and Wake do not play away on day 18 */
    if (pat[i][17] == 1) {
      if (insert_cl_1(PI(Clem, i), FF)) return 1;
      if (insert_cl_1(PI(UMD, i), FF)) return 1;
      if (insert_cl_1(PI(Wake, i), FF)) return 1;
    }

    /* Clem, Duke, UMD and Wake do not play away on day 1 */
    if (pat[i][0] == 1) {
      if (insert_cl_1(PI(Clem, i), FF)) return 1;
      if (insert_cl_1(PI(Duke, i), FF)) return 1;
      if (insert_cl_1(PI(UMD, i), FF)) return 1;
      if (insert_cl_1(PI(Wake, i), FF)) return 1;
    }

    /* UNC plays Clem in the second day */
    if (pat[i][1] == 0) {
      if (insert_cl_1(PI(Clem, i), FF)) return 1;
      if (insert_cl_1(PI(UNC, i), FF)) return 1;
    }

    /* FSU, NCS doesn't have a bye on last day */
    if (pat[i][17] == 0) {
      if (insert_cl_1(PI(FSU, i), FF)) return 1;
      if (insert_cl_1(PI(NCS, i), FF)) return 1;
    }

    /* UNC doesn't have a bye on first day */
    if (pat[i][0] == 0) {
      if (insert_cl_1(PI(UNC, i), FF)) return 1;
    }

  }

  /* UNC plays Clem in the second day */
  for (x = 0; x < TEAM; x++) {
    if (x != Clem) {
      if (insert_cl_1(GAME(UNC, x, 1), FF)) return 1; 
      if (insert_cl_1(GAME(x, UNC, 1), FF)) return 1; 
    }
    if (x != UNC) {
      if (insert_cl_1(GAME(Clem, x, 1), FF)) return 1; 
      if (insert_cl_1(GAME(x, Clem, 1), FF)) return 1; 
    }
  }
  cl_arr[0] = GAME(Clem, UNC, 1);
  sign_arr[cl_arr[0]] = 1;
  cl_arr[1] = GAME(UNC, Clem, 1);
  sign_arr[cl_arr[1]] = 1;
  Clause_num++;
  if (insert_clause ( cl_arr, sign_arr, 2) == 1)	
    return 1;

  for (z = 0; z < DAY; z++)
    for (x = 0; x < TEAM; x++) 
      for (y = x+1; y < TEAM; y++) {
	if (insert_cl_2(GAME(x, y, z),
			GAME(y, x, mirror[z]), 
			1, cl_arr, sign_arr)) return 1;
    }

  /* GAME rules */
  for (x = 0; x < TEAM; x++) 
    for (y = 0; y < TEAM; y++) 
      for (z = 0; z < DAY; z++) {

	/* each team plays another team at home at most once */
	for (u = z+1; u < DAY; u++) {
	  if (insert_cl_2(GAME(x, y, z),
			  GAME(x, y, u), 
			  0, cl_arr, sign_arr)) return 1;
	}

	/* a team can play at most once at one slot */
	for (u = 0; u < TEAM; u++) if (u != y) {
	  if (insert_cl_2(GAME(x, y, z),
			  GAME(x, u, z), 
			  0, cl_arr, sign_arr)) return 1;
	  if (insert_cl_2(GAME(y, x, z),
			  GAME(u, x, z), 
			  0, cl_arr, sign_arr)) return 1; 
	  if (insert_cl_2(GAME(x, y, z),
			  GAME(u, x, z), 
			  0, cl_arr, sign_arr)) return 1;
	}
      }

  /* relation between PI and GAME */
  for (i = 0; i < TEAM; i++) 
    for (z = 0; z < DAY; z++) {
      if (pat[i][z] == 0) {
	for (x = 0; x < TEAM; x++)
	  for (y = 0; y < TEAM; y++) {
	    if (insert_cl_2(PI(x, i), 
			    GAME(x, y, z),
			    0, cl_arr, sign_arr)) return 1;
	    if (insert_cl_2(PI(x, i), 
			    GAME(y, x, z),
			    0, cl_arr, sign_arr)) return 1;
	  }
      } else if (pat[i][z] == 1) {
	for (x = 0; x < TEAM; x++)
	  for (y = 0; y < TEAM; y++) {
	    if (insert_cl_2(PI(x, i), 
			    GAME(x, y, z),
			    0, cl_arr, sign_arr)) return 1;
	  }
      } else {
	for (x = 0; x < TEAM; x++)
	  for (y = 0; y < TEAM; y++) {
	    if (insert_cl_2(PI(x, i), 
			    GAME(y, x, z),
			    0, cl_arr, sign_arr)) return 1;
	  }
      }
    }
  
  /* PI cannot be all true */
  for (x = 0; x < TEAM; x++) 
    for (y = x+1; y < TEAM; y++) 
      for (z = TEAM-1; z >= 0; z--) {
	if (insert_cl_2(PI(y, z),
			PI(x, z), 
			0, cl_arr, sign_arr)) return 1;
	if (insert_cl_2(PI(z, y),
			PI(z, x), 
			0, cl_arr, sign_arr)) return 1;
      }

  /* 8. Opponent Sequence */
  for (x = 0; x < TEAM; x++) if (x != Duke && x != UNC) 
    for (z = 0; z < DAY-1; z++) {
      if (insert_cl_2(GAME(Duke, x, z),
		      GAME(UNC, x, z+1), 
		      0, cl_arr, sign_arr)) return 1;
      if (insert_cl_2(GAME(UNC, x, z),
		      GAME(Duke, x, z+1), 
		      0, cl_arr, sign_arr)) return 1;
    }

  for (x = 0; x < TEAM; x++) if (x != Duke && x != UNC && x != Wake) 
    for (y = 0; y < TEAM; y++) if (y == Duke || y == UNC || y == Wake)
      for (u = 0; u < TEAM; u++) 
	if (u != y && (u == Duke || u == UNC || u == Wake))
	for (v = 0; v < TEAM; v++) 
	  if (v != u && v != y && (v == Duke || v == UNC || v == Wake))
	  for (z = 0; z < DAY-2; z++) {
	    if (insert_cl_all_3(GAME(y, x, z+2),
				GAME(x, u, z+1), 
				GAME(x, v, z), 
				0, cl_arr, sign_arr)) return 1;
	    if (insert_cl_all_3(GAME(x, y, z+2),
				GAME(u, x, z+1), 
				GAME(x, v, z), 
				0, cl_arr, sign_arr)) return 1;
	    if (insert_cl_all_3(GAME(x, y, z+2),
				GAME(x, u, z+1), 
				GAME(v, x, z), 
				0, cl_arr, sign_arr)) return 1;
	    if (insert_cl_all_3(GAME(y, x, z+2),
				GAME(u, x, z+1), 
				GAME(x, v, z), 
				0, cl_arr, sign_arr)) return 1;
	    if (insert_cl_all_3(GAME(y, x, z+2),
				GAME(x, u, z+1), 
				GAME(v, x, z), 
				0, cl_arr, sign_arr)) return 1;
	    if (insert_cl_all_3(GAME(x, y, z+2),
				GAME(u, x, z+1), 
				GAME(v, x, z), 
				0, cl_arr, sign_arr)) return 1;
	  }

  /* PI cannot be false */
  for (x = 0; x < TEAM; x++) {
    for (v = TEAM-1; v >= 0; v--) {
      cl_arr[v] = PI(x, v);
      sign_arr[cl_arr[v]] = 1;
    }
    Clause_num++;
    if (insert_clause(cl_arr, sign_arr, TEAM) == 1)	
      return 1;

    for (v = TEAM-1; v >= 0; v--) {
      cl_arr[v] = PI(v, x);
      sign_arr[cl_arr[v]] = 1;
    }
    Clause_num++;
    if (insert_clause(cl_arr, sign_arr, TEAM) == 1)	
      return 1;
  }

  /* a game must be played between x and y */
  for (x = 0; x < TEAM; x++) {
    for (y = 0; y < TEAM; y++) if (y != x) {
      for (z = 0; z < DAY; z++) {
	cl_arr[z] = GAME(x, y, z);
	sign_arr[cl_arr[z]] = 1;
      }
      Clause_num++;
      if (insert_clause ( cl_arr, sign_arr, DAY) == 1)	
	return 1;
    }
  }

  return 0;
}

int bigten_match_clauses ()
     /* return 1 if an empty clause is found; otherwise, 0 */
{
  int cl_arr [ MAX_ATOM ], sign_arr [ MAX_ATOM ];
  int i, j, x, y, z, u, v;
  int set[11];
  char *name;
  SIZE = TEAM * TEAM * DAY; 

  if (TRACE > 8 || TRACE == 4) {
    for (i = 0; i < TEAM; i++)
      for (j = 0; j < TEAM; j++)
	for (z = 0; z < DAY; z++)
	  printf("GAME(%d, %d, %d) = %d\n", i, j, z, GAME(i, j, z));
    for (i = 0; i < TEAM; i++)
      for (j = 0; j < TEAM; j++)
	printf("PI(%d, %d) = %d\n", i, j, PI(i, j));
  }

  name = "patset";
  Input_sqs = fopen(name, "r");
  if (Input_sqs == NULL) {
    printf("File %s doesn't exist!\n", name);
    exit(0);
  }
  for (i = 1; i <= QUEEN; i++)
    for (j = 0; j < TEAM; j++) {
      if (fscanf(Input_sqs, "%d", &x) == EOF) 
	{ printf("Data incomplete\n"); exit(0); }
      if (i == QUEEN) set[j] = x;
    }
  fclose(Input_sqs);

  name = "patterns";
  Input_sqs = fopen(name, "r");
  if (Input_sqs == NULL) {
    printf("File %s doesn't exist!\n", name);
    exit(0);
  }
  y = 0;
  for (i = 0; y < TEAM; i++)
    if (i == set[y]) {
      for (j = 0; j < DAY; j++) {
	if (fscanf(Input_sqs, "%d", &x) == EOF) 
	  { printf("Data incomplete\n"); exit(0); }
	pat[y][j] = x;
      }
      y++;
    } else
      for (j = 0; j < DAY; j++) {
	if (fscanf(Input_sqs, "%d", &x) == EOF) 
	  { printf("Data incomplete\n"); exit(0); }
      }
  fclose(Input_sqs);

  printf("\nPattern set:\n");
  for (j = 0; j < TEAM; j++) {
    printf("\n %d: ", j);
    for (i = 0; i < DAY; i++) printf(" %d ", pat[j][i]);
  }     
  printf("\n\n");

  /* x doesn't play x */
  for (x = 0; x < TEAM; x++) 
    for (z = 0; z < DAY; z++) {
      if (insert_cl_1(GAME(x, x, z), FF)) return 1;
    }

  /* 9. Idiosyncratic criteria */
  /* Some teams have a bye for nonconference games */
  for (i = 0; i < TEAM; i++) { 
    if (LINE % 2) {
      if (insert_cl_1(PI(i, i), TT)) return 1; 
    } else {
      /* Ohio Sate not available on Day 2 
	 if (pat[i][2] == 0) if (insert_cl_1(PI(Ohi, i), TT)) return 1; */
    }
  }

  /* Dropped games */
  if (PIGEON) {
    int h[4];
    name = "bigten.four";
    Input_sqs = fopen(name, "r");
    if (Input_sqs == NULL) {
      printf("File %s doesn't exist!\n", name);
      exit(0);
    }
    for (i = 1; i <= PIGEON; i++) for (j = 0; j < 4; j++) {
      if (fscanf(Input_sqs, "%d", &x) == EOF) 
	{ printf("Data incomplete\n"); exit(0); }
      if (i == PIGEON) h[j] = x;
    }
    fclose(Input_sqs);
    printf("No %d at %d and %d at %d in the last four days\n", 
	   h[0], h[2], h[1], h[3]);

    /* h[0] vs h[2], h[1] vs h[3]: no play in days 18-21 */
    for (z = 18; z < 22; z++) {
      if (insert_cl_1(GAME(h[0], h[2], z), FF)) return 1; 
      if (insert_cl_1(GAME(h[2], h[0], z), FF)) return 1; 
      if (insert_cl_1(GAME(h[1], h[3], z), FF)) return 1; 
      if (insert_cl_1(GAME(h[3], h[1], z), FF)) return 1; 
    }      
    /* no weekend game for h[0] at h[2] */
    for (z = 1; z < 18; z += 2) {
      if (insert_cl_1(GAME(h[2], h[0], z), FF)) return 1; 
      if (insert_cl_1(GAME(h[1], h[3], z), FF)) return 1; 
    }
    /* no week day game for h[1] at h[3] */
    for (z = 0; z < 18; z += 2) {
      if (insert_cl_1(GAME(h[0], h[2], z), FF)) return 1; 
      if (insert_cl_1(GAME(h[3], h[1], z), FF)) return 1; 
    }

    name = "bigten.missed";
    Input_sqs = fopen(name, "r");
    if (Input_sqs == NULL) {
      printf("File %s doesn't exist!\n", name);
      exit(0);
    }

    for (x = 0; x < TEAM; x++) for (u = 0; u < 2; u++) {
      if (fscanf(Input_sqs, "%d", &y) == EOF) 
	{ printf("Data incomplete\n"); exit(0); }
      y--;

      /* x plays y either in Day 18-21 or 
	 x = h[2] and y = h[0] or
	 x = h[3] and y = h[1])  */

      for (x = 0; x < TEAM; x++)
	for (y = 0; y < TEAM; y++) if (x != y) {
	  if ((x == h[2] && y == h[0]) ||
	      (x == h[3] && y == h[1]))
	    ;
	  else 
	    /* no (x, y) home games in Days 0-17 */
	    for (z = 0; z < 18; z++) 
	      if (insert_cl_1(GAME(x, y, z), FF)) return 1;
	}
    }
    fclose(Input_sqs);
  }

  /* 6. Rivaries in the last day */
  if ((LINE/100) % 2)
  for (x = 0; x < TEAM; x++) if (x != Nor) {

    if (x != Ill) {
      if (insert_cl_1(GAME(Iow, x, 17), FF)) return 1; 
      if (insert_cl_1(GAME(x, Iow, 17), FF)) return 1; 
    }
    if (x != Iow) {
      if (insert_cl_1(GAME(Ill, x, 17), FF)) return 1; 
      if (insert_cl_1(GAME(x, Ill, 17), FF)) return 1; 
    }
    
    if (x != Mic) {
      if (insert_cl_1(GAME(MiS, x, 17), FF)) return 1; 
      if (insert_cl_1(GAME(x, MiS, 17), FF)) return 1; 
    }
    if (x != MiS) {
      if (insert_cl_1(GAME(Mic, x, 17), FF)) return 1; 
      if (insert_cl_1(GAME(x, Mic, 17), FF)) return 1; 
    }

    if (x != Ind) {
      if (insert_cl_1(GAME(Pur, x, 17), FF)) return 1; 
      if (insert_cl_1(GAME(x, Pur, 17), FF)) return 1; 
    }
    if (x != Pur) {
      if (insert_cl_1(GAME(Ind, x, 17), FF)) return 1; 
      if (insert_cl_1(GAME(x, Ind, 17), FF)) return 1; 
    }

    if (x != Min) {
      if (insert_cl_1(GAME(Wis, x, 17), FF)) return 1; 
      if (insert_cl_1(GAME(x, Wis, 17), FF)) return 1; 
    }
    if (x != Wis) {
      if (insert_cl_1(GAME(Min, x, 17), FF)) return 1; 
      if (insert_cl_1(GAME(x, Min, 17), FF)) return 1; 
    }

    if (x != Ohi) {
      if (insert_cl_1(GAME(Pen, x, 17), FF)) return 1; 
      if (insert_cl_1(GAME(x, Pen, 17), FF)) return 1; 
    }
    if (x != Pen) {
      if (insert_cl_1(GAME(Ohi, x, 17), FF)) return 1; 
      if (insert_cl_1(GAME(x, Ohi, 17), FF)) return 1; 
    }
  } 

  /* 1. Mirroring: */
  for (z = 0; z < DAY; z++)
    for (x = 0; x < TEAM; x++) 
      for (y = x+1; y < TEAM; y++) {
	if (insert_cl_2(GAME(x, y, z),
			GAME(y, x, mirror[z]), 
			1, cl_arr, sign_arr)) return 1;
    }

  /* GAME rules */
  for (x = 0; x < TEAM; x++) 
    for (y = 0; y < TEAM; y++) 
      for (z = 0; z < DAY; z++) {

	/* each team plays another team at home at most once */
	for (u = z+1; u < DAY; u++) {
	  if (insert_cl_2(GAME(x, y, z),
			  GAME(x, y, u), 
			  0, cl_arr, sign_arr)) return 1;
	}

	/* a team can play at most once at one slot */
	for (u = 0; u < TEAM; u++) if (u != y) {
	  if (insert_cl_2(GAME(x, y, z),
			  GAME(x, u, z), 
			  0, cl_arr, sign_arr)) return 1;
	  if (insert_cl_2(GAME(y, x, z),
			  GAME(u, x, z), 
			  0, cl_arr, sign_arr)) return 1; 
	  if (insert_cl_2(GAME(x, y, z),
			  GAME(u, x, z), 
			  0, cl_arr, sign_arr)) return 1;
	}
      }

  /* relation between PI and GAME */
  for (i = 0; i < TEAM; i++) 
    for (z = 0; z < DAY; z++) {
      if (pat[i][z] == 0) {
	for (x = 0; x < TEAM; x++)
	  for (y = 0; y < TEAM; y++) {
	    if (insert_cl_2(PI(x, i), 
			    GAME(x, y, z),
			    0, cl_arr, sign_arr)) return 1;
	    if (insert_cl_2(PI(x, i), 
			    GAME(y, x, z),
			    0, cl_arr, sign_arr)) return 1;
	  }
      } else if (pat[i][z] == 1) {
	for (x = 0; x < TEAM; x++)
	  for (y = 0; y < TEAM; y++) {
	    if (insert_cl_2(PI(x, i), 
			    GAME(x, y, z),
			    0, cl_arr, sign_arr)) return 1;
	  }
      } else {
	for (x = 0; x < TEAM; x++)
	  for (y = 0; y < TEAM; y++) {
	    if (insert_cl_2(PI(x, i), 
			    GAME(y, x, z),
			    0, cl_arr, sign_arr)) return 1;
	  }
      }
    }

  /* removed games */
  if ((LINE/10) % 2) {
    int b[4];
    for (i = 0; i < TEAM; i++) 
      for (z = 18; z < 22; z++)
	if (pat[i][z] == 0) b[z-18] = i;

    for (x = 0; x < TEAM; x++)
      for (y = 0; y < TEAM; y++) {
	/* (x y) game in a weekday */
	for (z = 0; z < 18; z++) if (z < 2 || z > 15 || z % 2) {
	  if (insert_cl_all_3(PI(x, b[2]), 
			      PI(y, b[0]), 
			      GAME(x, y, z),
			      0, cl_arr, sign_arr)) return 1;
	}
	/* (x y) game in a weekend or a weekday*/
	for (z = 0; z < 18; z++) if (z < 2 || z > 15 || z % 2 == 0) {
	  if (insert_cl_all_3(PI(x, b[3]), 
			      PI(y, b[1]), 
			      GAME(x, y, z),
			      0, cl_arr, sign_arr)) return 1;
	}

	for (z = 1; z < 14; z++) {
	  if ((pat[b[0]][z-1] == 2 && pat[b[0]][z] == 2 && pat[b[0]][z+2] == 2) ||
	      (pat[b[0]][z] == 2 && pat[b[0]][z+2] == 2 && pat[b[0]][z+3] == 2) ||
	      (pat[b[2]][z-1] == 1 && pat[b[2]][z] == 1 && pat[b[2]][z+2] == 1) ||
	      (pat[b[2]][z] == 1 && pat[b[2]][z+2] == 1 && pat[b[2]][z+3] == 1)) {
	    if (insert_cl_all_3(PI(x, b[2]), 
				PI(y, b[0]), 
				GAME(x, y, z+1),
				0, cl_arr, sign_arr)) return 1;
	  }

	  if ((pat[b[1]][z-1] == 2 && pat[b[1]][z] == 2 && pat[b[1]][z+2] == 2) ||
	      (pat[b[1]][z] == 2 && pat[b[1]][z+2] == 2 && pat[b[1]][z+3] == 2) ||
	      (pat[b[3]][z-1] == 1 && pat[b[3]][z] == 1 && pat[b[3]][z+2] == 1) ||
	      (pat[b[3]][z] == 1 && pat[b[3]][z+2] == 1 && pat[b[3]][z+3] == 1)) {
	    if (insert_cl_all_3(PI(x, b[3]), 
				PI(y, b[1]), 
				GAME(x, y, z+1),
				0, cl_arr, sign_arr)) return 1;
	  }
	}
      }
  }
  
  /* PI cannot be all true */
  for (x = 0; x < TEAM; x++) 
    for (y = x+1; y < TEAM; y++) 
      for (z = TEAM-1; z >= 0; z--) {
	if (insert_cl_2(PI(y, z),
			PI(x, z), 
			0, cl_arr, sign_arr)) return 1;
	if (insert_cl_2(PI(z, y),
			PI(z, x), 
			0, cl_arr, sign_arr)) return 1;
      }

  /* 8. Opponent Sequence */
  /* no info */

  /* PI cannot be false */
  for (x = 0; x < TEAM; x++) {
    for (v = TEAM-1; v >= 0; v--) {
      cl_arr[v] = PI(x, v);
      sign_arr[cl_arr[v]] = 1;
    }
    Clause_num++;
    if (insert_clause(cl_arr, sign_arr, TEAM) == 1)	
      return 1;

    for (v = TEAM-1; v >= 0; v--) {
      cl_arr[v] = PI(v, x);
      sign_arr[cl_arr[v]] = 1;
    }
    Clause_num++;
    if (insert_clause(cl_arr, sign_arr, TEAM) == 1)	
      return 1;
  }

  /* a game must be played between x and y */
  for (x = 0; x < TEAM; x++) 
    for (y = 0; y < TEAM; y++) if (y != x) {
      for (z = 0; z < DAY; z++) {
	cl_arr[z] = GAME(x, y, z);
	sign_arr[cl_arr[z]] = 1;
      }
      Clause_num++;
      if (insert_clause ( cl_arr, sign_arr, DAY) == 1)	
	return 1;
    }
  fclose(Input_sqs);

  printf("Team = %d, Day = %d\n", TEAM, DAY);
  return 0;
}

int bigten_clauses ()
     /* return 1 if an empty clause is found; otherwise, 0 */
{
  int cl_arr [ MAX_ATOM ], sign_arr [ MAX_ATOM ];
  int n, x, y, u, v, w, z;
  char name[20];
  SIZE = TEAM * TEAM * DAY; 
  n = TEAM;

  sprintf(name, "missed%d", LINE);
  Input_sqs = fopen(name, "r");
  if (Input_sqs == NULL) {
    printf("File %s doesn't exist!\n", name);
    exit(0);
  }

  /* rivaries in the last day 
  if (insert_cl_1(GAME(0, 2, DAY-1), TT)) return 1;
  if (insert_cl_1(GAME(1, 9, DAY-1), TT)) return 1;
  if (insert_cl_1(GAME(4, 3, DAY-1), TT)) return 1;
  if (insert_cl_1(GAME(5, 10, DAY-1), TT)) return 1;
  if (insert_cl_1(GAME(7, 8, DAY-1), TT)) return 1;
  */

  /* Illinois schedule */
  if (RESTRICT % 10 > 1) {
    if (insert_cl_1(GAME(0, 5, 0), TT)) return 1;
    if (insert_cl_1(GAME(10, 0, 1), TT)) return 1;
    if (insert_cl_1(GAME(9, 0, 2), TT)) return 1;
    if (insert_cl_1(GAME(0, 3, 3), TT)) return 1;
    if (insert_cl_1(GAME(0, 2, 4), TT)) return 1;
    if (insert_cl_1(GAME(1, 0, 5), TT)) return 1;

    if (insert_cl_1(GAME(0, 10, 7), TT)) return 1;
    if (insert_cl_1(GAME(7, 0, 8), TT)) return 1;
    if (insert_cl_1(GAME(0, 4, 9), TT)) return 1;
    if (insert_cl_1(GAME(3, 0, 10), TT)) return 1;
    if (insert_cl_1(GAME(0, 9, 11), TT)) return 1;
    if (insert_cl_1(GAME(4, 0, 12), TT)) return 1;

    if (insert_cl_1(GAME(0, 8, 14), TT)) return 1;
    if (insert_cl_1(GAME(6, 0, 15), TT)) return 1;
    if (insert_cl_1(GAME(0, 1, 16), TT)) return 1;
    if (insert_cl_1(GAME(5, 0, 17), TT)) return 1;
  }

  if (RESTRICT % 10 > 2) {
    /* Michigan schedule */
    if (insert_cl_1(GAME(8, 3, 0), TT)) return 1;
    if (insert_cl_1(GAME(3, 9, 1), TT)) return 1;
    if (insert_cl_1(GAME(5, 3, 2), TT)) return 1;
    if (insert_cl_1(GAME(0, 3, 3), TT)) return 1;
    if (insert_cl_1(GAME(3, 1, 4), TT)) return 1;
    if (insert_cl_1(GAME(3, 6, 5), TT)) return 1;
    if (insert_cl_1(GAME(4, 3, 6), TT)) return 1;

    if (insert_cl_1(GAME(3, 10, 8), TT)) return 1;
    if (insert_cl_1(GAME(7, 3, 9), TT)) return 1;
    if (insert_cl_1(GAME(3, 0, 10), TT)) return 1;
    if (insert_cl_1(GAME(3, 8, 11), TT)) return 1;

    if (insert_cl_1(GAME(9, 3, 13), TT)) return 1;
    if (insert_cl_1(GAME(3, 5, 14), TT)) return 1;
    if (insert_cl_1(GAME(2, 3, 15), TT)) return 1;
    if (insert_cl_1(GAME(10, 3, 16), TT)) return 1;
    if (insert_cl_1(GAME(3, 7, 17), TT)) return 1;
  }

  if (RESTRICT % 10 > 0) {
    /* Illinois not available on Day 13 */
    if (insert_cl_1(HOME(0, 13), FF)) return 1;
    if (insert_cl_1(AWAY(0, 13), FF)) return 1;

    /* Indiana not available on Day 11 */
    if (insert_cl_1(HOME(1, 11), FF)) return 1;
    if (insert_cl_1(AWAY(1, 11), FF)) return 1;

    /* Michgan not available on Day 7 and 12 */
    /* if (insert_cl_1(HOME(3, 7), FF)) return 1;
       if (insert_cl_1(AWAY(3, 7), FF)) return 1; */
    if (insert_cl_1(HOME(3, 12), FF)) return 1;
    if (insert_cl_1(AWAY(3, 12), FF)) return 1;

    /* Northwestern not available on Day 7 */
    if (insert_cl_1(HOME(6, 7), FF)) return 1;
    if (insert_cl_1(AWAY(6, 7), FF)) return 1;

    /* Ohio Sate not available on Day 2 */
    if (insert_cl_1(HOME(7, 2), FF)) return 1;
    if (insert_cl_1(AWAY(7, 2), FF)) return 1;
    }

  for (x = 0; x < n; x++) {
    if (fscanf(Input_sqs, "%d", &u) == EOF) 
      { printf("Data incomplete\n"); exit(0); }
    if (fscanf(Input_sqs, "%d", &v) == EOF) 
      { printf("Data incomplete\n"); exit(0); }
    u--; v--;

    for (y = 0; y < n; y++) if (y == x || y == u || y == v) {
      /* no (x, y) home games */
      for (z = 0; z < DAY; z++) {
	if (insert_cl_1(GAME(x, y, z), FF)) return 1;
      }
    }
  }
  fclose(Input_sqs);

  for (x = 0; x < n; x++) 
    for (y = 0; y < n; y++) 
      for (z = 0; z < DAY; z++) {

	/* each team plays another team at home at most once */
	for (u = z+1; u < DAY; u++) {
	  if (insert_cl_2(GAME(x, y, z),
			  GAME(x, y, u), 
			  0, cl_arr, sign_arr)) return 1;
	}

	/* the two teams cannot play again in the next two games */
	for (u = z; u < z+3 && u < DAY; u++) {
	  if (insert_cl_2(GAME(x, y, z),
			  GAME(y, x, u), 
			  0, cl_arr, sign_arr)) return 1;
	}

	/* a team can play at most once at one slot */
	for (u = 0; u < n; u++) if (u != y) {
	  if (insert_cl_2(GAME(x, y, z),
			  GAME(x, u, z), 
			  0, cl_arr, sign_arr)) return 1;
	  if (insert_cl_2(GAME(y, x, z),
			  GAME(u, x, z), 
			  0, cl_arr, sign_arr)) return 1; 
	  if (insert_cl_2(GAME(x, y, z),
			  GAME(u, x, z), 
			  0, cl_arr, sign_arr)) return 1;
	}
      }

  /* relation between GAME and HOME/AWAY */
  for (x = 0; x < n; x++) 
    for (y = 0; y < n; y++) 
      for (z = 0; z < DAY; z++) {
	if (insert_cl_2(GAME(x, y, z),
			HOME(x, z), 
			1, cl_arr, sign_arr)) return 1;
	if (insert_cl_2(GAME(x, y, z),
			AWAY(y, z), 
			1, cl_arr, sign_arr)) return 1;
      }

  for (x = 0; x < n; x++) 
    for (z = 0; z < DAY-2; z++) {
      /* no three consecutive home games */
      if (insert_cl_all_3(HOME(x, z),
			  HOME(x, z+1), 
			  HOME(x, z+2),
			  0, cl_arr, sign_arr))
	return 1;

      /* no three consecutive away games */
      if (insert_cl_all_3(AWAY(x, z),
			  AWAY(x, z+1), 
			  AWAY(x, z+2),
			  0, cl_arr, sign_arr))
	return 1;
    }

  if ((RESTRICT/10) % 10 > 0) {
    /* no four home/away games in five days */
    for (x = 0; x < n; x++) 
      for (z = 0; z < DAY-4; z++) {
	if (insert_cl_4(HOME(x, z),
			HOME(x, z+1),
			HOME(x, z+3), 
			HOME(x, z+4),
			0, cl_arr, sign_arr))
	  return 1;
	if (insert_cl_4(AWAY(x, z),
			AWAY(x, z+1),
			AWAY(x, z+3), 
			AWAY(x, z+4),
			0, cl_arr, sign_arr))
	  return 1;
      }
  } else {
    /* no idle day between three home/away games */
    for (x = 0; x < n; x++) 
      for (z = 0; z < DAY-3; z++) {
	if (insert_cl_4(HOME(x, z+3),
			HOME(x, z+2),
			HOME(x, z), 
			AWAY(x, z+1),
			1, cl_arr, sign_arr))
	  return 1;
	if (insert_cl_4(AWAY(x, z+3),
			AWAY(x, z+2),
			AWAY(x, z), 
			HOME(x, z+1),
			1, cl_arr, sign_arr))
	  return 1;
	if (insert_cl_4(HOME(x, z+3),
			HOME(x, z+1),
			HOME(x, z), 
			AWAY(x, z+2),
			1, cl_arr, sign_arr))
	  return 1;
	if (insert_cl_4(AWAY(x, z+3),
			AWAY(x, z+1),
			AWAY(x, z), 
			HOME(x, z+2),
			1, cl_arr, sign_arr))
	  return 1;
      }
  }

  if ((RESTRICT/100) % 10 > 0) {
    /* same number of home/away games on weekdays and weekends */
    int s;
    for (x = 0; x < n; x++) for (s = 0; s < 2; s++)
      for (z = s; z < DAY-8; z += 2) 
	for (y = z+2; y < DAY-6; y += 2)
	  for (w = y+2; w < DAY-4; w += 2)
	    for (v = w+2; v < DAY-2; v += 2)
	      for (u = v+2; u < DAY; u += 2) {
		if (insert_cl_5(
				HOME(x, u),
				HOME(x, v),
				HOME(x, w), 
				HOME(x, y),
				HOME(x, z),
				0, cl_arr, sign_arr))
		  return 1;
		if (insert_cl_5(
				AWAY(x, u),
				AWAY(x, v),
				AWAY(x, w), 
				AWAY(x, y),
				AWAY(x, z),
				0, cl_arr, sign_arr))
		  return 1;
	      }
  }

  /* relation between GAME and HOME/AWAY */
  for (x = 0; x < n; x++) 
    for (z = 0; z < DAY; z++) {
	      
      for (v = n-1; v >= 0; v--) {
	cl_arr[v] = GAME(x, v, z);
	sign_arr[cl_arr[v]] = 1;
      }
      cl_arr[n] = HOME(x, z);
      sign_arr[cl_arr[n]] = 0;
      Clause_num++;
      if (insert_clause(cl_arr, sign_arr, n+1) == 1)	
	return 1;

      for (v = n-1; v >= 0; v--) {
	cl_arr[v] = GAME(v, x, z);
	sign_arr[cl_arr[v]] = 1;
      }
      cl_arr[n] = AWAY(x, z);
      sign_arr[cl_arr[n]] = 0;
      Clause_num++;
      if (insert_clause(cl_arr, sign_arr, n+1) == 1)	
	return 1;
    }

  Input_sqs = fopen(name, "r");
  for (x = 0; x < n; x++) {
    fscanf(Input_sqs, "%d", &u);
    fscanf(Input_sqs, "%d", &v);
    u--; v--;
    for (y = 0; y < n; y++) if (y != x && y != u && y != v) {
      for (z = 0; z < DAY; z++) {
	cl_arr[z] = GAME(x, y, z);
	sign_arr[cl_arr[z]] = 1;
      }
      Clause_num++;
      if (insert_clause ( cl_arr, sign_arr, DAY) == 1)	
	return 1;
    }
  }
  fclose(Input_sqs);

  return 0;
}

int acc_clauses ()
     /* return 1 if an empty clause is found; otherwise, 0 */
{
  printf("The function is no longer there.\n");
  return 1;
}

print_bigten_schedule ()
{
  if (TEAM == 1 || TEAM == 2) {
    int i, j, x, y, res[22], sum;
    if (TEAM == 1) sum = 4; else sum = 5;

    for (i = 0; i < DAY; i++) res[i] = 0;
    for (i = 1; i <= DAY+DAY; i++) if (Value[i] == TT) { 
      if (i > DAY) res[i-DAY-1] = 2;
      else res[i-1] = 1;
    }

    /* check pattern */
    if (LINE % 2) {
      if (res[0] == 0 && res[17] == 1) printf("b1+a18 >= 2\n");
      if (res[0] == 0 && res[16] == 2) printf("b1+h17 >= 2\n");
      if (res[15] == 0 && res[17] == 1) printf("b16+a18 >= 2\n");
    }

    for (j = 0; j < 2; j++) {
      x = y = 0;
      for (i = j; i < DAY; i+=2) 
	if (res[i] == 2) x++;
	else if (res[i] == 1) y++;
      if (x != sum || y != sum) {
	if (TRACE > 2) printf("%d: no %d home/away games\n", x, sum);
	return 0;
      }
    }
    x = 0;
    for (i = 1; i < 10; i+=2) if (res[i] != 1) x++;
    if (x < 2) printf("%d: too much away games in first five weekends\n", x);

    for (i = 0; i < 15; i++) {
      x = 0;
      for (j = i; j <= i+3; j++) if (res[j] < 2) x++;
      if (x >= 4) printf("%d: no home games in 4\n", j);
    }

    for (i = 0; i < 14; i++) {
      x = 0;
      for (j = i; j <= i+4; j++) if (res[j] != 1) x++;
      if (x >= 5) printf("%d: no away games in 5\n", j);
    }

    if (QUEEN && PIGEON) {
      j = 0;
      for (i = 0; i < DAY; i++) if (res[i] == 0) j += j*DAY+i;
      printf("%2d: ", j);
    }
    for (i = 0; i < DAY; i++) printf(" %d", res[i]);
    printf("\n");
 
  } else if (TEAM == 3 || TEAM == 4) {
    int i, j=0, x, y, z, res[100], team;
    team = (TEAM == 3)? 9 : 11;

    for (i = 1; i <= Max_atom; i++) if (Value[i] == TT) { 
      res[j++] = i-1;
    }

    if (j != team) {
      if (TRACE > 4) printf("Below: Found %d != %d patterns\n", j, NINE);
      else return 0;
      team = j;
    }

    for (j = 0; j < DAY; j++) {
      x=y=z=0;
      for (i = 0; i < team; i++) {
	if (pat[res[i]][j] == 2) x++;
	else if (pat[res[i]][j] == 1) y++;
	else z++;
      }

      if (TEAM == 3) {
	if (x != 4 || y != 4 || z != 1) {
	  if (TRACE > 3) printf("Below: %d home, %d away, %d bye\n", x, y, z);
	  else return 0;
	}
      } else if (x != 5 || y != 5 || z != 1) {
	if (TRACE > 3) printf("Below: %d home, %d away, %d bye\n", x, y, z);
	else return 0;
      }
    }

    for (i = 0; i < team; i++) printf(" %2d", res[i]); 
    printf("\n");

    /*
      int res2[11];
      static int a[100], b[100], mirror=0;

      if (Branch_succ == 1) {
	for (i = 0; i < PATTERN-1; i++) 
	  if (pat[i][0] != 0 && pat[i][1] != 0 && pat[i][2] != 0 
	      && pat[i][16] != 0  && pat[i][17] != 0 && pat[i][15] != 0)
	  for (j = i+1; j < PATTERN; j++) 
	    if (pat[j][0] != 0 && pat[j][1] != 0 && pat[j][2] != 0 
		&& pat[j][16] != 0 && pat[j][17] != 0 && pat[j][15] != 0)
	    {
	    int y, x=1;
	    for (y = 0; x && (y < DAY); y++)
	      if (pat[i][y] + pat[j][y] != 3 &&
		  pat[i][y] + pat[j][y] != 0) x = 0;
	    if (x) { a[mirror] = i; b[mirror++] = j; j = PATTERN; }
	  }
	printf("\n%d pairs of mirror patterns\n", mirror);
      }

      for (i = 0; i < mirror; i++) {
	y = 0; j = 0; x = 0;
	while (j < NINE) {
	  if (x == 0) {
	    if (res[j] == a[i]) j = y = NINE;
	    else if (res[j] < a[i]) res2[j] = res[j];
	    else { res2[j] = a[i]; x++; res2[j+x] = res[j]; }
	  } else if (x == 1) {
	    if (res[j] == b[i]) j = y = NINE;
	    else if (res[j] < b[i]) res2[j+x] = res[j];
	    else { res2[j+x] = b[i]; x++; res2[j+x] = res[j]; }
	  } else res2[j+x] = res[j];
	  j++;
	}
	if (y == 0) {
	  for (j = 0; j < 11; j++) printf(" %2d", res2[j]); 
	  printf("\n");
	}
      }
    }
    */

  } else {
  int x, y, z, i, i1, i2, i3, i4, res[11][22];
  char *team[12];
  if (TEAM == 11) {
  team[0] = "Ill";
  team[1] = "Ind";
  team[2] = "Iow";
  team[3] = "Mic";
  team[4] = "MiS";
  team[5] = "Min";
  team[6] = "Nor";
  team[7] = "Ohi";
  team[8] = "Pen";
  team[9] = "Pur";
  team[10] = "Wis";
  } else {
  team[0] = "Clem";
  team[1] = "Duke";
  team[2] = "FSU";
  team[3] = "GT";
  team[4] = "UMD";
  team[5] = "UNC";
  team[6] = "NCS";
  team[7] = "UVA";
  team[8] = "Wake";
  }
 
  for (x = 0; x < TEAM; x++) for (z = 0; z < DAY; z++) res[x][z] = -100;

  printf("\nSchedule #%ld:\n", Branch_succ);
  for (i = 1+SIZE; i <= Max_atom; i++) if (Value[i] == TT) { 
    z = (i-1-SIZE)%TEAM;
    y = (i-1-SIZE)/TEAM;
    printf("Pattern %d goes to %s\n", z, team[y]);
  }
  printf("\n");

  for (i = 1; i <= SIZE; i++) if (Value[i] == TT) { 
    z = (i-1)%DAY;
    y = ((i-1)/DAY)%TEAM;
    x = (i-1)/(DAY*TEAM);
    res[x][z] = y;
    res[y][z] = -x-1;
  }

  /* remove two games */
  if (TEAM == 11) {
    for (x = 0; x < TEAM; x++) 
      if (res[x][18] == -100) i1 = x;
      else if (res[x][19] == -100) i2 = x;
      else if (res[x][20] == -100) i3 = x;
      else if (res[x][21] == -100) i4 = x;
    
    /* remove games of i3 at i1 and i4 at i2 */
    for (z = 0; z < 18; z++) {
      if (res[i3][z] == i1) { 
	res[i3][z] = res[i1][z] = -100;
	printf("Game %s at %s in week %d (%d) is cancelled\n", 
	       team[i3], team[i1], 1+z/2, 1+z%2);
      } 
      if (res[i4][z] == i2) { 
	res[i4][z] = res[i2][z] = -100;
	printf("Game %s at %s in week %d (%d) is cancelled\n", 
	       team[i4], team[i2], 1+z/2, 1+z%2);
      }
    }
  }

  /*
  for (x = 0; x < TEAM; x++) {
    printf("\n%s's schedule:\n", team[x]);
    for (z = 0; z < DAY; z++) 
      if (res[x][z] >= 0) 
	printf("  vs %s in week %d (%d)\n", team[res[x][z]], 1+z/2, 1+z%2);
      else if (res[x][z] > -100) 
	printf("  at %s in week %d (%d)\n", team[-res[x][z]-1], 1+z/2, 1+z%2);
  }
  */
  
  printf("\n Weeks |");
  for (x = 0; x < TEAM; x++) printf("  %s ", team[x]);
  for (z = 0; z < DAY; z++) { 
    printf("\n W%d(%d) |", 1+z/2, 1+z%2);   
    for (x = 0; x < TEAM; x++) {
      if (res[x][z] >= 0) 
	printf("  %s ", team[res[x][z]]);
      else if (res[x][z] > -100) 
	printf(" @%s ", team[-res[x][z]-1]);
      else
	printf("  bye ");
    }
  }
  }
  return 0;
}

/**** The following function generates the input clauses for
  checking if two Latin squares are isomorphic ****/

int isomo_clauses ()
     /* return 1 if an empty clause is found; otherwise, 0 */
{
  int cl_arr [ MAX_ATOM ], sign_arr [ MAX_ATOM ];
  int n, n1, x, y, v, u;
  char name[20];
  int T1[10][10], T2[10][10];

  n = INCOMPLETE;
  n1 = n-1;
  sprintf(name, "i%d.in", LINE);
  Input_sqs = fopen(name, "r");
  if (Input_sqs == NULL) {
    printf("File %s doesn't exist!\n", name);
    exit(0);
  }

  for (x = 0; x < n; x++)
    for (y = 0; y < n; y++) {
      if (fscanf(Input_sqs, "%d", &u) == EOF) 
	{ printf("Squares incomplete\n"); exit(0); }
      T1[x][y] = u;
    }
  for (x = 0; x < n; x++)
    for (y = 0; y < n; y++) {
      if (fscanf(Input_sqs, "%d", &u) == EOF) 
	{ printf("Squares incomplete\n"); exit(0); }
      T2[x][y] = u;
    }
  fclose(Input_sqs);
  Input_sqs = NULL;

  if (TRACE>1) {
    for (x = 0; x < n; x++) {
      for (y = 0; y < n; y++) 
      	printf(" %d", T1[x][y]); 
      printf("      ");
      for (y = 0; y < n; y++) 
      	printf(" %d", T2[x][y]); 
      printf("\n");
    }
    printf("\n");
  }

  /* T1 must be nonassociative */
  v = 1;
  for (x = 0; x < n; x++) if (v)
    for (y = 0; y < n; y++) if (v)
      for (u = 0; u < n; u++) 
	if (T1[T1[x][y]][u] != T1[x][T1[y][u]]) {
	  v = 0;
	}
  if (v) {
    printf("The first table is associative.\n");
    exit(1);
  }

  if (IDEMPOTENT) {
    /* map 0 to 0 */
    cl_arr[0] = PAIR2KEY(0, 0);
    sign_arr[cl_arr[0]] = 1;
    Clause_num++;
    if (insert_clause ( cl_arr, sign_arr, 1) == 1)	
      return 1;
  }

  /* No two numbers are mapped to the same number. */
  for (x = n1; x >= 0; x--)
    for (y = n1; y >= 0; y--) 
      for (v = x-1; v >= 0; v--) {
	cl_arr[0] = PAIR2KEY(x, y);
	sign_arr[cl_arr[0]] = 0;
	cl_arr[1] = PAIR2KEY(v, y);
	sign_arr[cl_arr[1]] = 0;
	Clause_num++;
	if (insert_clause ( cl_arr, sign_arr, 2) == 1)	
	  return 1;
      }

  /* No number can mapped to different number. */
  for (x = n1; x >= 0; x--)
    for (y = n1; y >= 0; y--) 
      for (v = x-1; v >= 0; v--) {
	cl_arr[0] = PAIR2KEY(y, x);
	sign_arr[cl_arr[0]] = 0;
	cl_arr[1] = PAIR2KEY(y, v);
	sign_arr[cl_arr[1]] = 0;
	Clause_num++;
	if (insert_clause ( cl_arr, sign_arr, 2) == 1)	
	  return 1;
      }

  /* It's a morphisim: T1(f(x), f(y)) = f(T2(x, y)) */
  for (x = n1; x >= 0; x--)
    for (y = n1; y >= 0; y--) 
      for (v = n1; v >= 0; v--)
	for (u = n1; u >= 0; u--) {
	  int a, total;
	  Clause_num++;
	  cl_arr[0] = PAIR2KEY(x, v);
	  sign_arr[cl_arr[0]] = 0;
	  a = PAIR2KEY(y, u);
	  if ((total = insert_one_key(a, 0, cl_arr, sign_arr, 1)) == 0)
	    Subsume_num++;
	  else {
	    a = PAIR2KEY(T1[x][y], T2[v][u]);
	    if ((total = insert_one_key(a, 1, cl_arr, sign_arr, total)) == 0)
	      Subsume_num++;
	    else if (insert_clause ( cl_arr, sign_arr, total) == 1)	
	      return 1;
	  }
	}
  
  /* Each number is mapped to a number. */
  for (x = n1; x >= 0; x--) {
    v = n1;
    for (y = 0; y < n; y++) {
      cl_arr[y] = PAIR2KEY(x, v--);
      sign_arr[cl_arr[y]] = 1;
    }
    Clause_num++;
    if (insert_clause ( cl_arr, sign_arr, n) == 1)	
      return 1;
  }

  /* For each x, there is a number mapped to x. */
  for (x = n1; x >= 0; x--) {
    v = n1;
    for (y = 0; y < n; y++) {
      cl_arr[y] = PAIR2KEY(v--, x);
      sign_arr[cl_arr[y]] = 1;
    }
    Clause_num++;
    if (insert_clause ( cl_arr, sign_arr, n) == 1)	
      return 1;
  }

  return 0;
}

/**** The following function generates the input clauses for
  the Queen problems ****/

int queen_clauses ()
     /* return 1 if an empty clause is found; otherwise, 0 */
{
  int cl_arr [ MAX_ATOM ], sign_arr [ MAX_ATOM ];
  int n, n1, x, y, v, u;

  n = LINE = QUEEN;
  n1 = n-1;

  /* Each row must have a queen. */
  for (x = n1; x >= 0; x--) {
    v = n1;
    for (y = 0; y < n; y++) {
      cl_arr[y] = PAIR2KEY(x, v--);
      sign_arr[cl_arr[y]] = 1;
    }
    Clause_num++;
    if (insert_clause ( cl_arr, sign_arr, n) == 1)	
      return 1;
  }

  if (!IDEMPOTENT) {
  /* Each column must have a queen. */
  for (x = n1; x >= 0; x--) {
    v = n1;
    for (y = 0; y < n; y++) {
      cl_arr[y] = PAIR2KEY(v--, x);
      sign_arr[cl_arr[y]] = 1;
    }
    Clause_num++;
    if (insert_clause ( cl_arr, sign_arr, n) == 1)	
      return 1;
  }}

  /* No two queens are in the same column. */
  for (x = n1; x >= 0; x--)
    for (y = n1; y >= 0; y--) 
      for (v = x-1; v >= 0; v--) {
	cl_arr[0] = PAIR2KEY(x, y);
	sign_arr[cl_arr[0]] = 0;
	cl_arr[1] = PAIR2KEY(v, y);
	sign_arr[cl_arr[1]] = 0;
	Clause_num++;
	if (insert_clause ( cl_arr, sign_arr, 2) == 1)	
	  return 1;
      }

  /* No two queens are in the same row. */
  for (x = n1; x >= 0; x--)
    for (y = n1; y >= 0; y--) 
      for (v = x-1; v >= 0; v--) {
	cl_arr[0] = PAIR2KEY(y, x);
	sign_arr[cl_arr[0]] = 0;
	cl_arr[1] = PAIR2KEY(y, v);
	sign_arr[cl_arr[1]] = 0;
	Clause_num++;
	if (insert_clause ( cl_arr, sign_arr, 2) == 1)	
	  return 1;
      }

  /* No two queens are in the same diagonal. */
  for (x = n1; x >= 0; x--)
    for (y = n1; y >= 0; y--) 
      for (v = x-1; v >= 0; v--) 
	for (u = n1; u >= 0; u--) 
	  if (x - v == abs(y - u)) {
	    cl_arr[0] = PAIR2KEY(x, y);
	    sign_arr[cl_arr[0]] = 0;
	    cl_arr[1] = PAIR2KEY(v, u);
	    sign_arr[cl_arr[1]] = 0;
	    Clause_num++;
	    if (insert_clause ( cl_arr, sign_arr, 2) == 1)	
	      return 1;
	  }

  return 0;
}

/**** The following function generates the input clauses for
  the pigeon-hole problems ****/

int pigeonhole_clauses ()
     /* return 1 if an empty clause is found; otherwise, 0 */
{
  int cl_arr [ MAX_ATOM ], sign_arr [ MAX_ATOM ];
  int n, nminus1, x, y, v;

  n = LINE = PIGEON;
  nminus1 = n-1;

  /*  each pigeon is in a hole. */
  for (x = n; x >= 0; x--) {
    v = nminus1;
    for (y = 0; y < n; y++) {
      cl_arr[y] = PAIR2KEY(x, v--);
      sign_arr[cl_arr[y]] = 1;
    }
    Clause_num++;
    if (insert_clause ( cl_arr, sign_arr, n) == 1)	
      return 1;
  }

  /* No hole has more than one pigeon */
  for (x = n; x >= 0; x--)
    for (y = nminus1; y >= 0; y--) 
      for (v = x-1; v >= 0; v--) {
	cl_arr[0] = PAIR2KEY(x, y);
	sign_arr[cl_arr[0]] = 0;
	cl_arr[1] = PAIR2KEY(v, y);
	sign_arr[cl_arr[1]] = 0;
	Clause_num++;
	if (insert_clause ( cl_arr, sign_arr, 2) == 1)	
	  return 1;
      }
  return 0;
}

/**** The following function generates the input clauses for
  Ramsey number problems ****/
/*  
   | 3   4   5   6   7    8     9
 --|------------------------------
 3 | 6   9  14  18  22  28-29

*/

int ramsey_clauses ()
     /* return 1 if an empty clause is found; otherwise, 0 */
{
  int n, r, x, y, u, v;
  int pair_to_key [MAX_RAMSEY] [MAX_RAMSEY];
  int comb[MAX_RAMSEY];
  int cl_arr [ MAX_ATOM ], sign_arr [ MAX_ATOM ];

  if (RAMSEY > MAX_RAMSEY) {
    fprintf ( stderr, "%d >= MAX_RAMSEY(=%d) (redefine it in test.c).\n",
	       RAMSEY, MAX_STACK);
    exit(0);
  } else if (PIGEON <= 2 || QUEEN <= 2) {
    fprintf ( stderr, "The solution is trivial when min(%d, %d) <= 2.\n\n",
	     PIGEON, QUEEN);
    exit(0);
  } else if (PIGEON >= RAMSEY || QUEEN >= RAMSEY) {
    fprintf ( stderr, "The solution is trivial when max(%d, %d) >= %d.\n\n",
	     PIGEON, QUEEN, RAMSEY);
    exit(0);
  }

  printf("Looking for Ramsey(%d, %d) <= %d\n",
	 PIGEON, QUEEN, RAMSEY);

  n = RAMSEY;
  LINE = QUEEN;

  x = 0;
  for (u = 0; (u < n); u++)
    for (v = u+1; (v < n); v++)
      pair_to_key[v][u] = pair_to_key[u][v] = ++x;

  /* break some symmetries */
  r = QUEEN-1;
  for (x = 0; x < n-r; x++) 
    for (y = x+r; y < n; y++) 
      if (n - y + x >= QUEEN) {
	cl_arr[0] = pair_to_key[x][y];
	printf("no edge (%d %d)\n", x, y);
	sign_arr[cl_arr[0]] = 0;
	Clause_num++;
	if (insert_clause ( cl_arr, sign_arr, 1) == 1)	
	  return 1;
      }
      

  /* there are no p-cliques */
  r = PIGEON-1; 
  for (x = 0; (x <= r); x++) comb[x] = x;
  
  while (comb[0] != n) {
    u = 0;
    for (x = r; (x > 0); x--)
      for (y = x-1; (y >= 0); y--) {
	v = cl_arr[u++] = pair_to_key[comb[y]][comb[x]];
	sign_arr[v] = 0;
      }
    Clause_num++;
    if (insert_clause ( cl_arr, sign_arr, u) == 1)	
      return 1;
  
    if ((comb[0] + r) == n-1)
      comb[0] = n;
    else 
      next_combination(r, n-1, comb);
  }

  /* no degree greater than q for R(r,q) */
  r = QUEEN-1; 
  for (x = 0; (x <= r); x++) comb[x] = x;
  
  if (0 && RAMSEY > 10) {
  while (comb[0] != n) {
    for (y = n-1; (y >= 0); y--) {
      x = r;
      while ((x >= 0) && (y != comb[x])) x--;
      if (x < 0) {
	u = 0;
	for (x = r; x >= 0; x--) {
	  v = cl_arr[u++] = pair_to_key[y][comb[x]];
	  sign_arr[v] = 0;
	}
	Clause_num++;
	if (insert_clause ( cl_arr, sign_arr, u) == 1)	
	  return 1;
      }
    }
    if ((comb[0] + r) == n-1)
      comb[0] = n;
    else 
      next_combination(r, n-1, comb);
  }
  }

  /* there are no q-independent sets */
  r = QUEEN-1; 
  for (x = 0; (x <= r); x++) comb[x] = x;
  
  while (comb[0] != n) {
    u = 0;
    for (x = r; (x > 0); x--)
      for (y = x-1; (y >= 0); y--) {
	v = cl_arr[u++] = pair_to_key[comb[y]][comb[x]];
	sign_arr[v] = 1;
      }
    Clause_num++;
    if (insert_clause ( cl_arr, sign_arr, u) == 1)	
      return 1;
  
    if ((comb[0] + r) == n-1)
      comb[0] = n;
    else 
      next_combination(r, n-1, comb);
  }

  return 0;
}

void next_combination (r, n, comb)
     int r, n, comb[];
{
  int i, j, nr1;

  i = r;
  nr1 = n - i;
  while (comb[i] == nr1 + i) i--;
  nr1 = ++comb[i];
  for (j = i+1; (j <= r); j++) comb[j] = ++nr1;
  
  /* printf("[ ");
  for (i = 0; i <= r; i++) printf("%2d ", comb[i]);
  printf("]\n"); */
}
    
/*****/
int next_permutation (p, l)
     int p[], l;
{
  int i, j, x, y;

  if (l-- < 2) return 0;
  i = l - 1;
  x = p[l]; y = p[i];
  while (y > x) {
    x = y;
    if (i-- == 0) return 0;
    y = p[i];
  }

  j = l;
  while (y > p[j]) j--;

  p[i] = p[j]; 
  p[j] = y;

  i++;
  j = l;
  while (i < j) {
    x = p[i];
    p[i++] = p[j];
    p[j--] = x;
  }

  /*
  printf("   Perm: ");
  for (i = 0; i <= l ; i++) printf(" %d", p[i]);
  printf("\n");
  */
  return 1;
}

int gcd(a, b)
     int a, b;
{
  int x;
  while (a>0) {
    x = b % a;
    b = a; 
    a = x; 
  }
  return b;
}

