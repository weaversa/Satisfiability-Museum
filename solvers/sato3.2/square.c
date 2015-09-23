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
#define GETNUM(i,j,k) (is_same_hole(i,j)? -1 : Triple[i][j][k])

extern int m, n, n1, n_sqt, n_cube, n_four, max_seed;

int Same_hole[MAX_SQUARE1][MAX_SQUARE1];
int Triple[MAX_SQUARE1][MAX_SQUARE1][MAX_SQUARE1]; 
int print_error = 1;

void set_same_hole(x,y) int x, y; { 
  Same_hole[x][y] = 1; 
}
int is_same_hole(x,y) int x, y; { return Same_hole[x][y]; }

int Lsquare[MAX_SQUARE1][MAX_SQUARE1];
int Lsquare2[MAX_SQUARE2][MAX_SQUARE2];
int Lsquare3[MAX_SQUARE2][MAX_SQUARE2];

GLOB int ABG_f[MAX_ABG_SIZE][MAX_ABG_SIZE];
GLOB int ABG_g[MAX_ABG_SIZE];

void print_num (x) 
     int x;
{
  if (x < 0) printf("   ");
  else if (x >= m) printf(" x%d", x-m+1);
  else if (x < 10) printf("  %d", x);
  else printf(" %d", x);
}

void test_round_robin()
{
  int x, y, u, v, done[MAX_SQUARE1][MAX_SQUARE1];
  int n2 = m/2;

  printf("\nRound-robin tournament for %d teams:\n", n);
  for (x = 0; x < n; x++)
    for (y = 1; y < n; y++) done[x][y] = 0;

  if (QUEEN == 37) 
    for (x = 0; x < n-1; x++) {
      printf("\nWeek %2d:", x+1);
      for (y = 0; y < n2; y++) {
	printf(" %2d - %2d,", u=Lsquare[x][y], v=Lsquare[x][y+n2]);
	if (u > v) { v = u; u = Lsquare[x][y+n2]; }
	if (done[u][v] == 0) 
	  done[u][v] = 1;
	else 
	  printf(" (twice) ");
      }
      if (x < m) 
	for (y = m; y < n1; y+=2) {
	  printf(" %2d - %2d,", u=Lsquare[x][y], v=Lsquare[x][y+1]);
	  if (u > v) { v = u; u = Lsquare[x][y+1]; }
	  if (done[u][v] == 0) 
	    done[u][v] = 1;
	  else 
	    printf(" (twice) ");
	}
    }
  else
    for (x = 0; x < n-1; x++) {
      printf("\nWeek %2d:", x+1);
      for (y = 0; y < n1; y+=2) {
	printf(" %2d - %2d,", u=Lsquare[x][y], v=Lsquare[x][y+1]);
	if (u > v) { v = u; u = Lsquare[x][y+1]; }
	if (done[u][v] == 0) 
	  done[u][v] = 1;
	else 
	  printf(" (twice) ");
      }
    }
  printf("\n\nLatin square:");
  print_square(0);
}

void print_qgroup_model (f)
     FILE *f;
{
  int i, x, y, z;

  for (x = 0; x < n; x++) {
    for (y = 0; y < n; y++) Lsquare[x][y] = -2;
    Lsquare[x][x] = x;
  }
  for (i = Max_atom; i > 0; i--) if (Value[i] == TT) {
    if (multi_squares() && (i > SQUARE2)) {
      int square3 = SQUARE2+SQUARE2;
      if (i > square3) {
	key2triple(i-square3, &x, &y, &z);
	Lsquare3[x][y] = z; 
      } else {
	key2triple(i-SQUARE2, &x, &y, &z);
	Lsquare2[x][y] = z; 
      }
    } else {
      key2triple(i, &x, &y, &z);
      if ((63 <= QUEEN && QUEEN <= 68) && ((x > y) || (x > z))) {
	x = n1-x; y = n1-y; z = n1-z;
      } 
      Lsquare[x][y] = z; 
      if (63 <= QUEEN && QUEEN <= 68) {
	Lsquare[y][z] = x; 
	Lsquare[z][x] = y; 
      }
    }
  }
  
  if (Branch_succ) {
    if (CREATE) {
      if (CREATE <= Branch_succ) print_output_sq();
    } else {

      if (QUEEN == 90 || QUEEN == 83) print_output_sq();
      else if ((QUEEN <= 1 || QUEEN == 43 || QUEEN == 20) && MODEL != 1) 
	print_output_sq();

      if (QUEEN == 37 || QUEEN == 38)
	test_round_robin();
      else if (QUEEN == 29 || QUEEN == 39) 
	test_r_sols();
      /*
      else if (QUEEN == 28) 
	test_r_ortho();
      */
      else {
	test_qg(); 

	if (QUEEN == 50 || QUEEN == 51) {
	  if (associtive()) {
	    Branch_succ--;
	    Branch_fail++;
	  } else {
	    FILE *output;
	    char cmd[50];
	    output = fopen("sq.in", "w");
	    for (x = 0; x < QGROUP; x++)
	      for (y = 0; y < QGROUP; y++)
		fprintf(output, " %d", Lsquare[x][y]);
	    fprintf(output, "\n");
	    fclose(output);
	    sprintf(cmd, "/space/hzhang/sato/hp/run.iso %d", QGROUP);
	    system(cmd);
	  }
	} else {

	  if (Branch_succ) {
	    printf("\nModel #%ld:\n", Branch_succ);
	    print_square(0);
	    test_all();
	  }

	}
	if (QUEEN == 15 || QUEEN == 10) print_qg15_blocks();
	else if (QUEEN == 44) { print_qg44_blocks(); }
	else if (QUEEN >= 63 && QUEEN <= 68) print_qg63_blocks(); 

	if (multi_squares()) {
	  test_orthogonal2();
	  printf("\nThe second square:\n");
	  print_square(2);

	  if (multi_squares() > 1) {
	    printf("\nThe third square:\n");
	    print_square(3);
	  }
	}
      }
    }
  }
}

test_r_ortho ()
{
  int r, x, y, s3[MAX_SQUARE1][MAX_SQUARE1];

  /* bug fix: */
  if (Lsquare[0][0] != 0) Lsquare[0][0] = 0;

  for (x = 0; x < QGROUP; x++)
    for (y = 0; y < QGROUP; y++) s3[x][y] = 0;
  for (x = 0; x < QGROUP; x++)
    for (y = 0; y < QGROUP; y++) 
      s3[Lsquare[x][y]][Lsquare2[x][y]] = 1;
  r = 0;
  for (x = 0; x < QGROUP; x++)
    for (y = 0; y < QGROUP; y++) 
      if (s3[x][y] == 1) r++;

  if (QGROUP == 77 && r == 28) {
    Branch_succ--;
    Branch_fail++;
  } else {
    printf("%d 1\n", Branch_succ);
    print_square(0);
    printf("%d 2\n", r);
    print_square(2);
  }
  return 0;
}

test_r_sols ()
{
  int r, x, y;
  static int done[50];

  if (Branch_succ == 1) for (x = 0; x < 50; x++) done[x] = 0;

  for (x = 0; x < QGROUP; x++)
    for (y = 0; y < QGROUP; y++) Lsquare2[x][y] = 0;
  for (x = 0; x < QGROUP; x++)
    for (y = 0; y < QGROUP; y++) 
      Lsquare2[Lsquare[x][y]][Lsquare[y][x]] = 1;

  r = 0;
  for (x = 0; x < QGROUP; x++)
    for (y = 0; y < QGROUP; y++) 
      if (Lsquare2[x][y] == 0) {
	if (TRACE > 1) printf("<%d %d> ", x, y);
	r++;
      }
  if (TRACE > 1 && r) printf(" <-- missed pairs\n");

  if (done[r] != 100) {
    printf("%dx%d - %d = %d\n", QGROUP, QGROUP, r, QGROUP*QGROUP-r);
    print_square(0);
    done[r] = 100;
  } else {
    Branch_succ--;
    Branch_fail++;
  }
  return 0;
}

void copy_sq1_to_sq2() 
{ int x, y; 
  for(x=0;x<QGROUP;x++) for(y=0;y<QGROUP;y++) Lsquare2[x][y]=Lsquare[x][y]; }

void copy_sq1_to_sq3() 
{ int x, y; 
  for(x=0;x<QGROUP;x++) for(y=0;y<QGROUP;y++) Lsquare3[x][y]=Lsquare[x][y]; }

void print_cyclic_model (f)
     FILE *f;
{
  int mn = m * n;
  int mk = m * INCOMPLETE;
  int i, j, x, y, num, step[3], n2;
  int Kmax, nk2m;
  if (!(max_seed = get_addk())) max_seed = 1;

  if (CYCLIC == 'C') {
    nk2m = (QGROUP + INCOMPLETE + INCOMPLETE)*(QGROUP - INCOMPLETE);
    Kmax = nk2m + nk2m + max_seed*(QGROUP - INCOMPLETE);
  } else {
    Kmax = (QGROUP + 2*INCOMPLETE)*(QGROUP - INCOMPLETE);
  }

  step[0] = 0; step[1] = SQUARE2; step[2] = SQUARE2+SQUARE2;
  num = multi_squares();
  n2 = Max_atom / (1+num);

  /* printf("n2 = %d, Kmax = %d, max_seed = %d\n", n2, Kmax, max_seed); */

  for (j = num; j >= 0; j--) {
    int i2, k;
    for (i2 = n2; i2 > 0; i2--) if (Value[i2+step[j]] == TT) { 
      i = i2 % Kmax;
      if (i == 0) i = Kmax;
      k = (i2-i)/Kmax;

      if (i <= mn) { 
	x = (i - 1) % m;
	y = (i - 1 - x) / m;
	Lsquare[k][x] = y;
      } else if (i <= (mn + mk)) {
	y = (i - 1) % m;
	x = (i - 1 - y - mn) / m + m;
	Lsquare[k][x] = y;
      } else if (i <= (mn + (mk << 1))) {
	y = (i - 1) % m;
	x = (i - 1 - y - mn - mk) / m + m;
	Lsquare[x][k] = y;
      }

    }
    fill_table(max_seed);
    if (j == 2) copy_sq1_to_sq3();
    else if (j == 1) copy_sq1_to_sq2();
  }

  if (CREATE) {
    if (CREATE <= Branch_succ) print_output_sq();
  } else if (MODEL == 2 && (QUEEN == 0 || QUEEN == 3)) {
    print_sq_to_tuples();
  } else if (QUEEN == 37 || QUEEN == 38) {
    test_round_robin();
  } else {

    if (QUEEN == 90) print_output_sq();
    printf("\nModel #%ld:\n", Branch_succ);
    print_square(0);

    if (QUEEN < 3 || QUEEN == 31 || (QUEEN >= 20 && QUEEN <= 24)) { 
      print_first_row();
    }

    if (QUEEN == 3) { print_qg3_blocks(); /* adjust_dia();*/ }
    else if (QUEEN == 33) { print_qg3_blocks(); test_dia(); }
    /* else if (QUEEN == 30) print_qg30_blocks();*/
    else if (QUEEN == 4) print_qg4_blocks();
    else if (QUEEN == 44) { print_qg44_blocks(); }
    else if (QUEEN == 15 || QUEEN == 10) print_qg15_blocks();
    else if (QUEEN >= 63 && QUEEN <= 68) print_qg63_blocks(); 
    else if (QUEEN == 100) print_qg100_blocks();

    test_qg();
    if (CREATE == 0) test_all();

    if (multi_squares()) { 
      test_orthogonal2(multi_squares()); 
      print_square(2); 
      print_first_row2();
      if (QUEEN == 24) print_q24_5tuple();
    }
  }
}

int switch_indices()
{
  int i, j, x, y;

  printf("Please enter two integers separated by a space: ");
  scanf("%d %d", &i, &j);

  if (i == j) { 
    printf("the two numbers are the same\n");
    return 0;
  }

  if (i < 0 || i > n) { 
    printf("the first number is out of range\n");
    return 0;
  }
  if (j < 0 || j > n) {
    printf("the second number is out of range\n");
    return 0;
  }

  for (x = 0; x < n; x++) { 
    y = Lsquare[i][x]; 
    Lsquare[i][x] = Lsquare[j][x]; 
    Lsquare[j][x] = y; 
  }

  for (x = 0; x < n; x++) { 
    y = Lsquare[x][i]; 
    Lsquare[x][i] = Lsquare[x][j]; 
    Lsquare[x][j] = y; 
  }

  for (x = 0; x < n; x++) 
    for (y = 0; y < n; y++) {
      if (Lsquare[x][y] == i) Lsquare[x][y] = j; 
      else if (Lsquare[x][y] == j) Lsquare[x][y] = i; 
    }

  print_square(0);
  return 1;
}

test_dia()
{
  int test[100];
  int n1 = n-1;
  int i, j, wrong;

  wrong = 0;
  for (i = 0; i < n; i++) test[i] = 0;
  for (i = 0; i < n; i++) {
    j = Lsquare[i][n1-i];
    if (test[j]) {
      printf("  entry[%d][%d] = %d repeats\n", i, n1-i, j);
      wrong = 1;
    }
    test[j]++;
  }

  if (wrong) {
    printf("Unused values: ");
    for (i = 0; i < n; i++) if (test[i] == 0) printf("%d ", i);
    printf("\n\n");

    for (i = 1; i < n; i++) if (test[Lsquare[n1-i][i]] > 1) 
      for (j = 0; j < i; j++) if (test[Lsquare[n1-j][j]] > 1) {
	if (test[Lsquare[n1-j][i]] < 2 && test[Lsquare[n1-i][j]] < 2)
	    printf("  suggested switch: %d, %d (confidence: %d)\n",
		   j, i, test[Lsquare[n1-j][i]]+test[Lsquare[n1-i][j]]+
		   test[Lsquare[i][n1-j]]+test[Lsquare[j][n1-i]]);
	  }
  }
  return wrong;
}

void adjust_dia()
{
  while (test_dia() && switch_indices());
}

void fill_table (seed)
     int seed;
{
  int i, j, x, k;

  for (k = 0; k < seed; k++)
    for (i = seed; i+k < m; i += seed) {
      for (j = 0; j < m; j++) {
	x = Lsquare[k][j];
	Lsquare[ABG_f[k][i]][ABG_f[j][i]] = 
	  (x >= m || x < 0)? x : ABG_f[x][i];
      }

      for (j = m; j < n; j++) {
	/*
	  Lsquare[i][j] = (Lsquare[i-1][j] + 1) % m;
	  Lsquare[j][i] = (Lsquare[j][i-1] + 1) % m;
	  */
	Lsquare[ABG_f[k][i]][j] = ABG_f[Lsquare[k][j]][i];
	Lsquare[j][ABG_f[k][i]] = ABG_f[Lsquare[j][k]][i];
      }
    }
}

void print_output_sq ()
{
  int i, j;
  FILE *output;
  char name[60];

  if (QUEEN == 43)
    sprintf(name, "/space/hzhang/sato/qg42/qg%d.%d.sqs.out", QUEEN, FLAG);
  else
    sprintf(name, "qg%d.%d.sqs.out", QUEEN, QGROUP);
  output = fopen(name, "a");
  fprintf(output, "%d %d", QGROUP, Branch_succ); 
  for (i = 0; i < QGROUP; i++) {
    fprintf(output, "\t");
    for (j = 0; j < QGROUP; j++) 
      if (is_same_hole(i, j))
	fprintf(output, "%d ", i);
      else
	fprintf(output, "%d ", Lsquare[i][j]);
  }
  fprintf(output, "\n");
  fclose(output);
}

void print_sq_to_tuples ()
{
  int i;
  FILE *output;

  output = fopen("tmp.in", "a");
  fprintf(output, "%d %d\n", QGROUP, Branch_succ);

  for (i = m; i < QGROUP; i++)
    fprintf(output, " %d 0 %d %d -2\n", i, Lsquare[i][0], Lsquare[0][i]);

  for (i = m; i < QGROUP; i++)
    fprintf(output, " 0 %d %d %d -2\n", i, Lsquare[0][i], Lsquare[i][0]);

  for (i = (IDEMPOTENT)? 1 : 0; i < m; i++) if (!is_same_hole(i, 0)) 
    fprintf(output, " 0 %d %d %d -2\n", i, Lsquare[0][i], Lsquare[i][0]);

  fprintf(output, "\n");
  fclose(output);
}

associtive ()
     /* return 1 iff the square is associtive */
{
  int k, i, j;

  for (i = 0; i < n; i++) 
    for (j = 0; j < n; j++) 
      for (k = 0; k < n; k++) 
	if (Lsquare[Lsquare[i][j]][k] != Lsquare[i][Lsquare[j][k]]) {
	  printf("Nonassociative: (%d*%d)*%d != %d*(%d*%d)\n", 
		 i, j, k, i, j, k);
	  return 0;
	}
  return 1;
}

void print_square (second)
     int second;
{
  int k, i, j;

  if (second == 3) printf("\n  + |"); 
  else if (second) printf("\n  . |"); else printf("\n  * |");
  for (i = 0; i < n; i++) print_num(i);
  printf("\n  --+-");
  for (i = 0; i < n; i++) printf("---");
  printf("\n"); 

  for (i = 0; i < n; i++) {
    print_num(i); printf(" |");
    if (i < m) k = n; else k = m;
    for (j = 0; j < k; j++) 
      if (is_same_hole(i, j)) {
	printf("   ");
      } else if (second == 3)
	print_num(Lsquare3[i][j]);
      else if (second)
	print_num(Lsquare2[i][j]);
      else
	print_num(Lsquare[i][j]);
    printf("\n");
  }
  printf("\n"); 
}

void print_qg15_blocks ()
{
  int x, y, z, u, v, done[MAX_SQUARE1][MAX_SQUARE1];
  int i = 0;

  if (get_k_flag()) max_seed = get_k_flag();
  else max_seed = 1;

  printf("\nBase blocks (+%d mod %d):\n", max_seed, m);
  for (x = 0; x < m; x++)
    for (y = 1; y < m; y++) done[x][y] = 0;

  for (x = 0; x < m; x++) 
    for (y = x+1; y < QGROUP; y++) 
      if (done[x][y] == 0 && is_same_hole(x, y) == 0) {
      z = Lsquare[x][y];
      u = Lsquare[y][z];
      v = Lsquare[z][u];

      if (Lsquare[u][v] != x) {
	printf("Counterexample: <%d, %d, %d, %d, %d>\n",
	       x, y, z, u, v);
	return;
      }

      printf("   block %d: {", ++i);
      print_num(x);
      print_num(y);
      print_num(z);
      print_num(u);
      print_num(v);
      printf(" }");

      done[x][y] = 1;
      done[y][z] = 1;
      done[z][u] = 1;
      done[u][v] = 1;
      done[v][x] = 1;

      if (PIGEON == 2) {

	for (z = 1; z < QGROUP; z++) {
	  if (Value[u=OMEGA(x, y, z)] == TT) printf(" --%d", z);
	}
      }
      printf("\n");
    }
}

print_qg30_blocks ()
{
  int x, y, z, u, done[MAX_SQUARE1][MAX_SQUARE1];

  if (get_addk() > 0) max_seed = get_addk();
  else max_seed = 1;

  printf("\nBase blocks (+%d mod %d):\n", max_seed, m);
  for (x = 0; x < m; x++)
    for (y = 1; y < m; y++) done[x][y] = 0;

  for (x = 0; x < max_seed; x++) 
    for (y = x+1; y < m; y++) 
      if (done[x][y] == 0 && is_same_hole(x, y) == 0) {
      z = Lsquare[x][y];

      if (Lsquare[y][z] != x) {
	printf("Counterexample: <%d, %d, %d>\n",
	       x, y, z);
	return 0;
      }

      printf("   {");
      print_num(x);
      print_num(y);
      print_num(z);
      printf(" }\n");

      for (u = 0; u < m; u += max_seed) {
	done[(x+u)%m][(y+u)%m] = 1;
	if (z < m) {
	  done[(y+u)%m][(z+u)%m] = 1;
	  done[(z+u)%m][(x+u)%m] = 1;
	}
      }
    }
  return 0;
}

void print_qg100_blocks()
{
  int x, y, z, u, v, done[5][MAX_SQUARE1];
  int i = 0;

  if (get_k_flag()) max_seed = get_k_flag();
  else max_seed = 1;

  printf("\nBase blocks (+%d mod %d):\n", max_seed, m);
  for (x = 0; x < max_seed; x++)
    for (y = 1; y < m; y++) done[x][y] = 0;

  for (y = 0; y < max_seed/2; y++) 
    for (x = m; x < QGROUP; x++) {
      z = Lsquare[x][y];
      u = Lsquare[y][z];
      v = Lsquare[z][u];

      if (Lsquare[u][v] != x) {
	printf("Counterexample: <%d, %d, %d, %d, %d>\n",
	       x, y, z, u, v);
	return;
      }

      printf("   block %d: {", ++i);
      print_num(x);
      print_num(y);
      print_num(z);
      print_num(u);
      print_num(v);
      printf(" }\n");

      done[y % max_seed][DIFF(y, z)] = 1;
      done[z % max_seed][DIFF(z, y)] = 1;
      done[z % max_seed][DIFF(z, u)] = 1;
      done[u % max_seed][DIFF(u, z)] = 1;
      done[u % max_seed][DIFF(u, v)] = 1;
      done[v % max_seed][DIFF(v, u)] = 1;
    }

  for (x = 0; x < max_seed; x++)
    for (y = x+1; y < m; y++) {
      z = DIFF(x,y);
      if (is_same_hole(x, y)) done[x][z] = 1;
      else if (done[x][z] != 1) {
	done[x][z] = 1;
	done[y % max_seed][DIFF(y, x)] = 1;

	z = Lsquare[x][y];
	u = Lsquare[y][z];
	v = Lsquare[z][u];

	if (Lsquare[u][v] != x) {
	  printf("Counterexample: <%d, %d, %d, %d, %d>\n",
		 x, y, z, u, v);
	  return;
	}

	printf("   block %d: {", ++i);
	print_num(x);
	print_num(y);
	print_num(z);
	print_num(u);
	print_num(v);
	printf(" }\n");

	done[y % max_seed][DIFF(y, z)] = 1;
	done[z % max_seed][DIFF(z, y)] = 1;
	done[z % max_seed][DIFF(z, u)] = 1;
	done[u % max_seed][DIFF(u, z)] = 1;
	done[u % max_seed][DIFF(u, v)] = 1;
	done[v % max_seed][DIFF(v, u)] = 1;
	done[v % max_seed][DIFF(v, x)] = 1;
	done[x][DIFF(x, v)] = 1;
      }
    }

  printf("\n");
}

void print_qg4_blocks()
{
  int a, b, ab, ba, d, done[5][MAX_SQUARE1];
  int i = 0;

  if (get_k_flag()) max_seed = get_k_flag();
  else max_seed = 1;

  printf("\nBase blocks (+%d mod %d):\n", max_seed, m);
  for (a = 0; a < max_seed; a++)
    for (b = 1; b < m; b++) done[a][b] = 0;

  for (a = m; a < QGROUP; a++)
    for (ab = 0; ab < max_seed; ab++)
      for (b = 0; b < m; b++) if (Lsquare[a][b] == ab) {
	ba = Lsquare[b][a];

	printf("   block %d: {", ++i);
	print_num(a);
	print_num(ab);
	print_num(b);
	print_num(ba);
	printf("  }\n");

	done[ab % max_seed][DIFF(ab,b)] = 1;
	done[b % max_seed][DIFF(b, ba)] = 1;

	b = m;
      }

  for (a = 0; a < max_seed; a++)
    for (ab = a+1; ab < m; ab++) {
      d = DIFF(a,ab);
      if (is_same_hole(a, ab)) done[a][d] = 1;
      else if (done[a][d] != 1) {
	for (b = 1; b < m; b++) if (Lsquare[a][b] == ab) {
	  ba = Lsquare[b][a];

	  printf("   block %d: {", ++i);
	  print_num(a);
	  print_num(ab);
	  print_num(b);
	  print_num(ba);
	  printf("  }\n");

	  done[a][d] = 1;
	  done[ab % max_seed][DIFF(ab,b)] = 1;
	  done[b % max_seed][DIFF(b, ba)] = 1;
	  done[ba % max_seed][DIFF(ba, a)] = 1; 

	  b = m;
	}
      }
    }

  printf("\n");
}

print_qg44_blocks()
{
  int w, x, y, z, n2 = n/2;
  int i=0;

  printf("\nGames:\n");

  for (x = 0; x < n1; x++) {
    for (y = 0; y < n2; y += 2) {
      /* (a c) or (c a) */
      printf("   %2d: (", ++i);
      print_num(Lsquare[x][y]);
      print_num(Lsquare[x][y+1]);
      print_num(Lsquare[x][y+n2]);
      print_num(Lsquare[x][y+n2+1]);
      printf(" ) ");
    }
    printf("\n");
  }
  printf("\n");
}

void print_qg63_blocks()
{
  FILE *file;
  FILE *file2;
  int i, j, k, y, n2;
  int x = 0;
  int a;

  if (QUEEN == 66 || QUEEN == 63) {
    a = n; n2 = m;
  } else if (QUEEN == 64 || QUEEN == 67) {
    a = get_k_flag();
    if (a < 2 && QUEEN == 64) {
      a = 1; n2 = n-2;
    } else {
      n2 = n-a;
      a = 1;
    }
  } else {
    a = get_addk();
    if (a < 2) {
      a = 1; n2 = n-2;
    } else {
      n2 = n-n%a;
    }
  }

  file = fopen("MTS.atoms", "a");
  file2 = fopen("mts.atoms", "a");

  for (y = 0; y < n2; y += a) {
    for (i = 0; i < n; i++)
      for (j = i+1; j < n; j++) {
	k = Lsquare[i][j];
	if (k > 0 && i < k) {
	  int old_cyclic = CYCLIC;
	  if (y == 0) {
	    print_good63(++x, i, j, k, n2);
	    if (CYCLIC != 0)
	      fprintf(file2, "%d\n", TRIPLE2KEY(i, j, k));
	  }
	  
	  CYCLIC = 0;
	  fprintf(file, "%d ", TRIPLE2KEY(good63(i,y,n2), 
					  good63(j,y,n2),
					  good63(k,y,n2)));
	  CYCLIC = old_cyclic;
	}
    }

    if (y == 0) {
      printf("\n");
    }
    fprintf(file, "\n");
  }

  fclose(file);
  fclose(file2);
}

int good63 (i, x, n2)
     int i, x, n2;
{
  if (i < n2)
    return ((i+x)%n2);
  else
    return i;
}

int print_good63 (x, i, j, k, n2)
     int x, i, j, k, n2;
{
  int y;

  if (j >= n2) {
    y = i; i = j; j = k; k = y; 
  } else if (k >= n2) { 
    y = i; i = k; k = j; j = y; 
  }

  printf(" { %d, %d, %d } :b%d\n", i, j, k, x);

  return 0;
}

void print_qg3_blocks()
{
  int a, b, ab, c, d, done[5][MAX_SQUARE1];
  int i = 0;

  if (get_k_flag()) max_seed = get_k_flag();
  else max_seed = 1;

  printf("\nBase blocks (+%d mod %d):\n", max_seed, m);
  for (a = 0; a < max_seed; a++)
    for (b = 1; b < m; b++) done[a][b] = 0;

  for (a = 0; a < max_seed; a++)
  for (b = 0; b < m; b++) {
    ab = DIFF(a,b);
    if (is_same_hole(a, b)) done[a][ab] = 1;
    else if (done[a][ab] != 1 && ((c = Lsquare[a][b]) < m )) {
      d = Lsquare[b][a];

      if (Lsquare[c][d] != a) 
	printf("Counterexample: %d * %d = %d, %d * %d = %d, but %d * %d = %d != %d\n",
	       a, b, c, b, a, d, c, d, Lsquare[c][d], a);

      if (Lsquare[d][c] != b) 
	printf("Counterexample: %d * %d = %d, %d * %d = %d, but %d * %d = %d != %d\n",
	       a, b, c, b, a, d, d, c, Lsquare[d][c], b);

      printf("   block %d: {", ++i);
      print_num(a);
      print_num(b);
      print_num(c);
      print_num(d);
      printf("  }\n");

      done[a][ab] = 1;
      done[b % max_seed][DIFF(b,a)] = 1;
      if (d < m) 
	done[c % max_seed][DIFF(c, d)] = done[d % max_seed][DIFF(d, c)] = 1; 
    }
  }
  printf("\n");
}

void init_same_hole() 
{ 
  int i, j; 

  for (i = m; i < QGROUP; i++)
    for (j = m; j < QGROUP; j++) Same_hole[i][j] = 1;

  for (i = 0; i < m; i++)
    for (j = 0; j < m; j++) Same_hole[i][j] = 0; 
}

void fill_triple ()
{
  int x,y,z;

  for (x = 0; x < n; x++)  
    for (y = 0; y < n; y++) 
      for (z = 0; z < n; z++)
	Triple[x][y][z] = TRIPLE2KEY(x,y,z);
}

int conjugate_num (op)
  int op;
{
       if (op == 0) return 123;
  else if (op == 1) return 231;
  else if (op == 2) return 312;
  else if (op == 3) return 132;
  else if (op == 4) return 321;
  else if (op == 5) return 213;
  else return(0);
}

int co_key (op, x, y, z)
     int op, x, y, z;
{
       if (op == 0) return Triple[x][y][z];  /* op0 = 123 */
  else if (op == 1) return Triple[z][x][y];  /* op1 = 231 */
  else if (op == 2) return Triple[y][z][x];  /* op2 = 312 */
  else if (op == 3) return Triple[x][z][y];  /* op3 = 132 */
  else if (op == 4) return Triple[z][y][x];  /* op4 = 321 */
  else if (op == 5) return Triple[y][x][z];  /* op5 = 213 */
  else return(0);
}

/*** Functions for testing co cycles ***/

void fill_triple2 ()
{
  int x,y,z;

  for (x = 0; x < n; x++)  
    for (y = 0; y < n; y++) if (is_same_hole(x, y) == 0) {
      z = get0123(x, y);
      if (is_same_hole(x, z) == 0 && is_same_hole(y, z) == 0) {
	Triple[x][y][0] = z;
	Triple[y][z][1] = x;
	Triple[z][x][2] = y;
	Triple[x][z][3] = y;
	Triple[z][y][4] = x;
	Triple[y][x][5] = z;
      }
    }
}

int test_co (op1, op2)
     int op1, op2;
{
  int x, y, z, t, u, v;
  
  for (x = 0; x < n; x++) 
    for (y = n-1; y >= 0; y--) 
      if (is_same_hole(x, y) == 0)
	for (z = 0; z < n; z++) 
	  for (t = n-1; t >= 0; t--) if (x != z || y != t) {
	    u = Triple[x][y][op1];
	    v = Triple[x][y][op2];
	    if (is_same_hole(z, t) == 0 &&
		is_same_hole(x, u) == 0 &&
		is_same_hole(y, u) == 0 &&
		is_same_hole(z, u) == 0 &&
		is_same_hole(t, u) == 0 &&
		is_same_hole(x, v) == 0 &&
		is_same_hole(y, v) == 0 &&
		is_same_hole(z, v) == 0 &&
		is_same_hole(t, v) == 0) {

	      if (is_same_hole(u, v)) {

		if (print_error) {
		  printf("Counterexample for Orthogonality <%d,%d>:", op1, op2);
		  printf("\n    %d *%d %d = %d", 
		       x, conjugate_num(op1), y, u);
		  printf("      %d *%d %d = %d,   <%d, %d> is a hole\n", 
			 x, conjugate_num(op2), y, v, u, v);
		}
		return 0;
	      }

	      if (u == Triple[z][t][op1] &&
		  v == Triple[z][t][op2]) {

	      if (print_error) {
		printf("Counterexample for Orthogonality <%d,%d>:", op1, op2);
		printf("\n    %d *%d %d = %d *%d %d = %d", 
		       x, conjugate_num(op1), y,
		       z, conjugate_num(op1), t, Triple[x][y][op1]);
		printf("      %d *%d %d = %d *%d %d = %d\n", 
		       x, conjugate_num(op2), y, 
		       z, conjugate_num(op2), t, Triple[x][y][op2]);
	      }
	      return 0;
	      }
	    }
	  }

  printf("  Found orthogonality between (%d)- and (%d)-conjugates <%d,%d>\n",
	   conjugate_num(op1), conjugate_num(op2), op1, op2);
  return 1;
}

void test_c6_qg3()
{
  int edge[10], i;

  print_error = 0;
  for (i = 1; i < 10; i++) edge[i] = 0;
  edge[5] = 1;
  edge[8] = 1;
  edge[9] = 1;

  if (LINE == 20) LINE = 5;
  print_error = 1;
  test_colsg(edge);

  /* if (MODEL > 10000) print_first_rows(); */
}

void test_c6_qg4()
{
  int edge[10], i;

  for (i = 1; i < 10; i++) edge[i] = 0;
  edge[5] = 1;
  edge[6] = 1;

  /*
  print_error = 0;
  if (test_co(0, 1)) edge[1] = edge[9] = 1;
  else if (test_co(0, 2)) edge[2] = edge[8] = 1;
  else if (test_co(0, 3)) edge[3] = edge[8] = 1;
  else if (test_co(0, 4)) edge[4] = edge[9] = 1;
  else return; */

  if (LINE == 20) LINE = 5;
  print_error = 1;
  test_colsg(edge);
}

void test_c6_qg6()
{
  int edge[10], i;

  for (i = 1; i < 10; i++) edge[i] = 0;
  edge[3] = 1;
  edge[4] = 1;
  edge[7] = 1;
  if (LINE == 20) LINE = 5;

  test_colsg(edge);
}

void test_c6_qg7()
{
  int edge[10], i;

  for (i = 1; i < 10; i++) edge[i] = 0;
  edge[1] = 1;
  edge[2] = 1;
  edge[7] = 1;
  if (LINE == 20) LINE = 5;

  test_colsg(edge);
}

void print_first_rows ()
{
  int x, y, z;
  int i = 0;
  int A[15],B[15];

  printf("\nFirst Row:\n");

  while (i < QGROUP) {
    y = ((i + 15) < QGROUP)? 15 : QGROUP-i;
    printf("            x:");
    for (x = 0; x < y; x++) print_num(x + i);
    printf("\n A = 0 *123 x:");
    for (x = 0; x < y; x++) print_num(A[i]=GETNUM(0, x + i, 0));

    for (z = 1; z < 6; z++) {
      printf("\nB%d = 0 *%d x:", z, conjugate_num(z));
      for (x = 0; x < y; x++) 
	print_num(B[x] = GETNUM(0, (x + i), z));
      printf("\n C%d = A - B%d :", z, z);
      for (x = 0; x < y; x++) 
	print_num((A[x] < 0 || A[x] >= m || B[x] >= m)? -1 : 
		  ABG_f[A[x]][ABG_g[B[x]]]);
      printf("\n\n");
    }
    i += 15;
  }

  if (INCOMPLETE) {
    printf("First Column:\n           x:");
    for (x = 0; x < INCOMPLETE; x++) print_num(x + m);
    printf("\nA = x *123 0:");
    for (x = 0; x < INCOMPLETE; x++) print_num(A[x] = GETNUM(x + m, 0, 0));

    for (z = 1; z < 6; z++) {
      printf("\nB%d = x *%d 0:", z, conjugate_num(z));

      for (x = 0; x < INCOMPLETE; x++) 
	print_num(B[x] = GETNUM((x + m), 0, z));

      printf("\n C%d = A - B%d :", z, z);
      for (x = 0; x < INCOMPLETE; x++) 
	print_num((A[x] < 0 || A[x] >= m || B[x] >= m)? -1 :
		  ABG_f[A[x]][ABG_g[B[x]]]);
      printf("\n");
    }
  }
}

void print_first_row ()
{
  int x, y, k;
  int A[MAX_SQUARE1], B[MAX_SQUARE1];

  for (k = 0; k < max_seed; k++) {
  int i = 0;
  printf("\n Row #%d:\n", k);

  while (i < QGROUP) {
    y = ((i + 15) < QGROUP)? 15 : QGROUP-i;
    printf("           x:");
    for (x = 0; x < y; x++) print_num(x + i);
    printf("\nA = %d *123 x:", k);
    for (x = 0; x < y; x++) print_num(A[x] = get123(k, x + i));
    if (QUEEN == 0 || QUEEN == 20 || QUEEN == 31) printf("\nB = %d *213 x:", k); 
    else if (QUEEN == 1 || QUEEN == 21) printf("\nB = %d *321 x:", k); 
    else printf("\nB = %d *312 x:", k);
    for (x = 0; x < y; x++) 
      print_num(B[x] = ((QUEEN == 0 || QUEEN == 20 || QUEEN == 31)? 
			get213(k, (x + i)) :
			((QUEEN == 1 || QUEEN == 21)? 
			 get321(k, (x + i)) :
			 get312(k, (x + i)))));
    printf("\nC =  A - B  :");
    for (x = 0; x < y; x++) 
      print_num((A[x] < 0 || A[x] >= m || B[x] >= m)? -1 :
		ABG_f[A[x]][ABG_g[B[x]]]);
    printf("\n\n");
    i += 15;
  }

  if (INCOMPLETE) {
    printf("\n Column #%d:\n           x:", k);
    for (x = 0; x < INCOMPLETE; x++) print_num(x + m);
    printf("\nA = x *123 %d:", k);
    for (x = 0; x < INCOMPLETE; x++) print_num(A[x] = get123(x + m, k));
    if (QUEEN == 0 || QUEEN == 20 || QUEEN == 31) printf("\nB = x *213 %d:", k); 
    else if (QUEEN == 1 || QUEEN == 21) printf("\nB = x *321 %d:", k); 
    else printf("\nB = x *312 %d:", k);
    for (x = 0; x < INCOMPLETE; x++) 
      print_num(B[x] = ((QUEEN == 0 || QUEEN == 20 || QUEEN == 31)? 
			get213((x + m), k) :
			((QUEEN == 1 || QUEEN == 21)? 
			 get321((x + m), k) :
			 get312((x + m), k))));
    printf("\nC =  A - B  :");
    for (x = 0; x < INCOMPLETE; x++) 
      print_num((A[x] < 0 || A[x] >= m || B[x] >= m)? -1 :
		ABG_f[A[x]][ABG_g[B[x]]]);
    printf("\n");
  }
  }
}

void print_first_row2 ()
{
  int x, y;
  int i = 0;
  int A[MAX_SQUARE1], B[MAX_SQUARE1];

  printf("\nFirst Row:\n");

  while (i < QGROUP) {
    y = ((i + 15) < QGROUP)? 15 : QGROUP-i;
    printf("           x:");
    for (x = 0; x < y; x++) print_num(x + i);
    printf("\n   A = 0 * x:");
    for (x = 0; x < y; x++) print_num(A[x] = get123(0, x + i));
    printf("\n   B = 0 . x:"); 

    for (x = 0; x < y; x++) 
      print_num(B[x] = get123_2(0, x + i));
    printf("\n   C = A - B:");
    for (x = 0; x < y; x++) 
      print_num((A[x] < 0 || A[x] >= m || B[x] >= m)? -1 :
		ABG_f[A[x]][ABG_g[B[x]]]);
    printf("\n\n");
    i += 15;
  }

  if (INCOMPLETE) {
    printf("\nFirst Column:\n           x:");
    for (x = 0; x < INCOMPLETE; x++) print_num(x + m);
    printf("\n   A = x * 0:");
    for (x = 0; x < INCOMPLETE; x++) print_num(A[x] = get123(x + m, 0));
    printf("\n   B = x . 0:"); 
    for (x = 0; x < INCOMPLETE; x++) 
      print_num(B[x] = get123_2(x + m, 0));
    printf("\n   C = A - B:");
    for (x = 0; x < INCOMPLETE; x++) 
      print_num((A[x] < 0 || A[x] >= m || B[x] >= m)? -1 :
		ABG_f[A[x]][ABG_g[B[x]]]);
    printf("\n");
  }
}

void print_q24_5tuple ()
{
  int i;

  printf("\n5-tuples:\n");

  for (i = m; i < QGROUP; i++) {
    print_num(i);
    print_num(0);
    print_num(get123(i, 0));
    print_num(get123(0, i));
    print_num(get123_2(i, 0));
    printf("\n");
  }

  for (i = 0; i < QGROUP; i++) {
    print_num(0);
    print_num(i);
    print_num(get123(0, i));
    print_num(get123(i, 0));
    print_num(get123_2(0, i));
    printf("\n");
  }
}

void test_qg81_new()
{
  int edge[10], i;

  for (i = 1; i < 10; i++) edge[i] = 0;
  edge[3] = 1;
  edge[4] = 1;
  edge[8] = 1;
  edge[9] = 1;
  if (LINE == 20) LINE = 5;

  test_colsg(edge);
}

void test_co_cycle()
{
  int edge[10], i, j;

  /* decompose QUEEN into a list of digits */
  for (i = 1; i < 10; i++) edge[i] = 0;
  i = QUEEN;
  while (i) {
    j = i % 10;
    i = (i - j)/10;
    edge[j] = 1;
  }

  test_colsg(edge);
}

void test_all ()
{
  int edge[10], i;
  for (i = 1; i < 10; i++) edge[i] = 1;
  test_colsg(edge);
}
	  
void test_colsg (edge)
     int edge[];
{ 
  int i, j;

  fill_triple2();

  j = 0;
  for (i = 1; i < 10; i++) if (edge[i] == 1) {
    if (i < 6) j += test_co(0, i);
    else if (i < 9) j += test_co(1, i-4);
    else j += test_co(2, 3);
  }
  printf("\n");

  if (j != 3 && (QUEEN == 69 || QUEEN == 79 || QUEEN == 89)) { Branch_succ--; Branch_fail++; }
  if (j != 2 && (QUEEN == 78 || QUEEN == 88)) { Branch_succ--; Branch_fail++; }
}

void print_co_squares ()
{
  int k, i, j, x;

  printf("\nConjugates:\n");

  for (x = 0; x < 6; x++) {
    printf("\n*%d|", conjugate_num(x));
    for (i = 0; i < n; i++) print_num(i);
    printf("\n----+-");
    for (i = 0; i < n; i++) printf("---");
    printf("\n"); 

    for (i = 0; i < n; i++) {
      int goodi = (NHOLE && i < m)? (i % NHOLE) : i;

      print_num(i); printf(" |");
      if (i < m) k = n; else k = m;
      for (j = 0; j < k; j++) 
	if (NHOLE && (j < m) && (j % NHOLE == goodi))
	  printf("   ");
	else
	  print_num(Triple[i][j][x]);
      printf("\n");
    }
  }
}

/* individual testing */

void test_qg ()
{
  if (QUEEN == 0) test_qg0();
  else if (QUEEN == 1) test_qg1(); 
  else if (QUEEN == 2) test_qg2();
  else if (QUEEN == 3) { test_qg3(); /* test_c6_qg3(); test_qgd0(); */ }
  else if (QUEEN == 4) { test_qg4(); /* test_c6_qg4(); test_qgd0(); */ }
  else if (QUEEN == 45 || QUEEN == 46) { test_qg45(); }
  else if (QUEEN == 5) { test_qg5(); }
  else if (QUEEN == 6) /* test_qg6(); */ test_c6_qg6();
  else if (QUEEN == 7) test_qg7();
  else if (QUEEN == 8) { test_qg8(); /* test_qgd0(); */ }
  else if (QUEEN == 81) test_qg81_new();
  else if (QUEEN == 9) { test_qg91(); test_qg0(); }
  else if (QUEEN == 91) test_qg91();
  else if (QUEEN == 92) { test_qg91(); 
			  if (test_qg0()) { Branch_succ--; Branch_fail++; }}
  else if (QUEEN == 10) test_qgd0();
  else if (QUEEN == 100) { test_qg101(); test_qg102(); }
  else if (QUEEN == 101) test_qg101();
  else if (QUEEN == 102) test_qg102();
  else if (QUEEN == 104) test_orthogonal2();
  else if (QUEEN > 110) test_co_cycle();
}

int test_qg0()
{
  int x, y, z, t;

  for (x = 0; x < n; x++) 
    for (y = (x >= m)? m-1 : n-1; y >= 0; y--) if (is_same_hole(x, y) == 0)
      for (z = x+1; z < n; z++) 
	for (t = (z >= m)? m-1 : n-1; t >= 0; t--)  
	  if (is_same_hole(z, t) == 0 &&
	      Lsquare[y][x] == Lsquare[t][z] &&
	      Lsquare[x][y] == Lsquare[z][t]) {
	    printf("\nCounter example for QG0:");
	    printf("\n    %d *123 %d = %d *123 %d = %d", 
		   x, y, z, t, Lsquare[x][y]);
	    printf("\n    %d *213 %d = %d *213 %d = %d\n", 
		   x, y, z, t, Lsquare[y][x]);
	    return 1;
	  }
  return 0;
}

int test_qgd0()
{
  int x, y, z, t;

  for (x = 0; x < n; x++) 
    for (y = (x >= m)? m-1 : n-1; y >= 0; y--) if (is_same_hole(x, y) == 0)
      for (z = x+1; z < n; z++) 
	for (t = (z >= m)? m-1 : n-1; t >= 0; t--)  
	  if (is_same_hole(z, t) == 0 &&
	      Lsquare[x][y] == Lsquare[z][t] &&
	      Lsquare[n1-y][n1-x] == Lsquare[n1-t][n1-z]) {
	    printf("\nCounter example for QG0:");
	    printf("\n    %d *123 %d = %d *123 %d = %d", 
		   x, y, z, t, Lsquare[x][y]);
	    printf("\n    %d *d21 %d = %d *d21 %d = %d\n", 
		   x, y, z, t, Lsquare[n1-y][n1-x]);
	    return 1;
	  }
  Branch_succ += 10000; 
  return 0;
}

void test_qg1()
{
  int i, x, y, z, t;

  for (x = 0; x < n; x++) 
    for (y = (x >= m)? m-1 : n-1; y >= 0; y--) if (is_same_hole(x, y) == 0)
      for (z = x+1; z < n; z++) 
	for (t = (z >= m)? m-1 : n-1; t >= 0; t--) 
	  if (is_same_hole(z, t) == 0) {
	    for (i = (y < m && t < m)? n-1 : m-1; i >= 0; i--) 
	      if (is_same_hole(i, y) == 0 && is_same_hole(i, t) &&
		  Lsquare[i][y] == x &&
		  Lsquare[i][t] == z &&
		  Lsquare[x][y] == Lsquare[z][t]) {
		printf("\nCounter example for QG1:");
		printf("\n    %d *123 %d = %d *123 %d = %d", 
		       x, y, z, t, Lsquare[x][y]);
		printf("\n    %d *321 %d = %d *321 %d = %d\n", 
		       x, y, z, t, i);
		return;
	    }
	  } else { /* if (is_same_hole(z, t)) .. */
	    if (is_same_hole(z, y) == 0 && is_same_hole(z, x) &&
		Lsquare[x][y] == z &&
		Lsquare[t][y] == x) {
	      printf("\nCounter example for QG1:");
	      printf("\n    %d *123 %d = %d *123 %d = %d", 
		     x, y, z, z, z);
	      printf("\n    %d *321 %d = %d *321 %d = %d\n", 
		     x, y, t, t, t);
	      return;
	    }
	  }
}

void test_qg2()
{
  int i, x, y, z, t;

  for (x = 0; x < n; x++) 
    for (y = (x >= m)? m-1 : n-1; y >= 0; y--) if (is_same_hole(x, y) == 0)
      for (z = x+1; z < n; z++) 
	for (t = (z >= m)? m-1 : n-1; t >= 0; t--) if (is_same_hole(z, t) == 0)
	  for (i = (y < m && t < m)? n-1 : m-1; i >= 0; i--) 
	    if (is_same_hole(i, y) == 0 && is_same_hole(i, t) &&
		Lsquare[y][i] == x &&
		Lsquare[t][i] == z &&
		Lsquare[x][y] == Lsquare[z][t]) {
	      printf("\nCounter example for QG2:");
	      printf("\n    %d *123 %d = %d *123 %d = %d", 
		     x, y, z, t, Lsquare[x][y]);
	      printf("\n    %d *312 %d = %d *312 %d = %d\n", 
		     x, y, z, t, i);
	      return;
	    }
}

void test_qg3()
{
  int i, j;

  for (i = 0; i < n; i++) 
    for (j =  (i < m)? n-1 : m-1; j >= 0; j--) 
      if (is_same_hole(i, j) == 0 &&
	  Lsquare[Lsquare[i][j]][Lsquare[j][i]] != i) {
	int i_j = Lsquare[i][j];
	int j_i = Lsquare[j][i];
	printf("Counter example for QG3:\n");
	printf("   %d * %d = %d, %d * %d = %d but %d * %d = %d != %d\n\n",
	       i, j, i_j, j, i, j_i, i_j, j_i, Lsquare[i_j][j_i], i);
	return;
      }
}

void test_qg4()
{
  int i, j;

  for (i = 0; i < n; i++) 
    for (j =  (i < m)? n-1 : m-1; j >= 0; j--) 
      if (is_same_hole(i, j) == 0 &&
	  Lsquare[Lsquare[i][j]][Lsquare[j][i]] != j) {
	int i_j = Lsquare[i][j];
	int j_i = Lsquare[j][i];
	printf("Counter example for QG4:\n");
	printf("   %d * %d = %d, %d * %d = %d but %d * %d = %d != %d\n\n",
	       i, j, i_j, j, i, j_i, i_j, j_i, Lsquare[i_j][j_i], j);
	return;
      }
}

void test_qg45()
{
  int i, j, res[10][10], total=0;
  int pair=(QGROUP&1)? 4 : 3;

  if (QUEEN == 46) pair = 3;

  for (i = 0; i < 10; i++) for (j = 0; j < 10; j++) res[i][j] = 0;

  for (i = 0; i < n; i++) 
    for (j = 0; j < n; j++) {
      int x = Lsquare[i][j];
      int y = Lsquare[j][i];
      if ((QUEEN == 45 && 
	   !(((x&1) == 0 && y == x+1) || ((y&1) == 0 && x == y+1))) ||
	  (QUEEN == 46 && x != y)) {
	if (res[x][y] == 0) {
	  res[x][y] = 1;
	  total++;
	}}
      if (total > pair) { Branch_succ--; Branch_fail++; 
      /* print_square(0);
	 printf("total=%d, pair=%d\n", total, pair);  */
      return; }
    }

  if (total < pair) { Branch_succ--; Branch_fail++; }
  /* print_square(0);
     printf("total=%d, pair=%d\n", total, pair); */
}

void test_qg5()
{
  int i, j;

  for (i = 0; i < n; i++) 
    for (j =  (i < m)? n-1 : m-1; j >= 0; j--) 
      if (is_same_hole(i, j) == 0 &&
	  Lsquare[Lsquare[Lsquare[i][j]][i]][i] != j) {
	int i_j = Lsquare[i][j];
	int i_j_i = Lsquare[i_j][i];
	printf("Counter example for QG5:\n");
	printf("   %d * %d = %d, %d * %d = %d but %d * %d = %d != %d\n\n",
	       i, j, i_j, i_j, i, i_j_i, i_j_i, i, Lsquare[i_j_i][i], j);
	return;
      }
}

void test_qg6()
{
  int i, j;

  for (i = 0; i < n; i++) 
    for (j =  (i < m)? n-1 : m-1; j >= 0; j--) 
      if (is_same_hole(i, j) == 0 &&
	  Lsquare[Lsquare[i][j]][j] != Lsquare[i][Lsquare[i][j]]) {
	int i_j = Lsquare[i][j];
	printf("Counter example for QG6:\n");
	printf("   %d * %d = %d, %d * %d = %d != %d * %d = %d\n\n",
	       i, j, i_j, i_j, j, Lsquare[i_j][j], i, i_j, Lsquare[i][i_j]);
	return;
      }
}

void test_qg7()
{
  int i, j;

  for (i = 0; i < n; i++) 
    for (j =  (i < m)? n-1 : m-1; j >= 0; j--) 
      if (is_same_hole(i, j) == 0 &&
	  Lsquare[Lsquare[i][j]][i] != Lsquare[j][Lsquare[i][j]]) {
	int i_j = Lsquare[i][j];
	printf("Counter example for QG7:\n");
	printf("   %d * %d = %d, %d * %d = %d != %d * %d = %d\n\n",
	       i, j, i_j, i_j, i, Lsquare[i_j][i], j, i_j, Lsquare[j][i_j]);
	return;
      }
}

void test_qg8()
{
  int i, j;

  for (i = 0; i < n; i++) 
    for (j =  (i < m)? n-1 : m-1; j >= 0; j--) 
      if (is_same_hole(i, j) == 0 && 
	  Lsquare[i][Lsquare[i][j]] != Lsquare[j][i]) {
	int i_j = Lsquare[i][j];
	printf("Counter example for QG8:\n");
	printf("   %d * %d = %d, %d * %d = %d != %d * %d = %d\n\n",
	       i, j, i_j, i, i_j, Lsquare[i][i_j], j, i, Lsquare[j][i]);
	return;
      }
}

void test_qg91()
{
  int i, j;

  for (i = 0; i < n; i++) 
    for (j =  (i < m)? n-1 : m-1; j >= 0; j--) 
      if (is_same_hole(i, j) == 0 &&
	  Lsquare[Lsquare[i][j]][i] != j) {
	  int i_j = Lsquare[i][j];
	  printf("Counter example for QG91:\n");
	  printf("   %d * %d = %d, %d * %d = %d != %d\n\n",
		 i, j, i_j, i_j, i, Lsquare[i_j][i], j);
	  return;
	}
}

void test_qg101()
{
  int i, j;

  for (i = 0; i < n; i++) 
    for (j =  (i < m)? n-1 : m-1; j >= 0; j--) 
      if (is_same_hole(i, j) == 0 && 
	  Lsquare[Lsquare[i][j]][j] != i) {
	  int i_j = Lsquare[i][j];
	  printf("Counter example for QG10.1:\n");
	  printf("   %d * %d = %d, %d * %d = %d != %d\n\n",
		 i, j, i_j, i_j, j, Lsquare[i_j][j], i);
	  return;
	}
}

int test_qg102 ()
     /* test x * (y * x) = y * (x * y) */
{
  int x, y;

  for (x = n-1; x >= 0; x--) {
    int x1 = (NHOLE)? x % NHOLE : x;
    for (y = n-1; y >= 0; y--) {
      int y1 = (NHOLE)? y % NHOLE : y;
      if (x1 != y1) {
	int xy = Lsquare[x][y];
	int yx = Lsquare[y][x];
	if (NHOLE == 0 || ((x1 != yx % NHOLE) && (y1 != xy % NHOLE))) {
	    if (Lsquare[x][yx] != Lsquare[y][xy]) {
	      printf("Counter example for QG10.2:\n");
      printf("   %d * %d = %d, %d * %d = %d, %d * %d = %d != %d * %d = %d\n\n",
		     x, y, xy, y, x, yx, x, yx, Lsquare[x][yx], 
		     y, xy, Lsquare[y][xy]);
	      return 0;	      
	    }
	  }}}}

  return 1;
}

int test_orthogonal2 (num)
     int num;
{
  int x, y, z, t;
  int flag = 1;

  if (num > 1) print_square(3); 

  for (x = 0; x < n; x++) {
    int goodx = (NHOLE == 0 || x >= m)? 1 : x % NHOLE;
    for (y = (x >= m)? m-1 : n-1; y >= 0; y--) {
      int goody = (NHOLE == 0 || y >= m)? 2 : y % NHOLE;
      if (goodx != goody) 
	for (z = x+1; z < n; z++) {
	  int goodz = (NHOLE == 0 || z >= m)? 3 : z % NHOLE;
	  for (t = (z >= m)? m-1 : n-1; t >= 0; t--) {
	    int goodt = (NHOLE == 0 || t >= m)? 4 : t % NHOLE;
	    if (goodz != goodt) {
	      if (Lsquare[x][y] == Lsquare[z][t] &&
		  Lsquare2[x][y] == Lsquare2[z][t]) {
		printf("\nCounter example for Orthogonality:");
		printf("\n    %d * %d = %d * %d = %d", 
		       x, y, z, t, Lsquare[x][y]);
		printf("\n    %d . %d = %d . %d = %d\n", 
		       x, y, z, t, Lsquare2[x][y]);
		flag=0;
	      }

	      if (num > 1 &&
		  Lsquare[x][y] == Lsquare[z][t] &&
		  Lsquare3[x][y] == Lsquare3[z][t]) {
		printf("\nCounter example for Orthogonality:");
		printf("\n    %d * %d = %d * %d = %d", 
		       x, y, z, t, Lsquare[x][y]);
		printf("\n    %d + %d = %d + %d = %d\n", 
		       x, y, z, t, Lsquare3[x][y]);
		flag=0;
	      }

	      if (num > 1 &&
		  Lsquare2[x][y] == Lsquare2[z][t] &&
		  Lsquare3[x][y] == Lsquare3[z][t]) {
		printf("\nCounter example for Orthogonality:");
		printf("\n    %d . %d = %d . %d = %d", 
		       x, y, z, t, Lsquare2[x][y]);
		printf("\n    %d + %d = %d + %d = %d\n", 
		       x, y, z, t, Lsquare3[x][y]);
		flag=0;
	      }
	    }
	  }}}}
  return flag;
}

int read_two ()
{
  read_in_square("two.sqs", 0);
  read_in_square("two.sqs", 1);
  return test_orthogonal2();
}

void open_input_sqs (name) 
     char *name;
{ 
  int k;

  Input_sqs = fopen(name, "r");
  if (Input_sqs == NULL) {
    printf("File %s doesn't exist!\n", name);
    exit(1);
  }
  /* skip the first number */
  read_int ( Input_sqs, &k );
}

void read_in_square (name, which)
     char name[]; int which;
{
  int i, j, k, s;

  if (Input_sqs == NULL) open_input_sqs(name);
  if ((s = read_int ( Input_sqs, &k )) == 3) {
    printf("The input square file reaches the end!\n");
    exit(1);
  }

  for (i = 0; i < QGROUP; i++)
    for (j = 0; j < QGROUP; j++) {
      s = read_int ( Input_sqs, &k );
      if (s == 0) k = -k;
      /* printf("<%d,%d,%d>", i, j, k); */
      if (which) 
	Lsquare2[i][j] = k;
      else
	Lsquare[i][j] = Lsquare2[i][j] = k;
    }

  printf("Read in a square:\n");
  print_square(1);
}

int getxyz(x, y, z) { return Triple[x][y][z]; }
int get0123(x, y) { return Lsquare[x][y]; }

int get123 (x, y)
     int x, y;
{
  if ((NHOLE > 0) && (x < m) && (y < m) && ((x - y) % NHOLE == 0))
    return -1;
  else 
    return Lsquare[x][y];
}

int get123_2 (x, y)
     int x, y;
{
  if ((NHOLE > 0) && (x < m) && (y < m) && ((x - y) % NHOLE == 0))
    return -1;
  else 
    return Lsquare2[x][y];
}

int get213(x, y)
     int x, y;
{
  if ((NHOLE > 0) && (x < m) && (y < m) && ((x - y) % NHOLE == 0))
    return -1;
  else 
    return Lsquare[y][x];
}

int get321 (x, y)
     int x, y;
{
  if ((NHOLE > 0) && (x < m) && (y < m) && ((x - y) % NHOLE == 0))
    return -1;
  else {
    int z;
    for (z = 0; z < QGROUP; z++) 
      if (Lsquare[z][y] == x) return z;
  }
  return(-1);
}

int get312 (x, y)
     int x, y;
{
  if ((NHOLE > 0) && (x < m) && (y < m) && ((x - y) % NHOLE == 0))
    return -1;
  else {
    int z;
    for (z = 0; z < QGROUP; z++) 
      if (Lsquare[y][z] == x) return z;
  }
  return(-1); 
}

void key2triple (i, x, y, z)
     int i, *x, *y, *z;
{
  *z = (--i) % QGROUP;
  i = (i - *z) / QGROUP;
  *y = i % QGROUP;
  *x = (i - *y) / QGROUP;
}

void print_cell(i)
     int i;
{ 
  int x, y, z;
  
  key2triple(i, &x, &y, &z);
  
  if (Value[i] == TT)
    printf(">>>>>>>>>>> %d * %d == %d\n", x, y, z);
  else
    printf(">>>>>>>>>>> %d * %d != %d\n", x, y, z);
}

void transpose_square2 ()
{
  int x, y;

  for (x = 0; x < n; x++)
    for (y = x+1; y < n; y++) {
      int z = Lsquare2[x][y];
      Lsquare2[x][y] = Lsquare2[y][x]; 
      Lsquare2[y][x] = z; 
    }
}
 
void conjugate321_square ()
{
  int x, y;

  for (x = 0; x < n; x++)
    for (y = 0; y < n; y++) {
      int z = Lsquare[x][y];
      Lsquare2[z][y] = x;
    }
}
 
int qg00 (cl_arr, sign_arr, load)
     int cl_arr [], sign_arr [];
     int load;
     /* read-in a square and generate orthogonal clauses 
	between the current and the read-in squares */
{
  int x, y, z, u, v, w;

  if (load) read_in_square("sqs.in", 0);

  for (x = n1; x > 0; x--)
    for (y = (x >= m)? m-1 : n1; y >= 0; y--) if (x != y) {

      for (z = (x < m && y < m)? n1 : m-1; z >= 0; z--) 
	if (z != x && z != y && 
	    Lsquare2[y][y] == y &&
	    Lsquare2[x][z] == y && 
	    insert_cl_2(TRIPLE2KEY(y, y, y),
			TRIPLE2KEY(x, z, y), 
			0, cl_arr, sign_arr))
	  return 1;

      for (z = x-1; z >= 0; z--) 
	for (w = (z >= m)? m-1 : n1; w >= 0; w--) if (y != w && z != w) 
	  for (u = (x < m && y < m && z < m && w < m)? n1 : m-1; u >= 0; u--) 
	    for (v = (x < m && y < m && z < m && w < m)? n1 : m-1; v >= 0; v--) 
	      if (Lsquare2[x][y] == u &&
		  Lsquare2[z][w] == u && 
		  insert_cl_2(TRIPLE2KEY(x, y, v), 
			      TRIPLE2KEY(z, w, v), 
			      0, cl_arr, sign_arr))
		return 1;
    }

  return 0;
}

sq_read_square ()
{
  int i, j, k;
  char name[20];

  sprintf(name, "l%d.in", LINE % 1000);
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
      if (is_same_hole(i, j) == 0) {
	if (k < 0) { 
	  printf("Bad input: %d\n", k); exit(1); 
	} else {
	  printf("%d ", k);
	  Lsquare[i][j] = k;
	}
      }
    }
  }
  printf("\n\n");

  test_qg3();
  test_dia();

  return 0;
}

void shuffle_sq (a, b)
     int a, b;
{
  int i, j;

  for (i = 0; i < n; i++) {
    j = Lsquare[i][a];
    Lsquare[i][a] = Lsquare[i][b];
    Lsquare[i][b] = j;
  }

  for (i = 0; i < n; i++) {
    j = Lsquare[a][i];
    Lsquare[a][i] = Lsquare[b][i];
    Lsquare[b][i] = j;
  }

  for (i = 0; i < n; i++)
    for (j = 0; j < n; j++)
      if (Lsquare[i][j] == b) Lsquare[i][j] = a;
      else if (Lsquare[i][j] == a) Lsquare[i][j] = b;

  printf("Switching row %d with row %d:\n", a, b);
  if (TRACE > 1) print_square(0);
}

extern long random_seed;
void shuffle_square2 ()
{
  int i;
  long a, b;

  for (a = 0; a < n; a++)
    for (b = 0; b < n; b++)
      Lsquare[a][b] = Lsquare2[a][b];
  for (i = 0; i < n; i++) {
    a = good_random() % m;
    b = good_random() % m;
    if (a != b) shuffle_sq((int) a, (int) b);
  }

  print_output_sq();
}
