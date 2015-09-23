/* Global variables */
#include <stdio.h>
#include <sys/time.h>
#include <sys/resource.h>  

char *T[10][10000];
int N[10], n;
int V[10];

main(argc, argv)
     int argc;
     char **argv;
{
  int i;

  if (argc > 1) 
    n = str_int(argv[1], 0);
  else {
    printf("Usage: term <n>\n");
    exit(0);
  }

  for (i = 0; i <= n; i++) {
    N[i] = 0; V[i] = 1;
  }

  dp(n, 0);
  var_perm();
}

int dp (i, f)
     int i, f;
{ 
  if (N[i] == 0) {
    if (i == 1) {
      T[i][0] = "_";
      N[i] = 1;
    } else if (i == 2) {
      T[i][0] = "f(_,_)";
      N[i] = 1;
    } else {
      int j, x, y, m;
      m = 0;
      for (j = i-1; j > 0 && (f || j+j >= i); j--) {
	dp(j, 0);
	dp(i-j, 0);
	for (x = 0; x < N[j]; x++)
	  for (y = 0; y < N[i-j]; y++) {
	    char z[50];
	    sprintf(z, "f(%s,%s)", T[j][x], T[i-j][y]); 
	    T[i][m++] = strdup(z);
	  }
      }
      N[i] = m;
    }
  }
}

int str_int (s, i)
     char s[];
     int i;
{
  int n = 0;
  for( ; s[i] >= '0' && s[i] <= '9'; i++)
    n = n * 10 + s[i] - '0';

  return n;
} 

int var_perm ()
{
  int i;

  for (i = 0; i < n; i++) V[i] = 1;
  while (increase()) {
    if (lessthan(5)) 
      print_TV();
  }
}

int lessthan (m)
     int m;
{
  int x1, x2, x3, i;
  x1=x2=x3=0;
  for (i = 0; i < n; i++)
    if (V[i] == 1) { x1++; if (x1 >= m) return 0; }
    else if (V[i] == 2) { x2++; if (x2 >= m) return 0; }
    else if (V[i] == 3) { x3++; if (x3 >= m) return 0; }
  if (x1 > 0) {
    if (x2 > x3) return 1;
    else if (x2 == x3)
      for (i = 0; i < n; i++)
	if (V[i] == 2) return 1;
	else if (V[i] == 3) return 0;
  }
  return 0;
}
  
int increase ()
{
  int i;
  for (i = 0; i < n; i++)
    if (V[i] == 3) V[i] = 1;
    else { V[i]++; return 1; }
  return 0;
}

print_TV()
{
  int j, i, k;
  char *s;
  for (i = 0; i < N[n]; i++) {
    s = T[n][i];
    k = 0;
    for (j = 0; j < 200; j++)
      if (s[j] == '_') {
	printf("x%d", V[k]);
	k++;
      } else if  (s[j] == '\0') 
	j = 200;
    else
      printf("%c", s[j]);
    printf("\n");
  }
}
