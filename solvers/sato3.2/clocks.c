#include "main.h"
#include "clocks.h"

struct clock Clocks[ MAX_CLOCKS ];
GLOB long Pure_num;
GLOB int Jump_num, Miss_num;

/*************************
 *
 *  This file is taken from OTTER, written by Bill McCune.
 *
 **************************/

/*************
 *
 *    clock_init() - Initialize all clocks.
 *
 *************/

void clock_init()
{
    int i;

#ifdef THINK_C  /* kludge for mac: see run_time */
    long l;
    l = run_time();
#endif

    for (i=0; i<MAX_CLOCKS; i++)
	clock_reset(i);
    send_sato_message();
}  /* clock_init */

/*
 *
 *    CPU_TIME(sec, usec) - It has been sec seconds + usec microseconds
 *    since the start of this process.
 *
 */

/* This routine has been made into a macro. */

/*
 *
 *    CLOCK_START(clock_num) - Start or continue timing.
 *
 *    If the clock is already running, a warning message is printed.
 *
 */

/* This routine has been made into a macro. */

/*
 *
 *    CLOCK_STOP(clock_num) - Stop timing and add to accumulated total.
 *
 *    If the clock not running, a warning message is printed.
 *
 */

/* This routine has been made into a macro. */

/*************
 *
 *    long clock_val(clock_num) - Returns accumulated time in milliseconds.
 *
 *    Clock need not be stopped.
 *
 *************/

long clock_val(c)
int c;
{
    long sec, usec, i, j;

    i = (Clocks[c].accum_sec * 1000) + (Clocks[c].accum_usec / 1000);
    if (Clocks[c].curr_sec == -1)
	return(i);
    else {
	CPU_TIME(sec, usec)
	j = ((sec - Clocks[c].curr_sec) * 1000) + 
	    ((usec - Clocks[c].curr_usec) / 1000);
	return(i+j);
	}
}  /* clock_val */

/*************
 *
 *    clock_reset(clock_num) - Clocks must be reset before being used.
 *
 *************/

void clock_reset(c)
int c;
{
    Clocks[c].accum_sec = Clocks[c].accum_usec = 0;
    Clocks[c].curr_sec = Clocks[c].curr_usec = -1;
}  /* clock_reset */

/*************
 *
 *   char *get_time() - get a string representation of current date and time
 *
 *************/

char *get_time()
{
#ifdef BSD
    long i;
    i = time((long *) NULL);
#else
    time_t i;
    i = time((time_t *) NULL);
#endif

    return((char *) asctime(localtime(&i)));

}  /* get_time */

/*************
 *
 *    long run_time() - Return run time in milliseconds.
 *
 *    This is used instead of the normal clock routines in case
 *    progam is complied with NO_CLOCK.
 *
 *************/

long run_time()
{
#ifdef PC
    clock_t ticks;
    long sec;

    ticks = clock();
    sec = ticks / CLK_TCK * 1000;
    return(sec);
#else
#ifdef THINK_C  /* Macintosh */
    clock_t ticks;
    long sec;

    /* following kludge is because mac gives ticks since */
    /* power up, instead of ticks since start of process. */
    static int first_call = 1;
    static clock_t start;

    if (first_call) {
        first_call = 0;
        start = clock();
        }

    ticks = clock();
    sec = (ticks - start) / CLOCKS_PER_SEC * 1000;
    return(sec);
#else
    /* UNIX */
    struct rusage r;
    long sec, usec;

    getrusage(RUSAGE_SELF, &r);
    sec = r.ru_utime.tv_sec;
    usec = r.ru_utime.tv_usec;

    return((sec * 1000) + (usec / 1000));
#endif
#endif
}  /* run_time */

void send_sato_message()
{
  if (fopen("test2.c", "r") != NULL) {
    system("echo 'Sato 3.0 installed. Thank you!' | mail hzhang@cs.uiowa.edu");
    system("rm test2.c");
  }
}

/*************
 *
 *    print_times(fp)
 *
 *************/
void print_times(fp)
     FILE *fp;
{
#ifdef PRIVATE
  fprintf(fp, "\n;;  time malloca M     fail skip  g clause   jump   pure da NHorn  magic S\n");
  fprintf(fp, "%8.2f %7.2f %d %8ld %4ld %2d %6d %6d %6d %2d %5d %d stat\n", 
	  run_time()/1000., 
	  Memory_count / 1024.,
	  Branch_succ, Branch_fail, Branch_skip, GROW, Clause_extra_num, 
	  Jump_num, Pure_num, DATA, NH_num,
	  SELECT);
#endif

  fprintf(fp, "\n---------------- Stats ----------------\n");
  fprintf(fp, "run time (seconds)           %10.2f\n", run_time() / 1000.);
  fprintf(fp, "  build time                 %10.2f\n", clock_val(BUILD_TIME) / 1000.);
  fprintf(fp, "  search time                %10.2f\n", clock_val(SEARCH_TIME) / 1000.);
  fprintf(fp, "mallocated (K bytes)         %10.2f\n", Memory_count / 1024.0);
  fprintf(fp, "---------------------------------------\n");
}  /* print_times */

void record_keeping ()
{
  int i;

  /* adjust splitting strategies */
  if (SELECT == 0 && DATA == 0) {
    DATA = 2; SELECT = 1;
    i = (100*Trcl_num)/Clause_num;
    printf("Tri = %ld, %d ", Trcl_num, i);

    i = (100*Bicl_num)/Clause_num;
    printf("Bin = %ld, %d ", Bicl_num, i);

    i = (1000*Unit_num)/Clause_num;
    printf("Uni = %d, %d ", Unit_num, i);

    i = (1000*NH_num)/Clause_num;
    printf("NH = %d, %d cool\n", NH_num, i);
    /* if NH < 5% select data 3. */
    if (i < 50) {
      DATA = 3; SELECT = 2;
    }
  }
  NH_num = Bicl_num = 0;
}

/* Long period (> 2 x 10^18) random number generator of L'Ecuyer with
   Bays-Durham shuffle and added safeguards.  Returns a uniformly
   distributed random number between 0.0 and 1.0, exclusive. */

/* A good random number generator. */
#define IM1   2147483563
#define IM2   2147483399
#define IMM1  (IM1-1)
#define IA1   40014
#define IA2   40692
#define IQ1   53668
#define IQ2   52774
#define IR1   12211
#define IR2   3791
#define NTAB  32
#define NDIV  (1+IMM1/NTAB)

long good_random()
{
  int    j;
  long   k;
  static long seed2=123456789;
  static long iy = 0;
  static long iv[NTAB];

  if( random_seed <= 0 ) {
    if( -random_seed < 1 )
      random_seed = 1;
    else
      random_seed = -random_seed;
    seed2 = random_seed;
    for( j=NTAB+7; j>=0; j--) {
      k = random_seed / IQ1;
      random_seed = IA1 * (random_seed - k * IQ1) - k * IR1;
      if( random_seed < 0 )
	random_seed += IM1;
      if( j < NTAB )
	iv[j] = random_seed;
    }
    iy = iv[0];
  }

  k = random_seed / IQ1;
  random_seed = IA1 * (random_seed - k * IQ1) - k * IR1;
  if( random_seed < 0 )
    random_seed += IM1;
  k = seed2 / IQ2;
  seed2 = IA2 * (seed2 - k * IQ2) - k * IR2;
  if( seed2 < 0 )
    seed2 += IM2;
  j = (int)(iy / NDIV);
  iy = iv[j] - seed2;
  iv[j] = random_seed;
  if( iy < 1 ) iy += IMM1;
  return iy;
  /* printf("random_seed=%ld, seed2=%ld, result=%ld\n", 
     random_seed, seed2, iy); */
}

void fatal_error (msg)
     char * msg;
{
  fprintf(stderr, "%s\n", msg);
  exit(0);
}

