/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.5 $ */

/* main() and the other top-level functions. */

#include <stdlib.h>
#include <ctype.h>
#include <limits.h>
#include <math.h>
#include <signal.h>
#include <stdio.h>
#include <string.h>

#ifdef THINK_C
#include <time.h>    /* For clock(). */
#else
#include <sys/time.h>
#include <sys/resource.h>
#ifndef RUSAGE_SELF
#include <fcntl.h>
#include <sys/procfs.h>
#include <unistd.h>
#endif /* RUSAGE_SELF */
#endif /* THINK_C */

#include "ballbin.h"
#include "cnfforms.h"
#include "cmn-flgs.h"
#include "dmcs-cnf.h"
#include "defines.h"
#include "dimacs.h"
#include "dynamic.h"
#include "dynstats.h"
#include "k-lits.h"
#include "good-rnd.h"
#include "graphclr.h"
#include "m-n-reg.h"
#include "n-queens.h"
#include "rnd-ksat.h"
#include "readdata.h"
#include "safemall.h"
#include "statevec.h"
#include "main.h"

static char version[] = "1.0";

static char *progname;

static char *env_choice;

static char *problem_file = NULL;
static char probfile_buffer[LINEMAX];
static char *log_file = NULL;
static char *error_file = NULL;
static char *stats_file = NULL;
static FILE *statistics_file = NULL;

problem_type problem_choice;

int machine_readable;

#define UNSET -99

/* The number of trials to perform. */
static long number_of_trials = UNSET;

/* Whether to echo internally generated SAT problems to stderr. */
static int echo_problems = UNSET;

/* Whether to solve the given problem(s) at all. */
static int do_not_solve = 0;

/* Variables for internally generated problems. */

static long randomksat_propcount;
static long randomksat_clausecount;
static long randomksat_clauselength;

static long mnregular_posoccurrences;
static long mnregular_negoccurrences;
static long mnregular_propcount;
static long mnregular_clauselength;

static long graphcolor_vertexcount;
static double graphcolor_edge_prob;
static long graphcolor_colorcount;

static long nqueens_queencount;

static long ballsinbins_ballcount;
static long ballsinbins_bincount;

double *grand_avgs;
unsigned long *grand_counts;
#ifdef GRAND_STATS
#define GRAND_PROP_COUNT 150
#else
#define GRAND_PROP_COUNT 1
#endif /* GRAND_STATS */


/* Whatever I have to do at the end of the program.  The argument
   makes this function compatible with signal(). */

static void cleanup( int dummy )
{
#ifdef DEBUG
  printf( "\nmalloc_counter:  %ld\n", malloc_counter );
#endif
  (void)fflush( stdout );
  if( statistics_file )
    (void)fflush( statistics_file );
  exit( 0 );
}

/* Whatever I have to do at the start of the program. */

static void setup( char *argv[] )
{
  void (*sig_result)(int);

  progname = argv[0];
  problem_choice = None;
  machine_readable = UNSET;
  random_seed = 0;
#ifdef DEBUG
  malloc_counter = 0;
#endif /* DEBUG */
  /* This is the correct way to handle a signal. */
  sig_result = signal( SIGINT, SIG_IGN );
  if( sig_result == SIG_ERR )
    fatal_error( "First call to signal() failed" );
  if( sig_result != SIG_IGN &&
      signal(SIGINT, cleanup) == SIG_ERR )
    fatal_error( "Second call to signal() failed" );
}

static void construct_formula( void )
{
  switch( problem_choice ) {
  case NQueens:
    n_queens( nqueens_queencount, 0 );
    break;
  case MitchellKSAT:
    random_ksat( randomksat_propcount,
                 randomksat_clausecount,
                 randomksat_clauselength,
                 0 );
    break;
  case GraphColoring:
    graph_coloring( graphcolor_vertexcount,
                    graphcolor_edge_prob,
                    graphcolor_colorcount );
    break;
  case MNRegular:
    m_n_regular( mnregular_posoccurrences,
                 mnregular_negoccurrences,
                 mnregular_propcount,
                 mnregular_clauselength );
    break;
  case BallsInBins:
    balls_in_bins( ballsinbins_ballcount,
                   ballsinbins_bincount );
    break;
  case FromStdin:
  case FromFile:
    get_dimacs_formula();
    break;
  case None:
    fatal_error( "construct_formula:  Nothing to construct" );
    break;
  }
}

/* Construct the formula, construct the state vector, call
   the search algorithm, free the formula, and generate
   statistics. */

static double sigma( double *data, long n )
{
  long i;
  double mean_sum = 0.0;
  double sqr_sum = 0.0;

  if( n < 2 )
    return 0.0;
  for( i=0; i<n; i++ ) {
    mean_sum += data[i];
    sqr_sum += data[i] * data[i];
  }
  return( sqrt((sqr_sum - (mean_sum * mean_sum / n)) / (n - 1)) );
}

static void satisfy_and_analyze_global( void )
{
#ifdef THINK_C
  clock_t starting_time;
#else
  double starting_time;
#ifdef PIOCUSAGE
  int fd;
  char proc[LINEMAX];
  prusage_t pru;
#else
  struct rusage ru;
#endif /* PIOCUSAGE */
#endif /* THINK_C */
  truth_value preprocess_result;
  long i, initial_seed;

#ifdef PIOCUSAGE
  sprintf( proc, "/proc/%ld", (long)getpid() );
  if( (fd = open(proc, O_RDONLY)) == -1 )
    fatal_error( "open() failed" );
#endif /* PIOCUSAGE */
  the_dynamic_stats =
    (dynamic_stats)safe_malloc( sizeof(dynamic_stats_object) );

  grand_avgs = (double *)safe_malloc( GRAND_PROP_COUNT * sizeof(double) );
  grand_counts =
    (unsigned long *)safe_malloc( GRAND_PROP_COUNT * sizeof(unsigned long) );
  for( i=0; i<GRAND_PROP_COUNT; i++ ) {
    grand_avgs[i] = 0.0;
    grand_counts[i] = 0;
  }

  if( number_of_trials == 1 ) {
    initial_seed = random_seed;
    the_dynamic_stats->nodes =
      the_dynamic_stats->solution_count = 0;
    the_dynamic_stats->cpu_time = 0.0;
    construct_formula();

    if( echo_problems ) {
      formula_print_cnf( 0 );
      if( do_not_solve ) {
        proplist_free( the_prop_list );
        formula_free( the_formula );
        safe_free( the_dynamic_stats );
        safe_free( grand_avgs );
        safe_free( grand_counts );
        return;
      }
    }

#ifdef SIMPLIFY_FIRST
    if( problem_choice == MitchellKSAT ||
        problem_choice == FromStdin ||
        problem_choice == FromFile ) {
      /* simplify_formula() usually consumes a negligible amount
         of CPU time. */
      switch( simplify_formula() ) {
      case Indeterminate:
        break;
      case True:
        if( !machine_readable )
          printf( "This formula is trivially satisfiable.\n" );
        proplist_free( the_prop_list );
        formula_free( the_formula );
        safe_free( the_dynamic_stats );
        safe_free( grand_avgs );
        safe_free( grand_counts );
        if( statistics_file ) {
          fprintf( statistics_file, "1\t0\t0.000\n" );
          (void)fflush( statistics_file );
        }
        return;
      case False:
        if( !machine_readable )
          printf( "This formula is trivially unsatisfiable.\n" );
        proplist_free( the_prop_list );
        formula_free( the_formula );
        safe_free( the_dynamic_stats );
        safe_free( grand_avgs );
        safe_free( grand_counts );
        if( statistics_file ) {
          fprintf( statistics_file, "0\t0\t0.000\n" );
          (void)fflush( statistics_file );
        }
        return;
      }
    }
#endif /* SIMPLIFY_FIRST */
    preprocess_result = sv_make_and_preprocess();
    switch( preprocess_result ) {
    case Indeterminate:
#ifdef THINK_C
      starting_time = clock();
#else
#ifdef PIOCUSAGE
      if( ioctl(fd, PIOCUSAGE, &pru) == -1 )
        fatal_error( "ioctl() failed." );
      starting_time =
        (double)pru.pr_utime.tv_sec +
          (double)pru.pr_utime.tv_nsec / 1000000000;
#else
      if( getrusage(RUSAGE_SELF, &ru) == -1 )
        fatal_error( "getrusage() failed" );
      starting_time =
        (double)ru.ru_utime.tv_sec +
          (double)ru.ru_utime.tv_usec / 1000000;
#endif /* PIOCUSAGE */
#endif /* THINK_C */
      satisfy_dynamic();
#ifdef THINK_C
      the_dynamic_stats->cpu_time =
        ((float)(clock() - starting_time)) / CLOCKS_PER_SEC;
#else
#ifdef PIOCUSAGE
      if( ioctl(fd, PIOCUSAGE, &pru) == -1 )
        fatal_error( "ioctl() failed." );
      the_dynamic_stats->cpu_time =
        (double)pru.pr_utime.tv_sec +
          (double)pru.pr_utime.tv_nsec / 1000000000 - starting_time;
#else
      if( getrusage(RUSAGE_SELF, &ru) == -1 )
        fatal_error( "getrusage() failed" );
      the_dynamic_stats->cpu_time =
        (double)ru.ru_utime.tv_sec +
          (double)ru.ru_utime.tv_usec / 1000000 - starting_time;
#endif /* PIOCUSAGE */
#endif /* THINK_C */
      break;
    case True:
      if( !machine_readable )
        printf( "This formula is trivially satisfiable.\n" );
      the_dynamic_stats->solution_count++;
      break;
    case False:
      if( !machine_readable )
        printf( "This formula is trivially unsatisfiable.\n" );
      break;
    }
    global_status_report( the_dynamic_stats );
    if( statistics_file ) {
      fprintf( statistics_file, "%ld\t%ld\t%.3f\n",
               the_dynamic_stats->solution_count,
               the_dynamic_stats->nodes,
               the_dynamic_stats->cpu_time );
      (void)fflush( statistics_file );
    }
#ifdef DEBUG
    printf( "Initial seed:  %ld\n", initial_seed );
#endif
    sv_free();
    safe_free( the_dynamic_stats );
    safe_free( grand_avgs );
    safe_free( grand_counts );
    return;
  }    /* number_of_trials == 1 */

  if( do_not_solve ) {
    for( i=0; i<number_of_trials; i++ ) {
      construct_formula();
      formula_print_cnf( 0 );
      proplist_free( the_prop_list );
      formula_free( the_formula );
    }
    safe_free( the_dynamic_stats );
    safe_free( grand_avgs );
    safe_free( grand_counts );
    return;
  }

  /* In the following basic block, number_of_trials > 1 and
     do_not_solve = 0. */

  {
    long nodes;
    double cpu_time;
    double mean, std_dev;

    long satisfiable = 0;
    long unsatisfiable = 0;
    long total_nodes_sat = 0;
    long total_nodes_unsat = 0;
    long total_nodes = 0;
    double total_time_sat = 0.0;
    double total_time_unsat = 0.0;
    double total_time = 0.0;

    long max_nodes_sat = LONG_MIN;
    long max_nodes_unsat = LONG_MIN;
    long max_nodes = LONG_MIN;
    double max_time_sat = -1.0;
    double max_time_unsat = -1.0;
    double max_time = -1.0;

    long min_nodes_sat = LONG_MAX;
    long min_nodes_unsat = LONG_MAX;
    long min_nodes = LONG_MAX;
    double min_time_sat = (double)LONG_MAX;
    double min_time_unsat = (double)LONG_MAX;
    double min_time = (double)LONG_MAX;

    double *nodes_data_sat = NULL;
    double *nodes_data_unsat = NULL;
    double *nodes_data = NULL;
    double *time_data_sat = NULL;
    double *time_data_unsat = NULL;
    double *time_data = NULL;

#ifdef GRAND_STATS
    long j;
#endif /* GRAND_STATS */

    if( !machine_readable ) {
      nodes_data_sat =
        (double *)safe_malloc( (size_t)number_of_trials * sizeof(double) );
      nodes_data_unsat =
        (double *)safe_malloc( (size_t)number_of_trials * sizeof(double) );
      nodes_data =
        (double *)safe_malloc( (size_t)number_of_trials * sizeof(double) );
      time_data_sat =
        (double *)safe_malloc( (size_t)number_of_trials * sizeof(double) );
      time_data_unsat =
        (double *)safe_malloc( (size_t)number_of_trials * sizeof(double) );
      time_data =
        (double *)safe_malloc( (size_t)number_of_trials * sizeof(double) );
    }
    
    for( i=0; i<number_of_trials; i++ ) {
      initial_seed = random_seed;
      if( !machine_readable )
        printf( "Problem number %ld:\n", i+1 );
      the_dynamic_stats->nodes =
        the_dynamic_stats->solution_count = 0;
      the_dynamic_stats->cpu_time = 0.0;
      construct_formula();
      if( problem_choice == FromFile )
        if( fseek(stdin, 0L, 0) == -1 )
          fatal_error( "fseek() failed" );

      if( echo_problems )
        formula_print_cnf( 0 );

#ifdef SIMPLIFY_FIRST
      if( problem_choice == MitchellKSAT ||
          problem_choice == FromStdin ||
          problem_choice == FromFile ) {
        /* simplify_formula() usually consumes a negligible amount
           of CPU time. */
        switch( simplify_formula() ) {
        case Indeterminate:
          break;
        case True:
          if( !machine_readable )
            printf( "This formula is trivially satisfiable.\n\n" );
          proplist_free( the_prop_list );
          formula_free( the_formula );
          if( statistics_file ) {
            fprintf( statistics_file, "1\t0\t0.000\n" );
            (void)fflush( statistics_file );
          }
          /* Update the statistics if necessary. */
          if( !machine_readable ) {
            nodes_data_sat[satisfiable] = 0.0;
            time_data_sat[satisfiable] = 0.0;
            satisfiable++;
            nodes_data[i] = 0.0;
            time_data[i] = 0.0;
            if( 0 < min_nodes_sat )
              min_nodes_sat = 0;
            if( 0.0 < min_time_sat )
              min_time_sat = 0.0;
          }
          continue;
        case False:
          if( !machine_readable )
            printf( "This formula is trivially unsatisfiable.\n\n" );
          proplist_free( the_prop_list );
          formula_free( the_formula );
          if( statistics_file ) {
            fprintf( statistics_file, "0\t0\t0.000\n" );
            (void)fflush( statistics_file );
          }
          /* Update the statistics if necessary. */
          if( !machine_readable ) {
            nodes_data_sat[unsatisfiable] = 0.0;
            time_data_sat[unsatisfiable] = 0.0;
            unsatisfiable++;
            nodes_data[i] = 0.0;
            time_data[i] = 0.0;
            if( 0 < min_nodes_unsat )
              min_nodes_unsat = 0;
            if( 0.0 < min_time_unsat )
              min_time_unsat = 0.0;
          }
          continue;
        }
      }
#endif /* SIMPLIFY_FIRST */
      preprocess_result = sv_make_and_preprocess();
      switch( preprocess_result ) {
      case Indeterminate:
#ifdef THINK_C
        starting_time = clock();
#else
#ifdef PIOCUSAGE
        if( ioctl(fd, PIOCUSAGE, &pru) == -1 )
          fatal_error( "ioctl() failed." );
        starting_time =
          (double)pru.pr_utime.tv_sec +
            (double)pru.pr_utime.tv_nsec / 1000000000;
#else
        if( getrusage(RUSAGE_SELF, &ru) == -1 )
          fatal_error( "getrusage() failed" );
        starting_time =
          (double)ru.ru_utime.tv_sec +
            (double)ru.ru_utime.tv_usec / 1000000;
#endif /* PIOCUSAGE */
#endif /* THINK_C */
        satisfy_dynamic();
#ifdef THINK_C
        the_dynamic_stats->cpu_time =
          ((float)(clock() - starting_time)) / CLOCKS_PER_SEC;
#else
#ifdef PIOCUSAGE
        if( ioctl(fd, PIOCUSAGE, &pru) == -1 )
          fatal_error( "ioctl() failed." );
        the_dynamic_stats->cpu_time =
          (double)pru.pr_utime.tv_sec +
            (double)pru.pr_utime.tv_nsec / 1000000000 - starting_time;
#else
        if( getrusage(RUSAGE_SELF, &ru) == -1 )
          fatal_error( "getrusage() failed" );
        the_dynamic_stats->cpu_time =
          (double)ru.ru_utime.tv_sec +
            (double)ru.ru_utime.tv_usec / 1000000 - starting_time;
#endif /* PIOCUSAGE */
#endif /* THINK_C */
        break;
      case True:
        if( !machine_readable )
          printf( "This formula is trivially satisfiable.\n" );
        the_dynamic_stats->solution_count++;
        break;
      case False:
        if( !machine_readable )
          printf( "This formula is trivially unsatisfiable.\n" );
        break;
      }

      /* Print out the results. */

      global_status_report( the_dynamic_stats );

      nodes = the_dynamic_stats->nodes;
      cpu_time = the_dynamic_stats->cpu_time;
      if( machine_readable )
        printf( "\n" );
      if( statistics_file ) {
        fprintf( statistics_file, "%ld\t%ld\t%.3f\n",
                 the_dynamic_stats->solution_count,
                 nodes, cpu_time );
        (void)fflush( statistics_file );
      }
#ifdef DEBUG
      printf( "Initial seed:  %ld\n", initial_seed );
#endif

      if( !machine_readable ) {
        if( the_dynamic_stats->solution_count ) {
          total_nodes_sat += nodes;
          nodes_data_sat[satisfiable] = (double)nodes;
          total_time_sat += cpu_time;
          time_data_sat[satisfiable] = cpu_time;
          satisfiable++;

          if( nodes > max_nodes_sat )
            max_nodes_sat = nodes;
          if( nodes < min_nodes_sat )
            min_nodes_sat = nodes;
          if( cpu_time > max_time_sat )
            max_time_sat = cpu_time;
          if( cpu_time < min_time_sat )
            min_time_sat = cpu_time;
        }
        else {
          total_nodes_unsat += nodes;
          nodes_data_unsat[unsatisfiable] = (double)nodes;
          total_time_unsat += cpu_time;
          time_data_unsat[unsatisfiable] = cpu_time;
          unsatisfiable++;

          if( nodes > max_nodes_unsat )
            max_nodes_unsat = nodes;
          if( nodes < min_nodes_unsat )
            min_nodes_unsat = nodes;
          if( cpu_time > max_time_unsat )
            max_time_unsat = cpu_time;
          if( cpu_time < min_time_unsat )
            min_time_unsat = cpu_time;
        }
        total_nodes += nodes;
        nodes_data[i] = (double)nodes;
        total_time += cpu_time;
        time_data[i] = cpu_time;
      }

      if( !machine_readable ) {
        /* The statistics for unsatisfiable problems are more
           interesting than the ones for satisfiable problems. */
        if( unsatisfiable )
          printf( "Avgs.:\tnodes = %.3f, CPU time = %.3f,\n\t\
%% sat = %.2f, unsat nodes = %.3f, unsat CPU time = %.3f.\n\n",
                  (double)total_nodes / (i + 1),
                  total_time / (i + 1),
                  (double)satisfiable * 100.0 / (i + 1),
                  (double)total_nodes_unsat / unsatisfiable,
                  total_time_unsat / unsatisfiable );
        else
          printf( "Avgs.:\tnodes = %.3f, CPU time = %.3f.\n\n",
                  (double)total_nodes / (i + 1),
                  total_time / (i + 1) );
      }

      sv_free();

#ifdef GRAND_STATS
      /* Print out running averages. */
      printf( "\nRunning averages:\n" );
      for( j=0; j<GRAND_PROP_COUNT; j++ )
        printf( "(%.3f, %ld) ", grand_avgs[j], grand_counts[j] );
      printf( "\n" );
      (void)fflush( stdout );
#endif /* GRAND_STATS */

    }   /* for */

    /* Print out max's, min's, averages, and standard deviations. */

    max_nodes =
      (max_nodes_sat > max_nodes_unsat ? max_nodes_sat : max_nodes_unsat);
    min_nodes =
      (min_nodes_sat < min_nodes_unsat ? min_nodes_sat : min_nodes_unsat);
    max_time =
      (max_time_sat > max_time_unsat ? max_time_sat : max_time_unsat);
    min_time =
      (min_time_sat < min_time_unsat ? min_time_sat : min_time_unsat);

    if( !machine_readable )
      printf( "There are %ld problems.\n%ld (%.2f%%) are satisfiable \
and %ld (%.2f%%) are unsatisfiable.\n\n",
              number_of_trials,
              satisfiable,
              (double)satisfiable * 100.0 / number_of_trials,
              unsatisfiable,
              (double)unsatisfiable * 100.0 / number_of_trials );

    if( !machine_readable ) {
      printf( "Satisfiable problems:\n" );
      if( satisfiable ) {
        printf( "\tMin. no. of nodes:\t%8ld\tMax.:\t%8ld\n",
                min_nodes_sat, max_nodes_sat );
        printf( "\tMin. CPU time:\t\t%8.3f\tMax.:\t%8.3f\n\n",
                min_time_sat, max_time_sat );

        mean = (double)total_nodes_sat / satisfiable;
        std_dev = sigma( nodes_data_sat, satisfiable );
        printf( "\tAvg. no. of nodes:\t%8.3f\tS.D.:\t%8.3f\n",
                mean, std_dev );
        if( mean > 0.0 )
          printf( "\tC.V.:\t\t\t%8.3f\n", 100.0 * std_dev / mean );
        mean = total_time_sat / satisfiable;
        std_dev = sigma( time_data_sat, satisfiable );
        printf( "\tAvg. CPU time:\t\t%8.3f\tS.D.:\t%8.3f\n",
                mean, std_dev );
        if( mean > 0.0 )
          printf( "\tC.V.:\t\t\t%8.3f\n", 100.0 * std_dev / mean );
      }
    }

    if( !machine_readable ) {
      printf( "\nUnsatisfiable problems:\n" );
      if( unsatisfiable ) {
        printf( "\tMin. no. of nodes:\t%8ld\tMax.:\t%8ld\n",
                min_nodes_unsat, max_nodes_unsat );
        printf( "\tMin. CPU time:\t\t%8.3f\tMax.:\t%8.3f\n\n",
                min_time_unsat, max_time_unsat );

        mean = (double)total_nodes_unsat / unsatisfiable;
        std_dev = sigma( nodes_data_unsat, unsatisfiable );
        printf( "\tAvg. no. of nodes:\t%8.3f\tS.D.:\t%8.3f\n",
                mean, std_dev );
        if( mean > 0.0 )
          printf( "\tC.V.:\t\t\t%8.3f\n", 100.0 * std_dev / mean );
        mean = total_time_unsat / unsatisfiable;
        std_dev = sigma( time_data_unsat, unsatisfiable );
        printf( "\tAvg. CPU time:\t\t%8.3f\tS.D.:\t%8.3f\n",
                mean, std_dev );
        if( mean > 0.0 )
          printf( "\tC.V.:\t\t\t%8.3f\n", 100.0 * std_dev / mean );
      }
    }

    if( !machine_readable ) {
      printf( "\nAll problems:\n" );
      printf( "\tMin. no. of nodes:\t%8ld\tMax.:\t%8ld\n",
              min_nodes, max_nodes );
      printf( "\tMin. CPU time:\t\t%8.3f\tMax.:\t%8.3f\n\n",
              min_time, max_time );

      mean = (double)total_nodes / number_of_trials;
      std_dev = sigma( nodes_data, number_of_trials );
      printf( "\tAvg. no. of nodes:\t%8.3f\tS.D.:\t%8.3f\n",
              mean, std_dev );
      if( mean > 0.0 )
        printf( "\tC.V.:\t\t\t%8.3f\n", 100.0 * std_dev / mean );
      mean = total_time / number_of_trials;
      std_dev = sigma( time_data, number_of_trials );
      printf( "\tAvg. CPU time:\t\t%8.3f\tS.D.:\t%8.3f\n",
              mean, std_dev );
      if( mean > 0.0 )
        printf( "\tC.V.:\t\t\t%8.3f\n", 100.0 * std_dev / mean );
    }

    if( !machine_readable ) {
      safe_free( nodes_data_sat );
      safe_free( nodes_data_unsat );
      safe_free( nodes_data );
      safe_free( time_data_sat );
      safe_free( time_data_unsat );
      safe_free( time_data );
    }

    safe_free( the_dynamic_stats );

#ifdef GRAND_STATS
    printf( "\nGrand averages:\n" );
    for( i=0; i<GRAND_PROP_COUNT; i++ )
      printf( "(%.3f, %ld) ", grand_avgs[i], grand_counts[i] );
    printf( "\n" );
    (void)fflush( stdout );
#endif /* GRAND_STATS */
    safe_free( grand_avgs );
    safe_free( grand_counts );

  }  /* Basic block */

}

static void get_problem_choice( void )
{
  if( problem_choice == None ) {
    if( (env_choice = getenv("POSIT_PROBLEM_CHOICE")) == NULL )
      do {
        printf( "Problem choices:\n" );
        printf( "1.  Random K-SAT (Mitchell et al.)\n" );
        printf( "2.  Random M-N-regular K-SAT (Pehoushek)\n" );
        printf( "3.  Random graph-coloring\n" );
        printf( "4.  N-queens\n" );
        printf( "5.  Balls in bins\n" );
        printf( "6.  From stdin\n" );
        printf( "7.  From a file\n" );
        problem_choice = (problem_type)read_long( "Your choice", 0, 0 );
      } while( problem_choice < 1 || problem_choice > 7 );
    else if( strcmp(env_choice, "mitchellksat") == 0 )
      problem_choice = MitchellKSAT;
    else if( strcmp(env_choice, "mnregular") == 0 )
      problem_choice = MNRegular;
    else if( strcmp(env_choice, "graphcoloring") == 0 )
      problem_choice = GraphColoring;
    else if( strcmp(env_choice, "nqueens") == 0 )
      problem_choice = NQueens;
    else if( strcmp(env_choice, "ballsinbins") == 0 )
      problem_choice = BallsInBins;
    else if( strcmp(env_choice, "stdin") == 0 )
      problem_choice = FromStdin;
    else if( strcmp(env_choice, "file") == 0 )
      problem_choice = FromFile;
    else
      fatal_error( "POSIT_PROBLEM_CHOICE is invalid" );
  }
}

/* It should be possible to echo external problems as well. */

static void get_echo_problems( void )
{
  if( echo_problems == UNSET ) {
    if( getenv("POSIT_ECHO_INTERNAL_PROBLEMS") == NULL )
      echo_problems = 0;        /* The default */
    else
      echo_problems = 1;
  }
}

static void get_machine_readable( void )
{
  if( machine_readable == UNSET ) {
    if( getenv("POSIT_MACHINE_READABLE_OUTPUT") == NULL )
      machine_readable = 0;     /* The default */
    else
      machine_readable = 1;
  }
}

static void get_number_of_trials( void )
{
  if( number_of_trials == UNSET )
    if( (env_choice = getenv("POSIT_NUMBER_OF_TRIALS")) == NULL )
      number_of_trials = 1;    /* The default */
    else
      if( (number_of_trials = atol(env_choice)) < 1 )
        fatal_error( "POSIT_NUMBER_OF_TRIALS is invalid" );
}

static void get_random_seed( void )
{
  if( random_seed == 0 &&
      (env_choice = getenv("POSIT_RANDOM_SEED")) != NULL )
    random_seed = atol( env_choice );
  /* reset_seed() is called immediately after this function. */
}

/* These parameters cannot be set on the command line. */

static void get_random_ksat_data( void )
{
  if( (env_choice = getenv("POSIT_RANDOMKSAT_PROPCOUNT")) == NULL )
    do {
      randomksat_propcount =
        read_long( "Number of propositions", 100, 1 );
    } while( randomksat_propcount < 2 );
  else
    if( (randomksat_propcount = atol(env_choice)) < 2 )
      fatal_error( "POSIT_RANDOMKSAT_PROPCOUNT is invalid" );

  if( (env_choice = getenv("POSIT_RANDOMKSAT_CLAUSECOUNT")) == NULL )
    do {
      randomksat_clausecount = read_long( "Number of clauses", 430, 1 );
    } while( randomksat_clausecount < randomksat_propcount );
  else
    if( (randomksat_clausecount = atol(env_choice)) <
        randomksat_propcount )
      fatal_error( "POSIT_RANDOMKSAT_CLAUSECOUNT is invalid" );

  if( (env_choice = getenv("POSIT_RANDOMKSAT_CLAUSELENGTH")) == NULL )
    do {
      randomksat_clauselength =
        read_long( "Length of each clause", 3, 1 );
    } while( (randomksat_clauselength < 2) ||
             (randomksat_clauselength > randomksat_propcount) );
  else
    if( (randomksat_clauselength = atol(env_choice)) < 2 ||
        randomksat_clauselength > randomksat_propcount )
      fatal_error( "POSIT_RANDOMKSAT_CLAUSELENGTH is invalid" );
}

/* These parameters cannot be set on the command line. */

static void get_m_n_regular_data( void )
{
  if( (env_choice = getenv("POSIT_MNREGULAR_POSOCCURRENCES")) == NULL )
    do {
      mnregular_posoccurrences =
        read_long( "Number of positive occurrences", 5, 1 );
    } while( mnregular_posoccurrences < 1 );
  else
    if( (mnregular_posoccurrences = atol(env_choice)) < 1 )
      fatal_error( "POSIT_MNREGULAR_POSOCCURRENCES is invalid" );

  if( (env_choice = getenv("POSIT_MNREGULAR_NEGOCCURRENCES")) == NULL )
    do {
      mnregular_negoccurrences =
        read_long( "Number of negative occurrences", 5, 1 );
    } while( mnregular_negoccurrences < 1 );
  else
    if( (mnregular_negoccurrences = atol(env_choice)) < 1 )
      fatal_error( "POSIT_MNREGULAR_NEGOCCURRENCES is invalid" );

  if( (env_choice = getenv("POSIT_MNREGULAR_PROPCOUNT")) == NULL )
    do {
      mnregular_propcount = read_long( "Number of propositions", 9, 1 );
    } while( mnregular_propcount < 2 );
  else
    if( (mnregular_propcount = atol(env_choice)) < 2 )
      fatal_error( "POSIT_MNREGULAR_PROPCOUNT is invalid" );

  if( (env_choice = getenv("POSIT_MNREGULAR_CLAUSELENGTH")) == NULL )
    do {
      mnregular_clauselength =
        read_long( "Length of each clause", 3, 1 );
    } while( (mnregular_clauselength < 2) ||
             (mnregular_clauselength > mnregular_propcount) );
  else
    if( (mnregular_clauselength = atol(env_choice)) < 2 ||
        mnregular_clauselength > mnregular_propcount )
      fatal_error( "POSIT_MNREGULAR_CLAUSELENGTH is invalid" );

  if( ((mnregular_posoccurrences + mnregular_negoccurrences) *
       mnregular_propcount) % mnregular_clauselength )
    fatal_error( "Combination of inputs is invalid" );
}

/* These parameters cannot be set on the command line. */

static void get_graph_coloring_data( void )
{
  if( (env_choice = getenv("POSIT_GRAPHCOLOR_VERTEXCOUNT")) == NULL )
    do {
      graphcolor_vertexcount = read_long( "Number of vertices", 10, 1 );
    } while( graphcolor_vertexcount < 1 );
  else
    if( (graphcolor_vertexcount = atol(env_choice)) < 1 )
      fatal_error( "POSIT_GRAPHCOLOR_VERTEXCOUNT is invalid" );

  if( (env_choice = getenv("POSIT_GRAPHCOLOR_EDGE_PROB")) == NULL )
    do {
      graphcolor_edge_prob = read_double( "Edge probability", 0.5, 1 );
    } while( graphcolor_edge_prob < 0.0 || graphcolor_edge_prob > 1.0 );
  else
    if( (graphcolor_edge_prob = atof(env_choice)) < 0.0 ||
        graphcolor_edge_prob > 1.0 )
      fatal_error( "POSIT_GRAPHCOLOR_EDGE_PROB is invalid" );

  if( (env_choice = getenv("POSIT_GRAPHCOLOR_COLORCOUNT")) == NULL )
    do {
      graphcolor_colorcount = read_long( "Number of colors", 4, 1 );
    } while( graphcolor_colorcount < 1 );
  else
    if( (graphcolor_colorcount = atol(env_choice)) < 1 )
      fatal_error( "POSIT_GRAPHCOLOR_COLORCOUNT is invalid" );
}

/* This parameter cannot be set on the command line. */

static void get_nqueens_data( void )
{
  if( (env_choice = getenv("POSIT_NQUEENS_QUEENCOUNT")) == NULL )
    do {
      nqueens_queencount = read_long( "Number of queens", 4, 1 );
    } while( nqueens_queencount < 4 );
  else
    if( (nqueens_queencount = atol(env_choice)) < 4 )
      fatal_error( "POSIT_NQUEENS_QUEENCOUNT is invalid" );
}

/* These parameters cannot be set on the command line. */

static void get_balls_in_bins_data( void )
{
  if( (env_choice = getenv("POSIT_BALLSINBINS_BALLCOUNT")) == NULL )
    do {
      ballsinbins_ballcount = read_long( "Number of balls", 0, 0 );
    } while( ballsinbins_ballcount < 1 );
  else
    if( (ballsinbins_ballcount = atol(env_choice)) < 1 )
      fatal_error( "POSIT_BALLSINBINS_BALLCOUNT is invalid" );

  if( (env_choice = getenv("POSIT_BALLSINBINS_BINCOUNT")) == NULL )
    do {
      ballsinbins_bincount = read_long( "Number of bins", 0, 0 );
    } while( ballsinbins_bincount < 1 );
  else
    if( (ballsinbins_bincount = atol(env_choice)) < 1 )
      fatal_error( "POSIT_BALLSINBINS_BINCOUNT is invalid" );
}

static void get_internal_problem_data( void )
{
  switch( problem_choice ) {
  case MitchellKSAT:
    get_random_ksat_data();
    break;
  case MNRegular:
    get_m_n_regular_data();
    break;
  case GraphColoring:
    get_graph_coloring_data();
    break;
  case NQueens:
    get_nqueens_data();
    break;
  case BallsInBins:
    get_balls_in_bins_data();
    break;
  default:
    break;
  }
}

static void open_problem_file( void )
{
  FILE *the_file;

  if( problem_choice == FromFile ) {
    if( problem_file == NULL ) {
      do {
        problem_file = read_string( "File name" );
        (void)strncpy( probfile_buffer, problem_file, LINEMAX );
        probfile_buffer[LINEMAX - 1] = '\0';
        safe_free( problem_file );
        if( *probfile_buffer == '\0' )
          ;
        else if( (the_file = fopen(probfile_buffer, "r")) == NULL )
          printf( "That file does not exist--please enter another.\n" );
        else {
          *stdin = *the_file;
          break;
        }
      } while( 1 );
    }
    else if( freopen(problem_file, "r", stdin) == NULL )
      fatal_error( "Could not open problem file" );
    else
      (void)strncpy( probfile_buffer, problem_file, LINEMAX );
  }
}

/* It's useful to be able to append to an existing file. */

static void open_log_file( void )
{
  if( log_file )
    if( freopen(log_file, "a", stdout) == NULL )
      fatal_error( "Could not open log file" );
}

static void open_error_file( void )
{
  if( error_file )
    if( freopen(error_file, "a", stderr) == NULL )
      fatal_error( "Could not open error file" );
}

static void open_statistics_file( void )
{
  if( stats_file && !statistics_file )
    if( (statistics_file = fopen(stats_file, "a")) == NULL )
      fatal_error( "Could not open statistics file" );
}

static void usage_error( void )
{
  fprintf( stderr,
           "Usage:  %s [options], where options are:\n\
-\tGet problem from stdin\n\
-f <f>\tGet problem from file <f>\n\
-g <n>\tGenerate internal problem <n>:\n\
\t  1 => Random K-SAT (Mitchell et al.)\n\
\t  2 => M-N-regular random K-SAT (Pehoushek)\n\
\t  3 => Random graph coloring\n\
\t  4 => N-queens\n\
\t  5 => Balls in bins\n\
\n\
-n <n>\tRun <n> trials\n\
-r <n>\tInitialize random number seed to <n>\n\
\n\
-e\tEcho problem(s) to stderr\n\
-eo\tEcho only; do not solve the given problem(s)\n\
-fe <f>\tSpecify error file <f>\n\
-fl <f>\tSpecify log file <f>\n\
-fs <f>\tSave statistics in file <f>\n\
-m\tGenerate machine-readable output\n\
-v\tPrint version number\n",
           progname );
  exit( 0 );
}

static void process_options( int argc, char *argv[] )
{
  int i;

  for( i=1; i<argc; i++ )
    if( *argv[i] == '-' )
      switch( *(argv[i] + 1) ) {
      case 'v':
        /* Print the version number and die. */
        printf( "This is POSIT, version %s.\n", version );
        exit( 0 );
      case 'e':
        echo_problems = 1;
        if( *(argv[i] + 2) == 'o' )   /* Echo only. */
          do_not_solve = 1;
        break;
      case 'm':
        machine_readable = 1;
        break;
      case 'f':
        switch( *(argv[i] + 2) ) {
        case '\0':    /* Problem file */
          if( problem_choice != None )
            usage_error();
          problem_choice = FromFile;
          i++;
          if( i < argc )
            problem_file = argv[i];
          else
            usage_error();
          break;
        case 'e':     /* Error file. */
          i++;
          if( i < argc )
            error_file = argv[i];
          else
            usage_error();
          break;
        case 'l':     /* Log file. */
          i++;
          if( i < argc )
            log_file = argv[i];
          else
            usage_error();
          break;
        case 's':     /* Statistics file. */
          i++;
          if( i < argc )
            stats_file = argv[i];
          else
            usage_error();
          break;
        }
        break;
      case 'r':
        i++;
        if( i < argc )
          random_seed = atol( argv[i] );
        else
          usage_error();
        break;
      case 'n':
        i++;
        if( i < argc &&       /* Short circuit */
            (number_of_trials = atol(argv[i])) > 0 )
          ;
        else
          usage_error();
        break;
      case 'g':
        if( problem_choice != None )
          usage_error();
        i++;
        if( i < argc )
          switch( (problem_choice = (problem_type)atol(argv[i])) ) {
          case MitchellKSAT:
          case MNRegular:
          case GraphColoring:
          case NQueens:
          case BallsInBins:
            break;
          default:     /* None, FromStdin, FromFile */
            usage_error();
          }
        else
          usage_error();
        break;
      case '\0':
        if( problem_choice == None )
          problem_choice = FromStdin;
        if( problem_choice != FromStdin )
          usage_error();
        break;
      default:
        usage_error();
      }
    else    /* *argv[i] != '-' */
      usage_error();
  get_problem_choice();
  get_echo_problems();
  get_machine_readable();
  get_number_of_trials();
  get_random_seed();
  reset_seed();
  get_internal_problem_data();
  /* All interaction with the user must be completed before calling
     these functions. */
  open_problem_file();
  open_log_file();
  open_error_file();
  open_statistics_file();
  satisfy_and_analyze_global();
}

int main( int argc, char *argv[] )
{
  setup( argv );
  process_options( argc, argv );
  cleanup( 0 );
  return( 0 );
}

