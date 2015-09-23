/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.2 $ */

#include <errno.h>
#include <limits.h>
#include <malloc.h>
#include <math.h>
#include <stdio.h>
#include <sys/types.h>

/* Analyze the data in a POSIT statistics file. */

#define BUFFER_SIZE 80

static FILE *statistics_file;
static char line_buffer[BUFFER_SIZE];
static int solution_type;

static long satisfiable = 0;
static long unsatisfiable = 0;
static long N = 0;

static long total_nodes_sat = 0;
static long total_nodes_unsat = 0;
static long total_nodes = 0;
static double total_time_sat = 0.0;
static double total_time_unsat = 0.0;
static double total_time = 0.0;

static long max_nodes_sat = LONG_MIN;
static long max_nodes_unsat = LONG_MIN;
static long max_nodes = LONG_MIN;
static double max_time_sat = -1.0;
static double max_time_unsat = -1.0;
static double max_time = -1.0;

static long min_nodes_sat = LONG_MAX;
static long min_nodes_unsat = LONG_MAX;
static long min_nodes = LONG_MAX;
static double min_time_sat = (double)LONG_MAX;
static double min_time_unsat = (double)LONG_MAX;
static double min_time = (double)LONG_MAX;

static double *nodes_data_sat;
static double *nodes_data_unsat;
static double *nodes_data;
static double *time_data_sat;
static double *time_data_unsat;
static double *time_data;


static void fatal_error( char *message )
{
  if( errno )
    perror( message );
  else
    fprintf( stderr, "%s.\n", message );
  exit( 1 );
}

static void *safe_malloc( size_t size )
{
  void *result;

  if( (result = malloc(size)) == NULL )
    fatal_error( "Unable to allocate enough memory" );
  return result;
}

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

int main( int argc, char *argv[] )
{
  long i;
  long nodes;
  double cpu_time;
  long total_counter = 0;
  long sat_counter = 0;
  long unsat_counter = 0;
  double mean;
  double std_dev;
  int scanned;

  /* Open the statistics file.  It does have to be an actual file,
     because we rewind it after first counting the total number of
     lines. */
  switch( argc ) {
  case 1:
    if( (statistics_file = fopen("./posit.stats", "r")) == NULL )
      fatal_error( "Could not open statistics file ./posit.stats" );
    break;
  case 2:
    if( (statistics_file = fopen(argv[1], "r")) == NULL ) {
      fprintf( stderr, "%s:  Could not open statistics file %s\n",
	       argv[0], argv[1] );
      exit( 1 );
    }
    break;
  default:
    fprintf( stderr, "Usage:  %s [statistics file]\n", argv[0] );
    return 0;
  }

  /* Scan through the file, counting the number of lines and
     the number of SAT and UNSAT lines, respectively. */
  while( fgets(line_buffer, BUFFER_SIZE, statistics_file) ) {
    /* The first character in a non-blank line is either '1' or '0'. */
    if( *line_buffer == '1' ) {
      N++;
      satisfiable++;
    }
    else if( *line_buffer == '0' ) {
      N++;
      unsatisfiable++;
    }
  }

  /* Allocate space for the data. */

  if( N ) {
    nodes_data = (double *)safe_malloc( N * sizeof(double) );
    time_data = (double *)safe_malloc( N * sizeof(double) );
  }
  if( satisfiable ) {
    nodes_data_sat =
      (double *)safe_malloc( satisfiable * sizeof(double) );
    time_data_sat =
      (double *)safe_malloc( satisfiable * sizeof(double) );
  }
  if( unsatisfiable ) {
    nodes_data_unsat =
      (double *)safe_malloc( unsatisfiable * sizeof(double) );
    time_data_unsat =
      (double *)safe_malloc( unsatisfiable * sizeof(double) );
  }

  /* Rewind the statistics file. */
  if( fseek(statistics_file, 0L, 0) == -1 )
    fatal_error( "Failed to rewind the statistics file" );

  /* Scan through the file again, putting data into the arrays. */
  i = 1;
  while( fgets(line_buffer, BUFFER_SIZE, statistics_file) ) {
    scanned = sscanf( line_buffer, "%d %ld %lf",
                      &solution_type, &nodes, &cpu_time );
    if( scanned < 3 ) {
      if( *line_buffer == '#' ||
          *line_buffer == '\n' )
        continue;
      fprintf( stderr, "%s:  Bad data on line %ld.\n", argv[0], i );
      exit( 1 );
    }

    i++;

    total_nodes += nodes;
    total_time += cpu_time;
    nodes_data[total_counter] = (double)nodes;
    time_data[total_counter] = cpu_time;
    total_counter++;

    if( solution_type == 1 ) {     /* Satisfiable. */
      total_nodes_sat += nodes;
      total_time_sat += cpu_time;
      nodes_data_sat[sat_counter] = (double)nodes;
      time_data_sat[sat_counter] = cpu_time;
      sat_counter++;

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
      total_time_unsat += cpu_time;
      nodes_data_unsat[unsat_counter] = (double)nodes;
      time_data_unsat[unsat_counter] = cpu_time;
      unsat_counter++;

      if( nodes > max_nodes_unsat )
	max_nodes_unsat = nodes;
      if( nodes < min_nodes_unsat )
	min_nodes_unsat = nodes;
      if( cpu_time > max_time_unsat )
	max_time_unsat = cpu_time;
      if( cpu_time < min_time_unsat )
	min_time_unsat = cpu_time;
    }
  }

  max_nodes =
    (max_nodes_sat > max_nodes_unsat ? max_nodes_sat : max_nodes_unsat);
  min_nodes =
    (min_nodes_sat < min_nodes_unsat ? min_nodes_sat : min_nodes_unsat);
  max_time =
    (max_time_sat > max_time_unsat ? max_time_sat : max_time_unsat);
  min_time =
    (min_time_sat < min_time_unsat ? min_time_sat : min_time_unsat);

  /* Print out the results. */
  printf( "There are %ld problems.\n%ld (%.2f%%) are satisfiable and \
%ld (%.2f%%) are unsatisfiable.\n\n",
	  N, satisfiable,
	  (N ? (double)satisfiable * 100.0 / N : 0.0),
	  unsatisfiable,
	  (N ? (double)unsatisfiable * 100.0 / N : 0.0) );

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
    printf( "\tC.V.:\t\t\t%8.3f\n", 100.0 * std_dev / mean );
    mean = total_time_sat / satisfiable;
    std_dev = sigma( time_data_sat, satisfiable );
    printf( "\tAvg. CPU time:\t\t%8.3f\tS.D.:\t%8.3f\n",
	    mean, std_dev );
    printf( "\tC.V.:\t\t\t%8.3f\n", 100.0 * std_dev / mean );
  }

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
    printf( "\tC.V.:\t\t\t%8.3f\n", 100.0 * std_dev / mean );
    mean = total_time_unsat / unsatisfiable;
    std_dev = sigma( time_data_unsat, unsatisfiable );
    printf( "\tAvg. CPU time:\t\t%8.3f\tS.D.:\t%8.3f\n",
	    mean, std_dev );
    printf( "\tC.V.:\t\t\t%8.3f\n", 100.0 * std_dev / mean );
  }

  printf( "\nAll problems:\n" );
  if( N ) {
    printf( "\tMin. no. of nodes:\t%8ld\tMax.:\t%8ld\n",
	    min_nodes, max_nodes );
    printf( "\tMin. CPU time:\t\t%8.3f\tMax.:\t%8.3f\n\n",
	    min_time, max_time );

    mean = (double)total_nodes / N;
    std_dev = sigma( nodes_data, N );
    printf( "\tAvg. no. of nodes:\t%8.3f\tS.D.:\t%8.3f\n",
	    mean, std_dev );
    printf( "\tC.V.:\t\t\t%8.3f\n", 100.0 * std_dev / mean );
    mean = total_time / N;
    std_dev = sigma( time_data, N );
    printf( "\tAvg. CPU time:\t\t%8.3f\tS.D.:\t%8.3f\n",
	    mean, std_dev );
    printf( "\tC.V.:\t\t\t%8.3f\n", 100.0 * std_dev / mean );
  }

  /* Close the posit.stats file. */
  (void)fclose( statistics_file );

  /* It is not necessary to free the arrays. */

  return 0;
}
