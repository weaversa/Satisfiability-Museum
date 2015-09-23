#ifdef HP_UX
#include <sys/syscall.h>
#define getrusage(a, b)  syscall(SYS_GETRUSAGE, a, b)
#endif /* HP_UX */

/*************
 *
 *    This file is from OTTER.
 *
 *************/

#define MAX_CLOCK           4294967295  /* max microsecond clock value */
#define MAX_CLOCKS          3

struct clock {    /* for timing operations; see clocks.c */
  long accum_sec;   /* accumulated time */
  long accum_usec;
  long curr_sec;    /* time since clock has been turned on */
  long curr_usec;
};

/*************
 *
 *    CPU_TIME(sec, usec) - It has been sec seconds + usec microseconds
 *        since the start of this process.
 *
 *************/

#ifdef PC
#define CPU_TIME(sec, usec)  \
{  \
    struct timeb r;  \
    ftime(&r);  \
    sec = r.time;  \
    usec = (long) r.millitm * 1000;  \
}  /* CPU_TIME */
#else
#ifdef THINK_C  /* Macintosh */
#define CPU_TIME(sec, usec) \
{ \
    clock_t ticks; \
    ticks = clock(); \
    sec = ticks / CLOCKS_PER_SEC; \
    usec = 0; \
}  /* CPU_TIME */
#else
#define CPU_TIME(sec, usec)  \
{  \
    struct rusage r;  \
    getrusage(RUSAGE_SELF, &r);  \
    sec = r.ru_utime.tv_sec;  \
    usec = r.ru_utime.tv_usec;  \
}  /* CPU_TIME */
#endif
#endif

/*************
 *
 *    CLOCK_START(clock_num) - Start or continue timing.
 *
 *        If the clock is already running, a warning message is printed.
 *
 *************/

#ifdef NO_CLOCK
#define CLOCK_START(c)   /* empty string */
#else
#define CLOCK_START(c)  \
{  \
    struct clock *cp;  \
  \
    cp = &Clocks[c];  \
    if (cp->curr_sec != -1) {  \
	fprintf(stderr, "c WARNING, CLOCK_START: clock %d already on.\n", c);  \
	printf("WARNING, CLOCK_START: clock %d already on.\n", c);  \
	}  \
    else  \
	CPU_TIME(cp->curr_sec, cp->curr_usec) \
}  /* CLOCK_START */
#endif

/*************
 *
 *    CLOCK_STOP(clock_num) - Stop timing and add to accumulated total.
 *
 *        If the clock not running, a warning message is printed.
 *
 *************/

#ifdef NO_CLOCK
#define CLOCK_STOP(c)   /* empty string */
#else
#define CLOCK_STOP(c)  \
{  \
    long sec, usec;  \
    struct clock *cp;  \
  \
    cp = &Clocks[c];  \
    if (cp->curr_sec == -1) {  \
	fprintf(stderr, "c WARNING, CLOCK_STOP: clock %d already off.\n", c);  \
	printf("WARNING, CLOCK_STOP: clock %d already off.\n", c);  \
	}  \
    else {  \
	CPU_TIME(sec, usec)  \
	cp->accum_sec += sec - cp->curr_sec;  \
	cp->accum_usec += usec - cp->curr_usec;  \
	cp->curr_sec = -1;  \
	cp->curr_usec = -1;  \
	}  \
}  /* CLOCK_STOP */
#endif



