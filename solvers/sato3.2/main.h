#define PRIVATE
#define BSD /* for SUN and RS6000 */

/* SATOINT as int uses more space but saves time */ 
#define SATOINT         int        /* either int or short */

#include <stdio.h>
#include <sys/time.h>
#include <sys/resource.h>  
#include "sato.h"


/****************************************************
 *
 *  MACRO Declaration
 *
 ****************************************************/

#ifdef MORETRACE
#define trace(x,y) if (TRACE>=x) y
#define trace1(x,y) if (TRACE==x || x>8) y
#define check(x,y) if (x) y
#else
#define trace(x,y) 
#define trace1(x,y) 
#define check(x,y) 
#endif

