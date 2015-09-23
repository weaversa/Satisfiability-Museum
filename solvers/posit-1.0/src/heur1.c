/* Copyright (c) 1994 by Jon Freeman. */
/* $Revision: 1.5 $ */

#include "cnfforms.h"
#include "cmn-carr.h"
#include "cmn-parr.h"
#include "gbl-carr.h"
#include "gbl-parr.h"
#include "gbl-sv.h"
#include "heurs.h"
#include "heur1.h"


long heuristic1_nonbinary( long pindex, long *poscost )
{
  common_parray_element cparrelt;
  long *cindex_ptr;
  long poscount, negcount;
  signed char vcarrelt_data;

  poscount = 0;
  cparrelt = common_p_array + pindex;

  for( cindex_ptr = common_l_members[litinfo_to_lindex(Pos,pindex)];
       *cindex_ptr != -99;
       cindex_ptr++ ) {
    vcarrelt_data = global_c_array[*cindex_ptr].data;
    if( vcarrelt_data > 0 ) {     /* Indeterminate. */
      poscount +=
        (1 << (6 < vcarrelt_data ? 0 : 6 - vcarrelt_data));
    }
  }

  if( poscount == 0 ) {
    /* Neg pindex is a pure literal. */
    gapplyh_pure_lindex = 2 * pindex + 1;
    return 0;
  }

  *poscost = poscount;
  global_pcount_array[pindex].poscount = poscount;

  negcount = 0;
  for( cindex_ptr = common_l_members[litinfo_to_lindex(Neg,pindex)];
       *cindex_ptr != -99;
       cindex_ptr++ ) {
    vcarrelt_data = global_c_array[*cindex_ptr].data;
    if( vcarrelt_data > 0 ) {     /* Indeterminate. */
      negcount +=
        (1 << (6 < vcarrelt_data ? 0 : 6 - vcarrelt_data));
    }
  }

  if( negcount == 0 ) {
    /* Pos pindex is a pure literal. */
    gapplyh_pure_lindex = 2 * pindex;
    return 0;
  }

  global_pcount_array[pindex].negcount = negcount;

  return( poscount + negcount );
}
