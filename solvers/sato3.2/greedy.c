/*********************************************************************
; Copyright 1992-99, The University of Iowa (UI).  All rights reserved. 
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
#include "trie0.h"

/* Usage: if (greedy_search()) return handle_succ_end(); */

int greedy_search ()
     /* Hill-climb search */
{
  int i, try;

  /* Collect variables into the array Tmp */
  Tmp_idx = 0;
  for (i = 1; i <= Max_atom; i++)
    if (Value[i] == DC) Tmp[Tmp_idx++] = i;

#ifdef MORETRACE
  if (TRACE == 2)
    printf("There are %d variables in the greedy search\n", Tmp_idx);
#endif

  for (try = 0; try < MAX_TRIES; try++) {

    /* Random values for the variables */
    for (i = 0; i < Tmp_idx; i++) {
      Value[Tmp[i]] = rand() % 2;
#ifdef MORETRACE
      if (TRACE == 2) {
	printf("  V%d = %d\n", Tmp[i], Value[Tmp[i]]);
      }
#endif
    }

    if (hill_climb()) return 1;
  }

  /* Restore the value of the variables */
  for (i = 0; i < Tmp_idx; i++) Value[Tmp[i]] = DC;
  
  return 0;
}

int hill_climb ()
{
  int i, w, best_wei, best_var;
  int wei = weight_of_clauses();
  int flag = 1;

  printf("hill_climb %d\n", wei);
  best_wei = wei;

  while (flag) {
    for (i = 0; i < Tmp_idx; i++) {
      w = weight_flip_one(wei, Tmp[i]);
      if (w < best_wei) {
	best_wei = w;
	best_var = i;
      }
    }
    if (best_wei < wei) {
#ifdef MORETRACE
      if (TRACE == 2)
	printf("  Weight: %d -> %d when V%d(%d) changes\n", 
	       wei, best_wei, Tmp[best_var], Value[Tmp[best_var]]);
#endif
      Value[Tmp[best_var]] = NEG(Value[Tmp[best_var]]);
      wei = best_wei;
    } else {
      flag = 0;
    }
  }

  return (best_wei == 0);
}

int weight_flip_one (wei, var)
     /* return the updated weight after flipping the value of var */
     int wei, var;
{
  int w;
  int oldval = Value[var];

  Value[var] = NEG(oldval);
  w = weight_of_clauses();
  Value[var] = oldval;

#ifdef MORETRACE
  if (TRACE > 2)
    printf("  Weight: %d -> %d when V%d(%d) changes\n", 
	   wei, w, var, Value[var]);
#endif
  return w;
}
