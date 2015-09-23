/* Following use of TRIE_PUSH_BROTHERS is identical to trie_push_brothers(top_no). 
   struct trie *tr = top_no;
   TRIE_PUSH_BROTHERS
*/
#define TRIE_PUSH_BROTHERS \
  struct trie *bros[MAX_SHORT];\
  struct trie *no;\
  int i;\
  int esign;\
  int vi;\
  int idx;\
  struct var3 *it;\
  idx = 1;\
  bros[0] = tr;\
  while (idx > 0) {\
    tr = bros[--idx];\
    while (tr != NULL) {\
      no = tr;\
      i = no->key;\
      esign = no->esign;\
      vi = Value[i];\
      it = V3[i];\
      if (esign == TT) {\
	if (vi == DC) {\
	  trie_assign_value(i, TT);\
	} else if (vi == FF) {\
	  return handle_fail_end();\
	}\
	if (tr->bro != NULL) bros[idx++] = tr->bro;\
	tr = no->neg;\
      } else if (esign == FF) {\
	if (vi == DC) {\
	  trie_assign_value(i, FF);\
	} else if (vi == TT) {\
	  return handle_fail_end();\
	}\
	if (tr->bro != NULL) bros[idx++] = tr->bro;\
	tr = no->pos;\
      } else { /* esign == DC */ \
	if (vi == TT) {\
	  if (tr->bro != NULL) bros[idx++] = tr->bro;\
	  tr = no->neg;\
	} else if (vi == FF) {\
	  if (tr->bro != NULL) bros[idx++] = tr->bro;\
	  tr = no->pos;\
	} else {  /* vi == DC */ \
	  struct cap *cp;\
	  if (no->neg == NULL) {\
	    if (no->pos != NULL) {\
	      cp = it->poss;\
	      no->link->lin = cp->tr;\
	      cp->tr = no;\
	      if (Backup_idx) {\
		no->link->stamp = cp;\
		no->link->back = Top_var3->push;\
		Top_var3->push = no;\
	      }\
	    }\
	  } else if (no->pos == NULL) {\
	    cp = it->negs;\
	    no->link->lin = cp->tr;\
	    cp->tr = no;\
	    if (Backup_idx) {\
	      no->link->stamp = cp;\
	      no->link->back = Top_var3->push;\
	      Top_var3->push = no;\
	    }\
	  } else {\
	    cp = it->both;\
	    no->link->lin = cp->tr;\
	    cp->tr = no;\
	    if (Backup_idx) {\
	      no->link->stamp = cp;\
	      no->link->back = Top_var3->push;\
	      Top_var3->push = no;\
	    }\
	  }\
	  tr = tr->bro;\
	}\
      }\
    }\
  }
