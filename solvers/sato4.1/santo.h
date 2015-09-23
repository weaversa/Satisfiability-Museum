/*********************************************************************
; Copyright 2002, Hantao Zhang (HZ).  All rights reserved. 
; By using this software the USER indicates that he or she has read, 
; understood and will comply with the following:
;
; --- HZ hereby grants USER nonexclusive permission to use, copy and/or
; modify this software for internal, noncommercial, research purposes only.
; Any distribution, including commercial sale or license, of this software,
; copies of the software, its associated documentation and/or modifications
; of either is strictly prohibited without the prior consent of HZ.  Title
; to copyright to this software and its associated documentation shall at
; all times remain with HZ.  Appropriate copyright notice shall be placed
; on all software copies, and a complete copy of this notice shall be
; included in all copies of the associated documentation.  No right is
; granted to use in advertising, publicity or otherwise any trademark,
; service mark, or the name of HZ.  Software and/or its associated
; documentation identified as "confidential," if any, will be protected
; from unauthorized use/disclosure with the same degree of care USER
; regularly employs to safeguard its own such information.
;
; --- This software and any associated documentation is provided "as is," and
; HZ MAKES NO REPRESENTATIONS OR WARRANTIES, EXPRESS OR IMPLIED, INCLUDING
; THOSE OF MERCHANTABILITY OR FITNESS FOR A PARTICULAR PURPOSE, OR THAT
; USE OF THE SOFTWARE, MODIFICATIONS, OR ASSOCIATED DOCUMENTATION WILL
; NOT INFRINGE ANY PATENTS, COPYRIGHTS, TRADEMARKS OR OTHER INTELLECTUAL
; PROPERTY RIGHTS OF A THIRD PARTY.  HZ, the University of Iowa,
; its Regents, officers, and employees shall not be liable under any
; circumstances for any direct, indirect, special, incidental, or
; consequential damages with respect to any claim by USER or any third
; party on account of or arising from the use, or inability to use, this
; software or its associated documentation, even if HZ has been advised
; of the possibility of those damages.
*********************************************************************/

int santo_search ()
{
  int i, a;

  for (i = 0; i < ANT; i++) {
    trace(1, printf("Round #%d\n", i));
    for (a = 1; a <= Max_atom; a++) if (Value[a] == DC) {
      if (send_one_ant(a)) return 1;
    }
    weight_update0();
  }
  return Stop;
}

send_one_ant (a)
     int a;
     /* Send one ant out from variable a */
{
  one_ant_move(a);
  while (!Stop && uqueue_nonempty()) {
    if (handle_unit_clauses() == UNSAT) {
      update_trail();
      return SAT;
    } else {	
      if (one_ant_move(0)) return 1;
    }
  }
}

one_ant_move (i)
     int i;
{
  static int last_key;
  int s;
  
  if (!i) i = last_key; 

  if (Value[i] != DC) {
    s = i++;
    while (i <= Max_atom && Value[i] != DC) i++;
    if (i > Max_atom) {
      i = 1;
      while (i < s && Value[i] != DC) i++;
      if (i >= s) {
	Branch_num++;
	Branch_succ++;
	if (var5_check_model()) trace(1, "Wrong model!\n");
	print_model(stdout);
	return Stop = 1;
      }
    }
  }

  last_key = i+1;
  s = get_lit(i,ant_move_sign(i));
  print_let_x_have(s);
  assign_value0(s);
  vstack_push1(s);

  return 0;
}

ant_move_sign (i)
     int i;
{
  int n = weight_value(get_lit(i,0));

  if ((good_random()%(weight_value(get_lit(i,1))+n)) < n) return FF;
  else return TT;
}

update_trail ()
     /* called when an empty clause is found */
{
  int i, n=0;

  Branch_num++;
  Branch_fail++;

  /* check how many clauses are true and false 
  n = slot_count_true()>> 5; */
  n = vstack_size();

  /* leave positive trait */
  for (i = 1; i <= Max_atom; i++) 
    if (Value[i] != DC) weight_add(get_lit(i,Value[i]), n);

  /* leave negative traits */
  for (i = 1; i <= Max_atom; i++) 
    if (Value[i] != DC && !var_gmark(i)) weight_add(get_lit(i,NEG(Value[i])), n);

  Conflict_gcl = NULL;

  /* restore the backtrack stack */
  vstack_reinit();
}
