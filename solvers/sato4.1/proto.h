/* proto.h made 
Fri Mar 24 12:14:12 CST 2000
*/

/* clocks.c */

void clock_init();
long clock_val();
void clock_reset();
char *get_time();
long run_time();
void send_sato_message();
void print_times();
long good_random();
void fatal_error ();

/* grow.c */

int *insert_clause_to_tape ();
int *insert_lemma_to_tape ();
void print_model ();
void print_clause ();
void fprint_clause ();
void str_cat();
void str_copy();
void adjust_record ();
void init_grow_once_forall ();
void init_var5_table ();
void print_all_clauses ();
void print_var5_clause ();
void print_var5_nclause ();
/* main.c */

void p_banner();
void print_menu();
void handle_guide_path ();
void save_untouched ();
void append_cmd_line();
void print_command ();
void p_input_stats();
void p_paras ();
int p_stats ();
int check_stop ();
void bug ();
char *tp_alloc();
void print_guide_path ();
void output_guide_path ();
int read_guide_path ();
void print_read_guide_path ();
