/* proto.h made 
Fri Mar 24 12:14:12 CST 2000
*/

/* bench.c */

int isomo_clauses ();
int queen_clauses ();
int pigeonhole_clauses ();
int ramsey_clauses ();
void next_combination ();
int next_permutation ();
int gcd();

/* cgroup.c */

void print_qp_coding();
void gen_gp_table ();
void decode_pair ();
void fill_qp_table ();
int gp_one_product();
void gen_abg_table();
void abg_encode ();
int abg_decode ();
void fix_abg_g ();
void prn_abg_table ();
void init_cgroups ();
void print_encoding ();
int cyclic_qgroup_clauses ();
int cqg_iso_cls ();
int cqg_multi2_cls ();
int cqg_cls ();
int qg1_2000 ();
int cqg3 ();
int cqg9 ();
int cqg13 ();
int cqg63 ();
void cqg_locate_holes ();
int unique_cover_clauses ();
int test_omts ();
void cqg_extra_unit_cls();

/* clause.c */

void print_model ();
void print_clause ();
void fprint_clause ();
void print_unit_clause ();
int read_one_clause ();
int input_clauses ();
int insert_one_key ();
int read_long ();
int read_int ();
int rename_long ();
int skip_chars_until ();
void reverse ();
int insert_sorter ();
int str_int();
void str_cat();
void str_copy();

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

/* greedy.c */

int greedy_search ();
int hill_climb ();
int weight_flip_one ();

/* list.c */

void list_init_once_forall();
int get_tape ();
void init_list ();
int list_insert_clause ();
int create_variable_table ();
void fill_in_clauses ();
void print_variable_clause();
struct clause *get_clause();
void free_clause ();
int list_search2 ();
int list_next_key ();
int list_best_key();
int list_strategy1();
int list_strategy2();
int list_strategy3();
int list_strategy4();
int list_strategy6_9();
int list_prev_key ();
int propagate_true ();
int propagate_false ();
void list_clean_dependents ();
int list_collect_unit_clauses ();
int list_handle_unit_clauses ();
void print_a_clause ();
void print_clause_address();

/* main.c */

void p_banner();
void print_menu();
void read_one_problem ();
void save_untouched ();
void append_cmd_line();
void print_command ();

/* ngroup.c */

int co_cls ();
int how_many_co ();
int co_cycle_cls();
int orthogonal_to_first();
int qg30 ();
int qg104 ();
int qg_symmetric ();

/* oarray.c */

void init_oarray();
void print_oa_encoding ();
void set_expanding();
void print_mext_reps ();
void fix_seed_minus1();
void fix_seed_zero();
int fix_seed ();
void fix_remainder ();
int fill_seed();
int read_special_seed();
int oarray_clauses();
int oarray_unique_cls ();
int oarray_row2_cls ();
int oarray_posi_cls ();
int oarray_diff_cls ();
int oarray_diff_cls_30 ();
int oarray_diff_cls_31 ();
int oarray_expand_cls ();
int oarray_trans ();
int oarray_qg1 ();
int oarray_qg2 ();
int oarray_qg20 ();
int oarray_qg30 ();
int oarray_auto_cls();
int oarray_unit_cls ();
int pre_set_infinity ();
void print_oarray_portrait ();
void print_oarray ();
void print_oarray20 ();
void print_oarray2();
void print_oarray_model();
void oa_print_squares ();
int oarray_mod_blocks ();
int oarray_rem ();
int oa_type ();
int oa_type2 ();

/* pmd.c */

void init_pmd();
int pmd_fill_remainder ();
void pmd_clause_init();
int pmd_clauses();
int pmd_avoid_nums ();
int pmd_unique_cls ();
int pmd_row2_cls ();
int pmd_posi_cls ();
int pmd_diff_cls ();
int pmd_resolve ();
int avoid_entry_in_col ();
int pmd_unit_cls ();
void print_one_pmd_block ();
void print_pmd ();
void print_pmd_model2 ();
void print_pmd_model ();
void pmd_print_code();
void pmd_gene_partials ();
int pmd_fill_seed();
int pmd_mod23_blocks ();
void mod_init_col ();
int mod_inc_col ();
void mod_apart_count();
int mod_insert_code ();
int q100_clauses ();
int q100_unit_cls ();
int q100_unique_cls ();
int q100_pair_cls ();
int blocks_clauses ();
int blocks_unit_cls ();
int blocks_unique_cls ();
int blocks_pair_cls ();
void print_short_blocks ();
int good_short_block ();
int bad_short_num ();

/* qgroup.c */

void init_qgroups();
void print_qg_encoding();
void transpose_Lsquare2();
int qgroup_clauses ();
int qg1 ();
int qg2 ();
int qg3 ();
int qg4 ();
int qg5 ();
int qg6 ();
int qg7 ();
int qg71 ();
int qg8 ();
int qg81 ();
int qg9 ();
int qg11 ();
int qg12 ();
int qg13 ();
int qg63 ();
int qg64 ();
int qg66 ();
int qg67 ();
int qg68 ();
int qg101 ();
int qg102 ();
int P2_vs_P3();
int qg_insert_clause ();
int rpmd_cls ();
int omega_cls ();
int phi_cls_P2 ();

/* random.c */

void random_ksat_init();
int random_ksat_cls();
int ksat_make_mitchell();
void tiset_adjoin();
void tiset_delete_all();

/* sato.c */

int sato ();
int build ();
void p_input_stats();
void p_paras ();
void p_stats ();
int check_stop ();
int handle_succ_end ();
int handle_fail_end ();
void bug ();
int strategy0();
char *tp_alloc();
void print_guide_path ();
void output_guide_path ();
int read_guide_path ();
void print_read_guide_path ();

/* square.c */

void print_qgroup_model ();
void print_cyclic_model ();
int switch_indices();
void adjust_dia();
void fill_table ();
void print_output_sq ();
void print_sq_to_tuples ();
void print_square ();
void print_qg15_blocks ();
void print_qg100_blocks();
void print_qg4_blocks();
void print_qg63_blocks();
int good63 ();
int print_good63 ();
void print_qg3_blocks();
void fill_triple ();
int conjugate_num ();
int co_key ();
void fill_triple2 ();
int test_co ();
void test_c6_qg3();
void test_c6_qg4();
void test_c6_qg6();
void test_c6_qg7();
void print_first_rows ();
void print_first_row ();
void print_first_row2 ();
void print_q24_5tuple ();
void test_qg81_new();
void test_co_cycle();
void test_all ();
void test_colsg ();
void print_co_squares ();
void test_qg ();
int test_qg0();
int test_qgd0();
void test_qg1();
void test_qg2();
void test_qg3();
void test_qg4();
void test_qg45();
void test_qg5();
void test_qg6();
void test_qg7();
void test_qg8();
void test_qg91();
void test_qg101();
int test_qg102 ();
int test_orthogonal2 ();
int read_two ();
void read_in_square ();
int get123 ();
int get123_2 ();
int get213();
int get321 ();
int get312 ();
void key2triple ();
void print_cell();
void transpose_square2 ();
void conjugate321_square ();
int qg00 ();
void shuffle_sq ();
void shuffle_square2 ();

/* trie.c */

void trie_init_once_forall ();
void init_trie ();
struct trie *trie_create_one_path ();
struct trie *trie_insert_clause2 ();
int trie_subsume_clause ();
struct trie *merge_tries();
struct trie *get_trie ();
void free_trie ();
void print_trie ();
void print_trie_aux();
void print_clauses_in_trie ();
void print_cl_in_trie_aux ();
int trie_search2 ();
int trie_next_key ();
int trie_best_key();
int trie_list_len ();
int trie_strategy1 ();
int trie_strategy2 ();
int trie_strategy3 ();
int trie_strategy4 ();
int trie_strategy5 ();
int trie_prev_key ();
int trie_look_ahead ();
int trie_propagate_values ();
int trie_pull_list ();
int trie_pull_par_up ();
int trie_push_list_pos ();
int trie_push_list_neg ();
int trie_push_brothers ();
void trie_clean_dependents ();
int trie_short_clause_all();
void p_trie_info ();
void init_var3_table ();
long visit_trie ();
int trie_create_var_table();
void init_var2_table ();
struct trie **get_trie2_array ();
long visit_trie2 ();
void trie2_fill_in_clauses ();
void var_clauses();
void print_clause_from_leaf ();
int trie2_search2 ();
int trie2_next_key ();
int trie2_prev_key ();
int trie2_best_key();
int trie2_mom ();
int trie2_compute_mom ();
int trie2_strategy1 ();
int trie2_strategy2 ();
int trie2_strategy3 ();
int trie2_strategy4 ();
int trie2_strategy5 ();
int trie2_strategy6 ();
void trie2_pure_delete ();
void trie2_pure_check ();
int trie2_propagate_true ();
int trie2_propagate_false ();
void trie2_clean_dependents ();
void trie2_clean_one_var ();
void trie2_freeze_clauses();
int trie2_handle_unit_clauses ();
void trie2_record_conflict ();
struct trie *trie_insert_clause_end ();
void trie2_integrate_clause ();
int trie2_locate_uips ();
int trie2_dfs ();
int topo_sort ();
int trie2_max_level ();
void trie2_adjust_counts ();
int trie2_cl_count ();
void trie2_empty ();
int trie2_is_empty ();
void trie_stats ();
void print_all_clauses ();
int trie_insert_one_key ();
void record_keeping ();
int weight_of_clauses ();
int count_false_cl_trie ();
