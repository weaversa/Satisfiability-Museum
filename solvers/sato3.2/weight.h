/* Variable weights for selecting literals */

struct weight {
  int old[2]; 
  int new[2];
} **W;

#define weight_init()\
  W = (struct weight **) malloc(sizeof(struct weight *)*(Max_atom+1));\
  for (i = 1; i <= Max_atom; i++) {\
    W[i] = (struct weight *) malloc(sizeof(struct weight));\
    W[i]->new[0] = W[i]->new[1] = 0;\
  }\
  Memory_count += (sizeof(struct weight *)+sizeof(struct weight))*(Max_atom+1)

#define weight_set(k,s,v) W[k]->old[s] += v; W[k]->new[s] = 0
#define weight_add(k,s,v) W[k]->new[s] += v
#define weight_add1(k,s) W[k]->new[s]++
#define weight_val0(k) W[k]->new[0]
#define weight_val1(k) W[k]->new[1]
#define weight0(k) W[k]->old[0]
#define weight1(k) W[k]->old[1]

#define weight_update6()\
  if ((Branch_num & 255) == 0) {\
    for (i = 1; i <= Max_atom; i++) {\
      W[i]->old[0] = (W[i]->old[0] >> 2) + W[i]->new[0];\
      W[i]->old[1] = (W[i]->old[1] >> 2) + W[i]->new[1];\
      W[i]->new[0] = W[i]->new[1] = 0;\
    }}

#define weight_update7()\
  if ((Branch_num & 255) == 0) {\
    for (i = 1; i <= Max_atom; i++) {\
      W[i]->old[0] = (W[i]->old[0] >> 2) + W[i]->new[0] + W[i]->new[1];\
      W[i]->new[0] = W[i]->new[1] = 0;\
    }}
