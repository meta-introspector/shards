/*2:*/
#line 7 "monster_196883_shards.w"

/*3:*/
#line 21 "monster_196883_shards.w"

#include <stdio.h> 
#include <stdint.h> 
#include <stdlib.h> 

/*:3*/
#line 8 "monster_196883_shards.w"

/*4:*/
#line 26 "monster_196883_shards.w"

typedef uint64_t num_t;

/*:4*/
#line 9 "monster_196883_shards.w"

/*5:*/
#line 29 "monster_196883_shards.w"

num_t shard_idx;
num_t s71,s59,s47;
num_t hint;
const num_t MONSTER_DIM= 196883;

/*:5*/
#line 10 "monster_196883_shards.w"

/*10:*/
#line 71 "monster_196883_shards.w"



/*:10*/
#line 11 "monster_196883_shards.w"


int main(int argc,char*argv[]){
/*6:*/
#line 35 "monster_196883_shards.w"

if(argc<2)exit(1);
shard_idx= strtoull(argv[1],NULL,10);
if(shard_idx>=MONSTER_DIM)exit(1);

/*:6*/
#line 14 "monster_196883_shards.w"

/*7:*/
#line 42 "monster_196883_shards.w"

s71= shard_idx%71;
s59= (shard_idx/71)%59;
s47= (shard_idx/(71*59))%47;

/*:7*/
#line 15 "monster_196883_shards.w"

/*8:*/
#line 47 "monster_196883_shards.w"

hint= 46+(shard_idx%MONSTER_DIM);

/*:8*/
#line 16 "monster_196883_shards.w"

/*9:*/
#line 52 "monster_196883_shards.w"

{
printf("@* Shard %lu.\n",shard_idx);
printf("Indices: (%lu, %lu, %lu) mod (71, 59, 47).\n\n",s71,s59,s47);
printf("@ Hint: $2^{%lu}$\n\n",hint);
printf("@ FRACTRAN: $[3/2, 5/3, 7/5]$\n\n");
printf("@<Shard %lu computation@>=\n",shard_idx);
printf("/* Input: 2^%lu */\n",hint);
printf("state = (1ULL << %lu);\n",hint%64);
printf("/* Apply [3/2]: 2^%lu -> 3^%lu */\n",hint,s71);
printf("state = fractran(state, 3, 2) %% 71;\n");
printf("/* Apply [5/3]: 3^%lu -> 5^%lu */\n",s71,s59);
printf("state = fractran(state, 5, 3) %% 59;\n");
printf("/* Apply [7/5]: 5^%lu -> 7^%lu */\n",s59,s47);
printf("state = fractran(state, 7, 5) %% 47;\n");
printf("/* Output: 7^%lu */\n",s47);
printf("\n");
}

/*:9*/
#line 17 "monster_196883_shards.w"

return 0;
}

/*:2*/
