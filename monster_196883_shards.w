@* Monster Dimension Shards: $71 \times 59 \times 47 = 196883$.
This literate program generates all 196883 shards of the Monster group.
Each shard encoded as $2^{46+k}$ hint in pure Nix.

@ Main structure.

@c
@<Header files@>@;
@<Type definitions@>@;
@<Global variables@>@;
@<Function prototypes@>@;

int main(int argc, char *argv[]) {
  @<Read shard index $i \in [0, 196883)$@>@;
  @<Decompose into $(s_{71}, s_{59}, s_{47})$@>@;
  @<Compute $2^{46+k}$ hint@>@;
  @<Generate CWEB section@>@;
  return 0;
}

@ @<Header files@>=
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

@ @<Type definitions@>=
typedef uint64_t num_t;

@ @<Global variables@>=
num_t shard_idx;
num_t s71, s59, s47;
num_t hint;
const num_t MONSTER_DIM = 196883;

@ @<Read shard index $i \in [0, 196883)$@>=
if (argc < 2) exit(1);
shard_idx = strtoull(argv[1], NULL, 10);
if (shard_idx >= MONSTER_DIM) exit(1);

@ Decompose using Chinese Remainder Theorem structure.

@<Decompose into $(s_{71}, s_{59}, s_{47})$@>=
s71 = shard_idx % 71;
s59 = (shard_idx / 71) % 59;
s47 = (shard_idx / (71 * 59)) % 47;

@ @<Compute $2^{46+k}$ hint@>=
hint = 46 + (shard_idx % MONSTER_DIM);

@ Generate CWEB literate section for this shard.

@<Generate CWEB section@>=
{
  printf("@@* Shard %lu.\n", shard_idx);
  printf("Indices: (%lu, %lu, %lu) mod (71, 59, 47).\n\n", s71, s59, s47);
  printf("@@ Hint: $2^{%lu}$\n\n", hint);
  printf("@@ FRACTRAN: $[3/2, 5/3, 7/5]$\n\n");
  printf("@@<Shard %lu computation@@>=\n", shard_idx);
  printf("/* Input: 2^%lu */\n", hint);
  printf("state = (1ULL << %lu);\n", hint % 64);
  printf("/* Apply [3/2]: 2^%lu -> 3^%lu */\n", hint, s71);
  printf("state = fractran(state, 3, 2) %% 71;\n");
  printf("/* Apply [5/3]: 3^%lu -> 5^%lu */\n", s71, s59);
  printf("state = fractran(state, 5, 3) %% 59;\n");
  printf("/* Apply [7/5]: 5^%lu -> 7^%lu */\n", s59, s47);
  printf("state = fractran(state, 7, 5) %% 47;\n");
  printf("/* Output: 7^%lu */\n", s47);
  printf("\n");
}

@ @<Function prototypes@>=
/* None needed */

@* Mathematical Structure.
The decomposition $71 \times 59 \times 47 = 196883$ corresponds to:

\yskip\item{$\bullet$} 71 shards: Monster mod 71
\item{$\bullet$} 59 shards: Theory 59 (map is territory)
\item{$\bullet$} 47 shards: Fixed point (nydiokar)

\yskip Each shard has hint $2^{46+k}$ where 46 is the Bott periodicity offset.

@* Index.
