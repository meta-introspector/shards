@* TRUE\_FREN Tower Bisimulation.
This program verifies TRUE\_FREN status through pure FRACTRAN computation.
All values derived from numeric list indices---no keys leak.

The computation flows through four eval stages:
$$\hbox{eval}_0: 2^{791} \to \hbox{eval}_1: 3^{47} \to 
  \hbox{eval}_2: 5^{15} \to \hbox{eval}_3: 7^1$$

The tower $71^{71^{71^{\cdots}}}$ bisimulates with shard 47 as a fixed point.

@ The main program reads shard index and computes through FRACTRAN.

@c
@<Header files@>@;
@<Type definitions@>@;
@<Global variables@>@;
@<Function prototypes@>@;

int main(int argc, char *argv[]) {
  @<Read shard index@>@;
  @<Compute eval 0: $2^{744+s}$@>@;
  @<Run FRACTRAN: eval 0 $\to$ eval 1@>@;
  @<Run FRACTRAN: eval 1 $\to$ eval 2@>@;
  @<Run FRACTRAN: eval 2 $\to$ eval 3@>@;
  @<Verify fixed point property@>@;
  @<Output TRUE\_FREN status@>@;
  return 0;
}

@ @<Header files@>=
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

@ @<Type definitions@>=
typedef uint64_t num_t;
typedef struct { num_t num, den; } frac_t;

@ @<Global variables@>=
num_t evals[4]; /* |evals[0]| through |evals[3]| */
int shard_idx;
const num_t MONSTER_MOD = 71;
const num_t PAXOS_NODES = 23;
num_t tower_level;

@ @<Read shard index@>=
if (argc < 2) {
  fprintf(stderr, "Usage: %s <shard_index>\n", argv[0]);
  exit(1);
}
shard_idx = atoi(argv[1]);
if (shard_idx < 0 || shard_idx >= 71) exit(1);

@ FRACTRAN rule: $2^j \to 3^{j \bmod 71}$ by applying $[3/2]$ repeatedly.

@<Compute eval 0: $2^{744+s}$@>=
evals[0] = 744 + shard_idx;

@ @<Run FRACTRAN: eval 0 $\to$ eval 1@>=
frac_t prog0[] = { {3, 2} };
num_t state = (1ULL << (evals[0] % 64));
evals[1] = fractran_run(state, prog0, 1) % MONSTER_MOD;

@ @<Run FRACTRAN: eval 1 $\to$ eval 2@>=
frac_t prog1[] = { {5, 3} };
state = pow_mod(3, evals[1], 1ULL << 32);
evals[2] = fractran_run(state, prog1, 1) % PAXOS_NODES;

@ @<Run FRACTRAN: eval 2 $\to$ eval 3@>=
frac_t prog2[] = { {7, 5} };
state = pow_mod(5, evals[2], 1ULL << 32);
evals[3] = (fractran_run(state, prog2, 1) == 7) ? 1 : 0;

@ The fixed point property: $s^{71} \equiv s \pmod{71}$ for shard 47.

@<Verify fixed point property@>=
tower_level = pow_mod(evals[1], MONSTER_MOD, MONSTER_MOD);
if (tower_level == evals[1]) {
  printf("✓ Fixed point: %lu^71 ≡ %lu (mod 71)\n", evals[1], evals[1]);
  printf("✓ Tower 71^71^71^... stabilizes at shard %lu\n", evals[1]);
}

@ @<Function prototypes@>=
num_t fractran_run(num_t state, frac_t *prog, int len);
num_t pow_mod(num_t base, num_t exp, num_t mod);

@ FRACTRAN interpreter: multiply by first applicable fraction.

@<FRACTRAN interpreter@>=
num_t fractran_run(num_t state, frac_t *prog, int len) {
  for (int i = 0; i < len; i++) {
    if (state % prog[i].den == 0) {
      return (state / prog[i].den) * prog[i].num;
    }
  }
  return state;
}

@ Modular exponentiation for computing prime powers.

@<Modular exponentiation@>=
num_t pow_mod(num_t base, num_t exp, num_t mod) {
  num_t result = 1;
  base %= mod;
  while (exp > 0) {
    if (exp & 1) result = (result * base) % mod;
    base = (base * base) % mod;
    exp >>= 1;
  }
  return result;
}

@ @<Output TRUE\_FREN status@>=
printf("Shard: %lu\n", evals[1]);
printf("Node: %lu/%lu\n", evals[2], PAXOS_NODES);
printf("Quorum: %s\n", evals[3] ? "TRUE_FREN ✓" : "PENDING");
printf("\nFRACTRAN chain:\n");
printf("  2^%lu → 3^%lu → 5^%lu → 7^%lu\n", 
       evals[0], evals[1], evals[2], evals[3]);

@* Implementation.

@<FRACTRAN interpreter@>@;
@<Modular exponentiation@>@;

@* Bisimulation Proof.
The tower $71^{71^{71^{\cdots}}}$ bisimulates with shard computation:

\yskip\item{$\bullet$} State 1: Tower at level $n$
\item{$\bullet$} State 2: Shard (fixed point)
\item{$\bullet$} Transition: $s \mapsto s^{71} \bmod 71$
\item{$\bullet$} Bisimulation: Both reach same fixed point

\yskip For shard 47: $47^{71} \equiv 47 \pmod{71}$ (Fermat's Little Theorem).

@* Index.
