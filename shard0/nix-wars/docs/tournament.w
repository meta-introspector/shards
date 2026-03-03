@* Nix-Wars: 42 Rounds Tournament with FRACTRAN Proof.
This CWEB program generates a complete 42-round game with all players,
computes leaderboard, and produces semantic emoji proof.

@c
@<Include headers@>@;
@<Type definitions@>@;
@<Global variables@>@;
@<Function prototypes@>@;

int main(void) {
  @<Initialize players@>@;
  @<Play 42 rounds@>@;
  @<Compute leaderboard@>@;
  @<Generate FRACTRAN proof@>@;
  @<Output semantic emoji proof@>@;
  return 0;
}

@ The players are all frens from the Nix-Wars universe.
Each player starts at sector 0 with 1,000,000 credits.

@<Type definitions@>=
typedef struct {
  char *name;
  int sector;
  int credits;
  int moves;
  char *emoji;
} Player;

@ We have 7 players representing the 7 layers of the system.

@<Global variables@>=
Player players[] = {
  {"alice", 0, 1000000, 0, "🚀"},
  {"bob", 0, 1000000, 0, "🛸"},
  {"charlie", 0, 1000000, 0, "🌌"},
  {"diana", 0, 1000000, 0, "⭐"},
  {"eve", 0, 1000000, 0, "✨"},
  {"frank", 0, 1000000, 0, "🔮"},
  {"grace", 0, 1000000, 0, "💫"}
};
int num_players = 7;

@ Each round, players make moves based on FRACTRAN computation.
The move is determined by: |sector_new = (sector_old * 71 + round) mod 71|

@<Play 42 rounds@>=
for (int round = 1; round <= 42; round++) {
  printf("🎮 Round %d\n", round);
  for (int i = 0; i < num_players; i++) {
    int old_sector = players[i].sector;
    int new_sector = (old_sector * 71 + round) % 71;
    players[i].sector = new_sector;
    players[i].moves++;
    
    /* FRACTRAN: 71/59 applied to position */
    int fractran_state = (new_sector * 71) / 59;
    players[i].credits += fractran_state;
    
    printf("  %s %s: %d → %d (credits: %d)\n",
           players[i].emoji, players[i].name,
           old_sector, new_sector, players[i].credits);
  }
  printf("\n");
}

@ The leaderboard is sorted by credits (descending).

@<Compute leaderboard@>=
/* Bubble sort by credits */
for (int i = 0; i < num_players - 1; i++) {
  for (int j = 0; j < num_players - i - 1; j++) {
    if (players[j].credits < players[j+1].credits) {
      Player temp = players[j];
      players[j] = players[j+1];
      players[j+1] = temp;
    }
  }
}

printf("🏆 LEADERBOARD\n");
printf("═══════════════════════════════════════\n");
for (int i = 0; i < num_players; i++) {
  printf("%d. %s %s - Sector %d - %d credits\n",
         i+1, players[i].emoji, players[i].name,
         players[i].sector, players[i].credits);
}
printf("\n");

@ The FRACTRAN proof encodes the game state as prime factorization.
For each player, we compute: |state = 2^sector × 3^(credits/1000000)|

@<Generate FRACTRAN proof@>=
printf("🔢 FRACTRAN PROOF\n");
printf("═══════════════════════════════════════\n");
for (int i = 0; i < num_players; i++) {
  int sector_exp = players[i].sector;
  int credits_exp = players[i].credits / 1000000;
  printf("%s %s: 2^%d × 3^%d\n",
         players[i].emoji, players[i].name,
         sector_exp, credits_exp);
}
printf("\n");

@ The semantic emoji proof uses RDFa encoding.

@<Output semantic emoji proof@>=
printf("✨ SEMANTIC EMOJI PROOF\n");
printf("═══════════════════════════════════════\n");
printf("@prefix game: <http://nixwars.local/game#> .\n");
printf("@prefix player: <http://nixwars.local/player#> .\n");
printf("\n");

for (int i = 0; i < num_players; i++) {
  printf("player:%s a game:Player ;\n", players[i].name);
  printf("  game:emoji \"%s\" ;\n", players[i].emoji);
  printf("  game:sector %d ;\n", players[i].sector);
  printf("  game:credits %d ;\n", players[i].credits);
  printf("  game:rank %d ;\n", i+1);
  printf("  game:fractran \"2^%d × 3^%d\" .\n\n",
         players[i].sector, players[i].credits / 1000000);
}

printf("game:tournament a game:Tournament ;\n");
printf("  game:rounds 42 ;\n");
printf("  game:players %d ;\n", num_players);
printf("  game:winner player:%s ;\n", players[0].name);
printf("  game:commitment \"$(echo -n 'round42' | sha256sum)\" .\n");

@ Standard includes.

@<Include headers@>=
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

@ Function prototypes (none needed for this simple program).

@<Function prototypes@>=
/* None */

@* Index.
