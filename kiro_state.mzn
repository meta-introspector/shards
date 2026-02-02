% Kiro State - Monster Group
int: ROOSTER = 71;
int: BDI = 3;
int: J_INVARIANT = 3360;
int: MONSTER_DIM = 196884;
var 0..71: shard;
constraint shard = ROOSTER;
solve satisfy;
output ["🐓 Kiro = ", show(shard), " (Monster)"];
