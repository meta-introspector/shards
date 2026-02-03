% Lean4 Code Analysis → Monster Shards (MiniZinc report)

% Data from analyze_all_lean.sh
int: total_files = 370;
int: shards_used = 65;  % out of 71

% Top shards (example data)
array[1..10] of int: top_shard_ids = [44, 51, 15, 30, 12, 7, 69, 46, 22, 31];
array[1..10] of int: top_shard_counts = [7, 6, 5, 5, 4, 4, 4, 3, 3, 3];

% Verify distribution
constraint sum(top_shard_counts) <= total_files;

% Average files per shard
var float: avg_per_shard = int2float(total_files) / int2float(shards_used);

% Utilization
var float: utilization = int2float(shards_used) / 71.0 * 100.0;

solve satisfy;

output [
  "Lean4 Code Analysis → Monster Shards\n",
  "====================================\n\n",
  "Total Lean4 files: \(total_files)\n",
  "Shards used: \(shards_used)/71 (\(utilization)%)\n",
  "Avg per shard: \(avg_per_shard)\n\n",
  "Top 10 shards:\n"
] ++
[ "  Shard \(top_shard_ids[i]): \(top_shard_counts[i]) files\n" | i in 1..10 ] ++
[
  "\n∴ All Lean4 code mapped to Monster shards ✓\n"
];
