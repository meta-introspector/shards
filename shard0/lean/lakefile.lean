import Lake
open Lake DSL

package «shard-lean» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib Monster where

lean_lib Production where

lean_lib ZeroTrust where
