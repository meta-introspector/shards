{
  description = "Pure FRACTRAN constants as Nix flake inputs";

  outputs = { self }: {
    # 71 shards as list (index = shard number)
    # Each shard is a list: [eval0, eval1, eval2, eval3, lean4_list, mes_list]
    shards = builtins.genList (s: [
      # 0: eval 0 = 2^(744+s)
      (744 + s)
      
      # 1: eval 1 = 3^s
      s
      
      # 2: eval 2 = 5^((s*13) mod 23)
      (builtins.mod (s * 13) 23)
      
      # 3: eval 3 = 7^{0|1}
      (if (builtins.mod (s * 13) 23) > 11 then 1 else 0)
      
      # 4: Lean4 expressions as list
      [
        "def j_invariant : Nat := ${toString (744 + s)}"
        "def shard : Nat := ${toString s}"
        "def node : Nat := ${toString (builtins.mod (s * 13) 23)}"
        "def quorum : Bool := ${if (builtins.mod (s * 13) 23) > 11 then "true" else "false"}"
      ]
      
      # 5: MES expressions as list
      [
        "(define j-invariant ${toString (744 + s)})"
        "(define shard ${toString s})"
        "(define node ${toString (builtins.mod (s * 13) 23)})"
        "(define quorum ${if (builtins.mod (s * 13) 23) > 11 then "#t" else "#f"})"
      ]
    ]) 71;
  };
}
