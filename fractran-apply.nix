{
  description = "Apply FRACTRAN 71 times through Nix store";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    cweb-shards.url = "path:./cweb-shards-196883.nix";
    cweb-shards.flake = false;
  };

  outputs = { self, nixpkgs, cweb-shards }:
    let
      pkgs = import nixpkgs { system = "x86_64-linux"; };
      shards = import cweb-shards;
      
      # Build derivation for each iteration
      buildShard = i: pkgs.writeText "shard-${toString i}" ''
        Iteration: ${toString i}
        Shard: ${toString (builtins.elemAt (builtins.elemAt shards i) 1)}
        Hint: 2^${toString (builtins.elemAt (builtins.elemAt shards i) 0)}
        FRACTRAN: ${toString (builtins.elemAt (builtins.elemAt shards i) 4)}
      '';
      
      # Apply 71 times
      iterations = builtins.genList (i: buildShard i) 71;
      
    in
      # Apply pipeline
      pkgs.writeShellScriptBin "fractran-pipeline" ''
        #!/bin/sh
        ${builtins.concatStringsSep "\n" (builtins.genList (i: ''
          echo "=== Iteration ${toString i} ==="
          cat ${builtins.elemAt iterations i}
          echo
        '') 71)}
      '';
}
