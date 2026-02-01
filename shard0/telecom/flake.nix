{
  description = "Erlang OTP telecom layer for 71 shards";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs { inherit system; };
    in {
      packages.${system}.default = pkgs.stdenv.mkDerivation {
        name = "shard-telecom";
        src = ./.;
        buildInputs = [ pkgs.erlang pkgs.rebar3 ];
        buildPhase = ''
          rebar3 compile
        '';
        installPhase = ''
          mkdir -p $out
          cp -r _build/default/lib/shard_telecom $out/
        '';
      };

      devShells.${system}.default = pkgs.mkShell {
        buildInputs = with pkgs; [
          erlang
          rebar3
        ];
        shellHook = ''
          echo "Erlang OTP telecom layer ready"
          echo "Start node: rebar3 shell --sname shard0"
        '';
      };
    };
}
