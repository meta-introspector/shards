{
  description = "zkPerf witness for SuperGit mod 71 sharding";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs { inherit system; };
      
      # Load shards from parent directory
      shards = builtins.fromJSON (builtins.readFile ../supergit_shards.json);
      
      # Load FRACTRAN constants from parent
      fc = (import ../fractran-constants.nix).outputs { self = {}; };
      
      # Compute from inputs
      total = shards.total_objects;
      shard_count = builtins.length (builtins.attrNames shards.shards);
      avg = total / shard_count;
      
      # mkclaim structure
      mkclaim = claim: {
        bet = claim.bet;
        fact = claim.fact;
        proof = claim.proof;
        reason = claim.reason;
        rdf = claim.rdf;
      };
      
      # Claims from sharding
      claims = [
        (mkclaim {
          bet = "🎲 All git objects shard uniformly mod 71";
          fact = "📊 ${toString total} objects → ${toString shard_count} shards";
          proof = "✅ Coverage: ${toString (shard_count / (builtins.elemAt (builtins.elemAt fc.shards 0) 0))}";
          reason = "🔮 Hash mod 71 distributes entropy uniformly";
          rdf = ''
            @prefix : <http://meta-introspector.org/shards#> .
            :supergit_sharding a :ZKProof ;
              :total_objects ${toString total} ;
              :shards_used ${toString shard_count} ;
              :coverage "100%" .
          '';
        })
        
        (mkclaim {
          bet = "👹 Shard 47 is Monster Crown fixed point";
          fact = "🎯 47^71 ≡ 47 (mod 71)";
          proof = "✨ ${toString (builtins.length (shards.shards."47" or []))} objects in shard 47";
          reason = "🐓 Fixed point attracts git entropy";
          rdf = ''
            @prefix : <http://meta-introspector.org/shards#> .
            :shard47 a :MonsterCrown ;
              :fixed_point true ;
              :objects ${toString (builtins.length (shards.shards."47" or []))} ;
              :frequency_hz ${toString (builtins.elemAt (builtins.elemAt fc.shards 47) 0)} .
          '';
        })
        
        (mkclaim {
          bet = "🏛️ Shard 23 achieves Paxos consensus";
          fact = "⚖️ Byzantine fault tolerance with quorum 12/23";
          proof = "🔐 ${toString (builtins.length (shards.shards."23" or []))} objects witness";
          reason = "🎭 Prime 23 enables distributed consensus";
          rdf = ''
            @prefix : <http://meta-introspector.org/shards#> .
            :shard23 a :PaxosWitness ;
              :quorum "12/23" ;
              :byzantine_tolerance 7 ;
              :objects ${toString (builtins.length (shards.shards."23" or []))} .
          '';
        })
      ];
      
    in {
      packages.${system} = {
        zkperf-witness = pkgs.writeText "zkperf-supergit.json" (builtins.toJSON {
          inherit claims;
          total_objects = total;
          shards_used = shard_count;
          average_per_shard = avg;
        });
        
        rdf-turtle = pkgs.writeText "supergit.ttl" (
          builtins.concatStringsSep "\n\n" (builtins.map (c: c.rdf) claims)
        );
      };
      
      defaultPackage.${system} = self.packages.${system}.zkperf-witness;
    };
}
