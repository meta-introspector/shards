# Wikidata Dataset Flakes: Sharded by Author/Repo/File/Line/Token/Value

{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = { self, nixpkgs }:
    let
      pkgs = nixpkgs.legacyPackages.x86_64-linux;
      
      # Each dataset as separate flake input
      datasets = [
        {
          name = "wikidata-full";
          url = "github:philippesaade/wikidata";
          author = "philippesaade";
          repo = "wikidata";
        }
        {
          name = "wikidata-5m";
          url = "github:Vijaysr4/en_wikidata_5M_entities";
          author = "Vijaysr4";
          repo = "en_wikidata_5M_entities";
        }
        {
          name = "wikidata-triples";
          url = "github:piebro/wikidata-extraction";
          author = "piebro";
          repo = "wikidata-extraction";
        }
      ];
      
      # Shard function: author→71, repo→59, file→47, line→43
      shardDataset = ds:
        let
          # Hash author to shard mod 71
          authorHash = builtins.hashString "sha256" ds.author;
          authorShard = (builtins.fromTOML "x=${authorHash}").x - ((builtins.fromTOML "x=${authorHash}").x / 71) * 71;
          
          # Hash repo to shard mod 59
          repoHash = builtins.hashString "sha256" ds.repo;
          repoShard = (builtins.fromTOML "x=${repoHash}").x - ((builtins.fromTOML "x=${repoHash}").x / 59) * 59;
          
        in {
          inherit (ds) name url author repo;
          shards = {
            author_mod_71 = authorShard;
            repo_mod_59 = repoShard;
            # file_mod_47, line_mod_43, token, value computed on fetch
          };
        };
      
      # Shard all datasets
      shardedDatasets = builtins.map shardDataset datasets;
      
    in {
      inherit datasets shardedDatasets;
      
      # Generate flake inputs for each
      flakeInputs = builtins.listToAttrs (builtins.map (ds: {
        name = ds.name;
        value = {
          url = ds.url;
          flake = true;
        };
      }) datasets);
    };
}
