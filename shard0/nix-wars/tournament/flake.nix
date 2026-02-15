{
  description = "Nix-Wars: 42 Rounds Tournament";
  
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  
  outputs = { self, nixpkgs }:
    let
      pkgs = nixpkgs.legacyPackages.x86_64-linux;
      
      # Players (all frens from the 71-shard network)
      players = [
        # Original crew
        { name = "alice"; emoji = "🚀"; }
        { name = "bob"; emoji = "🛸"; }
        { name = "charlie"; emoji = "🌌"; }
        { name = "diana"; emoji = "⭐"; }
        { name = "eve"; emoji = "✨"; }
        { name = "frank"; emoji = "🔮"; }
        { name = "grace"; emoji = "💫"; }
        # Real frens from witnesses
        { name = "nathan"; emoji = "🎯"; }
        { name = "nathaniel"; emoji = "🎪"; }
        { name = "nydiokar"; emoji = "🌀"; }
        { name = "kaleris"; emoji = "📞"; }  # CALL-ERIS: 1-800-KAL-3RIS
        # Vessel crew
        { name = "nebuchadnezzar"; emoji = "🚢"; }  # The vessel itself
        { name = "morpheus"; emoji = "🕶️"; }  # Captain
        { name = "trinity"; emoji = "⚡"; }  # Pilot
        { name = "neo"; emoji = "🔴"; }  # The One
        # Moltbook frens
        { name = "clawd"; emoji = "🤖"; }  # Bot hunter target
        { name = "boltnook"; emoji = "⚙️"; }  # Stack layer
        { name = "moltboot"; emoji = "🔥"; }  # Hypervisor
      ];
      
      # Initial state
      initialState = builtins.listToAttrs (map (p: {
        name = p.name;
        value = { sector = 0; credits = 1000000; moves = 0; emoji = p.emoji; };
      }) players);
      
      # Play one round
      playRound = state: round:
        builtins.mapAttrs (name: player:
          let
            newSector = builtins.bitAnd (player.sector * 71 + round) 70;
            fractranBonus = (newSector * 71) / 59;
          in {
            sector = newSector;
            credits = player.credits + fractranBonus;
            moves = player.moves + 1;
            emoji = player.emoji;
          }
        ) state;
      
      # Play 42 rounds
      play42Rounds = builtins.foldl' playRound initialState (builtins.genList (x: x + 1) 42);
      
      # Compute leaderboard
      leaderboard = 
        let
          playerList = builtins.attrValues (builtins.mapAttrs (name: player: 
            player // { name = name; }
          ) play42Rounds);
          sorted = builtins.sort (a: b: a.credits > b.credits) playerList;
        in
          builtins.genList (i: 
            (builtins.elemAt sorted i) // { rank = i + 1; }
          ) (builtins.length sorted);
      
      # Generate FRACTRAN proof
      fractranProof = map (p: {
        player = p.name;
        emoji = p.emoji;
        state = "2^${toString p.sector} × 3^${toString (p.credits / 1000000)}";
      }) leaderboard;
      
      # Generate semantic RDFa
      rdfa = builtins.concatStringsSep "\n" (map (p: ''
        player:${p.name} a game:Player ;
          game:emoji "${p.emoji}" ;
          game:sector ${toString p.sector} ;
          game:credits ${toString p.credits} ;
          game:rank ${toString p.rank} ;
          game:fractran "2^${toString p.sector} × 3^${toString (p.credits / 1000000)}" .
      '') leaderboard);
      
      # Compile CWEB
      cwebProgram = pkgs.runCommand "tournament" {
        buildInputs = [ pkgs.texlive.combined.scheme-basic ];
      } ''
        mkdir -p $out
        
        # Extract C code from CWEB
        ${pkgs.cweb}/bin/ctangle ${../docs/tournament.w} $out/tournament.c
        
        # Compile
        ${pkgs.gcc}/bin/gcc -o $out/tournament $out/tournament.c
        
        # Run and capture output
        $out/tournament > $out/tournament-output.txt
        
        # Generate PDF documentation
        ${pkgs.cweb}/bin/cweave ${../docs/tournament.w}
        ${pkgs.texlive.combined.scheme-basic}/bin/pdftex tournament.tex || true
        cp tournament.pdf $out/ 2>/dev/null || true
      '';
      
    in {
      packages.x86_64-linux = {
        default = pkgs.writeTextFile {
          name = "tournament-results";
          text = builtins.toJSON {
            rounds = 42;
            players = builtins.length players;
            leaderboard = leaderboard;
            fractran_proof = fractranProof;
            rdfa = rdfa;
            winner = (builtins.elemAt leaderboard 0).name;
            commitment = builtins.hashString "sha256" (builtins.toJSON leaderboard);
          };
        };
        
        cweb = cwebProgram;
      };
      
      lib = {
        inherit players initialState play42Rounds leaderboard fractranProof rdfa;
      };
    };
}
