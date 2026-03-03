{
  description = "FRACTRAN Witness - Pure Nix Store Reads + zkTLS Oracles";

  outputs = { self }:
    let
      # Pure: Read from Nix store only
      nixStorePath = /nix/store;
      
      # FRACTRAN witness function
      witness = file: 
        let
          # Pure: Read file from Nix store
          content = builtins.readFile file;
          
          # FRACTRAN: Resolve via 71×59×47
          resolve = data:
            let
              hash = builtins.hashString "sha256" data;
              num = builtins.foldl' (acc: c: (acc * 256) % 196883) 0 
                    (builtins.stringToCharacters (builtins.substring 0 8 hash));
            in num;
          
        in {
          file = file;
          witnessed = resolve content;
          timestamp = "24/7";  # Continuous witnessing
        };
      
      # zkTLS Oracle for impure data
      zkTLSOracle = {
        protocol = "zkTLS";
        witnessing = "24/7";
        
        # Impure data must go through oracle
        addImpureData = path: {
          path = path;
          status = "pending-oracle-witness";
          requires = "zkTLS-attestation";
        };
      };
      
    in {
      fractran_witness = {
        # Pure reads allowed
        pure = {
          nix_store = nixStorePath;
          witness_fn = witness;
        };
        
        # Impure reads require zkTLS
        impure = zkTLSOracle;
        
        # Example: Witness breaking of claw
        claw_witness = witness /nix/store/openclaw;
      };
    };
}
