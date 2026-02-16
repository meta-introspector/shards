{
  description = "Multi-Chain Witness + Silver Automaten (Offering to God)";

  outputs = { self }:
    let
      # F: Pure function
      F = x: (x * x + x) % 196883;
      
      # Multi-chain witness
      multiChainWitness = witness_data: {
        # Solana
        solana = {
          program = "vapnik-witness-71";
          account = "witness-pool";
          instruction = {
            data = F witness_data;
            shard_71 = witness_data % 71;
            shard_59 = (witness_data / 71) % 59;
            shard_47 = (witness_data / (71 * 59)) % 47;
          };
        };
        
        # Ethereum
        ethereum = {
          contract = "VapnikWitness";
          function = "recordWitness";
          args = {
            witnessHash = F witness_data;
            timestamp = "block.timestamp";
          };
        };
        
        # Bitcoin
        bitcoin = {
          op_return = "OP_RETURN";
          data = builtins.substring 0 80 (toString (F witness_data));
          witness_script = "witness-${toString witness_data}";
        };
        
        # All chains witnessed
        witnessed = true;
      };
      
      # Silver coin automaten
      silverAutomaten = sol_payment: witness_id: {
        # Pay SOL
        payment = {
          amount_sol = sol_payment;
          destination = "silver-mint-pool";
          chain = "solana";
        };
        
        # Mint silver coin
        silver_coin = {
          witness_id = witness_id;
          
          # Custom form (user choice)
          form = "user-specified";  # Round, square, custom shape
          
          # Inscription
          inscription = {
            front = "Vapnik-${toString witness_id}";
            back = "71×59×47";
            edge = "196883";
          };
          
          # Weight (pure silver)
          weight_grams = sol_payment * 10;  # 10g per SOL
          
          # Offering
          offering = {
            to = "God";
            purpose = "witness-vapnik-spaceflight";
            blessed = true;
          };
        };
        
        # Automaten delivery
        delivery = {
          method = "physical-automaten";
          location = "distributed-globally";
          pickup = "witness-verified";
        };
      };
      
      # Complete witness flow
      witnessFlow = witness_data: sol_amount: {
        # Step 1: Multi-chain witness
        chains = multiChainWitness witness_data;
        
        # Step 2: Pay SOL
        payment = sol_amount;
        
        # Step 3: Mint silver
        silver = silverAutomaten sol_amount witness_data;
        
        # Step 4: Record
        recorded = {
          blockchain = true;
          physical = true;
          offering = true;
        };
      };
      
    in {
      witness_system = {
        # Multi-chain
        chains = ["solana" "ethereum" "bitcoin"];
        
        # Silver automaten
        automaten = silverAutomaten;
        
        # Complete flow
        flow = witnessFlow;
        
        # Offering
        offering = {
          to = "God";
          form = "silver-coin";
          witnessed = "multi-chain";
        };
      };
    };
}
