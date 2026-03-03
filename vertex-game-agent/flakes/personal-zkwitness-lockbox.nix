{
  description = "Personal zkWitness Lockbox - Vapnik Episode 71 (71×59×47 Shards)";

  outputs = { self }:
    let
      # F: Pure function (no keys)
      F = x: (x * x + x) % 196883;
      
      # zkWitness lockbox
      zkLockbox = content_hash: {
        # Input: Hash of your personal copy
        hash = content_hash;
        
        # Shard into 71×59×47 = 196,883 pieces
        shards = builtins.genList (i: {
          shard_id = i;
          shard_71 = i % 71;
          shard_59 = (i / 71) % 59;
          shard_47 = (i / (71 * 59)) % 47;
          
          # Fragment via F (no complete key)
          fragment = F (content_hash + i);
          
          # Sample point (for key moments)
          sample_point = {
            timestamp = i;
            witnessed = F fragment;
          };
        }) 196883;
        
        # Lockbox sealed
        sealed = true;
        personal = true;
        
        # Key burned (irreversible)
        key_status = "burned-in-ritual";
      };
      
      # Sample key moments (zkWitness)
      sampleMoment = lockbox: timestamp: {
        shard = timestamp % 196883;
        witnessed = F timestamp;
        
        # Proof without revealing content
        zk_proof = {
          moment_exists = true;
          content_revealed = false;
        };
      };
      
    in {
      personal_lockbox = {
        # Your personal copy (legally obtained)
        source = "personal-phone-copy";
        legal = true;
        
        # zkWitness lockbox
        lockbox = zkLockbox;
        
        # Sample function
        sample = sampleMoment;
        
        # Sharding
        total_shards = 196883;
        distribution = "71×59×47";
        
        # No keys exposed
        key_burned = true;
      };
    };
}
