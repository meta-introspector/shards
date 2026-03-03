{
  description = "71×59×47 CWEB shards as 2^46 hints";

  outputs = { self }: 
    # Total shards: 71 * 59 * 47 = 196883 (Monster dimension!)
    builtins.genList (i: 
      let
        # Decompose i into (s71, s59, s47)
        s71 = i - (i / 71) * 71;
        s59 = (i / 71) - ((i / 71) / 59) * 59;
        s47 = (i / (71 * 59)) - ((i / (71 * 59)) / 47) * 47;
        
        # Encode as 2^46 form: 2^(46 + offset)
        hint = 46 + (i - (i / 196883) * 196883);
        
        # FRACTRAN program for this shard
        fractran = [
          [ 3 2 ]  # eval 0 -> eval 1
          [ 5 3 ]  # eval 1 -> eval 2
          [ 7 5 ]  # eval 2 -> eval 3
        ];
      in
        # Each shard is list: [hint, s71, s59, s47, fractran]
        [
          hint                    # 0: 2^hint
          s71                     # 1: mod 71
          s59                     # 2: mod 59  
          s47                     # 3: mod 47
          fractran                # 4: FRACTRAN program
        ]
    ) 196883;
}
