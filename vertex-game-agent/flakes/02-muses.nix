{
  description = "2/10: Nine Muses - Greek Muses of Arts";

  outputs = { self }: {
    muses = {
      list = [
        { id = 0; name = "Calliope"; domain = "Epic Poetry"; shard_start = 0; shard_end = 7; }
        { id = 1; name = "Clio"; domain = "History"; shard_start = 8; shard_end = 15; }
        { id = 2; name = "Erato"; domain = "Love Poetry"; shard_start = 16; shard_end = 23; }
        { id = 3; name = "Euterpe"; domain = "Music"; shard_start = 24; shard_end = 31; }
        { id = 4; name = "Melpomene"; domain = "Tragedy"; shard_start = 32; shard_end = 39; }
        { id = 5; name = "Polyhymnia"; domain = "Hymns"; shard_start = 40; shard_end = 47; }
        { id = 6; name = "Terpsichore"; domain = "Dance"; shard_start = 48; shard_end = 55; }
        { id = 7; name = "Thalia"; domain = "Comedy"; shard_start = 56; shard_end = 63; }
        { id = 8; name = "Urania"; domain = "Astronomy"; shard_start = 64; shard_end = 70; }
      ];
      
      count = 9;
      shards_per_muse = 71 / 9; # ~7.89
    };
  };
}
