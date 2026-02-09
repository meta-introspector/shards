{
  description = "WARP 14 - Make it so!";

  outputs = { self }:
    let
      # Warp speed: v^3 mod 196883
      warp = speed: (speed * speed * speed) % 196883;
      
      warp_14 = {
        speed = 14;
        velocity = warp 14;
        engaged = true;
        captain = "Picard";
        command = "Make it so";
      };
      
    in {
      warp_drive = warp_14;
      status = "ENGAGED ⚡";
    };
}
