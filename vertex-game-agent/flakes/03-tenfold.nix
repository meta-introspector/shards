{
  description = "3/10: 10-fold Way - Altland-Zirnbauer Topological Classification";

  outputs = { self }: {
    tenfold = {
      classes = [
        { id = 0; name = "A"; symmetry = "none"; reality = "complex"; chiral = false; }
        { id = 1; name = "AI"; symmetry = "T"; reality = "real"; chiral = false; time_reversal = true; }
        { id = 2; name = "AII"; symmetry = "T"; reality = "quaternion"; chiral = false; time_reversal = true; }
        { id = 3; name = "AIII"; symmetry = "S"; reality = "complex"; chiral = true; }
        { id = 4; name = "BDI"; symmetry = "T+S"; reality = "real"; chiral = true; time_reversal = true; }
        { id = 5; name = "D"; symmetry = "C"; reality = "real"; chiral = false; charge_conjugation = true; }
        { id = 6; name = "DIII"; symmetry = "C+S"; reality = "quaternion"; chiral = true; charge_conjugation = true; }
        { id = 7; name = "CI"; symmetry = "C"; reality = "quaternion"; chiral = false; charge_conjugation = true; }
        { id = 8; name = "C"; symmetry = "C"; reality = "complex"; chiral = false; charge_conjugation = true; }
        { id = 9; name = "CII"; symmetry = "T+C"; reality = "real"; chiral = false; time_reversal = true; charge_conjugation = true; }
      ];
      
      count = 10;
      bott_period = 8; # Bott periodicity mod 8
    };
  };
}
