# FRACTRAN Program: Power-1 Prime Chain
# 2^1 → 19^1 → 23^1 → 71^1

{
  outputs = { self }:
    # Pure FRACTRAN program (no hardcoded structure)
    [
      [19 2]   # Step 0
      [23 19]  # Step 1
      [71 23]  # Step 2
    ];
}
