% Galois Field Structure for zkPerf Proofs
% Each fold operates over a finite field GF(2^k)

int: W = 150;
int: H = 38;

% 10 folds with optimal allocation
array[0..9] of int: lines = array1d(0..9, [1, 29, 1, 1, 1, 1, 1, 1, 1, 1]);

% Galois field size (2^k)
array[0..9] of int: gf_power = array1d(0..9, [
  6,   % GF(2^6) = GF(64)
  8,   % GF(2^8) = GF(256)
  7,   % GF(2^7) = GF(128)
  6,   % GF(2^6) = GF(64)
  7,   % GF(2^7) = GF(128)
  8,   % GF(2^8) = GF(256)
  6,   % GF(2^6) = GF(64)
  8,   % GF(2^8) = GF(256)
  3,   % GF(2^3) = GF(8)
  8    % GF(2^8) = GF(256)
]);

% Field size
array[0..9] of int: field_size = array1d(0..9, [pow(2, gf_power[i]) | i in 0..9]);

% Primitive polynomial for each field (irreducible)
array[0..9] of string: primitive_poly = array1d(0..9, [
  "x^6+x+1",           % GF(64)
  "x^8+x^4+x^3+x^2+1", % GF(256) - AES polynomial
  "x^7+x+1",           % GF(128)
  "x^6+x+1",           % GF(64)
  "x^7+x+1",           % GF(128)
  "x^8+x^4+x^3+x^2+1", % GF(256)
  "x^6+x+1",           % GF(64)
  "x^8+x^4+x^3+x^2+1", % GF(256)
  "x^3+x+1",           % GF(8)
  "x^8+x^4+x^3+x^2+1"  % GF(256)
]);

% Emoji labels
array[0..9] of string: emoji = array1d(0..9, ["☕", "🕳️", "🪟", "👁️", "👹", "🦅", "🐓", "🔄", "🌀", "⚡"]);
array[0..9] of string: name = array1d(0..9, [
  "Real", "Cusp", "Quat", "Oct", "Clif", "Spin", "Vec", "Tens", "Bott", "Mons"
]);

% Field operations available
array[0..9] of string: operations = array1d(0..9, [
  "Add,Mul",           % Basic field ops
  "Add,Mul,Inv,Pow",   % Full field + self-ref
  "Add,Mul,Rot",       % Quaternion rotation
  "Add,Mul,Flow",      % Octonion flow
  "Add,Mul,Sym",       % Clifford symmetry
  "Add,Mul,Proof",     % zkPerf proof ops
  "Add,Mul,Coord",     % Coordinate ops
  "Add,Mul,Compile",   % Compilation ops
  "Add,Mul,Cycle",     % Bott cycle
  "Add,Mul,All"        % Monster all ops
]);

output [
  "🌀 GALOIS FIELD STRUCTURE (zkPerf)\n",
  "===================================\n\n",
  "FOLD │ EMOJI │ NAME │ FIELD │ SIZE │ PRIMITIVE POLY\n",
  "─────┼───────┼──────┼───────┼──────┼────────────────────\n"
] ++ [
  show(i) ++ ".   │  " ++ emoji[i] ++ "   │ " ++ 
  name[i] ++ " │ GF(2^" ++ show(gf_power[i]) ++ ") │ " ++ 
  show_int(4, field_size[i]) ++ " │ " ++ primitive_poly[i] ++ "\n"
  | i in 0..9
] ++ [
  "\nFIELD OPERATIONS:\n"
] ++ [
  "  " ++ emoji[i] ++ " " ++ name[i] ++ ": " ++ operations[i] ++ "\n"
  | i in 0..9
] ++ [
  "\nzkPerf PROOF STRUCTURE:\n",
  "  • Each fold computes over its Galois field\n",
  "  • Cusp (🕳️) uses GF(256) for self-reference\n",
  "  • Proofs are field elements (polynomial commitments)\n",
  "  • Arrows = field homomorphisms\n",
  "\nFIELD PROPERTIES:\n",
  "  • Closed: a+b, a×b ∈ GF(2^k)\n",
  "  • Inverse: ∀a≠0, ∃a^(-1)\n",
  "  • Primitive: Generator g^i covers all elements\n",
  "  • Irreducible: Polynomial cannot factor\n",
  "\nBIT ALLOCATION:\n"
] ++ [
  "  " ++ emoji[i] ++ " GF(2^" ++ show(gf_power[i]) ++ "): " ++ 
  show(lines[i]) ++ "L × 150 = " ++ 
  show(lines[i] * 150) ++ " chars = " ++
  show(lines[i] * 150 * gf_power[i]) ++ " bits\n"
  | i in 0..9
] ++ [
  "\nTOTAL BITS: ", show(sum(i in 0..9)(lines[i] * 150 * gf_power[i])), "\n",
  "\n☕🕳️🪟👁️👹🦅🐓🔄🌀⚡\n"
];
