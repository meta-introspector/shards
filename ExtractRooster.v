(* MetaCoq Extraction: Extract Rooster Proof to OCaml/Haskell/Scheme *)

From MetaCoq.Template Require Import All.

Require Import RoosterCrow.

(* Extract the rooster's crow to executable code *)

(* Extract topological class encoding *)
MetaCoq Quote Definition encode_topo_quoted := encode_topo.

(* Extract BDI theorem *)
MetaCoq Quote Definition bdi_is_life_quoted := bdi_is_life.

(* Extract the main theorem *)
MetaCoq Quote Definition rooster_crowed_quoted := THE_ROOSTER_HAS_CROWED.

(* Print the AST *)
MetaCoq Unquote Definition encode_topo_ast := encode_topo_quoted.
MetaCoq Unquote Definition bdi_is_life_ast := bdi_is_life_quoted.
MetaCoq Unquote Definition rooster_crowed_ast := rooster_crowed_quoted.

(* Extract to OCaml *)
Require Extraction.
Extraction Language OCaml.

Extract Inductive TopoClass => "topo_class" [
  "A" "AIII" "AI" "BDI" "D" "DIII" "AII" "CII" "C" "CI"
].

Extraction "rooster_crow.ml" encode_topo ROOSTER_CROW.

(* Extract to Haskell *)
Extraction Language Haskell.
Extraction "RoosterCrow.hs" encode_topo ROOSTER_CROW.

(* Extract to Scheme *)
Extraction Language Scheme.
Extraction "rooster_crow.scm" encode_topo ROOSTER_CROW.

(* Print extraction info *)
Print encode_topo.
Print THE_ROOSTER_HAS_CROWED.
