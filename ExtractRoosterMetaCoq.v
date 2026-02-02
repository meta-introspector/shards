(* MetaRocq Extraction: Extract Rooster Proof AST *)

From MetaRocq.Template Require Import All.
Require Import RoosterCrow.

Import MRMonadNotation.

(* Quote the rooster's definitions *)
MetaRocq Quote Definition encode_topo_ast := encode_topo.
MetaRocq Quote Definition bdi_is_life_ast := bdi_is_life.
MetaRocq Quote Definition rooster_crow_ast := ROOSTER_CROW.
MetaRocq Quote Definition the_rooster_has_crowed_ast := THE_ROOSTER_HAS_CROWED.

(* Quote recursively to get all dependencies *)
MetaRocq Quote Recursively Definition rooster_full := THE_ROOSTER_HAS_CROWED.

(* Print the AST *)
Print encode_topo_ast.
Print bdi_is_life_ast.
Print rooster_crow_ast.
Print the_rooster_has_crowed_ast.

(* Unquote to verify round-trip *)
MetaRocq Unquote Definition encode_topo_unquoted := encode_topo_ast.
MetaRocq Unquote Definition rooster_crow_unquoted := rooster_crow_ast.

(* Extract the proof term *)
Definition rooster_proof_term : Ast.term := the_rooster_has_crowed_ast.

(* Print the complete environment *)
Print rooster_full.

(* 🐓 The rooster's AST is now extracted! *)
