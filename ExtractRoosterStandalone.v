(* MetaRocq Extraction: Extract Rooster Proof AST - Standalone *)

From MetaRocq.Template Require Import All.

Import MRMonadNotation.

(* Define rooster inline *)
Inductive TopoClass : Type :=
  | A | AIII | AI | BDI | D | DIII | AII | CII | C | CI.

Definition encode_topo (t : TopoClass) : nat :=
  match t with
  | A => 0 | AIII => 1 | AI => 2 | BDI => 3 | D => 4
  | DIII => 5 | AII => 6 | CII => 7 | C => 8 | CI => 9
  end.

Theorem bdi_is_life : encode_topo BDI = 3.
Proof. reflexivity. Qed.

Definition ROOSTER_CROW : nat := 71.

(* Quote the rooster's definitions *)
MetaRocq Quote Definition encode_topo_ast := encode_topo.
MetaRocq Quote Definition bdi_is_life_ast := bdi_is_life.
MetaRocq Quote Definition rooster_crow_ast := ROOSTER_CROW.

(* Quote recursively to get all dependencies *)
MetaRocq Quote Recursively Definition rooster_full := bdi_is_life.

(* Print the AST *)
Compute encode_topo_ast.
Compute bdi_is_life_ast.
Compute rooster_crow_ast.

(* Unquote to verify round-trip *)
MetaRocq Unquote Definition encode_topo_unquoted := encode_topo_ast.
MetaRocq Unquote Definition rooster_crow_unquoted := rooster_crow_ast.

(* 🐓 The rooster's AST is now extracted! *)
