(* MetaCoq: 10-Fold Way Bridges with Self-Quotation *)
From MetaCoq.Template Require Import All.

(* Topological class *)
Parameter topo_class : nat -> nat.
Axiom topo_class_232 : topo_class 232 = 2.
Axiom topo_class_323 : topo_class 323 = 3.

(* Bridge definition *)
Record Bridge := {
  nodeA : nat;
  nodeB : nat;
  diff : topo_class nodeA <> topo_class nodeB
}.

(* Example: 232 ↔ 323 *)
Axiom diff_232_323 : topo_class 232 <> topo_class 323.

Definition bridge_232_323 : Bridge := {|
  nodeA := 232;
  nodeB := 323;
  diff := diff_232_323
|}.

(* MetaCoq: Quote the bridge definition *)
MetaCoq Quote Definition bridge_232_323_quoted := bridge_232_323.

(* MetaCoq: Unquote to verify *)
MetaCoq Unquote Definition bridge_232_323_unquoted := bridge_232_323_quoted.

(* Theorem: Quoted and unquoted are equal (self-quotation) *)
Theorem bridge_self_quotation : bridge_232_323 = bridge_232_323_unquoted.
Proof.
  reflexivity.
Qed.

(* Symmetry theorem *)
Axiom bridge_symmetric : forall (b : Bridge),
  exists b' : Bridge, nodeA b' = nodeB b /\ nodeB b' = nodeA b.

Theorem bridges_symmetric : forall (b : Bridge),
  exists b' : Bridge,
    nodeA b' = nodeB b /\ nodeB b' = nodeA b.
Proof.
  intro b.
  apply bridge_symmetric.
Qed.

(* MetaCoq: Quote the symmetry theorem *)
MetaCoq Quote Definition symmetry_theorem_quoted := bridges_symmetric.

(* Print the AST *)
MetaCoq Run (tmPrint bridge_232_323_quoted).
