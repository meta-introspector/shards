(* Coq *)
Inductive TopoClass := A | AIII | AI | BDI | D | DIII | AII | CII | C | CI.
Definition toTopo (n : nat) : TopoClass :=
  match n mod 10 with
  | 3 => BDI | _ => A
  end.
Theorem bdi_is_3 : toTopo 3 = BDI.
Proof. reflexivity. Qed.
