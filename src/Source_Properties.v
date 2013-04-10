Set Implicit Arguments.
Require Import LibLN.
Require Import Core_Definitions.
Require Import Source_Definitions.

Implicit Type x : var.
Implicit Type X : var.

Theorem s_typing_implies_s_ok : forall G e s,
  s_typing G e s -> s_ok G.
Proof. (* TODO *)
  intros G e s P.
  induction P; auto.
  unfolds s_ok.
  split.
  pick_fresh.

Admitted. 

Theorem s_typing_implies_s_type : forall G e s,
  s_typing G e s -> s_type s.
Proof. (* TODO *)
Admitted. 

Theorem s_typing_implies_s_term : forall G e s,
  s_typing G e s -> s_term e.
Proof. (* TODO *)
Admitted. 




