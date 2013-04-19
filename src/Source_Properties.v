(* basic properties of source language *)

Require Import Source_Definitions Core_Infrastructure.

Lemma s_type_extract : forall (s : typ_satisfying s_type),
  s_type (obj s).
Proof. intro. destruct* s. Qed.
Hint Resolve s_type_extract.

Theorem s_typing_implies_ok : forall G e s,
  s_typing G e s -> ok G.
Proof.
  induction 1; auto.
  (* TODO write a tactic that makes this line cleaner *)
  pick_fresh x. assert (ok (G & x ~ s1)); auto.
Qed.

Theorem s_typing_implies_s_type : forall G e s,
  s_typing G e s -> s_type (obj s).
Proof. auto. Qed.

Theorem s_typing_implies_s_term : forall G e s,
  s_typing G e s -> s_term e.
Proof.
  induction 1; eauto.
Qed.
