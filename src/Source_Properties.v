(***************************************************************************
* STLC (source language) properties                                        *
* William J. Bowman, Phillip Mates & James T. Perconti                     *
***************************************************************************)

Require Import LibWfenv Source_Definitions Core_Infrastructure.

(* ********************************************************************** *)

Theorem s_typing_implies_s_ok : forall G e s,
  s_typing G e s -> wfenv s_type G.
Proof. 
  intros G e s P.
  induction P; auto.
  pick_fresh x.
  apply (wfenv_push_inv_wfenv s_type G x s1). 
  apply* H0.
Qed. 

Theorem s_typing_implies_s_type : forall G e s,
  s_typing G e s -> s_type s.
Proof. 
  induction 1; eauto.
  apply* (wfenv_binds s_type G x s).
  apply* s_type_arrow.
  pick_fresh x.
  apply* (H0 x).
  inversion* IHs_typing1.
Qed. 

Theorem s_typing_implies_s_term : forall G e s,
  s_typing G e s -> s_term e.
Proof. 
  induction 1; eauto.
Qed. 