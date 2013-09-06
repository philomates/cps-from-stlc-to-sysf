(***************************************************************************
* STLC (source language) properties                                        *
* William J. Bowman, Phillip Mates & James T. Perconti                     *
***************************************************************************)

Require Import LibWfenv Source_Definitions Core_Infrastructure.

(* ********************************************************************** *)

(* regularity of s_typing *)

Theorem s_typing_implies_wfenv : forall G e s,
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

(* regularity of s_context_typing *)

Theorem s_context_typing_implies_s_context : forall C G_hole s_hole G s,
  s_context_typing C G_hole s_hole G s -> s_context C.
Proof.
  induction 1; eauto using s_typing_implies_s_term.
Qed.

Theorem s_context_typing_implies_wfenv_hole : forall C G_hole s_hole G s,
  s_context_typing C G_hole s_hole G s -> wfenv s_type G_hole.
Proof.
  induction 1; auto. pick_fresh x. apply* (H0 x).
Qed.

Theorem s_context_typing_implies_s_type_hole : forall C G_hole s_hole G s,
  s_context_typing C G_hole s_hole G s -> s_type s_hole.
Proof.
  induction 1; auto. pick_fresh x. apply* (H0 x).
Qed.

Theorem s_context_typing_implies_wfenv : forall C G_hole s_hole G s,
  s_context_typing C G_hole s_hole G s -> wfenv s_type G.
Proof.
  induction 1; auto.
  pick_fresh x. apply (wfenv_push_inv_wfenv s_type G x s). apply* H0.
Qed.

Theorem s_context_typing_implies_s_type : forall C G_hole s_hole G s,
  s_context_typing C G_hole s_hole G s -> s_type s.
Proof.
  induction 1; eauto using s_typing_implies_s_type.
  inversion* IHs_context_typing.
  apply s_typing_implies_s_type in H. inversion* H.
  apply* s_type_arrow. pick_fresh x. apply* (H0 x).
Qed.

(* Other properties of contexts *)

Theorem s_eval_context_implies_s_context : forall E,
  s_eval_context E -> s_context E.
Proof.
  induction 1; auto.
Qed.

Lemma open_ee_rec_s_term_core : forall e j e' e'' i, i <> j ->
  (open_ee_rec source j e' e) =
    open_ee_rec source i e'' (open_ee_rec source j e' e) ->
  e = open_ee_rec source i e'' e.
Proof.
  (* literally just copy-pasted this proof from open_tt_rec_t_type_core
     in Target_Properties.v and changed t to e in the first tactic.
     seems like there is some automation to be done here -JTP *)
  induction e; intros; simpl in *; inversion H0; f_equal*.
  case_eq (EqNat.beq_nat i n); intros; auto.
  apply EqNat.beq_nat_true in H1. subst.
  case_eq (EqNat.beq_nat j n); intros; auto.
  apply EqNat.beq_nat_true in H1. subst. destruct* H.
  rewrite H1 in H0. simpl in H0. rewrite* NPeano.Nat.eqb_refl in H0.
Qed.

Lemma open_ee_rec_s_term : forall e e' n,
  s_term e -> open_ee_rec source n e' e = e.
Proof.
  intros. gen n.
  apply (s_term_mut (fun e WF => forall n, open_ee_rec source n e' e = e)
                    (fun v WF => forall n, open_ee_rec source n e' v = v));
  intros; simpl; f_equal*.
  pick_fresh x. symmetry.
  replace (inc_if_eq source source) with S; auto.
  apply open_ee_rec_s_term_core with (j := 0) (e' := s_trm_fvar x).
  auto. symmetry; auto.
Qed.

Lemma plug_s_term_open_ee_rec : forall C e n e', s_term e ->
  open_ee_rec source n e' (plug C e) = plug (ctx_open_ee_rec source n e' C) e.
Proof.
  induction C; intros; simpl; f_equal; auto using open_ee_rec_s_term.
Qed.

Theorem plug_preserves_s_term : forall C e,
  s_context C -> s_term e -> s_term (plug C e).
Proof.
  induction 1; intros; simpl; auto.
  apply s_term_value. apply_fresh s_value_abs as x; auto.
  rewrite* plug_s_term_open_ee_rec.
Qed.

(* TODO: how to prove this? or maybe we should change s_context_typing
 * to concatenate something instead of extending arbitrarily.
 * would that be ok or would something else break? *)
Lemma s_typing_weaken : forall G G' e s,
  extends G' G -> s_typing G' e s -> s_typing G e s.
Admitted.

Theorem plug_preserves_s_typing : forall C e G_e s_e G s,
  s_context_typing C G_e s_e G s -> s_typing G_e e s_e ->
  s_typing G (plug C e) s.
Proof.
  intros; induction H; simpl; eauto using s_typing_weaken.
  apply_fresh s_typing_abs as x; auto.
  rewrite plug_s_term_open_ee_rec; eauto using s_typing_implies_s_term.
Qed.
