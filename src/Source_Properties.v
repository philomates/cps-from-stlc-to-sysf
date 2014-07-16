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
  induction 1; frauto.
Qed.

Theorem s_typing_implies_s_type : forall G e s,
  s_typing G e s -> s_type s.
Proof. 
  induction 1; frauto.
  apply* (wfenv_binds s_type G x s).
  inverts* IHs_typing1.
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
  induction 1; frauto.
Qed.

Theorem s_context_typing_implies_s_type_hole : forall C G_hole s_hole G s,
  s_context_typing C G_hole s_hole G s -> s_type s_hole.
Proof.
  induction 1; frauto.
Qed.

Theorem s_context_typing_implies_wfenv : forall C G_hole s_hole G s,
  s_context_typing C G_hole s_hole G s -> wfenv s_type G.
Proof.
  induction 1; frauto.
Qed.

Theorem s_context_typing_implies_s_type : forall C G_hole s_hole G s,
  s_context_typing C G_hole s_hole G s -> s_type s.
Proof.
  induction 1; eauto using s_typing_implies_s_type.
  inverts* IHs_context_typing.
  apply s_typing_implies_s_type in H. inverts* H.
  frauto.
Qed.

(* Weakening for s_typing *)

Lemma s_typing_weaken_generalized : forall E F G e s,
  s_typing (E & G) e s -> wfenv s_type (E & F & G) ->
  s_typing (E & F & G) e s.
Proof.
  intros. gen_eq K: (E & G). gen E F G.
  induction H; intros; subst*.
  apply* s_typing_var. apply* binds_weaken. eapply wfenv_ok. eassumption.
  apply_fresh* s_typing_abs as x. apply_ih_bind* H0.
  apply wfenv_push; auto.
Qed.

Lemma s_typing_weaken : forall G G' e s,
  s_typing G e s -> wfenv s_type (G & G') -> s_typing (G & G') e s.
Proof.
  intros. rewrite <- (concat_empty_r (G & G')).
  apply s_typing_weaken_generalized; rewrite* concat_empty_r.
Qed.

(* Basic properties of subst_ee and open_ee *)

Lemma open_ee_rec_s_term_core : forall e j e' e'' i, i <> j ->
  (open_ee_rec source j e' e) =
    open_ee_rec source i e'' (open_ee_rec source j e' e) ->
  e = open_ee_rec source i e'' e.
Proof.
  induction e; intros; simpl in *; inversion H0; f_equal*.
  case_if*. apply EqNat.beq_nat_true in H1. subst.
  case_if. apply EqNat.beq_nat_true in H1. substs. destruct* H.
  simpl in *. case_if*. rewrite NPeano.Nat.eqb_refl in H3. false.
Qed.

Lemma open_ee_rec_s_term : forall e e' n,
  s_term e -> open_ee_rec source n e' e = e.
Proof.
  intros. gen n.
  apply (s_term_mut (fun e WF => forall n, open_ee_rec source n e' e = e)
                    (fun v WF => forall n, open_ee_rec source n e' v = v));
  intros; simpl; f_equal*.
  pick_fresh x. symmetry. unfold inc_if_eq. simpl.
  apply open_ee_rec_s_term_core with (j := 0) (e' := s_trm_fvar x).
  auto. symmetry; auto.
Qed.

Lemma plug_s_term_open_ee_rec : forall C e n e', s_term e ->
  open_ee_rec source n e' (plug C e) = plug (ctx_open_ee_rec source n e' C) e.
Proof.
  induction C; intros; simpl; f_equal; auto using open_ee_rec_s_term.
Qed.

(* Other properties of contexts *)

Theorem s_eval_context_implies_s_context : forall E,
  s_eval_context E -> s_context E.
Proof.
  induction 1; auto.
Qed.

Theorem plug_preserves_s_term : forall C e,
  s_context C -> s_term e -> s_term (plug C e).
Proof.
  induction 1; intros; simpl; auto.
  apply s_term_value. apply_fresh s_value_abs as x; auto.
  rewrite* plug_s_term_open_ee_rec.
Qed.

Theorem plug_preserves_s_typing : forall C e G_e s_e G s,
  s_context_typing C G_e s_e G s -> s_typing G_e e s_e ->
  s_typing G (plug C e) s.
Proof.
  intros; induction H; simpl; eauto using s_typing_weaken.
  apply_fresh s_typing_abs as x; auto.
  rewrite plug_s_term_open_ee_rec; eauto using s_typing_implies_s_term.
Qed.

(* inversion for s_type *)

Lemma s_type_arrow_inv_l : forall s1 s2,
 s_type (s_typ_arrow s1 s2) -> s_type s1.
Proof. inversion 1. assumption. Qed.

Lemma s_type_arrow_inv_r : forall s1 s2,
 s_type (s_typ_arrow s1 s2) -> s_type s2.
Proof. inversion 1. assumption. Qed.

(* inversion for s_typing *)

Lemma s_typing_var_inv : forall G x s,
  s_typing G (s_trm_fvar x) s -> binds x s G.
Proof. inversion 1. assumption. Qed.

Lemma s_typing_abs_inv : forall G e s1 s2,
  s_typing G (s_trm_abs s1 e) (s_typ_arrow s1 s2) ->
  exists L, forall x, x \notinLN L ->
  s_typing (G & x ~ s1) (s_open_ee_var e x) s2.
Proof. inversion 1. exists L. intros. apply* H4. Qed.

Lemma s_typing_if_inv_test : forall G e1 e2 e3 s,
 s_typing G (s_trm_if e1 e2 e3) s -> s_typing G e1 s_typ_bool.
Proof. inversion 1. assumption. Qed.

Lemma s_typing_if_inv_true : forall G e1 e2 e3 s,
 s_typing G (s_trm_if e1 e2 e3) s -> s_typing G e2 s.
Proof. inversion 1. assumption. Qed.

Lemma s_typing_if_inv_false : forall G e1 e2 e3 s,
 s_typing G (s_trm_if e1 e2 e3) s -> s_typing G e3 s.
Proof. inversion 1. assumption. Qed.

Lemma s_typing_app_inv : forall G e1 e2 s,
  s_typing G (s_trm_app e1 e2) s ->
  exists s', s_typing G e1 (s_typ_arrow s' s) /\ s_typing G e2 s'.
Proof. inversion 1. exists s1. auto. Qed.

Lemma s_typing_app_inv_l : forall G e1 e2 s,
  s_typing G (s_trm_app e1 e2) s ->
  exists s', s_typing G e1 (s_typ_arrow s' s).
Proof. inversion 1. exists s1. assumption. Qed.

Lemma s_typing_app_inv_r : forall G e1 e2 s,
  s_typing G (s_trm_app e1 e2) s -> exists s', s_typing G e2 s'.
Proof. inversion 1. exists s1. assumption. Qed.
