Require Import LibWfenv Core_Infrastructure
               Source_Definitions Target_Definitions
               Source_Properties Target_Properties
               Cps_Trans_Definitions.
Require Import CpdtTactics2.
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq path Eqdep.
Require Import Recdef.

(* CPS type translation properties *)
Lemma cps_type_trans_preserves_well_formed_types : forall s,
  s_type s -> t_type (s+).
Proof.
  induction 1; auto.
  simpl. apply_fresh t_type_arrow as X; simpl; auto.
  apply t_type_pair; rewrite* open_tt_rec_t_type.
  apply_fresh t_type_arrow as Y; rewrite* open_tt_rec_t_type.
Qed.

Lemma cps_type_trans_preserves_well_formed_types_ssr : forall s,
  s_type s -> t_type (s+).
Proof.
  case.
  move/eqP.
Qed.

Lemma cps_type_trans_preserves_wft : forall s,
  s_type s -> t_wft empty (s+).
Proof.
  induction 1; auto.
  apply_fresh t_wft_arrow as X; simpl; auto.
  apply t_wft_pair. rewrite* open_tt_rec_t_type. apply* t_wft_weaken.
  apply_fresh t_wft_arrow as Y; simpl; auto.
  repeat rewrite* open_tt_rec_t_type. repeat apply* t_wft_weaken.
Qed.

Lemma cps_type_trans_preserves_wfenv : forall G,
  wfenv s_type G -> wfenv (t_wft empty) (map cps_type_trans G).
Proof.
  apply wfenv_ind.
  rewrite map_empty. apply wfenv_empty.
  intros.
  rewrite map_push.
  apply wfenv_push; auto.
  apply* cps_type_trans_preserves_wft.
Qed.

(* CPS term translation properties *)
(* compiler only defined on well-typed source terms *)
Lemma cps_trans_implies_s_typing : forall G e s u,
  cps_trans G e s u -> s_typing G e s.
Proof. induction 1; eauto. Qed.

(* hints for following lemma *)
Hint Local Resolve
     cps_type_trans_preserves_wfenv 
     cps_type_trans_preserves_wft
     cps_type_trans_preserves_well_formed_types
     (wfenv_binds s_type)
     cps_trans_implies_s_typing
     t_wft_weaken.

Ltac prove_app :=
  match goal with
    | [ |- t_typing (empty & ?X ~ star) _ (t_trm_app _ _ _) _] =>
      replace (t_typ_fvar X) with (open_tt (t_typ_fvar X) dummy_type); auto;
      apply* t_typing_app end.

Ltac simplify_t_wft_arrow :=
  let Y := fresh "Y" in
    apply_fresh t_wft_arrow as Y; simpl; repeat rewrite* open_tt_rec_t_type; try apply* t_wft_var.

Ltac prove_t_wft :=
  match goal with
    | [ |- t_wft _ (t_typ_arrow _ _)] => simplify_t_wft_arrow; prove_t_wft
    | [ |- t_wft _ (t_typ_pair _ _)] => apply* t_wft_pair; prove_t_wft
    | [ |- (t_wft _ _)] =>
      apply* t_wft_weaken; repeat apply* ok_push; auto using cps_type_trans_preserves_wft; prove_t_wft end.

Ltac prove_t_value_typing :=
  match goal with
    | [ |- t_value_typing _ _ (t_trm_fvar _) _] => apply* t_value_typing_var
    | [ |- t_value_typing _ _ t_trm_true _] => apply* t_value_typing_true
    | [ |- t_value_typing _ _ t_trm_false _] => apply* t_value_typing_false
    | [ |- t_value_typing _ _ (t_trm_abs _ _) _] =>
      let y := fresh "y" in apply_fresh* t_value_typing_abs as y; intros; simpl end;
  repeat rewrite* open_tt_rec_t_type;
  repeat apply wfenv_push; try apply (wfenv_implies (t_wft empty)); auto;
  try apply cps_type_trans_preserves_wfenv; try apply* s_typing_implies_wfenv;
  try prove_t_wft.

(* type-preserving compilation *)
Lemma cps_trans_implies_t_typing : forall G e s u,
  cps_trans G e s u -> t_value_typing empty (map cps_type_trans G) u (s%).
Proof.
  induction 1;
  apply_fresh* t_value_typing_abs as k; (* all cases start with lambda k. _ *)
  try solve [apply* cps_type_trans_preserves_wfenv; apply* s_typing_implies_wfenv];
  intros; simpl;
  rename x into k. (* I dunno why the "as k" above doesn't work but whatever *)

  (* variable case *)
  prove_app; prove_t_value_typing.

  (* true case *)
  prove_app; prove_t_value_typing.

  (* false case *)
  prove_app; prove_t_value_typing.

  (* abs case *)
  assert (s_type s2).
    apply* s_typing_implies_s_type. apply* cps_trans_implies_s_typing. apply* (H k).
  repeat rewrite* open_tt_rec_t_type. unfold inc_if_eq. simpl.
  prove_app; simpl. (* k (lambda ...) *)
    (* k *)
    prove_t_value_typing.

    (* (lambda ...) *)
    simpl. repeat rewrite* open_tt_rec_t_type. prove_t_value_typing.
    apply_fresh t_typing_let_fst as x; simpl. prove_t_value_typing.
    apply_fresh t_typing_let_snd as k'; simpl. prove_t_value_typing.
    replace (t_typ_fvar X0) with (open_tt (t_typ_bvar 0) (t_typ_fvar X0)); auto.
    unfold inc_if_eq. cases_if*.
    apply t_typing_app with (t1 := t_typ_arrow (s2+) (t_typ_bvar 1));
    auto; simpl; repeat rewrite* open_tt_rec_t_type.
    rewrite* open_ee_rec_t_term;
    rewrite* t_open_ee_rec_open_te_rec; rewrite* open_te_rec_t_term;
    rewrite* t_open_ee_rec_open_ee_rec; rewrite* open_ee_rec_t_term;
    rewrite* t_open_ee_rec_open_te_rec; rewrite* open_te_rec_t_term;
    rewrite* t_open_ee_rec_open_ee_rec; rewrite* open_ee_rec_t_term.
    apply t_value_typing_weaken.
    apply t_value_typing_weaken_generalized. apply t_value_typing_weaken_generalized.
    repeat apply* t_value_typing_weaken_delta.
    rewrite <- map_push.
    apply* H0.
    (* clean up after all those weakens *)
    repeat apply wfenv_push; auto. apply* (wfenv_implies (t_wft empty)).
    apply cps_type_trans_preserves_wfenv. apply* s_typing_implies_wfenv.
    prove_t_wft.

    repeat apply wfenv_push; auto. apply* (wfenv_implies (t_wft empty)).
    apply cps_type_trans_preserves_wfenv. apply* s_typing_implies_wfenv.
    prove_t_wft. prove_t_wft.
 
    repeat apply wfenv_push; auto. apply* (wfenv_implies (t_wft empty)).
    apply cps_type_trans_preserves_wfenv. apply* s_typing_implies_wfenv.
    prove_t_wft. prove_t_wft. prove_t_wft.

    (* ok on to k' finally *)
    prove_t_value_typing.

  (* if case *)
  assert (s_type s). apply* s_typing_implies_s_type.
  replace (t_typ_fvar X) with (open_tt (t_typ_bvar 0) (t_typ_fvar X)); auto.
  apply* t_typing_app; simpl.
    (* u1 *)
    rewrite* open_ee_rec_t_term. rewrite* open_te_rec_t_term. rewrite* open_tt_rec_t_type.
    apply* t_value_typing_weaken. apply* t_value_typing_weaken_delta. apply wfenv_push; auto.
      apply (wfenv_implies (t_wft empty)); auto;
        apply cps_type_trans_preserves_wfenv; apply* s_typing_implies_wfenv.
      prove_t_wft.
    
    (* if x then u2 else u3 *)
    unfold inc_if_eq. cases_if*.
    prove_t_value_typing. apply* t_typing_if; try prove_t_value_typing;
    replace (t_typ_fvar X) with (open_tt (t_typ_bvar 0) (t_typ_fvar X)); auto;
    apply* t_typing_app; simpl;
    try (rewrite* open_te_rec_t_term; rewrite* open_ee_rec_t_term;
         rewrite* open_te_rec_t_term; rewrite* open_ee_rec_t_term;
         repeat apply* t_value_typing_weaken; try solve [repeat apply* t_value_typing_weaken_delta];
         repeat apply wfenv_push; auto; try prove_t_wft; apply (wfenv_implies (t_wft empty)); auto;
         apply cps_type_trans_preserves_wfenv; apply* s_typing_implies_wfenv);
    simpl; prove_t_value_typing.

  (* app case *)
  assert (s_type s1). apply* s_typing_implies_s_type.
  assert (s_type s2). apply* s_typing_implies_s_type.
  replace (t_typ_fvar X) with (open_tt (t_typ_bvar 0) (t_typ_fvar X)); auto.
  apply* t_typing_app; simpl.
    (* u1 *)
    rewrite* open_ee_rec_t_term. rewrite* open_te_rec_t_term. rewrite* open_tt_rec_t_type.
    apply* t_value_typing_weaken. apply* t_value_typing_weaken_delta. apply wfenv_push; auto.
      apply (wfenv_implies (t_wft empty)); auto;
        apply cps_type_trans_preserves_wfenv; apply* s_typing_implies_wfenv.
      prove_t_wft.
    
    (* u2 *)
    unfold inc_if_eq. cases_if*.
    prove_t_value_typing.
    replace (t_typ_fvar X) with (open_tt (t_typ_bvar 0) (t_typ_fvar X)); auto.
    apply* t_typing_app; simpl.
    rewrite* open_te_rec_t_term; rewrite* open_ee_rec_t_term;
    rewrite* open_te_rec_t_term; rewrite* open_ee_rec_t_term.
    repeat apply* t_value_typing_weaken; try solve [repeat apply* t_value_typing_weaken_delta];
    repeat apply wfenv_push; auto; try prove_t_wft; apply (wfenv_implies (t_wft empty)); auto;
    apply cps_type_trans_preserves_wfenv; apply* s_typing_implies_wfenv.
    
    (* x1 x2 *)
    simpl. rewrite* open_tt_rec_t_type. prove_t_value_typing.
    replace (t_typ_fvar X) with (open_tt (t_typ_bvar 0) (t_typ_fvar X)); auto.
    apply* t_typing_app; simpl. prove_t_value_typing. simpl. apply* t_value_typing_pair; prove_t_value_typing.
Qed.
