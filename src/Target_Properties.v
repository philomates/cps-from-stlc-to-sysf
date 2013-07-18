(***************************************************************************
* Basic properties of target language                                      *
* William J. Bowman, Phillip Mates & James T. Perconti                     *
***************************************************************************)

Require Import LibWfenv Target_Definitions Core_Infrastructure.

(* ********************************************************************** *)

Lemma t_wft_implies_t_type : forall D t, t_wft D t -> t_type t.
Proof. induction 1; eauto. Qed.
Hint Resolve t_wft_implies_t_type.

Theorem t_typing_implies_ok : forall D G m t,
  t_typing D G m t -> ok D.
Proof.
  induction 1; auto.
  pick_fresh x. pick_fresh X. assert (ok (D & X ~ star)); auto.
  apply* (H1 x X).
Qed.

Theorem t_typing_implies_wfenv : forall D G m t,
  t_typing D G m t -> wfenv (t_wft D) G.
Proof.
   induction 1; auto.
Qed.

Theorem t_typing_implies_t_term : forall D G m t,
  t_typing D G m t -> t_term m.
Proof.
  induction 1; eauto.
  apply t_term_value. apply_fresh* t_value_abs as X.
  pick_fresh x.
  assert (wfenv (t_wft (D & X ~ star)) (G & x ~ open_tt t1 (t_typ_fvar X))).
    eapply t_typing_implies_wfenv. apply* H0.
  apply wfenv_push_inv in H2. destruct H2. destruct* H3.
Qed.

Lemma t_typing_wft : forall D G m t,
  t_typing D G m t -> t_wft D t.
Proof.
  intros.
  assert (ok D). apply* t_typing_implies_ok.
  induction H; auto.
  eapply wfenv_binds. exact H1. exact H2.
  pick_fresh x. apply_fresh t_wft_arrow as X.
    assert (wfenv (t_wft (D & X ~ star)) (G & x ~ open_tt t1 (t_typ_fvar X))).
      eapply t_typing_implies_wfenv. apply* H1.
    apply wfenv_push_inv in H3. destruct H3. destruct* H4.
    apply* (H2 x X).
  pick_fresh x. apply* (H3 x).
  pick_fresh x. apply* (H3 x).
  (* TODO: need a substitution lemma to handle app case -JTP *)
Admitted.

(** weakening (not sure where these might be needed but
 *             some of them were in here before) *)

Lemma t_wft_weaken_generalized : forall G T E F,
  t_wft (E & G) T -> ok (E & F & G) ->
  t_wft (E & F & G) T.
Proof.
  (* TODO: I don't know what half the tactics in this proof are;
   * we should figure that out because they seem pretty useful -JTP *)
  intros. gen_eq K: (E & G). gen E F G.
  induction H; intros; subst; eauto.
  (* case: var *)
  apply* t_wft_var. apply* binds_weaken.
  (* case: all *)
  apply_fresh* t_wft_arrow as Y. apply_ih_bind* H0. apply_ih_bind* H2.
Qed.

Lemma t_wft_weaken : forall T E F,
  t_wft E T -> ok (E & F) -> t_wft (E & F) T.
Proof.
  intros. rewrite <- (concat_empty_r (E & F)).
  apply t_wft_weaken_generalized; rewrite* concat_empty_r.
Qed.

Lemma wfenv_t_wft_weaken : forall D X G,
  wfenv (t_wft D) G -> ok (D & X ~ star) -> wfenv (t_wft (D & X ~ star)) G.
Proof.
  intros. apply* (wfenv_implies (t_wft D)). intros. apply* t_wft_weaken.
Qed.
