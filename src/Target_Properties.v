(***************************************************************************
* Basic properties of target language                                      *
* William J. Bowman, Phillip Mates & James T. Perconti                     *
***************************************************************************)

Require Import LibWfenv Target_Definitions Core_Infrastructure.

(* ********************************************************************** *)

Lemma t_wft_implies_ok : forall D t, t_wft D t -> ok D.
Proof.
  induction 1; auto.
  pick_fresh X. assert (ok (D & X ~ star)); auto.
Qed.

Lemma t_wft_implies_t_type : forall D t, t_wft D t -> t_type t.
Proof. induction 1; eauto. Qed.
Hint Resolve t_wft_implies_ok t_wft_implies_t_type.

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

Lemma subst_tt_open_tt_rec : forall t t' n d, wfenv t_type d ->
  subst_tt d (open_tt_rec n t' t) =
  open_tt_rec n (subst_tt d t') (subst_tt d t).
Admitted.

Lemma subst_tt_open_tt : forall t t' d, wfenv t_type d ->
  subst_tt d (open_tt t t') =
  open_tt (subst_tt d t) (subst_tt d t').
Admitted.

Lemma subst_tt_open_tt_var : forall t X d, X # d -> wfenv t_type d ->
  (open_tt_var (subst_tt d t) X) = (subst_tt d (open_tt_var t X)).
Proof.
  intros. simpl. rewrite* subst_tt_open_tt. simpl.
  apply get_none in H. rewrite* H.
Qed.

Lemma subst_tt_intro : forall X t t',
  X \notin fv_tt t -> t_type t' ->
  open_tt t t' = subst_tt (X ~ t') (open_tt_var t X).
Admitted.

(* TODO name this and next lemma better (or at least uniquely)
        figure out if this is provable
        see also note in the next proof -JTP
Lemma t_wft_subst_tt : forall D X t, X # D ->
  (forall t', t_wft D t -> t_wft D (subst_tt (X ~ t') t)) ->
  t_wft (D & X ~ star) t.
 *)
  

Lemma t_wft_subst_tt : forall D d t,
  ok (D & map (fun _ => star) d) -> wfenv (t_wft D) d ->
  t_wft (D & map (fun _ => star) d) t ->
  t_wft D (subst_tt d t).
Proof.
  intros. remember (map (fun _ => star) d) as D'. gen d.
  remember (D & D') as DD. gen D. gen D'.
  induction H1; intros; simpl.
  case_eq (get X d); intros.
    eapply wfenv_binds. exact H2. apply H3.
    apply* t_wft_var. subst*.
    apply get_none_inv in H3.
    assert (X # D'); subst. auto.
    eapply binds_concat_left_inv; eauto.
  subst. apply* t_wft_bool.
  apply* t_wft_pair.
  apply_fresh t_wft_arrow as X; subst;
  rewrite* subst_tt_open_tt_var.
  assert (forall t, t_wft D0 t ->
          t_wft D0 (subst_tt (d & X ~ t) (open_tt_var t1 X))).
    intros. apply H1 with (D' := map (fun _ => star) d & X ~ star); auto.
    rewrite* concat_assoc. rewrite* map_push. apply* (wfenv_push (t_wft D0)).
  skip.
  (* still stuck; need to get this part of this proof and also
     prove the other lemmas above. some of them should perhaps be moved
     to Core_Infrastructure.v -JTP *)
  apply* (wfenv_implies (t_wft D0)).
  assert (forall t, t_wft D0 t ->
          t_wft D0 (subst_tt (d & X ~ t) (open_tt_var t2 X))).
    intros. apply H3 with (D' := map (fun _ => star) d & X ~ star); auto.
    rewrite* concat_assoc. rewrite* map_push. apply* (wfenv_push (t_wft D0)).
Admitted.

Lemma t_wft_arrow_apply : forall D t1 t2 t,
  t_wft D (t_typ_arrow t1 t2) -> t_wft D t ->
  t_wft D (open_tt t2 t).
Proof.
  intros. inversion H. subst.
  pick_fresh X.
  assert (t_wft (D & X ~ star) (open_tt t2 (t_typ_fvar X))); auto.
  rewrite* (subst_tt_intro X).
  apply t_wft_subst_tt; try rewrite map_single; auto.
  apply* ok_push. apply wfenv_single; auto.
Qed.

Theorem t_typing_implies_t_wft : forall D G m t,
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
  eapply t_wft_arrow_apply.
  apply* IHt_typing1. auto.
Qed.

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
