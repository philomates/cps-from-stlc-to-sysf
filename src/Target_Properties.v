(***************************************************************************
* Basic properties of target language                                      *
* William J. Bowman, Phillip Mates & James T. Perconti                     *
***************************************************************************)

Require Import LibWfenv Target_Definitions Core_Infrastructure.

(* ********************************************************************** *)

(* Regularity of t_wft *)

Lemma t_wft_implies_ok : forall D t, t_wft D t -> ok D.
Proof.
  induction 1; auto.
  pick_fresh X. assert (ok (D & X ~ star)); auto.
Qed.

Lemma t_wft_implies_t_type : forall D t, t_wft D t -> t_type t.
Proof. induction 1; eauto. Qed.
Hint Resolve t_wft_implies_ok t_wft_implies_t_type.

(* weakening for t_wft *)

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

(* Basic properties of substitution *)

Lemma open_tt_rec_t_type_core : forall t j t' t'' i, i <> j ->
  (open_tt_rec j t' t) = open_tt_rec i t'' (open_tt_rec j t' t) ->
  t = open_tt_rec i t'' t.
Proof.
  induction t; intros; simpl in *; inversion H0; f_equal*.
  (* is there a tactic that can do this automatically from here? *)
  case_eq (EqNat.beq_nat i n); intros; auto.
  apply EqNat.beq_nat_true in H1. subst.
  case_eq (EqNat.beq_nat j n); intros; auto.
  apply EqNat.beq_nat_true in H1. subst. destruct* H.
  rewrite H1 in H0. simpl in H0. rewrite* NPeano.Nat.eqb_refl in H0.
Qed.

Lemma open_tt_rec_t_type : forall t t' n, t_type t ->
  t = open_tt_rec n t' t.
Proof.
  intros; gen t' n; induction H; intros; simpl in *; f_equal; auto;
  subst; pick_fresh X;
  apply open_tt_rec_t_type_core with (j := 0) (t' := t_typ_fvar X); auto.
Qed.

Lemma subst_tt_open_tt_rec : forall t t' n d, wfenv t_type d ->
  subst_tt d (open_tt_rec n t' t) =
  open_tt_rec n (subst_tt d t') (subst_tt d t).
Proof.
  induction t; intros; auto; simpl; try f_equal; auto. 
  destruct (EqNat.beq_nat n0 n); auto.
  case_eq (get v d); intros; auto.
    assert (t_type t). apply* (wfenv_binds t_type d v).
    apply* open_tt_rec_t_type.
Qed.

Lemma subst_tt_open_tt : forall t t' d, wfenv t_type d ->
  subst_tt d (open_tt t t') =
  open_tt (subst_tt d t) (subst_tt d t').
Proof.
  intros. apply* subst_tt_open_tt_rec.
Qed.

Lemma subst_tt_open_tt_var : forall t X d, X # d -> wfenv t_type d ->
  (open_tt_var (subst_tt d t) X) = (subst_tt d (open_tt_var t X)).
Proof.
  intros. simpl. rewrite* subst_tt_open_tt. simpl.
  apply get_none in H. rewrite* H.
Qed.

Lemma subst_tt_intro_rec : forall X t t' n,
  X \notin fv_tt t -> t_type t' ->
  open_tt_rec n t' t = subst_tt (X ~ t') (open_tt_rec n (t_typ_fvar X) t).
Proof.
  intros X t. gen X. induction t; intros; auto; simpl in *; try f_equal; auto.
  destruct (EqNat.beq_nat n0 n); auto. simpl. rewrite get_single. rewrite* If_l.
  rewrite get_single. rewrite* If_r.
Qed.

Lemma subst_tt_intro : forall X t t',
  X \notin fv_tt t -> t_type t' ->
  open_tt t t' = subst_tt (X ~ t') (open_tt_var t X).
Proof.
  intros. apply* subst_tt_intro_rec.
Qed.  

(* this lemma is nice and all but I'm not sure it actually helps -JTP *)
Lemma subst_tt_preserves_t_type : forall d t,
  t_type t -> wfenv t_type d -> t_type (subst_tt d t).
Proof.
  induction 1; intros; simpl; auto.
  case_eq (get x d); intros. eapply wfenv_binds; eassumption. auto.
  apply_fresh t_type_arrow as X;
  replace (t_typ_fvar X) with (subst_tt d (t_typ_fvar X));
  try rewrite <- subst_tt_open_tt; auto; simpl;
  case_eq (get X d); intros; try apply binds_fresh_inv in H4;
  try contradiction; auto.
Qed.

(* substitution preserves t_wft *)

Lemma subst_tt_preserves_t_wft_generalized : forall D D' t X t',
  X # (D & D') -> t_wft (D & D') t' -> t_wft (D & X ~ star & D') t ->
  t_wft (D & D') (subst_tt (X ~ t') t).
Proof.
  intros. remember (D & X ~ star & D') as DXD'. gen D. gen X. gen D'.
  induction H1; intros; subst; simpl; auto.
  rewrite get_single. destruct (classicT (X = X0)).
    auto.
    apply t_wft_var; auto. eapply binds_subst; eauto.
  apply_fresh t_wft_arrow as Y;
  rewrite subst_tt_open_tt_var; auto; try rewrite <- concat_assoc.
  apply H0; try rewrite concat_assoc; auto. apply* t_wft_weaken.
  apply wfenv_single. eapply t_wft_implies_t_type. eauto.
  apply H2; try rewrite concat_assoc; auto. apply* t_wft_weaken.
  apply wfenv_single. eapply t_wft_implies_t_type. eauto.
Qed.

Lemma subst_tt_preserves_t_wft : forall D t X t',
  X # D -> t_wft D t' -> t_wft (D & X ~ star) t ->
  t_wft D (subst_tt (X ~ t') t).
Proof.
  intros.
  replace D with (D & empty); replace D with (D & empty) in H0;
    try apply concat_empty_r.
  replace (D & X ~ star) with (D & X ~ star & empty) in H1;
    try apply concat_empty_r.
  apply subst_tt_preserves_t_wft_generalized; auto.
Qed.

Lemma t_wft_arrow_apply : forall D t1 t2 t,
  t_wft D (t_typ_arrow t1 t2) -> t_wft D t ->
  t_wft D (open_tt t2 t).
Proof.
  intros. inversion H. subst.
  pick_fresh X.
  assert (t_wft (D & X ~ star) (open_tt t2 (t_typ_fvar X))); auto.
  rewrite* (subst_tt_intro X).
  apply subst_tt_preserves_t_wft; try rewrite map_single; auto.
Qed.

(* Regularity of t_typing *) 

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
