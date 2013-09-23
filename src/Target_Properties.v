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

(* Weakening for t_wft *)

Lemma t_wft_weaken_generalized : forall G T E F,
  t_wft (E & G) T -> ok (E & F & G) ->
  t_wft (E & F & G) T.
Proof.
  intros. gen_eq K: (E & G). gen E F G.
  induction H; intros; subst; eauto.
  apply* t_wft_var. apply* binds_weaken.
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

(* Basic properties of subst_tt and open_tt *)

Lemma open_tt_rec_t_type_core : forall t j t' t'' i, i <> j ->
  (open_tt_rec j t' t) = open_tt_rec i t'' (open_tt_rec j t' t) ->
  t = open_tt_rec i t'' t.
Proof.
  induction t; intros; simpl in *; inversion H0; f_equal*.
  case_if*. apply EqNat.beq_nat_true in H1. subst.
  case_if*. apply EqNat.beq_nat_true in H1. false.
  simpl in *. case_if*. apply EqNat.beq_nat_false in H3. false.
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
  case_if*. cases* (get v d).
  apply* open_tt_rec_t_type. apply* (wfenv_binds t_type d v).
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
  cases_if*. simpl. rewrite get_single. cases_if*.
  rewrite get_single. cases_if*. false. apply* notin_same.
Qed.

Lemma subst_tt_intro : forall X t t',
  X \notin fv_tt t -> t_type t' ->
  open_tt t t' = subst_tt (X ~ t') (open_tt_var t X).
Proof.
  intros. apply* subst_tt_intro_rec.
Qed.  

(* XXX: unused *)
Lemma subst_tt_preserves_t_type : forall d t,
  t_type t -> wfenv t_type d -> t_type (subst_tt d t).
Proof.
  induction 1; intros; simpl; auto.
  cases* (get x d). eapply wfenv_binds; eassumption.
  apply_fresh t_type_arrow as X;
  replace (t_typ_fvar X) with (subst_tt d (t_typ_fvar X));
  try rewrite <- subst_tt_open_tt; auto; simpl;
  case_eq (get X d); intros; try apply binds_fresh_inv in H4;
  try contradiction; auto.
Qed.

(* subst_tt preserves t_wft *)

Lemma subst_tt_preserves_t_wft_generalized : forall D D' t X t',
  X # (D & D') -> t_wft (D & D') t' -> t_wft (D & X ~ star & D') t ->
  t_wft (D & D') (subst_tt (X ~ t') t).
Proof.
  intros. gen_eq DXD' : (D & X ~ star & D'). gen D X D'.
  induction H1; intros; subst; simpl; auto.
  rewrite get_single. cases_if*.
    apply* t_wft_var. apply* binds_subst.
  apply_fresh t_wft_arrow as Y;
  rewrite* subst_tt_open_tt_var. apply_ih_bind* H0. apply* t_wft_weaken.
  apply wfenv_single. apply* t_wft_implies_t_type.
  apply_ih_bind* H2. apply* t_wft_weaken.
  apply wfenv_single. apply* t_wft_implies_t_type.
Qed.

Lemma subst_tt_preserves_t_wft : forall D t X t',
  X # D -> t_wft D t' -> t_wft (D & X ~ star) t ->
  t_wft D (subst_tt (X ~ t') t).
Proof.
  intros.
  rewrite <- (concat_empty_r D). rewrite <- (concat_empty_r D) in H0.
  rewrite <- (concat_empty_r (D & X ~ star)) in H1.
  apply* subst_tt_preserves_t_wft_generalized.
Qed.

Lemma t_wft_arrow_apply : forall D t1 t2 t,
  t_wft D (t_typ_arrow t1 t2) -> t_wft D t ->
  t_wft D (open_tt t2 t).
Proof.
  intros. inverts H.
  pick_fresh X. rewrite* (subst_tt_intro X). apply* subst_tt_preserves_t_wft.
Qed.

(* Regularity of t_typing *) 

Theorem t_typing_implies_ok : forall D G m t,
  t_typing D G m t -> ok D.
Proof.
  apply (t_typing_mut (fun D G m t pf => ok D)
                      (fun D G u t pf => ok D)); auto.
  intros. pick_fresh x. pick_fresh X. assert (ok (D & X ~ star)); auto.
  apply* (H x X).
Qed.

Corollary t_value_typing_implies_ok : forall D G u t,
  t_value_typing D G u t -> ok D.
Proof. eauto using t_typing_implies_ok. Qed.

Theorem t_typing_implies_wfenv : forall D G m t,
  t_typing D G m t -> wfenv (t_wft D) G.
Proof.
  apply (t_typing_mut (fun D G m t pf => wfenv (t_wft D) G)
                      (fun D G u t pf => wfenv (t_wft D) G)); auto.
Qed.

Corollary t_value_typing_implies_wfenv : forall D G u t,
  t_value_typing D G u t -> wfenv (t_wft D) G.
Proof. eauto using t_typing_implies_wfenv. Qed.

Theorem t_typing_implies_t_term : forall D G m t,
  t_typing D G m t -> t_term m.
Proof.
  apply (t_typing_mut (fun D G m t pf => t_term m)
                      (fun D G u t pf => t_value u)); eauto.
  intros. apply_fresh* t_value_abs as X.
  pick_fresh x.
  assert (wfenv (t_wft (D & X ~ star)) (G & x ~ open_tt t1 (t_typ_fvar X))).
    eapply t_typing_implies_wfenv. apply* t.
  apply wfenv_push_inv in H0. destructs* H0.
Qed.

Theorem t_value_typing_implies_t_value : forall D G u t,
  t_value_typing D G u t -> t_value u.
Proof.
  apply (t_value_typing_mut (fun D G m t pf => t_term m)
                            (fun D G u t pf => t_value u)); eauto.
  intros. apply_fresh* t_value_abs as X.
  pick_fresh x.
  assert (wfenv (t_wft (D & X ~ star)) (G & x ~ open_tt t1 (t_typ_fvar X))).
    eapply t_typing_implies_wfenv. apply* t.
  apply wfenv_push_inv in H0. destructs* H0.
Qed.

Hint Resolve t_typing_implies_t_term t_value_typing_implies_t_value.

Theorem t_typing_implies_t_wft : forall D G m t,
  t_typing D G m t -> t_wft D t.
Proof.
  apply (t_typing_mut (fun D G m t pf => t_wft D t)
                      (fun D G u t pf => t_wft D t)); intros; auto.
  pick_fresh x. apply* (H0 x).
  pick_fresh x. apply* (H0 x).
  apply* t_wft_arrow_apply.
  apply* (wfenv_binds (t_wft D)).
  pick_fresh x. apply_fresh t_wft_arrow as X; try (apply* (H x X)).
    assert (wfenv (t_wft (D & X ~ star)) (G & x ~ open_tt_var t1 X)).
      apply* t_typing_implies_wfenv.
    apply wfenv_push_inv in H0. destructs* H0.
Qed.

Corollary t_value_typing_implies_t_wft : forall D G u t,
  t_value_typing D G u t -> t_wft D t.
Proof. eauto using t_typing_implies_t_wft. Qed.

(* weakening for t_typing *)

Lemma t_typing_weaken_delta_generalized : forall D D' D'' G m t,
  t_typing (D & D'') G m t -> ok (D & D' & D'') ->
  t_typing (D & D' & D'') G m t.
Proof.
  intros. gen_eq DD : (D & D''). gen D D' D''.
  apply (t_typing_mut
          (fun DD G m t pf =>
            forall D D' D'', ok (D & D' & D'') -> DD = D & D'' ->
            t_typing (D & D' & D'') G m t)
          (fun DD G u t pf =>
            forall D D' D'', ok (D & D' & D'') -> DD = D & D'' ->
            t_value_typing (D & D' & D'') G u t));
  intros; subst; auto using t_wft_weaken_generalized;
  try (pick_fresh x; apply_fresh t_value_typing_abs as X);
  eauto using t_wft_weaken_generalized, (wfenv_implies (t_wft (D0 & D''))).
  intros. apply_ih_bind* H0.
Qed.

Lemma t_typing_weaken_delta : forall D D' G m t,
  t_typing D G m t -> ok (D & D') -> t_typing (D & D') G m t.
Proof.
  intros. rewrite <- (concat_empty_r (D & D')) in *.
  apply* t_typing_weaken_delta_generalized. rewrite* concat_empty_r.
Qed.

Lemma t_typing_weaken_generalized : forall D G G' G'' m t,
  t_typing D (G & G'') m t -> wfenv (t_wft D) (G & G' & G'') ->
  t_typing D (G & G' & G'') m t.
Proof.
  intros. gen_eq GG : (G & G''). gen G G' G''.
  apply (t_typing_mut
          (fun D GG m t pf =>
            forall G G' G'', wfenv (t_wft D) (G & G' & G'') -> GG = G & G'' ->
            t_typing D (G & G' & G'') m t)
          (fun D GG u t pf =>
            forall G G' G'', wfenv (t_wft D) (G & G' & G'') -> GG = G & G'' ->
            t_value_typing D (G & G' & G'') u t));
  intros; subst; eauto.
  apply_fresh* t_typing_let_fst as x. apply_ih_bind* H1.
    apply wfenv_push; auto.
    apply t_value_typing_implies_t_wft in t3. inverts* t3.
  apply_fresh* t_typing_let_snd as x. apply_ih_bind* H1.
    apply wfenv_push; auto.
    apply t_value_typing_implies_t_wft in t3. inverts* t3.
  apply* t_value_typing_var. apply* binds_weaken. eapply wfenv_ok. eauto.
  apply_fresh* t_value_typing_abs as X. intros. apply_ih_bind* H0.
    apply wfenv_push; auto.
    apply* (wfenv_implies (t_wft D0)). eauto using t_wft_weaken.
    eapply wfenv_push_inv. eapply t_typing_implies_wfenv. apply* (t0 x X).
Qed.

Lemma t_typing_weaken : forall D G G' m t,
  t_typing D G m t -> wfenv (t_wft D) (G & G') -> t_typing D (G & G') m t.
Proof.
  intros. rewrite <- (concat_empty_r (G & G')) in *.
  apply* t_typing_weaken_generalized. rewrite* concat_empty_r.
Qed.

(* basic properties of subst_ee and open_ee *)

Lemma open_ee_rec_t_term_core : forall m j m' m'' i, i <> j ->
  (open_ee_rec target j m' m) =
    open_ee_rec target i m'' (open_ee_rec target j m' m) ->
  m = open_ee_rec target i m'' m.

Lemma open_ee_rec_t_term : forall m m' i,
  t_term m -> open_ee_rec target i m' m = m.

Lemma plug_t_term_open_ee_rec : forall C m i m', t_term m ->
  open_ee_rec target i m' (plug C m) = plug (ctx_open_ee_rec target i m' C) m.

(* regularity of t_context_typing *)

Theorem t_context_typing_implies_ok_hole : forall b C Dh Gh th D G t,
  t_context_typing b C Dh Gh th D G t -> ok Dh.
Proof.
  apply (t_context_typing_mut (fun b C Dh Gh th D G t pf => ok Dh)
                              (fun b C Dh Gh th D G t pf => ok Dh));
  intros; eauto;
  pick_fresh x; pick_fresh X; try apply* (H x X); apply* (H x).
Qed.

Theorem t_context_typing_implies_wfenv_hole : forall b C Dh Gh th D G t,
  t_context_typing b C Dh Gh th D G t -> wfenv (t_wft Dh) Gh.
Proof.
  apply (t_context_typing_mut
          (fun b C Dh Gh th D G t pf => wfenv (t_wft Dh) Gh)
          (fun b C Dh Gh th D G t pf => wfenv (t_wft Dh) Gh)); intros; eauto;
  pick_fresh x; pick_fresh X; try apply* (H x X); apply* (H x).
Qed.

Theorem t_context_typing_implies_t_wft_hole : forall b C Dh Gh th D G t,
  t_context_typing b C Dh Gh th D G t -> t_wft Dh th.
  apply (t_context_typing_mut (fun b C Dh Gh th D G t pf => t_wft Dh th)
                              (fun b C Dh Gh th D G t pf => t_wft Dh th));
  intros; eauto;
  pick_fresh x; pick_fresh X; try apply* (H x X); apply* (H x).
Qed.

Theorem t_context_typing_implies_ok : forall b C Dh Gh th D G t,
  t_context_typing b C Dh Gh th D G t -> ok D.
Proof.
  apply (t_context_typing_mut (fun b C Dh Gh th D G t pf => ok D)
                              (fun b C Dh Gh th D G t pf => ok D));
  intros; eauto; pick_fresh x; pick_fresh X; try apply* (H x).
  eapply ok_push_inv_ok. apply* (H x X).
Qed.

Theorem t_context_typing_implies_wfenv : forall b C Dh Gh th D G t,
  t_context_typing b C Dh Gh th D G t -> wfenv (t_wft D) G.
Proof.
  apply (t_context_typing_mut
          (fun b C Dh Gh th D G t pf => wfenv (t_wft D) G)
          (fun b C Dh Gh th D G t pf => wfenv (t_wft D) G)); intros; eauto;
  pick_fresh x; eapply wfenv_push_inv_wfenv; apply* (H x).
Qed.

Theorem t_context_typing_implies_t_wft : forall b C Dh Gh th D G t,
  t_context_typing b C Dh Gh th D G t -> t_wft D t.
Proof.
  apply (t_context_typing_mut (fun b C Dh Gh th D G t pf => t_wft D t)
                              (fun b C Dh Gh th D G t pf => t_wft D t));
  intros; eauto using t_typing_implies_t_wft;
  try apply* t_wft_weaken;
  try (pick_fresh x; apply* (H x)).
  pick_fresh x. eauto using t_typing_implies_t_wft, (t3 x).
  pick_fresh x. eauto using t_typing_implies_t_wft, (t3 x).
  inverts H. pick_fresh X. rewrite* (subst_tt_intro X).
    apply* subst_tt_preserves_t_wft.
  apply t_value_typing_implies_t_wft in t0. inverts t0.
    pick_fresh X. rewrite* (subst_tt_intro X).
    apply* subst_tt_preserves_t_wft.
  pick_fresh x. apply_fresh t_wft_arrow as X.
    eapply wfenv_binds. eapply t_context_typing_implies_wfenv.
      apply* (t x X). auto.
    apply* (H x X).
Qed.

Theorem t_context_typing_implies_t_context : forall b C Dh Gh th D G t,
  t_context_typing b C Dh Gh th D G t -> t_context b C.
Proof.
  eapply (t_context_typing_mut
           (fun b C Dh Gh th D G t pf => t_context b C)
           (fun b C Dh Gh th D G t pf => t_value_context b C)); intros; eauto.
  pick_fresh x. apply_fresh* t_value_context_abs as X.
  assert (IH : wfenv (t_wft (D & X ~ star)) (G & x ~ open_tt_var t1 X)).
    eapply t_context_typing_implies_wfenv. apply* (t x X).
  apply wfenv_push_inv in IH. destructs IH. apply* t_wft_implies_t_type.
Qed.

(* other properties of contexts *)

Theorem t_eval_context_implies_t_context : forall E,
 t_eval_context E -> t_context false E.
Proof. intros. inverts* H. Qed.

Theorem plug_preserves_t_term : forall C m,
  t_context false C -> t_term m -> t_term (plug C m).
(* TODO more versions for various cases? *)

Theorem plug_preserves_t_typing : forall C e D_e G_e t_e D G t,
  t_context_typing false C D_e G_e t_e D G t -> t_typing D_e G_e e t_e ->
  t_typing D G (plug C e) t.
