(**********************************************************************
 * Prototype of logical relations, just using target language for now *
 **********************************************************************)

Require Import Program.
Require Import LibWfenv Core_Infrastructure Target_Definitions Target_Properties.

Definition atom : Type := prod trm trm.

Definition Atom (t1 t2 : typ) (a : atom) : Prop :=
  t_typing empty empty (fst a) t1 /\ t_typing empty empty (snd a) t2.

Definition AtomVal (t1 t2 : typ) (a : atom) : Prop :=
  t_value_typing empty empty (fst a) t1 /\
  t_value_typing empty empty (snd a) t2.

Definition Rel (t1 t2 : typ) (R : atom -> Prop) : Prop :=
  (forall a, R a -> (AtomVal t1 t2 a)).
(* I think equivalence-respecting property is only needed in multi-language relation *)
(*  /\ (forall u1 u2 u2', R (u1, u2) ->
        ciu_approx empty empty u2 u2' t2 -> R (u1, u2')). *)

Definition somerel := prod (prod typ typ) (atom -> Prop).

Definition relat_env := env somerel.
Definition subst1_tt (rho : relat_env) := subst_tt (map fst (map fst rho)).
Definition subst2_tt (rho : relat_env) := subst_tt (map snd (map fst rho)).
Definition subst1_te (rho : relat_env) := subst_te (map fst (map fst rho)).
Definition subst2_te (rho : relat_env) := subst_te (map snd (map fst rho)).

Definition interpD (D : env_type) (rho : relat_env) : Prop :=
  relenv (fun _ => True) D
         (fun RR => Rel (fst (fst RR)) (snd (fst RR)) (snd RR)) rho
         (fun _ _ => True).

Lemma interpD_ok : forall D rho, interpD D rho ->
  dom D = dom rho /\ ok D /\ ok rho.
Proof.
  unfold interpD. intuition. eapply relenv_dom. exact H.
  eapply wfenv_ok. eapply relenv_wfenv_1. exact H.
  eapply wfenv_ok. eapply relenv_wfenv_2. exact H.
Qed.

(* V and E relations *)

Definition termrel (t1 t2 : typ) (V : atom -> Prop) (a : atom) : Prop :=
  Atom t1 t2 a /\
  forall v1, t_eval (fst a) v1 -> exists v2, t_eval (snd a) v2 /\ V (v1, v2).

Program Fixpoint interpV (t : typ) (rho : relat_env) (a : atom)
  {measure (typ_size t)} : Prop :=
    match t with
      | t_typ_fvar X => exists RR, binds X RR rho /\ (snd RR) a
      | t_typ_bool => a = (t_trm_true, t_trm_true) \/
                      a = (t_trm_false, t_trm_false)
      | t_typ_pair t t' => exists v1 v1' v2 v2',
          a = (t_trm_pair v1 v1', t_trm_pair v2 v2') /\
          interpV t rho (v1, v2) /\ interpV t' rho (v1', v2')
      | t_typ_arrow t' t'' =>
          AtomVal (subst1_tt rho t) (subst2_tt rho t) a /\
          forall t1 t2 R u1 u2,
            Rel t1 t2 R ->
            exists L, forall X, X \notin L ->
              interpV (open_tt_var t' X) (rho & X ~ (t1, t2, R)) (u1, u2) ->
              termrel (subst1_tt (rho & X ~ (t1, t2, R)) (open_tt_var t'' X))
                      (subst2_tt (rho & X ~ (t1, t2, R)) (open_tt_var t'' X))
                      (fun a =>
                        interpV (open_tt_var t'' X) (rho & X ~ (t1, t2, R)) a)
                      (t_trm_app (fst a) t1 u1, t_trm_app (snd a) t2 u2)
      | _ => False
    end. 
Next Obligation. simpl. omega. Defined.
Next Obligation. simpl. omega. Defined.
Next Obligation. simpl. rewrite typ_size_open_var. omega. Defined.
Next Obligation. simpl. rewrite typ_size_open_var. omega. Defined.
Next Obligation. splits; intros; inversion 1. Defined.
Next Obligation. splits; intros; inversion 1. Defined.
Next Obligation. splits; intros; inversion 1. Defined.
Next Obligation. splits; intros; inversion 1. Defined.

Definition interpE (t : typ) (rho : relat_env) : atom -> Prop :=
  termrel (subst1_tt rho t) (subst2_tt rho t) (interpV t rho).

Lemma interpV_var : forall X rho a,
  interpV (t_typ_fvar X) rho a <->
  exists RR, binds X RR rho /\ (snd RR) a.
Proof.
  compute; intuition.
Qed.

Lemma interpV_bool : forall rho a,
  interpV t_typ_bool rho a <->
  a = (t_trm_true, t_trm_true) \/ a = (t_trm_false, t_trm_false).
Proof.
  compute; intuition.
Qed.

Lemma interpV_pair : forall t t' rho a,
  interpV (t_typ_pair t t') rho a <->
  exists v1 v1' v2 v2',
    a = (t_trm_pair v1 v1', t_trm_pair v2 v2') /\
    interpV t rho (v1, v2) /\ interpV t' rho (v1', v2').
Proof.
  split.
  intros. unfold interpV in H. unfold interpV_func in H.
  rewrite* WfExtensionality.fix_sub_eq_ext in H.
  intros. unfold interpV. unfold interpV_func.
  rewrite* WfExtensionality.fix_sub_eq_ext.
Qed.

Lemma interpV_arrow : forall t t' rho a,
  interpV (t_typ_arrow t t') rho a <->
  AtomVal (subst1_tt rho (t_typ_arrow t t')) (subst2_tt rho (t_typ_arrow t t')) a /\
  (forall t1 t2 R u1 u2,
    Rel t1 t2 R ->
    exists L, forall X, X \notin L ->
      interpV (open_tt_var t X) (rho & X ~ (t1, t2, R)) (u1, u2) ->
      interpE (open_tt_var t' X) (rho & X ~ (t1, t2, R))
              (t_trm_app (fst a) t1 u1, t_trm_app (snd a) t2 u2)).
Proof.
  split; intros.
  unfold interpV in H. unfold interpV_func in H.
  rewrite* WfExtensionality.fix_sub_eq_ext in H.
  unfold interpV. unfold interpV_func. rewrite* WfExtensionality.fix_sub_eq_ext.
Qed.

(* G relation and logical equivalence *)

Definition interpG (G : env_term) (rho : relat_env) g1 g2 : Prop :=
  relenv3 (t_wft (map (fun _ => star) rho)) G
          (fun u => t_value u) g1
          (fun u => t_value u) g2
          (fun t u1 u2 => interpV t rho (u1, u2)).

Definition log_approx (D : env_type) (G : env_term) (m1 m2 : trm) (t : typ) :=
  t_typing D G m1 t /\ t_typing D G m2 t /\
  forall rho g1 g2, interpD D rho -> interpG G rho g1 g2 ->
    interpE t rho
          (subst1_te rho (t_subst_ee g1 m1), subst2_te rho (t_subst_ee g2 m2)).

Definition log_equiv (D : env_type) (G : env_term) (m1 m2 : trm) (t : typ) :=
  log_approx D G m1 m2 t /\ log_approx D G m2 m1 t.

(* notations *)

Notation "D[[ D ]]" := (interpD D) (at level 0).
Notation "rho \in D[[ D ]]" := (interpD D rho) (at level 0).
Notation "G[[ G ]] rho" := (interpG G rho) (at level 0).
Notation "( g1 , g2 ) \in G[[ G ]] rho" := (interpG G rho g1 g2) (at level 0).
Notation "V[[ t ]] rho" := (interpV t rho) (at level 0).
Notation "a \in V[[ t ]] rho" := (interpV t rho a) (at level 0).
Notation "E[[ t ]] rho" := (interpE t rho) (at level 0).
Notation "a \in E[[ t ]] rho" := (interpE t rho a) (at level 0).

(* basic properties *)

Lemma interpV_AtomVal : forall D t rho a,
  t_wft D t -> rho \in D[[ D ]] -> a \in V[[ t ]]rho ->
  AtomVal (subst1_tt rho t) (subst2_tt rho t) a.
Proof.
  intros. gen rho a.
  induction H; intros; unfold subst1_tt; unfold subst2_tt; simpl.

  rewrite interpV_var in H2. destruct H2 as [RR]. destruct H2.
  destruct RR as [[t1 t2] R].
  assert (Rel t1 t2 R).
    apply relenv_wfenv_2 in H1.
    apply wfenv_binds with (x := X) (v := (t1, t2, R)) in H1; auto.
  repeat rewrite get_map with (v := (t1, t2)). simpl in *. apply* H4.
  rewrite get_map with (v := (t1, t2, R)); auto.
  rewrite get_map with (v := (t1, t2, R)); auto.

  rewrite interpV_bool in H1. destruct H1; subst; split; simpl;
    try apply* t_value_typing_true; try apply* t_value_typing_false; apply wfenv_empty.

  rewrite interpV_pair in H2.
  destruct H2 as [v1]. destruct H2 as [v1']. destruct H2 as [v2]. destruct H2 as [v2'].
  intuition. subst.
  destruct (IHt_wft1 rho H1 (v1, v2) H2). destruct (IHt_wft2 rho H1 (v1', v2') H5).
  split; simpl; apply* t_value_typing_pair.

  rewrite interpV_arrow in H4. destruct* H4.
Qed.

Lemma interpE_weaken_generalized : forall D D' t rho rho' X RR,
  t_wft (D & D') t -> rho \in D[[ D ]] -> rho' \in D[[ D' ]] ->
  X \notin dom (D & D') ->
  (forall a, a \in V[[ t ]](rho & rho') <-> a \in V[[ t ]](rho & X ~ RR & rho')) ->
  forall a,  a \in E[[ t ]](rho & rho') <-> a \in E[[ t ]](rho & X ~ RR & rho').
Proof.
  unfold interpE. intros. unfold subst1_tt. unfold subst2_tt.
  repeat rewrite map_concat. repeat rewrite map_single. repeat rewrite subst_tt_weaken;
  try (intro; apply (t_wft_fv_tt t (D & D')) in H4; auto).
  unfold termrel. split; split; intuition;
  destruct (H6 v1 H4) as [v2]; exists v2; intuition. rewrite* <- H3. rewrite* H3.
Qed.

Lemma interpV_weaken_generalized : forall D D' t rho rho' X t1 t2 R a,
  t_wft (D & D') t -> (rho & rho') \in D[[ D & D' ]] -> dom rho = dom D -> dom rho' = dom D' ->
  Rel t1 t2 R -> X # D -> X # D' ->
  (a \in V[[ t ]](rho & rho') <-> a \in V[[ t ]](rho & X ~ (t1, t2, R) & rho')).
Proof.
  intros. remember (D & D') as D0. gen D D' rho rho' X t1 t2 R a.
  induction H; split; intros; subst.
  (* var *)
  rewrite interpV_var. rewrite interpV_var in H7. destruct H7 as [RR]. exists RR. intuition.
    apply* binds_weaken.
      gen D'. induction rho' using env_ind; intros.
        rewrite dom_empty in H3. symmetry in H3. apply dom_empty_empty in H3. subst.
        repeat rewrite concat_empty_r in *. apply interpD_ok in H2. intuition.
        apply ok_push; auto. assert (X0 \notin (dom rho)); auto. rewrite* H1.
      rewrite concat_assoc. apply ok_push.
      (* want to apply IHrho' here but stuck *) skip.
      repeat rewrite dom_concat. repeat rewrite notin_union.
      rewrite concat_assoc in H2. apply interpD_ok in H2. intuition.
      apply ok_push_inv in H11. intuition. rewrite dom_single. rewrite notin_singleton.
      (* need to break down D' here too *) skip.
      apply ok_push_inv in H11. intuition.

(*      induction D' using env_ind; intros.
      rewrite dom_empty in H3. apply dom_empty_empty in H3. subst.
        repeat rewrite concat_empty_r in *. apply ok_push.
        apply interpD_ok in H2. intuition. assert (X0 \notin (dom rho)); auto. rewrite* H1.
      gen D'. induction rho' using env_ind; intros.
      try rewrite concat_empty_r in *. apply ok_push. apply interpD_ok in H2. intuition.
        assert (X0 \notin (dom rho)); auto. rewrite* H1.
        rewrite concat_empty_r in H2. apply interpD
        apply relenv_wfenv_2 in H2. apply wfenv_ok in H2. auto.
        assert (X0 \notin (dom rho)). rewrite* H1. exact H10.
      rewrite concat_assoc. apply ok_push.

          
        apply IHrho' with (D' := D' & x ~ star). *)
      
  rewrite interpV_var. rewrite interpV_var in H5. destruct H5 as [RR]. exists RR. intuition.
    apply binds_middle_inv in H6. intuition.
    subst. false. apply ok_middle_inv in H4.
    apply interpD_ok in H1. apply interpD_ok in H2. intuition.
    eapply binds_fresh_inv. exact H0. rewrite dom_concat. rewrite notin_union.
    rewrite H6. rewrite H1. auto.

  (* bool *)
  rewrite interpV_bool. rewrite interpV_bool in H4. intuition.
  rewrite interpV_bool. rewrite interpV_bool in H4. intuition.

  (* pair *)
  rewrite interpV_pair. rewrite interpV_pair in H5.
    destruct H5 as [v1]. destruct H5 as [v1']. destruct H5 as [v2]. destruct H5 as [v2'].
    exists v1 v1' v2 v2'. intuition.
    rewrite* <- (IHt_wft1 D0 D'). rewrite* <- (IHt_wft2 D0 D').
  rewrite interpV_pair. rewrite interpV_pair in H5.
    destruct H5 as [v1]. destruct H5 as [v1']. destruct H5 as [v2]. destruct H5 as [v2'].
    exists v1 v1' v2 v2'. intuition.
    rewrite* (IHt_wft1 D0 D'). rewrite* (IHt_wft2 D0 D').

  (* arrow *)
  rewrite interpV_arrow. split. skip.
(* prove atom
    rewrite interpV_arrow in H7. destruct H7. unfold subst1_tt in *. unfold subst2_tt in *.
    repeat rewrite map_concat in *. repeat rewrite map_single in *.
    repeat rewrite subst_tt_weaken; intuition.*)
  rewrite interpV_arrow in H7. destruct H7.
  intros. destruct (H8 t4 t5 R0 u1 u2 H9) as [L'].
  exists (L \u L' \u dom (rho & X ~ (t0, t3, R) & rho')). intros.
  rewrite <- concat_assoc.
  rewrite <- (interpE_weaken_generalized D0 (D' & X0 ~ star)).
  (* the interesting premise *)
  rewrite concat_assoc. apply* H10.
  rewrite <- concat_assoc.
  rewrite H0 with (D := D0) (D'0 := D' & X0 ~ star); auto using concat_assoc.
  rewrite concat_assoc. apply H12.
    (* "easy" premises of IH for t1 *)
    apply relenv_push; auto. skip. (* TODO fix freshness premise *)
    auto.
    rewrite concat_assoc. apply* ok_push.
  (* the "easy" premises of interpE_weaken_generalized / IH for t2*)
  rewrite concat_assoc. apply* H1.
  auto.
  apply relenv_push; auto. skip. (* TODO fix freshness premise *)
  skip. (* TODO make freshness premises of interpE_weaken less annoying*)
  apply H2 with (D := D0) (D'0 := D' & X0 ~ star); auto. rewrite* concat_assoc.
  apply relenv_push; auto. skip. (* TODO fix freshness premise *)
  rewrite concat_assoc. apply* ok_push.


  rewrite interpV_arrow. rewrite interpV_arrow in H7.
    split; unfold subst1_tt in *; unfold subst2_tt in *.
    repeat rewrite* map_concat in H7. skip.



Lemma interpV_Rel : forall D t rho,
  t_wft D t -> rho \in D[[ D ]] ->
  Rel (subst1_tt rho t) (subst2_tt rho t) (V[[ t ]]rho).
Proof.
  induction 1; intros.
  (* var *)
  unfold subst1_tt in *; unfold subst2_tt in *; simpl in *.
  unfold interpD in H1. apply H1 in H0.
  destruct H0 as [t1]. destruct H0 as [t2]. destruct H0 as [R]. destruct H0.
  rewrite binds_map with (v := (t1, t2)). simpl.
  rewrite binds_map with (v := (t1, t2)). simpl.
  unfold Rel in *. intros. apply H2. apply interpV_var in H3. destruct H3.
  replace x with (t1, t2, R) in H3. intuition. destruct H3. unfold binds in *.
  (* why doesn't "rewrite H0 in H3" work? *)
  assert (Some (t1, t2, R) = Some x). rewrite <- H0. rewrite <- H3. reflexivity.
  inverts* H5.
  apply binds_map with (v := (t1, t2, R)). auto.
  apply binds_map with (v := (t1, t2, R)). auto.

  (* bool *)
  unfold subst1_tt in *; unfold subst2_tt in *; simpl in *.
  unfold Rel. intros. apply interpV_bool in H1. unfold AtomVal.
  intuition; subst; simpl;
    auto using t_value_typing_true, t_value_typing_false, ok_empty, wfenv_empty.

  (* pair *)
  unfold subst1_tt in *; unfold subst2_tt in *; simpl in *.
  unfold Rel in *. intros. apply interpV_pair in H2.
  destruct H2 as [v1]. destruct H2 as [v1']. destruct H2 as [v2]. destruct H2 as [v2'].
  intuition. subst. unfold AtomVal in *. destruct (H4 (v1, v2) H2). destruct (H6 (v1', v2') H5).
  split; apply* t_value_typing_pair.

  (* arrow *)
  unfold Rel in *. intros. apply interpV_arrow in H4. intuition.
Qed.

Lemma interpV_substitution : forall D X t t' rho a,
  t_wft (D & X ~ star) t -> t_wft D t' -> rho \in D[[ D ]] ->
  (a \in V[[ subst_tt (X ~ t') t ]]rho <->
   a \in V[[ t ]](rho & (X ~ (subst1_tt rho t', subst2_tt rho t', V[[ t' ]] rho)))).
Proof.
  induction 1; split; intros; simpl in *.

  (* var *)
  case_eq (get X0 (X ~ t')); intros.
  apply binds_single_inv in H4. destruct H4. subst. rewrite get_single in H3. case_if.
    apply interpV_var; exists (subst1_tt rho t', subst2_tt rho t', V[[t']](rho)). auto.
  rewrite H4 in H3. apply interpV_var in H3. destruct H3. apply interpV_var.
    exists x. intuition. apply* binds_push_neq. intro. rewrite get_single in H4. case_if*.

  case_eq (get X0 (X ~ t')); intros.
  apply binds_single_inv in H4. destruct H4. subst.
    apply interpV_var in H3. destruct H3. destruct H3. apply binds_push_eq_inv in H3.
    subst. simpl in *. auto.
clear H0
  

  
