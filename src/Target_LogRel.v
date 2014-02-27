(**********************************************************************
 * Prototype of logical relations, just using target language for now *
 **********************************************************************)

Require Import Program Program.Wf.
Require Import LibWfenv Target_Definitions Core_Infrastructure.

Definition atom : Type := prod trm trm.

Definition Atom (t1 t2 : typ) (a : atom) : Prop :=
  t_typing empty empty (fst a) t1 /\ t_typing empty empty (snd a) t2.

Definition AtomVal (t1 t2 : typ) (a : atom) : Prop :=
  t_value_typing empty empty (fst a) t1 /\
  t_value_typing empty empty (snd a) t2.

Definition Rel (t1 t2 : typ) (R : atom -> Prop) : Prop :=
  (forall a, R a -> (AtomVal t1 t2 a)) /\
  (forall u1 u2 u2', R (u1, u2) ->
    ciu_approx empty empty u2 u2' t2 -> R (u1, u2')).

Definition somerel := prod (prod typ typ) (atom -> Prop).

Definition relat_env := env somerel.
Definition subst1_tt (rho : relat_env) := subst_tt (map fst (map fst rho)).
Definition subst2_tt (rho : relat_env) := subst_tt (map snd (map fst rho)).
Definition subst1_te (rho : relat_env) := subst_te (map fst (map fst rho)).
Definition subst2_te (rho : relat_env) := subst_te (map snd (map fst rho)).

Definition interpD (D : env_type) (rho : relat_env) : Prop :=
  forall X, binds X star D ->
    exists t1 t2 R, binds X (t1, t2, R) rho /\ Rel t1 t2 R.

(* V and E relations *)

Definition termrel (t1 t2 : typ) (V : atom -> Prop) (a : atom) : Prop :=
  Atom t1 t2 a /\
  forall v1, t_eval (fst a) v1 -> exists v2, t_eval (snd a) v2 /\ V (v1, v2).

Program Fixpoint interpV (t : typ) (rho : relat_env) (a : atom)
  {measure (typ_size t)} : Prop :=
  interpD D rho /\ t_Wft D t /\
  match t with
    | t_typ_fvar X => exists RR, binds X RR rho /\ (snd RR) a
    | t_typ_bool => a = (t_trm_true, t_trm_true) \/
                    a = (t_trm_false, t_trm_false)
    | t_typ_pair t t' => exists v1 v1' v2 v2',
        a = (t_trm_pair v1 v1', t_trm_pair v2 v2') /\
        interpV t rho (v1, v2) /\ interpV t' rho (v1', v2')
    | t_typ_arrow t' t'' =>
        Atom (subst1_tt rho t) (subst2_tt rho t) a /\
        forall t1 t2 R u1 u2 X,
          Rel t1 t2 R ->
          interpV (open_tt_var t' X) (rho & X ~ (t1, t2, R))
          (u1, u2) ->
          termrel (subst1_tt (rho & X ~ (t1, t2, R)) (open_tt_var t'' X))
                  (subst2_tt (rho & X ~ (t1, t2, R)) (open_tt_var t'' X))
                  (fun a =>
                    interpV (open_tt_var t' X) (rho & X ~ (t1, t2, R)) a)
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

(* why can't I prove this *)
Lemma interpV_pair : forall t t' rho a,
  interpV (t_typ_pair t t') rho a ->
  exists v1 v1' v2 v2',
    a = (t_trm_pair v1 v1', t_trm_pair v2 v2') /\
    interpV t rho (v1, v2) /\ interpV t' rho (v1', v2').
Proof.
  intros. 
  destruct H as [v1 H]. destruct H as [v1' H].
  destruct H as [v2 H]. destruct H as [v2' H].
  exists v1 v1' v2 v2'. intuition.
  (* H should be exactly what we need but uh *)
  (* H2 should be exactly what we need but uh *)

(* G relation and logical equivalence *)

Definition interpG (G : env_term) (rho : relat_env) g1 g2 : Prop :=
  wfenv (t_wft (map (fun _ => star) rho)) G /\
  forall x t, binds x t G -> exists u1 u2,
    binds x u1 g1 /\ binds x u2 g2 /\ interpV t rho (u1, u2).

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


(* this is a mess; need to get the definition working right first *)
Lemma interpV_equivalence_respecting : forall D rho t u1 u2 u2',
 t_wft D t -> rho \in D[[ D ]] ->
 (u1, u2) \in V[[ t ]] rho ->
 ciu_approx empty empty u2 u2' (subst2_tt rho t) -> t_value u2' ->
 (u1, u2') \in V[[ t ]] rho.
Proof.
  induction 1; intros.
  (* type variable case: uses inherited property from rho(X) *)
  compute. compute in H2.
    unfold interpD in H1. apply (H1 X) in H0.
    destruct H0 as [t1]. destruct H0 as [t2]. destruct H0 as [R]. destruct H0.
    exists (t1, t2, R). split*.
    destruct H2 as [RR]. destruct H2.
    assert (RR = (t1, t2, R)). erewrite binds_get in H2.
      inversion H2. reflexivity. auto. subst.
    unfold Rel in H5. destruct H5. apply* H7.
    unfold subst2_tt in H3. simpl in *.
    erewrite get_map in H3; try (erewrite get_map; auto; exact H2). auto.
  (* bool case: is a mess, needs to be split into some lemmas *)
  compute. compute in H1. unfold subst2_tt in *. simpl in *.
    assert (u2 = u2'); subst; auto.
    destruct H1; inverts H1;
    unfold ciu_approx in *; simpl in *;
    destruct H2; destruct H2.
    assert (t_eval u2' t_trm_true).
      replace u2'
        with (plug t_ctx_hole (subst_te empty (t_subst_ee empty u2'))); auto.
      apply* H4. rewrite <- concat_empty_r with (A := typ) at 2.
                 rewrite <- concat_empty_r at 2.
      apply* t_context_typing_hole.
      apply wfenv_empty.
      rewrite concat_empty_r with (A := typ). apply wfenv_empty.
      rewrite concat_empty_r. apply ok_empty.
      unfold relenv. split. repeat rewrite* dom_empty.
      intros. apply binds_empty_inv in H7. contradiction.
      unfold relenv. split. repeat rewrite* dom_empty.
      intros. apply binds_empty_inv in H7. contradiction.
      apply* t_eval_red. apply* t_red_refl.
      simpl. (* TODO: subst_te_empty *) skip.
    inverts H5. inverts* H6. false. inverts H5.
    induction H9; inverts H6; simpl in H3; inverts H3.
    assert (t_eval u2' t_trm_false).
      replace u2'
        with (plug t_ctx_hole (subst_te empty (t_subst_ee empty u2'))); auto.
      apply* H4. rewrite <- concat_empty_r with (A := typ) at 2.
                 rewrite <- concat_empty_r at 2.
      apply* t_context_typing_hole.
      apply wfenv_empty.
      rewrite concat_empty_r with (A := typ). apply wfenv_empty.
      rewrite concat_empty_r. apply ok_empty.
      unfold relenv. split. repeat rewrite* dom_empty.
      intros. apply binds_empty_inv in H7. contradiction.
      unfold relenv. split. repeat rewrite* dom_empty.
      intros. apply binds_empty_inv in H7. contradiction.
      apply* t_eval_red. apply* t_red_refl.
      simpl. (* TODO: subst_te_empty *) skip.
    inverts H5. inverts* H6. false. inverts H5.
    induction H9; inverts H6; simpl in H3; inverts H3.
  (* pair case: just induction *)
(* don't use compute *)
  (* arrow case *)
