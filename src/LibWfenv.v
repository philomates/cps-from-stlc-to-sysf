(*****************************************************************************
 * Extension to TLC's LibEnv.ok to allow checking stronger properties of env *
 * William J. Bowman, Phillip Mates & James T. Perconti                      *
 *****************************************************************************)

Require Export LibEnv.

Definition wfenv {A: Type} (P : A -> Prop) (E : env A) : Prop :=
  ok E /\ forall x v, binds x v E -> P v.

Definition relenv {A B : Type}
  (P : A -> Prop) (E : env A)
  (Q : B -> Prop) (F : env B) (R : A -> B -> Prop) : Prop :=
  dom E = dom F /\
  forall x a b, wfenv P E -> wfenv Q F -> binds x a E -> binds x b F -> R a b.

Lemma wfenv_ok : forall {A : Type} (P : A -> Prop) (E : env A),
  wfenv P E -> ok E.
Proof. unfold wfenv. intuition. Qed.

Lemma wfenv_binds : forall {A : Type} (P : A -> Prop) (E : env A) x v,
  wfenv P E -> binds x v E -> P v.
Proof. unfold wfenv. intuition. eauto. Qed.

Lemma relenv_dom : forall {A B : Type}
  (P : A -> Prop) (E : env A)
  (Q : B -> Prop) (F : env B) (R : A -> B -> Prop),
  relenv P E Q F R -> dom E = dom F.
Proof. unfold relenv. intuition. Qed.

Lemma relenv_rel : forall {A B : Type}
  (P : A -> Prop) (E : env A)
  (Q : B -> Prop) (F : env B) (R : A -> B -> Prop),
  relenv P E Q F R ->
  forall x a b, wfenv P E -> wfenv Q F -> binds x a E -> binds x b F -> R a b.
Proof. unfold relenv. intuition. Qed.

(* Here we reprove some lemmas from LibEnv about ok as lemmas about wfenv *)

Lemma wfenv_empty : forall {A : Type} (P : A -> Prop), wfenv P empty.
Proof.
  unfold wfenv. split.
  apply ok_empty.
  intros. apply binds_empty_inv in H. contradiction.
Qed.

Lemma wfenv_push : forall {A : Type} (P : A -> Prop) (E : env A) x v,
  wfenv P E -> x # E -> P v -> wfenv P (E & x ~ v).
Proof.
  unfold wfenv. split.
  apply ok_push; intuition.
  intros. destruct H. apply binds_push_inv in H2.
  intuition; subst; try apply (H3 x0); auto.
Qed.

Lemma wfenv_push_inv : forall {A : Type} (P : A -> Prop) (E : env A) x v,
  wfenv P (E & x ~ v) -> wfenv P E /\ x # E /\ P v.
Proof.
  unfold wfenv. intuition. apply (H1 x0).
  apply binds_push_neq; auto. intro contra. subst.
  apply binds_fresh_inv in H. auto. apply ok_push_inv in H0. intuition.
  apply ok_push_inv in H0. intuition.
  apply (H1 x). apply binds_push_eq.
Qed.

Lemma wfenv_push_inv_wfenv : forall {A : Type} (P : A -> Prop) (E : env A) x v,
  wfenv P (E & x ~ v) -> wfenv P E.
Proof.
  intros. remember (wfenv_push_inv P E x v H) as H'. destruct H'. auto.
Qed.

Lemma wfenv_concat_inv : forall {A : Type} (P : A -> Prop) (E F : env A),
  wfenv P (E & F) -> wfenv P E /\ wfenv P F.
Proof.
  intros. generalize dependent F.
  apply (env_ind (fun F => wfenv P (E & F) -> wfenv P E /\ wfenv P F)).
  rewrite concat_empty_r. intuition. apply wfenv_empty.
  intros. rewrite concat_assoc in H0. apply wfenv_push_inv in H0.
  destruct H0. apply H in H0. split; intuition.
  apply wfenv_push; auto.
Qed.

Lemma wfenv_concat_inv_l :  forall {A : Type} (P : A -> Prop) (E F : env A),
  wfenv P (E & F) -> wfenv P E.
Proof.
  intros. remember (wfenv_concat_inv P E F H) as H'. destruct H'. auto.
Qed.

Lemma wfenv_concat_inv_r :  forall {A : Type} (P : A -> Prop) (E F : env A),
  wfenv P (E & F) -> wfenv P F.
Proof.
  intros. remember (wfenv_concat_inv P E F H) as H'. destruct H'. auto.
Qed.

Lemma wfenv_ind : forall {A : Type} (P : A -> Prop) (Q : env A -> Prop),
  Q empty ->
  (forall (E : env A) (x : var) (v : A),
    wfenv P E -> Q E -> x # E -> P v -> Q (E & x ~ v)) ->
  forall (E : env A), wfenv P E -> Q E.
Proof.
  intros A P Q H H' E. apply (env_ind (fun E => wfenv P E -> Q E)); auto.
  intros. apply wfenv_push_inv in H1. intuition.
Qed.

(* TODO: We might want more of the lemmas we have about ok for wfenv.
 *       The remaining ones are:
 *        ok_middle_change, ok_middle_inv, ok_middle_inv_l, ok_middle_inv_r,
 *        ok_remove, ok_map, ok_concat_map, ok_singles *)

(* additional lemmas specific to wfenv *)
(* TODO: what else is useful here? *)

Lemma wfenv_implies : forall {A : Type} (P Q : A -> Prop) (E : env A),
  (forall v, P v -> Q v) -> wfenv P E -> wfenv Q E.
Proof.
  intros. apply (wfenv_ind P (fun E => wfenv P E -> wfenv Q E));
  auto using wfenv_empty.
  intros. apply wfenv_push_inv in H5. apply wfenv_push; auto.
Qed.

(* TODO: lemmas about relenv *)
