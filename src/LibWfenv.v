(*****************************************************************************
 * Extension to TLC's LibEnv.ok to allow checking stronger properties of env *
 * William J. Bowman, Phillip Mates & James T. Perconti                      *
 *****************************************************************************)

Require Export LibEnv.

(* Lemma that LibEnv should really have provided *)

Lemma get_map : forall A B x (v : A) (f : A -> B) (E : env A),
  get x E = Some v -> get x (map f E) = Some (f v).
Proof. intros. apply binds_get. apply binds_map. auto. Qed.

(* LibEnv provides the predicate 'ok', which
 * checks basic well-formedness of an env:
 * namely, that there are no duplicate keys *)

(* wfenv makes sure an env is ok and that all its values satisfy property P *)
Definition wfenv {A: Type} (P : A -> Prop) (E : env A) : Prop :=
  ok E /\ forall x v, binds x v E -> P v.

Lemma wfenv_ok : forall {A : Type} (P : A -> Prop) (E : env A),
  wfenv P E -> ok E.
Proof. unfold wfenv. intuition. Qed.

Lemma wfenv_binds : forall {A : Type} (P : A -> Prop) (E : env A) x v,
  wfenv P E -> binds x v E -> P v.
Proof. unfold wfenv. intuition. eauto. Qed.

(* check that two wfenvs have the same set of keys and that
 * the values for those keys are related according to R.
 * example: if G is the type environment and g is a substitution,
            we want the values in g to have the types in G, that is, we want
            relenv value g type G (typing empty) *)
Definition relenv {A B : Type}
  (P : A -> Prop) (E : env A)
  (Q : B -> Prop) (F : env B) (R : A -> B -> Prop) : Prop :=
  dom E = dom F /\ wfenv P E /\ wfenv Q F /\
  forall x a b, binds x a E -> binds x b F -> R a b.

Lemma relenv_dom : forall {A B : Type}
  (P : A -> Prop) (E : env A)
  (Q : B -> Prop) (F : env B) (R : A -> B -> Prop),
  relenv P E Q F R -> dom E = dom F.
Proof. unfold relenv. intuition. Qed.

Lemma relenv_wfenv_1 : forall {A B : Type}
  (P : A -> Prop) (E : env A)
  (Q : B -> Prop) (F : env B) (R : A -> B -> Prop),
  relenv P E Q F R -> wfenv P E.
Proof. unfold relenv. intuition. Qed.

Lemma relenv_wfenv_2 : forall {A B : Type}
  (P : A -> Prop) (E : env A)
  (Q : B -> Prop) (F : env B) (R : A -> B -> Prop),
  relenv P E Q F R -> wfenv Q F.
Proof. unfold relenv. intuition. Qed.

Lemma relenv_rel : forall {A B : Type}
  (P : A -> Prop) (E : env A)
  (Q : B -> Prop) (F : env B) (R : A -> B -> Prop),
  relenv P E Q F R ->
  forall x a b, binds x a E -> binds x b F -> R a b.
Proof. unfold relenv. intuition. Qed.

(* check that three wfenvs have the same set of keys and that
 * the values for those keys are related according to R. *)
Definition relenv3 {A B C : Type}
  (P : A -> Prop) (E : env A)
  (Q : B -> Prop) (F : env B)
  (R : C -> Prop) (G : env C)
  (S : A -> B -> C -> Prop) : Prop :=
  dom E = dom F /\ dom F = dom G /\ wfenv P E /\ wfenv Q F /\ wfenv R G /\
  forall x a b c, binds x a E -> binds x b F -> binds x c G -> S a b c.

Lemma relenv3_dom_1_2 : forall {A B C : Type}
  (P : A -> Prop) (E : env A)
  (Q : B -> Prop) (F : env B)
  (R : C -> Prop) (G : env C)
  (S : A -> B -> C -> Prop),
  relenv3 P E Q F R G S -> dom E = dom F.
Proof. unfold relenv3. intuition. Qed.

Lemma relenv3_dom_2_3 : forall {A B C : Type}
  (P : A -> Prop) (E : env A)
  (Q : B -> Prop) (F : env B)
  (R : C -> Prop) (G : env C)
  (S : A -> B -> C -> Prop),
  relenv3 P E Q F R G S -> dom F = dom G.
Proof. unfold relenv3. intuition. Qed.

Lemma relenv3_dom_1_3 : forall {A B C : Type}
  (P : A -> Prop) (E : env A)
  (Q : B -> Prop) (F : env B)
  (R : C -> Prop) (G : env C)
  (S : A -> B -> C -> Prop),
  relenv3 P E Q F R G S -> dom E = dom F.
Proof. unfold relenv3. intuition. Qed.

Lemma relenv3_wfenv_1 : forall {A B C : Type}
  (P : A -> Prop) (E : env A)
  (Q : B -> Prop) (F : env B)
  (R : C -> Prop) (G : env C)
  (S : A -> B -> C -> Prop),
  relenv3 P E Q F R G S -> wfenv P E.
Proof. unfold relenv3. intuition. Qed.

Lemma relenv3_wfenv_2 : forall {A B C : Type}
  (P : A -> Prop) (E : env A)
  (Q : B -> Prop) (F : env B)
  (R : C -> Prop) (G : env C)
  (S : A -> B -> C -> Prop),
  relenv3 P E Q F R G S -> wfenv Q F.
Proof. unfold relenv3. intuition. Qed.

Lemma relenv3_wfenv_3 : forall {A B C : Type}
  (P : A -> Prop) (E : env A)
  (Q : B -> Prop) (F : env B)
  (R : C -> Prop) (G : env C)
  (S : A -> B -> C -> Prop),
  relenv3 P E Q F R G S -> wfenv R G.
Proof. unfold relenv3. intuition. Qed.

Lemma relenv3_rel : forall {A B C : Type}
  (P : A -> Prop) (E : env A)
  (Q : B -> Prop) (F : env B)
  (R : C -> Prop) (G : env C)
  (S : A -> B -> C -> Prop),
  relenv3 P E Q F R G S ->
  forall x a b c, binds x a E -> binds x b F -> binds x c G -> S a b c.
Proof. unfold relenv3. intuition. Qed.

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

Hint Resolve wfenv_push_inv_wfenv.

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

Lemma wfenv_exchange : forall {A : Type} (P : A -> Prop) (E : env A) (F : env A)
  (x : var) (y : var) (a : A) (b : A),
  wfenv P (E & x ~ a & y ~ b & F) -> wfenv P (E & y ~ b & x ~ a & F).
Proof.
  induction F using env_ind; intros. try rewrite concat_empty_r in *.
  apply wfenv_push_inv in H. apply wfenv_push; intuition;
  apply wfenv_push_inv in H0; try apply wfenv_push; intuition.
  try rewrite concat_assoc in *. apply wfenv_push_inv in H. apply wfenv_push. intuition.
  intuition. intuition.
Qed.

(* TODO: what else is useful here? *)

Lemma wfenv_implies : forall {A : Type} (P Q : A -> Prop) (E : env A),
  (forall v, P v -> Q v) -> wfenv P E -> wfenv Q E.
Proof.
  intros. apply (wfenv_ind P (fun E => wfenv P E -> wfenv Q E));
  auto using wfenv_empty.
  intros. apply wfenv_push_inv in H5. apply wfenv_push; auto.
Qed.

Lemma ok_wfenv_trivial : forall {A : Type} (E : env A),
  ok E -> wfenv (fun _ => True) E.
Proof.
  induction 1; auto using wfenv_empty, wfenv_push.
Qed.

Lemma wfenv_single : forall {A : Type} (P : A -> Prop) X (v : A),
  P v -> wfenv P (X ~ v).
Proof.
  intros. rewrite <- concat_empty_l. apply wfenv_push; auto. apply wfenv_empty.
Qed.

(* TODO: lemmas about relenv *)

Lemma relenv_empty : forall {A B : Type} (P : A -> Prop) (Q : B -> Prop) (R : A -> B -> Prop),
  relenv P empty Q empty R .
Proof.
  unfold relenv. intuition; auto using wfenv_empty.
  repeat rewrite dom_empty. reflexivity.
  apply binds_empty_inv in H. contradiction.
Qed.

Lemma relenv_push : forall {A B : Type}
  (P : A -> Prop) (E : env A) (Q : B -> Prop) (F : env B) (R : A -> B -> Prop)
  (x : var) (a : A) (b : B),
  relenv P E Q F R -> x # E -> P a -> Q b -> R a b ->
  relenv P (E & x ~ a) Q (F & x ~ b) R.
Proof.
  unfold relenv. intuition.
  repeat rewrite dom_concat. repeat rewrite dom_single. rewrite H4. reflexivity.
  apply wfenv_push; auto.
  apply wfenv_push; auto. rewrite <- H4. auto.
  apply binds_push_inv in H6. apply binds_push_inv in H8. intuition.
    subst. auto. apply (H7 x0); auto.
Qed.

Lemma relenv_concat_inv : forall {A B : Type}
  (P : A -> Prop) (E E' : env A) (Q : B -> Prop) (F F' : env B) (R : A -> B -> Prop),
  relenv P (E & E') Q (F & F') R -> dom E = dom F -> dom E' = dom F' ->
  relenv P E Q F R /\ relenv P E' Q F' R.
Proof.
  unfold relenv. intros. intuition;
  try solve [apply wfenv_concat_inv in H; apply wfenv_concat_inv in H3; intuition].
  apply (H5 x); apply binds_concat_left_ok; eauto using wfenv_ok.
  apply (H5 x); apply binds_concat_right; auto.
Qed.

Lemma dom_empty_empty : forall {A : Type} (E : env A),
  dom E = \{} -> E = empty.
Proof.
  induction E using env_ind. auto.
  intros.
  assert (x \in \{}). rewrite <- H.
  rewrite dom_push. rewrite in_union. left. rewrite in_singleton. auto.
  apply in_empty_elim in H0. contradiction.
Qed.

Lemma relenv_empty_empty_1 : forall {A B : Type}
  (P : A -> Prop) (E : env A) (Q : B -> Prop) (R : A -> B -> Prop),
  relenv P E Q empty R -> E = empty.
Proof.
  unfold relenv. intuition. apply dom_empty_empty. rewrite dom_empty in H0. exact H0.
Qed.

Lemma relenv_empty_empty_2 : forall {A B : Type}
  (P : A -> Prop) (Q : B -> Prop) (F : env B) (R : A -> B -> Prop),
  relenv P empty Q F R -> F = empty.
Proof. 
  unfold relenv. intuition. apply dom_empty_empty. rewrite dom_empty in H0. symmetry. exact H0.
Qed. 

Lemma relenv_exchange_1 : forall {A B : Type}
  (P : A -> Prop) (E : env A) (E' : env A) (Q : B -> Prop) (F : env B) (R : A -> B -> Prop)
  (x y : var) (a a' : A),
  relenv P (E & x ~ a & y ~ a' & E') Q F R -> relenv P (E & y ~ a' & x ~ a & E') Q F R.
Proof.
  unfold relenv. intuition. repeat rewrite dom_concat in *.
  rewrite <- union_assoc with (E := dom E) in *.
  rewrite union_comm with (E := dom (y ~ a')). exact H0.
  apply wfenv_exchange. auto.
  apply (H3 x0). apply binds_concat_inv in H2. intuition. apply binds_concat_left; auto.
  apply binds_push_inv in H6. intuition. subst. apply binds_middle_eq.
    apply wfenv_ok in H. apply ok_concat_inv in H; destruct H. apply ok_push_inv in H. intuition.
  apply binds_push_inv in H7. intuition. subst. apply binds_push_eq. exact H4.
Qed.

(* Lemma relenv_find : forall {A B : Type}
  (P : A -> Prop) (Q : B -> Prop) (R : A -> B -> Prop) (E : env A) (F : env B),
  (forall (x : var) (b : B),
    relenv P E Q (F & x ~ b) R -> exists E', exists a,
      binds x a E /\ P a /\ relenv P E' Q F R /\ R a b) /\
  (forall (x : var) (a : A),
    relenv P (E & x ~ a) Q F R -> exists F', exists b,
      binds x b F /\ Q b /\ relenv P E Q F' R /\ R a b).
Proof.
  intros. induction E using env_ind; induction F using env_ind; split; intros.
  unfold relenv in H. destruct H.
  assert (x \in \{}). rewrite dom_empty in H. rewrite H.
  apply get_some_inv with (v := b). apply binds_push_eq.
  apply in_empty_elim in H1. contradiction.

  unfold relenv in H. destruct H.
  assert (x \in \{}). rewrite dom_empty in H. rewrite <- H.
  apply get_some_inv with (v := a). apply binds_push_eq.
  apply in_empty_elim in H1. contradiction.

  unfold relenv in H. destruct H.
  assert (x \in \{}). rewrite dom_empty in H. rewrite H.
  rewrite dom_concat. rewrite in_union. left.
  apply get_some_inv with (v := v). apply binds_push_eq.
  apply in_empty_elim in H1. contradiction.

  rewrite concat_empty_l in H.
  unfold relenv in H. destruct H.
  assert (F = empty). rewrite dom_push in H. rewrite dom_single in H.
  assert (x0 = x). apply 

  destruct (IHE Q F R x0 b).
Qed. *)

(* 
Lemma relenv_ind : forall {A B : Type} (P : A -> Prop) (Q : B -> Prop) (R : A -> B -> Prop)
  (goal : env A -> env B -> Prop),
  goal empty empty ->
  (forall (E : env A) (F : env B) (x : var) (a : A) (b : B),
    relenv P E Q F R -> goal E F -> x # E -> P a -> Q b -> R a b ->
    goal (E & x ~ a) (F & x ~ b)) ->
  forall (E : env A) (F : env B), relenv P E Q F R -> goal E F.
Proof.
  intros.
  generalize dependent E.
  induction F using env_ind; intros. apply relenv_empty_empty_1 in H1. rewrite H1. auto.
  generalize dependent F.
  induction E using env_ind; intros. apply relenv_empty_empty_2 in H1. rewrite H1. auto.

  (* problem: how to get the same x on both sides!?
     might not be doable with this induction strategy *) *)
