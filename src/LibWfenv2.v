(*****************************************************************************
 * Extension to TLC's LibEnv.ok to allow checking stronger properties of env *
 * William J. Bowman, Phillip Mates & James T. Perconti                      *
 *****************************************************************************)

(* in this file: wfenv, relenv, relenv3, and related lemmas *)

Require Export LibEnv.

(* Lemmas that LibEnv should really have provided *)

Lemma get_map : forall A B x (v : A) (f : A -> B) (E : env A),
  get x E = Some v -> get x (map f E) = Some (f v).
Proof. intros. apply binds_get. apply binds_map. auto. Qed.

Lemma dom_empty_empty : forall {A : Type} (E : env A),
  dom E = \{} -> E = empty.
Proof.
  induction E using env_ind. auto.
  intros.
  assert (x \in \{}). rewrite <- H.
  rewrite dom_push. rewrite in_union. left. rewrite in_singleton. auto.
  apply in_empty_elim in H0. contradiction.
Qed.

(* LibEnv provides the predicate 'ok', which checks basic well-formedness
 * of an env: namely, that there are no duplicate keys
 *
 * wfenv makes sure an env is ok and that all its values satisfy property P *)
Inductive wfenv {A : Type} : (A -> Prop) -> (env A) -> Prop :=
| wfenv_empty : forall (P : A -> Prop), wfenv P empty
| wfenv_push : forall (P : A -> Prop) (E : env A) (x : var) (v : A),
    wfenv P E -> x # E -> P v -> wfenv P (E & x ~ v).

Hint Constructors wfenv.

(* Properties of wfenv *)

Lemma wfenv_push_inv : forall {A : Type} (P : A -> Prop) (E : env A) x v,
  wfenv P (E & x ~ v) -> wfenv P E /\ x # E /\ P v.
Proof.
  intros. inversion H. apply empty_push_inv in H2. contradiction.
  apply eq_push_inv in H0. intuition; subst; auto.
Qed.  

Lemma wfenv_push_inv_wfenv : forall {A : Type} (P : A -> Prop) (E : env A) x v,
  wfenv P (E & x ~ v) -> wfenv P E.
Proof.
  intros. apply wfenv_push_inv in H. intuition.
Qed.

Lemma wfenv_ok : forall {A : Type} (P : A -> Prop) (E : env A),
  wfenv P E -> ok E.
Proof.
  induction E using env_ind; intros.
  apply ok_empty.
  apply wfenv_push_inv in H. intuition.
Qed.

Lemma wfenv_binds : forall {A : Type} (P : A -> Prop) (E : env A) x v,
  wfenv P E -> binds x v E -> P v.
Proof.
  induction 1; intros.
  apply binds_empty_inv in H. contradiction.
  apply binds_push_inv in H2. intuition. subst. auto.
Qed.

Lemma wfenv_weaken : forall {A : Type} (P : A -> Prop) (E F : env A) x v,
  wfenv P (E & F) -> x # (E & F) -> P v -> wfenv P (E & x ~ v & F).
Proof.
  intros. remember (E & F) as E'.
  generalize dependent F. generalize dependent E.
  induction H; intros.
  apply empty_concat_inv in HeqE'. intuition. subst.
    rewrite concat_empty_r. auto.
  induction F using env_ind.
  try rewrite concat_empty_r in *. subst. auto.
  try rewrite concat_assoc in *.
  apply eq_push_inv in HeqE'. intuition. subst. auto.
Qed.

Lemma wfenv_concat_inv : forall {A : Type} (P : A -> Prop) (E F : env A),
  wfenv P (E & F) -> wfenv P E /\ wfenv P F.
Proof.
  intros. generalize dependent E.
  induction F using env_ind; intros.
  rewrite concat_empty_r in H. intuition. auto.
  rewrite concat_assoc in H. apply wfenv_push_inv in H.
  intuition; auto; apply IHF in H0; intuition.
Qed.

Lemma wfenv_concat_inv_l : forall {A : Type} (P : A -> Prop) (E F :env A),
  wfenv P (E & F) -> wfenv P E.
Proof.
  intros. apply wfenv_concat_inv in H. intuition.
Qed.

Lemma wfenv_concat_inv_r : forall {A : Type} (P : A -> Prop) (E F :env A),
  wfenv P (E & F) -> wfenv P F.
Proof.
  intros. apply wfenv_concat_inv in H. intuition.
Qed.

Lemma wfenv_exchange : forall {A : Type} (P : A -> Prop) (E : env A) (F : env A)
  (x : var) (y : var) (a : A) (b : A),
  wfenv P (E & x ~ a & y ~ b & F) -> wfenv P (E & y ~ b & x ~ a & F).
Proof.
  induction F using env_ind; intros. try rewrite concat_empty_r in *.
  apply wfenv_push_inv in H; intuition.
  apply wfenv_push_inv in H0; intuition.
  try rewrite concat_assoc in *.
  apply wfenv_push_inv in H. intuition.
Qed.

Lemma wfenv_implies : forall {A : Type} (P Q : A -> Prop) (E : env A),
  (forall v, P v -> Q v) -> wfenv P E -> wfenv Q E.
Proof.
  intros. induction H0; auto.
Qed.

Lemma ok_wfenv_trivial : forall {A : Type} (E : env A),
  ok E -> wfenv (fun _ => True) E.
Proof.
  induction 1; auto.
Qed.

Lemma wfenv_single : forall {A : Type} (P : A -> Prop) x v,
  P v -> wfenv P (x ~ v).
Proof.
  intros. rewrite <- concat_empty_l. auto.
Qed.

(* TODO: We might want more of the lemmas we have about ok for wfenv.
 *       The remaining ones are:
 *        ok_middle_change, ok_middle_inv, ok_middle_inv_l, ok_middle_inv_r,
 *        ok_remove, ok_map, ok_concat_map, ok_singles *)


(***** relenv *******)
(* check that two wfenvs have the same set of keys and that
 * the values for those keys are related according to R.
 * example: if G is the type environment and g is a substitution,
            we want the values in g to have the types in G, that is, we want
            relenv value g type G (typing empty) *)
Inductive relenv {A B : Type}
  : (A -> Prop) -> (env A) -> (B -> Prop) -> (env B) ->
    (A -> B -> Prop) -> Prop :=
| relenv_empty : forall P Q R, relenv P empty Q empty R
| relenv_push : forall P E Q F R x a b,
    relenv P E Q F R -> x # E -> P a -> Q b -> R a b ->
    relenv P (E & x ~ a) Q (F & x ~ b) R.

Hint Constructors relenv.

Lemma relenv_dom : forall {A B : Type}
  (P : A -> Prop) (E : env A) (Q : B -> Prop) (F : env B) (R : A -> B -> Prop),
  relenv P E Q F R -> dom E = dom F.
Proof.
  induction 1. repeat rewrite dom_empty. reflexivity.
  repeat rewrite dom_push. f_equal; auto.
Qed.

Lemma relenv_wfenv_1 : forall {A B : Type}
  (P : A -> Prop) (E : env A) (Q : B -> Prop) (F : env B) (R : A -> B -> Prop),
  relenv P E Q F R -> wfenv P E.
Proof.
  induction 1; auto.
Qed.

Lemma relenv_wfenv_2 : forall {A B : Type}
  (P : A -> Prop) (E : env A) (Q : B -> Prop) (F : env B) (R : A -> B -> Prop),
  relenv P E Q F R -> wfenv Q F.
Proof.
  intros. induction H; auto.
  assert (dom E = dom F). eapply relenv_dom. eauto.
  rewrite H4 in H0. auto.
Qed.

Lemma relenv_rel : forall {A B : Type}
  (P : A -> Prop) (E : env A) (Q : B -> Prop) (F : env B) (R : A -> B -> Prop),
  relenv P E Q F R -> forall x a b, binds x a E -> binds x b F -> R a b.
Proof.
  induction 1; intros.
  apply binds_empty_inv in H. contradiction.
  apply binds_push_inv in H4. apply binds_push_inv in H5.
  intuition. subst. auto.
  apply (IHrelenv x0); auto.
Qed.

Lemma relenv_push_inv : forall {A B : Type}
  (P : A -> Prop) (E : env A) (Q : B -> Prop) (F : env B) (R : A -> B -> Prop)
  x a b,
  relenv P (E & x ~ a) Q (F & x ~ b) R ->
  relenv P E Q F R /\ x # E /\ x # F /\ P a /\ Q b /\ R a b.
Proof.
  intros. inversion H. apply empty_push_inv in H2. contradiction.
  apply eq_push_inv in H0. apply eq_push_inv in H1. intuition; subst; auto.
  apply relenv_dom in H2. rewrite <- H2. auto.
Qed.

Lemma relenv_concat_dom : forall {A B : Type}
  (P : A -> Prop) (E E' : env A) (Q : B -> Prop) (F F' : env B)
  (R : A -> B -> Prop),
  relenv P (E & E') Q (F & F') R -> dom E = dom F -> dom E' = dom F'.
Proof.
  intros. remember (E & E') as EE. remember (F & F') as FF.
  generalize dependent E. generalize dependent F.
  generalize dependent E'. generalize dependent F'.
  induction H; intros.
  apply empty_concat_inv in HeqFF. apply empty_concat_inv in HeqEE.
    intuition. subst. repeat rewrite dom_empty. reflexivity.
  

Lemma relenv_concat_inv : forall {A B : Type}
  (P : A -> Prop) (E E' : env A) (Q : B -> Prop) (F F' : env B)
  (R : A -> B -> Prop),
  relenv P (E & E') Q (F & F') R -> dom E = dom F -> dom E' = dom F' ->
  relenv P E Q F R /\ relenv P E' Q F' R.
Proof.
  intros. remember (E & E') as EE. remember (F & F') as FF.
  generalize dependent E. generalize dependent F.
  generalize dependent E'. generalize dependent F'.
  induction H; intros.
  apply empty_concat_inv in HeqEE. apply empty_concat_inv in HeqFF.
  intuition; subst; auto.
  generalize dependent F'. induction E' using env_ind; intros.
  rewrite dom_empty in H4. symmetry in H4. apply dom_empty_empty in H4. subst.
  try rewrite concat_empty_r in *. subst. intuition.
  induction F' using env_ind; intros.
  rewrite dom_empty in H4. apply dom_empty_empty in H4.
  symmetry in H4. apply empty_push_inv in H4. contradiction.
  try rewrite concat_assoc in *.
  apply eq_push_inv in HeqEE. apply eq_push_inv in HeqFF.
  intuition; subst; subst. clear IHF'. clear IHE'.
  assert (relenv P E0 Q F0 R /\ relenv P E' Q F' R).
   apply IHrelenv; auto.
   (* if I had a notin_union_strengthen lemma or some such thing...
      A \u {x} = B \u {x} -> x \notin A -> x \notin B -> A = B *)

  
hi