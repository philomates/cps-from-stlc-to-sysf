(* Basic properties of target language *)

Require Import Target_Definitions Core_Infrastructure.

(* ********************************************************************** *)
(** * Properties of well-formedness of a type in an environment *)

(** If a type is well-formed in an environment then it is locally closed. *)
Lemma t_wft_implies_t_type : forall D t,
  t_wft D t -> t_type t.
Proof.
  intros.
  induction H; eauto.
Qed.
Hint Resolve t_wft_implies_t_type.

Lemma t_ok_implies_t_type : forall D G t x,
  t_ok D G -> binds x t G -> t_type t.
Proof.
  induction 1; intros.
  apply binds_empty_inv in H0; contradiction.
  apply binds_push_inv in H2.
  destruct H2; destruct H2; subst;
  eauto.
Qed.
  
Hint Resolve t_ok_implies_t_type.

Lemma t_typing_wft : forall D G m t,
  t_typing D G m t -> t_type t.
Proof.
  intros.
  induction H; eauto;
  try 
    (pick_fresh x;
      apply (@H1 x); auto).
  inversion IHt_typing1; subst.
 (* TODO *)
  apply subst_tt_intro.
  apply subst_tt_type.
  open_tt t1 t == (subst_tt X t (open_tt_var t1 X))
  unfolds open_tt_var.
  pick_fresh X. eapply H5.
Admitted.

Lemma t_wft_type : forall D t,
  t_wft D t -> type t.
Proof.
  (* induction 1; eauto. *)
(* Qed. *)
Admitted.

(** Through weakening *)

Lemma t_wft_weaken : forall G T E F,
  t_wft (E & G) T ->
  ok (E & F & G) ->
  t_wft (E & F & G) T.
Proof.
  (* intros. gen_eq K: (E & G). gen E F G. *)
  (* induction H; intros; subst; eauto. *)
  (* case: var *)
  (* apply wft_var. apply* binds_weaken. *)
  (* case: all *)
  (* apply_fresh* wft_arrow as Y. apply_ih_bind* H0. *)
  (* apply_ih_bind* H2. *)
Qed.
