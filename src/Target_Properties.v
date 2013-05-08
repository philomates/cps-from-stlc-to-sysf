(***************************************************************************
* Basic properties of target language                                      *
* William J. Bowman, Phillip Mates & James T. Perconti                     *
***************************************************************************)

Require Import LibWfenv Target_Definitions Core_Infrastructure.

(* ********************************************************************** *)

Theorem t_typing_implies_wfenv : forall D G m t,
  t_typing D G m t -> wfenv (t_wft D) G.
Proof.
   induction 1; eauto.
   eapply wfenv_push_inv_wfenv.
   (* TODO: Need lemmas that relate wfenv with (t_wft D) and (t_wft (D & (X ~ star))) *)
Admitted.

Theorem t_typing_implies_t_term : forall D G m t,
  t_typing D G m t -> t_term m.
Proof.
  induction 1; eauto.
  skip.
  apply t_term_if; eauto.
  (* TODO: Typing alone does not guarentee well-formed terms, due to value/term restrictions *)
Admitted.

(** * Properties of well-formedness of a type in an environment *)

(** If a type is well-formed in an environment then it is locally closed. *)
Lemma t_wft_implies_t_type : forall D t,
  t_wft D t -> t_type t.
Proof.
  intros.
  induction H; eauto.
Qed.
Hint Resolve t_wft_implies_t_type.

Lemma t_typing_wft : forall D G m t,
  t_typing D G m t -> t_type t.
Proof.
  induction 1; eauto; try (pick_fresh x; apply* (H1 x)).
  eapply t_wft_implies_t_type.
  eapply wfenv_binds; eauto. (* TODO *)
  inversion IHt_typing1.
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
