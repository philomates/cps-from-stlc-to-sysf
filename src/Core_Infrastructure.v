(***************************************************************************
* Core Infrastructure                                                      *
* Multilanguage present in Ahmed & Blume ICFP 2011
* William J. Bowman, Phillip Mates & James T. Perconti                     *
***************************************************************************)

Require Export Core_Definitions.

(* ********************************************************************** *)
(** * Additional Definitions Used in the Proofs *)

(** Computing free type variables in a type *)

Fixpoint fv_tt (T : typ) {struct T} : vars :=
  match T with
  | s_typ_bool        => \{}
  | s_typ_arrow s1 s2 => (fv_tt s1) \u (fv_tt s2)

  | t_typ_bvar J      => \{}
  | t_typ_fvar X      => \{X}
  | t_typ_bool        => \{}
  | t_typ_pair t1 t2  => (fv_tt t1) \u (fv_tt t2)
  | t_typ_arrow t1 t2 => (fv_tt t1) \u (fv_tt t2)
  | typ_bad => \{}
  end.

(** Computing free type variables in a term *)

Fixpoint fv_te (e : trm) {struct e} : vars :=
  match e with
  | s_trm_bvar i    => \{}
  | s_trm_fvar x    => \{}
  | s_trm_true      => \{}
  | s_trm_false     => \{}
  | s_trm_abs s e1  => (fv_te e1)
  | s_trm_if e1 e2 e3 => (fv_te e1) \u (fv_te e2) \u (fv_te e3)
  | s_trm_app e1 e2 => (fv_te e1) \u (fv_te e2)

  | t_trm_bvar i    => \{}
  | t_trm_fvar x    => \{}
  | t_trm_true      => \{}
  | t_trm_false     => \{}
  | t_trm_pair e1 e2 => (fv_te e1) \u (fv_te e2)
  | t_trm_abs t e1  => (fv_tt t) \u (fv_te e1)
  | t_trm_if v e1 e2 => (fv_te v) \u (fv_te e1) \u (fv_te e2)
  | t_trm_let_fst v e2 => (fv_te v) \u (fv_te e2)
  | t_trm_let_snd v e2 => (fv_te v) \u (fv_te e2)
  | t_trm_app e1 t e2 => (fv_te e1) \u (fv_tt t) \u (fv_te e2)

  | s_trm_st m1 s1 => (fv_te m1)
  | t_trm_ts e1 s1 m2 => (fv_te e1) \u (fv_te m2)

  | trm_bad => \{}
  end.

(** Computing free term variables in a term *)

Fixpoint fv_ee (l : lang) (e : trm) {struct e} : vars :=
  match e with
  | s_trm_bvar i    => \{}
  | s_trm_fvar x    => if beq_lang l source then \{x} else \{}
  | s_trm_true      => \{}
  | s_trm_false     => \{}
  | s_trm_abs s e1  => (fv_ee l e1)
  | s_trm_if e1 e2 e3 => (fv_ee l e1) \u (fv_ee l e2) \u (fv_ee l e3)
  | s_trm_app e1 e2 => (fv_ee l e1) \u (fv_ee l e2)

  | t_trm_bvar i    => \{}
  | t_trm_fvar x    => if beq_lang l target then \{x} else \{}
  | t_trm_true      => \{}
  | t_trm_false     => \{}
  | t_trm_pair e1 e2 => (fv_ee l e1) \u (fv_ee l e2)
  | t_trm_abs t e1  => (fv_ee l e1)
  | t_trm_if v e1 e2 => (fv_ee l v) \u (fv_ee l e1) \u (fv_ee l e2)
  | t_trm_let_fst v e2 => (fv_ee l v) \u (fv_ee l e2)
  | t_trm_let_snd v e2 => (fv_ee l v) \u (fv_ee l e2)
  | t_trm_app e1 t e2 => (fv_ee l e1) \u (fv_ee l e2)

  | s_trm_st m1 s1 => (fv_ee l m1)
  | t_trm_ts e1 s1 m2 => (fv_ee l e1) \u (fv_ee l m2)

  | trm_bad => \{}
  end.

(************************************************************************)

(* turn an fvar into a bvar (inverse of open) *)
Fixpoint close_ee_rec (l : lang) (x : var) (k : nat) (e : trm) : trm :=
  match e with
  (* source terms *)
  | s_trm_bvar i => s_trm_bvar i
  | s_trm_fvar y => if andb (beq_lang l source) (LibReflect.decide (x = y))
                    then s_trm_bvar k else s_trm_fvar y
  | s_trm_true => s_trm_true
  | s_trm_false => s_trm_false
  | s_trm_abs s e => s_trm_abs s (close_ee_rec l x (inc_if_eq l source k) e)
  | s_trm_if e1 e2 e3 => s_trm_if (close_ee_rec l x k e1)
                                  (close_ee_rec l x k e2)
                                  (close_ee_rec l x k e3)
  | s_trm_app e1 e2 => s_trm_app (close_ee_rec l x k e1)
                                 (close_ee_rec l x k e2)
  | s_trm_st m s => s_trm_st (close_ee_rec l x k m) s
  (* target terms *)
  | t_trm_bvar i => t_trm_bvar i
  | t_trm_fvar y => if andb (beq_lang l target) (LibReflect.decide (x = y))
                    then t_trm_bvar k else t_trm_fvar y
  | t_trm_true => t_trm_true
  | t_trm_false => t_trm_false
  | t_trm_pair u1 u2 => t_trm_pair (close_ee_rec l x k u1)
                                   (close_ee_rec l x k u2)
  | t_trm_abs t m => t_trm_abs t (close_ee_rec l x (inc_if_eq l target k) m)
  | t_trm_if u m1 m2 => t_trm_if (close_ee_rec l x k u)
                                 (close_ee_rec l x k m1)
                                 (close_ee_rec l x k m2)
  | t_trm_let_fst u m => t_trm_let_fst (close_ee_rec l x k u)
                                       (close_ee_rec l x (inc_if_eq l target k) m)
  | t_trm_let_snd u m => t_trm_let_snd (close_ee_rec l x k u)
                                       (close_ee_rec l x (inc_if_eq l target k) m)
  | t_trm_app m1 t m2 => t_trm_app (close_ee_rec l x k m1)
                                   t
                                   (close_ee_rec l x k m2)
  | t_trm_ts e s m    => t_trm_ts (close_ee_rec l x k e)
                                  s
                                  (close_ee_rec l x (inc_if_eq l target k) m)
  (* blah *)
  | trm_bad => trm_bad
  end.

Definition close_ee (l : lang) (x : var) (e : trm) := close_ee_rec l x 0 e.
Definition s_close_ee := close_ee source.
Definition t_close_ee := close_ee target.

(************************************************************************)

(** Size of a type *)
Fixpoint typ_size (t : typ) : nat :=
  match t with
  (* source types *)
  | s_typ_bool        => 1
  | s_typ_arrow s1 s2   => (typ_size s1) + (typ_size s2)
  (* target types *)
  | t_typ_bvar _      => 1
  | t_typ_fvar _      => 1
  | t_typ_bool        => 1
  | t_typ_pair t1 t2  => 1 + (typ_size t1) + (typ_size t2)
  | t_typ_arrow t1 t2 => 1 + (typ_size t1) + (typ_size t2)
  (* blah *)
  | typ_bad => 1
  end.

(** Size of a term *)
Fixpoint trm_size (t : trm) : nat :=
  match t with
  (* source values *)
  | s_trm_bvar _ => 1
  | s_trm_fvar _ => 1
  | s_trm_true => 1
  | s_trm_false => 1
  | s_trm_abs s e => 1 + (typ_size s) + (trm_size e)
  (* source non-values *)
  | s_trm_if e1 e2 e3 => 1 + (trm_size e1) + (trm_size e2) + (trm_size e3)
  | s_trm_app e1 e2 => 1 + (trm_size e1) + (trm_size e2)

  (* target values *)
  | t_trm_bvar _ => 1
  | t_trm_fvar _ => 1
  | t_trm_true  => 1
  | t_trm_false => 1
  | t_trm_pair u1 u2 => 1 + (trm_size u1) + (trm_size u2)
  | t_trm_abs t m => 1 + (typ_size t) + (trm_size m)
  (* target non-values *)
  | t_trm_if u m1 m2 => 1 + (trm_size u) + (trm_size m1) + (trm_size m2)
  | t_trm_let_fst u m => 1 + (trm_size u) + (trm_size m)
  | t_trm_let_snd u m => 1 + (trm_size u) + (trm_size m)
  | t_trm_app u1 t u2 => 1 + (trm_size u1) + (typ_size t) + (trm_size u2)

  (* Boundary Terms *)
  | s_trm_st m s => 1 + (trm_size m) + (typ_size s)
  | t_trm_ts e s m => 1 + (trm_size e) + (typ_size s) + (trm_size m)

  (* error case *)
  | trm_bad => 1
  end.

Lemma typ_size_open_var : forall X t,
  typ_size (open_tt_var t X) = typ_size t.
Proof.
  intros. generalize 0.
  induction t; intros; simpl; auto.
  case_if*.
Qed.

Lemma s_trm_size_open_var : forall x t,
  trm_size (s_open_ee_var t x) = trm_size t.
Proof.
  intros. generalize 0.
  induction t; intros; simpl; auto.
  case_if*.
Qed.

Lemma t_trm_size_open_var : forall x t,
  trm_size (t_open_ee_var t x) = trm_size t.
Proof.
  intros. generalize 0.
  induction t; intros; simpl; auto.
  case_if*.
Qed.

(* empty substitutions don't do anyting *)

Lemma subst_tt_empty : forall t, subst_tt empty t = t.
Proof.
  induction t; simpl; fequals; auto. rewrite* get_none.
Qed.

Lemma subst_te_empty : forall e, subst_te empty e = e.
Proof.
  induction e; simpl; fequals; auto using subst_tt_empty.
Qed.

Lemma subst_ee_empty : forall l e, subst_ee l empty e = e.
Proof.
  induction e; simpl; fequals; auto; cases_if*; rewrite* get_none.
Qed.

(* weakening for substitutions *)

Lemma subst_tt_push : forall t X t' d, X \notin fv_tt t ->
  subst_tt (d & X ~ t') t = subst_tt d t.
Proof.
  induction t; simpl; intros; auto; try rewrite* IHt1; try rewrite* IHt2.
  rewrite get_push. cases_if*. false. auto using in_singleton_self.
Qed.

Lemma subst_te_push : forall e X t d, X \notin fv_te e ->
  subst_te (d & X ~ t) e = subst_te d e.
Proof.
  induction e; simpl; auto; intros; try rewrite* subst_tt_push;
    try rewrite* IHe; try rewrite* IHe1; try rewrite* IHe2; try rewrite* IHe3.
Qed.

Lemma subst_ee_push : forall e x e' g l, x \notin fv_ee l e ->
  subst_ee l (g & x ~ e') e = subst_ee l g e.
Proof.
  induction e; simpl; intros; auto;
    try rewrite* IHe; try rewrite* IHe1; try rewrite* IHe2; try rewrite* IHe3;
  cases_if*; rewrite get_push; cases_if*; false; auto using in_singleton_self.
Qed.

Lemma subst_tt_weaken : forall t X t' d d', X \notin fv_tt t ->
  subst_tt (d & X ~ t' & d') t = subst_tt (d & d') t.
Proof.
  induction t; simpl; intros; auto; try rewrite* IHt1; try rewrite* IHt2.
  repeat rewrite get_concat. destruct* (get v d').
  rewrite get_single. cases_if*. false. auto using in_singleton_self.
Qed.

Lemma subst_te_weaken : forall e X t d d', X \notin fv_te e ->
  subst_te (d & X ~ t & d') e = subst_te (d & d') e.
Proof.
  induction e; simpl; auto; intros; try rewrite* subst_tt_weaken;
    try rewrite* IHe; try rewrite* IHe1; try rewrite* IHe2; try rewrite* IHe3.
Qed.

Lemma subst_ee_weaken : forall e x e' g g' l, x \notin fv_ee l e ->
  subst_ee l (g & x ~ e' & g') e = subst_ee l (g & g') e.
Proof.
  induction e; simpl; intros; auto;
    try rewrite* IHe; try rewrite* IHe1; try rewrite* IHe2; try rewrite* IHe3;
  cases_if*; repeat rewrite get_concat; destruct* (get v g');
    rewrite get_single; cases_if*; false; auto using in_singleton_self.
Qed.

(* exchange for substitutions *)

Lemma subst_tt_exchange : forall t D1 D2 D3 D4, ok (D1 & D2 & D3 & D4) ->
  subst_tt (D1 & D2 & D3 & D4) t = subst_tt (D1 & D3 & D2 & D4) t.
Proof.
  induction t; simpl; intros; f_equal*.
  repeat rewrite get_concat.
  case_eq (get v D1); case_eq (get v D2); case_eq (get v D3); case_eq (get v D4); intros; auto;
  apply binds_func with (x := v) (E := D1 & D2 & D3 & D4); repeat apply* binds_concat_left_ok.
Qed.

(* fv and open *)

Lemma open_tt_rec_fv_tt : forall t n X,
  fv_tt (open_tt_rec n (t_typ_fvar X) t) = (fv_tt t \u \{ X }) \/
  fv_tt (open_tt_rec n (t_typ_fvar X) t) = (fv_tt t).
Proof.
  induction t; simpl; auto using subset_union_weak_l; intros.
  cases_if; simpl; auto. left. rewrite* union_empty_l.
  destruct (IHt1 n X); destruct (IHt2 n X).
    left. rewrite <- union_same with (E := \{ X });
          rewrite <- union_assoc; rewrite union_assoc with (E := fv_tt t2);
          rewrite union_comm with (E := fv_tt t2 \u \{ X }); rewrite union_assoc.
          rewrite H. rewrite* H0.
    left. rewrite H. rewrite H0.
          rewrite <- union_assoc. rewrite union_comm with (E := \{ X }). apply union_assoc.
    left. rewrite H. rewrite H0. apply union_assoc.
    right. rewrite H. rewrite* H0.
  destruct (IHt1 (S n) X); destruct (IHt2 (S n) X).
    left. rewrite <- union_same with (E := \{ X });
          rewrite <- union_assoc; rewrite union_assoc with (E := fv_tt t2);
          rewrite union_comm with (E := fv_tt t2 \u \{ X }); rewrite union_assoc.
          rewrite H. rewrite* H0.
    left. rewrite H. rewrite H0.
          rewrite <- union_assoc. rewrite union_comm with (E := \{ X }). apply union_assoc.
    left. rewrite H. rewrite H0. apply union_assoc.
    right. rewrite H. rewrite* H0.  
Qed.

Lemma open_tt_var_fv_tt : forall t X,
  fv_tt (open_tt_var t X) = (fv_tt t \u \{ X }) \/
  fv_tt (open_tt_var t X) = (fv_tt t).
Proof.
  intros. apply* open_tt_rec_fv_tt.
Qed.

(* ********************************************************************** *)
(** * Tactics *)

(** Gathering free names already used in the proofs *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : typ => fv_tt x) in
  let D := gather_vars_with (fun x : trm => fv_te x) in
  let E := gather_vars_with (fun x : trm => fv_ee source x) in
  let F := gather_vars_with (fun x : trm => fv_ee target x) in
  let G := gather_vars_with (fun x : env_type => dom x) in
  let H := gather_vars_with (fun x : env_term => dom x) in
  let I := gather_vars_with (fun x : env_term => fold_vars fv_tt x) in
  let J := gather_vars_with (fun x : subst_type => dom x) in
  let K := gather_vars_with (fun x : subst_type => fold_vars fv_tt x) in
  let L := gather_vars_with (fun x : subst_term => dom x) in
  let M := gather_vars_with (fun x : subst_term => fold_vars fv_te x) in
  let N := gather_vars_with (fun x : subst_term =>
                               fold_vars (fv_ee source) x) in
  let O := gather_vars_with (fun x : subst_term =>
                               fold_vars (fv_ee target) x) in
  constr:(A \u B \u C \u D \u E \u F \u G \u H \u
          I \u J \u K \u L \u M \u N \u O).

(** "pick_fresh x" tactic create a fresh variable with name x *)

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).

(** "apply_fresh T as x" is used to apply inductive rule which
   use an universal quantification over a cofinite set *)

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; auto*.

(* try to auto a goal with a fresh variable needed *)
Ltac frauto :=
  eauto;
  let x := fresh "x" in
    pick_fresh x; eauto;
      try match goal with
            | [ H : (forall x : var, x \notin ?L -> _) |- _ ]
              => let Fr := fresh "Fr" in assert (Fr : x \notin L); eauto end.

(** These tactics help applying a lemma which conclusion mentions
  an environment (E & F) in the particular case when F is empty *)

(* TODO:
Ltac get_env_type :=
  match goal with
  | |- wft ?D _ => D
  | |- typing ?D _ _ _ => D
  end.

Ltac get_env_term :=
  match goal with
  | |- typing _ ?G _ _ => G
  end.
*)

Tactic Notation "apply_empty_bis" tactic(get_env) constr(lemma) :=
  let E := get_env in rewrite <- (concat_empty_r E);
  eapply lemma; try rewrite concat_empty_r.

(* TODO:
Tactic Notation "apply_empty" constr(F) :=
  try apply_empty_bis (get_env_term) F;
  try apply_empty_bis (get_env_type) F.
*)

Tactic Notation "apply_empty" "*" constr(F) :=
  apply_empty F; auto*.

(** Tactic to undo when Coq does too much simplification *)

Ltac unsimpl_map_bind :=
  match goal with |- context [ ?B (subst_tt ?Z ?P ?U) ] =>
    unsimpl ((subst_tt Z P) (B U)) end.

Tactic Notation "unsimpl_map_bind" "*" :=
  unsimpl_map_bind; auto*.
