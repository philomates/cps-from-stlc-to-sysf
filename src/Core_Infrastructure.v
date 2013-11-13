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

