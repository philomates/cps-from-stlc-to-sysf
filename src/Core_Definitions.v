(********************************************************
 * Core source/target/combined language definitions     *
 * from Ahmed & Blume ICFP 2011                         *
 * William J. Bowman, Phillip Mates & James T. Perconti *
 ********************************************************)

Set Implicit Arguments.
Require Import LibLN.
Implicit Type x : var.
Implicit Type X : var.

(* Syntax of pre-types *)

Inductive typ : Set :=
  (* Source types *)
  | s_typ_bool : typ                (* bool *)
  | s_typ_arrow : typ -> typ -> typ (* s -> s *)

  (* Target types *)
  | t_typ_bool : typ                (* bool *)
  | t_typ_pair : typ -> typ -> typ  (* t x t *)
  | t_typ_bvar : nat -> typ         (* N *)
  | t_typ_fvar : var -> typ         (* X *)
  | t_typ_arrow : typ -> typ -> typ (* forall . t -> t *).

(* Syntax of pre-terms *)

Inductive trm : Set :=
  (* source values *)
  | s_trm_bvar : nat -> trm             (* n *)
  | s_trm_fvar : var -> trm             (* x *)
  | s_trm_true : trm                    (* tt *)
  | s_trm_false : trm                   (* ff *)
  | s_trm_abs : typ -> trm -> trm       (* lambda : s . e *)
  (* source non-values *)
  | s_trm_if : trm -> trm -> trm -> trm (* if e e e *)
  | s_trm_app : trm -> trm -> trm       (* e e *)

  (* target values *)
  | t_trm_bvar  : nat -> trm               (* n *)
  | t_trm_fvar  : var -> trm               (* x *)
  | t_trm_true  : trm                      (* tt *)
  | t_trm_false : trm                      (* ff *)
  | t_trm_pair  : trm -> trm -> trm        (* (u, u) *)
  | t_trm_abs   : typ -> trm -> trm        (* Lambda . lambda : t . m *)
  (* target non-values *)
  | t_trm_if    : trm -> trm -> trm -> trm (* if u e e *)
  | t_trm_let_fst : trm -> trm -> trm      (* let  = fst u in m *)
  | t_trm_let_snd : trm -> trm -> trm      (* let  = snd u in m *)
  | t_trm_app   : trm -> typ -> trm -> trm (* u [t] u *)

  (* Boundary Terms *)
  | trm_st : trm -> typ -> trm         (* (s) ST m *)
  | trm_ts : trm -> typ -> trm -> trm  (* let  = TS (s) e in m *).

(* Opening up a type binder occuring in a type *)
Fixpoint open_tt_rec (K : nat) (t' : typ) (t : typ) {struct t} : typ :=
  match t with
  (* no type variables in source types *)
  | s_typ_bool        => t
  | s_typ_arrow _ _   => t
  (* target types *)
  | t_typ_bool        => t_typ_bool
  | t_typ_pair t1 t2  => t_typ_pair (open_tt_rec K t' t1)
                                    (open_tt_rec K t' t2)
  | t_typ_bvar N      => If K = N then t' else (t_typ_bvar N)
  | t_typ_fvar X      => t_typ_fvar X
  | t_typ_arrow t1 t2 => t_typ_arrow (open_tt_rec (S K) t' t1)
                                     (open_tt_rec (S K) t' t2)
  end.

Definition open_tt t t' := open_tt_rec 0 t' t. (* t [t' / 0] *)

(** Opening up a type binder occuring in a term *)
Fixpoint open_te_rec (K : nat) (t' : typ) (e : trm) {struct e} : trm :=
  match e with
  (* source terms *)
  | s_trm_bvar n      => s_trm_bvar n
  | s_trm_fvar x      => s_trm_fvar x
  | s_trm_true        => s_trm_true
  | s_trm_false       => s_trm_false
  | s_trm_abs s e     => s_trm_abs s (open_te_rec K t' e)
  | s_trm_if e1 e2 e3 => s_trm_if (open_te_rec K t' e1)
                                  (open_te_rec K t' e2)
                                  (open_te_rec K t' e3)
  | s_trm_app e1 e2   => s_trm_app (open_te_rec K t' e1)
                                   (open_te_rec K t' e2)
  (* target terms *)
  | t_trm_bvar i      => t_trm_bvar i
  | t_trm_fvar x      => t_trm_fvar x
  | t_trm_true        => t_trm_true
  | t_trm_false       => t_trm_false
  | t_trm_pair u1 u2  => t_trm_pair (open_te_rec K t' u1)
                                    (open_te_rec K t' u2)
     (* t_trm_abs is the only form that binds a type variable *)
  | t_trm_abs t m     => t_trm_abs (open_tt_rec (S K) t' t)
                                   (open_te_rec (S K) t' m)
  | t_trm_if u m1 m2  => t_trm_if (open_te_rec K t' u)
                                  (open_te_rec K t' m1)
                                  (open_te_rec K t' m2)
  | t_trm_let_fst u m => t_trm_let_fst (open_te_rec K t' u)
                                       (open_te_rec K t' m)
  | t_trm_let_snd u m => t_trm_let_snd (open_te_rec K t' u)
                                       (open_te_rec K t' m)
  | t_trm_app m1 t m2 => t_trm_app (open_te_rec K t' m1)
                                   (open_tt_rec K t' t)
                                   (open_te_rec K t' m2)
  (* boundary terms *)
  | trm_st m t        => trm_st (open_te_rec K t' m)
                                (open_tt_rec K t' t)
  | trm_ts e t m      => trm_ts (open_te_rec K t' e)
                                (open_tt_rec K t' t)
                                (open_te_rec K t' m)
  end.

Definition open_te e t' := open_te_rec 0 t' e. (* e [t' / 0] *)

(** Opening up a term binder occuring in a term *)
Fixpoint open_ee_rec (k : nat) (f : trm) (e : trm) {struct e} : trm :=
  match e with
  | s_trm_bvar i      => If k = i then f else (s_trm_bvar i)
  | s_trm_fvar x      => s_trm_fvar x
  | s_trm_true        => s_trm_true
  | s_trm_false       => s_trm_false
  | s_trm_abs t e1    => s_trm_abs t (open_ee_rec (S k) f e1)
  | s_trm_if v e1 e2  => s_trm_if (open_ee_rec k f v)
                                  (open_ee_rec k f e1)
                                  (open_ee_rec k f e2)
  | s_trm_app e1 e2   => s_trm_app (open_ee_rec k f e1)
                                   (open_ee_rec k f e2)
  | t_trm_bvar i      => If k = i then f else (t_trm_bvar i)
  | t_trm_fvar x      => t_trm_fvar x
  | t_trm_true        => t_trm_true
  | t_trm_false       => t_trm_false
  | t_trm_pair v1 v2  => t_trm_pair (open_ee_rec k f v1) (open_ee_rec k f v2)
  | t_trm_abs t e1    => t_trm_abs t (open_ee_rec (S k) f e1)
  | t_trm_if v e1 e2  => t_trm_if (open_ee_rec k f v)
                                  (open_ee_rec k f e1)
                                  (open_ee_rec k f e2)
  | t_trm_let_fst v e => t_trm_let_fst (open_ee_rec k f v)
                                       (open_ee_rec (S k) f e)
  | t_trm_let_snd v e => t_trm_let_snd (open_ee_rec k f v)
                                       (open_ee_rec (S k) f e)
  | t_trm_app e1 t e2 => t_trm_app (open_ee_rec k f e1)
                                   t
                                   (open_ee_rec k f e2)
  | trm_st e t        => trm_st (open_ee_rec k f e) t
  | trm_ts e1 t e2    => trm_ts (open_ee_rec k f e1) t (open_ee_rec k f e2)
  end.

Definition open_ee t u := open_ee_rec 0 u t.

(** Notation for opening up binders with type or term variables *)

(* changing type vars in a term *)
Definition t_open_te_var e X := (open_te e (t_typ_fvar X)).
(* changing type vars in a type *)
Definition t_open_tt_var T X := (open_tt T (t_typ_fvar X)).
(* changing a term var in a term *)
Definition s_open_ee_var e x := (open_ee e (s_trm_fvar x)).
Definition t_open_ee_var e x := (open_ee e (t_trm_fvar x)).

(* Syntax of types *)
Inductive t_type : typ -> Prop :=
  | t_type_bool :
      t_type t_typ_bool
  | t_type_pair : forall T1 T2,
      t_type T1 -> t_type T2 -> t_type (t_typ_pair T1 T2)
  | t_type_var : forall X,
      t_type (t_typ_fvar X)
  | t_type_arrow : forall L T1 T2,
      (forall X, X \notin L ->
        t_type (t_open_tt_var T1 X)) ->
      (forall X, X \notin L -> t_type (t_open_tt_var T2 X)) ->
      t_type (t_typ_arrow T1 T2).

Inductive s_type : typ -> Prop :=
  | s_type_bool : s_type s_typ_bool
  | s_type_arrow : forall T1 T2, s_type (s_typ_arrow T1 T2).


Inductive type : typ -> Prop :=
  | type_t : forall t, t_type t -> type t
  | type_s : forall t, s_type t -> type t.


(* Source terms *)
Inductive s_term : trm -> Prop :=
  | s_term_value : forall v, s_value v -> s_term v
  | s_term_if : forall e1 e2 e3,
      s_term e1 -> s_term e2 -> s_term e3 ->
      s_term (s_trm_if e1 e2 e3)
  | s_term_app : forall e1 e2,
      s_term e1 -> s_term e2 ->
      s_term (s_trm_app e1 e2)

with s_value : trm -> Prop :=
  | s_value_var : forall x, s_value (s_trm_fvar x)
  | s_value_true : s_value s_trm_true
  | s_value_false : s_value s_trm_false
  | s_value_abs  : forall L T e,
      (forall x, x \notin L -> s_term (s_open_ee_var e x)) ->
      s_value (s_trm_abs T e).

Scheme s_term_mut := Induction for s_term Sort Prop
with s_value_mut := Induction for s_value Sort Prop.

(* TODO: Environments *)

(* Contexts *)
Inductive ctx : Set :=
  (* Source *)
  (* evaluation and general contexts *)
  | s_ctx_hole : ctx
  | s_ctx_if : ctx -> trm -> trm -> ctx
  | s_ctx_app1 : ctx -> trm -> ctx
  | s_ctx_app2 : trm -> ctx -> ctx
  (* general contexts only *)
  | s_ctx_abs : type -> ctx -> ctx
  | s_ctx_if_true : trm -> ctx -> trm -> ctx
  | s_ctx_if_false : trm -> trm -> ctx -> ctx
  (* evaluation context: CPS makes this simple *)

  (* Target *)
  | t_ctx_hole : ctx
  (* value contexts *)
  | t_ctx_pair_left : ctx -> trm -> ctx
  | t_ctx_pair_right : trm -> ctx -> ctx
  | t_ctx_abs : typ -> ctx -> ctx
  (* general contexts *)
  | t_ctx_if : ctx -> trm -> trm -> ctx
  | t_ctx_if_true : trm -> ctx -> trm -> ctx
  | t_ctx_if_false : trm -> trm -> ctx -> ctx
  | t_ctx_let_pair1 : ctx -> trm -> ctx
  | t_ctx_let_pair2 : ctx -> trm -> ctx
  | t_ctx_let_exp1 : trm -> ctx -> ctx
  | t_ctx_let_exp2 : trm -> ctx -> ctx
  | t_ctx_app1 : ctx -> typ -> trm -> ctx
  | t_ctx_app2 : trm -> typ -> ctx -> ctx.

(* Opening of contexts *)
Fixpoint ctx_open_ee_rec (k : nat) (f : trm) (C : ctx) {struct C} : ctx :=
  match C with
    | s_ctx_hole => s_ctx_hole
    | s_ctx_if C e2 e3 => s_ctx_if (ctx_open_ee_rec K f C)
                                   (open_ee_rec K f e2)
                                   (open_ee_rec K f e3)
    | s_ctx_app1 C e => s_ctx_app1 (ctx_open_ee_rec K f C) (open_ee_rec K f e)
    | s_ctx_app2 e C => s_ctx_app2 (open_ee_rec K f e) (ctx_open_ee_rec K f C)
    | s_ctx_abs s C  => s_ctx_abs s (ctx_open_ee_rec K f C)
    | s_ctx_if_true e1 C e3 => s_ctx_if_true (open_ee_rec K f e1)
                                             (ctx_open_ee_rec K f C)
                                             (open_ee_rec K f e3)
    | s_ctx_if_false e1 e2 C => s_ctx_if_false (open_ee_rec K f e1)
                                               (open_ee_rec K f e2)
                                               (ctx_open_ee_rec K f C)

    | t_ctx_hole => t_ctx_hole
    | t_ctx_pair_left C m => t_ctx_pair_left (ctx_open_ee_rec (S K) f C)
                                         (open_ee_rec K f m)
    | t_ctx_pair_right m C => t_ctx_pair_right (open_ee_rec K f m)
                                           (ctx_open_ee_rec (S K) f C)
    | t_ctx_abs t C  => t_ctx_abs t (ctx_open_ee_rec (S K) f C)
    | t_ctx_if C m1 m2 => t_ctx_if (ctx_open_ee_rec K f C)
                                 (open_ee_rec K f m1)
                                 (open_ee_rec K f m2)
    | t_ctx_if_true m1 C m2 => t_ctx_if_true (open_ee_rec K f m1)
                                 (ctx_open_ee_rec K f C)
                                 (open_ee_rec K f m2)
    | t_ctx_if_false m1 m2 C => t_ctx_if_false (open_ee_rec K f m1)
                                 (open_ee_rec K f m2)
                                 (ctx_open_ee_rec K f C)
    | t_ctx_let_pair1 C m => t_ctx_let_pair1 (ctx_open_ee_rec K f C)
                                         (open_ee_rec K f m)
    | t_ctx_let_pair2 C m => t_ctx_let_pair2 (ctx_open_ee_rec K f C)
                                         (open_ee_rec K f m)
    | t_ctx_let_exp1 m C => t_ctx_let_exp1 (open_ee_rec K f m)
                                       (ctx_open_ee_rec K f C)
    | t_ctx_let_exp2 m C => t_ctx_let_exp2 (open_ee_rec K f m)
                                       (ctx_open_ee_rec K f C)
    | t_ctx_app1 C t m => t_ctx_app1 (ctx_open_ee_rec K f C) t (open_ee_rec K f m)
    | t_ctx_app2 m t C => t_ctx_app2 (open_ee_rec K f m) t (ctx_open_ee_rec K f C)
  end.

Fixpoint ctx_open_te_rec (K : nat) (t' : typ) (C : ctx) {struct C} : ctx :=
  match C with
    | s_ctx_hole => s_ctx_hole
    | s_ctx_if C e2 e3 => s_ctx_if (ctx_open_te_rec K t' C)
                                   (open_te_rec K t' e2)
                                   (open_te_rec K t' e3)
    | s_ctx_app1 C e => s_ctx_app1 (ctx_open_te_rec K t' C) (open_te_rec K t' e)
    | s_ctx_app2 e C => s_ctx_app2 (open_te_rec K t' e) (ctx_open_te_rec K t' C)
    | s_ctx_abs s C  => s_ctx_abs s (ctx_open_te_rec K t' C)
    | s_ctx_if_true e1 C e3 => s_ctx_if_true (open_te_rec K t' e1)
                                             (ctx_open_te_rec K t' C)
                                             (open_te_rec K t' e3)
    | s_ctx_if_false e1 e2 C => s_ctx_if_false (open_te_rec K t' e1)
                                               (open_te_rec K t' e2)
                                               (ctx_open_te_rec K t' C)

    | t_ctx_hole => t_ctx_hole
    | t_ctx_pair_left C m => t_ctx_pair_left (ctx_open_te_rec (S K) t' C)
                                             (open_te_rec K t' m)
    | t_ctx_pair_right m C => t_ctx_pair_right (open_te_rec K t' m)
                                               (ctx_open_te_rec (S K) t' C)
    | t_ctx_abs t C  => t_ctx_abs (open_tt_rec (S K) t' t) 
                                  (ctx_open_te_rec (S K) t' C)
    | t_ctx_if C m1 m2 => t_ctx_if (ctx_open_te_rec K t' C)
                                   (open_te_rec K t' m1)
                                   (open_te_rec K t' m2)
    | t_ctx_if_true m1 C m2 => t_ctx_if_true (open_te_rec K t' m1)
                                             (ctx_open_te_rec K t' C)
                                             (open_te_rec K t' m2)
    | t_ctx_if_false m1 m2 C => t_ctx_if_false (open_te_rec K t' m1)
                                               (open_te_rec K t' m2)
                                               (ctx_open_te_rec K t' C)
    | t_ctx_let_pair1 C m => t_ctx_let_pair1 (ctx_open_te_rec K t' C)
                                             (open_te_rec K t' m)
    | t_ctx_let_pair2 C m => t_ctx_let_pair2 (ctx_open_te_rec K t' C)
                                             (open_te_rec K t' m)
    | t_ctx_let_exp1 m C => t_ctx_let_exp1 (open_te_rec K t' m)
                                           (ctx_open_te_rec K t' C)
    | t_ctx_let_exp2 m C => t_ctx_let_exp2 (open_te_rec K t' m)
                                           (ctx_open_te_rec K t' C)
    | t_ctx_app1 C t m => t_ctx_app1 (ctx_open_te_rec K t' C)
                                     (open_tt_rec (S K) t' t)
                                     (open_te_rec K t' m)
    | t_ctx_app2 m t C => t_ctx_app2 (open_te_rec K t' m)
                                     (open_tt_rec (S K) t' t)
                                     (ctx_open_te_rec K t' C)
  end.

Definition ctx_open_ee C m := ctx_open_ee_rec 0 m C.
Definition ctx_open_te C t := ctx_open_te_rec 0 t C.
Definition ctx_open_ee_var C x := ctx_open_ee C (trm_fvar x).
Definition ctx_open_te_var C X := ctx_open_te C (t_typ_fvar X).

(* TODO: Reduction rules *)
(* TODO: Equivalence *)
