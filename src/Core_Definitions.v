(********************************************************
 * Core source/target/combined language definitions     *
 * from Ahmed & Blume ICFP 2011                         *
 * William J. Bowman, Phillip Mates & James T. Perconti *
 ********************************************************)

Set Implicit Arguments.
Require Import LibLN.
Require Import EqNat.
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
  | t_typ_bvar N      => if beq_nat K N then t' else (t_typ_bvar N)
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

(** Opening up a source-language term binder *)
Fixpoint s_open_ee_rec (k : nat) (e' : trm) (e : trm) { struct e} : trm :=
  match e with
  (* source terms *)
  | s_trm_bvar i      => if beq_nat k i then e' else (s_trm_bvar i)
  | s_trm_fvar x      => s_trm_fvar x
  | s_trm_true        => s_trm_true
  | s_trm_false       => s_trm_false
     (* s_trm_abs is the only binding form we care about here *)
  | s_trm_abs s e     => s_trm_abs s (s_open_ee_rec (S k) e' e)
  | s_trm_if e1 e2 e3 => s_trm_if (s_open_ee_rec k e' e1)
                                  (s_open_ee_rec k e' e2)
                                  (s_open_ee_rec k e' e3)
  | s_trm_app e1 e2   => s_trm_app (s_open_ee_rec k e' e1)
                                   (s_open_ee_rec k e' e2)
  (* target terms *)
  | t_trm_bvar i      => t_trm_bvar i
  | t_trm_fvar x      => t_trm_fvar x
  | t_trm_true        => t_trm_true
  | t_trm_false       => t_trm_false
  | t_trm_pair u1 u2  => t_trm_pair (s_open_ee_rec k e' u1)
                                    (s_open_ee_rec k e' u2)
  | t_trm_abs t m     => t_trm_abs t (s_open_ee_rec k e' m)
  | t_trm_if u m1 m2  => t_trm_if (s_open_ee_rec k e' u)
                                  (s_open_ee_rec k e' m1)
                                  (s_open_ee_rec k e' m2)
  | t_trm_let_fst u m => t_trm_let_fst (s_open_ee_rec k e' u)
                                       (s_open_ee_rec k e' m)
  | t_trm_let_snd u m => t_trm_let_snd (s_open_ee_rec k e' u)
                                       (s_open_ee_rec k e' m)
  | t_trm_app m1 t m2 => t_trm_app (s_open_ee_rec k e' m1)
                                   t
                                   (s_open_ee_rec k e' m2)
  (* boundary terms *)
  | trm_st m t        => trm_st (s_open_ee_rec k e' m) t
  | trm_ts e t m      => trm_ts (s_open_ee_rec k e' e) t (s_open_ee_rec k e' m)
  end.

Definition s_open_ee e e' := s_open_ee_rec 0 e' e. (* e [e' / 0] *)

(** Opening up a target-language term binder *)
Fixpoint t_open_ee_rec (k : nat) (m' : trm) (e : trm) {struct e} : trm :=
  match e with
  (* source terms *)
  | s_trm_bvar i      => s_trm_bvar i
  | s_trm_fvar x      => s_trm_fvar x
  | s_trm_true        => s_trm_true
  | s_trm_false       => s_trm_false
  | s_trm_abs s e     => s_trm_abs s (t_open_ee_rec k m' e)
  | s_trm_if u e1 e2  => s_trm_if (t_open_ee_rec k m' u)
                                  (t_open_ee_rec k m' e1)
                                  (t_open_ee_rec k m' e2)
  | s_trm_app e1 e2   => s_trm_app (t_open_ee_rec k m' e1)
                                   (t_open_ee_rec k m' e2)
  (* target terms *)
  | t_trm_bvar i      => if beq_nat k i then m' else (t_trm_bvar i)
  | t_trm_fvar x      => t_trm_fvar x
  | t_trm_true        => t_trm_true
  | t_trm_false       => t_trm_false
  | t_trm_pair u1 u2  => t_trm_pair (t_open_ee_rec k m' u1)
                                    (t_open_ee_rec k m' u2)
  | t_trm_abs t m     => t_trm_abs t (t_open_ee_rec (S k) m' m)
  | t_trm_if u m1 m2  => t_trm_if (t_open_ee_rec k m' u)
                                  (t_open_ee_rec k m' m1)
                                  (t_open_ee_rec k m' m2)
  | t_trm_let_fst u m => t_trm_let_fst (t_open_ee_rec k m' u)
                                       (t_open_ee_rec (S k) m' m)
  | t_trm_let_snd u m => t_trm_let_snd (t_open_ee_rec k m' u)
                                       (t_open_ee_rec (S k) m' m)
  | t_trm_app m1 t m2 => t_trm_app (t_open_ee_rec k m' m1)
                                   t
                                   (t_open_ee_rec k m' m2)
  (* boundary terms *)
  | trm_st m t        => trm_st (t_open_ee_rec k m' m) t
  | trm_ts e t m      => trm_ts (t_open_ee_rec k m' e) t (t_open_ee_rec (S k) m' m)
  end.

Definition t_open_ee e m' := t_open_ee_rec 0 m' e. (* e [m' / 0] *)

(** Notation for opening up binders with type or term variables *)

(* changing type vars in a term *)
Definition open_te_var e X := (open_te e (t_typ_fvar X)).
(* changing type vars in a type *)
Definition open_tt_var T X := (open_tt T (t_typ_fvar X)).
(* changing a term var in a term *)
Definition s_open_ee_var e x := (s_open_ee e (s_trm_fvar x)).
Definition t_open_ee_var e x := (t_open_ee e (t_trm_fvar x)).

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
        t_type (open_tt_var T1 X)) ->
      (forall X, X \notin L -> t_type (open_tt_var T2 X)) ->
      t_type (t_typ_arrow T1 T2).

(* Target terms *)
Inductive t_term : trm -> Prop :=
  | t_term_value : forall v, t_value v -> t_term v
  | t_term_if : forall v e1 e2,
      t_value v ->
      t_term e1 ->
      t_term e2 ->
      t_term (t_trm_if v e1 e2)
  | t_term_let_fst : forall L v e,
      t_value v ->
      (forall x, x \notin L -> t_term (t_open_ee_var e x)) ->
      t_term (t_trm_let_fst v e)
  | t_term_let_snd : forall L v e,
      t_value v ->
      (forall x, x \notin L -> t_term (t_open_ee_var e x)) ->
      t_term (t_trm_let_snd v e)
  | t_term_app : forall T v1 v2,
      t_value v1 ->
      t_type T ->
      t_value v2 ->
      t_term (t_trm_app v1 T v2)

with t_value : trm -> Prop :=
  | t_value_var : forall x,
      t_value (t_trm_fvar x)
  | t_value_true : t_value t_trm_true
  | t_value_false : t_value t_trm_false
  | t_value_pair : forall v1 v2,
      t_value v1 -> t_value v2 -> t_value (t_trm_pair v1 v2)
  | t_value_abs  : forall L T e1,
      (forall X, X \notin L ->
        t_type (open_tt_var T X)) ->
      (forall x X, x \notin L -> X \notin L ->
        t_term (open_te_var (t_open_ee_var e1 x) X)) ->
      t_value (t_trm_abs T e1).

(* Contexts *)
Inductive ctx : Set :=
  (* Source *)
  (* evaluation and general contexts *)
  | s_ctx_hole : ctx
  | s_ctx_if : ctx -> trm -> trm -> ctx
  | s_ctx_app1 : ctx -> trm -> ctx
  | s_ctx_app2 : trm -> ctx -> ctx
  (* general contexts only *)
  | s_ctx_abs : typ -> ctx -> ctx
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
  | t_ctx_app2 : trm -> typ -> ctx -> ctx

  (* Boundary Terms *)
  | ctx_st : ctx -> typ -> ctx (* σ ST E *)
  | ctx_ts : ctx -> typ -> trm -> ctx (* let _ = (ST σ E) in m *).

(* Opening of contexts *)
(* isS = True means we are opening a source term
 * isS = False means we are opening a target term *)
Fixpoint ctx_open_ee_rec (isS : bool) (K : nat) (f : trm)
                         (C : ctx) {struct C} : ctx :=
  let (Ss,St) := match isS with
              | true => (S,id)
              | false => (id,S)
            end in
  match C with
    (* source contexts *)
    | s_ctx_hole => s_ctx_hole
    | s_ctx_if C e2 e3 => s_ctx_if (ctx_open_ee_rec isS K f C)
                                   (s_open_ee_rec K f e2)
                                   (s_open_ee_rec K f e3)
    | s_ctx_app1 C e => s_ctx_app1 (ctx_open_ee_rec isS K f C) (s_open_ee_rec K f e)
    | s_ctx_app2 e C => s_ctx_app2 (s_open_ee_rec K f e) (ctx_open_ee_rec isS K f C)
    | s_ctx_abs s C  => s_ctx_abs s (ctx_open_ee_rec isS (Ss K) f C)
    | s_ctx_if_true e1 C e3 => s_ctx_if_true (s_open_ee_rec K f e1)
                                             (ctx_open_ee_rec isS K f C)
                                             (s_open_ee_rec K f e3)
    | s_ctx_if_false e1 e2 C => s_ctx_if_false (s_open_ee_rec K f e1)
                                               (s_open_ee_rec K f e2)
                                               (ctx_open_ee_rec isS K f C)
    (* target contexts *)
    | t_ctx_hole => t_ctx_hole
    | t_ctx_pair_left C m => t_ctx_pair_left (ctx_open_ee_rec isS (St K) f C)
                                             (t_open_ee_rec K f m)
    | t_ctx_pair_right m C => t_ctx_pair_right (t_open_ee_rec K f m)
                                               (ctx_open_ee_rec isS (St K) f C)
    | t_ctx_abs t C  => t_ctx_abs t (ctx_open_ee_rec isS (St K) f C)
    | t_ctx_if C m1 m2 => t_ctx_if (ctx_open_ee_rec isS K f C)
                                   (t_open_ee_rec K f m1)
                                   (t_open_ee_rec K f m2)
    | t_ctx_if_true m1 C m2 => t_ctx_if_true (t_open_ee_rec K f m1)
                                             (ctx_open_ee_rec isS K f C)
                                             (t_open_ee_rec K f m2)
    | t_ctx_if_false m1 m2 C => t_ctx_if_false (t_open_ee_rec K f m1)
                                               (t_open_ee_rec K f m2)
                                               (ctx_open_ee_rec isS K f C)
    | t_ctx_let_pair1 C m => t_ctx_let_pair1 (ctx_open_ee_rec isS K f C)
                                             (t_open_ee_rec K f m)
    | t_ctx_let_pair2 C m => t_ctx_let_pair2 (ctx_open_ee_rec isS K f C)
                                             (t_open_ee_rec K f m)
    | t_ctx_let_exp1 m C => t_ctx_let_exp1 (t_open_ee_rec K f m)
                                           (ctx_open_ee_rec isS K f C)
    | t_ctx_let_exp2 m C => t_ctx_let_exp2 (t_open_ee_rec K f m)
                                           (ctx_open_ee_rec isS (St K) f C)
    | t_ctx_app1 C t m => t_ctx_app1 (ctx_open_ee_rec isS K f C) t
                                     (t_open_ee_rec K f m)
    | t_ctx_app2 m t C => t_ctx_app2 (t_open_ee_rec K f m) t
                                     (ctx_open_ee_rec isS K f C)
    (* boundary contexts *)
    | ctx_st C s => ctx_st (ctx_open_ee_rec isS K f C) s
    | ctx_ts C s m => ctx_ts (ctx_open_ee_rec isS K f C) s
                             (t_open_ee_rec (St K) f m)
  end.

Fixpoint ctx_open_te_rec (K : nat) (t' : typ) (C : ctx) {struct C} : ctx :=
  match C with
    (* source contexts *)
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

    (* target contexts *)
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
                                           (ctx_open_te_rec (S K) t' C)
    | t_ctx_app1 C t m => t_ctx_app1 (ctx_open_te_rec K t' C)
                                     (open_tt_rec (S K) t' t)
                                     (open_te_rec K t' m)
    | t_ctx_app2 m t C => t_ctx_app2 (open_te_rec K t' m)
                                     (open_tt_rec (S K) t' t)
                                     (ctx_open_te_rec K t' C)
    (* boundary contexts *)
    | ctx_st C s => ctx_st (ctx_open_te_rec K t' C) s
    | ctx_ts C s m => ctx_ts (ctx_open_te_rec K t' C) s (open_te_rec (S K) t' m)
  end.

Definition t_ctx_open_ee C m := ctx_open_ee_rec false 0 m C.
Definition s_ctx_open_ee C m := ctx_open_ee_rec true 0 m C.
Definition ctx_open_te C t := ctx_open_te_rec 0 t C.
Definition t_ctx_open_ee_var C x := t_ctx_open_ee C (t_trm_fvar x).
Definition t_ctx_open_te_var C X := ctx_open_te C (t_typ_fvar X).
Definition s_ctx_open_ee_var C x := s_ctx_open_ee C (s_trm_fvar x).


(* Fill a context with a term *)
Fixpoint plug (C : ctx) (m : trm) : trm :=
  match C with
  | s_ctx_hole => m
  | s_ctx_if C' e1 e2 => s_trm_if (plug C' m) e1 e2
  | s_ctx_app1 C' e' => s_trm_app (plug C' m) e'
  | s_ctx_app2 v C' => s_trm_app v (plug C' m)
  | s_ctx_abs T C' => s_trm_abs T (plug C' m)
  | s_ctx_if_true e1 C' e3 => s_trm_if e1 (plug C' m) e3
  | s_ctx_if_false e1 e2 C' => s_trm_if e1 e2 (plug C' m)

  | t_ctx_hole => m
  | t_ctx_pair_left C' m1 => t_trm_pair (plug C' m) m1
  | t_ctx_pair_right m1 C' => t_trm_pair m1 (plug C' m)
  | t_ctx_abs t C' => t_trm_abs t (plug C' m)
  | t_ctx_if C' m1 m2 => t_trm_if (plug C' m) m1 m2
  | t_ctx_if_true m1 C' m2 => t_trm_if m1 (plug C' m) m2
  | t_ctx_if_false m1 m2 C' => t_trm_if m1 m2 (plug C' m)
  | t_ctx_let_pair1 C' m1 => t_trm_let_fst (plug C' m) m1
  | t_ctx_let_pair2 C' m1 => t_trm_let_snd (plug C' m) m1
  | t_ctx_let_exp1 m1 C' => t_trm_let_fst m1 (plug C' m)
  | t_ctx_let_exp2 m1 C' => t_trm_let_snd m1 (plug C' m)
  | t_ctx_app1 C' t m1 => t_trm_app (plug C' m) t m1
  | t_ctx_app2 m1 t C' => t_trm_app m1 t (plug C' m)

  | ctx_st C' s => trm_st (plug C' m) s
  | ctx_ts C' s m1 => trm_ts (plug C' m) s m1
  end.
(* end of contexts *)

(* TODO: Environments *)
(* TODO: Reduction rules *)
(* TODO: Equivalence *)
