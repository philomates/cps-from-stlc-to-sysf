(***************************************************************************
* STLC (source language) definitions From Ahmed & Blume ICFP 2011          *
* William J. Bowman, Phillip Mates & James T. Perconti                     *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN.
Implicit Type x : var.
Implicit Type X : var.

(* ********************************************************************** *)
(** * Description of the Language *)

(** Representation of types *)

Inductive type : Set :=
  | type_bool : type
  | type_arrow : type -> type -> type.

(** Representation of pre-terms *)

Inductive trm : Set :=
  (* values *)
  | trm_bvar : nat -> trm
  | trm_fvar : var -> trm
  | trm_true : trm
  | trm_false : trm
  | trm_abs : type -> trm -> trm
  (* non-values *)
  | trm_if : trm -> trm -> trm -> trm
  | trm_app : trm -> trm -> trm.

Fixpoint open_rec (k : nat) (f : trm) (e : trm) {struct e} : trm :=
  match e with
    | trm_bvar i    => If k = i then f else (trm_bvar i)
    | trm_fvar x    => trm_fvar x
    | trm_true      => trm_true
    | trm_false     => trm_false
    | trm_abs t e1  => trm_abs t (open_rec (S k) f e1)
    | trm_if e1 e2 e3 => trm_if (open_rec k f e1)
                                (open_rec k f e2)
                                (open_rec k f e3)
    | trm_app e1 e2 => trm_app (open_rec k f e1) (open_rec k f e2)
  end.

Definition open t u := open_rec 0 u t.
Definition open_var e x := open e (trm_fvar x).

(* Terms as locally-closed pre-terms *)

Inductive term : trm -> Prop :=
  | term_value : forall v, value v -> term v
  | term_if : forall e1 e2 e3,
      term e1 -> term e2 -> term e3 ->
      term (trm_if e1 e2 e3)
  | term_app : forall e1 e2,
      term e1 -> term e2 ->
      term (trm_app e1 e2)

with value : trm -> Prop :=
  | value_var : forall x, value (trm_fvar x)
  | value_true : value trm_true
  | value_false : value trm_false
  | value_abs  : forall L T e,
      (forall x, x \notin L -> term (open_var e x)) ->
      value (trm_abs T e).

Scheme term_mut := Induction for term Sort Prop
with value_mut := Induction for value Sort Prop.

Definition env := LibEnv.env type.

Inductive typing : env -> trm -> type -> Prop :=
  | typing_var : forall G x T,
      ok G -> binds x T G -> typing G (trm_fvar x) T
  | typing_true : forall G,
      ok G -> typing G trm_true type_bool
  | typing_false : forall G,
      ok G -> typing G trm_false type_bool
  | typing_abs : forall L G e T1 T2,
      (forall x, x \notin L ->
        typing (G & x ~ T1) (open_var e x) T2) ->
      typing G (trm_abs T1 e) (type_arrow T1 T2)
  | typing_if : forall G e1 e2 e3 T,
      typing G e1 type_bool -> typing G e2 T -> typing G e3 T ->
      typing G (trm_if e1 e2 e3) T
  | typing_app : forall G e1 e2 T1 T2,
      typing G e1 (type_arrow T1 T2) -> typing G e2 T1 ->
      typing G (trm_app e1 e2) T2.

(* evaluation contexts *)

Inductive eval_ctx : Set :=
  | eval_ctx_hole : eval_ctx
  | eval_ctx_if : eval_ctx -> trm -> trm -> eval_ctx
  | eval_ctx_app1 : eval_ctx -> trm -> eval_ctx
  | eval_ctx_app2 : trm -> eval_ctx -> eval_ctx.

Inductive eval_context : eval_ctx -> Prop :=
  | eval_context_hole : eval_context eval_ctx_hole
  | eval_context_if : forall E e1 e2,
      eval_context E -> term e1 -> term e2 ->
      eval_context (eval_ctx_if E e1 e2)
  | eval_context_app1 : forall E e,
      eval_context E -> term e ->
      eval_context (eval_ctx_app1 E e)
  | eval_context_app2 : forall v E,
      value v -> eval_context E ->
      eval_context (eval_ctx_app2 v E).

Fixpoint plug (E : eval_ctx) (e : trm) : trm :=
  match E with
  | eval_ctx_hole => e
  | eval_ctx_if E' e1 e2 => trm_if (plug E' e) e1 e2
  | eval_ctx_app1 E' e' => trm_app (plug E' e) e'
  | eval_ctx_app2 v E' => trm_app v (plug E' e)
  end.

(* one-step reduction *)

Inductive red_base : trm -> trm -> Prop :=
  | red_if_true : forall e1 e2,
      term e1 -> term e2 ->
      red_base (trm_if trm_true e1 e2) e1
  | red_if_false : forall e1 e2,
      term e1 -> term e2 ->
      red_base (trm_if trm_false e1 e2) e2
  | red_app : forall e v T1,
      value (trm_abs T1 e) -> value v ->
      red_base (trm_app (trm_abs T1 e) v) (open e v).

Inductive red : trm -> trm -> Prop :=
  | red_ctx : forall E e e',
      red_base e e' -> eval_context E ->
      red (plug E e) (plug E e').
