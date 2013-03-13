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

(* contexts *)

Inductive ctx : Set :=
  (* evaluation and general contexts *)
  | ctx_hole : ctx
  | ctx_if : ctx -> trm -> trm -> ctx
  | ctx_app1 : ctx -> trm -> ctx
  | ctx_app2 : trm -> ctx -> ctx
  (* general contexts only *)
  | ctx_abs : type -> ctx -> ctx
  | ctx_if_true : trm -> ctx -> trm -> ctx
  | ctx_if_false : trm -> trm -> ctx -> ctx.

Fixpoint ctx_open_rec (k : nat) (f : trm) (C : ctx) {struct C} : ctx :=
  match C with
    | ctx_hole => ctx_hole
    | ctx_if C e2 e3 => ctx_if (ctx_open_rec k f C)
                               (open_rec k f e2)
                               (open_rec k f e3)
    | ctx_app1 C e => ctx_app1 (ctx_open_rec k f C) (open_rec k f e)
    | ctx_app2 e C => ctx_app2 (open_rec k f e) (ctx_open_rec k f C)
    | ctx_abs T C  => ctx_abs T (ctx_open_rec (S k) f C)
    | ctx_if_true e1 C e3 => ctx_if_true (open_rec k f e1)
                                         (ctx_open_rec k f C)
                                         (open_rec k f e3)
    | ctx_if_false e1 e2 C => ctx_if_false (open_rec k f e1)
                                           (open_rec k f e2)
                                           (ctx_open_rec k f C)
  end.

Definition ctx_open C e := ctx_open_rec 0 e C.
Definition ctx_open_var C x := ctx_open C (trm_fvar x).

Inductive eval_context : ctx -> Prop :=
  | eval_context_hole : eval_context ctx_hole
  | eval_context_if : forall E e1 e2,
      eval_context E -> term e1 -> term e2 -> eval_context (ctx_if E e1 e2)
  | eval_context_app1 : forall E e,
      eval_context E -> term e -> eval_context (ctx_app1 E e)
  | eval_context_app2 : forall v E,
      value v -> eval_context E -> eval_context (ctx_app2 v E).

Inductive context : ctx -> Prop :=
  | context_hole : context ctx_hole
  | context_if : forall C e1 e2,
      context C -> term e1 -> term e2 -> context (ctx_if C e1 e2)
  | context_app1 : forall C e,
      context C -> term e -> context (ctx_app1 C e)
  | context_app2 : forall v C,
      value v -> context C -> context (ctx_app2 v C)
  | context_abs : forall L T C,
      (forall x, x \notin L -> context (ctx_open_var C x)) ->
      context (ctx_abs T C)
  | context_if_true : forall e1 C e3,
      term e1 -> context C -> term e3 -> context (ctx_if_true e1 C e3)
  | context_if_false : forall e1 e2 C,
      term e1 -> term e2 -> context C -> context (ctx_if_false e1 e2 C).

Fixpoint plug (C : ctx) (e : trm) : trm :=
  match C with
  | ctx_hole => e
  | ctx_if C' e1 e2 => trm_if (plug C' e) e1 e2
  | ctx_app1 C' e' => trm_app (plug C' e) e'
  | ctx_app2 v C' => trm_app v (plug C' e)
  | ctx_abs T C' => trm_abs T (plug C' e)
  | ctx_if_true e1 C' e3 => trm_if e1 (plug C' e) e3
  | ctx_if_false e1 e2 C' => trm_if e1 e2 (plug C' e)
  end.

(* typing for contexts *)

Inductive context_typing : ctx -> env -> type -> env -> type -> Prop :=
  | context_typing_hole : forall G_hole T_hole G,
      ok G_hole -> ok G -> extends G_hole G ->
      context_typing ctx_hole G_hole T_hole G T_hole
  | context_typing_if : forall C G_hole T_hole G e2 e3 T,
      context_typing C G_hole T_hole G type_bool ->
      typing G e2 T -> typing G e3 T ->
      context_typing (ctx_if C e2 e3) G_hole T_hole G T
  | context_typing_app1 : forall C G_hole T_hole G e T T',
      context_typing C G_hole T_hole G (type_arrow T T') ->
      typing G e T ->
      context_typing (ctx_app1 C e) G_hole T_hole G T'
  | context_typing_app2 : forall C G_hole T_hole G e T T',
      typing G e (type_arrow T T') ->
      context_typing C G_hole T_hole G T ->
      context_typing (ctx_app2 e C) G_hole T_hole G T'
  | context_typing_abs : forall L C G_hole T_hole G T T',
      (forall x, x \notin L ->
        context_typing (ctx_open_var C x) G_hole T_hole (G & x ~ T) T') ->
      context_typing (ctx_abs T C) G_hole T_hole G (type_arrow T T')
  | context_typing_if_true : forall C G_hole T_hole G e1 e3 T,
      typing G e1 type_bool ->
      context_typing C G_hole T_hole G T ->
      typing G e3 T ->
      context_typing (ctx_if_true e1 C e3) G_hole T_hole G T
  | context_typing_if_false : forall C G_hole T_hole G e1 e2 T,
      typing G e1 type_bool -> typing G e2 T ->
      context_typing C G_hole T_hole G T ->
      context_typing (ctx_if_false e1 e2 C) G_hole T_hole G T.

(* reduction *)

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

Inductive red_star : trm -> trm -> Prop :=
  | red_refl : forall e, term e -> red_star e e
  | red_step : forall e1 e2 e3,
      red e1 e2 -> red_star e2 e3 -> red_star e1 e3.

Inductive eval : trm -> trm -> Prop :=
  | eval_red : forall e v,
      red_star e v -> value v -> eval e v.

(* contextual and ciu equivalence *)

