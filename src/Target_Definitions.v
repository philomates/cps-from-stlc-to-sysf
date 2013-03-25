(***************************************************************************
* Preservation and Progress for CPS System-F - Definitions                 *
* Target language present in Ahmed & Blume ICFP 2011                       *
* William J. Bowman, Phillip Mates & James T. Perconti                     *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN.
Implicit Types x : var.
Implicit Types X : var.

(* ********************************************************************** *)
(** * Description of the Language *)

(** Representation of pre-types *)

Inductive typ : Set :=
  | typ_bool  : typ
  | typ_pair  : typ -> typ -> typ
  | typ_bvar  : nat -> typ
  | typ_fvar  : var -> typ
  (* forall . tau_1 -> tau_2; where alpha is 0 due to LN. *)
  | typ_arrow : typ -> typ -> typ.

(** Representation of pre-terms *)

Inductive trm : Set :=
  (* values *)
  | trm_bvar  : nat -> trm
  | trm_fvar  : var -> trm
  | trm_true  : trm
  | trm_false : trm
  | trm_pair  : trm -> trm -> trm
  | trm_abs   : typ -> trm -> trm
  (* non-values *)
  | trm_if    : trm -> trm -> trm -> trm
  (* let 0 be 1st proj of pair in body *)
  | trm_let_fst : trm -> trm -> trm
  (* let 0 be 2nd proj of pair in body *)
  | trm_let_snd : trm -> trm -> trm
  | trm_app   : trm -> typ -> trm -> trm.

(** Opening up a type binder occuring in a type *)

Fixpoint open_tt_rec (K : nat) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_bool        => typ_bool
  | typ_pair T1 T2  => typ_pair (open_tt_rec K U T1)
                                (open_tt_rec K U T2)
  | typ_bvar J      => If K = J then U else (typ_bvar J)
  | typ_fvar X      => typ_fvar X
  | typ_arrow T1 T2 => typ_arrow (open_tt_rec (S K) U T1) (open_tt_rec (S K) U T2)
  end.

Definition open_tt T U := open_tt_rec 0 U T.

(** Opening up a type binder occuring in a term *)

Fixpoint open_te_rec (K : nat) (U : typ) (e : trm) {struct e} : trm :=
  match e with
  | trm_bvar i    => trm_bvar i
  | trm_fvar x    => trm_fvar x
  | trm_true      => trm_true
  | trm_false     => trm_false
  | trm_pair v1 v2 => trm_pair  (open_te_rec K U v1)  (open_te_rec K U v2)
  | trm_abs t e1  => trm_abs  (open_tt_rec (S K) U t)  (open_te_rec (S K) U e1)
  | trm_if v e1 e2 => trm_if (open_te_rec K U v)
                             (open_te_rec K U e1)
                             (open_te_rec K U e2)
  | trm_let_fst v e => trm_let_fst (open_te_rec K U v)
                                   (open_te_rec K U e)
  | trm_let_snd v e => trm_let_snd (open_te_rec K U v)
                                   (open_te_rec K U e)
  | trm_app e1 t e2 => trm_app  (open_te_rec K U e1)
                                (open_tt_rec K U t)
                                (open_te_rec K U e2)
  end.

Definition open_te t U := open_te_rec 0 U t.

(** Opening up a term binder occuring in a term *)

Fixpoint open_ee_rec (k : nat) (f : trm) (e : trm) {struct e} : trm :=
  match e with
  | trm_bvar i    => If k = i then f else (trm_bvar i)
  | trm_fvar x    => trm_fvar x
  | trm_true      => trm_true
  | trm_false     => trm_false
  | trm_pair v1 v2 => trm_pair  (open_ee_rec k f v1)  (open_ee_rec k f v2)
  | trm_abs t e1  => trm_abs t (open_ee_rec (S k) f e1)
  | trm_if v e1 e2 => trm_if (open_ee_rec k f v)
                             (open_ee_rec k f e1)
                             (open_ee_rec k f e2)
  | trm_let_fst v e => trm_let_fst (open_ee_rec k f v)
                                   (open_ee_rec (S k) f e)
  | trm_let_snd v e => trm_let_snd (open_ee_rec k f v)
                                   (open_ee_rec (S k) f e)
  | trm_app e1 t e2 => trm_app  (open_ee_rec k f e1)
                                t
                                (open_ee_rec k f e2)
  end.

Definition open_ee t u := open_ee_rec 0 u t.

(** Notation for opening up binders with type or term variables *)

(* changing type vars in a term *)
Definition open_te_var e X := (open_te e (typ_fvar X)).
(* changing type vars in a type *)
Definition open_tt_var T X := (open_tt T (typ_fvar X)).
(* changing a term var in a term *)
Definition open_ee_var e x := (open_ee e (trm_fvar x)).

(** Types as locally closed pre-types *)

Inductive type : typ -> Prop :=
  | type_bool :
      type typ_bool
  | type_pair : forall T1 T2,
      type T1 -> type T2 -> type (typ_pair T1 T2)
  | type_var : forall X,
      type (typ_fvar X)
  | type_arrow : forall L T1 T2,
      (forall X, X \notin L ->
        type (open_tt_var T1 X)) ->
      (forall X, X \notin L -> type (open_tt_var T2 X)) ->
      type (typ_arrow T1 T2).

(** Terms as locally closed pre-terms *)

Inductive term : trm -> Prop :=
  | term_value : forall v, value v -> term v
  | term_if : forall v e1 e2,
      value v ->
      term e1 ->
      term e2 ->
      term (trm_if v e1 e2)
  | term_let_fst : forall L v e,
      value v ->
      (forall x, x \notin L -> term (open_ee_var e x)) ->
      term (trm_let_fst v e)
  | term_let_snd : forall L v e,
      value v ->
      (forall x, x \notin L -> term (open_ee_var e x)) ->
      term (trm_let_snd v e)
  | term_app : forall T v1 v2,
      value v1 ->
      type T ->
      value v2 ->
      term (trm_app v1 T v2)

with value : trm -> Prop :=
  | value_var : forall x,
      value (trm_fvar x)
  | value_true : value trm_true
  | value_false : value trm_false
  | value_pair : forall v1 v2,
      value v1 -> value v2 -> value (trm_pair v1 v2)
  | value_abs  : forall L T e1,
      (forall X, X \notin L ->
        type (open_tt_var T X)) ->
      (forall x X, x \notin L -> X \notin L ->
        term (open_te_var (open_ee_var e1 x) X)) ->
      value (trm_abs T e1).

Scheme term_mut := Induction for term Sort Prop
with value_mut := Induction for value Sort Prop.

(** Environment is an associative list of bindings. *)

Definition env_term := LibEnv.env typ.
Definition env_type := LibEnv.env unit.
Definition star := tt.        (* base kind: '*' *)

(** Well-formedness of a pre-type T in an environment E:
  all the type variables of T must be bound via a
  subtyping relation in E. This predicates implies
  that T is a type *)

(* Delta |- tau *)
Inductive wft : env_type -> typ -> Prop :=
  | wft_bool : forall D,
      wft D typ_bool
  | wft_pair : forall D T1 T2,
      wft D T1 ->
      wft D T2 ->
      wft D (typ_pair T1 T2)
  | wft_var : forall D X,
      binds X star D ->
      wft D (typ_fvar X)
  | wft_arrow : forall L D T1 T2,
      (forall X, X \notin L ->
        wft (D & X ~ star) (open_tt_var T1 X)) ->
      (forall X, X \notin L ->
        wft (D & X ~ star) (open_tt_var T2 X)) ->
      wft D (typ_arrow T1 T2).


(** A environment E is well-formed if it contains no duplicate bindings
  and if each type in it is well-formed with respect to the environment
  it is pushed on to. *)

(* Delta |- Gamma *)
Inductive okt : env_type -> env_term -> Prop :=
  | okt_empty : forall D,
      ok D ->
      okt D empty
  | okt_typ : forall D G x T,
      okt D G -> wft D T -> x # G -> okt D (G & x ~ T).

(** Typing relation *)
(* Delta;Gamma |- e:T *)
(* NOTE: Might need to enforce value restrictions
         we need to be able to prove: D G |- e : T -> term e *)
Inductive typing : env_type -> env_term -> trm -> typ -> Prop :=
  | typing_var : forall D G x T,
      okt D G ->
      binds x T G ->
      typing D G (trm_fvar x) T
  | typing_true : forall D G,
     okt D G ->
     typing D G trm_true typ_bool
  | typing_false : forall D G,
     okt D G ->
     typing D G trm_false typ_bool
  | typing_pair : forall D G v1 v2 T1 T2,
    typing D G v1 T1 ->
    typing D G v2 T2 ->
    typing D G (trm_pair v1 v2) (typ_pair T1 T2)
  | typing_abs : forall L D G e T1 T2,
      (forall x X, x \notin L -> X \notin L ->
        typing (D & X ~ star)
               (G & x ~ (open_tt_var T1 X))
               (open_te_var (open_ee_var e x) X)
               (open_tt_var T2 X)) ->
      typing D G (trm_abs T1 e) (typ_arrow T1 T2)
  | typing_if : forall D G v e1 e2 T,
    typing D G v typ_bool ->
    typing D G e1 T ->
    typing D G e2 T ->
    typing D G (trm_if v e1 e2) T
  | typing_let_fst : forall L D G v e T1 T2 T,
    typing D G v (typ_pair T1 T2) ->
    (forall x, x \notin L ->
      typing D (G & x ~ T1) (open_ee_var e x) T) ->
    typing D G (trm_let_fst v e) T
  | typing_let_snd : forall L D G v e T1 T2 T,
    typing D G v (typ_pair T1 T2) ->
    (forall x, x \notin L ->
      typing D (G & x ~ T2) (open_ee_var e x) T) ->
    typing D G (trm_let_snd v e) T
  | typing_app : forall D G v1 v2 T T1 T2,
      wft D T ->
      typing D G v1 (typ_arrow T1 T2) ->
      typing D G v2 (open_tt T1 T) ->
      typing D G (trm_app v1 T v2) (open_tt T2 T).

(* contexts *)

Inductive ctx : Set :=
  (* evaluation context: CPS makes this simple *)
  | ctx_hole : ctx
  (* value contexts *)
  | ctx_pair_left : ctx -> trm -> ctx
  | ctx_pair_right : trm -> ctx -> ctx
  | ctx_abs : typ -> ctx -> ctx
  (* general contexts *)
  | ctx_if : ctx -> trm -> trm -> ctx
  | ctx_if_true : trm -> ctx -> trm -> ctx
  | ctx_if_false : trm -> trm -> ctx -> ctx
  | ctx_let_pair1 : ctx -> trm -> ctx
  | ctx_let_pair2 : ctx -> trm -> ctx
  | ctx_let_exp1 : trm -> ctx -> ctx
  | ctx_let_exp2 : trm -> ctx -> ctx
  | ctx_app1 : ctx -> typ -> trm -> ctx
  | ctx_app2 : trm -> typ -> ctx -> ctx.

(* Opening of contexts *)
Fixpoint ctx_open_ee_rec (k : nat) (f : trm) (C : ctx) {struct C} : ctx :=
  match C with
    | ctx_hole => ctx_hole
    | ctx_pair_left C e => ctx_pair_left (ctx_open_ee_rec (S k) f C)
                                         (open_ee_rec k f e)
    | ctx_pair_right e C => ctx_pair_right (open_ee_rec k f e)
                                           (ctx_open_ee_rec (S k) f C)
    | ctx_abs T C  => ctx_abs T (ctx_open_ee_rec (S k) f C)
    | ctx_if C e1 e2 => ctx_if (ctx_open_ee_rec k f C)
                                 (open_ee_rec k f e1)
                                 (open_ee_rec k f e2)
    | ctx_if_true e1 C e2 => ctx_if_true (open_ee_rec k f e1)
                                 (ctx_open_ee_rec k f C)
                                 (open_ee_rec k f e2)
    | ctx_if_false e1 e2 C => ctx_if_false (open_ee_rec k f e1)
                                 (open_ee_rec k f e2)
                                 (ctx_open_ee_rec k f C)
    | ctx_let_pair1 C e => ctx_let_pair1 (ctx_open_ee_rec k f C)
                                         (open_ee_rec k f e)
    | ctx_let_pair2 C e => ctx_let_pair2 (ctx_open_ee_rec k f C)
                                         (open_ee_rec k f e)
    | ctx_let_exp1 e C => ctx_let_exp1 (open_ee_rec k f e)
                                       (ctx_open_ee_rec k f C)
    | ctx_let_exp2 e C => ctx_let_exp2 (open_ee_rec k f e)
                                       (ctx_open_ee_rec k f C)
    | ctx_app1 C T e => ctx_app1 (ctx_open_ee_rec k f C) T (open_ee_rec k f e)
    | ctx_app2 e T C => ctx_app2 (open_ee_rec k f e) T (ctx_open_ee_rec k f C)
  end.

Fixpoint ctx_open_te_rec (k : nat) (U : typ) (C : ctx) {struct C} : ctx :=
  match C with
    | ctx_hole => ctx_hole
    | ctx_pair_left C e => ctx_pair_left (ctx_open_te_rec (S k) U C)
                                         (open_te_rec k U e)
    | ctx_pair_right e C => ctx_pair_right (open_te_rec k U e)
                                           (ctx_open_te_rec (S k) U C)
    | ctx_abs T C  => ctx_abs (open_tt_rec (S k) U T) (ctx_open_te_rec (S k) U C)
    | ctx_if C e1 e2 => ctx_if (ctx_open_te_rec k U C)
                                 (open_te_rec k U e1)
                                 (open_te_rec k U e2)
    | ctx_if_true e1 C e2 => ctx_if_true (open_te_rec k U e1)
                                 (ctx_open_te_rec k U C)
                                 (open_te_rec k U e2)
    | ctx_if_false e1 e2 C => ctx_if_false (open_te_rec k U e1)
                                 (open_te_rec k U e2)
                                 (ctx_open_te_rec k U C)
    | ctx_let_pair1 C e => ctx_let_pair1 (ctx_open_te_rec k U C)
                                         (open_te_rec k U e)
    | ctx_let_pair2 C e => ctx_let_pair2 (ctx_open_te_rec k U C)
                                         (open_te_rec k U e)
    | ctx_let_exp1 e C => ctx_let_exp1 (open_te_rec k U e)
                                       (ctx_open_te_rec k U C)
    | ctx_let_exp2 e C => ctx_let_exp2 (open_te_rec k U e)
                                       (ctx_open_te_rec k U C)
    | ctx_app1 C T e => ctx_app1 (ctx_open_te_rec k U C)
                                 (open_tt_rec (S k) U T)
                                 (open_te_rec k U e)
    | ctx_app2 e T C => ctx_app2 (open_te_rec k U e)
                                 (open_tt_rec (S k) U T)
                                 (ctx_open_te_rec k U C)
  end.

Definition ctx_open_ee C e := ctx_open_ee_rec 0 e C.
Definition ctx_open_te C T := ctx_open_te_rec 0 T C.
Definition ctx_open_ee_var C x := ctx_open_ee C (trm_fvar x).
Definition ctx_open_te_var C X := ctx_open_te C (typ_fvar X).

(* CPS makes evaluation context of target lang simple *)
Inductive eval_context : ctx -> Prop :=
  | eval_context_hole : eval_context ctx_hole.

(* Well-formed context *)
Inductive context : ctx -> Prop :=
  | context_hole : context ctx_hole
  | context_pair_left : forall C v,
      context C -> value v -> context (ctx_pair_left C v)
  | context_pair_right : forall C v,
      value v -> context C -> context (ctx_pair_right v C)
  | context_abs : forall L T C,
      (forall X, X \notin L ->
        type (open_tt_var T X)) ->
      (forall x X, x \notin L -> X \notin L ->
        context (ctx_open_te_var (ctx_open_ee_var C x) X)) ->
      context (ctx_abs T C)
  | context_if : forall C e1 e2,
      context C -> term e1 -> term e2 -> context (ctx_if C e1 e2)
  | context_if_true : forall C e1 e2,
      context C -> term e1 -> term e2 -> context (ctx_if_true e1 C e2)
  | context_if_false : forall C e1 e2,
      context C -> term e1 -> term e2 -> context (ctx_if_false e1 e2 C)
  | context_let_pair1 : forall C e,
      context C -> term e -> context (ctx_let_pair1 C e)
  | context_let_pair2 : forall C e,
      context C -> term e -> context (ctx_let_pair2 C e)
  | context_let_exp1 : forall C v,
      context C -> value v -> context (ctx_let_exp1 v C)
  | context_let_exp2 : forall C v,
      context C -> value v -> context (ctx_let_exp2 v C)
  | context_app1 : forall C T v,
      context C -> type T -> value v -> context (ctx_app1 C T v)
  | context_app2 : forall C T v,
      context C -> type T -> value v -> context (ctx_app2 v T C).

(* Fill a context with a term *)
Fixpoint plug (C : ctx) (e : trm) : trm :=
  match C with
  | ctx_hole => e
  | ctx_pair_left C' e1 => trm_pair (plug C' e) e1
  | ctx_pair_right e1 C' => trm_pair e1 (plug C' e)
  | ctx_abs T C' => trm_abs T (plug C' e)
  | ctx_if C' e1 e2 => trm_if (plug C' e) e1 e2
  | ctx_if_true e1 C' e2 => trm_if e1 (plug C' e) e2
  | ctx_if_false e1 e2 C' => trm_if e1 e2 (plug C' e)
  | ctx_let_pair1 C' e1 => trm_let_fst (plug C' e) e1
  | ctx_let_pair2 C' e1 => trm_let_snd (plug C' e) e1
  | ctx_let_exp1 e1 C' => trm_let_fst e1 (plug C' e)
  | ctx_let_exp2 e1 C' => trm_let_snd e1 (plug C' e)
  | ctx_app1 C' T e1 => trm_app (plug C' e) T e1
  | ctx_app2 e1 T C' => trm_app e1 T (plug C' e)
  end.

(* typing for contexts *)
Inductive context_typing : ctx -> env_type -> env_term -> typ -> env_type -> env_term -> typ -> Prop :=
  | context_typing_hole : forall D_hole G_hole T_hole D G,
      okt D_hole G_hole -> okt D G -> extends G_hole G ->
      extends D_hole D ->
      context_typing ctx_hole D_hole G_hole T_hole D G T_hole
  | context_typing_pair_left : forall C D_hole G_hole T_hole D G v T1 T2,
      context_typing C D_hole G_hole T_hole D G T1 ->
      typing D G v T2 ->
      context_typing (ctx_pair_left C v) D_hole G_hole T_hole D G (typ_pair T1 T2)
  | context_typing_pair_right : forall C D_hole G_hole T_hole D G v T1 T2,
      context_typing C D_hole G_hole T_hole D G T2 ->
      typing D G v T1 ->
      context_typing (ctx_pair_right v C) D_hole G_hole T_hole D G
                     (typ_pair T1 T2)
  | context_typing_abs : forall L C D_hole G_hole T_hole D G T1 T2,
      (forall x X, x \notin L -> X \notin L ->
        context_typing (ctx_open_te_var (ctx_open_ee_var C x) X)
                       D_hole G_hole T_hole
                       (D & X ~ star) (G & x ~ (open_tt_var T1 X))
                       (open_tt_var T2 X)) ->
      context_typing (ctx_abs T1 C) D_hole G_hole T_hole D G (typ_arrow T1 T2)
  | context_typing_if : forall C D_hole G_hole T_hole D G e2 e3 T,
      context_typing C D_hole G_hole T_hole D G typ_bool ->
      typing D G e2 T -> typing D G e3 T ->
      context_typing (ctx_if C e2 e3) D_hole G_hole T_hole D G T
  | context_typing_if_true : forall C D_hole G_hole T_hole D G e1 e3 T,
      typing D G e1 typ_bool ->
      context_typing C D_hole G_hole T_hole D G T ->
      typing D G e3 T ->
      context_typing (ctx_if_true e1 C e3) D_hole G_hole T_hole D G T
  | context_typing_if_false : forall C D_hole G_hole T_hole D G e1 e2 T,
      typing D G e1 typ_bool -> typing D G e2 T ->
      context_typing C D_hole G_hole T_hole D G T ->
      context_typing (ctx_if_false e1 e2 C) D_hole G_hole T_hole D G T
  | context_typing_let_pair1 : forall L C D_hole G_hole T_hole D G e T1 T2 T,
      context_typing C D_hole G_hole T_hole D G (typ_pair T1 T2) ->
      (forall x, x \notin L ->
        typing D (G & x ~ T1) (open_ee_var e x) T) ->
      context_typing (ctx_let_pair1 C e) D_hole G_hole T_hole D G T
  | context_typing_let_pair2 : forall L C D_hole G_hole T_hole D G e T1 T2 T,
      context_typing C D_hole G_hole T_hole D G (typ_pair T1 T2) ->
      (forall x, x \notin L ->
        typing D (G & x ~ T2) (open_ee_var e x) T) ->
      context_typing (ctx_let_pair2 C e) D_hole G_hole T_hole D G T
  | context_typing_let_exp1 : forall L C D_hole G_hole T_hole D G v T1 T2 T,
      typing D G v (typ_pair T1 T2) ->
      (forall x, x \notin L ->
        context_typing C D_hole G_hole T_hole D (G & x ~ T1) T) ->
      context_typing (ctx_let_exp1 v C) D_hole G_hole T_hole D G T
  | context_typing_let_exp2 : forall L C D_hole G_hole T_hole D G v T1 T2 T,
      typing D G v (typ_pair T1 T2) ->
      (forall x, x \notin L ->
        context_typing C D_hole G_hole T_hole D (G & x ~ T2) T) ->
      context_typing (ctx_let_exp2 v C) D_hole G_hole T_hole D G T
  | context_typing_app1 : forall C D_hole G_hole T_hole D G v T T1 T2,
      context_typing C D_hole G_hole T_hole D G (typ_arrow T1 T2) ->
      wft D T ->
      typing D G v (open_tt T1 T) ->
      context_typing (ctx_app1 C T v) D_hole G_hole T_hole D G (open_tt T2 T)
  | context_typing_app2 : forall C D_hole G_hole T_hole D G v T T1 T2,
      wft D T ->
      typing D G v (typ_arrow T1 T2) ->
      context_typing C D_hole G_hole T_hole D G (open_tt T1 T) ->
      context_typing (ctx_app2 v T C) D_hole G_hole T_hole D G T2.

(** reduction *)

(** one step *)
Inductive red_base : trm -> trm -> Prop :=
  | red_if_true : forall e1 e2,
    term e1 ->
    term e2 ->
    red_base (trm_if trm_true e1 e2) e1
  | red_if_false : forall e1 e2,
    term e1 ->
    term e2 ->
    red_base (trm_if trm_false e1 e2) e2
  | red_let_fst : forall e v1 v2,
    term e ->
    value v1 ->
    value v2 ->
    red_base (trm_let_fst (trm_pair v1 v2) e) (open_ee e v1)
  | red_let_snd : forall e v1 v2,
    term e ->
    value v1 ->
    value v2 ->
    red_base (trm_let_snd (trm_pair v1 v2) e) (open_ee e v2)
  | red_app : forall e v T1 T,
    value v ->
    type T ->
    value (trm_abs T1 e) ->
    red_base (trm_app (trm_abs T1 e) T v) (open_te (open_ee e v) T).

(** context step *)
Inductive red : trm -> trm -> Prop :=
  | red_ctx : forall E e e',
      red_base e e' -> eval_context E ->
      red (plug E e) (plug E e').

(** multi-step step *)
Inductive red_star : trm -> trm -> Prop :=
  | red_refl : forall e, term e -> red_star e e
  | red_step : forall e1 e2 e3,
      red e1 e2 -> red_star e2 e3 -> red_star e1 e3.

Inductive eval : trm -> trm -> Prop :=
  | eval_red : forall e v,
      red_star e v -> value v -> eval e v.

(* contextual equivalence *)
Definition ctx_approx (D : env_type) (G : env_term) (e1 e2 : trm) (T : typ) :=
  typing D G e1 T /\ typing D G e2 T /\
  forall C v,
    context_typing C D G T empty empty typ_bool ->
    eval (plug C e1) v ->
    eval (plug C e2) v.

Definition ctx_equiv (D : env_type) (G : env_term) (e1 e2 : trm) (T : typ) :=
  ctx_approx D G e1 e2 T /\ ctx_approx D G e2 e1 T.

(* CIU equivalence *)

Definition term_substitution := LibEnv.env trm.
Definition type_substitution := LibEnv.env typ.

Definition term_subst_satisfies g G :=
  forall x v T, binds x v g -> value v /\ binds x T G /\ typing empty empty v T.

Definition type_subst_satisfies d D := forall X t T,
  binds X t d -> type t /\ binds T star D.

(* Use type and term (delta and gamma) substitions to close of open terms *)
Fixpoint apply_type_subst (d : type_substitution) (t : typ) :=
  match t with
  | typ_bool        => typ_bool
  | typ_pair T1 T2  => typ_pair (apply_type_subst d T1)
                                (apply_type_subst d T2)
  | typ_bvar J      => t
  | typ_fvar X      => match get X d with
                       | None => typ_fvar X
                       | Some v => v end
  | typ_arrow T1 T2 => typ_arrow (apply_type_subst d T1) (apply_type_subst d T2)
  end.

Fixpoint apply_term_subst (d : type_substitution)
                          (g : term_substitution) (e : trm) :=
  match e with
  | trm_bvar n => trm_bvar n
  | trm_fvar x => match get x g with None => trm_fvar x
                    | Some v => v end
  | trm_true => trm_true
  | trm_false => trm_false
  | trm_pair v1 v2 => trm_pair (apply_term_subst d g v1) (apply_term_subst d g v2)
  | trm_abs t e1  => trm_abs (apply_type_subst d t) (apply_term_subst d g e1)
  | trm_if v e1 e2 => trm_if (apply_term_subst d g v)
                             (apply_term_subst d g e1)
                             (apply_term_subst d g e2)
  | trm_let_fst v e => trm_let_fst (apply_term_subst d g v)
                                   (apply_term_subst d g e)
  | trm_let_snd v e => trm_let_snd (apply_term_subst d g v)
                                   (apply_term_subst d g e)
  | trm_app e1 t e2 => trm_app (apply_term_subst d g e1)
                               (apply_type_subst d t)
                               (apply_term_subst d g e2)
  end.

Definition ciu_approx (D : env_type) (G : env_term) (e1 e2 : trm) (T : typ) :=
  typing D G e1 T /\ typing D G e2 T /\
  forall E d g v,
    eval_context E -> context_typing E empty empty T empty empty typ_bool ->
    type_subst_satisfies d D ->
    term_subst_satisfies g G ->
    eval (plug E (apply_term_subst d g e1)) v ->
    eval (plug E (apply_term_subst d g e2)) v.

(** We'll Eventually prove preservation and progress *)
Definition preservation := forall D G e e' T,
  typing D G e T ->
  red e e' ->
  typing D G e' T.

Definition progress := forall e T,
  typing empty empty e T ->
     value e
  \/ exists e', red e e'.

