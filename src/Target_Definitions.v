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
      (forall x X, x \notin L -> X \notin L ->
        type (open_tt_var T X) /\ term (open_te_var (open_ee_var e1 x) X)) ->
      value (trm_abs T e1).

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
        wft (D & X ~ star) (open_tt_var T1 X) /\
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

(** One-step reduction *)

Inductive red : trm -> trm -> Prop :=
  | red_if_true : forall e1 e2,
    term e1 ->
    term e2 ->
    red (trm_if trm_true e1 e2) e1
  | red_if_false : forall e1 e2,
    term e1 ->
    term e2 ->
    red (trm_if trm_false e1 e2) e2
  | red_let_fst : forall e v1 v2,
    term e ->
    value v1 ->
    value v2 ->
    red (trm_let_fst (trm_pair v1 v2) e) (open_ee e v1)
  | red_let_snd : forall e v1 v2,
    term e ->
    value v1 ->
    value v2 ->
    red (trm_let_snd (trm_pair v1 v2) e) (open_ee e v2)
  | red_app : forall e v T1 T,
    value v ->
    type T ->
    value (trm_abs T1 e) ->
    red (trm_app (trm_abs T1 e) T v) (open_te (open_ee e v) T).

(** Our goal is to prove preservation and progress *)

Definition preservation := forall D G e e' T,
  typing D G e T ->
  red e e' ->
  typing D G e' T.

Definition progress := forall e T,
  typing empty empty e T ->
     value e
  \/ exists e', red e e'.

