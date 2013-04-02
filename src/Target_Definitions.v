(***************************************************************************
* Preservation and Progress for CPS System-F - Definitions                 *
* Target language present in Ahmed & Blume ICFP 2011                       *
* William J. Bowman, Phillip Mates & James t. Perconti                     *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN Core_Definitions.
Implicit Types x : var.
Implicit Types X : var.

(* ********************************************************************** *)
(** * Description of the Language *)

(** Terms as locally closed pre-terms *)
Inductive t_term : trm -> Prop :=
  | t_term_value : forall u, t_value u -> t_term u
  | t_term_if : forall u m1 m2,
      t_value u ->
      t_term m1 ->
      t_term m2 ->
      t_term (t_trm_if u m1 m2)
  | t_term_let_fst : forall L u m,
      t_value u ->
      (forall x, x \notin L -> t_term (t_open_ee_var m x)) ->
      t_term (t_trm_let_fst u m)
  | t_term_let_snd : forall L u m,
      t_value u ->
      (forall x, x \notin L -> t_term (t_open_ee_var m x)) ->
      t_term (t_trm_let_snd u m)
  | t_term_app : forall t v1 v2,
      t_value v1 ->
      t_type t ->
      t_value v2 ->
      t_term (t_trm_app v1 t v2)

with t_value : trm -> Prop :=
  | t_value_var : forall x,
      t_value (t_trm_fvar x)
  | t_value_true : t_value t_trm_true
  | t_value_false : t_value t_trm_false
  | t_value_pair : forall v1 v2,
      t_value v1 -> t_value v2 -> t_value (t_trm_pair v1 v2)
  | t_value_abs  : forall L t m1,
      (forall X, X \notin L ->
        t_type (t_open_tt_var t X)) ->
      (forall x X, x \notin L -> X \notin L ->
        t_term (t_open_te_var (t_open_ee_var m1 x) X)) ->
      t_value (t_trm_abs t m1).

Scheme t_term_mut := Induction for t_term Sort Prop
with t_value_mut := Induction for t_value Sort Prop.

(** Environment is an associative list of bindings. *)

Definition env_term := LibEnv.env typ.
Definition env_type := LibEnv.env unit.
Definition star := tt.        (* base kind: '*' *)

(** Well-formedness of a pre-type t in an environment E:
  all the type variables of t must be bound via a
  subtyping relation in E. This predicates implies
  that t is a type *)

(* Delta |- tau *)
Inductive wft : env_type -> typ -> Prop :=
  | wft_bool : forall D,
      wft D t_typ_bool
  | wft_pair : forall D t1 t2,
      wft D t1 ->
      wft D t2 ->
      wft D (t_typ_pair t1 t2)
  | wft_var : forall D X,
      binds X star D ->
      wft D (t_typ_fvar X)
  | wft_arrow : forall L D t1 t2,
      (forall X, X \notin L ->
        wft (D & X ~ star) (t_open_tt_var t1 X)) ->
      (forall X, X \notin L ->
        wft (D & X ~ star) (t_open_tt_var t2 X)) ->
      wft D (t_typ_arrow t1 t2).


(** A environment E is well-formed if it contains no duplicate bindings
  and if each type in it is well-formed with respect to the environment
  it is pushed on to. *)

(* Delta |- Gamma *)
Inductive okt : env_type -> env_term -> Prop :=
  | okt_empty : forall D,
      ok D ->
      okt D empty
  | okt_typ : forall D G x t,
      okt D G -> wft D t -> x # G -> okt D (G & x ~ t).

(** Typing relation *)
(* Delta;Gamma |- m:t *)
(* NOTE: Might need to enforce value restrictions
         we need to be able to prove: D G |- m : t -> term m *)
Inductive t_typing : env_type -> env_term -> trm -> typ -> Prop :=
  | t_typing_var : forall D G x t,
      okt D G ->
      binds x t G ->
      t_typing D G (t_trm_fvar x) t
  | t_typing_true : forall D G,
     okt D G ->
     t_typing D G t_trm_true t_typ_bool
  | t_typing_false : forall D G,
     okt D G ->
     t_typing D G t_trm_false t_typ_bool
  | t_typing_pair : forall D G u1 u2 t1 t2,
    t_typing D G u1 t1 ->
    t_typing D G u2 t2 ->
    t_value u1 ->
    t_value u2 ->
    t_typing D G (t_trm_pair u1 u2) (t_typ_pair t1 t2)
  | t_typing_abs : forall L D G m t1 t2,
      (forall x X, x \notin L -> X \notin L ->
        t_typing (D & X ~ star)
               (G & x ~ (t_open_tt_var t1 X))
               (t_open_te_var (t_open_ee_var m x) X)
               (t_open_tt_var t2 X)) ->
      t_typing D G (t_trm_abs t1 m) (t_typ_arrow t1 t2)
  | t_typing_if : forall D G u m1 m2 t,
    t_typing D G u t_typ_bool ->
    t_typing D G m1 t ->
    t_typing D G m2 t ->
    t_typing D G (t_trm_if u m1 m2) t
  | t_typing_let_fst : forall L D G u m t1 t2 t,
    t_typing D G u (t_typ_pair t1 t2) ->
    (forall x, x \notin L ->
      t_typing D (G & x ~ t1) (t_open_ee_var m x) t) ->
    t_typing D G (t_trm_let_fst u m) t
  | t_typing_let_snd : forall L D G u m t1 t2 t,
    t_typing D G u (t_typ_pair t1 t2) ->
    (forall x, x \notin L ->
      t_typing D (G & x ~ t2) (t_open_ee_var m x) t) ->
    t_typing D G (t_trm_let_snd u m) t
  | t_typing_app : forall D G u1 u2 t t1 t2,
      wft D t ->
      t_typing D G u1 (t_typ_arrow t1 t2) ->
      t_typing D G u2 (open_tt t1 t) ->
      t_typing D G (t_trm_app u1 t u2) (open_tt t2 t).

(* CPS makes evaluation context of target lang simple *)
Inductive t_eval_context : ctx -> Prop :=
  | t_eval_context_hole : t_eval_context t_ctx_hole.

(* Well-formed context *)
Inductive t_context : ctx -> Prop :=
  | t_context_hole : t_context t_ctx_hole
  | t_context_pair_left : forall C u,
      t_context C -> t_value u -> t_context (t_ctx_pair_left C u)
  | t_context_pair_right : forall C u,
      t_value u -> t_context C -> t_context (t_ctx_pair_right u C)
  | t_context_abs : forall L t C,
      (forall X, X \notin L ->
        t_type (t_open_tt_var t X)) ->
      (forall x X, x \notin L -> X \notin L ->
        t_context (t_ctx_open_te_var (t_ctx_open_ee_var C x) X)) ->
      t_context (t_ctx_abs t C)
  | t_context_if : forall C m1 m2,
      t_context C -> t_term m1 -> t_term m2 -> t_context (t_ctx_if C m1 m2)
  | t_context_if_true : forall C m1 m2,
      t_context C -> t_term m1 -> t_term m2 -> t_context (t_ctx_if_true m1 C m2)
  | t_context_if_false : forall C m1 m2,
      t_context C -> t_term m1 -> t_term m2 -> t_context (t_ctx_if_false m1 m2 C)
  | t_context_let_pair1 : forall C m,
      t_context C -> t_term m -> t_context (t_ctx_let_pair1 C m)
  | t_context_let_pair2 : forall C m,
      t_context C -> t_term m -> t_context (t_ctx_let_pair2 C m)
  | t_context_let_exp1 : forall C u,
      t_context C -> t_value u -> t_context (t_ctx_let_exp1 u C)
  | t_context_let_exp2 : forall C u,
      t_context C -> t_value u -> t_context (t_ctx_let_exp2 u C)
  | t_context_app1 : forall C t u,
      t_context C -> t_type t -> t_value u -> t_context (t_ctx_app1 C t u)
  | t_context_app2 : forall C t u,
      t_context C -> t_type t -> t_value u -> t_context (t_ctx_app2 u t C).

(* typing for contexts *)
Inductive t_context_typing : ctx -> env_type -> env_term -> typ -> env_type -> env_term -> typ -> Prop :=
  | t_context_typing_hole : forall D_hole G_hole T_hole D G,
      okt D_hole G_hole -> okt D G -> extends G_hole G ->
      extends D_hole D ->
      t_context_typing t_ctx_hole D_hole G_hole T_hole D G T_hole
  | t_context_typing_pair_left : forall C D_hole G_hole T_hole D G u t1 t2,
      t_context_typing C D_hole G_hole T_hole D G t1 ->
      t_typing D G u t2 ->
      t_context_typing (t_ctx_pair_left C u) D_hole G_hole T_hole D G (t_typ_pair t1 t2)
  | t_context_typing_pair_right : forall C D_hole G_hole T_hole D G u t1 t2,
      t_context_typing C D_hole G_hole T_hole D G t2 ->
      t_typing D G u t1 ->
      t_context_typing (t_ctx_pair_right u C) D_hole G_hole T_hole D G
                     (t_typ_pair t1 t2)
  | t_context_typing_abs : forall L C D_hole G_hole T_hole D G t1 t2,
      (forall x X, x \notin L -> X \notin L ->
        t_context_typing (t_ctx_open_te_var (t_ctx_open_ee_var C x) X)
                       D_hole G_hole T_hole
                       (D & X ~ star) (G & x ~ (t_open_tt_var t1 X))
                       (t_open_tt_var t2 X)) ->
      t_context_typing (t_ctx_abs t1 C) D_hole G_hole T_hole D G (t_typ_arrow t1 t2)
  | t_context_typing_if : forall C D_hole G_hole T_hole D G m2 e3 t,
      t_context_typing C D_hole G_hole T_hole D G t_typ_bool ->
      t_typing D G m2 t -> t_typing D G e3 t ->
      t_context_typing (t_ctx_if C m2 e3) D_hole G_hole T_hole D G t
  | t_context_typing_if_true : forall C D_hole G_hole T_hole D G m1 e3 t,
      t_typing D G m1 t_typ_bool ->
      t_context_typing C D_hole G_hole T_hole D G t ->
      t_typing D G e3 t ->
      t_context_typing (t_ctx_if_true m1 C e3) D_hole G_hole T_hole D G t
  | t_context_typing_if_false : forall C D_hole G_hole T_hole D G m1 m2 t,
      t_typing D G m1 t_typ_bool -> t_typing D G m2 t ->
      t_context_typing C D_hole G_hole T_hole D G t ->
      t_context_typing (t_ctx_if_false m1 m2 C) D_hole G_hole T_hole D G t
  | t_context_typing_let_pair1 : forall L C D_hole G_hole T_hole D G m t1 t2 t,
      t_context_typing C D_hole G_hole T_hole D G (t_typ_pair t1 t2) ->
      (forall x, x \notin L ->
        t_typing D (G & x ~ t1) (t_open_ee_var m x) t) ->
      t_context_typing (t_ctx_let_pair1 C m) D_hole G_hole T_hole D G t
  | t_context_typing_let_pair2 : forall L C D_hole G_hole T_hole D G m t1 t2 t,
      t_context_typing C D_hole G_hole T_hole D G (t_typ_pair t1 t2) ->
      (forall x, x \notin L ->
        t_typing D (G & x ~ t2) (t_open_ee_var m x) t) ->
      t_context_typing (t_ctx_let_pair2 C m) D_hole G_hole T_hole D G t
  | t_context_typing_let_exp1 : forall L C D_hole G_hole T_hole D G u t1 t2 t,
      t_typing D G u (t_typ_pair t1 t2) ->
      (forall x, x \notin L ->
        t_context_typing C D_hole G_hole T_hole D (G & x ~ t1) t) ->
      t_context_typing (t_ctx_let_exp1 u C) D_hole G_hole T_hole D G t
  | t_context_typing_let_exp2 : forall L C D_hole G_hole T_hole D G u t1 t2 t,
      t_typing D G u (t_typ_pair t1 t2) ->
      (forall x, x \notin L ->
        t_context_typing C D_hole G_hole T_hole D (G & x ~ t2) t) ->
      t_context_typing (t_ctx_let_exp2 u C) D_hole G_hole T_hole D G t
  | t_context_typing_app1 : forall C D_hole G_hole T_hole D G u t t1 t2,
      t_context_typing C D_hole G_hole T_hole D G (t_typ_arrow t1 t2) ->
      wft D t ->
      t_typing D G u (open_tt t1 t) ->
      t_context_typing (t_ctx_app1 C t u) D_hole G_hole T_hole D G (open_tt t2 t)
  | t_context_typing_app2 : forall C D_hole G_hole T_hole D G u t t1 t2,
      wft D t ->
      t_typing D G u (t_typ_arrow t1 t2) ->
      t_context_typing C D_hole G_hole T_hole D G (open_tt t1 t) ->
      t_context_typing (t_ctx_app2 u t C) D_hole G_hole T_hole D G t2.

(** reduction *)

(** one step *)
Inductive red_base : trm -> trm -> Prop :=
  | red_if_true : forall m1 m2,
    term m1 ->
    term m2 ->
    red_base (trm_if trm_true m1 m2) m1
  | red_if_false : forall m1 m2,
    term m1 ->
    term m2 ->
    red_base (trm_if trm_false m1 m2) m2
  | red_let_fst : forall m v1 v2,
    term m ->
    value v1 ->
    value v2 ->
    red_base (trm_let_fst (trm_pair v1 v2) m) (open_ee m v1)
  | red_let_snd : forall m v1 v2,
    term m ->
    value v1 ->
    value v2 ->
    red_base (trm_let_snd (trm_pair v1 v2) m) (open_ee m v2)
  | red_app : forall m u t1 t,
    value u ->
    type t ->
    value (trm_abs t1 m) ->
    red_base (trm_app (trm_abs t1 m) t u) (open_te (open_ee m u) t).

(** context step *)
Inductive red : trm -> trm -> Prop :=
  | red_ctx : forall E m m',
      red_base m m' -> eval_context E ->
      red (plug E m) (plug E m').

(** multi-step step *)
Inductive red_star : trm -> trm -> Prop :=
  | red_refl : forall m, term m -> red_star m m
  | red_step : forall m1 m2 e3,
      red m1 m2 -> red_star m2 e3 -> red_star m1 e3.

Inductive eval : trm -> trm -> Prop :=
  | eval_red : forall m u,
      red_star m u -> value u -> eval m u.

(* contextual equivalence *)
Definition ctx_approx (D : env_type) (G : env_term) (m1 m2 : trm) (t : typ) :=
  typing D G m1 t /\ typing D G m2 t /\
  forall C u,
    context_typing C D G t empty empty t_typ_bool ->
    eval (plug C m1) u ->
    eval (plug C m2) u.

Definition ctx_equiv (D : env_type) (G : env_term) (m1 m2 : trm) (t : typ) :=
  ctx_approx D G m1 m2 t /\ ctx_approx D G m2 m1 t.

(* CIU equivalence *)

Definition term_substitution := LibEnv.env trm.
Definition type_substitution := LibEnv.env typ.

Definition term_subst_satisfies g G :=
  forall x u t, binds x u g -> value u /\ binds x t G /\ typing empty empty u t.

Definition type_subst_satisfies d D := forall X t t,
  binds X t d -> type t /\ binds t star D.

(* Use type and term (delta and gamma) substitions to close of open terms *)
Fixpoint apply_type_subst (d : type_substitution) (t : typ) :=
  match t with
  | t_typ_bool        => t_typ_bool
  | t_typ_pair t1 t2  => t_typ_pair (apply_type_subst d t1)
                                (apply_type_subst d t2)
  | t_typ_bvar J      => t
  | t_typ_fvar X      => match get X d with
                       | None => t_typ_fvar X
                       | Some u => u end
  | t_typ_arrow t1 t2 => t_typ_arrow (apply_type_subst d t1) (apply_type_subst d t2)
  end.

Fixpoint apply_term_subst (d : type_substitution)
                          (g : term_substitution) (m : trm) :=
  match m with
  | trm_bvar n => trm_bvar n
  | trm_fvar x => match get x g with None => trm_fvar x
                    | Some u => u end
  | trm_true => trm_true
  | trm_false => trm_false
  | trm_pair v1 v2 => trm_pair (apply_term_subst d g v1) (apply_term_subst d g v2)
  | trm_abs t m1  => trm_abs (apply_type_subst d t) (apply_term_subst d g m1)
  | trm_if u m1 m2 => trm_if (apply_term_subst d g u)
                             (apply_term_subst d g m1)
                             (apply_term_subst d g m2)
  | trm_let_fst u m => trm_let_fst (apply_term_subst d g u)
                                   (apply_term_subst d g m)
  | trm_let_snd u m => trm_let_snd (apply_term_subst d g u)
                                   (apply_term_subst d g m)
  | trm_app m1 t m2 => trm_app (apply_term_subst d g m1)
                               (apply_type_subst d t)
                               (apply_term_subst d g m2)
  end.

Definition ciu_approx (D : env_type) (G : env_term) (m1 m2 : trm) (t : typ) :=
  typing D G m1 t /\ typing D G m2 t /\
  forall E d g u,
    eval_context E -> context_typing E empty empty t empty empty t_typ_bool ->
    type_subst_satisfies d D ->
    term_subst_satisfies g G ->
    eval (plug E (apply_term_subst d g m1)) u ->
    eval (plug E (apply_term_subst d g m2)) u.

(** We'll Eventually prove preservation and progress *)
Definition preservation := forall D G m m' t,
  typing D G m t ->
  red m m' ->
  typing D G m' t.

Definition progress := forall m t,
  typing empty empty m t ->
     value m
  \/ exists m', red m m'.
