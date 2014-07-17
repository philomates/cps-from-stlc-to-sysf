(***************************************************************************
* Target language definitions From Ahmed +&+ Blume ICFP 2011                 *
* William J. Bowman, Phillip Mates +&+ James T. Perconti                     *
***************************************************************************)

Require Import Core_Definitions LibWfenv Core_Infrastructure.
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq path Eqdep.

(* ********************************************************************** *)

(* Locally-closed types and terms  *)

(* Target Types *)

Inductive t_type (t : typ) : Prop :=
| t_type_var x of t = t_typ_fvar x -> t_type t
| t_type_bool
| t_type_pair : forall t1 t2, t_type t1 -> t_type t2 -> 
                  t = t_typ_pair t1 t2 -> t_type t
| t_type_arrow : forall (L : vars) t1 t2,
     (forall X, X \notinLN L -> t_type (open_tt_var t1 X)) ->
     (forall X, X \notinLN L -> t_type (open_tt_var t2 X)) ->
     t = t_typ_arrow t1 t2 -> t_type t.

(*
Inductive t_type : typ -> Prop :=
  | t_type_var : forall x, t_type (t_typ_fvar x)
  | t_type_bool : t_type t_typ_bool
  | t_type_pair : forall t1 t2,
      t_type t1 -> t_type t2 -> t_type (t_typ_pair t1 t2)
  | t_type_arrow : forall L t1 t2,
      (forall X, X \notinLN L -> t_type (open_tt_var t1 X)) ->
      (forall X, X \notinLN L -> t_type (open_tt_var t2 X)) ->
      t_type (t_typ_arrow t1 t2).
*)





Fixpoint t_typeb (t : typ) : bool :=
  match t with
    t_typ_fvar x => true
  | t_typ_bool  => true
  | t_typ_pair t1 t2 => t_typeb t1 && t_typeb t2
  | t_typ_arrow t1 t2 => t_typeb t1 && t_typeb t2
  | _ => false
  end.


(* Target Terms *)

Inductive t_term : trm -> Prop :=
  | t_term_value : forall u, t_value u -> t_term u
  | t_term_if : forall u m1 m2,
      t_value u -> t_term m1 -> t_term m2 -> t_term (t_trm_if u m1 m2)
  | t_term_let_fst : forall L u m,
      t_value u ->
      (forall x, x \notinLN L -> t_term (t_open_ee_var m x)) ->
      t_term (t_trm_let_fst u m)
  | t_term_let_snd : forall L u m,
      t_value u ->
      (forall x, x \notinLN L -> t_term (t_open_ee_var m x)) ->
      t_term (t_trm_let_snd u m)
  | t_term_app : forall u1 t u2,
      t_value u1 -> t_type t -> t_value u2 -> t_term (t_trm_app u1 t u2)

with t_value : trm -> Prop :=
  | t_value_var : forall x, t_value (t_trm_fvar x)
  | t_value_true : t_value t_trm_true
  | t_value_false : t_value t_trm_false
  | t_value_pair : forall u1 u2,
      t_value u1 -> t_value u2 -> t_value (t_trm_pair u1 u2)
  | t_value_abs  : forall L t m,
      (forall X, X \notinLN L -> t_type (open_tt_var t X)) ->
      (forall x X, x \notinLN L -> X \notinLN L ->
        t_term (open_te_var (t_open_ee_var m x) X)) ->
      t_value (t_trm_abs t m).

Scheme t_term_mut := Induction for t_term Sort Prop
with t_value_mut := Induction for t_value Sort Prop.

Hint Constructors t_term t_value.

(* Type System *)

(* Delta |- tau *)
Inductive t_wft : env_type -> typ -> Prop :=
  | t_wft_var : forall D X, ok D -> binds X star D -> t_wft D (t_typ_fvar X)
  | t_wft_bool : forall D, ok D -> t_wft D t_typ_bool
  | t_wft_pair : forall D t1 t2,
      t_wft D t1 -> t_wft D t2 -> t_wft D (t_typ_pair t1 t2)
  | t_wft_arrow : forall L D t1 t2,
      (forall X, X \notinLN L -> t_wft (D +&+ X ~ star) (open_tt_var t1 X)) ->
      (forall X, X \notinLN L -> t_wft (D +&+ X ~ star) (open_tt_var t2 X)) ->
      t_wft D (t_typ_arrow t1 t2).

Hint Constructors t_wft.

(** Typing relation *)
(* Delta;Gamma |- m:t *)
Inductive t_typing : env_type -> env_term -> trm -> typ -> Prop :=
  | t_typing_value : forall D G u t,
      t_value_typing D G u t -> t_typing D G u t
  | t_typing_if : forall D G u m1 m2 t,
      t_value_typing D G u t_typ_bool ->
      t_typing D G m1 t -> t_typing D G m2 t ->
      t_typing D G (t_trm_if u m1 m2) t
  | t_typing_let_fst : forall L D G u m t1 t2 t,
      t_value_typing D G u (t_typ_pair t1 t2) ->
      (forall x, x \notinLN L -> t_typing D (G +&+ x ~ t1) (t_open_ee_var m x) t) ->
      t_typing D G (t_trm_let_fst u m) t
  | t_typing_let_snd : forall L D G u m t1 t2 t,
      t_value_typing D G u (t_typ_pair t1 t2) ->
      (forall x, x \notinLN L -> t_typing D (G +&+ x ~ t2) (t_open_ee_var m x) t) ->
      t_typing D G (t_trm_let_snd u m) t
  | t_typing_app : forall D G u1 u2 t t1 t2,
      t_value_typing D G u1 (t_typ_arrow t1 t2) ->
      t_wft D t ->
      t_value_typing D G u2 (open_tt t1 t) ->
      t_typing D G (t_trm_app u1 t u2) (open_tt t2 t)

with t_value_typing : env_type -> env_term -> trm -> typ -> Prop :=
  | t_value_typing_var : forall D G x t,
      ok D -> wfenv (t_wft D) G -> binds x t G ->
      t_value_typing D G (t_trm_fvar x) t
  | t_value_typing_true : forall D G,
      ok D -> wfenv (t_wft D) G -> t_value_typing D G t_trm_true t_typ_bool
  | t_value_typing_false : forall D G,
      ok D -> wfenv (t_wft D) G -> t_value_typing D G t_trm_false t_typ_bool
  | t_value_typing_pair : forall D G u1 u2 t1 t2,
      t_value_typing D G u1 t1 -> t_value_typing D G u2 t2 ->
      t_value_typing D G (t_trm_pair u1 u2) (t_typ_pair t1 t2)
  | t_value_typing_abs : forall L D G m t1 t2,
      wfenv (t_wft D) G ->
      (forall x X, x \notinLN L -> X \notinLN L ->
        t_typing (D +&+ X ~ star)
                 (G +&+ x ~ (open_tt_var t1 X))
                 (open_te_var (t_open_ee_var m x) X)
                 (open_tt_var t2 X)) ->
      t_value_typing D G (t_trm_abs t1 m) (t_typ_arrow t1 t2).

Scheme t_typing_mut := Induction for t_typing Sort Prop
with t_value_typing_mut := Induction for t_value_typing Sort Prop.

Hint Constructors t_typing t_value_typing.

(* CPS makes evaluation context of target lang simple *)
Inductive t_eval_context : ctx -> Prop :=
  | t_eval_context_hole : t_eval_context t_ctx_hole.

(* Well-formed context *)
Inductive t_context : bool (* accept only values? *) -> ctx -> Prop :=
  | t_context_value_context : forall b C,
      t_value_context b C -> t_context b C
  | t_context_hole : forall b, t_context b t_ctx_hole
  | t_context_if : forall b C m1 m2,
      t_value_context b C -> t_term m1 -> t_term m2 ->
      t_context b (t_ctx_if C m1 m2)
  | t_context_if_true : forall u b C m2,
      t_value u -> t_context b C -> t_term m2 ->
      t_context b (t_ctx_if_true u C m2)
  | t_context_if_false : forall u m1 b C,
      t_value u -> t_term m1 -> t_context b C ->
      t_context b (t_ctx_if_false u m1 C)
  | t_context_let_fst : forall L b C m,
      t_value_context b C ->
      (forall x, x \notinLN L -> t_term (t_open_ee_var m x)) ->
      t_context b (t_ctx_let_fst C m)
  | t_context_let_fst_k : forall L u b C,
      t_value u ->
      (forall x, x \notinLN L -> t_context b (t_ctx_open_ee_var C x)) ->
      t_context b (t_ctx_let_fst_k u C)
  | t_context_let_snd : forall L b C m,
      t_value_context b C ->
      (forall x, x \notinLN L -> t_term (t_open_ee_var m x)) ->
      t_context b (t_ctx_let_snd C m)
  | t_context_let_snd_k : forall L u b C,
      t_value u ->
      (forall x, x \notinLN L -> t_context b (t_ctx_open_ee_var C x)) ->
      t_context b (t_ctx_let_snd_k u C)
  | t_context_app1 : forall b C t u,
      t_value_context b C -> t_type t -> t_value u ->
      t_context b (t_ctx_app1 C t u)
  | t_context_app2 : forall u t b C,
      t_value u -> t_type t -> t_value_context b C ->
      t_context b (t_ctx_app2 u t C)

with t_value_context : bool (* accept only values? *) -> ctx -> Prop :=
  | t_value_context_hole : t_value_context true t_ctx_hole
  | t_value_context_pair_left : forall b C u,
      t_value_context b C -> t_value u ->
      t_value_context b (t_ctx_pair_left C u)
  | t_value_context_pair_right : forall b C u,
      t_value u -> t_value_context b C ->
      t_value_context b (t_ctx_pair_right u C)
  | t_value_context_abs : forall L t b C,
      (forall X, X \notinLN L -> t_type (open_tt_var t X)) ->
      (forall x X, x \notinLN L -> X \notinLN L ->
        t_context b (ctx_open_te_var (t_ctx_open_ee_var C x) X)) ->
      t_value_context b (t_ctx_abs t C).

Scheme t_context_mut := Induction for t_context Sort Prop
with t_value_context_mut := Induction for t_value_context Sort Prop.

Hint Constructors t_context t_value_context.

(* typing for contexts *)

Inductive t_context_typing (* |- C : ( D ; G |- t ) ~> ( D' ; G' |- t' ) *)
  : bool (* accept only values? *) -> ctx ->
    env_type -> env_term -> typ -> env_type -> env_term -> typ -> Prop :=
  | t_context_typing_hole : forall b D_hole G_hole t_hole D G,
      wfenv (t_wft D_hole) G_hole -> wfenv (t_wft (D_hole +&+ D)) (G_hole +&+ G) ->
      t_wft D_hole t_hole -> ok (D_hole +&+ D) ->
      t_context_typing b t_ctx_hole D_hole G_hole t_hole
                                    (D_hole +&+ D) (G_hole +&+ G) t_hole
  | t_context_typing_if : forall b Cv D_hole G_hole t_hole D G m1 m2 t,
      t_value_context_typing b Cv D_hole G_hole t_hole D G t_typ_bool ->
      t_typing D G m1 t -> t_typing D G m2 t ->
      t_context_typing b (t_ctx_if Cv m1 m2) D_hole G_hole t_hole D G t
  | t_context_typing_if_true : forall b C D_hole G_hole t_hole D G u m2 t,
      t_value_typing D G u t_typ_bool ->
      t_context_typing b C D_hole G_hole t_hole D G t -> t_typing D G m2 t ->
      t_context_typing b (t_ctx_if_true u C m2) D_hole G_hole t_hole D G t
  | t_context_typing_if_false : forall b C D_hole G_hole t_hole D G u m1 t,
      t_value_typing D G u t_typ_bool ->
      t_typing D G m1 t -> t_context_typing b C D_hole G_hole t_hole D G t ->
      t_context_typing b (t_ctx_if_false u m1 C) D_hole G_hole t_hole D G t
  | t_context_typing_let_fst : forall b L Cv D_hole G_hole t_hole D G m t1 t2 t,
      t_value_context_typing b Cv D_hole G_hole t_hole D G (t_typ_pair t1 t2) ->
      (forall x, x \notinLN L ->
        t_typing D (G +&+ x ~ t1) (t_open_ee_var m x) t) ->
      t_context_typing b (t_ctx_let_fst Cv m) D_hole G_hole t_hole D G t
  | t_context_typing_let_fst_k
    : forall b L C D_hole G_hole t_hole D G u t1 t2 t,
      t_value_typing D G u (t_typ_pair t1 t2) ->
      (forall x, x \notinLN L ->
        t_context_typing b (t_ctx_open_ee_var C x) D_hole G_hole t_hole
                                                   D (G +&+ x ~ t1) t) ->
      t_context_typing b (t_ctx_let_fst_k u C) D_hole G_hole t_hole D G t
  | t_context_typing_let_snd : forall b L Cv D_hole G_hole t_hole D G m t1 t2 t,
      t_value_context_typing b Cv D_hole G_hole t_hole D G (t_typ_pair t1 t2) ->
      (forall x, x \notinLN L ->
        t_typing D (G +&+ x ~ t2) (t_open_ee_var m x) t) ->
      t_context_typing b (t_ctx_let_snd Cv m) D_hole G_hole t_hole D G t
  | t_context_typing_let_snd_k
    : forall b L C D_hole G_hole t_hole D G u t1 t2 t,
      t_value_typing D G u (t_typ_pair t1 t2) ->
      (forall x, x \notinLN L ->
        t_context_typing b (t_ctx_open_ee_var C x) D_hole G_hole t_hole
                                                   D (G +&+ x ~ t2) t) ->
      t_context_typing b (t_ctx_let_snd_k u C) D_hole G_hole t_hole D G t
  | t_context_typing_app1 : forall b Cv D_hole G_hole t_hole D G u t t1 t2,
      t_value_context_typing b Cv D_hole G_hole t_hole
                                  D G (t_typ_arrow t1 t2) ->
      t_wft D t ->
      t_value_typing D G u (open_tt t1 t) ->
      t_context_typing b (t_ctx_app1 Cv t u) D_hole G_hole t_hole
                       D G (open_tt t2 t)
  | t_context_typing_app2 : forall b Cv D_hole G_hole t_hole D G u t t1 t2,
      t_value_typing D G u (t_typ_arrow t1 t2) ->
      t_wft D t ->
      t_value_context_typing b Cv D_hole G_hole t_hole D G (open_tt t1 t) ->
      t_context_typing b (t_ctx_app2 u t Cv) D_hole G_hole t_hole
                                             D G (open_tt t2 t)

with t_value_context_typing (* |- Cv : ( D ; G |- t ) ~> ( D' ; G' |- t' ) *)
  : bool (* accept only values? *) -> ctx ->
    env_type -> env_term -> typ -> env_type -> env_term -> typ -> Prop :=
  | t_value_context_typing_hole : forall D_hole G_hole t_hole D G,
      wfenv (t_wft D_hole) G_hole -> wfenv (t_wft (D_hole +&+ D)) (G_hole +&+ G) ->
      t_wft D_hole t_hole -> ok (D_hole +&+ D) ->
      t_value_context_typing true t_ctx_hole D_hole G_hole t_hole
                                             (D_hole +&+ D) (G_hole +&+ G) t_hole
  | t_value_context_typing_pair_left
    : forall b Cv D_hole G_hole t_hole D G u t1 t2,
      t_value_context_typing b Cv D_hole G_hole t_hole D G t1 ->
      t_value_typing D G u t2 ->
      t_value_context_typing b (t_ctx_pair_left Cv u) D_hole G_hole t_hole
                                                      D G (t_typ_pair t1 t2)
  | t_value_context_typing_pair_right
    : forall b Cv D_hole G_hole t_hole D G u t1 t2,
      t_value_context_typing b Cv D_hole G_hole t_hole D G t2 ->
      t_value_typing D G u t1 ->
      t_value_context_typing b (t_ctx_pair_right u Cv) D_hole G_hole t_hole
                                                       D G (t_typ_pair t1 t2)
  | t_value_context_typing_abs : forall b L C D_hole G_hole t_hole D G t1 t2,
      wfenv (t_wft D) G ->
      (forall x X, x \notinLN L -> X \notinLN L ->
        t_context_typing b (ctx_open_te_var (t_ctx_open_ee_var C x) X)
                       D_hole G_hole t_hole
                       (D +&+ X ~ star) (G +&+ x ~ (open_tt_var t1 X))
                       (open_tt_var t2 X)) ->
      t_value_context_typing b (t_ctx_abs t1 C) D_hole G_hole t_hole
                                                D G (t_typ_arrow t1 t2).

Scheme t_context_typing_mut := Induction for t_context_typing Sort Prop
with t_value_context_typing_mut
  := Induction for t_value_context_typing Sort Prop.

Hint Constructors t_context_typing t_value_context_typing.

(** reduction *)

(** one step *)
Inductive t_red_base : trm -> trm -> Prop :=
  | t_red_if_true : forall m1 m2,
      t_term m1 -> t_term m2 -> t_red_base (t_trm_if t_trm_true m1 m2) m1
  | t_red_if_false : forall m1 m2,
      t_term m1 -> t_term m2 -> t_red_base (t_trm_if t_trm_false m1 m2) m2
  | t_red_let_fst : forall u1 u2 m,
      t_value u1 -> t_value u2 -> t_term m ->
      t_red_base (t_trm_let_fst (t_trm_pair u1 u2) m) (t_open_ee m u1)
  | t_red_let_snd : forall u1 u2 m,
      t_value u1 -> t_value u2 -> t_term m ->
      t_red_base (t_trm_let_snd (t_trm_pair u1 u2) m) (t_open_ee m u2)
  | t_red_app : forall t1 m t u,
      t_value (t_trm_abs t1 m) -> t_type t -> t_value u ->
      t_red_base (t_trm_app (t_trm_abs t1 m) t u) (open_te (t_open_ee m u) t).

(** context step *)
Inductive t_red : trm -> trm -> Prop :=
  | t_red_ctx : forall E m m',
      t_red_base m m' -> t_eval_context E -> t_red (plug E m) (plug E m').

(** multi-step step *)
Inductive t_red_star : trm -> trm -> Prop :=
  | t_red_refl : forall m, t_term m -> t_red_star m m
  | t_red_step : forall m1 m2 m3,
      t_red m1 m2 -> t_red_star m2 m3 -> t_red_star m1 m3.

Inductive t_eval : trm -> trm -> Prop :=
  | t_eval_red : forall m u,
      t_red_star m u -> t_value u -> t_eval m u.

(* contextual equivalence *)

Definition t_ctx_approx (D : env_type) (G : env_term) (m1 m2 : trm) (t : typ) :=
  t_typing D G m1 t /\ t_typing D G m2 t /\
  forall C u,
    t_context_typing false C D G t empty empty t_typ_bool ->
    t_eval (plug C m1) u ->
    t_eval (plug C m2) u.

Definition t_ctx_equiv (D : env_type) (G : env_term) (m1 m2 : trm) (t : typ) :=
  t_ctx_approx D G m1 m2 t /\ t_ctx_approx D G m2 m1 t.

(* CIU equivalence *)
(* This definition isn't actually useful: it only handles terms of type bool *)

Definition ciu_approx (D : env_type) (G : env_term) (m1 m2 : trm) (t : typ) :=
  t_typing D G m1 t /\ t_typing D G m2 t /\
  forall E d g u,
    t_eval_context E ->
    t_context_typing false E empty empty (subst_tt d t)
                             empty empty t_typ_bool ->
    relenv t_type d (fun _ => True) D (fun t _ => t_wft empty t) ->
    relenv t_value g t_type G (t_typing D empty) ->
    t_eval (plug E (subst_te d (t_subst_ee g m1))) u ->
    t_eval (plug E (subst_te d (t_subst_ee g m2))) u.
