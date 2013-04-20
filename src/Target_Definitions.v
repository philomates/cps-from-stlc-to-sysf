(***************************************************************************
* Target language definitions From Ahmed & Blume ICFP 2011                 *
* William J. Bowman, Phillip Mates & James T. Perconti                     *
***************************************************************************)

Require Import Core_Infrastructure.

(* ********************************************************************** *)
(** * Description of the Language *)

(* Target Types *)

Inductive t_type : typ -> Prop :=
  | t_type_pf_var : forall x, t_type (t_typ_fvar x)
  | t_type_pf_bool : t_type t_typ_bool
  | t_type_pf_pair : forall t1 t2,
      t_type t1 -> t_type t2 -> t_type (t_typ_pair t1 t2)
  | t_type_pf_arrow : forall L t1 t2,
      (forall X, X \notin L -> t_type (open_tt_var t1 X)) ->
      (forall X, X \notin L -> t_type (open_tt_var t2 X)) ->
      t_type (t_typ_arrow t1 t2).

Hint Constructors t_type.

(* Target Terms *)

Inductive t_term : trm -> Prop :=
  | t_term_value : forall u, t_value u -> t_term u
  | t_term_if : forall u m1 m2,
      t_value u -> t_term m1 -> t_term m2 -> t_term (t_trm_if u m1 m2)
  | t_term_let_fst : forall L u m,
      t_value u ->
      (forall x, x \notin L -> t_term (t_open_ee_var m x)) ->
      t_term (t_trm_let_fst u m)
  | t_term_let_snd : forall L u m,
      t_value u ->
      (forall x, x \notin L -> t_term (t_open_ee_var m x)) ->
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
      (forall X, X \notin L -> t_type (open_tt_var t X)) ->
      (forall x X, x \notin L -> X \notin L ->
        t_term (open_te_var (t_open_ee_var m x) X)) ->
      t_value (t_trm_abs t m).

Scheme t_term_mut := Induction for t_term Sort Prop
with t_value_mut := Induction for t_value Sort Prop.
Hint Constructors t_term t_value.

(* Delta |- tau *)
Inductive t_wft : env_type -> typ -> Prop :=
  | t_wft_var : forall D X, binds X star D -> t_wft D (t_typ_fvar X)
  | t_wft_bool : forall D, t_wft D t_typ_bool
  | t_wft_pair : forall D t1 t2,
      t_wft D t1 -> t_wft D t2 -> t_wft D (t_typ_pair t1 t2)
  | t_wft_arrow : forall L D t1 t2,
      (forall X (fr1 : X \notin L), t_wft (D & X ~ star) (open_tt_var t1 X)) ->
      (forall X (fr2 : X \notin L), t_wft (D & X ~ star) (open_tt_var t2 X)) ->
      t_wft D (t_typ_arrow t1 t2).

Hint Constructors t_wft.

Notation t_type_bool D := [t_typ_bool, t_wft_bool D; t_wft D].
Notation t_type_pair D t1 t2 :=
  [t_typ_pair (obj t1) (obj t2),
   t_wft_pair D (obj t1) (obj t2) (pf t1) (pf t2);
   t_wft D].
(* Notation t_type_arrow L t1 t2 :
  [t_typ_arrow (obj t1) (obj t2),
   t_type_pf_arrow L (obj t1) (obj t2) ? ?;
   t_type]. *)

Lemma t_wft_weaken_base : forall D DD D' t,
  t_wft (D & D') t -> ok (D & DD & D') -> t_wft (D & DD & D') t.
Proof.
  intros. remember (D & D') as D0. generalize dependent D'.
  induction H; intros; subst; auto.
  apply t_wft_var. apply* binds_weaken.
Admitted.
(*  apply_fresh t_wft_arrow as X.
  rewrite <- concat_assoc.
  apply H0; try rewrite concat_assoc; auto.
  apply ok_push; auto. *)

Lemma t_wft_weaken : forall D X t,
  t_wft D t -> ok (D & X ~ star) -> t_wft (D & X ~ star) t.
Proof.
  intros.
  replace (D & X ~ star) with (D & X ~ star & empty);
  try apply t_wft_weaken_base;
  rewrite* concat_empty_r.
Qed.

Lemma t_wftenv_weaken : forall D (G : env_term (t_wft D)) X,
  ok G -> ok (D & X ~ star) ->
  exists (G' : env_term (t_wft (D & X ~ star))),
    forall x t, binds x t (map (fun t => obj t) G) <->
                binds x t (map (fun t => obj t) G').
Proof.
  induction 1; intros.
  exists (empty : env_term (t_wft (D & X ~ star))).
  rewrite map_empty. rewrite* map_empty.
  remember ([obj v, t_wft_weaken D X (obj v) (pf v) H1]
            : typ_satisfying (t_wft (D & X ~ star))) as v'.
  assert (IH : ok (D & X ~ star)). exact H1.
  apply IHok in IH. destruct IH as [G' IH].
  exists (G' & x ~ v').
  repeat rewrite map_concat. repeat rewrite map_single.
  destruct v as [t p]. subst. simpl.
  split; intros; apply binds_push_inv in H2; destruct H2; destruct H2;
  destruct (IH x0 t0) as [IH1 IH2]; subst;
  try apply binds_push_eq; apply* binds_push_neq.
Qed.

(** Typing relation *)
(* Delta;Gamma |- m:t *)
(* NOTE: Might need to enforce value restrictions
         we need to be able to prove: D G |- m : t -> term m *)
Inductive t_typing (D : env_type) : env_term (t_wft D) ->
                     trm -> typ_satisfying (t_wft D) -> Prop :=
  | t_typing_var : forall (G : env_term (t_wft D)) x t,
      ok D -> ok G -> binds x t G -> t_typing D G (t_trm_fvar x) t
  | t_typing_true : forall G,
      ok D -> ok G -> t_typing D G t_trm_true (t_type_bool D)
  | t_typing_false : forall G,
      ok D -> ok G -> t_typing D G t_trm_false (t_type_bool D)
  | t_typing_pair : forall G u1 u2 t1 t2,
      t_typing D G u1 t1 -> t_typing D G u2 t2 -> t_value u1 -> t_value u2 ->
      t_typing D G (t_trm_pair u1 u2) (t_type_pair D t1 t2)
  | t_typing_abs : forall L (G : env_term (t_wft D)) m t1 t2,
      forall (pf1 :
        forall X, X \notin L -> t_wft (D & X ~ star) (open_tt_var t1 X)),
      forall (pf2 :
        forall X, X \notin L -> t_wft (D & X ~ star) (open_tt_var t2 X)),
      (forall x X (frx : x \notin L) (frX : X \notin L),
        t_typing (D & X ~ star)
                    (* in the line below, instead of G we need something
                       of type (env_term (t_wft D & X ~ star))
                       but I don't know how to get that.
                       I think we'll need t_wftenv_weaken (above) -JTP *)
                 (G & x ~ [open_tt_var t1 X, pf1 X frX; t_wft (D & X ~ star)])
                 (open_te_var (t_open_ee_var m x) X)
                 [open_tt_var t2 X, pf2 X frX; t_wft (D & X ~ star)]) ->
      t_typing D G (t_trm_abs t1 m)
               [t_typ_arrow t1 t2,
                t_wft_arrow L D t1 t2 pf1 ;
                t_wft D]
  | t_typing_if : forall G u m1 m2 t,
      t_typing D G u (t_type_bool D) ->
      t_typing D G m1 t -> t_typing D G m2 t ->
      t_typing D G (t_trm_if u m1 m2) t
  | t_typing_let_fst : forall L G u m t1 t2 t,
      t_typing D G u (t_type_pair D t1 t2) ->
      (forall x, x \notin L -> t_typing D (G & x ~ t1) (t_open_ee_var m x) t) ->
      t_typing D G (t_trm_let_fst u m) t
  | t_typing_let_snd : forall L G u m t1 t2 t,
      t_typing D G u (t_type_pair D t1 t2) ->
      (forall x, x \notin L -> t_typing D (G & x ~ t2) (t_open_ee_var m x) t) ->
      t_typing D G (t_trm_let_snd u m) t.
(*  | t_typing_app : forall G u1 u2 t t1 t2,
      t_wft D t ->
      t_typing D G u1 (t_typ_arrow t1 t2) ->
      t_typing D G u2 (open_tt t1 t) ->
      t_typing D G (t_trm_app u1 t u2) (open_tt t2 t). *)

Hint Constructors t_typing.

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
  | t_context_let_fst : forall b C m,
      t_value_context b C -> t_term m -> t_context b (t_ctx_let_fst C m)
  | t_context_let_fst_k : forall u b C,
      t_value u -> t_context b C -> t_context b (t_ctx_let_fst_k u C)
  | t_context_let_snd : forall b C m,
      t_value_context b C -> t_term m -> t_context b (t_ctx_let_snd C m)
  | t_context_let_snd_k : forall u b C,
      t_value u -> t_context b C -> t_context b (t_ctx_let_snd_k u C)
  | t_context_app1 : forall b C t u,
      t_value_context b C -> t_type t -> t_value u ->
      t_context b (t_ctx_app1 C t u)
  | t_context_app2 : forall u t b C,
      t_value u -> t_type t -> t_value_context b C ->
      t_context b (t_ctx_app2 u t C)

with t_value_context : bool (* accept only values? *) -> ctx -> Prop :=
  | t_value_context_hole : t_value_context true t_ctx_hole
  | t_context_pair_left : forall b C u,
      t_value_context b C -> t_value u ->
      t_value_context b (t_ctx_pair_left C u)
  | t_context_pair_right : forall b C u,
      t_value u -> t_value_context b C ->
      t_value_context b (t_ctx_pair_right u C)
  | t_context_abs : forall L t b C,
      (forall X, X \notin L -> t_type (open_tt_var t X)) ->
      (forall x X, x \notin L -> X \notin L ->
        t_context b (ctx_open_te_var (t_ctx_open_ee_var C x) X)) ->
      t_value_context b (t_ctx_abs t C).

(* typing for contexts
 *  TODO: update this
 *  I'm concerned that this doesn't track all the places where we need
 *  values vs terms: what properties should hold if t_context_typing holds?
 *  We probably expect something about t_context but I don't think we are
 *  checking enough things to have that.  -JTP
 *)
Inductive t_context_typing (* |- C : ( D ; G |- t ) ~> ( D' ; G' |- t' ) *)
  : ctx -> env_type -> env_term -> typ -> env_type -> env_term -> typ -> Prop :=
  | t_context_typing_hole : forall D_hole G_hole T_hole D G,
      ok D_hole G_hole -> ok D -> ok G ->
      extends G_hole G -> extends D_hole D ->
      t_context_typing t_ctx_hole D_hole G_hole T_hole D G T_hole
  | t_context_typing_pair_left : forall C D_hole G_hole T_hole D G u t1 t2,
      t_context_typing C D_hole G_hole T_hole D G t1 ->
      t_typing D G u t2 ->
      t_context_typing (t_ctx_pair_left C u) D_hole G_hole T_hole
                                             D G (t_typ_pair t1 t2)
  | t_context_typing_pair_right : forall C D_hole G_hole T_hole D G u t1 t2,
      t_context_typing C D_hole G_hole T_hole D G t2 ->
      t_typing D G u t1 ->
      t_context_typing (t_ctx_pair_right u C) D_hole G_hole T_hole D G
                     (t_typ_pair t1 t2)
  | t_context_typing_abs : forall L C D_hole G_hole T_hole D G t1 t2,
      (forall x X, x \notin L -> X \notin L ->
        t_context_typing (ctx_open_te_var (t_ctx_open_ee_var C x) X)
                       D_hole G_hole T_hole
                       (D & X ~ star) (G & x ~ (open_tt_var t1 X))
                       (open_tt_var t2 X)) ->
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
  | t_context_typing_let_fst : forall L C D_hole G_hole T_hole D G m t1 t2 t,
      t_context_typing C D_hole G_hole T_hole D G (t_typ_pair t1 t2) ->
      (forall x, x \notin L ->
        t_typing D (G & x ~ t1) (t_open_ee_var m x) t) ->
      t_context_typing (t_ctx_let_fst C m) D_hole G_hole T_hole D G t
  | t_context_typing_let_fst_k : forall L C D_hole G_hole T_hole D G u t1 t2 t,
      t_typing D G u (t_typ_pair t1 t2) ->
      (forall x, x \notin L ->
        t_context_typing C D_hole G_hole T_hole D (G & x ~ t1) t) ->
      t_context_typing (t_ctx_let_fst_k u C) D_hole G_hole T_hole D G t
  | t_context_typing_let_snd : forall L C D_hole G_hole T_hole D G m t1 t2 t,
      t_context_typing C D_hole G_hole T_hole D G (t_typ_pair t1 t2) ->
      (forall x, x \notin L ->
        t_typing D (G & x ~ t2) (t_open_ee_var m x) t) ->
      t_context_typing (t_ctx_let_snd C m) D_hole G_hole T_hole D G t
  | t_context_typing_let_snd_k : forall L C D_hole G_hole T_hole D G u t1 t2 t,
      t_typing D G u (t_typ_pair t1 t2) ->
      (forall x, x \notin L ->
        t_context_typing C D_hole G_hole T_hole D (G & x ~ t2) t) ->
      t_context_typing (t_ctx_let_snd_k u C) D_hole G_hole T_hole D G t
  | t_context_typing_app1 : forall C D_hole G_hole T_hole D G u t t1 t2,
      t_context_typing C D_hole G_hole T_hole D G (t_typ_arrow t1 t2) ->
      t_wft D t ->
      t_typing D G u (open_tt t1 t) ->
      t_context_typing (t_ctx_app1 C t u) D_hole G_hole T_hole D G (open_tt t2 t)
  | t_context_typing_app2 : forall C D_hole G_hole T_hole D G u t t1 t2,
      t_wft D t ->
      t_typing D G u (t_typ_arrow t1 t2) ->
      t_context_typing C D_hole G_hole T_hole D G (open_tt t1 t) ->
      t_context_typing (t_ctx_app2 u t C) D_hole G_hole T_hole D G t2.

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
  | t_red_step : forall m1 m2 e3,
      t_red m1 m2 -> t_red_star m2 e3 -> t_red_star m1 e3.

Inductive t_eval : trm -> trm -> Prop :=
  | t_eval_red : forall m u,
      t_red_star m u -> t_value u -> t_eval m u.

(* contextual equivalence *)
(* TODO: Danger! t_context_typing might not sufficiently check
   that it's ok to plug (see the comment above t_context_typing)  -JTP *)
Definition t_ctx_approx (D : env_type) (G : env_term) (m1 m2 : trm) (t : typ) :=
  t_typing D G m1 t /\ t_typing D G m2 t /\
  forall C u,
    t_context_typing C D G t empty empty t_typ_bool ->
    t_eval (plug C m1) u ->
    t_eval (plug C m2) u.

Definition t_ctx_equiv (D : env_type) (G : env_term) (m1 m2 : trm) (t : typ) :=
  t_ctx_approx D G m1 m2 t /\ t_ctx_approx D G m2 m1 t.

(* CIU equivalence *)
(* TODO: is my CIU definition correct?  -JTP *)

Inductive t_tysubst_satisfies (* |- d : D *) : subst_type -> env_type -> Prop :=
  | t_tysubst_satisfies_empty : t_tysubst_satisfies empty empty
  | t_tysubst_satisfies_extend : forall d D X t,
      t_tysubst_satisfies d D -> X # D -> t_wft empty t ->
      t_tysubst_satisfies (d & X ~ t) (D & X ~ star).

Inductive t_subst_satisfies (* D |- g : G *)
  : env_type -> subst_term -> env_term -> Prop :=
  | t_subst_satisfies_empty : forall D, ok D -> t_subst_satisfies D empty empty
  | t_subst_satisfies_extend : forall D g G x u t,
      t_subst_satisfies D g G -> x # G -> t_typing D empty u t ->
      t_subst_satisfies D (g & x ~ u) (G & x ~ t).

Definition ciu_approx (D : env_type) (G : env_term) (m1 m2 : trm) (t : typ) :=
  t_typing D G m1 t /\ t_typing D G m2 t /\
  forall E d g u,
    t_eval_context E ->
    t_context_typing E empty empty t empty empty t_typ_bool ->
    t_tysubst_satisfies d D -> t_subst_satisfies D g G ->
    t_eval (plug E (subst_te d (subst_ee g m1))) u ->
    t_eval (plug E (subst_te d (subst_ee g m2))) u.
