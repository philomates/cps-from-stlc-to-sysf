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
| t_type_var X of t = t_typ_fvar X
| t_type_bool of t = t_typ_bool
| t_type_pair t1 t2 of
    t_type t1 & t_type t2 & t = t_typ_pair t1 t2
| t_type_arrow (L : vars) t1 t2 of
     forall X, X \notinLN L -> t_type (open_tt_var t1 X) &
     forall X, X \notinLN L -> t_type (open_tt_var t2 X) &
     t = t_typ_arrow t1 t2.

Fixpoint t_typeb (t : typ) : bool :=
  match t with
    t_typ_fvar x => true
  | t_typ_bool  => true
  | t_typ_pair t1 t2 => t_typeb t1 && t_typeb t2
  | t_typ_arrow t1 t2 => t_typeb t1 && t_typeb t2
  | _ => false
  end.

(* Target Terms *)


Inductive t_term (m : trm) : Prop :=
| t_term_value of t_value m
| t_term_if u m1 m2 of
    t_value u & t_term m1 & t_term m2 & m = t_trm_if u m1 m2
| t_term_let_fst L u m1 of
    t_value u & forall x, x \notinLN L -> t_term (t_open_ee_var m1 x) &
    m = t_trm_let_fst u m1
| t_term_let_snd (L : vars) (u : trm) (m1 : trm) of
    t_value u &
    forall x, x \notinLN L -> t_term (t_open_ee_var m1 x) &
    m = t_trm_let_snd u m1
| t_term_app u1 T u2 of
    t_value u1 & t_type T & t_value u2 & m = t_trm_app u1 T u2

with t_value (m : trm) : Prop :=
| t_value_var x of m = t_trm_fvar x
| t_value_true of m = t_trm_true
| t_value_false of m = t_trm_false
| t_value_pair u1 u2 of
   t_value u1 & t_value u2 & m = t_trm_pair u1 u2
| t_value_abs L T m1 of
   forall X, X \notinLN L -> t_type (open_tt_var T X) &
   forall x X, x \notinLN L -> X \notinLN L -> t_term (open_te_var (t_open_ee_var m1 x) X) &
   m = t_trm_abs T m1.

Scheme t_term_mut := Induction for t_term Sort Prop
with t_value_mut := Induction for t_value Sort Prop.

Hint Constructors t_term t_value.


(* Type System *)

(* Delta |- tau *)
Inductive t_wft (D : env_type) (t : typ) : Prop :=
  | t_wft_var X of ok D & binds X star D & t = t_typ_fvar X
  | t_wft_bool of ok D & t = t_typ_bool
  | t_wft_pair t1 t2 of
      t_wft D t1 & t_wft D t2 & t = (t_typ_pair t1 t2)
  | t_wft_arrow L t1 t2 of
      forall X, X \notinLN L -> t_wft (D +&+ X ~ star) (open_tt_var t1 X) &
      forall X, X \notinLN L -> t_wft (D +&+ X ~ star) (open_tt_var t2 X) &
      t = t_typ_arrow t1 t2.

Hint Constructors t_wft.

(** Typing relation *)
(* Delta;Gamma |- m:t *)
Inductive t_typing (D : env_type) (G : env_term) (m : trm) (t : typ) : Prop :=
  | t_typing_value of t_value_typing D G m t & t_typing D G m t
  | t_typing_if u m1 m2 of
      t_value_typing D G u t_typ_bool &
      t_typing D G m1 t & t_typing D G m2 t &
      t_typing D G (t_trm_if u m1 m2) t &
      m = t_trm_if u m1 m2
  | t_typing_let_fst L u m1 t1 t2 of
      t_value_typing D G u (t_typ_pair t1 t2) &
      forall x, x \notinLN L -> t_typing D (G +&+ x ~ t1) (t_open_ee_var m1 x) t &
      t_typing D G (t_trm_let_fst u m1) t &
      m = t_trm_let_fst u m1
  | t_typing_let_snd L u m1 t1 t2 of
      t_value_typing D G u (t_typ_pair t1 t2) &
      forall x, x \notinLN L -> t_typing D (G +&+ x ~ t2) (t_open_ee_var m1 x) t &
      t_typing D G (t_trm_let_snd u m1) t &
      m = t_trm_let_snd u m1
  | t_typing_app u1 u2 t1 t2 targ of
      t_value_typing D G u1 (t_typ_arrow t1 t2) &
      t_wft D t &
      t_value_typing D G u2 (open_tt t1 targ) &
      t_typing D G (t_trm_app u1 t u2) (open_tt t2 targ) &
      t = open_tt t2 targ & m = t_trm_app u1 t u2

with t_value_typing (D : env_type) (G : env_term) (m : trm) (t : typ) : Prop :=
  | t_value_typing_var x of
      ok D & wfenv (t_wft D) G & binds x t G &
      t_value_typing D G (t_trm_fvar x) t &
      m = t_trm_fvar x
  | t_value_typing_true of
      ok D & wfenv (t_wft D) G & t_value_typing D G t_trm_true t_typ_bool &
      t = t_typ_bool & m = t_trm_true
  | t_value_typing_false of
      ok D & wfenv (t_wft D) G & t_value_typing D G t_trm_false t_typ_bool &
      t = t_typ_bool & m = t_trm_false
  | t_value_typing_pair u1 u2 t1 t2 of
      t_value_typing D G u1 t1 & t_value_typing D G u2 t2 &
      t_value_typing D G (t_trm_pair u1 u2) (t_typ_pair t1 t2) &
      t = t_typ_pair t1 t2 & m = t_trm_pair u1 u2
  | t_value_typing_abs L t1 t2 m1 of
      wfenv (t_wft D) G &
      forall x X, x \notinLN L -> X \notinLN L ->
        t_typing (D +&+ X ~ star)
        (G +&+ x ~ (open_tt_var t1 X))
        (open_te_var (t_open_ee_var m1 x) X)
        (open_tt_var t2 X) &
      t_value_typing D G (t_trm_abs t1 m1) (t_typ_arrow t1 t2) &
      m = t_trm_abs t1 m1 & t = t_typ_arrow t1 t2.

Scheme t_typing_mut := Induction for t_typing Sort Prop
with t_value_typing_mut := Induction for t_value_typing Sort Prop.

Hint Constructors t_typing t_value_typing.

(* CPS makes evaluation context of target lang simple *)
Inductive t_eval_context (C : ctx) : Prop :=
  | t_eval_context_hole of C = t_ctx_hole.

(* Well-formed context *)
(* b : accept only values? *)
Inductive t_context (b : bool) (C : ctx) : Prop :=
  | t_context_value_context of t_value_context b C
  | t_context_hole of C = t_ctx_hole
  | t_context_if m1 m2 of
      t_value_context b C & t_term m1 & t_term m2 &
      C = t_ctx_if C m1 m2
  | t_context_if_true u m2 C1 of
      t_value u & t_context b C1 & t_term m2 &
      t_context b (t_ctx_if_true u C m2) &
      C = t_ctx_if_true u C1 m2
  | t_context_if_false u m1 C1 of
      t_value u & t_term m1 & t_context b C1 &
      t_context b (t_ctx_if_false u m1 C1) &
      C = t_ctx_if_false u m1 C1
  | t_context_let_fst L C1 m of
      t_value_context b C1 &
      forall x, x \notinLN L -> t_term (t_open_ee_var m x) &
      t_context b (t_ctx_let_fst C1 m) &
      C = t_ctx_let_fst C1 m
  | t_context_let_fst_k L u C1 of
      t_value u &
      forall x, x \notinLN L -> t_context b (t_ctx_open_ee_var C1 x) &
      t_context b (t_ctx_let_fst_k u C1) &
      C = t_ctx_let_fst_k u C1
  | t_context_let_snd L C1 m of
      t_value_context b C1 &
      forall x, x \notinLN L -> t_term (t_open_ee_var m x) &
      t_context b (t_ctx_let_snd C1 m) &
      C = t_ctx_let_snd C1 m
  | t_context_let_snd_k L u C1 of
      t_value u &
      forall x, x \notinLN L -> t_context b (t_ctx_open_ee_var C1 x) &
      t_context b (t_ctx_let_snd_k u C1) &
      C = t_ctx_let_snd_k u C1
  | t_context_app1 C1 t u of
      t_value_context b C1 & t_type t & t_value u &
      t_context b (t_ctx_app1 C1 t u) &
      C = t_ctx_app1 C1 t u
  | t_context_app2 u t C1 of
      t_value u & t_type t & t_value_context b C1 &
      t_context b (t_ctx_app2 u t C1) &
      C = t_ctx_app2 u t C1

with t_value_context (b : bool) (C : ctx) : Prop :=
  | t_value_context_hole of b = true & C = t_ctx_hole
  | t_value_context_pair_left C1 u of
      t_value_context b C1 & t_value u &
      t_value_context b (t_ctx_pair_left C1 u) &
      C = t_ctx_pair_left C1 u
  | t_value_context_pair_right C1 u of
      t_value u & t_value_context b C1 &
      t_value_context b (t_ctx_pair_right u C1) &
      C = t_ctx_pair_right u C1
  | t_value_context_abs L t C1 of
      forall X, X \notinLN L -> t_type (open_tt_var t X) &
      forall x X, x \notinLN L -> X \notinLN L ->
        t_context b (ctx_open_te_var (t_ctx_open_ee_var C1 x) X) &
      t_value_context b (t_ctx_abs t C1) &
      C = t_ctx_abs t C1.

Scheme t_context_mut := Induction for t_context Sort Prop
with t_value_context_mut := Induction for t_value_context Sort Prop.

Hint Constructors t_context t_value_context.

(* typing for contexts *)

(* b : accept only values? *)
(* |- C : ( D_hole ; G_hole |- t_hole ) ~> ( D ; G |- t ) *)
Inductive t_context_typing (b : bool)
                           (C : ctx) (D_hole : env_type) (G_hole : env_term) (t_hole : typ)
                           (D : env_type) (G : env_term) (t : typ) : Prop :=
  | t_context_typing_hole D1 G1 of
      wfenv (t_wft D_hole) G_hole & wfenv (t_wft (D_hole +&+ D1)) (G_hole +&+ G1) &
      t_wft D_hole t_hole & ok (D_hole +&+ D1) &
      t_context_typing b t_ctx_hole D_hole G_hole t_hole (D_hole +&+ D1) (G_hole +&+ G1) t_hole &
      C = t_ctx_hole & D = D_hole +&+ D1 & G = G_hole +&+ G1 & t = t_hole
  | t_context_typing_if Cv m1 m2 of
      t_value_context_typing b Cv D_hole G_hole t_hole D G t_typ_bool &
      t_typing D G m1 t & t_typing D G m2 t &
      t_context_typing b (t_ctx_if Cv m1 m2) D_hole G_hole t_hole D G t &
      C = t_ctx_if Cv m1 m2
  | t_context_typing_if_true C1 u m2 of
      t_value_typing D G u t_typ_bool &
      t_context_typing b C1 D_hole G_hole t_hole D G t & t_typing D G m2 t &
      t_context_typing b (t_ctx_if_true u C1 m2) D_hole G_hole t_hole D G t &
      C = t_ctx_if_true u C1 m2
  | t_context_typing_if_false C1 u m1 of
      t_value_typing D G u t_typ_bool &
      t_typing D G m1 t & t_context_typing b C1 D_hole G_hole t_hole D G t &
      t_context_typing b (t_ctx_if_false u m1 C1) D_hole G_hole t_hole D G t &
      C = t_ctx_if_false u m1 C1
  | t_context_typing_let_fst L Cv m t1 t2 of
      t_value_context_typing b Cv D_hole G_hole t_hole D G (t_typ_pair t1 t2) &
      forall x, x \notinLN L ->
        t_typing D (G +&+ x ~ t1) (t_open_ee_var m x) t &
      t_context_typing b (t_ctx_let_fst Cv m) D_hole G_hole t_hole D G t &
      C = t_ctx_let_fst Cv m
  | t_context_typing_let_fst_k L C1 u t1 t2 of
      t_value_typing D G u (t_typ_pair t1 t2) &
      forall x, x \notinLN L ->
        t_context_typing b (t_ctx_open_ee_var C1 x) D_hole G_hole t_hole D (G +&+ x ~ t1) t &
      t_context_typing b (t_ctx_let_fst_k u C1) D_hole G_hole t_hole D G t &
      C = t_ctx_let_fst_k u C1
  | t_context_typing_let_snd L Cv m t1 t2 of
      t_value_context_typing b Cv D_hole G_hole t_hole D G (t_typ_pair t1 t2) &
      forall x, x \notinLN L -> t_typing D (G +&+ x ~ t2) (t_open_ee_var m x) t &
      t_context_typing b (t_ctx_let_snd Cv m) D_hole G_hole t_hole D G t &
      C = t_ctx_let_snd Cv m
  | t_context_typing_let_snd_k L C1 u t1 t2 of
      t_value_typing D G u (t_typ_pair t1 t2) &
      forall x, x \notinLN L ->
        t_context_typing b (t_ctx_open_ee_var C1 x) D_hole G_hole t_hole
        D (G +&+ x ~ t2) t &
      t_context_typing b (t_ctx_let_snd_k u C1) D_hole G_hole t_hole D G t &
      C = t_ctx_let_snd_k u C1
  | t_context_typing_app1 Cv u targ t1 t2 of
      t_value_context_typing b Cv D_hole G_hole t_hole D G (t_typ_arrow t1 t2) &
      t_wft D targ &
      t_value_typing D G u (open_tt t1 targ) &
      t_context_typing b (t_ctx_app1 Cv targ u) D_hole G_hole t_hole D G (open_tt t2 targ) &
      C = t_ctx_app1 Cv targ u & t = open_tt t2 targ
  | t_context_typing_app2 Cv u targ t1 t2 of
      t_value_typing D G u (t_typ_arrow t1 t2) &
      t_wft D targ &
      t_value_context_typing b Cv D_hole G_hole t_hole D G (open_tt t1 targ) &
      t_context_typing b (t_ctx_app2 u targ Cv) D_hole G_hole t_hole D G (open_tt t2 targ) &
      C = t_ctx_app2 u targ Cv & t = open_tt t2 targ

with t_value_context_typing (b : bool)
                            (C : ctx) (D_hole : env_type) (G_hole : env_term) (t_hole : typ)
                            (D : env_type) (G : env_term) (t : typ) : Prop :=
  | t_value_context_typing_hole D1 G1 of
      wfenv (t_wft D_hole) G_hole & wfenv (t_wft (D_hole +&+ D1)) (G_hole +&+ G1) &
      t_wft D_hole t_hole & ok (D_hole +&+ D1) &
      t_value_context_typing true t_ctx_hole D_hole G_hole t_hole (D_hole +&+ D1) (G_hole +&+ G1) t_hole &
      D = D_hole +&+ D1 & G = G_hole +&+ G1 & t = t_hole
  | t_value_context_typing_pair_left Cv u t1 t2 of
      t_value_context_typing b Cv D_hole G_hole t_hole D G t1 &
      t_value_typing D G u t2 &
      t_value_context_typing b (t_ctx_pair_left Cv u) D_hole G_hole t_hole D G (t_typ_pair t1 t2) &
      C = t_ctx_pair_left Cv u & t = t_typ_pair t1 t2
  | t_value_context_typing_pair_right Cv u t1 t2 of
      t_value_context_typing b Cv D_hole G_hole t_hole D G t2 &
      t_value_typing D G u t1 &
      t_value_context_typing b (t_ctx_pair_right u Cv) D_hole G_hole t_hole D G (t_typ_pair t1 t2) &
      C = t_ctx_pair_right u Cv & t = t_typ_pair t1 t2
  | t_value_context_typing_abs L C1 t1 t2 of
      wfenv (t_wft D) G &
      forall x X, x \notinLN L -> X \notinLN L ->
       t_context_typing b (ctx_open_te_var (t_ctx_open_ee_var C1 x) X)
                      D_hole G_hole t_hole
                      (D +&+ X ~ star) (G +&+ x ~ (open_tt_var t1 X))
                      (open_tt_var t2 X) &
      t_value_context_typing b (t_ctx_abs t1 C1) D_hole G_hole t_hole D G (t_typ_arrow t1 t2) &
      C = t_ctx_abs t1 C1 & t = t_typ_arrow t1 t2.

Scheme t_context_typing_mut := Induction for t_context_typing Sort Prop
with t_value_context_typing_mut
  := Induction for t_value_context_typing Sort Prop.

Hint Constructors t_context_typing t_value_context_typing.

(** reduction *)

(** one step *)
Inductive t_red_base (ml : trm) (mr : trm) : Prop :=
  | t_red_if_true m1 m2 of
      t_term m1 & t_term m2 & t_red_base (t_trm_if t_trm_true m1 m2) m1 &
      ml = t_trm_if t_trm_true m1 m2 & mr = m1
  | t_red_if_false m1 m2 of
      t_term m1 & t_term m2 & t_red_base (t_trm_if t_trm_false m1 m2) m2 &
      ml = t_trm_if t_trm_true m1 m2 & mr = m2
  | t_red_let_fst u1 u2 m of
      t_value u1 & t_value u2 & t_term m &
      t_red_base (t_trm_let_fst (t_trm_pair u1 u2) m) (t_open_ee m u1) &
      ml = t_trm_let_fst (t_trm_pair u1 u2) m & mr = t_open_ee m u1
  | t_red_let_snd u1 u2 m of
      t_value u1 & t_value u2 & t_term m &
      t_red_base (t_trm_let_snd (t_trm_pair u1 u2) m) (t_open_ee m u2) &
      ml = t_trm_let_snd (t_trm_pair u1 u2) m & mr = t_open_ee m u2
  | t_red_app t1 m t u of
      t_value (t_trm_abs t1 m) & t_type t & t_value u &
      t_red_base (t_trm_app (t_trm_abs t1 m) t u) (open_te (t_open_ee m u) t) &
      ml = t_trm_app (t_trm_abs t1 m) t u & mr = open_te (t_open_ee m u) t.

(** context step *)
Inductive t_red (ml : trm) (mr :  trm) : Prop :=
  | t_red_ctx E m m' of
      t_red_base m m' & t_eval_context E & t_red (plug E m) (plug E m') &
      ml = plug E m & mr = plug E m'.

(** multi-step step *)
Inductive t_red_star (ml : trm) (mr :  trm) : Prop :=
  | t_red_refl of t_term ml & t_red_star ml mr & ml = mr
  | t_red_step mmid of t_red ml mmid & t_red_star mmid mr.

Inductive t_eval (m : trm) (u :  trm) : Prop :=
  | t_eval_red of t_red_star m u & t_value u.

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
