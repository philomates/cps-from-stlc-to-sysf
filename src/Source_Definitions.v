(***************************************************************************
* STLC (source language) definitions From Ahmed & Blume ICFP 2011          *
* William J. Bowman, Phillip Mates & James T. Perconti                     *
***************************************************************************)

Require Import Core_Definitions LibWfenv.

(* ********************************************************************** *)
(** * Description of the Language *)

(* Source Types *)

Inductive s_type : typ -> Prop :=
  | s_type_bool : s_type s_typ_bool
  | s_type_arrow : forall s1 s2, 
      s_type s1 -> s_type s2 -> s_type (s_typ_arrow s1 s2).

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
  | s_value_abs  : forall L s e,
      (forall x, x \notin L -> s_term (s_open_ee_var e x)) ->
      (s_type s) ->
      s_value (s_trm_abs s e).

Scheme s_term_mut := Induction for s_term Sort Prop
with s_value_mut := Induction for s_value Sort Prop.

Inductive s_typing : env_term -> trm -> typ -> Prop :=
  | s_typing_var : forall G x s,
      wfenv s_type G -> binds x s G -> s_typing G (s_trm_fvar x) s
  | s_typing_true : forall G,
      wfenv s_type G -> s_typing G s_trm_true s_typ_bool
  | s_typing_false : forall G,
      wfenv s_type G -> s_typing G s_trm_false s_typ_bool
  | s_typing_abs : forall L G e s1 s2,
      (forall x, x \notin L -> s_typing (G & x ~ s1) (s_open_ee_var e x) s2) ->
      (s_type s1) ->
      s_typing G (s_trm_abs s1 e) (s_typ_arrow s1 s2)
  | s_typing_if : forall G e1 e2 e3 s,
      s_typing G e1 s_typ_bool -> s_typing G e2 s -> s_typing G e3 s ->
      s_typing G (s_trm_if e1 e2 e3) s
  | s_typing_app : forall G e1 e2 s1 s2,
      s_typing G e1 (s_typ_arrow s1 s2) -> s_typing G e2 s1 ->
      s_typing G (s_trm_app e1 e2) s2.

Hint Constructors s_type s_term s_value s_typing. 

(* contexts *)

Inductive s_eval_context : ctx -> Prop :=
  | s_eval_context_hole : s_eval_context s_ctx_hole
  | s_eval_context_if : forall E e1 e2,
      s_eval_context E -> s_term e1 -> s_term e2 ->
      s_eval_context (s_ctx_if E e1 e2)
  | s_eval_context_app1 : forall E e,
      s_eval_context E -> s_term e ->
      s_eval_context (s_ctx_app1 E e)
  | s_eval_context_app2 : forall v E,
      s_value v -> s_eval_context E ->
      s_eval_context (s_ctx_app2 v E).

Inductive s_context : ctx -> Prop :=
  | s_context_hole : s_context s_ctx_hole
  | s_context_if : forall C e1 e2,
      s_context C -> s_term e1 -> s_term e2 ->
      s_context (s_ctx_if C e1 e2)
  | s_context_app1 : forall C e,
      s_context C -> s_term e ->
      s_context (s_ctx_app1 C e)
  | s_context_app2 : forall v C,
      s_value v -> s_context C ->
      s_context (s_ctx_app2 v C)
  | s_context_abs : forall L T C,
      (forall x, x \notin L -> s_context (s_ctx_open_ee_var C x)) ->
      (s_type T) ->
      s_context (s_ctx_abs T C)
  | s_context_if_true : forall e1 C e3,
      s_term e1 -> s_context C -> s_term e3 ->
      s_context (s_ctx_if_true e1 C e3)
  | s_context_if_false : forall e1 e2 C,
      s_term e1 -> s_term e2 -> s_context C ->
      s_context (s_ctx_if_false e1 e2 C).

(* typing for contexts *)

Inductive s_context_typing (* |- C : G |- s ~> G' |- s' *)
  : ctx -> env_term -> typ -> env_term -> typ -> Prop :=
  | s_context_typing_hole : forall G_hole s_hole G,
      wfenv s_type G_hole -> wfenv s_type G -> extends G_hole G -> 
      s_type s_hole ->
      s_context_typing s_ctx_hole G_hole s_hole G s_hole
  | s_context_typing_if : forall C G_hole s_hole G e2 e3 s,
      s_context_typing C G_hole s_hole G s_typ_bool ->
      s_typing G e2 s -> s_typing G e3 s ->
      s_context_typing (s_ctx_if C e2 e3) G_hole s_hole G s
  | s_context_typing_app1 : forall C G_hole s_hole G e s s',
      s_context_typing C G_hole s_hole G (s_typ_arrow s s') ->
      s_typing G e s ->
      s_context_typing (s_ctx_app1 C e) G_hole s_hole G s'
  | s_context_typing_app2 : forall C G_hole s_hole G e s s',
      s_typing G e (s_typ_arrow s s') ->
      s_context_typing C G_hole s_hole G s ->
      s_context_typing (s_ctx_app2 e C) G_hole s_hole G s'
  | s_context_typing_abs : forall L C G_hole s_hole G s s',
      (forall x, x \notin L -> s_context_typing (s_ctx_open_ee_var C x)
                                                G_hole s_hole
                                                (G & x ~ s) s') ->
      s_type s -> (* XXX: Not sure if this check is necessary. *)
      s_context_typing (s_ctx_abs s C) G_hole s_hole G (s_typ_arrow s s')
  | s_context_typing_if_true : forall C G_hole s_hole G e1 e3 s,
      s_typing G e1 s_typ_bool ->
      s_context_typing C G_hole s_hole G s ->
      s_typing G e3 s ->
      s_context_typing (s_ctx_if_true e1 C e3) G_hole s_hole G s
  | s_context_typing_if_false : forall C G_hole s_hole G e1 e2 s,
      s_typing G e1 s_typ_bool -> s_typing G e2 s ->
      s_context_typing C G_hole s_hole G s ->
      s_context_typing (s_ctx_if_false e1 e2 C) G_hole s_hole G s.

(* reduction *)

Inductive s_red_base : trm -> trm -> Prop :=
  | s_red_if_true : forall e1 e2,
      s_term e1 -> s_term e2 ->
      s_red_base (s_trm_if s_trm_true e1 e2) e1
  | s_red_if_false : forall e1 e2,
      s_term e1 -> s_term e2 ->
      s_red_base (s_trm_if s_trm_false e1 e2) e2
  | s_red_app : forall e v s,
      s_value (s_trm_abs s e) -> s_value v ->
      s_red_base (s_trm_app (s_trm_abs s e) v) (s_open_ee e v).

Inductive s_red : trm -> trm -> Prop :=
  | s_red_ctx : forall E e e',
      s_red_base e e' -> s_eval_context E ->
      s_red (plug E e) (plug E e').

Inductive s_red_star : trm -> trm -> Prop :=
  | s_red_refl : forall e, s_term e -> s_red_star e e
  | s_red_step : forall e1 e2 e3,
      s_red e1 e2 -> s_red_star e2 e3 -> s_red_star e1 e3.

Inductive s_eval : trm -> trm -> Prop :=
  | s_eval_red : forall e v,
      s_red_star e v -> s_value v -> s_eval e v.

(* contextual equivalence *)

Definition s_ctx_approx (G : env_term) (e1 e2 : trm) (s : typ) :=
  s_typing G e1 s /\ s_typing G e2 s /\
  forall C v,
    s_context_typing C G s empty s_typ_bool ->
    s_eval (plug C e1) v ->
    s_eval (plug C e2) v.

Definition s_ctx_equiv (G : env_term) (e1 e2 : trm) (s : typ) :=
  s_ctx_approx G e1 e2 s /\ s_ctx_approx G e2 e1 s.

(* CIU equivalence *)

Definition s_ciu_approx (G : env_term) (e1 e2 : trm) (s : typ) :=
  s_typing G e1 s /\ s_typing G e2 s /\
  forall E g v,
    s_eval_context E -> s_context_typing E empty s empty s_typ_bool ->
    relenv s_value g s_type G (s_typing empty) ->
    s_eval (plug E (s_subst_ee g e1)) v ->
    s_eval (plug E (s_subst_ee g e2)) v.

Definition s_ciu_equiv (G : env_term) (e1 e2 : trm) (s : typ) :=
  s_ciu_approx G e1 e2 s /\ s_ciu_approx G e2 e1 s.
