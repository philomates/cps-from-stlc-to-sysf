(***************************************************************************
* STLC (source language) definitions From Ahmed & Blume ICFP 2011          *
* William J. Bowman, Phillip Mates & James T. Perconti                     *
***************************************************************************)

Set Implicit Arguments.
Require Import LibLN.
Require Import Core_Definitions.
Implicit Type x : var.
Implicit Type X : var.

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
  | s_value_abs  : forall L T e,
      (forall x, x \notin L -> s_term (s_open_ee_var e x)) ->
      (s_type T) ->
      s_value (s_trm_abs T e).

Scheme s_term_mut := Induction for s_term Sort Prop
with s_value_mut := Induction for s_value Sort Prop.

Definition s_env := LibEnv.env typ.

(* TODO: s_ok will need to ensure s_type hold on each typ *)
Inductive s_typing : s_env -> trm -> typ -> Prop :=
  | s_typing_var : forall G x T,
      s_ok G -> binds x T G -> s_typing G (s_trm_fvar x) T
  | s_typing_true : forall G,
      s_ok G -> s_typing G s_trm_true s_typ_bool
  | s_typing_false : forall G,
      s_ok G -> s_typing G s_trm_false s_typ_bool
  | s_typing_abs : forall L G e T1 T2,
      (forall x, x \notin L ->
        s_typing (G & x ~ T1) (s_open_ee_var e x) T2) ->
        (s_type T1) ->
        s_typing G (s_trm_abs T1 e) (s_typ_arrow T1 T2)
  | s_typing_if : forall G e1 e2 e3 T,
      s_typing G e1 s_typ_bool -> s_typing G e2 T -> s_typing G e3 T ->
      s_typing G (s_trm_if e1 e2 e3) T
  | s_typing_app : forall G e1 e2 T1 T2,
      s_typing G e1 (s_typ_arrow T1 T2) -> s_typing G e2 T1 ->
      s_typing G (s_trm_app e1 e2) T2.

(* Santity check theorem. a well-typed source term should have a
 * well-formed source type 
 *)
Theorem s_typing_implies_s_type : forall G e s,
  s_typing G e s -> s_type s.
Proof. (* TODO *)
Admitted. 

(* contexts *)

Inductive s_eval_context : ctx -> Prop :=
  | s_eval_context_hole : s_eval_context ctx_hole
  | s_eval_context_if : forall E e1 e2,
      s_eval_context E -> s_term e1 -> s_term e2 -> s_eval_context (s_ctx_if E e1 e2)
  | s_eval_context_app1 : forall E e,
      s_eval_context E -> s_term e -> s_eval_context (s_ctx_app1 E e)
  | s_eval_context_app2 : forall v E,
      s_value v -> s_eval_context E -> s_eval_context (s_ctx_app2 v E).

(* TODO: santity check theorem *)

Inductive s_context : ctx -> Prop :=
  | s_context_hole : s_context s_ctx_hole
  | s_context_if : forall C e1 e2,
      s_context C -> s_term e1 -> s_term e2 -> s_context (s_ctx_if C e1 e2)
  | s_context_app1 : forall C e,
      s_context C -> s_term e -> s_context (s_ctx_app1 C e)
  | s_context_app2 : forall v C,
      s_value v -> s_context C -> s_context (s_ctx_app2 v C)
  | s_context_abs : forall L T C,
      (forall x, x \notin L -> s_context (s_ctx_open_var C x)) ->
      (s_type T) ->
      s_context (s_ctx_abs T C)
  | s_context_if_true : forall e1 C e3,
      s_term e1 -> s_context C -> s_term e3 -> s_context (s_ctx_if_true e1 C e3)
  | s_context_if_false : forall e1 e2 C,
      s_term e1 -> s_term e2 -> s_context C -> s_context (s_ctx_if_false e1 e2 C).

(* TODO: santity check theorem *)

(* typing for contexts *)

Inductive s_context_typing : ctx -> env -> typ -> env -> typ -> Prop :=
  | s_context_typing_hole : forall G_hole s_hole G,
      s_ok G_hole -> s_ok G -> extends G_hole G -> 
      s_type s_hole ->
      s_context_typing s_ctx_hole G_hole s_hole G T_hole
  | s_context_typing_if : forall C G_hole s_hole G e2 e3 s,
      s_context_typing C G_hole s_hole G s_typ_bool ->
      s_typing G e2 s -> s_typing G e3 s ->
      s_context_typing (s_ctx_if C e2 e3) G_hole s_hole G s
  | s_context_typing_app1 : forall C G_hole s_hole G e s s',
      s_context_typing C G_hole s_hole G (s_type_arrow s s') ->
      s_typing G e s ->
      s_context_typing (s_ctx_app1 C e) G_hole s_hole G s'
  | s_context_typing_app2 : forall C G_hole s_hole G e s s',
      s_typing G e (s_type_arrow s s') ->
      s_context_typing C G_hole s_hole G s ->
      s_context_typing (s_ctx_app2 e C) G_hole s_hole G s'
  | s_context_typing_abs : forall L C G_hole s_hole G s s',
      (forall x, x \notin L ->
        s_context_typing (s_ctx_open_var C x) G_hole s_hole (G & x ~ s) s') ->
      s_type T -> (* XXX: Not sure if this check is necessary. *)
      s_context_typing (s_ctx_abs s C) G_hole s_hole G (s_type_arrow s s')
  | s_context_typing_if_true : forall C G_hole s_hole G e1 e3 s,
      s_typing G e1 s_type_bool ->
      (* TODO: Go back and s/s_type/s_typ/g *)
      s_context_typing C G_hole s_hole G s ->
      s_typing G e3 s ->
      s_context_typing (s_ctx_if_true e1 C e3) G_hole s_hole G s
  | s_context_typing_if_false : forall C G_hole s_hole G e1 e2 s,
      s_typing G e1 s_type_bool -> s_typing G e2 s ->
      s_context_typing C G_hole s_hole G s ->
      s_context_typing (s_ctx_if_false e1 e2 C) G_hole s_hole G s.

(* TODO: santity check theorem *)

(* reduction *)

Inductive s_red_base : trm -> trm -> Prop :=
  | s_red_if_true : forall e1 e2,
      s_term e1 -> s_term e2 ->
      s_red_base (s_trm_if s_trm_true e1 e2) e1
  | s_red_if_false : forall e1 e2,
      s_term e1 -> s_term e2 ->
      s_red_base (s_trm_if s_trm_false e1 e2) e2
  | s_red_app : forall e v T1,
      s_value (s_trm_abs T1 e) -> s_value v ->
      s_red_base (s_trm_app (s_trm_abs T1 e) v) (s_open_ee_var e v).

(* TODO: santity check theorem *)
(* TODO: Requires definition of plug *)

Inductive s_red : trm -> trm -> Prop :=
  | s_red_ctx : forall E e e',
      s_red_base e e' -> s_eval_context E ->
      s_red (s_plug E e) (s_plug E e').

Inductive s_red_star : trm -> trm -> Prop :=
  | s_red_refl : forall e, s_term e -> s_red_star e e
  | s_red_step : forall e1 e2 e3,
      s_red e1 e2 -> s_red_star e2 e3 -> s_red_star e1 e3.

Inductive s_eval : trm -> trm -> Prop :=
  | s_eval_red : forall e v,
      s_red_star e v -> s_value v -> s_eval e v.

(* TODO: I am here *)

(* contextual equivalence *)

Definition s_ctx_approx (G : env) (e1 e2 : trm) (T : typ) :=
  s_typing G e1 T /\ s_typing G e2 T /\
  forall C v,
    s_context_typing C G T empty s_typ_bool ->
    s_eval (s_plug C e1) v ->
    s_eval (s_plug C e2) v.

Definition ctx_equiv (G : env) (e1 e2 : trm) (T : type) :=
  ctx_approx G e1 e2 T /\ ctx_approx G e2 e1 T.

(* CIU equivalence *)

Definition substitution := LibEnv.env trm.

Definition subst_satisfies g G :=
  forall x v T, binds x v g -> value v /\ binds x T G /\ typing empty v T.

Fixpoint apply_subst (g : substitution) (e : trm) :=
  match e with
  | trm_bvar n => trm_bvar n
  | trm_fvar x => match get x g with None => trm_fvar x
                    | Some v => v end
  | trm_true => trm_true
  | trm_false => trm_false
  | trm_abs T e => trm_abs T (apply_subst g e)
  | trm_if e1 e2 e3 => trm_if (apply_subst g e1)
                              (apply_subst g e2)
                              (apply_subst g e3)
  | trm_app e1 e2 => trm_app (apply_subst g e1)
                            (apply_subst g e2)
  end.

Definition ciu_approx (G : env) (e1 e2 : trm) (T : type) :=
  typing G e1 T /\ typing G e2 T /\
  forall E g v,
    eval_context E -> context_typing E empty T empty type_bool ->
    subst_satisfies g G ->
    eval (plug E (apply_subst g e1)) v ->
    eval (plug E (apply_subst g e2)) v.
