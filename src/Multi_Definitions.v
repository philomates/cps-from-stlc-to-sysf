(**************************************************************************
* Multi-Language definitions From Ahmed & Blume ICFP 2011                 *
* William J. Bowman, Phillip Mates & James T. Perconti                    *
***************************************************************************)
Require Import Core_Definitions Source_Definitions Target_Definitions LibWfenv Cps_Trans.

(* ********************************************************************** *)
(** * Description of the Language *)
Inductive st_type : typ -> Prop :=
| st_s_type : forall s, s_type s -> st_type s
| st_t_type : forall t, t_type t -> st_type t.

Hint Constructors st_type.

Inductive trans_type : typ -> Prop :=
| trans_s_type : forall s, s_type s -> trans_type s
| trans_t_type : forall s t, (s+) = t -> trans_type t.

(* this is wrong - need to actually copy the s_term and t_term rules
   so that boundaries can appear nested in any subexpression.
   several other definitions in this file have the same problem *)
Inductive st_term : trm -> Prop :=
| st_s_term : forall e, s_term e -> st_term e
| st_t_term : forall m, t_term m -> st_term m
| st_boundary_st_term : forall s m,
    s_type s -> t_term m -> st_term (s_trm_st m s)
| st_boundary_ts_term : forall L s e m,
    s_type s -> s_term e ->
    (forall x, x \notin L -> t_term (t_open_ee_var m x)) ->
    st_term (t_trm_ts e s m)

with st_value : trm -> Prop :=
| st_s_value : forall v, s_value v -> st_value v
| st_t_value : forall u, t_value u -> st_value u.

Scheme st_term_mut := Induction for st_term Sort Prop
with st_value_mut := Induction for st_value Sort Prop.

Hint Constructors st_term st_value.

Inductive st_eval_context : ctx -> Prop :=
  | st_eval_context_t : forall E,
      t_eval_context E -> st_eval_context E
  | st_eval_context_s : forall E,
      s_eval_context E -> st_eval_context E
  | st_eval_context_st_boundary : forall E s,
      s_type s -> t_eval_context E -> st_eval_context (s_ctx_st E s)
  | st_eval_context_ts_boundary : forall E s m,
      s_type s -> s_eval_context E -> st_eval_context (t_ctx_ts E s m).

(* reduction *)
(* TODO: move me later) *)
(* target level identity function *)
Definition t_id := (t_trm_abs (t_typ_bvar 0) (t_trm_bvar 0)).
Lemma IdTest : 
  t_eval (t_trm_app t_id t_typ_bool t_trm_false) t_trm_false.
Proof.
  Admitted.

Inductive st_red_base : trm -> trm -> Prop :=
  | st_red_base_st_true : st_red_base (s_trm_st t_trm_true s_typ_bool) s_trm_true
  | st_red_base_st_false : st_red_base (s_trm_st t_trm_false s_typ_bool) s_trm_false
  | st_red_base_st_abs : forall u s1 s2,
      s_type (s_typ_arrow s1 s2) -> t_value u ->
      st_red_base
        (s_trm_st u (s_typ_arrow s1 s2))
        (s_trm_abs s1 (s_trm_st
                       (t_trm_ts (t_trm_bvar 1) s1
                         (t_trm_app u (s2+) (t_trm_pair (t_trm_bvar 0) t_id)))
                       s2))
  | st_red_base_ts_true : forall m,
      st_term (t_trm_ts s_trm_true s_typ_bool m) ->
      st_red_base (t_trm_ts s_trm_true s_typ_bool m)
        (t_open_ee m t_trm_true)
  | st_red_base_ts_false : forall m,
      st_term (t_trm_ts s_trm_false s_typ_bool m) ->
      st_red_base (t_trm_ts s_trm_false s_typ_bool m)
        (t_open_ee m t_trm_false)
  | st_red_base_ts_abs : forall s1 s2 v m,
      s_type (s_typ_arrow s1 s2) ->
      st_term (t_trm_ts v (s_typ_arrow s1 s2) m) ->
      st_red_base (t_trm_ts v (s_typ_arrow s1 s2) m)
        (t_open_ee m
          (* λ [α] (x, k) . let z = (TS (v ST x)) in k [α] z *)
          (t_trm_abs
          (* (x,k) : (s1+, (s2+ → α)) *)
          (t_typ_pair (s1+) (t_typ_arrow (s2+) (t_typ_bvar 1)))
            (t_trm_let_fst (t_trm_bvar 0) (* let x = fst (x,k) in *)
              (t_trm_let_snd (t_trm_bvar 1) (* let k = snd (x,k) in *)
                (t_trm_ts
                  (s_trm_app v (s_trm_st (t_trm_bvar 1) s1)) (* let z = TS (v (ST x)) in *)
                  s2
                  (t_trm_app (t_trm_bvar 1) (t_typ_bvar 0) (t_trm_bvar 0))))))). (* k [α] z *)


Inductive st_red : trm -> trm -> Prop :=
  | t_red_ctx : forall E e e',
      t_red_base e e' -> t_eval_context E ->
      st_red (plug E e) (plug E e')
  | s_red_ctx : forall E e e',
      s_red_base e e' -> s_eval_context E ->
      st_red (plug E e) (plug E e')
  | st_red_ctx : forall E e e',
      st_red_base e e' -> st_eval_context E ->
      st_red (plug E e) (plug E e').

(** Typing relation *)
(* Delta;Gamma |- e:s *)
Inductive st_typing : env_type -> env_term -> trm -> typ -> Prop :=
| st_s_typing : forall G e s, s_typing G e s -> st_typing empty G e s
| st_t_typing : forall D G m t, t_typing D G m t -> st_typing D G m t
| st_boundary_st_typing : forall D G m s,
    st_typing D G m (s+) -> st_typing D G (s_trm_st m s) s
| st_boundary_ts_typing : forall L D G e m s t,
    st_typing D G e s -> 
    (forall x, x \notin L -> st_typing D (G & x ~ (s+)) (t_open_ee_var m x) t) ->
    st_typing D G (t_trm_ts e s m) t.

(* Examples *)
