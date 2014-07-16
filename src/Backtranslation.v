(**************************************************************************
* Backtranslation from Ahmed & Blume ICFP 2011                            *
* William J. Bowman, Phillip Mates & James T. Perconti                    *
***************************************************************************)
Require Import Core_Definitions Source_Definitions Target_Definitions
               LibWfenv Cps_Trans_Definitions Multi_Definitions.

(* Subformula Property *)
Inductive subformula : env_term -> trm -> typ -> Prop :=
(* source type *)
| sf_s_var : forall G x s,
    wfenv trans_type G -> binds x s G -> subformula G (s_trm_fvar x) s
| sf_s_true : forall G,
    wfenv trans_type G -> subformula G s_trm_true s_typ_bool
| sf_s_false : forall G,
    wfenv trans_type G -> subformula G s_trm_false s_typ_bool
| sf_s_abs : forall L G e s1 s2,
    (forall x, x \notinLN L -> subformula (G & x ~ s1) (s_open_ee_var e x) s2) ->
    (s_type s1) ->
    subformula G (s_trm_abs s1 e) (s_typ_arrow s1 s2)
| sf_s_if : forall G e1 e2 e3 s,
    subformula G e1 s_typ_bool -> subformula G e2 s -> subformula G e3 s ->
    subformula G (s_trm_if e1 e2 e3) s
| sf_s_app : forall G e1 e2 s1 s2,
    subformula G e1 (s_typ_arrow s1 s2) -> subformula G e2 s1 ->
    subformula G (s_trm_app e1 e2) s2
(* trans type *)
| sf_t_var : forall G x t,
    wfenv trans_type G -> binds x t G ->
    subformula G (t_trm_fvar x) t
| sf_t_true : forall G,
    wfenv trans_type G -> subformula G t_trm_true t_typ_bool
| sf_t_false : forall G,
    wfenv trans_type G -> subformula G t_trm_false t_typ_bool
| sf_t_abs : forall L G m s s1 s2,
    wfenv trans_type G ->
    (* The follow may be wrong, we need to add the first projection of the functions argument to the context *)
    (forall x, x \notinLN L ->
      subformula (G & x ~ (t_typ_pair (s1+) (t_typ_arrow (s2+) (s2+)))) (t_open_ee_var m x) (s2+)) ->
    subformula G
    (* λ[α] (y,k) . let x = TS STe in (k x) *)
    (t_trm_abs (t_typ_pair (s1+) (t_typ_arrow (s2+) (t_typ_bvar 1)))
      (t_trm_ts (s_trm_st m s)
        s
        (t_trm_let_snd (t_trm_bvar 1) (* let k = snd (y,k) in *)
        (t_trm_app (t_trm_bvar 0) (t_typ_bvar 0) (t_trm_bvar 1)))))
    ((s_typ_arrow s1 s2)+)
| sf_t_if : forall G u m1 m2 t,
    subformula G u t_typ_bool ->
    subformula G m1 t -> subformula G m2 t ->
    subformula G (t_trm_if u m1 m2) t
| sf_t_app : forall L G u1 u2a u2kontbody s s1 s2,
    subformula G u1 ((s_typ_arrow s1 s2)+) ->
    subformula G u2a (s1+) ->
    (forall x, x \notinLN L -> subformula (G & x ~ (s2+)) (t_open_ee_var u2kontbody x) (s+)) ->
    subformula G (t_trm_app u1 (s+) (t_trm_pair u2a (t_trm_abs (s2+) u2kontbody))) (s+)
(* boundary type *)
| sf_st : forall G m s,
    subformula G m (s+) -> subformula G (s_trm_st m s) s
| sf_ts : forall L G e m s t,
    subformula G e s ->
    (forall x, x \notinLN L -> subformula (G & x ~ (s+)) (t_open_ee_var m x) t) ->
    subformula G (t_trm_ts e s m) t.

(* Partial reduction relation *)
Inductive partial_eval : env_term -> trm -> typ -> trm -> Prop :=
(* source type *)
| sf_s_var : forall G x s,
    wfenv trans_type G -> binds x s G -> partial_eval G (s_trm_fvar x) s (s_trm_fvar x)
| sf_s_true : forall G,
    wfenv trans_type G -> partial_eval G s_trm_true s_typ_bool s_trm_true
| sf_s_false : forall G,
    wfenv trans_type G -> partial_eval G s_trm_false s_typ_bool s_trm_false
| sf_s_abs : forall L G e ep s1 s2,
    (forall x, x \notinLN L -> partial_eval (G & x ~ s1) (s_open_ee_var e x) s2 (s_open_ee_var ep x)) ->
    (s_type s1) ->
    partial_eval G (s_trm_abs s1 e) (s_typ_arrow s1 s2) (s_trm_abs s1 ep)
| sf_s_if : forall G e1 e1p e2 e2p e3 e3p s,
    partial_eval G e1 s_typ_bool e1p -> partial_eval G e2 s e2p -> partial_eval G e3 s e3p ->
    partial_eval G (s_trm_if e1 e2 e3) s (s_trm_if e1p e2p e3p)
| sf_s_app : forall G e1 e1p e2 e2p s1 s2,
    partial_eval G e1 (s_typ_arrow s1 s2) e1p -> partial_eval G e2 s1 e2p ->
    partial_eval G (s_trm_app e1 e2) s2 (s_trm_app e1p e2p)
(* trans type *)
| sf_t_var : forall G x t,
    wfenv trans_type G -> binds x t G ->
    partial_eval G (t_trm_fvar x) t (t_trm_fvar x)
| sf_t_true : forall G,
    wfenv trans_type G -> partial_eval G t_trm_true t_typ_bool t_trm_true
| sf_t_false : forall G,
    wfenv trans_type G -> partial_eval G t_trm_false t_typ_bool t_trm_false
| sf_t_abs : forall L G m mp s s1 s2,
    wfenv trans_type G ->
    (forall y, y \notinLN L -> partial_eval (G & y ~ (s1+))
      (t_trm_let_fst (t_trm_bvar 0)
        (t_open_ee (t_open_ee (open_te m (s2+)) t_id)) y))
      (s2+) mp) ->
    partial_eval G
    (t_trm_abs (t_typ_pair (s1+) (t_typ_arrow (s2+) (t_typ_bvar 1)))
      (t_trm_let_fst (t_trm_bvar 0)
        (t_trm_let_snd (t_trm_bvar 1) m)))
    ((s_typ_arrow s1 s2)+)
    (* λ[α] (y,k) . let x = TS STe in (k x) *)
    (t_trm_abs (t_typ_pair (s1+) (t_typ_arrow (s2+) (t_typ_bvar 1)))
      (t_trm_ts (s_trm_st mp s)
        s
        (t_trm_let_snd (t_trm_bvar 0) (* let k = snd (x,k) in *)
        (t_trm_app (t_trm_bvar 0) (t_typ_bvar 0) (t_trm_bvar 1)))))
| sf_t_if : forall G u up m1 m1p m2 m2p t,
    partial_eval G u t_typ_bool up ->
    partial_eval G m1 t m1p -> partial_eval G m2 t m2p ->
    partial_eval G (t_trm_if u m1 m2) t (t_trm_if up m1p m2p)
| sf_t_app : forall L G u1 u1p u2a u2ap u2kontbody u2kontbodyp s s1 s2,
    partial_eval G u1 ((s_typ_arrow s1 s2)+) u1p ->
    partial_eval G u2a (s1+) u2ap ->
    (forall x, x \notinLN L -> partial_eval (G & x ~ (s2+)) (t_open_ee_var u2kontbody x) (s+)) (t_open_ee_var u2kontbodyp x)->
    partial_eval G (t_trm_app u1 (s+) (t_trm_pair u2a (t_trm_abs (s2+) u2kontbody))) (s+)
(* boundary type *)
| sf_st : forall G m mp s,
    partial_eval G m (s+) mp -> partial_eval G (s_trm_st m s) s (s_trm_st mp s)
| sf_ts : forall L G e ep m mp s t,
    partial_eval G e s ep ->
    (forall x, x \notinLN L -> partial_eval (G & x ~ (s+)) (t_open_ee_var m x) t (t_open_ee_var mp x)) ->
    partial_eval G (t_trm_ts e s m) t (t_trm_ts ep s mp).
