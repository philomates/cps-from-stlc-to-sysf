(**************************************************************************
* Backtranslation from Ahmed & Blume ICFP 2011                            *
* William J. Bowman, Phillip Mates & James T. Perconti                    *
***************************************************************************)
Require Import Core_Definitions Source_Definitions Target_Definitions LibWfenv Cps_Trans Multi_Definitions.

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
    (forall x, x \notin L -> subformula (G & x ~ s1) (s_open_ee_var e x) s2) ->
    (trans_type s1) ->
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
    (forall x, x \notin L -> subformula (G & x ~ (s1+)) m (s2+)) ->
    subformula G
    (* λ[α] (y,k) . let x = TS STe in (k x) *)
    (t_trm_abs (t_typ_pair (s1+) (t_typ_arrow (s2+) (t_typ_bvar 1)))
      (t_trm_ts (s_trm_st m s)
        s
        (t_trm_let_snd (t_trm_bvar 0) (* let k = snd (x,k) in *)
        (t_trm_app (t_trm_bvar 0) (t_typ_bvar 0) (t_trm_bvar 1)))))
    ((s_typ_arrow s1 s2)+)
| sf_t_if : forall G u m1 m2 t,
    subformula G u t_typ_bool ->
    subformula G m1 t -> subformula G m2 t ->
    subformula G (t_trm_if u m1 m2) t
| sf_t_app : forall L G u1 u2a u2kontbody s s1 s2,
    subformula G u1 ((s_typ_arrow s1 s2)+) ->
    subformula G u2a (s1+) ->
    (forall x, x \notin L -> subformula (G & x ~ (s2+)) (t_open_ee_var u2kontbody x) (s+)) ->
    subformula G (t_trm_app u1 (s+) (t_trm_pair u2a (t_trm_abs (s2+) u2kontbody))) (s+)
(* boundary type *)
| sf_st : forall G m s,
    subformula G m (s+) -> subformula G (s_trm_st m s) s
| sf_ts : forall L G e m s t,
    subformula G e s ->
    (forall x, x \notin L -> subformula (G & x ~ (s+)) (t_open_ee_var m x) t) ->
    subformula G (t_trm_ts e s m) t.
