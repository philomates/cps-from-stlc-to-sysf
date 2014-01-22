(************************************************************
 * Core of source/target/combined language definitions      *
 *   Defines: pre-types (typ), pre-terms (trm),             *
 *            substitution for free/bound vars (open/subst) *
 *            pre-contexts (ctx), plug, ctx_open, ctx_subst *
 * from Ahmed & Blume ICFP 2011                             *
 * William J. Bowman, Phillip Mates & James T. Perconti     *
 ************************************************************)

Require Export LibLN.
Require Import EqNat.
Implicit Type x : var.
Implicit Type X : var.

(* flag for convenience later *)
Inductive lang : Set := source : lang | target : lang.

Definition beq_lang l1 l2 :=
  match (l1, l2) with
  | (source, source) => true
  | (target, target) => true
  | (_, _) => false
  end.

Definition inc_if_eq (l1 l2 : lang) : nat -> nat :=
  if beq_lang l1 l2 then S else id.

(*** Syntax of pre-types ***)

Inductive typ : Set :=
  (* Source types *)
  | s_typ_bool : typ                (* bool *)
  | s_typ_arrow : typ -> typ -> typ (* s -> s *)

  (* Target types *)
  | t_typ_bvar : nat -> typ         (* N *)
  | t_typ_fvar : var -> typ         (* X *)
  | t_typ_bool : typ                (* bool *)
  | t_typ_pair : typ -> typ -> typ  (* t x t *)
  | t_typ_arrow : typ -> typ -> typ (* forall . t -> t *)

  (* error case *)
  | typ_bad : typ.

(*** Syntax of pre-terms ***)

Inductive trm : Set :=
  (* source values *)
  | s_trm_bvar : nat -> trm             (* n *)
  | s_trm_fvar : var -> trm             (* x *)
  | s_trm_true : trm                    (* tt *)
  | s_trm_false : trm                   (* ff *)
  | s_trm_abs : typ -> trm -> trm       (* lambda : s . e *)
  (* source non-values *)
  | s_trm_if : trm -> trm -> trm -> trm (* if e e e *)
  | s_trm_app : trm -> trm -> trm       (* e e *)

  (* target values *)
  | t_trm_bvar  : nat -> trm               (* n *)
  | t_trm_fvar  : var -> trm               (* x *)
  | t_trm_true  : trm                      (* tt *)
  | t_trm_false : trm                      (* ff *)
  | t_trm_pair  : trm -> trm -> trm        (* (u, u) *)
  | t_trm_abs   : typ -> trm -> trm        (* Lambda . lambda : t . m *)
  (* target non-values *)
  | t_trm_if    : trm -> trm -> trm -> trm (* if u m m *)
  | t_trm_let_fst : trm -> trm -> trm      (* let  = fst u in m *)
  | t_trm_let_snd : trm -> trm -> trm      (* let  = snd u in m *)
  | t_trm_app   : trm -> typ -> trm -> trm (* u [t] u *)

  (* Boundary Terms *)
  | s_trm_st : trm -> typ -> trm         (* (s) ST m *)
  | t_trm_ts : trm -> typ -> trm -> trm  (* let  = TS (s) e in m *)

  (* error case *)
  | trm_bad.

(*** Substitution for (type and term) bvars ***)

(* Opening up a type binder occuring in a type *)
Fixpoint open_tt_rec (K : nat) (t' : typ) (t : typ) : typ :=
  match t with
  (* no type variables in source types *)
  | s_typ_bool        => t
  | s_typ_arrow _ _   => t
  (* target types *)
  | t_typ_bvar N      => if beq_nat K N then t' else (t_typ_bvar N)
  | t_typ_fvar X      => t_typ_fvar X
  | t_typ_bool        => t_typ_bool
  | t_typ_pair t1 t2  => t_typ_pair (open_tt_rec K t' t1)
                                    (open_tt_rec K t' t2)
     (* t_typ_arrow is the binding form for type variables *)
  | t_typ_arrow t1 t2 => t_typ_arrow (open_tt_rec (S K) t' t1)
                                     (open_tt_rec (S K) t' t2)
  (* blah *)
  | typ_bad => typ_bad
  end.

(** Opening up a type binder occuring in a term *)
Fixpoint open_te_rec (K : nat) (t' : typ) (e : trm) : trm :=
  match e with
  (* source terms *)
  | s_trm_bvar n      => s_trm_bvar n
  | s_trm_fvar x      => s_trm_fvar x
  | s_trm_true        => s_trm_true
  | s_trm_false       => s_trm_false
  | s_trm_abs s e     => s_trm_abs s (open_te_rec K t' e)
  | s_trm_if e1 e2 e3 => s_trm_if (open_te_rec K t' e1)
                                  (open_te_rec K t' e2)
                                  (open_te_rec K t' e3)
  | s_trm_app e1 e2   => s_trm_app (open_te_rec K t' e1)
                                   (open_te_rec K t' e2)
  | s_trm_st m s      => s_trm_st (open_te_rec K t' m) s
  (* target terms *)
  | t_trm_bvar i      => t_trm_bvar i
  | t_trm_fvar x      => t_trm_fvar x
  | t_trm_true        => t_trm_true
  | t_trm_false       => t_trm_false
  | t_trm_pair u1 u2  => t_trm_pair (open_te_rec K t' u1)
                                    (open_te_rec K t' u2)
     (* t_trm_abs is the only term-level form that binds a type variable *)
  | t_trm_abs t m     => t_trm_abs (open_tt_rec (S K) t' t)
                                   (open_te_rec (S K) t' m)
  | t_trm_if u m1 m2  => t_trm_if (open_te_rec K t' u)
                                  (open_te_rec K t' m1)
                                  (open_te_rec K t' m2)
  | t_trm_let_fst u m => t_trm_let_fst (open_te_rec K t' u)
                                       (open_te_rec K t' m)
  | t_trm_let_snd u m => t_trm_let_snd (open_te_rec K t' u)
                                       (open_te_rec K t' m)
  | t_trm_app m1 t m2 => t_trm_app (open_te_rec K t' m1)
                                   (open_tt_rec K t' t)
                                   (open_te_rec K t' m2)
  | t_trm_ts e s m    => t_trm_ts (open_te_rec K t' e) s (open_te_rec K t' m)
  (* blah *)
  | trm_bad => trm_bad
  end.

(** Opening up a term binder appearing in a term *)
Fixpoint open_ee_rec (l : lang) (k : nat) (e' : trm) (e : trm) : trm :=
  match e with
  (* source terms *)
  | s_trm_bvar i      => if andb (beq_lang l source) (beq_nat k i)
                         then e'
                         else (s_trm_bvar i)
  | s_trm_fvar x      => s_trm_fvar x
  | s_trm_true        => s_trm_true
  | s_trm_false       => s_trm_false
  | s_trm_abs s e     => s_trm_abs s
                                   (open_ee_rec l (inc_if_eq l source k) e' e)
  | s_trm_if e1 e2 e3 => s_trm_if (open_ee_rec l k e' e1)
                                  (open_ee_rec l k e' e2)
                                  (open_ee_rec l k e' e3)
  | s_trm_app e1 e2   => s_trm_app (open_ee_rec l k e' e1)
                                   (open_ee_rec l k e' e2)
  | s_trm_st m s      => s_trm_st (open_ee_rec l k e' m) s
  (* target terms *)
  | t_trm_bvar i      => if andb (beq_lang l target) (beq_nat k i)
                         then e'
                         else t_trm_bvar i
  | t_trm_fvar x      => t_trm_fvar x
  | t_trm_true        => t_trm_true
  | t_trm_false       => t_trm_false
  | t_trm_pair u1 u2  => t_trm_pair (open_ee_rec l k e' u1)
                                    (open_ee_rec l k e' u2)
  | t_trm_abs t m     => t_trm_abs t (open_ee_rec l (inc_if_eq l target k) e' m)
  | t_trm_if u m1 m2  => t_trm_if (open_ee_rec l k e' u)
                                  (open_ee_rec l k e' m1)
                                  (open_ee_rec l k e' m2)
  | t_trm_let_fst u m => t_trm_let_fst (open_ee_rec l k e' u)
                                       (open_ee_rec l
                                         (inc_if_eq l target k) e' m)
  | t_trm_let_snd u m => t_trm_let_snd (open_ee_rec l k e' u)
                                       (open_ee_rec l
                                         (inc_if_eq l target k) e' m)
  | t_trm_app m1 t m2 => t_trm_app (open_ee_rec l k e' m1)
                                   t
                                   (open_ee_rec l k e' m2)
  | t_trm_ts e s m    => t_trm_ts (open_ee_rec l k e' e)
                                  s
                                  (open_ee_rec l (inc_if_eq l target k) e' m)
  (* blah *)
  | trm_bad => trm_bad
  end.

Notation "< t { t' / K }>" := (open_tt_rec K t' t).
Notation "< e { t / K }>" := (open_te_rec K t e).
Notation "< e [ e' / k ]>" := (open_ee_rec target k e' e).

Notation open_tt := (fun t t' => open_tt_rec 0 t' t). (* t [t' / 0] *)
Notation open_te := (fun e t' => open_te_rec 0 t' e). (* e [t' / 0] *)
Notation s_open_ee := (fun e e' => open_ee_rec source 0 e' e). (* e [e' / 0] *)
Notation t_open_ee := (fun e m' => open_ee_rec target 0 m' e). (* e [m' / 0] *)

Notation open_tt_var := (fun t X => open_tt t (t_typ_fvar X)).
Notation open_te_var := (fun e X => open_te e (t_typ_fvar X)).
Notation s_open_ee_var := (fun e x => s_open_ee e (s_trm_fvar x)).
Notation t_open_ee_var := (fun e x => t_open_ee e (t_trm_fvar x)).

(*** Environments and Substitutions ***)

(* an env_type is a set of type variables with their kinds *)
Definition env_type := LibEnv.env unit. (* Delta *)
Definition star := tt. (* base kind '*' that all types share *)

(* an env_term is a set of term variables with their types *)
Definition env_term := LibEnv.env typ.  (* Gamma *)

(* a subst_type is a mapping (substitution) from type variables to types *)
Definition subst_type := LibEnv.env typ. (* delta *)

(* a subst_term is a mapping (substitution) from term variables to terms *)
Definition subst_term := LibEnv.env trm. (* gamma *)

(** apply a subst_type in a type *)
Fixpoint subst_tt (d : subst_type) (t : typ) :=
  match t with
  (* no type variables in source types *)
  | s_typ_bool        => t
  | s_typ_arrow _ _   => t
  (* target types *)
  | t_typ_bvar N      => t_typ_bvar N
  | t_typ_fvar X      => match get X d with None => t_typ_fvar X
                           | Some t => t end
  | t_typ_bool        => t_typ_bool
  | t_typ_pair t1 t2  => t_typ_pair (subst_tt d t1) (subst_tt d t2)
  | t_typ_arrow t1 t2 => t_typ_arrow (subst_tt d t1) (subst_tt d t2)
  (* blah *)
  | typ_bad => typ_bad
  end.

(** apply a subst_type in a term *)
Fixpoint subst_te (d : subst_type) (e : trm) :=
  match e with
    | s_trm_bvar n      => s_trm_bvar n
    | s_trm_fvar x      => s_trm_fvar x
    | s_trm_true        => s_trm_true
    | s_trm_false       => s_trm_false
    | s_trm_abs s e     => s_trm_abs s (subst_te d e)
    | s_trm_if e1 e2 e3 => s_trm_if (subst_te d e1)
                                    (subst_te d e2)
                                    (subst_te d e3)
    | s_trm_app e1 e2   => s_trm_app (subst_te d e1) (subst_te d e2)
    | s_trm_st m s      => s_trm_st (subst_te d m) s

    | t_trm_bvar n      => t_trm_bvar n
    | t_trm_fvar x      => t_trm_fvar x
    | t_trm_true        => t_trm_true
    | t_trm_false       => t_trm_false
    | t_trm_pair u1 u2  => t_trm_pair (subst_te d u1) (subst_te d u2)
    | t_trm_abs t m     => t_trm_abs (subst_tt d t) (subst_te d m)
    | t_trm_if u m1 m2  => t_trm_if (subst_te d u)
                                    (subst_te d m1)
                                    (subst_te d m2)
    | t_trm_let_fst u m => t_trm_let_fst (subst_te d u) (subst_te d m)
    | t_trm_let_snd u m => t_trm_let_snd (subst_te d u) (subst_te d m)
    | t_trm_app m1 t m2 => t_trm_app (subst_te d m1)
                                     (subst_tt d t)
                                     (subst_te d m2)
    | t_trm_ts e s m    => t_trm_ts (subst_te d e) s (subst_te d m)
    | trm_bad => trm_bad
  end.


(** apply a subst_term in a term *)
(* This definition only allows us to apply single-language substitutions.
   Since envs are not tagged with the language of the vars in their domains,
   we have to be careful about which language variables are in. *)
Fixpoint subst_ee (l : lang) (g : subst_term) (e : trm) :=
  match e with
    | s_trm_bvar n      => s_trm_bvar n
    | s_trm_fvar x      => if beq_lang l source
                           then match get x g with
                                  | Some v => v
                                  | None => s_trm_fvar x end
                           else s_trm_fvar x
    | s_trm_true        => s_trm_true
    | s_trm_false       => s_trm_false
    | s_trm_abs s e     => s_trm_abs s (subst_ee l g e)
    | s_trm_if e1 e2 e3 => s_trm_if (subst_ee l g e1)
                                    (subst_ee l g e2)
                                    (subst_ee l g e3)
    | s_trm_app e1 e2   => s_trm_app (subst_ee l g e1) (subst_ee l g e2)
    | s_trm_st m s      => s_trm_st (subst_ee l g m) s

    | t_trm_bvar n      => t_trm_bvar n
    | t_trm_fvar x      => if beq_lang l target
                           then match get x g with
                             | Some v => v
                             | None => t_trm_fvar x end
                           else t_trm_fvar x
    | t_trm_true        => t_trm_true
    | t_trm_false       => t_trm_false
    | t_trm_pair u1 u2  => t_trm_pair (subst_ee l g u1) (subst_ee l g u2)
    | t_trm_abs t m     => t_trm_abs t (subst_ee l g m)
    | t_trm_if u m1 m2  => t_trm_if (subst_ee l g u)
                                    (subst_ee l g m1)
                                    (subst_ee l g m2)
    | t_trm_let_fst u m => t_trm_let_fst (subst_ee l g u) (subst_ee l g m)
    | t_trm_let_snd u m => t_trm_let_snd (subst_ee l g u) (subst_ee l g m)
    | t_trm_app m1 t m2 => t_trm_app (subst_ee l g m1) t (subst_ee l g m2)
    | t_trm_ts e s m    => t_trm_ts (subst_ee l g e) s (subst_ee l g m)
    | trm_bad => trm_bad
  end.

Notation s_subst_ee := (subst_ee source).
Notation t_subst_ee := (subst_ee target).

Notation "tt[ t' / X ] t" := (subst_tt (X ~ t') t) (at level 75).
Notation "te[ t' / X ] m" := (subst_te (X ~ t') m) (at level 75).

(*** Contexts ***)

Inductive ctx : Set :=
  (* Source *)
  (* evaluation and general contexts *)
  | s_ctx_hole : ctx                          (* [] *)
  | s_ctx_if : ctx -> trm -> trm -> ctx       (* if E e e *)
  | s_ctx_app1 : ctx -> trm -> ctx            (* E e *)
  | s_ctx_app2 : trm -> ctx -> ctx            (* v E / e C *)
  (* general contexts only *)
  | s_ctx_abs : typ -> ctx -> ctx             (* lambda : s . C *)
  | s_ctx_if_true : trm -> ctx -> trm -> ctx  (* if e C e *)
  | s_ctx_if_false : trm -> trm -> ctx -> ctx (* if e e C *)

  (* Target *)
  (* evaluation, value, term contexts *)
  | t_ctx_hole : ctx                          (* [] *)
  (* value and term contexts *)
  | t_ctx_pair_left : ctx -> trm -> ctx       (* (Cval, u) *)
  | t_ctx_pair_right : trm -> ctx -> ctx      (* (u, Cval) *)
  | t_ctx_abs : typ -> ctx -> ctx             (* Lambda . lambda : t . C *)
  (* term contexts *)
  | t_ctx_if : ctx -> trm -> trm -> ctx       (* if Cval m m *)
  | t_ctx_if_true : trm -> ctx -> trm -> ctx  (* if m C m *)
  | t_ctx_if_false : trm -> trm -> ctx -> ctx (* if m m C *)
  | t_ctx_let_fst : ctx -> trm -> ctx         (* let  = fst Cval in m *)
  | t_ctx_let_fst_k : trm -> ctx -> ctx       (* let  = fst m in C *)
  | t_ctx_let_snd : ctx -> trm -> ctx         (* let  = snd Cval in m *)
  | t_ctx_let_snd_k : trm -> ctx -> ctx       (* let  = snd Cval in m *)
  | t_ctx_app1 : ctx -> typ -> trm -> ctx     (* Cval t v *)
  | t_ctx_app2 : trm -> typ -> ctx -> ctx     (* v t Cval *)

  (* Boundaries *)
  (* evaluation and general contexts *)
  | s_ctx_st : ctx -> typ -> ctx              (* s ST E *)
  | t_ctx_ts : ctx -> typ -> trm -> ctx       (* let  = (TS s E) in m *)
  (* general contexts only *)
  | t_ctx_ts_k : trm -> typ -> ctx -> ctx     (* let  = (TS s e) in C *).

(* Fill a context with a term *)
Fixpoint plug (C : ctx) (e : trm) : trm :=
  match C with
  | s_ctx_hole              => e
  | s_ctx_if C' e2 e3       => s_trm_if (plug C' e) e2 e3
  | s_ctx_app1 C' e'        => s_trm_app (plug C' e) e'
  | s_ctx_app2 e' C'        => s_trm_app e' (plug C' e)
  | s_ctx_abs s C'          => s_trm_abs s (plug C' e)
  | s_ctx_if_true e1 C' e3  => s_trm_if e1 (plug C' e) e3
  | s_ctx_if_false e1 e2 C' => s_trm_if e1 e2 (plug C' e)
  | s_ctx_st C' s           => s_trm_st (plug C' e) s

  | t_ctx_hole              => e
  | t_ctx_pair_left C' m'   => t_trm_pair (plug C' e) m'
  | t_ctx_pair_right m' C'  => t_trm_pair m' (plug C' e)
  | t_ctx_abs t C'          => t_trm_abs t (plug C' e)
  | t_ctx_if C' m2 m3       => t_trm_if (plug C' e) m2 m3
  | t_ctx_if_true m1 C' m2  => t_trm_if m1 (plug C' e) m2
  | t_ctx_if_false m1 m2 C' => t_trm_if m1 m2 (plug C' e)
  | t_ctx_let_fst C' m'     => t_trm_let_fst (plug C' e) m'
  | t_ctx_let_fst_k m' C'   => t_trm_let_fst m' (plug C' e)
  | t_ctx_let_snd C' m'     => t_trm_let_snd (plug C' e) m'
  | t_ctx_let_snd_k m' C'   => t_trm_let_snd m' (plug C' e)
  | t_ctx_app1 C' t m1      => t_trm_app (plug C' e) t m1
  | t_ctx_app2 m1 t C'      => t_trm_app m1 t (plug C' e)
  | t_ctx_ts C' s m'        => t_trm_ts (plug C' e) s m'
  | t_ctx_ts_k e' s C'      => t_trm_ts e' s (plug C' e)
  end.

(** Opening for contexts *)
Fixpoint ctx_open_te_rec (K : nat) (t' : typ) (C : ctx) {struct C} : ctx :=
  match C with
  (* source contexts *)
  | s_ctx_hole             => s_ctx_hole
  | s_ctx_if C e2 e3       => s_ctx_if (ctx_open_te_rec K t' C)
                                       (open_te_rec K t' e2)
                                       (open_te_rec K t' e3)
  | s_ctx_app1 C e         => s_ctx_app1 (ctx_open_te_rec K t' C)
                                         (open_te_rec K t' e)
  | s_ctx_app2 e C         => s_ctx_app2 (open_te_rec K t' e)
                                         (ctx_open_te_rec K t' C)
  | s_ctx_abs s C          => s_ctx_abs s (ctx_open_te_rec K t' C)
  | s_ctx_if_true e1 C e3  => s_ctx_if_true (open_te_rec K t' e1)
                                            (ctx_open_te_rec K t' C)
                                            (open_te_rec K t' e3)
  | s_ctx_if_false e1 e2 C => s_ctx_if_false (open_te_rec K t' e1)
                                             (open_te_rec K t' e2)
                                             (ctx_open_te_rec K t' C)
  | s_ctx_st C s           => s_ctx_st (ctx_open_te_rec K t' C) s
  (* target contexts *)
  | t_ctx_hole             => t_ctx_hole
  | t_ctx_pair_left C m    => t_ctx_pair_left (ctx_open_te_rec K t' C)
                                              (open_te_rec K t' m)
  | t_ctx_pair_right m C   => t_ctx_pair_right (open_te_rec K t' m)
                                               (ctx_open_te_rec K t' C)
     (* only binding form for type variables *)
  | t_ctx_abs t C          => t_ctx_abs (open_tt_rec (S K) t' t)
                                        (ctx_open_te_rec (S K) t' C)
  | t_ctx_if C m1 m2       => t_ctx_if (ctx_open_te_rec K t' C)
                                       (open_te_rec K t' m1)
                                       (open_te_rec K t' m2)
  | t_ctx_if_true m1 C m2  => t_ctx_if_true (open_te_rec K t' m1)
                                            (ctx_open_te_rec K t' C)
                                            (open_te_rec K t' m2)
  | t_ctx_if_false m1 m2 C => t_ctx_if_false (open_te_rec K t' m1)
                                             (open_te_rec K t' m2)
                                             (ctx_open_te_rec K t' C)
  | t_ctx_let_fst C m      => t_ctx_let_fst (ctx_open_te_rec K t' C)
                                            (open_te_rec K t' m)
  | t_ctx_let_fst_k m C    => t_ctx_let_fst_k (open_te_rec K t' m)
                                              (ctx_open_te_rec K t' C)
  | t_ctx_let_snd C m      => t_ctx_let_snd (ctx_open_te_rec K t' C)
                                            (open_te_rec K t' m)
  | t_ctx_let_snd_k m C    => t_ctx_let_snd_k (open_te_rec K t' m)
                                              (ctx_open_te_rec K t' C)
  | t_ctx_app1 C t m       => t_ctx_app1 (ctx_open_te_rec K t' C)
                                         (open_tt_rec K t' t)
                                         (open_te_rec K t' m)
  | t_ctx_app2 m t C       => t_ctx_app2 (open_te_rec K t' m)
                                         (open_tt_rec K t' t)
                                         (ctx_open_te_rec K t' C)
  | t_ctx_ts C s m         => t_ctx_ts (ctx_open_te_rec K t' C)
                                       s
                                       (open_te_rec K t' m)
  | t_ctx_ts_k e s C       => t_ctx_ts_k (open_te_rec K t' e)
                                         s
                                         (ctx_open_te_rec K t' C)
  end.

Fixpoint ctx_open_ee_rec (l : lang) (K : nat) (e' : trm) (C : ctx) : ctx :=
  match C with
  (* source contexts *)
  | s_ctx_hole             => s_ctx_hole
  | s_ctx_if C e2 e3       => s_ctx_if (ctx_open_ee_rec l K e' C)
                                       (open_ee_rec l K e' e2)
                                       (open_ee_rec l K e' e3)
  | s_ctx_app1 C e         => s_ctx_app1 (ctx_open_ee_rec l K e' C)
                                         (open_ee_rec l K e' e)
  | s_ctx_app2 e C         => s_ctx_app2 (open_ee_rec l K e' e)
                                         (ctx_open_ee_rec l K e' C)
  | s_ctx_abs s C          => s_ctx_abs s
                                        (ctx_open_ee_rec l
                                          (inc_if_eq l source K) e' C)
  | s_ctx_if_true e1 C e3  => s_ctx_if_true (open_ee_rec l K e' e1)
                                            (ctx_open_ee_rec l K e' C)
                                            (open_ee_rec l K e' e3)
  | s_ctx_if_false e1 e2 C => s_ctx_if_false (open_ee_rec l K e' e1)
                                             (open_ee_rec l K e' e2)
                                             (ctx_open_ee_rec l K e' C)
  | s_ctx_st C s           => s_ctx_st (ctx_open_ee_rec l K e' C) s
  (* target contexts *)
  | t_ctx_hole             => t_ctx_hole
  | t_ctx_pair_left C m    => t_ctx_pair_left (ctx_open_ee_rec l K e' C)
                                              (open_ee_rec l K e' m)
  | t_ctx_pair_right m C   => t_ctx_pair_right (open_ee_rec l K e' m)
                                               (ctx_open_ee_rec l K e' C)
  | t_ctx_abs t C          => t_ctx_abs t
                                        (ctx_open_ee_rec l
                                          (inc_if_eq l target K) e' C)
  | t_ctx_if C m1 m2       => t_ctx_if (ctx_open_ee_rec l K e' C)
                                       (open_ee_rec l K e' m1)
                                       (open_ee_rec l K e' m2)
  | t_ctx_if_true m1 C m2  => t_ctx_if_true (open_ee_rec l K e' m1)
                                            (ctx_open_ee_rec l K e' C)
                                            (open_ee_rec l K e' m2)
  | t_ctx_if_false m1 m2 C => t_ctx_if_false (open_ee_rec l K e' m1)
                                             (open_ee_rec l K e' m2)
                                             (ctx_open_ee_rec l K e' C)
  | t_ctx_let_fst C m      => t_ctx_let_fst (ctx_open_ee_rec l K e' C)
                                            (open_ee_rec l
                                              (inc_if_eq l target K) e' m)
  | t_ctx_let_fst_k m C    => t_ctx_let_fst_k (open_ee_rec l K e' m)
                                              (ctx_open_ee_rec l
                                                (inc_if_eq l target K) e' C)
  | t_ctx_let_snd C m      => t_ctx_let_snd (ctx_open_ee_rec l K e' C)
                                            (open_ee_rec l
                                              (inc_if_eq l target K) e' m)
  | t_ctx_let_snd_k m C    => t_ctx_let_snd_k (open_ee_rec l K e' m)
                                              (ctx_open_ee_rec l
                                                (inc_if_eq l target K) e' C)
  | t_ctx_app1 C t m       => t_ctx_app1 (ctx_open_ee_rec l K e' C) t
                                         (open_ee_rec l K e' m)
  | t_ctx_app2 m t C       => t_ctx_app2 (open_ee_rec l K e' m) t
                                         (ctx_open_ee_rec l K e' C)
  | t_ctx_ts C s m         => t_ctx_ts (ctx_open_ee_rec l K e' C)
                                       s
                                       (open_ee_rec l
                                         (inc_if_eq l target K) e' m)
  | t_ctx_ts_k e s C       => t_ctx_ts_k (open_ee_rec l K e' e)
                                         s
                                         (ctx_open_ee_rec l
                                           (inc_if_eq l target K) e' C)
  end.

Notation ctx_open_te := (fun C t' => ctx_open_te_rec 0 t' C).
Notation s_ctx_open_ee := (fun C e' => ctx_open_ee_rec source 0 e' C).
Notation t_ctx_open_ee := (fun C m' => ctx_open_ee_rec target 0 m' C).

Notation ctx_open_te_var := (fun C X => ctx_open_te C (t_typ_fvar X)).
Notation s_ctx_open_ee_var := (fun C x => s_ctx_open_ee C (s_trm_fvar x)).
Notation t_ctx_open_ee_var := (fun C x => t_ctx_open_ee C (t_trm_fvar x)).

(** subst for contexts *)

Fixpoint ctx_subst_te (d : subst_type) (C : ctx) :=
  match C with
  (* source contexts *)
  | s_ctx_hole             => s_ctx_hole
  | s_ctx_if C e2 e3       => s_ctx_if (ctx_subst_te d C)
                                       (subst_te d e2)
                                       (subst_te d e3)
  | s_ctx_app1 C e         => s_ctx_app1 (ctx_subst_te d C) (subst_te d e)
  | s_ctx_app2 e C         => s_ctx_app2 (subst_te d e) (ctx_subst_te d C)
  | s_ctx_abs s C          => s_ctx_abs s (ctx_subst_te d C)
  | s_ctx_if_true e1 C e3  => s_ctx_if_true (subst_te d e1)
                                            (ctx_subst_te d C)
                                            (subst_te d e3)
  | s_ctx_if_false e1 e2 C => s_ctx_if_false (subst_te d e1)
                                             (subst_te d e2)
                                             (ctx_subst_te d C)
  | s_ctx_st C s           => s_ctx_st (ctx_subst_te d C) s
  (* target contexts *)
  | t_ctx_hole             => t_ctx_hole
  | t_ctx_pair_left C m    => t_ctx_pair_left (ctx_subst_te d C) (subst_te d m)
  | t_ctx_pair_right m C   => t_ctx_pair_right (subst_te d m) (ctx_subst_te d C)
  | t_ctx_abs t C          => t_ctx_abs (subst_tt d t) (ctx_subst_te d C)
  | t_ctx_if C m1 m2       => t_ctx_if (ctx_subst_te d C)
                                       (subst_te d m1)
                                       (subst_te d m2)
  | t_ctx_if_true m1 C m2  => t_ctx_if_true (subst_te d m1)
                                            (ctx_subst_te d C)
                                            (subst_te d m2)
  | t_ctx_if_false m1 m2 C => t_ctx_if_false (subst_te d m1)
                                             (subst_te d m2)
                                             (ctx_subst_te d C)
  | t_ctx_let_fst C m      => t_ctx_let_fst (ctx_subst_te d C) (subst_te d m)
  | t_ctx_let_fst_k m C    => t_ctx_let_fst_k (subst_te d m) (ctx_subst_te d C)
  | t_ctx_let_snd C m      => t_ctx_let_snd (ctx_subst_te d C) (subst_te d m)
  | t_ctx_let_snd_k m C    => t_ctx_let_snd_k (subst_te d m) (ctx_subst_te d C)
  | t_ctx_app1 C t m       => t_ctx_app1 (ctx_subst_te d C)
                                         (subst_tt d t)
                                         (subst_te d m)
  | t_ctx_app2 m t C       => t_ctx_app2 (subst_te d m)
                                         (subst_tt d t)
                                         (ctx_subst_te d C)
  | t_ctx_ts C s m         => t_ctx_ts (ctx_subst_te d C) s (subst_te d m)
  | t_ctx_ts_k e s C       => t_ctx_ts_k (subst_te d e) s (ctx_subst_te d C)
  end.

Fixpoint ctx_subst_ee (l : lang) (g : subst_term) (C : ctx) :=
  match C with
  (* source contexts *)
  | s_ctx_hole             => s_ctx_hole
  | s_ctx_if C e2 e3       => s_ctx_if (ctx_subst_ee l g C)
                                       (subst_ee l g e2)
                                       (subst_ee l g e3)
  | s_ctx_app1 C e         => s_ctx_app1 (ctx_subst_ee l g C) (subst_ee l g e)
  | s_ctx_app2 e C         => s_ctx_app2 (subst_ee l g e) (ctx_subst_ee l g C)
  | s_ctx_abs s C          => s_ctx_abs s (ctx_subst_ee l g C)
  | s_ctx_if_true e1 C e3  => s_ctx_if_true (subst_ee l g e1)
                                            (ctx_subst_ee l g C)
                                            (subst_ee l g e3)
  | s_ctx_if_false e1 e2 C => s_ctx_if_false (subst_ee l g e1)
                                             (subst_ee l g e2)
                                             (ctx_subst_ee l g C)
  | s_ctx_st C s           => s_ctx_st (ctx_subst_ee l g C) s
  (* target contexts *)
  | t_ctx_hole             => t_ctx_hole
  | t_ctx_pair_left C m    => t_ctx_pair_left (ctx_subst_ee l g C)
                                              (subst_ee l g m)
  | t_ctx_pair_right m C   => t_ctx_pair_right (subst_ee l g m)
                                               (ctx_subst_ee l g C)
  | t_ctx_abs t C          => t_ctx_abs t (ctx_subst_ee l g C)
  | t_ctx_if C m1 m2       => t_ctx_if (ctx_subst_ee l g C)
                                       (subst_ee l g m1)
                                       (subst_ee l g m2)
  | t_ctx_if_true m1 C m2  => t_ctx_if_true (subst_ee l g m1)
                                            (ctx_subst_ee l g C)
                                            (subst_ee l g m2)
  | t_ctx_if_false m1 m2 C => t_ctx_if_false (subst_ee l g m1)
                                             (subst_ee l g m2)
                                             (ctx_subst_ee l g C)
  | t_ctx_let_fst C m      => t_ctx_let_fst (ctx_subst_ee l g C)
                                            (subst_ee l g m)
  | t_ctx_let_fst_k m C    => t_ctx_let_fst_k (subst_ee l g m)
                                              (ctx_subst_ee l g C)
  | t_ctx_let_snd C m      => t_ctx_let_snd (ctx_subst_ee l g C)
                                            (subst_ee l g m)
  | t_ctx_let_snd_k m C    => t_ctx_let_snd_k (subst_ee l g m)
                                              (ctx_subst_ee l g C)
  | t_ctx_app1 C t m       => t_ctx_app1 (ctx_subst_ee l g C) t
                                         (subst_ee l g m)
  | t_ctx_app2 m t C       => t_ctx_app2 (subst_ee l g m) t
                                         (ctx_subst_ee l g C)
  | t_ctx_ts C s m         => t_ctx_ts (ctx_subst_ee l g C)
                                       s
                                       (subst_ee l g m)
  | t_ctx_ts_k e s C       => t_ctx_ts_k (subst_ee l g e)
                                         s
                                         (ctx_subst_ee l g C)
  end.

Notation s_ctx_subst_ee := (ctx_subst_ee source).
Notation t_ctx_subst_ee := (ctx_subst_ee target).
