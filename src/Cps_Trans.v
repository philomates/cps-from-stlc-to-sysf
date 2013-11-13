Require Import LibWfenv Core_Infrastructure
               Source_Definitions Target_Definitions
               Source_Properties Target_Properties.

(* for applications where the type argument is irrelevant *)
Definition dummy_type := t_typ_bool.

Fixpoint cps_type_trans (s:typ) :=
  match s with
    | s_typ_bool => t_typ_bool
    | s_typ_arrow s1 s2 =>
      t_typ_arrow (t_typ_pair (cps_type_trans s1)
                              (t_typ_arrow (cps_type_trans s2) (t_typ_bvar 1)))
                  (t_typ_bvar 0)
    | _ => typ_bad
  end.

Notation "( s +)" := (cps_type_trans s) (at level 0).

Lemma cps_type_trans_preserves_well_formed_types : forall s,
  s_type s -> t_type (s+).
Proof.
  induction 1; auto.
  simpl. apply_fresh t_type_arrow as X; simpl; auto.
  apply t_type_pair; rewrite* open_tt_rec_t_type.
  apply_fresh t_type_arrow as Y; rewrite* open_tt_rec_t_type.
Qed.

Definition cps_type_trans_computation (s : typ) :=
  t_typ_arrow (t_typ_arrow (s+) (t_typ_bvar 1)) (t_typ_bvar 0).

Notation "( s %)" := (cps_type_trans_computation s) (at level 0).

Inductive cps_trans (G:env_term) (e:trm) (s:typ) (m:trm) : Prop :=
  | cps_trans_var : forall G x s, wfenv s_type G ->
    cps_trans G (s_trm_fvar x) s
      (t_trm_abs (t_typ_arrow (s+) (t_typ_bvar 1))
        (t_trm_app (t_trm_bvar 0) dummy_type (t_trm_fvar x)))
  | cps_trans_true : forall G x s, wfenv s_type G ->
    cps_trans G s_trm_true s
      (t_trm_abs (t_typ_arrow t_typ_bool (t_typ_bvar 1))
        (t_trm_app (t_trm_bvar 0) dummy_type t_trm_true))
  | cps_trans_false : forall G x s, wfenv s_type G ->
    cps_trans G s_trm_false s
      (t_trm_abs (t_typ_arrow t_typ_bool (t_typ_bvar 1))
        (t_trm_app (t_trm_bvar 0) dummy_type t_trm_false))
  | cps_trans_abs : forall L G e s1 s2 u,
      (forall x, x \notin L -> cps_trans (G & x ~ s1) (s_open_ee_var e x) s2 u) ->
      s_type s1 ->
      cps_trans G (s_trm_abs s1 e) (s_typ_arrow s1 s2)
        (t_trm_abs (*A*)
                   (*k*)(t_typ_arrow ((s_typ_arrow s1 s2)+) (t_typ_bvar 1))
          (t_trm_app (*k*)(t_trm_bvar 0) dummy_type
            (t_trm_abs (*B*)
                       (*p*) (t_typ_pair (s1+) (t_typ_arrow (s2+) (t_typ_bvar 1)))
              (t_trm_let_fst (t_trm_bvar 0) (* let x = fst p in *)
                (t_trm_let_snd (t_trm_bvar 1) (* let k' = snd p in *)
                  (t_trm_app u (*B*)(t_typ_bvar 0) (*k'*)(t_trm_bvar 0))))))).
 (* TODO last line is wrong, need to turn x's in u into bvars *)
 (* TODO app, if *)