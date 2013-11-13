Require Import LibWfenv Core_Infrastructure
               Source_Definitions Target_Definitions
               Source_Properties Target_Properties.

(* for applications where the type argument is irrelevant *)
Definition dummy_type := t_typ_bool.
Definition s_dummy_type := s_typ_bool.

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

(* TODO: add induction on the size of e following LN CPS formulation *)
Fixpoint cps_term_trans (G : env_term)  (e : trm) {struct e}: trm :=
match e with
| s_trm_fvar v =>
  let s := get v G in
  match s with
  | Some s' =>
    (t_trm_abs (t_typ_arrow (cps_type_trans s') (t_typ_bvar 0))
               (t_trm_app (t_trm_bvar 0) dummy_type (t_trm_fvar v)))
  | None => trm_bad
  end
| s_trm_true =>
  (t_trm_abs (t_typ_arrow (cps_type_trans s_typ_bool) (t_typ_bvar 0))
                     (t_trm_app (t_trm_bvar 0) dummy_type t_trm_true))
| s_trm_false =>
  (t_trm_abs (t_typ_arrow (cps_type_trans s_typ_bool) (t_typ_bvar 0))
                     (t_trm_app (t_trm_bvar 0) dummy_type t_trm_false))
| s_trm_abs s1 bdy =>
  (* TODO: write a type inferencer to get s2 *)
  let s2 := s_dummy_type in
  let x := var_gen (fv_ee source bdy) in
  (t_trm_abs (t_typ_arrow (cps_type_trans (s_typ_arrow s1 s2)) (t_typ_bvar 0))
                   (t_trm_app (t_trm_bvar 0) dummy_type
                              (t_trm_abs 
                                (t_typ_pair (cps_type_trans s1) (t_typ_arrow (cps_type_trans s2) (t_typ_bvar 0)))
                                (* TODO: check let projection bvar indices *)
                                (t_trm_let_fst (t_trm_bvar 0) (* project out x and bind to 0 *)
                                  (t_trm_let_snd (t_trm_bvar 1) (* project out k' and bind to 0 *)
                                    (t_trm_app (cps_term_trans (G & x ~ s1) (s_open_ee_var bdy x)) (t_typ_bvar 0) (t_trm_bvar 0)))))))
(* TODO: finish *)
| s_trm_app e1 e2 => trm_bad
| s_trm_if e1 e2 e3 => trm_bad
| _ => trm_bad
end.

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
