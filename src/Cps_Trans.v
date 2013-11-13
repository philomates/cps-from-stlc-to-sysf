Require Import Core_Infrastructure Source_Definitions Target_Definitions
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
