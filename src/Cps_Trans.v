Require Import Core_Infrastructure Source_Definitions Target_Definitions
               Source_Properties Target_Properties.

Definition dummy_type := t_typ_bool.

Lemma s_type_arrow_inv_l : forall s1 s2,
 s_type (s_typ_arrow s1 s2) -> s_type s1.
Proof. inversion 1. assumption. Qed.

Lemma s_type_arrow_inv_r : forall s1 s2,
 s_type (s_typ_arrow s1 s2) -> s_type s2.
Proof. inversion 1. assumption. Qed.

Definition cps_type_trans (s:typ) (wf : s_type s) : typ.
 induction s; try solve [elimtype False; inversion wf].
 (* bool+ = bool *)
 exact t_typ_bool.
 (* (s1->s2)+ = forall a, s1+ X ((s2+ -> a) -> a) *)
 exact (t_typ_arrow (t_typ_pair (IHs1 (s_type_arrow_inv_l s1 s2 wf))
                                (t_typ_arrow (IHs2 (s_type_arrow_inv_r s1 s2 wf))
                                             (t_typ_bvar 1)))
                    (t_typ_bvar 0)).
Defined.

Lemma cps_type_trans_bool : forall wf,
  cps_type_trans s_typ_bool wf = t_typ_bool.
Proof. auto. Qed.

Lemma cps_type_trans_arrow : forall s1 s2 wf,
  cps_type_trans (s_typ_arrow s1 s2) wf = 
  t_typ_arrow (t_typ_pair (cps_type_trans s1 (s_type_arrow_inv_l s1 s2 wf))
                          (t_typ_arrow
                            (cps_type_trans s2 (s_type_arrow_inv_r s1 s2 wf))
                            (t_typ_bvar 1)))
              (t_typ_bvar 0).
Proof. intros. simpl. f_equal. Qed.

Lemma cps_type_trans_produces_t_type : forall s wf_s,
  t_type (cps_type_trans s wf_s).
Proof.
  induction s; intros; auto; try solve [elimtype False; inversion wf_s].
  rewrite cps_type_trans_arrow.
  apply_fresh t_type_arrow as X. simpl.
  apply t_type_pair.
  rewrite open_tt_rec_t_type; apply IHs1.
  apply_fresh t_type_arrow as Y.
  rewrite open_tt_rec_t_type; rewrite open_tt_rec_t_type; apply IHs2.
  apply t_type_var. apply t_type_var.
Qed.

Extraction cps_type_trans. (* BAM *)

Definition cps_type_trans_computation (s : typ) (wf : s_type s) :=
  t_typ_arrow (t_typ_arrow (cps_type_trans s wf) (t_typ_bvar 1))
              (t_typ_bvar 0).

Eval simpl in cps_type_trans (s_typ_arrow s_typ_bool s_typ_bool).

Fixpoint cps_term_trans (G:env_term) (e:trm) (s:typ)
  (s_der : s_typing G e s) : trm :=
match e with
| s_trm_true => t_trm_abs (t_typ_arrow (cps_type_trans s)
                                       (t_typ_bvar 0)) (* \[a](k:bool->a). *)
                          (t_trm_app (t_trm_bvar 0)    (*        k true    *)
                                     dummy_type
                                     t_trm_true)
| _ => t_trm_false
end.

Eval simpl in
  cps_term_trans empty s_trm_true s_typ_bool
                 (s_typing_true empty (LibWfenv.wfenv_empty s_type)).