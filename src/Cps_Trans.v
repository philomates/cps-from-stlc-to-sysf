Require Import Core_Definitions.

Definition dummy_type := t_typ_bool.

Fixpoint cps_type_trans (s:typ) : typ :=
match s with
| s_typ_bool => t_typ_bool
| s_typ_arrow s1 s2 => t_typ_arrow (t_typ_pair (cps_type_trans s1) (t_typ_arrow (cps_type_trans s2) (t_typ_bvar 1))) (t_typ_bvar 0)
| _ => dummy_type
end.

Eval simpl in cps_type_trans (s_typ_arrow s_typ_bool s_typ_bool).

Fixpoint cps_term_trans (e:trm) : trm :=
match e with
| s_trm_true => t_trm_abs (t_typ_arrow (cps_type_trans s) (t_typ_bvar 0)) (t_trm_app (t_trm_bvar 0) dummy_type t_trm_true)
| _ => t_trm_false
end.



Eval simpl in cps_term_trans s_trm_true.

Fixpoint cps_typing_derivation (G:env trm) (e:trm) (s:typ) (s_der : s_typing G e s) : trm :=
match s_der with
| s_typing_true _ _ => t_trm_abs (t_typ_arrow (cps_type_trans s) (t_typ_bvar 0)) (t_trm_app (t_trm_bvar 0) dummy_type t_trm_true)
| _ => t_trm_true
end.
