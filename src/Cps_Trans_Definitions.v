Require Import LibWfenv Core_Infrastructure
               Source_Definitions Target_Definitions
               Source_Properties Target_Properties.
Require Import CpdtTactics.
Require Import Recdef.

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

Definition cps_type_trans_computation (s : typ) :=
  t_typ_arrow (t_typ_arrow (s+) (t_typ_bvar 1)) (t_typ_bvar 0).

Notation "( s %)" := (cps_type_trans_computation s) (at level 0).

(* Relational cps term translation *)
Inductive cps_trans : env_term -> trm -> typ -> trm -> Prop :=
  | cps_trans_var : forall G x s, wfenv s_type G -> binds x s G ->
    cps_trans G (s_trm_fvar x) s
      (t_trm_abs (t_typ_arrow (s+) (t_typ_bvar 1))
        (t_trm_app (t_trm_bvar 0) dummy_type (t_trm_fvar x)))
  | cps_trans_true : forall G, wfenv s_type G ->
    cps_trans G s_trm_true s_typ_bool
      (t_trm_abs (t_typ_arrow t_typ_bool (t_typ_bvar 1))
        (t_trm_app (t_trm_bvar 0) dummy_type t_trm_true))
  | cps_trans_false : forall G, wfenv s_type G ->
    cps_trans G s_trm_false s_typ_bool
      (t_trm_abs (t_typ_arrow t_typ_bool (t_typ_bvar 1))
        (t_trm_app (t_trm_bvar 0) dummy_type t_trm_false))
  | cps_trans_abs : forall L G e s1 s2 u,
      (forall x, x \notin L ->
        cps_trans (G & x ~ s1) (s_open_ee_var e x) s2 (open_ee_rec target 1 (t_trm_fvar x) u)) ->
      s_type s1 ->
      cps_trans G (s_trm_abs s1 e) (s_typ_arrow s1 s2)
        (t_trm_abs (*A*)
                   (*k*)(t_typ_arrow ((s_typ_arrow s1 s2)+) (t_typ_bvar 1))
          (t_trm_app (*k*)(t_trm_bvar 0) dummy_type
            (t_trm_abs (*B*)
                       (*p*) (t_typ_pair (s1+) (t_typ_arrow (s2+) (t_typ_bvar 1)))
              (t_trm_let_fst (t_trm_bvar 0) (* let x = fst p in *)
                (t_trm_let_snd (t_trm_bvar 1) (* let k' = snd p in *)
                  (t_trm_app u (*B*)(t_typ_bvar 0) (*k'*)(t_trm_bvar 0)))))))
  | cps_trans_if : forall G e1 e2 e3 s u1 u2 u3,
      cps_trans G e1 s_typ_bool u1 ->
      cps_trans G e2 s u2 -> cps_trans G e3 s u3 ->
      cps_trans G (s_trm_if e1 e2 e3) s
        (t_trm_abs (*A*) (*k*)(t_typ_arrow (s+) (t_typ_bvar 1))
          (t_trm_app u1 (t_typ_bvar 0)
            (t_trm_abs (*x*)t_typ_bool
              (t_trm_if (t_trm_bvar 0)
                (t_trm_app u2 (t_typ_bvar 1) (t_trm_bvar 1))
                (t_trm_app u3 (t_typ_bvar 1) (t_trm_bvar 1))))))
  | cps_trans_app : forall G e1 e2 s1 s2 u1 u2,
      cps_trans G e1 (s_typ_arrow s1 s2) u1 -> cps_trans G e2 s1 u2 ->
      cps_trans G (s_trm_app e1 e2) s2
        (t_trm_abs (*A*) (*k*)(t_typ_arrow (s2+) (t_typ_bvar 1))
          (t_trm_app u1 (t_typ_bvar 0)
            (t_trm_abs (*x1*)((s_typ_arrow s1 s2)+)
              (t_trm_app u2 (t_typ_bvar 1)
                (t_trm_abs (*x2*)(s1+)
                  (t_trm_app (t_trm_bvar 1) (t_typ_bvar 2)
                    (t_trm_pair (t_trm_bvar 0) (t_trm_bvar 2)))))))).

(* Attempt at a constructive cps term translation function; incomplete *) 
Function cps_term_trans (G : env_term)  (e : trm) {measure trm_size e}: trm :=
match e with
| s_trm_fvar v =>
  let s := get v G in
  match s with
  | Some s' =>
    (* λ [σ] k:s+ → α . k [_] x *)
    (t_trm_abs (t_typ_arrow (cps_type_trans s') (t_typ_bvar 0))
               (t_trm_app (t_trm_bvar 0) dummy_type (t_trm_fvar v)))
  | None => trm_bad
  end
| s_trm_true =>
  (* λ [σ] k:bool+ → α . k [_] true *)
  (t_trm_abs (t_typ_arrow (cps_type_trans s_typ_bool) (t_typ_bvar 0))
                     (t_trm_app (t_trm_bvar 0) dummy_type t_trm_true))
| s_trm_false =>
  (* λ [σ] k:bool+ → α . k [_] false *)
  (t_trm_abs (t_typ_arrow (cps_type_trans s_typ_bool) (t_typ_bvar 0))
                     (t_trm_app (t_trm_bvar 0) dummy_type t_trm_false))
| s_trm_abs s1 bdy =>
  (* TODO: write a type inferencer to get s2 *)
  let s2 := s_dummy_type in
  let x := var_gen (fv_ee source bdy) in
  let v := cps_term_trans (G & x ~ s1) (s_open_ee_var bdy x) in
  (* λ [α] k:((σ1 → σ2)+ → α) . *)
  (t_trm_abs (t_typ_arrow (cps_type_trans (s_typ_arrow s1 s2)) (t_typ_bvar 0))
    (* k [_] ... *)
    (t_trm_app (t_trm_bvar 0) dummy_type
      (* (λ [β] pr:(σ1+ ⅹ (σ2+ → β)) . *)
      (t_trm_abs (t_typ_pair (cps_type_trans s1) (t_typ_arrow (cps_type_trans s2) (t_typ_bvar 0)))
        (* TODO: check let projection bvar indices *)
        (* let y = fst pr in let k' = snd pr in *)
        (t_trm_let_fst (t_trm_bvar 0)
          (t_trm_let_snd (t_trm_bvar 1)
            (* (v [β] k') *)
            (t_trm_app v (t_typ_bvar 0) (t_trm_bvar 0)))))))
| s_trm_app e1 e2 =>
  (* TODO: s2 -> s from type inference e1 *)
  let s := s_dummy_type in
  let s2 := s_dummy_type in
  let s_arr_plus := (cps_type_trans (s_typ_arrow s2 s)) in
  let v1 := (cps_term_trans G e1) in
  let v2 := (cps_term_trans G e2) in
  (t_trm_abs
    (* k : s+ -> α *)
    (t_typ_arrow (cps_type_trans s) (t_typ_bvar 0))
    (t_trm_app v1 (t_typ_bvar 0)
      (* λ [_] x1:(σ2→σ)+ . *)
      (t_trm_abs s_arr_plus
        (* v1 [σ] ... *)
        (t_trm_app v2 (t_typ_bvar 1)
          (* λ [_] x2:σ2+ . *)
          (t_trm_abs (cps_type_trans s2)
            (* x1 [σ] (x2, k) *)
            (t_trm_app (t_trm_bvar 1) (t_typ_bvar 2)
              (t_trm_pair (t_trm_bvar 0) (t_trm_bvar 2))))))))

| s_trm_if e e1 e2 =>
  (* TODO: s from type inference of e2 *)
  let s_plus := (cps_type_trans s_dummy_type) in
  let v := (cps_term_trans G e) in
  let v1 := (cps_term_trans G e1) in
  let v2 := (cps_term_trans G e2) in
  (* λ [α] k:(σ+ → α) . ...*)
  (t_trm_abs (t_typ_arrow s_plus (t_typ_bvar 0))
    (* v [σ] ... *)
    (t_trm_app v (t_typ_bvar 0)
      (* λ [_] x:bool . if x then (v1 [α] k) else (v2 [α] k) *)
      (t_trm_abs t_typ_bool
        (t_trm_if (t_trm_bvar 0)
          (t_trm_app v1 (t_typ_bvar 0) (t_trm_bvar 1))
          (t_trm_app v2 (t_typ_bvar 0) (t_trm_bvar 1))))))


| _ => trm_bad
end.
(* termination proof *)
  (* abs case *)
  intros. simpl. pick_fresh x. rewrite* s_trm_size_open_var. crush.
  (* if case *)
  crush. crush. crush.
  (* app case *)
  crush. crush.
Defined.

