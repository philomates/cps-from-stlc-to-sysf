(********************************************************
 * Core source/target/combined language definitions     *
 * from Ahmed & Blume ICFP 2011                         *
 * William J. Bowman, Phillip Mates & James T. Perconti *
 ********************************************************)

Set Implicit Arguments.
Require Import LibLN.
Implicit Type x : var.
Implicit Type X : var.

(* Syntax of pre-types *)

Inductive s_typ : Set :=
  | s_typ_bool : s_typ                    (* bool *)
  | s_typ_arrow : s_typ -> s_typ -> s_typ (* s -> s *).

Inductive t_typ : Set :=
  | t_typ_bool : t_typ                    (* bool *)
  | t_typ_pair : t_typ -> t_typ -> t_typ  (* t x t *)
  | t_typ_bvar : nat -> t_typ             (* n *)
  | t_typ_fvar : var -> t_typ             (* X *)
  | t_typ_arrow : t_typ -> t_typ -> t_typ (* forall . t -> t *).

Inductive typ : Set :=
  | typ_s : s_typ -> typ
  | typ_t : t_typ -> typ.
