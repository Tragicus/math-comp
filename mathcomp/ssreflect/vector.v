From Coq Require Import Uint63 PArray.

(******************************************************************************)
(*                         Vectors (dynamic arrays)                           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope vect_scope.
Delimit Scope vect_scope with vect.

Local Open Scope uint63_scope.
Local Open Scope array_scope.
Local Open Scope vect_scope.

Section Def.
Variables (T : Type).

(* Invariant: size t <= length (as_array t). *)
Record vector := {
  as_array : array T;
  size : int
}.

Definition make n x := Build_vector (make n x) n.

Definition get t n := (as_array t).[n].

Definition capacity t := length (as_array t).

(* Sets t's capacity to n, removing the last elements of t as needed. *)
Definition reserve n t :=
  if n =? capacity t then t else
  let s := size t in
  let s := if n <? s then n else s in
  let t := as_array t in
  Build_vector (
    (fix F n u :=
      match n with
      | 0 => u
      | S n => let i := s - of_nat n in
          F n u.[i <- t.[i]]
      end) (S (to_nat s)) (PArray.make n (default t)))
    s.

Definition set t n x :=
  let s := size t in
  if n <? s then Build_vector (set (as_array t) n x) s
  else let c := s << 1 in
  let c := if n <? c then c else n+1 in
  Build_vector ((as_array (reserve c t)).[n <- x]) n.

Definition copy t := Build_vector (copy (as_array t)) (size t).

Definition append t x :=


End Def.
