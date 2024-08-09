(* TODO: remove when requiring coq8.21 *)
From Coq Require Import ZArith.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq choice fintype order.
From Coq Require Export Uint63.

Local Open Scope uint63_scope.

Definition to_nat n := Z.to_nat (to_Z n).
Definition of_nat n := of_Z (Z.of_nat n).

Lemma to_natK : cancel to_nat of_nat.
Proof.
move=> x; rewrite /to_nat /of_nat Z2Nat.id ?of_to_Z//.
by case: (to_Z_bounded x).
Qed.

Lemma eqbP : Equality.axiom eqb.
Proof.
move=> x y; apply/Bool.iff_reflect.
(* Why does apply introduce a hole, the goal clearly matches *)
by refine (iff_sym _); apply/eqb_spec.
Qed.

HB.instance Definition _ := hasDecEq.Build int eqbP.

Module Enum.
Fact enum_key : unit. exact: tt. Qed.


End Enum.

Check fin_type.
HB.about isFinite.Build.
HB.about hasChoice.Build.

HB.howto int finType.

Lemma of_nat_rect (K : int -> Type) :
  (forall (n : nat), (to_nat (of_nat n) == n) -> K (of_nat n)) ->
  forall x : int, K x.
Proof. by move=> KP x; rewrite -[x]to_natK; apply/KP; rewrite to_natK. Qed.

Lemma of_natK_subproof (n : nat) : (to_nat (of_nat n) == n) ->
  to_nat (of_nat n) = n.
Proof. by move=> /eqP. Qed.

HB.instance Definition _ := @isSub.Build nat (fun n => to_nat (of_nat n) == n)
  int to_nat (fun n _ => of_nat n) of_nat_rect of_natK_subproof.

HB.about isSub.Build.
HB.howto int subType.
Search subType can_type.

Lemma to_natK : cancel 
HB.howto int porderType.


