From Coq Require Import PArray.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype order ssralg uint63.

(******************************************************************************)
(*                         Vectors (dynamic arrays)                           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope vect_scope.
Delimit Scope vect_scope with vect.

Local Open Scope order_scope.
Local Open Scope ring_scope.
Local Open Scope uint63_scope.
Local Open Scope array_scope.
Local Open Scope vect_scope.

Import Order.Def Order.POrderTheory Order.TotalTheory.

Section Def.
Variables (T : Type).

(* Invariant: size t <= length (as_array t). *)
Record vector := {
  as_array : array T;
  size : uint63;
  sizeP_subproof : size <= length as_array
}.

Definition capacity t := length (as_array t).

Lemma sizeP t : size t <= capacity t.
Proof. exact: sizeP_subproof. Qed.

Lemma make_subproof (n : uint63) (x : T) :
  let n := min n max_length in
  n <= length (make n x).
Proof.
by rewrite /= length_make -[leb _ _]/(@Order.le _ uint63 _ _)
  [X in if X then _ else _]ge_min lexx orbT.
Qed.

Definition make (n : uint63) (x : T) := Build_vector (make_subproof n x).

Lemma size_make n x : size (make n x) = min n max_length.
Proof. by []. Qed.

Lemma capacity_make n x : capacity (make n x) = min n max_length.
Proof.
rewrite /capacity/= length_make.
suff ->: min n max_length ≤? max_length by [].
by rewrite [_ <=? _](@ge_min _ uint63) lexx orbT.
Qed.

Definition get t n := (as_array t).[n].

Definition move_subdef t s n :=
  iteri (min (size t) n)
      (let t := as_array t in fun i u => u.[i <- t.[i]]) s.

Lemma move_subproof t s :
  (size s) <= length (move_subdef t (as_array s) (size s)).
Proof.
apply/(@iteri_ind _ (fun x => (size s) <= length x)); first exact: sizeP.
by move=> u n _ su/=; rewrite length_set.
Qed.

Definition move t s := Build_vector (move_subproof t s).

Lemma size_move t s : size (move t s) = size s.
Proof. by []. Qed.

Lemma capacity_move t s : capacity (move t s) = capacity s.
Proof.
apply/(@iteri_ind _ (fun x => length x = capacity s)) => // y n _ ys.
by rewrite length_set.
Qed.

Lemma reserve_subproof n t :
  min n (size t) <= length (PArray.make n (default (as_array t))).
Proof.
rewrite length_make -(minEle n max_length) le_min !ge_min lexx/=.
apply/orP; right; apply/(le_trans (sizeP t))/leb_length.
Qed.

(* Sets t's capacity to n, removing the last elements of t as needed. *)
Definition reserve (n : uint63) t :=
  if n == capacity t then t else
  move t (Build_vector (reserve_subproof n t)).

Lemma size_reserve (n : uint63) t : size (reserve n t) = min n (size t).
Proof.
rewrite /reserve.
have [->|_] := eqVneq n (capacity t); first exact/esym/min_idPr/sizeP.
by rewrite size_move/=.
Qed.

Lemma capacity_reserve (n : uint63) t :
  capacity (reserve n t) = min n max_length.
Proof.
rewrite /reserve.
have [->//|_] := eqVneq n (capacity t).
  by rewrite (@min_idPl _ uint63 _ _ (leb_length _ _)).
by rewrite capacity_move/= [LHS]length_make minEle.
Qed.

Lemma set_subproof1 t n x : size t <= length (set (as_array t) n x).
Proof. by rewrite length_set; apply: sizeP. Qed.

Lemma set_subproof2 t (n : uint63) x :
  let c := max (n+1 : uint63) (lsl (size t) 1) in
  min (n+1 : uint63) max_length <= length ((as_array (reserve c t)).[n <- x]).
Proof.
by rewrite /= length_set [leRHS]capacity_reserve min_maxl le_max lexx.
Qed.

Definition set t n x :=
  let s := size t in
  if n <? s then Build_vector (set_subproof1 t n x)
  else Build_vector (set_subproof2 t n x).

Lemma copy_subproof t : size t <= length (copy (as_array t)).
Proof. rewrite length_copy; apply/sizeP. Qed.

Definition copy t := Build_vector (copy_subproof t).

Definition append t x := set t (size t) x.

Require Import ssrnat.
Import Order.OrderEmbeddingTheory.

Lemma lt_predu (x y : uint63) : x < y -> (y - 1 : uint63) < y.
Proof.
rewrite -!(oembedding_lt to_nat) => xy/=.
suff ->: to_nat (y - 1) = (to_nat y).-1.
  by rewrite /Order.lt/= prednK//; apply/(leq_ltn_trans _ xy).
rewrite /=/to_nat/= sub_spec -Znat.Z2Nat.inj_pred BinInt.Z.sub_1_r.
rewrite Zdiv.Zmod_small//.
case: (to_Z_bounded y) => y0 /BinInt.Z.lt_lt_pred ywB.
split=> //.
apply/BinInt.Z.lt_le_pred/Znat.Z2Nat.inj_lt => //=.
exact/ltP/(leq_ltn_trans _ xy).
Qed.

Lemma pop_back_subproof t :
  (0 : uint63) < size t -> (size t) - 1 <= length (as_array t) :> uint63.
Proof. by move=> t0; apply/(le_trans _ (sizeP t))/(ltW (lt_predu t0)). Qed.

Definition pop_back t :=
  let s := size t in
  let c : uint63 := lsr (capacity t) 1 in
  if (s - 1 : uint63) <= c then reserve c t else
    (if (0 : uint63) < s as b return ((0 : uint63) < s = b -> vector)
    then fun sgt => Build_vector (pop_back_subproof sgt)
    else fun=> t) erefl.

Lemma size_pop_back t : size (pop_back t) = min (size t) (size t - 1).
Proof.
rewrite /pop_back/=; case: ifP => [cs|_].
  rewrite size_reserve cs.


End Def.
