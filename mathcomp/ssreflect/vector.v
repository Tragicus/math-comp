From Coq Require Import PArray.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype order ssralg uint63 pointed.

(******************************************************************************)
(*                         Vectors (dynamic arrays)                           *)
(*                                                                            *)
(* Efficient dynamic data structure for storing arrays of objects. The        *)
(* elements of a vector need to come from a pointedType, lest the equality    *)
(* operator fails to compare equal vectors because they were created with     *)
(* different default elements.                                                *)
(*                                                                            *)
(* Operations:                                                                *)
(*    capacity t == maximum number of elements the vector t can hold before   *)
(*                  adding one results in a reallocation                      *)
(*        size t == number of elements in t                                   *)
(*      make n x == vector containing n elements equal to x                   *)
(*       get t n == the n-th element of t, or (default t) when size t <= n    *)
(*      move t s == copies t into s                                           *)
(*   reserve n t == sets the capacity of t to n, resizing t if needed         *)
(*     set t n x == sets the n-th element of t to x, increasing the size of t *)
(*                  if necessary                                              *)
(*        copy t == returns a copy of t                                       *)
(*    append t x == adds an element x at the end of t, increasing its size by *)
(*                  1                                                         *)
(*    pop_back t == removes the last element of t, actually shrinking t only  *)
(*                  when it is sufficiently empty                             *)
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

Import Order.Def Order.POrderTheory Order.TotalTheory Order.OrderEmbeddingTheory.
Import Order.BPOrderTheory Order.TPOrderTheory GRing.Theory.

Section Def.
Variables (T : ptEqType).

(* Invariant: size t <= length (as_array t). *)
Record vector := {
  as_array : array T;
  size : uint63;
  sizeP_subproof : size <= length as_array;
  defaultE : default as_array == pt;
  get_large : forall i, (size <= i) -> as_array.[i] == pt
}.

Definition capacity t : uint63 := length (as_array t).

Lemma sizeP t : size t <= capacity t.
Proof. exact: sizeP_subproof. Qed.

Lemma make_subproof_size (n : uint63) :
  let n := min n max_length in
  n <= length (make n (@pt T)).
Proof.
by rewrite /= length_make -[leb _ _]/(@Order.le _ uint63 _ _)
  [X in if X then _ else _]ge_min lexx orbT.
Qed.

Lemma make_subproof_default (n : uint63) :
  default (make n (@pt T)) == pt.
Proof. exact/eqP/default_make. Qed.

Lemma make_subproof_get (n i : uint63) : n <= i ->
  (make n (@pt T)).[i] == pt.
Proof. by move=> _; rewrite get_make. Qed.

Definition make (n : uint63) :=
  Build_vector (make_subproof_size n) (make_subproof_default _) (@make_subproof_get _).

Lemma size_make n : size (make n) = min n max_length.
Proof. by []. Qed.

Lemma capacity_make n : capacity (make n) = min n max_length.
Proof.
rewrite /capacity/= length_make.
suff ->: min n max_length ≤? max_length by [].
by rewrite [_ <=? _](@ge_min _ uint63) lexx orbT.
Qed.

Definition get t (n : uint63) := (as_array t).[n].

Definition move_subdef t s n :=
  iteri (min (size t) n)
      (let t := as_array t in fun i u => u.[i <- t.[i]]) s.

Lemma move_subproof_size t s :
  (size s) <= length (move_subdef t (as_array s) (size s)).
Proof.
apply/(@iteri_ind _ (fun _ x => (size s) <= length x)); first exact: sizeP.
by move=> u n _ su/=; rewrite length_set.
Qed.

Lemma move_subproof_default t s :
  default (move_subdef t (as_array s) (size s)) == pt.
Proof.
rewrite /move_subdef.
apply: (iteri_ind (P:=fun _ x => default x == pt)); first exact: defaultE.
by move=> u n _; rewrite default_set.
Qed.

Lemma move_subproof_get t s i : size s <= i ->
  (move_subdef t (as_array s) (size s)).[i] == pt.
Proof.
rewrite /move_subdef => si.
apply: (iteri_ind (P:=fun j x => x.[i] == pt)); first exact: get_large.
move=> u j jlt ui; rewrite get_set_other// => ji.
move: jlt; rewrite ji => /(le_lt_trans si).
by rewrite ltNge ge_min lexx orbT.
Qed.

Definition move t s :=
  Build_vector (move_subproof_size t s) (move_subproof_default t s)
    (@move_subproof_get t s).

Lemma size_move t s : size (move t s) = size s.
Proof. by []. Qed.

Lemma capacity_move t s : capacity (move t s) = capacity s.
Proof.
apply/(@iteri_ind _ (fun _ x => length x = capacity s)) => // y n _ ys.
by rewrite length_set.
Qed.

Lemma reserve_subproof_size n t :
  min n (size t) <= length (PArray.make n (@pt T)).
Proof.
rewrite length_make -(minEle n max_length) le_min !ge_min lexx/=.
apply/orP; right; apply/(le_trans (sizeP t))/leb_length.
Qed.

Lemma reserve_subproof_get n t i :
  min n (size t) <= i -> (PArray.make n (@pt T)).[i] == pt.
Proof. move=> _; apply/eqP/get_make. Qed.

(* Sets t's capacity to n, removing the last elements of t as needed. *)
Definition reserve (n : uint63) t :=
  if n == capacity t then t else
  move t (Build_vector (reserve_subproof_size n t) (make_subproof_default n)
    (@reserve_subproof_get n t)).

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

Lemma set_subproof_size t n x : size t <= length (as_array t).[n <- x].
Proof. by rewrite length_set; apply: sizeP. Qed.

Lemma set_subproof_default t n x : default (as_array t).[n <- x] == @pt T.
Proof. by rewrite default_set; apply: defaultE. Qed.

Lemma set_subproof_get t n x : n < (size t) ->
  forall i, size t <= i -> (as_array t).[n <- x].[i] == pt.
Proof.
move=> nt i ti; rewrite get_set_other; first exact/get_large.
by move: nt => /[swap] ->; rewrite ltNge ti.
Qed.

Definition set t n x :=
  let s := size t in
  (if n < s as b return (n < s = b -> vector) then
    fun ns => Build_vector (set_subproof_size t n x)
      (set_subproof_default t n x) (@set_subproof_get t n x ns)
  else fun=> t) erefl.

Lemma size_set t n x : size (set t n x) = size t.
Proof. by rewrite /set; move: erefl; case: {2 3}(n < size t). Qed.

Lemma capacity_set t n x : capacity (set t n x) = capacity t.
Proof.
rewrite /set/capacity; move: erefl; case: {2 3}(n < size t) => //= _.
exact: length_set.
Qed.

Lemma get_set t n x i : n < size t ->
  get (set t n x) i = if i == n then x else get t i.
Proof.
move=> nt.
rewrite /get/set; move: erefl; rewrite {2 3}nt/= => _.
have [->|/negP ni] := eqVneq i n.
  exact/get_set_same/(lt_le_trans nt)/sizeP.
by apply/get_set_other => /esym/(@eqP uint63).
Qed.

Lemma copy_subproof_size t : size t <= length (copy (as_array t)).
Proof. rewrite length_copy; apply/sizeP. Qed.

Lemma copy_subproof_default t : default (copy (as_array t)) == pt.
Proof. by rewrite default_copy; apply: defaultE. Qed.

Lemma copy_subproof_get t i : size t <= i -> (copy (as_array t)).[i] == pt.
Proof. by move=> /get_large; rewrite get_copy. Qed.

Definition copy t :=
  Build_vector (copy_subproof_size t) (copy_subproof_default t)
    (@copy_subproof_get t).

Lemma append_subproof_get t i :
  size t + 1 <= i :> uint63 -> (as_array t).[i] == pt.
Proof.
move=> ti; apply/get_large/(le_trans _ ti)/ltW/(@ltuS _ \top).
exact/(le_lt_trans (@sizeP t))/(le_lt_trans (T:=uint63) (leb_length _ _)).
Qed.

Definition append t x :=
  set ((if size t < capacity t as b return ((size t < capacity t) = b -> vector)
  then fun sc => Build_vector (ltWlel sc) (defaultE t) (@append_subproof_get t)
  else fun=> reserve (lsl (size t) 1) t) erefl) (size t) x.

Require Import ssrnat.
Import Order.OrderEmbeddingTheory.

Lemma pop_back_subproof_size t :
  (0 : uint63) < size t -> (size (set t (size t - 1) pt)) - 1 <= length (as_array t) :> uint63.
Proof.
by rewrite size_set => t0; apply/(le_trans _ (sizeP t))/(ltW (lt_predu t0)).
Qed.

Lemma pop_back_subproof_get t i : 0 < size t :> uint63 ->
  size t - 1 <= i :> uint63 ->
  (as_array (set t (size t - 1) pt)).[i] = pt.
Proof.
rewrite le_eqVlt => t0 /orP[/eqP <-|/ltWlel].
  by rewrite [LHS]get_set ?eqxx//; apply/lt_predu/t0.
rewrite -[leLHS](@addrA uint63).


Definition pop_back t :=
  let s := size t in
  (if (0 : uint63) < s as b return ((0 : uint63) < s = b -> vector)
  then fun sgt =>
    let s = s - 1 in
    let t = set t s pt in
    let t := Build_vector (pop_back_subproof sgt) (defaultE _) in
    let c : uint63 := (capacity t) / 3 in
    if (s - 1 : uint63) <= c then reserve c t else t
  else fun=> t) erefl.

Lemma size_pop_back t : size (pop_back t) = min (size t) (size t - 1).
Proof.
rewrite /pop_back/=.
move: erefl; case: {2 3}((0 : uint63) < size t) => [t0|]; last first.
  move=> /(introT negPf); rewrite lt0x negbK => /eqP ->.
  exact/esym/min_idPl/le0x.
rewrite (min_idPr (ltW (lt_predu t0))).
case: ifP => /= [cs|_ //].
by rewrite size_reserve/=; apply/min_idPr. 
Qed.

End Def.

Notation "t '.[' n ']'" := (get t n) : vect_scope.
Notation "t '.[' n '<-' x ']'" := (set t n x) : vect_scope.

Section Equality.
Variable (T : ptEqType).

Definition eq_op (t u : vector T) :=
  (size t == size u) && (capacity t == capacity u) &&
  all (size t) (fun i => t.[i] == u.[i]).

Lemma eqP : Equality.axiom eq_op.
Proof.
move=> t u; apply/(iffP idP) => [|->]; last first.
  by rewrite /eq_op !eqxx/=; apply/allP.
move: t u => [] t ts + [] u us + /andP[]/andP[] /eqP/= tus.
rewrite {}tus /get/capacity/= => + + /eqP tus /allP/= tsE.
have: t = u.
  apply: array_ext => //.
Search array.

