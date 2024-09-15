From HB Require Import structures.
From mathcomp Require Import all_ssreflect interval.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope order_scope.
Local Open Scope nat_scope.

Import Order.POrderTheory Order.TotalTheory Order.LatticeTheoryMeet Order.LatticeTheoryJoin.

Lemma itvI (d' : unit) (T : orderType d') (a b c d : itv_bound T) :
  Interval a b `&` Interval c d = Interval (a `|` c) (b `&` d).
Proof. by []. Qed.

Lemma subitvE (disp : unit) (T : porderType disp) (itv itv' : interval T) :
  ((itv <= itv') = (itv'.1 <= itv.1) && (itv.2 <= itv'.2))%O.
Proof. by case: itv; case: itv'. Qed.

Lemma itv_boundlr (disp : unit) (T : porderType disp) (itv : interval T) (x : T) :
  x \in itv = (itv.1 <= BLeft x)%O && (BRight x <= itv.2)%O.
Proof. by case: itv. Qed.

Module RBtree.

Module Subdef.

Section Def.
Variables (d : unit) (elt : orderType d).

Inductive t : Type :=
  | leaf
  | node : t -> elt -> t -> bool -> t.

Fixpoint eqb (s t : t) : bool :=
  match s, t with
  | leaf, leaf => true
  | node sl sx sr sc, node tl tx tr tc => (sc == tc) && (sx == tx) && (eqb sl tl) && (eqb sr tr)
  | _, _ => false
  end.

Lemma eqbP s t : reflect (s = t) (eqb s t).
Proof.
elim: s t => [|sl IHsl sx sr IHsr sb]; case=> [|tl tx tr tb]; apply/(iffP idP) => //=.
  by move=> /andP[]/andP[]/andP[] /eqP -> /eqP -> /IHsl -> /IHsr ->.
case=> stl -> str ->; rewrite 2!eqxx/=; apply/andP; split; first exact/IHsl.
exact/IHsr.
Qed.

#[export]
HB.instance Definition _ := hasDecEq.Build t eqbP.

Definition is_red s :=
  match s with
  | leaf => false
  | node _ _ _ c => c
  end.

Fixpoint black_height s :=
  match s with
  | leaf => Some 0
  | node l _ r c =>
    obind (fun l =>
      obind (fun r =>
        if l == r then Some (l + ~~ c) else None)
        (black_height r))
      (black_height l)
  end.

Fixpoint well_formed s :=
  match s with
  | leaf => true
  | node l _ r c =>
      (c ==> ~~ (is_red l) && ~~ (is_red r)) && well_formed l && well_formed r
  end.

Fixpoint well_ordered s (itv : interval elt) := 
  match s with
  | leaf => true
  | node l x r _ => (x \in itv) && (well_ordered l (Interval itv.1 (BLeft x))) && (well_ordered r (Interval (BRight x) itv.2))
  end.

Definition is_rb (s : t) := ~~ is_red s && (black_height s != None) && well_formed s && well_ordered s `]-oo, +oo[.

Definition create l x r := node l x r false.
Arguments create : simpl never.

Definition bal l x r c :=
  if c then node l x r c else
  match l, r with
  | leaf, leaf => node l x r false
  | node (node lll llx llr true) lx lr true, node rl rx rr true =>
      node (node (node lll llx llr true) lx lr false) x (node rl rx rr false) true
  | node (node lll llx llr true) lx lr true, r =>
      node (node lll llx llr true) lx (node lr x r true) false
  | node ll lx (node lrl lrx lrr true) true, node rl rx rr true =>
      node (node ll lx (node lrl lrx lrr true) false) x (node rl rx rr false) true
  | node ll lx (node lrl lrx lrr true) true, r =>
      node (node ll lx lrl true) lrx (node lrr x r true) false
  | node ll lx lr true, node (node rll rlx rlr true) rx rr true =>
      node (node ll lx lr false) x (node (node rll rlx rlr true) rx rr false) true
  | l, node (node rll rlx rlr true) rx rr true =>
      node (node l x rll true) rlx (node rlr rx rr true) false
  | node ll lx lr true, node rl rx (node rrl rrx rrr true) true =>
      node (node ll lx lr true) x (node rl rx (node rrl rrx rrr true) false) true
  | l, node rl rx (node rrl rrx rrr true) true =>
      node (node l x rl true) rx (node rrl rrx rrr true) false
  | l, r => node l x r c
  end.
Arguments bal : simpl never.

Definition wf_bal s :=
  match s with
  | node l x r true => well_formed l && well_formed r
  | _ => well_formed s
  end.

Definition singleton x := create leaf x leaf.
Arguments singleton : simpl never.

Fixpoint add x s :=
  match s with
  | leaf => singleton x
  | node l sx r c => if x == sx then node l x r c else
    if (x < sx)%O then bal (add x l) sx r c
    else bal l sx (add x r) c
  end.
Arguments add : simpl never.
  
End Def.

Section Theory.
Variables (d d' : unit) (elt : orderType d) (elt' : orderType d').
Implicit Types (s l r : t elt) (x : elt) (itv : interval elt).

Lemma well_orderedW s itv itv0 : (itv <= itv0)%O -> well_ordered s itv -> well_ordered s itv0.
Proof.
elim: s itv itv0 => [//|] l IHl x r IHr/= _ itv itv0 itvle.
move=> /andP[]/andP[] /(subitvP itvle) ->.
move=> /IHl ->; last by move: itvle; rewrite !subitvE/= lexx => /andP[->].
by move=> /IHr -> //; move: itvle; rewrite !subitvE/= lexx => /andP[_].
Qed.

Lemma well_orderedWT s itv : well_ordered s itv -> well_ordered s `]-oo, +oo[.
Proof. exact/well_orderedW/Order.lex1. Qed.

Lemma well_orderedWl s itv lb : (itv.1 <= lb)%O -> well_ordered s (Interval lb itv.2) -> well_ordered s itv.
Proof. by move=> lbi; apply/well_orderedW; rewrite subitvE lbi/=. Qed.

Lemma well_orderedWr s itv ub : (ub <= itv.2)%O -> well_ordered s (Interval itv.1 ub) -> well_ordered s itv.
Proof. by move=> iub; apply/well_orderedW; rewrite subitvE/= lexx iub. Qed.

Lemma well_orderedWTl s itv : well_ordered s itv -> well_ordered s (Interval -oo itv.2).
Proof. by apply/well_orderedW; rewrite subitvE/=. Qed.

Lemma well_orderedWTr s itv : well_ordered s itv -> well_ordered s (Interval itv.1 +oo).
Proof. by apply/well_orderedW; rewrite subitvE/= lexx Order.lex1. Qed.

Lemma well_formed_create l x r : well_formed l -> well_formed r -> well_formed (create l x r).
Proof. by move=> /= ->. Qed.

Lemma well_ordered_create l x r itv : x \in itv -> well_ordered l (Interval itv.1 (BLeft x)) -> well_ordered r (Interval (BRight x) itv.2) -> well_ordered (create l x r) itv.
Proof. by move=> /= -> ->. Qed.

Lemma well_formed_bal l x r c : wf_bal l -> wf_bal r -> wf_bal (bal l x r c).
Proof.
case: c => [/=|].

case: l => [_|ll lx lr lc].
  

