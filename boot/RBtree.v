From HB Require Import structures.
From mathcomp Require Import all_ssreflect interval.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope order_scope.
Local Open Scope nat_scope.

Import Order.POrderTheory Order.TotalTheory.

Lemma itvI d' (T : orderType d') (a b c d : itv_bound T) :
  Interval a b `&` Interval c d = Interval (a `|` c) (b `&` d).
Proof. by []. Qed.

Lemma subitvE disp (T : porderType disp) (itv itv' : interval T) :
  ((itv <= itv') = (itv'.1 <= itv.1) && (itv.2 <= itv'.2))%O.
Proof. by case: itv; case: itv'. Qed.

Lemma itv_boundlr disp (T : porderType disp) (itv : interval T) (x : T) :
  x \in itv = (itv.1 <= BLeft x)%O && (BRight x <= itv.2)%O.
Proof. by case: itv. Qed.

Lemma ifC T a b (x y z t : T) :
  (if a then if b then x else y else if b then z else t) =
  if b then if a then x else z else if a then y else t.
Proof. by case: a; case: b. Qed.

Module RBtree.

Module Subdef.

Section Def.
Variables (d : Order.disp_t) (elt : orderType d).

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

(* well_formed c s checks that there are no two consecutive red nodes in the tree where s is the child of a root of color c. *)
Fixpoint well_formed c s :=
  match s with
  | leaf => true
  | node l _ r c' =>
      ~~ (c && c') && well_formed c' l && well_formed c' r
  end.

Fixpoint well_ordered s (itv : interval elt) := 
  match s with
  | leaf => true
  | node l x r _ => (x \in itv) && (well_ordered l (Interval itv.1 (BLeft x))) && (well_ordered r (Interval (BRight x) itv.2))
  end.

Definition is_rb (s : t) := (black_height s != None) && well_formed true s && well_ordered s `]-oo, +oo[.

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
Variables (d d' : Order.disp_t) (elt : orderType d) (elt' : orderType d').
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

Lemma well_formed_create l x r : well_formed false l -> well_formed false r -> well_formed true (create l x r).
Proof. by move=> /= ->. Qed.

Lemma well_ordered_create l x r itv : x \in itv -> well_ordered l (Interval itv.1 (BLeft x)) -> well_ordered r (Interval (BRight x) itv.2) -> well_ordered (create l x r) itv.
Proof. by move=> /= -> ->. Qed.

Lemma well_formed_bal l x r c : well_formed c l -> well_formed c r -> well_formed false (bal l x r c).
Proof.
(* I am so sorry, but doing this by hand is so much fun. *)
case: c => [/= -> //|].
case: l => [_|ll lx lr lc]/=.
  case: r => // rl rx rr rc.
  case: rl => [|rll rlx rlr rlc]; case: rr => [//|rrl rrx rrr rrc]/=.
  - rewrite -if_and [rrc && _]andbC => /andP[]/andP[] /negPf rcE.
    by rewrite rcE/= rcE/= => ->.
  - rewrite -if_and [rlc && _]andbC andbT => /andP[]/andP[] /negPf rcE.
    by rewrite rcE/= rcE/= => -> ->. 
  - rewrite -if_and if_same =>
      /andP[] /andP[] /andP[] /negPf rlcE ? ? /andP[] /andP[] /negPf rrcE ? ?.
    rewrite andbC rrcE -if_and andbC rlcE/= rlcE rrcE/=.
    by repeat (apply/andP; split).
case: ll => [|lll llx llr llc]/=; case: lr => [|lrl lrx lrr lrc]/=.
- move=> _; case: r => /= [_|rl rx rr rc]; first by rewrite if_same.
  case: rl => [|rll rlx rlr rlc]; case: rr => [|rrl rrx rrr rrc]/=.
  + by rewrite if_same.
  + rewrite -!if_and [rrc && _]andbC => /andP[]/andP[] /negPf rrcE.
    by rewrite rrcE if_same/= rrcE => ->.
  + rewrite -!if_and [rlc && _]andbC andbT => /andP[]/andP[] /negPf rlcE.
    by rewrite rlcE if_same/= rlcE => -> ->.
  + rewrite -!if_and if_same [rrc && _]andbC
      => /andP[]/andP[]/andP[] /negPf rlcE ? ? /andP[]/andP[] /negPf rrcE ? ?.
    rewrite rrcE -!if_and andbC rlcE if_same -if_and andbC rlcE if_same/= rrcE rlcE/=.
    by repeat (apply/andP; split).
- case: r => /= [|rl rx rr rc] /andP[]/andP[] /negPf lrcE.
    by rewrite if_same -if_and andbC lrcE/= lrcE/= => -> ->.
  case: rl => [|rll rlx rlr rlc]; case: rr => [|rrl rrx rrr rrc]/=.
  + by rewrite if_same -if_and andbC lrcE/= lrcE => -> ->.
  + rewrite if_same -!if_and [rrc && _]andbC
      => ? ? /andP[]/andP[] /negPf rrcE ? ?.
    rewrite rrcE if_same -if_and andbC lrcE/= lrcE rrcE/=.
    by repeat (apply/andP; split).
  + rewrite if_same -!if_and [rlc && _]andbC andbT
      => ? ? /andP[]/andP[] /negPf rlcE ? ?.
    rewrite rlcE if_same -if_and andbC lrcE/= lrcE rlcE/=.
    by repeat (apply/andP; split).
  + rewrite !if_same -!if_and
      => ? ? /andP[]/andP[]/andP[] /negPf rlcE ? ? /andP[]/andP[] /negPf rrcE ? ?.
    rewrite andbC rrcE -!if_and andbC rlcE if_same -if_and andbC lrcE/= lrcE rlcE rrcE/=.
    by repeat (apply/andP; split).
- case: r => /= [|rl rx rr rc] /andP[]/andP[]/andP[] /negPf llcE + + _.
    by rewrite if_same -if_and andbC llcE/= llcE => -> ->.
  case: rl => [|rll rlx rlr rlc]; case: rr => [|rrl rrx rrr rrc]/=.
  + by rewrite if_same -if_and andbC llcE/= llcE => -> ->.
  + rewrite if_same -!if_and => ? ? /andP[]/andP[] /negPf rrcE ? ?.
    rewrite andbC rrcE if_same -if_and andbC llcE/= llcE rrcE/=.
    by repeat (apply/andP; split).
  + rewrite if_same -!if_and => ? ? /andP[]/andP[]/andP[] /negPf rlcE ? ? _.
    rewrite andbC rlcE if_same -if_and andbC llcE/= llcE rlcE/=.
    by repeat (apply/andP; split).
  + rewrite !if_same -!if_and
      => ? ? /andP[]/andP[]/andP[] /negPf rlcE ? ? /andP[]/andP[] /negPf rrcE ? ?.
    rewrite andbC rrcE -!if_and andbC rlcE if_same -if_and andbC llcE/= llcE rlcE rrcE/=.
    by repeat (apply/andP; split).
- case: r => /= [|rl rx rr rc] /andP[]/andP[]/andP[] /negPf llcE ? ?.
    rewrite !if_same -if_and => /andP[]/andP[] /negPf lrcE ? ? _.
    rewrite andbC lrcE -if_and andbC llcE/= llcE lrcE/=.
    by repeat (apply/andP; split).
  case: rl => [|rll rlx rlr rlc]; case: rr => [|rrl rrx rrr rrc]/= /andP[]/andP[] /negPf lrcE ? ?.
  + rewrite !if_same -if_and andbC lrcE -if_and andbC llcE/= llcE lrcE/= => _.
    by repeat (apply/andP; split).
  + rewrite !if_same -!if_and => /andP[]/andP[] /negPf rrcE ? ?.
    rewrite andbC rrcE if_same -if_and andbC lrcE -if_and andbC llcE/= llcE lrcE rrcE/=.
    by repeat (apply/andP; split).
  + rewrite !if_same -!if_and => /andP[]/andP[]/andP[] /negPf rlcE ? ? _.
    rewrite andbC rlcE if_same -if_and andbC lrcE -if_and andbC llcE/= llcE lrcE rlcE/=.
    by repeat (apply/andP; split).
  + rewrite !if_same -!if_and
      => /andP[]/andP[]/andP[] /negPf rlcE ? ? /andP[]/andP[] /negPf rrcE ? ?.
      rewrite andbC rrcE -!if_and andbC rlcE if_same -if_and andbC lrcE -if_and andbC llcE/= llcE lrcE rlcE rrcE/=.

    by repeat (apply/andP; split).
Qed.
  
  

  

  

