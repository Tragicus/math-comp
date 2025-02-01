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

Lemma omap_obind (aT rT sT : Type) (f : aT -> option rT) (g : rT -> sT) (x : option aT) :
  omap g (obind f x) = obind (omap g \o f) x.
Proof. by case: x. Qed.

Lemma eq_obind (aT rT : Type) (f g : aT -> option rT) :
  f =1 g -> obind f =1 obind g.
Proof. by move=> + []. Qed.

Module RBtree.

Module Subdef.

Section Def.
Variables (d : Order.disp_t) (elt : orderType d).

Inductive t : Type :=
  | leaf
  | node : t -> elt -> t -> bool -> t.

Definition red := true.
Definition black := false.

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

Definition recolor c s :=
  match s with
  | leaf => leaf
  | node l x r _ => node l x r c
  end.

Fixpoint black_height s :=
  match s with
  | leaf => Some 0
  | node l _ r c =>
    obind (fun l =>
      obind (fun r =>
        if l == r then Some (~~ c + l) else None)
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

Definition head_wf t :=
  match t with
  | leaf => true
  | node l x r false => true
  | node l x r true => ~~ is_red l && ~~ is_red r
  end.

Fixpoint well_ordered s (itv : interval elt) := 
  match s with
  | leaf => true
  | node l x r _ => (x \in itv) && (well_ordered l (Interval itv.1 (BLeft x))) && (well_ordered r (Interval (BRight x) itv.2))
  end.

Definition is_rb (s : t) := (black_height s != None) && well_formed true s && well_ordered s `]-oo, +oo[.

Definition create l x r := node l x r black.
Arguments create : simpl never.

(* Balancing *)

Definition lbal l x r c :=
  if c then node l x r c else
  match l with
  | node (node ll llx llr true) lx lr true | node ll llx (node llr lx lr true) true =>
      node (node ll llx llr black) lx (node lr x r black) red
  | _ => node l x r c
  end.

Definition rbal l x r c :=
  if c then node l x r c else
  match r with
  | node (node rl rlx rlr true) rx rr true | node rl rlx (node rlr rx rr true) true =>
      node (node l x rl black) rlx (node rlr rx rr black) red
  | _ => node l x r c
  end.

Arguments lbal : simpl never.
Arguments rbal : simpl never.

Definition singleton x := create leaf x leaf.
Arguments singleton : simpl never.

Fixpoint add_subdef x s :=
  match s with
  | leaf => node leaf x leaf red
  | node l sx r c => if x == sx then node l x r c else
    if (x < sx)%O then lbal (add_subdef x l) sx r c
    else rbal l sx (add_subdef x r) c
  end.

Definition add x s := recolor black (add_subdef x s).
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

Lemma well_formedW (t : t elt) c c' : c ==> c' -> well_formed c' t -> well_formed c t.
Proof.
case: t => [//|l x r tc]/=.
by case: c => /=[-> //|_]; rewrite -andbA => /andP[] _.
Qed.

Lemma well_formedWF (t : t elt) c : well_formed c t -> well_formed black t.
Proof. exact: well_formedW. Qed.

Lemma well_formedEF (t : t elt) c : well_formed c t = ~~ (c && is_red t) && well_formed false t.
Proof. by case: t => /=[|l _ r c']; rewrite (andbF, andbA). Qed.

Lemma lbal_case (Pl P : t elt -> Prop) l x r c:
  ((c || head_wf l) -> P (node l x r c)) ->
  (forall ll llx llr lx lr,
    ~~ c -> Pl (node (node ll llx llr red) lx lr red) \/ Pl (node ll llx (node llr lx lr red) red) ->
    P (node (node ll llx llr black) lx (node lr x r black) red)) ->
  Pl l -> P (lbal l x r c).
Proof.
case: c => [/(_ isT)//|]/= + IHP.
by case: l => /=[|ll lx lr lc];
  try case: ll => [|lll llx llr llc]; 
  try case: lr => [|lrl lrx lrr lrc];
  try case: lc; try case: llc; try case: lrc;
  try move=> /(_ isT)//;
  move=> _ IHl; apply: IHP => //; (try by left); right.
Qed.

Lemma well_ordered_lbal l x r c itv : well_ordered (node l x r c) itv -> well_ordered (lbal l x r c) itv.
Proof.
move=> /=/andP[]/andP[] xI lwo rwo.
apply: (@lbal_case (fun l => well_ordered l (Interval itv.1 (BLeft x))) (fun s => well_ordered s itv)) => //.
  by move=> _ /=; rewrite xI lwo.
move=> ll llx llr lx lr/= _ /orP +; rewrite rwo.
move: xI; rewrite !itv_boundlr !bnd_simp/= => /andP[] _ xI.
rewrite [X in X || _](AC (2*4*1) (2*3*4*5*6*7*1))/=.
rewrite [X in _ || X](AC (3*4) (5*1*4*3*6*7*2))/=.
rewrite -!andb_orr; (repeat move=> /andP[]) => lxx Illx llxlx -> -> -> _.
rewrite lxx Illx llxlx.
repeat (apply/andP; split=> //); first exact/(le_trans Illx)/ltW.
exact/(le_trans _ xI)/ltW.
Qed.

Lemma black_height_lbal l x r c : black_height (lbal l x r c) = black_height (node l x r c).
Proof.
have orPP: forall P, P \/ P -> P by move=> p; case.
apply: (@lbal_case (fun l' => black_height l' = black_height l) (fun t => black_height t = black_height (node l x r c))) => //.
move=> ll llx llr lx lr/= /negPf ->.
case: (black_height ll) => /=[llh|/orPP <- //].
case: (black_height llr) => /=[llrh|/orPP <- //].
case: ifP => [/eqP ->|llhE [<- //|<-]]/=; last first.
  case: (black_height lr) => //= lrh.
  case: ifP => //= _.
  by rewrite add0n llhE.
case: (black_height lr) => /=[lrh|/orPP <- //].
rewrite !add0n.
case: ifP => /=[/eqP ->|llrhE /orPP <- /=]; last first.
  case: (black_height r) => //= rh.
  case: ifP => //= _.
  by rewrite (inj_eq (@addnI 1)) llrhE.
rewrite eqxx => /orPP <- /=.
case: (black_height r) => //= rh.
case: ifP => //= _.
by rewrite eqxx.
Qed.

Lemma rbal_case (Pr P : t elt -> Prop) l x r c:
  ((c || head_wf r) -> P (node l x r c)) ->
  (forall rl rlx rlr rx rr,
    ~~ c -> Pr (node (node rl rlx rlr red) rx rr red) \/ Pr (node rl rlx (node rlr rx rr red) red) ->
    P (node (node l x rl black) rlx (node rlr rx rr black) red)) ->
  Pr r -> P (rbal l x r c).
Proof.
case: c => [/(_ isT)//|]/= + IHP.
by case: r => /=[|rl rx rr rc];
  try case: rl => [|rll rlx rlr rlc]; 
  try case: rr => [|rrl rrx rrr rrc];
  try case: rc; try case: rlc; try case: rrc;
  try move=> /(_ isT)//;
  move=> _ IHl; apply: IHP => //; (try by left); right.
Qed.

Lemma well_ordered_rbal l x r c itv : well_ordered (node l x r c) itv -> well_ordered (rbal l x r c) itv.
Proof.
move=> /=/andP[]/andP[] xI lwo rwo.
apply: (@rbal_case (fun l => well_ordered l (Interval (BRight x) itv.2)) (fun s => well_ordered s itv)) => //.
  by move=> _ /=; rewrite xI lwo.
move=> rl rlx rlr rx rr/= _ /orP +; rewrite lwo.
move: xI; rewrite !itv_boundlr !bnd_simp/= => /andP[] Ix _.
rewrite [X in X || _](AC (2*4*1) (2*3*4*5*6*7*1))/=.
rewrite [X in _ || X](AC (3*4) (5*1*4*3*6*7*2))/=.
rewrite -!andb_orr; (repeat move=> /andP[]) => rxI xrlx rlxrx -> -> -> _.
rewrite rxI xrlx rlxrx.
repeat (apply/andP; split=> //); first exact/(le_trans Ix)/ltW.
exact/(le_trans _ rxI)/ltW.
Qed.

Lemma black_height_rbal l x r c : black_height (rbal l x r c) = black_height (node l x r c).
Proof.
have orPP: forall P, P \/ P -> P by move=> p; case.
apply: (@rbal_case (fun r' => black_height r' = black_height r) (fun t => black_height t = black_height (node l x r c))) => //.
move=> rl rlx rlr rx rr/= /negPf ->.
case: (black_height l) => /=[lh|//].
case: (black_height rl) => /=[rlh|/orPP <- //].
case: ifP => [/eqP ->|lhE]/=; last first.
  case: (black_height rlr) => //= [rlrh|/orPP <- //].
  case: ifP => //= [/eqP <-|rlhE]; case: (black_height rr) => //= [rrh|/orPP <- //]; last first.
    case: ifP => /=[_|_ /orPP <- //].
    by rewrite add0n rlhE => /orPP <-.
  rewrite add0n; case: ifP => [_|_ /orPP <- //]/=.
  by rewrite eqxx => /orPP <-/=; rewrite lhE.
case: (black_height rlr) => /=[rlrh|/orPP <- //].
case: ifP => //= [/eqP ->|rlhE]; last first.
  case: (black_height rr) => /=[rrh|/orPP <- //].
  case: ifP => [_|_ /orPP <- //]/=.
  by rewrite add0n (inj_eq (@addnI 1)) rlhE => /orPP <-/=.
case: (black_height rr) => /=[rrh|/orPP <- //].
rewrite add0n.
case: ifP => /=[/eqP ->|_ /orPP <- //].
rewrite eqxx => /orPP <- /=.
by rewrite (inj_eq (@addnI 1)) add0n.
Qed.

Lemma well_formed_add t x : well_formed black t -> well_formed black (add x t).
Proof.
move=> twf.
suff: if is_red t then well_formed black (add x t) else well_formed black (add_subdef x t).
  case: ifP => // _; rewrite /add; case: (add_subdef _ _) => [//|l tx r c]/=.
  by move=> /andP[] /well_formedWF -> /well_formedWF.
elim: t twf => [//|l IHl tx r IHr c]/= /andP[].
rewrite /add/=.
case: (ltgtP x tx) => /= _ lwf rwf; last first.
- by case: c lwf rwf => [|-> //] /well_formedWF -> /well_formedWF.
- pattern (rbal l tx (add_subdef x r) c).
  apply: (@rbal_case (fun l => well_formed false (recolor black l))) => //; last first.
  + move: rwf => /well_formedWF /IHr.
    case: ifP => _ //; case: (add_subdef _ _) => [//|rl rx rr rc]/=.
    by move=> /andP[] /well_formedWF -> /well_formedWF.
  + move: lwf => /well_formedWF /= -> rl rlx rlr rx rr /negPf ->/=.
    by move=> [/andP[]/andP[] /well_formedWF ->|/andP[] -> /andP[]] /well_formedWF -> /well_formedWF ->.
  case: c lwf rwf => /= /well_formedWF ->.
    by rewrite well_formedEF/= => /andP[] /negPf + /IHr => ->.
  move=> /IHr.
  rewrite /add; case: (add_subdef _ _) => [//|rl rx rr rc]/=.
  case: rc; last by rewrite if_same => ->.
  rewrite ![well_formed true _]well_formedEF => + /andP[] rlred rrred.
  by rewrite rlred rrred/= if_same => ->.
- pattern (lbal (add_subdef x l) tx r c).
  apply: (@lbal_case (fun l => well_formed false (recolor black l))) => //; last first.
  + move: lwf => /well_formedWF /IHl.
    case: ifP => _ //; case: (add_subdef _ _) => [//|ll lx lr lc]/=.
    by move=> /andP[] /well_formedWF -> /well_formedWF.
  + move: rwf => /well_formedWF rwf ll llx llr lx lr /negPf ->/=.
    by move=> [/andP[]/andP[] /well_formedWF ->|/andP[] -> /andP[]] /well_formedWF -> /well_formedWF ->.
  case: c lwf rwf => /=.
    by rewrite well_formedEF/= => /andP[] /negPf + /IHl + /well_formedWF => -> ->.
  move=> /IHl.
  rewrite /add; case: (add_subdef _ _) => [//|ll lx lr lc]/=.
  case: lc; last by rewrite if_same => ->.
  rewrite ![well_formed true _]well_formedEF => + + /andP[] llred lrred.
  by rewrite llred lrred/= if_same => ->.
Qed.
 
Lemma well_ordered_add t x itv : x \in itv -> well_ordered t itv -> well_ordered (add x t) itv.
Proof.
move=> xI two.
suff: well_ordered (add_subdef x t) itv.
  by rewrite /add; case: (add_subdef _ _).
elim: t itv xI two => /=[? -> //|l IHl tx r IHr tc itv] + /andP[]/andP[].
case: (ltgtP x tx) => [| |/= -> -> _ -> //] xtx xI txI lwo rwo.
  apply/well_ordered_lbal => /=; repeat (apply/andP; split=> //).
  apply/IHl => //.
  by move: xI; rewrite !itv_boundlr/= => /andP[] -> _.
apply/well_ordered_rbal => /=; repeat (apply/andP; split=> //).
apply/IHr => //.
by move: xI; rewrite !itv_boundlr/= bnd_simp xtx => /andP[].
Qed.

Lemma black_height_add t x :
  (black_height (add x t) == black_height t) || (black_height (add x t) == omap succn (black_height t)).
Proof.
have ->: black_height (add x t) = omap (addn (is_red (add_subdef x t))) (black_height (add_subdef x t)).
  rewrite /add; case: (add_subdef x t) => //= l _ r []; last first.
    by rewrite (@eq_omap _ _ (addn 0) id)// omap_id.
  rewrite omap_obind; apply/eq_obind => n/=.
  rewrite omap_obind; apply/eq_obind => m/=.
  by case: ifP.
suff ->: black_height (add_subdef x t) = black_height t.
  case: (is_red _).
    by rewrite (@eq_omap _ _ (addn 1) succn)// eqxx orbT.
  by rewrite (@eq_omap _ _ (addn 0) id)// omap_id eqxx.
elim: t => //= l IHl tx r IHr c.
case: (ltgtP x tx) => _ //=.
  by rewrite black_height_lbal/= IHl.
by rewrite black_height_rbal/= IHr.
Qed.

