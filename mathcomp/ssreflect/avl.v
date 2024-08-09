From HB Require Import structures.
From mathcomp Require Import all_ssreflect interval.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope order_scope.
Local Open Scope nat_scope.

Import Order.PreorderTheory Order.POrderTheory Order.TotalTheory Order.LatticeTheoryMeet Order.LatticeTheoryJoin.

Ltac mp :=
  match goal with
  | |- (?x -> _) -> _ => have /[swap]/[apply]: x
  end.

Ltac mk_conj :=
  match goal with
  | |- _ -> _ -> _ =>
      let H := fresh "H" in let H0 := fresh "H" in
      move=> H H0; move: (conj H H0) => /andP {H H0}
  end.

Lemma andbb b : b && b = b.
Proof. by case: b. Qed.

Lemma imply_mp (a b : bool) : (a && (a ==> b)) = (a && b).
Proof. by case: a; case: b. Qed.

Lemma imply_andbl (a b : bool) : (a ==> b) -> (a && b = a).
Proof. by case: a; case: b. Qed.

Lemma imply_orbl (a b : bool) : (b ==> a) -> (a || b = a).
Proof. by case: a; case: b. Qed.

Lemma andb_eq [T : eqType] (P : pred T) (x y : T) :
  P x && (x == y) = P y && (x == y).
Proof.
apply/andP/andP => [|] [Pxy /eqP xy]; (split; last by apply/eqP).
- by rewrite -xy.
- by rewrite xy.
Qed.

Lemma ifTb a b : (if a then true else b) = a || b.
Proof. by case: a => //; case: b. Qed.

Lemma ifFb a b : (if a then false else b) = ~~ a && b.
Proof. by case: a => //; case: b. Qed.

Definition diffn (n m : nat) :=
  if (n < m)%N then m - n else n - m.

Lemma diffn_subnE n m : diffn n m = (maxn n m) - (minn n m).
Proof. by rewrite /diffn; case: (ltnP n m). Qed.

Lemma diffnC n m : diffn n m = diffn m n.
Proof. by rewrite 2!diffn_subnE maxnC minnC. Qed.

Lemma diffnn n : diffn n n = 0.
Proof. by rewrite /diffn ltnn subnn. Qed.

Lemma diffnS n m : diffn n.+1 m.+1 = diffn n m.
Proof. by rewrite /diffn ltnS 2!subSS. Qed.

Lemma geq_diffn n m k : diffn n m <= k = ((n <= m + k) && (m <= n + k)).
Proof.
by rewrite /diffn; case: (ltnP n m) => [/ltnW|] nm;
  rewrite leq_subLR; [rewrite andbC|];
  apply/esym/imply_andbl/implyP => _;
  exact (leq_trans nm (leq_addr k _)).
Qed.

Lemma leq_diffnD n m k : diffn m k <= diffn m n + diffn n k.
Proof.
wlog: m k / m <= k => [H|].
  move: (leq_total m k) => /orP; case=> /H //.
  rewrite addnC; congr (_ <= _ + _); exact: diffnC.
rewrite 3!diffn_subnE => /[dup] /maxn_idPr -> /[dup] /minn_idPl -> mk.
case: (leqP m n) => [mn|/ltnW nm]; case: (leqP n k) => [nk|/ltnW kn].
- by rewrite addnC addnBA// subnK. 
- rewrite addnC addnBA// leq_sub2r// addnC addnBA// leq_subRL; first exact: leq_add.
  by rewrite -[k]addn0; apply/leq_add.
- by rewrite addnC leq_subLR addnA [m + _]addnBA// [m + _]addnC -[k + _ - _]addnBA// -addnA -{1}[k]addn0; apply/leq_add.
- suff ->: k = m by rewrite subnn.
  apply/anti_leq/andP; split => //.
  exact: (leq_trans kn).
Qed.

Definition map_or [A B : Type] (f : A -> B) (d : B) (x : option A) :=
  match x with
  | None => d
  | Some x => f x
  end.

Definition map2_or [A B C : Type] (f : A -> B -> C) (d : C) (a : option A) (b : option B) :=
  match a, b with
  | Some a, Some b => f a b
  | _, _ => d
  end.

Variant diffn_leq_xor_gt (k m n : nat) : bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> Type :=
  LtnDiffn : m + k < n -> diffn_leq_xor_gt k m n true false false true false true false true
  | GtnDiffn : n + k < m -> diffn_leq_xor_gt k m n false true true false false true false true
  | LeqDiffn : diffn m n <= k -> diffn_leq_xor_gt k m n false true false true true false true false.

Lemma leq_diffnP (k m n : nat) : diffn_leq_xor_gt k m n (m + k < n) (n <= m + k) (n + k < m) (m <= n + k) (diffn m n <= k) (k < diffn m n) (diffn n m <= k) (k < diffn n m).
Proof.
rewrite (diffnC n m).
case: (ltnP k (diffn m n)) => [|/[dup] lek]; last first.
  rewrite geq_diffn => /andP[] /[dup] + -> /[dup] + ->.
  do 2 (rewrite leqNgt => /negPf ->).
  exact: LeqDiffn.
rewrite ltnNge geq_diffn negb_and -2!ltnNge.
case: (ltnP (n + k) m) => [mgt _ |_]; last first.
  by case: (ltnP (m + k) n) => [+ _|//]; apply: LtnDiffn.
move: (ltn_addr k mgt); rewrite ltn_add2r => /(ltn_addr k.+1).
rewrite addnS ltnS; case (ltnP (m + k) n) => // _ _.
exact: GtnDiffn.
Qed.

Variant diffn_leq_xor_gt1 (m n : nat) : bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> Type :=
  LtnDiffn1 : m.+1 < n -> diffn_leq_xor_gt1 m n true false false true false true false true
  | GtnDiffn1 : n.+1 < m -> diffn_leq_xor_gt1 m n false true true false false true false true
  | LeqDiffn1 : diffn m n <= 1 -> diffn_leq_xor_gt1 m n false true false true true false true false.

Lemma leq_diffn1P (m n : nat) : diffn_leq_xor_gt1 m n (m.+1 < n) (n <= m.+1) (n.+1 < m) (m <= n.+1) (diffn m n <= 1) (1 < diffn m n) (diffn n m <= 1) (1 < diffn n m).
Proof.
rewrite -[m.+1]addn1 -[n.+1]addn1.
case: (leq_diffnP 1 m n); rewrite ?addn1.
- exact: LtnDiffn1.
- exact: GtnDiffn1.
- exact: LeqDiffn1.
Qed.

Variant diffn_leq_xor_gt2 (m n : nat) : bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> Type :=
  LtnDiffn2 : m.+2 < n -> diffn_leq_xor_gt2 m n true false false true false true false true
  | GtnDiffn2 : n.+2 < m -> diffn_leq_xor_gt2 m n false true true false false true false true
  | LeqDiffn2 : diffn m n <= 2 -> diffn_leq_xor_gt2 m n false true false true true false true false.

Lemma leq_diffn2P (m n : nat) : diffn_leq_xor_gt2 m n (m.+2 < n) (n <= m.+2) (n.+2 < m) (m <= n.+2) (diffn m n <= 2) (2 < diffn m n) (diffn n m <= 2) (2 < diffn n m).
Proof.
rewrite -[m.+2]addn2 -[n.+2]addn2.
case: (leq_diffnP 2 m n); rewrite ?addn2.
- exact: LtnDiffn2.
- exact: GtnDiffn2.
- exact: LeqDiffn2.
Qed.

Lemma behead_catl (T : eqType) (l r : seq T) : (behead (l ++ r) == behead l ++ r) = ((l != [::]) || (r == [::])).
Proof.
case: l => /= [|_ l]; last exact/eqxx.
case: r => //= x r.
transitivity false; last by apply/esym/negP => /eqP.
by apply/negP => /eqP => /(congr1 size)/= /n_Sn.
Qed.

(* Wrong if l is non-empty and constant and r starts with the element in l.
Lemma behead_catr (T : eqType) (l r : seq T) : (behead (l ++ r) == l ++ behead r) = (l == [::]).
Proof.
case: l => /= [|x l]; first exact/eqxx.
case: r => //=.  y r.
transitivity false; last by apply/esym/negP => /eqP.
by apply/negP => /eqP => /(congr1 size)/= /n_Sn.
Qed.*)

Lemma itvI (d' : unit) (T : orderType d') (a b c d : itv_bound T) :
  Interval a b `&` Interval c d = Interval (a `|` c) (b `&` d).
Proof. by []. Qed.

Lemma subitvE (disp : unit) (T : porderType disp) (itv itv' : interval T) :
  ((itv <= itv') = (itv'.1 <= itv.1) && (itv.2 <= itv'.2))%O.
Proof. by case: itv; case: itv'. Qed.

Lemma itv_boundlr (disp : unit) (T : porderType disp) (itv : interval T) (x : T) :
  x \in itv = (itv.1 <= BLeft x)%O && (BRight x <= itv.2)%O.
Proof. by case: itv. Qed.

Section Leo.
Variables (d : unit) (T : orderType d).
Implicit Types (n m : option T) (p q : T).

Definition leo n m :=
  map2_or <=%O true n m.

Lemma leo_trans p n m : leo n (Some p) -> leo (Some p) m -> leo n m.
Proof. by case: n => //; case: m => // n m; exact: le_trans. Qed.

Lemma leSomeo p n : leo (Some p) n = map_or (>= p)%O true n.
Proof. by case n. Qed.
Lemma leoSome p n : leo n (Some p) = map_or (<= p)%O true n.
Proof. by case n. Qed.

Definition lto n m :=
  map2_or <%O true n m.

Lemma lto_trans p n m : lto n (Some p) -> lto (Some p) m -> lto n m.
Proof. by case: n => //; case: m => // n m; exact: lt_trans. Qed.

Lemma leo_lto_trans p n m : leo n (Some p) -> lto (Some p) m -> lto n m.
Proof. by case: n => //; case: m => // n m; exact: le_lt_trans. Qed.

Lemma lto_leo_trans p n m : lto n (Some p) -> leo (Some p) m -> lto n m.
Proof. by case: n => //; case: m => // n m; exact: lt_le_trans. Qed.

Lemma ltSomeo p n : lto (Some p) n = map_or (> p)%O true n.
Proof. by case n. Qed.
Lemma ltoSome p n : lto n (Some p) = map_or (< p)%O true n.
Proof. by case n. Qed.

Lemma ltoW n m : lto n m -> leo n m.
Proof. by case: n => //; case: m => // n m; exact: ltW. Qed.

Definition omin n m :=
  match n, m with
  | None, _ => m
  | Some n, None => Some n
  | Some n, Some m => Some (Order.min n m)
  end.

End Leo.

Module Avl.

Module Subdef.

Section Def.
Variables (d : unit) (elt : orderType d).

Inductive t : Type :=
  | leaf
  | node : t -> elt -> t -> nat -> t.

Fixpoint eqb (s t : t) : bool :=
  match s, t with
  | leaf, leaf => true
  | node sl sx sr sh, node tl tx tr th => (sh == th) && (sx == tx) && (eqb sl tl) && (eqb sr tr)
  | _, _ => false
  end.

Lemma eqbP s t : reflect (s = t) (eqb s t).
Proof.
elim: s t => [|sl IHsl sx sr IHsr sh]; case=> [|ul ux ur uh]; apply/(iffP idP) => //=.
  by move=> /andP[]/andP[]/andP[] /eqP -> /eqP -> /IHsl -> /IHsr ->.
case=> sul -> sur ->; rewrite 2!eqxx/=; apply/andP; split; first exact/IHsl.
exact/IHsr.
Qed.

#[export]
HB.instance Definition _ := hasDecEq.Build t eqbP.

Definition height s :=
  match s with
  | leaf => 0
  | node _ _ _ h => h
  end.

Fixpoint well_formed s :=
  match s with
  | leaf => true
  | node l _ r h => (h == (maxn (height l) (height r)).+1) && (well_formed l) && (well_formed r)
  end.

Fixpoint balanced s :=
  match s with
  | leaf => true
  | node l _ r h => (diffn (height l) (height r) <= 2) && (balanced l) && (balanced r)
  end.

Fixpoint well_ordered s (itv : interval elt) := 
  match s with
  | leaf => true
  | node l x r _ => (x \in itv) && (well_ordered l (Interval itv.1 (BLeft x))) && (well_ordered r (Interval (BRight x) itv.2))
  end.

Definition is_avl s := (well_formed s) && (balanced s) && (well_ordered s `]-oo, +oo[).

Definition create l x r := (node l x r (maxn (height l) (height r)).+1).
Arguments create : simpl never.

Definition bal l x r := (if diffn (height l) (height r) <= 2 then create l x r else
  if (height r).+2 < height l then
    match l with
    | leaf => leaf
    | node ll lx lr lh => if height lr <= height ll then create ll lx (create lr x r) else
      match lr with
      | leaf => leaf
      | node lrl lrx lrr lrh => create (create ll lx lrl) lrx (create lrr x r)
      end
    end
  else match r with
    | leaf => leaf
    | node rl rx rr rh => if height rl <= height rr then create (create l x rl) rx rr else
      match rl with
      | leaf => leaf
      | node rll rlx rlr rlh => create (create l x rll) rlx (create rlr rx rr)
      end
    end).
Arguments bal : simpl never.

Definition singleton x := create leaf x leaf.
Arguments singleton : simpl never.

Fixpoint add x s :=
  match s with
  | leaf => singleton x
  | node l sx r h => if x == sx then node l x r h else
    if (x < sx)%O then bal (add x l) sx r
    else bal l sx (add x r)
  end.
Arguments add : simpl never.

Fixpoint add_min_element x s :=
  match s with
  | leaf => singleton x
  | node l sx r h => bal (add_min_element x l) sx r
  end.

Fixpoint add_max_element x s :=
  match s with
  | leaf => singleton x
  | node l sx r h => bal l sx (add_max_element x r)
  end.

Fixpoint join l x r :=
  match l with
  | leaf => add_min_element x r
  | node ll lx lr lh => (fix F r :=
    match r with
    | leaf => add_max_element x l
    | node rl rx rr rh =>
      if diffn lh rh <= 2 then create l x r else
      if rh.+2 < lh then bal ll lx (join lr x r)
      else bal (F rl) rx rr
    end) r
  end.

Fixpoint min s :=
  match s with
  | leaf => None
  | node leaf x _ _ => Some x
  | node l _ _ _ => min l
  end.

Fixpoint max s :=
  match s with
  | leaf => None
  | node _ x leaf _ => Some x
  | node _ _ r _ => max r
  end.

Fixpoint remove_min s :=
  match s with
  | leaf => leaf
  | node leaf _ r _ => r
  | node l x r _ => bal (remove_min l) x r
  end.

Definition merge l r :=
  match min r with
  | None => l
  | Some x => bal l x (remove_min r)
  end.

Definition concat l r :=
  match min r with
  | None => l
  | Some x => join l x (remove_min r)
  end.

Fixpoint split x s := 
  match s with
  | leaf => (leaf, false, leaf)
  | node l sx r _ => 
    if x == sx then (l, true, r) else
    if (x < sx)%O then let (llmem, lr) := split x l in let (ll, mem) := llmem in (ll, mem, join lr sx r)
    else let (rlmem, rr) := split x r in let (rl, mem) := rlmem in (join l sx rl, mem, rr)
  end.

Definition is_empty s := match s with | leaf => true | _ => false end.

Fixpoint remove x s :=
  match s with
  | leaf => leaf
  | node l sx r _ => 
    if x == sx then merge l r else
    if (x < sx)%O then bal (remove x l) sx r
    else bal l sx (remove x r)
  end.

(* This does not have a decreasing argument (essentially because we can split on the left or on the right. *)
Definition union_subdef n s t := (fix F n s t := match n with | 0 => leaf | S n =>
  match s with
  | leaf => t
  | node sl sx sr sh =>
    match t with
    | leaf => s
    | node tl tx tr th =>
      if th <= sh then
        if th == 1 then add tx s
        else let (l_, r) := split sx t in let (l, _) := l_ in join (F n sl l) sx (F n sr r)
      else
        if sh == 1 then add sx t
        else let (l_, r) := split tx s in let (l, _) := l_ in join (F n l tl) tx (F n r tr)
    end
  end end) n s t.

Definition union s t := union_subdef (height s + height t) s t.

Fixpoint inter s t :=
  match s with
  | leaf => leaf
  | node sl sx sr _ =>
    match split sx t with
    | (tl, false, tr) => concat (inter sl tl) (inter sr tr)
    | (tl, true, tr) => join (inter sl tl) sx (inter sr tr)
    end
  end.

Fixpoint split_bis x s : option (t * (unit -> t)) :=
  match s with
  | leaf => Some (leaf, fun=> leaf)
  | node sl sx sr _ => if x == sx then None else
    if (x < sx)%O then omap (fun lr : t * (unit -> t) => let (l, r) := lr in (l, fun _ => join (r tt) sx sr)) (split_bis x sl)
    else omap (fun lr : t * (unit -> t) => let (l, r) := lr in (join sl sx l, r)) (split_bis x sr)
  end.

Fixpoint disjoint s t :=
  match s, t with
  | leaf, _ | _, leaf => true
  | node sl sx sr _, _ =>
    match split_bis sx t with
    | None => false
    | Some (tl, tr) => disjoint sl tl && disjoint sr (tr tt)
    end
  end.

Fixpoint diff s t :=
  match s, t with
  | leaf, _ => leaf
  | _, leaf => s
  | node sl sx sr _, _ =>
    match split sx t with
    | (tl, false, tr) => join (diff sl tl) sx (diff sr tr)
    | (tl, true, tr) => concat (diff sl tl) (diff sr tr)
    end
  end.

Fixpoint subset_subdef n s t := match n with | 0 => true | S n =>
  match s with
  | leaf => true
  | node sl sx sr _ =>
    match t with
    | leaf => false
    | node tl tx tr _ => if sx == tx then subset_subdef n sl tl && subset_subdef n sr tr else
      if (sx < tx)%O then subset_subdef n (node sl sx leaf 0) tl && subset_subdef n sr t
      else subset_subdef n sl t && subset_subdef n (node leaf sx sr 0) tr
    end
  end end.

Definition subset s t := subset_subdef (height s + height t) s t.

Fixpoint fold rT (f : elt -> rT -> rT) s accu :=
  match s with
  | leaf => accu
  | node l x r _ => fold f r (f x (fold f l accu))
  end.

Fixpoint mem s x :=
  match s with
  | leaf => false
  | node l sx r _ => (x == sx) || (mem (if (x < sx)%O then l else r) x)
  end.

Fixpoint all (p : pred elt) s :=
  match s with
  | leaf => true
  | node l x r _ => p x && all p l && all p r
  end.

Fixpoint has (p : pred elt) s :=
  match s with
  | leaf => false
  | node l x r _ => p x || has p l || has p r
  end.

Fixpoint filter (p : pred elt) s :=
  match s with
  | leaf => leaf
  | node l x r _ => if p x then join (filter p l) x (filter p r)
    else concat (filter p l) (filter p r)
  end.

Fixpoint partition (p : pred elt) s :=
  match s with
  | leaf => (leaf, leaf)
  | node l x r _ =>
    let (lt, lf) := partition p l in
    let (rt, rf) := partition p r in
    if p x then (join lt x rt, concat lf rf)
    else (concat lt rt, join lf x rf)
  end.

Fixpoint card s :=
  match s with
  | leaf => 0
  | node l _ r _ => (card l + card r).+1
  end.

Fixpoint elements_subdef accu s :=
  match s with
  | leaf => accu
  | node l x r _ => elements_subdef (x :: elements_subdef accu r) l
  end.

Definition elements := elements_subdef [::].

Definition choose s :=
  match s with
  | leaf => None
  | node _ x _ _ => Some x
  end.

Definition try_join l x r :=
  if (map_or (< x)%O true (max l)) && (map_or (> x)%O true (min r)) then join l x r
  else union l (add x r).

Definition try_concat l r :=
  match l, r with
  | leaf, s | s, leaf => s
  | _, _ =>
    match min r with
    | None => l
    | Some mr => try_join l mr (remove_min r)
    end
  end.

End Def.

Section Def2.
Variables (d d' : unit) (elt : orderType d) (elt' : orderType d').

Fixpoint map (f : elt -> elt') s :=
  match s with
  | leaf => leaf elt'
  | node l x r _ => try_join (map f l) (f x) (map f r)
  end.

Fixpoint filter_map (f : elt -> option elt') s :=
  match s with
  | leaf => leaf elt'
  | node l x r _ => let l := filter_map f l in
    let r := filter_map f r in
    match f x with
    | None => try_concat l r
    | Some x => try_join l x r
    end
  end.

End Def2.

Section Theory.
Variables (d d' : unit) (elt : orderType d) (elt' : orderType d').
Implicit Types (s l r : t elt) (x : elt) (itv : interval elt).

Lemma elements_subdefE a s : elements_subdef a s = elements s ++ a.
Proof.
rewrite /elements -{1}/([::] ++ a).
elim: s [::] => [//|l IHl x r IHr h] s/=.
by rewrite IHr -cat_cons IHl.
Qed.

Lemma elements_node l x r h :
  elements (node l x r h) = elements l ++ x :: elements r.
Proof.
rewrite /elements.
elim: l x => [//|ll IHl lx lr IHr n] x/=.
by rewrite !elements_subdefE !cats0 -catA cat_cons.
Qed.

Lemma cardE s: card s = size (elements s).
Proof.
elim: s => [//|/= l -> x r -> h]/=.
by rewrite elements_node size_cat/= addnS.
Qed.

Lemma height0 s : well_formed s -> height s == 0 = (s == leaf elt).
Proof. by case: s => [//|l x r h] /= /andP[]/andP[] /eqP ->. Qed.

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

Lemma all_andb p q s : all (predI p q) s = all p s && all q s.
Proof.
elim: s => [//|] l IHl x r IHr h/=.
rewrite -!andbA; congr andb.
rewrite andbCA IHl -andbA; congr andb.
rewrite andbCA [in RHS]andbCA; congr andb.
by rewrite andbCA; congr andb.
Qed.

Lemma eq_all p q s : p =1 q -> all p s = all q s.
Proof. by move=> pq; elim: s => [//|] /= l -> x r -> h; rewrite pq. Qed.

Lemma well_orderedP s itv : well_ordered s itv = (well_ordered s `]-oo, +oo[ && all (fun x => x \in itv) s).
Proof.
elim: s itv => [//|] l IHl x r IHr h/= itv.
case/boolP: (x \in itv) => /=; last by rewrite andbF.
rewrite itv_boundlr => /andP[] ix xi.
rewrite IHl [in RHS]IHl.
case: (well_ordered _ _) => //=.
rewrite IHr [in RHS]IHr.
case: (well_ordered _ _) => /=; last by rewrite !andbF.
rewrite andbACA -!all_andb; congr andb; apply/eq_all => y /=; rewrite !itv_boundlr/=.
  rewrite andbCA; congr andb.
  case/boolP: (_ <= _)%O => //= yx.
  by apply/esym/(le_trans yx)/(le_trans _ xi); rewrite bnd_simp.
rewrite !andbA; congr andb.
case/boolP: (_ <= _)%O => //= xy.
by apply/esym/(le_trans ix)/(le_trans _ xy); rewrite bnd_simp.
Qed.
  
Lemma mem_well_ordered x s itv: well_ordered s itv -> mem s x -> (x \in itv).
Proof.
elim: s itv => [//|l IHl sx r IHr /= _] itv /andP[]/andP[] /[dup] sxP.
rewrite itv_boundlr => /andP[] isx sxi lwo rwo.
case /comparable_ltgtP: (comparableT x sx) => /= [xsx|sxx|-> //].
  by apply/IHl/(well_orderedW _ lwo); rewrite subitvE/= lexx (le_trans _ sxi)//= bnd_simp.
by apply/IHr/(well_orderedW _ rwo); rewrite subitvE/= lexx (le_trans isx)//= bnd_simp.
Qed.

Lemma mem_node y l x r h : well_ordered (node l x r h) `]-oo, +oo[ -> mem (node l x r h) y = (y == x) || (mem l y) || (mem r y).
Proof.
rewrite /mem /=; case /comparable_ltgtP: (comparableT x y) => [xy|yx|//]/= /andP[] lwo rwo.
  by rewrite orbC -[LHS]orbF; congr orb; apply/esym/negP => /(mem_well_ordered lwo) /andP[_]/= /(lt_trans xy); rewrite ltxx.
by rewrite -[LHS]orbF; congr orb; apply/esym/negP => /(mem_well_ordered rwo) /andP[] /(lt_trans yx) + _; rewrite ltxx.
Qed.

Lemma mem_elements s x : well_ordered s `]-oo, +oo[ -> mem s x = (x \in (elements s)).
Proof.
elim: s => [//|l IHl y r IHr h]/= /andP[] lwo rwo.
rewrite elements_node mem_cat in_cons orbCA.
case: (comparable_ltgtP (comparableT x y)) => //= xy.
  rewrite (IHl (well_orderedWT lwo)) orbC.
  case/boolP: (x \in elements r) => //.
  rewrite -(IHr (well_orderedWT rwo)) => /(mem_well_ordered rwo).
  by rewrite in_itv/= andbT => /(lt_trans xy); rewrite ltxx.
rewrite (IHr (well_orderedWT rwo)).
case/boolP: (x \in elements l) => //.
rewrite -(IHl (well_orderedWT lwo)) => /(mem_well_ordered lwo)/=.
by rewrite in_itv/= => /(lt_trans xy); rewrite ltxx.
Qed.

Lemma sorted_elements s : well_ordered s `]-oo, +oo[ -> sorted <%O (elements s).
Proof.
elim: s => //= l IHl x r IHr h /andP[] lwo rwo.
rewrite elements_node; apply/(sortedP x) => i.
rewrite size_cat/= addnS -addSn => ilt.
rewrite !nth_cat.
case: (ltnP i.+1 (size (elements l))) => [iltl|].
  by rewrite (ltnW iltl); move: lwo => /well_orderedWT /IHl /(sortedP x) ->.
rewrite leq_eqVlt => /orP[/eqP iE|].
  rewrite iE leqnn subnn/=.
  suff: mem l (nth x (elements l) i).
    by move=> /(mem_well_ordered lwo); rewrite in_itv.
  rewrite mem_elements; last exact/(well_orderedWT lwo).
  by apply/mem_nth; rewrite iE.
rewrite ltnS ltnNge => /[dup] + -> /=; rewrite leq_eqVlt => /orP[/eqP iE|igt].
  rewrite iE subSn// subnn/=.
  suff: mem r (nth x (elements r) 0).
    by move=> /(mem_well_ordered rwo); rewrite in_itv andbT.
  rewrite mem_elements; last exact/(well_orderedWT rwo).
  apply/mem_nth; move: ilt; rewrite iE.
  by case: (size _) => //; rewrite addn0 ltnn.
rewrite subSn ?(ltnW igt)//= -subSS subSn//=.
move: rwo => /well_orderedWT /IHr /(sortedP x) -> //.
by rewrite -subSn// ltn_subLR// ltnS (ltnW igt).
Qed.

Lemma well_formed_create l x r : well_formed l -> well_formed r -> well_formed (create l x r).
Proof. by rewrite /= eqxx => -> ->. Qed.

Lemma balanced_create l x r : balanced l -> balanced r -> diffn (height l) (height r) <= 2 -> balanced (create l x r).
Proof. by move=> /= -> -> ->. Qed.

Lemma well_ordered_create l x r itv : x \in itv -> well_ordered l (Interval itv.1 (BLeft x)) -> well_ordered r (Interval (BRight x) itv.2) -> well_ordered (create l x r) itv.
Proof. by move=> /= -> ->. Qed.

Lemma mem_create y l x r : well_ordered (create l x r) `]-oo, +oo[ -> mem (create l x r) y = (y == x) || (mem l y) || (mem r y).
Proof. exact: mem_node. Qed.

Lemma elements_create l x r : elements (create l x r) = elements l ++ x :: elements r.
Proof. exact: elements_node. Qed.

Lemma card_create l x r : card (create l x r) = (card l + card r).+1.
Proof. by []. Qed.

Ltac case_bal l r :=
  let ll := fresh "ll" in
  let lx := fresh "lx" in
  let lr := fresh "lr" in
  let lh := fresh "lh" in
  let lrd := fresh "lrd" in
  let rl := fresh "rl" in
  let rx := fresh "rx" in
  let rr := fresh "rr" in
  let rh := fresh "rh" in
  let lrl := fresh "lrl" in
  let lrx := fresh "lrx" in
  let lrr := fresh "lrr" in
  let lrh := fresh "lrh" in
  let rll := fresh "rll" in
  let rlx := fresh "rlx" in
  let rlr := fresh "rlr" in
  let rlh := fresh "rlh" in
  rewrite /bal;
  case: (leq_diffn2P (height l) (height r)) => [| |lrd];
  [case: r => [//|rl rx rr rh]; case: (ltnP (height rr) (height rl));
    [case: rl => [//|rll rlx rlr rlh]|]
  |case: l => [//|ll lx lr lh]; case: (ltnP (height ll) (height lr));
    [case: lr => [//|lrl lrx lrr lrh]|]
  |].

Lemma well_formed_bal l x r : well_formed l -> well_formed r -> well_formed (bal l x r).
Proof.
case_bal l r; last exact: well_formed_create.
- by move=> _ _ /= -> /andP[]/andP[] _ /andP[]/andP[] _ -> -> ->; rewrite !eqxx.
- by move=> _ _ /= -> /andP[]/andP[] _ -> ->; rewrite !eqxx.
- by move=> _ _ /= /andP[]/andP[] _ -> /andP[]/andP[] _ -> -> ->; rewrite !eqxx.
- by move=> _ _ /= /andP[]/andP[] _ -> -> ->; rewrite !eqxx. 
Qed.

Lemma height_bal l x r : well_formed l -> well_formed r -> height (bal l x r) <= height (create l x r) <= (height (bal l x r)).+1.
Proof.
case_bal l r => /=; last by rewrite leqnn leqnSn.
- rewrite maxnSS !maxnA -[maxn (maxn _ _) (height rlr)]maxnA.
  move: (maxn (height rll) (height rlr)) => h /[dup] + /ltnW/maxn_idPl -> + _ /andP[]/andP[] /eqP rhE /andP[]/andP[] /eqP rlhE _ _ _.
  subst rh rlh; rewrite !ltnS => rrh /ltnW lh.
  by rewrite (maxn_idPr lh) (maxn_idPl rrh) (maxn_idPr (leqW (leqW lh))) leqnSn leqnn.
- move=> /[dup] + /maxn_idPr -> + _ /andP[]/andP[] /eqP rhE _ _.
  rewrite {}rhE !ltnS -maxnSS maxnAC => rlrr /ltnW lrr.
  by rewrite (maxn_idPr lrr) (maxn_idPr (ltnW (leqW lrr))) !ltnS leq_maxl geq_max leqnSn ltnS rlrr.
- rewrite maxnSS !maxnA -[maxn (maxn _ _) (height lrr)]maxnA.
  move: (maxn (height lrl) (height lrr)) => h /[dup] + /ltnW/maxn_idPr -> + /andP[]/andP[] /eqP lhE _ /andP[]/andP[] /eqP lrhE _ _ _.
  subst lh lrh; rewrite !ltnS => llh /ltnW rh.
  by rewrite (maxn_idPr llh) (maxn_idPl rh) (maxn_idPl (leqW (leqW rh))) leqnSn leqnn.
- move=> /[dup] + /maxn_idPl -> + /andP[]/andP[] /eqP lhE _ _ _.
  rewrite {}lhE !ltnS -maxnSS maxnCA => lrll /ltnW rll.
  by rewrite (maxn_idPl rll) (maxn_idPl (ltnW (leqW rll))) -maxnSS leq_maxr geq_max ltnS lrll leqnSn.
Qed.

Lemma diffn_height_bal l x r : well_formed l -> well_formed r -> diffn (height (bal l x r)) (height (create l x r)) <= 1.
Proof.
move=> lwf rwf; move: (height_bal x lwf rwf) => /andP[] bc cb.
by rewrite geq_diffn !addn1 (leqW bc).
Qed.

Lemma balanced_bal l x r : well_formed l -> well_formed r -> balanced l -> balanced r -> diffn (height l) (height r) <= 3 -> balanced (bal l x r).
Proof.
case_bal l r => /=.
- move=> /= + + _ /andP[]/andP[] /eqP rhE /andP[]/andP[] /eqP rlhE _ _ _ -> /andP[]/andP[] + /andP[]/andP[] + -> -> ->.
  subst rh rlh; rewrite !ltnS diffnS => rrle.
  rewrite (maxn_idPl (leqW rrle)) !geq_diffn !addn2 !addn3 !ltnS => + /andP[] rrge _ /andP[] rllrlr rlrrll /andP[] _; mk_conj => /anti_leq lh.
  rewrite -ltnS -[height l <= _]ltnS -!maxnSS lh -!maxnSS maxnAC (maxn_idPr (leqnSn _)) maxnAC (maxn_idPr (leqnSn _)).
  move: rrge; rewrite !geq_max !leq_max !ltnS => /andP[] rllrr rlrrr.
  rewrite rllrlr rlrrll !(leqW (leqW (leqnSn _))) !leqnSn (leqW rlrrr) (leqW rlrrll)/=.
  have: maxn (height rll) (height rlr) <= minn (height rll).+2 (height rlr).+2.
    by rewrite leq_min !geq_max !(leqW (leqnSn _)) rlrrll rllrlr.
  by rewrite leq_min => /andP[] /(leq_trans rrle) -> /(leq_trans rrle) ->.
- move=> rlrr + _ /= /andP[]/andP[] /eqP rhE _ _ -> /andP[]/andP[] + -> ->.
  subst rh; rewrite (maxn_idPr rlrr) /= !geq_diffn !addn2 !addn3 !ltnS => + /andP[] _ rrrl /andP[] _; mk_conj=> /anti_leq rrE.
  move: rlrr rrrl; rewrite -rrE !ltnS => rll lrl.
  by rewrite -!maxnSS !geq_max !leq_max rll (leqW lrl) (leqW (leqW lrl)) (leqW rll) (leqW (leqW (leqnSn _))) orbT.
- move=> /= + + /andP[]/andP[] /eqP lhE _ /andP[]/andP[] /eqP lrhE _ _ _ /andP[]/andP[] + -> /andP[]/andP[] + -> -> ->.
  subst lh lrh; rewrite !geq_diffn !addn2 !addn3 !ltnS => llle.
  rewrite geq_max (maxn_idPr (leqW llle)) !ltnS => + /andP[_]/andP[] lrlll lrrll /andP[] lrllrr lrrlrl /andP[]; mk_conj=> /anti_leq rE _.
  rewrite -[maxn _ (height r) <= _]ltnS -[height r <= _]ltnS -!maxnSS {}rE -!maxnSS maxnCA (maxn_idPl (leqnSn _)) maxnCA (maxn_idPl (leqnSn _)) !geq_max !leq_max.
  rewrite lrllrr (leqW (leqW lrlll)) !ltnS (leqW lrrll) (leqW lrlll) !leqnSn (leqW lrllrr) !(leqW (leqW (leqnSn _)))/= orbT/= !andbT.
  have: maxn (height lrl) (height lrr) <= minn (height lrl).+2 (height lrr).+2.
    by rewrite leq_min !geq_max !(leqW (leqnSn _)) lrllrr lrrlrl.
  rewrite leq_min => /andP[] /(leq_trans llle) -> /(leq_trans llle) ->.
  by rewrite orbT.
- move=> lrll + /andP[]/andP[] /eqP lhE _ _ _ /andP[]/andP[] + -> -> ->.
  subst lh; rewrite !geq_diffn !addn2 !addn3 !ltnS => + /andP[] lllr _ /andP[]; mk_conj => /anti_leq rE _.
  by rewrite -!maxnSS leq_max (leqW lllr)/= geq_max (leqW lrll)/= -2!ltnS !andbT -2![X in [&& _, _ & X]]ltnS rE leq_maxr !geq_max (leqW (leqW (leqnSn _))) (leqW (leqW (leqW lrll))) (leqW (leqW lllr)) (leqW (leqW (leqW (leqnSn _)))).
- by move=> _ _ ->; rewrite lrd.
Qed.

Lemma well_ordered_bal l x r itv : well_ordered (bal l x r) itv = ((x \in itv) && well_ordered l (Interval itv.1 (BLeft x)) && well_ordered r (Interval (BRight x) itv.2)).
Proof.
case_bal l r => //= _ _; apply/idP/idP => /andP[]/andP[];
    rewrite !itv_boundlr/= !bnd_simp.
- move=> /andP[] irlx rlxi /andP[]/andP[]/andP[] ix xrlx -> -> /andP[]/andP[]/andP[] rlxrx rxi -> ->.
  rewrite ix (lt_trans xrlx rlxrx) rxi xrlx rlxrx/= (le_trans _ rxi)// bnd_simp.
  exact/ltW/(lt_trans xrlx).
- move=> /andP[] ix xi -> /andP[]/andP[]/andP[] xrx rxi /andP[]/andP[]/andP[] xrlx rlxrx -> -> ->.
  rewrite ix xrlx rlxrx rxi/= !andbT; apply/andP; split.
    by apply/(le_trans ix); rewrite bnd_simp; apply/ltW.
  by apply/(le_trans _ rxi); rewrite bnd_simp; apply/ltW.
- move=> /andP[] irx rxi /andP[]/andP[]/andP[] ix xrx -> -> ->.
  by rewrite ix xrx rxi/= (le_trans _ rxi)// bnd_simp ltW.
- move=> /andP[] ix xi -> /andP[]/andP[]/andP[] xrx rxi -> ->.
  by rewrite ix rxi xrx/= (le_trans ix)// bnd_simp ltW.
- move=> /andP[] ilrx lrxi /andP[]/andP[]/andP[] ilx lxlrx -> -> /andP[]/andP[]/andP[] lrxx xi -> ->.
  rewrite xi ilx (lt_trans lxlrx lrxx) lxlrx lrxx/= (le_trans ilx)// bnd_simp.
  exact/ltW/(lt_trans lxlrx).
- move=> /andP[] ix xi /andP[]/andP[]/andP[] ilx lxx -> /andP[]/andP[]/andP[] lxlrx lrxx -> -> ->.
  rewrite ilx lxlrx lrxx xi/= !andbT; apply/andP; split.
    by apply/(le_trans ilx); rewrite bnd_simp; apply/ltW.
  by apply/(le_trans _ xi); rewrite bnd_simp; apply/ltW.
- move=> /andP[] ilx lxi -> /andP[]/andP[]/andP[] lxx xi -> ->.
  by rewrite xi ilx lxx/= (le_trans ilx)// bnd_simp ltW.
- move=> /andP[] ix xi /andP[]/andP[]/andP[] ilx lxx -> -> ->.
  by rewrite ilx lxx xi/= (le_trans _ xi)// bnd_simp ltW.
Qed.

Lemma elements_bal l x r : elements (bal l x r) = elements l ++ x :: elements r.
Proof.
case_bal l r; rewrite !elements_node//.
- by move=> _ _; rewrite -!catA !cat_cons.
- by move=> _ _; rewrite -!catA !cat_cons.
- by move=> _ _; rewrite -!catA !cat_cons -catA.
- by move=> _ _; rewrite -!catA !cat_cons.
Qed.

Lemma mem_bal y l x r : well_ordered (bal l x r) `]-oo, +oo[ -> mem (bal l x r) y = (y == x) || (mem l y) || (mem r y).
Proof.
move=> wo; rewrite mem_elements// elements_bal mem_cat in_cons orbCA orbA.
move: wo; rewrite well_ordered_bal => /andP[] /andP[] _.
move=> /well_orderedWT/mem_elements <-. 
by move=> /well_orderedWT/mem_elements <-. 
Qed.

Lemma card_bal l x r : card (bal l x r) = (card l + card r).+1.
Proof. by case_bal l r => // _ _ /=; rewrite !addSn !addnS !addnA. Qed.

Lemma well_formed_add x s : well_formed s -> well_formed (add x s).
Proof.
elim: s => [//|l IHl sx r IHr h] /= /andP[]/andP[] /eqP -> {h} /[dup] lwf {}/IHl xlwf /[dup] rwf {}/IHr xrwf.
case /comparable_ltgtP: (comparableT x sx) => _.
- exact: well_formed_bal.
- exact: well_formed_bal.
- by rewrite /= eqxx lwf.
Qed.

Lemma balanced_height_add x s : well_formed s -> balanced s -> (balanced (add x s) && (height s <= height (add x s) <= (height s).+1)).
Proof.
elim: s => [//|l IHl sx r IHr h] /=
    /andP[]/andP[] /eqP -> {h} /[dup] lwf /[dup] /(well_formed_add x) xlwf {}/IHl IHl /[dup] rwf /[dup] /(well_formed_add x) xrwf {}/IHr IHr
    /andP[]/andP[] lrd /[dup] lb {}/IHl /andP[] xlb /andP[] lxl xll /[dup] rb {}/IHr /andP[] xrb /andP[] rxr xrr.
case /comparable_ltgtP: (comparableT x sx) => _; last first.
- by rewrite /= lrd lb rb leqnn leqnSn.
- apply/andP; split.
    apply: balanced_bal => //.
    apply/(leq_trans (leq_diffnD (height r) _ _))/(@leq_add _ _ 2 1) => //.
    by rewrite geq_diffn !addn1 xrr (leqW rxr).
  move: (height_bal sx lwf xrwf) => /andP[] bc cb.
  apply/andP; split; last first.
    by apply: (leq_trans bc) => /=; rewrite ltnS geq_max -!maxnSS !leq_max leqnSn xrr orbT.
  case /boolP: (diffn (height l) (height (add x r)) <= 2) => [lxrd|].
    by rewrite /bal lxrd /= ltnS geq_max leq_maxl leq_max rxr orbT.
  move: rxr; rewrite leq_eqVlt => /orP; case=> [/eqP <-|]; first by rewrite lrd.
  move: xrr; mk_conj=> /anti_leq {}xrr lxrd.
  rewrite -ltnS; refine (leq_trans _ cb); rewrite /= ltnS.
  move: lrd lxrd; rewrite xrr !geq_diffn !addn2 => /andP[] /leqW -> _.
  rewrite /= -leqNgt => /ltnW/ltnW lr.
  by rewrite (maxn_idPr lr) (maxn_idPr (leqW lr)) leqnn.
- apply/andP; split.
    apply: balanced_bal => //.
    apply/(leq_trans (leq_diffnD (height l) _ _))/(@leq_add _ _ 1 2) => //.
    by rewrite geq_diffn !addn1 xll (leqW lxl).
  move: (height_bal sx xlwf rwf) => /andP[] bc cb.
  apply/andP; split; last first.
    by apply: (leq_trans bc) => /=; rewrite ltnS geq_max -!maxnSS !leq_max leqnSn xll orbT.
  case /boolP: (diffn (height (add x l)) (height r) <= 2) => [xlrd|].
    by rewrite /bal xlrd /= ltnS geq_max leq_maxr leq_max lxl.
  move: lxl; rewrite leq_eqVlt => /orP; case=> [/eqP <-|]; first by rewrite lrd.
  move: xll; mk_conj=> /anti_leq {}xll xlrd.
  rewrite -ltnS; refine (leq_trans _ cb); rewrite /= ltnS.
  move: lrd xlrd; rewrite xll !geq_diffn !addn2 => /andP[] _ /leqW ->.
  rewrite andbT -leqNgt => /ltnW/ltnW rl.
  by rewrite (maxn_idPl rl) (maxn_idPl (leqW rl)) leqnn.
Qed.

Lemma balanced_add x s : well_formed s -> balanced s -> balanced (add x s).
Proof. by move=> swf /(balanced_height_add x swf) /andP[]. Qed.

Lemma well_ordered_add x s itv : well_ordered s itv -> x \in itv -> well_ordered (add x s) itv.
Proof.
elim: s itv => /= [_ itv -> //|] l IHl sx r IHr h itv /andP[]/andP[] sxi lwo rwo xi.
case /comparable_ltgtP: (comparableT x sx) => [sxx|xsx|->].
- rewrite well_ordered_bal sxi rwo IHl//=.
  by move: xi; rewrite !itv_boundlr => /andP[] -> _; rewrite bnd_simp.
- rewrite well_ordered_bal sxi lwo IHr//=.
  by move: xi; rewrite !itv_boundlr => /andP[_] ->; rewrite bnd_simp xsx.
- by rewrite /= sxi lwo.
Qed.

Lemma is_avl_add x s : is_avl s -> is_avl (add x s).
Proof.
move=> /andP[]/andP[] swf sb swo; apply/andP; split; [apply/andP; split|].
- exact/well_formed_add.
- exact/balanced_add.
- exact/well_ordered_add.
Qed.

Lemma mem_add y x s : well_ordered s `]-oo, +oo[ -> mem (add x s) y = (y == x) || (mem s y).
Proof.
elim: s => /= [_|l IHl sx r IHr h /andP[] lwo rwo]; first by rewrite if_same.
case /comparable_ltgtP: (comparableT x sx) => [sxx|xsx|<-]; last first.
- by rewrite /= orbA orbb.
- rewrite mem_bal; last first.
    rewrite well_ordered_bal lwo/=; apply/well_ordered_add => //.
    by rewrite in_itv/= xsx.
  rewrite (IHr (well_orderedWT rwo))//.
  move: (@mem_node y l sx r h) => /= ->; last by rewrite lwo.
  by rewrite !orbA; congr orb; rewrite orbC !orbA.
- rewrite mem_bal; last first.
    by rewrite well_ordered_bal rwo/= andbT; apply/well_ordered_add.
  rewrite (IHl (well_orderedWT lwo)).
  move: (@mem_node y l sx r h) => /= ->; last by rewrite lwo.
  by rewrite !orbA; congr orb; rewrite orbAC orbC !orbA.
Qed.

Lemma card_add x s : card (add x s) = card s + (~~ mem s x).
Proof.
elim: s => [//|] l IHl sx r IHr h/=.
case /comparable_ltgtP: (comparableT x sx) => /= _.
- by rewrite card_bal IHl addSn addnAC.
- by rewrite card_bal IHr addSn addnA.
- by rewrite addn0.
Qed.

Lemma well_formed_add_min_element x s : well_formed s -> well_formed (add_min_element x s).
Proof.
elim: s => [//|] l IHl sx r _ h /= /andP[]/andP[] _ {h} lwf rwf.
by apply/well_formed_bal => //; apply/IHl.
Qed.

Lemma balanced_height_add_min_element x s : well_formed s -> balanced s -> (balanced (add_min_element x s) && (height s <= height (add_min_element x s) <= (height s).+1)).
Proof.
elim: s => [//|] l IHl sx r IHr h /=
    /andP[]/andP[] /eqP -> {h} /[dup] lwf {}/IHl IHl /[dup] rwf {}/IHr IHr
    /andP[]/andP[] lrd /[dup] lb {}/IHl /andP[] xlb /andP[] lxl xll /[dup] rb {}/IHr /andP[] xrb /andP[] rxr xrr.
apply/andP; split.
  apply balanced_bal => //; first exact/well_formed_add_min_element.
  apply/(leq_trans (leq_diffnD (height l) _ _))/(@leq_add _ _ 1 2) => //.
  by rewrite geq_diffn !addn1 xll (leqW lxl).
rewrite /bal; case /boolP: (diffn (height (add_min_element x l)) (height r) <= 2) => [_|].
  by rewrite /= !ltnS -maxnSS !geq_max !leq_max lxl leqnn xll leqnSn !orbT.
move: lxl; rewrite leq_eqVlt => /orP; case=> [/eqP <-|].
  by rewrite lrd.
move: xll; mk_conj=> /anti_leq /[dup] {}xll ->.
move: lrd; rewrite 2!geq_diffn !addn2 ltnS => /andP[] + /leqW ->.
rewrite andbT -ltnNge; mk_conj=> /anti_leq lrh.
move: xll; rewrite {}lrh (maxn_idPl (leqW (leqnSn _))) leqnn.
case: (add_min_element x l) (well_formed_add_min_element x lwf) xlb => [//|] xll xlx xlr xlh /= /andP[]/andP[] /eqP -> {xlh} xllwf xlrwf /andP[]/andP[] xd xllb xlrb /eqP.
rewrite eqSS => /eqP; case: (ltnP (height xll) (height xlr)); last first.
  by move=> + xllE /=; rewrite xllE maxnSS !ltnS maxnCA (maxn_idPl (leqnSn _)) leq_maxr geq_max leqnSn => ->.
case: xlr xlrwf xlrb xd => [//|] xlll xllx xllr xllh /= /andP[]/andP[] /eqP -> {xllh} _ _ _ _ + /eqP.
rewrite maxnSS !ltnS eqSS maxnA -[maxn (maxn _ _) (height xllr)]maxnA => /maxn_idPr -> /eqP ->.
by rewrite (maxn_idPl (leqnSn _)) leqnn leqnSn.
Qed.

Lemma balanced_add_min_element x s : well_formed s -> balanced s -> balanced (add_min_element x s).
Proof. by move=> swf /(balanced_height_add_min_element x swf)/andP[]. Qed.

Lemma well_ordered_add_min_element x s itv : well_ordered s (Interval (BRight x) itv.2) -> x \in itv -> well_ordered (add_min_element x s) itv.
Proof.
elim: s itv => /= [itv _ ->//|l IHl sx r _ h] itv /andP[]/andP[]/andP[].
rewrite bnd_simp => xsx sxi lwo rwo /[dup] xitv.
rewrite itv_boundlr => /andP[] ix xi.
rewrite well_ordered_bal rwo itv_boundlr sxi !andbT; apply/andP; split.
  by apply/(le_trans ix)/ltW.
by apply/IHl => //; rewrite itv_boundlr/= ix.
Qed.

Lemma elements_add_min_element x s :
  elements (add_min_element x s) = x :: elements s.
Proof.
elim: s => [//|l IHl y r _ h]/=.
by rewrite elements_bal IHl elements_node cat_cons.
Qed.

Lemma mem_add_min_element y x s : well_ordered s `]x, +oo[ -> mem (add_min_element x s) y = (y == x) || (mem s y).
Proof.
move=> swo; rewrite mem_elements; last exact/well_ordered_add_min_element.
rewrite mem_elements; last exact/(well_orderedWT swo).
by rewrite elements_add_min_element in_cons.
Qed.

Lemma card_add_min_element x s : card (add_min_element x s) = (card s).+1.
Proof. by rewrite !cardE elements_add_min_element. Qed.

Lemma well_formed_add_max_element x s : well_formed s -> well_formed (add_max_element x s).
Proof.
elim: s => [//|] l _ sx r IHr h /= /andP[]/andP[] _ {h} lwf rwf.
by apply/well_formed_bal => //; apply/IHr.
Qed.

Lemma balanced_height_add_max_element x s : well_formed s -> balanced s -> (balanced (add_max_element x s) && (height s <= height (add_max_element x s) <= (height s).+1)).
Proof.
elim: s => [//|] l IHl sx r IHr h /=
    /andP[]/andP[] /eqP -> {h} /[dup] lwf {}/IHl IHl /[dup] rwf {}/IHr IHr
    /andP[]/andP[] lrd /[dup] lb {}/IHl /andP[] xlb /andP[] lxl xll /[dup] rb {}/IHr /andP[] xrb /andP[] rxr xrr.
apply/andP; split.
  apply balanced_bal => //; first exact/well_formed_add_max_element.
  apply/(leq_trans (leq_diffnD (height r) _ _))/(@leq_add _ _ 2 1) => //.
  by rewrite geq_diffn !addn1 xrr (leqW rxr).
rewrite /bal; case /boolP: (diffn (height l) (height (add_max_element x r)) <= 2) => [_|].
  by rewrite /= !ltnS -maxnSS !geq_max !leq_max rxr leqnn xrr leqnSn !orbT.
move: rxr; rewrite leq_eqVlt => /orP; case=> [/eqP <-|].
  by rewrite lrd.
move: xrr; mk_conj=> /anti_leq /[dup] {}xrr ->.
move: lrd; rewrite 2!geq_diffn !addn2 [_ < height l]ltnNge !ltnS => /andP[] /leqW -> /=.
rewrite -ltnNge; mk_conj=> /anti_leq rlh.
move: xrr; rewrite {}rlh (maxn_idPr (leqW (leqnSn _))).
case: (add_max_element x r) (well_formed_add_max_element x rwf) xrb => [//|] xrl xrx xrr xrh /= /andP[]/andP[] /eqP -> {xrh} xrlwf xrrwf /andP[]/andP[] xd xrlb xrrb /eqP.
rewrite eqSS => /eqP; case: (ltnP (height xrr) (height xrl)); last first.
  by move=> + xrlE /=; rewrite xrlE  maxnSS !ltnS maxnAC (maxn_idPr (leqnSn _)) leq_maxl geq_max leqnSn => ->.
case: xrl xrlwf xrlb xd => [//|] xrll xrlx xrlr xrlh /= /andP[]/andP[] /eqP -> {xrlh} _ _ _ _ + /eqP.
rewrite maxnSS !ltnS eqSS -maxnA [maxn (height xrll) (maxn _ _)]maxnA => /maxn_idPl -> /eqP ->.
  by rewrite (maxn_idPr (leqnSn _)) leqnn leqnSn.
Qed.

Lemma well_ordered_add_max_element x s itv : well_ordered s (Interval itv.1 (BLeft x)) -> x \in itv -> well_ordered (add_max_element x s) itv.
Proof.
elim: s itv => /= [itv _ ->//|l _ sx r IHr h] itv /andP[]/andP[].
rewrite itv_boundlr/= bnd_simp => /andP[] isx sxx lwo rwo /[dup] xitv.
rewrite itv_boundlr => /andP[] ix xi.
rewrite well_ordered_bal lwo itv_boundlr isx/= andbT; apply/andP; split.
  by apply/(le_trans _ xi)/ltW.
by apply/IHr => //; rewrite itv_boundlr/= xi andbT; apply/ltW.
Qed.

Lemma elements_add_max_element x s :
  elements (add_max_element x s) = rcons (elements s) x.
Proof.
elim: s => [//|l _ y r IHr h]/=.
by rewrite elements_bal IHr elements_node rcons_cat.
Qed.

Lemma mem_add_max_element y x s : well_ordered s `]-oo, x[ -> mem (add_max_element x s) y = (y == x) || (mem s y).
Proof.
move=> swo; rewrite mem_elements; last exact/well_ordered_add_max_element.
rewrite mem_elements; last exact/(well_orderedWT swo).
by rewrite elements_add_max_element mem_rcons.
Qed.

Lemma card_add_max_element x s : card (add_max_element x s) = (card s).+1.
Proof. by rewrite !cardE elements_add_max_element size_rcons. Qed.

Lemma well_formed_join l x r : well_formed l -> well_formed r -> well_formed (join l x r).
Proof.
elim: l r => [|ll IHll lx lr IHlr lh] r lwf rwf; first exact/well_formed_add_min_element.
elim: r rwf => [|rl IHrl rx rr IHrr rh] rwf; first exact/well_formed_add_max_element.
move: rwf lwf => /= /andP[]/andP[] /eqP rhE rlwf rrwf /= /andP[]/andP[] /eqP lhE llwf lrwf; subst lh rh.
case: (leq_diffn2P _ _) => _; last first.
- by rewrite /= !eqxx llwf lrwf rlwf.
- by apply/well_formed_bal => //; apply IHrl.
apply/well_formed_bal => //; apply IHlr => //.
by rewrite /= eqxx rlwf.
Qed.

Lemma balanced_height_join l x r : well_formed l -> well_formed r -> balanced l -> balanced r -> balanced (join l x r) && (height (join l x r) <= height (create l x r) <= (height (join l x r)).+1).
Proof.
elim: l r => [|ll IHll lx lr IHlr lh] r lwf rwf lb rb.
  by rewrite /= max0n ltnS [(_ <= _) && _]andbC; apply/balanced_height_add_min_element.
elim: r rwf rb => [|rl IHrl rx rr IHrr rh] rwf rb /=.
  by rewrite /= maxn0 ltnS [(_ <= _) && _]andbC; apply/(balanced_height_add_max_element x lwf).
case: (leq_diffn2P lh _); last first.
- by move: lb rb => /= -> -> ->; rewrite leqnSn leqnn.
- move: lwf lb => /= /andP[]/andP[] /eqP lhE llwf lrwf /andP[]/andP[] lrd llb lrb rhlh.
  move: (IHlr _ lrwf rwf lrb rb) => {IHlr} /andP[] bj /andP[] /=.
  have /maxn_idPl ->: rh <= (height lr).
    rewrite -3!ltnS; apply/(leq_trans rhlh); rewrite lhE ltnS geq_max (leqW (leqnSn _)).
    by move: lrd; rewrite geq_diffn addn2 => /andP[] ->.
  rewrite (maxn_idPl (ltnW (ltnW (ltnW rhlh)))) !ltnS => jc cj.
  apply/andP; split.
    apply/balanced_bal => //; first exact/well_formed_join.
    apply/(leq_trans (leq_diffnD (height lr) _ _))/(@leq_add _ _ 2 1) => //.
    by rewrite geq_diffn !addn1 jc (leqW cj).
  move: (height_bal lx llwf (well_formed_join x lrwf rwf)).
  rewrite /= ltnS lhE => /andP[] bc cb; apply/andP; split.
    by rewrite (leq_trans bc)// ltnS geq_max (leqW (leq_maxl _ _))/= -maxnSS leq_max jc orbT.
  move: cj; rewrite leq_eqVlt => /orP; case=> [/eqP lrhE|].
    by move: lrd; rewrite lrhE /bal => ->; rewrite leqnn.
  move: jc; mk_conj => /anti_leq lrhE.
  case /boolP: (diffn (height ll) (height (join lr x (node rl rx rr rh))) <= 2).
    by rewrite /bal => -> /=; rewrite ltnS geq_max leq_maxl leq_max lrhE leqnSn orbT.
  move: lrd; rewrite lrhE !geq_diffn !addn2 ltnS => /andP[] /leqW -> _.
  rewrite /= -ltnNge => /ltnW/ltnW lllr.
  by refine (leq_trans _ cb); rewrite lrhE (maxn_idPr lllr) (maxn_idPr (leqW lllr)) leqnn.
- move: rwf rb => /= /andP[]/andP[] /eqP rhE rlwf rrwf /andP[]/andP[] rld rlb rrb lhrh.
  move: (IHrl rlwf rlb) => {IHlr} /andP[] bj /andP[] /=.
  have /maxn_idPr ->: lh <= (height rl).
    rewrite -3!ltnS; apply/(leq_trans lhrh); rewrite rhE ltnS geq_max (leqW (leqnSn _)).
    by move: rld; rewrite geq_diffn !addn2 => /andP[].
  rewrite (maxn_idPr (ltnW (ltnW (ltnW lhrh)))) !ltnS => jc cj.
  apply/andP; split.
    apply/balanced_bal => //; first exact/(well_formed_join x lwf).
    apply/(leq_trans (leq_diffnD (height rl) _ _))/(@leq_add _ _ 1 2) => //.
    by rewrite geq_diffn !addn1 jc (leqW cj).
  move: (height_bal rx (well_formed_join x lwf rlwf) rrwf).
  rewrite /= ltnS rhE => /andP[] bc cb; apply/andP; split.
    by rewrite (leq_trans bc)// ltnS geq_max (leqW (leq_maxr _ _))/= -maxnSS leq_max jc.
  move: cj; rewrite leq_eqVlt => /orP; case=> [/eqP rlhE|].
    by move: rld; rewrite rlhE /bal => ->; rewrite leqnn.
  move: jc; mk_conj => /anti_leq rlhE.
  case /boolP: (diffn (height ((fix F r : t elt :=
         match r with
         | @leaf _ _ => bal ll lx (add_max_element x lr)
         | node rl0 rx0 rr0 rh0 =>
             if diffn lh rh0 <= 2
             then create (node ll lx lr lh) x r
             else
              if rh0.+2 < lh
              then bal ll lx (join lr x r)
              else bal (F rl0) rx0 rr0
         end) rl)) (height rr) <= 2).
    by rewrite {4}/bal => -> /=; rewrite ltnS geq_max leq_maxr leq_max rlhE leqnSn.
  move: rld; rewrite rlhE !geq_diffn !addn2 ltnS => /andP[] _ /leqW ->.
  rewrite andbT -ltnNge => /ltnW/ltnW rlrr.
  by refine (leq_trans _ cb); rewrite rlhE (maxn_idPl rlrr) (maxn_idPl (leqW rlrr)) leqnn.
Qed.

Lemma balanced_join l x r : well_formed l -> well_formed r -> balanced l -> balanced r -> balanced (join l x r).
Proof. by move=> lwf rwf lb /(balanced_height_join x lwf rwf lb) /andP[]. Qed.

Lemma well_ordered_join l x r itv : well_ordered l (Interval itv.1 (BLeft x)) -> well_ordered r (Interval (BRight x) itv.2) -> x \in itv -> well_ordered (join l x r) itv. 
Proof.
case: itv => lb ub; rewrite itv_boundlr/=.
elim: l r lb ub => /= [|ll IHll lx lr IHlr lh] r lb ub lwo rwo xitv; first exact/well_ordered_add_min_element.
move: (xitv) (lwo); rewrite itv_boundlr/= => /andP[] lbx xub /andP[]/andP[]/andP[] lblx lxx llwo lrwo.
elim: r ub xitv xub rwo => [|rl IHrl rx rr IHrr rh] ub xitv xub rwo.
  rewrite well_ordered_bal itv_boundlr/= lblx llwo/= andbT; apply/andP; split.
    exact/(le_trans lxx)/ltW.
  apply/well_ordered_add_max_element => //.
  by rewrite itv_boundlr/= lxx.
move=> /=; case (leq_diffn2P _ _) => [rhlh|lhrh|_]; last exact/well_ordered_create.
  rewrite well_ordered_bal llwo IHlr// ?lxx// itv_boundlr lblx/= !andbT.
  exact/(le_trans lxx)/ltW.
rewrite well_ordered_bal. 
move: rwo => /= /andP[]/andP[]/andP[] xrx rxub rlwo ->.
rewrite itv_boundlr rxub !andbT; apply/andP; split.
  exact/(le_trans lbx)/ltW.
by apply/IHrl => //; rewrite lbx; apply/ltW.
Qed.

Lemma elements_join l x r : elements (join l x r) = elements l ++ x :: elements r.
Proof.
elim: l r => /= [|ll IHll lx lr IHlr lh] r; first exact/elements_add_min_element.
rewrite elements_node; elim: r => [|rl IHrl rx rr IHrr rh].
  by rewrite elements_bal elements_add_max_element cats1 rcons_cat.
case: (_ <= 2); first by rewrite !elements_node.
case: (_ < _); first by rewrite elements_bal IHlr -catA cat_cons.
by rewrite elements_bal IHrl elements_node -catA cat_cons.
Qed.

Lemma mem_join y l x r : well_ordered l `]-oo, x[ -> well_ordered r `]x, +oo[ -> mem (join l x r) y = (y == x) || (mem l y) || (mem r y).
Proof.
move=> lwo rwo.
rewrite mem_elements; last exact/well_ordered_join.
rewrite mem_elements; last exact/(well_orderedWT lwo).
rewrite mem_elements; last exact/(well_orderedWT rwo).
by rewrite elements_join mem_cat in_cons orbCA orbA.
Qed.

Lemma card_join l x r : card (join l x r) = (card l + card r).+1.
Proof. by rewrite !cardE elements_join size_cat/= addnS. Qed.

Lemma well_formed_remove_min s : well_formed s -> well_formed (remove_min s).
Proof.
elim: s => [//|l IHl x r _ h] /= /andP[]/andP[] _ {}/IHl + rwo.
case: l => [//|ll lx lr lh] lwo.
exact/well_formed_bal.
Qed.

Lemma balanced_height_remove_min s : well_formed s -> balanced s -> balanced (remove_min s) && (height (remove_min s) <= height s <= (height (remove_min s)).+1).
Proof.
elim: s => [//|l IHl x r _ h] /= /andP[]/andP[]/= /eqP -> {h} /[dup] lwf {}/IHl IHl rwf /andP[]/andP[] + {}/IHl /andP[] + /andP[] + + rb.
case: l lwf => [|ll lx lr lh] lwf lrd lb ml lm; first by rewrite rb/= max0n leqnSn leqnn.
apply/andP; split.
  apply/balanced_bal => //; first exact/well_formed_remove_min.
  apply/(leq_trans (leq_diffnD lh _ _))/(@leq_add _ _ 1 2) => //.
  rewrite geq_diffn !addn1; apply/andP; split=> //.
  exact/leqW.
move: (remove_min _) (height_bal x (well_formed_remove_min lwf) rwf) lb ml lm lrd => m /= /andP[].
rewrite !ltnS => mr rm mb.
rewrite leq_eqVlt => /orP; case=> [/eqP <- _ _|]; first by rewrite mr rm.
mk_conj => /anti_leq <- mrd; apply/andP; split.
  by apply/(leq_trans mr); rewrite ltnS geq_max leq_maxr andbT ltnW// leq_maxl.
case /boolP: (diffn (height m) (height r) <= 2) => [{}mrd|].
  by rewrite /bal mrd/= -maxnSS geq_max leq_maxl ltnW// leq_maxr.
move: mrd; rewrite !geq_diffn !addn2 !ltnS => /andP[] /leqW -> _ /=.
rewrite -ltnNge => /ltnW/ltnW {}mr.
by move: rm; rewrite (maxn_idPr mr) (maxn_idPr (ltnW mr)).
Qed.

Lemma balanced_remove_min s : well_formed s -> balanced s -> balanced (remove_min s).
Proof. by move=> swf /(balanced_height_remove_min swf) /andP[]. Qed.

Lemma height_remove_min s : well_formed s -> balanced s -> (height (remove_min s) <= height s <= (height (remove_min s)).+1).
Proof. by move=> swf /(balanced_height_remove_min swf) /andP[]. Qed.

Lemma min0P s : (min s == None) = (s == leaf elt).
Proof. by elim: s => [//|+ + sx r _ h]; case. Qed.

Lemma minP x s : well_ordered s `]-oo, +oo[ -> mem s x -> map_or (fun m => m <= x)%O false (min s).
Proof.
elim: s x => [//|l IHl sx r _ h] x swo.
rewrite mem_node// orbC orbA; move: swo => /= /andP[] lwo /mem_well_ordered rsx.
  case: l IHl lwo => [/=|ll lx lr lh] mP lwo.
  rewrite orbF => /orP; case=> [/rsx|/eqP ->]; last exact/lexx.
  by rewrite in_itv/= => /andP[] /ltW.
move=> /orP; case => [xm|/(mP _ (well_orderedWT lwo))//].
have lxP: mem (node ll lx lr lh) lx by rewrite /= eqxx.
move: mP => /(_ lx (well_orderedWT lwo) lxP).
case: (min _) => [m|//] /= mlx; apply/(le_trans mlx).
move: (mem_well_ordered lwo lxP); rewrite in_itv/= => /ltW lsx.
apply/(le_trans lsx).
by move: xm => /orP; case=> [/rsx|/eqP -> //]; rewrite in_itv/= => /andP[] /ltW.
Qed.

Lemma mem_min s : well_ordered s `]-oo, +oo[ -> map_or (mem s) (s == leaf elt) (min s).
Proof.
elim: s => [//|] l + x r _ h.
rewrite /min -/(min l); case: l => [|ll lx lr lh].
  by move=> _ _ /=; rewrite eqxx.
have: (node ll lx lr lh != leaf elt) by [].
move: (node ll lx lr lh) => l; case: (min l) => [m _ IHl swo|/negP l0]/=; last first.
  by move=> /[swap] /andP[] /well_orderedWT lwo _ /(_ lwo).
rewrite -/(mem (node l x r h) m) mem_node//.
by move: swo IHl => /= /andP[] /well_orderedWT lwo _ -> //; rewrite orbT.
Qed.

Lemma max0P s : (max s == None) = (s == leaf elt).
Proof. by elim: s => [//|l _ sx + +  h]; case. Qed.

Lemma maxP x s : well_ordered s `]-oo, +oo[ -> mem s x -> map_or (fun m => x <= m)%O false (max s).
Proof.
elim: s x => [//|l _ sx r IHr h] x swo.
rewrite mem_node//; move: swo => /= /andP[] /mem_well_ordered/= lsx rwo.
case: r IHr rwo => [/=|rl rx rr rh] mP rwo.
  rewrite orbF => /orP; case=> [/eqP ->|/lsx]; first exact/lexx.
  by rewrite in_itv/= => /ltW.
move=> /orP; case => [xm|/(mP _ (well_orderedWT rwo))//].
have rxP: mem (node rl rx rr rh) rx by rewrite /= eqxx.
move: mP => /(_ rx (well_orderedWT rwo) rxP).
case: (max _) => [m|//]/= rxm; apply/(le_trans _ rxm).
move: (mem_well_ordered rwo rxP); rewrite in_itv/= andbT => /ltW srx.
apply/(le_trans _ srx).
move: xm => /orP; case=> [/eqP ->//|/lsx].
by rewrite in_itv/= => /ltW.
Qed. 

Lemma mem_max s : well_ordered s `]-oo, +oo[ -> map_or (mem s) true (max s).
Proof.
elim: s => [//|] l _ x r + h.
rewrite /max -/(max r); case: r => [|rl rx rr rh].
  by move=> _ _ /=; rewrite eqxx.
move: (node rl rx rr rh) => r; case: (max r) => [|//] m IHr swo.
rewrite /= -/(mem (node l x r h) m) mem_node//.
by move: swo IHr => /= /andP[] _ /well_orderedWT rwo -> //; rewrite !orbT.
Qed.

Lemma well_ordered_remove_min s ub : well_ordered s (Interval -oo ub) -> well_ordered (remove_min s) (Interval (map_or BRight -oo (min s)) ub).
Proof.
elim: s ub => [//|l IHl x r _ h]/= ub /andP[]/andP[].
rewrite itv_boundlr/= => xub /[dup] lwo' {}/IHl + rwo.
case: l lwo' => [//|ll lx lr lh] lwo' lwo.
rewrite well_ordered_bal lwo rwo.
move: (lwo') => /[dup] /well_orderedWT lwoN /mem_well_ordered-/(_ lx); mp.
  by rewrite /= eqxx.
rewrite in_itv => lxx.
move: (minP (x:=lx) lwoN); mp; first by rewrite /= eqxx.
case: (min _) => [m|//] /= mlx.
rewrite itv_boundlr/= xub !andbT.
exact/(le_lt_trans mlx lxx).
Qed.

Lemma elements_min s : elements s = (map_or cons id (min s) (elements (remove_min s))).
Proof.
elim: s => [//|l IHl x r IHr h] /=.
case: l IHl => // ll y lr lh IHl.
by rewrite elements_bal elements_node IHl; case: (min _).
Qed.

Lemma elements_remove_min s : elements (remove_min s) = behead (elements s).
Proof.
by rewrite [in RHS]elements_min; case: (min s) (min0P s) => [x _|/esym/eqP ->].
Qed.

Lemma mem_remove_min x s : well_ordered s `]-oo, +oo[ -> mem (remove_min s) x = (Some x != min s) && (mem s x).
Proof.
move=> swo; rewrite !mem_elements//; last first.
  exact/(well_orderedWTl (well_ordered_remove_min swo)).
move: (sorted_elements swo); rewrite elements_min sorted_pairwise; last first.
  exact/lt_trans.
case: (min s) (min0P s) => [y _|/esym/eqP -> //] /= /andP[] /allP ys _.
rewrite in_cons (inj_eq Some_inj).
have [-> /=|//] := eqVneq x y.
by apply/negP => /ys; rewrite ltxx.
Qed.

Lemma mem_remove_min' x s : well_ordered s `]-oo, +oo[ -> mem s x = (Some x == min s) || (mem (remove_min s) x).
Proof.
move=> swo; rewrite !mem_elements//; last first.
  exact/(well_orderedWTl (well_ordered_remove_min swo)).
by rewrite elements_min; case: (min s).
Qed.

Lemma card_remove_min s : card (remove_min s) = (card s).-1.
Proof.
elim: s => [//|] l IHl x r _ h/=.
case: l IHl => [//|] ll lx lr lh IHl.
by rewrite card_bal IHl/= addSn.
Qed.

Lemma well_formed_merge l r : well_formed l -> well_formed r -> well_formed (merge l r).
Proof.
move=> lwf rwf; rewrite /merge; case: (min r) => [|//] m.
by apply/well_formed_bal => //; apply/well_formed_remove_min.
Qed.

Lemma balanced_merge l r : well_formed l -> well_formed r -> balanced l -> balanced r -> diffn (height l) (height r) <= 2 -> balanced (merge l r).
Proof.
move=> lwf rwf lb rb lrd; rewrite /merge; case: (min r) => [|//] m.
apply/balanced_bal => //.
- exact/well_formed_remove_min.
- exact/balanced_remove_min.
move: (height_remove_min rwf rb) => /andP[].
rewrite leq_eqVlt => /orP; case=> [/eqP -> _|]; first exact/(leq_trans lrd).
mk_conj=> /anti_leq rE.
apply/(leq_trans (leq_diffnD (height r) _ _))/(leq_add lrd).
by rewrite -rE diffn_subnE (maxn_idPl (leqnSn _)) (minn_idPr (leqnSn _)) subSnn.
Qed.

Lemma height_merge l r : well_formed l -> well_formed r -> balanced r -> diffn (height l) (height r) <= 2 -> well_ordered r `]-oo, +oo[ -> maxn (height l) (height r) <= (height (merge l r)) <= (maxn (height l) (height r)).+1.
Proof.
move=> lwf rwf rb lrd rwo; rewrite /merge; case: (min r) (mem_min rwo) => [m _|/= /eqP -> /=]; last by rewrite maxn0 leqnn leqnSn.
move: (height_remove_min rwf rb) (height_bal m lwf (well_formed_remove_min rwf)) => /andP[] mr rm /=.
case/boolP: (diffn (height l) (height (remove_min r)) <= 2) => [lrmd _|].
  by rewrite /bal lrmd/= ltnS -maxnSS !geq_max leq_maxl !leq_max leqnSn rm mr !orbT.
move: lrd; rewrite !geq_diffn !addn2 => /andP[] lr rl.
rewrite (leq_trans mr rl) andbT -ltnNge => /ltnW/ltnW {}rl.
by rewrite (maxn_idPl (leq_trans rm rl)) (maxn_idPl (ltnW rl)) ltnS => /andP[] -> ->.
Qed.

Lemma well_ordered_merge l r itv : well_ordered l (Interval itv.1 (map_or BLeft itv.2 (min r))) -> well_ordered r itv -> well_ordered (merge l r) itv.
Proof.
move=> + /[dup] rwo /well_orderedWTl/well_ordered_remove_min.
move: (mem_min (well_orderedWT rwo)).
rewrite /merge; case: (min r) => [m|_ + _]/=; last first.
  by case: itv {rwo}.
move=> /(mem_well_ordered rwo) mi lwo {}rwo.
by rewrite well_ordered_bal mi lwo.
Qed.

Lemma elements_merge l r : elements (merge l r) = elements l ++ elements r.
Proof.
rewrite /merge; case: (min r) (min0P r) (elements_min r) => [x _ ->|/esym/eqP -> _] /=.
  exact/elements_bal.
by rewrite cats0.
Qed.

Lemma mem_merge x l r : well_ordered l (Interval -oo (map_or BLeft +oo (min r))) -> well_ordered r `]-oo, +oo[ -> mem (merge l r) x = (mem l x || mem r x).
Proof.
move=> lwo rwo; rewrite !mem_elements//.
- by rewrite elements_merge mem_cat.
- exact/(well_orderedWT lwo).
- exact/well_ordered_merge.
Qed.

Lemma card_merge l r : card (merge l r) = card l + card r.
Proof.
rewrite /merge; case: (min r) (min0P r) => [x xr|/esym/eqP ->]; last by rewrite addn0.
rewrite card_bal card_remove_min -addnS; congr (_ + _).
by case: r xr.
Qed.

Lemma well_formed_concat l r : well_formed l -> well_formed r -> well_formed (concat l r).
Proof.
move=> lwf rwf; rewrite /concat; case: (min r) => [|//] m.
by apply/well_formed_join => //; apply/well_formed_remove_min.
Qed.

Lemma balanced_concat l r : well_formed l -> well_formed r -> balanced l -> balanced r -> balanced (concat l r).
Proof.
move=> lwf rwf lb rb; rewrite /concat; case: (min r) => [|//] m.
apply/balanced_join => //.
- exact/well_formed_remove_min.
- exact/balanced_remove_min.
Qed.

Lemma well_ordered_concat l r itv : well_ordered l (Interval itv.1 (map_or BLeft itv.2 (min r))) -> well_ordered r itv -> well_ordered (concat l r) itv.
Proof.
move=> + /[dup] rwo /well_orderedWTl/well_ordered_remove_min.
move: (mem_min (well_orderedWT rwo)).
rewrite /concat; case: (min r) => [m|/eqP -> + _]/=; last first.
  by case: itv {rwo}.
move=> /(mem_well_ordered rwo) mi lwo {}rwo.
by rewrite well_ordered_join.
Qed.

Lemma elements_concat l r : elements (concat l r) = elements l ++ elements r.
Proof.
rewrite /concat; case: (min r) (min0P r) (elements_min r) => [x _ ->|/esym/eqP -> _].
  exact/elements_join.
by rewrite cats0.
Qed.

Lemma mem_concat x l r : well_ordered l (Interval -oo (map_or BLeft +oo (min r))) -> well_ordered r `]-oo, +oo[ -> mem (concat l r) x = (mem l x || mem r x).
Proof.
move=> lwo rwo; rewrite !mem_elements//.
- by rewrite elements_concat mem_cat.
- exact/(well_orderedWT lwo).
- exact/well_ordered_concat.
Qed.

Lemma card_concat l r : well_ordered l (Interval -oo (map_or BLeft +oo (min r))) -> well_ordered r `]-oo, +oo[ -> card (concat l r) = card l + card r.
Proof. by move=> lwo rwo; rewrite !cardE elements_concat size_cat. Qed.

Lemma well_formed_splitl x s : well_formed s -> well_formed (split x s).1.1.
Proof.
elim: s => [//|] l IHl sx r IHr h /= /andP[]/andP[] _ {h} lwf rwf.
case /comparable_ltgtP: (comparableT x sx) => // xsx.
  by case: (split x l) (IHl lwf) => [[]].
case: (split x r) (IHr rwf) => [[/=]] sr _ _ srwf.
exact/well_formed_join.
Qed.

Lemma well_formed_splitr x s : well_formed s -> well_formed (split x s).2.
Proof.
elim: s => [//|] l IHl sx r IHr h /= /andP[]/andP[] _ {h} lwf rwf.
case /comparable_ltgtP: (comparableT x sx) => // xsx; last first.
  by case: (split x r) (IHr rwf) => [[]].
case: (split x l) (IHl lwf) => [[/=]] _ _ sl slwf.
exact/well_formed_join.
Qed.

Lemma balanced_splitl x s : well_formed s -> balanced s -> balanced (split x s).1.1.
Proof.
elim: s => [//|] l IHl sx r IHr h /= /andP[]/andP[] _ {h} lwf rwf /andP[]/andP[] lrd lb rb.
case /comparable_ltgtP: (comparableT x sx) => // xsx.
  by case: (split x l) (IHl lwf lb) => [[]].
case: (split x r) (IHr rwf rb) (well_formed_splitl x rwf) => [[/=]] sr _ _ srb srwf.
by apply/balanced_join.
Qed.

Lemma balanced_splitr x s : well_formed s -> balanced s -> balanced (split x s).2.
Proof.
elim: s => [//|] l IHl sx r IHr h /= /andP[]/andP[] _ {h} lwf rwf /andP[]/andP[] lrd lb rb.
case /comparable_ltgtP: (comparableT x sx) => // xsx; last first.
  by case: (split x r) (IHr rwf rb) => [[]].
case: (split x l) (IHl lwf lb) (well_formed_splitr x lwf) => [[/=]] _ _ sl slb slwf.
by apply/balanced_join.
Qed.

Lemma height_split x s : well_formed s -> balanced s -> (height (split x s).1.1 <= height s) && (height (split x s).2 <= height s).
Proof.
elim: s => [//|] l IHl sx r IHr h /= /andP[]/andP[] /eqP -> {h} lwf rwf /andP[]/andP[] _ lb rb.
case /comparable_ltgtP: (comparableT x sx) => xsx; last first.
- by rewrite /= -!maxnSS !leq_max !leqnSn orbT.
- case: (split x r) IHr
    (well_formed_splitl x rwf) (well_formed_splitr x rwf)
    (balanced_splitl x rwf rb) (balanced_splitr x rwf rb) => [[sl /= _]] sr /(_ rwf rb) /andP[] slr srr slwf srwf slb srb.
  move: (balanced_height_join sx lwf slwf lb slb) => /andP[] _ /= /andP[] jm mj.
  apply/andP; split.
    by apply/(leq_trans jm); rewrite ltnS geq_max leq_maxl leq_max slr orbT.
  by rewrite -maxnSS leq_max (leqW srr) orbT.
- case: (split x l) IHl
    (well_formed_splitl x lwf) (well_formed_splitr x lwf)
    (balanced_splitl x lwf lb) (balanced_splitr x lwf lb) => [[sl /= _]] sr /(_ lwf lb) /andP[] sll srl slwf srwf slb srb.
  move: (balanced_height_join sx srwf rwf srb rb) => /andP[] _ /= /andP[] jm mj.
  rewrite -{1}maxnSS leq_max (leqW sll)/=.
  by apply/(leq_trans jm); rewrite ltnS geq_max leq_maxr leq_max srl.
Qed.

Lemma well_ordered_splitl x s lb : well_ordered s (Interval lb +oo) -> well_ordered (split x s).1.1 (Interval lb (BLeft x)).
Proof.
elim: s lb => [//|] l IHl sx r IHr h lb /= /andP[]/andP[]/andP[] lbsx _ lwo rwo.
case /comparable_ltgtP: (comparableT x sx) => [| |-> //] xsx.
  by case: (split x l) (IHl _ (well_orderedWTr lwo)) => [[]].
case: (split x r) (IHr _ rwo) => [[/=]] sr _ _ srwo.
by apply/well_ordered_join => //=; rewrite itv_boundlr/= lbsx.
Qed.

Lemma well_ordered_splitr x s ub : well_ordered s (Interval -oo ub) -> well_ordered (split x s).2 (Interval (BRight x) ub).
Proof.
elim: s ub => [//|] l IHl sx r IHr h ub /= /andP[]/andP[] sxub lwo rwo.
case /comparable_ltgtP: (comparableT x sx) => [| |-> //] xsx; last first.
  by case: (split x r) (IHr _ (well_orderedWTl rwo)) => [[]].
case: (split x l) (IHl _ lwo) => [[/=]] _ _ sl slwo.
by apply/well_ordered_join => //=; rewrite itv_boundlr/= bnd_simp xsx.
Qed.

Lemma elements_split x s : elements s = elements (split x s).1.1 ++ (if (split x s).1.2 then cons x else id) (elements (split x s).2).
Proof.
elim: s => [//|l IHl sx r IHr h]/=; rewrite elements_node.
case /comparable_ltgtP: (comparableT x sx) => [| |-> //] xsx; last first.
  rewrite IHr; case: (split x r) => -[] rl rx rr/=.
  by rewrite elements_join -catA cat_cons.
rewrite IHl; case: (split x l) => -[] ll lx lr/=.
by rewrite elements_join; case: lx; rewrite -catA// cat_cons.
Qed.

Lemma mem_split x y s : well_ordered s `]-oo, +oo[ -> mem s x = ((split y s).1.2 && (x == y)) || mem (split y s).1.1 x || mem (split y s).2 x.
Proof.
move=> swo; rewrite !mem_elements//; first last.
- exact/(well_orderedWT (well_ordered_splitl y swo)).
- exact/(well_orderedWT (well_ordered_splitr y swo)).
rewrite (elements_split y) mem_cat if_arg 2!fun_if in_cons.
by rewrite -[RHS]orbAC orbC; congr orb; case: (split y s).1.2.
Qed.

Lemma card_split x s : card s = (split x s).1.2 + card (split x s).1.1 + card (split x s).2.
Proof.
rewrite !cardE (elements_split x) size_cat if_arg fun_if/=.
by rewrite -[RHS]addnAC addnC; congr addn; case: (split x s).1.2.
Qed.

Lemma elements_add x s : elements (add x s) = elements (split x s).1.1 ++ x :: elements (split x s).2.
Proof.
elim: s => [//|l IHl sx r IHr h]/=.
case /comparable_ltgtP: (comparableT x sx) => _; last by rewrite elements_node.
  rewrite elements_bal IHl; case: (split x l) => -[] ll lb lr/=.
  by rewrite elements_join -catA cat_cons.
rewrite elements_bal IHr; case: (split x r) => -[] rl rb rr/=.
by rewrite elements_join -catA cat_cons.
Qed.

Lemma well_formed_remove x s : well_formed s -> well_formed (remove x s).
Proof.
elim: s => [//|] l IHl sx r IHr h /= /andP[]/andP[] _ {h} lwf rwf.
case /comparable_ltgtP: (comparableT x sx) => _.
- by apply/well_formed_bal => //; apply/IHl.
- by apply/well_formed_bal => //; apply/IHr.
- exact/well_formed_merge.
Qed.

Lemma balanced_height_remove x s : well_formed s -> balanced s -> well_ordered s `]-oo, +oo[ -> balanced (remove x s) && (height s <= (height (remove x s)).+1 <= (height s).+1).
Proof.
elim: s => [//|] l IHl sx r IHr h/= /andP[]/andP[] /eqP -> {h} lwf rwf /andP[]/andP[] lrd lb rb /andP[] /well_orderedWT lwo /well_orderedWT rwo.
move: IHl IHr => /(_ lwf lb lwo) /andP[] lb' /andP[] lxl xll /(_ rwf rb rwo) /andP[] rb' /andP[] rxr xrr.
case /comparable_ltgtP: (comparableT x sx) => _; last first.
- apply/andP; split; first exact/balanced_merge.
  by rewrite !ltnS; apply: height_merge.
- apply/andP; split.
    apply/balanced_bal => //; first exact/well_formed_remove.
    apply/(leq_trans (leq_diffnD (height r) _ _))/(@leq_add _ _ 2 1) => //.
    by rewrite geq_diffn !addn1 rxr (ltnW xrr).
  case/boolP: (diffn (height l) (height (remove x r)) <= 2) => [xlrd|].
    rewrite /bal xlrd/= !ltnS -maxnSS !geq_max leq_maxl !leq_max rxr leqnSn orbT/=.
    by apply/orP; right.
  move: lrd; rewrite !geq_diffn !addn2 => /andP[] lr rl.
  rewrite (leq_trans (m:=(height (remove x r))) xrr rl) andbT -ltnNge => /ltnW/ltnW xrl.
  rewrite (maxn_idPl (leq_trans rxr xrl)).
  move: (height_bal sx lwf (well_formed_remove x rwf)) => /andP[]/=.
  by rewrite (maxn_idPl (ltnW xrl)) => bm ->; rewrite ltnS.
- apply/andP; split.
    apply/balanced_bal => //; first exact/well_formed_remove.
    apply/(leq_trans (leq_diffnD (height l) _ _))/(@leq_add _ _ 1 2) => //.
    by rewrite geq_diffn !addn1 lxl (ltnW xll).
  case/boolP: (diffn (height (remove x l)) (height r) <= 2) => [xlrd|].
    rewrite /bal xlrd/= !ltnS -maxnSS !geq_max leq_maxr !leq_max lxl leqnSn orbT/= andbT.
    by apply/orP; left.
  move: lrd; rewrite !geq_diffn !addn2 => /andP[] lr rl.
  rewrite (leq_trans (m:=(height (remove x l))) xll lr)/= -ltnNge => /ltnW/ltnW xlr.
  rewrite (maxn_idPr (leq_trans lxl xlr)).
  move: (height_bal sx (well_formed_remove x lwf) rwf) => /andP[]/=.
  by rewrite (maxn_idPr (ltnW xlr)) => bm ->; rewrite ltnS.
Qed.

Lemma balanced_remove x s : well_formed s -> balanced s -> well_ordered s `]-oo, +oo[ -> balanced (remove x s).
Proof.
by move=> swf sb swo; move: (balanced_height_remove x swf sb swo) => /andP[].
Qed.

Lemma well_ordered_remove x s itv : well_ordered s itv -> well_ordered (remove x s) itv.
Proof.
elim: s itv => [//|] l IHl sx r IHr h/= itv /andP[]/andP[] sxi lwo rwo.
case /comparable_ltgtP: (comparableT x sx) => _.
- rewrite well_ordered_bal sxi rwo/= andbT.
  by apply/IHl.
- rewrite well_ordered_bal sxi lwo/=.
  by apply/IHr.
move: sxi; rewrite itv_boundlr => /andP[] isx sxi.
apply/well_ordered_merge; last first.
  apply/(well_orderedW _ rwo); rewrite subitvE/= lexx andbT.
  by apply/(le_trans isx); rewrite bnd_simp.
case: (min r) (mem_min (well_orderedWT rwo)) => /= [m|_]; last first.
  apply/(well_orderedW _ lwo); rewrite subitvE lexx/=.
  by apply/(le_trans _ sxi); rewrite bnd_simp.
move=> /(mem_well_ordered rwo); rewrite itv_boundlr/= => /andP[sxm] _.
by apply/(well_orderedW _ lwo); rewrite subitvE lexx/=; apply/ltW.
Qed.

Lemma elements_remove x s : elements (remove x s) = elements (split x s).1.1 ++ elements (split x s).2.
Proof.
elim: s => [//|] l IHl sx r IHr h/=.
case /comparable_ltgtP: (comparableT x sx) => _.
- rewrite elements_bal IHl; case: (split x l) => -[] ll lb lr/=.
  by rewrite elements_join catA.
- rewrite elements_bal IHr; case: (split x r) => -[] rl rb rr/=.
  by rewrite elements_join -catA cat_cons.
- by rewrite elements_merge.
Qed.

Lemma mem_remove x y s : well_ordered s `]-oo, +oo[ -> mem (remove y s) x = (x != y) && mem s x.
Proof.
move=> swo; rewrite !mem_elements//; last exact/well_ordered_remove.
rewrite elements_remove [in RHS](elements_split y) !mem_cat.
case/boolP: (_ \in _) => xl/=.
  rewrite andbT; apply/esym/eqP => xy.
  move: swo xl => /(well_ordered_splitl y) lwo.
  rewrite -mem_elements; last exact/(well_orderedWT lwo).
  by move=> /(mem_well_ordered lwo); rewrite xy in_itv/= ltxx.
rewrite if_arg 2!fun_if in_cons.
case/boolP: (_ \in _) => xr/=; last first.
  by rewrite orbF -Bool.andb_lazy_alt andbCA andNb andbF.
rewrite orbT if_same andbT; apply/esym/eqP => xy.
move: swo xr => /(well_ordered_splitr y) rwo.
rewrite -mem_elements; last exact/(well_orderedWT rwo).
by move=> /(mem_well_ordered rwo); rewrite xy in_itv/= ltxx.
Qed.

Lemma card_remove x s : well_ordered s `]-oo, +oo[ -> card (remove x s) = card s - (mem s x).
Proof.
elim: s => [//|] l IHl sx r IHr h/= /andP[] /well_orderedWT lwo /well_orderedWT rwo.
case /comparable_ltgtP: (comparableT x sx) => [xsx|sxx|->]/=.
- rewrite card_bal IHl// -!addnS subDnCA; first by rewrite addnC.
  by case: l {IHl lwo} => [//|] ll lx lr lh; case: (mem _ _).
- rewrite card_bal IHr// -!addSn [in RHS]addnC subDnCA//.
  by case: r {IHr rwo} => [//|] rl rx rr rh; case: (mem _ _).
- by rewrite card_merge// subSS subn0.
Qed.

Lemma well_formed_union_subdef n s t : well_formed s -> well_formed t -> well_formed (union_subdef n s t).
Proof.
rewrite /union_subdef; elim: n s t => [//|] n IHn s t.
case: s => [//|] sl sx sr sh swf.
case: t => [//|] tl tx tr th twf.
case: (th <= sh).
  case: (th == 1); first exact/well_formed_add.
  case: (split _ _) (well_formed_splitl sx twf) (well_formed_splitr sx twf) => [[stl /= _]] str stlwf strwf.
  move: swf => /= /andP[]/andP[] _ slwf srwf.
  by apply/well_formed_join; apply/IHn.
case: (sh == 1); first exact/well_formed_add.
case: (split _ _) (well_formed_splitl tx swf) (well_formed_splitr tx swf) => [[ssl /= _]] ssr sslwf ssrwf.
move: twf => /= /andP[]/andP[] _ tlwf trwf.
by apply/well_formed_join; apply/IHn.
Qed.

Lemma balanced_union_subdef n s t : well_formed s -> well_formed t -> balanced s -> balanced t -> balanced (union_subdef n s t).
Proof.
rewrite /union_subdef; elim: n s t => [//|] n IHn s t.
case: s => [//|] sl sx sr sh swf + sb.
case: t => [//|] tl tx tr th twf tb.
case: (th <= sh).
  case: (th == 1); first exact/balanced_add.
  case: (split _ _) (well_formed_splitl sx twf) (well_formed_splitr sx twf) (balanced_splitl sx twf tb) (balanced_splitr sx twf tb) => [[stl /= _]] str stlwf strwf stlb strb.
  move: swf sb => /= /andP[]/andP[] _ slwf srwf /andP[]/andP[] _ slb srb.
  apply/balanced_join.
  - exact/well_formed_union_subdef.
  - exact/well_formed_union_subdef.
  - exact/IHn. 
  - exact/IHn. 
case: (sh == 1); first exact/balanced_add.
case: (split _ _) (well_formed_splitl tx swf) (well_formed_splitr tx swf) (balanced_splitl tx swf sb) (balanced_splitr tx swf sb) => [[ssl /= _]] ssr sslwf ssrwf sslb ssrb.
move: twf tb => /= /andP[]/andP[] _ tlwf trwf /andP[]/andP[] _ tlb trb.
apply/balanced_join.
- exact/well_formed_union_subdef.
- exact/well_formed_union_subdef.
- exact/IHn.
- exact/IHn.
Qed.

Lemma well_ordered_union_subdef n s t itv : well_ordered s itv -> well_ordered t itv -> well_ordered (union_subdef n s t) itv.
Proof.
rewrite /union_subdef; elim: n s t itv => [//|] n IHn s t itv.
case: s => [//|] sl sx sr sh swo.
case: t => [//|] tl tx tr th two.
case: (th <= sh).
  case: (th == 1); first by apply/well_ordered_add; move: two => //= /andP[]/andP[].
  case: (split _ _)
    (well_ordered_splitl sx (well_orderedWTr two))
    (well_ordered_splitr sx (well_orderedWTl two))
    => [[stl /= _]] str stlwo strwo.
  move: swo => /= /andP[]/andP[] sxi slwo srwo.
  by apply/well_ordered_join => //; apply/IHn.
case: (sh == 1); first by apply/well_ordered_add; move: swo => //= /andP[]/andP[].
case: (split _ _)
  (well_ordered_splitl tx (well_orderedWTr swo))
  (well_ordered_splitr tx (well_orderedWTl swo))
  => [[ssl /= _]] ssr sslwo ssrwo.
move: two => /= /andP[]/andP[] txi tlwo trwo.
by apply/well_ordered_join => //; apply/IHn.
Qed.

Lemma mem_union_subdef x n s t : well_formed s -> well_formed t -> balanced s -> balanced t -> well_ordered s `]-oo, +oo[ -> well_ordered t `]-oo, +oo[ -> (height s + height t <= n) -> mem (union_subdef n s t) x = (mem s x) || mem t x.
Proof.
rewrite /union_subdef; elim: n s t => [|n IHn] s t.
  by rewrite leqn0 addn_eq0 => /height0 -> /height0 -> _ _ _ _ /andP[] /eqP -> /eqP ->.
case: s => [//|] sl sx sr sh swf + sb + swo.
case: t => [|tl tx tr th twf tb two stn]; first by rewrite orbF.
case: (th <= sh).
  case/boolP: (th == 1) twf two => [/eqP -> twf two|_ twf two].
    rewrite mem_add// orbC; congr orb.
    rewrite mem_node//.
    move: twf => /=; rewrite -andbA andbC eqSS eq_sym -leqn0 geq_max !leqn0 => /andP[]/andP[] /height0 -> /height0 -> /andP[] /eqP -> /eqP ->.
    by rewrite 2!orbF.
  rewrite mem_node//.
  case: (split sx _) (mem_split x sx two)
    (well_formed_splitl sx twf) (well_formed_splitr sx twf)
    (balanced_splitl sx twf tb) (balanced_splitr sx twf tb)
    (well_ordered_splitl sx two) (well_ordered_splitr sx two)
    (height_split sx twf tb) swf swo => [[stl stb]] str -> /= stlwf strwf stlb strb stlwo strwo /andP[] stlh strh /andP[]/andP[] /eqP shE slwf srwf /andP[] slwo srwo.
  rewrite mem_join; first last.
  + exact/well_ordered_union_subdef.
  + exact/well_ordered_union_subdef.
  move: sb => /= /andP[]/andP[] _ slb srb.
  rewrite IHn//; first last.
  + move: shE stn => /= ->; rewrite addSn ltnS; refine (leq_trans _).
    by apply/leq_add => //; apply/leq_maxl.
  + exact (well_orderedWT stlwo).
  + exact (well_orderedWT slwo).
  rewrite IHn//; last first.
  + move: shE stn => /= ->; rewrite addSn ltnS; refine (leq_trans _).
    by apply/leq_add => //; apply/leq_maxr.
  + exact (well_orderedWT strwo).
  + exact (well_orderedWT srwo).
  rewrite -!orbA; apply/orb_id2l => /negPf ->; congr orb.
  rewrite andbF/= !orbA; congr orb.
  exact/orbC.
case/boolP: (sh == 1) swf swo => [/eqP -> swf swo|_ swf swo].
  rewrite mem_add//; congr orb; rewrite mem_node//.
  move: swf => /=; rewrite -andbA andbC eqSS eq_sym -leqn0 geq_max !leqn0 => /andP[]/andP[] /height0 -> /height0 -> /andP[] /eqP -> /eqP ->.
  by rewrite 2!orbF.
rewrite orbC mem_node//.
case: (split tx _) (mem_split x tx swo)
  (well_formed_splitl tx swf) (well_formed_splitr tx swf)
  (balanced_splitl tx swf sb) (balanced_splitr tx swf sb)
  (well_ordered_splitl tx swo) (well_ordered_splitr tx swo)
  (height_split tx swf sb) twf two => [[ssl ssb]] ssr -> /= sslwf ssrwf sslb ssrb sslwo ssrwo /andP[] sslh ssrh /andP[]/andP[] /eqP thE tlwf trwf /andP[] tlwo trwo.
rewrite mem_join; first last.
+ exact/well_ordered_union_subdef.
+ exact/well_ordered_union_subdef.
move: tb => /= /andP[]/andP[] _ tlb trb.
rewrite IHn//; first last.
+ move: thE stn => /= ->; rewrite addnS ltnS; refine (leq_trans _).
  by apply/leq_add => //; apply/leq_maxl.
+ exact (well_orderedWT tlwo).
+ exact (well_orderedWT sslwo).
rewrite IHn//; last first.
+ move: thE stn => /= ->; rewrite addnS ltnS; refine (leq_trans _).
  by apply/leq_add => //; apply/leq_maxr.
+ exact (well_orderedWT trwo).
+ exact (well_orderedWT ssrwo).
rewrite -!orbA; apply/orb_id2l => /negPf ->.
rewrite andbF/= orbC -orbA; congr orb.
by rewrite orbA orbC orbA orbC orbA.
Qed.

Lemma well_formed_union s t : well_formed s -> well_formed t -> well_formed (union s t).
Proof. exact/well_formed_union_subdef. Qed.

Lemma balanced_union s t : well_formed s -> well_formed t -> balanced s -> balanced t -> balanced (union s t).
Proof. exact/balanced_union_subdef. Qed.

Lemma well_ordered_union s t itv : well_ordered s itv -> well_ordered t itv -> well_ordered (union s t) itv.
Proof. exact/well_ordered_union_subdef. Qed.

Lemma mem_union x s t : well_formed s -> well_formed t -> balanced s -> balanced t -> well_ordered s `]-oo, +oo[ -> well_ordered t `]-oo, +oo[ -> mem (union s t) x = (mem s x) || mem t x.
Proof.
move=> swf twf sb tb swo two.
exact/mem_union_subdef.
Qed.

Lemma well_formed_inter s t : well_formed s -> well_formed t -> well_formed (inter s t).
Proof.
elim: s t => [//|] l IHl sx r IHr h t/= /andP[]/andP[] _ {h} lwf rwf twf.
case: (split sx t) (well_formed_splitl sx twf) (well_formed_splitr sx twf) => [[tl /= tb]] tr tlwf trwf.
case: tb.
  apply/well_formed_join.
    exact/IHl.
  exact/IHr.
apply/well_formed_concat.
  exact/IHl.
exact/IHr.
Qed.

Lemma balanced_inter s t : well_formed s -> well_formed t -> balanced s -> balanced t -> balanced (inter s t).
Proof.
elim: s t => [//|] l IHl sx r IHr h t/= /andP[]/andP[] _ {h} lwf rwf twf /andP[]/andP[] _ lb rb tb.
case: (split sx t)
  (well_formed_splitl sx twf) (well_formed_splitr sx twf)
  (balanced_splitl sx twf tb) (balanced_splitr sx twf tb) => [[tl /= +]] tr tlwf trwf tlb trb.
case.
  apply/balanced_join; try exact/well_formed_inter.
    exact/IHl.
  exact/IHr.
apply/balanced_concat; try exact/well_formed_inter.
  exact/IHl.
exact/IHr.
Qed.

Lemma well_ordered_mem_inter x s t itv : well_ordered s itv -> well_ordered t itv -> well_ordered (inter s t) itv && (mem (inter s t) x == mem s x && mem t x).
Proof.
elim: s t itv => [//|] l IHl sx r IHr h t itv swo.
rewrite mem_node ?(well_orderedWT swo)//; move: swo => /= /andP[]/andP[] sxi lwo rwo two.
case: (split sx t) (well_ordered_splitl sx (well_orderedWTr two)) (well_ordered_splitr sx (well_orderedWTl two)) (mem_split x sx (well_orderedWT two)) => [[tl /= +]] tr tlwo trwo.
case => /= xt.
  move: IHl IHr => /(_ tl _ lwo tlwo) /andP[] ltlwo /eqP xltl
    /(_ tr _ rwo trwo) /andP[] rtrwo /eqP xrtr.
  apply/andP; split; first exact/well_ordered_join.
  rewrite mem_join//; first last.
  - exact/(well_orderedWTr rtrwo).
  - exact/(well_orderedWTl ltlwo).
  apply/eqP; rewrite xltl xrtr xt -!orbA -orb_andr; congr orb.
  rewrite andb_orl !andb_orr !orbA; congr orb; rewrite -orbA -[LHS]orbF; congr orb.
  apply/esym/Bool.orb_false_intro; apply/negP => /andP[].
    move=> /(mem_well_ordered lwo)/= + /(mem_well_ordered trwo)/=.
    by rewrite !in_itv/= => /andP[_] xsx /andP[] /(lt_trans xsx); rewrite ltxx.
  move=> /(mem_well_ordered rwo)/= + /(mem_well_ordered tlwo)/=.
  by rewrite !in_itv/= => /andP[sxx] _ /andP[_] /(lt_trans sxx); rewrite ltxx.
move: IHl IHr => /(_ tl _ lwo tlwo) /andP[] ltlwo /eqP xltl
  /(_ tr _ rwo trwo) /andP[] rtrwo /eqP xrtr.
have sxm: leo (Some sx) (min (inter r tr)).
  case: (min _) (mem_min (well_orderedWT rtrwo)) => /= [m|//].
  move=> /(mem_well_ordered rtrwo)/=.
  by rewrite in_itv/= => /andP[]/ltW.
apply/andP; split.
  apply/well_ordered_concat => //; last first.
    apply/(well_orderedW _ rtrwo); rewrite subitvE/= lexx andbT.
    by move: sxi; rewrite itv_boundlr => /andP[isx] _; apply/(le_trans isx); rewrite bnd_simp.
  apply/(well_orderedW _ ltlwo); rewrite subitvE lexx/=.
  case: (min _) sxm => /= [//|_].
  by move: sxi; rewrite itv_boundlr => /andP[_] sxi; apply/(le_trans _ sxi); rewrite bnd_simp.
rewrite mem_concat; first last.
- exact/(well_orderedWT rtrwo).
- apply/(well_orderedW _ ltlwo); rewrite subitvE/=.
  by case: (min _) sxm.
apply/eqP; rewrite xltl xrtr xt.
case/boolP: (mem l x) => [xl|_]/=.
  rewrite orbT/= andbC; congr orb; apply/imply_andbl/implyP.
  move: (mem_well_ordered lwo xl) => /= + /(mem_well_ordered trwo)/=.
  by rewrite !in_itv/= => /andP[_] sxx /andP[] /(lt_trans sxx); rewrite ltxx.
rewrite orbF; case/boolP: (mem r x) => [xr|_]/=.
  rewrite orbT/= orbC; apply/esym/imply_orbl/implyP.
  move: (mem_well_ordered rwo xr) => /= + /(mem_well_ordered tlwo)/=.
  by rewrite !in_itv/= => /andP[sxx] _ /andP[_] /(lt_trans sxx); rewrite ltxx.
rewrite orbF; apply/esym/negP => /andP[] /eqP xsx /orP; case.
  move=> /(mem_well_ordered tlwo)/=.
  by rewrite in_itv/= xsx ltxx andbF.
move=> /(mem_well_ordered trwo)/=.
by rewrite in_itv/= xsx ltxx.
Qed.

Lemma well_ordered_inter s t itv : well_ordered s itv -> well_ordered t itv -> well_ordered (inter s t) itv.
Proof.
by case: s => [//|] l x r h swo /(well_ordered_mem_inter x swo) => /andP[].
Qed.

Lemma mem_inter x s t : well_ordered s `]-oo, +oo[ -> well_ordered t `]-oo, +oo[ -> mem (inter s t) x = mem s x && mem t x.
Proof. by move=> swo /(well_ordered_mem_inter x swo) => /andP[] _ /eqP. Qed.

Lemma inters0 s : inter s (leaf elt) = (leaf elt).
Proof. by elim: s => [//|l IHl x r IHr h]/=; rewrite IHl IHr. Qed.

Lemma inters1 s x : inter s (singleton x) = if mem s x then singleton x else leaf elt.
Proof.
elim: s => [//|l IHl y r IHr h]/=.
case /comparable_ltgtP: (comparableT x y) => /=; rewrite !inters0 /=.
- by rewrite IHl => _; case: (mem _ _).
- by rewrite IHr => _; case: (mem _ _).
- by move=> ->.
Qed.

(*Lemma cardUI s t : well_formed s -> well_formed t -> card (union s t) + card (inter s t) = card s + card t.
Proof.
rewrite /union; move: {2 3}(height s + height t) (leqnn (height s + height t)) => n.
elim: n s t => [s t + swf twf|n IHn s t].
  by rewrite leqn0 addn_eq0 height0// height0// => /andP[] /eqP -> /eqP ->.
case: s => [/=|sl sx sr sh +] swf/=; first by rewrite addn0.
case: t => [|tl tx tr th stn twf]; first by rewrite /= 2!inters0.
case: (th <= sh).
  case/boolP: (th == 1).
    move: twf => /[swap] /eqP -> /=; rewrite eqSS eq_sym -leqn0 geq_max !leqn0.
    move=> /andP[]/andP[] /[swap] /height0 -> /[swap] /height0 -> /andP[] /eqP -> /eqP -> /=.
    rewrite -/(add tx (node sl sx sr sh)) card_add -addnA/=; congr (_ + _).
    by case /comparable_ltgtP: (comparableT sx tx) => // _; rewrite !inters0//= inters1; case: (mem _ _) => /=.
    Search split.
 *)

Lemma split_bisP x s : well_ordered s `]-oo, +oo[ ->
  match split_bis x s with
  | None => mem s x
  | Some (l, r) => (l == (split x s).1.1) && (r tt == (split x s).2) && ((split x s).1.2 == false)
  end.
Proof.
elim: s => [//|] l IHl sx r IHr h /= /andP[] lwo rwo.
case /comparable_ltgtP: (comparableT x sx) => // [xsx|sxx].
  case: (split_bis x l) (IHl (well_orderedWT lwo)) => [|//] [sl sr]/= /andP[]/andP[] /eqP -> /eqP ->.
  case: (split x l) => [[]]/= ssl ssb ssr ->.
  by rewrite !eqxx.
case: (split_bis x r) (IHr (well_orderedWT rwo)) => [|//] [sl sr]/= /andP[]/andP[] /eqP -> /eqP ->.
case: (split x r) => [[]]/= ssl ssb ssr ->.
by rewrite !eqxx.
Qed.

Lemma disjointP s t : well_ordered s `]-oo, +oo[ -> well_ordered t `]-oo, +oo[ -> reflect (forall x, ~~ (mem s x && mem t x)) (disjoint s t).
Proof.
elim: s t => [|l IHl sx r IHr h] t swo two; first exact/(iffP idP).
rewrite [X in reflect _ X]/=.
case: t two => [|tl tx tr th] two.
  by apply/(iffP idP) => // _ x; rewrite andbF.
move: (node tl tx tr th) two => t two {tl tx tr th}.
case: (split_bis sx t) (split_bisP sx two) => [[tl tr] /andP[]/andP[] /eqP -> /eqP -> /eqP|] sxt; last first.
  by apply/Bool.ReflectF => /(_ sx); rewrite /= eqxx sxt.
case: (split sx t) (well_ordered_splitl sx two) (well_ordered_splitr sx two) sxt (fun x => mem_split x sx two) => [[stl stb]] str stlwo strwo sxt.
rewrite sxt [X in X -> _]/= => xt.
apply/(iffP andP) => [[lstl rstr] x|xmem/=]; last first.
  move: (swo) stlwo strwo => /= /andP[] /well_orderedWT lwo /well_orderedWT rwo /well_orderedWT stlwo /well_orderedWT strwo.
  split.
    apply/IHl => // x; apply/negP => /andP[] xl xstl.
    move: xmem => /(_ x).
    by rewrite mem_node// xt xl xstl orbT.
  apply/IHr => // x; apply/negP => /andP[] xr xstr.
  move: xmem => /(_ x).
  by rewrite mem_node// xt xr xstr !orbT.
rewrite mem_node// xt andbC.
move: (swo) => /= /andP[] lwo rwo.
apply/andP => -[]/orP; case=> [xstl|xstr].
  move: lstl => /= /IHl-/(_ (well_orderedWT lwo) (well_orderedWT stlwo) x).
  rewrite xstl andbT => /negPf ->; rewrite orbF.
  move: (mem_well_ordered stlwo xstl); rewrite in_itv/= => xsx.
  move=> /orP; case=> [/eqP xsxE|/(mem_well_ordered rwo)].
    by move: xsx; rewrite xsxE ltxx.
  by rewrite in_itv/= andbT => /(lt_trans xsx); rewrite ltxx.
move: rstr => /= /IHr-/(_ (well_orderedWT rwo) (well_orderedWT strwo) x).
rewrite xstr andbT => /negPf ->; rewrite orbF.
move: (mem_well_ordered strwo xstr); rewrite in_itv/= andbT => sxx.
move=> /orP; case=> [/eqP xsx|/(mem_well_ordered lwo)].
  by move: sxx; rewrite xsx ltxx.
by rewrite in_itv/= => /(lt_trans sxx); rewrite ltxx.
Qed.

Lemma well_formed_diff s t : well_formed s -> well_formed t -> well_formed (diff s t).
Proof.
elim: s t => [//|] l IHl sx r IHr h t swo.
case: t => [//|] tl tx tr th two/=. 
rewrite -/(split sx (node tl tx tr th)).
move: (node tl tx tr th) two swo => t twf/= /andP[]/andP[] _ {h} lwf rwf.

case: (split sx t) (well_formed_splitl sx twf) (well_formed_splitr sx twf) => [[stl /= +]] str stlwf strwf.
case.
  apply/well_formed_concat.
    exact/IHl.
  exact/IHr.
apply/well_formed_join.
  exact/IHl.
exact/IHr.
Qed.

Lemma balanced_diff s t : well_formed s -> well_formed t -> balanced s -> balanced t -> balanced (diff s t).
Proof.
elim: s t => [//|] l IHl sx r IHr h t swf + sb.
case: t => [//|] tl tx tr th twf tb/=.
rewrite -/(split sx (node tl tx tr th)).
move: (node tl tx tr th) twf tb swf sb => t twf tb/= /andP[]/andP[] _ {h} lwf rwf /andP[]/andP[] _ lb rb.
case: (split sx t)
  (well_formed_splitl sx twf) (well_formed_splitr sx twf)
  (balanced_splitl sx twf tb) (balanced_splitr sx twf tb) => [[stl /= +]] str stlwf strwf stlb strb.
case.
  apply/balanced_concat; try exact/well_formed_diff.
    exact/IHl.
  exact/IHr.
apply/balanced_join; try exact/well_formed_diff.
  exact/IHl.
exact/IHr.
Qed.

Lemma well_ordered_mem_diff x s t itv : well_ordered s itv -> well_ordered t itv -> well_ordered (diff s t) itv && (mem (diff s t) x == mem s x && ~~ mem t x).
Proof.
elim: s t itv => [//|] l IHl sx r IHr h t itv swo.
rewrite mem_node ?(well_orderedWT swo)//.
case: t => [//|tl tx tr th] two.
  by rewrite /diff swo mem_node ?(well_orderedWT swo)// andbT/=.
rewrite [diff _ _]/= -/(split sx (node tl tx tr th)).
move: (node tl tx tr th) two swo => t two/= /andP[]/andP[] sxi lwo rwo.
case: (split sx t) (well_ordered_splitl sx (well_orderedWTr two)) (well_ordered_splitr sx (well_orderedWTl two)) (mem_split x sx (well_orderedWT two)) => [[stl /= +]] str stlwo strwo.
case => /= xt; last first.
  move: IHl IHr => /(_ stl _ lwo stlwo) /andP[] ltlwo /eqP xltl
    /(_ str _ rwo strwo) /andP[] rtrwo /eqP xrtr.
  apply/andP; split; first exact/well_ordered_join.
  rewrite mem_join//; first last.
  - exact/(well_orderedWTr rtrwo).
  - exact/(well_orderedWTl ltlwo).
  apply/eqP; rewrite xltl xrtr xt. 
  case/boolP: (mem stl x) => [/(mem_well_ordered stlwo)/=|_].
    rewrite in_itv/= => /andP[_].
    have [->|_] := eqVneq x sx; first by rewrite ltxx.
    case/boolP: (mem r x) => [/(mem_well_ordered rwo)/=|_].
      by rewrite in_itv/= => /andP[sxx] _ /(lt_trans sxx); rewrite ltxx.
    case/boolP: (mem str x) => [/(mem_well_ordered strwo)/=|_ _].
      by rewrite in_itv/= => /andP[xsx] _ /(lt_trans xsx); rewrite ltxx.
    by rewrite /= !orbF.
  case/boolP: (mem str x) => [/(mem_well_ordered strwo)/=|_]; last by rewrite !andbT.
  rewrite in_itv/= => /andP[+] _.
  have [->|_] := eqVneq x sx; first by rewrite ltxx.
  case/boolP: (mem l x) => [/(mem_well_ordered lwo)/=|//].
  by rewrite in_itv/= => /andP[_] xsx /(lt_trans xsx); rewrite ltxx.
move: IHl IHr => /(_ stl _ lwo stlwo) /andP[] ltlwo /eqP xltl
  /(_ str _ rwo strwo) /andP[] rtrwo /eqP xrtr.
have sxm: leo (Some sx) (min (diff r str)).
  case: (min _) (mem_min (well_orderedWT rtrwo)) => /= [m|//].
  move=> /(mem_well_ordered rtrwo)/=.
  by rewrite in_itv/= => /andP[]/ltW.
apply/andP; split.
  apply/well_ordered_concat => //; last first.
    apply/(well_orderedWl _ rtrwo).
    by move: sxi; rewrite itv_boundlr => /andP[isx] _; apply/(le_trans isx); rewrite bnd_simp.
  (* N.B. Coq instanciates `itv` too early to use `well_orderedWr`. *)
  apply/(well_orderedW _ ltlwo); rewrite subitvE lexx/=.
  case: (min _) sxm => /= [//|_].
  by move: sxi; rewrite itv_boundlr => /andP[_] sxi; apply/(le_trans _ sxi); rewrite bnd_simp.
rewrite mem_concat; first last.
- exact/(well_orderedWT rtrwo).
  (* N.B. Coq instanciates `itv` too early to use `well_orderedWr`. *)
- apply/(well_orderedW _ ltlwo); rewrite subitvE/=.
  by case: (min _) sxm.
apply/eqP; rewrite xltl xrtr xt.
move: lwo rwo => /well_orderedWTl/mem_well_ordered lwo /well_orderedWTr/mem_well_ordered rwo.
have [->|_]/= := eqVneq x sx.
  apply/negP => /orP; case=> /andP[].
    by move=> /lwo; rewrite in_itv/= ltxx.
  by move=> /rwo; rewrite in_itv/= ltxx.
case/boolP: (mem l x) => [/lwo/=|_].
  rewrite in_itv/= => xsx.
  case/boolP: (mem r x) => [/rwo|_]/=.
    by rewrite in_itv/= andbT => /(lt_trans xsx); rewrite ltxx.
  case/boolP: (mem str x) => [/(mem_well_ordered strwo)|_]/=.
    by rewrite in_itv/= => /andP[] /(lt_trans xsx); rewrite ltxx.
  by rewrite !orbF.
case/boolP: (mem r x) => [/rwo/=|//].
rewrite in_itv/= andbT => sxx.
case/boolP: (mem stl x) => [/(mem_well_ordered stlwo)|//]/=.
by rewrite in_itv/= => /andP[_] /(lt_trans sxx); rewrite ltxx.
Qed.

Lemma well_ordered_diff s t itv : well_ordered s itv -> well_ordered t itv -> well_ordered (diff s t) itv.
Proof.
by case: s => [//|] l x r h swo /(well_ordered_mem_diff x swo) => /andP[].
Qed.

Lemma mem_diff x s t : well_ordered s `]-oo, +oo[ -> well_ordered t `]-oo, +oo[ -> mem (diff s t) x = mem s x && ~~ mem t x.
Proof. by move=> swo /(well_ordered_mem_diff x swo) => /andP[] _ /eqP. Qed.

Lemma subset_subdefP n s t : well_formed s -> well_formed t -> well_ordered s `]-oo, +oo[ -> well_ordered t `]-oo, +oo[ -> height s + height t <= n -> reflect (forall x, mem s x -> mem t x) (subset_subdef n s t).
Proof.
pose f := fix F s := match s with | leaf => 0 | node l _ r _ => (maxn (F l) (F r)).+1 end.
have fE : forall s, well_formed s -> height s = f s.
  by elim=> //= l IHl _ r IHr h /andP[]/andP[] /eqP -> /IHl -> /IHr ->.
move=> swf twf; rewrite !fE// => {swf twf}.
elim: n s t => [|n IHn] s t.
  rewrite leqn0 addn_eq0.
  case: s => [|//] _.
  case: t => [|//] _ _ /=.
  exact/(iffP idP).
case: s => [|sl sx sr sh] swo.
  by move=> _ _; apply/(iffP idP).
case: t => [|tl tx tr th] two hn.
  by apply/(iffP idP) => // /(_ sx)/=; apply; rewrite eqxx.
rewrite [X in reflect _ X]/=.
move: (swo); rewrite [well_ordered _ _]/= => /andP[] /[dup] slwo /well_orderedWT slwo' /[dup] srwo /well_orderedWT srwo'.
move: (two); rewrite [well_ordered _ _]/= => /andP[] /[dup] tlwo /well_orderedWT tlwo' /[dup] trwo /well_orderedWT trwo'.
have sl0wo : well_ordered (node sl sx (leaf elt) 0) `]-oo, +oo[.
  by rewrite /= andbT.
have sl0tln : f (node sl sx (leaf elt) 0) + f tl <= n.
  by move: hn => /=; rewrite addnS ltnS maxn0; refine (leq_trans _); apply/leq_add; [rewrite ltnS|]; apply/leq_maxl.
have srtn : f sr + f (node tl tx tr th) <= n.
  by move: hn => /=; rewrite addSn ltnS; refine (leq_trans _); rewrite leq_add2r leq_maxr.
have sltn : f sl + f (node tl tx tr th) <= n.
  by move: hn => /=; rewrite addSn ltnS; refine (leq_trans _); rewrite leq_add2r leq_maxl.
have sr0trn : f (node (leaf elt) sx sr 0) + f tr <= n.
  by move: hn => /=; rewrite addnS ltnS max0n; refine (leq_trans _); apply/leq_add; [rewrite ltnS|]; apply/leq_maxr.
have sltln : f sl + f tl <= n.
  by move: hn => /=; rewrite addSn ltnS; refine (leq_trans _); apply/leq_add; [|apply/leqW]; apply/leq_maxl.
have srtrn : f sr + f tr <= n.
  by move: hn => /=; rewrite addSn ltnS; refine (leq_trans _); apply/leq_add; [|apply/leqW]; apply/leq_maxr.
case /comparable_ltgtP: (comparableT sx tx) => sxtx; (apply/(iffP andP) => [[]|]).
- move=> /IHn-/(_ sl0wo tlwo' sl0tln) IHl /IHn-/(_ srwo' two srtn) IHr x.
  move: (IHl x) (IHr x); rewrite mem_node// mem_node// mem_node//= orbF => {}IHl {}IHr /orP.
  by case=> [/IHl|/IHr] -> //; rewrite orbT.
- move=> IH; split; apply/IHn => // x; rewrite mem_node//; last first.
    by move=> xr; move: (IH x); rewrite mem_node// mem_node// xr orbT; apply.
  rewrite orbF => xs; move: (IH x); rewrite mem_node// mem_node// xs/= => /(_ erefl).
  have xtx: (x < tx)%O.
    move/orP: xs; case => [/eqP -> //|/(mem_well_ordered slwo)/=].
    rewrite in_itv/= => xsx.
    exact/(lt_trans xsx sxtx).
  move=> /orP; case=> [/orP|]; [case=> [/eqP xtxE|//]|].
    by move: xtx; rewrite xtxE ltxx.
  move=> /(mem_well_ordered trwo)/=; rewrite in_itv/= andbT.
  by move=> /(lt_trans xtx); rewrite ltxx.
- move=> /IHn-/(_ slwo' two sltn) IHl /IHn-/(_ srwo trwo' sr0trn) IHr x.
  move: (IHl x) (IHr x); rewrite mem_node// mem_node// mem_node//= orbF => {}IHl {}IHr.
  by rewrite orbAC => /orP; case=> [/IHr|/IHl] -> //; rewrite orbT.
- move=> IH; split; apply/IHn => // x; rewrite mem_node//.
    by move=> xl; move: (IH x); rewrite mem_node// mem_node// xl orbT; apply.
  rewrite orbF => xs; move: (IH x); rewrite mem_node// mem_node// orbAC xs/= => /(_ erefl) /orP.
  have txx: (tx < x)%O.
    move/orP: xs; case => [/eqP -> //|/(mem_well_ordered srwo)/=].
    by rewrite in_itv/= andbT; apply/(lt_trans sxtx).
  case=> // /orP; case=> [/eqP xtxE|//].
    by move: txx; rewrite xtxE ltxx.
  move=> /(mem_well_ordered tlwo)/=.
  by rewrite in_itv/= => /(lt_trans txx); rewrite ltxx.
- move=> /IHn-/(_ slwo' tlwo' sltln) IHl /IHn-/(_ srwo' trwo' srtrn) IHr x.
  move: (IHl x) (IHr x); rewrite mem_node// mem_node// => {}IHl {}IHr.
  by rewrite sxtx => /orP; case=> [/orP|/IHr ->]; [case=> [-> //| /IHl ->]|]; rewrite orbT.
- subst tx.
  move=> IH; split; apply/IHn => // x.
    move=> /[dup] /(mem_well_ordered slwo)/=.
    rewrite in_itv/= => xsx xl; move: (IH x); rewrite mem_node// mem_node// xl orbT => /(_ erefl)/orP.
    case=> [/orP|]; [case=> [/eqP xsxE|//]|].
      by move: xsx; rewrite xsxE ltxx.
    move=> /(mem_well_ordered trwo)/=.
    by rewrite in_itv/= andbT => /(lt_trans xsx); rewrite ltxx.
  move=> /[dup] /(mem_well_ordered srwo)/=.
  rewrite in_itv/= andbT => sxx xr; move: (IH x); rewrite mem_node// mem_node// xr orbT => /(_ erefl)/orP.
  case=> [/orP|//]; case=> [/eqP xsxE|].
    by move: sxx; rewrite xsxE ltxx.
  move=> /(mem_well_ordered tlwo)/=.
  by rewrite in_itv/= => /(lt_trans sxx); rewrite ltxx.
Qed.

Lemma subsetP s t : well_formed s -> well_formed t -> well_ordered s `]-oo, +oo[ -> well_ordered t `]-oo, +oo[ -> reflect (forall x, mem s x -> mem t x) (subset s t).
Proof. by move=> swf twf swo two; apply/subset_subdefP. Qed.

Lemma allP (p : pred elt) s : well_ordered s `]-oo, +oo[ -> reflect (forall x, mem s x -> p x) (all p s).
Proof.
elim: s => [|l IHl x r IHr h] swo; apply/(iffP idP) => // [|mP/=];
  move: (swo) => /= /andP[]
    /well_orderedWT {}/IHl IHl
    /well_orderedWT {}/IHr IHr.
  move=> /andP[]/andP[] px {}/IHl lP {}/IHr rP y.
  by case /comparable_ltgtP: (comparableT x y) => /= [_|_|<-]//;
    [apply/rP|apply/lP].
apply/andP; split; [apply/andP; split|].
- by apply/mP; rewrite /= eqxx.
- by apply /IHl => y yl; apply/mP; rewrite mem_node// yl orbT.
- by apply /IHr => y yr; apply/mP; rewrite mem_node// yr !orbT.
Qed.

Lemma hasP (p : pred elt) s : well_ordered s `]-oo, +oo[ -> reflect (exists x, mem s x && p x) (has p s).
Proof.
elim: s => [|l IHl x r IHr h] swo; apply/(iffP idP) => [//|[]// y];
  move: (swo); rewrite [has _ _]/= [well_ordered _ _]/= => /andP[]
    /well_orderedWT lwo /well_orderedWT rwo.
  move=> /orP; case=>[/orP|/(IHr rwo) [y /andP[] yr py]]; [case=> [px|/(IHl lwo) [y /andP[] yl py]]|].
  - by exists x; rewrite /= eqxx.
  - by exists y; rewrite mem_node// yl orbT.
  - by exists y; rewrite mem_node// yr orbT.
rewrite mem_node// => /andP[] /orP + py; case=> [/orP|yr]; [case=> [/eqP <-|yl]|].
- by rewrite py.
- by apply/orP; left; apply/orP; right; apply/(IHl lwo); exists y; rewrite yl.
- by apply/orP; right; apply/(IHr rwo); exists y; rewrite yr.
Qed.

Lemma well_formed_filter p s : well_formed s -> well_formed (filter p s).
Proof.
elim: s => [//|l IHl x r IHr h]/= /andP[]/andP[_] /IHl lwf /IHr rwf.
case: (p x).
  exact/well_formed_join.
exact/well_formed_concat.
Qed.

Lemma balanced_filter p s : well_formed s -> balanced s -> balanced (filter p s).
Proof.
elim: s => [//|l IHl x r IHr h]/= /andP[]/andP[_] lwf rwf /andP[]/andP[_] /(IHl lwf) lb /(IHr rwf) rb.
case: (p x).
  by apply/balanced_join => //; apply/well_formed_filter.
by apply/balanced_concat => //; apply/well_formed_filter.
Qed.

Lemma well_ordered_filter p s itv : well_ordered s itv -> well_ordered (filter p s) itv.
Proof.
elim: s itv => [//|l IHl x r IHr h]/= itv /andP[]/andP[] xi /IHl lwo /IHr rwo.
case: (p x); first exact/well_ordered_join. 
move: xi; rewrite itv_boundlr => /andP[] ix xi.
apply/well_ordered_concat; last first.
  apply/(well_orderedW _ rwo); rewrite subitvE/= lexx andbT.
  exact/(le_trans ix)/lexx.
apply/(well_orderedW _ lwo); rewrite subitvE lexx/=.
case: (min _) (mem_min (well_orderedWT rwo)) => [y|_]/=.
  move=> /(mem_well_ordered rwo).
  by rewrite in_itv/= => /andP[]/ltW.
exact/(le_trans _ xi)/lexx.
Qed.

Lemma well_formed_partition p s : well_formed s -> well_formed (partition p s).1 && well_formed (partition p s).2.
Proof.
elim: s => [//|] l IHl x r IHr h/= /andP[]/andP[] _ {h} {}/IHl + {}/IHr.
move: (partition p l) => [pll plr]/= /andP[] pllwf plrwf.
move: (partition p r) => [prl prr]/= /andP[] prlwf prrwf.
case: (p x) => /=; apply/andP; split.
- exact/well_formed_join.
- exact/well_formed_concat.
- exact/well_formed_concat.
- exact/well_formed_join.
Qed.

Lemma balanced_partition p s : well_formed s -> balanced s -> balanced (partition p s).1 && balanced (partition p s).2.
Proof.
elim: s => [//|] l IHl x r IHr h/= /andP[]/andP[] _ {h} /[dup] lwo {}/IHl IHl /[dup] rwo {}/IHr IHr /andP[]/andP[] _ {}/IHl + {}/IHr.
move: (partition p l) (well_formed_partition p lwo) => [pll plr]/= /andP[] pllwf plrwf /andP[] pllb plrb.
move: (partition p r) (well_formed_partition p rwo) => [prl prr]/= /andP[] prlwf prrwf /andP[] prlb prrb.
case: (p x) => /=; apply/andP; split.
- exact/balanced_join.
- exact/balanced_concat.
- exact/balanced_concat.
- exact/balanced_join.
Qed.

Lemma well_ordered_partition p s itv : well_ordered s itv -> well_ordered (partition p s).1 itv && well_ordered (partition p s).2 itv.
Proof.
elim: s itv => [//|] l IHl x r IHr h itv/= /andP[]/andP[] xi' {}/IHl + {}/IHr.
move: (xi'); rewrite itv_boundlr => /andP[ix] xi.
move: (partition p l) => [pll plr]/= /andP[] pllwo plrwo.
move: (partition p r) => [prl prr]/= /andP[] prlwo prrwo.
case: (p x) => /=; apply/andP; split.
- exact/well_ordered_join.
- apply/well_ordered_concat; last first.
    by apply/(well_orderedWl _ prrwo)/(le_trans ix); rewrite bnd_simp.
  move: (min prr) (mem_min (well_orderedWT prrwo)) => [m|_]/=; last first.
  (* N.B. Coq instanciates `itv` too early to use `well_orderedWr`. *)
    apply/(well_orderedW _ plrwo); rewrite subitvE lexx/=.
    by apply/(le_trans _ xi); rewrite bnd_simp.
  move=> /[dup] /(mem_well_ordered (well_orderedWTl prrwo)) + /(mem_well_ordered (well_orderedWTr prrwo))/=.
  rewrite itv_boundlr/= in_itv/= andbT => mi xm.
  (* N.B. Coq instanciates `itv` too early to use `well_orderedWr`. *)
  apply/(well_orderedW _ plrwo); rewrite subitvE lexx/=.
  exact/ltW.
- apply/well_ordered_concat; last first.
    exact/(well_orderedWl _ prlwo)/(le_trans ix)/lexx.
  move: (min prl) (mem_min (well_orderedWT prlwo)) => [m|_]/=; last first.
    apply/(well_orderedW _ pllwo); rewrite subitvE lexx/=.
    exact/(le_trans _ xi)/lexx.
  move=> /(mem_well_ordered (well_orderedWTr prlwo)).
  rewrite itv_boundlr/= => /andP[] /ltW xm _.
  by apply/(well_orderedW _ pllwo); rewrite subitvE lexx/=.
- exact/well_ordered_join.
Qed.

Lemma mem_partition x p s : well_ordered s `]-oo, +oo[ -> (mem (partition p s).1 x == p x && mem s x) && (mem (partition p s).2 x == ~~ p x && mem s x).
Proof.
elim: s => [|l IHl sx r IHr h swo].
  by rewrite !andbF.
rewrite mem_node//; move: (swo) => /= /andP[] lwo rwo.
move: (partition p l) (well_ordered_partition p lwo) {IHl} (IHl (well_orderedWT lwo)) => [pll plr]/= /andP[] pllwo plrwo /andP[] /eqP xpll /eqP xplr.
move: (partition p r) (well_ordered_partition p rwo) {IHr} (IHr (well_orderedWT rwo)) => [prl prr]/= /andP[] prlwo prrwo /andP[] /eqP xprl /eqP xprr.
case/boolP: (p sx) => [|/negPf] /= psx; apply/andP; split; apply/eqP.
- by rewrite mem_join// xpll xprl 2!andb_orr andb_eq psx.
- rewrite mem_concat.
  + by rewrite xplr xprr 2!andb_orr (andb_eq (fun x => ~~ p x)) psx.
  + move: (min prr) (mem_min (well_orderedWT prrwo)) => [m|_]/=; last first.
      exact/(well_orderedWT plrwo).
    move=> /(mem_well_ordered (well_orderedWTr prrwo))/=.
    rewrite itv_boundlr/= => /andP[] /ltW sxm _.
    by apply/(well_orderedW _ plrwo); rewrite subitvE/=.
  + exact/(well_orderedWT prrwo).
- rewrite mem_concat.
  + by rewrite xpll xprl 2!andb_orr andb_eq psx.
  + move: (min prl) (mem_min (well_orderedWT prlwo)) => [m|_]/=; last first.
      exact/(well_orderedWT pllwo).
    move=> /(mem_well_ordered (well_orderedWTr prlwo))/=.
    rewrite itv_boundlr/= => /andP[] /ltW sxm _.
    by apply/(well_orderedW _ pllwo); rewrite subitvE/=.
  + exact/(well_orderedWT prlwo).
- by rewrite mem_join// xplr xprr 2!andb_orr (andb_eq (fun x => ~~ p x)) psx.
Qed.

Lemma well_formed_try_join l x r : well_formed l -> well_formed r -> well_formed (try_join l x r).
Proof.
move=> lwf rwf.
rewrite /try_join; case: (_ && _).
  exact/well_formed_join.
apply/well_formed_union => //.
exact/well_formed_add.
Qed.

Lemma balanced_try_join l x r : well_formed l -> well_formed r -> balanced l -> balanced r -> balanced (try_join l x r).
Proof.
move=> lwf rwf lb rb.
rewrite /try_join; case: (_ && _).
  exact/balanced_join.
apply/balanced_union => //.
  exact/well_formed_add.
exact/balanced_add.
Qed.

Lemma well_ordered_try_join l x r itv : x \in itv -> well_ordered l itv -> well_ordered r itv -> well_ordered (try_join l x r) itv.
Proof.
move=> xi lwo rwo.
rewrite /try_join; case/boolP: (_ && _) => [|_]; last first.
  by apply/well_ordered_union => //; apply/well_ordered_add.
move=> /andP[] xl xr.
apply/well_ordered_join => //.
  move: lwo; rewrite well_orderedP => /andP[] lwo /(allP _ lwo) li.
  rewrite well_orderedP; apply/andP; split=> //.
  apply/allP => //= y /[dup] /(maxP lwo) + /li.
  rewrite !itv_boundlr/= => + /andP[->] _ /=.
  move: xl; case: (max l) => [ml|//]/= mlx yml.
  by apply/(le_lt_trans yml).
move: rwo; rewrite well_orderedP => /andP[] rwo /(allP _ rwo) ri.
rewrite well_orderedP; apply/andP; split=> //.
apply/allP => //= y /[dup] /(minP rwo) + /ri.
rewrite !itv_boundlr/= => + /andP[_] -> /=.
move: xr; case: (min r) => [mr|//]/= xmr mry.
by rewrite andbT; apply/(lt_le_trans xmr).
Qed.

Lemma mem_try_join y l x r : well_formed l -> well_formed r -> balanced l -> balanced r -> well_ordered l `]-oo, +oo[ -> well_ordered r `]-oo, +oo[ ->
  mem (try_join l x r) y = (y == x) || mem l y || mem r y.
Proof.
move=> lwf rwf lb rb lwo rwo; rewrite /try_join; case: ifP => [|_]; last first.
  rewrite mem_union//.
  - by rewrite mem_add// orbCA orbA.
  - exact/well_formed_add.
  - exact/balanced_add.
  - exact/well_ordered_add.
move=> /andP[] xl xr.
rewrite mem_join//.
  rewrite well_orderedP; apply/andP; split=> //.
  apply/allP => //= {}y /(maxP lwo).
  rewrite itv_boundlr/=.
  move: xl; case: (max l) => [ml|//]/= mlx yml.
  exact/(le_lt_trans yml).
move: rwo; rewrite well_orderedP => /andP[] rwo /(allP _ rwo) ri.
rewrite well_orderedP; apply/andP; split=> //.
apply/allP => //= {}y /(minP rwo).
rewrite itv_boundlr/=.
move: xr; case: (min r) => [mr|//]/= xmr mry.
by rewrite andbT; apply/(lt_le_trans xmr).
Qed.

Lemma well_formed_try_concat l r : well_formed l -> well_formed r -> well_formed (try_concat l r).

End Theory.

Module AllExports. HB.reexport. End AllExports.

End Subdef.

Import Subdef.AllExports.

Section Def.
Variables (d : unit) (elt : orderType d).

Definition t := {s : Subdef.t elt | Subdef.is_avl s}.

Definition empty : t.
by exists (Subdef.leaf elt).
Defined.

Definition is_empty (s : t) := Subdef.is_empty (val s).

Definition singleton (x : elt) : t.
by exists (Subdef.singleton x).
Defined.

Definition add (x : elt) (s : t) : t.
move: (valP s) => /andP[]/andP[] swf sb swo.
exists (Subdef.add x (val s)).
apply/andP; split; [apply/andP; split|].
- exact/Subdef.well_formed_add.
- exact/Subdef.balanced_add.
- exact/Subdef.well_ordered_add.
Defined.

Definition split (x : elt) (s : t) : t * bool * t.
move: (valP s) => /andP[]/andP[] swf sb swo.
split; [split|].
- exists (Subdef.split x (val s)).1.1.
  apply/andP; split; [apply/andP; split|].
  + exact/Subdef.well_formed_splitl.
  + exact/Subdef.balanced_splitl.
  + exact/(Subdef.well_orderedWT (Subdef.well_ordered_splitl x swo)).
- exact/(Subdef.split x (val s)).1.2.
- exists (Subdef.split x (val s)).2.
  apply/andP; split; [apply/andP; split|].
  + exact/Subdef.well_formed_splitr.
  + exact/Subdef.balanced_splitr.
  + exact/(Subdef.well_orderedWT (Subdef.well_ordered_splitr x swo)).
Defined.

Definition remove (x : elt) (s : t) : t.
move: (valP s) => /andP[]/andP[] swf sb swo.
exists (Subdef.remove x (val s)).
apply/andP; split; [apply/andP; split|].
- exact/Subdef.well_formed_remove.
  Search Subdef.remove.
- exact/Subdef.balanced_remove.
- exact/Subdef.well_ordered_remove.
Defined.

Definition union (s u : t) : t.
move: (valP s) (valP u) => /andP[]/andP[] swf sb swo /andP[]/andP[] uwf ub uwo.
exists (Subdef.union (val s) (val u)).
apply/andP; split; [apply/andP; split|].
- exact/Subdef.well_formed_union.
- exact/Subdef.balanced_union.
- exact/Subdef.well_ordered_union.
Defined.

Definition inter (s u : t) : t.
move: (valP s) (valP u) => /andP[]/andP[] swf sb swo /andP[]/andP[] uwf ub uwo.
exists (Subdef.inter (val s) (val u)).
apply/andP; split; [apply/andP; split|].
- exact/Subdef.well_formed_inter.
- exact/Subdef.balanced_inter.
- exact/Subdef.well_ordered_inter.
Defined.

Definition disjoint (s t : t) := Subdef.disjoint (val s) (val t).

Definition diff (s u : t) : t.
move: (valP s) (valP u) => /andP[]/andP[] swf sb swo /andP[]/andP[] uwf ub uwo.
exists (Subdef.diff (val s) (val u)).
apply/andP; split; [apply/andP; split|].
- exact/Subdef.well_formed_diff.
- exact/Subdef.balanced_diff.
- exact/Subdef.well_ordered_diff.
Defined.

Definition subset (s t : t) := Subdef.subset (val s) (val t).

Definition fold rT (f : elt -> rT -> rT) s accu :=
  Subdef.fold f s accu.

Definition mem (s : t) x := Subdef.mem (val s) x.

Definition all p (s : t) := Subdef.all p (val s).

Definition has p (s : t) := Subdef.has p (val s).

Definition filter (p : pred elt) (s : t) : t.
move: (valP s) => /andP[]/andP[] swf sb swo.
exists (Subdef.filter p (val s)).
apply/andP; split; [apply/andP; split|].
- exact/Subdef.well_formed_filter.
- exact/Subdef.balanced_filter.
- exact/Subdef.well_ordered_filter.
Defined.

Definition partition (p : pred elt) (s : t) : t * t.
move: (valP s) => /andP[]/andP[] swf.
move=> /(Subdef.balanced_partition p swf) /andP[] lb rb.
move=> /(Subdef.well_ordered_partition p) /andP[] lo ro.
move: swf => /(Subdef.well_formed_partition p) /andP[] lf rf.
split.
  exists (Subdef.partition p (val s)).1.
  by apply/andP; split; [apply/andP; split|].
exists (Subdef.partition p (val s)).2.
by apply/andP; split; [apply/andP; split|].
Defined.

Definition card (s : t) := Subdef.card (val s).

Definition elements (s : t) := Subdef.elements (val s).

Definition choose (s : t) := Subdef.choose (val s).

End Def.

End Avl.


