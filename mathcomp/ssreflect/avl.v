From HB Require Import structures.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.PreorderTheory Order.POrderTheory Order.TotalTheory.

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

Fixpoint well_ordered s lb ub := 
  match s with
  | leaf => true
  | node l x r _ => (lto lb (Some x)) && (lto (Some x) ub)%O && (well_ordered l lb (Some x)) && (well_ordered r (Some x) ub)
  end.

Definition is_avl s := (well_formed s) && (balanced s) && (well_ordered s None None).

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

Definition empty := leaf.

Definition is_empty s := match s with | leaf => true | _ => false end.

Fixpoint mem x s :=
  match s with
  | leaf => false
  | node l sx r _ => (x == sx) || (mem x (if (x < sx)%O then l else r))
  end.

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

Fixpoint elements s := (fix F accu s :=
  match s with
  | leaf => accu
  | node l x r _ => F (x :: F accu r) l
  end) [::] s.

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
Implicit Types (s l r : t elt) (x : elt) (lb ub : option elt).

Lemma height0 s : well_formed s -> height s == 0 = (s == leaf elt).
Proof. by case: s => [//|l x r h] /= /andP[]/andP[] /eqP ->. Qed.

Lemma well_orderedWl s lb lb' ub : map_or (fun lb' : elt => map_or (>= lb')%O false lb) true lb'-> well_ordered s lb ub -> well_ordered s lb' ub.
Proof.
elim: s lb lb' ub => [//|] l IHl x r IHr/= _ lb lb' ub lb'lb
    /andP[]/andP[]/andP[] lbx xub lwo rwo.
rewrite xub rwo (IHl _ _ _ lb'lb)// !andbT.
by case: lb' lb'lb lbx => [|//]lb'; case: lb {lwo} => [|//]lb /=; apply: le_lt_trans.
Qed.

Lemma well_orderedWr s lb ub ub' : map_or (fun ub' : elt => map_or (<= ub')%O false ub) true ub' -> well_ordered s lb ub -> well_ordered s lb ub'.
Proof.
elim: s lb ub ub' => [//|] l IHl x r IHr/= _ lb ub ub' ubub'
    /andP[]/andP[]/andP[] lbx xub lwo rwo.
rewrite lbx lwo (IHr _ _ _ ubub')// !andbT.
by case: ub' ubub' xub => [|//]ub'; case: ub {rwo} => [|//]ub /= /[swap]; apply: lt_le_trans.
Qed.

Lemma well_orderedW s lb ub : well_ordered s lb ub -> well_ordered s None None.
Proof. move=> swo; exact/(well_orderedWl _ (well_orderedWr _ swo)). Qed.

Lemma mem_well_ordered x s lb ub : well_ordered s lb ub -> mem x s -> (lto lb (Some x) && lto (Some x) ub).
Proof.
elim: s lb ub => [//|l IHl sx r IHr /= _] lb ub /andP[]/andP[]/andP[] lbsx sxub /IHl {}IHl /IHr {}IHr.
case /comparable_ltgtP: (comparableT x sx) => /= [xsx|sxx|-> _]; last by apply/andP; split.
  by move=> /IHl /andP[] -> {}xsx; exact: (lto_trans xsx sxub).
by move=> /IHr /andP[] {}sxx /= ->; rewrite (lto_trans lbsx sxx).
Qed.

Lemma mem_node y l x r h : well_ordered (node l x r h) None None -> mem y (node l x r h) = (y == x) || (mem y l) || (mem y r).
Proof.
rewrite /mem /=; case /comparable_ltgtP: (comparableT x y) => [xy|yx|//]/= /andP[] lwo rwo.
  by rewrite orbC -[LHS]orbF; congr orb; apply/esym/negP => /(mem_well_ordered lwo) /andP[_]/= /(lt_trans xy); rewrite ltxx.
by rewrite -[LHS]orbF; congr orb; apply/esym/negP => /(mem_well_ordered rwo) /andP[] /(lt_trans yx) + _; rewrite ltxx.
Qed.

Lemma well_ordered_lbP x s lb : well_ordered s lb None -> mem x s -> lto lb (Some x).
Proof.
elim: s lb => [//|l IHl sx r IHr h] lb swo.
rewrite mem_node; last exact/(well_orderedW swo).
move: swo => /= /andP[]/andP[]/andP[] lbx _ /(well_orderedWr (ub':=None) erefl) {}/IHl IHl {}/IHr IHr /orP; case => [/orP|/IHr]; [case=> [/eqP ->|]//|].
exact/(lto_trans lbx).
Qed.

Lemma well_ordered_ubP x s ub : well_ordered s None ub -> mem x s -> lto (Some x) ub.
Proof.
elim: s ub => [//|l IHl sx r IHr h] ub swo.
rewrite mem_node; last exact/(well_orderedW swo).
move: swo => /= /andP[]/andP[] sxub {}/IHl IHl /(well_orderedWl (lb':=None) erefl) {}/IHr IHr /orP; case => [/orP|/IHr//]; case=> [/eqP ->//|/IHl xsx].
exact/(lto_trans xsx sxub).
Qed.

Lemma well_formed_create l x r : well_formed l -> well_formed r -> well_formed (create l x r).
Proof. by rewrite /= eqxx => -> ->. Qed.

Lemma balanced_create l x r : balanced l -> balanced r -> diffn (height l) (height r) <= 2 -> balanced (create l x r).
Proof. by move=> /= -> -> ->. Qed.

Lemma well_ordered_create l x r lb ub : well_ordered l lb (Some x) -> well_ordered r (Some x) ub -> lto lb (Some x) -> lto (Some x) ub -> well_ordered (create l x r) lb ub.
Proof. by move=> /= -> -> -> ->. Qed.

Lemma mem_create y l x r : well_ordered (create l x r) None None -> mem y (create l x r) = (y == x) || (mem y l) || (mem y r).
Proof. exact: mem_node. Qed.

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

Lemma well_ordered_bal l x r lb ub : well_ordered (bal l x r) lb ub = lto lb (Some x) && lto (Some x) ub && well_ordered l lb (Some x) && well_ordered r (Some x) ub.
Proof.
case_bal l r => //= _ _; apply/idP/idP => /andP[]/andP[]/andP[].
- move=> _ rlxub /andP[]/andP[]/andP[] -> xrlx -> -> /andP[]/andP[]/andP[] rlxrx rxub -> ->.
  rewrite rxub xrlx rlxrx (lt_trans xrlx rlxrx).
  by move: (lto_trans (n:=Some x) (lt_trans xrlx rlxrx) rxub) => /= ->.
- move=> lbx _ -> /andP[]/andP[]/andP[] xrx rxub /andP[]/andP[]/andP[] xrlx rlxrx -> -> ->.
  rewrite lbx xrlx rlxrx rxub (lto_trans (m:=Some rlx) lbx xrlx).
  by move: (lto_trans (n:=Some rlx) rlxrx rxub) => /= ->.
- move=> _ rxub /andP[]/andP[]/andP[] -> xrx -> -> ->.
  by move: (lto_trans (n:=Some x) xrx rxub) => /= ->; rewrite xrx rxub.
- move=> lbx _ -> /andP[]/andP[]/andP[] xrx -> -> ->.
  by rewrite xrx lbx (lto_trans (m:=Some rx) lbx xrx). 
- move=> lblrx _ /andP[]/andP[]/andP[] -> lxlrx -> -> /andP[]/andP[]/andP[] lrxx -> -> ->.
  by rewrite (lto_trans (m:=Some x) lblrx lrxx) (lt_trans lxlrx lrxx) lxlrx lrxx.
- move=> _ xub /andP[]/andP[]/andP[] lblx lxx -> /andP[]/andP[]/andP[] lxlrx lrxx -> -> ->.
  rewrite (lto_trans (m:=Some lrx) lblx lxlrx) lblx lxlrx lrxx xub.
  by move: (lto_trans (n:=Some lrx) lrxx xub) => /= ->.
- move=> lblx _ -> /andP[]/andP[]/andP[] lxx -> -> ->.
  by rewrite (lto_trans (m:=Some x) lblx lxx) lblx lxx.
- move=> _ xub /andP[]/andP[]/andP[] -> lxx -> -> ->.
  by rewrite xub lxx; move: (lto_trans (n:=Some lx) lxx xub) => /= ->.
Qed.

Lemma mem_bal y l x r : well_ordered (bal l x r) None None -> mem y (bal l x r) = (y == x) || (mem y l) || (mem y r).
Proof.
case_bal l r; last exact: mem_create.
- move=> _ _ /andP[]/andP[]/andP[] _ _ /andP[]/andP[]/andP[] _ xrlx
    lwo rllwo /andP[]/andP[]/andP[] rlxrx _ rlrwo rrwo.
  rewrite !mem_create; [rewrite !mem_node| | |] => /=.
  + rewrite !orbA; congr (_ || _ || _).
    rewrite [(y == rlx) || _]orbC -!orbA; congr orb.
    rewrite [mem y rll || _]orbC !orbA; congr orb.
    rewrite [_ || mem y l]orbC -!orbA; congr orb.
    exact: orbC.
  + by rewrite (well_orderedWl (lb':=None) erefl rllwo) (well_orderedWr (ub':=None) erefl rlrwo).
    (* TODO: AAAAAArgh, completely and utterly broken unification! *)
  + by rewrite (well_orderedWl (lb':=None) erefl rllwo) /well_ordered rlrwo rrwo !andbT.
  + by rewrite (well_orderedWl (lb':=None) erefl rlrwo) /well_ordered rrwo.
  + by rewrite (well_orderedWr (ub':=None) erefl rllwo) /well_ordered lwo.
  + by rewrite /well_ordered lwo rllwo rlrwo rrwo; move: xrlx rlxrx => /= -> ->.
- move=> _ _ /andP[]/andP[]/andP[] _ _ /andP[]/andP[]/andP[] _ xrx lwo rlwo rrwo.
  rewrite !mem_create; [rewrite !mem_node| |] => /=.
  + rewrite !orbA; congr (_ || _ || _).
    rewrite [(y == rx) || _]orbC -!orbA; congr orb.
    exact: orbC.
  + by rewrite (well_orderedWl (lb':=None) erefl rlwo).
  + by rewrite (well_orderedWr (ub':=None) erefl rlwo) /well_ordered lwo.
  + by rewrite /well_ordered lwo rlwo rrwo !andbT.
- move=> _ _ /andP[]/andP[]/andP[] _ _ /andP[]/andP[]/andP[] _ lxlrx llwo lrlwo /andP[]/andP[]/andP[] lrxx _ lrrwo rwo.
  rewrite !mem_create; [rewrite !mem_node| | |] => /=.
  + rewrite !orbA; congr (_ || _ || _).
    rewrite orbC -!orbA; congr orb.
    rewrite !orbA; congr orb.
    rewrite [(y == lrx) || _]orbC -!orbA; congr orb.
    exact: orbC.
  + by rewrite (well_orderedWl (lb':=None) erefl lrlwo) (well_orderedWr (ub':=None) erefl lrrwo).
    (* TODO: AAAAAArgh, completely and utterly broken unification! *)
  + by rewrite (well_orderedWl (lb':=None) erefl llwo) (well_orderedWr (ub':=None) erefl lrrwo) /well_ordered lrlwo !andbT.
  + by rewrite (well_orderedWl (lb':=None) erefl lrrwo) /well_ordered rwo.
  + by rewrite (well_orderedWr (ub':=None) erefl lrlwo) /well_ordered llwo.
  + by rewrite /well_ordered llwo lrlwo lrrwo rwo; move: lxlrx lrxx => /= -> ->.
- move=> _ _ /andP[]/andP[]/andP[] _ _ llwo /andP[]/andP[]/andP[] lxx _ lrwo rwo.
  rewrite !mem_create; [rewrite !mem_node| |] => /=.
  + by rewrite !orbA; congr (_ || _ || _); rewrite orbC -!orbA.
  + by rewrite (well_orderedWl (lb':=None) erefl llwo) (well_orderedWr (ub':=None) erefl lrwo).
  + by rewrite (well_orderedWl (lb':=None) erefl lrwo) /well_ordered rwo.
  + by rewrite /well_ordered llwo lrwo rwo !andbT.
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

Lemma well_ordered_add x s lb ub : well_ordered s lb ub -> lto lb (Some x) -> lto (Some x) ub -> well_ordered (add x s) lb ub.
Proof.
elim: s lb ub => /= [_ lb ub -> -> //|] l IHl sx r IHr h lb ub /andP[]/andP[]/andP[] lbsx sxub lwo rwo lbx xub.
case /comparable_ltgtP: (comparableT x sx) => [sxx|xsx|->].
- by rewrite well_ordered_bal lbsx rwo IHl//= sxub.
- by rewrite well_ordered_bal lbsx lwo IHr//= sxub.
- by rewrite /= lbsx sxub lwo.
Qed.

Lemma is_avl_add x s : is_avl s -> is_avl (add x s).
Proof.
move=> /andP[]/andP[] swf sb swo; apply/andP; split; [apply/andP; split|].
- exact/well_formed_add.
- exact/balanced_add.
- exact/well_ordered_add.
Qed.

Lemma mem_add y x s : well_ordered s None None -> mem y (add x s) = (y == x) || (mem y s).
Proof.
elim: s => /= [_|l IHl sx r IHr h /andP[] lwo rwo]; first by rewrite if_same.
case /comparable_ltgtP: (comparableT x sx) => [sxx|xsx|<-]; last first.
- by rewrite /= orbA orbb.
- rewrite mem_bal; last first.
    by rewrite well_ordered_bal lwo/=; apply/well_ordered_add.
  rewrite IHr ?(well_orderedW rwo)//.
  move: (@mem_node y l sx r h) => /= ->; last by rewrite lwo.
  by rewrite !orbA; congr orb; rewrite orbC !orbA.
- rewrite mem_bal; last first.
    by rewrite well_ordered_bal rwo/= andbT; apply/well_ordered_add.
  rewrite IHl ?(well_orderedW lwo)//.
  move: (@mem_node y l sx r h) => /= ->; last by rewrite lwo.
  by rewrite !orbA; congr orb; rewrite orbAC orbC !orbA.
Qed.

Lemma card_add x s : card (add x s) = card s + (~~ mem x s).
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

Lemma well_ordered_add_min_element x s lb ub : well_ordered s (Some x) ub -> lto lb (Some x) -> lto (Some x) ub -> well_ordered (add_min_element x s) lb ub.
Proof.
elim: s lb ub => /= [lb ub _ -> ->//|l IHl sx r _ h] lb ub /andP[]/andP[]/andP[] xsx sxub lwo rwo lbx xub.
by rewrite well_ordered_bal/= (lto_trans (m:=Some sx) lbx xsx) sxub rwo/= andbT; apply/IHl.
Qed.

Lemma mem_add_min_element y x s : well_ordered s (Some x) None -> mem y (add_min_element x s) = (y == x) || (mem y s).
Proof.
elim: s => /= [_|l IHl sx r IHr h /andP[]/andP[]/andP[] xsx _ lwo rwo]; first by rewrite if_same.
rewrite mem_bal; last by rewrite well_ordered_bal/= rwo andbT; apply/well_ordered_add_min_element.
rewrite IHl ?(well_orderedWr (ub':=None) erefl lwo)//.
move: (@mem_node y l sx r h) => /= ->; last by rewrite (well_orderedWl (lb':=None) erefl lwo).
by rewrite !orbA; congr orb; rewrite orbAC orbC !orbA.
Qed.

Lemma card_add_min_element x s : well_ordered s (Some x) None -> card (add_min_element x s) = (card s).+1.
Proof.
elim: s => [//|] l IHl sx r _ h/= /andP[]/andP[]/andP[] xsx _ lwo rwo.
by rewrite card_bal IHl ?(well_orderedWr _ lwo)// addSn addnAC.
Qed.

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

Lemma well_ordered_add_max_element x s lb ub : well_ordered s lb (Some x) -> lto lb (Some x) -> lto (Some x) ub -> well_ordered (add_max_element x s) lb ub.
Proof.
elim: s lb ub => /= [lb ub _ -> ->//|l _ sx r IHr h] lb ub /andP[]/andP[]/andP[] lbsx sxx lwo rwo lbx xub.
rewrite well_ordered_bal lbsx lwo.
by move: (lto_trans (n:=Some sx) sxx xub) => /= ->; apply/IHr.
Qed.

Lemma mem_add_max_element y x s : well_ordered s None (Some x) -> mem y (add_max_element x s) = (y == x) || (mem y s).
Proof.
elim: s => /= [_|l IHl sx r IHr h /andP[]/andP[] sxx lwo rwo]; first by rewrite if_same.
rewrite mem_bal; last first.
  by rewrite well_ordered_bal lwo/=; apply/well_ordered_add_max_element.
rewrite IHr ?(well_orderedWl (lb':=None) erefl rwo)//.
move: (@mem_node y l sx r h) => /= ->; last by rewrite lwo (well_orderedWr (ub':=None) erefl rwo).
by rewrite !orbA; congr orb; rewrite orbC !orbA.
Qed.

Lemma card_add_max_element x s : well_ordered s None (Some x) -> card (add_max_element x s) = (card s).+1.
Proof.
elim: s => [//|] l _ sx r IHr h/= /andP[]/andP[] sxx lwo rwo.
by rewrite card_bal IHr ?(well_orderedWl _ rwo)// addnS.
Qed.

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

Lemma well_ordered_join l x r lb ub : well_ordered l lb (Some x) -> well_ordered r (Some x) ub -> lto lb (Some x) -> lto (Some x) ub -> well_ordered (join l x r) lb ub. 
Proof.
elim: l r lb ub => [|ll IHll lx lr IHlr lh] r lb ub lwo rwo lbx xub; first exact/well_ordered_add_min_element.
elim: r ub xub rwo => [|rl IHrl rx rr IHrr rh] ub xub rwo; first exact/well_ordered_add_max_element.
move=> /=; case (leq_diffn2P _ _) => [rhlh|lhrh|_]; last by move: lwo rwo lbx xub => /= -> -> -> ->.
  move: lwo => /= /andP[]/andP[]/andP[] lblx lxx llwo lrwo.
  by rewrite well_ordered_bal lblx (lto_trans (n:=Some lx) lxx xub) llwo IHlr.
move: rwo => /= /andP[]/andP[]/andP[] xrx rxub rlwo rrwo.
by rewrite well_ordered_bal (lto_trans (m:=Some rx) lbx xrx)/= rxub rrwo IHrl.
Qed.

Lemma mem_join y l x r : well_ordered l None (Some x) -> well_ordered r (Some x) None -> mem y (join l x r) = (y == x) || (mem y l) || (mem y r).
Proof.
move=> lwo rwo; move: lwo rwo (well_ordered_join lwo rwo erefl erefl).
elim: l r => [|ll IHll lx lr IHlr lh] r lwo rwo swo; first by rewrite /= orbF; apply/mem_add_min_element.
elim: r rwo swo => [|rl IHrl rx rr IHrr rh] rwo swo; first by rewrite (mem_add_max_element y lwo) orbF.
rewrite mem_node ?(well_orderedW lwo)// mem_node ?(well_orderedW rwo)//. 
move: (lwo) (rwo) swo => /= /andP[]/andP[] lxx llwo lrwo /andP[]/andP[]/andP[] xrx _ rlwo rrwo.
case: (leq_diffn2P _ _) => _ swo; last first.
- rewrite mem_create// !mem_node//=; apply/andP; split=> //=.
    exact: (well_orderedWl (lb':=None) erefl rlwo).
  exact: (well_orderedWr (ub':=None) erefl lrwo).
- rewrite mem_bal// IHrl; first last.
  + by move: swo; rewrite well_ordered_bal => /andP[]/andP[]/andP[] _ _ /(well_orderedWr (ub':=None) erefl) + _.
  + exact/(well_orderedWr (ub:=Some rx)).
  rewrite mem_node; last exact/(well_orderedWr (ub:=Some x)).
  rewrite !orbA; congr (_ || _ || _).
  by rewrite [RHS]orbC !orbA.
- rewrite mem_bal// IHlr//; first last.
  + by move: swo; rewrite well_ordered_bal => /andP[]/andP[]/andP[] _ _ _ /(well_orderedWl (lb':=None) erefl).
  + exact/(well_orderedWl (lb:=Some lx)).
  rewrite mem_node; last exact/(well_orderedWl (lb:=Some x)).
  rewrite !orbA; congr (_ || _ || _ || _ || _).
  by rewrite orbC !orbA.
Qed.

Lemma card_join l x r : well_ordered l None (Some x) -> well_ordered r (Some x) None -> card (join l x r) = (card l + card r).+1.
Proof.
elim: l r => [|ll IHll lx lr IHlr lh] r lwo rwo/=.
  exact/card_add_min_element.
move: (lwo) => /= /andP[]/andP[] lxx llwo lrwo.
elim: r rwo => [|rl IHrl rx rr IHrr rh] rwo/=.
  by rewrite card_bal card_add_max_element ?(well_orderedWl (lb':=None) erefl lrwo)// addnS addn0.
move: (rwo) => /= /andP[]/andP[]/andP[] xrx _ rlwo rrwo.
case: (leq_diffn2P _ _) => _ //=.
- by rewrite card_bal IHlr// ?(well_orderedWl (lb':=None) erefl lrwo)//= addSn !addnS addnA.
- by rewrite card_bal IHrl// ?(well_orderedWr (ub':=None) erefl rlwo)//= addnS !addSn addnA.
Qed.

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

Lemma minP x s : well_ordered s None None -> mem x s -> leo (min s) (Some x).
Proof.
elim: s x => [//|l IHl sx r _ h] x swo.
rewrite mem_node// orbC orbA; move: swo => /= /andP[] lwo /well_ordered_lbP/= xr.
case: l IHl lwo => [/=|ll lx lr lh] mP lwo.
  by rewrite orbF => /orP; case=> [/xr/ltW//|/eqP ->]; apply/lexx.
move=> /orP; case => [xm|/(mP _ (well_orderedW lwo))//].
move: mP => /(_ lx (well_orderedW lwo)); mp=> [|mlx]; first by rewrite /= eqxx.
apply/(leo_trans mlx) => /=; move: (well_ordered_ubP (x:=lx) lwo); mp=> [|/= /ltW lxsx].
  by rewrite /= eqxx.
move: xm => /orP; case=> [/xr/ltW|/eqP ->//].
exact/(le_trans lxsx).
Qed.

Lemma mem_min s : well_ordered s None None -> map_or (fun x => mem x s) (s == leaf elt) (min s).
Proof.
elim: s => [//|] l + x r _ h.
rewrite /min -/(min l); case: l => [|ll lx lr lh].
  by move=> _ _ /=; rewrite eqxx.
have: (node ll lx lr lh != leaf elt) by [].
move: (node ll lx lr lh) => l; case: (min l) => [m _ IHl swo|/negP l0]/=; last first.
  by move=> /[swap] /andP[] /well_orderedW lwo _ /(_ lwo).
rewrite -/(mem m (node l x r h)) mem_node//.
by move: swo IHl => /= /andP[] /well_orderedW lwo _ -> //; rewrite orbT.
Qed.

Lemma maxP x s : well_ordered s None None -> mem x s -> leo (Some x) (max s).
Proof.
elim: s x => [//|l _ sx r IHr h] x swo.
rewrite mem_node//; move: swo => /= /andP[] /well_ordered_ubP/= xl rwo.
case: r IHr rwo => [/=|rl rx rr rh] mP rwo.
  by rewrite orbF => /orP; case=> [/eqP ->|/xl/ltW//]; apply/lexx.
move=> /orP; case => [xm|/(mP _ (well_orderedW rwo))//].
move: mP => /(_ rx (well_orderedW rwo)); mp=> [|mrx]; first by rewrite /= eqxx.
move=> /=; move: (erefl (leo (Some x) (max (node rl rx rr rh)))); rewrite [RHS]/= => <-.
refine (leo_trans _ mrx) => /=; move: (well_ordered_lbP (x:=rx) rwo); mp=> [|/= /ltW sxrx].
  by rewrite /= eqxx.
move: xm => /orP; case=> [/eqP ->//|/xl/ltW] xsx.
exact/(le_trans xsx sxrx).
Qed. 

Lemma mem_max s : well_ordered s None None -> map_or (fun x => mem x s) true (max s).
Proof.
elim: s => [//|] l _ x r + h.
rewrite /max -/(max r); case: r => [|rl rx rr rh].
  by move=> _ _ /=; rewrite eqxx.
move: (node rl rx rr rh) => r; case: (max r) => [|//] m IHr swo.
rewrite /= -/(mem m (node l x r h)) mem_node//.
by move: swo IHr => /= /andP[] _ /well_orderedW rwo -> //; rewrite !orbT.
Qed.

Lemma well_ordered_remove_min s ub : well_ordered s None ub -> well_ordered (remove_min s) (min s) ub.
Proof.
elim: s ub => [//|l IHl x r _ h]/= ub /andP[]/andP[] xub /[dup] lwo' {}/IHl + rwo.
case: l lwo' => [//|ll lx lr lh] lwo' lwo.
rewrite well_ordered_bal lwo rwo/= xub.
move: (lwo') => /[dup] /well_orderedW lwoN /well_ordered_ubP-/(_ lx); mp => [|lxx].
  by rewrite /= eqxx.
move: (minP (x:=lx) lwoN); mp => [|mlx]; first by rewrite /= eqxx.
by move: (leo_lto_trans mlx lxx) => /= ->.
Qed.

Lemma mem_remove_min x s : well_ordered s None None -> mem x (remove_min s) = (Some x != min s) && (mem x s).
Proof.
elim: s => [//|] l + sx r _ h.
case: l => [|ll lx lr lh IHl swo].
  move=> _ /= rwo; rewrite (inj_eq Some_inj) andb_orr andNb/= fun_if ifFb -leNgt eq_sym andbA -lt_neqAle andbC.
  by apply/esym/imply_andbl/implyP => /(well_ordered_lbP rwo).
rewrite [LHS]/= [X in _ = X && _]/= -/(remove_min (node ll lx lr lh)) -/(min (node ll lx lr lh)).
move: (node ll lx lr lh) IHl swo => l IHl swo.
rewrite mem_node// mem_bal; last first.
  move: swo => /= /andP[] lwo rwo.
  rewrite well_ordered_bal rwo/= andbT; apply/(well_orderedWl (lb:=min l)) => //.
  exact/well_ordered_remove_min.
move: swo => /= /andP[] /[dup] lwo /well_orderedW lwoN rwo.
rewrite IHl// 2!andb_orr; (congr (_ || _ || _);
    rewrite andbC; apply/esym/imply_andbl/implyP) => [/eqP ->|xr];
    apply/negP => /eqP mE; move: (mem_min lwoN); rewrite -mE/= => /(well_ordered_ubP lwo)/=.
  by rewrite ltxx.
move: (well_ordered_lbP rwo xr) => /ltW. 
by rewrite leNgt => /negP.
Qed.

Lemma mem_remove_min' x s : well_ordered s None None -> mem x s = (Some x == min s) || (mem x (remove_min s)).
Proof.
move=> swo; rewrite (mem_remove_min _ swo) orb_andr orbN/= orbC.
case/boolP: (mem x s) => [//|] /= /negP xs; apply/esym/negP => /eqP xm.
by move: (mem_min swo); rewrite -xm.
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

Lemma height_merge l r : well_formed l -> well_formed r -> balanced r -> diffn (height l) (height r) <= 2 -> well_ordered r None None -> maxn (height l) (height r) <= (height (merge l r)) <= (maxn (height l) (height r)).+1.
Proof.
move=> lwf rwf rb lrd rwo; rewrite /merge; case: (min r) (mem_min rwo) => [m _|/= /eqP -> /=]; last by rewrite maxn0 leqnn leqnSn.
move: (height_remove_min rwf rb) (height_bal m lwf (well_formed_remove_min rwf)) => /andP[] mr rm /=.
case/boolP: (diffn (height l) (height (remove_min r)) <= 2) => [lrmd _|].
  by rewrite /bal lrmd/= ltnS -maxnSS !geq_max leq_maxl !leq_max leqnSn rm mr !orbT.
move: lrd; rewrite !geq_diffn !addn2 => /andP[] lr rl.
rewrite (leq_trans mr rl) andbT -ltnNge => /ltnW/ltnW {}rl.
by rewrite (maxn_idPl (leq_trans rm rl)) (maxn_idPl (ltnW rl)) ltnS => /andP[] -> ->.
Qed.

Lemma well_ordered_merge l r lb ub : well_ordered l lb (omin (min r) ub) -> well_ordered r lb ub -> well_ordered (merge l r) lb ub.
Proof.
move=> + /[dup] rwo /well_orderedW rwoN; move: (mem_min rwoN) (well_ordered_remove_min (well_orderedWl (lb':=None) erefl rwo)).
rewrite /merge; case: (min r) => [|//] m /= mr mwo lwo.
move: (well_ordered_lbP (well_orderedWr (ub':=None) erefl rwo) mr) (well_ordered_ubP (well_orderedWl (lb':=None) erefl rwo) mr) => lbm mub.
rewrite well_ordered_bal lbm mub mwo andbT/=.
move: lwo; congr well_ordered.
by case: ub mub {mwo rwo} => [|//] ub/= mub; rewrite minElt mub.
Qed.

Lemma mem_merge x l r : well_ordered l None (min r) -> well_ordered r None None -> mem x (merge l r) = (mem x l || mem x r).
Proof.
rewrite /merge => + rwo; case: (min r) (mem_min rwo) (mem_remove_min' x rwo) (well_ordered_remove_min rwo) => /= [m _|/eqP ->] xr mrwo lwo; last by rewrite orbF.
rewrite mem_bal; last by rewrite well_ordered_bal/= lwo/=.
by rewrite xr (inj_eq Some_inj) orbA; congr orb; exact: orbC.
Qed.

Lemma card_merge l r : well_ordered r None None -> card (merge l r) = card l + card r.
Proof.
rewrite /merge => rwo; case: (min r) (mem_min rwo) => [x xr|/eqP ->]; last by rewrite addn0.
rewrite card_bal card_remove_min -addnS; congr (_ + _).
by case: r rwo xr.
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

Lemma well_ordered_concat l r lb ub : well_ordered l lb (omin (min r) ub) -> well_ordered r lb ub -> well_ordered (concat l r) lb ub.
Proof.
move=> + /[dup] rwo /well_orderedW rwoN; move: (mem_min rwoN) (well_ordered_remove_min (well_orderedWl (lb':=None) erefl rwo)).
rewrite /concat; case: (min r) => [|//] m /= mr mwo lwo.
move: (well_ordered_lbP (well_orderedWr (ub':=None) erefl rwo) mr) (well_ordered_ubP (well_orderedWl (lb':=None) erefl rwo) mr) => lbm mub.
apply/well_ordered_join => //.
move: lwo; congr well_ordered.
by case: ub mub {mwo rwo} => [|//] ub/= mub; rewrite minElt mub.
Qed.

Lemma mem_concat x l r : well_ordered l None (min r) -> well_ordered r None None -> mem x (concat l r) = (mem x l || mem x r).
Proof.
rewrite /concat => + rwo; case: (min r) (mem_min rwo) (mem_remove_min' x rwo) (well_ordered_remove_min rwo) => /= [m _|/eqP ->] xr mrwo lwo; last by rewrite orbF.
rewrite mem_join// xr (inj_eq Some_inj) orbA; congr orb; exact: orbC.
Qed.

Lemma card_concat l r : well_ordered l None (min r) -> well_ordered r None None -> card (concat l r) = card l + card r.
Proof.
rewrite /concat => + rwo; case: (min r) (mem_min rwo) (well_ordered_remove_min rwo) => [x xr rwo' lwo|/eqP ->]; last by rewrite addn0.
rewrite card_join// card_remove_min -addnS; congr (_ + _).
by case: r lwo rwo rwo' xr.
Qed.

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

Lemma well_ordered_splitl x s lb : well_ordered s lb None -> well_ordered (split x s).1.1 lb (Some x).
Proof.
elim: s lb => [//|] l IHl sx r IHr h lb /= /andP[]/andP[]/andP[] lbsx _ lwo rwo.
case /comparable_ltgtP: (comparableT x sx) => [| |-> //] xsx.
  by case: (split x l) (IHl _ (well_orderedWr (ub':=None) erefl lwo)) => [[]].
case: (split x r) (IHr _ rwo) => [[/=]] sr _ _ srwo.
by apply/well_ordered_join.
Qed.

Lemma well_ordered_splitr x s ub : well_ordered s None ub -> well_ordered (split x s).2 (Some x) ub.
Proof.
elim: s ub => [//|] l IHl sx r IHr h ub /= /andP[]/andP[] sxub lwo rwo.
case /comparable_ltgtP: (comparableT x sx) => [| |-> //] xsx; last first.
  by case: (split x r) (IHr _ (well_orderedWl (lb':=None) erefl rwo)) => [[]].
case: (split x l) (IHl _ lwo) => [[/=]] _ _ sl slwo.
by apply/well_ordered_join.
Qed.

Lemma mem_split x y s : well_ordered s None None -> mem x s = ((split y s).1.2 && (x == y)) || mem x (split y s).1.1 || mem x (split y s).2.
Proof.
move=> swo.
elim: s swo (well_ordered_splitl y swo) (well_ordered_splitr y swo) => [//|] l IHl sx r IHr h swo; rewrite mem_node//.
move: swo => /= /andP[] lwo rwo.
case /comparable_ltgtP: (comparableT y sx) => [| |-> //] ysx.
  case: (split y l) (IHl (well_orderedW lwo)) (well_ordered_splitr y lwo) => [[/=]] sl sb sr {}IHl srwo slwo jwo.
  rewrite mem_join//; last exact: (well_orderedWl _ srwo).
  rewrite !orbA; congr orb.
  rewrite [RHS]orbC !orbA [RHS]orbC -!orbA; congr orb.
  by rewrite orbC; apply/IHl => //; apply: (well_orderedWr _ srwo).
case: (split y r) (IHr (well_orderedW rwo)) (well_ordered_splitl y rwo) => [[/=]] sl sb sr {}IHr slwo jwo srwo.
rewrite -!orbA [RHS]orbC.
rewrite mem_join//; last exact: (well_orderedWr _ slwo).
rewrite -!orbA; congr orb; congr orb.
by rewrite orbA orbC orbA; apply/IHr => //; apply: (well_orderedWl _ slwo).
Qed.

Lemma card_split x s : well_ordered s None None -> (split x s).1.2 + card (split x s).1.1 + card(split x s).2 = card s.
Proof.
move=> swo.
elim: s swo (well_ordered_splitl x swo) (well_ordered_splitr x swo) => [//|] l IHl sx r IHr h swo.
move: swo => /= /andP[] lwo rwo.
case /comparable_ltgtP: (comparableT x sx) => [| |-> //] xsx.
  case: (split x l) (IHl (well_orderedW lwo)) (well_ordered_splitr x lwo) => [[/=]] sl sb sr {}IHl srwo slwo jwo.
  rewrite card_join//; last exact: (well_orderedWl _ srwo).
  rewrite -!addnS addnA IHl//.
  exact: (well_orderedWr _ srwo).
case: (split x r) (IHr (well_orderedW rwo)) (well_ordered_splitl x rwo) => [[/=]] sl sb sr {}IHr slwo jwo srwo.
rewrite card_join//; last exact: (well_orderedWr _ slwo).
rewrite -!addSn addnA [sb + _]addnC -[_ + sb + _]addnA -addnA IHr//.
exact: (well_orderedWl _ slwo).
Qed.

Lemma well_formed_remove x s : well_formed s -> well_formed (remove x s).
Proof.
elim: s => [//|] l IHl sx r IHr h /= /andP[]/andP[] _ {h} lwf rwf.
case /comparable_ltgtP: (comparableT x sx) => _.
- by apply/well_formed_bal => //; apply/IHl.
- by apply/well_formed_bal => //; apply/IHr.
- exact/well_formed_merge.
Qed.

Lemma balanced_height_remove x s : well_formed s -> balanced s -> well_ordered s None None -> balanced (remove x s) && (height s <= (height (remove x s)).+1 <= (height s).+1).
Proof.
elim: s => [//|] l IHl sx r IHr h/= /andP[]/andP[] /eqP -> {h} lwf rwf /andP[]/andP[] lrd lb rb /andP[] /well_orderedW lwo /well_orderedW rwo.
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

Lemma well_ordered_remove x s lb ub : well_ordered s lb ub -> well_ordered (remove x s) lb ub.
Proof.
elim: s lb ub => [//|] l IHl sx r IHr h/= lb ub /andP[]/andP[]/andP[] lbsx sxub lwo rwo.
case /comparable_ltgtP: (comparableT x sx) => _.
- rewrite well_ordered_bal lbsx/= sxub rwo/= andbT.
  by apply/IHl.
- rewrite well_ordered_bal lbsx/= sxub lwo/=.
  by apply/IHr.
- apply/well_ordered_merge; last first.
    refine (well_orderedWl _ rwo) => /=.
    by case: lb {lwo lbsx} (ltoW lbsx).
  refine (well_orderedWr _ lwo) => /=.
  case: (min r) (mem_min (well_orderedW rwo)) => /= [m mr|_]; last first.
    by case: ub {rwo} sxub => [|//] ub /ltW.
  move: (well_ordered_lbP (well_orderedWr (ub':=None) erefl rwo) mr) => /= /ltW sxm.
  case: ub {rwo} sxub => [|//] ub /= /ltW sxub.
  by rewrite le_min sxm sxub.
Qed.

Lemma mem_remove x y s : well_ordered s None None -> mem x (remove y s) = (x != y) && mem x s.
Proof.
elim: s => [/= _|l IHl sx r IHr h swo]; first exact/esym/andbF.
rewrite mem_node//; move: swo => /= /andP[] /[dup] lwo /well_orderedW {}/IHl xl /[dup] rwo /well_orderedW {}/IHr xr.
case /comparable_ltgtP: (comparableT y sx) => [ysx|sxy|sxy].
- rewrite mem_bal; last first.
    by rewrite well_ordered_bal/= rwo andbT; apply/well_ordered_remove.
  rewrite !andb_orr; congr (_ || _ || _) => //; rewrite andbC; apply/esym/imply_andbl/implyP.
    by move: ysx; rewrite lt_def => /andP[] sxy _ /eqP ->.
  by move=> /(well_ordered_lbP rwo) /(lt_trans ysx); rewrite lt_def => /andP[].
- rewrite mem_bal; last first.
    by rewrite well_ordered_bal/= lwo; apply/well_ordered_remove.
  rewrite !andb_orr; congr (_ || _ || _) => //; rewrite andbC; apply/esym/imply_andbl/implyP.
    by move: sxy; rewrite lt_def eq_sym => /andP[] sxy _ /eqP ->.
  move=> /(well_ordered_ubP lwo)/= xsx. 
  by move: (lt_trans xsx sxy); rewrite lt_def eq_sym => /andP[].
- subst y; have rwo' := well_orderedW rwo; rewrite mem_merge//; last first.
    refine (well_orderedWr _ lwo) => /=.
    case: (min r) (mem_min (well_orderedW rwo)) => [|//] m/= mr.
    by move: (well_ordered_lbP rwo mr) => /= /ltW.
  rewrite andbC 2!andb_orl andbN/=; congr orb; apply/esym/imply_andbl/implyP.
    move=> /(well_ordered_ubP lwo)/=.
    by rewrite lt_def eq_sym => /andP[].
  move=> /(well_ordered_lbP rwo)/=.
  by rewrite lt_def eq_sym => /andP[].
Qed.

Lemma card_remove x s : well_ordered s None None -> card (remove x s) = card s - (mem x s).
Proof.
elim: s => [//|] l IHl sx r IHr h/= /andP[] /well_orderedW lwo /well_orderedW rwo.
case /comparable_ltgtP: (comparableT x sx) => [xsx|sxx|->]/=.
- rewrite card_bal IHl// -!addnS subDnCA; first by rewrite addnC.
  by case: l {IHl lwo} => [//|] ll lx lr lh; case: (mem x _).
- rewrite card_bal IHr// -!addSn [in RHS]addnC subDnCA//.
  by case: r {IHr rwo} => [//|] rl rx rr rh; case: (mem x _).
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

Lemma well_ordered_union_subdef n s t lb ub : well_ordered s lb ub -> well_ordered t lb ub -> well_ordered (union_subdef n s t) lb ub.
Proof.
rewrite /union_subdef; elim: n s t lb ub => [//|] n IHn s t lb ub.
case: s => [//|] sl sx sr sh swo.
case: t => [//|] tl tx tr th two.
case: (th <= sh).
  case: (th == 1); first by apply/well_ordered_add; move: two => //= /andP[]/andP[]/andP[].
  case: (split _ _)
    (well_ordered_splitl sx (well_orderedWr (ub':=None) erefl two))
    (well_ordered_splitr sx (well_orderedWl (lb':=None) erefl two))
    => [[stl /= _]] str stlwo strwo.
  move: swo => /= /andP[]/andP[]/andP[] lbsx sxub slwo srwo.
  by apply/well_ordered_join => //; apply/IHn.
case: (sh == 1); first by apply/well_ordered_add; move: swo => //= /andP[]/andP[]/andP[].
case: (split _ _)
  (well_ordered_splitl tx (well_orderedWr (ub':=None) erefl swo))
  (well_ordered_splitr tx (well_orderedWl (lb':=None) erefl swo))
  => [[ssl /= _]] ssr sslwo ssrwo.
move: two => /= /andP[]/andP[]/andP[] lbtx txub tlwo trwo.
by apply/well_ordered_join => //; apply/IHn.
Qed.

Lemma mem_union_subdef x n s t : well_formed s -> well_formed t -> balanced s -> balanced t -> well_ordered s None None -> well_ordered t None None -> (height s + height t <= n) -> mem x (union_subdef n s t) = (mem x s) || mem x t.
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
  + exact (well_orderedW stlwo).
  + exact (well_orderedW slwo).
  rewrite IHn//; last first.
  + move: shE stn => /= ->; rewrite addSn ltnS; refine (leq_trans _).
    by apply/leq_add => //; apply/leq_maxr.
  + exact (well_orderedW strwo).
  + exact (well_orderedW srwo).
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
+ exact (well_orderedW tlwo).
+ exact (well_orderedW sslwo).
rewrite IHn//; last first.
+ move: thE stn => /= ->; rewrite addnS ltnS; refine (leq_trans _).
  by apply/leq_add => //; apply/leq_maxr.
+ exact (well_orderedW trwo).
+ exact (well_orderedW ssrwo).
rewrite -!orbA; apply/orb_id2l => /negPf ->.
rewrite andbF/= orbC -orbA; congr orb.
by rewrite orbA orbC orbA orbC orbA.
Qed.

Lemma well_formed_union s t : well_formed s -> well_formed t -> well_formed (union s t).
Proof. exact/well_formed_union_subdef. Qed.

Lemma balanced_union s t : well_formed s -> well_formed t -> balanced s -> balanced t -> balanced (union s t).
Proof. exact/balanced_union_subdef. Qed.

Lemma well_ordered_union s t lb ub : well_ordered s lb ub -> well_ordered t lb ub -> well_ordered (union s t) lb ub.
Proof. exact/well_ordered_union_subdef. Qed.

Lemma mem_union x s t : well_formed s -> well_formed t -> balanced s -> balanced t -> well_ordered s None None -> well_ordered t None None -> mem x (union s t) = (mem x s) || mem x t.
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

Lemma well_ordered_mem_inter x s t lb ub : well_ordered s lb ub -> well_ordered t lb ub -> well_ordered (inter s t) lb ub && (mem x (inter s t) == mem x s && mem x t).
Proof.
elim: s t lb ub => [//|] l IHl sx r IHr h t lb ub swo.
rewrite mem_node ?(well_orderedW swo)//; move: swo => /= /andP[]/andP[]/andP[] lbsx sxub lwo rwo two.
case: (split sx t) (well_ordered_splitl sx (well_orderedWr (ub':=None) erefl two)) (well_ordered_splitr sx (well_orderedWl (lb':=None) erefl two)) (mem_split x sx (well_orderedW two)) => [[tl /= +]] tr tlwo trwo.
case => /= xt.
  move: IHl IHr => /(_ tl lb (Some sx) lwo tlwo) /andP[] ltlwo /eqP xltl
    /(_ tr (Some sx) ub rwo trwo) /andP[] rtrwo /eqP xrtr.
  apply/andP; split; first exact/well_ordered_join.
  rewrite mem_join//; first last.
  - exact/(well_orderedWr _ rtrwo).
  - exact/(well_orderedWl _ ltlwo).
  apply/eqP; rewrite xltl xrtr xt -!orbA -orb_andr; congr orb.
  rewrite andb_orl !andb_orr !orbA; congr orb; rewrite -orbA -[LHS]orbF; congr orb.
  apply/esym/Bool.orb_false_intro; apply/negP => /andP[].
    move=> /(well_ordered_ubP (well_orderedWl (lb':=None) erefl lwo))/= xsx.
    move=> /(well_ordered_lbP (well_orderedWr (ub':=None) erefl trwo))/= /(lt_trans xsx).
    by rewrite ltxx.
  move=> /(well_ordered_lbP (well_orderedWr (ub':=None) erefl rwo))/= sxx.
  move=> /(well_ordered_ubP (well_orderedWl (lb':=None) erefl tlwo))/= /(lt_trans sxx).
  by rewrite ltxx.
move: IHl IHr => /(_ tl lb (Some sx) lwo tlwo) /andP[] ltlwo /eqP xltl
  /(_ tr (Some sx) ub rwo trwo) /andP[] rtrwo /eqP xrtr.
have sxm: leo (Some sx) (min (inter r tr)).
  case: (min _) (mem_min (well_orderedW rtrwo)) => /= [m|//].
  by move=> /(well_ordered_lbP (well_orderedWr (ub':=None) erefl rtrwo))/= /ltW.
apply/andP; split.
  apply/well_ordered_concat => //; last first.
    apply/(well_orderedWl _ rtrwo) => /=.
    by case: lb lbsx {lwo two tlwo ltlwo} => [|//] lb/= /ltW.
  apply/(well_orderedWr _ ltlwo) => /=.
  case: (min _) sxm => /= [m sxm|_]; last first.
    by case: ub sxub {rwo two trwo rtrwo} => [|//] ub/= /ltW.
  case: ub sxub {rwo two trwo rtrwo} => [|//] ub/= /ltW sxub.
  by rewrite le_min sxm sxub.
rewrite mem_concat; first last.
- exact/(well_orderedW rtrwo).
- exact/(well_orderedWr _ (well_orderedWl _ ltlwo)).
apply/eqP; rewrite xltl xrtr xt.
case/boolP: (mem x l) => [xl|_]/=.
  rewrite orbT/= andbC; congr orb; apply/imply_andbl/implyP.
  move: (well_ordered_ubP (well_orderedWl (lb':=None) erefl lwo) xl) => /= xsx.
  move=> /(well_ordered_lbP (well_orderedWr (ub':=None) erefl trwo))/= /(lt_trans xsx).
  by rewrite ltxx.
rewrite orbF; case/boolP: (mem x r) => [xr|_]/=.
  rewrite orbT/= orbC; apply/esym/imply_orbl/implyP.
  move: (well_ordered_lbP (well_orderedWr (ub':=None) erefl rwo) xr) => /= sxx.
  move=> /(well_ordered_ubP (well_orderedWl (lb':=None) erefl tlwo))/= /(lt_trans sxx).
  by rewrite ltxx.
rewrite orbF; apply/esym/negP => /andP[] /eqP xsx /orP; case.
  move=> /(well_ordered_ubP (well_orderedWl (lb':=None) erefl tlwo))/=.
  by rewrite xsx ltxx.
move=> /(well_ordered_lbP (well_orderedWr (ub':=None) erefl trwo))/=.
by rewrite xsx ltxx.
Qed.

Lemma well_ordered_inter s t lb ub : well_ordered s lb ub -> well_ordered t lb ub -> well_ordered (inter s t) lb ub.
Proof.
by case: s => [//|] l x r h swo /(well_ordered_mem_inter x swo) => /andP[].
Qed.

Lemma mem_inter x s t : well_ordered s None None -> well_ordered t None None -> mem x (inter s t) = mem x s && mem x t.
Proof. by move=> swo /(well_ordered_mem_inter x swo) => /andP[] _ /eqP. Qed.

Lemma inters0 s : inter s (leaf elt) = (leaf elt).
Proof. by elim: s => [//|l IHl x r IHr h]/=; rewrite IHl IHr. Qed.

Lemma cardUI s t : well_formed s -> well_formed t -> card (union s t) + card (inter s t) = card s + card t.
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
    case /comparable_ltgtP: (comparableT sx tx) => //; rewrite !inters0 /=. 


Lemma split_bisP x s : well_ordered s None None ->
  match split_bis x s with
  | None => mem x s
  | Some (l, r) => (l == (split x s).1.1) && (r tt == (split x s).2) && ((split x s).1.2 == false)
  end.
Proof.
elim: s => [//|] l IHl sx r IHr h /= /andP[] lwo rwo.
case /comparable_ltgtP: (comparableT x sx) => // [xsx|sxx].
  case: (split_bis x l) (IHl (well_orderedW lwo)) => [|//] [sl sr]/= /andP[]/andP[] /eqP -> /eqP ->.
  case: (split x l) => [[]]/= ssl ssb ssr ->.
  by rewrite !eqxx.
case: (split_bis x r) (IHr (well_orderedW rwo)) => [|//] [sl sr]/= /andP[]/andP[] /eqP -> /eqP ->.
case: (split x r) => [[]]/= ssl ssb ssr ->.
by rewrite !eqxx.
Qed.

Lemma disjointP s t : well_ordered s None None -> well_ordered t None None -> reflect (forall x, ~~ (mem x s && mem x t)) (disjoint s t).
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
  move: (swo) stlwo strwo => /= /andP[] /well_orderedW lwo /well_orderedW rwo /well_orderedW stlwo /well_orderedW strwo.
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
  move: lstl => /= /IHl-/(_ (well_orderedW lwo) (well_orderedW stlwo) x).
  rewrite xstl andbT => /negPf ->; rewrite orbF.
  move: (well_ordered_ubP stlwo xstl) => /= xsx.
  move=> /orP; case=> [/eqP xsxE|/(well_ordered_lbP rwo)/(lt_trans xsx)].
    by move: xsx; rewrite xsxE ltxx.
  by rewrite ltxx.
move: rstr => /= /IHr-/(_ (well_orderedW rwo) (well_orderedW strwo) x).
rewrite xstr andbT => /negPf ->; rewrite orbF.
move: (well_ordered_lbP strwo xstr) => /= sxx.
move=> /orP; case=> [/eqP xsx|/(well_ordered_ubP lwo)/(lt_trans sxx)].
  by move: sxx; rewrite xsx ltxx.
by rewrite ltxx.
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

Lemma well_ordered_mem_diff x s t lb ub : well_ordered s lb ub -> well_ordered t lb ub -> well_ordered (diff s t) lb ub && (mem x (diff s t) == mem x s && ~~ mem x t).
Proof.
elim: s t lb ub => [//|] l IHl sx r IHr h t lb ub swo.
rewrite mem_node ?(well_orderedW swo)//.
case: t => [//|tl tx tr th] two.
  by rewrite /diff swo mem_node ?(well_orderedW swo)// andbT/=.
rewrite [diff _ _]/= -/(split sx (node tl tx tr th)).
move: (node tl tx tr th) two swo => t two/= /andP[]/andP[]/andP[] lbsx sxub lwo rwo.
case: (split sx t) (well_ordered_splitl sx (well_orderedWr (ub':=None) erefl two)) (well_ordered_splitr sx (well_orderedWl (lb':=None) erefl two)) (mem_split x sx (well_orderedW two)) => [[stl /= +]] str stlwo strwo.
case => /= xt; last first.
  move: IHl IHr => /(_ stl lb (Some sx) lwo stlwo) /andP[] ltlwo /eqP xltl
    /(_ str (Some sx) ub rwo strwo) /andP[] rtrwo /eqP xrtr.
  apply/andP; split; first exact/well_ordered_join.
  rewrite mem_join//; first last.
  - exact/(well_orderedWr _ rtrwo).
  - exact/(well_orderedWl _ ltlwo).
  apply/eqP; rewrite xltl xrtr xt. 
  case/boolP: (mem x stl) => [/(well_ordered_ubP (well_orderedWl (lb':=None) erefl stlwo))/=|_].
    have [->|_] := eqVneq x sx; first by rewrite ltxx.
    case/boolP: (mem x r) => [/(well_ordered_lbP (well_orderedWr (ub':=None) erefl rwo))/= sxx /(lt_trans sxx)|_].
      by rewrite ltxx.
    case/boolP: (mem x str) => [/(well_ordered_lbP (well_orderedWr (ub':=None) erefl strwo))/= sxx /(lt_trans sxx)|_ _].
      by rewrite ltxx.
    by rewrite /= !orbF.
  case/boolP: (mem x str) => [/(well_ordered_lbP (well_orderedWr (ub':=None) erefl strwo))/=|_]; last by rewrite !andbT.
  have [->|_] := eqVneq x sx; first by rewrite ltxx.
  case/boolP: (mem x l) => [/(well_ordered_ubP (well_orderedWl (lb':=None) erefl lwo))/= xsx /(lt_trans xsx)|//].
  by rewrite ltxx.
move: IHl IHr => /(_ stl lb (Some sx) lwo stlwo) /andP[] ltlwo /eqP xltl
  /(_ str (Some sx) ub rwo strwo) /andP[] rtrwo /eqP xrtr.
have sxm: leo (Some sx) (min (diff r str)).
  case: (min _) (mem_min (well_orderedW rtrwo)) => /= [m|//].
  by move=> /(well_ordered_lbP (well_orderedWr (ub':=None) erefl rtrwo))/= /ltW.
apply/andP; split.
  apply/well_ordered_concat => //; last first.
    apply/(well_orderedWl _ rtrwo) => /=.
    by case: lb lbsx {lwo two stlwo ltlwo} => [|//] lb/= /ltW.
  apply/(well_orderedWr _ ltlwo) => /=.
  case: (min _) sxm => /= [m sxm|_]; last first.
    by case: ub sxub {rwo two strwo rtrwo} => [|//] ub/= /ltW.
  case: ub sxub {rwo two strwo rtrwo} => [|//] ub/= /ltW sxub.
  by rewrite le_min sxm sxub.
rewrite mem_concat; first last.
- exact/(well_orderedW rtrwo).
- exact/(well_orderedWr _ (well_orderedWl _ ltlwo)).
apply/eqP; rewrite xltl xrtr xt.
move: lwo rwo => /(well_orderedWl (lb':=None) erefl)/well_ordered_ubP lwo /(well_orderedWr (ub':=None) erefl)/well_ordered_lbP rwo.
have [->|_]/= := eqVneq x sx.
  apply/negP => /orP; case=> /andP[].
    by move=> /lwo => /=; rewrite ltxx.
  by move=> /rwo => /=; rewrite ltxx.
case/boolP: (mem x l) => [/lwo/= xsx|_].
  case/boolP: (mem x r) => [/rwo /(lt_trans xsx)|_]/=; first by rewrite ltxx.
  case/boolP: (mem x str) => [/(well_ordered_lbP (well_orderedWr (ub':=None) erefl strwo))/(lt_trans xsx)|_]/=.
    by rewrite ltxx.
  by rewrite !orbF.
case/boolP: (mem x r) => [/rwo/= sxx|//].
  case/boolP: (mem x stl) => [/(well_ordered_ubP (well_orderedWl (lb':=None) erefl stlwo))/(lt_trans sxx)|//]/=.
  by rewrite ltxx.
Qed.

Lemma well_ordered_diff s t lb ub : well_ordered s lb ub -> well_ordered t lb ub -> well_ordered (diff s t) lb ub.
Proof.
by case: s => [//|] l x r h swo /(well_ordered_mem_diff x swo) => /andP[].
Qed.

Lemma mem_diff x s t : well_ordered s None None -> well_ordered t None None -> mem x (diff s t) = mem x s && ~~ mem x t.
Proof. by move=> swo /(well_ordered_mem_diff x swo) => /andP[] _ /eqP. Qed.

Lemma subset_subdefP n s t : well_formed s -> well_formed t -> well_ordered s None None -> well_ordered t None None -> height s + height t <= n -> reflect (forall x, mem x s -> mem x t) (subset_subdef n s t).
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
move: (swo); rewrite [well_ordered _ _ _]/= => /andP[] /[dup] slwo /well_orderedW slwo' /[dup] srwo /well_orderedW srwo'.
move: (two); rewrite [well_ordered _ _ _]/= => /andP[] /[dup] tlwo /well_orderedW tlwo' /[dup] trwo /well_orderedW trwo'.
have sl0wo : well_ordered (node sl sx (leaf elt) 0) None None
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
    move/orP: xs; case => [/eqP -> //|/(well_ordered_ubP slwo)/= xsx].
    exact/(lt_trans xsx sxtx).
  move=> /orP; case=> [/orP|]; [case=> [/eqP xtxE|//]|].
    by move: xtx; rewrite xtxE ltxx.
  by move=> /(well_ordered_lbP trwo)/= /(lt_trans xtx); rewrite ltxx.
- move=> /IHn-/(_ slwo' two sltn) IHl /IHn-/(_ srwo trwo' sr0trn) IHr x.
  move: (IHl x) (IHr x); rewrite mem_node// mem_node// mem_node//= orbF => {}IHl {}IHr.
  by rewrite orbAC => /orP; case=> [/IHr|/IHl] -> //; rewrite orbT.
- move=> IH; split; apply/IHn => // x; rewrite mem_node//.
    by move=> xl; move: (IH x); rewrite mem_node// mem_node// xl orbT; apply.
  rewrite orbF => xs; move: (IH x); rewrite mem_node// mem_node// orbAC xs/= => /(_ erefl) /orP.
  have txx: (tx < x)%O.
    move/orP: xs; case => [/eqP -> //|/(well_ordered_lbP srwo)/= sxx].
    exact/(lt_trans sxtx sxx).
  case=> // /orP; case=> [/eqP xtxE|//].
    by move: txx; rewrite xtxE ltxx.
  by move=> /(well_ordered_ubP tlwo)/= /(lt_trans txx); rewrite ltxx.
- move=> /IHn-/(_ slwo' tlwo' sltln) IHl /IHn-/(_ srwo' trwo' srtrn) IHr x.
  move: (IHl x) (IHr x); rewrite mem_node// mem_node// => {}IHl {}IHr.
  by rewrite sxtx => /orP; case=> [/orP|/IHr ->]; [case=> [-> //| /IHl ->]|]; rewrite orbT.
- subst tx.
  move=> IH; split; apply/IHn => // x.
    move=> /[dup] /(well_ordered_ubP slwo)/= xsx xl; move: (IH x); rewrite mem_node// mem_node// xl orbT => /(_ erefl)/orP.
    case=> [/orP|]; [case=> [/eqP xsxE|//]|].
      by move: xsx; rewrite xsxE ltxx.
    by move=> /(well_ordered_lbP trwo)/= /(lt_trans xsx); rewrite ltxx.
  move=> /[dup] /(well_ordered_lbP srwo)/= sxx xr; move: (IH x); rewrite mem_node// mem_node// xr orbT => /(_ erefl)/orP.
  case=> [/orP|//]; case=> [/eqP xsxE|].
    by move: sxx; rewrite xsxE ltxx.
  by move=> /(well_ordered_ubP tlwo)/= /(lt_trans sxx); rewrite ltxx.
Qed.

Lemma subsetP s t : well_formed s -> well_formed t -> well_ordered s None None -> well_ordered t None None -> reflect (forall x, mem x s -> mem x t) (subset s t).
Proof. by move=> swf twf swo two; apply/subset_subdefP. Qed.

Lemma allP (p : pred elt) s : well_ordered s None None -> reflect (forall x, mem x s -> p x) (all p s).
Proof.
elim: s => [|l IHl x r IHr h] swo; apply/(iffP idP) => // [|mP/=];
  move: (swo) => /= /andP[]
    /well_orderedW {}/IHl IHl
    /well_orderedW {}/IHr IHr.
  move=> /andP[]/andP[] px {}/IHl lP {}/IHr rP y.
  by case /comparable_ltgtP: (comparableT x y) => /= [_|_|<-]//;
    [apply/rP|apply/lP].
apply/andP; split; [apply/andP; split|].
- by apply/mP; rewrite /= eqxx.
- by apply /IHl => y yl; apply/mP; rewrite mem_node// yl orbT.
- by apply /IHr => y yr; apply/mP; rewrite mem_node// yr !orbT.
Qed.

Lemma hasP (p : pred elt) s : well_ordered s None None -> reflect (exists x, mem x s && p x) (has p s).
Proof.
elim: s => [|l IHl x r IHr h] swo; apply/(iffP idP) => [//|[]// y];
  move: (swo); rewrite [has _ _]/= [well_ordered _ _ _]/= => /andP[]
    /well_orderedW lwo /well_orderedW rwo.
  move=> /orP; case=>[/orP|/(IHr rwo) [y /andP[] yr py]]; [case=> [px|/(IHl lwo) [y /andP[] yl py]]|].
  - by exists x; rewrite /= eqxx.
  - by exists y; rewrite mem_node// yl orbT.
  - by exists y; rewrite mem_node// yr orbT.
rewrite mem_node// => /andP[] /orP + py; case=> [/orP|yr]; [case=> [/eqP <-|yl]|].
- by rewrite py.
- by apply/orP; left; apply/orP; right; apply/(IHl lwo); exists y; rewrite yl.
- by apply/orP; right; apply/(IHr rwo); exists y; rewrite yr.
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

Lemma well_ordered_partition p s lb ub : well_ordered s lb ub -> well_ordered (partition p s).1 lb ub && well_ordered (partition p s).2 lb ub.
Proof.
elim: s lb ub => [//|] l IHl x r IHr h lb ub/= /andP[]/andP[]/andP[] lbx xub {}/IHl + {}/IHr.
move: (partition p l) => [pll plr]/= /andP[] pllwo plrwo.
move: (partition p r) => [prl prr]/= /andP[] prlwo prrwo.
case: (p x) => /=; apply/andP; split.
- exact/well_ordered_join.
- apply/well_ordered_concat; last first.
    apply/(well_orderedWl _ prrwo).
    by case: lb lbx {pllwo plrwo} => [|//] lb/= /ltW.
  move: (min prr) (mem_min (well_orderedW prrwo)) => [m|_]/=; last first.
    apply/(well_orderedWr _ plrwo).
    by case: ub xub {prlwo prrwo} => [|//] rb/= /ltW.
  move=> /[dup] /(well_ordered_ubP (well_orderedWl (lb':=None) erefl prrwo)) + /(well_ordered_lbP (well_orderedWr (ub':=None) erefl prrwo)) /ltoW xm.
  by case: ub xub {prlwo prrwo} => [ub xub /ltW mub|_ _]/=; [rewrite (min_idPl mub)|]; apply/(well_orderedWr _ plrwo).
- apply/well_ordered_concat; last first.
    apply/(well_orderedWl _ prlwo).
    by case: lb lbx {pllwo plrwo} => [|//] lb/= /ltW.
  move: (min prl) (mem_min (well_orderedW prlwo)) => [m|_]/=; last first.
    apply/(well_orderedWr _ pllwo).
    by case: ub xub {prlwo prrwo} => [|//] rb/= /ltW.
  move=> /[dup] /(well_ordered_ubP (well_orderedWl (lb':=None) erefl prlwo)) + /(well_ordered_lbP (well_orderedWr (ub':=None) erefl prlwo)) /ltoW xm.
  by case: ub xub {prrwo prlwo} => [ub xub /ltW mub|_ _]/=; [rewrite (min_idPl mub)|]; apply/(well_orderedWr _ pllwo).
- exact/well_ordered_join.
Qed.

Lemma mem_partition x p s : well_ordered s None None -> (mem x (partition p s).1 == p x && mem x s) && (mem x (partition p s).2 == ~~ p x && mem x s).
Proof.
elim: s => [|l IHl sx r IHr h swo].
  by rewrite !andbF.
rewrite mem_node//; move: (swo) => /= /andP[] lwo rwo.
move: (partition p l) (well_ordered_partition p lwo) {IHl} (IHl (well_orderedW lwo)) => [pll plr]/= /andP[] pllwo plrwo /andP[] /eqP xpll /eqP xplr.
move: (partition p r) (well_ordered_partition p rwo) {IHr} (IHr (well_orderedW rwo)) => [prl prr]/= /andP[] prlwo prrwo /andP[] /eqP xprl /eqP xprr.
case/boolP: (p sx) => [|/negPf] /= psx; apply/andP; split; apply/eqP.
- by rewrite mem_join// xpll xprl 2!andb_orr andb_eq psx.
- rewrite mem_concat.
  + by rewrite xplr xprr 2!andb_orr (andb_eq (fun x => ~~ p x)) psx.
  + move: (min prr) (mem_min (well_orderedW prrwo)) => [m|_]/=; last first.
      exact/(well_orderedW plrwo).
    move=> /(well_ordered_lbP (well_orderedWr (ub':=None) erefl prrwo)) /ltoW xm.
    exact/(well_orderedWr _ plrwo).
  + exact/(well_orderedW prrwo).
- rewrite mem_concat.
  + by rewrite xpll xprl 2!andb_orr andb_eq psx.
  + move: (min prl) (mem_min (well_orderedW prlwo)) => [m|_]/=; last first.
      exact/(well_orderedW pllwo).
    move=> /(well_ordered_lbP (well_orderedWr (ub':=None) erefl prlwo)) /ltoW xm.
    exact/(well_orderedWr _ pllwo).
  + exact/(well_orderedW prlwo).
- by rewrite mem_join// xplr xprr 2!andb_orr (andb_eq (fun x => ~~ p x)) psx.
Qed.





End Subdef.

Fixpoint well_formed t :=
  match t with
  | leaf => true
  | node l r h _ => (h == (maxn (height l) (height r)).+1) && (well_formed l) && (well_formed r)
  end.

Fixpoint balanced t :=
  match t with
  | leaf => true
  | node l r h _ => (diffn (height l) (height r) <= 2) && (balanced l) && (balanced r)
  end.

Fixpoint well_ordered_subdef t lb ub := 
  match t with
  | leaf => true
  | node l r _ x => (map_or (fun lb => lb < x)%O true lb) && (map_or (fun ub => x < ub) true ub)%O && (well_ordered_subdef l lb (Some x)) && (well_ordered_subdef r (Some x) ub)
  end.

Lemma well_ordered_subdefWl t lb lb' ub : map_or (fun lb' => map_or (>= lb')%O false lb) true lb'-> well_ordered_subdef t lb ub -> well_ordered_subdef t lb' ub.
Proof.
elim: t lb lb' ub => [//|] l IHl r IHr/= _ x lb lb' ub lb'lb
    /andP[]/andP[]/andP[] lbx xub lwo rwo.
rewrite xub andbT.
apply/andP; split; last first.
  apply/IHr; last exact: rwo.
  exact: le_refl.
apply/andP; split; last by apply/IHl; last exact: lwo.
by case: lb' lb'lb lbx => [|//]lb'; case: lb {lwo} => [|//]lb /=; apply: le_lt_trans.
Qed.

Lemma well_ordered_subdefWr t lb ub ub' : map_or (fun ub' => map_or (<= ub')%O false ub) true ub' -> well_ordered_subdef t lb ub -> well_ordered_subdef t lb ub'.
Proof.
elim: t lb ub ub' => [//|] l IHl r IHr/= _ x lb ub ub' ubub'
    /andP[]/andP[]/andP[] lbx xub lwo rwo.
rewrite lbx/=.
apply/andP; split; last by apply/IHr; last exact: rwo.
apply/andP; split; last first.
  apply/IHl; last exact: lwo.
  exact: le_refl.
by case: ub' ubub' xub => [|//]ub'; case: ub {rwo} => [|//]ub /= /[swap]; apply: lt_le_trans.
Qed.

Definition well_ordered t := well_ordered_subdef t None None .
Arguments well_ordered : simpl never.

Definition is_avl t := (well_formed t) && (balanced t) && (well_ordered t).

Definition t := {x | is_avl x}.

Definition empty : t := exist _ leaf erefl.

Definition singleton x : t := exist _ (node leaf leaf 1 x) erefl.

Definition height (t : t) := height (val t).
Arguments height : simpl never.

Fixpoint size_subdef t :=
  match t with
  | leaf => 0
  | node l r _ _ => ((size_subdef l) + size_subdef r).+1
  end.

Definition size (t : t) := size_subdef (val t).
Arguments size : simpl never.

Fixpoint all_subdef (P : pred elt) t :=
  match t with
  | leaf => true
  | node l r _ x => (P x) && (all_subdef P l) && (all_subdef P r)
  end.

Definition all P (t : t) := all_subdef P (val t).
Arguments all : simpl never.

Fixpoint mem_subdef (x : elt) t :=
  match t with
  | node l r _ y => (x == y) || (if (x < y)%O then mem_subdef x l else mem_subdef x r)
  | leaf => false
  end.

Definition mem x (t : t) := mem_subdef x (val t).
Arguments mem : simpl never.

Lemma mem_well_ordered_subdef x t lb ub : well_ordered_subdef t lb ub -> mem_subdef x t -> map_or (< x)%O true lb /\ map_or (> x)%O true ub.
Proof.
elim: t lb ub => [//|] l IHl r IHr h tx lb ub/= /andP[]/andP[]/andP[] lbtx txub /IHl {}IHl /IHr {}IHr.
case /comparable_ltgtP: (comparableT x tx) => [_ /= /IHl/= [lbx xtx]|_ /= /IHr/= [txx xub]|-> //]; split=> //.
  by case: ub txub {IHr} => [|//]ub/=; apply/lt_trans.
by case: lb lbtx {IHl} => [|//]lb/= lbtx; apply: (lt_trans lbtx).
Qed.

Fixpoint opp_subdef (t : t_subdef) :=
  match t with
  | leaf => leaf
  | node l r h x => node (opp_subdef r) (opp_subdef l) h x
  end.

Lemma height_opp_subdef t : height (opp_subdef t) = height t.
Proof. by case: t. Qed.

Lemma well_formed_opp_subdef t : well_formed (opp_subdef t) = well_formed t.
Proof.
by elim: t => //= l -> r -> h _; rewrite 2!height_opp_subdef -2!andbA [well_formed _ && _]andbC maxnC.
Qed.

Lemma balanced_opp_subdef t : balanced (opp_subdef t) = balanced t.
Proof.
by elim: t => //= l -> r -> _ _; rewrite 2!height_opp_subdef -2!andbA [balanced _ && _]andbC diffnC.
Qed.

(* We assume t is well_heighted, so a lot of `leaf` cases are discarded. *)
Definition balance_node t := (fun t =>
  match t with
  | leaf => t
  | node l r h x => if diffn (height r) (height l) <= 1 then t else
    if (height r).+1 < height l then
      match l with
      | leaf => t
      | node ll lr lh lx =>
        if height ll < height lr then
          match lr with
          | leaf => t
          | node lrl lrr lrh lrx => let hl := (maxn (height ll) (height lrl)).+1 in
            let hr := (maxn (height lrr) (height r)).+1 in
            node (node ll lrl hl lx) (node lrr r hr x) (maxn hl hr).+1 lrx
          end
        else let hr := (maxn (height lr) (height r)).+1 in
          node ll (node lr r hr x) (maxn (height ll) hr).+1 lx
      end
    else
      match r with
      | leaf => t
      | node rl rr rh rx =>
        if height rr < height rl then
          match rl with
          | leaf => t
          | node rll rlr rlh rlx => let hl := (maxn (height l) (height rll)).+1 in
            let hr := (maxn (height rlr) (height rr)).+1 in
            node (node l rll hl x) (node rlr rr hr rx) (maxn hl hr).+1 rlx
          end
        else let hl := (maxn (height l) (height rl)).+1 in
          node (node l rl hl x) rr (maxn hl (height rr)).+1 rx
      end
  end) t.
Arguments balance_node : simpl never.

Lemma balance_node_opp_subdef t : balance_node (opp_subdef t) = opp_subdef (balance_node t).
Proof.
case: t => //= l r h x; rewrite /balance_node !height_opp_subdef.
case: (leq_diffn1P _ _); case: (leq_diffn1P _ _) => // + _; last first.
  case: r => [//|] rl rr rh rx /= _; rewrite !height_opp_subdef.
  case: (ltnP _ _) => [|_ /=]; last first.
    by congr node; rewrite maxnC//; congr ((maxn _ _).+1); rewrite maxnC.
  case: rl => [//|rll rlr rlh rlx] _ /=.
  by rewrite !height_opp_subdef; congr node; rewrite maxnC//; congr ((maxn _ _).+1); rewrite maxnC.
case: l => [//|ll lr lh lx] _ /=; rewrite !height_opp_subdef.
case: (ltnP _ _) => [|_ /=]; last first.
  by congr node; rewrite maxnC//; congr ((maxn _ _).+1); rewrite maxnC.
case: lr => [//|lrl lrr lrh lrx] _ /=.
by rewrite !height_opp_subdef; congr node; rewrite maxnC//; congr ((maxn _ _).+1); rewrite maxnC.
Qed.

Lemma well_formed_balance_node t :
  well_formed t -> well_formed (balance_node t).
Proof.
case: t => [//|] l r h x /= /andP[]/andP[] => /eqP -> {h}.
wlog: l r / height r <= height l => [H|rl] lwf rwf.
  move/orP: (le_total (height r) (height l)); case=> [rl|lr].
    exact: H.
  rewrite -well_formed_opp_subdef -balance_node_opp_subdef/= maxnC -height_opp_subdef -(height_opp_subdef l).
  by apply: H; rewrite ?well_formed_opp_subdef//  2!height_opp_subdef.
rewrite /balance_node; case: (leq_diffn1P _ _); last by rewrite /= eqxx lwf.
  by move/leqW: rl; rewrite leqNgt => /negPf ->.
case: l lwf {rl} => [//|] ll lr lh lx /= /andP[]/andP[] /eqP -> llwf lrwf _.
case: (ltnP (height ll) (height lr)) => [|_].
case: lr lrwf => [//|] lrl lrr lrh /= _ /andP[]/andP[] /eqP -> {lrh} lrlwf lrrwf _.
  by rewrite !eqxx/= llwf lrlwf lrrwf.
by rewrite /= 2!eqxx/= llwf lrwf.
Qed.

Lemma balanced_balance_node l r h x :
  well_formed l -> balanced l -> well_formed r -> balanced r -> diffn (height l) (height r) <= 2
  -> balanced (balance_node (node l r h x)).
Proof.
wlog: l r / height r <= height l => [H|rlh] lwf lb rwf rb lrd.
  move/orP: (le_total (height r) (height l)); case=> [rlh|lrh].
    exact: H.
  rewrite -balanced_opp_subdef -balance_node_opp_subdef/=.
  by apply: H; rewrite ?well_formed_opp_subdef// ?balanced_opp_subdef// 2!height_opp_subdef// diffnC.
move: (rlh) (rlh) lrd; rewrite diffn_subnE => /maxn_idPl -> /minn_idPr ->; rewrite leq_subLR addn2 => lrh.
rewrite /balance_node; case: (leq_diffn1P _ _); last by rewrite /= lb diffnC => ->.
  by move/leqW: rlh => /[dup] rlh; rewrite leqNgt => /negPf ->.
case: l lwf lb lrh {rlh} => [//|] ll lr lh lx /= /andP[]/andP[] /eqP -> {lh} _ lrwf /andP[]/andP[].
rewrite /diffn; case: (ltnP _ _) => + + llb lrb; rewrite leq_subLR addn1; last first.
  rewrite !ltnS => lrh llh /= llr rll.
  move: (leq_trans rll llh); rewrite ltnS => /[dup] rlr /maxn_idPl ->.
  by rewrite llb lrb rb 3!andbT !geq_diffn !addn1 (leqW llh) ltnS lrh (leq_trans lrh llr) (leqW rlr).
case: lr lrwf lrb => [//|] lrl lrr lrh lrx /= /andP[]/andP[] /eqP -> {lrh} _ _ /andP[]/andP[] + lrlb lrrb.
rewrite geq_diffn !addn1 !ltnS diffnS => /andP[] lrlh lrrh; mk_conj => /anti_leq ->; mk_conj => /anti_leq <-.
rewrite rb llb lrlb lrrb 4!andbT maxnAC maxnn maxnCA maxnn diffnn/= !diffn_subnE.
rewrite maxnAC maxnn maxnK -maxnCA maxnn maxKn !leq_subLR !addn1.
by case: (ltnP (height lrl) (height lrr)) => _; rewrite ?lrlh ?lrrh leqnSn.
Qed.

Lemma well_ordered_subdef_balance_node t lb ub :
  well_ordered_subdef t lb ub -> well_ordered_subdef (balance_node t) lb ub.
Proof.
case: t lb ub => [//|] l r h x lb ub/= /andP[]/andP[]/andP[] lbx xub lwo rwo.
rewrite /balance_node; case: (leq_diffn1P _ _) => [+|+|_]; last first.
- by rewrite /= lbx xub lwo.
- case: l lwo => [//|] ll lr lh lx /= /andP[]/andP[]/andP[] lblx lxx llwo lrwo _.
  case: (ltnP _ _); last first.
    rewrite /= lblx lxx llwo lrwo rwo xub.
    by case: ub xub {rwo} => [ub|//]/= /(lt_trans lxx) ->.
  case: lr lrwo => [//|] lrl lrr lrh lrx /= /andP[]/andP[]/andP[] lxlrx lrxx -> -> _.
  rewrite lblx xub lxlrx llwo rwo lrxx !andbT; apply/andP; split.
    by case: lb lblx {lbx llwo} => [lb|//]/= lblx; apply: (lt_trans lblx).
  by case: ub xub {rwo} => [ub|//]/=; apply/lt_trans.
case: r rwo => [//|] rl rr rh rx /= /andP[]/andP[]/andP[] xrx rxub rlwo rrwo _.
case: (ltnP _ _); last first.
  rewrite /= rxub lbx xrx lwo rlwo rrwo !andbT.
  by case: lb lbx {lwo} => [lb|//]/= lbx _; apply: (lt_trans lbx).
case: rl rlwo => [//|] rll rlr rlh rlx /= /andP[]/andP[]/andP[] xrlx rlxrx -> -> _.
rewrite lbx xrlx lwo rlxrx rxub rrwo !andbT; apply/andP; split.
  by case: lb lbx {lwo} => [lb|//]/= lbx; apply: (lt_trans lbx).
by case: ub rxub {xub rrwo} => [ub|//]/=; apply/lt_trans.
Qed.

Lemma height_balance_nodel ll lr r h hl x xl :
  well_formed (node (node ll lr hl xl) r h x) -> (height r).+1 < hl ->
  height (balance_node (node (node ll lr hl xl) r h x)) = hl + (height ll == height lr).
Proof.
rewrite /balance_node => /= /andP[]/andP[] /eqP -> /andP[]/andP[] /eqP -> _ lrwf _.
case: (leq_diffn1P _ _) => // + _; rewrite ltnS.
case: (ltnP (height ll) (height lr)); last first.
  rewrite /= -(maxnSS (height lr) _) maxnCA => + /maxn_idPl ->.
  have [-> _|] := (eqVneq (height lr) (height ll)).
    by move: (leqnSn (height ll)) => /maxn_idPl ->; rewrite addn1.
  by mk_conj; rewrite -ltn_neqAle addn0 => /maxn_idPr ->.
case: lr lrwf => [//|] lrl lrr lrh lrx /= /andP[]/andP[] /eqP -> _ _ /[dup] /ltn_eqF ->. 
by rewrite maxnSS !ltnS maxnA -(maxnA (height ll)) addn0 => /maxn_idPr -> /maxn_idPl ->.
Qed.

Lemma balance_node_balanced' l r h x :
  diffn (height l) (height r) <= 1 -> balance_node (node l r h x) = node l r h x.
Proof. by rewrite /balance_node; case: (leq_diffn1P _ _). Qed.

Lemma height_balance_node t :
  well_formed t -> (height t).-1 <= height (balance_node t) <= (height t).
Proof.
case: t => [//|] l r h x /= /andP[]/andP[] /eqP -> {h}; rewrite -pred_Sn.
wlog: l r / height r <= height l => [H|rlh] lwf rwf.
  move/orP: (le_total (height r) (height l)); case=> [rlh|lrh].
    exact: H.
  rewrite -height_opp_subdef -(height_opp_subdef r) -(height_opp_subdef (balance_node _)) -balance_node_opp_subdef/= maxnC.
  by apply: H; rewrite ?well_formed_opp_subdef// !height_opp_subdef.
move: (rlh) => /maxn_idPl ->.
case /boolP: (diffn (height l) (height r) <= 1).
  by move=> /balance_node_balanced' -> /=; rewrite leqnn leqnSn.
rewrite /balance_node; case: (leq_diffn1P _ _) => // + _; last first.
  by move/leqW: rlh => /[dup] rlh; rewrite leqNgt => /negPf ->.
case: l lwf {rlh} => [//|] ll lr lh lx /= /andP[]/andP[] lhE llwf lrwf rlh.
move: (rlh) => /(@height_balance_nodel ll lr r lh.+1 lh x lx) => /=; mp. 
  rewrite eqSS lhE llwf lrwf rwf !andbT; apply/eqP/esym/maxn_idPl.
  by move: rlh => /leqW/leqW; rewrite 2!ltnS.
move: rlh; rewrite /balance_node; case: (leq_diffn1P (height r) lh) => // rlh _.
move=> ->.
by have [_|_] := (eqVneq (height ll) (height lr));
  rewrite ?addn1 ?addn0 leqnn leqnSn.
Qed.

Lemma mem_balance_node x t : well_ordered t -> mem_subdef x (balance_node t) = mem_subdef x t.
Proof.
case: t => [//|] l r h tx /andP[]/andP[] _; rewrite -/well_ordered_subdef /balance_node => lwo rwo; case: (leq_diffn1P _ _) => //.
  case: r rwo => [//|] rl rr rh rx /= /andP[]/andP[]/andP[] txrx _ rlwo _ _.
  case: (ltnP _ _) => [|_ /=]; last first.
    case /comparable_ltgtP: (comparableT x tx) => [xtx|//|->] /=; last by rewrite txrx orbT.
    by move: (lt_trans xtx txrx) => /[dup] + ->; rewrite lt_neqAle => /andP[] /negPf ->.
  case: rl rlwo => [//|] rll rlr rlh rlx/= /andP[]/andP[]/andP[] txrlx rlxrx _ _ _.
  case /comparable_ltgtP: (comparableT x tx) => [xtx|_|->] /=; last by rewrite txrlx orbT.
    by move: (lt_trans xtx txrlx) => /[dup] + ->; rewrite lt_neqAle => /andP[] /negPf ->.
  case /comparable_ltgtP: (comparableT x rlx) => [xrlx|//|->] /=; last by rewrite rlxrx orbT.
  by move: (lt_trans xrlx rlxrx) => /[dup] + ->; rewrite lt_neqAle => /andP[] /negPf ->.
case: l lwo => [//|] ll lr lh lx /= /andP[]/andP[] lxtx _ lrwo _. 
case: (ltnP _ _) => [|_ /=]; last first.
  case /comparable_ltgtP: (comparableT x lx) => [xlx|//|->] /=; last by rewrite lxtx orbT.
  by move: (lt_trans xlx lxtx) => /[dup] + ->; rewrite lt_neqAle => /andP[] /negPf ->.
case: lr lrwo => [//|] lrl lrr lrh lrx/= /andP[]/andP[]/andP[] lxlrx lrxtx _ _ _.
case /comparable_ltgtP: (comparableT x lx) => [xlx|_|->] /=; last by rewrite lxlrx (lt_trans lxlrx lrxtx) !orbT.
  move: (lt_trans xlx lxlrx) => /[dup] + ->; rewrite lt_neqAle => /andP[] /negPf -> xlrx.
  by move: (le_lt_trans xlrx lrxtx) => /[dup] + ->; rewrite lt_neqAle => /andP[] /negPf ->.
case /comparable_ltgtP: (comparableT x lrx) => [xlrx|//|->] /=; last by rewrite lrxtx orbT.
by move: (lt_trans xlrx lrxtx) => /[dup] + ->; rewrite lt_neqAle => /andP[] /negPf ->.
Qed.

Fixpoint add_subdef x t :=
  match t with
  | leaf => node leaf leaf 1 x
  | node l r h y => if x == y then t else
    if (x < y)%O then balance_node (node (add_subdef x l) r (maxn (height (add_subdef x l)) (height r)).+1 y)
    else balance_node (node l (add_subdef x r) (maxn (height l) (height (add_subdef x r))).+1 y)
  end.

Lemma well_formed_add x t :
  well_formed t -> well_formed (add_subdef x t).
Proof.
elim: t => [//|] l IHl r IHr h y.
rewrite /add_subdef.
case /comparable_ltgtP: (comparableT x y) => // _ /andP[]/andP[] hE /[dup] lw /IHl lw' /[dup] rw /IHr rw'; apply/well_formed_balance_node; rewrite /= eqxx /=.
  by rewrite lw'.
by rewrite rw' andbT.
Qed.

Lemma balanced_add x t :
  well_formed t -> balanced t -> balanced (add_subdef x t).
Proof.
move=> twf tb; suff: balanced (add_subdef x t) /\ height t <= height (add_subdef x t) <= (height t).+1.
  by move=> [+ _].
elim: t twf tb => [//|] l IHl r IHr h y /=
  /andP[]/andP[/eqP -> {h}] /[dup] lwf /IHl {}IHl /[dup] rwf /IHr {}IHr
  /andP[]/andP[/[dup] lrd +] /[dup] lb /IHl {IHl} [xlb /andP[lxl xll]] /[dup] rb /IHr {IHr} [xrb /andP[rxr xrr]].
rewrite geq_diffn 2!addn1 => /andP[lrh rlh].
case /comparable_ltgtP: (comparableT x y) => _ /=; last first.
- by split; [rewrite lrd lb | apply/andP; split].
- split.
    apply/balanced_balance_node => //; first exact/well_formed_add.
    rewrite geq_diffn !addn2; apply/andP; split.
      by apply: (leq_trans lrh); rewrite ltnS; apply/leqW.
    by apply: (leq_trans xrr); rewrite ltnS.
  move: (@height_balance_node (node l (add_subdef x r)
      (maxn (height l) (height (add_subdef x r))).+1 y)); mp.
    by rewrite /= eqxx lwf well_formed_add.
  move=> /andP[]/= bge ble.
  apply/andP; split; last first.
    apply: (leq_trans ble); rewrite ltnS geq_max; apply/andP; split.
      exact/leqW/leq_maxl.
    by rewrite -maxnSS leq_max xrr orbT.
  case /boolP: (diffn (height l) (height (add_subdef x r)) <= 1) => [lxr|].
    rewrite balance_node_balanced'//= ltnS geq_max leq_maxl/=.
    exact/(leq_trans rxr)/leq_maxr.
  move: rxr; rewrite geq_diffn !addn1 -ltnS => /(leq_trans lrh) -> /=.
  rewrite -ltnNge => lxr.
  move: (@height_balance_node (node l (add_subdef x r)
        (maxn (height l) (height (add_subdef x r))).+1 y)); mp.
    by rewrite /= eqxx lwf/=; apply/well_formed_add.
  move=> /= /andP[+ _]; apply leq_trans.
  move: (lxr) => /leqW/leqW; rewrite 2!ltnS => /maxn_idPr ->.
  rewrite gtn_max; apply/andP; split; last exact/(leq_ltn_trans rlh).
  by rewrite -ltnS; apply/leqW.
split.
  apply/balanced_balance_node => //; first exact/well_formed_add.
  rewrite geq_diffn !addn2; apply/andP; split.
    by apply: (leq_trans xll); rewrite ltnS.
  by apply: (leq_trans rlh); rewrite ltnS; apply/leqW.
move: (@height_balance_node (node (add_subdef x l) r
    (maxn (height (add_subdef x l)) (height r)).+1 y)); mp.
  by rewrite /= eqxx rwf well_formed_add.
move=> /andP[]/= bge ble.
apply/andP; split; last first.
  apply: (leq_trans ble); rewrite ltnS geq_max; apply/andP; split.
    by rewrite -maxnSS leq_max xll.
  exact/leqW/leq_maxr.
case /boolP: (diffn (height (add_subdef x l)) (height r) <= 1) => [xlr|].
  rewrite balance_node_balanced'//= ltnS geq_max leq_maxr/= andbT.
  exact/(leq_trans lxl)/leq_maxl.
move: lxl; rewrite geq_diffn !addn1 -ltnS => /(leq_trans rlh) -> /=.
rewrite andbT -ltnNge => rxl.
move: (@height_balance_node (node (add_subdef x l) r
        (maxn (height (add_subdef x l)) (height r)).+1 y)); mp.
  by rewrite /= eqxx rwf andbT; apply/well_formed_add.
move=> /= /andP[+ _]; apply leq_trans.
move: (rxl) => /leqW/leqW; rewrite 2!ltnS => /maxn_idPl ->.
rewrite gtn_max; apply/andP; split; first exact/(leq_ltn_trans lrh).
by rewrite -ltnS; apply/leqW.
Qed.

Lemma well_ordered_add x t lb ub :
  well_ordered_subdef t lb ub -> map_or (< x)%O true lb -> map_or (> x)%O true ub ->
  well_ordered_subdef (add_subdef x t) lb ub.
Proof.
elim: t lb ub => [lb ub/= _ -> ->//|l IHl r IHr h xt] lb ub/=
  /andP[]/andP[]/andP[] lbxt xtub lwo rwo lbx xub.
case /comparable_ltgtP: (comparableT x xt) => [xxt|xtx|xxt]; last first.
- by rewrite /= lbxt xtub lwo.
- apply/well_ordered_subdef_balance_node; rewrite /= lbxt xtub lwo/=.
  exact: IHr.
- apply/well_ordered_subdef_balance_node; rewrite /= lbxt xtub rwo andbT/=.
  exact: IHl.
Qed.

Lemma is_avl_add x (t : t) : is_avl (add_subdef x (val t)).
Proof.
case: t => t/= /andP[]/andP[] twf tb two.
apply/andP; split; last exact: well_ordered_add.
apply/andP; split; first exact: well_formed_add.
exact: balanced_add.
Qed.
    
Definition add x (t : t) : Def.t := exist _ (add_subdef x (val t)) (is_avl_add x t).

Lemma mem_add x y (t : t) : mem x (add y t) = (x == y) || mem x t.
Proof.
rewrite /mem/add/=; case: t => t/= /andP[] _.
elim: t => [//=|l IHl r IHr h tx/=]; first by rewrite if_same.
rewrite /well_ordered/= => /andP[] /[dup] lwo /(well_ordered_subdefWr (ub':=None) erefl) /IHl {}IHl /[dup] rwo /(well_ordered_subdefWl (lb':=None) erefl) /IHr {}IHr.
case /comparable_ltgtP: (comparableT y tx) => [ytx|txy|->]; last by rewrite !orbA orbb.
  rewrite mem_balance_node/=; last by rewrite /well_ordered/= rwo andbT; apply/well_ordered_add.
  case: (ltP x tx) => [xtx|txx]; first by rewrite IHl !orbA [(_ == _) || _]orbC.
  by move: (lt_le_trans ytx txx); rewrite lt_neqAle eq_sym => /andP[] /negPf ->.
rewrite mem_balance_node/=; last by rewrite /well_ordered/= lwo/=; apply/well_ordered_add.
case /comparable_ltgtP: (comparableT x tx) => [xtx|//|->].
  by move: (lt_trans xtx txy); rewrite lt_neqAle eq_sym => /andP[] /negPf ->.
by move: txy; rewrite lt_neqAle eq_sym => /andP[] /negPf ->.
Qed.

Fixpoint pop_min_subdef (t : t_subdef) : t_subdef * option elt :=
  match t with
  | leaf => (t, None)
  | node l r h x =>
      match l with
      | leaf => (r, Some x)
      | node ll lr lh lx => let (l, y) := pop_min_subdef l in (balance_node (node l r (maxn (height l) (height r)).+1 x), y)
      end
  end.

Lemma pop_min_subdef0 t : ((pop_min_subdef t).2 == None) = (t == leaf).
Proof.
elim: t => [//|] l IHl r _ h x/=.
move: (pop_min_subdef l) IHl => [pml ml]/=.
by case: l => [//|] ll lr lh lx ->.
Qed.

Lemma well_formed_pop_min_subdef t : well_formed t -> well_formed (pop_min_subdef t).1.
Proof.
elim: t => [//|] l IHl r _/= h x /= /andP[]/andP[] _ {h} /IHl {}IHl rwf.
move: (pop_min_subdef l) IHl => [pml ml] /= pmlwf.
case: l => [//|] ll lr lh lx /=.
by apply/well_formed_balance_node; rewrite /= eqxx pmlwf.
Qed.


Lemma balanced_height_pop_min_subdef t : well_formed t -> balanced t -> balanced (pop_min_subdef t).1 /\ (height t).-1 <= height (pop_min_subdef t).1 <= height t.
Proof.
elim: t => [//|] l IHl r _ h x /= /andP[]/andP[] /eqP -> {h} /IHl {}IHl rwf /andP[]/andP[] lrd /IHl {IHl} [pmlb pmlh] rb.
move: (pop_min_subdef l) pmlb pmlh => [pml ml]/= pmlb pmlh.
case: l lrd pmlh => /=.
  by move=> _ _; split=> //; rewrite max0n leqnn leqnSn.
move=> _ _ h _ hrd /andP[] hpml pmlh.
move: hpml; rewrite -ltnS => /(leq_trans (leqSpred h)) hpml.
case /boolP: (diffn (height pml) (height r) <= 1).
  move=> /[dup] pmlrd /balance_node_balanced' -> /=.
  rewrite pmlrd pmlb; split=> //.
  rewrite ltnS 2!geq_max leq_maxr leq_max pmlh/= andbT; apply/andP; split; last first.
    exact/leqW/leq_maxr.
  by apply: (leq_trans hpml); rewrite ltnS leq_maxl.
move=> pmlr.
have hE: h = (height pml).+1.
  move: hrd; have [-> pmlr'|hpmlne _] := eqVneq h (height pml).
    by move: pmlr; rewrite pmlr'.
  by apply/anti_leq/andP; split=> //; rewrite ltn_neqAle eq_sym hpmlne.
subst h.
move: hrd pmlr {hpml pmlh}; rewrite !geq_diffn !addn1 ltnS => /andP[] /[dup] pmlr /leqW -> rpml /=.
rewrite -ltnNge /balance_node; case: (leq_diffn1P _ _) => // {}pmlr _.
move: rpml pmlr; mk_conj => /anti_leq.
case: r rwf rb => [//|] rl rr rh rx/= /andP[]/andP[] /eqP -> {rh} rlwf _ /andP[]/andP[] + rlb rrb /eqP => /[swap].
rewrite diffn_subnE leq_subLR addn1 eqSS; case: (ltnP (height rr) (height rl)) => /[swap] /eqP /[dup] + ->; last first.
  rewrite /= ltnS => rrE rlpml /[dup] pmlrl /maxn_idPr ->.
  rewrite !maxnSS (maxn_idPl pmlrl) (maxn_idPr (leqnSn (height pml))) rrE diffnS diffnC pmlb rlb rrb !andbT andbb !ltnS; split; last first.
    by apply/andP; split.
  by rewrite geq_diffn !addn1 rlpml andbT; apply/leqW.
move=> rlpml; mk_conj => /anti_leq /eqP; rewrite eqSS => /eqP rrpml.
case: rl rlwf rlb rlpml => [//|] rll rlr rlh rlx/= /andP[]/andP[] /eqP -> {rlh} _ _ /andP[]/andP[] rd -> -> /eqP.
rewrite eqSS => /eqP pmlE.
rewrite !ltnS diffnS pmlb rrb !maxnSS (maxn_idPr (leqnSn (height pml))) !ltnS rrpml -pmlE.
rewrite maxnAC maxnn maxnCA maxnn diffnn/= maxnn leqnn leqnSn; split=> //.
by move: rd; rewrite !andbT !geq_diffn !addn1 -!maxnSS !geq_max !leq_max !leqnSn => /andP[] -> ->.
Qed.

Lemma balanced_pop_min_subdef t : well_formed t -> balanced t -> (height t).-1 <= height (pop_min_subdef t).1 <= height t.
Proof. by move=> twf /(balanced_height_pop_min_subdef twf) [_]. Qed.


Lemma height_pop_min_subdef t : well_formed t -> balanced t -> balanced (pop_min_subdef t).1.
Proof. by move=> twf /(balanced_height_pop_min_subdef twf) [+ _]. Qed.
  
Lemma well_ordered_pop_min_subdef t lb ub : well_ordered_subdef t lb ub -> (well_ordered_subdef (pop_min_subdef t).1 (pop_min_subdef t).2 ub /\ map2_or <%O true lb (pop_min_subdef t).2 /\ map2_or <%O true (pop_min_subdef t).2 ub).
Proof.
case: t => [|l r h x] two; first by split=> //; split=> //; case: lb {two}.
suff: well_ordered_subdef (pop_min_subdef (node l r h x)).1 (pop_min_subdef (node l r h x)).2 ub /\ map2_or <%O true lb (pop_min_subdef (node l r h x)).2 /\ map2_or <%O true (pop_min_subdef (node l r h x)).2 ub /\ (map_or (<= x)%O true (pop_min_subdef (node l r h x)).2).
  by move=> [pmtwo][lbmt][mtub] mtx.
elim: l lb ub r h x two => [|ll IHll lr _ lh lx]/= lb ub r h x /andP[]/andP[]/andP[] lbx xub.
  by rewrite le_refl => _ ->; split=> //; split.
move=> /[dup] /andP[]/andP[]/andP[] lblx lxx _ _ /IHll-/(_ lh) []{}IHll []lbml []mllx mlllx rwo.
move: IHll lbml mllx mlllx => /=.
move: (pop_min_subdef ll) => [pmll mll]/=.
case: ll => /= [|_ _ _ _].
  move=> lrwo {}lblx _ _; split.
    by apply/well_ordered_subdef_balance_node => /=; rewrite lxx xub lrwo.
  split=> //; split; last exact/ltW.
  by case: ub xub {rwo} => [|//]ub; apply/lt_trans.
move=> pmllwo lbmll; split; last first.
  split=> //.
  case: mll mllx {pmllwo mlllx lbmll} => [|//]mll/= mlllx; split; last exact/ltW.
  by case: ub xub {rwo} => [|//]ub/=; apply/lt_trans.
apply/well_ordered_subdef_balance_node => /=.
rewrite xub rwo pmllwo !andbT.
by case: mll mlllx {pmllwo lbmll mllx} => [|//]mll/= mlllx; apply/(le_lt_trans mlllx).
Qed.

Lemma mem_pop_min_subdef x t : well_ordered t -> mem_subdef x (pop_min_subdef t).1 = (mem_subdef x t && (Some x != (pop_min_subdef t).2)).
Proof.
rewrite /well_ordered; elim: t => [//|] l IHl r _ h tx/= /andP[] lwo rwo.
move: (pop_min_subdef l) IHl (well_ordered_pop_min_subdef lwo) => [pml ml]/= /(_ (well_ordered_subdefWr (ub':=None) erefl lwo)) IHl []pmlwo [] _ mltx.
case: l {lwo} IHl => [|ll lr lh lx]/= IHl.
  have: mem_subdef x r -> (tx < x)%O by move=> /(mem_well_ordered_subdef rwo) /= [].
  rewrite (inj_eq Some_inj); case /comparable_ltgtP: (comparableT x tx) => //= _.
  - by case: (mem_subdef x r) => // /(_ erefl).
  - by rewrite andbT.
  - by case: (mem_subdef x r) => // /(_ erefl).
rewrite mem_balance_node/=; last first.
  by rewrite /well_ordered/= rwo andbT; apply/(well_ordered_subdefWl (lb:=ml)).
rewrite {}IHl; case /comparable_ltgtP: (comparableT x tx) => //= [txx|->].
  case: ml mltx {pmlwo} => [ml|]/= mltx; last by rewrite andbT.
  move: (lt_trans mltx txx); rewrite (inj_eq Some_inj) lt_neqAle eq_sym => /andP[] ->.
  by rewrite andbT.
case: ml mltx {pmlwo} => [|//]ml/= mltx.
by move: mltx; rewrite (inj_eq Some_inj) lt_neqAle eq_sym => /andP[] ->.
Qed.

Lemma mem_pop_min_subdef' x t : well_ordered t -> mem_subdef x t = (mem_subdef x (pop_min_subdef t).1 || (Some x == (pop_min_subdef t).2)).
Proof.
rewrite /well_ordered; elim: t => [//|] l IHl r _ h tx/= /andP[] lwo rwo.
move: (pop_min_subdef l) IHl (well_ordered_pop_min_subdef lwo) => [pml ml]/= /(_ (well_ordered_subdefWr (ub':=None) erefl lwo)) IHl []pmlwo [] _ mltx.
case: l {lwo} IHl => [|ll lr lh lx]/= IHl.
  have: mem_subdef x r -> (tx < x)%O by move=> /(mem_well_ordered_subdef rwo) /= [].
  rewrite (inj_eq Some_inj); case /comparable_ltgtP: (comparableT x tx) => //= _.
  - by case: (mem_subdef x r) => // /(_ erefl).
  - by rewrite orbF.
  - by case: (mem_subdef x r) => // /(_ erefl).
rewrite mem_balance_node/=; last first.
  by rewrite /well_ordered/= rwo andbT; apply/(well_ordered_subdefWl (lb:=ml)).
rewrite {}IHl; case /comparable_ltgtP: (comparableT x tx) => //= txx.
case: ml mltx {pmlwo} => [ml|] mltx/=; last by rewrite orbF.
by move: (lt_trans mltx txx); rewrite (inj_eq Some_inj) lt_neqAle eq_sym => /andP[] /negPf ->; rewrite orbF.
Qed.

Fixpoint pop_max_subdef (t : t_subdef) : t_subdef * option elt :=
  match t with
  | leaf => (t, None)
  | node l r h x =>
      match r with
      | leaf => (l, Some x)
      | node ll lr lh lx => let (r, y) := pop_max_subdef r in (balance_node (node l r (maxn (height l) (height r)).+1 x), y)
      end
  end.

Lemma pop_max_subdef0 t : ((pop_max_subdef t).2 == None) = (t == leaf).
Proof.
elim: t => [//|] l _ r IHr h x/=.
move: (pop_max_subdef r) IHr => [pmr mr]/=.
by case: r => [//|] rl rr rh rx ->.
Qed.

Lemma well_formed_pop_max_subdef t : well_formed t -> well_formed (pop_max_subdef t).1.
Proof.
elim: t => [//|] l _ r IHr/= h x /= /andP[]/andP[] _ {h} lwf /IHr {}IHr.
move: (pop_max_subdef r) IHr => [pmr mr] /= pmrwf.
case: r => [//|] rl rr rh rx /=.
by apply/well_formed_balance_node; rewrite /= eqxx pmrwf lwf.
Qed.

Lemma balanced_height_pop_max_subdef t : well_formed t -> balanced t -> balanced (pop_max_subdef t).1 /\ (height t).-1 <= height (pop_max_subdef t).1 <= height t.
Proof.
elim: t => [//|] l _ r IHr h x /= /andP[]/andP[] /eqP -> {h} lwf /IHr {}IHr /andP[]/andP[] lrd lb /IHr {IHr} [pmrb pmrh].
move: (pop_max_subdef r) pmrb pmrh => [pmr mr]/= pmrb pmrh.
case: r lrd pmrh => /=.
  by move=> _ _; split=> //; rewrite maxn0 leqnn leqnSn.
move=> _ _ h _ hld /andP[] hpmr pmrh.
move: hpmr; rewrite -ltnS => /(leq_trans (leqSpred h)) hpmr.
case /boolP: (diffn (height l) (height pmr) <= 1).
  move=> /[dup] lpmrd /balance_node_balanced' -> /=.
  rewrite lpmrd pmrb lb; split=> //.
  by rewrite ltnS 2!geq_max leq_maxl -maxnSS !leq_max leqnSn/= hpmr pmrh !orbT.
move=> lpmr.
have hE: h = (height pmr).+1.
  move: hld; have [-> lpmr'|hpmrne _] := eqVneq h (height pmr).
    by move: lpmr; rewrite lpmr'.
  by apply/anti_leq/andP; split=> //; rewrite ltn_neqAle eq_sym hpmrne.
subst h.
move: hld lpmr {hpmr pmrh}; rewrite !geq_diffn !addn1 ltnS => /andP[] lpmr /[dup] pmrl /leqW -> /=.
rewrite andbT -ltnNge /balance_node; case: (leq_diffn1P _ _) => // {}pmrl _.
move: lpmr pmrl; mk_conj => /anti_leq.
case: l lwf lb => [//|] ll lr lh lx/= /andP[]/andP[] /eqP -> {lh} _ lrwf /andP[]/andP[] + llb lrb /eqP => /[swap].
rewrite diffn_subnE leq_subLR addn1 eqSS; case: (ltnP (height ll) (height lr)) => /[swap] /eqP /[dup] + ->; last first.
  rewrite /= ltnS => llE lrpmr /[dup] pmrlr /maxn_idPl ->.
  rewrite !maxnSS (maxn_idPr pmrlr) (maxn_idPl (leqnSn (height pmr))) llE diffnS diffnC pmrb llb lrb !andbT andbb !ltnS; split; last first.
    by apply/andP; split.
  by rewrite geq_diffn !addn1 lrpmr/=; apply/leqW.
move=> lrpmr; mk_conj => /anti_leq /eqP; rewrite eqSS => /eqP llpmr.
case: lr lrwf lrb lrpmr => [//|] lrl lrr lrh lrx/= /andP[]/andP[] /eqP -> {lrh} _ _ /andP[]/andP[] ld -> -> /eqP.
rewrite eqSS => /eqP pmrE.
rewrite !ltnS diffnS pmrb llb !maxnSS (maxn_idPl (leqnSn (height pmr))) !ltnS llpmr -pmrE.
rewrite maxnAC maxnn maxnCA maxnn diffnn/= maxnn leqnn leqnSn; split=> //.
by move: ld; rewrite !andbT !geq_diffn !addn1 -!maxnSS !geq_max !leq_max !leqnSn => /andP[] -> ->.
Qed.

Lemma balanced_pop_max_subdef t : well_formed t -> balanced t -> (height t).-1 <= height (pop_max_subdef t).1 <= height t.
Proof. by move=> twf /(balanced_height_pop_max_subdef twf) [_]. Qed.


Lemma height_pop_max_subdef t : well_formed t -> balanced t -> balanced (pop_max_subdef t).1.
Proof. by move=> twf /(balanced_height_pop_max_subdef twf) [+ _]. Qed.
  
Lemma well_ordered_pop_max_subdef t lb ub : well_ordered_subdef t lb ub -> (well_ordered_subdef (pop_max_subdef t).1 lb (pop_max_subdef t).2 /\ map2_or <%O true lb (pop_max_subdef t).2 /\ map2_or <%O true (pop_max_subdef t).2 ub).
Proof.
case: t => [|l r h x] two; first by split=> //; split=> //; case: lb {two}.
suff: well_ordered_subdef (pop_max_subdef (node l r h x)).1 lb (pop_max_subdef (node l r h x)).2 /\ map2_or <%O true lb (pop_max_subdef (node l r h x)).2 /\ map2_or <%O true (pop_max_subdef (node l r h x)).2 ub /\ (map_or (>= x)%O true (pop_max_subdef (node l r h x)).2).
  by move=> [pmtwo][lbmt][mtub] mtx.
elim: r lb ub l h x two => [|rl _ rr IHrr rh rx]/= lb ub l h x /andP[]/andP[]/andP[] lbx xub.
  by move=> -> _; rewrite le_refl; split=> //; split.
move=> lwo /[dup] /andP[]/andP[]/andP[] xrx rxub _ _ /IHrr-/(_ rh) []{}IHrr []lbmr []mrrx rxmr.
move: IHrr lbmr mrrx rxmr => /=.
move: (pop_max_subdef rr) => [pmrr mrr]/=.
case: rr => /= [|_ _ _ _].
  move=> rlwo _ {}rxub _; split.
    by apply/well_ordered_subdef_balance_node => /=; rewrite xrx lbx rlwo andbT.
  split; first by case: lb lbx {lwo} => [|//]lb/= lbx; apply: (lt_trans lbx).
  by split=> //; apply/ltW.
move=> pmrrwo xmrr; split; last first.
  split; [|split=> //]; case: mrr xmrr {pmrrwo mrrx rxmr} => [mrr|//]/= xmrr; last exact/ltW.
    by case: lb lbx {lwo} => [|//]lb/= lbx; apply: (lt_trans lbx).
  by case: lb {lbx lwo}.
apply/well_ordered_subdef_balance_node => /=.
rewrite lbx lwo pmrrwo !andbT/=.
by case: mrr rxmr {pmrrwo xmrr mrrx} => [|//]mrr/= /(lt_le_trans xrx).
Qed.

Lemma mem_pop_max_subdef x t : well_ordered t -> mem_subdef x (pop_max_subdef t).1 = (mem_subdef x t && (Some x != (pop_max_subdef t).2)).
Proof.
rewrite /well_ordered; elim: t => [//|] l _ r IHr h tx/= /andP[] lwo rwo.
move: (pop_max_subdef r) IHr (well_ordered_pop_max_subdef rwo) => [pmr mr]/= /(_ (well_ordered_subdefWl (lb':=None) erefl rwo)) IHr []pmrwo [] txmr _.
case: r {rwo} IHr => [|rl rr rh rx]/= IHr.
  have: mem_subdef x l -> (x < tx)%O by move=> /(mem_well_ordered_subdef lwo) /= [].
  rewrite (inj_eq Some_inj); case /comparable_ltgtP: (comparableT x tx) => //= _.
  - by rewrite andbT.
  - by case: (mem_subdef x l) => // /(_ erefl).
  - by case: (mem_subdef x l) => // /(_ erefl).
rewrite mem_balance_node/=; last first.
  by rewrite /well_ordered/= lwo/=; apply/(well_ordered_subdefWr (ub:=mr)).
rewrite {}IHr; case /comparable_ltgtP: (comparableT x tx) => //= [xtx|->].
  case: mr txmr {pmrwo} => [mr|]/= txmr; last by rewrite andbT.
  move: (lt_trans xtx txmr); rewrite (inj_eq Some_inj) lt_neqAle eq_sym => /andP[] ->.
  by rewrite andbT.
case: mr txmr {pmrwo} => [|//]mr/= txmr.
by move: txmr; rewrite (inj_eq Some_inj) lt_neqAle eq_sym => /andP[] ->.
Qed.

Lemma mem_pop_max_subdef' x t : well_ordered t -> mem_subdef x t = (mem_subdef x (pop_max_subdef t).1 || (Some x == (pop_max_subdef t).2)).
Proof.
rewrite /well_ordered; elim: t => [//|] l _ r IHr h tx/= /andP[] lwo rwo.
move: (pop_max_subdef r) IHr (well_ordered_pop_max_subdef rwo) => [pmr mr]/= /(_ (well_ordered_subdefWl (lb':=None) erefl rwo)) IHr []pmrwo [] txmr _.
case: r {rwo} IHr => [|rl rr rh rx]/= IHr.
  have: mem_subdef x l -> (x < tx)%O by move=> /(mem_well_ordered_subdef lwo) /= [].
  rewrite (inj_eq Some_inj); case /comparable_ltgtP: (comparableT x tx) => //= _.
  - by rewrite orbF.
  - by case: (mem_subdef x l) => // /(_ erefl).
  - by case: (mem_subdef x l) => // /(_ erefl).
rewrite mem_balance_node/=; last first.
  by rewrite /well_ordered/= lwo/=; apply/(well_ordered_subdefWr (ub:=mr)).
rewrite {}IHr; case /comparable_ltgtP: (comparableT x tx) => //= xtx.
case: mr txmr {pmrwo} => [mr|]/= txmr; last by rewrite orbF.
by move: (lt_trans xtx txmr); rewrite (inj_eq Some_inj) lt_neqAle eq_sym => /andP[] /negPf ->; rewrite orbF.
Qed.

Fixpoint remove_subdef (x : elt) (t : t_subdef) :=
  match t with
  | leaf => leaf
  | node l r h y =>
    if (x == y) then
      let (a, z) :=
        if height l < height r then
          let (r, z) := pop_min_subdef r in (l, r, z)
        else let (l, z) := pop_max_subdef l in (l, r, z)
      in let (l, r) := a in match z with | None => leaf | Some z => node l r (maxn (height l) (height r)).+1 z end
    else if (x < y)%O then balance_node (let l := remove_subdef x l in node l r (maxn (height l) (height r)).+1 y)
    else balance_node (let r := remove_subdef x r in node l r (maxn (height l) (height r)).+1 y)
  end.

Lemma well_formed_remove x t : well_formed t -> well_formed (remove_subdef x t).
Proof.
elim: t => [//|l xlwf r xrwf h xt] /=/andP[]/andP[] _ {h} /[dup] lwf /xlwf {}xlwf /[dup] rwf /xrwf {}xrwf.
rewrite /remove_subdef; case /comparable_ltgtP: (comparableT x xt) => _; rewrite -/remove_subdef.
- by apply/well_formed_balance_node => /=; rewrite eqxx xlwf.
- by apply/well_formed_balance_node => /=; rewrite eqxx lwf.
- case: (ltnP _ _) => _.
    move: (pop_min_subdef r) (well_formed_pop_min_subdef rwf) => [pmr +]/= pmrwf; case=> [|//]mr /=.
    by rewrite eqxx lwf.
  move: (pop_max_subdef l) (well_formed_pop_max_subdef lwf) => [pml +]/= pmlwf; case=> [|//]ml /=.
  by rewrite eqxx pmlwf.
Qed.

Lemma balanced_remove x t : well_formed t -> balanced t -> balanced (remove_subdef x t).
Proof.
move=> twf tb; suff: balanced (remove_subdef x t) /\ (height t).-1 <= height (remove_subdef x t) <= height t by case.
elim: t twf tb => [//|] l xlb r xrb h xt/=
    /andP[]/andP[] /eqP -> {h} /[dup] lwf /xlb {}xlb /[dup] rwf /xrb {}xrb
    /andP[]/andP[] lrd /[dup] lb /xlb [{}xlb /andP[lxl xll]] /[dup] rb /xrb [{}xrb /andP[rxr xrr]].
move: lxl; rewrite -ltnS => /(leq_trans (leqSpred (height l))) lxl.
move: rxr; rewrite -ltnS => /(leq_trans (leqSpred (height r))) rxr.
case /comparable_ltgtP: (comparableT x xt) => _.
- case /boolP: (diffn (height (remove_subdef x l)) (height r) <= 1) {xrb rxr xrr}.
    move=> /[dup] xlrd /balance_node_balanced' -> /=.
    split; first by rewrite xlrd xlb.
    move: lrd xlrd; rewrite !geq_diffn !addn1 => /andP[lr rl] /andP[xlr rxl].
    by rewrite ltnS -!maxnSS !geq_max leq_maxr !leq_max lr rxl leqnSn xll/= orbT.
  move=> xlrd; have {}lxl: height l = (height (remove_subdef x l)).+1.
    move: xll; rewrite leq_eqVlt => /orP; case=> [/eqP {}lxl|xll].
      by move: xlrd lrd; rewrite lxl => /negP.
    by apply/anti_leq/andP; split.
  move: lrd xlrd; rewrite !geq_diffn !addn1 => /andP[] /[dup] lr /(leq_trans xll) -> rl.
  rewrite /= -ltnNge /balance_node; case: (leq_diffn1P (height (remove_subdef x l)) (height r)) => //.
  rewrite -lxl; move: rl; mk_conj => /anti_leq {xll lr} + _.
  case: r rwf rb => [//|] rl rr rh rx/= /andP[]/andP[] /eqP -> rlwf _ /andP[]/andP[] rlrrd rlb rrb /eqP.
  rewrite eqSS => /eqP; case: (ltnP _ _) => [rrrl|rlrr] hlE/=; last first.
    move: rlrrd rlrr; rewrite hlE lxl !geq_diffn !addn1 !ltnS => /andP[] _ xlrl rlxl.
    rewrite -!maxnSS maxnAC maxnn maxnAC maxnn xlb rlb rrb !andbT.
    rewrite (maxn_idPr (leqnSn _)) !maxnSS !ltnS.
    by rewrite (maxn_idPr xlrl) rlxl xlrl (leqW xlrl).
  case: rl rlwf rlb rrrl rlrrd hlE => [//|] rll rlr rlh rlx/= /andP[]/andP[] /eqP -> {rlh} _ _ /andP[]/andP[] + -> -> + + /eqP.
  rewrite diffnS !geq_diffn !addn1 !ltnS lxl eqSS maxnC => /andP[] rllrlr rlrrll + /andP[+ _]; mk_conj => /anti_leq -> /eqP <-.
  rewrite maxnA maxnn -maxnA maxnn leqnSn (maxn_idPr (leqnSn _)) maxnn xlb rrb leqnSn leqnn/=; split=>//.
  by rewrite !andbT -!maxnSS !leq_max !geq_max rllrlr rlrrll !leqnSn.
- case /boolP: (diffn (height l) (height (remove_subdef x r)) <= 1) {xlb lxl xll}.
    move=> /[dup] lxrd /balance_node_balanced' -> /=.
    split; first by rewrite lxrd lb.
    move: lrd lxrd; rewrite !geq_diffn !addn1 => /andP[lr rl] /andP[lxr xrl].
    by rewrite ltnS -!maxnSS !geq_max leq_maxl !leq_max rl lxr leqnSn xrr/= orbT.
  move=> lxrd; have {}rxr: height r = (height (remove_subdef x r)).+1.
    move: xrr; rewrite leq_eqVlt => /orP; case=> [/eqP {}rxr|xrr].
      by move: lxrd lrd; rewrite rxr => /negP.
    by apply/anti_leq/andP; split.
  move: lrd lxrd; rewrite !geq_diffn !addn1 => /andP[] lr /[dup] rl /(leq_trans xrr) ->.
  rewrite /= andbT -ltnNge /balance_node; case: (leq_diffn1P (height l) (height (remove_subdef x r))) => //.
  rewrite -rxr; move: lr; mk_conj => /anti_leq {xrr rl} + _.
  case: l lwf lb => [//|] ll lr lh lx/= /andP[]/andP[] /eqP -> _ lrwf /andP[]/andP[] lllrd llb lrb /eqP.
  rewrite eqSS => /eqP; case: (ltnP _ _) => [lllr|lrll] hrE/=; last first.
    move: lllrd lrll; rewrite hrE rxr !geq_diffn !addn1 !ltnS => /andP[] xrll _ lrxr.
    rewrite -!maxnSS maxnCA maxnn maxnCA maxnn xrb lrb llb !andbT.
    rewrite (maxn_idPl (leqnSn _)) !maxnSS !ltnS.
    by rewrite (maxn_idPl xrll) lrxr xrll (leqW xrll).
  case: lr lrwf lrb lllr lllrd hrE => [//|] lrl lrr lrh lrx/= /andP[]/andP[] /eqP -> {lrh} _ _ /andP[]/andP[] + -> -> + + /eqP.
  rewrite diffnS !geq_diffn !addn1 !ltnS rxr eqSS maxnC => /andP[] lrllrr lrrlrl + /andP[_]; mk_conj => /anti_leq -> /eqP <-.
  rewrite maxnA maxnn -maxnA maxnn leqnSn (maxn_idPl (leqnSn _)) maxnn xrb llb leqnSn leqnn/=; split=>//.
  by rewrite !andbT -!maxnSS !leq_max !geq_max lrllrr lrrlrl !leqnSn.
- rewrite -pred_Sn; case: (ltnP _ _) => [lr|rl].
    move: (pop_min_subdef r) (balanced_height_pop_min_subdef rwf rb) (pop_min_subdef0 r) => [pmr mr]/= [pmrb] /andP[] rpmr pmrr.
    case: mr => [mr _ /=|]; last by rewrite eqxx => /esym/eqP ->; split.
    move: lrd; rewrite !geq_diffn !addn1 lb pmrb => /andP[_].
    move: lr; mk_conj => /anti_leq hrE.
    move: rpmr; rewrite -hrE -pred_Sn => lpmr.
    by rewrite -maxnSS leq_maxl geq_max leqnSn hrE (leqW lpmr) ltnS pmrr.
  move: (pop_max_subdef l) (balanced_height_pop_max_subdef lwf lb) (pop_max_subdef0 l) => [pml ml]/= [pmlb] /andP[] lpml pmll.
  case: ml => [ml _ /=|]; last by rewrite eqxx => /esym/eqP ->; split.
  move: lrd; rewrite !geq_diffn !addn1 rb pmlb => /andP[lr _].
  move: lpml; rewrite -ltnS => /(leq_trans (leqSpred (height l))) => lpml.
  by rewrite (leq_trans pmll lr) (leq_trans rl lpml) ltnS -maxnSS leq_max lpml/= geq_max rl pmll.
Qed.

Lemma well_ordered_remove x t lb ub : well_ordered_subdef t lb ub -> well_ordered_subdef (remove_subdef x t) lb ub.
Proof.
elim: t lb ub => [//|] l xlwo r xrwo h xt lb ub/= /andP[]/andP[]/andP[] lbxt xtub /[dup] lwo /xlwo {}xlwo /[dup] rwo /xrwo {}xrwo.
case /comparable_ltgtP: (comparableT x xt) => [xxt|xtx|xxt].
- by apply/well_ordered_subdef_balance_node => /=; rewrite lbxt xtub xlwo.
- by apply/well_ordered_subdef_balance_node => /=; rewrite lbxt xtub lwo.
subst xt.
case: (ltnP _ _) {xlwo xrwo} => _.
  move: (pop_min_subdef r) (well_ordered_pop_min_subdef rwo) => [pmr mr]/=.
  case: mr => [|//]mr []pmrwo []xmr mrub/=.
  apply/andP; split=> //; apply/andP; split; last first.
    by apply/(well_ordered_subdefWr _ lwo) => /=; apply/ltW.
  apply/andP; split; last by case: ub mrub {rwo xtub pmrwo}.
  by case: lb lbxt {lwo} => [|//]lb/= lbx; apply: (lt_trans lbx).
move: (pop_max_subdef l) (well_ordered_pop_max_subdef lwo) => [pml ml]/=.
case: ml => [|//]ml []pmlwo []lbml mlx/=.
apply/andP; split; last first.
  by apply/(well_ordered_subdefWl _ rwo) => /=; apply/ltW.
apply/andP; split=> //; apply/andP; split; first by case: lb lbml {lwo lbxt pmlwo}.
by case: ub xtub {rwo} => [|//]ub/=; apply/lt_trans.
Qed.

Lemma is_avl_remove x (t : t) : is_avl (remove_subdef x (val t)).
Proof.
case: t => t/= /andP[]/andP[] twf tb two; apply/andP; split; last exact/well_ordered_remove.
by apply/andP; split; [apply/well_formed_remove|apply/balanced_remove].
Qed.

Definition remove x (t : t) : Def.t := exist _ (remove_subdef x (val t)) (is_avl_remove x t).

Lemma mem_remove x y t : mem x (remove y t) = mem x t && (x != y).
Proof.
rewrite /mem/remove; case: t => /= t /andP[]/andP[] + _.
elim: t => [//|] l IHl r IHr h xt /=; rewrite /well_ordered/= => /andP[]/andP[] _ {h} lwf rwf /andP[] lwo rwo.
move: (well_ordered_subdefWr (ub':=None) erefl lwo) (well_ordered_subdefWl (lb':=None) erefl rwo) => lwo' rwo'.
case /comparable_ltgtP: (comparableT y xt) => [yxt|xty|yxt].
- rewrite mem_balance_node /well_ordered/=; last first.
    by rewrite rwo andbT; apply/well_ordered_remove.
  case /comparable_ltgtP: (comparableT x xt) => [xxt|xtx|->].
  + by rewrite IHl.
  + by move: (lt_trans yxt xtx); rewrite lt_neqAle eq_sym => /andP[] ->; rewrite andbT.
  + by move: yxt; rewrite lt_neqAle eq_sym => /andP[] ->; rewrite andbT.
- rewrite mem_balance_node /well_ordered/=; last first.
    by rewrite lwo/=; apply/well_ordered_remove.
  case /comparable_ltgtP: (comparableT x xt) => [xxt|xtx|->].
  + by move: (lt_trans xxt xty); rewrite lt_neqAle eq_sym => /andP[] ->; rewrite andbT.
  + by rewrite IHr.
  + by move: xty; rewrite lt_neqAle eq_sym => /andP[] ->; rewrite andbT.
subst y.
case: (ltnP _ _) => [lr|rl].
  move: (pop_min_subdef r)
      (mem_pop_min_subdef x rwo')
      (mem_pop_min_subdef' x rwo')
      (pop_min_subdef0 r)
      (well_ordered_pop_min_subdef rwo) => [pmr mr]/=.
  case: mr => [mr xpmr xr _|_ _ /esym]/=; last by move: lr; rewrite eqxx => /[swap] /eqP ->.
  move: xpmr xr; rewrite (inj_eq Some_inj) => xpmr xr []pmrwo []xtmr _.
  have xl: mem_subdef x l -> (x < xt)%O by move=> /(mem_well_ordered_subdef lwo) [].
  have xpmr': mem_subdef x pmr -> (mr < x)%O by move=> /(mem_well_ordered_subdef pmrwo) [].
  case /comparable_ltgtP: (comparableT x xt) xpmr xr xl => [xxt|xtx|->]/= xpmr xr xl.
  - by move: (lt_trans xxt xtmr) => /[dup]; rewrite {1}lt_neqAle eq_sym => /andP[] /negPf -> _ ->; rewrite andbT.
  - case /comparable_ltgtP: (comparableT x mr) xpmr xr xpmr' => [xmr|//|->]/= xpmr xr xpmr'; last first.
      by rewrite xr orbT.
    case: (mem_subdef x l) xl => [/(_ erefl)//|_].
    rewrite xr andbT orbF.
    by case: (mem_subdef x pmr) xpmr' => [/(_ erefl)|].
  - move: (xtmr); rewrite lt_neqAle => /andP[] /negPf -> _ /=.
    case: (xt <= mr)%O; first by case: (mem_subdef xt l) xl => [/(_ erefl)|].
    by apply/negP => /(mem_well_ordered_subdef pmrwo)/= [] /(lt_nsym xtmr).
move: (pop_max_subdef l)
    (mem_pop_max_subdef x lwo')
    (mem_pop_max_subdef' x lwo')
    (pop_max_subdef0 l)
    (well_ordered_pop_max_subdef lwo) => [pml ml]/=.
case: ml => [ml xpml xl _|_ _ /esym]/=; last first.
  move: rl; rewrite eqxx => /[swap] /eqP -> /=.
  case: r rwf {IHr rwo rwo'} => [_ _ _|rl rr rh rx /andP[]/andP[] /eqP -> //].
  by rewrite if_same orbF andbN.
move: xpml xl; rewrite (inj_eq Some_inj) => xpml xl []pmlwo [] _ mlxt.
have xr: mem_subdef x r -> (xt < x)%O by move=> /(mem_well_ordered_subdef rwo) [].
have xpml': mem_subdef x pml -> (x < ml)%O by move=> /(mem_well_ordered_subdef pmlwo) [].
case /comparable_ltgtP: (comparableT x xt) xpml xl xr => [xxt|xtx|->]/= xpml xl xr.
- case /comparable_ltgtP: (comparableT x ml) xpml xl xpml' => [//|xml|->]/= xpml xl xpml'; last first.
    by rewrite xl orbT.
  case: (mem_subdef x r) xr => [/(_ erefl)//|_].
  rewrite xl andbT orbF.
  by case: (mem_subdef x pml) xpml' => [/(_ erefl)|].
- by move: (lt_trans mlxt xtx) => /[dup]; rewrite {1}lt_neqAle eq_sym leNgt => /andP[] /negPf -> /negPf ->; rewrite andbT.
- move: (mlxt); rewrite lt_neqAle eq_sym leNgt => /[dup] /andP[] /negPf -> /negPf -> _ /=.
  by case: (mem_subdef xt r) xr => [/(_ erefl)|].
Qed.

Definition elements t := (fix F t e :=
  match t with
  | leaf => e
  | node l r _ x => F l (x :: (F r e))
  end) t [::].

Fixpoint min t :=
  match t with
  | leaf => None
  | node l _ _ x => match min l with None => Some x | Some y => Some y end
  end.

Fixpoint max t :=
  match t with
  | leaf => None
  | node _ r _ x => match max r with None => Some x | Some y => Some y end
  end.

End Def.

Section Theory.

Variables (d : unit) (elt : orderType d).
Notation t := (t elt).

  

  
  


  


    




End AVL.
