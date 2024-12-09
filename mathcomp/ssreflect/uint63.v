(* TODO: remove when requiring coq8.21 *)
From Coq Require Import ZArith Init.Wf.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat div eqtype seq choice fintype order ssralg.
From Coq Require Export Uint63.

(******************************************************************************)
(*                    uint63 (unsigned integers on 63 bits)                      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.POrderTheory Order.TotalTheory Order.OrderEmbeddingTheory.
Import Order.BPOrderTheory Order.TPOrderTheory GRing.Theory.

Local Open Scope nat_scope.
Local Open Scope uint63_scope.

Definition uint63 := int.

(* TODO: port back to div *)

Lemma modnE n m : n %% m = (n mod m)%N.
Proof.
rewrite {2}(divn_eq n m) mulnE addnE.
rewrite Nat.Div0.add_mod Nat.Div0.mod_mul Nat.Div0.mod_mod.
case: m => [|m]; first by rewrite modn0 Nat.mod_0_r.
by rewrite Nat.mod_small//; apply/ssrnat.ltP/ltn_pmod.
Qed.

Definition to_nat (n : uint63) := Z.to_nat (to_Z n).
Definition of_nat n : uint63 := of_Z (Z.of_nat n).

Lemma to_natK : cancel to_nat of_nat.
Proof.
move=> x; rewrite /to_nat /of_nat Z2Nat.id ?of_to_Z//.
by case: (to_Z_bounded x).
Qed.

Lemma to_natI : injective to_nat.
Proof. exact: (ssrfun.can_inj to_natK). Qed.

Lemma wBE : wB = Z.of_nat (2 ^ size).
Proof.
rewrite /wB.
elim: size => [//|] s IHs.
rewrite Nat2Z.inj_succ Z.pow_succ_r; last exact: Nat2Z.is_nonneg.
rewrite expnS IHs.
elim: (2 ^ s) => [//|] n IHn.
rewrite mul2n doubleS !Nat2Z.inj_succ -mul2n.
by rewrite -Z.add_diag Z.add_succ_l Z.add_succ_r Z.add_diag IHn.
Qed.

Lemma to_nat_bounded n : (to_nat n < 2 ^ size)%N.
Proof.
move: (to_Z_bounded n) => [n0] /Z2Nat.inj_lt-/(_ n0 ltac:(done))/ssrnat.ltP.
by rewrite wBE Nat2Z.id.
Qed.

Lemma of_natK n : to_nat (of_nat n) = n %% 2 ^ size.
Proof.
rewrite /to_nat /of_nat of_Z_spec Z2Nat.inj_mod.
- by rewrite wBE !Nat2Z.id modnE.
- exact: Nat2Z.is_nonneg.
- by rewrite wBE; exact: Nat2Z.is_nonneg.
Qed.

Lemma of_nat_modn m : of_nat (m %% 2 ^ size) = of_nat m.
Proof. by apply: to_natI; rewrite !of_natK modn_mod. Qed.

Definition to_I63 (n : uint63) := Ordinal (to_nat_bounded n).
Definition of_I63 (n : 'I_(2 ^ size)) : uint63 := of_nat n.

Lemma to_I63K : cancel to_I63 of_I63.
Proof. exact: to_natK. Qed.

Lemma of_I63K : cancel of_I63 to_I63.
Proof. by move=> n; apply/val_inj => /=; rewrite of_natK modn_small. Qed.

Lemma eqbP : Equality.axiom eqb.
Proof.
move=> x y; apply/Bool.iff_reflect.
(* Why does apply introduce a hole, the goal clearly matches *)
by refine (iff_sym _); apply/eqb_spec.
Qed.

HB.instance Definition _ := hasDecEq.Build uint63 eqbP.

Module Sub.
Definition Sub n (_ : predT n) := of_I63 n.

Lemma Sub_rect K : (forall x Px, K (@Sub x Px)) -> forall u, K u.
Proof.
move=> + u => /(_ (to_I63 u) isT).
by rewrite /Sub to_I63K.
Qed.

Lemma SubK_subproof x Px : to_I63 (@Sub x Px) = x.
Proof. exact: of_I63K. Qed.

End Sub.

HB.instance Definition _ := isSub.Build _ _ uint63 Sub.Sub_rect Sub.SubK_subproof.

Module Choice.
Import Choice.InternalTheory.

Definition find_subdef P n := omap of_I63 (@find 'I__ (P \o of_I63) n).

Lemma correct_subdef P n x : find_subdef P n = Some x -> P x.
Proof.
rewrite /find_subdef.
case: (find _ _) (@choice_correct_subdef _ (P \o of_I63) n) => [y|//].
by move=> /(_ y erefl)/= Py /Some_inj <-.
Qed.

Lemma complete_subdef (P : {pred uint63}) :
  (exists x, P x) -> exists n, find_subdef P n.
Proof.
move=> [x] Px.
move: (@choice_complete_subdef _ (P \o of_I63)) => /(_ _)/wrap[].
  by exists (to_I63 x); rewrite /= to_I63K.
move=> [n] Pn; exists n.
by rewrite /find_subdef; case: (find _ _) Pn.
Qed.

Lemma extensional_subdef P Q : P =1 Q -> find_subdef P =1 find_subdef Q.
Proof.
move=> PQ x; rewrite /find_subdef; congr (omap _ _).
by apply/choice_extensional_subdef => y /=; apply: PQ.
Qed.

End Choice.

HB.instance Definition _  :=
  hasChoice.Build uint63
    Choice.correct_subdef Choice.complete_subdef Choice.extensional_subdef.

Module Countable.
  
Definition unpickle n := Some (of_nat n).

Lemma pickleK : pcancel to_nat unpickle.
Proof. by move=> x; rewrite /unpickle to_natK. Qed.

End Countable.

HB.instance Definition _ := Choice_isCountable.Build uint63 Countable.pickleK.

Module Enum.
Fact enum_key : unit. exact: tt. Qed.

Definition enum := [seq of_I63 n | n <- enum 'I__].

Lemma enumP : Finite.axiom (enum : list uint63).
Proof.
move=> x.
rewrite count_map (eq_count (a2 := pred1 (to_I63 x))) => [|y /=]; last first.
  exact/(can2_eq of_I63K to_I63K).
rewrite count_uniq_mem; last exact/enum_uniq.
by rewrite mem_enum.
Qed.

End Enum.

HB.instance Definition _ := isFinite.Build uint63 Enum.enumP.

Module Order.

Lemma lt_def (x y : uint63) : (x <? y) = (y != x) && (x <=? y).
Proof.
apply/ltbP/andP => [xy|[] /eqP yx /lebP xy]; last first.
  by apply/Z.nle_gt => /(Z.le_antisymm _ _ xy)/to_Z_inj/esym.
split; last by apply/lebP/Z.lt_le_incl.
apply/negP => /eqP yx.
by move: xy; rewrite yx => /Z.lt_irrefl.
Qed.

Lemma le_anti: antisymmetric leb.
Proof.
by move=> x y /andP[] /lebP xy /lebP /(Z.le_antisymm _ _ xy)/to_Z_inj.
Qed.

Lemma le_trans : transitive leb.
Proof. by move=> x y z /lebP yx /lebP /(Z.le_trans _ _ _ yx) /lebP. Qed.

Lemma le_total : total leb.
Proof.
move=> x y; case: (Z.le_ge_cases (to_Z x) (to_Z y)) => /lebP -> //; exact/orbT.
Qed.

Lemma le_to_nat : {mono to_nat : x y / (x <=? y) >-> (x <= y)%O}.
Proof.
move=> x y.
case: (to_Z_bounded x) (to_Z_bounded y) => x0 _ [] y0 _.
by apply/ssrnat.leP/lebP => /Z2Nat.inj_le; apply.
Qed.

Lemma le0x x : 0 <=? x.
Proof. by apply/lebP; case: (to_Z_bounded x). Qed.

Lemma lex1 x : x <=? 9223372036854775807.
Proof. by apply/lebP; case: (to_Z_bounded x) => _ /Z.lt_le_pred. Qed.

End Order.

Fact uint63_display : Order.disp_t. Proof. split; exact/tt. Qed.

HB.instance Definition _ :=
  Order.isOrder.Build uint63_display uint63 Order.lt_def (fun x y => erefl)
    (fun x y => erefl) Order.le_anti Order.le_trans Order.le_total.

HB.instance Definition _ :=
  Order.hasBottom.Build uint63_display uint63 Order.le0x.
HB.instance Definition _ :=
  Order.hasTop.Build uint63_display uint63 Order.lex1.

HB.instance Definition _ := Order.isOrderEmbedding.Build
  uint63_display uint63 Order.NatOrder.nat_display nat to_nat Order.le_to_nat.

Lemma ltuS {i j : uint63} : (i < j -> i < i + 1)%O.
Proof.
case: (to_Z_bounded i) (to_Z_bounded j) => i0 _ [] j0 jwB.
rewrite -!(oembedding_lt to_nat) => /ssrnat.ltP/inj_lt.
rewrite !Z2Nat.id// => /Ztac.Zlt_le_add_1 ij.
rewrite /={2}/to_nat/= add_spec Z.mod_small.
  rewrite Z2Nat.inj_add// Nat.add_1_r.
  by rewrite /Order.lt/=.
split; first exact/Z.add_nonneg_nonneg.
exact: Z.le_lt_trans jwB.
Qed.

Lemma lt_predu (x y : uint63) : (x < y -> (y - 1 : uint63) < y)%O.
Proof.
rewrite -!(oembedding_lt to_nat) => xy/=.
suff ->: to_nat (y - 1) = (to_nat y).-1.
  by rewrite /Order.lt/= prednK//; apply/(leq_ltn_trans _ xy).
rewrite /=/to_nat/= sub_spec -Znat.Z2Nat.inj_pred BinInt.Z.sub_1_r.
rewrite Zdiv.Zmod_small//.
case: (to_Z_bounded y) => y0 /BinInt.Z.lt_lt_pred ywB.
split=> //.
apply/BinInt.Z.lt_le_pred/Znat.Z2Nat.inj_lt => //=.
exact/ssrnat.ltP/(leq_ltn_trans _ xy).
Qed.

Module Ring.

Lemma addrA : associative add.
Proof.
move=> x y z; rewrite -[LHS]of_to_Z -[RHS]of_to_Z; congr of_Z.
by rewrite !add_spec Zplus_mod_idemp_r Zplus_mod_idemp_l Z.add_assoc.
Qed.

Lemma addrC : commutative add.
Proof.
move=> x y; rewrite -[LHS]of_to_Z -[RHS]of_to_Z; congr of_Z.
by rewrite !add_spec Z.add_comm.
Qed.

Lemma add0r : left_id 0 add.
Proof.
move=> x; rewrite -[LHS]of_to_Z add_spec/= Z.mod_small.
  by rewrite of_to_Z.
exact/to_Z_bounded.
Qed.

Lemma addNr : left_inverse 0 opp add.
Proof.
move=> x; rewrite -[LHS]of_to_Z add_spec/= opp_spec.
by rewrite Zplus_mod Zmod_mod -Zplus_mod Z.add_opp_diag_l.
Qed.

Lemma mulrA : associative mul.
Proof.
move=> x y z; rewrite -[LHS]of_to_Z -[RHS]of_to_Z; congr of_Z.
by rewrite !mul_spec Zmult_mod_idemp_r Zmult_mod_idemp_l Z.mul_assoc.
Qed.

Lemma mulrC : commutative mul.
Proof.
move=> x y.
rewrite -[LHS]of_to_Z -[RHS]of_to_Z; congr of_Z.
by rewrite !mul_spec Z.mul_comm.
Qed.

Lemma mul1r : left_id 1 mul.
Proof.
move=> x; rewrite -[LHS]of_to_Z (mul_spec 1 x) Z.mul_1_l Z.mod_small.
  by rewrite of_to_Z.
exact/to_Z_bounded.
Qed.

Lemma mulrDl : left_distributive mul add.
Proof.
move=> x y z; rewrite -[LHS]of_to_Z -[RHS]of_to_Z add_spec !mul_spec !add_spec.
rewrite Zplus_mod_idemp_l Zplus_mod_idemp_r Zmult_mod_idemp_l.
by rewrite Z.mul_add_distr_r.
Qed.

Lemma oner_neq0 : is_true (1 != 0 :> uint63). Proof. by []. Qed.

End Ring.

HB.instance Definition _ :=
  GRing.isZmodule.Build uint63 Ring.addrA Ring.addrC Ring.add0r Ring.addNr.
HB.instance Definition _ :=
  GRing.Zmodule_isComRing.Build uint63
    Ring.mulrA Ring.mulrC Ring.mul1r Ring.mulrDl Ring.oner_neq0.

Lemma to_natD x y : to_nat (x + y) = ((to_nat x + to_nat y) %% 2 ^ size)%N.
Proof.
case: (to_Z_bounded x) => x0 _; case: (to_Z_bounded y) => y0 _.
rewrite [LHS]/= [LHS]/to_nat add_spec wBE Z2Nat.inj_mod.
- by rewrite Nat2Z.id modnE Z2Nat.inj_add.
- exact: Z.add_nonneg_nonneg.
- exact: Nat2Z.is_nonneg.
Qed.

Lemma additive_of_nat : GRing.semi_additive of_nat.
Proof. by split=> // x y; apply/to_natI; rewrite to_natD !of_natK modnDm. Qed.

HB.instance Definition _ :=
  GRing.isSemiAdditive.Build _ _ of_nat additive_of_nat.

Lemma to_nat_top : to_nat \top%O = (2 ^ size).-1.
Proof.
suff ->: \top%O = of_nat (2 ^ size).-1.
  by rewrite of_natK modn_small ?prednK ?leqnn.
have: (2 ^ size).-1.+1 = 2 ^ size by rewrite prednK.
move: _.-1 => n nE.
apply: (addrI (of_nat 1)); rewrite -[RHS](raddfD of_nat).
rewrite -[RHS]of_nat_modn.
by rewrite [(1%N + _)%R]add1n nE modnn.
Qed.

Lemma ltWlel (x y : uint63) : (x < y -> (x + 1 : uint63) <= y)%O.
Proof.
move=> /[dup] xy; rewrite -(oembedding_lt to_nat) -(oembedding_le to_nat)/=.
congr (_ <= _)%N; rewrite to_natD addn1 modn_small//.
rewrite -ltn_predRL -to_nat_top.
(* Hack to prevent Qed from computing `to_nat \top` *)
move: \top%O (lex1 y) => top xle.
rewrite [_ < _](oembedding_lt to_nat).
exact/(lt_le_trans xy).
Qed.

Lemma ltWler (x y : uint63) : (x < y + 1 -> x <= y)%O.
Proof.
case: (ltP y \top%O) => [ylt|]; last by rewrite le1x => /eqP ->.
move=> /[dup] xy; rewrite -(oembedding_lt to_nat) -(oembedding_le to_nat)/=.
rewrite to_natD addn1 modn_small; first by [].
rewrite -ltn_predRL -to_nat_top.
by move: \top%O ylt => top; rewrite -(oembedding_lt to_nat).
Qed.

Lemma to_natM x y : to_nat (x * y) = ((to_nat x * to_nat y) %% 2 ^ size)%N.
Proof.
case: (to_Z_bounded x) => x0 _; case: (to_Z_bounded y) => y0 _.
rewrite [LHS]/= [LHS]/to_nat mul_spec wBE Z2Nat.inj_mod.
- by rewrite Nat2Z.id modnE Z2Nat.inj_mul.
- exact: Z.mul_nonneg_nonneg.
- exact: Nat2Z.is_nonneg.
Qed.

Lemma multiplicative_of_nat : GRing.multiplicative of_nat.
Proof. by split=> // x y; apply/to_natI; rewrite to_natM !of_natK modnMm. Qed.

(* Program Fixpoint is too painful, let's use Acc instead. *)
(* FIXME: `comparable_leP` will probably block the extraction. *)
Fixpoint iteri_subdef (T : Type) (n : uint63) (f : uint63 -> T -> T)
  (x : T) (i : uint63) (acc : Acc (fun x y => y < x)%O i) {struct acc} :=
  (if (i < n)%O as b return (i < n)%O = b -> T then
    fun ilt => iteri_subdef n f (f i x) (Acc_inv acc (ltuS ilt))
  else fun=> x) erefl.

Lemma gt_wf (n : uint63) : Acc (fun x y : uint63 => y < x)%O n.
Proof.
(* Hack to prevent Qed from computing `to_nat \top` *)
move: \top%O (@lex1 _ uint63) (@le1x _ uint63) (@lt1x _ uint63).
move=> top lex1 le1x lt1x.
move kE: (to_nat top - (to_nat n))%N => k.
apply: Acc_intro.
elim: k n kE => [n /eqP|k IHk n /(congr1 predn) + y ny].
  rewrite subn_eq0 [_ <= _](oembedding_le to_nat) le1x => /eqP -> y.
  by rewrite lt1x.
rewrite succnK -subnS -[(to_nat n).+1]addn1.
move: (to_natD n 1); rewrite modn_small; last first.
  rewrite addn1 -ltn_predRL -to_nat_top.
  have ->: \top%O = top.
    by apply/le_anti; rewrite Order.TPOrderTheory.lex1 lex1.
  rewrite [_ < _](oembedding_lt to_nat).
  exact/(lt_le_trans ny).
move=> <- /IHk {}IHk.
move: ny => /ltWlel; rewrite le_eqVlt => /orP[/eqP <-|]; last exact: IHk.
exact: Acc_intro.
Qed.

Definition iteri (T : Type) (n : uint63) (f : uint63 -> T -> T) (x : T) :=
  iteri_subdef n f x (gt_wf 0).

(* TOTHINK: What I really need is `n < n+1`. *)
Lemma iteriS (T : Type) (n : uint63) (f : uint63 -> T -> T) (x : T) :
  (n < \top)%O -> iteri (n+1) f x = f n (iteri n f x).
Proof.
move=> /ltuS nlt; rewrite /iteri -[0]to_natK [X in X 0]/to_nat/= -(subnn (to_nat n)).
move: (gt_wf _) {1}(gt_wf _) x.
have: (to_nat n - to_nat n <= to_nat n)%N by rewrite subnn.
elim: {2 5 7 9 11}(to_nat n) => [_|k].
  rewrite subn0 to_natK => -[] accn [] accn'/= x.
  move: erefl; rewrite {2 3}nlt => {}nlt.
  move: erefl; rewrite {2 3}ltxx => _.
  case: (accn' _ _) => accnS/=.
  by move: erefl; rewrite {2 3}ltxx => _.
rewrite subnS; case: (to_nat n - k)%N => [//|{}k/= IHk kn] [] acck []acck'/= x.
have kT : k < 2 ^ size.
  apply/(leq_ltn_trans kn)/ssrnat.ltP/Nat2Z.inj_lt.
  case: (to_Z_bounded n) => n0 nwB.
  by rewrite -wBE /to_nat Z2Nat.id.
move: kn IHk.
rewrite -{1 2}(modn_small kT) -of_natK [_ <= _](oembedding_le to_nat) => kn. 
rewrite [_ < _](oembedding_lt to_nat) => IHk.
move: erefl; rewrite {2 3}(le_lt_trans kn nlt) => kn'.
move: kn; rewrite le_eqVlt => /orP[/eqP knE|klt].
  move: erefl; rewrite {2 7}knE ltxx => _.
  case: (acck' _ _) => acckS/=.
  by move: erefl; rewrite {2 3}knE ltxx knE.
move: erefl; rewrite {2 3}klt => klt'.
move: (acck' _ _) (acck _ _).
suff ->: of_nat k + 1 = of_nat k.+1 by move=> acck'S acckS; exact: IHk.
rewrite /of_nat Nat2Z.inj_succ -Z.add_1_r.
apply/(ssrfun.can_inj of_to_Z).
by rewrite add_spec !of_Z_spec Zplus_mod_idemp_l.
Qed.

Lemma iteriE (T : Type) (n : uint63) (f : uint63 -> T -> T) (x : T) :
  iteri n f x = ssrnat.iteri (to_nat n) (f \o of_nat) x.
Proof.
rewrite -{1}(to_natK n).
move: (lex1 n); rewrite -(oembedding_le to_nat)/=.
elim: (to_nat n) => [_|k IHk]/=.
  by rewrite /iteri; case: (gt_wf 0) => acc0/=.
rewrite /Order.le/= => klt.
rewrite -addn1 raddfD/=.
rewrite -(IHk (ltnW klt)) iteriS// -(oembedding_lt to_nat)/= of_natK.
exact/(leq_ltn_trans _ klt)/leq_mod.
Qed.

Lemma iteri_ind (T : Type) (P : uint63 -> T -> Prop)
    (n : uint63) (f : uint63 -> T -> T) (x : T) :
  P 0 x -> (forall y (m : uint63), (m < n)%O -> P m y -> P (m+1) (f m y)) ->
  P n (iteri n f x).
Proof.
move=> Px Pf.
have {Pf}: forall (y : T) m , (to_nat m < to_nat n) -> P m y -> P (m+1) (f m y).
  by move=> y m mn; apply: Pf; rewrite -(oembedding_lt to_nat)/=.
rewrite iteriE -{1}[X in P X]to_natK; elim: (to_nat n) => //= k IHk Pf.
rewrite -addn1 raddfD/=.
apply/Pf; first by rewrite of_natK ltnS leq_mod.
by apply: IHk => y m mk; apply/Pf/(leq_trans mk).
Qed.

Lemma iteri_ind2 (T U : Type) (P : uint63 -> T -> U -> Prop)
    (n : uint63) (f : uint63 -> T -> T) (g : uint63 -> U -> U) (x : T) (y : U):
  P 0 x y ->
  (forall x' y' (m : uint63), (m < n)%O -> P m x' y' -> P (m+1) (f m x') (g m y')) ->
  P n (iteri n f x) (iteri n g y).
Proof.
move=> Px Pf.
have {Pf}: forall x' y' m , (to_nat m < to_nat n) -> P m x' y' -> P (m+1) (f m x') (g m y').
  by move=> x' y' m mn; apply: Pf; rewrite -(oembedding_lt to_nat)/=.
rewrite !iteriE -{1}[X in P X]to_natK; elim: (to_nat n) => //= k IHk Pf.
rewrite -addn1 raddfD/=.
apply/Pf; first by rewrite of_natK ltnS leq_mod.
by apply: IHk => x' y' m mk; apply/Pf/(leq_trans mk).
Qed.

Lemma eq_iteri (T : Type) (n : uint63) (f g : uint63 -> T -> T) (x : T) :
  (forall i, (i < n)%O -> f i =1 g i) -> iteri n f x = iteri n g x.
Proof.
move=> /= fg.
apply: (iteri_ind2 (P:=fun _ x y => x = y)) => // x' y' m mn ->.
exact: fg.
Qed.

Lemma iteri_id (T : Type) (n : uint63) (x : T) : iteri n (fun=> id) x = x.
Proof. exact: (iteri_ind (P:=fun _ y => y = x)). Qed.

Definition all (n : uint63) (P : uint63 -> bool) :=
  iteri n (fun i b => b && P i) true.

Lemma allP n (P : uint63 -> bool) :
  reflect (forall i, (i < n)%O -> P i) (all n P).
Proof.
rewrite /all; apply/Bool.iff_reflect.
apply (iteri_ind (P:=fun m x => (forall i, (i < m)%O -> P i) <-> x = true)).
  by split=> // _ i; rewrite ltx0.
case=> /= m mn IHm; split=> //.
- by move=> /(_ m (ltuS mn)).
- move=> Pm i /ltWler; rewrite le_eqVlt => /orP[/eqP -> //|].
  by case: IHm => _; apply.
- by move=> IHm'; apply/IHm => i im; apply/IHm'/(lt_trans im (ltuS mn)).
Qed.

Definition has (n : uint63) (P : uint63 -> bool) :=
  iteri n (fun i b => b || P i) false.

Lemma hasP n (P : uint63 -> bool) :
  reflect (exists i, (i < n)%O && P i) (has n P).
Proof.
rewrite /all; apply/Bool.iff_reflect.
apply (iteri_ind (P:=fun m x => (exists i, (i < m)%O && P i) <-> x = true)).
  by split=> // -[] i; rewrite ltx0.
case=> /= m mn IHm; split=> //.
- case: IHm => _ /(_ erefl)[] i /andP[] im Pi _; exists i.
  apply/andP; split=> //.
  exact/(lt_trans im (ltuS mn)).
- case=> i /andP[] /ltWler; rewrite le_eqVlt => /orP[/eqP -> //|im Pi].
  by case: IHm => /(_ _)/wrap[]//; exists i; apply/andP.
- by move=> Pm; exists m; apply/andP; split=> //; apply: (ltuS mn).
Qed.
  
