
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From elpi Require Import elpi.

Section Permutations.

Variable T : eqType.
Implicit Types (x : T) (s t : seq T) (bs : seq (T * nat)) (acc : seq (seq T)).

Fixpoint incr_tally bs x :=
  if bs isn't b :: bs then [:: (x, 1)] else
  if x == b.1 then (x, b.2.+1) :: bs else b :: incr_tally bs x.

Definition tally s := foldl incr_tally [::] s.

Definition wf_tally :=
  [qualify a bs : seq (T * nat) | uniq (unzip1 bs) && (0 \notin unzip2 bs)].

Definition tally_seq bs := flatten [seq nseq b.2 b.1 | b <- bs].
Local Notation tseq := tally_seq.

Lemma size_tally_seq bs : size (tally_seq bs) = sumn (unzip2 bs).
Proof.
by rewrite size_flatten /shape -map_comp; under eq_map do rewrite /= size_nseq.
Qed.

Lemma tally_seqK : {in wf_tally, cancel tally_seq tally}.
Proof.
move=> bs /andP[]; elim: bs => [|[x [|n]] bs IHbs] //= /andP[bs'x Ubs] bs'0.
rewrite inE /tseq /tally /= -[n.+1]addn1 in bs'0 *.
elim: n 1 => /= [|n IHn] m; last by rewrite eqxx IHn addnS.
rewrite -{}[in RHS]IHbs {Ubs bs'0}// /tally /tally_seq add0n.
elim: bs bs'x [::] => [|[y n] bs IHbs] //= /[1!inE] /norP[y'x bs'x].
by elim: n => [|n IHn] bs1 /=; [rewrite IHbs | rewrite eq_sym ifN // IHn].
Qed.

Lemma incr_tallyP x : {homo incr_tally^~ x : bs / bs \in wf_tally}.
Proof.
move=> bs /andP[]; rewrite unfold_in.
elim: bs => [|[y [|n]] bs IHbs] //= /andP[bs'y Ubs] /[1!inE] /= bs'0.
have [<- | y'x] /= := eqVneq y; first by rewrite bs'y Ubs.
rewrite -andbA {}IHbs {Ubs bs'0}// andbT.
elim: bs bs'y => [|b bs IHbs] /=; rewrite inE ?y'x // => /norP[b'y bs'y].
by case: ifP => _; rewrite /= inE negb_or ?y'x // b'y IHbs.
Qed.

Lemma tallyP s : tally s \is a wf_tally.
Proof.
rewrite /tally; set bs := [::]; have: bs \in wf_tally by [].
by elim: s bs => //= x s IHs bs /(incr_tallyP x)/IHs.
Qed.

Lemma tallyK s : perm_eq (tally_seq (tally s)) s.
Proof.
rewrite -[s in perm_eq _ s]cats0 -[nil]/(tseq [::]) /tally.
elim: s [::] => //= x s IHs bs; rewrite {IHs}(permPl (IHs _)).
rewrite perm_sym -cat1s perm_catCA {s}perm_cat2l.
elim: bs => //= b bs IHbs; case: eqP => [-> | _] //=.
by rewrite -cat1s perm_catCA perm_cat2l.
Qed.

Lemma tallyEl s : perm_eq (unzip1 (tally s)) (undup s).
Proof.
have /andP[Ubs bs'0] := tallyP s; set bs := tally s in Ubs bs'0 *.
rewrite uniq_perm ?undup_uniq {Ubs}// => x.
rewrite mem_undup -(perm_mem (tallyK s)) -/bs.
elim: bs => [|[y [|m]] bs IHbs] //= in bs'0 *.
by rewrite inE IHbs // mem_cat mem_nseq.
Qed.
Elpi Query foo lp:{{
coq.say "anchor".
}}.
Lemma tallyE s : perm_eq (tally s) [seq (x, count_mem x s) | x <- undup s].
Proof.
have /andP[Ubs _] := tallyP s; pose b := [fun s x => (x, count_mem x (tseq s))].
Set Debug "elpi-unification".
Set Debug "elpi".
Elpi Debug.
suffices : perm_eq (tally s) (map (b (tally s)) (unzip1 (tally s))).
AHA.
  congr perm_eq: (perm_map (b (tally s)) (tallyEl s)).
  by under eq_map do rewrite /= (permP (tallyK s)).
elim: (tally s) Ubs => [|[x m] bs IH] //= /andP[bs'x /IH-IHbs {IH}].
rewrite /tseq /= -/(tseq _) count_cat count_nseq /= eqxx mul1n.
rewrite (count_memPn _) ?addn0 ?perm_cons; last first.
  apply: contra bs'x; elim: {b IHbs}bs => //= b bs IHbs.
  by rewrite mem_cat mem_nseq inE andbC; case: (_ == _).
congr perm_eq: IHbs; apply/eq_in_map=> y bs_y; congr (y, _).
by rewrite count_cat count_nseq /= (negPf (memPnC bs'x y bs_y)).
Qed.

Lemma perm_tally s1 s2 : perm_eq s1 s2 -> perm_eq (tally s1) (tally s2).
Proof.
move=> eq_s12; apply: (@perm_trans _ [seq (x, count_mem x s2) | x <- undup s1]).
  by congr perm_eq: (tallyE s1); under eq_map do rewrite (permP eq_s12).
by rewrite (permPr (tallyE s2)); apply/perm_map/perm_undup/(perm_mem eq_s12).
Qed.

Lemma perm_tally_seq bs1 bs2 :
  perm_eq bs1 bs2 -> perm_eq (tally_seq bs1) (tally_seq bs2).
Proof. by move=> Ebs12; rewrite perm_flatten ?perm_map. Qed.
Local Notation perm_tseq := perm_tally_seq.

Lemma perm_count_undup s :
  perm_eq (flatten [seq nseq (count_mem x s) x | x <- undup s]) s.
Proof.
by rewrite -(permPr (tallyK s)) (permPr (perm_tseq (tallyE s))) /tseq -map_comp.
Qed.

Local Fixpoint cons_perms_ perms_rec (s : seq T) bs bs2 acc :=
  if bs isn't b :: bs1 then acc else
  if b isn't (x, m.+1) then cons_perms_ perms_rec s bs1 bs2 acc else
  let acc_xs := perms_rec (x :: s) ((x, m) :: bs1 ++ bs2) acc in
  cons_perms_ perms_rec s bs1 (b :: bs2) acc_xs.

Local Fixpoint perms_rec n s bs acc :=
  if n isn't n.+1 then s :: acc else cons_perms_ (perms_rec n) s bs [::] acc.
Local Notation cons_perms n := (cons_perms_ (perms_rec n) [::]).

Definition permutations s := perms_rec (size s) [::] (tally s) [::].

Let permsP s : exists n bs,
   [/\ permutations s = perms_rec n [::] bs [::],
       size (tseq bs) == n, perm_eq (tseq bs) s & uniq (unzip1 bs)].
Proof.
have /andP[Ubs _] := tallyP s; exists (size s), (tally s).
by rewrite (perm_size (tallyK s)) tallyK.
Qed.

Local Notation bsCA := (permEl (perm_catCA _ [:: _] _)).
Let cons_permsE : forall n x bs bs1 bs2,
  let cp := cons_perms n bs bs2 in let perms s := perms_rec n s bs1 [::] in
  cp (perms [:: x]) = cp [::] ++ [seq rcons t x | t <- perms [::]].
Proof.
pose is_acc f := forall acc, f acc = f [::] ++ acc. (* f is accumulating. *)
have cpE: forall f & forall s bs, is_acc (f s bs), is_acc (cons_perms_ f _ _ _).
  move=> s bs bs2 f fE acc; elim: bs => [|[x [|m]] bs IHbs] //= in s bs2 acc *.
  by rewrite fE IHbs catA -IHbs.
have prE: is_acc (perms_rec _ _ _) by elim=> //= n IHn s bs; apply: cpE.
pose has_suffix f := forall s : seq T, f s = [seq t ++ s | t <- f [::]].
suffices prEs n bs: has_suffix (fun s => perms_rec n s bs [::]).
  move=> n x bs bs1 bs2 /=; rewrite cpE // prEs.
  by under eq_map do rewrite cats1.
elim: n bs => //= n IHn bs s; elim: bs [::] => [|[x [|m]] bs IHbs] //= bs1.
rewrite cpE // IHbs IHn [in RHS]cpE // [in RHS]IHn map_cat -map_comp.
by congr (_ ++ _); apply: eq_map => t /=; rewrite -catA.
Qed.

Lemma mem_permutations s t : (t \in permutations s) = perm_eq t s.
Proof.
have{s} [n [bs [-> Dn /permPr<- _]]] := permsP s.
elim: n => [|n IHn] /= in t bs Dn *.
  by rewrite inE (nilP Dn); apply/eqP/perm_nilP.
rewrite -[bs in tseq bs]cats0 in Dn *; have x0 : T by case: (tseq _) Dn.
rewrite -[RHS](@andb_idl (last x0 t \in tseq bs)); last first.
  case/lastP: t {IHn} => [|t x] Dt; first by rewrite -(perm_size Dt) in Dn.
  by rewrite -[bs]cats0 -(perm_mem Dt) last_rcons mem_rcons mem_head.
elim: bs [::] => [|[x [|m]] bs IHbs] //= bs2 in Dn *.
rewrite cons_permsE -!cat_cons !mem_cat (mem_nseq m.+1) orbC andb_orl.
rewrite {}IHbs ?(perm_size (perm_tseq bsCA)) //= (permPr (perm_tseq bsCA)).
congr (_ || _); apply/mapP/andP=> [[t1 Dt1 ->] | [/eqP]].
  by rewrite last_rcons perm_rcons perm_cons IHn in Dt1 *.
case/lastP: t => [_ /perm_size//|t y]; rewrite last_rcons perm_rcons => ->.
by rewrite perm_cons; exists t; rewrite ?IHn.
Qed.

Lemma permutations_uniq s : uniq (permutations s).
Proof.
have{s} [n [bs [-> Dn _ Ubs]]] := permsP s.
elim: n => //= n IHn in bs Dn Ubs *; rewrite -[bs]cats0 /unzip1 in Dn Ubs.
elim: bs [::] => [|[x [|m]] bs IHbs] //= bs2 in Dn Ubs *.
  by case/andP: Ubs => _ /IHbs->.
rewrite /= cons_permsE cat_uniq has_sym andbCA andbC.
rewrite {}IHbs; first 1 last; first by rewrite (perm_size (perm_tseq bsCA)).
  by rewrite (perm_uniq (perm_map _ bsCA)).
rewrite (map_inj_uniq (rcons_injl x)) {}IHn {Dn}//=.
have: x \notin unzip1 bs by apply: contraL Ubs; rewrite map_cat mem_cat => ->.
move: {bs2 m Ubs}(perms_rec n _ _ _) (_ :: bs2) => ts.
elim: bs => [|[y [|m]] bs IHbs] //= /[1!inE] bs2 /norP[x'y /IHbs//].
rewrite cons_permsE has_cat negb_or has_map => ->.
by apply/hasPn=> t _; apply: contra x'y => /mapP[t1 _ /rcons_inj[_ ->]].
Qed.

Notation perms := permutations.
Lemma permutationsE s :
    0 < size s ->
  perm_eq (perms s) [seq x :: t | x <- undup s, t <- perms (rem x s)].
Proof.
move=> nt_s; apply/uniq_perm=> [||t]; first exact: permutations_uniq.
  apply/allpairs_uniq_dep=> [|x _|]; rewrite ?undup_uniq  ?permutations_uniq //.
  by case=> [_ _] [x t] _ _ [-> ->].
rewrite mem_permutations; apply/idP/allpairsPdep=> [Dt | [x [t1 []]]].
  rewrite -(perm_size Dt) in nt_s; case: t nt_s => // x t _ in Dt *.
  have s_x: x \in s by rewrite -(perm_mem Dt) mem_head.
  exists x, t; rewrite mem_undup mem_permutations; split=> //.
  by rewrite -(perm_cons x) (permPl Dt) perm_to_rem.
rewrite mem_undup mem_permutations -(perm_cons x) => s_x Dt1 ->.
by rewrite (permPl Dt1) perm_sym perm_to_rem.
Qed.

Lemma permutationsErot x s (le_x := fun t => iota 0 (index x t + 1)) :
  perm_eq (perms (x :: s)) [seq rot i (x :: t) | t <- perms s, i <- le_x t].
Proof.
have take'x t i: i <= index x t -> i <= size t /\ x \notin take i t.
  move=> le_i_x; have le_i_t: i <= size t := leq_trans le_i_x (index_size x t).
  case: (nthP x) => // -[j lt_j_i /eqP]; rewrite size_takel // in lt_j_i.
  by rewrite nth_take // [_ == _](before_find x (leq_trans lt_j_i le_i_x)).
pose xrot t i := rot i (x :: t); pose xrotV t := index x (rev (rot 1 t)).
have xrotK t: {in le_x t, cancel (xrot t) xrotV}.
  move=> i; rewrite mem_iota addn1 /xrotV => /take'x[le_i_t ti'x].
  rewrite -rotD ?rev_cat //= rev_cons cat_rcons index_cat mem_rev size_rev.
  by rewrite ifN // size_takel //= eqxx addn0.
apply/uniq_perm=> [||t]; first exact: permutations_uniq.
  apply/allpairs_uniq_dep=> [|t _|]; rewrite ?permutations_uniq ?iota_uniq //.
  move=> _ _ /allpairsPdep[t [i [_ ? ->]]] /allpairsPdep[u [j [_ ? ->]]] Etu.
  have Eij: i = j by rewrite -(xrotK t i) // /xrot Etu xrotK.
  by move: Etu; rewrite Eij => /rot_inj[->].
rewrite mem_permutations; apply/esym; apply/allpairsPdep/idP=> [[u [i]] | Dt].
  rewrite mem_permutations => -[Du _ /(canLR (rotK i))]; rewrite /rotr.
  by set j := (j in rot j _) => Dt; apply/perm_consP; exists j, u.
pose r := rev (rot 1 t); pose i := index x r; pose u := rev (take i r).
have r_x: x \in r by rewrite mem_rev mem_rot (perm_mem Dt) mem_head.
have [v Duv]: {v | rot i (x :: u ++ v) = t}; first exists (rev (drop i.+1 r)).
  rewrite -rev_cat -rev_rcons -rot1_cons -cat_cons -(nth_index x r_x).
  by rewrite -drop_nth ?index_mem // rot_rot !rev_rot revK rotK rotrK.
exists (u ++ v), i; rewrite mem_permutations -(perm_cons x) -(perm_rot i) Duv.
rewrite mem_iota addn1 ltnS /= index_cat mem_rev size_rev.
by have /take'x[le_i_t ti'x] := leqnn i; rewrite ifN ?size_takel ?leq_addr.
Qed.

Lemma size_permutations s : uniq s -> size (permutations s) = (size s)`!.
Proof.
move Dn: (size s) => n Us; elim: n s => [[]|n IHn s] //= in Dn Us *.
rewrite (perm_size (permutationsE _)) ?Dn // undup_id // factS -Dn.
rewrite -(size_iota 0 n`!) -(size_allpairs (fun=>id)) !size_allpairs_dep.
by apply/congr1/eq_in_map=> x sx; rewrite size_iota IHn ?size_rem ?Dn ?rem_uniq.
Qed.

Lemma permutations_all_uniq s : uniq s -> all uniq (permutations s).
Proof.
by move=> Us; apply/allP=> t; rewrite mem_permutations => /perm_uniq->.
Qed.

Lemma perm_permutations s t :
  perm_eq s t -> perm_eq (permutations s) (permutations t).
Proof.
move=> Est; apply/uniq_perm; try exact: permutations_uniq.
by move=> u; rewrite !mem_permutations (permPr Est).
Qed.

End Permutations.

Section AllIff.
(* The Following Are Equivalent *)

(* We introduce a specific conjunction, used to chain the consecutive *)
(* items in a circular list of implications *)
Inductive all_iff_and (P Q : Prop) : Prop := AllIffConj of P & Q.

Definition all_iff (P0 : Prop) (Ps : seq Prop) : Prop :=
  let fix loop (P : Prop) (Qs : seq Prop) : Prop :=
    if Qs is Q :: Qs then all_iff_and (P -> Q) (loop Q Qs) else P -> P0 in
  loop P0 Ps.

Lemma all_iffLR P0 Ps : all_iff P0 Ps ->
  forall m n, nth P0 (P0 :: Ps) m -> nth P0 (P0 :: Ps) n.
Proof.
move=> iffPs; have PsS n: nth P0 Ps n -> nth P0 Ps n.+1.
  elim: n P0 Ps iffPs => [|n IHn] P0 [|P [|Q Ps]] //= [iP0P] //; first by case.
    by rewrite nth_nil.
  by case=> iPQ iffPs; apply: IHn; split=> // /iP0P.
have{PsS} lePs: {homo nth P0 Ps : m n / m <= n >-> (m -> n)}.
  by move=> m n /subnK<-; elim: {n}(n - m) => // n IHn /IHn; apply: PsS.
move=> m n P_m; have{m P_m} hP0: P0.
  case: m P_m => //= m /(lePs m _ (leq_maxl m (size Ps))).
  by rewrite nth_default ?leq_maxr.
case: n =>// n; apply: lePs 0 n (leq0n n) _.
by case: Ps iffPs hP0 => // P Ps [].
Qed.

Lemma all_iffP P0 Ps :
   all_iff P0 Ps -> forall m n, nth P0 (P0 :: Ps) m <-> nth P0 (P0 :: Ps) n.
Proof. by move=> /all_iffLR-iffPs m n; split => /iffPs. Qed.

End AllIff.
Arguments all_iffLR {P0 Ps}.
Arguments all_iffP {P0 Ps}.
Coercion all_iffP : all_iff >-> Funclass.

(* This means "the following are all equivalent: P0, ... Pn" *)
Notation "[ '<->' P0 ; P1 ; .. ; Pn ]" :=
  (all_iff P0 (@cons Prop P1 (.. (@cons Prop Pn nil) ..))) : form_scope.

Ltac tfae := do !apply: AllIffConj.
