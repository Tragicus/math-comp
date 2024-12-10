(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import div choice fintype tuple finfun bigop prime.
From mathcomp Require Import ssralg poly polydiv ssrnum ssrint archimedean rat.
From mathcomp Require Import finalg zmodp matrix mxalgebra mxpoly vector intdiv.
From mathcomp Require Import falgebra fieldext separable galois algC cyclotomic.

(******************************************************************************)
(* This file provides a few basic results and constructions in algebraic      *)
(* number theory, that are used in the character theory library. Most of      *)
(* these could be generalized to a more abstract setting. Note that the type  *)
(* of abstract number fields is simply extFieldType rat. We define here:      *)
(*  x \in Crat_span X <=> x is a Q-linear combination of elements of          *)
(*                        X : seq algC.                                       *)
(*  x \in Cint_span X <=> x is a Z-linear combination of elements of          *)
(*                        X : seq algC.                                       *)
(*         x \in Aint <=> x : algC is an algebraic integer, i.e., the (monic) *)
(*                        polynomial of x over Q has integer coefficients.    *)
(*         (e %| a)%A <=> e divides a with respect to algebraic integers,     *)
(*        (e %| a)%Ax     i.e., a is in the algebraic integer ideal generated *)
(*                        by e. This is is notation for a \in dvdA e, where   *)
(*                        dvdv is the (collective) predicate for the Aint     *)
(*                        ideal generated by e. As in the (e %| a)%C notation *)
(*                        e and a can be coerced to algC from nat or int.     *)
(*                        The (e %| a)%Ax display form is a workaround for    *)
(*                        design limitations of the Coq Notation facilities.  *)
(* (a == b %[mod e])%A, (a != b %[mod e])%A <=>                               *)
(*                       a is equal (resp. not equal) to b mod e, i.e., a and *)
(*                       b belong to the same e * Aint class. We do not       *)
(*                       force a, b and e to be algebraic integers.           *)
(*            #[x]%C == the multiplicative order of x, i.e., the n such that  *)
(*                      x is an nth primitive root of unity, or 0 if x is not *)
(*                      a root of unity.                                      *)
(* In addition several lemmas prove the (constructive) existence of number    *)
(* fields and of automorphisms of algC.                                       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope algC_scope.
Declare Scope algC_expanded_scope.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Local Notation ZtoQ := (intr : int -> rat).
Local Notation ZtoC := (intr : int -> algC).
Local Notation QtoC := (ratr : rat -> algC).

Local Notation intrp := (map_poly intr).
Local Notation pZtoQ := (map_poly ZtoQ).
Local Notation pZtoC := (map_poly ZtoC).
Local Notation pQtoC := (map_poly ratr).

Local Definition intr_inj_ZtoC := (intr_inj : injective ZtoC).
#[local] Hint Resolve intr_inj_ZtoC : core.

Section MoreAlgCaut.

Implicit Type rR : unitRingType.

Lemma alg_num_field (Qz : fieldExtType rat) a : a%:A = ratr a :> Qz.
Proof. by rewrite -in_algE fmorph_eq_rat. Qed.

Lemma rmorphZ_num (Qz : fieldExtType rat) rR (f : {rmorphism Qz -> rR}) a x :
  f (a *: x) = ratr a * f x.
Proof. by rewrite -mulr_algl rmorphM alg_num_field fmorph_rat. Qed.

Lemma fmorph_numZ (Qz1 Qz2 : fieldExtType rat) (f : {rmorphism Qz1 -> Qz2}) :
  scalable f.
Proof. by move=> a x; rewrite rmorphZ_num -alg_num_field mulr_algl. Qed.

End MoreAlgCaut.

(* Number fields and rational spans. *)
Lemma algC_PET (s : seq algC) :
  {z | exists a : nat ^ size s, z = \sum_(i < size s) s`_i *+ a i
     & exists ps, s = [seq (pQtoC p).[z] | p <- ps]}.
Proof.
elim: s => [|x s [z /sig_eqW[a Dz] /sig_eqW[ps Ds]]].
  by exists 0; [exists [ffun _ => 2%N]; rewrite big_ord0 | exists nil].
have r_exists (y : algC): {r | r != 0 & root (pQtoC r) y}.
  have [r [_ mon_r] dv_r] := minCpolyP y.
  by exists r; rewrite ?monic_neq0 ?dv_r.
suffices /sig_eqW[[n [|px [|pz []]]]// [Dpx Dpz]]:
  exists np, let zn := x *+ np.1 + z in
    [:: x; z] = [seq (pQtoC p).[zn] | p <- np.2].
- exists (x *+ n + z).
    exists [ffun i => oapp a n (unlift ord0 i)].
    rewrite /= big_ord_recl ffunE unlift_none Dz; congr (_ + _).
    by apply: eq_bigr => i _; rewrite ffunE liftK.
  exists (px :: [seq p \Po pz | p <- ps]); rewrite /= -Dpx; congr (_ :: _).
  rewrite -map_comp Ds; apply: eq_map => p /=.
  by rewrite map_comp_poly horner_comp -Dpz.
have [rx nz_rx rx0] := r_exists x.
have [rz nz_rz rz0] := r_exists (- z).
have pchar0_Q: [pchar rat] =i pred0 by apply: pchar_num.
have [n [[pz Dpz] [px Dpx]]] := pchar0_PET nz_rz rz0 nz_rx rx0 pchar0_Q.
by exists (n, [:: px; - pz]); rewrite /= !raddfN hornerN -[z]opprK Dpz Dpx.
Qed.

Lemma num_field_exists (s : seq algC) :
  {Qs : fieldExtType rat & {QsC : {rmorphism Qs -> algC}
   & {s1 : seq Qs | map QsC s1 = s & <<1 & s1>>%VS = fullv}}}.
Proof.
have [z /sig_eqW[a Dz] /sig_eqW[ps Ds]] := algC_PET s.
suffices [Qs [QsC [z1 z1C z1gen]]]:
  {Qs : fieldExtType rat & {QsC : {rmorphism Qs -> algC} &
     {z1 : Qs | QsC z1 = z & forall xx, exists p, fieldExt_horner z1 p = xx}}}.
- set inQs := fieldExt_horner z1 in z1gen *; pose s1 := map inQs ps.
  have inQsK p: QsC (inQs p) = (pQtoC p).[z].
    rewrite /= -horner_map z1C -map_poly_comp; congr _.[z].
    by apply: eq_map_poly => b /=; rewrite alg_num_field fmorph_rat.
  exists Qs, QsC, s1; first by rewrite -map_comp Ds (eq_map inQsK).
  have sz_ps: size ps = size s by rewrite Ds size_map.
  apply/vspaceP=> x; rewrite memvf; have [p {x}<-] := z1gen x.
  elim/poly_ind: p => [|p b ApQs]; first by rewrite /inQs rmorph0 mem0v.
  rewrite /inQs rmorphD rmorphM /= fieldExt_hornerX fieldExt_hornerC -/inQs /=.
  suffices ->: z1 = \sum_(i < size s) s1`_i *+ a i.
    rewrite memvD ?memvZ ?mem1v ?memvM ?memv_suml // => i _.
    by rewrite rpredMn ?seqv_sub_adjoin ?mem_nth // size_map sz_ps.
  apply: (fmorph_inj QsC); rewrite z1C Dz rmorph_sum; apply: eq_bigr => i _.
  by rewrite rmorphMn {1}Ds !(nth_map 0) ?sz_ps //= inQsK.
have [r [Dr /monic_neq0 nz_r] dv_r] := minCpolyP z.
have rz0: root (pQtoC r) z by rewrite dv_r.
have irr_r: irreducible_poly r.
  by apply/(subfx_irreducibleP rz0 nz_r)=> q qz0 nzq; rewrite dvdp_leq // -dv_r.
exists (SubFieldExtType rz0 irr_r), (@subfx_inj _ _ QtoC z r).
exists (subfx_root _ z r) => [|x]; first exact: subfx_inj_root.
by have{x} [p ->] := subfxEroot rz0 nz_r x; exists p.
Qed.

Definition in_Crat_span s x :=
  exists a : rat ^ size s, x = \sum_i QtoC (a i) * s`_i.

Fact Crat_span_subproof s x : decidable (in_Crat_span s x).
Proof.
have [Qxs [QxsC [[|x1 s1] // [<- <-] {x s} _]]] := num_field_exists (x :: s).
apply: decP (x1 \in <<in_tuple s1>>%VS) _; rewrite /in_Crat_span size_map.
apply: (iffP idP) => [/coord_span-> | [a Dx]].
  move: (coord _) => a; exists [ffun i => a i x1]; rewrite rmorph_sum /=.
  by apply: eq_bigr => i _; rewrite ffunE rmorphZ_num (nth_map 0).
have{Dx} ->: x1 = \sum_i a i *: s1`_i.
  apply: (fmorph_inj QxsC); rewrite Dx rmorph_sum /=.
  by apply: eq_bigr => i _; rewrite rmorphZ_num (nth_map 0).
by apply: memv_suml => i _; rewrite memvZ ?memv_span ?mem_nth.
Qed.

Definition Crat_span s : pred algC := Crat_span_subproof s.
Lemma Crat_spanP s x : reflect (in_Crat_span s x) (x \in Crat_span s).
Proof. exact: sumboolP. Qed.

Lemma mem_Crat_span s : {subset s <= Crat_span s}.
Proof.
move=> _ /(nthP 0)[ix ltxs <-]; pose i0 := Ordinal ltxs.
apply/Crat_spanP; exists [ffun i => (i == i0)%:R].
rewrite (bigD1_ord i0) //= ffunE eqxx // rmorph1 mul1r.
by rewrite big1 ?addr0 // => i; rewrite ffunE rmorph_nat mulr_natl lift_eqF.
Qed.

Fact Crat_span_zmod_closed s : zmod_closed (Crat_span s).
Proof.
split=> [|_ _ /Crat_spanP[x ->] /Crat_spanP[y ->]].
  apply/Crat_spanP; exists 0.
  by apply/esym/big1=> i _; rewrite ffunE rmorph0 mul0r.
apply/Crat_spanP; exists (x - y); rewrite -sumrB; apply: eq_bigr => i _.
by rewrite -mulrBl -rmorphB !ffunE.
Qed.
HB.instance Definition _ s := GRing.isZmodClosed.Build _ (Crat_span s)
  (Crat_span_zmod_closed s).

Section NumFieldProj.

Variables (Qn : fieldExtType rat) (QnC : {rmorphism Qn -> algC}).

Lemma Crat_spanZ b a : {in Crat_span b, forall x, ratr a * x \in Crat_span b}.
Proof.
move=> _ /Crat_spanP[a1 ->]; apply/Crat_spanP; exists [ffun i => a * a1 i].
by rewrite mulr_sumr; apply: eq_bigr => i _; rewrite ffunE mulrA -rmorphM.
Qed.

Lemma Crat_spanM b : {in Crat & Crat_span b, forall a x, a * x \in Crat_span b}.
Proof. by move=> _ x /CratP[a ->]; apply: Crat_spanZ. Qed.

(* In principle CtoQn could be taken to be additive and Q-linear, but this    *)
(* would require a limit construction.                                        *)
Lemma num_field_proj : {CtoQn | CtoQn 0 = 0 & cancel QnC CtoQn}.
Proof.
pose b := vbasis {:Qn}.
have Qn_bC (u : {x | x \in Crat_span (map QnC b)}): {y | QnC y = sval u}.
  case: u => _ /= /Crat_spanP/sig_eqW[a ->].
  exists (\sum_i a i *: b`_i); rewrite rmorph_sum /=; apply: eq_bigr => i _.
  by rewrite rmorphZ_num (nth_map 0) // -(size_map QnC).
pose CtoQn x := oapp (fun u => sval (Qn_bC u)) 0 (insub x).
suffices QnCK: cancel QnC CtoQn by exists CtoQn; rewrite // -(rmorph0 QnC) /=.
move=> x; rewrite /CtoQn insubT => /= [|Qn_x]; last first.
  by case: (Qn_bC _) => x1 /= /fmorph_inj.
rewrite (coord_vbasis (memvf x)) rmorph_sum rpred_sum //= => i _.
rewrite rmorphZ_num Crat_spanZ ?mem_Crat_span // -/b.
by rewrite -tnth_nth -tnth_map mem_tnth.
Qed.

Lemma restrict_aut_to_num_field (nu : {rmorphism algC -> algC}) :
    (forall x, exists y, nu (QnC x) = QnC y) ->
  {nu0 : {lrmorphism Qn -> Qn} | {morph QnC : x / nu0 x >-> nu x}}.
Proof.
move=> Qn_nu; pose nu0 x := sval (sig_eqW (Qn_nu x)).
have QnC_nu0: {morph QnC : x / nu0 x >-> nu x}.
  by rewrite /nu0 => x; case: (sig_eqW _).
have nu0a : additive nu0.
  by move=> x y; apply: (fmorph_inj QnC); rewrite !(QnC_nu0, rmorphB).
have nu0m : multiplicative nu0.
  split=> [x y|]; apply: (fmorph_inj QnC); rewrite ?QnC_nu0 ?rmorph1 //.
  by rewrite !rmorphM /= !QnC_nu0.
pose nu0aM := GRing.isAdditive.Build Qn Qn nu0 nu0a.
pose nu0mM := GRing.isMultiplicative.Build Qn Qn nu0 nu0m.
pose nu0RM : {rmorphism _ -> _} := HB.pack nu0 nu0aM nu0mM.
pose nu0lM := GRing.isScalable.Build rat Qn Qn *:%R nu0 (fmorph_numZ nu0RM).
pose nu0LRM : {lrmorphism _ -> _} := HB.pack nu0 nu0aM nu0mM nu0lM.
by exists nu0LRM.
Qed.

Lemma map_Qnum_poly (nu : {rmorphism algC -> algC}) p :
  p \in polyOver 1%VS -> map_poly (nu \o QnC) p = (map_poly QnC p).
Proof.
move=> Qp; apply/polyP=> i; rewrite /= !coef_map /=.
have /vlineP[a ->]: p`_i \in 1%VS by apply: polyOverP.
by rewrite alg_num_field !fmorph_rat.
Qed.

End NumFieldProj.

Lemma restrict_aut_to_normal_num_field (Qn : splittingFieldType rat)
  (QnC : {rmorphism Qn -> algC})(nu : {rmorphism algC -> algC}) :
    {nu0 : {lrmorphism Qn -> Qn} | {morph QnC : x / nu0 x >-> nu x}}.
Proof.
apply: restrict_aut_to_num_field => x.
case: (splitting_field_normal 1%AS x) => rs /eqP Hrs.
have: root (map_poly (nu \o QnC) (minPoly 1%AS x)) (nu (QnC x)).
  by rewrite fmorph_root root_minPoly.
rewrite map_Qnum_poly ?minPolyOver // Hrs.
rewrite [map_poly _ _](_:_ = \prod_(y <- map QnC rs) ('X - y%:P)).
  by rewrite root_prod_XsubC; case/mapP => y _ ?; exists y.
by rewrite big_map rmorph_prod /=; apply: eq_bigr => i _; rewrite map_polyXsubC.
Qed.

(* Integral spans. *)

Lemma dec_Cint_span (V : vectType algC) m (s : m.-tuple V) v :
  decidable (inIntSpan s v).
Proof.
have s_s (i : 'I_m): s`_i \in <<s>>%VS by rewrite memv_span ?memt_nth.
have s_Zs a: \sum_(i < m) s`_i *~ a i \in <<s>>%VS.
  by rewrite memv_suml // => i _; rewrite -scaler_int memvZ.
case s_v: (v \in <<s>>%VS); last by right=> [[a Dv]]; rewrite Dv s_Zs in s_v.
pose IzT := {: 'I_m * 'I_(\dim <<s>>)}; pose Iz := 'I_#|IzT|.
pose b := vbasis <<s>>.
pose z_s := [seq coord b ij.2 (tnth s ij.1) | ij : IzT].
pose rank2 j i: Iz := enum_rank (i, j); pose val21 (p : Iz) := (enum_val p).1.
pose inQzs w := [forall j, Crat_span z_s (coord b j w)].
have enum_pairK j: {in predT, cancel (rank2 j) val21}.
  by move=> i; rewrite /val21 enum_rankK.
have Qz_Zs a: inQzs (\sum_(i < m) s`_i *~ a i).
  apply/forallP=> j; apply/Crat_spanP; rewrite /in_Crat_span size_map -cardE.
  exists [ffun ij => (a (val21 ij))%:Q *+ ((enum_val ij).2 == j)].
  rewrite linear_sum {1}(reindex_onto _ _ (enum_pairK j)) big_mkcond /=.
  apply: eq_bigr => ij _ /=; rewrite nth_image (tnth_nth 0) ffunE /val21.
  rewrite raddfMz rmorphMn rmorph_int mulrnAl mulrzl /=.
  rewrite (can2_eq (@enum_rankK _) (@enum_valK _)).
  by case: (enum_val ij) => i j1; rewrite xpair_eqE eqxx; have [->|] := eqVneq.
case Qz_v: (inQzs v); last by right=> [[a Dv]]; rewrite Dv Qz_Zs in Qz_v.
have [Qz [QzC [z1s Dz_s _]]] := num_field_exists z_s.
have sz_z1s: size z1s = #|IzT| by rewrite -(size_map QzC) Dz_s size_map cardE.
have xv j: {x | coord b j v = QzC x}.
  apply: sig_eqW; have /Crat_spanP[x ->] := forallP Qz_v j.
  exists (\sum_ij x ij *: z1s`_ij); rewrite rmorph_sum; apply: eq_bigr => ij _.
  by rewrite rmorphZ_num -[in RHS](nth_map _ 0) ?Dz_s // -(size_map QzC) Dz_s.
pose sz := [tuple [ffun j => z1s`_(rank2 j i)] | i < m].
have [Zsv | Zs'v] := dec_Qint_span sz [ffun j => sval (xv j)].
  left; have{Zsv} [a Dv] := Zsv; exists a.
  transitivity (\sum_j \sum_(i < m) QzC ((sz`_i *~ a i) j) *: b`_j).
    rewrite {1}(coord_vbasis s_v) -/b; apply: eq_bigr => j _.
    rewrite -scaler_suml; congr (_ *: _).
    have{Dv} /ffunP/(_ j) := Dv; rewrite sum_ffunE !ffunE -rmorph_sum => <-.
    by case: (xv j).
  rewrite exchange_big; apply: eq_bigr => i _.
  rewrite (coord_vbasis (s_s i)) -/b mulrz_suml; apply: eq_bigr => j _.
  rewrite scalerMzl ffunMzE rmorphMz; congr ((_ *~ _) *: _).
  rewrite nth_mktuple ffunE -(nth_map _ 0) ?sz_z1s // Dz_s.
  by rewrite nth_image enum_rankK /= (tnth_nth 0).
right=> [[a Dv]]; case: Zs'v; exists a.
apply/ffunP=> j; rewrite sum_ffunE !ffunE; apply: (fmorph_inj QzC).
case: (xv j) => /= _ <-; rewrite Dv linear_sum rmorph_sum /=.
apply: eq_bigr => i _; rewrite nth_mktuple raddfMz !ffunMzE rmorphMz ffunE.
by rewrite -(nth_map _ 0 QzC) ?sz_z1s // Dz_s nth_image enum_rankK -tnth_nth.
Qed.

Definition Cint_span (s : seq algC) : pred algC :=
  fun x => dec_Cint_span (in_tuple [seq \row_(i < 1) y | y <- s]) (\row_i x).

Lemma Cint_spanP n (s : n.-tuple algC) x :
  reflect (inIntSpan s x) (x \in Cint_span s).
Proof.
rewrite unfold_in; case: (dec_Cint_span _ _) => [Zs_x | Zs'x] /=.
  left; have{Zs_x} [] := Zs_x; rewrite /= size_map size_tuple => a /rowP/(_ 0).
  rewrite !mxE => ->; exists a; rewrite summxE; apply: eq_bigr => i _.
  by rewrite -scaler_int (nth_map 0) ?size_tuple // !mxE mulrzl.
right=> [[a Dx]]; have{Zs'x} [] := Zs'x.
rewrite /inIntSpan /= size_map size_tuple; exists a.
apply/rowP=> i0; rewrite !mxE summxE Dx; apply: eq_bigr => i _.
by rewrite -scaler_int mxE mulrzl (nth_map 0) ?size_tuple // !mxE.
Qed.

Lemma mem_Cint_span s : {subset s <= Cint_span s}.
Proof.
move=> _ /(nthP 0)[ix ltxs <-]; apply/(Cint_spanP (in_tuple s)).
exists [ffun i => i == Ordinal ltxs : int].
rewrite (bigD1 (Ordinal ltxs)) //= ffunE eqxx.
by rewrite big1 ?addr0 // => i; rewrite ffunE => /negbTE->.
Qed.

Lemma Cint_span_zmod_closed s : zmod_closed (Cint_span s).
Proof.
have sP := Cint_spanP (in_tuple s); split=> [|_ _ /sP[x ->] /sP[y ->]].
  by apply/sP; exists 0; rewrite big1 // => i; rewrite ffunE.
apply/sP; exists (x - y); rewrite -sumrB; apply: eq_bigr => i _.
by rewrite !ffunE raddfB.
Qed.
HB.instance Definition _ s := GRing.isZmodClosed.Build _ (Cint_span s)
  (Cint_span_zmod_closed s).

(* Automorphism extensions. *)
Lemma extend_algC_subfield_aut (Qs : fieldExtType rat)
  (QsC : {rmorphism Qs -> algC}) (phi : {rmorphism Qs -> Qs}) :
  {nu : {rmorphism algC -> algC} | {morph QsC : x / phi x >-> nu x}}.
Proof.
pose numF_inj (Qr : fieldExtType rat) := {rmorphism Qr -> algC}.
pose subAut := {Qr : _ & numF_inj Qr * {lrmorphism Qr -> Qr}}%type.
pose SubAut := existT _ _ (_, _) : subAut.
pose Sdom (mu : subAut) := projT1 mu.
pose Sinj (mu : subAut) : {rmorphism Sdom mu -> algC} := (projT2 mu).1.
pose Saut (mu : subAut) : {rmorphism Sdom mu -> Sdom mu} := (projT2 mu).2.
have Sinj_poly Qr (QrC : numF_inj Qr) p:
  map_poly QrC (map_poly (in_alg Qr) p) = pQtoC p.
- rewrite -map_poly_comp; apply: eq_map_poly => a.
  by rewrite /= rmorphZ_num rmorph1 mulr1.
have ext1 mu0 x : {mu1 | exists y, x = Sinj mu1 y
  & exists2 in01 : {lrmorphism _ -> _}, Sinj mu0 =1 Sinj mu1 \o in01
  & {morph in01: y / Saut mu0 y >-> Saut mu1 y}}.
- pose b0 := vbasis {:Sdom mu0}.
  have [z _ /sig_eqW[[|px ps] // [Dx Ds]]] := algC_PET (x :: map (Sinj mu0) b0).
  have [p [_ mon_p] /(_ p) pz0] := minCpolyP z; rewrite dvdpp in pz0.
  have [r Dr] := closed_field_poly_normal (pQtoC p : {poly algC}).
  rewrite lead_coef_map {mon_p}(monicP mon_p) rmorph1 scale1r in Dr.
  have{pz0} rz: z \in r by rewrite -root_prod_XsubC -Dr.
  have [Qr [QrC [rr Drr genQr]]] := num_field_exists r.
  have{rz} [zz Dz]: {zz | QrC zz = z}.
    by move: rz; rewrite -Drr => /mapP/sig2_eqW[zz]; exists zz.
  have{ps Ds} [in01 Din01]:
      {in01 : {lrmorphism _ -> _} | Sinj mu0 =1 QrC \o in01}.
    have in01P y: {yy | Sinj mu0 y = QrC yy}.
      exists (\sum_i coord b0 i y *: (map_poly (in_alg Qr) ps`_i).[zz]).
      rewrite {1}(coord_vbasis (memvf y)) !rmorph_sum /=; apply: eq_bigr => i _.
      rewrite 2!rmorphZ_num -(nth_map _ 0) ?size_tuple // Ds.
      rewrite -horner_map Dz Sinj_poly (nth_map 0) //.
      by have:= congr1 size Ds; rewrite !size_map size_tuple => <-.
    pose in01 y := sval (in01P y).
    have Din01 y: Sinj mu0 y = QrC (in01 y) by rewrite /in01; case: (in01P y).
    pose rwM := (=^~ Din01, rmorphZ_num, rmorph1, rmorphB, rmorphM).
    have in01a : additive in01.
      by move=> ? ?; apply: (fmorph_inj QrC); rewrite !rwM.
    have in01m : multiplicative in01.
      by split; try move=> ? ?; apply: (fmorph_inj QrC); rewrite !rwM /= ?rwM.
    have in01l : scalable in01.
      by try move=> ? ?; apply: (fmorph_inj QrC); rewrite !rwM.
    pose in01aM := GRing.isAdditive.Build _ _ in01 in01a.
    pose in01mM := GRing.isMultiplicative.Build _ _ in01 in01m.
    pose in01lM := GRing.isScalable.Build _ _  _ _ in01 in01l.
    pose in01LRM : {lrmorphism _ -> _} := HB.pack in01
      in01aM in01mM in01lM.
    by exists in01LRM.
  have {z zz Dz px} Dx: exists xx, x = QrC xx.
    exists (map_poly (in_alg Qr) px).[zz].
    by rewrite -horner_map Dz Sinj_poly Dx.
  pose lin01 := linfun in01; pose K := (lin01 @: fullv)%VS.
  have memK y: reflect (exists yy, y = in01 yy) (y \in K).
    apply: (iffP memv_imgP) => [[yy _ ->] | [yy ->]];
      by exists yy; rewrite ?lfunE ?memvf.
  have algK: is_aspace K.
    rewrite /is_aspace has_algid1; last first.
      by apply/memK; exists 1; rewrite rmorph1.
    apply/prodvP=> _ _ /memK[y1 ->] /memK[y2 ->].
    by apply/memK; exists (y1 * y2); rewrite rmorphM.
  have ker_in01: lker lin01 == 0%VS.
    by apply/lker0P=> y1 y2; rewrite !lfunE; apply: fmorph_inj.
  pose f := (lin01 \o linfun (Saut mu0) \o lin01^-1)%VF.
  have Df y: f (in01 y) = in01 (Saut mu0 y).
    transitivity (f (lin01 y)); first by rewrite !lfunE.
    by do 4!rewrite lfunE /=; rewrite lker0_lfunK.
  have hom_f: kHom 1 (ASpace algK) f.
    apply/kHomP; split=> [_ _ /memK[y1 ->] /memK[y2 ->] |_ /vlineP[a ->]].
      by rewrite -rmorphM !Df !rmorphM.
    by rewrite -(rmorph_alg in01) Df /= !rmorph_alg.
  pose pr := map_poly (in_alg Qr) p.
  have Qpr: pr \is a polyOver 1%VS.
    by apply/polyOverP=> i; rewrite coef_map memvZ ?memv_line.
  have splitQr: splittingFieldFor K pr fullv.
    apply: splittingFieldForS (sub1v (Sub K algK)) (subvf _) _; exists rr => //.
    congr (_ %= _): (eqpxx pr); apply/(map_poly_inj QrC).
    rewrite Sinj_poly Dr -Drr big_map rmorph_prod /=; apply: eq_bigr => zz _.
    by rewrite map_polyXsubC.
  have [f1 aut_f1 Df1]:= kHom_extends (sub1v (ASpace algK)) hom_f Qpr splitQr.
  pose f1mM := GRing.isMultiplicative.Build _ _ f1 (kHom_lrmorphism aut_f1).
  pose nu : {lrmorphism _ -> _} := HB.pack (fun_of_lfun f1) f1mM.
  exists (SubAut Qr QrC nu) => //; exists in01 => //= y.
  by rewrite -Df -Df1 //; apply/memK; exists y.
have phiZ: scalable phi.
  by move=> a y; rewrite rmorphZ_num -alg_num_field mulr_algl.
pose philM := GRing.isScalable.Build _ _ _ _ phi phiZ.
pose phiLRM : {lrmorphism _ -> _} := HB.pack (GRing.RMorphism.sort phi) philM.
pose fix ext n :=
  if n is i.+1 then oapp (fun x => s2val (ext1 (ext i) x)) (ext i) (unpickle i)
  else SubAut Qs QsC phiLRM.
have mem_ext x n: (pickle x < n)%N -> {xx | Sinj (ext n) xx = x}.
  move=> ltxn; apply: sig_eqW; elim: n ltxn => // n IHn.
  rewrite ltnS leq_eqVlt => /predU1P[<- | /IHn[xx <-]] /=.
    by rewrite pickleK /=; case: (ext1 _ x) => mu [xx]; exists xx.
  case: (unpickle n) => /= [y|]; last by exists xx.
  case: (ext1 _ y) => mu /= _ [in_mu inj_in_mu _].
  by exists (in_mu xx); rewrite inj_in_mu.
pose nu x := Sinj _ (Saut _ (sval (mem_ext x _ (ltnSn _)))).
have nu_inj n y: nu (Sinj (ext n) y) = Sinj (ext n) (Saut (ext n) y).
  rewrite /nu; case: (mem_ext _ _ _); move: _.+1 => n1 y1 Dy /=.
  without loss /subnK Dn1: n n1 y y1 Dy / (n <= n1)%N.
    by move=> IH; case/orP: (leq_total n n1) => /IH => [/(_ y) | /(_ y1)]->.
  move: (n1 - n)%N => k in Dn1; elim: k => [|k IHk] in n Dn1 y Dy *.
    by move: y1 Dy; rewrite -Dn1 => y1  /fmorph_inj ->.
  rewrite addSnnS in Dn1; move/IHk: Dn1 => /=.
  case: (unpickle _) => [z|] /=; last exact.
  case: (ext1 _ _) => mu /= _ [in_mu Dinj Daut].
  by rewrite Dy => /(_ _ (Dinj _))->; rewrite -Daut Dinj.
pose le_nu (x : algC) n := (pickle x < n)%N.
have max3 x1 x2 x3: exists n, [/\ le_nu x1 n, le_nu x2 n & le_nu x3 n].
  exists (maxn (pickle x1) (maxn (pickle x2) (pickle x3))).+1.
  by apply/and3P; rewrite /le_nu !ltnS -!geq_max.
have nua : additive nu.
  move=> x1 x2; have [n] := max3 (x1 - x2) x1 x2.
  case=> /mem_ext[y Dx] /mem_ext[y1 Dx1] /mem_ext[y2 Dx2].
  rewrite -Dx nu_inj; rewrite -Dx1 -Dx2 -rmorphB in Dx.
  by rewrite (fmorph_inj _ Dx) !rmorphB -!nu_inj Dx1 Dx2.
have num : multiplicative nu.
  split=> [x1 x2|]; last by rewrite -(rmorph1 QsC) (nu_inj 0) !rmorph1.
  have [n] := max3 (x1 * x2) x1 x2.
  case=> /mem_ext[y Dx] /mem_ext[y1 Dx1] /mem_ext[y2 Dx2].
  rewrite -Dx nu_inj; rewrite -Dx1 -Dx2 -rmorphM in Dx.
  by rewrite (fmorph_inj _ Dx) !rmorphM /= -!nu_inj Dx1 Dx2.
pose nuaM := GRing.isAdditive.Build _ _ nu nua.
pose numM := GRing.isMultiplicative.Build _ _ nu num.
pose nuRM : {rmorphism _ -> _} := HB.pack nu nuaM numM.
by exists nuRM => x; rewrite /= (nu_inj 0).
Qed.

(* Extended automorphisms of Q_n. *)
Lemma Qn_aut_exists k n :
    coprime k n ->
  {u : {rmorphism algC -> algC} | forall z, z ^+ n = 1 -> u z = z ^+ k}.
Proof.
have [-> /eqnP | n_gt0 co_k_n] := posnP n.
  by rewrite gcdn0 => ->; exists idfun.
have [z prim_z] := C_prim_root_exists n_gt0.
have [Qn [QnC [[|zn []] // [Dz]]] genQn] := num_field_exists [:: z].
pose phi := kHomExtend 1 \1 zn (zn ^+ k).
have homQn1: kHom 1 1 (\1%VF : 'End(Qn)) by rewrite kHom1.
have pzn_zk0: root (map_poly \1%VF (minPoly 1 zn)) (zn ^+ k).
  rewrite -(fmorph_root QnC) rmorphXn /= Dz -map_poly_comp.
  rewrite (@eq_map_poly _ _ _ QnC) => [|a]; last by rewrite /= id_lfunE.
  set p1 := map_poly _ _.
  have [q1 Dp1]: exists q1, p1 = pQtoC q1.
    have aP i: (minPoly 1 zn)`_i \in 1%VS.
      by apply/polyOverP; apply: minPolyOver.
    have{aP} a_ i := sig_eqW (vlineP _ _ (aP i)).
    exists (\poly_(i < size (minPoly 1 zn)) sval (a_ i)).
    apply/polyP=> i; rewrite coef_poly coef_map coef_poly /=.
    case: ifP => _; rewrite ?rmorph0 //; case: (a_ i) => a /= ->.
    by rewrite alg_num_field fmorph_rat.
  have: root p1 z by rewrite -Dz fmorph_root root_minPoly.
  rewrite Dp1; have [q2 [Dq2 _] ->] := minCpolyP z.
  case/dvdpP=> r1 ->; rewrite rmorphM rootM /= -Dq2; apply/orP; right.
  rewrite (minCpoly_cyclotomic prim_z) /cyclotomic.
  rewrite (bigD1 (Ordinal (ltn_pmod k n_gt0))) ?coprime_modl //=.
  by rewrite rootM root_XsubC prim_expr_mod ?eqxx.
have phim : multiplicative phi.
  by apply/kHom_lrmorphism; rewrite -genQn span_seq1 /= kHomExtendP.
pose phimM := GRing.isMultiplicative.Build _ _ phi phim.
pose phiRM : {rmorphism _ -> _} := HB.pack (fun_of_lfun phi) phimM.
have [nu Dnu] := extend_algC_subfield_aut QnC phiRM.
exists nu => _ /(prim_rootP prim_z)[i ->].
rewrite rmorphXn /= exprAC -Dz -Dnu /= -{1}[zn]hornerX /phi.
rewrite (kHomExtend_poly homQn1) ?polyOverX //.
rewrite map_polyE map_id_in => [|?]; last by rewrite id_lfunE.
by rewrite polyseqK hornerX rmorphXn.
Qed.

(* Algebraic integers. *)

Definition Aint : {pred algC} := fun x => minCpoly x \is a polyOver Num.int.

Lemma root_monic_Aint p x :
  root p x -> p \is monic -> p \is a polyOver Num.int -> x \in Aint.
Proof.
have pZtoQtoC pz: pQtoC (pZtoQ pz) = pZtoC pz.
  by rewrite -map_poly_comp; apply: eq_map_poly => b; rewrite /= rmorph_int.
move=> px0 mon_p /floorpP[pz Dp]; rewrite unfold_in.
move: px0; rewrite Dp -pZtoQtoC; have [q [-> mon_q] ->] := minCpolyP x.
case/dvdpP_rat_int=> qz [a nz_a Dq] [r].
move/(congr1 (fun q1 => lead_coef (a *: pZtoQ q1))).
rewrite rmorphM scalerAl -Dq lead_coefZ lead_coefM /=.
have /monicP->: pZtoQ pz \is monic by rewrite -(map_monic QtoC) pZtoQtoC -Dp.
rewrite (monicP mon_q) mul1r mulr1 lead_coef_map_inj //; last exact: intr_inj.
rewrite Dq => ->; apply/polyOverP=> i; rewrite !(coefZ, coef_map).
by rewrite -rmorphM /= rmorph_int.
Qed.

Lemma Cint_rat_Aint z : z \in Crat -> z \in Aint -> z \in Num.int.
Proof.
case/CratP=> a ->{z} /polyOverP/(_ 0).
have [p [Dp mon_p] dv_p] := minCpolyP (ratr a); rewrite Dp coef_map.
suffices /eqP->: p == 'X - a%:P by rewrite polyseqXsubC /= rmorphN rpredN.
rewrite -eqp_monic ?monicXsubC // irredp_XsubC //.
  by rewrite -(size_map_poly QtoC) -Dp neq_ltn size_minCpoly orbT.
by rewrite -dv_p fmorph_root root_XsubC.
Qed.

Lemma Aint_Cint : {subset Num.int <= Aint}.
Proof.
move=> x; rewrite -polyOverXsubC.
by apply: root_monic_Aint; rewrite ?monicXsubC ?root_XsubC.
Qed.

Lemma Aint_int x : x%:~R \in Aint. Proof. by rewrite Aint_Cint. Qed.

Lemma Aint0 : 0 \in Aint. Proof. exact: Aint_int 0. Qed.
Lemma Aint1 : 1 \in Aint. Proof. exact: Aint_int 1. Qed.
#[global] Hint Resolve Aint0 Aint1 : core.

Lemma Aint_unity_root n x : (n > 0)%N -> n.-unity_root x -> x \in Aint.
Proof.
move=> n_gt0 xn1; apply: root_monic_Aint xn1 (monicXnsubC _ n_gt0) _.
by apply/polyOverP=> i; rewrite coefB coefC -mulrb coefXn /= rpredB ?rpred_nat.
Qed.

Lemma Aint_prim_root n z : n.-primitive_root z -> z \in Aint.
Proof.
move=> pr_z; apply/(Aint_unity_root (prim_order_gt0 pr_z))/unity_rootP.
exact: prim_expr_order.
Qed.

Lemma Aint_Cnat : {subset Num.nat <= Aint}.
Proof. by move=> z /intr_nat/Aint_Cint. Qed.

(* This is Isaacs, Lemma (3.3) *)
Lemma Aint_subring_exists (X : seq algC) :
    {subset X <= Aint} ->
  {S : pred algC &
     (*a*) subring_closed S
  /\ (*b*) {subset X <= S}
   & (*c*) {Y : {n : nat & n.-tuple algC} &
                {subset tagged Y <= S}
              & forall x, reflect (inIntSpan (tagged Y) x) (x \in S)}}.
Proof.
move=> AZ_X; pose m := (size X).+1.
pose n (i : 'I_m) := (size (minCpoly X`_i)).-2; pose N := (\max_i n i).+1.
pose IY := family (fun i => [pred e : 'I_N | e <= n i]%N).
have IY_0: 0 \in IY by apply/familyP=> // i; rewrite ffunE.
pose inIY := enum_rank_in IY_0.
pose Y := [seq \prod_(i < m) X`_i ^+ (f : 'I_N ^ m) i | f in IY].
have S_P := Cint_spanP [tuple of Y]; set S := Cint_span _ in S_P.
have sYS: {subset Y <= S} by apply: mem_Cint_span.
have S_1: 1 \in S.
  by apply/sYS/imageP; exists 0 => //; rewrite big1 // => i; rewrite ffunE.
have SmulX (i : 'I_m): {in S, forall x, x * X`_i \in S}.
  move=> _ /S_P[x ->]; rewrite mulr_suml rpred_sum // => j _.
  rewrite mulrzAl rpredMz {x}// nth_image mulrC (bigD1 i) //= mulrA -exprS.
  move: {j}(enum_val j) (familyP (enum_valP j)) => f fP.
  have:= fP i; rewrite inE /= leq_eqVlt => /predU1P[-> | fi_ltn]; last first.
    apply/sYS/imageP; have fiK: (inord (f i).+1 : 'I_N) = (f i).+1 :> nat.
      by rewrite inordK // ltnS (bigmax_sup i).
    exists (finfun [eta f with i |-> inord (f i).+1]).
      apply/familyP=> i1; rewrite inE ffunE /= fun_if fiK.
      by case: eqP => [-> // | _]; apply: fP.
    rewrite (bigD1 i isT) ffunE /= eqxx fiK; congr (_ * _).
    by apply: eq_bigr => i1 /[!ffunE]/= /negPf->.
  have [/monicP ] := (minCpoly_monic X`_i, root_minCpoly X`_i).
  rewrite /root horner_coef lead_coefE -(subnKC (size_minCpoly _)) subn2.
  rewrite big_ord_recr /= addrC addr_eq0 => ->; rewrite mul1r => /eqP->.
  have /floorpP[p Dp]: X`_i \in Aint.
    by have [/(nth_default 0)-> | /(mem_nth 0)/AZ_X] := leqP (size X) i.
  rewrite -/(n i) Dp mulNr rpredN // mulr_suml rpred_sum // => [[e le_e]] /= _.
  rewrite coef_map -mulrA mulrzl rpredMz ?sYS //; apply/imageP.
  have eK: (inord e : 'I_N) = e :> nat by rewrite inordK // ltnS (bigmax_sup i).
  exists (finfun [eta f with i |-> inord e]).
    apply/familyP=> i1; rewrite inE ffunE /= fun_if eK.
    by case: eqP => [-> // | _]; apply: fP.
  rewrite (bigD1 i isT) ffunE /= eqxx eK; congr (_ * _).
  by apply: eq_bigr => i1 /[!ffunE] /= /negPf->.
exists S; last by exists (Tagged (fun n => n.-tuple _) [tuple of Y]).
split=> [|x Xx]; last first.
  by rewrite -[x]mul1r -(nth_index 0 Xx) (SmulX (Ordinal _)) // ltnS index_size.
split=> // x y Sx Sy; first by rewrite rpredB.
case/S_P: Sy => {y}[y ->]; rewrite mulr_sumr rpred_sum //= => j.
rewrite mulrzAr rpredMz {y}// nth_image; move: {j}(enum_val j) => f.
elim/big_rec: _ => [|i y _ IHy] in x Sx *; first by rewrite mulr1.
rewrite mulrA {y}IHy //.
elim: {f}(f i : nat) => [|e IHe] in x Sx *; first by rewrite mulr1.
by rewrite exprS mulrA IHe // SmulX.
Qed.

Section AlgIntSubring.

(* This is Isaacs, Theorem (3.4). *)
Theorem fin_Csubring_Aint S n (Y : n.-tuple algC) :
     mulr_closed S -> (forall x, reflect (inIntSpan Y x) (x \in S)) ->
  {subset S <= Aint}.
Proof.
move=> mulS.
pose Sm := GRing.isMulClosed.Build _ _ mulS.
pose SC : mulrClosed _ := HB.pack S Sm.
have ZP_C c: (ZtoC c)%:P \is a polyOver Num.int_num_subdef.
  by rewrite raddfMz rpred_int.
move=> S_P x Sx; pose v := \row_(i < n) Y`_i.
have [v0 | nz_v] := eqVneq v 0.
  case/S_P: Sx => {}x ->; rewrite big1 ?isAlgInt0 // => i _.
  by have /rowP/(_ i)/[!mxE] -> := v0; rewrite mul0rz.
have sYS (i : 'I_n): x * Y`_i \in SC.
  by rewrite rpredM //; apply/S_P/Cint_spanP/mem_Cint_span/memt_nth.
pose A := \matrix_(i, j < n) sval (sig_eqW (S_P _ (sYS j))) i.
pose p := char_poly (map_mx ZtoC A).
have: p \is a polyOver Num.int_num_subdef.
  rewrite rpred_sum // => s _; rewrite rpredMsign rpred_prod // => j _.
  by rewrite !mxE /= rpredB ?rpredMn ?polyOverX.
apply: root_monic_Aint (char_poly_monic _).
rewrite -eigenvalue_root_char; apply/eigenvalueP; exists v => //.
apply/rowP=> j; case dAj: (sig_eqW (S_P _ (sYS j))) => [a DxY].
by rewrite !mxE DxY; apply: eq_bigr => i _; rewrite !mxE dAj /= mulrzr.
Qed.

(* This is Isaacs, Corollary (3.5). *)
Corollary Aint_subring : subring_closed Aint.
Proof.
suff rAZ: {in Aint &, forall x y, (x - y \in Aint) * (x * y \in Aint)}.
  by split=> // x y AZx AZy; rewrite rAZ.
move=> x y AZx AZy.
have [|S [ringS] ] := @Aint_subring_exists [:: x; y]; first exact/allP/and3P.
move=> /allP/and3P[Sx Sy _] [Y _ genYS].
have AZ_S := fin_Csubring_Aint ringS genYS.
by have [_ S_B S_M] := ringS; rewrite !AZ_S ?S_B ?S_M.
Qed.
HB.instance Definition _ := GRing.isSubringClosed.Build _ Aint Aint_subring.

End AlgIntSubring.

Lemma Aint_aut (nu : {rmorphism algC -> algC}) x :
  (nu x \in Aint) = (x \in Aint).
Proof. by rewrite !unfold_in minCpoly_aut. Qed.

Definition dvdA (e : Algebraics.divisor) : {pred algC} :=
  fun z => if e == 0 then z == 0 else z / e \in Aint.
Delimit Scope algC_scope with A.
Delimit Scope algC_expanded_scope with Ax.
Notation "e %| x" := (x \in dvdA e) : algC_expanded_scope.
Notation "e %| x" := (@in_mem Algebraics.divisor x (mem (dvdA e))) : algC_scope.

Fact dvdA_zmod_closed e : zmod_closed (dvdA e).
Proof.
split=> [|x y]; first by rewrite unfold_in mul0r eqxx rpred0 ?if_same.
rewrite ![(e %| _)%A]unfold_in.
case: ifP => [_ x0 /eqP-> | _]; first by rewrite subr0.
by rewrite mulrBl; apply: rpredB.
Qed.
HB.instance Definition _ e := GRing.isZmodClosed.Build _ (dvdA e)
  (dvdA_zmod_closed e).

Definition eqAmod (e x y : Algebraics.divisor) := (e %| x - y)%A.
Notation "x == y %[mod e ]" := (eqAmod e x y) : algC_scope.
Notation "x != y %[mod e ]" := (~~ (eqAmod e x y)) : algC_scope.

Lemma eqAmod_refl e x : (x == x %[mod e])%A.
Proof. by rewrite /eqAmod subrr rpred0. Qed.
#[global] Hint Resolve eqAmod_refl : core.

Lemma eqAmod_sym e x y : ((x == y %[mod e]) = (y == x %[mod e]))%A.
Proof. by rewrite /eqAmod -opprB rpredN. Qed.

Lemma eqAmod_trans e y x z :
  (x == y %[mod e] -> y == z %[mod e] -> x == z %[mod e])%A.
Proof.
by move=> Exy Eyz; rewrite /eqAmod -[x](subrK y) -[_ - z]addrA rpredD.
Qed.

Lemma eqAmod_transl e x y z :
  (x == y %[mod e])%A -> (x == z %[mod e])%A = (y == z %[mod e])%A.
Proof. by move/(sym_left_transitive (eqAmod_sym e) (@eqAmod_trans e)). Qed.

Lemma eqAmod_transr e x y z :
  (x == y %[mod e])%A -> (z == x %[mod e])%A = (z == y %[mod e])%A.
Proof. by move/(sym_right_transitive (eqAmod_sym e) (@eqAmod_trans e)). Qed.

Lemma eqAmod0 e x : (x == 0 %[mod e])%A = (e %| x)%A.
Proof. by rewrite /eqAmod subr0. Qed.

Lemma eqAmodN e x y : (- x == y %[mod e])%A = (x == - y %[mod e])%A.
Proof. by rewrite eqAmod_sym /eqAmod !opprK addrC. Qed.

Lemma eqAmodDr e x y z : (y + x == z + x %[mod e])%A = (y == z %[mod e])%A.
Proof. by rewrite /eqAmod addrAC opprD !addrA subrK. Qed.

Lemma eqAmodDl e x y z : (x + y == x + z %[mod e])%A = (y == z %[mod e])%A.
Proof. by rewrite !(addrC x) eqAmodDr. Qed.

Lemma eqAmodD e x1 x2 y1 y2 :
  (x1 == x2 %[mod e] -> y1 == y2 %[mod e] -> x1 + y1 == x2 + y2 %[mod e])%A.
Proof.
by rewrite -(eqAmodDl e x2 y1) -(eqAmodDr e y1); apply: eqAmod_trans.
Qed.

Lemma eqAmodm0 e : (e == 0 %[mod e])%A.
Proof. by rewrite /eqAmod subr0 unfold_in; case: ifPn => // /divff->. Qed.
#[global] Hint Resolve eqAmodm0 : core.

Lemma eqAmodMr e :
  {in Aint, forall z x y, x == y %[mod e] -> x * z == y * z %[mod e]}%A.
Proof.
move=> z Zz x y.
rewrite /eqAmod -mulrBl ![(e %| _)%A]unfold_in mulf_eq0 mulrAC.
by case: ifP => [_ -> // | _ Exy]; apply: rpredM.
Qed.

Lemma eqAmodMl e :
  {in Aint, forall z x y, x == y %[mod e] -> z * x == z * y %[mod e]}%A.
Proof. by move=> z Zz x y Exy; rewrite !(mulrC z) eqAmodMr. Qed.

Lemma eqAmodMl0 e : {in Aint, forall x, x * e == 0 %[mod e]}%A.
Proof. by move=> x Zx; rewrite -(mulr0 x) eqAmodMl. Qed.

Lemma eqAmodMr0 e : {in Aint, forall x, e * x == 0 %[mod e]}%A.
Proof. by move=> x Zx; rewrite /= mulrC eqAmodMl0. Qed.

Lemma eqAmod_addl_mul e : {in Aint, forall x y, x * e + y == y %[mod e]}%A.
Proof. by move=> x Zx y; rewrite -{2}[y]add0r eqAmodDr eqAmodMl0. Qed.

Lemma eqAmodM e : {in Aint &, forall x1 y2 x2 y1,
  x1 == x2 %[mod e] -> y1 == y2 %[mod e] -> x1 * y1 == x2 * y2 %[mod e]}%A.
Proof.
move=> x1 y2 Zx1 Zy2 x2 y1 eq_x /(eqAmodMl Zx1)/eqAmod_trans-> //.
exact: eqAmodMr.
Qed.

Lemma eqAmod_rat :
  {in Crat & &, forall e m n, (m == n %[mod e])%A = (m == n %[mod e])%C}.
Proof.
move=> e m n Qe Qm Qn; rewrite /eqCmod unfold_in /eqAmod unfold_in.
case: ifPn => // nz_e; apply/idP/idP=> [/Cint_rat_Aint | /Aint_Cint] -> //.
by rewrite rpred_div ?rpredB.
Qed.

Lemma eqAmod0_rat : {in Crat &, forall e n, (n == 0 %[mod e])%A = (e %| n)%C}.
Proof. by move=> e n Qe Qn; rewrite /= eqAmod_rat /eqCmod ?subr0 ?Crat0. Qed.

Lemma eqAmod_nat (e m n : nat) : (m == n %[mod e])%A = (m == n %[mod e])%N.
Proof. by rewrite eqAmod_rat ?rpred_nat // eqCmod_nat. Qed.

Lemma eqAmod0_nat (e m : nat) : (m == 0 %[mod e])%A = (e %| m)%N.
Proof. by rewrite eqAmod0_rat ?rpred_nat // dvdC_nat. Qed.

(* Multiplicative order. *)

Definition orderC x :=
  let p := minCpoly x in
  oapp val 0 [pick n : 'I_(2 * size p ^ 2) | p == intrp 'Phi_n].

Notation "#[ x ]" := (orderC x) : C_scope.

Lemma exp_orderC x : x ^+ #[x]%C = 1.
Proof.
rewrite /orderC; case: pickP => //= [] [n _] /= /eqP Dp.
have n_gt0: (0 < n)%N.
  rewrite lt0n; apply: contraTneq (size_minCpoly x) => n0.
  by rewrite Dp n0 Cyclotomic0 rmorph1 size_poly1.
have [z prim_z] := C_prim_root_exists n_gt0.
rewrite prim_expr_order // -(root_cyclotomic prim_z).
by rewrite -Cintr_Cyclotomic // -Dp root_minCpoly.
Qed.

Lemma dvdn_orderC x n : (#[x]%C %| n)%N = (x ^+ n == 1).
Proof.
apply/idP/eqP=> [|x_n_1]; first by apply: expr_dvd; apply: exp_orderC.
have [-> | n_gt0] := posnP n; first by rewrite dvdn0.
have [m prim_x m_dv_n] := prim_order_exists n_gt0 x_n_1.
have{n_gt0} m_gt0 := dvdn_gt0 n_gt0 m_dv_n; congr (_ %| n)%N: m_dv_n.
pose p := minCpoly x; have Dp: p = cyclotomic x m := minCpoly_cyclotomic prim_x.
rewrite /orderC; case: pickP => /= [k /eqP Dp_k | no_k]; last first.
  suffices lt_m_2p: (m < 2 * size p ^ 2)%N.
    have /eqP[] := no_k (Ordinal lt_m_2p).
    by rewrite /= -/p Dp -Cintr_Cyclotomic.
  rewrite Dp size_cyclotomic (sqrnD 1) addnAC mulnDr -add1n leq_add //.
  suffices: (m <= \prod_(q <- primes m | q == 2) q * totient m ^ 2)%N.
    have [m_even | m_odd] := boolP (2%N \in primes m).
      by rewrite -big_filter filter_pred1_uniq ?primes_uniq // big_seq1.
    by rewrite big_hasC ?has_pred1 // => /leq_trans-> //; apply: leq_addl.
  rewrite big_mkcond totientE // -mulnn -!big_split /=.
  rewrite {1}[m]prod_prime_decomp // prime_decompE big_map /= !big_seq.
  elim/big_ind2: _ => // [n1 m1 n2 m2 | q]; first exact: leq_mul.
  rewrite mem_primes => /and3P[q_pr _ q_dv_m].
  rewrite lognE q_pr m_gt0 q_dv_m /=; move: (logn q _) => k.
  rewrite !mulnA expnS leq_mul //.
  case: (ltngtP q 2) (prime_gt1 q_pr) => // [q_gt2|->] _.
    rewrite mul1n mulnAC mulnn -{1}[q]muln1 leq_mul ?expn_gt0 ?prime_gt0 //.
    by rewrite -(subnKC q_gt2) (ltn_exp2l 1).
  by rewrite !muln1 -expnS (ltn_exp2l 0).
have k_prim_x: k.-primitive_root x.
  have k_gt0: (0 < k)%N.
    rewrite lt0n; apply: contraTneq (size_minCpoly x) => k0.
    by rewrite Dp_k k0 Cyclotomic0 rmorph1 size_poly1.
  have [z prim_z] := C_prim_root_exists k_gt0.
  rewrite -(root_cyclotomic prim_z) -Cintr_Cyclotomic //.
  by rewrite -Dp_k root_minCpoly.
apply/eqP; rewrite eqn_dvd !(@prim_order_dvd _ _ x) //.
by rewrite !prim_expr_order ?eqxx.
Qed.
