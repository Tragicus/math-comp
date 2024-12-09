From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype choice fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

HB.mixin Record hasPt (T : Type) := { pt : T }.

#[short(type="pointedType")]
HB.structure Definition Pointed := {T of hasPt T}.

#[short(type="ptEqType")]
HB.structure Definition PointedEquality := {T of hasPt T & hasDecEq T}.

#[short(type="ptChoiceType")]
HB.structure Definition PointedChoice := {T of hasPt T & Choice T}.

#[short(type="ptCountableType")]
HB.structure Definition PointedCount := {T of hasPt T & Countable T}.

#[short(type="ptFinType")]
HB.structure Definition PointedFinite := {T of hasPt T & Finite T}.

HB.instance Definition _ := hasPt.Build unit tt.
HB.instance Definition _ := hasPt.Build bool false.
HB.instance Definition _ (T1 T2 : pointedType) :=
  hasPt.Build (T1 * T2)%type (pt, pt).
HB.instance Definition _ T := hasPt.Build (option T) None.
HB.instance Definition _ (T1 T2 : pointedType) :=
  hasPt.Build (T1 + T2)%type (inl pt).

Definition pointed_at (T : Type) (pt : T) := T.

HB.instance Definition _ (T : Type) (pt : T) := hasPt.Build (pointed_at pt) pt.
