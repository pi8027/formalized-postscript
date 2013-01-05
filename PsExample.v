Require Import
  Strings.String ssreflect seq
  Common PsCore PsTemplate PsBool PsNat.

(* rev3 *)

Definition rev3 : inst := instseqc
  [:: instquote; instswap; instquote; instcons;
    instswap; instquote; instcons; instexec].

Goal forall i1 i2 i3 vs cs,
  (i3 :: i2 :: i1 :: vs, rev3 :: cs) |=>* (i1 :: i2 :: i3 :: vs, cs).
Proof.
  move=> i1 i2 i3 vs cs.
  evalpartial evalseqc.
  simpl.
  evalpartial evalquote.
  evalpartial evalswap.
  evalpartial evalquote.
  evalpartial evalcons.
  evalpartial evalswap.
  evalpartial evalquote.
  evalpartial evalcons.
  evalpartial evalexec.
  do 2 evalpartial evalpair.
  do 3 evalpartial evalpush.
  apply evalrtc_refl.
Qed.

Goal forall i1 i2 i3 vs cs,
  (i3 :: i2 :: i1 :: vs, rev3 :: cs) |=>* (i1 :: i2 :: i3 :: vs, cs).
Proof.
  move=> i1 i2 i3 vs cs.
  evalauto.
Qed.

Theorem rev3_exists :
  { rev3 : inst |
    forall i1 i2 i3 vs cs,
    (i3 :: i2 :: i1 :: vs, rev3 :: cs) |=>* (i1 :: i2 :: i3 :: vs, cs) }.
Proof.
  eexists => i1 i2 i3 vs cs.
  evalpartial' evalquote.
  evalpartial' evalswap.
  evalpartial' evalquote.
  evalpartial' evalcons.
  evalpartial' evalswap.
  evalpartial' evalquote.
  evalpartial' evalcons.
  evalpartial evalexec.
  evalauto.
Defined.

(*
Eval compute in (proj1_sig rev3_exists).
*)

Theorem rev3_exists' :
  { rev3 : inst |
    forall i1 i2 i3 vs cs,
    (i3 :: i2 :: i1 :: vs, rev3 :: cs) |=>* (i1 :: i2 :: i3 :: vs, cs) }.
Proof.
  eexists => i1 i2 i3 vs cs.
  evaltemplate 3 [:: instthole 2; instthole 1; instthole 0] (@nil instt).
Defined.

(*
Eval compute in (proj1_sig rev3_exists').
*)
