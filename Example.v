Require Import
  Coq.Strings.String Ssreflect.ssreflect Ssreflect.seq FormalPS.stdlib_ext
  FormalPS.Core FormalPS.Template FormalPS.Bool FormalPS.Nat.

(* rev3 *)

Definition rev3 : inst := instseqc
  [:: instquote; instswap; instquote; instcons;
    instswap; instquote; instcons; instexec].

Goal forall i1 i2 i3 vs cs,
  (i3 :: i2 :: i1 :: vs, rev3 :: cs) |=>* (i1 :: i2 :: i3 :: vs, cs).
Proof.
  move => i1 i2 i3 vs cs.
  evalpartial evalseqc => /=.
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
  move => i1 i2 i3 vs cs.
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
  evalauto.
Defined.

(*
Eval compute in (proj1_sig rev3_exists').
*)

(* examples for PRO-99 *)

Set Printing Width 51.

Lemma example1 a b c d :
  ([:: a; b; c; d], [::
   instswap; instpop; instswap; instquote; instquote;
   instcopy; instcons; instswap; instquote; instquote;
   instcons; instexec; instswap; instcons; instquote;
   instcons; instswap; instquote; instcons; instexec;
   instquote; instcons; instexec]) |=>*
  ([:: d; c; a; c], [::]).
Proof.
  eapply evalrtc_cons.
  Show Existentials.
  by apply evalswap.
  do !econstructor.
  Undo.
  set cs := [:: instexec];
    move: {1 3}cs (eq_refl cs); subst cs => cs Hcs.
  do !econstructor.
  Undo.
  evalauto.
  rewrite Hcs.
  evalauto.
Qed.

Lemma example2 :
  { p | forall a b c d,
    ([:: a; b; c; d], p) |=>*
    ([:: d; c; a; c], [::]) }.
Proof.
  eexists => a b c d.
  eapply evalrtc_cons; first by apply evalswap.
  evalpartial evalpop. evalpartial evalswap.
  evalpartial evalquote. evalpartial evalquote.
  evalpartial evalcopy. evalpartial evalcons.
  evalpartial evalswap. evalpartial evalquote.
  evalpartial evalquote. evalpartial evalcons.
  evalpartial evalexec. evalauto.
  evalpartial evalswap. evalpartial evalcons.
  evalpartial evalquote. evalpartial evalcons.
  evalpartial evalswap. evalpartial evalquote.
  evalpartial evalcons. evalpartial evalexec.
  evalauto.
  evalpartial evalquote. evalpartial evalcons.
  evalpartial evalexec. evalauto.
Defined.

Goal forall a, a = size [::tt; tt] -> a = 2.
Proof.
  move=> a H.
  (eapply eq_trans; first apply H); simpl.
  Undo.
  (eapply eq_trans; first apply H);
    subst_evars; simpl.
  done.
Qed.

Eval compute in (proj1_sig example2).

Lemma example3 :
  { p |
    forall i1 i2 i3 vs cs,
    (i1 :: i2 :: i3 :: vs, p :: cs) |=>*
    (instpair i1 instsnoc ::
     instpair i3 (instpush i1) :: vs, cs) }.
Proof.
  eexists => i1 i2 i3 vs cs.
  evaltemplate 3
    [:: insttpair (instthole 0)
          (instt_of_inst instsnoc);
        insttpair (instthole 2)
          (insttpush (instthole 0))]
    (Nil instt).
  evalauto.
Defined.

Eval compute in (inst_size (proj1_sig example3)).
