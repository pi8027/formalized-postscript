Require Import Basics.
Require Import Relations.
Require Import List.

Require Import Utils.
Require Import PsCore.

Definition instfalse_spec (i1 : inst) : Prop :=
  forall (i2 i3 : inst) (vs ps : stack),
    (i3 :: i2 :: vs, i1 :: ps) |=>* (i3 :: i2 :: vs, ps).

Definition insttrue_spec (i1 : inst) : Prop :=
  forall (i2 i3 : inst) (vs ps : stack),
    (i3 :: i2 :: vs, i1 :: ps) |=>* (i2 :: i3 :: vs, ps).

Definition instbool_spec (b : bool) (i : inst) : Prop :=
  if b then insttrue_spec i else instfalse_spec i.

Definition instfalse := instnop.

Definition insttrue := instswap.

Lemma eval_insttrue : insttrue_spec insttrue.
  repeat intro ; evalauto.
Qed.

Lemma eval_instfalse : instfalse_spec instfalse.
  repeat intro ; evalauto.
Qed.

Definition instnot := instseq [ instpush ; instswap ; instcons ].

Lemma instnot_proof : forall (b : bool) (i1 : inst) (vs ps : stack),
  instbool_spec b i1 ->
    exists i2 : inst,
      instbool_spec (negb b) i2 /\
      (i1 :: vs, instnot :: ps) |=>* (i2 :: vs, ps).
  intros ; evalauto ; destruct b ;
    repeat intro ; evalauto ; evalpartial H ; evalauto.
Qed.

Definition instif := instseq [ instexec ; instswap ; instpop ].

Lemma eval_instif : forall (b : bool) (i1 i2 i3 : inst) (vs ps : stack),
  instbool_spec b i3 -> (i3 :: i2 :: i1 :: vs, instif :: ps) |=>*
    ((if b then i1 else i2) :: vs, ps).
  intros.
  destruct b ; evalauto ; evalpartial H ; evalauto.
Qed.

Definition instexecif := instseq [ instif ; instexec ].

Lemma eval_instexecif : forall (b : bool) (i1 i2 i3 : inst) (vs ps : stack),
  instbool_spec b i3 -> (i3 :: i2 :: i1 :: vs, instexecif :: ps) |=>*
    (vs, (if b then i1 else i2) :: ps).
  intros.
  destruct b ; evalauto ; evalpartial H ; evalauto.
Qed.

Definition instxor := instcons.

Lemma instxor_proof : forall (b1 b2 : bool) (i1 i2 : inst) (vs ps : stack),
  instbool_spec b1 i1 -> instbool_spec b2 i2 ->
    exists i3 : inst,
      instbool_spec (xorb b1 b2) i3 /\
      (i2 :: i1 :: vs, instxor :: ps) |=>* (i3 :: vs, ps).
  intros ; evalauto ; destruct b1, b2 ; repeat intro ;
    evalauto ; evalpartial H ; evalpartial H0 ; evalauto.
Qed.
