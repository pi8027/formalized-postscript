Require Import Basics Relations List.
Require Import Utils PsCore.

(*
instfalse_spec, insttrue_spec, instbool_spec:
  ブール値の仕様。
  false は何もしない命令である。
  true は swap と同様の振舞いをする命令である。
*)
Definition instfalse_spec (i1 : inst) : Prop :=
  forall (i2 i3 : inst) (vs cs : stack),
    (i3 :: i2 :: vs, i1 :: cs) |=>* (i3 :: i2 :: vs, cs).

Definition insttrue_spec (i1 : inst) : Prop :=
  forall (i2 i3 : inst) (vs cs : stack),
    (i3 :: i2 :: vs, i1 :: cs) |=>* (i2 :: i3 :: vs, cs).

Definition instbool_spec (b : bool) (i : inst) : Prop :=
  if b then insttrue_spec i else instfalse_spec i.

(*
instfalse, insttrue:
  ブール値の仕様を満たす命令。
*)
Definition instfalse := instnop.

Definition insttrue := instswap.

Lemma eval_insttrue : insttrue_spec insttrue.
  repeat intro ; evalauto.
Qed.

Lemma eval_instfalse : instfalse_spec instfalse.
  repeat intro ; evalauto.
Qed.

(*
instnot:
  not 命令。
*)
Definition instnot := instseq [ instpush ; instswap ; instcons ].

Lemma instnot_proof :
  forall (b : bool) (i1 : inst) (vs cs : stack), instbool_spec b i1 ->
    exists i2 : inst, instbool_spec (negb b) i2 /\
    (i1 :: vs, instnot :: cs) |=>* (i2 :: vs, cs).
  intros ; evalauto ; destruct b ;
    repeat intro ; evalauto ; evalpartial H ; evalauto.
Qed.

Opaque instnot.

(*
instif, instexecif:
  ブール値による条件分岐の命令。
  instif は、ブール値によってスタックの先頭にある2つの値のうちどちらを残すかを切
  り替える。後者は、instif によって選択される命令を実行する。
*)
Definition instif := instseq
  [ instquote ;
    instswap ; instquote ; instsnoc ;
    instswap ; instquote ; instcons ;
    instexec ;
    instexec ; instswap ; instpop ].

Lemma eval_instif : forall (b : bool) (i1 i2 i3 : inst) (vs cs : stack),
  instbool_spec b i1 -> (i3 :: i2 :: i1 :: vs, instif :: cs) |=>*
    ((if b then i2 else i3) :: vs, cs).
  intros.
  destruct b ; evalauto ; evalpartial H ; evalauto.
Qed.

Definition instexecif := instseq [ instif ; instexec ].

Lemma eval_instexecif : forall (b : bool) (i1 i2 i3 : inst) (vs cs : stack),
  instbool_spec b i1 -> (i3 :: i2 :: i1 :: vs, instexecif :: cs) |=>*
    (vs, (if b then i2 else i3) :: cs).
  intros.
  destruct b ; evalauto ; evalpartial H ; evalauto.
Qed.

(*
instxor:
  xor 命令。
*)
Definition instxor := instcons.

Lemma instxor_proof : forall (b1 b2 : bool) (i1 i2 : inst) (vs cs : stack),
  instbool_spec b1 i1 -> instbool_spec b2 i2 ->
    exists i3 : inst, instbool_spec (xorb b1 b2) i3 /\
    (i2 :: i1 :: vs, instxor :: cs) |=>* (i3 :: vs, cs).
  intros ; evalauto ; destruct b1, b2 ; repeat intro ;
    evalauto ; evalpartial H ; evalpartial H0 ; evalauto.
Qed.

Opaque instxor.
