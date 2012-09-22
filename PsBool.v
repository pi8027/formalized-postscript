Require Import
  Program.Basics Relations.Relations Lists.List ssreflect Common PsCore.

(*
instfalse_spec, insttrue_spec, instbool_spec:
  ブール値の仕様。
  false は何もしない命令である。
  true は swap と同様の振舞いをする命令である。
*)
Definition instfalse_spec (i1 : inst) : Prop :=
  forall i2 i3 vs cs, (i3 :: i2 :: vs, i1 :: cs) |=>* (i3 :: i2 :: vs, cs).

Definition insttrue_spec (i1 : inst) : Prop :=
  forall i2 i3 vs cs, (i3 :: i2 :: vs, i1 :: cs) |=>* (i2 :: i3 :: vs, cs).

Definition instbool_spec (b : bool) (i : inst) :=
  if b then insttrue_spec i else instfalse_spec i.

(*
instfalse, insttrue:
  ブール値の仕様を満たす命令。
*)
Definition instfalse : inst := instnop.

Definition insttrue : inst := instswap.

Lemma eval_insttrue : insttrue_spec insttrue.
Proof.
  repeat intro ; evalauto.
Qed.

Lemma eval_instfalse : instfalse_spec instfalse.
Proof.
  repeat intro ; evalauto.
Qed.

(*
instnot:
  not 命令。
*)
Definition instnot : inst := instpair (instpush instswap) instcons.

Lemma instnot_proof :
  forall b i1, instbool_spec b i1 -> forall vs cs,
  exists i2 : inst, instbool_spec (negb b) i2 /\
  (i1 :: vs, instnot :: cs) |=>* (i2 :: vs, cs).
Proof.
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
Definition instif : inst := instseq
  [ instquote ; instswap ; instquote ; instcons ;
    instswap ; instquote ; instcons ; instexec ;
    instexec ; instpop ].

Lemma eval_instif :
  forall b i1 i2 i3, instbool_spec b i1 -> forall vs cs,
  (i3 :: i2 :: i1 :: vs, instif :: cs) |=>*
    ((if b then i2 else i3) :: vs, cs).
Proof.
  intros.
  destruct b ; evalauto ; evalpartial H ; evalauto.
Qed.

Definition instexecif : inst := instpair instif instexec.

Lemma eval_instexecif :
  forall b i1 i2 i3, instbool_spec b i1 -> forall vs cs,
  (i3 :: i2 :: i1 :: vs, instexecif :: cs) |=>*
    (vs, (if b then i2 else i3) :: cs).
Proof.
  intros.
  destruct b ; evalauto ; evalpartial H ; evalauto.
Qed.

(*
instxor:
  xor 命令。
*)
Definition instxor : inst := instcons.

Lemma instxor_proof :
  forall b1 b2 i1 i2, instbool_spec b1 i1 -> instbool_spec b2 i2 ->
  forall vs cs,
  exists i3 : inst, instbool_spec (xorb b1 b2) i3 /\
  (i2 :: i1 :: vs, instxor :: cs) |=>* (i3 :: vs, cs).
Proof.
  intros ; evalauto ; destruct b1, b2 ; repeat intro ;
    evalauto ; evalpartial H ; evalpartial H0 ; evalauto.
Qed.

Opaque instxor.
