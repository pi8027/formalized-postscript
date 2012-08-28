Require Import
  Relations.Relations Lists.List Program.Basics ssreflect Common PsCore.

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
exists_false, exists_true:
  ブール値の仕様を満たす命令。
*)

Lemma exists_false : { instfalse : inst | instfalse_spec instfalse }.
Proof.
  eexists ; move=> i1 i2 vs cs.
  evalpartial propnop.
  constructor.
Defined.

Definition instfalse := proj1_sig exists_false.
Definition propfalse := proj2_sig exists_false.

Lemma exists_true : { insttrue : inst | insttrue_spec insttrue }.
Proof.
  eexists ; move=> i1 i2 vs cs.
  evalpartial evalswap.
  constructor.
Defined.

Definition insttrue := proj1_sig exists_true.
Definition proptrue := proj2_sig exists_true.

(*
exists_not:
  not 命令。
*)
Lemma exists_not : { instnot : inst |
  forall b i1 vs cs, instbool_spec b i1 ->
  exists i2 : inst, instbool_spec (negb b) i2 /\
  (i1 :: vs, instnot :: cs) |=>* (i2 :: vs, cs) }.
Proof.
  eexists ; move=> b i1 vs cs H.
  evalpartial evalpair.
  evalpartial (evalpush instswap).
  evalpartial evalcons.
  evalauto.
  destruct b ; move=> i2 i3 vs' cs' ;
    evalauto ; evalpartial H ; evalauto.
Defined.

Definition instnot := proj1_sig exists_not.
Definition propnot := proj2_sig exists_not.

(*
exists_if, exists_execif:
  ブール値による条件分岐の命令。
  instif は、ブール値によってスタックの先頭にある2つの値のうちどちらを残すかを切
  り替える。後者は、instif によって選択される命令を実行する。
*)
Lemma exists_if : { instif : inst |
  forall b i1 i2 i3 vs cs, instbool_spec b i1 ->
  (i3 :: i2 :: i1 :: vs, instif :: cs) |=>*
  ((if b then i2 else i3) :: vs, cs) }.
Proof.
  eexists ; move=> b i1 i2 i3 vs cs H.
  evalpartial evalpair. evalpartial evalquote.
  evalpartial evalpair. evalpartial evalswap.
  evalpartial evalpair. evalpartial evalquote.
  evalpartial evalpair. evalpartial evalcons.
  evalpartial evalpair. evalpartial propsnoc.
  evalpartial evalpair. evalpartial evalexec.
  evalauto.
  destruct b ; evalpartial H ; evalpartial evalpop ; evalauto.
Defined.

Definition instif := proj1_sig exists_if.
Definition propif := proj2_sig exists_if.

Lemma exists_execif : { instexecif : inst |
  forall b i1 i2 i3 vs cs, instbool_spec b i1 ->
  (i3 :: i2 :: i1 :: vs, instexecif :: cs) |=>*
  (vs, (if b then i2 else i3) :: cs) }.
Proof.
  eexists ; move=> b i1 i2 i3 vs cs H.
  evalpartial evalpair.
  evalpartial (propif b) by auto.
  evalpartial evalexec.
  evalauto.
Qed.

Definition instexecif := proj1_sig exists_execif.
Definition propexecif := proj2_sig exists_execif.

(*
instxor:
  xor 命令。
*)
Definition instxor : inst := instcons.

Lemma propxor : forall b1 b2 i1 i2 vs cs,
  instbool_spec b1 i1 -> instbool_spec b2 i2 ->
  exists i3 : inst, instbool_spec (xorb b1 b2) i3 /\
  (i2 :: i1 :: vs, instxor :: cs) |=>* (i3 :: vs, cs).
Proof.
  intros ; evalauto ; destruct b1, b2 ; repeat intro ;
    evalauto ; evalpartial H ; evalpartial H0 ; evalauto.
Qed.
