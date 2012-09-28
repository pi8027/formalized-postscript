Require Import
  Relations.Relations Lists.List Program.Basics Program.Syntax ssreflect
  Common PsCore PsBool.

(*
instnat_spec:
  自然数の仕様。
*)
Definition instnat_spec (n : nat) (i1 : inst) : Prop :=
  forall i2 vs cs,
  (i2 :: vs, i1 :: cs) |=>* (instseq_replicate n i2 :: vs, cs).

(*
exists_instnat:
  自然数の仕様を満たす命令。
*)
Lemma exists_instnat : forall n,  { i : inst | instnat_spec n i }.
Proof.
  induction n.
  - eexists ; move=> i2 vs cs ; simpl.
    evalpartial' evalpop.
    evalpartial evalpush.
    evalauto.
  - move: IHn => [i H].
    eexists ; move=> i2 vs cs.
    evalpartial' evalcopy.
    evalpartial' H.
    apply evalsnoc.
Qed.

Definition instnat (n : nat) := proj1_sig (exists_instnat n).
Definition eval_instnat (n : nat) := proj2_sig (exists_instnat n).

(*
instnat_eqmap:
  任意の自然数 n, m と任意の命令 i について、i が自然数 n, m としての仕様を同時
  に満たしていれば、必ず n = m である。
  よって、n /= m であればある命令が自然数 n, m としての仕様を同時に満たすことは
*)
Lemma instnat_eqmap :
  forall n m i, instnat_spec n i -> instnat_spec m i -> n = m.
Proof.
  move=> n m i1 H0 H1.
  have H2: (([], replicate n instpop) |=>* ([], replicate m instpop) \/
      ([], replicate m instpop) |=>* ([], replicate n instpop)).
    apply (eval_semi_uniqueness ([ instpop ], [ i1 ; instexec ])).
    - evalpartial H0.
      evalauto.
      evalpartial evalseq_replicate.
      evalauto.
      rtcrefl.
      apply app_nil_r.
    - evalpartial H1.
      evalauto.
      evalpartial evalseq_replicate.
      evalauto.
      rtcrefl.
      apply app_nil_r.
  have: (replicate n instpop = replicate m instpop).
    by destruct H2 ; destruct n ; destruct m ; inversion H ;
      (inversion H2 || simpl ; f_equal).
  clear.
  move: m ; induction n ; intro ; destruct m ; simpl ; intros ;
    (congruence || f_equal ; apply IHn ; congruence).
Qed.

(*
instnat_succ:
  後者関数。
*)
Lemma exists_instnat_succ :
  { instnat_succ : inst |
    forall n i1, instnat_spec n i1 -> forall vs cs,
    exists i2 : inst, instnat_spec (S n) i2 /\
    (i1 :: vs, instnat_succ :: cs) |=>* (i2 :: vs, cs) }.
Proof.
  eexists ; move=> n i1 H vs cs.
  eexists ; split.
  - move=> i2 vs' cs'.
    evalpartial' evalcopy.
    evalpartial' H.
    apply evalsnoc.
  - evalpartial' evalpush.
    evalpartial' evalcons.
    evalpartial' evalpush.
    apply evalsnoc.
Qed.

Definition instnat_succ := proj1_sig exists_instnat_succ.
Definition instnat_succ_proof := proj2_sig exists_instnat_succ.

(*
instnat_add:
  加算命令。
*)
Lemma exists_instnat_add :
  { instnat_add : inst |
    forall n m i1 i2, instnat_spec n i1 -> instnat_spec m i2 -> forall vs cs,
    exists i3 : inst, instnat_spec (n + m) i3 /\
    (i2 :: i1 :: vs, instnat_add :: cs) |=>* (i3 :: vs, cs) }.
Proof.
  eexists ; move=> n m i1 i2 H H0 vs cs.
  evalpartial' evalswap.
  evalpartial' evalpush.
  evalpartial' evalswap.
  evalpartial' evalexec.
  evalpartial H.
  evalpartial evalexec.
  evalpartial evalseq_replicate.
  evalauto.
  clear H i1 ; move: n m i2 H0 vs cs ;
    elim => [ m i1 H vs cs | n H m i1 H0 vs cs ] ; simpl.
  - by evalauto.
  - edestruct (instnat_succ_proof m i1 H0) as [i2 [H1 H2]].
    evalpartial H2.
    replace (S (n + m)) with (n + S m) by omega.
    apply (H (S m) i2 H1).
Qed.

Definition instnat_add := proj1_sig exists_instnat_add.
Definition instnat_add_proof := proj2_sig exists_instnat_add.