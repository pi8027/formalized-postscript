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
Lemma exists_instnat : forall n, { i : inst | instnat_spec n i }.
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
Defined.

Notation instnat := (fun n => proj1_sig (exists_instnat n)).
Notation eval_instnat := (fun n => proj2_sig (exists_instnat n)).

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
      rtcrefl.
      apply app_nil_r.
    - evalpartial H1.
      evalauto.
      evalpartial evalseq_replicate.
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
Defined.

Notation instnat_succ := (proj1_sig exists_instnat_succ).
Notation instnat_succ_proof := (proj2_sig exists_instnat_succ).

(*
instnat_add:
  加算命令。
*)
Lemma exists_instnat_add_tail :
  { instnat_add : inst |
    forall n m i1 i2, instnat_spec n i1 -> instnat_spec m i2 -> forall vs cs,
    exists i3 : inst, instnat_spec (Plus.tail_plus n m) i3 /\
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
  clear H i1 ; move: n m i2 H0 vs cs ;
    elim => [ m i1 H vs cs | n H m i1 H0 vs cs ] ; simpl.
  - by evalauto.
  - edestruct (instnat_succ_proof m i1 H0) as [i2 [H1 H2]].
    evalpartial H2.
    apply (H (S m) i2 H1).
Defined.

Notation instnat_add := (proj1_sig exists_instnat_add_tail).
Notation instnat_add_proof_tail := (proj2_sig exists_instnat_add_tail).

Lemma exists_instnat_add :
  { instnat_add : inst |
    forall n m i1 i2, instnat_spec n i1 -> instnat_spec m i2 -> forall vs cs,
    exists i3 : inst, instnat_spec (n + m) i3 /\
    (i2 :: i1 :: vs, instnat_add :: cs) |=>* (i3 :: vs, cs) }.
Proof.
  exists instnat_add.
  move=> n m.
  rewrite Plus.plus_tail_plus.
  apply instnat_add_proof_tail.
Defined.

Notation instnat_add_proof := (proj2_sig exists_instnat_add).

(*
instnat_mult:
  乗算命令。
*)
Lemma exists_instnat_mult_tail :
  { instnat_mult : inst |
    forall n m i1 i2, instnat_spec n i1 -> instnat_spec m i2 -> forall vs cs,
    exists i3 : inst, instnat_spec (Mult.tail_mult n m) i3 /\
    (i2 :: i1 :: vs, instnat_mult :: cs) |=>* (i3 :: vs, cs) }.
Proof.
  rewrite /Mult.tail_mult.
  move: (0) (instnat 0) (eval_instnat 0).
  move=> o i1 H ; eexists ; move=> n m i2 i3 H0 H1 vs cs.
  evalpartial' evalquote.
  evalpartial' evalpush.
  evalpartial' evalcons.
  evalpartial' evalquote.
  evalpartial' evalsnoc.
  evalpartial' evalpush.
  evalpartial' evalswap.
  evalpartial' evalexec.
  evalauto.
  evalpartial H0.
  evalpartial evalexec.
  evalpartial evalseq_replicate.
  clear i2 H0.
  move: o i1 i3 H H1 vs cs ;
    elim: n => [ o i1 i2 H H0 vs cs | n H o i1 i2 H0 H1 vs cs ] ; simpl.
  - evalauto.
    eauto.
  - evalauto.
    evalpartial' evalswap.
    edestruct (instnat_add_proof_tail m o i2 i1 H1 H0) as [i3 [H2 H3]].
    evalpartial H3.
    auto.
Defined.

Notation instnat_mult := (proj1_sig exists_instnat_mult_tail).
Notation instnat_mult_proof_tail := (proj2_sig exists_instnat_mult_tail).

Lemma exists_instnat_mult :
  { instnat_mult : inst |
    forall n m i1 i2, instnat_spec n i1 -> instnat_spec m i2 -> forall vs cs,
    exists i3 : inst, instnat_spec (n * m) i3 /\
    (i2 :: i1 :: vs, instnat_mult :: cs) |=>* (i3 :: vs, cs) }.
Proof.
  exists instnat_mult.
  move=> n m.
  rewrite Mult.mult_tail_mult.
  apply instnat_mult_proof_tail.
Defined.

Notation instnat_mult_proof := (proj2_sig exists_instnat_mult).
