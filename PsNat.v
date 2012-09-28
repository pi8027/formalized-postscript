Require Import
  Relations.Relations Lists.List Program.Basics Program.Syntax ssreflect
  Common PsCore PsBool.

(*
instnat_spec:
  自然数の仕様。
*)
Definition instnat_spec (n : nat) (i1 : inst) : Prop :=
  forall i2 vs cs,
  (i2 :: vs, i1 :: cs) |=>* (instseq (replicate n i2) :: vs, cs).

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
    evalpartial evalsnoc.
    by rtcrefl ; rewrite /instseq 2!instseq_replicate.
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
      evalpartial evalseq.
      erewrite app_nil_r.
      evalauto.
    - evalpartial H1.
      evalauto.
      evalpartial evalseq.
      erewrite app_nil_r.
      evalauto.
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
Lemma exists_instnat_succ:
  { instnat_succ : inst |
    forall n i1, instnat_spec n i1 -> forall vs cs,
      exists i2 : inst, instnat_spec (S n) i2 /\
      (i1 :: vs, instnat_succ :: cs) |=>* (i2 :: vs, cs) }.
Proof.
  eexists ; move=> n i1 H vs cs.
  eexists ; split.
  - move=> i2 vs' cs'.
    rewrite /instseq instseq_replicate ;
      simpl ; rewrite -instseq_replicate /flip.
    evalpartial' evalcopy.
    evalpartial' H.
    evalpartial evalsnoc.
    evalauto.
  - evalpartial' evalpush.
    evalpartial' evalcons.
    evalpartial' evalpush.
    evalpartial evalsnoc.
    evalauto.
Qed.

Definition instnat_succ := proj1_sig exists_instnat_succ.
Definition instnat_succ_proof := proj2_sig exists_instnat_succ.