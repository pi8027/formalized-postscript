Require Import Basics.
Require Import Relations.
Require Import Relation_Operators.
Require Import Logic.Decidable.
Require Import List.

Require Import Listutils.

Inductive inst : Set :=
  | instpop  : inst
  | instdup  : inst
  | instswap : inst
  | instcons : inst
  | instpush : inst
  | instexec : inst
  | instpair : inst -> inst -> inst.

Definition stack : Set := list inst.

Definition environment : Set := (stack * stack)%type.

Inductive eval : relation environment :=
  | evalpop  :
      forall (i : inst) (vs ps : stack),
      eval (i :: vs, instpop :: ps) (vs, ps)
  | evaldup  :
      forall (i : inst) (vs ps : stack),
      eval (i :: vs, instdup :: ps) (i :: i :: vs, ps)
  | evalswap :
      forall (i1 i2 : inst) (vs ps : stack),
      eval (i1 :: i2 :: vs, instswap :: ps) (i2 :: i1 :: vs, ps)
  | evalcons :
      forall (i1 i2 : inst) (vs ps : stack),
      eval (i1 :: i2 :: vs, instcons :: ps) (instpair i2 i1 :: vs, ps)
  | evalpush :
      forall (i : inst) (vs ps : stack),
      eval (vs, instpush :: i :: ps) (i :: vs, ps)
  | evalexec :
      forall (i : inst) (vs ps : stack),
      eval (i :: vs, instexec :: ps) (vs, i :: ps)
  | evalpair  :
      forall (i1 i2 : inst) (vs ps : stack),
      eval (vs, instpair i1 i2 :: ps) (vs, i1 :: i2 :: ps).

Definition evalrtc : relation environment := clos_refl_trans _ eval.
Definition evalrtc' : relation environment := clos_refl_trans_1n _ eval.

Infix "|=>" := eval (at level 80, no associativity).
Infix "|=>*" := evalrtc (at level 80, no associativity).
Infix "|=>*'" := evalrtc' (at level 80, no associativity).

Lemma evalrtc_is_evalrtc' :
  forall (e1 e2 : environment), e1 |=>* e2 <-> e1 |=>*' e2.
  intros ; split ; [ apply clos_rt_rt1n | apply clos_rt1n_rt ].
Qed.

Lemma decide_eval : forall (e1 : environment),
  decidable (exists e2 : environment, e1 |=> e2).
  intros.
  destruct e1.
  destruct s0.
  right ; intro.
  destruct H.
  inversion H.
  destruct i.
  destruct s.
  right ; intro ; destruct H ; inversion H.
  left ; eexists ; apply evalpop.
  destruct s.
  right ; intro ; destruct H ; inversion H.
  left ; eexists ; apply evaldup.
  destruct s.
  right ; intro ; destruct H ; inversion H.
  destruct s.
  right ; intro ; destruct H ; inversion H.
  left ; eexists ; apply evalswap.
  destruct s.
  right ; intro ; destruct H ; inversion H.
  destruct s.
  right ; intro ; destruct H ; inversion H.
  left ; eexists ; apply evalcons.
  destruct s0.
  right ; intro ; destruct H ; inversion H.
  left ; eexists ; apply evalpush.
  destruct s.
  right ; intro ; destruct H ; inversion H.
  left ; eexists ; apply evalexec.
  left ; eexists ; apply evalpair.
Defined.

Lemma uniqueness_of_eval :
  forall (a b c : environment), a |=> b -> a |=> c -> b = c.
  intros.
  destruct a, b, c.
  destruct s0.
  inversion H.
  destruct i.
  destruct s ; [ inversion H | inversion H ; inversion H0 ; congruence ].
  destruct s ; [ inversion H | inversion H ; inversion H0 ; congruence ].
  destruct s ; [ inversion H | inversion H ; inversion H0 ; congruence ].
  destruct s ; [ inversion H | inversion H ; inversion H0 ; congruence ].
  destruct s ; [ inversion H | inversion H ; inversion H0 ; congruence ].
  destruct s0 ; [ inversion H | inversion H ; inversion H0 ; congruence ].
  destruct s ; [ inversion H | inversion H ; inversion H0 ; congruence ].
  inversion H ; inversion H0 ; congruence.
Qed.

Lemma evalrtc'_confluence : forall (e1 e2 e3 : environment),
  e1 |=>*' e2 -> e1 |=>*' e3 -> e2 |=>*' e3 \/ e3 |=>*' e2.
  intros.
  induction H ; auto.
  inversion H0.
  rewrite <- H2.
  right.
  eapply rt1n_trans ; [ apply H | apply H1 ].
  apply IHclos_refl_trans_1n.
  rewrite (uniqueness_of_eval _ _ _ H H2) ; auto.
Qed.

Lemma evalrtc_confluence : forall (e1 e2 e3 : environment),
  e1 |=>* e2 -> e1 |=>* e3 -> e2 |=>* e3 \/ e3 |=>* e2.
  do 3 intro.
  repeat erewrite evalrtc_is_evalrtc'.
  eapply evalrtc'_confluence.
Qed.

Ltac evalstep' e1 e2 :=
  try apply rt_refl ;
  match eval hnf in (decide_eval e1) with
    | or_introl _ (ex_intro _ ?e3 ?p) =>
      apply (rt_trans _ _ _ _ _ (rt_step _ _ _ _ p))
    | _ => idtac
  end.

Ltac evalstep :=
  match goal with
    | |- ?e1 |=>* ?e2 => evalstep' e1 e2
    | |- clos_refl_trans _ eval ?e1 ?e2 => evalstep' e1 e2
    | _ => fail 2 "The goal is invalid."
  end.

Ltac evalauto := repeat evalstep.

Ltac evalpartial H := eapply rt_trans ; [ apply H ; fail | ].

Ltac evalpartial' H := eapply rt_trans ; [ eapply H | ].

Ltac rtcequal :=
  hnf ;
  match goal with
    | |- clos_refl_trans _ _ ?e1 ?e2 =>
      replace e1 with e2 ; [ apply rt_refl | repeat f_equal ]
    | _ => fail 2 "The goal is invalid."
  end.

Definition instnop : inst := instpair (instpair instpush instpop) instpop.

Lemma evalnop : forall (vs ps : stack), (vs, instnop :: ps) |=>* (vs, ps).
  intros ; evalauto.
Qed.

Definition instseq' : list inst -> inst -> inst := fold_left instpair.

Lemma evalseq' : forall (is : list inst) (i : inst) (vs ps : stack),
  (vs, instseq' is i :: ps) |=>* (vs, i :: is ++ ps).
  induction is ; intros.
  evalauto.
  evalpartial IHis ; evalauto.
Qed.

Definition instseq (is : list inst) : inst := instseq' is instnop.

Lemma evalseq : forall (is : list inst) (vs ps : stack),
  (vs, instseq is :: ps) |=>* (vs, is ++ ps).
  intros.
  evalpartial evalseq'.
  evalauto.
Qed.

Lemma instseq_replicate : forall (n : nat) (i1 i2 : inst),
  instseq' (replicate n i1) i2 =
    fold_right (flip instpair) i2 (replicate n i1).
  intros.
  rewrite (replicate_rev_id n i1) at 2.
  apply (eq_sym (fold_left_rev_right (flip instpair) (replicate n i1) i2)).
Qed.

Lemma app_instseq' : forall (is1 is2 : list inst) (i : inst),
  instseq' (is1 ++ is2) i = instseq' is2 (instseq' is1 i).
  intros ; apply fold_left_app.
Qed.

Lemma app_instseq : forall (is1 is2 : list inst),
  instseq (is1 ++ is2) = instseq' is2 (instseq is1).
  intros ; apply app_instseq'.
Qed.

Definition instsnoc : inst := instseq [ instswap ; instcons ].

Lemma evalsnoc : forall (i1 i2 : inst) (vs ps : stack),
  (i1 :: i2 :: vs, instsnoc :: ps) |=>* (instpair i1 i2 :: vs, ps).
  intros ; evalauto.
Qed.

Definition instquote : inst := instseq [instpush ; instpush ; instsnoc ].

Lemma evalquote : forall (i : inst) (vs ps : stack),
  (i :: vs, instquote :: ps) |=>* (instpair instpush i :: vs, ps).
  intros ; evalauto.
Qed.
