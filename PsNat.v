Require Import Basics.
Require Import Relations.
Require Import Arith.Even.
Require Import List.
Require Import Omega.

Require Import Utils.
Require Import PsCore.
Require Import PsBool.

Definition instincr : inst := instseq
  [ instdup ; instquote ; instswap ; instquote ; instcons ;
    instswap ; instquote ; instcons ; instexec ;
    instsnoc ; instswap ].

Lemma eval_instincr : forall (i1 i2 : inst) (vs ps : stack),
  (i1 :: i2 :: vs, instincr :: ps) |=>* (i1 :: instpair i2 i1 :: vs, ps).
  intros ; evalauto.
Qed.

Lemma eval_instincr_replicate : forall (n : nat) (i1 i2 : inst) (vs ps : stack),
  (i1 :: i2 :: vs, replicate n instincr ++ ps) |=>*
    (i1 :: instseq' (replicate n i1) i2 :: vs, ps).
  induction n ; intros ; evalauto.
  evalpartial IHn ; evalauto.
Qed.

Definition instnatq (n : nat) : inst := instseq (replicate n instincr).

Lemma eval_instnatq : forall (n : nat) (i1 i2 : inst) (vs ps : stack),
  (i1 :: i2 :: vs, instnatq n :: ps) |=>*
    (i1 :: instseq' (replicate n i1) i2 :: vs, ps).
  intros.
  evalpartial evalseq.
  evalpartial eval_instincr_replicate.
  evalauto.
Qed.

Definition instnat_spec (n : nat) (i1 : inst) : Prop :=
  forall (i2 : inst) (vs ps : stack),
    (i2 :: vs, i1 :: ps) |=>* (vs, replicate n i2 ++ ps).

Definition instnat (n : nat) : inst := instseq
  [ instpush ; instnop ; instswap ; instnatq n ; instpop ; instexec ].

Lemma eval_instnat : forall (n : nat), instnat_spec n (instnat n).
  repeat intro.
  evalpartial evalseq ; evalauto.
  evalpartial eval_instnatq ; evalauto.
  apply evalseq.
Qed.

Definition instnat_quote : inst := instseq
  [ instpush ; instnop ; instquote ;
    instpush ; instincr ; instquote ; instcons ;
    instswap ; instquote ; instcons ; instexec ;
    instpush ; instincr ; instswap ; instexec ; instpop ].

Lemma eval_instnat_quote :
  forall (n : nat) (i : inst) (vs ps : stack), instnat_spec n i ->
    (i :: vs, instnat_quote :: ps) |=>* (instnatq n :: vs, ps).
  repeat intro.
  evalauto ; evalpartial H ; evalpartial eval_instincr_replicate ; evalauto.
Qed.

Definition instnat_unquote : inst := instseq
  [ instpush ; instnop ;
    instpush ; instpush ; instcons ;
    instpush ; instnop ; instcons ;
    instpush ; instswap ; instcons ;
    instsnoc ;
    instpush ; instpop ; instcons ;
    instpush ; instexec ; instcons ].

Definition eval_instnat_unquote : forall (n : nat) (vs ps : stack),
  (instnatq n :: vs, instnat_unquote :: ps) |=>* (instnat n :: vs, ps).
  repeat intro ; evalauto.
Qed.

Lemma instnatq_eqmap : forall (n m : nat), instnatq n = instnatq m -> n = m.
  intro.
  induction n ; intros ; destruct m.
  auto.
  unfold instnatq, instseq, replicate at 1, instseq' at 1, fold_left in H.
  rewrite (instseq_replicate (S m) instincr instnop) in H.
  inversion H.
  unfold instnatq, instseq, replicate at 2, instseq' at 2, fold_left in H.
  rewrite (instseq_replicate (S n) instincr instnop) in H.
  inversion H.
  f_equal.
  apply IHn.
  unfold instnatq, instseq in *.
  repeat erewrite instseq_replicate in *.
  inversion H.
  auto.
Qed.

Lemma instnat_eqmap : forall (n m : nat) (i : inst),
  instnat_spec n i -> instnat_spec m i -> n = m.
  intros.
  assert
    (([], replicate n instpop) |=>*' ([], replicate m instpop) \/
     ([], replicate m instpop) |=>*' ([], replicate n instpop)).
    repeat erewrite <- evalrtc_is_evalrtc'.
    apply (evalrtc_confluence ([ instpop ], [ i ])).
    evalpartial H.
    erewrite app_nil_r.
    evalauto.
    evalpartial H0.
    erewrite app_nil_r.
    evalauto.
  assert (replicate n instpop = replicate m instpop).
    destruct H1 ; destruct n ; destruct m ; inversion H1 ;
      (auto || inversion H2 || simpl ; f_equal ; auto).
  clear H H0 H1.
  revert m H2 ; induction n ; intro ; destruct m ; simpl ; intros ;
    (auto || congruence || f_equal ; apply IHn ; congruence).
Qed.

Definition instnatq_succ : inst := instseq [ instpush ; instincr ; instcons ].

Lemma eval_instnatq_succ : forall (n : nat) (vs ps : stack),
  (instnatq n :: vs, instnatq_succ :: ps) |=>* (instnatq (S n) :: vs, ps).
  intros.
  evalauto.
  rtcrefl.
  unfold instnat, instnatq, instseq.
  erewrite instseq_replicate.
  simpl ; unfold flip ; f_equal.
  apply eq_sym, instseq_replicate.
Qed.

Definition instnat_succ : inst :=
  instseq [ instnat_quote ; instnatq_succ ; instnat_unquote ].

Lemma eval_instnat_succ :
  forall (n : nat) (i : inst) (vs ps : stack), instnat_spec n i ->
    (i :: vs, instnat_succ :: ps) |=>* (instnat (S n) :: vs, ps).
  intros.
  evalpartial evalseq.
  evalpartial eval_instnat_quote by eauto.
  evalpartial eval_instnatq_succ.
  evalauto.
Qed.

Lemma instnat_succ_proof :
  forall (n : nat) (i1 : inst) (vs ps : stack), instnat_spec n i1 ->
    exists i2 : inst, instnat_spec (S n) i2 /\
      (i1 :: vs, instnat_succ :: ps) |=>* (i2 :: vs, ps).
  intros.
  evalpartial eval_instnat_succ by eauto.
  evalauto.
  apply (eval_instnat (S n)).
Qed.

Definition instnat_add : inst := instseq
  [ instswap ; instpush ; instnat_succ ; instswap ; instexec ].

Lemma instnat_add_proof : forall (n m : nat) (i1 i2 : inst) (vs ps : stack),
  instnat_spec n i1 -> instnat_spec m i2 ->
    exists i3 : inst, instnat_spec (n + m) i3 /\
      (i2 :: i1 :: vs, instnat_add :: ps) |=>* (i3 :: vs, ps).
  intros.
  evalauto.
  evalpartial H.
  generalize m as m', i2 as i3, H0 ; clear H H0.
  induction n ; intros ; simpl.
  evalauto ; apply H0.
  edestruct (instnat_succ_proof _ _ _ _ H0) as [? [? ?]].
  evalpartial H1.
  replace (S (n + m')) with (n + S m') by omega.
  apply (IHn (S m') x H).
Qed.

Definition instnatq_add : inst := instseq
  [ instnat_unquote ; instswap ; instnat_unquote ; instswap ;
    instnat_add ; instnat_quote ].

Lemma eval_instnatq_add : forall (n m : nat) (vs ps : stack),
  (instnatq m :: instnatq n :: vs, instnatq_add :: ps) |=>*
    (instnatq (n + m) :: vs, ps).
  intros.
  evalpartial evalseq.
  do 2 (evalpartial eval_instnat_unquote ; evalstep).
  edestruct (instnat_add_proof _ _ _ _ _ _
    (eval_instnat n) (eval_instnat m)) as [? [? ?]].
  evalpartial H0.
  apply (eval_instnat_quote (n + m) x vs ps H).
Qed.

Definition instnat_mult : inst := instseq
  [ instswap ; instquote ; instpush ; instnat_add ; instcons ; instquote ;
    instsnoc ; instpush ; instnat 0 ; instquote ; instsnoc ; instexec ].

Lemma instnat_mult_proof : forall (n m : nat) (i1 i2 : inst) (vs ps : stack),
  instnat_spec n i1 -> instnat_spec m i2 ->
    exists i3 : inst, instnat_spec (m * n) i3 /\
      (i2 :: i1 :: vs, instnat_mult :: ps) |=>* (i3 :: vs, ps).
  intros.
  evalauto.
  evalpartial H0.
  clear H0.
  replace (m * n) with (m * n + 0) by omega.
  generalize 0 as o, (instnat 0) as i3, (eval_instnat 0).
  induction m ; intros ; simpl.
  evalauto ; apply H0.
  do 3 evalstep.
  edestruct (instnat_add_proof _ _ _ _ _ _ H0 H) as [? [? ?]].
  evalpartial H2.
  replace (n + m * n + o) with (m * n + (o + n)) by omega.
  apply IHm ; auto.
Qed.

Definition instnatq_mult : inst := instseq
  [ instnat_unquote ; instswap ; instnat_unquote ; instswap ;
    instnat_mult ; instnat_quote ].

Lemma eval_instnatq_mult : forall (n m : nat) (vs ps : stack),
  (instnatq m :: instnatq n :: vs, instnatq_mult :: ps) |=>*
    (instnatq (m * n) :: vs, ps).
  intros.
  evalpartial evalseq.
  do 2 (evalpartial eval_instnat_unquote ; evalstep).
  edestruct (instnat_mult_proof _ _ _ _ _ _
    (eval_instnat n) (eval_instnat m)) as [? [? ?]].
  evalpartial H0.
  apply eval_instnat_quote ; auto.
Qed.

Definition instnat_even : inst := instseq
  [ instpush ; instnot ; instquote ; instsnoc ;
    instpush ; insttrue ; instswap ; instexec ].

Lemma instnat_even_proof :
  forall (n : nat) (i1 : inst) (vs ps : stack), even n -> instnat_spec n i1 ->
    exists i2 : inst, insttrue_spec i2 /\
      (i1 :: vs, instnat_even :: ps) |=>* (i2 :: vs, ps).
  intros.
  evalauto.
  evalpartial H0.
  generalize insttrue, H, insttrue_proof.
  clear H.
  refine ((fix IHn (n : nat) :=
    match n with
      | 0 => _
      | S 0 => _
      | S (S n) => _
    end) n) ; intros.
  evalauto.
  repeat intro ; evalpartial H1 ; evalauto.
  inversion H ; inversion H3.
  evalauto.
  eapply IHn.
  inversion H ; inversion H3 ; auto.
  repeat intro ; evalauto ; evalpartial H1 ; evalauto.
Qed.

Lemma instnat_even_proof' :
  forall (n : nat) (i1 : inst) (vs ps : stack), odd n -> instnat_spec n i1 ->
    exists i2 : inst, instfalse_spec i2 /\
      (i1 :: vs, instnat_even :: ps) |=>* (i2 :: vs, ps).
  intros.
  evalauto.
  evalpartial H0.
  generalize insttrue, H, insttrue_proof.
  clear H.
  refine ((fix IHn (n : nat) :=
    match n with
      | 0 => _
      | S 0 => _
      | S (S n) => _
    end) n) ; intros.
  inversion H.
  evalauto.
  repeat intro ; evalauto ; evalpartial H1 ; evalauto.
  evalauto.
  eapply IHn.
  inversion H ; inversion H3 ; auto.
  repeat intro ; evalauto ; evalpartial H1 ; evalauto.
Qed.
