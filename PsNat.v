Require Import Basics.
Require Import Relations.
Require Import List.
Require Import Omega.

Require Import Listutils.
Require Import PsCore.

Definition termincr : term := termseq
  [ termdup ; termquote ; termswap ; termquote ; termcons ;
    termswap ; termquote ; termcons ; termexec ;
    termsnoc ; termswap ].

Lemma eval_termincr : forall (t1 t2 : term) (vs ps : stack),
  (t1 :: t2 :: vs, termincr :: ps) |=>* (t1 :: termpair t2 t1 :: vs, ps).
  intros ; evalauto.
Qed.

Lemma eval_termincr_replicate : forall (n : nat) (t1 t2 : term) (vs ps : stack),
  (t1 :: t2 :: vs, replicate n termincr ++ ps) |=>*
    (t1 :: termseq' (replicate n t1) t2 :: vs, ps).
  induction n ; intros ; evalauto.
  evalpartial IHn ; evalauto.
Qed.

Definition termnatq (n : nat) : term := termseq (replicate n termincr).

Lemma eval_termnatq : forall (n : nat) (t1 t2 : term) (vs ps : stack),
  (t1 :: t2 :: vs, termnatq n :: ps) |=>*
    (t1 :: termseq' (replicate n t1) t2 :: vs, ps).
  intros.
  evalpartial eval_termseq.
  evalpartial eval_termincr_replicate.
  evalauto.
Qed.

Definition termnat_spec (n : nat) (t1 : term) : Prop :=
  forall (t2 : term) (vs ps : stack),
    (t2 :: vs, t1 :: ps) |=>* (vs, replicate n t2 ++ ps).

Definition termnat (n : nat) : term := termseq
  [ termpush ; termnop ; termswap ; termnatq n ; termpop ; termexec ].

Lemma eval_termnat : forall (n : nat), termnat_spec n (termnat n).
  repeat intro.
  evalpartial eval_termseq ; evalauto.
  evalpartial eval_termnatq ; evalauto.
  apply eval_termseq.
Qed.

Definition termnat_quote : term := termseq
  [ termpush ; termnop ; termquote ;
    termpush ; termincr ; termquote ; termcons ;
    termswap ; termquote ; termcons ; termexec ;
    termpush ; termincr ; termswap ; termexec ; termpop ].

Lemma eval_termnat_quote :
  forall (n : nat) (t : term) (vs ps : stack), termnat_spec n t ->
    (t :: vs, termnat_quote :: ps) |=>* (termnatq n :: vs, ps).
  repeat intro.
  evalauto ; evalpartial H ; evalpartial eval_termincr_replicate ; evalauto.
Qed.

Definition termnat_unquote : term := termseq
  [ termpush ; termnop ;
    termpush ; termpush ; termcons ;
    termpush ; termnop ; termcons ;
    termpush ; termswap ; termcons ;
    termsnoc ;
    termpush ; termpop ; termcons ;
    termpush ; termexec ; termcons ].

Definition eval_termnat_unquote : forall (n : nat) (vs ps : stack),
  (termnatq n :: vs, termnat_unquote :: ps) |=>* (termnat n :: vs, ps).
  repeat intro ; evalauto.
Qed.

Lemma termnatq_eqmap : forall (n m : nat), termnatq n = termnatq m -> n = m.
  intro.
  induction n ; intros ; destruct m.
  auto.
  unfold termnatq, termseq, replicate at 1, termseq' at 1, fold_left in H.
  rewrite (termseq_replicate (S m) termincr termnop) in H.
  inversion H.
  unfold termnatq, termseq, replicate at 2, termseq' at 2, fold_left in H.
  rewrite (termseq_replicate (S n) termincr termnop) in H.
  inversion H.
  f_equal.
  apply IHn.
  unfold termnatq, termseq in *.
  repeat erewrite termseq_replicate in *.
  inversion H.
  auto.
Qed.

Lemma termnat_eqmap : forall (n m : nat) (t : term),
  termnat_spec n t -> termnat_spec m t -> n = m.
  intros.
  assert
    (([], replicate n termpop) |=>*' ([], replicate m termpop) \/
     ([], replicate m termpop) |=>*' ([], replicate n termpop)).
    repeat erewrite <- evalrtc_is_evalrtc'.
    apply (@evalrtc_confluence ([ termpop ], [ t ])).
    evalpartial H.
    erewrite app_nil_r.
    evalauto.
    evalpartial H0.
    erewrite app_nil_r.
    evalauto.
  assert (replicate n termpop = replicate m termpop).
    destruct H1 ; destruct n ; destruct m ; inversion H1 ;
      (auto || inversion H2 || simpl ; f_equal ; auto).
  clear H H0 H1.
  revert m H2 ; induction n ; intro ; destruct m ; simpl ; intros ;
    (auto || congruence || f_equal ; apply IHn ; congruence).
Qed.

Definition termnatq_succ : term :=
  termseq [ termpush ; termincr ; termcons ].

Lemma eval_termnatq_succ : forall (n : nat) (vs ps : stack),
  (termnatq n :: vs, termnatq_succ :: ps) |=>* (termnatq (S n) :: vs, ps).
  intros.
  evalauto.
  rtcequal.
  unfold termnat, termnatq, termseq.
  erewrite termseq_replicate.
  simpl ; unfold flip ; f_equal.
  apply eq_sym, termseq_replicate.
Qed.

Lemma eval_termnatq_succ_replicate : forall (n m : nat) (vs ps : stack),
  (termnatq n :: vs, replicate m termnatq_succ ++ ps) |=>*
    (termnatq (m + n) :: vs, ps).
  intros ; revert n.
  induction m ; intros.
  evalauto.
  simpl.
  evalpartial eval_termnatq_succ.
  evalpartial IHm.
  rtcequal ; omega.
Qed.

Definition termnat_succ : term :=
  termseq [ termnat_quote ; termnatq_succ ; termnat_unquote ].

Lemma eval_termnat_succ :
  forall (n : nat) (t : term) (vs ps : stack), termnat_spec n t ->
    (t :: vs, termnat_succ :: ps) |=>* (termnat (S n) :: vs, ps).
  intros.
  evalpartial eval_termseq.
  evalpartial' eval_termnat_quote.
  apply H.
  evalpartial eval_termnatq_succ.
  evalauto.
Qed.

Lemma termnat_succ_proof :
  forall (n : nat) (t1 : term) (vs ps : stack), termnat_spec n t1 ->
    exists t2 : term, termnat_spec (S n) t2 /\
      (t1 :: vs, termnat_succ :: ps) |=>* (t2 :: vs, ps).
  intros.
  exists (termnat (S n)).
  split.
  apply eval_termnat.
  apply eval_termnat_succ ; auto.
Qed.

Definition termnatq_add : term :=
  termseq [ termpush ; termincr ; termswap ; termexec ; termpop ].

Lemma eval_termnatq_add : forall (n m : nat) (vs ps : stack),
  (termnatq m :: termnatq n :: vs, termnatq_add :: ps) |=>*
    (termnatq (n + m) :: vs, ps).
  intros.
  evalauto.
  evalpartial eval_termnatq.
  evalauto.
  unfold termnatq.
  erewrite <- app_termseq, replicate_app.
  evalauto.
Qed.

Definition termnat_add : term := termseq
  [ termnat_quote ; termswap ;
    termpush ; termnatq_succ ; termswap ; termexec ; termnat_unquote ].

Lemma eval_termnat_add : forall (n m : nat) (t1 t2 : term) (vs ps : stack),
  termnat_spec n t1 -> termnat_spec m t2 ->
    (t2 :: t1 :: vs, termnat_add :: ps) |=>* (termnat (n + m) :: vs, ps).
  intros.
  evalpartial eval_termseq.
  evalpartial' eval_termnat_quote.
  apply H0.
  evalauto.
  evalpartial H.
  evalpartial eval_termnatq_succ_replicate.
  apply eval_termnat_unquote.
Qed.

Lemma termnat_add_proof : forall (n m : nat) (t1 t2 : term) (vs ps : stack),
  termnat_spec n t1 -> termnat_spec m t2 ->
    exists t3 : term, termnat_spec (n + m) t3 /\
      (t2 :: t1 :: vs, termnat_add :: ps) |=>* (t3 :: vs, ps).
  intros.
  eexists.
  split.
  apply eval_termnat.
  apply eval_termnat_add ; auto.
Qed.

Definition termnatq_mult : term := termseq
  [ termpush ; termnop ; termpush ; termpush ; termcons ; termsnoc ;
    termpush ; termnatq_add ; termcons ; termquote ;
    termpush ; termnatq 0 ; termquote ; termsnoc ;
    termswap ; termnat_unquote ; termcons ; termexec ].

Lemma eval_termnatq_mult : forall (n m : nat) (vs ps : stack),
  (termnatq m :: termnatq n :: vs, termnatq_mult :: ps) |=>*
    (termnatq (n * m) :: vs, ps).
  intros.
  do 126 evalstep.
  evalpartial eval_termnat.
  assert (forall (a : nat), (termnatq a :: vs,
    replicate n (termseq [ termpush ; termnatq m ; termnatq_add ]) ++ ps)
      |=>* (termnatq (a + n * m) :: vs, ps)).
    induction n ; intros.
    replace (a + 0 * m) with a by omega.
    evalauto.
    simpl.
    evalpartial eval_termseq.
    evalstep.
    evalpartial eval_termnatq_add.
    replace (a + (m + n * m)) with ((a + m) + n * m) by omega.
    apply IHn.
  evalpartial (H 0) ; evalauto.
Qed.

Definition termnat_mult : term := termseq
  [ termnat_quote ; termswap ; termnat_quote ; termswap ;
    termnatq_mult ; termnat_unquote ].

Lemma eval_termnat_mult : forall (n m : nat) (t1 t2 : term) (vs ps : stack),
  termnat_spec n t1 -> termnat_spec m t2 ->
    (t2 :: t1 :: vs, termnat_mult :: ps) |=>* (termnat (n * m) :: vs, ps).
  intros.
  evalpartial eval_termseq.
  evalpartial' eval_termnat_quote.
  apply H0.
  evalstep.
  evalpartial' eval_termnat_quote.
  apply H.
  evalstep.
  evalpartial eval_termnatq_mult.
  apply eval_termnat_unquote.
Qed.

Lemma termnat_mult_proof : forall (n m : nat) (t1 t2 : term) (vs ps : stack),
  termnat_spec n t1 -> termnat_spec m t2 ->
    exists t3 : term, termnat_spec (n * m) t3 /\
      (t2 :: t1 :: vs, termnat_mult :: ps) |=>* (t3 :: vs, ps).
  intros.
  eexists.
  split.
  apply eval_termnat.
  apply eval_termnat_mult ; auto.
Qed.
