Require Import Basics.
Require Import Relations.
Require Import List.
Require Import Omega.

Require Import Listutils.
Require Import PsCore.

Definition termincr : term := term_list
  [ term_dup ; term_quote ; term_swap ; term_quote ; term_cons ;
    term_swap ; term_quote ; term_cons ; term_exec ;
    term_snoc ; term_swap ].

Lemma eval_termincr : forall (t1 t2 : term) (vs ps : stack),
  (t1 :: t2 :: vs, termincr :: ps) |=>* (t1 :: term_seq t2 t1 :: vs, ps).
  intros ; evalauto.
Qed.

Lemma eval_termincr_replicate : forall (n : nat) (t1 t2 : term) (vs ps : stack),
  (t1 :: t2 :: vs, replicate n termincr ++ ps) |=>*
    (t1 :: term_list' (replicate n t1) t2 :: vs, ps).
  induction n ; intros ; evalauto.
  evalpartial IHn ; evalauto.
Qed.

Definition termnatq (n : nat) : term := term_list (replicate n termincr).

Lemma eval_termnatq : forall (n : nat) (t1 t2 : term) (vs ps : stack),
  (t1 :: t2 :: vs, termnatq n :: ps) |=>*
    (t1 :: term_list' (replicate n t1) t2 :: vs, ps).
  intros.
  evalpartial eval_term_list.
  evalpartial eval_termincr_replicate.
  evalauto.
Qed.

Definition termnat (n : nat) (t1 : term) : Prop :=
  forall (t2 : term) (vs ps : stack),
    (t2 :: vs, t1 :: ps) |=>* (vs, replicate n t2 ++ ps).

Definition termnat_term (n : nat) : term := term_list
  [ term_push ; termnop ; term_swap ; termnatq n ; term_pop ; term_exec ].

Lemma eval_termnat_term : forall (n : nat), termnat n (termnat_term n).
  repeat intro.
  evalpartial eval_term_list ; evalauto.
  evalpartial eval_termnatq ; evalauto.
  apply eval_term_list.
Qed.

Definition termnat_quote : term := term_list
  [ term_push ; termnop ; term_quote ;
    term_push ; termincr ; term_quote ; term_cons ;
    term_swap ; term_quote ; term_cons ; term_exec ;
    term_push ; termincr ; term_swap ; term_exec ; term_pop ].

Lemma eval_termnat_quote : forall (n : nat) (t : term) (vs ps : stack),
  termnat n t -> (t :: vs, termnat_quote :: ps) |=>* (termnatq n :: vs, ps).
  repeat intro.
  evalauto ; evalpartial H ; evalpartial eval_termincr_replicate ; evalauto.
Qed.

Definition termnat_unquote : term := term_list
  [ term_push ; termnop ;
    term_push ; term_push ; term_cons ;
    term_push ; termnop ; term_cons ;
    term_push ; term_swap ; term_cons ;
    term_snoc ;
    term_push ; term_pop ; term_cons ;
    term_push ; term_exec ; term_cons ].

Definition eval_termnat_unquote : forall (n : nat) (vs ps : stack),
  (termnatq n :: vs, termnat_unquote :: ps) |=>* (termnat_term n :: vs, ps).
  repeat intro ; evalauto.
Qed.

Lemma termnatq_eqmap : forall (n m : nat), termnatq n = termnatq m -> n = m.
  intro.
  induction n ; intros ; destruct m.
  auto.
  unfold termnatq, term_list, replicate at 1, term_list' at 1, fold_left in H.
  rewrite (term_list_replicate (S m) termincr termnop) in H.
  inversion H.
  unfold termnatq, term_list, replicate at 2, term_list' at 2, fold_left in H.
  rewrite (term_list_replicate (S n) termincr termnop) in H.
  inversion H.
  f_equal.
  apply IHn.
  unfold termnatq, term_list in H.
  rewrite (term_list_replicate (S n) termincr termnop) in H.
  rewrite (term_list_replicate (S m) termincr termnop) in H.
  simpl in H.
  inversion H.
  rewrite <- (term_list_replicate n termincr termnop) in H1.
  rewrite <- (term_list_replicate m termincr termnop) in H1.
  auto.
Qed.

Lemma termnat_eqmap : forall (n m : nat) (t1 t2 : term),
  termnat n t1 -> termnat m t2 -> t1 = t2 -> n = m.
  intros.
  assert
    (([], replicate n term_pop) |=>* ([], replicate m term_pop) \/
     ([], replicate m term_pop) |=>* ([], replicate n term_pop)).
    eapply (evalrts_confluence ([ term_pop ], [ t1 ])).
    evalpartial H.
    rewrite (app_nil_r (replicate n term_pop)).
    evalauto.
    rewrite H1.
    evalpartial H0.
    rewrite (app_nil_r (replicate m term_pop)).
    evalauto.
  assert
    (([], replicate n term_pop) |=>*' ([], replicate m term_pop) \/
     ([], replicate m term_pop) |=>*' ([], replicate n term_pop)).
    destruct H2 ; [ left | right ] ; apply clos_rt_rt1n ; auto.
  assert (replicate n term_pop = replicate m term_pop).
    destruct H3 ; destruct n ; destruct m ; inversion H3 ;
      (auto || inversion H4 || simpl ; f_equal ; auto).
  assert (forall a b, replicate a term_pop = replicate b term_pop -> a = b).
    intro ; induction a ; intro ; destruct b ; simpl ; intro.
    auto.
    congruence.
    congruence.
    f_equal.
    apply IHa.
    congruence.
  apply H5 ; auto.
Qed.

Definition termnatq_succ : term :=
  term_list [ term_push ; termincr ; term_cons ].

Lemma eval_termnatq_succ : forall (n : nat) (vs ps : stack),
  (termnatq n :: vs, termnatq_succ :: ps) |=>* (termnatq (S n) :: vs, ps).
  intros.
  evalauto.
  rtcequal.
  unfold termnat_term, termnatq, term_list.
  rewrite (term_list_replicate (S n) termincr termnop).
  simpl ; unfold flip ; f_equal.
  apply (eq_sym (term_list_replicate n termincr termnop)).
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
  term_list [ termnat_quote ; termnatq_succ ; termnat_unquote ].

Lemma eval_termnat_succ :
  forall (n : nat) (t : term) (vs ps : stack), termnat n t ->
    (t :: vs, termnat_succ :: ps) |=>* (termnat_term (S n) :: vs, ps).
  intros.
  evalpartial eval_term_list.
  evalpartial' eval_termnat_quote.
  apply H.
  evalpartial eval_termnatq_succ.
  evalauto.
Qed.

Lemma termnat_succ_prop :
  forall (n : nat) (t1 : term) (vs ps : stack), termnat n t1 ->
    exists t2 : term, termnat (S n) t2 /\
      (t1 :: vs, termnat_succ :: ps) |=>* (t2 :: vs, ps).
  intros.
  exists (termnat_term (S n)).
  split.
  apply eval_termnat_term.
  apply eval_termnat_succ ; auto.
Qed.

Definition termnatq_add : term :=
  term_list [ term_push ; termincr ; term_swap ; term_exec ; term_pop ].

Lemma eval_termnatq_add : forall (n m : nat) (vs ps : stack),
  (termnatq m :: termnatq n :: vs, termnatq_add :: ps) |=>*
    (termnatq (n + m) :: vs, ps).
  intros.
  evalauto.
  evalpartial eval_termnatq.
  evalauto.
  unfold termnatq.
  rewrite <- (app_term_list _ _).
  rewrite <- (replicate_app _ _ _).
  evalauto.
Qed.

Definition termnat_add : term := term_list
  [ termnat_quote ; term_swap ;
    term_push ; termnatq_succ ; term_swap ; term_exec ; termnat_unquote ].

Lemma eval_termnat_add : forall (n m : nat) (t1 t2 : term) (vs ps : stack),
  termnat n t1 -> termnat m t2 ->
    (t2 :: t1 :: vs, termnat_add :: ps) |=>* (termnat_term (n + m) :: vs, ps).
  intros.
  evalpartial eval_term_list.
  evalpartial' eval_termnat_quote.
  apply H0.
  evalauto.
  evalpartial H.
  evalpartial eval_termnatq_succ_replicate.
  apply eval_termnat_unquote.
Qed.

Lemma termnat_add_prop : forall (n m : nat) (t1 t2 : term) (vs ps : stack),
  termnat n t1 -> termnat m t2 ->
    exists t3 : term, termnat (n + m) t3 /\
      (t2 :: t1 :: vs, termnat_add :: ps) |=>* (t3 :: vs, ps).
  intros.
  eexists.
  split.
  apply eval_termnat_term.
  apply eval_termnat_add ; auto.
Qed.

Definition termnatq_mult : term := term_list
  [ term_swap ; termnat_unquote ;
    term_swap ; term_push ; term_push ; term_snoc ; term_snoc ;
    term_push ; termnop ; term_swap ;
    term_push ; termincr ; term_swap ;
    term_exec ; term_pop ].

Lemma eval_termnatq_mult : forall (n m : nat) (vs ps : stack),
  (termnatq m :: termnatq n :: vs, termnatq_mult :: ps) |=>*
    (termnatq (n * m) :: vs, ps).
  intros.
  evalpartial eval_term_list.
  evalauto.
  evalpartial eval_termnatq.
  evalauto.
  evalpartial eval_term_list.
  simpl.
  assert (forall (a : nat) (vs ps : stack),
    (termincr :: termnatq a :: vs, replicate n (termnatq m) ++ ps) |=>*
      (termincr :: termnatq (a + n * m) :: vs, ps)).
    induction n ; intros.
    replace (a + 0 * m) with a by omega.
    evalauto.
    simpl.
    evalpartial eval_termnatq.
    replace (a + (m + n * m)) with ((m + a) + n * m) by omega.
    replace (term_list' (replicate m termincr) (termnatq a)) with
      (termnatq (m + a)).
    apply IHn.
    unfold termnatq.
    replace (m + a) with (a + m) by omega.
    rewrite <- (replicate_app a m termincr).
    apply app_term_list.
  evalpartial (H 0).
  evalauto.
Qed.

Definition termnat_mult : term := term_list
  [ termnat_quote ; term_swap ; termnat_quote ; term_swap ;
    termnatq_mult ; termnat_unquote ].

Lemma eval_termnat_mult : forall (n m : nat) (t1 t2 : term) (vs ps : stack),
  termnat n t1 -> termnat m t2 ->
    (t2 :: t1 :: vs, termnat_mult :: ps) |=>* (termnat_term (n * m) :: vs, ps).
  intros.
  evalpartial eval_term_list.
  evalpartial' eval_termnat_quote.
  apply H0.
  evalstep.
  evalpartial' eval_termnat_quote.
  apply H.
  evalstep.
  evalpartial eval_termnatq_mult.
  apply eval_termnat_unquote.
Qed.
