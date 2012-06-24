Require Import Basics.
Require Import Relations.
Require Import Relation_Operators.
Require Import Logic.Decidable.
Require Import List.

Require Import Listutils.

Inductive term : Set :=
  | termpop  : term
  | termdup  : term
  | termswap : term
  | termcons : term
  | termpush : term
  | termexec : term
  | termpair : term -> term -> term.

Definition stack : Set := list term.

Definition environment : Set := (stack * stack)%type.

Inductive eval : relation environment :=
  | evalpop  :
      forall (t : term) (vs ps : stack),
      eval (t :: vs, termpop :: ps) (vs, ps)
  | evaldup  :
      forall (t : term) (vs ps : stack),
      eval (t :: vs, termdup :: ps) (t :: t :: vs, ps)
  | evalswap :
      forall (t1 t2 : term) (vs ps : stack),
      eval (t1 :: t2 :: vs, termswap :: ps) (t2 :: t1 :: vs, ps)
  | evalcons :
      forall (t1 t2 : term) (vs ps : stack),
      eval (t1 :: t2 :: vs, termcons :: ps) (termpair t2 t1 :: vs, ps)
  | evalpush :
      forall (t : term) (vs ps : stack),
      eval (vs, termpush :: t :: ps) (t :: vs, ps)
  | evalexec :
      forall (t : term) (vs ps : stack),
      eval (t :: vs, termexec :: ps) (vs, t :: ps)
  | evalpair  :
      forall (t1 t2 : term) (vs ps : stack),
      eval (vs, termpair t1 t2 :: ps) (vs, t1 :: t2 :: ps).

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
  destruct t.
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

Lemma eval_unique : forall (a b c : environment), a |=> b -> a |=> c -> b = c.
  intros.
  destruct a, b, c.
  destruct s0.
  inversion H.
  destruct t.
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
  rewrite (eval_unique _ _ _ H H2) ; auto.
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

Ltac evalpartial t := eapply rt_trans ; [ apply t ; fail | ].

Ltac evalpartial' t := eapply rt_trans ; [ eapply t | ].

Ltac rtcequal :=
  hnf ;
  match goal with
    | |- clos_refl_trans _ _ ?e1 ?e2 =>
      replace e1 with e2 ; [ apply rt_refl | repeat f_equal ]
    | _ => fail 2 "The goal is invalid."
  end.

Definition termnop : term := termpair (termpair termpush termpop) termpop.

Lemma evalnop : forall (vs ps : stack), (vs, termnop :: ps) |=>* (vs, ps).
  intros ; evalauto.
Qed.

Definition termseq' : list term -> term -> term := fold_left termpair.

Lemma eval_termseq' : forall (ts : list term) (t : term) (vs ps : stack),
  (vs, termseq' ts t :: ps) |=>* (vs, t :: ts ++ ps).
  induction ts ; intros.
  evalauto.
  evalpartial IHts ; evalauto.
Qed.

Definition termseq (ts : list term) : term := termseq' ts termnop.

Lemma eval_termseq : forall (ts : list term) (vs ps : stack),
  (vs, termseq ts :: ps) |=>* (vs, ts ++ ps).
  intros.
  evalpartial eval_termseq'.
  evalauto.
Qed.

Lemma termseq_replicate : forall (n : nat) (t1 t2 : term),
  termseq' (replicate n t1) t2 =
    fold_right (flip termpair) t2 (replicate n t1).
  intros.
  rewrite (replicate_rev_id n t1) at 2.
  apply (eq_sym (fold_left_rev_right (flip termpair) (replicate n t1) t2)).
Qed.

Lemma app_termseq' : forall (ts1 ts2 : list term) (t : term),
  termseq' (ts1 ++ ts2) t = termseq' ts2 (termseq' ts1 t).
  intros ; apply fold_left_app.
Qed.

Lemma app_termseq : forall (ts1 ts2 : list term),
  termseq (ts1 ++ ts2) = termseq' ts2 (termseq ts1).
  intros ; apply app_termseq'.
Qed.

Definition termsnoc : term := termseq [ termswap ; termcons ].

Lemma evalsnoc : forall (t1 t2 : term) (vs ps : stack),
  (t1 :: t2 :: vs, termsnoc :: ps) |=>* (termpair t1 t2 :: vs, ps).
  intros ; evalauto.
Qed.

Definition termquote : term := termseq [termpush ; termpush ; termsnoc ].

Lemma eval_termquote : forall (t : term) (vs ps : stack),
  (t :: vs, termquote :: ps) |=>* (termpair termpush t :: vs, ps).
  intros ; evalauto.
Qed.
