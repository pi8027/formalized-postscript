Require Import Basics.
Require Import Relations.
Require Import Relation_Operators.
Require Import Logic.Decidable.
Require Import List.

Require Import Listutils.

Inductive term : Set :=
  | term_pop  : term
  | term_dup  : term
  | term_swap : term
  | term_cons : term
  | term_push : term
  | term_exec : term
  | term_seq  : term -> term -> term.

Definition stack : Set := list term.

Definition environment : Set := (stack * stack)%type.

Inductive eval : relation environment :=
  | evalpop  :
      forall (t : term) (vs ps : stack),
      eval (t :: vs, term_pop :: ps) (vs, ps)
  | evaldup  :
      forall (t : term) (vs ps : stack),
      eval (t :: vs, term_dup :: ps) (t :: t :: vs, ps)
  | evalswap :
      forall (t1 t2 : term) (vs ps : stack),
      eval (t1 :: t2 :: vs, term_swap :: ps) (t2 :: t1 :: vs, ps)
  | evalcons :
      forall (t1 t2 : term) (vs ps : stack),
      eval (t1 :: t2 :: vs, term_cons :: ps) (term_seq t2 t1 :: vs, ps)
  | evalpush :
      forall (t : term) (vs ps : stack),
      eval (vs, term_push :: t :: ps) (t :: vs, ps)
  | evalexec :
      forall (t : term) (vs ps : stack),
      eval (t :: vs, term_exec :: ps) (vs, t :: ps)
  | evalseq  :
      forall (t1 t2 : term) (vs ps : stack),
      eval (vs, term_seq t1 t2 :: ps) (vs, t1 :: t2 :: ps).

Definition evalrtc : relation environment := clos_refl_trans _ eval.
Definition evalrtc' : relation environment := clos_refl_trans_1n _ eval.

Infix "|=>" := eval (at level 80, no associativity).
Infix "|=>*" := evalrtc (at level 80, no associativity).
Infix "|=>*'" := evalrtc' (at level 80, no associativity).

Lemma evalrtc_is_evalrtc' : forall (e1 e2 : environment), e1 |=>* e2 <-> e1 |=>*' e2.
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
  left ; eexists ; apply evalseq.
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
    | or_intror _ _ => idtac
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

Definition termnop : term := term_seq (term_seq term_push term_pop) term_pop.

Lemma evalnop : forall (vs ps : stack), (vs, termnop :: ps) |=>* (vs, ps).
  intros ; evalauto.
Qed.

Definition term_list' : list term -> term -> term := fold_left term_seq.

Lemma eval_term_list' : forall (ts : list term) (t : term) (vs ps : stack),
  (vs, term_list' ts t :: ps) |=>* (vs, t :: ts ++ ps).
  induction ts ; intros.
  evalauto.
  evalpartial IHts ; evalauto.
Qed.

Definition term_list (ts : list term) : term := term_list' ts termnop.

Lemma eval_term_list : forall (ts : list term) (vs ps : stack),
  (vs, term_list ts :: ps) |=>* (vs, ts ++ ps).
  intros.
  evalpartial eval_term_list'.
  evalauto.
Qed.

Lemma term_list_replicate : forall (n : nat) (t1 t2 : term),
  term_list' (replicate n t1) t2 =
    fold_right (flip term_seq) t2 (replicate n t1).
  intros.
  rewrite (replicate_rev_id n t1) at 2.
  apply (eq_sym (fold_left_rev_right (flip term_seq) (replicate n t1) t2)).
Qed.

Lemma app_term_list' : forall (ts1 ts2 : list term) (t : term),
  term_list' (ts1 ++ ts2) t = term_list' ts2 (term_list' ts1 t).
  intros ; apply fold_left_app.
Qed.

Lemma app_term_list : forall (ts1 ts2 : list term),
  term_list (ts1 ++ ts2) = term_list' ts2 (term_list ts1).
  intros ; apply app_term_list'.
Qed.

Definition term_snoc : term := term_list [ term_swap ; term_cons ].

Lemma evalsnoc : forall (t1 t2 : term) (vs ps : stack),
  (t1 :: t2 :: vs, term_snoc :: ps) |=>* (term_seq t1 t2 :: vs, ps).
  intros ; evalauto.
Qed.

Definition term_quote : term := term_list [term_push ; term_push ; term_snoc ].

Lemma eval_term_quote : forall (t : term) (vs ps : stack),
  (t :: vs, term_quote :: ps) |=>* (term_seq term_push t :: vs, ps).
  intros ; evalauto.
Qed.
