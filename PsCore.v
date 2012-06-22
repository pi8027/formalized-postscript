Require Import Basics.
Require Import Relations.
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

Inductive reduction : relation environment :=
  | reduction_pop  :
      forall (t : term) (vs ps : stack),
      reduction (t :: vs, term_pop :: ps) (vs, ps)
  | reduction_dup  :
      forall (t : term) (vs ps : stack),
      reduction (t :: vs, term_dup :: ps) (t :: t :: vs, ps)
  | reduction_swap :
      forall (t1 t2 : term) (vs ps : stack),
      reduction (t1 :: t2 :: vs, term_swap :: ps) (t2 :: t1 :: vs, ps)
  | reduction_cons :
      forall (t1 t2 : term) (vs ps : stack),
      reduction (t1 :: t2 :: vs, term_cons :: ps) (term_seq t2 t1 :: vs, ps)
  | reduction_push :
      forall (t : term) (vs ps : stack),
      reduction (vs, term_push :: t :: ps) (t :: vs, ps)
  | reduction_exec :
      forall (t : term) (vs ps : stack),
      reduction (t :: vs, term_exec :: ps) (vs, t :: ps)
  | reduction_seq  :
      forall (t1 t2 : term) (vs ps : stack),
      reduction (vs, term_seq t1 t2 :: ps) (vs, t1 :: t2 :: ps).

Definition redstar : relation environment := clos_refl_trans _ reduction.

Definition redstar' : relation environment := clos_refl_trans_1n _ reduction.

Lemma decide_reduction : forall (e1 : environment),
  decidable (exists e2 : environment, reduction e1 e2).
  intros.
  destruct e1.
  destruct s0.
  right ; intro.
  destruct H.
  inversion H.
  destruct t.
  destruct s.
  right ; intro ; destruct H ; inversion H.
  left ; eexists ; apply reduction_pop.
  destruct s.
  right ; intro ; destruct H ; inversion H.
  left ; eexists ; apply reduction_dup.
  destruct s.
  right ; intro ; destruct H ; inversion H.
  destruct s.
  right ; intro ; destruct H ; inversion H.
  left ; eexists ; apply reduction_swap.
  destruct s.
  right ; intro ; destruct H ; inversion H.
  destruct s.
  right ; intro ; destruct H ; inversion H.
  left ; eexists ; apply reduction_cons.
  destruct s0.
  right ; intro ; destruct H ; inversion H.
  left ; eexists ; apply reduction_push.
  destruct s.
  right ; intro ; destruct H ; inversion H.
  left ; eexists ; apply reduction_exec.
  left ; eexists ; apply reduction_seq.
Defined.

Lemma reduction_unique : forall (a b c : environment),
  reduction a b -> reduction a c -> b = c.
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

Lemma redstar_confluence : forall (a b c : environment),
  redstar a b -> redstar a c -> redstar b c \/ redstar c b.
  unfold redstar.
  intros.
  assert (redstar' a b).
    apply clos_rt_rt1n ; auto.
  assert (redstar' a c).
    apply clos_rt_rt1n ; auto.
  induction H1 ; auto.
  inversion H2.
  rewrite <- H4 ; auto.
  apply IHclos_refl_trans_1n.
  apply clos_rt1n_rt ; auto.
  apply clos_rt1n_rt ; rewrite (reduction_unique _ _ _ H1 H4) ; auto.
  rewrite (reduction_unique _ _ _ H1 H4) ; auto.
Qed.

Ltac evalstep' e1 e2 :=
  try apply rt_refl ;
  match eval hnf in (decide_reduction e1) with
    | or_introl _ (ex_intro _ ?e3 ?p) =>
      apply (rt_trans _ _ _ _ _ (rt_step _ _ _ _ p))
    | or_intror _ _ => idtac
    | _ => idtac
  end.

Ltac evalstep :=
  match goal with
    | |- redstar ?e1 ?e2 => evalstep' e1 e2
    | |- clos_refl_trans _ reduction ?e1 ?e2 => evalstep' e1 e2
    | _ => fail 2 "The goal is invalid."
  end.

Ltac evalauto := repeat evalstep.

Ltac redpartial t := eapply rt_trans ; [ apply t ; fail | ].

Ltac redpartial' t := eapply rt_trans ; [ eapply t | ].

Ltac rtequal :=
  hnf ;
  match goal with
    | |- clos_refl_trans _ _ ?e1 ?e2 =>
      replace e1 with e2 ; [ apply rt_refl | repeat f_equal ]
    | _ => fail 2 "The goal is invalid."
  end.

Definition termnop : term := term_seq (term_seq term_push term_pop) term_pop.

Lemma rednop : forall (vs ps : stack), redstar (vs, termnop :: ps) (vs, ps).
  intros ; evalauto.
Qed.

Definition term_list' : list term -> term -> term := fold_left term_seq.

Lemma red_term_list' : forall (ts : list term) (t : term) (vs ps : stack),
  redstar (vs, term_list' ts t :: ps) (vs, t :: ts ++ ps).
  induction ts ; intros.
  evalauto.
  redpartial IHts ; evalauto.
Qed.

Definition term_list (ts : list term) : term := term_list' ts termnop.

Lemma red_term_list : forall (ts : list term) (vs ps : stack),
  redstar (vs, term_list ts :: ps) (vs, ts ++ ps).
  intros.
  redpartial red_term_list'.
  evalauto.
Qed.

Lemma term_list_replicate : forall (n : nat) (t1 t2 : term),
  term_list' (replicate n t1) t2 =
    fold_right (flip term_seq) t2 (replicate n t1).
  intros.
  unfold term_list'.
  rewrite (replicate_rev_id n t1) at 2.
  apply (eq_sym (fold_left_rev_right (flip term_seq) (replicate n t1) t2)).
Qed.

Lemma term_list'_app : forall (ts1 ts2 : list term) (t : term),
  term_list' (ts1 ++ ts2) t = term_list' ts2 (term_list' ts1 t).
  intros ; apply fold_left_app.
Qed.

Lemma term_list_app : forall (ts1 ts2 : list term),
  term_list (ts1 ++ ts2) = term_list' ts2 (term_list ts1).
  intros ; apply term_list'_app.
Qed.

Definition term_snoc : term := term_list [ term_swap ; term_cons ].

Lemma red_snoc : forall (t1 t2 : term) (vs ps : stack),
  redstar (t1 :: t2 :: vs, term_snoc :: ps) (term_seq t1 t2 :: vs, ps).
  intros ; evalauto.
Qed.

Definition term_quote : term := term_list [term_push ; term_push ; term_snoc ].

Lemma red_term_quote : forall (t : term) (vs ps : stack),
  redstar (t :: vs, term_quote :: ps) (term_seq term_push t :: vs, ps).
  intros ; evalauto.
Qed.
