Require Import Relations.
Require Import Arith.
Require Import List.
Require Import Omega.

Notation "[]" := nil : list_scope.

Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..) : list_scope.

Fixpoint replicate {A : Set} (n : nat) (a : A) :=
  match n with
    | 0 => nil
    | S n => a :: replicate n a
  end.

Lemma app_replicate : forall (A : Set) (n m : nat) (a : A),
  replicate n a ++ replicate m a = replicate (n + m) a.
  intros.
  induction n.
  compute ; auto.
  replace (S n + m) with (S (n + m)) by omega.
  compute ; f_equal ; apply IHn.
Qed.

Inductive term : Set :=
  (* value stack operators *)
  | term_pop  : term
  | term_dup  : term
  | term_swap : term
  | term_cons : term
  (* continuation stack operators *)
  | term_push : term
  | term_exec : term
  (* structure *)
  | term_seq  : term -> term -> term.

Definition stack : Set := list term.

(* Environment is product of the value stack and the continuacion stack. *)
Definition environment : Set := (stack * stack)%type.

Inductive reduction : relation environment :=
  | reduction_pop  : forall (t : term) (vs ps : stack),
                     reduction (t :: vs, term_pop :: ps) (vs, ps)
  | reduction_dup  : forall (t : term) (vs ps : stack),
                     reduction (t :: vs, term_dup :: ps) (t :: t :: vs, ps)
  | reduction_swap : forall (t1 t2 : term) (vs ps : stack),
                     reduction (t1 :: t2 :: vs, term_swap :: ps) (t2 :: t1 :: vs, ps)
  | reduction_cons : forall (t1 t2 : term) (vs ps : stack),
                     reduction (t1 :: t2 :: vs, term_cons :: ps) (term_seq t1 t2 :: vs, ps)
  | reduction_push : forall (t : term) (vs ps : stack),
                     reduction (vs, term_push :: t :: ps) (t :: vs, ps)
  | reduction_exec : forall (t : term) (vs ps : stack),
                     reduction (t :: vs, term_exec :: ps) (vs, t :: ps)
  | reduction_seq  : forall (t1 t2 : term) (vs ps : stack),
                     reduction (vs, term_seq t1 t2 :: ps) (vs, t1 :: t2 :: ps).

Definition redstar : relation environment := clos_refl_trans _ reduction.

Lemma decide_reduction : forall (e1 : environment),
  (exists e2 : environment, reduction e1 e2) \/
  ~(exists e2 : environment, reduction e1 e2).
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

Definition termnop : term := term_seq (term_seq term_push term_pop) term_pop.

Lemma rednop : forall (vs ps : stack), redstar (vs, termnop :: ps) (vs, ps).
  intros ; evalauto.
Qed.

Definition term_list' : list term -> term -> term := fold_left term_seq.

Definition term_list (ts : list term) : term := term_list' ts termnop.

Lemma red_term_list : forall (ts : list term) (vs ps : stack),
  redstar (vs, term_list ts :: ps) (vs, ts ++ ps).
  intros.
  assert (forall head, redstar (vs, term_list' ts head :: ps) (vs, head :: ts ++ ps)).
    induction ts ; intros.
    evalauto.
    redpartial IHts ; evalauto.
  redpartial H ; evalauto.
Qed.

Definition term_snoc : term := term_list [ term_swap ; term_cons ].

Lemma red_snoc : forall (t1 t2 : term) (vs ps : stack),
  redstar (t1 :: t2 :: vs, term_snoc :: ps) (term_seq t2 t1 :: vs, ps).
  intros ; evalauto.
Qed.

Definition term_quote : term := term_list [term_push ; term_push ; term_cons ].

Lemma red_term_quote : forall (t : term) (vs ps : stack),
  redstar (t :: vs, term_quote :: ps) (term_seq term_push t :: vs, ps).
  intros ; evalauto.
Qed.

Definition termnat_quoted (n : nat) (t1 : term) : Prop :=
  forall (t2 t3 : term) (vs ps : stack),
    redstar (t2 :: t3 :: vs, t1 :: ps) (t2 :: term_list' (replicate n t2) t3 :: vs, ps).

Definition termnat (n : nat) (t1 : term) : Prop :=
  forall (t2 : term) (vs ps : stack),
    redstar (t2 :: vs, t1 :: ps) (vs, replicate n t2 ++ ps).

Definition termincr : term := term_list
  [ term_dup ; term_quote ; term_swap ; term_quote ; term_cons ;
    term_swap ; term_quote ; term_snoc ; term_exec ;
    term_cons ; term_swap ].

Lemma red_termincr : forall (t1 t2 : term) (vs ps : stack),
  redstar (t1 :: t2 :: vs, termincr :: ps) (t1 :: term_seq t2 t1 :: vs, ps).
  intros ; evalauto.
Qed.

Lemma red_termincr_replicate : forall (n : nat) (t1 t2 : term) (vs ps : stack),
  redstar (t1 :: t2 :: vs, replicate n termincr ++ ps)
    (t1 :: term_list' (replicate n t1) t2 :: vs, ps).
  induction n ; intros ; evalauto.
  redpartial IHn ; evalauto.
Qed.

Definition termnat_quoted_term (n : nat) : term := term_list (replicate n termincr).

Lemma termnat_quoted_term_prop : forall (n : nat), termnat_quoted n (termnat_quoted_term n).
  repeat intro.
  redpartial red_term_list.
  apply red_termincr_replicate.
Qed.

Definition termnat_term (n : nat) : term := term_list
  [ term_push ; termnop ; term_swap ; term_list (replicate n termincr) ; term_pop ; term_exec ].

Lemma termnat_term_prop : forall (n : nat), termnat n (termnat_term n).
  repeat intro.
  redpartial red_term_list ; evalauto.
  redpartial termnat_quoted_term_prop ; evalauto.
  apply red_term_list.
Qed.

Definition termnat_quote : term := term_list
  [ term_push ; termnop ; term_quote ;
    term_push ; termincr ; term_quote ; term_snoc ;
    term_swap ; term_quote ; term_snoc ; term_exec ;
    term_push ; termincr ; term_swap ; term_exec ; term_pop ].

Lemma termnat_quote_prop : forall (n : nat) (t1 t2 : term) (vs ps : stack),
  termnat n t1 ->
  exists t2, termnat_quoted n t2 /\ redstar (t1 :: vs, termnat_quote :: ps) (t2 :: vs, ps).
  repeat intro.
  eexists.
  split.
  apply termnat_quoted_term_prop.
  evalauto ; redpartial H ; redpartial red_termincr_replicate ; evalauto.
Qed.

Definition termnat_unquote : term := term_list
  [ term_push ; termnop ;
    term_push ; term_push ; term_snoc ;
    term_push ; termnop ; term_snoc ;
    term_push ; term_swap ; term_snoc ;
    term_cons ;
    term_push ; term_pop ; term_snoc ;
    term_push ; term_exec ; term_snoc ].

Definition termnat_unquote_prop : forall (n : nat) (t1 t2 : term) (vs ps : stack),
  termnat_quoted n t1 ->
  exists t2, termnat n t2 /\ redstar (t1 :: vs, termnat_unquote :: ps) (t2 :: vs, ps).
  repeat intro.
  apply (ex_intro _ (term_list [ term_push ; termnop ; term_swap ; t1 ; term_pop ; term_exec])).
  split.
  repeat intro.
  evalauto.
  redpartial H.
  evalauto.
  redpartial red_term_list.
  evalauto.
  evalauto.
Qed.

Definition termsucc : term := term_list
  [ term_push ; termnop ;
    term_push ; term_push ; term_snoc ;
    term_push ; termnop ; term_snoc ;
    term_push ; term_swap ; term_snoc ;
    term_push ; termincr ; term_snoc ;
    term_push ; termincr ; term_quote ; term_snoc ;
    term_cons ;
    term_push ; term_pop ; term_snoc ;
    term_push ; term_exec ; term_snoc ].

Lemma termsucc_prop : forall (n : nat) (t1 : term) (vs ps : stack), termnat n t1 ->
  exists t2 : term, termnat (S n) t2 /\ redstar (t1 :: vs, termsucc :: ps) (t2 :: vs, ps).
  intros.
  apply (ex_intro _ (term_list
    [ term_push ; termnop ; term_swap ; termincr ;
      term_seq term_push termincr ; t1 ; term_pop ; term_exec ])).
  split.
  repeat intro.
  evalauto.
  redpartial H.
  redpartial red_termincr_replicate.
  evalauto.
  assert (term_list' (replicate n t2) (term_seq termnop t2) = term_list (replicate (S n) t2)).
    intros ; induction n ; auto.
  rewrite H0.
  apply red_term_list.
  evalauto.
Qed.
