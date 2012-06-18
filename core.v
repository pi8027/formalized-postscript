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
  | reduction_pop  : forall (v : term) (vs ps : stack),
                     reduction (v :: vs, term_pop :: ps) (vs, ps)
  | reduction_dup  : forall (v : term) (vs ps : stack),
                     reduction (v :: vs, term_dup :: ps) (v :: v :: vs, ps)
  | reduction_swap : forall (v1 v2 : term) (vs ps : stack),
                     reduction (v1 :: v2 :: vs, term_swap :: ps) (v2 :: v1 :: vs, ps)
  | reduction_cons : forall (v1 v2 : term) (vs ps : stack),
                     reduction (v1 :: v2 :: vs, term_cons :: ps) (term_seq v1 v2 :: vs, ps)
  | reduction_push : forall (v : term) (vs ps : stack),
                     reduction (vs, term_push :: v :: ps) (v :: vs, ps)
  | reduction_exec : forall (p : term) (vs ps : stack),
                     reduction (p :: vs, term_exec :: ps) (vs, p :: ps)
  | reduction_seq  : forall (p1 p2 : term) (vs ps : stack),
                     reduction (vs, term_seq p1 p2 :: ps) (vs, p1 :: p2 :: ps).

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
      apply (rt_step _ _ _ _ p) ||
      apply (rt_trans _ _ _ _ _ (rt_step _ _ _ _ p))
    | or_intror _ _ => idtac
    | _ => idtac
  end.

Ltac evalstep :=
  match goal with
    | |- redstar ?e1 ?e2 => evalstep' e1 e2
    | |- clos_refl_trans _ reduction ?e1 ?e2 => evalstep' e1 e2
    | _ => idtac
  end.

Definition termnop : term := term_seq (term_seq term_push term_pop) term_pop.

Lemma rednop : forall (vs ps : stack), redstar (vs, termnop :: ps) (vs, ps).
  intros ; repeat evalstep.
Qed.

Definition term_list' : list term -> term -> term := fold_left term_seq.

Definition term_list (ts : list term) : term := term_list' ts termnop.

Lemma term_list_prop : forall (ts : list term) (vs ps : stack),
  redstar (vs, term_list ts :: ps) (vs, ts ++ ps).
  intros.
  assert (forall head, redstar (vs, term_list' ts head :: ps) (vs, head :: ts ++ ps)).
    induction ts ; intros.
    evalstep.
    apply (rt_trans _ _ _ _ _ (IHts (term_seq head a))) ; evalstep.
  apply (rt_trans _ _ _ _ _ (H termnop) (rednop _ _)).
Qed.

Definition term_quote : term := term_list [term_push ; term_push ; term_cons].

Lemma red_term_quote : forall (v : term) (vs ps : stack),
  redstar (v :: vs, term_quote :: ps) (term_seq term_push v :: vs, ps).
  intros ; repeat evalstep.
Qed.

Definition termnat (n : nat) (p : term) : Prop :=
  forall (v : term) (vs ps : stack),
    redstar (v :: vs, p :: ps) (vs, replicate n v ++ ps).

Definition termincr : term := term_list
  [ term_dup ; term_quote ; term_swap ; term_quote ; term_cons ;
    term_swap ; term_quote ; term_swap ; term_cons ; term_exec ;
    term_cons ; term_swap ].

Lemma termincr_prop : forall (p1 p2 : term) (vs ps : stack),
  redstar (p1 :: p2 :: vs, termincr :: ps) (p1 :: term_seq p2 p1 :: vs, ps).
  intros ; repeat evalstep.
Qed.

Lemma termincr_replicate_prop : forall (n : nat) (p1 p2 : term) (vs ps : stack),
  redstar (p1 :: p2 :: vs, replicate n termincr ++ ps)
    (p1 :: term_list' (replicate n p1) p2 :: vs, ps).
  induction n ; intros ; repeat evalstep.
  apply (rt_trans _ _ _ _ _ (IHn p1 (term_seq p2 p1) vs ps)).
  assert (term_list' (replicate n p1) (term_seq p2 p1) = term_list' (replicate (S n) p1) p2).
    intros ; induction n ; compute ; auto.
  rewrite H ; evalstep.
Qed.

Definition termnat_term (n : nat) : term := term_list
  [ term_push ; termnop ; term_swap ; term_list (replicate n termincr) ; term_pop ; term_exec ].

Lemma termnat_prop : forall (n : nat), termnat n (termnat_term n).
  repeat intro.
  apply (rt_trans _ _ _ _ _ (term_list_prop _ _ _)).
  repeat evalstep.
  apply (rt_trans _ _ _ _ _ (term_list_prop _ _ _)).
  apply (rt_trans _ _ _ _ _ (termincr_replicate_prop _ _ _ _ _)).
  repeat evalstep.
  apply term_list_prop.
Qed.

Definition termsucc : term := term_list
  [ term_push ; term_list [ term_push ; termnop ; term_swap ; termincr ] ; term_swap ;
    term_push ; termincr ; term_quote ; term_cons ;
    term_push ; term_pop ; term_swap ; term_cons ;
    term_push ; term_exec ; term_swap ; term_cons ;
    term_swap ; term_cons ].

Lemma termsucc_prop : forall (n : nat) (p1 : term) (vs ps : stack), termnat n p1 ->
  exists p2 : term, termnat (S n) p2 /\ redstar (p1 :: vs, termsucc :: ps) (p2 :: vs, ps).
  intros.
  apply (ex_intro _
    (term_seq (term_list [term_push; termnop; term_swap; termincr])
      (term_seq (term_seq (term_seq (term_seq term_push termincr) p1) term_pop) term_exec))).
  split.
  repeat intro.
  repeat evalstep.
  apply (rt_trans _ _ _ _ _ (H _ _ _)).
  apply (rt_trans _ _ _ _ _ (termincr_replicate_prop _ _ _ _ _)).
  repeat evalstep.
  assert (term_list' (replicate n v) (term_seq termnop v) = term_list (replicate (S n) v)).
    intros ; induction n ; auto.
  rewrite H0.
  apply term_list_prop.
  repeat evalstep.
Qed.
