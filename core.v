Require Import Relations.
Require Import Arith.
Require Import List.
Require Import Omega.

Inductive term : Set :=
  | term_pop  : term
  | term_dup  : term
  | term_swap : term
  | term_push : term -> term
  | term_seq  : term -> term -> term
  | term_exec : term.

Definition stack : Set := list term.

(* Environment is product of the value stack and the continuacion stack. *)
Definition environment : Set := (stack * stack)%type.

Inductive reduction : relation environment :=
  | red_pop  : forall (v : term) (vs ps : stack),
               reduction ((v :: vs), (term_pop :: ps)) (vs, ps)
  | red_dup  : forall (v : term) (vs ps : stack),
               reduction ((v :: vs), (term_dup :: ps)) ((v :: v :: vs), ps)
  | red_swap : forall (v1 v2 : term) (vs ps : stack),
               reduction ((v1 :: v2 :: vs), (term_swap :: ps)) ((v2 :: v1 :: vs), ps)
  | red_push : forall (v : term) (vs ps : stack),
               reduction (vs, (term_push v :: ps)) ((v :: vs) , ps)
  | red_seq  : forall (p1 p2 : term) (vs ps : stack),
               reduction (vs, (term_seq p1 p2 :: ps)) (vs, (p1 :: p2 :: ps))
  | red_exec : forall (p : term) (vs ps : stack),
               reduction ((p :: vs), (term_exec :: ps)) (vs, (p :: ps)).

Definition redstar : relation environment := clos_refl_trans _ reduction.

Definition termnop : term := term_seq (term_push term_pop) term_pop.

Lemma termnop_proof : forall (vs ps : stack),
  redstar (vs, (termnop :: ps)) (vs, ps).
  intros.
  unfold termnop.
  apply (rt_trans _ _ _ _ _ (rt_step _ _ _ _ (red_seq _ _ _ _))).
  apply (rt_trans _ _ _ _ _ (rt_step _ _ _ _ (red_push _ _ _))).
  apply (rt_step _ _ _ _ (red_pop _ _ _)).
Qed.

Fixpoint replicate {A : Set} (n : nat) (a : A) :=
  match n with
    | 0 => nil
    | S n' => a :: replicate n' a
  end.

Lemma app_replicate : forall (A : Set) (n m : nat) (a : A),
  replicate n a ++ replicate m a = replicate (n + m) a.
  intros.
  induction n.
  unfold replicate, app ; auto.
  assert (S n + m = S (n + m)).
  omega.
  rewrite H.
  unfold replicate, app ; f_equal ; apply IHn.
Qed.

Definition termnat (n : nat) (p : term) : Set :=
  forall (v : term) (vs ps : stack),
    redstar ((v :: vs), (p :: ps)) (replicate (S n) v ++ vs, ps).

Fixpoint termnat_term (n : nat) : term :=
  match n with
    | 0 => termnop
    | S n => term_seq term_dup (termnat_term n)
  end.

Lemma termnat_proof : forall (n : nat), termnat n (termnat_term n).
  intros.
  induction n ; unfold termnat ; intros.
  apply termnop_proof.
  apply (rt_trans _ _ _ _ _ (rt_step _ _ _ _ (red_seq _ _ _ _))).
  apply (rt_trans _ _ _ _ _ (rt_step _ _ _ _ (red_dup _ _ _))).
  assert (replicate (S (S n)) v = replicate (S n) v ++ replicate 1 v).
    assert (S (S n) = S n + 1).
      omega.
    rewrite H.
    apply eq_sym.
    apply app_replicate.
  rewrite H.
  rewrite (eq_sym (app_assoc (replicate (S n) v) (replicate 1 v) vs)).
  apply IHn.
Qed.

