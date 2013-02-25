Require Import
  Coq.Relations.Relations Omega
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype
  Ssreflect.ssrnat Ssreflect.seq.

Set Implicit Arguments.

Lemma nseq_rev_id : forall A n (a : A), nseq n a = rev (nseq n a).
Proof.
  move => A n a.
  rewrite /rev -{1}(cats0 (nseq n a)) -[[::]]/(nseq 0 a).
  move: n 0; elim => //= n IH m; rewrite -(IH m.+1); clear.
  by elim: n => //= n IH; f_equal.
Qed.

Lemma rt1n_trans' : forall A (R : relation A) (x y z : A),
  clos_refl_trans_1n A R x y -> clos_refl_trans_1n A R y z ->
  clos_refl_trans_1n A R x z.
Proof.
  move => A R x y z; elim=> //=.
  clear => x y z' H H0 IH H2; apply Relation_Operators.rt1n_trans with y; auto.
Qed.

(* well-founded induction *)
Definition ltof A (f : A -> nat) (a b : A) := (f a < f b)%nat.

Theorem well_founded_ltof :
  forall (A : Type) (f : A -> nat), well_founded (ltof f).
Proof.
  rewrite /ltof => A f x.
  move: {2}(f x) (leqnn (f x)) => n.
  move: n x.
  elim => [ | n IHn ] x H; constructor => y H0.
  - apply False_ind, notF.
    rewrite -(ltn0 (f y)).
    apply (leq_trans H0 H).
  - apply IHn.
    rewrite -ltnS.
    apply (leq_trans H0 H).
Defined.

Theorem well_founded_lt : well_founded (fun n m => n < m).
Proof.
  move: (well_founded_ltof id).
  rewrite /ltof //.
Defined.

(* subst_evars *)
Ltac subst_evars := match goal with |- _ => idtac end.

(* ssromega *)
Ltac arith_hypo_ssrnat2coqnat :=
  match goal with
    | H : context [?L < ?R] |- _ => move/ltP: H => H
    | H : context [addn ?L ?R] |- _ => rewrite -plusE in H
    | H : context [muln ?L ?R] |- _ => rewrite -multE in H
  end.

Ltac arith_goal_ssrnat2coqnat :=
  rewrite ?NatTrec.trecE -?plusE -?minusE -?multE;
  match goal with
    | |- is_true (_ < _) => apply/ltP
    | |- _ => idtac
  end.

Ltac ssromega :=
  repeat arith_hypo_ssrnat2coqnat ;
  arith_goal_ssrnat2coqnat ;
  omega.
