Require Import
  Relations.Relations Relations.Relation_Operators Omega
  ssreflect ssrnat seq.

Lemma nseq_app :
  forall {A : Set} n m (a : A), nseq n a ++ nseq m a = nseq (n + m) a.
Proof.
  move=> A; elim.
  done.
  by simpl=>n IH m a; f_equal.
Qed.

Lemma nseq_rev_id : forall {A : Set} n (a : A), nseq n a = rev (nseq n a).
Proof.
  move=> A n a.
  rewrite -{1}(cats0 (nseq n a)) /rev.
  rewrite -{1 2}/(iter 0 (cons a) [::]) -/(ncons 0 a [::]) -/(nseq 0 a).
  move: n (0); elim.
  - by simpl=> m.
  - simpl=> m IH n.
    rewrite -(IH (S n)) !nseq_app.
    by replace (m + n.+1) with (S (m + n)).
Qed.

(*
rt1n_trans':
  clos_refl_trans_1n は推移関係である。
*)
Lemma rt1n_trans' : forall (A : Type) (R : relation A) (x y z : A),
  clos_refl_trans_1n A R x y -> clos_refl_trans_1n A R y z ->
  clos_refl_trans_1n A R x z.
Proof.
  move=> A R x y z; elim.
  auto.
  clear=> x y z' H H0 IH H2; apply rt1n_trans with y; auto.
Qed.

(*
sb_decidable:
*)
Notation sb_decidable a := ({a}+{~a}).
