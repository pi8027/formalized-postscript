Require Import
  Relations.Relations Relations.Relation_Operators Omega ssreflect seq.

(*
replicate:
  自然数 n と値 a を取り、a だけで構成された長さ n のリストを返す。
*)
Fixpoint replicate {A : Set} (n : nat) (a : A) :=
  match n with
    | 0 => nil
    | S n => a :: replicate n a
  end.

Lemma replicate_app : forall {A : Set} (n m : nat) (a : A),
  replicate n a ++ replicate m a = replicate (n + m) a.
Proof.
  move=> A ; elim=> [ | n IH m a].
  done.
  by simpl ; f_equal.
Qed.

Lemma replicate_rev_id :
  forall {A : Set} (n : nat) (a : A), replicate n a = rev (replicate n a).
Proof.
  move=> A n a.
  rewrite /rev -{1}(cats0 (replicate n a)) -/(replicate 0 a).
  move: n (0).
  elim=> [m | n IH m].
  - auto.
  - simpl.
    rewrite -(IH (S m)) !replicate_app.
    by replace (n + S m) with (S (n + m)) by omega.
Qed.

(*
rt1n_trans':
  clos_refl_trans_1n は推移関係である。
*)
Lemma rt1n_trans' : forall (A : Type) (R : relation A) (x y z : A),
  clos_refl_trans_1n A R x y -> clos_refl_trans_1n A R y z ->
  clos_refl_trans_1n A R x z.
Proof.
  move=> A R x y z ; elim.
  auto.
  clear=> x y z' H H0 IH H2 ; apply rt1n_trans with y ; auto.
Qed.

(*
sb_decidable:
*)
Notation sb_decidable a := ({a}+{~a}).
