Require Import
  Relations.Relations Relations.Relation_Operators Lists.List Program.Syntax
  Omega ssreflect.

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
  move=> A ; elim=> [ | n IH a].
  auto.
  simpl.
  rewrite -IH (replicate_app n 1 a).
  by replace (n + 1) with (S n) by omega.
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

(*
iff_decidable:
*)
Theorem iff_decidable : forall A B, iff A B -> sb_decidable A -> sb_decidable B.
Proof.
  by move=> A B eq ; case=> H ; [left | right] ; rewrite -eq.
Defined.

(*
skipn_length:
*)
Theorem skipn_length :
  forall A (xs : list A) n, length (skipn n xs) = length xs - n.
Proof.
  move=> A ; elim=> [ | x xs IH] [ | n] ; auto.
  apply IH.
Qed.

(*
app_length_firstn:
*)
Theorem app_length_firstn :
  forall A (xs ys : list A), xs = firstn (length xs) (xs ++ ys).
Proof.
  move=> A ; elim => [ | x xs IH].
  auto.
  simpl=> ys ; f_equal ; auto.
Qed.

(*
Forall2_eq_length:
*)
Theorem Forall2_eq_length :
  forall A B (R : A -> B -> Prop) xs ys,
  Forall2 R xs ys -> length xs = length ys.
Proof.
  move=> A B R ; elim=> [ | x xs IH] => ys H ; inversion H.
  done.
  simpl ; f_equal ; auto.
Qed.
