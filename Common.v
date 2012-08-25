Require Import
  Relations.Relations Relations.Relation_Operators Lists.List Omega ssreflect.

Notation "[]" := nil : list_scope.
Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..) : list_scope.

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
  intros.
  by induction n ; last simpl ; f_equal.
Qed.

Lemma replicate_rev_id :
  forall {A : Set} (n : nat) (a : A), replicate n a = rev (replicate n a).
Proof.
  intros.
  induction n.
  auto.
  simpl.
  rewrite -IHn -/(replicate 1 a) (replicate_app n 1 a).
  by replace (n + 1) with (S n) by omega.
Qed.

(*
rt1n_trans:
  clos_refl_trans_1n は推移関係である。
*)
Lemma rt1n_trans' : forall (A : Type) (R : relation A) (x y z : A),
  clos_refl_trans_1n A R x y -> clos_refl_trans_1n A R y z ->
  clos_refl_trans_1n A R x z.
Proof.
  intros.
  induction H ; last apply (rt1n_trans _ _ _ _ _ H) ; auto.
Qed.
