Require Import List.
Require Import Omega.

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
  intros.
  induction n.
  compute ; auto.
  replace (S n + m) with (S (n + m)) by omega.
  compute ; f_equal ; apply IHn.
Qed.

Lemma replicate_rev_id :
  forall {A : Set} (n : nat) (a : A), replicate n a = rev (replicate n a).
  intros.
  induction n.
  auto.
  simpl.
  rewrite <- IHn.
  fold (replicate 1 a).
  rewrite (replicate_app n 1 a).
  replace (n + 1) with (S n) by omega.
  auto.
Qed.

(*
exists_map, and_map_left, and_map_right, or_map_left, or_map_right:
  exists, and, or の部分を書き換える。
*)

Lemma exists_map :
  forall (A : Set) (P Q : A -> Prop),
  (forall (a : A), P a -> Q a) -> (exists a : A, P a) -> (exists a : A, Q a).
  intros ; firstorder auto.
Qed.

Lemma and_map_left : forall (P P' Q : Prop), (P -> P') -> P /\ Q -> P' /\ Q.
  intros ; tauto.
Qed.

Lemma and_map_right : forall (P Q Q' : Prop), (Q -> Q') -> P /\ Q -> P /\ Q'.
  intros ; tauto.
Qed.

Lemma or_map_left : forall (P P' Q : Prop), (P -> P') -> P /\ Q -> P' /\ Q.
  intro ; tauto.
Qed.

Lemma or_map_right : forall (P Q Q' : Prop), (Q -> Q') -> P /\ Q -> P /\ Q'.
  intro ; tauto.
Qed.
