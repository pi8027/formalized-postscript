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
split_list_length:
*)
Theorem split_list_length :
  forall A (xs : list A) n m, length xs = n + m ->
  exists ys zs, xs = ys ++ zs /\ length ys = n /\ length zs = m.
Proof.
  move=> A l n ; move: n l ; elim=> [ | n IH].
  - simpl=> l m H.
    apply: (ex_intro _ []).
    apply: (ex_intro _ l).
    auto.
  - simpl=> l ; move: l n IH ; case=> [ | h l] n IH m H ; inversion H.
    elim (IH l m H1)=> [ys [zs [H2 [H3 H4]]]].
    apply (ex_intro _ (h :: ys)), (ex_intro _ zs).
    split.
    by simpl ; f_equal.
    split.
    by simpl ; f_equal.
    done.
Qed.
