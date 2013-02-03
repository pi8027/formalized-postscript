Require Import
  Coq.Relations.Relations Coq.Relations.Relation_Operators Omega
  Ssreflect.ssreflect Ssreflect.ssrnat Ssreflect.seq.

Lemma nseq_app : forall A n m (a : A), nseq n a ++ nseq m a = nseq (n + m) a.
Proof.
  move=> A; elim.
  done.
  by simpl=>n IH m a; f_equal.
Qed.

Lemma nseq_rev_id : forall A n (a : A), nseq n a = rev (nseq n a).
Proof.
  move=> A n a.
  rewrite -{1}(cats0 (nseq n a)) /rev -[[::]]/(nseq 0 a).
  move: n (0); elim.
  - by simpl=> m.
  - rewrite //= => n IH m.
    rewrite -(IH m.+1) !nseq_app.
    by replace (n + m.+1) with (n + m).+1.
Qed.

(*
rt1n_trans':
  clos_refl_trans_1n は推移関係である。
*)
Lemma rt1n_trans' : forall A (R : relation A) (x y z : A),
  clos_refl_trans_1n A R x y -> clos_refl_trans_1n A R y z ->
  clos_refl_trans_1n A R x z.
Proof.
  move=> A R x y z; elim.
  auto.
  clear=> x y z' H H0 IH H2; apply rt1n_trans with y; auto.
Qed.

(* sb_decidable *)
Notation sb_decidable a := ({a}+{~a}).

(* subst_evars *)
Ltac subst_evars := match goal with |- _ => idtac end.

(* ssromega *)
Ltac ssromega := rewrite -?plusE -?minusE -?multE; omega.
